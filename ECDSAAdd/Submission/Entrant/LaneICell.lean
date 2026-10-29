import ECDSAAdd.Submission.Entrant.LaneIKernel
import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalReplay
import ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonicalReplay
import ECDSAAdd.Arithmetic.EndpointSwapTrimProgram
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Baselines.SlotMapped

/-! Field cells, replays and the endpoint cell built on the 256-wide fold
kernels, with exact State equality to the original cells on their frames,
and an instruction-level inclusion into the original programs. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic Secp256k1 BalancedField OffsetBorrowedCanonical

/-! ### Generic State-equality composition -/

theorem seq_eq (P P' Q Q' : Program) (s : State) (m : List Bool)
    (hc : measurementCount P'=measurementCount P)
    (hp : run P' (m.take (measurementCount P)) s=run P (m.take (measurementCount P)) s)
    (hq : run Q' (m.drop (measurementCount P)) (run P (m.take (measurementCount P)) s)=
      run Q (m.drop (measurementCount P)) (run P (m.take (measurementCount P)) s)) :
    run (P'++Q') m s=run (P++Q) m s := by
  rw [run_append,run_append,hc,hp,hq]

theorem window_split (b source flag : Wire) (c : Bool) (P : Program) :
    transcriptSelectWindow b source flag c P=
      (transcriptSelectCompute b source flag c++transcriptSelectExpose flag c)++
        (P++(transcriptSelectExpose flag c++transcriptSelectErase b source flag c)) := by
  simp only [transcriptSelectWindow,List.append_assoc]

private theorem select_startI (b source flag : Wire) (constant : Bool)
    (hn : [b,source,flag].Nodup) (s : State) (m : List Bool)
    (hf : s.basis flag=false) :
    run (transcriptSelectCompute b source flag constant ++
      transcriptSelectExpose flag constant) m s=
      ⟨s.phase,mixedTranscriptBase s.basis b source flag constant⟩ := by
  rw [run_append,transcriptSelectCompute_correct b source flag constant hn]
  apply State.extensionality
  · cases constant <;> rfl
  · funext q
    by_cases hq : q=flag
    · subst q
      cases hb : s.basis b <;> cases hs : s.basis source <;> cases constant <;>
        simp [transcriptSelectExpose,run,mixedTranscriptBase,mixedTranscriptBit,
          writeBit,Function.update,hf,hb,hs]
    · cases constant <;>
        simp [transcriptSelectExpose,run,mixedTranscriptBase,writeBit,Function.update,hq]

theorem select_start_frame (b source flag : Wire) (constant : Bool)
    (z a : List Wire) (hn : [b,source,flag].Nodup)
    (hb : b∉z ∧ b∉a) (hs : source∉z ∧ source∉a)
    (hf : flag∉z ∧ flag∉a) (base : BasisState) (hzero : base flag=false) (X Y : Nat) :
    Triple (PairFrame z a base X Y)
      (transcriptSelectCompute b source flag constant ++ transcriptSelectExpose flag constant)
      (PairFrame z a (mixedTranscriptBase base b source flag constant) X Y) := by
  intro s m h
  have hz : s.basis flag=false := (h.2.2 flag hf.1 hf.2).trans hzero
  rw [select_startI b source flag constant hn s m hz]
  refine ⟨rfl,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => by
      simp [mixedTranscriptBase,writeBit,Function.update,show q≠flag from
        fun he => hf.1 (he ▸ hq)])).trans h.1
  · exact (regValue_congr _ _ _ (fun q hq => by
      simp [mixedTranscriptBase,writeBit,Function.update,show q≠flag from
        fun he => hf.2 (he ▸ hq)])).trans h.2.1
  · intro q hqz hqa
    by_cases hq : q=flag
    · subst q
      simp [mixedTranscriptBase,mixedTranscriptBit,writeBit,
        h.2.2 b hb.1 hb.2,h.2.2 source hs.1 hs.2]
    · simpa [mixedTranscriptBase,writeBit,Function.update,hq] using h.2.2 q hqz hqa

theorem window_eq (b source flag : Wire) (constant : Bool)
    (z a : List Wire) (hn : [b,source,flag].Nodup)
    (hb : b∉z ∧ b∉a) (hs : source∉z ∧ source∉a)
    (hf : flag∉z ∧ flag∉a) (base : BasisState) (hzero : base flag=false) (X Y : Nat)
    (P P' : Program) (hc : measurementCount P'=measurementCount P)
    (heq : ∀ (t : State) (r : List Bool),
      PairFrame z a (mixedTranscriptBase base b source flag constant) X Y t.basis →
      run P' r t=run P r t)
    (s : State) (m : List Bool) (h : PairFrame z a base X Y s.basis) :
    run (transcriptSelectWindow b source flag constant P') m s=
      run (transcriptSelectWindow b source flag constant P) m s := by
  rw [window_split,window_split]
  have start := select_start_frame b source flag constant z a hn hb hs hf base hzero X Y
  apply seq_eq _ _ _ _ s m rfl rfl
  apply seq_eq _ _ _ _ _ _ hc _ rfl
  exact heq _ _ (start s _ h).2

theorem window_counts_eq (b source flag : Wire) (c : Bool) (P P' : Program)
    (hc : measurementCount P'=measurementCount P) :
    measurementCount (transcriptSelectWindow b source flag c P')=
      measurementCount (transcriptSelectWindow b source flag c P) := by
  rw [(transcriptSelectWindow_counts b source flag c P').2,
    (transcriptSelectWindow_counts b source flag c P).2,hc]

theorem window_toffoli (b source flag : Wire) (c : Bool) (P P' : Program) (k : Nat)
    (hc : toffoliCount P'+k=toffoliCount P) :
    toffoliCount (transcriptSelectWindow b source flag c P')+k=
      toffoliCount (transcriptSelectWindow b source flag c P) := by
  rw [(transcriptSelectWindow_counts b source flag c P').1,
    (transcriptSelectWindow_counts b source flag c P).1,←hc]
  omega

/-! ### Instruction-level inclusion -/

/-- Every instruction of `P'` occurs in `P`, except clean measurements of
wires already used by `P`; and `P'` has no more syntax slots than `P`. -/
def InstrSub (P' P : Program) : Prop :=
  (∀ i∈P', i∈P ∨ ∃ t∈wires P, i=.measureX t [] []) ∧
    Challenge.gateSlots P'≤Challenge.gateSlots P

theorem mem_wires_iff (P : Program) (q : Wire) : q∈wires P ↔ ∃ i∈P, q∈i.wires := by
  induction P with
  | nil => simp [wires]
  | cons i p ih =>
    simp only [wires,Finset.mem_union,ih,List.mem_cons]
    constructor
    · rintro (h|⟨j,hj,hq⟩)
      · exact ⟨i,Or.inl rfl,h⟩
      · exact ⟨j,Or.inr hj,hq⟩
    · rintro ⟨j,(rfl|hj),hq⟩
      · exact Or.inl hq
      · exact Or.inr ⟨j,hj,hq⟩

theorem InstrSub.wires_sub {P' P : Program} (h : InstrSub P' P) : wires P'⊆wires P := by
  intro q hq
  obtain ⟨i,hi,hq⟩ := (mem_wires_iff P' q).mp hq
  rcases h.1 i hi with hi|⟨t,ht,rfl⟩
  · exact (mem_wires_iff P q).mpr ⟨i,hi,hq⟩
  · have : q=t := by simpa [Instr.wires,correctionWires] using hq
    subst q; exact ht

theorem InstrSub.physical {P' P : Program} (h : InstrSub P' P) (hp : GatePhysical P) :
    GatePhysical P' := by
  intro i hi
  rcases h.1 i hi with hi|⟨t,_,rfl⟩
  · exact hp i hi
  · trivial

theorem InstrSub.slots {P' P : Program} (h : InstrSub P' P) :
    Challenge.gateSlots P'≤Challenge.gateSlots P := h.2

theorem InstrSub.refl (P : Program) : InstrSub P P := ⟨fun i hi => Or.inl hi,le_refl _⟩

theorem InstrSub.append {P₁' P₁ P₂' P₂ : Program} (h₁ : InstrSub P₁' P₁) (h₂ : InstrSub P₂' P₂) :
    InstrSub (P₁'++P₂') (P₁++P₂) := by
  refine ⟨?_,?_⟩
  · intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · rcases h₁.1 i hi with h|⟨t,ht,e⟩
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr ⟨t,by rw [wires_append]; exact Finset.mem_union_left _ ht,e⟩
    · rcases h₂.1 i hi with h|⟨t,ht,e⟩
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr ⟨t,by rw [wires_append]; exact Finset.mem_union_right _ ht,e⟩
  · simp only [Challenge.gateSlots_append]
    exact Nat.add_le_add h₁.2 h₂.2

theorem InstrSub.rename (f : Wire → Wire) {P' P : Program} (h : InstrSub P' P) :
    InstrSub (renameProgram f P') (renameProgram f P) := by
  refine ⟨?_,?_⟩
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    rcases h.1 j hj with h|⟨t,ht,rfl⟩
    · exact Or.inl (List.mem_map.mpr ⟨j,h,rfl⟩)
    · refine Or.inr ⟨f t,?_,?_⟩
      · rw [renameProgram_support]; exact Finset.mem_image_of_mem f ht
      · simp [renameInstr]
  · simp only [Baselines.rename_gateSlots]
    exact h.2

theorem InstrSub.window (b source flag : Wire) (c : Bool) {P' P : Program} (h : InstrSub P' P) :
    InstrSub (transcriptSelectWindow b source flag c P') (transcriptSelectWindow b source flag c P) := by
  simp only [transcriptSelectWindow]
  exact (((InstrSub.refl _).append (InstrSub.refl _)).append h |>.append (InstrSub.refl _)).append
    (InstrSub.refl _)

theorem InstrSub.trans {P'' P' P : Program} (h₁ : InstrSub P'' P') (h₂ : InstrSub P' P) :
    InstrSub P'' P := by
  refine ⟨?_,h₁.2.trans h₂.2⟩
  intro i hi
  rcases h₁.1 i hi with h|⟨t,ht,e⟩
  · exact h₂.1 i h
  · exact Or.inr ⟨t,h₂.wires_sub ht,e⟩

/-! ### The narrow fold is an instruction subset of the wide fold -/

theorem mappedAdd_mem_extend (bs : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (b : MappedBit) (y c : Wire) (hl : bs.length=ys.length) (hc : cs.length+1=ys.length) :
    (∀ i∈mappedAdd bs ys cs cin, i∈mappedAdd (bs++[b]) (ys++[y]) (cs++[c]) cin) ∧
    Challenge.gateSlots (mappedAdd bs ys cs cin)≤
      Challenge.gateSlots (mappedAdd (bs++[b]) (ys++[y]) (cs++[c]) cin) := by
  induction ys generalizing bs cs cin with
  | nil => simp at hc
  | cons y0 ys ih =>
    cases bs with
    | nil => simp at hl
    | cons b0 bs =>
      cases ys with
      | nil =>
        have hb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        have hcs : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
        subst hb; subst hcs
        simp only [List.nil_append,List.cons_append,mappedAdd,Challenge.gateSlots_append]
        refine ⟨fun i hi => ?_,by omega⟩
        simp only [List.mem_append]
        exact Or.inr hi
      | cons y1 ys =>
        cases bs with
        | nil => simp at hl
        | cons b1 bs =>
          cases cs with
          | nil => simp at hc
          | cons c0 cs =>
            have hrec := ih (b1::bs) cs c0 (by simpa using hl) (by simpa using hc)
            simp only [List.cons_append] at hrec
            simp only [List.cons_append,mappedAdd,Challenge.gateSlots_append]
            refine ⟨fun i hi => ?_,by omega⟩
            simp only [List.mem_append] at hi ⊢
            rcases hi with ((h|h)|h)|h
            · exact Or.inl (Or.inl (Or.inl h))
            · exact Or.inl (Or.inl (Or.inr (hrec.1 i h)))
            · exact Or.inl (Or.inr h)
            · exact Or.inr h

theorem carry_split (L : BalancedCircuit.Layout) (hw : L.Widths) :
    ∃ c, L.carry=L.carry.take 255++[c] := by
  have len := (BalancedCircuit.widths L hw).2.2.2.2
  have d : (L.carry.drop 255).length=1 := by rw [List.length_drop,len]
  obtain ⟨c,hc⟩ := List.length_eq_one_iff.mp d
  exact ⟨c,by rw [←hc,List.take_append_drop]⟩

theorem foldI_sub (L : BalancedCircuit.Layout) (hw : L.Widths) :
    InstrSub (foldI L) (BalancedCircuit.fold L) := by
  obtain ⟨c,hc⟩ := carry_split L hw
  have w := BalancedCircuit.widths L hw
  have tl : (BalancedCircuit.foldTarget L).length=256 := by
    have h := w.2.2.1
    simp only [List.length_append,List.length_cons,List.length_nil] at h
    omega
  have cl : (L.carry.take 255).length+1=(BalancedCircuit.foldTarget L).length := by
    rw [List.length_take,w.2.2.2.2,tl]; decide
  have bl : (foldBitsI L).length=(BalancedCircuit.foldTarget L).length := by rw [foldBitsI_length,tl]
  have ext := mappedAdd_mem_extend (foldBitsI L) (BalancedCircuit.foldTarget L) (L.carry.take 255)
    L.parity {wire:=none,flip:=false} L.cout c bl cl
  rw [←hc,←foldBits_split] at ext
  refine ⟨?_,?_⟩
  · intro i hi
    rcases List.mem_append.mp hi with h|h
    · right
      refine ⟨L.cout,?_,by simpa using h⟩
      simp only [BalancedCircuit.fold,wires_append]
      apply Finset.mem_union_right
      simp [wires,Instr.wires]
    · left
      simp only [BalancedCircuit.fold]
      exact List.mem_append_left _ (ext.1 i h)
  · have e := ext.2
    simp only [foldI,BalancedCircuit.fold,Challenge.gateSlots_append]
    simp only [Baselines.gateSlots_cons,Baselines.gateSlots_nil,Challenge.instructionSlots,
      List.length_nil]
    omega

theorem undoFoldI_sub (L : BalancedCircuit.Layout) (hw : L.Widths) :
    InstrSub (undoFoldI L) (BalancedInverse.undoFold L) := by
  obtain ⟨c,hc⟩ := carry_split L hw
  have w := BalancedCircuit.widths L hw
  have tl : (BalancedCircuit.foldTarget L).length=256 := by
    have h := w.2.2.1
    simp only [List.length_append,List.length_cons,List.length_nil] at h
    omega
  have cl : (L.carry.take 255).length+1=(BalancedCircuit.foldTarget L).length := by
    rw [List.length_take,w.2.2.2.2,tl]; decide
  have bl : (foldBitsI L).length=(BalancedCircuit.foldTarget L).length := by rw [foldBitsI_length,tl]
  have ext := mappedAdd_mem_extend (foldBitsI L) (BalancedCircuit.foldTarget L) (L.carry.take 255)
    L.parity {wire:=none,flip:=false} L.cout c bl cl
  rw [←hc,←foldBits_split] at ext
  have nots : ∀ i∈notRegister (BalancedCircuit.foldTarget L),
      i∈notRegister (BalancedCircuit.foldTarget L++[L.cout]) := by
    intro i hi
    simp only [notRegister,List.map_append] at hi ⊢
    exact List.mem_append_left _ hi
  have notSlots (r : List Wire) : Challenge.gateSlots (notRegister r)=r.length := by
    induction r with
    | nil => rfl
    | cons a r ih =>
      simp only [notRegister,List.map_cons,Baselines.gateSlots_cons,Challenge.instructionSlots,
        List.length_cons] at ih ⊢
      rw [ih]; omega
  refine ⟨?_,?_⟩
  · intro i hi
    rcases List.mem_append.mp hi with h|h
    · right
      refine ⟨L.cout,?_,by simpa using h⟩
      simp only [BalancedInverse.undoFold,wires_append]
      apply Finset.mem_union_left
      simp [wires,Instr.wires]
    · left
      simp only [BalancedInverse.undoFold,mappedSub] at h ⊢
      simp only [List.mem_append] at h ⊢
      rcases h with (h|h)|h
      · exact Or.inr (Or.inl (Or.inl (nots i h)))
      · exact Or.inr (Or.inl (Or.inr (ext.1 i h)))
      · exact Or.inr (Or.inr (nots i h))
  · have e := ext.2
    simp only [undoFoldI,BalancedInverse.undoFold,mappedSub,Challenge.gateSlots_append,notSlots,
      List.length_append,List.length_cons,List.length_nil]
    simp only [Baselines.gateSlots_cons,Baselines.gateSlots_nil,Challenge.instructionSlots,
      List.length_nil]
    omega

theorem coreI_sub (L : BalancedCircuit.Layout) (hw : L.Widths) :
    InstrSub (coreProgramI L) (BalancedCircuit.coreProgram L) := by
  simp only [coreProgramI,BalancedCircuit.coreProgram]
  exact (InstrSub.refl _).append ((InstrSub.refl _).append ((InstrSub.refl _).append
    ((foldI_sub L hw).append (InstrSub.refl _))))

theorem fieldProgramI_sub (w : Nat → Wire) (sign : Wire) :
    InstrSub (fieldProgramI w sign) (OffsetBorrowedField.program w sign) := by
  simp only [fieldProgramI,OffsetBorrowedField.program]
  exact (coreI_sub _ (balancedSharedPorts_widths w sign)).append (InstrSub.refl _)

theorem invFieldProgramI_sub (w : Nat → Wire) (sign : Wire) :
    InstrSub (invFieldProgramI w sign) (OffsetBorrowedInverse.program w sign) := by
  simp only [invFieldProgramI,OffsetBorrowedInverse.program,tailI,OffsetBorrowedInverse.tail]
  exact ((InstrSub.refl _).append (InstrSub.refl _)).append
    (((((((InstrSub.refl _).append (InstrSub.refl _)).append
      (undoFoldI_sub _ (balancedSharedPorts_widths w sign))).append (InstrSub.refl _)).append
      (InstrSub.refl _)).append (InstrSub.refl _)))

/-! ### Kernels wrapped by the sign flips -/

/-- Inside an `X sign` wrapper, the new forward kernel gives the old State. -/
theorem xwrap_forward_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (he : Env w base)
    (X Y : Fp) (C : Program) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run ([.X sign]++(fieldProgramI w sign++C)) m s=
      run ([.X sign]++(OffsetBorrowedField.program w sign++C)) m s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have aw := BalancedCircuit.flagAway L nd sign (by simp [L,balancedSharedPorts])
  have sa : sign∉L.r ∧ sign∉L.y := ⟨fun h => aw (by simp [h]),fun h => aw (by simp [h])⟩
  have se := pair_env w sign hn base s.basis _ _ he h
  apply seq_eq _ _ _ _ s m rfl rfl
  generalize eu : run [.X sign] (m.take (measurementCount [.X sign])) s=u
  have us := BalancedCleanupOffset.x_run sign s (m.take (measurementCount [.X sign]))
  rw [eu] at us
  have uf (q : Wire) (hq : q≠sign) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ue : Env w u.basis := by
    rw [us]
    exact env_write w sign ho s.basis (!s.basis sign) se
  have ug : u.basis sign= !base sign := by
    rw [us]
    simp only [writeBit,Function.update_self,h.2.2 sign sa.1 sa.2]
  have uv (r : List Wire) (a : sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => uf q (fun e => a (e ▸ hq)))
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.2.1,centerWord_decode]
  apply seq_eq _ _ _ _ _ _ (fieldProgramI_counts w sign).2 _ rfl
  exact fieldProgram_eq w sign hn ho (!base sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u _ ug ur uy ue

/-- Inside an `X sign` wrapper, the new inverse kernel gives the old State. -/
theorem xwrap_inverse_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (he : Env w base)
    (X Y : Fp) (C : Program) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run ([.X sign]++(invFieldProgramI w sign++C)) m s=
      run ([.X sign]++(OffsetBorrowedInverse.program w sign++C)) m s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have aw := BalancedCircuit.flagAway L nd sign (by simp [L,balancedSharedPorts])
  have sa : sign∉L.r ∧ sign∉L.y := ⟨fun h => aw (by simp [h]),fun h => aw (by simp [h])⟩
  have se := pair_env w sign hn base s.basis _ _ he h
  apply seq_eq _ _ _ _ s m rfl rfl
  generalize eu : run [.X sign] (m.take (measurementCount [.X sign])) s=u
  have us := BalancedCleanupOffset.x_run sign s (m.take (measurementCount [.X sign]))
  rw [eu] at us
  have uf (q : Wire) (hq : q≠sign) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ue : Env w u.basis := by
    rw [us]
    exact env_write w sign ho s.basis (!s.basis sign) se
  have ug : u.basis sign= !base sign := by
    rw [us]
    simp only [writeBit,Function.update_self,h.2.2 sign sa.1 sa.2]
  have uv (r : List Wire) (a : sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => uf q (fun e => a (e ▸ hq)))
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.2.1,centerWord_decode]
  apply seq_eq _ _ _ _ _ _ (invFieldProgramI_counts w sign).2 _ rfl
  exact invField_eq w sign hn ho (centerFp X) (centerFp Y) (!base sign)
    (centerFp_bounds X) (centerFp_bounds Y) u _ ur uy ug ue.1 ue.2.1 ue.2.2

/-! ### Forward cell -/

def bodyFI (w : Nat → Wire) (sign effS : Wire) : Program :=
  [.X sign]++fieldProgramI w sign++[.X sign]++
    swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y

def cellFI (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b g sign ig (transcriptSelectWindow b swap effS is (bodyFI w sign effS))

theorem bodyFI_counts (w : Nat → Wire) (sign effS : Wire) :
    measurementCount (bodyFI w sign effS)=measurementCount (OffsetBorrowedCanonical.body w sign effS) ∧
    toffoliCount (bodyFI w sign effS)+1=toffoliCount (OffsetBorrowedCanonical.body w sign effS) := by
  have c := fieldProgramI_counts w sign
  simp only [bodyFI,OffsetBorrowedCanonical.body,measurementCount_append,toffoliCount_append]
  constructor <;> omega

theorem cellFI_counts (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    measurementCount (cellFI w b g swap sign effS ig is)=
      measurementCount (OffsetBorrowedCanonical.cell w b g swap sign effS ig is) ∧
    toffoliCount (cellFI w b g swap sign effS ig is)+1=
      toffoliCount (OffsetBorrowedCanonical.cell w b g swap sign effS ig is) := by
  have c := bodyFI_counts w sign effS
  exact ⟨window_counts_eq _ _ _ _ _ _ (window_counts_eq _ _ _ _ _ _ c.1),
    window_toffoli _ _ _ _ _ _ 1 (window_toffoli _ _ _ _ _ _ 1 c.2)⟩

theorem cellFI_sub (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    InstrSub (cellFI w b g swap sign effS ig is) (OffsetBorrowedCanonical.cell w b g swap sign effS ig is) := by
  apply InstrSub.window; apply InstrSub.window
  simp only [bodyFI,OffsetBorrowedCanonical.body]
  exact (((InstrSub.refl _).append (fieldProgramI_sub w sign)).append (InstrSub.refl _)).append
    (InstrSub.refl _)

theorem bodyFI_eq (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (bodyFI w sign effS) m s=run (OffsetBorrowedCanonical.body w sign effS) m s := by
  simp only [bodyFI,OffsetBorrowedCanonical.body,List.append_assoc]
  exact xwrap_forward_eq w sign hn ho base he X Y _ s m h

theorem cellFI_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false) (hs0 : base effS=false)
    (he : Env w base) (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (cellFI w b g swap sign effS ig is) m s=
      run (OffsetBorrowedCanonical.cell w b g swap sign effS ig is) m s := by
  let bg := mixedTranscriptBase base b g sign ig
  let bs := mixedTranscriptBase bg b swap effS is
  have flags := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have sg : [b,g,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ss : [b,swap,effS].Nodup := by simp [List.nodup_cons]; tauto
  have ne : effS≠sign := Ne.symm (by tauto)
  have bgS : bg effS=false := by simp only [bg,mixedTranscriptBase,writeBit,Function.update_of_ne ne,hs0]
  have ge : Env w bg := env_write w sign ho base _ he
  have se : Env w bs := env_write w effS hoS bg _ ge
  have c := bodyFI_counts w sign effS
  apply window_eq b g sign ig _ _ sg (hl.outside b (by simp)) (hl.outside g (by simp))
    (hl.outside sign (by simp [balancedSharedPorts])) base hg0 _ _ _ _
    (window_counts_eq _ _ _ _ _ _ c.1) _ s m h
  intro t r ht
  apply window_eq b swap effS is _ _ ss (hl.outside b (by simp)) (hl.outside swap (by simp))
    (hl.outside effS (by simp)) bg bgS _ _ _ _ c.1 _ t r ht
  intro t' r' ht'
  exact bodyFI_eq w sign effS hn ho bs se X Y t' r' ht'

/-! ### Inverse cell -/

def doubleII (w : Nat → Wire) (sign : Wire) : Program :=
  [.X sign]++invFieldProgramI w sign++[.X sign]

def bodyII (w : Nat → Wire) (sign effS : Wire) : Program :=
  swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y++doubleII w sign

def cellII (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b g sign ig (transcriptSelectWindow b swap effS is (bodyII w sign effS))

theorem bodyII_counts (w : Nat → Wire) (sign effS : Wire) :
    measurementCount (bodyII w sign effS)=measurementCount (OffsetBorrowedInverseCanonical.body w sign effS) ∧
    toffoliCount (bodyII w sign effS)+1=toffoliCount (OffsetBorrowedInverseCanonical.body w sign effS) := by
  have c := invFieldProgramI_counts w sign
  simp only [bodyII,doubleII,OffsetBorrowedInverseCanonical.body,OffsetBorrowedInverseCanonical.double,
    measurementCount_append,toffoliCount_append]
  constructor <;> omega

theorem cellII_counts (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    measurementCount (cellII w b g swap sign effS ig is)=
      measurementCount (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is) ∧
    toffoliCount (cellII w b g swap sign effS ig is)+1=
      toffoliCount (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is) := by
  have c := bodyII_counts w sign effS
  exact ⟨window_counts_eq _ _ _ _ _ _ (window_counts_eq _ _ _ _ _ _ c.1),
    window_toffoli _ _ _ _ _ _ 1 (window_toffoli _ _ _ _ _ _ 1 c.2)⟩

theorem cellII_sub (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    InstrSub (cellII w b g swap sign effS ig is)
      (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is) := by
  apply InstrSub.window; apply InstrSub.window
  simp only [bodyII,doubleII,OffsetBorrowedInverseCanonical.body,OffsetBorrowedInverseCanonical.double]
  exact (InstrSub.refl _).append (((InstrSub.refl _).append (invFieldProgramI_sub w sign)).append
    (InstrSub.refl _))

private theorem swap_pairI (r y : List Wire) (c : Wire) (hlen : r.length=y.length)
    (hn : (c::r++y).Nodup) (base : BasisState) (A B : Nat) :
    Triple (PairFrame r y base A B) (swapRegisters c r y)
      (PairFrame r y base (if base c then B else A) (if base c then A else B)) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  have ca : c∉r ∧ c∉y := by
    have d := (List.nodup_cons.mp hn).1
    exact ⟨fun hm => d (List.mem_append_left _ hm),fun hm => d (List.mem_append_right _ hm)⟩
  have same := h.2.2 c ca.1 ca.2
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,same,h.1,h.2.1]
  · rw [v.2.2.2,same,h.1,h.2.1]

theorem bodyII_eq (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (hsw : (effS::(balancedSharedPorts w sign).r++
      (balancedSharedPorts w sign).y).Nodup) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (bodyII w sign effS) m s=run (OffsetBorrowedInverseCanonical.body w sign effS) m s := by
  let L := balancedSharedPorts w sign
  have len := BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w sign)
  simp only [bodyII,OffsetBorrowedInverseCanonical.body]
  apply seq_eq _ _ _ _ s m rfl rfl
  have sw := swap_pairI L.r L.y effS (len.2.1.trans len.2.2.1.symm) hsw base
    (centerWord X) (centerWord Y) s (m.take (measurementCount (swapRegisters effS L.r L.y))) h
  generalize run (swapRegisters effS L.r L.y) (m.take (measurementCount (swapRegisters effS L.r L.y))) s=u at sw ⊢
  let A := if base effS then Y else X
  let B := if base effS then X else Y
  have view : PairFrame L.r L.y base (centerWord A) (centerWord B) u.basis := by
    cases e : base effS <;> simpa only [A,B,e,Bool.false_eq_true,if_true,if_false] using sw.2
  simp only [doubleII,OffsetBorrowedInverseCanonical.double,List.append_assoc]
  exact xwrap_inverse_eq w sign hn ho base he A B _ u _ view

theorem cellII_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false) (hs0 : base effS=false)
    (he : Env w base) (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (cellII w b g swap sign effS ig is) m s=
      run (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is) m s := by
  let bg := mixedTranscriptBase base b g sign ig
  let bs := mixedTranscriptBase bg b swap effS is
  have flags := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have sg : [b,g,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ss : [b,swap,effS].Nodup := by simp [List.nodup_cons]; tauto
  have ne : effS≠sign := Ne.symm (by tauto)
  have bgS : bg effS=false := by simp only [bg,mixedTranscriptBase,writeBit,Function.update_of_ne ne,hs0]
  have ge : Env w bg := env_write w sign ho base _ he
  have se : Env w bs := env_write w effS hoS bg _ ge
  have c := bodyII_counts w sign effS
  apply window_eq b g sign ig _ _ sg (hl.outside b (by simp)) (hl.outside g (by simp))
    (hl.outside sign (by simp [balancedSharedPorts])) base hg0 _ _ _ _
    (window_counts_eq _ _ _ _ _ _ c.1) _ s m h
  intro t r ht
  apply window_eq b swap effS is _ _ ss (hl.outside b (by simp)) (hl.outside swap (by simp))
    (hl.outside effS (by simp)) bg bgS _ _ _ _ c.1 _ t r ht
  intro t' r' ht'
  exact bodyII_eq w sign effS hn ho hl.swapND bs se X Y t' r' ht'

/-! ### Replays -/

def replayFI (w : Nat → Wire) (b sign effS : Wire) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => cellFI w b l.1.1 l.1.2 sign effS l.2.1 l.2.2++replayFI w b sign effS ls

def replayII (w : Nat → Wire) (b sign effS : Wire) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => replayII w b sign effS ls++cellII w b l.1.1 l.1.2 sign effS l.2.1 l.2.2

theorem replayFI_counts (w : Nat → Wire) (b sign effS : Wire) (ls : List MixedTranscriptLetter) :
    measurementCount (replayFI w b sign effS ls)=measurementCount (OffsetBorrowedCanonical.replay w b sign effS ls) ∧
    toffoliCount (replayFI w b sign effS ls)+ls.length=toffoliCount (OffsetBorrowedCanonical.replay w b sign effS ls) := by
  induction ls with
  | nil => simp [replayFI,OffsetBorrowedCanonical.replay]
  | cons l ls ih =>
    have c := cellFI_counts w b l.1.1 l.1.2 sign effS l.2.1 l.2.2
    simp only [replayFI,OffsetBorrowedCanonical.replay,measurementCount_append,toffoliCount_append,
      List.length_cons]
    constructor <;> omega

theorem replayII_counts (w : Nat → Wire) (b sign effS : Wire) (ls : List MixedTranscriptLetter) :
    measurementCount (replayII w b sign effS ls)=measurementCount (OffsetBorrowedInverseCanonical.replay w b sign effS ls) ∧
    toffoliCount (replayII w b sign effS ls)+ls.length=toffoliCount (OffsetBorrowedInverseCanonical.replay w b sign effS ls) := by
  induction ls with
  | nil => simp [replayII,OffsetBorrowedInverseCanonical.replay]
  | cons l ls ih =>
    have c := cellII_counts w b l.1.1 l.1.2 sign effS l.2.1 l.2.2
    simp only [replayII,OffsetBorrowedInverseCanonical.replay,measurementCount_append,toffoliCount_append,
      List.length_cons]
    constructor <;> omega

theorem replayFI_sub (w : Nat → Wire) (b sign effS : Wire) (ls : List MixedTranscriptLetter) :
    InstrSub (replayFI w b sign effS ls) (OffsetBorrowedCanonical.replay w b sign effS ls) := by
  induction ls with
  | nil => exact InstrSub.refl _
  | cons l ls ih => exact (cellFI_sub _ _ _ _ _ _ _ _).append ih

theorem replayII_sub (w : Nat → Wire) (b sign effS : Wire) (ls : List MixedTranscriptLetter) :
    InstrSub (replayII w b sign effS ls) (OffsetBorrowedInverseCanonical.replay w b sign effS ls) := by
  induction ls with
  | nil => exact InstrSub.refl _
  | cons l ls ih => exact ih.append (cellII_sub _ _ _ _ _ _ _ _)

theorem replayFI_eq (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base sign=false) (hs0 : base effS=false) (he : Env w base) (X Y : Fp)
    (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (replayFI w b sign effS ls) m s=run (OffsetBorrowedCanonical.replay w b sign effS ls) m s := by
  induction ls generalizing X Y s m with
  | nil => rfl
  | cons l ls ih =>
    let next := skywalkPayloadCell (mixedTranscriptBit base b l.1.1 l.2.1)
      (mixedTranscriptBit base b l.1.2 l.2.2) (X,Y)
    have hl := balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho
    have fr := OffsetBorrowedCanonical.cell_frame w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hn hl
      (ho sign (by simp)) (ho effS (by simp)) base hg0 hs0 he X Y
    simp only [replayFI,OffsetBorrowedCanonical.replay]
    apply seq_eq _ _ _ _ s m (cellFI_counts _ _ _ _ _ _ _ _).1
      (cellFI_eq w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hn hl (ho sign (by simp)) (ho effS (by simp))
        base hg0 hs0 he X Y s _ h)
    exact ih (fun q hq => hf q (by simp [hq])) next.1 next.2 _ _ (fr s _ h).2

theorem replayII_eq (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base sign=false) (hs0 : base effS=false) (he : Env w base) (X Y : Fp)
    (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (replayII w b sign effS ls) m s=run (OffsetBorrowedInverseCanonical.replay w b sign effS ls) m s := by
  induction ls generalizing X Y s m with
  | nil => rfl
  | cons l ls ih =>
    have hl := balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho
    have hr : MixedTranscriptReplayLayout w b sign effS ls := fun q hq => hf q (by simp [hq])
    have fr := OffsetBorrowedInverseCanonical.replay_frame w b sign effS hn ls hr ho base hg0 hs0 he X Y
    simp only [replayII,OffsetBorrowedInverseCanonical.replay]
    apply seq_eq _ _ _ _ s m (replayII_counts _ _ _ _ _).1 (ih hr X Y s _ h)
    exact cellII_eq w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hn hl (ho sign (by simp)) (ho effS (by simp))
      base hg0 hs0 he _ _ _ _ (fr s _ h).2

/-! ### Endpoint cells (no S window) -/

def trimFI (w : Nat → Wire) (b g flag : Wire) (ig : Bool) : Program :=
  transcriptSelectWindow b g flag ig ([.X flag]++fieldProgramI w flag++[.X flag])

def trimII (w : Nat → Wire) (b g flag : Wire) (ig : Bool) : Program :=
  transcriptSelectWindow b g flag ig ([.X flag]++invFieldProgramI w flag++[.X flag])

theorem trim_counts (w : Nat → Wire) (b g flag : Wire) (ig : Bool) :
    measurementCount (trimFI w b g flag ig)=measurementCount (EndpointSwapTrim.forward w b g flag ig) ∧
    toffoliCount (trimFI w b g flag ig)+1=toffoliCount (EndpointSwapTrim.forward w b g flag ig) ∧
    measurementCount (trimII w b g flag ig)=measurementCount (EndpointSwapTrim.inverse w b g flag ig) ∧
    toffoliCount (trimII w b g flag ig)+1=toffoliCount (EndpointSwapTrim.inverse w b g flag ig) := by
  have f := fieldProgramI_counts w flag
  have i := invFieldProgramI_counts w flag
  have a : measurementCount ([.X flag]++fieldProgramI w flag++[.X flag])=
      measurementCount ([.X flag]++OffsetBorrowedField.program w flag++[.X flag]) := by
    simp only [measurementCount_append]; omega
  have b' : toffoliCount ([.X flag]++fieldProgramI w flag++[.X flag])+1=
      toffoliCount ([.X flag]++OffsetBorrowedField.program w flag++[.X flag]) := by
    simp only [toffoliCount_append]; omega
  have c : measurementCount ([.X flag]++invFieldProgramI w flag++[.X flag])=
      measurementCount ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag]) := by
    simp only [measurementCount_append]; omega
  have d : toffoliCount ([.X flag]++invFieldProgramI w flag++[.X flag])+1=
      toffoliCount ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag]) := by
    simp only [toffoliCount_append]; omega
  exact ⟨window_counts_eq _ _ _ _ _ _ a,window_toffoli _ _ _ _ _ _ 1 b',
    window_counts_eq _ _ _ _ _ _ c,window_toffoli _ _ _ _ _ _ 1 d⟩

theorem trim_sub (w : Nat → Wire) (b g flag : Wire) (ig : Bool) :
    InstrSub (trimFI w b g flag ig) (EndpointSwapTrim.forward w b g flag ig) ∧
    InstrSub (trimII w b g flag ig) (EndpointSwapTrim.inverse w b g flag ig) := by
  constructor
  · apply InstrSub.window
    exact ((InstrSub.refl _).append (fieldProgramI_sub w flag)).append (InstrSub.refl _)
  · apply InstrSub.window
    exact ((InstrSub.refl _).append (invFieldProgramI_sub w flag)).append (InstrSub.refl _)

theorem trim_eq (divide : Bool) (w : Nat → Wire) (b g swap sign effS : Wire) (ig : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false)
    (he : Env w base) (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (if divide then trimFI w b g sign ig else trimII w b g sign ig) m s=
      run (if divide then EndpointSwapTrim.forward w b g sign ig
        else EndpointSwapTrim.inverse w b g sign ig) m s := by
  let bg := mixedTranscriptBase base b g sign ig
  have flags := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have sg : [b,g,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ge : Env w bg := env_write w sign ho base _ he
  have tc := trim_counts w b g sign ig
  have ci : measurementCount ([.X sign]++invFieldProgramI w sign++[.X sign])=
      measurementCount ([.X sign]++OffsetBorrowedInverse.program w sign++[.X sign]) := by
    have i := invFieldProgramI_counts w sign
    simp only [measurementCount_append]; omega
  have cf : measurementCount ([.X sign]++fieldProgramI w sign++[.X sign])=
      measurementCount ([.X sign]++OffsetBorrowedField.program w sign++[.X sign]) := by
    have i := fieldProgramI_counts w sign
    simp only [measurementCount_append]; omega
  cases divide
  · simp only [Bool.false_eq_true,if_false]
    apply window_eq b g sign ig _ _ sg (hl.outside b (by simp)) (hl.outside g (by simp))
      (hl.outside sign (by simp [balancedSharedPorts])) base hg0 _ _ _ _ ci _ s m h
    intro t r ht
    simp only [List.append_assoc]
    exact xwrap_inverse_eq w sign hn ho bg ge X Y _ t r ht
  · simp only [if_true]
    apply window_eq b g sign ig _ _ sg (hl.outside b (by simp)) (hl.outside g (by simp))
      (hl.outside sign (by simp [balancedSharedPorts])) base hg0 _ _ _ _ cf _ s m h
    intro t r ht
    simp only [List.append_assoc]
    exact xwrap_forward_eq w sign hn ho bg ge X Y _ t r ht

end ECDSAAdd.Entrant.LaneI
