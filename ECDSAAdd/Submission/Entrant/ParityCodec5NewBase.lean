import ECDSAAdd.Submission.Entrant.MainPre

/-! A legal fifth-trit permutation makes the raw sign parity an affine payload bit. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ParityCodec5New
open Arithmetic Challenge RecordedQuantum Baselines
open MeasuredCodec5 (bitsOf legal local_word bitRun legalNat safe run_sim sim_safe)

def twist : Program := [.X 9,.CX 8 9]
def untwist : Program := [.CX 8 9,.X 9]
def encode : Program := twist ++ MeasuredCodec5.encode
def decode : Program := MeasuredCodec5.decode ++ untwist
abbrev legalAt := MeasuredCodec5.legalAt

def rawParity (s : BasisState) : Bool := s 1 ^^ s 3 ^^ s 5 ^^ s 7 ^^ s 9
def payloadParity (s : BasisState) : Bool :=
  s 0 ^^ s 1 ^^ s 2 ^^ s 3 ^^ s 4 ^^ s 6 ^^ s 7 ^^ s 8

theorem twist_phase (s : State) (m : List Bool) : (run twist m s).phase=s.phase := rfl

theorem twist_basis (s : State) (m : List Bool) :
    (run twist m s).basis=writeBit s.basis 9 (!s.basis 9 ^^ s.basis 8) := by
  simp [twist,run,writeBit,Function.update]

theorem twist_roundtrip (s : State) (m n : List Bool) :
    run untwist n (run twist m s)=s := by
  cases s with
  | mk ph b =>
    apply State.extensionality
    · rfl
    · funext q
      by_cases hq:q=9
      · subst q; simp [twist,untwist,run,writeBit,Function.update]
      · simp [twist,untwist,run,writeBit,Function.update,hq]

theorem twist_legal (s : State) (m : List Bool) (h : legal s.basis) :
    legal (run twist m s).basis := by
  intro i hi
  rw [twist_basis]
  interval_cases i
  · simpa [MeasuredCodec5.pair,writeBit,Function.update] using h 0 (by decide)
  · simpa [MeasuredCodec5.pair,writeBit,Function.update] using h 1 (by decide)
  · simpa [MeasuredCodec5.pair,writeBit,Function.update] using h 2 (by decide)
  · simpa [MeasuredCodec5.pair,writeBit,Function.update] using h 3 (by decide)
  · have hh:=h 4 (by decide)
    cases a:s.basis 8 <;> cases b:s.basis 9 <;>
      simp_all [MeasuredCodec5.pair,writeBit,Function.update]

theorem encode_correct (s : State) (m : List Bool) (h : legal s.basis) :
    (run encode m s).phase=s.phase ∧ (run encode m s).basis 5=false ∧
    (run encode m s).basis 9=false := by
  have hh:=MeasuredCodec5.encode_correct (run twist [] s) m (twist_legal s [] h)
  simpa only [encode,run_append,show measurementCount twist=0 from rfl,
    List.take_zero,List.drop_zero,twist_phase] using hh

theorem roundtrip (s : State) (mE mD : List Bool) (h : legal s.basis) :
    run decode mD (run encode mE s)=s := by
  simp only [encode,decode,run_append,show measurementCount twist=0 from rfl,
    List.take_zero,List.drop_zero]
  rw [MeasuredCodec5.roundtrip _ _ _ (twist_legal s [] h),twist_roundtrip]

theorem encode_independent (s : State) (m n : List Bool) (h : legal s.basis) :
    run encode m s=run encode n s := by
  apply State.extensionality
  · exact (encode_correct s m h).1.trans (encode_correct s n h).1.symm
  · exact run_basis_records _ s s m n rfl

theorem support_exact : wires encode=Finset.range 10 ∧ wires decode=Finset.range 10 := by
  simp only [encode,decode,wires_append,MeasuredCodec5.support_exact.1,MeasuredCodec5.support_exact.2]
  decide

theorem support : wires encode⊆Finset.range 10 ∧ wires decode⊆Finset.range 10 := by
  rw [support_exact.1,support_exact.2]
  exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩

theorem counts : toffoliCount encode=9 ∧ measurementCount encode=4 ∧
    toffoliCount decode=11 ∧ measurementCount decode=2 := by
  simp only [encode,decode,toffoliCount_append,measurementCount_append]
  simpa [twist,untwist,toffoliCount,measurementCount] using MeasuredCodec5.counts

theorem slots : gateSlots encode=144 ∧ gateSlots decode=142 := by
  rw [encode,decode,gateSlots_append,gateSlots_append,MeasuredCodec5.slots.1,MeasuredCodec5.slots.2]
  decide

theorem physical : GatePhysical encode ∧ GatePhysical decode := by
  have ht:GatePhysical twist := by simp [GatePhysical,twist,PhysicalInstr,ProperGate]
  have hu:GatePhysical untwist := by simp [GatePhysical,untwist,PhysicalInstr,ProperGate]
  exact ⟨(gatePhysical_append _ _).mpr ⟨ht,MeasuredCodec5.physical.1⟩,
    (gatePhysical_append _ _).mpr ⟨MeasuredCodec5.physical.2,hu⟩⟩

theorem finite_parity : ∀ x<1024, legalNat x=true →
    rawParity (bitsOf x)=payloadParity (bitsOf (bitRun encode x)) := by
  decide +kernel

theorem encode_parity (s : State) (m : List Bool) (h : legal s.basis) :
    rawParity s.basis=payloadParity (run encode m s).basis := by
  obtain ⟨x,hx,lx,hb⟩:=local_word s h
  have hh:=pool_run_agrees encode (Finset.range 10) support.1 m s ⟨s.phase,bitsOf x⟩ rfl hb
  have modeled:=run_sim encode m s.phase x
  have hs:safe encode x=true := by
    change safe MeasuredCodec5.encode (MeasuredCodec5.bitStep (.CX 8 9)
      (MeasuredCodec5.bitStep (.X 9) x))=true
    have old:=MeasuredCodec5.finite_encode
    have legalTwist:∀x<1024,legalNat x=true →
        MeasuredCodec5.bitStep (.CX 8 9) (MeasuredCodec5.bitStep (.X 9) x)<1024 ∧
        legalNat (MeasuredCodec5.bitStep (.CX 8 9) (MeasuredCodec5.bitStep (.X 9) x))=true := by decide +kernel
    exact (old _ (legalTwist x hx lx).1 (legalTwist x hx lx).2).1
  rw [sim_safe encode x hs] at modeled
  have out (q : Nat) (hq:q<10) : (run encode m s).basis q=(bitsOf (bitRun encode x)) q :=
    (hh.2 q (Finset.mem_range.mpr hq)).trans (congrArg (fun t:State=>t.basis q) modeled)
  have rawEq:rawParity s.basis=rawParity (bitsOf x) := by
    simp only [rawParity,hb 1 (by decide),hb 3 (by decide),hb 5 (by decide),hb 7 (by decide),hb 9 (by decide)]
  rw [rawEq,finite_parity x hx lx]
  simp only [payloadParity,out 0 (by decide),out 1 (by decide),out 2 (by decide),out 3 (by decide),
    out 4 (by decide),out 6 (by decide),out 7 (by decide),out 8 (by decide)]

/-- Only the ten declared local ports are mapped. -/
abbrev label := MeasuredCodec5.label

def encodeAt (f : Fin 10→Wire) : Program := renameProgram (label f) encode
def decodeAt (f : Fin 10→Wire) : Program := renameProgram (label f) decode

private theorem label_inj (f : Fin 10→Wire) (hf : Function.Injective f) :
    ∀a∈Finset.range 10,∀b∈Finset.range 10,label f a=label f b → a=b := by
  intro a ha b hb e
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have eq : f ⟨a,ha'⟩=f ⟨b,hb'⟩ := by simpa only [label,MeasuredCodec5.label,dif_pos ha',dif_pos hb'] using e
  exact congrArg Fin.val (hf eq)

private theorem label_image (f : Fin 10→Wire) :
    (Finset.range 10).image (label f)=Finset.univ.image f := by
  ext q
  simp only [Finset.mem_image,Finset.mem_range,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,e⟩
    exact ⟨⟨i,hi⟩,by simpa only [label,MeasuredCodec5.label,dif_pos hi] using e⟩
  · rintro ⟨i,e⟩
    exact ⟨i.val,i.isLt,by simpa only [label,MeasuredCodec5.label,dif_pos i.isLt] using e⟩

theorem supportAt_exact (f : Fin 10→Wire) :
    wires (encodeAt f)=Finset.univ.image f ∧ wires (decodeAt f)=Finset.univ.image f := by
  simp only [encodeAt,decodeAt,renameProgram_support,support_exact.1,support_exact.2,label_image]
  exact ⟨trivial,trivial⟩

theorem supportAt (f : Fin 10→Wire) :
    wires (encodeAt f)⊆Finset.univ.image f ∧ wires (decodeAt f)⊆Finset.univ.image f := by
  rw [(supportAt_exact f).1,(supportAt_exact f).2]
  exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩

theorem site_mem (f : Fin 10→Wire) (i : Fin 10) : f i∈wires (encodeAt f) := by
  rw [(supportAt_exact f).1]
  exact Finset.mem_image_of_mem f (Finset.mem_univ i)

theorem countsAt (f : Fin 10→Wire) : toffoliCount (encodeAt f)=9 ∧ measurementCount (encodeAt f)=4 ∧
    toffoliCount (decodeAt f)=11 ∧ measurementCount (decodeAt f)=2 := by
  simpa only [encodeAt,decodeAt,(renameProgram_counts (label f) encode).1,
    (renameProgram_counts (label f) encode).2,(renameProgram_counts (label f) decode).1,
    (renameProgram_counts (label f) decode).2] using counts

theorem slotsAt (f : Fin 10→Wire) : gateSlots (encodeAt f)=144 ∧ gateSlots (decodeAt f)=142 := by
  simpa only [encodeAt,decodeAt,rename_gateSlots] using slots

theorem physicalAt (f : Fin 10→Wire) (hf : Function.Injective f) :
    GatePhysical (encodeAt f) ∧ GatePhysical (decodeAt f) := by
  exact ⟨gatePhysical_rename_support _ _
    (fun a ha b hb e => label_inj f hf a (support.1 ha) b (support.1 hb) e) physical.1,
    gatePhysical_rename_support _ _
    (fun a ha b hb e => label_inj f hf a (support.2 ha) b (support.2 hb) e) physical.2⟩

theorem encodeAt_correct (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legalAt f s.basis) :
    (run (encodeAt f) m s).phase=s.phase ∧
    (run (encodeAt f) m s).basis (f 5)=false ∧ (run (encodeAt f) m s).basis (f 9)=false := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have localResult := encode_correct t m h
  have placed := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 m t s rfl (fun _ _ => rfl)
  refine ⟨placed.1.trans localResult.1,?_,?_⟩
  · have e := (placed.2 5 (by decide)).trans localResult.2.1
    simpa only [label,MeasuredCodec5.label,dif_pos (show 5<10 by decide)] using e
  · have e := (placed.2 9 (by decide)).trans localResult.2.2
    simpa only [label,MeasuredCodec5.label,dif_pos (show 9<10 by decide)] using e

theorem legalAt_iff (f : Fin 10→Wire) (s : BasisState) : legalAt f s ↔
    ∀i : Fin 5,(s (f ⟨2*i.val,by omega⟩) && s (f ⟨2*i.val+1,by omega⟩))=false :=
  MeasuredCodec5.legalAt_iff f s

theorem encodeAt_phase (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legalAt f s.basis) : (run (encodeAt f) m s).phase=s.phase :=
  (encodeAt_correct f hf s m h).1

theorem encodeAt_independent (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m n : List Bool) (h : legalAt f s.basis) :
    run (encodeAt f) m s=run (encodeAt f) n s := by
  apply State.extensionality
  · exact (encodeAt_phase f hf s m h).trans (encodeAt_phase f hf s n h).symm
  · exact run_basis_records _ s s m n rfl

theorem roundtripAt (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (mE mD : List Bool) (h : legalAt f s.basis) :
    run (decodeAt f) mD (run (encodeAt f) mE s)=s := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have pe := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 mE t s rfl (fun _ _ => rfl)
  have pd := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) decode
    support.2 mD (run encode mE t) (run (encodeAt f) mE s) pe.1.symm
    (fun q hq => (pe.2 q hq).symm)
  have inv := roundtrip t mE mD h
  apply State.extensionality
  · have hp := congrArg State.phase inv
    exact pd.1.trans hp
  · funext q
    by_cases hq : q∈Finset.univ.image f
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
      have eq := (pd.2 i.val (Finset.mem_range.mpr i.isLt)).trans
        (congrArg (fun st : State => st.basis i.val) inv)
      simpa only [t,label,MeasuredCodec5.label,dif_pos i.isLt] using eq
    · exact (run_preserves_outside (decodeAt f) mD (run (encodeAt f) mE s) q
        (fun used => hq ((supportAt f).2 used))).trans
        (run_preserves_outside (encodeAt f) mE s q (fun used => hq ((supportAt f).1 used)))

theorem encodeAt_zero_phase (f : Fin 10→Wire) (hf : Function.Injective f) (s : State) :
    (run (encodeAt f) [] s).phase=s.phase := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have placed := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 [] t s rfl (fun _ _ => rfl)
  exact placed.1.trans (MeasuredCodec5.zero_phase encode (by decide) t)

theorem mapped_support_eq (f : Fin 10→Wire) :
    wires (encodeAt f)=wires (MeasuredCodec5.encodeAt f) ∧
    wires (decodeAt f)=wires (MeasuredCodec5.decodeAt f) := by
  rw [(supportAt_exact f).1,(supportAt_exact f).2,
    (MeasuredCodec5.supportAt_exact f).1,(MeasuredCodec5.supportAt_exact f).2]
  exact ⟨rfl,rfl⟩

theorem encodeAt_parity (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legalAt f s.basis) :
    (s.basis (f 1) ^^ s.basis (f 3) ^^ s.basis (f 5) ^^ s.basis (f 7) ^^ s.basis (f 9))=
    ((run (encodeAt f) m s).basis (f 0) ^^ (run (encodeAt f) m s).basis (f 1) ^^
      (run (encodeAt f) m s).basis (f 2) ^^ (run (encodeAt f) m s).basis (f 3) ^^
      (run (encodeAt f) m s).basis (f 4) ^^ (run (encodeAt f) m s).basis (f 6) ^^
      (run (encodeAt f) m s).basis (f 7) ^^ (run (encodeAt f) m s).basis (f 8)) := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have result := encode_parity t m h
  have placed := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 m t s rfl (fun _ _ => rfl)
  have port (q : Fin 10) : (run (encodeAt f) m s).basis (f q)=(run encode m t).basis q.val := by
    simpa only [label,MeasuredCodec5.label,dif_pos q.isLt] using placed.2 q.val (Finset.mem_range.mpr q.isLt)
  simpa only [rawParity,payloadParity,t,label,dif_pos (show 0<10 by decide),
    dif_pos (show 1<10 by decide),dif_pos (show 2<10 by decide),dif_pos (show 3<10 by decide),
    dif_pos (show 4<10 by decide),dif_pos (show 5<10 by decide),dif_pos (show 6<10 by decide),
    dif_pos (show 7<10 by decide),dif_pos (show 8<10 by decide),dif_pos (show 9<10 by decide),
    port 0,port 1,port 2,port 3,port 4,port 6,port 7,port 8] using result

end ECDSAAdd.Entrant.ParityCodec5New
