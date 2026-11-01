import ECDSAAdd.Submission.Entrant.MainA

/-! # FirstZero: the zero-word first divide cell

`Rolling1588.firstCells true` starts with the field cell of letter 1 (`cell true 0 1 4`),
right after the first swap. The divide stage enters its first packet with payload `(Y,0)`, so this
cell always sees one payload word equal to zero (which one depends on the first transcript
bit). Then the raw sum `T = X ± Y` is centered, and its original parity equals the sign of the
biased normalized half `normalizedR (halfResult T)` that the forward kernel prefix leaves in the
result register. The generic kernel's comparator block (`TopCarryBorrow`, 255 Toffoli and
256 records, with its prepare/exposure views) is therefore replaced by two Clifford gates.
257 empty-correction erasures of the clean `one` wire (the comparator's 256 records and the
generic kernel's final `one` erasure) keep the record length unchanged.

The new forward kernel runs exactly like `Q6StructuralCell.forward` on every such state
(full `State` equality, for independent record lists), so every caller frame is transported
by run equality. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.FirstZero
open Arithmetic Arithmetic.BalancedField BalancedCircuit MappedCompressed
attribute [local irreducible] wires

/-! ### Arithmetic -/

private theorem normalized_cases (R : Int) :
    normalizedR R=(if R<0 then -R-1 else R)-h+(if R<0 then 1 else 0) := by
  unfold normalizedR magnitude signBit negative
  by_cases hR : R<0 <;> simp [hR]

/-- For a centered raw sum, the original parity is the sign of the biased normalized half. -/
theorem parity_normalized (T : Int) (hT : Centered T) :
    originalParity T=decide (0≤normalizedR (halfResult T)) := by
  obtain ⟨hq0,hpq,hq1,hqh,hh0,-,-⟩ := constants
  unfold Centered at hT
  have key : ∀ E : Int, evenLift T=E → (T%2≠0 ↔ 0≤normalizedR (E/2)) →
      originalParity T=decide (0≤normalizedR (halfResult T)) := by
    intro E hE h
    unfold originalParity halfResult
    rw [hE]
    exact decide_eq_decide.mpr h
  by_cases h2 : T%2=0
  · apply key T (by simp [evenLift,h2])
    rw [normalized_cases]
    by_cases hn : T/2<0
    · rw [if_pos hn,if_pos hn]; constructor <;> intro <;> omega
    · rw [if_neg hn,if_neg hn]; constructor <;> intro <;> omega
  · by_cases ht : 0≤T
    · apply key (T-(ECDSAAdd.p:Int)) (by simp [evenLift,h2,ht])
      rw [normalized_cases]
      by_cases hn : (T-(ECDSAAdd.p:Int))/2<0
      · rw [if_pos hn,if_pos hn]; constructor <;> intro <;> omega
      · rw [if_neg hn,if_neg hn]; constructor <;> intro <;> omega
    · apply key (T+(ECDSAAdd.p:Int)) (by simp [evenLift,h2,ht])
      rw [normalized_cases]
      by_cases hn : (T+(ECDSAAdd.p:Int))/2<0
      · rw [if_pos hn,if_pos hn]; constructor <;> intro <;> omega
      · rw [if_neg hn,if_neg hn]; constructor <;> intro <;> omega

theorem encode255_high (z : Int) (h1 : -h≤z) (h2 : z<h) :
    2^254≤encodeWord 255 z ↔ z<0 := by
  obtain ⟨-,-,-,-,hh0,hh1,-⟩ := constants
  have c := encodeWord_cast 255 z
  have b := encodeWord_bound 255 z
  norm_num only [Nat.reducePow,Nat.cast_ofNat] at c b hh1 ⊢
  constructor <;> intro hz <;> omega

theorem low_arith (R : Int) (hr : Centered R) :
    (encodeWord 255 (normalizedR R)+BalancedCleanup.positiveLiteral+(!negative R).toNat)%2^255=
      (magnitude R).toNat := by
  have ar := normalizedR_lowword_arithmetic R hr
  have mb := magnitude_bounds R hr
  obtain ⟨hq0,hpq,hq1,hqh,hh0,hh1,hq2⟩ := constants
  have hm := Int.toNat_of_nonneg mb.1
  have hh := Int.toNat_of_nonneg (show 0≤h by omega)
  have hl := Int.toNat_of_nonneg (show 0≤h-1 by omega)
  have a1 := ar.1
  unfold BalancedCleanup.positiveLiteral
  rw [ar.2]
  norm_num only [Nat.reducePow,Nat.cast_ofNat] at hh1 hq2 a1 ⊢
  cases hneg : negative R <;>
    simp only [Bool.not_false,Bool.not_true,Bool.toNat_false,Bool.toNat_true] <;> omega

theorem centered_of_zero (B : Bool) (X Y : Fp) (hz : X=0 ∨ Y=0) :
    Centered (rawSum B (centerFp X) (centerFp Y)) := by
  have c0 : centerFp (0:Fp)=0 := by
    have hc := centerFp_of_center 0 (by unfold Centered; have := constants; omega)
    simpa using hc
  rcases hz with rfl|rfl
  · rw [c0]
    unfold rawSum
    simpa using signedY_bounds B _ (centerFp_bounds Y)
  · rw [c0]
    unfold rawSum signedY
    cases B <;> simpa using centerFp_bounds X

/-! ### Program -/

/-- Parity erasure from bit 254 (the sign of the biased low word). -/
def eraseParity (L : BalancedCircuit.Layout) : Program :=
  [.CX (L.rtail.getD 253 0) L.parity,.X L.parity]

def tail (L : BalancedCircuit.Layout) : Program :=
  eraseParity L++(BalancedCleanup.unnormalize L.toLayout++
    ((BalancedCleanup.prepareSign L.toLayout).reverse++
      List.replicate 257 (Instr.measureX L.one [] [])))

def forward (L : BalancedCircuit.Layout) : Program :=
  Q6StructuralCell.forwardPrefix L++tail L

theorem pad_run (n : Nat) (c : Wire) (m : List Bool) (t : State) (h : t.basis c=false) :
    run (List.replicate n (Instr.measureX c [] [])) m t=t := by
  induction n generalizing m t with
  | zero => simp only [List.replicate_zero,run]
  | succ n ih =>
    rw [List.replicate_succ]
    have one : run [.measureX c [] []] m t=t := by
      obtain ⟨ph,bs⟩ := t
      simp only at h
      have e : writeBit bs c false=bs := by
        funext q; by_cases hq : q=c
        · subst hq; simp [writeBit,h]
        · simp [writeBit,Function.update,hq]
      simp only [run,measureAndCorrect,h,Bool.and_false,Bool.xor_false,e]
      cases m.headD false <;> rfl
    change run (Instr.measureX c [] [] :: List.replicate n (Instr.measureX c [] [])) m t=t
    simp only [run] at one ⊢
    rw [one]
    exact ih _ _ h

theorem rtail_split (xs : List Wire) (h : xs.length=254) :
    xs=xs.take 253++[xs.getD 253 0] := by
  have hlt : 253<xs.length := by omega
  rw [List.getD_eq_getElem _ _ hlt]
  conv_lhs => rw [←List.take_append_drop 253 xs]
  congr 1
  rw [List.drop_eq_getElem_cons hlt]
  have : xs.drop 254=[] := List.drop_eq_nil_of_le (by omega)
  simp [this]

/-! ### State after the shared prefix -/

theorem prefix_facts (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    (run (Q6StructuralCell.forwardPrefix L) m s).phase=s.phase ∧
    regValue L.r (run (Q6StructuralCell.forwardPrefix L) m s).basis=
      encodeWord 255 (normalizedR (halfResult (rawSum B X Y))) ∧
    (run (Q6StructuralCell.forwardPrefix L) m s).basis L.lower=negative (halfResult (rawSum B X Y)) ∧
    (run (Q6StructuralCell.forwardPrefix L) m s).basis L.parity=originalParity (rawSum B X Y) ∧
    (run (Q6StructuralCell.forwardPrefix L) m s).basis L.one=false ∧
    (∀q∈L.carry,(run (Q6StructuralCell.forwardPrefix L) m s).basis q=false) ∧
    (∀q,q∉L.r → q≠L.lower → q≠L.parity →
      (run (Q6StructuralCell.forwardPrefix L) m s).basis q=s.basis q) := by
  have a254 : 254<L.carry.length := by rw [hw.2.2]; omega
  have ha : L.carry.getD 254 0∈L.carry := by
    rw [List.getD_eq_getElem _ _ a254]; exact List.getElem_mem _
  have shape : Q6StructuralCell.forwardPrefix L=Q6Cell.forwardPrefix L (L.carry.getD 254 0) := by
    rw [Q6StructuralCell.forwardPrefix,Q6Cell.forwardPrefix,Q6Cell.rawAdd,Q6Structural.rawAdd_eq L hw hn]
  have uOld : run (Q6StructuralCell.forwardPrefix L) m s=
      run (FifthCarry.oldForwardPrefix L) (false::m) s := by
    rw [shape,Q6Cell.forwardPrefix_eq L hw hn _ ha s m hc,FifthCarry2.forwardPrefix_shifted L hw hn s m hc]
  have apart := FifthCarry.forward_prefix_apart L hw hn B X Y hx hy s (false::m) hs hr hyr hc
  have post := ShortBiasedFold.prefixPost L hw hn B X Y hx hy s (false::m) hs hr hyr hc
  have clean := FifthCarry.forward_prefix_clean L hw hn B X Y hx hy s (false::m) hs hr hyr hc
  rw [←uOld] at apart clean
  have nd := scalarND L hn
  have sgR : L.sourceGuard∉L.r := fun h => flagAway L hn L.sourceGuard (by simp) (by simp [h])
  have sgFree : L.sourceGuard∉wires (Q6StructuralCell.forwardPrefix L) := by
    intro hmem
    apply (Q6StructuralCell.unused_free L hw hn L.sourceGuard (by simp)).1
    simp only [Q6StructuralCell.forward,wires_append,Finset.mem_union]
    exact Or.inl (Or.inl hmem)
  have uSg := run_preserves_outside _ m s _ sgFree
  have lg : L.lower≠L.sourceGuard := by intro e; rw [e] at nd; simp at nd
  have pg : L.parity≠L.sourceGuard := by intro e; rw [e] at nd; simp at nd
  refine ⟨apart.1.trans post.phase,?_,(apart.2 _ lg).trans post.lower,
    (apart.2 _ pg).trans post.parity,clean.1,clean.2,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => apart.2 q (fun e => sgR (e ▸ hq)))).trans post.value
  · intro q qr ql qp
    by_cases qg : q=L.sourceGuard
    · subst q; exact uSg
    · exact (apart.2 q qg).trans (post.frame q qr ql qp qg)

/-! ### The tail -/

theorem tail_run (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hR : Centered R) (P : Bool) (hP : P=decide (0≤normalizedR R))
    (s u F : State) (m : List Bool)
    (uPhase : u.phase=s.phase) (uR : regValue L.r u.basis=encodeWord 255 (normalizedR R))
    (uLower : u.basis L.lower=negative R) (uPar : u.basis L.parity=P)
    (uOne : u.basis L.one=false) (uCarry : ∀q∈L.carry,u.basis q=false)
    (uFrame : ∀q,q∉L.r → q≠L.lower → q≠L.parity → u.basis q=s.basis q)
    (sPar : s.basis L.parity=false) (sLower : s.basis L.lower=false) (sOne : s.basis L.one=false)
    (FPhase : F.phase=s.phase) (FR : regValue L.r F.basis=encodeWord 256 R)
    (FFrame : ∀q,q∉L.r → F.basis q=s.basis q) :
    run (tail L) m u=F := by
  have w := BalancedCleanup.widths L.toLayout hw
  have hn' : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have nd := scalarND L hn
  have flagR (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q∉L.r := fun h => flagAway L hn q hq (by simp [h])
  have flagC (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q∉L.carry := fun h => flagAway L hn q hq (by simp [h])
  have parR : L.parity∉L.r := flagR _ (by simp)
  have lowR : L.lower∉L.r := flagR _ (by simp)
  have oneR : L.one∉L.r := flagR _ (by simp)
  have rEq : L.r=L.low++[L.rmsb] := rfl
  have rLow (q : Wire) (hq : q∈L.low) : q∈L.r := by rw [rEq]; exact List.mem_append_left _ hq
  have rmsbR : L.rmsb∈L.r := by rw [rEq]; simp
  have rmsbLow : L.rmsb∉L.low := by
    have d := List.nodup_append'.mp (List.nodup_append'.mp (L.toLayout.dataND hn')).1
    exact fun h => List.disjoint_left.mp d.2.2 h (by simp)
  have lp : L.lower≠L.parity := by intro e; rw [e] at nd; simp at nd
  have op : L.one≠L.parity := by intro e; rw [e] at nd; simp at nd
  have single (t : BasisState) : regValue [L.rmsb] t=(if t L.rmsb then 1 else 0) := by simp [regValue]
  -- the result word of the prefix is below `2^255`: its top bit is clear
  have rsplit : regValue L.r u.basis=regValue L.low u.basis+2^255*regValue [L.rmsb] u.basis := by
    rw [rEq,regValue_append,w.1]
  have rlt := encodeWord_bound 255 (normalizedR R)
  have uRmsb : u.basis L.rmsb=false := by
    cases hb : u.basis L.rmsb
    · rfl
    · exfalso
      rw [single,hb,if_pos rfl,uR] at rsplit
      omega
  have uLow : regValue L.low u.basis=encodeWord 255 (normalizedR R) := by
    rw [single,uRmsb,uR] at rsplit
    simp only [Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at rsplit
    exact rsplit.symm
  -- bit 254 is the sign of the biased word
  have split : L.low=(L.r0::L.rtail.take 253)++[L.rtail.getD 253 0] := by
    rw [show L.low=L.r0::L.rtail from rfl]
    conv_lhs => rw [rtail_split L.rtail hw.1]
    rfl
  have memLow : L.rtail.getD 253 0∈L.low := by rw [split]; simp
  have b254R : L.rtail.getD 253 0≠L.parity := fun e => parR (e ▸ rLow _ memLow)
  have b254 : u.basis (L.rtail.getD 253 0)=!P := by
    have hi := regValue_highBit (L.r0::L.rtail.take 253) (L.rtail.getD 253 0) u.basis
    rw [←split,uLow] at hi
    have len : (L.r0::L.rtail.take 253).length=254 := by simp [List.length_take,hw.1]
    rw [len] at hi
    have nb := normalizedR_bounds R hR
    have hi2 := encode255_high (normalizedR R) nb.1 nb.2
    rw [hP]
    by_cases hneg : normalizedR R<0
    · have hb := hi.mpr (hi2.mpr hneg)
      rw [hb]
      simp [not_le.mpr hneg]
    · have hb : ¬u.basis (L.rtail.getD 253 0)=true := fun h => hneg (hi2.mp (hi.mp h))
      simp only [Bool.not_eq_true] at hb
      rw [hb]
      simp [not_lt.mp hneg]
  -- erasure
  let u2 : State := run (eraseParity L) [] u
  have u2Phase : u2.phase=u.phase := rfl
  have u2Par : u2.basis L.parity=false := by
    simp only [u2,eraseParity,run,writeBit,Function.update_self,
      Function.update_of_ne b254R,uPar,b254]
    cases P <;> rfl
  have u2Other (q : Wire) (hq : q≠L.parity) : u2.basis q=u.basis q := by
    simp only [u2,eraseParity,run,writeBit,Function.update_of_ne hq]
  -- unnormalize
  have u2One : u2.basis L.one=false := (u2Other _ op).trans uOne
  have u2Carry : ∀q∈L.carry,u2.basis q=false := fun q hq =>
    (u2Other q (fun e => flagC L.parity (by simp) (e ▸ hq))).trans (uCarry q hq)
  let mU := m.take (measurementCount (BalancedCleanup.unnormalize L.toLayout))
  have un := BalancedCleanup.unnormalize_correct L.toLayout hw hn' u2 mU u2One u2Carry
  let u3 := run (BalancedCleanup.unnormalize L.toLayout) mU u2
  have u2Low : regValue L.low u2.basis=regValue L.low u.basis :=
    regValue_congr _ _ _ (fun q hq => u2Other q (fun e => parR (e ▸ rLow q hq)))
  have u3Low : regValue L.low u3.basis=(magnitude R).toNat := by
    have e := un.2.1
    change regValue L.low u3.basis=_ at e
    rw [e,u2Low,uLow,u2Other _ lp,uLower]
    exact low_arith R hR
  have u3Rmsb : u3.basis L.rmsb=false :=
    (un.2.2 _ rmsbLow).trans ((u2Other _ (fun e => parR (e ▸ rmsbR))).trans uRmsb)
  have u3R : regValue L.r u3.basis=(magnitude R).toNat := by
    rw [rEq,regValue_append,w.1,u3Low,single,u3Rmsb]
    simp
  have u3Lower : u3.basis L.lower=negative R :=
    (un.2.2 _ (fun h => lowR (rLow _ h))).trans ((u2Other _ lp).trans uLower)
  have u3Frame (q : Wire) (qr : q∉L.r) (ql : q≠L.lower) : u3.basis q=s.basis q := by
    have e := un.2.2 q (fun h => qr (rLow q h))
    change u3.basis q=_ at e
    rw [e]
    by_cases qp : q=L.parity
    · subst q; exact u2Par.trans sPar.symm
    · exact (u2Other q qp).trans (uFrame q qr ql qp)
  have u3Phase : u3.phase=s.phase := un.1.trans (u2Phase.trans uPhase)
  -- the old final state is the preimage of `u3` under `prepareSign`
  have FLower : F.basis L.lower=false := (FFrame _ lowR).trans sLower
  have FOne : F.basis L.one=false := (FFrame _ oneR).trans sOne
  have ps := BalancedCleanup.prepareSign_value L.toLayout hw hn' R hR F [] FR FLower
  have psPhase := FiniteUnitary.run_phase (BalancedCleanup.prepareSign L.toLayout)
    (BalancedCleanup.prepareSign_proper L.toLayout hn') F []
  have eq3 : run (BalancedCleanup.prepareSign L.toLayout) [] F=u3 := by
    apply State.extensionality
    · exact psPhase.trans (FPhase.trans u3Phase.symm)
    · funext q
      by_cases qr : q∈L.r
      · exact (regValue_eq_iff L.r _ _).mp (ps.1.trans u3R.symm) q qr
      by_cases ql : q=L.lower
      · subst q; exact ps.2.1.trans u3Lower.symm
      exact (ps.2.2 q qr ql).trans ((FFrame q qr).trans (u3Frame q qr ql).symm)
  -- assemble
  have e0 : measurementCount (eraseParity L)=0 := rfl
  rw [tail,run_append,e0,List.take_zero,List.drop_zero,run_append,run_append]
  change run (List.replicate 257 (Instr.measureX L.one [] [])) _
    (run (BalancedCleanup.prepareSign L.toLayout).reverse _ (run (BalancedCleanup.unnormalize L.toLayout) _ u2))=F
  change run (List.replicate 257 (Instr.measureX L.one [] [])) _
    (run (BalancedCleanup.prepareSign L.toLayout).reverse _ u3)=F
  rw [←eq3,run_reverse_proper _ (BalancedCleanup.prepareSign_proper L.toLayout hn')]
  exact pad_run 257 L.one _ F FOne

/-! ### Forward kernel equality -/

theorem forward_eq_old (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y) (hT : Centered (rawSum B X Y))
    (s : State) (m m' : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    run (forward L) m s=run (Q6StructuralCell.forward L) m' s := by
  have a254 : 254<L.carry.length := by rw [hw.2.2]; omega
  have ha : L.carry.getD 254 0∈L.carry := by
    rw [List.getD_eq_getElem _ _ a254]; exact List.getElem_mem _
  have oldEq : run (Q6StructuralCell.forward L) m' s=run (FifthCarry2.forward L) m' s := by
    rw [Q6StructuralCell.forward_eq L hw hn]
    exact Q6Cell.forward_eq L hw hn _ ha B X Y hx hy s m' hs hr hyr hc
  have spec := FifthCarry2.forward_correct L hw hn B X Y hx hy s m' hs hr hyr hc
  obtain ⟨Fph,FR,Fwork,FFrame⟩ := spec
  have hR : Centered (halfResult (rawSum B X Y)) :=
    (halfResult_spec _ (rawSum_bounds B X Y hx hy)).1
  have pre := prefix_facts L hw hn B X Y hx hy s
    (m.take (measurementCount (Q6StructuralCell.forwardPrefix L))) hs hr hyr hc
  obtain ⟨uPh,uR,uL,uP,uO,uC,uF⟩ := pre
  rw [oldEq,forward,run_append]
  exact tail_run L hw hn _ hR _ (parity_normalized _ hT) s _ _ _ uPh uR uL uP uO uC uF
    (hc _ (by simp [work])) (hc _ (by simp [work])) (hc _ (by simp [work])) Fph FR FFrame


/-! ### Resources of the forward kernel -/

theorem rep_facts (n : Nat) (c : Wire) :
    toffoliCount (List.replicate n (Instr.measureX c [] []))=0 ∧
    measurementCount (List.replicate n (Instr.measureX c [] []))=n ∧
    Challenge.gateSlots (List.replicate n (Instr.measureX c [] []))=n ∧
    wires (List.replicate n (Instr.measureX c [] []))⊆{c} ∧
    GatePhysical (List.replicate n (Instr.measureX c [] [])) := by
  induction n with
  | zero => simp [toffoliCount,measurementCount,Challenge.gateSlots,wires,GatePhysical]
  | succ n ih =>
    obtain ⟨h1,h2,h3,h4,h5⟩ := ih
    rw [List.replicate_succ]
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa [toffoliCount] using h1
    · simp [measurementCount,h2];omega
    · simp only [Challenge.gateSlots,List.map_cons,List.sum_cons] at h3 ⊢
      simp [Challenge.instructionSlots,h3];omega
    · intro q hq
      simp only [wires,Instr.wires,correctionWires,Finset.mem_union] at hq
      rcases hq with hq|hq
      · simpa using hq
      · exact h4 hq
    · intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · simp [RecordedQuantum.PhysicalInstr,ProperGate,correctionWires]
      · exact h5 i hi

theorem prepareCompare_counts (L : BalancedCleanup.Layout) :
    toffoliCount (BalancedCleanup.prepareCompare L)=0 ∧
    measurementCount (BalancedCleanup.prepareCompare L)=0 := by
  have rot := rotate_counts L.r
  have ys := signComplement_counts L.sign L.y
  have yl := signComplement_counts L.lower L.y
  simp only [BalancedCleanup.prepareCompare,toffoliCount_append,measurementCount_append,
    rot.2.2.1,rot.2.2.2,ys.1,ys.2,yl.1,yl.2]
  simp [toffoliCount,measurementCount]

theorem prepareSign_counts (L : BalancedCleanup.Layout) :
    toffoliCount (BalancedCleanup.prepareSign L)=0 ∧
    measurementCount (BalancedCleanup.prepareSign L)=0 := by
  have r := signComplement_counts L.lower L.r
  simp only [BalancedCleanup.prepareSign,toffoliCount_append,measurementCount_append,r.1,r.2]
  simp [toffoliCount,measurementCount]

theorem forward_counts (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (forward L)+255=toffoliCount (Q6StructuralCell.forward L) ∧
    measurementCount (forward L)=measurementCount (Q6StructuralCell.forward L) := by
  have cmp := TopCarryBorrow.program_counts (Q6Structural.carryLayout L) (Q6StructuralCell.carry_widths L hw)
  have pc := prepareCompare_counts L.toLayout
  have ps := prepareSign_counts L.toLayout
  have ex := Q6LowerExposure.expose_counts L.sign L.lower L.r0
  have rp := rep_facts 257 L.one
  simp only [forward,tail,eraseParity,Q6StructuralCell.forward,Q6StructuralCell.cleanup,
    FifthCarry2.cleanupRest,Q6Structural.compareForward,Q6StructuralCell.exposure,
    toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    cmp.1,cmp.2,pc.1,pc.2,ps.1,ps.2,ex.1,ex.2,rp.1,rp.2.1]
  simp only [toffoliCount,measurementCount]
  constructor <;> omega

theorem forward_slots (L : BalancedCircuit.Layout) (hw : L.Widths) :
    Challenge.gateSlots (forward L)≤Challenge.gateSlots (Q6StructuralCell.forward L) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have ys := Baselines.signComplement_gateSlots L.sign L.y
  have yl := Baselines.signComplement_gateSlots L.lower L.y
  have rp := (rep_facts 257 L.one).2.2.1
  simp only [forward,tail,eraseParity,Q6StructuralCell.forward,Q6StructuralCell.cleanup,
    FifthCarry2.cleanupRest,BalancedCleanup.prepareCompare,Challenge.gateSlots_append,
    Baselines.reverse_gateSlots,ys,yl,rp,w.2.2.1]
  simp only [Challenge.gateSlots,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Challenge.instructionSlots]
  omega

theorem forward_wires (L : BalancedCircuit.Layout) (hw : L.Widths) :
    wires (forward L)⊆wires (Q6StructuralCell.forward L) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have split : L.low=(L.r0::L.rtail.take 253)++[L.rtail.getD 253 0] := by
    rw [show L.low=L.r0::L.rtail from rfl]
    conv_lhs => rw [rtail_split L.rtail hw.1]
    rfl
  have rmem : L.rtail.getD 253 0∈wires (BalancedCleanup.prepareSign L.toLayout) := by
    have inR : L.rtail.getD 253 0∈L.r := by
      rw [show L.r=L.low++[L.rmsb] from rfl,split]; simp
    simp only [BalancedCleanup.prepareSign,wires_append,Finset.mem_union]
    exact Or.inr (FifthCarry2.signComplement_mem _ _ _ inR)
  have pmem : L.parity∈wires (Q6StructuralCell.forwardPrefix L) := by
    simp [Q6StructuralCell.forwardPrefix,GuardCompression.seed,wires_append,wires,Instr.wires]
  have rp := (rep_facts 257 L.one).2.2.2.1
  have omem : L.one∈wires [Instr.measureX L.one [] []] := by simp [wires,Instr.wires]
  intro q hq
  simp only [forward,tail,wires_append,wires_reverse,Finset.mem_union] at hq
  simp only [Q6StructuralCell.forward,Q6StructuralCell.cleanup,FifthCarry2.cleanupRest,
    wires_append,wires_reverse,Finset.mem_union]
  rcases hq with hq|(hq|hq|hq|hq)
  · exact Or.inl (Or.inl hq)
  · have h2 : q=L.rtail.getD 253 0 ∨ q=L.parity := by
      simp only [eraseParity,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
      tauto
    rcases h2 with h2|h2 <;> subst q
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr rmem))))
    · exact Or.inl (Or.inl pmem)
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hq))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hq))))
  · have e := Finset.mem_singleton.mp (rp hq)
    subst q
    exact Or.inr omem

theorem forward_physical (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (old : GatePhysical (Q6StructuralCell.forward L)) : GatePhysical (forward L) := by
  simp only [Q6StructuralCell.forward,Q6StructuralCell.cleanup,FifthCarry2.cleanupRest,
    gatePhysical_append] at old
  have split : L.low=(L.r0::L.rtail.take 253)++[L.rtail.getD 253 0] := by
    rw [show L.low=L.r0::L.rtail from rfl]
    conv_lhs => rw [rtail_split L.rtail hw.1]
    rfl
  have ne : L.rtail.getD 253 0≠L.parity := by
    intro e
    have hr : L.parity∉L.r := fun h => flagAway L hn L.parity (by simp) (by simp [h])
    apply hr
    rw [←e,show L.r=L.low++[L.rmsb] from rfl,split]
    simp
  have er : GatePhysical (eraseParity L) := by
    unfold eraseParity
    generalize L.rtail.getD 253 0=b at ne ⊢
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl
    · exact ne
    · trivial
  have rp := (rep_facts 257 L.one).2.2.2.2
  simp only [forward,tail,gatePhysical_append]
  exact ⟨by tauto,er,by tauto,by tauto,rp⟩


/-! ### The half (sign flips around the forward kernel) -/

def half (w : Nat → Wire) (sign : Wire) : Program :=
  [.X sign]++forward (Q6EndpointCell.ports w sign)++[.X sign]

/-- Complete `State` equality with the generic divide half, for every incoming phase and
record list, whenever one payload word is zero. -/
theorem half_run_eq (w : Nat → Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (origin : BasisState) (hc : ∀q∈work (Q6EndpointCell.ports w sign),origin q=false)
    (X Y : Fp) (hz : X=0 ∨ Y=0) (s : State) (m : List Bool)
    (h : PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
      (centerWord X) (centerWord Y) s.basis) :
    run (half w sign) m s=run (Q6EndpointCell.half true w sign) m s := by
  let L := Q6EndpointCell.ports w sign
  have hw : L.Widths := Q6EndpointCell.ports_widths w sign
  have sg : L.sign=sign := rfl
  have aw := flagAway L hn L.sign (by simp)
  have sa : L.sign∉L.r ∧ L.sign∉L.y :=
    ⟨fun h => aw (by simp [h]),fun h => aw (by simp [h])⟩
  rw [Q6EndpointCell.half_true]
  unfold half
  rw [List.append_assoc,List.append_assoc]
  apply LaneI.seq_eq _ _ _ _ s m rfl rfl
  generalize eu : run [.X sign] (m.take (measurementCount [.X sign])) s=u
  have us := BalancedCleanupOffset.x_run sign s (m.take (measurementCount [.X sign]))
  rw [eu] at us
  have uf (q : Wire) (hq : q≠sign) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ug : u.basis sign= !origin sign := by
    rw [us]
    simp only [writeBit,Function.update_self]
    rw [h.2.2 sign sa.1 sa.2]
  have uv (r : List Wire) (a : sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => uf q (fun e => a (e ▸ hq)))
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout hw).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout hw).2.2.1,centerWord_decode]
  have uc : ∀q∈work L,u.basis q=false := by
    intro q hq
    have a := OwnQ6Core5.work_away L hn q hq
    exact (uf q (fun e => OwnQ6Core5.sign_work L hn (by rw [sg,←e]; exact hq))).trans
      ((h.2.2 q a.1 a.2).trans (hc q hq))
  rw [run_append,run_append]
  have qx : ∀ (r1 r2 : List Bool) (t : State), run [Instr.X sign] r1 t=run [Instr.X sign] r2 t := by
    intro r1 r2 t; rfl
  rw [qx _ (List.drop (measurementCount (Q6StructuralCell.forward L)) _),
    forward_eq_old L hw hn (!origin L.sign) (centerFp X) (centerFp Y)
      (centerFp_bounds X) (centerFp_bounds Y) (centered_of_zero _ X Y hz) u _ _ ug ur uy uc]

theorem half_counts (w : Nat → Wire) (sign : Wire) :
    toffoliCount (half w sign)+255=toffoliCount (Q6EndpointCell.half true w sign) ∧
    measurementCount (half w sign)=measurementCount (Q6EndpointCell.half true w sign) := by
  have k := forward_counts (Q6EndpointCell.ports w sign) (Q6EndpointCell.ports_widths w sign)
  rw [Q6EndpointCell.half_true]
  simp only [half,toffoliCount_append,measurementCount_append]
  simp only [toffoliCount,measurementCount]
  constructor <;> omega

theorem half_slots (w : Nat → Wire) (sign : Wire) :
    Challenge.gateSlots (half w sign)≤Challenge.gateSlots (Q6EndpointCell.half true w sign) := by
  have k := forward_slots (Q6EndpointCell.ports w sign) (Q6EndpointCell.ports_widths w sign)
  rw [Q6EndpointCell.half_true]
  simp only [half,Challenge.gateSlots_append]
  omega

theorem half_wires (w : Nat → Wire) (sign : Wire) :
    wires (FirstZero.half w sign)⊆wires (Q6EndpointCell.half true w sign) := by
  intro q hq
  have hw : (Q6EndpointCell.ports w sign).Widths := Q6EndpointCell.ports_widths w sign
  rw [Q6EndpointCell.half_true]
  unfold FirstZero.half at hq
  simp only [wires_append,Finset.mem_union] at hq ⊢
  rcases hq with (hq|hq)|hq
  · exact Or.inl (Or.inl hq)
  · exact Or.inl (Or.inr (forward_wires (Q6EndpointCell.ports w sign) hw hq))
  · exact Or.inr hq

/-! ### The loaned, rebound window and the first cell -/

def halfWindow : Program :=
  ControlLoan1589.loanWindow (base 1) (base 2409) (base 516)
    (renameProgram (Equiv.swap (base 719) (base 1032)) (half base (base 2409)))

def oldHalfWindow : Program :=
  ControlLoan1589.loanWindow (base 1) (base 2409) (base 516)
    (renameProgram (Equiv.swap (base 719) (base 1032)) (Q6EndpointCell.half true base (base 2409)))

/-- The new first divide cell (letter 1, active trit 1, hole trit 4). -/
def cell : Program := halfWindow++SW.selW (base 1029) (base 2409) FrontierSW1591.swapBody

/-- The generic cell it replaces (`Rolling1588.cell true 0 1 4`, unfolded). -/
def oldCell : Program := oldHalfWindow++SW.selW (base 1029) (base 2409) FrontierSW1591.swapBody

private theorem pull_swap_invol (a b : Wire) (s : State) :
    pullState (Equiv.swap a b) (pullState (Equiv.swap a b) s)=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (Equiv.swap a b (Equiv.swap a b q))=s.basis q
    rw [Equiv.swap_apply_self]

theorem rename_congr (a b : Wire) (P Q : Program) (s : State) (r : List Bool)
    (ha : s.basis a=false) (hb : s.basis b=false) (same : run P r s=run Q r s) :
    run (renameProgram (Equiv.swap a b) P) r s=run (renameProgram (Equiv.swap a b) Q) r s := by
  have e1 := ECDSAAdd.run_rename (Equiv.swap a b) (Equiv.swap a b).injective P r s
  have e2 := ECDSAAdd.run_rename (Equiv.swap a b) (Equiv.swap a b).injective Q r s
  rw [pullState_zero_swap a b s ha hb] at e1 e2
  have both := congrArg (pullState (Equiv.swap a b)) (e1.trans (same.trans e2.symm))
  simpa only [pull_swap_invol] using both

theorem loan_congr (g flag c : Wire) (P Q : Program) (s : State) (m : List Bool)
    (count : measurementCount P=measurementCount Q)
    (same : ∀r,run (renameProgram (Equiv.swap c g) P) r (run [.CX g flag,.CX flag g] [] s)=
      run (renameProgram (Equiv.swap c g) Q) r (run [.CX g flag,.CX flag g] [] s)) :
    run (ControlLoan1589.loanWindow g flag c P) m s=
      run (ControlLoan1589.loanWindow g flag c Q) m s := by
  have hc : measurementCount (renameProgram (Equiv.swap c g) P)=
      measurementCount (renameProgram (Equiv.swap c g) Q) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,count]
  have h0 : measurementCount [Instr.CX g flag,.CX flag g]=0 := rfl
  have shape (M : Program) : run ([.CX g flag,.CX flag g]++M++[.CX flag g,.measureX flag [] [.Z g]]) m s=
      run [.CX flag g,.measureX flag [] [.Z g]] (m.drop (measurementCount M))
        (run M (m.take (measurementCount M)) (run [.CX g flag,.CX flag g] [] s)) := by
    rw [run_append,run_append,measurementCount_append,h0,Nat.zero_add]
    simp only [List.take_take,Nat.min_self,Nat.zero_le,Nat.min_eq_left,List.take_zero,
      List.drop_zero]
  unfold ControlLoan1589.loanWindow
  rw [shape,shape,hc,same]

private theorem ports_nodup : (Q6EndpointCell.ports base (base 2409)).wires.Nodup :=
  Q6EndpointCell.ports_nodup_injective base (base 2409) base_injective (by
    intro member
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp member
    have same := base_injective eq
    have bound := Q6EndpointCell.ids_bound i hi
    omega)

theorem halfWindow_run_eq (X Y : Fp) (hz : X=0 ∨ Y=0) (state : State) (records : List Bool)
    (clean : Q6EndpointCell.Clean base state.basis)
    (rValue : regValue (Q6EndpointCell.ports base (base 2409)).r state.basis=centerWord X)
    (yValue : regValue (Q6EndpointCell.ports base (base 2409)).y state.basis=centerWord Y)
    (flagIn : state.basis (base 2409)=false) (holeIn : state.basis (base 1032)=false) :
    run halfWindow records state=run oldHalfWindow records state := by
  apply loan_congr
  · rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2]
    exact (half_counts base (base 2409)).2
  · intro r
    let a := run [.CX (base 1) (base 2409),.CX (base 2409) (base 1)] [] state
    have n12 : base 1≠base 2409 := fun e => by have := base_injective e; omega
    have aOther (q : Wire) (h1 : q≠base 1) (h2 : q≠base 2409) : a.basis q=state.basis q := by
      simp only [a,run,writeBit,Function.update_of_ne h1,Function.update_of_ne h2]
    have a1 : a.basis (base 1)=false := by
      simp only [a,run,writeBit,Function.update_self,Function.update_of_ne n12,
        Function.update_of_ne (Ne.symm n12),flagIn]
      cases state.basis (base 1) <;> rfl
    have workAway (q : Wire) (hq : q∈Q6EndpointCell.workIds.map base) : q≠base 1 ∧ q≠base 2409 := by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [Q6EndpointCell.workIds,List.mem_append,List.mem_cons,List.not_mem_nil,
        List.mem_range'_1,or_false] at hi
      constructor <;> intro e <;> have := base_injective e <;> omega
    have aClean : Q6EndpointCell.Clean base a.basis := fun q hq =>
      (aOther q (workAway q hq).1 (workAway q hq).2).trans (clean q hq)
    have regAway (r : List Wire) (hr : r=(Q6EndpointCell.ports base (base 2409)).r ∨
        r=(Q6EndpointCell.ports base (base 2409)).y) (q : Wire) (hq : q∈r) : q≠base 1 ∧ q≠base 2409 := by
      rcases hr with rfl|rfl
      · rw [Q6EndpointCell.ports_r,balancedSharedPorts_r] at hq
        exact ⟨fun e => OwnPlusHost.not_block 1 2056 256 (by omega) (e ▸ hq),
          fun e => OwnPlusHost.not_block 2409 2056 256 (by omega) (e ▸ hq)⟩
      · rw [Q6EndpointCell.ports_y,balancedSharedPorts_y] at hq
        exact ⟨fun e => OwnPlusHost.not_block 1 770 256 (by omega) (e ▸ hq),
          fun e => OwnPlusHost.not_block 2409 770 256 (by omega) (e ▸ hq)⟩
    have aR : regValue (Q6EndpointCell.ports base (base 2409)).r a.basis=centerWord X :=
      (regValue_congr _ _ _ (fun q hq => aOther q (regAway _ (Or.inl rfl) q hq).1
        (regAway _ (Or.inl rfl) q hq).2)).trans rValue
    have aY : regValue (Q6EndpointCell.ports base (base 2409)).y a.basis=centerWord Y :=
      (regValue_congr _ _ _ (fun q hq => aOther q (regAway _ (Or.inr rfl) q hq).1
        (regAway _ (Or.inr rfl) q hq).2)).trans yValue
    have m516 : base 516∈Q6EndpointCell.workIds.map base :=
      List.mem_map.mpr ⟨516,by simp [Q6EndpointCell.workIds,List.mem_range'_1],rfl⟩
    have m719 : base 719∈Q6EndpointCell.workIds.map base :=
      List.mem_map.mpr ⟨719,by simp [Q6EndpointCell.workIds,List.mem_range'_1],rfl⟩
    have n1032 : base 1032≠base 1 ∧ base 1032≠base 2409 :=
      ⟨fun e => by have := base_injective e; omega,fun e => by have := base_injective e; omega⟩
    apply rename_congr (base 516) (base 1) _ _ a r (aClean _ m516) a1
    apply rename_congr (base 719) (base 1032) _ _ a r (aClean _ m719)
      ((aOther _ n1032.1 n1032.2).trans holeIn)
    exact half_run_eq base (base 2409) ports_nodup a.basis
      (Q6EndpointCell.clean_work base (base 2409) a.basis aClean) X Y hz a r
      ⟨aR,aY,fun _ _ _ => rfl⟩

theorem cell_run_eq (X Y : Fp) (hz : X=0 ∨ Y=0) (state : State) (records : List Bool)
    (clean : Q6EndpointCell.Clean base state.basis)
    (rValue : regValue (Q6EndpointCell.ports base (base 2409)).r state.basis=centerWord X)
    (yValue : regValue (Q6EndpointCell.ports base (base 2409)).y state.basis=centerWord Y)
    (flagIn : state.basis (base 2409)=false) (holeIn : state.basis (base 1032)=false) :
    run cell records state=run oldCell records state := by
  have count : measurementCount halfWindow=measurementCount oldHalfWindow := by
    simp only [halfWindow,oldHalfWindow,ControlLoan1589.loanWindow,measurementCount_append,
      (renameProgram_counts _ _).2,(half_counts base (base 2409)).2]
  unfold cell oldCell
  rw [run_append,run_append,count,
    halfWindow_run_eq X Y hz state _ clean rValue yValue flagIn holeIn]

theorem cell_counts :
    toffoliCount cell+255=toffoliCount oldCell ∧ measurementCount cell=measurementCount oldCell ∧
      Challenge.gateSlots cell≤Challenge.gateSlots oldCell := by
  have k := half_counts base (base 2409)
  have sl := half_slots base (base 2409)
  simp only [cell,oldCell,halfWindow,oldHalfWindow,ControlLoan1589.loanWindow,
    toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem cell_wires : wires FirstZero.cell⊆wires FirstZero.oldCell := by
  have k : wires (FirstZero.half base (base 2409))⊆wires (Q6EndpointCell.half true base (base 2409)) :=
    half_wires base (base 2409)
  have mono (f : Wire → Wire) (P Q : Program) (h : wires P⊆wires Q) :
      wires (renameProgram f P)⊆wires (renameProgram f Q) := by
    rw [renameProgram_support,renameProgram_support]
    exact Finset.image_subset_image h
  have rn := mono (Equiv.swap (base 516) (base 1)) _ _
    (mono (Equiv.swap (base 719) (base 1032)) _ _ k)
  simp only [cell,oldCell,halfWindow,oldHalfWindow,ControlLoan1589.loanWindow,wires_append]
  intro q hq
  simp only [Finset.mem_union] at hq ⊢
  rcases hq with ((hq|hq)|hq)|hq
  · exact Or.inl (Or.inl (Or.inl hq))
  · exact Or.inl (Or.inl (Or.inr (rn hq)))
  · exact Or.inl (Or.inr hq)
  · exact Or.inr hq

theorem cell_physical (old : GatePhysical oldCell) : GatePhysical cell := by
  have hn := ports_nodup
  have hw := Q6EndpointCell.ports_widths base (base 2409)
  have kernel := Q6EndpointCell.kernel_physical true base base_injective
  simp only [OwnQ6Core5.kernel,if_true] at kernel
  have fwd := forward_physical _ hw hn kernel
  have x : GatePhysical [.X (base 2409)] := by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  have hf : GatePhysical (half base (base 2409)) := by
    simp only [half,gatePhysical_append]
    exact ⟨⟨x,fwd⟩,x⟩
  have win : GatePhysical halfWindow :=
    ControlLoan1589.loanWindow_physical _ _ _ _ (fun e => by have := base_injective e; omega)
      (gatePhysical_rename _ (Equiv.swap (base 719) (base 1032)).injective _ hf)
  simp only [oldCell,cell,gatePhysical_append] at old ⊢
  exact ⟨win,old.2⟩


/-- The first-packet payload hypothesis of both stages: the multiply stage needs the old
second-word zero after the replay; the divide stage now needs its incoming second word zero. -/
def FirstHyp (divide : Bool) (origin : BasisState) (X Y : Fp) : Prop :=
  (divide=false → (Replay5.firstPayload divide origin (X,Y)).2=0) ∧ (divide=true → Y=0)


/-- Toffoli saving of the divide first packet (an atom for `omega` in the resource chain). -/
def saving (divide : Bool) : Nat := if divide then 255 else 0

end ECDSAAdd.Entrant.FirstZero
