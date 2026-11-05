import ECDSAAdd.Submission.Entrant.MainA
import ECDSAAdd.Arithmetic.BalancedFieldCircuitProof
import ECDSAAdd.Arithmetic.BalancedInverseComposeProof
import ECDSAAdd.Framework.GateInverse
import ECDSAAdd.Arithmetic.MeasuredGateSupport

-- ===== merged module ECDSAAdd.Submission.Entrant.FirstZero =====
section
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
end

-- ===== merged module ECDSAAdd.Submission.Entrant.TerminalGraph =====
section
/-! Terminal graph decoder for the divide endpoint, from ArthurOstapenko's submission baaabf50
(`TerminalGraph.lean` of commit ab9dd95), sections GraphCell … EndpointCaller, TerminalSupportOnly,
TerminalFootprint and TerminalPhysicalOnly copied unchanged. -/

-- TERMINAL GRAPH COMPONENT GraphCell
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def xorSum (a b cin out : Wire) : Program := [.CX a out,.CX b out,.CX cin out]

theorem xorSum_run (a b cin out : Wire) (ha : a≠out) (hb : b≠out) (hc : cin≠out)
    (s : State) (m : List Bool) :
    run (xorSum a b cin out) m s =
      ⟨s.phase,writeBit s.basis out (s.basis out ^^ sumBit (s.basis a) (s.basis b) (s.basis cin))⟩ := by
  simp only [xorSum,run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq:q=out
  · subst q
    simp [writeBit,Function.update,ha,hb,hc,sumBit,Bool.xor_assoc]
  · simp [writeBit,Function.update,hq]

/-- Decode a supplied sum bit into a clean carry wire using only CNOTs. -/
theorem extractCarry_run (a b out carry : Wire)
    (ha : a≠carry) (hb : b≠carry) (ho : out≠carry)
    (s : State) (m : List Bool) (clean : s.basis carry=false) (C : Bool)
    (sum : s.basis out=sumBit (s.basis a) (s.basis b) C) :
    run (xorSum a b out carry) m s=⟨s.phase,writeBit s.basis carry C⟩ := by
  rw [xorSum_run a b out carry ha hb ho,clean,sum]
  congr 2
  cases s.basis a <;> cases s.basis b <;> cases C <;> rfl

def eraseGraphCell (a b cin out carry : Wire) : Program :=
  xorSum a b cin out ++ eraseCarry a b cin carry

/-- A supplied sum/majority graph is erased with zero T, for every measurement tape. -/
theorem eraseGraphCell_run (a b cin out carry : Wire)
    (ha : a≠out) (hb : b≠out) (hc : cin≠out)
    (hak : a≠carry) (hbk : b≠carry) (hck : cin≠carry)
    (hok : out≠carry) (s : State) (m : List Bool)
    (sum : s.basis out=sumBit (s.basis a) (s.basis b) (s.basis cin))
    (maj : s.basis carry=carryBit (s.basis a) (s.basis b) (s.basis cin)) :
    run (eraseGraphCell a b cin out carry) m s=
      ⟨s.phase,writeBit (writeBit s.basis out false) carry false⟩ := by
  have x : run (xorSum a b cin out) m s=⟨s.phase,writeBit s.basis out false⟩ := by
    rw [xorSum_run a b cin out ha hb hc,sum]
    simp
  let t : State:=⟨s.phase,writeBit s.basis out false⟩
  have tm : t.basis carry=carryBit (t.basis a) (t.basis b) (t.basis cin) := by
    simpa only [t,writeBit,Function.update_of_ne ha,Function.update_of_ne hb,
      Function.update_of_ne hc,Function.update_of_ne hok.symm] using maj
  rw [eraseGraphCell,run_append,run_take,x]
  simpa only [t] using eraseCarry_correct a b cin carry hak hbk hck t tm
    (m.drop (measurementCount (xorSum a b cin out)))

theorem graphCell_resources (a b cin out carry : Wire) :
    toffoliCount (eraseGraphCell a b cin out carry)=0 ∧
    measurementCount (eraseGraphCell a b cin out carry)=1 := by
  simp [eraseGraphCell,xorSum,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,eraseCarry]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AffineStream
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def parity (xs : List Wire) (b : BasisState) : Bool:=xs.foldr (fun x t=>b x ^^ t) false
def xorList (xs : List Wire) (target : Wire) : Program:=xs.map (fun x=>.CX x target)

theorem parity_congr (xs : List Wire) (b b' : BasisState) (h : ∀q∈xs,b q=b' q) :
    parity xs b=parity xs b' := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    change (b x ^^ parity xs b)=(b' x ^^ parity xs b')
    rw [h x (by simp),ih (fun q hq=>h q (by simp [hq]))]

theorem xorList_run (xs : List Wire) (target : Wire) (away : target∉xs)
    (s : State) (m : List Bool) :
    run (xorList xs target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^ parity xs s.basis)⟩ := by
  induction xs generalizing s with
  | nil=>
    simp only [xorList,List.map_nil,run,parity,List.foldr_nil,Bool.xor_false]
    cases s with
    | mk phase basis =>
      apply congrArg (State.mk phase)
      funext q
      by_cases hq:q=target <;> simp [writeBit,hq]
  | cons x xs ih=>
    have xt:x≠target:=fun e=>away (by simp [e])
    have tail:target∉xs:=fun h=>away (by simp [h])
    let t : State:=⟨s.phase,writeBit s.basis target (s.basis target ^^ s.basis x)⟩
    have pa:parity xs t.basis=parity xs s.basis:=parity_congr _ _ _ (by
      intro q hq
      have nq:q≠target:=fun e=>tail (e ▸ hq)
      simp [t,writeBit,nq])
    simp only [xorList,List.map_cons,run]
    change run (xorList xs target) m t=_
    rw [ih tail t,pa]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq:q=target
    · subst q
      simp [t,writeBit,parity,Bool.xor_assoc]
    · simp [t,writeBit,hq]

/-- Move a supplied output into a consumed clean target slot, removing its affine sum.
The full state map is Clifford and holds without any arithmetic-graph premise. -/
def streamStage (xs : List Wire) (prev out : Wire) : Program:=
  [.CX out prev]++xorList xs prev++xorList xs out++[.CX prev out]

theorem streamStage_run (xs : List Wire) (prev out : Wire)
    (ne : prev≠out) (ap : prev∉xs) (ao : out∉xs)
    (s : State) (m : List Bool) (clean : s.basis prev=false) :
    run (streamStage xs prev out) m s=
      ⟨s.phase,writeBit (writeBit s.basis prev (s.basis out ^^ parity xs s.basis)) out false⟩ := by
  let t : State:=⟨s.phase,writeBit s.basis prev (s.basis out)⟩
  have first (r : List Bool) : run [.CX out prev] r s=t:=by simp [run,t,writeBit,clean]
  have par1:parity xs t.basis=parity xs s.basis:=parity_congr _ _ _ (by
    intro q hq;have nq:q≠prev:=fun e=>ap (e ▸ hq);simp [t,writeBit,nq])
  let u : State:=⟨s.phase,writeBit t.basis prev (s.basis out ^^ parity xs s.basis)⟩
  have second (r : List Bool) : run (xorList xs prev) r t=u:=by
    rw [xorList_run xs prev ap,par1]
    simp [u,t,writeBit]
  have par2:parity xs u.basis=parity xs s.basis:=parity_congr _ _ _ (by
    intro q hq;have nq:q≠prev:=fun e=>ap (e ▸ hq);simp [u,t,writeBit,nq])
  let v : State:=⟨s.phase,writeBit u.basis out (s.basis out ^^ parity xs s.basis)⟩
  have third (r : List Bool) : run (xorList xs out) r u=v:=by
    rw [xorList_run xs out ao,par2]
    simp [v,u,t,writeBit,Ne.symm ne]
  have final:run [.CX prev out] m v=
      ⟨s.phase,writeBit (writeBit s.basis prev (s.basis out ^^ parity xs s.basis)) out false⟩ := by
    simp only [run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hp:q=prev
    · subst q;simp [v,u,t,writeBit,ne]
    · by_cases ho:q=out
      · subst q;simp [v,u,t,writeBit,ne,Ne.symm ne]
      · simp [v,u,t,writeBit,hp,ho]
  have zero (xs : List Wire) (target : Wire) : measurementCount (xorList xs target)=0:=by
    induction xs with
    | nil=>rfl
    | cons x xs ih=>simpa only [xorList,List.map_cons,measurementCount,List.map_cons,List.sum_cons,Nat.zero_add] using ih
  rw [streamStage]
  simp only [List.append_assoc,run_append,run_take,measurementCount,List.sum_cons,
    List.sum_nil,Nat.zero_add,List.take_zero,List.drop_zero,zero]
  rw [first,second,third]
  exact final
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT ControlledCompare
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def selectedBorrow (bit : Bool) (x cin carry control target : Wire) : Program :=
  constantBorrow bit x cin carry ++ [.CCX control carry target] ++ constantBorrowErase bit x cin carry

theorem selectedBorrow_counts (bit : Bool) (x cin carry control target : Wire) :
    toffoliCount (selectedBorrow bit x cin carry control target)=2 ∧
    measurementCount (selectedBorrow bit x cin carry control target)=1 := by
  have c:=constantBorrow_counts bit x cin carry
  simp only [selectedBorrow,toffoliCount_append,measurementCount_append,c.1,c.2.1,c.2.2.1,c.2.2.2]
  simp [toffoliCount,measurementCount]

def compareSelected : List Wire → List Wire → Wire → Wire → Wire → Nat → Program
  | x::x'::xs,c::cs,cin,control,target,k =>
      constantBorrow (decide (k%2=1)) x cin c ++
        compareSelected (x'::xs) cs c control target (k/2) ++
          constantBorrowErase (decide (k%2=1)) x cin c
  | [x],c::_,cin,control,target,k => selectedBorrow (decide (k%2=1)) x cin c control target
  | _,_,_,_,_,_ => []

theorem compareSelected_counts (xs carry : List Wire) (cin control target : Wire) (k : Nat)
    (hn : 0<xs.length) (hc : carry.length=xs.length) :
    toffoliCount (compareSelected xs carry cin control target k)=xs.length+1 ∧
    measurementCount (compareSelected xs carry cin control target k)=xs.length := by
  induction xs generalizing carry cin k with
  | nil => simp at hn
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases carry with
      | nil => simp at hc
      | cons c cs => simpa only [compareSelected,List.length_cons,List.length_nil] using selectedBorrow_counts (decide (k%2=1)) x cin c control target
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have r:=ih cs c (k/2) (by simp) (by simpa using hc)
        have b:=constantBorrow_counts (decide (k%2=1)) x cin c
        rw [compareSelected]
        constructor
        · simp only [toffoliCount_append,b.1,b.2.2.1,r.1,List.length_cons];omega
        · simp only [measurementCount_append,b.2.1,b.2.2.2,r.2,List.length_cons];omega

theorem selectedBorrow_correct (bit : Bool) (x cin carry control target : Wire)
    (hn : [x,cin,carry,control,target].Nodup) (s : State) (m : List Bool)
    (zero : s.basis carry=false) :
    run (selectedBorrow bit x cin carry control target) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (s.basis target ^^ (s.basis control && carryBit (!s.basis x) bit (s.basis cin)))) carry false⟩ := by
  have nd : [x,cin,carry].Nodup:=hn.sublist (by simp)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at hn
  obtain ⟨⟨hxi,hxc,hxb,hxt⟩,⟨hic,hib,hit⟩,⟨hcb,hct⟩,hbt⟩:=hn
  let K:=carryBit (!s.basis x) bit (s.basis cin)
  let s1 : State:=⟨s.phase,writeBit s.basis carry K⟩
  have first (r : List Bool) : run (constantBorrow bit x cin carry) r s=s1 := by
    rw [constantBorrow_correct bit x cin carry nd,zero]
    simp [s1,K]
  let s2 : State:=⟨s.phase,writeBit s1.basis target (s.basis target ^^ (s.basis control && K))⟩
  have second (r : List Bool) : run [.CCX control carry target] r s1=s2 := by
    simp [s1,s2,run,writeBit,(Ne.symm hct),(Ne.symm hcb)]
  have final (r : List Bool) : run (constantBorrowErase bit x cin carry) r s2=
      ⟨s.phase,writeBit s2.basis carry false⟩ := by
    have km : s2.basis carry=carryBit (!s2.basis x) bit (s2.basis cin) := by
      simp [s2,s1,writeBit,hct,hxt,hit,hxc,hic,K]
    exact constantBorrowErase_correct bit x cin carry nd s2 r km
  have counts:=constantBorrow_counts bit x cin carry
  rw [selectedBorrow]
  simp only [List.append_assoc,run_append,run_take,counts.2.1,List.take_zero,List.drop_zero]
  rw [first,second,final]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq:q=carry
  · subst q;simp [s1,s2,writeBit]
  · by_cases ht:q=target
    · subst q;simp [s1,s2,writeBit,(Ne.symm hct),K]
    · simp [s1,s2,writeBit,hq,ht]

theorem compareSelected_correct (xs carry : List Wire) (cin control target : Wire) (k : Nat)
    (hn : (control::target::cin::(xs++carry)).Nodup) (hpos : 0<xs.length)
    (hc : carry.length=xs.length) (hk : k<2^xs.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    (run (compareSelected xs carry cin control target k) m s).phase=s.phase ∧
    (∀q,q≠target → (run (compareSelected xs carry cin control target k) m s).basis q=s.basis q) ∧
    (run (compareSelected xs carry cin control target k) m s).basis target=
      (s.basis target ^^ (s.basis control && decide (regValue xs s.basis<k+(s.basis cin).toNat))) := by
  induction xs generalizing carry cin k s m with
  | nil => simp at hpos
  | cons x xs ih =>
    have cnt:=List.nodup_iff_count.mp hn
    have htx : target≠x := by
      intro bad;have h:=cnt target;subst x
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    have htci : target≠cin := by
      intro bad;have h:=cnt target;subst cin
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    have hxc : x≠cin := by
      intro bad;have h:=cnt cin;subst x
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    cases xs with
    | nil =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have nd : [x,cin,c,control,target].Nodup := by
          apply List.nodup_iff_count.mpr;intro q;have h:=cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have htc : target≠c := by
          intro bad;have h:=cnt target;subst c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have zero:=hclean c (by simp)
        rw [compareSelected,selectedBorrow_correct _ _ _ _ _ _ nd s m zero]
        refine ⟨rfl,?_,?_⟩
        · intro q hq
          by_cases hqc:q=c
          · subst q;simp [writeBit,zero]
          · simp [writeBit,hqc,hq]
        · have small : k<2 := by simpa using hk
          by_cases h0:k=0
          · subst k
            cases hx:s.basis x <;> cases hi:s.basis cin <;> cases hb:s.basis control <;>
              simp [writeBit,htc,regValue,carryBit,hx,hi,hb]
          · have h1:k=1:=by omega
            subst k
            cases hx:s.basis x <;> cases hi:s.basis cin <;> cases hb:s.basis control <;>
              simp [writeBit,htc,regValue,carryBit,hx,hi,hb]
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have htc : target≠c := by
          intro bad; have h := cnt target; subst c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hbc : control≠c := by
          intro bad; have h:=cnt control;subst c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hxc' : x≠c := by
          intro bad; have h := cnt c; subst x
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hcic : cin≠c := by
          intro bad; have h := cnt c; subst cin
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hctail : c∉x'::xs := by
          intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
          omega
        have hccs : c∉cs := by
          intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have nd : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr; intro q; have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have nd' : (control::target::c::((x'::xs)++cs)).Nodup := by
          apply List.nodup_iff_count.mpr; intro q; have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        let bit := decide (k%2=1)
        let K := carryBit (!s.basis x) bit (s.basis cin)
        let s1 : State := ⟨s.phase,writeBit s.basis c K⟩
        have keep (q : Wire) (hq : q≠c) : s1.basis q=s.basis q := by simp [s1,writeBit,hq]
        have zero := hclean c (by simp)
        have first (record : List Bool) : run (constantBorrow bit x cin c) record s=s1 := by
          rw [constantBorrow_correct _ _ _ _ nd]
          simp [s1,K,zero]
        have clean' : ∀q∈cs,s1.basis q=false := by
          intro q hq
          rw [keep q (fun bad => hccs (bad ▸ hq))]
          exact hclean q (by simp [hq])
        have high : k/2<2^(x'::xs).length := by
          simp only [List.length_cons,Nat.pow_succ] at hk ⊢
          omega
        obtain ⟨hp,he,hv⟩ := ih cs c (k/2) nd' (by simp) (by simpa using hc) high s1 m clean'
        let t := run (compareSelected (x'::xs) cs c control target (k/2)) m s1
        have tx : t.basis x=s.basis x := (he x htx.symm).trans (keep x hxc')
        have ti : t.basis cin=s.basis cin := (he cin htci.symm).trans (keep cin hcic)
        have tk : t.basis c=K := by rw [he c htc.symm]; simp [s1,writeBit]
        have clear (record : List Bool) : run (constantBorrowErase bit x cin c) record t=
            ⟨t.phase,writeBit t.basis c false⟩ := by
          apply constantBorrowErase_correct _ _ _ _ nd t record
          rw [tx,ti,tk]
        have counts := constantBorrow_counts (decide (k%2=1)) x cin c
        rw [compareSelected]
        simp only [List.append_assoc,run_append,run_take,counts.2.1,List.take_zero,List.drop_zero]
        rw [first]
        change (run (constantBorrowErase bit x cin c) _ t).phase=_ ∧ _
        rw [clear]
        refine ⟨hp,?_,?_⟩
        · intro q hq
          by_cases hqc : q=c
          · subst q; simp [writeBit,zero]
          · simp only [writeBit,Function.update_of_ne hqc]
            exact (he q hq).trans (keep q hqc)
        · simp only [writeBit,Function.update_of_ne htc]
          rw [hv,keep target htc,keep control hbc]
          have v : regValue (x'::xs) s1.basis=regValue (x'::xs) s.basis :=
            regValue_congr _ _ _ (fun q hq => keep q (fun bad => hctail (bad ▸ hq)))
          have carryVal : s1.basis c=K := by simp [s1,writeBit]
          rw [v,carryVal]
          have split : bit.toNat+2*(k/2)=k := by
            have e := Nat.mod_add_div k 2
            have b := Nat.mod_lt k (by decide : 0<2)
            by_cases odd : k%2=1 <;> simp [bit,odd] <;> omega
          have thr := borrow_threshold (s.basis x) bit (s.basis cin)
            (regValue (x'::xs) s.basis) (k/2)
          rw [split] at thr
          have pred : decide (regValue (x::x'::xs) s.basis<k+(s.basis cin).toNat)=
              decide (regValue (x'::xs) s.basis<k/2+K.toNat) := by
            apply decide_eq_decide.mpr
            simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,K] using thr
          rw [pred]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Emitter
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

structure DecoderLayout where
  y : List Wire
  r : List Wire
  carry : List Wire
  sigma : Wire
  h : Wire
  bias : Wire

def DecoderLayout.Widths (L : DecoderLayout) : Prop:=L.y.length=256 ∧ L.r.length=256 ∧ L.carry.length=255

def DecoderLayout.Y (L : DecoderLayout) (i : Nat):Wire:=L.y.getD i 0
def DecoderLayout.R (L : DecoderLayout) (i : Nat):Wire:=L.r.getD i 0
def DecoderLayout.A (L : DecoderLayout) (i : Nat):Wire:=L.carry.getD i 0

def rawSources (L : DecoderLayout) (i : Nat) : List Wire:=
 if i=0 then [L.Y 0]
 else if i<255 then [L.Y (i-1),L.Y i,L.sigma,L.A (i-1)]
 else [L.Y 254,L.sigma,L.A 254]

def correction (L : DecoderLayout) (i : Nat) : MappedBit:=
 if i=1 then ⟨some L.bias,false⟩
 else if Nat.testBit (2^32+977) i then ⟨some L.h,false⟩ else ⟨none,false⟩

def correctionSources (L : DecoderLayout) (i : Nat) : List Wire:=
 (correction L i).wire.toList

def addCarry (L : DecoderLayout) (i : Nat) : Program:=
 if i=0 then [.CX L.sigma (L.Y 0),.CCX L.sigma (L.Y 0) (L.A 0),.CX L.sigma (L.Y 0)]
 else [.CX L.sigma (L.Y i)]++majority (L.Y (i-1)) (L.Y i) (L.A (i-1)) (L.A i)++[.CX L.sigma (L.Y i)]

def eraseAddCarry (L : DecoderLayout) (i : Nat) : Program:=
 if i=0 then [.CX L.sigma (L.Y 0),.measureX (L.A 0) [] [.CZ L.sigma (L.Y 0)],.CX L.sigma (L.Y 0)]
 else [.CX L.sigma (L.Y i)]++eraseCarry (L.Y (i-1)) (L.Y i) (L.A (i-1)) (L.A i)++[.CX L.sigma (L.Y i)]

def streamCarry (L : DecoderLayout) (i : Nat) : Program:=
 streamStage (rawSources L i++correctionSources L i) (L.R (i-1)) (L.R i)

def eraseCorrectionCarry (L : DecoderLayout) (i : Nat) : Program:=
 if i=1 then [.measureX (L.R 0) [] [.CZ (L.Y 0) L.h]]
 else xorList (rawSources L (i-1)) (L.R 255)++
   mappedEraseCarry (correction L (i-1)) (L.R 255) (L.R (i-2)) (L.R (i-1))++
     xorList (rawSources L (i-1)) (L.R 255)

def biasCompute (L : DecoderLayout) : Program:=
 [.X L.sigma,.CCX (L.Y 255) L.sigma L.bias,.X L.sigma]
def biasErase (L : DecoderLayout) : Program:=
 [.X L.sigma,.measureX L.bias [] [.CZ (L.Y 255) L.sigma],.X L.sigma]

def normalize (L : DecoderLayout) : Program:=
 (L.y.take 255).map (fun q=>.CX (L.Y 255) q)++L.r.map (fun q=>.CX (L.Y 255) q)
def restoreSource (L : DecoderLayout) : Program:=(L.y.take 255).map (fun q=>.CX (L.Y 255) q)
def copySource (L : DecoderLayout) : Program:=(L.y.zip L.r).map (fun q=>.CX q.1 q.2)

def clearQuotient (L : DecoderLayout) : Program:=
 [.X (L.Y 255),.X L.sigma]++
   compareSelected (L.y.take 255) L.carry (L.Y 255) L.sigma L.h (((ECDSAAdd.p-1)/2)/3)++
     [.CX L.sigma L.h,.X L.sigma,.X (L.Y 255)]

def decoder (L : DecoderLayout) : Program:=
 normalize L++[.CX (L.R 0) L.h,.CX (L.Y 0) L.h]++biasCompute L++
 (List.range 255).flatMap (addCarry L)++
 xorList (rawSources L 0++correctionSources L 0) (L.R 0)++
 (List.range' 1 255).flatMap (streamCarry L)++
 (List.range' 1 255).reverse.flatMap (eraseCorrectionCarry L)++
 (List.range 255).reverse.flatMap (eraseAddCarry L)++
 biasErase L++clearQuotient L++restoreSource L++copySource L

theorem xorList_counts (xs : List Wire) (target : Wire) :
 toffoliCount (xorList xs target)=0 ∧ measurementCount (xorList xs target)=0 := by
 induction xs with
 | nil=>exact ⟨rfl,rfl⟩
 | cons x xs ih=>simpa only [xorList,List.map_cons,toffoliCount,measurementCount,List.map_cons,List.sum_cons,Nat.zero_add] using ih

theorem streamStage_counts (xs : List Wire) (prev out : Wire) :
 toffoliCount (streamStage xs prev out)=0 ∧ measurementCount (streamStage xs prev out)=0 := by
 have p:=xorList_counts xs prev;have q:=xorList_counts xs out
 simp [streamStage,toffoliCount_append,measurementCount_append,p.1,p.2,q.1,q.2,toffoliCount,measurementCount]

theorem local_counts (L : DecoderLayout) (i : Nat) :
 (toffoliCount (addCarry L i)=1 ∧ measurementCount (addCarry L i)=0) ∧
 (toffoliCount (eraseAddCarry L i)=0 ∧ measurementCount (eraseAddCarry L i)=1) ∧
 (toffoliCount (streamCarry L i)=0 ∧ measurementCount (streamCarry L i)=0) ∧
 (toffoliCount (eraseCorrectionCarry L i)=0 ∧ measurementCount (eraseCorrectionCarry L i)=1) := by
 have st:=streamStage_counts (rawSources L i++correctionSources L i) (L.R (i-1)) (L.R i)
 have x:=xorList_counts (rawSources L (i-1)) (L.R 255)
 have m:=mappedBit_counts (correction L (i-1)) (L.R 255) (L.R (i-2)) (L.R (i-1))
 constructor
 · by_cases h:i=0 <;> simp [addCarry,h,majority,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount]
 constructor
 · by_cases h:i=0 <;> simp [eraseAddCarry,h,eraseCarry,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount]
 constructor
 · exact st
 · by_cases h:i=1
   · simp [eraseCorrectionCarry,h,toffoliCount,measurementCount]
   · simp only [eraseCorrectionCarry,h,ite_false,toffoliCount_append,measurementCount_append,x.1,x.2,m.2.2.1,m.2.2.2.1]
     simp
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Counts
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem flat_counts {α : Type} (xs : List α) (f : α→Program) (T M : Nat)
    (h : ∀i∈xs,toffoliCount (f i)=T ∧ measurementCount (f i)=M) :
    toffoliCount (xs.flatMap f)=T*xs.length ∧ measurementCount (xs.flatMap f)=M*xs.length := by
 induction xs with
 | nil=>simp [toffoliCount,measurementCount]
 | cons x xs ih=>
   have a:=h x (by simp)
   have b:=ih (fun i hi=>h i (by simp [hi]))
   simp only [List.flatMap_cons,toffoliCount_append,measurementCount_append,List.length_cons,a.1,a.2,b.1,b.2,Nat.mul_succ]
   constructor <;> omega

theorem cxMap_counts {α : Type} (xs : List α) (f g : α→Wire) :
    toffoliCount (xs.map (fun x=>Instr.CX (f x) (g x)))=0 ∧
    measurementCount (xs.map (fun x=>Instr.CX (f x) (g x)))=0 := by
 induction xs with
 | nil=>exact ⟨rfl,rfl⟩
 | cons x xs ih=>simpa only [List.map_cons,toffoliCount,measurementCount,List.map_cons,List.sum_cons,Nat.zero_add] using ih

theorem simple_counts (L : DecoderLayout) :
 (toffoliCount (normalize L)=0 ∧ measurementCount (normalize L)=0) ∧
 (toffoliCount (restoreSource L)=0 ∧ measurementCount (restoreSource L)=0) ∧
 (toffoliCount (copySource L)=0 ∧ measurementCount (copySource L)=0) ∧
 (toffoliCount (biasCompute L)=1 ∧ measurementCount (biasCompute L)=0) ∧
 (toffoliCount (biasErase L)=0 ∧ measurementCount (biasErase L)=1) := by
 have a:=cxMap_counts (L.y.take 255) (fun _=>L.Y 255) id
 have b:=cxMap_counts L.r (fun _=>L.Y 255) id
 have c:=cxMap_counts (L.y.zip L.r) Prod.fst Prod.snd
 simp only [id_eq] at a b
 refine ⟨?_,?_,?_,?_,?_⟩
 · simp only [normalize,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,Nat.zero_add,and_self]
 · exact a
 · exact c
 · simp [biasCompute,toffoliCount,measurementCount]
 · simp [biasErase,toffoliCount,measurementCount]


theorem clearQuotient_counts (L : DecoderLayout) (hw : L.Widths) :
 toffoliCount (clearQuotient L)=256 ∧ measurementCount (clearQuotient L)=255 := by
 have yl : (L.y.take 255).length=255:=by simp [hw.1]
 have c:=compareSelected_counts (L.y.take 255) L.carry (L.Y 255) L.sigma L.h (((ECDSAAdd.p-1)/2)/3)
   (by omega) (by rw [hw.2.2,yl])
 simp only [clearQuotient,toffoliCount_append,measurementCount_append,c.1,c.2,yl]
 simp [toffoliCount,measurementCount]

theorem decoder_counts (L : DecoderLayout) (hw : L.Widths) :
 toffoliCount (decoder L)=512 ∧ measurementCount (decoder L)=766 := by
 have a:=flat_counts (List.range 255) (addCarry L) 1 0 (fun i _=>(local_counts L i).1)
 have b:=flat_counts (List.range' 1 255) (streamCarry L) 0 0 (fun i _=>(local_counts L i).2.2.1)
 have c:=flat_counts (List.range' 1 255).reverse (eraseCorrectionCarry L) 0 1 (fun i _=>(local_counts L i).2.2.2)
 have d:=flat_counts (List.range 255).reverse (eraseAddCarry L) 0 1 (fun i _=>(local_counts L i).2.1)
 have z:=xorList_counts (rawSources L 0++correctionSources L 0) (L.R 0)
 have e:=simple_counts L
 have q:=clearQuotient_counts L hw
 simp only [List.length_range,List.length_range',List.length_reverse,Nat.one_mul,Nat.zero_mul] at a b c d
 simp only [decoder,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,d.1,d.2,z.1,z.2,
   e.1.1,e.1.2,e.2.1.1,e.2.1.2,e.2.2.1.1,e.2.2.1.2,e.2.2.2.1.1,e.2.2.2.1.2,e.2.2.2.2.1,e.2.2.2.2.2,q.1,q.2]
 simp [toffoliCount,measurementCount]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CarryWindow
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def cxWindow (sigma x : Wire) (P : Program) : Program := [.CX sigma x]++P++[.CX sigma x]
def cxBasis (sigma x : Wire) (b : BasisState) : BasisState :=writeBit b x (b x ^^ b sigma)

theorem cxWindow_write (sigma x target : Wire) (P : Program)
    (hsx : sigma≠x) (hst : sigma≠target) (hxt : x≠target)
    (s : State) (m : List Bool) (value : Bool)
    (middle : ∀r,run P r ⟨s.phase,cxBasis sigma x s.basis⟩=
      ⟨s.phase,writeBit (cxBasis sigma x s.basis) target value⟩) :
    run (cxWindow sigma x P) m s=⟨s.phase,writeBit s.basis target value⟩ := by
  have first (r : List Bool):run [.CX sigma x] r s=⟨s.phase,cxBasis sigma x s.basis⟩:=rfl
  rw [cxWindow]
  simp only [List.append_assoc,run_append,run_take,measurementCount,List.map_cons,List.sum_cons,List.sum_nil,Nat.zero_add,List.take_zero,List.drop_zero]
  rw [first,middle]
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hx:q=x
  · subst q;simp [cxBasis,writeBit,hsx,hst,hxt]
  · by_cases ht:q=target
    · subst q;simp [cxBasis,writeBit,hxt,Ne.symm hxt]
    · simp [cxBasis,writeBit,hx,ht]

theorem cxBasis_mapped (b : MappedBit) (sigma x : Wire) (basis : BasisState)
    (ha : ∀q∈b.wire,q≠x) : b.value (cxBasis sigma x basis)=b.value basis := by
 apply mappedBit_value_congr
 intro q hq
 simp [cxBasis,writeBit,ha q hq]

theorem windowMajority_run (b : MappedBit) (sigma x cin cout : Wire)
    (nd : [x,cin,cout].Nodup) (ha : ∀q∈b.wire,q∉[x,cin,cout])
    (hsx : sigma≠x) (hsc : sigma≠cout)
    (s : State) (m : List Bool) :
    run (cxWindow sigma x (mappedMajority b x cin cout)) m s=
      ⟨s.phase,writeBit s.basis cout (s.basis cout ^^
        carryBit (b.value s.basis) (s.basis x ^^ s.basis sigma) (s.basis cin))⟩ := by
 have xc:x≠cout:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 have ic:cin≠x:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 apply cxWindow_write sigma x cout _ hsx hsc xc
 intro r
 rw [mappedMajority_correct b x cin cout nd ha]
 have bm:=cxBasis_mapped b sigma x s.basis (by
   intro q hq hqx;exact ha q hq (by simp [hqx]))
 rw [bm]
 simp [cxBasis,writeBit,Ne.symm xc,ic]

theorem windowErase_run (b : MappedBit) (sigma x cin cout : Wire)
    (nd : [x,cin,cout].Nodup) (ha : ∀q∈b.wire,q∉[x,cin,cout])
    (hsx : sigma≠x) (hsc : sigma≠cout)
    (s : State) (m : List Bool)
    (known : s.basis cout=carryBit (b.value s.basis) (s.basis x ^^ s.basis sigma) (s.basis cin)) :
    run (cxWindow sigma x (mappedEraseCarry b x cin cout)) m s=
      ⟨s.phase,writeBit s.basis cout false⟩ := by
 have xc:x≠cout:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 have ic:cin≠x:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 apply cxWindow_write sigma x cout _ hsx hsc xc
 intro r
 apply mappedEraseCarry_correct b x cin cout nd ha
 have bm:=cxBasis_mapped b sigma x s.basis (by
   intro q hq hqx;exact ha q hq (by simp [hqx]))
 rw [bm]
 simpa [cxBasis,writeBit,Ne.symm xc,ic] using known
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT LayoutFacts
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def DecoderLayout.wires (L : DecoderLayout) : List Wire:=
 [L.sigma,L.h,L.bias]++L.y++L.r++L.carry

def ofBalanced (L : BalancedCircuit.Layout) : DecoderLayout:=
 ⟨L.y,L.r,L.carry.take 254++[L.lower],L.sign,L.one,L.parity⟩

theorem ofBalanced_widths (L : BalancedCircuit.Layout) (hw : L.Widths) :
 (ofBalanced L).Widths := by
 have w:=BalancedCleanup.widths L.toLayout hw
 simp [ofBalanced,DecoderLayout.Widths,w.2.1,w.2.2.1,List.length_take,hw.2.2]

theorem ofBalanced_nodup (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
 (ofBalanced L).wires.Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 have take: (L.carry.take 254).count q≤L.carry.count q:=(List.take_sublist 254 L.carry).count_le q
 simp only [ofBalanced,DecoderLayout.wires,BalancedCircuit.Layout.wires,
  BalancedCleanup.Layout.wires,BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,
  BalancedCleanup.Layout.low,List.count_append,List.count_cons,List.count_nil] at h ⊢
 omega

theorem getD_mem (xs : List Wire) (i : Nat) (hi : i<xs.length) : xs.getD i 0∈xs := by
 rw [List.getD_eq_getElem _ _ hi]
 exact List.getElem_mem hi

theorem getD_inj (xs : List Wire) (hn : xs.Nodup) (i j : Nat)
    (hi : i<xs.length) (hj : j<xs.length) (eq : xs.getD i 0=xs.getD j 0) : i=j := by
 apply List.getElem?_inj hi hn
 have x:=congrArg some eq
 simpa only [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj,
   List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using x

theorem register_nodup (L : DecoderLayout) (hn : L.wires.Nodup) :
 L.y.Nodup ∧ L.r.Nodup ∧ L.carry.Nodup := by
 unfold DecoderLayout.wires at hn
 have a:=List.nodup_append'.mp hn
 have b:=List.nodup_append'.mp a.1
 have c:=List.nodup_append'.mp b.1
 exact ⟨c.2.1,b.2.1,a.2.1⟩

theorem carry_source_away (L : DecoderLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : q∉L.carry := by
 intro hc
 have h:=List.nodup_iff_count.mp hn q
 have pos:0<L.carry.count q:=List.count_pos_iff.mpr hc
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
 rcases hq with hy|rfl|rfl|rfl
 · have yy:=List.count_pos_iff.mpr hy;omega
 all_goals simp only [beq_self_eq_true,if_true] at h;omega

theorem carry_ne_carry (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i j : Nat) (hi : i<255) (hj : j<255) (ne : i≠j) : L.A i≠L.A j := by
 intro eq
 have len:=hw.2.2
 exact ne (getD_inj L.carry (register_nodup L hn).2.2 i j (by omega) (by omega) eq)
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Geometry
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem y_mem (L : DecoderLayout) (hw : L.Widths) (i : Nat) (hi : i<256) : L.Y i∈L.y :=
 getD_mem L.y i (by have h:=hw.1;omega)
theorem a_mem (L : DecoderLayout) (hw : L.Widths) (i : Nat) (hi : i<255) : L.A i∈L.carry :=
 getD_mem L.carry i (by have h:=hw.2.2;omega)
theorem r_mem (L : DecoderLayout) (hw : L.Widths) (i : Nat) (hi : i<256) : L.R i∈L.r :=
 getD_mem L.r i (by have h:=hw.2.1;omega)

theorem y_ne_a (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i j : Nat) (hi : i<256) (hj : j<255) : L.Y i≠L.A j := by
 intro e
 exact carry_source_away L hn _ (Or.inl (y_mem L hw i hi)) (e ▸ a_mem L hw j hj)

theorem sigma_ne_a (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<255) : L.sigma≠L.A i := by
 intro e
 exact carry_source_away L hn _ (Or.inr (Or.inl rfl)) (e ▸ a_mem L hw i hi)

theorem sigma_ne_y (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) : L.sigma≠L.Y i := by
 intro eq
 have h:=List.nodup_iff_count.mp hn L.sigma
 have mem:=y_mem L hw i hi
 rw [←eq] at mem
 have pos:=List.count_pos_iff.mpr mem
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil,
  beq_self_eq_true,if_true] at h
 omega

theorem y_ne_y (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i j : Nat) (hi : i<256) (hj : j<256) (ne : i≠j) : L.Y i≠L.Y j := by
 intro eq
 have len:=hw.1
 exact ne (getD_inj L.y (register_nodup L hn).1 i j (by omega) (by omega) eq)

theorem source_r_away (L : DecoderLayout) (hn : L.wires.Nodup)
 (q : Wire) (hq : q∈L.y ∨ q∈L.carry ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : q∉L.r := by
 intro hr
 have h:=List.nodup_iff_count.mp hn q
 have pos:=List.count_pos_iff.mpr hr
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
 rcases hq with hy|hc|rfl|rfl|rfl
 · have yy:=List.count_pos_iff.mpr hy;omega
 · have cc:=List.count_pos_iff.mpr hc;omega
 all_goals simp only [beq_self_eq_true,if_true] at h;omega

theorem raw_source_r_away (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (q : Wire) (hq : q∈rawSources L i) : q∉L.r := by
 apply source_r_away L hn q
 unfold rawSources at hq
 split_ifs at hq with h0 h255
 · have eq:q=L.Y 0:=by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hq
   subst q
   exact Or.inl (y_mem L hw 0 (by omega))
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl
   · exact Or.inl (y_mem L hw (i-1) (by omega))
   · exact Or.inl (y_mem L hw i hi)
   · exact Or.inr (Or.inr (Or.inl rfl))
   · exact Or.inr (Or.inl (a_mem L hw (i-1) (by omega)))
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl
   · exact Or.inl (y_mem L hw 254 (by omega))
   · exact Or.inr (Or.inr (Or.inl rfl))
   · exact Or.inr (Or.inl (a_mem L hw 254 (by omega)))
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT QuotientClear
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run compareSelected

theorem state_ext (s t : State) (hp : s.phase=t.phase) (hb : ∀q,s.basis q=t.basis q) : s=t := by
 cases s
 cases t
 exact congrArg₂ State.mk hp (funext hb)

theorem y_split (L : DecoderLayout) (hw : L.Widths) :
 L.y=L.y.take 255++[L.Y 255] := by
 have len:=hw.1
 have split : L.y.take 255++[L.y.getD 255 0]=L.y.take 256 := by
   conv_rhs=>rw [show 256=255+1 from rfl,List.take_add_one]
   simp only [List.getD_eq_getElem _ _ (by omega : 255<L.y.length)]
   simp [List.getElem?_eq_getElem (by omega : 255<L.y.length)]
 simpa only [DecoderLayout.Y,List.take_of_length_le (by omega : L.y.length≤256)] using split.symm

theorem compare_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 (L.sigma::L.h::L.Y 255::(L.y.take 255++L.carry)).Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 unfold DecoderLayout.wires at h
 rw [y_split L hw] at h
 simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
 omega

theorem clearQuotient_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) (clean : ∀q∈L.carry,s.basis q=false)
 (quotient : s.basis L.h = (!s.basis L.sigma &&
   !(decide (regValue (L.y.take 255) s.basis < ((p-1)/2)/3+(!s.basis (L.Y 255)).toNat)))) :
 run (clearQuotient L) m s=⟨s.phase,writeBit s.basis L.h false⟩ := by
 have nd:=compare_nd L hw hn
 have yz:=sigma_ne_y L hw hn 255 (by omega)
 have hs : L.h≠L.sigma := by
   intro e
   have h:=List.nodup_iff_count.mp nd L.h
   simp only [List.count_cons,List.count_append,List.count_nil] at h
   simp only [e,beq_self_eq_true,if_true] at h
   omega
 have hy : L.h≠L.Y 255 := by
   intro e
   have h:=List.nodup_iff_count.mp nd L.h
   simp only [List.count_cons,List.count_append,List.count_nil] at h
   simp only [e,beq_self_eq_true,if_true] at h
   omega
 let t : State:=⟨s.phase,writeBit (writeBit s.basis (L.Y 255) (!s.basis (L.Y 255))) L.sigma (!s.basis L.sigma)⟩
 have pre (r : List Bool) : run [.X (L.Y 255),.X L.sigma] r s=t := by
   simp [run,t,writeBit,yz]
 have tclean : ∀q∈L.carry,t.basis q=false := by
   intro q hq
   have qy:q≠L.Y 255:=fun e=>carry_source_away L hn _ (Or.inl (y_mem L hw 255 (by omega))) (e ▸ hq)
   have qs:q≠L.sigma:=fun e=>carry_source_away L hn _ (Or.inr (Or.inl rfl)) (e ▸ hq)
   simpa only [t,writeBit,Function.update_of_ne qs,Function.update_of_ne qy] using clean q hq
 have tv : regValue (L.y.take 255) t.basis=regValue (L.y.take 255) s.basis := by
   apply regValue_congr
   intro q hq
   have qs:q≠L.sigma := fun e => (List.nodup_cons.mp nd).1 (by simp [←e,hq])
   have qy:q≠L.Y 255 := fun e =>
     (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp nd).2).2).1 (by simp [←e,hq])
   simp [t,writeBit,qs,qy]
 let k:=((p-1)/2)/3
 let v : State:=⟨s.phase,writeBit t.basis L.h
   (s.basis L.h ^^ (!s.basis L.sigma && decide (regValue (L.y.take 255) s.basis < k+(!s.basis (L.Y 255)).toNat)))⟩
 have mid (r : List Bool) :
   run (compareSelected (L.y.take 255) L.carry (L.Y 255) L.sigma L.h k) r t=v := by
   have c:=compareSelected_correct (L.y.take 255) L.carry (L.Y 255) L.sigma L.h k nd
     (by simp [hw.1]) (by simp [hw.1,hw.2.2]) (by norm_num [k,p,hw.1]) t r tclean
   rw [tv] at c
   apply state_ext
   · exact c.1
   · intro q
     by_cases eq:q=L.h
     · subst q
       simpa [v,t,writeBit,hs,hy,Ne.symm yz,tv] using c.2.2
     · simpa [v,writeBit,eq] using c.2.1 q eq
 have post (r : List Bool) : run [.CX L.sigma L.h,.X L.sigma,.X (L.Y 255)] r v=
   ⟨s.phase,writeBit s.basis L.h false⟩ := by
   apply state_ext
   · simp [run,v,t]
   · intro q
     by_cases qh:q=L.h
     · subst q
       simp only [run,v,t,writeBit,Function.update_apply]
       simp only [hs,hy,Ne.symm hs,Ne.symm hy,yz,Ne.symm yz,if_false,if_true]
       rw [quotient]
       cases s.basis L.sigma <;>
         cases decide (regValue (L.y.take 255) s.basis < k+(!s.basis (L.Y 255)).toNat) <;>
         simp_all [k]
     · by_cases qs:q=L.sigma
       · subst q;simp [run,v,t,writeBit,hs,Ne.symm hs,yz,Ne.symm yz]
       · by_cases qy:q=L.Y 255
         · subst q;simp [run,v,t,writeBit,hy,Ne.symm hy,yz,Ne.symm yz]
         · simp [run,v,t,writeBit,qh,qs,qy]
 have result:=run_three_states [.X (L.Y 255),.X L.sigma]
   (compareSelected (L.y.take 255) L.carry (L.Y 255) L.sigma L.h k)
   [.CX L.sigma L.h,.X L.sigma,.X (L.Y 255)]
   (fun a d => a=s → d=⟨s.phase,writeBit s.basis L.h false⟩) (by
     intro a b c d m1 m2 m3 hab hbc hcd eq
     subst a
     rw [pre] at hab
     subst b
     rw [mid] at hbc
     subst c
     exact hcd.symm.trans (post m3)) s m
 simpa only [clearQuotient,List.append_assoc,k] using result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT BiasSteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run

theorem bias_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 [L.Y 255,L.sigma,L.bias].Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 have mem:=y_mem L hw 255 (by omega)
 have take : (if L.Y 255==q then 1 else 0) ≤ L.y.count q := by
   by_cases eq:L.Y 255=q
   · subst q;simpa using (List.count_pos_iff.mpr mem)
   · simp [eq]
 simp only [DecoderLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
 omega

theorem biasCompute_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (biasCompute L) m s=
   ⟨s.phase,writeBit s.basis L.bias
      (s.basis L.bias ^^ (s.basis (L.Y 255) && !s.basis L.sigma))⟩ := by
 have nd:=bias_nd L hw hn
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
   not_false_eq_true,and_true] at nd
 obtain ⟨⟨yx,yb⟩,xb⟩:=nd
 simp only [biasCompute,run]
 apply congrArg (State.mk s.phase)
 funext q
 by_cases eq:q=L.sigma
 · subst q;simp [writeBit,yx,xb]
 · by_cases eb:q=L.bias
   · subst q;simp [writeBit,yx,Ne.symm xb]
   · simp [writeBit,eq,eb,yx]

theorem biasErase_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool)
 (known : s.basis L.bias=(s.basis (L.Y 255) && !s.basis L.sigma)) :
 run (biasErase L) m s=⟨s.phase,writeBit s.basis L.bias false⟩ := by
 have nd:=bias_nd L hw hn
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
   not_false_eq_true,and_true] at nd
 obtain ⟨⟨yx,yb⟩,xb⟩:=nd
 simp only [biasErase,run]
 cases hm:m.headD false <;>
   simp [measureAndCorrect,correct,writeBit,yx,xb,Ne.symm xb,yb,known]
 all_goals
   funext q
   by_cases eq:q=L.sigma
   · subst q;simp [xb]
   · simp [Function.update_apply,eq]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT NormalizeSteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run

def complementBasis (control : Wire) (xs : List Wire) (b : BasisState) : BasisState :=
 fun q=>if q∈xs then b q ^^ b control else b q

theorem conditional_complement_run (control : Wire) (xs : List Wire)
 (hn : xs.Nodup) (away : control∉xs) (s : State) (m : List Bool) :
 run (xs.map (fun q=>Instr.CX control q)) m s=⟨s.phase,complementBasis control xs s.basis⟩ := by
 induction xs generalizing s with
 | nil =>
   apply state_ext
   · simp [run]
   · intro q;simp [run,complementBasis]
 | cons x xs ih =>
   obtain ⟨xaway,tailnd⟩:=List.nodup_cons.mp hn
   have cx:control≠x:=fun e=>away (by simp [e])
   have ct:control∉xs:=fun h=>away (by simp [h])
   let t : State:=⟨s.phase,writeBit s.basis x (s.basis x ^^ s.basis control)⟩
   simp only [List.map_cons,run]
   change run (xs.map (fun q=>Instr.CX control q)) m t=_
   rw [ih tailnd ct]
   apply congrArg (State.mk s.phase)
   funext q
   by_cases eq:q=x
   · subst q;simp [complementBasis,t,writeBit,xaway]
   · simp [complementBasis,t,writeBit,eq,cx]

theorem normalize_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 (L.y.take 255++L.r).Nodup ∧ L.Y 255∉L.y.take 255++L.r := by
 have full:(L.y++L.r).Nodup := by
   apply List.nodup_iff_count.mpr
   intro q
   have h:=List.nodup_iff_count.mp hn q
   simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
   omega
 have sub:(L.y.take 255++L.r).Sublist (L.y++L.r) := (List.take_sublist 255 L.y).append (List.Sublist.refl _)
 constructor
 · exact full.sublist sub
 · have shape:=y_split L hw
   have hn':(L.y.take 255++[L.Y 255]++L.r).Nodup := by simpa only [←shape] using full
   intro mem
   have c:=List.nodup_iff_count.mp hn' (L.Y 255)
   have pos:=List.count_pos_iff.mpr mem
   simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c pos
   omega

theorem normalize_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (normalize L) m s=
 ⟨s.phase,complementBasis (L.Y 255) (L.y.take 255++L.r) s.basis⟩ := by
 have nd:=normalize_nd L hw hn
 simpa only [normalize,List.map_append] using conditional_complement_run (L.Y 255) (L.y.take 255++L.r) nd.1 nd.2 s m

theorem restoreSource_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (restoreSource L) m s=
 ⟨s.phase,complementBasis (L.Y 255) (L.y.take 255) s.basis⟩ := by
 have nd:=normalize_nd L hw hn
 exact conditional_complement_run (L.Y 255) (L.y.take 255)
   (List.nodup_append'.mp nd.1).1 (fun h=>nd.2 (List.mem_append_left _ h)) s m
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamGeometry
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def bSources (L : DecoderLayout) (i : Nat) : List Wire:=rawSources L i++correctionSources L i

theorem r_ne_r (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i j : Nat) (hi : i<256) (hj : j<256) (ne : i≠j) : L.R i≠L.R j := by
 intro eq
 have len:=hw.2.1
 exact ne (getD_inj L.r (register_nodup L hn).2.1 i j (by omega) (by omega) eq)

theorem correction_r_away (L : DecoderLayout) (hn : L.wires.Nodup)
 (i : Nat) (q : Wire) (hq : q∈correctionSources L i) : q∉L.r := by
 apply source_r_away L hn q
 unfold correctionSources correction at hq
 split_ifs at hq with h1 hc
 · have eq:q=L.bias:=by simpa using hq
   subst q;exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
 · have eq:q=L.h:=by simpa using hq
   subst q;exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
 · simp at hq

theorem bSources_r_away (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (q : Wire) (hq : q∈bSources L i) : q∉L.r := by
 rcases List.mem_append.mp hq with h|h
 · exact raw_source_r_away L hw hn i hi q h
 · exact correction_r_away L hn i q h

theorem bSources_parity (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (s t : BasisState)
 (agree : ∀q,q∉L.r→s q=t q) : parity (bSources L i) s=parity (bSources L i) t := by
 apply parity_congr
 intro q hq
 exact agree q (bSources_r_away L hw hn i hi q hq)
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamForward
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def bExpected (L : DecoderLayout) (origin : BasisState) (i : Nat) : Bool:=
 origin (L.R i) ^^ parity (bSources L i) origin

structure StreamFrame (L : DecoderLayout) (origin : State) (nDone : Nat) (s : State) : Prop where
 phase : s.phase=origin.phase
 outside : ∀q,q∉L.r→s.basis q=origin.basis q
 stored : ∀j,j<nDone→s.basis (L.R j)=bExpected L origin.basis (j+1)
 current : s.basis (L.R nDone)=false
 pending : ∀j,nDone<j→j<256→s.basis (L.R j)=origin.basis (L.R j)

theorem stream_initial (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (m : List Bool)
 (low : origin.basis (L.R 0)=parity (bSources L 0) origin.basis) :
 StreamFrame L origin 0 (run (xorList (bSources L 0) (L.R 0)) m origin) := by
 have away:L.R 0∉bSources L 0:=by
   intro h;exact bSources_r_away L hw hn 0 (by omega) _ h (r_mem L hw 0 (by omega))
 rw [xorList_run _ _ away,low]
 simp only [Bool.xor_self]
 refine ⟨rfl,?_,?_,?_,?_⟩
 · intro q hq
   have ne:q≠L.R 0:=fun e=>hq (e ▸ r_mem L hw 0 (by omega))
   simp [writeBit,ne]
 · intro j hj;omega
 · simp [writeBit]
 · intro j hj hbound
   simp [writeBit,r_ne_r L hw hn j 0 hbound (by omega) (by omega)]

theorem stream_frame_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (n : Nat) (bound : n<255) (f : StreamFrame L origin n s) (m : List Bool) :
 StreamFrame L origin (n+1) (run (streamCarry L (n+1)) m s) := by
 have ne:=r_ne_r L hw hn n (n+1) (by omega) (by omega) (by omega)
 have ap:L.R n∉bSources L (n+1):=by
   intro h;exact bSources_r_away L hw hn (n+1) (by omega) _ h (r_mem L hw n (by omega))
 have ao:L.R (n+1)∉bSources L (n+1):=by
   intro h;exact bSources_r_away L hw hn (n+1) (by omega) _ h (r_mem L hw (n+1) (by omega))
 have par:=bSources_parity L hw hn (n+1) (by omega) s.basis origin.basis f.outside
 have pending:=f.pending (n+1) (by omega) (by omega)
 simp only [streamCarry,Nat.add_sub_cancel]
 change StreamFrame L origin (n+1) (run (streamStage (bSources L (n+1)) (L.R n) (L.R (n+1))) m s)
 rw [streamStage_run _ _ _ ne ap ao s m f.current,pending,par]
 change StreamFrame L origin (n+1)
   ⟨s.phase,writeBit (writeBit s.basis (L.R n) (bExpected L origin.basis (n+1))) (L.R (n+1)) false⟩
 refine ⟨f.phase,?_,?_,?_,?_⟩
 · intro q hq
   have n0:q≠L.R n:=fun e=>hq (e ▸ r_mem L hw n (by omega))
   have n1:q≠L.R (n+1):=fun e=>hq (e ▸ r_mem L hw (n+1) (by omega))
   simpa only [writeBit,Function.update_of_ne n0,Function.update_of_ne n1] using f.outside q hq
 · intro j hj
   have nj1:=r_ne_r L hw hn j (n+1) (by omega) (by omega) (by omega)
   simp only [writeBit,Function.update_of_ne nj1]
   by_cases eq:j=n
   · subst j;simp
   · have nj0:=r_ne_r L hw hn j n (by omega) (by omega) eq
     simpa only [Function.update_of_ne nj0] using f.stored j (by omega)
 · simp [writeBit]
 · intro j hj hbound
   have nj1:=r_ne_r L hw hn j (n+1) hbound (by omega) (by omega)
   have nj0:=r_ne_r L hw hn j n hbound (by omega) (by omega)
   simpa only [writeBit,Function.update_of_ne nj0,Function.update_of_ne nj1] using f.pending j (by omega) hbound

theorem stream_forward_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (f : StreamFrame L origin 0 s) (n : Nat) (bound : n≤255) (m : List Bool) :
 StreamFrame L origin n (run ((List.range' 1 n).flatMap (streamCarry L)) m s) := by
 induction n generalizing m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range'_1_concat,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   rw [Nat.add_comm 1 n]
   apply stream_frame_step L hw hn origin _ n (by omega)
   exact ih (by omega) _

end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT XorWindow
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def xorWindow (xs : List Wire) (temp : Wire) (P : Program) : Program:=xorList xs temp++P++xorList xs temp

theorem xorWindow_write (xs : List Wire) (temp target : Wire) (P : Program)
 (awayT : temp∉xs) (awayQ : target∉xs) (ne : temp≠target)
 (s : State) (m : List Bool) (value : Bool)
 (middle : ∀r,run P r ⟨s.phase,writeBit s.basis temp (s.basis temp ^^ parity xs s.basis)⟩=
   ⟨s.phase,writeBit (writeBit s.basis temp (s.basis temp ^^ parity xs s.basis)) target value⟩) :
 run (xorWindow xs temp P) m s=⟨s.phase,writeBit s.basis target value⟩ := by
 let t : State:=⟨s.phase,writeBit s.basis temp (s.basis temp ^^ parity xs s.basis)⟩
 let u : State:=⟨s.phase,writeBit t.basis target value⟩
 have first (r : List Bool):run (xorList xs temp) r s=t:=xorList_run _ _ awayT _ _
 have par:parity xs u.basis=parity xs s.basis:=by
   apply parity_congr
   intro q hq
   have qt:q≠temp:=fun e=>awayT (e ▸ hq)
   have qq:q≠target:=fun e=>awayQ (e ▸ hq)
   simp [u,t,writeBit,qt,qq]
 have last (r : List Bool):run (xorList xs temp) r u=⟨s.phase,writeBit s.basis target value⟩:=by
   rw [xorList_run _ _ awayT,par]
   apply congrArg (State.mk s.phase)
   funext q
   by_cases qt:q=temp
   · subst q;simp [u,t,writeBit,ne]
   · by_cases qq:q=target
     · subst q;simp [u,t,writeBit,ne,Ne.symm ne]
     · simp [u,t,writeBit,qt,qq]
 rw [xorWindow]
 simp only [List.append_assoc,run_append,run_take,(xorList_counts xs temp).2,List.take_zero,List.drop_zero]
 rw [first,middle]
 exact last _
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamEraseSteps
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def BGraph (L : DecoderLayout) (origin : BasisState) : Prop:=
 ∀ i, 1 ≤ i → i ≤ 255 → bExpected L origin i=
   carryBit ((correction L (i-1)).value origin) (parity (rawSources L (i-1)) origin)
     (if i=1 then false else bExpected L origin (i-1))

structure EraseBFrame (L : DecoderLayout) (origin : State) (nLive : Nat) (s : State) : Prop where
 phase : s.phase=origin.phase
 outside : ∀ q, q∉L.r → s.basis q=origin.basis q
 live : ∀j,j<nLive → s.basis (L.R j)=bExpected L origin.basis (j+1)
 clean : ∀j,nLive ≤ j → j<256 → s.basis (L.R j)=false

theorem flag_y_away (L : DecoderLayout) (hn : L.wires.Nodup) (q : Wire)
 (hq : q∈[L.sigma,L.h,L.bias]) : q∉L.y := by
 intro hy
 have p:=List.count_pos_iff.mpr hq
 have y:=List.count_pos_iff.mpr hy
 have h:=List.nodup_iff_count.mp hn q
 simp only [DecoderLayout.wires,List.count_append] at h
 omega

theorem correction_option_r_away (L : DecoderLayout) (hn : L.wires.Nodup) (i : Nat)
 (q : Wire) (hq : q∈(correction L i).wire) : q∉L.r := by
 apply correction_r_away L hn i q
 simpa only [correctionSources,Option.mem_toList] using hq

theorem correction_value_same (L : DecoderLayout) (hn : L.wires.Nodup) (i : Nat)
 (s t : BasisState) (same : ∀ q, q∉L.r → s q=t q) :
 (correction L i).value s=(correction L i).value t := by
 apply mappedBit_value_congr
 intro q hq
 exact same q (correction_option_r_away L hn i q hq)

theorem raw_parity_same (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (s t : BasisState) (same : ∀ q, q∉L.r → s q=t q) :
 parity (rawSources L i) s=parity (rawSources L i) t := by
 apply parity_congr
 intro q hq
 exact same q (raw_source_r_away L hw hn i hi q hq)

theorem eraseCorrectionCarry_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hlo : 1 ≤ i) (hi : i ≤ 255)
 (graph : BGraph L origin.basis) (f : EraseBFrame L origin i s) (m : List Bool) :
 run (eraseCorrectionCarry L i) m s=⟨s.phase,writeBit s.basis (L.R (i-1)) false⟩ := by
 by_cases h1:i=1
 · subst i
   have ym:=y_mem L hw 0 (by omega)
   have rm:=r_mem L hw 0 (by omega)
   have hy:L.h∉L.y:=flag_y_away L hn _ (by simp)
   have yr:L.Y 0≠L.R 0:=fun e=>source_r_away L hn _ (Or.inl ym) (e ▸ rm)
   have hr:L.h≠L.R 0:=fun e=>source_r_away L hn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (e ▸ rm)
   have yh:L.Y 0≠L.h:=fun e=>hy (e ▸ ym)
   have nd:[L.Y 0,L.h,L.R 0].Nodup:=by simp [yh,yr,hr]
   have ySame:=f.outside (L.Y 0) (source_r_away L hn _ (Or.inl ym))
   have hSame:=f.outside L.h (source_r_away L hn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
   have g:=graph 1 (by omega) (by omega)
   have k:=f.live 0 (by omega)
   have corr:correction L 0=⟨some L.h,false⟩:=by rfl
   rw [show 1-1=0 by omega] at g
   rw [corr] at g
   simp only [rawSources,ite_true,parity,List.foldr_cons,List.foldr_nil,Bool.xor_false,
     MappedBit.value,Option.map_some,Option.getD_some,Bool.false_xor,ite_true] at g
   have known:s.basis (L.R 0)=carryBit false (s.basis (L.Y 0)) (s.basis L.h) := by
     rw [k,g,ySame,hSame]
     cases origin.basis (L.Y 0) <;> cases origin.basis L.h <;> rfl
   change run (mappedEraseCarry ⟨none,false⟩ (L.Y 0) L.h (L.R 0)) m s=_
   apply mappedEraseCarry_correct ⟨none,false⟩ (L.Y 0) L.h (L.R 0) nd (by simp)
   simpa [MappedBit.value] using known
 · have h2:2 ≤ i:=by omega
   let tmp:=L.R 255
   let cin:=L.R (i-2)
   let target:=L.R (i-1)
   have tc:tmp≠cin:=r_ne_r L hw hn 255 (i-2) (by omega) (by omega) (by omega)
   have tt:tmp≠target:=r_ne_r L hw hn 255 (i-1) (by omega) (by omega) (by omega)
   have ct:cin≠target:=r_ne_r L hw hn (i-2) (i-1) (by omega) (by omega) (by omega)
   have nd:[tmp,cin,target].Nodup:=by simp [tc,tt,ct]
   have optAway:∀q∈(correction L (i-1)).wire,q∉[tmp,cin,target]:=by
     intro q hq bad
     have away:=correction_option_r_away L hn (i-1) q hq
     simp only [List.mem_cons,List.not_mem_nil,or_false] at bad
     rcases bad with rfl|rfl|rfl
     · exact away (r_mem L hw 255 (by omega))
     · exact away (r_mem L hw (i-2) (by omega))
     · exact away (r_mem L hw (i-1) (by omega))
   have awayTemp:tmp∉rawSources L (i-1):=by
     intro q;exact raw_source_r_away L hw hn (i-1) (by omega) tmp q (r_mem L hw 255 (by omega))
   have aq:target∉rawSources L (i-1):=by
     intro q;exact raw_source_r_away L hw hn (i-1) (by omega) target q (r_mem L hw (i-1) (by omega))
   have tempZero:s.basis tmp=false:=f.clean 255 hi (by omega)
   have rawSame:=raw_parity_same L hw hn (i-1) (by omega) s.basis origin.basis f.outside
   have corSame:=correction_value_same L hn (i-1) s.basis origin.basis f.outside
   have cinValue:s.basis cin=bExpected L origin.basis (i-1):=by
     have a:=f.live (i-2) (by omega)
     simpa only [show i-2+1=i-1 by omega] using a
   have targetValue:s.basis target=bExpected L origin.basis i:=by
     have a:=f.live (i-1) (by omega)
     simpa only [show i-1+1=i by omega] using a
   rw [eraseCorrectionCarry,if_neg h1]
   change run (xorWindow (rawSources L (i-1)) tmp
     (mappedEraseCarry (correction L (i-1)) tmp cin target)) m s=_
   apply xorWindow_write _ tmp target _ awayTemp aq tt
   intro r
   apply mappedEraseCarry_correct (correction L (i-1)) tmp cin target nd optAway
   have bm:(correction L (i-1)).value
       (writeBit s.basis tmp (s.basis tmp ^^ parity (rawSources L (i-1)) s.basis))=
       (correction L (i-1)).value origin.basis := by
     apply correction_value_same L hn (i-1)
     intro q hq
     have nq:q≠tmp:=fun e=>hq (e ▸ r_mem L hw 255 (by omega))
     simpa [writeBit,nq] using f.outside q hq
   rw [bm]
   simp only [writeBit,Function.update_of_ne (Ne.symm tt),Function.update_of_ne (Ne.symm tc),
     Function.update_self,tempZero,Bool.false_xor,targetValue,cinValue,rawSame]
   simpa only [h1,ite_false] using graph i hlo hi
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Front
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run normalize biasCompute

def front (L : DecoderLayout) : Program :=
 normalize L ++ ([.CX (L.R 0) L.h,.CX (L.Y 0) L.h] ++ biasCompute L)

def frontBasis (L : DecoderLayout) (b : BasisState) : BasisState :=
 let n:=complementBasis (L.Y 255) (L.y.take 255++L.r) b
 writeBit (writeBit n L.h (n L.h ^^ n (L.R 0) ^^ n (L.Y 0))) L.bias
   (n L.bias ^^ (n (L.Y 255) && !n L.sigma))

theorem front_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (front L) m s=⟨s.phase,frontBasis L s.basis⟩ := by
 have hy:L.h≠L.Y 0:=fun e=>flag_y_away L hn _ (by simp) (e ▸ y_mem L hw 0 (by omega))
 have hr:L.h≠L.R 0:=fun e=>source_r_away L hn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (e ▸ r_mem L hw 0 (by omega))
 have hh : [L.sigma,L.h,L.bias].Nodup := by
   apply List.nodup_iff_count.mpr
   intro q
   have c:=List.nodup_iff_count.mp hn q
   simp only [DecoderLayout.wires,List.count_append] at c
   omega
 have hs:L.sigma≠L.h := fun e=>(List.nodup_cons.mp hh).1 (by simp[e])
 have hb:L.bias≠L.h := fun e=>(List.nodup_cons.mp (List.nodup_cons.mp hh).2).1 (by simp[e])
 have htop:L.Y 255≠L.h:=fun e=>flag_y_away L hn _ (by simp) (e.symm ▸ y_mem L hw 255 (by omega))
 let n : State:=⟨s.phase,complementBasis (L.Y 255) (L.y.take 255++L.r) s.basis⟩
 let u : State:=⟨s.phase,writeBit n.basis L.h (n.basis L.h ^^ n.basis (L.R 0) ^^ n.basis (L.Y 0))⟩
 have middle (r : List Bool) : run [.CX (L.R 0) L.h,.CX (L.Y 0) L.h] r n=u := by
   simp only [run]
   apply congrArg (State.mk s.phase)
   funext q
   by_cases eq:q=L.h
   · subst q;simp [u,n,writeBit,Ne.symm hy]
   · simp [u,n,writeBit,eq]
 have last (r : List Bool) : run (biasCompute L) r u=⟨s.phase,frontBasis L s.basis⟩ := by
   rw [biasCompute_run L hw hn]
   simp only [u,n,frontBasis,writeBit,Function.update_of_ne hb,Function.update_of_ne htop,Function.update_of_ne hs]
 have result:=run_three_states (normalize L) [.CX (L.R 0) L.h,.CX (L.Y 0) L.h] (biasCompute L)
   (fun a d=>a=s → d=⟨s.phase,frontBasis L s.basis⟩) (by
     intro a b c d m1 m2 m3 hab hbc hcd eq
     subst a
     rw [normalize_run L hw hn] at hab
     change n=b at hab
     subst b
     rw [middle] at hbc
     subst c
     exact hcd.symm.trans (last m3)) s m
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CopySteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run

theorem zip_copy (ys rs : List Wire) :
 (ys.zip rs).map (fun q=>Instr.CX q.1 q.2)=copyRegister none ys rs := by
 induction ys generalizing rs with
 |nil=>cases rs <;>rfl
 |cons y ys ih=>cases rs with
   |nil=>rfl
   |cons r rs=>simp only [List.zip_cons_cons,List.map_cons,copyRegister,copyGate,List.singleton_append];rw[ih]

theorem yr_nodup (L : DecoderLayout) (hn : L.wires.Nodup) : (L.y++L.r).Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
 omega

theorem copySource_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) :
 (run (copySource L) m s).phase=s.phase ∧
 (∀q,q∉L.r → (run (copySource L) m s).basis q=s.basis q) ∧
 regValue L.r (run (copySource L) m s).basis=regValue L.r s.basis ^^^ regValue L.y s.basis := by
 rw [copySource,zip_copy]
 simpa only [copyValue] using copyRegister_correct none L.y L.r (hw.1.trans hw.2.1.symm)
   (yr_nodup L hn) (by simp) s m

theorem complementBasis_value (control : Wire) (xs : List Wire) (b : BasisState) :
 regValue xs (complementBasis control xs b)=
 if b control then 2^xs.length-1-regValue xs b else regValue xs b := by
 cases hb:b control
 · apply regValue_congr
   intro q hq
   simp [complementBasis,hb,hq]
 · rw [regValue_congr xs _ (fun q=>!b q) (by intro q hq;simp[complementBasis,hb,hq])]
   exact regValue_complement xs b
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT FrontFacts
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem flags_nd (L : DecoderLayout) (hn : L.wires.Nodup) : [L.sigma,L.h,L.bias].Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have c:=List.nodup_iff_count.mp hn q
 simp only [DecoderLayout.wires,List.count_append] at c
 omega

theorem flags_bank_away (L : DecoderLayout) (hn : L.wires.Nodup) (f : Wire)
 (hf : f=L.h ∨ f=L.bias) (q : Wire) (hq:q∈L.y ∨ q∈L.r ∨ q∈L.carry) : q≠f := by
 intro eq
 subst q
 rcases hq with hy|hr|hc
 · exact flag_y_away L hn f (by rcases hf with rfl|rfl <;>simp) hy
 · exact source_r_away L hn f (by rcases hf with rfl|rfl <;>tauto) hr
 · exact carry_source_away L hn f (by rcases hf with rfl|rfl <;>tauto) hc

theorem front_on_banks (L : DecoderLayout) (hn : L.wires.Nodup) (b : BasisState)
 (q : Wire) (hq:q∈L.y ∨ q∈L.r ∨ q∈L.carry) :
 frontBasis L b q=complementBasis (L.Y 255) (L.y.take 255++L.r) b q := by
 have qh:=flags_bank_away L hn L.h (Or.inl rfl) q hq
 have qb:=flags_bank_away L hn L.bias (Or.inr rfl) q hq
 simp [frontBasis,writeBit,qh,qb]

theorem normalized_flag (L : DecoderLayout) (hn : L.wires.Nodup) (b : BasisState)
 (f : Wire) (hf:f∈[L.sigma,L.h,L.bias]) :
 complementBasis (L.Y 255) (L.y.take 255++L.r) b f=b f := by
 have ya:=flag_y_away L hn f hf
 have ra:f∉L.r:=by
   simp only[List.mem_cons,List.not_mem_nil,or_false] at hf
   apply source_r_away L hn f
   rcases hf with rfl|rfl|rfl <;>tauto
 simp [complementBasis,show f∉L.y.take 255 from fun h=>ya (List.mem_of_mem_take h),ra]

theorem front_source_sigma (L : DecoderLayout) (hn : L.wires.Nodup) (b : BasisState) :
 frontBasis L b L.sigma=b L.sigma := by
 have nd:=flags_nd L hn
 have sh:L.sigma≠L.h:=fun e=>(List.nodup_cons.mp nd).1 (by simp[e])
 have sb:L.sigma≠L.bias:=fun e=>(List.nodup_cons.mp nd).1 (by simp[e])
 simp only[frontBasis,writeBit,Function.update_of_ne sh,Function.update_of_ne sb]
 exact normalized_flag L hn b L.sigma (by simp)

theorem front_bias (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (clean : b L.bias=false) :
 frontBasis L b L.bias=(b (L.Y 255) && !b L.sigma) := by
 have norm:=normalize_nd L hw hn
 simp only[frontBasis,writeBit,Function.update_self]
 rw[normalized_flag L hn b L.bias (by simp),normalized_flag L hn b L.sigma (by simp)]
 simp [complementBasis,norm.2,clean]

theorem front_h (L : DecoderLayout) (hn : L.wires.Nodup)
 (b : BasisState) (clean : b L.h=false) :
 frontBasis L b L.h=
  (complementBasis (L.Y 255) (L.y.take 255++L.r) b (L.R 0) ^^
   complementBasis (L.Y 255) (L.y.take 255++L.r) b (L.Y 0)) := by
 have nd:=flags_nd L hn
 have hb:L.h≠L.bias:=fun e=>(List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp[e])
 simp only[frontBasis,writeBit,Function.update_of_ne hb,Function.update_self]
 rw[normalized_flag L hn b L.h (by simp),clean,Bool.false_xor]

theorem front_carry_clean (L : DecoderLayout) (hn : L.wires.Nodup)
 (b : BasisState) (clean : ∀q∈L.carry,b q=false) : ∀q∈L.carry,frontBasis L b q=false := by
 intro q hq
 rw[front_on_banks L hn b q (Or.inr (Or.inr hq))]
 have qy:q∉L.y := by
   intro hy
   exact carry_source_away L hn q (Or.inl hy) hq
 have qr:q∉L.r:=source_r_away L hn q (Or.inr (Or.inl hq))
 simp [complementBasis,show q∉L.y.take 255 from fun h=>qy (List.mem_of_mem_take h),qr,clean q hq]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT FrontValues
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem complement_subset_value (control : Wire) (xs region : List Wire)
 (sub : ∀q∈xs,q∈region) (b : BasisState) :
 regValue xs (complementBasis control region b)=
 if b control then 2^xs.length-1-regValue xs b else regValue xs b := by
 rw[regValue_congr xs _ (complementBasis control xs b) (by intro q hq;simp[complementBasis,hq,sub q hq])]
 exact complementBasis_value control xs b

theorem getD_testBit (xs : List Wire) (i : Nat) (b : BasisState) (hi:i<xs.length) :
 b (xs.getD i 0)=Nat.testBit (regValue xs b) i := by
 have h:=regValue_bit xs i 0 b hi
 rw[Nat.testBit_eq_decide_div_mod_eq]
 cases eq:b (xs.getD i 0) <;> simp only[eq,Bool.toNat_false,Bool.toNat_true] at h ⊢ <;>
   simp[←h]

theorem front_low_value (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) (b : BasisState) :
 regValue (L.y.take 255) (frontBasis L b)=
 if b (L.Y 255) then 2^255-1-regValue L.y b%2^255 else regValue L.y b%2^255 := by
 rw[regValue_congr (L.y.take 255) _ (complementBasis (L.Y 255) (L.y.take 255++L.r) b)
   (by intro q hq;exact front_on_banks L hn b q (Or.inl (List.mem_of_mem_take hq)))]
 rw[complement_subset_value _ _ _ (by intro q hq;exact List.mem_append_left _ hq)]
 have len:=hw.1
 rw[CuccaroStreamedSquareWideLayout.regValue_take_mod L.y 255 (by omega) b]
 simp only[List.length_take,len,Nat.min_eq_left (by omega : 255≤256)]

theorem front_r_value (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) (b : BasisState) :
 regValue L.r (frontBasis L b)=
 if b (L.Y 255) then 2^256-1-regValue L.r b else regValue L.r b := by
 rw[regValue_congr L.r _ (complementBasis (L.Y 255) (L.y.take 255++L.r) b)
   (by intro q hq;exact front_on_banks L hn b q (Or.inr (Or.inl hq)))]
 rw[complement_subset_value _ _ _ (by intro q hq;exact List.mem_append_right _ hq)]
 rw[hw.2.1]

theorem front_h_value (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (clean:b L.h=false) :
 frontBasis L b L.h=
   (Nat.testBit (regValue L.r (frontBasis L b)) 0 ^^
    Nat.testBit (regValue (L.y.take 255) (frontBasis L b)) 0) := by
 rw[front_h L hn b clean]
 have r:=getD_testBit L.r 0 (frontBasis L b) (by have len:=hw.2.1;omega)
 have y:=getD_testBit (L.y.take 255) 0 (frontBasis L b) (by simp[hw.1])
 have yget:(L.y.take 255).getD 0 0=L.Y 0 :=by
   cases eq:L.y with
   |nil=>have len:=hw.1;simp[eq] at len
   |cons a as=>simp[DecoderLayout.Y,eq]
 rw[yget] at y
 change frontBasis L b (L.R 0)=_ at r
 rw[front_on_banks L hn b (L.R 0) (Or.inr (Or.inl (r_mem L hw 0 (by omega))))] at r
 rw[front_on_banks L hn b (L.Y 0) (Or.inl (y_mem L hw 0 (by omega)))] at y
 rw[r,y]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT QuotientMath
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.TerminalGraph
open Secp256k1

def M : Int:=2^256
def C : Int:=2^32+977
def Q : Int:=((p:Int)-1)/2

theorem constants : (p:Int)=M-C ∧ M%2=0 ∧ C%2=1 ∧ C%4=1 ∧ C%4<2 ∧ Q%3=0 := by
  norm_num [M,C,Q,p]

/-- One's-complement normalization leaves only a nonnegative single-bit modular correction. -/
theorem normalized_equation (z r j sigma sy : Int)
    (eq : r=(3-2*sigma)*z-j*(p:Int))
    (sg : z=(1-2*sy)*((if sy=0 then z else -z-1)+sy))
    (hs : sy=0 ∨ sy=1) :
    let y:=if sy=0 then z else -z-1
    let t:=if sy=0 then r else -r-1
    let h:=(1-2*sy)*j
    t=(3-2*sigma)*y+2*(1-sigma)*sy-h*(p:Int) := by
  rcases hs with rfl|rfl <;> dsimp <;> simp [eq] <;> ring


theorem positive_correction (y t h sigma sy : Int)
    (eq : t=(3-2*sigma)*y+2*(1-sigma)*sy-h*(p:Int)) :
    (3-2*sigma)*y+2*(1-sigma)*sy+h*C=t+h*M := by
  rw [constants.1] at eq
  linear_combination -eq

/-- The quotient flag can be copied from the low parity, without a wide comparator. -/
theorem quotient_low (y t h sigma sy : Int)
    (hs : sigma=0 ∨ sigma=1) (hh : h=0 ∨ h=1)
    (eq : t=(3-2*sigma)*y+2*(1-sigma)*sy-h*(p:Int)) :
    (t-y)%2=h := by
  rcases hs with rfl|rfl <;> rcases hh with rfl|rfl <;>
    norm_num [p] at eq ⊢ <;> omega

/-- A paid comparator can clear the quotient after the graph carries are erased. -/
theorem quotient_threshold (y t h sy : Int)
    (hy : 0≤y) (hs : sy=0 ∨ sy=1) (hh : h=0 ∨ h=1)
    (eq : t=3*y+2*sy-h*(p:Int)) (bounds : -Q-sy≤t ∧ t≤Q) :
    h=1 ↔ Q/3<y ∨ (sy=1 ∧ y=Q/3) := by
  rcases hs with rfl|rfl <;> rcases hh with rfl|rfl <;>
    norm_num [Q,p] at eq bounds ⊢ <;> omega
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT FpQuotient
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphFp
open Arithmetic Secp256k1 Arithmetic.BalancedField

theorem center_triple (z : Int) (hz : Centered z) :
    centerFp (3*(z:Fp)) =
      if q<3*z then 3*z-(p:Int) else if 3*z< -q then 3*z+(p:Int) else 3*z := by
  have hp := BalancedField.constants
  have pc : ((p:Int):Fp)=0 := by simp
  unfold Centered at hz
  split_ifs with hi hlo
  · apply centered_cast_unique _ _ (centerFp_bounds _)
    · unfold Centered; constructor <;> omega
    · rw [centerFp_cast]; simp [Int.cast_sub,Int.cast_mul,pc]
  · apply centered_cast_unique _ _ (centerFp_bounds _)
    · unfold Centered; constructor <;> omega
    · rw [centerFp_cast]; simp [Int.cast_add,Int.cast_mul,pc]
  · apply centered_cast_unique _ _ (centerFp_bounds _)
    · unfold Centered; constructor <;> omega
    · rw [centerFp_cast]; simp

/-- The signed modular quotient has one bit of magnitude and follows the source sign. -/
theorem quotient_exists (Y : Fp) (sigma : Bool) :
    let z:=centerFp Y
    let r:=centerFp ((if sigma then 1 else 3)*Y)
    ∃ j : Int, r=(if sigma then 1 else 3)*z-j*(p:Int) ∧
      -1≤j ∧ j≤1 ∧ (0≤z → 0≤j) ∧ (z<0 → j≤0) ∧ (sigma=true → j=0) := by
  have hz:=centerFp_bounds Y
  have hp:=BalancedField.constants
  cases sigma
  · dsimp
    have eq:=center_triple (centerFp Y) hz
    rw [centerFp_cast] at eq
    unfold Centered at hz
    by_cases hi : q<3*centerFp Y
    · refine ⟨1,?_,by omega,by omega,?_,?_,by simp⟩
      · simpa [hi] using eq
      · intro _; omega
      · intro hn; omega
    · by_cases hlo : 3*centerFp Y< -q
      · refine ⟨-1,?_,by omega,by omega,?_,?_,by simp⟩
        · simpa [hi,hlo] using eq
        · intro hn; omega
        · intro _; omega
      · refine ⟨0,?_,by omega,by omega,?_,?_,by simp⟩
        · simpa [hi,hlo] using eq
        · intro _; omega
        · intro _; omega
  · dsimp; refine ⟨0,?_,by omega,by omega,?_,?_,by simp⟩
    · simp
    · intro _; omega
    · intro _; omega

/-- Actual Fp inputs supply every signed/range premise of the checked decoder algebra. -/
theorem normalized_bridge (Y : Fp) (sigma : Bool) :
    let z:=centerFp Y
    let r:=centerFp ((if sigma then 1 else 3)*Y)
    let sy:Int:=if z<0 then 1 else 0
    let y:=if sy=0 then z else -z-1
    let t:=if sy=0 then r else -r-1
    ∃ h : Int, (h=0 ∨ h=1) ∧ 0≤y ∧ -TerminalGraph.Q-sy≤t ∧ t≤TerminalGraph.Q ∧
      t=(3-2*(if sigma then 1 else 0))*y+
        2*(1-(if sigma then 1 else 0))*sy-h*(p:Int) ∧ (sigma=true → h=0) := by
  dsimp
  obtain ⟨j,he,hlo,hhi,hpos,hneg,hzero⟩:=quotient_exists Y sigma
  have hz:=centerFp_bounds Y
  have hr:=centerFp_bounds ((if sigma then 1 else 3)*Y)
  have he' : centerFp ((if sigma then 1 else 3)*Y)=
      (3-2*(if sigma then 1 else 0 : Int))*centerFp Y-j*(p:Int) := by
    cases sigma <;> simpa using he
  by_cases hs : centerFp Y<0
  · have sg : centerFp Y=(1-2*(1:Int))*(-centerFp Y-1+1) := by ring
    have hn:=TerminalGraph.normalized_equation _ _ _ (if sigma then 1 else 0) 1 he' sg (Or.inr rfl)
    simp only [show ¬(1:Int)=0 by omega,if_false] at hn
    unfold Centered at hz hr
    refine ⟨-j,?_,?_,?_,?_,?_,?_⟩
    · have hj:=hneg hs; omega
    · simp [hs]; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simpa [hs] using hn
    · intro ht; rw [hzero ht]; omega
  · have sg : centerFp Y=(1-2*(0:Int))*(centerFp Y+0) := by ring
    have hn:=TerminalGraph.normalized_equation _ _ _ (if sigma then 1 else 0) 0 he' sg (Or.inl rfl)
    simp only [mul_zero,sub_zero,if_pos rfl,zero_add,one_mul] at hn
    unfold Centered at hz hr
    refine ⟨j,?_,?_,?_,?_,?_,?_⟩
    · have hj:=hpos (by omega); omega
    · simp [hs]; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simpa [hs] using hn
    · exact hzero
end ECDSAAdd.Entrant.TerminalGraphFp


-- TERMINAL GRAPH COMPONENT WordBridge
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphFp
open Arithmetic Secp256k1 Arithmetic.BalancedField

theorem normalized_source_bounds (Y : Fp) :
    0≤(if centerFp Y<0 then -centerFp Y-1 else centerFp Y) ∧
    (if centerFp Y<0 then -centerFp Y-1 else centerFp Y)≤TerminalGraph.Q := by
  have h:=centerFp_bounds Y
  unfold Centered at h
  have eq : q=TerminalGraph.Q := rfl
  split_ifs <;> omega

theorem centerWord_msb (Y : Fp) :
    (centerWord Y).testBit 255=decide (centerFp Y<0) := by
  have hb : centerWord Y<2^256:=encodeWord_bound _ _
  have hs:=centerWord_sign Y
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hd : centerWord Y / 2^255 < 2 := by
    norm_num only [Nat.reducePow] at hb ⊢
    omega
  rw [Nat.mod_eq_of_lt hd]
  have eq : centerWord Y / 2^255 = 1 ↔ centerFp Y<0 := by
    norm_num only [Nat.reducePow] at hb hs ⊢
    omega
  simp only [eq]

/-- Complementing a complete canonical256-bit word is exact one's complement. -/
theorem full_complement_word (Y : Fp) :
    2^256-1-centerWord Y=encodeWord 256 (-centerFp Y-1) := by
  have hb : centerWord Y<2^256:=encodeWord_bound _ _
  have hd:=centerWord_decode Y
  have hc : 2^256-1-centerWord Y<2^256 := by omega
  have dec : signedDecode 256 (2^256-1-centerWord Y)= -centerFp Y-1 := by
    unfold signedDecode at hd ⊢
    norm_num only [Nat.reduceSub,Nat.reducePow] at hd hb ⊢
    split_ifs at hd ⊢ <;> omega
  rw [←dec,encode_decodeWord 256 _ hc]

def lowNormalize (w : Nat) (sign : Bool) : Nat :=
  if sign then 2^255+(2^255-1-w%2^255) else w

/-- Low255 complement retains the original source MSB and exposes the nonnegative magnitude. -/
theorem low_complement_word (Y : Fp) :
    lowNormalize (centerWord Y) (decide (centerFp Y<0))=
      (if centerFp Y<0 then -centerFp Y-1 else centerFp Y).toNat+
        (decide (centerFp Y<0)).toNat*2^255 := by
  have hb : centerWord Y<2^256:=encodeWord_bound _ _
  have hd:=centerWord_decode Y
  have hs:=centerWord_sign Y
  have hz:=centerFp_bounds Y
  unfold Centered at hz
  have hq:=BalancedField.constants
  unfold lowNormalize signedDecode at *
  norm_num only [Nat.reduceSub,Nat.reducePow] at *
  by_cases hn : centerFp Y<0
  · have ge : 2^255≤centerWord Y := hs.mpr hn
    norm_num only [Nat.reducePow] at ge
    have hdec : ¬centerWord Y<57896044618658097711785492504343953926634992332820282019728792003956564819968 := by omega
    simp only [if_neg hdec] at hd
    have pos : 0≤ -centerFp Y-1 := by omega
    have tn:=Int.toNat_of_nonneg pos
    simp [hn]
    omega
  · have lt : centerWord Y<2^255 := by have :=hs.not.mpr hn;omega
    norm_num only [Nat.reducePow] at lt
    simp only [if_pos lt] at hd
    have pos : 0≤centerFp Y := by omega
    have tn:=Int.toNat_of_nonneg pos
    simp [hn]
    omega
end ECDSAAdd.Entrant.TerminalGraphFp


-- TERMINAL GRAPH COMPONENT FrontMath
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphFp
open Arithmetic Secp256k1 Arithmetic.BalancedField

theorem encoded_positive (y : Nat) (sigma sy h : Bool) (t : Int)
 (eq : t=(3-2*(sigma.toNat:Int))*(y:Int)+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-(h.toNat:Int)*(p:Int)) :
 encodeWord 256 t=
 ((if sigma then y else 3*y)+2*(sy && !sigma).toNat+h.toNat*(2^32+977))%2^256 := by
 have corr:=TerminalGraph.positive_correction (y:Int) t (h.toNat:Int) (sigma.toNat:Int) (sy.toNat:Int) eq
 apply Int.ofNat_injective
 change (encodeWord 256 t:Int)=((((if sigma then y else 3*y)+2*(sy && !sigma).toNat+h.toNat*(2^32+977))%2^256 : Nat):Int)
 rw [encodeWord_cast,Int.natCast_emod]
 cases sigma <;> cases sy <;> cases h <;>
   norm_num [TerminalGraph.C,TerminalGraph.M] at corr ⊢ <;> omega

theorem encoded_parity (y : Nat) (sigma sy h : Bool) (t : Int)
 (eq : t=(3-2*(sigma.toNat:Int))*(y:Int)+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-(h.toNat:Int)*(p:Int)) :
 (Nat.testBit (encodeWord 256 t) 0 ^^ Nat.testBit y 0)=h := by
 have e:=encoded_positive y sigma sy h t eq
 rw [e,Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq]
 simp only [Nat.pow_zero,Nat.div_one]
 have parityEq : (((if sigma then y else 3*y)+2*(sy && !sigma).toNat+h.toNat*(2^32+977))%2^256)%2=(y+h.toNat)%2 := by
   cases sigma <;> cases sy <;> cases h <;> norm_num at * <;> omega
 rw [parityEq]
 cases h <;> simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
 · simp
 · have bound : y%2<2:=Nat.mod_lt _ (by omega)
   by_cases h0:y%2=0
   · have h1 : (y+1)%2=1:=by omega
     simp [h0,h1]
   · have h1 : y%2=1:=by omega
     have h2 : (y+1)%2=0:=by omega
     simp [h1,h2]
def frontY (Y : Fp) : Nat := (if centerFp Y<0 then -centerFp Y-1 else centerFp Y).toNat

def frontR (Y : Fp) (sigma : Bool) : Nat :=
 if centerFp Y<0 then 2^256-1-centerWord ((if sigma then 1 else 3)*Y)
 else centerWord ((if sigma then 1 else 3)*Y)

def frontH (Y : Fp) (sigma : Bool) : Bool := Nat.testBit (frontR Y sigma) 0 ^^ Nat.testBit (frontY Y) 0

theorem actual_front_equations (Y : Fp) (sigma : Bool) :
 frontR Y sigma=((if sigma then frontY Y else 3*frontY Y)+
  2*(decide (centerFp Y<0) && !sigma).toNat+(frontH Y sigma).toNat*(2^32+977))%2^256 ∧
 frontH Y sigma=(!sigma && !decide (frontY Y<((p-1)/2)/3+(!decide (centerFp Y<0)).toNat)) := by
 let sy:=decide (centerFp Y<0)
 let yi:=if centerFp Y<0 then -centerFp Y-1 else centerFp Y
 let ti:=if centerFp Y<0 then -centerFp ((if sigma then 1 else 3)*Y)-1 else centerFp ((if sigma then 1 else 3)*Y)
 have norm : ∃h:Int,(h=0 ∨ h=1) ∧ 0≤yi ∧ -TerminalGraph.Q-(sy.toNat:Int)≤ti ∧ ti≤TerminalGraph.Q ∧
   ti=(3-2*(sigma.toNat:Int))*yi+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-h*(p:Int) ∧ (sigma=true→h=0) := by
   have nn:=normalized_bridge Y sigma
   cases sigma <;> by_cases hs:centerFp Y<0 <;> simpa [sy,yi,ti,hs] using nn
 obtain ⟨h,hh,hy,hlo,hhi,he,hzero⟩:=norm
 let hb:=decide (h=1)
 have hc : (hb.toNat:Int)=h := by
   rcases hh with h0|h1
   · simp [hb,h0]
   · simp [hb,h1]
 have yc : (frontY Y:Int)=yi := Int.toNat_of_nonneg hy
 have he' : ti=(3-2*(sigma.toNat:Int))*(frontY Y:Int)+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-(hb.toNat:Int)*(p:Int) := by rw [yc,hc];exact he
 have rwrd : frontR Y sigma=encodeWord 256 ti := by
   by_cases hs:centerFp Y<0
   · simpa [frontR,ti,hs] using full_complement_word ((if sigma then 1 else 3)*Y)
   · simp [frontR,ti,hs,centerWord]
 have par : frontH Y sigma=hb := by
   unfold frontH
   rw [rwrd]
   exact encoded_parity _ _ _ _ _ he'
 constructor
 · rw [par,rwrd]
   exact encoded_positive _ _ _ _ _ he'
 · rw [par]
   have threshold : hb=(!sigma && !decide (frontY Y<((p-1)/2)/3+(!sy).toNat)) := by
     cases eqs:sigma with
     | true =>
       have hz:=hzero eqs
       simp [hb,hz]
     | false =>
       have hef : ti=3*yi+2*(sy.toNat:Int)-h*(p:Int) := by simpa [eqs] using he
       have hs : (sy.toNat:Int)=0 ∨ (sy.toNat:Int)=1 := by cases sy <;> simp
       have ht:=TerminalGraph.quotient_threshold yi ti h (sy.toNat:Int) hy hs hh hef ⟨hlo,hhi⟩
       have yn : 0≤(frontY Y:Int):=by omega
       norm_num [TerminalGraph.Q,p] at ht ⊢
       dsimp [hb]
       by_cases sign:sy=true
       · simp [sign] at ht ⊢
         rw [←yc] at ht
         by_cases hp:h=1 <;> simp [hp] at ht ⊢ <;> omega
       · have sf:sy=false:=Bool.eq_false_iff.mpr sign
         simp [sf] at ht ⊢
         rw [←yc] at ht
         by_cases hp:h=1 <;> simp [hp] at ht ⊢ <;> omega
   simpa [sy] using threshold
end ECDSAAdd.Entrant.TerminalGraphFp


-- TERMINAL GRAPH COMPONENT ActualFront
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic Secp256k1 Arithmetic.BalancedField TerminalGraphFp

theorem normalized_low_word (Y : Fp) :
 (if decide (centerFp Y<0) then 2^255-1-centerWord Y%2^255 else centerWord Y%2^255)=frontY Y := by
 have h:=low_complement_word Y
 have hs:=centerWord_sign Y
 by_cases neg:centerFp Y<0
 · simp [lowNormalize,frontY,neg] at h ⊢
   omega
 · have lt:centerWord Y<2^255:=by have nn:=hs.not.mpr neg;omega
   simp [lowNormalize,frontY,neg] at h ⊢
   simpa only[Nat.reducePow] using (Nat.mod_eq_of_lt lt).trans h

theorem actual_front_values (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (Y : Fp) (sigma : Bool)
 (ys : regValue L.y b=centerWord Y)
 (rs : regValue L.r b=centerWord ((if sigma then 1 else 3)*Y))
 (sig : b L.sigma=sigma) (hc:b L.h=false) (bc:b L.bias=false) :
 let f:=frontBasis L b
 regValue (L.y.take 255) f=frontY Y ∧ regValue L.r f=frontR Y sigma ∧
 f L.h=frontH Y sigma ∧ f L.bias=(decide (centerFp Y<0) && !sigma) ∧
 f L.sigma=sigma ∧ f (L.Y 255)=decide (centerFp Y<0) := by
 have msb:b (L.Y 255)=decide (centerFp Y<0) := by
   have g:=getD_testBit L.y 255 b (by have len:=hw.1;omega)
   rw[ys,centerWord_msb] at g
   exact g
 have fy:regValue (L.y.take 255) (frontBasis L b)=frontY Y := by
   rw[front_low_value L hw hn,ys,msb]
   exact normalized_low_word Y
 have fr:regValue L.r (frontBasis L b)=frontR Y sigma := by
   rw[front_r_value L hw hn,rs,msb]
   simp only[frontR]
   split_ifs <;>simp_all
 have fh:frontBasis L b L.h=frontH Y sigma := by
   rw[front_h_value L hw hn b hc,fy,fr]
   rfl
 refine ⟨fy,fr,fh,?_,?_,?_⟩
 · rw[front_bias L hw hn b bc,msb,sig]
 · rw[front_source_sigma L hn b,sig]
 · rw[front_on_banks L hn b (L.Y 255) (Or.inl (y_mem L hw 255 (by omega)))]
   simp only[complementBasis,if_neg (normalize_nd L hw hn).2,msb]

theorem actual_front_scalar (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (Y : Fp) (sigma : Bool)
 (ys : regValue L.y b=centerWord Y)
 (rs : regValue L.r b=centerWord ((if sigma then 1 else 3)*Y))
 (sig : b L.sigma=sigma) (hc:b L.h=false) (bc:b L.bias=false) :
 let f:=frontBasis L b
 regValue L.r f=((if f L.sigma then regValue (L.y.take 255) f else 3*regValue (L.y.take 255) f)+
   2*(f L.bias).toNat+(f L.h).toNat*(2^32+977))%2^256 ∧
 f L.h=(!f L.sigma && !(decide (regValue (L.y.take 255) f<((p-1)/2)/3+(!f (L.Y 255)).toNat))) := by
 have v:=actual_front_values L hw hn b Y sigma ys rs sig hc bc
 dsimp only
 rw[v.1,v.2.1,v.2.2.1,v.2.2.2.1,v.2.2.2.2.1,v.2.2.2.2.2]
 exact actual_front_equations Y sigma
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AddCarrySteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def aStepValue (L : DecoderLayout) (s : BasisState) (i : Nat) : Bool:=
 if i=0 then carryBit false (s L.sigma) (s (L.Y 0) ^^ s L.sigma)
 else carryBit (s (L.Y (i-1))) (s (L.Y i) ^^ s L.sigma) (s (L.A (i-1)))

theorem step_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (h0 : i≠0) :
    [L.Y i,L.A (i-1),L.A i].Nodup := by
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
  not_or,not_false_eq_true,and_true]
 exact ⟨⟨y_ne_a L hw hn i (i-1) (by omega) (by omega),
   y_ne_a L hw hn i i (by omega) hi⟩,
   carry_ne_carry L hw hn (i-1) i (by omega) hi (by omega)⟩

theorem step_source_away (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (h0 : i≠0) :
    ∀q∈(some (L.Y (i-1))),q∉[L.Y i,L.A (i-1),L.A i] := by
 intro q hq
 have eq:L.Y (i-1)=q:=by simpa using hq
 subst q
 simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
 exact ⟨y_ne_y L hw hn (i-1) i (by omega) (by omega) (by omega),
   y_ne_a L hw hn (i-1) (i-1) (by omega) (by omega),
   y_ne_a L hw hn (i-1) i (by omega) hi⟩

theorem addCarry_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (s : State) (m : List Bool) :
    run (addCarry L i) m s=
      ⟨s.phase,writeBit s.basis (L.A i) (s.basis (L.A i) ^^ aStepValue L s.basis i)⟩ := by
 by_cases h0:i=0
 · subst i
   have sy:=sigma_ne_y L hw hn 0 (by omega)
   have sa:=sigma_ne_a L hw hn 0 (by omega)
   have ya:=y_ne_a L hw hn 0 0 (by omega) (by omega)
   change run (cxWindow L.sigma (L.Y 0) [.CCX L.sigma (L.Y 0) (L.A 0)]) m s=_
   apply cxWindow_write L.sigma (L.Y 0) (L.A 0) _ sy sa ya
   intro r
   simp [run,cxBasis,writeBit,sy,Ne.symm sy,Ne.symm sa,Ne.symm ya,aStepValue,carryBit]
 · have h:=windowMajority_run (⟨some (L.Y (i-1)),false⟩ : MappedBit)
     L.sigma (L.Y i) (L.A (i-1)) (L.A i) (step_nd L hw hn i hi h0)
     (step_source_away L hw hn i hi h0) (sigma_ne_y L hw hn i (by omega))
     (sigma_ne_a L hw hn i hi) s m
   simpa only [addCarry,h0,ite_false,cxWindow,mappedMajority,Bool.false_eq_true,
     aStepValue,MappedBit.value,Bool.xor_false,Bool.false_xor,Option.map_some,Option.getD_some] using h

theorem eraseAddCarry_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (s : State) (m : List Bool)
    (known : s.basis (L.A i)=aStepValue L s.basis i) :
    run (eraseAddCarry L i) m s=⟨s.phase,writeBit s.basis (L.A i) false⟩ := by
 by_cases h0:i=0
 · subst i
   have sy:=sigma_ne_y L hw hn 0 (by omega)
   have sa:=sigma_ne_a L hw hn 0 (by omega)
   have ya:=y_ne_a L hw hn 0 0 (by omega) (by omega)
   have nd:[L.sigma,L.Y 0,L.A 0].Nodup:=by simp [sy,sa,ya]
   change run (cxWindow L.sigma (L.Y 0)
     (mappedEraseCarry ⟨none,false⟩ L.sigma (L.Y 0) (L.A 0))) m s=_
   apply cxWindow_write L.sigma (L.Y 0) (L.A 0) _ sy sa ya
   intro r
   apply mappedEraseCarry_correct ⟨none,false⟩ L.sigma (L.Y 0) (L.A 0) nd (by simp)
   simpa [cxBasis,writeBit,sy,Ne.symm sy,Ne.symm ya,MappedBit.value,aStepValue] using known
 · have h:=windowErase_run (⟨some (L.Y (i-1)),false⟩ : MappedBit)
     L.sigma (L.Y i) (L.A (i-1)) (L.A i) (step_nd L hw hn i hi h0)
     (step_source_away L hw hn i hi h0) (sigma_ne_y L hw hn i (by omega))
     (sigma_ne_a L hw hn i hi) s m (by simpa [aStepValue,h0,MappedBit.value] using known)
   simpa only [eraseAddCarry,h0,ite_false,cxWindow,mappedEraseCarry,Bool.false_eq_true] using h
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AddChain
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def aExpected (L : DecoderLayout) (origin : BasisState) : Nat→Bool
 | 0 => carryBit false (origin L.sigma) (origin (L.Y 0) ^^ origin L.sigma)
 | j+1 => carryBit (origin (L.Y j)) (origin (L.Y (j+1)) ^^ origin L.sigma) (aExpected L origin j)

structure AddFrame (L : DecoderLayout) (origin : State) (nDone : Nat) (s : State) : Prop where
 phase : s.phase=origin.phase
 sigma : s.basis L.sigma=origin.basis L.sigma
 source : ∀ i, i<256 → s.basis (L.Y i)=origin.basis (L.Y i)
 computed : ∀ i, i< nDone → s.basis (L.A i)=aExpected L origin.basis i
 clean : ∀ i, nDone≤ i → i<255 → s.basis (L.A i)=false

theorem addFrame_initial (L : DecoderLayout) (s : State)
 (clean : ∀ i, i<255 → s.basis (L.A i)=false) : AddFrame L s 0 s := by
 refine ⟨rfl,rfl,fun _ _=>rfl,?_,?_⟩
 · intro i hi;omega
 · intro i _ hi;exact clean i hi

theorem value_expected (L : DecoderLayout) (origin s : State) (nDone i : Nat)
 (f : AddFrame L origin nDone s) (hi : i<255) (hd : i≤nDone) :
 aStepValue L s.basis i=aExpected L origin.basis i := by
 by_cases h0:i=0
 · subst i
   simp only [aStepValue,ite_true,aExpected]
   rw [f.sigma,f.source 0 (by omega)]
 · obtain ⟨j,rfl⟩:∃j,i=j+1:=⟨i-1,by omega⟩
   simp only [aStepValue,Nat.add_sub_cancel,show ¬j+1=0 by omega,ite_false,aExpected]
   rw [f.source j (by omega),f.source (j+1) (by omega),f.sigma,f.computed j (by omega)]

theorem addFrame_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hi : i<255) (f : AddFrame L origin i s) (m : List Bool) :
 AddFrame L origin (i+1) (run (addCarry L i) m s) := by
 have val:=value_expected L origin s i i f hi (le_refl _)
 have zero:=f.clean i (le_refl _) hi
 rw [addCarry_run L hw hn i hi s m,zero,val,Bool.false_xor]
 refine ⟨f.phase,?_,?_,?_,?_⟩
 · simpa only [writeBit,Function.update_of_ne (sigma_ne_a L hw hn i hi)] using f.sigma
 · intro j hj
   simpa only [writeBit,Function.update_of_ne (y_ne_a L hw hn j i hj hi)] using f.source j hj
 · intro j hj
   by_cases eq:j=i
   · subst j;simp [writeBit]
   · have ne:=carry_ne_carry L hw hn j i (by omega) hi eq
     simpa only [writeBit,Function.update_of_ne ne] using f.computed j (by omega)
 · intro j hji hj
   have ne:=carry_ne_carry L hw hn j i hj hi (by omega)
   simpa only [writeBit,Function.update_of_ne ne] using f.clean j (by omega) hj

theorem addFrame_erase_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hi : i<255) (f : AddFrame L origin (i+1) s) (m : List Bool) :
 AddFrame L origin i (run (eraseAddCarry L i) m s) := by
 have val:=value_expected L origin s (i+1) i f hi (by omega)
 have known:s.basis (L.A i)=aStepValue L s.basis i:=(f.computed i (by omega)).trans val.symm
 rw [eraseAddCarry_run L hw hn i hi s m known]
 refine ⟨f.phase,?_,?_,?_,?_⟩
 · simpa only [writeBit,Function.update_of_ne (sigma_ne_a L hw hn i hi)] using f.sigma
 · intro j hj
   simpa only [writeBit,Function.update_of_ne (y_ne_a L hw hn j i hj hi)] using f.source j hj
 · intro j hj
   have ne:=carry_ne_carry L hw hn j i (by omega) hi (by omega)
   simpa only [writeBit,Function.update_of_ne ne] using f.computed j (by omega)
 · intro j hji hj
   by_cases eq:j=i
   · subst j;simp [writeBit]
   · have ne:=carry_ne_carry L hw hn j i hj hi eq
     simpa only [writeBit,Function.update_of_ne ne] using f.clean j (by omega) hj

theorem add_forward_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (f : AddFrame L origin 0 s) (n : Nat) (bound : n≤255) (m : List Bool) :
 AddFrame L origin n (run ((List.range n).flatMap (addCarry L)) m s) := by
 induction n generalizing m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   apply addFrame_step L hw hn origin _ n (by omega)
   exact ih (by omega) _

theorem add_reverse_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (n : Nat) (bound : n≤255) (s : State) (f : AddFrame L origin n s) (m : List Bool) :
 AddFrame L origin 0 (run ((List.range n).reverse.flatMap (eraseAddCarry L)) m s) := by
 induction n generalizing s m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range_succ,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
     List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   apply ih (by omega)
   exact addFrame_erase_step L hw hn origin s n (by omega) f _
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AddOutside
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run addCarry eraseAddCarry

theorem add_forward_outside (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (n : Nat) (bound : n ≤ 255) (s : State) (m : List Bool) (q : Wire)
 (away : q ∉ L.carry) :
 (run ((List.range n).flatMap (addCarry L)) m s).basis q=s.basis q := by
 induction n generalizing m with
 | zero => simp [run]
 | succ n ih =>
   rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   rw [addCarry_run L hw hn n (by omega)]
   have ne:q ≠ L.A n := fun e => away (e ▸ a_mem L hw n (by omega))
   simp only [writeBit,Function.update_of_ne ne]
   exact ih (by omega) _

theorem add_reverse_outside (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (n : Nat) (bound : n ≤ 255) (s : State)
 (f : AddFrame L origin n s) (m : List Bool) (q : Wire) (away : q ∉ L.carry) :
 (run ((List.range n).reverse.flatMap (eraseAddCarry L)) m s).basis q=s.basis q := by
 induction n generalizing s m with
 | zero => simp [run]
 | succ n ih =>
   rw [List.range_succ,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
     List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   have f' := addFrame_erase_step L hw hn origin s n (by omega) f m
   rw [ih (by omega) _ f' _]
   have val:=value_expected L origin s (n+1) n f (by omega) (by omega)
   have known:s.basis (L.A n)=aStepValue L s.basis n := (f.computed n (by omega)).trans val.symm
   rw [eraseAddCarry_run L hw hn n (by omega) s m known]
   have ne:q ≠ L.A n := fun e => away (e ▸ a_mem L hw n (by omega))
   simp only [writeBit,Function.update_of_ne ne]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamReverse
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run xorList streamCarry eraseCorrectionCarry

theorem stream_to_erase (L : DecoderLayout) (origin s : State)
 (f : StreamFrame L origin 255 s) : EraseBFrame L origin 255 s := by
 refine ⟨f.phase,f.outside,f.stored,?_⟩
 intro j hj hbound
 have eq:j=255:=by omega
 subst j
 exact f.current

theorem eraseBFrame_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hlo : 1 ≤ i) (hi : i ≤ 255)
 (graph : BGraph L origin.basis) (f : EraseBFrame L origin i s) (m : List Bool) :
 EraseBFrame L origin (i-1) (run (eraseCorrectionCarry L i) m s) := by
 rw [eraseCorrectionCarry_run L hw hn origin s i hlo hi graph f m]
 refine ⟨f.phase,?_,?_,?_⟩
 · intro q hq
   have ne:q≠L.R (i-1):=fun e=>hq (e ▸ r_mem L hw (i-1) (by omega))
   simpa only [writeBit,Function.update_of_ne ne] using f.outside q hq
 · intro j hj
   have ne:=r_ne_r L hw hn j (i-1) (by omega) (by omega) (by omega)
   simpa only [writeBit,Function.update_of_ne ne] using f.live j (by omega)
 · intro j hji hj
   by_cases eq:j=i-1
   · subst j;simp [writeBit]
   · have ne:=r_ne_r L hw hn j (i-1) hj (by omega) eq
     simpa only [writeBit,Function.update_of_ne ne] using f.clean j (by omega) hj

theorem eraseB_reverse_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (graph : BGraph L origin.basis) (n : Nat) (bound : n ≤ 255)
 (s : State) (f : EraseBFrame L origin n s) (m : List Bool) :
 EraseBFrame L origin 0 (run ((List.range' 1 n).reverse.flatMap (eraseCorrectionCarry L)) m s) := by
 induction n generalizing s m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range'_1_concat,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
     List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take,Nat.add_comm 1 n]
   apply ih (by omega)
   have a:=eraseBFrame_step L hw hn origin s (n+1) (by omega) bound graph f
     m
   simpa only [Nat.add_sub_cancel] using a

def bBlock (L : DecoderLayout) : Program:=
 xorList (bSources L 0) (L.R 0)++(List.range' 1 255).flatMap (streamCarry L)++
   (List.range' 1 255).reverse.flatMap (eraseCorrectionCarry L)

theorem bBlock_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (graph : BGraph L origin.basis)
 (low : origin.basis (L.R 0)=parity (bSources L 0) origin.basis) (m : List Bool) :
 (run (bBlock L) m origin).phase=origin.phase ∧
 (∀q,q∉L.r → (run (bBlock L) m origin).basis q=origin.basis q) ∧
 ∀i,i<256 → (run (bBlock L) m origin).basis (L.R i)=false := by
 have f : EraseBFrame L origin 0 (run (bBlock L) m origin) := by
   rw [bBlock,List.append_assoc,run_append,run_take]
   rw [run_append,run_take]
   apply eraseB_reverse_frame L hw hn origin graph 255 (le_refl _)
   apply stream_to_erase
   apply stream_forward_frame L hw hn origin _ _ 255 (le_refl _)
   exact stream_initial L hw hn origin _ low
 exact ⟨f.phase,f.outside,fun i hi=>f.clean i (by omega) hi⟩
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CoreStages
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run addCarry eraseAddCarry bBlock

def aProgram (L : DecoderLayout) : Program := (List.range 255).flatMap (addCarry L)
def eraseAProgram (L : DecoderLayout) : Program := (List.range 255).reverse.flatMap (eraseAddCarry L)

theorem aProgram_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean : ∀i,i<255 → s.basis (L.A i)=false) (m : List Bool) :
 AddFrame L s 255 (run (aProgram L) m s) :=
 add_forward_frame L hw hn s s (addFrame_initial L s clean) 255 (le_refl _) m

theorem eraseAProgram_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (f : AddFrame L origin 255 s) (m : List Bool) :
 AddFrame L origin 0 (run (eraseAProgram L) m s) :=
 add_reverse_frame L hw hn origin 255 (le_refl _) s f m

attribute [local irreducible] aProgram eraseAProgram

theorem bBlock_addFrame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin a : State) (af : AddFrame L origin 255 a)
 (graph : BGraph L a.basis) (low : a.basis (L.R 0)=parity (bSources L 0) a.basis)
 (m : List Bool) : AddFrame L origin 255 (run (bBlock L) m a) := by
 have bc:=bBlock_correct L hw hn a graph low m
 refine ⟨bc.1.trans af.phase,?_,?_,?_,?_⟩
 · exact (bc.2.1 L.sigma (source_r_away L hn _ (by tauto))).trans af.sigma
 · intro i hi
   exact (bc.2.1 (L.Y i) (source_r_away L hn _ (Or.inl (y_mem L hw i hi)))).trans (af.source i hi)
 · intro i hi
   exact (bc.2.1 (L.A i) (source_r_away L hn _ (Or.inr (Or.inl (a_mem L hw i hi))))).trans (af.computed i hi)
 · intro i hi hb;omega
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CarryMath
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalCarryMath
open Arithmetic

def value : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat+2*value bs

def sums : List Bool → List Bool → Bool → List Bool
  | a::as,b::bs,c => sumBit a b c::sums as bs (carryBit a b c)
  | _,_,_ => []

def carryAt : List Bool → List Bool → Bool → Nat → Bool
  | _,_,c,0 => c
  | a::as,b::bs,c,n+1 => carryAt as bs (carryBit a b c) n
  | _,_,_,_ => false

theorem sums_length (A B : List Bool) (c : Bool) (hlen : A.length=B.length) :
    (sums A B c).length=A.length := by
  induction A generalizing B c with
  | nil => cases B <;> simp_all [sums]
  | cons a as ih =>
    cases B with
    | nil => simp at hlen
    | cons b bs => simp only [sums,List.length_cons];rw [ih bs _ (by simpa using hlen)]

theorem sums_value (A B : List Bool) (c : Bool) (hlen : A.length=B.length) :
    value (sums A B c)=(value A+value B+c.toNat)%2^A.length := by
  induction A generalizing B c with
  | nil => cases B with
    | nil => cases c <;> decide
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases B with
    | nil => simp at hlen
    | cons b bs =>
      simp only [sums,value,List.length_cons]
      rw [ih bs _ (by simpa using hlen)]
      exact sum_value_step a b c (value as) (value bs) as.length

theorem value_injective (A B : List Bool) (hlen : A.length=B.length)
    (hv : value A=value B) : A=B := by
  induction A generalizing B with
  | nil => cases B <;> simp_all
  | cons a as ih =>
    cases B with
    | nil => simp at hlen
    | cons b bs =>
      have head : a=b := by
        cases a <;> cases b <;> simp only [value,Bool.toNat_false,Bool.toNat_true] at hv ⊢ <;> omega
      subst b
      have tail : value as=value bs := by simp only [value] at hv;omega
      rw [ih bs (by simpa using hlen) tail]

theorem graph_eq_sums (A B R : List Bool) (c : Bool)
    (hlen : A.length=B.length) (hr : R.length=A.length)
    (hv : value R=(value A+value B+c.toNat)%2^A.length) : R=sums A B c :=
  value_injective R _ (hr.trans (sums_length A B c hlen).symm)
    (hv.trans (sums_value A B c hlen).symm)

theorem sums_at (A B : List Bool) (c : Bool) (i : Nat)
    (hlen : A.length=B.length) (hi : i<A.length) :
    (sums A B c).getD i false=
      sumBit (A.getD i false) (B.getD i false) (carryAt A B c i) := by
  induction i generalizing A B c with
  | zero =>
    cases A with
    | nil => simp at hi
    | cons a as => cases B with
      | nil => simp at hlen
      | cons b bs => rfl
  | succ i ih =>
    cases A with
    | nil => simp at hi
    | cons a as => cases B with
      | nil => simp at hlen
      | cons b bs =>
        simpa only [sums,carryAt,List.getD_cons_succ] using
          ih as bs (carryBit a b c) (by simpa using hlen) (by simpa using hi)

theorem graph_carry_extract (A B R : List Bool) (c : Bool) (i : Nat)
    (hlen : A.length=B.length) (hr : R.length=A.length)
    (hv : value R=(value A+value B+c.toNat)%2^A.length) (hi : i<A.length) :
    carryAt A B c i=R.getD i false ^^ A.getD i false ^^ B.getD i false := by
  rw [graph_eq_sums A B R c hlen hr hv,sums_at A B c i hlen hi]
  cases A.getD i false <;> cases B.getD i false <;> cases carryAt A B c i <;> decide
end ECDSAAdd.Entrant.TerminalCarryMath


-- TERMINAL GRAPH COMPONENT GraphValues
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic TerminalCarryMath

def bitVector (n : Nat) (f : Nat → Bool) : List Bool := (List.range n).map f
@[simp] theorem bitVector_length (n : Nat) (f : Nat → Bool) : (bitVector n f).length=n := by simp [bitVector]
theorem bitVector_get (n : Nat) (f : Nat → Bool) (i : Nat) (hi : i<n) :
 (bitVector n f).getD i false=f i := by
 rw [List.getD_eq_getElem _ _ (by simpa using hi)]
 simp [bitVector]

theorem carryAt_next (A B : List Bool) (c : Bool) (i : Nat)
 (ha : i<A.length) (hb : i<B.length) :
 carryAt A B c (i+1)=carryBit (A.getD i false) (B.getD i false) (carryAt A B c i) := by
 induction i generalizing A B c with
 | zero => cases A with
   | nil => simp at ha
   | cons a as => cases B with
     | nil => simp at hb
     | cons b bs => simp [carryAt]
 | succ i ih => cases A with
   | nil => simp at ha
   | cons a as => cases B with
     | nil => simp at hb
     | cons b bs => simpa only [carryAt,List.getD_cons_succ] using ih as bs (carryBit a b c) (by simpa using ha) (by simpa using hb)

theorem correctionSources_parity (L : DecoderLayout) (i : Nat) (s : BasisState) :
 parity (correctionSources L i) s=(correction L i).value s := by
 unfold correctionSources correction
 split_ifs <;> simp [MappedBit.value,parity]

theorem parity_cat (xs ys : List Wire) (s : BasisState) :
 parity (xs++ys) s=(parity xs s ^^ parity ys s) := by
 induction xs with
 | nil => simp [parity]
 | cons x xs ih =>
   change (s x ^^ parity (xs++ys) s)=((s x ^^ parity xs s) ^^ parity ys s)
   rw [ih,Bool.xor_assoc]

def rawBits (L : DecoderLayout) (s : BasisState) : List Bool := bitVector 256 (fun i=>parity (rawSources L i) s)
def correctionBits (L : DecoderLayout) (s : BasisState) : List Bool := bitVector 256 (fun i=>(correction L i).value s)
def resultBits (L : DecoderLayout) (s : BasisState) : List Bool := bitVector 256 (fun i=>s (L.R i))

theorem graph_of_bit_values (L : DecoderLayout) (s : BasisState)
 (hv : value (resultBits L s)=(value (rawBits L s)+value (correctionBits L s))%2^256) :
 BGraph L s ∧ s (L.R 0)=parity (bSources L 0) s := by
 let A:=rawBits L s
 let B:=correctionBits L s
 let R:=resultBits L s
 have la:A.length=256:=bitVector_length _ _
 have lb:B.length=256:=bitVector_length _ _
 have lr:R.length=256:=bitVector_length _ _
 have av (i : Nat) (hi : i<256) : A.getD i false=parity (rawSources L i) s:=bitVector_get _ _ _ hi
 have bv (i : Nat) (hi : i<256) : B.getD i false=(correction L i).value s:=bitVector_get _ _ _ hi
 have rv (i : Nat) (hi : i<256) : R.getD i false=s (L.R i):=bitVector_get _ _ _ hi
 have val : value R=(value A+value B+false.toNat)%2^A.length := by simpa [la] using hv
 have extract (i : Nat) (hi : i<256) : carryAt A B false i=bExpected L s i := by
   have old:=graph_carry_extract A B R false i (la.trans lb.symm) (lr.trans la.symm) val (by omega)
   have e : carryAt A B false i=(R.getD i false ^^ A.getD i false ^^ B.getD i false) := by
     cases hc:carryAt A B false i <;> cases hr:R.getD i false <;> cases ha:A.getD i false <;> cases hb:B.getD i false <;> simp_all
   rw [rv i hi,av i hi,bv i hi] at e
   rw [e]
   simp only [bExpected,bSources,parity_cat,correctionSources_parity,Bool.xor_assoc]
 constructor
 · intro i hl hi
   rw [←extract i (by omega)]
   have eq : i-1+1=i:=by omega
   have step:=carryAt_next A B false (i-1) (by omega) (by omega)
   rw [eq] at step
   rw [step]
   have prev : carryAt A B false (i-1)=(if i=1 then false else bExpected L s (i-1)) := by
     split_ifs with e
     · subst i;rfl
     · exact extract _ (by omega)
   rw [prev,av (i-1) (by omega),bv (i-1) (by omega)]
   cases (correction L (i-1)).value s <;> cases parity (rawSources L (i-1)) s <;> cases (if i=1 then false else bExpected L s (i-1)) <;> decide
 · have e:=sums_at A B false 0 (la.trans lb.symm) (by rw [la];omega)
   have eq:=graph_eq_sums A B R false (la.trans lb.symm) (lr.trans la.symm) val
   rw [←eq] at e
   rw [rv 0 (by omega),av 0 (by omega),bv 0 (by omega)] at e
   simpa [bSources,parity_cat,correctionSources_parity,sumBit,carryAt] using e
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT GraphRaw
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic TerminalCarryMath

theorem value_append_bits (xs ys : List Bool) :
 value (xs++ys)=value xs+2^xs.length*value ys := by
 induction xs with
 | nil => simp [value]
 | cons x xs ih => simp only [List.cons_append,value,List.length_cons,ih,Nat.pow_succ];ring

theorem value_map_register (xs : List Wire) (s : BasisState) : value (xs.map s)=regValue xs s := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
   change (s x).toNat+2*value (xs.map s)=(if s x then 1 else 0)+2*regValue xs s
   rw [ih];cases s x <;> rfl

theorem getD_map_valid {α β : Type} (xs : List α) (f : α→β) (d : α) (e : β) (i : Nat) (hi : i<xs.length) :
 (xs.map f).getD i e=f (xs.getD i d) := by
 rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi]
 simp

theorem bitVector_register (xs : List Wire) (s : BasisState) :
 bitVector xs.length (fun i=>s (xs.getD i 0))=xs.map s := by
 apply List.ext_getElem (by simp)
 intro i hi hj
 have bound:i<xs.length:=by simpa using hi
 rw [←List.getD_eq_getElem _ false hi,←List.getD_eq_getElem _ false hj]
 rw [bitVector_get _ _ _ bound,getD_map_valid xs s 0 false i bound]

theorem resultBits_value (L : DecoderLayout) (hw : L.Widths) (s : BasisState) :
 value (resultBits L s)=regValue L.r s := by
 change value (bitVector 256 (fun i=>s (L.r.getD i 0)))=_
 rw [←hw.2.1,bitVector_register,value_map_register]

theorem complement_value (xs : List Bool) : value (xs.map not)=2^xs.length-1-value xs := by
 have hs : value (xs.map not)+value xs+1=2^xs.length := by
   induction xs with
   | nil => rfl
   | cons x xs ih => simp only [List.map_cons,value,List.length_cons,Nat.pow_succ];cases x <;> simp only [Bool.not_true,Bool.not_false,Bool.toNat_true,Bool.toNat_false] <;> omega
 omega

def lowBits (L : DecoderLayout) (s : BasisState) : List Bool := (L.y.take 255).map s

theorem lowBits_length (L : DecoderLayout) (hw : L.Widths) (s : BasisState) : (lowBits L s).length=255 := by simp [lowBits,hw.1]

theorem lowBits_get (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<255) :
 (lowBits L s).getD i false=s (L.Y i) := by
 unfold lowBits DecoderLayout.Y
 rw [getD_map_valid _ s 0 false i (by simp [hw.1];omega)]
 rw [List.getD_eq_getElem _ _ (by simp [hw.1];omega),List.getD_eq_getElem _ _ (by rw [hw.1];omega)]
 simp [lowBits,DecoderLayout.Y]

def sourceA (L : DecoderLayout) (s : BasisState) : List Bool := false::lowBits L s
def sourceB (L : DecoderLayout) (s : BasisState) : List Bool := (lowBits L s++[false]).map (fun b=>b^^s L.sigma)

theorem sources_length (L : DecoderLayout) (hw : L.Widths) (s : BasisState) :
 (sourceA L s).length=256 ∧ (sourceB L s).length=256 := by simp [sourceA,sourceB,lowBits_length L hw s]

theorem sources_value (L : DecoderLayout) (hw : L.Widths) (s : BasisState) :
 (value (sourceA L s)+value (sourceB L s)+(s L.sigma).toNat)%2^256=
 (if s L.sigma then regValue (L.y.take 255) s else 3*regValue (L.y.take 255) s)%2^256 := by
 have vy : value (lowBits L s)=regValue (L.y.take 255) s:=value_map_register _ _
 have ly:=lowBits_length L hw s
 have h:=regValue_lt (L.y.take 255) s
 have ln : (L.y.take 255).length=255:=by simp [hw.1]
 rw [ln] at h
 cases eq:s L.sigma with
 | false => simp [sourceA,sourceB,eq,value_append_bits,value,vy];congr 1;omega
 | true =>
   have bb : sourceB L s=(lowBits L s++[false]).map not := by
     simp only [sourceB,eq];congr 1;funext b;cases b <;> rfl
   rw [bb,complement_value]
   simp only [sourceA,value,List.length_append,List.length_singleton,ly,value_append_bits,vy,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,eq,Bool.toNat_true,ite_true]
   norm_num only [Nat.reducePow] at h ⊢
   omega
theorem sourceA_get (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<256) :
 (sourceA L s).getD i false=(if i=0 then false else s (L.Y (i-1))) := by
 cases i with
 | zero => rfl
 | succ i => simpa only [sourceA,List.getD_cons_succ,Nat.add_sub_cancel,show ¬i+1=0 by omega,ite_false] using lowBits_get L hw s i (by omega)

theorem sourceB_get (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<256) :
 (sourceB L s).getD i false=(if i<255 then s (L.Y i) ^^ s L.sigma else s L.sigma) := by
 unfold sourceB
 rw [getD_map_valid _ _ false false i (by simp [lowBits_length L hw s];omega)]
 by_cases h:i<255
 · rw [if_pos h,List.getD_append _ _ _ _ (by rw [lowBits_length L hw s];omega),lowBits_get L hw s i h]
 · have e:i=255:=by omega
   subst i
   rw [List.getD_eq_getElem _ _ (by simp [lowBits_length L hw s])]
   simp [List.getElem_append,lowBits_length L hw s]

theorem source_carry (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<255) :
 carryAt (sourceA L s) (sourceB L s) (s L.sigma) (i+1)=aExpected L s i := by
 induction i with
 | zero =>
   rw [carryAt_next _ _ _ 0 (by rw [(sources_length L hw s).1];omega) (by rw [(sources_length L hw s).2];omega),sourceA_get L hw s 0 (by omega),sourceB_get L hw s 0 (by omega)]
   simp only [ite_true,show 0<255 by omega,aExpected,carryAt]
   cases s L.sigma <;> cases s (L.Y 0) <;> decide
 | succ i ih =>
   rw [carryAt_next _ _ _ (i+1) (by rw [(sources_length L hw s).1];omega) (by rw [(sources_length L hw s).2];omega),sourceA_get L hw s (i+1) (by omega),sourceB_get L hw s (i+1) (by omega),ih (by omega)]
   simp [aExpected,show ¬i+1=0 by omega,show i+1<255 by omega]

theorem raw_bit_sum (L : DecoderLayout) (hw : L.Widths) (s : BasisState)
 (carries : ∀i,i<255→s (L.A i)=aExpected L s i) (i : Nat) (hi : i<256) :
 parity (rawSources L i) s=sumBit ((sourceA L s).getD i false) ((sourceB L s).getD i false)
   (carryAt (sourceA L s) (sourceB L s) (s L.sigma) i) := by
 rw [sourceA_get L hw s i hi,sourceB_get L hw s i hi]
 by_cases z:i=0
 · subst i
   simp only [rawSources,ite_true,show 0<255 by omega,parity,List.foldr_cons,List.foldr_nil,carryAt,sumBit]
   cases s (L.Y 0) <;> cases s L.sigma <;> decide
 · obtain ⟨j,rfl⟩:∃j,i=j+1:=⟨i-1,by omega⟩
   rw [source_carry L hw s j (by omega)]
   simp only [rawSources,show ¬j+1=0 by omega,ite_false,Nat.add_sub_cancel]
   by_cases h:j+1<255
   · simp only [h,ite_true,parity,List.foldr_cons,List.foldr_nil,sumBit]
     rw [carries j (by omega)]
     cases s (L.Y j) <;> cases s (L.Y (j+1)) <;> cases s L.sigma <;> cases aExpected L s j <;> decide
   · have e:j=254:=by omega
     subst j
     simp only [show ¬254+1<255 by omega,ite_false,parity,List.foldr_cons,List.foldr_nil,sumBit]
     rw [carries 254 (by omega)]
     cases s (L.Y 254) <;> cases s L.sigma <;> cases aExpected L s 254 <;> decide

theorem rawBits_eq_sums (L : DecoderLayout) (hw : L.Widths) (s : BasisState)
 (carries : ∀i,i<255→s (L.A i)=aExpected L s i) :
 rawBits L s=sums (sourceA L s) (sourceB L s) (s L.sigma) := by
 have lens: (sourceA L s).length=(sourceB L s).length:=(sources_length L hw s).1.trans (sources_length L hw s).2.symm
 apply List.ext_getElem (by rw [sums_length _ _ _ lens];simp [rawBits,(sources_length L hw s).1])
 intro i hi hj
 have h:i<256:=by simpa [rawBits] using hi
 rw [←List.getD_eq_getElem _ false hi,←List.getD_eq_getElem _ false hj]
 rw [rawBits,bitVector_get _ _ _ h,sums_at _ _ _ _ lens (by rw [(sources_length L hw s).1];omega)]
 exact raw_bit_sum L hw s carries i h

theorem rawBits_value (L : DecoderLayout) (hw : L.Widths) (s : BasisState)
 (carries : ∀i,i<255→s (L.A i)=aExpected L s i) :
 value (rawBits L s)=(if s L.sigma then regValue (L.y.take 255) s else 3*regValue (L.y.take 255) s)%2^256 := by
 rw [rawBits_eq_sums L hw s carries,sums_value _ _ _ ((sources_length L hw s).1.trans (sources_length L hw s).2.symm),(sources_length L hw s).1]
 exact sources_value L hw s
theorem correction_literal (h b : Bool) :
 value (bitVector 256 (fun i=>if i=1 then b else if Nat.testBit (2^32+977) i then h else false))=
 h.toNat*(2^32+977)+2*b.toNat := by
 cases h <;> cases b <;> decide +kernel

theorem correctionBits_value (L : DecoderLayout) (s : BasisState) :
 value (correctionBits L s)=(s L.h).toNat*(2^32+977)+2*(s L.bias).toNat := by
 have eq : correctionBits L s=bitVector 256 (fun i=>if i=1 then s L.bias else if Nat.testBit (2^32+977) i then s L.h else false) := by
   unfold correctionBits
   congr 1
   funext i
   unfold correction
   split_ifs <;> simp [MappedBit.value]
 rw [eq,correction_literal]

theorem graph_of_register_values (L : DecoderLayout)
 (hw : L.Widths) (hn : L.wires.Nodup) (basis : BasisState)
 (carries : ∀i,i<255→basis (L.A i)=aExpected L basis i)
 (hv : regValue L.r basis=
 ((if basis L.sigma then regValue (L.y.take 255) basis else 3*regValue (L.y.take 255) basis)+
  2*(basis L.bias).toNat+(basis L.h).toNat*(2^32+977))%2^256) :
 BGraph L basis ∧ basis (L.R 0)=parity (bSources L 0) basis := by
 apply graph_of_bit_values
 rw [resultBits_value L hw,rawBits_value L hw basis carries,correctionBits_value]
 rw [hv,Nat.mod_add_mod]
 congr 1
 ring
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT GraphCore
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run addCarry eraseAddCarry bBlock aProgram eraseAProgram

def graphCore (L : DecoderLayout) : Program := aProgram L ++ (bBlock L ++ eraseAProgram L)

theorem graphCore_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean : ∀i,i<255 → s.basis (L.A i)=false)
 (graph : ∀m, BGraph L (run (aProgram L) m s).basis)
 (low : ∀m, let t:=run (aProgram L) m s
   t.basis (L.R 0)=parity (bSources L 0) t.basis) (m : List Bool) :
 (run (graphCore L) m s).phase=s.phase ∧
 (∀q,q∉L.carry → q∉L.r → (run (graphCore L) m s).basis q=s.basis q) ∧
 (∀i,i<255 → (run (graphCore L) m s).basis (L.A i)=false) ∧
 (∀i,i<256 → (run (graphCore L) m s).basis (L.R i)=false) := by
 have result:=run_three_states (aProgram L) (bBlock L) (eraseAProgram L)
   (fun a d => a=s → d.phase=s.phase ∧
    (∀q,q∉L.carry → q∉L.r → d.basis q=s.basis q) ∧
    (∀i,i<255 → d.basis (L.A i)=false) ∧
    (∀i,i<256 → d.basis (L.R i)=false)) (by
   intro a b c d m1 m2 m3 hab hbc hcd eq
   subst a
   have af:=aProgram_frame L hw hn s clean m1
   have g:=graph m1
   have l:=low m1
   rw [hab] at af g l
   have bc:=bBlock_correct L hw hn b g l m2
   have bf:=bBlock_addFrame L hw hn s b af g l m2
   rw [hbc] at bc bf
   have final:=eraseAProgram_frame L hw hn s c bf m3
   rw [hcd] at final
   have out (q : Wire) (hq:q∉L.carry) : d.basis q=c.basis q := by
     rw [←hcd]
     simpa only [eraseAProgram] using add_reverse_outside L hw hn s 255 (le_refl _) c bf m3 q hq
   refine ⟨final.phase,?_,fun i hi=>final.clean i (by omega) hi,?_⟩
   · intro q hc hr
     have first : b.basis q=s.basis q := by
       rw [←hab]
       simpa only [aProgram] using add_forward_outside L hw hn 255 (le_refl _) s m1 q hc
     exact (out q hc).trans ((bc.2.1 q hr).trans first)
   · intro i hi
     have away : L.R i∉L.carry := by
       intro ha
       exact source_r_away L hn _ (Or.inr (Or.inl ha)) (r_mem L hw i hi)
     exact (out (L.R i) away).trans (bc.2.2 i hi)) s m
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CleanedCore
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run graphCore biasErase clearQuotient

def CoreResult (L : DecoderLayout) (s t : State) : Prop :=
 t.phase=s.phase ∧ (∀q,q∉L.carry → q∉L.r → t.basis q=s.basis q) ∧
 (∀i,i<255 → t.basis (L.A i)=false) ∧ (∀i,i<256 → t.basis (L.R i)=false)

def cleanedCore (L : DecoderLayout) : Program :=graphCore L++(biasErase L++clearQuotient L)

theorem source_outside (L : DecoderLayout) (hn : L.wires.Nodup) (q : Wire)
 (hq : q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : q∉L.carry ∧ q∉L.r := by
 refine ⟨carry_source_away L hn q hq,?_⟩
 apply source_r_away L hn q
 rcases hq with h|h|h|h
 · exact Or.inl h
 · exact Or.inr (Or.inr (Or.inl h))
 · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
 · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem cleanedCore_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean : ∀i,i<255 → s.basis (L.A i)=false)
 (graph : ∀m, BGraph L (run (aProgram L) m s).basis)
 (low : ∀m, let t:=run (aProgram L) m s
   t.basis (L.R 0)=parity (bSources L 0) t.basis)
 (bias : s.basis L.bias=(s.basis (L.Y 255) && !s.basis L.sigma))
 (quotient : s.basis L.h=(!s.basis L.sigma &&
   !(decide (regValue (L.y.take 255) s.basis < ((p-1)/2)/3+(!s.basis (L.Y 255)).toNat))))
 (m : List Bool) :
 ∃t,CoreResult L s t ∧ run (cleanedCore L) m s=
   ⟨s.phase,writeBit (writeBit t.basis L.bias false) L.h false⟩ := by
 have result:=run_three_states (graphCore L) (biasErase L) (clearQuotient L)
   (fun a d=>a=s → ∃t,CoreResult L s t ∧ d=
     ⟨s.phase,writeBit (writeBit t.basis L.bias false) L.h false⟩) (by
   intro a t u v m1 m2 m3 hat htu huv eq
   subst a
   have tc:=graphCore_correct L hw hn s clean graph low m1
   rw [hat] at tc
   have stable (q : Wire) (hq:q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : t.basis q=s.basis q :=
     tc.2.1 q (source_outside L hn q hq).1 (source_outside L hn q hq).2
   have tsy:=stable (L.Y 255) (Or.inl (y_mem L hw 255 (by omega)))
   have ts:=stable L.sigma (by tauto)
   have th:=stable L.h (by tauto)
   have tb:=stable L.bias (by tauto)
   have bknown:t.basis L.bias=(t.basis (L.Y 255) && !t.basis L.sigma) := by rw[tb,tsy,ts];exact bias
   have ub:=biasErase_run L hw hn t m2 bknown
   rw[htu] at ub
   have baway:L.bias∉L.y:=flag_y_away L hn _ (by simp)
   have nd: [L.sigma,L.h,L.bias].Nodup := by
     apply List.nodup_iff_count.mpr
     intro q
     have h:=List.nodup_iff_count.mp hn q
     simp only[DecoderLayout.wires,List.count_append] at h
     omega
   have sh:L.sigma≠L.bias :=fun e=>(List.nodup_cons.mp nd).1 (by simp[e])
   have hb:L.h≠L.bias :=fun e=>(List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp[e])
   have yb:L.Y 255≠L.bias :=fun e=>baway (e ▸ y_mem L hw 255 (by omega))
   have uy:u.basis (L.Y 255)=s.basis (L.Y 255) :=by rw[ub];simpa[writeBit,yb] using tsy
   have us:u.basis L.sigma=s.basis L.sigma :=by rw[ub];simpa[writeBit,sh] using ts
   have uh:u.basis L.h=s.basis L.h :=by rw[ub];simpa[writeBit,hb] using th
   have uv:regValue (L.y.take 255) u.basis=regValue (L.y.take 255) s.basis := by
     apply regValue_congr
     intro q hq
     have qb:q≠L.bias:=fun e=>baway (e ▸ List.mem_of_mem_take hq)
     rw[ub]
     simpa[writeBit,qb] using stable q (Or.inl (List.mem_of_mem_take hq))
   have uq:u.basis L.h=(!u.basis L.sigma && !(decide (regValue (L.y.take 255) u.basis<((p-1)/2)/3+(!u.basis (L.Y 255)).toNat))) := by
     rw[uy,us,uh,uv];exact quotient
   have uc:∀q∈L.carry,u.basis q=false := by
     intro q hq
     obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
     have i255:i<255:=by have len:=hw.2.2;omega
     have aeq:L.A i=q:=by
       change L.carry.getD i 0=q
       rw[List.getD_eq_getElem _ _ hi]
       exact eq
     have qb:q≠L.bias:=fun e=>carry_source_away L hn _ (by tauto) (e ▸ hq)
     rw[ub]
     simpa only[writeBit,Function.update_of_ne qb,←aeq] using tc.2.2.1 i i255
   have vc:=clearQuotient_correct L hw hn u m3 uc uq
   rw[huv] at vc
   refine ⟨t,tc,?_⟩
   rw[vc,ub]
   simp only[tc.1]) s m
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT PostAGraph
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run aProgram

theorem aExpected_congr (L : DecoderLayout) (a b : BasisState)
 (sigma : a L.sigma=b L.sigma) (ys : ∀i,i<256→a (L.Y i)=b (L.Y i))
 (i : Nat) (hi:i<255) : aExpected L a i=aExpected L b i := by
 induction i with
 |zero=>simp only[aExpected];rw[sigma,ys 0 (by omega)]
 |succ i ih=>simp only[aExpected];rw[ys i (by omega),ys (i+1) (by omega),sigma,ih (by omega)]

theorem aProgram_graph (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean:∀i,i<255→s.basis (L.A i)=false)
 (hv : regValue L.r s.basis=
 ((if s.basis L.sigma then regValue (L.y.take 255) s.basis else 3*regValue (L.y.take 255) s.basis)+
  2*(s.basis L.bias).toNat+(s.basis L.h).toNat*(2^32+977))%2^256) (m : List Bool) :
 BGraph L (run (aProgram L) m s).basis ∧
 (run (aProgram L) m s).basis (L.R 0)=parity (bSources L 0) (run (aProgram L) m s).basis := by
 let t:=run (aProgram L) m s
 have af:=aProgram_frame L hw hn s clean m
 have out (q : Wire) (hq:q∉L.carry) : t.basis q=s.basis q :=by
   simpa only[t,aProgram] using add_forward_outside L hw hn 255 (le_refl _) s m q hq
 have stable (q : Wire) (hq:q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : t.basis q=s.basis q :=
   out q (carry_source_away L hn q hq)
 apply graph_of_register_values L hw hn t.basis
 · intro i hi
   exact (af.computed i hi).trans (aExpected_congr L s.basis t.basis af.sigma.symm
     (fun j hj=>(af.source j hj).symm) i hi)
 · have rv:regValue L.r t.basis=regValue L.r s.basis :=by
     apply regValue_congr
     intro q hq
     apply out
     intro hc
     exact source_r_away L hn q (Or.inr (Or.inl hc)) hq
   have yv:regValue (L.y.take 255) t.basis=regValue (L.y.take 255) s.basis :=by
     apply regValue_congr
     intro q hq
     exact stable q (Or.inl (List.mem_of_mem_take hq))
   rw[rv,yv,stable L.sigma (by tauto),stable L.h (by tauto),stable L.bias (by tauto)]
   exact hv
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Back
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run restoreSource copySource

theorem index_zero_mem (xs : List Wire) (b : BasisState)
 (zero:∀i,i<xs.length→b (xs.getD i 0)=false) (q : Wire) (hq:q∈xs) : b q=false := by
 obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
 have get:xs.getD i 0=q := by rw[List.getD_eq_getElem _ _ hi];exact eq
 rw[←get]
 exact zero i hi

def zeroR (L : DecoderLayout) (b : BasisState) : BasisState :=
 fun q=>if q∈L.r then false else complementBasis (L.Y 255) (L.y.take 255) b q

theorem cleaned_front_basis (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (phase : Bool) (t : State)
 (f : CoreResult L ⟨phase,frontBasis L b⟩ t)
 (ch:b L.h=false) (cb:b L.bias=false) (cc:∀q∈L.carry,b q=false) :
 writeBit (writeBit t.basis L.bias false) L.h false=zeroR L b := by
 have nd:=flags_nd L hn
 have hb:L.h≠L.bias:=fun e=>(List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp[e])
 have hy:=flag_y_away L hn L.h (by simp)
 have byy:=flag_y_away L hn L.bias (by simp)
 have hr:=source_r_away L hn L.h (by tauto)
 have br:=source_r_away L hn L.bias (by tauto)
 have tr:∀q∈L.r,t.basis q=false := index_zero_mem L.r t.basis (by intro i hi;exact f.2.2.2 i (by have len:=hw.2.1;omega))
 have tc:∀q∈L.carry,t.basis q=false :=index_zero_mem L.carry t.basis (by intro i hi;exact f.2.2.1 i (by have len:=hw.2.2;omega))
 funext q
 by_cases qh:q=L.h
 · subst q
   simp[writeBit,zeroR,hr,complementBasis,show L.h∉L.y.take 255 from fun h=>hy (List.mem_of_mem_take h),ch]
 · by_cases qb:q=L.bias
   · subst q
     simp[writeBit,Ne.symm hb,zeroR,br,complementBasis,show L.bias∉L.y.take 255 from fun h=>byy (List.mem_of_mem_take h),cb]
   · simp only[writeBit,Function.update_of_ne qh,Function.update_of_ne qb]
     by_cases qr:q∈L.r
     · simp[zeroR,qr,tr q qr]
     · by_cases qc:q∈L.carry
       · have qy:q∉L.y:=fun h=>carry_source_away L hn q (Or.inl h) qc
         simp[zeroR,qr,tc q qc,complementBasis,show q∉L.y.take 255 from fun h=>qy (List.mem_of_mem_take h),cc q qc]
       · rw[f.2.1 q qc qr]
         simp[frontBasis,writeBit,qh,qb,zeroR,qr,complementBasis]

theorem restore_zeroR (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (phase : Bool) (m : List Bool) :
 run (restoreSource L) m ⟨phase,zeroR L b⟩=
  ⟨phase,fun q=>if q∈L.r then false else b q⟩ := by
 rw[restoreSource_run L hw hn]
 have nd:=normalize_nd L hw hn
 have sig:zeroR L b (L.Y 255)=b (L.Y 255):=by
   simp[zeroR,complementBasis,show L.Y 255∉L.y.take 255 from fun h=>nd.2 (List.mem_append_left _ h),
     show L.Y 255∉L.r from fun h=>nd.2 (List.mem_append_right _ h)]
 apply congrArg (State.mk phase)
 funext q
 simp only[complementBasis,sig]
 by_cases qr:q∈L.r
 · have qt:q∉L.y.take 255 := by
     intro h
     exact source_r_away L hn q (Or.inl (List.mem_of_mem_take h)) qr
   simp[qr,qt,zeroR]
 · by_cases qt:q∈L.y.take 255
   · simp[zeroR,complementBasis,qr,qt,Bool.xor_assoc]
   · simp[zeroR,complementBasis,qr,qt]

def back (L : DecoderLayout) : Program :=restoreSource L++copySource L

theorem back_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (phase : Bool) (m : List Bool) :
 (run (back L) m ⟨phase,zeroR L b⟩).phase=phase ∧
 (∀q,q∉L.r → (run (back L) m ⟨phase,zeroR L b⟩).basis q=b q) ∧
 regValue L.r (run (back L) m ⟨phase,zeroR L b⟩).basis=regValue L.y b := by
 rw[back,run_append,run_take,restore_zeroR L hw hn]
 let v : State:=⟨phase,fun q=>if q∈L.r then false else b q⟩
 have c:=copySource_correct L hw hn v (m.drop (measurementCount (restoreSource L)))
 refine ⟨c.1,?_,?_⟩
 · intro q hq
   simpa only[v,if_neg hq] using c.2.1 q hq
 · rw[c.2.2]
   have rz:regValue L.r v.basis=0 :=(regValue_zero _ _).mpr (by intro q hq;simp[v,hq])
   have yv:regValue L.y v.basis=regValue L.y b :=by
     apply regValue_congr
     intro q hq
     have qr:q∉L.r:=source_r_away L hn q (Or.inl hq)
     simp[v,qr]
   rw[rz,yv,Nat.zero_xor]
end ECDSAAdd.Entrant.TerminalGraph



-- TERMINAL GRAPH COMPONENT DecoderCorrect
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic Secp256k1 Arithmetic.BalancedField
attribute [local irreducible] run front cleanedCore back aProgram

theorem decoder_parts (L : DecoderLayout) : decoder L=front L++(cleanedCore L++back L) := by
 simp only[decoder,front,cleanedCore,graphCore,aProgram,eraseAProgram,bBlock,bSources,back,List.append_assoc]

theorem decoder_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (Y : Fp) (sigma : Bool) (s : State) (m : List Bool)
 (ys:regValue L.y s.basis=centerWord Y)
 (rs:regValue L.r s.basis=centerWord ((if sigma then 1 else 3)*Y))
 (sig:s.basis L.sigma=sigma) (hc:s.basis L.h=false) (bc:s.basis L.bias=false)
 (cc:∀q∈L.carry,s.basis q=false) :
 (run (decoder L) m s).phase=s.phase ∧
 (∀q,q∉L.r → (run (decoder L) m s).basis q=s.basis q) ∧
 regValue L.r (run (decoder L) m s).basis=centerWord Y := by
 have result:=run_three_states (front L) (cleanedCore L) (back L)
   (fun a d=>a=s → d.phase=s.phase ∧ (∀q,q∉L.r → d.basis q=s.basis q) ∧
     regValue L.r d.basis=centerWord Y) (by
   intro a n u d m1 m2 m3 han hnu hud eq
   subst a
   have nf:=front_run L hw hn s m1
   rw[han] at nf
   let f : State:=⟨s.phase,frontBasis L s.basis⟩
   have neq:n=f:=nf
   subst n
   rw[nf] at hnu
   have scalar:=actual_front_scalar L hw hn s.basis Y sigma ys rs sig hc bc
   have nc:∀i,i<255→f.basis (L.A i)=false :=by
     intro i hi
     exact front_carry_clean L hn s.basis cc (L.A i) (a_mem L hw i hi)
   have bb:f.basis L.bias=(f.basis (L.Y 255) && !f.basis L.sigma) :=by
     have facts:=actual_front_values L hw hn s.basis Y sigma ys rs sig hc bc
     change frontBasis L s.basis L.bias=(frontBasis L s.basis (L.Y 255) && !frontBasis L s.basis L.sigma)
     rw[facts.2.2.2.1,facts.2.2.2.2.1,facts.2.2.2.2.2]
   have cg:=cleanedCore_correct L hw hn f nc
     (fun r=>(aProgram_graph L hw hn f nc scalar.1 r).1)
     (fun r=>(aProgram_graph L hw hn f nc scalar.1 r).2) bb scalar.2 m2
   obtain ⟨t,tf,ut⟩:=cg
   rw[hnu] at ut
   have cleanbasis:=cleaned_front_basis L hw hn s.basis s.phase t tf hc bc cc
   have uz:u=⟨s.phase,zeroR L s.basis⟩ :=by
     rw[ut,cleanbasis]
   have done:=back_correct L hw hn s.basis s.phase m3
   rw[uz] at hud
   rw[hud] at done
   exact ⟨done.1,done.2.1,done.2.2.trans ys⟩) s m
 rw[decoder_parts]
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Caller
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic Secp256k1 Arithmetic.BalancedField
attribute [local irreducible] run decoder

def work (L : DecoderLayout) : List Wire:=L.carry++[L.h,L.bias]

theorem work_away (L : DecoderLayout) (hn : L.wires.Nodup) (q : Wire) (hq:q∈work L) :
 q∉L.r ∧ q∉L.y := by
 simp only[work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with hc|rfl|rfl
 · refine ⟨source_r_away L hn q (Or.inr (Or.inl hc)),?_⟩
   intro hy
   exact carry_source_away L hn q (Or.inl hy) hc
 · exact ⟨source_r_away L hn _ (by tauto),flag_y_away L hn _ (by simp)⟩
 · exact ⟨source_r_away L hn _ (by tauto),flag_y_away L hn _ (by simp)⟩

theorem terminal_relation (X Y : Fp) (sigma : Bool)
 (h:(X+(if sigma then Y else -Y))/2=Y) : X=(if sigma then 1 else 3)*Y := by
 have two:(2:Fp)≠0:=by decide
 have e: X+(if sigma then Y else -Y)=Y*2 := (div_eq_iff two).mp h
 cases sigma <;> simp only[Bool.false_eq_true,if_false,if_true] at e ⊢ <;> linear_combination e

theorem decoder_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : BasisState) (clean : ∀q∈work L,origin q=false) (X Y : Fp)
 (hend:(X+(if origin L.sigma then Y else -Y))/2=Y) :
 Triple (PairFrame L.r L.y origin (centerWord X) (centerWord Y)) (decoder L)
   (PairFrame L.r L.y origin (centerWord Y) (centerWord Y)) := by
 intro s m input
 have cleanS (q : Wire) (hq:q∈work L) : s.basis q=false :=
   (input.2.2 q (work_away L hn q hq).1 (work_away L hn q hq).2).trans (clean q hq)
 have sig:s.basis L.sigma=origin L.sigma:=input.2.2 L.sigma
   (source_r_away L hn _ (by tauto)) (flag_y_away L hn _ (by simp))
 have rel:=terminal_relation X Y (origin L.sigma) hend
 have rword:regValue L.r s.basis=centerWord ((if origin L.sigma then 1 else 3)*Y) := by
   rw[input.1,rel]
 have c:=decoder_correct L hw hn Y (origin L.sigma) s m input.2.1 rword sig
   (cleanS L.h (by simp[work])) (cleanS L.bias (by simp[work]))
   (fun q hq=>cleanS q (by simp[work,hq]))
 refine ⟨c.1,c.2.2,?_,?_⟩
 · exact (regValue_congr L.y _ _ (fun q hq=>c.2.1 q (source_r_away L hn q (Or.inl hq)))).trans input.2.1
 · intro q qr qy
   exact (c.2.1 q qr).trans (input.2.2 q qr qy)
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT EndpointCaller
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphEndpoint
open Arithmetic Secp256k1 BalancedField TerminalGraph
attribute [local irreducible] run TerminalGraph.decoder

def half (divide : Bool) (w : Nat→Wire) (sign : Wire) : Program :=
 if divide then decoder (ofBalanced (Q6EndpointCell.ports w sign)) else Q6EndpointCell.half false w sign

def endpoint (divide : Bool) (w : Nat→Wire) (b g sign : Wire) (ig : Bool) : Program :=
 transcriptSelectWindow b g sign ig (half divide w sign)

theorem clean_decoder (w : Nat→Wire) (sign : Wire) (origin : BasisState)
 (hc:Q6EndpointCell.Clean w origin) :
 ∀q∈work (ofBalanced (Q6EndpointCell.ports w sign)),origin q=false := by
 have cl:=Q6EndpointCell.clean_work w sign origin hc
 intro q hq
 apply cl
 simp only[work,ofBalanced,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
 simp only[BalancedCircuit.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
 rcases hq with (h|rfl)|rfl|rfl
 · exact Or.inr (List.mem_of_mem_take h)
 all_goals tauto

theorem half_frame (divide : Bool) (w : Nat→Wire) (sign : Wire)
 (hn:(Q6EndpointCell.ports w sign).wires.Nodup) (origin : BasisState)
 (hc:Q6EndpointCell.Clean w origin) (X Y : Fp)
 (hend:divide=true→(X+(if origin sign then Y else -Y))/2=Y) :
 Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin (centerWord X) (centerWord Y))
   (half divide w sign)
   (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
     (centerWord (if divide then (X+(if origin sign then Y else -Y))/2 else 2*X+(if origin sign then -Y else Y)))
     (centerWord Y)) := by
 cases divide
 · exact Q6EndpointCell.half_frame false w sign hn origin hc X Y
 · have c:=decoder_frame (ofBalanced (Q6EndpointCell.ports w sign))
     (ofBalanced_widths _ (Q6EndpointCell.ports_widths w sign)) (ofBalanced_nodup _ hn)
     origin (clean_decoder w sign origin hc) X Y (by simpa only[ofBalanced,Q6EndpointCell.ports_sign] using hend rfl)
   simpa only[half,ofBalanced,if_true,hend rfl] using c

theorem endpoint_frame (divide : Bool) (w : Nat → Wire) (b g sign : Wire) (ig : Bool)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup) (nd : [b,g,sign].Nodup)
    (hb : b∉(Q6EndpointCell.ports w sign).r ∧ b∉(Q6EndpointCell.ports w sign).y)
    (hg : g∉(Q6EndpointCell.ports w sign).r ∧ g∉(Q6EndpointCell.ports w sign).y)
    (hs : sign∉(Q6EndpointCell.ports w sign).r ∧ sign∉(Q6EndpointCell.ports w sign).y)
    (origin : BasisState) (hz : origin sign=false) (hc : Q6EndpointCell.Clean w origin) (X Y : Fp)
    (hend : divide=true → (X+(if mixedTranscriptBit origin b g ig then Y else -Y))/2=Y) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
      (centerWord X) (centerWord Y)) (endpoint divide w b g sign ig)
      (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (centerWord (if divide then (X+(if mixedTranscriptBit origin b g ig then Y else -Y))/2
          else 2*X+(if mixedTranscriptBit origin b g ig then -Y else Y))) (centerWord Y)) := by
 have ns:=OwnQ6Core5.sign_work (Q6EndpointCell.ports w sign) hn
 have cl:Q6EndpointCell.Clean w (mixedTranscriptBase origin b g sign ig) :=by
   intro q hq
   have nq:q≠sign:=fun e=>ns (by simpa only[Q6EndpointCell.ports_work] using e ▸ hq)
   simpa only[mixedTranscriptBase,writeBit,Function.update_of_ne nq] using hc q hq
 have body:=half_frame divide w sign hn (mixedTranscriptBase origin b g sign ig) cl X Y
   (by simpa only[mixedTranscriptBase,writeBit,Function.update_self] using hend)
 simp only[mixedTranscriptBase,writeBit,Function.update_self] at body
 exact transcriptSelectWindow_pairFrame b g sign ig _ _ nd hb hg hs origin hz _ _ _ _ _ body

theorem half_counts (divide : Bool) (w : Nat→Wire) (sign : Wire) :
 toffoliCount (half divide w sign)=(if divide then 512 else 1020) ∧
 measurementCount (half divide w sign)=(if divide then 766 else 1021) := by
 cases divide
 · exact Q6EndpointCell.half_counts false w sign
 · exact decoder_counts _ (ofBalanced_widths _ (Q6EndpointCell.ports_widths w sign))
end ECDSAAdd.Entrant.TerminalGraphEndpoint


-- TERMINAL GRAPH COMPONENT TerminalSupportOnly
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphSupportOnly
open Arithmetic MappedCompressed TerminalGraph

def actualLayout (sign : Nat) : DecoderLayout :=
  ofBalanced (Q6EndpointCell.ports base (base sign))
def actualDecoder (sign : Nat) : Program := decoder (actualLayout sign)

private abbrev footprint (s q : Nat) : Prop :=
 q=base s ∨ q=base 1027 ∨ q=base 768 ∨ q=base 1797 ∨ q=base 1540 ∨
 (base 770≤q ∧ q<base 1026) ∨ (base 2056≤q ∧ q<base 2312) ∨
 (base 512≤q ∧ q<base 765)

private theorem block_mem (q start n : Nat) :
 q∈wireBlock base start n ↔ base start≤q ∧ q<base (start+n) := by
 simp only [wireBlock,List.mem_map,List.mem_range'_1]
 constructor
 · rintro ⟨a,⟨ha,hb⟩,he⟩
   change a+16=q at he
   constructor
   · change start+16≤q
     rw [←he]
     exact Nat.add_le_add_right ha 16
   · change q<start+n+16
     rw [←he]
     exact Nat.add_lt_add_right hb 16
 · rintro ⟨hlo,hhi⟩
   change start+16≤q at hlo
   change q<start+n+16 at hhi
   have hq : 16≤q := le_trans (Nat.le_add_left 16 start) hlo
   have eq : q-16+16=q := Nat.sub_add_cancel hq
   refine ⟨q-16,⟨?_,?_⟩,?_⟩
   · have hh : start+16≤q-16+16 := by rw [eq]; exact hlo
     exact (show start+16≤q-16+16 ↔ start≤q-16 from Nat.add_le_add_iff_right).mp hh
   · have hh : q-16+16<start+n+16 := by rw [eq]; exact hhi
     exact (show q-16+16<start+n+16 ↔ q-16<start+n from Nat.add_lt_add_iff_right).mp hh
   · exact eq

private theorem actual_carry (s : Nat) :
 (actualLayout s).carry=wireBlock base 512 253++[base 1540,base 1797] := by
 simp only [actualLayout,ofBalanced,Q6EndpointCell.ports,List.take_append,
   show (wireBlock base 512 253).length=253 from by simp [wireBlock],
   show (wireBlock base 512 253).take 254=wireBlock base 512 253 from
     List.take_of_length_le (by simp [wireBlock]),Nat.reduceSub,List.take_succ_cons,
   List.take_zero,List.nil_append,List.append_assoc,List.singleton_append]

private theorem actual_y (s : Nat) :
 (actualLayout s).y=wireBlock base 770 256 := by rfl
private theorem actual_r (s : Nat) :
 (actualLayout s).r=wireBlock base 2056 256 := by rfl

private theorem actual_sites (s q : Nat) :
 q∈(actualLayout s).wires.toFinset ↔ footprint s q := by
 simp only [List.mem_toFinset,DecoderLayout.wires,List.mem_append,
   List.mem_cons,List.not_mem_nil,or_false,actual_carry,actual_y,actual_r,block_mem]
 simp only [actualLayout,ofBalanced,Q6EndpointCell.ports,footprint]
 tauto

private def correctionCheck (s : Nat) : List Correction→Bool
 | []=>true
 | .Z t::cs=>decide (footprint s t) && correctionCheck s cs
 | .CZ a b::cs=>decide (footprint s a) && decide (footprint s b) && correctionCheck s cs

private theorem correctionCheck_iff (s : Nat) (cs : List Correction) :
 correctionCheck s cs=true ↔ correctionWires cs⊆(actualLayout s).wires.toFinset := by
 induction cs with
 | nil=>simp [correctionCheck,correctionWires]
 | cons c cs ih=>
   cases c <;>
     simp only [correctionCheck,correctionWires,Bool.and_eq_true,decide_eq_true_eq,
       Finset.union_subset_iff,Finset.singleton_subset_iff,Finset.insert_subset_iff,
       Finset.empty_subset,and_true,ih,actual_sites]

private def instructionCheck (s : Nat) : Instr→Bool
 | .X t=>decide (footprint s t)
 | .CX a t=>decide (footprint s a) && decide (footprint s t)
 | .CCX a b t=>decide (footprint s a) && decide (footprint s b) && decide (footprint s t)
 | .measureX t c d=>decide (footprint s t) && correctionCheck s c && correctionCheck s d

private theorem instructionCheck_iff (s : Nat) (i : Instr) :
 instructionCheck s i=true ↔ i.wires⊆(actualLayout s).wires.toFinset := by
 cases i <;>
   simp only [instructionCheck,Instr.wires,Bool.and_eq_true,decide_eq_true_eq,
     Finset.union_subset_iff,Finset.singleton_subset_iff,Finset.insert_subset_iff,
     Finset.empty_subset,and_true,actual_sites,correctionCheck_iff,and_assoc]

private def supportCheck (s : Nat) (P : Program) : Bool := P.all (instructionCheck s)
private theorem supportCheck_correct (s : Nat) (P : Program)
 (h : supportCheck s P=true) : wires P⊆(actualLayout s).wires.toFinset := by
 induction P with
 | nil=>simp [wires]
 | cons i P ih=>
   have hh : instructionCheck s i=true ∧ supportCheck s P=true := by
     simpa only [supportCheck,List.all_cons,Bool.and_eq_true] using h
   simp only [wires,Finset.union_subset_iff]
   exact ⟨(instructionCheck_iff s i).mp hh.1,ih hh.2⟩

theorem actual_decoder_support :
    wires (actualDecoder 2409)⊆(ofBalanced (Q6EndpointCell.ports base (base 2409))).wires.toFinset ∧
    wires (actualDecoder 2410)⊆(ofBalanced (Q6EndpointCell.ports base (base 2410))).wires.toFinset := by
  constructor <;> apply supportCheck_correct <;> decide +kernel

end ECDSAAdd.Entrant.TerminalGraphSupportOnly


-- TERMINAL GRAPH COMPONENT TerminalFootprint
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic MappedCompressed
attribute [local irreducible] wires CoherentTail.addPrefix Q6Structural.rawAdd Q6EndpointStructural.forwardE Q6EndpointCell.halfE
theorem prefix_sites (x y c : List Wire) (a t z cin : Wire)
 (hy:y.length=x.length) (hc:c.length=x.length) :
 wires (CoherentTail.addPrefix x y c a t z cin)=(x++y++c++[a,t,z,cin]).toFinset := by
 induction x generalizing y c cin with
 | nil=>
   have ey:y=[]:=List.eq_nil_of_length_eq_zero hy
   have ec:c=[]:=List.eq_nil_of_length_eq_zero hc
   subst y; subst c
   ext q
   simp [CoherentTail.addPrefix,CoherentTail.program,wires,Instr.wires]
   tauto
 | cons b xs ih=>
   cases y with
   | nil=>simp at hy
   | cons d ys=>
     cases c with
     | nil=>simp at hc
     | cons k ks=>
       have hy':ys.length=xs.length:=by simpa using hy
       have hc':ks.length=xs.length:=by simpa using hc
       rw [CoherentTail.addPrefix,wires_append,wires_append,wires_append,ih _ _ _ hy' hc']
       ext q
       simp [majority,eraseCarry,wires,Instr.wires,correctionWires]
       tauto

theorem layout_subset_forwardE (L : BalancedCircuit.Layout) (hw : L.Widths) :
 (ofBalanced L).wires.toFinset⊆wires (Q6EndpointStructural.forwardE L) := by
 have len:=hw.2.2
 have yw:=hw.2.1
 have rw:=hw.1
 have ct:(Q6Structural.carryLayout L).carry.take 255=L.carry.take 254++[L.lower] := by
   simp [Q6Structural.carryLayout,Q6Structural.q6Carry,List.take_append,List.length_take,len]
 have plen:((Q6Structural.carryLayout L).carry.take 255).length=L.ylow.length :=by
   rw[ct]
   simp[yw,len]
 have ylen:L.low.length=L.ylow.length:=by simp[BalancedCleanup.Layout.low,rw,yw]
 have pref:=prefix_sites L.ylow L.low ((Q6Structural.carryLayout L).carry.take 255)
   L.ymsb L.rmsb L.one L.sign ylen plen
 have rawsub:wires (CoherentTail.addPrefix L.ylow L.low ((Q6Structural.carryLayout L).carry.take 255)
   L.ymsb L.rmsb L.one L.sign)⊆wires (Q6Structural.rawAdd L) :=by
   simp only[Q6Structural.rawAdd,FifthCarry.rawAdd,Q6Structural.carryLayout,FieldRename.mapCircuit] at *
   intro q hq
   simp only[wires_append]
   exact Finset.mem_union_left _ (Finset.mem_union_right _ hq)
 have allsub:wires (GuardCompression.seed L)∪wires (Q6Structural.rawAdd L)⊆wires (Q6EndpointStructural.forwardE L) :=by
   intro q hq
   simp only[Q6EndpointStructural.forwardE,Q6StructuralCell.forwardPrefix,wires_append,Finset.mem_union] at hq ⊢
   tauto
 intro q hq
 apply allsub
 by_cases parity:q=L.parity
 · subst q
   exact Finset.mem_union_left _ (by simp[GuardCompression.seed,wires,Instr.wires])
 · apply Finset.mem_union_right
   apply rawsub
   rw[pref,ct]
   simp only[DecoderLayout.wires,ofBalanced,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
     BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low] at hq ⊢
   tauto

theorem actual_layout_subset_halfE :
 (ofBalanced (Q6EndpointCell.ports base (base 2409))).wires.toFinset⊆
 wires (Q6EndpointCell.halfE true base (base 2409)) := by
 have core:=layout_subset_forwardE (Q6EndpointCell.ports base (base 2409)) (Q6EndpointCell.ports_widths _ _)
 intro q hq
 have h:=core hq
 rw[Q6EndpointCell.halfE_true,wires_append,wires_append]
 exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
end ECDSAAdd.Entrant.TerminalGraph



-- TERMINAL GRAPH COMPONENT TerminalPhysicalOnly
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.TerminalGraphPhysicalOnly
open Arithmetic MappedCompressed

def actualDecoder (sign : Nat) : Program :=
 TerminalGraph.decoder (TerminalGraph.ofBalanced (Q6EndpointCell.ports base (base sign)))
attribute [local irreducible] GatePhysical actualDecoder TerminalGraph.decoder

theorem physical : GatePhysical (actualDecoder 2409) :=
 physicalGateCheck_correct _ (by decide +kernel)

theorem slots : Challenge.gateSlots (actualDecoder 2409)≤23900 := by
 decide +kernel
end ECDSAAdd.Entrant.TerminalGraphPhysicalOnly
end

-- ===== merged module ECDSAAdd.Submission.Entrant.JointInverse1588 =====
section
set_option Elab.async false

/-! Measured joint inverse of the S2 (multiplication) first packet, placed in the 1,588-qubit
Rolling layout.

Ported from submission f2dcda16 (ArthurOstapenko): `CleanInverse5` and `FirstInverse5` below are
that submission's generic measured inverse of the forward joint entry `EntryRetained5.program`
(which is already in the record).  The record's layout has two fewer clean wires than f2's at this
point (virtual carries `516` and `1541` have no host: `516` was hosted on G1 by the record's
`loanWindow`, but the joint inverse needs G1 as a control and the flag `2409` as its `sign`
scalar), so `JointInverse1588` hosts them inside the kernel:
* during `clearParity` on the still-clean scalars `one` and `sign`;
* during the inner adder (source bits 4..255) of the subtraction on `lowY` (u = J∧G) and
  `sign` (e = lower∧u), which are measured away before and recomputed after (+2 Toffolis).

Retiring virtual `760` (carry #248, pool wire 760) for the 1,587-qubit layout:
* during the parity carry chain of `clearParity` carry #248 sits on `rmsb`, which `prepareMagnitude`
  has just cleared (`lower := rmsb`, then the word is complemented under `lower`) and the chain never
  reads (`clearParityH`, a pure rename);
* during the inner adder carry #248 sits on carry #1 (`maj(one⊕sign, r1, c0)`), which is measured away
  before `loanW`'s two measurements (while `sign` is still present) and recomputed after its two
  Toffolis (`loanC`, +1 Toffoli, +1 record; the padding drops one erasure so the record length is kept). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CleanInverse5
open Arithmetic
attribute [local irreducible] run

def undo : Instr → Program
  | .CCX a b t => [.measureX t [] [.CZ a b]]
  | .X t => [.X t]
  | .CX a t => [.CX a t]
  | .measureX _ _ _ => []

def inverse : Program → Program
  | [] => []
  | i::p => inverse p ++ undo i

def CleanTarget (i : Instr) (s : State) : Prop :=
  match i with | .CCX _ _ t => s.basis t=false | _ => True

def Ready : Program → State → Prop
  | [],_ => True
  | i::p,s => ProperGate i ∧
      CleanTarget i s ∧
      Ready p (run [i] [] s)

theorem ready_proper (p : Program) (s : State) (h : Ready p s) : ProperProgram p := by
  induction p generalizing s with
  | nil => simp [ProperProgram]
  | cons i p ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl|hj
    · exact h.1
    · exact ih _ h.2.2 _ hj

theorem ready_append (p q : Program) (s : State) :
    Ready (p++q) s ↔ Ready p s ∧ Ready q (run p [] s) := by
  induction p generalizing s with
  | nil => simp [Ready,run]
  | cons i p ih =>
    cases i <;> simp only [List.cons_append,Ready,CleanTarget] <;>
      simp only [ih,run] <;> tauto

theorem undo_gate (i : Instr) (s : State) (m : List Bool)
    (hp : ProperGate i)
    (hc : CleanTarget i s) :
    run (undo i) m (run [i] [] s)=s := by
  cases i with
  | X t => exact properGate_involution (.X t) hp s [] m
  | CX a t => exact properGate_involution (.CX a t) hp s [] m
  | measureX t c0 c1 => contradiction
  | CCX a b t =>
    have ha : a≠t := hp.1
    have hb : b≠t := hp.2
    have erase := EntryHalf5.eraseAnd a b t ha hb (run [.CCX a b t] [] s) m (by
      simp [run,writeBit,CleanTarget] at hc ⊢
      simp [hc,ha,hb])
    change run [.measureX t [] [.CZ a b]] m (run [.CCX a b t] [] s)=s
    rw [erase]
    apply State.extensionality
    · simp only [run]
    · funext q
      by_cases hq : q=t
      · subst q;simp [writeBit,CleanTarget] at hc ⊢
        exact hc
      · simp [run,writeBit,hq]

theorem inverse_run (p : Program) (s : State) (h : Ready p s) (m : List Bool) :
    run (inverse p) m (run p [] s)=s := by
  induction p generalizing s m with
  | nil => simp [inverse,run]
  | cons i p ih =>
    have hp : ProperProgram p := ready_proper p _ h.2.2
    have pm := properProgram_measurementCount p hp
    have first : run (i::p) [] s=run p [] (run [i] [] s) := by
      cases i <;> simp_all [run,ProperGate,CleanTarget]
    rw [inverse,first,run_append,run_take,ih _ h.2.2]
    exact undo_gate i s _ h.1 h.2.1

theorem counts (p : Program) (hp : ProperProgram p) :
    toffoliCount (inverse p)=0 ∧ measurementCount (inverse p)=toffoliCount p := by
  induction p with
  | nil => exact ⟨rfl,rfl⟩
  | cons i p ih =>
    have h := hp i (by simp)
    have t := ih (fun j hj => hp j (by simp [hj]))
    cases i <;> simp_all [ProperGate,inverse,undo,toffoliCount_append,measurementCount_append,
      toffoliCount,measurementCount,Nat.add_comm]

theorem ready_zero (p : Program) (hp : ProperProgram p) (ht : toffoliCount p=0) (s : State) :
    Ready p s := by
  induction p generalizing s with
  | nil => trivial
  | cons i p ih =>
    have hi := hp i (by simp)
    have tail : ProperProgram p := fun j hj => hp j (by simp [hj])
    cases i with
    | measureX t c0 c1 => contradiction
    | CCX a b t => simp [toffoliCount] at ht
    | X t =>
      refine ⟨hi,trivial,ih tail ?_ _⟩
      simpa [toffoliCount] using ht
    | CX a t =>
      refine ⟨hi,trivial,ih tail ?_ _⟩
      simpa [toffoliCount] using ht

theorem copy_ready (j : Wire) (xs ys : List Wire) (s : State)
    (hn : (j::xs++ys).Nodup) (clean : ∀q∈ys,s.basis q=false) :
    Ready (copyRegister (some j) xs ys) s := by
  induction xs generalizing ys s with
  | nil => trivial
  | cons x xs ih =>
    cases ys with
    | nil => trivial
    | cons y ys =>
      have ct := List.nodup_iff_count.mp hn
      have nj : j≠y := by
        intro bad;have h:=ct y;subst j
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have nx : x≠y := by
        intro bad;have h:=ct y;subst x
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have nd : (j::xs++ys).Nodup := by
        apply List.nodup_iff_count.mpr
        intro q;have h:=ct q
        simp only [List.count_cons,List.count_append] at h ⊢
        omega
      have yt : y∉ys := by
        intro bad
        have h:=ct y;have pos:=List.count_pos_iff.mpr bad
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      change ProperGate (.CCX j x y) ∧ s.basis y=false ∧ _
      refine ⟨⟨nj,nx⟩,clean y (by simp),ih ys _ nd ?_⟩
      intro q hq
      simpa only [copyGate,run,writeBit,Function.update_of_ne (show q≠y from fun e=>yt (e ▸ hq))]
        using clean q (by simp [hq])

end ECDSAAdd.Entrant.CleanInverse5

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5
attribute [local irreducible] run

def restoreScalars (p a d e u j b h : Wire) : Program :=
  [.measureX u [] [.CZ j p], .CCX j b u,
   .CCX p u d, .CX p a, .CCX p h a, .CX d a, .CCX a u e]

def restoreAt (L : Layout) (J B : Wire) : Program :=
  restoreScalars L.parity L.lower L.one L.sign (lowY L) J B L.rmsb

def subtract (L : Layout) : Program :=
  notRegister L.r ++ Affine.add (sources L) L.r (L.carry.take 255) (lowY L) ++ notRegister L.r

def eraseCopy (j : Wire) : List Wire → List Wire → Program
  | x::xs,y::ys => [.measureX y [] [.CZ j x]] ++ eraseCopy j xs ys
  | _,_ => []

def unseed (L : Layout) : Program :=
  [.CX L.parity L.r0,
    .measureX L.sign [] [.CZ L.lower (lowY L)],
    .measureX L.one [] [.CZ L.parity (lowY L)],
    .measureX L.lower [] [.CZ L.parity L.rmsb],
    .CX L.r0 L.parity]

def unprepare (L : Layout) (J B : Wire) : Program :=
  (signComplement (lowY L) L.r).reverse ++ (rightShift L).reverse ++
    unseed L ++ eraseCopy J L.r.tail L.y.tail ++ [.measureX (lowY L) [] [.CZ J B]]

def program (L : Layout) (J B : Wire) : Program :=
  clearParity L J ++ restoreAt L J B ++ subtract L ++ unprepare L J B

theorem restoreScalars_counts (p a d e u j b h : Wire) :
    toffoliCount (restoreScalars p a d e u j b h)=4 ∧
      measurementCount (restoreScalars p a d e u j b h)=1 := by
  simp [restoreScalars,toffoliCount,measurementCount]

theorem eraseCopy_counts (j : Wire) (xs ys : List Wire) (hl : xs.length=ys.length) :
    toffoliCount (eraseCopy j xs ys)=0 ∧ measurementCount (eraseCopy j xs ys)=ys.length := by
  induction xs generalizing ys with
  | nil => have h : ys=[] := List.eq_nil_of_length_eq_zero hl.symm; simp [h,eraseCopy,toffoliCount,measurementCount]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have t := ih ys (by simpa using hl)
      simp [eraseCopy,toffoliCount,measurementCount,t.1,t.2,Nat.add_comm]

theorem counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (program L J B)=515 ∧ measurementCount (program L J B)=770 := by
  have w:=BalancedCleanup.widths L.toLayout hw
  have r:=restoreScalars_counts L.parity L.lower L.one L.sign (lowY L) J B L.rmsb
  have a:=arithmetic_counts L hw
  unfold arithmetic at a
  have c:=clearParity_counts L hw J
  have e:=eraseCopy_counts J L.r.tail L.y.tail (by simp [List.length_tail,w.2.1,w.2.2.1])
  have sc:=signComplement_counts (lowY L) L.r
  have rt:=rotate_counts L.r
  simp only [program,restoreAt,subtract,unprepare,rightShift,unseed,arithmetic,
    toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    c.1,c.2,r.1,r.2,a.1,a.2,e.1,e.2,sc.1,sc.2,rt.1,rt.2.1,
    (notRegister_counts L.r).1,(notRegister_counts L.r).2,List.length_tail,w.2.2.1]
  norm_num [toffoliCount,measurementCount]

theorem restoreScalars_inverse (p a d e u j b h : Wire)
    (hn : [p,a,d,e,u,j,b,h].Nodup) (s : State) (m : List Bool)
    (he : s.basis e=(s.basis a && s.basis u))
    (ha : s.basis a=((s.basis p && s.basis h) ^^ s.basis p ^^ s.basis d))
    (hd : s.basis d=(s.basis p && s.basis u))
    (hu : s.basis u=(s.basis j && s.basis b)) :
    run (restoreScalars p a d e u j b h) m
      ⟨s.phase,erasedBasis p a d e u j s.basis⟩=s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  rcases hn with ⟨⟨n01,n02,n03,n04,n05,n06,n07⟩,
    ⟨⟨n12,n13,n14,n15,n16,n17⟩,
    ⟨⟨n23,n24,n25,n26,n27⟩,
    ⟨⟨n34,n35,n36,n37⟩,
    ⟨⟨n45,n46,n47⟩,⟨⟨n56,n57⟩,n67⟩⟩⟩⟩⟩⟩
  have r01 : a≠p := Ne.symm n01
  have r02 : d≠p := Ne.symm n02
  have r03 : e≠p := Ne.symm n03
  have r04 : u≠p := Ne.symm n04
  have r05 : j≠p := Ne.symm n05
  have r06 : b≠p := Ne.symm n06
  have r07 : h≠p := Ne.symm n07
  have r12 : d≠a := Ne.symm n12
  have r13 : e≠a := Ne.symm n13
  have r14 : u≠a := Ne.symm n14
  have r15 : j≠a := Ne.symm n15
  have r16 : b≠a := Ne.symm n16
  have r17 : h≠a := Ne.symm n17
  have r23 : e≠d := Ne.symm n23
  have r24 : u≠d := Ne.symm n24
  have r25 : j≠d := Ne.symm n25
  have r26 : b≠d := Ne.symm n26
  have r27 : h≠d := Ne.symm n27
  have r34 : u≠e := Ne.symm n34
  have r35 : j≠e := Ne.symm n35
  have r36 : b≠e := Ne.symm n36
  have r37 : h≠e := Ne.symm n37
  have r45 : j≠u := Ne.symm n45
  have r46 : b≠u := Ne.symm n46
  have r47 : h≠u := Ne.symm n47
  have r56 : b≠j := Ne.symm n56
  have r57 : h≠j := Ne.symm n57
  have r67 : h≠b := Ne.symm n67
  have erased := EntryHalf5.eraseAnd j p u r45 n04
    (⟨s.phase,erasedBasis p a d e u j s.basis⟩ : State) m (by
      simp [erasedBasis,writeBit,Function.update,n01,n02,n03,n04,n05,n06,n07,n12,n13,n14,n15,n16,n17,n23,n24,n25,n26,n27,n34,n35,n36,n37,n45,n46,n47,n56,n57,n67,r01,r02,r03,r04,r05,r06,r07,r12,r13,r14,r15,r16,r17,r23,r24,r25,r26,r27,r34,r35,r36,r37,r45,r46,r47,r56,r57,r67])
  change run ([.measureX u [] [.CZ j p]] ++
      [.CCX j b u,.CCX p u d,.CX p a,.CCX p h a,.CX d a,.CCX a u e]) m _=s
  rw [run_append,run_take,erased]
  apply State.extensionality
  · simp only [run]
  · funext q
    by_cases qa : q=a
    · subst q
      simp [run,erasedBasis,writeBit,Function.update,n01,n02,n03,n04,n05,n06,n07,n12,n13,n14,n15,n16,n17,n23,n24,n25,n26,n27,n34,n35,n36,n37,n45,n46,n47,n56,n57,n67,r01,r02,r03,r04,r05,r06,r07,r12,r13,r14,r15,r16,r17,r23,r24,r25,r26,r27,r34,r35,r36,r37,r45,r46,r47,r56,r57,r67,ha,hd,he,hu,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
    by_cases qd : q=d
    · subst q
      simp [run,erasedBasis,writeBit,Function.update,n01,n02,n03,n04,n05,n06,n07,n12,n13,n14,n15,n16,n17,n23,n24,n25,n26,n27,n34,n35,n36,n37,n45,n46,n47,n56,n57,n67,r01,r02,r03,r04,r05,r06,r07,r12,r13,r14,r15,r16,r17,r23,r24,r25,r26,r27,r34,r35,r36,r37,r45,r46,r47,r56,r57,r67,ha,hd,he,hu,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
    by_cases qe : q=e
    · subst q
      simp [run,erasedBasis,writeBit,Function.update,n01,n02,n03,n04,n05,n06,n07,n12,n13,n14,n15,n16,n17,n23,n24,n25,n26,n27,n34,n35,n36,n37,n45,n46,n47,n56,n57,n67,r01,r02,r03,r04,r05,r06,r07,r12,r13,r14,r15,r16,r17,r23,r24,r25,r26,r27,r34,r35,r36,r37,r45,r46,r47,r56,r57,r67,ha,hd,he,hu,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
    by_cases qu : q=u
    · subst q
      simp [run,erasedBasis,writeBit,Function.update,n01,n02,n03,n04,n05,n06,n07,n12,n13,n14,n15,n16,n17,n23,n24,n25,n26,n27,n34,n35,n36,n37,n45,n46,n47,n56,n57,n67,r01,r02,r03,r04,r05,r06,r07,r12,r13,r14,r15,r16,r17,r23,r24,r25,r26,r27,r34,r35,r36,r37,r45,r46,r47,r56,r57,r67,ha,hd,he,hu,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
    simp [run,erasedBasis,writeBit,Function.update,qa,qd,qe,qu]
end ECDSAAdd.Entrant.FirstInverse5


set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5
attribute [local irreducible] run

def affineSub (bs : List Affine.Bit) (ys cs : List Wire) (ci : Wire) : Program :=
  notRegister ys ++ Affine.add bs ys cs ci ++ notRegister ys

theorem affine_value_lt (bs : List Affine.Bit) (s : BasisState) : Affine.value bs s<2^bs.length := by
  induction bs with
  | nil => simp [Affine.value]
  | cons b bs ih =>
    have h : (b.value s).toNat≤1 := by cases b.value s <;> decide
    simp only [Affine.value,List.length_cons,Nat.pow_succ]
    omega

theorem complement_inverse (A Y C N : Nat) (hA : A<N) (hY : Y<N) (hC : C≤1) :
    N-1-((A+(N-1-((A+Y+C)%N))+C)%N)=Y := by
  by_cases small : A+Y+C<N
  · rw [Nat.mod_eq_of_lt small]
    have equal : A+(N-1-(A+Y+C))+C=N-1-Y := by omega
    rw [equal,Nat.mod_eq_of_lt (by omega)]
    omega
  · have bound : A+Y+C-N<N := by omega
    have equal : A+Y+C=(A+Y+C-N)+N := by omega
    rw [equal,Nat.add_mod_right,Nat.mod_eq_of_lt bound]
    have inside : A+(N-1-(A+Y+C-N))+C=(N-1-Y)+N := by omega
    rw [inside,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega

theorem affineSub_spec (bits : List Affine.Bit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈Affine.sites bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hvalid : ∀b∈bits,b.Valid) :
    let out := run (affineSub bits ys carry cin) m s
    out.phase=s.phase ∧ (∀q,q∉ys → out.basis q=s.basis q) ∧
      regValue ys out.basis=2^ys.length-1-
        ((Affine.value bits s.basis+(2^ys.length-1-regValue ys s.basis)+(s.basis cin).toNat)%2^ys.length) := by
  have nd := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1
  have away (q : Wire) (hq : q∈cin::carry) : q∉ys := by
    intro bad
    have h:=List.nodup_iff_count.mp hn q
    have a:=List.count_pos_iff.mpr hq
    have b:=List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h a
    omega
  let u : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  have first (record : List Bool) : run (notRegister ys) record s=u := notRegister_correct ys nd s record
  have keep (q : Wire) (hq : q∉ys) : u.basis q=s.basis q := by simp [u,hq]
  have clean : ∀q∈carry,u.basis q=false := by
    intro q hq
    exact (keep q (away q (by simp [hq]))).trans (hclean q hq)
  have src : Affine.value bits u.basis=Affine.value bits s.basis := by
    apply Affine.value_congr
    intro q hq
    exact keep q (fun bad => hs q hq (by simp [bad]))
  have ci : u.basis cin=s.basis cin := keep cin (away cin (by simp))
  have inverted : regValue ys u.basis=2^ys.length-1-regValue ys s.basis := by
    rw [regValue_congr ys u.basis (fun q => !s.basis q) (by intro q hq;simp [u,hq]),regValue_complement]
  obtain ⟨phase,same,value⟩ := Affine.add_correct bits ys carry cin hn hs hl hc u m clean hvalid
  let v := run (Affine.add bits ys carry cin) m u
  have outvalue : regValue ys (fun q => if q∈ys then !v.basis q else v.basis q)=
      2^ys.length-1-regValue ys v.basis := by
    rw [regValue_congr ys _ (fun q => !v.basis q) (by intro q hq;simp [hq]),regValue_complement]
  have zeroM := (notRegister_counts ys).2
  simp only [affineSub,List.append_assoc,run_append,run_take,zeroM,List.take_zero,List.drop_zero]
  rw [first]
  change (run (notRegister ys) _ v).phase=s.phase ∧ _
  rw [notRegister_correct ys nd]
  refine ⟨phase,?_,?_⟩
  · intro q hq
    simp only [hq,if_false]
    exact (same q hq).trans (keep q hq)
  · rw [outvalue,value,src,inverted,ci]

theorem affineSub_inverse (bits : List Affine.Bit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈Affine.sites bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m n : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hvalid : ∀b∈bits,b.Valid) :
    run (affineSub bits ys carry cin) n (run (Affine.add bits ys carry cin) m s)=s := by
  let t:=run (Affine.add bits ys carry cin) m s
  have a:=Affine.add_correct bits ys carry cin hn hs hl hc s m hclean hvalid
  have away (q : Wire) (hq : q∈cin::carry) : q∉ys := by
    intro bad
    have h:=List.nodup_iff_count.mp hn q
    have x:=List.count_pos_iff.mpr hq
    have y:=List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h x
    omega
  have clean : ∀q∈carry,t.basis q=false := fun q hq =>
    (a.2.1 q (away q (by simp [hq]))).trans (hclean q hq)
  have b:=affineSub_spec bits ys carry cin hn hs hl hc t n clean hvalid
  have src : Affine.value bits t.basis=Affine.value bits s.basis := by
    apply Affine.value_congr
    intro q hq
    exact a.2.1 q (fun bad => hs q hq (by simp [bad]))
  have ci : t.basis cin=s.basis cin := a.2.1 cin (away cin (by simp))
  have val : regValue ys (run (affineSub bits ys carry cin) n t).basis=regValue ys s.basis := by
    rw [b.2.2,src,ci,a.2.2]
    exact complement_inverse _ _ _ _ (by simpa [hl] using affine_value_lt bits s.basis)
      (regValue_lt ys s.basis) (by cases s.basis cin <;> decide)
  apply State.extensionality
  · exact b.1.trans a.1
  · funext q
    by_cases qy : q∈ys
    · exact regValue_equal_bits ys _ _ val q qy
    · exact (b.2.1 q qy).trans (a.2.1 q qy)
end ECDSAAdd.Entrant.FirstInverse5


set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5 CleanInverse5
attribute [local irreducible] run

theorem rotateRight_proper (r : List Wire) (hn : r.Nodup) : ProperProgram (rotateRight r) := by
  induction r with
  | nil => simp [rotateRight,ProperProgram]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,ProperProgram]
    | cons b r =>
      have nd:=List.nodup_cons.mp hn
      have ne : a≠b := fun e=>nd.1 (by simp [e])
      exact (properProgram_append _ _).mpr
        ⟨by simp [swapBits,ProperProgram,ProperGate,ne,Ne.symm ne],ih nd.2⟩

theorem rightShift_proper (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ProperProgram (rightShift L) := by
  have len:=BalancedCleanup.widths L.toLayout hw
  have nd:=EntryHalf5.target_nodup L hn
  have lt : 254<L.low.length := by rw [len.1];decide
  have ix : 254<L.r.length := by rw [len.2.1];decide
  have eq : L.r.getD 254 0=L.low[254] := by
    rw [List.getD_eq_getElem _ _ ix]
    exact (List.getElem_append_left' lt [L.rmsb]).symm
  have away : L.rmsb∉L.low := fun h=>List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 h (by simp)
  have ne : L.r.getD 254 0≠L.rmsb := by
    rw [eq]
    exact fun e=>away (e ▸ List.getElem_mem lt)
  exact (properProgram_append _ _).mpr
    ⟨rotateRight_proper L.r nd,by simpa [ProperProgram,ProperGate] using ne⟩

theorem seed_ready (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (s : State)
    (zp : s.basis L.parity=false) (za : s.basis L.lower=false)
    (zd : s.basis L.one=false) (ze : s.basis L.sign=false) :
    Ready (productsSeed L) s := by
  have nd : [L.r0,L.rmsb,L.parity,L.lower,L.one,L.sign,lowY L].Nodup := by
    cases hy : L.ylow with
    | nil => have h:=hw.2.1;simp [hy] at h
    | cons a as =>
      apply List.nodup_iff_count.mpr
      intro q
      have h:=List.nodup_iff_count.mp hn q
      simp only [Layout.wires,BalancedCleanup.Layout.wires,lowY,hy,List.getD_cons_zero,
        List.count_append,List.count_cons,List.count_nil] at h ⊢
      omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨n01,n02,n03,n04,n05,n06⟩,⟨⟨n12,n13,n14,n15,n16⟩,
    ⟨⟨n23,n24,n25,n26⟩,⟨⟨n34,n35,n36⟩,⟨⟨n45,n46⟩,n56⟩⟩⟩⟩⟩
  simp [productsSeed,Ready,CleanTarget,ProperGate,run,writeBit,Function.update,
    zp,za,zd,ze,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,
    n34,n35,n36,n45,n46,n56,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,
    Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,
    Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,
    Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,Ne.symm n56]

theorem prepare_ready (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (s : State)
    (hy : regValue L.y s.basis=0) (hc : ∀q∈work L,s.basis q=false)
    (hz : s.basis L.sign=false) : Ready (prepare L J B) s := by
  have len:=BalancedCleanup.widths L.toLayout hw
  have yhead:=y_cons L hw
  have y0 : lowY L∈L.y := by rw [yhead];simp
  have yn : L.y.Nodup := by
    have nd:=allND L hn
    exact (List.nodup_append'.mp (List.nodup_append'.mp
      (List.nodup_append'.mp nd).2.1).1).2.1
  have ya : lowY L∉L.y.tail := by rw [yhead] at yn;exact (List.nodup_cons.mp yn).1
  have notY (q : Wire) (h : q∉L.wires) : q∉L.y :=
    fun bad=>h (data_member L q (by simp [bad]))
  have nj : J≠lowY L := fun e=>notY J hJ (e.symm ▸ y0)
  have nb : B≠lowY L := fun e=>notY B hB (e.symm ▸ y0)
  have ys : ∀q∈L.y,s.basis q=false := (regValue_zero _ _).mp hy
  let u:=run [.CCX J B (lowY L)] [] s
  have nd : (J::L.r.tail++L.y.tail).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have jp : J∉L.r.tail++L.y.tail := by
      intro bad
      rcases List.mem_append.mp bad with bad|bad
      · exact hJ (data_member L J (by simp [List.mem_of_mem_tail bad]))
      · exact hJ (data_member L J (by simp [List.mem_of_mem_tail bad]))
    have c:=List.nodup_iff_count.mp (copyND L hn) q
    by_cases eq : q=J
    · subst q;simp [jp,List.count_eq_zero.mpr jp]
    · simpa [List.count_cons,eq,Ne.symm eq] using c
  have tail := copy_ready J L.r.tail L.y.tail u nd (by
    intro q hq
    have ne : q≠lowY L := fun e=>ya (e ▸ hq)
    simpa only [u,run,writeBit,Function.update_of_ne ne] using ys q (List.mem_of_mem_tail hq))
  have copy : Ready (copyControl L J B) s := by
    change ProperGate (.CCX J B (lowY L)) ∧ s.basis (lowY L)=false ∧ _
    exact ⟨⟨nj,nb⟩,ys _ y0,tail⟩
  let v:=run (copyControl L J B) [] s
  have cp:=copyControl_spec L hw hn J B hJ hB (s.basis J) (s.basis B)
    (regValue L.r s.basis) s [] rfl hy rfl rfl
  have fl (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : v.basis q=false := by
    have away : q∉L.y := by
      intro bad
      have mem : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
        simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢
        tauto
      exact flagAway L hn q mem (by simp [bad])
    rw [show v.basis q=s.basis q from cp.2.2.2 q away]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact hc _ (by simp [work])
    · exact hc _ (by simp [work])
    · exact hc _ (by simp [work])
    · exact hz
  have seed:=seed_ready L hw hn v (fl _ (by simp)) (fl _ (by simp))
    (fl _ (by simp)) (fl _ (by simp))
  have shift : ∀t,Ready (rightShift L) t :=
    ready_zero _ (rightShift_proper L hw hn) (by
      simp [rightShift,toffoliCount_append,(rotate_counts L.r).1,toffoliCount])
  have nr : lowY L∉L.r := by
    have d:=allND L hn
    have dis:=(List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp d).2.1).1).2.2
    exact fun bad=>List.disjoint_left.mp dis bad y0
  have comp : ∀t,Ready (signComplement (lowY L) L.r) t :=
    ready_zero _ (BalancedCleanup.complement_proper _ _ nr) (signComplement_counts _ _).1
  rw [prepare_shape]
  apply (ready_append _ _ _).mpr
  refine ⟨?_,comp _⟩
  apply (ready_append _ _ _).mpr
  refine ⟨?_,shift _⟩
  exact (ready_append _ _ _).mpr ⟨copy,seed⟩
end ECDSAAdd.Entrant.FirstInverse5


set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5
attribute [local irreducible] run

theorem clear_xor (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (clearParity L J) m s=⟨s.phase,writeBit s.basis L.parity
      (s.basis L.parity ^^ s.basis (lowY L) ^^
        ((!s.basis J) && decide (EntryHalf5.threshold<R.natAbs)))⟩ := by
  let u : State := ⟨s.phase,writeBit s.basis L.parity
    (s.basis L.parity ^^ s.basis (lowY L))⟩
  have pa := flagAway L hn L.parity (by simp)
  have away (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity :=
    fun e=>pa (e ▸ hq)
  have lp : L.lower≠L.parity := by
    have nd:=List.nodup_iff_count.mp (scalarND L hn) L.lower
    intro e;simp [e,List.count_cons] at nd;omega
  have jp : J≠L.parity := fun e=>hJ (by simp [e,Layout.wires,BalancedCleanup.Layout.wires])
  have ur : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hR
    intro q hq
    simp [u,writeBit,away q (by simp [hq])]
  have core:=EntryHalf5.recoverParity_xor L hw hn J hJ (s.basis J) R hr u m ur
    (by simp [u,writeBit,jp]) (by simpa [u,writeBit,lp] using hl)
    (fun q hq=>by simpa [u,writeBit,away q (by simp [hq])] using hc q hq)
  have first : run [.CX (lowY L) L.parity] [] s=u := by simp [run,u]
  change run ([.CX (lowY L) L.parity]++EntryHalf5.recoverParity L J) m s=_
  rw [run_append,show measurementCount [.CX (lowY L) L.parity]=0 from rfl,
    List.take_zero,List.drop_zero,first,core]
  apply State.extensionality
  · rfl
  · funext q
    by_cases qp : q=L.parity
    · subst q;simp [u,writeBit]
    · simp [u,writeBit,qp]

theorem clear_involution (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R) (s : State) (m n : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (clearParity L J) n (run (clearParity L J) m s)=s := by
  let u:=run (clearParity L J) m s
  have a:=clear_xor L hw hn J hJ R hr s m hR hl hc
  have pa:=flagAway L hn L.parity (by simp)
  have away (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity := fun e=>pa (e ▸ hq)
  have same (q : Wire) (hq : q≠L.parity) : u.basis q=s.basis q := by
    rw [show u= _ from a]
    simp [writeBit,hq]
  have lp : L.lower≠L.parity := by
    have nd:=List.nodup_iff_count.mp (scalarND L hn) L.lower
    intro e;simp [e,List.count_cons] at nd;omega
  have jp : J≠L.parity := fun e=>hJ (by simp [e,Layout.wires,BalancedCleanup.Layout.wires])
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have yp : lowY L≠L.parity := away (lowY L) (by
    simp only [List.mem_append];exact Or.inl (Or.inr y0))
  have ur : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans (regValue_congr _ _ _ (fun q hq=>same q (away q (by simp [hq])))) hR
  have b:=clear_xor L hw hn J hJ R hr u n ur ((same _ lp).trans hl)
    (fun q hq=>(same q (away q (by simp [hq]))).trans (hc q hq))
  change run (clearParity L J) n u=s
  rw [b]
  apply State.extensionality
  · rw [show u= _ from a]
  · funext q
    by_cases qp : q=L.parity
    · subst q
      simp only [writeBit,Function.update_self]
      rw [same (lowY L) yp,same J jp]
      rw [show u= _ from a]
      simp [writeBit,yp,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
    · simp only [writeBit,Function.update_of_ne qp]
      exact same q qp
end ECDSAAdd.Entrant.FirstInverse5


set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5 CleanInverse5
attribute [local irreducible] run

def programC (L : Layout) (J B : Wire) : Program :=
  clearParity L J ++ restoreAt L J B ++ affineSub (sources L) L.r (L.carry.take 255) (lowY L) ++
    CleanInverse5.inverse (prepare L J B)

theorem programC_counts (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) :
    toffoliCount (programC L J B)=515 ∧ measurementCount (programC L J B)=770 := by
  let zero : State:=⟨false,fun _=>false⟩
  have ready:=prepare_ready L hw hn J B hJ hB zero
    ((regValue_zero _ _).mpr (by intro q hq;rfl)) (by intro q hq;rfl) rfl
  have k:=CleanInverse5.counts (prepare L J B) (ready_proper _ _ ready)
  have c:=clearParity_counts L hw J
  have r:=restoreScalars_counts L.parity L.lower L.one L.sign (lowY L) J B L.rmsb
  have a:=arithmetic_counts L hw
  have p:=prepare_counts L hw J B
  unfold arithmetic at a
  simp only [programC,restoreAt,affineSub,toffoliCount_append,measurementCount_append,
    k.1,k.2,c.1,c.2,r.1,r.2,a.1,a.2,p.1,
    (notRegister_counts L.r).1,(notRegister_counts L.r).2]
  decide

theorem inverse_forward (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    run (programC L J B) m (run (EntryRetained5.program L J B) [] s)=s := by
  let a:=run (prepare L J B) [] s
  let b:=run (arithmetic L) [] a
  let c:=run (eraseScalarsAt L J B) [] b
  have prep:=prepare_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  change Prepared L J B Jv Bv Y s a at prep
  have pref:=prefix_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  have prefix_run : run (prefixProgram L J B) [] s=b := by
    simp only [prefixProgram,run_append,List.take_nil,List.drop_nil]
    rfl
  rw [prefix_run] at pref
  have dd : b.basis L.one=(b.basis L.parity && b.basis (lowY L)) := by
    rw [pref.parity,pref.u]
    exact pref.d
  have ee : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)) := by
    rw [pref.a,pref.u]
    exact pref.e
  have uu : b.basis (lowY L)=(b.basis J && b.basis B) := by rw [pref.u,pref.j,pref.b]
  have aa:=scalar_erase_relation L hw Jv Bv Y hy b.basis pref.target pref.parity pref.a pref.d
  have erased:=eraseScalarsAt_run L hw hn J B hJ hB hJB b [] ee aa dd uu
  change c=⟨b.phase,erasedBasis L.parity L.lower L.one L.sign (lowY L) J b.basis⟩ at erased
  have en:=erasePorts_nodup L hw hn J B hJ hB hJB
  have restore:=restoreScalars_inverse L.parity L.lower L.one L.sign (lowY L) J B L.rmsb en b
  have undoRestore (n : List Bool) : run (restoreAt L J B) n c=b := by
    rw [erased]
    exact restore n ee aa dd uu
  have nd:=allND L hn
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have data : (L.r++L.y++L.carry).Nodup := (List.nodup_append'.mp nd).2.1
  have ry : (L.r++L.y).Nodup := (List.nodup_append'.mp data).1
  have rdy := (List.nodup_append'.mp ry).2.2
  have dyc := (List.nodup_append'.mp data).2.2
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r++L.y++L.carry := by
    have mem : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢
      tauto
    exact flagAway L hn q mem
  have cSame (q : Wire) (hq : q∈L.r++L.carry) : c.basis q=b.basis q := by
    have qdata : q∈L.r++L.y++L.carry := by
      simp only [List.mem_append] at hq ⊢
      tauto
    have qu : q≠lowY L := by
      intro eq
      rcases List.mem_append.mp hq with qr|qc
      · exact List.disjoint_left.mp rdy qr (eq.symm ▸ y0)
      · exact List.disjoint_left.mp dyc (List.mem_append_right _ y0) (eq ▸ qc)
    have qf (f : Wire) (hf : f∈[L.parity,L.lower,L.one,L.sign]) : q≠f := fun e=>flag f hf (e ▸ qdata)
    rw [erased]
    exact erasedBasis_frame _ _ _ _ _ _ _ q (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      exact not_or_intro (qf _ (by simp)) (not_or_intro (qf _ (by simp))
        (not_or_intro (qf _ (by simp)) qu)))
  have cR : regValue L.r c.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) :=
    (regValue_congr _ _ _ (fun q hq=>cSame q (List.mem_append_left _ hq))).trans pref.target
  have cCarry : ∀q∈L.carry,c.basis q=false := fun q hq=>
    (cSame q (List.mem_append_right _ hq)).trans (pref.carry q hq)
  have ca : c.basis L.lower=false := by
    have ne : L.lower≠lowY L := by
      intro e;exact flag L.lower (by simp) (by simp [e,y0])
    have ad : L.lower≠L.one := by
      have h:=List.nodup_iff_count.mp en L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,ne,ad]
  have bounds:=signedY_bounds (Jv && Bv) Y hy
  have rc : Centered (halfResult (signedY (Jv && Bv) Y)) := by
    apply (halfResult_spec _ ?_).1
    have hp:=constants
    unfold Centered at bounds
    omega
  have undoClear (n : List Bool) :
      run (clearParity L J) n (run (clearParity L J) [] c)=c :=
    clear_involution L hw hn J hJ _ rc c [] n cR ca cCarry
  have undoAdd (n : List Bool) :
      run (affineSub (sources L) L.r (L.carry.take 255) (lowY L)) n b=a := by
    exact affineSub_inverse _ _ _ _ (arithmeticND L hw hn) (sources_away L hw hn)
      (by rw [sources_length,(BalancedCleanup.widths L.toLayout hw).2.1])
      (by simp [List.length_take,hw.2.2,(BalancedCleanup.widths L.toLayout hw).2.1]) a [] n
      (fun q hq=>prep.carry q (List.mem_of_mem_take hq)) (sources_valid L hn)
  have undoPrep (n : List Bool) : run (CleanInverse5.inverse (prepare L J B)) n a=s :=
    CleanInverse5.inverse_run _ _ (prepare_ready L hw hn J B hJ hB s hY hc hz) n
  have forward_run : run (EntryRetained5.program L J B) [] s=run (clearParity L J) [] c := by
    simp only [EntryRetained5.program,prefixProgram,run_append,List.take_nil,List.drop_nil]
    rfl
  rw [forward_run,programC]
  simp only [List.append_assoc,run_append,run_take]
  rw [undoClear,undoRestore,undoAdd,undoPrep]
end ECDSAAdd.Entrant.FirstInverse5


set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5
attribute [local irreducible] run

def putWord : List Wire → Nat → BasisState → BasisState
  | [],_,s => s
  | q::qs,v,s => writeBit (putWord qs (v/2) s) q (decide (v%2=1))

theorem putWord_outside (xs : List Wire) (v : Nat) (s : BasisState) (q : Wire) (hq : q∉xs) :
    putWord xs v s q=s q := by
  induction xs generalizing v with
  | nil => rfl
  | cons a xs ih =>
    have h : q≠a ∧ q∉xs := by simpa using hq
    simp only [putWord,writeBit,Function.update_of_ne h.1,ih _ h.2]

theorem putWord_value (xs : List Wire) (hn : xs.Nodup) (v : Nat) (hv : v<2^xs.length)
    (s : BasisState) : regValue xs (putWord xs v s)=v := by
  induction xs generalizing v with
  | nil =>
    have h : v=0 := by simpa using hv
    subst v
    rfl
  | cons a xs ih =>
    have nd:=List.nodup_cons.mp hn
    have lt : v/2<2^xs.length := by rw [List.length_cons,Nat.pow_succ] at hv;omega
    have tail : regValue xs (putWord (a::xs) v s)=regValue xs (putWord xs (v/2) s) := by
      apply regValue_congr
      intro q hq
      have ne : q≠a := fun e=>nd.1 (e ▸ hq)
      simp [putWord,writeBit,ne]
    change (if putWord (a::xs) v s a then 1 else 0)+2*regValue xs (putWord (a::xs) v s)=v
    rw [tail,ih nd.2 _ lt]
    simp only [putWord,writeBit,Function.update_self]
    have mod:=Nat.mod_lt v (by decide : 0<2)
    have div:=Nat.mod_add_div v 2
    by_cases odd : v%2=1 <;> simp [odd] <;> omega

theorem inverse_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hY : regValue L.y s.basis=encodeWord 256 (if Jv then Y else 0))
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    let out:=run (programC L J B) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis (encodeWord 256 Y) 0 out.basis := by
  let t : State:=⟨s.phase,putWord L.r (encodeWord 256 Y) (putWord L.y 0 s.basis)⟩
  have len:=BalancedCleanup.widths L.toLayout hw
  have nd:=allND L hn
  have nr:=EntryHalf5.target_nodup L hn
  have ny : L.y.Nodup := by
    exact (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).1).2.1
  have dis : List.Disjoint L.r L.y :=
    (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).1).2.2
  have outside (q : Wire) (qr : q∉L.r) (qy : q∉L.y) : t.basis q=s.basis q := by
    simp only [t,putWord_outside _ _ _ q qr,putWord_outside _ _ _ q qy]
  have tr : regValue L.r t.basis=encodeWord 256 Y :=
    putWord_value L.r nr _ (by rw [len.2.1];exact encodeWord_bound 256 Y) _
  have ty : regValue L.y t.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (putWord_value L.y ny 0 (Nat.two_pow_pos _) s.basis)
    intro q hq
    apply putWord_outside
    exact fun bad=>List.disjoint_left.mp dis bad hq
  have noData (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (data_member L q (by simp [bad]))
    · exact hq (data_member L q (by simp [bad]))
  have workAway (q : Wire) (hq : q∈work L) : q∉L.r ∧ q∉L.y := by
    have n:=List.nodup_iff_count.mp nd q
    have w:=List.count_pos_iff.mpr hq
    constructor <;> intro bad <;> have b:=List.count_pos_iff.mpr bad
    all_goals
      simp only [work,List.count_append,List.count_cons,List.count_nil] at w
      simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.y,BalancedCleanup.Layout.low,
        List.count_append,List.count_cons,List.count_nil] at n b
      omega
  have tc : ∀q∈work L,t.basis q=false := fun q hq=>
    (outside q (workAway q hq).1 (workAway q hq).2).trans (hc q hq)
  have signAway : L.sign∉L.r ∧ L.sign∉L.y := by
    have h:=flagAway L hn L.sign (by simp)
    exact ⟨fun a=>h (by simp [a]),fun a=>h (by simp [a])⟩
  have tz : t.basis L.sign=false := (outside _ signAway.1 signAway.2).trans hz
  have tj : t.basis J=Jv := (outside J (noData J hJ).1 (noData J hJ).2).trans hj
  have tb : t.basis B=Bv := (outside B (noData B hB).1 (noData B hB).2).trans hb
  have f:=EntryRetained5.program_frame L hw hn J B hJ hB hJB Jv Bv Y hy t [] tr ty tc tz tj tb
  have ss : PairFrame L.r L.y t.basis
      (encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) s.basis :=
    ⟨hR,hY,fun q qr qy=>(outside q qr qy).symm⟩
  have eq : run (EntryRetained5.program L J B) [] t=s := by
    apply State.extensionality
    · exact f.1
    · exact PairFrame.unique _ _ _ _ _ _ _ f.2 ss
  have inv:=inverse_forward L hw hn J B hJ hB hJB Jv Bv Y hy t m tr ty tc tz tj tb
  rw [eq] at inv
  dsimp only
  rw [inv]
  exact ⟨rfl,tr,ty,outside⟩
end ECDSAAdd.Entrant.FirstInverse5

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CleanInverse5
open Arithmetic Challenge Baselines RecordedQuantum

theorem inverse_support (p : Program) : wires (inverse p)⊆wires p := by
  induction p with
  | nil => simp [inverse]
  | cons i p ih =>
    cases i <;> simp only [inverse,wires_append,Finset.union_subset_iff]
    all_goals constructor
    all_goals first
      | exact ih.trans (Finset.subset_union_right)
      | intro q hq
        simp_all [undo,wires,Instr.wires,correctionWires] <;> tauto

theorem inverse_physical (p : Program) (hp : GatePhysical p) : GatePhysical (inverse p) := by
  induction p with
  | nil => simp [inverse,GatePhysical]
  | cons i p ih =>
    have ht : GatePhysical p := fun j hj=>hp j (by simp [hj])
    have hi:=hp i (by simp)
    rw [inverse,gatePhysical_append]
    refine ⟨ih ht,?_⟩
    cases i <;> simp_all [undo,GatePhysical,PhysicalInstr,ProperGate]

theorem inverse_slots (p : Program) (hp : ProperProgram p) :
    gateSlots (inverse p)≤gateSlots p+toffoliCount p := by
  induction p with
  | nil => simp [inverse,gateSlots]
  | cons i p ih =>
    have hi:=hp i (by simp)
    have h:=ih (fun j hj=>hp j (by simp [hj]))
    cases i <;> simp_all [ProperGate,inverse,undo,gateSlots_append,gateSlots,
      instructionSlots,toffoliCount] <;> omega
end ECDSAAdd.Entrant.CleanInverse5

namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5 Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

theorem programC_support (L : Layout) (hw : L.Widths) (J B : Wire) :
    wires (programC L J B)⊆retSites L J B := by
  have old:=EntryRetained5.program_support L hw J B
  have parts : ((wires (prepare L J B)⊆retSites L J B ∧ wires (arithmetic L)⊆retSites L J B) ∧
      wires (eraseScalarsAt L J B)⊆retSites L J B) ∧ wires (clearParity L J)⊆retSites L J B := by
    simpa only [EntryRetained5.program,prefixProgram,wires_append,Finset.union_subset_iff] using old
  have r (q : Wire) (hq : q∈L.r) : q∈retSites L J B := by simp [retSites,hq]
  have y (q : Wire) (hq : q∈L.y) : q∈retSites L J B := by simp [retSites,hq]
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have rh : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have erase : wires (restoreAt L J B)⊆retSites L J B := by
    intro q hq
    simp only [restoreAt,restoreScalars,wires,Instr.wires,correctionWires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    have hu:=y (lowY L) y0
    have hh:=r L.rmsb rh
    have hp : L.parity∈retSites L J B := by simp [retSites]
    have ha : L.lower∈retSites L J B := by simp [retSites]
    have hd : L.one∈retSites L J B := by simp [retSites]
    have he : L.sign∈retSites L J B := by simp [retSites]
    have hj : J∈retSites L J B := by simp [retSites]
    have hb : B∈retSites L J B := by simp [retSites]
    aesop

  have notr : wires (notRegister L.r)⊆retSites L J B := by
    rw [notRegister_wires]
    intro q hq
    exact r q (List.mem_toFinset.mp hq)
  have sub : wires (affineSub (sources L) L.r (L.carry.take 255) (lowY L))⊆retSites L J B := by
    simp only [affineSub,wires_append,Finset.union_subset_iff]
    exact ⟨⟨notr,parts.1.1.2⟩,notr⟩
  simp only [programC,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨parts.2,erase⟩,sub⟩,(CleanInverse5.inverse_support _).trans parts.1.1.1⟩

theorem programC_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup) :
    GatePhysical (programC L J B) := by
  have old:=EntryRetained5.program_physical L hw hn J B hJ hB hJB
  have parts : ((GatePhysical (prepare L J B) ∧ GatePhysical (arithmetic L)) ∧
      GatePhysical (eraseScalarsAt L J B)) ∧ GatePhysical (clearParity L J) := by
    simpa only [EntryRetained5.program,prefixProgram,gatePhysical_append] using old
  have n:=erasePorts_nodup L hw hn J B hJ hB hJB
  have ctr : (lowY L)≠J ∧ L.parity≠L.lower ∧ (lowY L)≠L.one ∧ L.parity≠L.one ∧
      L.rmsb≠L.lower ∧ L.one≠L.lower ∧ L.lower≠L.sign ∧ (lowY L)≠L.sign ∧ J≠lowY L ∧ B≠lowY L := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at n
    rcases n with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
      ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
    exact ⟨uJ,pA,Ne.symm dU,pD,Ne.symm aH,Ne.symm aD,aE,Ne.symm eU,
      Ne.symm uJ,Ne.symm uB⟩
  have restore : GatePhysical (restoreAt L J B) := by
    simp [restoreAt,restoreScalars,GatePhysical,PhysicalInstr,ProperGate,ctr.1,ctr.2.1,
      ctr.2.2.1,ctr.2.2.2.1,ctr.2.2.2.2.1,ctr.2.2.2.2.2.1,
      ctr.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.2.2]
  have sub : GatePhysical (affineSub (sources L) L.r (L.carry.take 255) (lowY L)) := by
    simp only [affineSub,gatePhysical_append]
    exact ⟨⟨notRegister_physical _,parts.1.1.2⟩,notRegister_physical _⟩
  simp only [programC,gatePhysical_append]
  exact ⟨⟨⟨parts.2,restore⟩,sub⟩,CleanInverse5.inverse_physical _ parts.1.1.1⟩

theorem programC_slots (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) : gateSlots (programC L J B)≤10000 := by
  let zero : State:=⟨false,fun _=>false⟩
  have ready:=prepare_ready L hw hn J B hJ hB zero
    ((regValue_zero _ _).mpr (by intro q hq;rfl)) (by intro q hq;rfl) rfl
  have inv:=CleanInverse5.inverse_slots _ (CleanInverse5.ready_proper _ _ ready)
  have prep:=prepare_slots_le L hw J B
  have arith:=arithmetic_slots L hw
  have par:=clearParity_slots_le L hw J
  have pc:=prepare_counts L hw J B
  have xr:=notRegister_gateSlots L.r
  have len:=BalancedCleanup.widths L.toLayout hw
  have rest : gateSlots (restoreAt L J B)=8 := rfl
  simp only [programC,affineSub,gateSlots_append,show Affine.add (sources L) L.r
    (L.carry.take 255) (lowY L)=arithmetic L from rfl,xr,len.2.1,arith,rest]
  omega
end ECDSAAdd.Entrant.FirstInverse5

set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField

def jointInv (L : BalancedCircuit.Layout) (J G : Wire) : Program :=
  [.X G] ++ programC L J G ++ [.X G]


theorem jointInv_counts (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) :
    toffoliCount (jointInv L J G)=515 ∧ measurementCount (jointInv L J G)=770 := by
  have h:=programC_counts L hw hn J G hJ hG
  simpa only [jointInv,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,Nat.zero_add,Nat.add_zero] using h

private theorem outside_layout (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q ∉ L.wires) : q ∉ L.r ∧ q ∉ L.y ∧ q ∉ BalancedCircuit.work L := by
  have zero := List.count_eq_zero.mpr hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    List.count_append,List.count_cons,List.count_nil] at zero
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at pos
    omega
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at pos
    omega
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at pos
    omega

/-- Read the first sign directly from its history wire and restore that wire.
The two record lists of a later old/new comparison can be independent. -/
theorem jointInv_frame (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J,G].Nodup)
    (Jv Gv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)))
    (hY : regValue L.y s.basis = encodeWord 256 (if Jv then Y else 0))
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false)
    (sign : s.basis L.sign=false) (j : s.basis J=Jv) (g : s.basis G=Gv) :
    let out := run (jointInv L J G) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis
      (encodeWord 256 Y) 0 out.basis := by
  have apart : J≠G := fun eq => (List.nodup_cons.mp hJG).1 (List.mem_singleton.mpr eq)
  have away := outside_layout L G hG
  let a : State := ⟨s.phase,writeBit s.basis G (!s.basis G)⟩
  have head : run [Instr.X G] [] s=a := rfl
  have keep (q : Wire) (hq : q≠G) : a.basis q=s.basis q := by
    simp only [a,writeBit,Function.update_of_ne hq]
  have aR : regValue L.r a.basis=encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)) :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.1 (eq ▸ hq)))).trans hR
  have aY : regValue L.y a.basis=encodeWord 256 (if Jv then Y else 0) :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.2.1 (eq ▸ hq)))).trans hY
  have ac : ∀q∈BalancedCircuit.work L,a.basis q=false := by
    intro q hq
    exact (keep q (fun eq => away.2.2 (eq ▸ hq))).trans (clean q hq)
  have sign_mem : L.sign∈L.wires := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have sg : L.sign≠G := fun eq => hG (eq ▸ sign_mem)
  have aj : a.basis J=Jv := (keep J apart).trans j
  have ag : a.basis G= !Gv := by simp only [a,writeBit,Function.update_self,g]
  generalize ht : run (programC L J G)
    (m.take (measurementCount (programC L J G))) a=t
  have result := inverse_frame L hw hn J G hJ hG hJG Jv (!Gv) Y hy a
    (m.take (measurementCount (programC L J G))) aR aY ac ((keep _ sg).trans sign) aj ag
  rw [ht] at result
  let v : State := ⟨t.phase,writeBit t.basis G (!t.basis G)⟩
  have shape : run (jointInv L J G) m s=v := by
    have xm : measurementCount [Instr.X G]=0 := rfl
    simp only [jointInv,run_append,measurementCount_append,xm,Nat.zero_add,
      List.take_zero,List.drop_zero,head,ht] <;> rfl
  dsimp only
  rw [shape]
  refine ⟨result.1,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.1
    intro q hq
    have qg : q≠G := fun eq => away.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.2.1
    intro q hq
    have qg : q≠G := fun eq => away.2.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · intro q hr hyq
    by_cases eq : q=G
    · subst q
      change (writeBit t.basis G (!t.basis G)) G=s.basis G
      simp only [writeBit,Function.update_self]
      rw [result.2.2.2 G away.1 away.2.1]
      simp only [a,writeBit,Function.update_self,Bool.not_not]
    · change (writeBit t.basis G (!t.basis G)) q=s.basis q
      rw [show (writeBit t.basis G (!t.basis G)) q=t.basis q by
        simp only [writeBit,Function.update_of_ne eq], result.2.2.2 q hr hyq,keep q eq]

end ECDSAAdd.Entrant.FirstInverse5

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField Secp256k1
attribute [local irreducible] run

theorem unary_half (b : Bool) (Z : Fp) :
    halfResult (signedY b (centerFp Z))=centerFp ((if b then -Z else Z)/2) := by
  have h:=signedY_bounds b (centerFp Z) (centerFp_bounds Z)
  have q0 : 0≤BalancedField.q := (BalancedField.constants).1.le
  have bounds : -(2*BalancedField.q)≤signedY b (centerFp Z) ∧
      signedY b (centerFp Z)≤2*BalancedField.q := by
    unfold Centered at h
    omega
  have hh:=halfResult_center _ bounds
  cases b <;> simpa only [signedY,Bool.false_eq_true,if_false,if_true,Int.cast_neg,centerFp_cast] using hh

theorem source_word (b : Bool) (Z : Fp) :
    encodeWord 256 (if b then centerFp Z else 0)=centerWord (if b then Z else 0) := by
  cases b
  · simp [centerWord,centerFp,encodeWord,show (0:Int)≤q from (constants).1.le]
  · rfl

theorem work_no_data (L : Layout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈work L) :
    q∉L.r ∧ q∉L.y := by
  have nd:=allND L hn
  have h:=List.nodup_iff_count.mp nd q
  have w:=List.count_pos_iff.mpr hq
  constructor <;> intro bad <;> have b:=List.count_pos_iff.mpr bad
  all_goals
    simp only [work,List.count_append,List.count_cons,List.count_nil] at w
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.y,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at h b
    omega

theorem jointInv_pair (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (origin : BasisState) (clean : ∀q∈work L,origin q=false) (sign : origin L.sign=false)
    (Z : Fp) :
    Triple (PairFrame L.r L.y origin
      (centerWord ((if origin J && !origin G then -Z else Z)/2))
      (centerWord (if origin J then Z else 0))) (jointInv L J G)
      (PairFrame L.r L.y origin (centerWord Z) 0) := by
  have outside (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
  have sf:=flagAway L hn L.sign (by simp)
  have sa : L.sign∉L.r ∧ L.sign∉L.y :=
    ⟨fun bad=>sf (by simp [bad]),fun bad=>sf (by simp [bad])⟩
  intro s m h
  have hc : ∀q∈work L,s.basis q=false := fun q hq=>
    (h.2.2 q (work_no_data L hn q hq).1 (work_no_data L hn q hq).2).trans (clean q hq)
  have rr : regValue L.r s.basis=encodeWord 256
      (halfResult (signedY (origin J && !origin G) (centerFp Z))) := by
    rw [unary_half]
    exact h.1
  have yy : regValue L.y s.basis=encodeWord 256 (if origin J then centerFp Z else 0) := by
    rw [source_word]
    exact h.2.1
  have out:=jointInv_frame L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m rr yy hc ((h.2.2 _ sa.1 sa.2).trans sign)
    (h.2.2 _ (outside J hJ).1 (outside J hJ).2) (h.2.2 _ (outside G hG).1 (outside G hG).2)
  exact ⟨out.1,out.2.1,out.2.2.1,fun q qr qy=>(out.2.2.2 q qr qy).trans (h.2.2 q qr qy)⟩

theorem matrix_inverse (J G : Bool) (X Y : Fp)
    (hz : (if J then 2*X+(if G then -Y else Y) else Y)=0) :
    let Z:=if J then Y else 2*X+(if G then -Y else Y)
    X=(if J && !G then -Z else Z)/2 ∧ Y=(if J then Z else 0) := by
  have two : (2:Fp)≠0 := by decide
  cases J
  · simp only [Bool.false_eq_true,if_false,Bool.false_and] at hz ⊢
    rw [hz]
    cases G <;> simp [mul_div_cancel_left₀ X two]
  · simp only [if_true,Bool.true_and] at hz ⊢
    refine ⟨?_,trivial⟩
    cases G <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false] at hz ⊢
    all_goals apply (eq_div_iff two).mpr
    · linear_combination hz
    · linear_combination hz
end ECDSAAdd.Entrant.FirstInverse5


/-! ## Hosting the two carries that have no physical site in the 1,588 layout -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

/-- Carry #4 (virtual `516`) and carry #254 (virtual `1541`). -/
def cLo (L : Layout) : Wire := L.carry.getD 4 0
def cHi (L : Layout) : Wire := L.carry.getD 254 0

theorem pull_swap_invol (a b : Wire) (s : State) :
    pullState (Equiv.swap a b) (pullState (Equiv.swap a b) s)=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (Equiv.swap a b (Equiv.swap a b q))=s.basis q
    rw [Equiv.swap_apply_self]

/-- A program may run with two clean sites exchanged. -/
theorem rebind_swap_run (a b : Wire) (P : Program) (s : State) (m : List Bool)
    (ha : s.basis a=false) (hb : s.basis b=false)
    (oa : (run P m s).basis a=false) (ob : (run P m s).basis b=false) :
    run (renameProgram (Equiv.swap a b) P) m s=run P m s := by
  have eq := ECDSAAdd.run_rename (Equiv.swap a b) (Equiv.swap a b).injective P m s
  rw [pullState_zero_swap a b s ha hb,
    ←pullState_zero_swap a b (run P m s) oa ob] at eq
  have both := congrArg (pullState (Equiv.swap a b)) eq
  simpa only [pull_swap_invol] using both

/-! ### Records -/

theorem append_split (l r : List Bool) (n : Nat) (hl : l.length≤n)
    (hr : l.length<n → r=[]) : (l++r).take n=l ∧ (l++r).drop n=r := by
  rcases Nat.lt_or_ge l.length n with h|h
  · have e := hr h
    subst e
    simp only [List.append_nil]
    exact ⟨List.take_of_length_le hl,List.drop_eq_nil_of_le hl⟩
  · have e : l.length=n := le_antisymm hl h
    subst e
    simp

/-- Replace a block `P` by a block `Q` whose first `k` records are extra. -/
theorem context_eq (Pre P Q Post : Program) (k : Nat) (s : State) (m : List Bool)
    (hpre : measurementCount Pre=0) (hq : measurementCount Q=k+measurementCount P)
    (hrun : ∀r,run Q r (run Pre [] s)=run P (r.drop k) (run Pre [] s)) :
    run (Pre++Q++Post) m s=
      run (Pre++P++Post) ((m.drop k).take (measurementCount P)++m.drop (measurementCount Q)) s := by
  let A := (m.drop k).take (measurementCount P)
  let B := m.drop (measurementCount Q)
  have lenA : A.length≤measurementCount P := List.length_take_le _ _
  have short : A.length<measurementCount P → B=[] := by
    intro h
    have hA : A.length=(m.drop k).length := by
      simp only [A,List.length_take] at h ⊢
      omega
    have : m.length≤measurementCount Q := by
      simp only [List.length_drop] at hA
      omega
    exact List.drop_eq_nil_of_le this
  have sp := append_split A B (measurementCount P) lenA short
  rw [List.append_assoc,run_append,hpre,List.take_zero,List.drop_zero,run_append,
    List.append_assoc,run_append,hpre,List.take_zero,List.drop_zero,run_append,sp.1,sp.2,
    hrun]
  congr 2
  simp only [A]
  rw [List.drop_take,hq,Nat.add_sub_cancel_left]

/-! ### The measured loan of `sign` (= lower∧lowY) and `lowY` (= J∧B) -/

def loanW (e a u j b lo hi : Wire) (P : Program) : Program :=
  [.measureX e [] [.CZ a u],.measureX u [] [.CZ j b]]++
    renameProgram (Equiv.swap hi e) (renameProgram (Equiv.swap lo u) P)++
    [.CCX j b u,.CCX a u e]

theorem loanW_counts (e a u j b lo hi : Wire) (P : Program) :
    toffoliCount (loanW e a u j b lo hi P)=toffoliCount P+2 ∧
    measurementCount (loanW e a u j b lo hi P)=2+measurementCount P := by
  have r1 := renameProgram_counts (Equiv.swap lo u) P
  have r2 := renameProgram_counts (Equiv.swap hi e) (renameProgram (Equiv.swap lo u) P)
  simp only [loanW,toffoliCount_append,measurementCount_append,r1.1,r1.2,r2.1,r2.2,
    toffoliCount,measurementCount]
  omega

theorem loanW_run (e a u j b lo hi : Wire) (P : Program) (x : State) (r : List Bool)
    (nd : [e,a,u,j,b,lo,hi].Nodup)
    (he : x.basis e=(x.basis a && x.basis u)) (hu : x.basis u=(x.basis j && x.basis b))
    (ue : u∉wires P) (ee : e∉wires P)
    (keep : ∀t,(run P t x).basis a=x.basis a ∧ (run P t x).basis j=x.basis j ∧
      (run P t x).basis b=x.basis b)
    (lo0 : x.basis lo=false) (hi0 : x.basis hi=false)
    (loOut : ∀t,(run P t x).basis lo=false) (hiOut : ∀t,(run P t x).basis hi=false) :
    run (loanW e a u j b lo hi P) r x=run P (r.drop 2) x := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨ea,eu,ej,eb,elo,ehi⟩,⟨⟨au,aj,ab,alo,ahi⟩,⟨⟨uj,ub,ulo,uhi⟩,
    ⟨⟨jb,jlo,jhi⟩,⟨⟨blo,bhi⟩,lohi⟩⟩⟩⟩⟩
  let t := r.drop 2
  let x1 : State := ⟨x.phase,writeBit x.basis e false⟩
  let x2 : State := ⟨x.phase,writeBit (writeBit x.basis e false) u false⟩
  have step1 : run [.measureX e [] [.CZ a u]] (r.take 1) x=x1 :=
    EntryHalf5.eraseAnd a u e (Ne.symm ea) (Ne.symm eu) x _ he
  have step2 : run [.measureX u [] [.CZ j b]] ((r.drop 1).take 1) x1=x2 := by
    have h := EntryHalf5.eraseAnd j b u (Ne.symm uj) (Ne.symm ub) x1 ((r.drop 1).take 1) (by
      simp only [x1,writeBit,Function.update_of_ne (Ne.symm eu),Function.update_of_ne (Ne.symm ej),
        Function.update_of_ne (Ne.symm eb)]
      exact hu)
    simpa only [x1,x2] using h
  have unloan : run [.measureX e [] [.CZ a u],.measureX u [] [.CZ j b]] (r.take 2) x=x2 := by
    have split : ([.measureX e [] [.CZ a u],.measureX u [] [.CZ j b]] : Program)=
        [.measureX e [] [.CZ a u]]++[.measureX u [] [.CZ j b]] := rfl
    rw [split,run_append]
    have c1 : measurementCount ([.measureX e [] [.CZ a u]] : Program)=1 := rfl
    rw [c1,List.take_take,show min 1 2=1 from rfl,step1,List.drop_take]
    simpa only [show 2-1=1 from rfl] using step2
  -- running `P` on the zeroed state
  have w1 := G0CarryLoan5.run_write_outside P e ee x t false
  have w2 := G0CarryLoan5.run_write_outside P u ue x1 t false
  let y := run P t x
  have yrun : run P t x2=⟨y.phase,writeBit (writeBit y.basis e false) u false⟩ := by
    change run P t ⟨x1.phase,writeBit x1.basis u false⟩=_
    rw [w2]
    change (⟨(run P t ⟨x.phase,writeBit x.basis e false⟩).phase,
      writeBit (run P t ⟨x.phase,writeBit x.basis e false⟩).basis u false⟩ : State)=_
    rw [w1]
  have yu : y.basis u=x.basis u := run_preserves_outside P t x u ue
  have ye : y.basis e=x.basis e := run_preserves_outside P t x e ee
  have k := keep t
  -- rebinding the two hosts
  have inner : run (renameProgram (Equiv.swap lo u) P) t x2=run P t x2 := by
    apply rebind_swap_run lo u P x2 t
    · simp only [x2,writeBit,Function.update_of_ne (Ne.symm ulo),Function.update_of_ne (Ne.symm elo)]
      exact lo0
    · simp only [x2,writeBit,Function.update_self]
    · rw [yrun]
      simp only [writeBit,Function.update_of_ne (Ne.symm ulo),Function.update_of_ne (Ne.symm elo)]
      exact loOut t
    · rw [yrun]
      simp only [writeBit,Function.update_self]
  have outer : run (renameProgram (Equiv.swap hi e) (renameProgram (Equiv.swap lo u) P)) t x2=
      run P t x2 := by
    rw [rebind_swap_run hi e _ x2 t ?_ ?_ ?_ ?_,inner]
    · simp only [x2,writeBit,Function.update_of_ne (Ne.symm uhi),Function.update_of_ne (Ne.symm ehi)]
      exact hi0
    · simp only [x2,writeBit,Function.update_of_ne eu,Function.update_self]
    · rw [inner,yrun]
      simp only [writeBit,Function.update_of_ne (Ne.symm uhi),Function.update_of_ne (Ne.symm ehi)]
      exact hiOut t
    · rw [inner,yrun]
      simp only [writeBit,Function.update_of_ne eu,Function.update_self]
  have c2 : measurementCount ([.measureX e [] [.CZ a u],.measureX u [] [.CZ j b]] : Program)=2 := rfl
  rw [loanW,List.append_assoc,run_append,c2,unloan,run_append,run_take,outer,yrun]
  have ya : y.basis a=x.basis a := k.1
  have yj : y.basis j=x.basis j := k.2.1
  have yb : y.basis b=x.basis b := k.2.2
  change _=y
  apply State.extensionality
  · simp only [run]
  · funext q
    simp only [run,writeBit,Function.update_apply]
    by_cases qe : q=e
    · subst q
      simp [Ne.symm eu,Ne.symm ea,Ne.symm ej,Ne.symm eb,au,aj,ab,uj,ub,ya,yj,yb,ye,yu,he,hu,
        Ne.symm au,Ne.symm aj,Ne.symm ab,Ne.symm uj,Ne.symm ub,eu,ea,ej,eb]
    · by_cases qu : q=u
      · subst q
        simp [Ne.symm eu,Ne.symm uj,Ne.symm ub,uj,ub,yj,yb,yu,hu,eu,Ne.symm ej,Ne.symm eb,ej,eb]
      · simp [qe,qu]

end ECDSAAdd.Entrant.JointInverse1588


/-! ### Splitting the subtraction's adder after its first four source bits -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

def rAt (L : Layout) (i : Nat) : Wire := L.r.getD i 0
def cAt (L : Layout) (i : Nat) : Wire := L.carry.getD i 0

def pre4 (L : Layout) : Program :=
  Affine.majority (source L 0) (rAt L 0) (lowY L) (cAt L 0)++
  Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)++
  Affine.majority (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)++
  Affine.majority (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)

def inner (L : Layout) : Program :=
  Affine.add ((sources L).drop 4) (L.r.drop 4) ((L.carry.take 255).drop 4) (cAt L 3)

def post4 (L : Layout) : Program :=
  Affine.erase (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)++Affine.sum (source L 3) (rAt L 3) (cAt L 2)++
  Affine.erase (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)++Affine.sum (source L 2) (rAt L 2) (cAt L 1)++
  Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)++Affine.sum (source L 1) (rAt L 1) (cAt L 0)++
  Affine.erase (source L 0) (rAt L 0) (lowY L) (cAt L 0)++Affine.sum (source L 0) (rAt L 0) (lowY L)

theorem range_head : List.range 256=0::1::2::3::4::List.range' 5 251 := by decide

theorem shapes (L : Layout) (hw : L.Widths) :
    ∃ r1 r2 r3 r4 rt c0 c1 c2 c3 ct,
      L.r=L.r0::r1::r2::r3::r4::rt ∧ L.carry.take 255=c0::c1::c2::c3::ct ∧
      sources L=source L 0::source L 1::source L 2::source L 3::source L 4::
        (List.range' 5 251).map (source L) := by
  have len := hw
  obtain ⟨hrt,_,hc⟩ := len
  match hr : L.rtail, hcc : L.carry with
  | r1::r2::r3::r4::rt, c0::c1::c2::c3::ct =>
    refine ⟨r1,r2,r3,r4,rt++[L.rmsb],c0,c1,c2,c3,ct.take 251,?_,?_,?_⟩
    · simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,hr]
    · simp
    · simp only [sources,range_head,List.map_cons]
  | [],_ => simp [hr] at hrt
  | [_],_ => simp [hr] at hrt
  | [_,_],_ => simp [hr] at hrt
  | [_,_,_],_ => simp [hr] at hrt
  | _::_::_::_::_,[] => simp [hcc] at hc
  | _::_::_::_::_,[_] => simp [hcc] at hc
  | _::_::_::_::_,[_,_] => simp [hcc] at hc
  | _::_::_::_::_,[_,_,_] => simp [hcc] at hc

theorem add_split (L : Layout) (hw : L.Widths) :
    Affine.add (sources L) L.r (L.carry.take 255) (lowY L)=pre4 L++inner L++post4 L := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,hs⟩ := shapes L hw
  have hc' : L.carry.getD 0 0=c0 ∧ L.carry.getD 1 0=c1 ∧ L.carry.getD 2 0=c2 ∧
      L.carry.getD 3 0=c3 := by
    have t : ∀i,i<255 → L.carry.getD i 0=(L.carry.take 255).getD i 0 := by
      intro i hi
      simp only [List.getD_eq_getElem?_getD,List.getElem?_take,if_pos hi]
    rw [t 0 (by decide),t 1 (by decide),t 2 (by decide),t 3 (by decide),hc]
    simp
  simp only [pre4,inner,post4,rAt,cAt,hr,hs,hc,hc'.1,hc'.2.1,hc'.2.2.1,hc'.2.2.2,
    List.getD_cons_zero,List.getD_cons_succ,List.drop_succ_cons,List.drop_zero,
    List.map_cons,Affine.add,List.append_assoc]

theorem pre4_counts (L : Layout) : toffoliCount (pre4 L)=4 ∧ measurementCount (pre4 L)=0 := by
  have a := Affine.bit_counts (source L 0) (rAt L 0) (lowY L) (cAt L 0)
  have b := Affine.bit_counts (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
  have c := Affine.bit_counts (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)
  have d := Affine.bit_counts (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)
  simp only [pre4,toffoliCount_append,measurementCount_append,a.1,a.2.1,b.1,b.2.1,c.1,c.2.1,d.1,d.2.1]
  decide

theorem post4_counts (L : Layout) : toffoliCount (post4 L)=0 ∧ measurementCount (post4 L)=4 := by
  have a := Affine.bit_counts (source L 0) (rAt L 0) (lowY L) (cAt L 0)
  have b := Affine.bit_counts (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
  have c := Affine.bit_counts (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)
  have d := Affine.bit_counts (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)
  simp only [post4,toffoliCount_append,measurementCount_append,a.2.2.1,a.2.2.2.1,a.2.2.2.2.1,
    a.2.2.2.2.2,b.2.2.1,b.2.2.2.1,b.2.2.2.2.1,b.2.2.2.2.2,c.2.2.1,c.2.2.2.1,c.2.2.2.2.1,
    c.2.2.2.2.2,d.2.2.1,d.2.2.2.1,d.2.2.2.2.1,d.2.2.2.2.2]
  decide

end ECDSAAdd.Entrant.JointInverse1588


/-! ### The hosted measured inverse -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

/-- `positiveParity` with carry #248 hosted on `rmsb`: `prepareMagnitude` copies `rmsb` into the clean
`lower` and complements the whole target word under it, so `rmsb` is clean for the whole carry chain,
which reads only the low 255 target bits. -/
def positiveParityH (L : Layout) (ctl : Wire) : Program :=
  EntryHalf5.prepareMagnitude L++(renameProgram (Equiv.swap (cAt L 248) L.rmsb)
    (EntryHalf5.parityCarry L ctl)++(EntryHalf5.prepareMagnitude L).reverse)

def recoverParityH (L : Layout) (J : Wire) : Program :=
  [.X J]++positiveParityH L J++[.X J]

def clearParityH (L : Layout) (J : Wire) : Program :=
  [.CX (L.ylow.getD 0 0) L.parity]++recoverParityH L J

/-- The measured loan of carry #1 around `loanW`: carry #1 (`maj(one⊕sign,r1,c0)`, still readable
while `sign` is present) is erased before `loanW`'s two measurements and recomputed after its two
Toffolis; inside, carry #248 is hosted on carry #1's site. -/
def loanC (L : Layout) (J B : Wire) : Program :=
  Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)++
    (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L)
      (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L))++
    Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))

/-- `clearParity` with carry #4 on `one`, carry #254 on `sign` and carry #248 on `rmsb`. -/
def clearH (L : Layout) (J : Wire) : Program :=
  renameProgram (Equiv.swap (cHi L) L.sign) (renameProgram (Equiv.swap (cLo L) L.one) (clearParityH L J))

/-- The subtraction with carry #4 on `lowY`, carry #254 on `sign` and (measured loan of carry #1)
carry #248 on carry #1's site inside source bits 4..255. -/
def affineH (L : Layout) (J B : Wire) : Program :=
  notRegister L.r++pre4 L++loanC L J B++post4 L++notRegister L.r

def programH (L : Layout) (J B : Wire) : Program :=
  clearH L J++restoreAt L J B++affineH L J B++CleanInverse5.inverse (prepare L J B)

theorem carry_mem (L : Layout) (hw : L.Widths) (i : Nat) (hi : i<256) : L.carry.getD i 0∈L.carry := by
  have len : i<L.carry.length := by rw [hw.2.2];exact hi
  rw [List.getD_eq_getElem _ _ len]
  exact List.getElem_mem len

theorem carry_take_mem (L : Layout) (hw : L.Widths) (i : Nat) (hi : i<255) :
    L.carry.getD i 0∈L.carry.take 255 := by
  have len : i<(L.carry.take 255).length := by simp [hw.2.2,hi]
  have eq : L.carry.getD i 0=(L.carry.take 255).getD i 0 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_take,if_pos hi]
  rw [eq,List.getD_eq_getElem _ _ len]
  exact List.getElem_mem len

/-- The scalars and the two hosted carries are distinct. -/
theorem hosts_distinct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.one≠cLo L ∧ L.one≠cHi L ∧ L.parity≠cLo L ∧ L.parity≠cHi L ∧ L.one≠L.sign ∧
      cLo L≠cHi L ∧ L.parity≠L.one ∧ L.parity≠L.sign := by
  have nd := allND L hn
  have lo := carry_mem L hw 4 (by decide)
  have hi := carry_mem L hw 254 (by decide)
  have cd : (L.carry).Nodup :=
    (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).2.1
  have loHi : cLo L≠cHi L := by
    intro e
    have := (List.Nodup.getElem_inj_iff cd (i:=4) (j:=254) (hi:=by rw [hw.2.2];decide)
      (hj:=by rw [hw.2.2];decide)).mp (by
        simp only [cLo,cHi,List.getD_eq_getElem _ _ (show 4<L.carry.length by rw [hw.2.2];decide),
          List.getD_eq_getElem _ _ (show 254<L.carry.length by rw [hw.2.2];decide)] at e
        exact e)
    omega
  have flags (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q∉L.r++L.y++L.carry := flagAway L hn q hq
  have sc := scalarND L hn
  have dataIn (q : Wire) (hq : q∈L.carry) : q∈L.r++L.y++L.carry := by
    simp only [List.mem_append]; tauto
  have nO (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.one := fun e => flags L.one (by simp) (e ▸ hq)
  have nP (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity := fun e => flags L.parity (by simp) (e ▸ hq)
  have os : L.one≠L.sign := by
    have h := List.nodup_iff_count.mp sc L.one
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  have ps : L.parity≠L.sign := by
    have h := List.nodup_iff_count.mp sc L.parity
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  have po : L.parity≠L.one := by
    have h := List.nodup_iff_count.mp sc L.parity
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  exact ⟨Ne.symm (nO _ (dataIn _ lo)),Ne.symm (nO _ (dataIn _ hi)),
    Ne.symm (nP _ (dataIn _ lo)),Ne.symm (nP _ (dataIn _ hi)),os,loHi,po,ps⟩

/-- The scalars, the two hosted carries and the controls are distinct. -/
theorem ports_distinct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup) :
    [L.sign,L.lower,lowY L,J,B,cLo L,cHi L].Nodup ∧ L.one≠cLo L ∧ L.one≠cHi L ∧
      L.parity≠cLo L ∧ L.parity≠cHi L ∧ L.one≠L.sign ∧ cLo L≠cHi L ∧ L.parity≠L.one ∧
      L.parity≠L.sign := by
  have nd := allND L hn
  have lo := carry_mem L hw 4 (by decide)
  have hi := carry_mem L hw 254 (by decide)
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have cd : (L.carry).Nodup :=
    (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).2.1
  have loHi : cLo L≠cHi L := by
    intro e
    have := (List.Nodup.getElem_inj_iff cd (i:=4) (j:=254) (hi:=by rw [hw.2.2];decide)
      (hj:=by rw [hw.2.2];decide)).mp (by
        simp only [cLo,cHi,List.getD_eq_getElem _ _ (show 4<L.carry.length by rw [hw.2.2];decide),
          List.getD_eq_getElem _ _ (show 254<L.carry.length by rw [hw.2.2];decide)] at e
        exact e)
    omega
  have flags (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q∉L.r++L.y++L.carry := flagAway L hn q hq
  have sc := scalarND L hn
  have notData (q : Wire) (hq : q∉L.wires) : q∉L.r++L.y++L.carry := fun bad => hq (data_member L q bad)
  have dataIn (q : Wire) (hq : q∈L.carry ∨ q∈L.y) : q∈L.r++L.y++L.carry := by
    simp only [List.mem_append]; tauto
  have jb : J≠B := by simpa using hJB
  -- scalar distinctness
  have sl : L.sign≠L.lower := by
    have h := List.nodup_iff_count.mp sc L.sign
    intro e; rw [←e] at h; simp [List.count_cons] at h; omega
  have nS (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.sign := fun e => flags L.sign (by simp) (e ▸ hq)
  have nL (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.lower := fun e => flags L.lower (by simp) (e ▸ hq)
  have nO (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.one := fun e => flags L.one (by simp) (e ▸ hq)
  have nP (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity := fun e => flags L.parity (by simp) (e ▸ hq)
  have nJ (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠J := fun e => notData J hJ (e ▸ hq)
  have nB (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠B := fun e => notData B hB (e ▸ hq)
  have sJ : L.sign≠J := fun e => hJ (e ▸ (by simp [Layout.wires,BalancedCleanup.Layout.wires]))
  have sB : L.sign≠B := fun e => hB (e ▸ (by simp [Layout.wires,BalancedCleanup.Layout.wires]))
  have lJ : L.lower≠J := fun e => hJ (e ▸ (by simp [Layout.wires,BalancedCleanup.Layout.wires]))
  have lB : L.lower≠B := fun e => hB (e ▸ (by simp [Layout.wires,BalancedCleanup.Layout.wires]))
  have yc : lowY L≠cLo L ∧ lowY L≠cHi L := by
    have d := (List.nodup_append'.mp nd).2.1
    have yc := (List.nodup_append'.mp d).2.2
    exact ⟨fun e => List.disjoint_left.mp yc (List.mem_append_right _ y0) (e ▸ lo),
      fun e => List.disjoint_left.mp yc (List.mem_append_right _ y0) (e ▸ hi)⟩
  have os : L.one≠L.sign := by
    have h := List.nodup_iff_count.mp sc L.one
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  have ps : L.parity≠L.sign := by
    have h := List.nodup_iff_count.mp sc L.parity
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  have po : L.parity≠L.one := by
    have h := List.nodup_iff_count.mp sc L.parity
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  refine ⟨?_,Ne.symm (nO _ (dataIn _ (Or.inl lo))),Ne.symm (nO _ (dataIn _ (Or.inl hi))),
    Ne.symm (nP _ (dataIn _ (Or.inl lo))),Ne.symm (nP _ (dataIn _ (Or.inl hi))),os,loHi,po,ps⟩
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true]
  refine ⟨⟨sl,Ne.symm (nS _ (dataIn _ (Or.inr y0))),sJ,sB,Ne.symm (nS _ (dataIn _ (Or.inl lo))),
    Ne.symm (nS _ (dataIn _ (Or.inl hi)))⟩,⟨Ne.symm (nL _ (dataIn _ (Or.inr y0))),lJ,lB,
    Ne.symm (nL _ (dataIn _ (Or.inl lo))),Ne.symm (nL _ (dataIn _ (Or.inl hi)))⟩,
    ⟨nJ _ (dataIn _ (Or.inr y0)),nB _ (dataIn _ (Or.inr y0)),yc.1,yc.2⟩,
    ⟨jb,fun e => nJ _ (dataIn _ (Or.inl lo)) e.symm,fun e => nJ _ (dataIn _ (Or.inl hi)) e.symm⟩,
    ⟨fun e => nB _ (dataIn _ (Or.inl lo)) e.symm,fun e => nB _ (dataIn _ (Or.inl hi)) e.symm⟩,loHi⟩

end ECDSAAdd.Entrant.JointInverse1588


/-! ### Facts about the four leading majorities and the inner adder -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

theorem source_mem (L : Layout) (i : Nat) (hi : i<256) : source L i∈sources L :=
  List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩

theorem source_site (L : Layout) (i : Nat) (hi : i<256) (q : Wire) (hq : q∈(source L i).wires) :
    q∈Affine.sites (sources L) :=
  List.mem_flatMap.mpr ⟨source L i,source_mem L i hi,hq⟩

/-- Positions of the first four targets and carries. -/
theorem atoms (L : Layout) (hw : L.Widths) :
    ∃ r1 r2 r3 r4 rt c0 c1 c2 c3 ct,
      L.r=L.r0::r1::r2::r3::r4::rt ∧ L.carry.take 255=c0::c1::c2::c3::ct ∧
      rAt L 0=L.r0 ∧ rAt L 1=r1 ∧ rAt L 2=r2 ∧ rAt L 3=r3 ∧
      cAt L 0=c0 ∧ cAt L 1=c1 ∧ cAt L 2=c2 ∧ cAt L 3=c3 := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,_⟩ := shapes L hw
  have t : ∀i,i<255 → L.carry.getD i 0=(L.carry.take 255).getD i 0 := by
    intro i hi
    simp only [List.getD_eq_getElem?_getD,List.getElem?_take,if_pos hi]
  refine ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | simp [rAt,hr]
    | (simp only [cAt]; rw [t _ (by decide),hc]; simp)

theorem maj_keep (b : Affine.Bit) (hb : b.Valid) (y cin co : Wire)
    (hn : [y,cin,co].Nodup) (ha : ∀q∈b.wires,q∉[y,cin,co]) (s : State) (m : List Bool) :
    (run (Affine.majority b y cin co) m s).phase=s.phase ∧
    ∀q,q≠co → (run (Affine.majority b y cin co) m s).basis q=s.basis q := by
  rw [Affine.majority_correct b hb y cin co hn ha s m]
  exact ⟨rfl,fun q hq => by simp [writeBit,hq]⟩

theorem pre4_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (s : State) (m : List Bool) :
    (run (pre4 L) m s).phase=s.phase ∧
    ∀q,q≠cAt L 0 → q≠cAt L 1 → q≠cAt L 2 → q≠cAt L 3 → (run (pre4 L) m s).basis q=s.basis q := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have nd := arithmeticND L hw hn
  have away := sources_away L hw hn
  rw [hr,hc] at nd
  have sub : [lowY L,L.r0,r1,r2,r3,c0,c1,c2,c3].Sublist
      (lowY L::(L.r0::r1::r2::r3::r4::rt++c0::c1::c2::c3::ct)) := by
    apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂
    apply List.Sublist.cons₂;apply List.Sublist.cons₂
    apply List.Sublist.cons
    apply List.sublist_append_of_sublist_right
    apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂
    exact List.nil_sublist _
  have nd9 := nd.sublist sub
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd9
  rcases nd9 with ⟨⟨u0,u1,u2,u3,uc0,uc1,uc2,uc3⟩,⟨⟨a1,a2,a3,a0c0,a0c1,a0c2,a0c3⟩,
    ⟨⟨b2,b3,b1c0,b1c1,b1c2,b1c3⟩,⟨⟨c23,c2c0,c2c1,c2c2,c2c3⟩,⟨⟨d0,d1,d2,d3⟩,
    ⟨⟨g01,g02,g03⟩,⟨⟨g12,g13⟩,g23⟩⟩⟩⟩⟩⟩⟩
  have src (i : Nat) (hi : i<4) (y cin co : Wire) (hy : y∈L.r)
      (hcin : cin=lowY L ∨ cin∈L.carry.take 255) (hco : co∈L.carry.take 255) :
      ∀q∈(source L i).wires,q∉[y,cin,co] := by
    intro q hq bad
    have aw := away q (source_site L i (by omega) q hq)
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false,not_or] at aw bad
    rcases bad with rfl|rfl|rfl
    · exact aw.2.1 hy
    · rcases hcin with rfl|h
      · exact aw.1 rfl
      · exact aw.2.2 h
    · exact aw.2.2 hco
  have valid (i : Nat) (hi : i<4) := sources_valid L hn _ (source_mem L i (by omega))
  have rm (i : Nat) (hi : i<4) : rAt L i∈L.r := by
    rw [hr]
    interval_cases i <;> simp [e0,e1,e2,e3]
  have cm (i : Nat) (hi : i<4) : cAt L i∈L.carry.take 255 := by
    rw [hc]
    interval_cases i <;> simp [f0,f1,f2,f3]
  have k0 := maj_keep (source L 0) (valid 0 (by decide)) (rAt L 0) (lowY L) (cAt L 0)
    (by rw [e0,f0];simp [Ne.symm u0,uc0,a0c0])
    (src 0 (by decide) _ _ _ (rm 0 (by decide)) (Or.inl rfl) (cm 0 (by decide)))
  have k1 := maj_keep (source L 1) (valid 1 (by decide)) (rAt L 1) (cAt L 0) (cAt L 1)
    (by rw [e1,f0,f1];simp [b1c0,b1c1,g01])
    (src 1 (by decide) _ _ _ (rm 1 (by decide)) (Or.inr (cm 0 (by decide))) (cm 1 (by decide)))
  have k2 := maj_keep (source L 2) (valid 2 (by decide)) (rAt L 2) (cAt L 1) (cAt L 2)
    (by rw [e2,f1,f2];simp [c2c1,c2c2,g12])
    (src 2 (by decide) _ _ _ (rm 2 (by decide)) (Or.inr (cm 1 (by decide))) (cm 2 (by decide)))
  have k3 := maj_keep (source L 3) (valid 3 (by decide)) (rAt L 3) (cAt L 2) (cAt L 3)
    (by rw [e3,f2,f3];simp [d2,d3,g23])
    (src 3 (by decide) _ _ _ (rm 3 (by decide)) (Or.inr (cm 2 (by decide))) (cm 3 (by decide)))
  have z (b : Affine.Bit) (y cin co : Wire) : measurementCount (Affine.majority b y cin co)=0 :=
    (Affine.bit_counts b y cin co).2.1
  simp only [pre4,run_append,measurementCount_append,z,Nat.add_zero,List.take_zero,List.drop_zero]
  refine ⟨?_,?_⟩
  · rw [(k3 _ _).1,(k2 _ _).1,(k1 _ _).1,(k0 _ _).1]
  · intro q h0 h1 h2 h3
    rw [(k3 _ _).2 q h3,(k2 _ _).2 q h2,(k1 _ _).2 q h1,(k0 _ _).2 q h0]

/-- Source bits 4..255 do not read `sign`. -/
theorem source_high_sites (L : Layout) (i : Nat) (hi : 4 ≤ i) :
    (source L i).wires⊆[L.parity,L.lower,L.one] := by
  intro q hq
  unfold source at hq
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)] at hq
  split_ifs at hq <;> simp_all [Affine.Bit.wires] <;> tauto

theorem inner_sites (L : Layout) (q : Wire) (hq : q∈Affine.sites ((sources L).drop 4)) :
    q∈[L.parity,L.lower,L.one] := by
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  simp only [sources,← List.map_drop,List.mem_map] at hb
  obtain ⟨i,hi,rfl⟩ := hb
  have : 4 ≤ i := by
    obtain ⟨n,hn,eq⟩ := List.getElem_of_mem hi
    rw [List.getElem_drop,List.getElem_range] at eq
    omega
  exact source_high_sites L i this hq

end ECDSAAdd.Entrant.JointInverse1588


/-! ### The hosted pieces run exactly like f2dcda16's pieces on reachable states -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

/-- `clearParity` never touches `one` or `sign`. -/
theorem clearParity_support (L : Layout) (hw : L.Widths) (J : Wire) :
    wires (clearParity L J)⊆(L.r++L.y++L.carry.take 255++[L.parity,L.lower,J]).toFinset := by
  let W := (L.r++L.y++L.carry.take 255++[L.parity,L.lower,J]).toFinset
  have data (q : Wire) (hq : q∈L.r++L.y++L.carry.take 255) : q∈W := by
    simp only [W,List.mem_toFinset,List.mem_append] at hq ⊢
    exact Or.inl hq
  have scalar (q : Wire) (hq : q∈[L.parity,L.lower,J]) : q∈W :=
    List.mem_toFinset.mpr (List.mem_append_right _ hq)
  have hp := scalar L.parity (by simp)
  have ha := scalar L.lower (by simp)
  have hj := scalar J (by simp)
  have r (q : Wire) (hq : q∈L.r) : q∈W := data q (by simp [hq])
  have y (q : Wire) (hq : q∈L.y) : q∈W := data q (by simp [hq])
  have c (q : Wire) (hq : q∈L.carry.take 255) : q∈W := data q (by simp [hq])
  have rh := r L.rmsb (by simp [BalancedCleanup.Layout.r])
  have yu : lowY L∈L.y := by rw [y_cons L hw]; simp
  have u := y (lowY L) yu
  have ul : L.ylow[0]?.getD 0∈W := u
  have len := BalancedCleanup.widths L.toLayout hw
  have comp (ctl : Wire) (hctl : ctl∈W) : wires (signComplement ctl L.r)⊆W := by
    intro q hq
    have h := signComplement_wires_subset ctl L.r hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with rfl|h
    · exact hctl
    · exact r q h
  have mag : wires (EntryHalf5.prepareMagnitude L)⊆W := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,wires_append,
      Finset.union_subset_iff]
    exact ⟨by simp [wires,Instr.wires,Finset.insert_subset_iff,rh,ha],comp _ ha⟩
  have carry : wires (EntryHalf5.parityCarry L J)⊆W := by
    apply (DiagonalCarry5.support EntryHalf5.parityBits L.low (L.carry.take 255) L.lower J L.parity
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|hq|hq
    · exact hj
    · exact hp
    · exact ha
    · exact r q (List.mem_append_left _ hq)
    · exact c q hq
  simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,
    wires_append,wires_reverse,Finset.union_subset_iff]
  refine ⟨?_,⟨⟨?_,⟨mag,⟨carry,mag⟩⟩⟩,?_⟩⟩
  · intro q hq
    have h : q=L.ylow.getD 0 0 ∨ q=L.parity := by
      simpa [wires,Instr.wires] using hq
    rcases h with rfl|rfl
    · exact u
    · exact hp
  · simp [wires,Instr.wires,Finset.insert_subset_iff,hj]
  · simp [wires,Instr.wires,Finset.insert_subset_iff,hj]

theorem clearParity_scalar_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (q : Wire) (hq : q=L.one ∨ q=L.sign) :
    q∉wires (clearParity L J) := by
  intro used
  have m := List.mem_toFinset.mp (clearParity_support L hw J used)
  have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
    rcases hq with rfl|rfl <;> simp
  have away := flagAway L hn q flag
  have sc := scalarND L hn
  have qj : q≠J := by
    intro e; apply hJ; rw [←e]
    rcases hq with rfl|rfl <;> simp [Layout.wires,BalancedCleanup.Layout.wires]
  have qp : q≠L.parity := by
    have h := List.nodup_iff_count.mp sc L.parity
    rcases hq with rfl|rfl <;> intro e <;> rw [e] at h <;> simp [List.count_cons] at h <;> omega
  have ql : q≠L.lower := by
    have h := List.nodup_iff_count.mp sc L.lower
    rcases hq with rfl|rfl <;> intro e <;> rw [e] at h <;> simp [List.count_cons] at h <;> omega
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with ((hr|hy)|hc)|rfl|rfl|rfl
  · exact away (by simp [hr])
  · exact away (by simp [hy])
  · exact away (by simp [List.mem_of_mem_take hc])
  · exact qp rfl
  · exact ql rfl
  · exact qj rfl


end ECDSAAdd.Entrant.JointInverse1588


/-! ### The hosted subtraction equals the original one on the restored-scalar state -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

theorem carry_nodup (L : Layout) (hn : L.wires.Nodup) : L.carry.Nodup :=
  (List.nodup_append'.mp (List.nodup_append'.mp (allND L hn)).2.1).2.1

theorem carry_index_ne (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (i j : Nat)
    (hi : i<256) (hj : j<256) (hij : i≠j) : L.carry.getD i 0≠L.carry.getD j 0 := by
  intro e
  have li : i<L.carry.length := by rw [hw.2.2];exact hi
  have lj : j<L.carry.length := by rw [hw.2.2];exact hj
  rw [List.getD_eq_getElem _ _ li,List.getD_eq_getElem _ _ lj] at e
  exact hij ((List.Nodup.getElem_inj_iff (carry_nodup L hn)).mp e)

theorem carry_not_r (L : Layout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈L.carry) : q∉L.r := by
  intro hr
  have nd := allND L hn
  have h := List.nodup_iff_count.mp nd q
  have a := List.count_pos_iff.mpr hr
  have b := List.count_pos_iff.mpr hq
  simp only [List.count_append] at h
  omega

theorem y_not_r (L : Layout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈L.y) : q∉L.r := by
  intro hr
  have nd := allND L hn
  have h := List.nodup_iff_count.mp nd q
  have a := List.count_pos_iff.mpr hr
  have b := List.count_pos_iff.mpr hq
  simp only [List.count_append] at h
  omega

theorem y_not_carry (L : Layout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈L.y) : q∉L.carry := by
  intro hc
  have nd := allND L hn
  have h := List.nodup_iff_count.mp nd q
  have a := List.count_pos_iff.mpr hc
  have b := List.count_pos_iff.mpr hq
  simp only [List.count_append] at h
  omega

/-- A wire away from the target register and the carries is kept by the four majorities. -/
theorem prefix_keep (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (b : State) (q : Wire)
    (hr : q∉L.r) (hc : ∀i,i<4 → q≠cAt L i) :
    (run (notRegister L.r++pre4 L) [] b).basis q=b.basis q ∧
      (run (notRegister L.r++pre4 L) [] b).phase=b.phase := by
  have nr := EntryHalf5.target_nodup L hn
  have mz := (notRegister_counts L.r).2
  rw [run_append,mz,List.take_zero,List.drop_zero,notRegister_correct L.r nr b []]
  have p := pre4_run L hw hn ⟨b.phase,fun w => if w∈L.r then !b.basis w else b.basis w⟩ []
  refine ⟨?_,p.1⟩
  rw [p.2 q (hc 0 (by decide)) (hc 1 (by decide)) (hc 2 (by decide)) (hc 3 (by decide))]
  simp [hr]

theorem inner_support (L : Layout) :
    wires (inner L)⊆(Affine.sites ((sources L).drop 4)++L.r.drop 4++
      (L.carry.take 255).drop 4++[cAt L 3]).toFinset :=
  Affine.add_support_to _ _ _ _ _ (fun q hq => by simp [hq]) (fun q hq => by simp [hq])
    (fun q hq => by simp [hq]) (by simp)

theorem inner_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (q : Wire)
    (hs : q∉[L.parity,L.lower,L.one]) (hr : q∉L.r) (hc : q∉L.carry) : q∉wires (inner L) := by
  intro used
  have m := List.mem_toFinset.mp (inner_support L used)
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with ((h|h)|h)|h
  · exact hs (inner_sites L q h)
  · exact hr (List.mem_of_mem_drop h)
  · exact hc (List.mem_of_mem_take (List.mem_of_mem_drop h))
  · exact hc (by rw [h];exact carry_mem L hw 3 (by decide))

/-- `Affine.add_correct` for the inner adder on any state with clean high carries. -/
theorem inner_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (x : State) (t : List Bool)
    (clean : ∀q∈(L.carry.take 255).drop 4,x.basis q=false) :
    (run (inner L) t x).phase=x.phase ∧
      ∀q,q∉L.r → (run (inner L) t x).basis q=x.basis q := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have nd := arithmeticND L hw hn
  have away := sources_away L hw hn
  have len := BalancedCleanup.widths L.toLayout hw
  have rl : L.r.length=256 := len.2.1
  rw [hr,hc] at nd
  have nd' : (c3::((r4::rt)++ct)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append] at h ⊢
    split_ifs at h ⊢ <;> omega
  have hd : (L.r.drop 4)=r4::rt := by rw [hr];rfl
  have cd : (L.carry.take 255).drop 4=ct := by rw [hc];rfl
  have s3 : cAt L 3=c3 := f3
  have res := Affine.add_correct ((sources L).drop 4) (r4::rt) ct c3 nd'
    (by
      intro q hq bad
      have aw := away q (List.mem_flatMap.mpr (by
        obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
        exact ⟨b,List.mem_of_mem_drop hb,hq⟩))
      rw [hr,hc] at aw
      apply aw
      simp only [List.mem_cons,List.mem_append] at bad ⊢
      rcases bad with rfl|(h|h)|h
      · simp
      · simp [h]
      · simp [h]
      · simp [h])
    (by
      have a : ((sources L).drop 4).length=252 := by simp [sources_length]
      have b : (r4::rt).length=252 := by
        have := congrArg List.length hr
        simp only [List.length_cons] at this ⊢
        omega
      rw [a,b])
    (by
      have b : (r4::rt).length=252 := by
        have := congrArg List.length hr
        simp only [List.length_cons] at this ⊢
        omega
      have c : ct.length=251 := by
        have := congrArg List.length hc
        simp only [List.length_cons,List.length_take,hw.2.2] at this
        omega
      rw [b,c])
    x t (by rw [←cd];exact clean)
    (fun b hb => sources_valid L hn b (List.mem_of_mem_drop hb))
  have shape : inner L=Affine.add ((sources L).drop 4) (r4::rt) ct c3 := by
    rw [inner,hd,cd,s3]
  rw [shape]
  refine ⟨res.1,fun q hq => res.2.1 q ?_⟩
  intro h
  apply hq
  rw [hr]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ h)))

/-- After the four leading majorities, carry #1 is the majority of source bit 1, `r1` and carry #0. -/
theorem pre4_c1 (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (s : State)
    (h1 : s.basis (cAt L 1)=false) :
    (run (pre4 L) [] s).basis (cAt L 1)=carryBit ((source L 1).value (run (pre4 L) [] s).basis)
      ((run (pre4 L) [] s).basis (rAt L 1)) ((run (pre4 L) [] s).basis (cAt L 0)) := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have nd := arithmeticND L hw hn
  have away := sources_away L hw hn
  rw [hr,hc] at nd
  have sub : [lowY L,L.r0,r1,r2,r3,c0,c1,c2,c3].Sublist
      (lowY L::(L.r0::r1::r2::r3::r4::rt++c0::c1::c2::c3::ct)) := by
    apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂
    apply List.Sublist.cons₂;apply List.Sublist.cons₂
    apply List.Sublist.cons
    apply List.sublist_append_of_sublist_right
    apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂
    exact List.nil_sublist _
  have nd9 := nd.sublist sub
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd9
  rcases nd9 with ⟨⟨u0,u1,u2,u3,uc0,uc1,uc2,uc3⟩,⟨⟨a1,a2,a3,a0c0,a0c1,a0c2,a0c3⟩,
    ⟨⟨b2,b3,b1c0,b1c1,b1c2,b1c3⟩,⟨⟨c23,c2c0,c2c1,c2c2,c2c3⟩,⟨⟨d0,d1,d2,d3⟩,
    ⟨⟨g01,g02,g03⟩,⟨⟨g12,g13⟩,g23⟩⟩⟩⟩⟩⟩⟩
  have src (i : Nat) (hi : i<4) (y cin co : Wire) (hy : y∈L.r)
      (hcin : cin=lowY L ∨ cin∈L.carry.take 255) (hco : co∈L.carry.take 255) :
      ∀q∈(source L i).wires,q∉[y,cin,co] := by
    intro q hq bad
    have aw := away q (source_site L i (by omega) q hq)
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false,not_or] at aw bad
    rcases bad with rfl|rfl|rfl
    · exact aw.2.1 hy
    · rcases hcin with rfl|h
      · exact aw.1 rfl
      · exact aw.2.2 h
    · exact aw.2.2 hco
  have valid (i : Nat) (hi : i<4) := sources_valid L hn _ (source_mem L i (by omega))
  have rm (i : Nat) (hi : i<4) : rAt L i∈L.r := by
    rw [hr]
    interval_cases i <;> simp [e0,e1,e2,e3]
  have cm (i : Nat) (hi : i<4) : cAt L i∈L.carry.take 255 := by
    rw [hc]
    interval_cases i <;> simp [f0,f1,f2,f3]
  have k0 := maj_keep (source L 0) (valid 0 (by decide)) (rAt L 0) (lowY L) (cAt L 0)
    (by rw [e0,f0];simp [Ne.symm u0,uc0,a0c0])
    (src 0 (by decide) _ _ _ (rm 0 (by decide)) (Or.inl rfl) (cm 0 (by decide)))
  have m1 := Affine.majority_correct (source L 1) (valid 1 (by decide)) (rAt L 1) (cAt L 0) (cAt L 1)
    (by rw [e1,f0,f1];simp [b1c0,b1c1,g01])
    (src 1 (by decide) _ _ _ (rm 1 (by decide)) (Or.inr (cm 0 (by decide))) (cm 1 (by decide)))
  have k2 := maj_keep (source L 2) (valid 2 (by decide)) (rAt L 2) (cAt L 1) (cAt L 2)
    (by rw [e2,f1,f2];simp [c2c1,c2c2,g12])
    (src 2 (by decide) _ _ _ (rm 2 (by decide)) (Or.inr (cm 1 (by decide))) (cm 2 (by decide)))
  have k3 := maj_keep (source L 3) (valid 3 (by decide)) (rAt L 3) (cAt L 2) (cAt L 3)
    (by rw [e3,f2,f3];simp [d2,d3,g23])
    (src 3 (by decide) _ _ _ (rm 3 (by decide)) (Or.inr (cm 2 (by decide))) (cm 3 (by decide)))
  have z (b : Affine.Bit) (y cin co : Wire) : measurementCount (Affine.majority b y cin co)=0 :=
    (Affine.bit_counts b y cin co).2.1
  -- wires of source bit 1 and the two read sites avoid carries #1..#3
  have sw (q : Wire) (hq : q∈(source L 1).wires) (i : Nat) (hi : i<4) : q≠cAt L i := by
    intro e
    have aw := away q (source_site L 1 (by decide) q hq)
    exact aw (by rw [e]; simp [cm i hi])
  have r1c (i : Nat) (h1 : 1 ≤ i) (h4 : i<4) : rAt L 1≠cAt L i := by
    rw [e1]
    interval_cases i
    · rw [f1];exact b1c1
    · rw [f2];exact b1c2
    · rw [f3];exact b1c3
  have c0c (i : Nat) (h1 : 1 ≤ i) (h4 : i<4) : cAt L 0≠cAt L i := by
    rw [f0]
    interval_cases i
    · rw [f1];exact g01
    · rw [f2];exact g02
    · rw [f3];exact g03
  have c1c (i : Nat) (h1 : 2 ≤ i) (h4 : i<4) : cAt L 1≠cAt L i := by
    rw [f1]
    interval_cases i
    · rw [f2];exact g12
    · rw [f3];exact g13
  have c10 : cAt L 1≠cAt L 0 := by rw [f0,f1];exact Ne.symm g01
  simp only [pre4,run_append,measurementCount_append,z,Nat.add_zero,List.take_zero,List.drop_zero,
    List.take_nil,List.drop_nil]
  generalize hs0 : run (Affine.majority (source L 0) (rAt L 0) (lowY L) (cAt L 0)) [] s=s0
  have s0c1 : s0.basis (cAt L 1)=false := by rw [←hs0,(k0 _ _).2 _ c10];exact h1
  rw [m1 s0 []]
  generalize hs1 : (⟨s0.phase,writeBit s0.basis (cAt L 1) (s0.basis (cAt L 1) ^^
    carryBit ((source L 1).value s0.basis) (s0.basis (rAt L 1)) (s0.basis (cAt L 0)))⟩ : State)=s1
  have k23 (q : Wire) (h2 : q≠cAt L 2) (h3 : q≠cAt L 3) :
      (run (Affine.majority (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)) []
        (run (Affine.majority (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)) [] s1)).basis q=s1.basis q := by
    rw [(k3 _ _).2 q h3,(k2 _ _).2 q h2]
  have s1keep (q : Wire) (hq : q≠cAt L 1) : s1.basis q=s0.basis q := by
    rw [←hs1];simp [writeBit,hq]
  have value : (source L 1).value (run (Affine.majority (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)) []
        (run (Affine.majority (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)) [] s1)).basis=
      (source L 1).value s0.basis := by
    apply Affine.Bit.value_congr
    intro q hq
    rw [k23 q (sw q hq 2 (by decide)) (sw q hq 3 (by decide)),s1keep q (sw q hq 1 (by decide))]
  rw [value,k23 _ (c1c 2 (by decide) (by decide)) (c1c 3 (by decide) (by decide)),
    k23 _ (r1c 2 (by decide) (by decide)) (r1c 3 (by decide) (by decide)),k23 _ (c0c 2 (by decide) (by decide)) (c0c 3 (by decide) (by decide)),
    s1keep _ (r1c 1 (by decide) (by decide)),s1keep _ (c0c 1 (by decide) (by decide)),←hs1]
  simp [writeBit,s0c1]

/-- The inner adder's carries are not among carries #0..#3. -/
theorem carry_drop4_ne (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈(L.carry.take 255).drop 4) (i : Nat) (hi : i<4) : q≠cAt L i := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hct,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have ndc : (L.carry.take 255).Nodup := (carry_nodup L hn).sublist (List.take_sublist _ _)
  rw [hct] at ndc hq
  simp only [List.drop_succ_cons,List.drop_zero] at hq
  simp only [List.nodup_cons,List.mem_cons,not_or] at ndc
  intro e
  interval_cases i
  · rw [f0] at e;exact ndc.1.2.2.2 (e ▸ hq)
  · rw [f1] at e;exact ndc.2.1.2.2 (e ▸ hq)
  · rw [f2] at e;exact ndc.2.2.1.2 (e ▸ hq)
  · rw [f3] at e;exact ndc.2.2.2.1 (e ▸ hq)

/-- The inner adder's targets are not among targets #0..#3. -/
theorem r_drop4_ne (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.r.drop 4) (i : Nat) (hi : i<4) : q≠rAt L i := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hct,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have ndr := EntryHalf5.target_nodup L hn
  rw [hr] at ndr hq
  simp only [List.drop_succ_cons,List.drop_zero,List.mem_cons] at hq
  simp only [List.nodup_cons,List.mem_cons,not_or] at ndr
  intro e
  interval_cases i
  · rw [e0] at e;subst e
    rcases hq with h|h
    · exact ndr.1.2.2.2.1 h
    · exact ndr.1.2.2.2.2 h
  · rw [e1] at e;subst e
    rcases hq with h|h
    · exact ndr.2.1.2.2.1 h
    · exact ndr.2.1.2.2.2 h
  · rw [e2] at e;subst e
    rcases hq with h|h
    · exact ndr.2.2.1.2.1 h
    · exact ndr.2.2.1.2.2 h
  · rw [e3] at e;subst e
    rcases hq with h|h
    · exact ndr.2.2.2.1.1 h
    · exact ndr.2.2.2.1.2 h

/-- Carries #0..#2 and the targets #0..#3 lie outside the inner adder. -/
theorem low_inner_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (∀i,i<3 → cAt L i∉wires (inner L)) ∧ (∀i,i<4 → rAt L i∉wires (inner L)) := by
  have flagsAway (q : Wire) (hq : q∈[L.parity,L.lower,L.one]) : q∉L.r++L.y++L.carry :=
    flagAway L hn q (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto)
  constructor
  · intro i hi used
    have m := List.mem_toFinset.mp (inner_support L used)
    have ci : cAt L i∈L.carry := carry_mem L hw i (by omega)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with ((h|h)|h)|h
    · exact flagsAway _ (inner_sites L _ h) (by simp [ci])
    · exact carry_not_r L hn _ ci (List.mem_of_mem_drop h)
    · exact carry_drop4_ne L hw hn _ h i (by omega) rfl
    · exact carry_index_ne L hw hn i 3 (by omega) (by decide) (by omega) h
  · intro i hi used
    have m := List.mem_toFinset.mp (inner_support L used)
    have ri : rAt L i∈L.r := by
      have len := BalancedCleanup.widths L.toLayout hw
      have lt : i<L.r.length := by rw [len.2.1];omega
      simp only [rAt,List.getD_eq_getElem _ _ lt]
      exact List.getElem_mem lt
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with ((h|h)|h)|h
    · exact flagsAway _ (inner_sites L _ h) (by simp [ri])
    · exact r_drop4_ne L hw hn _ h i hi rfl
    · exact carry_not_r L hn _ (List.mem_of_mem_take (List.mem_of_mem_drop h)) ri
    · exact carry_not_r L hn (cAt L 3) (carry_mem L hw 3 (by decide)) (by rw [←h];exact ri)

/-- A wire outside `P` and distinct from the two swapped sites stays outside the renamed `P`. -/
theorem swap_free (a b q : Wire) (P : Program) (hq : q∉wires P) (ha : q≠a) (hb : q≠b) :
    q∉wires (renameProgram (Equiv.swap a b) P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp used
  have back : x=Equiv.swap a b q := by rw [←ex];simp only [Equiv.swap_apply_self]
  rw [Equiv.swap_apply_of_ne_of_ne ha hb] at back
  exact hq (back ▸ hx)

/-- The image of a renamed program lies in any set containing the old support and both sites. -/
theorem swap_support (a b : Wire) (P : Program) (W : Finset Wire) (hP : wires P⊆W)
    (ha : a∈W) (hb : b∈W) : wires (renameProgram (Equiv.swap a b) P)⊆W := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  have hyW := hP hy
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

theorem loanC_counts (L : Layout) (J B : Wire) :
    toffoliCount (loanC L J B)=toffoliCount (inner L)+3 ∧
    measurementCount (loanC L J B)=3+measurementCount (inner L) := by
  have e := Affine.bit_counts (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
  have w := loanW_counts L.sign L.lower (lowY L) J B (cLo L) (cHi L)
    (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L))
  have r := renameProgram_counts (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)
  simp only [loanC,toffoliCount_append,measurementCount_append,e.1,e.2.1,e.2.2.1,e.2.2.2.1,
    w.1,w.2,r.1,r.2]
  omega

/-- On a state where `sign = lower∧lowY`, `lowY = J∧B` and every carry is clean, the carry-#1 loan
after `pre4` runs as the inner adder (it only reads three extra records). -/
theorem loanC_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (b : State) (r : List Bool)
    (he : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)))
    (hu : b.basis (lowY L)=(b.basis J && b.basis B))
    (hc : ∀q∈L.carry,b.basis q=false) :
    run (loanC L J B) r (run (pre4 L) [] b)=run (inner L) (r.drop 3) (run (pre4 L) [] b) := by
  generalize hx : run (pre4 L) [] b=x
  have dist := ports_distinct L hw hn J B hJ hB hJB
  have nd7 := dist.1
  have flags (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q∉L.r++L.y++L.carry := flagAway L hn q hq
  have notData (q : Wire) (hq : q∉L.wires) : q∉L.r++L.y++L.carry := fun bad => hq (data_member L q bad)
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have lowCarry (i : Nat) (hi : i<4) : cAt L i∈L.carry := carry_mem L hw i (by omega)
  have offData (q : Wire) (hq : q∉L.r++L.y++L.carry) : q∉L.r ∧ ∀i,i<4 → q≠cAt L i :=
    ⟨fun h => hq (by simp [h]),fun i hi e => hq (by rw [e];simp [lowCarry i hi])⟩
  have pk (q : Wire) (h4 : ∀i,i<4 → q≠cAt L i) : x.basis q=b.basis q := by
    rw [←hx]
    exact (pre4_run L hw hn b []).2 q (h4 0 (by decide)) (h4 1 (by decide)) (h4 2 (by decide))
      (h4 3 (by decide))
  have keepS := pk L.sign (offData _ (flags _ (by simp))).2
  have keepA := pk L.lower (offData _ (flags _ (by simp))).2
  have keepU := pk (lowY L) (fun i hi e => y_not_carry L hn _ y0 (by rw [e];exact lowCarry i hi))
  have keepJ := pk J (offData _ (notData _ hJ)).2
  have keepB := pk B (offData _ (notData _ hB)).2
  have hiIdx (k : Nat) (hk : 4≤k ∧ k<256) (i : Nat) (hi : i<4) : L.carry.getD k 0≠cAt L i :=
    carry_index_ne L hw hn k i (by omega) (by omega) (by omega)
  have keepLo := pk (cLo L) (hiIdx 4 (by decide))
  have keepHi := pk (cHi L) (hiIdx 254 (by decide))
  have keep248 := pk (cAt L 248) (hiIdx 248 (by decide))
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have cleanX : ∀q∈(L.carry.take 255).drop 4,x.basis q=false := fun q hq =>
    (pk q (carry_drop4_ne L hw hn q hq)).trans (hc q (List.mem_of_mem_take (List.mem_of_mem_drop hq)))
  -- carry #1 holds its majority: erase it
  have c1val : x.basis (cAt L 1)=carryBit ((source L 1).value x.basis) (x.basis (rAt L 1))
      (x.basis (cAt L 0)) := by
    rw [←hx];exact pre4_c1 L hw hn b (hc _ (lowCarry 1 (by decide)))
  have valid1 := sources_valid L hn _ (source_mem L 1 (by decide))
  have r1mem : rAt L 1∈L.r := by
    have len := BalancedCleanup.widths L.toLayout hw
    have lt : 1<L.r.length := by rw [len.2.1];decide
    simp only [rAt,List.getD_eq_getElem _ _ lt]
    exact List.getElem_mem lt
  have c10 : cAt L 1≠cAt L 0 := carry_index_ne L hw hn 1 0 (by decide) (by decide) (by decide)
  have loc : [rAt L 1,cAt L 0,cAt L 1].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
      not_false_eq_true,and_true]
    exact ⟨⟨fun e => carry_not_r L hn _ (lowCarry 0 (by decide)) (e ▸ r1mem),
      fun e => carry_not_r L hn _ (lowCarry 1 (by decide)) (e ▸ r1mem)⟩,Ne.symm c10⟩
  have srcAway (q : Wire) (hq : q∈(source L 1).wires) : q∉L.r++L.y++L.carry := by
    have m := source_sites L 1 hq
    exact flagAway L hn q (by simp only [List.mem_cons,List.not_mem_nil,or_false] at m ⊢;tauto)
  have locAway : ∀q∈(source L 1).wires,q∉[rAt L 1,cAt L 0,cAt L 1] := by
    intro q hq bad
    simp only [List.mem_cons,List.not_mem_nil,or_false] at bad
    rcases bad with rfl|rfl|rfl
    · exact srcAway _ hq (by simp [r1mem])
    · exact srcAway _ hq (by simp [lowCarry 0 (by decide)])
    · exact srcAway _ hq (by simp [lowCarry 1 (by decide)])
  have erase (t : List Bool) :
      run (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) t x=
        ⟨x.phase,writeBit x.basis (cAt L 1) false⟩ :=
    Affine.erase_correct _ valid1 _ _ _ loc locAway x t c1val
  generalize hx1 : (⟨x.phase,writeBit x.basis (cAt L 1) false⟩ : State)=x1 at erase
  have x1keep (q : Wire) (hq : q≠cAt L 1) : x1.basis q=x.basis q := by
    rw [←hx1];simp [writeBit,hq]
  have x1c1 : x1.basis (cAt L 1)=false := by rw [←hx1];simp [writeBit]
  have lf := low_inner_free L hw hn
  have c1In : cAt L 1∉wires (inner L) := lf.1 1 (by decide)
  have c248ne1 : cAt L 248≠cAt L 1 := carry_index_ne L hw hn 248 1 (by decide) (by decide) (by decide)
  have cleanX1 : ∀q∈(L.carry.take 255).drop 4,x1.basis q=false := fun q hq =>
    (x1keep q (carry_drop4_ne L hw hn q hq 1 (by decide))).trans (cleanX q hq)
  have inn (t : List Bool) := inner_correct L hw hn x1 t cleanX1
  -- the renamed inner adder runs as the inner adder on `x1`
  have host (t : List Bool) :
      run (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) t x1=run (inner L) t x1 := by
    apply rebind_swap_run
    · rw [x1keep _ c248ne1,keep248];exact hc _ m248
    · exact x1c1
    · rw [(inn t).2 _ (carry_not_r L hn _ m248),x1keep _ c248ne1,keep248];exact hc _ m248
    · rw [run_preserves_outside _ _ _ _ c1In];exact x1c1
  -- loanW on `x1`
  have uIn : lowY L∉wires (inner L) := inner_free L hw hn _ (fun h => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with e|e|e
      · exact flags L.parity (by simp) (by rw [←e];simp [y0])
      · exact flags L.lower (by simp) (by rw [←e];simp [y0])
      · exact flags L.one (by simp) (by rw [←e];simp [y0]))
      (y_not_r L hn _ y0) (y_not_carry L hn _ y0)
  have eIn : L.sign∉wires (inner L) := inner_free L hw hn _ (fun h => by
      have sc := scalarND L hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with e|e|e <;>
        (have c := List.nodup_iff_count.mp sc L.sign
         rw [e] at c;simp [List.count_cons] at c;omega))
      (offData _ (flags _ (by simp))).1 (fun h => flags L.sign (by simp) (by simp [h]))
  have uc (i : Nat) (hi : i<256) : lowY L≠L.carry.getD i 0 :=
    fun e => y_not_carry L hn _ y0 (by rw [e];exact carry_mem L hw i hi)
  have ec (i : Nat) (hi : i<256) : L.sign≠L.carry.getD i 0 :=
    fun e => flags L.sign (by simp) (by rw [e];exact List.mem_append_right _ (carry_mem L hw i hi))
  have loC : cLo L≠cAt L 1 := carry_index_ne L hw hn 4 1 (by decide) (by decide) (by decide)
  have hiC : cHi L≠cAt L 1 := carry_index_ne L hw hn 254 1 (by decide) (by decide) (by decide)
  have aC : L.lower≠cAt L 1 := fun e => flags L.lower (by simp)
    (by rw [e];exact List.mem_append_right _ (lowCarry 1 (by decide)))
  have jC : J≠cAt L 1 := fun e => notData J hJ (by rw [e];exact List.mem_append_right _ (lowCarry 1 (by decide)))
  have bC : B≠cAt L 1 := fun e => notData B hB (by rw [e];exact List.mem_append_right _ (lowCarry 1 (by decide)))
  have loan (t : List Bool) := loanW_run L.sign L.lower (lowY L) J B (cLo L) (cHi L)
    (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) x1 t nd7
    (by rw [x1keep _ (ec 1 (by decide)),x1keep _ aC,x1keep _ (uc 1 (by decide)),keepS,keepA,keepU];exact he)
    (by rw [x1keep _ (uc 1 (by decide)),x1keep _ jC,x1keep _ bC,keepU,keepJ,keepB];exact hu)
    (swap_free _ _ _ _ uIn (uc 248 (by decide)) (uc 1 (by decide)))
    (swap_free _ _ _ _ eIn (ec 248 (by decide)) (ec 1 (by decide)))
    (by
      intro t
      rw [host t]
      have i := (inn t).2
      exact ⟨i _ (offData _ (flags _ (by simp))).1,i _ (offData _ (notData _ hJ)).1,
        i _ (offData _ (notData _ hB)).1⟩)
    (by rw [x1keep _ loC,keepLo];exact hc _ (carry_mem L hw 4 (by decide)))
    (by rw [x1keep _ hiC,keepHi];exact hc _ (carry_mem L hw 254 (by decide)))
    (by
      intro t
      rw [host t,(inn t).2 (cLo L) (carry_not_r L hn _ (carry_mem L hw 4 (by decide))),x1keep _ loC,keepLo]
      exact hc _ (carry_mem L hw 4 (by decide)))
    (by
      intro t
      rw [host t,(inn t).2 (cHi L) (carry_not_r L hn _ (carry_mem L hw 254 (by decide))),x1keep _ hiC,keepHi]
      exact hc _ (carry_mem L hw 254 (by decide)))
  -- the inner adder on `x1` is the inner adder on `x` with carry #1 cleared
  have outside (t : List Bool) : run (inner L) t x1=
      ⟨(run (inner L) t x).phase,writeBit (run (inner L) t x).basis (cAt L 1) false⟩ := by
    rw [←hx1];exact G0CarryLoan5.run_write_outside (inner L) (cAt L 1) c1In x t false
  have innX (t : List Bool) := inner_correct L hw hn x t cleanX
  -- recompute carry #1
  have r1c1 : rAt L 1≠cAt L 1 := fun e => carry_not_r L hn _ (lowCarry 1 (by decide)) (e ▸ r1mem)
  have restore (t t' : List Bool) :
      run (Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) t' (run (inner L) t x1)=
        run (inner L) t x := by
    rw [outside t,Affine.majority_correct _ valid1 _ _ _ loc locAway]
    generalize hy : run (inner L) t x=y
    have yc1 : y.basis (cAt L 1)=x.basis (cAt L 1) := by
      rw [←hy];exact run_preserves_outside _ _ _ _ c1In
    have yr1 : y.basis (rAt L 1)=x.basis (rAt L 1) := by
      rw [←hy];exact run_preserves_outside _ _ _ _ (lf.2 1 (by decide))
    have yc0 : y.basis (cAt L 0)=x.basis (cAt L 0) := by
      rw [←hy];exact run_preserves_outside _ _ _ _ (lf.1 0 (by decide))
    have yv : (source L 1).value (Function.update y.basis (cAt L 1) false)=(source L 1).value x.basis := by
      apply Affine.Bit.value_congr
      intro q hq
      have qc1 : q≠cAt L 1 := fun e => locAway q hq (by simp [e])
      have qr : q∉L.r := fun h => srcAway q hq (by simp [h])
      rw [Function.update_of_ne qc1,←hy]
      exact (innX t).2 q qr
    apply State.extensionality
    · rfl
    · funext q
      by_cases qe : q=cAt L 1
      · subst qe
        simp only [writeBit,Function.update_self,Function.update_of_ne r1c1,Function.update_of_ne (Ne.symm c10),
          Bool.false_xor]
        rw [yv,yr1,yc0,←c1val,yc1]
      · simp [writeBit,qe]
  -- assemble
  have e1c : measurementCount (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))=1 :=
    (Affine.bit_counts (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)).2.2.2.1
  rw [loanC,run_append,e1c,erase,run_append,run_take,loan,host,restore]
  congr 1
  rw [List.drop_drop]


/-! ### Carry #248 on the cleared `rmsb` during the parity carry chain -/




theorem positiveParityH_counts (L : Layout) (ctl : Wire) :
    toffoliCount (positiveParityH L ctl)=toffoliCount (EntryHalf5.positiveParity L ctl) ∧
    measurementCount (positiveParityH L ctl)=measurementCount (EntryHalf5.positiveParity L ctl) := by
  have r := renameProgram_counts (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L ctl)
  simp only [positiveParityH,EntryHalf5.positiveParity,toffoliCount_append,measurementCount_append,r.1,r.2]
  exact ⟨trivial,trivial⟩

/-- `prepareMagnitude` leaves `rmsb` clean on a centered target word with clean `lower`. -/
theorem prepare_rmsb (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hz : s.basis L.lower=false) :
    (run (EntryHalf5.prepareMagnitude L) m s).basis L.rmsb=false := by
  have nd := (List.nodup_append'.mp hn).2.1
  have h := BalancedCleanup.prepareSign_value L.toLayout hw nd R hr s m hR hz
  let t := run (EntryHalf5.prepareMagnitude L) m s
  change regValue L.r t.basis=(magnitude R).toNat ∧ t.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → t.basis q=s.basis q) at h
  change t.basis L.rmsb=false
  have b := magnitude_bounds R hr
  have z := Int.toNat_of_nonneg b.1
  have c := constants
  have bound : (magnitude R).toNat<2^255 := by norm_num only [Nat.reducePow] at ⊢; omega
  have split : regValue L.r t.basis=regValue L.low t.basis+2^255*(t.basis L.rmsb).toNat := by
    rw [BalancedCleanup.Layout.r,regValue_append,(BalancedCleanup.widths L.toLayout hw).1]
    cases k : t.basis L.rmsb <;> simp [regValue,k]
  rw [h.1] at split
  cases k : t.basis L.rmsb
  · rfl
  · rw [k] at split
    simp only [Bool.toNat_true,Nat.mul_one] at split
    omega

theorem positiveParityH_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (ctl : Wire) (hctl : ctl∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (positiveParityH L ctl) m s=run (EntryHalf5.positiveParity L ctl) m s := by
  let c := run (EntryHalf5.prepareMagnitude L) [] s
  have pv := EntryHalf5.prepare_low_value L hw hn R hr s [] hR hz
  change regValue L.low c.basis=(magnitude R).toNat ∧ c.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → c.basis q=s.basis q) at pv
  have rz : c.basis L.rmsb=false := prepare_rmsb L hw hn R hr s [] hR hz
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have notLower (a : Wire) (ha : a∈L.carry) : a≠L.lower := fun e =>
    flagAway L hn L.lower (by simp) (by rw [←e];exact List.mem_append_right _ ha)
  have c248 : c.basis (cAt L 248)=false :=
    (pv.2.2 _ (carry_not_r L hn _ m248) (notLower _ m248)).trans (hc _ m248)
  have nd := EntryHalf5.carry_nodup L hn ctl hctl
  have clean : ∀a∈L.carry.take 255,c.basis a=false := by
    intro a ha
    have am := List.mem_of_mem_take ha
    exact (pv.2.2 a (carry_not_r L hn a am) (notLower a am)).trans (hc a am)
  have len := BalancedCleanup.widths L.toLayout hw
  have one (t : List Bool) := DiagonalCarry5.correct EntryHalf5.parityBits L.low (L.carry.take 255)
    L.lower ctl L.parity nd
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2]) c t clean
  have pc : cAt L 248≠L.parity := fun e =>
    flagAway L hn L.parity (by simp) (by rw [←e];exact List.mem_append_right _ m248)
  have rmem : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have pr : L.rmsb≠L.parity := fun e =>
    flagAway L hn L.parity (by simp) (by rw [←e];simp [rmem])
  have host (t : List Bool) :
      run (renameProgram (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L ctl)) t c=
        run (EntryHalf5.parityCarry L ctl) t c := by
    apply rebind_swap_run _ _ _ c t c248 rz
    · exact ((one t).2.1 _ pc).trans c248
    · exact ((one t).2.1 _ pr).trans rz
  have pm := (EntryHalf5.prepare_counts L).2
  have rc := renameProgram_counts (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L ctl)
  rw [positiveParityH,EntryHalf5.positiveParity,run_append,run_append (EntryHalf5.prepareMagnitude L),
    pm,List.take_zero,List.drop_zero,run_append,run_append (EntryHalf5.parityCarry L ctl),rc.2,host]

theorem recoverParityH_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (recoverParityH L J) m s=run (EntryHalf5.recoverParity L J) m s := by
  let u : State := ⟨s.phase,writeBit s.basis J (!s.basis J)⟩
  have away (q : Wire) (hq : q∈L.wires) : q≠J := fun e => hJ (e ▸ hq)
  have same (q : Wire) (hq : q∈L.wires) : u.basis q=s.basis q := by
    simp only [u,writeBit,Function.update_of_ne (away q hq)]
  have sameR : regValue L.r u.basis=encodeWord 256 R :=
    (regValue_congr _ _ _ (fun q hq => same q (by
      simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
        BalancedCleanup.Layout.low,List.mem_append,List.mem_cons,List.mem_singleton] at hq ⊢
      tauto))).trans hR
  have uz : u.basis L.lower=false := by
    rw [same _ (by simp [Layout.wires,BalancedCleanup.Layout.wires])];exact hz
  have uc : ∀q∈L.carry,u.basis q=false := fun q hq =>
    (same q (by simp [Layout.wires,BalancedCleanup.Layout.wires,hq])).trans (hc q hq)
  have first : run [.X J] [] s=u := by simp [u,run,writeBit]
  have cnt := (positiveParityH_counts L J).2
  have e := context_eq [.X J] (EntryHalf5.positiveParity L J) (positiveParityH L J) [.X J] 0 s m rfl
    (by rw [cnt,Nat.zero_add])
    (by
      intro r
      rw [first,List.drop_zero]
      exact positiveParityH_eq L hw hn J hJ R hr u r sameR uz uc)
  rw [recoverParityH,EntryHalf5.recoverParity,e,List.drop_zero,cnt,List.take_append_drop]

theorem clearParityH_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (clearParityH L J) m s=run (clearParity L J) m s := by
  let u : State := ⟨s.phase,writeBit s.basis L.parity (s.basis L.parity ^^ s.basis (L.ylow.getD 0 0))⟩
  have pa := flagAway L hn L.parity (by simp)
  have away (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity := fun e => pa (e ▸ hq)
  have lp : L.lower≠L.parity := by
    have nd := List.nodup_iff_count.mp (scalarND L hn) L.lower
    intro e;simp [e,List.count_cons] at nd;omega
  have ur : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hR
    intro q hq
    simp [u,writeBit,away q (by simp [hq])]
  have uz : u.basis L.lower=false := by simpa [u,writeBit,lp] using hz
  have uc : ∀q∈L.carry,u.basis q=false := fun q hq => by
    simpa [u,writeBit,away q (by simp [hq])] using hc q hq
  have first : run [.CX (L.ylow.getD 0 0) L.parity] [] s=u := by simp [run,u]
  rw [clearParityH,clearParity,run_append,run_append,
    show measurementCount [Instr.CX (L.ylow.getD 0 0) L.parity]=0 from rfl,List.take_zero,List.drop_zero,first]
  exact recoverParityH_eq L hw hn J hJ R hr u m ur uz uc


theorem clearH_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J : Wire) (hJ : J∉L.wires)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) (ho : s.basis L.one=false) (hs : s.basis L.sign=false) :
    run (clearH L J) m s=run (clearParity L J) m s := by
  have dist := hosts_distinct L hw hn
  have lo : cLo L∈L.carry := carry_mem L hw 4 (by decide)
  have hi : cHi L∈L.carry := carry_mem L hw 254 (by decide)
  have base := clearParityH_eq L hw hn J hJ R hr s m hR hl hc
  have cx := clear_xor L hw hn J hJ R hr s m hR hl hc
  have same (q : Wire) (hq : q≠L.parity) : (run (clearParityH L J) m s).basis q=s.basis q := by
    rw [base,cx]; simp [writeBit,hq]
  have innerEq : run (renameProgram (Equiv.swap (cLo L) L.one) (clearParityH L J)) m s=
      run (clearParityH L J) m s :=
    rebind_swap_run _ _ _ s m (hc _ lo) ho
      ((same _ (Ne.symm dist.2.2.1)).trans (hc _ lo))
      ((same _ (Ne.symm dist.2.2.2.2.2.2.1)).trans ho)
  rw [clearH,rebind_swap_run _ _ _ s m (hc _ hi) hs
    (by rw [innerEq];exact (same _ (Ne.symm dist.2.2.2.1)).trans (hc _ hi))
    (by rw [innerEq];exact (same _ (Ne.symm dist.2.2.2.2.2.2.2)).trans hs),innerEq,base]


theorem affineH_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (b : State) (m : List Bool)
    (he : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)))
    (hu : b.basis (lowY L)=(b.basis J && b.basis B))
    (hc : ∀q∈L.carry,b.basis q=false) :
    ∃m',run (affineH L J B) m b=run (affineSub (sources L) L.r (L.carry.take 255) (lowY L)) m' b := by
  let Pre := notRegister L.r++pre4 L
  let Post := post4 L++notRegister L.r
  let Q := loanC L J B
  have shapeS : affineSub (sources L) L.r (L.carry.take 255) (lowY L)=Pre++inner L++Post := by
    simp only [affineSub,add_split L hw,Pre,Post,List.append_assoc]
  have shapeH : affineH L J B=Pre++Q++Post := by
    simp only [affineH,Pre,Post,Q,List.append_assoc]
  refine ⟨(m.drop 3).take (measurementCount (inner L))++m.drop (measurementCount Q),?_⟩
  rw [shapeH,shapeS]
  apply context_eq Pre (inner L) Q Post 3 b m
  · simp only [Pre,measurementCount_append,(notRegister_counts _).2,(pre4_counts L).2]
  · exact (loanC_counts L J B).2
  · intro r
    have pre : run Pre [] b=run (pre4 L) [] (run (notRegister L.r) [] b) := by
      simp only [Pre,run_append,(notRegister_counts L.r).2,List.take_zero,List.drop_zero,List.take_nil,
        List.drop_nil]
    rw [pre]
    have nr := EntryHalf5.target_nodup L hn
    have keep (q : Wire) (hq : q∉L.r) : (run (notRegister L.r) [] b).basis q=b.basis q := by
      rw [notRegister_correct L.r nr b []]; simp [hq]
    have flags (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
        q∉L.r++L.y++L.carry := flagAway L hn q hq
    have notData (q : Wire) (hq : q∉L.wires) : q∉L.r++L.y++L.carry := fun bad => hq (data_member L q bad)
    have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
    have sR : L.sign∉L.r := fun h => flags L.sign (by simp) (by simp [h])
    have aR : L.lower∉L.r := fun h => flags L.lower (by simp) (by simp [h])
    have uR : lowY L∉L.r := y_not_r L hn _ y0
    have jR : J∉L.r := fun h => notData J hJ (by simp [h])
    have bR : B∉L.r := fun h => notData B hB (by simp [h])
    apply loanC_run L hw hn J B hJ hB hJB _ r
    · rw [keep _ sR,keep _ aR,keep _ uR];exact he
    · rw [keep _ uR,keep _ jR,keep _ bR];exact hu
    · intro q hq;rw [keep q (carry_not_r L hn q hq)];exact hc q hq

end ECDSAAdd.Entrant.JointInverse1588


/-! ### The hosted joint inverse: f2dcda16's frame, unchanged -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Secp256k1
attribute [local irreducible] run

theorem inverseH_forward (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    run (programH L J B) m (run (EntryRetained5.program L J B) [] s)=s := by
  let a:=run (prepare L J B) [] s
  let b:=run (arithmetic L) [] a
  let c:=run (eraseScalarsAt L J B) [] b
  have prep:=prepare_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  change Prepared L J B Jv Bv Y s a at prep
  have pref:=prefix_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  have prefix_run : run (prefixProgram L J B) [] s=b := by
    simp only [prefixProgram,run_append,List.take_nil,List.drop_nil]
    rfl
  rw [prefix_run] at pref
  have dd : b.basis L.one=(b.basis L.parity && b.basis (lowY L)) := by
    rw [pref.parity,pref.u]
    exact pref.d
  have ee : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)) := by
    rw [pref.a,pref.u]
    exact pref.e
  have uu : b.basis (lowY L)=(b.basis J && b.basis B) := by rw [pref.u,pref.j,pref.b]
  have aa:=scalar_erase_relation L hw Jv Bv Y hy b.basis pref.target pref.parity pref.a pref.d
  have erased:=eraseScalarsAt_run L hw hn J B hJ hB hJB b [] ee aa dd uu
  change c=⟨b.phase,erasedBasis L.parity L.lower L.one L.sign (lowY L) J b.basis⟩ at erased
  have en:=erasePorts_nodup L hw hn J B hJ hB hJB
  have restore:=restoreScalars_inverse L.parity L.lower L.one L.sign (lowY L) J B L.rmsb en b
  have undoRestore (n : List Bool) : run (restoreAt L J B) n c=b := by
    rw [erased]
    exact restore n ee aa dd uu
  have nd:=allND L hn
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have data : (L.r++L.y++L.carry).Nodup := (List.nodup_append'.mp nd).2.1
  have ry : (L.r++L.y).Nodup := (List.nodup_append'.mp data).1
  have rdy := (List.nodup_append'.mp ry).2.2
  have dyc := (List.nodup_append'.mp data).2.2
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r++L.y++L.carry := by
    have mem : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢
      tauto
    exact flagAway L hn q mem
  have cSame (q : Wire) (hq : q∈L.r++L.carry) : c.basis q=b.basis q := by
    have qdata : q∈L.r++L.y++L.carry := by
      simp only [List.mem_append] at hq ⊢
      tauto
    have qu : q≠lowY L := by
      intro eq
      rcases List.mem_append.mp hq with qr|qc
      · exact List.disjoint_left.mp rdy qr (eq.symm ▸ y0)
      · exact List.disjoint_left.mp dyc (List.mem_append_right _ y0) (eq ▸ qc)
    have qf (f : Wire) (hf : f∈[L.parity,L.lower,L.one,L.sign]) : q≠f := fun e=>flag f hf (e ▸ qdata)
    rw [erased]
    exact erasedBasis_frame _ _ _ _ _ _ _ q (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      exact not_or_intro (qf _ (by simp)) (not_or_intro (qf _ (by simp))
        (not_or_intro (qf _ (by simp)) qu)))
  have cR : regValue L.r c.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) :=
    (regValue_congr _ _ _ (fun q hq=>cSame q (List.mem_append_left _ hq))).trans pref.target
  have cCarry : ∀q∈L.carry,c.basis q=false := fun q hq=>
    (cSame q (List.mem_append_right _ hq)).trans (pref.carry q hq)
  have ca : c.basis L.lower=false := by
    have ne : L.lower≠lowY L := by
      intro e;exact flag L.lower (by simp) (by simp [e,y0])
    have ad : L.lower≠L.one := by
      have h:=List.nodup_iff_count.mp en L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,ne,ad]
  have bounds:=signedY_bounds (Jv && Bv) Y hy
  have rc : Centered (halfResult (signedY (Jv && Bv) Y)) := by
    apply (halfResult_spec _ ?_).1
    have hp:=constants
    unfold Centered at bounds
    omega
  have undoClear (n : List Bool) :
      run (clearParity L J) n (run (clearParity L J) [] c)=c :=
    clear_involution L hw hn J hJ _ rc c [] n cR ca cCarry
  have undoAdd (n : List Bool) :
      run (affineSub (sources L) L.r (L.carry.take 255) (lowY L)) n b=a := by
    exact affineSub_inverse _ _ _ _ (arithmeticND L hw hn) (sources_away L hw hn)
      (by rw [sources_length,(BalancedCleanup.widths L.toLayout hw).2.1])
      (by simp [List.length_take,hw.2.2,(BalancedCleanup.widths L.toLayout hw).2.1]) a [] n
      (fun q hq=>prep.carry q (List.mem_of_mem_take hq)) (sources_valid L hn)
  have undoPrep (n : List Bool) : run (CleanInverse5.inverse (prepare L J B)) n a=s :=
    CleanInverse5.inverse_run _ _ (prepare_ready L hw hn J B hJ hB s hY hc hz) n
  have forward_run : run (EntryRetained5.program L J B) [] s=run (clearParity L J) [] c := by
    simp only [EntryRetained5.program,prefixProgram,run_append,List.take_nil,List.drop_nil]
    rfl
  have notU (q : Wire) (hq : q=L.one ∨ q=L.sign) : q≠lowY L := by
    intro e
    have f := flagAway L hn q (by rcases hq with rfl|rfl <;> simp)
    exact f (by rw [e];simp [y0])
  have cOne : c.basis L.one=false := by
    have ad : L.lower≠L.one := by
      have h:=List.nodup_iff_count.mp en L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,notU L.one (Or.inl rfl)]
  have cSign : c.basis L.sign=false := by
    have sa : L.sign≠L.lower := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    have sd : L.sign≠L.one := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,notU L.sign (Or.inr rfl),sa,sd]
  have undoClearH (n : List Bool) :
      run (clearH L J) n (run (clearParity L J) [] c)=c := by
    have cx := clear_xor L hw hn J hJ _ rc c [] cR ca cCarry
    have po : L.parity∉L.r := fun h => flag L.parity (by simp) (by simp [h])
    have keepC (q : Wire) (hq : q≠L.parity) : (run (clearParity L J) [] c).basis q=c.basis q := by
      rw [cx];simp [writeBit,hq]
    have dist := hosts_distinct L hw hn
    have sc := scalarND L hn
    have lp : L.lower≠L.parity := by
      have h:=List.nodup_iff_count.mp sc L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [clearH_eq L hw hn J hJ _ rc _ n
      ((regValue_congr _ _ _ (fun q hq => keepC q (fun e => po (e ▸ hq)))).trans cR)
      ((keepC _ lp).trans ca)
      (fun q hq => (keepC q (fun e => flag L.parity (by simp) (by rw [←e];simp [hq]))).trans (cCarry q hq))
      ((keepC _ (Ne.symm dist.2.2.2.2.2.2.1)).trans cOne)
      ((keepC _ (Ne.symm dist.2.2.2.2.2.2.2)).trans cSign)]
    exact undoClear n
  have undoAddH (n : List Bool) : run (affineH L J B) n b=a := by
    obtain ⟨m',h⟩ := affineH_eq L hw hn J B hJ hB hJB b n ee uu pref.carry
    rw [h]
    exact undoAdd m'
  rw [forward_run,programH]
  simp only [List.append_assoc,run_append,run_take]
  rw [undoClearH,undoRestore,undoAddH,undoPrep]

theorem inverseH_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hY : regValue L.y s.basis=encodeWord 256 (if Jv then Y else 0))
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    let out:=run (programH L J B) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis (encodeWord 256 Y) 0 out.basis := by
  let t : State:=⟨s.phase,putWord L.r (encodeWord 256 Y) (putWord L.y 0 s.basis)⟩
  have len:=BalancedCleanup.widths L.toLayout hw
  have nd:=allND L hn
  have nr:=EntryHalf5.target_nodup L hn
  have ny : L.y.Nodup := by
    exact (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).1).2.1
  have dis : List.Disjoint L.r L.y :=
    (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).1).2.2
  have outside (q : Wire) (qr : q∉L.r) (qy : q∉L.y) : t.basis q=s.basis q := by
    simp only [t,putWord_outside _ _ _ q qr,putWord_outside _ _ _ q qy]
  have tr : regValue L.r t.basis=encodeWord 256 Y :=
    putWord_value L.r nr _ (by rw [len.2.1];exact encodeWord_bound 256 Y) _
  have ty : regValue L.y t.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (putWord_value L.y ny 0 (Nat.two_pow_pos _) s.basis)
    intro q hq
    apply putWord_outside
    exact fun bad=>List.disjoint_left.mp dis bad hq
  have noData (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (data_member L q (by simp [bad]))
    · exact hq (data_member L q (by simp [bad]))
  have workAway (q : Wire) (hq : q∈work L) : q∉L.r ∧ q∉L.y := by
    have n:=List.nodup_iff_count.mp nd q
    have w:=List.count_pos_iff.mpr hq
    constructor <;> intro bad <;> have b:=List.count_pos_iff.mpr bad
    all_goals
      simp only [work,List.count_append,List.count_cons,List.count_nil] at w
      simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.y,BalancedCleanup.Layout.low,
        List.count_append,List.count_cons,List.count_nil] at n b
      omega
  have tc : ∀q∈work L,t.basis q=false := fun q hq=>
    (outside q (workAway q hq).1 (workAway q hq).2).trans (hc q hq)
  have signAway : L.sign∉L.r ∧ L.sign∉L.y := by
    have h:=flagAway L hn L.sign (by simp)
    exact ⟨fun a=>h (by simp [a]),fun a=>h (by simp [a])⟩
  have tz : t.basis L.sign=false := (outside _ signAway.1 signAway.2).trans hz
  have tj : t.basis J=Jv := (outside J (noData J hJ).1 (noData J hJ).2).trans hj
  have tb : t.basis B=Bv := (outside B (noData B hB).1 (noData B hB).2).trans hb
  have f:=EntryRetained5.program_frame L hw hn J B hJ hB hJB Jv Bv Y hy t [] tr ty tc tz tj tb
  have ss : PairFrame L.r L.y t.basis
      (encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) s.basis :=
    ⟨hR,hY,fun q qr qy=>(outside q qr qy).symm⟩
  have eq : run (EntryRetained5.program L J B) [] t=s := by
    apply State.extensionality
    · exact f.1
    · exact PairFrame.unique _ _ _ _ _ _ _ f.2 ss
  have inv:=inverseH_forward L hw hn J B hJ hB hJB Jv Bv Y hy t m tr ty tc tz tj tb
  rw [eq] at inv
  dsimp only
  rw [inv]
  exact ⟨rfl,tr,ty,outside⟩

end ECDSAAdd.Entrant.JointInverse1588

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Secp256k1

def jointH (L : BalancedCircuit.Layout) (J G : Wire) : Program :=
  [.X G] ++ programH L J G ++ [.X G]


private theorem outside_layoutH (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q ∉ L.wires) : q ∉ L.r ∧ q ∉ L.y ∧ q ∉ BalancedCircuit.work L := by
  have zero := List.count_eq_zero.mpr hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    List.count_append,List.count_cons,List.count_nil] at zero
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at pos
    omega
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at pos
    omega
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at pos
    omega

/-- Read the first sign directly from its history wire and restore that wire.
The two record lists of a later old/new comparison can be independent. -/
theorem jointH_frame (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J,G].Nodup)
    (Jv Gv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)))
    (hY : regValue L.y s.basis = encodeWord 256 (if Jv then Y else 0))
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false)
    (sign : s.basis L.sign=false) (j : s.basis J=Jv) (g : s.basis G=Gv) :
    let out := run (jointH L J G) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis
      (encodeWord 256 Y) 0 out.basis := by
  have apart : J≠G := fun eq => (List.nodup_cons.mp hJG).1 (List.mem_singleton.mpr eq)
  have away := outside_layoutH L G hG
  let a : State := ⟨s.phase,writeBit s.basis G (!s.basis G)⟩
  have head : run [Instr.X G] [] s=a := rfl
  have keep (q : Wire) (hq : q≠G) : a.basis q=s.basis q := by
    simp only [a,writeBit,Function.update_of_ne hq]
  have aR : regValue L.r a.basis=encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)) :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.1 (eq ▸ hq)))).trans hR
  have aY : regValue L.y a.basis=encodeWord 256 (if Jv then Y else 0) :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.2.1 (eq ▸ hq)))).trans hY
  have ac : ∀q∈BalancedCircuit.work L,a.basis q=false := by
    intro q hq
    exact (keep q (fun eq => away.2.2 (eq ▸ hq))).trans (clean q hq)
  have sign_mem : L.sign∈L.wires := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have sg : L.sign≠G := fun eq => hG (eq ▸ sign_mem)
  have aj : a.basis J=Jv := (keep J apart).trans j
  have ag : a.basis G= !Gv := by simp only [a,writeBit,Function.update_self,g]
  generalize ht : run (programH L J G)
    (m.take (measurementCount (programH L J G))) a=t
  have result := inverseH_frame L hw hn J G hJ hG hJG Jv (!Gv) Y hy a
    (m.take (measurementCount (programH L J G))) aR aY ac ((keep _ sg).trans sign) aj ag
  rw [ht] at result
  let v : State := ⟨t.phase,writeBit t.basis G (!t.basis G)⟩
  have shape : run (jointH L J G) m s=v := by
    have xm : measurementCount [Instr.X G]=0 := rfl
    simp only [jointH,run_append,measurementCount_append,xm,Nat.zero_add,
      List.take_zero,List.drop_zero,head,ht] <;> rfl
  dsimp only
  rw [shape]
  refine ⟨result.1,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.1
    intro q hq
    have qg : q≠G := fun eq => away.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.2.1
    intro q hq
    have qg : q≠G := fun eq => away.2.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · intro q hr hyq
    by_cases eq : q=G
    · subst q
      change (writeBit t.basis G (!t.basis G)) G=s.basis G
      simp only [writeBit,Function.update_self]
      rw [result.2.2.2 G away.1 away.2.1]
      simp only [a,writeBit,Function.update_self,Bool.not_not]
    · change (writeBit t.basis G (!t.basis G)) q=s.basis q
      rw [show (writeBit t.basis G (!t.basis G)) q=t.basis q by
        simp only [writeBit,Function.update_of_ne eq], result.2.2.2 q hr hyq,keep q eq]


theorem jointH_pair (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (origin : BasisState) (clean : ∀q∈work L,origin q=false) (sign : origin L.sign=false)
    (Z : Fp) :
    Triple (PairFrame L.r L.y origin
      (centerWord ((if origin J && !origin G then -Z else Z)/2))
      (centerWord (if origin J then Z else 0))) (jointH L J G)
      (PairFrame L.r L.y origin (centerWord Z) 0) := by
  have outside (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
  have sf:=flagAway L hn L.sign (by simp)
  have sa : L.sign∉L.r ∧ L.sign∉L.y :=
    ⟨fun bad=>sf (by simp [bad]),fun bad=>sf (by simp [bad])⟩
  intro s m h
  have hc : ∀q∈work L,s.basis q=false := fun q hq=>
    (h.2.2 q (work_no_data L hn q hq).1 (work_no_data L hn q hq).2).trans (clean q hq)
  have rr : regValue L.r s.basis=encodeWord 256
      (halfResult (signedY (origin J && !origin G) (centerFp Z))) := by
    rw [unary_half]
    exact h.1
  have yy : regValue L.y s.basis=encodeWord 256 (if origin J then centerFp Z else 0) := by
    rw [source_word]
    exact h.2.1
  have out:=jointH_frame L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m rr yy hc ((h.2.2 _ sa.1 sa.2).trans sign)
    (h.2.2 _ (outside J hJ).1 (outside J hJ).2) (h.2.2 _ (outside G hG).1 (outside G hG).2)
  exact ⟨out.1,out.2.1,out.2.2.1,fun q qr qy=>(out.2.2.2 q qr qy).trans (h.2.2 q qr qy)⟩


end ECDSAAdd.Entrant.JointInverse1588


/-! ### Exact syntax slots of the literal carry chain -/
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Challenge Baselines RecordedQuantum

/-- Exact syntax slots of a literal carry chain: three per bit, four more per set literal bit. -/
theorem chain_slots (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    gateSlots (DiagonalCarry5.chain bs xs cs cin ctl target)=3*bs.length+4*bs.count true+1 := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    simp [DiagonalCarry5.chain,ex,ec,gateSlots,instructionSlots]
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have r := ih xs cs c (by simpa using hx) (by simpa using hc)
        have cell : gateSlots (mappedMajority (DiagonalCarry5.bit b) x cin c)+
            gateSlots (mappedEraseCarry (DiagonalCarry5.bit b) x cin c)=3+4*(if b then 1 else 0) := by
          cases b <;> norm_num [DiagonalCarry5.bit,mappedMajority,mappedEraseCarry,gateSlots,instructionSlots]
        simp only [DiagonalCarry5.chain,gateSlots_append,List.length_cons,List.count_cons]
        cases b <;> simp at cell ⊢ <;> omega

theorem parityBits_count : EntryHalf5.parityBits.count true=7 := by decide

theorem parityCarry_slots (L : Layout) (hw : L.Widths) (J : Wire) :
    gateSlots (EntryHalf5.parityCarry L J)=794 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h := chain_slots EntryHalf5.parityBits L.low (L.carry.take 255) L.lower J L.parity
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
  rw [parityBits_count,EntryHalf5.parityBits,DiagonalCarry5.literal_length] at h
  exact h

end ECDSAAdd.Entrant.JointInverse1588

/-! ### Supports, physicality and slots of the carry-#1 loan and of the `rmsb`-hosted chain -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

/-- A renamed program avoids the first swapped site when the old program avoids the second. -/
theorem swap_free_left (a b : Wire) (P : Program) (hb : b∉wires P) :
    a∉wires (renameProgram (Equiv.swap a b) P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp used
  have back : x=b := by
    have h := congrArg (Equiv.swap a b) ex
    rwa [Equiv.swap_apply_self,Equiv.swap_apply_left] at h
  exact hb (back ▸ hx)

theorem prep_support (L : Layout) :
    wires (EntryHalf5.prepareMagnitude L)⊆(L.lower::L.r).toFinset := by
  intro q hq
  simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,wires_append,Finset.mem_union] at hq
  rcases hq with h|h
  · have e : q=L.rmsb ∨ q=L.lower := by simpa [wires,Instr.wires] using h
    rcases e with rfl|rfl
    · simp [BalancedCleanup.Layout.r]
    · simp
  · have h' := signComplement_wires_subset L.lower L.r h
    simpa only [List.mem_toFinset,List.mem_cons] using h'

theorem chain_support (L : Layout) (hw : L.Widths) (J : Wire) :
    wires (EntryHalf5.parityCarry L J)⊆(J::L.parity::L.lower::(L.low++L.carry.take 255)).toFinset := by
  have len := BalancedCleanup.widths L.toLayout hw
  exact DiagonalCarry5.support EntryHalf5.parityBits L.low (L.carry.take 255) L.lower J L.parity
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])

/-- The chain-hosted parity clear never touches `one`, `sign` or carry #248. -/
theorem clearParityH_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J : Wire) (hJ : J∉L.wires)
    (q : Wire) (hq : q=L.one ∨ q=L.sign ∨ q=cAt L 248) : q∉wires (clearParityH L J) := by
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have rmem : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have sc := scalarND L hn
  have qw : q∈L.wires := by
    rcases hq with rfl|rfl|rfl
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · exact data_member L _ (by simp [m248])
  have qJ : q≠J := fun e => hJ (e ▸ qw)
  have qr : q∉L.r := by
    rcases hq with rfl|rfl|rfl
    · exact fun h => flagAway L hn L.one (by simp) (by simp [h])
    · exact fun h => flagAway L hn L.sign (by simp) (by simp [h])
    · exact carry_not_r L hn _ m248
  have qu : q≠lowY L := by
    rcases hq with rfl|rfl|rfl
    · exact fun e => flagAway L hn L.one (by simp) (by rw [e];simp [y0])
    · exact fun e => flagAway L hn L.sign (by simp) (by rw [e];simp [y0])
    · exact fun e => y_not_carry L hn _ y0 (e ▸ m248)
  have qp : q≠L.parity := by
    rcases hq with rfl|rfl|rfl
    · intro e;have h := List.nodup_iff_count.mp sc L.parity;rw [←e] at h;simp [List.count_cons] at h;omega
    · intro e;have h := List.nodup_iff_count.mp sc L.parity;rw [←e] at h;simp [List.count_cons] at h;omega
    · exact fun e => flagAway L hn L.parity (by simp) (by rw [←e];exact List.mem_append_right _ m248)
  have ql : q≠L.lower := by
    rcases hq with rfl|rfl|rfl
    · intro e;have h := List.nodup_iff_count.mp sc L.lower;rw [←e] at h;simp [List.count_cons] at h;omega
    · intro e;have h := List.nodup_iff_count.mp sc L.lower;rw [←e] at h;simp [List.count_cons] at h;omega
    · exact fun e => flagAway L hn L.lower (by simp) (by rw [←e];exact List.mem_append_right _ m248)
  have prepF : q∉wires (EntryHalf5.prepareMagnitude L) := by
    intro used
    have m := List.mem_toFinset.mp (prep_support L used)
    simp only [List.mem_cons] at m
    rcases m with e|h
    · exact ql e
    · exact qr h
  have lowR (x : Wire) (hx : x∈L.low) : x∈L.r := by simp [BalancedCleanup.Layout.r,hx]
  have chainF : q∉wires (renameProgram (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L J)) := by
    rcases hq with rfl|rfl|rfl
    · apply swap_free _ _ _ _ _ (fun e => flagAway L hn L.one (by simp) (by rw [e];exact List.mem_append_right _ m248))
        (fun e => flagAway L hn L.one (by simp) (by rw [e];simp [rmem]))
      intro used
      have m := List.mem_toFinset.mp (chain_support L hw J used)
      simp only [List.mem_cons,List.mem_append] at m
      rcases m with e|e|e|h|h
      · exact qJ e
      · exact qp e
      · exact ql e
      · exact qr (lowR _ h)
      · exact flagAway L hn L.one (by simp) (List.mem_append_right _ (List.mem_of_mem_take h))
    · apply swap_free _ _ _ _ _ (fun e => flagAway L hn L.sign (by simp) (by rw [e];exact List.mem_append_right _ m248))
        (fun e => flagAway L hn L.sign (by simp) (by rw [e];simp [rmem]))
      intro used
      have m := List.mem_toFinset.mp (chain_support L hw J used)
      simp only [List.mem_cons,List.mem_append] at m
      rcases m with e|e|e|h|h
      · exact qJ e
      · exact qp e
      · exact ql e
      · exact qr (lowR _ h)
      · exact flagAway L hn L.sign (by simp) (List.mem_append_right _ (List.mem_of_mem_take h))
    · apply swap_free_left
      intro used
      have m := List.mem_toFinset.mp (chain_support L hw J used)
      have rw' : L.rmsb∈L.wires := data_member L _ (by simp [rmem])
      have nr := EntryHalf5.target_nodup L hn
      simp only [List.mem_cons,List.mem_append] at m
      rcases m with e|e|e|h|h
      · exact hJ (e ▸ rw')
      · exact flagAway L hn L.parity (by simp) (by rw [←e];simp [rmem])
      · exact flagAway L hn L.lower (by simp) (by rw [←e];simp [rmem])
      · simp only [BalancedCleanup.Layout.r] at nr
        exact (List.nodup_append'.mp nr).2.2 h (by simp)
      · exact carry_not_r L hn _ (List.mem_of_mem_take h) rmem
  simp only [clearParityH,recoverParityH,positiveParityH,wires_append,wires_reverse,Finset.mem_union,not_or]
  refine ⟨?_,⟨⟨?_,prepF,chainF,prepF⟩,?_⟩⟩
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,
      or_false,not_or]
    exact ⟨qu,qp⟩
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false]
    exact qJ
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false]
    exact qJ

theorem clearParityH_support (L : Layout) (J : Wire) (W : Finset Wire)
    (hP : wires (clearParity L J)⊆W) (h248 : cAt L 248∈W) (hr : L.rmsb∈W) :
    wires (clearParityH L J)⊆W := by
  simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,wires_append,wires_reverse,
    Finset.union_subset_iff] at hP
  simp only [clearParityH,recoverParityH,positiveParityH,wires_append,wires_reverse,Finset.union_subset_iff]
  exact ⟨hP.1,⟨⟨hP.2.1.1,hP.2.1.2.1,swap_support _ _ _ _ hP.2.1.2.2.1 h248 hr,hP.2.1.2.1⟩,hP.2.2⟩⟩

theorem clearParityH_physical (L : Layout) (J : Wire) (hP : GatePhysical (clearParity L J)) :
    GatePhysical (clearParityH L J) := by
  simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,gatePhysical_append] at hP
  simp only [clearParityH,recoverParityH,positiveParityH,gatePhysical_append]
  exact ⟨hP.1,⟨⟨hP.2.1.1,hP.2.1.2.1,gatePhysical_rename _ (Equiv.swap _ _).injective _ hP.2.1.2.2.1,
    hP.2.1.2.2.2⟩,hP.2.2⟩⟩

theorem clearParityH_counts (L : Layout) (hw : L.Widths) (J : Wire) :
    toffoliCount (clearParityH L J)=256 ∧ measurementCount (clearParityH L J)=255 := by
  have p := positiveParityH_counts L J
  have c := clearParity_counts L hw J
  simp only [clearParity,EntryHalf5.recoverParity,toffoliCount_append,measurementCount_append] at c
  simp only [clearParityH,recoverParityH,toffoliCount_append,measurementCount_append,p.1,p.2]
  exact c

theorem clearParityH_slots (L : Layout) (hw : L.Widths) (J : Wire) :
    gateSlots (clearParityH L J)=1311 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have mag : gateSlots (EntryHalf5.prepareMagnitude L)=257 := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,gateSlots_append,
      gateSlots_cons,gateSlots_nil,instructionSlots,signComplement_gateSlots,len.2.1]
  have ch := parityCarry_slots L hw J
  simp only [clearParityH,recoverParityH,positiveParityH,gateSlots_append,reverse_gateSlots,
    rename_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,mag,ch]

/-- The four extra carry-#1 instructions only touch source bit 1, `r1` and carries #0/#1. -/
theorem loanC_edge_support (L : Layout) :
    wires (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))⊆
      ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset ∧
    wires (Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))⊆
      ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset := by
  have b := Affine.local_support (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
    ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset
    (fun q hq => List.mem_toFinset.mpr (List.mem_append_left _ hq))
    (by simp) (by simp) (by simp)
  exact ⟨b.2.1,b.1⟩


theorem source1_sites (L : Layout) (q : Wire) (hq : q∈(source L 1).wires) : q=L.one ∨ q=L.sign := by
  simpa [source,Affine.Bit.wires] using hq


theorem loanC_slots (L : Layout) (J B : Wire) : gateSlots (loanC L J B)=gateSlots (inner L)+20 := by
  have a : gateSlots ([Instr.measureX L.sign [] [Correction.CZ L.lower (lowY L)],
      Instr.measureX (lowY L) [] [Correction.CZ J B]] : Program)=4 := rfl
  have b : gateSlots ([Instr.CCX J B (lowY L),Instr.CCX L.lower (lowY L) L.sign] : Program)=2 := rfl
  have ls := Affine.local_slots (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
  have t1 : (source L 1).terms.length=1 := by simp [source]
  simp only [loanC,loanW,gateSlots_append,rename_gateSlots,a,b,ls.1,ls.2.1,t1]
  omega


end ECDSAAdd.Entrant.JointInverse1588


/-! ### Resources of the hosted joint inverse -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Challenge Baselines RecordedQuantum
attribute [local irreducible] run

theorem inner_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (inner L)=251 ∧ measurementCount (inner L)=251 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h := Affine.add_counts ((sources L).drop 4) (L.r.drop 4) ((L.carry.take 255).drop 4) (cAt L 3)
    (by simp [sources_length,len.2.1]) (by simp [List.length_take,hw.2.2,len.2.1])
  simp only [List.length_drop,len.2.1] at h
  exact h

theorem programH_counts (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) :
    toffoliCount (programH L J B)=518 ∧ measurementCount (programH L J B)=773 := by
  let zero : State:=⟨false,fun _=>false⟩
  have ready:=prepare_ready L hw hn J B hJ hB zero
    ((regValue_zero _ _).mpr (by intro q hq;rfl)) (by intro q hq;rfl) rfl
  have k:=CleanInverse5.counts (prepare L J B) (CleanInverse5.ready_proper _ _ ready)
  have c:=clearParityH_counts L hw J
  have r:=restoreScalars_counts L.parity L.lower L.one L.sign (lowY L) J B L.rmsb
  have p:=prepare_counts L hw J B
  have i:=inner_counts L hw
  have w:=loanC_counts L J B
  have c1:=renameProgram_counts (Equiv.swap (cLo L) L.one) (clearParityH L J)
  have c2:=renameProgram_counts (Equiv.swap (cHi L) L.sign)
    (renameProgram (Equiv.swap (cLo L) L.one) (clearParityH L J))
  simp only [programH,clearH,restoreAt,affineH,toffoliCount_append,measurementCount_append,
    k.1,k.2,c.1,c.2,r.1,r.2,p.1,w.1,w.2,i.1,i.2,c1.1,c1.2,c2.1,c2.2,(pre4_counts L).1,(pre4_counts L).2,
    (post4_counts L).1,(post4_counts L).2,(notRegister_counts L.r).1,(notRegister_counts L.r).2]
  all_goals simp


theorem jointH_counts (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) :
    toffoliCount (jointH L J G)=518 ∧ measurementCount (jointH L J G)=773 := by
  have h:=programH_counts L hw hn J G hJ hG
  simpa only [jointH,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,Nat.zero_add,Nat.add_zero] using h


/-- Every wire of a two-swap renaming lies in the old support or is one of the two hosts. -/
theorem swap2_support (a b c d : Wire) (P : Program) (W : Finset Wire) (hP : wires P⊆W)
    (ha : a∈W) (hb : b∈W) (hc : c∈W) (hd : d∈W) :
    wires (renameProgram (Equiv.swap c d) (renameProgram (Equiv.swap a b) P))⊆W := by
  rw [renameProgram_support,renameProgram_support]
  intro q hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hyW := hP hy
  have inner : Equiv.swap a b y∈W := by
    rw [Equiv.swap_apply_def]
    split_ifs <;> assumption
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

/-- A two-swap renaming avoids `a` and `c` when `P` avoids the hosts `b` and `d`. -/
theorem swap2_free (a b c d : Wire) (P : Program) (hb : b∉wires P) (hd : d∉wires P)
    (hac : a≠c) (had : a≠d) (hdb : d≠b) (q : Wire) (hq : q=a ∨ q=c) :
    q∉wires (renameProgram (Equiv.swap c d) (renameProgram (Equiv.swap a b) P)) := by
  rw [renameProgram_support,renameProgram_support]
  intro used
  obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp used
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have back : y=Equiv.swap a b (Equiv.swap c d q) := by
    rw [←ex]
    simp only [Equiv.swap_apply_self]
  rcases hq with rfl|rfl
  · rw [Equiv.swap_apply_of_ne_of_ne hac had,Equiv.swap_apply_left] at back
    exact hb (back ▸ hy)
  · rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne (Ne.symm had) hdb] at back
    exact hd (back ▸ hy)

end ECDSAAdd.Entrant.JointInverse1588


/-! ### Support, physicality and syntax slots of the hosted joint inverse -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

/-- `prepare` reads no carry. -/
theorem prepare_support (L : Layout) (hw : L.Widths) (J B : Wire) :
    wires (prepare L J B)⊆(L.r++L.y++[L.parity,L.lower,L.one,L.sign,J,B]).toFinset := by
  let W := (L.r++L.y++[L.parity,L.lower,L.one,L.sign,J,B]).toFinset
  have scalar (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign,J,B]) : q∈W :=
    List.mem_toFinset.mpr (List.mem_append_right _ hq)
  have hp := scalar L.parity (by simp)
  have ha := scalar L.lower (by simp)
  have hd := scalar L.one (by simp)
  have he := scalar L.sign (by simp)
  have hj := scalar J (by simp)
  have hb := scalar B (by simp)
  have r (q : Wire) (hq : q∈L.r) : q∈W := by simp [W,hq]
  have y (q : Wire) (hq : q∈L.y) : q∈W := by simp [W,hq]
  have r0 := r L.r0 (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
  have rh := r L.rmsb (by simp [BalancedCleanup.Layout.r])
  have yu : lowY L∈L.y := by rw [y_cons L hw]; simp
  have u := y (lowY L) yu
  have len := BalancedCleanup.widths L.toLayout hw
  have idx : 254<L.r.length := by rw [len.2.1]; decide
  have ri := r (L.r.getD 254 0) (by rw [List.getD_eq_getElem _ _ idx]; exact List.getElem_mem _)
  have riAlt : L.r[254]?.getD 0∈W := ri
  have cp : wires (copyRegister (some J) L.r.tail L.y.tail)⊆W := by
    rw [copyRegister_wires _ _ _ (by simp [len.2.1,len.2.2.1])]
    split
    · exact Finset.empty_subset _
    · intro q hq
      simp only [List.mem_toFinset,List.mem_append,Option.toList_some,List.mem_singleton] at hq
      rcases hq with (rfl|hq)|hq
      · exact hj
      · exact r q (List.mem_of_mem_tail hq)
      · exact y q (List.mem_of_mem_tail hq)
  have rot : wires (rotateRight L.r)⊆W := by
    rw [(rotate_wires L.r).1,if_neg (by rw [len.2.1]; omega)]
    exact fun q hq => r q (List.mem_toFinset.mp hq)
  have comp (ctl : Wire) (hctl : ctl∈W) : wires (signComplement ctl L.r)⊆W := by
    intro q hq
    have h := signComplement_wires_subset ctl L.r hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with rfl|h
    · exact hctl
    · exact r q h
  have first : wires [Instr.CCX J B (lowY L)]⊆W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,hj,hb,u]
  have seeds : wires [Instr.CX L.r0 L.parity,Instr.CCX L.parity L.rmsb L.lower,
      Instr.CCX L.parity (lowY L) L.one,Instr.CCX L.lower (lowY L) L.sign,
      Instr.CX L.parity L.r0]⊆W := by
    simp [wires,Instr.wires,Finset.union_subset_iff,Finset.insert_subset_iff,r0,rh,hp,ha,hd,he,u]
  have extend : wires [Instr.CX (L.r.getD 254 0) L.rmsb]⊆W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,ri,riAlt,rh]
  simpa only [prepare,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro (And.intro (And.intro first cp) seeds) rot) extend) (comp _ u)

theorem pre4_post4_support (L : Layout) (hw : L.Widths) :
    wires (pre4 L)⊆wires (arithmetic L) ∧ wires (inner L)⊆wires (arithmetic L) ∧
      wires (post4 L)⊆wires (arithmetic L) := by
  have h : arithmetic L=pre4 L++inner L++post4 L := add_split L hw
  rw [h]
  simp only [wires_append]
  exact ⟨fun q hq => by simp [hq],fun q hq => by simp [hq],fun q hq => by simp [hq]⟩

theorem programH_support (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J B : Wire) :
    wires (programH L J B)⊆retSites L J B := by
  have old:=EntryRetained5.program_support L hw J B
  have parts : ((wires (prepare L J B)⊆retSites L J B ∧ wires (arithmetic L)⊆retSites L J B) ∧
      wires (eraseScalarsAt L J B)⊆retSites L J B) ∧ wires (clearParity L J)⊆retSites L J B := by
    simpa only [EntryRetained5.program,prefixProgram,wires_append,Finset.union_subset_iff] using old
  have r (q : Wire) (hq : q∈L.r) : q∈retSites L J B := by simp [retSites,hq]
  have y (q : Wire) (hq : q∈L.y) : q∈retSites L J B := by simp [retSites,hq]
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have rh : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have hp : L.parity∈retSites L J B := by simp [retSites]
  have ha : L.lower∈retSites L J B := by simp [retSites]
  have hd : L.one∈retSites L J B := by simp [retSites]
  have he : L.sign∈retSites L J B := by simp [retSites]
  have hj : J∈retSites L J B := by simp [retSites]
  have hb : B∈retSites L J B := by simp [retSites]
  have hu := y (lowY L) y0
  have carryIn (i : Nat) (hi : i<255) : L.carry.getD i 0∈retSites L J B := by
    have m := carry_take_mem L hw i hi
    simp only [retSites,List.mem_toFinset,List.mem_append]
    exact Or.inl (Or.inr m)
  have r1 : rAt L 1∈retSites L J B := by
    apply r
    have len := BalancedCleanup.widths L.toLayout hw
    have lt : 1<L.r.length := by rw [len.2.1];decide
    simp only [rAt,List.getD_eq_getElem _ _ lt]
    exact List.getElem_mem lt
  have erase : wires (restoreAt L J B)⊆retSites L J B := by
    intro q hq
    simp only [restoreAt,restoreScalars,wires,Instr.wires,correctionWires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    have hh:=r L.rmsb rh
    aesop
  have notr : wires (notRegister L.r)⊆retSites L J B := by
    rw [notRegister_wires]
    intro q hq
    exact r q (List.mem_toFinset.mp hq)
  have split := pre4_post4_support L hw
  have clearS : wires (clearH L J)⊆retSites L J B :=
    swap2_support _ _ _ _ _ _ (clearParityH_support L J _ parts.2 (carryIn 248 (by decide)) (r _ rh))
      (carryIn 4 (by decide)) hd (carryIn 254 (by decide)) he
  have edgeS : ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset⊆retSites L J B := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with h|rfl|rfl|rfl
    · rcases source1_sites L q h with rfl|rfl
      · exact hd
      · exact he
    · exact r1
    · exact carryIn 0 (by decide)
    · exact carryIn 1 (by decide)
  have es := loanC_edge_support L
  have loan : wires (loanC L J B)⊆retSites L J B := by
    simp only [loanC,loanW,wires_append,Finset.union_subset_iff]
    refine ⟨es.1.trans edgeS,⟨⟨?_,swap2_support _ _ _ _ _ _
      (swap_support _ _ _ _ (split.2.1.trans parts.1.1.2) (carryIn 248 (by decide)) (carryIn 1 (by decide)))
      (carryIn 4 (by decide)) hu (carryIn 254 (by decide)) he⟩,?_⟩,es.2.trans edgeS⟩
    · simp [wires,Instr.wires,correctionWires,Finset.insert_subset_iff,Finset.union_subset_iff,he,ha,hu,hj,hb]
    · simp [wires,Instr.wires,Finset.insert_subset_iff,Finset.union_subset_iff,he,ha,hu,hj,hb]
  have affine : wires (affineH L J B)⊆retSites L J B := by
    simp only [affineH,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨notr,split.1.trans parts.1.1.2⟩,loan⟩,split.2.2.trans parts.1.1.2⟩,notr⟩
  simp only [programH,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨clearS,erase⟩,affine⟩,(CleanInverse5.inverse_support _).trans parts.1.1.1⟩


theorem jointH_support (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J G : Wire) :
    wires (jointH L J G)⊆retSites L J G := by
  have g : G∈retSites L J G := by simp [retSites]
  have x : wires [Instr.X G]⊆retSites L J G := by
    intro q hq
    have : q=G := by simpa [wires,Instr.wires] using hq
    rw [this];exact g
  simp only [jointH,wires_append,Finset.union_subset_iff]
  exact ⟨⟨x,programH_support L hw hn J G⟩,x⟩

end ECDSAAdd.Entrant.JointInverse1588


/-! ### The hosted carries never appear; physicality and slots -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

theorem edge_support (L : Layout) :
    wires (pre4 L)⊆(Affine.sites (sources L)++[rAt L 0,rAt L 1,rAt L 2,rAt L 3,lowY L,
      cAt L 0,cAt L 1,cAt L 2,cAt L 3]).toFinset ∧
    wires (post4 L)⊆(Affine.sites (sources L)++[rAt L 0,rAt L 1,rAt L 2,rAt L 3,lowY L,
      cAt L 0,cAt L 1,cAt L 2,cAt L 3]).toFinset := by
  let W := (Affine.sites (sources L)++[rAt L 0,rAt L 1,rAt L 2,rAt L 3,lowY L,
      cAt L 0,cAt L 1,cAt L 2,cAt L 3]).toFinset
  have src (i : Nat) (hi : i<256) : ∀q∈(source L i).wires,q∈W := fun q hq =>
    List.mem_toFinset.mpr (List.mem_append_left _ (source_site L i hi q hq))
  have t (q : Wire) (hq : q∈[rAt L 0,rAt L 1,rAt L 2,rAt L 3,lowY L,cAt L 0,cAt L 1,cAt L 2,cAt L 3]) :
      q∈W := List.mem_toFinset.mpr (List.mem_append_right _ hq)
  have b0 := Affine.local_support (source L 0) (rAt L 0) (lowY L) (cAt L 0) W (src 0 (by decide))
    (t _ (by simp)) (t _ (by simp)) (t _ (by simp))
  have b1 := Affine.local_support (source L 1) (rAt L 1) (cAt L 0) (cAt L 1) W (src 1 (by decide))
    (t _ (by simp)) (t _ (by simp)) (t _ (by simp))
  have b2 := Affine.local_support (source L 2) (rAt L 2) (cAt L 1) (cAt L 2) W (src 2 (by decide))
    (t _ (by simp)) (t _ (by simp)) (t _ (by simp))
  have b3 := Affine.local_support (source L 3) (rAt L 3) (cAt L 2) (cAt L 3) W (src 3 (by decide))
    (t _ (by simp)) (t _ (by simp)) (t _ (by simp))
  constructor
  · simp only [pre4,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨b0.1,b1.1⟩,b2.1⟩,b3.1⟩
  · simp only [post4,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨b3.2.1,b3.2.2⟩,b2.2.1⟩,b2.2.2⟩,b1.2.1⟩,b1.2.2⟩,b0.2.1⟩,b0.2.2⟩

theorem programH_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (q : Wire) (hq : q=cLo L ∨ q=cHi L ∨ q=cAt L 248) : q∉wires (programH L J B) := by
  have dist := ports_distinct L hw hn J B hJ hB hJB
  have hd := hosts_distinct L hw hn
  have nd7 := dist.1
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd7
  rcases nd7 with ⟨⟨sl,su,sj,sb,slo,shi⟩,⟨⟨lu,lj,lb,llo,lhi⟩,⟨⟨uj,ub,ulo,uhi⟩,
    ⟨⟨jb,jlo,jhi⟩,⟨⟨blo,bhi⟩,lohi⟩⟩⟩⟩⟩
  have qc : q∈L.carry := by
    rcases hq with rfl|rfl|rfl
    · exact carry_mem L hw 4 (by decide)
    · exact carry_mem L hw 254 (by decide)
    · exact carry_mem L hw 248 (by decide)
  have qr : q∉L.r := carry_not_r L hn q qc
  have qy : q∉L.y := fun h => y_not_carry L hn q h qc
  have flagNe (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q≠f := fun e => flagAway L hn f hf (by rw [←e];simp [qc])
  have qJ : q≠J := fun e => hJ (e ▸ data_member L q (by simp [qc]))
  have qB : q≠B := fun e => hB (e ▸ data_member L q (by simp [qc]))
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have qu : q≠lowY L := fun e => qy (e ▸ y0)
  have qlow (i : Nat) (hi : i<4) : q≠cAt L i := by
    rcases hq with rfl|rfl|rfl
    · exact carry_index_ne L hw hn 4 i (by decide) (by omega) (by omega)
    · exact carry_index_ne L hw hn 254 i (by decide) (by omega) (by omega)
    · exact carry_index_ne L hw hn 248 i (by decide) (by omega) (by omega)
  have qsite (h : q∈Affine.sites (sources L)) : False := by
    have m := sources_sites L q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with e|e|e|e
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
  have rmem (i : Nat) (hi : i<4) : rAt L i∈L.r := by
    have len := BalancedCleanup.widths L.toLayout hw
    have lt : i<L.r.length := by rw [len.2.1];omega
    simp only [rAt,List.getD_eq_getElem _ _ lt]
    exact List.getElem_mem lt
  have edge (P : Program) (hP : wires P⊆(Affine.sites (sources L)++[rAt L 0,rAt L 1,rAt L 2,rAt L 3,
      lowY L,cAt L 0,cAt L 1,cAt L 2,cAt L 3]).toFinset) : q∉wires P := by
    intro used
    have m := List.mem_toFinset.mp (hP used)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with h|e|e|e|e|e|e|e|e|e
    · exact qsite h
    · exact qr (e ▸ rmem 0 (by decide))
    · exact qr (e ▸ rmem 1 (by decide))
    · exact qr (e ▸ rmem 2 (by decide))
    · exact qr (e ▸ rmem 3 (by decide))
    · exact qu e
    · exact qlow 0 (by decide) e
    · exact qlow 1 (by decide) e
    · exact qlow 2 (by decide) e
    · exact qlow 3 (by decide) e
  have es := edge_support L
  have c248lo : cAt L 248≠cLo L := carry_index_ne L hw hn 248 4 (by decide) (by decide) (by decide)
  have c248hi : cAt L 248≠cHi L := carry_index_ne L hw hn 248 254 (by decide) (by decide) (by decide)
  have clearF : q∉wires (clearH L J) := by
    rcases hq with h|h|h
    · exact swap2_free (cLo L) L.one (cHi L) L.sign (clearParityH L J)
        (clearParityH_free L hw hn J hJ L.one (Or.inl rfl))
        (clearParityH_free L hw hn J hJ L.sign (Or.inr (Or.inl rfl)))
        hd.2.2.2.2.2.1 (Ne.symm slo) (Ne.symm hd.2.2.2.2.1) q (Or.inl h)
    · exact swap2_free (cLo L) L.one (cHi L) L.sign (clearParityH L J)
        (clearParityH_free L hw hn J hJ L.one (Or.inl rfl))
        (clearParityH_free L hw hn J hJ L.sign (Or.inr (Or.inl rfl)))
        hd.2.2.2.2.2.1 (Ne.symm slo) (Ne.symm hd.2.2.2.2.1) q (Or.inr h)
    · rw [h] at flagNe
      rw [h]
      exact swap_free _ _ _ _ (swap_free _ _ _ _
        (clearParityH_free L hw hn J hJ _ (Or.inr (Or.inr rfl))) c248lo (flagNe L.one (by simp)))
        c248hi (flagNe L.sign (by simp))
  have restoreSub : wires (restoreAt L J B)⊆
      ([L.parity,L.lower,L.one,L.sign,lowY L,J,B,L.rmsb] : List Wire).toFinset := by
    intro x hx
    simp only [restoreAt,restoreScalars,wires,Instr.wires,correctionWires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hx
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  have rh : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have restoreF : q∉wires (restoreAt L J B) := by
    intro used
    have m := List.mem_toFinset.mp (restoreSub used)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with e|e|e|e|e|e|e|e
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
    · exact qu e
    · exact qJ e
    · exact qB e
    · exact qr (e ▸ rh)
  have notrF : q∉wires (notRegister L.r) := by
    rw [notRegister_wires]
    exact fun h => qr (List.mem_toFinset.mp h)
  have sc := scalarND L hn
  have uIn : lowY L∉wires (inner L) := inner_free L hw hn _ (fun h => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e
        · exact flagAway L hn L.parity (by simp) (by rw [←e];simp [y0])
        · exact flagAway L hn L.lower (by simp) (by rw [←e];simp [y0])
        · exact flagAway L hn L.one (by simp) (by rw [←e];simp [y0]))
        (y_not_r L hn _ y0) (y_not_carry L hn _ y0)
  have eIn : L.sign∉wires (inner L) := inner_free L hw hn _ (fun h => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e <;>
          (have c := List.nodup_iff_count.mp sc L.sign
           rw [e] at c;simp [List.count_cons] at c;omega))
        (fun h => flagAway L hn L.sign (by simp) (by simp [h]))
        (fun h => flagAway L hn L.sign (by simp) (by simp [h]))
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have m1 : cAt L 1∈L.carry := carry_mem L hw 1 (by decide)
  have uP : lowY L∉wires (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) :=
    swap_free _ _ _ _ uIn (fun e => y_not_carry L hn _ y0 (e ▸ m248)) (fun e => y_not_carry L hn _ y0 (e ▸ m1))
  have eP : L.sign∉wires (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) :=
    swap_free _ _ _ _ eIn (fun e => flagAway L hn L.sign (by simp) (by rw [e];exact List.mem_append_right _ m248))
      (fun e => flagAway L hn L.sign (by simp) (by rw [e];exact List.mem_append_right _ m1))
  have innerF : q∉wires (renameProgram (Equiv.swap (cHi L) L.sign)
      (renameProgram (Equiv.swap (cLo L) (lowY L))
        (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)))) := by
    rcases hq with h|h|h
    · exact swap2_free (cLo L) (lowY L) (cHi L) L.sign _ uP eP hd.2.2.2.2.2.1 (Ne.symm slo) su q (Or.inl h)
    · exact swap2_free (cLo L) (lowY L) (cHi L) L.sign _ uP eP hd.2.2.2.2.2.1 (Ne.symm slo) su q (Or.inr h)
    · rw [h] at flagNe qu
      rw [h]
      exact swap_free _ _ _ _ (swap_free _ _ _ _ (swap_free_left _ _ _ ((low_inner_free L hw hn).1 1 (by decide)))
        c248lo qu) c248hi (flagNe L.sign (by simp))
  have edgeSub : wires ([.measureX L.sign [] [.CZ L.lower (lowY L)],.measureX (lowY L) [] [.CZ J B]] : Program)∪
      wires ([.CCX J B (lowY L),.CCX L.lower (lowY L) L.sign] : Program)⊆
      ([L.sign,L.lower,lowY L,J,B] : List Wire).toFinset := by
    intro x hx
    simp only [wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false,Finset.union_empty] at hx
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  have edgeF : q∉([L.sign,L.lower,lowY L,J,B] : List Wire).toFinset := by
    intro h
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with e|e|e|e|e
    · exact flagNe L.sign (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact qu e
    · exact qJ e
    · exact qB e
  have ls := loanC_edge_support L
  have edge1 (P : Program) (hP : wires P⊆((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset) :
      q∉wires P := by
    intro used
    have m := List.mem_toFinset.mp (hP used)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with h|e|e|e
    · rcases source1_sites L q h with e|e
      · exact flagNe L.one (by simp) e
      · exact flagNe L.sign (by simp) e
    · exact qr (e ▸ rmem 1 (by decide))
    · exact qlow 0 (by decide) e
    · exact qlow 1 (by decide) e
  have loanF : q∉wires (loanC L J B) := by
    simp only [loanC,loanW,wires_append,Finset.mem_union,not_or]
    exact ⟨edge1 _ ls.1,⟨⟨fun h => edgeF (edgeSub (Finset.mem_union_left _ h)),innerF⟩,
      fun h => edgeF (edgeSub (Finset.mem_union_right _ h))⟩,edge1 _ ls.2⟩
  have prepF : q∉wires (CleanInverse5.inverse (prepare L J B)) := by
    intro used
    have m := List.mem_toFinset.mp (prepare_support L hw J B (CleanInverse5.inverse_support _ used))
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with (h|h)|e|e|e|e|e|e
    · exact qr h
    · exact qy h
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
    · exact qJ e
    · exact qB e
  simp only [programH,affineH,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨clearF,restoreF⟩,⟨⟨⟨⟨notrF,edge _ es.1⟩,loanF⟩,edge _ es.2⟩,notrF⟩⟩,prepF⟩


theorem jointH_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (q : Wire) (hq : q=cLo L ∨ q=cHi L ∨ q=cAt L 248) : q∉wires (jointH L J G) := by
  have core := programH_free L hw hn J G hJ hG hJG q hq
  have qc : q∈L.carry := by
    rcases hq with rfl|rfl|rfl
    · exact carry_mem L hw 4 (by decide)
    · exact carry_mem L hw 254 (by decide)
    · exact carry_mem L hw 248 (by decide)
  have qG : q≠G := fun e => hG (e ▸ data_member L q (by simp [qc]))
  simp only [jointH,wires_append,Finset.mem_union,not_or]
  refine ⟨⟨?_,core⟩,?_⟩ <;> simp [wires,Instr.wires,qG]


end ECDSAAdd.Entrant.JointInverse1588


/-! ### Physicality and syntax slots -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

theorem programH_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup) :
    GatePhysical (programH L J B) := by
  have old:=EntryRetained5.program_physical L hw hn J B hJ hB hJB
  have parts : ((GatePhysical (prepare L J B) ∧ GatePhysical (arithmetic L)) ∧
      GatePhysical (eraseScalarsAt L J B)) ∧ GatePhysical (clearParity L J) := by
    simpa only [EntryRetained5.program,prefixProgram,gatePhysical_append] using old
  have n:=erasePorts_nodup L hw hn J B hJ hB hJB
  have ctr : (lowY L)≠J ∧ L.parity≠L.lower ∧ (lowY L)≠L.one ∧ L.parity≠L.one ∧
      L.rmsb≠L.lower ∧ L.one≠L.lower ∧ L.lower≠L.sign ∧ (lowY L)≠L.sign ∧ J≠lowY L ∧ B≠lowY L := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at n
    rcases n with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
      ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
    exact ⟨uJ,pA,Ne.symm dU,pD,Ne.symm aH,Ne.symm aD,aE,Ne.symm eU,
      Ne.symm uJ,Ne.symm uB⟩
  have restore : GatePhysical (restoreAt L J B) := by
    simp [restoreAt,restoreScalars,GatePhysical,PhysicalInstr,ProperGate,ctr.1,ctr.2.1,
      ctr.2.2.1,ctr.2.2.2.1,ctr.2.2.2.2.1,ctr.2.2.2.2.2.1,
      ctr.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.2.2]
  have arith : GatePhysical (pre4 L) ∧ GatePhysical (inner L) ∧ GatePhysical (post4 L) := by
    have h := parts.1.1.2
    rw [show arithmetic L=pre4 L++inner L++post4 L from add_split L hw] at h
    simp only [gatePhysical_append] at h
    exact ⟨h.1.1,h.1.2,h.2⟩
  have clear : GatePhysical (clearH L J) :=
    gatePhysical_rename _ (Equiv.swap _ _).injective _
      (gatePhysical_rename _ (Equiv.swap _ _).injective _ (clearParityH_physical L J parts.2))
  have e1 : GatePhysical (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) := by
    have h := arith.2.2
    simp only [post4,gatePhysical_append] at h
    exact h.1.1.1.2
  have m1 : GatePhysical (Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) := by
    have h := arith.1
    simp only [pre4,gatePhysical_append] at h
    exact h.1.1.2
  have loan : GatePhysical (loanC L J B) := by
    simp only [loanC,loanW,gatePhysical_append]
    refine ⟨e1,⟨⟨?_,gatePhysical_rename _ (Equiv.swap _ _).injective _
      (gatePhysical_rename _ (Equiv.swap _ _).injective _
        (gatePhysical_rename _ (Equiv.swap _ _).injective _ arith.2.1))⟩,?_⟩,m1⟩
    · simp [GatePhysical,PhysicalInstr]
    · simp [GatePhysical,PhysicalInstr,ProperGate,ctr.2.2.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.2.2,
        ctr.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.1]
  have affine : GatePhysical (affineH L J B) := by
    simp only [affineH,gatePhysical_append]
    exact ⟨⟨⟨⟨notRegister_physical _,arith.1⟩,loan⟩,arith.2.2⟩,notRegister_physical _⟩
  simp only [programH,gatePhysical_append]
  exact ⟨⟨⟨clear,restore⟩,affine⟩,CleanInverse5.inverse_physical _ parts.1.1.1⟩


theorem jointH_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup) :
    GatePhysical (jointH L J G) := by
  have core := programH_physical L hw hn J G hJ hG hJG
  have x : GatePhysical [Instr.X G] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  simp only [jointH,gatePhysical_append]
  exact ⟨⟨x,core⟩,x⟩

theorem programH_slots (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) : gateSlots (programH L J B)≤10006 := by
  let zero : State:=⟨false,fun _=>false⟩
  have ready:=prepare_ready L hw hn J B hJ hB zero
    ((regValue_zero _ _).mpr (by intro q hq;rfl)) (by intro q hq;rfl) rfl
  have inv:=CleanInverse5.inverse_slots _ (CleanInverse5.ready_proper _ _ ready)
  have prep:=prepare_slots_le L hw J B
  have arith:=arithmetic_slots L hw
  have par:=clearParityH_slots L hw J
  have pc:=prepare_counts L hw J B
  have xr:=notRegister_gateSlots L.r
  have len:=BalancedCleanup.widths L.toLayout hw
  have rest : gateSlots (restoreAt L J B)=8 := rfl
  have split : gateSlots (pre4 L)+gateSlots (inner L)+gateSlots (post4 L)=4369 := by
    rw [←arith,show arithmetic L=pre4 L++inner L++post4 L from add_split L hw]
    simp only [gateSlots_append]
  have loanS := loanC_slots L J B
  simp only [programH,clearH,affineH,gateSlots_append,rename_gateSlots,xr,len.2.1,rest,loanS,par]
  omega


theorem jointH_slots (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) : gateSlots (jointH L J G)≤10008 := by
  have h := programH_slots L hw hn J G hJ hG
  have x : gateSlots [Instr.X G]=1 := rfl
  simp only [jointH,gateSlots_append,x]
  omega

end ECDSAAdd.Entrant.JointInverse1588


/-! ## The S2 first-packet kernel in the record's 1,588 layout -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum
  EntryRetained5 FirstInverse5 Challenge Baselines
attribute [local irreducible] wires

/-- The record's half-kernel ports (f2dcda16's `loanPorts1592`). -/
def portsJ : BalancedCircuit.Layout := Q6EndpointCell.ports base (base 2409)

theorem portsJ_eq : portsJ=Q6EndpointCell.ports base (base 2409) := rfl

theorem portsJ_widths : portsJ.Widths := by rw [portsJ_eq];exact Q6EndpointCell.ports_widths base (base 2409)

theorem portsJ_nodup : portsJ.wires.Nodup := by
  rw [portsJ_eq]
  exact Q6EndpointCell.ports_nodup_injective base (base 2409) base_injective (by
    intro member
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp member
    have same := base_injective eq
    have bound := Q6EndpointCell.ids_bound i hi
    omega)

theorem portsJ_outside (i : Nat) (hi : i=1028 ∨ i=1 ∨ i=1032 ∨ i=0) : base i∉portsJ.wires := by
  simp only [portsJ,Q6EndpointCell.ports,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    wireBlock,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_map,List.mem_range'_1,
    or_false,base_injective.eq_iff]
  rcases hi with rfl|rfl|rfl|rfl <;> omega

theorem controls_nodup : [base 1028,base 1].Nodup := by
  simp [base_injective.eq_iff]

theorem cLo_eq : cLo portsJ=base 516 := by
  simp [cLo,portsJ,Q6EndpointCell.ports,wireBlock,List.getD_eq_getElem?_getD]

theorem cHi_eq : cHi portsJ=base 1541 := by
  simp [cHi,portsJ,Q6EndpointCell.ports,wireBlock,List.getD_eq_getElem?_getD]

/-- Carry #248 is virtual `760`, the retired pool wire. -/
theorem c248_eq : cAt portsJ 248=base 760 := by
  simp [cAt,portsJ,Q6EndpointCell.ports,wireBlock,List.getD_eq_getElem?_getD]

/-- The joint inverse with virtual carry `719` on the open trit hole `s 0 4 = base 1032`. -/
def kernel : Program :=
  renameProgram (Equiv.swap (base 719) (base 1032)) (jointH portsJ (base 1028) (base 1))

/-- Record-length padding: 506 empty-correction erasures of the clean carry `base 512`
(the replaced half window has 1022 and the measured first swap 257 records; the kernel has 773,
one of them the measured loan of carry #1 that retires virtual `760`). -/
def padding : Program := List.replicate 506 (Instr.measureX (base 512) [] [])

def padded : Program := kernel++padding

theorem pad_run (c : Wire) (n : Nat) (r : List Bool) (t : State) (hc : t.basis c=false) :
    run (List.replicate n (Instr.measureX c [] [])) r t=t := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have one : measureAndCorrect c [] [] (r.headD false) t=t := by
      apply State.extensionality
      · simp [measureAndCorrect,correct,hc]
      · funext q
        by_cases e : q=c
        · subst q;simp [measureAndCorrect,correct,writeBit,hc]
        · simp [measureAndCorrect,correct,writeBit,e]
    change run (Instr.measureX c [] []::List.replicate n (Instr.measureX c [] [])) r t=t
    simp only [run]
    rw [one]
    exact ih _

theorem pad_wires (c : Wire) (n : Nat) : wires (List.replicate n (Instr.measureX c [] []))⊆{c} := by
  induction n with
  | zero => simp [wires]
  | succ n ih =>
    rw [List.replicate_succ]
    intro q hq
    simp only [wires,Finset.mem_union] at hq
    rcases hq with h|h
    · simpa [Instr.wires,correctionWires] using h
    · exact ih h

theorem padding_counts : toffoliCount padding=0 ∧ measurementCount padding=506 := by
  have h (n : Nat) : toffoliCount (List.replicate n (Instr.measureX (base 512) [] []))=0 ∧
      measurementCount (List.replicate n (Instr.measureX (base 512) [] []))=n := by
    induction n with
    | zero => exact ⟨rfl,rfl⟩
    | succ n ih =>
      rw [List.replicate_succ]
      simp [toffoliCount,measurementCount,ih.1,ih.2,Nat.add_comm]
  exact h 506

theorem padded_counts : toffoliCount padded=518 ∧ measurementCount padded=1279 := by
  have j := jointH_counts portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl)))
  have r := renameProgram_counts (Equiv.swap (base 719) (base 1032)) (jointH portsJ (base 1028) (base 1))
  have p := padding_counts
  simp only [padded,kernel,toffoliCount_append,measurementCount_append,r.1,r.2,j.1,j.2,p.1,p.2]
  all_goals simp

theorem padded_slots : gateSlots padded≤10515 := by
  have j := jointH_slots portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl)))
  have p : gateSlots padding=506 := by
    have h (n : Nat) : gateSlots (List.replicate n (Instr.measureX (base 512) [] []))=n := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [List.replicate_succ,gateSlots_cons,ih]
        simp [instructionSlots]
        omega
    exact h 506
  simp only [padded,kernel,gateSlots_append,rename_gateSlots,p]
  omega

theorem padded_physical : GatePhysical padded := by
  have j := jointH_physical portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  have p : GatePhysical padding := by
    intro i hi
    rw [padding,List.mem_replicate] at hi
    rw [hi.2]
    simp [PhysicalInstr]
  simp only [padded,kernel,gatePhysical_append]
  exact ⟨gatePhysical_rename _ (Equiv.swap _ _).injective _ j,p⟩

theorem portsJ_r : portsJ.r=wireBlock base 2056 256 := by
  rw [portsJ_eq,Q6EndpointCell.ports_r,balancedSharedPorts_r]
theorem portsJ_y : portsJ.y=wireBlock base 770 256 := by
  rw [portsJ_eq,Q6EndpointCell.ports_y,balancedSharedPorts_y]
theorem portsJ_carry : portsJ.carry=wireBlock base 512 253++[base 1540,base 1541,base 1026] := rfl

theorem portsJ_take254 : portsJ.carry.take 254=wireBlock base 512 253++[base 1540] := by
  have wl : (wireBlock base 512 253).length=253 := wireBlock_length _ _ _
  rw [portsJ_carry,List.take_append,List.take_of_length_le (by omega),wl]
  rfl

theorem portsJ_take255 : portsJ.carry.take 255=portsJ.carry.take 254++[base 1541] := by
  have wl : (wireBlock base 512 253).length=253 := wireBlock_length _ _ _
  rw [portsJ_take254,portsJ_carry,List.take_append,List.take_of_length_le (by omega),wl]
  simp

/-- A numbered wire away from the three blocks and the three tail carries. -/
theorem off_ports (i : Nat) (hr : i<2056 ∨ 2312 ≤ i) (hy : i<770 ∨ 1026 ≤ i) (hc : i<512 ∨ 765 ≤ i)
    (h1 : i≠1540) (h2 : i≠1541) (h3 : i≠1026) :
    base i∉portsJ.r ∧ base i∉portsJ.y ∧ base i∉portsJ.carry := by
  refine ⟨?_,?_,?_⟩
  · rw [portsJ_r];exact OwnPlusHost.not_block i 2056 256 (by omega)
  · rw [portsJ_y];exact OwnPlusHost.not_block i 770 256 (by omega)
  · rw [portsJ_carry]
    intro h
    rcases List.mem_append.mp h with h|h
    · exact OwnPlusHost.not_block i 512 253 (by omega) h
    · simp only [List.mem_cons,List.not_mem_nil,or_false,base_injective.eq_iff] at h
      omega

/-- The sites the padded kernel may use: data words, the first 254 carries, the four scalars,
the controls `S0`, `G1` and the trit hole `s 0 4`. -/
def kernelSites : Finset Wire :=
  (portsJ.r++portsJ.y++portsJ.carry.take 254++
    [portsJ.parity,portsJ.lower,portsJ.one,portsJ.sign,base 1028,base 1,base 1032]).toFinset

theorem hole_free : base 1032∉wires (jointH portsJ (base 1028) (base 1)) := by
  have sup := jointH_support portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
  intro used
  have m := List.mem_toFinset.mp (sup used)
  have off := off_ports 1032 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [retSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with ((h|h)|h)|h
  · exact off.1 h
  · exact off.2.1 h
  · exact off.2.2 (List.mem_of_mem_take h)
  · simp only [portsJ,Q6EndpointCell.ports,base_injective.eq_iff] at h
    omega

theorem padded_support : wires padded⊆kernelSites := by
  have sup := jointH_support portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
  have lo := jointH_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq,c248_eq] at lo
  have keep (q : Wire) (hq : q∈wires (jointH portsJ (base 1028) (base 1))) : q∈kernelSites := by
    have m := List.mem_toFinset.mp (sup hq)
    have q1541 : q≠base 1541 := fun e => lo _ (Or.inr (Or.inl e)) hq
    simp only [retSites,List.mem_append] at m
    simp only [kernelSites,List.mem_toFinset,List.mem_append]
    rcases m with ((h|h)|h)|h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · rw [portsJ_take255,List.mem_append,List.mem_singleton] at h
      rcases h with h|h
      · exact Or.inl (Or.inr h)
      · exact absurd h q1541
    · right
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
  intro q hq
  simp only [padded,kernel,wires_append,Finset.mem_union,renameProgram_support] at hq
  rcases hq with hq|hq
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    by_cases a719 : a=base 719
    · subst a
      rw [Equiv.swap_apply_left]
      simp [kernelSites]
    · by_cases a1032 : a=base 1032
      · exact absurd (a1032 ▸ ha) hole_free
      · rw [Equiv.swap_apply_of_ne_of_ne a719 a1032]
        exact keep a ha
  · have e : q=base 512 := Finset.mem_singleton.mp (pad_wires (base 512) 506 hq)
    subst e
    have m : base 512∈wireBlock base 512 253 :=
      List.mem_map.mpr ⟨512,by simp [List.mem_range'_1],rfl⟩
    simp only [kernelSites,List.mem_toFinset,List.mem_append,portsJ_take254]
    exact Or.inl (Or.inr (Or.inl m))

theorem padded_free (i : Nat) (hi : i=0 ∨ i=516 ∨ i=719 ∨ i=1541) : base i∉wires padded := by
  have lo := jointH_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq,c248_eq] at lo
  rcases hi with rfl|rfl|rfl|rfl
  · intro used
    have m := List.mem_toFinset.mp (padded_support used)
    have off := off_ports 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with ((h|h)|h)|h
    · exact off.1 h
    · exact off.2.1 h
    · exact off.2.2 (List.mem_of_mem_take h)
    · simp only [portsJ,Q6EndpointCell.ports,base_injective.eq_iff] at h
      omega
  all_goals
    intro used
    simp only [padded,kernel,wires_append,Finset.mem_union,renameProgram_support] at used
    rcases used with used|used
    · obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp used
      by_cases a719 : a=base 719
      · subst a719
        rw [Equiv.swap_apply_left,base_injective.eq_iff] at eq
        omega
      · by_cases a1032 : a=base 1032
        · subst a1032
          exact hole_free ha
        · rw [Equiv.swap_apply_of_ne_of_ne a719 a1032] at eq
          subst eq
          first
            | exact a719 rfl
            | exact lo _ (Or.inl rfl) ha
            | exact lo _ (Or.inr (Or.inl rfl)) ha
    · have e := Finset.mem_singleton.mp (pad_wires (base 512) 506 used)
      rw [base_injective.eq_iff] at e
      omega

/-- Virtual wire `760` (carry #248, the retired pool wire) never occurs in the padded joint inverse. -/
theorem padded_760_free : base 760∉wires padded := by
  have lo := jointH_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq,c248_eq] at lo
  intro used
  simp only [padded,kernel,wires_append,Finset.mem_union,renameProgram_support] at used
  rcases used with used|used
  · obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp used
    by_cases a719 : a=base 719
    · subst a719
      rw [Equiv.swap_apply_left,base_injective.eq_iff] at eq
      omega
    · by_cases a1032 : a=base 1032
      · subst a1032
        exact hole_free ha
      · rw [Equiv.swap_apply_of_ne_of_ne a719 a1032] at eq
        subst eq
        exact lo _ (Or.inr (Or.inr rfl)) ha
  · have e := Finset.mem_singleton.mp (pad_wires (base 512) 506 used)
    rw [base_injective.eq_iff] at e
    omega

end ECDSAAdd.Entrant.JointInverse1588


/-! ### The padded kernel's frame on the replay state -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum
  EntryRetained5 FirstInverse5 Challenge Baselines
attribute [local irreducible] wires

theorem off_data (i : Nat) (hr : i<2056 ∨ 2312 ≤ i) (hy : i<770 ∨ 1026 ≤ i) :
    base i∉portsJ.r ∧ base i∉portsJ.y := by
  refine ⟨?_,?_⟩
  · rw [portsJ_r];exact OwnPlusHost.not_block i 2056 256 (by omega)
  · rw [portsJ_y];exact OwnPlusHost.not_block i 770 256 (by omega)

theorem carry_work (i : Nat) (hi : 512 ≤ i ∧ i<765) : base i∈BalancedCircuit.work portsJ := by
  have m : base i∈wireBlock base 512 253 := List.mem_map.mpr ⟨i,by simp [List.mem_range'_1];omega,rfl⟩
  simp only [BalancedCircuit.work,List.mem_append,portsJ_carry]
  exact Or.inr (Or.inl m)

/-- On any replay state with clean scalar bank, clean flag and open trit hole, the padded kernel
performs f2dcda16's joint inverse `(±Z/2, J?Z:0) ↦ (Z,0)`. -/
theorem padded_pair (st : BasisState) (clean : ∀q∈BalancedCircuit.work portsJ,st q=false)
    (sign : st (base 2409)=false) (hole : st (base 1032)=false) (Z : Fp) :
    Triple (PairFrame portsJ.r portsJ.y st
      (centerWord ((if st (base 1028) && !st (base 1) then -Z else Z)/2))
      (centerWord (if st (base 1028) then Z else 0))) padded
      (PairFrame portsJ.r portsJ.y st (centerWord Z) 0) := by
  have j := jointH_pair portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup st clean
    (by simpa [portsJ_eq] using sign) Z
  intro s m input
  have a719 := off_data 719 (by omega) (by omega)
  have a1032 := off_data 1032 (by omega) (by omega)
  have a512 := off_data 512 (by omega) (by omega)
  let mk := m.take (measurementCount kernel)
  have out := j s mk input
  have in719 : s.basis (base 719)=false :=
    (input.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have in1032 : s.basis (base 1032)=false := (input.2.2 _ a1032.1 a1032.2).trans hole
  have o719 : (run (jointH portsJ (base 1028) (base 1)) mk s).basis (base 719)=false :=
    (out.2.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have o1032 : (run (jointH portsJ (base 1028) (base 1)) mk s).basis (base 1032)=false :=
    (out.2.2.2 _ a1032.1 a1032.2).trans hole
  have k : run kernel mk s=run (jointH portsJ (base 1028) (base 1)) mk s :=
    rebind_swap_run _ _ _ s mk in719 in1032 o719 o1032
  have o512 : (run (jointH portsJ (base 1028) (base 1)) mk s).basis (base 512)=false :=
    (out.2.2.2 _ a512.1 a512.2).trans (clean _ (carry_work 512 (by omega)))
  have shape : run padded m s=run (jointH portsJ (base 1028) (base 1)) mk s := by
    rw [padded,run_append,k,padding]
    exact pad_run (base 512) 506 _ _ o512
  rw [shape]
  exact out

end ECDSAAdd.Entrant.JointInverse1588

/-! ### Syntax-slot comparison with the replaced half window -/
set_option maxRecDepth 100000
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic MappedCompressed Challenge


end ECDSAAdd.Entrant.JointInverse1588

namespace ECDSAAdd.Entrant.JointInverse1588

/-- Toffoli saving of the S2 (multiply) first body: the 1020-T G1 half window and the 0-T final
measured swap become the 518-T padded joint inverse (517 + the measured loan of carry #1 that
retires virtual `760`). -/
def saving (divide : Bool) : Nat := if divide then 0 else 502

end ECDSAAdd.Entrant.JointInverse1588
end

-- ===== merged module ECDSAAdd.Submission.Entrant.JointForward1588 =====
section
set_option Elab.async false

/-! Forward joint entry of the S1 (divide) first packet, placed in the 1,588-qubit Rolling layout.

The divide stage's first packet starts on the pair `(Z, 0)`.  Its first measured selector swap
(`FrontierSW1591.firstSwapS`, controlled by `S0`) and its trit-1 half window (controlled by `G1`)
together compute `((±Z)/2, S0 ? Z : 0)`.  The joint entry `EntryRetained5.program` (spariev,
submission 74fe2201, already in the record) computes the same pair directly; the measured joint
inverse of the multiplication stage (`JointInverse1588`) is its mirror image.

As there, the record's layout has no sites for the virtual carries `516` and `1541`, so the
forward program hosts them inside the kernel:
* during the inner adder (source bits 4..255) of the forward addition on `lowY` (u = J∧B) and
  `sign` (e = lower∧u), which are measured away before and recomputed after (+2 Toffolis), with
  `JointInverse1588.loanW`;
* during the final `clearParity` on the scalars `one` and `sign`, which `eraseScalars` has
  just cleared (as `JointInverse1588.clearH`).

Retiring virtual `760` (carry #248) for the 1,587-qubit layout, exactly as in `JointInverse1588`:
* during the parity carry chain of the final `clearParity` carry #248 sits on `rmsb`, which
  `prepareMagnitude` has just cleared and the chain never reads (`clearParityF`, a pure rename);
* during the inner adder carry #248 sits on carry #1, measured away before `loanW`'s two
  measurements and recomputed after its two Toffolis (`loanF`, +1 Toffoli, +1 record). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false


/-! ### Retiring carry #248 (virtual `760`): the measured loan of carry #1 and the `rmsb` host
(copies of the `JointInverse1588` lemmas, so that this file only relies on unchanged helpers there) -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588
attribute [local irreducible] run

/-- After the four leading majorities, carry #1 is the majority of source bit 1, `r1` and carry #0. -/
theorem pre4_c1F (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (s : State)
    (h1 : s.basis (cAt L 1)=false) :
    (run (pre4 L) [] s).basis (cAt L 1)=carryBit ((source L 1).value (run (pre4 L) [] s).basis)
      ((run (pre4 L) [] s).basis (rAt L 1)) ((run (pre4 L) [] s).basis (cAt L 0)) := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have nd := arithmeticND L hw hn
  have away := sources_away L hw hn
  rw [hr,hc] at nd
  have sub : [lowY L,L.r0,r1,r2,r3,c0,c1,c2,c3].Sublist
      (lowY L::(L.r0::r1::r2::r3::r4::rt++c0::c1::c2::c3::ct)) := by
    apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂
    apply List.Sublist.cons₂;apply List.Sublist.cons₂
    apply List.Sublist.cons
    apply List.sublist_append_of_sublist_right
    apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂
    exact List.nil_sublist _
  have nd9 := nd.sublist sub
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd9
  rcases nd9 with ⟨⟨u0,u1,u2,u3,uc0,uc1,uc2,uc3⟩,⟨⟨a1,a2,a3,a0c0,a0c1,a0c2,a0c3⟩,
    ⟨⟨b2,b3,b1c0,b1c1,b1c2,b1c3⟩,⟨⟨c23,c2c0,c2c1,c2c2,c2c3⟩,⟨⟨d0,d1,d2,d3⟩,
    ⟨⟨g01,g02,g03⟩,⟨⟨g12,g13⟩,g23⟩⟩⟩⟩⟩⟩⟩
  have src (i : Nat) (hi : i<4) (y cin co : Wire) (hy : y∈L.r)
      (hcin : cin=lowY L ∨ cin∈L.carry.take 255) (hco : co∈L.carry.take 255) :
      ∀q∈(source L i).wires,q∉[y,cin,co] := by
    intro q hq bad
    have aw := away q (source_site L i (by omega) q hq)
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false,not_or] at aw bad
    rcases bad with rfl|rfl|rfl
    · exact aw.2.1 hy
    · rcases hcin with rfl|h
      · exact aw.1 rfl
      · exact aw.2.2 h
    · exact aw.2.2 hco
  have valid (i : Nat) (hi : i<4) := sources_valid L hn _ (source_mem L i (by omega))
  have rm (i : Nat) (hi : i<4) : rAt L i∈L.r := by
    rw [hr]
    interval_cases i <;> simp [e0,e1,e2,e3]
  have cm (i : Nat) (hi : i<4) : cAt L i∈L.carry.take 255 := by
    rw [hc]
    interval_cases i <;> simp [f0,f1,f2,f3]
  have k0 := maj_keep (source L 0) (valid 0 (by decide)) (rAt L 0) (lowY L) (cAt L 0)
    (by rw [e0,f0];simp [Ne.symm u0,uc0,a0c0])
    (src 0 (by decide) _ _ _ (rm 0 (by decide)) (Or.inl rfl) (cm 0 (by decide)))
  have m1 := Affine.majority_correct (source L 1) (valid 1 (by decide)) (rAt L 1) (cAt L 0) (cAt L 1)
    (by rw [e1,f0,f1];simp [b1c0,b1c1,g01])
    (src 1 (by decide) _ _ _ (rm 1 (by decide)) (Or.inr (cm 0 (by decide))) (cm 1 (by decide)))
  have k2 := maj_keep (source L 2) (valid 2 (by decide)) (rAt L 2) (cAt L 1) (cAt L 2)
    (by rw [e2,f1,f2];simp [c2c1,c2c2,g12])
    (src 2 (by decide) _ _ _ (rm 2 (by decide)) (Or.inr (cm 1 (by decide))) (cm 2 (by decide)))
  have k3 := maj_keep (source L 3) (valid 3 (by decide)) (rAt L 3) (cAt L 2) (cAt L 3)
    (by rw [e3,f2,f3];simp [d2,d3,g23])
    (src 3 (by decide) _ _ _ (rm 3 (by decide)) (Or.inr (cm 2 (by decide))) (cm 3 (by decide)))
  have z (b : Affine.Bit) (y cin co : Wire) : measurementCount (Affine.majority b y cin co)=0 :=
    (Affine.bit_counts b y cin co).2.1
  -- wires of source bit 1 and the two read sites avoid carries #1..#3
  have sw (q : Wire) (hq : q∈(source L 1).wires) (i : Nat) (hi : i<4) : q≠cAt L i := by
    intro e
    have aw := away q (source_site L 1 (by decide) q hq)
    exact aw (by rw [e]; simp [cm i hi])
  have r1c (i : Nat) (h1 : 1 ≤ i) (h4 : i<4) : rAt L 1≠cAt L i := by
    rw [e1]
    interval_cases i
    · rw [f1];exact b1c1
    · rw [f2];exact b1c2
    · rw [f3];exact b1c3
  have c0c (i : Nat) (h1 : 1 ≤ i) (h4 : i<4) : cAt L 0≠cAt L i := by
    rw [f0]
    interval_cases i
    · rw [f1];exact g01
    · rw [f2];exact g02
    · rw [f3];exact g03
  have c1c (i : Nat) (h1 : 2 ≤ i) (h4 : i<4) : cAt L 1≠cAt L i := by
    rw [f1]
    interval_cases i
    · rw [f2];exact g12
    · rw [f3];exact g13
  have c10 : cAt L 1≠cAt L 0 := by rw [f0,f1];exact Ne.symm g01
  simp only [pre4,run_append,measurementCount_append,z,Nat.add_zero,List.take_zero,List.drop_zero,
    List.take_nil,List.drop_nil]
  generalize hs0 : run (Affine.majority (source L 0) (rAt L 0) (lowY L) (cAt L 0)) [] s=s0
  have s0c1 : s0.basis (cAt L 1)=false := by rw [←hs0,(k0 _ _).2 _ c10];exact h1
  rw [m1 s0 []]
  generalize hs1 : (⟨s0.phase,writeBit s0.basis (cAt L 1) (s0.basis (cAt L 1) ^^
    carryBit ((source L 1).value s0.basis) (s0.basis (rAt L 1)) (s0.basis (cAt L 0)))⟩ : State)=s1
  have k23 (q : Wire) (h2 : q≠cAt L 2) (h3 : q≠cAt L 3) :
      (run (Affine.majority (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)) []
        (run (Affine.majority (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)) [] s1)).basis q=s1.basis q := by
    rw [(k3 _ _).2 q h3,(k2 _ _).2 q h2]
  have s1keep (q : Wire) (hq : q≠cAt L 1) : s1.basis q=s0.basis q := by
    rw [←hs1];simp [writeBit,hq]
  have value : (source L 1).value (run (Affine.majority (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)) []
        (run (Affine.majority (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)) [] s1)).basis=
      (source L 1).value s0.basis := by
    apply Affine.Bit.value_congr
    intro q hq
    rw [k23 q (sw q hq 2 (by decide)) (sw q hq 3 (by decide)),s1keep q (sw q hq 1 (by decide))]
  rw [value,k23 _ (c1c 2 (by decide) (by decide)) (c1c 3 (by decide) (by decide)),
    k23 _ (r1c 2 (by decide) (by decide)) (r1c 3 (by decide) (by decide)),k23 _ (c0c 2 (by decide) (by decide)) (c0c 3 (by decide) (by decide)),
    s1keep _ (r1c 1 (by decide) (by decide)),s1keep _ (c0c 1 (by decide) (by decide)),←hs1]
  simp [writeBit,s0c1]

/-- The inner adder's carries are not among carries #0..#3. -/
theorem carry_drop4_neF (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈(L.carry.take 255).drop 4) (i : Nat) (hi : i<4) : q≠cAt L i := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hct,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have ndc : (L.carry.take 255).Nodup := (carry_nodup L hn).sublist (List.take_sublist _ _)
  rw [hct] at ndc hq
  simp only [List.drop_succ_cons,List.drop_zero] at hq
  simp only [List.nodup_cons,List.mem_cons,not_or] at ndc
  intro e
  interval_cases i
  · rw [f0] at e;exact ndc.1.2.2.2 (e ▸ hq)
  · rw [f1] at e;exact ndc.2.1.2.2 (e ▸ hq)
  · rw [f2] at e;exact ndc.2.2.1.2 (e ▸ hq)
  · rw [f3] at e;exact ndc.2.2.2.1 (e ▸ hq)

/-- The inner adder's targets are not among targets #0..#3. -/
theorem r_drop4_neF (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.r.drop 4) (i : Nat) (hi : i<4) : q≠rAt L i := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hct,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have ndr := EntryHalf5.target_nodup L hn
  rw [hr] at ndr hq
  simp only [List.drop_succ_cons,List.drop_zero,List.mem_cons] at hq
  simp only [List.nodup_cons,List.mem_cons,not_or] at ndr
  intro e
  interval_cases i
  · rw [e0] at e;subst e
    rcases hq with h|h
    · exact ndr.1.2.2.2.1 h
    · exact ndr.1.2.2.2.2 h
  · rw [e1] at e;subst e
    rcases hq with h|h
    · exact ndr.2.1.2.2.1 h
    · exact ndr.2.1.2.2.2 h
  · rw [e2] at e;subst e
    rcases hq with h|h
    · exact ndr.2.2.1.2.1 h
    · exact ndr.2.2.1.2.2 h
  · rw [e3] at e;subst e
    rcases hq with h|h
    · exact ndr.2.2.2.1.1 h
    · exact ndr.2.2.2.1.2 h

/-- Carries #0..#2 and the targets #0..#3 lie outside the inner adder. -/
theorem low_inner_freeF (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (∀i,i<3 → cAt L i∉wires (inner L)) ∧ (∀i,i<4 → rAt L i∉wires (inner L)) := by
  have flagsAway (q : Wire) (hq : q∈[L.parity,L.lower,L.one]) : q∉L.r++L.y++L.carry :=
    flagAway L hn q (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto)
  constructor
  · intro i hi used
    have m := List.mem_toFinset.mp (inner_support L used)
    have ci : cAt L i∈L.carry := carry_mem L hw i (by omega)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with ((h|h)|h)|h
    · exact flagsAway _ (inner_sites L _ h) (by simp [ci])
    · exact carry_not_r L hn _ ci (List.mem_of_mem_drop h)
    · exact carry_drop4_neF L hw hn _ h i (by omega) rfl
    · exact carry_index_ne L hw hn i 3 (by omega) (by decide) (by omega) h
  · intro i hi used
    have m := List.mem_toFinset.mp (inner_support L used)
    have ri : rAt L i∈L.r := by
      have len := BalancedCleanup.widths L.toLayout hw
      have lt : i<L.r.length := by rw [len.2.1];omega
      simp only [rAt,List.getD_eq_getElem _ _ lt]
      exact List.getElem_mem lt
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with ((h|h)|h)|h
    · exact flagsAway _ (inner_sites L _ h) (by simp [ri])
    · exact r_drop4_neF L hw hn _ h i hi rfl
    · exact carry_not_r L hn _ (List.mem_of_mem_take (List.mem_of_mem_drop h)) ri
    · exact carry_not_r L hn (cAt L 3) (carry_mem L hw 3 (by decide)) (by rw [←h];exact ri)

/-- A wire outside `P` and distinct from the two swapped sites stays outside the renamed `P`. -/
theorem swap_freeF (a b q : Wire) (P : Program) (hq : q∉wires P) (ha : q≠a) (hb : q≠b) :
    q∉wires (renameProgram (Equiv.swap a b) P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp used
  have back : x=Equiv.swap a b q := by rw [←ex];simp only [Equiv.swap_apply_self]
  rw [Equiv.swap_apply_of_ne_of_ne ha hb] at back
  exact hq (back ▸ hx)

/-- The image of a renamed program lies in any set containing the old support and both sites. -/
theorem swap_supportF (a b : Wire) (P : Program) (W : Finset Wire) (hP : wires P⊆W)
    (ha : a∈W) (hb : b∈W) : wires (renameProgram (Equiv.swap a b) P)⊆W := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  have hyW := hP hy
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

/-- The measured loan of carry #1 around `loanW`: carry #1 (`maj(one⊕sign,r1,c0)`, still readable
while `sign` is present) is erased before `loanW`'s two measurements and recomputed after its two
Toffolis; inside, carry #248 is hosted on carry #1's site. -/
def loanF (L : Layout) (J B : Wire) : Program :=
  Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)++
    (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L)
      (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L))++
    Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))

theorem loanF_counts (L : Layout) (J B : Wire) :
    toffoliCount (loanF L J B)=toffoliCount (inner L)+3 ∧
    measurementCount (loanF L J B)=3+measurementCount (inner L) := by
  have e := Affine.bit_counts (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
  have w := loanW_counts L.sign L.lower (lowY L) J B (cLo L) (cHi L)
    (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L))
  have r := renameProgram_counts (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)
  simp only [loanF,toffoliCount_append,measurementCount_append,e.1,e.2.1,e.2.2.1,e.2.2.2.1,
    w.1,w.2,r.1,r.2]
  omega

/-- On a state where `sign = lower∧lowY`, `lowY = J∧B` and every carry is clean, the carry-#1 loan
after `pre4` runs as the inner adder (it only reads three extra records). -/
theorem loanF_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (b : State) (r : List Bool)
    (he : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)))
    (hu : b.basis (lowY L)=(b.basis J && b.basis B))
    (hc : ∀q∈L.carry,b.basis q=false) :
    run (loanF L J B) r (run (pre4 L) [] b)=run (inner L) (r.drop 3) (run (pre4 L) [] b) := by
  generalize hx : run (pre4 L) [] b=x
  have dist := ports_distinct L hw hn J B hJ hB hJB
  have nd7 := dist.1
  have flags (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q∉L.r++L.y++L.carry := flagAway L hn q hq
  have notData (q : Wire) (hq : q∉L.wires) : q∉L.r++L.y++L.carry := fun bad => hq (data_member L q bad)
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have lowCarry (i : Nat) (hi : i<4) : cAt L i∈L.carry := carry_mem L hw i (by omega)
  have offData (q : Wire) (hq : q∉L.r++L.y++L.carry) : q∉L.r ∧ ∀i,i<4 → q≠cAt L i :=
    ⟨fun h => hq (by simp [h]),fun i hi e => hq (by rw [e];simp [lowCarry i hi])⟩
  have pk (q : Wire) (h4 : ∀i,i<4 → q≠cAt L i) : x.basis q=b.basis q := by
    rw [←hx]
    exact (pre4_run L hw hn b []).2 q (h4 0 (by decide)) (h4 1 (by decide)) (h4 2 (by decide))
      (h4 3 (by decide))
  have keepS := pk L.sign (offData _ (flags _ (by simp))).2
  have keepA := pk L.lower (offData _ (flags _ (by simp))).2
  have keepU := pk (lowY L) (fun i hi e => y_not_carry L hn _ y0 (by rw [e];exact lowCarry i hi))
  have keepJ := pk J (offData _ (notData _ hJ)).2
  have keepB := pk B (offData _ (notData _ hB)).2
  have hiIdx (k : Nat) (hk : 4≤k ∧ k<256) (i : Nat) (hi : i<4) : L.carry.getD k 0≠cAt L i :=
    carry_index_ne L hw hn k i (by omega) (by omega) (by omega)
  have keepLo := pk (cLo L) (hiIdx 4 (by decide))
  have keepHi := pk (cHi L) (hiIdx 254 (by decide))
  have keep248 := pk (cAt L 248) (hiIdx 248 (by decide))
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have cleanX : ∀q∈(L.carry.take 255).drop 4,x.basis q=false := fun q hq =>
    (pk q (carry_drop4_neF L hw hn q hq)).trans (hc q (List.mem_of_mem_take (List.mem_of_mem_drop hq)))
  -- carry #1 holds its majority: erase it
  have c1val : x.basis (cAt L 1)=carryBit ((source L 1).value x.basis) (x.basis (rAt L 1))
      (x.basis (cAt L 0)) := by
    rw [←hx];exact pre4_c1F L hw hn b (hc _ (lowCarry 1 (by decide)))
  have valid1 := sources_valid L hn _ (source_mem L 1 (by decide))
  have r1mem : rAt L 1∈L.r := by
    have len := BalancedCleanup.widths L.toLayout hw
    have lt : 1<L.r.length := by rw [len.2.1];decide
    simp only [rAt,List.getD_eq_getElem _ _ lt]
    exact List.getElem_mem lt
  have c10 : cAt L 1≠cAt L 0 := carry_index_ne L hw hn 1 0 (by decide) (by decide) (by decide)
  have loc : [rAt L 1,cAt L 0,cAt L 1].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
      not_false_eq_true,and_true]
    exact ⟨⟨fun e => carry_not_r L hn _ (lowCarry 0 (by decide)) (e ▸ r1mem),
      fun e => carry_not_r L hn _ (lowCarry 1 (by decide)) (e ▸ r1mem)⟩,Ne.symm c10⟩
  have srcAway (q : Wire) (hq : q∈(source L 1).wires) : q∉L.r++L.y++L.carry := by
    have m := source_sites L 1 hq
    exact flagAway L hn q (by simp only [List.mem_cons,List.not_mem_nil,or_false] at m ⊢;tauto)
  have locAway : ∀q∈(source L 1).wires,q∉[rAt L 1,cAt L 0,cAt L 1] := by
    intro q hq bad
    simp only [List.mem_cons,List.not_mem_nil,or_false] at bad
    rcases bad with rfl|rfl|rfl
    · exact srcAway _ hq (by simp [r1mem])
    · exact srcAway _ hq (by simp [lowCarry 0 (by decide)])
    · exact srcAway _ hq (by simp [lowCarry 1 (by decide)])
  have erase (t : List Bool) :
      run (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) t x=
        ⟨x.phase,writeBit x.basis (cAt L 1) false⟩ :=
    Affine.erase_correct _ valid1 _ _ _ loc locAway x t c1val
  generalize hx1 : (⟨x.phase,writeBit x.basis (cAt L 1) false⟩ : State)=x1 at erase
  have x1keep (q : Wire) (hq : q≠cAt L 1) : x1.basis q=x.basis q := by
    rw [←hx1];simp [writeBit,hq]
  have x1c1 : x1.basis (cAt L 1)=false := by rw [←hx1];simp [writeBit]
  have lf := low_inner_freeF L hw hn
  have c1In : cAt L 1∉wires (inner L) := lf.1 1 (by decide)
  have c248ne1 : cAt L 248≠cAt L 1 := carry_index_ne L hw hn 248 1 (by decide) (by decide) (by decide)
  have cleanX1 : ∀q∈(L.carry.take 255).drop 4,x1.basis q=false := fun q hq =>
    (x1keep q (carry_drop4_neF L hw hn q hq 1 (by decide))).trans (cleanX q hq)
  have inn (t : List Bool) := inner_correct L hw hn x1 t cleanX1
  -- the renamed inner adder runs as the inner adder on `x1`
  have host (t : List Bool) :
      run (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) t x1=run (inner L) t x1 := by
    apply rebind_swap_run
    · rw [x1keep _ c248ne1,keep248];exact hc _ m248
    · exact x1c1
    · rw [(inn t).2 _ (carry_not_r L hn _ m248),x1keep _ c248ne1,keep248];exact hc _ m248
    · rw [run_preserves_outside _ _ _ _ c1In];exact x1c1
  -- loanW on `x1`
  have uIn : lowY L∉wires (inner L) := inner_free L hw hn _ (fun h => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with e|e|e
      · exact flags L.parity (by simp) (by rw [←e];simp [y0])
      · exact flags L.lower (by simp) (by rw [←e];simp [y0])
      · exact flags L.one (by simp) (by rw [←e];simp [y0]))
      (y_not_r L hn _ y0) (y_not_carry L hn _ y0)
  have eIn : L.sign∉wires (inner L) := inner_free L hw hn _ (fun h => by
      have sc := scalarND L hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with e|e|e <;>
        (have c := List.nodup_iff_count.mp sc L.sign
         rw [e] at c;simp [List.count_cons] at c;omega))
      (offData _ (flags _ (by simp))).1 (fun h => flags L.sign (by simp) (by simp [h]))
  have uc (i : Nat) (hi : i<256) : lowY L≠L.carry.getD i 0 :=
    fun e => y_not_carry L hn _ y0 (by rw [e];exact carry_mem L hw i hi)
  have ec (i : Nat) (hi : i<256) : L.sign≠L.carry.getD i 0 :=
    fun e => flags L.sign (by simp) (by rw [e];exact List.mem_append_right _ (carry_mem L hw i hi))
  have loC : cLo L≠cAt L 1 := carry_index_ne L hw hn 4 1 (by decide) (by decide) (by decide)
  have hiC : cHi L≠cAt L 1 := carry_index_ne L hw hn 254 1 (by decide) (by decide) (by decide)
  have aC : L.lower≠cAt L 1 := fun e => flags L.lower (by simp)
    (by rw [e];exact List.mem_append_right _ (lowCarry 1 (by decide)))
  have jC : J≠cAt L 1 := fun e => notData J hJ (by rw [e];exact List.mem_append_right _ (lowCarry 1 (by decide)))
  have bC : B≠cAt L 1 := fun e => notData B hB (by rw [e];exact List.mem_append_right _ (lowCarry 1 (by decide)))
  have loan (t : List Bool) := loanW_run L.sign L.lower (lowY L) J B (cLo L) (cHi L)
    (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) x1 t nd7
    (by rw [x1keep _ (ec 1 (by decide)),x1keep _ aC,x1keep _ (uc 1 (by decide)),keepS,keepA,keepU];exact he)
    (by rw [x1keep _ (uc 1 (by decide)),x1keep _ jC,x1keep _ bC,keepU,keepJ,keepB];exact hu)
    (swap_freeF _ _ _ _ uIn (uc 248 (by decide)) (uc 1 (by decide)))
    (swap_freeF _ _ _ _ eIn (ec 248 (by decide)) (ec 1 (by decide)))
    (by
      intro t
      rw [host t]
      have i := (inn t).2
      exact ⟨i _ (offData _ (flags _ (by simp))).1,i _ (offData _ (notData _ hJ)).1,
        i _ (offData _ (notData _ hB)).1⟩)
    (by rw [x1keep _ loC,keepLo];exact hc _ (carry_mem L hw 4 (by decide)))
    (by rw [x1keep _ hiC,keepHi];exact hc _ (carry_mem L hw 254 (by decide)))
    (by
      intro t
      rw [host t,(inn t).2 (cLo L) (carry_not_r L hn _ (carry_mem L hw 4 (by decide))),x1keep _ loC,keepLo]
      exact hc _ (carry_mem L hw 4 (by decide)))
    (by
      intro t
      rw [host t,(inn t).2 (cHi L) (carry_not_r L hn _ (carry_mem L hw 254 (by decide))),x1keep _ hiC,keepHi]
      exact hc _ (carry_mem L hw 254 (by decide)))
  -- the inner adder on `x1` is the inner adder on `x` with carry #1 cleared
  have outside (t : List Bool) : run (inner L) t x1=
      ⟨(run (inner L) t x).phase,writeBit (run (inner L) t x).basis (cAt L 1) false⟩ := by
    rw [←hx1];exact G0CarryLoan5.run_write_outside (inner L) (cAt L 1) c1In x t false
  have innX (t : List Bool) := inner_correct L hw hn x t cleanX
  -- recompute carry #1
  have r1c1 : rAt L 1≠cAt L 1 := fun e => carry_not_r L hn _ (lowCarry 1 (by decide)) (e ▸ r1mem)
  have restore (t t' : List Bool) :
      run (Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) t' (run (inner L) t x1)=
        run (inner L) t x := by
    rw [outside t,Affine.majority_correct _ valid1 _ _ _ loc locAway]
    generalize hy : run (inner L) t x=y
    have yc1 : y.basis (cAt L 1)=x.basis (cAt L 1) := by
      rw [←hy];exact run_preserves_outside _ _ _ _ c1In
    have yr1 : y.basis (rAt L 1)=x.basis (rAt L 1) := by
      rw [←hy];exact run_preserves_outside _ _ _ _ (lf.2 1 (by decide))
    have yc0 : y.basis (cAt L 0)=x.basis (cAt L 0) := by
      rw [←hy];exact run_preserves_outside _ _ _ _ (lf.1 0 (by decide))
    have yv : (source L 1).value (Function.update y.basis (cAt L 1) false)=(source L 1).value x.basis := by
      apply Affine.Bit.value_congr
      intro q hq
      have qc1 : q≠cAt L 1 := fun e => locAway q hq (by simp [e])
      have qr : q∉L.r := fun h => srcAway q hq (by simp [h])
      rw [Function.update_of_ne qc1,←hy]
      exact (innX t).2 q qr
    apply State.extensionality
    · rfl
    · funext q
      by_cases qe : q=cAt L 1
      · subst qe
        simp only [writeBit,Function.update_self,Function.update_of_ne r1c1,Function.update_of_ne (Ne.symm c10),
          Bool.false_xor]
        rw [yv,yr1,yc0,←c1val,yc1]
      · simp [writeBit,qe]
  -- assemble
  have e1c : measurementCount (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))=1 :=
    (Affine.bit_counts (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)).2.2.2.1
  rw [loanF,run_append,e1c,erase,run_append,run_take,loan,host,restore]
  congr 1
  rw [List.drop_drop]

/-- `positiveParity` with carry #248 hosted on `rmsb`: `prepareMagnitude` copies `rmsb` into the clean
`lower` and complements the whole target word under it, so `rmsb` is clean for the whole carry chain,
which reads only the low 255 target bits. -/
def positiveParityF (L : Layout) (ctl : Wire) : Program :=
  EntryHalf5.prepareMagnitude L++(renameProgram (Equiv.swap (cAt L 248) L.rmsb)
    (EntryHalf5.parityCarry L ctl)++(EntryHalf5.prepareMagnitude L).reverse)

def recoverParityF (L : Layout) (J : Wire) : Program :=
  [.X J]++positiveParityF L J++[.X J]

def clearParityF (L : Layout) (J : Wire) : Program :=
  [.CX (L.ylow.getD 0 0) L.parity]++recoverParityF L J

theorem positiveParityF_counts (L : Layout) (ctl : Wire) :
    toffoliCount (positiveParityF L ctl)=toffoliCount (EntryHalf5.positiveParity L ctl) ∧
    measurementCount (positiveParityF L ctl)=measurementCount (EntryHalf5.positiveParity L ctl) := by
  have r := renameProgram_counts (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L ctl)
  simp only [positiveParityF,EntryHalf5.positiveParity,toffoliCount_append,measurementCount_append,r.1,r.2]
  exact ⟨trivial,trivial⟩

/-- `prepareMagnitude` leaves `rmsb` clean on a centered target word with clean `lower`. -/
theorem prepare_rmsbF (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hz : s.basis L.lower=false) :
    (run (EntryHalf5.prepareMagnitude L) m s).basis L.rmsb=false := by
  have nd := (List.nodup_append'.mp hn).2.1
  have h := BalancedCleanup.prepareSign_value L.toLayout hw nd R hr s m hR hz
  let t := run (EntryHalf5.prepareMagnitude L) m s
  change regValue L.r t.basis=(magnitude R).toNat ∧ t.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → t.basis q=s.basis q) at h
  change t.basis L.rmsb=false
  have b := magnitude_bounds R hr
  have z := Int.toNat_of_nonneg b.1
  have c := constants
  have bound : (magnitude R).toNat<2^255 := by norm_num only [Nat.reducePow] at ⊢; omega
  have split : regValue L.r t.basis=regValue L.low t.basis+2^255*(t.basis L.rmsb).toNat := by
    rw [BalancedCleanup.Layout.r,regValue_append,(BalancedCleanup.widths L.toLayout hw).1]
    cases k : t.basis L.rmsb <;> simp [regValue,k]
  rw [h.1] at split
  cases k : t.basis L.rmsb
  · rfl
  · rw [k] at split
    simp only [Bool.toNat_true,Nat.mul_one] at split
    omega

theorem positiveParityF_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (ctl : Wire) (hctl : ctl∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (positiveParityF L ctl) m s=run (EntryHalf5.positiveParity L ctl) m s := by
  let c := run (EntryHalf5.prepareMagnitude L) [] s
  have pv := EntryHalf5.prepare_low_value L hw hn R hr s [] hR hz
  change regValue L.low c.basis=(magnitude R).toNat ∧ c.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → c.basis q=s.basis q) at pv
  have rz : c.basis L.rmsb=false := prepare_rmsbF L hw hn R hr s [] hR hz
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have notLower (a : Wire) (ha : a∈L.carry) : a≠L.lower := fun e =>
    flagAway L hn L.lower (by simp) (by rw [←e];exact List.mem_append_right _ ha)
  have c248 : c.basis (cAt L 248)=false :=
    (pv.2.2 _ (carry_not_r L hn _ m248) (notLower _ m248)).trans (hc _ m248)
  have nd := EntryHalf5.carry_nodup L hn ctl hctl
  have clean : ∀a∈L.carry.take 255,c.basis a=false := by
    intro a ha
    have am := List.mem_of_mem_take ha
    exact (pv.2.2 a (carry_not_r L hn a am) (notLower a am)).trans (hc a am)
  have len := BalancedCleanup.widths L.toLayout hw
  have one (t : List Bool) := DiagonalCarry5.correct EntryHalf5.parityBits L.low (L.carry.take 255)
    L.lower ctl L.parity nd
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2]) c t clean
  have pc : cAt L 248≠L.parity := fun e =>
    flagAway L hn L.parity (by simp) (by rw [←e];exact List.mem_append_right _ m248)
  have rmem : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have pr : L.rmsb≠L.parity := fun e =>
    flagAway L hn L.parity (by simp) (by rw [←e];simp [rmem])
  have host (t : List Bool) :
      run (renameProgram (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L ctl)) t c=
        run (EntryHalf5.parityCarry L ctl) t c := by
    apply rebind_swap_run _ _ _ c t c248 rz
    · exact ((one t).2.1 _ pc).trans c248
    · exact ((one t).2.1 _ pr).trans rz
  have pm := (EntryHalf5.prepare_counts L).2
  have rc := renameProgram_counts (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L ctl)
  rw [positiveParityF,EntryHalf5.positiveParity,run_append,run_append (EntryHalf5.prepareMagnitude L),
    pm,List.take_zero,List.drop_zero,run_append,run_append (EntryHalf5.parityCarry L ctl),rc.2,host]

theorem recoverParityF_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (recoverParityF L J) m s=run (EntryHalf5.recoverParity L J) m s := by
  let u : State := ⟨s.phase,writeBit s.basis J (!s.basis J)⟩
  have away (q : Wire) (hq : q∈L.wires) : q≠J := fun e => hJ (e ▸ hq)
  have same (q : Wire) (hq : q∈L.wires) : u.basis q=s.basis q := by
    simp only [u,writeBit,Function.update_of_ne (away q hq)]
  have sameR : regValue L.r u.basis=encodeWord 256 R :=
    (regValue_congr _ _ _ (fun q hq => same q (by
      simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
        BalancedCleanup.Layout.low,List.mem_append,List.mem_cons,List.mem_singleton] at hq ⊢
      tauto))).trans hR
  have uz : u.basis L.lower=false := by
    rw [same _ (by simp [Layout.wires,BalancedCleanup.Layout.wires])];exact hz
  have uc : ∀q∈L.carry,u.basis q=false := fun q hq =>
    (same q (by simp [Layout.wires,BalancedCleanup.Layout.wires,hq])).trans (hc q hq)
  have first : run [.X J] [] s=u := by simp [u,run,writeBit]
  have cnt := (positiveParityF_counts L J).2
  have e := context_eq [.X J] (EntryHalf5.positiveParity L J) (positiveParityF L J) [.X J] 0 s m rfl
    (by rw [cnt,Nat.zero_add])
    (by
      intro r
      rw [first,List.drop_zero]
      exact positiveParityF_eq L hw hn J hJ R hr u r sameR uz uc)
  rw [recoverParityF,EntryHalf5.recoverParity,e,List.drop_zero,cnt,List.take_append_drop]

theorem clearParityF_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (clearParityF L J) m s=run (clearParity L J) m s := by
  let u : State := ⟨s.phase,writeBit s.basis L.parity (s.basis L.parity ^^ s.basis (L.ylow.getD 0 0))⟩
  have pa := flagAway L hn L.parity (by simp)
  have away (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity := fun e => pa (e ▸ hq)
  have lp : L.lower≠L.parity := by
    have nd := List.nodup_iff_count.mp (scalarND L hn) L.lower
    intro e;simp [e,List.count_cons] at nd;omega
  have ur : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hR
    intro q hq
    simp [u,writeBit,away q (by simp [hq])]
  have uz : u.basis L.lower=false := by simpa [u,writeBit,lp] using hz
  have uc : ∀q∈L.carry,u.basis q=false := fun q hq => by
    simpa [u,writeBit,away q (by simp [hq])] using hc q hq
  have first : run [.CX (L.ylow.getD 0 0) L.parity] [] s=u := by simp [run,u]
  rw [clearParityF,clearParity,run_append,run_append,
    show measurementCount [Instr.CX (L.ylow.getD 0 0) L.parity]=0 from rfl,List.take_zero,List.drop_zero,first]
  exact recoverParityF_eq L hw hn J hJ R hr u m ur uz uc

/-- `clearParity` with carry #4 on `one`, carry #254 on `sign` and carry #248 on `rmsb`. -/
def clearF (L : Layout) (J : Wire) : Program :=
  renameProgram (Equiv.swap (cHi L) L.sign) (renameProgram (Equiv.swap (cLo L) L.one) (clearParityF L J))

theorem clearF_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J : Wire) (hJ : J∉L.wires)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) (ho : s.basis L.one=false) (hs : s.basis L.sign=false) :
    run (clearF L J) m s=run (clearParity L J) m s := by
  have dist := hosts_distinct L hw hn
  have lo : cLo L∈L.carry := carry_mem L hw 4 (by decide)
  have hi : cHi L∈L.carry := carry_mem L hw 254 (by decide)
  have base := clearParityF_eq L hw hn J hJ R hr s m hR hl hc
  have cx := clear_xor L hw hn J hJ R hr s m hR hl hc
  have same (q : Wire) (hq : q≠L.parity) : (run (clearParityF L J) m s).basis q=s.basis q := by
    rw [base,cx]; simp [writeBit,hq]
  have innerEq : run (renameProgram (Equiv.swap (cLo L) L.one) (clearParityF L J)) m s=
      run (clearParityF L J) m s :=
    rebind_swap_run _ _ _ s m (hc _ lo) ho
      ((same _ (Ne.symm dist.2.2.1)).trans (hc _ lo))
      ((same _ (Ne.symm dist.2.2.2.2.2.2.1)).trans ho)
  rw [clearF,rebind_swap_run _ _ _ s m (hc _ hi) hs
    (by rw [innerEq];exact (same _ (Ne.symm dist.2.2.2.1)).trans (hc _ hi))
    (by rw [innerEq];exact (same _ (Ne.symm dist.2.2.2.2.2.2.2)).trans hs),innerEq,base]

end ECDSAAdd.Entrant.JointForward1588

namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588 Challenge Baselines RecordedQuantum

/-- Exact syntax slots of a literal carry chain: three per bit, four more per set literal bit. -/
theorem chain_slotsF (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    gateSlots (DiagonalCarry5.chain bs xs cs cin ctl target)=3*bs.length+4*bs.count true+1 := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    simp [DiagonalCarry5.chain,ex,ec,gateSlots,instructionSlots]
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have r := ih xs cs c (by simpa using hx) (by simpa using hc)
        have cell : gateSlots (mappedMajority (DiagonalCarry5.bit b) x cin c)+
            gateSlots (mappedEraseCarry (DiagonalCarry5.bit b) x cin c)=3+4*(if b then 1 else 0) := by
          cases b <;> norm_num [DiagonalCarry5.bit,mappedMajority,mappedEraseCarry,gateSlots,instructionSlots]
        simp only [DiagonalCarry5.chain,gateSlots_append,List.length_cons,List.count_cons]
        cases b <;> simp at cell ⊢ <;> omega

theorem parityBits_countF : EntryHalf5.parityBits.count true=7 := by decide

theorem parityCarry_slotsF (L : Layout) (hw : L.Widths) (J : Wire) :
    gateSlots (EntryHalf5.parityCarry L J)=794 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h := chain_slotsF EntryHalf5.parityBits L.low (L.carry.take 255) L.lower J L.parity
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
  rw [parityBits_countF,EntryHalf5.parityBits,DiagonalCarry5.literal_length] at h
  exact h

end ECDSAAdd.Entrant.JointForward1588

namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588 Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

/-- A renamed program avoids the first swapped site when the old program avoids the second. -/
theorem swap_free_leftF (a b : Wire) (P : Program) (hb : b∉wires P) :
    a∉wires (renameProgram (Equiv.swap a b) P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp used
  have back : x=b := by
    have h := congrArg (Equiv.swap a b) ex
    rwa [Equiv.swap_apply_self,Equiv.swap_apply_left] at h
  exact hb (back ▸ hx)

theorem prep_supportF (L : Layout) :
    wires (EntryHalf5.prepareMagnitude L)⊆(L.lower::L.r).toFinset := by
  intro q hq
  simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,wires_append,Finset.mem_union] at hq
  rcases hq with h|h
  · have e : q=L.rmsb ∨ q=L.lower := by simpa [wires,Instr.wires] using h
    rcases e with rfl|rfl
    · simp [BalancedCleanup.Layout.r]
    · simp
  · have h' := signComplement_wires_subset L.lower L.r h
    simpa only [List.mem_toFinset,List.mem_cons] using h'

theorem chain_supportF (L : Layout) (hw : L.Widths) (J : Wire) :
    wires (EntryHalf5.parityCarry L J)⊆(J::L.parity::L.lower::(L.low++L.carry.take 255)).toFinset := by
  have len := BalancedCleanup.widths L.toLayout hw
  exact DiagonalCarry5.support EntryHalf5.parityBits L.low (L.carry.take 255) L.lower J L.parity
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])

/-- The chain-hosted parity clear never touches `one`, `sign` or carry #248. -/
theorem clearParityF_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J : Wire) (hJ : J∉L.wires)
    (q : Wire) (hq : q=L.one ∨ q=L.sign ∨ q=cAt L 248) : q∉wires (clearParityF L J) := by
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have rmem : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have sc := scalarND L hn
  have qw : q∈L.wires := by
    rcases hq with rfl|rfl|rfl
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · exact data_member L _ (by simp [m248])
  have qJ : q≠J := fun e => hJ (e ▸ qw)
  have qr : q∉L.r := by
    rcases hq with rfl|rfl|rfl
    · exact fun h => flagAway L hn L.one (by simp) (by simp [h])
    · exact fun h => flagAway L hn L.sign (by simp) (by simp [h])
    · exact carry_not_r L hn _ m248
  have qu : q≠lowY L := by
    rcases hq with rfl|rfl|rfl
    · exact fun e => flagAway L hn L.one (by simp) (by rw [e];simp [y0])
    · exact fun e => flagAway L hn L.sign (by simp) (by rw [e];simp [y0])
    · exact fun e => y_not_carry L hn _ y0 (e ▸ m248)
  have qp : q≠L.parity := by
    rcases hq with rfl|rfl|rfl
    · intro e;have h := List.nodup_iff_count.mp sc L.parity;rw [←e] at h;simp [List.count_cons] at h;omega
    · intro e;have h := List.nodup_iff_count.mp sc L.parity;rw [←e] at h;simp [List.count_cons] at h;omega
    · exact fun e => flagAway L hn L.parity (by simp) (by rw [←e];exact List.mem_append_right _ m248)
  have ql : q≠L.lower := by
    rcases hq with rfl|rfl|rfl
    · intro e;have h := List.nodup_iff_count.mp sc L.lower;rw [←e] at h;simp [List.count_cons] at h;omega
    · intro e;have h := List.nodup_iff_count.mp sc L.lower;rw [←e] at h;simp [List.count_cons] at h;omega
    · exact fun e => flagAway L hn L.lower (by simp) (by rw [←e];exact List.mem_append_right _ m248)
  have prepF : q∉wires (EntryHalf5.prepareMagnitude L) := by
    intro used
    have m := List.mem_toFinset.mp (prep_supportF L used)
    simp only [List.mem_cons] at m
    rcases m with e|h
    · exact ql e
    · exact qr h
  have lowR (x : Wire) (hx : x∈L.low) : x∈L.r := by simp [BalancedCleanup.Layout.r,hx]
  have chainF : q∉wires (renameProgram (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L J)) := by
    rcases hq with rfl|rfl|rfl
    · apply swap_freeF _ _ _ _ _ (fun e => flagAway L hn L.one (by simp) (by rw [e];exact List.mem_append_right _ m248))
        (fun e => flagAway L hn L.one (by simp) (by rw [e];simp [rmem]))
      intro used
      have m := List.mem_toFinset.mp (chain_supportF L hw J used)
      simp only [List.mem_cons,List.mem_append] at m
      rcases m with e|e|e|h|h
      · exact qJ e
      · exact qp e
      · exact ql e
      · exact qr (lowR _ h)
      · exact flagAway L hn L.one (by simp) (List.mem_append_right _ (List.mem_of_mem_take h))
    · apply swap_freeF _ _ _ _ _ (fun e => flagAway L hn L.sign (by simp) (by rw [e];exact List.mem_append_right _ m248))
        (fun e => flagAway L hn L.sign (by simp) (by rw [e];simp [rmem]))
      intro used
      have m := List.mem_toFinset.mp (chain_supportF L hw J used)
      simp only [List.mem_cons,List.mem_append] at m
      rcases m with e|e|e|h|h
      · exact qJ e
      · exact qp e
      · exact ql e
      · exact qr (lowR _ h)
      · exact flagAway L hn L.sign (by simp) (List.mem_append_right _ (List.mem_of_mem_take h))
    · apply swap_free_leftF
      intro used
      have m := List.mem_toFinset.mp (chain_supportF L hw J used)
      have rw' : L.rmsb∈L.wires := data_member L _ (by simp [rmem])
      have nr := EntryHalf5.target_nodup L hn
      simp only [List.mem_cons,List.mem_append] at m
      rcases m with e|e|e|h|h
      · exact hJ (e ▸ rw')
      · exact flagAway L hn L.parity (by simp) (by rw [←e];simp [rmem])
      · exact flagAway L hn L.lower (by simp) (by rw [←e];simp [rmem])
      · simp only [BalancedCleanup.Layout.r] at nr
        exact (List.nodup_append'.mp nr).2.2 h (by simp)
      · exact carry_not_r L hn _ (List.mem_of_mem_take h) rmem
  simp only [clearParityF,recoverParityF,positiveParityF,wires_append,wires_reverse,Finset.mem_union,not_or]
  refine ⟨?_,⟨⟨?_,prepF,chainF,prepF⟩,?_⟩⟩
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,
      or_false,not_or]
    exact ⟨qu,qp⟩
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false]
    exact qJ
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false]
    exact qJ

theorem clearParityF_support (L : Layout) (J : Wire) (W : Finset Wire)
    (hP : wires (clearParity L J)⊆W) (h248 : cAt L 248∈W) (hr : L.rmsb∈W) :
    wires (clearParityF L J)⊆W := by
  simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,wires_append,wires_reverse,
    Finset.union_subset_iff] at hP
  simp only [clearParityF,recoverParityF,positiveParityF,wires_append,wires_reverse,Finset.union_subset_iff]
  exact ⟨hP.1,⟨⟨hP.2.1.1,hP.2.1.2.1,swap_supportF _ _ _ _ hP.2.1.2.2.1 h248 hr,hP.2.1.2.1⟩,hP.2.2⟩⟩

theorem clearParityF_physical (L : Layout) (J : Wire) (hP : GatePhysical (clearParity L J)) :
    GatePhysical (clearParityF L J) := by
  simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,gatePhysical_append] at hP
  simp only [clearParityF,recoverParityF,positiveParityF,gatePhysical_append]
  exact ⟨hP.1,⟨⟨hP.2.1.1,hP.2.1.2.1,gatePhysical_rename _ (Equiv.swap _ _).injective _ hP.2.1.2.2.1,
    hP.2.1.2.2.2⟩,hP.2.2⟩⟩

theorem clearParityF_counts (L : Layout) (hw : L.Widths) (J : Wire) :
    toffoliCount (clearParityF L J)=256 ∧ measurementCount (clearParityF L J)=255 := by
  have p := positiveParityF_counts L J
  have c := clearParity_counts L hw J
  simp only [clearParity,EntryHalf5.recoverParity,toffoliCount_append,measurementCount_append] at c
  simp only [clearParityF,recoverParityF,toffoliCount_append,measurementCount_append,p.1,p.2]
  exact c

theorem clearParityF_slots (L : Layout) (hw : L.Widths) (J : Wire) :
    gateSlots (clearParityF L J)=1311 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have mag : gateSlots (EntryHalf5.prepareMagnitude L)=257 := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,gateSlots_append,
      gateSlots_cons,gateSlots_nil,instructionSlots,signComplement_gateSlots,len.2.1]
  have ch := parityCarry_slotsF L hw J
  simp only [clearParityF,recoverParityF,positiveParityF,gateSlots_append,reverse_gateSlots,
    rename_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,mag,ch]

/-- The four extra carry-#1 instructions only touch source bit 1, `r1` and carries #0/#1. -/
theorem loanF_edge_support (L : Layout) :
    wires (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))⊆
      ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset ∧
    wires (Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))⊆
      ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset := by
  have b := Affine.local_support (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
    ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset
    (fun q hq => List.mem_toFinset.mpr (List.mem_append_left _ hq))
    (by simp) (by simp) (by simp)
  exact ⟨b.2.1,b.1⟩

theorem source1_sitesF (L : Layout) (q : Wire) (hq : q∈(source L 1).wires) : q=L.one ∨ q=L.sign := by
  simpa [source,Affine.Bit.wires] using hq

theorem loanF_slots (L : Layout) (J B : Wire) : gateSlots (loanF L J B)=gateSlots (inner L)+20 := by
  have a : gateSlots ([Instr.measureX L.sign [] [Correction.CZ L.lower (lowY L)],
      Instr.measureX (lowY L) [] [Correction.CZ J B]] : Program)=4 := rfl
  have b : gateSlots ([Instr.CCX J B (lowY L),Instr.CCX L.lower (lowY L) L.sign] : Program)=2 := rfl
  have ls := Affine.local_slots (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
  have t1 : (source L 1).terms.length=1 := by simp [source]
  simp only [loanF,loanW,gateSlots_append,rename_gateSlots,a,b,ls.1,ls.2.1,t1]
  omega

end ECDSAAdd.Entrant.JointForward1588

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588
attribute [local irreducible] run

/-- The forward addition with carry #4 on `lowY`, carry #254 on `sign` and (measured loan of carry #1)
carry #248 on carry #1's site inside source bits 4..255. -/
def arithH (L : Layout) (J B : Wire) : Program :=
  pre4 L++loanF L J B++post4 L

/-- `EntryRetained5.program` with the hosted carries (#4, #254, and #248 retired from its own site). -/
def programF (L : Layout) (J B : Wire) : Program :=
  prepare L J B++arithH L J B++eraseScalarsAt L J B++clearF L J

theorem pre4_keep (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (b : State) (q : Wire)
    (hc : ∀i,i<4 → q≠cAt L i) :
    (run (pre4 L) [] b).basis q=b.basis q ∧ (run (pre4 L) [] b).phase=b.phase := by
  have p := pre4_run L hw hn b []
  exact ⟨p.2 q (hc 0 (by decide)) (hc 1 (by decide)) (hc 2 (by decide)) (hc 3 (by decide)),p.1⟩

/-- The final parity clear with carries #4 and #254 on the cleared `one` and `sign` (and carry #248 on
`rmsb`) runs as the record's `clearParity` on every state reached by the forward prefix and the scalar
erasure. -/
theorem tail_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (t1 t2 n : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    run (clearF L J) n (run (eraseScalarsAt L J B) t2 (run (prefixProgram L J B) t1 s))=
      run (clearParity L J) n (run (eraseScalarsAt L J B) t2 (run (prefixProgram L J B) t1 s)) := by
  have pref := prefix_spec L hw hn J B hJ hB hJB Jv Bv Y hy s t1 hR hY hc hz hj hb
  generalize hbdef : run (prefixProgram L J B) t1 s=b at pref ⊢
  have dd : b.basis L.one=(b.basis L.parity && b.basis (lowY L)) := by
    rw [pref.parity,pref.u]
    exact pref.d
  have ee : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)) := by
    rw [pref.a,pref.u]
    exact pref.e
  have uu : b.basis (lowY L)=(b.basis J && b.basis B) := by rw [pref.u,pref.j,pref.b]
  have aa:=scalar_erase_relation L hw Jv Bv Y hy b.basis pref.target pref.parity pref.a pref.d
  generalize hcdef : run (eraseScalarsAt L J B) t2 b=c
  have erased : c=⟨b.phase,erasedBasis L.parity L.lower L.one L.sign (lowY L) J b.basis⟩ := by
    rw [←hcdef]
    exact eraseScalarsAt_run L hw hn J B hJ hB hJB b t2 ee aa dd uu
  have en:=erasePorts_nodup L hw hn J B hJ hB hJB
  have nd:=allND L hn
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have data : (L.r++L.y++L.carry).Nodup := (List.nodup_append'.mp nd).2.1
  have ry : (L.r++L.y).Nodup := (List.nodup_append'.mp data).1
  have rdy := (List.nodup_append'.mp ry).2.2
  have dyc := (List.nodup_append'.mp data).2.2
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r++L.y++L.carry := by
    have mem : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢
      tauto
    exact flagAway L hn q mem
  have cSame (q : Wire) (hq : q∈L.r++L.carry) : c.basis q=b.basis q := by
    have qdata : q∈L.r++L.y++L.carry := by
      simp only [List.mem_append] at hq ⊢
      tauto
    have qu : q≠lowY L := by
      intro eq
      rcases List.mem_append.mp hq with qr|qc
      · exact List.disjoint_left.mp rdy qr (eq.symm ▸ y0)
      · exact List.disjoint_left.mp dyc (List.mem_append_right _ y0) (eq ▸ qc)
    have qf (f : Wire) (hf : f∈[L.parity,L.lower,L.one,L.sign]) : q≠f := fun e=>flag f hf (e ▸ qdata)
    rw [erased]
    exact erasedBasis_frame _ _ _ _ _ _ _ q (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      exact not_or_intro (qf _ (by simp)) (not_or_intro (qf _ (by simp))
        (not_or_intro (qf _ (by simp)) qu)))
  have cR : regValue L.r c.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) :=
    (regValue_congr _ _ _ (fun q hq=>cSame q (List.mem_append_left _ hq))).trans pref.target
  have cCarry : ∀q∈L.carry,c.basis q=false := fun q hq=>
    (cSame q (List.mem_append_right _ hq)).trans (pref.carry q hq)
  have ca : c.basis L.lower=false := by
    have ne : L.lower≠lowY L := by
      intro e;exact flag L.lower (by simp) (by simp [e,y0])
    have ad : L.lower≠L.one := by
      have h:=List.nodup_iff_count.mp en L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,ne,ad]
  have bounds:=signedY_bounds (Jv && Bv) Y hy
  have rc : Centered (halfResult (signedY (Jv && Bv) Y)) := by
    apply (halfResult_spec _ ?_).1
    have hp:=constants
    unfold Centered at bounds
    omega
  have notU (q : Wire) (hq : q=L.one ∨ q=L.sign) : q≠lowY L := by
    intro e
    have f := flagAway L hn q (by rcases hq with rfl|rfl <;> simp)
    exact f (by rw [e];simp [y0])
  have cOne : c.basis L.one=false := by
    rw [erased]
    simp [erasedBasis,writeBit,notU L.one (Or.inl rfl)]
  have cSign : c.basis L.sign=false := by
    have sa : L.sign≠L.lower := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    have sd : L.sign≠L.one := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,notU L.sign (Or.inr rfl),sa,sd]
  exact clearF_eq L hw hn J hJ _ rc c n cR ca cCarry cOne cSign

/-- The hosted forward program runs as `EntryRetained5.program` on the entry frame, for a
re-aligned record list. -/
theorem programF_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    ∃m',run (programF L J B) m s=run (EntryRetained5.program L J B) m' s := by
  let Pre := prepare L J B++pre4 L
  let Q := loanF L J B
  let Post := post4 L++eraseScalarsAt L J B++clearF L J
  have shapeF : programF L J B=Pre++Q++Post := by
    simp only [programF,arithH,Pre,Q,Post,List.append_assoc]
  have prep := prepare_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  have pc := prepare_counts L hw J B
  have preRun : run Pre [] s=run (pre4 L) [] (run (prepare L J B) [] s) := by
    simp only [Pre,run_append,List.take_nil,List.drop_nil]
  have hpre : measurementCount Pre=0 := by
    simp only [Pre,measurementCount_append,pc.2,(pre4_counts L).2]
  have stepA := context_eq Pre (inner L) Q Post 3 s m hpre (loanF_counts L J B).2 (by
    intro r
    rw [preRun]
    exact loanF_run L hw hn J B hJ hB hJB _ r
      (by rw [prep.a,prep.u];exact prep.e)
      (by rw [prep.u,prep.j,prep.b])
      prep.carry)
  refine ⟨(m.drop 3).take (measurementCount (inner L))++m.drop (measurementCount Q),?_⟩
  rw [shapeF,stepA]
  generalize (m.drop 3).take (measurementCount (inner L))++m.drop (measurementCount Q)=n
  have shape1 : Pre++inner L++Post=(prefixProgram L J B++eraseScalarsAt L J B)++clearF L J := by
    simp only [Pre,Post,prefixProgram,arithmetic,add_split L hw,List.append_assoc]
  have shape2 : EntryRetained5.program L J B=
      (prefixProgram L J B++eraseScalarsAt L J B)++clearParity L J := rfl
  rw [shape1,shape2,run_append,run_append (prefixProgram L J B++eraseScalarsAt L J B),
    run_append (prefixProgram L J B)]
  exact tail_eq L hw hn J B hJ hB hJB Jv Bv Y hy s _ _ _ hR hY hc hz hj hb

end ECDSAAdd.Entrant.JointForward1588


/-! ### The hosted forward joint entry -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588 Secp256k1

def jointF (L : BalancedCircuit.Layout) (J G : Wire) : Program :=
  [.X G]++programF L J G++[.X G]

theorem xwrap_run (G : Wire) (P : Program) (m : List Bool) (s : State) :
    run ([.X G]++P++[.X G]) m s=run [.X G] [] (run P m (run [.X G] [] s)) := by
  have xm : measurementCount [Instr.X G]=0 := rfl
  have any (r : List Bool) (t : State) : run [Instr.X G] r t=run [Instr.X G] [] t := by
    have h := run_take [Instr.X G] r t
    rw [xm,List.take_zero] at h
    exact h.symm
  rw [run_append ([Instr.X G]++P) [Instr.X G],any,run_append [Instr.X G] P,xm,List.take_zero,
    List.drop_zero,measurementCount_append,xm,Nat.zero_add,run_take]

private theorem outside_layoutF (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q ∉ L.wires) : q ∉ L.r ∧ q ∉ L.y ∧ q ∉ BalancedCircuit.work L := by
  have zero := List.count_eq_zero.mpr hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    List.count_append,List.count_cons,List.count_nil] at zero
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at pos
    omega
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at pos
    omega
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at pos
    omega

/-- The hosted forward joint runs as `FrontierEntry.joint` on the entry frame. -/
theorem jointF_eq (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J,G].Nodup)
    (Jv Gv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 Y)
    (hY : regValue L.y s.basis = 0)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false)
    (sign : s.basis L.sign=false) (j : s.basis J=Jv) (g : s.basis G=Gv) :
    ∃m',run (jointF L J G) m s=run (FrontierEntry.joint L J G) m' s := by
  have apart : J≠G := fun eq => (List.nodup_cons.mp hJG).1 (List.mem_singleton.mpr eq)
  have away := outside_layoutF L G hG
  let a : State := ⟨s.phase,writeBit s.basis G (!s.basis G)⟩
  have head : run [Instr.X G] [] s=a := rfl
  have keep (q : Wire) (hq : q≠G) : a.basis q=s.basis q := by
    simp only [a,writeBit,Function.update_of_ne hq]
  have aR : regValue L.r a.basis=encodeWord 256 Y :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.1 (eq ▸ hq)))).trans hR
  have aY : regValue L.y a.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.2.1 (eq ▸ hq)))).trans hY
  have ac : ∀q∈BalancedCircuit.work L,a.basis q=false := by
    intro q hq
    exact (keep q (fun eq => away.2.2 (eq ▸ hq))).trans (clean q hq)
  have sign_mem : L.sign∈L.wires := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have sg : L.sign≠G := fun eq => hG (eq ▸ sign_mem)
  have aj : a.basis J=Jv := (keep J apart).trans j
  have ag : a.basis G= !Gv := by simp only [a,writeBit,Function.update_self,g]
  obtain ⟨m',h⟩ := programF_eq L hw hn J G hJ hG hJG Jv (!Gv) Y hy a m aR aY ac
    ((keep _ sg).trans sign) aj ag
  refine ⟨m',?_⟩
  rw [jointF,xwrap_run,FrontierEntry.joint,xwrap_run,head,h]

/-- `(Z, 0) ↦ ((±Z)/2, J ? Z : 0)`: the first selector swap and the G1 half of the divide replay. -/
theorem jointF_pair (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (origin : BasisState) (clean : ∀q∈work L,origin q=false) (sign : origin L.sign=false)
    (Z : Fp) :
    Triple (PairFrame L.r L.y origin (centerWord Z) 0) (jointF L J G)
      (PairFrame L.r L.y origin
        (centerWord ((if origin J && !origin G then -Z else Z)/2))
        (centerWord (if origin J then Z else 0))) := by
  have outside (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
  have sf:=flagAway L hn L.sign (by simp)
  have sa : L.sign∉L.r ∧ L.sign∉L.y :=
    ⟨fun bad=>sf (by simp [bad]),fun bad=>sf (by simp [bad])⟩
  intro s m h
  have hc : ∀q∈work L,s.basis q=false := fun q hq=>
    (h.2.2 q (work_no_data L hn q hq).1 (work_no_data L hn q hq).2).trans (clean q hq)
  have ss : s.basis L.sign=false := (h.2.2 _ sa.1 sa.2).trans sign
  have sj : s.basis J=origin J := h.2.2 _ (outside J hJ).1 (outside J hJ).2
  have sg : s.basis G=origin G := h.2.2 _ (outside G hG).1 (outside G hG).2
  obtain ⟨m',eq⟩ := jointF_eq L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m h.1 h.2.1 hc ss sj sg
  have out := FrontierEntry.joint_frame L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m' h.1 h.2.1 hc ss sj sg
  dsimp only at out
  rw [unary_half,source_word] at out
  rw [eq]
  exact ⟨out.1,out.2.1,out.2.2.1,fun q qr qy=>(out.2.2.2 q qr qy).trans (h.2.2 q qr qy)⟩

end ECDSAAdd.Entrant.JointForward1588


/-! ### Resources, support and physicality of the hosted forward joint -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588
  Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

theorem programF_counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (programF L J B)=774 ∧ measurementCount (programF L J B)=517 := by
  have p:=prepare_counts L hw J B
  have i:=inner_counts L hw
  have w:=loanF_counts L J B
  have e:=eraseScalars_counts L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J B L.rmsb
  have c:=clearParityF_counts L hw J
  have c1:=renameProgram_counts (Equiv.swap (cLo L) L.one) (clearParityF L J)
  have c2:=renameProgram_counts (Equiv.swap (cHi L) L.sign)
    (renameProgram (Equiv.swap (cLo L) L.one) (clearParityF L J))
  simp only [programF,arithH,clearF,eraseScalarsAt,toffoliCount_append,measurementCount_append,
    p.1,p.2,w.1,w.2,i.1,i.2,e.1,e.2,c.1,c.2,c1.1,c1.2,c2.1,c2.2,(pre4_counts L).1,(pre4_counts L).2,
    (post4_counts L).1,(post4_counts L).2]
  all_goals simp

theorem jointF_counts (L : Layout) (hw : L.Widths) (J G : Wire) :
    toffoliCount (jointF L J G)=774 ∧ measurementCount (jointF L J G)=517 := by
  have h:=programF_counts L hw J G
  simpa only [jointF,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,Nat.zero_add,Nat.add_zero] using h

theorem programF_slots (L : Layout) (hw : L.Widths) (J B : Wire) :
    gateSlots (programF L J B)≤7975 := by
  have prep:=prepare_slots_le L hw J B
  have arith:=arithmetic_slots L hw
  have par:=clearParityF_slots L hw J
  have er : gateSlots (eraseScalarsAt L J B)=11 := rfl
  have split : gateSlots (pre4 L)+gateSlots (inner L)+gateSlots (post4 L)=4369 := by
    rw [←arith,show arithmetic L=pre4 L++inner L++post4 L from add_split L hw]
    simp only [gateSlots_append]
  have loanS := loanF_slots L J B
  simp only [programF,arithH,clearF,gateSlots_append,rename_gateSlots,er,loanS,par]
  omega

theorem jointF_slots (L : Layout) (hw : L.Widths) (J G : Wire) : gateSlots (jointF L J G)≤7977 := by
  have h := programF_slots L hw J G
  have x : gateSlots [Instr.X G]=1 := rfl
  simp only [jointF,gateSlots_append,x]
  omega

theorem programF_support (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J B : Wire) :
    wires (programF L J B)⊆retSites L J B := by
  have old:=EntryRetained5.program_support L hw J B
  have parts : ((wires (prepare L J B)⊆retSites L J B ∧ wires (arithmetic L)⊆retSites L J B) ∧
      wires (eraseScalarsAt L J B)⊆retSites L J B) ∧ wires (clearParity L J)⊆retSites L J B := by
    simpa only [EntryRetained5.program,prefixProgram,wires_append,Finset.union_subset_iff] using old
  have r (q : Wire) (hq : q∈L.r) : q∈retSites L J B := by simp [retSites,hq]
  have y (q : Wire) (hq : q∈L.y) : q∈retSites L J B := by simp [retSites,hq]
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have rh : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have ha : L.lower∈retSites L J B := by simp [retSites]
  have hd : L.one∈retSites L J B := by simp [retSites]
  have he : L.sign∈retSites L J B := by simp [retSites]
  have hj : J∈retSites L J B := by simp [retSites]
  have hb : B∈retSites L J B := by simp [retSites]
  have hu := y (lowY L) y0
  have carryIn (i : Nat) (hi : i<255) : L.carry.getD i 0∈retSites L J B := by
    have m := carry_take_mem L hw i hi
    simp only [retSites,List.mem_toFinset,List.mem_append]
    exact Or.inl (Or.inr m)
  have r1 : rAt L 1∈retSites L J B := by
    apply r
    have len := BalancedCleanup.widths L.toLayout hw
    have lt : 1<L.r.length := by rw [len.2.1];decide
    simp only [rAt,List.getD_eq_getElem _ _ lt]
    exact List.getElem_mem lt
  have split := pre4_post4_support L hw
  have clearS : wires (clearF L J)⊆retSites L J B :=
    swap2_support _ _ _ _ _ _ (clearParityF_support L J _ parts.2 (carryIn 248 (by decide)) (r _ rh))
      (carryIn 4 (by decide)) hd (carryIn 254 (by decide)) he
  have edgeS : ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset⊆retSites L J B := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with h|rfl|rfl|rfl
    · rcases source1_sitesF L q h with rfl|rfl
      · exact hd
      · exact he
    · exact r1
    · exact carryIn 0 (by decide)
    · exact carryIn 1 (by decide)
  have es := loanF_edge_support L
  have loan : wires (loanF L J B)⊆retSites L J B := by
    simp only [loanF,loanW,wires_append,Finset.union_subset_iff]
    refine ⟨es.1.trans edgeS,⟨⟨?_,swap2_support _ _ _ _ _ _
      (swap_supportF _ _ _ _ (split.2.1.trans parts.1.1.2) (carryIn 248 (by decide)) (carryIn 1 (by decide)))
      (carryIn 4 (by decide)) hu (carryIn 254 (by decide)) he⟩,?_⟩,es.2.trans edgeS⟩
    · simp [wires,Instr.wires,correctionWires,Finset.insert_subset_iff,Finset.union_subset_iff,he,ha,hu,hj,hb]
    · simp [wires,Instr.wires,Finset.insert_subset_iff,Finset.union_subset_iff,he,ha,hu,hj,hb]
  simp only [programF,arithH,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨parts.1.1.1,⟨⟨split.1.trans parts.1.1.2,loan⟩,split.2.2.trans parts.1.1.2⟩⟩,parts.1.2⟩,clearS⟩

theorem jointF_support (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J G : Wire) :
    wires (jointF L J G)⊆retSites L J G := by
  have g : G∈retSites L J G := by simp [retSites]
  have x : wires [Instr.X G]⊆retSites L J G := by
    intro q hq
    have : q=G := by simpa [wires,Instr.wires] using hq
    rw [this];exact g
  simp only [jointF,wires_append,Finset.union_subset_iff]
  exact ⟨⟨x,programF_support L hw hn J G⟩,x⟩

theorem programF_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (q : Wire) (hq : q=cLo L ∨ q=cHi L ∨ q=cAt L 248) : q∉wires (programF L J B) := by
  have dist := ports_distinct L hw hn J B hJ hB hJB
  have hd := hosts_distinct L hw hn
  have nd7 := dist.1
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd7
  rcases nd7 with ⟨⟨sl,su,sj,sb,slo,shi⟩,⟨⟨lu,lj,lb,llo,lhi⟩,⟨⟨uj,ub,ulo,uhi⟩,
    ⟨⟨jb,jlo,jhi⟩,⟨⟨blo,bhi⟩,lohi⟩⟩⟩⟩⟩
  have qc : q∈L.carry := by
    rcases hq with rfl|rfl|rfl
    · exact carry_mem L hw 4 (by decide)
    · exact carry_mem L hw 254 (by decide)
    · exact carry_mem L hw 248 (by decide)
  have qr : q∉L.r := carry_not_r L hn q qc
  have qy : q∉L.y := fun h => y_not_carry L hn q h qc
  have flagNe (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q≠f := fun e => flagAway L hn f hf (by rw [←e];simp [qc])
  have qJ : q≠J := fun e => hJ (e ▸ data_member L q (by simp [qc]))
  have qB : q≠B := fun e => hB (e ▸ data_member L q (by simp [qc]))
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have qu : q≠lowY L := fun e => qy (e ▸ y0)
  have qlow (i : Nat) (hi : i<4) : q≠cAt L i := by
    rcases hq with rfl|rfl|rfl
    · exact carry_index_ne L hw hn 4 i (by decide) (by omega) (by omega)
    · exact carry_index_ne L hw hn 254 i (by decide) (by omega) (by omega)
    · exact carry_index_ne L hw hn 248 i (by decide) (by omega) (by omega)
  have qsite (h : q∈Affine.sites (sources L)) : False := by
    have m := sources_sites L q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with e|e|e|e
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
  have rmem (i : Nat) (hi : i<4) : rAt L i∈L.r := by
    have len := BalancedCleanup.widths L.toLayout hw
    have lt : i<L.r.length := by rw [len.2.1];omega
    simp only [rAt,List.getD_eq_getElem _ _ lt]
    exact List.getElem_mem lt
  have edge (P : Program) (hP : wires P⊆(Affine.sites (sources L)++[rAt L 0,rAt L 1,rAt L 2,rAt L 3,
      lowY L,cAt L 0,cAt L 1,cAt L 2,cAt L 3]).toFinset) : q∉wires P := by
    intro used
    have m := List.mem_toFinset.mp (hP used)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with h|e|e|e|e|e|e|e|e|e
    · exact qsite h
    · exact qr (e ▸ rmem 0 (by decide))
    · exact qr (e ▸ rmem 1 (by decide))
    · exact qr (e ▸ rmem 2 (by decide))
    · exact qr (e ▸ rmem 3 (by decide))
    · exact qu e
    · exact qlow 0 (by decide) e
    · exact qlow 1 (by decide) e
    · exact qlow 2 (by decide) e
    · exact qlow 3 (by decide) e
  have es := edge_support L
  have c248lo : cAt L 248≠cLo L := carry_index_ne L hw hn 248 4 (by decide) (by decide) (by decide)
  have c248hi : cAt L 248≠cHi L := carry_index_ne L hw hn 248 254 (by decide) (by decide) (by decide)
  have clearFr : q∉wires (clearF L J) := by
    rcases hq with h|h|h
    · exact swap2_free (cLo L) L.one (cHi L) L.sign (clearParityF L J)
        (clearParityF_free L hw hn J hJ L.one (Or.inl rfl))
        (clearParityF_free L hw hn J hJ L.sign (Or.inr (Or.inl rfl)))
        hd.2.2.2.2.2.1 (Ne.symm slo) (Ne.symm hd.2.2.2.2.1) q (Or.inl h)
    · exact swap2_free (cLo L) L.one (cHi L) L.sign (clearParityF L J)
        (clearParityF_free L hw hn J hJ L.one (Or.inl rfl))
        (clearParityF_free L hw hn J hJ L.sign (Or.inr (Or.inl rfl)))
        hd.2.2.2.2.2.1 (Ne.symm slo) (Ne.symm hd.2.2.2.2.1) q (Or.inr h)
    · rw [h] at flagNe
      rw [h]
      exact swap_freeF _ _ _ _ (swap_freeF _ _ _ _
        (clearParityF_free L hw hn J hJ _ (Or.inr (Or.inr rfl))) c248lo (flagNe L.one (by simp)))
        c248hi (flagNe L.sign (by simp))
  have eraseSub : wires (eraseScalarsAt L J B)⊆
      ([L.parity,L.lower,L.one,L.sign,lowY L,J,B,L.rmsb] : List Wire).toFinset := by
    intro x hx
    simp only [eraseScalarsAt,eraseScalars,wires,Instr.wires,correctionWires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hx
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    change x=L.parity ∨ x=L.lower ∨ x=L.one ∨ x=L.sign ∨ x=L.ylow.getD 0 0 ∨ x=J ∨ x=B ∨ x=L.rmsb
    tauto
  have rh : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have eraseF : q∉wires (eraseScalarsAt L J B) := by
    intro used
    have m := List.mem_toFinset.mp (eraseSub used)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with e|e|e|e|e|e|e|e
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
    · exact qu e
    · exact qJ e
    · exact qB e
    · exact qr (e ▸ rh)
  have sc := scalarND L hn
  have uIn : lowY L∉wires (inner L) := inner_free L hw hn _ (fun h => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e
        · exact flagAway L hn L.parity (by simp) (by rw [←e];simp [y0])
        · exact flagAway L hn L.lower (by simp) (by rw [←e];simp [y0])
        · exact flagAway L hn L.one (by simp) (by rw [←e];simp [y0]))
        (y_not_r L hn _ y0) (y_not_carry L hn _ y0)
  have eIn : L.sign∉wires (inner L) := inner_free L hw hn _ (fun h => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e <;>
          (have c := List.nodup_iff_count.mp sc L.sign
           rw [e] at c;simp [List.count_cons] at c;omega))
        (fun h => flagAway L hn L.sign (by simp) (by simp [h]))
        (fun h => flagAway L hn L.sign (by simp) (by simp [h]))
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have m1 : cAt L 1∈L.carry := carry_mem L hw 1 (by decide)
  have uP : lowY L∉wires (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) :=
    swap_freeF _ _ _ _ uIn (fun e => y_not_carry L hn _ y0 (e ▸ m248)) (fun e => y_not_carry L hn _ y0 (e ▸ m1))
  have eP : L.sign∉wires (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) :=
    swap_freeF _ _ _ _ eIn (fun e => flagAway L hn L.sign (by simp) (by rw [e];exact List.mem_append_right _ m248))
      (fun e => flagAway L hn L.sign (by simp) (by rw [e];exact List.mem_append_right _ m1))
  have innerF : q∉wires (renameProgram (Equiv.swap (cHi L) L.sign)
      (renameProgram (Equiv.swap (cLo L) (lowY L))
        (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)))) := by
    rcases hq with h|h|h
    · exact swap2_free (cLo L) (lowY L) (cHi L) L.sign _ uP eP hd.2.2.2.2.2.1 (Ne.symm slo) su q (Or.inl h)
    · exact swap2_free (cLo L) (lowY L) (cHi L) L.sign _ uP eP hd.2.2.2.2.2.1 (Ne.symm slo) su q (Or.inr h)
    · rw [h] at flagNe qu
      rw [h]
      exact swap_freeF _ _ _ _ (swap_freeF _ _ _ _ (swap_free_leftF _ _ _ ((low_inner_freeF L hw hn).1 1 (by decide)))
        c248lo qu) c248hi (flagNe L.sign (by simp))
  have edgeSub : wires ([.measureX L.sign [] [.CZ L.lower (lowY L)],.measureX (lowY L) [] [.CZ J B]] : Program)∪
      wires ([.CCX J B (lowY L),.CCX L.lower (lowY L) L.sign] : Program)⊆
      ([L.sign,L.lower,lowY L,J,B] : List Wire).toFinset := by
    intro x hx
    simp only [wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false,Finset.union_empty] at hx
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  have edgeF : q∉([L.sign,L.lower,lowY L,J,B] : List Wire).toFinset := by
    intro h
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with e|e|e|e|e
    · exact flagNe L.sign (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact qu e
    · exact qJ e
    · exact qB e
  have ls := loanF_edge_support L
  have edge1 (P : Program) (hP : wires P⊆((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset) :
      q∉wires P := by
    intro used
    have m := List.mem_toFinset.mp (hP used)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with h|e|e|e
    · rcases source1_sitesF L q h with e|e
      · exact flagNe L.one (by simp) e
      · exact flagNe L.sign (by simp) e
    · exact qr (e ▸ rmem 1 (by decide))
    · exact qlow 0 (by decide) e
    · exact qlow 1 (by decide) e
  have loanFr : q∉wires (loanF L J B) := by
    simp only [loanF,loanW,wires_append,Finset.mem_union,not_or]
    exact ⟨edge1 _ ls.1,⟨⟨fun h => edgeF (edgeSub (Finset.mem_union_left _ h)),innerF⟩,
      fun h => edgeF (edgeSub (Finset.mem_union_right _ h))⟩,edge1 _ ls.2⟩
  have prepF : q∉wires (prepare L J B) := by
    intro used
    have m := List.mem_toFinset.mp (prepare_support L hw J B used)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with (h|h)|e|e|e|e|e|e
    · exact qr h
    · exact qy h
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
    · exact qJ e
    · exact qB e
  simp only [programF,arithH,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨prepF,⟨⟨edge _ es.1,loanFr⟩,edge _ es.2⟩⟩,eraseF⟩,clearFr⟩

theorem jointF_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (q : Wire) (hq : q=cLo L ∨ q=cHi L ∨ q=cAt L 248) : q∉wires (jointF L J G) := by
  have core := programF_free L hw hn J G hJ hG hJG q hq
  have qc : q∈L.carry := by
    rcases hq with rfl|rfl|rfl
    · exact carry_mem L hw 4 (by decide)
    · exact carry_mem L hw 254 (by decide)
    · exact carry_mem L hw 248 (by decide)
  have qG : q≠G := fun e => hG (e ▸ data_member L q (by simp [qc]))
  simp only [jointF,wires_append,Finset.mem_union,not_or]
  refine ⟨⟨?_,core⟩,?_⟩ <;> simp [wires,Instr.wires,qG]

theorem programF_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup) :
    GatePhysical (programF L J B) := by
  have old:=EntryRetained5.program_physical L hw hn J B hJ hB hJB
  have parts : ((GatePhysical (prepare L J B) ∧ GatePhysical (arithmetic L)) ∧
      GatePhysical (eraseScalarsAt L J B)) ∧ GatePhysical (clearParity L J) := by
    simpa only [EntryRetained5.program,prefixProgram,gatePhysical_append] using old
  have n:=erasePorts_nodup L hw hn J B hJ hB hJB
  have ctr : L.lower≠L.sign ∧ (lowY L)≠L.sign ∧ J≠lowY L ∧ B≠lowY L := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at n
    rcases n with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
      ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
    exact ⟨aE,Ne.symm eU,Ne.symm uJ,Ne.symm uB⟩
  have jb : J≠B := by
    intro e
    simp [e] at hJB
  have arith : GatePhysical (pre4 L) ∧ GatePhysical (inner L) ∧ GatePhysical (post4 L) := by
    have h := parts.1.1.2
    rw [show arithmetic L=pre4 L++inner L++post4 L from add_split L hw] at h
    simp only [gatePhysical_append] at h
    exact ⟨h.1.1,h.1.2,h.2⟩
  have clear : GatePhysical (clearF L J) :=
    gatePhysical_rename _ (Equiv.swap _ _).injective _
      (gatePhysical_rename _ (Equiv.swap _ _).injective _ (clearParityF_physical L J parts.2))
  have e1 : GatePhysical (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) := by
    have h := arith.2.2
    simp only [post4,gatePhysical_append] at h
    exact h.1.1.1.2
  have m1 : GatePhysical (Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) := by
    have h := arith.1
    simp only [pre4,gatePhysical_append] at h
    exact h.1.1.2
  have loan : GatePhysical (loanF L J B) := by
    simp only [loanF,loanW,gatePhysical_append]
    refine ⟨e1,⟨⟨?_,gatePhysical_rename _ (Equiv.swap _ _).injective _
      (gatePhysical_rename _ (Equiv.swap _ _).injective _
        (gatePhysical_rename _ (Equiv.swap _ _).injective _ arith.2.1))⟩,?_⟩,m1⟩
    · simp [GatePhysical,PhysicalInstr]
    · simp [GatePhysical,PhysicalInstr,ProperGate,ctr.1,ctr.2.1,ctr.2.2.1,ctr.2.2.2,jb]
  simp only [programF,arithH,gatePhysical_append]
  exact ⟨⟨⟨parts.1.1.1,⟨⟨arith.1,loan⟩,arith.2.2⟩⟩,parts.1.2⟩,clear⟩

theorem jointF_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup) :
    GatePhysical (jointF L J G) := by
  have core := programF_physical L hw hn J G hJ hG hJG
  have x : GatePhysical [Instr.X G] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  simp only [jointF,gatePhysical_append]
  exact ⟨⟨x,core⟩,x⟩

end ECDSAAdd.Entrant.JointForward1588


/-! ## The S1 first-packet kernel in the record's 1,588 layout -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum
  EntryRetained5 FirstInverse5 JointInverse1588 Challenge Baselines
attribute [local irreducible] wires

/-- The forward joint with virtual carry `719` on the open trit hole `s 0 4 = base 1032`. -/
def kernel : Program :=
  renameProgram (Equiv.swap (base 719) (base 1032)) (jointF portsJ (base 1028) (base 1))

/-- Carry #248 is virtual `760`, the retired pool wire. -/
theorem c248_eq : cAt portsJ 248=base 760 := by
  simp [cAt,portsJ,Q6EndpointCell.ports,wireBlock,List.getD_eq_getElem?_getD]

/-- Record-length padding: 506 empty-correction erasures of the clean carry `base 512` (the
replaced first selector swap has 1 and the G1 half window 1022 records; the kernel has 517, one
of them the measured loan of carry #1 that retires virtual `760`). -/
def padding : Program := List.replicate 506 (Instr.measureX (base 512) [] [])

def padded : Program := kernel++padding

theorem padding_counts : toffoliCount padding=0 ∧ measurementCount padding=506 := by
  have h (n : Nat) : toffoliCount (List.replicate n (Instr.measureX (base 512) [] []))=0 ∧
      measurementCount (List.replicate n (Instr.measureX (base 512) [] []))=n := by
    induction n with
    | zero => exact ⟨rfl,rfl⟩
    | succ n ih =>
      rw [List.replicate_succ]
      simp [toffoliCount,measurementCount,ih.1,ih.2,Nat.add_comm]
  exact h 506

theorem padded_counts : toffoliCount padded=774 ∧ measurementCount padded=1023 := by
  have j := jointF_counts portsJ portsJ_widths (base 1028) (base 1)
  have r := renameProgram_counts (Equiv.swap (base 719) (base 1032)) (jointF portsJ (base 1028) (base 1))
  have p := padding_counts
  simp only [padded,kernel,toffoliCount_append,measurementCount_append,r.1,r.2,j.1,j.2,p.1,p.2]
  all_goals simp

theorem padded_slots : gateSlots padded≤8484 := by
  have j := jointF_slots portsJ portsJ_widths (base 1028) (base 1)
  have p : gateSlots padding=506 := by
    have h (n : Nat) : gateSlots (List.replicate n (Instr.measureX (base 512) [] []))=n := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [List.replicate_succ,gateSlots_cons,ih]
        simp [instructionSlots]
        omega
    exact h 506
  simp only [padded,kernel,gateSlots_append,rename_gateSlots,p]
  omega

theorem padded_physical : GatePhysical padded := by
  have j := jointF_physical portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  have p : GatePhysical padding := by
    intro i hi
    rw [padding,List.mem_replicate] at hi
    rw [hi.2]
    simp [PhysicalInstr]
  simp only [padded,kernel,gatePhysical_append]
  exact ⟨gatePhysical_rename _ (Equiv.swap _ _).injective _ j,p⟩

theorem hole_free : base 1032∉wires (jointF portsJ (base 1028) (base 1)) := by
  have sup := jointF_support portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
  intro used
  have m := List.mem_toFinset.mp (sup used)
  have off := off_ports 1032 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [retSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with ((h|h)|h)|h
  · exact off.1 h
  · exact off.2.1 h
  · exact off.2.2 (List.mem_of_mem_take h)
  · simp only [portsJ,Q6EndpointCell.ports,base_injective.eq_iff] at h
    omega

theorem padded_support : wires padded⊆kernelSites := by
  have sup := jointF_support portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
  have lo := jointF_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq,c248_eq] at lo
  have keep (q : Wire) (hq : q∈wires (jointF portsJ (base 1028) (base 1))) : q∈kernelSites := by
    have m := List.mem_toFinset.mp (sup hq)
    have q1541 : q≠base 1541 := fun e => lo _ (Or.inr (Or.inl e)) hq
    simp only [retSites,List.mem_append] at m
    simp only [kernelSites,List.mem_toFinset,List.mem_append]
    rcases m with ((h|h)|h)|h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · rw [portsJ_take255,List.mem_append,List.mem_singleton] at h
      rcases h with h|h
      · exact Or.inl (Or.inr h)
      · exact absurd h q1541
    · right
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
  intro q hq
  simp only [padded,kernel,wires_append,Finset.mem_union,renameProgram_support] at hq
  rcases hq with hq|hq
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    by_cases a719 : a=base 719
    · subst a
      rw [Equiv.swap_apply_left]
      simp [kernelSites]
    · by_cases a1032 : a=base 1032
      · exact absurd (a1032 ▸ ha) hole_free
      · rw [Equiv.swap_apply_of_ne_of_ne a719 a1032]
        exact keep a ha
  · have e : q=base 512 := Finset.mem_singleton.mp (pad_wires (base 512) 506 hq)
    subst e
    have m : base 512∈wireBlock base 512 253 :=
      List.mem_map.mpr ⟨512,by simp [List.mem_range'_1],rfl⟩
    simp only [kernelSites,List.mem_toFinset,List.mem_append,portsJ_take254]
    exact Or.inl (Or.inr (Or.inl m))

theorem padded_free (i : Nat) (hi : i=0 ∨ i=516 ∨ i=719 ∨ i=1541) : base i∉wires padded := by
  have lo := jointF_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq,c248_eq] at lo
  rcases hi with rfl|rfl|rfl|rfl
  · intro used
    have m := List.mem_toFinset.mp (padded_support used)
    have off := off_ports 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with ((h|h)|h)|h
    · exact off.1 h
    · exact off.2.1 h
    · exact off.2.2 (List.mem_of_mem_take h)
    · simp only [portsJ,Q6EndpointCell.ports,base_injective.eq_iff] at h
      omega
  all_goals
    intro used
    simp only [padded,kernel,wires_append,Finset.mem_union,renameProgram_support] at used
    rcases used with used|used
    · obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp used
      by_cases a719 : a=base 719
      · subst a719
        rw [Equiv.swap_apply_left,base_injective.eq_iff] at eq
        omega
      · by_cases a1032 : a=base 1032
        · subst a1032
          exact hole_free ha
        · rw [Equiv.swap_apply_of_ne_of_ne a719 a1032] at eq
          subst eq
          first
            | exact a719 rfl
            | exact lo _ (Or.inl rfl) ha
            | exact lo _ (Or.inr (Or.inl rfl)) ha
    · have e := Finset.mem_singleton.mp (pad_wires (base 512) 506 used)
      rw [base_injective.eq_iff] at e
      omega

/-- Virtual wire `760` (carry #248, the retired pool wire) never occurs in the padded forward joint. -/
theorem padded_760_free : base 760∉wires padded := by
  have lo := jointF_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq,c248_eq] at lo
  intro used
  simp only [padded,kernel,wires_append,Finset.mem_union,renameProgram_support] at used
  rcases used with used|used
  · obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp used
    by_cases a719 : a=base 719
    · subst a719
      rw [Equiv.swap_apply_left,base_injective.eq_iff] at eq
      omega
    · by_cases a1032 : a=base 1032
      · subst a1032
        exact hole_free ha
      · rw [Equiv.swap_apply_of_ne_of_ne a719 a1032] at eq
        subst eq
        exact lo _ (Or.inr (Or.inr rfl)) ha
  · have e := Finset.mem_singleton.mp (pad_wires (base 512) 506 used)
    rw [base_injective.eq_iff] at e
    omega

/-- On any replay state with clean scalar bank, clean flag and open trit hole, the padded kernel
performs the joint entry `(Z,0) ↦ ((±Z)/2, J?Z:0)`. -/
theorem padded_pair (st : BasisState) (clean : ∀q∈BalancedCircuit.work portsJ,st q=false)
    (sign : st (base 2409)=false) (hole : st (base 1032)=false) (Z : Fp) :
    Triple (PairFrame portsJ.r portsJ.y st (centerWord Z) 0) padded
      (PairFrame portsJ.r portsJ.y st
        (centerWord ((if st (base 1028) && !st (base 1) then -Z else Z)/2))
        (centerWord (if st (base 1028) then Z else 0))) := by
  have j := jointF_pair portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup st clean
    (by simpa [portsJ_eq] using sign) Z
  intro s m input
  have a719 := off_data 719 (by omega) (by omega)
  have a1032 := off_data 1032 (by omega) (by omega)
  have a512 := off_data 512 (by omega) (by omega)
  let mk := m.take (measurementCount kernel)
  have out := j s mk input
  have in719 : s.basis (base 719)=false :=
    (input.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have in1032 : s.basis (base 1032)=false := (input.2.2 _ a1032.1 a1032.2).trans hole
  have o719 : (run (jointF portsJ (base 1028) (base 1)) mk s).basis (base 719)=false :=
    (out.2.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have o1032 : (run (jointF portsJ (base 1028) (base 1)) mk s).basis (base 1032)=false :=
    (out.2.2.2 _ a1032.1 a1032.2).trans hole
  have k : run kernel mk s=run (jointF portsJ (base 1028) (base 1)) mk s :=
    rebind_swap_run _ _ _ s mk in719 in1032 o719 o1032
  have o512 : (run (jointF portsJ (base 1028) (base 1)) mk s).basis (base 512)=false :=
    (out.2.2.2 _ a512.1 a512.2).trans (clean _ (carry_work 512 (by omega)))
  have shape : run padded m s=run (jointF portsJ (base 1028) (base 1)) mk s := by
    rw [padded,run_append,k,padding]
    exact pad_run (base 512) 506 _ _ o512
  rw [shape]
  exact out

/-- Toffoli saving of the S1 (divide) first body: the 256-T first selector swap and the 765-T
comparator-free G1 half window become the 774-T padded forward joint (773 + the measured loan of
carry #1 that retires virtual `760`). -/
def saving (divide : Bool) : Nat := if divide then 247 else 0

end ECDSAAdd.Entrant.JointForward1588

/-! ### Syntax-slot comparison with the replaced half window -/
set_option maxRecDepth 100000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic MappedCompressed Challenge


end ECDSAAdd.Entrant.JointForward1588
end
