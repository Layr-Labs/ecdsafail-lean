import ECDSAAdd.Arithmetic.BalancedCoreComposeProof
import ECDSAAdd.Arithmetic.BalancedInverseComposeFold
import ECDSAAdd.Arithmetic.OffsetBorrowedFieldProof
import ECDSAAdd.Arithmetic.OffsetBorrowedInverseProof
import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalEnvironment
import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalReplay
import ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonicalReplay
import ECDSAAdd.Arithmetic.EndpointSwapTrimProgram
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Arithmetic.EntryForwardSelectedFieldSegment
import ECDSAAdd.Arithmetic.MappedFieldPhysical
import ECDSAAdd.Submission.Entrant.HalfLane

-- ===== LaneIFold =====

/-! Field cell fold without the carry-out position.

The original fold is a 257-wide mapped addition whose top position (`cout`)
is computed only to be cleared again by `CX minus cout`.  Here the addition is
256 wide; `cout` is never written.  A measurement of the (clean) `cout` wire
keeps the measurement count of the cell unchanged. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic BalancedCircuit BalancedField BalancedFold

def foldBitsI (L : Layout) : List MappedBit :=
  (List.range 256).map (fun i =>
    {wire:=some (if sparseF.testBit (i+1) then L.plus else L.minus),flip:=false})

theorem foldBits_split (L : Layout) :
    foldBits L=foldBitsI L++[{wire:=none,flip:=false}] := rfl

theorem foldBitsI_length (L : Layout) : (foldBitsI L).length=256 := by
  simp [foldBitsI]

theorem mappedValue_append_zero (bits : List MappedBit) (s : BasisState) :
    mappedValue (bits++[{wire:=none,flip:=false}]) s=mappedValue bits s := by
  induction bits with
  | nil => simp [mappedValue,MappedBit.value]
  | cons b bs ih => simp only [List.cons_append,mappedValue,ih]

theorem foldBitsI_value (L : Layout) (s : BasisState) :
    mappedValue (foldBitsI L) s=mappedValue (foldBits L) s := by
  rw [foldBits_split,mappedValue_append_zero]

theorem foldBitsI_sources (L : Layout) (w : Wire) (hw : w∈mappedWires (foldBitsI L)) :
    w=L.plus ∨ w=L.minus := by
  apply foldBits_sources L w
  rw [foldBits_split]
  simp only [mappedWires,List.flatMap_append,List.mem_append] at hw ⊢
  exact Or.inl hw

def foldI (L : Layout) : Program :=
  [.measureX L.cout [] []]++mappedAdd (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity

def undoFoldI (L : Layout) : Program :=
  [.measureX L.cout [] []]++mappedSub (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity

theorem clean_measure (t : Wire) (s : State) (m : List Bool) (h : s.basis t=false) :
    run [.measureX t [] []] m s=s := by
  apply State.extensionality
  · simp [run,measureAndCorrect,correct,h]
  · funext q
    by_cases hq : q=t
    · subst q; simp [run,measureAndCorrect,correct,writeBit,h]
    · simp [run,measureAndCorrect,correct,writeBit,Function.update_of_ne hq]

theorem foldI_ND (L : Layout) (hn : L.wires.Nodup) :
    (L.parity::(foldTarget L++L.carry.take 255)).Nodup := by
  have big := foldND L hn
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp big q
  have tk : (L.carry.take 255).count q≤L.carry.count q :=
    (List.take_sublist 255 L.carry).count_le q
  simp only [List.count_append,List.count_cons,List.count_nil] at h tk ⊢
  omega

theorem foldI_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (foldI L)=255 ∧ measurementCount (foldI L)=256 ∧
    toffoliCount (undoFoldI L)=255 ∧ measurementCount (undoFoldI L)=256 := by
  have w := BalancedCircuit.widths L hw
  have tl : (foldTarget L).length=256 := by
    have h := w.2.2.1
    simp only [List.length_append,List.length_cons,List.length_nil] at h
    omega
  have cl : (L.carry.take 255).length+1=(foldTarget L).length := by
    rw [List.length_take,w.2.2.2.2,tl]; decide
  have bl : (foldBitsI L).length=(foldTarget L).length := by rw [foldBitsI_length,tl]
  have a := mappedAdd_counts (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity bl cl
  have b := mappedSub_counts (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity bl cl
  simp only [foldI,undoFoldI,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,tl]
  norm_num [toffoliCount,measurementCount]

theorem fold_counts_old (L : Layout) (hw : L.Widths) :
    toffoliCount (fold L)=256 ∧ measurementCount (fold L)=256 ∧
    toffoliCount (BalancedInverse.undoFold L)=256 ∧
    measurementCount (BalancedInverse.undoFold L)=256 := by
  have w := BalancedCircuit.widths L hw
  have a := mappedAdd_counts (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
    (by omega) (by omega)
  have b := mappedSub_counts (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
    (by omega) (by omega)
  simp only [fold,BalancedInverse.undoFold,toffoliCount_append,measurementCount_append,
    a.1,a.2,b.1,b.2,w.2.2.1]
  norm_num [toffoliCount,measurementCount]

/-- Same contract as `fold_correct`, for the 256-wide fold. -/
theorem foldI_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hu : s.basis L.plus=plusController T) (hv : s.basis L.minus=minusController T)
    (hc : s.basis L.cout=false) (hcarry : regValue L.carry s.basis=0)
    (hword : regValue (foldTarget L) s.basis=toggledWord T/2) :
    (run (foldI L) m s).phase=s.phase ∧
    regValue (foldTarget L) (run (foldI L) m s).basis=encodeWord 256 (halfResult T) ∧
    (run (foldI L) m s).basis L.cout=false ∧
    ∀ w,w∉foldTarget L → (run (foldI L) m s).basis w=s.basis w := by
  have big := foldND L hn
  have nd := foldI_ND L hn
  have widths := BalancedCircuit.widths L hw
  have tl : (foldTarget L).length=256 := by
    have h := widths.2.2.1
    simp only [List.length_append,List.length_cons,List.length_nil] at h
    omega
  have cl : (L.carry.take 255).length+1=(foldTarget L).length := by
    rw [List.length_take,widths.2.2.2.2,tl]; decide
  have bl : (foldBitsI L).length=(foldTarget L).length := by rw [foldBitsI_length,tl]
  have coutAway : L.cout∉foldTarget L := by
    intro h
    have c := List.nodup_iff_count.mp big L.cout
    have pos := List.count_pos_iff.mpr h
    simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c
    omega
  have sourceAway : ∀ w∈mappedWires (foldBitsI L),w∉L.parity::(foldTarget L++L.carry.take 255) := by
    intro w h bad
    have c := List.nodup_iff_count.mp big w
    have tk : (L.carry.take 255).count w≤L.carry.count w :=
      (List.take_sublist 255 L.carry).count_le w
    have pos := List.count_pos_iff.mpr bad
    rcases foldBitsI_sources L w h with rfl|rfl
    · simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c pos tk
      omega
    · simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c pos tk
      omega
  have clean : ∀ q∈L.carry.take 255,s.basis q=false := by
    intro q hq
    exact (regValue_zero _ _).mp hcarry q (List.mem_of_mem_take hq)
  have source : mappedValue (foldBitsI L) s.basis=
      selectedSource (plusController T) (minusController T) := by
    have hex : ¬(s.basis L.plus && s.basis L.minus)=true := by
      rw [hu,hv]; exact controllers_exclusive T
    rw [foldBitsI_value]
    simpa only [hu,hv] using foldBits_value L s.basis hex
  have hadd := mappedAdd_correct (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity nd
    sourceAway bl cl s m.tail clean
  have actual : run (foldI L) m s=run (mappedAdd (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity) m.tail s := by
    have h0 := clean_measure L.cout s m hc
    simp only [foldI,List.singleton_append]
    simp only [run] at h0 ⊢
    rw [h0]
  rw [actual]
  refine ⟨hadd.1,?_,?_,hadd.2.1⟩
  · rw [hadd.2.2,source,hword,hp,tl]
    have fv := foldedSum_value T ht
    have bound := encodeWord_bound 256 (halfResult T)
    have fs : foldedSum T=toggledWord T/2+
        selectedSource (plusController T) (minusController T)+(originalParity T).toNat := rfl
    have mw : modulusWord=2^256 := rfl
    rw [show selectedSource (plusController T) (minusController T)+toggledWord T/2+
      (originalParity T).toNat=foldedSum T by omega,fv,mw]
    cases minusController T
    · simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
      exact Nat.mod_eq_of_lt bound
    · simp only [Bool.toNat_true,Nat.mul_one,Nat.add_mod_right]
      exact Nat.mod_eq_of_lt bound
  · exact (hadd.2.1 L.cout coutAway).trans hc

/-- Same contract as `undoFold_correct`, for the 256-wide subtraction. -/
theorem undoFoldI_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hu : s.basis L.plus=plusController T) (hv : s.basis L.minus=minusController T)
    (hc : s.basis L.cout=false) (hcarry : regValue L.carry s.basis=0)
    (hword : regValue (foldTarget L) s.basis=encodeWord 256 (halfResult T)) :
    (run (undoFoldI L) m s).phase=s.phase ∧
    regValue (foldTarget L) (run (undoFoldI L) m s).basis=toggledWord T/2 ∧
    (run (undoFoldI L) m s).basis L.cout=false ∧
    ∀w,w∉foldTarget L → (run (undoFoldI L) m s).basis w=s.basis w := by
  have big := foldND L hn
  have nd := foldI_ND L hn
  have widths := BalancedCircuit.widths L hw
  have tl : (foldTarget L).length=256 := by
    have h := widths.2.2.1
    simp only [List.length_append,List.length_cons,List.length_nil] at h
    omega
  have cl : (L.carry.take 255).length+1=(foldTarget L).length := by
    rw [List.length_take,widths.2.2.2.2,tl]; decide
  have bl : (foldBitsI L).length=(foldTarget L).length := by rw [foldBitsI_length,tl]
  have coutAway : L.cout∉foldTarget L := by
    intro h
    have c := List.nodup_iff_count.mp big L.cout
    have pos := List.count_pos_iff.mpr h
    simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c
    omega
  have sourceAway : ∀ w∈mappedWires (foldBitsI L),w∉L.parity::(foldTarget L++L.carry.take 255) := by
    intro w h bad
    have c := List.nodup_iff_count.mp big w
    have tk : (L.carry.take 255).count w≤L.carry.count w :=
      (List.take_sublist 255 L.carry).count_le w
    have pos := List.count_pos_iff.mpr bad
    rcases foldBitsI_sources L w h with rfl|rfl
    · simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c pos tk
      omega
    · simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c pos tk
      omega
  have clean : ∀ q∈L.carry.take 255,s.basis q=false := by
    intro q hq
    exact (regValue_zero _ _).mp hcarry q (List.mem_of_mem_take hq)
  have source : mappedValue (foldBitsI L) s.basis=
      selectedSource (plusController T) (minusController T) := by
    have hex : ¬(s.basis L.plus && s.basis L.minus)=true := by
      rw [hu,hv]; exact controllers_exclusive T
    rw [foldBitsI_value]
    simpa only [hu,hv] using foldBits_value L s.basis hex
  have sub := BalancedInverse.mappedSub_any_correct (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity nd
    sourceAway bl cl s m.tail clean
  have actual : run (undoFoldI L) m s=run (mappedSub (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity) m.tail s := by
    have h0 := clean_measure L.cout s m hc
    simp only [undoFoldI,List.singleton_append]
    simp only [run] at h0 ⊢
    rw [h0]
  rw [actual]
  refine ⟨sub.1,?_,?_,sub.2.1⟩
  · rw [sub.2.2,source,hword,hp,tl]
    have fv := foldedSum_value T ht
    have bound := prepared_upper_bound T ht
    have fs : foldedSum T=toggledWord T/2+
        selectedSource (plusController T) (minusController T)+(originalParity T).toNat := rfl
    have mw : modulusWord=2^256 := rfl
    rw [mw] at fv bound
    have pb : (originalParity T).toNat≤1 := by cases originalParity T <;> decide
    cases hm : minusController T
    · rw [hm] at fv
      simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at fv
      rw [show encodeWord 256 (halfResult T)+2^256-selectedSource (plusController T) false-
        (originalParity T).toNat=toggledWord T/2+2^256 by rw [hm] at fs; omega,Nat.add_mod_right]
      exact Nat.mod_eq_of_lt bound
    · rw [hm] at fv
      simp only [Bool.toNat_true,Nat.mul_one] at fv
      rw [show encodeWord 256 (halfResult T)+2^256-selectedSource (plusController T) true-
        (originalParity T).toNat=toggledWord T/2 by rw [hm] at fs; omega]
      exact Nat.mod_eq_of_lt bound
  · exact (sub.2.1 L.cout coutAway).trans hc

end ECDSAAdd.Entrant.LaneI


-- ===== LaneIKernel =====

/-! Forward and inverse field kernels using the 256-wide fold, and their exact
State equalities with the original kernels on the original kernel domain. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic BalancedCircuit BalancedField BalancedFold

section Core

def coreProgramI (L : Layout) : Program :=
  seedViews L++(rawAdd L++(prepareFold L++(foldI L++
    (rotateRight (rawTarget L)++releaseSelectors L))))

theorem coreI_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (coreProgramI L) m s
    t.phase=s.phase ∧
    regValue L.r t.basis=encodeWord 256 (halfResult (rawSum B X Y)) ∧
    t.basis L.parity=originalParity (rawSum B X Y) ∧
    t.basis L.sourceGuard=s.basis L.ymsb ∧
    (∀q∈coreClean L,t.basis q=false) ∧
    (∀q,q∉L.r → q≠L.parity → q≠L.sourceGuard → t.basis q=s.basis q) := by
  let T := rawSum B X Y
  let P := originalParity T
  let N := decide (T<0)
  let H := negative (halfResult T)
  let m₁ := m.drop (measurementCount (rawAdd L))
  let m₂ := m₁.drop (measurementCount (foldI L))
  generalize eu : run (seedViews L) m s = u
  generalize ev : run (rawAdd L) m u = v
  generalize ew : run (prepareFold L) m₁ v = w
  generalize ez : run (foldI L) m₁ w = z
  generalize ea : run (rotateRight (rawTarget L)) m₂ z = a
  generalize et : run (releaseSelectors L) m₂ a = t
  have ht := rawSum_bounds B X Y hx hy
  have ndR := List.nodup_reverse.mpr (scalarND L hn)
  simp only [List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ndR
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9,h0_10⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩,⟨h5_6,h5_7,h5_8,h5_9,h5_10⟩,⟨h6_7,h6_8,h6_9,h6_10⟩,⟨h7_8,h7_9,h7_10⟩,⟨h8_9,h8_10⟩,h9_10⟩
  rcases ndR with ⟨⟨r0_1,r0_2,r0_3,r0_4,r0_5,r0_6,r0_7,r0_8,r0_9,r0_10⟩,⟨r1_2,r1_3,r1_4,r1_5,r1_6,r1_7,r1_8,r1_9,r1_10⟩,⟨r2_3,r2_4,r2_5,r2_6,r2_7,r2_8,r2_9,r2_10⟩,⟨r3_4,r3_5,r3_6,r3_7,r3_8,r3_9,r3_10⟩,⟨r4_5,r4_6,r4_7,r4_8,r4_9,r4_10⟩,⟨r5_6,r5_7,r5_8,r5_9,r5_10⟩,⟨r6_7,r6_8,r6_9,r6_10⟩,⟨r7_8,r7_9,r7_10⟩,⟨r8_9,r8_10⟩,r9_10⟩
  have su := compose_seed_frame L hw hn s m hc
  rw [eu] at su
  have sv := seed_raw_signed L hw hn B X Y hx hy s m hs hr hyr hc
  simp only [run_append] at sv
  simp only [run_take] at sv
  simp only [show measurementCount (seedViews L)=0 from rfl,List.drop_zero] at sv
  rw [eu,ev] at sv
  have cu := (seed_signed L hw hn X Y s m hr hyr hc).2.2
  rw [eu] at cu
  have rf (q : Wire) (hq : q∉rawTarget L) : v.basis q=u.basis q :=
    by simpa only [ev] using rawAdd_frame L hw hn u m cu q hq
  have away (q : Wire)
      (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      q∉rawTarget L := compose_raw_away L hn q hq
  have vp : v.basis L.parity=P :=
    (rf _ (away _ (by simp))).trans (by simpa only [eu] using seed_parity L hw hn B X Y s m hr hyr hc)
  have vo : v.basis L.one=N := word_sign L.r L.one v.basis T sv.2.1
  have vr : v.basis L.r0=P := by
    apply word_parity L.r0 (L.rtail++[L.rmsb,L.one]) v.basis T
    simpa [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc] using sv.2.1
  have vz (q : Wire) (hq : q∈[L.cout,L.minus,L.plus,L.lower]++L.carry) : v.basis q=false := by
    have cv := compose_clean_views L hn q hq
    have qo : q≠L.one := fun e => cv.1 (e ▸ (by simp [rawTarget]))
    exact (rf q cv.1).trans ((su.2.2 q cv.2.1 qo cv.2.2.1).trans (hc q cv.2.2.2))
  have wp := compose_prepare_bits L hn P N v m₁ vp vo vr
    (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp))
  rw [ew] at wp
  have pf (q : Wire) (hq : q∉rawTarget L) (hl : q≠L.lower)
      (hm : q≠L.minus) (hu : q≠L.plus) : w.basis q=v.basis q :=
    by
      simpa only [ew] using (compose_prepare_frame L hn P N v m₁ vp vo vr
        (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp)) q hq hl hm hu)
  have wpar : w.basis L.parity=P := by
    exact (pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans vp
  have wc : w.basis L.cout=false := by
    exact (pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans (vz _ (by simp))
  have wcarry : regValue L.carry w.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have qne (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
        q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
    exact (pf q (away q (by simp [hq])) (qne _ (by simp))
      (qne _ (by simp)) (qne _ (by simp))).trans (vz q (by simp [hq]))
  have prepared := prepare_upper L hw hn T v m₁ sv.2.1 vp
    (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp))
  rw [ew] at prepared
  have zw := foldI_correct L hw hn T ht w m₁ wpar
    wp.2.2.2.2.1 wp.2.2.2.1 wc wcarry prepared
  rw [ez] at zw
  have z0 : z.basis L.r0=false :=
    (zw.2.2.2 _ (compose_not_fold_r0 L hn)).trans wp.2.1
  have az := rotate_folded L hw hn T ht z m₂ z0 zw.2.1
  rw [ea] at az
  have af (q : Wire) (hq : q∉rawTarget L) : a.basis q=w.basis q :=
    (az.2.2.2 q hq).trans (zw.2.2.2 q (compose_fold_subset L q hq))
  have ah : a.basis L.rmsb=H :=
    BalancedCleanup.result_msb L.toLayout hw (halfResult T) (halfResult_spec T ht).1 a.basis az.2.1
  have hp : a.basis L.parity=P := (af _ (away _ (by simp))).trans wpar
  have hsign : H=(N ^^ P) := halfResult_sign T ht
  have al : a.basis L.lower=(H ^^ P) := by
    rw [af _ (away _ (by simp)),wp.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have am : a.basis L.minus=(P && !H) := by
    rw [af _ (away _ (by simp)),wp.2.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have au : a.basis L.plus=(P ^^ (P && !H)) := by
    rw [af _ (away _ (by simp)),wp.2.2.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have ta := compose_release_frame L hn P H a m₂ hp ah al am au
  rw [et] at ta
  have tf (q : Wire) (hl : q≠L.lower) (hm : q≠L.minus) (hu : q≠L.plus) :
      t.basis q=a.basis q := ta.2.2.2.2 q hl hm hu
  have tr : regValue L.r t.basis=encodeWord 256 (halfResult T) := by
    apply Eq.trans _ az.2.1
    apply regValue_congr
    intro q hq
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
        q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
    exact tf q (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  have tp : t.basis L.parity=P := by
    exact (tf _ (by assumption) (by assumption) (by assumption)).trans hp
  have tg : t.basis L.sourceGuard=s.basis L.ymsb := by
    exact (tf _ (by assumption) (by assumption) (by assumption)).trans
      ((af _ (away _ (by simp))).trans
        ((pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans
          ((rf _ (away _ (by simp))).trans su.2.1)))
  have tz : ∀q∈coreClean L,t.basis q=false := by
    intro q hq
    simp only [coreClean,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|hq
    · exact (tf _ (by assumption) (by assumption) (by assumption)).trans
        ((az.2.2.2 _ (away _ (by simp))).trans zw.2.2.1)
    · exact ta.2.2.1
    · exact ta.2.2.2.1
    · exact ta.2.1
    · exact (tf _ (by assumption) (by assumption) (by assumption)).trans az.2.2.1
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
          q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
      exact (tf q (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((af q (away q (by simp [hq]))).trans
          ((pf q (away q (by simp [hq])) (neq _ (by simp)) (neq _ (by simp))
            (neq _ (by simp))).trans (vz q (by simp [hq]))))
  have frame : ∀q,q∉L.r → q≠L.parity → q≠L.sourceGuard → t.basis q=s.basis q := by
    intro q hqr hqp hqg
    by_cases hq : q∈coreClean L
    · exact (tz q hq).trans (hc q (coreClean_sub_work L q hq)).symm
    · have qo : q≠L.one := fun e => hq (by simp [coreClean,e])
      have ql : q≠L.lower := fun e => hq (by simp [coreClean,e])
      have qm : q≠L.minus := fun e => hq (by simp [coreClean,e])
      have qu : q≠L.plus := fun e => hq (by simp [coreClean,e])
      have qa : q∉rawTarget L := by simpa only [rawTarget,List.mem_append,
        List.mem_singleton,not_or] using And.intro hqr qo
      exact (tf q ql qm qu).trans ((af q qa).trans ((pf q qa ql qm qu).trans
        ((rf q qa).trans (su.2.2 q hqg qo hqp))))
  have actual : run (coreProgramI L) m s=t := by
    simp only [coreProgramI,run_append]
    simp only [run_take]
    simp only [
      show measurementCount (seedViews L)=0 from rfl,
      show measurementCount (prepareFold L)=0 from rfl,
      (rotate_counts (rawTarget L)).2.1,List.drop_zero]
    rw [eu,ev,ew,ez,ea,et]
  rw [actual]
  exact ⟨ta.1.trans (az.1.trans (zw.1.trans (wp.1.trans sv.1))),tr,tp,tg,tz,frame⟩


theorem coreI_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (coreProgramI L)+1=toffoliCount (coreProgram L) ∧
    measurementCount (coreProgramI L)=measurementCount (coreProgram L) := by
  have a := foldI_counts L hw
  have b := fold_counts_old L hw
  simp only [coreProgramI,coreProgram,toffoliCount_append,measurementCount_append,a.1,a.2.1,b.1,b.2.1]
  refine ⟨?_,?_⟩ <;> first | omega | trivial

/-- The new core produces the identical complete State on the core domain. -/
theorem core_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    run (coreProgramI L) m s=run (coreProgram L) m s := by
  have fresh := coreI_correct L hw hn B X Y hx hy s m hs hr hyr hc
  have old := core_correct L hw hn B X Y hx hy s m hs hr hyr hc
  apply State.extensionality
  · exact fresh.1.trans old.1.symm
  · funext q
    by_cases hq : q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (fresh.2.1.trans old.2.1.symm) q hq
    by_cases hp : q=L.parity
    · subst q; exact fresh.2.2.1.trans old.2.2.1.symm
    by_cases hg : q=L.sourceGuard
    · subst q; exact fresh.2.2.2.1.trans old.2.2.2.1.symm
    exact (fresh.2.2.2.2.2 q hq hp hg).trans (old.2.2.2.2.2 q hq hp hg).symm

end Core

section Inverse
open BalancedInverse

def invProgramI (L : Layout) : Program :=
  [.CX L.ymsb L.sourceGuard]++recoverParity L++recoverSelectors L++
  rotateLeft (rawTarget L)++undoFoldI L++undoPreparation L++rawSubtract L++(seedViews L).reverse

private theorem initialWork (L : Layout) (a : Wire)
    (ha : a∈[L.parity,L.lower,L.one]++L.carry) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem selectorWork (L : Layout) (a : Wire)
    (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem frameWork (L : Layout) (a : Wire)
    (ha : a∈[L.sourceGuard,L.one,L.parity,L.lower,L.minus,L.plus]) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem selectorAway (L : Layout) (hn : L.wires.Nodup) (a : Wire)
    (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) :
    a≠L.sourceGuard ∧ a≠L.parity := by
  have nd : ([L.sourceGuard,L.parity]++([L.cout,L.minus,L.plus,L.lower,L.one]++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (allND L hn) q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have sep := List.disjoint_left.mp (List.nodup_append'.mp nd).2.2
  exact ⟨fun e => sep (by simp [←e]) ha,fun e => sep (by simp [←e]) ha⟩


theorem invProgramI_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (invProgramI L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 256 (result B R Y) ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.r → t.basis q=s.basis q) := by
  let X := result B R Y
  let T := rawSum B X Y
  let P := originalParity T
  let m₁ := m.drop (measurementCount (recoverParity L))
  let m₂ := m₁.drop (measurementCount (undoFoldI L))
  let m₃ := m₂.drop (measurementCount (undoPreparation L))
  let m₄ := m₃.drop (measurementCount (rawSubtract L))
  generalize e₀ : run [.CX L.ymsb L.sourceGuard] m s=u₀
  generalize e₁ : run (recoverParity L) m u₀=u₁
  generalize e₂ : run (recoverSelectors L) m₁ u₁=u₂
  generalize e₃ : run (rotateLeft (rawTarget L)) m₁ u₂=u₃
  generalize e₄ : run (undoFoldI L) m₁ u₃=u₄
  generalize e₅ : run (undoPreparation L) m₂ u₄=u₅
  generalize e₆ : run (rawSubtract L) m₃ u₅=u₆
  generalize e₇ : run (seedViews L).reverse m₄ u₆=t
  have hx : Centered X := result_bounds B R Y
  have ht : -(2*q)≤T ∧ T≤2*q := rawSum_bounds B X Y hx hy
  have half : halfResult T=R := result_half B R Y hr hy
  have rawRange : -((2^(257-1) : Nat) : Int)≤T ∧ T<((2^(257-1) : Nat) : Int) := by
    have c := BalancedField.constants
    norm_num at ⊢
    omega
  have w := BalancedCircuit.widths L hw
  have rlen := (BalancedCleanup.widths L.toLayout hw).2.1
  have ylen := (BalancedCleanup.widths L.toLayout hw).2.2.1
  have cnd : L.toLayout.wires.Nodup :=
    (List.nodup_append'.mp (show ([L.sourceGuard,L.cout,L.minus,L.plus]++L.toLayout.wires).Nodup from hn)).2.1
  have ndR := List.nodup_reverse.mpr (scalarND L hn)
  simp only [List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ndR
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9,h0_10⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩,⟨h5_6,h5_7,h5_8,h5_9,h5_10⟩,⟨h6_7,h6_8,h6_9,h6_10⟩,⟨h7_8,h7_9,h7_10⟩,⟨h8_9,h8_10⟩,h9_10⟩
  rcases ndR with ⟨⟨r0_1,r0_2,r0_3,r0_4,r0_5,r0_6,r0_7,r0_8,r0_9,r0_10⟩,⟨r1_2,r1_3,r1_4,r1_5,r1_6,r1_7,r1_8,r1_9,r1_10⟩,⟨r2_3,r2_4,r2_5,r2_6,r2_7,r2_8,r2_9,r2_10⟩,⟨r3_4,r3_5,r3_6,r3_7,r3_8,r3_9,r3_10⟩,⟨r4_5,r4_6,r4_7,r4_8,r4_9,r4_10⟩,⟨r5_6,r5_7,r5_8,r5_9,r5_10⟩,⟨r6_7,r6_8,r6_9,r6_10⟩,⟨r7_8,r7_9,r7_10⟩,⟨r8_9,r8_10⟩,r9_10⟩
  have away (q : Wire)
      (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      q∉rawTarget L := compose_raw_away L hn q hq
  have zero (q : Wire) (hq : q∈work L) : s.basis q=false := hc q hq
  have f₀ (a : Wire) (ha : a≠L.sourceGuard) : u₀.basis a=s.basis a := by
    rw [←e₀]; simp only [run,writeBit,Function.update_of_ne ha]
  have guard₀ : u₀.basis L.sourceGuard=s.basis L.ymsb := by
    rw [←e₀]
    simp only [run,writeBit,Function.update_self]
    rw [hc L.sourceGuard (by simp [work])]
    simp only [Bool.false_xor]
  have R₀ : regValue L.r u₀.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 rlen s.basis R hR)
    apply regValue_congr
    intro a ha
    exact f₀ a (fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha]))
  have Y₀ : regValue L.y u₀.basis=encodeWord 256 Y := by
    apply Eq.trans _ (word_encoding L.y 256 ylen s.basis Y hY)
    apply regValue_congr
    intro a ha
    exact f₀ a (fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha]))
  have z₀ (a : Wire) (ha : a∈[L.parity,L.lower,L.one]++L.carry) : u₀.basis a=false := by
    have ne : a≠L.sourceGuard := by
      rcases List.mem_append.mp ha with ha|ha
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl <;> assumption
      · exact fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha])
    exact (f₀ a ne).trans (hc a (initialWork L a ha))
  have oneOracle := recoverParity_correct L hw cnd R Y B hr hy u₀ m R₀ Y₀
    ((f₀ _ (by assumption)).trans hs) (z₀ _ (by simp)) (z₀ _ (by simp))
    (fun a ha => z₀ a (by simp [ha])) (z₀ _ (by simp))
  have parity : decide (q < |2*R-signedY B Y|)=P := result_parity B R Y hr hy
  rw [parity,e₁] at oneOracle
  have p₁ : u₁.basis L.parity=P := by rw [oneOracle]; simp only [writeBit,Function.update_self]
  have f₁ (a : Wire) (hg : a≠L.sourceGuard) (hp : a≠L.parity) : u₁.basis a=s.basis a := by
    rw [oneOracle]; simp only [writeBit,Function.update_of_ne hp]; exact f₀ a hg
  have g₁ : u₁.basis L.sourceGuard=s.basis L.ymsb := by
    rw [oneOracle]; simpa only [writeBit,Function.update_of_ne (show L.sourceGuard≠L.parity by assumption)] using guard₀
  have z₁ (a : Wire) (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) : u₁.basis a=false := by
    have ne := selectorAway L hn a ha
    exact (f₁ a ne.1 ne.2).trans (hc a (selectorWork L a ha))
  have R₁ : regValue L.r u₁.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 rlen s.basis R hR)
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₁ a (neq _ (by simp)) (neq _ (by simp))
  have sign₁ : u₁.basis L.rmsb=decide (halfResult T<0) := by
    rw [half]
    exact BalancedCleanup.result_msb L.toLayout hw R hr u₁.basis R₁
  have packet₂ := recoverSelectors_packet L hn T ht u₁ m₁ p₁ sign₁
    (z₁ _ (by simp)) (z₁ _ (by simp)) (z₁ _ (by simp))
  rw [e₂] at packet₂
  have f₂ (a : Wire) (hl : a≠L.lower) (hm : a≠L.minus) (hu : a≠L.plus) : u₂.basis a=u₁.basis a :=
    packet₂.2.2.2.2 a hl hm hu
  have R₂ : regValue L.r u₂.basis=encodeWord 256 R := by
    apply Eq.trans _ R₁
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₂ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  have one₂ : u₂.basis L.one=false :=
    (f₂ _ (by assumption) (by assumption) (by assumption)).trans (z₁ _ (by simp))
  have packet₃ := rotate_unfold L hw hn R u₂ m₁ one₂ R₂
  rw [e₃] at packet₃
  have f₃ (a : Wire) (ha : a∉rawTarget L) : u₃.basis a=u₂.basis a := packet₃.2.2.2 a ha
  have p₃ : u₃.basis L.parity=P := (f₃ _ (away _ (by simp))).trans
    ((f₂ _ (by assumption) (by assumption) (by assumption)).trans p₁)
  have c₃ : u₃.basis L.cout=false := (f₃ _ (away _ (by simp))).trans
    ((f₂ _ (by assumption) (by assumption) (by assumption)).trans (z₁ _ (by simp)))
  have carry₃ : regValue L.carry u₃.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (f₃ a (away a (by simp [ha]))).trans
      ((f₂ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans (z₁ a (by simp [ha])))
  have upper₃ : regValue (foldTarget L) u₃.basis=encodeWord 256 (halfResult T) := by
    rw [half]; exact packet₃.2.2.1
  have packet₄ := undoFoldI_correct L hw hn T ht u₃ m₁ p₃
    ((f₃ _ (away _ (by simp))).trans packet₂.2.2.2.1)
    ((f₃ _ (away _ (by simp))).trans packet₂.2.2.1) c₃ carry₃ upper₃
  rw [e₄] at packet₄
  have f₄ (a : Wire) (ha : a∉rawTarget L) : u₄.basis a=u₃.basis a :=
    packet₄.2.2.2 a (compose_fold_subset L a ha)
  have zero₄ : u₄.basis L.r0=false :=
    (packet₄.2.2.2 _ (compose_not_fold_r0 L hn)).trans packet₃.2.1
  have packet₅ := undoPreparation_packet L hw hn T ht u₄ m₂
    ((f₄ _ (away _ (by simp))).trans p₃) zero₄
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.1))
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.2.1))
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.2.2.1)) packet₄.2.1
  rw [e₅] at packet₅
  have f₅ (a : Wire) (ha : a∉rawTarget L) (hl : a≠L.lower) (hm : a≠L.minus) (hu : a≠L.plus) :
      u₅.basis a=u₁.basis a := (packet₅.2.2.2.2.2 a ha hl hm hu).trans
    ((f₄ a ha).trans ((f₃ a ha).trans (f₂ a hl hm hu)))
  have raw₅ : signedRegValue (rawTarget L) u₅.basis=T := by
    unfold signedRegValue
    rw [w.2.1,packet₅.2.1]
    exact decode_encodeWord 257 (by norm_num) T rawRange
  have Y₅ : signedRegValue L.y u₅.basis=Y := by
    apply Eq.trans _ hY
    unfold signedRegValue
    congr 1
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (f₅ a (away a (by simp [ha])) (neq _ (by simp))
      (neq _ (by simp)) (neq _ (by simp))).trans (f₁ a (neq _ (by simp)) (neq _ (by simp)))
  have g₅ : u₅.basis L.sourceGuard=u₅.basis L.ymsb := by
    have left := (f₅ _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans g₁
    have right := (f₅ L.ymsb (away L.ymsb (by simp [BalancedCleanup.Layout.y]))
      (by assumption) (by assumption) (by assumption)).trans (f₁ L.ymsb (by assumption) (by assumption))
    exact left.trans right.symm
  have src₅ : signedRegValue (rawSource L) u₅.basis=Y := by
    exact (signed_extension L.ylow L.ymsb L.sourceGuard u₅.basis g₅).trans Y₅
  have carry₅ : regValue L.carry u₅.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (packet₅.2.2.2.2.2 a (away a (by simp [ha])) (neq _ (by simp))
      (neq _ (by simp)) (neq _ (by simp))).trans
      ((regValue_zero _ _).mp carry₃ a ha |> fun h => (f₄ a (away a (by simp [ha]))).trans h)
  have sign₅ : u₅.basis L.sign=B := (f₅ _ (away _ (by simp))
    (by assumption) (by assumption) (by assumption)).trans ((f₁ _ (by assumption) (by assumption)).trans hs)
  have packet₆ := rawSubtract_signed L hw hn B X Y hx u₅ m₃ sign₅ src₅ raw₅ carry₅
  rw [e₆] at packet₆
  have f₆ (a : Wire) (ha : a∉rawTarget L) : u₆.basis a=u₅.basis a := packet₆.2.2 a ha
  have Y₆ : signedRegValue L.y u₆.basis=Y := by
    apply Eq.trans _ Y₅
    unfold signedRegValue
    congr 1
    exact regValue_congr _ _ _ (fun a ha => f₆ a (away a (by simp [ha])))
  have g₆ : u₆.basis L.sourceGuard=u₆.basis L.ymsb := by
    exact (f₆ _ (away _ (by simp))).trans (g₅.trans
      (f₆ _ (away _ (by simp [BalancedCleanup.Layout.y]))).symm)
  have p₆ : u₆.basis L.parity=P := (f₆ _ (away _ (by simp))).trans
    ((f₅ _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans p₁)
  have packet₇ := unseed_packet L hw hn B X Y hx u₆ m₄ packet₆.2.1 Y₆ g₆ p₆
  rw [e₇] at packet₇
  have f₇ (a : Wire) (hg : a≠L.sourceGuard) (ho : a≠L.one) (hp : a≠L.parity) :
      t.basis a=u₆.basis a := packet₇.2.2.2.2 a hg ho hp
  have actual : run (invProgramI L) m s=t := by
    simp only [invProgramI,List.append_assoc]
    rw [run_append,run_take]
    simp only [show measurementCount [.CX L.ymsb L.sourceGuard]=0 from rfl,List.drop_zero]
    rw [e₀,run_append,run_take,e₁,run_append,run_take]
    simp only [show measurementCount (recoverSelectors L)=0 from rfl,List.drop_zero]
    rw [e₂,run_append,run_take,(rotate_counts (rawTarget L)).2.2.2,List.drop_zero,
      e₃,run_append,run_take,e₄,run_append,run_take,e₅,run_append,run_take,e₆,e₇]

  have clean : ∀a∈work L,t.basis a=false := by
    intro a ha
    simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|ha
    · exact packet₇.2.1
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans ((packet₅.2.2.2.2.2 _ (away _ (by simp))
          (by assumption) (by assumption) (by assumption)).trans packet₄.2.2.1))
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.2.1)
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.2.2.1)
    · exact packet₇.2.2.2.1
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.1)
    · exact packet₇.2.2.1
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
        fun e => flagAway L hn f hf (by simp [e ▸ ha])
      exact (f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((f₆ a (away a (by simp [ha]))).trans ((regValue_zero _ _).mp carry₅ a ha))
  have frame : ∀a,a∉L.r → t.basis a=s.basis a := by
    intro a ha
    by_cases workA : a∈work L
    · exact (clean a workA).trans (hc a workA).symm
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.one,L.parity,L.lower,L.minus,L.plus]) : a≠f :=
        fun e => workA (e.symm ▸ frameWork L f hf)
      have ar : a∉rawTarget L := by
        simp only [rawTarget,List.mem_append,List.mem_singleton,not_or]
        exact ⟨ha,neq _ (by simp)⟩
      exact (f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((f₆ a ar).trans ((f₅ a ar (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
          (f₁ a (neq _ (by simp)) (neq _ (by simp)))))
  have out : regValue L.r t.basis=encodeWord 256 X := by
    have corr := unseed_correlations L hw B X Y hx u₆ packet₆.2.1 Y₆ g₆ p₆
    have narrow : signedRegValue L.r u₆.basis=X :=
      (signed_extension (L.r0::L.rtail) L.rmsb L.one u₆.basis corr.1).symm.trans packet₆.2.1
    apply Eq.trans _ (word_encoding L.r 256 rlen u₆.basis X narrow)
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  rw [actual]
  exact ⟨packet₇.1.trans (packet₆.1.trans (packet₅.1.trans (packet₄.1.trans
    (packet₃.1.trans (packet₂.1.trans (by rw [oneOracle,←e₀]; rfl)))))),out,clean,frame⟩


theorem invProgramI_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (invProgramI L)+1=toffoliCount (BalancedInverse.program L) ∧
    measurementCount (invProgramI L)=measurementCount (BalancedInverse.program L) := by
  have a := foldI_counts L hw
  have b := fold_counts_old L hw
  simp only [invProgramI,BalancedInverse.program,toffoliCount_append,measurementCount_append,
    a.2.2.1,a.2.2.2,b.2.2.1,b.2.2.2]
  refine ⟨?_,?_⟩ <;> first | omega | trivial

theorem inv_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    run (invProgramI L) m s=run (BalancedInverse.program L) m s := by
  have fresh := invProgramI_correct L hw hn B R Y hr hy s m hs hR hY hc
  have old := BalancedInverse.program_correct L hw hn B R Y hr hy s m hs hR hY hc
  apply State.extensionality
  · exact fresh.1.trans old.1.symm
  · funext q
    by_cases hq : q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (fresh.2.1.trans old.2.1.symm) q hq
    · exact (fresh.2.2.2 q hq).trans (old.2.2.2 q hq).symm

end Inverse

section Field
open DirectSkywalk

/-- Forward field kernel with the 256-wide fold. -/
def fieldProgramI (w : Nat → Wire) (sign : Wire) : Program :=
  coreProgramI (balancedSharedPorts w sign)++
    (TerminalParityOffset.program (OffsetCleanupBorrowedCaller.layout w sign)++
      [.CX (balancedSharedPorts w sign).ymsb (balancedSharedPorts w sign).sourceGuard])

theorem fieldProgramI_counts (w : Nat → Wire) (sign : Wire) :
    toffoliCount (fieldProgramI w sign)+1=toffoliCount (OffsetBorrowedField.program w sign) ∧
    measurementCount (fieldProgramI w sign)=measurementCount (OffsetBorrowedField.program w sign) := by
  have c := coreI_counts (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  simp only [fieldProgramI,OffsetBorrowedField.program,toffoliCount_append,measurementCount_append]
  refine ⟨?_,?_⟩ <;> first | omega | trivial

theorem fieldProgram_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (B : Bool) (X Y : Int)
    (hx : Centered X) (hy : Centered Y) (s : State) (m : List Bool)
    (hs : s.basis sign=B)
    (hr : signedRegValue (balancedSharedPorts w sign).r s.basis=X)
    (hyv : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (he : OffsetBorrowedCanonical.Env w s.basis) :
    run (fieldProgramI w sign) m s=run (OffsetBorrowedField.program w sign) m s := by
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have eq := core_eq (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign) nd B X Y hx hy s m hs hr hyv
    (balancedSharedPorts_clean w sign s.basis he.1 he.2.1)
  have c := coreI_counts (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  simp only [fieldProgramI,OffsetBorrowedField.program]
  simp only [run_append,run_take]
  rw [c.2,eq]

end Field

section InverseField
open OffsetBorrowedInverse DirectSkywalk

def tailI (L : BalancedCircuit.Layout) : Program :=
  BalancedInverse.recoverSelectors L++rotateLeft (BalancedCircuit.rawTarget L)++
    undoFoldI L++BalancedInverse.undoPreparation L++
    BalancedInverse.rawSubtract L++(BalancedCircuit.seedViews L).reverse

/-- Inverse field kernel with the 256-wide subtraction. -/
def invFieldProgramI (w : Nat → Wire) (sign : Wire) : Program :=
  [.CX (balancedSharedPorts w sign).ymsb (balancedSharedPorts w sign).sourceGuard]++
    recoverParity w sign++tailI (balancedSharedPorts w sign)

theorem invFieldProgramI_counts (w : Nat → Wire) (sign : Wire) :
    toffoliCount (invFieldProgramI w sign)+1=toffoliCount (OffsetBorrowedInverse.program w sign) ∧
    measurementCount (invFieldProgramI w sign)=measurementCount (OffsetBorrowedInverse.program w sign) := by
  have a := foldI_counts (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  have b := fold_counts_old (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  simp only [invFieldProgramI,OffsetBorrowedInverse.program,tailI,OffsetBorrowedInverse.tail,
    toffoliCount_append,measurementCount_append,a.2.2.1,a.2.2.2,b.2.2.1,b.2.2.2]
  refine ⟨?_,?_⟩ <;> first | omega | trivial

private theorem lower_mem_work (L : BalancedCircuit.Layout) : L.lower∈BalancedCircuit.work L := by
  simp [BalancedCircuit.work]

private theorem one_mem_work (L : BalancedCircuit.Layout) : L.one∈BalancedCircuit.work L := by
  simp [BalancedCircuit.work]

private theorem carry_mem_work (L : BalancedCircuit.Layout) (a : Wire) (ha : a∈L.carry) :
    a∈BalancedCircuit.work L := List.mem_append_right _ ha

private theorem old_layout (L : BalancedCircuit.Layout) :
    invProgramI L=[.CX L.ymsb L.sourceGuard]++
      BalancedInverse.recoverParity L++tailI L := by
  simp only [invProgramI,tailI,List.append_assoc]

private theorem run_prefix (a b : Wire) (oracle rest : Program) (m : List Bool) (s : State) :
    run ([.CX a b]++oracle++rest) m s=
      run rest (m.drop (measurementCount oracle))
        (run oracle m (run [.CX a b] m s)) := by
  rw [List.append_assoc,run_append,run_take]
  change run (oracle++rest) m (run [.CX a b] m s)=_
  rw [run_append,run_take]

private theorem guard_records (a b : Wire) (m n : List Bool) (s : State) :
    run [.CX a b] m s=run [.CX a b] n s := by
  simp only [run]

private theorem index_ne (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i j : Nat) (hi : i<2314) (hj : j<2314) (hne : i≠j) : w i≠w j :=
  fun h => hne (skywalkShared_index_inj w hn i j hi hj h)

/-- The borrowed bank omits precisely the live source guard. -/
private theorem bank_guard_away (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (a : Wire) (ha : a∈OffsetCleanupBorrowedCaller.carry w) : a≠w 765 := by
  simp only [OffsetCleanupBorrowedCaller.carry,List.mem_append] at ha
  rcases ha with ha|ha
  · intro e
    exact arith_block_away w hn 765 512 253 (by omega) (by omega) (by omega) (e ▸ ha)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals exact index_ne w hn _ _ (by omega) (by omega) (by omega)

private theorem bank_target_away (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (a : Wire)
    (ha : a∈OffsetCleanupBorrowedCaller.carry w) : a∉(balancedSharedPorts w sign).r := by
  rw [balancedSharedPorts_r]
  simp only [OffsetCleanupBorrowedCaller.carry,List.mem_append] at ha
  rcases ha with ha|ha
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_range'_1] at hi
    exact arith_block_away w hn i 2056 256 (by omega) (by omega) (by omega)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals exact arith_block_away w hn _ 2056 256 (by omega) (by omega) (by omega)

/-- 254 padding records align the 764-record original recovery with the
510-record replacement. Their actual XOR outputs agree on independent records. -/
theorem invField_equivI (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool)
    (hR : signedRegValue (balancedSharedPorts w sign).r s.basis=R)
    (hY : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hS : s.basis sign=B)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hhigh : s.basis (w 1026)=false) :
    run (invFieldProgramI w sign) m s=
      run (invProgramI (balancedSharedPorts w sign))
        (List.replicate 254 false++m) s := by
  let L := balancedSharedPorts w sign
  let n := List.replicate 254 false++m
  let u := run [.CX L.ymsb L.sourceGuard] m s
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have nd := balancedSharedPorts_nodup w sign hn own
  have widths := balancedSharedPorts_widths w sign
  have clean := balancedSharedPorts_clean w sign s.basis hw hu
  have keep (a : Wire) (ha : a≠L.sourceGuard) : u.basis a=s.basis a := by
    simp only [u,run,writeBit,Function.update_of_ne ha]
  have dataAway (a : Wire) (ha : a∈L.r++L.y++L.carry) : a≠L.sourceGuard :=
    fun e => flagAway L nd L.sourceGuard (by simp) (e ▸ ha)
  have R₁ : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 (BalancedCleanup.widths L.toLayout widths).2.1 s.basis R hR)
    exact regValue_congr _ _ _ (fun a ha => keep a (dataAway a (by simp [ha])))
  have Y₁ : regValue L.y u.basis=encodeWord 256 Y := by
    apply Eq.trans _ (word_encoding L.y 256 (BalancedCleanup.widths L.toLayout widths).2.2.1 s.basis Y hY)
    exact regValue_congr _ _ _ (fun a ha => keep a (dataAway a (by simp [ha])))
  have scalar := scalarND L nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at scalar
  rcases scalar with ⟨⟨_,_,_,_,gSign,gLower,gOne,_,_,_⟩,_⟩
  have S₁ : u.basis sign=B := (keep L.sign (Ne.symm gSign)).trans hS
  have low₁ : u.basis (w 1797)=false :=
    (keep L.lower (Ne.symm gLower)).trans (clean L.lower (lower_mem_work L))
  have one₁ : u.basis (w 1027)=false :=
    (keep L.one (Ne.symm gOne)).trans (clean L.one (one_mem_work L))
  have high_ne : w 1026≠L.sourceGuard := by
    change w 1026≠w 765
    exact index_ne w hn 1026 765 (by omega) (by omega) (by omega)
  have high₁ : u.basis (w 1026)=false := (keep _ high_ne).trans hhigh
  have carry₁ : ∀a∈L.carry,u.basis a=false := by
    intro a ha
    exact (keep a (dataAway a (by simp [ha]))).trans (clean a (carry_mem_work L a ha))
  have bank₁ : ∀a∈OffsetCleanupBorrowedCaller.carry w,u.basis a=false := by
    intro a ha
    exact (keep a (by simpa only [L,balancedSharedPorts] using bank_guard_away w hn a ha)).trans
      (OffsetCleanupBorrowedCaller.entryCarry_clean w s.basis hw a ha)
  have oracle := recoverParity_equiv w sign hn hsOut R Y B hr hy u m n
    R₁ Y₁ S₁ low₁ one₁ high₁ carry₁ bank₁
  have oldCount : measurementCount (BalancedInverse.recoverParity L)=764 := by
    simpa only [BalancedInverse.recoverParity] using (BalancedCleanup.counts L.toLayout widths).2
  have freshCount : measurementCount (recoverParity w sign)=510 := by
    simpa only [recoverParity] using (BalancedCleanupOffsetZero.counts
      (OffsetCleanupBorrowedCaller.layout w sign) (OffsetCleanupBorrowedCaller.widths w sign)).2
  have align : n.drop 764=m.drop 510 := by simp [n,List.drop_append]
  have oldGuard : run [.CX L.ymsb L.sourceGuard] n s=u := guard_records _ _ n m s
  have freshRun : run (invFieldProgramI w sign) m s=
      run (tailI L) (m.drop 510) (run (recoverParity w sign) m u) := by
    rw [invFieldProgramI,run_prefix,freshCount]
  have oldRun : run (invProgramI L) n s=
      run (tailI L) (n.drop 764) (run (BalancedInverse.recoverParity L) n u) := by
    rw [old_layout,run_prefix,oldCount,oldGuard]
  rw [freshRun,oldRun,align,oracle]


theorem invField_eq (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool)
    (hR : signedRegValue (balancedSharedPorts w sign).r s.basis=R)
    (hY : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hS : s.basis sign=B)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hhigh : s.basis (w 1026)=false) :
    run (invFieldProgramI w sign) m s=run (OffsetBorrowedInverse.program w sign) m s := by
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have fresh := invField_equivI w sign hn hsOut R Y B hr hy s m hR hY hS hw hu hhigh
  have old := program_equiv w sign hn hsOut R Y B hr hy s m hR hY hS hw hu hhigh
  have mid := inv_eq (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
    (balancedSharedPorts_nodup w sign hn own) B R Y hr hy s (List.replicate 254 false++m) hS hR hY
    (balancedSharedPorts_clean w sign s.basis hw hu)
  rw [fresh,old,mid]

end InverseField

end ECDSAAdd.Entrant.LaneI


-- ===== LaneICell =====

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


-- ===== LaneISegment =====

/-! The selected field segment with every field cell using the 256-wide fold.
The single replacement point is `fieldSegmentI` for
`PenultimateMapped.fieldSegment` (= `selectedFieldSegment`): on the original
segment domain both produce the identical complete State. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic Secp256k1 BalancedField MappedCompressed CompressedAllocation
  CompressedFieldSupport
attribute [local irreducible] run logicalCell compressedHistoryEncode compressedHistoryDecode
  allGroupEncode

/-! ### Generic transports -/

/-- Renaming by a placement permutation preserves a State equality, given
only a clean input allocation boundary. -/
theorem rename_eq (e : Equiv.Perm Nat) (fix : ∀q,¬zeroRegion q → e q=q)
    (P P' : Program) (s : State) (m : List Bool)
    (hin : ∀q,zeroRegion q → s.basis (base q)=false)
    (h : run P' m s=run P m s) :
    run (renameProgram (shifted e) P') m s=run (renameProgram (shifted e) P) m s := by
  have input := shifted_zero_boundary e fix s hin
  apply pullState_perm_injective (shifted e)
  rw [run_rename _ (shifted e).injective,run_rename _ (shifted e).injective,input,h]

/-- A decoded window with any body equal on raw field frames is equal on
the encoded frame. -/
theorem encoded_window_eq (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (j : Nat) (hj : j < 170) (origin : BasisState) (legal : RawGroupLegal w 170 origin)
    (X Y : Fp) (body body' : Program)
    (support : wires body ⊆ groupReadSites w b sign eff (3*j))
    (sub : InstrSub body' body)
    (hc : measurementCount body'=measurementCount body)
    (heq : ∀ (t : State) (r : List Bool),
      PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        origin (centerWord X) (centerWord Y) t.basis → run body' r t=run body r t)
    (s : State) (m : List Bool) (input : EncodedFieldFrame w sign origin X Y s) :
    run (compressedHistoryDecode w (3*j)++body'++compressedHistoryEncode w (3*j)) m s=
      run (compressedHistoryDecode w (3*j)++body++compressedHistoryEncode w (3*j)) m s := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have hs := hp sign (by simp)
  have leg := frame_history_legal w sign hn hs origin raw.basis _ _ legal frame
  have factor := allGroupEncode_factor w pool hlo 170 j (by decide) hj raw
  have hE := otherGroupEncode_disjoint w pool hlo 170 j (by decide) hj
  have hB := otherGroupEncode_body_disjoint w b sign eff hn hlo
    (hp b (by simp)) hs (hp eff (by simp)) 170 j (by decide) hj body support
  have hB' := otherGroupEncode_body_disjoint w b sign eff hn hlo
    (hp b (by simp)) hs (hp eff (by simp)) 170 j (by decide) hj body' (sub.wires_sub.trans support)
  have zero := (compressedHistory_counts w (3*j)).2.2.2
  have shape (P : Program) : run (compressedHistoryDecode w (3*j)++P++compressedHistoryEncode w (3*j)) m s=
      run (compressedHistoryEncode w (3*j)) (m.drop (measurementCount P))
        (run P m (run (compressedHistoryDecode w (3*j)) []
          (run (otherGroupEncode w j 170) [] (run (compressedHistoryEncode w (3*j)) [] raw)))) := by
    rw [eq,factor]
    simp only [List.append_assoc]
    rw [run_append,zero,List.take_zero,List.drop_zero,run_append,run_take]
  have t1 := window_transport_other w (3*j) pool hlo (by omega)
    (otherGroupEncode w j 170) body hE hB raw [] [] [] m
    (m.drop (measurementCount body)) (leg j hj)
  have t2 := window_transport_other w (3*j) pool hlo (by omega)
    (otherGroupEncode w j 170) body' hE hB' raw [] [] [] m
    (m.drop (measurementCount body')) (leg j hj)
  rw [shape,shape,t1,t2,hc,heq raw m frame]

/-! ### Native packets -/

def baseGroupI (divide : Bool) (j : Nat) : Program :=
  compressedHistoryDecode base (3*j) ++
  (if divide then replayFI base (base 2400) (base 2409) (base 2410) (packetLetters j)
   else replayII base (base 2400) (base 2409) (base 2410) (packetLetters j)) ++
  compressedHistoryEncode base (3*j)

theorem baseGroup_shape (divide : Bool) (j : Nat) (hj : j < 170) :
    baseGroup divide j=compressedHistoryDecode base (3*j) ++
      (if divide then OffsetBorrowedCanonical.replay base (base 2400) (base 2409) (base 2410) (packetLetters j)
       else OffsetBorrowedInverseCanonical.replay base (base 2400) (base 2409) (base 2410) (packetLetters j)) ++
      compressedHistoryEncode base (3*j) := by
  rw [baseGroup_eq_packet divide j hj]
  cases divide <;> simp only [packetLetters,codecGroupForward,codecGroupBackward,
    OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,Bool.false_eq_true,
    if_false,if_true,List.append_assoc,List.append_nil,List.nil_append]

theorem baseGroupI_sub (divide : Bool) (j : Nat) (hj : j < 170) :
    InstrSub (baseGroupI divide j) (baseGroup divide j) := by
  rw [baseGroup_shape divide j hj]
  cases divide <;> simp only [baseGroupI,Bool.false_eq_true,if_false,if_true]
  · exact ((InstrSub.refl _).append (replayII_sub _ _ _ _ _)).append (InstrSub.refl _)
  · exact ((InstrSub.refl _).append (replayFI_sub _ _ _ _ _)).append (InstrSub.refl _)

theorem baseGroupI_counts (divide : Bool) (j : Nat) (hj : j < 170) :
    measurementCount (baseGroupI divide j)=measurementCount (baseGroup divide j) ∧
    toffoliCount (baseGroupI divide j)+3=toffoliCount (baseGroup divide j) := by
  rw [baseGroup_shape divide j hj]
  have len : (packetLetters j).length=3 := by simp [packetLetters]
  have f := replayFI_counts base (base 2400) (base 2409) (base 2410) (packetLetters j)
  have i := replayII_counts base (base 2400) (base 2409) (base 2410) (packetLetters j)
  rw [len] at f i
  cases divide <;> simp only [baseGroupI,Bool.false_eq_true,if_false,if_true,
    measurementCount_append,toffoliCount_append] <;> constructor <;> omega

private theorem packet_support (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base) :
    wires (if divide then OffsetBorrowedCanonical.replay base (base 2400) (base 2409) (base 2410) (packetLetters j)
       else OffsetBorrowedInverseCanonical.replay base (base 2400) (base 2409) (base 2410) (packetLetters j)) ⊆
      groupReadSites base (base 2400) (base 2409) (base 2410) (3*j) := by
  have h := packet_structural_support divide j hj hn hlo
  have shape : packetLetters j=[(packetLetters j).getD 0 ((0,0),(false,false)),
      (packetLetters j).getD 1 ((0,0),(false,false)),(packetLetters j).getD 2 ((0,0),(false,false))] := by
    simp [packetLetters]
  rw [shape]
  cases divide <;> simpa only [rawForwardPacket,rawBackwardPacket,Bool.false_eq_true,if_false,if_true] using h

theorem baseGroupI_eq (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (baseGroupI divide j) m s=run (baseGroup divide j) m s := by
  rw [baseGroup_shape divide j hj]
  have support := packet_support divide j hj hn hlo
  cases divide
  · simp only [baseGroupI,Bool.false_eq_true,if_false] at support ⊢
    exact encoded_window_eq base _ _ _ hn hlo hp j hj origin legal X Y _ _ support
      (replayII_sub _ _ _ _ _) (replayII_counts _ _ _ _ _).1
      (fun t r ht => replayII_eq base _ _ _ hn _ hf ho origin hg0 hs0 env X Y t r ht) s m input
  · simp only [baseGroupI,if_true] at support ⊢
    exact encoded_window_eq base _ _ _ hn hlo hp j hj origin legal X Y _ _ support
      (replayFI_sub _ _ _ _ _) (replayFI_counts _ _ _ _ _).1
      (fun t r ht => replayFI_eq base _ _ _ hn _ hf ho origin hg0 hs0 env X Y t r ht) s m input

def mappedGroupI (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (pi j)) (baseGroupI divide j)

theorem mappedGroupI_sub (divide : Bool) (j : Nat) (hj : j < 170) :
    InstrSub (mappedGroupI divide j) (mappedGroup divide j) := by
  rw [mappedGroup_eq_rename divide j hj]
  exact (baseGroupI_sub divide j hj).rename _

theorem mappedGroupI_counts (divide : Bool) (j : Nat) (hj : j < 170) :
    measurementCount (mappedGroupI divide j)=measurementCount (mappedGroup divide j) ∧
    toffoliCount (mappedGroupI divide j)+3=toffoliCount (mappedGroup divide j) := by
  rw [mappedGroup_eq_rename divide j hj]
  have a := renameProgram_counts (shifted (pi j)) (baseGroupI divide j)
  have b := renameProgram_counts (shifted (pi j)) (baseGroup divide j)
  have c := baseGroupI_counts divide j hj
  simp only [mappedGroupI]
  constructor <;> omega

theorem mappedGroupI_eq (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (mappedGroupI divide j) m s=run (mappedGroup divide j) m s := by
  have hin := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  rw [mappedGroup_eq_rename divide j hj]
  exact rename_eq (pi j) (fun q hq => pi_outside j q hj hq) _ _ s m hin
    (baseGroupI_eq divide j hj hn hlo ho hp hf origin hg0 hs0 env legal X Y s m input)

def mappedGroupsI (divide : Bool) (j n : Nat) : Program :=
  PacketSequence.program divide (mappedGroupI divide) j n

theorem mapped_sequence_eqI (divide : Bool) (j n : Nat) :
    PacketSequence.program divide (mappedGroup divide) j n=mappedGroups divide j n := by
  induction n generalizing j with
  | zero => simp only [PacketSequence.program,mappedGroups]
  | succ n ih => cases divide <;> simp only [PacketSequence.program,mappedGroups,
      Bool.false_eq_true,if_false,if_true,ih]

theorem mappedGroupsI_eq (divide : Bool) (j n : Nat) (bound : j+n ≤ 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : ∀k,k < 170 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters k))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (mappedGroupsI divide j n) m s=run (mappedGroups divide j n) m s := by
  let p : Nat → Program := fun k => if k < 170 then mappedGroupI divide k else mappedGroup divide k
  have peq : ∀ j n, j+n ≤ 170 → PacketSequence.program divide p j n=mappedGroupsI divide j n := by
    intro j n hb
    induction n generalizing j with
    | zero => rfl
    | succ n ih =>
      have head : p j=mappedGroupI divide j := by simp only [p,if_pos (show j < 170 by omega)]
      have rest := ih (j+1) (by omega)
      cases divide <;> simp only [mappedGroupsI,PacketSequence.program,Bool.false_eq_true,
        if_false,if_true] at rest ⊢ <;> rw [head,rest]
  have all := PacketSequence.frame divide p (mappedGroup divide)
    (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters k)) V)
    (fun V t => EncodedFieldFrame base (base 2409) origin V.1 V.2 t) 170
    (fun k => by
      by_cases hk : k < 170
      · simp only [p,if_pos hk]; exact (mappedGroupI_counts divide k hk).1
      · simp only [p,if_neg hk])
    (fun k hk V t records h => by
      have eq := mappedGroupI_eq divide k hk hn hlo ho hp (hf k hk) origin hg0 hs0 env legal V.1 V.2 t records h
      have old := mappedGroup_encoded_step divide k hk hn hlo ho hp (hf k hk) origin hg0 hs0 env legal
        V.1 V.2 t records h
      simp only [p,if_pos hk]
      rw [eq]
      exact ⟨rfl,old.1,old.2⟩) j n bound (X,Y) s m input
  rw [←mapped_sequence_eqI,←peq j n bound]
  exact all.1

theorem mappedGroupsI_sub (divide : Bool) (j n : Nat) (bound : j+n ≤ 170) :
    InstrSub (mappedGroupsI divide j n) (mappedGroups divide j n) := by
  rw [←mapped_sequence_eqI]
  induction n generalizing j with
  | zero => exact InstrSub.refl _
  | succ n ih =>
    have head := mappedGroupI_sub divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroupsI,PacketSequence.program,Bool.false_eq_true,if_false,if_true] at rest ⊢
    · exact rest.append head
    · exact head.append rest

theorem mappedGroupsI_counts (divide : Bool) (j n : Nat) (bound : j+n ≤ 170) :
    measurementCount (mappedGroupsI divide j n)=measurementCount (mappedGroups divide j n) ∧
    toffoliCount (mappedGroupsI divide j n)+3*n=toffoliCount (mappedGroups divide j n) := by
  rw [←mapped_sequence_eqI]
  induction n generalizing j with
  | zero => simp [mappedGroupsI,PacketSequence.program]
  | succ n ih =>
    have head := mappedGroupI_counts divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroupsI,PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      measurementCount_append,toffoliCount_append] at rest ⊢ <;> constructor <;> omega

end ECDSAAdd.Entrant.LaneI


-- ===== LaneITop =====

/-! First packet, endpoint cell, and the complete field segment with the
256-wide fold in every field cell. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic Secp256k1 BalancedField MappedCompressed CompressedAllocation
  CompressedFieldSupport EntryMappedFieldSegmentTrim
attribute [local irreducible] run logicalCell compressedHistoryEncode compressedHistoryDecode
  allGroupEncode mixedTranscriptUnitTrace

def unitI (i : Nat) : Bool×Bool := mixedTranscriptUnitTrace.getD i (false,false)

/-! ### First packet -/

def firstBodyFI : Program :=
  renameProgram base logicalZero ++
  cellFI base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410) (unitI 1).1 (unitI 1).2 ++
  cellFI base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410) (unitI 2).1 (unitI 2).2

def firstBodyII : Program :=
  cellII base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410) (unitI 2).1 (unitI 2).2 ++
  cellII base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410) (unitI 1).1 (unitI 1).2 ++
  renameProgram base logicalZero

def baseFirstGroupI (divide : Bool) : Program :=
  compressedHistoryDecode base 0 ++ (if divide then firstBodyFI else firstBodyII) ++
  compressedHistoryEncode base 0

def firstGroupI (divide : Bool) : Program :=
  renameProgram (shifted (pi 0)) (baseFirstGroupI divide)

def oldFirstBody (divide : Bool) : Program :=
  if divide then renameProgram base logicalZero ++
      OffsetBorrowedCanonical.cell base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410)
        (unitI 1).1 (unitI 1).2 ++
      OffsetBorrowedCanonical.cell base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410)
        (unitI 2).1 (unitI 2).2
  else OffsetBorrowedInverseCanonical.cell base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410)
        (unitI 2).1 (unitI 2).2 ++
      OffsetBorrowedInverseCanonical.cell base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410)
        (unitI 1).1 (unitI 1).2 ++
      renameProgram base logicalZero

theorem baseFirstGroup_shape (divide : Bool) :
    baseFirstGroup divide=compressedHistoryDecode base 0 ++ oldFirstBody divide ++
      compressedHistoryEncode base 0 := by
  cases divide <;> simp only [baseFirstGroup,oldFirstBody,base_cell_eq,unitI,
    Bool.false_eq_true,if_false,if_true]

theorem firstBody_sub (divide : Bool) :
    InstrSub (if divide then firstBodyFI else firstBodyII) (oldFirstBody divide) := by
  cases divide <;> simp only [firstBodyFI,firstBodyII,oldFirstBody,Bool.false_eq_true,if_false,if_true]
  · exact ((cellII_sub _ _ _ _ _ _ _ _).append (cellII_sub _ _ _ _ _ _ _ _)).append (InstrSub.refl _)
  · exact ((InstrSub.refl _).append (cellFI_sub _ _ _ _ _ _ _ _)).append (cellFI_sub _ _ _ _ _ _ _ _)

theorem firstBody_counts (divide : Bool) :
    measurementCount (if divide then firstBodyFI else firstBodyII)=measurementCount (oldFirstBody divide) ∧
    toffoliCount (if divide then firstBodyFI else firstBodyII)+2=toffoliCount (oldFirstBody divide) := by
  have a1 := cellFI_counts base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410) (unitI 1).1 (unitI 1).2
  have a2 := cellFI_counts base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410) (unitI 2).1 (unitI 2).2
  have b1 := cellII_counts base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410) (unitI 1).1 (unitI 1).2
  have b2 := cellII_counts base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410) (unitI 2).1 (unitI 2).2
  cases divide <;> simp only [firstBodyFI,firstBodyII,oldFirstBody,Bool.false_eq_true,if_false,if_true,
    measurementCount_append,toffoliCount_append] <;> constructor <;> omega

private theorem first_layouts
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0)) (i : Nat)
    (hi : i < 3) :
    BalancedTranscriptLayout (balancedSharedPorts base (base 2409)) (base 2400) (base i) (base (1028+i))
      (base 2410) := by
  have eq := mixedTape_base_getD i (by omega)
  have mem : (mixedTranscriptTape base).getD i ((0,0),(false,false))∈packetLetters 0 := by
    rcases (show i=0 ∨ i=1 ∨ i=2 by omega) with rfl|rfl|rfl <;> simp [packetLetters]
  have layout := balancedSharedTranscriptLayout_direct base (base 2400)
    ((mixedTranscriptTape base).getD i ((0,0),(false,false))).1.1
    ((mixedTranscriptTape base).getD i ((0,0),(false,false))).1.2
    (base 2409) (base 2410) (hf _ mem) ho
  rw [eq] at layout
  exact layout

theorem firstBody_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (X Y : Fp) (t : State) (r : List Bool)
    (h : PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y) t.basis) :
    run (if divide then firstBodyFI else firstBodyII) r t=run (oldFirstBody divide) r t := by
  have l0 := first_layouts ho hf 0 (by decide)
  have l1 := first_layouts ho hf 1 (by decide)
  have l2 := first_layouts ho hf 2 (by decide)
  have hS := ho (base 2409) (by simp)
  have hE := ho (base 2410) (by simp)
  cases divide
  · simp only [firstBodyII,oldFirstBody,Bool.false_eq_true,if_false]
    have m2 := (cellII_counts base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410)
      (unitI 2).1 (unitI 2).2).1
    have m1 := (cellII_counts base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410)
      (unitI 1).1 (unitI 1).2).1
    apply seq_eq _ _ _ _ t r (by simp only [measurementCount_append,m1,m2]) ?_ rfl
    · have fr := OffsetBorrowedInverseCanonical.cell_frame base (base 2400) (base 2) (base (1028+2))
        (base 2409) (base 2410) (unitI 2).1 (unitI 2).2 hn l2 hS hE origin hg0 hs0 env X Y
      apply seq_eq _ _ _ _ t _ (cellII_counts _ _ _ _ _ _ _ _).1
        (cellII_eq _ _ _ _ _ _ _ _ hn l2 hS hE origin hg0 hs0 env X Y t _ h)
      exact cellII_eq _ _ _ _ _ _ _ _ hn l1 hS hE origin hg0 hs0 env _ _ _ _ (fr t _ h).2
  · simp only [firstBodyFI,oldFirstBody,if_true]
    have sw := EntrySelectedSwapFrame.selectedSwap_frame base (base 2400) (base 0) (base (1028+0))
      (base 2409) (base 2410) (unitI 0).2 l0 origin hs0 X Y
    have zeroEq : renameProgram base logicalZero=EntryFieldSeedCancellation.selectedSwap base (base 2400)
        (base (1028+0)) (base 2409) (base 2410) (unitI 0).2 := by
      have rmap : (balancedSharedPorts base (base 2409)).r=
          (balancedSharedPorts id 2409).r.map base := by
        simpa only [Function.comp_id] using FieldRename.shared_r_map base id 2409
      have ymap : (balancedSharedPorts base (base 2409)).y=
          (balancedSharedPorts id 2409).y.map base := by
        simpa only [Function.comp_id] using FieldRename.shared_y_map base id 2409
      simp only [logicalZero,EntryFieldSeedCancellation.selectedSwap,FieldRename.selectWindow_natural,
        FieldRename.swapRegisters_natural,rmap,ymap,unitI]
    have fr1 := OffsetBorrowedCanonical.cell_frame base (base 2400) (base 1) (base (1028+1))
      (base 2409) (base 2410) (unitI 1).1 (unitI 1).2 hn l1 hS hE origin hg0 hs0 env
    have mc1 := (cellFI_counts base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410)
      (unitI 1).1 (unitI 1).2).1
    rw [zeroEq]
    apply seq_eq _ _ _ _ t r (by simp only [measurementCount_append,mc1]) ?_ ?_
    · apply seq_eq _ _ _ _ t _ rfl rfl
      exact cellFI_eq _ _ _ _ _ _ _ _ hn l1 hS hE origin hg0 hs0 env _ _ _ _ (sw t _ h).2
    · exact cellFI_eq _ _ _ _ _ _ _ _ hn l2 hS hE origin hg0 hs0 env _ _ _ _
        ((sw.seq (fr1 _ _)) t _ h).2

theorem firstGroupI_sub (divide : Bool) : InstrSub (firstGroupI divide) (firstGroup divide) := by
  rw [firstGroup_eq_rename]
  apply InstrSub.rename
  rw [baseFirstGroup_shape]
  exact ((InstrSub.refl _).append (firstBody_sub divide)).append (InstrSub.refl _)

theorem firstGroupI_counts (divide : Bool) :
    measurementCount (firstGroupI divide)=measurementCount (firstGroup divide) ∧
    toffoliCount (firstGroupI divide)+2=toffoliCount (firstGroup divide) := by
  have a := renameProgram_counts (shifted (pi 0)) (baseFirstGroupI divide)
  have b := renameProgram_counts (shifted (pi 0))
    (compressedHistoryDecode base 0 ++ oldFirstBody divide ++ compressedHistoryEncode base 0)
  have c := firstBody_counts divide
  rw [firstGroup_eq_rename,baseFirstGroup_shape]
  simp only [firstGroupI]
  rw [a.1,a.2,b.1,b.2]
  simp only [baseFirstGroupI,measurementCount_append,toffoliCount_append]
  constructor <;> omega

theorem firstGroupI_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (firstGroupI divide) m s=run (firstGroup divide) m s := by
  have hin := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  rw [firstGroup_eq_rename]
  apply rename_eq (pi 0) (fun q hq => pi_outside 0 q (by decide) hq) _ _ s m hin
  have support : wires (oldFirstBody divide) ⊆ groupReadSites base (base 2400) (base 2409) (base 2410) (3*0) := by
    cases divide
    · have h := inverseBody_support hn hlo
      simpa only [inverseBody,oldFirstBody,base_cell_eq,unitI,Bool.false_eq_true,if_false,Nat.mul_zero] using h
    · have h := EntryBodySupport.first_body_support hn hlo
      simpa only [oldFirstBody,base_cell_eq,unitI,if_true,Nat.mul_zero] using h
  have w := encoded_window_eq base _ _ _ hn hlo hp 0 (by decide) origin legal X Y _ _ support
    (firstBody_sub divide) (firstBody_counts divide).1
    (fun t r ht => firstBody_eq divide hn ho hf origin hg0 hs0 env X Y t r ht) s m input
  simp only [Nat.mul_zero] at w
  rw [baseFirstGroup_shape]
  exact w

/-! ### Endpoint cell 510 -/

def endBaseI (divide : Bool) : Program :=
  if divide then trimFI base (base 2400) (base 510) (base 2409) (unitI 510).1
  else trimII base (base 2400) (base 510) (base 2409) (unitI 510).1

def endI (divide : Bool) : Program := renameProgram (shifted pi0) (endBaseI divide)

theorem end_old_shape (divide : Bool) :
    renameProgram allPlaced (PenultimateSwapIdentity.cell divide)=
      renameProgram (shifted pi0) (if divide then EndpointSwapTrim.forward base (base 2400) (base 510)
        (base 2409) (unitI 510).1 else EndpointSwapTrim.inverse base (base 2400) (base 510)
        (base 2409) (unitI 510).1) := by
  have rename : renameProgram allPlaced (PenultimateSwapIdentity.cell divide)=
      renameProgram (shifted pi0) (renameProgram base (PenultimateSwapIdentity.cell divide)) := by
    rw [renameProgram_comp]
    congr 1
  rw [rename,PenultimateMappedCellProof.cell_natural]
  rfl

theorem endBaseI_sub (divide : Bool) :
    InstrSub (endBaseI divide) (if divide then EndpointSwapTrim.forward base (base 2400) (base 510)
        (base 2409) (unitI 510).1 else EndpointSwapTrim.inverse base (base 2400) (base 510)
        (base 2409) (unitI 510).1) := by
  have h := trim_sub base (base 2400) (base 510) (base 2409) (unitI 510).1
  cases divide <;> simp only [endBaseI,Bool.false_eq_true,if_false,if_true]
  · exact h.2
  · exact h.1

theorem endI_sub (divide : Bool) :
    InstrSub (endI divide) (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) := by
  rw [end_old_shape]
  exact (endBaseI_sub divide).rename _

theorem endI_counts (divide : Bool) :
    measurementCount (endI divide)=measurementCount (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) ∧
    toffoliCount (endI divide)+1=toffoliCount (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) := by
  rw [end_old_shape]
  have a := renameProgram_counts (shifted pi0) (endBaseI divide)
  have b := renameProgram_counts (shifted pi0) (if divide then EndpointSwapTrim.forward base (base 2400) (base 510)
        (base 2409) (unitI 510).1 else EndpointSwapTrim.inverse base (base 2400) (base 510)
        (base 2409) (unitI 510).1)
  have c := trim_counts base (base 2400) (base 510) (base 2409) (unitI 510).1
  simp only [endI]
  cases divide <;> simp only [endBaseI,Bool.false_eq_true,if_false,if_true] at a b ⊢ <;> constructor <;> omega

theorem endI_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (endI divide) m s=run (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) m s := by
  have hin := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  rw [end_old_shape]
  apply rename_eq pi0 pi0_outside _ _ s m hin
  let unit := mixedTranscriptUnitTrace.getD 510 (false,false)
  have letter : tapeLetter 510=((base 510,base 1538),unit) := by
    simp only [tapeLetter,mixedTape_base_getD 510 (by decide),Nat.reduceAdd,unit]
  have layout : MixedTranscriptFieldLayout base (base 2400) (base 510) (base 1538)
      (base 2409) (base 2410) := by
    simpa only [mixedTape_base_getD 510 (by decide),Nat.reduceAdd] using
      mixedTape_getD_layout base (base 2400) (base 2409) (base 2410) hf 510 (by decide)
  have hl := balancedSharedTranscriptLayout_direct base (base 2400) (base 510)
    (base 1538) (base 2409) (base 2410) layout ho
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have rawEq : run (endBaseI divide) m raw=
      run (if divide then EndpointSwapTrim.forward base (base 2400) (base 510)
        (base 2409) (unitI 510).1 else EndpointSwapTrim.inverse base (base 2400) (base 510)
        (base 2409) (unitI 510).1) m raw :=
    trim_eq divide base (base 2400) (base 510) (base 1538) (base 2409) (base 2410) (unitI 510).1
      hn hl (ho _ (by simp)) origin hg0 env X Y raw m frame
  have aligned : IndexedLetters base 510 [tapeLetter 510] := by
    simp only [letter,IndexedLetters]
    exact ⟨trivial,trivial⟩
  have dis := tail_replay_disjoint base (base 2400) (base 2409) (base 2410)
    hn hlo hp 510 [tapeLetter 510] (by omega) (by simp) aligned
  have oldDis : Disjoint (wires (allGroupEncode base 170))
      (wires (renameProgram base (logicalCell divide 510))) := by
    rw [FieldRename.logical_cell_natural]
    cases divide
    · simpa only [OffsetBorrowedInverseCanonical.replay,letter,List.append_nil,List.nil_append,
        Bool.false_eq_true,if_false,Nat.reduceAdd] using dis.2
    · simpa only [OffsetBorrowedCanonical.replay,letter,List.append_nil,List.nil_append,
        if_true,Nat.reduceAdd] using dis.1
  have sub : wires (if divide then EndpointSwapTrim.forward base (base 2400) (base 510)
        (base 2409) (unitI 510).1 else EndpointSwapTrim.inverse base (base 2400) (base 510)
        (base 2409) (unitI 510).1)⊆wires (renameProgram base (logicalCell divide 510)) := by
    have e := PenultimateMappedCellProof.cell_natural base divide
    have s2 : wires (renameProgram base (PenultimateSwapIdentity.cell divide))⊆
        wires (renameProgram base (logicalCell divide 510)) := by
      rw [renameProgram_support,renameProgram_support]
      exact Finset.image_mono base (PenultimateMappedCellProof.logical_support_subset divide)
    rw [e] at s2
    exact s2
  have oldDis' := oldDis.mono_right sub
  have newDis := oldDis'.mono_right (endBaseI_sub divide).wires_sub
  have newCommute := (run_disjoint_commute (allGroupEncode base 170) (endBaseI divide) newDis [] m raw).symm
  have oldCommute := (run_disjoint_commute (allGroupEncode base 170) _ oldDis' [] m raw).symm
  rw [encoded,newCommute,oldCommute,rawEq]

/-! ### Complete field segment -/

def replayI (divide : Bool) : Program :=
  if divide then firstGroupI true ++ mappedGroupsI true 1 169 ++ endI true
  else endI false ++ mappedGroupsI false 1 169 ++ firstGroupI false

def fieldSegmentI (divide : Bool) : Program :=
  (if divide then [] else renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) ++
  renameProgram allPlaced (converterPair false) ++ replayI divide ++
  renameProgram allPlaced (converterPair true) ++
  (if divide then renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) else [])

theorem fieldSegmentI_sub (divide : Bool) :
    InstrSub (fieldSegmentI divide) (PenultimateMapped.fieldSegment divide) := by
  have g := mappedGroupsI_sub divide 1 169 (by decide)
  cases divide <;> simp only [fieldSegmentI,PenultimateMapped.fieldSegment,replayI,PenultimateMapped.replay,
    Bool.false_eq_true,if_false,if_true]
  · exact ((((InstrSub.refl _).append (InstrSub.refl _)).append
      (((endI_sub false).append g).append (firstGroupI_sub false))).append (InstrSub.refl _)).append
      (InstrSub.refl _)
  · exact ((((InstrSub.refl _).append (InstrSub.refl _)).append
      (((firstGroupI_sub true).append g).append (endI_sub true))).append (InstrSub.refl _)).append
      (InstrSub.refl _)

theorem fieldSegmentI_counts (divide : Bool) :
    measurementCount (fieldSegmentI divide)=measurementCount (PenultimateMapped.fieldSegment divide) ∧
    toffoliCount (fieldSegmentI divide)+510=toffoliCount (PenultimateMapped.fieldSegment divide) := by
  have g := mappedGroupsI_counts divide 1 169 (by decide)
  have f := firstGroupI_counts divide
  have t := endI_counts divide
  cases divide <;> simp only [fieldSegmentI,PenultimateMapped.fieldSegment,replayI,PenultimateMapped.replay,
    Bool.false_eq_true,if_false,if_true,measurementCount_append,toffoliCount_append] <;>
    constructor <;> omega

theorem seq_eq_frame (P P' Q Q' : Program) (F : State → Prop) (s : State) (m : List Bool)
    (hc : measurementCount P'=measurementCount P)
    (hp : ∀ r, run P' r s=run P r s) (hF : ∀ r, F (run P r s))
    (hq : ∀ t r, F t → run Q' r t=run Q r t) :
    run (P'++Q') m s=run (P++Q) m s :=
  seq_eq P P' Q Q' s m hc (hp _) (hq _ _ (hF _))

theorem fieldSegmentI_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    run (fieldSegmentI divide) m s=run (PenultimateMapped.fieldSegment divide) m s := by
  have layouts := packet_layouts (base 2400) (base 2409) (base 2410) hf
  let E : Fp → Fp → State → Prop := fun X Y t => EncodedFieldFrame base (base 2409) origin X Y t
  cases divide
  · have shapeI : fieldSegmentI false=renameProgram allPlaced
        (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) ++
        (renameProgram allPlaced (converterPair false) ++ (endI false ++ (mappedGroupsI false 1 169 ++
        (firstGroupI false ++ renameProgram allPlaced (converterPair true))))) := by
      simp only [fieldSegmentI,replayI,Bool.false_eq_true,if_false,List.append_nil,List.append_assoc]
    have shapeO : PenultimateMapped.fieldSegment false=renameProgram allPlaced
        (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) ++
        (renameProgram allPlaced (converterPair false) ++
        (renameProgram allPlaced (PenultimateSwapIdentity.cell false) ++ (mappedGroups false 1 169 ++
        (firstGroup false ++ renameProgram allPlaced (converterPair true))))) := by
      simp only [PenultimateMapped.fieldSegment,PenultimateMapped.replay,Bool.false_eq_true,if_false,
        List.append_nil,List.append_assoc]
    rw [shapeI,shapeO]
    apply seq_eq_frame _ _ _ _ (fun t => EncodedCanonicalFrame origin Y Y t) s m rfl (fun _ => rfl)
      (fun r => by simpa only [copyPairAt] using (mapped_copy_fill hn origin Y s r input).2)
    intro s1 m1 c1
    apply seq_eq_frame _ _ _ _ (E Y Y) s1 m1 rfl (fun _ => rfl)
      (fun r => by
        have c := (encoded_center_pair hn origin hw hu hr hy Y Y s1 r c1).2
        rw [←converterPair_placement false] at c
        exact c)
    intro s2 m2 c2
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s2 m2 (endI_counts false).1
      (fun r => endI_eq false hn hlo ho hp hf origin hg0 hs0 env Y Y s2 r c2)
      (fun r => by
        rw [PenultimateMappedCellProof.inverse_cell_eq hn hlo ho hp hf origin hg0 hs0 env legal Y s2 r r c2]
        exact ⟨_,_,(trimCell_step false hn hlo ho hp hf origin hg0 hs0 env legal Y Y s2 r c2).2.2⟩)
    rintro s3 m3 ⟨X3,Y3,c3⟩
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s3 m3
      (mappedGroupsI_counts false 1 169 (by decide)).1
      (fun r => mappedGroupsI_eq false 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal _ _ s3 r c3)
      (fun r => ⟨_,_,(mappedGroups_frame false 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal
        _ _ s3 r c3).2.2⟩)
    rintro s4 m4 ⟨X4,Y4,c4⟩
    exact seq_eq _ _ _ _ s4 m4 (firstGroupI_counts false).1
      (firstGroupI_eq false hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal _ _ s4 _ c4) rfl
  · have shapeI : fieldSegmentI true=renameProgram allPlaced (converterPair false) ++
        (firstGroupI true ++ (mappedGroupsI true 1 169 ++ (endI true ++
        (renameProgram allPlaced (converterPair true) ++ renameProgram allPlaced
          (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a))))) := by
      simp only [fieldSegmentI,replayI,if_true,List.nil_append,List.append_assoc]
    have shapeO : PenultimateMapped.fieldSegment true=renameProgram allPlaced (converterPair false) ++
        (firstGroup true ++ (mappedGroups true 1 169 ++
        (renameProgram allPlaced (PenultimateSwapIdentity.cell true) ++
        (renameProgram allPlaced (converterPair true) ++ renameProgram allPlaced
          (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a))))) := by
      simp only [PenultimateMapped.fieldSegment,PenultimateMapped.replay,if_true,List.nil_append,
        List.append_assoc]
    rw [shapeI,shapeO]
    apply seq_eq_frame _ _ _ _ (E Y 0) s m rfl (fun _ => rfl)
      (fun r => by
        have c := (encoded_center_pair hn origin hw hu hr hy Y 0 s r input).2
        rw [←converterPair_placement false] at c
        exact c)
    intro s1 m1 c1
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s1 m1 (firstGroupI_counts true).1
      (fun r => firstGroupI_eq true hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal Y 0 s1 r c1)
      (fun r => ⟨_,_,(firstGroup_forward_step hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal
        Y s1 r c1).2⟩)
    rintro s2 m2 ⟨X2,Y2,c2⟩
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s2 m2
      (mappedGroupsI_counts true 1 169 (by decide)).1
      (fun r => mappedGroupsI_eq true 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal _ _ s2 r c2)
      (fun r => ⟨_,_,(mappedGroups_frame true 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal
        _ _ s2 r c2).2.2⟩)
    rintro s3 m3 ⟨X3,Y3,c3⟩
    exact seq_eq _ _ _ _ s3 m3 (endI_counts true).1
      (endI_eq true hn hlo ho hp hf origin hg0 hs0 env _ _ s3 _ c3) rfl

/-! ### Public segment facts (same statements as for `selectedFieldSegment`) -/

theorem fieldSegmentI_support (divide : Bool) : wires (fieldSegmentI divide) ⊆ slots.toFinset :=
  (fieldSegmentI_sub divide).wires_sub.trans (selectedFieldSegment_support divide)

theorem fieldSegmentI_physical (divide : Bool) : GatePhysical (fieldSegmentI divide) :=
  (fieldSegmentI_sub divide).physical (selectedFieldSegment_physical divide)

theorem fieldSegmentI_resources (divide : Bool) :
    toffoliCount (fieldSegmentI divide)=(if divide then 656540 else 657050) ∧
    measurementCount (fieldSegmentI divide)=525980 := by
  have c := fieldSegmentI_counts divide
  have o := selectedFieldSegment_counts divide
  simp only [selectedFieldSegment] at o
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true] at o ⊢ <;> constructor <;> omega

end ECDSAAdd.Entrant.LaneI


-- ===== LaneIReplay =====

/-! The entry-trimmed replay with every field cell using the 256-wide fold. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic Secp256k1 BalancedField MappedCompressed CompressedAllocation
  CompressedFieldSupport EntryMappedFieldSegmentTrim
attribute [local irreducible] run logicalCell compressedHistoryEncode compressedHistoryDecode
  allGroupEncode mixedTranscriptUnitTrace

theorem replayI_sub (divide : Bool) : InstrSub (replayI divide) (PenultimateMapped.replay divide) := by
  have g := mappedGroupsI_sub divide 1 169 (by decide)
  cases divide <;> simp only [replayI,PenultimateMapped.replay,Bool.false_eq_true,if_false,if_true]
  · exact ((endI_sub false).append g).append (firstGroupI_sub false)
  · exact ((firstGroupI_sub true).append g).append (endI_sub true)

theorem replayI_counts (divide : Bool) :
    measurementCount (replayI divide)=measurementCount (PenultimateMapped.replay divide) ∧
    toffoliCount (replayI divide)+510=toffoliCount (PenultimateMapped.replay divide) := by
  have g := mappedGroupsI_counts divide 1 169 (by decide)
  have f := firstGroupI_counts divide
  have t := endI_counts divide
  cases divide <;> simp only [replayI,PenultimateMapped.replay,Bool.false_eq_true,if_false,if_true,
    measurementCount_append,toffoliCount_append] <;> constructor <;> omega

/-- Replay equality; the entry payload is the one both segments present. -/
theorem replayI_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (Y : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin Y (if divide then 0 else Y) s) :
    run (replayI divide) m s=run (PenultimateMapped.replay divide) m s := by
  have layouts := packet_layouts (base 2400) (base 2409) (base 2410) hf
  let E : Fp → Fp → State → Prop := fun X Y t => EncodedFieldFrame base (base 2409) origin X Y t
  cases divide
  · simp only [Bool.false_eq_true,if_false] at input
    have shapeI : replayI false=endI false ++ (mappedGroupsI false 1 169 ++ firstGroupI false) := by
      simp only [replayI,Bool.false_eq_true,if_false,List.append_assoc]
    have shapeO : PenultimateMapped.replay false=renameProgram allPlaced (PenultimateSwapIdentity.cell false) ++
        (mappedGroups false 1 169 ++ firstGroup false) := by
      simp only [PenultimateMapped.replay,Bool.false_eq_true,if_false,List.append_assoc]
    rw [shapeI,shapeO]
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s m (endI_counts false).1
      (fun r => endI_eq false hn hlo ho hp hf origin hg0 hs0 env Y Y s r input)
      (fun r => by
        rw [PenultimateMappedCellProof.inverse_cell_eq hn hlo ho hp hf origin hg0 hs0 env legal Y s r r input]
        exact ⟨_,_,(trimCell_step false hn hlo ho hp hf origin hg0 hs0 env legal Y Y s r input).2.2⟩)
    rintro s3 m3 ⟨X3,Y3,c3⟩
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s3 m3
      (mappedGroupsI_counts false 1 169 (by decide)).1
      (fun r => mappedGroupsI_eq false 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal _ _ s3 r c3)
      (fun r => ⟨_,_,(mappedGroups_frame false 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal
        _ _ s3 r c3).2.2⟩)
    rintro s4 m4 ⟨X4,Y4,c4⟩
    exact firstGroupI_eq false hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal _ _ s4 _ c4
  · simp only [if_true] at input
    have shapeI : replayI true=firstGroupI true ++ (mappedGroupsI true 1 169 ++ endI true) := by
      simp only [replayI,if_true,List.append_assoc]
    have shapeO : PenultimateMapped.replay true=firstGroup true ++ (mappedGroups true 1 169 ++
        renameProgram allPlaced (PenultimateSwapIdentity.cell true)) := by
      simp only [PenultimateMapped.replay,if_true,List.append_assoc]
    rw [shapeI,shapeO]
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s m (firstGroupI_counts true).1
      (fun r => firstGroupI_eq true hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal Y 0 s r input)
      (fun r => ⟨_,_,(firstGroup_forward_step hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal
        Y s r input).2⟩)
    rintro s2 m2 ⟨X2,Y2,c2⟩
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s2 m2
      (mappedGroupsI_counts true 1 169 (by decide)).1
      (fun r => mappedGroupsI_eq true 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal _ _ s2 r c2)
      (fun r => ⟨_,_,(mappedGroups_frame true 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal
        _ _ s2 r c2).2.2⟩)
    rintro s3 m3 ⟨X3,Y3,c3⟩
    exact endI_eq true hn hlo ho hp hf origin hg0 hs0 env _ _ s3 _ c3

end ECDSAAdd.Entrant.LaneI


-- ===== LaneIHalf =====

/-! Halving-endpoint field segment with every field cell using the 256-wide
fold.  `segmentI` is state-equal to `HalfField.segment` on its domain. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic Secp256k1 BalancedField MappedCompressed CompressedAllocation
  CompressedFieldSupport HalfField
attribute [local irreducible] run allGroupEncode

def segmentI (divide : Bool) : Program :=
  if divide then centerT++(replayI true++(copyN++canonT))
  else centerT++(copyN++(replayI false++canonT))

theorem segmentI_sub (divide : Bool) : InstrSub (segmentI divide) (HalfField.segment divide) := by
  cases divide <;> simp only [segmentI,HalfField.segment,Bool.false_eq_true,if_false,if_true]
  · exact (InstrSub.refl _).append ((InstrSub.refl _).append ((replayI_sub false).append (InstrSub.refl _)))
  · exact (InstrSub.refl _).append ((replayI_sub true).append ((InstrSub.refl _).append (InstrSub.refl _)))

theorem segmentI_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    run (segmentI divide) m s=run (HalfField.segment divide) m s := by
  let E : Fp → Fp → State → Prop := fun X Y t => EncodedFieldFrame base (base 2409) origin X Y t
  cases divide
  · simp only [segmentI,HalfField.segment,Bool.false_eq_true,if_false]
    apply seq_eq_frame _ _ _ _ (E (Y/2) 0) s m rfl (fun _ => rfl)
      (fun r => (center_frame hn origin hw hu hr hy Y s r input).2)
    intro s1 m1 c1
    apply seq_eq_frame _ _ _ _ (E (Y/2) (Y/2)) s1 m1 rfl (fun _ => rfl)
      (fun r => (copy_fill hn origin (Y/2) s1 r c1).2)
    intro s2 m2 c2
    exact seq_eq _ _ _ _ s2 m2 (replayI_counts false).1
      (replayI_eq false hn hlo ho hp hf origin hg0 hs0 env legal (Y/2) s2 _ (by simpa using c2)) rfl
  · simp only [segmentI,HalfField.segment,if_true]
    apply seq_eq_frame _ _ _ _ (E (Y/2) 0) s m rfl (fun _ => rfl)
      (fun r => (center_frame hn origin hw hu hr hy Y s r input).2)
    intro s1 m1 c1
    exact seq_eq _ _ _ _ s1 m1 (replayI_counts true).1
      (replayI_eq true hn hlo ho hp hf origin hg0 hs0 env legal (Y/2) s1 _ (by simpa using c1)) rfl

theorem segmentI_support (divide : Bool) : wires (segmentI divide) ⊆ slots.toFinset :=
  (segmentI_sub divide).wires_sub.trans (HalfField.segment_support divide)

theorem segmentI_physical (divide : Bool) : GatePhysical (segmentI divide) :=
  (segmentI_sub divide).physical (HalfField.segment_physical divide)

theorem segmentI_avoid (divide : Bool) : Avoid (segmentI divide) :=
  avoid_sub (segmentI_sub divide).wires_sub (HalfLane.segment_avoid divide)

theorem segmentI_gateSlots_le (divide : Bool) :
    Challenge.gateSlots (segmentI divide) ≤ 14100000 :=
  (segmentI_sub divide).slots.trans (HalfLane.segment_gateSlots_le divide)

theorem segmentI_counts (divide : Bool) :
    toffoliCount (segmentI divide)=(if divide then 653990 else 654500) ∧
    measurementCount (segmentI divide)=523430 := by
  have c := replayI_counts divide
  have o := HalfField.segment_counts divide
  cases divide <;> simp only [segmentI,HalfField.segment,Bool.false_eq_true,if_false,if_true,
    measurementCount_append,toffoliCount_append] at o ⊢ <;> constructor <;> omega

end ECDSAAdd.Entrant.LaneI
