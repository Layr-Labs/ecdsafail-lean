import ECDSAAdd.Arithmetic.BalancedCoreComposeProof
import ECDSAAdd.Arithmetic.BalancedInverseComposeFold

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
