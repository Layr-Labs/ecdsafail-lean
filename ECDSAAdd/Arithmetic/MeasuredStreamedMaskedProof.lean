import ECDSAAdd.Arithmetic.MaskedSquareCallback
import ECDSAAdd.Arithmetic.MeasuredStreamedLoopProof

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measured_leaf_bank_count (L : CuccaroStreamedSquareWideLayout) (n : Nat) (q : Wire) :
    (L.inputBank.take n++L.leafPad++L.leafCarry).count q≤
      L.core.work.count q+L.foldPad.count q := by
  have inputBound := (List.take_sublist n L.inputBank).count_le q
  have workSplit := congrArg (List.count q) (List.take_append_drop 129 L.core.work)
  have padSplit := congrArg (List.count q) (List.take_append_drop 1 L.foldPad)
  have tailBound := (List.take_sublist 130 (L.foldPad.drop 1)).count_le q
  simp only [inputBank,leafPad,leafCarry,List.count_append] at inputBound workSplit padSplit ⊢
  omega

theorem measured_leaf_nodup (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) :
    (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  have a := hs q
  have b := hd q
  have banks := L.measured_leaf_bank_count src.length q
  simp only [wires,CuccaroStreamedSquareLayout.wires,foldPad,List.count_cons,
    List.count_append,List.count_nil] at h a banks ⊢
  omega

theorem measured_leaf_banks_clean (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (hc : L.PairClean base) (n : Nat) :
    regValue (L.inputBank.take n) base=0 ∧ regValue L.leafPad base=0 ∧ regValue L.leafCarry base=0 := by
  refine ⟨?_,?_,?_⟩
  · apply (regValue_zero _ _).mpr
    intro q hq
    exact (regValue_zero _ _).mp hc.work q (List.mem_of_mem_take (List.mem_of_mem_take hq))
  · apply (regValue_zero _ _).mpr
    intro q hq
    exact (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_take hq)
  · apply (regValue_zero _ _).mpr
    intro q hq
    simp only [leafCarry,List.mem_append] at hq
    rcases hq with hq|hq
    · exact (regValue_zero _ _).mp hc.work q (List.mem_of_mem_drop hq)
    · exact (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop (List.mem_of_mem_take hq))

theorem withMeasuredSquare_eq_callback (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (src dst : List Wire) (body : Program) :
    L.withMeasuredSquare control src dst body=
      maskedSquareCallback control src (L.inputBank.take src.length) dst L.leafPad L.leafCarry L.core.cin body := by
  simp [withMeasuredSquare,maskedSquareCallback,maskedSquareAction,maskedSquareBody,List.append_assoc]

/-- Actual-layout callback theorem for the masked 128/129-bit square
producer and its independent cleanup within the existing Step 4 pool. -/
theorem withMeasuredSquare_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (hs2 : 2≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (body : Program) (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (L.withMeasuredSquare control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (L.withMeasuredSquare control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (L.withMeasuredSquare control src dst body) records s).basis q=s.basis q := by
  rw [L.withMeasuredSquare_eq_callback]
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  exact maskedSquareCallback_correct control L.core.cin src (L.inputBank.take src.length) dst
    L.leafPad L.leafCarry L.core.out body (L.measured_leaf_nodup control hn src dst hs hd)
    inputLen.symm (by rw [inputLen];exact hs2) (by rw [inputLen];exact hlen)
    (by rw [sizes.2.2.1]) (by rw [sizes.2.1,hlen];omega) s records banks.1 banks.2.1 banks.2.2
    hc.cin hzero V callback

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
