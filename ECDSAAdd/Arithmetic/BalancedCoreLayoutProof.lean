import ECDSAAdd.Arithmetic.BalancedRawCircuitProof

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField

def work (L : Layout) := [L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.lower,L.one]++L.carry

theorem scalarND (L : Layout) (hn : L.wires.Nodup) :
    [L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0].Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem seedND (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    [L.sourceGuard,L.one,L.parity,L.ymsb,L.rmsb,L.ylow.getD 0 0,L.r0].Nodup := by
  cases hy : L.ylow with
  | nil => have h := hw.2.1; simp [hy] at h
  | cons a as =>
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [Layout.wires,BalancedCleanup.Layout.wires,hy,List.getD_cons_zero,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega

theorem rawTargetND (L : Layout) (hn : L.wires.Nodup) : (rawTarget L).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q; have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,rawTarget,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem allND (L : Layout) (hn : L.wires.Nodup) :
    ([L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]++
      (L.r++L.y++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q; have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem foldND (L : Layout) (hn : L.wires.Nodup) :
    ([L.plus,L.minus,L.parity]++(foldTarget L++[L.cout]++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q; have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,foldTarget,
    List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem flagAway (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
    q∉L.r++L.y++L.carry :=
  fun h => List.disjoint_left.mp (List.nodup_append'.mp (allND L hn)).2.2 hq h

theorem signed_extension (lo : List Wire) (msb guard : Wire) (b : BasisState)
    (hg : b guard=b msb) : signedRegValue ((lo++[msb])++[guard]) b=signedRegValue (lo++[msb]) b := by
  rw [signedRegValue_msb,signedRegValue_msb,regValue_append]
  cases hm : b msb <;>
    simp [hg,hm,regValue,List.length_append,Nat.pow_succ,Nat.cast_add,Nat.cast_mul] <;> ring

theorem word_encoding (r : List Wire) (n : Nat) (hn : r.length=n) (b : BasisState) (X : Int)
    (hx : signedRegValue r b=X) : regValue r b=encodeWord n X := by
  have he := encode_decodeWord n (regValue r b) (by simpa [hn] using regValue_lt r b)
  change encodeWord n (signedDecode n (regValue r b))=regValue r b at he
  change signedDecode r.length (regValue r b)=X at hx
  rw [hn] at hx
  rw [hx] at he
  exact he.symm

theorem word_sign (lo : List Wire) (msb : Wire) (b : BasisState) (X : Int)
    (hx : signedRegValue (lo++[msb]) b=X) : b msb=decide (X<0) := by
  have h := signedRegValue_neg_iff lo msb b
  rw [hx] at h
  cases hb : b msb
  · have hx0 : ¬X<0 := fun hn => by have hh := h.mp hn; simp [hb] at hh
    simp [hx0]
  · have hx0 : X<0 := h.mpr hb
    simp [hx0]

private theorem add_parity (X Y : Int) : originalParity (X+Y)=(originalParity Y ^^ originalParity X) := by
  have px := originalParity_value X
  have py := originalParity_value Y
  have pt := originalParity_value (X+Y)
  cases hx : originalParity X <;> cases hy : originalParity Y <;> cases ht : originalParity (X+Y)
  all_goals simp only [hx,hy,ht,Bool.false_eq_true,if_false,if_true] at px py pt ⊢
  all_goals first | rfl | omega

theorem raw_parity (S : Bool) (X Y : Int) :
    originalParity (rawSum S X Y)=(originalParity Y ^^ originalParity X) := by
  have neg : originalParity (-Y)=originalParity Y := by
    unfold originalParity
    apply decide_eq_decide.mpr
    omega
  cases S <;> simp only [rawSum,signedY,Bool.false_eq_true,if_false,if_true]
  · exact add_parity X Y
  · rw [add_parity,neg]

theorem word_parity (low : Wire) (tail : List Wire) (b : BasisState) (X : Int)
    (hx : signedRegValue (low::tail) b=X) : b low=originalParity X := by
  have h := signedRegValue_even_iff low tail b
  rw [hx] at h
  cases hb : b low
  · have he : X%2=0 := h.mpr hb
    simp [originalParity,he]
  · have he : X%2≠0 := fun he => by have hh := h.mp he; simp [hb] at hh
    simp [originalParity,he]

end ECDSAAdd.Arithmetic.BalancedCircuit
