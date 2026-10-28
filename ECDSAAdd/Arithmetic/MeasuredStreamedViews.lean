import ECDSAAdd.Arithmetic.MeasuredStreamedMaskedProof
import ECDSAAdd.Math.ExactStreamedFold

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measured_short_canonical (src : List Wire) (shift : Nat) (base : BasisState)
    (hlen : src.length+shift≤162) : regValue src base*2^shift<SquareReduction.p := by
  have bound := Nat.mul_lt_mul_of_pos_right (regValue_lt src base) (Nat.two_pow_pos shift)
  rw [←Nat.pow_add] at bound
  have power : 2^(src.length+shift)≤(2^162 : Nat) := Nat.pow_le_pow_right (by decide) hlen
  have prime : (2^162 : Nat)<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  exact lt_trans (lt_of_lt_of_le bound power) prime

theorem measured_short_view (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (src : List Wire) (negative : Bool) (shift : Nat)
    (hsrc : ∀q,src.count q≤L.core.product.count q) (hlen : src.length+shift≤162) :
    L.MeasuredFoldView base {negative:=negative,canonical:=true,src:=src,shift:=shift} :=
  ⟨hsrc,by change shift+src.length≤256;omega,fun _ => measured_short_canonical src shift base hlen⟩

theorem measured_naf_views (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (src : List Wire) (negative : Bool) (hsrc : ∀q,src.count q≤L.core.product.count q)
    (hlen : src.length+32≤162) :
    ∀f∈nafMinusOneItems negative src,L.MeasuredFoldView base f := by
  intro f hf
  simp only [nafMinusOneItems,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> apply L.measured_short_view base src _ _ hsrc <;> omega

theorem measured_rotated_count (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.rotated128.count q≤L.core.product.count q := by
  have split := congrArg (List.count q) (List.take_append_drop 128 L.core.product)
  have take := (List.take_sublist 128 (L.core.product.drop 128)).count_le q
  simp only [rotated128,List.count_append] at split ⊢
  omega

theorem measured_rotated_square_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (Y : Nat) (hP : regValue L.core.product base=Y^2) (negative : Bool) :
    L.MeasuredFoldView base {negative:=negative,canonical:=true,src:=L.rotated128} := by
  refine ⟨L.measured_rotated_count,?_,?_⟩
  · simp [rotated128,hw.core.product]
  · intro _
    have val := L.rotated128_value hw base (Y^2) hP
    have radix : (2^256 : Nat)=2^128*2^128 := by norm_num
    have div : (Y^2/2^128)%2^128=(Y^2%2^256)/2^128 := by
      rw [radix,Nat.mod_mul_right_div_self]
    rw [val,div]
    simpa only [Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_comm] using exactFold_rotate128_canonical Y

theorem measured_leaf128_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (Y : Nat) (hY : Y<2^128) (hP : regValue L.core.product base=Y^2)
    (negative : Bool) :
    L.MeasuredFoldView base {negative:=negative,canonical:=true,src:=L.core.product.take 256} := by
  refine ⟨fun q => (List.take_sublist 256 L.core.product).count_le q,by simp [hw.core.product],?_⟩
  intro _
  have square : Y^2<2^256 := by
    simpa using square_bound Y 128 hY
  rw [L.product_take_value hw base (Y^2) hP 256 (by omega),Nat.pow_zero,Nat.mul_one,Nat.mod_eq_of_lt square]
  exact exactFold_leaf128_canonical Y hY

theorem measured_shifted_product_views (L : CuccaroStreamedSquareWideLayout)
    (base : BasisState) (src : List Wire) (negative : Bool) (j : Nat)
    (hs : ∀q,src.count q≤L.core.product.count q) (hlen : src.length=256)
    (hj : j≤32) (hcanonical : regValue src base<SquareReduction.p) :
    ∀f∈shiftedProductItems negative src j,L.MeasuredFoldView base f := by
  intro f hf
  by_cases zero : j=0
  · simp [shiftedProductItems,zero] at hf
    subst f
    refine ⟨hs,by simp [hlen],?_⟩
    simpa using hcanonical
  · simp only [shiftedProductItems,zero,if_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|hf
    · refine ⟨?_,?_,by simp⟩
      · intro q
        have split := congrArg (List.count q) (List.take_append_drop (256-j) src)
        have bound := hs q
        simp only [rotateFull,List.count_append] at split ⊢
        omega
      · simp [rotateFull,hlen]
    · apply L.measured_naf_views base (src.drop (256-j)) negative
        (fun q => ((List.drop_sublist (256-j) src).count_le q).trans (hs q))
        (by simp [hlen];omega) f hf

theorem measuredA_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (Y : Nat) (hY : Y<2^128) (hP : regValue L.core.product base=Y^2) :
    ∀f∈L.measuredAItems,L.MeasuredFoldView base f := by
  intro f hf
  simp only [measuredAItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with (rfl|rfl)|hf
  · exact L.measured_leaf128_view hw base Y hY hP true
  · exact L.measured_rotated_square_view hw base Y hP false
  · exact L.measured_naf_views base (L.core.product.drop 128) false (L.productDrop_count 128)
      (by simp [hw.core.product]) f hf

theorem measuredB_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (Y : Nat) (hY : Y<2^128) (hP : regValue L.core.product base=Y^2) :
    ∀f∈L.measuredBItems,L.MeasuredFoldView base f := by
  have can : regValue (L.core.product.take 256) base<SquareReduction.p := by
    have view := L.measured_leaf128_view hw base Y hY hP true
    simpa using view.canonical rfl
  have all (negative : Bool) (j : Nat) (hj : j≤32) :
      ∀f∈shiftedProductItems negative (L.core.product.take 256) j,L.MeasuredFoldView base f :=
    L.measured_shifted_product_views base _ negative j
      (fun q => (List.take_sublist 256 L.core.product).count_le q) (by simp [hw.core.product]) hj can
  intro f hf
  simp only [measuredBItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with (((((rfl|hf)|hf)|hf)|hf)|hf)|hf
  · exact L.measured_rotated_square_view hw base Y hP false
  · exact L.measured_naf_views base (L.core.product.drop 128) false (L.productDrop_count 128)
      (by simp [hw.core.product]) f hf
  · exact all true 0 (by omega) f hf
  · exact all true 4 (by omega) f hf
  · exact all false 6 (by omega) f hf
  · exact all true 10 (by omega) f hf
  · exact all true 32 (by omega) f hf

theorem measuredC_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (Y : Nat) (hP : regValue L.core.product base=Y^2) :
    ∀f∈L.measuredCItems,L.MeasuredFoldView base f := by
  intro f hf
  simp only [measuredCItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with (rfl|hf)|rfl
  · exact L.measured_rotated_square_view hw base Y hP true
  · exact L.measured_naf_views base (L.core.product.drop 128) true (L.productDrop_count 128)
      (by simp [hw.core.product]) f hf
  · exact L.measured_short_view base (L.core.product.drop 256) true 128 (L.productDrop_count 256)
      (by simp [hw.core.product])

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
