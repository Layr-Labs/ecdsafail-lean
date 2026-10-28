import ECDSAAdd.Arithmetic.SquareFold
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem shiftedSource_count_le (src pad : List Wire) (j width : Nat) (w : Wire) :
    (shiftedSource src pad j width).count w ≤ src.count w + pad.count w := by
  have h := (List.take_sublist (width-j-src.length) (pad.drop j)).count_le w
  have he := congrArg (List.count w) (List.take_append_drop j pad)
  simp only [List.count_append] at he
  simp only [shiftedSource,List.count_append]
  omega

theorem squareFolds_physical (src dst pad carry : List Wire) (cin : Wire)
    (js : List Nat) (hn : (cin::(src++dst++pad++carry)).Nodup) :
    GatePhysical (squareFoldAdd src dst pad carry cin js) ∧
    GatePhysical (squareFoldClear src dst pad carry cin js) := by
  induction js with
  | nil => simp [squareFoldAdd,squareFoldClear,GatePhysical]
  | cons j js ih =>
    have nd : (cin::(shiftedSource src pad j dst.length++dst++carry.take (dst.length-1))).Nodup := by
      apply List.nodup_iff_count.mpr
      intro w
      have h := List.nodup_iff_count.mp hn w
      have hs := shiftedSource_count_le src pad j dst.length w
      have hc := (List.take_sublist (dst.length-1) carry).count_le w
      simp only [List.count_cons,List.count_append] at h ⊢
      omega
    have ha := addInPlace_physical _ _ _ _ nd
    have hs := subInPlace_physical _ _ _ _ nd
    simp only [squareFoldAdd,squareFoldClear,gatePhysical_append]
    exact ⟨⟨ha,ih.1⟩,⟨ih.2,hs⟩⟩

end ECDSAAdd.Arithmetic
