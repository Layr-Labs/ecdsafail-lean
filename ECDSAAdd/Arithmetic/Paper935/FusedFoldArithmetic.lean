import ECDSAAdd.Arithmetic.Paper935.FusedRowFoldSource

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Arithmetic effect on a larger register when a Cuccaro slice addition
fits its slice. The prefix and suffix are justified by the full-state frame. -/
theorem cuccaro_slice_value (pre dst post src : List Wire) (cin : Wire)
    (nd : (cin::src++dst).Nodup) (len : src.length=dst.length)
    (layout : (pre++dst++post).Nodup) (s : State) (m : List Bool)
    (carry : s.basis cin=false)
    (fits : regValue dst s.basis+regValue src s.basis<2^dst.length) :
    regValue (pre++dst++post) (run (cuccaroAdd src dst cin) m s).basis=
      regValue (pre++dst++post) s.basis+2^pre.length*regValue src s.basis := by
  have h := cuccaroAdd_cin_frame cin src dst nd len s.basis false carry
    (regValue dst s.basis) s m ⟨rfl,by intro q hq; rfl⟩
  have pv : regValue pre (run (cuccaroAdd src dst cin) m s).basis=regValue pre s.basis := by
    apply regValue_congr
    intro q hq
    apply h.2.2
    have dis := (List.nodup_append'.mp (List.nodup_append'.mp layout).1).2.2
    exact List.disjoint_left.mp dis hq
  have sv : regValue post (run (cuccaroAdd src dst cin) m s).basis=regValue post s.basis := by
    apply regValue_congr
    intro q hq
    apply h.2.2
    intro hd
    have dis := (List.nodup_append'.mp layout).2.2
    exact List.disjoint_left.mp dis (List.mem_append_right _ hd) hq
  have dv := h.2.1
  simp only [Bool.toNat_false,Nat.add_zero,Nat.mod_eq_of_lt fits] at dv
  simp only [regValue_append,List.length_append,pv,sv,dv]
  ring

end ECDSAAdd.Arithmetic.Paper935
