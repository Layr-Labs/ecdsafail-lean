import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.SignedTriangularSquare

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem xorWhenFalse_physical (c : Wire) (ys : List Wire) (hc : c ∉ ys) :
    GatePhysical (xorWhenFalse c ys) := by
  induction ys with
  | nil => simp [xorWhenFalse,GatePhysical]
  | cons y ys ih =>
    simp only [List.mem_cons,not_or] at hc
    simp only [xorWhenFalse,gatePhysical_append]
    exact ⟨by simpa [GatePhysical,PhysicalInstr,ProperGate] using hc.1,ih hc.2⟩

theorem signedSquareRow_physical (c : Wire) (xs dst pad carry : List Wire)
    (hn : (c :: xs ++ dst ++ pad ++ carry).Nodup) :
    GatePhysical (signedSquareRow c xs dst pad carry) ∧
    GatePhysical (signedSquareRowClear c xs dst pad carry) := by
  have hc : c ∉ dst := by
    intro hh; exact (List.nodup_cons.mp hn).1 (by simp [hh])
  have ht : c ∉ dst.take xs.length := fun hh => hc (List.mem_of_mem_take hh)
  have nd : (c :: (xs ++ pad.take 1) ++ dst ++ carry.take xs.length).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    have hp := (List.take_sublist 1 pad).count_le q
    have hk := (List.take_sublist xs.length carry).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  simp only [signedSquareRow,signedSquareRowClear,gatePhysical_append]
  exact ⟨⟨⟨xorWhenFalse_physical _ _ ht,addInPlace_physical _ _ _ _ nd⟩,
    xorWhenFalse_physical _ _ hc⟩,
    xorWhenFalse_physical _ _ hc,notRegister_physical _,addInPlace_physical _ _ _ _ nd,
    notRegister_physical _,xorWhenFalse_physical _ _ ht⟩

theorem signedSquareRows_physical (xs dst pad carry : List Wire)
    (hn : (xs ++ dst ++ pad ++ carry).Nodup) :
    GatePhysical (signedSquareRows xs dst pad carry) ∧
    GatePhysical (signedSquareRowsClear xs dst pad carry) := by
  induction xs generalizing dst with
  | nil => simp [signedSquareRows,signedSquareRowsClear,GatePhysical]
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedSquareRows,signedSquareRowsClear,GatePhysical]
    | cons d xs =>
      have nr : (c :: (d::xs) ++ (dst.drop 1).take ((d::xs).length+1) ++ pad ++ carry).Nodup := by
        apply List.nodup_iff_count.mpr; intro q
        have h := List.nodup_iff_count.mp hn q
        have hd := (List.drop_sublist 1 dst).count_le q
        have ht := (List.take_sublist ((d::xs).length+1) (dst.drop 1)).count_le q
        simp only [List.count_cons,List.count_append] at h ⊢; omega
      have nt : ((d::xs) ++ dst.drop 2 ++ pad ++ carry).Nodup := by
        apply List.nodup_iff_count.mpr; intro q
        have h := List.nodup_iff_count.mp hn q
        have hd := (List.drop_sublist 2 dst).count_le q
        simp only [List.count_cons,List.count_append] at h ⊢; omega
      have row := signedSquareRow_physical _ _ _ _ _ nr
      have tail := ih _ nt
      simp only [signedSquareRows,signedSquareRowsClear,gatePhysical_append]
      exact ⟨⟨row.1,tail.1⟩,tail.2,row.2⟩

theorem signedSquareTop_physical (xs dst : List Wire) (hn : (xs ++ dst).Nodup) :
    GatePhysical (signedSquareTop xs dst) := by
  induction xs generalizing dst with
  | nil => simp [signedSquareTop,GatePhysical]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp [signedSquareTop,GatePhysical]
      | cons d dst =>
        cases dst with
        | nil => simp [signedSquareTop,GatePhysical]
        | cons z dst =>
          have hx : x ≠ z := by
            intro he; subst x
            have h := List.nodup_iff_count.mp hn z
            simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,ite_true] at h
            omega
          simpa [signedSquareTop,GatePhysical,PhysicalInstr,ProperGate] using hx
    | cons x' xs =>
      cases dst with
      | nil => simp [signedSquareTop,GatePhysical]
      | cons d dst =>
        cases dst with
        | nil => simp [signedSquareTop,GatePhysical]
        | cons z dst =>
          apply ih
          apply List.nodup_iff_count.mpr; intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append] at h ⊢; omega

end ECDSAAdd.Arithmetic
