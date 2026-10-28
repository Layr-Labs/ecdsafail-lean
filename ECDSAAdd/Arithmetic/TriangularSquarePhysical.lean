import ECDSAAdd.Arithmetic.TriangularSquare
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem squareRow_physical (sub : Bool) (c : Wire) (xs pad mask dst carry : List Wire) (cin : Wire)
    (hn : (c::cin::(xs++pad++mask++dst++carry)).Nodup) :
    GatePhysical (squareRow sub c xs pad mask dst carry cin) := by
  have nd : (c::cin::((xs++pad.take xs.length)++mask.take (2*xs.length)++dst++carry.take (2*xs.length-1))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have hp := (List.take_sublist xs.length pad).count_le w
    have hm := (List.take_sublist (2*xs.length) mask).count_le w
    have hc := (List.take_sublist (2*xs.length-1) carry).count_le w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have h := measuredMasked_physical c cin _ _ _ _ nd
  cases sub
  · exact h.1
  · exact h.2

theorem triangularSquares_physical (xs dst pad mask carry : List Wire) (cin : Wire)
    (hn : (cin::(xs++dst++pad++mask++carry)).Nodup) :
    GatePhysical (triangularSquare xs dst pad mask carry cin) ∧
    GatePhysical (triangularSquareClear xs dst pad mask carry cin) := by
  induction xs generalizing dst with
  | nil => simp [triangularSquare,triangularSquareClear,GatePhysical]
  | cons c xs ih =>
    cases dst with
    | nil => simp [triangularSquare,triangularSquareClear,GatePhysical]
    | cons a dst =>
      cases dst with
      | nil => simp [triangularSquare,triangularSquareClear,GatePhysical]
      | cons b dst =>
        have nd : (cin::(xs++dst++pad++mask++carry)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro w
          have h := List.nodup_iff_count.mp hn w
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        have nr : (c::cin::(xs++pad++mask++dst++carry)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro w
          have h := List.nodup_iff_count.mp hn w
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        have ca : c ≠ a := by
          intro eq
          subst a
          have h := List.nodup_iff_count.mp hn c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have gate : GatePhysical [.CX c a] := by simp [GatePhysical,PhysicalInstr,ProperGate,ca]
        have hp : GatePhysical (if xs=[] then [] else squareRow false c xs pad mask dst carry cin) := by
          split
          · simp [GatePhysical]
          · exact squareRow_physical _ _ _ _ _ _ _ _ nr
        have hm : GatePhysical (if xs=[] then [] else squareRow true c xs pad mask dst carry cin) := by
          split
          · simp [GatePhysical]
          · exact squareRow_physical _ _ _ _ _ _ _ _ nr
        have ht := ih dst nd
        simp only [triangularSquare,triangularSquareClear,gatePhysical_append]
        exact ⟨⟨⟨ht.1,hp⟩,gate⟩,⟨⟨gate,hm⟩,ht.2⟩⟩

end ECDSAAdd.Arithmetic
