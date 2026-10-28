import ECDSAAdd.Arithmetic.BalancedFieldConvertProgram
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.LiteralConstAdd
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem literalCells_physical (bit : Bool) (x cin cout one : Wire)
    (hn : [x,cin,cout].Nodup) :
    GatePhysical (literalConstStep bit x cin cout) ∧
    GatePhysical (literalConstErase bit x cin cout one) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  cases bit <;> simp_all [literalConstStep,literalConstSum,literalConstCarry,
    literalConstErase,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

theorem literalAdd_physical (xs carry : List Wire) (cin one k : Nat)
    (hn : (cin::xs++carry).Nodup) : GatePhysical (literalConstAdd xs carry cin one k) := by
  induction xs generalizing carry cin k with
  | nil => simp [literalConstAdd,GatePhysical]
  | cons x xs ih =>
    cases xs with
    | nil =>
      have ne : cin≠x := fun he => (List.nodup_cons.mp hn).1 (by simp [he])
      simp only [literalConstAdd]
      unfold literalConstSum
      split <;> simp [GatePhysical,PhysicalInstr,ProperGate,ne]
    | cons y ys =>
      cases carry with
      | nil => simp [literalConstAdd,GatePhysical]
      | cons c cs =>
        have small : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr; intro w
          have h := List.nodup_iff_count.mp hn w
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
        have tail : (c::(y::ys)++cs).Nodup := by
          apply List.nodup_iff_count.mpr; intro w
          have h := List.nodup_iff_count.mp hn w
          simp only [List.count_cons,List.count_append] at h ⊢; omega
        have cells := literalCells_physical (decide (k%2=1)) x cin c one small
        have recs := ih cs c (k/2) tail
        simp only [literalConstAdd,gatePhysical_append]
        exact ⟨⟨cells.1,recs⟩,cells.2⟩

end ECDSAAdd.Arithmetic
