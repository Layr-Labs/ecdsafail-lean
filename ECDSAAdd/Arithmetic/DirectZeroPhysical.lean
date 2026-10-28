import ECDSAAdd.Arithmetic.DirectZeroControlled
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem zeroSeeded_physical (xs carry : List Wire) (cin target : Wire)
    (hn : (target::cin::(xs++carry)).Nodup) :
    GatePhysical (ZeroSeededConstantCompare.program xs carry cin target) := by
  cases xs with
  | nil => simp [ZeroSeededConstantCompare.program,GatePhysical]
  | cons x xs =>
    cases xs with
    | nil =>
      have ht : x ≠ target := by
        intro eq; subst target
        have h := List.nodup_iff_count.mp hn x
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      simp [ZeroSeededConstantCompare.program,ZeroSeededConstantCompare.prepare,GatePhysical,PhysicalInstr,ProperGate,ht]
    | cons y xs =>
      cases carry with
      | nil => simp [ZeroSeededConstantCompare.program,GatePhysical]
      | cons c cs =>
        have xc : x ≠ c := by
          intro eq; subst c
          have h := List.nodup_iff_count.mp hn x
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have nd : ([c,target]++(y::xs)++cs).Nodup := by
          apply List.nodup_iff_count.mpr
          intro w
          have h := List.nodup_iff_count.mp hn w
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have pre : GatePhysical (ZeroSeededConstantCompare.prepare x c) := by
          simp [ZeroSeededConstantCompare.prepare,GatePhysical,PhysicalInstr,ProperGate,xc]
        have post : GatePhysical (ZeroSeededConstantCompare.release x c) := by
          simp [ZeroSeededConstantCompare.release,GatePhysical,PhysicalInstr,ProperGate,xc]
        simp only [ZeroSeededConstantCompare.program,gatePhysical_append]
        exact ⟨⟨pre,compareConstantLt_physical _ _ _ _ _ nd⟩,post⟩

theorem directZero_physical (xs carry : List Wire) (cin flag : Wire) (kernel : Program)
    (hn : (flag::cin::(xs++carry)).Nodup) (hk : GatePhysical kernel) :
    GatePhysical (directZeroControlled xs carry cin flag kernel) := by
  have hz := zeroSeeded_physical xs carry cin flag hn
  have away : flag ∉ xs := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hm := maskedConstant_physical flag xs 1 away
  simp only [directZeroControlled,directZeroDivisorEnter,directZeroDivisorLeave,gatePhysical_append]
  exact ⟨⟨hz,hm⟩,hk,hm,hz⟩
end ECDSAAdd.Arithmetic
