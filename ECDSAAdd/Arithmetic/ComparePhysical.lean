import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.Compare

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem flipBelow_physical (control : Option Wire) (top t : Wire)
    (ht : top ≠ t) (hc : ∀ c ∈ control, c ≠ t) : GatePhysical (flipBelow control top t) := by
  cases control with
  | none => simp [flipBelow,GatePhysical,PhysicalInstr,ProperGate,ht]
  | some c => simp [flipBelow,GatePhysical,PhysicalInstr,ProperGate,ht,hc c rfl]

theorem compareChain_physical (control : Option Wire) (x y carry : List Wire) (cin t : Wire)
    (hn : (t :: cin :: x ++ y ++ carry).Nodup)
    (hc : ∀ c ∈ control, c ≠ t) : GatePhysical (compareChain control x y carry cin t) := by
  induction x generalizing y carry cin with
  | nil =>
    cases y with
    | cons b ys => simp [compareChain,GatePhysical]
    | nil =>
      cases carry with
      | cons k ks => simp [compareChain,GatePhysical]
      | nil =>
        apply flipBelow_physical control cin t _ hc
        have ht : t ≠ cin := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
        exact Ne.symm ht
  | cons a xs ih =>
    cases y with
    | nil => simp [compareChain,GatePhysical]
    | cons b ys =>
      cases carry with
      | nil => simp [compareChain,GatePhysical]
      | cons k ks =>
        have hs : [a,b,cin,k].Nodup := by
          apply List.nodup_iff_count.mpr; intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
        have ht : (t :: k :: xs ++ ys ++ ks).Nodup := by
          apply List.nodup_iff_count.mpr; intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append] at h ⊢; omega
        simp only [compareChain,gatePhysical_append]
        exact ⟨⟨majority_physical _ _ _ _ hs,ih ys ks k ht⟩,eraseCarry_physical _ _ _ _⟩

theorem compareLt_physical (control : Option Wire) (x y carry : List Wire) (cin t : Wire)
    (hn : (t :: cin :: x ++ y ++ carry).Nodup)
    (hc : ∀ c ∈ control, c ≠ t) : GatePhysical (compareLt control x y carry cin t) := by
  simp only [compareLt,gatePhysical_append]
  exact ⟨⟨notRegister_physical _,compareChain_physical _ _ _ _ _ _ hn hc⟩,notRegister_physical _⟩

theorem maskedAddConst_physical (c : Wire) (T y carry : List Wire) (cin K : Nat)
    (hn : (cin :: T ++ y ++ carry).Nodup) (hc : c ∉ T) :
    GatePhysical (maskedAddConst c T y carry cin K) := by
  simp only [maskedAddConst,gatePhysical_append]
  exact ⟨⟨maskedConstant_physical _ _ _ hc,addInPlace_physical _ _ _ _ hn⟩,
    maskedConstant_physical _ _ _ hc⟩

end ECDSAAdd.Arithmetic
