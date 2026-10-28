import ECDSAAdd.Framework.RecordedPhysical
import ECDSAAdd.Arithmetic.MeasuredMaskedAdder
import ECDSAAdd.Arithmetic.SwapRegisters
import ECDSAAdd.Arithmetic.MontRotate

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

def GatePhysical (p : Program) : Prop := ∀ i ∈ p, PhysicalInstr (.gate i)

@[simp] theorem gatePhysical_append (p q : Program) :
    GatePhysical (p++q) ↔ GatePhysical p ∧ GatePhysical q := by
  simp only [GatePhysical,List.mem_append,or_imp,forall_and]

theorem copyRegister_physical (control : Option Wire) (src dst : List Wire)
    (hnd : (src++dst).Nodup) (hc : ∀ c ∈ control, c ∉ dst) :
    GatePhysical (copyRegister control src dst) := by
  induction src generalizing dst with
  | nil => simp [copyRegister,GatePhysical]
  | cons a src ih =>
    cases dst with
    | nil => simp [copyRegister,GatePhysical]
    | cons b dst =>
      have hab : a ≠ b := by
        intro e; subst b
        have h := List.nodup_iff_count.mp hnd a
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have ht : (src++dst).Nodup := by
        apply List.nodup_iff_count.mpr; intro q
        have h := List.nodup_iff_count.mp hnd q
        simp only [List.count_cons,List.count_append] at h ⊢; omega
      rw [copyRegister,gatePhysical_append]
      constructor
      · cases control with
        | none => simpa [GatePhysical,copyGate,PhysicalInstr,ProperGate] using hab
        | some c =>
          have hcb : c ≠ b := fun e => hc c rfl (by simp [e])
          simpa [GatePhysical,copyGate,PhysicalInstr,ProperGate] using And.intro hcb hab
      · exact ih dst ht (fun c hm hh => hc c hm (List.mem_cons_of_mem _ hh))

theorem majority_physical (a b cin carry : Wire) (hn : [a,b,cin,carry].Nodup) :
    GatePhysical (majority a b cin carry) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  simp_all [GatePhysical,majority,PhysicalInstr,ProperGate]

theorem eraseCarry_physical (a b cin carry : Wire) : GatePhysical (eraseCarry a b cin carry) := by
  simp [GatePhysical,eraseCarry,PhysicalInstr]

theorem eraseMask_physical (c : Wire) (src dst : List Wire) : GatePhysical (eraseMask c src dst) := by
  induction src generalizing dst with
  | nil => simp [eraseMask,GatePhysical]
  | cons a src ih =>
    cases dst with
    | nil => simp [eraseMask,GatePhysical]
    | cons b dst =>
      simpa [eraseMask,GatePhysical,PhysicalInstr] using ih dst

theorem addInPlace_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: x ++ y ++ carry).Nodup) : GatePhysical (addInPlace x y carry cin) := by
  induction x generalizing y carry cin with
  | nil => simp [addInPlace,GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases y with
      | nil => simp [addInPlace,GatePhysical]
      | cons b ys =>
        cases ys with
        | cons b' ys => simp [addInPlace,GatePhysical]
        | nil =>
          have hab : a ≠ b := by
            intro e; subst b
            have h := List.nodup_iff_count.mp hn a
            simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
            omega
          have hcb : cin ≠ b := by
            intro e; subst cin
            have h := List.nodup_iff_count.mp hn b
            simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
            omega
          simp [addInPlace,GatePhysical,PhysicalInstr,ProperGate,hab,hcb]
    | cons a' xs =>
      cases y with
      | nil => simp [addInPlace,GatePhysical]
      | cons b ys =>
        cases ys with
        | nil => simp [addInPlace,GatePhysical]
        | cons b' ys =>
          cases carry with
          | nil => simp [addInPlace,GatePhysical]
          | cons k ks =>
            have hs : [a,b,cin,k].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
            have ht : (k :: (a'::xs) ++ (b'::ys) ++ ks).Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append] at h ⊢; omega
            have htail := ih (b'::ys) ks k ht
            rw [addInPlace]
            simp only [gatePhysical_append]
            refine ⟨⟨⟨majority_physical _ _ _ _ hs,htail⟩,eraseCarry_physical _ _ _ _⟩,?_⟩
            simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
              not_or,not_false_eq_true,and_true] at hs
            have hcb : cin ≠ b := Ne.symm hs.2.1.1
            simp [GatePhysical,PhysicalInstr,ProperGate,hs.1.1,hcb]

theorem notRegister_physical (r : List Wire) : GatePhysical (notRegister r) := by
  simp [GatePhysical,notRegister,PhysicalInstr,ProperGate]

theorem subInPlace_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: x ++ y ++ carry).Nodup) : GatePhysical (subInPlace x y carry cin) := by
  simp only [subInPlace,gatePhysical_append]
  exact ⟨⟨notRegister_physical _,addInPlace_physical _ _ _ _ hn⟩,notRegister_physical _⟩

theorem swapRegisters_physical (c : Wire) (a b : List Wire)
    (hn : (c :: a ++ b).Nodup) : GatePhysical (swapRegisters c a b) := by
  have nd := List.nodup_cons.mp hn
  have ba : (b++a).Nodup := List.nodup_append_comm.mpr nd.2
  have back := copyRegister_physical none b a ba (by simp)
  have mid := copyRegister_physical (some c) a b nd.2
    (by intro q hq h; cases hq; exact nd.1 (List.mem_append_right _ h))
  simp only [swapRegisters,gatePhysical_append]
  exact ⟨⟨back,mid⟩,back⟩

theorem measuredMasked_physical (c cin : Wire) (src t y carry : List Wire)
    (hn : (c :: cin :: src ++ t ++ y ++ carry).Nodup) :
    GatePhysical (measuredMaskedAddInPlace c src t y carry cin) ∧
    GatePhysical (measuredMaskedSubInPlace c src t y carry cin) := by
  have ndcopy : (src++t).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have ndadd : (cin :: t ++ y ++ carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have ct : c ∉ t := by
    intro hh
    have h := List.nodup_iff_count.mp hn c
    have ht := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
  have cp := copyRegister_physical (some c) src t ndcopy (by intro q hq; cases hq; exact ct)
  have er := eraseMask_physical c src t
  simp only [measuredMaskedAddInPlace,measuredMaskedSubInPlace,gatePhysical_append]
  exact ⟨⟨⟨cp,addInPlace_physical _ _ _ _ ndadd⟩,er⟩,
    ⟨⟨cp,subInPlace_physical _ _ _ _ ndadd⟩,er⟩⟩

theorem xorConstant_physical (r : List Wire) (k : Nat) : GatePhysical (xorConstant r k) := by
  induction r generalizing k with
  | nil => simp [xorConstant,GatePhysical]
  | cons a r ih =>
    rw [xorConstant,gatePhysical_append]
    refine ⟨?_,ih _⟩
    split <;> simp [GatePhysical,PhysicalInstr,ProperGate]

theorem maskedConstant_physical (c : Wire) (r : List Wire) (k : Nat) (hc : c ∉ r) :
    GatePhysical (maskedConstant c r k) := by
  induction r generalizing k with
  | nil => simp [maskedConstant,GatePhysical]
  | cons a r ih =>
    have ha : c ≠ a := fun e => hc (by simp [e])
    have hr : c ∉ r := fun h => hc (List.mem_cons_of_mem _ h)
    rw [maskedConstant,gatePhysical_append]
    refine ⟨?_,ih _ hr⟩
    split <;> simp [GatePhysical,PhysicalInstr,ProperGate,ha]

theorem swapBits_physical (a b : Wire) (h : a ≠ b) : GatePhysical (swapBits a b) := by
  simp [GatePhysical,swapBits,PhysicalInstr,ProperGate,h,Ne.symm h]

theorem rotate_physical (r : List Wire) (hn : r.Nodup) :
    GatePhysical (rotateRight r) ∧ GatePhysical (rotateLeft r) := by
  induction r with
  | nil => simp [rotateRight,rotateLeft,GatePhysical]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,rotateLeft,GatePhysical]
    | cons b r =>
      have ht := ih hn.tail
      have hab : a ≠ b := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
      simp only [rotateRight,rotateLeft,gatePhysical_append]
      exact ⟨⟨swapBits_physical _ _ hab,ht.1⟩,⟨ht.2,swapBits_physical _ _ hab⟩⟩

theorem rotateBits_physical (r : List Wire) (k : Nat) (hn : r.Nodup) :
    GatePhysical (rotateRightBits r k) ∧ GatePhysical (rotateLeftBits r k) := by
  induction k with
  | zero => simp [rotateRightBits,rotateLeftBits,GatePhysical]
  | succ k ih =>
    simp only [rotateRightBits,rotateLeftBits,gatePhysical_append]
    exact ⟨⟨(rotate_physical _ hn).1,ih.1⟩,⟨(rotate_physical _ hn).2,ih.2⟩⟩

end ECDSAAdd.Arithmetic
