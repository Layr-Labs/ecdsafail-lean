import ECDSAAdd.Arithmetic.CompressedCodecRebind
import Mathlib.Tactic

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedAllocation

def W (j : Nat) : Nat := 515+j
def H (j : Nat) : Nat := 1028+3*j+1
def spare : Nat := 684
def workRegion (q : Nat) : Prop := 515 ≤ q ∧ q ≤ 684
def holeRegion (q : Nat) : Prop := 1029 ≤ q ∧ q ≤ 1536 ∧ q%3=0
def zeroRegion (q : Nat) : Prop := workRegion q ∨ holeRegion q
def omitted (q : Nat) : Prop := 515 ≤ q ∧ q < 684

instance workRegion_decidable (q : Nat) : Decidable (workRegion q) := by
  unfold workRegion
  infer_instance

instance holeRegion_decidable (q : Nat) : Decidable (holeRegion q) := by
  unfold holeRegion
  infer_instance

private def baseFn (q : Nat) : Nat :=
  if workRegion q then H (q-515)
  else if holeRegion q then W ((q-1029)/3) else q

private theorem base_W (j : Nat) (hj : j < 170) : baseFn (W j)=H j := by
  have h : workRegion (W j) := by unfold workRegion W; omega
  simp only [baseFn,if_pos h]
  unfold W H
  omega

private theorem base_H (j : Nat) (hj : j < 170) : baseFn (H j)=W j := by
  have nw : ¬workRegion (H j) := by unfold workRegion H; omega
  have hh : holeRegion (H j) := by unfold holeRegion H; omega
  simp only [baseFn,if_neg nw,if_pos hh]
  unfold W H
  omega

private theorem base_involutive : Function.Involutive baseFn := by
  intro q
  by_cases hw : workRegion q
  · have hj : q-515 < 170 := by unfold workRegion at hw; omega
    have eq : q=W (q-515) := by unfold workRegion at hw; unfold W; omega
    rw [eq,base_W _ hj,base_H _ hj]
  · by_cases hh : holeRegion q
    · have hj : (q-1029)/3 < 170 := by unfold holeRegion at hh; omega
      have eq : q=H ((q-1029)/3) := by unfold holeRegion at hh; unfold H; omega
      rw [eq,base_H _ hj,base_W _ hj]
    · simp only [baseFn,if_neg hw,if_neg hh]

/-- Swap all170 disjoint work/codec-zero pairs. This is a total public
permutation, rather than a noninjective alias of old logical wires. -/
def pi0 : Equiv.Perm Nat :=
  { toFun:=baseFn,invFun:=baseFn,left_inv:=base_involutive,right_inv:=base_involutive }

theorem pi0_W (j : Nat) (hj : j < 170) : pi0 (W j)=H j := base_W j hj
theorem pi0_H (j : Nat) (hj : j < 170) : pi0 (H j)=W j := base_H j hj

theorem pi0_outside (q : Nat) (hq : ¬zeroRegion q) : pi0 q=q := by
  have hw : ¬workRegion q := fun h => hq (Or.inl h)
  have hh : ¬holeRegion q := fun h => hq (Or.inr h)
  change baseFn q=q
  simp only [baseFn,if_neg hw,if_neg hh]

private theorem swap_left (a b : Nat) : Equiv.swap a b a=b := by
  simp

private theorem swap_right (a b : Nat) : Equiv.swap a b b=a := by
  simp

private theorem swap_outside (a b q : Nat) (ha : q ≠ a) (hb : q ≠ b) :
    Equiv.swap a b q=q := by simp [Equiv.swap_apply_def,ha,hb]

/-- Restore the active raw codec slot while assigning its work role to
the common spare. The remaining role exchange is an injective3-cycle. -/
def pi (j : Nat) : Equiv.Perm Nat :=
  (Equiv.swap (W j) (H j)).trans ((Equiv.swap (H j) (H 169)).trans pi0)

theorem pi_apply (j q : Nat) :
    pi j q=pi0 (Equiv.swap (H j) (H 169) (Equiv.swap (W j) (H j) q)) := rfl

theorem pi_selected (j : Nat) (_hj : j < 170) : pi j (W j)=spare := by
  rw [pi_apply,swap_left,swap_left,pi0_H 169 (by omega)]
  rfl

theorem pi_current (j : Nat) (hj : j < 170) : pi j (H j)=H j := by
  have a : W j ≠ H j := by unfold W H; omega
  have b : W j ≠ H 169 := by unfold W H; omega
  rw [pi_apply,swap_right,swap_outside _ _ _ a b,pi0_W j hj]

theorem pi_other (j k : Nat) (hj : j < 170) (hk : k < 170) (hne : k ≠ j) :
    pi j (W k)=H k := by
  have a : W k ≠ W j := by unfold W; omega
  have b : W k ≠ H j := by unfold W H; omega
  have c : W k ≠ H 169 := by unfold W H; omega
  rw [pi_apply,swap_outside _ _ _ a b,swap_outside _ _ _ b c,pi0_W k hk]

theorem pi_outside (j q : Nat) (hj : j < 170) (hq : ¬zeroRegion q) : pi j q=q := by
  have nw : q ≠ W j := by intro e; subst q; apply hq; left; unfold workRegion W; omega
  have nh : q ≠ H j := by intro e; subst q; apply hq; right; unfold holeRegion H; omega
  have ns : q ≠ H 169 := by intro e; subst q; apply hq; right; unfold holeRegion H; omega
  rw [pi_apply,swap_outside _ _ _ nw nh,swap_outside _ _ _ nh ns,pi0_outside q hq]

theorem pi0_injective : Function.Injective pi0 := pi0.injective
theorem pi_injective (j : Nat) : Function.Injective (pi j) := (pi j).injective

theorem pi_selected_not_omitted (j : Nat) (hj : j < 170) : ¬omitted (pi j (W j)) := by
  rw [pi_selected j hj]
  unfold omitted spare
  omega

theorem pi_other_not_omitted (j k : Nat) (hj : j < 170) (hk : k < 170) (hne : k ≠ j) :
    ¬omitted (pi j (W k)) := by
  rw [pi_other j k hj hk hne]
  unfold omitted H
  omega

end ECDSAAdd.Arithmetic.CompressedAllocation
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.pi0_injective
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.pi_selected
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.pi_current
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.pi_other
