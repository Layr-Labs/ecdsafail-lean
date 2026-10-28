import ECDSAAdd.Arithmetic.SparseSelectedAdd
import ECDSAAdd.Arithmetic.Reduction

set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- Repeated controllers are permitted. Only the target, retained overflow,
carry bank and incoming carry have a distinct-site requirement. The complete
word, phase and carry restoration hold for every measurement record. -/
theorem sparseSelectedRetainedAdd_correct (controllers xs carry : List Wire) (cin cout : Wire)
    (hn : (cout::cin::(xs++carry)).Nodup)
    (hs : ∀ q∈controllers,q∉cout::cin::(xs++carry))
    (hl : controllers.length=xs.length) (hc : carry.length=xs.length)
    (s : State) (m : List Bool) (hcout : s.basis cout=false)
    (hclean : ∀ q∈carry,s.basis q=false) :
    (run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s).phase=s.phase ∧
    regValue xs (run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s).basis=
      (regValue xs s.basis+regValue controllers s.basis+(s.basis cin).toNat)%2^xs.length ∧
    (run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s).basis cout=
      decide (2^xs.length≤regValue xs s.basis+regValue controllers s.basis+(s.basis cin).toNat) ∧
    (∀ q,q≠cout → q∉xs →
      (run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s).basis q=s.basis q) := by
  have targetND : (cin::((xs++[cout])++carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have src : ∀ q∈mappedWires (sparseSelectedBits controllers),q∉cin::((xs++[cout])++carry) := by
    intro q hq bad
    rw [sparseSelectedBits_wires] at hq
    apply hs q hq
    simp only [List.mem_cons,List.mem_append,List.mem_singleton,or_assoc] at bad ⊢
    tauto
  have input : regValue (xs++[cout]) s.basis=regValue xs s.basis := by
    simp [regValue_append,regValue,hcout]
  let S := regValue xs s.basis+regValue controllers s.basis+(s.basis cin).toNat
  have sumBound : S<2^(xs.length+1) := by
    have hx := regValue_lt xs s.basis
    have ha := regValue_lt controllers s.basis
    rw [hl] at ha
    rw [Nat.pow_succ]
    cases hi : s.basis cin <;> simp only [S,hi,Bool.toNat_false,Bool.toNat_true] <;> omega
  have h := mappedAdd_correct (sparseSelectedBits controllers) (xs++[cout]) carry cin
    targetND src (by simp [sparseSelectedBits_length,hl]) (by simp [hc]) s m hclean
  let t := run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s
  have value : regValue (xs++[cout]) t.basis=S := by
    have hv := h.2.2
    rw [sparseSelectedBits_value,input] at hv
    simp only [List.length_append,List.length_singleton] at hv
    change regValue (xs++[cout]) t.basis=
      (regValue controllers s.basis+regValue xs s.basis+(s.basis cin).toNat)%2^(xs.length+1) at hv
    have hcS : regValue controllers s.basis+regValue xs s.basis+(s.basis cin).toNat=S := by
      simp only [S,Nat.add_comm]
    rw [hcS,Nat.mod_eq_of_lt sumBound] at hv
    exact hv
  have split : regValue xs t.basis+2^xs.length*(t.basis cout).toNat=S := by
    have hv := (regValue_append xs [cout] t.basis).symm.trans value
    simpa [regValue,Bool.toNat,Bool.cond_eq_ite] using hv
  have low := regValue_lt xs t.basis
  have word : regValue xs t.basis=S%2^xs.length := by
    have eq := congrArg (fun a => a%2^xs.length) split
    simpa [Nat.add_mod,Nat.mul_mod_right,Nat.mod_eq_of_lt low] using eq
  have flag : t.basis cout=decide (2^xs.length≤S) := by
    cases ht : t.basis cout
    · simp only [ht,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at split
      have small : S<2^xs.length := split ▸ low
      simp [ht,show ¬2^xs.length≤S from by omega]
    · have large : 2^xs.length≤S := by
        simp only [ht,Bool.toNat_true,Nat.mul_one] at split
        omega
      simp [ht,large]
  refine ⟨h.1,word,flag,?_⟩
  intro q hq hx
  exact h.2.1 q (by simp only [List.mem_append,List.mem_singleton,not_or]; exact ⟨hx,hq⟩)

/-- Incoming quantum Cin, every repeated controller and every carry bit
are restored; Cout alone retains the exact unsigned overflow predicate. -/
theorem sparseSelectedRetainedAdd_full (controllers xs carry : List Wire) (cin cout : Wire)
    (hn : (cout::cin::(xs++carry)).Nodup)
    (hs : ∀ q∈controllers,q∉cout::cin::(xs++carry))
    (hl : controllers.length=xs.length) (hc : carry.length=xs.length)
    (s : State) (m : List Bool) (hcout : s.basis cout=false)
    (hclean : ∀ q∈carry,s.basis q=false) :
    (run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s).phase=s.phase ∧
    regValue xs (run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s).basis=
      (regValue xs s.basis+regValue controllers s.basis+(s.basis cin).toNat)%2^xs.length ∧
    (run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s).basis cout=
      decide (2^xs.length≤regValue xs s.basis+regValue controllers s.basis+(s.basis cin).toNat) ∧
    (run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s).basis cin=s.basis cin ∧
    (∀ q∈controllers,(run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s).basis q=s.basis q) ∧
    (∀ q∈carry,(run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s).basis q=false) ∧
    (∀ q,q≠cout → q∉xs →
      (run (sparseSelectedRetainedAdd controllers xs carry cin cout) m s).basis q=s.basis q) := by
  have h := sparseSelectedRetainedAdd_correct controllers xs carry cin cout hn hs hl hc s m hcout hclean
  have ho := List.nodup_cons.mp hn
  have hi := List.nodup_cons.mp ho.2
  have ic : cin≠cout := fun he => ho.1 (by simp [he])
  have ix : cin∉xs := fun hx => hi.1 (List.mem_append_left _ hx)
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2 cin ic ix,?_,?_,h.2.2.2⟩
  · intro q hq
    have away := hs q hq
    exact h.2.2.2 q (fun he => away (by simp [he]))
      (fun hx => away (List.mem_cons_of_mem cout (List.mem_cons_of_mem cin (List.mem_append_left _ hx))))
  · intro q hq
    have qc : q≠cout := fun he => ho.1 (List.mem_cons_of_mem cin (List.mem_append_right _ (he ▸ hq)))
    have qx : q∉xs := fun hx => List.disjoint_left.mp (List.nodup_append'.mp hi.2).2.2 hx hq
    exact (h.2.2.2 q qc qx).trans (hclean q hq)

end ECDSAAdd.Arithmetic
