import ECDSAAdd.Arithmetic.RecordedRailVentedProof

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailVented
open RecordedRailRipple

def Ready (a b : List Wire) (prev : Option Wire) (work : List Wire)
    (cout : Wire) (bits : BasisState) : Prop :=
  Aligned a b work ∧ (prev.toList++a++b++work++[cout]).Nodup ∧
    (∀q∈work,bits q=false) ∧ bits cout=false

/-- Exact arithmetic and complete restoration, including the real carry-out
quotient. This is the proof target, never a semantic assumption. -/
def Result (a b work : List Wire) (prev : Option Wire) (cout : Wire)
    (bits : BasisState) (phase : Bool) (out : State) : Prop :=
  let total := regValue a bits+regValue b bits+(incomingValue prev bits).toNat
  out.phase=phase ∧ regValue a out.basis=regValue a bits ∧
    regValue (b++[cout]) out.basis=total ∧
    regValue b out.basis=total%2^b.length ∧
    (out.basis cout).toNat=total/2^b.length ∧
    incomingValue prev out.basis=incomingValue prev bits ∧
    (∀q,q∉b++[cout] → out.basis q=bits q) ∧
    (∀q∈work,out.basis q=false)

def UnsignedContract (a b : List Wire) (prev : Option Wire) (work : List Wire)
    (cout : Wire) : Prop :=
  ∀(bits : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat),
    Ready a b prev work cout bits →
    Result a b work prev cout bits phase
      (runWithTape (vented a b prev work cout) m cursor ⟨phase,bits⟩)

/-- Literal port uniqueness separates all preserved ports from the wide output. -/
theorem ports_disjoint (a b work : List Wire) (prev : Option Wire) (cout : Wire)
    (nd : (prev.toList++a++b++work++[cout]).Nodup) :
    (prev.toList++a++work).Disjoint (b++[cout]) := by
  have rearranged : ((prev.toList++a++work)++(b++[cout])).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  exact (List.nodup_append'.mp rearranged).2.2

theorem correct_of_shape (a b work : List Wire) (shape : Shape a b work)
    (prev : Option Wire) (cout : Wire) (bits : BasisState) (phase : Bool)
    (m : List Bool) (cursor : Nat) (ready : Ready a b prev work cout bits) :
    Result a b work prev cout bits phase
      (runWithTape (vented a b prev work cout) m cursor ⟨phase,bits⟩) := by
  obtain ⟨_,nd,clean,coutClean⟩ := ready
  let out := runWithTape (vented a b prev work cout) m cursor ⟨phase,bits⟩
  obtain ⟨hp,hs,hout⟩ := vented_frame a b work shape prev cout bits phase m cursor nd clean coutClean
  have dis := ports_disjoint a b work prev cout nd
  have outside : ∀q∈prev.toList++a++work,q∉b++[cout] := by
    intro q hq htarget
    exact List.disjoint_left.mp dis hq htarget
  change out.phase=phase ∧ regValue a out.basis=regValue a bits ∧
    regValue (b++[cout]) out.basis=regValue a bits+regValue b bits+(incomingValue prev bits).toNat ∧
    regValue b out.basis=(regValue a bits+regValue b bits+(incomingValue prev bits).toNat)%2^b.length ∧
    (out.basis cout).toNat=(regValue a bits+regValue b bits+(incomingValue prev bits).toNat)/2^b.length ∧
    incomingValue prev out.basis=incomingValue prev bits ∧
    (∀q,q∉b++[cout] → out.basis q=bits q) ∧ (∀q∈work,out.basis q=false)
  refine ⟨hp,?_,hs,?_,?_,?_,hout,?_⟩
  · apply regValue_congr
    intro q hq
    exact hout q (outside q (by simp [hq]))
  · rw [←hs]
    exact regValue_low b cout out.basis
  · rw [←hs,regValue_append,Nat.add_mul_div_left _ _ (Nat.two_pow_pos b.length),
      Nat.div_eq_of_lt (regValue_lt b out.basis),Nat.zero_add]
    cases hc : out.basis cout <;> simp [regValue,hc]
    all_goals simpa only [out] using hc
  · cases prev with
    | none => rfl
    | some p => exact hout p (outside p (by simp))
  · intro q hq
    rw [hout q (outside q (by simp [hq]))]
    exact clean q hq

/-- Every aligned literal vented call satisfies the full contract. -/
theorem correct (a b : List Wire) (prev : Option Wire) (work : List Wire) (cout : Wire) :
    UnsignedContract a b prev work cout := by
  intro bits phase m cursor ready
  exact correct_of_shape a b work (aligned_shape a b work ready.1)
    prev cout bits phase m cursor ready

/-- The exact wide sum also provides the requested modulo-width interface. -/
theorem wide_mod (a b : List Wire) (prev : Option Wire) (work : List Wire) (cout : Wire)
    (bits : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat)
    (ready : Ready a b prev work cout bits) :
    regValue (b++[cout]) (runWithTape (vented a b prev work cout) m cursor ⟨phase,bits⟩).basis=
      (regValue a bits+regValue b bits+(incomingValue prev bits).toNat)%2^(b.length+1) := by
  have h := correct a b prev work cout bits phase m cursor ready
  have hs := h.2.2.1
  rw [←hs]
  apply (Nat.mod_eq_of_lt ?_).symm
  simpa only [List.length_append,List.length_singleton] using
    regValue_lt (b++[cout]) (runWithTape (vented a b prev work cout) m cursor ⟨phase,bits⟩).basis

/-- Static sites count only the literal real ports, including the retained cout. -/
theorem site_bound (a b work : List Wire) (shape : Shape a b work)
    (prev : Option Wire) (cout : Wire) :
    (recordedWires (vented a b prev work cout)).card ≤ 3*a.length+prev.toList.length := by
  have h := Finset.card_le_card (support a b work shape prev cout)
  have bound := List.toFinset_card_le (prev.toList++a++b++work++[cout])
  have lengths := shape_lengths a b work shape
  simp only [sites] at h
  simp only [List.length_append,List.length_singleton] at bound
  simp only [Aligned] at lengths
  omega

theorem ghost_excluded (a b work : List Wire) (shape : Shape a b work)
    (prev : Option Wire) (cout q : Wire) (hq : q∉sites a b work prev cout) :
    q∉recordedWires (vented a b prev work cout) := fun h => hq (support a b work shape prev cout h)

end ECDSAAdd.Arithmetic.RecordedRailVented
#print axioms ECDSAAdd.Arithmetic.RecordedRailVented.correct
#print axioms ECDSAAdd.Arithmetic.RecordedRailVented.wide_mod
#print axioms ECDSAAdd.Arithmetic.RecordedRailVented.site_bound
