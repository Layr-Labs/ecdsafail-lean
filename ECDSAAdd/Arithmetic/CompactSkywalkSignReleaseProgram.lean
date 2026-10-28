import ECDSAAdd.Arithmetic.NarrowSignedRecord
import ECDSAAdd.Arithmetic.SignedWordBits

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- The retained sign belongs to the physical prefix. Released high sites
are distinct from every retained site and may subsequently be loaned. -/
structure CompactSkywalkSignReleaseLayout where
  low : List Wire
  sign : Wire
  released : List Wire

namespace CompactSkywalkSignReleaseLayout

def retained (L : CompactSkywalkSignReleaseLayout) : List Wire := L.low++[L.sign]
def expanded (L : CompactSkywalkSignReleaseLayout) : List Wire := L.retained++L.released
def Valid (L : CompactSkywalkSignReleaseLayout) : Prop := L.expanded.Nodup
def Copies (L : CompactSkywalkSignReleaseLayout) (s : BasisState) : Prop :=
  ∀q ∈ L.released,s q = s L.sign
def Clean (L : CompactSkywalkSignReleaseLayout) (s : BasisState) : Prop :=
  ∀q ∈ L.released,s q = false

def cleared (L : CompactSkywalkSignReleaseLayout) (s : BasisState) : BasisState :=
  fun q => if q ∈ L.released then false else s q
/-- Virtual sign-extension interface while high sites are physically clean. -/
def reconstructed (L : CompactSkywalkSignReleaseLayout) (s : BasisState) : BasisState :=
  fun q => if q ∈ L.released then s L.sign else s q

theorem releasedND (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid) : L.released.Nodup :=
  (List.nodup_append'.mp hv).2.1

theorem signAway (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid) : L.sign ∉ L.released := by
  have h := (List.nodup_append'.mp hv).2.2
  exact List.disjoint_left.mp h (by simp [retained])

theorem retainedAway (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (q : Wire) (hq : q ∈ L.retained) : q ∉ L.released :=
  List.disjoint_left.mp (List.nodup_append'.mp hv).2.2 hq

end CompactSkywalkSignReleaseLayout

/-- One emitted CX per redundant sign copy; there are no carry instructions. -/
def compactSkywalkSignRelease (L : CompactSkywalkSignReleaseLayout) : Program :=
  signComplement L.sign L.released
/-- The same independently emitted Clifford fanout reconstructs clean high sites. -/
def compactSkywalkSignExpand (L : CompactSkywalkSignReleaseLayout) : Program :=
  signComplement L.sign L.released

theorem compactSkywalkSignRelease_run (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) :
    run (compactSkywalkSignRelease L) m s = 
      ⟨s.phase,fun q => if q ∈ L.released then s.basis q ^^ s.basis L.sign else s.basis q⟩ :=
  narrow_fanout_correct L.sign L.released (L.releasedND hv) (L.signAway hv) s m

theorem compactSkywalkSignRelease_correct (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (hc : L.Copies s.basis) :
    run (compactSkywalkSignRelease L) m s = ⟨s.phase,L.cleared s.basis⟩ := by
  rw [compactSkywalkSignRelease_run L hv s m]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q ∈ L.released
  · simp only [CompactSkywalkSignReleaseLayout.cleared,if_pos hq,hc q hq]
    cases s.basis L.sign <;> rfl
  · simp [CompactSkywalkSignReleaseLayout.cleared,hq]

theorem compactSkywalkSignExpand_correct (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (hc : L.Clean s.basis) :
    run (compactSkywalkSignExpand L) m s = ⟨s.phase,L.reconstructed s.basis⟩ := by
  have h := compactSkywalkSignRelease_run L hv s m
  change run (compactSkywalkSignExpand L) m s = _ at h
  rw [h]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q ∈ L.released
  · simp only [CompactSkywalkSignReleaseLayout.reconstructed,if_pos hq,hc q hq]
    cases s.basis L.sign <;> rfl
  · simp [CompactSkywalkSignReleaseLayout.reconstructed,hq]

/-- Arbitrary incoming phase and arbitrary record lists are preserved. -/
theorem compactSkywalkSignRelease_phase_frame (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) :
    (run (compactSkywalkSignRelease L) m s).phase = s.phase ∧
    (∀q,q ∉ L.released → (run (compactSkywalkSignRelease L) m s).basis q = s.basis q) ∧
    (run (compactSkywalkSignExpand L) m s).phase = s.phase ∧
    (∀q,q ∉ L.released → (run (compactSkywalkSignExpand L) m s).basis q = s.basis q) := by
  have h := signComplement_correct L.sign L.released (L.releasedND hv) (L.signAway hv) s m
  exact ⟨h.1,h.2.1,h.1,h.2.1⟩

theorem compactSkywalkSignRelease_clean (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (hc : L.Copies s.basis) :
    L.Clean (run (compactSkywalkSignRelease L) m s).basis := by
  rw [compactSkywalkSignRelease_correct L hv s m hc]
  intro q hq
  simp [CompactSkywalkSignReleaseLayout.cleared,hq]

theorem compactSkywalkSignExpand_copies (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (hc : L.Clean s.basis) :
    L.Copies (run (compactSkywalkSignExpand L) m s).basis := by
  rw [compactSkywalkSignExpand_correct L hv s m hc]
  intro q hq
  simp [CompactSkywalkSignReleaseLayout.reconstructed,hq,L.signAway hv]

/-- Both physical direction orders are exact State inverses, even before
restricting to the sign-copy/clean-bank boundary predicates. -/
theorem compactSkywalkSignRelease_roundtrip (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m1 m2 : List Bool) :
    run (compactSkywalkSignExpand L) m2 (run (compactSkywalkSignRelease L) m1 s) = s ∧
    run (compactSkywalkSignRelease L) m2 (run (compactSkywalkSignExpand L) m1 s) = s := by
  have h := narrow_fanout_twice L.sign L.released (L.releasedND hv) (L.signAway hv) s m1 m2
  exact ⟨h,h⟩

theorem compactSkywalkSignRelease_counts (L : CompactSkywalkSignReleaseLayout) :
    toffoliCount (compactSkywalkSignRelease L) = 0 ∧ measurementCount (compactSkywalkSignRelease L) = 0 ∧
    toffoliCount (compactSkywalkSignExpand L) = 0 ∧ measurementCount (compactSkywalkSignExpand L) = 0 := by
  have h := signComplement_counts L.sign L.released
  exact ⟨h.1,h.2,h.1,h.2⟩

theorem compactSkywalkSignRelease_support (L : CompactSkywalkSignReleaseLayout) :
    wires (compactSkywalkSignRelease L) ⊆ (L.sign::L.released).toFinset ∧
    wires (compactSkywalkSignExpand L) ⊆ (L.sign::L.released).toFinset := by
  have h := signComplement_wires_subset L.sign L.released
  exact ⟨h,h⟩

theorem compactSkywalkSignRelease_length (L : CompactSkywalkSignReleaseLayout) :
    (compactSkywalkSignRelease L).length = L.released.length ∧
    (compactSkywalkSignExpand L).length = L.released.length := by
  simp [compactSkywalkSignRelease,compactSkywalkSignExpand,signComplement]

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignRelease_correct
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignRelease_roundtrip
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignRelease_counts
