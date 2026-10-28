import ECDSAAdd.Arithmetic.CompressedAllocationSupport
import ECDSAAdd.Arithmetic.CompressedCompactReverseProgram

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation

def indices : List Nat := List.range' 0 515++List.range' 684 1114++
  List.range' 2056 258++List.range' 2400 12
def slots : List Wire := indices.map (fun q => q+16)
def live (q : Nat) : Prop := q < 1798 ∨ (2056 ≤ q ∧ q < 2314) ∨ (2400 ≤ q ∧ q < 2412)
def base (q : Nat) : Wire := q+16
def placed (j q : Nat) : Wire := pi j q+16
def allPlaced (q : Nat) : Wire := pi0 q+16

theorem base_injective : Function.Injective base := by
  intro a b h
  change a+16=b+16 at h
  exact Nat.add_right_cancel h
theorem base_pool_nodup : (skywalkPoolWires base).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ h; exact base_injective h
  · exact List.nodup_range'

theorem base_above : CompressedHistoryAbove base := by
  intro q _
  change 6 ≤ q+16
  omega

theorem placed_injective (j : Nat) : Function.Injective (placed j) := by
  intro a b h
  apply (pi j).injective
  change pi j a+16=pi j b+16 at h
  exact Nat.add_right_cancel h
theorem allPlaced_injective : Function.Injective allPlaced := by
  intro a b h
  apply pi0.injective
  change pi0 a+16=pi0 b+16 at h
  exact Nat.add_right_cancel h

private theorem appendRange (xs : List Nat) (hd : xs.Nodup) (a n : Nat)
    (sep : ∀q∈xs,q < a ∨ a+n ≤ q) : (xs++List.range' a n).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨hd,List.nodup_range',List.disjoint_left.mpr ?_⟩
  intro q hq hr
  have hs := sep q hq
  simp only [List.mem_range'_1] at hr
  omega

theorem indices_nodup : indices.Nodup := by
  have a := appendRange (List.range' 0 515) List.nodup_range' 684 1114
    (by intro q h; simp only [List.mem_range'_1] at h; omega)
  have b := appendRange _ a 2056 258
    (by intro q h; simp only [List.mem_append,List.mem_range'_1] at h; omega)
  have c := appendRange _ b 2400 12
    (by intro q h; simp only [List.mem_append,List.mem_range'_1] at h; omega)
  exact c

theorem slots_nodup : slots.Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ h
    change a+16=b+16 at h
    exact Nat.add_right_cancel h
  · exact indices_nodup

theorem slots_length : slots.length=1899 := by simp [slots,indices]

theorem mem_indices (q : Nat) : q∈indices ↔ live q ∧ ¬omitted q := by
  simp only [indices,List.mem_append,List.mem_range'_1]
  unfold live omitted
  omega

theorem slot_mem (q : Nat) (hl : live q) (ho : ¬omitted q) : base q∈slots.toFinset := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨q,(mem_indices q).mpr ⟨hl,ho⟩,rfl⟩

private theorem outside_live_outside_zero (q : Nat) (h : ¬live q) : ¬zeroRegion q := by
  unfold live zeroRegion workRegion holeRegion at *
  omega

theorem pi_live (j q : Nat) (hj : j < 170) (hq : live q) : live (pi j q) := by
  by_contra bad
  have eq := (pi j).injective (pi_outside j (pi j q) hj (outside_live_outside_zero _ bad))
  exact bad (eq.symm ▸ hq)

theorem pi0_live (q : Nat) (hq : live q) : live (pi0 q) := by
  by_contra bad
  have eq := pi0.injective (pi0_outside (pi0 q) (outside_live_outside_zero _ bad))
  exact bad (eq.symm ▸ hq)

theorem field_live (q : Nat) (h : fieldSite q) : live q := by unfold fieldSite live at *; omega

theorem packet_live (j q : Nat) (hj : j < 170) (h : q∈packetSites j) : live q := by
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold live
  unfold H at h
  omega

theorem placed_field_mem (j q : Nat) (hj : j < 170) (h : fieldSite q) :
    placed j q∈slots.toFinset := slot_mem _ (pi_live j q hj (field_live q h)) (field_safe j q hj h)

theorem allPlaced_field_mem (q : Nat) (h : fieldSite q) : allPlaced q∈slots.toFinset :=
  slot_mem _ (pi0_live q (field_live q h)) (field_pi0_safe q h)

theorem placed_packet_mem (j q : Nat) (hj : j < 170) (h : q∈packetSites j) :
    placed j q∈slots.toFinset :=
  slot_mem _ (pi_live j q hj (packet_live j q hj h)) (packet_safe j q hj h)

theorem history_packet (j : Nat) (u : Fin 6) : compressedHistoryId (3*j) u∈packetSites j := by
  fin_cases u
  · change 3*j∈packetSites j
    simp [packetSites]
  · change 1028+3*j∈packetSites j
    simp [packetSites]
  · change 3*j+1∈packetSites j
    simp [packetSites]
  · change 1028+3*j+1∈packetSites j
    simp [packetSites,H]
  · change 3*j+2∈packetSites j
    simp [packetSites]
  · change 1028+3*j+2∈packetSites j
    have e : 1028+3*j+2=1030+3*j := by omega
    rw [e]
    simp [packetSites]

theorem placed_pool_nodup (j : Nat) : (skywalkPoolWires (placed j)).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ h; exact placed_injective j h
  · exact List.nodup_range'

theorem placed_above (j : Nat) : CompressedHistoryAbove (placed j) := by
  intro q _
  change 6 ≤ pi j q+16
  omega

/-- Codec placement is constructed above6, not by renaming a codec whose
logical template labels collided with raw group0. -/
theorem codec_support (j : Nat) (hj : j < 170) :
    wires (compressedHistoryEncode (placed j) (3*j))⊆slots.toFinset ∧
    wires (compressedHistoryDecode (placed j) (3*j))⊆slots.toFinset := by
  constructor
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inl rfl) q hq
    exact placed_packet_mem j _ hj (history_packet j u)
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inr rfl) q hq
    exact placed_packet_mem j _ hj (history_packet j u)

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.slots_nodup
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.slots_length
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.codec_support
