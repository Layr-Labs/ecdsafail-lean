import ECDSAAdd.Arithmetic.CompressedAllocationPermutation
import ECDSAAdd.Arithmetic.CompressedFieldCellSupport

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedAllocation

def fieldSite (q : Nat) : Prop :=
  (512 ≤ q ∧ q ≤ 769) ∨ (770 ≤ q ∧ q ≤ 1027) ∨
  (1540 ≤ q ∧ q ≤ 1797) ∨ (2056 ≤ q ∧ q ≤ 2312) ∨
  q=0 ∨ q=1 ∨ q=2400 ∨ q=2409 ∨ q=2410

def packetSites (j : Nat) : List Nat :=
  [3*j,1028+3*j,3*j+1,H j,3*j+2,1030+3*j]

def groupInventory (j : Nat) : List Nat :=
  CompressedFieldSupport.sharedSites id 2409 ++ [2400,2410] ++ packetSites j

theorem nonhole_pi_safe (j q : Nat) (hj : j < 170) (hq : ¬holeRegion q) :
    ¬omitted (pi j q) := by
  by_cases hw : workRegion q
  · have hk : q-515 < 170 := by unfold workRegion at hw; omega
    have eq : q=W (q-515) := by unfold workRegion at hw; unfold W; omega
    by_cases same : q-515=j
    · rw [eq,same]
      exact pi_selected_not_omitted j hj
    · rw [eq]
      exact pi_other_not_omitted j _ hj hk same
  · have hz : ¬zeroRegion q := fun h => h.elim hw hq
    rw [pi_outside j q hj hz]
    unfold omitted workRegion at *
    omega

theorem nonhole_pi0_safe (q : Nat) (hq : ¬holeRegion q) : ¬omitted (pi0 q) := by
  by_cases hw : workRegion q
  · have hk : q-515 < 170 := by unfold workRegion at hw; omega
    have eq : q=W (q-515) := by unfold workRegion at hw; unfold W; omega
    rw [eq,pi0_W _ hk]
    unfold omitted H
    omega
  · have hz : ¬zeroRegion q := fun h => h.elim hw hq
    rw [pi0_outside q hz]
    unfold omitted workRegion at *
    omega

theorem field_not_hole (q : Nat) (h : fieldSite q) : ¬holeRegion q := by
  unfold fieldSite holeRegion at *
  omega

theorem field_safe (j q : Nat) (hj : j < 170) (h : fieldSite q) : ¬omitted (pi j q) :=
  nonhole_pi_safe j q hj (field_not_hole q h)

theorem field_pi0_safe (q : Nat) (h : fieldSite q) : ¬omitted (pi0 q) :=
  nonhole_pi0_safe q (field_not_hole q h)

theorem packet_fixed (j q : Nat) (hj : j < 170) (h : q∈packetSites j) : pi j q=q := by
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  · apply pi_outside j _ hj; unfold zeroRegion workRegion holeRegion; omega
  · apply pi_outside j _ hj; unfold zeroRegion workRegion holeRegion; omega
  · apply pi_outside j _ hj; unfold zeroRegion workRegion holeRegion; omega
  · exact pi_current j hj
  · apply pi_outside j _ hj; unfold zeroRegion workRegion holeRegion; omega
  · apply pi_outside j _ hj; unfold zeroRegion workRegion holeRegion; omega

theorem packet_safe (j q : Nat) (hj : j < 170) (h : q∈packetSites j) : ¬omitted (pi j q) := by
  rw [packet_fixed j q hj h]
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold omitted
  unfold H at h
  omega

private theorem shared_field_site (q : Nat)
    (h : q∈CompressedFieldSupport.sharedSites id 2409) : fieldSite q := by
  simp only [CompressedFieldSupport.sharedSites,balancedSharedPorts,
    BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    OffsetCleanupBorrowedCaller.carry,wireBlock,List.map_id,List.mem_append,
    List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold fieldSite
  omega

theorem inventory_safe (j q : Nat) (hj : j < 170) (h : q∈groupInventory j) :
    ¬omitted (pi j q) := by
  simp only [groupInventory,List.mem_append] at h
  rcases h with (h|h)|h
  · exact field_safe j q hj (shared_field_site q h)
  · have hs : q=2400 ∨ q=2410 := by simpa using h
    apply field_safe j q hj
    unfold fieldSite
    omega
  · exact packet_safe j q hj h

/-- The certificate uses the accepted actual instruction-derived cell
support, rather than an assumed semantic frame or declared-list oracle. -/
theorem current_cells_avoid_omitted (j : Nat) (hj : j < 170)
    (g swap : Nat) (hg : g∈packetSites j) (hs : swap∈packetSites j) (ig is : Bool) :
    (∀q∈wires (renameProgram (pi j)
      (OffsetBorrowedCanonical.cell id 2400 g swap 2409 2410 ig is)),¬omitted q) ∧
    (∀q∈wires (renameProgram (pi j)
      (OffsetBorrowedInverseCanonical.cell id 2400 g swap 2409 2410 ig is)),¬omitted q) := by
  have actual := CompressedFieldSupport.cells_active id 2400 g swap 2409 2410 ig is
    (groupInventory j).toFinset
    (by intro q hq; simp only [groupInventory,List.mem_toFinset,List.mem_append];
        exact Or.inl (Or.inl (List.mem_toFinset.mp hq)))
    (by simp [groupInventory]) (by simp [groupInventory,hg])
    (by simp [groupInventory,hs]) (by simp [groupInventory])
  constructor
  · intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨old,hold,rfl⟩ := Finset.mem_image.mp hq
    exact inventory_safe j old hj (List.mem_toFinset.mp (actual.1 hold))
  · intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨old,hold,rfl⟩ := Finset.mem_image.mp hq
    exact inventory_safe j old hj (List.mem_toFinset.mp (actual.2 hold))

theorem current_work_record_disjoint (j k : Nat) (hj : j < 170) (hk : k < 170)
    (q : Nat) (h : q∈packetSites j) : pi j (W k) ≠ pi j q := by
  apply (pi j).injective.ne
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold W H at *
  omega

end ECDSAAdd.Arithmetic.CompressedAllocation
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.packet_fixed
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.current_cells_avoid_omitted
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.current_work_record_disjoint
