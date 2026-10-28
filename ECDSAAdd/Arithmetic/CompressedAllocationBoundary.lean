import ECDSAAdd.Arithmetic.CompressedAllocationPermutation
import ECDSAAdd.Arithmetic.CompressedCompactZeroSlots
import ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCallerClean

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedAllocation

private theorem region_W (q : Nat) (h : workRegion q) :
    ∃j, j < 170 ∧ q=W j := by
  refine ⟨q-515,?_,?_⟩
  · unfold workRegion at h; omega
  · unfold workRegion at h; unfold W; omega

private theorem region_H (q : Nat) (h : holeRegion q) :
    ∃j, j < 170 ∧ q=H j := by
  refine ⟨(q-1029)/3,?_,?_⟩
  · unfold holeRegion at h; omega
  · unfold holeRegion at h; unfold H; omega

/-- The accepted compressed integer assertion supplies every hole zero;
the actual existing caller field-work invariant supplies every work zero.
There is no additional assumed all-zero allocation-bank oracle. -/
theorem caller_zero_boundary (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (s : State) (hstage : CompressedCompactStage w x p 512 s.basis)
    (hw : regValue (skywalkSharedField w).work s.basis=0) :
    ∀q,zeroRegion q → (pullState w s).basis q=false := by
  intro q hq
  rcases hq with hq|hq
  · obtain ⟨j,hj,rfl⟩ := region_W q hq
    exact OffsetCleanupBorrowedCaller.maskBit_zero w s.basis hw (W j)
      (by unfold W; omega) (by unfold W; omega)
  · obtain ⟨j,hj,rfl⟩ := region_H q hq
    have zero := compressedCompactStage_512_zero_slots w hn hlo x p hp0 hpo s hstage j hj
    change s.basis (w (H j))=false
    have index : H j=1029+3*j := by unfold H; omega
    rw [index]
    exact zero

private theorem perm_preserves_region (e : Equiv.Perm Nat)
    (fix : ∀q,¬zeroRegion q → e q=q) (q : Nat) (hq : zeroRegion q) : zeroRegion (e q) := by
  by_contra bad
  have eq : e q=q := e.injective (fix (e q) bad)
  exact bad (eq.symm ▸ hq)

/-- Arbitrary phase and all live data are preserved: the entire placement
permutation acts only on sites supplied zero by the boundary certificate. -/
theorem pull_zero_permutation (e : Equiv.Perm Nat) (s : State)
    (fix : ∀q,¬zeroRegion q → e q=q)
    (hz : ∀q,zeroRegion q → s.basis q=false) : pullState e s=s := by
  apply State.extensionality
  · rfl
  · funext q
    by_cases hq : zeroRegion q
    · exact (hz (e q) (perm_preserves_region e fix q hq)).trans (hz q hq).symm
    · change s.basis (e q)=s.basis q
      rw [fix q hq]

theorem pi0_boundary (s : State) (hz : ∀q,zeroRegion q → s.basis q=false) :
    pullState pi0 s=s := pull_zero_permutation pi0 s pi0_outside hz

theorem pi_boundary (j : Nat) (hj : j < 170) (s : State)
    (hz : ∀q,zeroRegion q → s.basis q=false) : pullState (pi j) s=s :=
  pull_zero_permutation (pi j) s (pi_outside j · hj ·) hz

private theorem encode_other_zero_role (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (j : Nat) (hj : j < 170) (q : Nat)
    (hq : zeroRegion q) (hne : q ≠ H j) (s : State) (m : List Bool) :
    (run (compressedHistoryEncode w (3*j)) m s).basis (w q)=s.basis (w q) := by
  apply run_preserves_outside
  intro touch
  obtain ⟨index,eq⟩ := compressedHistory_gate_mem w hn hlo (3*j) (by omega)
    _ (Or.inl rfl) (w q) touch
  have qb : q < 1798 := by unfold zeroRegion workRegion holeRegion at hq; omega
  have same := skywalkPool_index_inj w hn q (compressedHistoryId (3*j) index)
    qb (compressedHistoryId_bound _ (by omega) index) eq
  have ix := index.isLt
  unfold zeroRegion workRegion holeRegion at hq
  unfold H at hne
  unfold compressedHistoryId at same
  split_ifs at same <;> omega

/-- The measured current encoder re-establishes all zero allocation roles.
Other packed holes and clean field work are transported by actual support;
only the current hole zero is supplied anew by the codec correctness proof. -/
theorem reencode_zero_boundary (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (j : Nat) (hj : j < 170) (s : State) (m : List Bool)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (other : ∀k, k < 170 → k ≠ j → s.basis (w (H k))=false)
    (legal : (s.basis (compressedHistoryMap w (3*j) 0) && s.basis (compressedHistoryMap w (3*j) 1))=false ∧
      (s.basis (compressedHistoryMap w (3*j) 2) && s.basis (compressedHistoryMap w (3*j) 3))=false ∧
      (s.basis (compressedHistoryMap w (3*j) 4) && s.basis (compressedHistoryMap w (3*j) 5))=false) :
    ∀q,zeroRegion q →
      (run (compressedHistoryEncode w (3*j)) m s).basis (w q)=false := by
  have codec := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*j))
    (compressedHistoryMap_injective w hn (3*j) (by omega))
    (compressedHistoryMap_above w (3*j) (by omega) hlo) s m legal
  intro q hq
  by_cases current : q=H j
  · subst q
    have hz := codec.2.1
    change (run (compressedHistoryEncode w (3*j)) m s).basis (w (1028+3*j+1))=false at hz
    have index : H j=1028+3*j+1 := rfl
    rw [index]
    exact hz
  · have keep := encode_other_zero_role w hn hlo j hj q hq current s m
    rw [keep]
    rcases hq with hq|hq
    · obtain ⟨k,hk,rfl⟩ := region_W q hq
      exact OffsetCleanupBorrowedCaller.maskBit_zero w s.basis hw (W k)
        (by unfold W; omega) (by unfold W; omega)
    · obtain ⟨k,hk,rfl⟩ := region_H q hq
      exact other k hk (by intro same; subst k; exact current rfl)

end ECDSAAdd.Arithmetic.CompressedAllocation
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.caller_zero_boundary
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.pi_boundary
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.reencode_zero_boundary
