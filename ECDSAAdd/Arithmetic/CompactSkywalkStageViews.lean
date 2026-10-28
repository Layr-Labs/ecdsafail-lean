import ECDSAAdd.Arithmetic.CompactSkywalkTickEntry
import ECDSAAdd.Arithmetic.CompactSkywalkTickOutputSpec

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Mathematical full-word interpretation. This is a basis function, not an
emitted sign-expansion program or an allocated high-copy register. -/
def compactSkywalkStageVirtual (w : Nat → Wire) (i : Nat) (s : BasisState) : BasisState :=
  let A := compactSkywalkSignPoolA w i
  let B := compactSkywalkSignPoolB w i
  fun q => if q ∈ A.released then s A.sign else if q ∈ B.released then s B.sign else s q

def CompactSkywalkStage (w : Nat → Wire) (r : SkywalkRails.State) (i : Nat)
    (s : BasisState) : Prop :=
  SkywalkIntegerStage w r i (compactSkywalkStageVirtual w i s) ∧
  (compactSkywalkSignPoolA w i).Clean s ∧ (compactSkywalkSignPoolB w i).Clean s

theorem compactSkywalkStage_width (i : Nat) (hi : i ≤ 512) :
    2 ≤ narrowSkywalkRouteWidth i ∧ narrowSkywalkRouteWidth i ≤ 258 := by
  unfold narrowSkywalkRouteWidth
  omega

private theorem blockND (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start count : Nat) (hb : start+count ≤ 1798) : (wireBlock w start count).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj he
    simp only [List.mem_range'_1] at hi hj
    exact skywalkPool_index_inj w hn i j (by omega) (by omega) he
  · exact List.nodup_range'

theorem compactSkywalkStage_valid (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) :
    (compactSkywalkSignPoolA w i).Valid ∧ (compactSkywalkSignPoolB w i).Valid := by
  have h := compactSkywalkStage_width i hi
  exact ⟨compactSkywalkSignWord_valid _ _ (by omega)
    (by simpa only [skywalkPoolA,wireBlock_length] using h.2)
    (blockND w hn i 258 (by omega)),
    compactSkywalkSignWord_valid _ _ (by omega)
    (by simpa only [skywalkPoolB,wireBlock_length] using h.2)
    (blockND w hn 770 258 (by decide))⟩

theorem compactSkywalkStage_expanded (w : Nat → Wire) (i : Nat) (hi : i ≤ 512) :
    (compactSkywalkSignPoolA w i).expanded = skywalkPoolA w i ∧
    (compactSkywalkSignPoolB w i).expanded = skywalkPoolB w := by
  have h := compactSkywalkStage_width i hi
  exact ⟨compactSkywalkSignWord_expanded _ _ (by omega)
    (by simpa only [skywalkPoolA,wireBlock_length] using h.2),
    compactSkywalkSignWord_expanded _ _ (by omega)
    (by simpa only [skywalkPoolB,wireBlock_length] using h.2)⟩

theorem compactSkywalkStage_words_disjoint (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) : (skywalkPoolA w i).Disjoint (skywalkPoolB w) := by
  apply List.disjoint_left.mpr
  intro q ha hb
  simp only [skywalkPoolA,skywalkPoolB,wireBlock,List.mem_map,List.mem_range'_1] at ha hb
  obtain ⟨a,ha,hea⟩ := ha
  obtain ⟨b,hb,heb⟩ := hb
  have he := skywalkPool_index_inj w hn a b (by omega) (by omega) (hea.trans heb.symm)
  omega

/-- Outside the two physically released banks the virtual basis is unchanged. -/
theorem compactSkywalkStage_virtual_outside (w : Nat → Wire) (i : Nat) (s : BasisState)
    (q : Wire) (ha : q ∉ (compactSkywalkSignPoolA w i).released)
    (hb : q ∉ (compactSkywalkSignPoolB w i).released) :
    compactSkywalkStageVirtual w i s q = s q := by
  simp [compactSkywalkStageVirtual,ha,hb]

theorem compactSkywalkStage_zero_tails (w : Nat → Wire) :
    (compactSkywalkSignPoolA w 0).released = [] ∧
    (compactSkywalkSignPoolB w 0).released = [] := by
  constructor
  · change (wireBlock w 0 258).drop 258 = []
    have h : (wireBlock w 0 258).drop (wireBlock w 0 258).length = [] := List.drop_length
    simpa only [wireBlock_length] using h
  · change (wireBlock w 770 258).drop 258 = []
    have h : (wireBlock w 770 258).drop (wireBlock w 770 258).length = [] := List.drop_length
    simpa only [wireBlock_length] using h

theorem compactSkywalkStage_zero_virtual (w : Nat → Wire) (s : BasisState) :
    compactSkywalkStageVirtual w 0 s = s := by
  funext q
  simp [compactSkywalkStageVirtual,(compactSkywalkStage_zero_tails w).1,
    (compactSkywalkStage_zero_tails w).2]

/-- The existing seed-stage predicate is exactly the initial compact stage. -/
theorem compactSkywalkStage_zero_iff (w : Nat → Wire) (r : SkywalkRails.State) (s : BasisState) :
    CompactSkywalkStage w r 0 s ↔ SkywalkIntegerStage w r 0 s := by
  simp [CompactSkywalkStage,compactSkywalkStage_zero_virtual,
    CompactSkywalkSignReleaseLayout.Clean,(compactSkywalkStage_zero_tails w).1,
    (compactSkywalkStage_zero_tails w).2]

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStage_zero_iff
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStage_valid
