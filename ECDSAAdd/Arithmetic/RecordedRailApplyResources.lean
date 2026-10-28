import ECDSAAdd.Arithmetic.RecordedRailApplyProgram
import ECDSAAdd.Arithmetic.RecordedRailDeferSupport

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply

theorem oldSlots_length (cursor : Nat) : (oldSlots cursor).length=254 := by
  simp [oldSlots]

theorem oldSlots_earlier (cursor : Nat) :
    ∀j∈(oldSlots cursor).filterMap id,j<cursor+254 := by
  intro j hj
  rcases List.mem_filterMap.mp hj with ⟨slot,member,equal⟩
  change slot=some j at equal
  subst slot
  have possible : j=cursor+62 ∨ j=cursor+94 ∨ j=cursor+126 ∨ j=cursor+158 ∨
      j=cursor+190 ∨ j=cursor+222 ∨ j=cursor+253 := by
    simpa [oldSlots] using member
  rcases possible with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

private theorem aligned (a b mirrorBank : List Wire) (oldCursor : Nat)
    (ha : a.length=256) (hb : b.length=256) (hm : mirrorBank.length=254) :
    RecordedRailRipple.Aligned a b mirrorBank (oldSlots oldCursor) := by
  simp [RecordedRailRipple.Aligned,ha,hb,hm,oldSlots_length]

theorem program_counts (a b mirrorBank : List Wire) (cin : Wire) (oldCursor : Nat)
    (ha : a.length=256) (hb : b.length=256) (hm : mirrorBank.length=254) :
    recordedToffoliCount (program a b mirrorBank cin oldCursor)=255 ∧
    recordedMeasurementCount (program a b mirrorBank cin oldCursor)=254 := by
  have core := RecordedRailRipple.aligned_counts a b mirrorBank (oldSlots oldCursor)
    (aligned a b mirrorBank oldCursor ha hb hm) (some cin)
  have n := embedRecorded_counts (notRegister b)
  have nc := notRegister_counts b
  simp only [program,recordedToffoliCount_append,recordedMeasurementCount_append,
    n.1,n.2,nc.1,nc.2,Nat.zero_add,Nat.add_zero]
  simpa only [ha] using core

theorem pair_counts (a b forwardBank mirrorBank : List Wire) (cin even odd : Wire)
    (oldCursor : Nat) (layout : Layout a b forwardBank mirrorBank cin even odd) :
    recordedToffoliCount (pair a b forwardBank mirrorBank cin even odd oldCursor)=510 ∧
    recordedMeasurementCount (pair a b forwardBank mirrorBank cin even odd oldCursor)=508 := by
  rcases layout with ⟨ha,hb,hf,hm,_,_,_⟩
  have f := RecordedRailDefer.forward32_counts a b forwardBank cin even odd ha hb hf
  have m := program_counts a b mirrorBank cin oldCursor ha hb hm
  simp only [pair,recordedToffoliCount_append,recordedMeasurementCount_append,f.1,f.2,m.1,m.2]
  constructor <;> trivial

def allSites (a b mirrorBank : List Wire) (cin : Wire) : Finset Wire :=
  (cin::(a++b++mirrorBank)).toFinset

theorem program_support (a b mirrorBank : List Wire) (cin : Wire) (oldCursor : Nat)
    (ha : a.length=256) (hb : b.length=256) (hm : mirrorBank.length=254) :
    recordedWires (program a b mirrorBank cin oldCursor) ⊆ allSites a b mirrorBank cin := by
  have h := RecordedRailRipple.ripple_support a b mirrorBank (oldSlots oldCursor)
    (RecordedRailRipple.aligned_shape _ _ _ _ (aligned a b mirrorBank oldCursor ha hb hm)) (some cin)
  simp only [program,recordedWires_append,embedRecorded_wires,notRegister_wires,
    Finset.union_subset_iff]
  have bd : b.toFinset ⊆ allSites a b mirrorBank cin := by
    intro q hq
    simp only [List.mem_toFinset] at hq
    simp [allSites,hq]
  exact ⟨⟨bd,by simpa [RecordedRailRipple.sites,allSites] using h⟩,bd⟩

theorem pair_support (a b forwardBank mirrorBank : List Wire) (cin even odd : Wire)
    (oldCursor : Nat) (layout : Layout a b forwardBank mirrorBank cin even odd) :
    recordedWires (pair a b forwardBank mirrorBank cin even odd oldCursor) ⊆
      allSites a b mirrorBank cin := by
  rcases layout with ⟨ha,hb,hf,hm,_,_,sub⟩
  have forward := RecordedRailDefer.forward32_support a b forwardBank cin even odd ha hb hf
  have slots : RecordedRailDefer.allSites a b forwardBank cin even odd ⊆ allSites a b mirrorBank cin := by
    intro q hq
    simp only [RecordedRailDefer.allSites,List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    simp only [allSites,List.mem_toFinset,List.mem_cons,List.mem_append] at ⊢
    have he : even∈mirrorBank := sub even (by simp)
    have ho : odd∈mirrorBank := sub odd (by simp)
    rcases hq with rfl|rfl|rfl|(haq|hbq)|hk
    · tauto
    · exact Or.inr (Or.inr he)
    · exact Or.inr (Or.inr ho)
    · tauto
    · tauto
    · exact Or.inr (Or.inr (sub q (List.mem_append_left _ hk)))
  simp only [pair,recordedWires_append,Finset.union_subset_iff]
  exact ⟨forward.trans slots,program_support a b mirrorBank cin oldCursor ha hb hm⟩

theorem pair_site_bound (a b forwardBank mirrorBank : List Wire) (cin even odd : Wire)
    (oldCursor : Nat) (layout : Layout a b forwardBank mirrorBank cin even odd) :
    (recordedWires (pair a b forwardBank mirrorBank cin even odd oldCursor)).card ≤767 := by
  have h := Finset.card_le_card (pair_support a b forwardBank mirrorBank cin even odd oldCursor layout)
  have bound := List.toFinset_card_le (cin::(a++b++mirrorBank))
  simp only [allSites] at h
  rcases layout with ⟨ha,hb,_,hm,_,_,_⟩
  simp only [List.length_cons,List.length_append,ha,hb,hm] at bound
  omega

end ECDSAAdd.Arithmetic.RecordedRailApply
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply.pair_counts
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply.pair_site_bound
