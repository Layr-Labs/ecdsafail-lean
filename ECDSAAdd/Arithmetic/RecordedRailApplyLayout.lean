import ECDSAAdd.Arithmetic.RecordedRailApplyDebt

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply

theorem slots_length (cursor : Nat) : (oldSlots cursor).length=254 := by
  simp [oldSlots]

theorem slots_earlier (cursor : Nat) : ∀j∈(oldSlots cursor).filterMap id,j<cursor+254 := by
  intro j hj
  simp only [oldSlots,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
    List.filterMap_replicate,Function.id_def,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at hj
  simp only [or_assoc,false_or] at hj
  rcases hj with h|h|h|h|h|h|h <;> subst j <;> omega

/-- Forward's real smaller scratch list inherits the large bank's separation. -/
theorem forward_ready (a b forwardBank mirrorBank : List Wire) (cin even odd : Wire)
    (bits : BasisState) (ready : Ready a b forwardBank mirrorBank cin even odd bits) :
    RecordedRailDefer.Ready32 a b forwardBank cin even odd bits := by
  obtain ⟨⟨aw,bw,fw,mw,nd,smallND,subset⟩,clean⟩ := ready
  have parts := List.nodup_append'.mp nd
  have smallDis : ([cin]++a++b).Disjoint (forwardBank++[even,odd]) := by
    apply List.disjoint_left.mpr
    intro q hq hs
    exact List.disjoint_left.mp parts.2.2 hq (subset q hs)
  have smallAll : (([cin]++a++b)++(forwardBank++[even,odd])).Nodup :=
    List.nodup_append'.mpr ⟨parts.1,smallND,smallDis⟩
  refine ⟨aw,bw,fw,?_,?_,?_,?_⟩
  · simpa only [List.append_assoc] using smallAll
  · intro q hq
    exact clean q (subset q (List.mem_append_left _ hq))
  · exact clean even (subset even (by simp))
  · exact clean odd (subset odd (by simp))

theorem aligned_mirror (a b forwardBank mirrorBank : List Wire) (cin even odd : Wire)
    (layout : Layout a b forwardBank mirrorBank cin even odd) (cursor : Nat) :
    RecordedRailRipple.Aligned a b mirrorBank (oldSlots cursor) := by
  obtain ⟨aw,bw,_,mw,_,_,_⟩ := layout
  simp [RecordedRailRipple.Aligned,aw,bw,mw,slots_length]

/-- Full source and control separation from the target is a layout fact. -/
theorem data_separation (a b mirrorBank : List Wire) (cin : Wire)
    (nd : ([cin]++a++b++mirrorBank).Nodup) :
    b.Nodup ∧ cin∉b ∧ (∀q∈a,q∉b) ∧ (∀q∈mirrorBank,q∉b) := by
  have parts := List.nodup_append'.mp nd
  have data := List.nodup_append'.mp parts.1
  refine ⟨data.2.1,?_,?_,?_⟩
  · intro h
    exact List.disjoint_left.mp data.2.2 (by simp) h
  · intro q hq h
    exact List.disjoint_left.mp data.2.2 (by simp [hq]) h
  · intro q hq h
    exact List.disjoint_left.mp parts.2.2 (by simp [h]) hq

/-- Actual bitwise complement with complete spectator and phase preservation. -/
theorem flip_state (b : List Wire) (nd : b.Nodup) (m : List Bool) (cursor : Nat) (s : State) :
    runWithTape (embedRecorded (notRegister b)) m cursor s=
      ⟨s.phase,fun q => if q∈b then !s.basis q else s.basis q⟩ := by
  rw [runWithTape_embedRecorded]
  exact notRegister_correct b nd s (m.drop cursor)

theorem flip_measurements (b : List Wire) :
    recordedMeasurementCount (embedRecorded (notRegister b))=0 :=
  (embedRecorded_counts _).2.trans (notRegister_counts b).2

end ECDSAAdd.Arithmetic.RecordedRailApply
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply.forward_ready
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply.flip_state
