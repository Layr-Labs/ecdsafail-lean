import ECDSAAdd.Arithmetic.Shift
import ECDSAAdd.Arithmetic.Divsteps.DeferredDecoder

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

/-- The finite history brigade shifts toward high indices before swapping
its low port with the branch bit. This is the author's controlled push order. -/
def pushHistory (store port : Wire) (record : List Wire) : Program :=
  shiftLeft store (port::record)

def popHistory (store port : Wire) (record : List Wire) : Program :=
  shiftRight store (port::record)

/-- The fit premise is the actual finite-history overflow event. -/
theorem pushHistory_spec (store port : Wire) (record : List Wire)
    (hn : (store::port::record).Nodup) (s : State) (m : List Bool)
    (hfit : s.basis store=true →
      2*regValue record s.basis+(s.basis port).toNat<2^record.length) :
    let t := run (pushHistory store port record) m s
    t.phase=s.phase ∧ t.basis store=s.basis store ∧
      t.basis port=(if s.basis store then false else s.basis port) ∧
      regValue record t.basis=(if s.basis store then
        2*regValue record s.basis+(s.basis port).toNat else regValue record s.basis) ∧
      ∀ w,w∉port::record → t.basis w=s.basis w := by
  have hv := shiftLeft_spec store (port::record) hn (s.basis store)
    (regValue (port::record) s.basis) (by
      intro hc
      have hf := hfit hc
      simp only [List.length_cons,pow_succ]
      change 2*((if s.basis port then 1 else 0)+2*regValue record s.basis)<2^record.length*2
      cases hp : s.basis port <;> simp [hp] at hf ⊢ <;> omega) s m ⟨rfl,rfl⟩
  have frame := (shift_frame store (port::record) s m).2.2
  dsimp only
  refine ⟨frame.1,hv.2.1,?_,?_,frame.2⟩
  · have hh := hv.2.2
    change (run (pushHistory store port record) m s).basis port=_
    change (if (run (pushHistory store port record) m s).basis port then 1 else 0)+
      2*regValue record (run (pushHistory store port record) m s).basis=_ at hh
    cases hc : s.basis store <;> cases hp : s.basis port <;>
      cases ht : (run (pushHistory store port record) m s).basis port <;>
      simp [hc,hp,ht,regValue] at hh ⊢ <;> omega
  · have hh := hv.2.2
    change (if (run (pushHistory store port record) m s).basis port then 1 else 0)+
      2*regValue record (run (pushHistory store port record) m s).basis=_ at hh
    cases hc : s.basis store <;> cases hp : s.basis port <;>
      cases ht : (run (pushHistory store port record) m s).basis port <;>
      simp [hc,hp,ht,regValue] at hh ⊢ <;> omega

theorem history_roundtrip (store port : Wire) (record : List Wire)
    (hn : (store::port::record).Nodup) (s : State) (m : List Bool) :
    run (popHistory store port record) m (run (pushHistory store port record) m s)=s :=
  shiftRight_left_cancel store (port::record) hn s m

theorem history_counts (store port : Wire) (record : List Wire) :
    toffoliCount (pushHistory store port record)=record.length ∧
    measurementCount (pushHistory store port record)=0 ∧
    toffoliCount (popHistory store port record)=record.length ∧
    measurementCount (popHistory store port record)=0 := by
  have h := shift_counts store (port::record)
  simpa only [pushHistory,popHistory,List.length_cons,Nat.add_sub_cancel] using
    (show toffoliCount (shiftLeft store (port::record))=(port::record).length-1 ∧
      measurementCount (shiftLeft store (port::record))=0 ∧
      toffoliCount (shiftRight store (port::record))=(port::record).length-1 ∧
      measurementCount (shiftRight store (port::record))=0 from ⟨h.2.2.1,h.2.2.2,h.1,h.2.1⟩)

/-- Store when selected, then release the physical branch port by X measurement.
The classical outcome is used at the mirrored reverse step. -/
def pushForget (store port : Wire) (record : List Wire) : RecordedProgram :=
  embedRecorded (pushHistory store port record) ++ forgetBranch port

theorem pushForget_run (store port : Wire) (record : List Wire)
    (hn : (store::port::record).Nodup) (s : State) (m : List Bool) (ordinal : Nat)
    (hfit : s.basis store=true →
      2*regValue record s.basis+(s.basis port).toNat<2^record.length) :
    let v := run (pushHistory store port record) (m.drop ordinal) s
    runWithTape (pushForget store port record) m ordinal s=
      ⟨s.phase ^^ (m.getD ordinal false && (!s.basis store && s.basis port)),
        writeBit v.basis port false⟩ := by
  have h := pushHistory_spec store port record hn s (m.drop ordinal) hfit
  dsimp only
  rw [pushForget,runWithTape_append,runWithTape_embedRecorded,
    (embedRecorded_counts _).2,(history_counts store port record).2.1,Nat.add_zero,
    forgetBranch_run,h.1,h.2.2.1]
  cases s.basis store <;> simp

/-- On a stored branch the port was already cleared, hence its measurement
has no phase debt. The actual pop network restores the entire input state. -/
theorem pushForget_pop_stored (store port : Wire) (record : List Wire)
    (hn : (store::port::record).Nodup) (s : State) (m : List Bool) (ordinal : Nat)
    (hc : s.basis store=true)
    (hfit : 2*regValue record s.basis+(s.basis port).toNat<2^record.length) :
    run (popHistory store port record) (m.drop ordinal)
      (runWithTape (pushForget store port record) m ordinal s)=s := by
  have h := pushHistory_spec store port record hn s (m.drop ordinal) (fun _ => hfit)
  have he : runWithTape (pushForget store port record) m ordinal s=
      run (pushHistory store port record) (m.drop ordinal) s := by
    rw [pushForget_run store port record hn s m ordinal (fun _ => hfit)]
    apply congrArg₂ State.mk
    · simpa [hc] using h.1.symm
    · funext w
      by_cases hw : w=port
      · subst w
        simpa [writeBit,hc] using h.2.2.1.symm
      · simp [writeBit,hw]
  rw [he]
  exact history_roundtrip store port record hn s (m.drop ordinal)

theorem pushForget_counts (store port : Wire) (record : List Wire) :
    recordedToffoliCount (pushForget store port record)=record.length ∧
    recordedMeasurementCount (pushForget store port record)=1 := by
  simp [pushForget,recordedToffoliCount_append,recordedMeasurementCount_append,
    (embedRecorded_counts _).1,(embedRecorded_counts _).2,
    (history_counts store port record).1,(history_counts store port record).2.1,
    (forgetBranch_resources port).1,(forgetBranch_resources port).2.1]

theorem history_support (store port : Wire) (record : List Wire) :
    wires (pushHistory store port record)⊆(store::port::record).toFinset ∧
    wires (popHistory store port record)⊆(store::port::record).toFinset := by
  have h := shift_wires store (port::record)
  rw [pushHistory,popHistory,h.1,h.2]
  split_ifs <;> simp

theorem pushForget_wellFormed (store port : Wire) (record : List Wire) (cursor : Nat) :
    RecordedWellFormedAt cursor (pushForget store port record) := by
  rw [pushForget,RecordedWellFormedAt_append]
  exact ⟨embedRecorded_wellFormed _ _,by simp [forgetBranch,RecordedWellFormedAt]⟩

theorem pushForget_support (store port : Wire) (record : List Wire) :
    recordedWires (pushForget store port record)⊆(store::port::record).toFinset := by
  rw [pushForget,recordedWires_append,embedRecorded_wires,(forgetBranch_resources port).2.2]
  exact Finset.union_subset (history_support store port record).1 (by simp)

end ECDSAAdd.Arithmetic.Paper935
