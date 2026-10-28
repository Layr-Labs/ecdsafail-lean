import ECDSAAdd.Arithmetic.RecordedRailApplyProof

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApplySigned

def topPre (aTop bTop tau : Wire) : Program := [.CX aTop tau,.CX bTop tau,.X tau]
def topPost (aTop bTop tau : Wire) : Program := [.X tau,.CX aTop tau,.CX bTop tau]
def mask (a : List Wire) (tau : Wire) : Program := a.map (fun q => .CX tau q)
def prepare (a : List Wire) (aTop bTop tau : Wire) : RecordedProgram :=
  embedRecorded (topPre aTop bTop tau ++ mask a tau)
def restore (a : List Wire) (aTop bTop tau : Wire) : RecordedProgram :=
  embedRecorded (mask a tau ++ topPost aTop bTop tau)

def signValue (aTop bTop tau : Wire) (bits : BasisState) : Bool :=
  !((bits tau ^^ bits aTop) ^^ bits bTop)

theorem top_states (aTop bTop tau : Wire) (hat : aTop≠tau) (hbt : bTop≠tau)
    (s : State) (m : List Bool) :
    run (topPre aTop bTop tau) m s=⟨s.phase,writeBit s.basis tau (signValue aTop bTop tau s.basis)⟩ ∧
    run (topPost aTop bTop tau) m s=⟨s.phase,writeBit s.basis tau (signValue aTop bTop tau s.basis)⟩ := by
  constructor <;> apply State.extensionality
  all_goals try rfl
  all_goals
    funext q
    by_cases hq : q=tau <;>
      cases ha : s.basis aTop <;> cases hb : s.basis bTop <;> cases ht : s.basis tau <;>
      simp_all [topPre,topPost,run,signValue,writeBit,Function.update]

theorem mask_state (a : List Wire) (tau : Wire) (nd : a.Nodup) (ht : tau∉a)
    (s : State) (m : List Bool) :
    run (mask a tau) m s=⟨s.phase,fun q => if q∈a then s.basis q ^^ s.basis tau else s.basis q⟩ := by
  induction a generalizing s with
  | nil => simp [mask,run]
  | cons q qs ih =>
    obtain ⟨hq,hn⟩ := List.nodup_cons.mp nd
    have htq : tau≠q := by intro h; exact ht (by simp [h])
    have hqt := Ne.symm htq
    have htt : tau∉qs := fun h => ht (List.mem_cons_of_mem q h)
    simp only [mask,List.map_cons,run]
    rw [show List.map (fun r => Instr.CX tau r) qs=mask qs tau from rfl,ih hn htt]
    apply State.extensionality
    · rfl
    · funext w
      by_cases hw : w=q <;> by_cases hwt : w=tau <;> by_cases hm : w∈qs <;>
        simp_all [writeBit,Function.update]

theorem mask_twice (a : List Wire) (tau : Wire) (nd : a.Nodup) (ht : tau∉a)
    (s : State) (m n : List Bool) : run (mask a tau) n (run (mask a tau) m s)=s := by
  rw [mask_state a tau nd ht,mask_state a tau nd ht]
  apply State.extensionality
  · rfl
  · funext q
    by_cases hq : q∈a <;> cases hp : s.basis tau <;> cases hv : s.basis q <;>
      simp_all

theorem tops_cancel (aTop bTop tau : Wire) (hat : aTop≠tau) (hbt : bTop≠tau)
    (s : State) (m n : List Bool) :
    run (topPost aTop bTop tau) n (run (topPre aTop bTop tau) m s)=s ∧
    run (topPre aTop bTop tau) n (run (topPost aTop bTop tau) m s)=s := by
  constructor
  · rw [(top_states aTop bTop tau hat hbt s m).1,
      (top_states aTop bTop tau hat hbt _ n).2]
    apply State.extensionality
    · rfl
    · funext q
      by_cases hq : q=tau <;>
        cases ha : s.basis aTop <;> cases hb : s.basis bTop <;> cases ht : s.basis tau <;>
        simp_all [signValue,writeBit,Function.update]
  · rw [(top_states aTop bTop tau hat hbt s m).2,
      (top_states aTop bTop tau hat hbt _ n).1]
    apply State.extensionality
    · rfl
    · funext q
      by_cases hq : q=tau <;>
        cases ha : s.basis aTop <;> cases hb : s.basis bTop <;> cases ht : s.basis tau <;>
        simp_all [signValue,writeBit,Function.update]

theorem mask_measurements (a : List Wire) (tau : Wire) : measurementCount (mask a tau)=0 := by
  induction a with
  | nil => rfl
  | cons q qs ih =>
    change measurementCount (Instr.CX tau q::mask qs tau)=0
    simp only [measurementCount,ih,Nat.zero_add]

theorem topPre_measurements (aTop bTop tau : Wire) : measurementCount (topPre aTop bTop tau)=0 := rfl
theorem topPost_measurements (aTop bTop tau : Wire) : measurementCount (topPost aTop bTop tau)=0 := rfl

theorem zero_measurements (a : List Wire) (aTop bTop tau : Wire) :
    recordedMeasurementCount (prepare a aTop bTop tau)=0 ∧
    recordedMeasurementCount (restore a aTop bTop tau)=0 := by
  simp only [prepare,restore,(embedRecorded_counts _).2,measurementCount_append,
    mask_measurements,topPre_measurements,topPost_measurements,Nat.add_zero]
  constructor <;> trivial

theorem run_zero_empty (p : Program) (hp : measurementCount p=0) (m : List Bool) (s : State) :
    run p m s=run p [] s := by
  simpa only [hp,List.take_zero] using (run_take p m s).symm

theorem restored_preparation (a : List Wire) (aTop bTop tau : Wire)
    (nd : a.Nodup) (ht : tau∉a) (hat : aTop≠tau) (hbt : bTop≠tau)
    (s : State) (m : List Bool) (k : Nat) :
    runWithTape (prepare a aTop bTop tau ++ restore a aTop bTop tau) m k s=s ∧
    runWithTape (restore a aTop bTop tau ++ prepare a aTop bTop tau) m k s=s := by
  rw [runWithTape_append,runWithTape_append,(zero_measurements a aTop bTop tau).1,
    (zero_measurements a aTop bTop tau).2]
  simp only [Nat.add_zero,prepare,restore,runWithTape_embedRecorded,run_append,run_take,
    mask_measurements,topPre_measurements,topPost_measurements,List.drop_zero]
  simp only [run_zero_empty (mask a tau) (mask_measurements a tau),
    run_zero_empty (topPre aTop bTop tau) (topPre_measurements aTop bTop tau),
    run_zero_empty (topPost aTop bTop tau) (topPost_measurements aTop bTop tau)]
  constructor
  · change run (topPost aTop bTop tau) []
      (run (mask a tau) [] (run (mask a tau) []
        (run (topPre aTop bTop tau) [] s)))=s
    rw [mask_twice a tau nd ht]
    exact (tops_cancel aTop bTop tau hat hbt s _ _).1
  · change run (mask a tau) []
      (run (topPre aTop bTop tau) [] (run (topPost aTop bTop tau) []
        (run (mask a tau) [] s)))=s
    rw [(tops_cancel aTop bTop tau hat hbt _ _ _).2]
    exact mask_twice a tau nd ht s _ _

end ECDSAAdd.Arithmetic.RecordedRailApplySigned
#print axioms ECDSAAdd.Arithmetic.RecordedRailApplySigned.restored_preparation
