import ECDSAAdd.Arithmetic.Divsteps.SwapHistory

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- Nested actual forward/reverse schedule. Every swap wire is measured after
its forward step, reconstructed from restored endpoint data on the reverse
pass, and phase-corrected using its own original absolute tape ordinal. -/
def StepLayout.deferredSwaps (L : StepLayout) (start : Nat) : Nat → Nat → RecordedProgram
  | 0, _ => []
  | n+1, cursor =>
    let A := L.at start
    embedRecorded A.program ++
      (forgetBranch A.history.swap ++
        L.deferredSwaps (start+1) n (cursor+measurementCount A.program+1) ++
        recoverBranch A.swapDecoder A.history.swap (cursor+measurementCount A.program)) ++
      embedRecorded A.undo

/-- All swaps are genuinely measured, including those in the intervening
schedule. No phase contract for an abstract gap is assumed. -/
theorem StepLayout.deferredSwaps_correct (L : StepLayout) (h : L.Valid)
    (p x : Int) (hp : p%2=1) (limit : Nat) (hhistory : limit≤L.future.length)
    (hfit : ∀ i, i<limit → (L.at i).Fits (zWalk p x i))
    (start n : Nat) (hrange : start+n≤limit) (s : State) (m : List Bool) (cursor : Nat)
    (hs : (L.at start).Ready (zWalk p x start) s.basis) :
    runWithTape (L.deferredSwaps start n cursor) m cursor s=s := by
  induction n generalizing start s cursor with
  | zero => rfl
  | succ n ih =>
    let A := L.at start
    let t := run A.program (m.drop cursor) s
    let ordinal := cursor+measurementCount A.program
    let u := runWithTape (forgetBranch A.history.swap) m ordinal t
    have hA := L.at_valid h start
    have hne : A.future≠[] := L.at_can_advance start (by omega)
    have ht : A.next.Ready (zWalk p x (start+1)) t.basis :=
      (A.program_spec hA (zWalk p x start) (hfit start (by omega)) hne s (m.drop cursor) hs).2
    have hu : (L.at (start+1)).Ready (zWalk p x (start+1)) u.basis := by
      rw [show u=runWithTape (forgetBranch A.history.swap) m ordinal t from rfl,forgetBranch_run]
      exact A.next.ready_write_past (A.next_valid hA) (zWalk p x (start+1)) t.basis
        A.history.swap false (A.current_in_next_past hne) ht
    have hg := ih (start+1) (by omega) u (ordinal+1) hu
    obtain ⟨ha,hl⟩ := A.swapDecoder_distinct hA
    have hv := A.swapDecoder_after hA p (zWalk p x start) (invariant_zWalk hp x start) hp
      (hfit start (by omega)) s (m.drop cursor) hs
    have hpair := deferredSwap_recorded_gap A.history.active A.fv.second A.history.swap ha hl
      (L.deferredSwaps (start+1) n (ordinal+1)) m ordinal t hv hg
    rw [deferredSwaps,runWithTape_append,runWithTape_append,runWithTape_embedRecorded]
    simp only [(embedRecorded_counts _).2,runWithTape_embedRecorded]
    simp only [A,t,ordinal] at hpair
    simp only [swapDecoder]
    rw [hpair]
    exact A.undo_after hA (zWalk p x start) (hfit start (by omega)) s (m.drop cursor) _
      hs.1 hs.2.1 hs.2.2.1

theorem StepLayout.deferredSwaps_wellFormed (L : StepLayout) (start n cursor : Nat) :
    RecordedWellFormedAt cursor (L.deferredSwaps start n cursor) := by
  induction n generalizing start cursor with
  | zero => trivial
  | succ n ih =>
    rw [deferredSwaps,RecordedWellFormedAt_append]
    refine ⟨?_,embedRecorded_wellFormed _ _⟩
    rw [RecordedWellFormedAt_append]
    refine ⟨embedRecorded_wellFormed _ _,?_⟩
    rw [(embedRecorded_counts _).2]
    exact deferredPair_wellFormed _ _ _ _ (ih (start+1) _)

theorem StepLayout.deferredSwaps_counts (L : StepLayout) (h : L.Valid)
    (n v k : Nat) (hw : L.Sized n v k) (start slots cursor : Nat) :
    recordedToffoliCount (L.deferredSwaps start slots cursor)=slots*(2*(5*n+5*v+k-4)+1) ∧
    recordedMeasurementCount (L.deferredSwaps start slots cursor)=slots*(2*(4*n+3*v+k-5)+1) := by
  induction slots generalizing start cursor with
  | zero => simp [deferredSwaps,recordedToffoliCount,recordedMeasurementCount]
  | succ slots ih =>
    have hf := (L.at start).program_counts (L.at_valid h start) n v k (L.at_sized n v k hw start)
    have hr := (L.at start).undo_counts (L.at_valid h start) n v k (L.at_sized n v k hw start)
    simp only [deferredSwaps,recordedToffoliCount_append,recordedMeasurementCount_append,
      (embedRecorded_counts _).1,(embedRecorded_counts _).2,
      (forgetBranch_resources _).1,(forgetBranch_resources _).2.1,
      (recoverBranch_resources _ _ _).1,(recoverBranch_resources _ _ _).2.1,
      swapDecoder,(decodeSwap_resources _ _ _).1,(decodeSwap_resources _ _ _).2.1,
      hf.1,hf.2,hr.1,hr.2,(ih _ _).1,(ih _ _).2]
    constructor <;> ring

theorem StepLayout.deferredSwaps_support (L : StepLayout) (h : L.Valid)
    (start slots cursor : Nat) : recordedWires (L.deferredSwaps start slots cursor)⊆L.used.toFinset := by
  induction slots generalizing start cursor with
  | zero => simp [deferredSwaps,recordedWires]
  | succ slots ih =>
    have hf := (L.at start).program_support (L.at_valid h start)
    have hr := (L.at start).undo_support (L.at_valid h start)
    have hd := (L.at start).swapRecovery_support (L.at_valid h start)
      (cursor+measurementCount (L.at start).program)
    rw [L.at_support start] at hf hr hd
    have hq : {(L.at start).history.swap}⊆L.used.toFinset := by
      intro w hw
      apply hd
      rw [(recoverBranch_resources _ _ _).2.2.1]
      exact Finset.mem_union_right _ hw
    simp only [deferredSwaps,recordedWires_append,embedRecorded_wires,
      (forgetBranch_resources _).2.2,Finset.union_subset_iff]
    exact ⟨⟨hf,⟨⟨hq,ih _ _⟩,hd⟩⟩,hr⟩

theorem StepLayout.deferredSwaps_qubits (L : StepLayout) (h : L.Valid)
    (start slots cursor : Nat) : (recordedWires (L.deferredSwaps start slots cursor)).card≤L.used.length := by
  have hh := Finset.card_le_card (L.deferredSwaps_support h start slots cursor)
  rwa [List.toFinset_card_of_nodup h.unique] at hh

/-- All 590 swap histories are measured and corrected; activity and parity
history are still retained, and no terminal g=0 assumption is made. -/
theorem StepLayout.deferredSwaps590_correct (L : StepLayout) (h : L.Valid)
    (hw : L.Sized 258 592 11) (hhistory : 590≤L.future.length)
    (p x : Int) (hp : 0≤p) (hodd : p%2=1) (hsmall : p<2^256) (hx : 0≤x) (hxp : x≤p)
    (s : State) (m : List Bool) (cursor : Nat) (hs : L.Ready (zSeed p x) s.basis) :
    runWithTape (L.deferredSwaps 0 590 cursor) m cursor s=s :=
  L.deferredSwaps_correct h p x hodd 590 hhistory
    (L.walk590_fits hw p x hp hodd hsmall hx hxp) 0 590 (by omega) s m cursor hs

theorem StepLayout.deferredSwaps590_counts (L : StepLayout) (h : L.Valid)
    (hw : L.Sized 258 592 11) (cursor : Nat) :
    recordedToffoliCount (L.deferredSwaps 0 590 cursor)=5023850 ∧
    recordedMeasurementCount (L.deferredSwaps 0 590 cursor)=3321110 := by
  have hh := L.deferredSwaps_counts h 258 592 11 hw 0 590 cursor
  norm_num at hh
  exact hh

end ECDSAAdd.Arithmetic.Divsteps
