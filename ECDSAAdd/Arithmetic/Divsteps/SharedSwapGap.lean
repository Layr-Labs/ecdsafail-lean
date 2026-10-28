import ECDSAAdd.Arithmetic.Divsteps.SharedSwapWalk
import ECDSAAdd.Framework.MeasuredLocality

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- Recovery only needs its three operands and the pending phase. Every other
basis bit may have changed during the gap. The recovered state retains those
changes, rather than asserting a full-state identity. -/
theorem deferredSwap_frame_gap (active low output : Wire)
    (ha : active≠output) (hl : low≠output) (gap : RecordedProgram)
    (m : List Bool) (ordinal : Nat) (s : State)
    (hs : s.basis output=(s.basis active && s.basis low))
    (hphase : (runWithTape gap m (ordinal+1)
      (runWithTape (forgetBranch output) m ordinal s)).phase=
      (runWithTape (forgetBranch output) m ordinal s).phase)
    (hbits : ∀ q∈[active,low,output],
      (runWithTape gap m (ordinal+1)
        (runWithTape (forgetBranch output) m ordinal s)).basis q=
        (runWithTape (forgetBranch output) m ordinal s).basis q) :
    runWithTape (forgetBranch output ++ gap ++
      recoverBranch (decodeSwap active low output) output ordinal) m ordinal s=
      ⟨s.phase,writeBit (runWithTape gap m (ordinal+1)
        (runWithTape (forgetBranch output) m ordinal s)).basis output (s.basis output)⟩ := by
  apply deferredPair_correct
  · simpa only [forgetBranch_run] using hphase
  · rw [decodeSwap_run]
    have hactive := hbits active (by simp)
    have hlow := hbits low (by simp)
    have hout := hbits output (by simp)
    have hactive := hactive.trans (show (runWithTape (forgetBranch output) m ordinal s).basis active=s.basis active by
      simp [forgetBranch_run,writeBit,ha])
    have hlow := hlow.trans (show (runWithTape (forgetBranch output) m ordinal s).basis low=s.basis low by
      simp [forgetBranch_run,writeBit,hl])
    have hout := hout.trans (show (runWithTape (forgetBranch output) m ordinal s).basis output=false by
      simp [forgetBranch_run,writeBit])
    rw [hactive,hlow,hout,←hs]
    simp

/-- A single actual step around an output-changing recorded gap. The swap
wire is measured, reused by the gap, recovered from its original record,
then cleared by the constructive inverse. -/
def StepLayout.swapAround (L : StepLayout) (gap : RecordedProgram) (cursor : Nat) : RecordedProgram :=
  embedRecorded L.program ++
    (forgetBranch L.history.swap ++ gap ++
      recoverBranch L.swapDecoder L.history.swap (cursor+measurementCount L.program)) ++
    embedRecorded L.undo

/-- The gap may update any designated output wires disjoint from the step.
It must restore all other bits and its input phase. This theorem proves that
actual recovery and measured inverse preserve its outputs while restoring
the entire step, including every history and arithmetic work bit. -/
theorem StepLayout.swapAround_run (L : StepLayout) (h : L.Valid)
    (p : Int) (st : ZState) (hi : Inv p st) (hp : p%2=1) (hfit : L.Fits st)
    (O : List Wire) (hsep : List.Disjoint O L.used) (gap : RecordedProgram)
    (s : State) (m : List Bool) (cursor : Nat) (hs : L.Ready st s.basis)
    (hphase : (runWithTape gap m (cursor+measurementCount L.program+1)
      (runWithTape (forgetBranch L.history.swap) m (cursor+measurementCount L.program)
        (run L.program (m.drop cursor) s))).phase=
      (runWithTape (forgetBranch L.history.swap) m (cursor+measurementCount L.program)
        (run L.program (m.drop cursor) s)).phase)
    (hframe : ∀ q, q∉O →
      (runWithTape gap m (cursor+measurementCount L.program+1)
        (runWithTape (forgetBranch L.history.swap) m (cursor+measurementCount L.program)
          (run L.program (m.drop cursor) s))).basis q=
      (runWithTape (forgetBranch L.history.swap) m (cursor+measurementCount L.program)
        (run L.program (m.drop cursor) s)).basis q) :
    let v := runWithTape gap m (cursor+measurementCount L.program+1)
      (runWithTape (forgetBranch L.history.swap) m (cursor+measurementCount L.program)
        (run L.program (m.drop cursor) s))
    let out := runWithTape (L.swapAround gap cursor) m cursor s
    out.phase=s.phase ∧ (∀ q, q∉O → out.basis q=s.basis q) ∧
      ∀ q∈O,out.basis q=v.basis q := by
  let t := run L.program (m.drop cursor) s
  let ordinal := cursor+measurementCount L.program
  let u := runWithTape (forgetBranch L.history.swap) m ordinal t
  let v := runWithTape gap m (ordinal+1) u
  let w : State := ⟨t.phase,writeBit v.basis L.history.swap (t.basis L.history.swap)⟩
  have hq : L.history.swap∈L.used := by simp [used,histories,StepHistory.wires]
  have away (q : Wire) (hq : q∈L.used) : q∉O :=
    fun ho => List.disjoint_left.mp hsep ho hq
  obtain ⟨ha,hl⟩ := L.swapDecoder_distinct h
  have hv := L.swapDecoder_after h p st hi hp hfit s (m.drop cursor) hs
  have hpair := deferredSwap_frame_gap L.history.active L.fv.second L.history.swap
    ha hl gap m ordinal t hv hphase (by
      intro q hmem
      apply hframe q (away q ?_)
      have hfv := L.fv.second_mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      simp only [used,data,histories,StepHistory.wires,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false]
      rcases hmem with rfl|rfl|rfl <;> tauto)
  have hw : ∀ q, q∉O → w.basis q=t.basis q := by
    intro q ho
    change writeBit v.basis L.history.swap (t.basis L.history.swap) q=t.basis q
    by_cases he : q=L.history.swap
    · simp [writeBit,Function.update,he]
    · have hf : v.basis q=u.basis q := hframe q ho
      rw [show writeBit v.basis L.history.swap (t.basis L.history.swap) q=v.basis q by
        simp [writeBit,he],hf]
      simp [u,forgetBranch_run,writeBit,he]
  have hlocal (mi : List Bool) := run_measured_locality L.undo L.used.toFinset
    (L.undo_support h) w t mi rfl (fun q hq => hw q (away q (List.mem_toFinset.mp hq)))
  have hrestore (mi : List Bool) :
      (run L.undo mi w).phase=s.phase ∧ (∀ q, q∉O → (run L.undo mi w).basis q=s.basis q) ∧
      ∀ q∈O,(run L.undo mi w).basis q=v.basis q := by
    have hi := L.undo_after h st hfit s (m.drop cursor) mi hs.1 hs.2.1 hs.2.2.1
    have hh := hlocal mi
    change run L.undo mi t=s at hi
    rw [hi] at hh
    refine ⟨hh.1,?_,?_⟩
    · intro q ho
      by_cases hq : q∈L.used.toFinset
      · exact hh.2 q hq
      · exact (run_preserves_outside _ _ _ q (fun hm => hq (L.undo_support h hm))).trans
          ((hw q ho).trans (run_preserves_outside _ _ _ q (fun hm => hq (L.program_support h hm))))
    · intro q ho
      rw [run_preserves_outside _ _ _ q (fun hm =>
        List.disjoint_left.mp hsep ho (List.mem_toFinset.mp (L.undo_support h hm)))]
      have he : q≠L.history.swap := fun he => away _ hq (he ▸ ho)
      simp [w,writeBit,he]
  dsimp only
  rw [swapAround,runWithTape_append,runWithTape_append,runWithTape_embedRecorded]
  simp only [(embedRecorded_counts _).2,runWithTape_embedRecorded]
  change runWithTape (forgetBranch L.history.swap ++ gap ++
    recoverBranch L.swapDecoder L.history.swap ordinal) m ordinal t=w at hpair
  rw [hpair]
  exact hrestore _

theorem StepLayout.swapAround_wellFormed (L : StepLayout) (gap : RecordedProgram) (cursor : Nat)
    (hg : RecordedWellFormedAt (cursor+measurementCount L.program+1) gap) :
    RecordedWellFormedAt cursor (L.swapAround gap cursor) := by
  rw [swapAround,RecordedWellFormedAt_append]
  refine ⟨?_,embedRecorded_wellFormed _ _⟩
  rw [RecordedWellFormedAt_append]
  refine ⟨embedRecorded_wellFormed _ _,?_⟩
  rw [(embedRecorded_counts _).2]
  exact deferredPair_wellFormed _ _ _ _ hg

theorem StepLayout.swapAround_counts (L : StepLayout) (h : L.Valid)
    (n v k : Nat) (hw : L.Sized n v k) (gap : RecordedProgram) (cursor : Nat) :
    recordedToffoliCount (L.swapAround gap cursor)=2*(5*n+5*v+k-4)+1+recordedToffoliCount gap ∧
    recordedMeasurementCount (L.swapAround gap cursor)=2*(4*n+3*v+k-5)+1+recordedMeasurementCount gap := by
  have hf := L.program_counts h n v k hw
  have hr := L.undo_counts h n v k hw
  simp only [swapAround,recordedToffoliCount_append,recordedMeasurementCount_append,
    (embedRecorded_counts _).1,(embedRecorded_counts _).2,
    (forgetBranch_resources _).1,(forgetBranch_resources _).2.1,
    (recoverBranch_resources _ _ _).1,(recoverBranch_resources _ _ _).2.1,
    swapDecoder,(decodeSwap_resources _ _ _).1,(decodeSwap_resources _ _ _).2.1,
    hf.1,hf.2,hr.1,hr.2]
  constructor <;> ring

theorem StepLayout.swapAround_support (L : StepLayout) (h : L.Valid)
    (gap : RecordedProgram) (cursor : Nat) :
    recordedWires (L.swapAround gap cursor)⊆L.used.toFinset ∪ recordedWires gap := by
  have hf := L.program_support h
  have hr := L.undo_support h
  have hd := L.swapRecovery_support h (cursor+measurementCount L.program)
  have hq : {L.history.swap}⊆L.used.toFinset := by
    intro q hq
    simp only [Finset.mem_singleton] at hq
    subst q
    simp [used,histories,StepHistory.wires]
  simp only [swapAround,recordedWires_append,embedRecorded_wires,
    (forgetBranch_resources _).2.2,Finset.union_subset_iff]
  exact ⟨⟨hf.trans Finset.subset_union_left,
    ⟨⟨hq.trans Finset.subset_union_left,Finset.subset_union_right⟩,
      hd.trans Finset.subset_union_left⟩⟩,hr.trans Finset.subset_union_left⟩

end ECDSAAdd.Arithmetic.Divsteps
