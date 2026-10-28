import ECDSAAdd.Arithmetic.Divsteps.PhysicalWalk
import ECDSAAdd.Arithmetic.Divsteps.SwapDecoder
import ECDSAAdd.Arithmetic.Divsteps.DeferredDecoder

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- The physical bit of weight two, including the two-bit signed-row case. -/
def StepRow.second (r : StepRow) : Wire :=
  match r.middle with
  | [] => r.sign
  | a::_ => a

private theorem second_bit_read (low second : Wire) (tail : List Wire) (s : BasisState) :
    s second=decide (bitk (signedRegValue (low::second::tail) s) 1=1) := by
  have hd := signedRegValue_cons low (second::tail) s (by simp)
  have he := signedRegValue_even_iff second tail s
  unfold bitk
  norm_num only [Nat.reduceAdd,pow_one,Int.reducePow]
  cases hlow : s low <;> cases hsecond : s second <;>
    simp only [hlow,hsecond,Bool.toNat_false,Bool.toNat_true,Nat.cast_zero,Nat.cast_one] at hd he ⊢ <;>
    simp_all <;> omega

theorem StepRow.second_bit (r : StepRow) (s : BasisState) :
    s r.second=decide (bitk (signedRegValue r.wires s) 1=1) := by
  cases r with
  | mk low mid sign =>
    cases mid with
    | nil => exact second_bit_read low sign [] s
    | cons a rest => exact second_bit_read low a (rest++[sign]) s

theorem StepRow.second_mem (r : StepRow) : r.second∈r.wires := by
  cases r with
  | mk low mid sign => cases mid <;> simp [second,wires]

/-- Swap reconstruction is valid for frozen as well as active reachable slots. -/
theorem slot_swap_bit (p : Int) (st : ZState) (h : Inv p st) (hp : p%2=1) :
    swapControl st=(activeControl st && decide (bitk (zSlot st).fv 1=1)) := by
  by_cases hg : st.g=0
  · simp [swapControl,activeControl,zSlot,hg]
  · simpa [swapControl,activeControl,zSlot,hg] using swap_bit_law p st h hp

/-- One Toffoli reconstructs the actual retained swap value from updated fv. -/
def StepLayout.swapDecoder (L : StepLayout) : Program :=
  decodeSwap L.history.active L.fv.second L.history.swap

theorem StepLayout.swapDecoder_after (L : StepLayout) (h : L.Valid) (p : Int) (st : ZState)
    (hi : Inv p st) (hp : p%2=1) (hfit : L.Fits st)
    (s : State) (m : List Bool) (hs : L.Ready st s.basis) :
    let t := run L.program m s
    t.basis L.history.swap=(t.basis L.history.active && t.basis L.fv.second) := by
  obtain ⟨_,he,_,ha,_,hq⟩ := L.program_zSlot_controls h st hfit s m hs.1 hs.2.1 hs.2.2.1
  have hfv := he.2.2.1
  rw [L.next_static.2.1] at hfv
  dsimp only
  rw [ha,hq,L.fv.second_bit (run L.program m s).basis,hfv]
  exact slot_swap_bit p st hi hp

/-- Reconstruct and correct exactly the state before measurement, using the
original absolute outcome even when the reverse cursor has advanced. -/
theorem recoverSwap_forget (active low output : Wire) (ha : active≠output) (hl : low≠output)
    (m : List Bool) (ordinal cursor : Nat) (s : State)
    (hs : s.basis output=(s.basis active && s.basis low)) :
    runWithTape (recoverBranch (decodeSwap active low output) output ordinal) m cursor
      (runWithTape (forgetBranch output) m ordinal s)=s := by
  rw [forgetBranch_run]
  have hd : run (decodeSwap active low output) (m.drop cursor)
      ⟨s.phase ^^ (m.getD ordinal false && s.basis output),writeBit s.basis output false⟩ =
      ⟨s.phase ^^ (m.getD ordinal false && s.basis output),
        writeBit (writeBit s.basis output false) output (s.basis output)⟩ := by
    rw [decodeSwap_run]
    simp [writeBit,ha,hl,hs]
  rw [recoverBranch_cancel _ _ _ _ _ _ _ s.phase rfl hd]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=output <;> simp [writeBit,hw]

/-- Identity gaps may contain measured arithmetic and consume arbitrary tape
lengths. The recovery still uses the old outcome, not the current cursor. -/
theorem deferredSwap_identity_gap (active low output : Wire)
    (ha : active≠output) (hl : low≠output) (gap : Program)
    (m : List Bool) (ordinal : Nat) (s : State)
    (hs : s.basis output=(s.basis active && s.basis low))
    (hgap : run gap (m.drop (ordinal+1))
      (runWithTape (forgetBranch output) m ordinal s)=
      runWithTape (forgetBranch output) m ordinal s) :
    runWithTape (forgetBranch output ++ embedRecorded gap ++
      recoverBranch (decodeSwap active low output) output ordinal) m ordinal s=s := by
  simp only [runWithTape_append,runWithTape_embedRecorded,recordedMeasurementCount_append]
  simp only [forgetBranch,recordedMeasurementCount,measurementCount,Nat.add_zero] at *
  rw [hgap]
  exact recoverSwap_forget active low output ha hl m ordinal _ s hs

/-- Ready deliberately imposes no values on past controls. Measuring one past
wire cannot invalidate the next step's arithmetic or freshness conditions. -/
theorem StepLayout.ready_write_past (L : StepLayout) (h : L.Valid)
    (st : ZState) (s : BasisState) (w : Wire) (b : Bool)
    (hw : w∈L.past.flatMap StepHistory.wires) (hs : L.Ready st s) :
    L.Ready st (writeBit s w b) := by
  have hp : 0<List.count w (L.past.flatMap StepHistory.wires) := List.count_pos_iff.mpr hw
  have hn := List.nodup_iff_count.mp h.unique w
  have away (u : Wire)
      (hu : u∈L.data++L.work++L.history.wires++L.future.flatMap StepHistory.wires) : u≠w := by
    intro he
    subst u
    have hc := List.count_pos_iff.mpr hu
    simp only [used,histories,List.count_append] at hn hc
    omega
  have keep (u : Wire)
      (hu : u∈L.data++L.work++L.history.wires++L.future.flatMap StepHistory.wires) :
      writeBit s w b u=s u := by simp [writeBit,away u hu]
  have val (xs : List Wire) (hx : xs⊆L.data) :
      signedRegValue xs (writeBit s w b)=signedRegValue xs s := by
    apply (signedRegValue_eq_iff _ _ _).mpr
    intro u hu
    exact keep u (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (hx hu))))
  refine ⟨?_,?_,?_,?_⟩
  · rcases hs.1 with ⟨hf,hg,hfv,hgv,hz⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    all_goals
      rw [val _ (by intro u hu; simp only [data,List.mem_append]; tauto)]
      assumption
  · intro u hu
    exact (keep u (by simp only [List.mem_append]; tauto)).trans (hs.2.1 u hu)
  · intro u hu
    exact (keep u (by simp only [List.mem_append]; tauto)).trans (hs.2.2.1 u hu)
  · intro u hu
    exact (keep u (by simp only [List.mem_append]; tauto)).trans (hs.2.2.2 u hu)

theorem StepLayout.current_in_next_past (L : StepLayout) (hne : L.future≠[]) :
    L.history.swap∈L.next.past.flatMap StepHistory.wires := by
  cases he : L.future with
  | nil => exact (hne he).elim
  | cons a rest => simp [next,nextHistory,halfView,he,StepHistory.wires]

/-- Actual later steps and their constructive inverses, retaining other history. -/
def StepLayout.swapGap (L : StepLayout) (n : Nat) : Program :=
  forwardWalk (fun i => (L.at i).program) 1 n ++
    inverseWalk (fun i => (L.at i).undo) 1 n

/-- Measure the first swap after its last forward use. Its correction references
that absolute outcome after the entire later walk has returned. -/
def StepLayout.deferredSwapRoundTrip (L : StepLayout) (n cursor : Nat) : RecordedProgram :=
  embedRecorded L.program ++
    (forgetBranch L.history.swap ++ embedRecorded (L.swapGap n) ++
      recoverBranch L.swapDecoder L.history.swap (cursor+measurementCount L.program)) ++
    embedRecorded L.undo

theorem StepLayout.swapDecoder_distinct (L : StepLayout) (h : L.Valid) :
    L.history.active≠L.history.swap ∧ L.fv.second≠L.history.swap := by
  constructor
  · have hh := (L.control_routing_nodup h).1
    intro he
    simp [he] at hh
  · intro he
    have hh := L.fv.second_mem
    rw [he] at hh
    have hq : L.history.swap∈[L.history.active,L.history.parity,L.history.swap] := by simp
    apply List.disjoint_left.mp (L.tags_away h) hq
    simp only [List.mem_append]
    tauto

/-- One deferred swap now crosses a concrete suffix walk, not an assumed
phase-neutral gap. Other history remains coherent in this baseline. -/
theorem StepLayout.deferredSwapRoundTrip_correct (L : StepLayout) (h : L.Valid)
    (p x : Int) (hp : p%2=1) (n : Nat) (hhistory : n+1≤L.future.length)
    (hfit : ∀ i, i<n+1 → (L.at i).Fits (zWalk p x i))
    (s : State) (m : List Bool) (cursor : Nat) (hs : L.Ready (zSeed p x) s.basis) :
    runWithTape (L.deferredSwapRoundTrip n cursor) m cursor s=s := by
  let t := run L.program (m.drop cursor) s
  let ordinal := cursor+measurementCount L.program
  let u := runWithTape (forgetBranch L.history.swap) m ordinal t
  have hne : L.future≠[] := L.at_can_advance 0 (by omega)
  have ht : L.next.Ready (zWalk p x 1) t.basis :=
    (L.program_spec h (zSeed p x) (hfit 0 (by omega)) hne s (m.drop cursor) hs).2
  have hu : (L.at 1).Ready (zWalk p x 1) u.basis := by
    rw [show u=runWithTape (forgetBranch L.history.swap) m ordinal t from rfl,
      forgetBranch_run]
    exact L.next.ready_write_past (L.next_valid h) (zWalk p x 1) t.basis
      L.history.swap false (L.current_in_next_past hne) ht
  have hstep : ∀ i, i<n+1 → Triple ((L.at i).Ready (zWalk p x i))
      (L.at i).program ((L.at (i+1)).Ready (zWalk p x (i+1))) := by
    intro i hi
    exact (L.at i).program_spec (L.at_valid h i) (zWalk p x i) (hfit i hi)
      (L.at_can_advance i (by omega))
  have hundo : ∀ i, i<n+1 → ∀ t ma mb, (L.at i).Ready (zWalk p x i) t.basis →
      run (L.at i).undo mb (run (L.at i).program ma t)=t := by
    intro i hi t ma mb ht
    exact (L.at i).undo_after (L.at_valid h i) (zWalk p x i) (hfit i hi)
      t ma mb ht.1 ht.2.1 ht.2.2.1
  have hg : run (L.swapGap n) (m.drop (ordinal+1)) u=u :=
    ECDSAAdd.Arithmetic.Divsteps.walk_roundTrip _ _ (fun i => (L.at i).Ready (zWalk p x i)) (n+1)
      hstep hundo 1 n (by omega) u _ hu
  obtain ⟨ha,hl⟩ := L.swapDecoder_distinct h
  have hvalue : t.basis L.history.swap=(t.basis L.history.active && t.basis L.fv.second) :=
    L.swapDecoder_after h p (zSeed p x) (invariant_zWalk hp x 0) hp
      (hfit 0 (by omega)) s (m.drop cursor) hs
  have hpair := deferredSwap_identity_gap L.history.active L.fv.second L.history.swap
    ha hl (L.swapGap n) m ordinal t hvalue hg
  rw [deferredSwapRoundTrip,runWithTape_append,runWithTape_append,runWithTape_embedRecorded]
  simp only [(embedRecorded_counts L.program).2]
  simp only [runWithTape_embedRecorded]
  simp only [t,ordinal] at hpair
  simp only [swapDecoder]
  rw [hpair]
  exact L.undo_after h (zSeed p x) (hfit 0 (by omega)) s (m.drop cursor) _ hs.1 hs.2.1 hs.2.2.1

theorem StepLayout.deferredSwapRoundTrip_wellFormed (L : StepLayout) (n cursor : Nat) :
    RecordedWellFormedAt cursor (L.deferredSwapRoundTrip n cursor) := by
  rw [deferredSwapRoundTrip,RecordedWellFormedAt_append]
  refine ⟨?_,embedRecorded_wellFormed _ _⟩
  rw [RecordedWellFormedAt_append]
  refine ⟨embedRecorded_wellFormed _ _,?_⟩
  rw [(embedRecorded_counts L.program).2]
  exact deferredPair_wellFormed _ _ _ _ (embedRecorded_wellFormed _ _)

theorem StepLayout.deferredSwapRoundTrip_counts (L : StepLayout) (h : L.Valid)
    (n v k slots cursor : Nat) (hw : L.Sized n v k) :
    recordedToffoliCount (L.deferredSwapRoundTrip slots cursor)=
      2*(slots+1)*(5*n+5*v+k-4)+1 ∧
    recordedMeasurementCount (L.deferredSwapRoundTrip slots cursor)=
      2*(slots+1)*(4*n+3*v+k-5)+1 := by
  have hf := L.program_counts h n v k hw
  have hr := L.undo_counts h n v k hw
  have hfg := forwardWalk_counts (fun i => (L.at i).program) _ _ (slots+1)
    (fun i _ => (L.at i).program_counts (L.at_valid h i) n v k (L.at_sized n v k hw i))
    1 slots (by omega)
  have hrg := inverseWalk_counts (fun i => (L.at i).undo) _ _ (slots+1)
    (fun i _ => (L.at i).undo_counts (L.at_valid h i) n v k (L.at_sized n v k hw i))
    1 slots (by omega)
  simp only [deferredSwapRoundTrip,recordedToffoliCount_append,recordedMeasurementCount_append,
    (embedRecorded_counts _).1,(embedRecorded_counts _).2,
    (forgetBranch_resources _).1,(forgetBranch_resources _).2.1,
    (recoverBranch_resources _ _ _).1,(recoverBranch_resources _ _ _).2.1,
    swapGap,toffoliCount_append,measurementCount_append,hf.1,hf.2,hr.1,hr.2,
    hfg.1,hfg.2,hrg.1,hrg.2,swapDecoder,
    (decodeSwap_resources _ _ _).1,(decodeSwap_resources _ _ _).2.1]
  constructor <;> ring

theorem StepLayout.swapGap_support (L : StepLayout) (h : L.Valid) (slots : Nat) :
    wires (L.swapGap slots)⊆L.used.toFinset := by
  rw [swapGap,wires_append,Finset.union_subset_iff]
  constructor
  · apply forwardWalk_wires_subset _ _ (slots+1) ?_ 1 slots (by omega)
    intro i _
    rw [←L.at_support i]
    exact (L.at i).program_support (L.at_valid h i)
  · apply inverseWalk_wires_subset _ _ (slots+1) ?_ 1 slots (by omega)
    intro i _
    rw [←L.at_support i]
    exact (L.at i).undo_support (L.at_valid h i)

theorem StepLayout.deferredSwapRoundTrip_support (L : StepLayout) (h : L.Valid)
    (slots cursor : Nat) : recordedWires (L.deferredSwapRoundTrip slots cursor)⊆L.used.toFinset := by
  have ht : {L.history.active,L.fv.second,L.history.swap}⊆L.used.toFinset := by
    intro w hw
    have hf := L.fv.second_mem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    simp only [List.mem_toFinset,used,data,work,histories,StepHistory.wires,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    rcases hw with rfl|rfl|rfl <;> tauto
  have hq : {L.history.swap}⊆L.used.toFinset := by
    intro w hw
    apply ht
    simp_all
  simp only [deferredSwapRoundTrip,recordedWires_append,embedRecorded_wires,
    (forgetBranch_resources _).2.2,(recoverBranch_resources _ _ _).2.2.1,
    swapDecoder,(decodeSwap_resources _ _ _).2.2,Finset.union_subset_iff]
  exact ⟨⟨L.program_support h,⟨⟨hq,L.swapGap_support h slots⟩,ht,hq⟩⟩,L.undo_support h⟩

theorem deferredSwap_recorded_gap (active low output : Wire)
    (ha : active≠output) (hl : low≠output) (gap : RecordedProgram)
    (m : List Bool) (ordinal : Nat) (s : State)
    (hs : s.basis output=(s.basis active && s.basis low))
    (hgap : runWithTape gap m (ordinal+1)
      (runWithTape (forgetBranch output) m ordinal s)=
      runWithTape (forgetBranch output) m ordinal s) :
    runWithTape (forgetBranch output ++ gap ++
      recoverBranch (decodeSwap active low output) output ordinal) m ordinal s=s := by
  simp only [runWithTape_append,recordedMeasurementCount_append]
  simp only [forgetBranch,recordedMeasurementCount,measurementCount,Nat.add_zero] at *
  rw [hgap]
  exact recoverSwap_forget active low output ha hl m ordinal _ s hs

theorem StepLayout.swapRecovery_support (L : StepLayout) (_h : L.Valid) (ordinal : Nat) :
    recordedWires (recoverBranch L.swapDecoder L.history.swap ordinal)⊆L.used.toFinset := by
  rw [(recoverBranch_resources _ _ _).2.2.1]
  rw [swapDecoder,(decodeSwap_resources _ _ _).2.2]
  intro w hw
  have hf := L.fv.second_mem
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hw
  simp only [List.mem_toFinset,used,data,work,histories,StepHistory.wires,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hw with (rfl|rfl|rfl)|rfl <;> tauto

end ECDSAAdd.Arithmetic.Divsteps
