import ECDSAAdd.Arithmetic.Divsteps.SharedSwapLayout

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- Current local controls and all still-unused retained controls are clean.
Unused swap addresses have no freshness requirement. -/
def StepLayout.SharedReady (L : StepLayout) (i : Nat) (st : ZState) (s : BasisState) : Prop :=
  (L.sharedAt i).Encodes st s ∧ (L.sharedAt i).Clean s ∧ (L.sharedAt i).Fresh s ∧
  ∀ w∈(L.at i).future.flatMap StepHistory.retained,s w=false

private theorem future_retained_mem (L : StepLayout) (i : Nat) (w : Wire)
    (hw : w∈(L.at i).future.flatMap StepHistory.retained) :
    w∈(L.history::L.future).flatMap StepHistory.retained := by
  obtain ⟨a,ha,hwa⟩ := List.mem_flatMap.mp hw
  exact List.mem_flatMap.mpr ⟨a,List.mem_cons_of_mem _ ((L.at_history_mem i).2 ha),hwa⟩

private theorem future_retained_wire (hs : List StepHistory) (w : Wire)
    (hw : w∈hs.flatMap StepHistory.retained) : w∈hs.flatMap StepHistory.wires := by
  obtain ⟨a,ha,hwa⟩ := List.mem_flatMap.mp hw
  exact List.mem_flatMap.mpr ⟨a,ha,by simpa [StepHistory.retained,StepHistory.wires] using
    (show w=a.active ∨ w=a.parity ∨ w=a.swap from by
      simp only [StepHistory.retained,List.mem_cons] at hwa; tauto)⟩

theorem StepLayout.shared_future_away (L : StepLayout) (h : L.Valid) (i : Nat) (w : Wire)
    (hw : w∈(L.at i).future.flatMap StepHistory.retained) : w∉(L.sharedAt i).used := by
  have hf := future_retained_wire _ w hw
  have hn := (L.at_valid h i).unique
  have hq : w≠L.history.swap := by
    have hh := L.sharedUsed_nodup h
    simp only [sharedUsed,List.nodup_append,List.nodup_cons] at hh
    intro he
    subst w
    exact hh.2.1.1 (future_retained_mem L i _ hw)
  have hc : List.Disjoint ((L.at i).data++(L.at i).work++(L.at i).history.wires)
      ((L.at i).future.flatMap StepHistory.wires) := by
    have hn' : (((L.at i).data++(L.at i).work++(L.at i).history.wires) ++
        ((L.at i).past.flatMap StepHistory.wires++(L.at i).future.flatMap StepHistory.wires)).Nodup := by
      simpa only [used,histories,List.append_assoc] using hn
    exact (List.disjoint_append_right.mp (List.nodup_append'.mp hn').2.2).2
  intro hu
  apply List.disjoint_left.mp hc _ hf
  simp only [sharedAt,used,data,work,histories,StepHistory.wires,List.flatMap_nil,
    List.append_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hu
  simp only [data,work,StepHistory.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  tauto

theorem StepLayout.shared_future_frame (L : StepLayout) (h : L.Valid) (i : Nat)
    (s : State) (m : List Bool) (w : Wire)
    (hw : w∈(L.at i).future.flatMap StepHistory.retained) :
    (run (L.sharedAt i).program m s).basis w=s.basis w := by
  apply run_preserves_outside
  intro hm
  exact L.shared_future_away h i w hw
    (List.mem_toFinset.mp ((L.sharedAt i).program_support (L.sharedAt_valid h i) hm))

/-- Forgetting the shared swap changes no data or reusable arithmetic work. -/
theorem StepLayout.write_swap_data_clean (L : StepLayout) (h : L.Valid)
    (st : ZState) (s : BasisState) (he : L.Encodes st s) (hc : L.Clean s) (b : Bool) :
    L.Encodes st (writeBit s L.history.swap b) ∧ L.Clean (writeBit s L.history.swap b) := by
  have away (u : Wire) (hu : u∈L.data++L.work) : u≠L.history.swap := by
    have hh := h.unique
    have hn := (List.nodup_append'.mp hh).2.2
    intro eq
    subst u
    exact List.disjoint_left.mp hn hu (by simp [histories,StepHistory.wires])
  have keep (u : Wire) (hu : u∈L.data++L.work) :
      writeBit s L.history.swap b u=s u := by simp [writeBit,away u hu]
  have val (xs : List Wire) (hx : xs⊆L.data) :
      signedRegValue xs (writeBit s L.history.swap b)=signedRegValue xs s := by
    apply (signedRegValue_eq_iff _ _ _).mpr
    intro u hu
    exact keep u (List.mem_append_left _ (hx hu))
  constructor
  · rcases he with ⟨hf,hg,hfv,hgv,hz⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    all_goals
      rw [val _ (by intro u hu; simp only [data,List.mem_append]; tauto)]
      assumption
  · intro u hu
    exact (keep u (List.mem_append_right _ hu)).trans (hc u hu)


/-- The same physical swap is zero again before selecting the next step. -/
theorem StepLayout.shared_step (L : StepLayout) (h : L.Valid) (i : Nat)
    (hne : (L.at i).future≠[]) (st : ZState) (hfit : (L.sharedAt i).Fits st)
    (s : State) (m mr : List Bool) (ordinal : Nat) (hs : L.SharedReady i st s.basis) :
    L.SharedReady (i+1) (zSlot st)
      (runWithTape (forgetBranch L.history.swap) mr ordinal
        (run (L.sharedAt i).program m s)).basis := by
  let A := L.sharedAt i
  let t := run A.program m s
  have hA := L.sharedAt_valid h i
  have ht := A.program_zSlot_controls hA st hfit s m hs.1 hs.2.1 hs.2.2.1
  have hec := A.next.write_swap_data_clean (A.next_valid hA) (zSlot st) t.basis
    ht.2.1 ht.2.2.1 false
  have hq : A.next.history.swap=L.history.swap := rfl
  rw [hq] at hec
  have hf (w : Wire) (hw : w∈(L.at i).future.flatMap StepHistory.retained) :
      writeBit t.basis L.history.swap false w=false := by
    have hneq : w≠L.history.swap := by
      intro he
      apply L.shared_future_away h i w hw
      simp [sharedAt,used,histories,StepHistory.wires,he]
    rw [show writeBit t.basis L.history.swap false w=t.basis w by simp [writeBit,hneq]]
    exact (L.shared_future_frame h i s m w hw).trans (hs.2.2.2 w hw)
  rw [forgetBranch_run]
  cases he : (L.at i).future with
  | nil => exact (hne he).elim
  | cons a rest =>
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [A,sharedAt,StepLayout.at,next,nextHistory,halfView,he,Encodes] using hec.1
    · simpa only [A,sharedAt,StepLayout.at,next,nextHistory,halfView,he,Clean,work] using hec.2
    · simp only [sharedAt,StepLayout.at,next,nextHistory,halfView,he,Fresh,StepHistory.wires,
        List.mem_cons,List.not_mem_nil,or_false]
      intro w hw
      rcases hw with rfl | rfl | rfl
      · exact hf _ (by simp [he,StepHistory.retained])
      · exact hf _ (by simp [he,StepHistory.retained])
      · simp [writeBit]
    · simp only [StepLayout.at,next,nextHistory,halfView,he]
      intro w hw
      exact hf w (by simp only [he,List.flatMap_cons,List.mem_append]; exact Or.inr hw)


/-- Nested actual forward/reverse schedule. Every swap wire is measured after
its forward step, reconstructed from restored endpoint data on the reverse
pass, and phase-corrected using its own original absolute tape ordinal. -/
def StepLayout.sharedSwaps (L : StepLayout) (start : Nat) : Nat → Nat → RecordedProgram
  | 0, _ => []
  | n+1, cursor =>
    let A := L.sharedAt start
    embedRecorded A.program ++
      (forgetBranch A.history.swap ++
        L.sharedSwaps (start+1) n (cursor+measurementCount A.program+1) ++
        recoverBranch A.swapDecoder A.history.swap (cursor+measurementCount A.program)) ++
      embedRecorded A.undo

/-- All swaps are genuinely measured, including those in the intervening
schedule. No phase contract for an abstract gap is assumed. -/
theorem StepLayout.sharedSwaps_correct (L : StepLayout) (h : L.Valid)
    (p x : Int) (hp : p%2=1) (limit : Nat) (hhistory : limit≤L.future.length)
    (hfit : ∀ i, i<limit → (L.at i).Fits (zWalk p x i))
    (start n : Nat) (hrange : start+n≤limit) (s : State) (m : List Bool) (cursor : Nat)
    (hs : L.SharedReady start (zWalk p x start) s.basis) :
    runWithTape (L.sharedSwaps start n cursor) m cursor s=s := by
  induction n generalizing start s cursor with
  | zero => rfl
  | succ n ih =>
    let A := L.sharedAt start
    let t := run A.program (m.drop cursor) s
    let ordinal := cursor+measurementCount A.program
    let u := runWithTape (forgetBranch A.history.swap) m ordinal t
    have hA := L.sharedAt_valid h start
    have hne := L.at_can_advance start (show start<L.future.length by omega)
    have hu : L.SharedReady (start+1) (zWalk p x (start+1)) u.basis :=
      L.shared_step h start hne (zWalk p x start) (hfit start (by omega))
        s (m.drop cursor) m ordinal hs
    have hg := ih (start+1) (by omega) u (ordinal+1) hu
    obtain ⟨ha,hl⟩ := A.swapDecoder_distinct hA
    have hready : A.Ready (zWalk p x start) s.basis :=
      ⟨hs.1,hs.2.1,hs.2.2.1,by simp [FutureClean,A,sharedAt]⟩
    have hv := A.swapDecoder_after hA p (zWalk p x start) (invariant_zWalk hp x start) hp
      (hfit start (by omega)) s (m.drop cursor) hready
    have hpair := deferredSwap_recorded_gap A.history.active A.fv.second A.history.swap ha hl
      (L.sharedSwaps (start+1) n (ordinal+1)) m ordinal t hv hg
    rw [sharedSwaps,runWithTape_append,runWithTape_append,runWithTape_embedRecorded]
    simp only [(embedRecorded_counts _).2,runWithTape_embedRecorded]
    simp only [A,t,ordinal] at hpair
    simp only [swapDecoder]
    rw [hpair]
    exact A.undo_after hA (zWalk p x start) (hfit start (by omega)) s (m.drop cursor) _
      hs.1 hs.2.1 hs.2.2.1

theorem StepLayout.sharedSwaps_wellFormed (L : StepLayout) (start n cursor : Nat) :
    RecordedWellFormedAt cursor (L.sharedSwaps start n cursor) := by
  induction n generalizing start cursor with
  | zero => trivial
  | succ n ih =>
    rw [sharedSwaps,RecordedWellFormedAt_append]
    refine ⟨?_,embedRecorded_wellFormed _ _⟩
    rw [RecordedWellFormedAt_append]
    refine ⟨embedRecorded_wellFormed _ _,?_⟩
    rw [(embedRecorded_counts _).2]
    exact deferredPair_wellFormed _ _ _ _ (ih (start+1) _)

theorem StepLayout.sharedSwaps_counts (L : StepLayout) (h : L.Valid)
    (n v k : Nat) (hw : L.Sized n v k) (start slots cursor : Nat) :
    recordedToffoliCount (L.sharedSwaps start slots cursor)=slots*(2*(5*n+5*v+k-4)+1) ∧
    recordedMeasurementCount (L.sharedSwaps start slots cursor)=slots*(2*(4*n+3*v+k-5)+1) := by
  induction slots generalizing start cursor with
  | zero => simp [sharedSwaps,recordedToffoliCount,recordedMeasurementCount]
  | succ slots ih =>
    have hf := (L.sharedAt start).program_counts (L.sharedAt_valid h start) n v k (L.sharedAt_sized n v k hw start)
    have hr := (L.sharedAt start).undo_counts (L.sharedAt_valid h start) n v k (L.sharedAt_sized n v k hw start)
    simp only [sharedSwaps,recordedToffoliCount_append,recordedMeasurementCount_append,
      (embedRecorded_counts _).1,(embedRecorded_counts _).2,
      (forgetBranch_resources _).1,(forgetBranch_resources _).2.1,
      (recoverBranch_resources _ _ _).1,(recoverBranch_resources _ _ _).2.1,
      swapDecoder,(decodeSwap_resources _ _ _).1,(decodeSwap_resources _ _ _).2.1,
      hf.1,hf.2,hr.1,hr.2,(ih _ _).1,(ih _ _).2]
    constructor <;> ring

theorem StepLayout.sharedSwaps_support (L : StepLayout) (h : L.Valid)
    (start slots cursor : Nat) : recordedWires (L.sharedSwaps start slots cursor)⊆L.sharedUsed.toFinset := by
  induction slots generalizing start cursor with
  | zero => simp [sharedSwaps,recordedWires]
  | succ slots ih =>
    have hf := (L.sharedAt start).program_support (L.sharedAt_valid h start)
    have hr := (L.sharedAt start).undo_support (L.sharedAt_valid h start)
    have hd := (L.sharedAt start).swapRecovery_support (L.sharedAt_valid h start)
      (cursor+measurementCount (L.sharedAt start).program)
    have hs := L.sharedAt_support start
    have hf := hf.trans hs
    have hr := hr.trans hs
    have hd := hd.trans hs
    have hq : {(L.sharedAt start).history.swap}⊆L.sharedUsed.toFinset := by
      intro w hw
      apply hd
      rw [(recoverBranch_resources _ _ _).2.2.1]
      exact Finset.mem_union_right _ hw
    simp only [sharedSwaps,recordedWires_append,embedRecorded_wires,
      (forgetBranch_resources _).2.2,Finset.union_subset_iff]
    exact ⟨⟨hf,⟨⟨hq,ih _ _⟩,hd⟩⟩,hr⟩

theorem StepLayout.sharedSwaps_qubits (L : StepLayout) (h : L.Valid)
    (start slots cursor : Nat) : (recordedWires (L.sharedSwaps start slots cursor)).card≤L.sharedUsed.length := by
  have hh := Finset.card_le_card (L.sharedSwaps_support h start slots cursor)
  rwa [List.toFinset_card_of_nodup (L.sharedUsed_nodup h)] at hh



theorem StepLayout.shared_ready_of_ready (L : StepLayout) (st : ZState) (s : BasisState)
    (hs : L.Ready st s) : L.SharedReady 0 st s := by
  refine ⟨hs.1,hs.2.1,hs.2.2.1,?_⟩
  intro w hw
  exact hs.2.2.2 w (future_retained_wire _ w hw)

/-- No terminal g=0 premise: this is a finite actual schedule and its inverse,
with all swap controls measured on one reused physical wire. -/
theorem StepLayout.sharedSwaps590_correct (L : StepLayout) (h : L.Valid)
    (hw : L.Sized 258 592 11) (hhistory : 590≤L.future.length)
    (p x : Int) (hp : 0≤p) (hodd : p%2=1) (hsmall : p<2^256) (hx : 0≤x) (hxp : x≤p)
    (s : State) (m : List Bool) (cursor : Nat) (hs : L.SharedReady 0 (zSeed p x) s.basis) :
    runWithTape (L.sharedSwaps 0 590 cursor) m cursor s=s :=
  L.sharedSwaps_correct h p x hodd 590 hhistory
    (L.walk590_fits hw p x hp hodd hsmall hx hxp) 0 590 (by omega) s m cursor hs

theorem StepLayout.sharedSwaps590_counts (L : StepLayout) (h : L.Valid)
    (hw : L.Sized 258 592 11) (cursor : Nat) :
    recordedToffoliCount (L.sharedSwaps 0 590 cursor)=5023850 ∧
    recordedMeasurementCount (L.sharedSwaps 0 590 cursor)=3321110 := by
  have hh := L.sharedSwaps_counts h 258 592 11 hw 0 590 cursor
  norm_num at hh
  exact hh

/-- Conditional physical support bound for the stated pool capacities.
No allocator at these numeric widths or paper-space claim is implicit. -/
theorem StepLayout.sharedSwaps590_qubits (L : StepLayout) (h : L.Valid)
    (hw : L.Sized 258 592 11) (hmask : L.mask.length≤592) (hcarry : L.carry.length≤591)
    (hhistory : L.future.length=590) (cursor : Nat) :
    (recordedWires (L.sharedSwaps 0 590 cursor)).card≤4337 := by
  have hq := L.sharedSwaps_qubits h 0 590 cursor
  have hl := L.sharedUsed_sized_length h 258 592 11 hw
  omega

theorem sharedSwapExample_support (cursor : Nat) :
    (recordedWires (sharedSwapExample.sharedSwaps 0 2 cursor)).card≤28 :=
  sharedSwapExample.sharedSwaps_qubits sharedSwapExample_valid 0 2 cursor

theorem sharedSwapExample_unused :
    26∉sharedSwapExample.sharedUsed.toFinset ∧ 29∉sharedSwapExample.sharedUsed.toFinset := by decide

end ECDSAAdd.Arithmetic.Divsteps
