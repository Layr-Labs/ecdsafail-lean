import ECDSAAdd.Arithmetic.Divsteps.SharedSwapScale
import ECDSAAdd.Arithmetic.Divsteps.PhysicalScale

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- Scalar specification in reverse slot order. This allocates no controls. -/
def reverseSlotHalves (p : Nat) (x : Int) (start : Nat) : Nat → Nat → Nat
  | 0, r => r
  | n+1, r =>
    let v := reverseSlotHalves p x (start+1) n r
    if activeControl (zWalk p x start) then halveMod p v else v

theorem reverseSlotHalves_bound (p : Nat) (x : Int) (start n r : Nat)
    (hp : p%2=1) (hr : r<p) : reverseSlotHalves p x start n r<p := by
  induction n generalizing start with
  | zero => exact hr
  | succ n ih =>
    simp only [reverseSlotHalves]
    split
    · exact halve_mod_bound p _ hp (ih (start+1))
    · exact ih (start+1)

/-- All slots reuse one physical swap wire. Each reverse layer halves the
separate accumulator before reconstructing its swap from the old record. -/
def StepLayout.sharedScale (L : StepLayout) (U : ModUnaryLayout) (p start : Nat) :
    Nat → Nat → RecordedProgram
  | 0, _ => []
  | n+1, cursor =>
    let A := L.sharedAt start
    A.swapAround (L.sharedScale U p (start+1) n (cursor+measurementCount A.program+1) ++
      embedRecorded (reverseHalf A.history.active U p)) cursor

/-- Actual finite measured shared-swap walk, physical modular halvings, and
constructive reverse. The accumulator is input separately; no copied endpoint
or termination assumption is supplied by this theorem. -/
theorem StepLayout.sharedScale_run (L : StepLayout) (h : L.Valid)
    (p : Nat) (x : Int) (limit : Nat) (hhistory : limit≤L.future.length)
    (hfit : ∀ i, i<limit → (L.at i).Fits (zWalk p x i))
    (U : ModUnaryLayout) (a : Nat) (hw : U.Widths a) (hU : U.wires.Nodup)
    (hsep : List.Disjoint U.wires L.sharedUsed) (hp : p%2=1) (hpn : p<2^a)
    (start n : Nat) (hrange : start+n≤limit) (r : Nat) (hr : r<p)
    (s : State) (m : List Bool) (cursor : Nat)
    (hs : L.SharedReady start (zWalk p x start) s.basis)
    (hz : regValue U.z s.basis=r) (hwork : regValue U.work s.basis=0) :
    let out := runWithTape (L.sharedScale U p start n cursor) m cursor s
    out.phase=s.phase ∧ regValue U.z out.basis=reverseSlotHalves p x start n r ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  induction n generalizing start s cursor r with
  | zero => exact ⟨rfl,hz,hwork,by intro q _; rfl⟩
  | succ n ih =>
    let A := L.sharedAt start
    let t := run A.program (m.drop cursor) s
    let ordinal := cursor+measurementCount A.program
    let u := runWithTape (forgetBranch A.history.swap) m ordinal t
    let inner := L.sharedScale U p (start+1) n (ordinal+1)
    let v := runWithTape inner m (ordinal+1) u
    let r' := reverseSlotHalves p x (start+1) n r
    let mc := ordinal+1+recordedMeasurementCount inner
    let w := run (reverseHalf A.history.active U p) (m.drop mc) v
    let gap := inner ++ embedRecorded (reverseHalf A.history.active U p)
    have hA := L.sharedAt_valid h start
    have hsepA : List.Disjoint U.wires A.used := by
      apply List.disjoint_left.mpr
      intro q hq hqA
      exact List.disjoint_left.mp hsep hq (List.mem_toFinset.mp
        (L.sharedAt_support start (List.mem_toFinset.mpr hqA)))
    have away (q : Wire) (hq : q∈A.used) : q∉U.z := fun hu =>
      List.disjoint_left.mp hsepA (List.mem_append_left _ hu) hq
    have hqa : A.history.active∈A.used := by simp [StepLayout.used,histories,StepHistory.wires]
    have hqs : A.history.swap∈A.used := by simp [StepLayout.used,histories,StepHistory.wires]
    have hnd : (A.history.active::U.wires).Nodup :=
      List.nodup_cons.mpr ⟨fun hu => List.disjoint_left.mp hsepA hu hqa,hU⟩
    have keep (q : Wire) (hq : q∈U.wires) : u.basis q=s.basis q := by
      have he : q≠A.history.swap := fun he => List.disjoint_left.mp hsepA hq (he ▸ hqs)
      simp only [u,forgetBranch_run]
      rw [show writeBit t.basis A.history.swap false q=t.basis q by simp [writeBit,he]]
      exact run_preserves_outside _ _ _ q (fun hm =>
        List.disjoint_left.mp hsepA hq (List.mem_toFinset.mp (A.program_support hA hm)))
    have val (xs : List Wire) (hx : xs⊆U.wires) : regValue xs u.basis=regValue xs s.basis := by
      apply (regValue_eq_iff _ _ _).mpr
      intro q hq
      exact keep q (hx hq)
    have hu : L.SharedReady (start+1) (zWalk p x (start+1)) u.basis :=
      L.shared_step h start (L.at_can_advance start (by omega)) (zWalk p x start)
        (hfit start (by omega)) s (m.drop cursor) m ordinal hs
    have hv := ih (start+1) (by omega) r hr u (ordinal+1) hu
      ((val U.z (List.subset_append_left _ _)).trans hz)
      ((val U.work (List.subset_append_right _ _)).trans hwork)
    have ha : v.basis A.history.active=activeControl (zWalk p x start) := by
      have he := (A.swapDecoder_distinct hA).1
      rw [show v.basis A.history.active=u.basis A.history.active from hv.2.2.2 _ (away _ hqa)]
      simp only [u,forgetBranch_run]
      rw [show writeBit t.basis A.history.swap false A.history.active=t.basis A.history.active by
        simp [writeBit,he]]
      exact (A.program_zSlot_controls hA _ (hfit start (by omega)) s (m.drop cursor)
        hs.1 hs.2.1 hs.2.2.1).2.2.2.1
    have hr' : r'<p := reverseSlotHalves_bound p x (start+1) n r hp hr
    have hw' := reverseHalf_spec A.history.active U a p r' (activeControl (zWalk p x start))
      hw hnd hp hpn hr' v (m.drop mc) ⟨⟨ha,hv.2.1⟩,hv.2.2.1⟩
    have frame (q : Wire) (hq : q∉U.z) : w.basis q=u.basis q :=
      (controlledHalf_frame A.history.active U a p r' (activeControl (zWalk p x start))
        hw hnd hp hpn hr' v (m.drop mc) ha hv.2.1 hv.2.2.1 q hq).trans (hv.2.2.2 q hq)
    have hgap : runWithTape gap m (ordinal+1) u=w := by
      change runWithTape (inner ++ embedRecorded (reverseHalf A.history.active U p)) m (ordinal+1) u=w
      rw [runWithTape_append,runWithTape_embedRecorded]
    have hpi : (p : Int)%2=1 := by omega
    have hready : A.Ready (zWalk p x start) s.basis :=
      ⟨hs.1,hs.2.1,hs.2.2.1,by simp [FutureClean,A,sharedAt]⟩
    have hh := A.swapAround_run hA p (zWalk p x start) (invariant_zWalk hpi x start) hpi
      (hfit start (by omega)) U.z (List.disjoint_append_left.mp hsepA).1 gap s m cursor hready
      (by change (runWithTape gap m (ordinal+1) u).phase=u.phase; rw [hgap]; exact hw'.1.trans hv.1)
      (by change ∀ q, q∉U.z → (runWithTape gap m (ordinal+1) u).basis q=u.basis q
          rw [hgap]; exact frame)
    dsimp only at hh ⊢
    change (runWithTape (A.swapAround gap cursor) m cursor s).phase=s.phase ∧ _
    refine ⟨hh.1,?_,?_,hh.2.1⟩
    · have he : regValue U.z (runWithTape (A.swapAround gap cursor) m cursor s).basis=
          regValue U.z w.basis := by
        apply (regValue_eq_iff _ _ _).mpr
        intro q hq
        have hb := hh.2.2 q hq
        change (runWithTape (A.swapAround gap cursor) m cursor s).basis q=
          (runWithTape gap m (ordinal+1) u).basis q at hb
        rwa [hgap] at hb
      exact he.trans hw'.2.1.2
    · have he : regValue U.work (runWithTape (A.swapAround gap cursor) m cursor s).basis=
          regValue U.work s.basis := by
        apply (regValue_eq_iff _ _ _).mpr
        intro q hq
        exact hh.2.1 q (fun hz => List.disjoint_left.mp (List.nodup_append'.mp hU).2.2 hz hq)
      exact he.trans hwork

private theorem halveActive_append (p : Nat) (xs ys : List Bool) (r : Nat) :
    halveActive p (xs++ys) r=halveActive p ys (halveActive p xs r) := by
  induction xs generalizing r with
  | nil => rfl
  | cons b xs ih => simpa only [List.cons_append,halveActive] using ih _

/-- The recursive scalar specification is exactly the reverse physical slot
activity sequence, not a separately supplied scale count. -/
theorem reverseSlotHalves_eq (p : Nat) (x : Int) (start n r : Nat) :
    reverseSlotHalves p x start n r=
      halveActive p (((List.range' start n).map fun i => activeControl (zWalk p x i)).reverse) r := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [reverseSlotHalves,List.range'_succ,List.map_cons,List.reverse_cons,
      halveActive_append,halveActive]
    rw [ih]

theorem reverseSlotHalves_zero (p : Nat) (x : Int) (N r : Nat) :
    reverseSlotHalves p x 0 N r=halveActive p (reverseActivities p x N) r := by
  rw [reverseSlotHalves_eq]
  simp [reverseActivities,activeControl,List.range'_eq_map_range]

theorem StepLayout.sharedScale_wellFormed (L : StepLayout) (U : ModUnaryLayout)
    (p start n cursor : Nat) : RecordedWellFormedAt cursor (L.sharedScale U p start n cursor) := by
  induction n generalizing start cursor with
  | zero => trivial
  | succ n ih =>
    apply StepLayout.swapAround_wellFormed
    rw [RecordedWellFormedAt_append]
    exact ⟨ih (start+1) _,embedRecorded_wellFormed _ _⟩

theorem StepLayout.sharedScale_counts (L : StepLayout) (h : L.Valid)
    (n v k a p : Nat) (hw : L.Sized n v k) (U : ModUnaryLayout) (hu : U.Widths a)
    (ha : 0<a) (start slots cursor : Nat) :
    recordedToffoliCount (L.sharedScale U p start slots cursor)=
      slots*(2*(5*n+5*v+k-4)+1+(3*a+2)) ∧
    recordedMeasurementCount (L.sharedScale U p start slots cursor)=
      slots*(2*(4*n+3*v+k-5)+1+2*a) := by
  induction slots generalizing start cursor with
  | zero => simp [sharedScale,recordedToffoliCount,recordedMeasurementCount]
  | succ slots ih =>
    have hh := (L.sharedAt start).swapAround_counts (L.sharedAt_valid h start) n v k
      (L.sharedAt_sized n v k hw start)
      (L.sharedScale U p (start+1) slots (cursor+measurementCount (L.sharedAt start).program+1) ++
        embedRecorded (reverseHalf (L.sharedAt start).history.active U p)) cursor
    simp only [recordedToffoliCount_append,recordedMeasurementCount_append,
      (embedRecorded_counts _).1,(embedRecorded_counts _).2,(ih _ _).1,(ih _ _).2,
      (reverseHalf_counts _ U a p hu ha).1,(reverseHalf_counts _ U a p hu ha).2] at hh
    change recordedToffoliCount ((L.sharedAt start).swapAround _ cursor)=_ ∧
      recordedMeasurementCount ((L.sharedAt start).swapAround _ cursor)=_
    rw [hh.1,hh.2]
    constructor <;> ring

theorem StepLayout.sharedScale_support (L : StepLayout) (h : L.Valid)
    (U : ModUnaryLayout) (a p : Nat) (hw : U.Widths a) (ha : 0<a)
    (start slots cursor : Nat) :
    recordedWires (L.sharedScale U p start slots cursor)⊆(L.sharedUsed++U.wires).toFinset := by
  induction slots generalizing start cursor with
  | zero => simp [sharedScale,recordedWires]
  | succ slots ih =>
    apply Finset.Subset.trans ((L.sharedAt start).swapAround_support (L.sharedAt_valid h start) _ cursor)
    rw [Finset.union_subset_iff,recordedWires_append,Finset.union_subset_iff,embedRecorded_wires]
    have hs : (L.sharedAt start).used.toFinset⊆(L.sharedUsed++U.wires).toFinset :=
      (L.sharedAt_support start).trans (by simp only [List.toFinset_append]; exact Finset.subset_union_left)
    refine ⟨hs,ih (start+1) _,?_⟩
    rw [reverseHalf_wires _ U a p hw ha]
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq
    rcases hq with ((rfl|hq)|hq)|rfl
    · apply hs
      simp [StepLayout.used,histories,StepHistory.wires]
    all_goals simp only [List.mem_toFinset,List.mem_append,ModUnaryLayout.wires,ModUnaryLayout.work,
      List.mem_cons,List.not_mem_nil,or_false]; tauto

theorem StepLayout.sharedScale_qubits (L : StepLayout) (h : L.Valid)
    (U : ModUnaryLayout) (a p : Nat) (hw : U.Widths a) (ha : 0<a)
    (start slots cursor : Nat) :
    (recordedWires (L.sharedScale U p start slots cursor)).card≤L.sharedUsed.length+U.wires.length := by
  have hh := (Finset.card_le_card (L.sharedScale_support h U a p hw ha start slots cursor)).trans
    (List.toFinset_card_le (L.sharedUsed++U.wires))
  simpa only [List.length_append] using hh

/-- Width-safe 590-slot specialization, without asserting that g has stopped. -/
theorem StepLayout.sharedScale590_run (L : StepLayout) (h : L.Valid)
    (hw : L.Sized 258 592 11) (hhistory : 590≤L.future.length)
    (p x r : Nat) (hp : p%2=1) (hsmall : p<2^256) (hx : x≤p) (hr : r<p)
    (U : ModUnaryLayout) (hu : U.Widths 256) (hU : U.wires.Nodup)
    (hsep : List.Disjoint U.wires L.sharedUsed)
    (s : State) (m : List Bool) (cursor : Nat) (hs : L.SharedReady 0 (zSeed p x) s.basis)
    (hz : regValue U.z s.basis=r) (hwork : regValue U.work s.basis=0) :
    let out := runWithTape (L.sharedScale U p 0 590 cursor) m cursor s
    out.phase=s.phase ∧ regValue U.z out.basis=halveActive p (reverseActivities p x 590) r ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  have hpi : (p : Int)%2=1 := by omega
  have hfit := L.walk590_fits hw p x (by omega) hpi (by exact_mod_cast hsmall) (by omega) (by omega)
  simpa only [reverseSlotHalves_zero] using
    L.sharedScale_run h p x 590 hhistory hfit U 256 hu hU hsep hp hsmall 0 590 (by omega)
      r hr s m cursor hs hz hwork

theorem StepLayout.sharedScale590_counts (L : StepLayout) (h : L.Valid)
    (hw : L.Sized 258 592 11) (U : ModUnaryLayout) (hu : U.Widths 256) (p cursor : Nat) :
    recordedToffoliCount (L.sharedScale U p 0 590 cursor)=5478150 ∧
    recordedMeasurementCount (L.sharedScale U p 0 590 cursor)=3623190 := by
  have hh := L.sharedScale_counts h 258 592 11 256 p hw U hu (by omega) 0 590 cursor
  norm_num at hh
  exact hh

/-- Conditional removal of the first-stop scale for the actual shared-swap
program. Neither the endpoint relation nor the stopping claim is synthesized. -/
theorem StepLayout.sharedScale_remove_scale (L : StepLayout) (h : L.Valid)
    (p x N t r : Nat) [Fact p.Prime] (target : ZMod p) (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i))
    (U : ModUnaryLayout) (a : Nat) (hw : U.Widths a) (hU : U.wires.Nodup)
    (hsep : List.Disjoint U.wires L.sharedUsed) (hp : p%2=1) (hpn : p<2^a) (hr : r<p)
    (h2 : (2 : ZMod p)≠0) (ht : t≤N) (hstop : (zWalk p x t).g=0)
    (hbefore : ∀ i, i<t → (zWalk p x i).g≠0) (hscaled : (r : ZMod p)=target*2^t)
    (s : State) (m : List Bool) (cursor : Nat) (hs : L.SharedReady 0 (zSeed p x) s.basis)
    (hz : regValue U.z s.basis=r) (hwork : regValue U.work s.basis=0) :
    let out := runWithTape (L.sharedScale U p 0 N cursor) m cursor s
    (regValue U.z out.basis : ZMod p)=target ∧ out.phase=s.phase ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  have hh := L.sharedScale_run h p x N hhistory hfit U a hw hU hsep hp hpn 0 N (by omega)
    r hr s m cursor hs hz hwork
  refine ⟨?_,hh.1,hh.2.2⟩
  rw [hh.2.1,reverseSlotHalves_zero]
  exact reverseWalk_remove_scale p x N t r target hp hr h2 ht hstop hbefore hscaled

/-- The earlier 4337-wire walk allocation excludes the extra accumulator and
its arithmetic work. This bound explicitly adds that entire allocation. -/
theorem StepLayout.sharedScale590_qubits (L : StepLayout) (h : L.Valid)
    (hw : L.Sized 258 592 11) (hmask : L.mask.length≤592) (hcarry : L.carry.length≤591)
    (hhistory : L.future.length=590) (U : ModUnaryLayout) (hu : U.Widths 256) (p cursor : Nat) :
    (recordedWires (L.sharedScale U p 0 590 cursor)).card≤4337+U.wires.length := by
  have hq := L.sharedScale_qubits h U 256 p hu (by omega) 0 590 cursor
  have hl := L.sharedUsed_sized_length h 258 592 11 hw
  omega

end ECDSAAdd.Arithmetic.Divsteps
