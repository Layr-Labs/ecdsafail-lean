import ECDSAAdd.Arithmetic.Divsteps.PhysicalWalk
import ECDSAAdd.Arithmetic.Divsteps.ScaleRemoval

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- Every completed slot's controls occur in the later layout's past. -/
theorem StepLayout.at_history_past (L : StepLayout) (i j : Nat)
    (hi : i≤L.future.length) (hj : j < i) (w : Wire) (hw : w∈(L.at j).history.wires) :
    w∈(L.at i).past.flatMap StepHistory.wires := by
  induction i with
  | zero => omega
  | succ i ih =>
    have hne := L.at_can_advance i (by omega)
    have hm : w∈(L.at i).history.wires ∨ w∈(L.at i).past.flatMap StepHistory.wires := by
      by_cases he : j=i
      · subst j; exact Or.inl hw
      · exact Or.inr (ih (by omega) (by omega))
    cases he : (L.at i).future with
    | nil => exact (hne he).elim
    | cons a rest =>
      simpa only [StepLayout.at,next,nextHistory,halfView,he,List.flatMap_cons,List.mem_append] using hm

/-- Values of all actual retained activity controls at the end of the forward
program. No external activity-list premise is needed. -/
theorem StepLayout.walk_activity (L : StepLayout) (h : L.Valid) (p x : Int) (N : Nat)
    (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i))
    (s : State) (m : List Bool) (hs : L.Ready (zSeed p x) s.basis) :
    ∀ i, i<N → (run (L.walk N) m s).basis (L.at i).history.active=activeControl (zWalk p x i) := by
  let P := fun i s => (L.at i).Ready (zWalk p x i) s ∧
    ∀ j, j < i → s (L.at j).history.active=activeControl (zWalk p x j)
  have hp : ∀ i, i<N → Triple (P i) (L.at i).program (P (i+1)) := by
    intro i hi t mt ht
    have hv := L.at_valid h i
    have hready := (L.at i).program_spec hv (zWalk p x i) (hfit i hi)
      (L.at_can_advance i (by omega)) t mt ht.1
    have hc := (L.at i).program_zSlot_controls hv (zWalk p x i) (hfit i hi) t mt
      ht.1.1 ht.1.2.1 ht.1.2.2.1
    refine ⟨hready.1,hready.2,?_⟩
    intro j hj
    by_cases he : j=i
    · subst j; exact hc.2.2.2.1
    · have hj' : j < i := by omega
      rw [(L.at i).reserved_frame hv t mt _ (List.mem_append_left _
        (L.at_history_past i j (by omega) hj' _ (by simp [StepHistory.wires])))]
      exact ht.2 j hj'
  have hstart : P 0 s.basis := ⟨hs,by intro j hj; omega⟩
  simpa only [Nat.zero_add,walk] using ((forwardWalk_spec (fun i => (L.at i).program) P N hp 0 N (by omega)) s m hstart).2.2

/-- Physical controls consumed in reverse chronological order. -/
def StepLayout.reverseActivityWires (L : StepLayout) (N : Nat) : List Wire :=
  ((List.range N).map fun i => (L.at i).history.active).reverse

theorem StepLayout.reverseActivityWires_values (L : StepLayout) (h : L.Valid)
    (p x : Int) (N : Nat) (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i))
    (s : State) (m : List Bool) (hs : L.Ready (zSeed p x) s.basis) :
    (L.reverseActivityWires N).map (run (L.walk N) m s).basis = reverseActivities p x N := by
  have hh := L.walk_activity h p x N hhistory hfit s m hs
  simp only [reverseActivityWires,reverseActivities,List.map_reverse,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simpa only [Function.comp_apply,activeControl] using hh i (List.mem_range.mp hi)

end ECDSAAdd.Arithmetic.Divsteps
