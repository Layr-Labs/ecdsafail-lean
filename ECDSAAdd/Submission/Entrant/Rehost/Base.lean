import ECDSAAdd.Submission.Entrant.Rehost.Defs
/-!
# Rehost: generic lemmas

Piecewise renaming of a program by involutive wire maps. The map may stay the same over several pieces; where it
changes, the wires on which the two maps differ must be zero in the run of the ORIGINAL program.
-/
namespace ECDSAAdd.Entrant.Rehost
open ECDSAAdd Arithmetic Challenge Secp256k1

/-- One swap of two wires as a plain function. -/
def sw (a b : Wire) (q : Wire) : Wire := if q = a then b else if q = b then a else q

theorem pullState_pullState (f : Wire → Wire) (hf : ∀ q, f (f q) = q) (s : State) :
    pullState f (pullState f s) = s := by
  apply State.extensionality
  · rfl
  · funext q
    show s.basis (f (f q)) = s.basis q
    rw [hf]

theorem injective_of_involutive (f : Wire → Wire) (hf : ∀ q, f (f q) = q) : Function.Injective f := by
  intro a b h
  have := congrArg f h
  rwa [hf, hf] at this

/-- Running a renamed piece from the pulled-back state gives the pulled-back result. -/
theorem run_rename_pull (f : Wire → Wire) (hf : ∀ q, f (f q) = q) (P : Program) (m : List Bool)
    (s : State) : run (renameProgram f P) m (pullState f s) = pullState f (run P m s) := by
  have r := run_rename f (injective_of_involutive f hf) P m (pullState f s)
  rw [pullState_pullState f hf] at r
  have e := congrArg (pullState f) r
  rwa [pullState_pullState f hf] at e

theorem pullState_congr (f g : Wire → Wire) (s : State)
    (h : ∀ q, s.basis (f q) = s.basis (g q)) : pullState f s = pullState g s := by
  apply State.extensionality
  · rfl
  · funext q
    exact h q

theorem pullState_id (s : State) : pullState (fun q => q) s = s := rfl

/-- `B` replays `A` up to the wire map `f`, on every tape, from the state `s`. -/
def Inv (f : Wire → Wire) (A B : Program) (s : State) : Prop :=
  measurementCount B = measurementCount A ∧ ∀ m, run B m s = pullState f (run A m s)

theorem inv_nil (s : State) : Inv (fun q => q) [] [] s := ⟨rfl, fun _ => rfl⟩

/-- Extend by one piece under the same map. -/
theorem inv_step {f : Wire → Wire} (hf : ∀ q, f (f q) = q) {A B : Program} {s : State}
    (h : Inv f A B s) (P : Program) : Inv f (A ++ P) (B ++ renameProgram f P) s := by
  refine ⟨?_, fun m => ?_⟩
  · rw [measurementCount_append, measurementCount_append, h.1, (renameProgram_counts f P).2]
  · rw [run_append, run_append, h.1, h.2, run_rename_pull f hf]

/-- Change the map at a boundary where the two maps agree on the reached states. -/
theorem inv_switch {f g : Wire → Wire} {A B : Program} {s : State} (h : Inv f A B s)
    (hc : ∀ m q, (run A m s).basis (f q) = (run A m s).basis (g q)) : Inv g A B s :=
  ⟨h.1, fun m => by rw [h.2, pullState_congr f g _ (hc m)]⟩

theorem inv_run_eq {A B : Program} {s : State} (h : Inv (fun q => q) A B s) (m : List Bool) :
    run B m s = run A m s := h.2 m

/-! ## Cleanliness along a program: forward and backward through an untouched piece -/

theorem basis_append_untouched (A P : Program) (m : List Bool) (s : State) (w : Wire)
    (hw : w ∉ wires P) :
    (run (A ++ P) m s).basis w = (run A (m.take (measurementCount A)) s).basis w := by
  rw [run_append]
  exact run_preserves_outside P _ _ w hw

/-- Forward: clean after `A` on every tape, untouched by `P`, hence clean after `A ++ P`. -/
theorem clean_forward (A P : Program) (s : State) (w : Wire) (hw : w ∉ wires P)
    (h : ∀ m, (run A m s).basis w = false) : ∀ m, (run (A ++ P) m s).basis w = false := by
  intro m
  rw [basis_append_untouched A P m s w hw]
  exact h _

/-- Backward: clean after `A ++ P` on every tape, untouched by `P`, hence clean after `A`. -/
theorem clean_backward (A P : Program) (s : State) (w : Wire) (hw : w ∉ wires P)
    (h : ∀ m, (run (A ++ P) m s).basis w = false) : ∀ m, (run A m s).basis w = false := by
  intro m
  have e := basis_append_untouched A P (m.take (measurementCount A)) s w hw
  rw [List.take_take, Nat.min_self, run_take] at e
  rw [← e]
  exact h _

end ECDSAAdd.Entrant.Rehost
