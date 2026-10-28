import ECDSAAdd.Framework.GateInverse

namespace ECDSAAdd
attribute [local irreducible] run measurementCount

/-- Compose an already established local State equality without reducing the
programs. The record splits are the ordinary operational splits of run_append. -/
theorem append_context_eq (P Q R : Program) (s : State) (m n : List Bool)
    (localEq :
      run Q (m.drop (measurementCount P)) (run P (m.take (measurementCount P)) s)=
      run R (n.drop (measurementCount P)) (run P (n.take (measurementCount P)) s)) :
    run (P++Q) m s=run (P++R) n s :=
  (run_append P Q m s).trans (localEq.trans (run_append P R n s).symm)

/-- A shared suffix observes equal head States on independent record lists.
No field or input hypothesis is introduced by this generic context lemma. -/
theorem suffix_context_eq (P Q S : Program) (s : State) (m n : List Bool)
    (headEq : run P (m.take (measurementCount P)) s=
      run Q (n.take (measurementCount Q)) s)
    (tailEq : m.drop (measurementCount P)=n.drop (measurementCount Q)) :
    run (P++S) m s=run (Q++S) n s := by
  have stateEq := congrArg (fun t : State => run S (m.drop (measurementCount P)) t) headEq
  have recordsEq := congrArg (fun k : List Bool =>
    run S k (run Q (n.take (measurementCount Q)) s)) tailEq
  exact (run_append P S m s).trans
    (stateEq.trans (recordsEq.trans (run_append Q S n s).symm))

/-- Keep program-shape conversion inside a generic theorem rather than asking
the caller's elaborator to unfold two concrete measured gate lists. -/
theorem program_shape_context_eq (P Q P' Q' : Program) (s : State) (m n : List Bool)
    (hp : P=P') (hq : Q=Q') (states : run P' m s=run Q' n s) :
    run P m s=run Q n s :=
  (congrArg (fun p : Program => run p m s) hp).trans
    (states.trans (congrArg (fun q : Program => run q n s) hq).symm)

end ECDSAAdd
#print axioms ECDSAAdd.append_context_eq
#print axioms ECDSAAdd.suffix_context_eq
#print axioms ECDSAAdd.program_shape_context_eq
