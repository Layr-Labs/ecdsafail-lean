import ECDSAAdd.Framework.Semantics

namespace ECDSAAdd

/-- Missing records are already interpreted as false by run. -/
theorem run_replicate_false (P : Program) (n : Nat) (s : State) :
    run P (List.replicate n false) s=run P [] s := by
  induction P generalizing n s with
  | nil => rfl
  | cons i P ih =>
    cases i with
    | X t => exact ih n _
    | CX c t => exact ih n _
    | CCX a b t => exact ih n _
    | measureX t c0 c1 =>
      cases n with
      | zero => rfl
      | succ n => simpa only [List.replicate_succ,run,List.headD_cons,List.tail_cons,
          List.headD_nil,List.tail_nil] using ih n (measureAndCorrect t c0 c1 false s)

/-- Padding a finite measurement tape by false preserves every State. -/
theorem run_pad_false (P : Program) (m : List Bool) (n : Nat) (s : State) :
    run P (m++List.replicate n false) s=run P m s := by
  induction P generalizing m s with
  | nil => rfl
  | cons i P ih =>
    cases i with
    | X t => exact ih m _
    | CX c t => exact ih m _
    | CCX a b t => exact ih m _
    | measureX t c0 c1 =>
      cases m with
      | nil => simpa only [List.nil_append] using
          run_replicate_false (.measureX t c0 c1::P) n s
      | cons b m =>
          simpa only [List.cons_append,run,List.headD_cons,List.tail_cons] using
            (ih m (measureAndCorrect t c0 c1 b s))

end ECDSAAdd
#print axioms ECDSAAdd.run_replicate_false
#print axioms ECDSAAdd.run_pad_false
