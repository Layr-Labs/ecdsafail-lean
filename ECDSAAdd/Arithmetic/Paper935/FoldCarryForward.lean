import ECDSAAdd.Arithmetic.Paper935.FoldCarryCell

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Actual forward cell leaves exactly the data dressing used by the author's
backward sweep, while restoring the shared literal control immediately. -/
theorem foldCarryForward_run (bit : Bool) (control data target : Wire) (cin : Option Wire)
    (hn : ([control,data,target]++cin.toList).Nodup)
    (s : State) (m : List Bool) (clean : s.basis target=false) :
    run (foldCarryForward bit control data target cin) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (carryBit (s.basis data) (bit && s.basis control) ((cin.map s.basis).getD false))) data
        (s.basis data ^^ (bit && (cin.map s.basis).getD false))⟩ := by
  cases cin with
  | none =>
    simp only [Option.toList_none,List.append_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
    obtain ⟨⟨hcd,hct⟩,hdt⟩ := hn
    have hdc := Ne.symm hcd
    have htc := Ne.symm hct
    have htd := Ne.symm hdt
    cases bit <;> cases hc : s.basis control <;> cases hd : s.basis data <;>
      simp_all [foldCarryForward,run,carryBit,writeBit,Function.update]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hqc : q=control <;> by_cases hqd : q=data <;> by_cases hqt : q=target <;>
        simp_all [Function.update]
  | some d =>
    simp only [Option.toList_some,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
    obtain ⟨⟨hcd,hct,hci⟩,⟨hdt,hdi⟩,hti⟩ := hn
    have hdc := Ne.symm hcd
    have htc := Ne.symm hct
    have htd := Ne.symm hdt
    have hic := Ne.symm hci
    have hid := Ne.symm hdi
    have hit := Ne.symm hti
    cases bit <;> cases hc : s.basis control <;> cases hd : s.basis data <;> cases hi : s.basis d <;>
      simp_all [foldCarryForward,run,carryBit,writeBit,Function.update]
    all_goals
      funext q
      by_cases hqc : q=control <;> by_cases hqd : q=data <;> by_cases hqt : q=target <;>
        by_cases hqi : q=d <;> simp_all [Function.update]

end ECDSAAdd.Arithmetic.Paper935
