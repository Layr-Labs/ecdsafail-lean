import ECDSAAdd.Arithmetic.MappedAdder

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- The author's literal-controlled fold carry cell. For a one literal the
data bit is left dressed by the incoming carry; the control is restored. -/
def foldCarryForward (bit : Bool) (control data target : Wire) (cin : Option Wire) : Program :=
  if bit then
    match cin with
    | none => [.CCX data control target]
    | some d => [.CX d data,.CX d control,.CCX data control target,.CX d target,.CX d control]
  else
    match cin with
    | none => []
    | some d => [.CCX data d target]

/-- Exact backward cell, including measured AND erasure and its correction.
A keeper cell retains its carry instead of measuring it. -/
def foldCarryBackward (bit : Bool) (control data target : Wire) (cin : Option Wire)
    (sums keep : Bool) : Program :=
  if bit then
    (if keep then [] else
      (cin.toList.flatMap fun d => [.CX d control,.CX d target]) ++
      [.measureX target [] [.CZ data control]] ++
      (cin.toList.map fun d => .CX d control)) ++
    (if sums then [.CX control data] else cin.toList.map fun d => .CX d data)
  else
    (if keep then [] else cin.toList.map fun d => .measureX target [] [.CZ data d]) ++
    (if sums then cin.toList.map fun d => .CX d data else [])

private theorem cell_none_false_false (control data target : Wire) 
    (sums : Bool) (hn : ([control,data,target]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (clean : s.basis target=false) :
    run (foldCarryForward false control data target (none : Option Wire) ++ foldCarryBackward false control data target (none : Option Wire) sums false) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (if false then carryBit (s.basis data) (false && s.basis control) (((none : Option Wire).map s.basis).getD false) else false)) data
        (if sums then sumBit (s.basis data) (false && s.basis control) (((none : Option Wire).map s.basis).getD false) else s.basis data)⟩ := by
  simp only [Option.toList_none,List.append_nil,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hcd,hct⟩,hdt⟩ := hn
  have hdc := Ne.symm hcd
  have htc := Ne.symm hct
  have htd := Ne.symm hdt
  cases sums <;> cases hc : s.basis control <;> cases hd : s.basis data <;>
    cases hm : m.head?.getD false <;>
    simp_all [foldCarryForward,foldCarryBackward,run,sumBit,writeBit]
  all_goals
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqc : q=control <;> by_cases hqd : q=data <;> by_cases hqt : q=target <;>
      simp_all [Function.update]


private theorem cell_none_false_true (control data target : Wire) 
    (sums : Bool) (hn : ([control,data,target]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (clean : s.basis target=false) :
    run (foldCarryForward false control data target (none : Option Wire) ++ foldCarryBackward false control data target (none : Option Wire) sums true) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (if true then carryBit (s.basis data) (false && s.basis control) (((none : Option Wire).map s.basis).getD false) else false)) data
        (if sums then sumBit (s.basis data) (false && s.basis control) (((none : Option Wire).map s.basis).getD false) else s.basis data)⟩ := by
  simp only [Option.toList_none,List.append_nil,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hcd,hct⟩,hdt⟩ := hn
  have hdc := Ne.symm hcd
  have htc := Ne.symm hct
  have htd := Ne.symm hdt
  cases sums <;> cases hc : s.basis control <;> cases hd : s.basis data <;>
    cases hm : m.head?.getD false <;>
    simp_all [foldCarryForward,foldCarryBackward,run,carryBit,sumBit,writeBit]
  all_goals
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqc : q=control <;> by_cases hqd : q=data <;> by_cases hqt : q=target <;>
      simp_all [Function.update]


private theorem cell_none_true_false (control data target : Wire) 
    (sums : Bool) (hn : ([control,data,target]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (clean : s.basis target=false) :
    run (foldCarryForward true control data target (none : Option Wire) ++ foldCarryBackward true control data target (none : Option Wire) sums false) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (if false then carryBit (s.basis data) (true && s.basis control) (((none : Option Wire).map s.basis).getD false) else false)) data
        (if sums then sumBit (s.basis data) (true && s.basis control) (((none : Option Wire).map s.basis).getD false) else s.basis data)⟩ := by
  simp only [Option.toList_none,List.append_nil,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hcd,hct⟩,hdt⟩ := hn
  have hdc := Ne.symm hcd
  have htc := Ne.symm hct
  have htd := Ne.symm hdt
  cases sums <;> cases hc : s.basis control <;> cases hd : s.basis data <;>
    cases hm : m.head?.getD false <;>
    simp_all [foldCarryForward,foldCarryBackward,run,measureAndCorrect,correct,sumBit,writeBit,Function.update]



private theorem cell_none_true_true (control data target : Wire) 
    (sums : Bool) (hn : ([control,data,target]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (clean : s.basis target=false) :
    run (foldCarryForward true control data target (none : Option Wire) ++ foldCarryBackward true control data target (none : Option Wire) sums true) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (if true then carryBit (s.basis data) (true && s.basis control) (((none : Option Wire).map s.basis).getD false) else false)) data
        (if sums then sumBit (s.basis data) (true && s.basis control) (((none : Option Wire).map s.basis).getD false) else s.basis data)⟩ := by
  simp only [Option.toList_none,List.append_nil,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hcd,hct⟩,hdt⟩ := hn
  have hdc := Ne.symm hcd
  have htc := Ne.symm hct
  have htd := Ne.symm hdt
  cases sums <;> cases hc : s.basis control <;> cases hd : s.basis data <;>
    cases hm : m.head?.getD false <;>
    simp_all [foldCarryForward,foldCarryBackward,run,carryBit,sumBit,writeBit,Function.update]



private theorem cell_some_false_false (control data target : Wire) (d : Wire)
    (sums : Bool) (hn : ([control,data,target]++(some d).toList).Nodup)
    (s : State) (m : List Bool) (clean : s.basis target=false) :
    run (foldCarryForward false control data target (some d) ++ foldCarryBackward false control data target (some d) sums false) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (if false then carryBit (s.basis data) (false && s.basis control) (((some d).map s.basis).getD false) else false)) data
        (if sums then sumBit (s.basis data) (false && s.basis control) (((some d).map s.basis).getD false) else s.basis data)⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hcd,hct,hci⟩,⟨hdt,hdi⟩,hti⟩ := hn
  have hdc := Ne.symm hcd
  have htc := Ne.symm hct
  have htd := Ne.symm hdt
  have hic := Ne.symm hci
  have hid := Ne.symm hdi
  have hit := Ne.symm hti
  cases sums <;> cases hc : s.basis control <;> cases hd : s.basis data <;>
    cases hi : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [foldCarryForward,foldCarryBackward,run,measureAndCorrect,correct,sumBit,writeBit,Function.update]



private theorem cell_some_false_true (control data target : Wire) (d : Wire)
    (sums : Bool) (hn : ([control,data,target]++(some d).toList).Nodup)
    (s : State) (m : List Bool) (clean : s.basis target=false) :
    run (foldCarryForward false control data target (some d) ++ foldCarryBackward false control data target (some d) sums true) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (if true then carryBit (s.basis data) (false && s.basis control) (((some d).map s.basis).getD false) else false)) data
        (if sums then sumBit (s.basis data) (false && s.basis control) (((some d).map s.basis).getD false) else s.basis data)⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hcd,hct,hci⟩,⟨hdt,hdi⟩,hti⟩ := hn
  have hdc := Ne.symm hcd
  have htc := Ne.symm hct
  have htd := Ne.symm hdt
  have hic := Ne.symm hci
  have hid := Ne.symm hdi
  have hit := Ne.symm hti
  cases sums <;> cases hc : s.basis control <;> cases hd : s.basis data <;>
    cases hi : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [foldCarryForward,foldCarryBackward,run,carryBit,sumBit,writeBit,Function.update]



private theorem cell_some_true_false (control data target : Wire) (d : Wire)
    (sums : Bool) (hn : ([control,data,target]++(some d).toList).Nodup)
    (s : State) (m : List Bool) (clean : s.basis target=false) :
    run (foldCarryForward true control data target (some d) ++ foldCarryBackward true control data target (some d) sums false) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (if false then carryBit (s.basis data) (true && s.basis control) (((some d).map s.basis).getD false) else false)) data
        (if sums then sumBit (s.basis data) (true && s.basis control) (((some d).map s.basis).getD false) else s.basis data)⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hcd,hct,hci⟩,⟨hdt,hdi⟩,hti⟩ := hn
  have hdc := Ne.symm hcd
  have htc := Ne.symm hct
  have htd := Ne.symm hdt
  have hic := Ne.symm hci
  have hid := Ne.symm hdi
  have hit := Ne.symm hti
  cases sums <;> cases hc : s.basis control <;> cases hd : s.basis data <;>
    cases hi : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [foldCarryForward,foldCarryBackward,run,measureAndCorrect,correct,sumBit,writeBit,Function.update]
  all_goals
    funext q
    by_cases hqc : q=control <;> by_cases hqd : q=data <;> by_cases hqt : q=target <;>
      by_cases hqi : q=d <;>
      simp_all [Function.update]


private theorem cell_some_true_true (control data target : Wire) (d : Wire)
    (sums : Bool) (hn : ([control,data,target]++(some d).toList).Nodup)
    (s : State) (m : List Bool) (clean : s.basis target=false) :
    run (foldCarryForward true control data target (some d) ++ foldCarryBackward true control data target (some d) sums true) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (if true then carryBit (s.basis data) (true && s.basis control) (((some d).map s.basis).getD false) else false)) data
        (if sums then sumBit (s.basis data) (true && s.basis control) (((some d).map s.basis).getD false) else s.basis data)⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hcd,hct,hci⟩,⟨hdt,hdi⟩,hti⟩ := hn
  have hdc := Ne.symm hcd
  have htc := Ne.symm hct
  have htd := Ne.symm hdt
  have hic := Ne.symm hci
  have hid := Ne.symm hdi
  have hit := Ne.symm hti
  cases sums <;> cases hc : s.basis control <;> cases hd : s.basis data <;>
    cases hi : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [foldCarryForward,foldCarryBackward,run,carryBit,sumBit,writeBit,Function.update]
  all_goals
    funext q
    by_cases hqc : q=control <;> by_cases hqd : q=data <;> by_cases hqt : q=target <;>
      by_cases hqi : q=d <;>
      simp_all [Function.update]


/-- Literal carry cell including measured phase correction and optional carry retention. -/
theorem foldCarryCell_run (bit : Bool) (control data target : Wire) (cin : Option Wire)
    (sums keep : Bool) (hn : ([control,data,target]++cin.toList).Nodup)
    (s : State) (m : List Bool) (clean : s.basis target=false) :
    run (foldCarryForward bit control data target cin ++ foldCarryBackward bit control data target cin sums keep) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (if keep then carryBit (s.basis data) (bit && s.basis control) ((cin.map s.basis).getD false) else false)) data
        (if sums then sumBit (s.basis data) (bit && s.basis control) ((cin.map s.basis).getD false) else s.basis data)⟩ := by
  cases cin with
  | none =>
    cases bit <;> cases keep
    · exact cell_none_false_false control data target sums hn s m clean
    · exact cell_none_false_true control data target sums hn s m clean
    · exact cell_none_true_false control data target sums hn s m clean
    · exact cell_none_true_true control data target sums hn s m clean
  | some d =>
    cases bit <;> cases keep
    · exact cell_some_false_false control data target d sums hn s m clean
    · exact cell_some_false_true control data target d sums hn s m clean
    · exact cell_some_true_false control data target d sums hn s m clean
    · exact cell_some_true_true control data target d sums hn s m clean

end ECDSAAdd.Arithmetic.Paper935
