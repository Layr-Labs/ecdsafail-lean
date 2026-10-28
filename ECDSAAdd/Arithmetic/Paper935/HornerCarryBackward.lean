import ECDSAAdd.Arithmetic.Paper935.HornerCarryCell

namespace ECDSAAdd.Arithmetic.Paper935

/-- Pure output of luo_core.py:897–910 on dressed operands and a valid
carry. Retained top carries are left unchanged. -/
def hornerCarryFinish (ctrl a e t : Wire) (cin : Option Wire) (sums keep : Bool)
    (s : BasisState) : BasisState :=
  let d := (cin.map s).getD false
  let A := s a ^^ d
  let E := s e ^^ d
  writeBit (writeBit (writeBit s t (if keep then s t else false)) a
    (if sums && s ctrl then sumBit A E d else A)) e E

private theorem backward_none_false_false (ctrl a e t : Wire) 
    (distinct : ([ctrl,a,e,t]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool)
    (carry : s.basis t=carryBit (s.basis a ^^ ((none : Option Wire).map s.basis).getD false)
      (s.basis e ^^ ((none : Option Wire).map s.basis).getD false) (((none : Option Wire).map s.basis).getD false)) :
    run (hornerCarryBackward ctrl a e t (none : Option Wire) false false) m s=
      ⟨s.phase,hornerCarryFinish ctrl a e t (none : Option Wire) false false s.basis⟩ := by
  simp only [Option.toList_none,List.append_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct⟩,⟨hae,hat⟩,het⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  cases hc : s.basis ctrl <;> cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryBackward,hornerCarryFinish,run,measureAndCorrect,correct,carryBit,writeBit,Function.update]
  all_goals
    try apply congrArg (State.mk s.phase)
    funext q
    by_cases hqa : q=a <;> by_cases hqe : q=e <;> by_cases hqt : q=t <;> simp_all [Function.update]

private theorem backward_none_false_true (ctrl a e t : Wire) 
    (distinct : ([ctrl,a,e,t]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool)
    (carry : s.basis t=carryBit (s.basis a ^^ ((none : Option Wire).map s.basis).getD false)
      (s.basis e ^^ ((none : Option Wire).map s.basis).getD false) (((none : Option Wire).map s.basis).getD false)) :
    run (hornerCarryBackward ctrl a e t (none : Option Wire) false true) m s=
      ⟨s.phase,hornerCarryFinish ctrl a e t (none : Option Wire) false true s.basis⟩ := by
  simp only [Option.toList_none,List.append_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct⟩,⟨hae,hat⟩,het⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  cases hc : s.basis ctrl <;> cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryBackward,hornerCarryFinish,run,carryBit,writeBit]
  all_goals
    try apply congrArg (State.mk s.phase)
    funext q
    by_cases hqa : q=a <;> by_cases hqe : q=e <;> by_cases hqt : q=t <;> simp_all [Function.update]

private theorem backward_none_true_false (ctrl a e t : Wire) 
    (distinct : ([ctrl,a,e,t]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool)
    (carry : s.basis t=carryBit (s.basis a ^^ ((none : Option Wire).map s.basis).getD false)
      (s.basis e ^^ ((none : Option Wire).map s.basis).getD false) (((none : Option Wire).map s.basis).getD false)) :
    run (hornerCarryBackward ctrl a e t (none : Option Wire) true false) m s=
      ⟨s.phase,hornerCarryFinish ctrl a e t (none : Option Wire) true false s.basis⟩ := by
  simp only [Option.toList_none,List.append_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct⟩,⟨hae,hat⟩,het⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  cases hc : s.basis ctrl <;> cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryBackward,hornerCarryFinish,run,measureAndCorrect,correct,carryBit,sumBit,writeBit,Function.update]

private theorem backward_none_true_true (ctrl a e t : Wire) 
    (distinct : ([ctrl,a,e,t]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool)
    (carry : s.basis t=carryBit (s.basis a ^^ ((none : Option Wire).map s.basis).getD false)
      (s.basis e ^^ ((none : Option Wire).map s.basis).getD false) (((none : Option Wire).map s.basis).getD false)) :
    run (hornerCarryBackward ctrl a e t (none : Option Wire) true true) m s=
      ⟨s.phase,hornerCarryFinish ctrl a e t (none : Option Wire) true true s.basis⟩ := by
  simp only [Option.toList_none,List.append_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct⟩,⟨hae,hat⟩,het⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  cases hc : s.basis ctrl <;> cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryBackward,hornerCarryFinish,run,carryBit,sumBit,writeBit]
  all_goals
    try apply congrArg (State.mk s.phase)
    funext q
    by_cases hqa : q=a <;> by_cases hqe : q=e <;> by_cases hqt : q=t <;> simp_all [Function.update]

private theorem backward_some_false_false (ctrl a e t : Wire) (d : Wire)
    (distinct : ([ctrl,a,e,t]++(some d : Option Wire).toList).Nodup)
    (s : State) (m : List Bool)
    (carry : s.basis t=carryBit (s.basis a ^^ ((some d : Option Wire).map s.basis).getD false)
      (s.basis e ^^ ((some d : Option Wire).map s.basis).getD false) (((some d : Option Wire).map s.basis).getD false)) :
    run (hornerCarryBackward ctrl a e t (some d : Option Wire) false false) m s=
      ⟨s.phase,hornerCarryFinish ctrl a e t (some d : Option Wire) false false s.basis⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct,hcd⟩,⟨hae,hat,had⟩,⟨het,hed⟩,htd⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  have hcdr := Ne.symm hcd
  have hadr := Ne.symm had
  have hedr := Ne.symm hed
  have htdr := Ne.symm htd
  cases hc : s.basis ctrl <;> cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hd : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryBackward,hornerCarryFinish,run,measureAndCorrect,correct,carryBit,writeBit,Function.update]

private theorem backward_some_false_true (ctrl a e t : Wire) (d : Wire)
    (distinct : ([ctrl,a,e,t]++(some d : Option Wire).toList).Nodup)
    (s : State) (m : List Bool)
    (carry : s.basis t=carryBit (s.basis a ^^ ((some d : Option Wire).map s.basis).getD false)
      (s.basis e ^^ ((some d : Option Wire).map s.basis).getD false) (((some d : Option Wire).map s.basis).getD false)) :
    run (hornerCarryBackward ctrl a e t (some d : Option Wire) false true) m s=
      ⟨s.phase,hornerCarryFinish ctrl a e t (some d : Option Wire) false true s.basis⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct,hcd⟩,⟨hae,hat,had⟩,⟨het,hed⟩,htd⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  have hcdr := Ne.symm hcd
  have hadr := Ne.symm had
  have hedr := Ne.symm hed
  have htdr := Ne.symm htd
  cases hc : s.basis ctrl <;> cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hd : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryBackward,hornerCarryFinish,run,carryBit,writeBit,Function.update]
  all_goals
    try apply congrArg (State.mk s.phase)
    funext q
    by_cases hqa : q=a <;> by_cases hqe : q=e <;> by_cases hqt : q=t <;> simp_all [Function.update]

private theorem backward_some_true_false (ctrl a e t : Wire) (d : Wire)
    (distinct : ([ctrl,a,e,t]++(some d : Option Wire).toList).Nodup)
    (s : State) (m : List Bool)
    (carry : s.basis t=carryBit (s.basis a ^^ ((some d : Option Wire).map s.basis).getD false)
      (s.basis e ^^ ((some d : Option Wire).map s.basis).getD false) (((some d : Option Wire).map s.basis).getD false)) :
    run (hornerCarryBackward ctrl a e t (some d : Option Wire) true false) m s=
      ⟨s.phase,hornerCarryFinish ctrl a e t (some d : Option Wire) true false s.basis⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct,hcd⟩,⟨hae,hat,had⟩,⟨het,hed⟩,htd⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  have hcdr := Ne.symm hcd
  have hadr := Ne.symm had
  have hedr := Ne.symm hed
  have htdr := Ne.symm htd
  cases hc : s.basis ctrl <;> cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hd : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryBackward,hornerCarryFinish,run,measureAndCorrect,correct,carryBit,sumBit,writeBit,Function.update]

private theorem backward_some_true_true (ctrl a e t : Wire) (d : Wire)
    (distinct : ([ctrl,a,e,t]++(some d : Option Wire).toList).Nodup)
    (s : State) (m : List Bool)
    (carry : s.basis t=carryBit (s.basis a ^^ ((some d : Option Wire).map s.basis).getD false)
      (s.basis e ^^ ((some d : Option Wire).map s.basis).getD false) (((some d : Option Wire).map s.basis).getD false)) :
    run (hornerCarryBackward ctrl a e t (some d : Option Wire) true true) m s=
      ⟨s.phase,hornerCarryFinish ctrl a e t (some d : Option Wire) true true s.basis⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct,hcd⟩,⟨hae,hat,had⟩,⟨het,hed⟩,htd⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  have hcdr := Ne.symm hcd
  have hadr := Ne.symm had
  have hedr := Ne.symm hed
  have htdr := Ne.symm htd
  cases hc : s.basis ctrl <;> cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hd : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryBackward,hornerCarryFinish,run,carryBit,sumBit,writeBit,Function.update]
  all_goals
    try apply congrArg (State.mk s.phase)
    funext q
    by_cases hqa : q=a <;> by_cases hqe : q=e <;> by_cases hqt : q=t <;> simp_all [Function.update]

/-- Exact descending cell semantics on the dressed values. This theorem
allows the other block cells to have already written their sums. -/
theorem hornerCarryBackward_run (ctrl a e t : Wire) (cin : Option Wire)
    (sums keep : Bool) (distinct : ([ctrl,a,e,t]++cin.toList).Nodup)
    (s : State) (m : List Bool)
    (carry : s.basis t=carryBit (s.basis a ^^ (cin.map s.basis).getD false)
      (s.basis e ^^ (cin.map s.basis).getD false) ((cin.map s.basis).getD false)) :
    run (hornerCarryBackward ctrl a e t cin sums keep) m s=
      ⟨s.phase,hornerCarryFinish ctrl a e t cin sums keep s.basis⟩ := by
  cases cin <;> cases sums <;> cases keep
  · exact backward_none_false_false ctrl a e t distinct s m carry
  · exact backward_none_false_true ctrl a e t distinct s m carry
  · exact backward_none_true_false ctrl a e t distinct s m carry
  · exact backward_none_true_true ctrl a e t distinct s m carry
  · exact backward_some_false_false ctrl a e t _ distinct s m carry
  · exact backward_some_false_true ctrl a e t _ distinct s m carry
  · exact backward_some_true_false ctrl a e t _ distinct s m carry
  · exact backward_some_true_true ctrl a e t _ distinct s m carry

end ECDSAAdd.Arithmetic.Paper935
