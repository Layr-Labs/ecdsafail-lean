import ECDSAAdd.Arithmetic.Paper935.FoldCarryCell

namespace ECDSAAdd.Arithmetic.Paper935

/-- luo_core.py:882–894, called by engine.py:2287: both quantum
operands are dressed by the incoming carry, unlike a literal fold cell. -/
def hornerCarryForward (a e t : Wire) (cin : Option Wire) : Program :=
  (cin.toList.flatMap fun d => [.CX d a,.CX d e]) ++ [.CCX a e t] ++
    (cin.toList.map fun d => .CX d t)

/-- luo_core.py:897–910: release the AND with its measurement correction,
then optionally write the controlled sum and undress both operands. -/
def hornerCarryBackward (ctrl a e t : Wire) (cin : Option Wire)
    (sums keep : Bool) : Program :=
  (if keep then [] else (cin.toList.map fun d => .CX d t) ++
    [.measureX t [] [.CZ a e]]) ++
  (if sums then [.CCX ctrl e a] else []) ++
  (cin.toList.flatMap fun d => [.CX d a,.CX d e])

/-- The actual forward carry value and both dressed operands, for use
between the forward and backward sweeps of a block. -/
theorem hornerCarryForward_run (a e t : Wire) (cin : Option Wire)
    (distinct : ([a,e,t]++cin.toList).Nodup) (s : State) (m : List Bool)
    (zero : s.basis t=false) :
    run (hornerCarryForward a e t cin) m s=
      ⟨s.phase,writeBit (writeBit (writeBit s.basis t
        (carryBit (s.basis a) (s.basis e) ((cin.map s.basis).getD false))) a
        (s.basis a ^^ (cin.map s.basis).getD false)) e
        (s.basis e ^^ (cin.map s.basis).getD false)⟩ := by
  cases cin with
  | none =>
    simp only [Option.toList_none,List.append_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
    obtain ⟨⟨hae,hat⟩,het⟩ := distinct
    have hea := Ne.symm hae
    have hta := Ne.symm hat
    have hte := Ne.symm het
    cases ha : s.basis a <;> cases he : s.basis e <;>
      simp_all [hornerCarryForward,run,carryBit,writeBit]
    all_goals
      funext q
      by_cases hqa : q=a <;> by_cases hqe : q=e <;> by_cases hqt : q=t <;>
        simp_all [Function.update]
  | some d =>
    simp only [Option.toList_some,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
    obtain ⟨⟨hae,hat,had⟩,⟨het,hed⟩,htd⟩ := distinct
    have hea := Ne.symm hae
    have hta := Ne.symm hat
    have hte := Ne.symm het
    have hda := Ne.symm had
    have hde := Ne.symm hed
    have hdt := Ne.symm htd
    cases ha : s.basis a <;> cases he : s.basis e <;> cases hd : s.basis d <;>
      simp_all [hornerCarryForward,run,carryBit,writeBit,Function.update]
    all_goals
      funext q
      by_cases hqa : q=a <;> by_cases hqe : q=e <;> by_cases hqt : q=t <;>
        simp_all [Function.update]

private theorem cell_none_false_false (ctrl a e t : Wire) 
    (distinct : ([ctrl,a,e,t]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (zero : s.basis t=false) :
    run (hornerCarryForward a e t (none : Option Wire) ++ hornerCarryBackward ctrl a e t (none : Option Wire) false false) m s=
      ⟨s.phase,writeBit (writeBit s.basis t
        (if false then carryBit (s.basis a) (s.basis e) (((none : Option Wire).map s.basis).getD false) else false)) a
        (if false && s.basis ctrl then sumBit (s.basis a) (s.basis e)
          (((none : Option Wire).map s.basis).getD false) else s.basis a)⟩ := by
  simp only [Option.toList_none,List.append_nil,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct⟩,⟨hae,hat⟩,het⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  cases hc : s.basis ctrl <;>
    cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryForward,hornerCarryBackward,run,measureAndCorrect,correct,
      writeBit,Function.update]

private theorem cell_none_false_true (ctrl a e t : Wire) 
    (distinct : ([ctrl,a,e,t]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (zero : s.basis t=false) :
    run (hornerCarryForward a e t (none : Option Wire) ++ hornerCarryBackward ctrl a e t (none : Option Wire) false true) m s=
      ⟨s.phase,writeBit (writeBit s.basis t
        (if true then carryBit (s.basis a) (s.basis e) (((none : Option Wire).map s.basis).getD false) else false)) a
        (if false && s.basis ctrl then sumBit (s.basis a) (s.basis e)
          (((none : Option Wire).map s.basis).getD false) else s.basis a)⟩ := by
  simp only [Option.toList_none,List.append_nil,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct⟩,⟨hae,hat⟩,het⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  cases hc : s.basis ctrl <;>
    cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryForward,hornerCarryBackward,run,
      carryBit,writeBit,Function.update]

private theorem cell_none_true_false (ctrl a e t : Wire) 
    (distinct : ([ctrl,a,e,t]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (zero : s.basis t=false) :
    run (hornerCarryForward a e t (none : Option Wire) ++ hornerCarryBackward ctrl a e t (none : Option Wire) true false) m s=
      ⟨s.phase,writeBit (writeBit s.basis t
        (if false then carryBit (s.basis a) (s.basis e) (((none : Option Wire).map s.basis).getD false) else false)) a
        (if true && s.basis ctrl then sumBit (s.basis a) (s.basis e)
          (((none : Option Wire).map s.basis).getD false) else s.basis a)⟩ := by
  simp only [Option.toList_none,List.append_nil,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct⟩,⟨hae,hat⟩,het⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  cases hc : s.basis ctrl <;>
    cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryForward,hornerCarryBackward,run,measureAndCorrect,correct,
      sumBit,writeBit,Function.update]

private theorem cell_none_true_true (ctrl a e t : Wire) 
    (distinct : ([ctrl,a,e,t]++(none : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (zero : s.basis t=false) :
    run (hornerCarryForward a e t (none : Option Wire) ++ hornerCarryBackward ctrl a e t (none : Option Wire) true true) m s=
      ⟨s.phase,writeBit (writeBit s.basis t
        (if true then carryBit (s.basis a) (s.basis e) (((none : Option Wire).map s.basis).getD false) else false)) a
        (if true && s.basis ctrl then sumBit (s.basis a) (s.basis e)
          (((none : Option Wire).map s.basis).getD false) else s.basis a)⟩ := by
  simp only [Option.toList_none,List.append_nil,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hca,hce,hct⟩,⟨hae,hat⟩,het⟩ := distinct
  have hcar := Ne.symm hca
  have hcer := Ne.symm hce
  have hctr := Ne.symm hct
  have haer := Ne.symm hae
  have hatr := Ne.symm hat
  have hetr := Ne.symm het
  cases hc : s.basis ctrl <;>
    cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryForward,hornerCarryBackward,run,
      carryBit,sumBit,writeBit,Function.update]

private theorem cell_some_false_false (ctrl a e t : Wire) (d : Wire)
    (distinct : ([ctrl,a,e,t]++(some d : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (zero : s.basis t=false) :
    run (hornerCarryForward a e t (some d : Option Wire) ++ hornerCarryBackward ctrl a e t (some d : Option Wire) false false) m s=
      ⟨s.phase,writeBit (writeBit s.basis t
        (if false then carryBit (s.basis a) (s.basis e) (((some d : Option Wire).map s.basis).getD false) else false)) a
        (if false && s.basis ctrl then sumBit (s.basis a) (s.basis e)
          (((some d : Option Wire).map s.basis).getD false) else s.basis a)⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
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
  cases hc : s.basis ctrl <;>
    cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hd : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryForward,hornerCarryBackward,run,measureAndCorrect,correct,
      writeBit,Function.update]

  all_goals
    funext q
    by_cases hqa : q=a <;> by_cases hqe : q=e <;> by_cases hqt : q=t <;>
      simp_all [Function.update]

private theorem cell_some_false_true (ctrl a e t : Wire) (d : Wire)
    (distinct : ([ctrl,a,e,t]++(some d : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (zero : s.basis t=false) :
    run (hornerCarryForward a e t (some d : Option Wire) ++ hornerCarryBackward ctrl a e t (some d : Option Wire) false true) m s=
      ⟨s.phase,writeBit (writeBit s.basis t
        (if true then carryBit (s.basis a) (s.basis e) (((some d : Option Wire).map s.basis).getD false) else false)) a
        (if false && s.basis ctrl then sumBit (s.basis a) (s.basis e)
          (((some d : Option Wire).map s.basis).getD false) else s.basis a)⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
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
  cases hc : s.basis ctrl <;>
    cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hd : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryForward,hornerCarryBackward,run,
      carryBit,writeBit,Function.update]

  all_goals
    funext q
    by_cases hqa : q=a <;> by_cases hqe : q=e <;> by_cases hqt : q=t <;>
      simp_all [Function.update]

private theorem cell_some_true_false (ctrl a e t : Wire) (d : Wire)
    (distinct : ([ctrl,a,e,t]++(some d : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (zero : s.basis t=false) :
    run (hornerCarryForward a e t (some d : Option Wire) ++ hornerCarryBackward ctrl a e t (some d : Option Wire) true false) m s=
      ⟨s.phase,writeBit (writeBit s.basis t
        (if false then carryBit (s.basis a) (s.basis e) (((some d : Option Wire).map s.basis).getD false) else false)) a
        (if true && s.basis ctrl then sumBit (s.basis a) (s.basis e)
          (((some d : Option Wire).map s.basis).getD false) else s.basis a)⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
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
  cases hc : s.basis ctrl <;>
    cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hd : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryForward,hornerCarryBackward,run,measureAndCorrect,correct,
      sumBit,writeBit,Function.update]

  all_goals
    funext q
    by_cases hqa : q=a <;> by_cases hqe : q=e <;> by_cases hqt : q=t <;>
      simp_all [Function.update]

private theorem cell_some_true_true (ctrl a e t : Wire) (d : Wire)
    (distinct : ([ctrl,a,e,t]++(some d : Option Wire).toList).Nodup)
    (s : State) (m : List Bool) (zero : s.basis t=false) :
    run (hornerCarryForward a e t (some d : Option Wire) ++ hornerCarryBackward ctrl a e t (some d : Option Wire) true true) m s=
      ⟨s.phase,writeBit (writeBit s.basis t
        (if true then carryBit (s.basis a) (s.basis e) (((some d : Option Wire).map s.basis).getD false) else false)) a
        (if true && s.basis ctrl then sumBit (s.basis a) (s.basis e)
          (((some d : Option Wire).map s.basis).getD false) else s.basis a)⟩ := by
  simp only [Option.toList_some,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
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
  cases hc : s.basis ctrl <;>
    cases ha : s.basis a <;> cases he : s.basis e <;>
    cases hd : s.basis d <;>
    cases hm : m.head?.getD false <;>
    simp_all [hornerCarryForward,hornerCarryBackward,run,
      carryBit,sumBit,writeBit,Function.update]

  all_goals
    funext q
    by_cases hqa : q=a <;> by_cases hqe : q=e <;> by_cases hqt : q=t <;>
      simp_all [Function.update]

theorem hornerCarryCell_run (ctrl a e t : Wire) (cin : Option Wire)
    (sums keep : Bool) (distinct : ([ctrl,a,e,t]++cin.toList).Nodup)
    (s : State) (m : List Bool) (zero : s.basis t=false) :
    run (hornerCarryForward a e t cin ++ hornerCarryBackward ctrl a e t cin sums keep) m s=
      ⟨s.phase,writeBit (writeBit s.basis t
        (if keep then carryBit (s.basis a) (s.basis e) ((cin.map s.basis).getD false) else false)) a
        (if sums && s.basis ctrl then sumBit (s.basis a) (s.basis e)
          ((cin.map s.basis).getD false) else s.basis a)⟩ := by
  cases cin <;> cases sums <;> cases keep
  · exact cell_none_false_false ctrl a e t distinct s m zero
  · exact cell_none_false_true ctrl a e t distinct s m zero
  · exact cell_none_true_false ctrl a e t distinct s m zero
  · exact cell_none_true_true ctrl a e t distinct s m zero
  · exact cell_some_false_false ctrl a e t _ distinct s m zero
  · exact cell_some_false_true ctrl a e t _ distinct s m zero
  · exact cell_some_true_false ctrl a e t _ distinct s m zero
  · exact cell_some_true_true ctrl a e t _ distinct s m zero

theorem hornerCarryCell_counts (ctrl a e t : Wire) (cin : Option Wire) (sums keep : Bool) :
    toffoliCount (hornerCarryForward a e t cin ++ hornerCarryBackward ctrl a e t cin sums keep)=
      1+(if sums then 1 else 0) ∧
    measurementCount (hornerCarryForward a e t cin ++ hornerCarryBackward ctrl a e t cin sums keep)=
      if keep then 0 else 1 := by
  cases cin <;> cases sums <;> cases keep <;> exact ⟨rfl,rfl⟩


end ECDSAAdd.Arithmetic.Paper935
