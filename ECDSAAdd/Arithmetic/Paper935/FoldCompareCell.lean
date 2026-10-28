import ECDSAAdd.Arithmetic.Paper935.FoldBlockOverflow

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Author `_clt_fwd_cin` cell. Data is complemented by the caller when this
carry is used to compute a borrow. -/
def foldCompareForward (bit : Bool) (data target : Wire) (cin : Option Wire) : Program :=
  if bit then
    match cin with
    | none => [.CX data target]
    | some d => [.X data,.X d,.CCX data d target,.X target,.X d,.X data]
  else cin.toList.map fun d => .CCX data d target

/-- Author `_clt_bwd_cin` cell with immediate measurement correction. -/
def foldCompareBackward (bit : Bool) (data target : Wire) (cin : Option Wire) : Program :=
  if bit then
    match cin with
    | none => [.measureX target [] [.Z data]]
    | some d => [.X target,.X data,.X d,.measureX target [] [.CZ data d],.X d,.X data]
  else cin.toList.map fun d => .measureX target [] [.CZ data d]

theorem foldCompareForward_run (bit : Bool) (data target : Wire) (cin : Option Wire)
    (hn : ([data,target]++cin.toList).Nodup) (s : State) (m : List Bool)
    (clean : s.basis target=false) :
    run (foldCompareForward bit data target cin) m s=
      ⟨s.phase,writeBit s.basis target (carryBit (s.basis data) bit ((cin.map s.basis).getD false))⟩ := by
  cases cin with
  | none =>
    have hd : data≠target := by simpa using hn
    have ht := Ne.symm hd
    cases bit <;> cases hx : s.basis data <;>
      simp_all [foldCompareForward,run,carryBit,writeBit]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=target <;> simp_all [Function.update]
  | some d =>
    simp only [Option.toList_some,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
      List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
    obtain ⟨⟨hxt,hxd⟩,htd⟩ := hn
    have htx := Ne.symm hxt
    have hdx := Ne.symm hxd
    have hdt := Ne.symm htd
    cases bit <;> cases hx : s.basis data <;> cases hi : s.basis d <;>
      simp_all [foldCompareForward,run,carryBit,writeBit,Function.update]
    all_goals
      funext q
      by_cases hq : q=target <;> by_cases hx : q=data <;> by_cases hi : q=d <;>
        simp_all [Function.update]

theorem foldCompareBackward_run (bit : Bool) (data target : Wire) (cin : Option Wire)
    (hn : ([data,target]++cin.toList).Nodup) (s : State) (m : List Bool)
    (known : s.basis target=carryBit (s.basis data) bit ((cin.map s.basis).getD false)) :
    run (foldCompareBackward bit data target cin) m s=⟨s.phase,writeBit s.basis target false⟩ := by
  cases cin with
  | none =>
    have hd : data≠target := by simpa using hn
    have ht := Ne.symm hd
    cases bit <;> cases hx : s.basis data <;> cases hm : m.head?.getD false <;>
      simp_all [foldCompareBackward,run,measureAndCorrect,correct,carryBit,writeBit,Function.update]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=target <;> simp_all [Function.update]
  | some d =>
    simp only [Option.toList_some,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
      List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at hn
    obtain ⟨⟨hxt,hxd⟩,htd⟩ := hn
    have htx := Ne.symm hxt
    have hdx := Ne.symm hxd
    have hdt := Ne.symm htd
    cases bit <;> cases hx : s.basis data <;> cases hi : s.basis d <;> cases hm : m.head?.getD false <;>
      simp_all [foldCompareBackward,run,measureAndCorrect,correct,carryBit,writeBit,Function.update]
    all_goals
      funext q
      by_cases hq : q=target <;> by_cases hx : q=data <;> by_cases hi : q=d <;>
        simp_all [Function.update]

theorem foldCompareForward_counts (bit : Bool) (data target : Wire) (cin : Option Wire) :
    toffoliCount (foldCompareForward bit data target cin)=(if cin.isSome then 1 else 0) ∧
    measurementCount (foldCompareForward bit data target cin)=0 := by
  cases cin <;> cases bit <;> simp [foldCompareForward,toffoliCount,measurementCount]

theorem foldCompareBackward_counts (bit : Bool) (data target : Wire) (cin : Option Wire) :
    toffoliCount (foldCompareBackward bit data target cin)=0 ∧
    measurementCount (foldCompareBackward bit data target cin)=(if bit || cin.isSome then 1 else 0) := by
  cases cin <;> cases bit <;> simp [foldCompareBackward,toffoliCount,measurementCount]

theorem foldCompare_support (bit : Bool) (data target : Wire) (cin : Option Wire) :
    wires (foldCompareForward bit data target cin ++ foldCompareBackward bit data target cin) ⊆
      ([data,target]++cin.toList).toFinset := by
  cases cin <;> cases bit <;>
    simp [foldCompareForward,foldCompareBackward,wires,Instr.wires,correctionWires,Finset.insert_subset_iff]

theorem foldCompare_physical (bit : Bool) (data target : Wire) (cin : Option Wire)
    (hn : ([data,target]++cin.toList).Nodup) :
    GatePhysical (foldCompareForward bit data target cin ++ foldCompareBackward bit data target cin) := by
  cases cin <;> cases bit <;>
    simp_all [foldCompareForward,foldCompareBackward,GatePhysical,
      ECDSAAdd.RecordedQuantum.PhysicalInstr,ProperGate,List.nodup_cons,ne_comm]

end ECDSAAdd.Arithmetic.Paper935
