import ECDSAAdd.Arithmetic.MappedAdder
import ECDSAAdd.Framework.WireRename

set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def literalConstSum (bit : Bool) (x cin : Wire) : Program :=
  (if bit then [.X x] else [])++[.CX cin x]

/-- Updated-X carry predicates, exactly matching the direct interval adder. -/
def literalConstCarry (bit : Bool) (x cin cout : Wire) : Program :=
  if bit then [.X cout,.X cin,.CCX cin x cout,.X cin]
  else [.X x,.CCX cin x cout,.X x]

def literalConstStep (bit : Bool) (x cin cout : Wire) : Program :=
  literalConstSum bit x cin++literalConstCarry bit x cin cout

def literalConstErase (bit : Bool) (x cin cout one : Wire) : Program :=
  if bit then [.X one,.measureX cout [] [.Z one,.Z x,.CZ x cin],.X one]
  else [.measureX cout [] [.Z cin,.CZ x cin]]

def literalCarryPredicate (bit x cin : Bool) : Bool :=
  if bit then !x || cin else !x && cin

theorem literalConstSum_correct (bit : Bool) (x cin : Wire) (hn : x≠cin)
    (s : State) (m : List Bool) :
    run (literalConstSum bit x cin) m s=
      ⟨s.phase,writeBit s.basis x (sumBit (s.basis x) bit (s.basis cin))⟩ := by
  cases bit <;> simp only [literalConstSum,Bool.false_eq_true,if_false,if_true,
    List.nil_append,List.singleton_append,run]
  all_goals
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q=x <;> simp [writeBit,Function.update,hq,Ne.symm hn,sumBit]

theorem literalConstStep_correct (bit : Bool) (x cin cout : Wire)
    (hn : [x,cin,cout].Nodup) (s : State) (m : List Bool) (hc : s.basis cout=false) :
    run (literalConstStep bit x cin cout) m s=
      ⟨s.phase,writeBit (writeBit s.basis x (sumBit (s.basis x) bit (s.basis cin)))
        cout (carryBit (s.basis x) bit (s.basis cin))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hxi,hxc⟩,hic⟩ := hn
  have hix := Ne.symm hxi
  have hcx := Ne.symm hxc
  have hci := Ne.symm hic
  cases bit <;> cases hx : s.basis x <;> cases hi : s.basis cin
  all_goals
    simp only [literalConstStep,literalConstSum,literalConstCarry,
      Bool.false_eq_true,if_false,if_true,List.cons_append,List.nil_append,run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqx : q=x <;> by_cases hqi : q=cin <;> by_cases hqc : q=cout <;>
      simp_all [writeBit,Function.update,sumBit,carryBit]

theorem literalCarryPredicate_sum (A B C : Bool) :
    literalCarryPredicate B (sumBit A B C) C=carryBit A B C := by
  cases A <;> cases B <;> cases C <;> rfl

/-- One supplies the literal phase correction only during the measurement.
Every record, including outcome one, restores phase and the clean One wire. -/
theorem literalConstErase_correct (bit : Bool) (x cin cout one : Wire)
    (hn : [one,x,cin,cout].Nodup) (s : State) (m : List Bool)
    (ho : s.basis one=false)
    (hc : s.basis cout=literalCarryPredicate bit (s.basis x) (s.basis cin)) :
    run (literalConstErase bit x cin cout one) m s=
      ⟨s.phase,writeBit s.basis cout false⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hox,hoi,hoc⟩,⟨hxi,hxc⟩,hic⟩ := hn
  have hxo := Ne.symm hox
  have hio := Ne.symm hoi
  have hco := Ne.symm hoc
  cases bit <;> cases hm : m.headD false <;> cases hx : s.basis x <;> cases hi : s.basis cin
  all_goals
    simp only [literalCarryPredicate,Bool.false_eq_true,if_false,if_true,
      Bool.not_false,Bool.not_true,Bool.false_and,Bool.true_and,Bool.false_or,Bool.true_or] at hc
    apply State.extensionality
    · simp_all [literalConstErase,run,measureAndCorrect,correct,writeBit,Function.update]
    · funext q
      by_cases hqo : q=one <;> by_cases hqc : q=cout <;>
        simp_all [literalConstErase,run,measureAndCorrect,correct,writeBit,Function.update]

theorem literalConstCell_counts (bit : Bool) (x cin cout one : Wire) :
    toffoliCount (literalConstStep bit x cin cout)=1 ∧
    measurementCount (literalConstStep bit x cin cout)=0 ∧
    toffoliCount (literalConstErase bit x cin cout one)=0 ∧
    measurementCount (literalConstErase bit x cin cout one)=1 ∧
    toffoliCount (literalConstSum bit x cin)=0 ∧
    measurementCount (literalConstSum bit x cin)=0 := by
  cases bit <;> simp [literalConstStep,literalConstSum,literalConstCarry,literalConstErase,
    toffoliCount,measurementCount]

theorem literalConstCell_wires (bit : Bool) (x cin cout one : Wire) :
    wires (literalConstStep bit x cin cout)⊆[one,cin,x,cout].toFinset ∧
    wires (literalConstErase bit x cin cout one)⊆[one,cin,x,cout].toFinset ∧
    wires (literalConstSum bit x cin)⊆[one,cin,x,cout].toFinset := by
  cases bit <;> simp [literalConstStep,literalConstSum,literalConstCarry,literalConstErase,
    wires,Instr.wires,correctionWires,Finset.subset_iff]

end ECDSAAdd.Arithmetic
