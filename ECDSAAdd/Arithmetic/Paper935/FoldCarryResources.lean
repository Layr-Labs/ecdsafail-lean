import ECDSAAdd.Arithmetic.Paper935.FoldCarryForward
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum

theorem foldCarryForward_counts (bit : Bool) (control data target : Wire) (cin : Option Wire) :
    toffoliCount (foldCarryForward bit control data target cin)=(if bit || cin.isSome then 1 else 0) ∧
    measurementCount (foldCarryForward bit control data target cin)=0 := by
  cases cin <;> cases bit <;> simp [foldCarryForward,toffoliCount,measurementCount]

theorem foldCarryBackward_counts (bit : Bool) (control data target : Wire) (cin : Option Wire)
    (sums keep : Bool) :
    toffoliCount (foldCarryBackward bit control data target cin sums keep)=0 ∧
    measurementCount (foldCarryBackward bit control data target cin sums keep)=
      (if !keep && (bit || cin.isSome) then 1 else 0) := by
  cases cin <;> cases bit <;> cases sums <;> cases keep <;>
    simp [foldCarryBackward,toffoliCount,measurementCount]

theorem foldCarry_support (bit : Bool) (control data target : Wire) (cin : Option Wire)
    (sums keep : Bool) :
    wires (foldCarryForward bit control data target cin ++ foldCarryBackward bit control data target cin sums keep) ⊆
      ([control,data,target]++cin.toList).toFinset := by
  cases cin <;> cases bit <;> cases sums <;> cases keep <;>
    simp [foldCarryForward,foldCarryBackward,wires,Instr.wires,correctionWires,
      Finset.insert_subset_iff]

theorem foldCarry_physical (bit : Bool) (control data target : Wire) (cin : Option Wire)
    (sums keep : Bool) (hn : ([control,data,target]++cin.toList).Nodup) :
    GatePhysical (foldCarryForward bit control data target cin ++ foldCarryBackward bit control data target cin sums keep) := by
  cases cin <;> cases bit <;> cases sums <;> cases keep <;>
    simp_all [foldCarryForward,foldCarryBackward,GatePhysical,PhysicalInstr,ProperGate,List.nodup_cons,ne_comm]

end ECDSAAdd.Arithmetic.Paper935
