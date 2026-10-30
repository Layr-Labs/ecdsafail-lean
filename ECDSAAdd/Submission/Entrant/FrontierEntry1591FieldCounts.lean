import ECDSAAdd.Submission.Entrant.FrontierEntry1591Field

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.FrontierEntry1591Field
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  entryHosted exitHosted

theorem entry_counts : toffoliCount entry=toffoliCount entryHosted ∧
    measurementCount entry=measurementCount entryHosted ∧
    Challenge.gateSlots entry=Challenge.gateSlots entryHosted+1632 := by
  have result := ParityField1591.counts controls work host entryHosted
  have size : 2*controls.length=1632 := by rw [controls_length]
  exact ⟨result.1,result.2.1,result.2.2.trans
    (congrArg (fun n => Challenge.gateSlots entryHosted+n) size)⟩

theorem exit_counts : toffoliCount exit=toffoliCount exitHosted ∧
    measurementCount exit=measurementCount exitHosted ∧
    Challenge.gateSlots exit=Challenge.gateSlots exitHosted+1632 := by
  have result := ParityField1591.counts controls work host exitHosted
  have size : 2*controls.length=1632 := by rw [controls_length]
  exact ⟨result.1,result.2.1,result.2.2.trans
    (congrArg (fun n => Challenge.gateSlots exitHosted+n) size)⟩

end ECDSAAdd.Entrant.FrontierEntry1591Field
