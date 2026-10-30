import ECDSAAdd.Submission.Entrant.NewEncodedFrame
import ECDSAAdd.Submission.Entrant.ParityCodec5New

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.NewHistory5
open Arithmetic Challenge Baselines

theorem decode_metrics (w : Nat → Wire) (start : Nat) :
    toffoliCount (decode w start)=toffoliCount (History5.decode w start) ∧
    measurementCount (decode w start)=measurementCount (History5.decode w start) ∧
    gateSlots (decode w start)=gateSlots (History5.decode w start)+2 := by
  have n := decode_counts w start
  have o := History5.decode_counts w start
  refine ⟨by omega,by omega,?_⟩
  change gateSlots (ParityCodec5New.decodeAt (History5.historyMap w start))=
    gateSlots (MeasuredCodec5.decodeAt (History5.historyMap w start))+2
  rw [(ParityCodec5New.slotsAt _).2,(MeasuredCodec5.slotsAt _).2]

theorem decodeBefore_metrics (w : Nat → Wire) (i : Nat) :
    toffoliCount (decodeBefore w i)=toffoliCount (History5.decodeBefore w i) ∧
    measurementCount (decodeBefore w i)=measurementCount (History5.decodeBefore w i) ∧
    gateSlots (decodeBefore w i)=gateSlots (History5.decodeBefore w i)+
      2*(if History5.packDue i then 1 else 0) := by
  change toffoliCount (if History5.packDue i then decode w (i-5) else [])=
      toffoliCount (if History5.packDue i then History5.decode w (i-5) else []) ∧
    measurementCount (if History5.packDue i then decode w (i-5) else [])=
      measurementCount (if History5.packDue i then History5.decode w (i-5) else []) ∧
    gateSlots (if History5.packDue i then decode w (i-5) else [])=
      gateSlots (if History5.packDue i then History5.decode w (i-5) else [])+
        2*(if History5.packDue i then 1 else 0)
  cases due : History5.packDue i
  · simp only [due,Bool.false_eq_true,if_false,mul_zero,add_zero]
    exact ⟨trivial,trivial,trivial⟩
  · simpa only [due,if_true,mul_one] using
      decode_metrics w (i-5)

end ECDSAAdd.Entrant.NewHistory5

namespace ECDSAAdd.Entrant.ParityCodec5New
open Arithmetic Challenge Baselines

theorem first_decode_metrics (f : Fin 10 → Wire) :
    toffoliCount (decodeAtFirst f)=toffoliCount (FirstNonzeroCodec.decodeAtFirst f) ∧
    measurementCount (decodeAtFirst f)=measurementCount (FirstNonzeroCodec.decodeAtFirst f) ∧
    gateSlots (decodeAtFirst f)=gateSlots (FirstNonzeroCodec.decodeAtFirst f)+2 := by
  have n := first_countsAt f
  have o := FirstNonzeroCodec.counts
  have ns := first_slotsAt f
  have os := FirstNonzeroCodec.restricted_slots
  simp only [FirstNonzeroCodec.decodeAtFirst,renameProgram_counts,rename_gateSlots]
  exact ⟨n.2.1.trans o.2.1.symm,n.2.2.2.trans o.2.2.2.symm,by omega⟩

end ECDSAAdd.Entrant.ParityCodec5New
