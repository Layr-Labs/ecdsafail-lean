import ECDSAAdd.Arithmetic.RecordedRailApplyLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply
open RecordedRailRipple ECDSAAdd.Math.RecordedCarryWordMirror

/-- Actual Defer, target complement, normal wrapped Apply using absolute old
records, and target complement back restore the complete original State.
Every fresh MX outcome is independent of the seven saved forward outcomes. -/
theorem correct_pair (a b forwardBank mirrorBank : List Wire) (cin even odd : Wire)
    (original : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat)
    (ready : Ready a b forwardBank mirrorBank cin even odd original) :
    runWithTape (pair a b forwardBank mirrorBank cin even odd cursor) m cursor ⟨phase,original⟩=
      ⟨phase,original⟩ := by
  have layout := ready.1
  obtain ⟨aw,bw,fw,mw,nd,smallND,subset⟩ := layout
  obtain ⟨bND,cinAway,sourceAway,bankAway⟩ := data_separation a b mirrorBank cin nd
  have forwardReady := forward_ready a b forwardBank mirrorBank cin even odd original ready
  let f := runWithTape (RecordedRailDefer.forward32 a b forwardBank cin even odd) m cursor ⟨phase,original⟩
  have forward := RecordedRailDefer.correct32 a b forwardBank cin even odd original phase m cursor forwardReady
  obtain ⟨fphase,fvalue,foutside,fbank,feven,fodd⟩ := forward
  change f.phase=(phase ^^ RecordedRailDefer.debt32 a b cin original m cursor) at fphase
  change regValue b f.basis=(regValue a original+regValue b original+(original cin).toNat)%2^256 at fvalue
  have fcin : f.basis cin=original cin := foutside cin cinAway
  have fsource : a.map f.basis=a.map original := by
    apply List.map_congr_left
    intro q hq
    exact foutside q (sourceAway q hq)
  have fsum : b.map f.basis=sumBits (a.map original) (b.map original) (original cin) :=
    mapped_sum a b original f.basis (original cin) (by omega) (by simpa only [bw] using fvalue)
  let rbits : BasisState := fun q => if q∈b then !f.basis q else f.basis q
  have rsource : a.map rbits=a.map original := by
    apply List.map_congr_left
    intro q hq
    simp only [rbits,if_neg (sourceAway q hq)]
    exact foutside q (sourceAway q hq)
  have rtarget : b.map rbits=(sumBits (a.map original) (b.map original) (original cin)).map (!·) := by
    rw [←fsum,List.map_map]
    apply List.map_congr_left
    intro q hq
    simp [rbits,hq]
  have rcin : rbits cin=original cin := by simp [rbits,cinAway,fcin]
  have rclean : ∀q∈mirrorBank,rbits q=false := by
    intro q hq
    simp only [rbits,if_neg (bankAway q hq)]
    rw [foutside q (bankAway q hq)]
    exact ready.2 q hq
  have aligned := aligned_mirror a b forwardBank mirrorBank cin even odd ready.1 cursor
  have shape := RecordedRailRipple.aligned_shape a b mirrorBank (oldSlots cursor) aligned
  have mirrorDebt := RecordedRailRipple.mirror_phaseDebt a b mirrorBank (oldSlots cursor)
    shape original rbits m (original cin) rsource rtarget
  have originalDebt := debt_forward a b mirrorBank cin original m cursor aw bw aligned
  have debtEq : phaseDebt a b (incomingValue (some cin) rbits) (oldSlots cursor) rbits m=
      RecordedRailDefer.debt32 a b cin original m cursor := by
    simp only [incomingValue,rcin]
    exact mirrorDebt.trans originalDebt
  have rippleReady : RecordedRailRipple.Ready a b (some cin) mirrorBank (oldSlots cursor) rbits (cursor+254) :=
    ⟨aligned,nd,rclean,slots_earlier cursor⟩
  let v := runWithTape (RecordedRailRipple.ripple a b (some cin) mirrorBank (oldSlots cursor))
    m (cursor+254) ⟨f.phase,rbits⟩
  have ripple := RecordedRailRipple.unsignedContract_of_aligned a b mirrorBank (oldSlots cursor) aligned
    (some cin) rbits phase m (cursor+254) rippleReady
  rw [debtEq,←fphase] at ripple
  obtain ⟨vphase,vsource,vvalue,voutside,vwork⟩ := ripple
  change v.phase=phase at vphase
  change regValue b v.basis=(regValue a rbits+regValue b rbits+(rbits cin).toNat)%2^b.length at vvalue
  have vsum : b.map v.basis=sumBits (a.map rbits) (b.map rbits) (rbits cin) :=
    mapped_sum a b rbits v.basis (rbits cin) (by omega) vvalue
  rw [rsource,rtarget,rcin,mirror_sum _ _ _ (by simpa using (show a.length=b.length from by omega))] at vsum
  let finalBits : BasisState := fun q => if q∈b then !v.basis q else v.basis q
  have finalMap : b.map finalBits=b.map original := by
    calc
      b.map finalBits=(b.map v.basis).map (!·) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro q hq
        simp [finalBits,hq]
      _=(b.map original).map ((!·) ∘ (!·)) := by rw [vsum,List.map_map]
      _=b.map original := by simp
  have targetSame : ∀q∈b,finalBits q=original q := by
    apply (regValue_eq_iff b finalBits original).mp
    have h := congrArg wordValue finalMap
    simpa only [wordValue_map] using h
  have finalSame : finalBits=original := by
    funext q
    by_cases hq : q∈b
    · exact targetSame q hq
    · have hv := voutside q hq
      change v.basis q=rbits q at hv
      simp only [finalBits,if_neg hq,hv,rbits,if_neg hq]
      exact foutside q hq
  have firstFlip : runWithTape (embedRecorded (notRegister b)) m (cursor+254) f=⟨f.phase,rbits⟩ :=
    flip_state b bND m (cursor+254) f
  have lastFlip (k : Nat) : runWithTape (embedRecorded (notRegister b)) m k v=⟨phase,original⟩ := by
    rw [flip_state b bND m k v,vphase]
    change (⟨phase,finalBits⟩ : State)=(⟨phase,original⟩ : State)
    rw [finalSame]
  have fcounts := RecordedRailDefer.forward32_counts a b forwardBank cin even odd aw bw fw
  rw [pair,runWithTape_append,fcounts.2]
  change runWithTape (program a b mirrorBank cin cursor) m (cursor+254) f=_
  rw [program,runWithTape_append,runWithTape_append]
  simp only [recordedMeasurementCount_append,flip_measurements,Nat.add_zero,Nat.zero_add]
  rw [firstFlip]
  change runWithTape (embedRecorded (notRegister b)) m
    (cursor+254+recordedMeasurementCount (RecordedRailRipple.ripple a b (some cin) mirrorBank (oldSlots cursor))) v=_
  exact lastFlip _

end ECDSAAdd.Arithmetic.RecordedRailApply
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply.correct_pair
