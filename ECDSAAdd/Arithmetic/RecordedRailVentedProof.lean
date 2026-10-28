import ECDSAAdd.Arithmetic.RecordedRailVentedFrame

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailVented
open RecordedRailCarry RecordedRailRipple

/-- Exact complete frame of the actual vented stream. The carry-out is a real
retained output, and every owned carry is returned to its initial zero state. -/
theorem vented_frame (a b work : List Wire) (shape : Shape a b work)
    (prev : Option Wire) (cout : Wire) (bits : BasisState) (phase : Bool)
    (m : List Bool) (cursor : Nat)
    (nd : (prev.toList++a++b++work++[cout]).Nodup)
    (clean : ∀q∈work,bits q=false) (coutClean : bits cout=false) :
    let out := runWithTape (vented a b prev work cout) m cursor ⟨phase,bits⟩
    out.phase=phase ∧
    regValue (b++[cout]) out.basis=regValue a bits+regValue b bits+
      (incomingValue prev bits).toNat ∧
    (∀q,q∉b++[cout] → out.basis q=bits q) := by
  induction shape generalizing prev bits phase cursor with
  | one a b =>
    have hn : (prev.toList++[a,b,cout]).Nodup := by
      simpa only [List.append_assoc,List.append_nil,List.cons_append,List.nil_append] using nd
    simpa only [vented,List.cons_append,List.nil_append] using
      top_frame a b cout prev hn bits phase m cursor coutClean
  | step a0 a1 b0 b1 c as bs cs shape ih =>
    let A := a1::as
    let B := b1::bs
    let C := carryFn (bits a0) (bits b0) (incomingValue prev bits)
    let cb := computedBits a0 b0 c prev bits
    obtain ⟨hn,htnd,haB,hbB,hcB,haway,hprev⟩ :=
      step_layout a0 b0 c cout A B cs prev nd
    have ch := computed_head a0 b0 c prev bits hn
    have hsame : ∀q∈A++B++cs++[cout],cb q=bits q := by
      intro q hq
      obtain ⟨hqa,hqb,hqc⟩ := haway q hq
      simp [cb,computedBits,writeBit,hqa,hqb,hqc]
    have hca : ∀q∈A,cb q=bits q := fun q hq => hsame q (by simp [hq])
    have hcb : ∀q∈B,cb q=bits q := fun q hq => hsame q (by simp [hq])
    have hclean : ∀q∈cs,cb q=false := by
      intro q hq
      rw [hsame q (by simp [hq])]
      exact clean q (by simp [hq])
    have hc0 : bits c=false := clean c (by simp)
    have hc1 : cb c=C := ch.2.2.1
    have hcout : cb cout=false := (hsame cout (by simp)).trans coutClean
    let t := runWithTape (vented A B (some c) cs cout) m cursor ⟨phase,cb⟩
    have htail := ih (some c) cb phase cursor htnd hclean hcout
    simp only [incomingValue,hc1] at htail
    change t.phase=phase ∧
      regValue (B++[cout]) t.basis=regValue A cb+regValue B cb+C.toNat ∧
      (∀q,q∉B++[cout] → t.basis q=cb q) at htail
    obtain ⟨htphase,htsum,htoutside⟩ := htail
    have htA : t.basis a0=(bits a0 ^^ incomingValue prev bits) :=
      (htoutside a0 haB).trans ch.1
    have htB : t.basis b0=(bits b0 ^^ incomingValue prev bits) :=
      (htoutside b0 hbB).trans ch.2.1
    have htC : t.basis c=C := (htoutside c hcB).trans hc1
    have htP : incomingValue prev t.basis=incomingValue prev bits := by
      calc
        incomingValue prev t.basis=incomingValue prev cb := by
          cases prev with
          | none => rfl
          | some p => exact htoutside p (hprev p (by simp))
        _=incomingValue prev bits := ch.2.2.2
    have hcarry : t.basis c=((t.basis a0 && t.basis b0) ^^ incomingValue prev t.basis) := by
      rw [htC,htA,htB,htP]
      rfl
    have hcompute : runWithTape (embedRecorded (carryStep a0 b0 prev c)) m cursor
        ⟨phase,bits⟩=⟨phase,cb⟩ := by
      rw [runWithTape_embedRecorded,carryStep_state a0 b0 c prev hn bits phase _ hc0]
    let outBits := writeBit (writeBit (writeBit t.basis c false)
      a0 (t.basis a0 ^^ incomingValue prev t.basis))
      b0 (t.basis b0 ^^ (t.basis a0 ^^ incomingValue prev t.basis))
    have hrun : runWithTape (vented (a0::A) (b0::B) prev (c::cs) cout) m cursor
        ⟨phase,bits⟩=⟨phase,outBits⟩ := by
      rw [show vented (a0::A) (b0::B) prev (c::cs) cout=
        embedRecorded (carryStep a0 b0 prev c) ++ vented A B (some c) cs cout ++
          embedRecorded (unwindStep a0 b0 prev c) from rfl]
      simp only [runWithTape_append,recordedMeasurementCount_append,
        carry_measurements,Nat.add_zero,Nat.zero_add]
      rw [hcompute]
      change runWithTape (embedRecorded (unwindStep a0 b0 prev c)) m
        (cursor+recordedMeasurementCount (vented A B (some c) cs cout)) t=_
      rw [runWithTape_embedRecorded]
      change run (unwindStep a0 b0 prev c) _ ⟨t.phase,t.basis⟩=_
      rw [unwind_state a0 b0 c prev hn t.basis t.phase _ hcarry,htphase]
    dsimp only
    rw [hrun]
    have hout := unwound_head a0 b0 c prev bits t.basis hn htA htB htP
    change outBits a0=bits a0 ∧
      outBits b0=((bits b0 ^^ bits a0) ^^ incomingValue prev bits) ∧ outBits c=false at hout
    have htailout : ∀q∈A++B++cs++[cout],outBits q=t.basis q := by
      intro q hq
      obtain ⟨hqa,hqb,hqc⟩ := haway q hq
      simp [outBits,writeBit,hqa,hqb,hqc]
    refine ⟨rfl,?_,?_⟩
    · have hx := regValue_congr A cb bits hca
      have hy := regValue_congr B cb bits hcb
      have hz := regValue_congr (B++[cout]) outBits t.basis (by
        intro q hq
        apply htailout
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
        tauto)
      change regValue (b0::(B++[cout])) outBits=
        regValue (a0::A) bits+regValue (b0::B) bits+(incomingValue prev bits).toNat
      rw [reg_cons b0 (B++[cout]) outBits,reg_cons a0 A bits,reg_cons b0 B bits]
      rw [hout.2.1,hz,htsum,hx,hy]
      exact wide_step (bits a0) (bits b0) (incomingValue prev bits)
        (regValue A bits) (regValue B bits)
    · intro q hq
      have hqb : q≠b0 := by intro h; exact hq (by simp [h])
      have hqB : q∉B++[cout] := by
        intro h
        exact hq (by simpa only [B] using List.mem_cons_of_mem b0 h)
      by_cases hqa : q=a0
      · subst q; exact hout.1
      by_cases hqc : q=c
      · subst q; exact hout.2.2.trans hc0.symm
      simp [outBits,writeBit,hqa,hqb,hqc,htoutside q hqB,cb,computedBits]

end ECDSAAdd.Arithmetic.RecordedRailVented
#print axioms ECDSAAdd.Arithmetic.RecordedRailVented.vented_frame
