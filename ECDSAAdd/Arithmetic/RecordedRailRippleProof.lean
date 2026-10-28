import ECDSAAdd.Arithmetic.RecordedRailRippleProofBase
import ECDSAAdd.Arithmetic.RecordedRailRippleProofLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailRipple
open RecordedRailCarry

/-- Actual emitted recursion, with original-operand phase debt, preserves every
spectator and returns the unsigned sum. Causality is a separate layout property. -/
theorem ripple_frame (a b work : List Wire) (slots : List (Option Nat))
    (shape : Shape a b work slots) (prev : Option Wire)
    (bits : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat)
    (nd : (prev.toList++a++b++work).Nodup)
    (clean : ∀q∈work,bits q=false) :
    let out := runWithTape (ripple a b prev work slots) m cursor
      ⟨phase ^^ phaseDebt a b (incomingValue prev bits) slots bits m,bits⟩
    out.phase=phase ∧
    regValue b out.basis=(regValue a bits+regValue b bits+
      (incomingValue prev bits).toNat)%2^b.length ∧
    (∀q,q∉b → out.basis q=bits q) := by
  induction shape generalizing prev bits phase cursor with
  | one a b =>
    have hn : (prev.toList++[a,b]).Nodup := by
      simpa only [List.append_assoc,List.append_nil,List.cons_append,List.nil_append] using nd
    simpa [phaseDebt] using one_frame a b prev hn bits phase m cursor
  | two a0 a1 b0 b1 =>
    have hn : (prev.toList++[a0,a1,b0,b1]).Nodup := by
      simpa only [List.append_assoc,List.append_nil,List.cons_append,List.nil_append] using nd
    simpa [phaseDebt] using two_frame a0 a1 b0 b1 prev hn bits phase m cursor
  | step a0 a1 a2 b0 b1 b2 c as bs cs d ds shape ih =>
    let A := a1::a2::as
    let B := b1::b2::bs
    let C := carryFn (bits a0) (bits b0) (incomingValue prev bits)
    let D := recordDebt d m C
    let cb := computedBits a0 b0 c prev bits
    obtain ⟨hn,htnd,haB,hbB,hcB,haway,hprev⟩ :=
      step_layout a0 b0 c A B cs prev nd
    have ch := computed_head a0 b0 c prev bits hn
    have hsame : ∀q∈A++B++cs,cb q=bits q := by
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
    have hd := phaseDebt_congr A B C ds cb bits m hca hcb
    let t := runWithTape (ripple A B (some c) cs ds) m cursor
      ⟨(phase ^^ D) ^^ phaseDebt A B C ds cb m,cb⟩
    have htail := ih (some c) cb (phase ^^ D) cursor htnd hclean
    simp only [incomingValue,hc1] at htail
    change t.phase=(phase ^^ D) ∧
      regValue B t.basis=(regValue A cb+regValue B cb+C.toNat)%2^B.length ∧
      (∀q,q∉B → t.basis q=cb q) at htail
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
        ⟨phase ^^ phaseDebt (a0::A) (b0::B) (incomingValue prev bits) (d::ds) bits m,bits⟩=
        ⟨(phase ^^ D) ^^ phaseDebt A B C ds cb m,cb⟩ := by
      rw [runWithTape_embedRecorded,carryStep_state a0 b0 c prev hn bits _ _ hc0]
      apply State.extensionality
      · change (phase ^^ (D ^^ phaseDebt A B C ds bits m))=
          ((phase ^^ D) ^^ phaseDebt A B C ds cb m)
        rw [hd]
        exact (Bool.xor_assoc phase D (phaseDebt A B C ds bits m)).symm
      · rfl
    have hold : runWithTape (oldCorrection c d) m
        (cursor+recordedMeasurementCount (ripple A B (some c) cs ds)) t=⟨phase,t.basis⟩ := by
      have he : t=⟨phase ^^ recordDebt d m (t.basis c),t.basis⟩ := by
        apply State.extensionality
        · rw [htphase,htC]
        · rfl
      rw [he,oldCorrection_state]
    let outBits := writeBit (writeBit (writeBit t.basis c false)
      a0 (t.basis a0 ^^ incomingValue prev t.basis))
      b0 (t.basis b0 ^^ (t.basis a0 ^^ incomingValue prev t.basis))
    have hrun : runWithTape (ripple (a0::A) (b0::B) prev (c::cs) (d::ds)) m cursor
        ⟨phase ^^ phaseDebt (a0::A) (b0::B) (incomingValue prev bits) (d::ds) bits m,bits⟩=
        ⟨phase,outBits⟩ := by
      rw [show ripple (a0::A) (b0::B) prev (c::cs) (d::ds)=
        embedRecorded (carryStep a0 b0 prev c) ++ ripple A B (some c) cs ds ++
          oldCorrection c d ++ embedRecorded (unwindStep a0 b0 prev c) from rfl]
      simp only [runWithTape_append,recordedMeasurementCount_append,
        carry_measurements,(oldCorrection_counts c d).2,Nat.add_zero,Nat.zero_add]
      rw [hcompute]
      change runWithTape (embedRecorded (unwindStep a0 b0 prev c)) m
        (cursor+recordedMeasurementCount (ripple A B (some c) cs ds))
        (runWithTape (oldCorrection c d) m
          (cursor+recordedMeasurementCount (ripple A B (some c) cs ds)) t)=_
      rw [hold,runWithTape_embedRecorded,unwind_state a0 b0 c prev hn t.basis phase _ hcarry]
    dsimp only
    rw [hrun]
    have hout := unwound_head a0 b0 c prev bits t.basis hn htA htB htP
    change outBits a0=bits a0 ∧
      outBits b0=((bits b0 ^^ bits a0) ^^ incomingValue prev bits) ∧ outBits c=false at hout
    have htailout : ∀q∈A++B++cs,outBits q=t.basis q := by
      intro q hq
      obtain ⟨hqa,hqb,hqc⟩ := haway q hq
      simp [outBits,writeBit,hqa,hqb,hqc]
    refine ⟨rfl,?_,?_⟩
    · have hx := regValue_congr A cb bits hca
      have hy := regValue_congr B cb bits hcb
      have hz := regValue_congr B outBits t.basis (fun q hq => htailout q (by simp [hq]))
      have rcons (q : Wire) (r : List Wire) (st : BasisState) :
          regValue (q::r) st=(st q).toNat+2*regValue r st := by
        cases hq : st q <;> simp [regValue,hq]
      rw [rcons b0 B outBits,rcons a0 A bits,rcons b0 B bits]
      change (outBits b0).toNat+2*regValue B outBits=
        ((bits a0).toNat+2*regValue A bits+((bits b0).toNat+2*regValue B bits)+
          (incomingValue prev bits).toNat)%2^(B.length+1)
      rw [hout.2.1,hz,htsum,hx,hy]
      exact unsigned_step (bits a0) (bits b0) (incomingValue prev bits)
        (regValue A bits) (regValue B bits) B.length
    · intro q hq
      have hqb : q≠b0 := by intro h; exact hq (by simp [h])
      have hqB : q∉B := by
        intro h
        exact hq (by simpa only [B] using List.mem_cons_of_mem b0 h)
      by_cases hqa : q=a0
      · subst q; exact hout.1
      by_cases hqc : q=c
      · subst q; exact hout.2.2.trans hc0.symm
      simp [outBits,writeBit,hqa,hqb,hqc,htoutside q hqB,cb,computedBits]

/-- The stated full result follows from the emitted-program frame theorem. -/
theorem unsignedContract_of_shape (a b work : List Wire) (slots : List (Option Nat))
    (shape : Shape a b work slots) : UnsignedContract a b prev work slots := by
  intro bits phase m cursor ready
  obtain ⟨_,nd,clean,_⟩ := ready
  obtain ⟨hp,hs,hout⟩ := ripple_frame a b work slots shape prev bits phase m cursor nd clean
  refine ⟨hp,?_,hs,hout,?_⟩
  · apply regValue_congr
    intro q hq
    apply hout
    have dis : ∀q∈a,q∉b := by
      have h := suffix_nodup prev.toList (a++b++work)
        (by simpa only [List.append_assoc] using nd)
      have dis := (List.nodup_append'.mp
        ((List.nodup_append'.mp h).1)).2.2
      intro r hr hb
      exact List.disjoint_left.mp dis hr hb
    exact dis q hq
  · intro q hq
    rw [hout q ?_]
    exact clean q hq
    have h := suffix_nodup prev.toList (a++b++work)
        (by simpa only [List.append_assoc] using nd)
    have dis := (List.nodup_append'.mp h).2.2
    exact fun hb => List.disjoint_left.mp dis (List.mem_append_right a hb) hq

end ECDSAAdd.Arithmetic.RecordedRailRipple
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.ripple_frame
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.unsignedContract_of_shape
