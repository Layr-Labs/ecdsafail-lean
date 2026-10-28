import ECDSAAdd.Arithmetic.Shift
import ECDSAAdd.Arithmetic.SignedWordBits

namespace ECDSAAdd.Arithmetic.Divsteps

/-- General left-rotation value, including inputs with their high bit set. -/
theorem shiftLeft_value_all (c low : Wire) (tail : List Wire)
    (hn : (c::low::tail).Nodup) (s : State) (m : List Bool) :
    regValue (low::tail) (run (shiftLeft c (low::tail)) m s).basis =
      if s.basis c then
        if regValue (low::tail) s.basis<2^tail.length then 2*regValue (low::tail) s.basis
        else 2*regValue (low::tail) s.basis-2^(tail.length+1)+1
      else regValue (low::tail) s.basis := by
  let t := run (shiftLeft c (low::tail)) m s
  have hc : t.basis c=s.basis c :=
    (shift_frame c (low::tail) s m).2.2.2 c (List.nodup_cons.mp hn).1
  have hcan := shiftRight_left_cancel c (low::tail) hn s m
  have hv := shiftRight_value c low tail hn t m
  rw [hcan,hc] at hv
  have hb := regValue_lt tail t.basis
  cases hctrl : s.basis c
  · simpa [hctrl] using hv.symm
  · simp only [hctrl,if_true] at hv ⊢
    change (if t.basis low then 1 else 0)+2*regValue tail t.basis = _
    cases hl : t.basis low <;> simp [hl,Bool.toNat,pow_succ] at hv ⊢ <;> split <;> omega

/-- A representable signed double retains its sign. After rotation that sign
appears at both endpoints, so one controlled XOR can clear the new low bit. -/
theorem shiftLeft_sign_agree (c low sign : Wire) (mid : List Wire)
    (hn : (c::low::(mid++[sign])).Nodup) (s : State) (m : List Bool)
    (hctrl : s.basis c=true)
    (hfit : -((2^(mid.length+1):Nat):Int) ≤ 2*signedRegValue (low::(mid++[sign])) s.basis ∧
      2*signedRegValue (low::(mid++[sign])) s.basis < ((2^(mid.length+1):Nat):Int)) :
    (run (shiftLeft c (low::(mid++[sign]))) m s).basis low=
      (run (shiftLeft c (low::(mid++[sign]))) m s).basis sign ∧
    (run (shiftLeft c (low::(mid++[sign]))) m s).basis sign=s.basis sign := by
  let t := run (shiftLeft c (low::(mid++[sign]))) m s
  have htc : t.basis c=true :=
    ((shift_frame c (low::(mid++[sign])) s m).2.2.2 c (List.nodup_cons.mp hn).1).trans hctrl
  have hv := shiftRight_value c low (mid++[sign]) hn t m
  rw [shiftRight_left_cancel c (low::(mid++[sign])) hn s m,htc] at hv
  have hb := regValue_lt (mid++[sign]) t.basis
  have hsign := regValue_highBit (low::mid) sign t.basis
  have horig := signedRegValue_msb (low::mid) sign s.basis
  change signedRegValue (low::(mid++[sign])) s.basis = _ at horig
  rw [horig] at hfit
  change t.basis low=t.basis sign ∧ t.basis sign=s.basis sign
  change t.basis sign=true ↔ 2^((low::mid).length)≤
    (if t.basis low then 1 else 0)+2*regValue (mid++[sign]) t.basis at hsign
  have hpow : ((2^mid.length:Nat):Int)=(2:Int)^mid.length := by norm_cast
  simp only [List.cons_append,List.length_cons,List.length_append,List.length_nil,pow_succ,
    Nat.cast_mul,Nat.cast_ofNat,if_true] at hv hb hsign hfit
  cases ho : s.basis sign <;> cases hl : t.basis low <;> cases hs : t.basis sign <;>
    simp [ho,hl,hs,Bool.toNat] at hv hsign hfit ⊢ <;> omega

/-- Rotate left conditionally, then clear the rotated sign bit from the low
wire. The signed-fit invariant ensures the new and old sign bits agree. -/
def doubleSigned (c low sign : Wire) (mid : List Wire) : Program :=
  shiftLeft c (low::(mid++[sign])) ++ [.CCX c sign low]

theorem doubleSigned_correct (c low sign : Wire) (mid : List Wire)
    (hn : (c::low::(mid++[sign])).Nodup) (s : State) (m : List Bool)
    (hfit : s.basis c=true →
      -((2^(mid.length+1):Nat):Int) ≤ 2*signedRegValue (low::(mid++[sign])) s.basis ∧
      2*signedRegValue (low::(mid++[sign])) s.basis < ((2^(mid.length+1):Nat):Int)) :
    (run (doubleSigned c low sign mid) m s).phase=s.phase ∧
    (∀ w, w∉low::(mid++[sign]) → (run (doubleSigned c low sign mid) m s).basis w=s.basis w) ∧
    signedRegValue (low::(mid++[sign])) (run (doubleSigned c low sign mid) m s).basis=
      (if s.basis c then 2*signedRegValue (low::(mid++[sign])) s.basis
        else signedRegValue (low::(mid++[sign])) s.basis) := by
  let r := low::(mid++[sign])
  let t := run (shiftLeft c r) m s
  let u := run [.CCX c sign low] m t
  have hf := shift_frame c r s m
  have htc : t.basis c=s.basis c := hf.2.2.2 c (List.nodup_cons.mp hn).1
  have hsl : sign≠low := by
    intro h
    exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [←h])
  have keep (w : Wire) (hw : w≠low) : u.basis w=t.basis w := by simp [u,run,writeBit,hw]
  have hs : u.basis sign=t.basis sign := keep sign hsl
  have htail : regValue (mid++[sign]) u.basis=regValue (mid++[sign]) t.basis := by
    apply regValue_congr
    intro w hw
    apply keep
    intro he
    exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (he ▸ hw)
  have hu : run (doubleSigned c low sign mid) m s=u := by
    rw [doubleSigned,run_append,run_take,(shift_counts c r).2.2.2,List.drop_zero]
  rw [hu]
  refine ⟨hf.2.2.1,?_,?_⟩
  · intro w hw
    have hwl : w≠low := by intro he; subst w; exact hw List.mem_cons_self
    exact (keep w hwl).trans (hf.2.2.2 w hw)
  · cases hctrl : s.basis c
    · have he : u=t := by
        have htc0 : t.basis c=false := htc.trans hctrl
        apply congrArg₂ State.mk
        · rfl
        · funext w
          by_cases hw : w=low <;> simp [htc0,writeBit,hw] <;> rfl
      have hv := shiftLeft_value_all c low (mid++[sign]) hn s m
      simp only [hctrl,Bool.false_eq_true,if_false] at hv ⊢
      unfold signedRegValue
      rw [he,hv]
    · have hagree := shiftLeft_sign_agree c low sign mid hn s m hctrl (hfit hctrl)
      change t.basis low=t.basis sign ∧ t.basis sign=s.basis sign at hagree
      have hl : u.basis low=false := by
        have htc1 : t.basis c=true := htc.trans hctrl
        simp [u,run,writeBit,htc1,hagree.1]
      have hv := shiftRight_value c low (mid++[sign]) hn t m
      rw [shiftRight_left_cancel c r hn s m,htc,hctrl] at hv
      simp only [if_true,hagree.1,hagree.2] at hv
      have hraw : regValue (low::(mid++[sign])) u.basis=2*regValue (mid++[sign]) t.basis := by
        change (if u.basis low then 1 else 0)+2*regValue (mid++[sign]) u.basis = _
        rw [hl,htail]
        simp
      simp only [if_true]
      have hU := signedRegValue_msb (low::mid) sign u.basis
      have hS := signedRegValue_msb (low::mid) sign s.basis
      simp only [List.cons_append] at hU hS
      rw [hU,hS,hraw,hs,hagree.2,hv]
      cases hb : s.basis sign <;>
        simp [Bool.toNat,List.length_cons,List.length_append,pow_succ,Nat.cast_add,Nat.cast_mul]
      all_goals ring

theorem doubleSigned_counts (c low sign : Wire) (mid : List Wire) :
    toffoliCount (doubleSigned c low sign mid)=mid.length+2 ∧
    measurementCount (doubleSigned c low sign mid)=0 := by
  have h := shift_counts c (low::(mid++[sign]))
  simp [doubleSigned,toffoliCount_append,measurementCount_append,toffoliCount,
    measurementCount,h.2.2.1,h.2.2.2]

theorem doubleSigned_wires (c low sign : Wire) (mid : List Wire) :
    wires (doubleSigned c low sign mid)=(c::low::(mid++[sign])).toFinset := by
  rw [doubleSigned,wires_append,(shift_wires c (low::(mid++[sign]))).2]
  simp only [show ¬(low::(mid++[sign])).length<2 by simp,if_false]
  ext w
  simp [wires,Instr.wires]
  tauto

theorem doubleSigned_qubits (c low sign : Wire) (mid : List Wire)
    (hn : (c::low::(mid++[sign])).Nodup) :
    qubitCount (doubleSigned c low sign mid)=mid.length+3 := by
  rw [qubitCount,doubleSigned_wires,List.toFinset_card_of_nodup hn]
  simp [Nat.add_assoc]

/-- Exact gate inverse; independent of the signed representability premise. -/
def undoubleSigned (c low sign : Wire) (mid : List Wire) : Program :=
  [.CCX c sign low] ++ shiftRight c (low::(mid++[sign]))

theorem undoubleSigned_doubleSigned (c low sign : Wire) (mid : List Wire)
    (hn : (c::low::(mid++[sign])).Nodup) (s : State) (m : List Bool) :
    run (undoubleSigned c low sign mid) m (run (doubleSigned c low sign mid) m s)=s := by
  have hcl : c≠low := by
    intro h
    exact (List.nodup_cons.mp hn).1 (by simp [h])
  have hsl : sign≠low := by
    intro h
    exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [←h])
  have twice (t : State) : run [.CCX c sign low] m (run [.CCX c sign low] m t)=t := by
    apply congrArg₂ State.mk
    · rfl
    · funext w
      by_cases hw : w=low
      · subst w
        cases ht : t.basis low <;> cases hc : t.basis c <;> cases hs : t.basis sign <;>
          simp [run,writeBit,hcl,hsl,ht,hc,hs]
      · simp [run,writeBit,hw]
  rw [doubleSigned,undoubleSigned,run_append,run_take]
  change run (shiftRight c (low::(mid++[sign]))) m
    (run [.CCX c sign low] m (run (shiftLeft c (low::(mid++[sign])) ++ [.CCX c sign low]) m s))=s
  rw [run_append,run_take,(shift_counts c (low::(mid++[sign]))).2.2.2,List.drop_zero,
    twice,shiftRight_left_cancel c (low::(mid++[sign])) hn s m]

end ECDSAAdd.Arithmetic.Divsteps
