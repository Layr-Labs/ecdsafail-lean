import ECDSAAdd.Arithmetic.Paper935.SlotFrontMath

namespace ECDSAAdd.Arithmetic.Paper935

/-- Completed slot metadata, before the retained branch bit is transported
to the history register and measured. -/
structure SlotRegisters.OutputValues (F : SlotRegisters) (s : BasisState) (old next : PinState) : Prop where
  one : s F.one=true
  frozen : s F.frozen=next.frozen
  parity : s F.parity=decide (ECDSAAdd.Divsteps.bbit old.rows=1)
  active : s F.active=false
  swap : s F.swap=false
  work0 : s F.work0=false
  work1 : s F.work1=false
  counter : signedRegValue F.counter s=next.rows.z
  offset : regValue F.offset s=next.offset

theorem SlotRegisters.output_from_post (F : SlotRegisters) (s t : BasisState) (old : PinState)
    (tmin index : Nat) (mid : F.MidValues s old)
    (frozen : t F.frozen=(pinStep tmin index old).frozen)
    (offset : regValue F.offset t=(pinStep tmin index old).offset)
    (active : t F.active=false) (work0 : t F.work0=false) (work1 : t F.work1=false)
    (frame : ∀ q,q≠F.active → q≠F.frozen → q∉F.offset → t q=s q)
    (separate : ∀ q∈[F.one,F.swap,F.parity]++F.counter,q≠F.active ∧ q≠F.frozen ∧ q∉F.offset) :
    F.OutputValues t old (pinStep tmin index old) := by
  have keep (q : Wire) (hq : q∈[F.one,F.swap,F.parity]++F.counter) : t q=s q := by
    obtain ⟨ha,hf,hr⟩ := separate q hq
    exact frame q ha hf hr
  constructor
  · exact (keep F.one (by simp)).trans mid.one
  · exact frozen
  · exact (keep F.parity (by simp)).trans mid.parity
  · exact active
  · exact (keep F.swap (by simp)).trans mid.swap
  · exact work0
  · exact work1
  · rw [pinStep_rows]
    unfold signedRegValue
    rw [regValue_congr F.counter t s (fun q hq => keep q (by simp [hq]))]
    exact mid.counter
  · exact offset

end ECDSAAdd.Arithmetic.Paper935
