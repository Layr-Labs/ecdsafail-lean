import ECDSAAdd.Baselines.SlotAlgebra

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem counter_gateSlots (L : AdderLayout) :
    gateSlots (counterInc L) = 28 * L.width + 2 ∧
    gateSlots (counterDec L) = 28 * L.width + 2 := by
  have hd (A : AdderLayout) : gateSlots (counterDecXor A) = 15 * A.width + 2 := by
    change gateSlots (notRegister (A.cin :: A.y) ++ add A ++ notRegister (A.cin :: A.y)) = _
    simp [add, AdderLayout.width, AdderLayout.y]; omega
  simp [counterInc, counterDec, counterIncXor, hd, add, AdderLayout.swapCounter, AdderLayout.width]
  omega

theorem counterActive_gateSlots_le (L : AdderLayout) (t i : Nat) :
    gateSlots (counterActiveXor L t i) ≤ 14 * L.width + 5 := by
  have h := compareLtConst_gateSlots_le none L.x L.y L.carry L.cin t (i+1)
  have hx : L.x.length = L.width := by simp [AdderLayout.x, AdderLayout.width]
  have hy : L.y.length = L.width := by simp [AdderLayout.y, AdderLayout.width]
  rw [hx, hy] at h
  simp only [counterActiveXor, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots]
  omega

theorem valueBody_gateSlots_le (L : RoundDataLayout) (a sw su : Wire) :
    gateSlots (valueBodyProgram L a sw su) ≤ 26 * L.width ∧
    gateSlots (valueUnbodyProgram L a sw su) ≤ 26 * L.width := by
  have hm := measuredMasked_gateSlots_le su (L.reg .v) (L.reg .y) (L.reg .u)
    ((L.reg .carry).take (L.width-1)) L.cin
  simp only [L.reg_length] at hm
  have hs := shift_gateSlots a L.u
  simp only [RoundDataLayout.u, L.reg_length] at hs
  simp only [valueBodyProgram, valueUnbodyProgram, inplaceArithmetic, ↓reduceIte,
    Bool.false_eq_true, gateSlots_append, swapRegisters_gateSlots,
    RoundDataLayout.u, RoundDataLayout.v, L.reg_length, Nat.min_self]
  constructor <;> omega

theorem recordRound_gateSlots_le (L : KaliskiRoundLayout) :
    gateSlots (recordRound L) ≤ 12 * L.data.width + 10 := by
  have h := compareLt_gateSlots_le (some L.bothWork) L.v L.u (L.data.reg .carry) L.cin L.swap
  have hu : L.u.length = L.data.width := L.data.reg_length .u
  have hv : L.v.length = L.data.width := L.data.reg_length .v
  rw [hu, hv] at h
  simp only [recordRound, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots]
  omega

theorem valueRound_gateSlots_le (L : KaliskiRoundLayout) (i : Nat) :
    gateSlots (valueRound L i) ≤ 45 * L.data.width + 42 * L.counter.width + 20 ∧
    gateSlots (valueUnround L i) ≤ 45 * L.data.width + 42 * L.counter.width + 20 := by
  have hb := valueBody_gateSlots_le L.data L.active L.swap L.subtract
  have hr := recordRound_gateSlots_le L
  have hc := counter_gateSlots L.counter
  have hd := counter_gateSlots L.counter.swapCounter
  have ha := counterActive_gateSlots_le L.comparator L.active i
  rw [L.comparator_fields.2.2.2.2.2] at ha
  rw [L.counter.swapCounter_fields.2.2.2.2.2] at hd
  have hz := zeroControlled_gateSlots L.active L.done (L.data.zeroBits .v)
  have hzl : (L.data.zeroBits .v).length = L.data.width := by simp [RoundDataLayout.zeroBits, RoundDataLayout.width]
  rw [hzl] at hz
  simp only [valueRound, valueUnround, roundActiveXor, gateSlots_append,
    loadActive, gateSlots_cons, gateSlots_nil, instructionSlots]
  constructor <;> omega

theorem valueLoop_gateSlots_le (L : KaliskiRoundLayout) (i : Nat) (rs : List RoundRecord)
    (hw : 2 ≤ L.data.width) :
    gateSlots (valueLoop L i rs) ≤ rs.length * (45 * L.data.width + 42 * L.counter.width + 20) ∧
    gateSlots (valueUnloop L i rs) ≤ rs.length * (45 * L.data.width + 42 * L.counter.width + 20) := by
  induction rs generalizing L i with
  | nil => simp [valueLoop, valueUnloop]
  | cons r rs ih =>
    have hd : L.swapCounter.data = L.data := rfl
    have hc : L.swapCounter.counter.width = L.counter.width := by
      simp [KaliskiRoundLayout.swapCounter, KaliskiRoundLayout.counter, AdderLayout.width]
    have ht := ih L.swapCounter (i+1) (by simpa [hd] using hw)
    rw [hd, hc] at ht
    have hv := valueWidth_bounds L.data.width i hw
    have hb := valueRound_gateSlots_le ((L.withRecord r).narrow (valueWidth L.data.width i)) i
    have hnw : ((L.withRecord r).narrow (valueWidth L.data.width i)).data.width = valueWidth L.data.width i :=
      (L.withRecord r).narrow_width _ (by omega) hv.2
    have hnc : ((L.withRecord r).narrow (valueWidth L.data.width i)).counter = L.counter := rfl
    rw [hnw, hnc] at hb
    simp only [valueLoop, valueUnloop, gateSlots_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    constructor <;> omega

end ECDSAAdd.Baselines
