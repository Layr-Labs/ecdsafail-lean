import ECDSAAdd.Baselines.SlotRounds
import ECDSAAdd.Baselines.SlotModular

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem replayLoop_gateSlots_le (L : ReplayLayout) (n p i : Nat) (rs : List RoundRecord)
    (hw : L.payload.Widths n) (hc : L.counter.width = 10) :
    gateSlots (replayLoop L p i rs) ≤ rs.length * (123*n+375) ∧
    gateSlots (replayUnloop L p i rs) ≤ rs.length * (95*n+346) := by
  induction rs generalizing i with
  | nil => simp [replayLoop, replayUnloop]
  | cons r rs ih =>
    have hm := replayCell_gateSlots_le L.active r.swap r.subtract L.payload n p hw
    have ha := counterActive_gateSlots_le L.counter L.active i
    rw [hc] at ha
    have ht := ih (i+1)
    simp only [replayLoop, replayUnloop, replayRound, replayUnround, gateSlots_append,
      List.length_cons, Nat.add_mul, Nat.one_mul]
    constructor <;> omega

theorem dialogLoad_gateSlots_le (L : DialogLayout) (p : Nat) (hw : L.Widths) :
    gateSlots (dialogLoad L p) ≤ 515 := by
  have hu : L.first.u.length = 257 := by
    simp [KaliskiRoundLayout.u, RoundDataLayout.u, KaliskiRoundLayout.data, RoundDataLayout.reg, hw.low]
  have hx : L.x.length = 256 := by simp [DialogLayout.x, hw.low]
  have h := xorConstant_gateSlots_le L.first.u p
  rw [hu] at h
  unfold dialogLoad
  split
  · simpa using h.trans (by omega : 257 ≤ 515)
  · simp only [gateSlots_append, safeDivisor, gateSlots_cons, instructionSlots,
      gateSlots_nil, copyRegister_gateSlots, hx]
    have hm := Nat.min_le_left 256 (1 + List.length ‹List Wire›)
    omega

theorem dialog_gateSlots_le (L : DialogLayout) (p : Nat) (hw : L.Widths) :
    gateSlots (dialogDivide L p) ≤ 29000000 ∧
    gateSlots (dialogMultiply L p) ≤ 25000000 := by
  have hd : L.first.data.width = 257 := by
    simp [KaliskiRoundLayout.data, RoundDataLayout.width, hw.low]
  have hv := valueLoop_gateSlots_le L.first 0 L.records (by omega)
  rw [hd, hw.counter, hw.records] at hv
  have hc : L.replay.counter.width = 10 := by
    exact hw.counter
  have hr := replayLoop_gateSlots_le L.replay 256 p 0 L.records (L.payload_widths hw) hc
  rw [hw.records] at hr
  have hl := dialogLoad_gateSlots_le L p hw
  have hy : L.y.length = 257 := by
    change (L.first.data.reg .s).length = 257
    rw [L.first.data.reg_length, hd]
  have hz : L.z.length = 257 := by
    change (L.first.data.reg .out).length = 257
    rw [L.first.data.reg_length, hd]
  simp only [dialogDivide, dialogMultiply, gateSlots_append, exchangeRegisters_gateSlots, hy, hz]
  constructor <;> omega

end ECDSAAdd.Baselines
