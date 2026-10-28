import ECDSAAdd.Baselines.SlotSignedInteger

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem codec_gateSlots_le (w : Nat → Wire) (start : Nat) :
    gateSlots (compressedHistoryEncode w start) ≤ 200 ∧
    gateSlots (compressedHistoryDecode w start) ≤ 200 := by
  simp only [compressedHistoryEncode,compressedHistoryDecode,TranscriptCodec3.encode,
    TranscriptCodec3.decode,rename_gateSlots]
  constructor <;> decide

theorem scheduledCodec_gateSlots_le (w : Nat → Wire) (i : Nat) :
    gateSlots (compressedPackAfter w i) ≤ 200 ∧
    gateSlots (compressedDecodeBefore w i) ≤ 200 := by
  have h := codec_gateSlots_le w (i-3)
  unfold compressedPackAfter compressedDecodeBefore
  split <;> simp_all only [gateSlots_nil, Nat.zero_le, and_self]

theorem compactLoops_gateSlots_le (w : Nat → Wire) (i n : Nat) (hn : i+n ≤ 512) :
    gateSlots (compressedCompactForward w i n) ≤ n*6200 ∧
    gateSlots (compressedCompactReverse w i n) ≤ n*6200 := by
  induction n generalizing i with
  | zero => simp only [compressedCompactForward,compressedCompactReverse,
      gateSlots_nil,Nat.zero_mul,Nat.le_refl,and_self]
  | succ n ih =>
    have h := compactTick_gateSlots_le w i (by omega)
    have hc := scheduledCodec_gateSlots_le w i
    have ht := ih (i+1) (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,gateSlots_append,
      Nat.succ_mul]
    omega

end ECDSAAdd.Baselines
