import ECDSAAdd.Arithmetic.Paper935.SlotDecoderRun

namespace ECDSAAdd.Arithmetic.Paper935

theorem decoderPin_values (index : Nat) (old : PinState)
    (unset : old.frozen=false → old.offset=0) :
    (pinStep 498 index old).frozen=(old.frozen || (!old.frozen && decide (498 ≤ index) &&
      decide ((ECDSAAdd.Divsteps.zStep old.rows).g=0))) ∧
    (pinStep 498 index old).offset=(if !old.frozen && decide (498 ≤ index) &&
      decide ((ECDSAAdd.Divsteps.zStep old.rows).g=0) then decoderOffset index else old.offset) := by
  cases hf : old.frozen with
  | true => simp [pinStep,hf]
  | false =>
    have hz := unset hf
    by_cases hi : 498 ≤ index
    · have k : decoderOffset index=index+1-498 := by unfold decoderOffset; omega
      by_cases hg : (ECDSAAdd.Divsteps.zStep old.rows).g=0 <;> simp [pinStep,hf,hi,hg,k,hz]
    · simp [pinStep,hf,hi,hz]

end ECDSAAdd.Arithmetic.Paper935
