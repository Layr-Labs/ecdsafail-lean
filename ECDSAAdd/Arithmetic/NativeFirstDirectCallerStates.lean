import ECDSAAdd.Arithmetic.NativeFirstDirectCallerProgram
import ECDSAAdd.Arithmetic.NativeFirstDirectCallerInput
import ECDSAAdd.Arithmetic.NativeFirstDirectCallerForward
import ECDSAAdd.Arithmetic.NativeFirstDirectCallerFirstStage
import ECDSAAdd.Arithmetic.NativeFirstDirectTailRestore
import ECDSAAdd.Arithmetic.NativeFirstKnownInverse
import ECDSAAdd.Arithmetic.MappedCompressedCallerStates

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open Secp256k1 DirectSkywalk OffsetBorrowedCanonical CompressedFieldSupport MappedCompressed
attribute [local irreducible] run measurementCount forward inverse NativeFirstKnown.inverse reference callerKernel
  literalSkywalkSeed compressedCompactForward compressedCompactReverse selectedFieldSegment
  skywalkArithmeticClear allGroupEncode SkywalkTrace.next Nat.iterate

/-- Pure intermediate helper: the first-stage witness is discharged by the
actual new prefix in the public theorem below. No phase/frame callback occurs. -/
private theorem kernel_states_from_first (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (s1 s2 s3 s4 s5 s6 s7 : State)
    (hs1 : run (forward base) m1 s = s1)
    (hs2 : run (compressedCompactForward base 1 511) m2 s1 = s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2 = s3)
    (hs4 : run (selectedFieldSegment divide) m4 s3 = s4)
    (hs5 : run (skywalkArithmeticClear base) m5 s4 = s5)
    (hs6 : run (compressedCompactReverse base 1 511) m6 s5 = s6)
    (hs7 : run (NativeFirstKnown.inverse base) m7 s6 = s7)
    (first : CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s s7 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let L := skywalkSharedSeed base
  let F := skywalkSharedField base
  let Z := (directSkywalkResult divide (s.basis (base 2400)) x Y).val
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := arith_coprime x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have ready := caller_ready base hn x Y.val s.basis hin
  have prefixPhase := forward_native_output base pool x hx s m1 ready.1 ready.2
  rw [hs1] at prefixPhase
  obtain ⟨oldSeed,seedEq,fullEq⟩ := forward_terminal_states base pool x hx s s1 s2
    m1 m2 ready.1 ready.2 hs1 hs2
  have oldhsSeed := (directSkywalkLiteralSeed_seed_eq base hn x Y.val hx s [] hin).symm.trans seedEq
  have seed := skywalkSeed_spec L 258 p x (skywalkShared_seed_widths base)
    (skywalkShared_seed_nodup base hn) (by omega) hp (hx.trans hp)
    s [] (arith_seed_input base hn x Y.val s.basis hin)
  rw [oldhsSeed] at seed
  have stage0 := arith_seed_stage0 base hn x Y.val hx s [] hin
  rw [oldhsSeed] at stage0
  have terminal := compressedCompactForward_512_spec base pool hlo x p hp0 hx0 hpo hp hx cop
    oldSeed (List.replicate 257 false++m2) stage0
  rw [fullEq] at terminal
  obtain ⟨origin,facts,_,encoded,entry⟩ := compressedPreparation_facts hn hlo ho x Y hx0 hx s
    [] (List.replicate 257 false++m2) m3 hin oldSeed s2 s3 seedEq fullEq hs3
  have selectorPool : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have h4 := selectedFieldSegment_spec divide hn hlo ho selectorPool hf origin.basis hg hs
    facts.env facts.legal facts.workZero facts.unusedZero facts.targetHigh facts.sourceHigh
    x hx0 hx facts.trace Y s3 m4 entry
  rw [hs4] at h4
  have actual4 := encodedCanonical_caller_frame hn hlo origin.basis facts.sourceZero _ s4 h4.2
  have result : fieldResult divide origin.basis x Y = directSkywalkResult divide (s.basis (base 2400)) x Y := by
    simp only [fieldResult,directSkywalkResult,skywalkArithmeticResult,
      facts.controls (base 2400) (by simp)]
  have value4 : regValue F.z s4.basis=Z := by
    rw [result] at actual4
    exact actual4.1
  have keeps := selectedFieldSegment_pool_frame divide hn hlo ho selectorPool hf origin.basis hg hs
    facts.env facts.legal facts.workZero facts.unusedZero facts.targetHigh facts.sourceHigh
    facts.sourceZero x hx0 hx facts.trace Y s3 m4 entry
  rw [hs4] at keeps
  have recovered := clear_after_pool_update hn s2 s4 m3 m5
    (by rw [hs3]; exact keeps.1) (by intro q hq; rw [hs3]; exact keeps.2 q hq)
  rw [hs5] at recovered
  have restored := tail_restore_pool base pool hlo x p hp0 hx0 hpo hp hx cop
    s1 s2 m6 first terminal.2
  have agrees := pool_run_agrees (compressedCompactReverse base 1 511) (skywalkPoolWires base).toFinset
    (compressedCompactReverse_support base pool hlo 1 511 (by omega)) m6 s5 s2 recovered.1
    (fun q hq => recovered.2 q (List.mem_toFinset.mp hq))
  rw [hs6] at agrees
  have phase6 : s6.phase=s1.phase :=
    agrees.1.trans (restored.1.trans ((terminal.1.trans seed.1).trans prefixPhase.1.symm))
  have pool6 : ∀q∈skywalkPoolWires base,s6.basis q=s1.basis q := by
    intro q hq
    exact (agrees.2 q (List.mem_toFinset.mpr hq)).trans (restored.2.1 q hq)
  have h7 := NativeFirstKnown.inverse_restore_after_outside base pool x s s6 m1 m7 ready.1
    (by rw [hs1]; exact phase6)
    (by intro q hq; rw [hs1]; exact pool6 q hq)
  rw [hs7] at h7
  have reverseAway (q : Wire) (hq : q∉skywalkPoolWires base) : s6.basis q=s5.basis q := by
    have a := compressedCompactReverse_frame base pool hlo 1 511 (by omega) s5 m6 q hq
    rw [hs6] at a
    exact a
  have frame7Z (q : Wire) (hz : q∉F.z) : s7.basis q=s.basis q := by
    by_cases hpool : q∈skywalkPoolWires base
    · exact h7.2.1 q hpool
    · have k5 := arith_clear_outside base hn s4 m5 q hpool
      have k3 := arith_clear_outside base hn s2 m3 q hpool
      have k2 := compressedCompactForward_frame base pool hlo 1 511 (by omega) s1 m2 q hpool
      have kEncode : s3.basis q=origin.basis q := by
        rw [encoded]
        exact run_preserves_outside _ [] origin q
          (fun used => hpool (List.mem_toFinset.mp (caller_encoder_pool_support hn hlo used)))
      have k1 : s1.basis q=s.basis q := by
        have a := run_preserves_outside (forward base) m1 s q (fun used => hpool
          (prefix_pool_subset base (List.mem_toFinset.mp ((prefix_support base).1 used))))
        rw [hs1] at a
        exact a
      rw [hs5] at k5
      rw [hs3] at k3
      rw [hs2] at k2
      exact (h7.2.2 q hpool).trans ((reverseAway q hpool).trans (k5.trans
        ((actual4.2 q hz hpool).trans (kEncode.symm.trans (k3.trans (k2.trans k1))))))
  have hz7 : regValue F.z s7.basis=Z := by
    apply Eq.trans (regValue_congr _ _ _ ?_) value4
    intro q hq
    have away : q∉skywalkPoolWires base := fun h => arith_pool_away_z base hn q h hq
    have k5 := arith_clear_outside base hn s4 m5 q away
    rw [hs5] at k5
    exact (h7.2.2 q away).trans ((reverseAway q away).trans k5)
  have hZ : Z<2^256 := (ZMod.val_lt (directSkywalkResult divide (s.basis (base 2400)) x Y)).trans hp
  have high := skywalkShared_numerator_high_zero base s7.basis Z hz7 hZ
  have low7 : regValue (skywalkArithmeticNumerator base) s7.basis=Z := by
    change regValue (wireBlock base 2056 256++[base 2312]) s7.basis=Z at hz7
    rw [regValue_append] at hz7
    simpa [regValue,high,skywalkArithmeticNumerator] using hz7
  refine ⟨h7.1,low7,?_⟩
  intro q hq
  by_cases hz : q∈F.z
  · change q∈wireBlock base 2056 256++[base 2312] at hz
    rcases List.mem_append.mp hz with hlow|hpad
    · exact False.elim (hq hlow)
    · have eq : q=base 2312 := by simpa using hpad
      subst q
      exact high.trans (arith_input_bit base hn x Y.val s.basis hin 2312 (by omega) (by omega) (by omega)).symm
  · exact frame7Z q hz

/-- Public exact seven-stage contract, with no new caller premises. -/
theorem kernel_states (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (s1 s2 s3 s4 s5 s6 s7 : State)
    (hs1 : run (forward base) m1 s=s1)
    (hs2 : run (compressedCompactForward base 1 511) m2 s1=s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2=s3)
    (hs4 : run (selectedFieldSegment divide) m4 s3=s4)
    (hs5 : run (skywalkArithmeticClear base) m5 s4=s5)
    (hs6 : run (compressedCompactReverse base 1 511) m6 s5=s6)
    (hs7 : run (NativeFirstKnown.inverse base) m7 s6=s7) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s s7 := by
  have first := caller_first_stage base hn x Y.val hx0 hx s m1 hin
  rw [hs1] at first
  exact kernel_states_from_first divide hn hlo ho hf x Y hx0 hx s m1 m2 m3 m4 m5 m6 m7
    hin hg0 hs0 s1 s2 s3 s4 s5 s6 s7 hs1 hs2 hs3 hs4 hs5 hs6 hs7 first

/-- Interpreter composition keeps every independent record split explicit. -/
theorem kernel_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s (run (callerKernel divide) m s) := by
  let P : State → State → Prop := fun initial out =>
    SkywalkArithmeticInput base x Y.val initial.basis →
    initial.basis (base 2409)=false → initial.basis (base 2410)=false →
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y initial out
  have all := skywalkRunSeven (forward base) (compressedCompactForward base 1 511)
    (skywalkArithmeticClear base) (selectedFieldSegment divide) (skywalkArithmeticClear base)
    (compressedCompactReverse base 1 511) (NativeFirstKnown.inverse base) P
    (by
      intro initial s1 s2 s3 s4 s5 s6 s7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 input hg hs
      exact kernel_states divide hn hlo ho hf x Y hx0 hx initial m1 m2 m3 m4 m5 m6 m7
        input hg hs s1 s2 s3 s4 s5 s6 s7 h1 h2 h3 h4 h5 h6 h7) s m
  simpa only [callerKernel,List.append_assoc] using all hin hg0 hs0

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kernel_states
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kernel_spec
