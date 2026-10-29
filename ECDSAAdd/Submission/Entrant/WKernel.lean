import ECDSAAdd.Submission.Entrant.WNativeFirstDirectCallerForward
import ECDSAAdd.Submission.Entrant.WNativeFirstDirectTailRestore
import ECDSAAdd.Arithmetic.NativeFirstDirectCallerStates
import ECDSAAdd.Arithmetic.MappedCompressedControlledSpec
import ECDSAAdd.Arithmetic.MappedCompressedStageCounts
import ECDSAAdd.Submission.Entrant.LaneSegment

/-! The mapped Skywalk arithmetic kernel with both integer passes replaced by
the narrowed passes of `WCompressedCompact*`.  The native prefix, the codec
schedule, the Lane A field segment (`LaneSegment`), the clears and the native inverse are
the unchanged blocks; the proofs below are those of `NativeFirstDirectCallerStates`,
`MappedCompressedControlledSpec`, `MappedCompressedStageCounts` and
`MappedCompressedStageSupport`, re-run over the new passes.  The only new
step is `compressedCompactForward_old_eq`: the narrowed forward pass ends in
the original terminal State, so the field-segment preparation is reused. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.W
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.NativeFirstDirect Secp256k1 DirectSkywalk
  OffsetBorrowedCanonical CompressedFieldSupport MappedCompressed CompressedAllocation

def kernel (divide : Bool) : Program :=
  NativeFirstDirect.forward base++compressedCompactForward base 1 511++
  skywalkArithmeticClear base++LaneA.laneSegment divide++skywalkArithmeticClear base++
  compressedCompactReverse base 1 511++NativeFirstKnown.inverse base

def controlled (divide : Bool) : Program :=
  directZeroControlled (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (kernel divide)

section States
attribute [local irreducible] run measurementCount NativeFirstDirect.forward NativeFirstDirect.inverse
  NativeFirstKnown.inverse reference callerKernel
  literalSkywalkSeed compressedCompactForward compressedCompactReverse
  Arithmetic.compressedCompactForward LaneA.laneSegment
  skywalkArithmeticClear allGroupEncode SkywalkTrace.next Nat.iterate

private theorem kernel_states_from_first (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (s1 s2 s3 s4 s5 s6 s7 : State)
    (hs1 : run (NativeFirstDirect.forward base) m1 s = s1)
    (hs2 : run (compressedCompactForward base 1 511) m2 s1 = s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2 = s3)
    (hs4 : run (LaneA.laneSegment divide) m4 s3 = s4)
    (hs5 : run (skywalkArithmeticClear base) m5 s4 = s5)
    (hs6 : run (compressedCompactReverse base 1 511) m6 s5 = s6)
    (hs7 : run (NativeFirstKnown.inverse base) m7 s6 = s7)
    (first : Arithmetic.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis) :
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
  obtain ⟨oldSeed,seedEq,fullEq⟩ := NativeFirstDirect.forward_terminal_states base pool x hx s s1 s2
    m1 m2 ready.1 ready.2 hs1 hs2
  have oldhsSeed := (directSkywalkLiteralSeed_seed_eq base hn x Y.val hx s [] hin).symm.trans seedEq
  have seed := skywalkSeed_spec L 258 p x (skywalkShared_seed_widths base)
    (skywalkShared_seed_nodup base hn) (by omega) hp (hx.trans hp)
    s [] (arith_seed_input base hn x Y.val s.basis hin)
  rw [oldhsSeed] at seed
  have stage0 := arith_seed_stage0 base hn x Y.val hx s [] hin
  rw [oldhsSeed] at stage0
  have fullOld : run (Arithmetic.compressedCompactForward base 0 512)
      (List.replicate 257 false++m2) oldSeed=s2 :=
    (compressedCompactForward_old_eq base hn hlo x p hp0 hx0 hpo hp hx cop oldSeed
      (List.replicate 257 false++m2) (List.replicate 257 false++m2) stage0).symm.trans fullEq
  have terminal := compressedCompactForward_512_spec base pool hlo x p hp0 hx0 hpo hp hx cop
    oldSeed (List.replicate 257 false++m2) stage0
  rw [fullEq] at terminal
  obtain ⟨origin,facts,_,encoded,entry⟩ := compressedPreparation_facts hn hlo ho x Y hx0 hx s
    [] (List.replicate 257 false++m2) m3 hin oldSeed s2 s3 seedEq fullOld hs3
  have selectorPool : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have h4 := LaneA.laneSegment_spec divide hn hlo ho selectorPool hf origin.basis hg hs
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
  have keeps := LaneA.laneSegment_pool_frame divide hn hlo ho selectorPool hf origin.basis hg hs
    facts.env facts.legal facts.workZero facts.unusedZero facts.targetHigh facts.sourceHigh
    facts.sourceZero x hx0 hx facts.trace Y s3 m4 entry
  rw [hs4] at keeps
  have recovered := clear_after_pool_update hn s2 s4 m3 m5
    (by rw [hs3]; exact keeps.1) (by intro q hq; rw [hs3]; exact keeps.2 q hq)
  rw [hs5] at recovered
  have restored := NativeFirstDirect.tail_restore_pool base pool hlo x p hp0 hx0 hpo hp hx cop
    s1 s2 m6 ((compactSkywalkStage_one base _ s1.basis).mpr first) terminal.2
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
        have a := run_preserves_outside (NativeFirstDirect.forward base) m1 s q (fun used => hpool
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

theorem kernel_states (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (s1 s2 s3 s4 s5 s6 s7 : State)
    (hs1 : run (NativeFirstDirect.forward base) m1 s=s1)
    (hs2 : run (compressedCompactForward base 1 511) m2 s1=s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2=s3)
    (hs4 : run (LaneA.laneSegment divide) m4 s3=s4)
    (hs5 : run (skywalkArithmeticClear base) m5 s4=s5)
    (hs6 : run (compressedCompactReverse base 1 511) m6 s5=s6)
    (hs7 : run (NativeFirstKnown.inverse base) m7 s6=s7) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s s7 := by
  have first := caller_first_stage base hn x Y.val hx0 hx s m1 hin
  rw [hs1] at first
  exact kernel_states_from_first divide hn hlo ho hf x Y hx0 hx s m1 m2 m3 m4 m5 m6 m7
    hin hg0 hs0 s1 s2 s3 s4 s5 s6 s7 hs1 hs2 hs3 hs4 hs5 hs6 hs7 first

theorem kernel_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s (run (kernel divide) m s) := by
  let P : State → State → Prop := fun initial out =>
    SkywalkArithmeticInput base x Y.val initial.basis →
    initial.basis (base 2409)=false → initial.basis (base 2410)=false →
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y initial out
  have all := skywalkRunSeven (NativeFirstDirect.forward base) (compressedCompactForward base 1 511)
    (skywalkArithmeticClear base) (LaneA.laneSegment divide) (skywalkArithmeticClear base)
    (compressedCompactReverse base 1 511) (NativeFirstKnown.inverse base) P
    (by
      intro initial s1 s2 s3 s4 s5 s6 s7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 input hg hs
      exact kernel_states divide hn hlo ho hf x Y hx0 hx initial m1 m2 m3 m4 m5 m6 m7
        input hg hs s1 s2 s3 s4 s5 s6 s7 h1 h2 h3 h4 h5 h6 h7) s m
  simpa only [kernel,List.append_assoc] using all hin hg0 hs0

end States

section Controlled
attribute [local irreducible] run measurementCount kernel
  directZeroDivisorEnter directZeroDivisorLeave

private theorem controlled_port_nodup :
    (base 2411::base 2313::(wireBlock base 770 256++wireBlock base 0 255++
      wireBlock base 2056 256)).Nodup := by
  have first : (List.range' 770 256++List.range' 0 255).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hx hc
    simp only [List.mem_range'_1] at hx hc
    omega
  have words : (List.range' 770 256++List.range' 0 255++List.range' 2056 256).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨first,List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hxy hz
    simp only [List.mem_append,List.mem_range'_1] at hxy hz
    omega
  have ids : (2411::2313::(List.range' 770 256++List.range' 0 255++List.range' 2056 256)).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp only [List.mem_cons,List.mem_append,List.mem_range'_1]
      omega
    · apply List.nodup_cons.mpr
      constructor
      · simp only [List.mem_append,List.mem_range'_1]
        omega
      · exact words
  change ((2411::2313::(List.range' 770 256++List.range' 0 255++
    List.range' 2056 256)).map base).Nodup
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact ids

private theorem zero_flag_outside : base 2411 ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hi
  have same := base_injective eq
  omega

/-- The zero-divisor wrapper around the narrowed kernel satisfies the original
strong port contract. -/
theorem controlled_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (zeroBranch : x = 0 → s.basis (base 2400) = false)
    (hflag : s.basis (base 2411) = false)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s (run (controlled divide) m s) := by
  let D := directDivisor x
  let R := (directSkywalkResult divide (s.basis (base 2400)) x Y).val
  have positive : 0 < D := Nat.pos_of_ne_zero (directDivisor_ne_zero x)
  have bound : D < p := by
    by_cases zero : x = 0
    · simp only [D,directDivisor,zero,if_true]
      norm_num [p]
    · simpa only [D,directDivisor,zero,if_false] using hx
  have sameResult : directSkywalkResult divide (s.basis (base 2400)) D Y =
      directSkywalkResult divide (s.basis (base 2400)) x Y := by
    by_cases zero : x = 0
    · simp only [directSkywalkResult,zeroBranch zero,Bool.false_eq_true,if_false]
    · simp only [D,directDivisor,zero,if_false]
  have cin : s.basis (base 2313) = false :=
    arith_input_bit base hn x Y.val s.basis hin 2313 (by omega) (by omega) (by omega)
  have carry : ∀ q ∈ wireBlock base 0 255,s.basis q = false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact arith_input_bit base hn x Y.val s.basis hin i (by omega) (by omega) (by omega)
  have callback : ∀ (t : State) (ms : List Bool),
      regValue (wireBlock base 770 256) t.basis = directDivisor (regValue (wireBlock base 770 256) s.basis) →
      regValue (wireBlock base 2056 256) t.basis = regValue (wireBlock base 2056 256) s.basis →
      t.basis (base 2411) = decide (regValue (wireBlock base 770 256) s.basis = 0) →
      (∀ q,q ≠ base 2411 → q ∉ wireBlock base 770 256 → t.basis q = s.basis q) →
      (run (kernel divide) ms t).phase = t.phase ∧
      regValue (wireBlock base 2056 256) (run (kernel divide) ms t).basis = R ∧
      ∀ q,q ∉ wireBlock base 2056 256 → (run (kernel divide) ms t).basis q = t.basis q := by
    intro t ms divisor numerator _ frame
    have input : SkywalkArithmeticInput base D Y.val t.basis := by
      refine ⟨divisor.trans (congrArg directDivisor hin.1),numerator.trans hin.2.1,?_⟩
      intro q hq hdx hdy
      have ne : q ≠ base 2411 := fun eq => zero_flag_outside (eq ▸ hq)
      exact (frame q ne hdx).trans (hin.2.2 q hq hdx hdy)
    have controls (q : Wire) (hq : q ∈ [base 2400,base 2409,base 2410]) :
        t.basis q = s.basis q := by
      have ne : q ≠ base 2411 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl|rfl|rfl
        all_goals intro eq; have same := base_injective eq; omega
      have away : q ∉ wireBlock base 770 256 :=
        fun bad => ho q hq (arith_block_subset_shared base 770 256 (by omega) bad)
      exact frame q ne away
    have strong := kernel_spec divide hn hlo ho hf D Y positive bound t ms input
      ((controls _ (by simp)).trans hg0) ((controls _ (by simp)).trans hs0)
    unfold DirectSkywalkArithmeticStrong at strong
    rw [controls (base 2400) (by simp),sameResult] at strong
    exact strong
  have width : (wireBlock base 0 255).length+1 = (wireBlock base 770 256).length := by
    simp only [wireBlock_length]
  have records := directZeroControlled_states (wireBlock base 770 256) (wireBlock base 2056 256)
    (wireBlock base 0 255) (base 2313) (base 2411) controlled_port_nodup width (kernel divide) s
    (m.take (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411))))
    ((m.drop (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411)))).take (measurementCount (kernel divide)))
    ((m.drop (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411)))).drop (measurementCount (kernel divide)))
    R cin hflag carry callback
  simpa only [DirectSkywalkArithmeticStrong,controlled,directZeroControlled,run_append,
    skywalkArithmeticNumerator,R] using records

end Controlled

section Counts
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] compactSkywalkForward compressedCompactForward compressedCompactReverse
attribute [local irreducible] toffoliCount measurementCount

/-- The delayed codec still emits all 170 packets after tick zero; the ticks
are 510 Toffolis and 255 records cheaper per pass. -/
theorem integer_tail_counts :
    toffoliCount (compressedCompactForward base 1 511)=197118 ∧
    measurementCount (compressedCompactForward base 1 511)=98346 ∧
    toffoliCount (compressedCompactReverse base 1 511)=197288 ∧
    measurementCount (compressedCompactReverse base 1 511)=98176 := by
  have f := compressedCompactForward_counts base base_pool_nodup 1 511 (by omega)
  have r := compressedCompactReverse_counts base base_pool_nodup 1 511 (by omega)
  have t : compactSkywalkForwardT 1 511=196608 := by decide +kernel
  have m : compactSkywalkForwardM 1 511=98176 := by decide +kernel
  have packs : compressedPackCount 1 511=170 := by decide
  simpa only [t,m,packs,Nat.reduceAdd,Nat.reduceMul] using
    And.intro f.1 (And.intro f.2 r)

theorem kernel_counts (divide : Bool) :
    toffoliCount (kernel divide)=(if divide then 1050182 else 1050692) ∧
    measurementCount (kernel divide)=721478 := by
  have f := NativeFirstDirect.forward_counts base
  have r := NativeFirstKnown.inverse_counts base
  have integer := integer_tail_counts
  have clear := skywalkTerminalClear_counts (base 511) (base 512) (base 770)
  have field := LaneA.laneSegment_counts divide
  simp only [kernel,skywalkArithmeticClear,toffoliCount_append,measurementCount_append,
    f.1,f.2,r.1,r.2,integer.1,integer.2.1,integer.2.2.1,integer.2.2.2,
    clear.1,clear.2,field.1,field.2]
  cases divide <;> constructor <;> norm_num

theorem controlled_counts (divide : Bool) :
    toffoliCount (controlled divide)=(if divide then 1050692 else 1051202) ∧
    measurementCount (controlled divide)=721986 := by
  have width : (wireBlock base 0 255).length+1=(wireBlock base 770 256).length := by
    simp [wireBlock]
  have wrapped := directZeroControlled_counts (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (kernel divide) width
  have core := kernel_counts divide
  simp only [controlled] at ⊢
  rw [wrapped.1,wrapped.2,core.1,core.2,wireBlock_length]
  cases divide <;> norm_num

end Counts

end ECDSAAdd.Entrant.W
