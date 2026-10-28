import ECDSAAdd.Arithmetic.EntryForwardSelectedPoolRestore
import ECDSAAdd.Arithmetic.MappedCompressedCallerPreparation
import ECDSAAdd.Arithmetic.MappedCompressedCallerFrame
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run measurementCount skywalkSeed skywalkUnseed
  literalSkywalkSeed literalSkywalkUnseed compressedCompactForward compressedCompactReverse
  selectedFieldSegment skywalkArithmeticClear allGroupEncode SkywalkTrace.next Nat.iterate

/-- Actual seven-stage caller contract on the original256-bit ports.
Field entry and encoded-pool restoration are derived from the emitted prefix. -/
theorem kernel_states (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (s1 s2 s3 s4 s5 s6 s7 : State)
    (hs1 : run (literalSkywalkSeed (literalSkywalkPoolSeed base) p) m1 s = s1)
    (hs2 : run (compressedCompactForward base 0 512) m2 s1 = s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2 = s3)
    (hs4 : run (selectedFieldSegment divide) m4 s3 = s4)
    (hs5 : run (skywalkArithmeticClear base) m5 s4 = s5)
    (hs6 : run (compressedCompactReverse base 0 512) m6 s5 = s6)
    (hs7 : run (literalSkywalkUnseed (literalSkywalkPoolSeed base) p) m7 s6 = s7) :
    s7.phase = s.phase ∧ regValue (skywalkArithmeticNumerator base) s7.basis =
      (directSkywalkResult divide (s.basis (base 2400)) x Y).val ∧
      ∀ q,q ∉ skywalkArithmeticNumerator base → s7.basis q = s.basis q := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let L := skywalkSharedSeed base
  let F := skywalkSharedField base
  let Z := (directSkywalkResult divide (s.basis (base 2400)) x Y).val
  have hp : p < 2^256 := by norm_num [p]
  have pool := skywalkShared_integer_nodup base hn
  have oldhs1 := (directSkywalkLiteralSeed_seed_eq base hn x Y.val hx s m1 hin).symm.trans hs1
  have h1 := skywalkSeed_spec L 258 p x (skywalkShared_seed_widths base)
    (skywalkShared_seed_nodup base hn) (by omega) hp (hx.trans hp)
    s m1 (arith_seed_input base hn x Y.val s.basis hin)
  rw [oldhs1] at h1
  have stage0 := arith_seed_stage0 base hn x Y.val hx s m1 hin
  rw [oldhs1] at stage0
  obtain ⟨origin,facts,_,encoded,entry⟩ := compressedPreparation_facts hn hlo ho
    x Y hx0 hx s m1 m2 m3 hin s1 s2 s3 hs1 hs2 hs3
  have selectorPool : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409) = false :=
    (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410) = false :=
    (facts.controls _ (by simp)).trans hs0
  have h4 := selectedFieldSegment_spec divide hn hlo ho selectorPool hf origin.basis hg hs
    facts.env facts.legal facts.workZero facts.unusedZero facts.targetHigh facts.sourceHigh
    x hx0 hx facts.trace Y s3 m4 entry
  rw [hs4] at h4
  have actual4 := encodedCanonical_caller_frame hn hlo origin.basis facts.sourceZero _ s4 h4.2
  have result : fieldResult divide origin.basis x Y = directSkywalkResult divide (s.basis (base 2400)) x Y := by
    simp only [fieldResult,directSkywalkResult,skywalkArithmeticResult,
      facts.controls (base 2400) (by simp)]
  have value4 : regValue F.z s4.basis = Z := by
    rw [result] at actual4
    exact actual4.1
  have inputRun : EncodedCanonicalFrame origin.basis Y 0
      (run (skywalkArithmeticClear base) m3 (run (compressedCompactForward base 0 512) m2 s1)) := by
    rw [hs2,hs3]
    exact entry
  have h6 := selectedFieldSegment_reverse_pool divide hn hlo ho selectorPool hf origin.basis hg hs
    facts.env facts.legal facts.workZero facts.unusedZero facts.targetHigh facts.sourceHigh
    facts.sourceZero x hx0 hx facts.trace Y s1 m2 m3 m4 m5 m6 stage0 inputRun
  dsimp only at h6
  rw [hs2,hs3,hs4,hs5,hs6] at h6
  have outsideZ (q : Wire) (hq : q ∉ F.z) : s6.basis q = s1.basis q := by
    by_cases hpool : q ∈ skywalkPoolWires base
    · exact h6.2.1 q hpool
    · have k5 := arith_clear_outside base hn s4 m5 q hpool
      have k3 := arith_clear_outside base hn s2 m3 q hpool
      have k2 := compressedCompactForward_frame base pool hlo 0 512 (by decide) s1 m2 q hpool
      have kEncode : s3.basis q = origin.basis q := by
        rw [encoded]
        exact run_preserves_outside _ [] origin q
          (fun used => hpool (List.mem_toFinset.mp (caller_encoder_pool_support hn hlo used)))
      rw [hs5] at k5
      rw [hs3] at k3
      rw [hs2] at k2
      exact (h6.2.2 q hpool).trans (k5.trans ((actual4.2 q hq hpool).trans
        (kEncode.symm.trans (k3.trans k2))))
  have seedAway (q : Wire) (hq : q ∈ L.usedWires) : q ∉ F.z := by
    change q ∈ base 2313::(wireBlock base 0 258++wireBlock base 770 258++
      wireBlock base 1798 258++wireBlock base 1540 257) at hq
    rw [skywalkShared_field_z]
    rcases List.mem_cons.mp hq with rfl|hr
    · exact arith_block_away base hn 2313 2056 257 (by omega) (by omega) (by omega)
    · simp only [List.mem_append,or_assoc] at hr
      rcases hr with hq|hq|hq|hq
      all_goals
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
        simp only [List.mem_range'_1] at hj
        exact arith_block_away base hn j 2056 257 (by omega) (by omega) (by omega)
  have readSeed (r : List Wire) (hr : r ⊆ L.usedWires) : regValue r s6.basis = regValue r s1.basis :=
    regValue_congr _ _ _ (fun q hq => outsideZ q (seedAway q (hr hq)))
  have hin6 : SkywalkSeedValues L (p+x) x 0 s6.basis := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · exact (readSeed L.a (arith_seed_components L).1).trans h1.2.a
    · exact (readSeed L.b (arith_seed_components L).2.1).trans h1.2.b
    · exact (readSeed L.constant (arith_seed_components L).2.2.1).trans h1.2.constant
    · exact (readSeed L.carry (arith_seed_components L).2.2.2).trans h1.2.carry
    · exact (outsideZ _ (seedAway _ (by simp [SkywalkSeedLayout.usedWires]))).trans h1.2.cin
    · exact (h6.2.1 _ (arith_mem base 0 1798 1797 (by omega) (by omega))).trans h1.2.orientation
  have oldhs7 := (directSkywalkLiteralSeed_unseed_eq base hn x Y.val hx s s1 s6 m1 m7
    hin oldhs1 hin6 h6.2.1).symm.trans hs7
  have h7 := skywalkUnseed_spec L 258 p x (skywalkShared_seed_widths base)
    (skywalkShared_seed_nodup base hn) (by omega) hp (hx.trans hp) s6 m7 hin6
  rw [oldhs7] at h7
  have frame7Z : ∀ q,q ∉ F.z → s7.basis q = s.basis q := by
    have hentry := arith_seed_input base hn x Y.val s.basis hin
    have readback (r : List Wire) (hb : regValue r s7.basis = regValue r s.basis) :
        ∀ q ∈ r,s7.basis q = s.basis q := (regValue_eq_iff r _ _).mp hb
    have hA := readback L.a (h7.2.a.trans hentry.a.symm)
    have hB := readback L.b (h7.2.b.trans hentry.b.symm)
    have hC := readback L.constant (h7.2.constant.trans hentry.constant.symm)
    have hD := readback L.carry (h7.2.carry.trans hentry.carry.symm)
    intro q hq
    by_cases hcin : q = L.cin
    · subst q; exact h7.2.cin.trans hentry.cin.symm
    by_cases hqa : q ∈ L.a
    · exact hA q hqa
    by_cases hqb : q ∈ L.b
    · exact hB q hqb
    by_cases hqc : q ∈ L.constant
    · exact hC q hqc
    by_cases hqd : q ∈ L.carry
    · exact hD q hqd
    have hout := arith_seed_away L q hcin hqa hqb hqc hqd
    have hb := skywalkSeed_frame L 258 p (skywalkShared_seed_widths base) s6 m7 q hout
    have hf := skywalkSeed_frame L 258 p (skywalkShared_seed_widths base) s m1 q hout
    rw [oldhs7] at hb
    rw [oldhs1] at hf
    exact hb.2.trans ((outsideZ q hq).trans hf.1)
  have hz7 : regValue F.z s7.basis = Z := by
    apply Eq.trans (regValue_congr _ _ _ ?_) value4
    intro q hq
    rw [skywalkShared_field_z] at hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    have hpaway := arith_block_away base hn j 0 1798 (by omega) (by omega) (by omega)
    have hsaway := arith_seed_outside base hn j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hseed := skywalkSeed_frame L 258 p (skywalkShared_seed_widths base) s6 m7 (base j) hsaway
    have hclear := arith_clear_outside base hn s4 m5 (base j) hpaway
    rw [oldhs7] at hseed
    rw [hs5] at hclear
    exact hseed.2.trans ((h6.2.2 _ hpaway).trans hclear)
  have hZ : Z < 2^256 := (ZMod.val_lt (directSkywalkResult divide (s.basis (base 2400)) x Y)).trans hp
  have high := skywalkShared_numerator_high_zero base s7.basis Z hz7 hZ
  have low7 : regValue (skywalkArithmeticNumerator base) s7.basis = Z := by
    change regValue (wireBlock base 2056 256++[base 2312]) s7.basis = Z at hz7
    rw [regValue_append] at hz7
    simpa [regValue,high,skywalkArithmeticNumerator] using hz7
  refine ⟨h7.1.trans (h6.1.trans h1.1),low7,?_⟩
  intro q hq
  by_cases hz : q ∈ F.z
  · change q ∈ wireBlock base 2056 256++[base 2312] at hz
    rcases List.mem_append.mp hz with hlow|hpad
    · exact False.elim (hq hlow)
    · have eq : q = base 2312 := by simpa using hpad
      subst q
      exact high.trans (arith_input_bit base hn x Y.val s.basis hin 2312 (by omega) (by omega) (by omega)).symm
  · exact frame7Z q hz

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.kernel_states
