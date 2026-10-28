import ECDSAAdd.Arithmetic.DirectSkywalkLiteralSeedBridge
import ECDSAAdd.Arithmetic.BalancedSharedDivision
import ECDSAAdd.Arithmetic.BalancedInverseSharedMultiplication

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic
open Secp256k1 DirectSkywalk

/-- Direct caller-divisor kernel: integer forward and restoration passes
surround a field replay selected by b. No safe-copy divisor is allocated. -/
def directSkywalkArithmetic (divide : Bool) (w : Nat → Wire) (b effG effS : Wire) : Program :=
  literalSkywalkSeed (literalSkywalkPoolSeed w) p ++
  (narrowSkywalkRoutedLoop w 0 512 ++
  (skywalkArithmeticClear w ++
  ((if divide then balancedSharedFieldDivision w b effG effS
      else balancedInverseSharedFieldMultiplication w b effG effS) ++
  (skywalkArithmeticClear w ++
  (narrowSkywalkRoutedUnloop w 0 512 ++ literalSkywalkUnseed (literalSkywalkPoolSeed w) p)))))

def directSkywalkResult (divide enabled : Bool) (x : Nat) (Y : Fp) : Fp :=
  if enabled then skywalkArithmeticResult divide x Y else Y

def DirectSkywalkArithmeticStrong (divide : Bool) (w : Nat → Wire) (b : Wire)
    (x : Nat) (Y : Fp) (initial out : State) : Prop :=
  out.phase=initial.phase ∧ regValue (skywalkArithmeticNumerator w) out.basis=
    (directSkywalkResult divide (initial.basis b) x Y).val ∧
    ∀ q,q∉skywalkArithmeticNumerator w → out.basis q=initial.basis q

attribute [local irreducible] skywalkSeed skywalkUnseed literalSkywalkSeed literalSkywalkUnseed
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop run
attribute [local irreducible] balancedSharedFieldDivision balancedInverseSharedFieldMultiplication
attribute [local irreducible] skywalkFieldDivisionRetained skywalkFieldMultiplicationRetained
attribute [local irreducible] SkywalkTrace.next Nat.iterate

theorem directSkywalkArithmetic_states (divide : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (b effG effS : Wire)
    (ho : ∀ q∈[b,effG,effS],q∉skywalkSharedWires w)
    (hl : MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hin : SkywalkArithmeticInput w x Y.val s.basis)
    (hg0 : s.basis effG=false) (hs0 : s.basis effS=false)
    (s1 s2 s3 s4 s5 s6 s7 : State)
    (hs1 : run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) m1 s=s1)
    (hs2 : run (narrowSkywalkRoutedLoop w 0 512) m2 s1=s2)
    (hs3 : run (skywalkArithmeticClear w) m3 s2=s3)
    (hs4 : run (if divide then balancedSharedFieldDivision w b effG effS
      else balancedInverseSharedFieldMultiplication w b effG effS) m4 s3=s4)
    (hs5 : run (skywalkArithmeticClear w) m5 s4=s5)
    (hs6 : run (narrowSkywalkRoutedUnloop w 0 512) m6 s5=s6)
    (hs7 : run (literalSkywalkUnseed (literalSkywalkPoolSeed w) p) m7 s6=s7) :
    s7.phase=s.phase ∧ regValue (skywalkArithmeticNumerator w) s7.basis=
      (directSkywalkResult divide (s.basis b) x Y).val ∧
      ∀ q,q∉skywalkArithmeticNumerator w → s7.basis q=s.basis q := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let L := skywalkSharedSeed w
  let F := skywalkSharedField w
  let Z := (directSkywalkResult divide (s.basis b) x Y).val
  have hw := skywalkShared_seed_widths w
  have hnseed := skywalkShared_seed_nodup w hn
  have hnpool := skywalkShared_integer_nodup w hn
  have hp : p < 2^256 := by norm_num [p]
  have hp0 : 0 < p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have oldhs1 := (directSkywalkLiteralSeed_seed_eq w hn x Y.val hx s m1 hin).symm.trans hs1
  have h1 := skywalkSeed_spec L 258 p x hw hnseed (by omega) hp (hx.trans hp)
    s m1 (arith_seed_input w hn x Y.val s.basis hin)
  rw [oldhs1] at h1
  have hstage0 := arith_seed_stage0 w hn x Y.val hx s m1 hin
  rw [oldhs1] at hstage0
  have h2 := narrowSkywalkRouted512_spec w hnpool x p hp0 hx0 hpo hp hx (arith_coprime x hx0 hx) s1 m2 hstage0
  rw [hs2] at h2
  have h3 := skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) s2 m3
  change (run (skywalkArithmeticClear w) m3 s2).phase=s2.phase ∧ _ at h3
  rw [hs3] at h3
  have hclean := arith_clean_preparation w hn x Y.val hx0 hx s m1 m2 m3 hin
  rw [oldhs1,hs2,hs3] at hclean
  have hwork := skywalkShared_clean_to_field w s3.basis hclean
  have hz3 : regValue F.z s3.basis=Y.val := by
    have hk := arith_preparation_frame w hn s m1 m2 m3
    rw [oldhs1,hs2,hs3] at hk
    exact (regValue_congr _ _ _ hk).trans (arith_z_input w hn x Y.val s.basis hin)
  have htape : skywalkTapeControls s3.basis (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)) :=
    by
      have hk := arith_tape_clear w hn s2 m3
      rw [hs3] at hk
      exact hk.trans (arith_tape w x s2.basis h2.2)
  have keepControl (q : Wire) (hq : q∈[b,effG,effS]) : s3.basis q=s.basis q := by
    have outside := ho q hq
    have poolAway : q∉skywalkPoolWires w :=
      fun bad => outside (arith_block_subset_shared w 0 1798 (by omega) bad)
    have seedAway : q∉(skywalkSharedSeed w).usedWires :=
      fun bad => outside (arith_seed_subset_shared w bad)
    have k1 := (skywalkSeed_frame (skywalkSharedSeed w) 258 p
      (skywalkShared_seed_widths w) s m1 q seedAway).1
    have k2 := arith_record_outside w hn s1 m2 q poolAway
    have k3 := arith_clear_outside w hn s2 m3 q poolAway
    rw [oldhs1] at k1
    rw [hs2] at k2
    rw [hs3] at k3
    exact k3.trans (k2.trans k1)
  have hg3 : s3.basis effG=false := (keepControl effG (by simp)).trans hg0
  have hs3clean : s3.basis effS=false := (keepControl effS (by simp)).trans hs0
  have hb3 : s3.basis b=s.basis b := keepControl b (by simp)
  have hf := directSkywalk_record_layout w b effG effS hl
  have h4 : s4.phase=s3.phase ∧ PairFrame F.z F.a s3.basis Z 0 s4.basis := by
    have hbefore : PairFrame F.z F.a s3.basis Y.val 0 s3.basis := ⟨hz3,hwork.1,fun _ _ _ => rfl⟩
    cases divide
    · have hh := balancedInverseSharedFieldMultiplication_spec w b effG effS hn hf ho
        s3.basis hg3 hs3clean hwork.2.1 hwork.2.2 x Y hx0 hx htape s3 m4 hbefore
      change run (balancedInverseSharedFieldMultiplication w b effG effS) m4 s3=s4 at hs4
      rw [hs4] at hh
      simpa only [Z,directSkywalkResult,skywalkArithmeticResult,Bool.false_eq_true,if_false,hb3] using hh
    · have hh := balancedSharedFieldDivision_spec w b effG effS hn hf ho
        s3.basis hg3 hs3clean hwork.2.1 hwork.2.2 x Y hx0 hx htape s3 m4 hbefore
      change run (balancedSharedFieldDivision w b effG effS) m4 s3=s4 at hs4
      rw [hs4] at hh
      simpa only [Z,directSkywalkResult,skywalkArithmeticResult,if_true,hb3] using hh
  have hframe4 := arith_field_frame F s3.basis s4.basis Z hwork.1 h4.2
  have h5 := skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) s4 m5
  change (run (skywalkArithmeticClear w) m5 s4).phase=s4.phase ∧ _ at h5
  rw [hs5] at h5
  have hframe5 := arith_clear_transport w hn s2 s4 m3 m5 (by rw [hs3]; exact hframe4)
  rw [hs5] at hframe5
  have hstage5 := arith_stage_congr w _ s2.basis s5.basis h2.2
    (fun q hq => hframe5 q (arith_pool_away_z w hn q hq))
  have h6 := narrowSkywalkRoutedUnloop_restore_pool w hnpool x p hp0 hx0 hpo hp hx (arith_coprime x hx0 hx) s1 s5 m6 hstage0 hstage5
  rw [hs6] at h6
  have outsideZ (q : Wire) (hq : q∉F.z) : s6.basis q=s1.basis q := by
    by_cases hpool : q∈skywalkPoolWires w
    · exact h6.2 q hpool
    · have hb := arith_unrecord_outside w hn s5 m6 q hpool
      have hf := arith_record_outside w hn s1 m2 q hpool
      rw [hs6] at hb
      rw [hs2] at hf
      exact hb.trans ((hframe5 q hq).trans hf)
  have seedAway (q : Wire) (hq : q∈L.usedWires) : q∉F.z := by
    change q∈w 2313::(wireBlock w 0 258++wireBlock w 770 258++
      wireBlock w 1798 258++wireBlock w 1540 257) at hq
    rw [skywalkShared_field_z]
    rcases List.mem_cons.mp hq with rfl|hr
    · exact arith_block_away w hn 2313 2056 257 (by omega) (by omega) (by omega)
    · simp only [List.mem_append,or_assoc] at hr
      rcases hr with hq|hq|hq|hq
      all_goals
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
        simp only [List.mem_range'_1] at hj
        exact arith_block_away w hn j 2056 257 (by omega) (by omega) (by omega)
  have readSeed (r : List Wire) (hr : r⊆L.usedWires) : regValue r s6.basis=regValue r s1.basis :=
    regValue_congr _ _ _ (fun q hq => outsideZ q (seedAway q (hr hq)))
  have hin6 : SkywalkSeedValues L (p+x) x 0 s6.basis := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · exact (readSeed L.a (arith_seed_components L).1).trans h1.2.a
    · exact (readSeed L.b (arith_seed_components L).2.1).trans h1.2.b
    · exact (readSeed L.constant (arith_seed_components L).2.2.1).trans h1.2.constant
    · exact (readSeed L.carry (arith_seed_components L).2.2.2).trans h1.2.carry
    · exact (outsideZ _ (seedAway _ (by simp [SkywalkSeedLayout.usedWires]))).trans h1.2.cin
    · exact (h6.2 _ (arith_mem w 0 1798 1797 (by omega) (by omega))).trans h1.2.orientation
  have oldhs7 := (directSkywalkLiteralSeed_unseed_eq w hn x Y.val hx s s1 s6 m1 m7
    hin oldhs1 hin6 h6.2).symm.trans hs7
  have h7 := skywalkUnseed_spec L 258 p x hw hnseed (by omega) hp (hx.trans hp) s6 m7 hin6
  rw [oldhs7] at h7
  have frame7Z : ∀ q,q∉F.z → s7.basis q=s.basis q := by
    have hentry := arith_seed_input w hn x Y.val s.basis hin
    have readback (r : List Wire) (hb : regValue r s7.basis=regValue r s.basis) :
        ∀ q∈r,s7.basis q=s.basis q := (regValue_eq_iff r _ _).mp hb
    have hA := readback L.a (h7.2.a.trans hentry.a.symm)
    have hB := readback L.b (h7.2.b.trans hentry.b.symm)
    have hC := readback L.constant (h7.2.constant.trans hentry.constant.symm)
    have hD := readback L.carry (h7.2.carry.trans hentry.carry.symm)
    intro q hq
    by_cases hcin : q=L.cin
    · subst q; exact h7.2.cin.trans hentry.cin.symm
    by_cases hqa : q∈L.a
    · exact hA q hqa
    by_cases hqb : q∈L.b
    · exact hB q hqb
    by_cases hqc : q∈L.constant
    · exact hC q hqc
    by_cases hqd : q∈L.carry
    · exact hD q hqd
    have hout := arith_seed_away L q hcin hqa hqb hqc hqd
    have hb := skywalkSeed_frame L 258 p hw s6 m7 q hout
    have hf := skywalkSeed_frame L 258 p hw s m1 q hout
    rw [oldhs7] at hb
    rw [oldhs1] at hf
    exact hb.2.trans ((outsideZ q hq).trans hf.1)
  have hz7 : regValue F.z s7.basis=Z := by
    apply Eq.trans (regValue_congr _ _ _ ?_) h4.2.1
    intro q hq
    rw [skywalkShared_field_z] at hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    have hpaway := arith_block_away w hn j 0 1798 (by omega) (by omega) (by omega)
    have hsaway := arith_seed_outside w hn j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hseed := skywalkSeed_frame L 258 p hw s6 m7 (w j) hsaway
    have hloop := arith_unrecord_outside w hn s5 m6 (w j) hpaway
    have hclear := arith_clear_outside w hn s4 m5 (w j) hpaway
    rw [oldhs7] at hseed
    rw [hs6] at hloop
    rw [hs5] at hclear
    exact hseed.2.trans (hloop.trans hclear)
  have hZ : Z < 2^256 := (ZMod.val_lt (directSkywalkResult divide (s.basis b) x Y)).trans hp
  have hhigh := skywalkShared_numerator_high_zero w s7.basis Z hz7 hZ
  have hlow7 : regValue (skywalkArithmeticNumerator w) s7.basis=Z := by
    change regValue (wireBlock w 2056 256++[w 2312]) s7.basis=Z at hz7
    rw [regValue_append] at hz7
    simpa [regValue,hhigh,skywalkArithmeticNumerator] using hz7
  refine ⟨h7.1.trans (h6.1.trans (h5.1.trans (h4.1.trans (h3.1.trans (h2.1.trans h1.1))))),hlow7,?_⟩
  intro q hq
  by_cases hz : q∈F.z
  · change q∈wireBlock w 2056 256++[w 2312] at hz
    rcases List.mem_append.mp hz with hlow|hpad
    · exact False.elim (hq hlow)
    · have he : q=w 2312 := by simpa using hpad
      subst q
      exact hhigh.trans (arith_input_bit w hn x Y.val s.basis hin 2312 (by omega) (by omega) (by omega)).symm
  · exact frame7Z q hz

/-- Full executable contract for every nonzero canonical divisor, both
control branches, arbitrary incoming phase and arbitrary measurement records.
All caller bits outside the numerator, including b and both selectors, restore. -/
theorem directSkywalkArithmetic_run (divide : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (b effG effS : Wire)
    (ho : ∀ q∈[b,effG,effS],q∉skywalkSharedWires w)
    (hl : MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput w x Y.val s.basis)
    (hg0 : s.basis effG=false) (hs0 : s.basis effS=false) :
    DirectSkywalkArithmeticStrong divide w b x Y s
      (run (directSkywalkArithmetic divide w b effG effS) m s) := by
  let P : State → State → Prop := fun initial out =>
    SkywalkArithmeticInput w x Y.val initial.basis → initial.basis effG=false →
      initial.basis effS=false → DirectSkywalkArithmeticStrong divide w b x Y initial out
  have hh := skywalkRunSeven
    (literalSkywalkSeed (literalSkywalkPoolSeed w) p) (narrowSkywalkRoutedLoop w 0 512)
    (skywalkArithmeticClear w)
    (if divide then balancedSharedFieldDivision w b effG effS
      else balancedInverseSharedFieldMultiplication w b effG effS)
    (skywalkArithmeticClear w) (narrowSkywalkRoutedUnloop w 0 512)
    (literalSkywalkUnseed (literalSkywalkPoolSeed w) p) P
    (by
      intro initial s1 s2 s3 s4 s5 s6 s7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 hi hg hs
      unfold DirectSkywalkArithmeticStrong
      exact directSkywalkArithmetic_states divide w hn b effG effS ho hl x Y hx0 hx initial
        m1 m2 m3 m4 m5 m6 m7 hi hg hs s1 s2 s3 s4 s5 s6 s7 h1 h2 h3 h4 h5 h6 h7)
    s m
  simpa only [directSkywalkArithmetic] using hh hin hg0 hs0

/-- Counts for the emitted intermediate kernel, including both integer
passes and the measured selectors. These do not meet the final <600KT goal. -/
theorem directSkywalkArithmetic_counts (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (b effG effS : Wire)
    (ho : ∀ q∈[b,effG,effS],q∉skywalkSharedWires w)
    (hl : MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w)) :
    toffoliCount (directSkywalkArithmetic true w b effG effS)=1185269 ∧
    measurementCount (directSkywalkArithmetic true w b effG effS)=856819 ∧
    toffoliCount (directSkywalkArithmetic false w b effG effS)=1185270 ∧
    measurementCount (directSkywalkArithmetic false w b effG effS)=856820 := by
  have hs := literalSkywalkPoolSeed_counts w p
  have hi := narrowSkywalkRouted512_counts w (skywalkShared_integer_nodup w hn)
  have hc := skywalkTerminalClear_counts (w 511) (w 512) (w 770)
  have hf := directSkywalk_record_layout w b effG effS hl
  have hd := balancedSharedFieldDivision_counts w b effG effS hn hf ho
  have hm := balancedInverseSharedFieldMultiplication_counts w b effG effS hn hf ho
  simp only [directSkywalkArithmetic,skywalkArithmeticClear,if_true,Bool.false_eq_true,if_false,
    toffoliCount_append,measurementCount_append,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,
    hi.1,hi.2.1,hi.2.2.1,hi.2.2.2,hc.1,hc.2,hd.1,hd.2,hm.1,hm.2]
  norm_num

end ECDSAAdd.Arithmetic
