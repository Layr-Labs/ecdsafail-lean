import ECDSAAdd.Arithmetic.CompactSkywalkCallerInteger
import ECDSAAdd.Arithmetic.CompressedTerminalEncodingBridge
import ECDSAAdd.Arithmetic.MappedCompressedAllocationSites
import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalEnvironment

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] skywalkSeed literalSkywalkSeed narrowSkywalkRoutedLoop
attribute [local irreducible] compactSkywalkForward run measurementCount
attribute [local irreducible] SkywalkTrace.next Nat.iterate

/-- Facts at the actual cleared raw caller boundary, before any history codec.
Every field and tape fact is derived from the original public input contract. -/
structure PreparationFacts (x : Nat) (Y : Fp) (entry origin : State) : Prop where
  sourceZero : regValue (skywalkSharedField base).a origin.basis = 0
  workZero : regValue (skywalkSharedField base).work origin.basis = 0
  unusedZero : regValue (skywalkSharedUnused base) origin.basis = 0
  targetValue : regValue (skywalkSharedField base).z origin.basis = Y.val
  env : Env base origin.basis
  targetHigh : origin.basis (base 2312) = false
  sourceHigh : origin.basis (base 1026) = false
  trace : skywalkTapeControls origin.basis (skywalkSharedTape base) =
    SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))
  legal : RawGroupLegal base 170 origin.basis
  controls : ∀ q ∈ [base 2400,base 2409,base 2410],origin.basis q = entry.basis q
  phase : origin.phase = entry.phase

/-- Clear uses only511,512,770. Every six-site group ends before510 or1538,
so its actual raw legality survives the caller's physical terminal clear. -/
private theorem clear_raw_legal (before after : State) (m : List Bool)
    (clear : run (skywalkArithmeticClear base) m before = after)
    (legal : RawGroupLegal base 170 before.basis) :
    RawGroupLegal base 170 after.basis := by
  have keep (j : Nat) (hj : j < 170) (u : Fin 6) :
      after.basis (compressedHistoryMap base (3*j) u) =
        before.basis (compressedHistoryMap base (3*j) u) := by
    have range : compressedHistoryId (3*j) u < 510 ∨
        (1028 ≤ compressedHistoryId (3*j) u ∧ compressedHistoryId (3*j) u < 1538) := by
      have hu := u.isLt
      unfold compressedHistoryId
      split <;> omega
    have away : base (compressedHistoryId (3*j) u) ∉ wires (skywalkArithmeticClear base) := by
      intro used
      rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at used
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at used
      rcases used with eq|eq|eq
      all_goals
        have same := base_injective eq
        omega
    have frame := run_preserves_outside (skywalkArithmeticClear base) m before
      (base (compressedHistoryId (3*j) u)) away
    rw [clear] at frame
    exact frame
  intro j hj
  rw [keep j hj 0,keep j hj 1,keep j hj 2,keep j hj 3,keep j hj 4,keep j hj 5]
  exact legal j hj

/-- The real literal seed, full raw compact loop, and actual terminal clear
prepare the unchanged field caller. No encoded-state Env is assumed. -/
theorem rawPreparation_facts
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m1 m2 m3 : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (s1 s2 origin : State)
    (hs1 : run (literalSkywalkSeed (literalSkywalkPoolSeed base) p) m1 s = s1)
    (hs2 : run (compactSkywalkForward base 0 512) m2 s1 = s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2 = origin) :
    PreparationFacts x Y s origin := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hp : p < 2^256 := by norm_num [p]
  have hp0 : 0 < p := by norm_num [p]
  have hpo : p%2 = 1 := by norm_num [p]
  have pool := skywalkShared_integer_nodup base hn
  have oldhs1 := (directSkywalkLiteralSeed_seed_eq base hn x Y.val hx s m1 hin).symm.trans hs1
  have h1 := skywalkSeed_spec (skywalkSharedSeed base) 258 p x
    (skywalkShared_seed_widths base) (skywalkShared_seed_nodup base hn)
    (by omega) hp (hx.trans hp) s m1 (arith_seed_input base hn x Y.val s.basis hin)
  rw [oldhs1] at h1
  have stage0 := arith_seed_stage0 base hn x Y.val hx s m1 hin
  rw [oldhs1] at stage0
  have oldhs2 := (compactSkywalkCaller_forward_eq base hn x p hp0 hx0 hpo hp hx
    (arith_coprime x hx0 hx) s1 m2 m2 stage0).symm.trans hs2
  have h2 := narrowSkywalkRouted512_spec base pool x p hp0 hx0 hpo hp hx
    (arith_coprime x hx0 hx) s1 m2 stage0
  rw [oldhs2] at h2
  have raw := compactSkywalkForward_512 base pool x p hp0 hx0 hpo hp hx
    (arith_coprime x hx0 hx) s1 m2 stage0
  rw [hs2] at raw
  have legalBefore := compact_terminal_raw_legal base pool x p hp0 hpo s2.basis raw.2
  have legal := clear_raw_legal s2 origin m3 hs3 legalBefore
  have h3 := skywalkTerminalClear_correct _ _ _ (arith_clear_gates base hn) s2 m3
  change (run (skywalkArithmeticClear base) m3 s2).phase = s2.phase ∧ _ at h3
  rw [hs3] at h3
  have clean := arith_clean_preparation base hn x Y.val hx0 hx s m1 m2 m3 hin
  rw [oldhs1,oldhs2,hs3] at clean
  have work := skywalkShared_clean_to_field base origin.basis clean
  have value : regValue (skywalkSharedField base).z origin.basis = Y.val := by
    have frame := arith_preparation_frame base hn s m1 m2 m3
    rw [oldhs1,oldhs2,hs3] at frame
    exact (regValue_congr _ _ _ frame).trans (arith_z_input base hn x Y.val s.basis hin)
  have tape : skywalkTapeControls origin.basis (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)) := by
    have frame := arith_tape_clear base hn s2 m3
    rw [hs3] at frame
    exact frame.trans (arith_tape base x s2.basis h2.2)
  have controls (q : Wire) (hq : q ∈ [base 2400,base 2409,base 2410]) :
      origin.basis q = s.basis q := by
    have outside := ho q hq
    have poolAway : q ∉ skywalkPoolWires base :=
      fun bad => outside (arith_block_subset_shared base 0 1798 (by omega) bad)
    have seedAway : q ∉ (skywalkSharedSeed base).usedWires :=
      fun bad => outside (arith_seed_subset_shared base bad)
    have k1 := (skywalkSeed_frame (skywalkSharedSeed base) 258 p
      (skywalkShared_seed_widths base) s m1 q seedAway).1
    have k2 := arith_record_outside base hn s1 m2 q poolAway
    have k3 := arith_clear_outside base hn s2 m3 q poolAway
    rw [oldhs1] at k1
    rw [oldhs2] at k2
    rw [hs3] at k3
    exact k3.trans (k2.trans k1)
  have environment : Env base origin.basis := env_of_canonical_source base hn
    origin.basis (0 : Fp) (by simpa using work.1) work.2.1 work.2.2
  have high := skywalkShared_numerator_high_zero base origin.basis Y.val value
    ((ZMod.val_lt Y).trans hp)
  exact ⟨work.1,work.2.1,work.2.2,value,environment,high,environment.2.2,
    tape,legal,controls,h3.1.trans (h2.1.trans h1.1)⟩

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.rawPreparation_facts
