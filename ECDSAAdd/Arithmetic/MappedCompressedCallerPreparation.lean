import ECDSAAdd.Arithmetic.MappedCompressedRawPreparation
import ECDSAAdd.Arithmetic.CompressedForwardCallerEquality
import ECDSAAdd.Arithmetic.MappedCompressedCanonicalFrame
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run compactSkywalkForward compressedCompactForward
  literalSkywalkSeed skywalkSeed skywalkArithmeticClear allGroupEncode

/-- The actual compressed caller prefix supplies the verified field
contract by an exact raw witness, not an assumed decoded-history state. -/
theorem compressedPreparation_facts (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (m1 m2 m3 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (s1 s2 s3 : State)
    (hs1 : run (literalSkywalkSeed (literalSkywalkPoolSeed base) p) m1 s=s1)
    (hs2 : run (compressedCompactForward base 0 512) m2 s1=s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2=s3) :
    ∃ origin : State,PreparationFacts x Y s origin ∧
      origin.phase=s3.phase ∧ s3=run (allGroupEncode base 170) [] origin ∧
      EncodedCanonicalFrame origin.basis Y 0 s3 := by
  have pool := skywalkShared_integer_nodup base hn
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have oldSeed := (directSkywalkLiteralSeed_seed_eq base hn x Y.val hx s m1 hin).symm.trans hs1
  have stage0 := arith_seed_stage0 base hn x Y.val hx s m1 hin
  rw [oldSeed] at stage0
  let recorded := run (compactSkywalkForward base 0 512) [] s1
  let origin := run (skywalkArithmeticClear base) m3 recorded
  have facts := rawPreparation_facts hn ho x Y hx0 hx s m1 [] m3 hin s1 recorded origin hs1 rfl rfl
  have forward := compressedCompactForward_caller_eq base hn hlo x p hp0 hx0 hpo hp hx
    (arith_coprime x hx0 hx) s1 m2 [] stage0
  rw [hs2] at forward
  have encoded : s3=run (allGroupEncode base 170) [] origin := by
    rw [←hs3,forward]
    exact (full_encoder_clear_commute base pool hlo recorded [] m3).symm
  have encoderPhase := allGroupEncode_phase base pool hlo 170 (by decide) origin [] facts.legal
  have phase : origin.phase=s3.phase := by
    rw [encoded]
    exact encoderPhase.symm
  refine ⟨origin,facts,phase,encoded,origin,phase,?_,encoded⟩
  exact ⟨facts.targetValue,by simpa only [ZMod.val_zero] using facts.sourceZero,fun _ _ _ => rfl⟩

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.compressedPreparation_facts
