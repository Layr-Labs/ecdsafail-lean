import ECDSAAdd.Arithmetic.NativeFirstDirectCallerInput
import ECDSAAdd.Arithmetic.NativeFirstDirectReferenceEq
import ECDSAAdd.Arithmetic.DirectSkywalkLiteralSeedBridge
import ECDSAAdd.Arithmetic.CompactSkywalkStageStepProof

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open DirectSkywalk
attribute [local irreducible] run forward reference literalSkywalkSeed skywalkSeed compactSkywalkTick

/-- All first-stage history and future-clean assertions follow from the
existing caller, not from an additional promised compressed history. -/
theorem caller_first_stage (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput w x y s.basis) :
    CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 1
      (run (forward w) m s).basis := by
  have pool := skywalkShared_integer_nodup w hn
  have ready := caller_ready w hn x y s.basis hin
  have stage0 := arith_seed_stage0 w hn x y hx s [] hin
  have seedEq := directSkywalkLiteralSeed_seed_eq w hn x y hx s [] hin
  rw [←seedEq] at stage0
  have compact0 := (compactSkywalkStage_zero_iff w
    (SkywalkRails.encode false false (x:Int) (p:Int)) _).mpr stage0
  have step := compactSkywalkStageStep w pool x p 0
    (by norm_num [p]) hx0 (by norm_num [p]) (by norm_num [p]) hx
    (arith_coprime x hx0 hx) (by omega)
    (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s) [] compact0
  have he := forward_reference_eq w pool x hx s m [] ready.1 ready.2
  have ref : run (reference w) [] s=
      run (compactSkywalkTick w 0) [] (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s) := by
    rw [reference,run_append]
    simp only [List.take_nil,List.drop_nil]
  rw [he,ref]
  exact step.2

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.caller_first_stage
