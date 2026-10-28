import ECDSAAdd.Arithmetic.DirectSkywalkCleanup
import ECDSAAdd.Arithmetic.LiteralSkywalkSeedSharedBridge
import ECDSAAdd.Arithmetic.MixedTranscriptReplay

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open Secp256k1 DirectSkywalk

private theorem directSkywalk_zip_records (rs : List (Wire×Wire)) (cs : List (Bool×Bool))
    (P : Wire×Wire → Prop) (hlen : rs.length=cs.length)
    (hl : ∀ l∈rs.zip cs,P l.1) : ∀ r∈rs,P r := by
  induction rs generalizing cs with
  | nil => simp
  | cons r rs ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have he : rs.length=cs.length := by simpa using hlen
      intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hl (q,c) (by simp)
      · exact ih cs he (fun l hm => hl l (by simp [hm])) q hq

theorem directSkywalk_record_layout (w : Nat → Wire) (b effG effS : Wire)
    (hl : MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w)) :
    ∀ r∈skywalkSharedTape w,MixedTranscriptFieldLayout w b r.1 r.2 effG effS :=
  directSkywalk_zip_records _ _ _
    ((skywalkShared_tape_length w).trans mixedTranscriptUnitTrace_length.symm) hl

/-- The loaned One is already clean in the original arithmetic input. -/
theorem directSkywalkLiteralSeed_seed_eq (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (x y : Nat) (hx : x<p)
    (s : State) (m : List Bool) (hin : SkywalkArithmeticInput w x y s.basis) :
    run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) m s=
      run (skywalkSeed (skywalkSharedSeed w) p) m s :=
  literalSkywalkSeedSharedBridge_seed_eq w p x hn arith_modulus_bound
    (hx.trans arith_modulus_bound) s m m (arith_seed_input w hn x y s.basis hin)
    (arith_input_bit w hn x y s.basis hin 1028 (by omega) (by omega) (by omega))

/-- The integer unloop restores the loaned One to its post-seed value;
the old seed frame identifies that value with the original clean input. -/
theorem directSkywalkLiteralSeed_unseed_eq (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (x y : Nat) (hx : x<p)
    (s s1 s6 : State) (m1 m7 : List Bool)
    (hin : SkywalkArithmeticInput w x y s.basis)
    (hs1 : run (skywalkSeed (skywalkSharedSeed w) p) m1 s=s1)
    (hin6 : SkywalkSeedValues (skywalkSharedSeed w) (p+x) x 0 s6.basis)
    (hpool : ∀q∈skywalkPoolWires w,s6.basis q=s1.basis q) :
    run (literalSkywalkUnseed (literalSkywalkPoolSeed w) p) m7 s6=
      run (skywalkUnseed (skywalkSharedSeed w) p) m7 s6 := by
  have one1 := literalSkywalkSeedSharedBridge_oldSeed_outsideA w p x hn
    arith_modulus_bound (hx.trans arith_modulus_bound) s m1
    (arith_seed_input w hn x y s.basis hin) (w 1028)
    (arith_block_away w hn 1028 0 258 (by omega) (by omega) (by omega))
  rw [hs1] at one1
  have one0 := arith_input_bit w hn x y s.basis hin 1028
    (by omega) (by omega) (by omega)
  have one6 := (hpool (w 1028) (arith_mem w 0 1798 1028 (by omega) (by omega))).trans
    (one1.trans one0)
  exact literalSkywalkSeedSharedBridge_unseed_eq w p x hn arith_modulus_bound
    (hx.trans arith_modulus_bound) s6 m7 m7 hin6 one6

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.directSkywalkLiteralSeed_seed_eq
#print axioms ECDSAAdd.Arithmetic.directSkywalkLiteralSeed_unseed_eq
