import ECDSAAdd.Arithmetic.CompactOffsetCallerStates
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open Secp256k1 DirectSkywalk
attribute [local irreducible] run compactSkywalkForward compactSkywalkReverse
/-- Full executable contract for every nonzero canonical divisor, both
control branches, arbitrary incoming phase and arbitrary measurement records.
All caller bits outside the numerator, including b and both selectors, restore. -/
theorem compactOffsetCallerArithmetic_run (divide : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (b effG effS : Wire)
    (ho : ∀ q∈[b,effG,effS],q∉skywalkSharedWires w)
    (hl : MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput w x Y.val s.basis)
    (hg0 : s.basis effG=false) (hs0 : s.basis effS=false) :
    DirectSkywalkArithmeticStrong divide w b x Y s
      (run (compactOffsetCallerArithmetic divide w b effG effS) m s) := by
  let P : State → State → Prop := fun initial out =>
    SkywalkArithmeticInput w x Y.val initial.basis → initial.basis effG=false →
      initial.basis effS=false → DirectSkywalkArithmeticStrong divide w b x Y initial out
  have hh := skywalkRunSeven
    (literalSkywalkSeed (literalSkywalkPoolSeed w) p) (compactSkywalkForward w 0 512)
    (skywalkArithmeticClear w)
    (if divide then offsetBorrowedSharedFieldDivision w b effG effS
      else offsetBorrowedInverseSharedFieldMultiplication w b effG effS)
    (skywalkArithmeticClear w) (compactSkywalkReverse w 0 512)
    (literalSkywalkUnseed (literalSkywalkPoolSeed w) p) P
    (by
      intro initial s1 s2 s3 s4 s5 s6 s7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 hi hg hs
      unfold DirectSkywalkArithmeticStrong
      exact compactOffsetCallerArithmetic_states divide w hn b effG effS ho hl x Y hx0 hx initial
        m1 m2 m3 m4 m5 m6 m7 hi hg hs s1 s2 s3 s4 s5 s6 s7 h1 h2 h3 h4 h5 h6 h7)
    s m
  simpa only [compactOffsetCallerArithmetic] using hh hin hg0 hs0

/-- Counts for the emitted intermediate kernel, including both integer
passes and the measured selectors. These do not meet the final <600KT goal. -/
theorem compactOffsetCallerArithmetic_counts (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (b effG effS : Wire)
    (ho : ∀ q∈[b,effG,effS],q∉skywalkSharedWires w)
    (hl : MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w)) :
    toffoliCount (compactOffsetCallerArithmetic true w b effG effS)=1054709 ∧
    measurementCount (compactOffsetCallerArithmetic true w b effG effS)=726261 ∧
    toffoliCount (compactOffsetCallerArithmetic false w b effG effS)=1055222 ∧
    measurementCount (compactOffsetCallerArithmetic false w b effG effS)=726262 := by
  have hs := literalSkywalkPoolSeed_counts w p
  have hi := compactSkywalkForward_512_counts w (skywalkShared_integer_nodup w hn)
  have hr := compactSkywalkReverse_512_counts w (skywalkShared_integer_nodup w hn)
  have hc := skywalkTerminalClear_counts (w 511) (w 512) (w 770)
  have hf := directSkywalk_record_layout w b effG effS hl
  have hd := offsetBorrowedSharedFieldDivision_counts w b effG effS hn hf ho
  have hm := offsetBorrowedInverseSharedFieldMultiplication_counts w b effG effS hn hf ho
  simp only [compactOffsetCallerArithmetic,skywalkArithmeticClear,if_true,Bool.false_eq_true,if_false,
    toffoliCount_append,measurementCount_append,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,
    hi.1,hi.2,hr.1,hr.2,hc.1,hc.2,hd.1,hd.2,hm.1,hm.2]
  norm_num

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactOffsetCallerArithmetic_run
#print axioms ECDSAAdd.Arithmetic.compactOffsetCallerArithmetic_counts
