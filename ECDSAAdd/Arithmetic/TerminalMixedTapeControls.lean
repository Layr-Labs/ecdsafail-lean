import ECDSAAdd.Math.SkywalkTerminalMixedControls
import ECDSAAdd.Arithmetic.MixedTranscriptReplay

set_option maxHeartbeats 800000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic
open Secp256k1
attribute [local irreducible] SkywalkTrace.trace skywalkSharedTape

def terminalMixedLetter (w : Nat → Wire) : MixedTranscriptLetter :=
  (mixedTranscriptTape w).getD 511 ((w 0,w 1028),(false,false))

/-- Actual recorded controls and the inactive unit trace give the same final
letter. This derives terminal controls from the original caller trace premise. -/
theorem terminalMixedLetter_controls (w : Nat → Wire) (base : BasisState) (b : Wire)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    (mixedTranscriptBit base b (terminalMixedLetter w).1.1 (terminalMixedLetter w).2.1,
      mixedTranscriptBit base b (terminalMixedLetter w).1.2 (terminalMixedLetter w).2.2)=
      (true,false) := by
  let read : (Wire×Wire) → Bool×Bool := fun r => (base r.1,base r.2)
  have record : (skywalkSharedTape w).map read=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)) := hr
  have selected := SkywalkTrace.mixed_letter_index511 (skywalkSharedTape w) read
    (base b) (w 0,w 1028) x hx0 hx record
  cases hb : base b <;>
    simpa only [terminalMixedLetter,mixedTranscriptTape,mixedTranscriptUnitTrace,
      mixedTranscriptBit,read,hb,if_true,if_false,Bool.false_eq_true] using selected

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.terminalMixedLetter_controls
