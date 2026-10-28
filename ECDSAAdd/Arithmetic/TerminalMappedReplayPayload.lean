import ECDSAAdd.Arithmetic.MappedCompressedReplayIdentity
import ECDSAAdd.Arithmetic.TerminalMixedTapeControls

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 CompressedFieldSupport
attribute [local irreducible] SkywalkTrace.trace mixedTranscriptTape mixedTranscriptUnitTrace

def trimLetters : List MixedTranscriptLetter := indexedLetters 0 511

private theorem indexed_step (start n : Nat) :
    indexedLetters start (n+1)=tapeLetter start::indexedLetters (start+1) n := by
  simp only [indexedLetters,List.range_succ_eq_map,List.map_cons,List.map_map,Function.comp_def]
  simp only [Nat.add_zero,Nat.succ_eq_add_one,Nat.add_comm,Nat.add_left_comm]

theorem indexedLetters_append (start n k : Nat) :
    indexedLetters start (n+k)=indexedLetters start n++indexedLetters (start+n) k := by
  induction n generalizing start with
  | zero => simp only [Nat.zero_add,Nat.add_zero,indexedLetters,List.range_zero,List.map_nil,List.nil_append]
  | succ n ih =>
    rw [show n+1+k=(n+k)+1 by omega,indexed_step,indexed_step,ih]
    simp only [List.cons_append]
    rw [show start+1+n=start+(n+1) by omega]

theorem trimLetters_last : trimLetters++[tapeLetter 511]=mixedTranscriptTape base := by
  have split := indexedLetters_append 0 511 1
  have last : indexedLetters 511 1=[tapeLetter 511] := by
    simp only [indexedLetters,List.range_one,List.map_cons,List.map_nil,Nat.add_zero]
  rw [last] at split
  simpa only [Nat.zero_add,Nat.reduceAdd,trimLetters,indexedLetters_full] using split.symm

private theorem getD_defaults {α : Type} (ls : List α) (i : Nat) (hi : i<ls.length) (a b : α) :
    ls.getD i a=ls.getD i b := by
  induction ls generalizing i with
  | nil => simp at hi
  | cons h t ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)

theorem lastLetter_controls (origin : BasisState) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    (mixedTranscriptBit origin (base 2400) (tapeLetter 511).1.1 (tapeLetter 511).2.1,
      mixedTranscriptBit origin (base 2400) (tapeLetter 511).1.2 (tapeLetter 511).2.2)=(true,false) := by
  have same : terminalMixedLetter base=tapeLetter 511 :=
    getD_defaults _ 511 (by rw [mixedTranscriptTape_length]; decide) _ _
  rw [←same]
  exact terminalMixedLetter_controls base origin (base 2400) x hx0 hx hr

attribute [local irreducible] indexedLetters trimLetters

private theorem replay_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplay (a++b) Q=skywalkPayloadReplay b (skywalkPayloadReplay a Q) := by
  induction a generalizing Q with
  | nil => rfl
  | cons l ls ih => exact ih (skywalkPayloadCell l.1 l.2 Q)

private theorem inverse_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplayInverse (a++b) Q=
      skywalkPayloadReplayInverse a (skywalkPayloadReplayInverse b Q) := by
  induction a with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.cons_append,skywalkPayloadReplayInverse,ih]

private theorem terminal_uncell (Y : Fp) : skywalkPayloadUncell true false (Y,Y)=(Y,Y) := by
  apply Prod.ext <;> simp only [skywalkPayloadUncell,Bool.false_eq_true,if_false,if_true]
  · ring

/-- The actual511-letter field prefix already reaches duplicated quotient
words. This is derived from the original512-trace contract and terminal control,
without adding a new point-input or record assumption. -/
theorem trimLetters_quotient (origin : BasisState) (x : Nat) (Y : Fp)
    (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) trimLetters) (2*Y,0)=
      (if origin (base 2400) then Y/(x : Fp) else Y,
       if origin (base 2400) then Y/(x : Fp) else Y) := by
  have full := mixedTranscriptTape_quotient base origin (base 2400) x Y hx0 hx hr
  rw [←trimLetters_last] at full
  simp only [mixedTranscriptControls,List.map_append,List.map_cons,List.map_nil,
    lastLetter_controls origin x hx0 hx hr,replay_append,skywalkPayloadReplay] at full
  have inv := congrArg (skywalkPayloadUncell true false) full
  rw [skywalkPayloadUncell_cell,terminal_uncell] at inv
  exact inv

theorem trimLetters_product (origin : BasisState) (x : Nat) (Y : Fp)
    (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) trimLetters) (Y,Y)=
      (2*(if origin (base 2400) then Y*(x : Fp) else Y),0) := by
  have full := mixedTranscriptTape_product base origin (base 2400) x Y hx0 hx hr
  rw [←trimLetters_last] at full
  simpa only [mixedTranscriptControls,List.map_append,List.map_cons,List.map_nil,
    lastLetter_controls origin x hx0 hx hr,inverse_append,skywalkPayloadReplayInverse,
    terminal_uncell] using full

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.trimLetters_quotient
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.trimLetters_product
