import ECDSAAdd.Arithmetic.RecordedRailApply258Layout
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply258
open RecordedRailDefer
private theorem segment_counts (a b bank : List Wire) (cin even odd : Wire)
    (aw : a.length=258) (bw : b.length=258) (kw : bank.length=32)
    (j : Nat) (hj : j<7) :
    recordedToffoliCount (segment a b (bank.take 31) cin even odd j)=32 ∧
    recordedMeasurementCount (segment a b (bank.take 31) cin even odd j)=(if j=0 then 31 else 32) := by
  have ca := chunk_length a aw j hj
  have cb := chunk_length b bw j hj
  have shape := RecordedRailVented.aligned_shape (chunk a j) (chunk b j) (bank.take 31)
    (by simp [RecordedRailVented.Aligned,ca,cb,kw])
  by_cases hz : j=0
  · have c := RecordedRailVented.counts (chunk a j) (chunk b j) (bank.take 31) shape (some cin) even
    subst j
    simpa only [segment,if_true,ca,Nat.reduceSub] using c
  · have c := advance_counts (chunk a j) (chunk b j) (bank.take 31) shape
      (boundary even odd (j-1)) (boundary even odd j)
    simpa only [segment,if_neg hz,if_neg (show j≠7 by omega),ca] using c
private theorem finish_counts258 (a b bank : List Wire) (even : Wire)
    (aw : a.length=258) (bw : b.length=258) (kw : bank.length=32) :
    recordedToffoliCount (finish (a.drop 224) (b.drop 224) bank even)=33 ∧
    recordedMeasurementCount (finish (a.drop 224) (b.drop 224) bank even)=33 := by
  have ca := tail_length a aw
  have cb := tail_length b bw
  have aligned : RecordedRailRipple.Aligned (a.drop 224) (b.drop 224)
      (bank.take ((a.drop 224).length-2)) (List.replicate ((a.drop 224).length-2) none) := by
    simp [RecordedRailRipple.Aligned,ca,cb,kw]
  have c := RecordedRailRipple.aligned_counts _ _ _ _ aligned (some even)
  have bare := bare_counts even
  simp only [ca] at c
  simp only [finish,ca,recordedToffoliCount_append,recordedMeasurementCount_append,
    c.1,c.2,bare.1,bare.2,Nat.add_zero,Nat.reduceSub,Nat.reduceAdd]
  constructor <;> trivial
theorem forward_counts (a b bank : List Wire) (cin even odd : Wire)
    (aw : a.length=258) (bw : b.length=258) (kw : bank.length=32) :
    recordedToffoliCount (forward a b bank cin even odd)=257 ∧
    recordedMeasurementCount (forward a b bank cin even odd)=256 := by
  have h0 := segment_counts a b bank cin even odd aw bw kw 0 (by decide)
  have h1 := segment_counts a b bank cin even odd aw bw kw 1 (by decide)
  have h2 := segment_counts a b bank cin even odd aw bw kw 2 (by decide)
  have h3 := segment_counts a b bank cin even odd aw bw kw 3 (by decide)
  have h4 := segment_counts a b bank cin even odd aw bw kw 4 (by decide)
  have h5 := segment_counts a b bank cin even odd aw bw kw 5 (by decide)
  have h6 := segment_counts a b bank cin even odd aw bw kw 6 (by decide)
  have h7 := finish_counts258 a b bank even aw bw kw
  simp only [forward,recordedToffoliCount_append,recordedMeasurementCount_append,
    h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2]
  constructor <;> decide
theorem oldSlots_length (cursor : Nat) : (oldSlots cursor).length=256 := by simp [oldSlots]
theorem apply_counts (a b mirrorBank : List Wire) (cin : Wire) (cursor : Nat)
    (aw : a.length=258) (bw : b.length=258) (mw : mirrorBank.length=256) :
    recordedToffoliCount (applyProgram a b mirrorBank cin cursor)=257 ∧
    recordedMeasurementCount (applyProgram a b mirrorBank cin cursor)=256 := by
  have aligned : RecordedRailRipple.Aligned a b mirrorBank (oldSlots cursor) := by
    simp [RecordedRailRipple.Aligned,aw,bw,mw,oldSlots_length]
  have c := RecordedRailRipple.aligned_counts _ _ _ _ aligned (some cin)
  have e := embedRecorded_counts (notRegister b)
  have n := notRegister_counts b
  simp only [applyProgram,recordedToffoliCount_append,recordedMeasurementCount_append,
    e.1,e.2,n.1,n.2,Nat.zero_add,Nat.add_zero]
  simpa only [aw] using c
theorem pair_counts (a b bank mirrorBank : List Wire) (cin even odd : Wire) (cursor : Nat)
    (aw : a.length=258) (bw : b.length=258) (kw : bank.length=32) (mw : mirrorBank.length=256) :
    recordedToffoliCount (pair a b bank mirrorBank cin even odd cursor)=514 ∧
    recordedMeasurementCount (pair a b bank mirrorBank cin even odd cursor)=512 := by
  have f := forward_counts a b bank cin even odd aw bw kw
  have c := apply_counts a b mirrorBank cin cursor aw bw mw
  simp only [pair,recordedToffoliCount_append,recordedMeasurementCount_append,f.1,f.2,c.1,c.2]
  constructor <;> trivial
end ECDSAAdd.Arithmetic.RecordedRailApply258
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply258.forward_counts
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply258.pair_counts
