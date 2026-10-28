import ECDSAAdd.Arithmetic.RecordedRailDeferProgram

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailDefer

theorem chunk_length32 (r : List Wire) (width : r.length=256) (j : Nat) (hj : j<8) :
    (chunk r j).length=32 := by
  simp only [chunk,List.length_take,List.length_drop,width]
  omega

theorem finish_counts (a b bank : List Wire)
    (ha : a.length=32) (hb : b.length=32) (hbank : bank.length=31)
    (incoming : Wire) :
    recordedToffoliCount (finish a b bank incoming)=31 ∧
    recordedMeasurementCount (finish a b bank incoming)=31 := by
  have aligned : RecordedRailRipple.Aligned a b (bank.take (a.length-2))
      (List.replicate (a.length-2) none) := by
    simp [RecordedRailRipple.Aligned,ha,hb,hbank]
  have costs := RecordedRailRipple.aligned_counts a b _ _ aligned (some incoming)
  simp only [finish,recordedToffoliCount_append,recordedMeasurementCount_append]
  rw [costs.1,costs.2,(bare_counts incoming).1,(bare_counts incoming).2,ha]
  norm_num

theorem segment_counts (a b bank : List Wire) (cin even odd : Wire)
    (ha : a.length=256) (hb : b.length=256) (hbank : bank.length=31)
    (j : Nat) (hj : j<8) :
    recordedToffoliCount (segment a b bank cin even odd j)=(if j=7 then 31 else 32) ∧
    recordedMeasurementCount (segment a b bank cin even odd j)=(if j=0 ∨ j=7 then 31 else 32) := by
  have aw := chunk_length32 a ha j hj
  have bw := chunk_length32 b hb j hj
  have aligned : RecordedRailVented.Aligned (chunk a j) (chunk b j) bank := by
    simp [RecordedRailVented.Aligned,aw,bw,hbank]
  have shape := RecordedRailVented.aligned_shape _ _ _ aligned
  by_cases zero : j=0
  · subst j
    have costs := RecordedRailVented.counts _ _ _ shape (some cin) even
    simpa only [segment,if_pos,aw,show ¬((0:Nat)=7) from by decide,if_neg,
      true_or] using costs
  · by_cases last : j=7
    · subst j
      have costs := finish_counts _ _ bank aw bw hbank even
      simpa only [segment,show ¬((7:Nat)=0) from by decide,if_neg,if_pos,
        false_or] using costs
    · have costs := advance_counts _ _ bank shape
        (boundary even odd (j-1)) (boundary even odd j)
      simpa only [segment,zero,last,if_neg,aw,or_self] using costs

/-- Exact counts of the literal source order, including all seven released
boundary carries. These are not counts of a complete GCD or point stage. -/
theorem forward32_counts (a b bank : List Wire) (cin even odd : Wire)
    (ha : a.length=256) (hb : b.length=256) (hbank : bank.length=31) :
    recordedToffoliCount (forward32 a b bank cin even odd)=255 ∧
    recordedMeasurementCount (forward32 a b bank cin even odd)=254 := by
  have c0 := segment_counts a b bank cin even odd ha hb hbank 0 (by decide)
  have c1 := segment_counts a b bank cin even odd ha hb hbank 1 (by decide)
  have c2 := segment_counts a b bank cin even odd ha hb hbank 2 (by decide)
  have c3 := segment_counts a b bank cin even odd ha hb hbank 3 (by decide)
  have c4 := segment_counts a b bank cin even odd ha hb hbank 4 (by decide)
  have c5 := segment_counts a b bank cin even odd ha hb hbank 5 (by decide)
  have c6 := segment_counts a b bank cin even odd ha hb hbank 6 (by decide)
  have c7 := segment_counts a b bank cin even odd ha hb hbank 7 (by decide)
  simp only [forward32,recordedToffoliCount_append,recordedMeasurementCount_append,
    c0.1,c0.2,c1.1,c1.2,c2.1,c2.2,c3.1,c3.2,c4.1,c4.2,c5.1,c5.2,c6.1,c6.2,c7.1,c7.2]
  decide

/-- Every retained ordinal is an earlier consumed measurement when Apply
starts at the end of this forward program. -/
theorem ordinals_earlier : ∀j∈ordinals,j<254 := by decide
theorem positions_in_owned_mirror : ∀j∈positions,j<254 := by decide

end ECDSAAdd.Arithmetic.RecordedRailDefer
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.forward32_counts
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.ordinals_earlier
