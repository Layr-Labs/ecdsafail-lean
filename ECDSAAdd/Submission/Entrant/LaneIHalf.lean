import ECDSAAdd.Submission.Entrant.LaneIReplay
import ECDSAAdd.Submission.Entrant.HalfLane

/-! Halving-endpoint field segment with every field cell using the 256-wide
fold.  `segmentI` is state-equal to `HalfField.segment` on its domain. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic Secp256k1 BalancedField MappedCompressed CompressedAllocation
  CompressedFieldSupport HalfField
attribute [local irreducible] run allGroupEncode

def segmentI (divide : Bool) : Program :=
  if divide then centerT++(replayI true++(copyN++canonT))
  else centerT++(copyN++(replayI false++canonT))

theorem segmentI_sub (divide : Bool) : InstrSub (segmentI divide) (HalfField.segment divide) := by
  cases divide <;> simp only [segmentI,HalfField.segment,Bool.false_eq_true,if_false,if_true]
  · exact (InstrSub.refl _).append ((InstrSub.refl _).append ((replayI_sub false).append (InstrSub.refl _)))
  · exact (InstrSub.refl _).append ((replayI_sub true).append ((InstrSub.refl _).append (InstrSub.refl _)))

theorem segmentI_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    run (segmentI divide) m s=run (HalfField.segment divide) m s := by
  let E : Fp → Fp → State → Prop := fun X Y t => EncodedFieldFrame base (base 2409) origin X Y t
  cases divide
  · simp only [segmentI,HalfField.segment,Bool.false_eq_true,if_false]
    apply seq_eq_frame _ _ _ _ (E (Y/2) 0) s m rfl (fun _ => rfl)
      (fun r => (center_frame hn origin hw hu hr hy Y s r input).2)
    intro s1 m1 c1
    apply seq_eq_frame _ _ _ _ (E (Y/2) (Y/2)) s1 m1 rfl (fun _ => rfl)
      (fun r => (copy_fill hn origin (Y/2) s1 r c1).2)
    intro s2 m2 c2
    exact seq_eq _ _ _ _ s2 m2 (replayI_counts false).1
      (replayI_eq false hn hlo ho hp hf origin hg0 hs0 env legal (Y/2) s2 _ (by simpa using c2)) rfl
  · simp only [segmentI,HalfField.segment,if_true]
    apply seq_eq_frame _ _ _ _ (E (Y/2) 0) s m rfl (fun _ => rfl)
      (fun r => (center_frame hn origin hw hu hr hy Y s r input).2)
    intro s1 m1 c1
    exact seq_eq _ _ _ _ s1 m1 (replayI_counts true).1
      (replayI_eq true hn hlo ho hp hf origin hg0 hs0 env legal (Y/2) s1 _ (by simpa using c1)) rfl

theorem segmentI_support (divide : Bool) : wires (segmentI divide) ⊆ slots.toFinset :=
  (segmentI_sub divide).wires_sub.trans (HalfField.segment_support divide)

theorem segmentI_physical (divide : Bool) : GatePhysical (segmentI divide) :=
  (segmentI_sub divide).physical (HalfField.segment_physical divide)

theorem segmentI_avoid (divide : Bool) : Avoid (segmentI divide) :=
  avoid_sub (segmentI_sub divide).wires_sub (HalfLane.segment_avoid divide)

theorem segmentI_gateSlots_le (divide : Bool) :
    Challenge.gateSlots (segmentI divide) ≤ 14100000 :=
  (segmentI_sub divide).slots.trans (HalfLane.segment_gateSlots_le divide)

theorem segmentI_counts (divide : Bool) :
    toffoliCount (segmentI divide)=(if divide then 653990 else 654500) ∧
    measurementCount (segmentI divide)=523430 := by
  have c := replayI_counts divide
  have o := HalfField.segment_counts divide
  cases divide <;> simp only [segmentI,HalfField.segment,Bool.false_eq_true,if_false,if_true,
    measurementCount_append,toffoliCount_append] at o ⊢ <;> constructor <;> omega

end ECDSAAdd.Entrant.LaneI
