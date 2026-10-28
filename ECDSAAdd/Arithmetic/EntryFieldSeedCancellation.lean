import ECDSAAdd.Arithmetic.EndpointSwapTrimProof
import ECDSAAdd.Arithmetic.BorrowedSkywalkUnaryFrames
import ECDSAAdd.Arithmetic.MappedCompressedConversionNaturality
import ECDSAAdd.Arithmetic.BalancedSharedDivisionBridge

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryFieldSeedCancellation
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run dblInPlace halfInPlace OffsetBorrowedCanonical.cell
attribute [local irreducible] transcriptSelectWindow swapRegisters

private theorem fp_bound (X : Fp) : X.val<2^256 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact (ZMod.val_lt X).trans (by norm_num [p])
private theorem word_bound (X : Fp) : centerWord X<2^256 := encodeWord_bound _ _
private theorem halve_double (X : Fp) : (2*X)/2=X := by
  have h : (2 : Fp)≠0 := by decide
  exact mul_div_cancel_left₀ X h

def centers (w : Nat → Wire) : Program := MappedCompressed.converterPairAt w false
def canonicals (w : Nat → Wire) : Program := MappedCompressed.converterPairAt w true
def selectedSwap (w : Nat → Wire) (b swap sign effS : Wire) (is : Bool) : Program :=
  transcriptSelectWindow b swap effS is
    (swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y)
def oldEntry (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) : Program :=
  dblInPlace (borrowedSkywalkUnary w) p++centers w++
    OffsetBorrowedCanonical.cell w b g swap sign effS ig is
def newEntry (w : Nat → Wire) (b swap sign effS : Wire) (is : Bool) : Program :=
  centers w++selectedSwap w b swap sign effS is

private theorem wide_lift (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (base : BasisState) (br : base (w 2312)=false) (by0 : base (w 1026)=false)
    (I J O P : Nat) (hi : I<2^256) (hj : J<2^256) (code : Program)
    (proof : Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base I J) code
      (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base O P)) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base I J) code
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base O P) := by
  intro s m input
  rw [balancedSharedDivision_z,balancedSharedDivision_a] at input
  have narrow := balancedPair_narrow _ _ _ _ base s.basis I J
    (by simpa only [wireBlock_length] using hi) (by simpa only [wireBlock_length] using hj) input br by0
  have output := proof s m narrow
  have away := balancedSharedDivision_high_outside w hn
  have wide := balancedPair_widen _ _ _ _ base _ O P output.2 away.1 away.2 br by0
  rw [←balancedSharedDivision_z,←balancedSharedDivision_a] at wide
  exact ⟨output.1,wide⟩

private theorem boundary_frame (canonical : Bool) (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (base : BasisState)
    (hw : regValue (skywalkSharedField w).work base=0) (hu : regValue (skywalkSharedUnused w) base=0)
    (br : base (w 2312)=false) (by0 : base (w 1026)=false) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
      (if canonical then centerWord X else X.val) (if canonical then centerWord Y else Y.val))
      (MappedCompressed.converterPairAt w canonical)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (if canonical then X.val else centerWord X) (if canonical then Y.val else centerWord Y)) := by
  let L := balancedSharedPorts w sign
  let D := balancedSharedBoundary w sign hn
  have clean := balancedSharedBoundary_clean w sign base hw hu
  cases canonical
  · have frame := balancedTranscriptCenterPair_frame L D base clean.1 clean.2 X Y
    have low : Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base X.val Y.val)
        (MappedCompressed.converterPairAt w false)
        (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base (centerWord X) (centerWord Y)) := by
      simpa only [L,D,balancedSharedPorts_r,balancedSharedPorts_y,balancedTranscriptCenterPair,
        balancedSharedBoundary,MappedCompressed.converterPairAt,Bool.false_eq_true,if_false] using frame
    exact wide_lift w hn base br by0 _ _ _ _ (fp_bound X) (fp_bound Y) _ low
  · have frame := balancedTranscriptCanonicalPair_frame L D base clean.1 clean.2 X Y
    have low : Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base (centerWord X) (centerWord Y))
        (MappedCompressed.converterPairAt w true)
        (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base X.val Y.val) := by
      simpa only [L,D,balancedSharedPorts_r,balancedSharedPorts_y,balancedTranscriptCanonicalPair,
        balancedSharedBoundary,MappedCompressed.converterPairAt,if_true] using frame
    exact wide_lift w hn base br by0 _ _ _ _ (word_bound X) (word_bound Y) _ low

private theorem swap_pair (r y : List Wire) (flag : Wire) (len : r.length=y.length)
    (nd : (flag::r++y).Nodup) (base : BasisState) (X Y : Nat) :
    Triple (PairFrame r y base X Y) (swapRegisters flag r y)
      (PairFrame r y base (if base flag then Y else X) (if base flag then X else Y)) := by
  intro s m input
  have out := swapRegisters_correct flag r y len nd s m
  have away := (List.nodup_cons.mp nd).1
  have same := input.2.2 flag (fun h => away (List.mem_append_left _ h))
    (fun h => away (List.mem_append_right _ h))
  refine ⟨out.1,?_,?_,fun q qr qy => (out.2.1 q qr qy).trans (input.2.2 q qr qy)⟩
  · rw [out.2.2.1,same,input.1,input.2.1]
  · rw [out.2.2.2,same,input.1,input.2.1]

private theorem swap_window_frame (w : Nat → Wire) (b g swap sign effS : Wire) (is : Bool)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (base : BasisState) (hs0 : base effS=false) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base (centerWord X) (centerWord Y))
      (selectedSwap w b swap sign effS is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if mixedTranscriptBit base b swap is then Y else X))
        (centerWord (if mixedTranscriptBit base b swap is then X else Y))) := by
  have controls := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at controls
  have nd : [b,swap,effS].Nodup := by simp [List.nodup_cons]; tauto
  have width := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have body := swap_pair _ _ effS (width.2.1.trans width.2.2.1.symm) hl.swapND
    (mixedTranscriptBase base b swap effS is) (centerWord X) (centerWord Y)
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at body
  have body' : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      (mixedTranscriptBase base b swap effS is) (centerWord X) (centerWord Y))
      (swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        (mixedTranscriptBase base b swap effS is)
        (centerWord (if mixedTranscriptBit base b swap is then Y else X))
        (centerWord (if mixedTranscriptBit base b swap is then X else Y))) := by
    cases bit : mixedTranscriptBit base b swap is <;>
      simpa only [mixedTranscriptBase,writeBit,bit,if_true,if_false,Bool.false_eq_true] using body
  exact transcriptSelectWindow_pairFrame b swap effS is _ _ nd (hl.outside b (by simp))
    (hl.outside swap (by simp)) (hl.outside effS (by simp)) base hs0 _ _ _ _ _ body'

theorem entry_frames (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false) (hs0 : base effS=false)
    (hw : regValue (skywalkSharedField w).work base=0) (hu : regValue (skywalkSharedUnused w) base=0)
    (he : Env w base) (br : base (w 2312)=false) (by0 : base (w 1026)=false) (Y : Fp) :
    let post := PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
      (centerWord (if mixedTranscriptBit base b swap is then 0 else Y))
      (centerWord (if mixedTranscriptBit base b swap is then Y else 0))
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base Y.val 0)
      (oldEntry w b g swap sign effS ig is) post ∧
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base Y.val 0)
      (newEntry w b swap sign effS is) post := by
  have doubled := borrowedSkywalkUnary_double_frame w hn base hw hu Y 0
  have oldCenter := boundary_frame false w sign hn base hw hu br by0 (2*Y) 0
  have newCenter := boundary_frame false w sign hn base hw hu br by0 Y 0
  have cell := OffsetBorrowedCanonical.cell_frame w b g swap sign effS ig is hn hl ho hoS base hg0 hs0 he (2*Y) 0
  have lowCell : Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base (centerWord (2*Y)) (centerWord 0))
      (OffsetBorrowedCanonical.cell w b g swap sign effS ig is)
      (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base
        (centerWord (if mixedTranscriptBit base b swap is then 0 else Y))
        (centerWord (if mixedTranscriptBit base b swap is then Y else 0))) := by
    cases bit : mixedTranscriptBit base b swap is <;>
      simpa only [balancedSharedPorts_r,balancedSharedPorts_y,skywalkPayloadCell,neg_zero,ite_self,
        add_zero,halve_double,bit,if_false,if_true,Bool.false_eq_true] using cell
  have wideCell := wide_lift w hn base br by0 _ _ _ _ (word_bound (2*Y)) (word_bound 0) _ lowCell
  have sw := swap_window_frame w b g swap sign effS is hl base hs0 Y 0
  have lowSwap := sw
  rw [balancedSharedPorts_r,balancedSharedPorts_y] at lowSwap
  have wideSwap := wide_lift w hn base br by0 _ _ _ _ (word_bound Y) (word_bound 0) _ lowSwap
  constructor
  · simpa only [oldEntry,ZMod.val_zero] using (doubled.seq oldCenter).seq wideCell
  · simpa only [newEntry,centers,ZMod.val_zero] using newCenter.seq wideSwap

/-- The extension zeros are derived from the actual canonical words. No
even-Y premise or extra caller-base semantic condition is introduced. -/
theorem entry_state_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (Y : Fp) (s : State) (mOld mNew : List Bool)
    (hg0 : s.basis sign=false) (hs0 : s.basis effS=false)
    (hw : regValue (skywalkSharedField w).work s.basis=0) (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hR : regValue (skywalkSharedField w).z s.basis=Y.val)
    (hY : regValue (skywalkSharedField w).a s.basis=0) :
    run (oldEntry w b g swap sign effS ig is) mOld s=run (newEntry w b swap sign effS is) mNew s := by
  have r := hR
  have y := hY
  rw [balancedSharedDivision_z] at r
  rw [balancedSharedDivision_a] at y
  have br := (balancedCanonical_high_zero _ _ s.basis Y.val
    (by simpa only [wireBlock_length] using fp_bound Y) r).2
  have by0 := (balancedCanonical_high_zero _ _ s.basis 0 (by simp [wireBlock_length]) y).2
  have env := env_of_canonical_source w hn s.basis 0 (by simpa using hY) hw hu
  have frames := entry_frames w b g swap sign effS ig is hn hl ho hoS s.basis hg0 hs0 hw hu env br by0 Y
  exact PairFrame.program_eq _ _ s.basis _ _ _ _ _ _ frames.1 frames.2 s mOld mNew
    ⟨hR,hY,fun _ _ _ => rfl⟩

theorem counts (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (effS::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup) :
    toffoliCount (oldEntry w b g swap sign effS ig is)=3321 ∧
    measurementCount (oldEntry w b g swap sign effS ig is)=3066 ∧
    toffoliCount (newEntry w b swap sign effS is)=1787 ∧
    measurementCount (newEntry w b swap sign effS is)=1531 := by
  have unary := modUnary_counts (borrowedSkywalkUnary w) 256 p (borrowedSkywalkUnary_widths w) (by omega)
  have target := BalancedConvert.counts (balancedSharedTargetConvert w) (balancedSharedTargetConvert_widths w)
  have source := BalancedConvert.counts (balancedSharedSourceConvert w) (balancedSharedSourceConvert_widths w)
  have cell := OffsetBorrowedCanonical.cell_counts w b g swap sign effS ig is hn
  have width := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have sw := swapRegisters_resources effS _ _ (width.2.1.trans width.2.2.1.symm) hn
  have selection := transcriptSelectWindow_counts b swap effS is
    (swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y)
  simp only [oldEntry,newEntry,centers,MappedCompressed.converterPairAt,Bool.false_eq_true,if_false,
    selectedSwap,toffoliCount_append,measurementCount_append,unary.1,unary.2.1,
    target.1,target.2.1,source.1,source.2.1,cell.1,cell.2,selection.1,selection.2,
    sw.1,sw.2.1,width.2.1]
  norm_num

end ECDSAAdd.Arithmetic.EntryFieldSeedCancellation
#print axioms ECDSAAdd.Arithmetic.EntryFieldSeedCancellation.entry_frames
#print axioms ECDSAAdd.Arithmetic.EntryFieldSeedCancellation.entry_state_eq
#print axioms ECDSAAdd.Arithmetic.EntryFieldSeedCancellation.counts
