import ECDSAAdd.Arithmetic.EntryForwardSelectedPoolRestore
import ECDSAAdd.Arithmetic.MappedFieldPhysical
import ECDSAAdd.Baselines.SlotField
import ECDSAAdd.Submission.Entrant.LaneConvert
import ECDSAAdd.Submission.Entrant.LaneForward

/-! Lane A field segment.  Both arithmetic segments keep a source word equal
to zero at one converter boundary, and the centered zero word is the
canonical zero word.  The corresponding converter (765 Toffoli each) is the
identity there and is omitted:
* multiplication: the exit `canonical(source)` after the inverse replay;
* division: the entry `center(source)` on the zero source word; at the exit the
  replay leaves the centered pair (Z,Z), so the copy clears the source in
  centered form and only the target is converted back;
* multiplication entry: the target is centered first and the centered word is
  copied into the zero source word, replacing `center(source)` by the copy.
The remaining target conversions use `BalancedConvert.LaneA` (threshold by one
literal comparison, 254 Toffoli cheaper each).  The division proof is a State
equality with the unchanged segment. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.MappedCompressed.LaneA
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport CompressedAllocation
attribute [local irreducible] run wires allGroupEncode BalancedConvert.center BalancedConvert.canonical
  PenultimateMapped.replay measurementCount

def origCanonTarget : Program := BalancedConvert.canonical (balancedSharedTargetConvert base)
def canonTarget : Program := BalancedConvert.LaneA.fastCanonical (balancedSharedTargetConvert base)
def canonSource : Program := BalancedConvert.canonical (balancedSharedSourceConvert base)

def origCentTarget : Program := BalancedConvert.center (balancedSharedTargetConvert base)
def centTarget : Program := BalancedConvert.LaneA.fastCenter (balancedSharedTargetConvert base)
def centSource : Program := BalancedConvert.center (balancedSharedSourceConvert base)

theorem cp_false_split : renameProgram allPlaced (converterPair false) = origCentTarget ++ centSource := by
  rw [converterPair_placement]
  simp only [converterPairAt, Bool.false_eq_true, if_false, origCentTarget, centSource]

theorem cp_true_split : renameProgram allPlaced (converterPair true) = origCanonTarget ++ canonSource := by
  rw [converterPair_placement]
  simp only [converterPairAt, if_true, origCanonTarget, canonSource]

theorem shared_nodup : (skywalkSharedWires base).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact List.nodup_range'

theorem target_slots : ∀ q ∈ (balancedSharedTargetConvert base).wires, q ∈ slots.toFinset := by
  intro q hq
  simp only [balancedSharedTargetConvert,BalancedConvert.Layout.wires,wireBlock,List.mem_append,
    List.mem_cons,List.mem_map,List.mem_range'_1,List.not_mem_nil,or_false,List.cons_append,
    List.nil_append] at hq
  rcases hq with h|h|h|h|h|h
  all_goals first
    | (subst h
       apply slot_mem
       · unfold live; omega
       · unfold omitted; omega)
    | (obtain ⟨i,hi,rfl⟩ := h
       apply slot_mem
       · unfold live; omega
       · unfold omitted; omega)

private def conversionIds : List Nat := [1797,1027,1796,2311,1025]++
  List.range' 2056 255++List.range' 770 255++List.range' 1540 255

private theorem target_declared :
    (balancedSharedTargetConvert base).wires.toFinset ⊆ (conversionIds.map base).toFinset := by
  intro q hq
  simp only [balancedSharedTargetConvert,BalancedConvert.Layout.wires,conversionIds,wireBlock,
    List.map_append,List.map_cons,List.map_nil,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at hq ⊢
  tauto

theorem encoder_target_layout_disjoint (P : Program)
    (hP : wires P ⊆ (balancedSharedTargetConvert base).wires.toFinset) :
    Disjoint (wires (allGroupEncode base 170)) (wires P) := by
  have hist := compressedPrefix_history_support base base_pool_nodup base_above 512 (by decide)
  rw [encode_prefix_512] at hist
  apply Finset.disjoint_left.mpr
  intro q hq hc
  have history := List.mem_toFinset.mp (hist hq)
  have converted := List.mem_toFinset.mp (target_declared (hP hc))
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp converted
  simp only [List.mem_append,wireBlock] at history
  rcases history with history|history
  all_goals
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp history
    have same := base_injective eq
    subst i
    simp only [List.mem_range'_1] at hi
    simp only [conversionIds,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
    omega

theorem centerWord_zero : centerWord (0:Fp) = 0 := by
  have h := BalancedField.constants.1
  unfold centerWord encodeWord centerFp
  rw [ZMod.val_zero]
  simp only [Nat.cast_zero, if_pos h.le]
  rfl

private theorem port_split (sign : Wire) :
    (skywalkSharedField base).z=(balancedSharedPorts base sign).r++[base 2312] ∧
    (skywalkSharedField base).a=(balancedSharedPorts base sign).y++[base 1026] := by
  rw [skywalkShared_field_z,balancedSharedPorts_r,balancedSharedPorts_y]
  constructor
  · have split := wireBlock_append base 2056 256 1
    simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using split.symm
  · have split := wireBlock_append base 770 256 1
    simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using split.symm

private theorem xor_neutral (a b : Bool) (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem encoder_target_disjoint :
    Disjoint (wires (allGroupEncode base 170)) (wires canonTarget) :=
  encoder_target_layout_disjoint _ (BalancedConvert.LaneA.fast_support _).2

private theorem transport (P : Program) (dis : Disjoint (wires (allGroupEncode base 170)) (wires P))
    (s raw : State) (m : List Bool)
    (encoded : s=run (allGroupEncode base 170) [] raw)
    (phase : (run P m raw).phase=raw.phase) :
    (run P m s).phase=s.phase ∧
    run P m s=run (allGroupEncode base 170) [] (run P m raw) := by
  have read : ∀q∈wires P,s.basis q=raw.basis q := by
    intro q hq
    rw [encoded]
    exact run_preserves_outside _ [] raw q (fun he => Finset.disjoint_left.mp dis he hq)
  have increment := (run_local_increment P s raw m read).1
  rw [phase,Bool.xor_self] at increment
  refine ⟨xor_neutral _ _ increment,?_⟩
  rw [encoded]
  exact (run_disjoint_commute _ _ dis [] m raw).symm

/-- Target-only exit conversion when the source word is the zero word. -/
theorem encoded_canonical_target (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X 0 s) :
    (run canonTarget m s).phase=s.phase ∧
    EncodedCanonicalFrame origin X 0 (run canonTarget m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have dis := (List.nodup_append'.mp (balancedSharedLayout_pairND base (base 2409) hn)).2.2
  have tw := balancedSharedTargetConvert_word base (base 2409)
  have away := (balancedSharedBoundary base (base 2409) hn).targetWorkAway
  rw [centerWord_zero] at frame
  have workClean : ∀q∈BalancedConvert.work (balancedSharedTargetConvert base),raw.basis q=false :=
    fun q hq => (frame.2.2 q (away q hq).1 (away q hq).2).trans (clean.1 q hq)
  have v := BalancedConvert.LaneA.fastCanonical_correct (balancedSharedTargetConvert base)
    (balancedSharedTargetConvert_widths base) (balancedSharedTargetConvert_nodup base hn) X raw m
    (by simpa only [tw] using frame.1) workClean
  have result : PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin X.val 0 (run canonTarget m raw).basis :=
    PairFrame.update_temp _ _ origin raw.basis _ _ 0 X.val dis frame
      (by simpa only [tw] using v.2.2.2) (by simpa only [tw] using v.2.1)
  have outside := balancedSharedDivision_high_outside base hn
  have wide := balancedPair_widen _ _ (base 2312) (base 1026) origin _ X.val 0 result
    (by simpa only [balancedSharedPorts_r,balancedSharedPorts_y] using outside.1)
    (by simpa only [balancedSharedPorts_r,balancedSharedPorts_y] using outside.2) hr hy
  have split := port_split (base 2409)
  rw [←split.1,←split.2] at wide
  have actual := transport canonTarget encoder_target_disjoint s raw m encoded v.1
  refine ⟨actual.1,run canonTarget m raw,v.1.trans (phase.trans actual.1.symm),
    by simpa only [ZMod.val_zero] using wide,actual.2⟩

private theorem value_bound (X : Fp) : X.val < 2^256 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact (ZMod.val_lt X).trans (by norm_num [p])

theorem encoder_center_disjoint :
    Disjoint (wires (allGroupEncode base 170)) (wires centTarget) ∧
    Disjoint (wires (allGroupEncode base 170)) (wires centSource) ∧
    Disjoint (wires (allGroupEncode base 170)) (wires origCentTarget) := by
  have d := encoder_conversion_disjoint false
  simp only [converterPairAt, Bool.false_eq_true, if_false, wires_append] at d
  exact ⟨encoder_target_layout_disjoint _ (BalancedConvert.LaneA.fast_support _).1,
    Finset.disjoint_of_subset_right Finset.subset_union_right d,
    Finset.disjoint_of_subset_right Finset.subset_union_left d⟩

/-- Target-only entry conversion when the source word is the zero word. -/
theorem encoded_center_target (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X 0 s) :
    (run centTarget m s).phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin X 0 (run centTarget m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have dis := (List.nodup_append'.mp (balancedSharedLayout_pairND base (base 2409) hn)).2.2
  have tw := balancedSharedTargetConvert_word base (base 2409)
  have away := (balancedSharedBoundary base (base 2409) hn).targetWorkAway
  have split := port_split (base 2409)
  rw [split.1,split.2] at frame
  have narrow := balancedPair_narrow _ _ (base 2312) (base 1026) origin raw.basis
    X.val (0:Fp).val (by simpa only [balancedSharedPorts_r,wireBlock_length] using value_bound X)
    (by simpa only [balancedSharedPorts_y,wireBlock_length] using value_bound 0) frame hr hy
  have workClean : ∀q∈BalancedConvert.work (balancedSharedTargetConvert base),raw.basis q=false :=
    fun q hq => (narrow.2.2 q (away q hq).1 (away q hq).2).trans (clean.1 q hq)
  have v := BalancedConvert.LaneA.fastCenter_correct (balancedSharedTargetConvert base)
    (balancedSharedTargetConvert_widths base) (balancedSharedTargetConvert_nodup base hn) X raw m
    (by simpa only [tw] using narrow.1) workClean
  have result : PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord 0) (run centTarget m raw).basis := by
    rw [centerWord_zero]
    have z : PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
        origin X.val 0 raw.basis := by simpa only [ZMod.val_zero] using narrow
    exact PairFrame.update_temp _ _ origin raw.basis _ _ 0 (centerWord X) dis z
      (by simpa only [tw] using v.2.2.2) (by simpa only [tw] using v.2.1)
  have actual := transport centTarget encoder_center_disjoint.1 s raw m encoded v.1
  exact ⟨actual.1,run centTarget m raw,v.1.trans (phase.trans actual.1.symm),result,actual.2⟩

/-- The original and the Lane A target entry conversions agree as State maps. -/
theorem encoded_center_state_eq (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (r r' : List Bool) (input : EncodedCanonicalFrame origin X 0 s) :
    run origCentTarget r s=run centTarget r' s := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have tw := balancedSharedTargetConvert_word base (base 2409)
  have away := (balancedSharedBoundary base (base 2409) hn).targetWorkAway
  have split := port_split (base 2409)
  rw [split.1,split.2] at frame
  have narrow := balancedPair_narrow _ _ (base 2312) (base 1026) origin raw.basis
    X.val (0:Fp).val (by simpa only [balancedSharedPorts_r,wireBlock_length] using value_bound X)
    (by simpa only [balancedSharedPorts_y,wireBlock_length] using value_bound 0) frame hr hy
  have workClean : ∀q∈BalancedConvert.work (balancedSharedTargetConvert base),raw.basis q=false :=
    fun q hq => (narrow.2.2 q (away q hq).1 (away q hq).2).trans (clean.1 q hq)
  have hx : regValue (balancedSharedTargetConvert base).word raw.basis=X.val := by
    simpa only [tw] using narrow.1
  have nd := balancedSharedTargetConvert_nodup base hn
  have wd := balancedSharedTargetConvert_widths base
  have vo := BalancedConvert.center_correct _ wd nd X raw r hx workClean
  have vf := BalancedConvert.LaneA.fastCenter_correct _ wd nd X raw r' hx workClean
  have rawEq := BalancedConvert.LaneA.fastCenter_state_eq _ wd nd X raw r' r hx workClean
  have tro := transport origCentTarget encoder_center_disjoint.2.2 s raw r encoded vo.1
  have tf := transport centTarget encoder_center_disjoint.1 s raw r' encoded vf.1
  rw [tro.2,tf.2]
  exact congrArg (run (allGroupEncode base 170) []) rawEq.symm

private theorem state_eq (a b : State) (hp : a.phase=b.phase) (hb : a.basis=b.basis) : a=b := by
  cases a; cases b; simp_all

/-- On a zero source word the source entry conversion is the identity State map. -/
theorem centSource_noop (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (X : Fp) (u : State) (n : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X 0 u) :
    run centSource n u=u := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have sw := balancedSharedSourceConvert_word base (base 2409)
  have away := (balancedSharedBoundary base (base 2409) hn).sourceWorkAway
  rw [centerWord_zero] at frame
  have workClean : ∀q∈BalancedConvert.work (balancedSharedSourceConvert base),raw.basis q=false :=
    fun q hq => (frame.2.2 q (away q hq).1 (away q hq).2).trans (clean.2 q hq)
  have word0 : regValue (balancedSharedSourceConvert base).word raw.basis=0 := by
    simpa only [sw] using frame.2.1
  have v := BalancedConvert.center_correct (balancedSharedSourceConvert base)
    (balancedSharedSourceConvert_widths base) (balancedSharedSourceConvert_nodup base hn) 0 raw n
    (by rw [word0,ZMod.val_zero]) workClean
  rw [centerWord_zero] at v
  have same : run centSource n raw=raw := by
    apply state_eq _ _ v.1
    funext q
    by_cases hq : q∈(balancedSharedSourceConvert base).word
    · exact ((regValue_zero _ _).mp v.2.1 q hq).trans ((regValue_zero _ _).mp word0 q hq).symm
    · exact v.2.2.2 q hq
  have actual := transport centSource encoder_center_disjoint.2.1 u raw n encoded v.1
  rw [actual.2,same,←encoded]

/-- Division segment: the source entry conversion is dropped. -/
def divSeg : Program :=
  centTarget ++ (PenultimateMapped.replay true ++ renameProgram allPlaced (copyPairAt id) ++
    canonTarget)

theorem old_div_split : PenultimateMapped.fieldSegment true =
    (origCentTarget ++ centSource) ++ (PenultimateMapped.replay true ++
      renameProgram allPlaced (converterPair true) ++ renameProgram allPlaced (copyPairAt id)) := by
  simp only [PenultimateMapped.fieldSegment,copyPairAt,if_true,List.nil_append,
    cp_false_split,List.append_assoc]

/-- Copying a centered target word into the zero source word yields the
centered pair (X,X); both high sites stay zero. -/
theorem encoded_copy_centered (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (u : State) (n : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X 0 u) :
    (run (copyPairAt base) n u).phase=u.phase ∧
    EncodedFieldFrame base (base 2409) origin X X (run (copyPairAt base) n u) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  rw [centerWord_zero] at frame
  have outside := balancedSharedDivision_high_outside base hn
  have wide := balancedPair_widen _ _ (base 2312) (base 1026) origin raw.basis (centerWord X) 0 frame
    (by simpa only [balancedSharedPorts_r,balancedSharedPorts_y] using outside.1)
    (by simpa only [balancedSharedPorts_r,balancedSharedPorts_y] using outside.2) hr hy
  have split := port_split (base 2409)
  rw [←split.1,←split.2] at wide
  have result := copyPair_frame hn origin (centerWord X) 0 raw n wide
  rw [Nat.zero_xor,split.1,split.2] at result
  have bound := (centerWord_valid X).1
  have narrow := balancedPair_narrow _ _ (base 2312) (base 1026) origin _
    (centerWord X) (centerWord X) (by simpa only [balancedSharedPorts_r,wireBlock_length] using bound)
    (by simpa only [balancedSharedPorts_y,wireBlock_length] using bound) result.2 hr hy
  have actual := transport (copyPairAt base) encoder_copy_disjoint u raw n encoded result.1
  exact ⟨actual.1,run (copyPairAt base) n raw,result.1.trans (phase.trans actual.1.symm),narrow,actual.2⟩

/-- XOR of the equal centered target word clears the source word. -/
theorem encoded_copy_clear_centered (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (u : State) (n : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X X u) :
    (run (copyPairAt base) n u).phase=u.phase ∧
    EncodedFieldFrame base (base 2409) origin X 0 (run (copyPairAt base) n u) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have outside := balancedSharedDivision_high_outside base hn
  have wide := balancedPair_widen _ _ (base 2312) (base 1026) origin raw.basis (centerWord X) (centerWord X) frame
    (by simpa only [balancedSharedPorts_r,balancedSharedPorts_y] using outside.1)
    (by simpa only [balancedSharedPorts_r,balancedSharedPorts_y] using outside.2) hr hy
  have split := port_split (base 2409)
  rw [←split.1,←split.2] at wide
  have result := copyPair_frame hn origin (centerWord X) (centerWord X) raw n wide
  rw [Nat.xor_self,split.1,split.2] at result
  have bound := (centerWord_valid X).1
  have narrow := balancedPair_narrow _ _ (base 2312) (base 1026) origin _
    (centerWord X) 0 (by simpa only [balancedSharedPorts_r,wireBlock_length] using bound)
    (by simp only [balancedSharedPorts_y,wireBlock_length]; positivity) result.2 hr hy
  have actual := transport (copyPairAt base) encoder_copy_disjoint u raw n encoded result.1
  refine ⟨actual.1,run (copyPairAt base) n raw,result.1.trans (phase.trans actual.1.symm),?_,actual.2⟩
  rw [centerWord_zero]
  exact narrow

theorem divSeg_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run divSeg m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out := by
  let Z := fieldResult true origin x Y
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedCanonicalFrame origin Z 0 out
  have all := run_three_states (centTarget ++ PenultimateMapped.replay true)
    (renameProgram allPlaced (copyPairAt id)) canonTarget P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      rw [run_append] at h1
      have a := encoded_center_target hn origin hw hu hr hy Y initial
        (m1.take (measurementCount centTarget)) hin
      have b := PenultimateMapped.LaneA.replay_forward_spec hn hlo ho hp hf origin hg0 hs0 env legal
        x hx0 hx trace Y _ (m1.drop (measurementCount centTarget)) a.2
      rw [h1] at b
      rw [copyPair_placement] at h2
      have c := encoded_copy_clear_centered hn origin hr hy Z s1 m2 b.2
      rw [h2] at c
      have d := encoded_canonical_target hn origin hw hu hr hy Z s2 m3 c.2
      rw [h3] at d
      exact ⟨d.1.trans (c.1.trans (b.1.trans a.1)),d.2⟩) s m input
  have join : divSeg = (centTarget ++ PenultimateMapped.replay true) ++
      (renameProgram allPlaced (copyPairAt id) ++ canonTarget) := by
    simp only [divSeg,List.append_assoc]
  rw [join]
  exact all

/-- Multiplication segment: center the target, copy, replay, convert the target. -/
def mulSeg : Program :=
  centTarget ++ renameProgram allPlaced (copyPairAt id) ++
    PenultimateMapped.replay false ++ canonTarget

def laneSegment (divide : Bool) : Program :=
  if divide then divSeg else mulSeg

private def inversePrefix : Program := centTarget ++ renameProgram allPlaced (copyPairAt id)

private theorem inversePrefix_spec
    (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    (run inversePrefix m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Y Y (run inversePrefix m s) := by
  let t := run centTarget (m.take (measurementCount centTarget)) s
  have first := encoded_center_target hn origin hw hu hr hy Y s (m.take (measurementCount centTarget)) input
  have second := encoded_copy_centered hn origin hr hy Y t
    (m.drop (measurementCount centTarget)) first.2
  simp only [inversePrefix,run_append,copyPair_placement]
  exact ⟨second.1.trans first.1,second.2⟩

theorem mulSeg_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run mulSeg m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult false origin x Y) 0 out := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedCanonicalFrame origin Z 0 out
  have all := run_three_states inversePrefix (PenultimateMapped.replay false) canonTarget P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have first := inversePrefix_spec hn origin hw hu hr hy Y initial m1 hin
      rw [h1] at first
      have middle := PenultimateMapped.replay_inverse_spec hn hlo ho hp hf origin hg0 hs0 env legal
        x Y hx0 hx trace s1 m2 first.2
      rw [h2] at middle
      have last := encoded_canonical_target hn origin hw hu hr hy Z s2 m3 middle.2
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m input
  have join : mulSeg = inversePrefix ++ (PenultimateMapped.replay false ++ canonTarget) := by
    simp only [mulSeg,inversePrefix,List.append_assoc]
  rw [join]
  simpa only [fieldResult,Bool.false_eq_true,if_false,Z] using all

theorem laneSegment_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (laneSegment divide) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out := by
  cases divide
  · simpa only [laneSegment, Bool.false_eq_true, if_false] using
      mulSeg_spec hn hlo ho hp hf origin hg0 hs0 env legal hw hu hr hy x hx0 hx trace Y s m input
  · simpa only [laneSegment, if_true] using
      divSeg_spec hn hlo ho hp hf origin hg0 hs0 env legal hw hu hr hy x hx0 hx trace Y s m input

theorem laneSegment_pool_frame (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    (run (laneSegment divide) m s).phase=s.phase ∧
      ∀q∈skywalkPoolWires base,(run (laneSegment divide) m s).basis q=s.basis q := by
  have result := laneSegment_spec divide hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy x hx0 hx trace Y s m input
  have before := encodedCanonical_pool_basis hn hlo origin ha Y s input
  have after := encodedCanonical_pool_basis hn hlo origin ha _ (run (laneSegment divide) m s) result.2
  exact ⟨result.1,fun q hq => (after q hq).trans (before q hq).symm⟩

/-! Resources, derived from the unchanged segment and the Lane A converter. -/

theorem old_split : PenultimateMapped.fieldSegment false =
    renameProgram allPlaced (copyPairAt id) ++ (origCentTarget ++ (centSource ++
      (PenultimateMapped.replay false ++ (origCanonTarget ++ canonSource)))) := by
  simp only [PenultimateMapped.fieldSegment,copyPairAt,Bool.false_eq_true,if_false,
    List.append_nil,cp_true_split,cp_false_split,List.append_assoc]

theorem laneSegment_support (divide : Bool) : wires (laneSegment divide) ⊆ slots.toFinset := by
  have old := selectedFieldSegment_support divide
  have sup := BalancedConvert.LaneA.fast_support (balancedSharedTargetConvert base)
  have fc : wires centTarget ⊆ slots.toFinset :=
    fun q hq => target_slots q (List.mem_toFinset.mp (sup.1 hq))
  have fk : wires canonTarget ⊆ slots.toFinset :=
    fun q hq => target_slots q (List.mem_toFinset.mp (sup.2 hq))
  cases divide
  · simp only [selectedFieldSegment] at old
    rw [old_split] at old
    simp only [wires_append,Finset.union_subset_iff] at old
    simp only [laneSegment,Bool.false_eq_true,if_false,mulSeg,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨fc,old.1⟩,old.2.2.2.1⟩,fk⟩
  · simp only [selectedFieldSegment] at old
    rw [old_div_split] at old
    simp only [wires_append,Finset.union_subset_iff] at old
    simp only [laneSegment,if_true,divSeg,wires_append,Finset.union_subset_iff]
    exact ⟨fc,⟨old.2.1.1,old.2.2⟩,fk⟩

theorem centSource_counts : toffoliCount centSource = 765 ∧ measurementCount centSource = 765 := by
  have c := BalancedConvert.counts (balancedSharedSourceConvert base) (balancedSharedSourceConvert_widths base)
  exact ⟨c.1,c.2.1⟩

theorem canonSource_counts : toffoliCount canonSource = 765 ∧ measurementCount canonSource = 765 := by
  have c := BalancedConvert.counts (balancedSharedSourceConvert base) (balancedSharedSourceConvert_widths base)
  exact ⟨c.2.2.1,c.2.2.2⟩

theorem laneSegment_counts (divide : Bool) :
    toffoliCount (laneSegment divide)=(if divide then 655006 else 655516) ∧
    measurementCount (laneSegment divide)=523934 := by
  have old := selectedFieldSegment_counts divide
  have src := canonSource_counts
  have csrc := centSource_counts
  have oc := BalancedConvert.counts (balancedSharedTargetConvert base) (balancedSharedTargetConvert_widths base)
  have fc := BalancedConvert.LaneA.fast_counts (balancedSharedTargetConvert base)
    (balancedSharedTargetConvert_widths base)
  have h1 : toffoliCount centTarget = 508 ∧ measurementCount centTarget = 507 := ⟨fc.1,fc.2.1⟩
  have h2 : toffoliCount canonTarget = 508 ∧ measurementCount canonTarget = 507 := ⟨fc.2.2.1,fc.2.2.2⟩
  have h3 : toffoliCount origCentTarget = 765 ∧ measurementCount origCentTarget = 765 := ⟨oc.1,oc.2.1⟩
  have h4 : toffoliCount origCanonTarget = 765 ∧ measurementCount origCanonTarget = 765 :=
    ⟨oc.2.2.1,oc.2.2.2⟩
  cases divide
  · simp only [selectedFieldSegment,old_split,toffoliCount_append,measurementCount_append,
      Bool.false_eq_true,if_false] at old
    simp only [laneSegment,Bool.false_eq_true,if_false,mulSeg,toffoliCount_append,
      measurementCount_append]
    omega
  · have ct := cp_true_split
    simp only [selectedFieldSegment,old_div_split,ct,toffoliCount_append,measurementCount_append,
      if_true] at old
    simp only [laneSegment,if_true,divSeg,toffoliCount_append,measurementCount_append]
    omega

theorem laneSegment_physical (divide : Bool) : GatePhysical (laneSegment divide) := by
  have old := selectedFieldSegment_physical divide
  have nd := balancedSharedTargetConvert_nodup base shared_nodup
  have fp := BalancedConvert.LaneA.fast_physical (balancedSharedTargetConvert base) nd
  have fc : GatePhysical centTarget := fp.1
  have fk : GatePhysical canonTarget := fp.2
  cases divide
  · rw [old_split] at old
    simp only [gatePhysical_append] at old
    simp only [laneSegment,Bool.false_eq_true,if_false,mulSeg,gatePhysical_append]
    exact ⟨⟨⟨fc,old.1⟩,old.2.2.2.1⟩,fk⟩
  · rw [old_div_split] at old
    simp only [gatePhysical_append] at old
    simp only [laneSegment,if_true,divSeg,gatePhysical_append]
    exact ⟨fc,⟨old.2.1.1,old.2.2⟩,fk⟩

open Challenge Baselines in
theorem laneSegment_gateSlots_le (divide : Bool) :
    gateSlots (laneSegment divide) ≤ 14100000 := by
  have g := mappedGroups_gateSlots_le divide 1 169
  have f := firstGroup_gateSlots_le divide
  have p := penultimateCell_gateSlots_le divide
  have b := converterPair_gateSlots_le true
  have hcopy : gateSlots (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) ≤ 257 := by
    rw [copyRegister_gateSlots]
    have hl : (skywalkSharedField id).z.length = 257 := by simp only [ModInPlaceLayout.z,ModAddCoreLayout.z,skywalkSharedField,List.length_append,List.length_singleton,wireBlock_length]
    rw [hl]; omega
  have replayEq (A B C : Program) (d : Bool) :
      gateSlots (if d then A++B++C else C++B++A) = gateSlots A+gateSlots B+gateSlots C := by
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte,gateSlots_append]
    omega
  have rep : gateSlots (PenultimateMapped.replay divide) ≤ 13941000 := by
    rw [PenultimateMapped.replay, replayEq,rename_gateSlots]
    omega
  have fs := BalancedConvert.LaneA.fast_gateSlots_le (balancedSharedTargetConvert base)
    (balancedSharedTargetConvert_widths base)
  have fc : gateSlots centTarget ≤ 12000 := fs.1
  have fk : gateSlots canonTarget ≤ 12000 := fs.2
  cases divide
  · simp only [laneSegment,Bool.false_eq_true,if_false,mulSeg,gateSlots_append,copyPairAt,
      rename_gateSlots]
    omega
  · simp only [laneSegment,if_true,divSeg,gateSlots_append,copyPairAt,rename_gateSlots]
    omega

end ECDSAAdd.Arithmetic.MappedCompressed.LaneA
