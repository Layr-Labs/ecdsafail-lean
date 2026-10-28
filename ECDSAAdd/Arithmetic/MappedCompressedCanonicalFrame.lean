import ECDSAAdd.Arithmetic.MappedCompressedConversionEncoding
import ECDSAAdd.Arithmetic.CompressedFieldEncodedZeros
import ECDSAAdd.Arithmetic.BalancedSharedDivisionBridge
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport CompressedAllocation
attribute [local irreducible] run wires allGroupEncode compressedHistoryEncode
  BalancedConvert.center BalancedConvert.canonical

/-- Actual257-bit public field ports under the fixed full history encoding. -/
def EncodedCanonicalFrame (origin : BasisState) (X Y : Fp) (s : State) : Prop :=
  ∃ raw : State,raw.phase=s.phase ∧
    PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X.val Y.val raw.basis ∧
    s=run (allGroupEncode base 170) [] raw

theorem canonical_pair_work_zero (hn : (skywalkSharedWires base).Nodup)
    (origin current : BasisState) (X Y : Nat)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (frame : PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X Y current) :
    regValue (skywalkSharedField base).work current=0 := by
  have full := skywalkShared_field_nodup base hn
  change ((skywalkSharedField base).a++(skywalkSharedField base).z++
    (skywalkSharedField base).work).Nodup at full
  have dis := (List.nodup_append'.mp full).2.2
  apply (regValue_zero _ _).mpr
  intro q hq
  have az : q∉(skywalkSharedField base).a ∧ q∉(skywalkSharedField base).z := by
    constructor
    · intro h; exact List.disjoint_left.mp dis (List.mem_append_left _ h) hq
    · intro h; exact List.disjoint_left.mp dis (List.mem_append_right _ h) hq
  exact (frame.2.2 q az.2 az.1).trans ((regValue_zero _ _).mp hw q hq)

theorem encoded_canonical_work_zero (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (X Y : Fp) (s : State) (frame : EncodedCanonicalFrame origin X Y s)
    (j : Nat) (hj : j < 170) : s.basis (base (W j))=false := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have rawWork := canonical_pair_work_zero hn origin raw.basis _ _ hw rawFrame
  have zero := OffsetCleanupBorrowedCaller.maskBit_zero base raw.basis rawWork (W j)
    (by unfold W; omega) (by unfold W; omega)
  have pool := skywalkShared_integer_nodup base hn
  have hist := compressedPrefix_history_support base pool hlo 512 (by decide)
  rw [encode_prefix_512] at hist
  have away : base (W j)∉wires (allGroupEncode base 170) := by
    intro used
    have mem := List.mem_toFinset.mp (hist used)
    rcases List.mem_append.mp mem with mem|mem
    all_goals
      obtain ⟨k,hk,eq⟩ := List.mem_map.mp mem
      simp only [List.mem_range'_1] at hk
      have same := skywalkPool_index_inj base pool k (W j) (by omega) (by unfold W; omega) eq
      unfold W at same
      omega
  rw [encoded]
  exact (run_preserves_outside (allGroupEncode base 170) [] raw _ away).trans zero

/-- Allocation work and codec holes are derived from the full canonical
frame and existing caller cleanliness, without an additional zero bank. -/
theorem encoded_canonical_zero_region (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (_hu : regValue (skywalkSharedUnused base) origin=0)
    (X Y : Fp) (s : State) (frame : EncodedCanonicalFrame origin X Y s) :
    ∀q,zeroRegion q → s.basis (base q)=false := by
  intro q hq
  rcases hq with work|hole
  · have index : q=W (q-515) := by unfold workRegion W at *; omega
    have bound : q-515 < 170 := by unfold workRegion at work; omega
    rw [index]
    exact encoded_canonical_work_zero hn hlo origin hw X Y s frame _ bound
  · have index : q=H ((q-1029)/3) := by unfold holeRegion H at *; omega
    have bound : (q-1029)/3 < 170 := by unfold holeRegion at hole; omega
    obtain ⟨raw,_,_,encoded⟩ := frame
    rw [encoded,index]
    exact allGroupEncode_holes_zero base (skywalkShared_integer_nodup base hn) hlo
      170 (by decide) raw [] _ bound

private theorem port_split (sign : Wire) :
    (skywalkSharedField base).z=(balancedSharedPorts base sign).r++[base 2312] ∧
    (skywalkSharedField base).a=(balancedSharedPorts base sign).y++[base 1026] := by
  rw [skywalkShared_field_z,balancedSharedPorts_r,balancedSharedPorts_y]
  constructor
  · have split := wireBlock_append base 2056 256 1
    simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using split.symm
  · have split := wireBlock_append base 770 256 1
    simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using split.symm

private theorem value_bound (X : Fp) : X.val < 2^256 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact (ZMod.val_lt X).trans (by norm_num [p])

private theorem xor_neutral (a b : Bool) (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

private theorem conversion_transport (canonical : Bool) (s raw : State) (m : List Bool)
    (encoded : s=run (allGroupEncode base 170) [] raw)
    (phase : (run (converterPairAt base canonical) m raw).phase=raw.phase) :
    (run (converterPairAt base canonical) m s).phase=s.phase ∧
    run (converterPairAt base canonical) m s=
      run (allGroupEncode base 170) [] (run (converterPairAt base canonical) m raw) := by
  have dis := encoder_conversion_disjoint canonical
  have read : ∀q∈wires (converterPairAt base canonical),s.basis q=raw.basis q := by
    intro q hq
    rw [encoded]
    exact run_preserves_outside _ [] raw q (fun he => Finset.disjoint_left.mp dis he hq)
  have increment := (run_local_increment (converterPairAt base canonical) s raw m read).1
  rw [phase,Bool.xor_self] at increment
  refine ⟨xor_neutral _ _ increment,?_⟩
  rw [encoded]
  exact encoder_conversion_commute canonical raw [] m

/-- Actual converter entry, retaining the same caller origin. Its high-zero
facts come from canonical origin ports, not from a low-word assertion. -/
theorem encoded_center_pair (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    (run (converterPairAt base false) m s).phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin X Y (run (converterPairAt base false) m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  let L := balancedSharedPorts base (base 2409)
  let D := balancedSharedBoundary base (base 2409) hn
  have split := port_split (base 2409)
  rw [split.1,split.2] at frame
  have narrow := balancedPair_narrow L.r L.y (base 2312) (base 1026) origin raw.basis
    X.val Y.val (by simpa only [L,balancedSharedPorts_r,wireBlock_length] using value_bound X)
    (by simpa only [L,balancedSharedPorts_y,wireBlock_length] using value_bound Y) frame hr hy
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have result := balancedTranscriptCenterPair_frame L D origin clean.1 clean.2 X Y raw m narrow
  change (run (converterPairAt base false) m raw).phase=raw.phase ∧ _ at result
  have actual := conversion_transport false s raw m encoded result.1
  refine ⟨actual.1,run (converterPairAt base false) m raw,
    result.1.trans (phase.trans actual.1.symm),result.2,actual.2⟩

/-- Actual converter exit widens back to both original257-bit ports. -/
theorem encoded_canonical_pair (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X Y : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    (run (converterPairAt base true) m s).phase=s.phase ∧
    EncodedCanonicalFrame origin X Y (run (converterPairAt base true) m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  let L := balancedSharedPorts base (base 2409)
  let D := balancedSharedBoundary base (base 2409) hn
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have result := balancedTranscriptCanonicalPair_frame L D origin clean.1 clean.2 X Y raw m frame
  change (run (converterPairAt base true) m raw).phase=raw.phase ∧ _ at result
  have outside := balancedSharedDivision_high_outside base hn
  have wide := balancedPair_widen L.r L.y (base 2312) (base 1026) origin _ X.val Y.val
    result.2 (by simpa only [L,balancedSharedPorts_r,balancedSharedPorts_y] using outside.1)
    (by simpa only [L,balancedSharedPorts_r,balancedSharedPorts_y] using outside.2) hr hy
  have split := port_split (base 2409)
  rw [←split.1,←split.2] at wide
  have actual := conversion_transport true s raw m encoded result.1
  refine ⟨actual.1,run (converterPairAt base true) m raw,
    result.1.trans (phase.trans actual.1.symm),wide,actual.2⟩

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.encoded_canonical_zero_region
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.encoded_center_pair
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.encoded_canonical_pair
