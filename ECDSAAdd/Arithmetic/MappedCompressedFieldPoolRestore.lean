import ECDSAAdd.Arithmetic.MappedCompressedFieldSegmentSpec
import ECDSAAdd.Arithmetic.CompressedCompactRestore
import ECDSAAdd.Arithmetic.DirectSkywalkCleanup
import ECDSAAdd.Arithmetic.RunPoolBasisAgreement
import ECDSAAdd.Arithmetic.EncodedFieldPoolBasis
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode compressedEncodePrefix
  compressedCompactForward compressedCompactReverse fieldSegment skywalkArithmeticClear

private theorem encoder_pool_support (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) :
    wires (allGroupEncode base 170)⊆(skywalkPoolWires base).toFinset := by
  have history := compressedPrefix_history_support base (skywalkShared_integer_nodup base hn)
    hlo 512 (by decide)
  rw [encode_prefix_512] at history
  intro q hq
  have member := List.mem_toFinset.mp (history hq)
  simp only [List.mem_append,wireBlock] at member
  rcases member with member|member
  all_goals
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1] at hi ⊢
    exact ⟨i,by omega,rfl⟩

/-- Source zero and the full257-bit frame determine every integer-pool
bit even though the numerator, outside that pool, has already changed. -/
theorem encodedCanonical_pool_basis (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame origin X 0 s) :
    ∀q∈skywalkPoolWires base,s.basis q=
      (run (allGroupEncode base 170) [] ({phase:=false,basis:=origin} : State)).basis q := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have narrow : PairFrame (skywalkSharedField base).z (skywalkSharedField base).a
      origin X.val 0 raw.basis := by simpa only [ZMod.val_zero] using rawFrame
  have support := encoder_pool_support hn hlo
  exact encoded_field_pool_basis base hn (allGroupEncode base 170) support origin ha
    X.val raw s narrow encoded

/-- The actual complete field segment keeps its incoming encoded pool and
phase; neither conclusion assumes a global tape-phase oracle. -/
theorem fieldSegment_pool_frame (divide : Bool)
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
    (run (fieldSegment divide) m s).phase=s.phase ∧
      ∀q∈skywalkPoolWires base,(run (fieldSegment divide) m s).basis q=s.basis q := by
  have result := fieldSegment_spec divide hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy x hx0 hx trace Y s m input
  have before := encodedCanonical_pool_basis hn hlo origin ha Y s input
  have after := encodedCanonical_pool_basis hn hlo origin ha _ (run (fieldSegment divide) m s) result.2
  exact ⟨result.1,fun q hq => (after q hq).trans (before q hq).symm⟩

private theorem clear_pool_support :
    wires (skywalkArithmeticClear base)⊆(skywalkPoolWires base).toFinset := by
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires]
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact List.mem_toFinset.mpr (arith_mem base 0 1798 _ (by omega) (by omega))

/-- The second independently recorded clear restores the encoded terminal
pool after a proven pool-preserving field update. -/
theorem clear_after_pool_update (hn : (skywalkSharedWires base).Nodup)
    (recorded field : State) (mFirst mLast : List Bool)
    (phase : field.phase=(run (skywalkArithmeticClear base) mFirst recorded).phase)
    (pool : ∀q∈skywalkPoolWires base,
      field.basis q=(run (skywalkArithmeticClear base) mFirst recorded).basis q) :
    (run (skywalkArithmeticClear base) mLast field).phase=recorded.phase ∧
      ∀q∈skywalkPoolWires base,(run (skywalkArithmeticClear base) mLast field).basis q=recorded.basis q := by
  have agrees := pool_run_agrees (skywalkArithmeticClear base) (skywalkPoolWires base).toFinset
    clear_pool_support mLast field (run (skywalkArithmeticClear base) mFirst recorded)
    phase (fun q hq => pool q (List.mem_toFinset.mp hq))
  have twice : run (skywalkArithmeticClear base) mLast
      (run (skywalkArithmeticClear base) mFirst recorded)=recorded := by
    simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
      (base 511) (base 512) (base 770) (arith_clear_gates base hn) recorded mFirst mLast
  rw [twice] at agrees
  exact ⟨agrees.1,fun q hq => agrees.2 q (List.mem_toFinset.mpr hq)⟩

/-- Actual forward, clear, field, clear and compact reverse composition.
All original512 rounds and every independent record list are retained. -/
theorem fieldSegment_reverse_pool (divide : Bool)
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
    (Y : Fp) (initial : State) (mForward mFirst mField mLast mReverse : List Bool)
    (hin : SkywalkIntegerStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (input : EncodedCanonicalFrame origin Y 0
      (run (skywalkArithmeticClear base) mFirst (run (compressedCompactForward base 0 512) mForward initial))) :
    let recorded := run (compressedCompactForward base 0 512) mForward initial
    let prepared := run (skywalkArithmeticClear base) mFirst recorded
    let field := run (fieldSegment divide) mField prepared
    let restored := run (skywalkArithmeticClear base) mLast field
    (run (compressedCompactReverse base 0 512) mReverse restored).phase=initial.phase ∧
      (∀q∈skywalkPoolWires base,(run (compressedCompactReverse base 0 512) mReverse restored).basis q=initial.basis q) ∧
      (∀q,q∉skywalkPoolWires base →
        (run (compressedCompactReverse base 0 512) mReverse restored).basis q=restored.basis q) := by
  let recorded := run (compressedCompactForward base 0 512) mForward initial
  let prepared := run (skywalkArithmeticClear base) mFirst recorded
  let field := run (fieldSegment divide) mField prepared
  let restored := run (skywalkArithmeticClear base) mLast field
  have keeps := fieldSegment_pool_frame divide hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy ha x hx0 hx trace Y prepared mField input
  have recovered := clear_after_pool_update hn recorded field mFirst mLast keeps.1 keeps.2
  exact compressedCompactReverse_restore_after_outside base (skywalkShared_integer_nodup base hn)
    hlo x p (by norm_num [p]) hx0 (by norm_num [p]) (by norm_num [p]) hx
    (arith_coprime x hx0 hx) initial restored mForward mReverse hin recovered.1 recovered.2

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.encodedCanonical_pool_basis
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.fieldSegment_pool_frame
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.clear_after_pool_update
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.fieldSegment_reverse_pool
