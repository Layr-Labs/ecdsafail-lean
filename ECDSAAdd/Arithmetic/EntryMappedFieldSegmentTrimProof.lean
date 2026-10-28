import ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
import ECDSAAdd.Arithmetic.MappedCompressedEncodedEndpoints
import ECDSAAdd.Arithmetic.MappedCompressedGroupsFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run logicalCell compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] allGroupEncode

/-- Full logical reference of the actual first packet. Its remaining two
cells and both codecs are exactly the old emitted instructions. -/
def baseFirstGroup (divide : Bool) : Program :=
  compressedHistoryDecode base 0 ++
  (if divide then renameProgram base logicalZero ++
      renameProgram base (logicalCell divide 1) ++ renameProgram base (logicalCell divide 2)
   else renameProgram base (logicalCell divide 2) ++
      renameProgram base (logicalCell divide 1) ++ renameProgram base logicalZero) ++
  compressedHistoryEncode base 0

theorem firstGroup_eq_rename (divide : Bool) :
    firstGroup divide=renameProgram (shifted (pi 0)) (baseFirstGroup divide) := by
  have codec := shifted_current_codec 0 (by decide)
  have append (f : Wire → Wire) (p q : Program) :
      renameProgram f (p++q)=renameProgram f p++renameProgram f q := by
    simp only [renameProgram,List.map_append]
  cases divide <;> simp only [firstGroup,baseFirstGroup,Bool.false_eq_true,if_false,if_true,
    append,Nat.mul_zero,codec.1,codec.2,shifted_cell]

theorem firstGroup_run (divide : Bool) (s : State) (m : List Bool) :
    pullState (shifted (pi 0)) (run (firstGroup divide) m s)=
      run (baseFirstGroup divide) m (pullState (shifted (pi 0)) s) := by
  rw [firstGroup_eq_rename]
  exact run_rename _ (shifted _).injective _ m s

/-- Structural allocation transport only. The caller must derive both
boundaries from its encoded frames before using this helper. -/
theorem firstGroup_state_eq (divide : Bool) (s : State) (m : List Bool)
    (hin : ∀q,zeroRegion q → s.basis (base q)=false)
    (hout : ∀q,zeroRegion q → (run (baseFirstGroup divide) m s).basis (base q)=false) :
    run (firstGroup divide) m s=run (baseFirstGroup divide) m s := by
  have fix := fun q hq => pi_outside 0 q (by decide) hq
  have input := shifted_zero_boundary (pi 0) fix s hin
  have output := shifted_zero_boundary (pi 0) fix (run (baseFirstGroup divide) m s) hout
  apply pullState_perm_injective (shifted (pi 0))
  rw [firstGroup_run,input,output]

/-- Encoding does not weaken the complete outside-register frame. Equal
payloads and physical phases identify one complete encoded State. -/
theorem encoded_field_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : EncodedFieldFrame base (base 2409) origin X Y s)
    (ht : EncodedFieldFrame base (base 2409) origin X Y t)
    (phase : s.phase=t.phase) : s=t := by
  obtain ⟨a,ha,fa,ea⟩ := hs
  obtain ⟨b,hb,fb,eb⟩ := ht
  have raw : a=b := by
    apply State.extensionality
    · exact ha.trans (phase.trans hb.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ fa fb
  rw [ea,eb,raw]

theorem encoded_canonical_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : EncodedCanonicalFrame origin X Y s)
    (ht : EncodedCanonicalFrame origin X Y t)
    (phase : s.phase=t.phase) : s=t := by
  obtain ⟨a,ha,fa,ea⟩ := hs
  obtain ⟨b,hb,fb,eb⟩ := ht
  have raw : a=b := by
    apply State.extensionality
    · exact ha.trans (phase.trans hb.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ fa fb
  rw [ea,eb,raw]

/-- The accepted leaf cancellation can be followed by actual remaining
cell instructions and the full encoder with one common suffix stream.
This statement makes no claim that the seed commutes with a decoder. -/
theorem raw_entry_suffix_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (Y : Fp) (s : State) (mOld mNew mSuffix : List Bool) (suffix : Program)
    (hg0 : s.basis sign=false) (hs0 : s.basis effS=false)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hR : regValue (skywalkSharedField w).z s.basis=Y.val)
    (hY : regValue (skywalkSharedField w).a s.basis=0) :
    run (allGroupEncode w 170) []
      (run suffix mSuffix (run (EntryFieldSeedCancellation.oldEntry w b g swap sign effS ig is) mOld s))=
    run (allGroupEncode w 170) []
      (run suffix mSuffix (run (EntryFieldSeedCancellation.newEntry w b swap sign effS is) mNew s)) := by
  rw [EntryFieldSeedCancellation.entry_state_eq w b g swap sign effS ig is hn hl ho hoS
    Y s mOld mNew hg0 hs0 hw hu hR hY]

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.firstGroup_eq_rename
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.encoded_field_unique
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.raw_entry_suffix_eq
