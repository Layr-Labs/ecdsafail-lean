import ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrimForward
import ECDSAAdd.Arithmetic.TerminalMappedFieldSegment

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run wires logicalCell mappedGroups toffoliCount measurementCount

/-- Entry cancellation and the previously proved terminal omission are
separate transformations: all170 native codecs and raw510 are retained. -/
def terminalReplay (divide : Bool) : Program :=
  if divide then firstGroup divide ++ mappedGroups divide 1 169 ++
      renameProgram allPlaced (logicalCell divide 510)
  else renameProgram allPlaced (logicalCell divide 510) ++
      mappedGroups divide 1 169 ++ firstGroup divide

def terminalFieldSegment (divide : Bool) : Program :=
  (if divide then [] else renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) ++
  renameProgram allPlaced (converterPair false) ++ terminalReplay divide ++
  renameProgram allPlaced (converterPair true) ++
  (if divide then renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) else [])

theorem terminalReplay_support_sub (divide : Bool) : wires (terminalReplay divide) ⊆ wires (replay divide) := by
  cases divide <;> simp only [terminalReplay,replay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.subset_iff]
  all_goals intro q h; simp only [Finset.mem_union] at h ⊢; tauto

private theorem terminal_empty_wires : wires ([] : Program)=∅ := by simp [wires]

theorem terminalFieldSegment_support (divide : Bool) : wires (terminalFieldSegment divide) ⊆ slots.toFinset := by
  have rp := (terminalReplay_support_sub divide).trans ((replay_support_sub divide).trans (mappedReplay_support divide))
  have a := converters_support false
  have b := converters_support true
  cases divide <;> simp only [terminalFieldSegment,Bool.false_eq_true,if_false,if_true,
    wires_append,terminal_empty_wires,Finset.empty_union,Finset.union_empty,
    Finset.union_subset_iff,and_assoc]
  · exact ⟨copy_support,a,rp,b⟩
  · exact ⟨a,rp,b,copy_support⟩

theorem terminalReplay_counts (divide : Bool) :
    toffoliCount (terminalReplay divide)=(if divide then 654247 else 654757) ∧ measurementCount (terminalReplay divide)=522921 := by
  have groups := mappedGroups_counts divide 1 169
  have first := firstGroup_counts divide
  have cell := logicalCell_counts divide 510
  have renamed := renameProgram_counts allPlaced (logicalCell divide 510)
  cases divide <;> simp only [terminalReplay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,groups.1,groups.2,first.1,first.2,
    renamed.1,renamed.2,cell.1,cell.2]
  all_goals norm_num

/-- Savings here include only the separately established terminal cell.
The1535 entry saving is relative to the current terminal-trim wrapper. -/
theorem terminalFieldSegment_counts (divide : Bool) :
    toffoliCount (terminalFieldSegment divide)=(if divide then 657307 else 657817) ∧ measurementCount (terminalFieldSegment divide)=525981 := by
  have old := fieldSegment_counts divide
  have full := replay_counts divide
  have trim := terminalReplay_counts divide
  simp only [fieldSegment,toffoliCount_append,measurementCount_append] at old
  simp only [terminalFieldSegment,toffoliCount_append,measurementCount_append]
  rw [full.1,full.2] at old
  rw [trim.1,trim.2]
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true] at old ⊢
  all_goals constructor <;> omega

private def oldTerminalPrefix : Program := fieldPrefix true ++
  renameProgram allPlaced (converterPair false) ++ mappedGroup true 0
private def newTerminalPrefix : Program := renameProgram allPlaced (converterPair false) ++ firstGroup true
private def terminalSuffix : Program := mappedGroups true 1 169 ++
  renameProgram allPlaced (logicalCell true 510) ++
  renameProgram allPlaced (converterPair true) ++ renameProgram allPlaced (copyPairAt id)

private theorem forward_groups_succ (j n : Nat) :
    mappedGroups true j (n+1)=mappedGroup true j++mappedGroups true (j+1) n := by
  simp only [mappedGroups,if_true]

private theorem oldTerminal_join : MappedCompressed.fieldTrimSegment true=oldTerminalPrefix++terminalSuffix := by
  have groups : mappedGroups true 0 170=mappedGroup true 0++mappedGroups true 1 169 :=
    forward_groups_succ 0 169
  simp only [MappedCompressed.fieldTrimSegment,canonicalTrimReplay,trimReplay,oldTerminalPrefix,
    terminalSuffix,fieldPrefix,fieldSuffix,groups,if_true,List.append_assoc]
private theorem newTerminal_join : terminalFieldSegment true=newTerminalPrefix++terminalSuffix := by
  simp only [terminalFieldSegment,terminalReplay,newTerminalPrefix,terminalSuffix,copyPairAt,
    if_true,List.nil_append,List.append_assoc]

-- Keep programs symbolic so kernel conversion does not evaluate concrete gate lists.
private theorem replace_prefix (P Q R : Program) (s : State) (m : List Bool)
    (same : ∀ a b, run P a s = run Q b s) :
    run (P ++ R) (List.replicate (measurementCount P) false ++
      m.drop (measurementCount Q)) s = run (Q ++ R) m s := by
  rw [run_append,run_append,same _ (m.take (measurementCount Q))]
  simp only [List.drop_append,List.length_replicate,Nat.sub_self,List.drop_zero,
    List.drop_replicate,List.replicate_zero,List.nil_append]

/-- Closed forward entry cancellation on the current511-cell wrapper.
Terminal omission is inherited from its accepted512-trace derivation,
without adding any terminal-source, activation or measurement premise. -/
theorem terminalFieldTrimSegment_forward_spec
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
    let out := run (terminalFieldSegment true) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out := by
  let suffixRecords := m.drop (measurementCount newTerminalPrefix)
  let records := List.replicate (measurementCount oldTerminalPrefix) false ++ suffixRecords
  have old := MappedCompressed.fieldTrimSegment_spec true hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy x hx0 hx trace Y s records input
  have actualStateEq : run (MappedCompressed.fieldTrimSegment true) records s=run (terminalFieldSegment true) m s := by
    rw [oldTerminal_join,newTerminal_join]
    exact replace_prefix oldTerminalPrefix newTerminalPrefix terminalSuffix s m (fun a b =>
      forward_prefix_state_eq hn hlo ho hp (packet_layouts _ _ _ hf 0 (by decide))
        origin hg0 hs0 env legal hw hu hr hy Y s a b input)
  rw [actualStateEq] at old
  exact old

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.terminalFieldSegment_support
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.terminalFieldSegment_counts
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.terminalFieldTrimSegment_forward_spec
