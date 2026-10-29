import ECDSAAdd.Submission.Entrant.HalfConvert
import ECDSAAdd.Arithmetic.EntryForwardSelectedPoolRestore
import ECDSAAdd.Arithmetic.PenultimateMappedForward
import ECDSAAdd.Arithmetic.PenultimateMappedInverse
import ECDSAAdd.Arithmetic.PenultimateMappedResources
import ECDSAAdd.Arithmetic.MappedFieldPhysical

/-! Field segment with halving endpoints.

The protected segment converts both 256-bit field ports to balanced form on
entry and both back on exit (four compare-based converters, 3,060 Toffolis).
Here only the target port is converted, by the halving converter of
`HalfConvert`, which stores the balanced word of `Y/2`; the source port is
filled from (multiplication) or cleared against (division) the target while
both are balanced, so it never needs a converter.  The unchanged entry-trimmed
511-cell replay is linear in its payload, so it runs on `Y/2` and the exit
converter doubles its result back.  Cost: 255 + 255 Toffolis per segment. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.HalfField
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed Secp256k1 BalancedField
open CompressedFieldSupport CompressedAllocation OffsetBorrowedCanonical RecordedQuantum
attribute [local irreducible] run wires allGroupEncode compressedHistoryEncode

abbrev tgt : BalancedConvert.Layout := balancedSharedTargetConvert base
abbrev ports : BalancedCircuit.Layout := balancedSharedPorts base (base 2409)

def centerT : Program := HalfConvert.center tgt
def canonT : Program := HalfConvert.canonical tgt
def copyN : Program := copyRegister none ports.r ports.y

/-- Division: halve-center the dividend, replay, clear the duplicated
source, double back.  Multiplication: halve-center, duplicate, replay, double. -/
def segment (divide : Bool) : Program :=
  if divide then centerT++(PenultimateMapped.replay true++(copyN++canonT))
  else centerT++(copyN++(PenultimateMapped.replay false++canonT))

/-! Site bookkeeping. -/

def ids : List Nat := [1797,1027,1796,2311,1025]++List.range' 2056 256++
  List.range' 770 256++List.range' 1540 255

private theorem ids_mem (i : Nat) (h : i=1797 ∨ i=1027 ∨ i=1796 ∨ i=2311 ∨ i=1025 ∨
    (2056 ≤ i ∧ i<2312) ∨ (770 ≤ i ∧ i<1026) ∨ (1540 ≤ i ∧ i<1795)) :
    base i∈(ids.map base).toFinset := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨i,?_,rfl⟩
  simp only [ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false]
  omega

private theorem tgt_ids : ∀q∈tgt.wires,q∈(ids.map base).toFinset := by
  intro q hq
  simp only [BalancedConvert.Layout.wires,balancedSharedTargetConvert,wireBlock,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((rfl|rfl|rfl|rfl)|⟨i,hi,rfl⟩)|⟨i,hi,rfl⟩
  all_goals apply ids_mem; omega

private theorem ports_r : ports.r=wireBlock base 2056 256 := balancedSharedPorts_r base (base 2409)
private theorem ports_y : ports.y=wireBlock base 770 256 := balancedSharedPorts_y base (base 2409)

theorem centerT_sites : wires centerT⊆(ids.map base).toFinset := by
  intro q hq
  exact tgt_ids q (List.mem_toFinset.mp
    ((HalfConvert.support tgt (balancedSharedTargetConvert_widths base)).1 hq))

theorem canonT_sites : wires canonT⊆(ids.map base).toFinset := by
  intro q hq
  exact tgt_ids q (List.mem_toFinset.mp
    ((HalfConvert.support tgt (balancedSharedTargetConvert_widths base)).2 hq))

theorem copyN_sites : wires copyN⊆(ids.map base).toFinset := by
  intro q hq
  have h := copyRegister_wires_subset none ports.r ports.y hq
  rw [ports_r,ports_y] at h
  simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append,
    wireBlock,List.mem_map,List.mem_range'_1] at h
  rcases h with ⟨i,hi,rfl⟩|⟨i,hi,rfl⟩
  all_goals apply ids_mem; omega

theorem ids_slots : (ids.map base).toFinset⊆slots.toFinset := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
  simp only [ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
  apply slot_mem
  · unfold live; omega
  · unfold omitted; omega

/-- The full history encoder never touches the endpoint sites. -/
theorem encoder_disjoint (P : Program) (h : wires P⊆(ids.map base).toFinset) :
    Disjoint (wires (allGroupEncode base 170)) (wires P) := by
  have hist := compressedPrefix_history_support base base_pool_nodup base_above 512 (by decide)
  rw [encode_prefix_512] at hist
  apply Finset.disjoint_left.mpr
  intro q hq hc
  have history := List.mem_toFinset.mp (hist hq)
  have converted := List.mem_toFinset.mp (h hc)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp converted
  simp only [List.mem_append,wireBlock] at history
  rcases history with history|history
  all_goals
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp history
    have same := base_injective eq
    subst i
    simp only [List.mem_range'_1] at hi
    simp only [ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
    omega

private theorem xor_neutral (a b : Bool) (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem encoded_transport (P : Program) (dis : Disjoint (wires (allGroupEncode base 170)) (wires P))
    (s raw : State) (m : List Bool) (encoded : s=run (allGroupEncode base 170) [] raw)
    (phase : (run P m raw).phase=raw.phase) :
    (run P m s).phase=s.phase ∧ run P m s=run (allGroupEncode base 170) [] (run P m raw) := by
  have read : ∀q∈wires P,s.basis q=raw.basis q := by
    intro q hq
    rw [encoded]
    exact run_preserves_outside _ [] raw q (fun he => Finset.disjoint_left.mp dis he hq)
  have increment := (run_local_increment P s raw m read).1
  rw [phase,Bool.xor_self] at increment
  refine ⟨xor_neutral _ _ increment,?_⟩
  rw [encoded]
  exact (run_disjoint_commute _ _ dis [] m raw).symm

/-! Frame steps. -/

private theorem port_split :
    (skywalkSharedField base).z=ports.r++[base 2312] ∧
    (skywalkSharedField base).a=ports.y++[base 1026] := by
  rw [skywalkShared_field_z,ports_r,ports_y]
  constructor
  · have split := wireBlock_append base 2056 256 1
    simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using split.symm
  · have split := wireBlock_append base 770 256 1
    simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using split.symm

private theorem value_bound (X : Fp) : X.val<2^256 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact (ZMod.val_lt X).trans (by norm_num [p])

theorem centerWord_zero : centerWord (0:Fp)=0 := by
  have h : (0:Int)≤q := by norm_num [q,p]
  simp [centerWord,centerFp,encodeWord,h]

private theorem target_clean (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0) (A B : Nat) (st : BasisState)
    (frame : PairFrame ports.r ports.y origin A B st) :
    ∀q∈BalancedConvert.work tgt,st q=false := by
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have away := (balancedSharedBoundary base (base 2409) hn).targetWorkAway
  intro q hq
  exact (frame.2.2 q (away q hq).1 (away q hq).2).trans (clean.1 q hq)

private theorem pair_dis (hn : (skywalkSharedWires base).Nodup) : ports.r.Disjoint ports.y :=
  (List.nodup_append'.mp (balancedSharedLayout_pairND base (base 2409) hn)).2.2

private theorem tgt_word : tgt.word=ports.r := balancedSharedTargetConvert_word base (base 2409)

/-- Halving entry conversion of the target port; the zero source port is
already its own balanced word. -/
theorem center_frame (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin (X/2) 0 (run centerT m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have split := port_split
  rw [split.1,split.2,ZMod.val_zero] at frame
  have narrow := balancedPair_narrow ports.r ports.y (base 2312) (base 1026) origin raw.basis
    X.val 0 (by rw [ports_r,wireBlock_length]; exact value_bound X)
    (by rw [ports_y,wireBlock_length]; norm_num) frame hr hy
  have c := HalfConvert.center_correct tgt (balancedSharedTargetConvert_widths base)
    (balancedSharedTargetConvert_nodup base hn) X raw m (by rw [tgt_word]; exact narrow.1)
    (target_clean hn origin hw hu _ _ _ narrow)
  have pf : PairFrame ports.r ports.y origin (centerWord (X/2)) (centerWord 0)
      (run centerT m raw).basis := by
    rw [centerWord_zero]
    exact PairFrame.update_temp ports.r ports.y origin raw.basis _ X.val 0 _ (pair_dis hn) narrow
      (by rw [←tgt_word]; exact c.2.2.2) (by rw [←tgt_word]; exact c.2.1)
  have actual := encoded_transport centerT (encoder_disjoint _ centerT_sites) s raw m encoded c.1
  exact ⟨actual.1,run centerT m raw,c.1.trans (phase.trans actual.1.symm),pf,actual.2⟩

/-- Doubling exit conversion of the target port; the zero source port is
already canonical. -/
theorem canon_frame (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X 0 s) :
    (run canonT m s).phase=s.phase ∧ EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  rw [centerWord_zero] at frame
  have c := HalfConvert.canonical_correct tgt (balancedSharedTargetConvert_widths base)
    (balancedSharedTargetConvert_nodup base hn) X raw m (by rw [tgt_word]; exact frame.1)
    (target_clean hn origin hw hu _ _ _ frame)
  have pf : PairFrame ports.r ports.y origin (2*X).val 0 (run canonT m raw).basis :=
    PairFrame.update_temp ports.r ports.y origin raw.basis _ _ 0 _ (pair_dis hn) frame
      (by rw [←tgt_word]; exact c.2.2.2) (by rw [←tgt_word]; exact c.2.1)
  have outside := balancedSharedDivision_high_outside base hn
  have wide := balancedPair_widen ports.r ports.y (base 2312) (base 1026) origin _ (2*X).val 0 pf
    (by rw [ports_r,ports_y]; exact outside.1) (by rw [ports_r,ports_y]; exact outside.2) hr hy
  have split := port_split
  rw [←split.1,←split.2] at wide
  have actual := encoded_transport canonT (encoder_disjoint _ canonT_sites) s raw m encoded c.1
  refine ⟨actual.1,run canonT m raw,c.1.trans (phase.trans actual.1.symm),?_,actual.2⟩
  rw [ZMod.val_zero]
  exact wide

private theorem copy_raw (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (A B : Nat) (raw : State) (m : List Bool)
    (frame : PairFrame ports.r ports.y origin A B raw.basis) :
    (run copyN m raw).phase=raw.phase ∧
    PairFrame ports.r ports.y origin A (B ^^^ A) (run copyN m raw).basis := by
  have len : ports.r.length=ports.y.length := by rw [ports_r,ports_y]; simp [wireBlock_length]
  obtain ⟨phase,keep,value⟩ := copyRegister_correct none ports.r ports.y len
    (balancedSharedLayout_pairND base (base 2409) hn) (by simp) raw m
  refine ⟨phase,PairFrame.update_dst _ _ origin raw.basis _ A B _ (pair_dis hn) frame keep ?_⟩
  simpa only [copyValue,frame.1,frame.2.1] using value

/-- Duplicate the balanced target into the clean source. -/
theorem copy_fill (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X 0 s) :
    (run copyN m s).phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin X X (run copyN m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have c := copy_raw hn origin _ _ raw m frame
  rw [centerWord_zero,Nat.zero_xor] at c
  have actual := encoded_transport copyN (encoder_disjoint _ copyN_sites) s raw m encoded c.1
  exact ⟨actual.1,run copyN m raw,c.1.trans (phase.trans actual.1.symm),c.2,actual.2⟩

/-- Clear the source against the equal balanced target. -/
theorem copy_clear (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X X s) :
    (run copyN m s).phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin X 0 (run copyN m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have c := copy_raw hn origin _ _ raw m frame
  rw [Nat.xor_self,←centerWord_zero] at c
  have actual := encoded_transport copyN (encoder_disjoint _ copyN_sites) s raw m encoded c.1
  exact ⟨actual.1,run copyN m raw,c.1.trans (phase.trans actual.1.symm),c.2,actual.2⟩

/-! The unchanged forward replay as a frame step. -/

private theorem replay_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplay (a++b) Q=skywalkPayloadReplay b (skywalkPayloadReplay a Q) := by
  induction a generalizing Q with
  | nil => rfl
  | cons l ls ih => exact ih (skywalkPayloadCell l.1 l.2 Q)

private theorem packet_indexed (j : Nat) : packetLetters j=indexedLetters (3*j) 3 := by
  simp [packetLetters,indexedLetters,tapeLetter,List.range_succ]

private theorem groups_succ (origin : BasisState) (j n : Nat) (Q : Fp×Fp) :
    groupsPayload true origin j (n+1) Q=groupsPayload true origin (j+1) n
      (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters j)) Q) := by
  simp only [groupsPayload,if_true,Bool.not_true,directionalPayload,Bool.false_eq_true,if_false]

private theorem first_rest_payload (origin : BasisState) (Y : Fp) :
    groupsPayload true origin 1 169
      (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0))=
      PenultimateSwapIdentity.penultimatePayload origin Y := by
  have start : groupsPayload true origin 0 170 (2*Y,0)=
      groupsPayload true origin 1 169
        (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)) :=
    groups_succ origin 0 169 (2*Y,0)
  have generic : groupsPayload true origin 0 170 (2*Y,0)=
      skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
        (indexedLetters (3*0) (3*170))) (2*Y,0) :=
    PenultimateMapped.forward_groups_payload 0 170 origin (2*Y,0)
  have zero : 3*0=0 := by decide
  have length : 3*170=510 := by decide
  have lettersEq : indexedLetters (3*0) (3*170)=indexedLetters 0 510 :=
    congrArg₂ indexedLetters zero length
  have lifted : skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
      (indexedLetters (3*0) (3*170))) (2*Y,0)=
        skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
          (indexedLetters 0 510)) (2*Y,0) :=
    congrArg (fun ls : List MixedTranscriptLetter =>
      skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) ls) (2*Y,0)) lettersEq
  have fold : skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
      (indexedLetters 0 510)) (2*Y,0)=PenultimateSwapIdentity.penultimatePayload origin Y := by
    unfold PenultimateSwapIdentity.penultimatePayload
    rfl
  exact start.symm.trans (generic.trans (lifted.trans fold))

private theorem trim_split : trimLetters=indexedLetters 0 510++[tapeLetter 510] := by
  have last : indexedLetters 510 1=[tapeLetter 510] := by
    simp only [indexedLetters,List.range_one,List.map_cons,List.map_nil,Nat.add_zero]
  have split := indexedLetters_append 0 510 1
  rw [last] at split
  simpa only [Nat.zero_add,Nat.reduceAdd,trimLetters] using split

private theorem last_payload (origin : BasisState) (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int))) :
    directionalPayload (!true) (mixedTranscriptControls origin (base 2400) [tapeLetter 510])
      ((PenultimateSwapIdentity.penultimatePayload origin Y).1,
       (PenultimateSwapIdentity.penultimatePayload origin Y).2)=
      (if origin (base 2400) then Y/(x:Fp) else Y,if origin (base 2400) then Y/(x:Fp) else Y) := by
  have whole := trimLetters_quotient origin x Y hx0 hx trace
  rw [trim_split] at whole
  simp only [mixedTranscriptControls,List.map_append,replay_append] at whole
  simp only [directionalPayload,Bool.not_true,Bool.false_eq_true,if_false,Prod.mk.eta,
    mixedTranscriptControls]
  rw [←whole]
  rfl

theorem replay_forward
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin Y 0 s) :
    (run (PenultimateMapped.replay true) m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin (if origin (base 2400) then Y/(x:Fp) else Y)
        (if origin (base 2400) then Y/(x:Fp) else Y) (run (PenultimateMapped.replay true) m s) := by
  let Z := if origin (base 2400) then Y/(x:Fp) else Y
  let A := PenultimateSwapIdentity.penultimatePayload origin Y
  let Q := skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)
  let P : State → State → Prop := fun initial out => EncodedFieldFrame base (base 2409) origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedFieldFrame base (base 2409) origin Z Z out
  have all := run_three_states (EntryMappedFieldSegmentTrim.firstGroup true) (mappedGroups true 1 169)
    (renameProgram allPlaced (PenultimateSwapIdentity.cell true)) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have a := EntryMappedFieldSegmentTrim.firstGroup_forward_step hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf 0 (by decide))
        origin hg0 hs0 env legal Y initial m1 hin
      rw [h1] at a
      have frame1 : EncodedFieldFrame base (base 2409) origin Q.1 Q.2 s1 := a.2
      have bAll := mappedGroups_frame true 1 169 (by decide) hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf)
        origin hg0 hs0 env legal Q.1 Q.2 s1 m2 frame1
      have bPhase : (run (mappedGroups true 1 169) m2 s1).phase=s1.phase := bAll.2.1
      have bFrame : EncodedFieldFrame base (base 2409) origin
          (groupsPayload true origin 1 169 (Q.1,Q.2)).1
          (groupsPayload true origin 1 169 (Q.1,Q.2)).2
          (run (mappedGroups true 1 169) m2 s1) := bAll.2.2
      rw [h2] at bPhase bFrame
      have payload : groupsPayload true origin 1 169 (Q.1,Q.2)=A := by
        change groupsPayload true origin 1 169 Q=A
        exact first_rest_payload origin Y
      rw [payload] at bFrame
      have same := PenultimateMappedCellProof.forward_cell_eq hn hlo ho hp hf origin hg0 hs0 env legal
        A.1 A.2 s2 m3 m3 bFrame (PenultimateSwapIdentity.penultimate_half_dup origin x Y hx0 hx trace)
      have old := trimCell_step true hn hlo ho hp hf origin hg0 hs0 env legal A.1 A.2 s2 m3 bFrame
      rw [←same,h3,last_payload origin x Y hx0 hx trace] at old
      exact ⟨old.2.1.trans (bPhase.trans a.1),old.2.2⟩) s m
  have shape : PenultimateMapped.replay true=EntryMappedFieldSegmentTrim.firstGroup true++
      (mappedGroups true 1 169++renameProgram allPlaced (PenultimateSwapIdentity.cell true)) := by
    simp only [PenultimateMapped.replay,if_true,List.append_assoc]
  rw [shape]
  exact all input

/-! Complete segment contract. -/

private theorem run_four_states (a b c d : Program) (P : State → State → Prop)
    (h : ∀ (s s1 s2 s3 s4 : State) (m1 m2 m3 m4 : List Bool),
      run a m1 s=s1 → run b m2 s1=s2 → run c m3 s2=s3 → run d m4 s3=s4 → P s s4)
    (s : State) (m : List Bool) : P s (run (a++(b++(c++d))) m s) := by
  simp only [run_append]
  exact h _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl

private theorem double_half (Y W : Fp) : 2*(Y/2*W)=Y*W := by
  have two : (2:Fp)≠0 := by decide
  field_simp

private theorem double_half_div (Y W : Fp) : 2*(Y/2/W)=Y/W := by
  have two : (2:Fp)≠0 := by decide
  rw [div_div,mul_comm (2:Fp) W,←div_div,mul_div_cancel₀ _ two]

private theorem double_half_one (Y : Fp) : 2*(Y/2)=Y := by
  have two : (2:Fp)≠0 := by decide
  exact mul_div_cancel₀ Y two

/-- Same hypotheses and conclusion as the protected selected field segment. -/
theorem segment_spec (divide : Bool)
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
    let out := run (segment divide) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out := by
  cases divide
  · let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
      out.phase=initial.phase ∧ EncodedCanonicalFrame origin (fieldResult false origin x Y) 0 out
    have all := run_four_states centerT copyN (PenultimateMapped.replay false) canonT P (by
      intro initial s1 s2 s3 s4 m1 m2 m3 m4 h1 h2 h3 h4 hin
      have c1 := center_frame hn origin hw hu hr hy Y initial m1 hin
      rw [h1] at c1
      have c2 := copy_fill hn origin (Y/2) s1 m2 c1.2
      rw [h2] at c2
      have c3 := PenultimateMapped.replay_inverse_spec hn hlo ho hp hf origin hg0 hs0 env legal
        x (Y/2) hx0 hx trace s2 m3 c2.2
      rw [h3] at c3
      have c4 := canon_frame hn origin hw hu hr hy _ s3 m4 c3.2
      rw [h4] at c4
      refine ⟨c4.1.trans (c3.1.trans (c2.1.trans c1.1)),?_⟩
      have eq : 2*(if origin (base 2400) then Y/2*(x:Fp) else Y/2)=fieldResult false origin x Y := by
        unfold fieldResult
        split
        · simp only [Bool.false_eq_true,if_false]; exact double_half Y _
        · exact double_half_one Y
      rw [←eq]
      exact c4.2) s m
    simpa only [segment,Bool.false_eq_true,if_false] using all input
  · let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
      out.phase=initial.phase ∧ EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out
    have all := run_four_states centerT (PenultimateMapped.replay true) copyN canonT P (by
      intro initial s1 s2 s3 s4 m1 m2 m3 m4 h1 h2 h3 h4 hin
      have c1 := center_frame hn origin hw hu hr hy Y initial m1 hin
      rw [h1] at c1
      have c2 := replay_forward hn hlo ho hp hf origin hg0 hs0 env legal x hx0 hx trace
        (Y/2) s1 m2 c1.2
      rw [h2] at c2
      have c3 := copy_clear hn origin _ s2 m3 c2.2
      rw [h3] at c3
      have c4 := canon_frame hn origin hw hu hr hy _ s3 m4 c3.2
      rw [h4] at c4
      refine ⟨c4.1.trans (c3.1.trans (c2.1.trans c1.1)),?_⟩
      have eq : 2*(if origin (base 2400) then Y/2/(x:Fp) else Y/2)=fieldResult true origin x Y := by
        unfold fieldResult
        split
        · simp only [if_true]; exact double_half_div Y _
        · exact double_half_one Y
      rw [←eq]
      exact c4.2) s m
    simpa only [segment,if_true] using all input

theorem segment_pool_frame (divide : Bool)
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
    (run (segment divide) m s).phase=s.phase ∧
      ∀q∈skywalkPoolWires base,(run (segment divide) m s).basis q=s.basis q := by
  have result := segment_spec divide hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy x hx0 hx trace Y s m input
  have before := encodedCanonical_pool_basis hn hlo origin ha Y s input
  have after := encodedCanonical_pool_basis hn hlo origin ha _ (run (segment divide) m s) result.2
  exact ⟨result.1,fun q hq => (after q hq).trans (before q hq).symm⟩

/-! Resources, support and physical form. -/

theorem segment_counts (divide : Bool) :
    toffoliCount (segment divide)=(if divide then 654500 else 655010) ∧
    measurementCount (segment divide)=523430 := by
  have c := HalfConvert.counts tgt (balancedSharedTargetConvert_widths base)
  have r := PenultimateMapped.replay_counts divide
  have len : ports.r.length=ports.y.length := by rw [ports_r,ports_y]; simp [wireBlock_length]
  have k := copyRegister_counts none ports.r ports.y len
  simp only [Option.isSome_none,Bool.false_eq_true,if_false] at k
  cases divide <;> simp only [segment,centerT,canonT,copyN,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,c.1,c.2.1,c.2.2.1,c.2.2.2,k.1,k.2] at r ⊢
  · rw [r.1,r.2]; norm_num
  · rw [r.1,r.2]; norm_num

theorem replay_sub (divide : Bool) :
    wires (PenultimateMapped.replay divide)⊆wires (PenultimateMapped.fieldSegment divide) := by
  intro q hq
  simp only [PenultimateMapped.fieldSegment,wires_append,Finset.mem_union]
  tauto

theorem segment_support (divide : Bool) : wires (segment divide)⊆slots.toFinset := by
  have rp := (replay_sub divide).trans (PenultimateMapped.fieldSegment_support divide)
  have ce := centerT_sites.trans ids_slots
  have ca := canonT_sites.trans ids_slots
  have co := copyN_sites.trans ids_slots
  cases divide <;> simp only [segment,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.union_subset_iff]
  · exact ⟨ce,co,rp,ca⟩
  · exact ⟨ce,rp,co,ca⟩

theorem segment_physical (divide : Bool) : GatePhysical (segment divide) := by
  have hn : (skywalkSharedWires base).Nodup := by
    apply List.Nodup.map_on
    · intro a _ b _ eq; exact base_injective eq
    · exact List.nodup_range'
  have h := HalfConvert.physical tgt (balancedSharedTargetConvert_widths base)
    (balancedSharedTargetConvert_nodup base hn)
  have cp : GatePhysical copyN :=
    copyRegister_physical none ports.r ports.y (balancedSharedLayout_pairND base (base 2409) hn) (by simp)
  have rp := penultimateReplay_physical divide
  cases divide <;> simp only [segment,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨h.1,cp,rp,h.2⟩
  · exact ⟨h.1,rp,cp,h.2⟩

end ECDSAAdd.Entrant.HalfField
