import ECDSAAdd.Submission.Entrant.LaneICell
import ECDSAAdd.Arithmetic.EntryForwardSelectedFieldSegment

/-! The selected field segment with every field cell using the 256-wide fold.
The single replacement point is `fieldSegmentI` for
`PenultimateMapped.fieldSegment` (= `selectedFieldSegment`): on the original
segment domain both produce the identical complete State. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic Secp256k1 BalancedField MappedCompressed CompressedAllocation
  CompressedFieldSupport
attribute [local irreducible] run logicalCell compressedHistoryEncode compressedHistoryDecode
  allGroupEncode

/-! ### Generic transports -/

/-- Renaming by a placement permutation preserves a State equality, given
only a clean input allocation boundary. -/
theorem rename_eq (e : Equiv.Perm Nat) (fix : ∀q,¬zeroRegion q → e q=q)
    (P P' : Program) (s : State) (m : List Bool)
    (hin : ∀q,zeroRegion q → s.basis (base q)=false)
    (h : run P' m s=run P m s) :
    run (renameProgram (shifted e) P') m s=run (renameProgram (shifted e) P) m s := by
  have input := shifted_zero_boundary e fix s hin
  apply pullState_perm_injective (shifted e)
  rw [run_rename _ (shifted e).injective,run_rename _ (shifted e).injective,input,h]

/-- A decoded window with any body equal on raw field frames is equal on
the encoded frame. -/
theorem encoded_window_eq (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (j : Nat) (hj : j < 170) (origin : BasisState) (legal : RawGroupLegal w 170 origin)
    (X Y : Fp) (body body' : Program)
    (support : wires body ⊆ groupReadSites w b sign eff (3*j))
    (sub : InstrSub body' body)
    (hc : measurementCount body'=measurementCount body)
    (heq : ∀ (t : State) (r : List Bool),
      PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        origin (centerWord X) (centerWord Y) t.basis → run body' r t=run body r t)
    (s : State) (m : List Bool) (input : EncodedFieldFrame w sign origin X Y s) :
    run (compressedHistoryDecode w (3*j)++body'++compressedHistoryEncode w (3*j)) m s=
      run (compressedHistoryDecode w (3*j)++body++compressedHistoryEncode w (3*j)) m s := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have hs := hp sign (by simp)
  have leg := frame_history_legal w sign hn hs origin raw.basis _ _ legal frame
  have factor := allGroupEncode_factor w pool hlo 170 j (by decide) hj raw
  have hE := otherGroupEncode_disjoint w pool hlo 170 j (by decide) hj
  have hB := otherGroupEncode_body_disjoint w b sign eff hn hlo
    (hp b (by simp)) hs (hp eff (by simp)) 170 j (by decide) hj body support
  have hB' := otherGroupEncode_body_disjoint w b sign eff hn hlo
    (hp b (by simp)) hs (hp eff (by simp)) 170 j (by decide) hj body' (sub.wires_sub.trans support)
  have zero := (compressedHistory_counts w (3*j)).2.2.2
  have shape (P : Program) : run (compressedHistoryDecode w (3*j)++P++compressedHistoryEncode w (3*j)) m s=
      run (compressedHistoryEncode w (3*j)) (m.drop (measurementCount P))
        (run P m (run (compressedHistoryDecode w (3*j)) []
          (run (otherGroupEncode w j 170) [] (run (compressedHistoryEncode w (3*j)) [] raw)))) := by
    rw [eq,factor]
    simp only [List.append_assoc]
    rw [run_append,zero,List.take_zero,List.drop_zero,run_append,run_take]
  have t1 := window_transport_other w (3*j) pool hlo (by omega)
    (otherGroupEncode w j 170) body hE hB raw [] [] [] m
    (m.drop (measurementCount body)) (leg j hj)
  have t2 := window_transport_other w (3*j) pool hlo (by omega)
    (otherGroupEncode w j 170) body' hE hB' raw [] [] [] m
    (m.drop (measurementCount body')) (leg j hj)
  rw [shape,shape,t1,t2,hc,heq raw m frame]

/-! ### Native packets -/

def baseGroupI (divide : Bool) (j : Nat) : Program :=
  compressedHistoryDecode base (3*j) ++
  (if divide then replayFI base (base 2400) (base 2409) (base 2410) (packetLetters j)
   else replayII base (base 2400) (base 2409) (base 2410) (packetLetters j)) ++
  compressedHistoryEncode base (3*j)

theorem baseGroup_shape (divide : Bool) (j : Nat) (hj : j < 170) :
    baseGroup divide j=compressedHistoryDecode base (3*j) ++
      (if divide then OffsetBorrowedCanonical.replay base (base 2400) (base 2409) (base 2410) (packetLetters j)
       else OffsetBorrowedInverseCanonical.replay base (base 2400) (base 2409) (base 2410) (packetLetters j)) ++
      compressedHistoryEncode base (3*j) := by
  rw [baseGroup_eq_packet divide j hj]
  cases divide <;> simp only [packetLetters,codecGroupForward,codecGroupBackward,
    OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,Bool.false_eq_true,
    if_false,if_true,List.append_assoc,List.append_nil,List.nil_append]

theorem baseGroupI_sub (divide : Bool) (j : Nat) (hj : j < 170) :
    InstrSub (baseGroupI divide j) (baseGroup divide j) := by
  rw [baseGroup_shape divide j hj]
  cases divide <;> simp only [baseGroupI,Bool.false_eq_true,if_false,if_true]
  · exact ((InstrSub.refl _).append (replayII_sub _ _ _ _ _)).append (InstrSub.refl _)
  · exact ((InstrSub.refl _).append (replayFI_sub _ _ _ _ _)).append (InstrSub.refl _)

theorem baseGroupI_counts (divide : Bool) (j : Nat) (hj : j < 170) :
    measurementCount (baseGroupI divide j)=measurementCount (baseGroup divide j) ∧
    toffoliCount (baseGroupI divide j)+3=toffoliCount (baseGroup divide j) := by
  rw [baseGroup_shape divide j hj]
  have len : (packetLetters j).length=3 := by simp [packetLetters]
  have f := replayFI_counts base (base 2400) (base 2409) (base 2410) (packetLetters j)
  have i := replayII_counts base (base 2400) (base 2409) (base 2410) (packetLetters j)
  rw [len] at f i
  cases divide <;> simp only [baseGroupI,Bool.false_eq_true,if_false,if_true,
    measurementCount_append,toffoliCount_append] <;> constructor <;> omega

private theorem packet_support (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base) :
    wires (if divide then OffsetBorrowedCanonical.replay base (base 2400) (base 2409) (base 2410) (packetLetters j)
       else OffsetBorrowedInverseCanonical.replay base (base 2400) (base 2409) (base 2410) (packetLetters j)) ⊆
      groupReadSites base (base 2400) (base 2409) (base 2410) (3*j) := by
  have h := packet_structural_support divide j hj hn hlo
  have shape : packetLetters j=[(packetLetters j).getD 0 ((0,0),(false,false)),
      (packetLetters j).getD 1 ((0,0),(false,false)),(packetLetters j).getD 2 ((0,0),(false,false))] := by
    simp [packetLetters]
  rw [shape]
  cases divide <;> simpa only [rawForwardPacket,rawBackwardPacket,Bool.false_eq_true,if_false,if_true] using h

theorem baseGroupI_eq (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (baseGroupI divide j) m s=run (baseGroup divide j) m s := by
  rw [baseGroup_shape divide j hj]
  have support := packet_support divide j hj hn hlo
  cases divide
  · simp only [baseGroupI,Bool.false_eq_true,if_false] at support ⊢
    exact encoded_window_eq base _ _ _ hn hlo hp j hj origin legal X Y _ _ support
      (replayII_sub _ _ _ _ _) (replayII_counts _ _ _ _ _).1
      (fun t r ht => replayII_eq base _ _ _ hn _ hf ho origin hg0 hs0 env X Y t r ht) s m input
  · simp only [baseGroupI,if_true] at support ⊢
    exact encoded_window_eq base _ _ _ hn hlo hp j hj origin legal X Y _ _ support
      (replayFI_sub _ _ _ _ _) (replayFI_counts _ _ _ _ _).1
      (fun t r ht => replayFI_eq base _ _ _ hn _ hf ho origin hg0 hs0 env X Y t r ht) s m input

def mappedGroupI (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (pi j)) (baseGroupI divide j)

theorem mappedGroupI_sub (divide : Bool) (j : Nat) (hj : j < 170) :
    InstrSub (mappedGroupI divide j) (mappedGroup divide j) := by
  rw [mappedGroup_eq_rename divide j hj]
  exact (baseGroupI_sub divide j hj).rename _

theorem mappedGroupI_counts (divide : Bool) (j : Nat) (hj : j < 170) :
    measurementCount (mappedGroupI divide j)=measurementCount (mappedGroup divide j) ∧
    toffoliCount (mappedGroupI divide j)+3=toffoliCount (mappedGroup divide j) := by
  rw [mappedGroup_eq_rename divide j hj]
  have a := renameProgram_counts (shifted (pi j)) (baseGroupI divide j)
  have b := renameProgram_counts (shifted (pi j)) (baseGroup divide j)
  have c := baseGroupI_counts divide j hj
  simp only [mappedGroupI]
  constructor <;> omega

theorem mappedGroupI_eq (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (mappedGroupI divide j) m s=run (mappedGroup divide j) m s := by
  have hin := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  rw [mappedGroup_eq_rename divide j hj]
  exact rename_eq (pi j) (fun q hq => pi_outside j q hj hq) _ _ s m hin
    (baseGroupI_eq divide j hj hn hlo ho hp hf origin hg0 hs0 env legal X Y s m input)

def mappedGroupsI (divide : Bool) (j n : Nat) : Program :=
  PacketSequence.program divide (mappedGroupI divide) j n

theorem mapped_sequence_eqI (divide : Bool) (j n : Nat) :
    PacketSequence.program divide (mappedGroup divide) j n=mappedGroups divide j n := by
  induction n generalizing j with
  | zero => simp only [PacketSequence.program,mappedGroups]
  | succ n ih => cases divide <;> simp only [PacketSequence.program,mappedGroups,
      Bool.false_eq_true,if_false,if_true,ih]

theorem mappedGroupsI_eq (divide : Bool) (j n : Nat) (bound : j+n ≤ 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : ∀k,k < 170 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters k))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (mappedGroupsI divide j n) m s=run (mappedGroups divide j n) m s := by
  let p : Nat → Program := fun k => if k < 170 then mappedGroupI divide k else mappedGroup divide k
  have peq : ∀ j n, j+n ≤ 170 → PacketSequence.program divide p j n=mappedGroupsI divide j n := by
    intro j n hb
    induction n generalizing j with
    | zero => rfl
    | succ n ih =>
      have head : p j=mappedGroupI divide j := by simp only [p,if_pos (show j < 170 by omega)]
      have rest := ih (j+1) (by omega)
      cases divide <;> simp only [mappedGroupsI,PacketSequence.program,Bool.false_eq_true,
        if_false,if_true] at rest ⊢ <;> rw [head,rest]
  have all := PacketSequence.frame divide p (mappedGroup divide)
    (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters k)) V)
    (fun V t => EncodedFieldFrame base (base 2409) origin V.1 V.2 t) 170
    (fun k => by
      by_cases hk : k < 170
      · simp only [p,if_pos hk]; exact (mappedGroupI_counts divide k hk).1
      · simp only [p,if_neg hk])
    (fun k hk V t records h => by
      have eq := mappedGroupI_eq divide k hk hn hlo ho hp (hf k hk) origin hg0 hs0 env legal V.1 V.2 t records h
      have old := mappedGroup_encoded_step divide k hk hn hlo ho hp (hf k hk) origin hg0 hs0 env legal
        V.1 V.2 t records h
      simp only [p,if_pos hk]
      rw [eq]
      exact ⟨rfl,old.1,old.2⟩) j n bound (X,Y) s m input
  rw [←mapped_sequence_eqI,←peq j n bound]
  exact all.1

theorem mappedGroupsI_sub (divide : Bool) (j n : Nat) (bound : j+n ≤ 170) :
    InstrSub (mappedGroupsI divide j n) (mappedGroups divide j n) := by
  rw [←mapped_sequence_eqI]
  induction n generalizing j with
  | zero => exact InstrSub.refl _
  | succ n ih =>
    have head := mappedGroupI_sub divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroupsI,PacketSequence.program,Bool.false_eq_true,if_false,if_true] at rest ⊢
    · exact rest.append head
    · exact head.append rest

theorem mappedGroupsI_counts (divide : Bool) (j n : Nat) (bound : j+n ≤ 170) :
    measurementCount (mappedGroupsI divide j n)=measurementCount (mappedGroups divide j n) ∧
    toffoliCount (mappedGroupsI divide j n)+3*n=toffoliCount (mappedGroups divide j n) := by
  rw [←mapped_sequence_eqI]
  induction n generalizing j with
  | zero => simp [mappedGroupsI,PacketSequence.program]
  | succ n ih =>
    have head := mappedGroupI_counts divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroupsI,PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      measurementCount_append,toffoliCount_append] at rest ⊢ <;> constructor <;> omega

end ECDSAAdd.Entrant.LaneI
