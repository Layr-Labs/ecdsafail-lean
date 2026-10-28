import ECDSAAdd.Arithmetic.CompressedFieldEncodingFactor
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run

private theorem history_words_away (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign ∉ skywalkPoolWires w)
    (start : Nat) (hs : start+3 ≤ 512) (j : Fin 6) :
    compressedHistoryMap w start j ∉ (balancedSharedPorts w sign).r ∧
    compressedHistoryMap w start j ∉ (balancedSharedPorts w sign).y := by
  have away := history_active_away w sign hn ho start hs j
  constructor <;> intro h <;> apply away
  all_goals
    simp only [compressedHistoryMap,sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
      BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      BalancedCleanup.Layout.y,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto

/-- Field frames preserve the raw legal history on the entire fixed tape. -/
theorem frame_history_legal (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign ∉ skywalkPoolWires w)
    (base s : BasisState) (X Y : Nat) (legal : RawGroupLegal w 170 base)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base X Y s) :
    RawGroupLegal w 170 s := by
  intro k hk
  have same (j : Fin 6) : s (compressedHistoryMap w (3*k) j) = base (compressedHistoryMap w (3*k) j) :=
    h.2.2 _ (history_words_away w sign hn ho (3*k) (by omega) j).1
      (history_words_away w sign hn ho (3*k) (by omega) j).2
  rw [same 0,same 1,same 2,same 3,same 4,same 5]
  exact legal k hk

private theorem current_records (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (j : Nat) (hj : j < 170) (s : State) (m : List Bool)
    (legal : RawGroupLegal w 170 s.basis) :
    run (compressedHistoryEncode w (3*j)) m s = run (compressedHistoryEncode w (3*j)) [] s := by
  have a := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*j))
    (compressedHistoryMap_injective w hn (3*j) (by omega))
    (compressedHistoryMap_above w (3*j) (by omega) hlo) s m (legal j hj)
  have z := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*j))
    (compressedHistoryMap_injective w hn (3*j) (by omega))
    (compressedHistoryMap_above w (3*j) (by omega) hlo) s [] (legal j hj)
  apply State.extensionality
  · simpa only [compressedHistoryEncode] using a.1.trans z.1.symm
  · exact run_basis_records _ s s m [] rfl

/-- A real three-cell forward packet advances the fixed full170-prefix
encoding invariant, including the physical caller phase and all raw outsiders.
Only structural packet support is assumed; its semantic frame is instantiated
from the accepted actual field cells, not supplied as a circuit oracle. -/
theorem encoded_forward_packet_step (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (j : Nat) (hj : j < 170) (a c d : MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign eff [a,c,d])
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (legal : RawGroupLegal w 170 base) (X Y : Fp)
    (support : wires (rawForwardPacket w b sign eff a c d) ⊆ groupReadSites w b sign eff (3*j))
    (s : State) (m : List Bool) (input : EncodedFieldFrame w sign base X Y s) :
    let out := run (codecGroupForward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) [a,c,d]) m s
    out.phase = s.phase ∧ EncodedFieldFrame w sign base
      (skywalkPayloadReplay (mixedTranscriptControls base b [a,c,d]) (X,Y)).1
      (skywalkPayloadReplay (mixedTranscriptControls base b [a,c,d]) (X,Y)).2 out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have hs := hp sign (by simp)
  have leg := frame_history_legal w sign hn hs base raw.basis _ _ legal frame
  have factor := allGroupEncode_factor w pool hlo 170 j (by decide) hj raw
  have hE := otherGroupEncode_disjoint w pool hlo 170 j (by decide) hj
  have hB := otherGroupEncode_body_disjoint w b sign eff hn hlo
    (hp b (by simp)) hs (hp eff (by simp)) 170 j (by decide) hj _ support
  obtain ⟨rawOut,state,outPhase,outFrame⟩ := forward_packet w b sign eff (3*j) a c d hn hlo
    (by omega) hf ho base hg0 he0 env X Y raw frame (leg j hj)
    (otherGroupEncode w j 170) hE hB [] [] m
  have outLegal := frame_history_legal w sign hn hs base rawOut.basis _ _ legal outFrame
  have records := current_records w pool hlo j hj rawOut
    (m.drop (measurementCount (rawForwardPacket w b sign eff a c d))) outLegal
  rw [records] at state
  have back := allGroupEncode_factor w pool hlo 170 j (by decide) hj rawOut
  rw [←back] at state
  have actual : run (codecGroupForward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) [a,c,d]) m s =
      run (allGroupEncode w 170) [] rawOut := by
    rw [eq,factor]
    exact state
  dsimp only
  rw [actual]
  have encodedPhase := allGroupEncode_phase w pool hlo 170 (by decide) rawOut [] outLegal
  refine ⟨encodedPhase.trans (outPhase.trans phase),?_⟩
  refine ⟨rawOut,encodedPhase.symm,outFrame,rfl⟩

/-- Reverse packet counterpart under the same fixed full encoding. -/
theorem encoded_backward_packet_step (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (j : Nat) (hj : j < 170) (a c d : MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign eff [a,c,d])
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (legal : RawGroupLegal w 170 base) (X Y : Fp)
    (support : wires (rawBackwardPacket w b sign eff a c d) ⊆ groupReadSites w b sign eff (3*j))
    (s : State) (m : List Bool) (input : EncodedFieldFrame w sign base X Y s) :
    let out := run (codecGroupBackward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) [a,c,d]) m s
    out.phase = s.phase ∧ EncodedFieldFrame w sign base
      (skywalkPayloadReplayInverse (mixedTranscriptControls base b [a,c,d]) (X,Y)).1
      (skywalkPayloadReplayInverse (mixedTranscriptControls base b [a,c,d]) (X,Y)).2 out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have hs := hp sign (by simp)
  have leg := frame_history_legal w sign hn hs base raw.basis _ _ legal frame
  have factor := allGroupEncode_factor w pool hlo 170 j (by decide) hj raw
  have hE := otherGroupEncode_disjoint w pool hlo 170 j (by decide) hj
  have hB := otherGroupEncode_body_disjoint w b sign eff hn hlo
    (hp b (by simp)) hs (hp eff (by simp)) 170 j (by decide) hj _ support
  obtain ⟨rawOut,state,outPhase,outFrame⟩ := backward_packet w b sign eff (3*j) a c d hn hlo
    (by omega) hf ho base hg0 he0 env X Y raw frame (leg j hj)
    (otherGroupEncode w j 170) hE hB [] [] m
  have outLegal := frame_history_legal w sign hn hs base rawOut.basis _ _ legal outFrame
  have records := current_records w pool hlo j hj rawOut
    (m.drop (measurementCount (rawBackwardPacket w b sign eff a c d))) outLegal
  rw [records] at state
  have back := allGroupEncode_factor w pool hlo 170 j (by decide) hj rawOut
  rw [←back] at state
  have actual : run (codecGroupBackward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) [a,c,d]) m s =
      run (allGroupEncode w 170) [] rawOut := by
    rw [eq,factor]
    exact state
  dsimp only
  rw [actual]
  have encodedPhase := allGroupEncode_phase w pool hlo 170 (by decide) rawOut [] outLegal
  refine ⟨encodedPhase.trans (outPhase.trans phase),?_⟩
  refine ⟨rawOut,encodedPhase.symm,outFrame,rfl⟩

end ECDSAAdd.Arithmetic.CompressedFieldSupport
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.frame_history_legal
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.encoded_forward_packet_step

#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.encoded_backward_packet_step
