import ECDSAAdd.Arithmetic.CompressedFieldTapeAlignment
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires allGroupEncode otherGroupEncode compressedHistoryEncode
attribute [local irreducible] OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
attribute [local irreducible] OffsetBorrowedCanonical.replay OffsetBorrowedInverseCanonical.replay

def directionalReplay (reverse : Bool) (w : Nat → Wire) (b sign eff : Wire)
    (ls : List MixedTranscriptLetter) : Program :=
  if reverse then OffsetBorrowedInverseCanonical.replay w b sign eff ls
  else OffsetBorrowedCanonical.replay w b sign eff ls

attribute [local irreducible] directionalReplay

def directionalPayload (reverse : Bool) (controls : List (Bool×Bool)) (xy : Fp×Fp) : Fp×Fp :=
  if reverse then skywalkPayloadReplayInverse controls xy else skywalkPayloadReplay controls xy

private theorem encoder_member (w : Nat → Wire) (q : Wire)
    (h : q ∈ wires (allGroupEncode w 170)) :
    ∃ k,k < 170 ∧ q ∈ wires (compressedHistoryEncode w (3*k)) := by
  rw [←otherGroupEncode_outside w 170 170 (Nat.le_refl _)] at h
  obtain ⟨k,hk,_,hm⟩ := otherGroupEncode_member w 170 170 q h
  exact ⟨k,hk,hm⟩

private theorem tail_cell_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (i : Nat) (hloi : 510 ≤ i) (hii : i < 512) (ig is : Bool) :
    Disjoint (wires (allGroupEncode w 170))
      (wires (OffsetBorrowedCanonical.cell w b (w i) (w (1028+i)) sign eff ig is)) ∧
    Disjoint (wires (allGroupEncode w 170))
      (wires (OffsetBorrowedInverseCanonical.cell w b (w i) (w (1028+i)) sign eff ig is)) := by
  let W := (sharedSites w sign).toFinset ∪ {b,eff,w i,w (1028+i)}
  have support := cells_active w b (w i) (w (1028+i)) sign eff ig is W
    (fun _ h => Finset.mem_union_left _ h) (by simp [W]) (by simp [W]) (by simp [W]) (by simp [W])
  have dis : Disjoint (wires (allGroupEncode w 170)) W := by
    apply Finset.disjoint_left.mpr
    intro q hq hW
    obtain ⟨k,hk,hm⟩ := encoder_member w q hq
    obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w (skywalkShared_integer_nodup w hn) hlo
      (3*k) (by omega) _ (Or.inl rfl) q hm
    let idx := compressedHistoryId (3*k) j
    have bound : idx < 1798 := compressedHistoryId_bound (3*k) (by omega) j
    have own : w idx ∈ skywalkPoolWires w := by
      simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
      exact ⟨idx,by omega,rfl⟩
    have active := history_active_away w sign hn (hp sign (by simp)) (3*k) (by omega) j
    have ng : w idx ≠ w i := by
      intro e
      have eq := skywalkShared_index_inj w hn idx i (by omega) (by omega) e
      have hj := j.isLt
      unfold idx compressedHistoryId at eq
      split_ifs at eq <;> omega
    have ns : w idx ≠ w (1028+i) := by
      intro e
      have eq := skywalkShared_index_inj w hn idx (1028+i) (by omega) (by omega) e
      have hj := j.isLt
      unfold idx compressedHistoryId at eq
      split_ifs at eq <;> omega
    simp only [W,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hW
    rcases hW with h|h|h|h|h
    · exact active (List.mem_toFinset.mp h)
    · exact hp b (by simp) (h ▸ own)
    · exact hp eff (by simp) (h ▸ own)
    · exact ng h
    · exact ns h
  exact ⟨dis.mono_right support.1,dis.mono_right support.2⟩

theorem tail_replay_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (i : Nat) (ls : List MixedTranscriptLetter) (start : 510 ≤ i)
    (bound : i+ls.length ≤ 512) (aligned : IndexedLetters w i ls) :
    Disjoint (wires (allGroupEncode w 170)) (wires (OffsetBorrowedCanonical.replay w b sign eff ls)) ∧
    Disjoint (wires (allGroupEncode w 170)) (wires (OffsetBorrowedInverseCanonical.replay w b sign eff ls)) := by
  induction ls generalizing i with
  | nil => simp [OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,wires]
  | cons l ls ih =>
    have first := tail_cell_disjoint w b sign eff hn hlo hp i start (by simp at bound; omega) l.2.1 l.2.2
    have rest := ih (i+1) (by omega) (by simp at bound; omega) aligned.2
    have control := aligned.1
    simp only [OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,
      wires_append,Finset.disjoint_union_right]
    rw [control]
    exact ⟨⟨first.1,rest.1⟩,⟨rest.2,first.2⟩⟩

/-- The final two original letters stay raw while the complete170 earlier
groups stay encoded. Both directions preserve the full encoding invariant. -/
theorem encoded_tail_replay (reverse : Bool) (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (i : Nat) (ls : List MixedTranscriptLetter) (start : 510 ≤ i)
    (bound : i+ls.length ≤ 512) (aligned : IndexedLetters w i ls)
    (hf : MixedTranscriptReplayLayout w b sign eff ls)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (legal : RawGroupLegal w 170 base) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame w sign base X Y s) :
    let out := run (directionalReplay reverse w b sign eff ls) m s
    out.phase = s.phase ∧ EncodedFieldFrame w sign base
      (directionalPayload reverse (mixedTranscriptControls base b ls) (X,Y)).1
      (directionalPayload reverse (mixedTranscriptControls base b ls) (X,Y)).2 out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have ds := tail_replay_disjoint w b sign eff hn hlo hp i ls start bound aligned
  have dis : Disjoint (wires (allGroupEncode w 170)) (wires (directionalReplay reverse w b sign eff ls)) := by
    cases reverse <;> simp only [directionalReplay,Bool.false_eq_true,if_false,if_true]
    · exact ds.1
    · exact ds.2
  have rr : (run (directionalReplay reverse w b sign eff ls) m raw).phase = raw.phase ∧
      PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (directionalPayload reverse (mixedTranscriptControls base b ls) (X,Y)).1)
        (centerWord (directionalPayload reverse (mixedTranscriptControls base b ls) (X,Y)).2)
        (run (directionalReplay reverse w b sign eff ls) m raw).basis := by
    cases reverse <;> simp only [directionalReplay,directionalPayload,Bool.false_eq_true,if_false,if_true]
    · exact OffsetBorrowedCanonical.replay_frame w b sign eff hn ls hf ho base hg0 he0 env X Y raw m frame
    · exact OffsetBorrowedInverseCanonical.replay_frame w b sign eff hn ls hf ho base hg0 he0 env X Y raw m frame
  let rawOut := run (directionalReplay reverse w b sign eff ls) m raw
  have leg := frame_history_legal w sign hn (hp sign (by simp)) base rawOut.basis _ _ legal rr.2
  have commute := (run_disjoint_commute (allGroupEncode w 170)
    (directionalReplay reverse w b sign eff ls) dis [] m raw).symm
  have actual : run (directionalReplay reverse w b sign eff ls) m s =
      run (allGroupEncode w 170) [] rawOut := by
    rw [eq,commute]
  dsimp only
  rw [actual]
  have p := allGroupEncode_phase w (skywalkShared_integer_nodup w hn) hlo 170 (by decide) rawOut [] leg
  exact ⟨p.trans (rr.1.trans phase),⟨rawOut,p.symm,rr.2,rfl⟩⟩

end ECDSAAdd.Arithmetic.CompressedFieldSupport
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.tail_replay_disjoint
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.encoded_tail_replay
