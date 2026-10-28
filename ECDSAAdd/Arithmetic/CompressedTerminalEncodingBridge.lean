import ECDSAAdd.Arithmetic.CompressedFieldFullEncoding
import ECDSAAdd.Arithmetic.CompressedFieldEncodingFactor
import ECDSAAdd.Arithmetic.SkywalkArithmeticCore
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode otherGroupEncode
  compressedHistoryEncode compressedEncodePrefix skywalkArithmeticClear

/-- The actual physical compact terminal tape satisfies every codec's
three ternary predicates, without a sampled or shortened trace. -/
theorem compact_terminal_raw_legal (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (s : BasisState)
    (stage : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 s) :
    RawGroupLegal w 170 s := by
  intro j hj
  exact compressedCompactHistory_legal w hn x p 512 (3*j) hp0 hpo
    (by omega) (by decide) s stage

/-- Recover a complete-State raw witness from the actual encoded integer
postcondition. Its phase is chosen to match the caller, then justified by
record-independent encoder correctness on the derived legal tape. -/
theorem compressed_terminal_encoded_state (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1) (s : State)
    (stage : CompressedCompactStage w x p 512 s.basis) :
    ∃ raw : State,
      CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 raw.basis ∧
      RawGroupLegal w 170 raw.basis ∧ raw.phase=s.phase ∧
      s=run (allGroupEncode w 170) [] raw := by
  obtain ⟨ghost,compact,bits⟩ := stage
  let raw : State := {basis:=ghost.basis,phase:=s.phase}
  have legal := compact_terminal_raw_legal w hn x p hp0 hpo raw.basis compact
  have phase := allGroupEncode_phase w hn hlo 170 (by decide) raw [] legal
  have basis : s.basis=(run (allGroupEncode w 170) [] raw).basis := by
    rw [encode_prefix_512] at bits
    exact bits.trans (run_basis_records (allGroupEncode w 170) ghost raw [] [] rfl)
  refine ⟨raw,compact,legal,rfl,?_⟩
  apply State.extensionality
  · exact phase.symm
  · exact basis

private theorem full_encoder_member (w : Nat → Wire) (q : Wire)
    (h : q∈wires (allGroupEncode w 170)) :
    ∃j,j < 170 ∧ q∈wires (compressedHistoryEncode w (3*j)) := by
  rw [←otherGroupEncode_outside w 170 170 (Nat.le_refl _)] at h
  obtain ⟨j,hj,_,member⟩ := otherGroupEncode_member w 170 170 q h
  exact ⟨j,hj,member⟩

/-- The actual last orientation511 remains raw. The full encoder uses
only records0..509 and1028..1537; clear targets512 and770 are nonhistory. -/
theorem full_encoder_clear_disjoint (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w) :
    Disjoint (wires (allGroupEncode w 170)) (wires (skywalkArithmeticClear w)) := by
  apply Finset.disjoint_left.mpr
  intro q encoded clear
  obtain ⟨j,hj,member⟩ := full_encoder_member w q encoded
  obtain ⟨u,rfl⟩ := compressedHistory_gate_mem w hn hlo (3*j) (by omega)
    _ (Or.inl rfl) q member
  let idx := compressedHistoryId (3*j) u
  have range : idx < 510 ∨ (1028 ≤ idx ∧ idx < 1538) := by
    have hu := u.isLt
    unfold idx compressedHistoryId
    split_ifs <;> omega
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at clear
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at clear
  rcases clear with eq|eq|eq
  · have same := skywalkPool_index_inj w hn idx 511 (by omega) (by omega) eq
    omega
  · have same := skywalkPool_index_inj w hn idx 512 (by omega) (by omega) eq
    omega
  · have same := skywalkPool_index_inj w hn idx 770 (by omega) (by omega) eq
    omega

/-- Exact complete-State commutation includes every measurement correction
and arbitrary independent encoder/clear record streams and incoming phase. -/
theorem full_encoder_clear_commute (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (s : State) (m n : List Bool) :
    run (allGroupEncode w 170) m (run (skywalkArithmeticClear w) n s)=
      run (skywalkArithmeticClear w) n (run (allGroupEncode w 170) m s) :=
  run_disjoint_commute _ _ (full_encoder_clear_disjoint w hn hlo) m n s

/-- The actual clear therefore retains a legal ghost encoding relation.
This bridge asserts no field Env before caller work and ports are prepared. -/
theorem compressed_terminal_clear_encoding (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1) (s : State)
    (stage : CompressedCompactStage w x p 512 s.basis) (m : List Bool) :
    ∃ raw : State,
      CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 raw.basis ∧
      RawGroupLegal w 170 raw.basis ∧ raw.phase=s.phase ∧
      run (skywalkArithmeticClear w) m s=
        run (allGroupEncode w 170) [] (run (skywalkArithmeticClear w) m raw) := by
  obtain ⟨raw,compact,legal,phase,encoded⟩ :=
    compressed_terminal_encoded_state w hn hlo x p hp0 hpo s stage
  refine ⟨raw,compact,legal,phase,?_⟩
  rw [encoded]
  exact (full_encoder_clear_commute w hn hlo raw [] m).symm

end ECDSAAdd.Arithmetic.CompressedFieldSupport
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.compact_terminal_raw_legal
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.compressed_terminal_encoded_state
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.full_encoder_clear_commute
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.compressed_terminal_clear_encoding
