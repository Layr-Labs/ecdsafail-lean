import ECDSAAdd.Arithmetic.CompressedFieldGroupPacket
import ECDSAAdd.Arithmetic.CompressedCompactMaskZeros
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run compressedHistoryEncode

def allGroupEncode (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => allGroupEncode w n++compressedHistoryEncode w (3*n)

/-- All legal raw groups, without any sampled or approximate tape domain. -/
def RawGroupLegal (w : Nat → Wire) (n : Nat) (s : BasisState) : Prop :=
  ∀ j,j < n →
    (s (compressedHistoryMap w (3*j) 0) && s (compressedHistoryMap w (3*j) 1)) = false ∧
    (s (compressedHistoryMap w (3*j) 2) && s (compressedHistoryMap w (3*j) 3)) = false ∧
    (s (compressedHistoryMap w (3*j) 4) && s (compressedHistoryMap w (3*j) 5)) = false

/-- This is the physical invariant: raw field frame under the fixed full
170-group encoding. It never asserts a raw frame on an encoded history. -/
def EncodedFieldFrame (w : Nat → Wire) (sign : Wire) (base : BasisState)
    (X Y : Fp) (s : State) : Prop :=
  ∃ raw : State,
    raw.phase = s.phase ∧
    PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) raw.basis ∧
    s = run (allGroupEncode w 170) [] raw

private theorem due1 (n : Nat) : compressedPackDue (3*n+1) = false := by
  simp [compressedPackDue,Nat.add_mod]
private theorem due2 (n : Nat) : compressedPackDue (3*n+2) = false := by
  simp [compressedPackDue,Nat.add_mod]
private theorem due3 (n : Nat) : compressedPackDue (3*n+3) = true := by
  simp [compressedPackDue]

/-- The fixed full encoding is exactly the existing delayed integer prefix. -/
theorem encode_prefix_index (w : Nat → Wire) (n : Nat) :
    compressedEncodePrefix w (3*n+1) = allGroupEncode w n := by
  induction n with
  | zero => simp [compressedEncodePrefix,compressedPackAfter,compressedPackDue,allGroupEncode]
  | succ n ih =>
    have index : 3*(n+1)+1 = ((3*n+1)+1)+1+1 := by omega
    rw [index,compressedEncodePrefix,compressedEncodePrefix,compressedEncodePrefix,ih]
    have d1 := due1 n
    have d2 := due2 n
    have d3 := due3 n
    have h2 : 3*n+1+1 = 3*n+2 := by omega
    have h3 : 3*n+1+1+1 = 3*n+3 := by omega
    rw [h2,h3]
    simp only [compressedPackAfter,d1,d2,d3,Bool.false_eq_true,if_false,if_true,List.append_nil]
    rw [show 3*n+3-3 = 3*n by omega]
    rfl

theorem encode_prefix_512 (w : Nat → Wire) :
    compressedEncodePrefix w 512 = allGroupEncode w 170 := by
  rw [show (512:Nat) = 511+1 from rfl,compressedEncodePrefix]
  rw [show (511:Nat) = 3*170+1 from rfl,encode_prefix_index]
  simp [compressedPackAfter,compressedPackDue]

theorem allGroupEncode_disjoint (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n j : Nat) (bound : 3*n ≤ 512) (outside : n ≤ j) (jb : 3*j+3 ≤ 512) :
    Disjoint (wires (allGroupEncode w n)) (wires (compressedHistoryEncode w (3*j))) := by
  induction n with
  | zero => simp [allGroupEncode,wires]
  | succ n ih =>
    have old := ih (by omega) (by omega)
    have now := compressedHistory_windows_disjoint w hn hlo (3*n) (3*j) (by omega) jb (by omega)
    simp only [allGroupEncode,wires_append,Finset.disjoint_union_left]
    exact ⟨old,now⟩

/-- Every encoder keeps its record-independent complete State on this
legal domain, including phase; all other groups are disjoint actual programs. -/
theorem allGroupEncode_phase (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n : Nat) (bound : 3*n ≤ 512) (s : State) (m : List Bool)
    (legal : RawGroupLegal w n s.basis) :
    (run (allGroupEncode w n) m s).phase = s.phase := by
  induction n generalizing m with
  | zero => simp only [allGroupEncode,run]
  | succ n ih =>
    let before := run (allGroupEncode w n) (m.take (measurementCount (allGroupEncode w n))) s
    have first := ih (by omega)
      (m.take (measurementCount (allGroupEncode w n))) (fun j hj => legal j (by omega))
    have dis := allGroupEncode_disjoint w hn hlo n n (by omega) (Nat.le_refl _) (by omega)
    have same (j : Fin 6) : before.basis (compressedHistoryMap w (3*n) j) =
        s.basis (compressedHistoryMap w (3*n) j) := by
      apply run_preserves_outside
      intro h
      exact Finset.disjoint_left.mp dis h (compressedHistory_site_mem w hn hlo (3*n) (by omega) j)
    have dom := legal n (by omega)
    have domBefore :
        (before.basis (compressedHistoryMap w (3*n) 0) && before.basis (compressedHistoryMap w (3*n) 1)) = false ∧
        (before.basis (compressedHistoryMap w (3*n) 2) && before.basis (compressedHistoryMap w (3*n) 3)) = false ∧
        (before.basis (compressedHistoryMap w (3*n) 4) && before.basis (compressedHistoryMap w (3*n) 5)) = false := by
      rw [same 0,same 1,same 2,same 3,same 4,same 5]
      exact dom
    have codec := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*n))
      (compressedHistoryMap_injective w hn (3*n) (by omega))
      (compressedHistoryMap_above w (3*n) (by omega) hlo) before
      (m.drop (measurementCount (allGroupEncode w n))) domBefore
    rw [allGroupEncode,run_append]
    simpa only [compressedHistoryEncode,before] using codec.1.trans first

theorem allGroupEncode_records (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n : Nat) (bound : 3*n ≤ 512) (s : State) (m k : List Bool)
    (legal : RawGroupLegal w n s.basis) :
    run (allGroupEncode w n) m s = run (allGroupEncode w n) k s := by
  apply State.extensionality
  · exact (allGroupEncode_phase w hn hlo n bound s m legal).trans
      (allGroupEncode_phase w hn hlo n bound s k legal).symm
  · exact run_basis_records _ s s m k rfl

end ECDSAAdd.Arithmetic.CompressedFieldSupport
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.encode_prefix_512
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.allGroupEncode_phase
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.allGroupEncode_records
