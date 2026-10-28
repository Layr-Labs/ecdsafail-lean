import ECDSAAdd.Arithmetic.EntryFieldSeedCancellation
import ECDSAAdd.Arithmetic.CompressedFieldInvariantStep

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Arithmetic.EntrySelectedSwapFrame
open Secp256k1 BalancedField CompressedFieldSupport
attribute [local irreducible] run transcriptSelectWindow swapRegisters

private theorem swap_pair (r y : List Wire) (flag : Wire) (len : r.length=y.length)
    (nd : (flag::r++y).Nodup) (origin : BasisState) (X Y : Nat) :
    Triple (PairFrame r y origin X Y) (swapRegisters flag r y)
      (PairFrame r y origin (if origin flag then Y else X) (if origin flag then X else Y)) := by
  intro s m input
  have out := swapRegisters_correct flag r y len nd s m
  have away := (List.nodup_cons.mp nd).1
  have same := input.2.2 flag (fun h => away (List.mem_append_left _ h))
    (fun h => away (List.mem_append_right _ h))
  refine ⟨out.1,?_,?_,fun q qr qy => (out.2.1 q qr qy).trans (input.2.2 q qr qy)⟩
  · rw [out.2.2.1,same,input.1,input.2.1]
  · rw [out.2.2.2,same,input.1,input.2.1]

/-- Retains the quantum activation control and the actual recorded S bit. -/
theorem selectedSwap_frame (w : Nat → Wire) (b g swap sign effS : Wire) (is : Bool)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (origin : BasisState) (hs0 : origin effS=false) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
      (centerWord X) (centerWord Y))
      (EntryFieldSeedCancellation.selectedSwap w b swap sign effS is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
        (centerWord (if mixedTranscriptBit origin b swap is then Y else X))
        (centerWord (if mixedTranscriptBit origin b swap is then X else Y))) := by
  have controls := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at controls
  have nd : [b,swap,effS].Nodup := by simp [List.nodup_cons]; tauto
  have width := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have body := swap_pair _ _ effS (width.2.1.trans width.2.2.1.symm) hl.swapND
    (mixedTranscriptBase origin b swap effS is) (centerWord X) (centerWord Y)
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at body
  have body' : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      (mixedTranscriptBase origin b swap effS is) (centerWord X) (centerWord Y))
      (swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        (mixedTranscriptBase origin b swap effS is)
        (centerWord (if mixedTranscriptBit origin b swap is then Y else X))
        (centerWord (if mixedTranscriptBit origin b swap is then X else Y))) := by
    cases bit : mixedTranscriptBit origin b swap is <;>
      simpa only [mixedTranscriptBase,writeBit,bit,if_true,if_false,Bool.false_eq_true] using body
  exact transcriptSelectWindow_pairFrame b swap effS is _ _ nd (hl.outside b (by simp))
    (hl.outside swap (by simp)) (hl.outside effS (by simp)) origin hs0 _ _ _ _ _ body'

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

/-- Generic codec conjugacy. The body frame is a reusable Hoare theorem;
all history legality and allocation boundaries still follow from the frame. -/
theorem encoded_window_step (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (j : Nat) (hj : j < 170) (origin : BasisState) (legal : RawGroupLegal w 170 origin)
    (X Y A B : Fp) (body : Program)
    (support : wires body ⊆ groupReadSites w b sign eff (3*j))
    (correct : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord X) (centerWord Y)) body
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame w sign origin X Y s) :
    let out := run (compressedHistoryDecode w (3*j)++body++compressedHistoryEncode w (3*j)) m s
    out.phase=s.phase ∧ EncodedFieldFrame w sign origin A B out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have hs := hp sign (by simp)
  have leg := frame_history_legal w sign hn hs origin raw.basis _ _ legal frame
  have factor := allGroupEncode_factor w pool hlo 170 j (by decide) hj raw
  have hE := otherGroupEncode_disjoint w pool hlo 170 j (by decide) hj
  have hB := otherGroupEncode_body_disjoint w b sign eff hn hlo
    (hp b (by simp)) hs (hp eff (by simp)) 170 j (by decide) hj body support
  let rawOut := run body m raw
  have result := correct raw m frame
  have outLegal := frame_history_legal w sign hn hs origin rawOut.basis _ _ legal result.2
  have transport := window_transport_other w (3*j) pool hlo (by omega)
    (otherGroupEncode w j 170) body hE hB raw [] [] [] m
    (m.drop (measurementCount body)) (leg j hj)
  rw [current_records w pool hlo j hj rawOut _ outLegal] at transport
  have back := allGroupEncode_factor w pool hlo 170 j (by decide) hj rawOut
  rw [←back] at transport
  have actual : run (compressedHistoryDecode w (3*j)++body++compressedHistoryEncode w (3*j)) m s =
      run (allGroupEncode w 170) [] rawOut := by
    rw [eq,factor]
    have zero := (compressedHistory_counts w (3*j)).2.2.2
    simp only [List.append_assoc]
    rw [run_append,zero,List.take_zero,List.drop_zero,run_append,run_take]
    exact transport
  dsimp only
  rw [actual]
  have encPhase := allGroupEncode_phase w pool hlo 170 (by decide) rawOut [] outLegal
  exact ⟨encPhase.trans (result.1.trans phase),rawOut,encPhase.symm,result.2,rfl⟩

end ECDSAAdd.Arithmetic.EntrySelectedSwapFrame
#print axioms ECDSAAdd.Arithmetic.EntrySelectedSwapFrame.selectedSwap_frame
#print axioms ECDSAAdd.Arithmetic.EntrySelectedSwapFrame.encoded_window_step
