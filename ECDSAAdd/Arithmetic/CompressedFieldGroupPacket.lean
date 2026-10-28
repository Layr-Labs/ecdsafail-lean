import ECDSAAdd.Arithmetic.CompressedFieldWindowTransport
import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalReplay
import ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonicalReplay
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell

def rawForwardPacket (w : Nat → Wire) (b sign eff : Wire) (a c d : MixedTranscriptLetter) : Program :=
  OffsetBorrowedCanonical.replay w b sign eff [a,c,d]
def rawBackwardPacket (w : Nat → Wire) (b sign eff : Wire) (a c d : MixedTranscriptLetter) : Program :=
  OffsetBorrowedInverseCanonical.replay w b sign eff [a,c,d]

private theorem forward_layout (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (a c d : MixedTranscriptLetter) :
    codecGroupForward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) start [a,c,d] =
    compressedHistoryDecode w start++rawForwardPacket w b sign eff a c d++compressedHistoryEncode w start := by
  simp only [codecGroupForward,rawForwardPacket,OffsetBorrowedCanonical.replay,List.append_nil,List.append_assoc]

private theorem backward_layout (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (a c d : MixedTranscriptLetter) :
    codecGroupBackward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) start [a,c,d] =
    compressedHistoryDecode w start++rawBackwardPacket w b sign eff a c d++compressedHistoryEncode w start := by
  simp only [codecGroupBackward,rawBackwardPacket,OffsetBorrowedInverseCanonical.replay,
    List.nil_append,List.append_assoc]

/-- Exact emitted decode/body/re-encode evaluation. Decoder consumes no
record, and each actual body and encoder receives its own record suffix. -/
private theorem window_run (w : Nat → Wire) (start : Nat) (body : Program) (s : State) (m : List Bool) :
    run (compressedHistoryDecode w start++body++compressedHistoryEncode w start) m s =
      run (compressedHistoryEncode w start) (m.drop (measurementCount body))
        (run body m (run (compressedHistoryDecode w start) [] s)) := by
  have zero := (compressedHistory_counts w start).2.2.2
  simp only [List.append_assoc]
  rw [run_append,zero,List.take_zero,List.drop_zero,run_append,run_take]

/-- Actual forward three-cell semantic packet under other encoded history.
The result carries complete State encoding and the old full field frame;
no raw PairFrame is assumed for the physical other-encoded input. -/
theorem forward_packet (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (a c d : MixedTranscriptLetter) (hn : (skywalkSharedWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (hs : start+3 ≤ 512)
    (hf : MixedTranscriptReplayLayout w b sign eff [a,c,d])
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (X Y : Fp) (s : State)
    (input : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis)
    (legal : (s.basis (compressedHistoryMap w start 0) && s.basis (compressedHistoryMap w start 1)) = false ∧
      (s.basis (compressedHistoryMap w start 2) && s.basis (compressedHistoryMap w start 3)) = false ∧
      (s.basis (compressedHistoryMap w start 4) && s.basis (compressedHistoryMap w start 5)) = false)
    (other : Program)
    (hE : Disjoint (wires other) (wires (compressedHistoryEncode w start)))
    (hB : Disjoint (wires other) (wires (rawForwardPacket w b sign eff a c d)))
    (mOther mInit m : List Bool) :
    ∃ rawOut : State,
      run (codecGroupForward w (fun l : MixedTranscriptLetter =>
        OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) start [a,c,d]) m
        (run other mOther (run (compressedHistoryEncode w start) mInit s)) =
      run other mOther (run (compressedHistoryEncode w start)
        (m.drop (measurementCount (rawForwardPacket w b sign eff a c d))) rawOut) ∧
      rawOut.phase = s.phase ∧
      PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls base b [a,c,d]) (X,Y)).1)
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls base b [a,c,d]) (X,Y)).2) rawOut.basis := by
  let body := rawForwardPacket w b sign eff a c d
  let rawOut := run body m s
  have raw := OffsetBorrowedCanonical.replay_frame w b sign eff hn [a,c,d] hf ho base hg0 he0 env X Y s m input
  have transport := window_transport_other w start (skywalkShared_integer_nodup w hn) hlo hs
    other body hE hB s mOther mInit [] m (m.drop (measurementCount body)) legal
  refine ⟨rawOut,?_,raw.1,raw.2⟩
  rw [forward_layout,window_run]
  exact transport

/-- Independently measured inverse packet executes the three inverse cells
in reverse order, retaining the same complete encoded State relation. -/
theorem backward_packet (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (a c d : MixedTranscriptLetter) (hn : (skywalkSharedWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (hs : start+3 ≤ 512)
    (hf : MixedTranscriptReplayLayout w b sign eff [a,c,d])
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (X Y : Fp) (s : State)
    (input : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis)
    (legal : (s.basis (compressedHistoryMap w start 0) && s.basis (compressedHistoryMap w start 1)) = false ∧
      (s.basis (compressedHistoryMap w start 2) && s.basis (compressedHistoryMap w start 3)) = false ∧
      (s.basis (compressedHistoryMap w start 4) && s.basis (compressedHistoryMap w start 5)) = false)
    (other : Program)
    (hE : Disjoint (wires other) (wires (compressedHistoryEncode w start)))
    (hB : Disjoint (wires other) (wires (rawBackwardPacket w b sign eff a c d)))
    (mOther mInit m : List Bool) :
    ∃ rawOut : State,
      run (codecGroupBackward w (fun l : MixedTranscriptLetter =>
        OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) start [a,c,d]) m
        (run other mOther (run (compressedHistoryEncode w start) mInit s)) =
      run other mOther (run (compressedHistoryEncode w start)
        (m.drop (measurementCount (rawBackwardPacket w b sign eff a c d))) rawOut) ∧
      rawOut.phase = s.phase ∧
      PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadReplayInverse (mixedTranscriptControls base b [a,c,d]) (X,Y)).1)
        (centerWord (skywalkPayloadReplayInverse (mixedTranscriptControls base b [a,c,d]) (X,Y)).2) rawOut.basis := by
  let body := rawBackwardPacket w b sign eff a c d
  let rawOut := run body m s
  have raw := OffsetBorrowedInverseCanonical.replay_frame w b sign eff hn [a,c,d] hf ho base hg0 he0 env X Y s m input
  have transport := window_transport_other w start (skywalkShared_integer_nodup w hn) hlo hs
    other body hE hB s mOther mInit [] m (m.drop (measurementCount body)) legal
  refine ⟨rawOut,?_,raw.1,raw.2⟩
  rw [backward_layout,window_run]
  exact transport

end ECDSAAdd.Arithmetic.CompressedFieldSupport
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.forward_packet
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.backward_packet
