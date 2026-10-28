import ECDSAAdd.Arithmetic.MappedCompressedFieldPoolRestore
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode

theorem caller_encoder_pool_support (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) :
    wires (allGroupEncode base 170) ⊆ (skywalkPoolWires base).toFinset := by
  have history := compressedPrefix_history_support base (skywalkShared_integer_nodup base hn)
    hlo 512 (by decide)
  rw [encode_prefix_512] at history
  intro q hq
  have member := List.mem_toFinset.mp (history hq)
  simp only [List.mem_append,wireBlock] at member
  rcases member with member|member
  all_goals
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1] at hi ⊢
    exact ⟨i,by omega,rfl⟩

/-- The physical encoded frame retains the full target port and every
nonpool outsider. Codec gates remain confined to the integer pool. -/
theorem encodedCanonical_caller_frame (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (ha : regValue (skywalkSharedField base).a origin = 0)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame origin X 0 s) :
    regValue (skywalkSharedField base).z s.basis = X.val ∧
    ∀ q,q ∉ (skywalkSharedField base).z → q ∉ skywalkPoolWires base → s.basis q = origin q := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have narrow : PairFrame (skywalkSharedField base).z (skywalkSharedField base).a
      origin X.val 0 raw.basis := by simpa only [ZMod.val_zero] using rawFrame
  have keeps := arith_field_frame (skywalkSharedField base) origin raw.basis X.val ha narrow
  have support := caller_encoder_pool_support hn hlo
  have encoderAway (q : Wire) (hq : q ∉ skywalkPoolWires base) :
      (run (allGroupEncode base 170) [] raw).basis q = raw.basis q :=
    run_preserves_outside _ [] raw q (fun h => hq (List.mem_toFinset.mp (support h)))
  constructor
  · apply Eq.trans (regValue_congr _ _ _ ?_) narrow.1
    intro q hq
    rw [encoded]
    exact encoderAway q (fun hp => arith_pool_away_z base hn q hp hq)
  · intro q hz hp
    rw [encoded]
    exact (encoderAway q hp).trans (keeps q hz)

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.encodedCanonical_caller_frame
