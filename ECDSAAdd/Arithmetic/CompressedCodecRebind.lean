import ECDSAAdd.Framework.CleanWireRebind
import ECDSAAdd.Arithmetic.TranscriptCodecPlacement

namespace ECDSAAdd.Arithmetic

/-- The actual three-trit codec supplies a universally clean physical site.
A second clean site outside the codec may exchange its allocation with that
site before the next instruction block. Every record and phase is included. -/
theorem compressedCodec_rebind_next (w : Fin 6 → Wire)
    (hw : Function.Injective w) (hlo : ∀ i, 6 ≤ w i)
    (f : Wire → Wire) (hf : Function.Injective f) (actual raw : State)
    (hmap : pullState f actual = raw) (spare : Wire)
    (hspare : raw.basis spare = false)
    (hout : spare ∉ wires (TranscriptCodec3.encode w))
    (legal : (raw.basis (w 0) && raw.basis (w 1)) = false ∧
      (raw.basis (w 2) && raw.basis (w 3)) = false ∧
      (raw.basis (w 4) && raw.basis (w 5)) = false)
    (next : Program) (mEncode mNext : List Bool) :
    pullState (f ∘ Equiv.swap (w 3) spare)
      (run (renameProgram (f ∘ Equiv.swap (w 3) spare) next) mNext
        (run (renameProgram f (TranscriptCodec3.encode w)) mEncode actual)) =
      run next mNext (run (TranscriptCodec3.encode w) mEncode raw) := by
  have codec := TranscriptCodec3.placement_correct w hw hlo raw mEncode legal
  have keep := run_preserves_outside (TranscriptCodec3.encode w) mEncode raw spare hout
  have cleanSpare : (run (TranscriptCodec3.encode w) mEncode raw).basis spare = false :=
    keep.trans hspare
  exact twoBlocks_cleanWireRebind f hf (TranscriptCodec3.encode w) next
    mEncode mNext actual raw (w 3) spare hmap codec.2.1 cleanSpare

/-- Counts include the actual encoder and its measured phase correction.
There is no extra Toffoli or measurement for the public zero-only rebind. -/
theorem compressedCodec_rebind_counts (w : Fin 6 → Wire) (f : Wire → Wire)
    (spare : Wire) (next : Program) :
    toffoliCount (renameProgram f (TranscriptCodec3.encode w) ++
      renameProgram (f ∘ Equiv.swap (w 3) spare) next) = toffoliCount next + 3 ∧
    measurementCount (renameProgram f (TranscriptCodec3.encode w) ++
      renameProgram (f ∘ Equiv.swap (w 3) spare) next) = measurementCount next + 1 := by
  have first := renameProgram_counts f (TranscriptCodec3.encode w)
  have second := cleanWireRebind_counts f (w 3) spare next
  have codec := TranscriptCodec3.placement_counts w
  rw [toffoliCount_append,measurementCount_append,first.1,first.2,second.1,second.2,
    codec.1,codec.2.1]
  constructor <;> omega

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compressedCodec_rebind_next
#print axioms ECDSAAdd.Arithmetic.compressedCodec_rebind_counts
