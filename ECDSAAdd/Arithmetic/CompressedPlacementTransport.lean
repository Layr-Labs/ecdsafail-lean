import ECDSAAdd.Arithmetic.MappedCompressedCodecAgreement
import ECDSAAdd.Framework.WireRenameComposition
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic.MappedCompressed

/-- Extend a logical permutation above the sixteen reserved labels. -/
def shiftedFn (e : Equiv.Perm Nat) (q : Nat) : Nat :=
  if q < 16 then q else e (q-16)+16

theorem shiftedFn_base (e : Equiv.Perm Nat) (q : Nat) :
    shiftedFn e (base q)=base (e q) := by
  simp [shiftedFn,base]

private theorem shifted_inverse (e : Equiv.Perm Nat) (q : Nat) :
    shiftedFn e.symm (shiftedFn e q)=q := by
  by_cases h : q < 16
  · simp [shiftedFn,h]
  · have bound : ¬e (q-16)+16 < 16 := by omega
    simp only [shiftedFn,if_neg h,if_neg bound,Nat.add_sub_cancel,
      e.symm_apply_apply]
    omega

def shifted (e : Equiv.Perm Nat) : Equiv.Perm Nat :=
  { toFun := shiftedFn e, invFun := shiftedFn e.symm,
    left_inv := shifted_inverse e, right_inv := shifted_inverse e.symm }

theorem shifted_base (e : Equiv.Perm Nat) (q : Nat) :
    shifted e (base q)=base (e q) := shiftedFn_base e q

/-- Natural relabeling includes every measurement correction in the codec. -/
theorem codec_rename (f : Wire → Wire) (w : Fin 6 → Wire)
    (hn : Function.Injective w) (hw : ∀i,6 ≤ w i)
    (hf : Function.Injective (f ∘ w)) (hfw : ∀i,6 ≤ f (w i)) :
    renameProgram f (TranscriptCodec3.encode w)=TranscriptCodec3.encode (f ∘ w) ∧
    renameProgram f (TranscriptCodec3.decode w)=TranscriptCodec3.decode (f ∘ w) := by
  have onSupport (q : Nat) (hq : q∈Finset.range 6) :
      (f ∘ TranscriptCodec3.placement w) q=TranscriptCodec3.placement (f ∘ w) q := by
    have lt := Finset.mem_range.mp hq
    have a := TranscriptCodec3.placement_apply w hn hw ⟨q,lt⟩
    have b := TranscriptCodec3.placement_apply (f ∘ w) hf hfw ⟨q,lt⟩
    exact (congrArg f a).trans b.symm
  constructor
  · unfold TranscriptCodec3.encode
    rw [renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    exact onSupport q (TranscriptCodec3.support.1 ▸ hq)
  · unfold TranscriptCodec3.decode
    rw [renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    exact onSupport q (TranscriptCodec3.support.2 ▸ hq)

theorem shifted_current_codec (j : Nat) (hj : j < 170) :
    renameProgram (shifted (CompressedAllocation.pi j))
        (compressedHistoryEncode base (3*j))=compressedHistoryEncode (placed j) (3*j) ∧
    renameProgram (shifted (CompressedAllocation.pi j))
        (compressedHistoryDecode base (3*j))=compressedHistoryDecode (placed j) (3*j) := by
  have maps : shifted (CompressedAllocation.pi j) ∘ compressedHistoryMap base (3*j)=
      compressedHistoryMap (placed j) (3*j) := by
    funext u
    exact shifted_base _ _
  have hn := compressedHistoryMap_injective base
    (List.Nodup.map base_injective List.nodup_range') (3*j) (by omega)
  have highBase : CompressedHistoryAbove base := by
    intro q _
    change 6 ≤ q+16
    omega
  have hw := compressedHistoryMap_above base (3*j) (by omega) highBase
  have hf : Function.Injective
      (shifted (CompressedAllocation.pi j) ∘ compressedHistoryMap base (3*j)) :=
    (shifted _).injective.comp hn
  have high : ∀u,6 ≤ shifted (CompressedAllocation.pi j) (compressedHistoryMap base (3*j) u) := by
    intro u
    rw [show shifted (CompressedAllocation.pi j) (compressedHistoryMap base (3*j) u)=
      compressedHistoryMap (placed j) (3*j) u from congrFun maps u]
    exact compressedHistoryMap_above (placed j) (3*j) (by omega) (placed_above j) u
  have result := codec_rename (shifted (CompressedAllocation.pi j))
    (compressedHistoryMap base (3*j)) hn hw hf high
  simpa only [compressedHistoryEncode,compressedHistoryDecode,maps] using result

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.shifted_current_codec
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.codec_rename
