import ECDSAAdd.Arithmetic.DirectSkywalkFieldSupport
import ECDSAAdd.Arithmetic.MixedTranscriptMultiplication
import ECDSAAdd.Arithmetic.BalancedSharedFieldSupport
import ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupportKernel

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace ECDSAAdd.Arithmetic.DirectSupport
open Secp256k1 DirectSkywalk
attribute [local irreducible] wireBlock dblInPlace halfInPlace copyRegister
attribute [local irreducible] skywalkSeed skywalkUnseed narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop
attribute [local irreducible] mixedTranscriptFieldDivision mixedTranscriptFieldMultiplication
attribute [local irreducible] mixedTranscriptReplay mixedTranscriptInverseReplay

theorem unary (w : Nat → Wire) (W : Finset Wire) (hW : (skywalkSharedWires w).toFinset⊆W) :
    wires (dblInPlace (skywalkSharedField w).unary p)⊆W ∧
    wires (halfInPlace (skywalkSharedField w).unary p)⊆W := by
  have hw := skywalkShared_field_widths w
  have hu := modUnary_wires (skywalkSharedField w).unary 256 p
    ((skywalkSharedField w).unary_widths 256 hw) (by omega)
  constructor
  · rw [hu.1]
    intro q hq
    apply hW
    apply List.mem_toFinset.mpr
    apply retained_field_subset_shared w
    simp only [List.mem_toFinset,List.mem_append,ModInPlaceLayout.wires,
      ModInPlaceLayout.work,ModInPlaceLayout.unary,ModUnaryLayout.z,
      ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,
      ModInPlaceLayout.z] at hq ⊢
    tauto
  · rw [hu.2]
    intro q hq
    apply hW
    apply List.mem_toFinset.mpr
    apply retained_field_subset_shared w
    simp only [List.mem_toFinset,List.mem_append,ModInPlaceLayout.wires,
      ModInPlaceLayout.work,ModInPlaceLayout.unary,ModUnaryLayout.z,
      ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,
      ModInPlaceLayout.z] at hq ⊢
    tauto

theorem copy (w : Nat → Wire) (W : Finset Wire) (hW : (skywalkSharedWires w).toFinset⊆W) :
    wires (copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a)⊆W := by
  have hw := skywalkShared_field_widths w
  have hlen : (skywalkSharedField w).z.length=(skywalkSharedField w).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  rw [copyRegister_wires none (skywalkSharedField w).z (skywalkSharedField w).a hlen]
  split
  · exact Finset.empty_subset _
  · intro q hq
    apply hW
    apply List.mem_toFinset.mpr
    apply retained_field_subset_shared w
    simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
    rcases hq with hz|ha
    · simp [ModInPlaceLayout.wires,hz]
    · simp [ModInPlaceLayout.wires,ha]

theorem endpoints (w : Nat → Wire) (b effG effS : Wire) (W : Finset Wire)
    (hW : (skywalkSharedWires w).toFinset⊆W) (hb : b∈W) (hg : effG∈W) (hs : effS∈W) :
    wires (mixedTranscriptFieldDivision w b effG effS)⊆W ∧
    wires (mixedTranscriptFieldMultiplication w b effG effS)⊆W := by
  have hu := unary w W hW
  have hc := copy w W hW
  have hr := mixedReplay w b effG effS (mixedTranscriptTape w) W hW hb hg hs (tapeSupport w W hW)
  simp only [mixedTranscriptFieldDivision,mixedTranscriptFieldMultiplication,wires_append,
    Finset.union_subset_iff]
  exact ⟨⟨⟨hu.1,hr.1⟩,hc⟩,⟨⟨hc,hr.2⟩,hu.2⟩⟩

/-- Actual static support of the emitted seven-stage direct kernel. All
measurement correction supports are included by the component wire lemmas. -/
theorem kernel (divide : Bool) (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (b effG effS : Wire) (W : Finset Wire) (hW : (skywalkSharedWires w).toFinset⊆W)
    (hb : b∈W) (hg : effG∈W) (hs : effS∈W) :
    wires (directSkywalkArithmetic divide w b effG effS)⊆W := by
  exact BorrowedSkywalkCompactSupport.kernel divide w hn b effG effS W
    ((BalancedSharedFieldSupport.compactSubsetShared w).trans hW) hb hg hs

end ECDSAAdd.Arithmetic.DirectSupport
