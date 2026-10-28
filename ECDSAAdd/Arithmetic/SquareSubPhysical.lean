import ECDSAAdd.Arithmetic.SquareSubLayout
import ECDSAAdd.Arithmetic.ModularPhysical
import ECDSAAdd.Arithmetic.KaratsubaSquarePhysical
import ECDSAAdd.Arithmetic.SquareReducePhysical

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem modInPlace_physical (L : ModInPlaceLayout) (p : Nat) (hn : L.wires.Nodup) :
    GatePhysical (modAddInPlace L p) ∧ GatePhysical (modSubInPlace L p) := by
  have nd : L.toModAddCoreLayout.wires.Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,ModInPlaceLayout.z,
      ModAddCoreLayout.wires,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have ha : GatePhysical (modAddInPlace L p) := modAddCore_physical _ _ nd
  have hn' := negRaw_physical L p hn
  exact ⟨ha,by simpa only [modSubInPlace,gatePhysical_append] using And.intro (And.intro hn' ha) hn'⟩

theorem squareSub_physical (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (squareSub L) := by
  have hi := karatsubaSquares_physical L.integer (L.integer_valid hw hn).nodup
  have hr := squareReductions_physical L.reduction (L.reduction_nodup hn)
  have ho := (modInPlace_physical L.output SquareReduction.p (L.output_nodup hn)).2
  simpa only [squareSub,gatePhysical_append] using
    And.intro (And.intro (And.intro (And.intro hi.1 hr.1) ho) hr.2) hi.2

end ECDSAAdd.Arithmetic
