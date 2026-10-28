import ECDSAAdd.Arithmetic.Paper935.WideCoefficientFold
import ECDSAAdd.Arithmetic.Paper935.Fold32PlacementResources

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- The existing physical reducer accepts an already encoded mathematical
fold. Producing that encoding is an explicit caller obligation. -/
theorem fold32PlacedReduce_wide_input (f : Wire → Wire) (hf : Function.Injective f)
    (z : Int) (hz : z.natAbs<2^280) (s : State) (m : List Bool)
    (ready : Fold32PlacedReady f s.basis) (enabled : s.basis (f 0)=true)
    (flag : s.basis (f 290)=false)
    (encoded : regValue (fold32Word.map f) s.basis=wideSignedFold z) :
    let out := run (fold32PlacedReduce f) m s
    regValue (fold32Word.map f) out.basis<fold32Prime ∧
    (regValue (fold32Word.map f) out.basis : ZMod fold32Prime)=(z : ZMod fold32Prime) ∧
    Fold32PlacedReady f out.basis ∧
    out.basis (f 290)=decide (wideSignedFold z<fold32Prime) ∧
    out.basis (f 0)=true ∧ out.phase=s.phase := by
  have bound : regValue (fold32Word.map f) s.basis<2*fold32Prime := by
    rw [encoded]
    exact wideSignedFold_bound z hz
  have h := fold32PlacedReduce_contract f hf s m ready enabled flag bound
  dsimp only at h ⊢
  rw [encoded] at h
  refine ⟨?_,?_,h.2.1,h.2.2.1,h.2.2.2⟩
  · rw [h.1]
    exact Nat.mod_lt _ (by norm_num [fold32Prime])
  · rw [h.1,ZMod.natCast_mod]
    exact wideSignedFold_mod z hz

end ECDSAAdd.Arithmetic.Paper935
