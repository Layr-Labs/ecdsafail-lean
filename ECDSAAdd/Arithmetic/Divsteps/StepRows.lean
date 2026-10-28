import ECDSAAdd.Arithmetic.Divsteps.HalfRow
import ECDSAAdd.Math.Divsteps.RowBounds

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- The actual half-row circuit implements the integer component of one divstep.
Parity and all intermediate bounds follow from the mathematical state invariant;
physical control and routed-input encoding remain explicit layout obligations. -/
theorem integerRow_zStep (q c cin low sign : Wire) (src mask mid carry : List Wire)
    (hn : (q::c::cin::(src++mask++(low::(mid++[sign]))++carry)).Nodup)
    (hs : src.length=mask.length) (ht : mask.length=mid.length+2)
    (hc : carry.length+1=mid.length+2)
    (st : ZState) (pB zB cB : Int) (hbound : Bounds pB zB cB st) (hf : st.f%2=1)
    (hfit : 2*pB<((2^(mid.length+1):Nat):Int))
    (s : ECDSAAdd.State) (m : List Bool)
    (hq : s.basis q=swapControl st) (hp : s.basis c=parityControl st)
    (hi : s.basis cin=false) (ha : signedRegValue src s.basis=routedF st)
    (hb : signedRegValue (low::(mid++[sign])) s.basis=routedG st)
    (hm : regValue mask s.basis=0) (hk : regValue carry s.basis=0) :
    (run (halfRow q c cin low sign src mask mid carry) m s).phase=s.phase ∧
    (∀ w, w∉low::(mid++[sign]) →
      (run (halfRow q c cin low sign src mask mid carry) m s).basis w=s.basis w) ∧
    signedRegValue (skywalkHalfView low (mid++[sign]))
      (run (halfRow q c cin low sign src mask mid carry) m s).basis=(zStep st).g := by
  have hr := routed_rows_bounds hbound
  have hfits := rowValue_fits (swapControl st) (parityControl st) (routedF st) (routedG st)
    pB (mid.length+2) hr.1 hr.2.1 (by simpa using hfit)
  have hcircuit := halfRow_correct q c cin low sign src mask mid carry hn hs ht hc
    (swapControl st) (parityControl st) (routedF st) (routedG st)
    (by simpa using hfits.1.1) (by simpa using hfits.1.2)
    (by simpa [rowValue] using hfits.2.1) (by simpa [rowValue] using hfits.2.2)
    (rowValue_even st hf) s m hq hp hi ha hb hm hk
  refine ⟨hcircuit.1,hcircuit.2.1,?_⟩
  exact hcircuit.2.2.trans (rowValue_zStep st).1.symm

/-- The same physical arithmetic kernel updates the growing coefficient row. -/
theorem coefficientRow_zStep (q c cin : Wire) (src mask y carry : List Wire)
    (hn : (q::c::cin::(src++mask++y++carry)).Nodup)
    (hs : src.length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length)
    (st : ZState) (pB zB cB : Int) (hbound : Bounds pB zB cB st)
    (hfit : 2*cB<((2^(y.length-1):Nat):Int))
    (s : ECDSAAdd.State) (m : List Bool)
    (hq : s.basis q=swapControl st) (hp : s.basis c=parityControl st)
    (hi : s.basis cin=false) (ha : signedRegValue src s.basis=routedFv st)
    (hb : signedRegValue y s.basis=routedGv st)
    (hm : regValue mask s.basis=0) (hk : regValue carry s.basis=0) :
    (run (rowKernel q c cin src mask y carry) m s).phase=s.phase ∧
    (∀ w, w∉y → (run (rowKernel q c cin src mask y carry) m s).basis w=s.basis w) ∧
    signedRegValue y (run (rowKernel q c cin src mask y carry) m s).basis=(zStep st).gv := by
  have hr := routed_rows_bounds hbound
  have hfits := rowValue_fits (swapControl st) (parityControl st) (routedFv st) (routedGv st)
    cB y.length hr.2.2.1 hr.2.2.2 hfit
  have hcircuit := rowKernel_correct q c cin src mask y carry hn hs ht hc
    (swapControl st) (parityControl st) (routedFv st) (routedGv st)
    hfits.1.1 hfits.1.2 hfits.2.1 hfits.2.2 s m hq hp hi ha hb hm hk
  exact ⟨hcircuit.1,hcircuit.2.1,hcircuit.2.2.trans (rowValue_zStep st).2.symm⟩

end ECDSAAdd.Arithmetic.Divsteps
