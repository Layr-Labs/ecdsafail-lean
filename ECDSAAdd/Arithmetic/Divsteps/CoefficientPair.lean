import ECDSAAdd.Arithmetic.Divsteps.StepRows
import ECDSAAdd.Arithmetic.Divsteps.DoubleRow

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- Update the second coefficient before doubling its source. The source must
remain available to the shared row kernel until its last use. -/
def coefficientPair (q parity cin active low sign : Wire)
    (mid mask target carry : List Wire) : Program :=
  rowKernel q parity cin (low::(mid++[sign])) mask target carry ++
    doubleSigned active low sign mid

private theorem signed_congr (xs : List Wire) (s t : BasisState)
    (h : ∀ w, w∈xs → s w=t w) : signedRegValue xs s=signedRegValue xs t := by
  unfold signedRegValue
  rw [regValue_congr xs s t h]

/-- Both coefficient outputs describe the same frozen-aware mathematical step;
all controls and reusable workspace are restored, for every measurement list. -/
theorem coefficientPair_zSlot (q parity cin active low sign : Wire)
    (mid mask target carry : List Wire)
    (hknd : (q::parity::cin::((low::(mid++[sign]))++mask++target++carry)).Nodup)
    (hdnd : (active::low::(mid++[sign])).Nodup)
    (hdis : List.Disjoint (low::(mid++[sign])) target)
    (haout : active∉target)
    (hs : (low::(mid++[sign])).length=mask.length)
    (ht : mask.length=target.length) (hk : carry.length+1=target.length)
    (st : ZState) (pB zB cB : Int) (hbnd : Bounds pB zB cB st)
    (hfit : 2*cB<((2^(target.length-1):Nat):Int))
    (s : State) (m : List Bool)
    (hq : s.basis q=swapControl st) (hp : s.basis parity=parityControl st)
    (ha : s.basis active=activeControl st) (hi : s.basis cin=false)
    (hf : signedRegValue (low::(mid++[sign])) s.basis=routedFv st)
    (hg : signedRegValue target s.basis=routedGv st)
    (hm : regValue mask s.basis=0) (hc : regValue carry s.basis=0) :
    (run (coefficientPair q parity cin active low sign mid mask target carry) m s).phase=s.phase ∧
    (∀ w, w∉(low::(mid++[sign]))++target →
      (run (coefficientPair q parity cin active low sign mid mask target carry) m s).basis w=s.basis w) ∧
    signedRegValue (low::(mid++[sign]))
      (run (coefficientPair q parity cin active low sign mid mask target carry) m s).basis=(zSlot st).fv ∧
    signedRegValue target
      (run (coefficientPair q parity cin active low sign mid mask target carry) m s).basis=(zSlot st).gv := by
  let k := rowKernel q parity cin (low::(mid++[sign])) mask target carry
  let t := run k m s
  let rest := m.drop (measurementCount k)
  obtain ⟨hphase,hframe,hvalue⟩ := coefficientRow_zStep q parity cin
    (low::(mid++[sign])) mask target carry hknd hs ht hk st pB zB cB hbnd hfit
    s m hq hp hi hf hg hm hc
  have hlen : target.length=mid.length+2 := by
    have hh := hs.trans ht
    simp only [List.length_cons,List.length_append,List.length_nil] at hh
    omega
  have hdoublefit : 2*cB<((2^(mid.length+1):Nat):Int) := by
    simpa [hlen] using hfit
  have hsource : signedRegValue (low::(mid++[sign])) t.basis=routedFv st :=
    (signed_congr _ _ _ (fun w hw => hframe w (List.disjoint_left.mp hdis hw))).trans hf
  obtain ⟨hdphase,hdframe,hdfv⟩ := doubleRow_zSlot active low sign mid hdnd st pB zB cB
    hbnd hdoublefit t rest ((hframe active haout).trans ha) hsource
  have hdgv : signedRegValue target (run (doubleSigned active low sign mid) rest t).basis=
      (zSlot st).gv := by
    calc
      _ = signedRegValue target t.basis := signed_congr _ _ _ (fun w hw =>
        hdframe w (fun hin => List.disjoint_left.mp hdis hin hw))
      _ = (zStep st).gv := hvalue
      _ = (zSlot st).gv := (target_rows_frozen st).2.1
  rw [coefficientPair,run_append,run_take]
  refine ⟨hdphase.trans hphase,?_,hdfv,hdgv⟩
  intro w hw
  have hfout : w∉low::(mid++[sign]) := fun h => hw (List.mem_append_left _ h)
  have hgout : w∉target := fun h => hw (List.mem_append_right _ h)
  exact (hdframe w hfout).trans (hframe w hgout)

theorem coefficientPair_counts (q parity cin active low sign : Wire)
    (mid mask target carry : List Wire)
    (hs : (low::(mid++[sign])).length=mask.length)
    (ht : mask.length=target.length) (hc : carry.length+1=target.length) :
    toffoliCount (coefficientPair q parity cin active low sign mid mask target carry)=
      (3*target.length-2)+(mid.length+2) ∧
    measurementCount (coefficientPair q parity cin active low sign mid mask target carry)=
      3*target.length-2 := by
  obtain ⟨htf,hm⟩ := rowKernel_counts q parity cin (low::(mid++[sign])) mask target carry hs ht hc
  simp [coefficientPair,toffoliCount_append,measurementCount_append,htf,hm,
    (doubleSigned_counts active low sign mid).1,(doubleSigned_counts active low sign mid).2]

end ECDSAAdd.Arithmetic.Divsteps
