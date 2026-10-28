import ECDSAAdd.Arithmetic.Paper935.HistoryControls
import ECDSAAdd.Arithmetic.Divsteps.SwapHistory

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps ECDSAAdd.Arithmetic.Divsteps

/-- Actual recorded offset distinguishes a newly fired lane from an older
frozen lane. The old offset is strictly below the current positive offset. -/
theorem historyControls_values (p : Int) (st : ZState) (hi : Inv p st) (hp : p%2=1)
    (frozen fire active sigma : Wire) (fv : StepRow) (rb : List ZeroBit) (k r : Nat)
    (hn : [frozen,fire,active,fv.second,sigma].Nodup)
    (hr : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length) (hlt : r<k)
    (oldFrozen fired : Bool) (hnew : oldFrozen=true → fired=false)
    (s : State) (m : List Bool) (hc : ∀ b∈rb,s.basis b.work=false)
    (hfire0 : s.basis fire=false) (ha : s.basis active=false) (hq : s.basis sigma=false)
    (hfrozen : s.basis frozen=(oldFrozen || fired))
    (hrecord : regValue (rb.map ZeroBit.input) s.basis=(if fired then k else r))
    (hrow : signedRegValue fv.wires s.basis=(if oldFrozen then st else zStep st).fv) :
    run (mintHistoryControls frozen fire active fv.second sigma rb k) m s=
      ⟨s.phase,writeBit (writeBit (writeBit s.basis fire fired) active (!oldFrozen)) sigma
        (!oldFrozen && decide (0≤st.z ∧ st.g%2=1))⟩ := by
  have hcmp : (s.basis frozen && decide (regValue (rb.map ZeroBit.input) s.basis=k))=fired := by
    rw [hfrozen,hrecord]
    cases fired <;> simp [show r≠k by omega]
  have halive : (!s.basis frozen ^^ fired)=!oldFrozen := by
    rw [hfrozen]
    cases ho : oldFrozen <;> cases hf : fired <;> simp_all
  have hswap : (!oldFrozen && s.basis fv.second)=
      (!oldFrozen && decide (0≤st.z ∧ st.g%2=1)) := by
    rw [fv.second_bit s.basis,hrow]
    cases oldFrozen with
    | true => simp
    | false => simpa using (swap_bit_law p st hi hp).symm
  rw [mintHistoryControls_run frozen fire active fv.second sigma rb k hn hr hk s m hc hfire0 ha hq]
  rw [hcmp,halive,hswap]

end ECDSAAdd.Arithmetic.Paper935
