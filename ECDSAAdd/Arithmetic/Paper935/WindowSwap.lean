import ECDSAAdd.Arithmetic.Paper935.WindowBank
import ECDSAAdd.Arithmetic.Paper935.RetiredInverse

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

def WindowRow.asStep (r : WindowRow) : StepRow :=
  ⟨r.payload.headD r.sign,r.payload.tail,r.sign⟩
def WindowRow.second (r : WindowRow) : Wire := r.asStep.second

theorem WindowRow.second_bit (r : WindowRow) (h : r.payload≠[]) (s : BasisState) :
    s r.second=decide (ECDSAAdd.Divsteps.bitk (r.value s) 1=1) := by
  cases r with
  | mk payload sign =>
    cases payload with
    | nil => exact (h rfl).elim
    | cons low mid => exact StepRow.second_bit ⟨low,mid,sign⟩ s

theorem WindowRow.second_mem (r : WindowRow) (h : r.payload≠[]) : r.second∈r.wires := by
  cases r with
  | mk payload sign =>
    cases payload with
    | nil => exact (h rfl).elim
    | cons low mid => exact StepRow.second_mem ⟨low,mid,sign⟩

/-- Swap reconstruction reads the current resized coefficient view, including
the case where its weight-two bit is the dedicated sign wire. -/
theorem WindowRow.swap_witness (r : WindowRow) (hn : r.payload≠[])
    (p : Int) (st : ECDSAAdd.Divsteps.ZState) (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1)
    (frozen : Bool) (active q : Wire) (s : BasisState)
    (ha : s active= !frozen) (hq : s q=decide (0≤st.z ∧ st.g%2=1))
    (hv : r.value s=(if frozen then st else ECDSAAdd.Divsteps.zStep st).fv)
    (hz : frozen=true → st.g=0) : s q=(s active && s r.second) := by
  rw [ha,hq,r.second_bit hn s,hv]
  cases frozen with
  | false => simpa using ECDSAAdd.Divsteps.swap_bit_law p st hi hp
  | true => simp [hz rfl]

theorem WindowRow.retire_swap (r : WindowRow) (hn : r.payload≠[])
    (p : Int) (st : ECDSAAdd.Divsteps.ZState) (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1)
    (frozen : Bool) (active q : Wire) (s : State) (m n : List Bool)
    (haq : active≠q) (hrq : r.second≠q)
    (ha : s.basis active= !frozen) (hq : s.basis q=decide (0≤st.z ∧ st.g%2=1))
    (hv : r.value s.basis=(if frozen then st else ECDSAAdd.Divsteps.zStep st).fv)
    (hz : frozen=true → st.g=0) :
    run (eraseAnd active r.second q) m s=⟨s.phase,writeBit s.basis q false⟩ ∧
    run [.CCX active r.second q] n (run (eraseAnd active r.second q) m s)=s := by
  have witness := r.swap_witness hn p st hi hp frozen active q s.basis ha hq hv hz
  exact ⟨eraseAnd_run active r.second q haq hrq s m witness,
    retireAnd_restore active r.second q haq hrq s m n witness⟩

end ECDSAAdd.Arithmetic.Paper935
