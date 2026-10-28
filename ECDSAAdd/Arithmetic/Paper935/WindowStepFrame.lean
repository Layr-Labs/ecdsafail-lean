import ECDSAAdd.Arithmetic.Paper935.WindowStep
import ECDSAAdd.Arithmetic.Paper935.WindowResizePhase

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

theorem RoutedBankLayout.rows_membership (L : RoutedBankLayout) (q : Wire) :
    q∈L.after.rows.flatMap WindowRow.wires ↔ q∈L.before.rows.flatMap WindowRow.wires := by
  simp only [after,before,WindowBank.rows,List.flatMap_cons,List.flatMap_nil,
    WindowRow.wires,List.mem_append,List.mem_cons,List.not_mem_nil]
  tauto

theorem RoutedBankLayout.windowStep_phase_frame (L : RoutedBankLayout) (hv : L.Valid)
    (out : WindowBank) (w : RowWindow) (A C D : Arena) (resize : Program)
    (hp : L.after.Planned out w A C resize) (z zero carry : List Wire)
    (hn : (L.active::L.q::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (hrow : (L.before.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (hborrow : C.reserve (zero++carry).toFinset=some D)
    (st : ECDSAAdd.Divsteps.ZState) (frozen : Bool) (hf : st.f%2=1)
    (s : State) (m : List Bool) (hu : s.basis L.u=false) (hk : s.basis L.k=false)
    (ha : s.basis L.active= !frozen)
    (hq : s.basis L.q=decide (0≤st.z ∧ st.g%2=1))
    (hb : s.basis L.parity=decide (ECDSAAdd.Divsteps.bbit st=1))
    (he : L.before.Encodes s.basis st) (hzero : frozen=true → st.g=0)
    (hg : frozen=false → PayloadFits (L.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep st).g))
    (hgv : frozen=false → PayloadFits (L.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep st).gv)
    (hfv : frozen=false → PayloadFits (L.vmid.length+1) (ECDSAAdd.Divsteps.zStep st).fv)
    (hready : A.Ready s.basis) (hfit : w.Fits (if frozen then st else ECDSAAdd.Divsteps.zStep st)) :
    (run (L.windowStep resize zero z carry) m s).phase=s.phase ∧
    ∀ q∈A.live,q∉L.before.rows.flatMap WindowRow.wires → q∉z →
      (run (L.windowStep resize zero z carry) m s).basis q=s.basis q := by
  let v := run L.program m s
  let ms := m.drop (measurementCount L.program)
  let t := run resize ms v
  have r := L.run_pinned hv st frozen hf s m hu hk ha hq hb he hzero hg hgv hfv
  have ready : A.Ready v.basis := by
    intro q hq hn
    rw [r.2.2 q (fun hh => hn (hrow (List.mem_toFinset.mpr hh)))]
    exact hready q hq hn
  have rs := L.after.resize_correct out w A C resize hp v ms
    (if frozen then st else ECDSAAdd.Divsteps.zStep st) ready r.1 hfit
  have fresh := (C.reserve_ready D (zero++carry).toFinset t.basis rs.2.1 hborrow).2
  have hz0 : regValue zero t.basis=0 := (regValue_zero zero t.basis).mpr
    (fun q hq => fresh q (by simp [hq]))
  have hc0 : regValue carry t.basis=0 := (regValue_zero carry t.basis).mpr
    (fun q hq => fresh q (by simp [hq]))
  constructor
  · rw [windowStep,run_append,run_take,run_append,run_take]
    have cp := (counterUpdate_spec L.active L.q zero z carry hn hz hc
      (t.basis L.active) (t.basis L.q) (regValue z t.basis) t
      (ms.drop (measurementCount resize)) ⟨rfl,rfl,hz0,rfl,hc0⟩).1
    exact cp.trans ((L.after.resize_phase out w A C resize hp v ms).trans r.2.1)
  · intro q hq hout hzout
    have afterout : q∉L.after.rows.flatMap WindowRow.wires := by
      simpa only [L.rows_membership] using hout
    have hresize := (rs.2.2.2.2 q hq afterout).2
    rw [windowStep,run_append,run_take,run_append,run_take]
    exact (counterUpdate_frame L.active L.q zero z carry hn hz hc t _ hz0 hc0 q hzout).trans
      (hresize.trans (r.2.2 q hout))

end ECDSAAdd.Arithmetic.Paper935
