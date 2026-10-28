import ECDSAAdd.Arithmetic.Paper935.WindowBank
import ECDSAAdd.Arithmetic.Paper935.RoutedInverse
import ECDSAAdd.Arithmetic.Paper935.IdleRows

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

/-- The public add-window view names both low wires explicitly. Halving g
rotates its physical view, while the coefficient shift retains its view. -/
structure RoutedBankLayout where
  q : Wire
  parity : Wire
  u : Wire
  k : Wire
  active : Wire
  f : WindowRow
  gv : WindowRow
  glow : Wire
  gmid : List Wire
  gsign : Wire
  vlow : Wire
  vmid : List Wire
  vsign : Wire

def RoutedBankLayout.before (L : RoutedBankLayout) : WindowBank :=
  ⟨L.f,⟨L.glow::L.gmid,L.gsign⟩,⟨L.vlow::L.vmid,L.vsign⟩,L.gv⟩
def RoutedBankLayout.after (L : RoutedBankLayout) : WindowBank :=
  ⟨L.f,⟨L.gmid++[L.gsign],L.glow⟩,⟨L.vlow::L.vmid,L.vsign⟩,L.gv⟩
def RoutedBankLayout.program (L : RoutedBankLayout) : Program :=
  routedStage L.q L.parity L.u L.k L.active L.glow L.gsign L.vlow L.vsign
    L.f.wires L.gmid L.vmid L.gv.wires

structure RoutedBankLayout.Valid (L : RoutedBankLayout) : Prop where
  addFG : (L.q::L.parity::L.u::L.k::(L.f.wires++(L.glow::(L.gmid++[L.gsign])))).Nodup
  addV : (L.q::L.parity::L.u::L.k::((L.vlow::(L.vmid++[L.vsign]))++L.gv.wires)).Nodup
  half : (L.glow::(L.gmid++[L.gsign])).Nodup
  double : (L.active::L.vlow::(L.vmid++[L.vsign])).Nodup
  gSep : List.Disjoint (L.glow::(L.gmid++[L.gsign])) ((L.vlow::(L.vmid++[L.vsign]))++L.gv.wires)
  vSep : List.Disjoint (L.vlow::(L.vmid++[L.vsign])) ((L.glow::(L.gmid++[L.gsign]))++L.gv.wires)
  activeSep : L.active∉(L.glow::(L.gmid++[L.gsign]))++L.gv.wires
  fgLength : L.f.wires.length=L.gmid.length+2
  vLength : L.gv.wires.length=L.vmid.length+2
  route : (L.q::((L.f.wires++(L.vlow::(L.vmid++[L.vsign])))++((L.glow::(L.gmid++[L.gsign]))++L.gv.wires))).Nodup
  controls : List.Disjoint [L.q,L.parity,L.u,L.k,L.active]
    (L.f.wires++(L.vlow::(L.vmid++[L.vsign]))++(L.glow::(L.gmid++[L.gsign]))++L.gv.wires)
  fSep : List.Disjoint L.f.wires ((L.glow::(L.gmid++[L.gsign]))++(L.vlow::(L.vmid++[L.vsign]))++L.gv.wires)

theorem RoutedBankLayout.run_rows (L : RoutedBankLayout) (hv : L.Valid)
    (st : ECDSAAdd.Divsteps.ZState) (hf : st.f%2=1) (s : State) (m : List Bool)
    (hu : s.basis L.u=false) (hk : s.basis L.k=false) (ha : s.basis L.active=true)
    (hq : s.basis L.q=decide (0≤st.z ∧ st.g%2=1))
    (hb : s.basis L.parity=decide (ECDSAAdd.Divsteps.bbit st=1))
    (he : L.before.Encodes s.basis st)
    (hg : PayloadFits (L.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep st).g))
    (hgv : PayloadFits (L.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep st).gv)
    (hfv : PayloadFits (L.vmid.length+1) (ECDSAAdd.Divsteps.zStep st).fv) :
    L.after.Encodes (run L.program m s).basis (ECDSAAdd.Divsteps.zStep st) ∧
    (run L.program m s).phase=s.phase ∧
    (∀ q,q∉L.before.rows.flatMap WindowRow.wires → (run L.program m s).basis q=s.basis q) := by
  have h := routedStage_divstep L.q L.parity L.u L.k L.active L.glow L.gsign L.vlow L.vsign
    L.f.wires L.gmid L.vmid L.gv.wires hv.addFG hv.addV hv.half hv.double hv.gSep hv.vSep
    hv.activeSep hv.fgLength hv.vLength hv.route hv.controls hv.fSep st hf s m hu hk ha hq hb
    he.1 he.2.1 he.2.2.1 he.2.2.2 hg.1 hg.2 hgv.1 hgv.2 hfv.1 hfv.2
  refine ⟨?_,h.1,?_⟩
  · simpa only [after,WindowBank.Encodes,WindowRow.value,WindowRow.wires,
      skywalkHalfView,List.cons_append] using h.2.2
  · intro q hq
    exact h.2.1 q (by simpa [before,WindowBank.rows,WindowRow.wires,List.append_assoc] using hq)

theorem RoutedBankLayout.widths_after (L : RoutedBankLayout) (w : RowWindow)
    (h : L.before.Widths w) : L.after.Widths w := by
  simpa [before,after,WindowBank.Widths,Nat.add_comm] using h

theorem RoutedBankLayout.run_idle (L : RoutedBankLayout) (hv : L.Valid)
    (st : ECDSAAdd.Divsteps.ZState) (s : State) (m : List Bool)
    (hu : s.basis L.u=false) (hk : s.basis L.k=false)
    (ha : s.basis L.active=false) (hq : s.basis L.q=false) (hb : s.basis L.parity=false)
    (he : L.before.Encodes s.basis st) (hg : st.g=0) :
    run L.program m s=s ∧ L.after.Encodes s.basis st := by
  have gz : signedRegValue (L.glow::(L.gmid++[L.gsign])) s.basis=0 := he.2.1.trans hg
  have gs : s.basis L.gsign=false := by
    by_contra hh
    have neg := (signedRegValue_neg_iff (L.glow::L.gmid) L.gsign s.basis).mpr
      (Bool.eq_true_of_not_eq_false hh)
    simp only [List.cons_append] at neg
    rw [gz] at neg
    omega
  have route := routeRows_idle L.q L.f.wires (L.glow::(L.gmid++[L.gsign]))
    (L.vlow::(L.vmid++[L.vsign])) L.gv.wires (by simpa using hv.fgLength)
    (by simpa using hv.vLength.symm) hv.route s m hq
  constructor
  · rw [program,routedStage,run_append,run_take,route]
    exact rowStage_idle L.q L.parity L.u L.k L.active L.glow L.gsign L.vlow L.vsign
      L.f.wires L.gmid L.vmid L.gv.wires hv.addFG hv.addV hv.double hv.fgLength hv.vLength
      s _ hu hk hb ha gs
  · refine ⟨he.1,?_,he.2.2⟩
    have hh := halfView_zero L.glow L.gsign L.gmid s.basis gz
    simpa [after,WindowRow.value,WindowRow.wires,skywalkHalfView,hg] using hh

def RoutedBankLayout.inverse (L : RoutedBankLayout) : Program :=
  routedStageInverse L.q L.parity L.u L.k L.active L.glow L.gsign L.vlow L.vsign
    L.f.wires L.gmid L.vmid L.gv.wires

theorem RoutedBankLayout.roundtrip (L : RoutedBankLayout) (hv : L.Valid)
    (s : State) (m n : List Bool) (hu : s.basis L.u=false) (hk : s.basis L.k=false) :
    run L.inverse n (run L.program m s)=s :=
  routedStage_roundtrip L.q L.parity L.u L.k L.active L.glow L.gsign L.vlow L.vsign
    L.f.wires L.gmid L.vmid L.gv.wires hv.addFG hv.addV hv.half hv.double hv.fgLength hv.vLength
    hv.route s m n hu hk

theorem RoutedBankLayout.run_pinned (L : RoutedBankLayout) (hv : L.Valid)
    (st : ECDSAAdd.Divsteps.ZState) (frozen : Bool) (hf : st.f%2=1)
    (s : State) (m : List Bool) (hu : s.basis L.u=false) (hk : s.basis L.k=false)
    (ha : s.basis L.active= !frozen)
    (hq : s.basis L.q=decide (0≤st.z ∧ st.g%2=1))
    (hb : s.basis L.parity=decide (ECDSAAdd.Divsteps.bbit st=1))
    (he : L.before.Encodes s.basis st) (hzero : frozen=true → st.g=0)
    (hg : frozen=false → PayloadFits (L.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep st).g))
    (hgv : frozen=false → PayloadFits (L.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep st).gv)
    (hfv : frozen=false → PayloadFits (L.vmid.length+1) (ECDSAAdd.Divsteps.zStep st).fv) :
    L.after.Encodes (run L.program m s).basis (if frozen then st else ECDSAAdd.Divsteps.zStep st) ∧
    (run L.program m s).phase=s.phase ∧
    (∀ q,q∉L.before.rows.flatMap WindowRow.wires → (run L.program m s).basis q=s.basis q) := by
  cases frozen with
  | false => exact L.run_rows hv st hf s m hu hk ha hq hb he (hg rfl) (hgv rfl) (hfv rfl)
  | true =>
    have gz := hzero rfl
    have q0 : s.basis L.q=false := by simpa [gz] using hq
    have b0 : s.basis L.parity=false := by simpa [ECDSAAdd.Divsteps.bbit,gz] using hb
    have idle := L.run_idle hv st s m hu hk ha q0 b0 he gz
    rw [idle.1]
    exact ⟨idle.2,rfl,fun _ _ => rfl⟩

end ECDSAAdd.Arithmetic.Paper935
