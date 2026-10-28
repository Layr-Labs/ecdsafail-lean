import ECDSAAdd.Arithmetic.Paper935.WindowRouted
import ECDSAAdd.Arithmetic.Paper935.TaggedInverse
import ECDSAAdd.Arithmetic.Paper935.Activity

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

def RoutedBankLayout.mintControls (L : RoutedBankLayout) (frozen zsign : Wire) : Program :=
  mintActivity frozen L.active++branchTags zsign L.glow L.parity L.q

theorem RoutedBankLayout.mintControls_run (L : RoutedBankLayout) (frozen zsign : Wire)
    (hn : [zsign,L.glow,L.parity,L.q].Nodup) (hfa : frozen≠L.active)
    (hsep : L.active∉[zsign,L.glow,L.parity,L.q])
    (st : ECDSAAdd.Divsteps.ZState) (zlo : List Wire) (s : State) (m : List Bool)
    (ha : s.basis L.active=false) (hp : s.basis L.parity=false) (hq : s.basis L.q=false)
    (hz : signedRegValue (zlo++[zsign]) s.basis=st.z)
    (hg : L.before.g.value s.basis=st.g) :
    let t := run (L.mintControls frozen zsign) m s
    t.phase=s.phase ∧ t.basis L.active= !s.basis frozen ∧
    t.basis L.parity=ECDSAAdd.Divsteps.parityControl st ∧
    t.basis L.q=ECDSAAdd.Divsteps.swapControl st ∧
    (∀ w,w≠L.active → w≠L.parity → w≠L.q → t.basis w=s.basis w) := by
  have ne (w : Wire) (hw : w∈[zsign,L.glow,L.parity,L.q]) : w≠L.active :=
    fun he => hsep (he ▸ hw)
  have zbit := swapControl_bits zsign L.glow zlo (L.gmid++[L.gsign]) st s.basis hz hg
  have gbit := parityControl_bit L.glow (L.gmid++[L.gsign]) st s.basis hg
  let v : State := ⟨s.phase,writeBit s.basis L.active (!s.basis frozen)⟩
  have va := mintActivity_run frozen L.active hfa s m ha
  have keep (w : Wire) (hw : w∈[zsign,L.glow,L.parity,L.q]) : v.basis w=s.basis w := by
    simp [v,writeBit,ne w hw]
  dsimp only
  rw [mintControls,run_append,run_take,va]
  change (run (branchTags zsign L.glow L.parity L.q) (m.drop _) v).phase=_ ∧ _
  rw [branchTags_correct zsign L.glow L.parity L.q hn v _
    ((keep L.parity (by simp)).trans hp) ((keep L.q (by simp)).trans hq)]
  have ap : L.active≠L.parity := (ne L.parity (by simp)).symm
  have aq : L.active≠L.q := (ne L.q (by simp)).symm
  have pq : L.parity≠L.q := by simp_all
  refine ⟨rfl,?_,?_,?_,?_⟩
  · simp [v,writeBit,ap,aq]
  · simp only [writeBit,Function.update_apply,pq,ite_false,ite_true]
    exact (keep L.glow (by simp)).trans gbit
  · simp only [writeBit,Function.update_apply,ite_true]
    rw [keep zsign (by simp),keep L.glow (by simp)]
    exact zbit
  · intro w hwa hwp hwq
    simp [v,writeBit,hwa,hwp,hwq]

theorem RoutedBankLayout.mintControls_proper (L : RoutedBankLayout) (frozen zsign : Wire)
    (hn : [zsign,L.glow,L.parity,L.q].Nodup) (hfa : frozen≠L.active) :
    ProperProgram (L.mintControls frozen zsign) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · simp only [mintActivity,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl
    · trivial
    · exact hfa
  · exact branchTags_proper zsign L.glow L.parity L.q hn g hg

theorem WindowBank.encodes_congr (b : WindowBank) (s t : BasisState)
    (st : ECDSAAdd.Divsteps.ZState) (he : b.Encodes s st)
    (h : ∀ q∈b.rows.flatMap WindowRow.wires,t q=s q) : b.Encodes t st := by
  have val (r : WindowRow) (hr : r∈b.rows) : r.value t=r.value s := by
    unfold WindowRow.value signedRegValue
    rw [regValue_congr r.wires t s (fun q hq => h q (List.mem_flatMap.mpr ⟨r,hr,hq⟩))]
  exact ⟨(val b.f (by simp [rows])).trans he.1,
    (val b.g (by simp [rows])).trans he.2.1,
    (val b.fv (by simp [rows])).trans he.2.2.1,
    (val b.gv (by simp [rows])).trans he.2.2.2⟩

end ECDSAAdd.Arithmetic.Paper935
