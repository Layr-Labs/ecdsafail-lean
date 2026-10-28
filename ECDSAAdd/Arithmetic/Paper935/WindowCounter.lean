import ECDSAAdd.Arithmetic.Paper935.WindowBank
import ECDSAAdd.Arithmetic.Paper935.CounterBorrow
import ECDSAAdd.Arithmetic.Divsteps.CounterUpdateInverse

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

/-- Row cleanup precedes the measured counter update. Scratch is reserved
from the smaller exit arena, so it may reuse the released high row sites. -/
theorem WindowBank.resize_then_counter (b out : WindowBank) (w : RowWindow)
    (A C D : Arena) (p : Program) (h : b.Planned out w A C p)
    (active swap : Wire) (z zero carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (hown : (active::swap::z).toFinset⊆A.live)
    (hsep : List.Disjoint (active::swap::z) (b.rows.flatMap WindowRow.wires))
    (hout : List.Disjoint z (out.rows.flatMap WindowRow.wires))
    (hborrow : C.reserve (zero++carry).toFinset=some D)
    (s : State) (m : List Bool) (st : ECDSAAdd.Divsteps.ZState)
    (hr : A.Ready s.basis) (he : b.Encodes s.basis st) (hf : w.Fits st) :
    let t := run (p++counterUpdate active swap zero z carry) m s
    C.Ready t.basis ∧ out.Encodes t.basis st ∧ out.Widths w ∧
    regValue z t.basis=counterWord z.length (s.basis active) (s.basis swap) (regValue z s.basis) := by
  let v := run p m s
  have resize := b.resize_correct out w A C p h s m st hr he hf
  have kept : ∀ q∈active::swap::z,q∈C.live ∧ v.basis q=s.basis q := by
    intro q hq
    exact resize.2.2.2.2 q (hown (List.mem_toFinset.mpr hq)) (List.disjoint_left.mp hsep hq)
  have cown : (active::swap::z).toFinset⊆C.live := by
    intro q hq; exact (kept q (List.mem_toFinset.mp hq)).1
  have step := counterUpdate_borrowed C D active swap z zero carry hn hz hc cown hborrow
    v (m.drop (measurementCount p)) resize.2.1
  have rowkeep (r : WindowRow) (hm : r∈out.rows) :
      r.value (run (counterUpdate active swap zero z carry) (m.drop (measurementCount p)) v).basis=
      r.value v.basis := by
    unfold WindowRow.value signedRegValue
    apply congrArg (signedDecode r.wires.length)
    apply regValue_congr
    intro q hq
    apply step.2.2.2.1 q
    intro hqz
    exact List.disjoint_left.mp hout hqz (List.mem_flatMap.mpr ⟨r,hm,hq⟩)
  have enc : out.Encodes (run (counterUpdate active swap zero z carry) (m.drop (measurementCount p)) v).basis st := by
    have prev := resize.2.2.1
    exact ⟨(rowkeep out.f (by simp [rows])).trans prev.1,
      (rowkeep out.g (by simp [rows])).trans prev.2.1,
      (rowkeep out.fv (by simp [rows])).trans prev.2.2.1,
      (rowkeep out.gv (by simp [rows])).trans prev.2.2.2⟩
  dsimp only
  rw [run_append,run_take]
  refine ⟨step.2.1,enc,resize.2.2.2.1,?_⟩
  rw [step.2.2.1,(kept active (by simp)).2,(kept swap (by simp)).2]
  rw [regValue_congr z v.basis s.basis (fun q hq => (kept q (by simp [hq])).2)]

/-- On reverse execution the counter is undone before restoring the old wider
row views; newly freed high sites therefore remain available to its scratch. -/
theorem WindowBank.resize_counter_roundtrip (b out : WindowBank) (w : RowWindow)
    (A C D : Arena) (p : Program) (h : b.Planned out w A C p)
    (active swap : Wire) (z zero carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (hown : (active::swap::z).toFinset⊆A.live)
    (hsep : List.Disjoint (active::swap::z) (b.rows.flatMap WindowRow.wires))
    (hborrow : C.reserve (zero++carry).toFinset=some D)
    (s : State) (m n : List Bool) (st : ECDSAAdd.Divsteps.ZState)
    (hr : A.Ready s.basis) (he : b.Encodes s.basis st) (hf : w.Fits st)
    (hAS : s.basis swap=true → s.basis active=true) :
    run (counterUpdateInverse active swap zero z carry++p.reverse) n
      (run (p++counterUpdate active swap zero z carry) m s)=s := by
  let v := run p m s
  have resize := b.resize_correct out w A C p h s m st hr he hf
  have kept : ∀ q∈active::swap::z,v.basis q=s.basis q := by
    intro q hq
    exact (resize.2.2.2.2 q (hown (List.mem_toFinset.mpr hq)) (List.disjoint_left.mp hsep hq)).2
  have fresh := (C.reserve_ready D (zero++carry).toFinset v.basis resize.2.1 hborrow).2
  have hz0 : regValue zero v.basis=0 := (regValue_zero zero v.basis).mpr
    (fun q hq => fresh q (by simp [hq]))
  have hc0 : regValue carry v.basis=0 := (regValue_zero carry v.basis).mpr
    (fun q hq => fresh q (by simp [hq]))
  have hrel : v.basis swap=true → v.basis active=true := by
    rw [(kept swap (by simp)),(kept active (by simp))]
    exact hAS
  rw [run_append,run_take,run_append,run_take]
  rw [counterUpdateInverse_after_forward active swap zero z carry hn hz hc v _ n hrel hz0 hc0]
  exact b.resize_roundtrip out w A C p h s m _

end ECDSAAdd.Arithmetic.Paper935
