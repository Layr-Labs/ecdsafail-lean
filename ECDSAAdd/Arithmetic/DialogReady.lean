import ECDSAAdd.Arithmetic.DialogState
import ECDSAAdd.Arithmetic.DialogLoad
import ECDSAAdd.Arithmetic.InverseSpec

namespace ECDSAAdd.Arithmetic
namespace DialogLayout

/-- 安全分母装卸期间保持为零的位；不含u/v和两个载荷。 -/
def rest (L : DialogLayout) : List Wire :=
  L.records.flatMap RoundRecord.wires ++
  [L.first.done,L.first.oddWork,L.first.bothWork,L.first.compareCin,L.first.cin] ++
  L.first.data.reg .y ++ L.first.data.reg .carry ++ L.first.data.reg .zero ++
  [L.first.active] ++ L.first.k ++ L.first.counter.y ++ L.first.kNext ++ L.first.counter.carry

theorem ready_perm (L : DialogLayout) :
    (L.control::L.x++L.y++L.z++L.first.u++L.first.v++L.rest).Perm L.wires := by
  apply List.Perm.trans ?_ L.registerWires_perm
  apply List.perm_iff_count.mpr
  intro w
  have hr : L.first.r=L.x++[L.control] := by
    simp [KaliskiRoundLayout.r,KaliskiRoundLayout.data,RoundDataLayout.r,RoundDataLayout.reg,
      x,control,RoundBit.get]
  simp only [registerWires,rest,hr,List.count_append,List.count_cons,List.count_nil]
  omega

end DialogLayout

private theorem tape_zero (rs : List RoundRecord) (s : BasisState) :
    TapeValues rs (List.replicate rs.length (false,false)) s ↔
      ∀ w∈rs.flatMap RoundRecord.wires,s w=false := by
  induction rs with
  | nil => simp [TapeValues]
  | cons r rs ih => simp only [List.length_cons,List.replicate_succ,TapeValues,List.flatMap_cons,RoundRecord.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_and,forall_eq,ih, and_assoc]

theorem dialogReady_iff (L : DialogLayout) (U V : Nat) (hV : V≠0) (s : BasisState) :
    (ValueLoopState L.first ⟨U,V,0⟩ s ∧
      TapeValues L.records (List.replicate L.records.length (false,false)) s) ↔
    (regValue L.first.u s=U ∧ regValue L.first.v s=V ∧ regValue L.rest s=0) := by
  have hr : regValue L.rest s=0 ↔
      (∀ w∈L.records.flatMap RoundRecord.wires,s w=false) ∧
      s L.first.done=false ∧ s L.first.oddWork=false ∧ s L.first.bothWork=false ∧
      s L.first.compareCin=false ∧ s L.first.cin=false ∧
      regValue (L.first.data.reg .y) s=0 ∧ regValue (L.first.data.reg .carry) s=0 ∧
      regValue (L.first.data.reg .zero) s=0 ∧ s L.first.active=false ∧
      regValue L.first.k s=0 ∧ regValue L.first.counter.y s=0 ∧
      regValue L.first.kNext s=0 ∧ regValue L.first.counter.carry s=0 := by
    simp only [DialogLayout.rest,regValue_zero,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,forall_and,or_imp,forall_eq,and_assoc]
  rw [hr]
  constructor
  · rintro ⟨h,ht⟩
    exact ⟨h.u,h.v,(tape_zero _ _).mp ht,by simpa [hV] using h.done,h.odd,h.both,h.cin,
      h.dataCin,h.mask,h.carry,h.zero,h.active,h.k,h.counterY,h.next,h.counterCarry⟩
  · rintro ⟨hu,hv,ht,hd,ho,hb,hc,hci,hy,hcarry,hz,ha,hk,hcy,hnext,hcc⟩
    exact ⟨⟨hu,hv,hy,hcarry,hz,hci,hk,hnext,hcy,hcc,ha,by simpa [hV] using hd,ho,hb,hc⟩,
      (tape_zero _ _).mpr ht⟩

/-- 装卸边界直接列出全部可见寄存器；rest是逐位零断言。 -/
def DialogValues (L : DialogLayout) (B : Bool) (X Y Z U V : Nat) (s : BasisState) : Prop :=
  s L.control=B ∧ regValue L.x s=X ∧ regValue L.y s=Y ∧ regValue L.z s=Z ∧
  regValue L.first.u s=U ∧ regValue L.first.v s=V ∧ regValue L.rest s=0

theorem dialogLoad_values (L : DialogLayout) (p : Nat) (hw : L.Widths) (hn : L.wires.Nodup)
    (hp : p<2^L.first.u.length) (B : Bool) (X Y Z U V : Nat) (hV : V<2^256) :
    Triple (DialogValues L B X Y Z U V) (dialogLoad L p)
      (DialogValues L B X Y Z (U ^^^ p) (V ^^^ (if B then X else 1))) := by
  intro s m h
  have hc := dialogLoad_correct L p hw hn hp s m
  have hv : L.first.v=L.vLow++[L.first.high.v] := by
    simp [DialogLayout.vLow,KaliskiRoundLayout.v,KaliskiRoundLayout.data,RoundDataLayout.v,
      RoundDataLayout.reg,RoundBit.get]
  have hvl : L.vLow.length=256 := by simp [DialogLayout.vLow,hw.low]
  have hh := (regValue_low_iff L.vLow [L.first.high.v] s.basis V (by simpa [hvl] using hV)).mp
    (by simpa only [←hv] using h.2.2.2.2.2.1)
  have hn' := L.ready_perm.nodup_iff.mpr hn
  have keep (w : Wire) (hm : w∈L.control::L.x++L.y++L.z++L.rest++[L.first.high.v]) :
      (run (dialogLoad L p) m s).basis w=s.basis w := by
    apply hc.2.1
    · intro hu
      have a := List.count_pos_iff.mpr hm
      have b := List.count_pos_iff.mpr hu
      have c := List.nodup_iff_count.mp hn' w
      rw [hv] at c
      simp only [List.count_cons,List.count_append,List.count_nil] at a c
      omega
    · intro hl
      have a := List.count_pos_iff.mpr hm
      have b := List.count_pos_iff.mpr hl
      have c := List.nodup_iff_count.mp hn' w
      rw [hv] at c
      simp only [List.count_cons,List.count_append,List.count_nil] at a c
      omega
  have regkeep (r : List Wire) (hr : r⊆L.control::L.x++L.y++L.z++L.rest++[L.first.high.v]) :
      regValue r (run (dialogLoad L p) m s).basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw => keep w (hr hw))
  refine ⟨hc.1,(keep _ (by simp)).trans h.1,
    (regkeep _ (by intro w hw; simp [hw])).trans h.2.1,
    (regkeep _ (by intro w hw; simp [hw])).trans h.2.2.1,
    (regkeep _ (by intro w hw; simp [hw])).trans h.2.2.2.1,?_,?_,
    (regkeep _ (by intro w hw; simp [hw])).trans h.2.2.2.2.2.2⟩
  · exact hc.2.2.1.trans (by rw [h.2.2.2.2.1])
  · rw [hv,regValue_append,regkeep [L.first.high.v] (by intro w hw; simp only [List.mem_singleton] at hw; subst w; simp),hh.2,Nat.mul_zero,Nat.add_zero,
      hc.2.2.2,hh.1,h.1,h.2.1]

end ECDSAAdd.Arithmetic
