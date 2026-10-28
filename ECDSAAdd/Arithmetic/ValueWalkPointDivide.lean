/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
import ECDSAAdd.Arithmetic.PointDialogLayout

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 同一原地乘除视图；目标高位归零后，只有低256位载荷改变。 -/
theorem valueWalkPointDialog_arithmetic_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let circuit := if multiply then dialogMultiply L.dialogPort p else dialogDivide L.dialogPort p
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run circuit m s).phase=s.phase ∧ regValue L.point.y (run circuit m s).basis=V ∧
      ∀ q∉L.point.y,(run circuit m s).basis q=s.basis q := by
  dsimp only
  let D := L.dialogPort
  have hd : D.Widths := DialogLayout.fromPool_widths _ _ _ _
  have nd := L.dialogPort_nodup hw hn
  have fields := L.dialogPort_fields hw
  have hwork : D.work ⊆ L.dialogPool := fun {_} h =>
    (List.take_subset 2612 L.dialogPool) ((L.dialogPort_work hw).subset h)
  have highMem : L.core.poolWire 2612∈L.dialogPool := by
    have h := L.dialogBit_prefix hw 2612 (by omega)
    have hh : L.core.poolWire 2612∈L.dialogPool.take 2612++[L.core.poolWire 2612] := by simp
    rw [h] at hh
    exact List.take_subset _ _ hh
  have hhigh := (regValue_zero _ _).mp hc _ highMem
  have hyD : regValue D.y s.basis=Y := by
    rw [fields.2.2,regValue_append,hy]; simp [regValue,hhigh]
  have hcD : regValue D.work s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (hwork hq))
  have hbD : s.basis D.control=B := fields.1 ▸ hb
  have hxD : regValue D.x s.basis=X := fields.2.1 ▸ hx
  have hv :
      (run (if multiply then dialogMultiply D p else dialogDivide D p) m s).phase=s.phase ∧
      Holds.holds (run (if multiply then dialogMultiply D p else dialogDivide D p) m s).basis
        D.control B ∧
      regValue D.x (run (if multiply then dialogMultiply D p else dialogDivide D p) m s).basis=X ∧
      regValue D.y (run (if multiply then dialogMultiply D p else dialogDivide D p) m s).basis=
        (if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y) ∧
      regValue D.work (run (if multiply then dialogMultiply D p else dialogDivide D p) m s).basis=0 := by
    cases multiply
    · simpa only [Bool.false_eq_true,if_false,Holds.holds,and_assoc] using
        dialogDivide_spec D hd nd B X Y hX hX0 hY s m ⟨⟨⟨hbD,hxD⟩,hyD⟩,hcD⟩
    · simpa only [if_true,Holds.holds,and_assoc] using
        dialogMultiply_spec D hd nd B X Y hX hX0 hY s m ⟨⟨⟨hbD,hxD⟩,hyD⟩,hcD⟩
  have bound : (if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y)<p := by
    split
    · split <;> exact ZMod.val_lt _
    · exact hY
  have low := (regValue_low_iff L.point.y [L.core.poolWire 2612] _
    _ (by rw [show L.point.y.length=256 from hw.inputY]; exact bound.trans (by norm_num [p]))).mp
    (fields.2.2 ▸ hv.2.2.2.1)
  refine ⟨hv.1,low.1,?_⟩
  intro q hq
  by_cases hg : q=D.control
  · subst q; exact hv.2.1.trans hbD.symm
  by_cases hxx : q∈D.x
  · exact (regValue_eq_iff _ _ _).mp (hv.2.2.1.trans hxD.symm) q hxx
  by_cases hh : q=L.core.poolWire 2612
  · subst q; exact ((regValue_zero _ _).mp low.2 _ (by simp)).trans hhigh.symm
  by_cases hwq : q∈D.work
  · exact (regValue_eq_iff _ _ _).mp (hv.2.2.2.2.trans hcD.symm) q hwq
  have outside : q∉D.wires := by
    intro mem
    have h := D.external_value_perm.mem_iff.mpr mem
    have hrest : q∉D.first.valueTapeWires D.records := fun hh =>
      hwq (List.mem_append_left _ hh)
    have hz : q∉D.z := fun hh => hwq (List.mem_append_right _ hh)
    change q∈(D.control::D.x++D.y++D.z)++D.first.valueTapeWires D.records at h
    simp only [List.mem_append,List.mem_cons] at h
    have hyq : q∉D.y := by rw [fields.2.2]; simp [hq,hh]
    rcases h with (((hg' | hx') | hy') | hz') | hr
    · exact hg hg'
    · exact hxx hx'
    · exact hyq hy'
    · exact hz hz'
    · exact hrest hr
  have frame := dialog_frame D p hd nd s m q outside
  dsimp only [D] at frame
  by_cases hm : multiply=true
  · rw [if_pos hm]; exact frame.2
  · rw [if_neg hm]; exact frame.1
end ECDSAAdd.Arithmetic
