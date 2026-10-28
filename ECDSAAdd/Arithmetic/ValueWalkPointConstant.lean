/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
import ECDSAAdd.Arithmetic.PointDialogLayout
import ECDSAAdd.Arithmetic.PointInPlaceConstant

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def valueWalkPointDialogConstantAdd (L : ControlledPointLayout) (r : List Wire) (k : Fp) : Program :=
  maskedConstant L.core.generic (L.dialogUnary r).a k.val ++
    modAddInPlace (L.dialogUnary r) p ++ maskedConstant L.core.generic (L.dialogUnary r).a k.val

/-- 常数加法在低256位上给出规范结果，源、目标高位及其余线路逐线恢复。 -/
theorem valueWalkPointDialogConstantAdd_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y)
    (k : Fp) (Z : Nat) (B : Bool) (hZ : Z<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hz : regValue r s.basis=Z)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (valueWalkPointDialogConstantAdd L r k) m s).phase=s.phase ∧
      regValue r (run (valueWalkPointDialogConstantAdd L r k) m s).basis=(Z+(if B then k.val else 0))%p ∧
      ∀ q∉r,(run (valueWalkPointDialogConstantAdd L r k) m s).basis q=s.basis q := by
  let M := L.dialogUnary r
  have hl : r.length=256 := by rcases hr with rfl | rfl; exact hw.inputX; exact hw.inputY
  have hM := L.dialogUnary_widths hw r hl
  have hnm : (L.core.generic::M.wires).Nodup := L.dialogUnary_nodup hw hnd r hr
  have hs : L.dialogPool.take 257++[L.core.poolWire 257]++M.work ⊆ L.dialogPool := by
    change (L.dialogUnary r).a++[(L.dialogUnary r).high]++(L.dialogUnary r).work ⊆ _
    rw [L.dialogUnary_borrow hw r]
    exact (List.take_sublist _ _).subset
  have clean := (regValue_zero _ _).mp hc
  have hhigh : s.basis (L.core.poolWire 257)=false := clean _ (hs (by simp))
  have ha : M.a=L.dialogPool.take 257 := by simp only [M,dialogUnary]
  have hsource : regValue M.a s.basis=0 := by
    rw [ha]
    exact (regValue_zero _ _).mpr
      (fun q hq => clean q (hs (List.mem_append_left _ (List.mem_append_left _ hq))))
  have hwork : regValue M.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_right _ hq)))
  have hout : regValue M.z s.basis=Z := by
    simp only [M,dialogUnary,ModInPlaceLayout.z,ModAddCoreLayout.z]
    rw [regValue_append,hz]
    simp [regValue,hhigh]
  obtain ⟨hp,hv⟩ := constant_program_spec M L.core.generic k.val Z B hM hnm k.isLt hZ
    s m ⟨⟨⟨hb,hsource⟩,hout⟩,hwork⟩
  have keep := constant_program_frame M L.core.generic k.val Z B hM hnm k.isLt hZ s m hb hsource hout hwork
  have hzView : M.z=r++[L.core.poolWire 257] := by
    simp only [M,dialogUnary,ModInPlaceLayout.z,ModAddCoreLayout.z]
  rw [hzView] at hv
  have hlow := (regValue_low_iff r [L.core.poolWire 257]
    (run (valueWalkPointDialogConstantAdd L r k) m s).basis ((Z+(if B then k.val else 0))%p)
    (by rw [hl]; exact (Nat.mod_lt _ (by norm_num [p])).trans (by norm_num [p]))).mp hv.1.2
  refine ⟨hp,hlow.1,?_⟩
  intro q hq
  by_cases he : q=L.core.poolWire 257
  · subst q
    exact ((regValue_zero _ _).mp hlow.2 _ (by simp)).trans hhigh.symm
  · apply keep q
    simp only [M,dialogUnary,ModInPlaceLayout.z,ModAddCoreLayout.z]
    simp [hq,he]

end ECDSAAdd.Arithmetic
