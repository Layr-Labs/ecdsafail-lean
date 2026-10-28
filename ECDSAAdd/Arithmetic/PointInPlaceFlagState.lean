import ECDSAAdd.Arithmetic.PointInPlaceCorners

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 按现有七个字段列出阶段标志；e/q在完整普通分支边界均零。 -/
def inPlaceFlagState (L : ControlledPointLayout) (O D I G H : Bool) : BasisState :=
  writeBit (writeBit (writeBit (writeBit (writeBit (fun _ => false)
    L.infinitySelect O) L.doubleSelect D) L.genericSelect I) L.core.generic G) L.core.double H

private theorem flagState_read (o d i g e q h : Wire) (hn : [o,d,i,g,e,q,h].Nodup)
    (O D I G H : Bool) :
    let f := writeBit (writeBit (writeBit (writeBit (writeBit (fun _ => false) o O) d D) i I) g G) h H
    f o=O ∧ f d=D ∧ f i=I ∧ f g=G ∧ f e=false ∧ f q=false ∧ f h=H := by
  simp only [List.nodup_cons,List.mem_cons,not_or] at hn
  simp_all [writeBit,eq_comm]

theorem inPlaceFlagState_read (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (O D I G H : Bool) :
    let f := inPlaceFlagState L O D I G H
    f L.infinitySelect=O ∧ f L.doubleSelect=D ∧ f L.genericSelect=I ∧
      f L.core.generic=G ∧ f L.core.equalX=false ∧ f L.core.equalNegY=false ∧ f L.core.double=H := by
  have hh : L.inPlaceFlags.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    simp only [List.count_append] at h
    omega
  exact flagState_read _ _ _ _ _ _ _ hh O D I G H

private theorem flagState_update (o d i g h : Wire) (hn : [o,d,i,g,h].Nodup)
    (O D I G H T : Bool) :
    let f O D I G H := writeBit (writeBit (writeBit (writeBit (writeBit (fun _ => false) o O) d D) i I) g G) h H
    writeBit (f O D I G H) o T=f T D I G H ∧
    writeBit (f O D I G H) d T=f O T I G H ∧
    writeBit (f O D I G H) i T=f O D T G H ∧
    writeBit (f O D I G H) g T=f O D I T H ∧
    writeBit (f O D I G H) h T=f O D I G T := by
  simp only [List.nodup_cons,List.mem_cons,not_or] at hn
  dsimp only
  repeat' constructor
  all_goals
    funext w
    by_cases ho : w=o <;> by_cases hd : w=d <;> by_cases hi : w=i <;>
      by_cases hg : w=g <;> by_cases hh : w=h <;> simp_all [writeBit,Function.update_apply,eq_comm]

theorem inPlaceFlagState_update (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (O D I G H T : Bool) :
    writeBit (inPlaceFlagState L O D I G H) L.infinitySelect T=inPlaceFlagState L T D I G H ∧
    writeBit (inPlaceFlagState L O D I G H) L.doubleSelect T=inPlaceFlagState L O T I G H ∧
    writeBit (inPlaceFlagState L O D I G H) L.genericSelect T=inPlaceFlagState L O D T G H ∧
    writeBit (inPlaceFlagState L O D I G H) L.core.generic T=inPlaceFlagState L O D I T H ∧
    writeBit (inPlaceFlagState L O D I G H) L.core.double T=inPlaceFlagState L O D I G T := by
  have hh : [L.infinitySelect,L.doubleSelect,L.genericSelect,L.core.generic,L.core.double].Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    simp only [inPlaceFlags,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  exact flagState_update _ _ _ _ _ hh O D I G H T

theorem inPlaceFlagState_zero (L : ControlledPointLayout) : inPlaceFlagState L false false false false false=(fun _ => false) := by
  funext q
  simp [inPlaceFlagState,writeBit]

/-- 相同七个位值描述同一阶段断言，不约束标志表之外的函数值。 -/
theorem PointInPlaceBoundary.congrFlags {L : ControlledPointLayout} {R : Point} {b : Bool}
    {f f' s : BasisState} (v : PointInPlaceBoundary L R b f s)
    (hh : ∀ q∈L.inPlaceFlags,f q=f' q) : PointInPlaceBoundary L R b f' s :=
  ⟨v.point,v.control,fun q hq => (v.flags q hq).trans (hh q hq),v.slope,v.clean⟩

end ECDSAAdd.Arithmetic
