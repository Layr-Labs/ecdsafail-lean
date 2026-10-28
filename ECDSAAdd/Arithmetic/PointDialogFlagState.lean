import ECDSAAdd.Arithmetic.PointDialogBoundarySteps

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def dialogFlagState (L : ControlledPointLayout) (O D I G E H K : Bool) : BasisState :=
  writeBit (writeBit (writeBit (writeBit (writeBit (writeBit (writeBit (fun _=>false)
    L.infinitySelect O) L.doubleSelect D) L.genericSelect I) L.core.generic G)
      L.core.equalX E) L.core.equalNegY H) L.core.double K

private theorem flag_reads (o d i g e h k : Wire) (hn : [o,d,i,g,e,h,k].Nodup)
    (O D I G E H K : Bool) :
    let f := writeBit (writeBit (writeBit (writeBit (writeBit (writeBit (writeBit (fun _=>false)
      o O) d D) i I) g G) e E) h H) k K
    f o=O ∧ f d=D ∧ f i=I ∧ f g=G ∧ f e=E ∧ f h=H ∧ f k=K := by
  simp only [List.nodup_cons,List.mem_cons,not_or] at hn
  simp_all [writeBit]

theorem dialogFlagState_read (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (O D I G E H K : Bool) :
    let f := dialogFlagState L O D I G E H K
    f L.infinitySelect=O ∧ f L.doubleSelect=D ∧ f L.genericSelect=I ∧
      f L.core.generic=G ∧ f L.core.equalX=E ∧ f L.core.equalNegY=H ∧ f L.core.double=K := by
  have hh : L.inPlaceFlags.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    simp only [dialogUsedWires,List.count_append] at h
    omega
  exact flag_reads _ _ _ _ _ _ _ hh O D I G E H K

theorem dialogFlagState_zero (L : ControlledPointLayout) :
    dialogFlagState L false false false false false false false=(fun _=>false) := by
  funext q
  simp [dialogFlagState,writeBit]

theorem PointDialogBoundary.congrFlags {L : ControlledPointLayout} {R : Point} {b : Bool}
    {f f' s : BasisState} (v : PointDialogBoundary L R b f s)
    (he : ∀q,q∈L.inPlaceFlags → f q=f' q) : PointDialogBoundary L R b f' s :=
  ⟨v.point,v.control,fun q hq=>(v.flags q hq).trans (he q hq),v.clean⟩

/-- 只比较七个真实标志位，不对函数在池外的取值施加要求。 -/
theorem dialogFlagState_update (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (O D I G E H K T : Bool) :
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.infinitySelect T q=dialogFlagState L T D I G E H K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.doubleSelect T q=dialogFlagState L O T I G E H K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.genericSelect T q=dialogFlagState L O D T G E H K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.core.generic T q=dialogFlagState L O D I T E H K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.core.equalX T q=dialogFlagState L O D I G T H K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.core.equalNegY T q=dialogFlagState L O D I G E T K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.core.double T q=dialogFlagState L O D I G E H T q) := by
  have hnd : L.inPlaceFlags.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    simp only [dialogUsedWires,List.count_append] at h
    omega
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at hnd
  repeat' constructor
  all_goals
    intro q hq
    simp only [inPlaceFlags,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [dialogFlagState,writeBit,eq_comm]

end ECDSAAdd.Arithmetic
