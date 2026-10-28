import ECDSAAdd.Arithmetic.PointInPlaceSteps

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y A : Fp) (G E Q : Bool)
include hw hn

theorem pointStep_zero :
    Triple (PointInPlaceValues L X Y A G E Q)
      (equalConstant L.core.generic L.core.equalX L.inPlaceXZero 0)
      (PointInPlaceValues L X Y A G (E ^^ (G && decide (X=0))) Q) := by
  have hnd : (L.core.generic::L.core.equalX::L.point.x++L.inPlaceBorrow.take 256).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    have hb := L.inPlaceBorrow_count q
    have ht := (List.take_sublist 256 L.inPlaceBorrow).count_le q
    simp only [PointAddLayout.pointWires,inPlaceFlags,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  intro s m v
  have hclean : regValue (L.inPlaceBorrow.take 256) s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => (regValue_zero _ _).mp v.borrow q ((List.take_sublist _ _).subset hq))
  have hh := equalPorts_correct L.core.generic L.core.equalX L.point.x (L.inPlaceBorrow.take 256) 0
    (by rw [show L.point.x.length=256 from hw.inputX]; simp [L.inPlaceBorrow_length hw]) hnd (by positivity) s m hclean
  have he : (ZMod.val X=0) ↔ X=0 := ⟨fun h => ZMod.val_injective p (h.trans ZMod.val_zero.symm),fun h => by simp [h]⟩
  change run (equalConstant L.core.generic L.core.equalX L.inPlaceXZero 0) m s=_ at hh
  refine ⟨by rw [hh],v.withEqual hw hn ?_ ?_⟩
  · rw [hh]
    simp [writeBit,v.equal,v.generic,show regValue L.point.x s.basis=ZMod.val X from v.x,he]
  · intro q hq
    rw [hh]
    simp [writeBit,hq]

theorem pointStep_quotient :
    Triple (PointInPlaceValues L X Y A G E Q)
      [.CX L.core.generic L.core.equalNegY,.CX L.core.equalX L.core.equalNegY]
      (PointInPlaceValues L X Y A G E ((Q ^^ G) ^^ E)) := by
  have hne : L.core.equalX≠L.core.equalNegY := by
    intro he
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) L.core.equalNegY
    simp only [inPlaceFlags,he,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  intro s m v
  refine ⟨rfl,v.withQuotient hw hn ?_ ?_⟩
  · simp [run,writeBit,hne,v.generic,v.equal,v.quotient]
  · intro q hq
    simp [run,writeBit,hq]

theorem pointStep_clearSlope (k : Fp) (hA : A=(if E then k else 0)) :
    Triple (PointInPlaceValues L X Y A G E Q) (maskedConstant L.core.equalX L.inPlaceSlope k.val)
      (PointInPlaceValues L X Y 0 G E Q) := by
  have hs : L.inPlaceSlope.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    simp only [List.count_append] at h
    omega
  have he : L.core.equalX∉L.inPlaceSlope := by
    intro hh
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) L.core.equalX
    have hp := List.count_pos_iff.mpr hh
    simp only [inPlaceFlags,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have hk : k.val<2^L.inPlaceSlope.length := by
    rw [L.inPlaceSlope_length hw]
    exact k.isLt.trans (by norm_num [p])
  intro s m v
  obtain ⟨hp,hf,hv⟩ := maskedConstant_correct L.core.equalX L.inPlaceSlope k.val hs he hk s m
  refine ⟨hp,v.withSlope hw hn ?_ hf⟩
  have hh : regValue L.inPlaceSlope s.basis=(if E then k.val else 0) := by
    rw [v.slope,hA]
    cases E <;> rfl
  simpa only [v.equal,hh,Nat.xor_self,ZMod.val_zero] using hv

end ECDSAAdd.Arithmetic
