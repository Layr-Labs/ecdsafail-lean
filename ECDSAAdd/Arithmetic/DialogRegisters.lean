import ECDSAAdd.Arithmetic.DialogLayoutProof

namespace ECDSAAdd.Arithmetic

private theorem value_data_count (L : RoundDataLayout) (w : Wire) :
    L.valueUsedWires.count w=
      (L.cin::(L.u++L.v++L.reg .y++L.reg .carry++L.reg .zero)).count w := by
  rcases L with ⟨bs,cin⟩
  induction bs with
  | nil => simp [RoundDataLayout.valueUsedWires,RoundDataLayout.u,RoundDataLayout.v,RoundDataLayout.reg]
  | cons b bs ih =>
    simp [RoundDataLayout.valueUsedWires,RoundDataLayout.u,RoundDataLayout.v,
      RoundDataLayout.reg,RoundBit.valueUsedWires,RoundBit.get,List.count_cons] at ih ⊢
    omega

namespace DialogLayout

def external (L : DialogLayout) : List Wire := L.control::L.x++L.y++L.z

theorem external_value_perm (L : DialogLayout) :
    (L.external++L.first.valueTapeWires L.records).Perm L.wires := by
  apply List.Perm.trans ?_ L.registerWires_perm
  apply List.perm_iff_count.mpr
  intro w
  have hd := value_data_count L.first.data w
  have hc := L.first.counter.interface_perm.count_eq w
  have hdc : L.first.data.cin=L.first.cin := rfl
  have hcc : L.first.counter.cin=L.first.active := rfl
  rw [hdc] at hd
  rw [hcc] at hc
  have hr : L.first.r=L.x++[L.control] := by
    simp [KaliskiRoundLayout.r,KaliskiRoundLayout.data,RoundDataLayout.r,RoundDataLayout.reg,
      x,control,RoundBit.get]
  simp only [external,registerWires,KaliskiRoundLayout.valueTapeWires,KaliskiRoundLayout.valueSharedWires,
    hr,List.count_append,List.count_cons,List.count_nil,KaliskiRoundLayout.k,KaliskiRoundLayout.kNext,KaliskiRoundLayout.u,KaliskiRoundLayout.v] at hd hc ⊢
  omega

theorem external_value_disjoint (L : DialogLayout) (hn : L.wires.Nodup) :
    L.external.Disjoint (L.first.valueTapeWires L.records) :=
  (List.nodup_append'.mp (L.external_value_perm.nodup_iff.mpr hn)).2.2

theorem external_nodup (L : DialogLayout) (hn : L.wires.Nodup) : L.external.Nodup :=
  (List.nodup_append'.mp (L.external_value_perm.nodup_iff.mpr hn)).1

end DialogLayout
end ECDSAAdd.Arithmetic
