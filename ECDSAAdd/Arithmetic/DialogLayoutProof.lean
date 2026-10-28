import ECDSAAdd.Arithmetic.DialogLayout

namespace ECDSAAdd.Arithmetic

private theorem data_count (L : RoundDataLayout) (w : Wire) :
    L.wires.count w=(L.cin::(L.u++L.v++L.r++L.s++L.reg .y++L.reg .out++L.reg .carry++L.reg .zero)).count w := by
  rcases L with ⟨bs,cin⟩
  induction bs with
  | nil => simp [RoundDataLayout.wires,RoundDataLayout.u,RoundDataLayout.v,
      RoundDataLayout.r,RoundDataLayout.s,RoundDataLayout.reg]
  | cons b bs ih =>
    simp [RoundDataLayout.wires,RoundDataLayout.u,RoundDataLayout.v,
      RoundDataLayout.r,RoundDataLayout.s,RoundDataLayout.reg,RoundBit.wires,RoundBit.get,
      List.count_cons] at ih ⊢
    omega

namespace DialogLayout

/-- 将旧视图按物理字段展开，供所有借用互异与包含关系核对。 -/
def registerWires (L : DialogLayout) : List Wire :=
  L.records.flatMap RoundRecord.wires ++ [L.first.done,L.first.oddWork,L.first.bothWork,L.first.compareCin] ++
  [L.first.cin] ++ L.first.u ++ L.first.v ++ L.first.r ++ L.y ++
  L.first.data.reg .y ++ L.z ++ L.first.data.reg .carry ++ L.first.data.reg .zero ++
  [L.first.active] ++ L.first.k ++ L.first.counter.y ++ L.first.kNext ++ L.first.counter.carry

theorem registerWires_perm (L : DialogLayout) : L.registerWires.Perm L.wires := by
  apply List.perm_iff_count.mpr
  intro w
  have hd := data_count L.first.data w
  have hc := L.first.counter.interface_perm.count_eq w
  have hdc : L.first.data.cin = L.first.cin := rfl
  have hcc : L.first.counter.cin = L.first.active := rfl
  rw [hdc] at hd
  rw [hcc] at hc
  simp only [registerWires,wires,KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,
    List.count_append,List.count_cons,List.count_nil,KaliskiRoundLayout.k,KaliskiRoundLayout.kNext,
    KaliskiRoundLayout.u,KaliskiRoundLayout.v,KaliskiRoundLayout.r,KaliskiRoundLayout.s,y,z] at hd hc ⊢
  omega

theorem replay_valid (L : DialogLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.replay.Valid 256 L.records := by
  have hreg := L.registerWires_perm.nodup_iff.mpr hn
  have count (w : Wire) := List.nodup_iff_count.mp hreg w
  have hy (w : Wire) := (List.take_sublist 247 (L.first.data.reg .y)).count_le w
  have hz (w : Wire) := (List.take_sublist 247 (L.first.data.reg .zero)).count_le w
  have hcarry (w : Wire) : (L.first.data.reg .carry).count w=
      (L.first.low.map (·.carry) ++ [L.first.high.carry]).count w := by
    simp [KaliskiRoundLayout.data,RoundDataLayout.reg,RoundBit.get]
  refine ⟨L.payload_widths hw,hw.counter,?_,?_,?_,?_,?_⟩
  · apply List.nodup_iff_count.mpr
    intro w
    have hh := count w
    have hyt := hy w
    have hzt := hz w
    have hc := hcarry w
    simp only [registerWires,replay,ReplayLayout.wires,ModInPlaceLayout.wires,
      ModInPlaceLayout.work,ModInPlaceLayout.z,ModAddCoreLayout.work,ModAddCoreLayout.z,payload,
      List.count_append,List.count_cons,List.count_nil] at hh hc ⊢
    have hs : (L.first.low.map (·.s) ++ [L.first.high.s]).count w=L.y.count w := by
      simp [y,KaliskiRoundLayout.s,KaliskiRoundLayout.data,RoundDataLayout.s,RoundDataLayout.reg,RoundBit.get]
    simp only [List.count_append,List.count_cons,List.count_nil] at hs
    simp only [KaliskiRoundLayout.k,AdderLayout.x] at hh ⊢
    omega
  · apply List.nodup_iff_count.mpr
    intro w
    have hh := count w
    have hc := hcarry w
    have ha := L.first.counter.interface_perm.count_eq w
    simp only [registerWires,replay,AdderLayout.wires,List.count_append,List.count_cons,List.count_nil] at hh hc ⊢
    simp only [AdderLayout.wires,List.count_append,List.count_cons] at ha
    have hci : L.first.counter.cin=L.first.active := rfl
    rw [hci] at ha
    simp only [KaliskiRoundLayout.k,KaliskiRoundLayout.kNext] at hh
    omega
  · intro w hwm
    change w∈L.first.counter.y at hwm
    simp [replay,payload,ModInPlaceLayout.work,ModAddCoreLayout.work,hwm]
  · intro w hwm
    change w∈L.first.counter.carry at hwm
    simp [replay,payload,ModInPlaceLayout.work,ModAddCoreLayout.work,hwm]
  · simp [replay,payload,ModInPlaceLayout.work,ModAddCoreLayout.work]

end DialogLayout
end ECDSAAdd.Arithmetic
