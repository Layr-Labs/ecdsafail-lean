import ECDSAAdd.Arithmetic.DialogSpec

namespace ECDSAAdd.Arithmetic

namespace DialogLayout

theorem replay_wires_subset (L : DialogLayout) : (L.replay.wires L.records).toFinset⊆L.wires.toFinset := by
  intro w hw
  have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hw)
  have he := L.registerWires_perm.count_eq w
  have hy := (List.take_sublist 247 (L.first.data.reg .y)).count_le w
  have hz := (List.take_sublist 247 (L.first.data.reg .zero)).count_le w
  have hcarry : (L.first.data.reg .carry).count w=
      (L.first.low.map (·.carry) ++ [L.first.high.carry]).count w := by
    simp [KaliskiRoundLayout.data,RoundDataLayout.reg,RoundBit.get]
  have hs : (L.first.low.map (·.s) ++ [L.first.high.s]).count w=L.y.count w := by
    simp [y,KaliskiRoundLayout.s,KaliskiRoundLayout.data,RoundDataLayout.s,RoundDataLayout.reg,RoundBit.get]
  apply List.mem_toFinset.mpr
  apply List.count_pos_iff.mp
  simp only [replay,ReplayLayout.wires,payload,ModInPlaceLayout.wires,ModInPlaceLayout.work,
    ModInPlaceLayout.z,ModAddCoreLayout.z,ModAddCoreLayout.work,registerWires,
    List.count_append,List.count_cons,List.count_nil,KaliskiRoundLayout.k,AdderLayout.x] at h he hs hcarry
  omega

theorem external_subset (L : DialogLayout) : L.external.toFinset⊆L.wires.toFinset := by
  intro w hw
  exact List.mem_toFinset.mpr (L.external_value_perm.mem_iff.mp
    (List.mem_append_left _ (List.mem_toFinset.mp hw)))

end DialogLayout

private theorem dialogLoad_wires (L : DialogLayout) (p : Nat) (hw : L.Widths) :
    wires (dialogLoad L p)⊆L.wires.toFinset ∧
      (L.control::L.x).toFinset⊆wires (dialogLoad L p) := by
  have hx : L.x.length=256 := by simp [DialogLayout.x,hw.low]
  have he : L.x.isEmpty=false := by cases hh : L.x <;> simp_all
  have hl : (L.first.low.map (·.v)).length=256 := by simp [hw.low]
  have sub : (L.control::L.x++L.first.u++L.vLow++[L.first.high.v]).toFinset⊆L.wires.toFinset := by
    intro w hw
    have hv : L.first.v=L.vLow++[L.first.high.v] := by
      simp [DialogLayout.vLow,KaliskiRoundLayout.v,KaliskiRoundLayout.data,RoundDataLayout.v,RoundDataLayout.reg,RoundBit.get]
    apply List.mem_toFinset.mpr
    apply L.ready_perm.mem_iff.mp
    simpa only [hv,List.mem_cons,List.mem_append,List.mem_singleton] using
      (show w∈L.control::L.x++L.y++L.z++L.first.u++(L.vLow++[L.first.high.v])++L.rest from by
        have hm := List.mem_toFinset.mp hw
        simp only [List.mem_cons,List.mem_append] at hm ⊢
        tauto)
  unfold dialogLoad
  split
  · simp_all
  · rename_i h t ht
    have hs := copyRegister_wires (some L.control) L.x (h::t) (by rw [hx,←ht,hl])
    rw [he] at hs
    simp only [Bool.false_eq_true,if_false,Option.toList_some] at hs
    have hv : L.vLow=h::t := ht
    simp only [wires_append,safeDivisor,wires_append,hs]
    constructor
    · intro w hwm
      rcases Finset.mem_union.mp hwm with hc|hr
      · have hm := List.mem_toFinset.mp (xorConstant_wires_subset _ _ hc)
        exact sub (by simp [hm])
      · apply sub
        simp [wires,Instr.wires] at hr
        simp only [List.mem_toFinset,List.mem_cons,List.mem_append,hv]
        tauto
    · intro w hwm
      apply Finset.mem_union_right
      apply Finset.mem_union_right
      simpa only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc] using
        (show w=L.control ∨ w∈L.x ∨ w∈h::t from by
          have hm := List.mem_toFinset.mp hwm
          simp only [List.mem_cons] at hm
          tauto)

/-- 完整乘除触及同一个紧凑物理集合，计数使用该集合而非旧分配池。 -/
theorem dialog_wires (L : DialogLayout) (p : Nat) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (dialogDivide L p)=L.wires.toFinset ∧ wires (dialogMultiply L p)=L.wires.toFinset := by
  have hd : L.first.data.width=257 := by simp [KaliskiRoundLayout.data,RoundDataLayout.width,hw.low]
  have hv := valueLoop_wires L.first L.records 0 hw.counter (by omega) (by omega)
  have he : L.records.isEmpty=false := by
    cases hh : L.records with
    | nil => have hz := hw.records; rw [hh] at hz; contradiction
    | cons _ _ => rfl
  simp only [he,Bool.false_eq_true,if_false] at hv
  have hr := replayLoop_wires_subset L.replay 256 p 0 L.records (L.replay_valid hw hn) (by omega)
  have hr1 := hr.1.trans L.replay_wires_subset
  have hr2 := hr.2.trans L.replay_wires_subset
  have hl := dialogLoad_wires L p hw
  have hyz : L.y.length=L.z.length := by
    simp [DialogLayout.y,DialogLayout.z,KaliskiRoundLayout.s,RoundDataLayout.s,RoundDataLayout.reg]
  have hyl : L.y.length=257 := by
    simp [DialogLayout.y,KaliskiRoundLayout.s,KaliskiRoundLayout.data,RoundDataLayout.s,RoundDataLayout.reg,hw.low]
  have hye : L.y.isEmpty=false := by cases hh : L.y <;> simp_all
  have hze : L.z.isEmpty=false := by cases hh : L.z <;> simp_all
  have hs : wires (exchangeRegisters L.y L.z)=(L.y++L.z).toFinset := by
    simp only [exchangeRegisters,wires_append,copyRegister_wires _ _ _ hyz,
      copyRegister_wires _ _ _ hyz.symm,hye,hze,Bool.false_eq_true,if_false,Option.toList_none,List.nil_append]
    ext w; simp only [Finset.mem_union,List.mem_toFinset,List.mem_append]; tauto
  have hvs : (L.first.valueTapeWires L.records).toFinset⊆L.wires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr ((L.first.valueTapeWires_sublist L.records).subset (List.mem_toFinset.mp hw))
  have hss : (L.y++L.z).toFinset⊆L.wires.toFinset := by
    intro w hw
    apply L.external_subset
    have hm := List.mem_toFinset.mp hw
    simp only [DialogLayout.external,List.mem_toFinset,List.mem_cons,List.mem_append] at hm ⊢
    tauto
  have base (w : Wire) (hw : w∈L.wires.toFinset) :
      w∈wires (dialogLoad L p) ∨ w∈(L.first.valueTapeWires L.records).toFinset ∨ w∈(L.y++L.z).toFinset := by
    have hm := L.external_value_perm.mem_iff.mpr (List.mem_toFinset.mp hw)
    simp only [DialogLayout.external,List.mem_append,List.mem_cons] at hm
    rcases hm with (((hc|hx)|hy)|hz)|ht
    · exact Or.inl (hl.2 (by simp [hc]))
    · exact Or.inl (hl.2 (by simp [hx]))
    · exact Or.inr (Or.inr (by simp [hy]))
    · exact Or.inr (Or.inr (by simp [hz]))
    · exact Or.inr (Or.inl (List.mem_toFinset.mpr ht))
  simp only [dialogDivide,dialogMultiply,wires_append,hv.1,hv.2,hs]
  constructor <;> apply Finset.Subset.antisymm
  · intro w hw
    simp only [Finset.mem_union] at hw
    rcases hw with ((((hw|hw)|hw)|hw)|hw)|hw
    · exact hl.1 hw
    · exact hvs hw
    · exact hss hw
    · exact hr1 hw
    · exact hvs hw
    · exact hl.1 hw
  · intro w hw
    have hh := base w hw
    simp only [Finset.mem_union]
    tauto
  · intro w hw
    simp only [Finset.mem_union] at hw
    rcases hw with ((((hw|hw)|hw)|hw)|hw)|hw
    · exact hl.1 hw
    · exact hvs hw
    · exact hr2 hw
    · exact hss hw
    · exact hvs hw
    · exact hl.1 hw
  · intro w hw
    have hh := base w hw
    simp only [Finset.mem_union]
    tauto

end ECDSAAdd.Arithmetic
