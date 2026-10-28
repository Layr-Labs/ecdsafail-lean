import ECDSAAdd.Arithmetic.InverseTerminalConstants
import ECDSAAdd.Arithmetic.InverseMiddle

namespace ECDSAAdd.Arithmetic

/-- 两次Kaliski循环之间不变的控制、记录和未使用分配。 -/
def CompactFrozen (L : InverseLoopLayout) (K : Nat) (cs : List (Bool×Bool)) (s : BasisState) : Prop :=
  InversePhase L K 0 s ∧ regValue (L.middle.data.reg .out) s=0 ∧
    s L.middle.data.cin=false ∧ s L.middle.done=true ∧
    s L.middle.oddWork=false ∧ s L.middle.bothWork=false ∧ OneBitRecordsValues L.records cs s

/-- 常量清除后r为唯一数据，历史和中段借用区均为空。 -/
def CompactReady (L : InverseLoopLayout) (K R : Nat) (cs : List (Bool×Bool)) (s : BasisState) : Prop :=
  regValue L.middle.r s=R ∧ regValue L.scaleLive s=0 ∧
    regValue L.compactBorrow s=0 ∧ CompactFrozen L K cs s

namespace InverseLoopLayout

theorem compact_data_nodup (L : InverseLoopLayout) (hn : L.wires.Nodup) : L.middle.data.wires.Nodup := by
  exact (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp
    (L.middle_nodup hn)).2.1).1).2.1

theorem compact_live_data (L : InverseLoopLayout) : L.scaleLive⊆L.middle.data.wires := by
  intro w h
  simp only [scaleLive,List.mem_append] at h
  rcases h with (h|h)|h
  · exact L.middle.data.reg_mem .y h
  · exact L.middle.data.reg_mem .zero (List.mem_of_mem_take h)
  · exact L.middle.data.reg_mem .carry h

theorem compact_phase_disjoint (L : InverseLoopLayout) (hn : L.wires.Nodup) :
    L.middle.data.wires.Disjoint L.phaseWires := by
  exact List.disjoint_left.mpr (fun _ hd hp => List.disjoint_left.mp (L.rest_phase_disjoint hn)
    (List.mem_append_right _ hd) hp)

private theorem field_not_live (L : InverseLoopLayout) (hn : L.wires.Nodup)
    (f : RoundField) (hy : f≠.y) (hz : f≠.zero) (hc : f≠.carry)
    {w : Wire} (hw : w∈L.middle.data.reg f) : w∉L.scaleLive := by
  intro h
  simp only [scaleLive,List.mem_append] at h
  rcases h with (h|h)|h
  · exact List.disjoint_left.mp (L.middle.data.reg_disjoint (L.compact_data_nodup hn) f .y hy) hw h
  · exact List.disjoint_left.mp (L.middle.data.reg_disjoint (L.compact_data_nodup hn) f .zero hz) hw (List.mem_of_mem_take h)
  · exact List.disjoint_left.mp (L.middle.data.reg_disjoint (L.compact_data_nodup hn) f .carry hc) hw h

end InverseLoopLayout

theorem CompactFrozen.congr (L : InverseLoopLayout) (hn : L.wires.Nodup)
    (K : Nat) (cs : List (Bool×Bool)) (s t : BasisState) (h : CompactFrozen L K cs s)
    (he : ∀ w,w∉L.middle.r → w∉L.scaleLive → t w=s w) : CompactFrozen L K cs t := by
  have keep (w : Wire) (hw : w∉L.middle.data.wires) : t w=s w :=
    he w (fun hr => hw (L.middle.data.reg_mem .r hr))
      (fun hl => hw (L.compact_live_data hl))
  have phase : InversePhase L K 0 t := InversePhase.congr L K 0 s t h.1
    (fun w hw => keep w (fun hd => List.disjoint_left.mp (L.compact_phase_disjoint hn) hd hw))
  have hnd := L.middle_nodup hn
  have outside (w : Wire) (hw : w∈[L.middle.done,L.middle.oddWork,L.middle.bothWork]++L.records.flatMap RoundRecord.wires) :
      w∉L.middle.data.wires := by
    intro hd
    have hp := List.nodup_iff_count.mp hnd w
    have h1 := List.count_pos_iff.mpr hw
    have h2 := List.count_pos_iff.mpr hd
    simp only [KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,
      List.count_append,List.count_cons,List.count_nil] at hp h1
    omega
  refine ⟨phase,?_,?_,?_,?_,?_,?_⟩
  · apply (regValue_congr _ _ _ ?_).trans h.2.1
    intro w hw
    exact he w (List.disjoint_left.mp (L.middle.data.reg_disjoint (L.compact_data_nodup hn) .out .r (by decide)) hw)
      (L.field_not_live hn .out (by decide) (by decide) (by decide) hw)
  · apply (he _ ?_ ?_).trans h.2.2.1
    · exact L.middle.data.cin_not_mem (L.compact_data_nodup hn) .r
    · intro hl
      simp only [InverseLoopLayout.scaleLive,List.mem_append] at hl
      rcases hl with (hl|hl)|hl
      · exact L.middle.data.cin_not_mem (L.compact_data_nodup hn) .y hl
      · exact L.middle.data.cin_not_mem (L.compact_data_nodup hn) .zero (List.mem_of_mem_take hl)
      · exact L.middle.data.cin_not_mem (L.compact_data_nodup hn) .carry hl
  · exact (keep _ (outside _ (by simp))).trans h.2.2.2.1
  · exact (keep _ (outside _ (by simp))).trans h.2.2.2.2.1
  · exact (keep _ (outside _ (by simp))).trans h.2.2.2.2.2.1
  · exact OneBitRecordsValues.congr L.records cs s t h.2.2.2.2.2.2
      (fun w hw => keep w (outside w (by simp [hw])))

theorem InverseMiddle.update_data (L : InverseLoopLayout) (hn : L.wires.Nodup)
    (z z' : KState) (cs : List (Bool×Bool)) (s t : BasisState)
    (h : InverseMiddle L z cs 0 s) (hk : z'.k=z.k) (hv : z'.v=z.v)
    (hd : RoundValues L.middle.data (roundDataValues z') t)
    (he : ∀ w,w∉L.middle.data.wires → t w=s w) : InverseMiddle L z' cs 0 t := by
  have outside (w : Wire) (hw : w∈[L.middle.done,L.middle.oddWork,L.middle.bothWork]++L.records.flatMap RoundRecord.wires) :
      w∉L.middle.data.wires := by
    intro hd
    have hp := List.nodup_iff_count.mp (L.middle_nodup hn) w
    have h1 := List.count_pos_iff.mpr hw
    have h2 := List.count_pos_iff.mpr hd
    simp only [KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,
      List.count_append,List.count_cons,List.count_nil] at hp h1
    omega
  refine ⟨⟨hd,?_,?_,?_,?_⟩,?_⟩
  · rw [hv]; exact (he _ (outside _ (by simp))).trans h.1.2.1
  · exact (he _ (outside _ (by simp))).trans h.1.2.2.1
  · exact (he _ (outside _ (by simp))).trans h.1.2.2.2.1
  · exact OneBitRecordsValues.congr _ _ _ _ h.1.2.2.2.2 (fun w hw => he w (outside w (by simp [hw])))
  · rw [hk]
    exact InversePhase.congr L _ 0 s t h.2
      (fun w hw => he w (fun hd => List.disjoint_left.mp (L.compact_phase_disjoint hn) hd hw))

/-- 中段全零断言与原轮状态断言逐字段对应；不丢弃未使用字段。 -/
theorem compactReady_iff (L : InverseLoopLayout) (K R : Nat) (cs : List (Bool×Bool)) (s : BasisState) :
    CompactReady L K R cs s ↔ InverseMiddle L ⟨0,0,R,0,K⟩ cs 0 s := by
  constructor
  · rintro ⟨hr,hh,hb,hf⟩
    have hzH := (regValue_zero _ _).mp hh
    have hzB := (regValue_zero _ _).mp hb
    have zero (f : RoundField) (hn : f≠.r) (ho : f≠.out) : regValue (L.middle.data.reg f) s=0 := by
      apply (regValue_zero _ _).mpr
      intro w hw
      cases f with
      | r => exact False.elim (hn rfl)
      | out => exact False.elim (ho rfl)
      | u => exact hzB w (by simp [InverseLoopLayout.compactBorrow,KaliskiRoundLayout.u,RoundDataLayout.u,hw])
      | v => exact hzB w (by simp [InverseLoopLayout.compactBorrow,KaliskiRoundLayout.v,RoundDataLayout.v,hw])
      | s => exact hzB w (by simp [InverseLoopLayout.compactBorrow,KaliskiRoundLayout.s,RoundDataLayout.s,hw])
      | y => exact hzH w (by simp [InverseLoopLayout.scaleLive,hw])
      | carry => exact hzH w (by simp [InverseLoopLayout.scaleLive,hw])
      | zero =>
        have hp := hw
        rw [←List.take_append_drop 4 (L.middle.data.reg .zero),List.mem_append] at hp
        rcases hp with hp|hp
        · exact hzH w (by simp [InverseLoopLayout.scaleLive,hp])
        · exact hzB w (by simp [InverseLoopLayout.compactBorrow,hp])
    refine ⟨⟨⟨?_,hf.2.2.1⟩,hf.2.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2.1,hf.2.2.2.2.2.2⟩,hf.1⟩
    intro f
    cases f with
    | r => exact hr
    | out => exact hf.2.1
    | u => exact zero .u (by decide) (by decide)
    | v => exact zero .v (by decide) (by decide)
    | s => exact zero .s (by decide) (by decide)
    | y => exact zero .y (by decide) (by decide)
    | carry => exact zero .carry (by decide) (by decide)
    | zero => exact zero .zero (by decide) (by decide)
  · intro h
    have zero (f : RoundField) (hf : f≠.r) (w : Wire) (hw : w∈L.middle.data.reg f) : s w=false := by
      have hv : regValue (L.middle.data.reg f) s=0 := by
        have hv := h.1.1.1 f
        cases f <;> simp_all [roundDataValues]
      exact (regValue_zero _ _).mp hv w hw
    refine ⟨h.1.1.1 .r,?_,?_,h.2,h.1.1.1 .out,h.1.1.2,h.1.2.1,h.1.2.2.1,h.1.2.2.2.1,h.1.2.2.2.2⟩
    · apply (regValue_zero _ _).mpr
      intro w hw
      simp only [InverseLoopLayout.scaleLive,List.mem_append] at hw
      rcases hw with (hw|hw)|hw
      · exact zero .y (by decide) w hw
      · exact zero .zero (by decide) w (List.mem_of_mem_take hw)
      · exact zero .carry (by decide) w hw
    · apply (regValue_zero _ _).mpr
      intro w hw
      simp only [InverseLoopLayout.compactBorrow,List.mem_append] at hw
      rcases hw with (((hw|hw)|hw)|hw)|hw
      · exact zero .u (by decide) w hw
      · exact zero .v (by decide) w hw
      · exact zero .s (by decide) w hw
      · exact zero .zero (by decide) w (List.mem_of_mem_drop hw)
      · exact (regValue_zero _ _).mp h.2.1.2.2 w (List.mem_append_right _ (List.mem_of_mem_take hw))

theorem compactConstants_values (L : InverseLoopLayout) (hn : L.wires.Nodup)
    (hl : L.first.low.length=256) (q R K : Nat) (hq : q<2^256) (cs : List (Bool×Bool)) :
    Triple (InverseMiddle L ⟨1,0,R,q,K⟩ cs 0) (terminalConstants L q) (CompactReady L K R cs) ∧
    Triple (CompactReady L K R cs) (terminalConstants L q) (InverseMiddle L ⟨1,0,R,q,K⟩ cs 0) := by
  have step (U S : Nat) : Triple (InverseMiddle L ⟨U,0,R,S,K⟩ cs 0) (terminalConstants L q)
      (InverseMiddle L ⟨U^^^1,0,R,S^^^q,K⟩ cs 0) := by
    intro st m h
    obtain ⟨hp,hu,hs,he⟩ := terminalConstants_correct L hn hl q hq st m
    have hu0 : regValue L.middle.u st.basis=U := h.1.1.1 .u
    have hs0 : regValue L.middle.s st.basis=S := h.1.1.1 .s
    refine ⟨hp,InverseMiddle.update_data L hn _ _ cs _ _ h rfl rfl ?_ ?_⟩
    · have hv := RoundValues.update_two L.middle.data (L.compact_data_nodup hn) _ .u .s
        (U^^^1) (S^^^q) _ _ h.1.1 he
        (by simpa only [hu0] using hu) (by simpa only [hs0] using hs)
      convert hv using 1
      funext f; cases f <;> simp [roundDataValues,Function.update]
    · intro w hw
      exact he w (fun hh => hw (L.middle.data.reg_mem .u hh)) (fun hh => hw (L.middle.data.reg_mem .s hh))
  constructor
  · apply Triple.conseq (fun _ h => h) (step 1 q)
    intro st h
    apply (compactReady_iff L K R cs st).mpr
    simpa only [Nat.xor_self] using h
  · apply Triple.conseq (fun st h => (compactReady_iff L K R cs st).mp h) (step 0 0)
    intro st h; simpa only [Nat.zero_xor] using h

end ECDSAAdd.Arithmetic
