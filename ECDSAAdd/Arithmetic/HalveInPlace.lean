import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.Shift
import ECDSAAdd.Arithmetic.BorrowFrame
import ECDSAAdd.Arithmetic.KaliskiRound
import ECDSAAdd.Math.HalvingBijection

namespace ECDSAAdd.Arithmetic

/-- 求逆第二阶段的原地减半/加倍布局：data 上原地操作；常数字、进位链（chain 给加法器，
chain ++ [top] 给比较器）、cin 与标志借自模算术工作区；active 与计数银行沿用第一阶段。 -/
structure HalvingLayout where
  data : List Wire
  constant : List Wire
  chain : List Wire
  top : Wire
  cin : Wire
  flag : Wire
  active : Wire
  counterLow : List AddBit
  counterHigh : AddBit
  compareCin : Wire

namespace HalvingLayout

def counter (L : HalvingLayout) : AdderLayout := ⟨L.counterLow ++ [L.counterHigh], L.compareCin⟩
def carry (L : HalvingLayout) : List Wire := L.chain ++ [L.top]
def wires (L : HalvingLayout) : List Wire :=
  L.active :: L.flag :: L.cin :: (L.data ++ L.constant ++ L.carry ++ L.counter.wires)
/-- 轮与轮之间为零的全部工作线。 -/
def work (L : HalvingLayout) : List Wire :=
  L.active :: L.flag :: L.cin :: (L.constant ++ L.carry ++ L.counter.y ++ L.counter.out ++
    L.counter.carry ++ [L.compareCin])

theorem carry_length (L : HalvingLayout) : L.carry.length = L.chain.length + 1 := by
  simp [carry]

end HalvingLayout

/-- 计数输入和值域不变；比较工作区为空。 -/
def HalvingCounter (L : AdderLayout) (K : Nat) (s : BasisState) : Prop :=
  regValue L.x s = K ∧ regValue L.y s = 0 ∧ s L.cin = false ∧
    regValue L.out s = 0 ∧ regValue L.carry s = 0

theorem HalvingCounter.congr (L : AdderLayout) (K : Nat) (s t : BasisState)
    (h : HalvingCounter L K s) (he : ∀ w ∈ L.wires, t w = s w) : HalvingCounter L K t := by
  have keep (r : List Wire) (hr : r ⊆ L.wires) : regValue r t = regValue r s :=
    regValue_congr _ _ _ (fun w hw => he w (hr hw))
  exact ⟨(keep L.x L.reg_subset.1).trans h.1,
    (keep L.y L.reg_subset.2.1).trans h.2.1,
    (he L.cin (by simp [AdderLayout.wires])).trans h.2.2.1,
    (keep L.out L.reg_subset.2.2.1).trans h.2.2.2.1,
    (keep L.carry L.reg_subset.2.2.2).trans h.2.2.2.2⟩

/-- 一轮受控原地模减半：active ^= [i<k]；flag ← active ∧ data₀；data += flag·q；
受控右移；flag ^= active；flag ^= active ∧ [data < (q+1)/2]；active ^= [i<k]。 -/
def halveStep (L : HalvingLayout) (q i : Nat) : Program :=
  -- 装入本轮使能 active = [i<k]，计数输入 k 保持。
  counterActiveXor L.counter L.active i ++
  -- 记录输入奇偶；奇数先加 q，使待右移的数为偶数。
  [.CCX L.active L.data.head! L.flag] ++
  maskedAddConst L.flag L.constant L.data L.chain L.cin q ++
  shiftRight L.active L.data ++
  -- 减半结果 ≥ (q+1)/2 当且仅当输入为奇数；CX 加“小于”比较清 flag。
  [.CX L.active L.flag] ++
  compareLtConst (some L.active) L.data L.constant L.carry L.cin L.flag ((q+1)/2) ++
  -- k 未变，再算同一个 [i<k]，将 active 清零。
  counterActiveXor L.counter L.active i

/-- 一轮受控原地模加倍，以独立前向门列恢复减半前的数据。 -/
def doubleStep (L : HalvingLayout) (q i : Nat) : Program :=
  -- 装入本轮使能；比较加 CX 得到 flag = active ∧ [data ≥ (q+1)/2]。
  counterActiveXor L.counter L.active i ++
  compareLtConst (some L.active) L.data L.constant L.carry L.cin L.flag ((q+1)/2) ++
  [.CX L.active L.flag] ++
  -- 左移加倍；flag 记录是否需要减 q，使结果回到 [0,q)。
  shiftLeft L.active L.data ++
  maskedSubConst L.flag L.constant L.data L.chain L.cin q ++
  -- q 为奇数，约减后结果的奇偶恰好等于约减标志，故可清 flag。
  [.CCX L.active L.data.head! L.flag] ++
  -- 同一计数比较清 active；本轮借用工作线全部恢复为零。
  counterActiveXor L.counter L.active i

/-- 轮内各步之间的状态：data 值、flag、active、计数输入 k；其余工作线为零。 -/
structure HalvingValues (L : HalvingLayout) (K X : Nat) (F A : Bool) (st : BasisState) : Prop where
  data : regValue L.data st = X
  flag : st L.flag = F
  active : st L.active = A
  cin : st L.cin = false
  constant : regValue L.constant st = 0
  chain : regValue L.chain st = 0
  top : st L.top = false
  counter : HalvingCounter L.counter K st

namespace HalvingLayout

/-- 位宽条件：常数字与 data 同宽，加法进位链少一位，计数器十位。 -/
structure Widths (L : HalvingLayout) : Prop where
  constant : L.constant.length = L.data.length
  chain : L.chain.length + 1 = L.data.length
  counter : L.counter.width = 10

theorem data_ne_nil (L : HalvingLayout) (hw : L.Widths) : L.data ≠ [] := by
  intro h; have := hw.chain; rw [h] at this; simp at this

/-- 由全局互异条件推出各子程序需要的互异条件与不重叠事实。 -/
theorem counter_nodup (L : HalvingLayout) (hnd : L.wires.Nodup) : (L.active :: L.counter.wires).Nodup := by
  have hcnt := List.nodup_iff_count.mp hnd
  apply List.nodup_iff_count.mpr; intro w; have := hcnt w
  simp only [wires, carry, List.count_cons, List.count_append] at this ⊢; omega

theorem addConst_nodup (L : HalvingLayout) (hnd : L.wires.Nodup) :
    (L.flag :: L.cin :: (L.constant ++ L.data ++ L.chain)).Nodup := by
  have hcnt := List.nodup_iff_count.mp hnd
  apply List.nodup_iff_count.mpr; intro w; have := hcnt w
  simp only [wires, carry, List.count_cons, List.count_append] at this ⊢; omega

theorem compare_nodup (L : HalvingLayout) (hnd : L.wires.Nodup) :
    (L.active :: L.flag :: L.cin :: (L.data ++ L.constant ++ L.carry)).Nodup := by
  have hcnt := List.nodup_iff_count.mp hnd
  apply List.nodup_iff_count.mpr; intro w; have := hcnt w
  simp only [wires, carry, List.count_cons, List.count_append] at this ⊢; omega

theorem shift_nodup (L : HalvingLayout) (hnd : L.wires.Nodup) : (L.active :: L.data).Nodup := by
  have hcnt := List.nodup_iff_count.mp hnd
  apply List.nodup_iff_count.mpr; intro w; have := hcnt w
  simp only [wires, carry, List.count_cons, List.count_append] at this ⊢; omega

end HalvingLayout


namespace HalvingLayout

/-- 不在某些寄存器里：把两处出现变成计数 ≥ 2 的矛盾。 -/
theorem not_active (L : HalvingLayout) (hnd : L.wires.Nodup) (w : Wire)
    (hw : w ∈ L.flag :: L.cin :: (L.data ++ L.constant ++ L.carry ++ L.counter.wires)) : w ≠ L.active := by
  intro heq
  have h1 := List.nodup_iff_count.mp hnd L.active
  have h2 := List.count_pos_iff.mpr (heq ▸ hw)
  simp only [wires, List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega

theorem not_flag (L : HalvingLayout) (hnd : L.wires.Nodup) (w : Wire)
    (hw : w ∈ L.active :: L.cin :: (L.data ++ L.constant ++ L.carry ++ L.counter.wires)) : w ≠ L.flag := by
  intro heq
  have h1 := List.nodup_iff_count.mp hnd L.flag
  have h2 := List.count_pos_iff.mpr (heq ▸ hw)
  simp only [wires, List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega

theorem not_data (L : HalvingLayout) (hnd : L.wires.Nodup) (w : Wire)
    (hw : w ∈ L.active :: L.flag :: L.cin :: (L.constant ++ L.carry ++ L.counter.wires)) : w ∉ L.data := by
  intro hd
  have h1 := List.nodup_iff_count.mp hnd w
  have h2 := List.count_pos_iff.mpr hw
  have h3 := List.count_pos_iff.mpr hd
  simp only [wires, List.count_cons, List.count_append] at h1 h2; omega

/-- 计数器线路与轮内其他线路不重叠。 -/
theorem counter_outside (L : HalvingLayout) (hnd : L.wires.Nodup) (w : Wire) (hw : w ∈ L.counter.wires) :
    w ∉ (L.active :: L.flag :: L.cin :: (L.data ++ L.constant ++ L.carry)).toFinset := by
  intro hm
  have h1 := List.nodup_iff_count.mp hnd w
  have h2 := List.count_pos_iff.mpr hw
  have h3 := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
  simp only [wires, List.count_cons, List.count_append] at h1 h3; omega

theorem carry_zero (L : HalvingLayout) (st : BasisState) :
    regValue L.carry st = 0 ↔ regValue L.chain st = 0 ∧ st L.top = false := by
  rw [carry, regValue_append]
  simp only [regValue, List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
  have hp := Nat.two_pow_pos L.chain.length
  constructor
  · intro h
    cases hb : st L.top
    · simpa [hb] using h
    · simp [hb] at h
  · rintro ⟨h1, h2⟩; simp [h1, h2]

end HalvingLayout

/-- 第 1、7 步：比较 i<k，翻转 active；计数与比较工作区逐线恢复。 -/
theorem step_active (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (i K X : Nat) (F A : Bool) (hi : i < 512) :
    Triple (HalvingValues L K X F A) (counterActiveXor L.counter L.active i)
      (HalvingValues L K X F (A ^^ decide (i < K))) := by
  intro s m h
  have hn := L.counter_nodup hnd
  obtain ⟨hp, hv⟩ := counterActiveXor_spec L.counter L.active hn hw.counter K i A hi s m
    ⟨⟨⟨⟨h.active, h.counter.1⟩, h.counter.2.1⟩, h.counter.2.2.1⟩, h.counter.2.2.2.2⟩
  have he := counterActiveXor_frame L.counter L.active
    hn hw.counter i K hi A s m h.active h.counter.1 h.counter.2.1 h.counter.2.2.1
    h.counter.2.2.2.2
  have hout : regValue L.counter.out (run (counterActiveXor L.counter L.active i) m s).basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ (fun w hw' => he w ?_)) h.counter.2.2.2.1
    exact fun e => (List.nodup_cons.mp hn).1 (e ▸ L.counter.reg_subset.2.2.1 hw')
  refine ⟨hp, ⟨?_, ?_, hv.1.1.1.1, ?_, ?_, ?_, ?_, ⟨hv.1.1.1.2, hv.1.1.2, hv.1.2, hout, hv.2⟩⟩⟩
  · exact (regValue_congr _ _ _ (fun w hw' => he w (L.not_active hnd w (by simp [hw'])))).trans h.data
  · exact (he _ (L.not_active hnd _ (by simp))).trans h.flag
  · exact (he _ (L.not_active hnd _ (by simp))).trans h.cin
  · exact (regValue_congr _ _ _ (fun w hw' => he w (L.not_active hnd w (by simp [hw'])))).trans h.constant
  · exact (regValue_congr _ _ _ (fun w hw' => he w (L.not_active hnd w
      (by simp [HalvingLayout.carry, hw'])))).trans h.chain
  · exact (he _ (L.not_active hnd _ (by simp [HalvingLayout.carry]))).trans h.top

/-- 第 2 步（减半）/ 第 6 步（加倍）：flag ^= active ∧ data 最低位。 -/
theorem step_parity (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (K X : Nat) (F A : Bool) :
    Triple (HalvingValues L K X F A) [.CCX L.active L.data.head! L.flag]
      (HalvingValues L K X (F ^^ (A && decide (X % 2 ≠ 0))) A) := by
  intro s m h
  have hne : L.data ≠ [] := L.data_ne_nil hw
  have hhead : s.basis L.data.head! = decide (X % 2 ≠ 0) := by rw [regValue_headBit _ hne s.basis, h.data]
  have hf (w : Wire) (hw' : w ∈ L.active :: L.cin :: (L.data ++ L.constant ++ L.carry ++ L.counter.wires)) :
      w ≠ L.flag := L.not_flag hnd w hw'
  simp only [run]
  refine ⟨trivial, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (regValue_congr _ _ _ (fun w hw' => by simp [writeBit, hf w (by simp [hw'])])).trans h.data
  · simp [writeBit, h.flag, h.active, hhead]
  · simpa [writeBit, hf L.active (by simp)] using h.active
  · simpa [writeBit, hf L.cin (by simp)] using h.cin
  · exact (regValue_congr _ _ _ (fun w hw' => by simp [writeBit, hf w (by simp [hw'])])).trans h.constant
  · exact (regValue_congr _ _ _ (fun w hw' => by
      simp [writeBit, hf w (by simp [HalvingLayout.carry, hw'])])).trans h.chain
  · simpa [writeBit, hf L.top (by simp [HalvingLayout.carry])] using h.top
  · exact HalvingCounter.congr _ _ _ _ h.counter (fun w hw' => by simp [writeBit, hf w (by simp [hw'])])

/-- 第 5 步（减半）/ 第 3 步（加倍）：flag ^= active。 -/
theorem step_flip (L : HalvingLayout) (hnd : L.wires.Nodup) (K X : Nat) (F A : Bool) :
    Triple (HalvingValues L K X F A) [.CX L.active L.flag] (HalvingValues L K X (F ^^ A) A) := by
  intro s m h
  have hf (w : Wire) (hw' : w ∈ L.active :: L.cin :: (L.data ++ L.constant ++ L.carry ++ L.counter.wires)) :
      w ≠ L.flag := L.not_flag hnd w hw'
  simp only [run]
  refine ⟨trivial, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (regValue_congr _ _ _ (fun w hw' => by simp [writeBit, hf w (by simp [hw'])])).trans h.data
  · simp [writeBit, h.flag, h.active]
  · simpa [writeBit, hf L.active (by simp)] using h.active
  · simpa [writeBit, hf L.cin (by simp)] using h.cin
  · exact (regValue_congr _ _ _ (fun w hw' => by simp [writeBit, hf w (by simp [hw'])])).trans h.constant
  · exact (regValue_congr _ _ _ (fun w hw' => by
      simp [writeBit, hf w (by simp [HalvingLayout.carry, hw'])])).trans h.chain
  · simpa [writeBit, hf L.top (by simp [HalvingLayout.carry])] using h.top
  · exact HalvingCounter.congr _ _ _ _ h.counter (fun w hw' => by simp [writeBit, hf w (by simp [hw'])])

/-- 受控右移：active 为真且 data 为偶数时精确减半。 -/
theorem step_shiftRight (L : HalvingLayout) (hnd : L.wires.Nodup) (K X : Nat) (F A : Bool)
    (heven : A = true → X % 2 = 0) :
    Triple (HalvingValues L K X F A) (shiftRight L.active L.data)
      (HalvingValues L K (if A then X / 2 else X) F A) := by
  intro s m h
  obtain ⟨hp, hv⟩ := shiftRight_spec L.active L.data (L.shift_nodup hnd) A X heven s m ⟨h.active, h.data⟩
  simp only [Holds.holds] at hv
  have he := (shift_frame L.active L.data s m).2.1
  have hd (w : Wire) (hw' : w ∈ L.active :: L.flag :: L.cin :: (L.constant ++ L.carry ++ L.counter.wires)) :
      w ∉ L.data := L.not_data hnd w hw'
  refine ⟨hp, ⟨hv.2, (he _ (hd _ (by simp))).trans h.flag, hv.1, (he _ (hd _ (by simp))).trans h.cin,
    (regValue_congr _ _ _ (fun w hw' => he w (hd w (by simp [hw'])))).trans h.constant,
    (regValue_congr _ _ _ (fun w hw' => he w (hd w (by simp [HalvingLayout.carry, hw'])))).trans h.chain,
    (he _ (hd _ (by simp [HalvingLayout.carry]))).trans h.top,
    HalvingCounter.congr _ _ _ _ h.counter (fun w hw' => he w (hd w (by simp [hw'])))⟩⟩

/-- 受控左移：active 为真且两倍仍装得下时精确加倍。 -/
theorem step_shiftLeft (L : HalvingLayout) (hnd : L.wires.Nodup) (K X : Nat) (F A : Bool)
    (hfit : A = true → 2 * X < 2^L.data.length) :
    Triple (HalvingValues L K X F A) (shiftLeft L.active L.data)
      (HalvingValues L K (if A then 2 * X else X) F A) := by
  intro s m h
  obtain ⟨hp, hv⟩ := shiftLeft_spec L.active L.data (L.shift_nodup hnd) A X hfit s m ⟨h.active, h.data⟩
  simp only [Holds.holds] at hv
  have he := (shift_frame L.active L.data s m).2.2.2
  have hd (w : Wire) (hw' : w ∈ L.active :: L.flag :: L.cin :: (L.constant ++ L.carry ++ L.counter.wires)) :
      w ∉ L.data := L.not_data hnd w hw'
  refine ⟨hp, ⟨hv.2, (he _ (hd _ (by simp))).trans h.flag, hv.1, (he _ (hd _ (by simp))).trans h.cin,
    (regValue_congr _ _ _ (fun w hw' => he w (hd w (by simp [hw'])))).trans h.constant,
    (regValue_congr _ _ _ (fun w hw' => he w (hd w (by simp [HalvingLayout.carry, hw'])))).trans h.chain,
    (he _ (hd _ (by simp [HalvingLayout.carry]))).trans h.top,
    HalvingCounter.congr _ _ _ _ h.counter (fun w hw' => he w (hd w (by simp [hw'])))⟩⟩

/-- 第 3 步（减半）：data += flag·q，常数字与进位链回零。 -/
theorem step_addConst (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (q K X : Nat) (F A : Bool) (hq : q < 2^L.constant.length) :
    Triple (HalvingValues L K X F A) (maskedAddConst L.flag L.constant L.data L.chain L.cin q)
      (HalvingValues L K ((X + (if F then q else 0)) % 2^L.data.length) F A) := by
  intro s m h
  obtain ⟨hp, hv⟩ := maskedAddConst_spec L.flag L.cin L.constant L.data L.chain (L.addConst_nodup hnd)
    hw.constant hw.chain q hq F X s m ⟨⟨⟨⟨h.flag, h.constant⟩, h.data⟩, h.cin⟩, h.chain⟩
  simp only [Holds.holds] at hv
  have hout (w : Wire) (hm : w ∉ (L.flag :: L.cin :: (L.constant ++ L.data ++ L.chain)).toFinset) :
      (run (maskedAddConst L.flag L.constant L.data L.chain L.cin q) m s).basis w = s.basis w :=
    run_preserves_outside _ m s w (fun hh =>
      hm ((maskedConst_wires_subset L.flag L.constant L.data L.chain L.cin q hw.constant hw.chain).1 hh))
  have hcnt := List.nodup_iff_count.mp hnd
  have hact : L.active ∉ (L.flag :: L.cin :: (L.constant ++ L.data ++ L.chain)).toFinset := by
    intro hm
    have h1 := hcnt L.active
    have h2 := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    simp only [HalvingLayout.wires, HalvingLayout.carry, List.count_cons, List.count_append,
      beq_self_eq_true, if_true] at h1 h2; omega
  have htop : L.top ∉ (L.flag :: L.cin :: (L.constant ++ L.data ++ L.chain)).toFinset := by
    intro hm
    have h1 := hcnt L.top
    have h2 := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    simp only [HalvingLayout.wires, HalvingLayout.carry, List.count_cons, List.count_append,
      beq_self_eq_true, if_true] at h1 h2; omega
  have hctr (w : Wire) (hw' : w ∈ L.counter.wires) :
      w ∉ (L.flag :: L.cin :: (L.constant ++ L.data ++ L.chain)).toFinset := by
    intro hm
    have := L.counter_outside hnd w hw'
    apply this
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, HalvingLayout.carry] at hm ⊢
    tauto
  refine ⟨hp, ⟨hv.1.1.2, hv.1.1.1.1, (hout _ hact).trans h.active, hv.1.2, hv.1.1.1.2, hv.2,
    (hout _ htop).trans h.top, HalvingCounter.congr _ _ _ _ h.counter (fun w hw' => hout w (hctr w hw'))⟩⟩

/-- 第 4 步（加倍）：data −= flag·q。 -/
theorem step_subConst (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (q K X : Nat) (F A : Bool) (hq : q < 2^L.constant.length) :
    Triple (HalvingValues L K X F A) (maskedSubConst L.flag L.constant L.data L.chain L.cin q)
      (HalvingValues L K ((X + 2^L.data.length - (if F then q else 0)) % 2^L.data.length) F A) := by
  intro s m h
  obtain ⟨hp, hv⟩ := maskedSubConst_spec L.flag L.cin L.constant L.data L.chain (L.addConst_nodup hnd)
    hw.constant hw.chain q hq F X s m ⟨⟨⟨⟨h.flag, h.constant⟩, h.data⟩, h.cin⟩, h.chain⟩
  simp only [Holds.holds] at hv
  have hout (w : Wire) (hm : w ∉ (L.flag :: L.cin :: (L.constant ++ L.data ++ L.chain)).toFinset) :
      (run (maskedSubConst L.flag L.constant L.data L.chain L.cin q) m s).basis w = s.basis w :=
    run_preserves_outside _ m s w (fun hh =>
      hm ((maskedConst_wires_subset L.flag L.constant L.data L.chain L.cin q hw.constant hw.chain).2 hh))
  have hcnt := List.nodup_iff_count.mp hnd
  have hact : L.active ∉ (L.flag :: L.cin :: (L.constant ++ L.data ++ L.chain)).toFinset := by
    intro hm
    have h1 := hcnt L.active
    have h2 := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    simp only [HalvingLayout.wires, HalvingLayout.carry, List.count_cons, List.count_append,
      beq_self_eq_true, if_true] at h1 h2; omega
  have htop : L.top ∉ (L.flag :: L.cin :: (L.constant ++ L.data ++ L.chain)).toFinset := by
    intro hm
    have h1 := hcnt L.top
    have h2 := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    simp only [HalvingLayout.wires, HalvingLayout.carry, List.count_cons, List.count_append,
      beq_self_eq_true, if_true] at h1 h2; omega
  have hctr (w : Wire) (hw' : w ∈ L.counter.wires) :
      w ∉ (L.flag :: L.cin :: (L.constant ++ L.data ++ L.chain)).toFinset := by
    intro hm
    have := L.counter_outside hnd w hw'
    apply this
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, HalvingLayout.carry] at hm ⊢
    tauto
  refine ⟨hp, ⟨hv.1.1.2, hv.1.1.1.1, (hout _ hact).trans h.active, hv.1.2, hv.1.1.1.2, hv.2,
    (hout _ htop).trans h.top, HalvingCounter.congr _ _ _ _ h.counter (fun w hw' => hout w (hctr w hw'))⟩⟩

/-- 第 6 步（减半）/ 第 2 步（加倍）：flag ^= active ∧ [data < Kc]，比较器工作区回零。 -/
theorem step_compare (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (Kc K X : Nat) (F A : Bool) (hKc : Kc < 2^L.constant.length) :
    Triple (HalvingValues L K X F A)
      (compareLtConst (some L.active) L.data L.constant L.carry L.cin L.flag Kc)
      (HalvingValues L K X (F ^^ (A && decide (X < Kc))) A) := by
  intro s m h
  have hcl : L.carry.length = L.constant.length := by
    rw [L.carry_length, hw.chain, hw.constant]
  have hcarry : regValue L.carry s.basis = 0 := (L.carry_zero s.basis).mpr ⟨h.chain, h.top⟩
  obtain ⟨hp, hv⟩ := maskedCompareLtConst_spec L.active L.data L.constant L.carry L.cin L.flag
    (L.compare_nodup hnd) hw.constant.symm hcl Kc hKc A X F s m
    ⟨⟨⟨⟨⟨h.active, h.data⟩, h.constant⟩, hcarry⟩, h.cin⟩, h.flag⟩
  simp only [Holds.holds] at hv
  have hout (w : Wire) (hm : w ∉ (L.active :: L.flag :: L.cin :: (L.data ++ L.constant ++ L.carry)).toFinset) :
      (run (compareLtConst (some L.active) L.data L.constant L.carry L.cin L.flag Kc) m s).basis w =
        s.basis w := by
    apply run_preserves_outside
    rw [(compareLt_wires (some L.active) L.data L.constant L.carry L.cin L.flag hw.constant.symm hcl).2 Kc]
    simpa only [Option.toList_some, List.singleton_append] using hm
  obtain ⟨hchain, htop⟩ := (L.carry_zero _).mp hv.1.1.2
  refine ⟨hp, ⟨hv.1.1.1.1.2, hv.2, hv.1.1.1.1.1, hv.1.2, hv.1.1.1.2, hchain, htop,
    HalvingCounter.congr _ _ _ _ h.counter (fun w hw' => hout w (L.counter_outside hnd w hw'))⟩⟩

/-- 完整减半轮：只改写 data，全部借用工作线清零，计数 K 保持。 -/
theorem halveStep_values (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (q i K X : Nat) (hq : q % 2 = 1) (hX : X < q)
    (hfit : 2*q ≤ 2^L.data.length) (hi : i < 512) :
    Triple (HalvingValues L K X false false) (halveStep L q i)
      (HalvingValues L K (if i < K then halveMod q X else X) false false) := by
  have hqfit : q < 2^L.constant.length := by rw [hw.constant]; omega
  have hcfit : (q+1)/2 < 2^L.constant.length := by omega
  let A := decide (i < K)
  let F := A && decide (X % 2 ≠ 0)
  let Y := X + (if F then q else 0)
  have hyfit : Y < 2^L.data.length := by dsimp [Y]; split_ifs <;> omega
  have heven : A = true → Y % 2 = 0 := by
    intro ha; simp only [Y, F, ha, Bool.true_and]; split_ifs <;> simp_all; omega
  have h1 := step_active L hnd hw i K X false false hi
  simp only [Bool.false_xor] at h1
  have h2 := step_parity L hnd hw K X false A
  simp only [Bool.false_xor] at h2
  have h3 := step_addConst L hnd hw q K X F A hqfit
  change Triple _ _ (HalvingValues L K (Y % 2^L.data.length) F A) at h3
  rw [Nat.mod_eq_of_lt hyfit] at h3
  have h4 := step_shiftRight L hnd K Y F A heven
  let Z := if A then Y/2 else Y
  have h5 := step_flip L hnd K Z F A
  have h6 := step_compare L hnd hw ((q+1)/2) K Z (F ^^ A) A hcfit
  have hflag : ((F ^^ A) ^^ (A && decide (Z < (q+1)/2))) = false := by
    by_cases ha : i < K
    · have hz : Z = halveMod q X := by
        simp only [Z, Y, F, A, ha, decide_true, Bool.true_and, if_true]
        unfold halveMod; split_ifs <;> simp_all
      have hp := halve_parity q X hq hX
      rw [hz]; dsimp [F, A]; simp only [ha, decide_true, Bool.true_and]
      by_cases hx : X % 2 ≠ 0 <;> by_cases hz : halveMod q X < (q+1)/2 <;> simp_all; omega
    · simp [F, A, ha]
  rw [hflag] at h6
  have h7 := step_active L hnd hw i K Z false A hi
  have haa : (A ^^ decide (i < K)) = false := by simp [A]
  rw [haa] at h7
  have hz : Z = if i < K then halveMod q X else X := by
    by_cases ha : i < K
    · simp only [Z, Y, F, A, ha, decide_true, Bool.true_and, if_true]
      unfold halveMod; split_ifs <;> simp_all
    · simp [Z, Y, F, A, ha]
  have hall := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7
  rw [hz] at hall
  exact hall

/-- 完整加倍轮：显式前向门列撤销减半，不倒放测量。 -/
theorem doubleStep_values (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (q i K X : Nat) (hq : q % 2 = 1) (hX : X < q)
    (hfit : 2*q ≤ 2^L.data.length) (hi : i < 512) :
    Triple (HalvingValues L K X false false) (doubleStep L q i)
      (HalvingValues L K (if i < K then (2*X)%q else X) false false) := by
  have hqfit : q < 2^L.constant.length := by rw [hw.constant]; omega
  have hcfit : (q+1)/2 < 2^L.constant.length := by omega
  let A := decide (i < K)
  let C := A && decide (X < (q+1)/2)
  let F := C ^^ A
  let Y := if A then 2*X else X
  let Z := (Y + 2^L.data.length - (if F then q else 0)) % 2^L.data.length
  have hd := double_flag q X hq hX
  have hz : Z = if i < K then (2*X)%q else X := by
    by_cases ha : i < K
    · by_cases hx : X < (q+1)/2
      · have hlt : 2*X < q := by omega
        simp [Z, Y, F, C, A, ha, hx, Nat.mod_eq_of_lt hlt,
          Nat.mod_eq_of_lt (show 2*X < 2^L.data.length by omega)]
      · have hle : q ≤ 2*X := by omega
        have he : 2*X + 2^L.data.length - q = (2*X-q) + 2^L.data.length := by omega
        simp [Z, Y, F, C, A, ha, hx, he, hd.2.1,
          show (q+1)/2 ≤ X by omega, Nat.mod_eq_of_lt (show 2*X-q < 2^L.data.length by omega)]
    · simp [Z, Y, F, C, A, ha, Nat.mod_eq_of_lt (show X < 2^L.data.length by omega)]
  have hflag : (F ^^ (A && decide (Z % 2 ≠ 0))) = false := by
    rw [hz]
    by_cases ha : i < K
    · by_cases hx : X < (q+1)/2
      · have he : ((2*X)%q)%2 = 0 := by omega
        simp [F, C, A, ha, hx, he]
      · have he : ((2*X)%q)%2 ≠ 0 := by omega
        simp [F, C, A, ha, hx, he]
    · simp [F, C, A, ha]
  have h1 := step_active L hnd hw i K X false false hi
  simp only [Bool.false_xor] at h1
  have h2 := step_compare L hnd hw ((q+1)/2) K X false A hcfit
  simp only [Bool.false_xor] at h2
  have h3 := step_flip L hnd K X C A
  have h4 := step_shiftLeft L hnd K X F A (by intro _; omega)
  have h5 := step_subConst L hnd hw q K Y F A hqfit
  have h6 := step_parity L hnd hw K Z F A
  rw [hflag] at h6
  have h7 := step_active L hnd hw i K Z false A hi
  have haa : (A ^^ decide (i < K)) = false := by simp [A]
  rw [haa] at h7
  have hall := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7
  rw [hz] at hall
  exact hall

/-- 轮边界的内部断言恰好是数据、计数寄存器的值及全部工作线清零。 -/
theorem HalvingValues.iff (L : HalvingLayout) (K X : Nat) (s : BasisState) :
    HalvingValues L K X false false s ↔
      ((regValue L.data s=X ∧ regValue L.counter.x s=K) ∧ regValue L.work s=0) := by
  have hw : regValue L.work s=0 ↔
      s L.active=false ∧ s L.flag=false ∧ s L.cin=false ∧
      regValue L.constant s=0 ∧ regValue L.chain s=0 ∧ s L.top=false ∧
      regValue L.counter.y s=0 ∧ regValue L.counter.out s=0 ∧
      regValue L.counter.carry s=0 ∧ s L.compareCin=false := by
    simp only [HalvingLayout.work,HalvingLayout.carry,regValue_zero,List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false,or_imp,forall_and,forall_eq]
    tauto
  rw [hw]
  constructor
  · intro h
    exact ⟨⟨h.data,h.counter.1⟩,h.active,h.flag,h.cin,h.constant,h.chain,h.top,
      h.counter.2.1,h.counter.2.2.2.1,h.counter.2.2.2.2,h.counter.2.2.1⟩
  · rintro ⟨⟨hd,hk⟩,ha,hf,hc,hconst,hchain,ht,hy,ho,hcarry,hcin⟩
    exact ⟨hd,hf,ha,hc,hconst,hchain,ht,⟨hk,hy,hcin,ho,hcarry⟩⟩

/-- 第 i 轮：i<k 时原地模减半，否则保持；k 不变且全部工作线清零。 -/
theorem halveStep_spec (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (q i K X : Nat) (hq : q % 2 = 1) (hX : X < q)
    (hfit : 2*q ≤ 2^L.data.length) (hi : i < 512) :
    {{ L.data=X, L.counter.x=K, L.work=0 }} halveStep L q i
    {{ L.data=(if i<K then halveMod q X else X), L.counter.x=K, L.work=0 }} :=
  Triple.conseq (fun s h => (HalvingValues.iff L K X s).mpr h)
    (halveStep_values L hnd hw q i K X hq hX hfit hi)
    (fun s h => (HalvingValues.iff L K _ s).mp h)

/-- 第 i 个恢复轮：i<k 时原地模加倍，否则保持；k 不变且全部工作线清零。 -/
theorem doubleStep_spec (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (q i K X : Nat) (hq : q % 2 = 1) (hX : X < q)
    (hfit : 2*q ≤ 2^L.data.length) (hi : i < 512) :
    {{ L.data=X, L.counter.x=K, L.work=0 }} doubleStep L q i
    {{ L.data=(if i<K then (2*X)%q else X), L.counter.x=K, L.work=0 }} :=
  Triple.conseq (fun s h => (HalvingValues.iff L K X s).mpr h)
    (doubleStep_values L hnd hw q i K X hq hX hfit hi)
    (fun s h => (HalvingValues.iff L K _ s).mp h)

end ECDSAAdd.Arithmetic
