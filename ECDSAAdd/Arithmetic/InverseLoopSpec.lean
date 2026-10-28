import ECDSAAdd.Arithmetic.InverseLoopProof
import ECDSAAdd.Math.KaliskiInverse

namespace ECDSAAdd.Arithmetic

theorem LoopState.iff (L : KaliskiRoundLayout) (z : KState) (s : BasisState) :
    LoopState L z s ↔
      (((((((regValue L.u s=z.u ∧ regValue L.v s=z.v) ∧ regValue L.r s=z.r) ∧ regValue L.s s=z.s) ∧
        regValue L.k s=z.k) ∧ regValue L.kNext s=0) ∧ s L.done=decide (z.v=0)) ∧ regValue L.scratch s=0) := by
  constructor
  · intro h
    have hr : RoundState L z z.k 0 false (decide (z.v=0)) (s L.swap) (s L.subtract) s :=
      ⟨h.data,h.k,h.next,h.y,h.carry,h.active,h.done,rfl,rfl,h.odd,h.both,h.cin⟩
    have hh := (roundState_iff L z z.k 0 _ _ _ s).mp hr
    exact ⟨hh.1.1.1,hh.2⟩
  · rintro ⟨h,hw⟩
    have hr := (roundState_iff L z z.k 0 _ (s L.swap) (s L.subtract) s).mpr ⟨⟨⟨h,rfl⟩,rfl⟩,hw⟩
    exact ⟨hr.1,hr.2.k,hr.2.next,hr.2.y,hr.2.carry,hr.2.active,hr.2.done,hr.2.odd,hr.2.both,hr.2.cin⟩

theorem TapeValues.zero_iff (rs : List RoundRecord) (s : BasisState) :
    TapeValues rs (List.replicate rs.length (false,false)) s ↔ regValue (rs.flatMap RoundRecord.wires) s=0 := by
  induction rs with
  | nil => simp [TapeValues,regValue]
  | cons r rs ih =>
    simp only [List.length_cons,List.replicate_succ,TapeValues,List.flatMap_cons,RoundRecord.wires]
    rw [ih]
    simp [regValue_zero,or_imp,forall_and]

def InverseLoopLayout.work (L : InverseLoopLayout) : List Wire :=
  L.first.kNext++L.first.scratch++L.records.flatMap RoundRecord.wires++L.extra

theorem InverseExtra.zero_iff (L : InverseLoopLayout) (s : BasisState) :
    InverseExtra L 0 s ↔ regValue L.extra s=0 := by
  simp [InverseExtra,InverseLoopLayout.extra,regValue_zero,or_imp,forall_and]

theorem InverseInitial.iff (L : InverseLoopLayout) (q a : Nat) (ha : 0<a) (s : BasisState) :
    InverseInitial L q a s ↔
      ((((((regValue L.first.u s=q ∧ regValue L.first.v s=a) ∧ regValue L.first.r s=0) ∧
        regValue L.first.s s=1) ∧ regValue L.first.k s=0) ∧ s L.first.done=false) ∧ regValue L.work s=0) := by
  simp only [InverseInitial,LoopState.iff,OneBitRecordsValues.zero_iff,InverseExtra.zero_iff,kaliskiInit,
    show decide (a=0)=false by simp [Nat.ne_of_gt ha]]
  simp only [InverseLoopLayout.work,regValue_zero,List.mem_append,or_imp,forall_and]
  tauto

/-- 显式保留缩放历史与第一阶段控制/记录；中段不得修改这些值。 -/
def InverseHistory (L : InverseLoopLayout) (q X : Nat) (s : BasisState) : Prop :=
  let z := kaliskiStep^[512] (kaliskiInit q X)
  let N := (-(z.r : ZMod q)).val
  regValue L.compactScaling.k s=z.k ∧ regValue L.compactScaling.stage.acc s=N ∧
    regValue L.compactScaling.stage.history s=montgomeryQuotient q (inverseScaleFactor q z.k) N 64 ∧
    s L.compactScaling.stage.flag=decide (montgomeryValue q (inverseScaleFactor q z.k) N 64<q) ∧
    CompactFrozen L z.k (kaliskiCodes 512 (kaliskiInit q X)) s

private theorem inverseScaled_history_iff (L : InverseLoopLayout) (q X : Nat)
    (hm : L.arithmetic.width=256) (hl : L.first.low.length=256) (s : BasisState) :
    let z := kaliskiStep^[512] (kaliskiInit q X)
    let N := (-(z.r : ZMod q)).val
    InverseScaledMiddle L q z (kaliskiCodes 512 (kaliskiInit q X)) N s ↔
      ((regValue L.middle.r s=montgomeryValue q (inverseScaleFactor q z.k) N 64%q ∧
        regValue L.compactBorrow s=0) ∧ InverseHistory L q X s) := by
  dsimp only
  have hb (hz : regValue L.compactBorrow s=0) : regValue L.compactScaling.work s=0 := by
    rw [L.compactScaling_work hm hl]
    exact (regValue_zero _ _).mpr (fun w hw => (regValue_zero _ _).mp hz w (List.mem_of_mem_take hw))
  constructor
  · rintro ⟨⟨hk,hr,ha,hh,hf,_⟩,hB,hF⟩
    exact ⟨⟨hr,hB⟩,hk,ha,hh,hf,hF⟩
  · rintro ⟨⟨hr,hB⟩,hk,ha,hh,hf,hF⟩
    exact ⟨⟨hk,hr,ha,hh,hf,hb hB⟩,hB,hF⟩

/-- 准备逆元，同时保留第一阶段和缩放历史，借用区为空。 -/
theorem inversePrepare_spec (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (hn : L.records.length=512) (hw : L.first.counter.width=10)
    (hlow : L.first.low.length=256) (harith : L.arithmetic.width=256)
    (ha : L.a.length=257) (ht : L.temp.length=257)
    (q X : Nat) (hq : q<2^256) (ho : q%16=15) (hX0 : 0<X) (hX : X<q) (hcop : q.Coprime X) :
    {{ L.first.u=q, L.first.v=X, L.first.r=0, L.first.s=1,
       L.first.k=0, L.first.done=false, L.work=0 }} inverseCompute L q
    {{ L.middle.r=((X : ZMod q)⁻¹).val, L.compactBorrow=0, InverseHistory L q X st }} := by
  have hc := (inverseCompute_values L hnd hn hw hlow harith ha ht q X hq ho hX hcop).1
  have hh (s : BasisState) := inverseScaled_history_iff L q X harith hlow s
  simp only [kaliski_montgomery_scale q X ho hq hX0 hX hcop] at hh
  exact Triple.conseq (fun s h => (InverseInitial.iff L q X hX0 s).mpr h) hc
    (fun s h => (hh s).mp h)

/-- 使用段保持完整历史后，恢复所有第一阶段初值并清空缩放历史。 -/
theorem inverseRestore_spec (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (hn : L.records.length=512) (hw : L.first.counter.width=10)
    (hlow : L.first.low.length=256) (harith : L.arithmetic.width=256)
    (ha : L.a.length=257) (ht : L.temp.length=257)
    (q X : Nat) (hq : q<2^256) (ho : q%16=15) (hX0 : 0<X) (hX : X<q) (hcop : q.Coprime X) :
    {{ L.middle.r=((X : ZMod q)⁻¹).val, L.compactBorrow=0, InverseHistory L q X st }}
      inverseUncompute L q
    {{ L.first.u=q, L.first.v=X, L.first.r=0, L.first.s=1,
       L.first.k=0, L.first.done=false, L.work=0 }} := by
  have hc := (inverseCompute_values L hnd hn hw hlow harith ha ht q X hq ho hX hcop).2
  have hh (s : BasisState) := inverseScaled_history_iff L q X harith hlow s
  simp only [kaliski_montgomery_scale q X ho hq hX0 hX hcop] at hh
  exact Triple.conseq (fun s h => (hh s).mpr h) hc
    (fun s h => (InverseInitial.iff L q X hX0 s).mp h)

/-- 任意输出的 XOR 形式；第一阶段已经载入 q、a、0、1，完整工作区初末均为零。 -/
theorem inverseLoop_xor_spec (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (hn : L.records.length=512) (hw : L.first.counter.width=10)
    (hlow : L.first.low.length=256) (harith : L.arithmetic.width=256)
    (ha : L.a.length=257) (ht : L.temp.length=257) (hout : L.out.length=257)
    (q a O : Nat) (hq : q<2^256) (ho : q%16=15) (hx0 : 0<a) (hx : a<q) (hcop : q.Coprime a) :
    {{ L.first.u=q, L.first.v=a, L.first.r=0, L.first.s=1, L.first.k=0, L.first.done=false, L.work=0, L.out=O }}
      inverseLoop L q
    {{ L.first.u=q, L.first.v=a, L.first.r=0, L.first.s=1, L.first.k=0, L.first.done=false, L.work=0,
      L.out=(O ^^^ kaliskiInverse q a 256) }} := by
  have h := inverseLoop_values L hnd hn hw hlow harith ha ht hout q a O hq ho hx0 hx hcop
  apply Triple.conseq ?_ h ?_
  · intro s h; exact ⟨(InverseInitial.iff L q a hx0 s).mpr h.1,h.2⟩
  · intro s h
    exact ⟨(InverseInitial.iff L q a hx0 s).mp h.1,by simpa only [kaliskiInverse] using h.2⟩

/-- 常用零输出形式。fieldInverse 负责把外部输入装入这里要求的已初始化寄存器。 -/
theorem inverseLoop_spec (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (hn : L.records.length=512) (hw : L.first.counter.width=10)
    (hlow : L.first.low.length=256) (harith : L.arithmetic.width=256)
    (ha : L.a.length=257) (ht : L.temp.length=257) (hout : L.out.length=257)
    (q a : Nat) (hq : q<2^256) (ho : q%16=15) (hx0 : 0<a) (hx : a<q) (hcop : q.Coprime a) :
    {{ L.first.u=q, L.first.v=a, L.first.r=0, L.first.s=1, L.first.k=0, L.first.done=false, L.work=0, L.out=0 }}
      inverseLoop L q
    {{ L.first.u=q, L.first.v=a, L.first.r=0, L.first.s=1, L.first.k=0, L.first.done=false, L.work=0,
      L.out=kaliskiInverse q a 256 }} := by
  simpa only [Nat.zero_xor] using inverseLoop_xor_spec L hnd hn hw hlow harith ha ht hout q a 0 hq ho hx0 hx hcop

end ECDSAAdd.Arithmetic
