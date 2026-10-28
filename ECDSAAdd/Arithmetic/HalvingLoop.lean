import ECDSAAdd.Arithmetic.HalveInPlace

namespace ECDSAAdd.Arithmetic

/-- 固定轮数前向减半，每轮仍执行同一字面门列。
从轮号 i 起执行 n 轮；先执行当前轮，再递增轮号。仅 i<k 的轮改变数据。 -/
def halveInPlace (L : HalvingLayout) (q i : Nat) : Nat → Program
  | 0 => []
  | n+1 => halveStep L q i ++ halveInPlace L q (i+1) n

/-- 恢复从 i 起的 n 轮：先恢复后续轮，再恢复当前轮，故轮号顺序与减半相反。 -/
def restoreInPlace (L : HalvingLayout) (q i : Nat) : Nat → Program
  | 0 => []
  | n+1 => restoreInPlace L q (i+1) n ++ doubleStep L q i

def halvingValue (q K i : Nat) : Nat → Nat → Nat
  | 0, X => X
  | n+1, X => halvingValue q K (i+1) n (if i<K then halveMod q X else X)

theorem halveInPlace_values (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (q K i n X : Nat) (hq : q % 2 = 1) (hX : X < q)
    (hfit : 2*q ≤ 2^L.data.length) (hn : i+n ≤ 512) :
    Triple (HalvingValues L K X false false) (halveInPlace L q i n)
      (HalvingValues L K (halvingValue q K i n X) false false) ∧
    Triple (HalvingValues L K (halvingValue q K i n X) false false) (restoreInPlace L q i n)
      (HalvingValues L K X false false) := by
  induction n generalizing i X with
  | zero => exact ⟨fun _ _ h => ⟨rfl,h⟩, fun _ _ h => ⟨rfl,h⟩⟩
  | succ n ih =>
    let Y := if i<K then halveMod q X else X
    have hy : Y < q := by dsimp [Y]; split_ifs; exact halve_mod_bound q X hq hX; exact hX
    obtain ⟨hf,hb⟩ := ih (i+1) Y hy (by omega)
    have hs := halveStep_values L hnd hw q i K X hq hX hfit (by omega)
    have hr := doubleStep_values L hnd hw q i K Y hq hy hfit (by omega)
    have hv : (if i<K then (2*Y)%q else Y) = X := by
      dsimp [Y]; split_ifs <;> simp_all [double_halve_mod q X hq hX]
    rw [hv] at hr
    exact ⟨hs.seq hf, hb.seq hr⟩

theorem halvingValue_eq (q K i n X : Nat) :
    halvingValue q K i n X = (halveMod q)^[min n (K-i)] X := by
  induction n generalizing i X with
  | zero => simp [halvingValue]
  | succ n ih =>
    rw [halvingValue, ih]
    by_cases hi : i<K
    · rw [if_pos hi, show min (n+1) (K-i) = min n (K-(i+1))+1 by omega,
        Function.iterate_succ_apply]
    · simp [hi, show K-i=0 by omega, show K-(i+1)=0 by omega]

/-- 固定 512 轮执行恰好 K 次模减半；保留计数，工作区清零。 -/
theorem halveInPlace_spec (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (q K X : Nat) (hq : q % 2 = 1) (hX : X < q)
    (hfit : 2*q ≤ 2^L.data.length) (hK : K ≤ 512) :
    {{ L.data=X, L.counter.x=K, L.work=0 }} halveInPlace L q 0 512
    {{ L.data=(halveMod q)^[K] X, L.counter.x=K, L.work=0 }} := by
  have h := (halveInPlace_values L hnd hw q K 0 512 X hq hX hfit (by omega)).1
  rw [halvingValue_eq,Nat.sub_zero,min_eq_right hK] at h
  exact Triple.conseq (fun s h => (HalvingValues.iff L K X s).mpr h) h
    (fun s h => (HalvingValues.iff L K _ s).mp h)

/-- 显式前向加倍门列撤销 K 次模减半；计数不变，工作区清零。 -/
theorem restoreInPlace_spec (L : HalvingLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (q K X : Nat) (hq : q % 2 = 1) (hX : X < q)
    (hfit : 2*q ≤ 2^L.data.length) (hK : K ≤ 512) :
    {{ L.data=(halveMod q)^[K] X, L.counter.x=K, L.work=0 }} restoreInPlace L q 0 512
    {{ L.data=X, L.counter.x=K, L.work=0 }} := by
  have h := (halveInPlace_values L hnd hw q K 0 512 X hq hX hfit (by omega)).2
  rw [halvingValue_eq,Nat.sub_zero,min_eq_right hK] at h
  exact Triple.conseq (fun s h => (HalvingValues.iff L K _ s).mpr h) h
    (fun s h => (HalvingValues.iff L K X s).mp h)

/-- 两种轮的门数相同：3n+40 Toffoli、2n+39 次测量。 -/
theorem halveStep_counts (L : HalvingLayout) (hw : L.Widths) (q i : Nat) :
    toffoliCount (halveStep L q i) = 3*L.data.length+20 ∧
    measurementCount (halveStep L q i) = 2*L.data.length+19 ∧
    toffoliCount (doubleStep L q i) = 3*L.data.length+20 ∧
    measurementCount (doubleStep L q i) = 2*L.data.length+19 := by
  have hc := counterActiveXor_counts L.counter L.active i
  have ha := addInPlace_counts L.constant L.data L.chain L.cin hw.constant hw.chain
  have hs := subInPlace_counts L.constant L.data L.chain L.cin hw.constant hw.chain
  have hm := maskedConstant_counts L.flag L.constant q
  have hh := shift_counts L.active L.data
  have hl : L.carry.length = L.constant.length := by rw [L.carry_length, hw.chain, hw.constant]
  have hp := (compareLt_counts (some L.active) L.data L.constant L.carry L.cin L.flag
    hw.constant.symm hl).2.2 ((q+1)/2)
  simp only [halveStep, doubleStep, maskedAddConst, maskedSubConst,
    toffoliCount_append, measurementCount_append, hc.1, hc.2, ha.1, ha.2, hs.1, hs.2,
    hm.1, hm.2, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, hp.1, hp.2, hw.counter,
    hw.constant, Option.isSome_some, if_true, toffoliCount, measurementCount]
  have := hw.chain
  omega

theorem halveInPlace_counts (L : HalvingLayout) (hw : L.Widths) (q i n : Nat) :
    toffoliCount (halveInPlace L q i n) = n*(3*L.data.length+20) ∧
    measurementCount (halveInPlace L q i n) = n*(2*L.data.length+19) ∧
    toffoliCount (restoreInPlace L q i n) = n*(3*L.data.length+20) ∧
    measurementCount (restoreInPlace L q i n) = n*(2*L.data.length+19) := by
  induction n generalizing i with
  | zero => simp [halveInPlace,restoreInPlace,toffoliCount,measurementCount]
  | succ n ih =>
    have hs := halveStep_counts L hw q i
    have hn := ih (i+1)
    simp only [halveInPlace,restoreInPlace,toffoliCount_append,measurementCount_append,
      hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,Nat.succ_mul]
    simp only [Nat.add_comm, and_self]

/-- 减半门列使用的线路；计数器另一银行 out 不参与活动比较。 -/
def HalvingLayout.usedWires (L : HalvingLayout) : List Wire :=
  L.flag :: L.active :: L.cin :: (L.data ++ L.constant ++ L.carry ++
    (L.counter.cin :: (L.counter.x ++ L.counter.y ++ L.counter.carry)))

theorem HalvingLayout.usedWires_subset (L : HalvingLayout) : L.usedWires ⊆ L.wires := by
  intro w h
  simp only [HalvingLayout.usedWires,List.mem_cons,List.mem_append] at h
  have hc : (L.counter.cin::(L.counter.x++L.counter.y++L.counter.carry)) ⊆ L.counter.wires := by
    intro w h
    simp only [List.mem_cons,List.mem_append] at h
    rcases h with rfl | (h|h) | h
    · simp [AdderLayout.wires]
    · exact L.counter.reg_subset.1 h
    · exact L.counter.reg_subset.2.1 h
    · exact L.counter.reg_subset.2.2.2 h
  simp only [HalvingLayout.wires,List.mem_cons,List.mem_append]
  have hm : w=L.counter.cin ∨ (w∈L.counter.x ∨ w∈L.counter.y) ∨ w∈L.counter.carry →
      w∈L.counter.wires := fun h => hc (by simpa only [List.mem_cons,List.mem_append] using h)
  tauto

theorem halveStep_wires (L : HalvingLayout) (hw : L.Widths) (q i : Nat) :
    wires (halveStep L q i) = L.usedWires.toFinset ∧
    wires (doubleStep L q i) = L.usedWires.toFinset := by
  have hc := counterActiveXor_wires L.counter L.active i
  have hl : L.carry.length = L.constant.length := by rw [L.carry_length, hw.chain, hw.constant]
  have hp := (compareLt_wires (some L.active) L.data L.constant L.carry L.cin L.flag
    hw.constant.symm hl).2 ((q+1)/2)
  have ha := maskedConst_wires_subset L.flag L.constant L.data L.chain L.cin q hw.constant hw.chain
  have hh := shift_wires L.active L.data
  have hhead : L.data.head! ∈ L.data := List.head!_mem_self (L.data_ne_nil hw)
  have hsub : (L.flag :: L.cin :: (L.constant ++ L.data ++ L.chain)).toFinset ⊆ L.usedWires.toFinset := by
    intro w; simp [HalvingLayout.usedWires,HalvingLayout.carry]; tauto
  have har := ha.1.trans hsub
  have has := ha.2.trans hsub
  have hshift : (L.active :: L.data).toFinset ⊆ L.usedWires.toFinset := by
    intro w; simp [HalvingLayout.usedWires]; tauto
  have hsr : wires (shiftRight L.active L.data) ⊆ L.usedWires.toFinset := by
    rw [hh.1]; split_ifs; exact Finset.empty_subset _; exact hshift
  have hsl : wires (shiftLeft L.active L.data) ⊆ L.usedWires.toFinset := by
    rw [hh.2]; split_ifs; exact Finset.empty_subset _; exact hshift
  have hcsub : (L.active :: L.counter.cin :: (L.counter.x ++ L.counter.y ++ L.counter.carry)).toFinset ⊆ L.usedWires.toFinset := by
    intro w; simp [HalvingLayout.usedWires]; tauto
  have hpsub : (L.active :: L.flag :: L.cin :: (L.data ++ L.constant ++ L.carry)).toFinset ⊆
      L.usedWires.toFinset := by intro w; simp [HalvingLayout.usedWires]; tauto
  have hsingle : wires [Instr.CCX L.active L.data.head! L.flag] ⊆ L.usedWires.toFinset := by
    intro w
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false]
    rintro (rfl|rfl|rfl) <;> simp [HalvingLayout.usedWires,hhead]
  have hflip : wires [Instr.CX L.active L.flag] ⊆ L.usedWires.toFinset := by
    intro w
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false]
    rintro (rfl|rfl) <;> simp [HalvingLayout.usedWires]
  have hcover : L.usedWires.toFinset ⊆ (L.active :: L.counter.cin :: (L.counter.x ++ L.counter.y ++ L.counter.carry)).toFinset ∪
      (L.active :: L.flag :: L.cin :: (L.data ++ L.constant ++ L.carry)).toFinset := by
    intro w; simp only [HalvingLayout.usedWires,List.mem_toFinset,List.mem_cons,List.mem_append,Finset.mem_union]
    tauto
  simp only [Option.toList_some,List.singleton_append] at hp
  constructor
  · apply Finset.Subset.antisymm
    · simp only [halveStep,wires_append,Finset.union_subset_iff,hc,hp]
      exact ⟨⟨⟨⟨⟨⟨hcsub,hsingle⟩,har⟩,hsr⟩,hflip⟩,hpsub⟩,hcsub⟩
    · intro w hw'
      have := hcover hw'
      simp only [halveStep,wires_append,hc,hp,Finset.mem_union] at this ⊢
      tauto
  · apply Finset.Subset.antisymm
    · simp only [doubleStep,wires_append,Finset.union_subset_iff,hc,hp]
      exact ⟨⟨⟨⟨⟨⟨hcsub,hpsub⟩,hflip⟩,hsl⟩,has⟩,hsingle⟩,hcsub⟩
    · intro w hw'
      have := hcover hw'
      simp only [doubleStep,wires_append,hc,hp,Finset.mem_union] at this ⊢
      tauto

theorem halveInPlace_wires (L : HalvingLayout) (hw : L.Widths) (q i n : Nat) :
    wires (halveInPlace L q i n) = (if n=0 then ∅ else L.usedWires.toFinset) ∧
    wires (restoreInPlace L q i n) = (if n=0 then ∅ else L.usedWires.toFinset) := by
  induction n generalizing i with
  | zero => simp [halveInPlace,restoreInPlace,wires]
  | succ n ih =>
    have hs := halveStep_wires L hw q i
    have hn := ih (i+1)
    simp only [halveInPlace,restoreInPlace,wires_append,hs.1,hs.2,hn.1,hn.2,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
    split_ifs <;> simp

end ECDSAAdd.Arithmetic
