import ECDSAAdd.Arithmetic.InverseScale
import ECDSAAdd.Arithmetic.InverseLoopLayout

namespace ECDSAAdd.Arithmetic.InverseLoopLayout

/-- 两次Kaliski循环之间可借用的零工作区，不含a或记录带。 -/
def scaleBorrow (I : InverseLoopLayout) : List Wire := I.temp++I.arithmetic.wires

/-- 历史按y、zero低4位、carry排列；不使用已退出支持集的out。 -/
def scaleLive (I : InverseLoopLayout) : List Wire :=
  I.middle.data.reg .y ++ (I.middle.data.reg .zero).take 4 ++ I.middle.data.reg .carry

/-- §22的固定借用视图；getD的默认位仅使坏布局上的定义全域成立。 -/
def scaling (I : InverseLoopLayout) : InverseScaleLayout where
  a := I.a
  k := I.middle.k
  factor := I.scaleBorrow.take 257
  stage := {
    acc := I.scaleLive.take 261
    history := (I.scaleLive.drop 261).take 256
    flag := I.scaleLive.getD 517 I.first.done
    table := (I.scaleBorrow.drop 257).take 261
    mask := (I.scaleBorrow.drop 518).take 261
    carry := (I.scaleBorrow.drop 779).take 260
    cin := I.scaleBorrow.getD 1039 I.first.done
    pad := (I.scaleBorrow.drop 1040).take 5
    scratch := (I.scaleBorrow.drop 1045).take 3 }
  extraScratch := (I.scaleBorrow.drop 1048).take 6

theorem scaleBorrow_length (I : InverseLoopLayout) (ht : I.temp.length=257)
    (ha : I.arithmetic.width=256) : I.scaleBorrow.length=2315 := by
  have hb (bs : List ModBit) : (bs.flatMap ModBit.all).length=8*bs.length := by
    induction bs with
    | nil => simp
    | cons b bs ih => simp [ModBit.all,ih]; omega
  simp only [scaleBorrow,ModLayout.wires,List.length_append,List.length_cons,
    hb,ModLayout.bits,List.length_cons,List.length_nil,ht]
  simp only [ModLayout.width] at ha
  omega

theorem scaleLive_length (I : InverseLoopLayout) (hl : I.first.low.length=256) :
    I.scaleLive.length=518 := by
  have hd (f : RoundField) : (I.middle.data.reg f).length=257 := by
    rw [middle,loopEnd_data,I.first.data_reg_length,hl]
  simp [scaleLive,hd]

theorem scaling_widths (I : InverseLoopLayout) (ha : I.a.length=257)
    (ht : I.temp.length=257) (hm : I.arithmetic.width=256)
    (hl : I.first.low.length=256) (hk : I.first.counter.width=10) : I.scaling.Widths := by
  have hb := I.scaleBorrow_length ht hm
  have hh := I.scaleLive_length hl
  have hc : I.middle.k.length=10 := by
    change I.middle.counter.x.length=10
    simpa only [AdderLayout.x,List.length_map,AdderLayout.width] using
      (loopEnd_counter_width I.first I.records.length).trans hk
  refine ⟨ha,hc,?_,⟨?_,?_,?_,?_,?_,?_,?_⟩,?_⟩ <;>
    simp [scaling,hb,hh]

private theorem one_slice (B : List Wire) (fallback : Wire) (n : Nat) (hn : n<B.length) :
    (B.drop n).take 1=[B.getD n fallback] := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hi'
    have : i=0 := by simpa using hi'
    subst i
    simp [hn]

theorem scaling_work (I : InverseLoopLayout) (ht : I.temp.length=257)
    (hm : I.arithmetic.width=256) : I.scaling.work=I.scaleBorrow.take 1054 := by
  have h := one_slice I.scaleBorrow I.first.done 1039 (by rw [I.scaleBorrow_length ht hm]; omega)
  simp only [scaling,InverseScaleLayout.work,MontStageLayout.work]
  rw [←h]
  simp only [←List.append_assoc,←List.take_add]

theorem scaling_live (I : InverseLoopLayout) (hl : I.first.low.length=256) :
    I.scaling.live=I.scaleLive := by
  have h := one_slice I.scaleLive I.first.done 517 (by rw [I.scaleLive_length hl]; omega)
  simp only [scaling,InverseScaleLayout.live]
  rw [←h,←List.take_add,←List.take_add]
  exact List.take_of_length_le (by rw [I.scaleLive_length hl])

private theorem live_count (D : RoundDataLayout) (w : Wire) :
    (D.reg .y).count w+(D.reg .zero).count w+(D.reg .carry).count w≤D.wires.count w := by
  rcases D with ⟨bs,cin⟩
  have h : (bs.map (fun b => b.y)).count w+(bs.map (fun b => b.zero)).count w+
      (bs.map (fun b => b.carry)).count w≤(bs.flatMap RoundBit.wires).count w := by
    induction bs with
    | nil => simp
    | cons b bs ih =>
      simp only [List.map_cons,List.flatMap_cons,List.count_append,RoundBit.wires,List.count_cons,List.count_nil]
      omega
  simp only [RoundDataLayout.reg,RoundBit.get,RoundDataLayout.wires,List.count_cons]
  omega

private theorem counter_count (L : AdderLayout) (w : Wire) : L.x.count w≤L.wires.count w := by
  rcases L with ⟨bs,cin⟩
  have h : (bs.map AddBit.x).count w≤(addWires bs).count w := by
    induction bs with
    | nil => simp [addWires]
    | cons b bs ih =>
      simp only [List.map_cons,addWires,List.count_cons] at *
      omega
  simp only [AdderLayout.x,AdderLayout.wires,List.count_cons]
  omega

theorem scaling_nodup (I : InverseLoopLayout) (ha : I.wires.Nodup)
    (ht : I.temp.length=257) (hm : I.arithmetic.width=256) (hl : I.first.low.length=256) :
    I.scaling.wires.Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have hh := List.nodup_iff_count.mp ha w
  have hp := I.middle_perm.count_eq w
  have hd := live_count I.middle.data w
  have hz := (List.take_sublist 4 (I.middle.data.reg .zero)).count_le w
  have hb := (List.take_sublist 1054 I.scaleBorrow).count_le w
  have hk := counter_count I.middle.counter w
  simp only [InverseScaleLayout.wires,I.scaling_work ht hm,I.scaling_live hl]
  change (I.a++I.middle.k++I.scaleLive++I.scaleBorrow.take 1054).count w≤1
  simp only [wires,extra,scaleLive,scaleBorrow,KaliskiRoundLayout.tapeWires,
    KaliskiRoundLayout.sharedWires,KaliskiRoundLayout.k,List.count_append,List.count_cons,List.count_nil] at hh hp hb ⊢
  omega

/-- 历史只借用原轮工作位，因而正轮结束的零断言足以初始化缩放。 -/
theorem scaleLive_subset (I : InverseLoopLayout) : I.scaleLive⊆I.middle.data.work := by
  intro w h
  simp only [scaleLive,List.mem_append] at h
  simp only [RoundDataLayout.work,List.mem_cons,List.mem_append]
  rcases h with (h|h)|h
  · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (List.mem_of_mem_take h))
  · exact Or.inr (Or.inl (Or.inr h))

end ECDSAAdd.Arithmetic.InverseLoopLayout
