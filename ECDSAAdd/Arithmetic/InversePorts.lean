import ECDSAAdd.Arithmetic.PoolLayout
import ECDSAAdd.Arithmetic.InverseResources

namespace ECDSAAdd.Arithmetic

private def poolRoundBit (w : Nat → Wire) (start : Nat) : RoundBit :=
  ⟨w start,w (start+1),w (start+2),w (start+3),w (start+4),
    w (start+5),w (start+6),w (start+7)⟩

private def poolAddBit (w : Nat → Wire) (start : Nat) : AddBit :=
  ⟨w start,w (start+1),w (start+2),w (start+3)⟩

/-- 基础轮的两根记录占位字段不会执行；每轮由 records 中的独立线路替换。 -/
private def poolFirstRound (w : Nat → Wire) : KaliskiRoundLayout :=
  ⟨(List.range 256).map (fun i => poolRoundBit w (5+8*i)),poolRoundBit w (5+8*256),w 4,
    (List.range 9).map (fun i => poolAddBit w (2062+4*i)),poolAddBit w (2062+4*9),
    w 2061,w 3,w 0,w 2102,w 2103,w 1,w 2⟩

/-- 现有求逆模块的 5699 根工作线映射到同一个模乘工作池的前缀。 -/
def poolInverse (w : Nat → Wire) (x out : List Wire) : InverseLayout :=
  ⟨⟨poolFirstRound w,
     (List.range 512).map (fun i => ⟨w (2102+2*i),w (2102+2*i+1)⟩),
     poolMod w 3126 256,wireBlock w 5184 257,
     wireBlock w 5441 257,out++[w 5698]⟩,x⟩

theorem poolInverse_widths (w : Nat → Wire) (x out : List Wire)
    (hx : x.length=256) (ho : out.length=256) : (poolInverse w x out).Widths := by
  constructor
  · exact hx
  · simp [poolInverse]
  · simp [poolInverse,poolFirstRound,KaliskiRoundLayout.counter,AdderLayout.width]
  · simp [poolInverse,poolFirstRound]
  · exact poolMod_width _ _ _
  · exact wireBlock_length _ _ _
  · exact wireBlock_length _ _ _
  · simp [poolInverse,ho]

theorem poolInverse_inputs (w : Nat → Wire) (x out : List Wire) (ho : out.length=256) :
    (poolInverse w x out).x=x ∧ (poolInverse w x out).out=out := by
  refine ⟨rfl,?_⟩
  change (out++[w 5698]).take 256=out
  rw [← ho,List.take_left]

private theorem poolRoundBit_wires (w : Nat → Wire) (start : Nat) :
    (poolRoundBit w start).wires=wireBlock w start 8 := by
  simp [poolRoundBit,RoundBit.wires,wireBlock,List.range',Nat.add_assoc]

private theorem poolAddBit_wires (w : Nat → Wire) (start : Nat) :
    addWires [poolAddBit w start]=wireBlock w start 4 := by
  simp [poolAddBit,addWires,wireBlock,List.range',Nat.add_assoc]

private theorem addWires_flatMap (bs : List AddBit) :
    addWires bs=bs.flatMap (fun b => addWires [b]) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [addWires] using ih

private theorem poolFirstRound_shared (w : Nat → Wire) :
    (poolFirstRound w).sharedWires=wireBlock w 0 2102 := by
  have hd : (poolFirstRound w).data.wires=wireBlock w 4 2057 := by
    have hb : (poolFirstRound w).data.bits=
        (List.range 257).map (fun i => poolRoundBit w (5+8*i)) := by
      rw [show (257:Nat)=256+1 from rfl,List.range_succ]
      simp [poolFirstRound,KaliskiRoundLayout.data]
    rw [RoundDataLayout.wires,hb,List.flatMap_map]
    simp only [poolRoundBit_wires]
    rw [wireBlock_flatMap]
    change w 4::wireBlock w (4+1) 2056=_
    rw [← wireBlock_append w 4 1 2056]
    rfl
  have hc : (poolFirstRound w).counter.wires=wireBlock w 2061 41 := by
    have hb : (poolFirstRound w).counter.bits=
        (List.range 10).map (fun i => poolAddBit w (2062+4*i)) := by
      rw [show (10:Nat)=9+1 from rfl,List.range_succ]
      simp [poolFirstRound,KaliskiRoundLayout.counter]
    rw [AdderLayout.wires,hb,addWires_flatMap,List.flatMap_map]
    simp only [poolAddBit_wires]
    rw [wireBlock_flatMap]
    change w 2061::wireBlock w (2061+1) 40=_
    rw [← wireBlock_append w 2061 1 40]
    rfl
  rw [KaliskiRoundLayout.sharedWires,hd,hc]
  change wireBlock w 0 4++wireBlock w 4 2057++wireBlock w 2061 41=_
  rw [show (4:Nat)=0+4 from rfl,wireBlock_append]
  rw [show (2061:Nat)=0+(4+2057) from rfl,wireBlock_append]

private theorem poolInverse_inner_perm (w : Nat → Wire) (x out : List Wire) :
    (poolInverse w x out).inner.wires.Perm (out++wireBlock w 0 5699) := by
  have hr : ((poolInverse w x out).inner.records.flatMap RoundRecord.wires)=
      wireBlock w 2102 1024 := by
    simp only [poolInverse,List.flatMap_map,RoundRecord.wires]
    change ((List.range 512).flatMap (fun i => wireBlock w (2102+2*i) 2))=_
    exact wireBlock_flatMap _ _ _ _
  have hj : wireBlock w 0 2102++wireBlock w 2102 1024++wireBlock w 3126 2058++
      wireBlock w 5184 257++wireBlock w 5441 257++wireBlock w 5698 1=
        wireBlock w 0 5699 := by
    rw [wireBlock_append w 0 2102 1024,wireBlock_append w 0 3126 2058,
      wireBlock_append w 0 5184 257,wireBlock_append w 0 5441 257,
      wireBlock_append w 0 5698 1]
  rw [InverseLoopLayout.wires,KaliskiRoundLayout.tapeWires,hr]
  change (wireBlock w 2102 1024++(poolFirstRound w).sharedWires++
    (wireBlock w 5184 257++wireBlock w 5441 257++
      (poolMod w 3126 256).wires)++(out++[w 5698])).Perm _
  rw [poolFirstRound_shared,poolMod_wires,← hj]
  change (wireBlock w 2102 1024++wireBlock w 0 2102++
    (wireBlock w 5184 257++wireBlock w 5441 257++wireBlock w 3126 2058)++
    (out++wireBlock w 5698 1)).Perm _
  apply List.perm_iff_count.mpr
  intro v
  simp only [List.count_append]
  ac_rfl

theorem poolInverse_work_perm (w : Nat → Wire) (x out : List Wire) (ho : out.length=256) :
    (poolInverse w x out).work.Perm (wireBlock w 0 5699) := by
  have hh := (poolInverse w x out).wires_perm
  unfold InverseLayout.wires at hh
  rw [(poolInverse_inputs w x out ho).1,(poolInverse_inputs w x out ho).2] at hh
  have ht := hh.trans (List.Perm.append_left x (poolInverse_inner_perm w x out))
  apply List.perm_iff_count.mpr
  intro v
  have hc := ht.count_eq v
  simp only [List.count_append] at hc
  omega

/-- 保留原池编号，跳过每个八线银行中的旧out位置10+8i。 -/
def poolInverseUsedWork (w : Nat → Wire) : List Wire :=
  wireBlock w 0 5 ++
    (List.range 257).flatMap (fun i => (poolRoundBit w (5+8*i)).usedWires) ++
    wireBlock w 2061 41 ++ (w 2102 :: (List.range 512).map (fun i => w (2103+2*i))) ++
    wireBlock w 3126 30 ++ wireBlock w 5698 1

theorem poolInverseUsedWork_length (w : Nat → Wire) : (poolInverseUsedWork w).length=2389 := by
  have hl (bs : List Nat) : (bs.flatMap (fun i => (poolRoundBit w (5+8*i)).usedWires)).length=7*bs.length := by
    induction bs with
    | nil => rfl
    | cons i bs ih =>
      rw [List.flatMap_cons,List.length_append,ih]
      change 7+7*bs.length=7*(bs.length+1)
      omega
  simp [poolInverseUsedWork,hl,wireBlock_length]

theorem poolInverse_used_perm (w : Nat → Wire) (x out : List Wire) :
    (poolInverse w x out).usedWires.Perm (x++out++poolInverseUsedWork w) := by
  have hd : (poolFirstRound w).data.bits=
      (List.range 257).map (fun i => poolRoundBit w (5+8*i)) := by
    rw [show (257:Nat)=256+1 from rfl,List.range_succ]
    simp [poolFirstRound,KaliskiRoundLayout.data]
  have hc : (poolFirstRound w).counter.wires=wireBlock w 2061 41 := by
    have hb : (poolFirstRound w).counter.bits=
        (List.range 10).map (fun i => poolAddBit w (2062+4*i)) := by
      rw [show (10:Nat)=9+1 from rfl,List.range_succ]
      simp [poolFirstRound,KaliskiRoundLayout.counter]
    rw [AdderLayout.wires,hb,addWires_flatMap,List.flatMap_map]
    simp only [poolAddBit_wires]
    rw [wireBlock_flatMap]
    change w 2061::wireBlock w (2061+1) 40=_
    rw [← wireBlock_append w 2061 1 40]
    rfl
  have hr : oneBitRecordWires (poolInverse w x out).inner.records =
      w 2102 :: (List.range 512).map (fun i => w (2103+2*i)) := by
    unfold poolInverse
    rw [oneBitRecordWires_range (n:=511)]
    simp only [Nat.mul_zero,Nat.add_zero]
    apply congrArg (List.cons (w 2102))
    apply List.map_congr_left
    intro i _
    congr 1
    omega
  rw [InverseLayout.usedWires,InverseLoopLayout.usedWires,InverseLoopLayout.usedCoreWires,
    KaliskiRoundLayout.usedRecordTapeWires,hr]
  change (x++((w 2102 :: (List.range 512).map (fun i => w (2103+2*i)))++(poolFirstRound w).usedSharedWires++
    (poolMod w 3126 256).wires.take 30++
    (out++[w 5698]))).Perm _
  rw [KaliskiRoundLayout.usedSharedWires,RoundDataLayout.usedWires,hd,hc,
    List.flatMap_map,poolMod_wires]
  have ht : (wireBlock w 3126 2058).take 30=wireBlock w 3126 30 := by
    rw [←wireBlock_append w 3126 30 2028]
    simpa only [wireBlock_length] using List.take_left (l₁ := wireBlock w 3126 30) (l₂ := wireBlock w 3156 2028)
  rw [ht,poolInverseUsedWork]
  change (x++((w 2102 :: (List.range 512).map (fun i => w (2103+2*i)))++([w 0,w 1,w 2,w 3,w 4]++
    ((List.range 257).flatMap (fun i => (poolRoundBit w (5+8*i)).usedWires))++wireBlock w 2061 41)++
    wireBlock w 3126 30++(out++[w 5698]))).Perm _
  apply List.perm_iff_count.mpr
  intro v
  rw [show wireBlock w 0 5=[w 0,w 1,w 2,w 3,w 4] from rfl,
    show wireBlock w 5698 1=[w 5698] from rfl]
  simp only [List.count_append,List.count_cons,List.count_nil]
  omega

theorem poolInverse_nodup (w : Nat → Wire) (x out : List Wire) (ho : out.length=256)
    (h : (x++out++wireBlock w 0 5699).Nodup) : (poolInverse w x out).wires.Nodup := by
  rw [InverseLayout.wires,(poolInverse_inputs w x out ho).1,(poolInverse_inputs w x out ho).2]
  exact (List.Perm.append_left (x++out) (poolInverse_work_perm w x out ho)).nodup_iff.mpr h

end ECDSAAdd.Arithmetic
