import ECDSAAdd.Arithmetic.DialogResources
import ECDSAAdd.Arithmetic.PoolLayout

namespace ECDSAAdd.Arithmetic
namespace DialogLayout

private def dataBit (w : Nat → Wire) (x y : List Wire) (i : Nat) : RoundBit :=
  ⟨w (5+5*i),w (5+5*i+1),x.getD i 0,y.getD i 0,w (5+5*i+2),
    w (2355+i),w (5+5*i+3),w (5+5*i+4)⟩

private def countBit (w : Nat → Wire) (i : Nat) : AddBit :=
  ⟨w (1291+4*i),w (1291+4*i+1),w (1291+4*i+2),w (1291+4*i+3)⟩

/-- 五个值走字按位交错；外部X/Y映射到不触及的r/s，Z占池末257位。 -/
def fromPool (w : Nat → Wire) (g : Wire) (x y : List Wire) : DialogLayout :=
  ⟨⟨(List.range 256).map (dataBit w x y),
      {dataBit w x y 256 with r:=g,s:=w 2612},w 4,
      (List.range 9).map (countBit w),countBit w 9,w 1290,w 3,w 0,
      w 1331,w 1332,w 1,w 2⟩,
    (List.range 512).map (fun i => ⟨w (1331+2*i),w (1331+2*i+1)⟩)⟩

theorem fromPool_widths (w : Nat → Wire) (g : Wire) (x y : List Wire) :
    (fromPool w g x y).Widths := by
  constructor <;> simp [fromPool,KaliskiRoundLayout.counter,AdderLayout.width]

private theorem getD_range (xs : List Wire) (n : Nat) (hn : xs.length=n) :
    (List.range n).map (fun i => xs.getD i 0)=xs := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem _ _ hj

theorem fromPool_fields (w : Nat → Wire) (g : Wire) (x y : List Wire)
    (hx : x.length=256) (hy : y.length=256) :
    (fromPool w g x y).control=g ∧ (fromPool w g x y).x=x ∧
    (fromPool w g x y).y=y++[w 2612] ∧
    (fromPool w g x y).z=wireBlock w 2355 257 := by
  have hr : (List.range 256).map (fun i => w (2355+i))++[w (2355+256)]=wireBlock w 2355 257 := by
    rw [show (257:Nat)=256+1 from rfl,←wireBlock_append w 2355 256 1]
    simp [wireBlock,List.range'_eq_map_range,Nat.add_comm]
  refine ⟨rfl,?_,?_,?_⟩
  · simpa only [fromPool,DialogLayout.x,List.map_map,Function.comp_def,dataBit] using getD_range x 256 hx
  · simpa only [fromPool,DialogLayout.y,KaliskiRoundLayout.s,KaliskiRoundLayout.data,RoundDataLayout.s,
      RoundDataLayout.reg,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,
      RoundBit.get,dataBit] using congrArg (·++[w 2612]) (getD_range y 256 hy)
  · simpa only [fromPool,z,KaliskiRoundLayout.data,RoundDataLayout.reg,List.map_append,List.map_cons,
      List.map_nil,List.map_map,Function.comp_def,RoundBit.get,dataBit] using hr

private theorem value_data (w : Nat → Wire) (g : Wire) (x y : List Wire) :
    (fromPool w g x y).first.data.valueUsedWires=wireBlock w 4 1286 := by
  have hb : (fromPool w g x y).first.data.bits.map RoundBit.valueUsedWires=
      (List.range 257).map (fun i => wireBlock w (5+5*i) 5) := by
    rw [show (257:Nat)=256+1 from rfl,List.range_succ]
    simp only [fromPool,KaliskiRoundLayout.data,List.map_append,List.map_cons,List.map_nil,List.map_map,
      Function.comp_def,RoundBit.valueUsedWires,dataBit]
    congr 1
  have hf := congrArg List.flatten hb
  change (fromPool w g x y).first.data.bits.flatMap RoundBit.valueUsedWires=
    (List.range 257).flatMap (fun i => wireBlock w (5+5*i) 5) at hf
  rw [wireBlock_flatMap] at hf
  change w 4 :: _ = _
  rw [hf,←wireBlock_append w 4 1 1285]
  rfl

private theorem value_counter (w : Nat → Wire) (g : Wire) (x y : List Wire) :
    (fromPool w g x y).first.counter.wires=wireBlock w 1290 41 := by
  have hb : (fromPool w g x y).first.counter.bits=(List.range 10).map (countBit w) := by
    rw [show (10:Nat)=9+1 from rfl,List.range_succ]
    simp [fromPool,KaliskiRoundLayout.counter]
  have hf (bs : List AddBit) : addWires bs=bs.flatMap (fun b => addWires [b]) := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simpa [addWires] using ih
  rw [AdderLayout.wires,hb,hf,List.flatMap_map]
  have single (i : Nat) : addWires [countBit w i]=wireBlock w (1291+4*i) 4 := by
    simp [countBit,addWires,wireBlock,List.range',Nat.add_assoc]
  simp only [single]
  rw [wireBlock_flatMap]
  change w 1290::wireBlock w 1291 40=_
  rw [←wireBlock_append w 1290 1 40]
  rfl

theorem fromPool_value_perm (w : Nat → Wire) (g : Wire) (x y : List Wire) :
    ((fromPool w g x y).first.valueTapeWires (fromPool w g x y).records).Perm (wireBlock w 0 2355) := by
  have hs : (fromPool w g x y).first.valueSharedWires=wireBlock w 0 1331 := by
    rw [KaliskiRoundLayout.valueSharedWires,value_data,value_counter]
    change wireBlock w 0 4++wireBlock w 4 1286++wireBlock w 1290 41=_
    rw [wireBlock_append w 0 4 1286,wireBlock_append w 0 1290 41]
  have ht : ((fromPool w g x y).records.flatMap RoundRecord.wires)=wireBlock w 1331 1024 := by
    simp only [fromPool,List.flatMap_map,RoundRecord.wires]
    change ((List.range 512).flatMap (fun i => wireBlock w (1331+2*i) 2))=_
    exact wireBlock_flatMap _ _ _ _
  rw [KaliskiRoundLayout.valueTapeWires,hs,ht,←wireBlock_append w 0 1331 1024]
  exact List.perm_append_comm

theorem fromPool_work_perm (w : Nat → Wire) (g : Wire) (x y : List Wire)
    (hx : x.length=256) (hy : y.length=256) :
    (fromPool w g x y).work.Perm (wireBlock w 0 2612) := by
  have hz := (fromPool_fields w g x y hx hy).2.2.2
  rw [work,hz,←wireBlock_append w 0 2355 257]
  exact (fromPool_value_perm w g x y).append_right _

theorem fromPool_wires_perm (w : Nat → Wire) (g : Wire) (x y : List Wire)
    (hx : x.length=256) (hy : y.length=256) :
    (fromPool w g x y).wires.Perm (g::x++y++wireBlock w 0 2613) := by
  apply List.perm_iff_count.mpr
  intro q
  have he := (fromPool w g x y).external_value_perm.count_eq q
  have hp := (fromPool_work_perm w g x y hx hy).count_eq q
  have fields := fromPool_fields w g x y hx hy
  have hb := congrArg (List.count q) (wireBlock_append w 0 2612 1)
  have hs : wireBlock w 2612 1=[w 2612] := rfl
  simp only [external,work,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,
    hs,List.count_append,List.count_cons,List.count_nil,Nat.reduceAdd] at he hp hb ⊢
  omega

end DialogLayout
end ECDSAAdd.Arithmetic
