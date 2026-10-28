import ECDSAAdd.Arithmetic.RoundBody
import ECDSAAdd.Arithmetic.Borrow

namespace ECDSAAdd.Arithmetic

/-- 单轮布局：数据、共享工作区、双银行计数器、两位记录与常数个控制工作位。 -/
structure KaliskiRoundLayout where
  low : List RoundBit
  high : RoundBit
  cin : Wire
  counterLow : List AddBit
  counterHigh : AddBit
  active : Wire
  compareCin : Wire
  done : Wire
  swap : Wire
  subtract : Wire
  oddWork : Wire
  bothWork : Wire

namespace KaliskiRoundLayout

def data (L : KaliskiRoundLayout) : RoundDataLayout := ⟨L.low++[L.high],L.cin⟩
def counter (L : KaliskiRoundLayout) : AdderLayout := ⟨L.counterLow++[L.counterHigh],L.active⟩

/-- 更新后的 k 在 counter.out；比较借用旧的空银行，cin 单独保持为零。 -/
def comparator (L : KaliskiRoundLayout) : AdderLayout :=
  { L.counter.swapCounter with cin:=L.compareCin }

def u (L : KaliskiRoundLayout) : List Wire := L.data.u
def v (L : KaliskiRoundLayout) : List Wire := L.data.v
def r (L : KaliskiRoundLayout) : List Wire := L.data.r
def s (L : KaliskiRoundLayout) : List Wire := L.data.s
def k (L : KaliskiRoundLayout) : List Wire := L.counter.x
def kNext (L : KaliskiRoundLayout) : List Wire := L.counter.out

def scratch (L : KaliskiRoundLayout) : List Wire :=
  L.data.work ++ L.counter.y ++ L.counter.carry ++ [L.active,L.compareCin,L.oddWork,L.bothWork]

def wires (L : KaliskiRoundLayout) : List Wire :=
  [L.done,L.swap,L.subtract,L.oddWork,L.bothWork,L.compareCin] ++ L.data.wires ++ L.counter.wires

/-- 下一轮仅交换计数器两份银行的角色；数据及算术工作区保持相同位置。 -/
def swapCounter (L : KaliskiRoundLayout) : KaliskiRoundLayout :=
  { L with
    counterLow := L.counterLow.map (fun b => {b with x:=b.out,out:=b.x})
    counterHigh := {L.counterHigh with x:=L.counterHigh.out,out:=L.counterHigh.x} }

def controls (L : KaliskiRoundLayout) : List Wire :=
  [L.active,L.done,L.swap,L.subtract,L.oddWork,L.bothWork,L.compareCin]

theorem data_nodup (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) : L.data.wires.Nodup :=
  (List.nodup_append'.mp (List.nodup_append'.mp hnd).1).2.1

theorem counter_nodup (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) : L.counter.wires.Nodup :=
  (List.nodup_append'.mp hnd).2.1

theorem controls_data_nodup (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) :
    (L.controls++L.data.wires).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have hh := List.nodup_iff_count.mp hnd w
  simp only [wires,controls,List.count_append,List.count_cons,List.count_nil,counter,AdderLayout.wires] at hh ⊢
  omega

theorem control_not_data (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) (c : Wire) (hc : c∈L.controls) :
    c∉L.data.wires := List.disjoint_left.mp (List.nodup_append'.mp (L.controls_data_nodup hnd)).2.2 hc

theorem comparator_nodup (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) :
    (L.active::L.comparator.wires).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have hh := List.nodup_iff_count.mp hnd w
  have hp := L.counter.swapCounter_perm.count_eq w
  simp only [comparator,AdderLayout.wires,List.count_cons,AdderLayout.swapCounter] at hp ⊢
  simp only [wires,List.count_append,List.count_cons,List.count_nil,counter,AdderLayout.wires] at hh hp ⊢
  omega

theorem comparator_fields (L : KaliskiRoundLayout) :
    L.comparator.x=L.kNext ∧ L.comparator.out=L.k ∧
    L.comparator.y=L.counter.y ∧ L.comparator.carry=L.counter.carry ∧
    L.comparator.cin=L.compareCin ∧ L.comparator.width=L.counter.width := by
  have h := L.counter.swapCounter_fields
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,rfl,h.2.2.2.2.2⟩

theorem data_reg_length (L : KaliskiRoundLayout) (f : RoundField) :
    (L.data.reg f).length=L.low.length+1 := by
  simp [RoundDataLayout.reg,data]

end KaliskiRoundLayout

/-- 非空小端寄存器的最低位等于读值的奇偶位。 -/
theorem regValue_headBit (r : List Wire) (hn : r≠[]) (s : BasisState) :
    s r.head! = decide (regValue r s%2≠0) := by
  cases r with
  | nil => contradiction
  | cons a r => cases ha : s a <;> simp [regValue,ha]


/-- 先保存奇偶条件，直接把受控比较 XOR 到记录位，再清条件；不生成差寄存器。 -/
def recordRound (L : KaliskiRoundLayout) : Program :=
  [.CCX L.active L.u.head! L.oddWork, .CCX L.oddWork L.v.head! L.bothWork,
   .CX L.bothWork L.subtract, .CX L.oddWork L.swap] ++
  compareLt (some L.bothWork) L.v L.u (L.data.reg .carry) L.cin L.swap ++
  [.CCX L.oddWork L.v.head! L.bothWork, .CCX L.active L.u.head! L.oddWork]

/-- 只翻转活动辅助位，既用于装入 !done，也用于恢复 done 后的清理。 -/
def loadActive (L : KaliskiRoundLayout) : Program := [.X L.active,.CX L.done L.active]

def roundActiveXor (L : KaliskiRoundLayout) (i : Nat) : Program :=
  counterActiveXor L.comparator L.active i

/-- 终止轮先更新并计数，再改变 done；最后用 i<新 k 清理活动工作位。 -/
def kaliskiRound (L : KaliskiRoundLayout) (i : Nat) : Program :=
  loadActive L ++ recordRound L ++ kaliskiBodyProgram L.data L.active L.swap L.subtract ++
  counterInc L.counter ++ zeroControlled L.active L.done (L.data.zeroBits .v) ++ roundActiveXor L i

/-- 逆轮先由新 k 恢复活动位和旧 done，再恢复数据/计数，最后清两位记录。 -/
def kaliskiUnround (L : KaliskiRoundLayout) (i : Nat) : Program :=
  roundActiveXor L i ++ zeroControlled L.active L.done (L.data.zeroBits .v) ++
  kaliskiUnbodyProgram L.data L.active L.swap L.subtract ++ counterDec L.counter.swapCounter ++
  recordRound L ++ loadActive L

end ECDSAAdd.Arithmetic
