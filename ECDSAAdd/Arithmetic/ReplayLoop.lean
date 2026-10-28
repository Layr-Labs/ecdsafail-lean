import ECDSAAdd.Arithmetic.ReplayCellResources
import ECDSAAdd.Arithmetic.KaliskiLoop
import ECDSAAdd.Arithmetic.BorrowFrame

namespace ECDSAAdd.Arithmetic

/-- 十位计数器的比较 scratch 借用载荷格的零工作区。 -/
structure ReplayLayout where
  payload : ModInPlaceLayout
  counter : AdderLayout
  active : Wire

namespace ReplayLayout

def wires (L : ReplayLayout) (rs : List RoundRecord) : List Wire :=
  L.active::L.counter.x ++ rs.flatMap RoundRecord.wires ++ L.payload.wires

structure Valid (L : ReplayLayout) (n : Nat) (rs : List RoundRecord) : Prop where
  widths : L.payload.Widths n
  counterWidth : L.counter.width=10
  nodup : (L.wires rs).Nodup
  counterNodup : (L.active::L.counter.wires).Nodup
  constant : L.counter.y⊆L.payload.work
  carry : L.counter.carry⊆L.payload.work
  cin : L.counter.cin∈L.payload.work

theorem Valid.tail (L : ReplayLayout) (n : Nat) (r : RoundRecord) (rs : List RoundRecord)
    (h : L.Valid n (r::rs)) : L.Valid n rs := by
  refine ⟨h.widths,h.counterWidth,?_,h.counterNodup,h.constant,h.carry,h.cin⟩
  apply List.nodup_iff_count.mpr; intro q
  have hh := List.nodup_iff_count.mp h.nodup q
  simp only [wires,List.flatMap_cons,List.count_cons,List.count_append] at hh ⊢
  omega

theorem Valid.cell (L : ReplayLayout) (n : Nat) (rs : List RoundRecord) (r : RoundRecord)
    (h : L.Valid n rs) (hr : r∈rs) :
    (L.active::r.swap::r.subtract::L.payload.wires).Nodup := by
  have ht : r.wires.Sublist (rs.flatMap RoundRecord.wires) := by
    induction rs with
    | nil => simp at hr
    | cons t ts ih =>
      rcases List.mem_cons.mp hr with he|he
      · subst t; exact List.sublist_append_left _ _
      · exact (ih (h.tail L n t ts) he).trans (List.sublist_append_right _ _)
  apply List.nodup_iff_count.mpr; intro q
  have hh := List.nodup_iff_count.mp h.nodup q
  have hc := ht.count_le q
  simp only [wires,RoundRecord.wires,List.count_cons,List.count_append,List.count_nil] at hh hc ⊢
  omega
end ReplayLayout

/-- 每格计算和清除活动位，不从 00 记录推断终止。 -/
def replayRound (L : ReplayLayout) (r : RoundRecord) (p i : Nat) : Program :=
  counterActiveXor L.counter L.active i ++
  replayCell L.active r.swap r.subtract L.payload p ++
  counterActiveXor L.counter L.active i

def replayUnround (L : ReplayLayout) (r : RoundRecord) (p i : Nat) : Program :=
  counterActiveXor L.counter L.active i ++
  replayUncell L.active r.swap r.subtract L.payload p ++
  counterActiveXor L.counter L.active i

def replayLoop (L : ReplayLayout) (p i : Nat) : List RoundRecord → Program
  | [] => []
  | r::rs => replayRound L r p i ++ replayLoop L p (i+1) rs

def replayUnloop (L : ReplayLayout) (p i : Nat) : List RoundRecord → Program
  | [] => []
  | r::rs => replayUnloop L p (i+1) rs ++ replayUnround L r p i

/-- 回放过程只改变两个载荷；ref 保存记录带及外部线路的初值。 -/
def ReplayState (L : ReplayLayout) (ref : BasisState) (C : Bool) (X Y : Nat) (s : BasisState) : Prop :=
  s L.active=C ∧ regValue L.payload.z s=X ∧ regValue L.payload.a s=Y ∧
  regValue L.payload.work s=0 ∧
  ∀ q, q∉L.payload.z → q∉L.payload.a → q≠L.active → s q=ref q

def replayNatLoop (p K i : Nat) (ref : BasisState) : List RoundRecord → Nat×Nat → Nat×Nat
  | [],v => v
  | r::rs,v => replayNatLoop p K (i+1) ref rs
      (replayNatStep p (decide (i<K)) (ref r.swap) (ref r.subtract) v.1 v.2)

def replayNatUnloop (p K i : Nat) (ref : BasisState) : List RoundRecord → Nat×Nat → Nat×Nat
  | [],v => v
  | r::rs,v =>
    let u := replayNatUnloop p K (i+1) ref rs v
    replayNatUnstep p (decide (i<K)) (ref r.swap) (ref r.subtract) u.1 u.2

end ECDSAAdd.Arithmetic
