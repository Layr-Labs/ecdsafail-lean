import ECDSAAdd.Arithmetic.RoundSpec

namespace ECDSAAdd.Arithmetic

/-- 每轮独占两根历史线路；数据与计数工作区逐轮复用。 -/
structure RoundRecord where
  swap : Wire
  subtract : Wire

def RoundRecord.wires (r : RoundRecord) : List Wire := [r.swap,r.subtract]

namespace KaliskiRoundLayout

def withRecord (L : KaliskiRoundLayout) (r : RoundRecord) : KaliskiRoundLayout :=
  {L with swap:=r.swap,subtract:=r.subtract}

def sharedWires (L : KaliskiRoundLayout) : List Wire :=
  [L.done,L.oddWork,L.bothWork,L.compareCin]++L.data.wires++L.counter.wires

def tapeWires (L : KaliskiRoundLayout) (rs : List RoundRecord) : List Wire :=
  rs.flatMap RoundRecord.wires++L.sharedWires

theorem withRecord_perm (L : KaliskiRoundLayout) (r : RoundRecord) :
    (L.withRecord r).wires.Perm (r.wires++L.sharedWires) := by
  apply List.perm_iff_count.mpr
  intro w
  simp [wires,withRecord,sharedWires,RoundRecord.wires,List.count_cons,data,counter]
  omega

theorem swapCounter_data (L : KaliskiRoundLayout) : L.swapCounter.data=L.data := rfl

theorem swapCounter_counter (L : KaliskiRoundLayout) : L.swapCounter.counter=L.counter.swapCounter := by
  simp [swapCounter,counter,AdderLayout.swapCounter]

theorem shared_swap_perm (L : KaliskiRoundLayout) : L.swapCounter.sharedWires.Perm L.sharedWires := by
  change (_++L.swapCounter.data.wires++L.swapCounter.counter.wires).Perm (_++L.data.wires++L.counter.wires)
  rw [L.swapCounter_data,L.swapCounter_counter]
  exact List.Perm.append_left _ L.counter.swapCounter_perm

theorem withRecord_nodup (L : KaliskiRoundLayout) (r : RoundRecord) (rs : List RoundRecord)
    (hnd : (L.tapeWires (r::rs)).Nodup) : (L.withRecord r).wires.Nodup := by
  apply (L.withRecord_perm r).nodup_iff.mpr
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp hnd w
  simp only [tapeWires,List.flatMap_cons,List.count_append] at h ⊢
  omega

theorem tail_nodup (L : KaliskiRoundLayout) (r : RoundRecord) (rs : List RoundRecord)
    (hnd : (L.tapeWires (r::rs)).Nodup) : (L.swapCounter.tapeWires rs).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp hnd w
  have hp := L.shared_swap_perm.count_eq w
  simp only [tapeWires,List.flatMap_cons,List.count_append] at h ⊢
  omega

end KaliskiRoundLayout

/-- 固定门列按记录带长度展开；银行交替与 i 都由程序构造决定。 -/
def kaliskiLoop (L : KaliskiRoundLayout) (i : Nat) : List RoundRecord → Program
  | [] => []
  | r::rs => kaliskiRound (L.withRecord r) i ++ kaliskiLoop L.swapCounter (i+1) rs

/-- 先恢复后面的轮，再以前向逆轮清除当前两位记录。 -/
def kaliskiUnloop (L : KaliskiRoundLayout) (i : Nat) : List RoundRecord → Program
  | [] => []
  | r::rs => kaliskiUnloop L.swapCounter (i+1) rs ++ kaliskiUnround (L.withRecord r) i

def loopEndLayout (L : KaliskiRoundLayout) : Nat → KaliskiRoundLayout
  | 0 => L
  | n+1 => loopEndLayout L.swapCounter n

def kaliskiCodes : Nat → KState → List (Bool×Bool)
  | 0,_ => []
  | n+1,z => kaliskiCode z::kaliskiCodes n (kaliskiStep z)

/-- 两位记录按轮保存精确布尔值，不由已更新数据重新猜测。 -/
def TapeValues : List RoundRecord → List (Bool×Bool) → BasisState → Prop
  | [],[],_ => True
  | r::rs,c::cs,st => st r.swap=c.1 ∧ st r.subtract=c.2 ∧ TapeValues rs cs st
  | _,_,_ => False

theorem TapeValues.congr (rs : List RoundRecord) (cs : List (Bool×Bool)) (s t : BasisState)
    (h : TapeValues rs cs s) (he : ∀ w, w∈rs.flatMap RoundRecord.wires → t w=s w) : TapeValues rs cs t := by
  induction rs generalizing cs with
  | nil => cases cs <;> exact h
  | cons r rs ih =>
    cases cs with
    | nil => exact h
    | cons c cs =>
      refine ⟨(he _ (by simp [RoundRecord.wires])).trans h.1,
        (he _ (by simp [RoundRecord.wires])).trans h.2.1,ih cs h.2.2 ?_⟩
      intro w hw
      exact he w (by simp [hw])

end ECDSAAdd.Arithmetic
