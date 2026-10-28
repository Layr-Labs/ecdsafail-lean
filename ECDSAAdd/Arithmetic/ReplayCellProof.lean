import ECDSAAdd.Arithmetic.ReplayCellState

namespace ECDSAAdd.Arithmetic

/-- 规范自然数形式的回放函数；第一坐标对应目标 z。 -/
def replayNatStep (p : Nat) (C W S : Bool) (X Y : Nat) : Nat×Nat :=
  let A := if W then Y else X
  let B := if W then X else Y
  let D := if S then (A+p-B)%p else A
  let H := if C then halveMod p D else D
  if W then (B,H) else (H,B)

def replayNatUnstep (p : Nat) (C W S : Bool) (X Y : Nat) : Nat×Nat :=
  let A := if W then Y else X
  let B := if W then X else Y
  let D := if C then (2*A)%p else A
  let H := if S then (D+B)%p else D
  if W then (B,H) else (H,B)

theorem replayNatStep_bound (p X Y : Nat) (C W S : Bool) (hp : p%2=1)
    (hX : X<p) (hY : Y<p) :
    (replayNatStep p C W S X Y).1<p ∧ (replayNatStep p C W S X Y).2<p := by
  have hp0 : 0<p := by omega
  have hd : (if S then ((if W then Y else X)+p-(if W then X else Y))%p
      else (if W then Y else X))<p := by
    split_ifs <;> first | exact Nat.mod_lt _ hp0 | assumption
  have hh := halve_mod_bound p _ hp hd
  cases W <;> cases C <;> simpa [replayNatStep] using (by constructor <;> assumption : _)

theorem replayNatUnstep_bound (p X Y : Nat) (C W S : Bool) (hp : 0<p)
    (hX : X<p) (hY : Y<p) :
    (replayNatUnstep p C W S X Y).1<p ∧ (replayNatUnstep p C W S X Y).2<p := by
  have hd : (if C then (2*(if W then Y else X))%p else (if W then Y else X))<p := by
    split_ifs <;> first | exact Nat.mod_lt _ hp | assumption
  have hh : (if S then ((if C then (2*(if W then Y else X))%p else (if W then Y else X))+
      (if W then X else Y))%p else (if C then (2*(if W then Y else X))%p else (if W then Y else X)))<p := by
    split_ifs <;> first | exact Nat.mod_lt _ hp | assumption
  cases W <;> simp only [replayNatUnstep,Bool.false_eq_true,if_false,if_true] at * <;> exact ⟨by assumption,by assumption⟩

/-- 两次低位交换、受控模减和活动减半的全记录规格。 -/
theorem replayCell_spec (active swap sub : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C W S : Bool) (hw : L.Widths n)
    (hnd : (active::swap::sub::L.wires).Nodup) (hp : p%2=1) (hpn : p<2^n)
    (hX : X<p) (hY : Y<p) :
    Triple (ReplayValues active swap sub L C W S X Y) (replayCell active swap sub L p)
      (ReplayValues active swap sub L C W S (replayNatStep p C W S X Y).1
        (replayNatStep p C W S X Y).2) := by
  let A := if W then Y else X
  let B := if W then X else Y
  let D := if S then (A+p-B)%p else A
  let H := if C then halveMod p D else D
  have ha : A<p := by dsimp [A]; split <;> assumption
  have hb : B<p := by dsimp [B]; split <;> assumption
  have hp0 : 0<p := by omega
  have hd : D<p := by dsimp [D]; split; exact Nat.mod_lt _ hp0; exact ha
  have hh : H<p := by dsimp [H]; split; exact halve_mod_bound p D hp hd; exact hd
  have h1 := ReplayValues.swap_step active swap sub L n X Y C W S hw hnd (by omega) (by omega)
  have h2 := ReplayValues.subtract_step active swap sub L n p A B C W S hw hnd hp0 hpn ha hb
  have h3 := ReplayValues.half_step active swap sub L n p D B C W S hw hnd hp hpn hd
  have h4 := ReplayValues.swap_step active swap sub L n H B C W S hw hnd (by omega) (by omega)
  have hall := ((h1.seq h2).seq h3).seq h4
  cases W <;> simpa only [replayCell,List.append_assoc,replayNatStep,A,B,D,H,
    Bool.false_eq_true,if_false,if_true] using hall

/-- 反回放由新的前向模倍/模加门列组成，所有记录下相位恢复。 -/
theorem replayUncell_spec (active swap sub : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C W S : Bool) (hw : L.Widths n)
    (hnd : (active::swap::sub::L.wires).Nodup) (hp : p%2=1) (hpn : p<2^n)
    (hX : X<p) (hY : Y<p) :
    Triple (ReplayValues active swap sub L C W S X Y) (replayUncell active swap sub L p)
      (ReplayValues active swap sub L C W S (replayNatUnstep p C W S X Y).1
        (replayNatUnstep p C W S X Y).2) := by
  let A := if W then Y else X
  let B := if W then X else Y
  let D := if C then (2*A)%p else A
  let H := if S then (D+B)%p else D
  have ha : A<p := by dsimp [A]; split <;> assumption
  have hb : B<p := by dsimp [B]; split <;> assumption
  have hp0 : 0<p := by omega
  have hd : D<p := by dsimp [D]; split; exact Nat.mod_lt _ hp0; exact ha
  have hh : H<p := by dsimp [H]; split; exact Nat.mod_lt _ hp0; exact hd
  have h1 := ReplayValues.swap_step active swap sub L n X Y C W S hw hnd (by omega) (by omega)
  have h2 := ReplayValues.double_step active swap sub L n p A B C W S hw hnd hp hpn ha
  have h3 := ReplayValues.add_step active swap sub L n p D B C W S hw hnd hp0 hpn hd hb
  have h4 := ReplayValues.swap_step active swap sub L n H B C W S hw hnd (by omega) (by omega)
  have hall := ((h1.seq h2).seq h3).seq h4
  cases W <;> simpa only [replayUncell,List.append_assoc,replayNatUnstep,A,B,D,H,
    Bool.false_eq_true,if_false,if_true] using hall

end ECDSAAdd.Arithmetic
