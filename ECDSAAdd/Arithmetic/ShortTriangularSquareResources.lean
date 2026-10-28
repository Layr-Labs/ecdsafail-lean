/- PR #81 的短源三角平方变体；与原三角平方共享基础加法器及状态断言。 -/
import ECDSAAdd.Arithmetic.ShortTriangularSquare

namespace ECDSAAdd.Arithmetic.ShortTriangular

theorem squareRow_counts (sub : Bool) (c : Wire) (xs pad mask dst carry : List Wire)
    (cin : Wire) (hx : 0 < xs.length) (hd : dst.length=2*xs.length)
    (_hp : xs.length≤pad.length) (hm : 2*xs.length≤mask.length)
    (hc : 2*xs.length-1≤carry.length) :
    toffoliCount (squareRow sub c xs pad mask dst carry cin)=3*xs.length-1 ∧
    measurementCount (squareRow sub c xs pad mask dst carry cin)=3*xs.length-1 := by
  have hs : xs.length≤(mask.take (2*xs.length)).length := by
    simp [List.length_take,Nat.min_eq_left hm]; omega
  have ht : (mask.take (2*xs.length)).length=dst.length := by simp [hd, Nat.min_eq_left hm]
  have hk : (carry.take (2*xs.length-1)).length+1=dst.length := by
    simp [List.length_take, Nat.min_eq_left hc]; omega
  have h := measuredShortInPlace_counts c xs
    (mask.take (2*xs.length)) dst (carry.take (2*xs.length-1)) cin hs ht hk
  cases sub <;> simp only [squareRow, Bool.false_eq_true, if_false, if_true]
  · simpa only [hd,show xs.length+2*xs.length=3*xs.length by omega] using h.1
  · simpa only [hd,show xs.length+2*xs.length=3*xs.length by omega] using h.2

theorem squareRow_wires (sub : Bool) (c : Wire) (xs pad mask dst carry : List Wire)
    (cin : Wire) (hx : 0 < xs.length) (hd : dst.length=2*xs.length)
    (_hp : xs.length≤pad.length) (hm : 2*xs.length≤mask.length)
    (hc : 2*xs.length-1≤carry.length) :
    wires (squareRow sub c xs pad mask dst carry cin)=
      (c::cin::(xs++mask.take (2*xs.length)++dst++
        carry.take (2*xs.length-1))).toFinset := by
  have hs : xs.length≤(mask.take (2*xs.length)).length := by
    simp [List.length_take,Nat.min_eq_left hm]; omega
  have ht : (mask.take (2*xs.length)).length=dst.length := by simp [hd, Nat.min_eq_left hm]
  have hk : (carry.take (2*xs.length-1)).length+1=dst.length := by
    simp [List.length_take, Nat.min_eq_left hc]; omega
  have h := measuredShortInPlace_wires c xs
    (mask.take (2*xs.length)) dst (carry.take (2*xs.length-1)) cin
    (List.length_pos_iff.mp hx) hs ht hk
  cases sub <;> simp only [squareRow, Bool.false_eq_true, if_false, if_true]
  · exact h.1
  · exact h.2

/-- Exact recurrence: each nontrivial k-bit cross row costs 3k−1. -/
def triangularSquareCount : Nat → Nat
  | 0 => 0
  | n+1 => triangularSquareCount n + (if n=0 then 0 else 3*n-1)

theorem triangularSquareCount_twice (n : Nat) :
    2*triangularSquareCount n=(n-1)*(3*n-2) := by
  induction n with
  | zero => simp [triangularSquareCount]
  | succ n ih =>
    by_cases hn : n=0
    · subst n; simp [triangularSquareCount]
    · have hp : 0<n := by omega
      have h1 : n-1+1=n := by omega
      have h2 : 3*n-2+2=3*n := by omega
      have h3 : 3*n-1+1=3*n := by omega
      have h4 : n+1-1=n := by omega
      have h5 : 3*(n+1)-2=3*n+1 := by omega
      simp only [triangularSquareCount,hn,if_false,h4,h5]
      nlinarith

theorem triangularSquareCount_closed (n : Nat) :
    triangularSquareCount n=(n-1)*(3*n-2)/2 := by
  rw [←triangularSquareCount_twice n]
  omega

/-- Each exact square and its independent cleanup cost (m−1)(3m−2)/2. -/
theorem triangularSquare_counts (xs dst pad mask carry : List Wire) (cin : Wire)
    (hd : dst.length=2*xs.length) (hp : xs.length-1≤pad.length)
    (hm : 2*(xs.length-1)≤mask.length) (hc : 2*(xs.length-1)-1≤carry.length) :
    (toffoliCount (triangularSquare xs dst pad mask carry cin)=(xs.length-1)*(3*xs.length-2)/2 ∧
      measurementCount (triangularSquare xs dst pad mask carry cin)=(xs.length-1)*(3*xs.length-2)/2) ∧
    (toffoliCount (triangularSquareClear xs dst pad mask carry cin)=(xs.length-1)*(3*xs.length-2)/2 ∧
      measurementCount (triangularSquareClear xs dst pad mask carry cin)=(xs.length-1)*(3*xs.length-2)/2) := by
  induction xs generalizing dst with
  | nil => simp [triangularSquare, triangularSquareClear, toffoliCount, measurementCount]
  | cons c xs ih =>
    cases dst with
    | nil => simp at hd
    | cons a dst =>
      cases dst with
      | nil => simp at hd; omega
      | cons b dst =>
        have hd' : dst.length=2*xs.length := by simp only [List.length_cons] at hd; omega
        have hp' : xs.length≤pad.length := by simpa using hp
        have hm' : 2*xs.length≤mask.length := by simpa using hm
        have hc' : 2*xs.length-1≤carry.length := by simpa using hc
        have hi := ih dst hd' (by omega) (by omega) (by omega)
        by_cases hx : xs=[]
        · subst xs; simp [triangularSquare, triangularSquareClear, toffoliCount, measurementCount]
        · have hn : 0<xs.length := List.length_pos_iff.mpr hx
          have ha := squareRow_counts false c xs pad mask dst carry cin hn hd' hp' hm' hc'
          have hs := squareRow_counts true c xs pad mask dst carry cin hn hd' hp' hm' hc'
          have he : (xs.length-1)*(3*xs.length-2)/2+(3*xs.length-1)=
              xs.length*(3*(xs.length+1)-2)/2 := by
            rw [←triangularSquareCount_closed xs.length]
            have hnext := triangularSquareCount_closed (xs.length+1)
            simp only [triangularSquareCount,Nat.ne_of_gt hn,if_false] at hnext
            simpa using hnext
          simp only [triangularSquare, triangularSquareClear, hx, if_false,
            toffoliCount_append, measurementCount_append, hi.1.1, hi.1.2, hi.2.1, hi.2.2,
            ha.1, ha.2, hs.1, hs.2, List.length_cons]
          simpa [toffoliCount, measurementCount,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using And.intro (And.intro he he) (And.intro he he)

/-- 按实际三角行列出的支持；第二个目标位不在任何行中。 -/
def triangularSquareWires : List Wire → List Wire → List Wire → List Wire → List Wire → Wire → List Wire
  | [], _, _, _, _, _ => []
  | c::xs, a::_b::dst, pad, mask, carry, cin =>
    triangularSquareWires xs dst pad mask carry cin ++
      (if xs=[] then [] else
        c::cin::(xs++mask.take (2*xs.length)++dst++
          carry.take (2*xs.length-1))) ++ [c,a]
  | _, _, _, _, _, _ => []

/-- 平方和清理程序有完全相同的实际支持，包括零位和单位宽度情形。 -/
theorem triangularSquare_wires (xs dst pad mask carry : List Wire) (cin : Wire)
    (hd : dst.length=2*xs.length) (hp : xs.length-1≤pad.length)
    (hm : 2*(xs.length-1)≤mask.length) (hc : 2*(xs.length-1)-1≤carry.length) :
    wires (triangularSquare xs dst pad mask carry cin)=
      (triangularSquareWires xs dst pad mask carry cin).toFinset ∧
    wires (triangularSquareClear xs dst pad mask carry cin)=
      (triangularSquareWires xs dst pad mask carry cin).toFinset := by
  induction xs generalizing dst with
  | nil => simp [triangularSquare, triangularSquareClear, triangularSquareWires, wires]
  | cons c xs ih =>
    cases dst with
    | nil => simp at hd
    | cons a dst =>
      cases dst with
      | nil => simp at hd; omega
      | cons b dst =>
        have hd' : dst.length=2*xs.length := by simp only [List.length_cons] at hd; omega
        have hp' : xs.length≤pad.length := by simpa using hp
        have hm' : 2*xs.length≤mask.length := by simpa using hm
        have hc' : 2*xs.length-1≤carry.length := by simpa using hc
        have hi := ih dst hd' (by omega) (by omega) (by omega)
        by_cases hx : xs=[]
        · subst xs
          simp [triangularSquare, triangularSquareClear, triangularSquareWires, wires, Instr.wires]
        · have hn : 0<xs.length := List.length_pos_iff.mpr hx
          have ha := squareRow_wires false c xs pad mask dst carry cin hn hd' hp' hm' hc'
          have hs := squareRow_wires true c xs pad mask dst carry cin hn hd' hp' hm' hc'
          simp only [triangularSquare, triangularSquareClear, triangularSquareWires, hx, if_false,
            wires_append, hi.1, hi.2, ha, hs, List.toFinset_append]
          constructor <;> ext w <;>
            simp [wires, Instr.wires, or_assoc, or_comm, or_left_comm]

/-- 每行只借用调用者给出的寄存器；此列表用于组合 frame 与布局包含证明。 -/
theorem triangularSquareWires_subset (xs dst pad mask carry : List Wire) (cin : Wire) :
    (triangularSquareWires xs dst pad mask carry cin).toFinset ⊆
      (cin::(xs++dst++pad++mask++carry)).toFinset := by
  induction xs generalizing dst with
  | nil => simp [triangularSquareWires]
  | cons c xs ih =>
    cases dst with
    | nil => simp [triangularSquareWires]
    | cons a dst =>
      cases dst with
      | nil => simp [triangularSquareWires]
      | cons b dst =>
        intro w hw
        simp only [triangularSquareWires, List.mem_toFinset, List.mem_append] at hw
        have hi := @ih dst w
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hi ⊢
        rcases hw with (hw | hw) | hw
        · rcases hi hw with hw | (((hw | hw) | hw) | hw) | hw
          all_goals simp [hw]
        · split_ifs at hw with hx
          · simp at hw
          · simp only [List.mem_cons, List.mem_append] at hw
            rcases hw with hw | hw | ((hw | hw) | hw) | hw
            · simp [hw]
            · simp [hw]
            · simp [hw]
            · have h := List.mem_of_mem_take hw
              simp [h]
            · simp [hw]
            · have h := List.mem_of_mem_take hw
              simp [h]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with hw | hw <;> simp [hw]

end ECDSAAdd.Arithmetic.ShortTriangular
