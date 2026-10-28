import ECDSAAdd.Baselines.SlotMapped

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

@[simp] theorem reverse_gateSlots (p : Program) : gateSlots p.reverse = gateSlots p := by
  simp [gateSlots, List.map_reverse]

@[simp] theorem xorWhenFalse_gateSlots (c : Wire) (ys : List Wire) :
    gateSlots (xorWhenFalse c ys) = 2*ys.length := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [xorWhenFalse, gateSlots_cons, instructionSlots, ih]; omega

theorem signedRow_gateSlots_le (c : Wire) (xs dst pad carry : List Wire) :
    gateSlots (signedSquareRow c xs dst pad carry) ≤ 12*(xs.length+1)+6*dst.length ∧
    gateSlots (signedSquareRowClear c xs dst pad carry) ≤ 12*(xs.length+1)+6*dst.length := by
  have ha := addInPlace_gateSlots_le (xs++pad.take 1) dst (carry.take xs.length) c
  simp only [List.length_append, List.length_take] at ha
  simp only [signedSquareRow, signedSquareRowClear, gateSlots_append, xorWhenFalse_gateSlots,
    notRegister_gateSlots, List.length_take]
  constructor <;> omega

theorem signedRows_gateSlots_le (xs dst pad carry : List Wire) :
    gateSlots (signedSquareRows xs dst pad carry) ≤ xs.length*(12*(xs.length+1)+6*dst.length) ∧
    gateSlots (signedSquareRowsClear xs dst pad carry) ≤ xs.length*(12*(xs.length+1)+6*dst.length) := by
  induction xs using List.twoStepInduction generalizing dst with
  | nil => simp [signedSquareRows, signedSquareRowsClear]
  | singleton x => simp [signedSquareRows, signedSquareRowsClear]
  | cons_cons x y xs ih ih' =>
    have ht := ih' y (dst.drop 2)
    have hr := signedRow_gateSlots_le x (y::xs) ((dst.drop 1).take ((y::xs).length+1)) pad carry
    simp only [List.length_drop, List.length_take, List.length_cons] at ht hr
    simp only [signedSquareRows, signedSquareRowsClear, gateSlots_append, List.length_cons]
    have hd : (dst.drop 2).length ≤ dst.length := by simp
    constructor <;> nlinarith [ht.1,ht.2,hr.1,hr.2, Nat.min_le_right (xs.length+1+1) (dst.length-1), Nat.sub_le dst.length 1, Nat.sub_le dst.length 2]

theorem signedTop_gateSlots_le (xs dst : List Wire) : gateSlots (signedSquareTop xs dst) ≤ 1 := by
  induction xs, dst using signedSquareTop.induct with
  | case1 dst => simp [signedSquareTop]
  | case2 x a z ds => simp [signedSquareTop, gateSlots_cons, instructionSlots]
  | case3 a x xs b c dst ih => simpa only [signedSquareTop] using ih
  | case4 xs dst h => simp [signedSquareTop]

theorem mappedSigned_gateSlots_le (xs dst pad carry : List Wire) (cin : Wire) :
    gateSlots (mappedSignedSquare xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 ∧
    gateSlots (mappedSignedSquareClear xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 := by
  have hr := signedRows_gateSlots_le xs dst pad carry
  have ht := signedTop_gateSlots_le xs dst
  have hm := mappedAdd_gateSlots_le (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin
  have hl : (mappedDiagonal xs).length ≤ 2*xs.length+1 := by
    simp only [mappedDiagonal, List.length_append, mappedRead_length, List.length_take, List.length_cons, List.length_nil]; omega
  simp only [mappedSignedSquare, mappedSignedSquareClear, mappedDiagSub, mappedDiagAdd,
    mappedSub, gateSlots_append, notRegister_gateSlots]
  constructor <;> omega

end ECDSAAdd.Baselines
