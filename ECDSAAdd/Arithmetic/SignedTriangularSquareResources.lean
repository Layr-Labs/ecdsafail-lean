import ECDSAAdd.Arithmetic.SignedTriangularSquare

namespace ECDSAAdd.Arithmetic

@[simp] theorem cxFrom_toffoliCount (c : Wire) (ys : List Wire) :
    toffoliCount (cxFrom c ys)=0 := by
  induction ys <;> simp_all [cxFrom,toffoliCount]

@[simp] theorem cxFrom_measurementCount (c : Wire) (ys : List Wire) :
    measurementCount (cxFrom c ys)=0 := by
  induction ys <;> simp_all [cxFrom,measurementCount]

@[simp] theorem xorWhenFalse_toffoliCount (c : Wire) (ys : List Wire) :
    toffoliCount (xorWhenFalse c ys)=0 := by
  induction ys <;> simp_all [xorWhenFalse,toffoliCount]

@[simp] theorem xorWhenFalse_measurementCount (c : Wire) (ys : List Wire) :
    measurementCount (xorWhenFalse c ys)=0 := by
  induction ys <;> simp_all [xorWhenFalse,measurementCount]

theorem signedSquareRow_counts (c : Wire) (xs dst pad carry : List Wire)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length) :
    toffoliCount (signedSquareRow c xs dst pad carry)=xs.length ∧
      measurementCount (signedSquareRow c xs dst pad carry)=xs.length := by
  have hs : (xs++pad.take 1).length=dst.length := by simp [hd,hp]
  have hk : (carry.take xs.length).length+1=dst.length := by simp [hd,hc]
  have h := addInPlace_counts (xs++pad.take 1) dst (carry.take xs.length) c hs hk
  simp [signedSquareRow,toffoliCount_append,measurementCount_append,h.1,h.2]
  omega

theorem signedSquareRowClear_counts (c : Wire) (xs dst pad carry : List Wire)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length) :
    toffoliCount (signedSquareRowClear c xs dst pad carry)=xs.length ∧
      measurementCount (signedSquareRowClear c xs dst pad carry)=xs.length := by
  have hs : (xs++pad.take 1).length=dst.length := by simp [hd,hp]
  have hk : (carry.take xs.length).length+1=dst.length := by simp [hd,hc]
  have h := addInPlace_counts (xs++pad.take 1) dst (carry.take xs.length) c hs hk
  simp [signedSquareRowClear,toffoliCount_append,measurementCount_append,h.1,h.2,
    (notRegister_counts dst).1,(notRegister_counts dst).2]
  omega

def signedSquareRowsCount : Nat → Nat
  | 0 => 0
  | n+1 => n+signedSquareRowsCount n

theorem signedSquareRows_counts (xs dst pad carry : List Wire)
    (hd : dst.length=2*xs.length) (hp : xs.length≤1 ∨ 1≤pad.length)
    (hc : xs.length-1≤carry.length) :
    (toffoliCount (signedSquareRows xs dst pad carry)=signedSquareRowsCount xs.length ∧
      measurementCount (signedSquareRows xs dst pad carry)=signedSquareRowsCount xs.length) ∧
    (toffoliCount (signedSquareRowsClear xs dst pad carry)=signedSquareRowsCount xs.length ∧
      measurementCount (signedSquareRowsClear xs dst pad carry)=signedSquareRowsCount xs.length) := by
  induction xs generalizing dst with
  | nil => simp [signedSquareRows,signedSquareRowsClear,signedSquareRowsCount,toffoliCount,measurementCount]
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedSquareRows,signedSquareRowsClear,signedSquareRowsCount,toffoliCount,measurementCount]
    | cons d tail =>
      simp only [List.length_cons] at hd hp hc
      have hcap : (d::tail).length+1≤(dst.drop 1).length := by
        simp
        omega
      have hrow : ((dst.drop 1).take ((d::tail).length+1)).length=(d::tail).length+1 := by
        exact List.length_take_of_le hcap
      have hnext : (dst.drop 2).length=2*(d::tail).length := by
        simp [List.length_drop]
        omega
      have hpad : 1≤pad.length := by rcases hp with hp|hp <;> omega
      have hcarry : (d::tail).length≤carry.length := by
        change tail.length+1≤carry.length
        omega
      have hr := signedSquareRow_counts c (d::tail)
        ((dst.drop 1).take ((d::tail).length+1)) pad carry hrow hpad hcarry
      have hrc := signedSquareRowClear_counts c (d::tail)
        ((dst.drop 1).take ((d::tail).length+1)) pad carry hrow hpad hcarry
      have hrecCarry : (d::tail).length-1≤carry.length := by omega
      have hi := ih (dst.drop 2) hnext (Or.inr hpad) hrecCarry
      constructor
      · constructor
        · rw [signedSquareRows,toffoliCount_append,hr.1,hi.1.1]
          simp [signedSquareRowsCount]
        · rw [signedSquareRows,measurementCount_append,hr.2,hi.1.2]
          simp [signedSquareRowsCount]
      · constructor
        · rw [signedSquareRowsClear,toffoliCount_append,hi.2.1,hrc.1]
          simp [signedSquareRowsCount]
          omega
        · rw [signedSquareRowsClear,measurementCount_append,hi.2.2,hrc.2]
          simp [signedSquareRowsCount]
          omega

theorem signedSquareRowsCount_closed (n : Nat) :
    2*signedSquareRowsCount n=n*(n-1) := by
  cases n with
  | zero => simp [signedSquareRowsCount]
  | succ n =>
    induction n with
    | zero => simp [signedSquareRowsCount]
    | succ n ih =>
      simp only [signedSquareRowsCount] at ih ⊢
      have h1 : n+1-1=n := by omega
      have h2 : n+1+1-1=n+1 := by omega
      rw [h1] at ih
      rw [h2]
      nlinarith

@[simp] theorem signedSquareTop_toffoliCount (xs dst : List Wire) :
    toffoliCount (signedSquareTop xs dst)=0 := by
  induction xs generalizing dst with
  | nil => simp [signedSquareTop,toffoliCount]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp [signedSquareTop,toffoliCount]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,toffoliCount]
        | cons z zs => simp [signedSquareTop,toffoliCount]
    | cons y ys =>
      cases dst with
      | nil => simp [signedSquareTop,toffoliCount]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,toffoliCount]
        | cons b tail => simpa [signedSquareTop] using ih tail

@[simp] theorem signedSquareTop_measurementCount (xs dst : List Wire) :
    measurementCount (signedSquareTop xs dst)=0 := by
  induction xs generalizing dst with
  | nil => simp [signedSquareTop,measurementCount]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp [signedSquareTop,measurementCount]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,measurementCount]
        | cons z zs => simp [signedSquareTop,measurementCount]
    | cons y ys =>
      cases dst with
      | nil => simp [signedSquareTop,measurementCount]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,measurementCount]
        | cons b tail => simpa [signedSquareTop] using ih tail

theorem signedDiag_counts (xs dst mask carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length) :
    (toffoliCount (signedDiagSub xs dst mask carry cin)=dst.length-1 ∧
      measurementCount (signedDiagSub xs dst mask carry cin)=dst.length-1) ∧
    (toffoliCount (signedDiagAdd xs dst mask carry cin)=dst.length-1 ∧
      measurementCount (signedDiagAdd xs dst mask carry cin)=dst.length-1) := by
  have htake : (xs.take (xs.length-1)).length=(mask.take (xs.length-1)).length := by
    simp [List.length_take]
    omega
  have hsrc : (signedDiagSource xs mask).length=dst.length := by
    simp [signedDiagSource,List.length_take,Nat.min_eq_left hm]
    omega
  have hcy : (carry.take (dst.length-1)).length+1=dst.length := by simp [hc]; omega
  have hcopy := copyRegister_counts none (xs.take (xs.length-1)) (mask.take (xs.length-1)) htake
  have ha := addInPlace_counts (signedDiagSource xs mask) dst (carry.take (dst.length-1)) cin hsrc hcy
  have hs := subInPlace_counts (signedDiagSource xs mask) dst (carry.take (dst.length-1)) cin hsrc hcy
  simp [signedDiagSub,signedDiagAdd,signedDiagLoad,signedDiagUnload,
    toffoliCount_append,measurementCount_append,hcopy.1,hcopy.2,
    ha.1,ha.2,hs.1,hs.2]

theorem signedTriangularSquare_counts (xs dst pad mask carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hm : xs.length≤mask.length) (hc : dst.length-1≤carry.length) :
    (toffoliCount (signedTriangularSquare xs dst pad mask carry cin)=
        signedSquareRowsCount xs.length+(dst.length-1) ∧
      measurementCount (signedTriangularSquare xs dst pad mask carry cin)=
        signedSquareRowsCount xs.length+(dst.length-1)) ∧
    (toffoliCount (signedTriangularSquareClear xs dst pad mask carry cin)=
        signedSquareRowsCount xs.length+(dst.length-1) ∧
      measurementCount (signedTriangularSquareClear xs dst pad mask carry cin)=
        signedSquareRowsCount xs.length+(dst.length-1)) := by
  have hn : xs≠[] := by intro h; simp [h] at hx
  have hsingle : ∀x,xs≠[x] := by intro x h; simp [h] at hx
  have hr := signedSquareRows_counts xs dst pad carry hd (Or.inr hp) (by omega)
  have hg := signedDiag_counts xs dst mask carry cin hx hd hm hc
  cases xs with
  | nil => contradiction
  | cons x tail =>
    cases tail with
    | nil => exact False.elim (hsingle x rfl)
    | cons y ys =>
      simp [signedTriangularSquare,signedTriangularSquareClear,toffoliCount_append,
        measurementCount_append,hr.1.1,hr.1.2,hr.2.1,hr.2.2,hg.1.1,hg.1.2,hg.2.1,hg.2.2]
      omega

theorem signedTriangularSquare_counts_128 (xs dst pad mask carry : List Wire) (cin : Wire)
    (hx : xs.length=128) (hd : dst.length=256) (hp : 1≤pad.length)
    (hm : 128≤mask.length) (hc : 255≤carry.length) :
    (toffoliCount (signedTriangularSquare xs dst pad mask carry cin)=8383 ∧
      measurementCount (signedTriangularSquare xs dst pad mask carry cin)=8383) ∧
    (toffoliCount (signedTriangularSquareClear xs dst pad mask carry cin)=8383 ∧
      measurementCount (signedTriangularSquareClear xs dst pad mask carry cin)=8383) := by
  have h := signedTriangularSquare_counts xs dst pad mask carry cin (by omega)
    (by omega) hp (by omega) (by omega)
  have hc' := signedSquareRowsCount_closed 128
  simp only [hx,hd] at h
  omega

theorem signedTriangularSquare_counts_129 (xs dst pad mask carry : List Wire) (cin : Wire)
    (hx : xs.length=129) (hd : dst.length=258) (hp : 1≤pad.length)
    (hm : 129≤mask.length) (hc : 257≤carry.length) :
    (toffoliCount (signedTriangularSquare xs dst pad mask carry cin)=8513 ∧
      measurementCount (signedTriangularSquare xs dst pad mask carry cin)=8513) ∧
    (toffoliCount (signedTriangularSquareClear xs dst pad mask carry cin)=8513 ∧
      measurementCount (signedTriangularSquareClear xs dst pad mask carry cin)=8513) := by
  have h := signedTriangularSquare_counts xs dst pad mask carry cin (by omega)
    (by omega) hp (by omega) (by omega)
  have hc' := signedSquareRowsCount_closed 129
  simp only [hx,hd] at h
  omega

end ECDSAAdd.Arithmetic
