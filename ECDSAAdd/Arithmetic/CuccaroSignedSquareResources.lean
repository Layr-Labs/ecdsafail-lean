import ECDSAAdd.Arithmetic.CuccaroSignedSquareProof
import ECDSAAdd.Arithmetic.SignedSquareLeafSpec

namespace ECDSAAdd.Arithmetic

theorem cuccaroSignedSquareRow_wires_subset (c : Wire) (xs dst pad carry : List Wire)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) :
    wires (cuccaroSignedSquareRow c xs dst pad carry)⊆
      (c::xs++dst++pad++carry).toFinset := by
  have hs : (xs++pad.take 1).length=dst.length := by simp [hd,hp]
  have ha := cuccaroAdd_wires_subset (xs++pad.take 1) dst c
  have hxl := xorWhenFalse_wires_subset c (dst.take xs.length)
  have hxr := xorWhenFalse_wires_subset c dst
  intro q hq
  simp only [cuccaroSignedSquareRow,wires_append,Finset.mem_union] at hq
  rcases hq with (hq|hq)|hq
  · have h := hxl hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    have ht : q∈dst.take xs.length → q∈dst := List.mem_of_mem_take
    grind
  · have h := ha hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    have hp' : q∈pad.take 1 → q∈pad := List.mem_of_mem_take
    grind
  · have h := hxr hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    grind

theorem cuccaroSignedSquareRowClear_wires_subset (c : Wire) (xs dst pad carry : List Wire)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) :
    wires (cuccaroSignedSquareRowClear c xs dst pad carry)⊆
      (c::xs++dst++pad++carry).toFinset := by
  rw [cuccaroSignedSquareRowClear,wires_reverse]
  exact cuccaroSignedSquareRow_wires_subset c xs dst pad carry hd hp


theorem cuccaroSignedSquareRows_wires_subset (xs dst pad carry : List Wire)
    (hd : dst.length=2*xs.length) (hp : xs.length≤1 ∨ 1≤pad.length)
    :
    wires (cuccaroSignedSquareRows xs dst pad carry)⊆(xs++dst++pad++carry).toFinset ∧
      wires (cuccaroSignedSquareRowsClear xs dst pad carry)⊆
        (xs++dst++pad++carry).toFinset := by
  induction xs generalizing dst with
  | nil => simp [cuccaroSignedSquareRows,cuccaroSignedSquareRowsClear,wires]
  | cons c xs ih =>
    cases xs with
    | nil => simp [cuccaroSignedSquareRows,cuccaroSignedSquareRowsClear,wires]
    | cons d tail =>
      simp only [List.length_cons] at hd hp
      let rest := d::tail
      let row := (dst.drop 1).take (rest.length+1)
      let dst2 := dst.drop 2
      have hpad : 1≤pad.length := by rcases hp with hp|hp <;> omega
      have rowLen : row.length=rest.length+1 := by
        apply List.length_take_of_le
        dsimp [row,rest]
        simp
        omega
      have dst2Len : dst2.length=2*rest.length := by
        dsimp [dst2,rest]
        simp
        omega
      have hr := cuccaroSignedSquareRow_wires_subset c rest row pad carry rowLen hpad
      have hrc := cuccaroSignedSquareRowClear_wires_subset c rest row pad carry rowLen hpad
      have hi := ih dst2 dst2Len (Or.inr hpad)
      have rowMem (q : Wire) (hq : q∈row) : q∈dst :=
        List.mem_of_mem_drop (List.mem_of_mem_take hq)
      have dst2Mem (q : Wire) (hq : q∈dst2) : q∈dst := List.mem_of_mem_drop hq
      constructor
      · intro q hq
        simp only [cuccaroSignedSquareRows,wires_append,Finset.mem_union] at hq
        rcases hq with hq|hq
        · have h := hr hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := hi.1 hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
      · intro q hq
        simp only [cuccaroSignedSquareRowsClear,wires_append,Finset.mem_union] at hq
        rcases hq with hq|hq
        · have h := hi.2 hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := hrc hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind

theorem cuccaroSignedTriangularSquare_wires_subset (cin : Wire)
    (xs dst pad mask carry : List Wire) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hm : xs.length≤mask.length) :
    wires (cuccaroSignedTriangularSquare xs dst pad mask carry cin)⊆
        (cin::xs++dst++pad++mask++carry).toFinset ∧
      wires (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin)⊆
        (cin::xs++dst++pad++mask++carry).toFinset := by
  have hr := cuccaroSignedSquareRows_wires_subset xs dst pad carry hd (Or.inr hp)
  have ht := signedSquareTop_wires_subset xs dst
  have hs := cuccaroSignedDiagSub_wires_subset cin xs dst mask carry
    (List.ne_nil_of_length_pos (by omega)) hd hm
  have forward : wires (cuccaroSignedTriangularSquare xs dst pad mask carry cin)⊆
      (cin::xs++dst++pad++mask++carry).toFinset := by
    cases xs with
    | nil => simp at hx
    | cons x tail =>
      cases tail with
      | nil => simp at hx
      | cons y ys =>
        intro q hq
        simp only [cuccaroSignedTriangularSquare,wires_append,Finset.mem_union] at hq
        rcases hq with hq|hq|hq
        · have h := hr.1 hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := ht hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := hs hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
  constructor
  · exact forward
  · rw [cuccaroSignedTriangularSquareClear,wires_reverse]
    exact forward

theorem cuccaroSignedSquareRow_counts (c : Wire) (xs dst pad carry : List Wire)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) :
    toffoliCount (cuccaroSignedSquareRow c xs dst pad carry)=2*xs.length ∧
      measurementCount (cuccaroSignedSquareRow c xs dst pad carry)=0 := by
  have hs : (xs++pad.take 1).length=dst.length := by simp [hd,hp]
  have h := cuccaroAdd_counts (xs++pad.take 1) dst c hs
  simp [cuccaroSignedSquareRow,toffoliCount_append,measurementCount_append,h.1,h.2]
  omega

theorem cuccaroSignedSquareRows_counts (xs dst pad carry : List Wire)
    (hd : dst.length=2*xs.length) (hp : xs.length≤1 ∨ 1≤pad.length) :
    (toffoliCount (cuccaroSignedSquareRows xs dst pad carry)=
        2*signedSquareRowsCount xs.length ∧
      measurementCount (cuccaroSignedSquareRows xs dst pad carry)=0) ∧
    (toffoliCount (cuccaroSignedSquareRowsClear xs dst pad carry)=
        2*signedSquareRowsCount xs.length ∧
      measurementCount (cuccaroSignedSquareRowsClear xs dst pad carry)=0) := by
  induction xs generalizing dst with
  | nil => simp [cuccaroSignedSquareRows,cuccaroSignedSquareRowsClear,
      signedSquareRowsCount,toffoliCount,measurementCount]
  | cons c xs ih =>
    cases xs with
    | nil => simp [cuccaroSignedSquareRows,cuccaroSignedSquareRowsClear,
        signedSquareRowsCount,toffoliCount,measurementCount]
    | cons d tail =>
      simp only [List.length_cons] at hd hp
      have hrow : ((dst.drop 1).take ((d::tail).length+1)).length=(d::tail).length+1 := by
        apply List.length_take_of_le
        simp
        omega
      have hnext : (dst.drop 2).length=2*(d::tail).length := by simp; omega
      have hpad : 1≤pad.length := by rcases hp with hp|hp <;> omega
      have hr := cuccaroSignedSquareRow_counts c (d::tail)
        ((dst.drop 1).take ((d::tail).length+1)) pad carry hrow hpad
      have hi := ih (dst.drop 2) hnext (Or.inr hpad)
      have hrcT := toffoliCount_reverse (cuccaroSignedSquareRow c (d::tail)
        ((dst.drop 1).take ((d::tail).length+1)) pad carry)
      have hrcM := measurementCount_reverse (cuccaroSignedSquareRow c (d::tail)
        ((dst.drop 1).take ((d::tail).length+1)) pad carry)
      constructor
      · constructor
        · rw [cuccaroSignedSquareRows,toffoliCount_append,hr.1,hi.1.1]
          simp [signedSquareRowsCount]
          omega
        · rw [cuccaroSignedSquareRows,measurementCount_append,hr.2,hi.1.2]
      · constructor
        · rw [cuccaroSignedSquareRowsClear,toffoliCount_append,hi.2.1,
            cuccaroSignedSquareRowClear,hrcT,hr.1]
          simp [signedSquareRowsCount]
          omega
        · rw [cuccaroSignedSquareRowsClear,measurementCount_append,hi.2.2,
            cuccaroSignedSquareRowClear,hrcM,hr.2]

theorem cuccaroSignedDiagSub_counts (xs dst mask carry : List Wire) (cin : Wire)
    (hd : dst.length=2*xs.length) (hm : xs.length≤mask.length) :
    toffoliCount (cuccaroSignedDiagSub xs dst mask carry cin)=2*(dst.length-1) ∧
      measurementCount (cuccaroSignedDiagSub xs dst mask carry cin)=0 := by
  have htake : (xs.take (xs.length-1)).length=(mask.take (xs.length-1)).length := by
    simp [List.length_take]
    omega
  have hsrc : (signedDiagSource xs mask).length=dst.length := by
    simp [signedDiagSource,List.length_take,Nat.min_eq_left hm]
    omega
  have hcopy := copyRegister_counts none (xs.take (xs.length-1))
    (mask.take (xs.length-1)) htake
  have ha := cuccaroSub_counts (signedDiagSource xs mask) dst cin hsrc
  simp [cuccaroSignedDiagSub,signedDiagLoad,signedDiagUnload,
    toffoliCount_append,measurementCount_append,hcopy.1,hcopy.2,ha.1,ha.2]

theorem cuccaroSignedTriangularSquare_counts (xs dst pad mask carry : List Wire)
    (cin : Wire) (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length) :
    (toffoliCount (cuccaroSignedTriangularSquare xs dst pad mask carry cin)=
        2*signedSquareRowsCount xs.length+2*(dst.length-1) ∧
      measurementCount (cuccaroSignedTriangularSquare xs dst pad mask carry cin)=0) ∧
    (toffoliCount (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin)=
        2*signedSquareRowsCount xs.length+2*(dst.length-1) ∧
      measurementCount (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin)=0) := by
  have hr := cuccaroSignedSquareRows_counts xs dst pad carry hd (Or.inr hp)
  have hg := cuccaroSignedDiagSub_counts xs dst mask carry cin hd hm
  have hfT := toffoliCount_reverse (cuccaroSignedTriangularSquare xs dst pad mask carry cin)
  have hfM := measurementCount_reverse (cuccaroSignedTriangularSquare xs dst pad mask carry cin)
  cases xs with
  | nil => simp at hx
  | cons x tail =>
    cases tail with
    | nil => simp at hx
    | cons y ys =>
      have forward : toffoliCount
          (cuccaroSignedTriangularSquare (x::y::ys) dst pad mask carry cin)=
            2*signedSquareRowsCount (x::y::ys).length+2*(dst.length-1) ∧
          measurementCount
            (cuccaroSignedTriangularSquare (x::y::ys) dst pad mask carry cin)=0 := by
        simp [cuccaroSignedTriangularSquare,toffoliCount_append,measurementCount_append,
          hr.1.1,hr.1.2,hg.1,hg.2]
      constructor
      · exact forward
      · rw [cuccaroSignedTriangularSquareClear,hfT,hfM]
        exact forward

theorem cuccaroSignedTriangularSquare_counts_128 (xs dst pad mask carry : List Wire)
    (cin : Wire) (hx : xs.length=128) (hd : dst.length=256)
    (hp : 1≤pad.length) (hm : 128≤mask.length) :
    (toffoliCount (cuccaroSignedTriangularSquare xs dst pad mask carry cin)=16766 ∧
      measurementCount (cuccaroSignedTriangularSquare xs dst pad mask carry cin)=0) ∧
    (toffoliCount (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin)=16766 ∧
      measurementCount (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin)=0) := by
  have h := cuccaroSignedTriangularSquare_counts xs dst pad mask carry cin
    (by omega) (by omega) hp (by omega)
  have hc := signedSquareRowsCount_closed 128
  simp only [hx,hd] at h
  omega

theorem cuccaroSignedTriangularSquare_counts_129 (xs dst pad mask carry : List Wire)
    (cin : Wire) (hx : xs.length=129) (hd : dst.length=258)
    (hp : 1≤pad.length) (hm : 129≤mask.length) :
    (toffoliCount (cuccaroSignedTriangularSquare xs dst pad mask carry cin)=17026 ∧
      measurementCount (cuccaroSignedTriangularSquare xs dst pad mask carry cin)=0) ∧
    (toffoliCount (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin)=17026 ∧
      measurementCount (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin)=0) := by
  have h := cuccaroSignedTriangularSquare_counts xs dst pad mask carry cin
    (by omega) (by omega) hp (by omega)
  have hc := signedSquareRowsCount_closed 129
  simp only [hx,hd] at h
  omega


end ECDSAAdd.Arithmetic
