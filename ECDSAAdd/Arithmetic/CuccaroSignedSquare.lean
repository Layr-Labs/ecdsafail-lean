import ECDSAAdd.Arithmetic.CuccaroAdder
import ECDSAAdd.Arithmetic.SignedSquareLeafProof
import ECDSAAdd.Framework.GateInverse

namespace ECDSAAdd.Arithmetic

/-- Signed triangular row using a Cuccaro carry ladder inside the source word.
It needs one clean padding bit and no carry bank. -/
def cuccaroSignedSquareRow (c : Wire) (xs dst pad _carry : List Wire) : Program :=
  xorWhenFalse c (dst.take xs.length) ++
    cuccaroAdd (xs ++ pad.take 1) dst c ++
    xorWhenFalse c dst

def cuccaroSignedSquareRowClear (c : Wire) (xs dst pad carry : List Wire) : Program :=
  (cuccaroSignedSquareRow c xs dst pad carry).reverse

/-- Low-to-high signed rows, with no retained per-bit carries. -/
def cuccaroSignedSquareRows : List Wire → List Wire → List Wire → List Wire → Program
  | [], _, _, _ => []
  | _::[], _, _, _ => []
  | c::d::tail, dst, pad, carry =>
      cuccaroSignedSquareRow c (d::tail)
        ((dst.drop 1).take ((d::tail).length+1)) pad carry ++
      cuccaroSignedSquareRows (d::tail) (dst.drop 2) pad carry

def cuccaroSignedSquareRowsClear : List Wire → List Wire → List Wire → List Wire → Program
  | [], _, _, _ => []
  | _::[], _, _, _ => []
  | c::d::tail, dst, pad, carry =>
      cuccaroSignedSquareRowsClear (d::tail) (dst.drop 2) pad carry ++
      cuccaroSignedSquareRowClear c (d::tail)
        ((dst.drop 1).take ((d::tail).length+1)) pad carry

/-- Exact affine diagonal correction without a carry bank. -/
def cuccaroSignedDiagSub (xs dst mask _carry : List Wire) (cin : Wire) : Program :=
  signedDiagLoad xs mask cin ++
    (cuccaroSub (signedDiagSource xs mask) dst cin ++
      signedDiagUnload xs mask cin)

/-- Measurement-free exact signed triangular square. -/
def cuccaroSignedTriangularSquare (xs dst pad mask carry : List Wire) (cin : Wire) : Program :=
  match xs, dst with
  | [], _ => []
  | [x], z::_ => [.CX x z]
  | _::_, _ => cuccaroSignedSquareRows xs dst pad carry ++
      (signedSquareTop xs dst ++ cuccaroSignedDiagSub xs dst mask carry cin)

/-- Every instruction in the producer is self-inverse; reversing the stream
is therefore an exact cleanup with an independent (unused) record list. -/
def cuccaroSignedTriangularSquareClear (xs dst pad mask carry : List Wire) (cin : Wire) : Program :=
  (cuccaroSignedTriangularSquare xs dst pad mask carry cin).reverse

/-- Cuccaro addition framed around one target register. -/
theorem cuccaroAdd_cin_frame (cin : Wire) (src dst : List Wire)
    (hnd : (cin::src++dst).Nodup) (hs : src.length=dst.length)
    (base : BasisState) (C : Bool) (hC : base cin=C) (V : Nat) :
    Triple (SquareFrame dst base V) (cuccaroAdd src dst cin)
      (SquareFrame dst base ((V+regValue src base+C.toNat)%2^dst.length)) := by
  have dis (w : Wire) (hw : w∈cin::src) : w∉dst := by
    intro hdw
    have hn := List.nodup_iff_count.mp hnd w
    have h1 := List.count_pos_iff.mpr hw
    have h2 := List.count_pos_iff.mpr hdw
    simp only [List.count_cons,List.count_append] at hn h1
    omega
  intro s m h
  have sv : regValue src s.basis=regValue src base :=
    regValue_congr _ _ _ (fun w hw => h.2 w (dis w (by simp [hw])))
  have cv : s.basis cin=C := (h.2 cin (dis cin (by simp))).trans hC
  have runh := cuccaroAdd_correct src dst cin hnd hs s m
  refine ⟨runh.1,?_,?_⟩
  · rw [runh.2.2.2.1,sv,h.1,cv]
    congr 2
    omega
  · intro w hw
    by_cases hwi : w=cin
    · subst w
      exact runh.2.2.1.trans (h.2 cin hw)
    by_cases hws : w∈src
    · exact ((regValue_eq_iff src _ _).mp runh.2.1 w hws).trans (h.2 w hw)
    · exact (runh.2.2.2.2 w (by simp [hwi,hws,hw])).trans (h.2 w hw)

/-- Cuccaro subtraction framed around one target register. -/
theorem cuccaroSub_frame (cin : Wire) (src dst : List Wire)
    (hnd : (cin::src++dst).Nodup) (hs : src.length=dst.length)
    (base : BasisState) (hC : base cin=false) (V : Nat) :
    Triple (SquareFrame dst base V) (cuccaroSub src dst cin)
      (SquareFrame dst base
        ((V+2^dst.length-regValue src base)%2^dst.length)) := by
  have dis (w : Wire) (hw : w∈cin::src) : w∉dst := by
    intro hdw
    have hn := List.nodup_iff_count.mp hnd w
    have h1 := List.count_pos_iff.mpr hw
    have h2 := List.count_pos_iff.mpr hdw
    simp only [List.count_cons,List.count_append] at hn h1
    omega
  intro s m h
  have sv : regValue src s.basis=regValue src base :=
    regValue_congr _ _ _ (fun w hw => h.2 w (dis w (by simp [hw])))
  have cv : s.basis cin=false := (h.2 cin (dis cin (by simp))).trans hC
  have runh := cuccaroSub_correct src dst cin hnd hs s m cv
  refine ⟨runh.1,?_,?_⟩
  · rw [runh.2.2.2.1,sv,h.1]
  · intro w hw
    by_cases hwi : w=cin
    · subst w
      exact (runh.2.2.1.trans cv.symm).trans (h.2 cin hw)
    by_cases hws : w∈src
    · exact ((regValue_eq_iff src _ _).mp runh.2.1 w hws).trans (h.2 w hw)
    · exact (runh.2.2.2.2 w (by simp [hwi,hws,hw])).trans (h.2 w hw)

/-- One Cuccaro signed row has the same exact arithmetic interface as the
measured carry-bank row, while using no carry register. -/
theorem cuccaroSignedSquareRow_frame (c : Wire) (xs dst pad carry : List Wire)
    (hnd : (c::xs++dst++pad++carry).Nodup) (hd : dst.length=xs.length+1)
    (hp : 1≤pad.length)
    (base : BasisState) (C : Bool) (hC : base c=C)
    (hz : regValue (pad++carry) base=0) (A : Nat) (hA : A<2^dst.length) :
    Triple (SquareFrame dst base A) (cuccaroSignedSquareRow c xs dst pad carry)
      (SquareFrame dst base (signedRowValue C A (regValue xs base) xs.length)) := by
  let src := xs++pad.take 1
  have ndc : (c::dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ndadd : (c::src++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    have hp' := (List.take_sublist 1 pad).count_le w
    simp only [src,List.count_cons,List.count_append] at h ⊢
    omega
  have hs : src.length=dst.length := by simp [src,hd,hp]
  have srcv : regValue src base=regValue xs base := by
    have p0 : regValue (pad.take 1) base=0 := (regValue_zero _ _).mpr
      (fun w hw => (regValue_zero _ _).mp hz w (by simp [List.mem_of_mem_take hw]))
    simp [src,regValue_append,p0]
  let P := if C then A else
    (2^xs.length-1-A%2^xs.length)+2^xs.length*(A/2^xs.length)
  let B := (P+regValue src base+C.toNat)%2^dst.length
  have h1 := xorWhenFalse_prefix_frame c dst xs.length ndc (by omega) base C A hC
  have h2 := cuccaroAdd_cin_frame c src dst ndadd hs base C hC P
  have h3 := xorWhenFalse_frame c dst ndc base C B hC
  have comp := h1.seq (h2.seq h3)
  have heq : (if C then B else 2^dst.length-1-B)=
      signedRowValue C A (regValue xs base) xs.length := by
    simp only [P,B,srcv]
    cases C with
    | true => simp [signedRowValue,hd]
    | false =>
      simp only [Bool.false_eq_true,if_false,Bool.toNat_false,Nat.add_zero]
      rw [hd] at hA
      have hS : regValue xs base<2^xs.length := regValue_lt xs base
      have hm : 0<2^xs.length := Nat.two_pow_pos _
      have hA2 : A<2*(2^xs.length) := by simpa [Nat.pow_succ,Nat.mul_comm] using hA
      rw [hd]
      simp only [signedRowValue,Bool.false_eq_true,if_false]
      rw [show 2^(xs.length+1)=2*(2^xs.length) by rw [Nat.pow_succ]; omega]
      exact signed_false_row_value A (regValue xs base) (2^xs.length) hm hA2 hS
  have final := Triple.conseq (fun _ h => h) comp
    (fun _ hpost => by simpa [heq] using hpost)
  simpa [cuccaroSignedSquareRow,src,List.append_assoc] using final

end ECDSAAdd.Arithmetic
