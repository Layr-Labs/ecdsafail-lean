import ECDSAAdd.Arithmetic.SignedTriangularSquareResources
import ECDSAAdd.Arithmetic.SquareSubResources

namespace ECDSAAdd.Arithmetic

namespace KaratsubaSquareLayout

def signedSquareLow (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquare L.low L.a L.pad L.mask L.carry L.cin
def signedClearLow (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquareClear L.low L.a L.pad L.mask L.carry L.cin
def signedSquareHigh (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquare L.high L.d L.pad L.mask L.carry L.cin
def signedClearHigh (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquareClear L.high L.d L.pad L.mask L.carry L.cin
def signedSquareSum (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquare L.sum L.c L.pad L.mask L.carry L.cin
def signedClearSquareSum (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquareClear L.sum L.c L.pad L.mask L.carry L.cin

end KaratsubaSquareLayout

/-- Drop-in gate-stream candidate: same Karatsuba schedule and exact reduction,
with every triangular leaf replaced by the exact signed-row producer. -/
def signedKaratsubaSquare (L : KaratsubaSquareLayout) : Program :=
  L.signedSquareLow ++ L.signedSquareHigh ++ L.prepareSum ++ L.signedSquareSum ++ L.clearSum ++
  L.copySquares ++ L.combine ++ L.prepareSum ++ L.signedClearSquareSum ++ L.clearSum

def signedKaratsubaSquareClear (L : KaratsubaSquareLayout) : Program :=
  L.prepareSum ++ L.signedSquareSum ++ L.clearSum ++ L.uncombine ++ L.copySquares ++
  L.prepareSum ++ L.signedClearSquareSum ++ L.clearSum ++ L.signedClearHigh ++ L.signedClearLow

theorem signedKaratsubaSquare_counts (L : KaratsubaSquareLayout) (h : L.Valid) :
    (toffoliCount (signedKaratsubaSquare L)=35453 ∧
      measurementCount (signedKaratsubaSquare L)=35453) ∧
    (toffoliCount (signedKaratsubaSquareClear L)=35453 ∧
      measurementCount (signedKaratsubaSquareClear L)=35453) := by
  have lo := signedTriangularSquare_counts_128 L.low L.a L.pad L.mask L.carry L.cin
    h.low_length h.a_length (by simp [h.pad_length]) (by simp [h.mask_length])
    (by simp [h.carry_length])
  have hi := signedTriangularSquare_counts_128 L.high L.d L.pad L.mask L.carry L.cin
    h.high_length h.d_length (by simp [h.pad_length]) (by simp [h.mask_length])
    (by simp [h.carry_length])
  have su := signedTriangularSquare_counts_129 L.sum L.c L.pad L.mask L.carry L.cin
    h.sum_length h.c_length (by simp [h.pad_length]) (by simp [h.mask_length])
    (by simp [h.carry_length])
  obtain ⟨sp,sc⟩ := L.sum_counts h
  obtain ⟨comb,uncomb⟩ := L.combine_counts h
  have cp := L.copySquares_counts h
  simp [signedKaratsubaSquare,signedKaratsubaSquareClear,
    KaratsubaSquareLayout.signedSquareLow,KaratsubaSquareLayout.signedClearLow,
    KaratsubaSquareLayout.signedSquareHigh,KaratsubaSquareLayout.signedClearHigh,
    KaratsubaSquareLayout.signedSquareSum,KaratsubaSquareLayout.signedClearSquareSum,
    toffoliCount_append,measurementCount_append,lo.1.1,lo.1.2,lo.2.1,lo.2.2,
    hi.1.1,hi.1.2,hi.2.1,hi.2.2,su.1.1,su.1.2,su.2.1,su.2.2,
    sp.1,sp.2,sc.1,sc.2,comb.1,comb.2,uncomb.1,uncomb.2,cp.1,cp.2]

/-- Complete exact-arithmetic square-subtract candidate.  Functional promotion
waits for the signed-leaf correctness theorem and the full point proof. -/
def signedSquareSub (L : SquareSubLayout) : Program :=
  signedKaratsubaSquare L.integer ++ squareReduce L.reduction ++
  modSubInPlace L.output SquareReduction.p ++ squareReduceClear L.reduction ++
  signedKaratsubaSquareClear L.integer

theorem signedSquareSub_counts (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    toffoliCount (signedSquareSub L)=81589 ∧
      measurementCount (signedSquareSub L)=81589 := by
  have hk := signedKaratsubaSquare_counts L.integer (L.integer_valid hw hn)
  have hr := squareReduce_counts L.reduction (L.reduction_widths hw)
  have ho := modSubInPlace_resources L.output 256 SquareReduction.p (L.output_widths hw)
    (L.output_nodup hn) (by omega)
  simp [signedSquareSub,toffoliCount_append,measurementCount_append,
    hk.1.1,hk.1.2,hk.2.1,hk.2.2,hr.1.1,hr.1.2,hr.2.1,hr.2.2,ho.1,ho.2.1]

/-- With the existing 256-bit controlled source load/unload around the square,
the complete stage prices at 82,101 Toffolis. -/
theorem signedPointSquare_projected_count : 512+81589=82101 := by norm_num

end ECDSAAdd.Arithmetic
