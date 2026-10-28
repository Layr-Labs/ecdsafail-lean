import ECDSAAdd.Arithmetic.KaratsubaSquare

namespace ECDSAAdd.Arithmetic

namespace KaratsubaSquareLayout

theorem sum_counts (L : KaratsubaSquareLayout) (h : L.Valid) :
    (toffoliCount L.prepareSum=128 ∧ measurementCount L.prepareSum=128) ∧
    (toffoliCount L.clearSum=128 ∧ measurementCount L.clearSum=128) := by
  have cp := copyRegister_counts none L.low (L.sum.take 128) (by simp [h.low_length,h.sum_length])
  have ap := addInPlace_counts (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin
    (by simp [h.high_length,h.pad_length,h.sum_length]) (by simp [h.carry_length,h.sum_length])
  have sp := subInPlace_counts (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin
    (by simp [h.high_length,h.pad_length,h.sum_length]) (by simp [h.carry_length,h.sum_length])
  simp [prepareSum,clearSum,cp.1,cp.2,ap.1,ap.2,sp.1,sp.2,h.sum_length]

theorem copySquares_counts (L : KaratsubaSquareLayout) (h : L.Valid) :
    toffoliCount L.copySquares=0 ∧ measurementCount L.copySquares=0 := by
  have a := copyRegister_counts none L.a (L.z.take 256) (by simp [h.a_length,h.z_length])
  have d := copyRegister_counts none L.d (L.z.drop 256) (by simp [h.d_length,h.z_length])
  simp [copySquares,a.1,a.2,d.1,d.2]

theorem combine_counts (L : KaratsubaSquareLayout) (h : L.Valid) :
    (toffoliCount L.combine=1149 ∧ measurementCount L.combine=1149) ∧
    (toffoliCount L.uncombine=1149 ∧ measurementCount L.uncombine=1149) := by
  have ac := addInPlace_counts (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin
    (by simp [h.c_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  have sc := subInPlace_counts (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin
    (by simp [h.c_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  have aa := addInPlace_counts (L.a++L.pad) (L.z.drop 128) L.carry L.cin
    (by simp [h.a_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  have sa := subInPlace_counts (L.a++L.pad) (L.z.drop 128) L.carry L.cin
    (by simp [h.a_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  have ad := addInPlace_counts (L.d++L.pad) (L.z.drop 128) L.carry L.cin
    (by simp [h.d_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  have sd := subInPlace_counts (L.d++L.pad) (L.z.drop 128) L.carry L.cin
    (by simp [h.d_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  simp [combine,uncombine,ac.1,ac.2,sc.1,sc.2,aa.1,aa.2,sa.1,sa.2,ad.1,ad.2,sd.1,sd.2,h.z_length]

theorem squares_counts (L : KaratsubaSquareLayout) (h : L.Valid) :
    (toffoliCount L.squareLow=32385 ∧ measurementCount L.squareLow=32385) ∧
    (toffoliCount L.clearLow=32385 ∧ measurementCount L.clearLow=32385) ∧
    (toffoliCount L.squareHigh=32385 ∧ measurementCount L.squareHigh=32385) ∧
    (toffoliCount L.clearHigh=32385 ∧ measurementCount L.clearHigh=32385) ∧
    (toffoliCount L.squareSum=32896 ∧ measurementCount L.squareSum=32896) ∧
    (toffoliCount L.clearSquareSum=32896 ∧ measurementCount L.clearSquareSum=32896) := by
  have a := triangularSquare_counts L.low L.a L.pad L.mask L.carry L.cin
    (by simp [h.a_length,h.low_length]) (by simp [h.low_length,h.pad_length])
    (by simp [h.low_length,h.mask_length]) (by simp [h.low_length,h.carry_length])
  have d := triangularSquare_counts L.high L.d L.pad L.mask L.carry L.cin
    (by simp [h.d_length,h.high_length]) (by simp [h.high_length,h.pad_length])
    (by simp [h.high_length,h.mask_length]) (by simp [h.high_length,h.carry_length])
  have c := triangularSquare_counts L.sum L.c L.pad L.mask L.carry L.cin
    (by simp [h.c_length,h.sum_length]) (by simp [h.sum_length,h.pad_length])
    (by simp [h.sum_length,h.mask_length]) (by simp [h.sum_length,h.carry_length])
  simpa [squareLow,clearLow,squareHigh,clearHigh,squareSum,clearSquareSum,h.low_length,h.high_length,h.sum_length]
    using And.intro a.1 (And.intro a.2 (And.intro d.1 (And.intro d.2 c)))

private theorem within (L : KaratsubaSquareLayout) (r : List Wire)
    (hc : ∀ w,r.count w≤L.wires.count w) : r.toFinset⊆L.wires.toFinset := by
  intro w hw
  apply List.mem_toFinset.mpr
  apply List.count_pos_iff.mp
  have hp := List.count_pos_iff.mpr (List.mem_toFinset.mp hw)
  exact lt_of_lt_of_le hp (hc w)

private theorem copy_within (L : KaratsubaSquareLayout) (src dst : List Wire)
    (hl : src.length=dst.length) (hs : (src++dst).toFinset⊆L.wires.toFinset) :
    ECDSAAdd.wires (copyRegister none src dst)⊆L.wires.toFinset := by
  rw [copyRegister_wires none src dst hl]
  split
  · exact Finset.empty_subset _
  · simpa using hs

theorem squareLow_wires_subset (L : KaratsubaSquareLayout) (h : L.Valid) :
    ECDSAAdd.wires L.squareLow⊆L.wires.toFinset ∧
    ECDSAAdd.wires L.clearLow⊆L.wires.toFinset := by
  have hw := triangularSquare_wires L.low L.a L.pad L.mask L.carry L.cin
    (by simp [h.a_length,h.low_length]) (by simp [h.low_length,h.pad_length])
    (by simp [h.low_length,h.mask_length]) (by simp [h.low_length,h.carry_length])
  have sub := triangularSquareWires_subset L.low L.a L.pad L.mask L.carry L.cin
  have own : (L.cin::L.low++L.a++L.pad++L.mask++L.carry).toFinset⊆L.wires.toFinset := by
    apply within; intro w
    simp only [wires,List.count_cons,List.count_append]
    omega
  exact ⟨hw.1 ▸ sub.trans own,hw.2 ▸ sub.trans own⟩

theorem squareHigh_wires_subset (L : KaratsubaSquareLayout) (h : L.Valid) :
    ECDSAAdd.wires L.squareHigh⊆L.wires.toFinset ∧
    ECDSAAdd.wires L.clearHigh⊆L.wires.toFinset := by
  have hw := triangularSquare_wires L.high L.d L.pad L.mask L.carry L.cin
    (by simp [h.d_length,h.high_length]) (by simp [h.high_length,h.pad_length])
    (by simp [h.high_length,h.mask_length]) (by simp [h.high_length,h.carry_length])
  have sub := triangularSquareWires_subset L.high L.d L.pad L.mask L.carry L.cin
  have own : (L.cin::L.high++L.d++L.pad++L.mask++L.carry).toFinset⊆L.wires.toFinset := by
    apply within; intro w
    simp only [wires,List.count_cons,List.count_append]
    omega
  exact ⟨hw.1 ▸ sub.trans own,hw.2 ▸ sub.trans own⟩

theorem squareSum_wires_subset (L : KaratsubaSquareLayout) (h : L.Valid) :
    ECDSAAdd.wires L.squareSum⊆L.wires.toFinset ∧
    ECDSAAdd.wires L.clearSquareSum⊆L.wires.toFinset := by
  have hw := triangularSquare_wires L.sum L.c L.pad L.mask L.carry L.cin
    (by simp [h.c_length,h.sum_length]) (by simp [h.sum_length,h.pad_length])
    (by simp [h.sum_length,h.mask_length]) (by simp [h.sum_length,h.carry_length])
  have sub := triangularSquareWires_subset L.sum L.c L.pad L.mask L.carry L.cin
  have own : (L.cin::L.sum++L.c++L.pad++L.mask++L.carry).toFinset⊆L.wires.toFinset := by
    apply within; intro w
    simp only [wires,List.count_cons,List.count_append]
    omega
  exact ⟨hw.1 ▸ sub.trans own,hw.2 ▸ sub.trans own⟩

theorem sum_wires_subset (L : KaratsubaSquareLayout) (h : L.Valid) :
    ECDSAAdd.wires L.prepareSum⊆L.wires.toFinset ∧
    ECDSAAdd.wires L.clearSum⊆L.wires.toFinset := by
  have cp := copy_within L L.low (L.sum.take 128) (by simp [h.low_length,h.sum_length]) (by
    apply within; intro w
    have ht := (List.take_sublist 128 L.sum).count_le w
    simp only [wires,List.count_cons,List.count_append]; omega)
  have asub : (L.cin::(L.high++L.pad.take 1)++L.sum++L.carry.take 128).toFinset⊆L.wires.toFinset := by
    apply within; intro w
    have hp := (List.take_sublist 1 L.pad).count_le w
    have hc := (List.take_sublist 128 L.carry).count_le w
    simp only [wires,List.count_cons,List.count_append]; omega
  have ha := addInPlace_wires (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin
    (by simp [h.high_length,h.pad_length,h.sum_length]) (by simp [h.carry_length,h.sum_length])
  have hs := subInPlace_wires (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin
    (by simp [h.high_length,h.pad_length,h.sum_length]) (by simp [h.carry_length,h.sum_length])
  simp only [prepareSum,clearSum,wires_append,Finset.union_subset_iff,ha,hs]
  exact ⟨⟨cp,asub⟩,asub,cp⟩

theorem copySquares_wires_subset (L : KaratsubaSquareLayout) (h : L.Valid) :
    ECDSAAdd.wires L.copySquares⊆L.wires.toFinset := by
  have ca := copy_within L L.a (L.z.take 256) (by simp [h.a_length,h.z_length]) (by
    apply within; intro w
    have hz := (List.take_sublist 256 L.z).count_le w
    simp only [wires,List.count_cons,List.count_append]; omega)
  have cd := copy_within L L.d (L.z.drop 256) (by simp [h.d_length,h.z_length]) (by
    apply within; intro w
    have hz := (List.drop_sublist 256 L.z).count_le w
    simp only [wires,List.count_cons,List.count_append]; omega)
  simpa only [copySquares,wires_append,Finset.union_subset_iff] using And.intro ca cd

theorem combine_wires_subset (L : KaratsubaSquareLayout) (h : L.Valid) :
    ECDSAAdd.wires L.combine⊆L.wires.toFinset ∧
    ECDSAAdd.wires L.uncombine⊆L.wires.toFinset := by
  have owna : (L.cin::(L.a++L.pad)++L.z.drop 128++L.carry).toFinset⊆L.wires.toFinset := by
    apply within; intro w
    have hz := (List.drop_sublist 128 L.z).count_le w
    simp only [wires,List.count_cons,List.count_append]; omega
  have aa := addInPlace_wires (L.a++L.pad) (L.z.drop 128) L.carry L.cin
    (by simp [h.a_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  have sa := subInPlace_wires (L.a++L.pad) (L.z.drop 128) L.carry L.cin
    (by simp [h.a_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  have ownd : (L.cin::(L.d++L.pad)++L.z.drop 128++L.carry).toFinset⊆L.wires.toFinset := by
    apply within; intro w
    have hz := (List.drop_sublist 128 L.z).count_le w
    simp only [wires,List.count_cons,List.count_append]; omega
  have ad := addInPlace_wires (L.d++L.pad) (L.z.drop 128) L.carry L.cin
    (by simp [h.d_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  have sd := subInPlace_wires (L.d++L.pad) (L.z.drop 128) L.carry L.cin
    (by simp [h.d_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  have ownc : (L.cin::(L.c++L.pad.take 126)++L.z.drop 128++L.carry).toFinset⊆L.wires.toFinset := by
    apply within; intro w
    have hz := (List.drop_sublist 128 L.z).count_le w
    have hp := (List.take_sublist 126 L.pad).count_le w
    simp only [wires,List.count_cons,List.count_append]; omega
  have ac := addInPlace_wires (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin
    (by simp [h.c_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  have sc := subInPlace_wires (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin
    (by simp [h.c_length,h.pad_length,h.z_length]) (by simp [h.carry_length,h.z_length])
  simp only [combine,uncombine,wires_append,aa,sa,ad,sd,ac,sc,Finset.union_subset_iff]
  exact ⟨⟨⟨ownc,owna⟩,ownd⟩,⟨ownd,owna⟩,ownc⟩

end KaratsubaSquareLayout

/-- Exact counts for each complete compute/cleanup, including both evaluations of C. -/
theorem karatsubaSquare_counts (L : KaratsubaSquareLayout) (h : L.Valid) :
    (toffoliCount (karatsubaSquare L)=132223 ∧ measurementCount (karatsubaSquare L)=132223) ∧
    (toffoliCount (karatsubaSquareClear L)=132223 ∧ measurementCount (karatsubaSquareClear L)=132223) := by
  obtain ⟨a,ac,d,dc,c,cc⟩ := L.squares_counts h
  obtain ⟨s,sc⟩ := L.sum_counts h
  obtain ⟨comb,uncomb⟩ := L.combine_counts h
  have cp := L.copySquares_counts h
  simp [karatsubaSquare,karatsubaSquareClear,a.1,a.2,ac.1,ac.2,d.1,d.2,dc.1,dc.2,c.1,c.2,cc.1,cc.2,
    s.1,s.2,sc.1,sc.2,comb.1,comb.2,uncomb.1,uncomb.2,cp.1,cp.2]

/-- Every physical wire used by either forward program belongs to the supplied layout. -/
theorem karatsubaSquare_wires_subset (L : KaratsubaSquareLayout) (h : L.Valid) :
    wires (karatsubaSquare L)⊆L.wires.toFinset ∧
    wires (karatsubaSquareClear L)⊆L.wires.toFinset := by
  obtain ⟨a,ac⟩ := L.squareLow_wires_subset h
  obtain ⟨d,dc⟩ := L.squareHigh_wires_subset h
  obtain ⟨c,cc⟩ := L.squareSum_wires_subset h
  obtain ⟨s,sc⟩ := L.sum_wires_subset h
  obtain ⟨comb,uncomb⟩ := L.combine_wires_subset h
  have cp := L.copySquares_wires_subset h
  simp only [karatsubaSquare,karatsubaSquareClear,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a,d⟩,s⟩,c⟩,sc⟩,cp⟩,comb⟩,s⟩,cc⟩,sc⟩,
    ⟨⟨⟨⟨⟨⟨⟨⟨s,c⟩,sc⟩,uncomb⟩,cp⟩,s⟩,cc⟩,sc⟩,dc⟩,ac⟩


end ECDSAAdd.Arithmetic
