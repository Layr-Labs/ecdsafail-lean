import ECDSAAdd.Arithmetic.KaratsubaSquare
import ECDSAAdd.Arithmetic.TriangularSquarePhysical

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem karatsubaSquares_physical (L : KaratsubaSquareLayout) (hn : L.wires.Nodup) :
    GatePhysical (karatsubaSquare L) ∧ GatePhysical (karatsubaSquareClear L) := by
  have nd_lo : (L.cin::(L.low++L.a++L.pad++L.mask++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have p1 := (List.take_sublist 1 L.pad).count_le w
    have p126 := (List.take_sublist 126 L.pad).count_le w
    have c128 := (List.take_sublist 128 L.carry).count_le w
    have s128 := (List.take_sublist 128 L.sum).count_le w
    have z256 := (List.take_sublist 256 L.z).count_le w
    have zd256 := (List.drop_sublist 256 L.z).count_le w
    have zd128 := (List.drop_sublist 128 L.z).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at h ⊢
    omega
  have lo := triangularSquares_physical L.low L.a L.pad L.mask L.carry L.cin nd_lo
  have nd_hi : (L.cin::(L.high++L.d++L.pad++L.mask++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have p1 := (List.take_sublist 1 L.pad).count_le w
    have p126 := (List.take_sublist 126 L.pad).count_le w
    have c128 := (List.take_sublist 128 L.carry).count_le w
    have s128 := (List.take_sublist 128 L.sum).count_le w
    have z256 := (List.take_sublist 256 L.z).count_le w
    have zd256 := (List.drop_sublist 256 L.z).count_le w
    have zd128 := (List.drop_sublist 128 L.z).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at h ⊢
    omega
  have hi := triangularSquares_physical L.high L.d L.pad L.mask L.carry L.cin nd_hi
  have nd_su : (L.cin::(L.sum++L.c++L.pad++L.mask++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have p1 := (List.take_sublist 1 L.pad).count_le w
    have p126 := (List.take_sublist 126 L.pad).count_le w
    have c128 := (List.take_sublist 128 L.carry).count_le w
    have s128 := (List.take_sublist 128 L.sum).count_le w
    have z256 := (List.take_sublist 256 L.z).count_le w
    have zd256 := (List.drop_sublist 256 L.z).count_le w
    have zd128 := (List.drop_sublist 128 L.z).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at h ⊢
    omega
  have su := triangularSquares_physical L.sum L.c L.pad L.mask L.carry L.cin nd_su
  have nd_prep : (L.cin::((L.high++L.pad.take 1)++L.sum++(L.carry.take 128))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have p1 := (List.take_sublist 1 L.pad).count_le w
    have p126 := (List.take_sublist 126 L.pad).count_le w
    have c128 := (List.take_sublist 128 L.carry).count_le w
    have s128 := (List.take_sublist 128 L.sum).count_le w
    have z256 := (List.take_sublist 256 L.z).count_le w
    have zd256 := (List.drop_sublist 256 L.z).count_le w
    have zd128 := (List.drop_sublist 128 L.z).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at h ⊢
    omega
  have prep_add := addInPlace_physical (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin nd_prep
  have prep_sub := subInPlace_physical (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin nd_prep
  have nd_cross : (L.cin::((L.c++L.pad.take 126)++(L.z.drop 128)++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have p1 := (List.take_sublist 1 L.pad).count_le w
    have p126 := (List.take_sublist 126 L.pad).count_le w
    have c128 := (List.take_sublist 128 L.carry).count_le w
    have s128 := (List.take_sublist 128 L.sum).count_le w
    have z256 := (List.take_sublist 256 L.z).count_le w
    have zd256 := (List.drop_sublist 256 L.z).count_le w
    have zd128 := (List.drop_sublist 128 L.z).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at h ⊢
    omega
  have cross_add := addInPlace_physical (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin nd_cross
  have cross_sub := subInPlace_physical (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin nd_cross
  have nd_a : (L.cin::((L.a++L.pad)++(L.z.drop 128)++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have p1 := (List.take_sublist 1 L.pad).count_le w
    have p126 := (List.take_sublist 126 L.pad).count_le w
    have c128 := (List.take_sublist 128 L.carry).count_le w
    have s128 := (List.take_sublist 128 L.sum).count_le w
    have z256 := (List.take_sublist 256 L.z).count_le w
    have zd256 := (List.drop_sublist 256 L.z).count_le w
    have zd128 := (List.drop_sublist 128 L.z).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at h ⊢
    omega
  have a_add := addInPlace_physical (L.a++L.pad) (L.z.drop 128) L.carry L.cin nd_a
  have a_sub := subInPlace_physical (L.a++L.pad) (L.z.drop 128) L.carry L.cin nd_a
  have nd_d : (L.cin::((L.d++L.pad)++(L.z.drop 128)++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have p1 := (List.take_sublist 1 L.pad).count_le w
    have p126 := (List.take_sublist 126 L.pad).count_le w
    have c128 := (List.take_sublist 128 L.carry).count_le w
    have s128 := (List.take_sublist 128 L.sum).count_le w
    have z256 := (List.take_sublist 256 L.z).count_le w
    have zd256 := (List.drop_sublist 256 L.z).count_le w
    have zd128 := (List.drop_sublist 128 L.z).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at h ⊢
    omega
  have d_add := addInPlace_physical (L.d++L.pad) (L.z.drop 128) L.carry L.cin nd_d
  have d_sub := subInPlace_physical (L.d++L.pad) (L.z.drop 128) L.carry L.cin nd_d
  have nd_sumcopy : (L.low++(L.sum.take 128)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have p1 := (List.take_sublist 1 L.pad).count_le w
    have p126 := (List.take_sublist 126 L.pad).count_le w
    have c128 := (List.take_sublist 128 L.carry).count_le w
    have s128 := (List.take_sublist 128 L.sum).count_le w
    have z256 := (List.take_sublist 256 L.z).count_le w
    have zd256 := (List.drop_sublist 256 L.z).count_le w
    have zd128 := (List.drop_sublist 128 L.z).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at h ⊢
    omega
  have sumcopy := copyRegister_physical none L.low (L.sum.take 128) nd_sumcopy (by simp)
  have nd_lowcopy : (L.a++(L.z.take 256)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have p1 := (List.take_sublist 1 L.pad).count_le w
    have p126 := (List.take_sublist 126 L.pad).count_le w
    have c128 := (List.take_sublist 128 L.carry).count_le w
    have s128 := (List.take_sublist 128 L.sum).count_le w
    have z256 := (List.take_sublist 256 L.z).count_le w
    have zd256 := (List.drop_sublist 256 L.z).count_le w
    have zd128 := (List.drop_sublist 128 L.z).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at h ⊢
    omega
  have lowcopy := copyRegister_physical none L.a (L.z.take 256) nd_lowcopy (by simp)
  have nd_highcopy : (L.d++(L.z.drop 256)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have p1 := (List.take_sublist 1 L.pad).count_le w
    have p126 := (List.take_sublist 126 L.pad).count_le w
    have c128 := (List.take_sublist 128 L.carry).count_le w
    have s128 := (List.take_sublist 128 L.sum).count_le w
    have z256 := (List.take_sublist 256 L.z).count_le w
    have zd256 := (List.drop_sublist 256 L.z).count_le w
    have zd128 := (List.drop_sublist 128 L.z).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at h ⊢
    omega
  have highcopy := copyRegister_physical none L.d (L.z.drop 256) nd_highcopy (by simp)
  simp only [karatsubaSquare,karatsubaSquareClear,
    KaratsubaSquareLayout.squareLow,KaratsubaSquareLayout.squareHigh,
    KaratsubaSquareLayout.squareSum,KaratsubaSquareLayout.clearLow,
    KaratsubaSquareLayout.clearHigh,KaratsubaSquareLayout.clearSquareSum,
    KaratsubaSquareLayout.prepareSum,KaratsubaSquareLayout.clearSum,
    KaratsubaSquareLayout.copySquares,KaratsubaSquareLayout.combine,
    KaratsubaSquareLayout.uncombine,gatePhysical_append]
  tauto

end ECDSAAdd.Arithmetic
