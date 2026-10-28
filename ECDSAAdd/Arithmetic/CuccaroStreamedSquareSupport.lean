import ECDSAAdd.Arithmetic.CuccaroStreamedSquareSpec
import ECDSAAdd.Arithmetic.CuccaroGateSupport

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

def Certified (L : CuccaroStreamedSquareWideLayout) (p : Program) : Prop :=
  ProperProgram p ∧ ECDSAAdd.wires p⊆L.wires.toFinset

theorem Certified.append {L : CuccaroStreamedSquareWideLayout} {a b : Program}
    (ha : L.Certified a) (hb : L.Certified b) : L.Certified (a++b) := by
  exact ⟨properProgram_append a b |>.mpr ⟨ha.1,hb.1⟩,
    by simpa only [wires_append,Finset.union_subset_iff] using And.intro ha.2 hb.2⟩

theorem Certified.reverse {L : CuccaroStreamedSquareWideLayout} {a : Program}
    (ha : L.Certified a) : L.Certified a.reverse := by
  exact ⟨properProgram_reverse a ha.1,by simpa only [wires_reverse] using ha.2⟩

theorem source_certified (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (src : List Wire) (hv : L.SourceView src) :
    L.Certified (L.addSource src) ∧ L.Certified (L.subSource src) := by
  have nd := L.source_nodup hn src hv
  have proper := cuccaroNormalizedMod_unitary (L.source src)
    SquareReduction.c SquareReduction.p nd
  have support := cuccaroNormalizedMod_wires_subset (L.source src) 256
    SquareReduction.c SquareReduction.p (L.source_widths hw src hv.length)
  have srcMem (q : Wire) (hq : q∈src) : q∈L.core.product ∨ q∈L.foldPad := by
    by_contra h
    simp only [not_or] at h
    have hs := hv.count_le q
    have hc := List.count_pos_iff.mpr hq
    rw [List.count_eq_zero.mpr h.1,List.count_eq_zero.mpr h.2] at hs
    omega
  have embed : (L.source src).wires.toFinset⊆L.wires.toFinset := by
    intro q hq
    simp only [source,CuccaroNormalizedModLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    have hs : q∈src → q∈L.core.product ∨ q∈L.core.pad ∨ q∈L.overflowPad := by
      intro h
      have m := srcMem q h
      simpa only [foldPad,List.mem_append,or_assoc] using m
    tauto
  exact ⟨⟨proper.1,support.1.trans embed⟩,⟨proper.2,support.2.trans embed⟩⟩

theorem producer_certified (L : CuccaroStreamedSquareWideLayout)
    (hn : L.wires.Nodup) (src dst mask : List Wire) (n : Nat)
    (hsrc : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hdst : ∀q,dst.count q≤L.core.product.count q)
    (hmask : ∀q,mask.count q≤L.core.work.count q)
    (hs : src.length=n) (hd : dst.length=2*n)
    (hm : n≤mask.length) (hp : 1≤L.core.pad.length) (hn2 : 2≤n) :
    L.Certified (cuccaroSignedTriangularSquare src dst L.core.pad mask [] L.core.cin) ∧
    L.Certified (cuccaroSignedTriangularSquareClear src dst L.core.pad mask [] L.core.cin) := by
  have nd : (L.core.cin::src++dst++L.core.pad++mask++[]).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have h1 := hsrc q
    have h2 := hdst q
    have h3 := hmask q
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
      List.count_cons,List.count_nil] at h h1 ⊢
    omega
  have proper := cuccaroSignedTriangularSquare_proper L.core.cin
    src dst L.core.pad mask [] nd
  have supp := cuccaroSignedTriangularSquare_wires_subset L.core.cin
    src dst L.core.pad mask [] (by omega) (by omega) hp (by omega)
  have embed : (L.core.cin::src++dst++L.core.pad++mask++[]).toFinset⊆L.wires.toFinset := by
    intro q hq
    have pos := List.count_pos_iff.mpr (List.mem_toFinset.mp hq)
    have h1 := hsrc q
    have h2 := hdst q
    have h3 := hmask q
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
      List.count_cons,List.count_nil] at pos h1 ⊢
    omega
  exact ⟨⟨proper,supp.1.trans embed⟩,
    ⟨properProgram_reverse _ proper,supp.2.trans embed⟩⟩

theorem square128_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (src : List Wire)
    (hs : src.length=128) (hsrc : ∀q,src.count q≤L.core.y.count q) :
    L.Certified (L.core.square128 src) ∧ L.Certified (L.core.square128Clear src) := by
  apply L.producer_certified hn src (L.core.product.take 256) (L.core.work.take 128) 128
    (by intro q; have h:=hsrc q; simp only [List.count_append]; omega)
    (by intro q; exact (List.take_sublist 256 L.core.product).count_le q)
    (by intro q; exact (List.take_sublist 128 L.core.work).count_le q) hs
    (by simp [hw.core.product]) (by simp [hw.core.work])
    (by rw [hw.core.pad]; omega) (by omega)

theorem square129_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) :
    L.Certified L.core.square129 ∧ L.Certified L.core.square129Clear := by
  apply L.producer_certified hn L.core.sum L.core.product (L.core.work.take 129) 129
    (by
      intro q
      have h1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
      have h2 := (List.drop_sublist 128 L.core.y).count_le q
      simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
        List.count_append] at h1 ⊢
      omega)
    (by intro q; exact le_rfl)
    (by intro q; exact (List.take_sublist 129 L.core.work).count_le q)
    (L.core.sum_length hw.core) (by rw [hw.core.product])
    (by simp [hw.core.work]) (by rw [hw.core.pad]; omega) (by omega)

theorem cMinusOne_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (src : List Wire)
    (hsrc : ∀q,src.count q≤L.core.product.count q)
    (hs2 : 2≤src.length) (hs : src.length+32≤256) :
    L.Certified (L.addCMinusOne src) ∧ L.Certified (L.subCMinusOne src) := by
  have s4 := L.source_certified hw hn (L.shifted src 4)
    (L.shifted_view hw src hsrc 4 hs2 (by omega))
  have s6 := L.source_certified hw hn (L.shifted src 6)
    (L.shifted_view hw src hsrc 6 hs2 (by omega))
  have s10 := L.source_certified hw hn (L.shifted src 10)
    (L.shifted_view hw src hsrc 10 hs2 (by omega))
  have s32 := L.source_certified hw hn (L.shifted src 32)
    (L.shifted_view hw src hsrc 32 hs2 hs)
  exact ⟨((s4.1.append s6.2).append s10.1).append s32.1,
    ((s4.2.append s6.1).append s10.2).append s32.2⟩

theorem rotate128_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (overhang : Bool) :
    L.Certified (L.addRotate128 overhang) ∧ L.Certified (L.subRotate128 overhang) := by
  have rot := L.source_certified hw hn L.rotated128 (L.rotated128_view hw)
  have terms := L.cMinusOne_certified hw hn (L.core.product.drop 128)
    (L.productDrop_count 128) (by simp [hw.core.product]) (by simp [hw.core.product])
  have tail := L.source_certified hw hn (L.shifted (L.core.product.drop 256) 128)
    (L.shiftedProductDrop_view hw 256 128 (by simp [hw.core.product])
      (by simp [hw.core.product]))
  have nil : L.Certified [] := by simp [Certified,ProperProgram,ECDSAAdd.wires]
  cases overhang
  · exact ⟨(rot.1.append terms.1).append nil,(rot.2.append terms.2).append nil⟩
  · exact ⟨(rot.1.append terms.1).append tail.1,(rot.2.append terms.2).append tail.2⟩

theorem shiftFull_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (j : Nat)
    (hj2 : 2≤j) (hj : j≤224) :
    L.Certified (L.addShiftFull (L.core.product.take 256) j) ∧
    L.Certified (L.subShiftFull (L.core.product.take 256) j) := by
  have rot := L.source_certified hw hn (rotateFull (L.core.product.take 256) j)
    (L.rotateFull_view hw j (by omega))
  have len : ((L.core.product.take 256).drop (256-j)).length=j := by
    simp [hw.core.product]
    omega
  have terms := L.cMinusOne_certified hw hn
    ((L.core.product.take 256).drop (256-j)) (L.productTakeDrop_count (256-j))
    (by rw [len]; exact hj2) (by rw [len]; omega)
  have jnz : j≠0 := by omega
  simpa only [addShiftFull,subShiftFull,jnz,if_false] using
    And.intro (rot.1.append terms.1) (rot.2.append terms.2)

theorem timesC_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) :
    L.Certified (L.subTimesC (L.core.product.take 256)) := by
  have base := L.source_certified hw hn (L.core.product.take 256)
    (L.productTake256_view hw)
  have s4 := L.shiftFull_certified hw hn 4 (by omega) (by omega)
  have s6 := L.shiftFull_certified hw hn 6 (by omega) (by omega)
  have s10 := L.shiftFull_certified hw hn 10 (by omega) (by omega)
  have s32 := L.shiftFull_certified hw hn 32 (by omega) (by omega)
  simpa only [subTimesC,subShiftFull,if_true] using
    (((base.2.append s4.2).append s6.1).append s10.2).append s32.2

theorem sum_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) :
    L.Certified L.core.prepareSum ∧ L.Certified L.core.clearSum := by
  have bitMem : L.core.pad.getD 0 0∈L.core.pad := by
    have h : 0<L.core.pad.length := by rw [hw.core.pad]; omega
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  have hiEq : L.core.high=L.core.y.drop 128 := by
    simp [CuccaroStreamedSquareLayout.high,hw.core.y]
  have bounds (q : Wire) :
      (L.core.cin::(L.core.low++[L.core.pad.getD 0 0])++L.core.sum).count q≤
        L.wires.count q := by
    have sp := congrArg (List.count q) (List.take_append_drop 128 L.core.y)
    have pb := (List.singleton_sublist.mpr bitMem).count_le q
    simp only [List.count_append] at sp
    simp only [wires,CuccaroStreamedSquareLayout.wires,
      CuccaroStreamedSquareLayout.low,CuccaroStreamedSquareLayout.sum,hiEq,
      List.count_append,List.count_cons,List.count_nil] at pb ⊢
    omega
  have nd : (L.core.cin::(L.core.low++[L.core.pad.getD 0 0])++L.core.sum).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    exact (bounds q).trans (List.nodup_iff_count.mp hn q)
  have producer : L.Certified L.core.prepareSum := by
    refine ⟨cuccaroAdd_proper _ _ _ nd,?_⟩
    intro q hq
    have mem := List.mem_toFinset.mp (cuccaroAdd_wires_subset
      (L.core.low++[L.core.pad.getD 0 0]) L.core.sum L.core.cin hq)
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp
      (lt_of_lt_of_le (List.count_pos_iff.mpr mem) (bounds q)))
  exact ⟨producer,producer.reverse⟩

theorem program_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : L.Certified L.program := by
  have low := L.square128_certified hw hn L.core.low (L.core.low_length hw.core)
    (by intro q; exact (List.take_sublist 128 L.core.y).count_le q)
  have high := L.square128_certified hw hn L.core.high (L.core.high_length hw.core)
    (by
      intro q
      exact ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
        ((List.drop_sublist 128 L.core.y).count_le q))
  have sum := L.square129_certified hw hn
  have prepare := L.sum_certified hw hn
  have rotate0 := L.rotate128_certified hw hn false
  have rotate1 := L.rotate128_certified hw hn true
  have sub := L.source_certified hw hn (L.core.product.take 256)
    (L.productTake256_view hw)
  have times := L.timesC_certified hw hn
  have a : L.Certified L.branchA :=
    (((low.1.append sub.2).append rotate0.1).append low.2)
  have b : L.Certified L.branchB :=
    (high.1.append rotate0.1).append (times.append high.2)
  have c : L.Certified L.branchC :=
    (prepare.1.append ((sum.1.append rotate1.2).append sum.2)).append prepare.2
  exact (a.append b).append c

theorem program_static_support (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : qubitCount L.program≤1287 := by
  have h := L.program_certified hw hn
  rw [qubitCount]
  calc
    _ ≤ L.wires.toFinset.card := Finset.card_le_card h.2
    _ = 1287 := by rw [List.toFinset_card_of_nodup hn,L.wires_length hw]

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
