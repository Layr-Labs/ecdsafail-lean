import ECDSAAdd.Arithmetic.CuccaroStreamedSquare
import ECDSAAdd.Arithmetic.SwapLow

set_option maxHeartbeats 8000000
set_option maxRecDepth 5000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

theorem regValue_take_mod (r : List Wire) (n : Nat) (hn : n≤r.length)
    (s : BasisState) : regValue (r.take n) s=regValue r s%2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at h
  rw [h,Nat.add_mul_mod_self_left]
  apply (Nat.mod_eq_of_lt ?_).symm
  simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s

theorem regValue_drop_div (r : List Wire) (n : Nat) (hn : n≤r.length)
    (s : BasisState) : regValue (r.drop n) s=regValue r s/2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at h
  have hl : regValue (r.take n) s<2^n := by
    simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s
  rw [h,Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),Nat.div_eq_of_lt hl,Nat.zero_add]

theorem product_take_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (s : BasisState) (P : Nat) (hP : regValue L.core.product s=P)
    (n : Nat) (hn : n≤258) :
    regValue (L.core.product.take n) s=P%2^n := by
  rw [regValue_take_mod L.core.product n (by rw [hw.core.product]; exact hn),hP]

theorem product_drop_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (s : BasisState) (P : Nat) (hP : regValue L.core.product s=P)
    (n : Nat) (hn : n≤258) :
    regValue (L.core.product.drop n) s=P/2^n := by
  rw [regValue_drop_div L.core.product n (by rw [hw.core.product]; exact hn),hP]

theorem rotated128_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (s : BasisState) (P : Nat) (hP : regValue L.core.product s=P) :
    regValue L.rotated128 s=(P/2^128)%2^128+2^128*(P%2^128) := by
  have high := L.product_drop_value hw s P hP 128 (by omega)
  have highLow := regValue_take_mod (L.core.product.drop 128) 128
    (by simp [hw.core.product]) s
  have low := L.product_take_value hw s P hP 128 (by omega)
  rw [rotated128,regValue_append,highLow,high,low]
  simp [hw.core.product]

theorem productTakeDrop_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (s : BasisState) (P : Nat) (hP : regValue L.core.product s=P)
    (j : Nat) (hj : j≤256) :
    regValue ((L.core.product.take 256).drop (256-j)) s=(P%2^256)/2^(256-j) := by
  rw [regValue_drop_div _ _ (by simp [hw.core.product]),
    L.product_take_value hw s P hP 256 (by omega)]

theorem rotateFull_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (s : BasisState) (P : Nat) (hP : regValue L.core.product s=P)
    (j : Nat) (hj : j≤256) :
    regValue (rotateFull (L.core.product.take 256) j) s=
      (P%2^256)/2^(256-j)+2^j*((P%2^256)%2^(256-j)) := by
  let src := L.core.product.take 256
  have slen : src.length=256 := by simp [src,hw.core.product]
  have sv : regValue src s=P%2^256 := by
    exact L.product_take_value hw s P hP 256 (by omega)
  have hi := regValue_drop_div src (256-j) (by rw [slen]; omega) s
  have lo := regValue_take_mod src (256-j) (by rw [slen]; omega) s
  change regValue (src.drop (256-j)++src.take (256-j)) s=_
  rw [regValue_append,hi,lo,sv,List.length_drop,slen,
    show 256-(256-j)=j by omega]

structure SourceView (L : CuccaroStreamedSquareWideLayout) (src : List Wire) : Prop where
  length : src.length=256
  count_le : ∀q,src.count q≤L.core.product.count q+L.foldPad.count q

theorem source_nodup (L : CuccaroStreamedSquareWideLayout) (hnd : L.wires.Nodup)
    (src : List Wire) (hv : L.SourceView src) : (L.source src).wires.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hnd q
  have hs := hv.count_le q
  simp only [wires,CuccaroStreamedSquareLayout.wires,foldPad,source,
    CuccaroNormalizedModLayout.wires,List.count_append,List.count_cons,
    List.count_nil] at h hs ⊢
  omega

private theorem source_away_out (L : CuccaroStreamedSquareWideLayout)
    (hnd : L.wires.Nodup) (src : List Wire) (hv : L.SourceView src)
    (q : Wire) (hq : q∈(L.source src).normalize.a) : q∉L.core.out := by
  intro ho
  have h := List.nodup_iff_count.mp hnd q
  have hs := hv.count_le q
  have hm := List.count_pos_iff.mpr hq
  have hout := List.count_pos_iff.mpr ho
  simp only [wires,CuccaroStreamedSquareLayout.wires,foldPad,source,
    CuccaroNormalizedModLayout.normalize,CuccaroNormalizeLayout.a,
    List.count_append,List.count_cons,List.count_nil] at h hs hm
  omega

private theorem work_away_out (L : CuccaroStreamedSquareWideLayout)
    (hnd : L.wires.Nodup) (q : Wire)
    (hq : q∈L.core.work++[L.core.productHigh,L.core.outHigh,L.core.workHigh,
      L.core.cin,L.core.normFlag,L.core.modFlag]) :
    q∉L.core.out := by
  intro ho
  have h := List.nodup_iff_count.mp hnd q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr ho
  simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
    List.count_cons,List.count_nil] at h h1
  omega

private theorem source_values_at_frame (L : CuccaroStreamedSquareWideLayout)
    (hnd : L.wires.Nodup) (src : List Wire) (hv : L.SourceView src)
    (base : BasisState) (S O : Nat)
    (hS : regValue src base=S) (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false)
    (s : State) (h : SquareFrame L.core.out base O s.basis) :
    CuccaroNormalizedModValues (L.source src) S O 0 false false false s.basis := by
  have keep (q : Wire) (hq : q∉L.core.out) : s.basis q=base q := h.2 q hq
  have srcv : regValue src s.basis=S := by
    rw [←hS]
    apply regValue_congr
    intro q hq
    exact keep q (L.source_away_out hnd src hv q (by
      simp [CuccaroNormalizedModLayout.normalize,CuccaroNormalizeLayout.a,
        CuccaroStreamedSquareWideLayout.source,hq]))
  have phv : s.basis L.core.productHigh=false :=
    (keep _ (L.source_away_out hnd src hv _ (by
      simp [CuccaroNormalizedModLayout.normalize,CuccaroNormalizeLayout.a,
        CuccaroStreamedSquareWideLayout.source]))).trans hph
  have workv : regValue L.core.work s.basis=0 := by
    rw [←hw0]
    apply regValue_congr
    intro q hq
    exact keep q (L.work_away_out hnd q (by simp [hq]))
  have whv : s.basis L.core.workHigh=false :=
    (keep _ (L.work_away_out hnd _ (by simp))).trans hwh
  have civ : s.basis L.core.cin=false :=
    (keep _ (L.work_away_out hnd _ (by simp))).trans hci
  have nfv : s.basis L.core.normFlag=false :=
    (keep _ (L.work_away_out hnd _ (by simp))).trans hnf
  have mfv : s.basis L.core.modFlag=false :=
    (keep _ (L.work_away_out hnd _ (by simp))).trans hmf
  have ohv : s.basis L.core.outHigh=false := by
    exact (keep _ (L.work_away_out hnd _ (by simp))).trans hoh
  have phreg : regValue [L.core.productHigh] s.basis=0 := by
    simp [regValue,phv]
  have ohreg : regValue [L.core.outHigh] s.basis=0 := by
    simp [regValue,ohv]
  have whreg : regValue [L.core.workHigh] s.basis=0 := by
    simp [regValue,whv]
  constructor
  · simp only [CuccaroStreamedSquareWideLayout.source,CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.a,regValue_append,srcv,phreg,Nat.mul_zero,Nat.add_zero]
  · simpa only [CuccaroStreamedSquareWideLayout.source,CuccaroNormalizedModLayout.modular,
      CuccaroModLayout.z,regValue_append,ohreg,Nat.mul_zero,Nat.add_zero] using h.1
  · simp only [CuccaroStreamedSquareWideLayout.source,CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.scratch,regValue_append,workv,whreg,Nat.mul_zero,Nat.add_zero]
  · exact civ
  · exact nfv
  · exact mfv

private theorem fold_frame_finish (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (src : List Wire) (hv : L.SourceView src)
    (base : BasisState) (S O R : Nat)
    (hR : R<SquareReduction.p)
    (hS : regValue src base=S) (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false)
    (s out : State) (hpre : SquareFrame L.core.out base O s.basis)
    (hout : CuccaroNormalizedModValues (L.source src) S R 0 false false false out.basis)
    (houtside : ∀q,q∉(L.source src).wires → out.basis q=s.basis q) :
    SquareFrame L.core.out base R out.basis := by
  have before := L.source_values_at_frame hnd src hv base S O hS hw0 hph hoh hwh hci hnf hmf s hpre
  have postZ : regValue (L.core.out++[L.core.outHigh]) out.basis=R := by
    simpa only [CuccaroStreamedSquareWideLayout.source,
      CuccaroNormalizedModLayout.modular,CuccaroModLayout.z] using hout.out
  have high0 : out.basis L.core.outHigh=false := by
    have hz := regValue_highBit L.core.out L.core.outHigh out.basis
    rw [hw.core.out,postZ] at hz
    have hp : R<2^256 := hR.trans (by
      norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    cases hb : out.basis L.core.outHigh <;> simp_all <;> omega
  constructor
  · have split := regValue_append L.core.out [L.core.outHigh] out.basis
    rw [postZ] at split
    simp [regValue,high0] at split
    exact split.symm
  · intro q hq
    by_cases hm : q∈(L.source src).wires
    · by_cases ha : q∈(L.source src).normalize.a
      · exact (regValue_eq_iff _ _ _).mp (hout.source.trans before.source.symm) q ha
          |>.trans (hpre.2 q hq)
      by_cases hz : q∈(L.source src).modular.z
      · have hor : q∈L.core.out∨q=L.core.outHigh := by
          simpa [CuccaroStreamedSquareWideLayout.source,
            CuccaroNormalizedModLayout.modular,CuccaroModLayout.z] using hz
        rcases hor with hor|rfl
        · exact False.elim (hq hor)
        · exact high0.trans hoh.symm
      by_cases hwork : q∈(L.source src).normalize.scratch
      · exact (regValue_eq_iff _ _ _).mp (hout.work.trans before.work.symm) q hwork
          |>.trans (hpre.2 q hq)
      by_cases hc : q=L.core.cin
      · subst q; exact hout.cin.trans hci.symm
      by_cases hn : q=L.core.normFlag
      · subst q; exact hout.normFlag.trans hnf.symm
      by_cases hf : q=L.core.modFlag
      · subst q; exact hout.modFlag.trans hmf.symm
      exfalso
      have hnot : q∉(L.source src).wires := by
        intro hmem
        simp only [CuccaroStreamedSquareWideLayout.source,
          CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.normalize,
          CuccaroNormalizedModLayout.modular,CuccaroNormalizeLayout.a,
          CuccaroNormalizeLayout.scratch,CuccaroModLayout.z,List.mem_append,
          List.mem_cons,List.not_mem_nil,or_false] at ha hz hwork hmem
        tauto
      exact hnot hm
    · exact (houtside q hm).trans (hpre.2 q hq)

theorem addSource_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (src : List Wire) (hv : L.SourceView src)
    (base : BasisState) (S O : Nat) (hS : regValue src base=S)
    (hSb : S<2^256) (hO : O<SquareReduction.p)
    (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false) :
    Triple (SquareFrame L.core.out base O) (L.addSource src)
      (SquareFrame L.core.out base ((S%SquareReduction.p+O)%SquareReduction.p)) := by
  have nd := L.source_nodup hnd src hv
  have spec := cuccaroNormalizedModAdd_spec (L.source src) 256 SquareReduction.c
    SquareReduction.p S O (L.source_widths hw src hv.length) nd
    (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    (by norm_num [SquareReduction.c]) (by norm_num [SquareReduction.c])
    (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]) hSb hO
  intro s records h
  have pre := L.source_values_at_frame hnd src hv base S O hS hw0 hph hoh hwh hci hnf hmf s h
  obtain ⟨phase,post⟩ := spec s records pre
  have outside := cuccaroNormalizedModAdd_preserves_outside (L.source src) 256
    SquareReduction.c SquareReduction.p (L.source_widths hw src hv.length) s records
  refine ⟨phase,L.fold_frame_finish hw hnd src hv base S O _
    (Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]))
    hS hw0 hph hoh hwh hci hnf hmf
    s (run (L.addSource src) records s) h post ?_⟩
  intro q hq
  exact outside q hq

theorem subSource_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (src : List Wire) (hv : L.SourceView src)
    (base : BasisState) (S O : Nat) (hS : regValue src base=S)
    (hSb : S<2^256) (hO : O<SquareReduction.p)
    (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false) :
    Triple (SquareFrame L.core.out base O) (L.subSource src)
      (SquareFrame L.core.out base
        ((O+SquareReduction.p-(S%SquareReduction.p))%SquareReduction.p)) := by
  have nd := L.source_nodup hnd src hv
  have spec := cuccaroNormalizedModSub_spec (L.source src) 256 SquareReduction.c
    SquareReduction.p S O (L.source_widths hw src hv.length) nd
    (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    (by norm_num [SquareReduction.c]) (by norm_num [SquareReduction.c])
    (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]) hSb hO
  intro s records h
  have pre := L.source_values_at_frame hnd src hv base S O hS hw0 hph hoh hwh hci hnf hmf s h
  obtain ⟨phase,post⟩ := spec s records pre
  have outside := cuccaroNormalizedModSub_preserves_outside (L.source src) 256
    SquareReduction.c SquareReduction.p (L.source_widths hw src hv.length) s records
  refine ⟨phase,L.fold_frame_finish hw hnd src hv base S O _
    (Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]))
    hS hw0 hph hoh hwh hci hnf hmf
    s (run (L.subSource src) records s) h post ?_⟩
  intro q hq
  exact outside q hq

theorem productTake256_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.SourceView (L.core.product.take 256) := by
  constructor
  · simp [hw.core.product]
  · intro q
    have ht := (List.take_sublist 256 L.core.product).count_le q
    simp only [foldPad,List.count_append]
    omega

theorem rotated128_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.SourceView L.rotated128 := by
  constructor
  · simp [rotated128,hw.core.product]
  · intro q
    have he := congrArg (List.count q) (List.take_append_drop 128 L.core.product)
    have ht := (List.take_sublist 128 (L.core.product.drop 128)).count_le q
    simp only [rotated128,foldPad,List.count_append] at he ⊢
    omega

private theorem shifted_count_bound (src pad : List Wire) (j width : Nat) (q : Wire) :
    (shiftedSource src pad j width).count q≤src.count q+pad.count q := by
  have h := (List.take_sublist (width-j-src.length) (pad.drop j)).count_le q
  have he := congrArg (List.count q) (List.take_append_drop j pad)
  simp only [shiftedSource,List.count_append] at he ⊢
  omega

theorem shifted_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (src : List Wire) (hsrc : ∀q,src.count q≤L.core.product.count q)
    (j : Nat) (hlo : 2≤src.length) (hlen : src.length+j≤256) :
    L.SourceView (L.shifted src j) := by
  constructor
  · exact L.shifted_length hw src j hlo hlen
  · intro q
    have hs := shifted_count_bound src L.foldPad j 256 q
    have hp := hsrc q
    change (shiftedSource src L.foldPad j 256).count q≤_
    omega

theorem productDrop_count (L : CuccaroStreamedSquareWideLayout) (k : Nat) (q : Wire) :
    (L.core.product.drop k).count q≤L.core.product.count q :=
  (List.drop_sublist k L.core.product).count_le q

theorem shiftedProductDrop_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (k j : Nat) (hlo : 2≤(L.core.product.drop k).length)
    (hlen : (L.core.product.drop k).length+j≤256) :
    L.SourceView (L.shifted (L.core.product.drop k) j) :=
  L.shifted_view hw _ (L.productDrop_count k) j hlo hlen

theorem rotateFull_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (j : Nat) (hj : j≤256) :
    L.SourceView (rotateFull (L.core.product.take 256) j) := by
  constructor
  · exact rotateFull_length _ _ (by simp [hw.core.product]) hj
  · intro q
    have he := congrArg (List.count q)
      (List.take_append_drop (256-j) (L.core.product.take 256))
    have ht := (List.take_sublist 256 L.core.product).count_le q
    simp only [rotateFull,foldPad,List.count_append] at he ⊢
    omega

theorem addShifted_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (src : List Wire)
    (hsrc : ∀q,src.count q≤L.core.product.count q)
    (j : Nat) (hlo : 2≤src.length) (hlen : src.length+j≤256)
    (base : BasisState) (O : Nat) (hO : O<SquareReduction.p)
    (hpad : regValue L.foldPad base=0) (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false) :
    Triple (SquareFrame L.core.out base O) (L.addSource (L.shifted src j))
      (SquareFrame L.core.out base
        (((regValue src base*2^j)%SquareReduction.p+O)%SquareReduction.p)) := by
  have view := L.shifted_view hw src hsrc j hlo hlen
  have value := shiftedSource_value src L.foldPad j 256 (by omega)
    (by rw [L.foldPad_length hw]; omega) base hpad
  have bound : regValue src base*2^j<2^256 := by
    have hs := regValue_lt src base
    have hp : 0<2^j := by positivity
    have hm := Nat.mul_lt_mul_of_pos_right hs hp
    rw [←Nat.pow_add] at hm
    exact lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hlen)
  exact L.addSource_frame hw hnd _ view base _ O value bound hO hw0
    hph hoh hwh hci hnf hmf

theorem subShifted_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (src : List Wire)
    (hsrc : ∀q,src.count q≤L.core.product.count q)
    (j : Nat) (hlo : 2≤src.length) (hlen : src.length+j≤256)
    (base : BasisState) (O : Nat) (hO : O<SquareReduction.p)
    (hpad : regValue L.foldPad base=0) (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false) :
    Triple (SquareFrame L.core.out base O) (L.subSource (L.shifted src j))
      (SquareFrame L.core.out base
        ((O+SquareReduction.p-(regValue src base*2^j)%SquareReduction.p)%
          SquareReduction.p)) := by
  have view := L.shifted_view hw src hsrc j hlo hlen
  have value := shiftedSource_value src L.foldPad j 256 (by omega)
    (by rw [L.foldPad_length hw]; omega) base hpad
  have bound : regValue src base*2^j<2^256 := by
    have hs := regValue_lt src base
    have hp : 0<2^j := by positivity
    have hm := Nat.mul_lt_mul_of_pos_right hs hp
    rw [←Nat.pow_add] at hm
    exact lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hlen)
  exact L.subSource_frame hw hnd _ view base _ O value bound hO hw0
    hph hoh hwh hci hnf hmf

def addModValue (S O : Nat) : Nat :=
  (S%SquareReduction.p+O)%SquareReduction.p

def subModValue (S O : Nat) : Nat :=
  (O+SquareReduction.p-S%SquareReduction.p)%SquareReduction.p

def addCMinusOneValue (H O : Nat) : Nat :=
  addModValue (H*2^32)
    (addModValue (H*2^10)
      (subModValue (H*2^6) (addModValue (H*2^4) O)))

def subCMinusOneValue (H O : Nat) : Nat :=
  subModValue (H*2^32)
    (subModValue (H*2^10)
      (addModValue (H*2^6) (subModValue (H*2^4) O)))

theorem addCMinusOne_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (high : List Wire)
    (hsrc : ∀q,high.count q≤L.core.product.count q)
    (hlo : 2≤high.length) (hhi : high.length+32≤256)
    (base : BasisState) (O : Nat) (hO : O<SquareReduction.p)
    (hpad : regValue L.foldPad base=0) (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false) :
    Triple (SquareFrame L.core.out base O) (L.addCMinusOne high)
      (SquareFrame L.core.out base (addCMinusOneValue (regValue high base) O)) := by
  let H := regValue high base
  let O4 := addModValue (H*2^4) O
  let O6 := subModValue (H*2^6) O4
  let O10 := addModValue (H*2^10) O6
  let O32 := addModValue (H*2^32) O10
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have h4 := L.addShifted_frame hw hnd high hsrc 4 hlo (by omega) base O hO
    hpad hw0 hph hoh hwh hci hnf hmf
  have h6 := L.subShifted_frame hw hnd high hsrc 6 hlo (by omega) base O4
    (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  have h10 := L.addShifted_frame hw hnd high hsrc 10 hlo (by omega) base O6
    (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  have h32 := L.addShifted_frame hw hnd high hsrc 32 hlo hhi base O10
    (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  simpa [addCMinusOne,addCMinusOneValue,addModValue,subModValue,H,O4,O6,O10,O32,
    List.append_assoc] using h4.seq (h6.seq (h10.seq h32))

theorem subCMinusOne_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (high : List Wire)
    (hsrc : ∀q,high.count q≤L.core.product.count q)
    (hlo : 2≤high.length) (hhi : high.length+32≤256)
    (base : BasisState) (O : Nat) (hO : O<SquareReduction.p)
    (hpad : regValue L.foldPad base=0) (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false) :
    Triple (SquareFrame L.core.out base O) (L.subCMinusOne high)
      (SquareFrame L.core.out base (subCMinusOneValue (regValue high base) O)) := by
  let H := regValue high base
  let O4 := subModValue (H*2^4) O
  let O6 := addModValue (H*2^6) O4
  let O10 := subModValue (H*2^10) O6
  let O32 := subModValue (H*2^32) O10
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have h4 := L.subShifted_frame hw hnd high hsrc 4 hlo (by omega) base O hO
    hpad hw0 hph hoh hwh hci hnf hmf
  have h6 := L.addShifted_frame hw hnd high hsrc 6 hlo (by omega) base O4
    (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  have h10 := L.subShifted_frame hw hnd high hsrc 10 hlo (by omega) base O6
    (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  have h32 := L.subShifted_frame hw hnd high hsrc 32 hlo hhi base O10
    (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  simpa [subCMinusOne,subCMinusOneValue,addModValue,subModValue,H,O4,O6,O10,O32,
    List.append_assoc] using h4.seq (h6.seq (h10.seq h32))

def addRotate128Value (R H E O : Nat) (withOverhang : Bool) : Nat :=
  let main := addCMinusOneValue H (addModValue R O)
  if withOverhang then addModValue (E*2^128) main else main

def subRotate128Value (R H E O : Nat) (withOverhang : Bool) : Nat :=
  let main := subCMinusOneValue H (subModValue R O)
  if withOverhang then subModValue (E*2^128) main else main

theorem addRotate128_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (withOverhang : Bool)
    (base : BasisState) (O : Nat) (hO : O<SquareReduction.p)
    (hpad : regValue L.foldPad base=0) (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false) :
    Triple (SquareFrame L.core.out base O) (L.addRotate128 withOverhang)
      (SquareFrame L.core.out base
        (addRotate128Value (regValue L.rotated128 base)
          (regValue (L.core.product.drop 128) base)
          (regValue (L.core.product.drop 256) base) O withOverhang)) := by
  let R := regValue L.rotated128 base
  let H := regValue (L.core.product.drop 128) base
  let E := regValue (L.core.product.drop 256) base
  let O1 := addModValue R O
  let O2 := addCMinusOneValue H O1
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hmain := L.addSource_frame hw hnd L.rotated128 (L.rotated128_view hw)
    base R O rfl (by
      have hb := regValue_lt L.rotated128 base
      rw [(L.rotated128_view hw).length] at hb
      exact hb) hO hw0
    hph hoh hwh hci hnf hmf
  have hcm := L.addCMinusOne_frame hw hnd (L.core.product.drop 128)
    (L.productDrop_count 128) (by simp [hw.core.product]) (by simp [hw.core.product])
    base O1 (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  have hover := L.addShifted_frame hw hnd (L.core.product.drop 256)
    (L.productDrop_count 256) 128 (by simp [hw.core.product]) (by simp [hw.core.product])
    base O2 (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  cases withOverhang
  · simpa [addRotate128,addRotate128Value,addModValue,R,H,E,O1,O2,List.append_assoc] using hmain.seq hcm
  · simpa [addRotate128,addRotate128Value,addModValue,R,H,E,O1,O2,List.append_assoc] using
      hmain.seq (hcm.seq hover)

theorem subRotate128_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (withOverhang : Bool)
    (base : BasisState) (O : Nat) (hO : O<SquareReduction.p)
    (hpad : regValue L.foldPad base=0) (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false) :
    Triple (SquareFrame L.core.out base O) (L.subRotate128 withOverhang)
      (SquareFrame L.core.out base
        (subRotate128Value (regValue L.rotated128 base)
          (regValue (L.core.product.drop 128) base)
          (regValue (L.core.product.drop 256) base) O withOverhang)) := by
  let R := regValue L.rotated128 base
  let H := regValue (L.core.product.drop 128) base
  let E := regValue (L.core.product.drop 256) base
  let O1 := subModValue R O
  let O2 := subCMinusOneValue H O1
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hmain := L.subSource_frame hw hnd L.rotated128 (L.rotated128_view hw)
    base R O rfl (by
      have hb := regValue_lt L.rotated128 base
      rw [(L.rotated128_view hw).length] at hb
      exact hb) hO hw0
    hph hoh hwh hci hnf hmf
  have hcm := L.subCMinusOne_frame hw hnd (L.core.product.drop 128)
    (L.productDrop_count 128) (by simp [hw.core.product]) (by simp [hw.core.product])
    base O1 (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  have hover := L.subShifted_frame hw hnd (L.core.product.drop 256)
    (L.productDrop_count 256) 128 (by simp [hw.core.product]) (by simp [hw.core.product])
    base O2 (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  cases withOverhang
  · simpa [subRotate128,subRotate128Value,subModValue,R,H,E,O1,O2,List.append_assoc] using hmain.seq hcm
  · simpa [subRotate128,subRotate128Value,subModValue,R,H,E,O1,O2,List.append_assoc] using
      hmain.seq (hcm.seq hover)

def addShiftFullValue (R H O : Nat) : Nat :=
  addCMinusOneValue H (addModValue R O)

def subShiftFullValue (R H O : Nat) : Nat :=
  subCMinusOneValue H (subModValue R O)

theorem productTakeDrop_count (L : CuccaroStreamedSquareWideLayout)
    (k : Nat) (q : Wire) :
    ((L.core.product.take 256).drop k).count q≤L.core.product.count q := by
  have h1 := (List.drop_sublist k (L.core.product.take 256)).count_le q
  have h2 := (List.take_sublist 256 L.core.product).count_le q
  omega

theorem addShiftFull_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (j : Nat) (hj0 : 2≤j) (hj : j≤224)
    (base : BasisState) (O : Nat) (hO : O<SquareReduction.p)
    (hpad : regValue L.foldPad base=0) (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false) :
    Triple (SquareFrame L.core.out base O)
      (L.addShiftFull (L.core.product.take 256) j)
      (SquareFrame L.core.out base
        (addShiftFullValue
          (regValue (rotateFull (L.core.product.take 256) j) base)
          (regValue ((L.core.product.take 256).drop (256-j)) base) O)) := by
  let R := regValue (rotateFull (L.core.product.take 256) j) base
  let H := regValue ((L.core.product.take 256).drop (256-j)) base
  let O1 := addModValue R O
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hm := L.addSource_frame hw hnd _ (L.rotateFull_view hw j (by omega))
    base R O rfl (by
      have hb := regValue_lt (rotateFull (L.core.product.take 256) j) base
      rw [(L.rotateFull_view hw j (by omega)).length] at hb
      exact hb) hO hw0 hph hoh hwh hci hnf hmf
  have hlen : ((L.core.product.take 256).drop (256-j)).length=j := by
    simp [hw.core.product]
    omega
  have hc := L.addCMinusOne_frame hw hnd _ (L.productTakeDrop_count (256-j))
    (by omega) (by rw [hlen]; omega) base O1 (Nat.mod_lt _ hp)
    hpad hw0 hph hoh hwh hci hnf hmf
  have jn : j≠0 := by omega
  simpa [addShiftFull,jn,addShiftFullValue,R,H,O1,List.append_assoc] using hm.seq hc

theorem subShiftFull_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (j : Nat) (hj0 : 2≤j) (hj : j≤224)
    (base : BasisState) (O : Nat) (hO : O<SquareReduction.p)
    (hpad : regValue L.foldPad base=0) (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false) :
    Triple (SquareFrame L.core.out base O)
      (L.subShiftFull (L.core.product.take 256) j)
      (SquareFrame L.core.out base
        (subShiftFullValue
          (regValue (rotateFull (L.core.product.take 256) j) base)
          (regValue ((L.core.product.take 256).drop (256-j)) base) O)) := by
  let R := regValue (rotateFull (L.core.product.take 256) j) base
  let H := regValue ((L.core.product.take 256).drop (256-j)) base
  let O1 := subModValue R O
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hm := L.subSource_frame hw hnd _ (L.rotateFull_view hw j (by omega))
    base R O rfl (by
      have hb := regValue_lt (rotateFull (L.core.product.take 256) j) base
      rw [(L.rotateFull_view hw j (by omega)).length] at hb
      exact hb) hO hw0 hph hoh hwh hci hnf hmf
  have hlen : ((L.core.product.take 256).drop (256-j)).length=j := by
    simp [hw.core.product]
    omega
  have hc := L.subCMinusOne_frame hw hnd _ (L.productTakeDrop_count (256-j))
    (by omega) (by rw [hlen]; omega) base O1 (Nat.mod_lt _ hp)
    hpad hw0 hph hoh hwh hci hnf hmf
  have jn : j≠0 := by omega
  simpa [subShiftFull,jn,subShiftFullValue,R,H,O1,List.append_assoc] using hm.seq hc

def subTimesCValue (P R4 H4 R6 H6 R10 H10 R32 H32 O : Nat) : Nat :=
  subShiftFullValue R32 H32
    (subShiftFullValue R10 H10
      (addShiftFullValue R6 H6
        (subShiftFullValue R4 H4 (subModValue P O))))

theorem subTimesC_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (O : Nat)
    (hO : O<SquareReduction.p)
    (hpad : regValue L.foldPad base=0) (hw0 : regValue L.core.work base=0)
    (hph : base L.core.productHigh=false) (hoh : base L.core.outHigh=false)
    (hwh : base L.core.workHigh=false) (hci : base L.core.cin=false)
    (hnf : base L.core.normFlag=false) (hmf : base L.core.modFlag=false) :
    let P := regValue (L.core.product.take 256) base
    let R4 := regValue (rotateFull (L.core.product.take 256) 4) base
    let H4 := regValue ((L.core.product.take 256).drop 252) base
    let R6 := regValue (rotateFull (L.core.product.take 256) 6) base
    let H6 := regValue ((L.core.product.take 256).drop 250) base
    let R10 := regValue (rotateFull (L.core.product.take 256) 10) base
    let H10 := regValue ((L.core.product.take 256).drop 246) base
    let R32 := regValue (rotateFull (L.core.product.take 256) 32) base
    let H32 := regValue ((L.core.product.take 256).drop 224) base
    Triple (SquareFrame L.core.out base O)
      (L.subTimesC (L.core.product.take 256))
      (SquareFrame L.core.out base
        (subTimesCValue P R4 H4 R6 H6 R10 H10 R32 H32 O)) := by
  dsimp only
  let P := regValue (L.core.product.take 256) base
  let O0 := subModValue P O
  let R4 := regValue (rotateFull (L.core.product.take 256) 4) base
  let H4 := regValue ((L.core.product.take 256).drop 252) base
  let O4 := subShiftFullValue R4 H4 O0
  let R6 := regValue (rotateFull (L.core.product.take 256) 6) base
  let H6 := regValue ((L.core.product.take 256).drop 250) base
  let O6 := addShiftFullValue R6 H6 O4
  let R10 := regValue (rotateFull (L.core.product.take 256) 10) base
  let H10 := regValue ((L.core.product.take 256).drop 246) base
  let O10 := subShiftFullValue R10 H10 O6
  let R32 := regValue (rotateFull (L.core.product.take 256) 32) base
  let H32 := regValue ((L.core.product.take 256).drop 224) base
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have pview := L.productTake256_view hw
  have h0 := L.subSource_frame hw hnd _ pview base P O rfl (by
    have hb := regValue_lt (L.core.product.take 256) base
    rw [pview.length] at hb
    exact hb) hO hw0 hph hoh hwh hci hnf hmf
  have h4 := L.subShiftFull_frame hw hnd 4 (by omega) (by omega) base O0
    (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  have h6 := L.addShiftFull_frame hw hnd 6 (by omega) (by omega) base O4
    (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  have h10 := L.subShiftFull_frame hw hnd 10 (by omega) (by omega) base O6
    (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  have h32 := L.subShiftFull_frame hw hnd 32 (by omega) (by omega) base O10
    (Nat.mod_lt _ hp) hpad hw0 hph hoh hwh hci hnf hmf
  simpa [subTimesC,subShiftFull,addShiftFull,subTimesCValue,P,O0,R4,H4,O4,
    R6,H6,O6,R10,H10,O10,R32,H32,List.append_assoc] using
      h0.seq (h4.seq (h6.seq (h10.seq h32)))

theorem square128_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (src : List Wire) (hlen : src.length=128)
    (hsrc : ∀q,src.count q≤L.core.y.count q)
    (base : BasisState) (X : Nat) (hX : regValue src base=X)
    (hprod : regValue L.core.product base=0)
    (hpad : regValue L.core.pad base=0) (hwork : regValue L.core.work base=0)
    (hcin : base L.core.cin=false) :
    Triple (SquareFrame (L.core.product.take 256) base 0) (L.core.square128 src)
      (SquareFrame (L.core.product.take 256) base (X^2)) := by
  let dst := L.core.product.take 256
  let mask := L.core.work.take 128
  have dlen : dst.length=256 := by simp [dst,hw.core.product]
  have mlen : mask.length=128 := by simp [mask,hw.core.work]
  have nd : (L.core.cin::src++dst++L.core.pad++mask++([] : List Wire)).Nodup := by
    dsimp [dst,mask]
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hnd q
    have hs := hsrc q
    have hd := (List.take_sublist 256 L.core.product).count_le q
    have hm := (List.take_sublist 128 L.core.work).count_le q
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
      List.count_cons,List.count_nil] at h ⊢
    omega
  have dst0 : regValue dst base=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hprod q (List.mem_of_mem_take hq))
  have mask0 : regValue mask base=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hwork q (List.mem_of_mem_take hq))
  intro s records h
  have away (q : Wire) (hq : q∈src++L.core.pad++mask++[L.core.cin]) : q∉dst := by
    intro hdq
    have hn := List.nodup_iff_count.mp nd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hdq
    simp only [List.count_append,List.count_cons,List.count_nil] at hn h1
    omega
  have srcS : regValue src s.basis=X := by
    rw [←hX]
    apply regValue_congr
    intro q hq
    exact h.2 q (away q (by simp [hq]))
  have padS : regValue L.core.pad s.basis=0 := by
    rw [←hpad]
    apply regValue_congr
    intro q hq
    exact h.2 q (away q (by simp [hq]))
  have maskS : regValue mask s.basis=0 := by
    rw [←mask0]
    apply regValue_congr
    intro q hq
    exact h.2 q (away q (by simp [hq]))
  have cinS : s.basis L.core.cin=false :=
    (h.2 _ (away _ (by simp))).trans hcin
  have runh := cuccaroSignedTriangularSquare_forward_correct L.core.cin src dst
    L.core.pad mask [] nd (by omega) (by omega) (by simp [hw.core.pad])
    (by omega) s records h.1 padS maskS rfl cinS
  refine ⟨runh.1,?_,?_⟩
  · simpa [srcS] using runh.2.1
  · intro q hq
    by_cases hs : q∈src
    · exact ((regValue_eq_iff src _ _).mp runh.2.2.1 q hs).trans
        (h.2 q (away q (by simp [hs])))
    by_cases hp : q∈L.core.pad
    · exact ((regValue_eq_iff L.core.pad _ _).mp (runh.2.2.2.1.trans padS.symm) q hp).trans
        (h.2 q (away q (by simp [hp])))
    by_cases hm : q∈mask
    · exact ((regValue_eq_iff mask _ _).mp (runh.2.2.2.2.1.trans maskS.symm) q hm).trans
        (h.2 q (away q (by simp [hm])))
    by_cases hc : q=L.core.cin
    · subst q; exact runh.2.2.2.2.2.2.trans hcin.symm
    have hsupp := (cuccaroSignedTriangularSquare_wires_subset L.core.cin src dst
      L.core.pad mask [] (by omega) (by omega) (by simp [hw.core.pad]) (by omega)).1
    have untouched : (run (L.core.square128 src) records s).basis q=s.basis q := by
      apply run_preserves_outside
      intro hmemb
      have hh := List.mem_toFinset.mp (hsupp hmemb)
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hh
      tauto
    exact untouched.trans (h.2 q hq)

theorem square128Clear_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (src : List Wire) (hlen : src.length=128)
    (hsrc : ∀q,src.count q≤L.core.y.count q)
    (base : BasisState) (X : Nat) (hX : regValue src base=X)
    (hprod : regValue L.core.product base=0)
    (hpad : regValue L.core.pad base=0) (hwork : regValue L.core.work base=0)
    (hcin : base L.core.cin=false) :
    Triple (SquareFrame (L.core.product.take 256) base (X^2))
      (L.core.square128Clear src)
      (SquareFrame (L.core.product.take 256) base 0) := by
  let dst := L.core.product.take 256
  let mask := L.core.work.take 128
  have nd : (L.core.cin::src++dst++L.core.pad++mask++([] : List Wire)).Nodup := by
    dsimp [dst,mask]
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hnd q
    have hs := hsrc q
    have hd := (List.take_sublist 256 L.core.product).count_le q
    have hm := (List.take_sublist 128 L.core.work).count_le q
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
      List.count_cons,List.count_nil] at h ⊢
    omega
  have dst0 : regValue dst base=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hprod q (List.mem_of_mem_take hq))
  intro s records hs
  let z : State := ⟨s.phase,base⟩
  have zpre : SquareFrame dst base 0 z.basis := ⟨dst0,fun _ _ => rfl⟩
  have ftriple := L.square128_frame hw hnd src hlen hsrc base X hX hprod hpad hwork hcin
  have f := ftriple z [] zpre
  let u := run (L.core.square128 src) [] z
  have us : u=s := by
    have ph : u.phase=s.phase := f.1
    have bs : u.basis=s.basis := by
      funext q
      by_cases hq : q∈dst
      · exact (regValue_eq_iff dst u.basis s.basis).mp (f.2.1.trans hs.1.symm) q hq
      · exact (f.2.2 q hq).trans (hs.2 q hq).symm
    calc
      u = ⟨u.phase,u.basis⟩ := rfl
      _ = ⟨s.phase,s.basis⟩ := by rw [ph,bs]
      _ = s := rfl
  have rr := cuccaroSignedTriangularSquare_roundtrip L.core.cin src dst
    L.core.pad mask [] nd z [] records
  change run (L.core.square128Clear src) records u=z at rr
  rw [us] at rr
  rw [rr]
  exact ⟨rfl,dst0,fun _ _ => rfl⟩

/-- Simultaneous frame for the live sub-square product and the point output.
This is the invariant needed by `with_square`: producers change `product`,
folds change `out`, and both preserve every wire outside those two registers. -/
structure PairFrame (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (P O : Nat) (s : BasisState) : Prop where
  product : regValue L.core.product s=P
  out : regValue L.core.out s=O
  frame : ∀q,q∉L.core.product → q∉L.core.out → s q=base q

theorem square128_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (src : List Wire) (hlen : src.length=128)
    (hsrc : ∀q,src.count q≤L.core.y.count q)
    (base : BasisState) (X O : Nat) (hX : regValue src base=X)
    (hpad : regValue L.core.pad base=0) (hwork : regValue L.core.work base=0)
    (hcin : base L.core.cin=false) :
    Triple (PairFrame L base 0 O) (L.core.square128 src)
      (PairFrame L base (X^2) O) := by
  have srcAway (q : Wire) (hq : q∈src) :
      q∉L.core.product ∧ q∉L.core.out := by
    constructor <;> intro hm
    · have h := List.nodup_iff_count.mp hnd q
      have hs := hsrc q
      have hq' := List.count_pos_iff.mpr hq
      have hp := List.count_pos_iff.mpr hm
      simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
        List.count_cons,List.count_nil] at h
      omega
    · have h := List.nodup_iff_count.mp hnd q
      have hs := hsrc q
      have hq' := List.count_pos_iff.mpr hq
      have ho := List.count_pos_iff.mpr hm
      simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
        List.count_cons,List.count_nil] at h
      omega
  have regAway (r : List Wire)
      (hr : r=L.core.pad ∨ r=L.core.work) (q : Wire) (hq : q∈r) :
      q∉L.core.product ∧ q∉L.core.out := by
    constructor <;> intro hm
    all_goals
      have h := List.nodup_iff_count.mp hnd q
      have h1 := List.count_pos_iff.mpr hq
      have h2 := List.count_pos_iff.mpr hm
      rcases hr with rfl|rfl
      all_goals
        simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
          List.count_cons,List.count_nil] at h h1
        omega
  have cinAway : L.core.cin∉L.core.product ∧ L.core.cin∉L.core.out := by
    constructor <;> intro hm
    all_goals
      have h := List.nodup_iff_count.mp hnd L.core.cin
      have h2 := List.count_pos_iff.mpr hm
      simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
        List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
      omega
  intro s records h
  have srcS : regValue src s.basis=X := by
    rw [←hX]
    apply regValue_congr
    intro q hq
    exact h.frame q (srcAway q hq).1 (srcAway q hq).2
  have padS : regValue L.core.pad s.basis=0 := by
    rw [←hpad]
    apply regValue_congr
    intro q hq
    exact h.frame q (regAway _ (Or.inl rfl) q hq).1
      (regAway _ (Or.inl rfl) q hq).2
  have workS : regValue L.core.work s.basis=0 := by
    rw [←hwork]
    apply regValue_congr
    intro q hq
    exact h.frame q (regAway _ (Or.inr rfl) q hq).1
      (regAway _ (Or.inr rfl) q hq).2
  have cinS : s.basis L.core.cin=false :=
    (h.frame _ cinAway.1 cinAway.2).trans hcin
  have take0 : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp h.product q
      (List.mem_of_mem_take hq))
  have sq := L.square128_frame hw hnd src hlen hsrc s.basis X srcS h.product
    padS workS cinS s records ⟨take0,fun _ _ => rfl⟩
  let out := run (L.core.square128 src) records s
  have high0 : regValue (L.core.product.drop 256) out.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have qt : q∉L.core.product.take 256 := by
      intro ht
      have hp : L.core.product.Nodup := by
        apply List.nodup_iff_count.mpr
        intro w
        have hh := List.nodup_iff_count.mp hnd w
        simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
          List.count_cons,List.count_nil] at hh ⊢
        omega
      exact List.disjoint_left.mp (List.disjoint_take_drop hp (show 256≤256 from le_rfl)) ht hq
    rw [sq.2.2 q qt]
    exact (regValue_zero _ _).mp h.product q (List.mem_of_mem_drop hq)
  have productOut : regValue L.core.product out.basis=X^2 := by
    have split := regValue_append (L.core.product.take 256)
      (L.core.product.drop 256) out.basis
    rw [List.take_append_drop,sq.2.1,high0,Nat.mul_zero,Nat.add_zero] at split
    exact split
  have outAway : L.core.out.Disjoint (L.core.product.take 256) := by
    apply List.disjoint_left.mpr
    intro q hq ho
    have ht := List.mem_of_mem_take ho
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr ht
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
      List.count_cons,List.count_nil] at hn
    omega
  have outputOut : regValue L.core.out out.basis=O :=
    (regValue_congr _ _ _ (fun q hq => sq.2.2 q
      (List.disjoint_left.mp outAway hq))).trans h.out
  refine ⟨sq.1,productOut,outputOut,?_⟩
  intro q hp ho
  exact (sq.2.2 q (fun ht => hp (List.mem_of_mem_take ht))).trans (h.frame q hp ho)

structure PairClean (L : CuccaroStreamedSquareWideLayout) (base : BasisState) : Prop where
  pad : regValue L.foldPad base=0
  work : regValue L.core.work base=0
  productHigh : base L.core.productHigh=false
  outHigh : base L.core.outHigh=false
  workHigh : base L.core.workHigh=false
  cin : base L.core.cin=false
  normFlag : base L.core.normFlag=false
  modFlag : base L.core.modFlag=false

theorem pairAuxAway (L : CuccaroStreamedSquareWideLayout)
    (hnd : L.wires.Nodup) (q : Wire)
    (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
    q∉L.core.product ∧ q∉L.core.out := by
  constructor <;> intro hm
  all_goals
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [wires,CuccaroStreamedSquareLayout.wires,foldPad,
      List.count_append,List.count_cons,List.count_nil] at h h1
    omega

theorem PairFrame.clean (L : CuccaroStreamedSquareWideLayout)
    (hnd : L.wires.Nodup) (base : BasisState) (P O : Nat) (s : BasisState)
    (h : PairFrame L base P O s) (hc : PairClean L base) : PairClean L s := by
  have keep (q : Wire)
      (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : s q=base q :=
    h.frame q (L.pairAuxAway hnd q hq).1 (L.pairAuxAway hnd q hq).2
  constructor
  · rw [←hc.pad]
    apply regValue_congr
    intro q hq
    exact keep q (by simp [hq])
  · rw [←hc.work]
    apply regValue_congr
    intro q hq
    exact keep q (by simp [hq])
  · exact (keep _ (by simp)).trans hc.productHigh
  · exact (keep _ (by simp)).trans hc.outHigh
  · exact (keep _ (by simp)).trans hc.workHigh
  · exact (keep _ (by simp)).trans hc.cin
  · exact (keep _ (by simp)).trans hc.normFlag
  · exact (keep _ (by simp)).trans hc.modFlag

theorem product_out_disjoint (L : CuccaroStreamedSquareWideLayout)
    (hnd : L.wires.Nodup) : L.core.product.Disjoint L.core.out := by
  apply List.disjoint_left.mpr
  intro q hp ho
  have h := List.nodup_iff_count.mp hnd q
  have h1 := List.count_pos_iff.mpr hp
  have h2 := List.count_pos_iff.mpr ho
  simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
    List.count_cons,List.count_nil] at h
  omega

theorem addSource_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (src : List Wire) (hv : L.SourceView src)
    (base : BasisState) (P O S : Nat) (hO : O<SquareReduction.p)
    (hc : PairClean L base)
    (hval : ∀s,PairFrame L base P O s → regValue src s=S) :
    Triple (PairFrame L base P O) (L.addSource src)
      (PairFrame L base P (addModValue S O)) := by
  intro s records h
  have clean := PairFrame.clean L hnd base P O s.basis h hc
  have sf := L.addSource_frame hw hnd src hv s.basis S O (hval s.basis h)
    (by rw [←hval s.basis h]; have hb := regValue_lt src s.basis; rw [hv.length] at hb; exact hb)
    hO clean.work clean.productHigh clean.outHigh clean.workHigh clean.cin
    clean.normFlag clean.modFlag
  have runh := sf s records ⟨h.out,fun _ _ => rfl⟩
  let out := run (L.addSource src) records s
  have dis := L.product_out_disjoint hnd
  have prod : regValue L.core.product out.basis=P :=
    (regValue_congr _ _ _ (fun q hq => runh.2.2 q
      (List.disjoint_left.mp dis hq))).trans h.product
  refine ⟨runh.1,prod,runh.2.1,?_⟩
  intro q hp ho
  exact (runh.2.2 q ho).trans (h.frame q hp ho)

theorem subSource_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (src : List Wire) (hv : L.SourceView src)
    (base : BasisState) (P O S : Nat) (hO : O<SquareReduction.p)
    (hc : PairClean L base)
    (hval : ∀s,PairFrame L base P O s → regValue src s=S) :
    Triple (PairFrame L base P O) (L.subSource src)
      (PairFrame L base P (subModValue S O)) := by
  intro s records h
  have clean := PairFrame.clean L hnd base P O s.basis h hc
  have sf := L.subSource_frame hw hnd src hv s.basis S O (hval s.basis h)
    (by rw [←hval s.basis h]; have hb := regValue_lt src s.basis; rw [hv.length] at hb; exact hb)
    hO clean.work clean.productHigh clean.outHigh clean.workHigh clean.cin
    clean.normFlag clean.modFlag
  have runh := sf s records ⟨h.out,fun _ _ => rfl⟩
  let out := run (L.subSource src) records s
  have dis := L.product_out_disjoint hnd
  have prod : regValue L.core.product out.basis=P :=
    (regValue_congr _ _ _ (fun q hq => runh.2.2 q
      (List.disjoint_left.mp dis hq))).trans h.product
  refine ⟨runh.1,prod,runh.2.1,?_⟩
  intro q hp ho
  exact (runh.2.2 q ho).trans (h.frame q hp ho)

theorem square128Clear_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (src : List Wire) (hlen : src.length=128)
    (hsrc : ∀q,src.count q≤L.core.y.count q)
    (base : BasisState) (X O : Nat) (hX : regValue src base=X)
    (hXb : X<2^128) (hprod : regValue L.core.product base=0)
    (hpad : regValue L.core.pad base=0) (hwork : regValue L.core.work base=0)
    (hcin : base L.core.cin=false) :
    Triple (PairFrame L base (X^2) O) (L.core.square128Clear src)
      (PairFrame L base 0 O) := by
  have dis := L.product_out_disjoint hnd
  have srcAwayOut (q : Wire) (hq : q∈src) : q∉L.core.out := by
    intro ho
    have h := List.nodup_iff_count.mp hnd q
    have hs := hsrc q
    have hp := List.count_pos_iff.mpr hq
    have hout := List.count_pos_iff.mpr ho
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
      List.count_cons,List.count_nil] at h
    omega
  intro s records h
  let cleanBase : BasisState := fun q => if q∈L.core.out then s.basis q else base q
  have localProd : regValue L.core.product cleanBase=0 := by
    rw [←hprod]
    apply regValue_congr
    intro q hq
    simp only [cleanBase]
    rw [if_neg (List.disjoint_left.mp dis hq)]
  have localSrc : regValue src cleanBase=X := by
    rw [←hX]
    apply regValue_congr
    intro q hq
    simp [cleanBase,srcAwayOut q hq]
  have localPad : regValue L.core.pad cleanBase=0 := by
    rw [←hpad]
    apply regValue_congr
    intro q hq
    have away : q∉L.core.out := (L.pairAuxAway hnd q (by
      simp [foldPad,hq])).2
    simp [cleanBase,away]
  have localWork : regValue L.core.work cleanBase=0 := by
    rw [←hwork]
    apply regValue_congr
    intro q hq
    have away : q∉L.core.out := (L.pairAuxAway hnd q (by simp [hq])).2
    simp [cleanBase,away]
  have localCin : cleanBase L.core.cin=false := by
    have away : L.core.cin∉L.core.out := (L.pairAuxAway hnd _ (by simp)).2
    simp [cleanBase,away,hcin]
  have sqb : X^2<2^256 := by
    simpa only [show 2*128=256 by omega] using square_bound X 128 hXb
  have splitS := regValue_take_drop_of_lt L.core.product 256 (X^2) s.basis
    (by simp [hw.core.product]) h.product sqb
  have pre : SquareFrame (L.core.product.take 256) cleanBase (X^2) s.basis := by
    constructor
    · exact splitS.1
    · intro q hq
      simp only [cleanBase]
      by_cases ho : q∈L.core.out
      · simp [ho]
      rw [if_neg ho]
      by_cases hp : q∈L.core.product
      · have hd : q∈L.core.product.drop 256 := by
          have he := List.mem_append.mp (show q∈L.core.product.take 256++
            L.core.product.drop 256 by rwa [List.take_append_drop])
          exact he.resolve_left hq
        exact ((regValue_zero _ _).mp splitS.2 q hd).trans
          ((regValue_zero _ _).mp hprod q hp).symm
      · exact h.frame q hp ho
  have clear := L.square128Clear_frame hw hnd src hlen hsrc cleanBase X localSrc
    localProd localPad localWork localCin s records pre
  let out := run (L.core.square128Clear src) records s
  have drop0 : regValue (L.core.product.drop 256) out.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have qt : q∉L.core.product.take 256 := fun ht => by
      have hp : L.core.product.Nodup := by
        apply List.nodup_iff_count.mpr
        intro w
        have hh := List.nodup_iff_count.mp hnd w
        simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
          List.count_cons,List.count_nil] at hh ⊢
        omega
      exact List.disjoint_left.mp (List.disjoint_take_drop hp
        (show 256≤256 from le_rfl)) ht hq
    rw [clear.2.2 q qt]
    have qp : q∈L.core.product := List.mem_of_mem_drop hq
    have qo : q∉L.core.out := List.disjoint_left.mp dis qp
    simp only [cleanBase,if_neg qo]
    exact (regValue_zero _ _).mp hprod q qp
  have product0 : regValue L.core.product out.basis=0 := by
    have split := regValue_append (L.core.product.take 256)
      (L.core.product.drop 256) out.basis
    rw [List.take_append_drop,clear.2.1,drop0,Nat.mul_zero,Nat.add_zero] at split
    exact split
  have outputO : regValue L.core.out out.basis=O := by
    calc
      regValue L.core.out out.basis = regValue L.core.out cleanBase :=
        regValue_congr _ _ _ (fun q hq => clear.2.2 q
          (fun ht => List.disjoint_left.mp dis (List.mem_of_mem_take ht) hq))
      _ = regValue L.core.out s.basis := by
        apply regValue_congr
        intro q hq
        simp [cleanBase,hq]
      _ = O := h.out
  refine ⟨clear.1,product0,outputO,?_⟩
  intro q hp ho
  have qt : q∉L.core.product.take 256 := fun ht => hp (List.mem_of_mem_take ht)
  rw [clear.2.2 q qt]
  simp [cleanBase,ho,h.frame q hp ho]

def addRotateProductValue (P O : Nat) (withOverhang : Bool) : Nat :=
  addRotate128Value ((P/2^128)%2^128+2^128*(P%2^128))
    (P/2^128) (P/2^256) O withOverhang

def subRotateProductValue (P O : Nat) (withOverhang : Bool) : Nat :=
  subRotate128Value ((P/2^128)%2^128+2^128*(P%2^128))
    (P/2^128) (P/2^256) O withOverhang

theorem addRotate128_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (withOverhang : Bool)
    (base : BasisState) (P O : Nat) (hO : O<SquareReduction.p)
    (hc : PairClean L base) :
    Triple (PairFrame L base P O) (L.addRotate128 withOverhang)
      (PairFrame L base P (addRotateProductValue P O withOverhang)) := by
  intro s records h
  have clean := PairFrame.clean L hnd base P O s.basis h hc
  have f := L.addRotate128_frame hw hnd withOverhang s.basis O hO clean.pad
    clean.work clean.productHigh clean.outHigh clean.workHigh clean.cin
    clean.normFlag clean.modFlag s records ⟨h.out,fun _ _ => rfl⟩
  let out := run (L.addRotate128 withOverhang) records s
  have rv := L.rotated128_value hw s.basis P h.product
  have hv := L.product_drop_value hw s.basis P h.product 128 (by omega)
  have ev := L.product_drop_value hw s.basis P h.product 256 (by omega)
  have outv : regValue L.core.out out.basis=addRotateProductValue P O withOverhang := by
    rw [f.2.1,addRotateProductValue,rv,hv,ev]
  have dis := L.product_out_disjoint hnd
  have prod : regValue L.core.product out.basis=P :=
    (regValue_congr _ _ _ (fun q hq => f.2.2 q
      (List.disjoint_left.mp dis hq))).trans h.product
  refine ⟨f.1,prod,outv,?_⟩
  intro q hp ho
  exact (f.2.2 q ho).trans (h.frame q hp ho)

theorem subRotate128_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (withOverhang : Bool)
    (base : BasisState) (P O : Nat) (hO : O<SquareReduction.p)
    (hc : PairClean L base) :
    Triple (PairFrame L base P O) (L.subRotate128 withOverhang)
      (PairFrame L base P (subRotateProductValue P O withOverhang)) := by
  intro s records h
  have clean := PairFrame.clean L hnd base P O s.basis h hc
  have f := L.subRotate128_frame hw hnd withOverhang s.basis O hO clean.pad
    clean.work clean.productHigh clean.outHigh clean.workHigh clean.cin
    clean.normFlag clean.modFlag s records ⟨h.out,fun _ _ => rfl⟩
  let out := run (L.subRotate128 withOverhang) records s
  have rv := L.rotated128_value hw s.basis P h.product
  have hv := L.product_drop_value hw s.basis P h.product 128 (by omega)
  have ev := L.product_drop_value hw s.basis P h.product 256 (by omega)
  have outv : regValue L.core.out out.basis=subRotateProductValue P O withOverhang := by
    rw [f.2.1,subRotateProductValue,rv,hv,ev]
  have dis := L.product_out_disjoint hnd
  have prod : regValue L.core.product out.basis=P :=
    (regValue_congr _ _ _ (fun q hq => f.2.2 q
      (List.disjoint_left.mp dis hq))).trans h.product
  refine ⟨f.1,prod,outv,?_⟩
  intro q hp ho
  exact (f.2.2 q ho).trans (h.frame q hp ho)

def rotatedFullValue (P j : Nat) : Nat :=
  (P%2^256)/2^(256-j)+2^j*((P%2^256)%2^(256-j))

def highFullValue (P j : Nat) : Nat := (P%2^256)/2^(256-j)

def subTimesProductValue (P O : Nat) : Nat :=
  subTimesCValue (P%2^256)
    (rotatedFullValue P 4) (highFullValue P 4)
    (rotatedFullValue P 6) (highFullValue P 6)
    (rotatedFullValue P 10) (highFullValue P 10)
    (rotatedFullValue P 32) (highFullValue P 32) O

theorem subTimesC_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (P O : Nat)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base P O) (L.subTimesC (L.core.product.take 256))
      (PairFrame L base P (subTimesProductValue P O)) := by
  intro s records h
  have clean := PairFrame.clean L hnd base P O s.basis h hc
  have f := L.subTimesC_frame hw hnd s.basis O hO clean.pad clean.work
    clean.productHigh clean.outHigh clean.workHigh clean.cin clean.normFlag
    clean.modFlag s records ⟨h.out,fun _ _ => rfl⟩
  let out := run (L.subTimesC (L.core.product.take 256)) records s
  have pv := L.product_take_value hw s.basis P h.product 256 (by omega)
  have r4 := L.rotateFull_value hw s.basis P h.product 4 (by omega)
  have h4 := L.productTakeDrop_value hw s.basis P h.product 4 (by omega)
  have r6 := L.rotateFull_value hw s.basis P h.product 6 (by omega)
  have h6 := L.productTakeDrop_value hw s.basis P h.product 6 (by omega)
  have r10 := L.rotateFull_value hw s.basis P h.product 10 (by omega)
  have h10 := L.productTakeDrop_value hw s.basis P h.product 10 (by omega)
  have r32 := L.rotateFull_value hw s.basis P h.product 32 (by omega)
  have h32 := L.productTakeDrop_value hw s.basis P h.product 32 (by omega)
  have outv : regValue L.core.out out.basis=subTimesProductValue P O := by
    rw [f.2.1]
    simp only [subTimesProductValue,rotatedFullValue,highFullValue]
    rw [pv,r4,h4,r6,h6,r10,h10,r32,h32]
  have dis := L.product_out_disjoint hnd
  have prod : regValue L.core.product out.basis=P :=
    (regValue_congr _ _ _ (fun q hq => f.2.2 q
      (List.disjoint_left.mp dis hq))).trans h.product
  refine ⟨f.1,prod,outv,?_⟩
  intro q hp ho
  exact (f.2.2 q ho).trans (h.frame q hp ho)

theorem PairClean.corePad (L : CuccaroStreamedSquareWideLayout)
    (base : BasisState) (h : PairClean L base) : regValue L.core.pad base=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  exact (regValue_zero _ _).mp h.pad q (by simp [foldPad,hq])

def branchAValue (A O : Nat) : Nat :=
  addRotateProductValue (A^2) (subModValue (A^2) O) false

def branchBValue (B O : Nat) : Nat :=
  subTimesProductValue (B^2) (addRotateProductValue (B^2) O false)

theorem branchA_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A O : Nat)
    (hA : regValue L.core.low base=A) (hAb : A<2^128)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.branchA
      (PairFrame L base 0 (branchAValue A O)) := by
  have lowLen := L.core.low_length hw.core
  have lowCount (q : Wire) : L.core.low.count q≤L.core.y.count q :=
    (List.take_sublist 128 L.core.y).count_le q
  have sqb : A^2<2^256 := by
    simpa only [show 2*128=256 by omega] using square_bound A 128 hAb
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let O1 := subModValue (A^2) O
  let O2 := addRotateProductValue (A^2) O1 false
  have sqT := L.square128_pair hw hnd L.core.low lowLen lowCount base A O hA
    (PairClean.corePad L base hc) hc.work hc.cin
  have subT := L.subSource_pair hw hnd (L.core.product.take 256)
    (L.productTake256_view hw) base (A^2) O (A^2) hO hc (by
      intro st hs
      rw [L.product_take_value hw st (A^2) hs.product 256 (by omega),
        Nat.mod_eq_of_lt sqb])
  have rotT := L.addRotate128_pair hw hnd false base (A^2) O1
    (Nat.mod_lt _ hp) hc
  have clrT := L.square128Clear_pair hw hnd L.core.low lowLen lowCount base A O2
    hA hAb hprod (PairClean.corePad L base hc) hc.work hc.cin
  intro s records hs
  let s1 := run (L.core.square128 L.core.low) [] s
  let s2 := run (L.subSource (L.core.product.take 256)) [] s1
  let s3 := run (L.addRotate128 false) [] s2
  let s4 := run (L.core.square128Clear L.core.low) records s3
  have e1 := sqT s [] hs
  have e2 := subT s1 [] e1.2
  have e3 := rotT s2 [] e2.2
  have e4 := clrT s3 records e3.2
  have sm := L.core.square128_counts hw.core L.core.low lowLen
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have subm : measurementCount (L.subSource (L.core.product.take 256))=0 := by
    simpa [subSource] using (cuccaroNormalizedModSub_counts
      (L.source (L.core.product.take 256)) 256 SquareReduction.c SquareReduction.p
      (L.source_widths hw _ p256)).2
  have rotm := L.rotate128_counts hw
  have exec : run L.branchA records s=s4 := by
    simp [branchA,s1,s2,s3,s4,run_append,sm.1.2,subm,rotm.1.2]
  rw [exec]
  exact ⟨e4.1.trans (e3.1.trans (e2.1.trans e1.1)),e4.2⟩

theorem branchB_prefix_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (B O : Nat)
    (hB : regValue L.core.high base=B)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O)
      (L.core.square128 L.core.high++L.addRotate128 false)
      (PairFrame L base (B^2) (addRotateProductValue (B^2) O false)) := by
  have highLen := L.core.high_length hw.core
  have highCount (q : Wire) : L.core.high.count q≤L.core.y.count q := by
    have h1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have h2 := (List.drop_sublist 128 L.core.y).count_le q
    simpa [CuccaroStreamedSquareLayout.high] using h1.trans h2
  have sqT := L.square128_pair hw hnd L.core.high highLen highCount base B O hB
    (PairClean.corePad L base hc) hc.work hc.cin
  have rotT := L.addRotate128_pair hw hnd false base (B^2) O hO hc
  intro s records hs
  let s1 := run (L.core.square128 L.core.high) [] s
  let s2 := run (L.addRotate128 false) records s1
  have e1 := sqT s [] hs
  have e2 := rotT s1 records e1.2
  have sm := L.core.square128_counts hw.core L.core.high highLen
  have exec : run (L.core.square128 L.core.high++L.addRotate128 false) records s=s2 := by
    simp [s1,s2,run_append,sm.1.2]
  rw [exec]
  exact ⟨e2.1.trans e1.1,e2.2⟩

private theorem padBit_mem (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.core.pad.getD 0 0∈L.core.pad := by
  have h : 0<L.core.pad.length := by rw [hw.core.pad]; omega
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem prepareSum_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B : Nat)
    (hA : regValue L.core.low base=A) (hB : regValue L.core.sum base=B)
    (hbound : A+B<2^129) (hpad : regValue L.core.pad base=0)
    (hcin : base L.core.cin=false) :
    Triple (SquareFrame L.core.sum base B) L.core.prepareSum
      (SquareFrame L.core.sum base (A+B)) := by
  let src := L.core.low++[L.core.pad.getD 0 0]
  have slen : src.length=129 := by simp [src,L.core.low_length hw.core]
  have dlen := L.core.sum_length hw.core
  have bit0 : base (L.core.pad.getD 0 0)=false :=
    (regValue_zero _ _).mp hpad _ (L.padBit_mem hw)
  have srcv : regValue src base=A := by
    rw [show src=L.core.low++[L.core.pad.getD 0 0] by rfl,
      regValue_append,hA]
    have hz : regValue [L.core.pad.getD 0 0] base=0 := by
      change (if base (L.core.pad.getD 0 0) then 1 else 0)=0
      rw [bit0]
      rfl
    rw [hz,Nat.mul_zero,Nat.add_zero]
  have nd : (L.core.cin::src++L.core.sum).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hnd q
    have hlo := (List.take_sublist 128 L.core.y).count_le q
    have hhi1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hhi2 := (List.drop_sublist 128 L.core.y).count_le q
    have hsplit := congrArg (List.count q) (List.take_append_drop 128 L.core.y)
    have hbit := (List.singleton_sublist.mpr (L.padBit_mem hw)).count_le q
    simp only [List.count_cons,List.count_nil,Nat.add_zero] at hbit
    simp only [List.count_append] at hsplit
    simp only [wires,CuccaroStreamedSquareLayout.wires,src,
      CuccaroStreamedSquareLayout.low,CuccaroStreamedSquareLayout.high,
      CuccaroStreamedSquareLayout.sum,List.count_append,List.count_cons,
      List.count_nil] at h ⊢
    omega
  have add := cuccaroAdd_cin_frame L.core.cin src L.core.sum nd
    (slen.trans dlen.symm) base false hcin B
  have val : (B+regValue src base+false.toNat)%2^L.core.sum.length=A+B := by
    rw [srcv]
    simp only [Bool.toNat_false,Nat.add_zero,dlen,Nat.mod_eq_of_lt (by omega),Nat.add_comm]
  rw [val] at add
  simpa only [CuccaroStreamedSquareLayout.prepareSum,src] using add

theorem clearSum_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B : Nat)
    (hA : regValue L.core.low base=A) (hB : regValue L.core.sum base=B)
    (hbound : A+B<2^129) (hpad : regValue L.core.pad base=0)
    (hcin : base L.core.cin=false) :
    Triple (SquareFrame L.core.sum base (A+B)) L.core.clearSum
      (SquareFrame L.core.sum base B) := by
  let src := L.core.low++[L.core.pad.getD 0 0]
  have nd : (L.core.cin::src++L.core.sum).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hnd q
    have hlo := (List.take_sublist 128 L.core.y).count_le q
    have hhi1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hhi2 := (List.drop_sublist 128 L.core.y).count_le q
    have hsplit := congrArg (List.count q) (List.take_append_drop 128 L.core.y)
    have hbit := (List.singleton_sublist.mpr (L.padBit_mem hw)).count_le q
    simp only [List.count_cons,List.count_nil,Nat.add_zero] at hbit
    simp only [List.count_append] at hsplit
    simp only [wires,CuccaroStreamedSquareLayout.wires,src,
      CuccaroStreamedSquareLayout.low,CuccaroStreamedSquareLayout.high,
      CuccaroStreamedSquareLayout.sum,List.count_append,List.count_cons,
      List.count_nil] at h ⊢
    omega
  have ftriple := L.prepareSum_frame hw hnd base A B hA hB hbound hpad hcin
  intro s records hs
  let z : State := ⟨s.phase,base⟩
  have zpre : SquareFrame L.core.sum base B z.basis := ⟨hB,fun _ _ => rfl⟩
  have f := ftriple z [] zpre
  let u := run L.core.prepareSum [] z
  have us : u=s := by
    have ph : u.phase=s.phase := f.1
    have bs : u.basis=s.basis := by
      funext q
      by_cases hq : q∈L.core.sum
      · exact (regValue_eq_iff L.core.sum u.basis s.basis).mp
          (f.2.1.trans hs.1.symm) q hq
      · exact (f.2.2 q hq).trans (hs.2 q hq).symm
    calc
      u = ⟨u.phase,u.basis⟩ := rfl
      _ = ⟨s.phase,s.basis⟩ := by rw [ph,bs]
      _ = s := rfl
  have rr := run_reverse_proper L.core.prepareSum
    (cuccaroAdd_proper src L.core.sum L.core.cin nd) z [] records
  change run L.core.clearSum records u=z at rr
  rw [us] at rr
  rw [rr]
  exact ⟨rfl,hB,fun _ _ => rfl⟩

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
