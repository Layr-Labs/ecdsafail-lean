import ECDSAAdd.Arithmetic.CuccaroMod
import ECDSAAdd.Math.ModInPlace

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic

structure CuccaroModValues (L : CuccaroModLayout)
    (A Z W : Nat) (C F : Bool) (s : BasisState) : Prop where
  a : regValue L.a s=A
  z : regValue L.z s=Z
  scratch : regValue L.scratch s=W
  cin : s L.cin=C
  flag : s L.flag=F

structure CuccaroModSplitValues (L : CuccaroModLayout)
    (A Z W : Nat) (H WH C F : Bool) (s : BasisState) : Prop where
  a : regValue L.a s=A
  low : regValue L.low s=Z
  high : s L.high=H
  work : regValue L.work s=W
  workHigh : s L.workHigh=WH
  cin : s L.cin=C
  flag : s L.flag=F

private theorem mod_subset_nodup (L : CuccaroModLayout) (hnd : L.wires.Nodup)
    (r : List Wire) (hr : ∀q,r.count q≤L.wires.count q) : r.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  exact (hr q).trans (List.nodup_iff_count.mp hnd q)

private theorem mod_disjoint (L : CuccaroModLayout) (hnd : L.wires.Nodup)
    (r t : List Wire) (_hr : ∀q,r.count q≤L.wires.count q)
    (_ht : ∀q,t.count q≤L.wires.count q)
    (hsep : ∀q,r.count q+t.count q≤L.wires.count q) : r.Disjoint t := by
  apply List.disjoint_left.mpr
  intro q hqr hqt
  have rpos := List.count_pos_iff.mpr hqr
  have tpos := List.count_pos_iff.mpr hqt
  have hall := List.nodup_iff_count.mp hnd q
  have hs := hsep q
  omega

private theorem split_at_high (v N : Nat) (J : Bool) (_hN : 0<N)
    (hv : v<2*N) (hJ : (N≤v ↔ J=true)) : v%N+N*J.toNat=v := by
  cases J with
  | false =>
    have hlt : v<N := Nat.lt_of_not_ge (fun h => by simpa using hJ.mp h)
    simp [Nat.mod_eq_of_lt hlt]
  | true =>
    have hge : N≤v := hJ.mpr rfl
    have hlt : v-N<N := by omega
    rw [Nat.mod_eq_sub_mod hge,Nat.mod_eq_of_lt hlt]
    simp
    omega

private theorem cuccaroMod_sum (L : CuccaroModLayout) (n A Z : Nat)
    (F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) :
    Triple (CuccaroModValues L A Z 0 false F)
      (cuccaroAdd L.a L.z L.cin)
      (CuccaroModValues L A ((A+Z)%2^(n+1)) 0 false F) := by
  have hz := L.z_length n hw
  have hsub : (L.cin::L.a++L.z).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have awayScratch (q : Wire) (hq : q∈L.scratch) : q∉L.z := by
    intro hzq
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hzq
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,List.count_append,
      List.count_cons,List.count_nil] at h
    omega
  have awayFlag : L.flag∉L.z := by
    intro hzq
    have h := List.nodup_iff_count.mp hnd L.flag
    have h2 := List.count_pos_iff.mpr hzq
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have flagOutside : L.flag∉L.cin::L.a++L.z := by
    intro hm
    have h := List.nodup_iff_count.mp hnd L.flag
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h h2
    omega
  intro s m h
  have runh := cuccaroAdd_correct L.a L.z L.cin hsub (hw.a.trans hz.symm) s m
  let out := run (cuccaroAdd L.a L.z L.cin) m s
  have scratchOut : regValue L.scratch out.basis=0 := by
    rw [← h.scratch]
    apply regValue_congr; intro q hq
    exact runh.2.2.2.2 q (by
      have ha : q∉L.a := by
        intro hqa
        have hn := List.nodup_iff_count.mp hnd q
        have h1 := List.count_pos_iff.mpr hq
        have h2 := List.count_pos_iff.mpr hqa
        simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,List.count_append] at hn
        omega
      have hc : q≠L.cin := by
        intro e; subst q
        have hn := List.nodup_iff_count.mp hnd L.cin
        have h1 := List.count_pos_iff.mpr hq
        simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,List.count_cons,
          List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn
        omega
      simp [hc,ha,awayScratch q hq])
  refine ⟨runh.1,?_⟩
  refine ⟨runh.2.1.trans h.a,?_,scratchOut,?_,?_⟩
  · rw [runh.2.2.2.1,h.a,h.z,h.cin,hz]
    rfl
  · exact runh.2.2.1.trans h.cin
  · exact (runh.2.2.2.2 L.flag flagOutside).trans h.flag

private theorem cuccaroMod_subZ (L : CuccaroModLayout) (n A Z W : Nat)
    (F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) :
    Triple (CuccaroModValues L A Z W false F) (cuccaroSub L.a L.z L.cin)
      (CuccaroModValues L A ((Z+2^(n+1)-A)%2^(n+1)) W false F) := by
  have hz := L.z_length n hw
  have hsub : (L.cin::L.a++L.z).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have outsideScratch (q : Wire) (hq : q∈L.scratch) : q∉L.cin::L.a++L.z := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at hn h2
    omega
  have outsideFlag : L.flag∉L.cin::L.a++L.z := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd L.flag
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn h2
    omega
  intro s m h
  have runh := cuccaroSub_correct L.a L.z L.cin hsub (hw.a.trans hz.symm) s m h.cin
  refine ⟨runh.1,⟨runh.2.1.trans h.a,?_,?_,runh.2.2.1,?_⟩⟩
  · rw [runh.2.2.2.1,h.z,h.a,hz]
  · rw [← h.scratch]; apply regValue_congr; intro q hq
    exact runh.2.2.2.2 q (outsideScratch q hq)
  · exact (runh.2.2.2.2 L.flag outsideFlag).trans h.flag

private theorem cuccaroMod_xorScratch (L : CuccaroModLayout) (A Z W p : Nat)
    (C F : Bool) (hnd : L.wires.Nodup) (hp : p<2^L.scratch.length) :
    Triple (CuccaroModValues L A Z W C F) (xorConstant L.scratch p)
      (CuccaroModValues L A Z (W ^^^ p) C F) := by
  have hs : L.scratch.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at h
    omega
  have outside (q : Wire) (hq : q∈L.a++L.z++[L.cin,L.flag]) : q∉L.scratch := by
    intro hsq
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hsq
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at h h1
    omega
  intro s m h
  obtain ⟨ph,fr,v⟩ := xorConstant_correct L.scratch hs p hp s m
  refine ⟨ph,⟨?_,?_,v.trans (congrArg (fun x => x ^^^ p) h.scratch),?_,?_⟩⟩
  · exact (regValue_congr _ _ _ (fun q hq => fr q (outside q (by simp [hq])))).trans h.a
  · exact (regValue_congr _ _ _ (fun q hq => fr q (outside q (by simp [hq])))).trans h.z
  · exact (fr L.cin (outside L.cin (by simp))).trans h.cin
  · exact (fr L.flag (outside L.flag (by simp))).trans h.flag

private theorem cuccaroMod_subScratch (L : CuccaroModLayout) (n A Z P : Nat)
    (F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) :
    Triple (CuccaroModValues L A Z P false F) (cuccaroSub L.scratch L.z L.cin)
      (CuccaroModValues L A ((Z+2^(n+1)-P)%2^(n+1)) P false F) := by
  have hz := L.z_length n hw
  have hs := L.scratch_length n hw
  have hsub : (L.cin::L.scratch++L.z).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have outsideA (q : Wire) (hq : q∈L.a) : q∉L.cin::L.scratch++L.z := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at hn h2
    omega
  have outsideFlag : L.flag∉L.cin::L.scratch++L.z := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd L.flag
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn h2
    omega
  intro s m h
  have runh := cuccaroSub_correct L.scratch L.z L.cin hsub (hs.trans hz.symm) s m h.cin
  let out := run (cuccaroSub L.scratch L.z L.cin) m s
  have keepA : regValue L.a out.basis=A := by
    rw [← h.a]
    apply regValue_congr; intro q hq
    exact runh.2.2.2.2 q (outsideA q hq)
  have keepFlag : out.basis L.flag=F := by
    exact (runh.2.2.2.2 L.flag outsideFlag).trans h.flag
  refine ⟨runh.1,⟨keepA,?_,runh.2.1.trans h.scratch,runh.2.2.1,keepFlag⟩⟩
  rw [runh.2.2.2.1,h.z,h.scratch,hz]

private theorem cuccaroMod_addScratch (L : CuccaroModLayout) (n A Z P : Nat)
    (F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) :
    Triple (CuccaroModValues L A Z P false F) (cuccaroAdd L.scratch L.z L.cin)
      (CuccaroModValues L A ((P+Z)%2^(n+1)) P false F) := by
  have hz := L.z_length n hw
  have hs := L.scratch_length n hw
  have hsub : (L.cin::L.scratch++L.z).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have outsideA (q : Wire) (hq : q∈L.a) : q∉L.cin::L.scratch++L.z := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at hn h2
    omega
  have outsideFlag : L.flag∉L.cin::L.scratch++L.z := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd L.flag
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn h2
    omega
  intro s m h
  have runh := cuccaroAdd_correct L.scratch L.z L.cin hsub (hs.trans hz.symm) s m
  refine ⟨runh.1,⟨?_,?_,runh.2.1.trans h.scratch,runh.2.2.1.trans h.cin,?_⟩⟩
  · rw [← h.a]; apply regValue_congr; intro q hq
    exact runh.2.2.2.2 q (outsideA q hq)
  · rw [runh.2.2.2.1,h.scratch,h.z,h.cin,hz]
    simp only [Bool.toNat_false,Nat.add_zero]
  · exact (runh.2.2.2.2 L.flag outsideFlag).trans h.flag

theorem cuccaroMod_reduce (L : CuccaroModLayout) (n A Z p : Nat)
    (F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) (hp : p<2^(n+1)) :
    Triple (CuccaroModValues L A Z 0 false F)
      (xorConstant L.scratch p++cuccaroSub L.scratch L.z L.cin++
        xorConstant L.scratch p)
      (CuccaroModValues L A ((Z+2^(n+1)-p)%2^(n+1)) 0 false F) := by
  have hs := L.scratch_length n hw
  have h1' := cuccaroMod_xorScratch L A Z 0 p false F hnd (by simpa [hs] using hp)
  have h1 : Triple (CuccaroModValues L A Z 0 false F) (xorConstant L.scratch p)
      (CuccaroModValues L A Z p false F) := by simpa using h1'
  have h2 := cuccaroMod_subScratch L n A Z p F hw hnd
  have h3' := cuccaroMod_xorScratch L A ((Z+2^(n+1)-p)%2^(n+1)) p p
    false F hnd (by simpa [hs] using hp)
  have h3 : Triple
      (CuccaroModValues L A ((Z+2^(n+1)-p)%2^(n+1)) p false F)
      (xorConstant L.scratch p)
      (CuccaroModValues L A ((Z+2^(n+1)-p)%2^(n+1)) 0 false F) := by
    simpa using h3'
  simpa using (h1.seq h2).seq h3

private theorem cuccaroMod_maskWork (L : CuccaroModLayout)
    (A Z W p : Nat) (H WH C F : Bool) (hnd : L.wires.Nodup)
    (hp : p<2^L.work.length) :
    Triple (CuccaroModSplitValues L A Z W H WH C F)
      (maskedConstant L.high L.work p)
      (CuccaroModSplitValues L A Z (W ^^^ if H then p else 0) H WH C F) := by
  have hn : L.work.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,List.count_cons,List.count_append,List.count_nil] at h
    omega
  have hc : L.high∉L.work := by
    intro hm
    have h := List.nodup_iff_count.mp hnd L.high
    have hp := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,CuccaroModLayout.z,List.count_cons,List.count_append,
      List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have outside (q : Wire) (hq : q∈L.a++L.low++[L.high,L.workHigh,L.cin,L.flag]) : q∉L.work := by
    intro hm
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,CuccaroModLayout.z,List.count_cons,List.count_append,
      List.count_nil] at h h1
    omega
  intro s m h
  obtain ⟨ph,fr,v⟩ := maskedConstant_correct L.high L.work p hn hc hp s m
  refine ⟨ph,⟨?_,?_,?_,?_,?_,?_,?_⟩⟩
  · exact (regValue_congr _ _ _ (fun q hq => fr q (outside q (by simp [hq])))).trans h.a
  · exact (regValue_congr _ _ _ (fun q hq => fr q (outside q (by simp [hq])))).trans h.low
  · exact (fr L.high (outside L.high (by simp))).trans h.high
  · rw [v,h.work,h.high]
  · exact (fr L.workHigh (outside L.workHigh (by simp))).trans h.workHigh
  · exact (fr L.cin (outside L.cin (by simp))).trans h.cin
  · exact (fr L.flag (outside L.flag (by simp))).trans h.flag

private theorem cuccaroMod_addLow (L : CuccaroModLayout) (n A Z W : Nat)
    (H WH F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) :
    Triple (CuccaroModSplitValues L A Z W H WH false F)
      (cuccaroAdd L.work L.low L.cin)
      (CuccaroModSplitValues L A ((Z+W)%2^n) W H WH false F) := by
  have hsub : (L.cin::L.work++L.low).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,CuccaroModLayout.z,List.count_cons,List.count_append,
      List.count_nil] at h ⊢
    omega
  have hlen := hw.work.trans hw.low.symm
  intro s m h
  have runh := cuccaroAdd_correct L.work L.low L.cin hsub hlen s m
  let out := run (cuccaroAdd L.work L.low L.cin) m s
  have outside (q : Wire) (hq : q∈L.a++[L.high,L.workHigh,L.flag]) :
      q∉L.cin::L.work++L.low := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,CuccaroModLayout.z,List.count_cons,List.count_append,
      List.count_nil] at hn h1 h2
    omega
  refine ⟨runh.1,⟨?_,?_,?_,runh.2.1.trans h.work,?_,
    runh.2.2.1.trans h.cin,?_⟩⟩
  · rw [← h.a]; apply regValue_congr; intro q hq
    exact runh.2.2.2.2 q (outside q (by simp [hq]))
  · rw [runh.2.2.2.1,h.work,h.low,h.cin,hw.low]
    simp only [Bool.toNat_false,Nat.add_zero,Nat.add_comm]
  · exact (runh.2.2.2.2 L.high (outside L.high (by simp))).trans h.high
  · exact (runh.2.2.2.2 L.workHigh (outside L.workHigh (by simp))).trans h.workHigh
  · exact (runh.2.2.2.2 L.flag (outside L.flag (by simp))).trans h.flag

theorem cuccaroMod_addback (L : CuccaroModLayout) (n A Z p : Nat)
    (B F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup)
    (_hZ : Z<2^n) (hp : p<2^n) :
    Triple (CuccaroModSplitValues L A Z 0 B false false F)
      (maskedConstant L.high L.work p++cuccaroAdd L.work L.low L.cin++
        maskedConstant L.high L.work p)
      (CuccaroModSplitValues L A ((Z+(if B then p else 0))%2^n) 0
        B false false F) := by
  have h1' := cuccaroMod_maskWork L A Z 0 p B false false F hnd (by simpa [hw.work] using hp)
  have h1 : Triple (CuccaroModSplitValues L A Z 0 B false false F)
      (maskedConstant L.high L.work p)
      (CuccaroModSplitValues L A Z (if B then p else 0) B false false F) := by
    simpa using h1'
  have h2 := cuccaroMod_addLow L n A Z (if B then p else 0) B false F hw hnd
  have h3' := cuccaroMod_maskWork L A ((Z+(if B then p else 0))%2^n)
    (if B then p else 0) p B false false F hnd (by simpa [hw.work] using hp)
  have h3 : Triple
      (CuccaroModSplitValues L A ((Z+(if B then p else 0))%2^n)
        (if B then p else 0) B false false F)
      (maskedConstant L.high L.work p)
      (CuccaroModSplitValues L A ((Z+(if B then p else 0))%2^n) 0
        B false false F) := by
    cases B <;> simpa using h3'
  simpa using (h1.seq h2).seq h3

private theorem cuccaroMod_copyLowToWork (L : CuccaroModLayout) (n A R : Nat)
    (B C F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) (hR : R<2^n) :
    Triple (CuccaroModValues L A (R+2^n*B.toNat) 0 C F)
      (copyRegister none L.low L.work)
      (CuccaroModValues L A (R+2^n*B.toNat) R C F) ∧
    Triple (CuccaroModValues L A (R+2^n*B.toNat) R C F)
      (copyRegister none L.low L.work)
      (CuccaroModValues L A (R+2^n*B.toNat) 0 C F) := by
  have hlen := hw.low.trans hw.work.symm
  have hcopy : (L.low++L.work).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,CuccaroModLayout.z,List.count_cons,List.count_append,
      List.count_nil] at h ⊢
    omega
  have outside (q : Wire) (hq : q∈L.a++[L.high,L.workHigh,L.cin,L.flag]) : q∉L.work := by
    intro hm
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,CuccaroModLayout.z,List.count_cons,List.count_append,
      List.count_nil] at h h1
    omega
  have outsideZ (q : Wire) (hq : q∈L.z) : q∉L.work := by
    intro hm
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,List.count_cons,List.count_append,List.count_nil] at h
    omega
  have one (W W' : Nat) (hW : W<2^n) (hxor : W' = W ^^^ R) :
      Triple (CuccaroModValues L A (R+2^n*B.toNat) W C F)
        (copyRegister none L.low L.work)
        (CuccaroModValues L A (R+2^n*B.toNat) W' C F) := by
    intro s m h
    have lowv : regValue L.low s.basis=R := by
      rw [regValue_low L.low L.high,← CuccaroModLayout.z,h.z,hw.low,Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hR]
    have wh0 : s.basis L.workHigh=false := by
      have hb := regValue_highBit L.work L.workHigh s.basis
      rw [← CuccaroModLayout.scratch,h.scratch] at hb
      cases hwv : s.basis L.workHigh
      · rfl
      · have hh := hb.mp hwv
        rw [hw.work] at hh
        omega
    have workv : regValue L.work s.basis=W := by
      have hs := regValue_append L.work [L.workHigh] s.basis
      rw [← CuccaroModLayout.scratch,h.scratch] at hs
      have hsingle : regValue [L.workHigh] s.basis=0 := by simp [regValue,wh0]
      rw [hsingle] at hs
      simp only [Nat.mul_zero,Nat.add_zero] at hs
      exact hs.symm
    obtain ⟨ph,fr,v⟩ := copyRegister_correct none L.low L.work hlen hcopy (by simp) s m
    have workHigh : (run (copyRegister none L.low L.work) m s).basis L.workHigh=
        s.basis L.workHigh := fr L.workHigh (by
      intro hm
      have hn := List.nodup_iff_count.mp hnd L.workHigh
      have hp := List.count_pos_iff.mpr hm
      simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
        CuccaroModLayout.scratch,List.count_cons,List.count_append,List.count_nil,
        beq_self_eq_true,if_true] at hn
      omega)
    refine ⟨ph,⟨?_,?_,?_,?_,?_⟩⟩
    · exact (regValue_congr _ _ _ (fun q hq => fr q (outside q (by simp [hq])))).trans h.a
    · exact (regValue_congr _ _ _ (fun q hq => fr q (outsideZ q hq))).trans h.z
    · rw [CuccaroModLayout.scratch,regValue_append,v,lowv]
      have hbout : (run (copyRegister none L.low L.work) m s).basis L.workHigh=false :=
        workHigh.trans wh0
      have hsingle : regValue [L.workHigh]
          (run (copyRegister none L.low L.work) m s).basis=0 := by simp [regValue,hbout]
      rw [hsingle,workv]
      simp [copyValue,hxor]
    · exact (fr L.cin (outside L.cin (by simp))).trans h.cin
    · exact (fr L.flag (outside L.flag (by simp))).trans h.flag
  constructor
  · exact one 0 R (Nat.two_pow_pos n) (by simp)
  · exact one R 0 hR (by simp [Nat.xor_self])

private theorem cuccaroMod_subAWork (L : CuccaroModLayout) (n A Z W : Nat)
    (F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) :
    Triple (CuccaroModValues L A Z W false F) (cuccaroSub L.a L.scratch L.cin)
      (CuccaroModValues L A Z ((W+2^(n+1)-A)%2^(n+1)) false F) := by
  have hs := L.scratch_length n hw
  have hsub : (L.cin::L.a++L.scratch).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have outsideZ (q : Wire) (hq : q∈L.z) : q∉L.cin::L.a++L.scratch := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at hn h2
    omega
  have outsideFlag : L.flag∉L.cin::L.a++L.scratch := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd L.flag
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn h2
    omega
  intro s m h
  have runh := cuccaroSub_correct L.a L.scratch L.cin hsub (hw.a.trans hs.symm) s m h.cin
  let out := run (cuccaroSub L.a L.scratch L.cin) m s
  have keepZ : regValue L.z out.basis=Z := by
    rw [← h.z]; apply regValue_congr; intro q hq
    exact runh.2.2.2.2 q (outsideZ q hq)
  have keepFlag : out.basis L.flag=F := by
    exact (runh.2.2.2.2 L.flag outsideFlag).trans h.flag
  refine ⟨runh.1,⟨runh.2.1.trans h.a,keepZ,?_,runh.2.2.1,keepFlag⟩⟩
  rw [runh.2.2.2.1,h.scratch,h.a,hs]

private theorem cuccaroMod_addAWork (L : CuccaroModLayout) (n A Z W : Nat)
    (F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) :
    Triple (CuccaroModValues L A Z W false F) (cuccaroAdd L.a L.scratch L.cin)
      (CuccaroModValues L A Z ((A+W)%2^(n+1)) false F) := by
  have hs := L.scratch_length n hw
  have hsub : (L.cin::L.a++L.scratch).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have outsideZ (q : Wire) (hq : q∈L.z) : q∉L.cin::L.a++L.scratch := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil] at hn h2
    omega
  have outsideFlag : L.flag∉L.cin::L.a++L.scratch := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd L.flag
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn h2
    omega
  intro s m h
  have runh := cuccaroAdd_correct L.a L.scratch L.cin hsub (hw.a.trans hs.symm) s m
  let out := run (cuccaroAdd L.a L.scratch L.cin) m s
  have keepZ : regValue L.z out.basis=Z := by
    rw [← h.z]; apply regValue_congr; intro q hq
    exact runh.2.2.2.2 q (outsideZ q hq)
  have keepFlag : out.basis L.flag=F := by
    exact (runh.2.2.2.2 L.flag outsideFlag).trans h.flag
  refine ⟨runh.1,⟨runh.2.1.trans h.a,keepZ,?_,runh.2.2.1.trans h.cin,keepFlag⟩⟩
  rw [runh.2.2.2.1,h.a,h.scratch,h.cin,hs]
  simp only [Bool.toNat_false,Nat.add_zero]

private theorem cuccaroMod_clearHigh (L : CuccaroModLayout) (n A R V : Nat)
    (B P F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup)
    (hR : R<2^n) (hB : B=!P)
    (hP : (2^n≤V ↔ P=true)) :
    Triple (CuccaroModValues L A (R+2^n*B.toNat) V false F)
      [.CX L.workHigh L.high,.X L.high]
      (CuccaroModValues L A R V false F) := by
  have hwh : L.workHigh≠L.high := by
    intro e
    have h := List.nodup_iff_count.mp hnd L.high
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,CuccaroModLayout.z,List.count_cons,List.count_append,
      List.count_nil,beq_self_eq_true,if_true] at h
    simp [e] at h
    omega
  intro s m h
  have hb : s.basis L.high=B := by
    have hh := regValue_highBit L.low L.high s.basis
    rw [← CuccaroModLayout.z,h.z,hw.low] at hh
    cases B with
    | false =>
      cases hsbit : s.basis L.high
      · rfl
      · have hv := hh.mp hsbit
        simp at hv
        omega
    | true =>
      cases hsbit : s.basis L.high
      · have hv : 2^n≤R+2^n := by omega
        have hv' : 2^n≤R+2^n*true.toNat := by
          simpa only [Bool.toNat_true,Nat.mul_one] using hv
        have := hh.mpr hv'
        simp_all
      · rfl
  have hwb : s.basis L.workHigh=P := by
    have hh := regValue_highBit L.work L.workHigh s.basis
    rw [← CuccaroModLayout.scratch,h.scratch,hw.work] at hh
    cases P with
    | false =>
      cases hsbit : s.basis L.workHigh
      · rfl
      · have hv := hP.mp (hh.mp hsbit)
        simp at hv
    | true =>
      cases hsbit : s.basis L.workHigh
      · have hv := hh.mpr (hP.mpr rfl)
        simp_all
      · rfl
  let out := run [.CX L.workHigh L.high,.X L.high] m s
  have high0 : out.basis L.high=false := by
    dsimp [out]
    simp only [run]
    cases P <;> simp_all [writeBit]
  have keep (q : Wire) (hq : q≠L.high) : out.basis q=s.basis q := by
    dsimp [out]
    simp [run,writeBit,hq]
  refine ⟨rfl,⟨?_,?_,?_,?_,?_⟩⟩
  · rw [← h.a]; apply regValue_congr; intro q hq
    apply keep q
    intro e; subst q
    have hn := List.nodup_iff_count.mp hnd L.high
    have hp := List.count_pos_iff.mpr hq
    simp only [CuccaroModLayout.wires,CuccaroModLayout.z,List.count_cons,List.count_append,
      List.count_nil,beq_self_eq_true,if_true] at hn
    omega
  · rw [CuccaroModLayout.z,regValue_append]
    have lowSame : regValue L.low out.basis=regValue L.low s.basis := by
      apply regValue_congr; intro q hq
      apply keep q
      intro e; subst q
      have hn := List.nodup_iff_count.mp hnd L.high
      have hp := List.count_pos_iff.mpr hq
      simp only [CuccaroModLayout.wires,CuccaroModLayout.z,List.count_cons,List.count_append,
        List.count_nil,beq_self_eq_true,if_true] at hn
      omega
    rw [lowSame]
    have hsingle : regValue [L.high] out.basis=0 := by simp [regValue,high0]
    rw [hsingle]
    have lowv := regValue_low L.low L.high s.basis
    rw [← CuccaroModLayout.z,h.z,hw.low,Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hR] at lowv
    simp [lowv]
  · have outsideScratch (q : Wire) (hq : q∈L.scratch) : q≠L.high := by
      intro e
      subst q
      have hn := List.nodup_iff_count.mp hnd L.high
      have hp := List.count_pos_iff.mpr hq
      simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
        CuccaroModLayout.scratch,CuccaroModLayout.z,List.count_cons,
        List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn hp
      omega
    rw [← h.scratch]; apply regValue_congr; intro q hq
    exact keep q (outsideScratch q hq)
  · exact (keep L.cin (by
      intro e
      have hn := List.nodup_iff_count.mp hnd L.high
      simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,CuccaroModLayout.z,
        List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn
      simp [e] at hn
      omega)).trans h.cin
  · exact (keep L.flag (by
      intro e
      have hn := List.nodup_iff_count.mp hnd L.high
      simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,CuccaroModLayout.z,
        List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn
      simp [e] at hn
      omega)).trans h.flag

private theorem cuccaroMod_moveHighToFlag (L : CuccaroModLayout) (n A R W : Nat)
    (K : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) (hR : R<2^n) :
    Triple (CuccaroModValues L A (R+2^n*K.toNat) W false false)
      [.CX L.high L.flag,.CX L.flag L.high]
      (CuccaroModValues L A R W false K) := by
  have hhf : L.high≠L.flag := by
    intro e
    have hn := List.nodup_iff_count.mp hnd L.high
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,CuccaroModLayout.z,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn
    simp [e] at hn
    omega
  intro s m h
  have highK : s.basis L.high=K := by
    have hb := regValue_highBit L.low L.high s.basis
    rw [← CuccaroModLayout.z,h.z,hw.low] at hb
    cases K with
    | false =>
      cases hv : s.basis L.high
      · rfl
      · have := hb.mp hv; simp at this; omega
    | true =>
      cases hv : s.basis L.high
      · have ht : 2^n≤R+2^n := by omega
        have ht' : 2^n≤R+2^n*true.toNat := by
          simpa only [Bool.toNat_true,Nat.mul_one] using ht
        have := hb.mpr ht'
        simp_all
      · rfl
  let out := run [.CX L.high L.flag,.CX L.flag L.high] m s
  have bits : out.basis L.high=false ∧ out.basis L.flag=K := by
    dsimp [out]
    cases K <;> simp_all [run,writeBit,h.flag,Ne.symm hhf]
  have keep (q : Wire) (hq : q≠L.high) (hf : q≠L.flag) : out.basis q=s.basis q := by
    dsimp [out]
    simp [run,writeBit,hq,hf]
  have away (r : List Wire) (hr : ∀q∈r,q≠L.high ∧ q≠L.flag) :
      regValue r out.basis=regValue r s.basis := regValue_congr _ _ _ (fun q hq =>
        keep q (hr q hq).1 (hr q hq).2)
  have safe (q : Wire) (hq : q∈L.a++L.low++L.scratch++[L.cin]) :
      q≠L.high ∧ q≠L.flag := by
    constructor <;> intro e
    · subst q
      have hn := List.nodup_iff_count.mp hnd L.high
      have hp := List.count_pos_iff.mpr hq
      simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
        CuccaroModLayout.scratch,CuccaroModLayout.z,List.count_cons,List.count_append,
        List.count_nil,beq_self_eq_true,if_true] at hn hp
      omega
    · subst q
      have hn := List.nodup_iff_count.mp hnd L.flag
      have hp := List.count_pos_iff.mpr hq
      simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
        CuccaroModLayout.scratch,CuccaroModLayout.z,List.count_cons,List.count_append,
        List.count_nil,beq_self_eq_true,if_true] at hn hp
      omega
  refine ⟨rfl,⟨(away L.a (fun q hq => safe q (by simp [hq]))).trans h.a,?_,
    (away L.scratch (fun q hq => safe q (by simp [hq]))).trans h.scratch,?_,bits.2⟩⟩
  · rw [CuccaroModLayout.z,regValue_append]
    have lowSame := away L.low (fun q hq => safe q (by simp [hq]))
    have lowv := regValue_low L.low L.high s.basis
    rw [← CuccaroModLayout.z,h.z,hw.low,Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hR] at lowv
    have hsingle : regValue [L.high] out.basis=0 := by simp [regValue,bits.1]
    rw [lowSame,lowv,hsingle]
    simp
  · exact (keep L.cin (safe L.cin (by simp)).1 (safe L.cin (by simp)).2).trans h.cin

private theorem cuccaroMod_clearFlag (L : CuccaroModLayout) (n A D W : Nat)
    (J K : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup)
    (hD : D<2^n) (hK : K=!J) :
    Triple (CuccaroModValues L A (D+2^n*J.toNat) W false K)
      [.X L.flag,.CX L.high L.flag]
      (CuccaroModValues L A (D+2^n*J.toNat) W false false) := by
  have hhf : L.high≠L.flag := by
    intro e
    have hn := List.nodup_iff_count.mp hnd L.high
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,CuccaroModLayout.z,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn
    simp [e] at hn
    omega
  intro s m h
  have highJ : s.basis L.high=J := by
    have hb := regValue_highBit L.low L.high s.basis
    rw [← CuccaroModLayout.z,h.z,hw.low] at hb
    cases J with
    | false =>
      cases hv : s.basis L.high
      · rfl
      · have := hb.mp hv; simp at this; omega
    | true =>
      cases hv : s.basis L.high
      · have ht : 2^n≤D+2^n := by omega
        have ht' : 2^n≤D+2^n*true.toNat := by
          simpa only [Bool.toNat_true,Nat.mul_one] using ht
        have := hb.mpr ht'
        simp_all
      · rfl
  let out := run [.X L.flag,.CX L.high L.flag] m s
  have flag0 : out.basis L.flag=false := by
    dsimp [out]
    cases J with
    | false =>
      have hk : K=true := by simpa using hK
      rw [hk] at h
      simp [run,writeBit,h.flag,highJ,hhf]
    | true =>
      have hk : K=false := by simpa using hK
      rw [hk] at h
      simp [run,writeBit,h.flag,highJ,hhf]
  have keep (q : Wire) (hq : q≠L.flag) : out.basis q=s.basis q := by
    dsimp [out]
    simp [run,writeBit,hq]
  have away (r : List Wire) (hr : ∀q∈r,q≠L.flag) :
      regValue r out.basis=regValue r s.basis := regValue_congr _ _ _ (fun q hq => keep q (hr q hq))
  have safe (q : Wire) (hq : q∈L.a++L.z++L.scratch++[L.cin]) : q≠L.flag := by
    intro e; subst q
    have hn := List.nodup_iff_count.mp hnd L.flag
    have hp := List.count_pos_iff.mpr hq
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,CuccaroModLayout.z,List.count_cons,
      List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn hp
    omega
  exact ⟨rfl,⟨(away L.a (fun q hq => safe q (by simp [hq]))).trans h.a,
    (away L.z (fun q hq => safe q (by simp [hq]))).trans h.z,
    (away L.scratch (fun q hq => safe q (by simp [hq]))).trans h.scratch,
    (keep L.cin (safe L.cin (by simp))).trans h.cin,flag0⟩⟩

theorem cuccaroMod_finishAdd (L : CuccaroModLayout) (n A R : Nat)
    (B F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup)
    (hA : A<2^n) (hR : R<2^n) (hB : B=!decide (R<A)) :
    Triple (CuccaroModValues L A (R+2^n*B.toNat) 0 false F)
      (copyRegister none L.low L.work++cuccaroSub L.a L.scratch L.cin++
        [.CX L.workHigh L.high,.X L.high]++cuccaroAdd L.a L.scratch L.cin++
        copyRegister none L.low L.work)
      (CuccaroModValues L A R 0 false F) := by
  let V := (R+2^(n+1)-A)%2^(n+1)
  let P := decide (R<A)
  have cp := cuccaroMod_copyLowToWork L n A R B false F hw hnd hR
  have cp0 := cuccaroMod_copyLowToWork L n A R false false F hw hnd hR
  have hs := cuccaroMod_subAWork L n A (R+2^n*B.toNat) R F hw hnd
  have hVP : 2^n≤V ↔ P=true := by
    dsimp [V,P]
    rw [Nat.pow_succ]
    by_cases h : R<A
    · simp only [h,decide_true]
      have he : R+2^n*2-A=(R+2^n-A)+2^n := by omega
      have hv : R+2^n*2-A<2^n*2 := by omega
      have hu : R+2^n-A<2^n := by omega
      rw [Nat.mod_eq_of_lt hv,he]
      constructor
      · intro _; trivial
      · intro _; omega
    · simp only [h,decide_false,Bool.false_eq_true,iff_false]
      have he : R+2^n*2-A=(R-A)+2^n*2 := by omega
      rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
      omega
  have hc := cuccaroMod_clearHigh L n A R V B P F hw hnd hR
    (by simpa [P] using hB) hVP
  have ha0 := cuccaroMod_addAWork L n A R V F hw hnd
  have restore : (A+V)%2^(n+1)=R := by
    dsimp [V]
    rw [Nat.pow_succ]
    by_cases h : R<A
    · have hv : R+2^n*2-A<2^n*2 := by omega
      rw [Nat.mod_eq_of_lt hv]
      have he : A+(R+2^n*2-A)=R+2^n*2 := by omega
      rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : R<2^n*2)]
    · have he : R+2^n*2-A=(R-A)+2^n*2 := by omega
      rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : R-A<2^n*2)]
      have : A+(R-A)=R := by omega
      rw [this,Nat.mod_eq_of_lt (by omega : R<2^n*2)]
  have ha : Triple (CuccaroModValues L A R V false F)
      (cuccaroAdd L.a L.scratch L.cin) (CuccaroModValues L A R R false F) := by
    simpa [restore] using ha0
  have cpClear : Triple (CuccaroModValues L A R R false F)
      (copyRegister none L.low L.work) (CuccaroModValues L A R 0 false F) := by
    simpa using cp0.2
  simpa [V,List.append_assoc] using ((((cp.1.seq hs).seq hc).seq ha).seq cpClear)

theorem cuccaroModAdd_spec (L : CuccaroModLayout) (n p A Z : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hp : 0<p) (hpn : p<2^n)
    (hA : A<p) (hZ : Z<p) :
    Triple (CuccaroModValues L A Z 0 false false) (cuccaroModAdd L p)
      (CuccaroModValues L A ((A+Z)%p) 0 false false) := by
  have hn : 0<n := by
    by_contra h
    have : n=0 := by omega
    rw [this] at hpn
    simp at hpn
    omega
  have hsum : A+Z<2^(n+1) := by rw [Nat.pow_succ]; omega
  have hwide : p<2^(n+1) := by rw [Nat.pow_succ]; omega
  let D := (A+Z+2^(n+1)-p)%2^(n+1)
  let R := (A+Z)%p
  let B := decide (A+Z<p)
  have hfirst0 := (cuccaroMod_sum L n A Z false hw hnd).seq
    (cuccaroMod_reduce L n A ((A+Z)%2^(n+1)) p false hw hnd hwide)
  have hfirst : Triple (CuccaroModValues L A Z 0 false false)
      (cuccaroAdd L.a L.z L.cin++
        (xorConstant L.scratch p++cuccaroSub L.scratch L.z L.cin++
          xorConstant L.scratch p))
      (CuccaroModValues L A D 0 false false) := by
    simpa [D,Nat.mod_eq_of_lt hsum] using hfirst0
  have hlow := modAddCore_low (A+Z) p n hp hpn (by omega)
  have hborrow := (addReduction (A+Z) p n hp hpn (by omega)).1
  have hlast : B=!decide (R<A) := by
    have hh := modAddCore_cleanup A Z p (by omega) hZ
    dsimp [B,R]
    by_cases h : A+Z<p
    · have hh' := hh.mp h
      simp [h,Nat.not_lt.mpr hh']
    · have hh' : ¬A≤(A+Z)%p := fun he => h (hh.mpr he)
      simp [h,Nat.lt_of_not_ge hh']
  have hadd := cuccaroMod_addback L n A (D%2^n) p B false hw hnd
    (Nat.mod_lt _ (Nat.two_pow_pos _)) hpn
  have hfinish := cuccaroMod_finishAdd L n A R B false hw hnd
    (hA.trans hpn) ((Nat.mod_lt _ hp).trans hpn) hlast
  have hrest : Triple (CuccaroModValues L A D 0 false false)
      (maskedConstant L.high L.work p++cuccaroAdd L.work L.low L.cin++
        maskedConstant L.high L.work p++
        (copyRegister none L.low L.work++cuccaroSub L.a L.scratch L.cin++
          [.CX L.workHigh L.high,.X L.high]++cuccaroAdd L.a L.scratch L.cin++
          copyRegister none L.low L.work))
      (CuccaroModValues L A R 0 false false) := by
    have middle : Triple (CuccaroModValues L A D 0 false false)
        (maskedConstant L.high L.work p++cuccaroAdd L.work L.low L.cin++
          maskedConstant L.high L.work p)
        (CuccaroModValues L A (R+2^n*B.toNat) 0 false false) := by
      apply hadd.conseq
      · intro st h
        have lowv : regValue L.low st=D%2^n := by
          rw [regValue_low L.low L.high,← CuccaroModLayout.z,h.z,hw.low]
        have highv : st L.high=B := by
          have hh := regValue_highBit L.low L.high st
          rw [← CuccaroModLayout.z,h.z,hw.low] at hh
          have he : st L.high=true ↔ A+Z<p := hh.trans hborrow
          cases hv : st L.high
          · have hf : ¬A+Z<p := fun ht => by simpa [hv] using he.mpr ht
            simp [B,hf]
          · have ht := he.mp hv
            simp [B,ht]
        have clean := (regValue_zero L.scratch st).mp h.scratch
        have workv : regValue L.work st=0 := (regValue_zero _ _).mpr
          (fun q hq => clean q (by simp [CuccaroModLayout.scratch,hq]))
        have whv : st L.workHigh=false := clean L.workHigh (by simp [CuccaroModLayout.scratch])
        exact ⟨h.a,lowv,highv,workv,whv,h.cin,h.flag⟩
      · intro st h
        have he : (D%2^n+(if B then p else 0))%2^n=R := by
          simpa [D,B,R] using hlow
        have zeq : regValue L.z st=R+2^n*B.toNat := by
          have hhigh : regValue [L.high] st=B.toNat := by
            change (if st L.high then 1 else 0)=B.toNat
            rw [h.high]
            cases B <;> rfl
          rw [CuccaroModLayout.z,regValue_append,h.low,hhigh,hw.low,he]
        have seq : regValue L.scratch st=0 := by
          have hhigh : regValue [L.workHigh] st=0 := by simp [regValue,h.workHigh]
          rw [CuccaroModLayout.scratch,regValue_append,h.work,hhigh]
          simp
        exact ⟨h.a,zeq,seq,h.cin,h.flag⟩
    exact middle.seq hfinish
  simpa [cuccaroModAdd,D,R,List.append_assoc] using hfirst.seq hrest

theorem cuccaroModSub_spec (L : CuccaroModLayout) (n p A Z : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hp : 0<p) (hpn : p<2^n)
    (hA : A<p) (hZ : Z<p) :
    Triple (CuccaroModValues L A Z 0 false false) (cuccaroModSub L p)
      (CuccaroModValues L A ((Z+p-A)%p) 0 false false) := by
  have hn : 0<n := by
    by_contra h
    have he : n=0 := by omega
    rw [he] at hpn
    simp at hpn
    omega
  let N := 2^n
  let M := 2^(n+1)
  let D := (Z+M-A)%M
  let K := decide (Z<A)
  let R := (Z+p-A)%p
  have hNM : M=2*N := by simp [M,N,Nat.pow_succ,Nat.mul_comm]
  have hDlt : D<2*N := by
    rw [← hNM]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hDhi : N≤D ↔ K=true := by
    dsimp [D,K,M,N]
    rw [Nat.pow_succ]
    by_cases h : Z<A
    · simp only [h,decide_true]
      have hv : Z+2^n*2-A<2^n*2 := by omega
      have he : Z+2^n*2-A=(Z+2^n-A)+2^n := by omega
      rw [Nat.mod_eq_of_lt hv,he]
      constructor
      · intro _; trivial
      · intro _; omega
    · simp only [h,decide_false,Bool.false_eq_true,iff_false]
      have he : Z+2^n*2-A=(Z-A)+2^n*2 := by omega
      rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
      omega
  have hlow : (D%N+(if K then p else 0))%N=R := by
    dsimp [D,K,R,M,N]
    rw [Nat.pow_succ]
    by_cases h : Z<A
    · simp only [h,decide_true,if_true]
      have hv : Z+2^n*2-A<2^n*2 := by omega
      have he : Z+2^n*2-A=(Z+2^n-A)+2^n := by omega
      have hu : Z+2^n-A<2^n := by omega
      rw [Nat.mod_eq_of_lt hv,he,Nat.add_mod_right,Nat.mod_eq_of_lt hu]
      have hzpa : Z+p-A<p := by omega
      have he2 : Z+2^n-A+p=(Z+p-A)+2^n := by omega
      rw [he2,Nat.add_mod_right,Nat.mod_eq_of_lt (hzpa.trans hpn),
        Nat.mod_eq_of_lt hzpa]
    · simp [h]
      have he : Z+2^n*2-A=(Z-A)+2^n*2 := by omega
      have hza : Z-A<2^n := by omega
      rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hza]
      have he2 : Z+p-A=(Z-A)+p := by omega
      rw [he2,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : Z-A<p)]
  have hinit := cuccaroMod_subZ L n A Z 0 false hw hnd
  have hadd0 := cuccaroMod_addback L n A (D%N) p K false hw hnd
    (Nat.mod_lt _ (Nat.two_pow_pos _)) (by simpa [N] using hpn)
  have hmid : Triple (CuccaroModValues L A D 0 false false)
      (maskedConstant L.high L.work p++cuccaroAdd L.work L.low L.cin++
        maskedConstant L.high L.work p)
      (CuccaroModValues L A (R+N*K.toNat) 0 false false) := by
    apply hadd0.conseq
    · intro st h
      have lowv : regValue L.low st=D%N := by
        rw [regValue_low L.low L.high,← CuccaroModLayout.z,h.z,hw.low]
      have highv : st L.high=K := by
        have hh := regValue_highBit L.low L.high st
        rw [← CuccaroModLayout.z,h.z,hw.low] at hh
        cases hs : st L.high <;> cases hk : K
        · rfl
        · have := hh.mpr (hDhi.mpr hk); simp_all
        · have := hDhi.mp (hh.mp hs); simp_all
        · rfl
      have clean := (regValue_zero L.scratch st).mp h.scratch
      exact ⟨h.a,lowv,highv,
        (regValue_zero _ _).mpr (fun q hq => clean q (by simp [CuccaroModLayout.scratch,hq])),
        clean L.workHigh (by simp [CuccaroModLayout.scratch]),h.cin,h.flag⟩
    · intro st h
      have highv : regValue [L.high] st=K.toNat := by
        change (if st L.high then 1 else 0)=K.toNat
        rw [h.high]
        cases K <;> rfl
      have zval : regValue L.z st=R+N*K.toNat := by
        rw [CuccaroModLayout.z,regValue_append,h.low,highv,hw.low,hlow]
      have whv : regValue [L.workHigh] st=0 := by simp [regValue,h.workHigh]
      have wval : regValue L.scratch st=0 := by
        rw [CuccaroModLayout.scratch,regValue_append,h.work,whv]
        simp
      exact ⟨h.a,zval,wval,h.cin,h.flag⟩
  have hmove0 := cuccaroMod_moveHighToFlag L n A R 0 K hw hnd
    (lt_trans (Nat.mod_lt _ hp) hpn)
  have hmove : Triple (CuccaroModValues L A (R+N*K.toNat) 0 false false)
      [.CX L.high L.flag,.CX L.flag L.high]
      (CuccaroModValues L A R 0 false K) := by simpa [N] using hmove0
  let T := A+R
  have hRlt : R<p := Nat.mod_lt _ hp
  have hTlt : T<2^(n+1) := by rw [Nat.pow_succ]; dsimp [T]; omega
  have hsum0 := cuccaroMod_sum L n A R K hw hnd
  have hsum : Triple (CuccaroModValues L A R 0 false K)
      (cuccaroAdd L.a L.z L.cin) (CuccaroModValues L A T 0 false K) := by
    simpa [T,Nat.mod_eq_of_lt hTlt] using hsum0
  have tEq : T=Z+K.toNat*p := by
    dsimp [T,R,K]
    by_cases h : Z<A
    · simp only [h,decide_true,Bool.toNat_true,Nat.one_mul]
      have hzpa : Z+p-A<p := by omega
      rw [Nat.mod_eq_of_lt hzpa]
      omega
    · simp only [h,decide_false,Bool.toNat_false,Nat.zero_mul,Nat.add_zero]
      have he : Z+p-A=(Z-A)+p := by omega
      rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
      omega
  have load0 := cuccaroMod_xorScratch L A T 0 p false K hnd
    (by simpa [L.scratch_length n hw] using (lt_trans hpn (by rw [Nat.pow_succ]; omega)))
  have load : Triple (CuccaroModValues L A T 0 false K) (xorConstant L.scratch p)
      (CuccaroModValues L A T p false K) := by simpa using load0
  let E := (T+2^(n+1)-p)%2^(n+1)
  have htrial := cuccaroMod_subScratch L n A T p K hw hnd
  have htrial' : Triple (CuccaroModValues L A T p false K)
      (cuccaroSub L.scratch L.z L.cin) (CuccaroModValues L A E p false K) := by
    simpa [E] using htrial
  let J := decide (T<p)
  have hEborrow : 2^n≤E ↔ J=true := by
    dsimp [E,J]
    simpa using (addReduction T p n hp hpn (by dsimp [T]; omega)).1
  have hKJ : K=!J := by
    by_cases h : Z<A
    · have hk : K=true := by simp [K,h]
      have ht : ¬T<p := by rw [tEq,hk]; simp
      have hj : J=false := by simp [J,ht]
      rw [hk,hj]
      rfl
    · have hk : K=false := by simp [K,h]
      have ht : T<p := by rw [tEq,hk]; simp; exact hZ
      have hj : J=true := by simp [J,ht]
      rw [hk,hj]
      rfl
  have hElt : E<2*2^n := by
    exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_eq (by
      rw [Nat.pow_succ,Nat.mul_comm])
  have hsplit : E%2^n+2^n*J.toNat=E :=
    split_at_high E (2^n) J (Nat.two_pow_pos _) hElt hEborrow
  have hclear0 := cuccaroMod_clearFlag L n A (E%2^n) p J K hw hnd
    (Nat.mod_lt _ (Nat.two_pow_pos _)) hKJ
  have hclear : Triple (CuccaroModValues L A E p false K)
      [.X L.flag,.CX L.high L.flag] (CuccaroModValues L A E p false false) := by
    simpa [hsplit] using hclear0
  have haddP0 := cuccaroMod_addScratch L n A E p false hw hnd
  have invTrial : (p+E)%2^(n+1)=T := by
    dsimp [E]
    have ht : T<2^(n+1) := hTlt
    by_cases h : T<p
    · have hv : T+2^(n+1)-p<2^(n+1) := by omega
      rw [Nat.mod_eq_of_lt hv]
      have he : p+(T+2^(n+1)-p)=T+2^(n+1) := by omega
      rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt ht]
    · have he : T+2^(n+1)-p=(T-p)+2^(n+1) := by omega
      rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : T-p<2^(n+1))]
      have he2 : p+(T-p)=T := by omega
      rw [he2,Nat.mod_eq_of_lt ht]
  have haddP : Triple (CuccaroModValues L A E p false false)
      (cuccaroAdd L.scratch L.z L.cin) (CuccaroModValues L A T p false false) := by
    simpa [invTrial] using haddP0
  have unload0 := cuccaroMod_xorScratch L A T p p false false hnd
    (by simpa [L.scratch_length n hw] using (lt_trans hpn (by rw [Nat.pow_succ]; omega)))
  have unload : Triple (CuccaroModValues L A T p false false) (xorConstant L.scratch p)
      (CuccaroModValues L A T 0 false false) := by simpa using unload0
  have hfinal0 := cuccaroMod_subZ L n A T 0 false hw hnd
  have finalEq : (T+2^(n+1)-A)%2^(n+1)=R := by
    dsimp [T]
    have he : A+R+2^(n+1)-A=R+2^(n+1) := by omega
    rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt
      ((Nat.mod_lt _ hp).trans (hpn.trans (by rw [Nat.pow_succ]; omega)))]
  have hfinal : Triple (CuccaroModValues L A T 0 false false)
      (cuccaroSub L.a L.z L.cin) (CuccaroModValues L A R 0 false false) := by
    simpa [finalEq] using hfinal0
  simpa [cuccaroModSub,D,R,E,T,List.append_assoc] using
    (((((((((hinit.seq hmid).seq hmove).seq hsum).seq load).seq htrial').seq hclear).seq
      haddP).seq unload).seq hfinal)

theorem cuccaroModAdd_preserves_outside (L : CuccaroModLayout) (n p : Nat)
    (hw : L.Widths n) (s : State) (m : List Bool) (q : Wire) (hq : q∉L.wires) :
    (run (cuccaroModAdd L p) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro hm
  apply hq
  simp only [cuccaroModAdd,wires_append,Finset.mem_union] at hm
  simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
    CuccaroModLayout.scratch,CuccaroModLayout.z,List.mem_cons,List.mem_append,
    List.not_mem_nil,or_false]
  rcases hm with (((((((((((hm|hm)|hm)|hm)|hm)|hm)|hm)|hm)|hm)|hm)|hm)|hm)
  · have h := cuccaroAdd_wires_subset L.a L.z L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · have h := xorConstant_wires_subset L.scratch p hm
    simp only [List.mem_toFinset] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · have h := cuccaroSub_wires_subset L.scratch L.z L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · have h := xorConstant_wires_subset L.scratch p hm
    simp only [List.mem_toFinset] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · have h := maskedConstant_wires_subset L.high L.work p hm
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with h|h <;> tauto
  · have h := cuccaroAdd_wires_subset L.work L.low L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    rcases h with (h|h)|h <;> tauto
  · have h := maskedConstant_wires_subset L.high L.work p hm
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with h|h <;> tauto
  · rw [copyRegister_wires none L.low L.work (hw.low.trans hw.work.symm)] at hm
    split at hm
    · simp at hm
    · simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hm; tauto
  · have h := cuccaroSub_wires_subset L.a L.scratch L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · simp [wires,Instr.wires] at hm; tauto
  · have h := cuccaroAdd_wires_subset L.a L.scratch L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · rw [copyRegister_wires none L.low L.work (hw.low.trans hw.work.symm)] at hm
    split at hm
    · simp at hm
    · simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hm; tauto

theorem cuccaroModSub_preserves_outside (L : CuccaroModLayout) (n p : Nat)
    (hw : L.Widths n) (s : State) (m : List Bool) (q : Wire) (hq : q∉L.wires) :
    (run (cuccaroModSub L p) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro hm
  apply hq
  simp only [cuccaroModSub,wires_append,Finset.mem_union] at hm
  simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
    CuccaroModLayout.scratch,CuccaroModLayout.z,List.mem_cons,List.mem_append,
    List.not_mem_nil,or_false]
  rcases hm with (((((((((((hm|hm)|hm)|hm)|hm)|hm)|hm)|hm)|hm)|hm)|hm)|hm)
  · have h := cuccaroSub_wires_subset L.a L.z L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · have h := maskedConstant_wires_subset L.high L.work p hm
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with h|h <;> tauto
  · have h := cuccaroAdd_wires_subset L.work L.low L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    rcases h with (h|h)|h <;> tauto
  · have h := maskedConstant_wires_subset L.high L.work p hm
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with h|h <;> tauto
  · simp [wires,Instr.wires] at hm; tauto
  · have h := cuccaroAdd_wires_subset L.a L.z L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · have h := xorConstant_wires_subset L.scratch p hm
    simp only [List.mem_toFinset] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · have h := cuccaroSub_wires_subset L.scratch L.z L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · simp [wires,Instr.wires] at hm; tauto
  · have h := cuccaroAdd_wires_subset L.scratch L.z L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · have h := xorConstant_wires_subset L.scratch p hm
    simp only [List.mem_toFinset] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · have h := cuccaroSub_wires_subset L.a L.z L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h; try simp only [CuccaroModLayout.z,CuccaroModLayout.scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h; tauto

end ECDSAAdd.Arithmetic
