import ECDSAAdd.Arithmetic.CuccaroNormalize
import ECDSAAdd.Arithmetic.CuccaroSignedSquareInverse

namespace ECDSAAdd.Arithmetic

structure CuccaroNormalizeValues (L : CuccaroNormalizeLayout)
    (V W : Nat) (C F : Bool) (s : BasisState) : Prop where
  a : regValue L.a s=V
  scratch : regValue L.scratch s=W
  cin : s L.cin=C
  flag : s L.flag=F

structure CuccaroNormalizeSplit (L : CuccaroNormalizeLayout)
    (V W : Nat) (H WH C F : Bool) (s : BasisState) : Prop where
  src : regValue L.src s=V
  high : s L.high=H
  work : regValue L.work s=W
  workHigh : s L.workHigh=WH
  cin : s L.cin=C
  flag : s L.flag=F

private theorem normalize_xorScratch (L : CuccaroNormalizeLayout)
    (V W c : Nat) (C F : Bool) (hnd : L.wires.Nodup)
    (hc : c<2^L.scratch.length) :
    Triple (CuccaroNormalizeValues L V W C F) (xorConstant L.scratch c)
      (CuccaroNormalizeValues L V (W ^^^ c) C F) := by
  have hn : L.scratch.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroNormalizeLayout.wires,List.count_cons,List.count_append,
      List.count_nil] at h
    omega
  have outside (q : Wire) (hq : q∈L.a++[L.cin,L.flag]) : q∉L.scratch := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroNormalizeLayout.wires,List.count_cons,List.count_append,
      List.count_nil] at hn h1
    omega
  intro s m h
  obtain ⟨ph,fr,v⟩ := xorConstant_correct L.scratch hn c hc s m
  refine ⟨ph,⟨?_,v.trans (congrArg (fun x => x ^^^ c) h.scratch),?_,?_⟩⟩
  · exact (regValue_congr _ _ _ (fun q hq => fr q (outside q (by simp [hq])))).trans h.a
  · exact (fr L.cin (outside L.cin (by simp))).trans h.cin
  · exact (fr L.flag (outside L.flag (by simp))).trans h.flag

private theorem normalize_addScratch (L : CuccaroNormalizeLayout) (n V W : Nat)
    (F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) :
    Triple (CuccaroNormalizeValues L V W false F)
      (cuccaroAdd L.scratch L.a L.cin)
      (CuccaroNormalizeValues L ((W+V)%2^(n+1)) W false F) := by
  have ha := L.a_length n hw
  have hs := L.scratch_length n hw
  have hsub : (L.cin::L.scratch++L.a).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroNormalizeLayout.wires,List.count_cons,List.count_append,
      List.count_nil] at h ⊢
    omega
  have outsideFlag : L.flag∉L.cin::L.scratch++L.a := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd L.flag
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroNormalizeLayout.wires,List.count_cons,List.count_append,
      List.count_nil,beq_self_eq_true,if_true] at hn h2
    omega
  intro s m h
  have runh := cuccaroAdd_correct L.scratch L.a L.cin hsub (hs.trans ha.symm) s m
  refine ⟨runh.1,⟨?_,runh.2.1.trans h.scratch,runh.2.2.1.trans h.cin,?_⟩⟩
  · rw [runh.2.2.2.1,h.scratch,h.a,h.cin,ha]
    simp only [Bool.toNat_false,Nat.add_zero]
  · exact (runh.2.2.2.2 L.flag outsideFlag).trans h.flag

private theorem normalize_maskWork (L : CuccaroNormalizeLayout)
    (V W c : Nat) (H WH C F : Bool) (hnd : L.wires.Nodup)
    (hc : c<2^L.work.length) :
    Triple (CuccaroNormalizeSplit L V W H WH C F)
      (maskedConstant L.high L.work c)
      (CuccaroNormalizeSplit L V (W ^^^ if H then c else 0) H WH C F) := by
  have hn : L.work.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.scratch,
      CuccaroNormalizeLayout.a,List.count_cons,List.count_append,List.count_nil] at h
    omega
  have hctl : L.high∉L.work := by
    intro hm
    have h := List.nodup_iff_count.mp hnd L.high
    have hp := List.count_pos_iff.mpr hm
    simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.scratch,
      CuccaroNormalizeLayout.a,List.count_cons,List.count_append,List.count_nil,
      beq_self_eq_true,if_true] at h
    omega
  have outside (q : Wire) (hq : q∈L.src++[L.high,L.workHigh,L.cin,L.flag]) : q∉L.work := by
    intro hm
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.scratch,
      CuccaroNormalizeLayout.a,List.count_cons,List.count_append,List.count_nil] at h h1
    omega
  intro s m h
  obtain ⟨ph,fr,v⟩ := maskedConstant_correct L.high L.work c hn hctl hc s m
  refine ⟨ph,⟨?_,?_,?_,?_,?_,?_⟩⟩
  · exact (regValue_congr _ _ _ (fun q hq => fr q (outside q (by simp [hq])))).trans h.src
  · exact (fr L.high (outside L.high (by simp))).trans h.high
  · rw [v,h.work,h.high]
  · exact (fr L.workHigh (outside L.workHigh (by simp))).trans h.workHigh
  · exact (fr L.cin (outside L.cin (by simp))).trans h.cin
  · exact (fr L.flag (outside L.flag (by simp))).trans h.flag

private theorem normalize_xorWork (L : CuccaroNormalizeLayout)
    (V W c : Nat) (H WH C F : Bool) (hnd : L.wires.Nodup)
    (hc : c<2^L.work.length) :
    Triple (CuccaroNormalizeSplit L V W H WH C F) (xorConstant L.work c)
      (CuccaroNormalizeSplit L V (W ^^^ c) H WH C F) := by
  have hn : L.work.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hh := List.nodup_iff_count.mp hnd q
    simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.scratch,
      List.count_cons,List.count_append,List.count_nil] at hh
    omega
  have outside (q : Wire) (hq : q∈L.src++[L.high,L.workHigh,L.cin,L.flag]) : q∉L.work := by
    intro hm
    have hh := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,
      CuccaroNormalizeLayout.scratch,List.count_cons,List.count_append,List.count_nil] at hh h1
    omega
  intro s m h
  obtain ⟨ph,fr,val⟩ := xorConstant_correct L.work hn c hc s m
  refine ⟨ph,⟨?_,?_,?_,?_,?_,?_⟩⟩
  · exact (regValue_congr _ _ _ (fun q hq => fr q (outside q (by simp [hq])))).trans h.src
  · exact (fr L.high (outside L.high (by simp))).trans h.high
  · rw [val,h.work]
  · exact (fr L.workHigh (outside L.workHigh (by simp))).trans h.workHigh
  · exact (fr L.cin (outside L.cin (by simp))).trans h.cin
  · exact (fr L.flag (outside L.flag (by simp))).trans h.flag

private theorem normalize_subLow (L : CuccaroNormalizeLayout) (n V W : Nat)
    (H WH F : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) :
    Triple (CuccaroNormalizeSplit L V W H WH false F)
      (cuccaroSub L.work L.src L.cin)
      (CuccaroNormalizeSplit L ((V+2^n-W)%2^n) W H WH false F) := by
  have hsub : (L.cin::L.work++L.src).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.scratch,
      CuccaroNormalizeLayout.a,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have hlen := hw.work.trans hw.src.symm
  have outside (q : Wire) (hq : q∈[L.high,L.workHigh,L.flag]) :
      q∉L.cin::L.work++L.src := by
    intro hm
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.scratch,
      CuccaroNormalizeLayout.a,List.count_cons,List.count_append,List.count_nil] at hn h1 h2
    omega
  intro s m h
  have runh := cuccaroSub_correct L.work L.src L.cin hsub hlen s m h.cin
  refine ⟨runh.1,⟨?_,?_,runh.2.1.trans h.work,?_,runh.2.2.1,?_⟩⟩
  · rw [runh.2.2.2.1,h.src,h.work,hw.src]
  · exact (runh.2.2.2.2 L.high (outside L.high (by simp))).trans h.high
  · exact (runh.2.2.2.2 L.workHigh (outside L.workHigh (by simp))).trans h.workHigh
  · exact (runh.2.2.2.2 L.flag (outside L.flag (by simp))).trans h.flag

private theorem normalize_moveHigh (L : CuccaroNormalizeLayout) (n V W : Nat)
    (K : Bool) (hw : L.Widths n) (hnd : L.wires.Nodup) (hV : V<2^n) :
    Triple (CuccaroNormalizeValues L (V+2^n*K.toNat) W false false)
      [.CX L.high L.flag,.CX L.flag L.high]
      (CuccaroNormalizeValues L V W false K) := by
  have hhf : L.high≠L.flag := by
    intro e
    have hn := List.nodup_iff_count.mp hnd L.high
    simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn
    simp [e] at hn
    omega
  intro s m h
  have highK : s.basis L.high=K := by
    have hb := regValue_highBit L.src L.high s.basis
    rw [← CuccaroNormalizeLayout.a,h.a,hw.src] at hb
    cases K with
    | false =>
      cases hv : s.basis L.high
      · rfl
      · have := hb.mp hv; simp at this; omega
    | true =>
      cases hv : s.basis L.high
      · have ht : 2^n≤V+2^n := by omega
        have ht' : 2^n≤V+2^n*true.toNat := by
          simpa only [Bool.toNat_true,Nat.mul_one] using ht
        have := hb.mpr ht'; simp_all
      · rfl
  let out := run [.CX L.high L.flag,.CX L.flag L.high] m s
  have bits : out.basis L.high=false ∧ out.basis L.flag=K := by
    dsimp [out]
    cases K <;> simp_all [run,writeBit,h.flag,Ne.symm hhf]
  have keep (q : Wire) (hq : q≠L.high) (hf : q≠L.flag) : out.basis q=s.basis q := by
    dsimp [out]
    simp [run,writeBit,hq,hf]
  have safe (q : Wire) (hq : q∈L.src++L.scratch++[L.cin]) :
      q≠L.high ∧ q≠L.flag := by
    constructor <;> intro e
    · subst q
      have hn := List.nodup_iff_count.mp hnd L.high
      have hp := List.count_pos_iff.mpr hq
      simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,
        CuccaroNormalizeLayout.scratch,List.count_cons,List.count_append,List.count_nil,
        beq_self_eq_true,if_true] at hn hp
      omega
    · subst q
      have hn := List.nodup_iff_count.mp hnd L.flag
      have hp := List.count_pos_iff.mpr hq
      simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,
        List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hn hp
      omega
  refine ⟨rfl,⟨?_,?_,?_,bits.2⟩⟩
  · rw [CuccaroNormalizeLayout.a,regValue_append]
    have srcSame : regValue L.src out.basis=regValue L.src s.basis :=
      regValue_congr _ _ _ (fun q hq => keep q (safe q (by simp [hq])).1 (safe q (by simp [hq])).2)
    have srcv := regValue_low L.src L.high s.basis
    rw [← CuccaroNormalizeLayout.a,h.a,hw.src,Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hV] at srcv
    have hh : regValue [L.high] out.basis=0 := by simp [regValue,bits.1]
    rw [srcSame,srcv,hh]
    simp
  · rw [← h.scratch]; apply regValue_congr; intro q hq
    exact keep q (safe q (by simp [hq])).1 (safe q (by simp [hq])).2
  · exact (keep L.cin (safe L.cin (by simp)).1 (safe L.cin (by simp)).2).trans h.cin

theorem cuccaroNormalize_spec (L : CuccaroNormalizeLayout) (n c V : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hc : 0<c) (hcn : c<2^n)
    (hcp : c<2^n-c) (hV : V<2^n) :
    let p := 2^n-c
    let K := decide (p≤V)
    Triple (CuccaroNormalizeValues L V 0 false false) (cuccaroNormalize L c)
      (CuccaroNormalizeValues L (V%p) 0 false K) := by
  let p := 2^n-c
  let K := decide (p≤V)
  have hp : 0<p := by dsimp [p]; omega
  have ha := L.a_length n hw
  have hs := L.scratch_length n hw
  have load0 := normalize_xorScratch L V 0 c false false hnd
    (by simpa [hs] using (hcn.trans (by rw [Nat.pow_succ]; omega)))
  have load : Triple (CuccaroNormalizeValues L V 0 false false)
      (xorConstant L.scratch c) (CuccaroNormalizeValues L V c false false) := by
    simpa using load0
  have add0 := normalize_addScratch L n V c false hw hnd
  have hsum : V+c<2^(n+1) := by rw [Nat.pow_succ]; omega
  have add : Triple (CuccaroNormalizeValues L V c false false)
      (cuccaroAdd L.scratch L.a L.cin) (CuccaroNormalizeValues L (V+c) c false false) := by
    simpa only [Nat.mod_eq_of_lt (by omega),Nat.add_comm c V] using add0
  have unload0 := normalize_xorScratch L (V+c) c c false false hnd
    (by simpa [hs] using (hcn.trans (by rw [Nat.pow_succ]; omega)))
  have unload : Triple (CuccaroNormalizeValues L (V+c) c false false)
      (xorConstant L.scratch c) (CuccaroNormalizeValues L (V+c) 0 false false) := by
    simpa using unload0
  have highEq : 2^n≤V+c ↔ K=true := by
    dsimp [K,p]
    simp only [decide_eq_true_eq]
    omega
  have first := (load.seq add).seq unload
  have loadXor0 := normalize_xorWork L ((V+c)%2^n) 0 c K false false false hnd
    (by simpa [hw.work] using hcn)
  have loadXor : Triple
      (CuccaroNormalizeSplit L ((V+c)%2^n) 0 K false false false)
      (xorConstant L.work c)
      (CuccaroNormalizeSplit L ((V+c)%2^n) c K false false false) := by
    simpa using loadXor0
  have loadMask0 := normalize_maskWork L ((V+c)%2^n) c c K false false false hnd
    (by simpa [hw.work] using hcn)
  have loadMask : Triple
      (CuccaroNormalizeSplit L ((V+c)%2^n) c K false false false)
      (maskedConstant L.high L.work c)
      (CuccaroNormalizeSplit L ((V+c)%2^n) (if K then 0 else c)
        K false false false) := by
    cases hk : K <;> simpa [hk] using loadMask0
  have sub0 := normalize_subLow L n ((V+c)%2^n) (if K then 0 else c)
    K false false hw hnd
  let R := (((V+c)%2^n)+2^n-(if K then 0 else c))%2^n
  have sub : Triple
      (CuccaroNormalizeSplit L ((V+c)%2^n) (if K then 0 else c)
        K false false false)
      (cuccaroSub L.work L.src L.cin)
      (CuccaroNormalizeSplit L R (if K then 0 else c) K false false false) := by
    simpa [R] using sub0
  have clearMask0 := normalize_maskWork L R (if K then 0 else c) c
    K false false false hnd (by simpa [hw.work] using hcn)
  have clearMask : Triple
      (CuccaroNormalizeSplit L R (if K then 0 else c) K false false false)
      (maskedConstant L.high L.work c)
      (CuccaroNormalizeSplit L R c K false false false) := by
    cases hk : K <;> simpa [hk] using clearMask0
  have clearXor0 := normalize_xorWork L R c c K false false false hnd
    (by simpa [hw.work] using hcn)
  have clearXor : Triple (CuccaroNormalizeSplit L R c K false false false)
      (xorConstant L.work c) (CuccaroNormalizeSplit L R 0 K false false false) := by
    simpa using clearXor0
  have move0 := normalize_moveHigh L n R 0 K hw hnd (by
    dsimp [R]
    exact Nat.mod_lt _ (Nat.two_pow_pos _))
  have resultEq : R=V%p := by
    dsimp [R,K,p]
    by_cases h : 2^n-c≤V
    · simp [h]
      have hv : 2^n≤V+c := by omega
      have hvc : V+c<2*2^n := by omega
      have low : (V+c)%2^n=V+c-2^n := by
        rw [Nat.mod_eq_sub_mod hv,Nat.mod_eq_of_lt (by omega)]
      rw [low]
      have he : V+c-2^n=V-(2^n-c) := by omega
      rw [he,Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
    · simp [h]
      have hv : V+c<2^n := by omega
      rw [Nat.mod_eq_of_lt hv]
      have inner : (V+c+2^n-c)%2^n=V := by
        have he : V+c+2^n-c=V+2^n := by omega
        rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt hV]
      rw [inner,Nat.mod_eq_of_lt (by omega)]
  have middle : Triple (CuccaroNormalizeValues L (V+c) 0 false false)
      (xorConstant L.work c++maskedConstant L.high L.work c++
        cuccaroSub L.work L.src L.cin++maskedConstant L.high L.work c++
        xorConstant L.work c++[.CX L.high L.flag,.CX L.flag L.high])
      (CuccaroNormalizeValues L (V%p) 0 false K) := by
    have pre : ∀s,CuccaroNormalizeValues L (V+c) 0 false false s →
        CuccaroNormalizeSplit L ((V+c)%2^n) 0 K false false false s := by
      intro s h
      have lowv := regValue_low L.src L.high s
      rw [← CuccaroNormalizeLayout.a,h.a,hw.src] at lowv
      have highv : s L.high=K := by
        have hh := regValue_highBit L.src L.high s
        rw [← CuccaroNormalizeLayout.a,h.a,hw.src] at hh
        have he := hh.trans highEq
        cases hs : s L.high <;> cases hk : K
        · rfl
        · have := he.mpr hk; simp_all
        · have := he.mp hs; simp_all
        · rfl
      have clean := (regValue_zero L.scratch s).mp h.scratch
      exact ⟨lowv,highv,
        (regValue_zero _ _).mpr (fun q hq => clean q (by simp [CuccaroNormalizeLayout.scratch,hq])),
        clean L.workHigh (by simp [CuccaroNormalizeLayout.scratch]),h.cin,h.flag⟩
    have move : Triple (CuccaroNormalizeSplit L R 0 K false false false)
        [.CX L.high L.flag,.CX L.flag L.high]
        (CuccaroNormalizeValues L R 0 false K) := by
      apply move0.conseq
      · intro s h
        have ahigh : regValue [L.high] s=K.toNat := by
          change (if s L.high then 1 else 0)=K.toNat
          rw [h.high]
          cases K <;> rfl
        have aval : regValue L.a s=R+2^n*K.toNat := by
          rw [CuccaroNormalizeLayout.a,regValue_append,h.src,ahigh,hw.src]
        have whigh : regValue [L.workHigh] s=0 := by simp [regValue,h.workHigh]
        have wval : regValue L.scratch s=0 := by
          rw [CuccaroNormalizeLayout.scratch,regValue_append,h.work,whigh]
          simp
        exact ⟨aval,wval,h.cin,h.flag⟩
      · intro _ h; exact h
    have body := ((((loadXor.seq loadMask).seq sub).seq clearMask).seq clearXor).seq move
    apply body.conseq
    · exact pre
    · intro s h
      simpa [resultEq] using h
  simpa [cuccaroNormalize,List.append_assoc,p,K] using first.seq middle

private theorem xorConstant_proper (r : List Wire) (k : Nat) :
    ProperProgram (xorConstant r k) := by
  induction r generalizing k with
  | nil => simp [xorConstant,ProperProgram]
  | cons q r ih =>
    by_cases h : k%2=1
    · simp only [xorConstant,h,if_true,properProgram_append]
      exact ⟨by simp [ProperProgram,ProperGate],ih (k/2)⟩
    · simp only [xorConstant,h,if_false,List.nil_append]
      exact ih (k/2)

private theorem maskedConstant_proper (c : Wire) (r : List Wire) (k : Nat)
    (hnd : (c::r).Nodup) : ProperProgram (maskedConstant c r k) := by
  induction r generalizing k with
  | nil => simp [maskedConstant,ProperProgram]
  | cons q r ih =>
    have hcq : c≠q := by intro e; subst q; simp at hnd
    have ht : (c::r).Nodup := by
      apply List.nodup_iff_count.mpr; intro w
      have h := List.nodup_iff_count.mp hnd w
      simp only [List.count_cons] at h ⊢
      omega
    by_cases h : k%2=1
    · simp only [maskedConstant,h,if_true,properProgram_append]
      exact ⟨by simpa [ProperProgram,ProperGate] using hcq,ih (k/2) ht⟩
    · simp only [maskedConstant,h,if_false,List.nil_append]
      exact ih (k/2) ht

theorem cuccaroNormalize_proper (L : CuccaroNormalizeLayout) (c : Nat)
    (hnd : L.wires.Nodup) : ProperProgram (cuccaroNormalize L c) := by
  have hadd : (L.cin::L.scratch++L.a).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroNormalizeLayout.wires,List.count_cons,List.count_append,
      List.count_nil] at h ⊢
    omega
  have hsub : (L.cin::L.work++L.src).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,
      CuccaroNormalizeLayout.scratch,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have hmask : (L.high::L.work).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,
      CuccaroNormalizeLayout.scratch,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have hhf : L.high≠L.flag := by
    intro e
    have h := List.nodup_iff_count.mp hnd L.high
    simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
    simp [e] at h
    omega
  simp only [cuccaroNormalize,properProgram_append]
  have last : ProperProgram [.CX L.high L.flag,.CX L.flag L.high] := by
    simpa [ProperProgram,ProperGate] using And.intro hhf (Ne.symm hhf)
  exact ⟨⟨⟨⟨⟨⟨⟨⟨xorConstant_proper L.scratch c,
    cuccaroAdd_proper L.scratch L.a L.cin hadd⟩,
    xorConstant_proper L.scratch c⟩,xorConstant_proper L.work c⟩,
    maskedConstant_proper L.high L.work c hmask⟩,
    cuccaroSub_proper L.work L.src L.cin hsub⟩,
    maskedConstant_proper L.high L.work c hmask⟩,
    xorConstant_proper L.work c⟩,last⟩

theorem cuccaroNormalize_roundtrip (L : CuccaroNormalizeLayout) (c : Nat)
    (hnd : L.wires.Nodup) (s : State) (m₁ m₂ : List Bool) :
    run (cuccaroNormalizeClear L c) m₂ (run (cuccaroNormalize L c) m₁ s)=s := by
  apply run_reverse_proper
  exact cuccaroNormalize_proper L c hnd

theorem cuccaroNormalize_wires_subset (L : CuccaroNormalizeLayout) (c : Nat) :
    wires (cuccaroNormalize L c)⊆L.wires.toFinset := by
  intro q hm
  simp only [cuccaroNormalize,wires_append,Finset.mem_union] at hm
  simp only [CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,
    CuccaroNormalizeLayout.scratch,List.mem_toFinset,List.mem_cons,List.mem_append,
    List.not_mem_nil,or_false]
  rcases hm with ((((((((hm|hm)|hm)|hm)|hm)|hm)|hm)|hm)|hm)
  · have h := xorConstant_wires_subset L.scratch c hm
    simp only [List.mem_toFinset,CuccaroNormalizeLayout.scratch,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · have h := cuccaroAdd_wires_subset L.scratch L.a L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,
      CuccaroNormalizeLayout.scratch,CuccaroNormalizeLayout.a,
      List.not_mem_nil,or_false] at h; tauto
  · have h := xorConstant_wires_subset L.scratch c hm
    simp only [List.mem_toFinset,CuccaroNormalizeLayout.scratch,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at h; tauto
  · have h := xorConstant_wires_subset L.work c hm
    simp only [List.mem_toFinset] at h; tauto
  · have h := maskedConstant_wires_subset L.high L.work c hm
    simp only [List.mem_toFinset,List.mem_cons] at h; tauto
  · have h := cuccaroSub_wires_subset L.work L.src L.cin hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h; tauto
  · have h := maskedConstant_wires_subset L.high L.work c hm
    simp only [List.mem_toFinset,List.mem_cons] at h; tauto
  · have h := xorConstant_wires_subset L.work c hm
    simp only [List.mem_toFinset] at h; tauto
  · simp [wires,Instr.wires] at hm; tauto

theorem cuccaroNormalize_preserves_outside (L : CuccaroNormalizeLayout) (c : Nat)
    (s : State) (m : List Bool) (q : Wire) (hq : q∉L.wires) :
    (run (cuccaroNormalize L c) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro hm
  exact hq (List.mem_toFinset.mp (cuccaroNormalize_wires_subset L c hm))

theorem cuccaroNormalizeClear_preserves_outside (L : CuccaroNormalizeLayout) (c : Nat)
    (s : State) (m : List Bool) (q : Wire) (hq : q∉L.wires) :
    (run (cuccaroNormalizeClear L c) m s).basis q=s.basis q := by
  apply run_preserves_outside
  rw [cuccaroNormalizeClear,wires_reverse]
  intro hm
  exact hq (List.mem_toFinset.mp (cuccaroNormalize_wires_subset L c hm))

end ECDSAAdd.Arithmetic
