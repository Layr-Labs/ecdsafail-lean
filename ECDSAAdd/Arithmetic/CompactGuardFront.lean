import ECDSAAdd.Arithmetic.FusedInverseFront

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace ECDSAAdd.Arithmetic

/-- One raw guard is sufficient with explicit signed-guard AND reconstruction. -/
def compactSignedHalfFront (b cin low a h j l m : Wire) (Y R C carry : List Wire)
    (P : Nat) : Program :=
  let ac := carry.take (R.length-1)
  fusedRawNormalize b h Y R C ac carry cin P ++ [.CX low a] ++
    fusedInverseCorrectionFlagsSeed b a h j l m ++ fusedEvenHalf b a h j l m C R ac cin P

theorem compactSignedHalfFront_correct (b cin low a h j l m : Wire) (Y R C carry : List Wire)
    (P X V : Nat) (hn : ([b,a,h,j,l,m,cin]++Y++R++C++carry).Nodup)
    (hY : Y.length=R.length) (hC : C.length=R.length) (hk : carry.length=R.length)
    (hlo : ∃ tail,R=low::tail) (hw : 0<R.length)
    (hp : P%2=1) (hX : X<P) (hV : V<P) (hfit : 2*P<2^R.length)
    (s : State) (record : List Bool) (hy : regValue Y s.basis=V) (hr : regValue R s.basis=X)
    (hc0 : regValue C s.basis=0) (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false)
    (ha0 : s.basis a=false) (hh0 : s.basis h=false) (hj0 : s.basis j=false)
    (hl0 : s.basis l=false) (hm0 : s.basis m=false) :
    (run (compactSignedHalfFront b cin low a h j l m Y R C carry P) record s).phase=s.phase ∧
    (∀ w,w∉R → w≠a → w≠h →
      (run (compactSignedHalfFront b cin low a h j l m Y R C carry P) record s).basis w=s.basis w) ∧
    regValue R (run (compactSignedHalfFront b cin low a h j l m Y R C carry P) record s).basis=
      FusedSignedHalf.result P (s.basis b) X V ∧
    (run (compactSignedHalfFront b cin low a h j l m Y R C carry P) record s).basis a=
      FusedSignedHalf.parity (FusedSignedHalf.signedSum (s.basis b) X V) ∧
    (run (compactSignedHalfFront b cin low a h j l m Y R C carry P) record s).basis h=
      FusedSignedHalf.reduction P (FusedSignedHalf.signedSum (s.basis b) X V) := by
  let ac := carry.take (R.length-1)
  have hsub : ac.Sublist carry := List.take_sublist _ _
  have hac : ac.length+1=R.length := by simp [ac,hk]; omega
  have hfull := hfit
  have hraw : ([b,h,cin]++Y++R++C++carry).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have hbits : [b,a,h,j,l,m,cin].Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have dif := hbits
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at dif
  have ah : a≠h := by tauto
  have aj : a≠j := by tauto
  have al : a≠l := by tauto
  have am : a≠m := by tauto
  have hj : h≠j := by tauto
  have hl : h≠l := by tauto
  have hm : h≠m := by tauto
  have bj : b≠j := by tauto
  have bl : b≠l := by tauto
  have bm : b≠m := by tauto
  have outside (w : Wire) (hw : w∈[b,a,h,j,l,m,cin]++Y++C++carry) : w∉R := by
    intro hwr
    have hc := List.nodup_iff_count.mp hn w
    have ho := List.count_pos_iff.mpr hw
    have hrr := List.count_pos_iff.mpr hwr
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ho
    omega
  have safe (w : Wire) (hw : w∈[b,cin]++Y++C++carry) : w∉R ∧ w∉[a,h,j,l,m] := by
    refine ⟨outside w (by simp only [List.mem_cons,List.mem_append,List.mem_nil_iff] at hw ⊢; tauto),?_⟩
    intro hf
    have hc := List.nodup_iff_count.mp hn w
    have ho := List.count_pos_iff.mpr hw
    have hh := List.count_pos_iff.mpr hf
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ho hh
    omega
  have lowR : low∈R := by rcases hlo with ⟨tail,rfl⟩; simp
  have hseed : [b,a,h,j,l,m].Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have heven : ([b,a,h,j,l,m,cin]++C++R++ac).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    have hz := hsub.count_le w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  let raw := signedWordValue R.length (s.basis b) V X
  let S := FusedSignedHalf.signedSum (s.basis b) X V
  let H := FusedSignedHalf.reduction P S
  let A := FusedSignedHalf.parity S
  let rawProg := fusedRawNormalize b h Y R C ac carry cin P
  let st1 := run rawProg record s
  have hac0 : regValue ac s.basis=0 := (regValue_zero _ _).mpr
    (fun w hw => (regValue_zero _ _).mp hk0 w (hsub.subset hw))
  have f1 := fusedRawNormalize_shared_correct b h Y R C ac carry cin P hraw hsub hY hC hac hk
    (by omega) s record hc0 hac0 hk0 hi hh0
  have rawR : regValue R st1.basis=raw := by simpa only [hy,hr] using f1.2.2.1
  have rawH : st1.basis h=H := by
    simpa only [hy,hr,fusedRawReduction R.length P X V (s.basis b) hX hV hfull] using f1.2.2.2
  have rawa0 : st1.basis a=false := (f1.2.1 a (outside a (by simp)) ah).trans ha0
  have rawb : st1.basis b=s.basis b := f1.2.1 b (outside b (by simp)) (by tauto)
  have rawlow : st1.basis low=A := by
    rcases hlo with ⟨tail,ht⟩
    have hb := fusedWordLowBit low tail st1.basis
    rw [←ht,rawR,fusedRawParity R.length P X V (s.basis b) hw hX hV hfull] at hb
    exact hb
  let r2 := record.drop (measurementCount rawProg)
  let st2 := run [.CX low a] r2 st1
  have f2 : st2.phase=st1.phase ∧ (∀ w,w≠a → st2.basis w=st1.basis w) ∧ st2.basis a=A := by
    refine ⟨rfl,?_,?_⟩
    · intro w hw'; simp [st2,run,writeBit,hw']
    · simp [st2,run,writeBit,rawa0,rawlow]
  let st3 := run (fusedInverseCorrectionFlagsSeed b a h j l m) r2 st2
  have f3 := fusedInverseCorrectionFlagsSeed_correct b a h j l m hseed st2 r2
    (by rw [f2.2.1 j aj.symm,f1.2.1 j (outside j (by simp)) hj.symm]; exact hj0)
    (by rw [f2.2.1 l al.symm,f1.2.1 l (outside l (by simp)) hl.symm]; exact hl0)
    (by rw [f2.2.1 m am.symm,f1.2.1 m (outside m (by simp)) hm.symm]; exact hm0)
  have fixed (w : Wire) (hwR : w∉R) (hwF : w∉[a,h,j,l,m]) : st3.basis w=s.basis w := by
    have hd : w≠a ∧ w≠h ∧ w≠j ∧ w≠l ∧ w≠m := by simpa only [List.mem_cons,List.mem_nil_iff,not_or,not_false_eq_true,and_true] using hwF
    exact (f3.2.1 w hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2).trans
      ((f2.2.1 w hd.1).trans (f1.2.1 w hwR hd.2.1))
  have b3 : st3.basis b=s.basis b := fixed b (safe b (by simp)).1 (safe b (by simp)).2
  have a3 : st3.basis a=A := (f3.2.1 a aj al am).trans f2.2.2
  have h3 : st3.basis h=H := (f3.2.1 h hj hl hm).trans ((f2.2.1 h ah.symm).trans rawH)
  have R3 : regValue R st3.basis=raw := (regValue_congr _ _ _ (fun w hwR => by
    have hnF : w≠a ∧ w≠j ∧ w≠l ∧ w≠m := by
      constructor
      · intro hh'; subst w; exact outside a (by simp) hwR
      constructor
      · intro hh'; subst w; exact outside j (by simp) hwR
      constructor
      · intro hh'; subst w; exact outside l (by simp) hwR
      · intro hh'; subst w; exact outside m (by simp) hwR
    exact (f3.2.1 w hnF.2.1 hnF.2.2.1 hnF.2.2.2).trans (f2.2.1 w hnF.1))).trans rawR
  have hj3 : st3.basis j=(st3.basis b&&st3.basis h) := by
    rw [f3.2.2.1,f3.2.1 b bj bl bm,f3.2.1 h hj hl hm]
  have hl3 : st3.basis l=(st3.basis a&&st3.basis h) := by
    rw [f3.2.2.2.1,f3.2.1 a aj al am,f3.2.1 h hj hl hm]
  have hm3 : st3.basis m=(st3.basis a&&st3.basis j) := by
    rw [f3.2.2.2.2,f3.2.1 a aj al am,f3.2.2.1]
  have c3 : regValue C st3.basis=0 := (regValue_congr _ _ _ (fun w hw' =>
    fixed w (safe w (by simp [hw'])).1 (safe w (by simp [hw'])).2)).trans hc0
  have k3 : regValue ac st3.basis=0 := (regValue_congr _ _ _ (fun w hw' =>
    fixed w (safe w (by simp [hsub.subset hw'])).1 (safe w (by simp [hsub.subset hw'])).2)).trans hac0
  have i3 : st3.basis cin=false := (fixed cin (safe cin (by simp)).1 (safe cin (by simp)).2).trans hi
  have f4 := fusedEvenHalf_correct b a h j l m C R ac cin P X V heven hC hac hp hX hV hfull st3 r2
    c3 k3 i3 (by simpa only [b3] using a3) (by simpa only [b3] using h3) hj3 hl3 hm3
    (by simpa only [b3] using R3)
  rw [compactSignedHalfFront,run_append,run_take,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,show measurementCount [.CX low a]=0 by rfl,
    (fusedInverseCorrectionFlagsSeed_counts b a h j l m).2,Nat.add_zero]
  change (run (fusedEvenHalf b a h j l m C R ac cin P) r2 st3).phase=s.phase ∧ _
  refine ⟨f4.1.trans (f3.1.trans (f2.1.trans f1.1)),?_,?_,?_,?_⟩
  · intro w hwR hwa hwh
    by_cases hwj : w=j
    · subst w; exact f4.2.2.2.1.trans hj0.symm
    by_cases hwl : w=l
    · subst w; exact f4.2.2.2.2.1.trans hl0.symm
    by_cases hwm : w=m
    · subst w; exact f4.2.2.2.2.2.trans hm0.symm
    exact (f4.2.1 w hwR hwj hwl hwm).trans (fixed w hwR (by simp [hwa,hwh,hwj,hwl,hwm]))
  · simpa only [b3] using f4.2.2.1
  · exact (f4.2.1 a (outside a (by simp)) aj al am).trans a3
  · exact (f4.2.1 h (outside h (by simp)) hj hl hm).trans h3

/-- Exact emitted cost of the composed canonical front, with selector cleanup. -/
theorem compactSignedHalfFront_counts (b cin low a h j l m : Wire) (Y R C carry : List Wire)
    (P : Nat) (hY : Y.length=R.length) (hC : C.length=R.length) (hk : carry.length=R.length)
    (hw : 0<R.length) :
    toffoliCount (compactSignedHalfFront b cin low a h j l m Y R C carry P)=3*R.length+1 ∧
    measurementCount (compactSignedHalfFront b cin low a h j l m Y R C carry P)=3*R.length+1 := by
  let ac := carry.take (R.length-1)
  have ha : ac.length+1=R.length := by simp [ac,hk]; omega
  have hr := fusedRawNormalize_counts b h Y R C ac carry cin P hY hC ha hk
  have he := fusedEvenHalf_counts b a h j l m C R ac cin P hC ha
  have hf := fusedInverseCorrectionFlagsSeed_counts b a h j l m
  dsimp only [ac] at hr he
  simp only [compactSignedHalfFront,toffoliCount_append,measurementCount_append,hr.1,hr.2,
    he.1,he.2,hf.1,hf.2,show toffoliCount [.CX low a]=0 by rfl,
    show measurementCount [.CX low a]=0 by rfl,Nat.add_zero]
  constructor <;> omega

private theorem compactRunSeven (p1 p2 p3 p4 p5 p6 p7 : Program) (P : State → State → Prop)
    (h : ∀ (s s1 s2 s3 s4 s5 s6 s7 : State) (m1 m2 m3 m4 m5 m6 m7 : List Bool),
      run p1 m1 s=s1 → run p2 m2 s1=s2 → run p3 m3 s2=s3 →
      run p4 m4 s3=s4 → run p5 m5 s4=s5 → run p6 m6 s5=s6 →
      run p7 m7 s6=s7 → P s s7) (s : State) (ms : List Bool) :
    P s (run (p1++(p2++(p3++(p4++(p5++(p6++p7)))))) ms s) := by
  simp only [run_append]
  apply h s _ _ _ _ _ _ _ _ _ _ _ _ _ _ <;> rfl

theorem compactSignedHalfUnfront_correct (b cin low a h j l m : Wire)
    (Y R C carry : List Wire) (P X V : Nat)
    (hn : ([b,a,h,j,l,m,cin]++Y++R++C++carry).Nodup)
    (hY : Y.length=R.length) (hC : C.length=R.length) (hk : carry.length=R.length)
    (hlo : ∃ tail,R=low::tail) (hw : 0<R.length)
    (hp : P%2=1) (hX : X<P) (hV : V<P) (hfit : 2*P<2^R.length)
    (s : State) (record : List Bool) (hin : FusedUnfrontInput b cin a h j l m Y R C carry P X V s.basis) :
    FusedUnfrontOutput a h R X s (run (fusedSignedHalfUnfront b cin low a h j l m Y R C carry P) record s) := by
  let ac := carry.take (R.length-1)
  let Goal : State → State → Prop := fun initial out =>
    FusedUnfrontInput b cin a h j l m Y R C carry P X V initial.basis →
      FusedUnfrontOutput a h R X initial out
  have all := compactRunSeven (rotateLeft R) (fusedInverseCorrectionFlagsSeed b a h j l m)
    (fusedCorrectionUndo a j l m C R ac cin P (2*P) (2^R.length-P))
    (fusedCorrectionFlagsErase b a h j l m) [.CX low a]
    (fusedInverseRawFlagClear R C carry cin h P) (signedSub b Y R ac) Goal
    (by
      intro initial s1 s2 s3 s4 s5 s6 s7 m1 m2 m3 m4 m5 m6 m7 hs1 hs2 hs3 hs4 hs5 hs6 hs7 input
      rcases input with ⟨hy,hr,hc0,hk0,hi,ha,hh,hj0,hl0,hm0⟩
      let B := initial.basis b
      let A := FusedSignedHalf.parity (FusedSignedHalf.signedSum B X V)
      let H := FusedSignedHalf.reduction P (FusedSignedHalf.signedSum B X V)
      let raw := signedWordValue R.length B V X
      have hac : ac.length+1=R.length := by simp [ac,hk]; omega
      have hsub : ac.Sublist carry := List.take_sublist _ _
      have hfull := hfit
      have hR : R.Nodup := by
        apply List.nodup_iff_count.mpr
        intro w
        have hc := List.nodup_iff_count.mp hn w
        simp only [List.count_cons,List.count_append,List.count_nil] at hc
        omega
      have hbits : [b,a,h,j,l,m,cin].Nodup := by
        apply List.nodup_iff_count.mpr
        intro w
        have hc := List.nodup_iff_count.mp hn w
        simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
        omega
      have dif := hbits
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at dif
      have hseed : [b,a,h,j,l,m].Nodup := by
        apply List.nodup_iff_count.mpr
        intro w
        have hc := List.nodup_iff_count.mp hbits w
        simp only [List.count_cons,List.count_nil] at hc ⊢
        omega
      have outside (w : Wire) (hw' : w∈[b,a,h,j,l,m,cin]++Y++C++carry) : w∉R := by
        intro hm
        have hc := List.nodup_iff_count.mp hn w
        have hq := List.count_pos_iff.mpr hw'
        have ht := List.count_pos_iff.mpr hm
        simp only [List.count_cons,List.count_append,List.count_nil] at hc hq
        omega
      have flagAway (w : Wire) (hw' : w∈Y++R++C++carry) :
          w≠a ∧ w≠h ∧ w≠j ∧ w≠l ∧ w≠m := by
        have hc := List.nodup_iff_count.mp hn w
        have hq := List.count_pos_iff.mpr hw'
        simp only [List.count_cons,List.count_append,List.count_nil] at hc hq
        repeat' constructor
        all_goals intro he; subst w; simp only [beq_self_eq_true,if_true] at hc; omega
      have rot := rotateLeft_spec R hR (FusedSignedHalf.result P B X V)
        (by have hb := (FusedSignedHalf.result_spec P X V B hp hX hV).1; omega) initial m1 hr
      have frame1 := (rotate_frame R initial m1).2.2.2
      rw [hs1] at rot frame1
      have f2 := fusedInverseCorrectionFlagsSeed_correct b a h j l m hseed s1 m2
        ((frame1 j (outside j (by simp))).trans hj0)
        ((frame1 l (outside l (by simp))).trans hl0)
        ((frame1 m (outside m (by simp))).trans hm0)
      rw [hs2] at f2
      have fixed2 (w : Wire) (hwR : w∉R) (hwj : w≠j) (hwl : w≠l) (hwm : w≠m) :
          s2.basis w=initial.basis w := (f2.2.1 w hwj hwl hwm).trans (frame1 w hwR)
      have b2 : s2.basis b=B := fixed2 b (outside b (by simp)) (by tauto) (by tauto) (by tauto)
      have a2 : s2.basis a=A := (fixed2 a (outside a (by simp)) (by tauto) (by tauto) (by tauto)).trans ha
      have h2 : s2.basis h=H := (fixed2 h (outside h (by simp)) (by tauto) (by tauto) (by tauto)).trans hh
      have j2 : s2.basis j=(B&&H) := by
        rw [f2.2.2.1,frame1 b (outside b (by simp)),frame1 h (outside h (by simp)),hh]
      have l2 : s2.basis l=(A&&H) := by
        rw [f2.2.2.2.1,frame1 a (outside a (by simp)),frame1 h (outside h (by simp)),ha,hh]
      have m2v : s2.basis m=(A&&(B&&H)) := by
        rw [f2.2.2.2.2,frame1 a (outside a (by simp)),frame1 b (outside b (by simp)),
          frame1 h (outside h (by simp)),ha,hh]
      have R2 : regValue R s2.basis=2*FusedSignedHalf.result P B X V :=
        (regValue_congr _ _ _ (fun w hw' => by
          have hf := flagAway w (by simp [hw'])
          exact f2.2.1 w hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2)).trans rot.2
      have clean2 (r : List Wire) (hm : ∀ w∈r,w∈Y++C++carry) :
          regValue r s2.basis=regValue r initial.basis := by
        apply regValue_congr
        intro w hw'
        have ho := hm w hw'
        have hf := flagAway w (by simp only [List.mem_append] at ho ⊢; tauto)
        exact fixed2 w (outside w (by simp only [List.mem_cons,List.mem_append,List.not_mem_nil] at ho ⊢; tauto))
          hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2
      have C2 := (clean2 C (by intro w hw'; simp [hw'])).trans hc0
      have K2 := (clean2 carry (by intro w hw'; simp [hw'])).trans hk0
      have i2 : s2.basis cin=false := (fixed2 cin (outside cin (by simp)) (by tauto) (by tauto) (by tauto)).trans hi
      have ac2 : regValue ac s2.basis=0 := (regValue_zero _ _).mpr
        (fun w hw' => (regValue_zero _ _).mp K2 w (hsub.subset hw'))
      have nundo : (cin::([a,j,l,m]++C++R++ac)).Nodup := by
        apply List.nodup_iff_count.mpr
        intro w
        have hc := List.nodup_iff_count.mp hn w
        have ht := hsub.count_le w
        simp only [List.count_cons,List.count_append,List.count_nil] at hc ht ⊢
        omega
      have hP : P<2^C.length := by rw [hC]; omega
      have hD : 2*P<2^C.length := by simpa only [hC] using hfull
      have hN : 2^R.length-P<2^C.length := by rw [hC]; omega
      have f3 := fusedCorrectionUndo_correct a j l m C R ac cin P (2*P) (2^R.length-P)
        nundo hC hac hP hD hN s2 m3 C2 ac2 i2
      rw [hs3] at f3
      have R3 : regValue R s3.basis=raw := by
        rw [f3.2.2,R2,a2,j2,l2,m2v]
        exact fusedCorrectionUndoMachine R.length P X V B hp hX hV hfull
      have b3 : s3.basis b=B := (f3.2.1 b (outside b (by simp))).trans b2
      have a3 : s3.basis a=A := (f3.2.1 a (outside a (by simp))).trans a2
      have h3 : s3.basis h=H := (f3.2.1 h (outside h (by simp))).trans h2
      have f4 := fusedCorrectionFlagsErase_correct b a h j l m hseed s3 m4
        (by rw [f3.2.1 j (outside j (by simp)),j2,b3,h3])
        (by rw [f3.2.1 l (outside l (by simp)),l2,a3,h3])
        (by rw [f3.2.1 m (outside m (by simp)),f3.2.1 j (outside j (by simp)),m2v,a3,j2])
      rw [hs4] at f4
      have fixed4 (w : Wire) (hwR : w∉R) (hwj : w≠j) (hwl : w≠l) (hwm : w≠m) :
          s4.basis w=initial.basis w := (f4.2.1 w hwj hwl hwm).trans
        ((f3.2.1 w hwR).trans (fixed2 w hwR hwj hwl hwm))
      have R4 : regValue R s4.basis=raw := (regValue_congr _ _ _ (fun w hw' => by
        have hf := flagAway w (by simp [hw'])
        exact f4.2.1 w hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2)).trans R3
      have lowR : low∈R := by rcases hlo with ⟨tail,rfl⟩; simp
      have lowa : low≠a := by intro he; subst low; exact outside a (by simp) lowR
      have low4 : s4.basis low=A := by
        rcases hlo with ⟨tail,ht⟩
        have hl := fusedWordLowBit low tail s4.basis
        rw [←ht,R4,fusedRawParity R.length P X V B hw hX hV hfull] at hl
        exact hl
      have a4 : s4.basis a=A := (fixed4 a (outside a (by simp)) (by tauto) (by tauto) (by tauto)).trans ha
      have f5 : s5.phase=s4.phase ∧ (∀ w,w≠a → s5.basis w=s4.basis w) ∧ s5.basis a=false := by
        rw [←hs5]
        refine ⟨by simp [run],?_,?_⟩
        · intro w hw'; simp [run,writeBit,hw']
        · simp [run,writeBit,a4,low4]
      have R5 : regValue R s5.basis=raw := (regValue_congr _ _ _ (fun w hw' =>
        f5.2.1 w (flagAway w (by simp [hw'])).1)).trans R4
      have clean5 (r : List Wire) (hm : ∀ w∈r,w∈Y++C++carry) :
          regValue r s5.basis=regValue r initial.basis := by
        apply regValue_congr
        intro w hw'
        have ho := hm w hw'
        have hf := flagAway w (by simp only [List.mem_append] at ho ⊢; tauto)
        exact (f5.2.1 w hf.1).trans
          (fixed4 w (outside w (by simp only [List.mem_cons,List.mem_append,List.not_mem_nil] at ho ⊢; tauto))
            hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2)
      have C5 := (clean5 C (by intro w hw'; simp [hw'])).trans hc0
      have K5 := (clean5 carry (by intro w hw'; simp [hw'])).trans hk0
      have i5 : s5.basis cin=false := (f5.2.1 cin (by tauto)).trans
        ((fixed4 cin (outside cin (by simp)) (by tauto) (by tauto) (by tauto)).trans hi)
      have H5 : s5.basis h= !decide (regValue R s5.basis<P) := by
        rw [f5.2.1 h (by tauto),fixed4 h (outside h (by simp)) (by tauto) (by tauto) (by tauto),hh,R5]
        exact (fusedRawReduction R.length P X V B hX hV hfull).symm
      have ncmp : (h::cin::(R++C++carry)).Nodup := by
        apply List.nodup_iff_count.mpr
        intro w
        have hc := List.nodup_iff_count.mp hn w
        simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
        omega
      have f6 := fusedInverseRawFlagClear_correct R C carry cin h P ncmp hC.symm
        (hk.trans hC.symm) hP s5 m6 C5 K5 i5 H5
      rw [hs6] at f6
      have R6 : regValue R s6.basis=raw := (regValue_congr _ _ _ (fun w hw' =>
        f6.2.1 w (flagAway w (by simp [hw'])).2.1)).trans R5
      have Y6 : regValue Y s6.basis=V := (regValue_congr _ _ _ (fun w hw' =>
        f6.2.1 w (flagAway w (by simp [hw'])).2.1)).trans
        ((clean5 Y (by intro w hw'; simp [hw'])).trans hy)
      have K6 : regValue carry s6.basis=0 := (regValue_congr _ _ _ (fun w hw' =>
        f6.2.1 w (flagAway w (by simp [hw'])).2.1)).trans K5
      have ac6 : regValue ac s6.basis=0 := (regValue_zero _ _).mpr
        (fun w hw' => (regValue_zero _ _).mp K6 w (hsub.subset hw'))
      have b6 : s6.basis b=B := (f6.2.1 b (by tauto)).trans ((f5.2.1 b (by tauto)).trans
        (fixed4 b (outside b (by simp)) (by tauto) (by tauto) (by tauto)))
      have nsub : (b::(Y++R++ac)).Nodup := by
        apply List.nodup_iff_count.mpr
        intro w
        have hc := List.nodup_iff_count.mp hn w
        have ht := hsub.count_le w
        simp only [List.count_cons,List.count_append,List.count_nil] at hc ht ⊢
        omega
      have f7 := signedSub_spec b Y R ac nsub hY hac B V raw s6 m7 ⟨⟨⟨b6,Y6⟩,R6⟩,ac6⟩
      have frame7 (w : Wire) (hw' : w∉R) :=
        (signedWord_frame b Y R ac nsub hY hac B V raw s6 m7 b6 Y6 R6 ac6 w hw').2
      rw [hs7] at f7
      have frame7' (w : Wire) (hw' : w∉R) : s7.basis w=s6.basis w := by
        simpa only [hs7] using frame7 w hw'
      unfold FusedUnfrontOutput
      refine ⟨f7.1.trans (f6.1.trans (f5.1.trans (f4.1.trans (f3.1.trans (f2.1.trans rot.1))))),?_,?_,?_,?_⟩
      · intro w hwR hwa hwh
        rw [frame7' w hwR,f6.2.1 w hwh,f5.2.1 w hwa]
        by_cases hwj : w=j
        · subst w; exact f4.2.2.1.trans hj0.symm
        by_cases hwl : w=l
        · subst w; exact f4.2.2.2.1.trans hl0.symm
        by_cases hwm : w=m
        · subst w; exact f4.2.2.2.2.trans hm0.symm
        exact fixed4 w hwR hwj hwl hwm
      · exact f7.2.1.2.trans (fusedSignedWordInverse R.length X V B (by omega) (by omega))
      · exact (frame7' a (outside a (by simp))).trans ((f6.2.1 a (by tauto)).trans f5.2.2)
      · exact (frame7' h (outside h (by simp))).trans f6.2.2)
    s record
  simpa only [fusedSignedHalfUnfront,List.append_assoc,ac] using all hin

end ECDSAAdd.Arithmetic
