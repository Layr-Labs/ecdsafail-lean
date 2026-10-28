import ECDSAAdd.Arithmetic.FusedInverseCorrection

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic

/-- The inverse front must reconstruct the signed-guard AND explicitly:
its old input-side guard no longer exists in the canonical output. -/
def fusedInverseCorrectionFlagsSeed (b a h j l m : Wire) : Program :=
  [.CCX b h j,.CCX a h l,.CCX a j m]

theorem fusedInverseCorrectionFlagsSeed_counts (b a h j l m : Wire) :
    toffoliCount (fusedInverseCorrectionFlagsSeed b a h j l m)=3 ∧
    measurementCount (fusedInverseCorrectionFlagsSeed b a h j l m)=0 := by
  constructor <;> rfl

theorem fusedInverseCorrectionFlagsSeed_correct (b a h j l m : Wire)
    (hn : [b,a,h,j,l,m].Nodup) (s : State) (record : List Bool)
    (hj : s.basis j=false) (hl : s.basis l=false) (hm : s.basis m=false) :
    (run (fusedInverseCorrectionFlagsSeed b a h j l m) record s).phase=s.phase ∧
    (∀ w,w≠j → w≠l → w≠m →
      (run (fusedInverseCorrectionFlagsSeed b a h j l m) record s).basis w=s.basis w) ∧
    (run (fusedInverseCorrectionFlagsSeed b a h j l m) record s).basis j=(s.basis b&&s.basis h) ∧
    (run (fusedInverseCorrectionFlagsSeed b a h j l m) record s).basis l=(s.basis a&&s.basis h) ∧
    (run (fusedInverseCorrectionFlagsSeed b a h j l m) record s).basis m=(s.basis a&&(s.basis b&&s.basis h)) := by
  have dif := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at dif
  have haj : a≠j := by tauto
  have hal : a≠l := by tauto
  have hhj : h≠j := by tauto
  have hlj : l≠j := by tauto
  have hmj : m≠j := by tauto
  have hml : m≠l := by tauto
  refine ⟨rfl,?_,?_,?_,?_⟩
  · intro w hwj hwl hwm
    simp [fusedInverseCorrectionFlagsSeed,run,writeBit,hwj,hwl,hwm]
  · simp [fusedInverseCorrectionFlagsSeed,run,writeBit,hj,Ne.symm hlj,Ne.symm hmj]
  · simp [fusedInverseCorrectionFlagsSeed,run,writeBit,hl,haj,hhj,hlj,Ne.symm hml]
  · simp [fusedInverseCorrectionFlagsSeed,run,writeBit,hj,hm,haj,hal,hhj,hml,hmj,Ne.symm hlj]

/-- Erase the exact raw normalization flag using a fresh full-width comparison. -/
def fusedInverseRawFlagClear (R C carry : List Wire) (cin h : Wire) (P : Nat) : Program :=
  compareLtConst none R C carry cin h P ++ [.X h]

private theorem inverse_const_compare_correct (x C carry : List Wire) (cin h : Wire)
    (K : Nat) (hn : (h::cin::(x++C++carry)).Nodup)
    (hC : x.length=C.length) (hk : carry.length=C.length) (hK : K<2^C.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false) :
    (run (compareLtConst none x C carry cin h K) record s).phase=s.phase ∧
    (∀ w,w≠h → (run (compareLtConst none x C carry cin h K) record s).basis w=s.basis w) ∧
    (run (compareLtConst none x C carry cin h K) record s).basis h=
      (s.basis h ^^ decide (regValue x s.basis<K)) := by
  obtain ⟨hf,hv⟩ := compareLtConst_spec x C carry cin h hn hC hk K hK
    (regValue x s.basis) (s.basis h) s record ⟨⟨⟨⟨rfl,hC0⟩,hk0⟩,hi⟩,rfl⟩
  simp only [Holds.holds] at hv
  refine ⟨hf,?_,hv.2⟩
  intro w hw
  by_cases hx : w∈x
  · exact (regValue_eq_iff _ _ _).mp hv.1.1.1.1 w hx
  by_cases hc : w∈C
  · exact (regValue_eq_iff _ _ _).mp (hv.1.1.1.2.trans hC0.symm) w hc
  by_cases hk' : w∈carry
  · exact (regValue_eq_iff _ _ _).mp (hv.1.1.2.trans hk0.symm) w hk'
  by_cases hi' : w=cin
  · subst w; exact hv.1.2.trans hi.symm
  apply run_preserves_outside
  rw [(compareLt_wires none x C carry cin h hC hk).2 K]
  simp [hw,hx,hc,hk',hi']


theorem fusedInverseRawFlagClear_correct (R C carry : List Wire) (cin h : Wire)
    (P : Nat) (hn : (h::cin::(R++C++carry)).Nodup)
    (hC : R.length=C.length) (hk : carry.length=C.length) (hP : P<2^C.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false)
    (hh : s.basis h= !decide (regValue R s.basis<P)) :
    (run (fusedInverseRawFlagClear R C carry cin h P) record s).phase=s.phase ∧
    (∀ w,w≠h → (run (fusedInverseRawFlagClear R C carry cin h P) record s).basis w=s.basis w) ∧
    (run (fusedInverseRawFlagClear R C carry cin h P) record s).basis h=false := by
  let cmp := compareLtConst none R C carry cin h P
  let st := run cmp record s
  have f := inverse_const_compare_correct R C carry cin h P hn hC hk hP s record hC0 hk0 hi
  have hout : st.basis h=true := by
    rw [f.2.2,hh]
    cases decide (regValue R s.basis<P) <;> rfl
  rw [fusedInverseRawFlagClear,run_append,run_take]
  change st.phase=s.phase ∧
    (∀ w,w≠h → (writeBit st.basis h (!st.basis h)) w=s.basis w) ∧
    (writeBit st.basis h (!st.basis h)) h=false
  refine ⟨f.1,?_,?_⟩
  · intro w hw
    simpa [writeBit,hw] using f.2.1 w hw
  · simp [writeBit,hout]

/-- Independent inverse front. Only Clifford rotations are run in opposite
order. Every arithmetic/comparison measurement is newly emitted and proved. -/
def fusedSignedHalfUnfront (b cin low a h j l m : Wire)
    (Y R C carry : List Wire) (P : Nat) : Program :=
  let ac := carry.take (R.length-1)
  rotateLeft R ++ fusedInverseCorrectionFlagsSeed b a h j l m ++
    fusedCorrectionUndo a j l m C R ac cin P (2*P) (2^R.length-P) ++
    fusedCorrectionFlagsErase b a h j l m ++ [.CX low a] ++
    fusedInverseRawFlagClear R C carry cin h P ++ signedSub b Y R ac

theorem fusedSignedHalfUnfront_counts (b cin low a h j l m : Wire)
    (Y R C carry : List Wire) (P : Nat)
    (hY : Y.length=R.length) (hC : C.length=R.length) (hk : carry.length=R.length)
    (hw : 0<R.length) :
    toffoliCount (fusedSignedHalfUnfront b cin low a h j l m Y R C carry P)=3*R.length+1 ∧
    measurementCount (fusedSignedHalfUnfront b cin low a h j l m Y R C carry P)=3*R.length+1 := by
  let ac := carry.take (R.length-1)
  have ha : ac.length+1=R.length := by simp [ac,hk]; omega
  have hrot := rotate_counts R
  have hseed := fusedInverseCorrectionFlagsSeed_counts b a h j l m
  have hundo := fusedCorrectionUndo_counts a j l m C R ac cin P (2*P) (2^R.length-P) hC ha
  have hflags := fusedCorrectionFlags_counts b low a h j l m
  have hcmp := (compareLt_counts none R C carry cin h hC.symm (hk.trans hC.symm)).2.2 P
  have hsub := signedWord_counts b Y R ac hY ha
  have hsm : measurementCount (signedSub b Y R (carry.take (R.length-1)))=R.length-1 := hsub.2.2.2
  dsimp only [ac] at hundo hsub
  simp only [fusedSignedHalfUnfront,fusedInverseRawFlagClear,toffoliCount_append,
    measurementCount_append,hrot.2.2.1,hrot.2.2.2,hseed.1,hseed.2,hundo.1,hundo.2,
    hflags.2.2.1,hflags.2.2.2,hcmp.1,hcmp.2,hsub.2.2.1,hsm,
    show toffoliCount [.CX low a]=0 by rfl,show measurementCount [.CX low a]=0 by rfl,
    show toffoliCount [.X h]=0 by rfl,show measurementCount [.X h]=0 by rfl,
    Nat.add_zero,Nat.zero_add,hC,Option.isSome,Bool.false_eq_true,if_false]
  constructor <;> omega

def FusedUnfrontInput (b cin a h j l m : Wire) (Y R C carry : List Wire)
    (P X V : Nat) (st : BasisState) : Prop :=
  regValue Y st=V ∧ regValue R st=FusedSignedHalf.result P (st b) X V ∧
    regValue C st=0 ∧ regValue carry st=0 ∧ st cin=false ∧
    st a=FusedSignedHalf.parity (FusedSignedHalf.signedSum (st b) X V) ∧
    st h=FusedSignedHalf.reduction P (FusedSignedHalf.signedSum (st b) X V) ∧
    st j=false ∧ st l=false ∧ st m=false

def FusedUnfrontOutput (a h : Wire) (R : List Wire) (X : Nat)
    (initial out : State) : Prop :=
  out.phase=initial.phase ∧
    (∀ w,w∉R → w≠a → w≠h → out.basis w=initial.basis w) ∧
    regValue R out.basis=X ∧ out.basis a=false ∧ out.basis h=false

private theorem inverseRunSeven (p1 p2 p3 p4 p5 p6 p7 : Program) (P : State → State → Prop)
    (h : ∀ (s s1 s2 s3 s4 s5 s6 s7 : State) (m1 m2 m3 m4 m5 m6 m7 : List Bool),
      run p1 m1 s=s1 → run p2 m2 s1=s2 → run p3 m3 s2=s3 →
      run p4 m4 s3=s4 → run p5 m5 s4=s5 → run p6 m6 s5=s6 →
      run p7 m7 s6=s7 → P s s7) (s : State) (ms : List Bool) :
    P s (run (p1++(p2++(p3++(p4++(p5++(p6++p7)))))) ms s) := by
  simp only [run_append]
  apply h s _ _ _ _ _ _ _ _ _ _ _ _ _ _ <;> rfl

attribute [local irreducible] run fusedCorrectionUndo fusedInverseRawFlagClear signedSub

/-- Complete inverse front, with independently measured arithmetic, explicit
selector reconstruction and all non-target work restored. -/
theorem fusedSignedHalfUnfront_correct (b cin low a h j l m : Wire)
    (Y R C carry : List Wire) (P X V : Nat)
    (hn : ([b,a,h,j,l,m,cin]++Y++R++C++carry).Nodup)
    (hY : Y.length=R.length) (hC : C.length=R.length) (hk : carry.length=R.length)
    (hlo : ∃ tail,R=low::tail) (hw : 0<R.length)
    (hp : P%2=1) (hX : X<P) (hV : V<P) (hfit : 2*P<2^(R.length-1))
    (s : State) (record : List Bool) (hin : FusedUnfrontInput b cin a h j l m Y R C carry P X V s.basis) :
    FusedUnfrontOutput a h R X s (run (fusedSignedHalfUnfront b cin low a h j l m Y R C carry P) record s) := by
  let ac := carry.take (R.length-1)
  let Goal : State → State → Prop := fun initial out =>
    FusedUnfrontInput b cin a h j l m Y R C carry P X V initial.basis →
      FusedUnfrontOutput a h R X initial out
  have all := inverseRunSeven (rotateLeft R) (fusedInverseCorrectionFlagsSeed b a h j l m)
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
      have hpow : 2^R.length=2*2^(R.length-1) := by
        calc
          2^R.length=2^((R.length-1)+1) := by congr 1; omega
          _=2^(R.length-1)*2 := pow_succ _ _
          _=2*2^(R.length-1) := Nat.mul_comm _ _
      have hfull : 2*P<2^R.length := by omega
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
