import ECDSAAdd.Arithmetic.FusedInverseSeed

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace ECDSAAdd.Arithmetic

/-- Fresh forward measured reconstruction of the reduction flag. The parity
control is preserved and all full-width scratch words restore. -/
def fusedRetainedFlagToggle (b cin q h t d e : Wire)
    (sourceHalf R A C carry : List Wire) : Program :=
  let ac := carry.take (R.length-1)
  fusedThresholdFlagsSeed b q e t d ++ fusedThresholdPrepare b sourceHalf A ++
    fusedRetainedThresholdRecover b q t d h R A C ac cin (FusedSignedHalf.halfThreshold p) (p+1) ++
    fusedThresholdUnprepare b sourceHalf A ++ fusedThresholdFlagsErase b q e t d

attribute [local irreducible] run fusedRetainedThresholdRecover

/-- Exact reduction-bit toggle for arbitrary incoming parity and reduction
flags, preserving every other bit and phase for every measurement record. -/
theorem fusedRetainedFlagToggle_correct (b cin q h t d e : Wire)
    (sourceHalf R A C carry : List Wire) (Z Y : Nat)
    (hn : ([b,q,h,t,d,e,cin]++sourceHalf++R++A++C++carry).Nodup)
    (hs : sourceHalf.length=R.length) (hA : A.length=R.length)
    (hC : C.length=R.length) (hk : carry.length=R.length)
    (hwidth : p+1<2^R.length) (hY : Y<p)
    (s : State) (record : List Bool) (hsV : regValue sourceHalf s.basis=Y/2)
    (heV : s.basis e=FusedSignedHalf.parity (Y:Int))
    (hr : regValue R s.basis=Z)
    (ha0 : regValue A s.basis=0) (hc0 : regValue C s.basis=0)
    (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false)
    (ht0 : s.basis t=false) (hd0 : s.basis d=false) :
    (run (fusedRetainedFlagToggle b cin q h t d e sourceHalf R A C carry) record s).phase=s.phase ∧
    (∀ w,w≠h → (run (fusedRetainedFlagToggle b cin q h t d e sourceHalf R A C carry) record s).basis w=s.basis w) ∧
    (run (fusedRetainedFlagToggle b cin q h t d e sourceHalf R A C carry) record s).basis h=
      ((s.basis h ^^ decide (Z<FusedSignedHalf.threshold p (s.basis b) (s.basis q) Y)) ^^ s.basis b) := by
  have bits : [b,q,h,t,d,e,cin].Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have dif := bits
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at dif
  have bh : b≠h := by tauto
  have qh : q≠h := by tauto
  have th : t≠h := by tauto
  have dh : d≠h := by tauto
  have eh : e≠h := by tauto
  have cht : cin≠h := by tauto
  have nseed : [b,q,e,t,d].Nodup := by simp; tauto
  have nprepare : (b::(sourceHalf++A)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have nrecover : ([b,q,t,d,h,cin]++R++A++C++carry).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have notA (w : Wire) (hw' : w∈[b,q,h,t,d,e,cin]++sourceHalf++R++C++carry) : w∉A := by
    intro hwA
    have hc := List.nodup_iff_count.mp hn w
    have ho := List.count_pos_iff.mpr hw'
    have hh' := List.count_pos_iff.mpr hwA
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ho
    omega
  have notTD (w : Wire) (hw' : w∈[b,q,h,e,cin]++sourceHalf++R++A++C++carry) : w≠t ∧ w≠d := by
    constructor
    · intro he; subst w
      have hc := List.nodup_iff_count.mp hn t
      have ho := List.count_pos_iff.mpr hw'
      simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hc ho
      omega
    · intro he; subst w
      have hc := List.nodup_iff_count.mp hn d
      have ho := List.count_pos_iff.mpr hw'
      simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hc ho
      omega
  have notH (w : Wire) (hw' : w∈sourceHalf++R++A++C++carry) : w≠h := by
    intro he; subst w
    have hc := List.nodup_iff_count.mp hn h
    have ho := List.count_pos_iff.mpr hw'
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hc ho
    omega
  let ac := carry.take (R.length-1)
  have hsub : ac.Sublist carry := List.take_sublist _ _
  have hpos : 0<R.length := by
    by_contra hz
    have hzero : R.length=0 := by omega
    simp [hzero] at hwidth
  have hac : ac.length+1=A.length := by simp [ac,hk,hA]; omega
  obtain ⟨st1,hst1⟩ : ∃ st1 : State, run (fusedThresholdFlagsSeed b q e t d) record s=st1 := ⟨_,rfl⟩
  obtain ⟨st2,hst2⟩ : ∃ st2 : State, run (fusedThresholdPrepare b sourceHalf A) record st1=st2 := ⟨_,rfl⟩
  have f1 := fusedThresholdFlagsSeed_correct b q e t d nseed s record ht0 hd0
  rw [hst1] at f1
  have a1 : regValue A st1.basis=0 := (regValue_congr _ _ _ (fun w hw' =>
    f1.2.1 w (notTD w (by simp [hw'])).1 (notTD w (by simp [hw'])).2)).trans ha0
  have f2 := fusedThresholdPrepare_correct b sourceHalf A nprepare (hs.trans hA.symm) st1 record a1
  rw [hst2] at f2
  have fixed2 (w : Wire) (hwA : w∉A) (hwt : w≠t) (hwd : w≠d) : st2.basis w=s.basis w :=
    (f2.2.1 w hwA).trans (f1.2.1 w hwt hwd)
  have b2 : st2.basis b=s.basis b := fixed2 b (notA b (by simp)) (by tauto) (by tauto)
  have q2 : st2.basis q=s.basis q := fixed2 q (notA q (by simp)) (by tauto) (by tauto)
  have h2 : st2.basis h=s.basis h := fixed2 h (notA h (by simp)) (by tauto) (by tauto)
  have e2 : st2.basis e=s.basis e := fixed2 e (notA e (by simp)) (by tauto) (by tauto)
  have t2 : st2.basis t=(st2.basis b&&st2.basis q) := by
    rw [f2.2.1 t (notA t (by simp)),f1.2.2.1,b2,q2]
  have d2 : st2.basis d=(!st2.basis q&&(st2.basis e^^st2.basis b)) := by
    rw [f2.2.1 d (notA d (by simp)),f1.2.2.2,b2,q2,e2]
  have R2 : regValue R st2.basis=Z := by
    exact (regValue_congr _ _ _ (fun w hw' => fixed2 w (notA w (by simp [hw']))
      (notTD w (by simp [hw'])).1 (notTD w (by simp [hw'])).2)).trans hr
  have C2 : regValue C st2.basis=0 := (regValue_congr _ _ _ (fun w hw' => fixed2 w (notA w (by simp [hw']))
    (notTD w (by simp [hw'])).1 (notTD w (by simp [hw'])).2)).trans hc0
  have K2 : regValue carry st2.basis=0 := (regValue_congr _ _ _ (fun w hw' => fixed2 w (notA w (by simp [hw']))
    (notTD w (by simp [hw'])).1 (notTD w (by simp [hw'])).2)).trans hk0
  have ac2 : regValue ac st2.basis=0 := (regValue_zero _ _).mpr
    (fun w hw' => (regValue_zero _ _).mp K2 w (hsub.subset hw'))
  have i2 : st2.basis cin=false := (fixed2 cin (notA cin (by simp)) (by tauto) (by tauto)).trans hi
  have U1 : regValue sourceHalf st1.basis=Y/2 := (regValue_congr _ _ _ (fun w hw' =>
    f1.2.1 w (notTD w (by simp [hw'])).1 (notTD w (by simp [hw'])).2)).trans hsV
  have A2 : regValue A st2.basis=signSourceValue A.length (st2.basis b) (Y/2) := by
    rw [f2.2.2,U1,f2.2.1 b (notA b (by simp))]
  let recoverProg := fusedRetainedThresholdRecover b q t d h R A C ac cin (FusedSignedHalf.halfThreshold p) (p+1)
  obtain ⟨st3,hst3⟩ : ∃ st3 : State, run recoverProg record st2=st3 := ⟨_,rfl⟩
  have nretained : ([b,q,t,d,h,cin]++R++A++C++ac).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp nrecover w
    have hs' := hsub.count_le w
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have smallK : FusedSignedHalf.halfThreshold p<2^C.length := by
    rw [hC]
    unfold FusedSignedHalf.halfThreshold
    omega
  have smallP : p+1<2^C.length := by simpa only [hC] using hwidth
  have smallOne : 1<2^C.length := by rw [hC]; omega
  have f3 := fusedRetainedThresholdRecover_correct b q t d h R A C ac cin
    (FusedSignedHalf.halfThreshold p) (p+1) nretained hA.symm
    (hC.trans hA.symm) hac smallK smallP smallOne st2 record C2 ac2 i2
  rw [hst3] at f3
  let r4 := record.drop (measurementCount recoverProg)
  obtain ⟨st4,hst4⟩ : ∃ st4 : State, run (fusedThresholdUnprepare b sourceHalf A) r4 st3=st4 := ⟨_,rfl⟩
  have unprepInput : regValue A st3.basis=signSourceValue A.length (st3.basis b) (regValue sourceHalf st3.basis) := by
    rw [(regValue_congr _ _ _ (fun w hw' => f3.2.1 w (notH w (by simp [hw'])))),
      f3.2.1 b bh,(regValue_congr _ _ _ (fun w hw' => f3.2.1 w (notH w (by simp [hw'])))),A2]
    have U2 : regValue sourceHalf st2.basis=Y/2 := (regValue_congr _ _ _ (fun w hw' =>
      f2.2.1 w (notA w (by simp [hw'])))).trans U1
    rw [U2]
  have f4 := fusedThresholdUnprepare_correct b sourceHalf A nprepare (hs.trans hA.symm) st3 r4 unprepInput
  rw [hst4] at f4
  obtain ⟨st5,hst5⟩ : ∃ st5 : State, run (fusedThresholdFlagsErase b q e t d) r4 st4=st5 := ⟨_,rfl⟩
  have t4 : st4.basis t=(st4.basis b&&st4.basis q) := by
    rw [f4.2.1 t (notA t (by simp)),f4.2.1 b (notA b (by simp)),f4.2.1 q (notA q (by simp)),
      f3.2.1 t th,f3.2.1 b bh,f3.2.1 q qh]
    exact t2
  have d4 : st4.basis d=(!st4.basis q&&(st4.basis e^^st4.basis b)) := by
    rw [f4.2.1 d (notA d (by simp)),f4.2.1 q (notA q (by simp)),f4.2.1 e (notA e (by simp)),
      f4.2.1 b (notA b (by simp)),f3.2.1 d dh,f3.2.1 q qh,f3.2.1 e eh,f3.2.1 b bh]
    exact d2
  have f5 := fusedThresholdFlagsErase_correct b q e t d nseed st4 r4 t4 d4
  rw [hst5] at f5
  have H3 : st3.basis h=
      ((s.basis h ^^ decide (Z<FusedSignedHalf.threshold p (s.basis b) (s.basis q) Y)) ^^ s.basis b) := by
    have machine := fusedThresholdMachine A.length p Y (st2.basis b) (st2.basis q)
      (by norm_num [ECDSAAdd.p]) FusedSignedHalf.secp_halfThreshold_even hY
      (by simpa only [hA] using hwidth)
    rw [f3.2.2,R2,A2,t2,d2,e2,heV,machine,b2,q2,h2]
  have prepCounts := fusedThresholdPreparation_counts b sourceHalf A (hs.trans hA.symm)
  have flagCounts := fusedThresholdFlags_counts b q e t d
  have hst1' : run (fusedThresholdFlagsSeed b q e t d) (record.take 0) s=st1 := by
    rw [←flagCounts.2.1,run_take]
    exact hst1
  have hst2' : run (fusedThresholdPrepare b sourceHalf A) (record.take 0) st1=st2 := by
    rw [←prepCounts.2.1,run_take]
    exact hst2
  have hst4' : run (fusedThresholdUnprepare b sourceHalf A) (r4.take 0) st3=st4 := by
    rw [←prepCounts.2.2.2,run_take]
    exact hst4
  have hst5' : run (fusedThresholdFlagsErase b q e t d) (r4.take 2) st4=st5 := by
    rw [←flagCounts.2.2.2,run_take]
    exact hst5
  have hRun : run (fusedRetainedFlagToggle b cin q h t d e sourceHalf R A C carry) record s=st5 := by
    simp only [fusedRetainedFlagToggle,List.append_assoc,run_append,run_take,
      flagCounts.2.1,prepCounts.2.1,prepCounts.2.2.2,List.drop_zero]
    rw [hst1',hst2',hst3,hst4']
    exact hst5
  rw [hRun]
  refine ⟨f5.1.trans (f4.1.trans (f3.1.trans (f2.1.trans f1.1))),?_,?_⟩
  · intro w hwh
    by_cases hwA : w∈A
    · exact (f5.2.1 w (notTD w (by simp [hwA])).1 (notTD w (by simp [hwA])).2).trans
        ((regValue_eq_iff A _ _).mp (f4.2.2.trans ha0.symm) w hwA)
    by_cases hwt : w=t
    · subst w; exact f5.2.2.1.trans ht0.symm
    by_cases hwd : w=d
    · subst w; exact f5.2.2.2.trans hd0.symm
    exact (f5.2.1 w hwt hwd).trans ((f4.2.1 w hwA).trans
      ((f3.2.1 w hwh).trans (fixed2 w hwA hwt hwd)))
  · exact (f5.2.1 h (by tauto) (by tauto)).trans
      ((f4.2.1 h (notA h (by simp))).trans H3)

theorem fusedRetainedFlagToggle_counts (b cin q h t d e : Wire)
    (sourceHalf R A C carry : List Wire)
    (hs : sourceHalf.length=R.length) (hA : A.length=R.length)
    (hC : C.length=R.length) (hk : carry.length=R.length) (hw : 3≤R.length) :
    toffoliCount (fusedRetainedFlagToggle b cin q h t d e sourceHalf R A C carry)=2*R.length+1 ∧
    measurementCount (fusedRetainedFlagToggle b cin q h t d e sourceHalf R A C carry)=2*R.length+1 := by
  let ac := carry.take (R.length-1)
  have hac : ac.length+1=A.length := by simp [ac,hk,hA]; omega
  have hf := fusedThresholdFlags_counts b q e t d
  have hp := fusedThresholdPreparation_counts b sourceHalf A (hs.trans hA.symm)
  have hr := fusedRetainedThresholdRecover_counts b q t d h R A C ac cin
    (FusedSignedHalf.halfThreshold p) (p+1) hA.symm (hC.trans hA.symm) hac
  dsimp only [ac] at hr
  simp only [fusedRetainedFlagToggle,toffoliCount_append,measurementCount_append,
    hf.1,hf.2.1,hf.2.2.1,hf.2.2.2,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,
    hr.1,hr.2,Nat.add_zero,Nat.zero_add,hA]
  constructor <;> omega

/-- Both inverse flags are seeded by newly emitted forward measurement streams.
No instruction with measurement is reversed. -/
def fusedInverseFlagSeed (b cin q h t d e : Wire)
    (sourceHalf R A C carry : List Wire) : Program :=
  fusedHalfParityClear R C carry cin q ++
    fusedRetainedFlagToggle b cin q h t d e sourceHalf R A C carry

theorem fusedInverseFlagSeed_counts (b cin q h t d e : Wire)
    (sourceHalf R A C carry : List Wire)
    (hs : sourceHalf.length=R.length) (hA : A.length=R.length)
    (hC : C.length=R.length) (hk : carry.length=R.length) (hw : 3≤R.length) :
    toffoliCount (fusedInverseFlagSeed b cin q h t d e sourceHalf R A C carry)=3*R.length-2 ∧
    measurementCount (fusedInverseFlagSeed b cin q h t d e sourceHalf R A C carry)=3*R.length-2 := by
  have hf := fusedRetainedFlagToggle_counts b cin q h t d e sourceHalf R A C carry hs hA hC hk hw
  have hp := fusedHalfParityClear_counts R C carry cin q hC hk
  simp only [fusedInverseFlagSeed,toffoliCount_append,measurementCount_append,
    hf.1,hf.2,hp.1,hp.2]
  constructor <;> omega

theorem fusedInverseFlagSeed_correct (b cin q h t d e : Wire)
    (sourceHalf R A C carry : List Wire) (X Y : Nat)
    (hn : ([b,q,h,t,d,e,cin]++sourceHalf++R++A++C++carry).Nodup)
    (hs : sourceHalf.length=R.length) (hA : A.length=R.length)
    (hC : C.length=R.length) (hk : carry.length=R.length) (hw : 3≤R.length)
    (hwidth : p+1<2^R.length) (hX : X<p) (hY : Y<p)
    (s : State) (record : List Bool) (hsV : regValue sourceHalf s.basis=Y/2)
    (heV : s.basis e=FusedSignedHalf.parity (Y:Int))
    (hr : regValue R s.basis=FusedSignedHalf.result p (s.basis b) X Y)
    (ha0 : regValue A s.basis=0) (hc0 : regValue C s.basis=0)
    (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false)
    (ht0 : s.basis t=false) (hd0 : s.basis d=false)
    (hq0 : s.basis q=false) (hh0 : s.basis h=false) :
    (run (fusedInverseFlagSeed b cin q h t d e sourceHalf R A C carry) record s).phase=s.phase ∧
    (∀ w,w≠q → w≠h → (run (fusedInverseFlagSeed b cin q h t d e sourceHalf R A C carry) record s).basis w=s.basis w) ∧
    (run (fusedInverseFlagSeed b cin q h t d e sourceHalf R A C carry) record s).basis q=
      FusedSignedHalf.normalizedParity p (FusedSignedHalf.signedSum (s.basis b) X Y) ∧
    (run (fusedInverseFlagSeed b cin q h t d e sourceHalf R A C carry) record s).basis h=
      FusedSignedHalf.reduction p (FusedSignedHalf.signedSum (s.basis b) X Y) := by
  have hp : p%2=1 := by norm_num [ECDSAAdd.p]
  have nparity : (q::cin::(R++C++carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have away (w : Wire) (hw' : w∈[b,h,t,d,e,cin]++sourceHalf++R++A++C++carry) : w≠q := by
    intro he
    subst w
    have hh := List.nodup_iff_count.mp hn q
    have hc := List.count_pos_iff.mpr hw'
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hh hc
    omega
  have qh : q≠h := (away h (by simp)).symm
  have hK : FusedSignedHalf.halfThreshold p<2^R.length := by
    unfold FusedSignedHalf.halfThreshold
    omega
  obtain ⟨st1,hst1⟩ : ∃ st1 : State,
    run (fusedHalfParityClear R C carry cin q) record s=st1 := ⟨_,rfl⟩
  have f1 := fusedHalfParitySeed_correct R C carry cin q nparity hw hC hk hK s record hc0 hk0 hi hq0
  rw [hst1] at f1
  have B1 : st1.basis b=s.basis b := f1.2.1 b (away b (by simp))
  have Q1 : st1.basis q=
      FusedSignedHalf.normalizedParity p (FusedSignedHalf.signedSum (s.basis b) X Y) := by
    rw [f1.2.2,hr]
    exact (FusedSignedHalf.normalizedParity_recovery p X Y (s.basis b) hp hX hY).symm
  have H1 : st1.basis h=false := (f1.2.1 h qh.symm).trans hh0
  have word (r : List Wire) (hr' : ∀ w∈r,w∈sourceHalf++R++A++C++carry) :
      regValue r st1.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw' => f1.2.1 w (away w (by
      have hm := hr' w hw'
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at hm ⊢
      tauto)))
  have half1 := (word sourceHalf (by intro w hw'; simp [hw'])).trans hsV
  have R1 := (word R (by intro w hw'; simp [hw'])).trans hr
  have A1 := (word A (by intro w hw'; simp [hw'])).trans ha0
  have C1 := (word C (by intro w hw'; simp [hw'])).trans hc0
  have K1 := (word carry (by intro w hw'; simp [hw'])).trans hk0
  let r2 := record.drop (measurementCount (fusedHalfParityClear R C carry cin q))
  have f2 := fusedRetainedFlagToggle_correct b cin q h t d e sourceHalf R A C carry
    (FusedSignedHalf.result p (s.basis b) X Y) Y hn hs hA hC hk hwidth hY st1 r2 half1
    ((f1.2.1 e (away e (by simp))).trans heV) R1 A1 C1 K1
    ((f1.2.1 cin (away cin (by simp))).trans hi)
    ((f1.2.1 t (away t (by simp))).trans ht0)
    ((f1.2.1 d (away d (by simp))).trans hd0)
  have recovery := FusedSignedHalf.reduction_recovery p X Y
    (FusedSignedHalf.result p (s.basis b) X Y) (s.basis b)
    (FusedSignedHalf.normalizedParity p (FusedSignedHalf.signedSum (s.basis b) X Y))
    (FusedSignedHalf.reduction p (FusedSignedHalf.signedSum (s.basis b) X Y)) hp hX hY
    (by
      have he := (FusedSignedHalf.result_spec p X Y (s.basis b) hp hX hY).2
      rw [FusedSignedHalf.evenLift,FusedSignedHalf.correction] at he
      cases hb : s.basis b <;> simp only [hb,Bool.false_eq_true,if_false,if_true] at he ⊢ <;> linarith)
  rw [fusedInverseFlagSeed,run_append,run_take,hst1]
  refine ⟨f2.1.trans f1.1,?_,?_,?_⟩
  · intro w hwq hwh
    exact (f2.2.1 w hwh).trans (f1.2.1 w hwq)
  · exact (f2.2.1 q qh).trans Q1
  · rw [f2.2.2,H1,B1,Q1,Bool.false_xor]
    exact recovery.symm

end ECDSAAdd.Arithmetic
