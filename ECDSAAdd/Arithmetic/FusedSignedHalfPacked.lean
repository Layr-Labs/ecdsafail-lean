import ECDSAAdd.Arithmetic.FusedSignedHalf

/-! Exact staged composition and storage packing for the signed field half. -/
namespace ECDSAAdd.Arithmetic

/-- Complete paid cleanup after flag transfer into target guards. All word
views here have n bits; the guard flags and constant selectors are outside them. -/
def fusedSignedHalfBack (b cin q h t d e : Wire) (sourceHalf R A C carry : List Wire) : Program :=
  let ac := carry.take (R.length-1)
  fusedThresholdFlagsSeed b q e t d ++ fusedThresholdPrepare b sourceHalf A ++
    fusedThresholdRecover b q t d h R A C ac carry cin (FusedSignedHalf.halfThreshold p) (p+1) ++
    fusedThresholdUnprepare b sourceHalf A ++ fusedThresholdFlagsErase b q e t d ++
    fusedHalfParityClear R C carry cin q

set_option maxHeartbeats 1500000 in
/-- All-record exact back composition: both retained flags become zero, every
other bit restores its input value, and phase is preserved. -/
theorem fusedSignedHalfBack_correct (b cin q h t d e : Wire) (sourceHalf R A C carry : List Wire)
    (X Y : Nat) (hn : ([b,q,h,t,d,e,cin]++sourceHalf++R++A++C++carry).Nodup)
    (hs : sourceHalf.length=R.length) (hA : A.length=R.length)
    (hC : C.length=R.length) (hk : carry.length=R.length) (hw : 3≤R.length)
    (hwidth : p+1<2^R.length) (hX : X<p) (hY : Y<p)
    (s : State) (record : List Bool) (hsV : regValue sourceHalf s.basis=Y/2)
    (heV : s.basis e=FusedSignedHalf.parity (Y:Int))
    (hr : regValue R s.basis=FusedSignedHalf.result p (s.basis b) X Y)
    (ha0 : regValue A s.basis=0) (hc0 : regValue C s.basis=0)
    (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false)
    (ht0 : s.basis t=false) (hd0 : s.basis d=false)
    (hq : s.basis q=FusedSignedHalf.normalizedParity p (FusedSignedHalf.signedSum (s.basis b) X Y))
    (hh : s.basis h=FusedSignedHalf.reduction p (FusedSignedHalf.signedSum (s.basis b) X Y)) :
    (run (fusedSignedHalfBack b cin q h t d e sourceHalf R A C carry) record s).phase=s.phase ∧
    (∀ w,w≠q → w≠h → (run (fusedSignedHalfBack b cin q h t d e sourceHalf R A C carry) record s).basis w=s.basis w) ∧
    (run (fusedSignedHalfBack b cin q h t d e sourceHalf R A C carry) record s).basis q=false ∧
    (run (fusedSignedHalfBack b cin q h t d e sourceHalf R A C carry) record s).basis h=false := by
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
  have nparity : (q::cin::(R++C++carry)).Nodup := by
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
  have R2 : regValue R st2.basis=FusedSignedHalf.result p (st2.basis b) X Y := by
    rw [b2]
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
  let recoverProg := fusedThresholdRecover b q t d h R A C ac carry cin (FusedSignedHalf.halfThreshold p) (p+1)
  obtain ⟨st3,hst3⟩ : ∃ st3 : State, run recoverProg record st2=st3 := ⟨_,rfl⟩
  have f3 := fusedThresholdRecover_shared_clears b q t d h R A C ac carry cin p X Y nrecover hsub hA.symm
    (hC.trans hA.symm) hac (hk.trans hA.symm) (by norm_num [ECDSAAdd.p]) FusedSignedHalf.secp_halfThreshold_even
    hX hY (by simpa only [hA] using hwidth) st2 record C2 ac2 K2 i2
    (by simpa only [q2,b2] using hq) (by simpa only [h2,b2] using hh) t2
    (by simpa only [e2,heV] using d2) R2 A2
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
  have word5 (r : List Wire) (hr' : ∀ w∈r,w∈R++C++carry) : regValue r st5.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw' => by
      have hm' := hr' w hw'
      exact (f5.2.1 w (notTD w (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm' ⊢; tauto)).1 (notTD w (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm' ⊢; tauto)).2).trans
        ((f4.2.1 w (notA w (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm' ⊢; tauto))).trans ((f3.2.1 w (notH w (by simp only [List.mem_append] at hm' ⊢; tauto))).trans
          (fixed2 w (notA w (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm' ⊢; tauto)) (notTD w (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm' ⊢; tauto)).1 (notTD w (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm' ⊢; tauto)).2))))
  have R5 := (word5 R (by intro w hw'; simp [hw'])).trans hr
  have C5 := (word5 C (by intro w hw'; simp [hw'])).trans hc0
  have K5 := (word5 carry (by intro w hw'; simp [hw'])).trans hk0
  have i5 : st5.basis cin=false := (f5.2.1 cin (by tauto) (by tauto)).trans
    ((f4.2.1 cin (notA cin (by simp))).trans ((f3.2.1 cin cht).trans i2))
  have q5 : st5.basis q=FusedSignedHalf.normalizedParity p (FusedSignedHalf.signedSum (s.basis b) X Y) :=
    (f5.2.1 q (by tauto) (by tauto)).trans ((f4.2.1 q (notA q (by simp))).trans
      ((f3.2.1 q qh).trans (q2.trans hq)))
  let r6 := record.drop (measurementCount recoverProg+2)
  have f6 := fusedHalfParityClear_from_result R C carry cin q X Y (s.basis b) nparity hw hC hk
    (by omega) st5 r6 C5 K5 i5 hX hY R5 q5
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
  have hRun : run (fusedSignedHalfBack b cin q h t d e sourceHalf R A C carry) record s=
      run (fusedHalfParityClear R C carry cin q) r6 st5 := by
    simp only [fusedSignedHalfBack,List.append_assoc,run_append,run_take,
      flagCounts.2.1,flagCounts.2.2.2,prepCounts.2.1,prepCounts.2.2.2,List.drop_zero]
    rw [hst1',hst2',hst3,hst4',hst5',List.drop_drop]
  rw [hRun]
  refine ⟨f6.1.trans (f5.1.trans (f4.1.trans (f3.1.trans (f2.1.trans f1.1)))),?_,f6.2.2,?_⟩
  · intro w hwq hwh
    by_cases hwA : w∈A
    · exact (f6.2.1 w hwq).trans ((f5.2.1 w (notTD w (by simp [hwA])).1 (notTD w (by simp [hwA])).2).trans
        ((regValue_eq_iff A _ _).mp (f4.2.2.trans ha0.symm) w hwA))
    by_cases hwt : w=t
    · subst w; exact (f6.2.1 t hwq).trans (f5.2.2.1.trans ht0.symm)
    by_cases hwd : w=d
    · subst w; exact (f6.2.1 d hwq).trans (f5.2.2.2.trans hd0.symm)
    exact (f6.2.1 w hwq).trans ((f5.2.1 w hwt hwd).trans ((f4.2.1 w hwA).trans
      ((f3.2.1 w hwh).trans (fixed2 w hwA hwt hwd))))
  · exact (f6.2.1 h qh.symm).trans ((f5.2.1 h (by tauto) (by tauto)).trans
      ((f4.2.1 h (notA h (by simp))).trans f3.2.2))

/-- Cleanup costs include the exact old-reduction and normalized-parity comparators. -/
theorem fusedSignedHalfBack_counts (b cin q h t d e : Wire) (sourceHalf R A C carry : List Wire)
    (hs : sourceHalf.length=R.length) (hA : A.length=R.length)
    (hC : C.length=R.length) (hk : carry.length=R.length) (hw : 3≤R.length) :
    toffoliCount (fusedSignedHalfBack b cin q h t d e sourceHalf R A C carry)=4*R.length-3 ∧
    measurementCount (fusedSignedHalfBack b cin q h t d e sourceHalf R A C carry)=4*R.length-3 := by
  let ac := carry.take (R.length-1)
  have hac : ac.length+1=A.length := by simp [ac,hk,hA]; omega
  have hf := fusedThresholdFlags_counts b q e t d
  have hp := fusedThresholdPreparation_counts b sourceHalf A (hs.trans hA.symm)
  have hr := fusedThresholdRecover_counts b q t d h R A C ac carry cin (FusedSignedHalf.halfThreshold p) (p+1)
    hA.symm (hC.trans hA.symm) hac (hk.trans hA.symm)
  have hq := fusedHalfParityClear_counts R C carry cin q hC hk
  dsimp only [ac] at hr
  constructor
  · simp only [fusedSignedHalfBack,toffoliCount_append,hf.1,hf.2.2.1,hp.1,hp.2.2.1,hr.1,hq.1,Nat.add_zero,hA]
    omega
  · simp only [fusedSignedHalfBack,measurementCount_append,hf.2.1,hf.2.2.2,hp.2.1,hp.2.2.2,hr.2,hq.2,Nat.add_zero,Nat.zero_add,hA]
    omega

/-- Packed fused-half ports: five early flags are borrowed from A, target guards
hold two retained flags later, and constant guards hold two threshold selectors.
All arithmetic chains use prefixes of a single full carry array. -/
structure FusedHalfPorts where
  b : Wire
  cin : Wire
  low : Wire
  e : Wire
  a : Wire
  h : Wire
  j : Wire
  l : Wire
  m : Wire
  qOut : Wire
  hOut : Wire
  t : Wire
  d : Wire
  yg0 : Wire
  yg1 : Wire
  rTail : List Wire
  yTail : List Wire
  C : List Wire
  A : List Wire
  carry : List Wire

namespace FusedHalfPorts

def targetLow (L : FusedHalfPorts) : List Wire := L.low::L.rTail
def source (L : FusedHalfPorts) : List Wire := (L.e::L.yTail)++[L.yg0,L.yg1]
def sourceHalf (L : FusedHalfPorts) : List Wire := L.yTail++[L.yg0]
def target (L : FusedHalfPorts) : List Wire := L.targetLow++[L.qOut,L.hOut]
def constant (L : FusedHalfPorts) : List Wire := L.C++[L.t,L.d]
def early (L : FusedHalfPorts) : List Wire := [L.a,L.h,L.j,L.l,L.m]
def wires (L : FusedHalfPorts) : List Wire := L.b::L.cin::(L.source++L.target++L.constant++L.carry++L.A)

def program (L : FusedHalfPorts) : Program :=
  fusedSignedHalfCandidate L.b L.cin L.low L.hOut L.a L.h L.j L.l L.m L.qOut L.hOut L.t L.d L.e
    L.source L.target L.constant L.carry L.A L.sourceHalf p

structure Widths (L : FusedHalfPorts) : Prop where
  min : 3≤L.A.length
  source : L.yTail.length+1=L.A.length
  target : L.rTail.length+1=L.A.length
  constant : L.C.length=L.A.length
  carry : L.carry.length=L.A.length+2

/-- Full and projected word lengths are exact physical lengths. -/
theorem widths (L : FusedHalfPorts) (hw : L.Widths) :
    L.source.length=L.A.length+2 ∧ L.target.length=L.A.length+2 ∧
    L.constant.length=L.A.length+2 ∧ L.sourceHalf.length=L.A.length ∧
    L.targetLow.length=L.A.length := by
  simp only [source,target,constant,sourceHalf,targetLow,List.length_append,List.length_cons,
    List.length_nil,hw.source,hw.target,hw.constant]
  trivial

/-- Early borrowed flag placements are valid for the complete front capsule. -/
theorem front_nodup (L : FusedHalfPorts) (hn : L.wires.Nodup) (he : L.early.Sublist L.A) :
    ([L.b,L.a,L.h,L.j,L.l,L.m,L.cin]++L.source++L.target++L.constant++L.carry).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have hc := List.nodup_iff_count.mp hn w
  have hp := he.count_le w
  simp only [wires,early,List.count_cons,List.count_append,List.count_nil] at hc hp ⊢
  omega

/-- Reusing target guards needs only already disjoint physical ports. -/
theorem move_nodup (L : FusedHalfPorts) (hn : L.wires.Nodup) (he : L.early.Sublist L.A) :
    [L.a,L.h,L.qOut,L.hOut].Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have hc := List.nodup_iff_count.mp hn w
  have hp := he.count_le w
  simp only [wires,early,target,List.count_cons,List.count_append,List.count_nil] at hc hp ⊢
  omega

/-- Late views exclude their live target/constant guard flags. The half-source
view retains one exact zero source guard and skips the other. -/
theorem back_nodup (L : FusedHalfPorts) (hn : L.wires.Nodup) :
    ([L.b,L.qOut,L.hOut,L.t,L.d,L.e,L.cin]++L.sourceHalf++L.targetLow++L.A++L.C++
      L.carry.take L.A.length).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have hc := List.nodup_iff_count.mp hn w
  have hk := (List.take_sublist L.A.length L.carry).count_le w
  simp only [wires,source,sourceHalf,target,constant,List.count_cons,List.count_append,List.count_nil] at hc ⊢
  omega

/-- Count the same emitted packed-port program; storage aliases do not add gates. -/
theorem counts (L : FusedHalfPorts) (hw : L.Widths) :
    toffoliCount L.program=7*L.A.length+3 ∧ measurementCount L.program=7*L.A.length+4 := by
  have hl := L.widths hw
  exact fusedSignedHalfCandidate_counts L.b L.cin L.low L.hOut L.a L.h L.j L.l L.m L.qOut L.hOut L.t L.d L.e
    L.source L.target L.constant L.carry L.A L.sourceHalf p hw.min hl.2.1
    (hl.1.trans hl.2.1.symm) (hl.2.2.1.trans hl.2.1.symm)
    (hw.carry.trans hl.2.1.symm) hl.2.2.2.1

/-- The packed stream is exactly front, physical guard transfer, then complete
back cleanup. No measurement instruction is reversed. -/
theorem program_eq_stages (L : FusedHalfPorts) (hw : L.Widths) :
    L.program=
      fusedSignedHalfFront L.b L.cin L.low L.hOut L.a L.h L.j L.l L.m L.source L.target L.constant L.carry p ++
      fusedFlagsMove L.a L.h L.qOut L.hOut ++
      fusedSignedHalfBack L.b L.cin L.qOut L.hOut L.t L.d L.e L.sourceHalf L.targetLow L.A L.C
        (L.carry.take L.A.length) := by
  have hl := L.widths hw
  have ht : L.target.take L.A.length=L.targetLow := by
    have hs := List.take_of_length_le (le_of_eq hl.2.2.2.2)
    simp only [target,List.take_append,hl.2.2.2.2,Nat.sub_self,List.take_zero,List.append_nil,hs]
  have hc : L.constant.take L.A.length=L.C := by
    have hs := List.take_of_length_le (le_of_eq hw.constant)
    simp only [constant,List.take_append,hw.constant,Nat.sub_self,List.take_zero,List.append_nil,hs]
  simp only [program,fusedSignedHalfCandidate,fusedSignedHalfFront,fusedSignedHalfBack,
    fusedThresholdPrepare,fusedThresholdUnprepare,ht,hc,hl.2.2.2.2,List.take_take,
    Nat.min_eq_left (Nat.sub_le _ _),List.append_assoc]

set_option maxHeartbeats 1000000 in
/-- Complete packed signed-half endpoint. Early flags are borrowed from A;
late flags occupy target and constant guards. Every non-target wire, phase and
complete scratch word restore for every independent measurement record. -/
theorem correct (L : FusedHalfPorts) (hw : L.Widths) (hn : L.wires.Nodup)
    (he : L.early.Sublist L.A) (hwidth : p+1<2^L.A.length)
    (X Y : Nat) (hX : X<p) (hY : Y<p) (s : State) (record : List Bool)
    (hy : regValue L.source s.basis=Y) (hx : regValue L.target s.basis=X)
    (hC0 : regValue L.constant s.basis=0) (hk0 : regValue L.carry s.basis=0)
    (ha0 : regValue L.A s.basis=0) (hi : s.basis L.cin=false) :
    (run L.program record s).phase=s.phase ∧
    (∀ w,w∉L.target → (run L.program record s).basis w=s.basis w) ∧
    regValue L.target (run L.program record s).basis=FusedSignedHalf.result p (s.basis L.b) X Y := by
  have hl := L.widths hw
  have hc (w : Wire) := List.nodup_iff_count.mp hn w
  have earlyA (w : Wire) (hm : w∈L.early) : w∈L.A := he.subset hm
  have aa : L.a∈L.A := earlyA L.a (by simp [early])
  have ah : L.h∈L.A := earlyA L.h (by simp [early])
  have aj : L.j∈L.A := earlyA L.j (by simp [early])
  have al : L.l∈L.A := earlyA L.l (by simp [early])
  have am : L.m∈L.A := earlyA L.m (by simp [early])
  have awayR (w : Wire) (hm : w∈[L.b,L.cin]++L.source++L.constant++L.carry++L.A) : w∉L.target := by
    intro hr
    have h1 := hc w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    simp only [wires,List.count_cons,List.count_append,List.count_nil] at h1 h2
    omega
  have awayA (w : Wire) (hm : w∈[L.b,L.cin]++L.source++L.target++L.constant++L.carry) : w∉L.A := by
    intro hr
    have h1 := hc w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    simp only [wires,List.count_cons,List.count_append,List.count_nil] at h1 h2
    omega
  have safe (w : Wire) (hm : w∈[L.b,L.cin]++L.source++L.constant++L.carry) : w∉L.target ∧ w≠L.a ∧ w≠L.h := by
    refine ⟨awayR w (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm ⊢; tauto),?_,?_⟩
    · intro hh; subst w; exact awayA L.a (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm ⊢; tauto) aa
    · intro hh; subst w; exact awayA L.h (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm ⊢; tauto) ah
  have qr : L.qOut∈L.target := by simp [target]
  have hr : L.hOut∈L.target := by simp [target]
  have nr : L.target.Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h1 := hc w
    simp only [wires,List.count_cons,List.count_append] at h1
    omega
  have lowAway (w : Wire) (hm : w∈L.targetLow) : w≠L.qOut ∧ w≠L.hOut := by
    have hd := (List.nodup_append'.mp nr).2.2
    have hnot := List.disjoint_left.mp hd hm
    simpa only [List.mem_cons,List.mem_nil_iff,not_or,not_false_eq_true,and_true] using hnot
  have moveND := L.move_nodup hn he
  have md := moveND
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at md
  have hp : p%2=1 := by norm_num [ECDSAAdd.p]
  have hwR : 0<L.target.length := by omega
  have hfit : 2*p<2^(L.target.length-1) := by
    rw [hl.2.1,show L.A.length+2-1=L.A.length+1 by omega,pow_succ]
    omega
  let front := fusedSignedHalfFront L.b L.cin L.low L.hOut L.a L.h L.j L.l L.m L.source L.target L.constant L.carry p
  obtain ⟨st1,hst1⟩ : ∃ st1 : State, run front record s=st1 := ⟨_,rfl⟩
  have f1 := fusedSignedHalfFront_correct L.b L.cin L.low L.hOut L.a L.h L.j L.l L.m L.source L.target L.constant L.carry
    p X Y (L.front_nodup hn he) (hl.1.trans hl.2.1.symm) (hl.2.2.1.trans hl.2.1.symm)
    (hw.carry.trans hl.2.1.symm)
    (by refine ⟨L.rTail++[L.qOut,L.hOut],?_⟩; rfl)
    (by refine ⟨L.targetLow++[L.qOut],?_⟩; simp [target,List.append_assoc]) hwR hp hX hY hfit s record hy hx hC0 hk0 hi
    ((regValue_zero _ _).mp ha0 L.a aa) ((regValue_zero _ _).mp ha0 L.h ah)
    ((regValue_zero _ _).mp ha0 L.j aj) ((regValue_zero _ _).mp ha0 L.l al) ((regValue_zero _ _).mp ha0 L.m am)
  rw [hst1] at f1
  let Z := FusedSignedHalf.result p (s.basis L.b) X Y
  have hz : Z<2^L.targetLow.length := by
    have h := (FusedSignedHalf.result_spec p X Y (s.basis L.b) hp hX hY).1
    rw [hl.2.2.2.2]
    omega
  have guards := fusedCanonicalGuards L.targetLow L.qOut L.hOut st1.basis Z hz f1.2.2.1
  let r2 := record.drop (measurementCount front)
  obtain ⟨st2,hst2⟩ : ∃ st2 : State, run (fusedFlagsMove L.a L.h L.qOut L.hOut) r2 st1=st2 := ⟨_,rfl⟩
  have f2 := fusedFlagsMove_correct L.a L.h L.qOut L.hOut moveND st1 r2 guards.2.1 guards.2.2
  rw [hst2] at f2
  have lowR (w : Wire) (hm : w∈L.targetLow) : w∈L.target := by simp [target,hm]
  have movedR : regValue L.targetLow st2.basis=Z := (regValue_congr _ _ _ (fun w hm => f2.2.1 w
    (by intro hh; subst w; exact awayR L.a (by simp [aa]) (lowR _ hm))
    (by intro hh; subst w; exact awayR L.h (by simp [ah]) (lowR _ hm)) (lowAway w hm).1 (lowAway w hm).2)).trans guards.1
  have movedA : regValue L.A st2.basis=0 := (regValue_zero _ _).mpr (by
    intro w hm
    by_cases hwa : w=L.a
    · subst w; exact f2.2.2.1
    by_cases hwh : w=L.h
    · subst w; exact f2.2.2.2.1
    have hwq : w≠L.qOut := by intro hh; subst w; exact awayA L.qOut (by simp [qr]) hm
    have hwo : w≠L.hOut := by intro hh; subst w; exact awayA L.hOut (by simp [hr]) hm
    exact (f2.2.1 w hwa hwh hwq hwo).trans ((f1.2.1 w (awayR w (by simp [hm])) hwa hwh).trans
      ((regValue_zero _ _).mp ha0 w hm)))
  have fixed2 (w : Wire) (hm : w∈[L.b,L.cin]++L.source++L.constant++L.carry) : st2.basis w=s.basis w := by
    have hs := safe w hm
    have hwq : w≠L.qOut := by intro hh; subst w; exact hs.1 qr
    have hwo : w≠L.hOut := by intro hh; subst w; exact hs.1 hr
    exact (f2.2.1 w hs.2.1 hs.2.2 hwq hwo).trans (f1.2.1 w hs.1 hs.2.1 hs.2.2)
  have b2 : st2.basis L.b=s.basis L.b := fixed2 L.b (by simp)
  have source2 : regValue L.source st2.basis=Y := (regValue_congr _ _ _ (fun w hm => fixed2 w (by simp [hm]))).trans hy
  have srcSmall : Y<2^(L.e::L.yTail).length := by
    simp only [List.length_cons,hw.source]
    omega
  have half2 := fusedSourceHalfValue L.e L.yTail L.yg0 L.yg1 st2.basis Y srcSmall source2
  have srcGuards := fusedCanonicalGuards (L.e::L.yTail) L.yg0 L.yg1 st2.basis Y srcSmall source2
  have e2 : st2.basis L.e=FusedSignedHalf.parity (Y:Int) := by
    have hb := fusedWordLowBit L.e L.yTail st2.basis
    rw [srcGuards.1] at hb
    rw [hb]
    apply decide_eq_decide.mpr
    change Y%2=1 ↔ (Y:Int)%2=1
    omega
  have cc2 : regValue L.C st2.basis=0 := (regValue_zero _ _).mpr (by
    intro w hm
    have hmem : w∈L.constant := by simp [constant,hm]
    exact (fixed2 w (by simp [hmem])).trans ((regValue_zero _ _).mp hC0 w hmem))
  have k2 : regValue (L.carry.take L.A.length) st2.basis=0 := (regValue_zero _ _).mpr (by
    intro w hm
    have hmem := List.mem_of_mem_take hm
    exact (fixed2 w (by simp [hmem])).trans ((regValue_zero _ _).mp hk0 w hmem))
  have i2 : st2.basis L.cin=false := (fixed2 L.cin (by simp)).trans hi
  have t2 : st2.basis L.t=false := (fixed2 L.t (by simp [constant])).trans
    ((regValue_zero _ _).mp hC0 L.t (by simp [constant]))
  have d2 : st2.basis L.d=false := (fixed2 L.d (by simp [constant])).trans
    ((regValue_zero _ _).mp hC0 L.d (by simp [constant]))
  have q2 : st2.basis L.qOut=FusedSignedHalf.normalizedParity p (FusedSignedHalf.signedSum (st2.basis L.b) X Y) := by
    rw [f2.2.2.2.2.1,f1.2.2.2.1,f1.2.2.2.2,b2]
    rfl
  have h2 : st2.basis L.hOut=FusedSignedHalf.reduction p (FusedSignedHalf.signedSum (st2.basis L.b) X Y) := by
    rw [f2.2.2.2.2.2,f1.2.2.2.2,b2]
  let back := fusedSignedHalfBack L.b L.cin L.qOut L.hOut L.t L.d L.e L.sourceHalf L.targetLow L.A L.C
    (L.carry.take L.A.length)
  obtain ⟨st3,hst3⟩ : ∃ st3 : State, run back r2 st2=st3 := ⟨_,rfl⟩
  have f3 := fusedSignedHalfBack_correct L.b L.cin L.qOut L.hOut L.t L.d L.e L.sourceHalf L.targetLow L.A L.C
    (L.carry.take L.A.length) X Y (L.back_nodup hn) (hl.2.2.2.1.trans hl.2.2.2.2.symm)
    hl.2.2.2.2.symm (hw.constant.trans hl.2.2.2.2.symm)
    (by simp [hw.carry,hl.2.2.2.2]) (by rw [hl.2.2.2.2]; exact hw.min) (by simpa only [hl.2.2.2.2] using hwidth)
    hX hY st2 r2 half2 e2 (by simpa only [b2] using movedR) movedA cc2 k2 i2 t2 d2 q2 h2
  rw [hst3] at f3
  have target3 : regValue L.target st3.basis=Z := by
    have low3 : regValue L.targetLow st3.basis=Z := (regValue_congr _ _ _ (fun w hm =>
      f3.2.1 w (lowAway w hm).1 (lowAway w hm).2)).trans movedR
    rw [target,regValue_append]
    change regValue L.targetLow st3.basis+2^L.targetLow.length*
      ((if st3.basis L.qOut then 1 else 0)+2*(if st3.basis L.hOut then 1 else 0))=Z
    rw [f3.2.2.1,f3.2.2.2]
    simpa only [Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] using low3
  have hRun : run L.program record s=st3 := by
    rw [L.program_eq_stages hw,List.append_assoc,run_append,run_take,hst1,run_append,run_take]
    simp only [(fusedFlagsMove_counts L.a L.h L.qOut L.hOut).2,List.drop_zero]
    rw [hst2,hst3]
  rw [hRun]
  refine ⟨f3.1.trans (f2.1.trans f1.1),?_,target3⟩
  intro w hwR
  have hwq : w≠L.qOut := by intro hh; subst w; exact hwR qr
  have hwo : w≠L.hOut := by intro hh; subst w; exact hwR hr
  rw [f3.2.1 w hwq hwo]
  by_cases hmA : w∈L.A
  · exact ((regValue_zero _ _).mp movedA w hmA).trans (((regValue_zero _ _).mp ha0 w hmA).symm)
  have hwa : w≠L.a := by intro hh; subst w; exact hmA aa
  have hwh : w≠L.h := by intro hh; subst w; exact hmA ah
  exact (f2.2.1 w hwa hwh hwq hwo).trans (f1.2.1 w hwR hwa hwh)

end FusedHalfPorts


end ECDSAAdd.Arithmetic
