import ECDSAAdd.Arithmetic.CompactGuardLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

attribute [local irreducible] run fusedSignedHalfUnfront fusedInverseFlagSeed

/-- Complete packed inverse endpoint, exact for every canonical input and
every measurement record. All controls, non-target bits and phase restore. -/
theorem compactInverse_correct (L : FusedHalfPorts) (hw : L.Widths) (hn : L.wires.Nodup)
    (he : L.early.Sublist L.A) (hwidth : p+1<2^L.A.length)
    (Z Y : Nat) (hZ : Z<p) (hY : Y<p) (s : State) (record : List Bool)
    (hy : regValue L.source s.basis=Y) (hz : regValue L.target s.basis=Z)
    (hC0 : regValue L.constant s.basis=0) (hk0 : regValue L.carry s.basis=0)
    (ha0 : regValue L.A s.basis=0) (hi : s.basis L.cin=false) :
    (run L.compactInverseProgram record s).phase=s.phase ∧
    (∀ w,w∉L.target → (run L.compactInverseProgram record s).basis w=s.basis w) ∧
    regValue L.target (run L.compactInverseProgram record s).basis=
      FusedSignedHalf.inverseValue (s.basis L.b) Z Y := by
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
  let X := FusedSignedHalf.inverseValue (s.basis L.b) Z Y
  have hX : X<p := FusedSignedHalf.inverseValue_bound _ _ _
  have image : FusedSignedHalf.result p (s.basis L.b) X Y=Z :=
    FusedSignedHalf.result_inverseValue _ Z Y hZ hY
  have zsmall : Z<2^L.targetLow.length := by rw [hl.2.2.2.2]; omega
  have guards := fusedCanonicalGuards L.targetLow L.qOut L.hOut s.basis Z zsmall hz
  have srcSmall : Y<2^(L.e::L.yTail).length := by
    simp only [List.length_cons,hw.source]
    omega
  have half := fusedSourceHalfValue L.e L.yTail L.yg0 L.yg1 s.basis Y srcSmall hy
  have srcGuards := fusedCanonicalGuards (L.e::L.yTail) L.yg0 L.yg1 s.basis Y srcSmall hy
  have e0 : s.basis L.e=FusedSignedHalf.parity (Y:Int) := by
    have hb := fusedWordLowBit L.e L.yTail s.basis
    rw [srcGuards.1] at hb
    rw [hb]
    apply decide_eq_decide.mpr
    change Y%2=1 ↔ (Y:Int)%2=1
    omega
  have c0 : regValue L.C s.basis=0 := (regValue_zero _ _).mpr
    (fun w hm => (regValue_zero _ _).mp hC0 w (by simp [constant,hm]))
  have k0 : regValue (L.carry.take L.A.length) s.basis=0 := (regValue_zero _ _).mpr
    (fun w hm => (regValue_zero _ _).mp hk0 w (List.mem_of_mem_take hm))
  have t0 : s.basis L.t=false := (regValue_zero _ _).mp hC0 _ (by simp [constant])
  have d0 : s.basis L.d=false := (regValue_zero _ _).mp hC0 _ (by simp [constant])
  let seed := fusedInverseFlagSeed L.b L.cin L.qOut L.hOut L.t L.d L.e
    L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length)
  obtain ⟨st1,hst1⟩ : ∃ st1 : State,run seed record s=st1 := ⟨_,rfl⟩
  have f1 := fusedInverseFlagSeed_correct L.b L.cin L.qOut L.hOut L.t L.d L.e
    L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length) X Y
    (L.back_nodup hn) (hl.2.2.2.1.trans hl.2.2.2.2.symm) hl.2.2.2.2.symm
    (hw.constant.trans hl.2.2.2.2.symm) (by simp [hw.carry,hl.2.2.2.2])
    (by rw [hl.2.2.2.2]; exact hw.min)
    (by simpa only [hl.2.2.2.2] using hwidth) hX hY s record half e0
    (guards.1.trans image.symm) ha0 c0 k0 hi t0 d0 guards.2.1 guards.2.2
  rw [hst1] at f1
  have fixed1 (w : Wire) (hwR : w∉L.target) : st1.basis w=s.basis w :=
    f1.2.1 w (fun heq => hwR (heq ▸ qr)) (fun heq => hwR (heq ▸ hr))
  let r2 := record.drop (measurementCount seed)
  obtain ⟨st2,hst2⟩ : ∃ st2 : State,run (fusedInverseFlagsMove L.a L.h L.qOut L.hOut) r2 st1=st2 := ⟨_,rfl⟩
  have f2 := fusedInverseFlagsMove_correct L.a L.h L.qOut L.hOut moveND
    (FusedSignedHalf.normalizedParity p (FusedSignedHalf.signedSum (s.basis L.b) X Y))
    (FusedSignedHalf.reduction p (FusedSignedHalf.signedSum (s.basis L.b) X Y)) st1 r2
    ((fixed1 L.a (awayR L.a (by simp [aa]))).trans ((regValue_zero _ _).mp ha0 _ aa))
    ((fixed1 L.h (awayR L.h (by simp [ah]))).trans ((regValue_zero _ _).mp ha0 _ ah))
    f1.2.2.1 f1.2.2.2
  rw [hst2] at f2
  have lowR (w : Wire) (hm : w∈L.targetLow) : w∈L.target := by simp [target,hm]
  have low1 : regValue L.targetLow st1.basis=Z := (regValue_congr _ _ _ (fun w hm =>
    f1.2.1 w (lowAway w hm).1 (lowAway w hm).2)).trans guards.1
  have low2 : regValue L.targetLow st2.basis=Z := (regValue_congr _ _ _ (fun w hm =>
    f2.2.1 w
      (by intro hwa; subst w; exact awayR L.a (by simp [aa]) (lowR _ hm))
      (by intro hwh; subst w; exact awayR L.h (by simp [ah]) (lowR _ hm))
      (lowAway w hm).1 (lowAway w hm).2)).trans low1
  have target2 : regValue L.target st2.basis=Z := by
    simp only [target,regValue_append,low2]
    simp [regValue,f2.2.2.2.2.1,f2.2.2.2.2.2]
  have fixed2 (w : Wire) (hm : w∈[L.b,L.cin]++L.source++L.constant++L.carry) :
      st2.basis w=s.basis w := by
    have hs := safe w hm
    exact (f2.2.1 w hs.2.1 hs.2.2
      (fun heq => hs.1 (heq ▸ qr)) (fun heq => hs.1 (heq ▸ hr))).trans (fixed1 w hs.1)
  have b2 : st2.basis L.b=s.basis L.b := fixed2 L.b (by simp)
  have source2 : regValue L.source st2.basis=Y := (regValue_congr _ _ _
    (fun w hm => fixed2 w (by simp [hm]))).trans hy
  have constant2 : regValue L.constant st2.basis=0 := (regValue_congr _ _ _
    (fun w hm => fixed2 w (by simp [hm]))).trans hC0
  have carry2 : regValue L.carry st2.basis=0 := (regValue_congr _ _ _
    (fun w hm => fixed2 w (by simp [hm]))).trans hk0
  have cin2 : st2.basis L.cin=false := (fixed2 L.cin (by simp)).trans hi
  have earlyND : [L.a,L.h,L.j,L.l,L.m].Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp (L.front_nodup hn he) w
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have ed := earlyND
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at ed
  have early2 (w : Wire) (hm : w∈L.A) (hwa : w≠L.a) (hwh : w≠L.h) : st2.basis w=false :=
    (f2.2.1 w hwa hwh
      (by intro heq; subst w; exact awayA L.qOut (by simp [qr]) hm)
      (by intro heq; subst w; exact awayA L.hOut (by simp [hr]) hm)).trans
      ((fixed1 w (awayR w (by simp [hm]))).trans ((regValue_zero _ _).mp ha0 w hm))
  have a2 : st2.basis L.a=FusedSignedHalf.parity (FusedSignedHalf.signedSum (st2.basis L.b) X Y) := by
    rw [f2.2.2.1,b2]
    unfold FusedSignedHalf.normalizedParity
    cases FusedSignedHalf.parity (FusedSignedHalf.signedSum (s.basis L.b) X Y) <;>
      cases FusedSignedHalf.reduction p (FusedSignedHalf.signedSum (s.basis L.b) X Y) <;> rfl
  have h2 : st2.basis L.h=FusedSignedHalf.reduction p (FusedSignedHalf.signedSum (st2.basis L.b) X Y) := by
    rw [f2.2.2.2.1,b2]
  have cw := L.compact_widths hw
  have chfit : 2*p<2^L.compactTarget.length := by
    rw [cw.2.1,pow_succ]
    omega
  have targetC2 : regValue L.compactTarget st2.basis=Z :=
    L.compact_target_value hw hwidth Z hZ st2.basis target2
  have input2 : FusedUnfrontInput L.b L.cin L.a L.h L.j L.l L.m
      L.compactSource L.compactTarget L.compactConstant L.compactCarry p X Y st2.basis :=
    ⟨L.compact_source_value hw hwidth Y hY st2.basis source2,
      by rw [targetC2,b2]; exact image.symm,
      L.compact_constant_clean st2.basis constant2,L.compact_carry_clean st2.basis carry2,
      cin2,a2,h2,early2 L.j aj (by tauto) (by tauto),
      early2 L.l al (by tauto) (by tauto),early2 L.m am (by tauto) (by tauto)⟩
  let unfront := fusedSignedHalfUnfront L.b L.cin L.low L.a L.h L.j L.l L.m
    L.compactSource L.compactTarget L.compactConstant L.compactCarry p
  obtain ⟨st3,hst3⟩ : ∃ st3 : State,run unfront r2 st2=st3 := ⟨_,rfl⟩
  have fc := compactSignedHalfUnfront_correct L.b L.cin L.low L.a L.h L.j L.l L.m
    L.compactSource L.compactTarget L.compactConstant L.compactCarry p X Y
    (L.compact_front_nodup hn he) (cw.1.trans cw.2.1.symm)
    (cw.2.2.1.trans cw.2.1.symm) (cw.2.2.2.trans cw.2.1.symm)
    (by refine ⟨L.rTail++[L.qOut],?_⟩; rfl) (by rw [cw.2.1]; omega)
    hp hX hY chfit st2 r2 input2
  change FusedUnfrontOutput L.a L.h L.compactTarget X st2 (run unfront r2 st2) at fc
  rw [hst3] at fc
  unfold FusedUnfrontOutput at fc
  have ho : L.hOut∉L.compactTarget := by
    intro hm
    have hc := List.nodup_iff_count.mp nr L.hOut
    have hh := List.count_pos_iff.mpr hm
    simp only [target,compactTarget,List.count_append,List.count_cons,List.count_nil,
      beq_self_eq_true,if_true] at hc hh
    omega
  have ha_o : L.a≠L.hOut := by tauto
  have hh_o : L.h≠L.hOut := by tauto
  have hO : st3.basis L.hOut=false :=
    (fc.2.1 L.hOut ho ha_o.symm hh_o.symm).trans f2.2.2.2.2.2
  have f3 : FusedUnfrontOutput L.a L.h L.target X st2 st3 :=
    ⟨fc.1,fun w hwR hwa hwh => fc.2.1 w
      (fun hm => hwR (L.compactTarget_sublist.subset hm)) hwa hwh,
      L.compact_target_lift st3.basis X fc.2.2.1 hO,fc.2.2.2.1,fc.2.2.2.2⟩
  unfold FusedUnfrontOutput at f3
  have moveM := (fusedInverseFlagsMove_counts L.a L.h L.qOut L.hOut).2
  have hRun : run L.compactInverseProgram record s=st3 := by
    rw [compactInverseProgram,List.append_assoc,run_append,run_take,hst1,run_append,run_take,
      moveM,List.drop_zero,hst2,hst3]
  rw [hRun]
  refine ⟨f3.1.trans (f2.1.trans f1.1),?_,f3.2.2.1⟩
  intro w hwR
  by_cases hwa : w=L.a
  · subst w
    exact f3.2.2.2.1.trans ((regValue_zero _ _).mp ha0 L.a aa).symm
  by_cases hwh : w=L.h
  · subst w
    exact f3.2.2.2.2.trans ((regValue_zero _ _).mp ha0 L.h ah).symm
  exact (f3.2.1 w hwR hwa hwh).trans ((f2.2.1 w hwa hwh
    (fun heq => hwR (heq ▸ qr)) (fun heq => hwR (heq ▸ hr))).trans (fixed1 w hwR))

end FusedHalfPorts
end ECDSAAdd.Arithmetic
