import ECDSAAdd.Arithmetic.CompactGuardLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

attribute [local irreducible] run compactSignedHalfFront

/-- Complete compact forward endpoint under the existing wide caller interface.
The separate borrowed normalization flag is restored before returning. -/
theorem compactForward_correct (L : FusedHalfPorts) (hw : L.Widths) (hn : L.wires.Nodup)
    (he : L.early.Sublist L.A) (hwidth : p+1<2^L.A.length)
    (X Y : Nat) (hX : X<p) (hY : Y<p) (s : State) (record : List Bool)
    (hy : regValue L.source s.basis=Y) (hx : regValue L.target s.basis=X)
    (hC0 : regValue L.constant s.basis=0) (hk0 : regValue L.carry s.basis=0)
    (ha0 : regValue L.A s.basis=0) (hi : s.basis L.cin=false) :
    (run L.compactForwardProgram record s).phase=s.phase ∧
    (∀ w,w∉L.target → (run L.compactForwardProgram record s).basis w=s.basis w) ∧
    regValue L.target (run L.compactForwardProgram record s).basis=
      FusedSignedHalf.result p (s.basis L.b) X Y := by
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
  have cw := L.compact_widths hw
  have chfit : 2*p<2^L.compactTarget.length := by
    rw [cw.2.1,pow_succ]
    omega
  let front := compactSignedHalfFront L.b L.cin L.low L.a L.h L.j L.l L.m
    L.compactSource L.compactTarget L.compactConstant L.compactCarry p
  obtain ⟨st1,hst1⟩ : ∃ st1 : State,run front record s=st1 := ⟨_,rfl⟩
  have fc := compactSignedHalfFront_correct L.b L.cin L.low L.a L.h L.j L.l L.m
    L.compactSource L.compactTarget L.compactConstant L.compactCarry p X Y
    (L.compact_front_nodup hn he) (cw.1.trans cw.2.1.symm)
    (cw.2.2.1.trans cw.2.1.symm) (cw.2.2.2.trans cw.2.1.symm)
    (by refine ⟨L.rTail++[L.qOut],?_⟩; rfl) (by rw [cw.2.1]; omega)
    hp hX hY chfit s record
    (L.compact_source_value hw hwidth Y hY s.basis hy)
    (L.compact_target_value hw hwidth X hX s.basis hx)
    (L.compact_constant_clean s.basis hC0) (L.compact_carry_clean s.basis hk0) hi
    ((regValue_zero _ _).mp ha0 L.a aa) ((regValue_zero _ _).mp ha0 L.h ah)
    ((regValue_zero _ _).mp ha0 L.j aj) ((regValue_zero _ _).mp ha0 L.l al)
    ((regValue_zero _ _).mp ha0 L.m am)
  change (run front record s).phase=s.phase ∧ _ at fc
  rw [hst1] at fc
  have ho : L.hOut∉L.compactTarget := by
    intro hm
    have hc := List.nodup_iff_count.mp nr L.hOut
    have hh := List.count_pos_iff.mpr hm
    simp only [target,compactTarget,List.count_append,List.count_cons,List.count_nil,
      beq_self_eq_true,if_true] at hc hh
    omega
  have ha_o : L.a≠L.hOut := by tauto
  have hh_o : L.h≠L.hOut := by tauto
  have xsmall : X<2^L.targetLow.length := by rw [hl.2.2.2.2]; omega
  have initialGuards := fusedCanonicalGuards L.targetLow L.qOut L.hOut s.basis X xsmall hx
  have hO : st1.basis L.hOut=false :=
    (fc.2.1 L.hOut ho ha_o.symm hh_o.symm).trans initialGuards.2.2
  have f1 : st1.phase=s.phase ∧
      (∀ w,w∉L.target → w≠L.a → w≠L.h → st1.basis w=s.basis w) ∧
      regValue L.target st1.basis=FusedSignedHalf.result p (s.basis L.b) X Y ∧
      st1.basis L.a=FusedSignedHalf.parity (FusedSignedHalf.signedSum (s.basis L.b) X Y) ∧
      st1.basis L.h=FusedSignedHalf.reduction p (FusedSignedHalf.signedSum (s.basis L.b) X Y) :=
    ⟨fc.1,fun w hwR hwa hwh => fc.2.1 w
      (fun hm => hwR (L.compactTarget_sublist.subset hm)) hwa hwh,
      L.compact_target_lift st1.basis _ fc.2.2.1 hO,fc.2.2.2.1,fc.2.2.2.2⟩
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
  let back := fusedSignedHalfRetainedBack L.b L.cin L.qOut L.hOut L.t L.d L.e L.sourceHalf L.targetLow L.A L.C
    (L.carry.take L.A.length)
  obtain ⟨st3,hst3⟩ : ∃ st3 : State, run back r2 st2=st3 := ⟨_,rfl⟩
  have f3 := fusedSignedHalfRetainedBack_correct L.b L.cin L.qOut L.hOut L.t L.d L.e L.sourceHalf L.targetLow L.A L.C
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
  have hRun : run L.compactForwardProgram record s=st3 := by
    rw [compactForwardProgram,List.append_assoc,run_append,run_take,hst1,run_append,run_take]
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
