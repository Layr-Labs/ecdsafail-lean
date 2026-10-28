import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.MaskedConstant
import ECDSAAdd.Arithmetic.Constant

namespace ECDSAAdd.Arithmetic
open Instr Correction

/-- 正分支返回后，以CX切到负分支；子树共用后续scratch，最后清负AND。 -/
private def lookupWalk (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat) : Program :=
  match controls, scratch with
  | [], _ => maskedConstant a target (table 0)
  | b::bs, q::qs =>
      [CCX a b q] ++ lookupWalk q bs qs target (fun d => table (1+2*d)) ++
      [CX a q] ++ lookupWalk q bs qs target (fun d => table (2*d)) ++
      [X b, measureX q [] [CZ a b], X b]
  | _::_, [] => []

private theorem eraseNegative_run (a b q : Wire) (hab : a≠b) (hbq : b≠q) (haq : a≠q)
    (s : State) (m : List Bool) (hq : s.basis q=(s.basis a && !s.basis b)) :
    run [X b,measureX q [] [CZ a b],X b] m s = ⟨s.phase,writeBit s.basis q false⟩ := by
  simp only [run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect,correct,writeBit,hab,hbq,hbq.symm,haq,hq]
  all_goals
    funext w
    by_cases hw : w=b
    · subst w; simp [hbq]
    · simp [Function.update_apply,hw]

private theorem lookupWalk_correct (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hnd : (a::(controls++scratch++target)).Nodup)
    (hlen : scratch.length=controls.length)
    (ht : ∀ d<2^controls.length, table d<2^target.length)
    (s : State) (m : List Bool) (hz : ∀ w∈scratch, s.basis w=false) :
    (run (lookupWalk a controls scratch target table) m s).phase=s.phase ∧
    (∀ w, w∉target → (run (lookupWalk a controls scratch target table) m s).basis w=s.basis w) ∧
    regValue target (run (lookupWalk a controls scratch target table) m s).basis =
      regValue target s.basis ^^^ (if s.basis a then table (regValue controls s.basis) else 0) := by
  induction controls generalizing a scratch table s m with
  | nil =>
    have hn := List.nodup_cons.mp hnd
    have htn := (List.nodup_append.mp (by simpa using hn.2)).2.1
    have ha : a∉target := by intro h; exact hn.1 (by simp [h])
    simpa [lookupWalk,regValue] using maskedConstant_correct a target (table 0) htn ha (ht 0 (by simp)) s m
  | cons b bs ih =>
    cases scratch with
    | nil => simp at hlen
    | cons q qs =>
      have hn : (q::(bs++qs++target)).Nodup := by
        apply List.nodup_iff_count.mpr; intro w
        have h := List.nodup_iff_count.mp hnd w
        simp only [List.count_cons,List.count_append] at h ⊢; omega
      have hqnot := (List.nodup_cons.mp hn).1
      have hanot := (List.nodup_cons.mp hnd).1
      have hbnot := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
      have hab : a≠b := by intro h; subst a; exact hanot (by simp)
      have haq : a≠q := by intro h; subst a; exact hanot (by simp)
      have hbq : b≠q := by intro h; subst b; exact hbnot (by simp)
      have haT : a∉target := by intro h; exact hanot (by simp [h])
      have hbT : b∉target := by intro h; exact hbnot (by simp [h])
      have hqT : q∉target := by intro h; exact hqnot (by simp [h])
      have hbsq (w : Wire) (hw : w∈bs) : w≠q := by intro h; subst w; exact hqnot (by simp [hw])
      have hqsq (w : Wire) (hw : w∈qs) : w≠q := by intro h; subst w; exact hqnot (by simp [hw])
      have hbsT (w : Wire) (hw : w∈bs) : w∉target := by
        intro hwT
        have h := List.nodup_iff_count.mp hn w
        have h1 := List.count_pos_iff.mpr hw
        have h2 := List.count_pos_iff.mpr hwT
        simp only [List.count_cons,List.count_append] at h; omega
      have hqsT (w : Wire) (hw : w∈qs) : w∉target := by
        intro hwT
        have h := List.nodup_iff_count.mp hn w
        have h1 := List.count_pos_iff.mpr hw
        have h2 := List.count_pos_iff.mpr hwT
        simp only [List.count_cons,List.count_append] at h; omega
      have ht1 : ∀ d<2^bs.length, table (1+2*d)<2^target.length := by
        intro d hd; apply ht; simp only [List.length_cons,Nat.pow_succ]; omega
      have ht0 : ∀ d<2^bs.length, table (2*d)<2^target.length := by
        intro d hd; apply ht; simp only [List.length_cons,Nat.pow_succ]; omega
      let p := lookupWalk q bs qs target (fun d => table (1+2*d))
      let r := lookupWalk q bs qs target (fun d => table (2*d))
      let s1 : State := ⟨s.phase,writeBit s.basis q (s.basis a && s.basis b)⟩
      have s1out (w : Wire) (hw : w≠q) : s1.basis w=s.basis w := by simp [s1,writeBit,hw]
      have hz1 : ∀ w∈qs, s1.basis w=false := by
        intro w hw; rw [s1out w (hqsq w hw)]; exact hz w (by simp [hw])
      have hlen' : qs.length=bs.length := by simpa using hlen
      obtain ⟨hp1,ho1,hv1⟩ := ih q qs (fun d => table (1+2*d)) hn hlen' ht1 s1 m hz1
      let t := run p m s1
      change t.phase=s1.phase at hp1
      change ∀ w, w∉target → t.basis w=s1.basis w at ho1
      change regValue target t.basis=_ at hv1
      have ta : t.basis a=s.basis a := (ho1 a haT).trans (s1out a haq)
      have tb : t.basis b=s.basis b := (ho1 b hbT).trans (s1out b hbq)
      have tq : t.basis q=(s.basis a && s.basis b) := by rw [ho1 q hqT]; simp [s1,writeBit]
      let s2 : State := ⟨t.phase,writeBit t.basis q (t.basis q ^^ t.basis a)⟩
      have s2q : s2.basis q=(s.basis a && !s.basis b) := by
        simp only [s2,writeBit,Function.update_self,ta,tq]
        cases s.basis a <;> cases s.basis b <;> rfl
      have s2out (w : Wire) (hw : w≠q) : s2.basis w=t.basis w := by simp [s2,writeBit,hw]
      have hz2 : ∀ w∈qs, s2.basis w=false := by
        intro w hw; rw [s2out w (hqsq w hw),ho1 w (hqsT w hw)]; exact hz1 w hw
      let m2 := m.drop (measurementCount p)
      obtain ⟨hp2,ho2,hv2⟩ := ih q qs (fun d => table (2*d)) hn hlen' ht0 s2 m2 hz2
      let v := run r m2 s2
      change v.phase=s2.phase at hp2
      change ∀ w, w∉target → v.basis w=s2.basis w at ho2
      change regValue target v.basis=_ at hv2
      have va : v.basis a=s.basis a := (ho2 a haT).trans ((s2out a haq).trans ta)
      have vb : v.basis b=s.basis b := (ho2 b hbT).trans ((s2out b hbq).trans tb)
      have vq : v.basis q=(v.basis a && !v.basis b) := by rw [va,vb,ho2 q hqT,s2q]
      have first (records : List Bool) : run [CCX a b q] records s=s1 := by simp [run,s1,hz q (by simp)]
      have hrun : run (lookupWalk a (b::bs) (q::qs) target table) m s =
          ⟨s.phase,writeBit v.basis q false⟩ := by
        change run ([CCX a b q] ++ p ++ [CX a q] ++ r ++ [X b,measureX q [] [CZ a b],X b]) m s = _
        simp only [List.append_assoc,run_append,run_take,measurementCount,List.drop_zero]
        rw [first]
        change run [X b,measureX q [] [CZ a b],X b] (m2.drop (measurementCount r)) v = _
        rw [eraseNegative_run a b q hab hbq haq v _ vq]
        have hp : v.phase=s.phase := hp2.trans hp1
        rw [hp]
      rw [hrun]
      refine ⟨rfl,?_,?_⟩
      · intro w hw
        by_cases h : w=q
        · subst w; simp [writeBit,hz q (by simp)]
        · simpa [writeBit,h] using (ho2 w hw).trans ((s2out w h).trans ((ho1 w hw).trans (s1out w h)))
      · have hout : regValue target (writeBit v.basis q false)=regValue target v.basis := by
          apply regValue_congr; intro w hw; simp [writeBit,show w≠q by intro h; subst w; exact hqT hw]
        have ht2 : regValue target s2.basis=regValue target t.basis := by
          apply regValue_congr; intro w hw; exact s2out w (by intro h; subst w; exact hqT hw)
        have ht1' : regValue target s1.basis=regValue target s.basis := by
          apply regValue_congr; intro w hw; exact s1out w (by intro h; subst w; exact hqT hw)
        have hb1 : regValue bs s1.basis=regValue bs s.basis :=
          regValue_congr _ _ _ (fun w hw => s1out w (hbsq w hw))
        have hb2 : regValue bs s2.basis=regValue bs s.basis := by
          apply regValue_congr; intro w hw
          exact (s2out w (hbsq w hw)).trans ((ho1 w (hbsT w hw)).trans (s1out w (hbsq w hw)))
        simp only [hout,hv2,ht2,hv1,ht1',hb1,hb2,s2q]
        have hq1 : s1.basis q=(s.basis a && s.basis b) := by simp [s1,writeBit]
        rw [hq1]
        cases ha : s.basis a <;> cases hb : s.basis b <;> simp [hb,regValue]

/-- 无外部控制：a本身使能第一半表，翻转a使能第二半表，末尾还原。 -/
def lookup (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat) : Program :=
  lookupWalk a controls scratch target (fun d => table (1+2*d)) ++ [X a] ++
  lookupWalk a controls scratch target (fun d => table (2*d)) ++ [X a]

/-- 查表保持地址与目标外所有线路，对全部测量记录恢复相位。 -/
private theorem lookup_correct_length (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hnd : (a::(controls++scratch++target)).Nodup)
    (hlen : scratch.length=controls.length)
    (ht : ∀ j<2^(controls.length+1), table j<2^target.length)
    (s : State) (m : List Bool) (hz : ∀ w∈scratch, s.basis w=false) :
    (run (lookup a controls scratch target table) m s).phase=s.phase ∧
    (∀ w, w∉target → (run (lookup a controls scratch target table) m s).basis w=s.basis w) ∧
    regValue target (run (lookup a controls scratch target table) m s).basis =
      regValue target s.basis ^^^ table (regValue (a::controls) s.basis) := by
  have hanot := (List.nodup_cons.mp hnd).1
  have haT : a∉target := by intro h; exact hanot (by simp [h])
  have hca (w : Wire) (hw : w∈controls) : w≠a := by intro h; subst w; exact hanot (by simp [hw])
  have hsa (w : Wire) (hw : w∈scratch) : w≠a := by intro h; subst w; exact hanot (by simp [hw])
  have hcT (w : Wire) (hw : w∈controls) : w∉target := by
    intro ht'
    have h := List.nodup_iff_count.mp hnd w
    have h1 := List.count_pos_iff.mpr hw
    have h2 := List.count_pos_iff.mpr ht'
    simp only [List.count_cons,List.count_append] at h; omega
  have hsT (w : Wire) (hw : w∈scratch) : w∉target := by
    intro ht'
    have h := List.nodup_iff_count.mp hnd w
    have h1 := List.count_pos_iff.mpr hw
    have h2 := List.count_pos_iff.mpr ht'
    simp only [List.count_cons,List.count_append] at h; omega
  have ht1 : ∀ d<2^controls.length, table (1+2*d)<2^target.length := by
    intro d hd; apply ht; rw [Nat.pow_succ]; omega
  have ht0 : ∀ d<2^controls.length, table (2*d)<2^target.length := by
    intro d hd; apply ht; rw [Nat.pow_succ]; omega
  let p := lookupWalk a controls scratch target (fun d => table (1+2*d))
  let r := lookupWalk a controls scratch target (fun d => table (2*d))
  let t := run p m s
  obtain ⟨hp1,ho1,hv1⟩ := lookupWalk_correct a controls scratch target _ hnd hlen ht1 s m hz
  change t.phase=s.phase at hp1
  change ∀ w, w∉target → t.basis w=s.basis w at ho1
  change regValue target t.basis=_ at hv1
  let s2 : State := ⟨t.phase,writeBit t.basis a (!t.basis a)⟩
  have s2a : s2.basis a= !s.basis a := by simp [s2,writeBit,ho1 a haT]
  have s2out (w : Wire) (hw : w≠a) : s2.basis w=t.basis w := by simp [s2,writeBit,hw]
  have hz2 : ∀ w∈scratch, s2.basis w=false := by
    intro w hw; rw [s2out w (hsa w hw),ho1 w (hsT w hw)]; exact hz w hw
  let m2 := m.drop (measurementCount p)
  let v := run r m2 s2
  obtain ⟨hp2,ho2,hv2⟩ := lookupWalk_correct a controls scratch target _ hnd hlen ht0 s2 m2 hz2
  change v.phase=s2.phase at hp2
  change ∀ w, w∉target → v.basis w=s2.basis w at ho2
  change regValue target v.basis=_ at hv2
  have va : v.basis a= !s.basis a := (ho2 a haT).trans s2a
  have hrun : run (lookup a controls scratch target table) m s =
      ⟨v.phase,writeBit v.basis a (!v.basis a)⟩ := by
    simp only [lookup,List.append_assoc,run_append,run_take,measurementCount,List.drop_zero]
    rfl
  rw [hrun]
  refine ⟨hp2.trans hp1,?_,?_⟩
  · intro w hw
    by_cases h : w=a
    · subst w; simp [writeBit,va]
    · simpa [writeBit,h] using (ho2 w hw).trans ((s2out w h).trans (ho1 w hw))
  · have hout : regValue target (writeBit v.basis a (!v.basis a))=regValue target v.basis := by
      apply regValue_congr; intro w hw; simp [writeBit,show w≠a by intro h; subst w; exact haT hw]
    have ht2 : regValue target s2.basis=regValue target t.basis := by
      apply regValue_congr; intro w hw; exact s2out w (by intro h; subst w; exact haT hw)
    have hctrl : regValue controls s2.basis=regValue controls s.basis := by
      apply regValue_congr; intro w hw
      exact (s2out w (hca w hw)).trans (ho1 w (hcT w hw))
    simp only [hout,hv2,ht2,hv1,hctrl,s2a]
    cases ha : s.basis a <;> simp [regValue,ha]

theorem lookup_correct (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hnd : (a::(controls++scratch++target)).Nodup)
    (hc : controls.length=3) (hs : scratch.length=3)
    (ht : ∀ j<16, table j<2^target.length)
    (s : State) (m : List Bool) (hz : ∀ w∈scratch, s.basis w=false) :
    (run (lookup a controls scratch target table) m s).phase=s.phase ∧
    (∀ w, w∉target → (run (lookup a controls scratch target table) m s).basis w=s.basis w) ∧
    regValue target (run (lookup a controls scratch target table) m s).basis =
      regValue target s.basis ^^^ table (regValue (a::controls) s.basis) := by
  apply lookup_correct_length a controls scratch target table hnd (hs.trans hc.symm)
  · simpa only [hc] using ht
  · exact hz
/-- 公开寄存器接口；工作辅助位初末均为零。 -/
theorem lookup_spec (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hnd : (a::(controls++scratch++target)).Nodup)
    (hc : controls.length=3) (hs : scratch.length=3)
    (ht : ∀ j<16, table j<2^target.length) (D T : Nat) :
    {{ (a::controls) = D, target = T, scratch = 0 }} lookup a controls scratch target table
    {{ (a::controls) = D, target = (T ^^^ table D), scratch = 0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hz : ∀ w∈scratch, s.basis w=false := (regValue_zero scratch s.basis).mp h.2
  obtain ⟨hp,ho,hv⟩ := lookup_correct a controls scratch target table hnd hc hs ht s m hz
  have hd : ((a::controls++scratch)++target).Nodup := by simpa using hnd
  have hn := (List.nodup_append.mp hd).2.2
  have ha : regValue (a::controls) (run (lookup a controls scratch target table) m s).basis=D := by
    rw [← h.1.1]; apply regValue_congr; intro w hw
    apply ho w; intro ht; exact hn w (by simp only [List.cons_append,List.mem_cons,List.mem_append] at hw ⊢; tauto) w ht rfl
  have hw : regValue scratch (run (lookup a controls scratch target table) m s).basis=0 := by
    rw [← h.2]; apply regValue_congr; intro w hw
    apply ho w; intro ht; exact hn w (by simp [hw]) w ht rfl
  exact ⟨hp,⟨ha,by simpa [h.1.1,h.1.2] using hv⟩,hw⟩

private theorem lookupWalk_counts (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hlen : scratch.length=controls.length) :
    toffoliCount (lookupWalk a controls scratch target table)=2^controls.length-1 ∧
    measurementCount (lookupWalk a controls scratch target table)=2^controls.length-1 := by
  induction controls generalizing a scratch table with
  | nil => simp [lookupWalk,(maskedConstant_counts a target (table 0)).1,(maskedConstant_counts a target (table 0)).2]
  | cons b bs ih =>
    cases scratch with
    | nil => simp at hlen
    | cons q qs =>
      have h1 := ih q qs (fun d => table (1+2*d)) (by simpa using hlen)
      have h0 := ih q qs (fun d => table (2*d)) (by simpa using hlen)
      have hpos := Nat.two_pow_pos bs.length
      simp [lookupWalk,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,h1,h0,Nat.pow_succ]
      omega

/-- 两半表各七个前缀AND；加载与重跑清理都是同一14/14门列。 -/
theorem lookup_counts (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hc : controls.length=3) (hs : scratch.length=3) :
    toffoliCount (lookup a controls scratch target table)=14 ∧
    measurementCount (lookup a controls scratch target table)=14 := by
  have h1 := lookupWalk_counts a controls scratch target (fun d => table (1+2*d)) (hs.trans hc.symm)
  have h0 := lookupWalk_counts a controls scratch target (fun d => table (2*d)) (hs.trans hc.symm)
  simp [lookup,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,h1,h0,hc]

private theorem lookupWalk_wires_subset (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat) :
    wires (lookupWalk a controls scratch target table) ⊆ (a::controls++scratch++target).toFinset := by
  induction controls generalizing a scratch table with
  | nil =>
    intro w hw
    have h := maskedConstant_wires_subset a target (table 0) hw
    simpa [lookupWalk] using (show w∈(a::[]++scratch++target).toFinset by
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢; tauto)
  | cons b bs ih =>
    cases scratch with
    | nil => simp [lookupWalk,wires]
    | cons q qs =>
      intro w hw
      simp only [lookupWalk,wires_append,wires,Instr.wires,correctionWires,
        Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hw
      have h1 := @ih q qs (fun d => table (1+2*d)) w
      have h0 := @ih q qs (fun d => table (2*d)) w
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h1 h0 ⊢
      tauto

/-- 与表项无关，单迭代门列触及全部地址和三根scratch。 -/
theorem lookup_core_wires (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hc : controls.length=3) (hs : scratch.length=3) :
    (a::controls++scratch).toFinset ⊆ wires (lookup a controls scratch target table) := by
  obtain ⟨b,c,d,rfl⟩ := List.length_eq_three.mp hc
  obtain ⟨u,v,w,rfl⟩ := List.length_eq_three.mp hs
  intro q hq
  simp only [lookup,lookupWalk,wires_append,wires,Instr.wires,correctionWires]
  simp only [List.toFinset_cons,List.toFinset_nil,Finset.mem_insert,
    Finset.notMem_empty,or_false,List.cons_append,List.nil_append] at hq
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false]
  tauto

/-- 目标中恒零的表列不一定触及；只承诺实际支持的包含关系。 -/
theorem lookup_wires_subset (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat) :
    wires (lookup a controls scratch target table) ⊆ (a::controls++scratch++target).toFinset := by
  intro w hw
  simp only [lookup,wires_append,wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,
    Finset.notMem_empty,or_false] at hw
  have h1 := @lookupWalk_wires_subset a controls scratch target (fun d => table (1+2*d)) w
  have h0 := @lookupWalk_wires_subset a controls scratch target (fun d => table (2*d)) w
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h1 h0 ⊢
  tauto
/-- 比支持集更强的frame：所有目标外线路（包括控制与scratch）初末相同。 -/
theorem lookup_frame (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hnd : (a::(controls++scratch++target)).Nodup)
    (hc : controls.length=3) (hs : scratch.length=3)
    (ht : ∀ j<16, table j<2^target.length)
    (s : State) (m : List Bool) (hz : regValue scratch s.basis=0) (w : Wire) (hw : w∉target) :
    (run (lookup a controls scratch target table) m s).basis w=s.basis w :=
  (lookup_correct a controls scratch target table hnd hc hs ht s m ((regValue_zero _ _).mp hz)).2.1 w hw

private theorem lookupWalk_core (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hlen : scratch.length=controls.length) :
    (controls++scratch).toFinset ⊆ wires (lookupWalk a controls scratch target table) := by
  induction controls generalizing a scratch table with
  | nil =>
    have : scratch=[] := by simpa using hlen
    simp [this]
  | cons b bs ih =>
    cases scratch with
    | nil => simp at hlen
    | cons q qs =>
      have h := ih q qs (fun d => table (1+2*d)) (by simpa using hlen)
      intro w hw
      have hh := @h w
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at hw hh
      simp only [lookupWalk,wires_append,wires,Instr.wires,correctionWires,
        Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false]
      tauto

/-- 十位地址和九根scratch均在实际支持内，与表值无关。 -/
theorem lookup10_core_wires (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hc : controls.length=9) (hs : scratch.length=9) :
    (a::controls++scratch).toFinset ⊆ wires (lookup a controls scratch target table) := by
  have h := lookupWalk_core a controls scratch target (fun d => table (1+2*d)) (hs.trans hc.symm)
  intro w hw
  have hh := @h w
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw hh
  simp only [lookup,wires_append,wires,Instr.wires,Finset.mem_union,
    Finset.mem_singleton,Finset.notMem_empty,or_false]
  tauto

/-- 十位计数查表：同一递归门列，九根scratch。 -/
theorem lookup10_correct (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hnd : (a::(controls++scratch++target)).Nodup)
    (hc : controls.length=9) (hs : scratch.length=9)
    (ht : ∀ j<1024, table j<2^target.length)
    (s : State) (m : List Bool) (hz : ∀ w∈scratch, s.basis w=false) :
    (run (lookup a controls scratch target table) m s).phase=s.phase ∧
    (∀ w, w∉target → (run (lookup a controls scratch target table) m s).basis w=s.basis w) ∧
    regValue target (run (lookup a controls scratch target table) m s).basis =
      regValue target s.basis ^^^ table (regValue (a::controls) s.basis) := by
  apply lookup_correct_length a controls scratch target table hnd (hs.trans hc.symm)
  · simpa only [hc] using ht
  · exact hz

theorem lookup10_spec (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hnd : (a::(controls++scratch++target)).Nodup)
    (hc : controls.length=9) (hs : scratch.length=9)
    (ht : ∀ j<1024, table j<2^target.length) (D T : Nat) :
    {{ (a::controls) = D, target = T, scratch = 0 }} lookup a controls scratch target table
    {{ (a::controls) = D, target = (T ^^^ table D), scratch = 0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hz : ∀ w∈scratch, s.basis w=false := (regValue_zero scratch s.basis).mp h.2
  obtain ⟨hp,ho,hv⟩ := lookup10_correct a controls scratch target table hnd hc hs ht s m hz
  have hd : ((a::controls++scratch)++target).Nodup := by simpa using hnd
  have hn := (List.nodup_append.mp hd).2.2
  have ha : regValue (a::controls) (run (lookup a controls scratch target table) m s).basis=D := by
    rw [← h.1.1]; apply regValue_congr; intro w hw
    apply ho w; intro ht; exact hn w (by simp only [List.cons_append,List.mem_cons,List.mem_append] at hw ⊢; tauto) w ht rfl
  have hw : regValue scratch (run (lookup a controls scratch target table) m s).basis=0 := by
    rw [← h.2]; apply regValue_congr; intro w hw
    apply ho w; intro ht; exact hn w (by simp [hw]) w ht rfl
  exact ⟨hp,⟨ha,by simpa [h.1.1,h.1.2] using hv⟩,hw⟩

theorem lookup10_counts (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hc : controls.length=9) (hs : scratch.length=9) :
    toffoliCount (lookup a controls scratch target table)=1022 ∧
    measurementCount (lookup a controls scratch target table)=1022 := by
  have h1 := lookupWalk_counts a controls scratch target (fun d => table (1+2*d)) (hs.trans hc.symm)
  have h0 := lookupWalk_counts a controls scratch target (fun d => table (2*d)) (hs.trans hc.symm)
  simp [lookup,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,h1,h0,hc]

theorem lookup10_frame (a : Wire) (controls scratch target : List Wire) (table : Nat → Nat)
    (hnd : (a::(controls++scratch++target)).Nodup)
    (hc : controls.length=9) (hs : scratch.length=9)
    (ht : ∀ j<1024, table j<2^target.length)
    (s : State) (m : List Bool) (hz : regValue scratch s.basis=0) (w : Wire) (hw : w∉target) :
    (run (lookup a controls scratch target table) m s).basis w=s.basis w :=
  (lookup10_correct a controls scratch target table hnd hc hs ht s m ((regValue_zero _ _).mp hz)).2.1 w hw

private theorem lookupWalk_physical (a : Wire) (controls scratch target : List Wire)
    (table : Nat → Nat) (hn : (a :: controls ++ scratch ++ target).Nodup) :
    GatePhysical (lookupWalk a controls scratch target table) := by
  induction controls generalizing a scratch table with
  | nil =>
    apply maskedConstant_physical
    intro h
    exact (List.nodup_cons.mp hn).1 (by simp [h])
  | cons b bs ih =>
    cases scratch with
    | nil => simp [lookupWalk,GatePhysical]
    | cons q qs =>
      have ht : (q :: bs ++ qs ++ target).Nodup := by
        apply List.nodup_iff_count.mpr; intro w
        have h := List.nodup_iff_count.mp hn w
        simp only [List.count_cons,List.count_append] at h ⊢; omega
      have haq : a ≠ q := by
        intro e; subst q
        have h := List.nodup_iff_count.mp hn a
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
      have hbq : b ≠ q := by
        intro e; subst q
        have h := List.nodup_iff_count.mp hn b
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
      have left := ih q qs (fun d => table (1+2*d)) ht
      have right := ih q qs (fun d => table (2*d)) ht
      simp only [lookupWalk,gatePhysical_append]
      refine ⟨⟨⟨⟨?_,left⟩,?_⟩,right⟩,?_⟩
      all_goals simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,haq,hbq]

/-- Every ordinary lookup gate has distinct target and controls; this is
independent of the lookup values and of the clean-state correctness contract. -/
theorem lookup_physical (a : Wire) (controls scratch target : List Wire)
    (table : Nat → Nat) (hn : (a :: controls ++ scratch ++ target).Nodup) :
    GatePhysical (lookup a controls scratch target table) := by
  simp only [lookup,gatePhysical_append]
  refine ⟨⟨⟨lookupWalk_physical _ _ _ _ _ hn,?_⟩,lookupWalk_physical _ _ _ _ _ hn⟩,?_⟩
  all_goals simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]

end ECDSAAdd.Arithmetic
