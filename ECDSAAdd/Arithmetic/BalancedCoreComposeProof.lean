import ECDSAAdd.Arithmetic.BalancedCoreComposeViews

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField BalancedFold

def coreProgram (L : Layout) : Program :=
  seedViews L++(rawAdd L++(prepareFold L++(fold L++
    (rotateRight (rawTarget L)++releaseSelectors L))))

def coreClean (L : Layout) : List Wire := [L.cout,L.minus,L.plus,L.lower,L.one]++L.carry

theorem coreClean_sub_work (L : Layout) (q : Wire) (hq : q∈coreClean L) : q∈work L := by
  simp only [coreClean,work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
  tauto

theorem program_eq_core (L : Layout) : program L=coreProgram L++
    BalancedCleanup.program L.toLayout++[.CX L.ymsb L.sourceGuard] := by
  simp only [program,coreProgram,List.append_assoc]

/-- Full forward balanced core, for arbitrary incoming phase and every
measurement stream. Its two retained views are exactly the raw parity and
the original source sign. All remaining work is clean. -/
theorem core_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (coreProgram L) m s
    t.phase=s.phase ∧
    regValue L.r t.basis=encodeWord 256 (halfResult (rawSum B X Y)) ∧
    t.basis L.parity=originalParity (rawSum B X Y) ∧
    t.basis L.sourceGuard=s.basis L.ymsb ∧
    (∀q∈coreClean L,t.basis q=false) ∧
    (∀q,q∉L.r → q≠L.parity → q≠L.sourceGuard → t.basis q=s.basis q) := by
  let T := rawSum B X Y
  let P := originalParity T
  let N := decide (T<0)
  let H := negative (halfResult T)
  let m₁ := m.drop (measurementCount (rawAdd L))
  let m₂ := m₁.drop (measurementCount (fold L))
  generalize eu : run (seedViews L) m s = u
  generalize ev : run (rawAdd L) m u = v
  generalize ew : run (prepareFold L) m₁ v = w
  generalize ez : run (fold L) m₁ w = z
  generalize ea : run (rotateRight (rawTarget L)) m₂ z = a
  generalize et : run (releaseSelectors L) m₂ a = t
  have ht := rawSum_bounds B X Y hx hy
  have ndR := List.nodup_reverse.mpr (scalarND L hn)
  simp only [List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ndR
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9,h0_10⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩,⟨h5_6,h5_7,h5_8,h5_9,h5_10⟩,⟨h6_7,h6_8,h6_9,h6_10⟩,⟨h7_8,h7_9,h7_10⟩,⟨h8_9,h8_10⟩,h9_10⟩
  rcases ndR with ⟨⟨r0_1,r0_2,r0_3,r0_4,r0_5,r0_6,r0_7,r0_8,r0_9,r0_10⟩,⟨r1_2,r1_3,r1_4,r1_5,r1_6,r1_7,r1_8,r1_9,r1_10⟩,⟨r2_3,r2_4,r2_5,r2_6,r2_7,r2_8,r2_9,r2_10⟩,⟨r3_4,r3_5,r3_6,r3_7,r3_8,r3_9,r3_10⟩,⟨r4_5,r4_6,r4_7,r4_8,r4_9,r4_10⟩,⟨r5_6,r5_7,r5_8,r5_9,r5_10⟩,⟨r6_7,r6_8,r6_9,r6_10⟩,⟨r7_8,r7_9,r7_10⟩,⟨r8_9,r8_10⟩,r9_10⟩
  have su := compose_seed_frame L hw hn s m hc
  rw [eu] at su
  have sv := seed_raw_signed L hw hn B X Y hx hy s m hs hr hyr hc
  simp only [run_append] at sv
  simp only [run_take] at sv
  simp only [show measurementCount (seedViews L)=0 from rfl,List.drop_zero] at sv
  rw [eu,ev] at sv
  have cu := (seed_signed L hw hn X Y s m hr hyr hc).2.2
  rw [eu] at cu
  have rf (q : Wire) (hq : q∉rawTarget L) : v.basis q=u.basis q :=
    by simpa only [ev] using rawAdd_frame L hw hn u m cu q hq
  have away (q : Wire)
      (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      q∉rawTarget L := compose_raw_away L hn q hq
  have vp : v.basis L.parity=P :=
    (rf _ (away _ (by simp))).trans (by simpa only [eu] using seed_parity L hw hn B X Y s m hr hyr hc)
  have vo : v.basis L.one=N := word_sign L.r L.one v.basis T sv.2.1
  have vr : v.basis L.r0=P := by
    apply word_parity L.r0 (L.rtail++[L.rmsb,L.one]) v.basis T
    simpa [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc] using sv.2.1
  have vz (q : Wire) (hq : q∈[L.cout,L.minus,L.plus,L.lower]++L.carry) : v.basis q=false := by
    have cv := compose_clean_views L hn q hq
    have qo : q≠L.one := fun e => cv.1 (e ▸ (by simp [rawTarget]))
    exact (rf q cv.1).trans ((su.2.2 q cv.2.1 qo cv.2.2.1).trans (hc q cv.2.2.2))
  have wp := compose_prepare_bits L hn P N v m₁ vp vo vr
    (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp))
  rw [ew] at wp
  have pf (q : Wire) (hq : q∉rawTarget L) (hl : q≠L.lower)
      (hm : q≠L.minus) (hu : q≠L.plus) : w.basis q=v.basis q :=
    by
      simpa only [ew] using (compose_prepare_frame L hn P N v m₁ vp vo vr
        (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp)) q hq hl hm hu)
  have wpar : w.basis L.parity=P := by
    exact (pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans vp
  have wc : w.basis L.cout=false := by
    exact (pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans (vz _ (by simp))
  have wcarry : regValue L.carry w.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have qne (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
        q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
    exact (pf q (away q (by simp [hq])) (qne _ (by simp))
      (qne _ (by simp)) (qne _ (by simp))).trans (vz q (by simp [hq]))
  have prepared := prepare_upper L hw hn T v m₁ sv.2.1 vp
    (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp))
  rw [ew] at prepared
  have zw := fold_correct L hw hn T ht w m₁ wpar
    wp.2.2.2.2.1 wp.2.2.2.1 wc wcarry prepared
  rw [ez] at zw
  have z0 : z.basis L.r0=false :=
    (zw.2.2.2 _ (compose_not_fold_r0 L hn)).trans wp.2.1
  have az := rotate_folded L hw hn T ht z m₂ z0 zw.2.1
  rw [ea] at az
  have af (q : Wire) (hq : q∉rawTarget L) : a.basis q=w.basis q :=
    (az.2.2.2 q hq).trans (zw.2.2.2 q (compose_fold_subset L q hq))
  have ah : a.basis L.rmsb=H :=
    BalancedCleanup.result_msb L.toLayout hw (halfResult T) (halfResult_spec T ht).1 a.basis az.2.1
  have hp : a.basis L.parity=P := (af _ (away _ (by simp))).trans wpar
  have hsign : H=(N ^^ P) := halfResult_sign T ht
  have al : a.basis L.lower=(H ^^ P) := by
    rw [af _ (away _ (by simp)),wp.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have am : a.basis L.minus=(P && !H) := by
    rw [af _ (away _ (by simp)),wp.2.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have au : a.basis L.plus=(P ^^ (P && !H)) := by
    rw [af _ (away _ (by simp)),wp.2.2.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have ta := compose_release_frame L hn P H a m₂ hp ah al am au
  rw [et] at ta
  have tf (q : Wire) (hl : q≠L.lower) (hm : q≠L.minus) (hu : q≠L.plus) :
      t.basis q=a.basis q := ta.2.2.2.2 q hl hm hu
  have tr : regValue L.r t.basis=encodeWord 256 (halfResult T) := by
    apply Eq.trans _ az.2.1
    apply regValue_congr
    intro q hq
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
        q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
    exact tf q (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  have tp : t.basis L.parity=P := by
    exact (tf _ (by assumption) (by assumption) (by assumption)).trans hp
  have tg : t.basis L.sourceGuard=s.basis L.ymsb := by
    exact (tf _ (by assumption) (by assumption) (by assumption)).trans
      ((af _ (away _ (by simp))).trans
        ((pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans
          ((rf _ (away _ (by simp))).trans su.2.1)))
  have tz : ∀q∈coreClean L,t.basis q=false := by
    intro q hq
    simp only [coreClean,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|hq
    · exact (tf _ (by assumption) (by assumption) (by assumption)).trans
        ((az.2.2.2 _ (away _ (by simp))).trans zw.2.2.1)
    · exact ta.2.2.1
    · exact ta.2.2.2.1
    · exact ta.2.1
    · exact (tf _ (by assumption) (by assumption) (by assumption)).trans az.2.2.1
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
          q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
      exact (tf q (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((af q (away q (by simp [hq]))).trans
          ((pf q (away q (by simp [hq])) (neq _ (by simp)) (neq _ (by simp))
            (neq _ (by simp))).trans (vz q (by simp [hq]))))
  have frame : ∀q,q∉L.r → q≠L.parity → q≠L.sourceGuard → t.basis q=s.basis q := by
    intro q hqr hqp hqg
    by_cases hq : q∈coreClean L
    · exact (tz q hq).trans (hc q (coreClean_sub_work L q hq)).symm
    · have qo : q≠L.one := fun e => hq (by simp [coreClean,e])
      have ql : q≠L.lower := fun e => hq (by simp [coreClean,e])
      have qm : q≠L.minus := fun e => hq (by simp [coreClean,e])
      have qu : q≠L.plus := fun e => hq (by simp [coreClean,e])
      have qa : q∉rawTarget L := by simpa only [rawTarget,List.mem_append,
        List.mem_singleton,not_or] using And.intro hqr qo
      exact (tf q ql qm qu).trans ((af q qa).trans ((pf q qa ql qm qu).trans
        ((rf q qa).trans (su.2.2 q hqg qo hqp))))
  have actual : run (coreProgram L) m s=t := by
    simp only [coreProgram,run_append]
    simp only [run_take]
    simp only [
      show measurementCount (seedViews L)=0 from rfl,
      show measurementCount (prepareFold L)=0 from rfl,
      (rotate_counts (rawTarget L)).2.1,List.drop_zero]
    rw [eu,ev,ew,ez,ea,et]
  rw [actual]
  exact ⟨ta.1.trans (az.1.trans (zw.1.trans (wp.1.trans sv.1))),tr,tp,tg,tz,frame⟩

end ECDSAAdd.Arithmetic.BalancedCircuit

#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.core_correct
