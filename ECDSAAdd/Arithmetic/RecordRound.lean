import ECDSAAdd.Arithmetic.KaliskiRound

namespace ECDSAAdd.Arithmetic

namespace KaliskiRoundLayout

theorem head_mem (L : KaliskiRoundLayout) (f : RoundField) :
    (L.data.reg f).head!∈L.data.reg f := by
  have hn : L.data.reg f≠[] := by
    intro he
    have h := L.data_reg_length f
    rw [he] at h
    simp at h
  cases hr : L.data.reg f with
  | nil => exact False.elim (hn hr)
  | cons a r => simp

/-- 比较所用子视图从全局互异条件导出。 -/
theorem record_compare_nodup (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) :
    (L.bothWork :: L.swap :: L.cin :: (L.v ++ L.u ++ L.data.reg .carry)).Nodup := by
  have hd := L.data_nodup hnd
  have hn := L.controls_data_nodup hnd
  have hc := (List.nodup_append'.mp hn).1
  have hb := L.control_not_data hnd L.bothWork (by simp [controls])
  have hs := L.control_not_data hnd L.swap (by simp [controls])
  have hb' : L.bothWork ≠ L.swap := by
    intro he
    have hh := List.nodup_iff_count.mp hc L.swap
    simp only [controls, he, List.count_cons, List.count_nil, beq_self_eq_true, if_true] at hh
    omega
  have hregs : (L.v ++ L.u ++ L.data.reg .carry).Nodup := by
    simp only [List.nodup_append', v, u, RoundDataLayout.v, RoundDataLayout.u]
    exact ⟨⟨L.data.reg_nodup hd .v, L.data.reg_nodup hd .u,
      L.data.reg_disjoint hd .v .u (by decide)⟩,
      L.data.reg_nodup hd .carry,
      List.disjoint_append_left.mpr ⟨L.data.reg_disjoint hd .v .carry (by decide),
        L.data.reg_disjoint hd .u .carry (by decide)⟩⟩
  have hsub : ∀ w ∈ L.cin :: (L.v ++ L.u ++ L.data.reg .carry), w ∈ L.data.wires := by
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | (hw | hw) | hw
    · exact List.mem_cons_self
    · exact L.data.reg_mem .v hw
    · exact L.data.reg_mem .u hw
    · exact L.data.reg_mem .carry hw
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hregs⟩⟩⟩
  · intro h
    rcases List.mem_cons.mp h with h | h
    · exact hb' h
    · exact hb (hsub _ h)
  · exact fun h => hs (hsub _ h)
  · simp only [List.mem_append, not_or]
    exact ⟨⟨L.data.cin_not_mem hd .v, L.data.cin_not_mem hd .u⟩,
      L.data.cin_not_mem hd .carry⟩

theorem record_controls_nodup (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) :
    [L.active,L.u.head!,L.v.head!,L.swap,L.subtract,L.oddWork,L.bothWork].Nodup := by
  have hd := L.data_nodup hnd
  have hu : L.u.head!∈L.data.reg .u := L.head_mem .u
  have hv : L.v.head!∈L.data.reg .v := L.head_mem .v
  have huv : L.u.head!≠L.v.head! := fun h =>
    List.disjoint_left.mp (L.data.reg_disjoint hd .u .v (by decide)) hu (h ▸ hv)
  have hh := List.nodup_append'.mp (L.controls_data_nodup hnd)
  have hc : (L.controls++[L.u.head!,L.v.head!]).Nodup :=
    List.nodup_append'.mpr ⟨hh.1, by simp [huv], List.disjoint_left.mpr (by
      intro w hw hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.disjoint_left.mp hh.2.2 hw (L.data.reg_mem .u hu)
      · have he := List.mem_singleton.mp hm
        exact List.disjoint_left.mp hh.2.2 hw (he ▸ L.data.reg_mem .v hv))⟩
  have hr := List.nodup_reverse.mpr hc
  simp only [controls,List.cons_append,List.nil_append,List.reverse_cons,List.reverse_nil,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true] at hc hr ⊢
  simp_all

end KaliskiRoundLayout

/-- 外部记录位更新后，数据布局与其余外部状态仍由同一 frame 精确描述。 -/
theorem RoundFrame.write_external (L : RoundDataLayout) (v : RoundField→Nat)
    (base st : BasisState) (c : Wire) (b : Bool) (hc : c∉L.wires)
    (h : RoundFrame L v base st) :
    RoundFrame L v (writeBit base c b) (writeBit st c b) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro f
    exact (regValue_congr _ _ _ (fun w hw => by
      have hn : w≠c := fun he => hc (he ▸ L.reg_mem f hw)
      simp [writeBit,hn])).trans (h.1.1 f)
  · have hn : L.cin≠c := fun he => hc (he ▸ List.mem_cons_self)
    simpa [writeBit,hn] using h.1.2
  · intro w hw
    by_cases he : w=c
    · subst w; simp [writeBit]
    · simp [writeBit,he,h.2 w hw]

/-- 只更新两个记录位，比较器恢复数据和进位；条件位在输入恢复后清零。 -/
theorem recordRound_correct (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (s : State) (m : List Bool) (ho : s.basis L.oddWork=false) (hb : s.basis L.bothWork=false)
    (hcin : s.basis L.cin=false) (hcarry : ∀ w ∈ L.data.reg .carry, s.basis w=false) :
    run (recordRound L) m s = ⟨s.phase,
      writeBit (writeBit s.basis L.swap
        (s.basis L.swap ^^ ((s.basis L.active && s.basis L.u.head!) ^^
          (s.basis L.active && s.basis L.u.head! && s.basis L.v.head! &&
            decide (regValue L.v s.basis < regValue L.u s.basis)))))
        L.subtract (s.basis L.subtract ^^
          (s.basis L.active && s.basis L.u.head! && s.basis L.v.head!))⟩ := by
  let p : Program := [.CCX L.active L.u.head! L.oddWork, .CCX L.oddWork L.v.head! L.bothWork,
    .CX L.bothWork L.subtract, .CX L.oddWork L.swap]
  let t := run p m s
  have hn := L.record_controls_nodup hnd
  have hr := List.nodup_reverse.mpr hn
  simp only [List.reverse_cons,List.reverse_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true] at hn hr
  have hncomp := L.record_compare_nodup hnd
  have keep (w : Wire) (hw : w ∈ L.data.wires) : t.basis w = s.basis w := by
    have hne (c : Wire) (hc : c ∈ L.controls) : w ≠ c := fun he =>
      L.control_not_data hnd c hc (he ▸ hw)
    have hwo := hne L.oddWork (by simp [KaliskiRoundLayout.controls])
    have hwb := hne L.bothWork (by simp [KaliskiRoundLayout.controls])
    have hws := hne L.swap (by simp [KaliskiRoundLayout.controls])
    have hwd := hne L.subtract (by simp [KaliskiRoundLayout.controls])
    simp [t,p,run,writeBit,hwo,hwb,hws,hwd]
  have hv : regValue L.v t.basis = regValue L.v s.basis :=
    regValue_congr _ _ _ (fun w hw => keep w (L.data.reg_mem .v hw))
  have hu : regValue L.u t.basis = regValue L.u s.basis :=
    regValue_congr _ _ _ (fun w hw => keep w (L.data.reg_mem .u hw))
  obtain ⟨hp, he, ht⟩ := compareLt_correct (some L.bothWork) L.v L.u (L.data.reg .carry)
    L.cin L.swap (List.nodup_cons.mp hncomp).2 (by
      intro c hc; simp only [Option.mem_def,Option.some.injEq] at hc; subst c
      exact (List.nodup_cons.mp hncomp).1)
    (by simp [KaliskiRoundLayout.v,KaliskiRoundLayout.u,RoundDataLayout.v,RoundDataLayout.u,L.data.reg_length])
    (by simp [KaliskiRoundLayout.u,RoundDataLayout.u,L.data.reg_length]) t m
    ((keep L.cin List.mem_cons_self).trans hcin)
    (fun w hw => (keep w (L.data.reg_mem .carry hw)).trans (hcarry w hw))
  let q := compareLt (some L.bothWork) L.v L.u (L.data.reg .carry) L.cin L.swap
  have eqt : run q m t = ⟨t.phase, writeBit t.basis L.swap
      (t.basis L.swap ^^ (t.basis L.bothWork &&
        decide (regValue L.v s.basis < regValue L.u s.basis)))⟩ := by
    apply (show ∀ a b : State, a.phase=b.phase → a.basis=b.basis → a=b from by
      intro a b hp hb; cases a; cases b; simp_all)
    · exact hp
    · funext w
      by_cases hw : w=L.swap
      · subst w; simpa [writeBit,controlValue,hv,hu] using ht
      · simpa [writeBit,hw] using he w hw
  change run (p ++ q ++ _) m s = _
  rw [run_append,run_take,run_append,run_take]
  simp only [show measurementCount p=0 from rfl, List.drop_zero]
  change run _ _ (run q m t) = _
  rw [eqt]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hsw : w=L.swap
  · subst w; simp_all [t,p,run,writeBit,Bool.and_assoc]
  by_cases hsu : w=L.subtract
  · subst w; simp_all [t,p,run,writeBit,Bool.and_assoc]
  by_cases how : w=L.oddWork
  · subst w; simp_all [t,p,run,writeBit,Bool.and_assoc]
  by_cases hbw : w=L.bothWork
  · subst w; simp_all [t,p,run,writeBit,Bool.and_assoc]
  · simp_all [t,p,run,writeBit]

/-- 记录输出之外逐线保持，包括初值任意的 y/out。 -/
theorem recordRound_preserves (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (s : State) (m : List Bool) (ho : s.basis L.oddWork=false) (hb : s.basis L.bothWork=false)
    (hcin : s.basis L.cin=false) (hcarry : ∀ w ∈ L.data.reg .carry, s.basis w=false)
    (w : Wire) (hs : w≠L.swap) (hd : w≠L.subtract) :
    (run (recordRound L) m s).basis w=s.basis w := by
  rw [recordRound_correct L hnd s m ho hb hcin hcarry]
  simp [writeBit,hs,hd]

/-- 任意旧记录的 XOR 契约，无有符号差范围前提；工作位恢复为零。 -/
theorem recordRound_spec (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (U V : Nat) (A S D : Bool) :
    {{ L.u=U, L.v=V, L.active=A, L.swap=S, L.subtract=D,
       L.oddWork=false, L.bothWork=false, L.data.reg .carry=0, L.cin=false }}
      recordRound L
    {{ L.u=U, L.v=V, L.active=A,
       L.swap=(S ^^ ((A && decide (U%2≠0)) ^^
         (A && decide (U%2≠0) && decide (V%2≠0) && decide (V<U)))),
       L.subtract=(D ^^ (A && decide (U%2≠0) && decide (V%2≠0))),
       L.oddWork=false, L.bothWork=false, L.data.reg .carry=0, L.cin=false }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hu,hv⟩,ha⟩,hs⟩,hd⟩,ho⟩,hb⟩,hk⟩,hc⟩
  have he := recordRound_correct L hnd s m ho hb hc ((regValue_zero _ _).mp hk)
  have hp := congrArg State.phase he
  have hn := L.record_controls_nodup hnd
  have hr := List.nodup_reverse.mpr hn
  simp only [List.reverse_cons,List.reverse_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true] at hn hr
  have keep (w : Wire) (hw : w∈L.data.wires) :
      (run (recordRound L) m s).basis w=s.basis w := by
    apply recordRound_preserves L hnd s m ho hb hc ((regValue_zero _ _).mp hk)
    · intro h; exact L.control_not_data hnd L.swap (by simp [KaliskiRoundLayout.controls]) (h ▸ hw)
    · intro h; exact L.control_not_data hnd L.subtract (by simp [KaliskiRoundLayout.controls]) (h ▸ hw)
  have hru := (regValue_congr _ _ _ (fun w hw => keep w (L.data.reg_mem .u hw))).trans hu
  have hrv := (regValue_congr _ _ _ (fun w hw => keep w (L.data.reg_mem .v hw))).trans hv
  have hrk := (regValue_congr _ _ _ (fun w hw => keep w (L.data.reg_mem .carry hw))).trans hk
  have hrc := (keep L.cin List.mem_cons_self).trans hc
  have huo : s.basis L.u.head! = decide (U%2≠0) := by
    rw [regValue_headBit L.u (by
      intro hh; have hm := L.head_mem .u; change L.u.head!∈L.u at hm; simp [hh] at hm) s.basis,hu]
  have hvo : s.basis L.v.head! = decide (V%2≠0) := by
    rw [regValue_headBit L.v (by
      intro hh; have hm := L.head_mem .v; change L.v.head!∈L.v at hm; simp [hh] at hm) s.basis,hv]
  refine ⟨hp, ⟨⟨⟨⟨⟨⟨⟨⟨hru,hrv⟩,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩,hrk⟩,hrc⟩⟩
  all_goals simp_all [writeBit]

/-- XOR 两位记录；同一个函数用于初次记录与恢复旧数据后的清理。 -/
def recordState (L : KaliskiRoundLayout) (z : KState) (base : BasisState) : BasisState :=
  writeBit (writeBit base L.swap (base L.swap ^^ (kaliskiCode z).1))
    L.subtract (base L.subtract ^^ (kaliskiCode z).2)


theorem recordRound_frame (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (z : KState) (base : BasisState)
    (ha : base L.active=decide (z.v≠0))
    (ho : base L.oddWork=false) (hb : base L.bothWork=false) :
    Triple (RoundFrame L.data (roundDataValues z) base) (recordRound L)
      (RoundFrame L.data (roundDataValues z) (recordState L z base)) := by
  have hn (c : Wire) (hc : c∈L.controls) := L.control_not_data hnd c hc
  have hs := hn L.swap (by simp [KaliskiRoundLayout.controls])
  have hd := hn L.subtract (by simp [KaliskiRoundLayout.controls])
  intro s m h
  have he (c : Wire) (hc : c∈L.controls) := h.2 c (hn c hc)
  have heu : s.basis L.u.head!=decide (z.u%2≠0) := by
    rw [regValue_headBit L.u (by
      intro hh
      have hm := L.head_mem .u
      change L.u.head!∈L.u at hm
      simp [hh] at hm) s.basis]
    have hh := h.1.1 .u
    change regValue L.u s.basis=z.u at hh
    rw [hh]
  have hev : s.basis L.v.head!=decide (z.v%2≠0) := by
    rw [regValue_headBit L.v (by
      intro hh
      have hm := L.head_mem .v
      change L.v.head!∈L.v at hm
      simp [hh] at hm) s.basis]
    have hh := h.1.1 .v
    change regValue L.v s.basis=z.v at hh
    rw [hh]
  have hsw := he L.swap (by simp [KaliskiRoundLayout.controls])
  have hsu := he L.subtract (by simp [KaliskiRoundLayout.controls])
  have hac := (he L.active (by simp [KaliskiRoundLayout.controls])).trans ha
  have hoc := (he L.oddWork (by simp [KaliskiRoundLayout.controls])).trans ho
  have hbc := (he L.bothWork (by simp [KaliskiRoundLayout.controls])).trans hb
  have hc := kaliski_code_bits z
  have hcarry : ∀ w ∈ L.data.reg .carry, s.basis w=false :=
    (regValue_zero _ _).mp (h.1.1 .carry)
  rw [recordRound_correct L hnd s m hoc hbc h.1.2 hcarry]
  have huv := h.1.1 .u
  have hvv := h.1.1 .v
  change regValue L.u s.basis = z.u at huv
  change regValue L.v s.basis = z.v at hvv
  simp only [heu,hev,hac,hsw,hsu,huv,hvv]
  have hc1 := congrArg Prod.fst hc
  have hc2 := congrArg Prod.snd hc
  dsimp at hc1 hc2
  rw [← hc1,← hc2]
  exact ⟨trivial,RoundFrame.write_external L.data (roundDataValues z) _ _ L.subtract _ hd
    (RoundFrame.write_external L.data (roundDataValues z) base s.basis L.swap _ hs h)⟩


end ECDSAAdd.Arithmetic
