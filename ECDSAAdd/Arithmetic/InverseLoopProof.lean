import ECDSAAdd.Arithmetic.InverseLoopSupport

namespace ECDSAAdd.Arithmetic

theorem InverseScaledMiddle.congr (L : InverseLoopLayout) (q : Nat) (z : KState)
    (cs : List (Bool×Bool)) (N : Nat) (s t : BasisState) (h : InverseScaledMiddle L q z cs N s)
    (he : ∀ w∈L.coreWires,t w=s w) : InverseScaledMiddle L q z cs N t := by
  have hd (w : Wire) (hw : w∈L.middle.data.wires) : t w=s w :=
    he w (L.rest_subset (List.mem_append_right _ hw))
  have hb (w : Wire) (hw : w∈L.compactBorrow) : t w=s w := by
    simp only [InverseLoopLayout.compactBorrow,List.mem_append] at hw
    rcases hw with (((hw|hw)|hw)|hw)|hw
    · exact hd w (L.middle.data.reg_mem .u hw)
    · exact hd w (L.middle.data.reg_mem .v hw)
    · exact hd w (L.middle.data.reg_mem .s hw)
    · exact hd w (L.middle.data.reg_mem .zero (List.mem_of_mem_drop hw))
    · exact he w (List.mem_append_right _ (by
        simp only [InverseLoopLayout.extra,List.mem_append]
        exact Or.inr (List.mem_of_mem_take hw)))
  have hl (w : Wire) (hw : w∈L.scaleLive) : t w=s w := hd w (L.compact_live_data hw)
  have hs (w : Wire) (hw : w∈L.restWires) := he w (L.rest_subset hw)
  have pk : regValue L.compactScaling.k t=regValue L.compactScaling.k s :=
    regValue_congr _ _ _ (fun w hw => he w (L.phase_subset (by
      have hc : w∈L.middle.counter.wires := by
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
        exact List.mem_cons_of_mem _ (mem_addWires hb).1
      simp [InverseLoopLayout.phaseWires,hc])))
  have pl (r : List Wire) (hr : r⊆L.scaleLive) : regValue r t=regValue r s :=
    regValue_congr _ _ _ (fun w hw => hl w (hr hw))
  have pb (r : List Wire) (hr : r⊆L.compactBorrow) : regValue r t=regValue r s :=
    regValue_congr _ _ _ (fun w hw => hb w (hr hw))
  have acc : L.compactScaling.stage.acc⊆L.scaleLive := List.take_subset _ _
  have hist : L.compactScaling.stage.history⊆L.scaleLive :=
    fun _ hw => List.mem_of_mem_drop (List.mem_of_mem_take hw)
  have fallback : t L.first.done=s L.first.done := he _ (List.mem_append_left _
    (by simp [KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires]))
  have getkeep (r : List Wire) (n : Nat) (hr : ∀ w∈r,t w=s w) :
      t (r.getD n L.first.done)=s (r.getD n L.first.done) := by
    by_cases hi : n<r.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hr _ (List.getElem_mem hi)
    · rw [List.getD_eq_default (l := r) (d := L.first.done) (n := n) (by omega)]; exact fallback
  have flag : t L.compactScaling.stage.flag=s L.compactScaling.stage.flag := getkeep L.scaleLive 517 hl
  have pw : regValue L.compactScaling.work t=regValue L.compactScaling.work s := by
    apply regValue_congr
    intro w hw
    simp only [InverseScaleLayout.work,List.mem_append] at hw
    rcases hw with (hw|hw)|hw
    · exact hb w (List.mem_of_mem_take hw)
    · simp only [MontStageLayout.work,List.mem_append] at hw
      rcases hw with ((((hw|hw)|hw)|hw)|hw)|hw
      · exact hb w (List.mem_of_mem_drop (List.mem_of_mem_take hw))
      · exact hb w (List.mem_of_mem_drop (List.mem_of_mem_take hw))
      · exact hb w (List.mem_of_mem_drop (List.mem_of_mem_take hw))
      · have he : w=L.compactScaling.stage.cin := by simpa using hw
        subst w; exact getkeep L.compactBorrow 1039 hb
      · exact hb w (List.mem_of_mem_drop (List.mem_of_mem_take hw))
      · exact hb w (List.mem_of_mem_drop (List.mem_of_mem_take hw))
    · exact hb w (List.mem_of_mem_drop (List.mem_of_mem_take hw))
  refine ⟨⟨pk.trans h.1.1,?_,(pl _ acc).trans h.1.2.2.1,(pl _ hist).trans h.1.2.2.2.1,
    flag.trans h.1.2.2.2.2.1,pw.trans h.1.2.2.2.2.2⟩,(pb _ (fun _ hw => hw)).trans h.2.1,
    InversePhase.congr L _ _ s t h.2.2.1 (fun w hw => he w (L.phase_subset hw)),
    ?_,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun w hw => hd w (L.middle.data.reg_mem .r hw))).trans h.1.2.1
  · exact (regValue_congr _ _ _ (fun w hw => hd w (L.middle.data.reg_mem .out hw))).trans h.2.2.2.1
  · exact (hd _ (by simp [RoundDataLayout.wires])).trans h.2.2.2.2.1
  · exact (hs _ (by simp [InverseLoopLayout.restWires])).trans h.2.2.2.2.2.1
  · exact (hs _ (by simp [InverseLoopLayout.restWires])).trans h.2.2.2.2.2.2.1
  · exact (hs _ (by simp [InverseLoopLayout.restWires])).trans h.2.2.2.2.2.2.2.1
  · exact OneBitRecordsValues.congr _ _ _ _ h.2.2.2.2.2.2.2.2 (fun w hw => hs w (by simp [InverseLoopLayout.restWires,hw]))

theorem inverseCopy_values (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (hlen : L.middle.r.length=L.out.length) (q : Nat) (z : KState) (cs : List (Bool×Bool)) (N O : Nat) :
    Triple (fun s => InverseScaledMiddle L q z cs N s ∧ regValue L.out s=O)
      (copyRegister none L.middle.r L.out)
      (fun s => InverseScaledMiddle L q z cs N s ∧
        regValue L.out s=(O ^^^ (montgomeryValue q (inverseScaleFactor q z.k) N 64%q))) := by
  intro s m h
  have hn : (L.middle.r++L.out).Nodup := by
    have hs := L.reg_first_used .r (by decide)
    have hd := (List.nodup_append'.mp hnd).2.2
    refine List.nodup_append'.mpr ⟨?_,(List.nodup_append'.mp hnd).2.1,?_⟩
    · exact (L.compact_data_nodup hnd) |> fun hh => L.middle.data.reg_nodup hh .r
    · exact List.disjoint_left.mpr (fun w hw ho => List.disjoint_left.mp hd
        (List.mem_append_left _ ((L.first.usedRecordTapeWires_sublist L.records).subset (hs hw))) ho)
  obtain ⟨hp,he,hz⟩ := copyRegister_correct none L.middle.r L.out hlen hn (by simp) s m
  have hdis : L.coreWires.Disjoint L.out := (List.nodup_append'.mp hnd).2.2
  refine ⟨hp,InverseScaledMiddle.congr L q z cs N s.basis _ h.1 ?_,?_⟩
  · intro w hw; exact he w (List.disjoint_left.mp hdis hw)
  · simpa only [copyValue,h.2,show regValue L.middle.r s.basis=montgomeryValue q (inverseScaleFactor q z.k) N 64%q from h.1.1.2.1] using hz

/-- 保留初始化数据，XOR写入规范逆元，再清除全部第一阶段与缩放历史。 -/
theorem inverseLoop_values (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (hn : L.records.length=512) (hw : L.first.counter.width=10)
    (hl : L.first.low.length=256) (hm : L.arithmetic.width=256)
    (ha : L.a.length=257) (ht : L.temp.length=257) (hout : L.out.length=257)
    (q a O : Nat) (hq : q<2^256) (ho : q%16=15) (hx0 : 0<a) (hx : a<q) (hcop : q.Coprime a) :
    Triple (fun s => InverseInitial L q a s ∧ regValue L.out s=O) (inverseLoop L q)
      (fun s => InverseInitial L q a s ∧ regValue L.out s=(O ^^^ kaliskiInverse q a 256)) := by
  let z := kaliskiStep^[512] (kaliskiInit q a)
  let cs := kaliskiCodes 512 (kaliskiInit q a)
  let N := (-(z.r : ZMod q)).val
  let R := montgomeryValue q (inverseScaleFactor q z.k) N 64%q
  have heq : R=kaliskiInverse q a 256 :=
    (kaliski_montgomery_scale q a ho hq hx0 hx hcop).trans
      (kaliski_correct q a 256 (by omega) hq hx0 (hx.trans hq) hcop).symm
  have hcompute := inverseCompute_values L hnd hn hw hl hm ha ht q a hq ho hx hcop
  have hd : L.first.data.width=257 := by simp [KaliskiRoundLayout.data,RoundDataLayout.width,hl]
  have hwires := inverseCompute_wires L hn hw (by omega) (by omega) (by omega) (by omega) hl hm q
  have hdis : L.coreWires.Disjoint L.out := (List.nodup_append'.mp hnd).2.2
  have frame (circ : Program) (hc : wires circ=L.usedCoreWires.toFinset) (V : Nat)
      (s t : BasisState) (he : ∀ w,w∉wires circ → s w=t w) (hv : regValue L.out s=V) :
      regValue L.out t=V := by
    apply (regValue_congr _ _ _ ?_).trans hv
    intro w hw
    apply (he w ?_).symm
    rw [hc]
    exact fun hh => List.disjoint_left.mp hdis (L.usedCoreWires_sublist.subset (List.mem_toFinset.mp hh)) hw
  have hf := hcompute.1.frame (frame _ hwires.1 O)
  have hb := hcompute.2.frame (frame _ hwires.2 (O ^^^ R))
  have hc := inverseCopy_values L hnd (by change (L.middle.data.reg .r).length=L.out.length; rw [InverseLoopLayout.middle,loopEnd_data,L.first.data_reg_length,hl,hout]) q z cs N O
  have hall := (hf.seq hc).seq hb
  simpa only [heq] using hall

end ECDSAAdd.Arithmetic
