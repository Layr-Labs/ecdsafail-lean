import ECDSAAdd.Arithmetic.Paper935.FiniteDepth

namespace ECDSAAdd.Arithmetic.Paper935

structure DepthLayout.FrozenReady (L : DepthLayout) (s : State) : Prop where
  hnz : (L.flag::L.pos::L.one::L.zz::L.zb.flatMap ZeroBit.wires).Nodup
  hnf : (L.one::L.flag::(L.frozen::L.positive::L.low).flatMap ZeroBit.wires).Nodup
  hsg : L.sign∈L.zb.map ZeroBit.input
  hpos : L.positive.input=L.pos
  hfr : L.frozen.input≠L.pos
  hlow : ∀ b∈L.low,b.input≠L.pos
  hworkpos : ∀ b∈L.frozen::L.positive::L.low,b.work≠L.pos
  hnlookup : (L.flag::L.output::L.address::((L.fdata++L.qbits)++L.scratch++[L.tmp])).Nodup
  hflen : L.fdata.length=4
  hqlen : L.qbits.length=5
  hs : L.scratch.length=9
  hflag : L.flag∉[L.one,L.zz,L.pos,L.sign]++L.zb.flatMap ZeroBit.wires++(L.frozen::L.positive::L.low).flatMap ZeroBit.wires
  hout : L.output∉[L.one,L.zz,L.pos,L.sign]++L.zb.flatMap ZeroBit.wires++(L.frozen::L.positive::L.low).flatMap ZeroBit.wires
  hone : s.basis L.one=true
  hzz : s.basis L.zz=false
  hpzero : s.basis L.pos=false
  hzw : ∀ b∈L.zb,s.basis b.work=false
  hfw : ∀ b∈L.frozen::L.positive::L.low,s.basis b.work=false
  hflag0 : s.basis L.flag=false
  htmp : s.basis L.tmp=false
  hwork : ∀ w∈L.scratch,s.basis w=false
  hmin : 2≤L.low.length
  hfrozen : s.basis L.frozen.input=true
  outputAway : L.output∉L.readWires

theorem DepthLayout.FrozenReady.frame (L : DepthLayout)
    (s t : State) (h : L.FrozenReady s)
    (hframe : ∀ w,w≠L.output → t.basis w=s.basis w) : L.FrozenReady t := by
  have keep (w : Wire) (hw : w∈L.readWires) : t.basis w=s.basis w :=
    hframe w (fun he => h.outputAway (he ▸ hw))
  have root (w : Wire) (hw : w∈[L.one,L.zz,L.pos,L.sign,L.flag,L.tmp]) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  have inZ (w : Wire) (hw : w∈L.zb.flatMap ZeroBit.wires) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append]
    tauto
  have inF (w : Wire) (hw : w∈(L.frozen::L.positive::L.low).flatMap ZeroBit.wires) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append]
    tauto
  have inScratch (w : Wire) (hw : w∈L.scratch) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append]
    tauto
  have zw : ∀ b∈L.zb,t.basis b.work=false := by
    intro b hb
    exact (keep b.work (inZ _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (h.hzw b hb)
  have fw : ∀ b∈L.frozen::L.positive::L.low,t.basis b.work=false := by
    intro b hb
    exact (keep b.work (inF _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (h.hfw b hb)
  exact {
    hnz := h.hnz
    hnf := h.hnf
    hsg := h.hsg
    hpos := h.hpos
    hfr := h.hfr
    hlow := h.hlow
    hworkpos := h.hworkpos
    hnlookup := h.hnlookup
    hflen := h.hflen
    hqlen := h.hqlen
    hs := h.hs
    hflag := h.hflag
    hout := h.hout
    hone := (keep L.one (root _ (by simp))).trans h.hone
    hzz := (keep L.zz (root _ (by simp))).trans h.hzz
    hpzero := (keep L.pos (root _ (by simp))).trans h.hpzero
    hzw := zw
    hfw := fw
    hflag0 := (keep L.flag (root _ (by simp))).trans h.hflag0
    htmp := (keep L.tmp (root _ (by simp))).trans h.htmp
    hwork := fun w hw => (keep w (inScratch w hw)).trans (h.hwork w hw)
    hmin := h.hmin
    hfrozen := (keep L.frozen.input L.frozen_mem).trans h.hfrozen
    outputAway := h.outputAway
  }

theorem DepthLayout.FrozenReady.run (L : DepthLayout) (p : Int) (s : State) (m : List Bool)
    (h : L.FrozenReady s) : ECDSAAdd.run (L.program p) m s=s := by
  have hfit : 2^(L.low.length-1)<2^L.low.length := by
    have hmin := h.hmin
    have he : L.low.length=(L.low.length-1)+1 := by omega
    conv_rhs => rw [he,pow_succ]
    have hh := Nat.two_pow_pos (L.low.length-1)
    omega
  rw [DepthLayout.program,classLookup_run L.one L.zz L.pos L.sign L.flag L.address L.tmp L.output
    L.zb L.frozen L.positive L.low (2^(L.low.length-1)) (L.fdata++L.qbits) L.scratch
    (residueBranchTable p L.low.length) h.hnz h.hnf h.hsg h.hpos h.hfr h.hlow h.hworkpos h.hnlookup
    (by simp [h.hflen,h.hqlen]) h.hs h.hflag h.hout s m h.hone h.hzz h.hpzero h.hzw h.hfw hfit h.hflag0 h.htmp h.hwork]
  simp [h.hfrozen,writeBit]

/-- Frozen lanes need clean work and separation, but no fictitious row update. -/
def DepthLayout.Available (L : DepthLayout) (st : ECDSAAdd.Divsteps.ZState) (s : State) : Prop :=
  L.Ready st s ∨ L.FrozenReady s

theorem DepthLayout.Available.frame (L : DepthLayout) (st : ECDSAAdd.Divsteps.ZState)
    (s t : State) (h : L.Available st s)
    (hframe : ∀ w,w≠L.output → t.basis w=s.basis w) : L.Available st t := by
  rcases h with h|h
  · exact Or.inl (h.frame L st s t hframe)
  · exact Or.inr (h.frame L s t hframe)

theorem DepthLayout.Available.run (L : DepthLayout) (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (s : State) (m : List Bool)
    (h : L.Available st s) :
    ECDSAAdd.run (L.program p) m s=⟨s.phase,writeBit s.basis L.output (s.basis L.output ^^
      ((!s.basis L.frozen.input && decide ((ECDSAAdd.Divsteps.zStep st).z≤0) &&
        decide (padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv=L.low.length)) &&
        decide (ECDSAAdd.Divsteps.bbit st=1)))⟩ := by
  rcases h with h|h
  · exact L.run p st hi hp s m h
  · rw [h.run L p s m]
    simp [h.hfrozen,writeBit]


private theorem state_eq {a b : State} (h : a.phase=b.phase) (hb : a.basis=b.basis) : a=b := by
  cases a; cases b; simp_all

theorem finiteDepthProgram_available (layouts : List DepthLayout) (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (output : Wire) (frozen : Bool)
    (s : State) (m : List Bool) (hready : ∀ L∈layouts,L.Available st s)
    (hout : ∀ L∈layouts,L.output=output) (hfr : ∀ L∈layouts,s.basis L.frozen.input=frozen) :
    run (finiteDepthProgram layouts p) m s=
      ⟨s.phase,writeBit s.basis output (s.basis output ^^ finiteDepthMask st frozen layouts)⟩ := by
  induction layouts generalizing s m with
  | nil =>
    simp only [finiteDepthProgram,List.flatMap_nil,run,finiteDepthMask,Bool.xor_false]
    apply state_eq
    · rfl
    · funext w
      by_cases hw : w=output <;> simp [writeBit,hw]
  | cons L ls ih =>
    have hl := hready L (by simp)
    have hlo := hout L (by simp)
    let bit := ((!frozen && decide ((ECDSAAdd.Divsteps.zStep st).z≤0) &&
      decide (padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv=L.low.length)) &&
      decide (ECDSAAdd.Divsteps.bbit st=1))
    let t : State := ⟨s.phase,writeBit s.basis output (s.basis output ^^ bit)⟩
    have hfirst : run (L.program p) m s=t := by
      rw [DepthLayout.Available.run L p st hi hp s m hl,hlo,hfr L (by simp)]
    have frame (w : Wire) (hw : w≠output) : t.basis w=s.basis w := Function.update_of_ne hw _ _
    have htready : ∀ K∈ls,K.Available st t := by
      intro K hk
      apply DepthLayout.Available.frame K st s t (hready K (by simp [hk]))
      intro w hw
      exact frame w (by simpa only [hout K (by simp [hk])] using hw)
    have htfr : ∀ K∈ls,t.basis K.frozen.input=frozen := by
      intro K hk
      have hK := hready K (by simp [hk])
      have hne : K.frozen.input≠output := by
        intro he
        apply (hK.elim (fun h => h.outputAway) (fun h => h.outputAway))
        rw [hout K (by simp [hk]),←he]
        exact K.frozen_mem
      exact (frame _ hne).trans (hfr K (by simp [hk]))
    have htail := ih t (m.drop (measurementCount (L.program p))) htready
      (fun K hk => hout K (by simp [hk])) htfr
    rw [finiteDepthProgram,List.flatMap_cons,run_append,run_take,hfirst]
    change run (finiteDepthProgram ls p) (m.drop (measurementCount (L.program p))) t=_
    rw [htail]
    apply state_eq
    · rfl
    · funext w
      by_cases hw : w=output
      · subst w
        simp [writeBit,t,finiteDepthMask,bit]
      · simp [writeBit,t,hw]

end ECDSAAdd.Arithmetic.Paper935
