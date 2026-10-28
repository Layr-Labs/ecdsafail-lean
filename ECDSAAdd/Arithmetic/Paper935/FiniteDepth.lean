import ECDSAAdd.Arithmetic.Paper935.DepthLookup

namespace ECDSAAdd.Arithmetic.Paper935

structure DepthLayout where
  one : Wire
  zz : Wire
  pos : Wire
  sign : Wire
  flag : Wire
  address : Wire
  tmp : Wire
  output : Wire
  zb : List ZeroBit
  frozen : ZeroBit
  positive : ZeroBit
  low : List ZeroBit
  fdata : List Wire
  qbits : List Wire
  scratch : List Wire
  flow : Wire
  vlow : Wire
  qlow : Wire
  zlo : List Wire
  vtail : List Wire
  ftail : List Wire
  slice : List Wire
  qtail : List Wire

def DepthLayout.program (L : DepthLayout) (p : Int) : Program :=
  classLookup L.one L.zz L.pos L.sign L.flag L.address L.tmp L.output L.zb L.frozen L.positive L.low
    (2^(L.low.length-1)) (L.fdata++L.qbits) L.scratch (residueBranchTable p L.low.length)

def DepthLayout.readWires (L : DepthLayout) : List Wire :=
  [L.one,L.zz,L.pos,L.sign,L.flag,L.tmp]++L.zb.flatMap ZeroBit.wires++
    (L.frozen::L.positive::L.low).flatMap ZeroBit.wires++L.scratch++
    (L.zlo++[L.sign])++(L.vlow::(L.low.map ZeroBit.input++L.vtail))++
    (L.flow::((L.address::L.fdata)++L.ftail))

structure DepthLayout.Ready (L : DepthLayout) (st : ECDSAAdd.Divsteps.ZState) (s : State) : Prop where
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
  hzview : L.zb.map ZeroBit.input=L.zlo++[L.sign]
  hvtail : L.vtail≠[]
  hmin : 2≤L.low.length
  hmax : L.low.length≤6
  hslen : L.slice.length=L.low.length
  hftail : L.ftail≠[]
  hqtail : L.qtail≠[]
  hzval : signedRegValue (L.zlo++[L.sign]) s.basis=(ECDSAAdd.Divsteps.zStep st).z
  hvval : signedRegValue (L.vlow::(L.low.map ZeroBit.input++L.vtail)) s.basis=(ECDSAAdd.Divsteps.zStep st).fv
  hfval : signedRegValue (L.flow::((L.address::L.fdata)++L.ftail)) s.basis=(ECDSAAdd.Divsteps.zStep st).f
  hcoeffview : L.vlow::(L.low.map ZeroBit.input++L.vtail)=L.slice++(L.qlow::(L.qbits++L.qtail))
  outputAway : L.output∉L.readWires

theorem DepthLayout.run (L : DepthLayout) (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (s : State) (m : List Bool)
    (h : L.Ready st s) :
    ECDSAAdd.run (L.program p) m s=⟨s.phase,writeBit s.basis L.output (s.basis L.output ^^
      ((!s.basis L.frozen.input && decide ((ECDSAAdd.Divsteps.zStep st).z≤0) &&
        decide (padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv=L.low.length)) &&
        decide (ECDSAAdd.Divsteps.bbit st=1)))⟩ := by
  exact depthLookup_run p st hi hp L.one L.zz L.pos L.sign L.flag L.address L.tmp L.output L.zb L.frozen L.positive L.low L.fdata L.qbits L.scratch h.hnz h.hnf h.hsg h.hpos h.hfr h.hlow h.hworkpos h.hnlookup h.hflen h.hqlen h.hs h.hflag h.hout s m h.hone h.hzz h.hpzero h.hzw h.hfw h.hflag0 h.htmp h.hwork L.flow L.vlow L.qlow L.zlo L.vtail L.ftail L.slice L.qtail h.hzview h.hvtail h.hmin h.hmax h.hslen h.hftail h.hqtail h.hzval h.hvval h.hfval h.hcoeffview


theorem DepthLayout.Ready.frame (L : DepthLayout) (st : ECDSAAdd.Divsteps.ZState)
    (s t : State) (h : L.Ready st s)
    (hframe : ∀ w,w≠L.output → t.basis w=s.basis w) : L.Ready st t := by
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
  have signed (xs : List Wire) (hx : xs⊆L.readWires) : signedRegValue xs t.basis=signedRegValue xs s.basis := by
    unfold signedRegValue
    rw [regValue_congr xs t.basis s.basis (fun w hw => keep w (hx hw))]
  have zkeep : signedRegValue (L.zlo++[L.sign]) t.basis=signedRegValue (L.zlo++[L.sign]) s.basis := by
    apply signed
    intro w hw
    simp only [DepthLayout.readWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  have vkeep : signedRegValue (L.vlow::(L.low.map ZeroBit.input++L.vtail)) t.basis=
      signedRegValue (L.vlow::(L.low.map ZeroBit.input++L.vtail)) s.basis := by
    apply signed
    intro w hw
    simp only [DepthLayout.readWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  have fkeep : signedRegValue (L.flow::((L.address::L.fdata)++L.ftail)) t.basis=
      signedRegValue (L.flow::((L.address::L.fdata)++L.ftail)) s.basis := by
    apply signed
    intro w hw
    simp only [DepthLayout.readWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
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
    hzview := h.hzview
    hvtail := h.hvtail
    hmin := h.hmin
    hmax := h.hmax
    hslen := h.hslen
    hftail := h.hftail
    hqtail := h.hqtail
    hzval := zkeep.trans h.hzval
    hvval := vkeep.trans h.hvval
    hfval := fkeep.trans h.hfval
    hcoeffview := h.hcoeffview
    outputAway := h.outputAway
  }


private theorem state_eq {a b : State} (h : a.phase=b.phase) (hb : a.basis=b.basis) : a=b := by
  cases a; cases b; simp_all

theorem DepthLayout.frozen_mem (L : DepthLayout) : L.frozen.input∈L.readWires := by
  have h : L.frozen.input∈(L.frozen::L.positive::L.low).flatMap ZeroBit.wires :=
    List.mem_flatMap.mpr ⟨L.frozen,by simp,by simp [ZeroBit.wires]⟩
  simp only [DepthLayout.readWires,List.mem_append]
  tauto

def finiteDepthProgram (layouts : List DepthLayout) (p : Int) : Program :=
  layouts.flatMap (fun L => L.program p)

def finiteDepthMask (st : ECDSAAdd.Divsteps.ZState) (frozen : Bool) : List DepthLayout → Bool
  | [] => false
  | L::ls => (((!frozen && decide ((ECDSAAdd.Divsteps.zStep st).z≤0) &&
      decide (padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv=L.low.length)) &&
      decide (ECDSAAdd.Divsteps.bbit st=1)) ^^ finiteDepthMask st frozen ls)

/-- Compose actual stages, re-establishing every clean-work and row premise
from their full frame theorem. No stage-correctness contract is assumed. -/
theorem finiteDepthProgram_run (layouts : List DepthLayout) (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (output : Wire) (frozen : Bool)
    (s : State) (m : List Bool) (hready : ∀ L∈layouts,L.Ready st s)
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
      rw [L.run p st hi hp s m hl,hlo,hfr L (by simp)]
    have frame (w : Wire) (hw : w≠output) : t.basis w=s.basis w := Function.update_of_ne hw _ _
    have htready : ∀ K∈ls,K.Ready st t := by
      intro K hk
      apply DepthLayout.Ready.frame K st s t (hready K (by simp [hk]))
      intro w hw
      exact frame w (by simpa only [hout K (by simp [hk])] using hw)
    have htfr : ∀ K∈ls,t.basis K.frozen.input=frozen := by
      intro K hk
      have hK := hready K (by simp [hk])
      have hne : K.frozen.input≠output := by
        intro he
        apply hK.outputAway
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

/-- The five disjoint depth classes recover exactly one branch on the
finite recovery range. Outside that range the decoder has no effect. -/
theorem finiteDepthMask_five (st : ECDSAAdd.Divsteps.ZState) (frozen : Bool)
    (a b c d e : DepthLayout) (ha : a.low.length=2) (hb : b.low.length=3)
    (hc : c.low.length=4) (hd : d.low.length=5) (he : e.low.length=6) :
    finiteDepthMask st frozen [a,b,c,d,e] =
      (!frozen && decide ((ECDSAAdd.Divsteps.zStep st).z≤0) &&
        decide (2≤padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv ∧
          padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv≤6) &&
        decide (ECDSAAdd.Divsteps.bbit st=1)) := by
  let v := padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv
  by_cases h : 2≤v ∧ v≤6
  · have casesv : v=2 ∨ v=3 ∨ v=4 ∨ v=5 ∨ v=6 := by omega
    rcases casesv with h2|h3|h4|h5|h6 <;>
      simp_all [finiteDepthMask,v]
  · have h2 : v≠2 := by omega
    have h3 : v≠3 := by omega
    have h4 : v≠4 := by omega
    have h5 : v≠5 := by omega
    have h6 : v≠6 := by omega
    simp_all [finiteDepthMask,v]

/-- Restore the old branch and cancel its original measurement phase only
once, after all five actual depth decoders have finished. -/
theorem finiteDepth_cancel (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1)
    (a b c d e : DepthLayout) (ha : a.low.length=2) (hb : b.low.length=3)
    (hc : c.low.length=4) (hd : d.low.length=5) (he : e.low.length=6)
    (output : Wire) (s : State) (m : List Bool)
    (hready : ∀ L∈[a,b,c,d,e],L.Ready st s)
    (hout : ∀ L∈[a,b,c,d,e],L.output=output)
    (hfr : ∀ L∈[a,b,c,d,e],s.basis L.frozen.input=false)
    (hz : (ECDSAAdd.Divsteps.zStep st).z≤0)
    (hdepth : 2≤padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv ∧
      padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv≤6)
    (hzero : s.basis output=false) (ordinal cursor : Nat) (phase : Bool)
    (hphase : s.phase=(phase ^^ (m.getD ordinal false && decide (ECDSAAdd.Divsteps.bbit st=1)))) :
    runWithTape (ECDSAAdd.Arithmetic.Divsteps.recoverBranch
      (finiteDepthProgram [a,b,c,d,e] p) output ordinal) m cursor s=
      ⟨phase,writeBit s.basis output (decide (ECDSAAdd.Divsteps.bbit st=1))⟩ := by
  apply ECDSAAdd.Arithmetic.Divsteps.recoverBranch_cancel _ _ _ _ _ _ _ _ hphase
  rw [finiteDepthProgram_run [a,b,c,d,e] p st hi hp output false s (m.drop cursor)
    hready hout hfr,finiteDepthMask_five st false a b c d e ha hb hc hd he]
  simp [hz,hdepth,hzero]

end ECDSAAdd.Arithmetic.Paper935
