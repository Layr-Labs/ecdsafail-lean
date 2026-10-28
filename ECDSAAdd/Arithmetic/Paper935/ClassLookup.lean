import ECDSAAdd.Arithmetic.Paper935.HistoryClassFlag
import ECDSAAdd.Arithmetic.Paper935.LookupBranch

namespace ECDSAAdd.Arithmetic.Paper935

/-- Mint the physical class flag, use the actual measured lookup decoder,
then recompute and clear the class flag. -/
def classLookup (one zz pos sign flag address tmp output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (target : Nat)
    (controls scratch : List Wire) (table : Nat → Bool) : Program :=
  historyClassFlag one zz pos sign flag zb frozen positive low target ++
    (lookupBranch flag address tmp output controls scratch table ++
      historyClassFlag one zz pos sign flag zb frozen positive low target)

private theorem state_eq {a b : State} (h : a.phase=b.phase) (hb : a.basis=b.basis) : a=b := by
  cases a; cases b; simp_all

theorem classLookup_run (one zz pos sign flag address tmp output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (target : Nat)
    (controls scratch : List Wire) (table : Nat → Bool)
    (hnz : (flag::pos::one::zz::zb.flatMap ZeroBit.wires).Nodup)
    (hnf : (one::flag::(frozen::positive::low).flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈zb.map ZeroBit.input) (hpos : positive.input=pos)
    (hfr : frozen.input≠pos) (hlow : ∀ b∈low,b.input≠pos)
    (hworkpos : ∀ b∈frozen::positive::low,b.work≠pos)
    (hnlookup : (flag::output::address::(controls++scratch++[tmp])).Nodup)
    (hc : controls.length=9) (hs : scratch.length=9)
    (hflag : flag∉[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires)
    (hout : output∉[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires)
    (s : State) (m : List Bool) (hone : s.basis one=true)
    (hzz : s.basis zz=false) (hpzero : s.basis pos=false)
    (hzw : ∀ b∈zb,s.basis b.work=false)
    (hfw : ∀ b∈frozen::positive::low,s.basis b.work=false)
    (hfit : target<2^low.length) (hflag0 : s.basis flag=false)
    (htmp : s.basis tmp=false) (hwork : ∀ w∈scratch,s.basis w=false) :
    run (classLookup one zz pos sign flag address tmp output zb frozen positive low target controls scratch table) m s=
      ⟨s.phase,writeBit s.basis output (s.basis output ^^
        ((!s.basis frozen.input && !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
          decide (regValue (low.map ZeroBit.input) s.basis=target)) &&
          table (regValue (address::controls) s.basis)))⟩ := by
  let selected := !s.basis frozen.input && !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
    decide (regValue (low.map ZeroBit.input) s.basis=target)
  let value := s.basis output ^^ (selected && table (regValue (address::controls) s.basis))
  let u : State := ⟨s.phase,writeBit s.basis flag selected⟩
  let v : State := ⟨s.phase,writeBit u.basis output value⟩
  let P := historyClassFlag one zz pos sign flag zb frozen positive low target
  let Q := lookupBranch flag address tmp output controls scratch table
  have hfirst (tape : List Bool) : run P tape s=u := by
    rw [historyClassFlag_run one zz pos sign flag zb frozen positive low target hnz hnf hsg hpos hfr hlow hworkpos s tape hone hzz hpzero hzw hfw hfit]
    simp [u,selected,hflag0]
  have hn := (List.nodup_cons.mp hnlookup).1
  have oflag : output≠flag := fun he => hn (by simp [he])
  have inlookup (w : Wire) (hw : w∈output::address::(controls++scratch++[tmp])) : w≠flag := fun he => hn (he ▸ hw)
  have ureg : regValue (address::controls) u.basis=regValue (address::controls) s.basis := by
    apply regValue_congr
    intro w hw
    have hm : w∈output::address::(controls++scratch++[tmp]) := by
      simp only [List.mem_cons,List.mem_append] at hw ⊢
      tauto
    exact Function.update_of_ne (inlookup w hm) _ _
  have umid (tape : List Bool) : run Q tape u=v := by
    rw [lookupBranch_run flag address tmp output controls scratch table hnlookup hc hs u tape
      (by simpa [u,writeBit,inlookup tmp (by simp)] using htmp)
      (by intro w hw; simpa [u,writeBit,inlookup w (by simp [hw])] using hwork w hw),ureg]
    simp [v,u,value,writeBit,oflag]
  let data := [one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires
  have keep (w : Wire) (hw : w∈data) : v.basis w=s.basis w := by
    have hf : w≠flag := fun he => hflag (he ▸ hw)
    have ho : w≠output := fun he => hout (he ▸ hw)
    simp [v,u,writeBit,hf,ho]
  have root (w : Wire) (hw : w∈[one,zz,pos,sign]) : w∈data :=
    List.mem_append_left _ (List.mem_append_left _ hw)
  have inZ (w : Wire) (hw : w∈zb.flatMap ZeroBit.wires) : w∈data :=
    List.mem_append_left _ (List.mem_append_right _ hw)
  have inF (w : Wire) (hw : w∈(frozen::positive::low).flatMap ZeroBit.wires) : w∈data :=
    List.mem_append_right _ hw
  have vzw : ∀ b∈zb,v.basis b.work=false := by
    intro b hb
    exact (keep b.work (inZ _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (hzw b hb)
  have vfw : ∀ b∈frozen::positive::low,v.basis b.work=false := by
    intro b hb
    exact (keep b.work (inF _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (hfw b hb)
  have vzreg : regValue (zb.map ZeroBit.input) v.basis=regValue (zb.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    exact keep _ (inZ _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))
  have vlreg : regValue (low.map ZeroBit.input) v.basis=regValue (low.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    exact keep _ (inF _ (List.mem_flatMap.mpr ⟨b,by simp [hb],by simp [ZeroBit.wires]⟩))
  have vfr : v.basis frozen.input=s.basis frozen.input :=
    keep _ (inF _ (List.mem_flatMap.mpr ⟨frozen,by simp,by simp [ZeroBit.wires]⟩))
  have vlast (tape : List Bool) : run P tape v=⟨s.phase,writeBit s.basis output value⟩ := by
    rw [historyClassFlag_run one zz pos sign flag zb frozen positive low target hnz hnf hsg hpos hfr hlow hworkpos v tape
      ((keep one (root _ (by simp))).trans hone) ((keep zz (root _ (by simp))).trans hzz)
      ((keep pos (root _ (by simp))).trans hpzero) vzw vfw hfit,
      vzreg,vlreg,vfr,keep sign (root _ (by simp))]
    have vf : v.basis flag=selected := by simp [v,u,writeBit,Ne.symm oflag]
    rw [vf]
    change (⟨s.phase,writeBit v.basis flag (selected ^^ selected)⟩ : State)=_
    rw [Bool.xor_self]
    apply state_eq
    · rfl
    · funext w
      by_cases hf : w=flag
      · subst w; simp [writeBit,Ne.symm oflag,hflag0]
      · by_cases ho : w=output
        · subst w; simp [v,u,writeBit,oflag]
        · simp [v,u,writeBit,hf,ho]
  change run (P++(Q++P)) m s=_
  rw [run_append,run_take,hfirst,run_append,run_take,umid,vlast]


theorem classLookup_counts (one zz pos sign flag address tmp output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (target : Nat)
    (controls scratch : List Wire) (table : Nat → Bool)
    (hc : controls.length=9) (hs : scratch.length=9) :
    toffoliCount (classLookup one zz pos sign flag address tmp output zb frozen positive low target controls scratch table)=
      8*zb.length+2*low.length+2053 ∧
    measurementCount (classLookup one zz pos sign flag address tmp output zb frozen positive low target controls scratch table)=
      8*zb.length+2*low.length+2048 := by
  have hf := historyClassFlag_counts one zz pos sign flag zb frozen positive low target
  have hl := lookupBranch_counts flag address tmp output controls scratch table hc hs
  simp only [classLookup,toffoliCount_append,measurementCount_append,hf.1,hf.2,hl.1,hl.2]
  constructor <;> omega

theorem classLookup_support (one zz pos sign flag address tmp output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (target : Nat)
    (controls scratch : List Wire) (table : Nat → Bool) :
    wires (classLookup one zz pos sign flag address tmp output zb frozen positive low target controls scratch table)=
      wires (historyClassFlag one zz pos sign flag zb frozen positive low target) ∪
      wires (lookupBranch flag address tmp output controls scratch table) := by
  rw [classLookup,wires_append,wires_append]
  ext w
  simp only [Finset.mem_union]
  tauto

end ECDSAAdd.Arithmetic.Paper935
