import ECDSAAdd.Arithmetic.Paper935.StoreFlag
import ECDSAAdd.Arithmetic.Paper935.DepthResidue

namespace ECDSAAdd.Arithmetic.Paper935

private theorem flag_compare (fr positive : Bool) (n target : Nat) :
    decide ((if fr then 1 else 0)+2*((if positive then 1 else 0)+2*n)=4*target)=
      (!fr && !positive && decide (n=target)) := by
  cases fr <;> cases positive <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega

/-- Compare a coefficient slice with a public residue while requiring a live
nonpositive-counter lane. The same measured computation clears its flag. -/
def historyClassFlag (one zz pos sign output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (target : Nat) : Program :=
  counterPositive one zz pos sign zb ++
    (equalConstant one output (frozen::positive::low) (4*target) ++
      counterPositive one zz pos sign zb)

theorem historyClassFlag_run (one zz pos sign output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (target : Nat)
    (hnz : (output::pos::one::zz::zb.flatMap ZeroBit.wires).Nodup)
    (hnf : (one::output::(frozen::positive::low).flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈zb.map ZeroBit.input) (hpos : positive.input=pos)
    (hfr : frozen.input≠pos) (hlow : ∀ b∈low,b.input≠pos)
    (hworkpos : ∀ b∈frozen::positive::low,b.work≠pos)
    (s : State) (m : List Bool) (hone : s.basis one=true)
    (hzz : s.basis zz=false) (hpzero : s.basis pos=false)
    (hzw : ∀ b∈zb,s.basis b.work=false)
    (hfw : ∀ b∈frozen::positive::low,s.basis b.work=false)
    (hfit : target<2^low.length) :
    run (historyClassFlag one zz pos sign output zb frozen positive low target) m s=
      ⟨s.phase,writeBit s.basis output (s.basis output ^^
        (!s.basis frozen.input &&
          !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
          decide (regValue (low.map ZeroBit.input) s.basis=target)))⟩ := by
  have hnc := (List.nodup_cons.mp hnz).2
  have ho := (List.nodup_cons.mp hnz).1
  have hp := (List.nodup_cons.mp hnc).1
  have op : output≠pos := fun he => ho (by simp [he])
  have oo : output≠one := fun he => ho (by simp [he])
  have oz : output≠zz := fun he => ho (by simp [he])
  have po : pos≠one := fun he => hp (by simp [he])
  have pz : pos≠zz := fun he => hp (by simp [he])
  have zmem (b : ZeroBit) (hb : b∈zb) : b.input∈zb.flatMap ZeroBit.wires ∧ b.work∈zb.flatMap ZeroBit.wires :=
    ⟨List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩,
      List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩⟩
  have pn (w : Wire) (hw : w∈zb.flatMap ZeroBit.wires) : w≠pos :=
    fun he => hp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (he ▸ hw)))
  have on (w : Wire) (hw : w∈zb.flatMap ZeroBit.wires) : w≠output :=
    fun he => ho (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (he ▸ hw))))
  have sm : sign∈zb.flatMap ZeroBit.wires := by
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hsg
    exact (zmem b hb).1
  let ispos := !s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)
  let select := !s.basis frozen.input && !ispos && decide (regValue (low.map ZeroBit.input) s.basis=target)
  let v : State := ⟨s.phase,writeBit s.basis pos ispos⟩
  let u : State := ⟨s.phase,writeBit v.basis output (s.basis output ^^ select)⟩
  have hfirst (tape : List Bool) : run (counterPositive one zz pos sign zb) tape s=v := by
    rw [counterPositive_run one zz pos sign zb hnc hsg s tape hone hzz hzw]
    simp [v,ispos,hpzero]
  have vwork : ∀ b∈frozen::positive::low,v.basis b.work=false := by
    intro b hb
    simp [v,writeBit,hworkpos b hb,hfw b hb]
  have vlo : regValue (low.map ZeroBit.input) v.basis=regValue (low.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    simp [v,writeBit,hlow b hb]
  have vselect : decide (regValue ((frozen::positive::low).map ZeroBit.input) v.basis=4*target)=select := by
    change decide ((if v.basis frozen.input then 1 else 0)+
      2*((if v.basis positive.input then 1 else 0)+2*regValue (low.map ZeroBit.input) v.basis)=4*target)=select
    rw [vlo]
    have vp : v.basis positive.input=ispos := by rw [hpos]; simp [v,writeBit]
    have vf : v.basis frozen.input=s.basis frozen.input := by simp [v,writeBit,hfr]
    rw [vp,vf]
    dsimp only [select]
    exact flag_compare (s.basis frozen.input) ispos (regValue (low.map ZeroBit.input) s.basis) target
  have hstore (tape : List Bool) : run (equalConstant one output (frozen::positive::low) (4*target)) tape v=u := by
    rw [equalConstant_correct one output (frozen::positive::low) (4*target) hnf (by simp only [List.length_cons,pow_succ]; omega) v tape vwork,vselect]
    simp [u,v,writeBit,op,Ne.symm po,hone]
  have uwork : ∀ b∈zb,u.basis b.work=false := by
    intro b hb
    simp [u,v,writeBit,pn _ (zmem b hb).2,on _ (zmem b hb).2,hzw b hb]
  have ug : regValue (zb.map ZeroBit.input) u.basis=regValue (zb.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    simp [u,v,writeBit,pn _ (zmem b hb).1,on _ (zmem b hb).1]
  have hlast (tape : List Bool) : run (counterPositive one zz pos sign zb) tape u=
      ⟨s.phase,writeBit s.basis output (s.basis output ^^ select)⟩ := by
    rw [counterPositive_run one zz pos sign zb hnc hsg u tape
      (by simp [u,v,writeBit,Ne.symm oo,Ne.symm po,hone])
      (by simp [u,v,writeBit,Ne.symm oz,Ne.symm pz,hzz]) uwork,ug]
    apply congrArg (State.mk s.phase)
    funext w
    by_cases hw : w=pos <;> by_cases ho' : w=output <;>
      simp_all [u,v,ispos,writeBit,Function.update_apply,pn sign sm,on sign sm]
  rw [historyClassFlag,run_append,run_take,hfirst,run_append,run_take,hstore,hlast]

theorem historyClassFlag_counts (one zz pos sign output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (target : Nat) :
    toffoliCount (historyClassFlag one zz pos sign output zb frozen positive low target)=4*zb.length+low.length+4 ∧
    measurementCount (historyClassFlag one zz pos sign output zb frozen positive low target)=4*zb.length+low.length+2 := by
  have hc := counterPositive_counts one zz pos sign zb
  have he := equalConstant_counts one output (frozen::positive::low) (4*target)
  simp only [historyClassFlag,toffoliCount_append,measurementCount_append,hc.1,hc.2,he.1,he.2,List.length_cons]
  constructor <;> omega

theorem historyClassFlag_support (one zz pos sign output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (target : Nat) :
    wires (historyClassFlag one zz pos sign output zb frozen positive low target)=
      wires (counterPositive one zz pos sign zb) ∪
        (one::output::(frozen::positive::low).flatMap ZeroBit.wires).toFinset := by
  rw [historyClassFlag,wires_append,wires_append,equalConstant_wires]
  ext w
  simp only [Finset.mem_union]
  tauto


/-- For a slice of coefficient bits 1 through j, this recognizes the unique
nonzero residue 2^(j-1), rather than all depths at or above a cutoff. -/
def historyDepthFlag (one zz pos sign output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) : Program :=
  historyClassFlag one zz pos sign output zb frozen positive low (2^(low.length-1))

theorem historyDepthFlag_run (one zz pos sign output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit)
    (hnz : (output::pos::one::zz::zb.flatMap ZeroBit.wires).Nodup)
    (hnf : (one::output::(frozen::positive::low).flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈zb.map ZeroBit.input) (hpos : positive.input=pos)
    (hfr : frozen.input≠pos) (hlow : ∀ b∈low,b.input≠pos)
    (hworkpos : ∀ b∈frozen::positive::low,b.work≠pos)
    (s : State) (m : List Bool) (hone : s.basis one=true)
    (hzz : s.basis zz=false) (hpzero : s.basis pos=false)
    (hzw : ∀ b∈zb,s.basis b.work=false)
    (hfw : ∀ b∈frozen::positive::low,s.basis b.work=false)
    (hlen : 0<low.length) :
    run (historyDepthFlag one zz pos sign output zb frozen positive low) m s=
      ⟨s.phase,writeBit s.basis output (s.basis output ^^
        (!s.basis frozen.input &&
          !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
          decide (regValue (low.map ZeroBit.input) s.basis=2^(low.length-1))))⟩ := by
  have hfit : 2^(low.length-1)<2^low.length := by
    have he : low.length=(low.length-1)+1 := by omega
    conv_rhs => rw [he,pow_succ]
    have hp := Nat.two_pow_pos (low.length-1)
    omega
  exact historyClassFlag_run one zz pos sign output zb frozen positive low (2^(low.length-1))
    hnz hnf hsg hpos hfr hlow hworkpos s m hone hzz hpzero hzw hfw hfit


theorem historyDepth_predicate_value (sign frozen vlow : Wire) (zb low : List ZeroBit)
    (zlo tail : List Wire) (s : BasisState) (st : ECDSAAdd.Divsteps.ZState)
    (hzview : zb.map ZeroBit.input=zlo++[sign]) (htail : tail≠[]) (hlen : 0<low.length)
    (hz : signedRegValue (zlo++[sign]) s=st.z)
    (hv : signedRegValue (vlow::(low.map ZeroBit.input++tail)) s=st.fv)
    (heven : st.fv%2=0) :
    (!s frozen && !(!s sign && !decide (regValue (zb.map ZeroBit.input) s=0)) &&
      decide (regValue (low.map ZeroBit.input) s=2^(low.length-1)))=
    (!s frozen && decide (st.z≤0) && decide (padicValInt 2 st.fv=low.length)) := by
  have hbit : s vlow=false := (signedRegValue_even_iff vlow _ s).mp (by rw [hv]; exact heven)
  have hlow := historyDepth_test vlow (low.map ZeroBit.input) tail s htail hbit (by simpa using hlen)
  rw [hv,List.length_map] at hlow
  rw [hzview,positivePredicate_value,hz]
  have hnonpos : (!decide (st.z>0))=decide (st.z≤0) := by
    apply Bool.eq_iff_iff.mpr
    simp
  rw [hnonpos]
  simp only [hlow]

end ECDSAAdd.Arithmetic.Paper935
