import ECDSAAdd.Arithmetic.Paper935.CounterPositive

namespace ECDSAAdd.Arithmetic.Paper935

/-- The coefficient test includes bit one, so it excludes the swap class
without keeping the retired swap tag. -/
def storeFlag (one zz pos sign output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) : Program :=
  counterPositive one zz pos sign zb ++
    (equalConstant one output (frozen::positive::low) 0 ++
      counterPositive one zz pos sign zb)

theorem storeFlag_run (one zz pos sign output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit)
    (hnz : (output::pos::one::zz::zb.flatMap ZeroBit.wires).Nodup)
    (hnf : (one::output::(frozen::positive::low).flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈zb.map ZeroBit.input) (hpos : positive.input=pos)
    (hfr : frozen.input≠pos) (hlow : ∀ b∈low,b.input≠pos)
    (hworkpos : ∀ b∈frozen::positive::low,b.work≠pos)
    (s : State) (m : List Bool) (hone : s.basis one=true)
    (hzz : s.basis zz=false) (hpzero : s.basis pos=false)
    (hzw : ∀ b∈zb,s.basis b.work=false)
    (hfw : ∀ b∈frozen::positive::low,s.basis b.work=false) :
    run (storeFlag one zz pos sign output zb frozen positive low) m s=
      ⟨s.phase,writeBit s.basis output (s.basis output ^^
        (!s.basis frozen.input &&
          !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
          decide (regValue (low.map ZeroBit.input) s.basis=0)))⟩ := by
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
  let select := !s.basis frozen.input && !ispos && decide (regValue (low.map ZeroBit.input) s.basis=0)
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
  have vselect : decide (regValue ((frozen::positive::low).map ZeroBit.input) v.basis=0)=select := by
    change decide ((if v.basis frozen.input then 1 else 0)+
      2*((if v.basis positive.input then 1 else 0)+2*regValue (low.map ZeroBit.input) v.basis)=0)=select
    rw [vlo]
    have vp : v.basis positive.input=ispos := by rw [hpos]; simp [v,writeBit]
    have vf : v.basis frozen.input=s.basis frozen.input := by simp [v,writeBit,hfr]
    rw [vp,vf]
    dsimp only [select]
    cases hf : s.basis frozen.input <;> cases hi : ispos <;> simp
  have hstore (tape : List Bool) : run (equalConstant one output (frozen::positive::low) 0) tape v=u := by
    rw [equalConstant_correct one output (frozen::positive::low) 0 hnf (by positivity) v tape vwork,vselect]
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
  rw [storeFlag,run_append,run_take,hfirst,run_append,run_take,hstore,hlast]

theorem storeFlag_predicate_value (sign frozen : Wire) (zb low : List ZeroBit)
    (lo : List Wire) (s : BasisState) (hz : zb.map ZeroBit.input=lo++[sign]) :
    (!s frozen && !(!s sign && !decide (regValue (zb.map ZeroBit.input) s=0)) &&
      decide (regValue (low.map ZeroBit.input) s=0))=
    (!s frozen && decide (signedRegValue (lo++[sign]) s≤0) &&
      decide (regValue (low.map ZeroBit.input) s=0)) := by
  rw [hz,positivePredicate_value]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp

theorem storeFlag_counts (one zz pos sign output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) :
    toffoliCount (storeFlag one zz pos sign output zb frozen positive low)=4*zb.length+low.length+4 ∧
    measurementCount (storeFlag one zz pos sign output zb frozen positive low)=4*zb.length+low.length+2 := by
  have hc := counterPositive_counts one zz pos sign zb
  have he := equalConstant_counts one output (frozen::positive::low) 0
  simp only [storeFlag,toffoliCount_append,measurementCount_append,hc.1,hc.2,he.1,he.2,List.length_cons]
  constructor <;> omega

theorem storeFlag_support (one zz pos sign output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) :
    wires (storeFlag one zz pos sign output zb frozen positive low)=
      wires (counterPositive one zz pos sign zb) ∪
        (one::output::(frozen::positive::low).flatMap ZeroBit.wires).toFinset := by
  rw [storeFlag,wires_append,wires_append,equalConstant_wires]
  ext w
  simp only [Finset.mem_union]
  tauto

end ECDSAAdd.Arithmetic.Paper935
