import ECDSAAdd.Arithmetic.Paper935.PositiveFlag

namespace ECDSAAdd.Arithmetic.Paper935

/-- Compute positivity from the actual signed row, then restore the exact-zero
witness. Repeating this circuit clears its output if the row is unchanged. -/
def counterPositive (one zz pos sign : Wire) (bs : List ZeroBit) : Program :=
  equalConstant one zz bs 0 ++
    (positiveFlag sign zz pos ++ equalConstant one zz bs 0)

theorem counterPositive_run (one zz pos sign : Wire) (bs : List ZeroBit)
    (hn : (pos::one::zz::bs.flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈bs.map ZeroBit.input) (s : State) (m : List Bool)
    (hone : s.basis one=true) (hzz : s.basis zz=false)
    (hw : ∀ b∈bs,s.basis b.work=false) :
    run (counterPositive one zz pos sign bs) m s=
      ⟨s.phase,writeBit s.basis pos (s.basis pos ^^
        (!s.basis sign && !decide (regValue (bs.map ZeroBit.input) s.basis=0)))⟩ := by
  have hni := (List.nodup_cons.mp hn).2
  have hp : pos∉one::zz::bs.flatMap ZeroBit.wires := (List.nodup_cons.mp hn).1
  have ho : one∉zz::bs.flatMap ZeroBit.wires := (List.nodup_cons.mp hni).1
  have hz : zz∉bs.flatMap ZeroBit.wires := (List.nodup_cons.mp (List.nodup_cons.mp hni).2).1
  have ins (b : ZeroBit) (hb : b∈bs) : b.input∈bs.flatMap ZeroBit.wires :=
    List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩
  have works (b : ZeroBit) (hb : b∈bs) : b.work∈bs.flatMap ZeroBit.wires :=
    List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩
  have sp : sign≠pos := by
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hsg
    exact fun hh => hp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hh ▸ he ▸ ins b hb)))
  have sz : sign≠zz := by
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hsg
    exact fun hh => hz (hh ▸ he ▸ ins b hb)
  have zp : zz≠pos := fun hh => hp (by simp [hh])
  have oz : one≠zz := fun hh => ho (by simp [hh])
  have op : one≠pos := fun hh => hp (by simp [hh])
  let ztest := decide (regValue (bs.map ZeroBit.input) s.basis=0)
  let positive := !s.basis sign && !ztest
  let v : State := ⟨s.phase,writeBit s.basis zz ztest⟩
  let u : State := ⟨s.phase,writeBit v.basis pos (s.basis pos ^^ positive)⟩
  have hfirst (tape : List Bool) : run (equalConstant one zz bs 0) tape s=v := by
    rw [equalConstant_correct one zz bs 0 hni (by positivity) s tape hw]
    simp [v,ztest,hone,hzz]
  have hpositive (tape : List Bool) : run (positiveFlag sign zz pos) tape v=u := by
    rw [positiveFlag_run sign zz pos sz sp zp]
    simp [u,v,positive,writeBit,sz,Ne.symm zp]
  have huwork : ∀ b∈bs,u.basis b.work=false := by
    intro b hb
    have hz' : b.work≠zz := fun hh => hz (hh ▸ works b hb)
    have hp' : b.work≠pos := fun hh => hp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hh ▸ works b hb)))
    simp [u,v,writeBit,hz',hp',hw b hb]
  have hug : regValue (bs.map ZeroBit.input) u.basis=regValue (bs.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hh
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hh
    have hz' : b.input≠zz := fun hh => hz (hh ▸ ins b hb)
    have hp' : b.input≠pos := fun hh => hp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hh ▸ ins b hb)))
    simp [u,v,writeBit,hz',hp']
  have hlast (tape : List Bool) : run (equalConstant one zz bs 0) tape u=
      ⟨s.phase,writeBit s.basis pos (s.basis pos ^^ positive)⟩ := by
    rw [equalConstant_correct one zz bs 0 hni (by positivity) u tape huwork,hug]
    apply congrArg (State.mk s.phase)
    funext w
    by_cases hz' : w=zz <;> by_cases hp' : w=pos <;>
      simp_all [u,v,ztest,writeBit,Function.update_apply]
  rw [counterPositive,run_append,run_take,hfirst,run_append,run_take,hpositive,hlast]

theorem counterPositive_counts (one zz pos sign : Wire) (bs : List ZeroBit) :
    toffoliCount (counterPositive one zz pos sign bs)=2*bs.length+1 ∧
    measurementCount (counterPositive one zz pos sign bs)=2*bs.length := by
  have h := equalConstant_counts one zz bs 0
  have hp := positiveFlag_counts sign zz pos
  simp only [counterPositive,toffoliCount_append,measurementCount_append,h.1,h.2,hp.1,hp.2.1]
  constructor <;> omega

theorem counterPositive_support (one zz pos sign : Wire) (bs : List ZeroBit) :
    wires (counterPositive one zz pos sign bs)=
      (one::zz::bs.flatMap ZeroBit.wires).toFinset ∪ {sign,zz,pos} := by
  rw [counterPositive,wires_append,wires_append,equalConstant_wires,(positiveFlag_support sign zz pos).1]
  ext w
  simp only [Finset.mem_union]
  tauto

end ECDSAAdd.Arithmetic.Paper935
