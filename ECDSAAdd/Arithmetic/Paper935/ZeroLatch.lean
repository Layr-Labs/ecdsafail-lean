import ECDSAAdd.Arithmetic.Paper935.Activity
import ECDSAAdd.Arithmetic.Paper935.Unfreeze
import ECDSAAdd.Arithmetic.EqualConstant
import ECDSAAdd.Arithmetic.SignedWordBits

namespace ECDSAAdd.Arithmetic.Paper935

/-- Detect zero on the actual row, latch, retire old activity, and clear the zero witness.
The fire bit is retained for offset-based retirement. -/
def zeroLatch (one zf frozen fire active : Wire) (bs : List ZeroBit)
    (record : List Wire) (k : Nat) : Program :=
  equalConstant one zf bs 0 ++
    (latchRetireActivity zf frozen fire active record k ++ equalConstant one zf bs 0)

theorem zeroLatch_run (one zf frozen fire active : Wire) (bs : List ZeroBit)
    (record : List Wire) (k : Nat)
    (hp : (one::zf::bs.flatMap ZeroBit.wires).Nodup)
    (hn : record.Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉record)
    (hazf : active≠zf) (hzfire : zf≠fire) (hzrecord : zf∉record)
    (hstable : ∀ w∈one::bs.flatMap ZeroBit.wires,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉record)
    (s : State) (m : List Bool) (hone : s.basis one=true) (hzc : s.basis zf=false)
    (hwork : ∀ b∈bs,s.basis b.work=false) (hc : s.basis fire=false)
    (ha : s.basis active= !s.basis frozen) :
    let v : State := ⟨s.phase,writeBit s.basis zf (decide (regValue (bs.map ZeroBit.input) s.basis=0))⟩
    let l := run (freezeLatch zf frozen fire record k) (m.drop bs.length) v
    run (zeroLatch one zf frozen fire active bs record k) m s=
      ⟨s.phase,writeBit (writeBit l.basis active false) zf false⟩ := by
  let v : State := ⟨s.phase,writeBit s.basis zf (decide (regValue (bs.map ZeroBit.input) s.basis=0))⟩
  let ms := m.drop bs.length
  let t := run (latchRetireActivity zf frozen fire active record k) ms v
  have hp0 := equalConstant_correct one zf bs 0 hp (by positivity) s m hwork
  have hv : run (equalConstant one zf bs 0) m s=v := by
    simpa only [hzc,hone,Bool.false_xor,Bool.true_and] using hp0
  have vkeep (w : Wire) (hw : w≠zf) : v.basis w=s.basis w := by simp [v,writeBit,hw]
  have vc : v.basis fire=false := (vkeep fire hzfire.symm).trans hc
  have va : v.basis active= !v.basis frozen := by rw [vkeep active hazf,vkeep frozen hzf.symm,ha]
  have hmid := latchRetireActivity_run zf frozen fire active record k hn hzf hfr hf hz hk
    haf haz har v ms vc va
  have hl := freezeLatch_run zf frozen fire record k hn hzf hfr hf hz hk v ms vc
  have midkeep (w : Wire) (hwa : w≠active) (hwf : w≠fire) (hwz : w≠frozen) (hwr : w∉record) :
      t.basis w=v.basis w := by
    dsimp only [t]
    dsimp only at hmid
    rw [hmid]
    simp only [writeBit,Function.update_apply,hwa,ite_false]
    exact hl.2.2.2.2 w hwf hwz hwr
  have zoutside : zf∉one::bs.flatMap ZeroBit.wires := by
    have h1 := (List.nodup_cons.mp hp).1
    have h2 := (List.nodup_cons.mp (List.nodup_cons.mp hp).2).1
    simp only [List.mem_cons] at h1 ⊢
    tauto
  have keep (w : Wire) (hw : w∈one::bs.flatMap ZeroBit.wires) : t.basis w=s.basis w := by
    obtain ⟨h1,h2,h3,h4⟩ := hstable w hw
    exact (midkeep w h1 h2 h3 h4).trans (vkeep w (fun h => zoutside (h ▸ hw)))
  have ti : regValue (bs.map ZeroBit.input) t.basis=regValue (bs.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    apply keep
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩)
  have tw : ∀ b∈bs,t.basis b.work=false := by
    intro b hb
    refine (keep b.work ?_).trans (hwork b hb)
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩)
  have tz : t.basis zf=decide (regValue (bs.map ZeroBit.input) s.basis=0) := by
    rw [midkeep zf hazf.symm hzfire hzf hzrecord]
    simp [v,writeBit]
  have tone : t.basis one=true := (keep one (by simp)).trans hone
  have tp : t.phase=s.phase := by dsimp only [t]; dsimp only at hmid; rw [hmid]
  have hm : measurementCount (latchRetireActivity zf frozen fire active record k)=0 := by
    simp [latchRetireActivity,measurementCount_append,(freezeLatch_counts zf frozen fire record k).2.1,
      retireActivity,measurementCount]
  have hp2 := equalConstant_correct one zf bs 0 hp (by positivity) t ms tw
  have hfinal : run (equalConstant one zf bs 0) ms t=⟨s.phase,writeBit t.basis zf false⟩ := by
    simpa only [tp,tz,tone,ti,Bool.true_and,Bool.xor_self] using hp2
  dsimp only
  rw [zeroLatch,run_append,run_take,hv,(equalConstant_counts one zf bs 0).2,
    run_append,run_take,hm,List.drop_zero]
  rw [hfinal]
  dsimp only [t]
  dsimp only at hmid
  rw [hmid]

theorem zeroLatch_spec (one zf frozen fire active : Wire) (bs : List ZeroBit)
    (record : List Wire) (k : Nat)
    (hp : (one::zf::bs.flatMap ZeroBit.wires).Nodup)
    (hn : record.Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉record)
    (hazf : active≠zf) (hzfire : zf≠fire) (hzrecord : zf∉record)
    (hstable : ∀ w∈one::bs.flatMap ZeroBit.wires,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉record)
    (s : State) (m : List Bool) (hone : s.basis one=true) (hzc : s.basis zf=false)
    (hwork : ∀ b∈bs,s.basis b.work=false) (hc : s.basis fire=false)
    (ha : s.basis active= !s.basis frozen) :
    let t := run (zeroLatch one zf frozen fire active bs record k) m s
    t.phase=s.phase ∧ t.basis active=false ∧ t.basis zf=false ∧
      t.basis fire=(decide (regValue (bs.map ZeroBit.input) s.basis=0) && !s.basis frozen) ∧
      t.basis frozen=(s.basis frozen || decide (regValue (bs.map ZeroBit.input) s.basis=0)) ∧
      regValue record t.basis=regValue record s.basis ^^^
        (if decide (regValue (bs.map ZeroBit.input) s.basis=0) && !s.basis frozen then k else 0) ∧
      ∀ w,w≠active → w≠fire → w≠frozen → w∉record → t.basis w=s.basis w := by
  let v : State := ⟨s.phase,writeBit s.basis zf (decide (regValue (bs.map ZeroBit.input) s.basis=0))⟩
  have keep (w : Wire) (hw : w≠zf) : v.basis w=s.basis w := by simp [v,writeBit,hw]
  have vc : v.basis fire=false := (keep fire hzfire.symm).trans hc
  have vz : v.basis zf=decide (regValue (bs.map ZeroBit.input) s.basis=0) := by simp [v,writeBit]
  have vr : regValue record v.basis=regValue record s.basis :=
    regValue_congr _ _ _ (fun w hw => keep w (fun h => hzrecord (h ▸ hw)))
  have h := freezeLatch_run zf frozen fire record k hn hzf hfr hf hz hk v (m.drop bs.length) vc
  have hr := zeroLatch_run one zf frozen fire active bs record k hp hn hzf hfr hf hz hk
    haf haz har hazf hzfire hzrecord hstable s m hone hzc hwork hc ha
  dsimp only at hr ⊢
  rw [hr]
  refine ⟨rfl,by simp [writeBit,hazf],by simp [writeBit],?_,?_,?_,?_⟩
  · simp only [writeBit,Function.update_apply,hzfire.symm,haf.symm,ite_false]
    change (run (freezeLatch zf frozen fire record k) (m.drop bs.length) v).basis fire=_
    rw [h.2.1,vz,keep frozen hzf.symm]
  · simp only [writeBit,Function.update_apply,hzf.symm,haz.symm,ite_false]
    change (run (freezeLatch zf frozen fire record k) (m.drop bs.length) v).basis frozen=_
    rw [h.2.2.1,vz,keep frozen hzf.symm]
  · have he : regValue record (writeBit (writeBit (run (freezeLatch zf frozen fire record k)
          (m.drop bs.length) v).basis active false) zf false)=
        regValue record (run (freezeLatch zf frozen fire record k) (m.drop bs.length) v).basis := by
      apply regValue_congr
      intro w hw
      simp [writeBit,show w≠active from fun h => har (h ▸ hw),
        show w≠zf from fun h => hzrecord (h ▸ hw)]
    rw [he,h.2.2.2.1,vz,vr,keep frozen hzf.symm]
  · intro w hwa hwf hwz hwr
    by_cases hw : w=zf
    · subst w; simp [writeBit,hzc]
    · simp only [writeBit,Function.update_apply,hw,hwa,ite_false]
      exact (h.2.2.2.2 w hwf hwz hwr).trans (keep w hw)

theorem zeroLatch_fire_witness (one zf frozen fire active : Wire) (bs : List ZeroBit)
    (record : List Wire) (k : Nat)
    (hp : (one::zf::bs.flatMap ZeroBit.wires).Nodup)
    (hn : record.Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉record)
    (hazf : active≠zf) (hzfire : zf≠fire) (hzrecord : zf∉record)
    (hstable : ∀ w∈one::bs.flatMap ZeroBit.wires,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉record)
    (s : State) (m : List Bool) (hone : s.basis one=true) (hzc : s.basis zf=false)
    (hwork : ∀ b∈bs,s.basis b.work=false) (hc : s.basis fire=false)
    (ha : s.basis active= !s.basis frozen)
    (hlt : regValue record s.basis<k)
    (hactive : s.basis frozen=false → regValue record s.basis=0) :
    let t := run (zeroLatch one zf frozen fire active bs record k) m s
    t.basis fire=(t.basis frozen && decide (regValue record t.basis=k)) := by
  have h := zeroLatch_spec one zf frozen fire active bs record k hp hn hzf hfr hf hz hk
    haf haz har hazf hzfire hzrecord hstable s m hone hzc hwork hc ha
  dsimp only
  rw [h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1]
  exact latch_reverse_witness _ _ _ _ hlt hactive

/-- Zero in the signed interpretation is exactly zero in the physical word. -/
theorem signedRegValue_zero_iff (xs : List Wire) (s : BasisState) :
    signedRegValue xs s=0 ↔ regValue xs s=0 := by
  constructor
  · intro h
    have hh := congrArg (fun x : Int => x%((2^xs.length:Nat):Int)) h
    simp only [signedRegValue,signedDecode_emod,Int.zero_emod] at hh
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast regValue_lt xs s)] at hh
    exact_mod_cast hh
  · intro h
    simp [signedRegValue,h,signedDecode]

theorem zeroLatch_counts (one zf frozen fire active : Wire) (bs : List ZeroBit)
    (record : List Wire) (k : Nat) :
    toffoliCount (zeroLatch one zf frozen fire active bs record k)=2*bs.length+1 ∧
    measurementCount (zeroLatch one zf frozen fire active bs record k)=2*bs.length := by
  have hp := equalConstant_counts one zf bs 0
  have hl := freezeLatch_counts zf frozen fire record k
  have ha := activity_counts frozen fire active
  simp only [zeroLatch,latchRetireActivity,toffoliCount_append,measurementCount_append,
    hp.1,hp.2,hl.1,hl.2.1,ha.2.2.1,ha.2.2.2]
  omega

theorem zeroLatch_support (one zf frozen fire active : Wire) (bs : List ZeroBit)
    (record : List Wire) (k : Nat) :
    wires (zeroLatch one zf frozen fire active bs record k)⊆
      (one::zf::frozen::fire::active::(record++bs.flatMap ZeroBit.wires)).toFinset := by
  have hp : wires (equalConstant one zf bs 0)⊆
      (one::zf::frozen::fire::active::(record++bs.flatMap ZeroBit.wires)).toFinset := by
    rw [equalConstant_wires]
    intro w hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢
    tauto
  have hl : wires (latchRetireActivity zf frozen fire active record k)⊆
      (one::zf::frozen::fire::active::(record++bs.flatMap ZeroBit.wires)).toFinset := by
    rw [latchRetireActivity,wires_append,(activity_wires frozen fire active).2]
    apply Finset.union_subset
    · apply (freezeLatch_support zf frozen fire record k).1.trans
      intro w hw
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢
      tauto
    · intro w hw
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
      tauto
  rw [zeroLatch,wires_append,wires_append]
  exact Finset.union_subset hp (Finset.union_subset hl hp)

end ECDSAAdd.Arithmetic.Paper935
