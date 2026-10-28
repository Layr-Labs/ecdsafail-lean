import ECDSAAdd.Arithmetic.Paper935.FreezeLatch

namespace ECDSAAdd.Arithmetic.Paper935

/-- Compute the old activity from the persistent frozen flag. -/
def mintActivity (frozen active : Wire) : Program := [.X active,.CX frozen active]

/-- Retire old activity after the latch changed frozen; fire records that change. -/
def retireActivity (frozen fire active : Wire) : Program :=
  [.X active,.CX frozen active,.CX fire active]

theorem mintActivity_run (frozen active : Wire) (hne : frozen≠active)
    (s : State) (m : List Bool) (hc : s.basis active=false) :
    run (mintActivity frozen active) m s=⟨s.phase,writeBit s.basis active (!s.basis frozen)⟩ := by
  apply congrArg (State.mk s.phase)
  funext w
  cases hf : s.basis frozen <;> simp [writeBit,hne,hc,hf]

theorem retireActivity_run (frozen fire active : Wire)
    (hf : frozen≠active) (hr : fire≠active) (s : State) (m : List Bool)
    (ha : s.basis active=(!(s.basis frozen) ^^ s.basis fire)) :
    run (retireActivity frozen fire active) m s=⟨s.phase,writeBit s.basis active false⟩ := by
  apply congrArg (State.mk s.phase)
  funext w
  cases hz : s.basis frozen <;> cases hb : s.basis fire <;>
    simp [writeBit,hf,hr,ha,hz,hb]

/-- The latch itself establishes the witness needed to retire activity. -/
theorem freezeLatch_activity (zf frozen fire active : Wire) (record : List Wire) (k : Nat)
    (hn : record.Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉record)
    (s : State) (m : List Bool) (hc : s.basis fire=false)
    (ha : s.basis active= !s.basis frozen) :
    let t := run (freezeLatch zf frozen fire record k) m s
    t.basis active=(!(t.basis frozen) ^^ t.basis fire) := by
  have h := freezeLatch_run zf frozen fire record k hn hzf hfr hf hz hk s m hc
  dsimp only
  rw [h.2.2.2.2 active haf haz har,h.2.2.1,h.2.1,ha]
  cases s.basis frozen <;> cases s.basis zf <;> rfl

/-- Concrete latch followed by activity retirement, with no extra scratch. -/
def latchRetireActivity (zf frozen fire active : Wire) (record : List Wire) (k : Nat) : Program :=
  freezeLatch zf frozen fire record k ++ retireActivity frozen fire active

theorem latchRetireActivity_run (zf frozen fire active : Wire) (record : List Wire) (k : Nat)
    (hn : record.Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉record)
    (s : State) (m : List Bool) (hc : s.basis fire=false)
    (ha : s.basis active= !s.basis frozen) :
    let t := run (freezeLatch zf frozen fire record k) m s
    run (latchRetireActivity zf frozen fire active record k) m s=
      ⟨s.phase,writeBit t.basis active false⟩ := by
  have h := freezeLatch_run zf frozen fire record k hn hzf hfr hf hz hk s m hc
  have hp := freezeLatch_activity zf frozen fire active record k hn hzf hfr hf hz hk
    haf haz har s m hc ha
  dsimp only
  rw [latchRetireActivity,run_append,run_take,
    retireActivity_run frozen fire active haz.symm haf.symm _ _ hp,h.1]

/-- Compute activity, apply a latch, and retire the same activity wire. -/
def activityLatch (zf frozen fire active : Wire) (record : List Wire) (k : Nat) : Program :=
  mintActivity frozen active ++ latchRetireActivity zf frozen fire active record k

theorem activityLatch_run (zf frozen fire active : Wire) (record : List Wire) (k : Nat)
    (hn : record.Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉record) (hazf : active≠zf)
    (s : State) (m : List Bool) (hc : s.basis fire=false) (ha : s.basis active=false) :
    let t := run (activityLatch zf frozen fire active record k) m s
    t.phase=s.phase ∧ t.basis active=false ∧
      t.basis fire=(s.basis zf && !s.basis frozen) ∧
      t.basis frozen=(s.basis frozen || s.basis zf) ∧
      regValue record t.basis=regValue record s.basis ^^^
        (if s.basis zf && !s.basis frozen then k else 0) ∧
      ∀ w,w≠fire → w≠frozen → w∉record → t.basis w=s.basis w := by
  let v := run (mintActivity frozen active) m s
  have hv := mintActivity_run frozen active haz.symm s m ha
  have keep (w : Wire) (hw : w≠active) : v.basis w=s.basis w := by
    dsimp only [v]; rw [hv]; simp [writeBit,hw]
  have va : v.basis active= !v.basis frozen := by
    dsimp only [v]; rw [hv]; simp [writeBit,haz.symm]
  have vc : v.basis fire=false := (keep fire haf.symm).trans hc
  have h := latchRetireActivity_run zf frozen fire active record k hn hzf hfr hf hz hk
    haf haz har v m vc va
  have hl := freezeLatch_run zf frozen fire record k hn hzf hfr hf hz hk v m vc
  have vr : regValue record v.basis=regValue record s.basis :=
    regValue_congr record _ _ (fun w hw => keep w (fun hh => har (hh ▸ hw)))
  have vp : v.phase=s.phase := by dsimp only [v]; rw [hv]
  dsimp only
  rw [activityLatch,run_append,run_take]
  have hm : measurementCount (mintActivity frozen active)=0 := rfl
  simp only [hm,List.drop_zero]
  dsimp only at h
  rw [h]
  refine ⟨vp,by simp [writeBit],?_,?_,?_,?_⟩
  · simp only [writeBit,Function.update_apply,haf.symm,ite_false,hl.2.1,
      keep zf hazf.symm,keep frozen haz.symm]
  · simp only [writeBit,Function.update_apply,haz.symm,ite_false,hl.2.2.1,
      keep zf hazf.symm,keep frozen haz.symm]
  · have hreg : regValue record (writeBit (run (freezeLatch zf frozen fire record k) m v).basis active false)=
        regValue record (run (freezeLatch zf frozen fire record k) m v).basis := by
      apply regValue_congr
      intro w hw
      simp [writeBit,show w≠active from fun hh => har (hh ▸ hw)]
    rw [hreg,hl.2.2.2.1,vr,keep zf hazf.symm,keep frozen haz.symm]
  · intro w hwf hwz hwr
    by_cases hwa : w=active
    · subst w; simp [writeBit,ha]
    · simp only [writeBit,Function.update_apply,hwa,ite_false]
      exact (hl.2.2.2.2 w hwf hwz hwr).trans (keep w hwa)

theorem activity_counts (frozen fire active : Wire) :
    toffoliCount (mintActivity frozen active)=0 ∧ measurementCount (mintActivity frozen active)=0 ∧
    toffoliCount (retireActivity frozen fire active)=0 ∧
    measurementCount (retireActivity frozen fire active)=0 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem activity_wires (frozen fire active : Wire) :
    wires (mintActivity frozen active)=[frozen,active].toFinset ∧
    wires (retireActivity frozen fire active)=[frozen,fire,active].toFinset := by
  constructor <;> ext w <;> simp [mintActivity,retireActivity,wires,Instr.wires]; all_goals tauto

theorem activityLatch_counts (zf frozen fire active : Wire) (record : List Wire) (k : Nat) :
    toffoliCount (activityLatch zf frozen fire active record k)=1 ∧
    measurementCount (activityLatch zf frozen fire active record k)=0 := by
  have h := freezeLatch_counts zf frozen fire record k
  simp [activityLatch,latchRetireActivity,mintActivity,retireActivity,
    toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,h.1,h.2.1]

theorem activityLatch_support (zf frozen fire active : Wire) (record : List Wire) (k : Nat) :
    wires (activityLatch zf frozen fire active record k)⊆(active::zf::frozen::fire::record).toFinset := by
  rw [activityLatch,latchRetireActivity,wires_append,wires_append,
    (activity_wires frozen fire active).1,(activity_wires frozen fire active).2]
  apply Finset.union_subset
  · intro w hw
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  · apply Finset.union_subset
    · exact (freezeLatch_support zf frozen fire record k).1.trans (by simp)
    · intro w hw
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
      tauto

end ECDSAAdd.Arithmetic.Paper935
