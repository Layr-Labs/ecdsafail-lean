import ECDSAAdd.Arithmetic.Paper935.BlockedLatch

namespace ECDSAAdd.Arithmetic.Paper935.BlockedPost
open ECDSAAdd.Arithmetic.Paper935

/-- Actual post-arithmetic zero test, freeze record update, activity retirement,
and record-derived fire cleanup. Both witnesses and all comparison work are restored. -/
def zeroFreeze (one zf frozen fire active witness : Wire) (bs : List BlockedZero.Block) (rb : List ZeroBit)
    (k : Nat) : Program :=
  zeroLatch one zf frozen fire active bs (rb.map ZeroBit.input) k ++
    fireCleanup one frozen fire witness rb k

theorem zeroFreeze_run (one zf frozen fire active witness : Wire) (bs : List BlockedZero.Block)
    (rb : List ZeroBit) (k : Nat)
    (hp : BlockedZero.Valid one zf bs)
    (hn : (rb.map ZeroBit.input).Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉(rb.map ZeroBit.input)) (hz : frozen∉(rb.map ZeroBit.input)) (hk : k<2^(rb.map ZeroBit.input).length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉(rb.map ZeroBit.input))
    (hazf : active≠zf) (hzfire : zf≠fire) (hzrecord : zf∉(rb.map ZeroBit.input))
    (hstable : ∀ w∈one::BlockedZero.ports bs,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉(rb.map ZeroBit.input))
    (s : State) (m : List Bool) (hone : s.basis one=true) (hzc : s.basis zf=false)
    (hwork : BlockedZero.clean bs s.basis) (hc : s.basis fire=false)
    (ha : s.basis active= !s.basis frozen)
    (hlt : regValue (rb.map ZeroBit.input) s.basis<k)
    (hactive : s.basis frozen=false → regValue (rb.map ZeroBit.input) s.basis=0)
    (hcnd : (one::witness::rb.flatMap ZeroBit.wires).Nodup)
    (hwf : witness≠fire) (hfw : frozen≠witness) (hfirework : fire∉rb.map ZeroBit.work)
    (hcleanframe : ∀ w∈witness::rb.map ZeroBit.work,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉rb.map ZeroBit.input)
    (hw : s.basis witness=false) (hcw : ∀ b∈rb,s.basis b.work=false) :
    let t := run (zeroLatch one zf frozen fire active bs (rb.map ZeroBit.input) k) m s
    run (zeroFreeze one zf frozen fire active witness bs rb k) m s=
      ⟨s.phase,writeBit t.basis fire false⟩ := by
  let p := zeroLatch one zf frozen fire active bs (rb.map ZeroBit.input) k
  let t := run p m s
  have h := zeroLatch_spec one zf frozen fire active bs (rb.map ZeroBit.input) k hp hn hzf hfr hf hz hk
    haf haz har hazf hzfire hzrecord hstable s m hone hzc hwork hc ha
  have hfired := zeroLatch_fire_witness one zf frozen fire active bs (rb.map ZeroBit.input) k
    hp hn hzf hfr hf hz hk haf haz har hazf hzfire hzrecord hstable s m hone hzc hwork hc ha hlt hactive
  have frame := h.2.2.2.2.2.2
  obtain ⟨hoa,hof,hoz,hor⟩ := hstable one (by simp)
  have tone : t.basis one=true := (frame one hoa hof hoz hor).trans hone
  obtain ⟨hwa,hwr,hwz,hwrecord⟩ := hcleanframe witness (by simp)
  have tw : t.basis witness=false := (frame witness hwa hwr hwz hwrecord).trans hw
  have tc : ∀ b∈rb,t.basis b.work=false := by
    intro b hb
    obtain ⟨h1,h2,h3,h4⟩ := hcleanframe b.work
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b,hb,rfl⟩))
    exact (frame b.work h1 h2 h3 h4).trans (hcw b hb)
  have pred : t.basis fire=((t.basis one && decide (regValue (rb.map ZeroBit.input) t.basis=k)) &&
      t.basis frozen) := by
    rw [tone,hfired]
    simp only [Bool.true_and,Bool.and_comm]
    rfl
  have hc := fireCleanup_run one frozen fire witness rb k hcnd hof hwf hfr.symm hfw hf hfirework
    (by simpa using hk) t (m.drop (measurementCount p)) tw tc pred
  dsimp only
  rw [zeroFreeze,run_append,run_take,hc,h.1]

theorem zeroFreeze_spec (one zf frozen fire active witness : Wire) (bs : List BlockedZero.Block)
    (rb : List ZeroBit) (k : Nat)
    (hp : BlockedZero.Valid one zf bs)
    (hn : (rb.map ZeroBit.input).Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉(rb.map ZeroBit.input)) (hz : frozen∉(rb.map ZeroBit.input)) (hk : k<2^(rb.map ZeroBit.input).length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉(rb.map ZeroBit.input))
    (hazf : active≠zf) (hzfire : zf≠fire) (hzrecord : zf∉(rb.map ZeroBit.input))
    (hstable : ∀ w∈one::BlockedZero.ports bs,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉(rb.map ZeroBit.input))
    (s : State) (m : List Bool) (hone : s.basis one=true) (hzc : s.basis zf=false)
    (hwork : BlockedZero.clean bs s.basis) (hc : s.basis fire=false)
    (ha : s.basis active= !s.basis frozen)
    (hlt : regValue (rb.map ZeroBit.input) s.basis<k)
    (hactive : s.basis frozen=false → regValue (rb.map ZeroBit.input) s.basis=0)
    (hcnd : (one::witness::rb.flatMap ZeroBit.wires).Nodup)
    (hwf : witness≠fire) (hfw : frozen≠witness) (hfirework : fire∉rb.map ZeroBit.work)
    (hcleanframe : ∀ w∈witness::rb.map ZeroBit.work,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉rb.map ZeroBit.input)
    (hw : s.basis witness=false) (hcw : ∀ b∈rb,s.basis b.work=false) :
    let t := run (zeroFreeze one zf frozen fire active witness bs rb k) m s
    t.phase=s.phase ∧ t.basis active=false ∧ t.basis zf=false ∧ t.basis fire=false ∧
      t.basis frozen=(s.basis frozen || decide (regValue (BlockedZero.inputs bs) s.basis=0)) ∧
      regValue (rb.map ZeroBit.input) t.basis=regValue (rb.map ZeroBit.input) s.basis ^^^
        (if decide (regValue (BlockedZero.inputs bs) s.basis=0) && !s.basis frozen then k else 0) ∧
      ∀ w,w≠active → w≠frozen → w∉rb.map ZeroBit.input → t.basis w=s.basis w := by
  have h := zeroLatch_spec one zf frozen fire active bs (rb.map ZeroBit.input) k
    hp hn hzf hfr hf hz hk haf haz har hazf hzfire hzrecord hstable s m hone hzc hwork hc ha
  have hr := zeroFreeze_run one zf frozen fire active witness bs rb k
    hp hn hzf hfr hf hz hk haf haz har hazf hzfire hzrecord hstable s m hone hzc hwork hc ha
    hlt hactive hcnd hwf hfw hfirework hcleanframe hw hcw
  dsimp only at hr ⊢
  rw [hr]
  refine ⟨rfl,?_,?_,by simp [writeBit],?_,?_,?_⟩
  · simpa only [writeBit,Function.update_apply,haf,ite_false] using h.2.1
  · simpa only [writeBit,Function.update_apply,hzfire,ite_false] using h.2.2.1
  · simpa only [writeBit,Function.update_apply,hfr.symm,ite_false] using h.2.2.2.2.1
  · have he : regValue (rb.map ZeroBit.input)
        (writeBit (run (zeroLatch one zf frozen fire active bs (rb.map ZeroBit.input) k) m s).basis fire false)=
        regValue (rb.map ZeroBit.input) (run (zeroLatch one zf frozen fire active bs (rb.map ZeroBit.input) k) m s).basis := by
      apply regValue_congr
      intro w hw
      simp [writeBit,show w≠fire from fun hh => hf (hh ▸ hw)]
    rw [he,h.2.2.2.2.2.1]
  · intro w hwa hwz hwr
    by_cases hwfire : w=fire
    · subst w; simp [writeBit,hc]
    · simp only [writeBit,Function.update_apply,hwfire,ite_false]
      exact h.2.2.2.2.2.2 w hwa hwfire hwz hwr

theorem zeroFreeze_counts (one zf frozen fire active witness : Wire) (bs : List BlockedZero.Block) (rb : List ZeroBit) (k : Nat) :
    toffoliCount (zeroFreeze one zf frozen fire active witness bs rb k)=4*(BlockedZero.inputs bs).length+1+2*rb.length ∧
    measurementCount (zeroFreeze one zf frozen fire active witness bs rb k)=4*(BlockedZero.inputs bs).length+(2*rb.length+1) := by
  have hl := zeroLatch_counts one zf frozen fire active bs (rb.map ZeroBit.input) k
  have hc := fireCleanup_counts one frozen fire witness rb k
  simp only [zeroFreeze,toffoliCount_append,measurementCount_append,hl.1,hl.2,hc.1,hc.2,and_self]

theorem zeroFreeze_support (one zf frozen fire active witness : Wire) (bs : List BlockedZero.Block) (rb : List ZeroBit) (k : Nat) :
    wires (zeroFreeze one zf frozen fire active witness bs rb k)⊆
      (one::zf::frozen::fire::active::witness::
        (rb.map ZeroBit.input++BlockedZero.ports bs++rb.flatMap ZeroBit.wires)).toFinset := by
  rw [zeroFreeze,wires_append]
  apply Finset.union_subset
  · apply (zeroLatch_support one zf frozen fire active bs (rb.map ZeroBit.input) k).trans
    intro w hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢
    tauto
  · apply (fireCleanup_support one frozen fire witness rb k).trans
    intro w hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢
    tauto

end ECDSAAdd.Arithmetic.Paper935.BlockedPost
