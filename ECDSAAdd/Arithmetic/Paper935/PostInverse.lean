import ECDSAAdd.Arithmetic.Paper935.PublicPost
import ECDSAAdd.Framework.GateInverse

namespace ECDSAAdd.Arithmetic.Paper935

private theorem state_eq {s t : State} (hp : s.phase=t.phase) (hb : s.basis=t.basis) : s=t := by
  cases s; cases t; simp_all

theorem equalConstant_clean (c target : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (c::target::bs.flatMap ZeroBit.wires).Nodup) (hk : k<2^bs.length)
    (s : State) (m : List Bool) (hc : ∀ b∈bs,s.basis b.work=false) :
    ∀ b∈bs,(run (equalConstant c target bs k) m s).basis b.work=false := by
  rw [equalConstant_correct c target bs k hn hk s m hc]
  intro b hb
  have hne : b.work≠target := by
    intro he
    exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
      (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires,←he]⟩)
  simpa [writeBit,hne] using hc b hb

theorem equalConstant_roundtrip (c target : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (c::target::bs.flatMap ZeroBit.wires).Nodup) (hk : k<2^bs.length)
    (s : State) (m n : List Bool) (hc : ∀ b∈bs,s.basis b.work=false) :
    run (equalConstant c target bs k) n (run (equalConstant c target bs k) m s)=s := by
  have hc' := equalConstant_clean c target bs k hn hk s m hc
  have hct : c≠target := fun he => (List.nodup_cons.mp hn).1 (by simp [he])
  have hi : target∉bs.map ZeroBit.input := by
    intro hw
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hw
    exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
      (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires,←he]⟩)
  have hv : regValue (bs.map ZeroBit.input) (run (equalConstant c target bs k) m s).basis=
      regValue (bs.map ZeroBit.input) s.basis := by
    rw [equalConstant_correct c target bs k hn hk s m hc]
    apply regValue_congr
    intro w hw
    simp [writeBit,show w≠target from fun he => hi (he ▸ hw)]
  rw [equalConstant_correct c target bs k hn hk _ n hc',hv,
    equalConstant_correct c target bs k hn hk s m hc]
  apply state_eq
  · rfl
  · funext w
    by_cases hw : w=target
    · subst w; simp [writeBit,hct]
    · simp [writeBit,hw]

def latchRetireInverse (zf frozen fire active : Wire) (record : List Wire) (k : Nat) : Program :=
  (retireActivity frozen fire active).reverse ++ freezeUnlatch zf frozen fire record k

theorem latchRetire_roundtrip (zf frozen fire active : Wire) (record : List Wire) (k : Nat)
    (hn : record.Nodup) (hzf : zf≠frozen) (hzr : zf≠fire) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (hfa : frozen≠active) (hra : fire≠active) (s : State) (m n : List Bool) :
    run (latchRetireInverse zf frozen fire active record k) n
      (run (latchRetireActivity zf frozen fire active record k) m s)=s := by
  have proper : ProperProgram (retireActivity frozen fire active) := by
    simp [retireActivity,ProperProgram,ProperGate,hfa,hra]
  rw [latchRetireActivity,latchRetireInverse,run_append,run_take,run_append,run_take]
  rw [run_reverse_proper _ proper]
  exact freezeLatch_roundtrip zf frozen fire record k hn hzf hzr hfr hf hz hk s m _

theorem latchRetire_support (zf frozen fire active : Wire) (record : List Wire) (k : Nat) :
    wires (latchRetireActivity zf frozen fire active record k)⊆(active::zf::frozen::fire::record).toFinset := by
  rw [latchRetireActivity,wires_append,(activity_wires frozen fire active).2]
  apply Finset.union_subset
  · exact (freezeLatch_support zf frozen fire record k).1.trans (by simp)
  · intro w hw
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto

def zeroLatchInverse (one zf frozen fire active : Wire) (bs : List ZeroBit)
    (record : List Wire) (k : Nat) : Program :=
  equalConstant one zf bs 0 ++
    (latchRetireInverse zf frozen fire active record k ++ equalConstant one zf bs 0)

theorem zeroLatch_roundtrip (one zf frozen fire active : Wire) (bs : List ZeroBit)
    (record : List Wire) (k : Nat)
    (hp : (one::zf::bs.flatMap ZeroBit.wires).Nodup)
    (hn : record.Nodup) (hzf : zf≠frozen) (hzr : zf≠fire) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (hfa : frozen≠active) (hra : fire≠active)
    (hstable : ∀ b∈bs,b.work≠active ∧ b.work≠fire ∧ b.work≠frozen ∧ b.work∉record)
    (s : State) (m n : List Bool) (hwork : ∀ b∈bs,s.basis b.work=false) :
    run (zeroLatchInverse one zf frozen fire active bs record k) n
      (run (zeroLatch one zf frozen fire active bs record k) m s)=s := by
  let probe := equalConstant one zf bs 0
  let latch := latchRetireActivity zf frozen fire active record k
  let v := run probe m s
  let t := run latch (m.drop (measurementCount probe)) v
  have vwork := equalConstant_clean one zf bs 0 hp (by positivity) s m hwork
  have twork : ∀ b∈bs,t.basis b.work=false := by
    intro b hb
    obtain ⟨h1,h2,h3,h4⟩ := hstable b hb
    have hz : b.work≠zf := by
      intro he
      exact (List.nodup_cons.mp (List.nodup_cons.mp hp).2).1
        (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires,←he]⟩)
    have outside : b.work∉wires latch := by
      intro hw
      have hh := latchRetire_support zf frozen fire active record k hw
      simp only [List.mem_toFinset,List.mem_cons] at hh
      exact hh.elim h1 (fun hh => hh.elim hz (fun hh => hh.elim h3 (fun hh => hh.elim h2 h4)))
    exact (run_preserves_outside latch _ v b.work outside).trans (vwork b hb)
  simp only [zeroLatch,zeroLatchInverse,run_append,run_take]
  rw [equalConstant_roundtrip one zf bs 0 hp (by positivity) t _ n twork]
  rw [latchRetire_roundtrip zf frozen fire active record k hn hzf hzr hfr hf hz hk hfa hra]
  exact equalConstant_roundtrip one zf bs 0 hp (by positivity) s m _ hwork

def zeroFreezeInverse (one zf frozen fire active : Wire) (bs rb : List ZeroBit) (k : Nat) : Program :=
  equalConstant frozen fire rb k ++ zeroLatchInverse one zf frozen fire active bs (rb.map ZeroBit.input) k

theorem zeroFreeze_roundtrip (one zf frozen fire active witness : Wire) (bs : List ZeroBit)
    (rb : List ZeroBit) (k : Nat)
    (hp : (one::zf::bs.flatMap ZeroBit.wires).Nodup)
    (hn : (rb.map ZeroBit.input).Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉(rb.map ZeroBit.input)) (hz : frozen∉(rb.map ZeroBit.input)) (hk : k<2^(rb.map ZeroBit.input).length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉(rb.map ZeroBit.input))
    (hazf : active≠zf) (hzfire : zf≠fire) (hzrecord : zf∉(rb.map ZeroBit.input))
    (hstable : ∀ w∈one::bs.flatMap ZeroBit.wires,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉(rb.map ZeroBit.input))
    (s : State) (m n : List Bool) (hone : s.basis one=true) (hzc : s.basis zf=false)
    (hwork : ∀ b∈bs,s.basis b.work=false) (hc : s.basis fire=false)
    (ha : s.basis active= !s.basis frozen)
    (hlt : regValue (rb.map ZeroBit.input) s.basis<k)
    (hactive : s.basis frozen=false → regValue (rb.map ZeroBit.input) s.basis=0)
    (hcnd : (one::witness::rb.flatMap ZeroBit.wires).Nodup)
    (hwf : witness≠fire) (hfw : frozen≠witness) (hfirework : fire∉rb.map ZeroBit.work)
    (hcleanframe : ∀ w∈witness::rb.map ZeroBit.work,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉rb.map ZeroBit.input)
    (hw : s.basis witness=false) (hcw : ∀ b∈rb,s.basis b.work=false)
    (hremint : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) :
    run (zeroFreezeInverse one zf frozen fire active bs rb k) n
      (run (zeroFreeze one zf frozen fire active witness bs rb k) m s)=s := by
  let t := run (zeroLatch one zf frozen fire active bs (rb.map ZeroBit.input) k) m s
  have ht := zeroLatch_spec one zf frozen fire active bs (rb.map ZeroBit.input) k hp hn hzf hfr hf hz hk
    haf haz har hazf hzfire hzrecord hstable s m hone hzc hwork hc ha
  have he := zeroFreeze_run one zf frozen fire active witness bs rb k hp hn hzf hfr hf hz hk
    haf haz har hazf hzfire hzrecord hstable s m hone hzc hwork hc ha hlt hactive hcnd hwf hfw hfirework hcleanframe hw hcw
  have hpending := zeroLatch_fire_witness one zf frozen fire active bs (rb.map ZeroBit.input) k
    hp hn hzf hfr hf hz hk haf haz har hazf hzfire hzrecord hstable s m hone hzc hwork hc ha hlt hactive
  have tw : ∀ b∈rb,t.basis b.work=false := by
    intro b hb
    obtain ⟨h1,h2,h3,h4⟩ := hcleanframe b.work
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b,hb,rfl⟩))
    exact (ht.2.2.2.2.2.2 b.work h1 h2 h3 h4).trans (hcw b hb)
  have restored : run (equalConstant frozen fire rb k) n
      (run (zeroFreeze one zf frozen fire active witness bs rb k) m s)=t := by
    rw [he,←ht.1]
    exact remintFire_run frozen fire rb k hremint hfr.symm hf hfirework (by simpa using hk) t n tw hpending
  rw [zeroFreezeInverse,run_append,run_take,restored]
  exact zeroLatch_roundtrip one zf frozen fire active bs (rb.map ZeroBit.input) k hp hn hzf hzfire hfr hf hz hk
    haz.symm haf.symm (fun b hb => hstable b.work
      (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))) s m _ hwork

def publicPostInverse (armed : Bool) (one zf frozen fire active : Wire)
    (bs rb : List ZeroBit) (k : Nat) : Program :=
  if armed then zeroFreezeInverse one zf frozen fire active bs rb k
  else (retireActivity frozen fire active).reverse

theorem publicPost_roundtrip (armed : Bool) (one zf frozen fire active witness : Wire) (bs : List ZeroBit)
    (rb : List ZeroBit) (k : Nat)
    (hp : (one::zf::bs.flatMap ZeroBit.wires).Nodup)
    (hn : (rb.map ZeroBit.input).Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉(rb.map ZeroBit.input)) (hz : frozen∉(rb.map ZeroBit.input)) (hk : armed=true → k<2^(rb.map ZeroBit.input).length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉(rb.map ZeroBit.input))
    (hazf : active≠zf) (hzfire : zf≠fire) (hzrecord : zf∉(rb.map ZeroBit.input))
    (hstable : ∀ w∈one::bs.flatMap ZeroBit.wires,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉(rb.map ZeroBit.input))
    (s : State) (m n : List Bool) (hone : s.basis one=true) (hzc : s.basis zf=false)
    (hwork : ∀ b∈bs,s.basis b.work=false) (hc : s.basis fire=false)
    (ha : s.basis active= !s.basis frozen)
    (hlt : armed=true → regValue (rb.map ZeroBit.input) s.basis<k)
    (hactive : s.basis frozen=false → regValue (rb.map ZeroBit.input) s.basis=0)
    (hcnd : (one::witness::rb.flatMap ZeroBit.wires).Nodup)
    (hwf : witness≠fire) (hfw : frozen≠witness) (hfirework : fire∉rb.map ZeroBit.work)
    (hcleanframe : ∀ w∈witness::rb.map ZeroBit.work,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉rb.map ZeroBit.input)
    (hw : s.basis witness=false) (hcw : ∀ b∈rb,s.basis b.work=false)
    (hremint : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) :
    run (publicPostInverse armed one zf frozen fire active bs rb k) n
      (run (publicPost armed one zf frozen fire active witness bs rb k) m s)=s := by
  cases armed with
  | true =>
    simp only [publicPost,publicPostInverse,ite_true]
    exact zeroFreeze_roundtrip one zf frozen fire active witness bs rb k hp hn hzf hfr hf hz (hk rfl)
      haf haz har hazf hzfire hzrecord hstable s m n hone hzc hwork hc ha (hlt rfl) hactive
      hcnd hwf hfw hfirework hcleanframe hw hcw hremint
  | false =>
    simp only [publicPost,publicPostInverse,Bool.false_eq_true,ite_false]
    exact run_reverse_proper _ (by simp [retireActivity,ProperGate,haz.symm,haf.symm]) s m n

end ECDSAAdd.Arithmetic.Paper935
