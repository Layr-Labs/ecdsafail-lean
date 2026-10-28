import ECDSAAdd.Arithmetic.Paper935.BlockedPublicPost
import ECDSAAdd.Framework.GateInverse

namespace ECDSAAdd.Arithmetic.Paper935.BlockedPost
open ECDSAAdd.Arithmetic.Paper935

private theorem state_eq {s t : State} (hp : s.phase=t.phase) (hb : s.basis=t.basis) : s=t := by
  cases s; cases t; simp_all

theorem probe_clean (c target : Wire) (bs : List BlockedZero.Block)
    (hv : BlockedZero.Valid c target bs) (s : State) (m : List Bool)
    (hz : BlockedZero.clean bs s.basis) :
    BlockedZero.clean bs (run (BlockedZero.program c target bs) m s).basis := by
  apply clean_transfer bs s.basis _ hz
  intro w hw
  rw [BlockedZero.run_eq c target bs hv s m hz]
  simp [writeBit,show w≠target from fun he => valid_target_outside c target bs hv
    (List.mem_cons_of_mem _ (he ▸ hw))]

theorem probe_roundtrip (c target : Wire) (bs : List BlockedZero.Block)
    (hv : BlockedZero.Valid c target bs) (s : State) (m n : List Bool)
    (hz : BlockedZero.clean bs s.basis) :
    run (BlockedZero.program c target bs) n (run (BlockedZero.program c target bs) m s)=s := by
  have hz' := probe_clean c target bs hv s m hz
  have hct : c≠target := fun he => valid_target_outside c target bs hv (by simp [he])
  have hi : target∉BlockedZero.inputs bs := fun h => valid_target_outside c target bs hv
    (List.mem_cons_of_mem _ (inputs_subset_ports bs h))
  have value : regValue (BlockedZero.inputs bs) (run (BlockedZero.program c target bs) m s).basis =
      regValue (BlockedZero.inputs bs) s.basis := by
    rw [BlockedZero.run_eq c target bs hv s m hz]
    apply regValue_congr
    intro w hw
    simp [writeBit,show w≠target from fun he => hi (he ▸ hw)]
  rw [BlockedZero.run_eq c target bs hv _ n hz',BlockedZero.test_eq_zero,value,
    BlockedZero.run_eq c target bs hv s m hz,BlockedZero.test_eq_zero]
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

def zeroLatchInverse (one zf frozen fire active : Wire) (bs : List BlockedZero.Block)
    (record : List Wire) (k : Nat) : Program :=
  BlockedZero.program one zf bs ++
    (latchRetireInverse zf frozen fire active record k ++ BlockedZero.program one zf bs)

theorem zeroLatch_roundtrip (one zf frozen fire active : Wire) (bs : List BlockedZero.Block)
    (record : List Wire) (k : Nat)
    (hp : BlockedZero.Valid one zf bs)
    (hn : record.Nodup) (hzf : zf≠frozen) (hzr : zf≠fire) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (hfa : frozen≠active) (hra : fire≠active)
    (hstable : ∀ w∈BlockedZero.ports bs,w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉record)
    (s : State) (m n : List Bool) (hwork : BlockedZero.clean bs s.basis) :
    run (zeroLatchInverse one zf frozen fire active bs record k) n
      (run (zeroLatch one zf frozen fire active bs record k) m s)=s := by
  let probe := BlockedZero.program one zf bs
  let latch := latchRetireActivity zf frozen fire active record k
  let v := run probe m s
  let t := run latch (m.drop (measurementCount probe)) v
  have vwork := probe_clean one zf bs hp s m hwork
  have twork : BlockedZero.clean bs t.basis := by
    apply clean_transfer bs v.basis t.basis vwork
    intro w hw
    obtain ⟨h1,h2,h3,h4⟩ := hstable w hw
    have hz : w≠zf := fun he => valid_target_outside one zf bs hp
      (List.mem_cons_of_mem _ (he ▸ hw))
    have outside : w∉wires latch := by
      intro hq
      have hh := latchRetire_support zf frozen fire active record k hq
      simp only [List.mem_toFinset,List.mem_cons] at hh
      exact hh.elim h1 (fun hh => hh.elim hz (fun hh => hh.elim h3 (fun hh => hh.elim h2 h4)))
    exact run_preserves_outside latch _ v w outside
  simp only [zeroLatch,zeroLatchInverse,run_append,run_take]
  rw [probe_roundtrip one zf bs hp t _ n twork]
  rw [latchRetire_roundtrip zf frozen fire active record k hn hzf hzr hfr hf hz hk hfa hra]
  exact probe_roundtrip one zf bs hp s m _ hwork

def zeroFreezeInverse (one zf frozen fire active : Wire) (bs : List BlockedZero.Block) (rb : List ZeroBit) (k : Nat) : Program :=
  equalConstant frozen fire rb k ++ zeroLatchInverse one zf frozen fire active bs (rb.map ZeroBit.input) k

theorem zeroFreeze_roundtrip (one zf frozen fire active witness : Wire) (bs : List BlockedZero.Block)
    (rb : List ZeroBit) (k : Nat)
    (hp : BlockedZero.Valid one zf bs)
    (hn : (rb.map ZeroBit.input).Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉(rb.map ZeroBit.input)) (hz : frozen∉(rb.map ZeroBit.input)) (hk : k<2^(rb.map ZeroBit.input).length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉(rb.map ZeroBit.input))
    (hazf : active≠zf) (hzfire : zf≠fire) (hzrecord : zf∉(rb.map ZeroBit.input))
    (hstable : ∀ w∈one::BlockedZero.ports bs,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉(rb.map ZeroBit.input))
    (s : State) (m n : List Bool) (hone : s.basis one=true) (hzc : s.basis zf=false)
    (hwork : BlockedZero.clean bs s.basis) (hc : s.basis fire=false)
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
    haz.symm haf.symm (fun w hw => hstable w (List.mem_cons_of_mem _ hw)) s m _ hwork

def publicPostInverse (armed : Bool) (one zf frozen fire active : Wire)
    (bs : List BlockedZero.Block) (rb : List ZeroBit) (k : Nat) : Program :=
  if armed then zeroFreezeInverse one zf frozen fire active bs rb k
  else (retireActivity frozen fire active).reverse

theorem publicPost_roundtrip (armed : Bool) (one zf frozen fire active witness : Wire) (bs : List BlockedZero.Block)
    (rb : List ZeroBit) (k : Nat)
    (hp : BlockedZero.Valid one zf bs)
    (hn : (rb.map ZeroBit.input).Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉(rb.map ZeroBit.input)) (hz : frozen∉(rb.map ZeroBit.input)) (hk : armed=true → k<2^(rb.map ZeroBit.input).length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉(rb.map ZeroBit.input))
    (hazf : active≠zf) (hzfire : zf≠fire) (hzrecord : zf∉(rb.map ZeroBit.input))
    (hstable : ∀ w∈one::BlockedZero.ports bs,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉(rb.map ZeroBit.input))
    (s : State) (m n : List Bool) (hone : s.basis one=true) (hzc : s.basis zf=false)
    (hwork : BlockedZero.clean bs s.basis) (hc : s.basis fire=false)
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

end ECDSAAdd.Arithmetic.Paper935.BlockedPost
