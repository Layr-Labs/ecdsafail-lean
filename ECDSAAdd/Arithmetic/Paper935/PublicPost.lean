import ECDSAAdd.Arithmetic.Paper935.ZeroFreeze

namespace ECDSAAdd.Arithmetic.Paper935

/-- The public early interval omits zero detection; activity is still retired. -/
def publicPost (armed : Bool) (one zf frozen fire active witness : Wire)
    (bs rb : List ZeroBit) (k : Nat) : Program :=
  if armed then zeroFreeze one zf frozen fire active witness bs rb k
  else retireActivity frozen fire active

theorem publicPost_spec (armed : Bool) (one zf frozen fire active witness : Wire) (bs : List ZeroBit)
    (rb : List ZeroBit) (k : Nat)
    (hp : (one::zf::bs.flatMap ZeroBit.wires).Nodup)
    (hn : (rb.map ZeroBit.input).Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉(rb.map ZeroBit.input)) (hz : frozen∉(rb.map ZeroBit.input)) (hk : armed=true → k<2^(rb.map ZeroBit.input).length)
    (haf : active≠fire) (haz : active≠frozen) (har : active∉(rb.map ZeroBit.input))
    (hazf : active≠zf) (hzfire : zf≠fire) (hzrecord : zf∉(rb.map ZeroBit.input))
    (hstable : ∀ w∈one::bs.flatMap ZeroBit.wires,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉(rb.map ZeroBit.input))
    (s : State) (m : List Bool) (hone : s.basis one=true) (hzc : s.basis zf=false)
    (hwork : ∀ b∈bs,s.basis b.work=false) (hc : s.basis fire=false)
    (ha : s.basis active= !s.basis frozen)
    (hlt : armed=true → regValue (rb.map ZeroBit.input) s.basis<k)
    (hactive : s.basis frozen=false → regValue (rb.map ZeroBit.input) s.basis=0)
    (hcnd : (one::witness::rb.flatMap ZeroBit.wires).Nodup)
    (hwf : witness≠fire) (hfw : frozen≠witness) (hfirework : fire∉rb.map ZeroBit.work)
    (hcleanframe : ∀ w∈witness::rb.map ZeroBit.work,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉rb.map ZeroBit.input)
    (hw : s.basis witness=false) (hcw : ∀ b∈rb,s.basis b.work=false) :
    let t := run (publicPost armed one zf frozen fire active witness bs rb k) m s
    t.phase=s.phase ∧ t.basis active=false ∧ t.basis zf=false ∧ t.basis fire=false ∧
      t.basis frozen=(s.basis frozen || (armed && decide (regValue (bs.map ZeroBit.input) s.basis=0))) ∧
      regValue (rb.map ZeroBit.input) t.basis=regValue (rb.map ZeroBit.input) s.basis ^^^
        (if armed && decide (regValue (bs.map ZeroBit.input) s.basis=0) && !s.basis frozen then k else 0) ∧
      ∀ w,w≠active → w≠frozen → w∉rb.map ZeroBit.input → t.basis w=s.basis w := by
  cases armed with
  | true =>
    have h := zeroFreeze_spec one zf frozen fire active witness bs rb k
      hp hn hzf hfr hf hz (hk rfl) haf haz har hazf hzfire hzrecord hstable s m hone hzc hwork hc ha
      (hlt rfl) hactive hcnd hwf hfw hfirework hcleanframe hw hcw
    simpa only [publicPost,ite_true,Bool.true_and] using h
  | false =>
    have hr := retireActivity_run frozen fire active haz.symm haf.symm s m
      (by simpa only [hc,Bool.xor_false] using ha)
    dsimp only
    simp only [publicPost,Bool.false_eq_true,ite_false,hr,Bool.false_and,Bool.or_false,Nat.xor_zero]
    refine ⟨trivial,by simp [writeBit],?_,?_,?_,?_,?_⟩
    · simp [writeBit,hazf.symm,hzc]
    · simp [writeBit,haf.symm,hc]
    · simp [writeBit,haz.symm]
    · apply regValue_congr
      intro w hw
      simp [writeBit,show w≠active from fun h => har (h ▸ hw)]
    · intro w hwa _ _
      simp [writeBit,hwa]

theorem publicPost_counts (armed : Bool) (one zf frozen fire active witness : Wire)
    (bs rb : List ZeroBit) (k : Nat) :
    toffoliCount (publicPost armed one zf frozen fire active witness bs rb k)=
      (if armed then 2*bs.length+1+2*rb.length else 0) ∧
    measurementCount (publicPost armed one zf frozen fire active witness bs rb k)=
      (if armed then 2*bs.length+(2*rb.length+1) else 0) := by
  cases armed
  · exact ⟨rfl,rfl⟩
  · exact zeroFreeze_counts one zf frozen fire active witness bs rb k

theorem publicPost_support (armed : Bool) (one zf frozen fire active witness : Wire)
    (bs rb : List ZeroBit) (k : Nat) :
    wires (publicPost armed one zf frozen fire active witness bs rb k)⊆
      (one::zf::frozen::fire::active::witness::
        (rb.map ZeroBit.input++bs.flatMap ZeroBit.wires++rb.flatMap ZeroBit.wires)).toFinset := by
  cases armed
  · rw [publicPost,if_neg Bool.false_ne_true,(activity_wires frozen fire active).2]
    intro w hw
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  · exact zeroFreeze_support one zf frozen fire active witness bs rb k

/-- The hardware flag/XOR-record formulas match the existing pin-step semantics
when the tested row is the post-arithmetic g value. -/
theorem pinStep_flag_record (tmin t : Nat) (u : PinState)
    (hactive : u.frozen=false → u.offset=0) :
    let g := if u.frozen then u.rows.g else (ECDSAAdd.Divsteps.zStep u.rows).g
    (pinStep tmin t u).frozen=(u.frozen || (decide (tmin≤t) && decide (g=0))) ∧
    (pinStep tmin t u).offset=u.offset ^^^
      (if decide (tmin≤t) && decide (g=0) && !u.frozen then t+1-tmin else 0) := by
  cases hf : u.frozen
  · have ho := hactive hf
    by_cases ht : tmin≤t <;> by_cases hg : (ECDSAAdd.Divsteps.zStep u.rows).g=0 <;>
      simp [pinStep,hf,ho,ht,hg]
  · simp [pinStep,hf]

end ECDSAAdd.Arithmetic.Paper935
