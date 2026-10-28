import ECDSAAdd.Arithmetic.Paper935.FreezeLatch
import ECDSAAdd.Arithmetic.EqualConstant

namespace ECDSAAdd.Arithmetic.Paper935

/-- An already-computed AND can be erased for either measurement result,
with its phase correction included. -/
def eraseAnd (a b target : Wire) : Program := [.measureX target [] [.CZ a b]]

theorem eraseAnd_run (a b target : Wire) (ha : a≠target) (hb : b≠target)
    (s : State) (m : List Bool) (h : s.basis target=(s.basis a && s.basis b)) :
    run (eraseAnd a b target) m s=⟨s.phase,writeBit s.basis target false⟩ := by
  simp only [eraseAnd,run]
  cases hm : m.headD false <;> simp [measureAndCorrect,correct,writeBit,ha,hb,h]

/-- Strictly older offsets cannot collide with the present step's record. -/
theorem latch_fire_witness (r k : Nat) (zf frozen : Bool) (hlt : r<k)
    (hactive : frozen=false → r=0) :
    (zf && !frozen) =
      ((zf && decide ((r ^^^ (if zf && !frozen then k else 0))=k)) &&
        (frozen || zf)) := by
  cases frozen <;> cases zf <;> simp_all [Nat.ne_of_lt hlt]

/-- F7's retained fire is derivable from the post-state, rather than an
independent cleanup premise, when the pre-step offset is strictly older. -/
theorem freezeLatch_fire_witness (zf frozen fire : Wire) (record : List Wire) (k : Nat)
    (hn : record.Nodup) (hzf : zf≠frozen) (hzr : zf≠fire) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hzw : zf∉record)
    (hk : k<2^record.length) (s : State) (m : List Bool)
    (hclean : s.basis fire=false) (hlt : regValue record s.basis<k)
    (hactive : s.basis frozen=false → regValue record s.basis=0) :
    let v := run (freezeLatch zf frozen fire record k) m s
    v.basis fire=((v.basis zf && decide (regValue record v.basis=k)) && v.basis frozen) := by
  have hv := freezeLatch_run zf frozen fire record k hn hzf hfr hf hz hk s m hclean
  dsimp only
  rw [hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2 zf hzr hzf hzw]
  exact latch_fire_witness _ _ _ _ hlt hactive

/-- A composed implementation of fire retirement. Comparison work is cleared
by each equalConstant call; the second call clears its output witness.
This recomputes the comparison rather than retaining the author's trail. -/
def fireCleanup (zf frozen fire witness : Wire) (bs : List ZeroBit) (k : Nat) : Program :=
  equalConstant zf witness bs k ++ eraseAnd witness frozen fire ++
    equalConstant zf witness bs k

theorem fireCleanup_run (zf frozen fire witness : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (zf::witness::bs.flatMap ZeroBit.wires).Nodup)
    (hzf : zf≠fire) (hwf : witness≠fire) (hff : frozen≠fire) (hfw : frozen≠witness)
    (hinput : fire∉bs.map ZeroBit.input) (hwork : fire∉bs.map ZeroBit.work)
    (hk : k<2^bs.length) (s : State) (m : List Bool)
    (hw : s.basis witness=false) (hz : ∀ b∈bs,s.basis b.work=false)
    (hfire : s.basis fire=((s.basis zf &&
      decide (regValue (bs.map ZeroBit.input) s.basis=k)) && s.basis frozen)) :
    run (fireCleanup zf frozen fire witness bs k) m s =
      ⟨s.phase,writeBit s.basis fire false⟩ := by
  let pred := s.basis zf && decide (regValue (bs.map ZeroBit.input) s.basis=k)
  let u : State := ⟨s.phase,writeBit s.basis witness pred⟩
  let v : State := ⟨s.phase,writeBit u.basis fire false⟩
  have hc (n : List Bool) : run (equalConstant zf witness bs k) n s=u := by
    rw [equalConstant_correct zf witness bs k hn hk s n hz]
    simp [u,pred,hw]
  have hf : u.basis fire=(u.basis witness && u.basis frozen) := by
    simpa [u,writeBit,Ne.symm hwf,hfw,pred] using hfire
  have he (n : List Bool) : run (eraseAnd witness frozen fire) n u=v := by
    exact eraseAnd_run witness frozen fire hwf hff u n hf
  have hnw : witness∉bs.flatMap ZeroBit.wires := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  have hzw : zf≠witness := by
    exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hi (b : ZeroBit) (hb : b∈bs) : b.input≠witness := by
    intro h
    exact hnw (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires,h]⟩)
  have hbw (b : ZeroBit) (hb : b∈bs) : b.work≠witness := by
    intro h
    exact hnw (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires,h]⟩)
  have hvz : ∀ b∈bs,v.basis b.work=false := by
    intro b hb
    have hbf : b.work≠fire := fun h => hwork (h ▸ List.mem_map.mpr ⟨b,hb,rfl⟩)
    simp [v,u,writeBit,hbf,hbw b hb,hz b hb]
  have hreg : regValue (bs.map ZeroBit.input) v.basis =
      regValue (bs.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro q hq
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
    have hbf : b.input≠fire := fun h => hinput (h ▸ List.mem_map.mpr ⟨b,hb,rfl⟩)
    simp [v,u,writeBit,hbf,hi b hb]
  have hout (n : List Bool) : run (equalConstant zf witness bs k) n v =
      ⟨s.phase,writeBit s.basis fire false⟩ := by
    rw [equalConstant_correct zf witness bs k hn hk v n hvz,hreg]
    have hvw : v.basis witness=pred := by simp [v,u,writeBit,hwf]
    have hvzf : v.basis zf=s.basis zf := by simp [v,u,writeBit,hzf,hzw]
    rw [hvw,hvzf]
    change State.mk s.phase (writeBit v.basis witness (pred ^^ pred)) = _
    rw [Bool.xor_self]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q=witness
    · subst q; simp [writeBit,hwf,hw]
    · by_cases hqf : q=fire
      · subst q; simp [v,u,writeBit,Ne.symm hwf]
      · simp [v,u,writeBit,hq,hqf]
  simp only [fireCleanup,run_append,run_take]
  rw [hc,he,hout]

theorem fireCleanup_counts (zf frozen fire witness : Wire) (bs : List ZeroBit) (k : Nat) :
    toffoliCount (fireCleanup zf frozen fire witness bs k)=2*bs.length ∧
      measurementCount (fireCleanup zf frozen fire witness bs k)=2*bs.length+1 := by
  simp [fireCleanup,toffoliCount_append,measurementCount_append,equalConstant_counts,
    eraseAnd,toffoliCount,measurementCount]
  omega

/-- Latch then retire fire, deriving the cleanup predicate from the old
offset invariant. Scratch freshness and nonaliasing remain explicit. -/
theorem freezeLatch_cleanup (zf frozen fire witness : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (bs.map ZeroBit.input).Nodup)
    (hc : (zf::witness::bs.flatMap ZeroBit.wires).Nodup)
    (hzf : zf≠frozen) (hzr : zf≠fire) (hfr : fire≠frozen)
    (hwf : witness≠fire) (hfw : frozen≠witness)
    (hf : fire∉bs.map ZeroBit.input) (hz : frozen∉bs.map ZeroBit.input)
    (hzw : zf∉bs.map ZeroBit.input) (hwork : fire∉bs.map ZeroBit.work)
    (hframe : ∀ q∈witness::bs.map ZeroBit.work,
      q≠fire ∧ q≠frozen ∧ q∉bs.map ZeroBit.input)
    (hk : k<2^bs.length) (s : State) (m n : List Bool)
    (hclean : s.basis fire=false) (hw : s.basis witness=false)
    (hscratch : ∀ b∈bs,s.basis b.work=false)
    (hlt : regValue (bs.map ZeroBit.input) s.basis<k)
    (hactive : s.basis frozen=false → regValue (bs.map ZeroBit.input) s.basis=0) :
    let v := run (freezeLatch zf frozen fire (bs.map ZeroBit.input) k) m s
    run (fireCleanup zf frozen fire witness bs k) n v =
      ⟨s.phase,writeBit v.basis fire false⟩ := by
  let v := run (freezeLatch zf frozen fire (bs.map ZeroBit.input) k) m s
  have hkl : k<2^(bs.map ZeroBit.input).length := by simpa using hk
  have hv := freezeLatch_run zf frozen fire (bs.map ZeroBit.input) k hn hzf hfr hf hz hkl s m hclean
  have hpred := freezeLatch_fire_witness zf frozen fire (bs.map ZeroBit.input) k
    hn hzf hzr hfr hf hz hzw hkl s m hclean hlt hactive
  have hvc : v.basis witness=false := by
    obtain ⟨h1,h2,h3⟩ := hframe witness (by simp)
    exact (hv.2.2.2.2 witness h1 h2 h3).trans hw
  have hvs : ∀ b∈bs,v.basis b.work=false := by
    intro b hb
    obtain ⟨h1,h2,h3⟩ := hframe b.work
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b,hb,rfl⟩))
    exact (hv.2.2.2.2 b.work h1 h2 h3).trans (hscratch b hb)
  change run (fireCleanup zf frozen fire witness bs k) n v = _
  rw [fireCleanup_run zf frozen fire witness bs k hc hzr hwf (Ne.symm hfr)
    hfw hf hwork hk v n hvc hvs hpred]
  rw [show v.phase=s.phase from hv.1]

/-- The integer execution invariant supplies both offset hypotheses used to
reconstruct fire at every armed step. -/
theorem pinWalk_cleanup_offset (tmin t : Nat) (p x : Int) (ht : tmin≤t) :
    (pinWalk tmin p x t).offset<t+1-tmin ∧
      ((pinWalk tmin p x t).frozen=false → (pinWalk tmin p x t).offset=0) := by
  obtain ⟨hf,hbound⟩ := pinWalk_record tmin p x t
  constructor
  · omega
  · intro h
    have hn : ¬0<(pinWalk tmin p x t).offset := by
      intro hp
      have hh := hf.mpr hp
      simp [h] at hh
    omega

theorem fireCleanup_support (zf frozen fire witness : Wire) (bs : List ZeroBit) (k : Nat) :
    wires (fireCleanup zf frozen fire witness bs k) ⊆
      (frozen::fire::zf::witness::bs.flatMap ZeroBit.wires).toFinset := by
  have hc := equalConstant_wires zf witness bs k
  simp only [fireCleanup,wires_append,hc]
  apply Finset.union_subset
  · apply Finset.union_subset
    · intro q hq
      simp only [List.toFinset_cons,Finset.mem_insert] at *
      tauto
    · simp [eraseAnd,wires,Instr.wires,correctionWires,Finset.insert_subset_iff]
  · intro q hq
    simp only [List.toFinset_cons,Finset.mem_insert] at *
    tauto

theorem fireCleanup_in_arena (zf frozen fire witness : Wire) (bs : List ZeroBit) (k : Nat)
    (h : (frozen::fire::zf::witness::bs.flatMap ZeroBit.wires).toFinset⊆arenaWires) :
    wires (fireCleanup zf frozen fire witness bs k)⊆arenaWires :=
  (fireCleanup_support zf frozen fire witness bs k).trans h

theorem fireCleanup_six_counts (zf frozen fire witness : Wire) (bs : List ZeroBit) (k : Nat)
    (h : bs.length=6) :
    toffoliCount (fireCleanup zf frozen fire witness bs k)=12 ∧
      measurementCount (fireCleanup zf frozen fire witness bs k)=13 := by
  simpa [h] using fireCleanup_counts zf frozen fire witness bs k

end ECDSAAdd.Arithmetic.Paper935
