import ECDSAAdd.Arithmetic.Paper935.FireCleanup

namespace ECDSAAdd.Arithmetic.Paper935

theorem latch_reverse_witness (r k : Nat) (zf frozen : Bool) (hlt : r<k)
    (hactive : frozen=false → r=0) :
    (zf && !frozen) =
      ((frozen || zf) && decide ((r ^^^ (if zf && !frozen then k else 0))=k)) := by
  cases frozen <;> cases zf <;> simp_all [Nat.ne_of_lt hlt]

/-- Reverse detection needs only the post-state frozen flag and stop record. -/
theorem freezeLatch_reverse_witness (zf frozen fire : Wire) (record : List Wire) (k : Nat)
    (hn : record.Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (s : State) (m : List Bool) (hclean : s.basis fire=false)
    (hlt : regValue record s.basis<k)
    (hactive : s.basis frozen=false → regValue record s.basis=0) :
    let v := run (freezeLatch zf frozen fire record k) m s
    v.basis fire=(v.basis frozen && decide (regValue record v.basis=k)) := by
  have hv := freezeLatch_run zf frozen fire record k hn hzf hfr hf hz hk s m hclean
  dsimp only
  rw [hv.2.1,hv.2.2.1,hv.2.2.2.1]
  exact latch_reverse_witness _ _ _ _ hlt hactive

/-- Recompute a retired firing bit from frozen AND record=k. All comparison
work is restored before the record can be changed. -/
theorem remintFire_run (frozen fire : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (frozen::fire::bs.flatMap ZeroBit.wires).Nodup)
    (hff : frozen≠fire) (hi : fire∉bs.map ZeroBit.input)
    (hw : fire∉bs.map ZeroBit.work) (hk : k<2^bs.length)
    (s : State) (m : List Bool) (hz : ∀ b∈bs,s.basis b.work=false)
    (hfire : s.basis fire=(s.basis frozen &&
      decide (regValue (bs.map ZeroBit.input) s.basis=k))) :
    run (equalConstant frozen fire bs k) m
      ⟨s.phase,writeBit s.basis fire false⟩=s := by
  let u : State := ⟨s.phase,writeBit s.basis fire false⟩
  have huz : ∀ b∈bs,u.basis b.work=false := by
    intro b hb
    have hbf : b.work≠fire := fun h => hw (h ▸ List.mem_map.mpr ⟨b,hb,rfl⟩)
    simp [u,writeBit,hbf,hz b hb]
  have hr : regValue (bs.map ZeroBit.input) u.basis=
      regValue (bs.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro q hq
    simp [u,writeBit,show q≠fire from fun h => hi (h ▸ hq)]
  change run (equalConstant frozen fire bs k) m u=s
  rw [equalConstant_correct frozen fire bs k hn hk u m huz,hr]
  have huf : u.basis frozen=s.basis frozen := by simp [u,writeBit,hff]
  rw [huf,←hfire]
  have hut : u.basis fire=false := by simp [u,writeBit]
  rw [hut]
  simp only [Bool.false_xor]
  apply (show ∀ a b : State,a.phase=b.phase → a.basis=b.basis → a=b from
    fun ⟨ap,ab⟩ ⟨bp,bb⟩ hp hb => by cases hp; cases hb; rfl)
  · rfl
  · funext q
    by_cases hq : q=fire
    · subst q; simp [writeBit]
    · simp [u,writeBit,hq]

def unfreezeRecord (frozen fire : Wire) (bs : List ZeroBit) (k : Nat) : Program :=
  equalConstant frozen fire bs k ++ recordToggle fire frozen (bs.map ZeroBit.input) k

/-- Reusing the cleared fire wire, reverse detection restores exactly the
pre-record state, including every scratch bit and phase. -/
theorem unfreezeRecord_after_latch (zf frozen fire : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (bs.map ZeroBit.input).Nodup)
    (hc : (frozen::fire::bs.flatMap ZeroBit.wires).Nodup)
    (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉bs.map ZeroBit.input) (hz : frozen∉bs.map ZeroBit.input)
    (hw : fire∉bs.map ZeroBit.work) (hk : k<2^bs.length)
    (s : State) (m n : List Bool) (hclean : s.basis fire=false)
    (hlt : regValue (bs.map ZeroBit.input) s.basis<k)
    (hactive : s.basis frozen=false → regValue (bs.map ZeroBit.input) s.basis=0)
    (hwork : ∀ b∈bs,
      (run (freezeLatch zf frozen fire (bs.map ZeroBit.input) k) m s).basis b.work=false) :
    let v := run (freezeLatch zf frozen fire (bs.map ZeroBit.input) k) m s
    run (unfreezeRecord frozen fire bs k) n ⟨v.phase,writeBit v.basis fire false⟩ =
      run (mintFire zf frozen fire) [] s := by
  have hkl : k<2^(bs.map ZeroBit.input).length := by simpa using hk
  have hp := freezeLatch_reverse_witness zf frozen fire (bs.map ZeroBit.input) k
    hn hzf hfr hf hz hkl s m hclean hlt hactive
  dsimp only
  rw [unfreezeRecord,run_append,run_take,
    remintFire_run frozen fire bs k hc (Ne.symm hfr) hf hw hk _ n hwork hp]
  simp only [freezeLatch,run_append,mintFire,measurementCount,List.take_zero,List.drop_zero]
  exact recordToggle_roundtrip fire frozen (bs.map ZeroBit.input) k hn hfr hf hz hkl _ _ _

/-- R13-style negative AND retirement, with phase correction. -/
def eraseFire (zf frozen fire : Wire) : Program :=
  [.X frozen] ++ eraseAnd zf frozen fire ++ [.X frozen]

theorem eraseFire_run (zf frozen fire : Wire) (hzf : zf≠frozen)
    (hzr : zf≠fire) (hfr : fire≠frozen) (s : State) (m : List Bool)
    (hp : s.basis fire=(s.basis zf && !s.basis frozen)) :
    run (eraseFire zf frozen fire) m s=⟨s.phase,writeBit s.basis fire false⟩ := by
  let u : State := ⟨s.phase,writeBit s.basis frozen (!s.basis frozen)⟩
  have hu : run [.X frozen] [] s=u := rfl
  have hp' : u.basis fire=(u.basis zf && u.basis frozen) := by
    simpa [u,writeBit,hfr,hzf] using hp
  simp only [eraseFire,run_append,run_take,measurementCount,List.drop_zero,List.take_zero,hu]
  rw [eraseAnd_run zf frozen fire hzr (Ne.symm hfr) u m hp']
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=frozen
  · subst q; simp [u,writeBit,Ne.symm hfr]
  · by_cases hqr : q=fire
    · subst q; simp [u,writeBit,hfr]
    · simp [u,writeBit,hq,hqr]

theorem mintFire_eraseFire (zf frozen fire : Wire) (hzf : zf≠frozen)
    (hzr : zf≠fire) (hfr : fire≠frozen) (s : State) (m n : List Bool)
    (hclean : s.basis fire=false) :
    run (eraseFire zf frozen fire) n (run (mintFire zf frozen fire) m s)=s := by
  have hp : (run (mintFire zf frozen fire) m s).basis fire =
      ((run (mintFire zf frozen fire) m s).basis zf &&
        !(run (mintFire zf frozen fire) m s).basis frozen) := by
    rw [mintFire_run zf frozen fire hzf hfr]
    simp [writeBit,hclean,hzr,Ne.symm hfr]
  rw [eraseFire_run zf frozen fire hzf hzr hfr _ n hp,mintFire_run zf frozen fire hzf hfr]
  apply (show ∀ a b : State,a.phase=b.phase → a.basis=b.basis → a=b from
    fun ⟨ap,ab⟩ ⟨bp,bb⟩ hp hb => by cases hp; cases hb; rfl)
  · rfl
  · funext q
    by_cases hq : q=fire
    · subst q; simp [writeBit,hclean]
    · simp [writeBit,hq]

theorem unfreezeRecord_counts (frozen fire : Wire) (bs : List ZeroBit) (k : Nat) :
    toffoliCount (unfreezeRecord frozen fire bs k)=bs.length ∧
      measurementCount (unfreezeRecord frozen fire bs k)=bs.length := by
  simp [unfreezeRecord,toffoliCount_append,measurementCount_append,equalConstant_counts,
    recordToggle_counts]

theorem eraseFire_counts (zf frozen fire : Wire) :
    toffoliCount (eraseFire zf frozen fire)=0 ∧
      measurementCount (eraseFire zf frozen fire)=1 := by
  simp [eraseFire,eraseAnd,toffoliCount,measurementCount]

/-- The local reverse record-and-retire sequence restores the entire original
state even though the forward fire bit has already been cleared. Intervening
author arithmetic stages are not included in this local roundtrip. -/
theorem unfreeze_roundtrip (zf frozen fire : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (bs.map ZeroBit.input).Nodup)
    (hc : (frozen::fire::bs.flatMap ZeroBit.wires).Nodup)
    (hzf : zf≠frozen) (hzr : zf≠fire) (hfr : fire≠frozen)
    (hf : fire∉bs.map ZeroBit.input) (hz : frozen∉bs.map ZeroBit.input)
    (hw : fire∉bs.map ZeroBit.work) (hk : k<2^bs.length)
    (s : State) (m n : List Bool) (hclean : s.basis fire=false)
    (hlt : regValue (bs.map ZeroBit.input) s.basis<k)
    (hactive : s.basis frozen=false → regValue (bs.map ZeroBit.input) s.basis=0)
    (hwork : ∀ b∈bs,
      (run (freezeLatch zf frozen fire (bs.map ZeroBit.input) k) m s).basis b.work=false) :
    let v := run (freezeLatch zf frozen fire (bs.map ZeroBit.input) k) m s
    run (unfreezeRecord frozen fire bs k ++ eraseFire zf frozen fire) n
      ⟨v.phase,writeBit v.basis fire false⟩=s := by
  dsimp only
  rw [run_append,run_take,
    unfreezeRecord_after_latch zf frozen fire bs k hn hc hzf hfr hf hz hw hk s m n
      hclean hlt hactive hwork]
  exact mintFire_eraseFire zf frozen fire hzf hzr hfr s [] _ hclean

theorem unfreezeRecord_support (frozen fire : Wire) (bs : List ZeroBit) (k : Nat) :
    wires (unfreezeRecord frozen fire bs k) ⊆
      (frozen::fire::bs.flatMap ZeroBit.wires).toFinset := by
  rw [unfreezeRecord,wires_append,equalConstant_wires]
  apply Finset.union_subset
  · exact Finset.Subset.refl _
  · apply (recordToggle_support fire frozen (bs.map ZeroBit.input) k).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq ⊢
    rcases hq with hq | hq | hq
    · exact Or.inl hq
    · exact Or.inr (Or.inl hq)
    · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
      exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))

theorem eraseFire_support (zf frozen fire : Wire) :
    wires (eraseFire zf frozen fire)⊆[zf,frozen,fire].toFinset := by
  simp [eraseFire,eraseAnd,wires,Instr.wires,correctionWires,Finset.insert_subset_iff]

theorem unfreeze_in_arena (zf frozen fire : Wire) (bs : List ZeroBit) (k : Nat)
    (h : (zf::frozen::fire::bs.flatMap ZeroBit.wires).toFinset⊆arenaWires) :
    wires (unfreezeRecord frozen fire bs k ++ eraseFire zf frozen fire)⊆arenaWires := by
  rw [wires_append]
  apply Finset.union_subset
  · apply (unfreezeRecord_support frozen fire bs k).trans
    exact (by simp : (frozen::fire::bs.flatMap ZeroBit.wires).toFinset ⊆
      (zf::frozen::fire::bs.flatMap ZeroBit.wires).toFinset).trans h
  · apply (eraseFire_support zf frozen fire).trans
    apply Finset.Subset.trans _ h
    simp [Finset.insert_subset_iff]

theorem unfreeze_six_counts (zf frozen fire : Wire) (bs : List ZeroBit) (k : Nat)
    (h : bs.length=6) :
    toffoliCount (unfreezeRecord frozen fire bs k ++ eraseFire zf frozen fire)=6 ∧
      measurementCount (unfreezeRecord frozen fire bs k ++ eraseFire zf frozen fire)=7 := by
  simp [toffoliCount_append,measurementCount_append,unfreezeRecord_counts,eraseFire_counts,h]

end ECDSAAdd.Arithmetic.Paper935
