import ECDSAAdd.Arithmetic.Paper935.FreezePin
import ECDSAAdd.Arithmetic.Paper935.Arena
import ECDSAAdd.Arithmetic.MaskedConstant

namespace ECDSAAdd.Arithmetic.Paper935

/-- Retain the firing bit while toggling the frozen flag and stop offset. -/
def recordToggle (fire frozen : Wire) (record : List Wire) (k : Nat) : Program :=
  [.CX fire frozen]++maskedConstant fire record k

theorem recordToggle_run (fire frozen : Wire) (record : List Wire) (k : Nat)
    (hn : record.Nodup) (hfr : fire≠frozen) (hf : fire∉record) (hz : frozen∉record)
    (hk : k<2^record.length) (s : State) (m : List Bool) :
    let t := run (recordToggle fire frozen record k) m s
    t.phase=s.phase ∧ t.basis fire=s.basis fire ∧
    t.basis frozen=(s.basis frozen ^^ s.basis fire) ∧
    regValue record t.basis=regValue record s.basis ^^^ (if s.basis fire then k else 0) ∧
    ∀ q,q≠frozen → q∉record → t.basis q=s.basis q := by
  let u : State := ⟨s.phase,writeBit s.basis frozen (s.basis frozen ^^ s.basis fire)⟩
  have hu : run [.CX fire frozen] [] s=u := rfl
  have hc := maskedConstant_correct fire record k hn hf hk u m
  have huf : u.basis fire=s.basis fire := by simp [u,writeBit,hfr]
  have hreg : regValue record u.basis=regValue record s.basis := by
    apply regValue_congr
    intro q hq
    simp [u,writeBit,show q≠frozen from fun h => hz (h ▸ hq)]
  simp only [recordToggle,run_append,measurementCount,List.take_zero,List.drop_zero,hu]
  refine ⟨hc.1,(hc.2.1 fire hf).trans huf,?_,?_,?_⟩
  · rw [hc.2.1 frozen hz]; simp [u,writeBit]
  · rw [hc.2.2,hreg,huf]
  · intro q hq hr
    rw [hc.2.1 q hr]
    simp [u,writeBit,hq]

theorem recordToggle_roundtrip (fire frozen : Wire) (record : List Wire) (k : Nat)
    (hn : record.Nodup) (hfr : fire≠frozen) (hf : fire∉record) (hz : frozen∉record)
    (hk : k<2^record.length) (s : State) (m n : List Bool) :
    run (recordToggle fire frozen record k) n (run (recordToggle fire frozen record k) m s)=s := by
  have h1 := recordToggle_run fire frozen record k hn hfr hf hz hk s m
  have h2 := recordToggle_run fire frozen record k hn hfr hf hz hk (run (recordToggle fire frozen record k) m s) n
  apply (show ∀ a b : State,a.phase=b.phase → a.basis=b.basis → a=b from
    fun ⟨ap,ab⟩ ⟨bp,bb⟩ hp hb => by cases hp; cases hb; rfl)
  · exact h2.1.trans h1.1
  · funext q
    by_cases hq : q=frozen
    · subst q
      rw [h2.2.2.1,h1.2.2.1,h1.2.1]
      cases s.basis frozen <;> cases s.basis fire <;> rfl
    · by_cases hr : q∈record
      · apply (regValue_eq_iff record _ _).mp _ q hr
        rw [h2.2.2.2.1,h1.2.2.2.1,h1.2.1]
        simp
      · exact (h2.2.2.2.2 q hq hr).trans (h1.2.2.2.2 q hq hr)

/-- The zero-test witness is an explicit input; proving its production from
the actual g row remains a separate obligation. -/
def mintFire (zf frozen fire : Wire) : Program :=
  [.X frozen,.CCX zf frozen fire,.X frozen]

theorem mintFire_run (zf frozen fire : Wire) (hzf : zf≠frozen)
    (hff : fire≠frozen) (s : State) (m : List Bool) :
    run (mintFire zf frozen fire) m s=
      ⟨s.phase,writeBit s.basis fire (s.basis fire ^^ (s.basis zf && !s.basis frozen))⟩ := by
  apply congrArg₂ State.mk
  · rfl
  · funext q
    by_cases hq : q=fire
    · subst q
      simp [writeBit,hzf,hff,Ne.symm hff]
    · by_cases hqf : q=frozen
      · subst q
        cases hs : s.basis frozen <;> simp [writeBit,hq,hzf,hs]
      · simp [writeBit,hq,hqf]

def freezeLatch (zf frozen fire : Wire) (record : List Wire) (k : Nat) : Program :=
  mintFire zf frozen fire++recordToggle fire frozen record k

def freezeUnlatch (zf frozen fire : Wire) (record : List Wire) (k : Nat) : Program :=
  recordToggle fire frozen record k++mintFire zf frozen fire

/-- F7 computes a live firing bit, flips the frozen flag, and XOR-writes the
public offset. The firing bit remains live for later source-style cleanup. -/
theorem freezeLatch_run (zf frozen fire : Wire) (record : List Wire) (k : Nat)
    (hn : record.Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (s : State) (m : List Bool) (hclean : s.basis fire=false) :
    let t := run (freezeLatch zf frozen fire record k) m s
    t.phase=s.phase ∧
    t.basis fire=(s.basis zf && !s.basis frozen) ∧
    t.basis frozen=(s.basis frozen || s.basis zf) ∧
    regValue record t.basis=regValue record s.basis ^^^
      (if s.basis zf && !s.basis frozen then k else 0) ∧
    ∀ q,q≠fire → q≠frozen → q∉record → t.basis q=s.basis q := by
  let u : State := ⟨s.phase,writeBit s.basis fire (s.basis zf && !s.basis frozen)⟩
  have hu : run (mintFire zf frozen fire) [] s=u := by
    rw [mintFire_run zf frozen fire hzf hfr]
    simp [hclean,u]
  have hc := recordToggle_run fire frozen record k hn hfr hf hz hk u m
  have hfired : u.basis fire=(s.basis zf && !s.basis frozen) := by simp [u,writeBit]
  have hfreeze : u.basis frozen=s.basis frozen := by simp [u,writeBit,Ne.symm hfr]
  have hreg : regValue record u.basis=regValue record s.basis := by
    apply regValue_congr
    intro q hq
    simp [u,writeBit,show q≠fire from fun h => hf (h ▸ hq)]
  simp only [freezeLatch,run_append,mintFire,measurementCount,List.take_zero,List.drop_zero] at hu ⊢
  rw [hu]
  refine ⟨hc.1,hc.2.1.trans hfired,?_,?_,?_⟩
  · rw [hc.2.2.1,hfired,hfreeze]
    cases s.basis zf <;> cases s.basis frozen <;> rfl
  · rw [hc.2.2.2.1,hreg,hfired]
  · intro q hq hfz hr
    rw [hc.2.2.2.2 q hfz hr]
    simp [u,writeBit,hq]

theorem mintFire_roundtrip (zf frozen fire : Wire) (hzf : zf≠frozen)
    (hzr : zf≠fire) (hfr : fire≠frozen) (s : State) (m n : List Bool) :
    run (mintFire zf frozen fire) n (run (mintFire zf frozen fire) m s)=s := by
  rw [mintFire_run zf frozen fire hzf hfr,mintFire_run zf frozen fire hzf hfr]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=fire
  · subst q
    cases hs : s.basis fire <;> cases hz : s.basis zf <;> cases hfz : s.basis frozen <;>
      simp [writeBit,hzr,Ne.symm hfr,hz,hfz]
  · simp [writeBit,hq]

theorem recordToggle_counts (fire frozen : Wire) (record : List Wire) (k : Nat) :
    toffoliCount (recordToggle fire frozen record k)=0 ∧
      measurementCount (recordToggle fire frozen record k)=0 := by
  simp [recordToggle,toffoliCount,
    measurementCount,maskedConstant_counts]

theorem freezeLatch_counts (zf frozen fire : Wire) (record : List Wire) (k : Nat) :
    toffoliCount (freezeLatch zf frozen fire record k)=1 ∧
      measurementCount (freezeLatch zf frozen fire record k)=0 ∧
      toffoliCount (freezeUnlatch zf frozen fire record k)=1 ∧
      measurementCount (freezeUnlatch zf frozen fire record k)=0 := by
  simp [freezeLatch,freezeUnlatch,mintFire,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,recordToggle_counts]

theorem freezeLatch_roundtrip (zf frozen fire : Wire) (record : List Wire) (k : Nat)
    (hn : record.Nodup) (hzf : zf≠frozen) (hzr : zf≠fire) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (hk : k<2^record.length)
    (s : State) (m n : List Bool) :
    run (freezeUnlatch zf frozen fire record k) n
      (run (freezeLatch zf frozen fire record k) m s)=s := by
  have hm : measurementCount (mintFire zf frozen fire)=0 := rfl
  simp only [freezeLatch,freezeUnlatch,run_append,hm,(recordToggle_counts fire frozen record k).2,
    List.take_zero,List.drop_zero]
  rw [recordToggle_roundtrip fire frozen record k hn hfr hf hz hk]
  exact mintFire_roundtrip zf frozen fire hzf hzr hfr s [] n

/-- The local latch matches the flag/offset part of an armed integer step.
The already-computed arithmetic result and its zero-test witness are explicit
premises; the theorem does not manufacture that missing arithmetic bridge. -/
theorem freezeLatch_model (zf frozen fire : Wire) (record : List Wire)
    (hn : record.Nodup) (hzf : zf≠frozen) (hfr : fire≠frozen)
    (hf : fire∉record) (hz : frozen∉record) (tmin t : Nat) (ht : tmin≤t)
    (hk : t+1-tmin<2^record.length) (u : PinState) (s : State) (m : List Bool)
    (hactive : u.frozen=false) (hflag : s.basis frozen=false)
    (hrecord : regValue record s.basis=0) (hfire : s.basis fire=false)
    (hwitness : s.basis zf=decide ((ECDSAAdd.Divsteps.zStep u.rows).g=0)) :
    let v := run (freezeLatch zf frozen fire record (t+1-tmin)) m s
    v.basis frozen=(pinStep tmin t u).frozen ∧
      regValue record v.basis=(pinStep tmin t u).offset := by
  have hc := freezeLatch_run zf frozen fire record (t+1-tmin) hn hzf hfr hf hz hk s m hfire
  constructor
  · rw [hc.2.2.1,hflag,hwitness]
    by_cases hh : (ECDSAAdd.Divsteps.zStep u.rows).g=0 <;> simp [pinStep,hactive,ht,hh]
  · rw [hc.2.2.2.1,hrecord,hflag,hwitness]
    by_cases hh : (ECDSAAdd.Divsteps.zStep u.rows).g=0 <;> simp [pinStep,hactive,ht,hh]

theorem recordToggle_support (fire frozen : Wire) (record : List Wire) (k : Nat) :
    wires (recordToggle fire frozen record k)⊆(frozen::fire::record).toFinset := by
  rw [recordToggle,wires_append]
  apply Finset.union_subset
  · simp [wires,Instr.wires,Finset.insert_subset_iff]
  · exact (maskedConstant_wires_subset fire record k).trans (by simp)

theorem freezeLatch_support (zf frozen fire : Wire) (record : List Wire) (k : Nat) :
    wires (freezeLatch zf frozen fire record k)⊆(zf::frozen::fire::record).toFinset ∧
      wires (freezeUnlatch zf frozen fire record k)⊆(zf::frozen::fire::record).toFinset := by
  have hm : wires (mintFire zf frozen fire)⊆(zf::frozen::fire::record).toFinset := by
    simp [mintFire,wires,Instr.wires,Finset.insert_subset_iff]
  have hr := (recordToggle_support fire frozen record k).trans
    (show (frozen::fire::record).toFinset⊆(zf::frozen::fire::record).toFinset by simp)
  simp only [freezeLatch,freezeUnlatch,wires_append]
  exact ⟨Finset.union_subset hm hr,Finset.union_subset hr hm⟩

theorem freezeLatch_in_arena (zf frozen fire : Wire) (record : List Wire) (k : Nat)
    (h : (zf::frozen::fire::record).toFinset⊆arenaWires) :
    wires (freezeLatch zf frozen fire record k)⊆arenaWires ∧
      wires (freezeUnlatch zf frozen fire record k)⊆arenaWires :=
  ⟨(freezeLatch_support zf frozen fire record k).1.trans h,
    (freezeLatch_support zf frozen fire record k).2.trans h⟩

end ECDSAAdd.Arithmetic.Paper935
