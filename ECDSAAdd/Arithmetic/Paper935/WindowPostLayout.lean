import ECDSAAdd.Arithmetic.Paper935.BlockedPostInverse
import ECDSAAdd.Arithmetic.Paper935.WindowRetired

namespace ECDSAAdd.Arithmetic.Paper935

/-- Public physical layout for the existing blocked freeze post-stage. -/
structure WindowPostLayout where
  armed : Bool
  one : Wire
  zf : Wire
  frozen : Wire
  fire : Wire
  active : Wire
  witness : Wire
  blocks : List BlockedZero.Block
  record : List ZeroBit
  offset : Nat

def WindowPostLayout.program (P : WindowPostLayout) : Program :=
  BlockedPost.publicPost P.armed P.one P.zf P.frozen P.fire P.active P.witness P.blocks P.record P.offset

def WindowPostLayout.inverse (P : WindowPostLayout) : Program :=
  BlockedPost.publicPostInverse P.armed P.one P.zf P.frozen P.fire P.active P.blocks P.record P.offset

def WindowPostLayout.recordWires (P : WindowPostLayout) : List Wire := P.record.map ZeroBit.input

def WindowPostLayout.scratch (P : WindowPostLayout) : List Wire :=
  P.zf::P.fire::P.witness::(P.blocks.map BlockedZero.Block.flag++
    P.blocks.flatMap (fun b => b.bits.map ZeroBit.work)++P.record.map ZeroBit.work)

structure WindowPostLayout.Valid (P : WindowPostLayout) : Prop where
  probe : BlockedZero.Valid P.one P.zf P.blocks
  record : P.recordWires.Nodup
  zfFrozen : P.zf≠P.frozen
  fireFrozen : P.fire≠P.frozen
  fireRecord : P.fire∉P.recordWires
  frozenRecord : P.frozen∉P.recordWires
  offsetFits : P.armed=true → P.offset<2^P.recordWires.length
  activeFire : P.active≠P.fire
  activeFrozen : P.active≠P.frozen
  activeRecord : P.active∉P.recordWires
  activeZf : P.active≠P.zf
  zfFire : P.zf≠P.fire
  zfRecord : P.zf∉P.recordWires
  stable : ∀ w∈P.one::BlockedZero.ports P.blocks,
    w≠P.active ∧ w≠P.fire ∧ w≠P.frozen ∧ w∉P.recordWires
  compare : (P.one::P.witness::P.record.flatMap ZeroBit.wires).Nodup
  witnessFire : P.witness≠P.fire
  frozenWitness : P.frozen≠P.witness
  fireWork : P.fire∉P.record.map ZeroBit.work
  workFrame : ∀ w∈P.witness::P.record.map ZeroBit.work,
    w≠P.active ∧ w≠P.fire ∧ w≠P.frozen ∧ w∉P.recordWires
  remint : (P.frozen::P.fire::P.record.flatMap ZeroBit.wires).Nodup

structure WindowPostLayout.Ready (P : WindowPostLayout) (s : BasisState) : Prop where
  one : s P.one=true
  clean : ∀ w∈P.scratch,s w=false
  activity : s P.active= !s P.frozen
  oldOffset : P.armed=true → regValue P.recordWires s<P.offset
  activeOffset : s P.frozen=false → regValue P.recordWires s=0

theorem WindowPostLayout.block_clean (P : WindowPostLayout) (s : BasisState)
    (h : ∀ w∈P.scratch,s w=false) : BlockedZero.clean P.blocks s := by
  intro b hb
  constructor
  · exact h b.flag (by simp [scratch,List.mem_map_of_mem hb])
  · intro x hx
    apply h x.work
    simp only [scratch,List.mem_cons,List.mem_append]
    right; right; right; left; right
    exact List.mem_flatMap.mpr ⟨b,hb,List.mem_map.mpr ⟨x,hx,rfl⟩⟩

theorem WindowPostLayout.run_spec (P : WindowPostLayout) (hv : P.Valid)
    (s : State) (m : List Bool) (h : P.Ready s.basis) :
    let t := run P.program m s
    t.phase=s.phase ∧ t.basis P.active=false ∧ t.basis P.zf=false ∧ t.basis P.fire=false ∧
    t.basis P.frozen=(s.basis P.frozen || (P.armed && decide (regValue (BlockedZero.inputs P.blocks) s.basis=0))) ∧
    regValue P.recordWires t.basis=regValue P.recordWires s.basis ^^^
      (if P.armed && decide (regValue (BlockedZero.inputs P.blocks) s.basis=0) && !s.basis P.frozen then P.offset else 0) ∧
    ∀ w,w≠P.active → w≠P.frozen → w∉P.recordWires → t.basis w=s.basis w := by
  exact BlockedPost.publicPost_spec P.armed P.one P.zf P.frozen P.fire P.active P.witness
    P.blocks P.record P.offset hv.probe hv.record hv.zfFrozen hv.fireFrozen hv.fireRecord hv.frozenRecord
    hv.offsetFits hv.activeFire hv.activeFrozen hv.activeRecord hv.activeZf hv.zfFire hv.zfRecord hv.stable
    s m h.one (h.clean _ (by simp [scratch])) (P.block_clean s.basis h.clean)
    (h.clean _ (by simp [scratch])) h.activity h.oldOffset h.activeOffset hv.compare hv.witnessFire
    hv.frozenWitness hv.fireWork hv.workFrame (h.clean _ (by simp [scratch]))
    (fun b hb => h.clean _ (by simp [scratch,List.mem_map_of_mem hb]))

theorem WindowPostLayout.roundtrip (P : WindowPostLayout) (hv : P.Valid)
    (s : State) (m n : List Bool) (h : P.Ready s.basis) :
    run P.inverse n (run P.program m s)=s := by
  exact BlockedPost.publicPost_roundtrip P.armed P.one P.zf P.frozen P.fire P.active P.witness
    P.blocks P.record P.offset hv.probe hv.record hv.zfFrozen hv.fireFrozen hv.fireRecord hv.frozenRecord
    hv.offsetFits hv.activeFire hv.activeFrozen hv.activeRecord hv.activeZf hv.zfFire hv.zfRecord hv.stable
    s m n h.one (h.clean _ (by simp [scratch])) (P.block_clean s.basis h.clean)
    (h.clean _ (by simp [scratch])) h.activity h.oldOffset h.activeOffset hv.compare hv.witnessFire
    hv.frozenWitness hv.fireWork hv.workFrame (h.clean _ (by simp [scratch]))
    (fun b hb => h.clean _ (by simp [scratch,List.mem_map_of_mem hb])) hv.remint

/-- The arena supplies all post-stage scratch clean after row shrinkage and
counter cleanup. No condition is imposed on the quantum input row bits. -/
theorem WindowPostLayout.ready_of_free (P : WindowPostLayout) (A : Arena) (s : BasisState)
    (ha : A.Ready s) (hs : P.scratch.toFinset⊆arenaWires\A.live)
    (hone : s P.one=true) (hactive : s P.active= !s P.frozen)
    (hoffset : P.armed=true → regValue P.recordWires s<P.offset)
    (hzero : s P.frozen=false → regValue P.recordWires s=0) : P.Ready s := by
  refine ⟨hone,?_,hactive,hoffset,hzero⟩
  intro q hq
  have hh := Finset.mem_sdiff.mp (hs (List.mem_toFinset.mpr hq))
  exact ha q hh.1 hh.2

theorem WindowPostLayout.arena_ready_after (P : WindowPostLayout) (hv : P.Valid)
    (A : Arena) (s : State) (m : List Bool) (h : P.Ready s.basis) (ha : A.Ready s.basis)
    (hown : (P.frozen::P.recordWires).toFinset⊆A.live) :
    A.Ready (run P.program m s).basis := by
  have step := P.run_spec hv s m h
  intro q hq hn
  by_cases eq : q=P.active
  · subst q; exact step.2.1
  · rw [step.2.2.2.2.2.2 q eq
      (fun he => hn (he ▸ hown (by simp)))
      (fun hm => hn (hown (by simp [hm])))]
    exact ha q hq hn

end ECDSAAdd.Arithmetic.Paper935
