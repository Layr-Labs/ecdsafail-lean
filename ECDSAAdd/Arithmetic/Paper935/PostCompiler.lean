import ECDSAAdd.Arithmetic.Paper935.ProbeCompilerReady
import ECDSAAdd.Arithmetic.Paper935.WindowPostLayout

namespace ECDSAAdd.Arithmetic.Paper935

def postStaticCheck (P : WindowPostLayout) : Prop :=
  (BlockedZero.Valid P.one P.zf P.blocks) ∧
  (P.recordWires.Nodup) ∧
  (P.zf≠P.frozen) ∧
  (P.fire≠P.frozen) ∧
  (P.fire∉P.recordWires) ∧
  (P.frozen∉P.recordWires) ∧
  (P.armed=true → P.offset<2^P.recordWires.length) ∧
  (P.active≠P.fire) ∧
  (P.active≠P.frozen) ∧
  (P.active∉P.recordWires) ∧
  (P.active≠P.zf) ∧
  (P.zf≠P.fire) ∧
  (P.zf∉P.recordWires) ∧
  (∀ w∈P.one::BlockedZero.ports P.blocks, w≠P.active ∧ w≠P.fire ∧ w≠P.frozen ∧ w∉P.recordWires) ∧
  ((P.one::P.witness::P.record.flatMap ZeroBit.wires).Nodup) ∧
  (P.witness≠P.fire) ∧
  (P.frozen≠P.witness) ∧
  (P.fire∉P.record.map ZeroBit.work) ∧
  (∀ w∈P.witness::P.record.map ZeroBit.work, w≠P.active ∧ w≠P.fire ∧ w≠P.frozen ∧ w∉P.recordWires) ∧
  ((P.frozen::P.fire::P.record.flatMap ZeroBit.wires).Nodup)

theorem postStaticCheck_iff (P : WindowPostLayout) : postStaticCheck P ↔ P.Valid := by
  constructor
  · rintro ⟨probe,record,zfFrozen,fireFrozen,fireRecord,frozenRecord,offsetFits,activeFire,activeFrozen,activeRecord,activeZf,zfFire,zfRecord,stable,compare,witnessFire,frozenWitness,fireWork,workFrame,remint⟩
    exact ⟨probe,record,zfFrozen,fireFrozen,fireRecord,frozenRecord,offsetFits,activeFire,activeFrozen,activeRecord,activeZf,zfFire,zfRecord,stable,compare,witnessFire,frozenWitness,fireWork,workFrame,remint⟩
  · intro h
    exact ⟨h.probe,h.record,h.zfFrozen,h.fireFrozen,h.fireRecord,h.frozenRecord,h.offsetFits,h.activeFire,h.activeFrozen,h.activeRecord,h.activeZf,h.zfFire,h.zfRecord,h.stable,h.compare,h.witnessFire,h.frozenWitness,h.fireWork,h.workFrame,h.remint⟩

instance postValidDecidable (P : WindowPostLayout) : Decidable P.Valid :=
  have : Decidable (postStaticCheck P) := by unfold postStaticCheck; infer_instance
  decidable_of_iff (postStaticCheck P) (postStaticCheck_iff P)

def postPoolSize (inputs record : List Wire) (width : Nat) : Nat :=
  max (width+(inputs.toChunks width).length) (record.length+1)

/-- Probe and offset-comparison work share the pool sequentially. All
record bits and probe inputs are checked against their physical registers. -/
def postCandidate (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) : WindowPostLayout :=
  let (xs,scratch) := probeCandidate inputs work width
  { armed := armed, one := one, zf := zf, frozen := frozen, fire := fire,
    active := active, witness := work.getD 0 0,
    blocks := BlockedZero.chunks xs scratch,
    record := List.zipWith ZeroBit.mk record (work.drop 1), offset := offset }

def compilePost (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) : Option WindowPostLayout :=
  let P := postCandidate armed one zf frozen fire active inputs record work width offset
  if P.Valid ∧ BlockedZero.inputs P.blocks=inputs ∧ P.recordWires=record ∧ work≠[] then some P else none

theorem compilePost_contract (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (h : compilePost armed one zf frozen fire active inputs record work width offset=some P) :
    P.Valid ∧ BlockedZero.inputs P.blocks=inputs ∧ P.recordWires=record ∧ work≠[] := by
  unfold compilePost at h
  dsimp only at h
  split at h
  next valid => cases h; exact valid
  next invalid => simp at h

def compileBorrowedPost (A : Arena) (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record : List Wire) (width offset : Nat) : Option (Arena × List Wire × WindowPostLayout) := do
  let (D,work) ← A.borrowMany (postPoolSize inputs record width)
  let P ← compilePost armed one zf frozen fire active inputs record work width offset
  pure (D,work,P)

theorem compileBorrowedPost_contract (A D : Arena) (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (h : compileBorrowedPost A armed one zf frozen fire active inputs record width offset=some (D,work,P)) :
    A.borrowMany (postPoolSize inputs record width)=some (D,work) ∧
    compilePost armed one zf frozen fire active inputs record work width offset=some P := by
  unfold compileBorrowedPost at h
  cases hb : A.borrowMany (postPoolSize inputs record width) with
  | none => simp [hb] at h
  | some result =>
    rcases result with ⟨B,ws⟩
    simp only [hb] at h
    dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd] at h
    cases hc : compilePost armed one zf frozen fire active inputs record ws width offset with
    | none => simp [hc] at h
    | some Q =>
      simp only [hc] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      exact ⟨rfl,hc⟩

/-- The actual armed post-stage can share eleven work wires between a
26-bit probe and six-bit freeze-offset comparison. -/
theorem compilePost_shared_example :
    (compilePost true 0 1 2 3 4 (List.range' 5 26)
      (List.range' 31 6) (List.range' 37 11) 6 1).isSome=true := by decide

end ECDSAAdd.Arithmetic.Paper935
