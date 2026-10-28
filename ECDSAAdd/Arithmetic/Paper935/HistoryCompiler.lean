import ECDSAAdd.Arithmetic.Paper935.HistoryAllocation
import ECDSAAdd.Arithmetic.Paper935.StorePush
import ECDSAAdd.Arithmetic.Paper935.HistoryPredicate

namespace ECDSAAdd.Arithmetic.Paper935

/-- Physical views used by the store predicate and the finite history brigade.
The counter detector and coefficient detector reuse their scratch sequentially. -/
structure HistoryLayout where
  one : Wire
  zz : Wire
  pos : Wire
  sign : Wire
  output : Wire
  port : Wire
  zb : List ZeroBit
  frozen : ZeroBit
  positive : ZeroBit
  low : List ZeroBit
  record : List Wire

def HistoryLayout.Valid (H : HistoryLayout) : Prop :=
  (H.output::H.pos::H.one::H.zz::H.zb.flatMap ZeroBit.wires).Nodup ∧
  (H.one::H.output::(H.frozen::H.positive::H.low).flatMap ZeroBit.wires).Nodup ∧
  H.sign∈H.zb.map ZeroBit.input ∧ H.positive.input=H.pos ∧
  H.frozen.input≠H.pos ∧ (∀ b∈H.low,b.input≠H.pos) ∧
  (∀ b∈H.frozen::H.positive::H.low,b.work≠H.pos) ∧
  (H.output::H.port::H.record).Nodup ∧
  H.output∉[H.one,H.zz,H.pos,H.sign]++H.zb.flatMap ZeroBit.wires++
    (H.frozen::H.positive::H.low).flatMap ZeroBit.wires ∧
  List.Disjoint (H.port::H.record) ([H.one,H.zz,H.pos,H.sign]++
    H.zb.flatMap ZeroBit.wires++(H.frozen::H.positive::H.low).flatMap ZeroBit.wires)

private def zeroBitEq : DecidableEq ZeroBit := by
  intro ⟨a,b⟩ ⟨c,d⟩
  exact decidable_of_iff (a=c ∧ b=d) (by simp only [ZeroBit.mk.injEq])

attribute [local instance] zeroBitEq

instance historyValidDecidable (H : HistoryLayout) : Decidable H.Valid := by
  unfold HistoryLayout.Valid List.Disjoint
  infer_instance

def HistoryLayout.program (H : HistoryLayout) : RecordedProgram :=
  storePushForget H.one H.zz H.pos H.sign H.output H.port H.zb H.frozen H.positive H.low H.record

def historyCandidate (one zz pos sign output port frozen : Wire)
    (counter coeffBits record work : List Wire) : HistoryLayout :=
  { one:=one, zz:=zz, pos:=pos, sign:=sign, output:=output, port:=port,
    zb:=List.zipWith ZeroBit.mk counter work,
    frozen:=⟨frozen,work.getD 0 0⟩, positive:=⟨pos,work.getD 1 0⟩,
    low:=List.zipWith ZeroBit.mk coeffBits (work.drop 2), record:=record }

def compileHistory (one zz pos sign output port frozen : Wire)
    (counter coeffBits record work : List Wire) : Option HistoryLayout :=
  let H := historyCandidate one zz pos sign output port frozen counter coeffBits record work
  if H.Valid ∧ H.zb.map ZeroBit.input=counter ∧ H.low.map ZeroBit.input=coeffBits ∧ 2≤work.length
  then some H else none

theorem compileHistory_contract (one zz pos sign output port frozen : Wire)
    (counter coeffBits record work : List Wire) (H : HistoryLayout)
    (h : compileHistory one zz pos sign output port frozen counter coeffBits record work=some H) :
    H.Valid ∧ H.zb.map ZeroBit.input=counter ∧ H.low.map ZeroBit.input=coeffBits ∧
    2≤work.length ∧ H.record=record ∧ H.frozen.input=frozen := by
  unfold compileHistory at h
  dsimp only at h
  split at h
  next valid => cases h; exact ⟨valid.1,valid.2.1,valid.2.2.1,valid.2.2.2,rfl,rfl⟩
  next invalid => simp at h

/-- Grow the real record first, then borrow the detector pool. The compiled
brigade receives exactly the grown record, never a table-derived substitute. -/
def compileGrowingHistory (A : Arena) (record : List Wire) (capacity : Nat)
    (one zz pos sign output port frozen : Wire) (counter coeffBits : List Wire) :
    Option (Arena × Arena × List Wire × HistoryLayout) := do
  let (B,grown) ← planHistoryGrow A record capacity
  let (D,work) ← B.borrowMany (max counter.length (coeffBits.length+2))
  let H ← compileHistory one zz pos sign output port frozen counter coeffBits grown work
  pure (B,D,work,H)

theorem compileGrowingHistory_contract (A B D : Arena) (record work : List Wire) (capacity : Nat)
    (one zz pos sign output port frozen : Wire) (counter coeffBits : List Wire) (H : HistoryLayout)
    (h : compileGrowingHistory A record capacity one zz pos sign output port frozen counter coeffBits=
      some (B,D,work,H)) :
    planHistoryGrow A record capacity=some (B,H.record) ∧
    B.borrowMany (max counter.length (coeffBits.length+2))=some (D,work) ∧
    compileHistory one zz pos sign output port frozen counter coeffBits H.record work=some H := by
  unfold compileGrowingHistory at h
  obtain ⟨⟨B',grown⟩,hg,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨D',work'⟩,hb,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨H',hc,h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  have ids := compileHistory_contract one zz pos sign output port frozen counter coeffBits grown work H hc
  rw [ids.2.2.2.2.1]
  exact ⟨hg,hb,hc⟩

theorem compileGrowingHistory_capacity (A B D : Arena) (record work : List Wire) (capacity : Nat)
    (one zz pos sign output port frozen : Wire) (counter coeffBits : List Wire) (H : HistoryLayout)
    (h : compileGrowingHistory A record capacity one zz pos sign output port frozen counter coeffBits=
      some (B,D,work,H))
    (hn : record.Nodup) (ho : record.toFinset⊆A.live) (s : BasisState) (ready : A.Ready s) :
    H.record.length=max capacity record.length ∧
    H.low.length=coeffBits.length ∧ B.Ready s ∧ regValue H.record s=regValue record s := by
  have hc := compileGrowingHistory_contract A B D record work capacity one zz pos sign output port frozen counter coeffBits H h
  have grow := planHistoryGrow_correct A B record H.record capacity hc.1 hn ho s ready
  have views := compileHistory_contract one zz pos sign output port frozen counter coeffBits H.record work H hc.2.2
  have len := congrArg List.length views.2.2.1
  simp only [List.length_map] at len
  exact ⟨grow.1,len,grow.2.2.2.1,grow.2.2.2.2.1⟩

end ECDSAAdd.Arithmetic.Paper935
