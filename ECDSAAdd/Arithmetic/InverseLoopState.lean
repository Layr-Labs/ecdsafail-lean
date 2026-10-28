import ECDSAAdd.Arithmetic.InverseLoopLayout

namespace ECDSAAdd.Arithmetic

/-- 第二阶段不会修改的数据、分支记录和第一阶段状态位。 -/
def InverseRest (L : InverseLoopLayout) (z : KState) (cs : List (Bool×Bool)) (s : BasisState) : Prop :=
  RoundValues L.middle.data (roundDataValues z) s ∧ s L.middle.done=decide (z.v=0) ∧
    s L.middle.oddWork=false ∧ s L.middle.bothWork=false ∧ OneBitRecordsValues L.records cs s

def InverseExtra (L : InverseLoopLayout) (A : Nat) (s : BasisState) : Prop :=
  regValue L.a s=A ∧ regValue L.temp s=0 ∧ regValue L.arithmetic.wires s=0

def InversePhase (L : InverseLoopLayout) (K A : Nat) (s : BasisState) : Prop :=
  (regValue L.a s=A ∧ s L.middle.active=false ∧ regValue (L.temp++L.arithmetic.wires) s=0) ∧
    HalvingCounter L.halving.counter K s

def InverseMiddle (L : InverseLoopLayout) (z : KState) (cs : List (Bool×Bool)) (A : Nat) (s : BasisState) : Prop :=
  InverseRest L z cs s ∧ InversePhase L z.k A s

theorem InverseRest.congr (L : InverseLoopLayout) (z : KState) (cs : List (Bool×Bool))
    (s t : BasisState) (h : InverseRest L z cs s) (he : ∀ w∈L.restWires, t w=s w) :
    InverseRest L z cs t := by
  have hd (w : Wire) (hw : w∈L.middle.data.wires) : t w=s w := he w (by simp [InverseLoopLayout.restWires,hw])
  have hr (f : RoundField) : regValue (L.middle.data.reg f) t=regValue (L.middle.data.reg f) s :=
    regValue_congr _ _ _ (fun w hw => hd w (L.middle.data.reg_mem f hw))
  refine ⟨⟨fun f => (hr f).trans (h.1.1 f), ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (hd _ (by simp [RoundDataLayout.wires])).trans h.1.2
  · exact (he _ (by simp [InverseLoopLayout.restWires])).trans h.2.1
  · exact (he _ (by simp [InverseLoopLayout.restWires])).trans h.2.2.1
  · exact (he _ (by simp [InverseLoopLayout.restWires])).trans h.2.2.2.1
  · exact OneBitRecordsValues.congr L.records cs s t h.2.2.2.2
      (fun w hw => he w (by simp [InverseLoopLayout.restWires,hw]))

theorem InverseMiddle.iff (L : InverseLoopLayout) (z : KState) (cs : List (Bool×Bool))
    (A : Nat) (s : BasisState) :
    InverseMiddle L z cs A s ↔
      LoopState L.middle z s ∧ OneBitRecordsValues L.records cs s ∧ InverseExtra L A s := by
  constructor
  · rintro ⟨hr,hp⟩
    refine ⟨⟨hr.1,hp.2.1,hp.2.2.2.2.1,hp.2.2.1,hp.2.2.2.2.2,
      hp.1.2.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hp.2.2.2.1⟩,hr.2.2.2.2,?_⟩
    have hw := (regValue_zero _ _).mp hp.1.2.2
    exact ⟨hp.1.1,
      (regValue_zero _ _).mpr (fun w hh => hw w (List.mem_append_left _ hh)),
      (regValue_zero _ _).mpr (fun w hh => hw w (List.mem_append_right _ hh))⟩
  · rintro ⟨h,ht,he⟩
    refine ⟨⟨h.data,h.done,h.odd,h.both,ht⟩,
      ⟨he.1,h.active,?_⟩,h.k,h.y,h.cin,h.next,h.carry⟩
    apply (regValue_zero _ _).mpr
    intro w hw
    rcases List.mem_append.mp hw with hh|hh
    · exact (regValue_zero _ _).mp he.2.1 w hh
    · exact (regValue_zero _ _).mp he.2.2 w hh

end ECDSAAdd.Arithmetic
