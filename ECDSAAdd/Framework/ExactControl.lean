import ECDSAAdd.Framework.UnitaryControl

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd

/-- An exact controlled replacement with one shared, restored scratch bit.
The contract is equality of the complete state, including phase. -/
structure ExactControl (c scratch : Wire) (original replacement : Program) : Prop where
  proper : ProperProgram original
  controlAway : c∉wires original
  scratchAway : scratch∉wires original
  measurement : measurementCount replacement=0
  support : wires replacement⊆{c,scratch}∪wires original
  execute : ∀ (s : State) (m : List Bool), s.basis scratch=false →
    run replacement m s=if s.basis c then run original m s else s

theorem ExactControl.direct (c scratch : Wire) (p : Program)
    (hp : ProperProgram p) (hc : c∉wires p) (hs : scratch∉wires p)
    (hcs : c≠scratch) : ExactControl c scratch p (controlUnitary c scratch p) :=
  ⟨hp,hc,hs,controlUnitary_measurementCount _ _ _,
    controlUnitary_wires_subset _ _ _,controlUnitary_run c scratch p hp hc hs hcs⟩

theorem ExactControl.nil (c scratch : Wire) : ExactControl c scratch [] [] := by
  refine ⟨by simp [ProperProgram],by simp [wires],by simp [wires],rfl,
    by simp [wires],?_⟩
  intro s m hz
  cases s.basis c <;> rfl

theorem ExactControl.append {c scratch : Wire} {p q p' q' : Program}
    (hp : ExactControl c scratch p p') (hq : ExactControl c scratch q q') :
    ExactControl c scratch (p++q) (p'++q') := by
  refine ⟨(properProgram_append p q).mpr ⟨hp.proper,hq.proper⟩,
    ?_,?_,?_,?_,?_⟩
  · simpa only [wires_append,Finset.mem_union,not_or] using
      And.intro hp.controlAway hq.controlAway
  · simpa only [wires_append,Finset.mem_union,not_or] using
      And.intro hp.scratchAway hq.scratchAway
  · simp only [measurementCount_append,hp.measurement,hq.measurement]
  · intro w hw
    simp only [wires_append,Finset.mem_union] at hw ⊢
    rcases hw with hw|hw
    · have h := hp.support hw
      simp only [Finset.mem_union] at h
      tauto
    · have h := hq.support hw
      simp only [Finset.mem_union] at h
      tauto
  · intro s m hz
    let u := if s.basis c then run p m s else s
    have uc : u.basis c=s.basis c := by
      cases hc : s.basis c
      · simp [u,hc]
      · simp only [u,hc,if_true]
        exact (run_preserves_outside p m s c hp.controlAway).trans hc
    have uz : u.basis scratch=false := by
      cases hc : s.basis c
      · simpa [u,hc] using hz
      · simp only [u,hc,if_true]
        exact (run_preserves_outside p m s scratch hp.scratchAway).trans hz
    rw [run_append,run_take,hp.measurement,List.drop_zero,hp.execute s m hz]
    change run q' m u=_
    rw [hq.execute u m uz,uc]
    have pm := properProgram_measurementCount p hp.proper
    cases hc : s.basis c
    · simp [hc,u]
    · simp only [hc,if_true,u]
      rw [run_append,run_take,pm,List.drop_zero]

/-- Leave reversible preparation and cleanup uncontrolled.  Only the middle
update needs control; the disabled branch is the exact preparation roundtrip. -/
theorem ExactControl.sandwich {c scratch : Wire} {p q q' : Program}
    (hp : ProperProgram p) (hc : c∉wires p) (hs : scratch∉wires p)
    (hq : ExactControl c scratch q q') :
    ExactControl c scratch (p++q++p.reverse) (p++q'++p.reverse) := by
  have pr := properProgram_reverse p hp
  have pm := properProgram_measurementCount p hp
  have prm : measurementCount p.reverse=0 := by rw [measurementCount_reverse,pm]
  refine ⟨(properProgram_append _ _).mpr
    ⟨(properProgram_append _ _).mpr ⟨hp,hq.proper⟩,pr⟩,?_,?_,?_,?_,?_⟩
  · simpa only [wires_append,wires_reverse,Finset.mem_union,not_or] using
      And.intro (And.intro hc hq.controlAway) hc
  · simpa only [wires_append,wires_reverse,Finset.mem_union,not_or] using
      And.intro (And.intro hs hq.scratchAway) hs
  · simp [measurementCount_append,pm,prm,hq.measurement]
  · intro w hw
    simp only [wires_append,wires_reverse,Finset.mem_union] at hw ⊢
    rcases hw with (hw|hw)|hw
    · tauto
    · have h := hq.support hw
      simp only [Finset.mem_union] at h
      tauto
    · tauto
  · intro s m hz
    let u := run p m s
    have uc : u.basis c=s.basis c := run_preserves_outside p m s c hc
    have uz : u.basis scratch=false := (run_preserves_outside p m s scratch hs).trans hz
    have qm := properProgram_measurementCount q hq.proper
    have pEmpty (st : State) : run p [] st=run p m st := by
      have h := run_take p m st
      simpa only [pm,List.take_zero] using h
    have qEmpty (st : State) : run q [] st=run q m st := by
      have h := run_take q m st
      simpa only [qm,List.take_zero] using h
    have q'Empty (st : State) : run q' [] st=run q' m st := by
      have h := run_take q' m st
      simpa only [hq.measurement,List.take_zero] using h
    simp only [List.append_assoc,run_append,pm,hq.measurement,qm,
      List.drop_zero,List.take_zero,pEmpty,qEmpty,q'Empty]
    change run p.reverse m (run q' m u)=_
    rw [hq.execute u m uz,uc]
    cases h : s.basis c
    · exact run_reverse_proper p hp s m m
    · rfl

end ECDSAAdd
