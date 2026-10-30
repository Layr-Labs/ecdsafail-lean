import ECDSAAdd.Submission.Entrant.ParityHost5
import ECDSAAdd.Submission.Entrant.ParityHostTransport5
import ECDSAAdd.Framework.MeasuredLocality

set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace ECDSAAdd.Entrant.ParityField1591
open ParityHost5 TraceParity5 Challenge Arithmetic RecordedQuantum
attribute [local irreducible] run wires

def clear (host : Wire) (s : State) : State :=
  ⟨s.phase,writeBit s.basis host false⟩

theorem run_clear (P : Program) (host : Wire) (s : State) (m : List Bool)
    (free : host∉wires P) : run P m (clear host s)=clear host (run P m s) := by
  have sameOnSupport := run_measured_locality P (wires P) (fun _ h => h)
    (clear host s) s m rfl (by
      intro q hq
      have ne : q≠host := fun e => free (e ▸ hq)
      simp only [clear,writeBit,Function.update_of_ne ne])
  apply State.extensionality
  · exact sameOnSupport.1
  · funext q
    by_cases same : q=host
    · subst q
      rw [run_preserves_outside P m (clear host s) host free]
      simp only [clear,writeBit,Function.update_self]
    · simp only [clear,writeBit,Function.update_of_ne same]
      by_cases used : q∈wires P
      · exact sameOnSupport.2 q used
      · change (run P m (clear host s)).basis q=(run P m s).basis q
        rw [run_preserves_outside P m (clear host s) q used,
          run_preserves_outside P m s q used]
        simp only [clear,writeBit,Function.update_of_ne same]

def program (controls : List Wire) (work host : Wire) (P : Program) : Program :=
  setup controls host ++ ParityHostTransport5.program work host P ++ setup controls host

/-- The original host value can be nonzero. The setup clears that value and
the final setup restores it after the complete field segment. -/
theorem run_eq (controls : List Wire) (work host : Wire) (P : Program)
    (s : State) (m : List Bool) (distinct : work≠host)
    (outside : host∉controls) (free : host∉wires P)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis))
    (workIn : s.basis work=false) (workOut : (run P m s).basis work=false)
    (payload : ∀q∈controls,(run P m s).basis q=s.basis q) :
    run (program controls work host P) m s=run P m s := by
  let out := run P m s
  have hostOut : out.basis host=s.basis host := run_preserves_outside P m s host free
  have initial := setup_zero controls host s [] outside parity
  have base := run_clear P host s m free
  have field := ParityHostTransport5.run_eq work host P (clear host s) m
    (by simp only [clear,writeBit,Function.update_of_ne distinct,workIn])
    (by simp only [clear,writeBit,Function.update_self])
    (by rw [base];simp only [clear,writeBit,Function.update_of_ne distinct,workOut]) free
  rw [base] at field
  have restored := restore_run controls host s (clear host out)
    (m.drop (measurementCount P)) outside parity
    (by
      intro q hq
      have ne : q≠host := fun e => outside (e ▸ hq)
      simpa only [clear,writeBit,Function.update_of_ne ne] using payload q hq)
    (by simp only [clear,writeBit,Function.update_self])
  have finish : run (setup controls host) (m.drop (measurementCount P))
      (clear host out)=out := by
    rw [restored]
    apply State.extensionality
    · rfl
    · funext q
      by_cases same : q=host
      · subst q;simpa only [writeBit,Function.update_self] using hostOut.symm
      · simp only [clear,writeBit,Function.update_of_ne same]
  have zeroM := (setup_counts controls host).2.1
  have bodyM := (ParityHostTransport5.counts work host P).2
  unfold program
  rw [run_append,measurementCount_append,zeroM,bodyM,Nat.zero_add,
    run_append,zeroM,List.take_zero,List.drop_zero,initial]
  change run (setup controls host) (m.drop (measurementCount P))
    (run (ParityHostTransport5.program work host P) (m.take (measurementCount P))
      (clear host s))=out
  rw [←bodyM,run_take,field]
  simpa only [bodyM] using finish

theorem counts (controls : List Wire) (work host : Wire) (P : Program) :
    toffoliCount (program controls work host P)=toffoliCount P ∧
      measurementCount (program controls work host P)=measurementCount P ∧
      gateSlots (program controls work host P)=gateSlots P+2*controls.length := by
  have setup := setup_counts controls host
  have body := ParityHostTransport5.counts work host P
  have slots := ParityHostTransport5.slots work host P
  simp only [program,toffoliCount_append,measurementCount_append,gateSlots_append,
    setup.1,setup.2.1,setup.2.2,body.1,body.2,slots,Nat.zero_add,Nat.add_zero]
  exact ⟨trivial,trivial,by omega⟩

theorem physical (controls : List Wire) (work host : Wire) (P : Program)
    (outside : host∉controls) (valid : GatePhysical P) :
    GatePhysical (program controls work host P) := by
  have setup : GatePhysical (setup controls host) := by
    intro i hi
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
    have ne : q≠host := fun e => outside (e ▸ hq)
    simpa only [PhysicalInstr,ProperGate] using ne
  exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr
    ⟨setup,ParityHostTransport5.physical work host P valid⟩,setup⟩

theorem avoids_work (controls : List Wire) (work host : Wire) (P : Program)
    (distinct : work≠host) (outside : work∉controls) (free : host∉wires P) :
    work∉wires (program controls work host P) := by
  have setup : work∉wires (setup controls host) := by
    intro used
    have mem := setup_support controls host used
    simp only [Finset.mem_insert,List.mem_toFinset] at mem
    exact mem.elim distinct outside
  have body := ParityHostTransport5.avoids_work work host P free
  simpa only [program,wires_append,Finset.mem_union,not_or] using ⟨⟨setup,body⟩,setup⟩

theorem support (controls : List Wire) (work host : Wire) (P : Program) :
    wires (program controls work host P)⊆
      insert host controls.toFinset ∪ (wires P).image (Equiv.swap work host) := by
  have setup := setup_support controls host
  rw [program,wires_append,wires_append,ParityHostTransport5.support]
  intro q hq
  rcases Finset.mem_union.mp hq with h|h
  · rcases Finset.mem_union.mp h with h|h
    · exact Finset.mem_union_left _ (setup h)
    · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ (setup h)

end ECDSAAdd.Entrant.ParityField1591
