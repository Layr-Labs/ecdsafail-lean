import ECDSAAdd.Submission.Entrant.ParityCodec5NewBase

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ParityCodec5New
open Arithmetic Challenge RecordedQuantum Baselines

def encodeFirst : Program := twist ++ FirstNonzeroCodec.encodeFirst
def decodeFirst : Program := FirstNonzeroCodec.decodeFirst ++ untwist
def encodeAtFirst (f : Fin 10→Wire) : Program := renameProgram (label f) encodeFirst
def decodeAtFirst (f : Fin 10→Wire) : Program := renameProgram (label f) decodeFirst

theorem first_counts : toffoliCount encodeFirst=8 ∧ toffoliCount decodeFirst=9 ∧
    measurementCount encodeFirst=4 ∧ measurementCount decodeFirst=2 := by
  simp only [encodeFirst,decodeFirst,toffoliCount_append,measurementCount_append]
  simpa [twist,untwist,toffoliCount,measurementCount] using FirstNonzeroCodec.counts

theorem first_slots : gateSlots encodeFirst=146 ∧ gateSlots decodeFirst=144 := by decide +kernel

theorem first_support_exact : wires encodeFirst=Finset.range 10 ∧
    wires decodeFirst=Finset.range 10 := by decide +kernel

theorem first_support : wires encodeFirst⊆Finset.range 10 ∧
    wires decodeFirst⊆Finset.range 10 := by
  rw [first_support_exact.1,first_support_exact.2]
  exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩

theorem first_physical : GatePhysical encodeFirst ∧ GatePhysical decodeFirst := by
  have ht : GatePhysical twist := by simp [GatePhysical,twist,PhysicalInstr,ProperGate]
  have hu : GatePhysical untwist := by simp [GatePhysical,untwist,PhysicalInstr,ProperGate]
  exact ⟨(gatePhysical_append _ _).mpr ⟨ht,FirstNonzeroCodec.physical.1⟩,
    (gatePhysical_append _ _).mpr ⟨FirstNonzeroCodec.physical.2,hu⟩⟩

theorem twist_first (s : State) (m : List Bool) :
    (run twist m s).basis 0=s.basis 0 ∧ (run twist m s).basis 1=s.basis 1 := by
  rw [twist_basis]
  simp [writeBit]

theorem encode_eq (s : State) (m : List Bool) (h : MeasuredCodec5.legal s.basis)
    (hn : s.basis 0=true ∨ s.basis 1=true) : run encodeFirst m s=run encode m s := by
  have nz : (run twist [] s).basis 0=true ∨ (run twist [] s).basis 1=true := by
    simpa only [(twist_first s []).1,(twist_first s []).2] using hn
  simp only [encodeFirst,encode,run_append,show measurementCount twist=0 from rfl,
    List.take_zero,List.drop_zero]
  exact FirstNonzeroCodec.encode_eq _ m (twist_legal s [] h) nz

theorem decode_eq (s : State) (mE mD : List Bool) (h : MeasuredCodec5.legal s.basis)
    (hn : s.basis 0=true ∨ s.basis 1=true) :
    run decodeFirst mD (run encode mE s)=run decode mD (run encode mE s) := by
  have nz : (run twist [] s).basis 0=true ∨ (run twist [] s).basis 1=true := by
    simpa only [(twist_first s []).1,(twist_first s []).2] using hn
  simp only [encode,decodeFirst,decode,run_append,show measurementCount twist=0 from rfl,
    List.take_zero,List.drop_zero,FirstNonzeroCodec.counts.2.2.2,MeasuredCodec5.counts.2.2.2]
  rw [FirstNonzeroCodec.decode_eq _ _ _ (twist_legal s [] h) nz]

theorem roundtripFirst (s : State) (mE mD : List Bool) (h : MeasuredCodec5.legal s.basis)
    (hn : s.basis 0=true ∨ s.basis 1=true) : run decodeFirst mD (run encodeFirst mE s)=s := by
  rw [encode_eq s mE h hn,decode_eq s mE mD h hn,roundtrip s mE mD h]

theorem first_independent (s : State) (m n : List Bool) (h : MeasuredCodec5.legal s.basis)
    (hn : s.basis 0=true ∨ s.basis 1=true) : run encodeFirst m s=run encodeFirst n s := by
  rw [encode_eq s m h hn,encode_eq s n h hn,encode_independent s m n h]

theorem first_countsAt (f : Fin 10→Wire) :
    toffoliCount (encodeAtFirst f)=8 ∧ toffoliCount (decodeAtFirst f)=9 ∧
    measurementCount (encodeAtFirst f)=4 ∧ measurementCount (decodeAtFirst f)=2 := by
  simpa only [encodeAtFirst,decodeAtFirst,(renameProgram_counts (label f) encodeFirst).1,
    (renameProgram_counts (label f) encodeFirst).2,(renameProgram_counts (label f) decodeFirst).1,
    (renameProgram_counts (label f) decodeFirst).2] using first_counts

theorem first_slotsAt (f : Fin 10→Wire) :
    gateSlots (encodeAtFirst f)=146 ∧ gateSlots (decodeAtFirst f)=144 := by
  simpa only [encodeAtFirst,decodeAtFirst,rename_gateSlots] using first_slots

theorem first_mapped_support (f : Fin 10→Wire) :
    wires (encodeAtFirst f)=wires (encodeAt f) ∧ wires (decodeAtFirst f)=wires (decodeAt f) := by
  simp only [encodeAtFirst,decodeAtFirst,encodeAt,decodeAt,renameProgram_support,
    first_support_exact.1,first_support_exact.2,support_exact.1,support_exact.2]
  exact ⟨trivial,trivial⟩

theorem first_mapped_physical (f : Fin 10→Wire) (hf : Function.Injective f) :
    GatePhysical (encodeAtFirst f) ∧ GatePhysical (decodeAtFirst f) := by
  exact ⟨gatePhysical_rename_support _ _
    (fun a ha b hb e => FirstNonzeroCodec.label_inj' f hf a (first_support.1 ha) b (first_support.1 hb) e)
      first_physical.1,
    gatePhysical_rename_support _ _
    (fun a ha b hb e => FirstNonzeroCodec.label_inj' f hf a (first_support.2 ha) b (first_support.2 hb) e)
      first_physical.2⟩

theorem encodeAt_eq (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (hl : legalAt f s.basis)
    (hn : s.basis (f 0)=true ∨ s.basis (f 1)=true) :
    run (encodeAtFirst f) m s=run (encodeAt f) m s := by
  apply FirstNonzeroCodec.renamed_eq f hf _ _ first_support.1 support.1 s m
  apply encode_eq (⟨s.phase,fun q => s.basis (label f q)⟩ : State) m hl
  simpa only [label,MeasuredCodec5.label,dif_pos (show 0<10 by decide),
    dif_pos (show 1<10 by decide)] using hn

theorem decodeAt_eq (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (mE mD : List Bool) (hl : legalAt f s.basis)
    (hn : s.basis (f 0)=true ∨ s.basis (f 1)=true) :
    run (decodeAtFirst f) mD (run (encodeAt f) mE s)=
      run (decodeAt f) mD (run (encodeAt f) mE s) := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have hn' : t.basis 0=true ∨ t.basis 1=true := by
    simpa only [t,label,MeasuredCodec5.label,dif_pos (show 0<10 by decide),
      dif_pos (show 1<10 by decide)] using hn
  have pe := run_rename_pool (label f) (Finset.range 10) (FirstNonzeroCodec.label_inj' f hf)
    encode support.1 mE t s rfl (fun _ _ => rfl)
  have pn := run_rename_pool (label f) (Finset.range 10) (FirstNonzeroCodec.label_inj' f hf)
    decodeFirst first_support.2 mD (run encode mE t) (run (encodeAt f) mE s) pe.1.symm
    (fun q hq => (pe.2 q hq).symm)
  have po := run_rename_pool (label f) (Finset.range 10) (FirstNonzeroCodec.label_inj' f hf)
    decode support.2 mD (run encode mE t) (run (encodeAt f) mE s) pe.1.symm
    (fun q hq => (pe.2 q hq).symm)
  have de := decode_eq t mE mD hl hn'
  apply State.extensionality
  · exact pn.1.trans ((congrArg State.phase de).trans po.1.symm)
  · funext z
    by_cases hz : z∈(Finset.range 10).image (label f)
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      exact (pn.2 q hq).trans ((congrArg (fun st : State => st.basis q) de).trans (po.2 q hq).symm)
    · have noP : z∉wires (decodeAtFirst f) := by
        rw [decodeAtFirst,renameProgram_support]
        intro hh
        obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp hh
        exact hz (Finset.mem_image.mpr ⟨q,first_support.2 hq,eq⟩)
      have noQ : z∉wires (decodeAt f) := by
        rw [decodeAt,renameProgram_support]
        intro hh
        obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp hh
        exact hz (Finset.mem_image.mpr ⟨q,support.2 hq,eq⟩)
      exact (run_preserves_outside _ mD _ z noP).trans (run_preserves_outside _ mD _ z noQ).symm

theorem roundtripAtFirst (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (mE mD : List Bool) (hl : legalAt f s.basis)
    (hn : s.basis (f 0)=true ∨ s.basis (f 1)=true) :
    run (decodeAtFirst f) mD (run (encodeAtFirst f) mE s)=s := by
  rw [encodeAt_eq f hf s mE hl hn,decodeAt_eq f hf s mE mD hl hn,roundtripAt f hf s mE mD hl]

theorem encodeAtFirst_correct (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (hl : legalAt f s.basis)
    (hn : s.basis (f 0)=true ∨ s.basis (f 1)=true) :
    (run (encodeAtFirst f) m s).phase=s.phase ∧
    (run (encodeAtFirst f) m s).basis (f 5)=false ∧
    (run (encodeAtFirst f) m s).basis (f 9)=false := by
  rw [encodeAt_eq f hf s m hl hn]
  exact encodeAt_correct f hf s m hl

theorem encodeAtFirst_independent (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m n : List Bool) (hl : legalAt f s.basis)
    (hn : s.basis (f 0)=true ∨ s.basis (f 1)=true) :
    run (encodeAtFirst f) m s=run (encodeAtFirst f) n s := by
  rw [encodeAt_eq f hf s m hl hn,encodeAt_eq f hf s n hl hn,encodeAt_independent f hf s m n hl]

theorem decodeAt_eq_on_pool (f : Fin 10→Wire) (hf : Function.Injective f)
    (raw s : State) (mE mD : List Bool) (hl : legalAt f raw.basis)
    (hn : raw.basis (f 0)=true ∨ raw.basis (f 1)=true)
    (hb : ∀q∈(Finset.range 10).image (label f),
      s.basis q=(run (encodeAt f) mE raw).basis q) :
    run (decodeAtFirst f) mD s=run (decodeAt f) mD s := by
  apply FirstNonzeroCodec.run_eq_local_transfer _ _ ((Finset.range 10).image (label f)) _ _ s
    (run (encodeAt f) mE raw) mD hb (decodeAt_eq f hf raw mE mD hl hn)
  · rw [decodeAtFirst,renameProgram_support]
    intro q hh
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_image_of_mem _ (first_support.2 hi)
  · rw [decodeAt,renameProgram_support]
    intro q hh
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_image_of_mem _ (support.2 hi)

end ECDSAAdd.Entrant.ParityCodec5New
