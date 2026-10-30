import ECDSAAdd.Submission.Entrant.FrontierEntry1591Endpoints
import ECDSAAdd.Submission.Entrant.FrontierEntry1591Replay

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry1591
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires

private theorem control_not_block (start len : Nat) (bound : start+len≤2400) :
    base 2400∉wireBlock base start len := by
  intro used
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp used
  have same := base_injective eq
  simp only [List.mem_range'_1] at hi
  omega

private theorem encoder_control_free : base 2400∉wires (NewHistory5.allEncode base 102) := by
  intro used
  have mem := List.mem_toFinset.mp (NewHistory5.allEncode_history_support base 102 (by decide) used)
  simp only [List.mem_append] at mem
  rcases mem with mem|mem
  all_goals
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp mem
    have same := base_injective eq
    simp only [List.mem_range'_1] at hi
    omega

private theorem pair_control_set (r y : List Wire) (hr : base 2400∉r) (hy : base 2400∉y)
    (origin bits : BasisState) (A B : Nat) (value : Bool) (frame : PairFrame r y origin A B bits) :
    PairFrame r y (writeBit origin (base 2400) value) A B (writeBit bits (base 2400) value) := by
  have same (qs : List Wire) (off : base 2400∉qs) :
      regValue qs (writeBit bits (base 2400) value)=regValue qs bits := by
    apply regValue_congr
    intro q hq
    have ne : q≠base 2400 := fun eq => off (eq ▸ hq)
    simp only [writeBit,Function.update_of_ne ne]
  refine ⟨(same r hr).trans frame.1,(same y hy).trans frame.2.1,?_⟩
  intro q qr qy
  by_cases eq : q=base 2400
  · subst q
    simp only [writeBit,Function.update_self]
  · simpa only [writeBit,Function.update_of_ne eq] using frame.2.2 q qr qy

theorem run_control_set (P : Program) (off : base 2400∉wires P)
    (s : State) (m : List Bool) (value : Bool) :
    run P m ⟨s.phase,writeBit s.basis (base 2400) value⟩=
      ⟨(run P m s).phase,writeBit (run P m s).basis (base 2400) value⟩ := by
  let t : State := ⟨s.phase,writeBit s.basis (base 2400) value⟩
  have agrees := pool_run_agrees P (wires P) (Finset.Subset.refl _) m t s rfl (by
    intro q hq
    have ne : q≠base 2400 := fun eq => off (eq ▸ hq)
    simp only [t,writeBit,Function.update_of_ne ne])
  apply State.extensionality
  · exact agrees.1
  · funext q
    change (run P m t).basis q=writeBit (run P m s).basis (base 2400) value q
    by_cases eq : q=base 2400
    · subst q
      simpa only [t,writeBit,Function.update_self] using run_preserves_outside P m t _ off
    · have update : writeBit (run P m s).basis (base 2400) value q=(run P m s).basis q := by
        simp only [writeBit,Function.update_of_ne eq]
      rw [update]
      by_cases used : q∈wires P
      · exact agrees.2 q used
      · exact (run_preserves_outside P m t q used).trans
          ((show t.basis q=s.basis q from by simp only [t,writeBit,Function.update_of_ne eq]).trans
            (run_preserves_outside P m s q used).symm)

theorem run_control_unset (P : Program) (off : base 2400∉wires P)
    (s : State) (m : List Bool) (value : Bool) :
    run P m s=⟨(run P m ⟨s.phase,writeBit s.basis (base 2400) value⟩).phase,
      writeBit (run P m ⟨s.phase,writeBit s.basis (base 2400) value⟩).basis
        (base 2400) (s.basis (base 2400))⟩ := by
  rw [run_control_set P off s m value]
  apply State.extensionality
  · rfl
  · funext q
    by_cases eq : q=base 2400
    · subst q
      simpa only [writeBit,Function.update_self] using run_preserves_outside P m s _ off
    · simp only [writeBit,Function.update_of_ne eq]

private theorem pull_control_set (s : State) (value : Bool) :
    pullState (OB5.sig 511) ⟨s.phase,writeBit s.basis (base 2400) value⟩=
      ⟨(pullState (OB5.sig 511) s).phase,
        writeBit (pullState (OB5.sig 511) s).basis (base 2400) value⟩ := by
  apply State.extensionality
  · rfl
  · funext q
    by_cases eq : q=base 2400
    · subst q
      change writeBit s.basis (base 2400) value (OB5.sig 511 (base 2400))=
        writeBit (pullState (OB5.sig 511) s).basis (base 2400) value (base 2400)
      rw [OneFlagSW.selSig_2400]
      simp only [writeBit,Function.update_self]
    · have ne : OB5.sig 511 q≠base 2400 := fun h => eq
        (OB5.sig_injective 511 (by decide) (h.trans OneFlagSW.selSig_2400.symm))
      simp only [pullState,writeBit,Function.update_of_ne eq,Function.update_of_ne ne]

theorem frame_control_set (origin : BasisState) (X Y : Fp) (s : State) (value : Bool)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin X Y s) :
    NewFieldFrameOB5.EncodedFieldFrame (writeBit origin (base 2400) value) X Y
      ⟨s.phase,writeBit s.basis (base 2400) value⟩ := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  refine ⟨⟨raw.phase,writeBit raw.basis (base 2400) value⟩,phase,?_,?_⟩
  · apply pair_control_set _ _ _ _ origin raw.basis _ _ value frame
    · rw [balancedSharedPorts_r]
      exact control_not_block 2056 256 (by decide)
    · rw [balancedSharedPorts_y]
      exact control_not_block 770 256 (by decide)
  · rw [pull_control_set,encoded,run_control_set _ encoder_control_free]

theorem canonical_control_set (origin : BasisState) (X Y : Fp) (s : State) (value : Bool)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X Y s) :
    NewFieldFrameOB5.EncodedCanonicalFrame (writeBit origin (base 2400) value) X Y
      ⟨s.phase,writeBit s.basis (base 2400) value⟩ := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  refine ⟨⟨raw.phase,writeBit raw.basis (base 2400) value⟩,phase,?_,?_⟩
  · apply pair_control_set _ _ _ _ origin raw.basis _ _ value frame
    · rw [skywalkShared_field_z]
      exact control_not_block 2056 257 (by decide)
    · exact control_not_block 770 257 (by decide)
  · rw [pull_control_set,encoded,run_control_set _ encoder_control_free]

theorem context_control_set (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (value : Bool) : FrontierReplay1591.Context (writeBit origin (base 2400) value) := by
  refine ⟨ctx.hn,ctx.ho,ctx.hp,ctx.hf,?_,?_,?_,?_,?_⟩
  · simpa only [writeBit,Function.update_of_ne (show base 2409≠base 2400 from by decide)] using ctx.hg0
  · simpa only [writeBit,Function.update_of_ne (show base 2410≠base 2400 from by decide)] using ctx.hs0
  · exact env_write base (base 2400) (ctx.ho _ (by simp)) origin value ctx.env
  · intro j hj
    have same (q : Fin 10) :
        (writeBit origin (base 2400) value) (History5.historyMap base (5*j) q)=
          origin (History5.historyMap base (5*j) q) := by
      have bound := History5.historyId_bound (5*j) (by omega) q
      have ne : History5.historyMap base (5*j) q≠base 2400 := by
        intro eq
        have eq := base_injective eq
        omega
      simp only [writeBit,Function.update_of_ne ne]
    apply (MeasuredCodec5.legalAt_iff _ _).mpr
    intro i
    rw [same,same]
    exact (MeasuredCodec5.legalAt_iff _ _).mp (ctx.legal j hj) i
  · simpa only [writeBit,Function.update_of_ne (show base 2312≠base 2400 from by decide)] using ctx.parity

theorem source_zero_control_set (origin : BasisState) (value : Bool)
    (ha : regValue (skywalkSharedField base).a origin=0) :
    regValue (skywalkSharedField base).a (writeBit origin (base 2400) value)=0 := by
  apply Eq.trans (regValue_congr _ _ _ ?_) ha
  intro q hq
  have ne : q≠base 2400 := fun eq => control_not_block 770 257 (by decide) (eq ▸ hq)
  simp only [writeBit,Function.update_of_ne ne]

theorem trace_control_set (origin : BasisState) (value : Bool) :
    skywalkTapeControls (writeBit origin (base 2400) value) (skywalkSharedTape base)=
      skywalkTapeControls origin (skywalkSharedTape base) := by
  simp only [skywalkTapeControls,skywalkSharedTape,List.map_map]
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  have first : base i≠base 2400 := by intro eq; have same := base_injective eq; omega
  have second : base (1028+i)≠base 2400 := by intro eq; have same := base_injective eq; omega
  simp only [Function.comp_apply,writeBit,Function.update_of_ne first,Function.update_of_ne second]

theorem parity_host_control_set (controls : List Wire) (host : Wire)
    (away : host≠base 2400) (off : base 2400∉controls) (s : State) (value : Bool)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis)) :
    (writeBit s.basis (base 2400) value) host=
      TraceParity5.parity (controls.map (writeBit s.basis (base 2400) value)) := by
  have same : controls.map (writeBit s.basis (base 2400) value)=controls.map s.basis := by
    apply List.map_congr_left
    intro q hq
    have ne : q≠base 2400 := fun eq => off (eq ▸ hq)
    simp only [writeBit,Function.update_of_ne ne]
  rw [same]
  simpa only [writeBit,Function.update_of_ne away] using parity

end ECDSAAdd.Entrant.FrontierEntry1591
