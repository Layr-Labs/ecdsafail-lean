import ECDSAAdd.Arithmetic.Paper935.HmrSignSourceBinding

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] s2SourceSign s6SourceSign s6SourceUnsign s6SourceCorrection
  s2SignMap s6SignMap placedSignFix

private theorem run_basis_congr (p : Program) (m : List Bool) (s t : State)
    (h : s.basis=t.basis) : (run p m s).basis=(run p m t).basis := by
  induction p generalizing m s t with
  | nil => exact h
  | cons i p ih =>
    cases i <;> simp only [run] <;> apply ih <;> simp_all [measureAndCorrect]

theorem s2SourceSign_cleanup (s : State) (tape : List Bool) (cursor : Nat)
    (clean : ∀i<24,s.basis (s2SignMap (257+i))=false) :
    let out := runWithTape s2SourceSign tape cursor s
    (∀i<24,out.basis (s2SignMap (257+i))=false) ∧
      out.basis (s2SignMap 0)=s.basis (s2SignMap 0) ∧ out.phase=s.phase := by
  rw [s2SourceSign_run]
  exact placedSignFix_cleanup _ _ s2SignMap_injective s2SignMap_rowSign_outside false s _ clean

theorem s6SourceSign_cleanup (s : State) (tape : List Bool) (cursor : Nat)
    (clean : ∀i<24,s.basis (s6SignMap (257+i))=false) :
    let out := runWithTape s6SourceSign tape cursor s
    (∀i<24,out.basis (s6SignMap (257+i))=false) ∧
      out.basis (s6SignMap 0)=s.basis (s6SignMap 0) ∧ out.phase=s.phase := by
  rw [s6SourceSign_run]
  exact placedSignFix_cleanup _ _ s6SignMap_injective s6SignMap_rowSign_outside false s _ clean

/-- Actual source sign, deferred record-Z, inverse sign restore every basis
bit for every tape and absolute cursor. The record-Z phase is not erased. -/
theorem s6SourceGap_basis (s : State) (tape : List Bool) (cursor : Nat)
    (clean : ∀i<24,s.basis (s6SignMap (257+i))=false) :
    (runWithTape s6SourceGap tape cursor s).basis=s.basis := by
  simp only [s6SourceGap,runWithTape_append]
  rw [s6SourceUnsign_run]
  have same := funext (s6SourceCorrection_basis tape
    (cursor+recordedMeasurementCount s6SourceSign)
    (runWithTape s6SourceSign tape cursor s))
  rw [run_basis_congr _ _ _ _ same,s6SourceSign_run]
  have back := placedSignFix_roundtrip s6SignMap s6HmrSourceRow.sign
    s6SignMap_injective (by decide +kernel) s (tape.drop cursor)
      (tape.drop (cursor + recordedMeasurementCount (s6SourceSign ++ s6SourceCorrection))) clean
  exact congrArg State.basis back

/-- The actual K2 suffix demolishes only y, so the restored scratch remains zero. -/
theorem s2SourceGap_pool (s : State) (tape : List Bool) (cursor : Nat)
    (clean : ∀i<24,s.basis (s2SignMap (257+i))=false) :
    ∀i<24,(runWithTape s2SourceGap tape cursor s).basis (s2SignMap (257+i))=false := by
  intro i hi
  have outside : ∀j<24,s2SignMap (257+j)∉s2SourceDemolished := by decide +kernel
  simp only [s2SourceGap,runWithTape_append,hmrDemolish_basis]
  simp only [outside i hi,if_false]
  exact (s2SourceSign_cleanup s tape cursor clean).1 i hi

/-- Caller-facing cleanup on the exact source ancillary list. -/
theorem s2SourceGap_anc (s : State) (tape : List Bool) (cursor : Nat)
    (clean : ∀q∈s2HmrSeamPorts.anc,s.basis q=false) :
    ∀q∈s2HmrSeamPorts.anc,(runWithTape s2SourceGap tape cursor s).basis q=false := by
  rw [←s2SignMap_pool] at clean ⊢
  simp only [List.mem_map,List.mem_range,forall_exists_index,and_imp,
    forall_apply_eq_imp_iff₂] at clean ⊢
  exact s2SourceGap_pool s tape cursor clean

/-- Exact source anc list, with no phase-restoration conclusion. -/
theorem s6SourceGap_basis_of_anc (s : State) (tape : List Bool) (cursor : Nat)
    (clean : ∀q∈s6HmrSeamPorts.anc,s.basis q=false) :
    (runWithTape s6SourceGap tape cursor s).basis=s.basis := by
  rw [←s6SignMap_pool] at clean
  simp only [List.mem_map,List.mem_range,forall_exists_index,and_imp,
    forall_apply_eq_imp_iff₂] at clean
  exact s6SourceGap_basis s tape cursor clean

end ECDSAAdd.Arithmetic.Paper935
