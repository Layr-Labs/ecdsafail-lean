import ECDSAAdd.Arithmetic.Paper935.Sign24Inverse
import ECDSAAdd.Arithmetic.CuccaroSignedSquareInverse

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- engine.py:3174–3199. Move the 24-wire pool above the entire 256-bit
payload, retaining control/sign 0 and low window 1..58. -/
def signWindowMap (q : Wire) : Wire := if q<59 then q else q+198

theorem signWindowMap_injective : Function.Injective signWindowMap := by
  intro a b h
  dsimp [signWindowMap] at h
  dsimp only [Wire] at *
  split_ifs at h <;> omega

def signPayload : List Wire := List.range' 1 256
def signWindow (subtract : Bool) : Program :=
  renameProgram signWindowMap (sign24Program subtract)
def SignReady (s : BasisState) : Prop := ∀ i<24,s (257+i)=false

/-- engine.py:3174: sign-controlled complement on all payload bits followed
by the actual truncated constant subtraction. Inverse adds the constant before undoing CXs. -/
def signCore (inverse : Bool) : Program :=
  if inverse then signWindow false ++ signComplement 0 signPayload
  else signComplement 0 signPayload ++ signWindow true

attribute [local irreducible] sign24Program signPayload

theorem signWindow_roundtrip (s : State) (m n : List Bool)
    (ready : SignReady s.basis) :
    run (signWindow false) n (run (signWindow true) m s)=s := by
  have clean : Sign24Ready 0 (pullState signWindowMap s).basis := by
    intro i hi _
    simpa [pullState,signWindowMap,show ¬59+i<59 by omega,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using ready i hi
  have pulled : pullState signWindowMap
      (run (signWindow false) n (run (signWindow true) m s))=
      pullState signWindowMap s := by
    rw [signWindow,run_rename _ signWindowMap_injective,
      signWindow,run_rename _ signWindowMap_injective]
    exact sign24Program_roundtrip_reverse _ m n clean
  apply State.extensionality
  · simpa only [pullState] using congrArg State.phase pulled
  · funext q
    by_cases low : q<59
    · have h := congrArg (fun t : State => t.basis q) pulled
      simpa [pullState,signWindowMap,low] using h
    by_cases high : 257≤q
    · have h := congrArg (fun t : State => t.basis (q-198)) pulled
      have lower : ¬q-198<59 := by dsimp only [Wire] at *; omega
      have eq : q-198+198=q := by dsimp only [Wire] at *; omega
      simpa [pullState,signWindowMap,lower,eq] using h
    · have away (b : Bool) : q∉wires (signWindow b) := by
        rw [signWindow,renameProgram_support]
        intro mem
        obtain ⟨j,_,eq⟩ := Finset.mem_image.mp mem
        dsimp [signWindowMap] at eq
        dsimp only [Wire] at *
        split_ifs at eq <;> omega
      exact (run_preserves_outside _ n _ q (away false)).trans
        (run_preserves_outside _ m s q (away true))

theorem signFan_roundtrip (s : State) (m n : List Bool) :
    run (signComplement 0 signPayload) n (run (signComplement 0 signPayload) m s) = s := by
  let t := run (signComplement 0 signPayload) m s
  have nodup : signPayload.Nodup := by unfold signPayload; exact List.nodup_range'
  have away : (0 : Wire) ∉ signPayload := by simp [signPayload]
  have a := signComplement_correct 0 signPayload nodup away s m
  have b := signComplement_correct 0 signPayload nodup away t n
  have ctrl : t.basis 0 = s.basis 0 := a.2.1 _ away
  have bound := regValue_lt signPayload s.basis
  have word : regValue signPayload (run (signComplement 0 signPayload) n t).basis =
      regValue signPayload s.basis := by
    rw [b.2.2, ctrl]
    have av := a.2.2
    change regValue signPayload t.basis = _ at av
    rw [av]
    cases s.basis 0 <;> simp only [Bool.false_eq_true, if_false, if_true]
    omega
  apply State.extensionality
  · exact b.1.trans a.1
  · funext q
    by_cases hq : q ∈ signPayload
    · exact (regValue_eq_iff signPayload _ _).mp word q hq
    · exact (b.2.1 q hq).trans (a.2.1 q hq)

theorem signCore_roundtrip (s : State) (m n : List Bool)
    (ready : SignReady s.basis) :
    run (signCore true) n (run (signCore false) m s)=s := by
  have complement := signComplement_correct 0 signPayload
    (by unfold signPayload; exact List.nodup_range') (by simp [signPayload]) s m
  have clean : SignReady (run (signComplement 0 signPayload) m s).basis := by
    intro i hi
    rw [complement.2.1 (257+i) (by simp [signPayload])]
    exact ready i hi
  simp only [signCore,Bool.false_eq_true,if_false,if_true,run_append,run_take]
  simp only [(signComplement_counts 0 signPayload).2,List.drop_zero]
  rw [signWindow_roundtrip _ m n clean]
  exact signFan_roundtrip s m _

theorem signWindow_support (b : Bool) : wires (signWindow b) ⊆ Finset.range 281 := by
  rw [signWindow,renameProgram_support]
  intro q hq
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
  have bound := sign24Program_support b hj
  simp only [Finset.mem_range] at bound ⊢
  dsimp [signWindowMap]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem signCore_support (inverse : Bool) :
    wires (signCore inverse) ⊆ Finset.range 281 := by
  have comp : wires (signComplement 0 signPayload) ⊆ Finset.range 281 := by
    apply Finset.Subset.trans (signComplement_wires_subset _ _)
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,signPayload,List.mem_range'] at hq
    simp only [Finset.mem_range]
    dsimp only [Wire] at *
    rcases hq with rfl|⟨i,hi,rfl⟩ <;> omega
  cases inverse <;> simp only [signCore,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff]
  · exact ⟨comp,signWindow_support true⟩
  · exact ⟨signWindow_support false,comp⟩

end ECDSAAdd.Arithmetic.Paper935
