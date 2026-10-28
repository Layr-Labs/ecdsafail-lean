import ECDSAAdd.Framework.RecordedWireRename
import ECDSAAdd.Framework.WireRenameComposition
import ECDSAAdd.Framework.OutputFrame

namespace ECDSAAdd

/-- Extend a finite self-placement by the identity outside its arena. Arbitrary
values of f outside S are deliberately irrelevant to physical placement. -/
def extendWireMap (S : Finset Wire) (f : Wire → Wire) (q : Wire) : Wire :=
  if q∈S then f q else q

theorem extendWireMap_on (S : Finset Wire) (f : Wire → Wire) (q : Wire) (hq : q∈S) :
    extendWireMap S f q=f q := if_pos hq

theorem extendWireMap_bijective (S : Finset Wire) (f : Wire → Wire)
    (inj : Set.InjOn f S) (image : S.image f=S) : Function.Bijective (extendWireMap S f) := by
  have inside (q : Wire) (hq : q∈S) : f q∈S := by
    rw [←image]
    exact Finset.mem_image_of_mem f hq
  constructor
  · intro a b he
    by_cases ha : a∈S <;> by_cases hb : b∈S
    · simp only [extendWireMap,if_pos ha,if_pos hb] at he
      exact inj ha hb he
    · simp only [extendWireMap,if_pos ha,if_neg hb] at he
      exact False.elim (hb (he ▸ inside a ha))
    · simp only [extendWireMap,if_neg ha,if_pos hb] at he
      exact False.elim (ha (he.symm ▸ inside b hb))
    · simpa only [extendWireMap,if_neg ha,if_neg hb] using he
  · intro q
    by_cases hq : q∈S
    · have hi : q∈S.image f := image.symm ▸ hq
      obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hi
      exact ⟨a,(extendWireMap_on S f a ha).trans he⟩
    · exact ⟨q,if_neg hq⟩

noncomputable def finiteWirePermutation (S : Finset Wire) (f : Wire → Wire)
    (inj : Set.InjOn f S) (image : S.image f=S) : Equiv.Perm Wire :=
  Equiv.ofBijective (extendWireMap S f) (extendWireMap_bijective S f inj image)

theorem finiteWirePermutation_on (S : Finset Wire) (f : Wire → Wire)
    (inj : Set.InjOn f S) (image : S.image f=S) (q : Wire) (hq : q∈S) :
    finiteWirePermutation S f inj image q=f q := extendWireMap_on S f q hq

theorem finiteWirePermutation_preserves (S : Finset Wire) (f : Wire → Wire)
    (inj : Set.InjOn f S) (image : S.image f=S) (q : Wire) :
    finiteWirePermutation S f inj image q∈S ↔ q∈S := by
  change extendWireMap S f q∈S ↔ q∈S
  by_cases hq : q∈S
  · rw [extendWireMap_on S f q hq]
    exact iff_of_true (image ▸ Finset.mem_image_of_mem f hq) hq
  · simp [extendWireMap,hq]

theorem renameRecorded_congr_support (f g : Wire → Wire) (p : RecordedProgram)
    (h : ∀q∈recordedWires p,f q=g q) : renameRecordedProgram f p=renameRecordedProgram g p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    have tail := ih (fun q hq => h q (Finset.mem_union_right _ hq))
    have head : renameRecordedInstr f i=renameRecordedInstr g i := by
      cases i with
      | gate i =>
        exact congrArg RecordedInstr.gate
          (renameInstr_congr f g i (fun q hq => h q (Finset.mem_union_left _ hq)))
      | phaseFromRecord j cs =>
        exact congrArg (RecordedInstr.phaseFromRecord j)
          (renameCorrections_congr f g cs (fun q hq => h q (Finset.mem_union_left _ hq)))
    simpa only [renameRecordedProgram,List.map_cons] using congrArg₂ List.cons head tail

theorem finiteWirePermutation_program (S : Finset Wire) (f : Wire → Wire)
    (inj : Set.InjOn f S) (image : S.image f=S) (p : RecordedProgram) (support : recordedWires p⊆S) :
    renameRecordedProgram (finiteWirePermutation S f inj image) p=renameRecordedProgram f p :=
  renameRecorded_congr_support _ _ p (fun q hq => finiteWirePermutation_on S f inj image q (support hq))

/-- Pullback by a permutation is faithful on the entire phase-and-basis state. -/
theorem pullState_equiv_injective (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
  intro s t h
  apply State.extensionality
  · simpa only [pullState] using congrArg State.phase h
  · funext q
    have hh := congrArg (fun u : State => u.basis (e.symm q)) h
    simpa only [pullState,Equiv.apply_symm_apply] using hh

theorem pullState_withOutput_image (e : Equiv.Perm Wire) (O : Finset Wire)
    (v : BasisState) (s : State) :
    pullState e (withOutput (O.image e) v s)=withOutput O (fun q => v (e q)) (pullState e s) := by
  apply State.extensionality
  · rfl
  · funext q
    simp [pullState,withOutput,Finset.mem_image,e.injective.eq_iff]

end ECDSAAdd
