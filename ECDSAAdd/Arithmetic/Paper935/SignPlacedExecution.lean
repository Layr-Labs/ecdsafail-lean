import ECDSAAdd.Arithmetic.Paper935.SignCoreValue
import ECDSAAdd.Arithmetic.Paper935.FusedPlacedExecution

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] signCore

def placedSignCore (f : Wire → Wire) (inverse : Bool) : Program :=
  renameProgram f (signCore inverse)

def placedSignFix (f : Wire → Wire) (sv : Wire) (inverse : Bool) : Program :=
  [.CX sv (f 0)] ++ placedSignCore f inverse ++ [.CX sv (f 0)]

theorem placedSignCore_cleanup (f : Wire → Wire)
    (inj : Set.InjOn f (Finset.range 281)) (inverse : Bool) (s : State) (m : List Bool)
    (clean : ∀ i<24,s.basis (f (257+i))=false) :
    let out := run (placedSignCore f inverse) m s
    (∀i<24,out.basis (f (257+i))=false) ∧
      out.basis (f 0)=s.basis (f 0) ∧ out.phase=s.phase := by
  have sem := run_rename_pool f (Finset.range 281) inj (signCore inverse)
    (signCore_support inverse) m (pullState f s) s rfl (fun _ _ => rfl)
  have tidy := signCore_cleanup inverse (pullState f s) m clean
  refine ⟨?_,?_,sem.1.trans tidy.2.2⟩
  · intro i hi
    dsimp only [Wire] at i hi
    exact (sem.2 _ (by simp only [Finset.mem_range]; dsimp only [Wire]; omega)).trans (tidy.1 i hi)
  · exact (sem.2 0 (by simp)).trans tidy.2.1

theorem placedSignCore_outside (f : Wire → Wire) (inverse : Bool)
    (s : State) (m : List Bool) (q : Wire) (outside : q∉(Finset.range 281).image f) :
    (run (placedSignCore f inverse) m s).basis q=s.basis q :=
  run_rename_pool_outside f _ _ (signCore_support inverse) m s q outside

theorem placedSignCore_roundtrip (f : Wire → Wire)
    (inj : Set.InjOn f (Finset.range 281)) (s : State) (m n : List Bool)
    (clean : ∀i<24,s.basis (f (257+i))=false) :
    run (placedSignCore f true) n (run (placedSignCore f false) m s)=s := by
  have first := run_rename_pool f (Finset.range 281) inj (signCore false)
    (signCore_support false) m (pullState f s) s rfl (fun _ _ => rfl)
  have second := run_rename_pool f (Finset.range 281) inj (signCore true)
    (signCore_support true) n (run (signCore false) m (pullState f s))
    (run (placedSignCore f false) m s) first.1.symm (fun q hq => (first.2 q hq).symm)
  have back := signCore_roundtrip (pullState f s) m n clean
  rw [back] at second
  apply State.extensionality
  · exact second.1
  · funext q
    by_cases inside : q∈(Finset.range 281).image f
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp inside
      exact second.2 j hj
    · exact (placedSignCore_outside f true _ n q inside).trans
        (placedSignCore_outside f false s m q inside)

private theorem cx_twice (a b : Wire) (ne : a≠b) (s : State) (m n : List Bool) :
    run [.CX a b] n (run [.CX a b] m s)=s := by
  apply State.extensionality
  · rfl
  · funext q
    by_cases h : q=b
    · subst q
      simp [run,writeBit,ne]
    · simp [run,writeBit,h]

theorem placedSignFix_roundtrip (f : Wire → Wire) (sv : Wire)
    (inj : Set.InjOn f (Finset.range 281)) (distinct : sv≠f 0)
    (s : State) (m n : List Bool) (clean : ∀i<24,s.basis (f (257+i))=false) :
    run (placedSignFix f sv true) n (run (placedSignFix f sv false) m s)=s := by
  have poolne (i : Nat) (hi : i<24) : f (257+i)≠f 0 := by
    intro eq
    have bad := inj (x₁:=257+i) (x₂:=0) (Finset.mem_range.mpr (by dsimp only [Wire]; omega))
      (Finset.mem_range.mpr (by decide)) eq
    dsimp only [Wire] at bad
    omega
  have ready : ∀i<24,(run [.CX sv (f 0)] m s).basis (f (257+i))=false := by
    intro i hi
    simpa [run,writeBit,poolne i hi] using clean i hi
  simp only [placedSignFix,run_append,run_take,measurementCount,List.drop_zero]
  rw [cx_twice sv (f 0) distinct]
  rw [placedSignCore_roundtrip f inj _ _ _ (by simpa only [run] using ready)]
  exact cx_twice sv (f 0) distinct s m _

/-- The external row-sign control is retained; the pool and f-sign are
restored, independently of the arithmetic SignGood condition. -/
theorem placedSignFix_cleanup (f : Wire → Wire) (sv : Wire)
    (inj : Set.InjOn f (Finset.range 281))
    (outside : sv∉(Finset.range 281).image f) (inverse : Bool)
    (s : State) (m : List Bool) (clean : ∀i<24,s.basis (f (257+i))=false) :
    let out := run (placedSignFix f sv inverse) m s
    (∀i<24,out.basis (f (257+i))=false) ∧
      out.basis (f 0)=s.basis (f 0) ∧ out.phase=s.phase := by
  have distinct : sv≠f 0 := by
    intro eq
    exact outside (Finset.mem_image.mpr ⟨0,by simp,eq.symm⟩)
  have poolne (i : Nat) (hi : i<24) : f (257+i)≠f 0 := by
    intro eq
    have bad := inj (x₁:=257+i) (x₂:=0)
      (Finset.mem_range.mpr (by dsimp only [Wire]; omega)) (Finset.mem_range.mpr (by decide)) eq
    dsimp only [Wire] at bad
    omega
  let t := run [.CX sv (f 0)] m s
  have ready : ∀i<24,t.basis (f (257+i))=false := by
    intro i hi
    simpa [t,run,writeBit,poolne i hi] using clean i hi
  have tidy := placedSignCore_cleanup f inj inverse t m ready
  have svframe := placedSignCore_outside f inverse t m sv outside
  simp only [placedSignFix,run_append,run_take,measurementCount,List.drop_zero]
  change (∀i<24,(run [.CX sv (f 0)] _ (run (placedSignCore f inverse) m t)).basis (f (257+i))=false) ∧ _
  refine ⟨?_,?_,?_⟩
  · intro i hi
    simpa [run,writeBit,poolne i hi] using tidy.1 i hi
  · simp only [run,writeBit,Function.update_self]
    change ((run (placedSignCore f inverse) m t).basis (f 0) ^^
      (run (placedSignCore f inverse) m t).basis sv) = s.basis (f 0)
    rw [tidy.2.1,svframe]
    simp [t,run,writeBit,distinct]
  · exact tidy.2.2

end ECDSAAdd.Arithmetic.Paper935
