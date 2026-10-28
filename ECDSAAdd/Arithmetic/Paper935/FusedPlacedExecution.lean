import ECDSAAdd.Arithmetic.Paper935.FusedMagnitudeValue
import ECDSAAdd.Arithmetic.Paper935.FusedRowFoldValue
import ECDSAAdd.Arithmetic.Paper935.FusedRowFoldSource
import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Arithmetic.Paper935.FusedBoundaryLayout
import Mathlib.Data.List.GetD

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] fusedMagnitudeLift fusedRowFoldSource

/-- The default is unreachable on a component's finite reference ports. -/
def fusedPlacementMap (ports : List Wire) (q : Wire) : Wire := ports.getD q 0

theorem fusedPlacementMap_injective (ports : List Wire) (n : Nat)
    (len : ports.length=n) (inj : Function.Injective ports.get) :
    Set.InjOn (fusedPlacementMap ports) (Finset.range n) := by
  intro a ha b hb eq
  have ha' : a<ports.length := len ▸ Finset.mem_range.mp ha
  have hb' : b<ports.length := len ▸ Finset.mem_range.mp hb
  have eq' : ports.get ⟨a,ha'⟩=ports.get ⟨b,hb'⟩ := by
    simpa only [fusedPlacementMap,List.getD_eq_getElem ports 0 ha',
      List.getD_eq_getElem ports 0 hb',List.get_eq_getElem] using eq
  exact congrArg Fin.val (inj eq')

/-- Allocator-derived injectivity for the actual sign/row/pool lift order. -/
theorem fusedLiftPlacementMap_injective (A B : Arena) (row pool : List Wire) (sign : Wire)
    (len : row.length=280) (distinct : (sign::row).Nodup)
    (owned : (sign::row).toFinset⊆A.live)
    (allocated : A.borrowMany 24=some (B,pool)) :
    Set.InjOn (fusedPlacementMap (sign::row++pool)) (Finset.range 305) := by
  apply fusedPlacementMap_injective
  · have plen := (A.borrowMany_contract B 24 pool allocated).1
    simp [len,plen]
  · exact fusedLiftPlacement_injective A B row pool sign distinct owned allocated

theorem fusedFoldPlacementMap_injective (A B : Arena) (row word pool : List Wire)
    (hr : row.length=280) (hw : word.length=256)
    (distinct : (row++word).Nodup) (owned : (row++word).toFinset⊆A.live)
    (allocated : A.borrowMany 24=some (B,pool)) :
    Set.InjOn (fusedPlacementMap (fusedFoldPlacement row word pool)) (Finset.range 537) := by
  apply fusedPlacementMap_injective
  · exact fusedFoldPlacement_length row word pool hr hw
      (A.borrowMany_contract B 24 pool allocated).1
  · exact fusedFoldPlacement_injective A B row word pool distinct owned allocated

/-- Only the component's finite reference ports must be injectively placed. -/
def placedMagnitude (f : Wire → Wire) (inverse : Bool) : Program :=
  renameProgram f (fusedMagnitudeLift inverse)

def placedRowFold (f : Wire → Wire) (inverse : Bool) : Program :=
  renameProgram f (fusedRowFoldSource inverse)

private theorem value_map (f : Wire → Wire) (xs : List Wire) (s : BasisState) :
    regValue (xs.map f) s = regValue xs (fun q => s (f q)) := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    change (if s (f q) then 1 else 0)+2*regValue (qs.map f) s =
      (if s (f q) then 1 else 0)+2*regValue qs (fun q => s (f q))
    rw [ih]

private theorem placed_value (f : Wire → Wire) (n : Nat)
    (inj : Set.InjOn f (Finset.range n)) (p : Program)
    (support : wires p⊆Finset.range n) (xs : List Wire)
    (ports : ∀ q∈xs,q<n) (s : State) (m : List Bool) :
    regValue (xs.map f) (run (renameProgram f p) m s).basis =
      regValue xs (run p m (pullState f s)).basis := by
  rw [value_map]
  apply regValue_congr
  intro q hq
  exact (run_rename_pool f (Finset.range n) inj p support m
    (pullState f s) s rfl (fun _ _ => rfl)).2 q (Finset.mem_range.mpr (ports q hq))

/-- Actual renamed lift output and cleanup for arbitrary measurement tapes.
The physical signed input convention is checked on the placed ports. -/
theorem placedMagnitude_of_good (f : Wire → Wire)
    (inj : Set.InjOn f (Finset.range 305)) (call : FusedCall)
    (s : State) (m : List Bool)
    (clean : ∀ i<24,s.basis (f (281+i))=false)
    (encoding : MagnitudeEncodes call.coefficient (fun q => s.basis (f q)))
    (good : call.LiftGood) :
    let out := run (placedMagnitude f false) m s
    regValue (magnitudePayload.map f) out.basis=call.coefficient.natAbs ∧
      (∀i<24,out.basis (f (281+i))=false) ∧
      out.basis (f 0)=s.basis (f 0) ∧ out.phase=s.phase := by
  have sem := run_rename_pool f (Finset.range 305) inj (fusedMagnitudeLift false)
    (fusedMagnitudeLift_support false) m (pullState f s) s rfl (fun _ _ => rfl)
  have tidy := fusedMagnitudeLift_cleanup (pullState f s) m clean
  refine ⟨?_,?_,?_,sem.1.trans tidy.2.2⟩
  · have ports : ∀q∈magnitudePayload,q<305 := by
      intro q hq
      simp only [magnitudePayload,List.mem_range'] at hq
      dsimp only [Wire] at *
      omega
    exact (placed_value f 305 inj _ (fusedMagnitudeLift_support false)
      magnitudePayload ports s m).trans
      (fusedMagnitudeLift_of_good call (pullState f s) m clean encoding good)
  · intro i hi
    dsimp only [Wire] at i hi
    exact (sem.2 _ (by simp only [Finset.mem_range]; dsimp only [Wire]; omega)).trans (tidy.1 i hi)
  · exact (sem.2 0 (by simp)).trans tidy.2.1

/-- Physical wires outside the finite placed component are unchanged. -/
theorem placedMagnitude_outside (f : Wire → Wire) (inverse : Bool)
    (s : State) (m : List Bool) (q : Wire)
    (outside : q∉(Finset.range 305).image f) :
    (run (placedMagnitude f inverse) m s).basis q=s.basis q :=
  run_rename_pool_outside f _ _ (fusedMagnitudeLift_support inverse) m s q outside


private theorem fold_low_ports : ∀q∈fusedFoldLow,q<537 := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  have hi := List.mem_range.mp hi
  dsimp only [Wire] at *
  omega

/-- The renamed source-order fold computes the mathematical scan value and
restores all physical ports except the low row, including all outsiders. -/
theorem placedRowFold_of_good (f : Wire → Wire)
    (inj : Set.InjOn f (Finset.range 537)) (call : FusedCall)
    (s : State) (m : List Bool)
    (clean : regValue (fusedFoldWord.map f) s.basis=0)
    (carry : s.basis (f 536)=false)
    (encoding : regValue ((fusedFoldLow++fusedFoldHigh).map f) s.basis=
      call.coefficient.natAbs) (good : call.RowGood) :
    let out := run (placedRowFold f false) m s
    regValue (fusedFoldLow.map f) out.basis=wideMagnitudeFold call.coefficient.natAbs ∧
      out.phase=s.phase ∧
      (∀q,q∉fusedFoldLow.map f → out.basis q=s.basis q) := by
  have clean' : regValue fusedFoldWord (pullState f s).basis=0 := by
    simpa only [value_map,pullState] using clean
  have encoding' : regValue (fusedFoldLow++fusedFoldHigh) (pullState f s).basis=
      call.coefficient.natAbs := by
    simpa only [value_map,pullState] using encoding
  have sem := run_rename_pool f (Finset.range 537) inj (fusedRowFoldSource false)
    (fusedRowFoldSource_resources false).1 m (pullState f s) s rfl (fun _ _ => rfl)
  have result := fusedRowFoldSource_forward (pullState f s) m clean' carry
  refine ⟨?_,sem.1.trans result.1,?_⟩
  · exact (placed_value f 537 inj _ (fusedRowFoldSource_resources false).1
      fusedFoldLow fold_low_ports s m).trans
      (fusedRowFoldSource_of_good call (pullState f s) m clean' carry encoding' good)
  · intro q hq
    by_cases inside : q∈(Finset.range 537).image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp inside
      have low : a∉fusedFoldLow := fun h => hq (List.mem_map.mpr ⟨a,h,rfl⟩)
      exact (sem.2 a ha).trans (result.2.1 a low)
    · exact run_rename_pool_outside f _ _ (fusedRowFoldSource_resources false).1 m s q inside

end ECDSAAdd.Arithmetic.Paper935
