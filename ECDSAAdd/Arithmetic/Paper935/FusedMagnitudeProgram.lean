import ECDSAAdd.Arithmetic.Paper935.Lift24Resources
import ECDSAAdd.Arithmetic.CuccaroSignedSquareInverse

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- engine.py:3296–3308. Move the 24-wire pool above the entire 280-bit
payload, retaining control/sign 0 and low window 1..58. -/
def magnitudeWindowMap (q : Wire) : Wire := if q<59 then q else q+222

theorem magnitudeWindowMap_injective : Function.Injective magnitudeWindowMap := by
  intro a b h
  dsimp [magnitudeWindowMap] at h
  dsimp only [Wire] at *
  split_ifs at h <;> omega

def magnitudePayload : List Wire := List.range' 1 280
def magnitudeWindow (subtract : Bool) : Program :=
  renameProgram magnitudeWindowMap (lift24Program subtract)
def MagnitudeReady (s : BasisState) : Prop := ∀ i<24,s (281+i)=false

/-- engine.py:3296: sign-controlled complement on all payload bits followed
by the actual truncated plus-one. Inverse subtracts one before undoing CXs. -/
def fusedMagnitudeLift (inverse : Bool) : Program :=
  if inverse then magnitudeWindow true ++ (signComplement 0 magnitudePayload).reverse
  else signComplement 0 magnitudePayload ++ magnitudeWindow false

attribute [local irreducible] lift24Program

theorem magnitudeWindow_roundtrip (s : State) (m n : List Bool)
    (ready : MagnitudeReady s.basis) :
    run (magnitudeWindow true) n (run (magnitudeWindow false) m s)=s := by
  have clean : Lift24Ready 0 (pullState magnitudeWindowMap s).basis := by
    intro i hi _
    simpa [pullState,magnitudeWindowMap,show ¬59+i<59 by omega,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using ready i hi
  have pulled : pullState magnitudeWindowMap
      (run (magnitudeWindow true) n (run (magnitudeWindow false) m s))=
      pullState magnitudeWindowMap s := by
    rw [magnitudeWindow,run_rename _ magnitudeWindowMap_injective,
      magnitudeWindow,run_rename _ magnitudeWindowMap_injective]
    exact lift24Program_roundtrip _ m n clean
  apply State.extensionality
  · simpa only [pullState] using congrArg State.phase pulled
  · funext q
    by_cases low : q<59
    · have h := congrArg (fun t : State => t.basis q) pulled
      simpa [pullState,magnitudeWindowMap,low] using h
    by_cases high : 281≤q
    · have h := congrArg (fun t : State => t.basis (q-222)) pulled
      have lower : ¬q-222<59 := by dsimp only [Wire] at *; omega
      have eq : q-222+222=q := by dsimp only [Wire] at *; omega
      simpa [pullState,magnitudeWindowMap,lower,eq] using h
    · have away (b : Bool) : q∉wires (magnitudeWindow b) := by
        rw [magnitudeWindow,renameProgram_support]
        intro mem
        obtain ⟨j,_,eq⟩ := Finset.mem_image.mp mem
        dsimp [magnitudeWindowMap] at eq
        dsimp only [Wire] at *
        split_ifs at eq <;> omega
      exact (run_preserves_outside _ n _ q (away true)).trans
        (run_preserves_outside _ m s q (away false))

theorem fusedMagnitudeLift_roundtrip (s : State) (m n : List Bool)
    (ready : MagnitudeReady s.basis) :
    run (fusedMagnitudeLift true) n (run (fusedMagnitudeLift false) m s)=s := by
  have complement := signComplement_correct 0 magnitudePayload
    (by exact List.nodup_range') (by simp [magnitudePayload]) s m
  have clean : MagnitudeReady (run (signComplement 0 magnitudePayload) m s).basis := by
    intro i hi
    rw [complement.2.1 (281+i) (by simp [magnitudePayload])]
    exact ready i hi
  have proper : ProperProgram (signComplement 0 magnitudePayload) := by
    intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    simp only [ProperGate]
    simp only [magnitudePayload,List.mem_range'] at hq
    dsimp only [Wire] at *
    omega
  simp only [fusedMagnitudeLift,Bool.false_eq_true,if_false,if_true,
    run_append,run_take]
  simp only [(signComplement_counts 0 magnitudePayload).2,List.drop_zero]
  rw [magnitudeWindow_roundtrip _ m n clean]
  exact run_reverse_proper _ proper s m _

theorem fusedMagnitudeLift_counts (inverse : Bool) :
    toffoliCount (fusedMagnitudeLift inverse)=95 ∧
    measurementCount (fusedMagnitudeLift inverse)=92 := by
  have counts (b : Bool) : toffoliCount (magnitudeWindow b)=95 ∧
      measurementCount (magnitudeWindow b)=92 := by
    rw [magnitudeWindow,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
    exact lift24Program_counts b
  cases inverse <;> simp [fusedMagnitudeLift,toffoliCount_reverse,measurementCount_reverse,
    counts,signComplement_counts]

theorem magnitudeWindow_support (b : Bool) : wires (magnitudeWindow b) ⊆ Finset.range 305 := by
  rw [magnitudeWindow,renameProgram_support]
  intro q hq
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
  have bound := lift24Program_support b hj
  simp only [Finset.mem_range] at bound ⊢
  dsimp [magnitudeWindowMap]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem fusedMagnitudeLift_support (inverse : Bool) :
    wires (fusedMagnitudeLift inverse) ⊆ Finset.range 305 := by
  have comp : wires (signComplement 0 magnitudePayload) ⊆ Finset.range 305 := by
    apply Finset.Subset.trans (signComplement_wires_subset _ _)
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,magnitudePayload,List.mem_range'] at hq
    simp only [Finset.mem_range]
    dsimp only [Wire] at *
    rcases hq with rfl|⟨i,hi,rfl⟩ <;> omega
  cases inverse <;> simp only [fusedMagnitudeLift,Bool.false_eq_true,if_false,if_true,
    wires_append,wires_reverse,Finset.union_subset_iff]
  · exact ⟨comp,magnitudeWindow_support false⟩
  · exact ⟨magnitudeWindow_support true,comp⟩

end ECDSAAdd.Arithmetic.Paper935
