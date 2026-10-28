import ECDSAAdd.Arithmetic.Paper935.Fold32Constants
import ECDSAAdd.Framework.WireRename

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic RecordedQuantum

/-- Move the control to a separate comparison flag while fixing data and pool. -/
def fold32ControlSwap (q : Wire) : Wire := if q=0 then 290 else if q=290 then 0 else q

def fold32FlagProgram (bits : Nat → Bool) : Program :=
  renameProgram fold32ControlSwap (fold32Program bits)

theorem fold32ControlSwap_injective : Function.Injective fold32ControlSwap := by
  intro a b h
  simp only [fold32ControlSwap] at h
  dsimp only [Wire] at *
  split_ifs at h <;> omega

private theorem swap_fixed (q : Wire) (h : 0<q ∧ q<290) : fold32ControlSwap q=q := by
  unfold fold32ControlSwap
  split_ifs <;> dsimp only [Wire] at * <;> omega

private theorem pull_word (s : State) :
    regValue fold32Word (pullState fold32ControlSwap s).basis=regValue fold32Word s.basis := by
  apply regValue_congr
  intro q hq
  simp only [fold32Word,List.mem_range'] at hq
  change s.basis (fold32ControlSwap q)=s.basis q
  rw [swap_fixed q (by dsimp only [Wire]; omega)]

theorem fold32FlagProgram_contract (bits : Nat → Bool) (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) :
    let out := run (fold32FlagProgram bits) m s
    regValue fold32Word out.basis=
      (regValue fold32Word s.basis+(if s.basis 290 then fold32Literal bits else 0))%2^257 ∧
    Fold32Ready 0 out.basis ∧ out.basis 290=s.basis 290 ∧ out.phase=s.phase := by
  have clean : Fold32Ready 0 (pullState fold32ControlSwap s).basis := by
    intro i hi lower
    change s.basis (fold32ControlSwap (258+i))=false
    rw [swap_fixed _ (by dsimp only [Wire]; omega)]
    exact ready i hi lower
  have contract := fold32Program_contract bits (pullState fold32ControlSwap s) m clean
  have execution := run_rename fold32ControlSwap fold32ControlSwap_injective (fold32Program bits) m s
  dsimp only at contract
  rw [←execution,pull_word,pull_word] at contract
  refine ⟨contract.1,?_,contract.2.2.1,contract.2.2.2⟩
  intro i hi lower
  have h := contract.2.1 i hi lower
  change (run (fold32FlagProgram bits) m s).basis (fold32ControlSwap (258+i))=false at h
  rwa [swap_fixed _ (by dsimp only [Wire]; omega)] at h

theorem fold32FlagProgram_support (bits : Nat → Bool) :
    wires (fold32FlagProgram bits) ⊆ Finset.range 291 := by
  rw [fold32FlagProgram,renameProgram_support]
  intro q hq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
  have bound := Finset.mem_range.mp (fold32Program_support bits ha)
  simp only [Finset.mem_range,fold32ControlSwap]
  split_ifs <;> omega

theorem fold32FlagProgram_physical (bits : Nat → Bool) : GatePhysical (fold32FlagProgram bits) := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have h := fold32Program_physical bits j hj
  cases j <;> simp_all [renameInstr,PhysicalInstr,ProperGate,fold32ControlSwap_injective.eq_iff]

/-- The original control is outside the renamed program. -/
theorem fold32FlagProgram_control (bits : Nat → Bool) (s : State) (m : List Bool) :
    (run (fold32FlagProgram bits) m s).basis 0=s.basis 0 := by
  apply run_preserves_outside
  intro h
  rw [fold32FlagProgram,renameProgram_support] at h
  obtain ⟨a,ha,h⟩ := Finset.mem_image.mp h
  have bound := Finset.mem_range.mp (fold32Program_support bits ha)
  simp only [fold32ControlSwap] at h
  split_ifs at h <;> dsimp only [Wire] at * <;> omega

end ECDSAAdd.Arithmetic.Paper935
