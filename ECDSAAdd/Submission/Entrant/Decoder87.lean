import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Framework.FiniteUnitary
import ECDSAAdd.Challenge.Contract

namespace ECDSAAdd.Entrant.Decoder87

open Challenge

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def full : Program :=
  [.CX 32 0,
   .X 0,
   .CCX 31 0 1,
   .CX 31 2,
   .CX 1 2,
   .CX 0 3,
   .CX 1 3,
   .CX 32 4,
   .CX 2 4,
   .CCX 30 3 5,
   .CCX 30 1 6,
   .CCX 30 4 7,
   .CX 30 8,
   .CX 5 8,
   .CX 6 8,
   .CX 7 8,
   .CX 3 9,
   .CX 5 9,
   .CX 1 10,
   .CX 6 10,
   .CX 4 11,
   .CX 7 11,
   .CX 2 12,
   .CX 8 12,
   .CCX 29 9 13,
   .CCX 29 5 14,
   .CCX 29 10 15,
   .CCX 29 6 16,
   .CCX 29 11 17,
   .CCX 29 7 18,
   .CCX 29 12 19,
   .CX 29 20,
   .CX 13 20,
   .CX 14 20,
   .CX 15 20,
   .CX 16 20,
   .CX 17 20,
   .CX 18 20,
   .CX 19 20,
   .CX 9 21,
   .CX 13 21,
   .CX 5 22,
   .CX 14 22,
   .CX 10 23,
   .CX 15 23,
   .CX 6 24,
   .CX 16 24,
   .CX 11 25,
   .CX 17 25,
   .CX 7 26,
   .CX 18 26,
   .CX 12 27,
   .CX 19 27,
   .CX 8 28,
   .CX 20 28]

def pruned : Program := full.take 29 ++ full.drop 31

def input (k q : Nat) : Bool := if q < 29 then false else k.testBit (q - 29)

theorem support_full : wires full ⊆ Finset.range 33 := by decide +kernel
theorem support_pruned : wires pruned ⊆ Finset.range 33 := by decide +kernel
theorem proper_full : ProperProgram full := by simp [ProperProgram, full, ProperGate]
theorem proper_pruned : ProperProgram pruned := by simp [ProperProgram, pruned, full, ProperGate]
theorem pruned_sublist : pruned.Sublist full := by decide +kernel
theorem counts :
    toffoliCount pruned + 2 = toffoliCount full ∧
    measurementCount pruned = 0 ∧ measurementCount full = 0 ∧
    gateSlots pruned + 2 = gateSlots full := by decide +kernel

theorem checked :
    ∀ k : Fin 11, ∀ q : Fin 33,
      (run pruned [] ⟨false, input k⟩).basis q =
        (run full [] ⟨false, input k⟩).basis q := by
  decide +kernel

private theorem state_eq (s t : State) (hp : s.phase = t.phase)
    (hb : s.basis = t.basis) : s = t := by
  cases s
  cases t
  simp_all

theorem model_run (k : Nat) (hk : k < 11) (phase : Bool) :
    run pruned [] ⟨phase, input k⟩ = run full [] ⟨phase, input k⟩ := by
  apply state_eq
  · exact (FiniteUnitary.run_phase pruned proper_pruned _ _).trans
      (FiniteUnitary.run_phase full proper_full _ _).symm
  · funext q
    rw [congrFun (FiniteUnitary.run_basis_phase pruned proper_pruned (input k) phase false []) q,
      congrFun (FiniteUnitary.run_basis_phase full proper_full (input k) phase false []) q]
    by_cases hq : q < 33
    · exact checked ⟨k, hk⟩ ⟨q, hq⟩
    · rw [run_preserves_outside pruned _ _ q (fun h => hq (Finset.mem_range.mp (support_pruned h))),
        run_preserves_outside full _ _ q (fun h => hq (Finset.mem_range.mp (support_full h)))]

theorem placed_run (f : Wire → Wire)
    (hf : ∀ a ∈ Finset.range 33, ∀ b ∈ Finset.range 33, f a = f b → a = b)
    (k : Nat) (hk : k < 11) (s : State) (m : List Bool)
    (hb : ∀ q ∈ Finset.range 33, s.basis (f q) = input k q) :
    run (renameProgram f pruned) m s = run (renameProgram f full) m s := by
  let t : State := ⟨s.phase, input k⟩
  have hp := run_rename_pool f (Finset.range 33) hf pruned support_pruned m t s rfl
    (fun q hq => (hb q hq).symm)
  have hr := run_rename_pool f (Finset.range 33) hf full support_full m t s rfl
    (fun q hq => (hb q hq).symm)
  have eq : run pruned m t = run full m t := by
    apply state_eq
    · exact (FiniteUnitary.run_phase pruned proper_pruned _ _).trans
        (FiniteUnitary.run_phase full proper_full _ _).symm
    · change (run pruned m ⟨s.phase, input k⟩).basis = (run full m ⟨s.phase, input k⟩).basis
      rw [FiniteUnitary.run_basis_phase pruned proper_pruned (input k) s.phase s.phase m,
        FiniteUnitary.run_basis_phase full proper_full (input k) s.phase s.phase m,
        model_run k hk s.phase]
  apply state_eq
  · exact hp.1.trans ((congrArg State.phase eq).trans hr.1.symm)
  · funext q
    by_cases hq : q ∈ (Finset.range 33).image f
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      exact (hp.2 a ha).trans ((congrFun (congrArg State.basis eq) a).trans (hr.2 a ha).symm)
    · exact (run_rename_pool_outside f (Finset.range 33) pruned support_pruned m s q hq).trans
        (run_rename_pool_outside f (Finset.range 33) full support_full m s q hq).symm

end ECDSAAdd.Entrant.Decoder87
