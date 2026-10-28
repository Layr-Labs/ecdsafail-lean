import ECDSAAdd.Arithmetic.Paper935.FoldHalve

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Reuse the same parity line and sixteen pool lines for each seam call. -/
def foldSeamProgram : Nat → Program
  | 0 => []
  | n+1 => foldHalveProgram++foldSeamProgram n

/-- The repeated physical seam implements repeated ideal halving on the
explicit per-call no-borrow event, with all work lines restored each time. -/
theorem foldSeam_contract (n : Nat) (s : State) (m : List Bool)
    (ready : Fold256Ready s.basis) (zero : s.basis 0=false)
    (good : ScalingNoBorrow (2^256-(2^32+977)) 58 (2^32+977)
      (List.replicate n true) (regValue fold256Word s.basis)) :
    let out := run (foldSeamProgram n) m s
    regValue fold256Word out.basis=(halveMod (2^256-(2^32+977)))^[n] (regValue fold256Word s.basis) ∧
    Fold256Ready out.basis ∧ out.basis 0=false ∧ out.phase=s.phase := by
  induction n generalizing s m with
  | zero => exact ⟨rfl,ready,zero,rfl⟩
  | succ n ih =>
    have conditions : FoldNoBorrow 58 (2^32+977) (regValue fold256Word s.basis) ∧
        ScalingNoBorrow (2^256-(2^32+977)) 58 (2^32+977) (List.replicate n true)
          (halveMod (2^256-(2^32+977)) (regValue fold256Word s.basis)) := by
      simpa only [List.replicate_succ,ScalingNoBorrow,true_implies,if_true] using good
    have first := foldHalve_contract s m ready zero
    have value := foldHalve_correct s m ready zero conditions.1
    dsimp only at first
    generalize hs : run foldHalveProgram m s=t at first value
    have restGood := conditions.2
    rw [←value] at restGood
    have tailResult := ih t (m.drop (measurementCount foldHalveProgram)) first.2.1 first.2.2.1 restGood
    dsimp only
    rw [foldSeamProgram,run_append,run_take,hs]
    refine ⟨?_,tailResult.2.1,tailResult.2.2.1,tailResult.2.2.2.trans first.2.2.2⟩
    rw [tailResult.1,value,Function.iterate_succ_apply]

/-- The author's fixed 498-call seam, before the active reverse rider. -/
theorem foldSeam498_correct (s : State) (m : List Bool)
    (ready : Fold256Ready s.basis) (zero : s.basis 0=false)
    (good : ScalingNoBorrow (2^256-(2^32+977)) 58 (2^32+977)
      (List.replicate 498 true) (regValue fold256Word s.basis)) :
    regValue fold256Word (run (foldSeamProgram 498) m s).basis=
      (halveMod (2^256-(2^32+977)))^[498] (regValue fold256Word s.basis) :=
  (foldSeam_contract 498 s m ready zero good).1

end ECDSAAdd.Arithmetic.Paper935
