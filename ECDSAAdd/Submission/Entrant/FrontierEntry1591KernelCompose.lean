import ECDSAAdd.Submission.Entrant.FrontierEntry1591Native

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk
attribute [local irreducible] run wires

theorem pool_away_numerator (q : Wire) (hq : q∈skywalkPoolWires base) :
    q∉wireBlock base 2056 256 := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [skywalkPoolWires,wireBlock,List.mem_range'_1] at hi
  exact OwnPlusHost.not_block _ 2056 256 (by omega)

theorem numerator_away_pool (q : Wire) (hq : q∈wireBlock base 2056 256) :
    q∉skywalkPoolWires base := by
  intro hp
  exact pool_away_numerator q hp hq

theorem paired_input (x y : Nat) (s t : State)
    (input : SkywalkArithmeticInput base x y s.basis)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q) :
    SkywalkArithmeticInput base x (regValue (wireBlock base 2056 256) t.basis) t.basis := by
  refine ⟨?_,rfl,?_⟩
  · change regValue (wireBlock base 770 256) t.basis=x
    apply (regValue_congr _ _ _ ?_).trans input.1
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact same _ (OwnPlusHost.not_block _ 2056 256 (by omega))
  · intro q hq hdx hdy
    exact (same q hdy).trans (input.2.2 q hq hdx hdy)

theorem sandwich_states (First Last : Program)
    (firstPool : wires First⊆(skywalkPoolWires base).toFinset)
    (lastPool : wires Last⊆(skywalkPoolWires base).toFinset)
    (initial before after out : State) (mp mr : List Bool) (value : Nat)
    (first : run First mp initial=before)
    (last : run Last mr after=out) (roundtrip : run Last mr before=initial)
    (result : after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q) :
    out.phase=initial.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=initial.basis q := by
  have agrees := pool_run_agrees Last (skywalkPoolWires base).toFinset lastPool mr
    after before result.1
    (fun q hq => result.2.2 q (pool_away_numerator q (List.mem_toFinset.mp hq)))
  rw [last,roundtrip] at agrees
  refine ⟨agrees.1,?_,?_⟩
  · have keep : regValue (wireBlock base 2056 256) out.basis=
        regValue (wireBlock base 2056 256) after.basis := by
      apply regValue_congr
      intro q hq
      rw [←last]
      exact run_preserves_outside _ mr after q
        (fun h => numerator_away_pool q hq (List.mem_toFinset.mp (lastPool h)))
    exact keep.trans result.2.1
  · intro q hq
    by_cases pool : q∈skywalkPoolWires base
    · exact agrees.2 q (List.mem_toFinset.mpr pool)
    · have lastKeep : out.basis q=after.basis q := by
        rw [←last]
        exact run_preserves_outside _ mr after q
          (fun h => pool (List.mem_toFinset.mp (lastPool h)))
      have firstKeep : before.basis q=initial.basis q := by
        rw [←first]
        exact run_preserves_outside _ mp initial q
          (fun h => pool (List.mem_toFinset.mp (firstPool h)))
      exact lastKeep.trans ((result.2.2 q hq).trans firstKeep)

end ECDSAAdd.Entrant.FrontierEntry1591Kernel
