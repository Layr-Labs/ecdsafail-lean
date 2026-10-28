import ECDSAAdd.Arithmetic.MappedCompressedCallerRun
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk
attribute [local irreducible] run measurementCount kernel
  directZeroDivisorEnter directZeroDivisorLeave

private theorem controlled_port_nodup :
    (base 2411::base 2313::(wireBlock base 770 256++wireBlock base 0 255++
      wireBlock base 2056 256)).Nodup := by
  have first : (List.range' 770 256++List.range' 0 255).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hx hc
    simp only [List.mem_range'_1] at hx hc
    omega
  have words : (List.range' 770 256++List.range' 0 255++List.range' 2056 256).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨first,List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hxy hz
    simp only [List.mem_append,List.mem_range'_1] at hxy hz
    omega
  have ids : (2411::2313::(List.range' 770 256++List.range' 0 255++List.range' 2056 256)).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp only [List.mem_cons,List.mem_append,List.mem_range'_1]
      omega
    · apply List.nodup_cons.mpr
      constructor
      · simp only [List.mem_append,List.mem_range'_1]
        omega
      · exact words
  change ((2411::2313::(List.range' 770 256++List.range' 0 255++
    List.range' 2056 256)).map base).Nodup
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact ids

private theorem zero_flag_outside : base 2411 ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hi
  have same := base_injective eq
  omega

/-- The actual zero-divisor wrapper satisfies the original strong port
contract. A zero divisor is allowed on the inactive arithmetic branch;
comparison work and repaired kernel cleanliness come from the caller input. -/
theorem controlled_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (zeroBranch : x = 0 → s.basis (base 2400) = false)
    (hflag : s.basis (base 2411) = false)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s (run (controlled divide) m s) := by
  let D := directDivisor x
  let R := (directSkywalkResult divide (s.basis (base 2400)) x Y).val
  have positive : 0 < D := Nat.pos_of_ne_zero (directDivisor_ne_zero x)
  have bound : D < p := by
    by_cases zero : x = 0
    · simp only [D,directDivisor,zero,if_true]
      norm_num [p]
    · simpa only [D,directDivisor,zero,if_false] using hx
  have sameResult : directSkywalkResult divide (s.basis (base 2400)) D Y =
      directSkywalkResult divide (s.basis (base 2400)) x Y := by
    by_cases zero : x = 0
    · simp only [directSkywalkResult,zeroBranch zero,Bool.false_eq_true,if_false]
    · simp only [D,directDivisor,zero,if_false]
  have cin : s.basis (base 2313) = false :=
    arith_input_bit base hn x Y.val s.basis hin 2313 (by omega) (by omega) (by omega)
  have carry : ∀ q ∈ wireBlock base 0 255,s.basis q = false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact arith_input_bit base hn x Y.val s.basis hin i (by omega) (by omega) (by omega)
  have callback : ∀ (t : State) (ms : List Bool),
      regValue (wireBlock base 770 256) t.basis = directDivisor (regValue (wireBlock base 770 256) s.basis) →
      regValue (wireBlock base 2056 256) t.basis = regValue (wireBlock base 2056 256) s.basis →
      t.basis (base 2411) = decide (regValue (wireBlock base 770 256) s.basis = 0) →
      (∀ q,q ≠ base 2411 → q ∉ wireBlock base 770 256 → t.basis q = s.basis q) →
      (run (kernel divide) ms t).phase = t.phase ∧
      regValue (wireBlock base 2056 256) (run (kernel divide) ms t).basis = R ∧
      ∀ q,q ∉ wireBlock base 2056 256 → (run (kernel divide) ms t).basis q = t.basis q := by
    intro t ms divisor numerator _ frame
    have input : SkywalkArithmeticInput base D Y.val t.basis := by
      refine ⟨divisor.trans (congrArg directDivisor hin.1),numerator.trans hin.2.1,?_⟩
      intro q hq hdx hdy
      have ne : q ≠ base 2411 := fun eq => zero_flag_outside (eq ▸ hq)
      exact (frame q ne hdx).trans (hin.2.2 q hq hdx hdy)
    have controls (q : Wire) (hq : q ∈ [base 2400,base 2409,base 2410]) :
        t.basis q = s.basis q := by
      have ne : q ≠ base 2411 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl|rfl|rfl
        all_goals intro eq; have same := base_injective eq; omega
      have away : q ∉ wireBlock base 770 256 :=
        fun bad => ho q hq (arith_block_subset_shared base 770 256 (by omega) bad)
      exact frame q ne away
    have strong := kernel_spec divide hn hlo ho hf D Y positive bound t ms input
      ((controls _ (by simp)).trans hg0) ((controls _ (by simp)).trans hs0)
    unfold DirectSkywalkArithmeticStrong at strong
    rw [controls (base 2400) (by simp),sameResult] at strong
    exact strong
  have width : (wireBlock base 0 255).length+1 = (wireBlock base 770 256).length := by
    simp only [wireBlock_length]
  have records := directZeroControlled_states (wireBlock base 770 256) (wireBlock base 2056 256)
    (wireBlock base 0 255) (base 2313) (base 2411) controlled_port_nodup width (kernel divide) s
    (m.take (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411))))
    ((m.drop (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411)))).take (measurementCount (kernel divide)))
    ((m.drop (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411)))).drop (measurementCount (kernel divide)))
    R cin hflag carry callback
  simpa only [DirectSkywalkArithmeticStrong,controlled,directZeroControlled,run_append,
    skywalkArithmeticNumerator,R] using records

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.controlled_spec
