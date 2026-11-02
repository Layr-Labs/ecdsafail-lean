import ECDSAAdd.Submission.Entrant.Prelude

/-! Ticks 509 and 510 of the integer walk as one forced block (terrapinelf, submission f753049b,
ported by e-man07 in e1b7db22 and a6dcb576).  This module carries the donor section unchanged. -/

section

/-! Ticks `509` and `510` as one block.

On the forced input of tick `509` (`u+v ≤ 4`, eighteen basis states) the function
space spanned by the forward outputs of ticks `509`–`510` exceeds the input-affine
functions by two dimensions, and both missing directions are products of
input-affine functions: `base 511·base 772` and `base 508·(base 510 ⊕ base 771)`.
The merged forward block computes these two products, maps the state affinely to the
outputs plus five garbage letters, and erases the letters by measurement with
quadratic corrections (two Toffolis instead of three).  The merged reverse block
rebuilds the inputs with five products of available affine functions and erases two
garbage letters (five Toffolis instead of six); its last two measurements act on
clean wires, so both blocks keep the measurement counts of the original ticks. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 History5

/-- Gate list of `W.ReverseCarry.compactReceiverTick base 509`. -/
def tick509ExR : Program :=
  [.CX 788 789, .CX 528 529, .CX 524 525, .CX 1553 789, .X 1553, .CX 528 1553, .CX 788 1553,
   .X 786, .X 787, .X 788, .CX 1553 526, .CX 1553 527, .CX 1553 528, .CX 526 786, .CX 526 1553,
   .CCX 786 1553 1556, .CX 526 1556, .CX 526 1553, .CX 526 786,
   .measureX 788 [] [.CZ 527 787, .CZ 527 1556, .CZ 787 1556], .CX 528 788, .CX 527 787,
   .CX 1556 787, .measureX 1556 [] [.CZ 526 786, .CZ 526 1553, .CZ 786 1553], .CX 526 786,
   .CX 1553 786, .CX 1553 526, .CX 1553 527, .CX 1553 528, .X 786, .X 787, .X 788, .X 1553,
   .CX 528 1553, .CX 788 1553, .CX 528 529, .CX 525 786, .CX 787 526, .CX 788 527, .CX 789 528,
   .CCX 525 526 787, .CCX 525 527 788, .CCX 525 528 789, .CX 787 526, .CX 788 527, .CX 789 528]

/-- Ticks `509` and `510` forward on the forced input of tick `509`. -/
def tickMF : Program :=
  [.CCX 527 788 1556, .CX 787 526, .CCX 524 526 1557, .CX 1557 1554, .CX 1557 788, .CX 1557 787,
   .CX 1557 528, .CX 1556 1553, .CX 1556 789, .CX 1556 527, .CX 1554 1557, .CX 1554 789,
   .CX 1554 788, .CX 1554 528, .CX 1557 1554, .CX 1553 1556, .CX 1553 527, .CX 1556 1553,
   .CX 789 1557, .CX 789 528, .CX 1557 789, .CX 788 789, .CX 789 788, .CX 787 1557, .CX 787 1553,
   .CX 787 529, .CX 787 528, .CX 787 526, .CX 529 787, .CX 787 529, .CX 528 1557, .CX 528 1554,
   .CX 1554 528, .CX 527 1556, .CX 1556 527, .CX 526 1554, .CX 526 1553, .CX 526 786,
   .CX 526 529, .CX 526 527, .CX 525 1554, .CX 525 1553, .CX 525 527, .CX 525 526, .CX 524 1554,
   .CX 524 1553, .CX 524 786, .CX 524 527, .CX 524 526, .CX 524 525, .X 527, .X 529, .X 786,
   .X 1553, .X 1554, .X 1556,
   .measureX 789 [] [.CZ 786 1557, .Z 1553, .CZ 525 527, .CZ 527 1556, .Z 1554],
   .measureX 1556 [] [.CZ 524 1553, .CZ 525 1557, .CZ 527 528, .CZ 525 527, .Z 526],
   .measureX 528 [] [.Z 524, .CZ 524 529],
   .measureX 529 [] [.CZ 526 1553, .CZ 525 1554, .Z 1554, .Z 525],
   .measureX 1557 [] [.CZ 524 1553, .CZ 524 1554]]

/-- Reverse ticks `510` and `509` on the merged forward outputs. -/
def tickMR : Program :=
  [.CCX 525 526 528, .CX 1554 1553, .CCX 524 1553 529, .CX 526 525, .CCX 1553 525 787,
   .CX 528 525, .CCX 524 525 788, .CX 528 524, .CX 787 524, .CX 788 526, .CX 1554 526,
   .CCX 524 526 789, .CX 1556 786, .CX 1554 1553, .CX 1554 787, .CX 1554 786, .CX 1554 529,
   .CX 1554 527, .CX 1554 525, .CX 1554 524, .CX 1553 1554, .CX 1553 529, .CX 1553 526,
   .CX 789 1554, .CX 789 1553, .CX 789 788, .CX 789 786, .CX 789 529, .CX 789 527, .CX 789 526,
   .CX 789 525, .CX 788 1553, .CX 1553 788, .CX 787 1553, .CX 787 788, .CX 787 786, .CX 787 527,
   .CX 787 525, .CX 787 524, .CX 786 1556, .CX 1556 786, .CX 529 1554, .CX 529 1553, .CX 529 789,
   .CX 529 526, .CX 789 529, .CX 528 1556, .CX 528 1554, .CX 528 527, .CX 528 526, .CX 528 524,
   .CX 1554 528, .CX 527 1556, .CX 527 1554, .CX 527 787, .CX 527 526, .CX 527 525, .CX 526 1553,
   .CX 526 788, .CX 526 529, .CX 526 527, .CX 527 526, .CX 525 786, .CX 525 527, .CX 525 526,
   .CX 524 1554, .CX 524 788, .CX 524 787, .CX 524 786, .CX 524 529, .CX 524 527, .CX 524 526,
   .CX 524 525, .X 525, .X 529, .X 788, .X 1553, .X 1554, .X 1556,
   .measureX 529 [] [.CZ 527 788, .Z 788], .measureX 1554 [] [.CZ 524 526, .Z 528, .CZ 526 786],
   .measureX 1556 [] [], .measureX 529 [] []]

/-- The fourteen physical wires of ticks `509` and `510`. -/
def sitesM : List Wire := [524, 525, 526, 527, 528, 529, 786, 787, 788, 789, 1553, 1554, 1556, 1557]

theorem tick509ExR_explicit : W.ReverseCarry.compactReceiverTick base 509 = tick509ExR := by
  decide +kernel
theorem tickMF_wires : wires tickMF ⊆ sitesM.toFinset := by decide +kernel
theorem tickMR_wires : wires tickMR ⊆ sitesM.toFinset := by decide +kernel
theorem pairF_wires : wires (tick509ExF ++ tick510ExF) ⊆ sitesM.toFinset := by decide +kernel
theorem pairR_wires : wires (tick510ExR ++ tick509ExR) ⊆ sitesM.toFinset := by decide +kernel
theorem tickMF_sub : wires tickMF ⊆ wires (tick509ExF ++ tick510ExF) := by decide +kernel
theorem sitesM_pool : ∀ q ∈ sitesM, q ∈ skywalkPoolWires base := by decide +kernel
theorem tickMR_sub : wires tickMR ⊆ wires (tick510ExR ++ tick509ExR) := by decide +kernel

theorem tickM_counts :
    toffoliCount tickMF = 2 ∧ measurementCount tickMF = 5 ∧
    toffoliCount (tick509ExF ++ tick510ExF) = 8 ∧ measurementCount (tick509ExF ++ tick510ExF) = 5 ∧
    toffoliCount tickMR = 5 ∧ measurementCount tickMR = 4 ∧
    toffoliCount (tick510ExR ++ tick509ExR) = 7 ∧ measurementCount (tick510ExR ++ tick509ExR) = 4 := by
  decide +kernel

theorem tickM_slots :
    Challenge.gateSlots tickMF ≤ Challenge.gateSlots (tick509ExF ++ tick510ExF) ∧
    Challenge.gateSlots tickMR ≤ Challenge.gateSlots (tick510ExR ++ tick509ExR) := by decide +kernel

theorem tickM_physical : GatePhysical tickMF ∧ GatePhysical tickMR := by
  constructor <;> simp [tickMF, tickMR, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]

/-- All measurement records of length at most `n`. -/
def recsUpTo : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => [] :: ((recsUpTo n).map (false :: ·) ++ (recsUpTo n).map (true :: ·))

theorem take_recsUpTo (n : Nat) (m : List Bool) : m.take n ∈ recsUpTo n := by
  induction n generalizing m with
  | zero => simp [recsUpTo]
  | succ n ih =>
    rcases m with _ | ⟨b, m⟩
    · simp [recsUpTo]
    · have h := ih m
      cases b <;> simp [recsUpTo, h]

theorem concMF : ∀ G S : Bool, ∀ uv ∈ pairs509, ∀ c ∈ recsUpTo 5,
    (run (tick509ExF ++ tick510ExF) c ⟨false, pre509 G S uv.1 uv.2⟩).phase =
      (run tickMF c ⟨false, pre509 G S uv.1 uv.2⟩).phase ∧
    ∀ q ∈ sitesM,
      (run (tick509ExF ++ tick510ExF) c ⟨false, pre509 G S uv.1 uv.2⟩).basis q =
        (run tickMF c ⟨false, pre509 G S uv.1 uv.2⟩).basis q := by
  decide +kernel

theorem concMR : ∀ G S : Bool, ∀ uv ∈ pairs509, ∀ c ∈ recsUpTo 4,
    (run (tick510ExR ++ tick509ExR) c
        ⟨false, (run (tick509ExF ++ tick510ExF) [] ⟨false, pre509 G S uv.1 uv.2⟩).basis⟩).phase =
      (run tickMR c ⟨false, (run (tick509ExF ++ tick510ExF) [] ⟨false, pre509 G S uv.1 uv.2⟩).basis⟩).phase ∧
    ∀ q ∈ sitesM,
      (run (tick510ExR ++ tick509ExR) c
          ⟨false, (run (tick509ExF ++ tick510ExF) [] ⟨false, pre509 G S uv.1 uv.2⟩).basis⟩).basis q =
        (run tickMR c ⟨false, (run (tick509ExF ++ tick510ExF) [] ⟨false, pre509 G S uv.1 uv.2⟩).basis⟩).basis q := by
  decide +kernel

theorem pack509_nil : History5.packAfter base 509 = [] := by decide +kernel
theorem decode509_nil : History5.decodeBefore base 509 = [] := by decide +kernel

attribute [local irreducible] run W.compactSkywalkStageVirtual SkywalkTrace.next Nat.iterate
  W.compactSkywalkTick History5.encodePrefix

/-- The tick-`510` history and the carry site exchanged by `OB5.sig 510` are clean
on the compressed stage before tick `509`. -/
theorem stage509_clean (x : Nat) (s : State)
    (stage : W.CompressedCompactStage5 base x p 509 s.basis) :
    s.basis (base 1538) = false ∧ s.basis (base 1543) = false := by
  obtain ⟨raw, hraw, hbits⟩ := stage
  have fields := (W.compactSkywalkStage_fields_iff base _ 509 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨-, -, -, -, future, carry, -, -, -⟩ := fields
  have k1 := StackOB5Base.prefix_keep 509 (by omega) raw 1538 (by omega)
  have k2 := StackOB5Base.prefix_keep 509 (by omega) raw 1543 (by omega)
  rw [hbits, k1, k2]
  exact ⟨(future 510 (by omega) (by omega)).2,
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1543, by simp, rfl⟩)⟩

/-- The compressed stage before tick `509` pins the fourteen merged wires. -/
theorem stage509_bitsM (x : Nat) (hx0 : 0 < x) (hx : x < p) (s : State)
    (stage : W.CompressedCompactStage5 base x p 509 s.basis) :
    ∃ G S : Bool, ∃ uv ∈ pairs509, ∀ q ∈ sitesM, s.basis q = pre509 G S uv.1 uv.2 q := by
  obtain ⟨G, S, uv, huv, bits⟩ := stage509_bits x hx0 hx s stage
  have cl := stage509_clean x s stage
  refine ⟨G, S, uv, huv, ?_⟩
  intro q hq
  by_cases h : q = 1554
  · subst h
    exact cl.1
  · apply bits q
    simp only [sitesM, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | exact absurd rfl h | decide

/-- Forward ticks `509` and `510` on a compressed stage state are the merged block. -/
theorem tickMF_forced (x : Nat) (hx0 : 0 < x) (hx : x < p) (t : State)
    (ht : W.CompressedCompactStage5 base x p 509 t.basis) (m : List Bool) :
    run tickMF m t = run (W.repairedTick base 509 ++ W.repairedTick base 510) m t := by
  obtain ⟨G, S, uv, huv, bits⟩ := stage509_bitsM x hx0 hx t ht
  rw [tick509ExF_explicit, tick510ExF_explicit]
  symm
  exact forced_eqN (tick509ExF ++ tick510ExF) tickMF sitesM (pre509 G S uv.1 uv.2) 5 (recsUpTo 5)
    (take_recsUpTo 5) pairF_wires tickMF_wires (le_of_eq tickM_counts.2.2.2.1) (le_of_eq tickM_counts.2.1)
    (fun c hc => concMF G S uv huv c hc) t bits m

/-- After ticks `509`, `510` and the pack, decoding and the merged reverse block agree
with decoding and the original reverse ticks `510`, `509`. -/
theorem blockM_eq (x : Nat) (hx0 : 0 < x) (hx : x < p) (t : State)
    (ht : W.CompressedCompactStage5 base x p 509 t.basis) (m1 m2 : List Bool) :
    run (History5.decodeBefore base 510 ++ tickMR) m2
        (run ((W.repairedTick base 509 ++ W.repairedTick base 510) ++ History5.packAfter base 510) m1 t) =
      run (History5.decodeBefore base 510 ++
          (W.ReverseCarry.compactReceiverTick base 510 ++ W.ReverseCarry.compactReceiverTick base 509)) m2
        (run ((W.repairedTick base 509 ++ W.repairedTick base 510) ++ History5.packAfter base 510) m1 t) := by
  obtain ⟨hp0, hpo, hp, cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  obtain ⟨G, S, uv, huv, bits⟩ := stage509_bitsM x hx0 hx t ht
  have due : History5.packDue 510 = true := by decide
  have rep : W.repairedTick base 510 = W.compactSkywalkTick base 510 := by
    rw [tick510ExF_explicit, tick510ExF_compact]
  set k := measurementCount (W.repairedTick base 509 ++ W.repairedTick base 510) with hk
  set k9 := measurementCount (W.repairedTick base 509) with hk9
  set d := measurementCount (History5.decodeBefore base 510) with hd
  set b := run (W.repairedTick base 509) ((m1.take k).take k9) t with hb
  set a := run (W.repairedTick base 509 ++ W.repairedTick base 510) (m1.take k) t with ha
  have bStage : W.CompressedCompactStage5 base x p 510 b.basis := by
    have h := (Stack5.step_spec base base_pool_nodup StackOB5.historyAbove x p 509 hp0 hx0 hpo hp hpGap hx
      cop (by omega) t ((m1.take k).take k9) ht).2
    rw [pack509_nil, List.append_nil] at h
    exact h
  have aSplit : a = run (W.repairedTick base 510) ((m1.take k).drop k9) b := by
    rw [ha, hb, run_append, ← hk9]
  have legal := Stack5.tick_pack_legal base base_pool_nodup x p 510 hp0 hx0 hpo hp hpGap hx cop
    (by omega) b ((m1.take k).drop k9) bStage due
  rw [← rep, ← aSplit] at legal
  have dp : run (History5.decodeBefore base 510) (m2.take d)
      (run (History5.packAfter base 510) (m1.drop k) a) = a := by
    simpa only [History5.packAfter, History5.decodeBefore, due, if_true, History5.encode,
      History5.decode] using
      MeasuredCodec5.roundtripAt (History5.historyMap base (510-5))
        (History5.historyMap_injective base base_pool_nodup (510-5) (by omega)) a (m1.drop k)
        (m2.take d) legal
  have abits : ∀ q ∈ sitesM, a.basis q =
      (run (tick509ExF ++ tick510ExF) [] ⟨false, pre509 G S uv.1 uv.2⟩).basis q := by
    intro q hq
    rw [ha, tick509ExF_explicit, tick510ExF_explicit,
      site_run (tick509ExF ++ tick510ExF) sitesM pairF_wires t ⟨false, pre509 G S uv.1 uv.2⟩ bits
        (m1.take k) q hq]
    exact congrFun (run_basis_records (tick509ExF ++ tick510ExF) _ _ (m1.take k) [] rfl) q
  rw [run_append (W.repairedTick base 509 ++ W.repairedTick base 510),
    run_append (History5.decodeBefore base 510) tickMR,
    run_append (History5.decodeBefore base 510), ← hk, ← hd, ← ha, dp,
    tick510ExR_explicit, tick509ExR_explicit]
  symm
  exact forced_eqN (tick510ExR ++ tick509ExR) tickMR sitesM _ 4 (recsUpTo 4) (take_recsUpTo 4)
    pairR_wires tickMR_wires (le_of_eq tickM_counts.2.2.2.2.2.2.2) (le_of_eq tickM_counts.2.2.2.2.2.1)
    (fun c hc => concMR G S uv huv c hc) a abits (m2.drop d)

end ECDSAAdd.Entrant
end

/-! ### Record counts of the merged blocks against the original tick programs -/
section
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1

theorem tickMF_records : measurementCount tickMF=
    measurementCount (W.repairedTick base 509)+measurementCount (W.repairedTick base 510) := by
  obtain ⟨_,c2,_,c4,_,_,_,_⟩ := tickM_counts
  rw [tick509ExF_explicit,tick510ExF_explicit,←measurementCount_append,c2,c4]

theorem tickMR_records : measurementCount tickMR=
    measurementCount (W.ReverseCarry.compactReceiverTick base 510)+
      measurementCount (W.ReverseCarry.compactReceiverTick base 509) := by
  obtain ⟨_,_,_,_,_,c6,_,c8⟩ := tickM_counts
  rw [tick510ExR_explicit,tick509ExR_explicit,←measurementCount_append,c6,c8]

end ECDSAAdd.Entrant
end
