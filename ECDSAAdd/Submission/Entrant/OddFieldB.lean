import ECDSAAdd.Submission.Entrant.OddField

/-! # Odd-word field replay, part (module split of OddField for replay) -/

-- file-level opens of OddField
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic MappedCompressed
open StairRestSupport ArchiveFieldScratch StairArchiveRelease

section

-- ============================================================================
-- Section 4: Odd-word division endpoint (`CompareDecoderOdd`)
--   Hosts all 44 `exclusiveHoles` on already-erased `R[13..56]` during
--   `window760Odd 0`, saving 44 T, 44 M, and 266 gateSlots vs `cellDecoderLoan`.
-- ============================================================================
section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.OddFullPass.CompareDecoderOdd
open Arithmetic Challenge RecordedQuantum MappedCompressed Secp256k1 BalancedField
open TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse
open CompareDecoder CompareDecoder.BoundaryLoan

/-- Minimal degree-<=2 ANF polynomials for bits `j = 0..5` on `oddWord`
    (`j = 0` evaluated after `[.X (L.R 0)]`). Bits `6..12` reuse
    `CompareDecoder.comparePolys` verbatim; bits `13..255` reuse
    `DirectDecoder.middle`, `highBlock`, and `upper` verbatim. -/
def lowPolysOdd : List Polynomial := [[[1], [14], [15]], [[15], [1, 2], [2, 14], [2, 15], [2, 20], [15, 20]], [[1], [3], [1, 14], [2, 21], [14, 21]], [[2], [4], [2, 3], [2, 14], [2, 22], [3, 22], [14, 22]], [[3], [5], [15], [3, 4], [3, 14], [3, 23], [4, 23], [14, 23]], [[4], [6], [15], [4, 5], [4, 14], [4, 15], [4, 24], [5, 24], [14, 24], [17], [15, 24]]]

/-- The 44 `R`-register wires (`R[13..56]`) already erased to `false` by
    `upper ++ highBlock ++ middle` before the comparison window runs. -/
def rHosts44 : List Wire := (List.range' 13 44).map fixedLayout.R

def frontFastOdd (L : DecoderLayout) : Program :=
  normalize L ++ [.CX (L.R 0) L.h, .CX (L.Y 0) L.h, .CX L.sigma L.h, .X L.h]

def correctionsOdd (L : DecoderLayout) (j : Nat) : List Correction :=
  if j < 6 then correctionsFor (initialWires L) (lowPolysOdd.getD j [])
  else correctionsFor (compareWires L) (comparePolys.getD (j - 6) [])

/-- Erase `R[12..1]` in descending order, then flip `R[0]` and erase `R[0]`. -/
def lowEraseOdd (L : DecoderLayout) : Program :=
  eraseRange (fun i => L.R (1 + i)) (fun i => correctionsOdd L (1 + i)) 12 ++
    [.X (L.R 0), .measureX (L.R 0) [] (correctionsOdd L 0)]

def lowBlockOdd (L : DecoderLayout) : Program :=
  andWrap (L.Y 4) L.h L.bias (lowEraseOdd L)

/-- Lower comparison ladder with `cin = fixedLayout.bias` (clean `false` before
    and after `lowBlockOdd`, so the threshold is uniform `y_norm >= K`). -/
def headLOdd : List StairLoan.CarryLayer :=
  ((StairLoan.mappedLayers borrowBits (xs ++ [fixedLayout.bias]) cs fixedLayout.bias).map
    (fun l => { l with finish := [] })).take 11

def top760Odd : Program :=
  notRegister xs ++ lowLive.map (fun q => .X q) ++ lowBlockOdd fixedLayout ++
    lowLive.map (fun q => .X q) ++
    [.X fixedLayout.sigma, .CX fixedLayout.sigma fixedLayout.h,
      .measureX fixedLayout.h [] [.CZ fixedLayout.sigma (fixedLayout.carry.getLastD fixedLayout.bias)]] ++
    notRegister xs

/-- Unloaned odd comparison window (depth 0; all 44 `exclusiveHoles` hosted on `rHosts44`). -/
def window760Odd0 : Program :=
  notRegister xs ++ StairLoan.emitUps headLOdd ++
    StairLoan.emitSweep tailL top760Odd ++
    StairLoan.emitDowns headLOdd ++ notRegister xs

def cellDecoderOddLoan : Program :=
  frontFastOdd fixedLayout ++ upper fixedLayout ++ DirectDecoder.highBlock fixedLayout ++
    DirectDecoder.middle fixedLayout ++
    StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0 ++
    [.X fixedLayout.sigma] ++ restoreSource fixedLayout ++ copySource fixedLayout

def endPacket760DivOddLoan : Program := k5Wrap cellDecoderOddLoan

/-- Flat decomposition of `cellDecoderOddLoan` without `rebindMany`. -/
def k5PreOdd : Program :=
  frontFastOdd fixedLayout ++ upper fixedLayout ++ DirectDecoder.highBlock fixedLayout ++
    DirectDecoder.middle fixedLayout

def k5SufOdd : Program :=
  [.X fixedLayout.sigma] ++ restoreSource fixedLayout ++ copySource fixedLayout

def k5FlatOdd : Program := k5PreOdd ++ window760Odd0 ++ k5SufOdd

theorem cellDecoderOddLoan_k5 : cellDecoderOddLoan = k5PreOdd ++
    StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0 ++ k5SufOdd := by
  simp only [cellDecoderOddLoan, k5PreOdd, k5SufOdd, List.append_assoc]

/-- One folded kernel pass proves exact counts (257 T, 514 M — saving 44 T and 44 M),
    exact gateSlots (5971 — saving 266 slots), and complete `GatePhysical`. -/
theorem k5FlatOdd_facts :
    toffoliCount k5FlatOdd = 257 ∧ measurementCount k5FlatOdd = 514 ∧
      gateSlots k5FlatOdd = 5972 ∧ k5FlatOdd.all CodecBitSliceVerify.physicalCheck = true := by
  simp only [k5FlatOdd, k5PreOdd, k5SufOdd, window760Odd0, StairLoan.emitSweep,
    toffoliCount_append, measurementCount_append, gateSlots_append, List.all_append,
    k5_tc_downs, k5_mc_downs, k5_gs_downs, k5_downs_all]
  decide +kernel

theorem cellDecoderOddLoan_facts :
    toffoliCount cellDecoderOddLoan = 257 ∧ measurementCount cellDecoderOddLoan = 514 ∧
      gateSlots cellDecoderOddLoan = 5972 ∧ GatePhysical cellDecoderOddLoan := by
  obtain ⟨t, m, g, p⟩ := k5FlatOdd_facts
  have rc := StairLoan.rebindMany_counts StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0
  have rs := k5_rebind_slots StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0
  have pp := CodecBitSliceVerify.physical_of_check _ p
  unfold k5FlatOdd at t m g pp
  simp only [toffoliCount_append, measurementCount_append, gateSlots_append] at t m g
  simp only [gatePhysical_append] at pp
  rw [cellDecoderOddLoan_k5]
  simp only [toffoliCount_append, measurementCount_append, gateSlots_append,
    gatePhysical_append, rc.1, rc.2, rs]
  refine ⟨by omega, by omega, by omega, ?_⟩
  exact ⟨⟨pp.1.1, StairLoan.rebindMany_physical _ _ _ pp.1.2⟩, pp.2⟩

theorem endPacket760DivOddLoan_counts :
    toffoliCount endPacket760DivOddLoan + 44 = toffoliCount endPacket760DivLoan ∧
    measurementCount endPacket760DivOddLoan + 44 = measurementCount endPacket760DivLoan := by
  obtain ⟨t, m, -, -⟩ := cellDecoderOddLoan_facts
  obtain ⟨t0, m0, -, -⟩ := cellDecoderLoan_facts
  rw [endPacket760DivOddLoan, endPacket760DivLoan_k5]
  have h := k5Wrap_counts cellDecoderLoan cellDecoderOddLoan 44 (by omega) (by omega)
  exact ⟨by omega, by omega⟩

theorem endPacket760DivOddLoan_slots_le :
    gateSlots endPacket760DivOddLoan ≤ gateSlots endPacket760DivLoan := by
  obtain ⟨-, -, g, -⟩ := cellDecoderOddLoan_facts
  obtain ⟨-, -, g0, -⟩ := cellDecoderLoan_facts
  rw [endPacket760DivOddLoan, endPacket760DivLoan_k5]
  simpa only [Nat.add_zero] using k5Wrap_slots cellDecoderOddLoan cellDecoderLoan 0 (by omega)

theorem endPacket760DivOddLoan_physical : GatePhysical endPacket760DivOddLoan :=
  k5Wrap_physical cellDecoderOddLoan cellDecoderOddLoan_facts.2.2.2

attribute [local irreducible] wires

private theorem eraseRange_mem (f : Nat → Wire) (c : Nat → List Correction) (n k : Nat) (hk : k < n) :
    f k ∈ wires (eraseRange f c n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [eraseRange, wires_append, Finset.mem_union]
    by_cases ke : k = n
    · subst ke
      left
      rw [OddFullPass.mem_wires_iff_flatMap]
      simp [OddFullPass.instrWiresList]
    · exact Or.inr (ih (by omega))

theorem rHosts44_in_record : ∀ q ∈ rHosts44, q ∈ wires CompareDecoder.cellDecoderNext := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  have hib := List.mem_range'_1.mp hi
  unfold CompareDecoder.cellDecoderNext
  apply CompareDecoder.BoundaryLoan.Inclusion.mem_nine
  by_cases h1 : i < 32
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    unfold DirectDecoder.middle
    rw [show i = 13 + (i - 13) by omega]
    exact eraseRange_mem (fun k => fixedLayout.R (13 + k)) _ 19 (i - 13) (by omega)
  · by_cases h2 : i < 36
    · refine Or.inr (Or.inr (Or.inl ?_))
      unfold DirectDecoder.highBlock DirectDecoder.highErase andWrap
      simp only [wires_append, Finset.mem_union]
      refine Or.inl (Or.inr ?_)
      rw [show i = 32 + (i - 32) by omega]
      exact eraseRange_mem (fun k => fixedLayout.R (32 + k)) _ 4 (i - 32) (by omega)
    · refine Or.inr (Or.inl ?_)
      unfold DirectDecoder.upper
      rw [show i = 36 + (i - 36) by omega]
      exact eraseRange_mem (fun k => fixedLayout.R (36 + k)) _ 220 (i - 36) (by omega)

private theorem bias_in_record : fixedLayout.bias ∈ wires CompareDecoder.cellDecoderNext := by
  unfold CompareDecoder.cellDecoderNext
  apply CompareDecoder.BoundaryLoan.Inclusion.mem_nine
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
  rw [OddFullPass.mem_wires_iff_flatMap]
  decide +kernel

private theorem lowBlockOdd_in_record :
    ∀ q ∈ wires (lowBlockOdd fixedLayout), q ∈ wires CompareDecoder.cellDecoderNext := by
  have hsub : ((lowBlockOdd fixedLayout).flatMap OddFullPass.instrWiresList).all
      (fun q => decide (q ∈ (CompareDecoder.lowBlock fixedLayout).flatMap OddFullPass.instrWiresList)) = true := by
    decide +kernel
  intro q hq
  rw [OddFullPass.mem_wires_iff_flatMap] at hq
  have hmem : q ∈ wires (CompareDecoder.lowBlock fixedLayout) :=
    (OddFullPass.mem_wires_iff_flatMap _ q).mpr (of_decide_eq_true (List.all_eq_true.mp hsub q hq))
  unfold CompareDecoder.cellDecoderNext
  exact CompareDecoder.BoundaryLoan.Inclusion.mem_nine
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmem))))))

private theorem headLOdd_in_record :
    (∀ q ∈ wires (StairLoan.emitUps headLOdd), q ∈ wires CompareDecoder.cellDecoderNext) ∧
    (∀ q ∈ wires (StairLoan.emitDowns headLOdd), q ∈ wires CompareDecoder.cellDecoderNext) := by
  have hup : ((StairLoan.emitUps headLOdd).flatMap OddFullPass.instrWiresList).all
      (fun q => decide (q ∈ xs ∨ q ∈ cs ∨ q = fixedLayout.bias)) = true := by
    decide +kernel
  have hdn : ((StairLoan.emitDowns headLOdd).flatMap OddFullPass.instrWiresList).all
      (fun q => decide (q ∈ xs ∨ q ∈ cs ∨ q = fixedLayout.bias)) = true := by
    decide +kernel
  have lift : ∀ P : Program, (P.flatMap OddFullPass.instrWiresList).all
      (fun q => decide (q ∈ xs ∨ q ∈ cs ∨ q = fixedLayout.bias)) = true →
      ∀ q ∈ wires P, q ∈ wires CompareDecoder.cellDecoderNext := by
    intro P hp q hq
    rw [OddFullPass.mem_wires_iff_flatMap] at hq
    rcases of_decide_eq_true (List.all_eq_true.mp hp q hq) with hx | hc | hb
    · exact CompareDecoder.BoundaryLoan.Inclusion.ladder_in_record q (Or.inl hx)
    · exact CompareDecoder.BoundaryLoan.Inclusion.ladder_in_record q (Or.inr (Or.inl hc))
    · subst hb; exact bias_in_record
  exact ⟨lift _ hup, lift _ hdn⟩

private theorem top760Odd_in_record :
    ∀ q ∈ wires top760Odd, q ∈ wires CompareDecoder.cellDecoderNext := by
  intro q hq
  unfold top760Odd at hq
  simp only [wires_append, Finset.mem_union, or_assoc] at hq
  rcases hq with hn | hl | hb | hl' | hk | hn'
  · exact CompareDecoder.BoundaryLoan.Inclusion.ladder_in_record q
      (Or.inl (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn))
  · have h : q ∈ (cs.drop 5).take 6 := CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hl
    exact CompareDecoder.BoundaryLoan.Inclusion.ladder_in_record q
      (Or.inr (Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take h))))
  · exact lowBlockOdd_in_record q hb
  · have h : q ∈ (cs.drop 5).take 6 := CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hl'
    exact CompareDecoder.BoundaryLoan.Inclusion.ladder_in_record q
      (Or.inr (Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take h))))
  · have hlast : fixedLayout.carry.getLastD fixedLayout.bias = fixedLayout.carry.getLastD (fixedLayout.Y 255) := by
      decide +kernel
    rw [hlast] at hk
    unfold CompareDecoder.cellDecoderNext
    apply CompareDecoder.BoundaryLoan.Inclusion.mem_nine
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
    unfold CompareDecoder.cmpBack
    apply CompareDecoder.BoundaryLoan.Inclusion.mem_four
    right; left
    rw [OddFullPass.mem_wires_iff_flatMap] at hk ⊢
    simp only [List.flatMap_cons, List.mem_append] at hk ⊢
    exact Or.inr hk
  · exact CompareDecoder.BoundaryLoan.Inclusion.ladder_in_record q
      (Or.inl (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn'))

theorem cellDecoderOddLoan_sub :
    wires cellDecoderOddLoan ⊆ wires CompareDecoder.cellDecoderNext := by
  have hwin : ∀ q ∈ wires window760Odd0, q ∈ wires CompareDecoder.cellDecoderNext := by
    intro q hq
    unfold window760Odd0 StairLoan.emitSweep at hq
    simp only [wires_append, Finset.mem_union, or_assoc] at hq
    rcases hq with hn | hu | tu | tt | td | hd | hn'
    · exact CompareDecoder.BoundaryLoan.Inclusion.ladder_in_record q
        (Or.inl (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn))
    · exact headLOdd_in_record.1 q hu
    · exact CompareDecoder.BoundaryLoan.Inclusion.ladder_in_record q
        (CompareDecoder.BoundaryLoan.Inclusion.ups_ladder tailL
          CompareDecoder.BoundaryLoan.Inclusion.tail_ladder q tu)
    · exact top760Odd_in_record q tt
    · exact CompareDecoder.BoundaryLoan.Inclusion.ladder_in_record q
        (CompareDecoder.BoundaryLoan.Inclusion.downs_ladder tailL
          CompareDecoder.BoundaryLoan.Inclusion.tail_ladder q td)
    · exact headLOdd_in_record.2 q hd
    · exact CompareDecoder.BoundaryLoan.Inclusion.ladder_in_record q
        (Or.inl (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn'))
  intro q hq
  unfold cellDecoderOddLoan at hq
  simp only [wires_append, Finset.mem_union, or_assoc] at hq
  rcases hq with h | h | h | h | h | h | h | h
  · unfold frontFastOdd at h
    rw [wires_append, Finset.mem_union] at h
    rcases h with h | h
    · unfold CompareDecoder.cellDecoderNext
      apply CompareDecoder.BoundaryLoan.Inclusion.mem_nine
      left; unfold frontFast; rw [wires_append, Finset.mem_union]; exact Or.inl h
    · rw [OddFullPass.mem_wires_iff_flatMap] at h
      simp only [List.flatMap_cons, List.flatMap_nil, OddFullPass.instrWiresList,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, or_self] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · unfold CompareDecoder.cellDecoderNext
        apply CompareDecoder.BoundaryLoan.Inclusion.mem_nine
        left; unfold frontFast; rw [wires_append, Finset.mem_union]; right
        rw [OddFullPass.mem_wires_iff_flatMap]; simp [OddFullPass.instrWiresList]
      · unfold CompareDecoder.cellDecoderNext
        apply CompareDecoder.BoundaryLoan.Inclusion.mem_nine
        left; unfold frontFast; rw [wires_append, Finset.mem_union]; right
        rw [OddFullPass.mem_wires_iff_flatMap]; simp [OddFullPass.instrWiresList]
      · unfold CompareDecoder.cellDecoderNext
        apply CompareDecoder.BoundaryLoan.Inclusion.mem_nine
        left; unfold frontFast; rw [wires_append, Finset.mem_union]; right
        rw [OddFullPass.mem_wires_iff_flatMap]; simp [OddFullPass.instrWiresList]
      · unfold CompareDecoder.cellDecoderNext
        apply CompareDecoder.BoundaryLoan.Inclusion.mem_nine
        left; unfold frontFast; rw [wires_append, Finset.mem_union]; right
        rw [OddFullPass.mem_wires_iff_flatMap]; simp [OddFullPass.instrWiresList]
      · unfold CompareDecoder.cellDecoderNext
        apply CompareDecoder.BoundaryLoan.Inclusion.mem_nine
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
        unfold CompareDecoder.cmpBack
        apply CompareDecoder.BoundaryLoan.Inclusion.mem_four
        right; left; rw [OddFullPass.mem_wires_iff_flatMap]; simp [OddFullPass.instrWiresList]
      · unfold CompareDecoder.cellDecoderNext
        apply CompareDecoder.BoundaryLoan.Inclusion.mem_nine
        left; unfold frontFast; rw [wires_append, Finset.mem_union]; right
        rw [OddFullPass.mem_wires_iff_flatMap]; simp [OddFullPass.instrWiresList]
  · unfold CompareDecoder.cellDecoderNext
    exact CompareDecoder.BoundaryLoan.Inclusion.mem_nine (Or.inr (Or.inl h))
  · unfold CompareDecoder.cellDecoderNext
    exact CompareDecoder.BoundaryLoan.Inclusion.mem_nine (Or.inr (Or.inr (Or.inl h)))
  · unfold CompareDecoder.cellDecoderNext
    exact CompareDecoder.BoundaryLoan.Inclusion.mem_nine (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · have hrb := OddFullPass.rebindMany_wires_sub StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0 h
    simp only [Finset.mem_union, List.mem_toFinset] at hrb
    rcases hrb with (hw | hr) | hh
    · exact hwin q hw
    · have hholes : StairBoundaryLoan.exclusiveHoles.all (fun w => decide (w ∈ cs)) = true := by decide +kernel
      exact CompareDecoder.BoundaryLoan.Inclusion.ladder_in_record q
        (Or.inr (Or.inl (of_decide_eq_true (List.all_eq_true.mp hholes q hr))))
    · exact rHosts44_in_record q hh
  · unfold CompareDecoder.cellDecoderNext
    apply CompareDecoder.BoundaryLoan.Inclusion.mem_nine
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
    unfold CompareDecoder.cmpBack
    apply CompareDecoder.BoundaryLoan.Inclusion.mem_four
    right; left
    rw [OddFullPass.mem_wires_iff_flatMap] at h ⊢
    simp [OddFullPass.instrWiresList] at h ⊢; tauto
  · unfold CompareDecoder.cellDecoderNext
    exact CompareDecoder.BoundaryLoan.Inclusion.mem_nine
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · unfold CompareDecoder.cellDecoderNext
    exact CompareDecoder.BoundaryLoan.Inclusion.mem_nine
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))

theorem endPacket760DivOddLoan_sub_record :
    wires endPacket760DivOddLoan ⊆ wires (R2SqEp760.endPacket760 true) := by
  rw [endPacket760DivOddLoan, endPacket760_true_k5]
  unfold k5Wrap ControlLoan1589.loanWindow
  exact StairLoanGroupSupport.rename_sub _ _ _
    (StairLoanGroupSupport.rename_sub _ _ _
      (StairLoanGroupSupport.append_sub _ _ _ _
        (StairLoanGroupSupport.append_sub _ _ _ _ (Finset.Subset.refl _)
          (StairLoanGroupSupport.rename_sub _ _ _
            (StairLoanGroupSupport.append_sub _ _ _ _ cellDecoderOddLoan_sub (Finset.Subset.refl _))))
        (Finset.Subset.refl _)))

/-- Kernel-checked verification of `lowPolysOdd` over all 192 reachable 6-bit states
    and of the 14 odd-word bit-4 seed states lying inside `CompareDecoder.states`. -/
private def checkLowOdd : Bool :=
  (List.range 64).all fun y =>
    let yb := (List.range 6).map (fun i => y.testBit i) ++ List.replicate 7 false
    [(false, false), (false, true), (true, false)].all fun (sig, h) =>
      let r := if sig then y else (3 * y + 1 + (if h then 977 else 0)) % 64
      let rb := (List.range 6).map (fun i => r.testBit i) ++ List.replicate 7 false
      let vec := [true] ++ yb ++ [sig, h, false, y.testBit 4 && h, false, false] ++ rb
      (evalPoly (lowPolysOdd.getD 0 []) vec == !(r.testBit 0)) &&
      (List.range' 1 5).all fun j => evalPoly (lowPolysOdd.getD j []) vec == r.testBit j

theorem lowPolysOdd_checked : checkLowOdd = true := by decide +kernel

private def oddSeedIndex (y : Nat) (sig h : Bool) : Nat :=
  let ys := (List.range 4).map (fun i => y.testBit i)
  let ds := (List.range 4).map (fun i => h && (977 : Nat).testBit i)
  let step := ys.zip ds |>.foldl
    (fun (st : Bool × Bool × Bool) (p : Bool × Bool) =>
      let (prev, a, c) := st
      let raw := prev ^^ p.1 ^^ sig ^^ a
      (p.1, carryBit prev (p.1 ^^ sig) a, carryBit p.2 raw c))
    (false, true, false)
  let cmp3 := (cmpSteps ys [true, false, true, true] false).getD 3 false
  (y.testBit 3).toNat + 2 * sig.toNat + 4 * h.toNat +
    8 * step.2.1.toNat + 16 * step.2.2.toNat + 32 * cmp3.toNat

theorem oddSeeds_valid :
    ((List.range 16).all fun y =>
      [(false, false), (false, true), (true, false)].all fun (sig, h) =>
        (2305880426972133179 : Nat).testBit (oddSeedIndex y sig h)) = true := by
  decide +kernel

theorem rHosts44_disjoint :
    (StairBoundaryLoan.exclusiveHoles ++ rHosts44).Nodup ∧
    ∀ q ∈ rHosts44, q ∉ wires window760Odd0 := by
  refine ⟨PeakNodup.nodup_of_mask _ (by decide +kernel), ?_⟩
  have h1 : rHosts44.all (fun q => decide (q ∉ xs ∧ q ∉ cs ∧ q ≠ fixedLayout.bias ∧
      q ∉ (lowBlockOdd fixedLayout).flatMap OddFullPass.instrWiresList ∧
      q ≠ fixedLayout.sigma ∧ q ≠ fixedLayout.h)) = true := by
    decide +kernel
  have hup : ((StairLoan.emitUps headLOdd).flatMap OddFullPass.instrWiresList).all
      (fun w => decide (w ∈ xs ∨ w ∈ cs ∨ w = fixedLayout.bias)) = true := by
    decide +kernel
  have hdn : ((StairLoan.emitDowns headLOdd).flatMap OddFullPass.instrWiresList).all
      (fun w => decide (w ∈ xs ∨ w ∈ cs ∨ w = fixedLayout.bias)) = true := by
    decide +kernel
  have hnc : rHosts44.all (fun w => decide (w ≠ cin)) = true := by decide +kernel
  have hlast : fixedLayout.carry.getLastD fixedLayout.bias ∈ cs := by decide +kernel
  intro q hq hw
  have hd := of_decide_eq_true (List.all_eq_true.mp h1 q hq)
  unfold window760Odd0 StairLoan.emitSweep at hw
  simp only [wires_append, Finset.mem_union, or_assoc] at hw
  rcases hw with hn | hu | tu | tt | td | hd' | hn'
  · exact hd.1 (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn)
  · rw [OddFullPass.mem_wires_iff_flatMap] at hu
    rcases of_decide_eq_true (List.all_eq_true.mp hup q hu) with h | h | h
    · exact hd.1 h
    · exact hd.2.1 h
    · exact hd.2.2.1 h
  · rcases CompareDecoder.BoundaryLoan.Inclusion.ups_ladder tailL
        CompareDecoder.BoundaryLoan.Inclusion.tail_ladder q tu with h | h | h
    · exact hd.1 h
    · exact hd.2.1 h
    · exact of_decide_eq_true (List.all_eq_true.mp hnc q hq) h
  · unfold top760Odd at tt
    simp only [wires_append, Finset.mem_union, or_assoc] at tt
    rcases tt with hn | hl | hb | hl' | hk | hn'
    · exact hd.1 (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn)
    · exact hd.2.1 (List.mem_of_mem_drop (List.mem_of_mem_take (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hl)))
    · exact hd.2.2.2.1 ((OddFullPass.mem_wires_iff_flatMap _ q).mp hb)
    · exact hd.2.1 (List.mem_of_mem_drop (List.mem_of_mem_take (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hl')))
    · rw [OddFullPass.mem_wires_iff_flatMap] at hk
      simp only [List.flatMap_cons, List.flatMap_nil, OddFullPass.instrWiresList,
        OddFullPass.correctionWiresList, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, false_or] at hk
      rcases hk with rfl | (rfl | rfl) | (rfl | rfl | rfl)
      · exact hd.2.2.2.2.1 rfl
      · exact hd.2.2.2.2.1 rfl
      · exact hd.2.2.2.2.2 rfl
      · exact hd.2.2.2.2.2 rfl
      · exact hd.2.2.2.2.1 rfl
      · exact hd.2.1 hlast
    · exact hd.1 (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn')
  · rcases CompareDecoder.BoundaryLoan.Inclusion.downs_ladder tailL
        CompareDecoder.BoundaryLoan.Inclusion.tail_ladder q td with h | h | h
    · exact hd.1 h
    · exact hd.2.1 h
    · exact of_decide_eq_true (List.all_eq_true.mp hnc q hq) h
  · rw [OddFullPass.mem_wires_iff_flatMap] at hd'
    rcases of_decide_eq_true (List.all_eq_true.mp hdn q hd') with h | h | h
    · exact hd.1 h
    · exact hd.2.1 h
    · exact hd.2.2.1 h
  · exact hd.1 (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn')

private theorem rHosts44_in_loan : ∀ q ∈ rHosts44, q ∈ wires cellDecoderLoan := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  have hib := List.mem_range'_1.mp hi
  unfold cellDecoderLoan
  simp only [wires_append, Finset.mem_union, or_assoc]
  by_cases h1 : i < 32
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    unfold DirectDecoder.middle
    rw [show i = 13 + (i - 13) by omega]
    exact eraseRange_mem (fun k => fixedLayout.R (13 + k)) _ 19 (i - 13) (by omega)
  · by_cases h2 : i < 36
    · refine Or.inr (Or.inr (Or.inl ?_))
      unfold DirectDecoder.highBlock DirectDecoder.highErase andWrap
      simp only [wires_append, Finset.mem_union]
      refine Or.inl (Or.inr ?_)
      rw [show i = 32 + (i - 32) by omega]
      exact eraseRange_mem (fun k => fixedLayout.R (32 + k)) _ 4 (i - 32) (by omega)
    · refine Or.inr (Or.inl ?_)
      unfold DirectDecoder.upper
      rw [show i = 36 + (i - 36) by omega]
      exact eraseRange_mem (fun k => fixedLayout.R (36 + k)) _ 220 (i - 36) (by omega)

private theorem rebindMany_mem_fixed (rs hs : List Wire) (P : Program) (q : Wire)
    (h1 : q ∈ wires P) (h2 : q ∉ rs) (h3 : q ∉ hs) :
    q ∈ wires (StairLoan.rebindMany rs hs P) := by
  induction rs generalizing hs with
  | nil => exact h1
  | cons r rs ih =>
    cases hs with
    | nil => exact h1
    | cons hh hs =>
      simp only [StairLoan.rebindMany, renameProgram_support]
      have qr : q ≠ r := fun e => h2 (e ▸ List.mem_cons_self)
      have qh : q ≠ hh := fun e => h3 (e ▸ List.mem_cons_self)
      exact Finset.mem_image.mpr ⟨q, ih hs (fun h => h2 (List.mem_cons_of_mem _ h))
        (fun h => h3 (List.mem_cons_of_mem _ h)), Equiv.swap_apply_of_ne_of_ne qr qh⟩

private theorem loan_core_wires :
    (∀ q ∈ xs, q ∈ wires (window760 44)) ∧
    (∀ q ∈ cs, q ∉ StairBoundaryLoan.exclusiveHoles → q ∈ wires (window760 44)) ∧
    fixedLayout.bias ∈ wires (window760 44) ∧
    fixedLayout.sigma ∈ wires (window760 44) ∧
    fixedLayout.h ∈ wires (window760 44) ∧
    cin ∈ wires (window760 44) := by
  have hxs : ∀ q ∈ xs, q ∈ wires (window760 44) := by
    intro q hq
    unfold window760
    simp only [wires_append, Finset.mem_union, or_assoc]
    left
    rw [notRegister_wires]; exact List.mem_toFinset.mpr hq
  have htop_mem : ∀ q, q ∈ wires top760 → q ∉ StairBoundaryLoan.exclusiveHoles.take 44 →
      q ∉ StairLoan.layerHosts (tailL.take 44) → q ∈ wires (window760 44) := by
    intro q hq hnr hnh
    unfold window760 StairLoan.emitLoan StairLoan.emitSweep
    simp only [wires_append, Finset.mem_union, or_assoc]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    apply rebindMany_mem_fixed _ _ _ q _ hnr hnh
    simp only [wires_append, Finset.mem_union]
    exact Or.inl (Or.inr hq)
  have hbias_top : fixedLayout.bias ∈ wires top760 :=
    (OddFullPass.mem_wires_iff_flatMap _ _).mpr (by decide +kernel)
  have hsig_top : fixedLayout.sigma ∈ wires top760 :=
    (OddFullPass.mem_wires_iff_flatMap _ _).mpr (by decide +kernel)
  have hh_top : fixedLayout.h ∈ wires top760 :=
    (OddFullPass.mem_wires_iff_flatMap _ _).mpr (by decide +kernel)
  have hcin_top : cin ∈ wires top760 :=
    (OddFullPass.mem_wires_iff_flatMap _ _).mpr (by decide +kernel)
  have hbias : fixedLayout.bias ∈ wires (window760 44) :=
    htop_mem _ hbias_top (by decide +kernel) (by decide +kernel)
  have hsig : fixedLayout.sigma ∈ wires (window760 44) :=
    htop_mem _ hsig_top (by decide +kernel) (by decide +kernel)
  have hh : fixedLayout.h ∈ wires (window760 44) :=
    htop_mem _ hh_top (by decide +kernel) (by decide +kernel)
  have hcin : cin ∈ wires (window760 44) :=
    htop_mem _ hcin_top (by decide +kernel) (by decide +kernel)
  have hcs : ∀ q ∈ cs, q ∉ StairBoundaryLoan.exclusiveHoles → q ∈ wires (window760 44) := by
    have hchk : cs.all (fun q =>
        decide (q ∈ StairBoundaryLoan.exclusiveHoles ∨
          q ∈ (StairLoan.emitUps headL).flatMap OddFullPass.instrWiresList ∨
          q ∈ (StairLoan.emitUps (tailL.take 45)).flatMap OddFullPass.instrWiresList ∨
          (q ∈ (StairLoan.emitUps (tailL.drop 45)).flatMap OddFullPass.instrWiresList ∧
           q ∉ StairLoan.layerHosts (tailL.take 44)))) = true := by
      decide +kernel
    intro q hq hnhole
    rcases of_decide_eq_true (List.all_eq_true.mp hchk q hq) with bad | h1 | h2 | ⟨h3, hnh⟩
    · exact absurd bad hnhole
    · unfold window760; simp only [wires_append, Finset.mem_union, or_assoc]
      exact Or.inr (Or.inl ((OddFullPass.mem_wires_iff_flatMap _ q).mpr h1))
    · unfold window760 StairLoan.emitLoan; simp only [wires_append, Finset.mem_union, or_assoc]
      exact Or.inr (Or.inr (Or.inl ((OddFullPass.mem_wires_iff_flatMap _ q).mpr h2)))
    · unfold window760 StairLoan.emitLoan StairLoan.emitSweep
      simp only [wires_append, Finset.mem_union, or_assoc]
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      apply rebindMany_mem_fixed _ _ _ q _
        (fun h => hnhole (List.mem_of_mem_take h)) hnh
      simp only [wires_append, Finset.mem_union]
      exact Or.inl (Or.inl ((OddFullPass.mem_wires_iff_flatMap _ q).mpr h3))
  exact ⟨hxs, hcs, hbias, hsig, hh, hcin⟩

private theorem window760Odd0_sdiff_in_loan :
    ∀ q ∈ wires window760Odd0, q ∉ StairBoundaryLoan.exclusiveHoles → q ∈ wires (window760 44) := by
  have hup : ((StairLoan.emitUps headLOdd).flatMap OddFullPass.instrWiresList).all
      (fun w => decide (w ∈ xs ∨ w ∈ cs ∨ w = fixedLayout.bias)) = true := by decide +kernel
  have hdn : ((StairLoan.emitDowns headLOdd).flatMap OddFullPass.instrWiresList).all
      (fun w => decide (w ∈ xs ∨ w ∈ cs ∨ w = fixedLayout.bias)) = true := by decide +kernel
  have hlbSub : ∀ q ∈ wires (CompareDecoder.lowBlock fixedLayout), q ∈ wires top760 := by
    intro q hq
    simp only [top760, wires_append, Finset.mem_union, hq, true_or, or_true]
  have hlbTop :
      let lbWires := (CompareDecoder.lowBlock fixedLayout).flatMap OddFullPass.instrWiresList
      let hosts44 := StairLoan.layerHosts (tailL.take 44)
      ((lowBlockOdd fixedLayout).flatMap OddFullPass.instrWiresList).all
        (fun w => decide (w ∈ lbWires ∧ w ∉ hosts44)) = true := by
    decide +kernel
  have htop_mem : ∀ q, q ∈ wires top760 → q ∉ StairBoundaryLoan.exclusiveHoles →
      q ∉ StairLoan.layerHosts (tailL.take 44) → q ∈ wires (window760 44) := by
    intro q hq hnr hnh
    unfold window760 StairLoan.emitLoan StairLoan.emitSweep
    simp only [wires_append, Finset.mem_union, or_assoc]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    apply rebindMany_mem_fixed _ _ _ q _ (fun h => hnr (List.mem_of_mem_take h)) hnh
    simp only [wires_append, Finset.mem_union]
    exact Or.inl (Or.inr hq)
  have hlast : fixedLayout.carry.getLastD fixedLayout.bias ∈ cs := by decide +kernel
  have hcore := loan_core_wires
  intro q hw hnh
  unfold window760Odd0 StairLoan.emitSweep at hw
  simp only [wires_append, Finset.mem_union, or_assoc] at hw
  rcases hw with hn | hu | tu | tt | td | hd' | hn'
  · exact hcore.1 q (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn)
  · rcases of_decide_eq_true (List.all_eq_true.mp hup q ((OddFullPass.mem_wires_iff_flatMap _ q).mp hu)) with h | h | rfl
    · exact hcore.1 q h
    · exact hcore.2.1 q h hnh
    · exact hcore.2.2.1
  · rcases CompareDecoder.BoundaryLoan.Inclusion.ups_ladder tailL
        CompareDecoder.BoundaryLoan.Inclusion.tail_ladder q tu with h | h | rfl
    · exact hcore.1 q h
    · exact hcore.2.1 q h hnh
    · exact hcore.2.2.2.2.2
  · unfold top760Odd at tt
    simp only [wires_append, Finset.mem_union, or_assoc] at tt
    rcases tt with hn | hl | hb | hl' | hk | hn'
    · exact hcore.1 q (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn)
    · exact hcore.2.1 q (List.mem_of_mem_drop (List.mem_of_mem_take (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hl))) hnh
    · have hm := of_decide_eq_true (List.all_eq_true.mp hlbTop q ((OddFullPass.mem_wires_iff_flatMap _ q).mp hb))
      exact htop_mem q (hlbSub q ((OddFullPass.mem_wires_iff_flatMap _ q).mpr hm.1)) hnh hm.2
    · exact hcore.2.1 q (List.mem_of_mem_drop (List.mem_of_mem_take (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hl'))) hnh
    · rw [OddFullPass.mem_wires_iff_flatMap] at hk
      simp only [List.flatMap_cons, List.flatMap_nil, OddFullPass.instrWiresList,
        OddFullPass.correctionWiresList, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, false_or, or_assoc] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hcore.2.2.2.1
      · exact hcore.2.2.2.1
      · exact hcore.2.2.2.2.1
      · exact hcore.2.2.2.2.1
      · exact hcore.2.2.2.1
      · exact hcore.2.1 _ hlast hnh
    · exact hcore.1 q (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn')
  · rcases CompareDecoder.BoundaryLoan.Inclusion.downs_ladder tailL
        CompareDecoder.BoundaryLoan.Inclusion.tail_ladder q td with h | h | rfl
    · exact hcore.1 q h
    · exact hcore.2.1 q h hnh
    · exact hcore.2.2.2.2.2
  · rcases of_decide_eq_true (List.all_eq_true.mp hdn q ((OddFullPass.mem_wires_iff_flatMap _ q).mp hd')) with h | h | rfl
    · exact hcore.1 q h
    · exact hcore.2.1 q h hnh
    · exact hcore.2.2.1
  · exact hcore.1 q (CompareDecoder.BoundaryLoan.Inclusion.mem_map_X _ q hn')

theorem cellDecoderOddLoan_sub_loan :
    wires cellDecoderOddLoan ⊆ wires cellDecoderLoan := by
  have hwin : ∀ q ∈ wires (window760 44), q ∈ wires cellDecoderLoan := by
    intro q hq
    unfold cellDecoderLoan; simp only [wires_append, Finset.mem_union, or_assoc]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq)))))
  have hrb := HalfConvertOdd.rebindMany_wires_sub_erase StairBoundaryLoan.exclusiveHoles rHosts44
    window760Odd0 (by decide) rHosts44_disjoint.1 rHosts44_disjoint.2
  intro q hq
  unfold cellDecoderOddLoan at hq
  simp only [wires_append, Finset.mem_union, or_assoc] at hq
  rcases hq with h | h | h | h | h | h | h | h
  · unfold frontFastOdd at h
    rw [wires_append, Finset.mem_union] at h
    rcases h with h | h
    · unfold cellDecoderLoan; simp only [wires_append, Finset.mem_union, or_assoc]
      left; unfold frontFast; rw [wires_append, Finset.mem_union]; exact Or.inl h
    · rw [OddFullPass.mem_wires_iff_flatMap] at h
      simp only [List.flatMap_cons, List.flatMap_nil, OddFullPass.instrWiresList,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, or_self] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · unfold cellDecoderLoan; simp only [wires_append, Finset.mem_union, or_assoc]
        left; unfold frontFast; rw [wires_append, Finset.mem_union]; right
        rw [OddFullPass.mem_wires_iff_flatMap]; simp [OddFullPass.instrWiresList]
      · exact hwin _ loan_core_wires.2.2.2.2.1
      · unfold cellDecoderLoan; simp only [wires_append, Finset.mem_union, or_assoc]
        left; unfold frontFast; rw [wires_append, Finset.mem_union]; right
        rw [OddFullPass.mem_wires_iff_flatMap]; simp [OddFullPass.instrWiresList]
      · exact hwin _ loan_core_wires.2.2.2.2.1
      · exact hwin _ loan_core_wires.2.2.2.1
      · exact hwin _ loan_core_wires.2.2.2.2.1
  · unfold cellDecoderLoan; simp only [wires_append, Finset.mem_union, or_assoc]
    exact Or.inr (Or.inl h)
  · unfold cellDecoderLoan; simp only [wires_append, Finset.mem_union, or_assoc]
    exact Or.inr (Or.inr (Or.inl h))
  · unfold cellDecoderLoan; simp only [wires_append, Finset.mem_union, or_assoc]
    exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases Finset.mem_union.mp (hrb h) with hs | hr
    · have hsd := Finset.mem_sdiff.mp hs
      exact hwin q (window760Odd0_sdiff_in_loan q hsd.1 (List.mem_toFinset.not.mp hsd.2))
    · exact rHosts44_in_loan q (List.mem_toFinset.mp hr)
  · rw [OddFullPass.mem_wires_iff_flatMap] at h
    simp [OddFullPass.instrWiresList] at h
    subst h; exact hwin _ loan_core_wires.2.2.2.1
  · unfold cellDecoderLoan; simp only [wires_append, Finset.mem_union, or_assoc]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · unfold cellDecoderLoan; simp only [wires_append, Finset.mem_union, or_assoc]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

theorem endPacket760DivOddLoan_wires_sub :
    wires endPacket760DivOddLoan ⊆ wires endPacket760DivLoan := by
  rw [endPacket760DivOddLoan, endPacket760DivLoan_k5]
  unfold k5Wrap ControlLoan1589.loanWindow
  exact StairLoanGroupSupport.rename_sub _ _ _
    (StairLoanGroupSupport.rename_sub _ _ _
      (StairLoanGroupSupport.append_sub _ _ _ _
        (StairLoanGroupSupport.append_sub _ _ _ _ (Finset.Subset.refl _)
          (StairLoanGroupSupport.rename_sub _ _ _
            (StairLoanGroupSupport.append_sub _ _ _ _ cellDecoderOddLoan_sub_loan (Finset.Subset.refl _))))
        (Finset.Subset.refl _)))

/-- Clean-wire rebind drop for `window760Odd0`: once `R[13..56]` (`rHosts44`) have been
    erased to `false` by `upper ++ highBlock ++ middle` and `exclusiveHoles` are clean (`false`),
    the zero-depth `rebindMany` runs identically to `window760Odd0`. -/
theorem window760OddLoan_run_eq (s : State) (m : List Bool)
    (hholes : ∀ q ∈ StairBoundaryLoan.exclusiveHoles, s.basis q = false)
    (hr : ∀ q ∈ rHosts44, s.basis q = false)
    (hrest : ∀ q ∈ StairBoundaryLoan.exclusiveHoles, (run window760Odd0 m s).basis q = false) :
    run (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0) m s =
      run window760Odd0 m s :=
  HalfConvertOdd.rebindMany_run_eq_of_clean StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0
    (by decide) rHosts44_disjoint.1 rHosts44_disjoint.2 s m hholes hr hrest

section
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Arithmetic Challenge MappedCompressed Secp256k1 BalancedField
open TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse DecoderCellCarryMath
open CompareDecoder CompareDecoder.BoundaryLoan OddFullPass CodecBitSliceVerify

private theorem normalize_mc : measurementCount (TerminalGraph.normalize fixedLayout) = 0 := by decide +kernel
private theorem lowBlockOdd_mc : measurementCount (lowBlockOdd fixedLayout) = 14 := by decide +kernel

attribute [local irreducible] run measurementCount

/-! ## Odd-word bit-4 seed certificate for `cin = bias = false` (`!cin = true`) -/

private def oddSeedIndexTrue (y : Nat) (sig h : Bool) : Nat :=
  let ys := (List.range 4).map (fun i => y.testBit i)
  let ds := (List.range 4).map (fun i => h && (977 : Nat).testBit i)
  let step := ys.zip ds |>.foldl
    (fun (st : Bool × Bool × Bool) (p : Bool × Bool) =>
      let (prev, a, c) := st
      let raw := prev ^^ p.1 ^^ sig ^^ a
      (p.1, carryBit prev (p.1 ^^ sig) a, carryBit p.2 raw c))
    (false, true, false)
  let cmp3 := (cmpSteps ys [true, false, true, true] true).getD 3 false
  (y.testBit 3).toNat + 2 * sig.toNat + 4 * h.toNat +
    8 * step.2.1.toNat + 16 * step.2.2.toNat + 32 * cmp3.toNat

private theorem oddSeeds_valid_true :
    ((List.range 16).all fun y =>
      [(false, false), (false, true), (true, false)].all fun (sig, h) =>
        (2305880426972133179 : Nat).testBit (oddSeedIndexTrue y sig h)) = true := by
  decide +kernel

/-! ## Ones'-complement normalization and `frontFastOdd` -/

private theorem regValue_complement_all (xs : List Wire) (b : BasisState) (flag : Bool) :
    regValue xs (fun q => b q ^^ flag) =
      if flag then 2 ^ xs.length - 1 - regValue xs b else regValue xs b := by
  cases flag with
  | false =>
    simp only [Bool.false_eq_true, if_false, Bool.xor_false]
  | true =>
    simp only [if_true]
    induction xs with
    | nil => simp [regValue]
    | cons x xs ih =>
      have hlt : regValue xs b < 2 ^ xs.length := regValue_lt xs b
      have hcons (st : BasisState) : regValue (x :: xs) st = (st x).toNat + 2 * regValue xs st := by
        simp only [regValue, List.foldr_cons]; cases st x <;> rfl
      rw [hcons, hcons, ih, List.length_cons, Nat.pow_succ]
      cases b x <;> simp <;> omega

private theorem regValue_take255_split (L : DecoderLayout) (hw : L.Widths) (b : BasisState) :
    regValue L.y b = regValue (L.y.take 255) b + 2 ^ 255 * (b (L.Y 255)).toNat := by
  have hy := y_split L hw
  conv_lhs => rw [hy]
  rw [regValue_append]
  have hlen : (L.y.take 255).length = 255 := by simp [hw.1]
  have hs1 : regValue [L.Y 255] b = (b (L.Y 255)).toNat := by
    simp only [regValue, List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero]
    cases b (L.Y 255) <;> rfl
  rw [hlen, hs1]

private theorem oddWord_sign_bit (L : DecoderLayout) (hw : L.Widths) (b : BasisState) (Z : Fp)
    (hZ : regValue L.y b = oddWord Z) :
    b (L.Y 255) = decide (oddRep Z < 0) ∧
    regValue (L.y.take 255) b =
      if oddRep Z < 0 then (2 ^ 255 + oddRep Z).toNat else (oddRep Z).toNat := by
  have hsp := regValue_take255_split L hw b
  have hlt : regValue (L.y.take 255) b < 2 ^ 255 := by
    have := regValue_lt (L.y.take 255) b
    simpa [hw.1] using this
  have hbd := oddRep_bounds Z
  unfold OddDomain at hbd
  have hq : q < 2 ^ 255 := by norm_num [q, p]
  rw [hZ] at hsp
  unfold oddWord encodeWord at hsp
  have h256c : ((2 ^ 256 : Nat) : Int) = 2 ^ 256 := by norm_num
  rw [h256c] at hsp
  by_cases hneg : oddRep Z < 0
  · have hmod : (oddRep Z % (2 ^ 256 : Int)).toNat = 2 ^ 255 + (2 ^ 255 + oddRep Z).toNat := by
      have h1 : oddRep Z % (2 ^ 256 : Int) = oddRep Z + 2 ^ 256 := by
        rw [Int.emod_eq_add_self_emod]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      omega
    rw [hmod] at hsp
    have hbit : b (L.Y 255) = true := by
      cases hb : b (L.Y 255)
      · rw [hb] at hsp; simp at hsp; omega
      · rfl
    rw [hbit] at hsp; simp at hsp
    exact ⟨by simp [hneg, hbit], by simp [hneg]; omega⟩
  · have hmod : (oddRep Z % (2 ^ 256 : Int)).toNat = (oddRep Z).toNat := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hmod] at hsp
    have hbit : b (L.Y 255) = false := by
      cases hb : b (L.Y 255)
      · rfl
      · rw [hb] at hsp; simp at hsp; omega
    rw [hbit] at hsp; simp at hsp
    exact ⟨by simp [hneg, hbit], by simp [hneg]; omega⟩

private theorem nat_mod_of_lt_2m (a m : Nat) (h1 : m ≤ a) (h2 : a < 2 * m) :
    a % m = a - m := by
  have h : a = (a - m) + m := by omega
  conv_lhs => rw [h]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem odd_norm_scalar (Y : Fp) (sigma : Bool) :
    let yN := if oddRep Y < 0 then (-oddRep Y - 1).toNat else (oddRep Y).toNat
    let rW := oddWord ((if sigma then 1 else 3) * Y)
    let rN := if oddRep Y < 0 then 2 ^ 256 - 1 - rW else rW
    let K := ((p - 1) / 2) / 3
    let hBit := !sigma && !(decide (yN < K))
    rN = ((if sigma then yN else 3 * yN + 1) + hBit.toNat * (2 ^ 32 + 977)) % 2 ^ 256 := by
  have hY := oddRep_bounds Y
  have hq : q = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by
    norm_num [q, p]
  have hp : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
    norm_num [p]
  have hK : ((p - 1) / 2) / 3 = 19298681539552699237261830834781317975544997444273427339909597334651472445277 := by
    norm_num [p]
  have hR := InverseTailCOdd.resultValueOdd_spec (!sigma) Y
  have hsig : (if !sigma then (3 : Fp) else 1) = (if sigma then 1 else 3) := by
    cases sigma <;> rfl
  rw [hsig] at hR
  dsimp only
  rw [oddWord, ← hR]
  unfold InverseTailCOdd.resultValueOdd InverseTailCOdd.rawValueOdd InverseTailCOdd.reducedFlagOdd encodeWord
  have hthird : InverseTailC.third = ((p - 1) / 2) / 3 := by unfold InverseTailC.third; rw [hq, hp]; decide
  rw [hthird]
  have h256c : ((2 ^ 256 : Nat) : Int) = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by norm_num
  have h256n : (2 ^ 256 : Nat) = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by norm_num
  rw [h256c, h256n]
  unfold OddDomain at hY
  cases sigma
  · simp only [Bool.not_false, Bool.false_eq_true, if_false, if_true, Bool.true_and]
    by_cases hneg : oddRep Y < 0
    · simp only [hneg, if_true]
      by_cases hlt : (-oddRep Y - 1).toNat < ((p - 1) / 2) / 3
      · have hge : ¬ (((p - 1) / 2) / 3 ≤ (-oddRep Y - 1).toNat) := by omega
        simp only [hlt, hge, decide_true, decide_false, Bool.false_eq_true, Bool.not_true,
          Bool.toNat_false, zero_mul, add_zero, if_false]
        have hm : (3 * oddRep Y + 1) % (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) =
            3 * oddRep Y + 1 + 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
        rw [hm, Nat.mod_eq_of_lt (by omega)]; omega
      · have hge : ((p - 1) / 2) / 3 ≤ (-oddRep Y - 1).toNat := by omega
        simp only [hlt, hge, decide_true, decide_false, Bool.false_eq_true, Bool.not_false,
          Bool.toNat_true, one_mul, if_true]
        by_cases hpos : 0 ≤ 3 * oddRep Y + 1 + (p : Int)
        · have hm : (3 * oddRep Y + 1 + (p : Int)) % (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) =
              3 * oddRep Y + 1 + (p : Int) := Int.emod_eq_of_lt (by omega) (by omega)
          rw [hm, Nat.mod_eq_of_lt (by omega)]; omega
        · have hm : (3 * oddRep Y + 1 + (p : Int)) % (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) =
              3 * oddRep Y + 1 + (p : Int) + 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
            rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
          rw [hm, nat_mod_of_lt_2m _ _ (by omega) (by omega)]; omega
    · simp only [hneg, if_false]
      by_cases hlt : (oddRep Y).toNat < ((p - 1) / 2) / 3
      · have hge : ¬ (((p - 1) / 2) / 3 ≤ (oddRep Y).toNat) := by omega
        simp only [hlt, hge, decide_true, decide_false, Bool.false_eq_true, Bool.not_true,
          Bool.toNat_false, zero_mul, add_zero, if_false]
        have hm : (3 * oddRep Y + 1) % (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) =
            3 * oddRep Y + 1 := Int.emod_eq_of_lt (by omega) (by omega)
        rw [hm, Nat.mod_eq_of_lt (by omega)]; omega
      · have hge : ((p - 1) / 2) / 3 ≤ (oddRep Y).toNat := by omega
        simp only [hlt, hge, decide_true, decide_false, Bool.false_eq_true, Bool.not_false,
          Bool.toNat_true, one_mul, if_true]
        by_cases hpos : 0 ≤ 3 * oddRep Y + 1 + -(p : Int)
        · have hm : (3 * oddRep Y + 1 + -(p : Int)) % (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) =
              3 * oddRep Y + 1 + -(p : Int) := Int.emod_eq_of_lt (by omega) (by omega)
          rw [hm, nat_mod_of_lt_2m _ _ (by omega) (by omega)]; omega
        · have hm : (3 * oddRep Y + 1 + -(p : Int)) % (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) =
              3 * oddRep Y + 1 + -(p : Int) + 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
            rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
          rw [hm, Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, if_true, if_false,
      Bool.toNat_false, zero_mul, add_zero]
    by_cases hneg : oddRep Y < 0
    · simp only [hneg, if_true]
      have hm : oddRep Y % (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) =
          oddRep Y + 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
        rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [hm, Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [hneg, if_false]
      have hm : oddRep Y % (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) =
          oddRep Y := Int.emod_eq_of_lt (by omega) (by omega)
      rw [hm, Nat.mod_eq_of_lt (by omega)]

private theorem frontFastOdd_spec (Y : Fp) (sigma : Bool) (s : State) (m : List Bool)
    (ys : regValue fixedLayout.y s.basis = oddWord Y)
    (rs : regValue fixedLayout.r s.basis = oddWord ((if sigma then 1 else 3) * Y))
    (sig : s.basis fixedLayout.sigma = sigma)
    (hc : s.basis fixedLayout.h = false)
    (bc : s.basis fixedLayout.bias = false)
    (cc : ∀ q ∈ fixedLayout.carry, s.basis q = false) :
    let L := fixedLayout
    let f := run (frontFastOdd L) m s
    let yN := regValue (L.y.take 255) f.basis
    let hBit := !sigma && !(decide (yN < ((p - 1) / 2) / 3))
    f.phase = s.phase ∧
    f.basis L.sigma = sigma ∧
    f.basis L.h = hBit ∧
    f.basis L.bias = false ∧
    (∀ q ∈ L.carry, f.basis q = false) ∧
    regValue L.r f.basis =
      ((if sigma then yN else 3 * yN + 1) + hBit.toNat * (2 ^ 32 + 977)) % 2 ^ 256 ∧
    (∀ q, q ∉ L.y.take 255 → q ∉ L.r → q ≠ L.h → f.basis q = s.basis q) ∧
    (∀ q ∈ L.y.take 255, f.basis q = (s.basis q ^^ s.basis (L.Y 255))) := by
  let L := fixedLayout
  have hw := fixed_widths
  have hn := fixed_nodup
  have hnorm0 : measurementCount (TerminalGraph.normalize L) = 0 := normalize_mc
  have hcomp_eq : run (frontFastOdd L) m s =
      run [.CX (L.R 0) L.h, .CX (L.Y 0) L.h, .CX L.sigma L.h, .X L.h] m
        ⟨s.phase, complementBasis (L.Y 255) (L.y.take 255 ++ L.r) s.basis⟩ := by
    unfold frontFastOdd
    rw [run_append, hnorm0, List.take_zero, List.drop_zero, normalize_run L hw hn]
  let nB := complementBasis (L.Y 255) (L.y.take 255 ++ L.r) s.basis
  have hR0h : L.R 0 ≠ L.h := by decide +kernel
  have hY0h : L.Y 0 ≠ L.h := by decide +kernel
  have hSigh : L.sigma ≠ L.h := by decide +kernel
  have htail_eq : run (frontFastOdd L) m s =
      ⟨s.phase, writeBit nB L.h ((((nB L.h ^^ nB (L.R 0)) ^^ nB (L.Y 0)) ^^ nB L.sigma) ^^ true)⟩ := by
    rw [hcomp_eq]
    have hnx : ∀ b : Bool, (!b) = (b ^^ true) := by decide
    have hstep : ∀ (b : BasisState),
        run [.CX (L.R 0) L.h, .CX (L.Y 0) L.h, .CX L.sigma L.h, .X L.h] m ⟨s.phase, b⟩ =
        ⟨s.phase, writeBit b L.h ((((b L.h ^^ b (L.R 0)) ^^ b (L.Y 0)) ^^ b L.sigma) ^^ true)⟩ := by
      intro b
      simp only [run, writeBit]
      apply State.extensionality
      · rfl
      · funext q
        by_cases hq : q = L.h
        · subst hq
          simp only [Function.update_self, Function.update_of_ne hR0h, Function.update_of_ne hY0h,
            Function.update_of_ne hSigh, hnx]
        · simp only [Function.update_of_ne hq]
    exact hstep nB
  have hsign := oddWord_sign_bit L hw s.basis Y ys
  have hnh : nB L.h = false := by
    have hnot : L.h ∉ L.y.take 255 ++ L.r := by decide +kernel
    change (if L.h ∈ L.y.take 255 ++ L.r then _ else s.basis L.h) = false; rw [if_neg hnot, hc]
  have hnsig : nB L.sigma = sigma := by
    have hnot : L.sigma ∉ L.y.take 255 ++ L.r := by decide +kernel
    change (if L.sigma ∈ L.y.take 255 ++ L.r then _ else s.basis L.sigma) = sigma; rw [if_neg hnot, sig]
  have hnbias : nB L.bias = false := by
    have hnot : L.bias ∉ L.y.take 255 ++ L.r := by decide +kernel
    change (if L.bias ∈ L.y.take 255 ++ L.r then _ else s.basis L.bias) = false; rw [if_neg hnot, bc]
  have hyN_eq : regValue (L.y.take 255) nB =
      if oddRep Y < 0 then (-oddRep Y - 1).toNat else (oddRep Y).toNat := by
    have hcongr : regValue (L.y.take 255) nB = regValue (L.y.take 255) (fun q => s.basis q ^^ s.basis (L.Y 255)) := by
      apply regValue_congr; intro q hq
      simp [nB, complementBasis, List.mem_append_left _ hq]
    have hlen : (L.y.take 255).length = 255 := by decide +kernel
    rw [hcongr, regValue_complement_all, hsign.1, hsign.2]
    rw [hlen]
    by_cases hneg : oddRep Y < 0
    · simp only [hneg, decide_true, if_true]
      have hbd := oddRep_bounds Y; unfold OddDomain at hbd
      have hq : q < 2 ^ 255 := by norm_num [q, p]
      have h255n : (2 ^ 255 : Nat) = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by norm_num
      have h255i : (2 ^ 255 : Int) = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by norm_num
      rw [h255n, h255i]; omega
    · simp only [hneg, decide_false, Bool.false_eq_true, if_false]
  have hrN_eq : regValue L.r nB =
      if oddRep Y < 0 then 2 ^ 256 - 1 - oddWord ((if sigma then 1 else 3) * Y)
      else oddWord ((if sigma then 1 else 3) * Y) := by
    have hcongr : regValue L.r nB = regValue L.r (fun q => s.basis q ^^ s.basis (L.Y 255)) := by
      apply regValue_congr; intro q hq
      simp [nB, complementBasis, List.mem_append_right _ hq]
    rw [hcongr, regValue_complement_all, hsign.1, rs, hw.2.1]
    by_cases hneg : oddRep Y < 0 <;> simp [hneg]
  have hsc := odd_norm_scalar Y sigma
  dsimp only at hsc
  rw [← hyN_eq, ← hrN_eq] at hsc
  have hbit0 : nB (L.R 0) = (regValue L.r nB).testBit 0 :=
    ECDSAAdd.Entrant.StairCodec.regValue_getD_testBit L.r 0 0 nB (by rw [hw.2.1]; decide)
  have hy0 : nB (L.Y 0) = (regValue (L.y.take 255) nB).testBit 0 := by
    have h0 : L.Y 0 = (L.y.take 255).getD 0 0 := by decide +kernel
    rw [h0]
    exact ECDSAAdd.Entrant.StairCodec.regValue_getD_testBit (L.y.take 255) 0 0 nB (by decide +kernel)
  have hval : ((((nB L.h ^^ nB (L.R 0)) ^^ nB (L.Y 0)) ^^ nB L.sigma) ^^ true) =
      (!sigma && !(decide (regValue (L.y.take 255) nB < ((p - 1) / 2) / 3))) := by
    rw [hnh, hnsig, hbit0, hy0, hsc]
    have hmod2 : ∀ a : Nat, a.testBit 0 = decide (a % 2 = 1) := by
      intro a; simp [Nat.testBit_zero]
    have hmod256 : ∀ a : Nat, (a % 2 ^ 256) % 2 = a % 2 := fun a =>
      Nat.mod_mod_of_dvd a (by decide : 2 ∣ 2 ^ 256)
    rw [hmod2, hmod2, hmod256]
    have hmod_add : ∀ a b : Nat, (a + b) % 2 = (a % 2 + b % 2) % 2 := fun a b => Nat.add_mod a b 2
    have hmod_mul3 : ∀ a : Nat, (3 * a) % 2 = a % 2 := fun a => by omega
    have h977 : (2 ^ 32 + 977) % 2 = 1 := by decide
    cases sigma <;> cases hlt : decide (regValue (L.y.take 255) nB < ((p - 1) / 2) / 3) <;>
      simp only [Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and, Bool.false_eq_true,
        if_true, if_false, Bool.toNat_true, Bool.toNat_false, zero_mul, one_mul, add_zero,
        Bool.false_xor, Bool.xor_false, Bool.xor_true] <;>
      (have hm2 : regValue (L.y.take 255) nB % 2 = 0 ∨ regValue (L.y.take 255) nB % 2 = 1 := Nat.mod_two_eq_zero_or_one _;
       rcases hm2 with hm2 | hm2 <;> simp [hmod_add, hmod_mul3, h977, hm2])
  have hhy_away : L.h ∉ L.y.take 255 := by decide +kernel
  have hhr_away : L.h ∉ L.r := by decide +kernel
  have hfy : regValue (L.y.take 255) (run (frontFastOdd L) m s).basis = regValue (L.y.take 255) nB := by
    rw [htail_eq]
    apply regValue_congr; intro q hq
    simp [writeBit, show q ≠ L.h from fun e => hhy_away (e ▸ hq)]
  have hfr : regValue L.r (run (frontFastOdd L) m s).basis = regValue L.r nB := by
    rw [htail_eq]
    apply regValue_congr; intro q hq
    simp [writeBit, show q ≠ L.h from fun e => hhr_away (e ▸ hq)]
  dsimp only
  rw [hfy, hfr]
  refine ⟨by rw [htail_eq], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htail_eq]; simp only [writeBit, Function.update_of_ne hSigh]; exact hnsig
  · rw [htail_eq]; simp only [writeBit, Function.update_self]; exact hval
  · rw [htail_eq]; simp only [writeBit, Function.update_of_ne (show L.bias ≠ L.h from by decide +kernel)]; exact hnbias
  · intro q hq
    have hqNeH : q ≠ L.h := fun e => carry_source_away L fixed_nodup L.h (Or.inr (Or.inr (Or.inl rfl))) (e ▸ hq)
    have hqNotY : q ∉ L.y.take 255 := fun hy => carry_source_away L fixed_nodup q (Or.inl (List.mem_of_mem_take hy)) hq
    have hqNotR : q ∉ L.r := fun hr => source_r_away L fixed_nodup q (Or.inr (Or.inl hq)) hr
    have hqNotYR : q ∉ L.y.take 255 ++ L.r := fun hm => (List.mem_append.mp hm).elim hqNotY hqNotR
    rw [htail_eq]; change writeBit nB L.h _ q = false
    refine (Function.update_of_ne hqNeH _ nB).trans ?_
    change (if q ∈ L.y.take 255 ++ L.r then _ else s.basis q) = false; rw [if_neg hqNotYR, cc q hq]
  · exact hsc
  · intro q hqy hqr hqh
    rw [htail_eq]; change writeBit nB L.h _ q = s.basis q
    refine (Function.update_of_ne hqh _ nB).trans ?_
    change (if q ∈ L.y.take 255 ++ L.r then _ else s.basis q) = s.basis q
    rw [if_neg (fun hm => (List.mem_append.mp hm).elim hqy hqr)]
  · intro q hqy
    have hqh : q ≠ L.h := fun e => hhy_away (e ▸ hqy)
    rw [htail_eq]; change writeBit nB L.h _ q = _
    refine (Function.update_of_ne hqh _ nB).trans ?_
    change (if q ∈ L.y.take 255 ++ L.r then s.basis q ^^ s.basis (L.Y 255) else s.basis q) = _
    rw [if_pos (List.mem_append_left _ hqy)]

/-! ## Bit-by-bit odd carry chains -/

private def oddA (L : DecoderLayout) (b : BasisState) : Nat → Bool
  | 0 => b (L.Y 0) ^^ b L.sigma
  | j + 1 => carryBit (b (L.Y j)) (b (L.Y (j + 1)) ^^ b L.sigma) (oddA L b j)

private def oddRaw (L : DecoderLayout) (b : BasisState) : Nat → Bool
  | 0 => b (L.Y 0) ^^ !(b L.sigma)
  | j + 1 => b (L.Y j) ^^ sourceAt L b (j + 1) ^^ b L.sigma ^^ oddA L b j

private def oddCorr (L : DecoderLayout) (b : BasisState) (j : Nat) : Bool :=
  b L.h && (2 ^ 32 + 977 : Nat).testBit j

private def oddB (L : DecoderLayout) (b : BasisState) : Nat → Bool
  | 0 => false
  | j + 1 => carryBit (oddCorr L b j) (oddRaw L b j) (oddB L b j)

private def oddRbit (L : DecoderLayout) (b : BasisState) (j : Nat) : Bool :=
  oddRaw L b j ^^ oddCorr L b j ^^ oddB L b j

private theorem oddA_zero (L : DecoderLayout) (b : BasisState) :
    oddA L b 0 = (b (L.Y 0) ^^ b L.sigma) := rfl
private theorem oddA_succ (L : DecoderLayout) (b : BasisState) (j : Nat) :
    oddA L b (j + 1) = carryBit (b (L.Y j)) (b (L.Y (j + 1)) ^^ b L.sigma) (oddA L b j) := rfl
private theorem oddB_zero (L : DecoderLayout) (b : BasisState) :
    oddB L b 0 = false := rfl
private theorem oddB_succ (L : DecoderLayout) (b : BasisState) (j : Nat) :
    oddB L b (j + 1) = carryBit (oddCorr L b j) (oddRaw L b j) (oddB L b j) := rfl

attribute [local irreducible] oddA oddB

private theorem oddA_sigma_true (L : DecoderLayout) (b : BasisState) (hs : b L.sigma = true) :
    ∀ j, oddA L b j = !(b (L.Y j))
  | 0 => by simp [oddA_zero, hs]
  | j + 1 => by
    rw [oddA_succ, oddA_sigma_true L b hs j, hs]
    cases b (L.Y j) <;> cases b (L.Y (j + 1)) <;> rfl

private theorem oddRaw_sigma_true (L : DecoderLayout) (b : BasisState) (hs : b L.sigma = true) :
    ∀ j, j < 256 → oddRaw L b j = sourceAt L b j
  | 0, _ => by simp [oddRaw, sourceAt, hs]
  | j + 1, _ => by
    rw [oddRaw, oddA_sigma_true L b hs j, hs]
    cases b (L.Y j) <;> cases sourceAt L b (j + 1) <;> rfl

private theorem oddB_h_false (L : DecoderLayout) (b : BasisState) (hh : b L.h = false) :
    ∀ j, oddB L b j = false
  | 0 => oddB_zero L b
  | j + 1 => by simp [oddB_succ, oddCorr, hh, oddB_h_false L b hh j, carryBit]

private theorem bitsSum_lt (f : Nat → Bool) :
    ∀ n, ((List.range n).map (fun j => (f j).toNat * 2 ^ j)).sum < 2 ^ n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, Nat.pow_succ]
    have ih := bitsSum_lt f n
    cases f n <;> simp <;> omega

private theorem bitsSum_testBit (f : Nat → Bool) :
    ∀ n j, j < n → (((List.range n).map (fun i => (f i).toNat * 2 ^ i)).sum).testBit j = f j
  | 0, _, hj => by omega
  | n + 1, j, hj => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have hlt := bitsSum_lt f n
    by_cases hjn : j < n
    · have hdiv : (((List.range n).map (fun i => (f i).toNat * 2 ^ i)).sum + (f n).toNat * 2 ^ n) % 2 ^ n =
          ((List.range n).map (fun i => (f i).toNat * 2 ^ i)).sum := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
      have htb := congrArg (fun x => x.testBit j) hdiv
      dsimp only at htb; rw [Nat.testBit_mod_two_pow, decide_eq_true hjn, Bool.true_and] at htb
      exact htb.trans (bitsSum_testBit f n j hjn)
    · have heq : j = n := by omega
      subst heq
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : (((List.range j).map (fun i => (f i).toNat * 2 ^ i)).sum + (f j).toNat * 2 ^ j) / 2 ^ j = (f j).toNat := by
        rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt hlt, Nat.zero_add]
      rw [hdiv]
      cases f j <;> decide

private theorem regValue_eq_bitsSum (xs : List Wire) (b : BasisState) :
    regValue xs b = ((List.range xs.length).map (fun j => (b (xs.getD j 0)).toNat * 2 ^ j)).sum := by
  induction xs with
  | nil => simp [regValue]
  | cons x xs ih =>
    have hcons : regValue (x :: xs) b = (b x).toNat + 2 * regValue xs b := by
      simp only [regValue, List.foldr_cons]; cases b x <;> rfl
    rw [hcons, ih]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons,
      List.getD_cons_zero, Nat.pow_zero, Nat.mul_one, List.map_map]
    congr 1
    have hmul : ∀ (l : List Nat), 2 * (l.map (fun j => (b (xs.getD j 0)).toNat * 2 ^ j)).sum =
        (l.map (fun j => (b (xs.getD j 0)).toNat * 2 ^ (j + 1))).sum := by
      intro l; induction l with
      | nil => simp
      | cons a l ihl =>
        simp only [List.map_cons, List.sum_cons, Nat.mul_add, ihl, Nat.pow_succ]
        ring
    rw [hmul]; rfl

private theorem range_sum_succ_eq (f : Nat → Nat) (n n1 : Nat) (hn : n1 = n + 1) :
    ((List.range n1).map f).sum = ((List.range n).map f).sum + f n := by
  subst hn
  rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

private theorem oddRaw_succ (L : DecoderLayout) (b : BasisState) (j : Nat) :
    oddRaw L b (j + 1) = (b (L.Y j) ^^ sourceAt L b (j + 1) ^^ b L.sigma ^^ oddA L b j) := rfl

private theorem oddRaw_sum_255 (L : DecoderLayout) (b : BasisState) (hs : b L.sigma = false) :
    ∀ k, k < 255 →
      ((List.range (k + 1)).map (fun j => (oddRaw L b j).toNat * 2 ^ j)).sum +
        (oddA L b k).toNat * 2 ^ (k + 1) =
      ((List.range (k + 1)).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum +
        2 * ((List.range k).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum + 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Nat.zero_add, Nat.add_zero, Nat.pow_zero,
      Nat.mul_one, Nat.pow_one, Nat.mul_zero, oddRaw, oddA_zero, hs, Bool.not_false, Bool.xor_false]
    cases b (L.Y 0) <;> decide
  | succ m ih =>
    intro hk
    have ihm := ih (by omega)
    have hR := range_sum_succ_eq (fun j => (oddRaw L b j).toNat * 2 ^ j) (m + 1) (m + 2) rfl
    have hY1 := range_sum_succ_eq (fun j => (b (L.Y j)).toNat * 2 ^ j) (m + 1) (m + 2) rfl
    have hY0 := range_sum_succ_eq (fun j => (b (L.Y j)).toNat * 2 ^ j) m (m + 1) rfl
    have hbit : (oddRaw L b (m + 1)).toNat + 2 * (oddA L b (m + 1)).toNat =
        (b (L.Y m)).toNat + (b (L.Y (m + 1))).toNat + (oddA L b m).toNat := by
      rw [oddRaw_succ, oddA_succ]
      simp only [sourceAt, hk, if_true, hs, Bool.xor_false]
      have hfa : ∀ x y a : Bool, (x ^^ y ^^ a).toNat + 2 * (carryBit x y a).toNat = x.toNat + y.toNat + a.toNat := by
        decide
      exact hfa (b (L.Y m)) (b (L.Y (m + 1))) (oddA L b m)
    have hp1 : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hp2 : 2 * ((b (L.Y m)).toNat * 2 ^ m) = (b (L.Y m)).toNat * 2 ^ (m + 1) := by
      rw [Nat.pow_succ]; ring
    have hmul : (oddRaw L b (m + 1)).toNat * 2 ^ (m + 1) + (oddA L b (m + 1)).toNat * 2 ^ (m + 1 + 1) =
        (b (L.Y m)).toNat * 2 ^ (m + 1) + (b (L.Y (m + 1))).toNat * 2 ^ (m + 1) + (oddA L b m).toNat * 2 ^ (m + 1) := by
      have h1 := congrArg (fun t => t * 2 ^ (m + 1)) hbit
      rw [hp1]; linarith [h1]
    linarith [ihm, hp2, hmul, hR, hY1, hY0]

private theorem oddRaw_sum_step (L : DecoderLayout) (b : BasisState) (hs : b L.sigma = false)
    (m m1 m2 : Nat) (hm1 : m1 = m + 1) (hm2 : m2 = m + 2)
    (hraw : oddRaw L b m1 = (b (L.Y m) ^^ oddA L b m))
    (hstep : ((List.range m1).map (fun j => (oddRaw L b j).toNat * 2 ^ j)).sum +
        (oddA L b m).toNat * 2 ^ m1 =
        ((List.range m1).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum +
        2 * ((List.range m).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum + 1) :
    ((List.range m2).map (fun j => (oddRaw L b j).toNat * 2 ^ j)).sum % 2 ^ m2 =
      (3 * ((List.range m1).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum + 1) % 2 ^ m2 := by
  subst hm1; subst hm2
  have hy1 := range_sum_succ_eq (fun j => (b (L.Y j)).toNat * 2 ^ j) m (m + 1) rfl
  have hr2 := range_sum_succ_eq (fun j => (oddRaw L b j).toNat * 2 ^ j) (m + 1) (m + 2) rfl
  have hbit : (oddRaw L b (m + 1)).toNat + 2 * (b (L.Y m) && oddA L b m).toNat =
      (b (L.Y m)).toNat + (oddA L b m).toNat := by
    rw [hraw]
    have h2 : ∀ x y : Bool, (x ^^ y).toNat + 2 * (x && y).toNat = x.toNat + y.toNat := by decide
    exact h2 (b (L.Y m)) (oddA L b m)
  have hp1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
  have hp2 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have heq : ((List.range (m + 2)).map (fun j => (oddRaw L b j).toNat * 2 ^ j)).sum +
      (b (L.Y m) && oddA L b m).toNat * 2 ^ (m + 2) =
      3 * ((List.range (m + 1)).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum + 1 := by
    have hmul : (oddRaw L b (m + 1)).toNat * 2 ^ (m + 1) + (b (L.Y m) && oddA L b m).toNat * 2 ^ (m + 2) =
        (b (L.Y m)).toNat * 2 ^ (m + 1) + (oddA L b m).toNat * 2 ^ (m + 1) := by
      have h1 := congrArg (fun t => t * 2 ^ (m + 1)) hbit
      rw [hp2]; linarith [h1]
    have h2p : 2 * ((b (L.Y m)).toNat * 2 ^ m) = (b (L.Y m)).toNat * 2 ^ (m + 1) := by rw [hp1]; ring
    linarith [hstep, hy1, hr2, hmul, h2p]
  rw [← heq, Nat.add_mul_mod_self_right]

private theorem oddRaw_sum_255_eq (L : DecoderLayout) (b : BasisState) (hs : b L.sigma = false)
    (k k1 : Nat) (hk : k < 255) (hk1 : k1 = k + 1) :
    ((List.range k1).map (fun j => (oddRaw L b j).toNat * 2 ^ j)).sum +
      (oddA L b k).toNat * 2 ^ k1 =
    ((List.range k1).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum +
      2 * ((List.range k).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum + 1 := by
  subst hk1
  exact oddRaw_sum_255 L b hs k hk

private theorem oddRaw_succ_eq (L : DecoderLayout) (b : BasisState) (j j1 : Nat) (hj : j1 = j + 1) :
    oddRaw L b j1 = (b (L.Y j) ^^ sourceAt L b j1 ^^ b L.sigma ^^ oddA L b j) := by
  subst hj; exact oddRaw_succ L b j

private theorem hySum_255 (L : DecoderLayout) (hw : L.Widths) (b : BasisState) :
    regValue (L.y.take 255) b =
      ((List.range 255).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum := by
  rw [regValue_eq_bitsSum]
  have hlen : (L.y.take 255).length = 255 := by simp [hw.1]
  rw [hlen]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have hjlt : j < 255 := List.mem_range.mp hj
  have hget : (L.y.take 255).getD j 0 = L.Y j := by
    simp [DecoderLayout.Y, List.getD_eq_getElem, hw.1, hjlt, show j < 256 by omega]
  rw [hget]

private theorem oddRaw_sum_false_gen (L : DecoderLayout) (b : BasisState) (hs : b L.sigma = false)
    (m m1 m2 : Nat) (hm : m = 254) (hm1 : m1 = m + 1) (hm2 : m2 = m + 2) :
    ((List.range m2).map (fun j => (oddRaw L b j).toNat * 2 ^ j)).sum % 2 ^ m2 =
      (3 * ((List.range m1).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum + 1) % 2 ^ m2 := by
  subst hm1; subst hm2
  have hlt : m < 255 := by omega
  have h255 := oddRaw_sum_255 L b hs m hlt
  have hraw : oddRaw L b (m + 1) = (b (L.Y m) ^^ oddA L b m) := by
    rw [oddRaw_succ]
    simp only [sourceAt, show ¬(m + 1 < 255) by omega, if_false, hs, Bool.xor_false]
  exact oddRaw_sum_step L b hs m (m + 1) (m + 2) rfl rfl hraw h255

private theorem oddRaw_sum_256_false (L : DecoderLayout) (b : BasisState) (hs : b L.sigma = false) :
    ((List.range 256).map (fun j => (oddRaw L b j).toNat * 2 ^ j)).sum % 2 ^ 256 =
      (3 * ((List.range 255).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum + 1) % 2 ^ 256 :=
  oddRaw_sum_false_gen L b hs 254 255 256 rfl rfl rfl

private theorem oddRaw_sum_true_gen (L : DecoderLayout) (b : BasisState) (hs : b L.sigma = true)
    (n n1 : Nat) (hn : n = 255) (hn1 : n1 = n + 1) :
    ((List.range n1).map (fun j => (oddRaw L b j).toNat * 2 ^ j)).sum =
      ((List.range n).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum := by
  subst hn1
  rw [range_sum_succ_eq _ n (n + 1) rfl, oddRaw_sigma_true L b hs n (by omega)]
  simp only [sourceAt, show ¬(n < 255) by omega, if_false, Bool.toNat_false, zero_mul, Nat.add_zero]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have hjlt : j < n := List.mem_range.mp hj
  rw [oddRaw_sigma_true L b hs j (by omega)]
  simp only [sourceAt, show j < 255 by omega, if_true]

private theorem oddRaw_sum_256_true (L : DecoderLayout) (b : BasisState) (hs : b L.sigma = true) :
    ((List.range 256).map (fun j => (oddRaw L b j).toNat * 2 ^ j)).sum =
      ((List.range 255).map (fun j => (b (L.Y j)).toNat * 2 ^ j)).sum :=
  oddRaw_sum_true_gen L b hs 255 256 rfl rfl

private theorem oddRaw_sum_256_mod (L : DecoderLayout) (hw : L.Widths) (b : BasisState) :
    ((List.range 256).map (fun j => (oddRaw L b j).toNat * 2 ^ j)).sum % 2 ^ 256 =
      (if b L.sigma then regValue (L.y.take 255) b else 3 * regValue (L.y.take 255) b + 1) % 2 ^ 256 := by
  rw [hySum_255 L hw b]
  cases hs : b L.sigma
  · simp only [Bool.false_eq_true, if_false]
    exact oddRaw_sum_256_false L b hs
  · simp only [if_true]
    rw [oddRaw_sum_256_true L b hs]

private theorem oddRbit_sum (L : DecoderLayout) (b : BasisState) :
    ∀ n, ((List.range n).map (fun j => (oddRbit L b j).toNat * 2 ^ j)).sum + (oddB L b n).toNat * 2 ^ n =
      ((List.range n).map (fun j => (oddRaw L b j).toNat * 2 ^ j)).sum +
      ((List.range n).map (fun j => (oddCorr L b j).toNat * 2 ^ j)).sum
  | 0 => by simp [oddB_zero]
  | n + 1 => by
    have ih := oddRbit_sum L b n
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have hbit : (oddRbit L b n).toNat + 2 * (oddB L b (n + 1)).toNat =
        (oddRaw L b n).toNat + (oddCorr L b n).toNat + (oddB L b n).toNat := by
      have hfa : ∀ r c k : Bool, (r ^^ c ^^ k).toNat + 2 * (carryBit c r k).toNat = r.toNat + c.toNat + k.toNat := by
        decide
      rw [oddRbit, oddB_succ]; exact hfa (oddRaw L b n) (oddCorr L b n) (oddB L b n)
    have hmul : (oddRbit L b n).toNat * 2 ^ n + (oddB L b (n + 1)).toNat * 2 ^ (n + 1) =
        (oddRaw L b n).toNat * 2 ^ n + (oddCorr L b n).toNat * 2 ^ n + (oddB L b n).toNat * 2 ^ n := by
      have h1 := congrArg (fun t => t * 2 ^ n) hbit
      have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hp]; linarith [h1]
    omega

private theorem oddCorr_sum_256 (L : DecoderLayout) (b : BasisState) :
    ((List.range 256).map (fun j => (oddCorr L b j).toNat * 2 ^ j)).sum =
      (b L.h).toNat * (2 ^ 32 + 977) := by
  have hconst : ∀ n, 33 ≤ n →
      ((List.range n).map (fun j => ((2 ^ 32 + 977 : Nat).testBit j).toNat * 2 ^ j)).sum = 2 ^ 32 + 977 := by
    intro n; induction n with
    | zero => intro h; omega
    | succ k ih =>
      intro hk
      by_cases h33 : 33 ≤ k
      · rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ih h33]
        have hlt : 2 ^ 32 + 977 < 2 ^ k := lt_of_lt_of_le (by decide : 2 ^ 32 + 977 < 2 ^ 33)
          (Nat.pow_le_pow_right (by decide : 1 ≤ 2) h33)
        rw [Nat.testBit_eq_false_of_lt hlt]; simp
      · have heq : k + 1 = 33 := by omega
        rw [heq]; decide +kernel
  cases hh : b L.h
  · simp [oddCorr, hh]
  · simp only [oddCorr, hh, Bool.true_and, Bool.toNat_true, one_mul]
    exact hconst 256 (by decide)

private theorem odd_bits_spec (L : DecoderLayout) (hw : L.Widths) (b : BasisState)
    (hscalar : regValue L.r b =
      ((if b L.sigma then regValue (L.y.take 255) b else 3 * regValue (L.y.take 255) b + 1) +
        (b L.h).toNat * (2 ^ 32 + 977)) % 2 ^ 256) :
    ∀ j, j < 256 → b (L.R j) = oddRbit L b j := by
  have hsum := oddRbit_sum L b 256
  have hmod : ((List.range 256).map (fun j => (oddRbit L b j).toNat * 2 ^ j)).sum = regValue L.r b := by
    have hlt := bitsSum_lt (oddRbit L b) 256
    rw [← Nat.mod_eq_of_lt hlt, ← Nat.add_mul_mod_self_right _ (oddB L b 256).toNat (2 ^ 256),
      hsum, Nat.add_mod, oddRaw_sum_256_mod L hw b, oddCorr_sum_256 L b, ← Nat.add_mod, hscalar]
  intro j hj
  rw [DecoderLayout.R, ECDSAAdd.Entrant.StairCodec.regValue_getD_testBit L.r j 0 b (by rw [hw.2.1]; exact hj),
    ← hmod, bitsSum_testBit (oddRbit L b) 256 j hj]

/-! ## `seedValid` and triangular erasure for `upper`, `highBlock`, `middle` -/

private theorem odd_seedValid (L : DecoderLayout) (b : BasisState)
    (hexcl : (b L.sigma && b L.h) = false)
    (j : Nat) (hj1 : 1 ≤ j) (hj : j < 255) (hc : oddCorr L b j = false) :
    seedValid (b (L.Y j)) (b L.sigma) (oddA L b j) (oddB L b (j + 1)) := by
  cases hs : b L.sigma
  · constructor
    · intro h; cases h
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hRaw : oddRaw L b (k + 1) = (b (L.Y k) ^^ b (L.Y (k + 1)) ^^ oddA L b k) := by
        simp [oddRaw, sourceAt, hj, hs]
      have hA : oddA L b (k + 1) = carryBit (b (L.Y k)) (b (L.Y (k + 1))) (oddA L b k) := by
        simp [oddA_succ, hs]
      have hB : oddB L b (k + 2) = (oddRaw L b (k + 1) && oddB L b (k + 1)) := by
        simp [oddB_succ, hc, DecoderCellCarryMath.carry_zero_correction]
      rw [hB, hRaw, hA]
      exact DecoderCellCarryMath.zero_triple (b (L.Y k)) (b (L.Y (k + 1))) (oddA L b k) (oddB L b (k + 1))
  · have hh : b L.h = false := by simp [hs] at hexcl; exact hexcl
    rw [oddA_sigma_true L b hs j, oddB_h_false L b hh (j + 1)]
    exact ⟨fun _ => ⟨rfl, rfl⟩, rfl⟩

private theorem odd_pair (L : DecoderLayout) (hw : L.Widths) (b : BasisState)
    (hbits : ∀ j, j < 256 → b (L.R j) = oddRbit L b j)
    (hexcl : (b L.sigma && b L.h) = false)
    (k : Nat) (hk : 2 ≤ k) (hi : k + 2 ≤ 255)
    (hc0 : oddCorr L b (k - 1) = false) (hc1 : oddCorr L b k = false)
    (hc2 : oddCorr L b (k + 1) = false) (hc3 : oddCorr L b (k + 2) = false) :
    b (L.R (k + 2)) = poly (b (L.Y (k - 1))) (b (L.Y k)) (b (L.Y (k + 1)))
      (sourceAt L b (k + 2)) (b L.sigma) (b (L.R (k + 1))) := by
  have hseed := odd_seedValid L b hexcl (k - 1) (by omega) (by omega) hc0
  have heq : k - 1 + 1 = k := by omega
  rw [heq] at hseed
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hseed hc0 ⊢
  have ha1 : oddA L b (m + 1) = carryBit (b (L.Y m)) (b (L.Y (m + 1)) ^^ b L.sigma) (oddA L b m) := oddA_succ L b m
  have ha2 : oddA L b (m + 2) = carryBit (b (L.Y (m + 1))) (b (L.Y (m + 2)) ^^ b L.sigma) (oddA L b (m + 1)) := oddA_succ L b (m + 1)
  have hb1 : oddB L b (m + 2) = ((b (L.Y m) ^^ b (L.Y (m + 1)) ^^ b L.sigma ^^ oddA L b m) && oddB L b (m + 1)) := by
    have hrk : oddRaw L b (m + 1) = (b (L.Y m) ^^ b (L.Y (m + 1)) ^^ b L.sigma ^^ oddA L b m) := by
      simp [oddRaw, sourceAt, show m + 1 < 255 by omega]
    rw [oddB_succ, hc1, hrk, DecoderCellCarryMath.carry_zero_correction]
  have hb2 : oddB L b (m + 3) = ((b (L.Y (m + 1)) ^^ b (L.Y (m + 2)) ^^ b L.sigma ^^ oddA L b (m + 1)) && oddB L b (m + 2)) := by
    have hrk : oddRaw L b (m + 2) = (b (L.Y (m + 1)) ^^ b (L.Y (m + 2)) ^^ b L.sigma ^^ oddA L b (m + 1)) := by
      simp [oddRaw, sourceAt, show m + 2 < 255 by omega]
    rw [oddB_succ, hc2, hrk, DecoderCellCarryMath.carry_zero_correction]
  have hr1 : b (L.R (m + 2)) = (b (L.Y (m + 1)) ^^ b (L.Y (m + 2)) ^^ b L.sigma ^^ oddA L b (m + 1) ^^ oddB L b (m + 2)) := by
    rw [hbits (m + 2) (by omega), oddRbit, hc2, Bool.xor_false]
    simp [oddRaw, sourceAt, show m + 2 < 255 by omega]
  have hr2 : b (L.R (m + 3)) = (b (L.Y (m + 2)) ^^ sourceAt L b (m + 3) ^^ b L.sigma ^^ oddA L b (m + 2) ^^ oddB L b (m + 3)) := by
    rw [hbits (m + 3) (by omega), oddRbit, hc3, Bool.xor_false]
    simp [oddRaw]
  rw [hr2, hr1, ha2, hb2, ha1, hb1]
  exact pair_identity _ _ _ _ _ _ _ hseed

private theorem oddCorr_false_of_region (L : DecoderLayout) (b : BasisState) (j : Nat)
    (hj : (10 ≤ j ∧ j ≤ 31) ∨ 33 ≤ j) : oddCorr L b j = false := by
  unfold oddCorr
  have hbit : (2 ^ 32 + 977 : Nat).testBit j = false := by
    rcases hj with ⟨hlo, hhi⟩ | h33
    · have : ∀ i : Fin 22, (2 ^ 32 + 977 : Nat).testBit (10 + i.val) = false := by decide +kernel
      have h := this ⟨j - 10, by omega⟩
      simpa only [show 10 + (j - 10) = j by omega] using h
    · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 2 ^ 32 + 977 < 2 ^ 33)
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) h33))
  rw [hbit]; simp

private theorem odd_chunk_eq (L : DecoderLayout) (hw : L.Widths) (b : BasisState)
    (hbits : ∀ j, j < 256 → b (L.R j) = oddRbit L b j) :
    ∀ n off, 1 ≤ off → off + n ≤ 255 →
      chunk ((List.range' off n).map (fun j => b (L.Y j)))
        ((List.range' off n).map (fun j => oddCorr L b j))
        (b (L.Y (off - 1))) (b L.sigma) (oddA L b (off - 1)) (oddB L b off) =
      (List.range' off n).map (fun j => b (L.R j))
  | 0, _, _, _ => rfl
  | n + 1, off, h1, hhi => by
    simp only [List.range'_succ, List.map_cons, chunk]
    have hr : b (L.R off) = ((b (L.Y (off - 1)) ^^ b (L.Y off) ^^ b L.sigma ^^ oddA L b (off - 1)) ^^
        oddCorr L b off ^^ oddB L b off) := by
      rw [hbits off (by omega), oddRbit]
      obtain ⟨m, rfl⟩ : ∃ m, off = m + 1 := ⟨off - 1, by omega⟩
      simp [oddRaw, sourceAt, show m + 1 < 255 by omega]
    have ha : carryBit (b (L.Y (off - 1))) (b (L.Y off) ^^ b L.sigma) (oddA L b (off - 1)) = oddA L b off := by
      obtain ⟨m, rfl⟩ : ∃ m, off = m + 1 := ⟨off - 1, by omega⟩
      exact (oddA_succ L b m).symm
    have hb : carryBit (oddCorr L b off) (b (L.Y (off - 1)) ^^ b (L.Y off) ^^ b L.sigma ^^ oddA L b (off - 1)) (oddB L b off) =
        oddB L b (off + 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, off = m + 1 := ⟨off - 1, by omega⟩
      simp [oddB_succ, oddRaw, sourceAt, show m + 1 < 255 by omega]
    rw [← hr, ha, hb]
    congr 1
    simpa only [Nat.add_sub_cancel] using odd_chunk_eq L hw b hbits n (off + 1) (by omega) (by omega)

private theorem odd_upper_correct (ref : BasisState)
    (hbits : ∀ j, j < 256 → ref (fixedLayout.R j) = oddRbit fixedLayout ref j)
    (hexcl : (ref fixedLayout.sigma && ref fixedLayout.h) = false)
    (s : State) (src : SourceData fixedLayout ref s) (rs : Pending fixedLayout ref 256 s) (m : List Bool) :
    ErasedRange (fun i => fixedLayout.R (36 + i)) 220 s (run (upper fixedLayout) m s) := by
  apply eraseRange_correct
  · intro i hi j hj eq
    have z := result_inj fixedLayout fixed_widths fixed_nodup (36 + i) (36 + j) (by omega) (by omega) eq
    omega
  · intro i hi
    exact poly_r_away fixedLayout fixed_widths fixed_nodup (36 + i) (36 + i) (by omega) (by omega) (by omega) (by omega) _
  · intro i hi j hij hj
    exact poly_r_away fixedLayout fixed_widths fixed_nodup (36 + i) (36 + j) (by omega) (by omega) (by omega) (by omega) _
  · intro i hi
    rw [rs _ (by omega), poly_correction_value,
      src.source (36 + i - 3) (by omega), src.source (36 + i - 2) (by omega),
      src.source (36 + i - 1) (by omega), src.source (36 + i) (by omega), src.sigma, rs _ (by omega)]
    have hp := odd_pair fixedLayout fixed_widths ref hbits hexcl (34 + i) (by omega) (by omega)
      (oddCorr_false_of_region _ _ _ (Or.inr (by omega)))
      (oddCorr_false_of_region _ _ _ (Or.inr (by omega)))
      (oddCorr_false_of_region _ _ _ (Or.inr (by omega)))
      (oddCorr_false_of_region _ _ _ (Or.inr (by omega)))
    have a : 34 + i + 2 = 36 + i := by omega
    have b1 : 34 + i - 1 = 36 + i - 3 := by omega
    have c1 : 34 + i = 36 + i - 2 := by omega
    have d1 : 34 + i + 1 = 36 + i - 1 := by omega
    rw [a, b1, d1, c1] at hp
    simpa only [sourceAt, decide_eq_true_eq] using hp

private theorem odd_middle_correct (ref : BasisState)
    (hbits : ∀ j, j < 256 → ref (fixedLayout.R j) = oddRbit fixedLayout ref j)
    (hexcl : (ref fixedLayout.sigma && ref fixedLayout.h) = false)
    (s : State) (src : SourceData fixedLayout ref s) (rs : Pending fixedLayout ref 32 s) (m : List Bool) :
    ErasedRange (fun i => fixedLayout.R (13 + i)) 19 s (run (middle fixedLayout) m s) := by
  apply eraseRange_correct
  · intro i hi j hj eq
    have z := result_inj fixedLayout fixed_widths fixed_nodup (13 + i) (13 + j) (by omega) (by omega) eq
    omega
  · intro i hi
    exact poly_r_away fixedLayout fixed_widths fixed_nodup (13 + i) (13 + i) (by omega) (by omega) (by omega) (by omega) _
  · intro i hi j hij hj
    exact poly_r_away fixedLayout fixed_widths fixed_nodup (13 + i) (13 + j) (by omega) (by omega) (by omega) (by omega) _
  · intro i hi
    rw [rs _ (by omega), poly_correction_value,
      src.source (13 + i - 3) (by omega), src.source (13 + i - 2) (by omega),
      src.source (13 + i - 1) (by omega), src.source (13 + i) (by omega), src.sigma, rs _ (by omega)]
    have hp := odd_pair fixedLayout fixed_widths ref hbits hexcl (11 + i) (by omega) (by omega)
      (oddCorr_false_of_region _ _ _ (Or.inl ⟨by omega, by omega⟩))
      (oddCorr_false_of_region _ _ _ (Or.inl ⟨by omega, by omega⟩))
      (oddCorr_false_of_region _ _ _ (Or.inl ⟨by omega, by omega⟩))
      (oddCorr_false_of_region _ _ _ (Or.inl ⟨by omega, by omega⟩))
    have a : 11 + i + 2 = 13 + i := by omega
    have b1 : 11 + i - 1 = 13 + i - 3 := by omega
    have c1 : 11 + i = 13 + i - 2 := by omega
    have d1 : 11 + i + 1 = 13 + i - 1 := by omega
    rw [a, b1, d1, c1] at hp
    simpa only [sourceAt, show 13 + i < 255 by omega, if_true] using hp

private def highRootOdd (L : DecoderLayout) (b : BasisState) : Nat := packBits
  [b (L.Y 29), b (L.Y 30), b (L.Y 31), b (L.Y 32), b (L.Y 33), b (L.Y 34), b (L.Y 35),
   b L.sigma, b L.h, oddA L b 29, oddB L b 30]

private theorem odd_highBlock_correct (ref : BasisState)
    (hbits : ∀ j, j < 256 → ref (fixedLayout.R j) = oddRbit fixedLayout ref j)
    (hexcl : (ref fixedLayout.sigma && ref fixedLayout.h) = false)
    (s : State) (src : SourceData fixedLayout ref s) (rs : Pending fixedLayout ref 36 s)
    (clean : s.basis (fixedLayout.A 0) = false) (m : List Bool) :
    ErasedRange (fun i => fixedLayout.R (32 + i)) 4 s (run (DirectDecoder.highBlock fixedLayout) m s) := by
  let L := fixedLayout
  let u := prepared s (L.Y 32) L.h (L.A 0)
  have us : SourceData L ref u := prepared_source L fixed_widths fixed_nodup ref s src _ _ 0 (by decide)
  have ur : Pending L ref 36 u := prepared_pending L fixed_widths fixed_nodup ref s 36 (by decide) rs _ _ 0 (by decide)
  have ua : u.basis (L.A 0) = (ref (L.Y 32) && ref L.h) := by
    change writeBit s.basis (L.A 0) (s.basis (L.Y 32) && s.basis L.h) (L.A 0) = _
    rw [writeBit, Function.update_self, src.source 32 (by decide), src.h]
  apply andWrap_erased
  · exact y_ne_a L fixed_widths fixed_nodup 32 0 (by decide) (by decide)
  · exact h_ne_a L fixed_widths fixed_nodup 0 (by decide)
  · intro i hi; exact y_ne_r L fixed_widths fixed_nodup 32 (32 + i) (by decide) (by omega)
  · intro i hi; exact flag_ne_r L fixed_widths fixed_nodup L.h (Or.inr (Or.inl rfl)) (32 + i) (by omega)
  · intro i hi; exact (r_ne_a L fixed_widths fixed_nodup (32 + i) 0 (by omega) (by decide)).symm
  · exact clean
  · apply eraseRange_correct
    · intro i hi j hj eq
      have z := result_inj L fixed_widths fixed_nodup (32 + i) (32 + j) (by omega) (by omega) eq
      omega
    · intro i hi; exact high_away ⟨i, hi⟩
    · intro i hi j hij hj; exact high_tri ⟨i, hi⟩ ⟨j, hj⟩ hij
    · intro i hi
      rw [ur (32 + i) (by omega), high_correction_value L u.basis ⟨i, hi⟩, highPhysical_eq L ref u us ur ua]
      symm
      have hbd : highRootOdd L ref < 2048 := by
        have h := pack_bound [ref (L.Y 29), ref (L.Y 30), ref (L.Y 31), ref (L.Y 32), ref (L.Y 33),
          ref (L.Y 34), ref (L.Y 35), ref L.sigma, ref L.h, oddA L ref 29, oddB L ref 30]
        norm_num only [List.length_cons, List.length_nil] at h; exact h
      have hval : highValid (highRootOdd L ref) = true := by
        have hseed := odd_seedValid L ref hexcl 29 (by decide) (by decide)
          (oddCorr_false_of_region L ref 29 (Or.inl ⟨by decide, by decide⟩))
        have hnd : (oddA L ref 29 && oddB L ref 30 && !(ref L.h)) = false := by
          cases hh : ref L.h
          · rw [oddB_h_false L ref hh 30]; simp
          · simp
        simp only [highValid, highRootOdd, CodecBitSliceVerify.pack_testBit]
        change (!(ref L.sigma && ref L.h) && seedOK (ref (L.Y 29)) (ref L.sigma) (oddA L ref 29) (oddB L ref 30) &&
          !(oddA L ref 29 && oddB L ref 30 && !(ref L.h))) = true
        simp only [Bool.and_eq_true, Bool.not_eq_true', seedOK_iff]
        exact ⟨⟨hexcl, hseed⟩, hnd⟩
      have hres : highRs (highRootOdd L ref) = (List.range' 30 6).map (fun j => ref (L.R j)) := by
        have hch := odd_chunk_eq L fixed_widths ref hbits 6 30 (by decide) (by decide)
        have hc30 : (List.range' 30 6).map (fun j => oddCorr L ref j) = [false, false, ref L.h, false, false, false] := by
          have hb30 : (2 ^ 32 + 977 : Nat).testBit 30 = false := by decide
          have hb31 : (2 ^ 32 + 977 : Nat).testBit 31 = false := by decide
          have hb32 : (2 ^ 32 + 977 : Nat).testBit 32 = true := by decide
          have hb33 : (2 ^ 32 + 977 : Nat).testBit 33 = false := by decide
          have hb34 : (2 ^ 32 + 977 : Nat).testBit 34 = false := by decide
          have hb35 : (2 ^ 32 + 977 : Nat).testBit 35 = false := by decide
          simp only [List.range'_succ, List.range'_zero, List.map_cons, List.map_nil, oddCorr, hb30, hb31, hb32, hb33, hb34, hb35, Bool.and_false, Bool.and_true]
        rw [hc30] at hch
        have hpb : ∀ k : Nat, (highRootOdd L ref).testBit k =
            ([ref (L.Y 29), ref (L.Y 30), ref (L.Y 31), ref (L.Y 32), ref (L.Y 33),
              ref (L.Y 34), ref (L.Y 35), ref L.sigma, ref L.h, oddA L ref 29, oddB L ref 30]).getD k false :=
          fun k => CodecBitSliceVerify.pack_testBit _ k
        simpa only [highRs, List.range_succ, List.range_zero, List.range'_succ, List.range'_zero,
          List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
          hpb, List.getD_cons_zero, List.getD_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] using hch
      have hvars : highVars (highRootOdd L ref) = highExpected L ref := by
        unfold highVars
        rw [hres]
        simp only [highRootOdd, highExpected, CodecBitSliceVerify.pack_testBit,
          List.range'_succ, List.range'_zero, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.getD_cons_zero, List.getD_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.drop_succ_cons, List.drop_zero]
      have ck := DirectDecoder.high_local_checked ⟨highRootOdd L ref, hbd⟩ hval ⟨i, hi⟩
      rw [hvars, hres] at ck
      rw [ck]
      have hget : ∀ k : Fin 4, ((List.range' 30 6).map (fun j => ref (L.R j))).getD (k.val + 2) false =
          ref (L.R (32 + k.val)) := fun k => by fin_cases k <;> rfl
      exact hget ⟨i, hi⟩

private theorem odd_upperStages_correct (ref : BasisState)
    (hbits : ∀ j, j < 256 → ref (fixedLayout.R j) = oddRbit fixedLayout ref j)
    (hexcl : (ref fixedLayout.sigma && ref fixedLayout.h) = false)
    (s : State) (hs : s.basis = ref) (hc : ∀ k, k < 255 → s.basis (fixedLayout.A k) = false) (m : List Bool) :
    ErasedRange (fun i => fixedLayout.R (13 + i)) 243 s (run (upperStages fixedLayout) m s) := by
  let L := fixedLayout
  let mh := m.drop (measurementCount (upper L))
  let mm := mh.drop (measurementCount (DirectDecoder.highBlock L))
  let u := run (upper L) m s
  let v := run (DirectDecoder.highBlock L) mh u
  let w := run (middle L) mm v
  have src : SourceData L ref s := ⟨fun j _ => by rw [hs], by rw [hs], by rw [hs]⟩
  have rs : Pending L ref 256 s := fun j _ => by rw [hs]
  have eu : ErasedRange (fun i => L.R (36 + i)) 220 s u := odd_upper_correct ref hbits hexcl s src rs m
  have su := range_source L fixed_widths fixed_nodup 36 220 (by decide) ref s u eu src
  have pu := range_pending L fixed_widths fixed_nodup 36 220 (by decide) ref s u eu (fun j hj => rs j (by omega))
  have cu : ∀ k, k < 255 → u.basis (L.A k) = false := fun k hk =>
    (range_carry L fixed_widths fixed_nodup 36 220 (by decide) s u eu k hk).trans (hc k hk)
  have ev : ErasedRange (fun i => L.R (32 + i)) 4 u v := odd_highBlock_correct ref hbits hexcl u su pu (cu 0 (by decide)) mh
  have sv := range_source L fixed_widths fixed_nodup 32 4 (by decide) ref u v ev su
  have pv := range_pending L fixed_widths fixed_nodup 32 4 (by decide) ref u v ev (fun j hj => pu j (by omega))
  have ew : ErasedRange (fun i => L.R (13 + i)) 19 v w := odd_middle_correct ref hbits hexcl v sv pv mm
  have runeq : run (upperStages L) m s = w := by simp only [upperStages, run_append, run_take]; rfl
  rw [runeq]
  refine ⟨ew.phase.trans (ev.phase.trans eu.phase), ?_, ?_⟩
  · intro q hq
    apply (ew.outside q (fun i hi => hq i (by omega))).trans
    apply (ev.outside q (fun i hi => by
      have h := hq (19 + i) (by omega)
      simpa only [show 13 + (19 + i) = 32 + i by omega] using h)).trans
    exact eu.outside q (fun i hi => by
      have h := hq (23 + i) (by omega)
      simpa only [show 13 + (23 + i) = 36 + i by omega] using h)
  · intro j hj
    by_cases low : j < 19
    · exact ew.cleared j low
    · rw [range_above L fixed_widths fixed_nodup 13 19 (by decide) v w ew (13 + j) (by omega) (by omega)]
      by_cases high : j < 23
      · have h := ev.cleared (j - 19) (by omega)
        simpa only [show 32 + (j - 19) = 13 + j by omega] using h
      · rw [range_above L fixed_widths fixed_nodup 32 4 (by decide) u v ev (13 + j) (by omega) (by omega)]
        have h := eu.cleared (j - 23) (by omega)
        simpa only [show 36 + (j - 23) = 13 + j by omega] using h

/-! ## Rearrangement of `window760Odd0` via `LREq` -/

private def ladderOdd : List StairLoan.CarryLayer :=
  (StairLoan.mappedLayers borrowBits (xs ++ [fixedLayout.bias]) cs fixedLayout.bias).map k5Clear

private theorem mappedLayers_indep_last :
    ∀ (bits : List MappedBit) (as bs : List Wire) (c0 z1 z2 : Wire),
      bits.length = as.length + 1 → bs.length = as.length →
      StairLoan.mappedLayers bits (as ++ [z1]) bs c0 =
      StairLoan.mappedLayers bits (as ++ [z2]) bs c0
  | [], _, _, _, _, _, hb, _ => by simp at hb
  | [_], [], [], _, _, _, _, _ => rfl
  | [_], [], _ :: _, _, _, _, _, hlen => by simp at hlen
  | [_], _ :: _, _, _, _, _, hb, _ => by simp at hb
  | _ :: _ :: _, [], _, _, _, _, hb, _ => by simp at hb
  | _ :: _ :: _, _ :: _, [], _, _, _, _, hlen => by simp at hlen
  | b :: b' :: bits, a :: as, c :: bs, c0, z1, z2, hb, hlen => by
    cases as with
    | nil =>
      cases bs with
      | nil => simp only [List.cons_append, List.nil_append, StairLoan.mappedLayers]
      | cons _ _ => simp at hlen
    | cons a' as' =>
      cases bs with
      | nil => simp at hlen
      | cons c' bs' =>
        simp only [List.cons_append, StairLoan.mappedLayers]
        congr 1
        exact mappedLayers_indep_last (b' :: bits) (a' :: as') (c' :: bs') c z1 z2
          (by simpa using hb) (by simpa using hlen)

private theorem mappedLayers_drop1 :
    ∀ (bits : List MappedBit) (as bs : List Wire) (c1 c2 z1 z2 : Wire),
      bits.length = as.length + 1 → bs.length = as.length → 1 ≤ as.length →
      (StairLoan.mappedLayers bits (as ++ [z1]) bs c1).drop 1 =
      (StairLoan.mappedLayers bits (as ++ [z2]) bs c2).drop 1
  | [], _, _, _, _, _, _, hb, _, _ => by simp at hb
  | [_], as, _, _, _, _, _, hb, _, h1 => by cases as <;> simp at hb h1
  | _ :: _ :: _, [], _, _, _, _, _, _, _, h1 => by simp at h1
  | _ :: _ :: _, _ :: _, [], _, _, _, _, _, hlen, _ => by simp at hlen
  | b0 :: b1 :: bits, a :: as, c :: bs, c1, c2, z1, z2, hb, hlen, _ => by
    cases as with
    | nil =>
      cases bs with
      | nil => simp only [List.cons_append, List.nil_append, StairLoan.mappedLayers, List.drop_succ_cons, List.drop_zero]
      | cons _ _ => simp at hlen
    | cons a' as' =>
      simp only [List.cons_append, StairLoan.mappedLayers, List.drop_succ_cons, List.drop_zero]
      exact mappedLayers_indep_last (b1 :: bits) (a' :: as') bs c z1 z2 (by simpa using hb) (by simpa using hlen)

private theorem ladderOdd_drop11 : ladderOdd.drop 11 = tailL := by
  have hlen_b : borrowBits.length = xs.length + 1 := by decide +kernel
  have hlen_c : cs.length = xs.length := by decide +kernel
  have h1 := mappedLayers_drop1 borrowBits xs cs fixedLayout.bias cin fixedLayout.bias cin hlen_b hlen_c (by decide +kernel)
  have h11 : (StairLoan.mappedLayers borrowBits (xs ++ [fixedLayout.bias]) cs fixedLayout.bias).drop 11 =
      (StairLoan.mappedLayers borrowBits (xs ++ [cin]) cs cin).drop 11 := by
    rw [show (11 : Nat) = 1 + 10 from rfl, ← List.drop_drop, ← List.drop_drop, h1]
  unfold ladderOdd tailL ladder
  rw [← List.map_drop, ← List.map_drop, h11]
  rfl

private def cmpFrontOdd : Program :=
  borrowPath false xs cs fixedLayout.bias K ++ invertCarry fixedLayout

private def cmpBackOdd : Program :=
  invertCarry fixedLayout ++
    [.X fixedLayout.sigma, .CX fixedLayout.sigma fixedLayout.h,
     .measureX fixedLayout.h [] [.CZ fixedLayout.sigma (fixedLayout.carry.getLastD fixedLayout.bias)]] ++
    borrowPath true xs cs fixedLayout.bias K

private theorem bias_ladder_inputs :
    xs.length = cs.length ∧ xs.Nodup ∧ cs.Nodup ∧ (∀ q ∈ xs, q ∉ cs) ∧
    fixedLayout.bias ∉ xs ∧ fixedLayout.bias ∉ cs := by
  obtain ⟨h1, h2, h3, h4, _, _⟩ := ladder_inputs
  exact ⟨h1, h2, h3, h4, by decide +kernel, by decide +kernel⟩

private theorem borrowFrontOdd_REq :
    LREq (borrowPath false xs cs fixedLayout.bias K)
      (notRegister xs ++ (StairLoan.emitUps headLOdd ++ StairLoan.emitUps tailL) ++ notRegister xs) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bias_ladder_inputs
  have h := borrowPath_false_REq xs cs fixedLayout.bias K h1 h2 h3 h4 h5 h6
  have hu := k5_ups_gen xs cs fixedLayout.bias fixedLayout.bias K h1
  have hbb : k5Bits K (255 + 1) = borrowBits := rfl
  rw [k5_xs_length, hbb] at hu
  change ups xs cs fixedLayout.bias K = StairLoan.emitUps ladderOdd at hu
  have hsp : StairLoan.emitUps ladderOdd = StairLoan.emitUps headLOdd ++ StairLoan.emitUps tailL := by
    rw [← StairLoan.emitUps_append, ← ladderOdd_drop11]
    change StairLoan.emitUps ladderOdd = StairLoan.emitUps (ladderOdd.take 11 ++ ladderOdd.drop 11)
    rw [List.take_append_drop]
  rwa [hu, hsp] at h

private theorem borrowBackOdd_REq :
    LREq (borrowPath true xs cs fixedLayout.bias K)
      (notRegister xs ++ (StairLoan.emitDowns tailL ++ StairLoan.emitDowns headLOdd) ++ notRegister xs) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bias_ladder_inputs
  have h := borrowPath_true_REq xs cs fixedLayout.bias K h1 h2 h3 h4 h5 h6
  have hd := k5_downs_gen xs cs fixedLayout.bias fixedLayout.bias K h1
  have hbb : k5Bits K (255 + 1) = borrowBits := rfl
  rw [k5_xs_length, hbb] at hd
  change downs xs cs fixedLayout.bias K = StairLoan.emitDowns ladderOdd at hd
  have hsp : StairLoan.emitDowns ladderOdd = StairLoan.emitDowns tailL ++ StairLoan.emitDowns headLOdd := by
    rw [← StairLoan.emitDowns_append, ← ladderOdd_drop11]
    change StairLoan.emitDowns ladderOdd = StairLoan.emitDowns (ladderOdd.take 11 ++ ladderOdd.drop 11)
    rw [List.take_append_drop]
  rwa [hd, hsp] at h

private theorem rest_avoid_lowOdd : ∀ q ∈ restCarries, q ∉ wires (lowBlockOdd fixedLayout) := by
  have hchk : restCarries.all (fun q => (lowBlockOdd fixedLayout).all (fun i => decide (q ∉ Instr.wires i))) = true :=
    k5_mask_avoid _ _ (by decide +kernel)
  intro q hq
  exact not_mem_wires_of_all _ q (List.all_eq_true.mp hchk q hq)

private theorem midOdd_REq :
    LREq (invertCarry fixedLayout ++ lowBlockOdd fixedLayout ++ invertCarry fixedLayout)
      (lowLive.map (fun q => Instr.X q) ++ lowBlockOdd fixedLayout ++ lowLive.map (fun q => Instr.X q)) := by
  show LREq (notRegister cs ++ lowBlockOdd fixedLayout ++ notRegister cs)
    (notRegister lowLive ++ lowBlockOdd fixedLayout ++ notRegister lowLive)
  have p1 : LREq (notRegister cs) (notRegister lowLive ++ notRegister restCarries) := by
    rw [← notRegister_append]; apply LREq.notRegister_par; intro q
    rw [cs_split]; simp only [restCarries, flipPar_append]
    cases flipPar (cs.take 5) q <;> cases flipPar lowLive q <;> cases flipPar (cs.drop 11) q <;> rfl
  have p2 : LREq (notRegister cs) (notRegister restCarries ++ notRegister lowLive) := by
    rw [← notRegister_append]; apply LREq.notRegister_par; intro q
    rw [cs_split]; simp only [restCarries, flipPar_append]
    cases flipPar (cs.take 5) q <;> cases flipPar lowLive q <;> cases flipPar (cs.drop 11) q <;> rfl
  have c := LREq.notRegister_comm _ _ rest_avoid_lowOdd
  have tw := LREq.notRegister_twice restCarries
  have st1 := (p1.append (LREq.refl (lowBlockOdd fixedLayout))).append p2
  have t1 := LREq.ctx (notRegister lowLive) (notRegister restCarries ++ notRegister lowLive) c
  have t2 := LREq.ctx (notRegister lowLive ++ lowBlockOdd fixedLayout) (notRegister lowLive) tw
  simp only [List.append_assoc, List.append_nil, List.nil_append] at st1 t1 t2 ⊢
  exact st1.trans (t1.trans t2)

private theorem window760Odd0_REq :
    LREq (cmpFrontOdd ++ lowBlockOdd fixedLayout ++ cmpBackOdd) window760Odd0 := by
  have h := (((borrowFrontOdd_REq.append midOdd_REq).append
      (LREq.refl [Instr.X fixedLayout.sigma, Instr.CX fixedLayout.sigma fixedLayout.h,
        Instr.measureX fixedLayout.h [] [Correction.CZ fixedLayout.sigma (fixedLayout.carry.getLastD fixedLayout.bias)]])).append
      borrowBackOdd_REq)
  simp only [List.append_assoc] at h
  simp only [cmpFrontOdd, cmpBackOdd, window760Odd0, top760Odd, StairLoan.emitSweep, List.append_assoc]
  exact h

/-! ## `lowBlockOdd` and `window760Odd0` correctness -/

private def comparisonOddValues (L : DecoderLayout) (b : BasisState) : List Bool :=
  cmpSteps ((List.range 13).map (fun j => b (L.Y j)))
    [true, false, true, true, true, false, true, false, true, true, true, true, true] true

private def comparisonOdd (L : DecoderLayout) (b : BasisState) (j : Nat) : Bool :=
  (comparisonOddValues L b).getD j false

private def rootOdd (L : DecoderLayout) (b : BasisState) : Nat := packBits
  [b (L.Y 3), b (L.Y 4), b (L.Y 5), b (L.Y 6), b (L.Y 7), b (L.Y 8), b (L.Y 9),
   b (L.Y 10), b (L.Y 11), b (L.Y 12), b L.sigma, b L.h, oddA L b 3, oddB L b 4, comparisonOdd L b 3]

private def rootOddCheck (x : Nat) : Bool :=
  let y0 := x.testBit 0; let y1 := x.testBit 1; let y2 := x.testBit 2; let y3 := x.testBit 3
  let sg := x.testBit 4; let hb := x.testBit 5
  let a0 := y0 ^^ sg
  let a1 := carryBit y0 (y1 ^^ sg) a0
  let a2 := carryBit y1 (y2 ^^ sg) a1
  let a3 := carryBit y2 (y3 ^^ sg) a2
  let r0 := y0 ^^ !sg
  let r1 := y0 ^^ y1 ^^ sg ^^ a0
  let r2 := y1 ^^ y2 ^^ sg ^^ a1
  let r3 := y2 ^^ y3 ^^ sg ^^ a2
  let b1 := carryBit (hb && true) r0 false
  let b2 := carryBit false r1 b1
  let b3 := carryBit false r2 b2
  let b4 := carryBit false r3 b3
  let cmp3 := (cmpSteps [y0, y1, y2, y3] [true, false, true, true] true).getD 3 false
  let idx := y3.toNat + 2 * sg.toNat + 4 * hb.toNat + 8 * a3.toNat + 16 * b4.toNat + 32 * cmp3.toNat
  (sg && hb) || (2305880426972133179 : Nat).testBit idx

private theorem rootOddCheck_all : (List.range 64).all rootOddCheck = true := by decide +kernel

private theorem rootOdd_valid (L : DecoderLayout) (b : BasisState)
    (hexcl : (b L.sigma && b L.h) = false) :
    CompareDecoder.valid (rootOdd L b) = true := by
  let x := CodecBitSliceVerify.packBits [b (L.Y 0), b (L.Y 1), b (L.Y 2), b (L.Y 3), b L.sigma, b L.h]
  have hx : x < 64 := by
    have h := pack_bound [b (L.Y 0), b (L.Y 1), b (L.Y 2), b (L.Y 3), b L.sigma, b L.h]
    norm_num only [List.length_cons, List.length_nil] at h; exact h
  have hck := List.all_eq_true.mp rootOddCheck_all x (List.mem_range.mpr hx)
  have htb : x.testBit 0 = b (L.Y 0) ∧ x.testBit 1 = b (L.Y 1) ∧ x.testBit 2 = b (L.Y 2) ∧
      x.testBit 3 = b (L.Y 3) ∧ x.testBit 4 = b L.sigma ∧ x.testBit 5 = b L.h := by
    simp only [x, CodecBitSliceVerify.pack_testBit, List.getD_cons_zero, List.getD_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, and_self]
  have hidx : seedIndex (rootOdd L b) =
      (b (L.Y 3)).toNat + 2 * (b L.sigma).toNat + 4 * (b L.h).toNat +
        8 * (oddA L b 3).toNat + 16 * (oddB L b 4).toNat + 32 * (comparisonOdd L b 3).toNat := by
    simp only [seedIndex, rootOdd, CodecBitSliceVerify.pack_testBit, List.getD_cons_zero, List.getD_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  have hcb : (2 ^ 32 + 977 : Nat).testBit 0 = true ∧ (2 ^ 32 + 977 : Nat).testBit 1 = false ∧
      (2 ^ 32 + 977 : Nat).testBit 2 = false ∧ (2 ^ 32 + 977 : Nat).testBit 3 = false := by decide
  have hcmp : comparisonOdd L b 3 =
      (cmpSteps [b (L.Y 0), b (L.Y 1), b (L.Y 2), b (L.Y 3)] [true, false, true, true] true).getD 3 false := by
    simp only [comparisonOdd, comparisonOddValues, List.range_succ, List.range_zero, List.map_append,
      List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
      cmpSteps, List.getD_cons_zero, List.getD_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  have ha0 : oddA L b 0 = (b (L.Y 0) ^^ b L.sigma) := oddA_zero L b
  have ha1 : oddA L b 1 = carryBit (b (L.Y 0)) (b (L.Y 1) ^^ b L.sigma) (oddA L b 0) := oddA_succ L b 0
  have ha2 : oddA L b 2 = carryBit (b (L.Y 1)) (b (L.Y 2) ^^ b L.sigma) (oddA L b 1) := oddA_succ L b 1
  have ha3 : oddA L b 3 = carryBit (b (L.Y 2)) (b (L.Y 3) ^^ b L.sigma) (oddA L b 2) := oddA_succ L b 2
  have hb4 : oddB L b 4 = carryBit false (b (L.Y 2) ^^ b (L.Y 3) ^^ b L.sigma ^^ oddA L b 2)
      (carryBit false (b (L.Y 1) ^^ b (L.Y 2) ^^ b L.sigma ^^ oddA L b 1)
        (carryBit false (b (L.Y 0) ^^ b (L.Y 1) ^^ b L.sigma ^^ oddA L b 0)
          (carryBit (b L.h && true) (b (L.Y 0) ^^ !b L.sigma) false))) := by
    simp only [oddB_succ, oddB_zero, oddRaw, oddCorr, sourceAt,
      show (0 : Nat) < 255 by decide, show (1 : Nat) < 255 by decide,
      show (2 : Nat) < 255 by decide, show (3 : Nat) < 255 by decide, if_true,
      hcb.1, hcb.2.1, hcb.2.2.1, hcb.2.2.2, Bool.and_false]
  dsimp only [rootOddCheck] at hck
  rw [htb.1, htb.2.1, htb.2.2.1, htb.2.2.2.1, htb.2.2.2.2.1, htb.2.2.2.2.2, hexcl, Bool.false_or] at hck
  unfold CompareDecoder.valid
  rw [hidx, hcmp, hb4, ha3, ha2, ha1, ha0]
  exact hck

private theorem lowOdd_math_high (L : DecoderLayout) (hw : L.Widths) (b : BasisState)
    (hbits : ∀ j, j < 256 → b (L.R j) = oddRbit L b j)
    (hexcl : (b L.sigma && b L.h) = false) (i : Fin 7) :
    let exp := [true] ++ (List.range' 3 10).map (fun j => b (L.Y j)) ++
      [b L.sigma, b L.h, b (L.Y 4) && b L.h] ++
      (List.range' 3 10).map (comparisonOdd L b) ++ (List.range' 4 9).map (fun j => b (L.R j))
    evalPoly (comparePolys.getD i.val []) exp = b (L.R (i.val + 6)) := by
  have hbd : rootOdd L b < 32768 := by
    have h := pack_bound [b (L.Y 3), b (L.Y 4), b (L.Y 5), b (L.Y 6), b (L.Y 7), b (L.Y 8), b (L.Y 9),
      b (L.Y 10), b (L.Y 11), b (L.Y 12), b L.sigma, b L.h, oddA L b 3, oddB L b 4, comparisonOdd L b 3]
    norm_num only [List.length_cons, List.length_nil] at h; exact h
  have hres : lowRs (rootOdd L b) = [false, false, false, false] ++ (List.range' 4 9).map (fun j => b (L.R j)) := by
    have hch := odd_chunk_eq L hw b hbits 9 4 (by decide) (by decide)
    have htb : ∀ j : Fin 9, (2 ^ 32 + 977 : Nat).testBit (j.val + 4) = (977 : Nat).testBit (j.val + 4) := by
      decide +kernel
    have hcorr : (List.range' 4 9).map (fun j => oddCorr L b j) =
        (List.range 9).map (fun j => b L.h && (977 : Nat).testBit (j + 4)) := by
      simp only [List.range_succ, List.range_zero, List.range'_succ, List.range'_zero,
        List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil, oddCorr,
        htb ⟨0, by decide⟩, htb ⟨1, by decide⟩, htb ⟨2, by decide⟩, htb ⟨3, by decide⟩,
        htb ⟨4, by decide⟩, htb ⟨5, by decide⟩, htb ⟨6, by decide⟩, htb ⟨7, by decide⟩, htb ⟨8, by decide⟩]
    rw [hcorr] at hch
    unfold lowRs
    congr 1
    have hpb : ∀ k : Nat, (rootOdd L b).testBit k =
        ([b (L.Y 3), b (L.Y 4), b (L.Y 5), b (L.Y 6), b (L.Y 7), b (L.Y 8), b (L.Y 9),
          b (L.Y 10), b (L.Y 11), b (L.Y 12), b L.sigma, b L.h, oddA L b 3, oddB L b 4, comparisonOdd L b 3]).getD k false :=
      fun k => CodecBitSliceVerify.pack_testBit _ k
    simpa only [List.range_succ, List.range_zero, List.range'_succ, List.range'_zero,
      List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
      hpb, List.getD_cons_zero, List.getD_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] using hch
  have hvars : compareVars (rootOdd L b) =
      [true] ++ (List.range' 3 10).map (fun j => b (L.Y j)) ++
      [b L.sigma, b L.h, b (L.Y 4) && b L.h] ++
      (List.range' 3 10).map (comparisonOdd L b) ++ (List.range' 4 9).map (fun j => b (L.R j)) := by
    unfold compareVars
    rw [hres]
    have hpb : ∀ k : Nat, (rootOdd L b).testBit k =
        ([b (L.Y 3), b (L.Y 4), b (L.Y 5), b (L.Y 6), b (L.Y 7), b (L.Y 8), b (L.Y 9),
          b (L.Y 10), b (L.Y 11), b (L.Y 12), b L.sigma, b L.h, oddA L b 3, oddB L b 4, comparisonOdd L b 3]).getD k false :=
      fun k => CodecBitSliceVerify.pack_testBit _ k
    simp only [hpb, List.range_succ, List.range_zero, List.range'_succ, List.range'_zero,
      List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
      List.getD_cons_zero, List.getD_cons_succ, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.drop_succ_cons, List.drop_zero,
      comparisonOdd, comparisonOddValues, cmpSteps]
  have ck := CompareDecoder.low_checked (rootOdd L b) hbd (rootOdd_valid L b hexcl) i
  rw [hvars, hres] at ck
  dsimp only
  rw [ck]
  fin_cases i <;> rfl

private theorem lowOdd_math_low (L : DecoderLayout) (hw : L.Widths) (b : BasisState)
    (hscalar : regValue L.r b =
      ((if b L.sigma then regValue (L.y.take 255) b else 3 * regValue (L.y.take 255) b + 1) +
        (b L.h).toNat * (2 ^ 32 + 977)) % 2 ^ 256)
    (hexcl : (b L.sigma && b L.h) = false) (j : Fin 6) :
    let initVec := [true] ++ (List.range 13).map (fun i => b (L.Y i)) ++
      [b L.sigma, b L.h, b (L.Y 255), b (L.Y 4) && b L.h, false, false] ++
      (List.range 13).map (fun i => b (L.R i))
    evalPoly (lowPolysOdd.getD j.val []) initVec =
      if j.val = 0 then !(b (L.R 0)) else b (L.R j.val) := by
  let y6 := regValue (L.y.take 255) b % 64
  have hy6 : y6 < 64 := Nat.mod_lt _ (by decide)
  have hmem : (b L.sigma, b L.h) ∈ [(false, false), (false, true), (true, false)] := by
    cases hs : b L.sigma <;> cases hh : b L.h <;> simp_all
  have hck := List.all_eq_true.mp (List.all_eq_true.mp lowPolysOdd_checked y6 (List.mem_range.mpr hy6))
    (b L.sigma, b L.h) hmem
  simp only [Bool.and_eq_true] at hck
  have hyb : ∀ i, i < 6 → y6.testBit i = b (L.Y i) := by
    intro i hi
    have h0 : L.Y i = (L.y.take 255).getD i 0 := by
      simp [DecoderLayout.Y, List.getD_eq_getElem, hw.1, show i < 255 by omega, show i < 256 by omega]
    rw [h0, ECDSAAdd.Entrant.StairCodec.regValue_getD_testBit (L.y.take 255) i 0 b (by simp [hw.1]; omega)]
    rw [show y6 = regValue (L.y.take 255) b % 2 ^ 6 from rfl, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
  have hr6_eq : regValue L.r b % 64 =
      if b L.sigma then y6 else (3 * y6 + 1 + (if b L.h then 977 else 0)) % 64 := by
    rw [hscalar, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 256)]
    cases hs : b L.sigma
    · simp only [Bool.false_eq_true, if_false]
      have h977 : (2 ^ 32 + 977) % 64 = 977 % 64 := by decide
      cases hh : b L.h <;> simp [y6, Nat.add_mod, Nat.mul_mod, h977]
    · have hh : b L.h = false := by simp [hs] at hexcl; exact hexcl
      simp [hh, y6]
  have hrb : ∀ i, i < 6 → (if b L.sigma then y6 else (3 * y6 + 1 + (if b L.h then 977 else 0)) % 64).testBit i = b (L.R i) := by
    intro i hi
    rw [← hr6_eq, DecoderLayout.R,
      ECDSAAdd.Entrant.StairCodec.regValue_getD_testBit L.r i 0 b (by rw [hw.2.1]; omega)]
    rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
  have hsame : evalPoly (lowPolysOdd.getD j.val [])
      ([true] ++ (List.range 13).map (fun i => b (L.Y i)) ++
        [b L.sigma, b L.h, b (L.Y 255), b (L.Y 4) && b L.h, false, false] ++
        (List.range 13).map (fun i => b (L.R i))) =
      evalPoly (lowPolysOdd.getD j.val [])
      ([true] ++ ((List.range 6).map (fun i => y6.testBit i) ++ List.replicate 7 false) ++
        [b L.sigma, b L.h, false, y6.testBit 4 && b L.h, false, false] ++
        ((List.range 6).map (fun i => (if b L.sigma then y6 else (3 * y6 + 1 + (if b L.h then 977 else 0)) % 64).testBit i) ++ List.replicate 7 false)) := by
    have hy0 := hyb 0 (by decide); have hy1 := hyb 1 (by decide); have hy2 := hyb 2 (by decide)
    have hy3 := hyb 3 (by decide); have hy4 := hyb 4 (by decide); have hy5 := hyb 5 (by decide)
    have hr0 := hrb 0 (by decide); have hr1 := hrb 1 (by decide); have hr2 := hrb 2 (by decide)
    have hr3 := hrb 3 (by decide); have hr4 := hrb 4 (by decide); have hr5 := hrb 5 (by decide)
    fin_cases j <;>
      simp [lowPolysOdd, evalPoly, List.range_succ, hy0, hy1, hy2, hy3, hy4, hy5, hr0, hr1, hr2, hr3, hr4, hr5]
  dsimp only
  rw [hsame]
  have hr0 := hrb 0 (by decide); have hr1 := hrb 1 (by decide); have hr2 := hrb 2 (by decide)
  have hr3 := hrb 3 (by decide); have hr4 := hrb 4 (by decide); have hr5 := hrb 5 (by decide)
  fin_cases j
  · simpa only [if_true, hr0] using beq_iff_eq.mp hck.1
  · have h1 := List.all_eq_true.mp hck.2 1 (by decide)
    simpa only [show (1 : Nat) ≠ 0 by decide, if_false, hr1] using beq_iff_eq.mp h1
  · have h2 := List.all_eq_true.mp hck.2 2 (by decide)
    simpa only [show (2 : Nat) ≠ 0 by decide, if_false, hr2] using beq_iff_eq.mp h2
  · have h3 := List.all_eq_true.mp hck.2 3 (by decide)
    simpa only [show (3 : Nat) ≠ 0 by decide, if_false, hr3] using beq_iff_eq.mp h3
  · have h4 := List.all_eq_true.mp hck.2 4 (by decide)
    simpa only [show (4 : Nat) ≠ 0 by decide, if_false, hr4] using beq_iff_eq.mp h4
  · have h5 := List.all_eq_true.mp hck.2 5 (by decide)
    simpa only [show (5 : Nat) ≠ 0 by decide, if_false, hr5] using beq_iff_eq.mp h5

private theorem lowOdd_correction_away :
    ∀ i : Fin 13, fixedLayout.R i.val ∉ correctionWires (correctionsOdd fixedLayout i.val) := by
  decide +kernel

private theorem lowOdd_correction_tri :
    ∀ i j : Fin 13, i.val < j.val →
      fixedLayout.R j.val ∉ correctionWires (correctionsOdd fixedLayout i.val) := by
  decide +kernel

private theorem initialOdd_value (L : DecoderLayout) (b : BasisState) (j : Fin 6) :
    phaseValue (correctionsOdd L j.val) b = evalPoly (lowPolysOdd.getD j.val []) (initialPhysical L b) := by
  fin_cases j <;> simp [correctionsOdd, correctionsFor, initialWires, initialPhysical,
    lowPolysOdd, phaseValue, evalPoly, List.range_succ]

private theorem compareOdd_value (L : DecoderLayout) (b : BasisState) (j : Fin 7) :
    phaseValue (correctionsOdd L (j.val + 6)) b = evalPoly (comparePolys.getD j.val []) (comparePhysical L b) := by
  have heq : correctionsOdd L (j.val + 6) = CompareDecoder.corrections L (j.val + 6) := by
    simp [correctionsOdd, CompareDecoder.corrections]
  rw [heq]
  exact CompareDecoder.compare_value L b j

private theorem lowEraseOdd_correct (ref : BasisState)
    (hbits : ∀ j, j < 256 → ref (fixedLayout.R j) = oddRbit fixedLayout ref j)
    (hscalar : regValue fixedLayout.r ref =
      ((if ref fixedLayout.sigma then regValue (fixedLayout.y.take 255) ref
        else 3 * regValue (fixedLayout.y.take 255) ref + 1) +
        (ref fixedLayout.h).toNat * (2 ^ 32 + 977)) % 2 ^ 256)
    (hexcl : (ref fixedLayout.sigma && ref fixedLayout.h) = false)
    (u : State) (us : SourceData fixedLayout ref u) (ur : Pending fixedLayout ref 13 u)
    (uc : ∀ j, 3 ≤ j → j < 13 → u.basis (fixedLayout.A j) = comparisonOdd fixedLayout ref j)
    (uh : u.basis fixedLayout.bias = (ref (fixedLayout.Y 4) && ref fixedLayout.h))
    (m : List Bool) :
    ErasedRange fixedLayout.R 13 u (run (lowEraseOdd fixedLayout) m u) := by
  let L := fixedLayout
  let P12 := eraseRange (fun i => L.R (1 + i)) (fun i => correctionsOdd L (1 + i)) 12
  have hP12 : ErasedRange (fun i => L.R (1 + i)) 12 u (run P12 (m.take (measurementCount P12)) u) :=
    eraseRange_correct (fun i => L.R (1 + i)) (fun i => correctionsOdd L (1 + i)) 12
      (fun i hi j hj eq => by
        have z := result_inj L fixed_widths fixed_nodup (1 + i) (1 + j) (by omega) (by omega) eq; omega)
      (fun i hi => lowOdd_correction_away ⟨1 + i, by omega⟩)
      (fun i hi j hij hj => lowOdd_correction_tri ⟨1 + i, by omega⟩ ⟨1 + j, by omega⟩ (by show 1 + i < 1 + j; omega))
      u
      (fun i hi => by
        rw [ur (1 + i) (by omega)]
        symm
        by_cases small : 1 + i < 6
        · rw [initialOdd_value L u.basis ⟨1 + i, small⟩]
          have heq : evalPoly (lowPolysOdd.getD (1 + i) []) (initialPhysical L u.basis) =
              evalPoly (lowPolysOdd.getD (1 + i) [])
                ([true] ++ (List.range 13).map (fun k => ref (L.Y k)) ++
                  [ref L.sigma, ref L.h, ref (L.Y 255), ref (L.Y 4) && ref L.h, false, false] ++
                  (List.range 13).map (fun k => ref (L.R k))) := by
            have hy : (List.range 13).map (fun k => u.basis (L.Y k)) = (List.range 13).map (fun k => ref (L.Y k)) :=
              List.map_congr_left (fun k hk => us.source k (by have := List.mem_range.mp hk; omega))
            have hr : (List.range 13).map (fun k => u.basis (L.R k)) = (List.range 13).map (fun k => ref (L.R k)) :=
              List.map_congr_left (fun k hk => ur k (List.mem_range.mp hk))
            unfold initialPhysical
            rw [hy, hr, us.sigma, us.h, us.source 255 (by decide), uh]
          rw [heq, lowOdd_math_low L fixed_widths ref hscalar hexcl ⟨1 + i, small⟩]
          simp [L, show 1 + i ≠ 0 by omega]
        · have hb : 1 + i - 6 < 7 := by omega
          have heq' : 1 + i - 6 + 6 = 1 + i := by omega
          have hcv := compareOdd_value L u.basis ⟨1 + i - 6, hb⟩
          simp only [heq'] at hcv
          rw [hcv]
          have hcp : comparePhysical L u.basis =
              [true] ++ (List.range' 3 10).map (fun k => ref (L.Y k)) ++
              [ref L.sigma, ref L.h, ref (L.Y 4) && ref L.h] ++
              (List.range' 3 10).map (comparisonOdd L ref) ++ (List.range' 4 9).map (fun k => ref (L.R k)) := by
            have hy : (List.range' 3 10).map (fun k => u.basis (L.Y k)) = (List.range' 3 10).map (fun k => ref (L.Y k)) :=
              List.map_congr_left (fun k hk => us.source k (by have := List.mem_range'.mp hk; omega))
            have hr : (List.range' 4 9).map (fun k => u.basis (L.R k)) = (List.range' 4 9).map (fun k => ref (L.R k)) :=
              List.map_congr_left (fun k hk => ur k (by have := List.mem_range'.mp hk; omega))
            have hc' : (List.range' 3 10).map (fun k => u.basis (L.A k)) = (List.range' 3 10).map (comparisonOdd L ref) :=
              List.map_congr_left (fun k hk => by rcases List.mem_range'.mp hk with ⟨_, _, _⟩; exact uc k (by omega) (by omega))
            unfold comparePhysical; rw [hy, hr, hc', us.sigma, us.h, uh]
          rw [hcp]
          simpa only [heq'] using lowOdd_math_high L fixed_widths ref hbits hexcl ⟨1 + i - 6, hb⟩)
      (m.take (measurementCount P12))
  let v := run P12 (m.take (measurementCount P12)) u
  let vx : State := ⟨v.phase, writeBit v.basis (L.R 0) (!(v.basis (L.R 0)))⟩
  have hv0 : v.basis (L.R 0) = u.basis (L.R 0) :=
    hP12.outside (L.R 0) (fun i hi => r_ne_r L fixed_widths fixed_nodup 0 (1 + i) (by decide) (by omega) (by omega))
  have hvx_r0 : vx.basis (L.R 0) = !(ref (L.R 0)) :=
    Eq.trans (by rw [show vx.basis = writeBit v.basis (L.R 0) (!(v.basis (L.R 0))) from rfl, writeBit, Function.update_self])
      (congrArg Bool.not (hv0.trans (ur 0 (by decide))))
  have hvx_poly : phaseValue (correctionsOdd L 0) vx.basis = !(ref (L.R 0)) := by
    rw [initialOdd_value L vx.basis ⟨0, by decide⟩]
    have h0_val : ∀ q, q ∈ [L.Y 0, L.sigma, L.h] → vx.basis q = ref q := by
      intro q hq
      have hq0 : q ≠ L.R 0 := by
        rcases (by simpa using hq : q = L.Y 0 ∨ q = L.sigma ∨ q = L.h) with rfl | rfl | rfl <;> decide +kernel
      have hq12 : ∀ i, i < 12 → q ≠ L.R (1 + i) := by
        intro i hi
        rcases (by simpa using hq : q = L.Y 0 ∨ q = L.sigma ∨ q = L.h) with rfl | rfl | rfl
        · exact y_ne_r L fixed_widths fixed_nodup 0 (1 + i) (by decide) (by omega)
        · exact flag_ne_r L fixed_widths fixed_nodup L.sigma (Or.inl rfl) (1 + i) (by omega)
        · exact flag_ne_r L fixed_widths fixed_nodup L.h (Or.inr (Or.inl rfl)) (1 + i) (by omega)
      have hvq : v.basis q = u.basis q := hP12.outside q hq12
      simp only [vx, writeBit, Function.update_of_ne hq0, hvq]
      rcases (by simpa using hq : q = L.Y 0 ∨ q = L.sigma ∨ q = L.h) with rfl | rfl | rfl
      · exact us.source 0 (by decide)
      · exact us.sigma
      · exact us.h
    have hp0 : lowPolysOdd.getD 0 [] = [[1], [14], [15]] := by decide +kernel
    have hsame0 : evalPoly (lowPolysOdd.getD 0 []) (initialPhysical L vx.basis) =
        evalPoly (lowPolysOdd.getD 0 [])
          ([true] ++ (List.range 13).map (fun k => ref (L.Y k)) ++
            [ref L.sigma, ref L.h, ref (L.Y 255), ref (L.Y 4) && ref L.h, false, false] ++
            (List.range 13).map (fun k => ref (L.R k))) := by
      have hev : ∀ (xs : List Bool), evalPoly [[1], [14], [15]] xs =
          (xs.getD 1 false ^^ xs.getD 14 false ^^ xs.getD 15 false) := by
        intro xs
        simp only [evalPoly, List.foldr_cons, List.foldr_nil, Bool.and_true, Bool.xor_false]
        cases xs.getD 1 false <;> cases xs.getD 14 false <;> cases xs.getD 15 false <;> rfl
      have hr13 : List.range 13 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := rfl
      rw [hp0, hev, hev]
      simp only [initialPhysical, hr13, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.getD_cons_zero, List.getD_cons_succ,
        h0_val (L.Y 0) (by simp), h0_val L.sigma (by simp), h0_val L.h (by simp)]
    rw [hsame0]
    simpa using lowOdd_math_low L fixed_widths ref hscalar hexcl ⟨0, by decide⟩
  have hm0 := measure_poly_away (L.R 0) (correctionsOdd L 0) vx (m.drop (measurementCount P12))
    (lowOdd_correction_away ⟨0, by decide⟩) (hvx_r0.trans hvx_poly.symm)
  have hrun : run (lowEraseOdd L) m u = ⟨v.phase, writeBit vx.basis (L.R 0) false⟩ := by
    unfold lowEraseOdd
    rw [run_append]
    change run ([.X (L.R 0)] ++ [.measureX (L.R 0) [] (correctionsOdd L 0)]) (m.drop (measurementCount P12)) v = _
    rw [run_append, show measurementCount ([.X (L.R 0)] : Program) = 0 from by simp [measurementCount], List.take_zero, List.drop_zero,
      BalancedCleanupOffset.x_run]
    exact hm0
  rw [hrun]
  refine ⟨hP12.phase, ?_, ?_⟩
  · intro q hq
    have hq0 : q ≠ L.R 0 := hq 0 (by decide)
    simp only [vx, writeBit, Function.update_of_ne hq0]
    exact hP12.outside q (fun i hi => hq (1 + i) (by omega))
  · intro i hi
    cases i with
    | zero => simp [L, writeBit]
    | succ k =>
      have hne : fixedLayout.R (k + 1) ≠ fixedLayout.R 0 :=
        r_ne_r L fixed_widths fixed_nodup (k + 1) 0 (by omega) (by decide) (by omega)
      simp only [L, vx, writeBit, Function.update_of_ne hne]
      simpa only [Nat.add_comm] using hP12.cleared k (by omega)

private theorem lowBlockOdd_correct (ref : BasisState)
    (hbits : ∀ j, j < 256 → ref (fixedLayout.R j) = oddRbit fixedLayout ref j)
    (hscalar : regValue fixedLayout.r ref =
      ((if ref fixedLayout.sigma then regValue (fixedLayout.y.take 255) ref
        else 3 * regValue (fixedLayout.y.take 255) ref + 1) +
        (ref fixedLayout.h).toNat * (2 ^ 32 + 977)) % 2 ^ 256)
    (hexcl : (ref fixedLayout.sigma && ref fixedLayout.h) = false)
    (s : State) (src : SourceData fixedLayout ref s) (rs : Pending fixedLayout ref 13 s)
    (cmp : ∀ j, 3 ≤ j → j < 13 → s.basis (fixedLayout.A j) = comparisonOdd fixedLayout ref j)
    (clean : s.basis fixedLayout.bias = false) (m : List Bool) :
    ErasedRange fixedLayout.R 13 s (run (lowBlockOdd fixedLayout) m s) := by
  let L := fixedLayout
  let u := prepared s (L.Y 4) L.h L.bias
  have us : SourceData L ref u := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      change writeBit s.basis L.bias (s.basis (L.Y 4) && s.basis L.h) (L.Y j) = ref (L.Y j)
      exact (Function.update_of_ne (y_ne_bias ⟨j, hj⟩) _ _).trans (src.source j hj)
    · change writeBit s.basis L.bias (s.basis (L.Y 4) && s.basis L.h) L.sigma = ref L.sigma
      exact (Function.update_of_ne (by decide +kernel : L.sigma ≠ L.bias) _ _).trans src.sigma
    · change writeBit s.basis L.bias (s.basis (L.Y 4) && s.basis L.h) L.h = ref L.h
      exact (Function.update_of_ne (by decide +kernel : L.h ≠ L.bias) _ _).trans src.h
  have ur : Pending L ref 13 u := fun j hj => by
    change writeBit s.basis L.bias (s.basis (L.Y 4) && s.basis L.h) (L.R j) = ref (L.R j)
    exact (Function.update_of_ne (flag_ne_r L fixed_widths fixed_nodup L.bias (Or.inr (Or.inr rfl)) j (by omega)).symm _ _).trans (rs j hj)
  have uc : ∀ j, 3 ≤ j → j < 13 → u.basis (L.A j) = comparisonOdd L ref j := fun j hlo hhi => by
    change writeBit s.basis L.bias (s.basis (L.Y 4) && s.basis L.h) (L.A j) = comparisonOdd L ref j
    exact (Function.update_of_ne (a_ne_bias ⟨j, by omega⟩) _ _).trans (cmp j hlo hhi)
  have uh : u.basis L.bias = (ref (L.Y 4) && ref L.h) := by
    change writeBit s.basis L.bias (s.basis (L.Y 4) && s.basis L.h) L.bias = _
    rw [writeBit, Function.update_self, src.source 4 (by decide), src.h]
  exact andWrap_erased fixedLayout.R 13 (L.Y 4) L.h L.bias (lowEraseOdd L)
    (y_ne_bias ⟨4, by decide⟩) (by decide +kernel)
    (fun i hi => y_ne_r L fixed_widths fixed_nodup 4 i (by decide) (by omega))
    (fun i hi => flag_ne_r L fixed_widths fixed_nodup L.h (Or.inr (Or.inl rfl)) i (by omega))
    (fun i hi => flag_ne_r L fixed_widths fixed_nodup L.bias (Or.inr (Or.inr rfl)) i (by omega))
    s clean m (lowEraseOdd_correct ref hbits hscalar hexcl u us ur uc uh m)

/-! ## `window760Odd0` + `[.X sigma]` full semantics -/

private theorem cmp_nodup_full :
    (fixedLayout.sigma :: fixedLayout.h :: fixedLayout.bias :: (fixedLayout.y.take 255 ++ fixedLayout.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hc := List.nodup_iff_count.mp fixed_nodup q
  have ht := (List.take_sublist 255 fixedLayout.y).count_le q
  simp only [DecoderLayout.wires, List.count_cons, List.count_append, List.count_nil] at hc ⊢
  omega

private theorem cmp_nodup_borrow :
    (fixedLayout.bias :: fixedLayout.y.take 255 ++ fixedLayout.carry).Nodup :=
  (List.nodup_cons.mp (List.nodup_cons.mp cmp_nodup_full).2).2

private def cmpBasisOdd (L : DecoderLayout) (b : BasisState) : BasisState :=
  let u := borrowBasis (L.y.take 255) L.carry L.bias K b
  fun q => if q ∈ L.carry then !(u q) else u q

attribute [local irreducible] borrowPath borrowBasis

private theorem cmpFrontOdd_run (s : State) (m : List Bool) :
    run cmpFrontOdd m s = ⟨s.phase, cmpBasisOdd fixedLayout s.basis⟩ := by
  have hnd : (fixedLayout.bias :: fixedLayout.y.take 255 ++ fixedLayout.carry).Nodup := cmp_nodup_borrow
  have hndc : fixedLayout.carry.Nodup := carry_nd fixedLayout fixed_nodup
  have hbz := borrowPath_zero (fixedLayout.y.take 255) fixedLayout.carry fixedLayout.bias K
  have hsp : cmpFrontOdd = borrowPath false (fixedLayout.y.take 255) fixedLayout.carry fixedLayout.bias K ++
      notRegister fixedLayout.carry := by
    unfold cmpFrontOdd invertCarry xs cs; rfl
  rw [hsp, run_append, hbz, List.take_zero, List.drop_zero, borrow_run _ _ _ _ hnd, notRegister_correct _ hndc]
  unfold cmpBasisOdd; rfl

private theorem cmpBasisOdd_outside (b : BasisState) (q : Wire) (hq : q ∉ fixedLayout.carry) :
    cmpBasisOdd fixedLayout b q = b q := by
  simp only [cmpBasisOdd, if_neg hq]
  exact borrow_outside _ _ _ _ _ q hq

private theorem cmpBasisOdd_comparison (b : BasisState) (clean : ∀ q ∈ fixedLayout.carry, b q = false)
    (hb : b fixedLayout.bias = false) (j : Fin 13) :
    cmpBasisOdd fixedLayout b (fixedLayout.A j.val) = comparisonOdd fixedLayout b j.val := by
  let L := fixedLayout
  have hnd : (L.bias :: L.y.take 255 ++ L.carry).Nodup := cmp_nodup_borrow
  have hgr := borrow_graph (L.y.take 255) L.carry L.bias K hnd b clean
  have hlen : L.carry.length = (L.y.take 255).length := by decide +kernel
  have hvals := graph_values (L.y.take 255) L.carry L.bias K _ hlen hgr
  have hmap : L.carry.map (cmpBasisOdd L b) = (L.carry.map (borrowBasis (L.y.take 255) L.carry L.bias K b)).map Bool.not := by
    rw [List.map_map]; apply List.map_congr_left; intro q hq; simp [cmpBasisOdd, hq]
  have hys : (L.y.take 255).map (borrowBasis (L.y.take 255) L.carry L.bias K b) = (L.y.take 255).map b := by
    apply List.map_congr_left; intro q hq
    exact borrow_outside _ _ _ _ _ q (carry_source_away L fixed_nodup q (Or.inl (List.mem_of_mem_take hq)))
  have hbi : borrowBasis (L.y.take 255) L.carry L.bias K b L.bias = false := by
    rw [borrow_outside _ _ _ _ _ L.bias (carry_source_away L fixed_nodup L.bias (Or.inr (Or.inr (Or.inr rfl)))), hb]
  have hall : L.carry.map (cmpBasisOdd L b) = cmpSteps ((L.y.take 255).map b) (literalBits 255 K) true := by
    rw [hmap, hvals, borrowValues_ge, hys, hbi]; rfl
  have h13 := congrArg (fun l : List Bool => l.take 13) hall
  dsimp only at h13
  rw [← List.map_take, carry13, cmpSteps_take, ← List.map_take, source13,
    literalBits_take 13 255 K (by decide),
    show literalBits 13 K = [true, false, true, true, true, false, true, false, true, true, true, true, true] from literal13] at h13
  have hget := congrArg (fun l : List Bool => l.getD j.val false) h13
  have hlhs : (((List.range 13).map L.A).map (cmpBasisOdd L b)).getD j.val false =
      cmpBasisOdd L b (L.A j.val) := by
    rw [List.map_map]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.isLt,
      Option.map_some, Option.getD_some, Function.comp_apply]
  have hrhs : (cmpSteps (((List.range 13).map L.Y).map b)
      [true, false, true, true, true, false, true, false, true, true, true, true, true] true).getD j.val false =
      comparisonOdd L b j.val := by
    simp only [comparisonOdd, comparisonOddValues, List.map_map, Function.comp_def]
  exact hlhs.symm.trans (hget.trans hrhs)

private theorem clearQuotientOdd_correct (s : State) (m : List Bool)
    (clean : ∀ q ∈ fixedLayout.carry, s.basis q = false)
    (hb : s.basis fixedLayout.bias = false)
    (quotient : s.basis fixedLayout.h =
      (!s.basis fixedLayout.sigma && !(decide (regValue (fixedLayout.y.take 255) s.basis < K)))) :
    run (cmpFrontOdd ++ cmpBackOdd ++ [.X fixedLayout.sigma]) m s =
      ⟨s.phase, writeBit s.basis fixedLayout.h false⟩ := by
  let L := fixedLayout
  have hnd : (L.sigma :: L.h :: L.bias :: (L.y.take 255 ++ L.carry)).Nodup := cmp_nodup_full
  have hndc : L.carry.Nodup := carry_nd L fixed_nodup
  have hbz := borrowPath_zero (L.y.take 255) L.carry L.bias K
  have hiz : measurementCount (invertCarry L) = 0 := (notRegister_counts L.carry).2
  have hfs : L.sigma ∉ wires (borrowPath false (L.y.take 255) L.carry L.bias K) := by
    intro hq; have hm := borrowPath_wires false (L.y.take 255) L.carry L.bias K hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hm
    have h1 : L.sigma ≠ L.bias := by decide +kernel
    have h2 : L.sigma ∉ L.y := flag_y_away L fixed_nodup L.sigma (by simp)
    have h3 : L.sigma ∉ L.carry := carry_source_away L fixed_nodup L.sigma (Or.inr (Or.inl rfl))
    rcases hm with e | hy | hc
    · exact h1 e
    · exact h2 (List.mem_of_mem_take hy)
    · exact h3 hc
  have hfh : L.h ∉ wires (borrowPath false (L.y.take 255) L.carry L.bias K) := by
    intro hq; have hm := borrowPath_wires false (L.y.take 255) L.carry L.bias K hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hm
    have h1 : L.h ≠ L.bias := by decide +kernel
    have h2 : L.h ∉ L.y := flag_y_away L fixed_nodup L.h (by simp)
    have h3 : L.h ∉ L.carry := carry_source_away L fixed_nodup L.h (Or.inr (Or.inr (Or.inl rfl)))
    rcases hm with e | hy | hc
    · exact h1 e
    · exact h2 (List.mem_of_mem_take hy)
    · exact h3 hc
  -- Collapse `cmpFrontOdd ++ cmpBackOdd ++ [.X sigma]` into `[.X sigma, .CX sigma h] ++ eraseSelected ++ [.X sigma]`
  let tail : Program :=
    [.measureX L.h [] [.CZ L.sigma (L.carry.getLastD L.bias)]] ++
      borrowPath true (L.y.take 255) L.carry L.bias K
  have hshape : cmpFrontOdd ++ cmpBackOdd ++ [.X L.sigma] =
      ((borrowPath false (L.y.take 255) L.carry L.bias K ++ invertCarry L ++ invertCarry L) ++
        [.X L.sigma, .CX L.sigma L.h]) ++ tail ++ [.X L.sigma] := by
    simp only [cmpFrontOdd, cmpBackOdd, tail, xs, cs, L, List.append_assoc, List.cons_append, List.nil_append]
  have hsh2 : run (cmpFrontOdd ++ cmpBackOdd ++ [.X L.sigma]) m s =
      run [.X L.sigma] []
        (run (eraseSelected (L.y.take 255) L.carry L.bias L.sigma L.h K) m
          (run [.X L.sigma, .CX L.sigma L.h] [] s)) := by
    rw [hshape]
    simp only [run_append, run_take, measurementCount_append, hbz, hiz, Nat.zero_add,
      List.take_zero, List.drop_zero, show measurementCount ([.X L.sigma, .CX L.sigma L.h] : Program) = 0 from by simp [measurementCount]]
    rw [show run (invertCarry L) [] (run (invertCarry L) [] (run (borrowPath false (L.y.take 255) L.carry L.bias K) [] s)) =
          run (borrowPath false (L.y.take 255) L.carry L.bias K) [] s from notRegister_twice L.carry hndc _ [] []]
    rw [← run_flagPre_outside _ L.sigma L.h hfs hfh]
    have her : run (eraseSelected (L.y.take 255) L.carry L.bias L.sigma L.h K) m
        (run [.X L.sigma, .CX L.sigma L.h] [] s) =
        run tail m (run (borrowPath false (L.y.take 255) L.carry L.bias K) []
          (run [.X L.sigma, .CX L.sigma L.h] [] s)) := by
      simp only [eraseSelected, tail, run_append, hbz, List.take_zero, List.drop_zero]
    rw [← her]
    exact FifthCarry.no_records [.X L.sigma] (by simp [measurementCount]) _ _ []
  rw [hsh2]
  have hhs : L.h ≠ L.sigma := by decide +kernel
  have hbs : L.bias ≠ L.sigma := by decide +kernel
  have hbh : L.bias ≠ L.h := by decide +kernel
  let u : State := ⟨s.phase, writeBit (writeBit s.basis L.sigma (!(s.basis L.sigma)))
    L.h (s.basis L.h ^^ !(s.basis L.sigma))⟩
  have hu : run [.X L.sigma, .CX L.sigma L.h] [] s = u := by
    simp [run, u, writeBit, hhs]
  rw [hu]
  have uclean : ∀ q ∈ L.carry, u.basis q = false := fun q hq => by
    have qs : q ≠ L.sigma := fun e => carry_source_away L fixed_nodup L.sigma (Or.inr (Or.inl rfl)) (e ▸ hq)
    have qh : q ≠ L.h := fun e => carry_source_away L fixed_nodup L.h (Or.inr (Or.inr (Or.inl rfl))) (e ▸ hq)
    simp [u, writeBit, qh, qs, clean q hq]
  have uknown : u.basis L.h = (u.basis L.sigma && decide (regValue (L.y.take 255) u.basis < K + (u.basis L.bias).toNat)) := by
    have uy : regValue (L.y.take 255) u.basis = regValue (L.y.take 255) s.basis := by
      apply regValue_congr; intro q hq
      have qs : q ≠ L.sigma := fun e => flag_y_away L fixed_nodup L.sigma (by simp) (e ▸ List.mem_of_mem_take hq)
      have qh : q ≠ L.h := fun e => flag_y_away L fixed_nodup L.h (by simp) (e ▸ List.mem_of_mem_take hq)
      simp [u, writeBit, qh, qs]
    have ub : u.basis L.bias = false := by
      simp only [u, writeBit, Function.update_of_ne hbh, Function.update_of_ne hbs]; exact hb
    have us : u.basis L.sigma = !(s.basis L.sigma) := by simp [u, writeBit, hhs.symm]
    have uh : u.basis L.h = (s.basis L.h ^^ !(s.basis L.sigma)) := by simp [u, writeBit]
    rw [uh, us, uy, ub, quotient]
    simp only [Bool.toNat_false, Nat.add_zero]
    exact (show ∀ a b : Bool, ((a && !b) ^^ a) = (a && b) from by decide) _ _
  have hly : L.y.length = 256 := fixed_widths.1
  have hlc : L.carry.length = 255 := fixed_widths.2.2
  rw [eraseSelected_correct _ _ _ _ _ _ hnd (by simp [hly]) (by simp [hly, hlc])
    (by simp only [List.length_take, hly]; norm_num [K, p]) u m uclean uknown]
  rw [BalancedCleanupOffset.x_run]
  apply State.extensionality
  · rfl
  · funext q
    by_cases hqh : q = L.h
    · subst hqh; simp [u, writeBit, hhs, L]
    · by_cases hqs : q = L.sigma
      · subst hqs; simp [u, writeBit, hhs.symm, L]
      · simp [u, writeBit, hqh, hqs, L]

private theorem cmpFrontOdd_mc : measurementCount cmpFrontOdd = 0 := by
  rw [show cmpFrontOdd = borrowPath false xs cs fixedLayout.bias K ++ notRegister fixedLayout.carry from rfl,
    measurementCount_append, borrowPath_zero, (notRegister_counts fixedLayout.carry).2]

private theorem cmpBackOdd_eq :
    cmpBackOdd = invertCarry fixedLayout ++
      [.X fixedLayout.sigma, .CX fixedLayout.sigma fixedLayout.h,
       .measureX fixedLayout.h [] [.CZ fixedLayout.sigma (fixedLayout.carry.getLastD fixedLayout.bias)]] ++
      borrowPath true xs cs fixedLayout.bias K := rfl

attribute [local irreducible] cmpFrontOdd cmpBackOdd lowBlockOdd window760Odd0

private theorem window760Odd0_correct (ref : BasisState)
    (hbits : ∀ j, j < 256 → ref (fixedLayout.R j) = oddRbit fixedLayout ref j)
    (hscalar : regValue fixedLayout.r ref =
      ((if ref fixedLayout.sigma then regValue (fixedLayout.y.take 255) ref
        else 3 * regValue (fixedLayout.y.take 255) ref + 1) +
        (ref fixedLayout.h).toNat * (2 ^ 32 + 977)) % 2 ^ 256)
    (hexcl : (ref fixedLayout.sigma && ref fixedLayout.h) = false)
    (s : State) (src : SourceData fixedLayout ref s) (rs : Pending fixedLayout ref 13 s)
    (clean : ∀ q ∈ fixedLayout.carry, s.basis q = false) (bias : s.basis fixedLayout.bias = false)
    (quotient : s.basis fixedLayout.h =
      (!s.basis fixedLayout.sigma && !(decide (regValue (fixedLayout.y.take 255) s.basis < K))))
    (m : List Bool) :
    run (window760Odd0 ++ [.X fixedLayout.sigma]) m s =
      ⟨s.phase, maskBasis ((List.range 13).map fixedLayout.R) (writeBit s.basis fixedLayout.h false)⟩ := by
  let L := fixedLayout
  have hreq : run (window760Odd0 ++ [.X L.sigma]) m s =
      run (cmpFrontOdd ++ lowBlockOdd L ++ cmpBackOdd ++ [.X L.sigma]) m s := by
    have h := (window760Odd0_REq.append (LREq.refl [Instr.X L.sigma])).2 m s
    simpa only [List.append_assoc] using h.symm
  rw [hreq]
  have hf0 : measurementCount cmpFrontOdd = 0 := cmpFrontOdd_mc
  have hlowM : measurementCount (lowBlockOdd L) = 14 := lowBlockOdd_mc
  let u : State := ⟨s.phase, cmpBasisOdd L s.basis⟩
  have usrc : SourceData L ref u := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      exact (cmpBasisOdd_outside s.basis _ (carry_source_away L fixed_nodup _ (Or.inl (y_mem L fixed_widths j hj)))).trans (src.source j hj)
    · exact (cmpBasisOdd_outside s.basis L.sigma (carry_source_away L fixed_nodup L.sigma (Or.inr (Or.inl rfl)))).trans src.sigma
    · exact (cmpBasisOdd_outside s.basis L.h (carry_source_away L fixed_nodup L.h (Or.inr (Or.inr (Or.inl rfl))))).trans src.h
  have urs : Pending L ref 13 u := fun j hj =>
    (cmpBasisOdd_outside s.basis _ (fun hc => source_r_away L fixed_nodup _ (Or.inr (Or.inl hc)) (r_mem L fixed_widths j (by omega)))).trans (rs j hj)
  have ubias : u.basis L.bias = false :=
    (cmpBasisOdd_outside s.basis L.bias (carry_source_away L fixed_nodup L.bias (Or.inr (Or.inr (Or.inr rfl))))).trans bias
  have ucmp : ∀ j, 3 ≤ j → j < 13 → u.basis (L.A j) = comparisonOdd L ref j := fun j _ hj => by
    change cmpBasisOdd fixedLayout s.basis (fixedLayout.A j) = comparisonOdd L ref j
    rw [cmpBasisOdd_comparison s.basis clean bias ⟨j, hj⟩]
    have hys : (List.range 13).map (fun k => s.basis (L.Y k)) = (List.range 13).map (fun k => ref (L.Y k)) :=
      List.map_congr_left (fun k hk => src.source k (by have := List.mem_range.mp hk; omega))
    unfold comparisonOdd comparisonOddValues
    rw [hys]
  have her := lowBlockOdd_correct ref hbits hscalar hexcl u usrc urs ucmp ubias (m.take 14)
  have heqBody := erased_eq L.R 13 u (run (lowBlockOdd L) (m.take 14) u) her
  have hfree : ∀ q ∈ (List.range 13).map L.R, q ∉ wires (cmpBackOdd ++ [.X L.sigma]) := by
    intro q hq hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    have hilt : i < 256 := by have := List.mem_range.mp hi; omega
    have hqr : L.R i ∈ L.r := r_mem L fixed_widths i hilt
    have hny : L.R i ∉ xs := fun h => source_r_away L fixed_nodup _ (Or.inl (List.mem_of_mem_take h)) hqr
    have hnc : L.R i ∉ cs := fun h => source_r_away L fixed_nodup _ (Or.inr (Or.inl h)) hqr
    have hns : L.R i ≠ L.sigma := (flag_ne_r L fixed_widths fixed_nodup L.sigma (Or.inl rfl) i hilt).symm
    have hnh : L.R i ≠ L.h := (flag_ne_r L fixed_widths fixed_nodup L.h (Or.inr (Or.inl rfl)) i hilt).symm
    have hnb : L.R i ≠ L.bias := (flag_ne_r L fixed_widths fixed_nodup L.bias (Or.inr (Or.inr rfl)) i hilt).symm
    rw [cmpBackOdd_eq] at hw
    simp only [wires_append, Finset.mem_union] at hw
    rcases hw with ((hi' | hm') | hb) | hx
    · have : L.R i ∈ cs := by
        change L.R i ∈ wires (notRegister cs) at hi'; rw [notRegister_wires] at hi'; exact List.mem_toFinset.mp hi'
      exact hnc this
    · have hlast : L.carry.getLastD L.bias ∈ cs := by decide +kernel
      simp only [wires, Instr.wires, correctionWires, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.notMem_empty, or_false] at hm'
      rcases hm' with e | (e | e) | e | (e | e)
      · exact hns e
      · exact hns e
      · exact hnh e
      · exact hnh e
      · exact hns e
      · exact hnc (e ▸ hlast)
    · have hbm := borrowPath_wires true xs cs L.bias K hb
      simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hbm
      rcases hbm with e | hx | hc
      · exact hnb e
      · exact hny hx
      · exact hnc hc
    · exact hns (by simpa [wires, Instr.wires] using hx)
  have hpair := clearQuotientOdd_correct s (m.drop 14) clean bias quotient
  have hsplit1 : cmpFrontOdd ++ cmpBackOdd ++ [.X L.sigma] = cmpFrontOdd ++ (cmpBackOdd ++ [.X L.sigma]) := by
    simp only [List.append_assoc]
  rw [hsplit1, run_append, hf0, List.take_zero, List.drop_zero, cmpFrontOdd_run] at hpair
  have hsplit2 : cmpFrontOdd ++ lowBlockOdd L ++ cmpBackOdd ++ [.X L.sigma] =
      (cmpFrontOdd ++ lowBlockOdd L) ++ (cmpBackOdd ++ [.X L.sigma]) := by
    simp only [List.append_assoc]
  rw [hsplit2, run_append, measurementCount_append, hf0, hlowM, Nat.zero_add]
  have hpre : run (cmpFrontOdd ++ lowBlockOdd L) (m.take 14) s = run (lowBlockOdd L) (m.take 14) u := by
    rw [run_append, hf0, List.take_zero, List.drop_zero, cmpFrontOdd_run]
  have hrm := run_mask (cmpBackOdd ++ [.X L.sigma]) ((List.range 13).map L.R) hfree u (m.drop 14)
  rw [hpre, heqBody]
  exact hrm.trans (by rw [show u = ⟨s.phase, cmpBasisOdd fixedLayout s.basis⟩ from rfl, hpair])

/-! ## Complete `cellDecoderOddLoan_correct` and `endPacket760DivOddLoan_frame` -/

private theorem cellDecoderOddLoan_split :
    cellDecoderOddLoan =
      frontFastOdd fixedLayout ++
        (upperStages fixedLayout ++
          ((StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0 ++ [.X fixedLayout.sigma]) ++
            back fixedLayout)) := by
  simp only [cellDecoderOddLoan, upperStages, back, List.append_assoc]

attribute [local irreducible] cellDecoderOddLoan

private theorem endPacket760DivOddLoan_eq :
    endPacket760DivOddLoan =
      renameProgram (Equiv.swap (base 760) (base 717))
        (renameProgram (shifted Placement5.pi0)
          (ControlLoan1589.loanWindow (base 510) (base 2409) (base 719)
            (cellDecoderOddLoan ++ List.replicate 507 (Instr.measureX (base 512) [] [])))) := by
  unfold endPacket760DivOddLoan k5Wrap; rfl

attribute [local irreducible] endPacket760DivOddLoan
  frontFastOdd upperStages back ControlLoan1589.loanWindow

theorem cellDecoderOddLoan_correct (Y : Fp) (sigma : Bool) (s : State) (m : List Bool)
    (ys : regValue fixedLayout.y s.basis = oddWord Y)
    (rs : regValue fixedLayout.r s.basis = oddWord ((if sigma then 1 else 3) * Y))
    (sig : s.basis fixedLayout.sigma = sigma)
    (hc : s.basis fixedLayout.h = false)
    (bc : s.basis fixedLayout.bias = false)
    (cc : ∀ q ∈ fixedLayout.carry, s.basis q = false) :
    (run cellDecoderOddLoan m s).phase = s.phase ∧
    (∀ q, q ∉ fixedLayout.r → (run cellDecoderOddLoan m s).basis q = s.basis q) ∧
    regValue fixedLayout.r (run cellDecoderOddLoan m s).basis = oddWord Y := by
  let L := fixedLayout
  obtain ⟨f, hfDef⟩ : ∃ f : State, f = run (frontFastOdd L) (m.take (measurementCount (frontFastOdd L))) s := ⟨_, rfl⟩
  have hf := frontFastOdd_spec Y sigma s (m.take (measurementCount (frontFastOdd L))) ys rs sig hc bc cc
  dsimp only at hf
  rw [← hfDef] at hf
  obtain ⟨hf_ph, hf_sig, hf_h, hf_bias, hf_carry, hf_sc, hf_out, hf_ytake⟩ := hf
  have hf_excl : (f.basis L.sigma && f.basis L.h) = false := by
    rw [hf_sig, hf_h]; cases sigma <;> simp
  have hf_sc' : regValue L.r f.basis =
      ((if f.basis L.sigma then regValue (L.y.take 255) f.basis else 3 * regValue (L.y.take 255) f.basis + 1) +
        (f.basis L.h).toNat * (2 ^ 32 + 977)) % 2 ^ 256 := by
    rw [hf_sig, hf_h]; exact hf_sc
  have hbits : ∀ j, j < 256 → f.basis (L.R j) = oddRbit L f.basis j :=
    odd_bits_spec L fixed_widths f.basis hf_sc'
  have hca : ∀ k, k < 255 → f.basis (L.A k) = false := fun k hk => hf_carry _ (a_mem L fixed_widths k hk)
  let m1 := m.drop (measurementCount (frontFastOdd L))
  obtain ⟨w, hwDef⟩ : ∃ w : State, w = run (upperStages L) (m1.take (measurementCount (upperStages L))) f := ⟨_, rfl⟩
  have her := odd_upperStages_correct f.basis hbits hf_excl f rfl hca (m1.take (measurementCount (upperStages L)))
  rw [← hwDef] at her
  have hw_eq : w = ⟨f.phase, maskBasis ((List.range 243).map (fun i => L.R (13 + i))) f.basis⟩ :=
    erased_eq (fun i => L.R (13 + i)) 243 f w her
  have hw_src : SourceData L f.basis w :=
    range_source L fixed_widths fixed_nodup 13 243 (by decide) f.basis f w her ⟨fun _ _ => rfl, rfl, rfl⟩
  have hw_rs : Pending L f.basis 13 w :=
    range_pending L fixed_widths fixed_nodup 13 243 (by decide) f.basis f w her (fun _ _ => rfl)
  have hw_carry : ∀ q ∈ L.carry, w.basis q = false := fun q hq => by
    have hnr : q ∉ L.r := fun hr => source_r_away L fixed_nodup q (Or.inr (Or.inl hq)) hr
    exact (range_outside L fixed_widths 13 243 (by decide) f w her q hnr).trans (hf_carry q hq)
  have hw_bias : w.basis L.bias = false :=
    (range_outside L fixed_widths 13 243 (by decide) f w her L.bias
      (source_r_away L fixed_nodup L.bias (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))).trans hf_bias
  have hw_quot : w.basis L.h = (!w.basis L.sigma && !(decide (regValue (L.y.take 255) w.basis < K))) := by
    have hvy : regValue (L.y.take 255) w.basis = regValue (L.y.take 255) f.basis := by
      apply regValue_congr; intro q hq
      exact range_outside L fixed_widths 13 243 (by decide) f w her q
        (source_r_away L fixed_nodup q (Or.inl (List.mem_of_mem_take hq)))
    rw [hw_src.h, hw_src.sigma, hvy, hf_sig]; exact hf_h
  -- Drop `rebindMany exclusiveHoles rHosts44 window760Odd0` -> `window760Odd0`
  let m2 := m1.drop (measurementCount (upperStages L))
  have hholes_in : ∀ q ∈ StairBoundaryLoan.exclusiveHoles, w.basis q = false := fun q hq =>
    hw_carry q (CompareDecoder.BoundaryLoan.Inclusion.holes_in_carry q hq)
  have hr44_in : ∀ q ∈ rHosts44, w.basis q = false := fun q hq => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    have hb := List.mem_range'_1.mp hi
    have hcl := her.cleared (i - 13) (by omega)
    simpa only [show 13 + (i - 13) = i by omega] using hcl
  have hwin_res := window760Odd0_correct f.basis hbits hf_sc' hf_excl w hw_src hw_rs hw_carry hw_bias hw_quot
    (m2.take (measurementCount (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0 ++ [.X L.sigma])))
  have hwin_rest : ∀ q ∈ StairBoundaryLoan.exclusiveHoles,
      (run window760Odd0 (m2.take (measurementCount (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0))) w).basis q = false := by
    intro q hq
    have hq_sig : q ≠ L.sigma := by
      have hc := CompareDecoder.BoundaryLoan.Inclusion.holes_in_carry q hq
      exact fun e => carry_source_away L fixed_nodup L.sigma (Or.inr (Or.inl rfl)) (e ▸ hc)
    have hq_h : q ≠ L.h := by
      have hc := CompareDecoder.BoundaryLoan.Inclusion.holes_in_carry q hq
      exact fun e => carry_source_away L fixed_nodup L.h (Or.inr (Or.inr (Or.inl rfl))) (e ▸ hc)
    have hq_r : q ∉ (List.range 13).map L.R := by
      intro hm; obtain ⟨i, hi, heq⟩ := List.mem_map.mp hm
      exact source_r_away L fixed_nodup q (Or.inr (Or.inl (CompareDecoder.BoundaryLoan.Inclusion.holes_in_carry q hq)))
        (heq ▸ r_mem L fixed_widths i (by have := List.mem_range.mp hi; omega))
    have hstep := window760Odd0_correct f.basis hbits hf_sc' hf_excl w hw_src hw_rs hw_carry hw_bias hw_quot
      (m2.take (measurementCount (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0)))
    rw [run_append, run_take] at hstep
    have hx := congrArg (fun st => st.basis q) hstep
    rw [BalancedCleanupOffset.x_run] at hx
    simp only [L, writeBit, Function.update_of_ne hq_sig, maskBasis, if_neg hq_r, Function.update_of_ne hq_h] at hx
    exact hx.trans (hholes_in q hq)
  have hdrop := window760OddLoan_run_eq w
    (m2.take (measurementCount (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0)))
    hholes_in hr44_in hwin_rest
  have hwin_loan : run (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0 ++ [.X L.sigma])
      (m2.take (measurementCount (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0 ++ [.X L.sigma]))) w =
      ⟨f.phase, writeBit (maskBasis L.r f.basis) L.h false⟩ := by
    have hmc : measurementCount (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0 ++ [.X L.sigma]) =
        measurementCount (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0) := by
      simp [measurementCount_append, measurementCount]
    rw [hmc, run_append, run_take, hdrop]
    let mt := m2.take (measurementCount (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0))
    have hwin2 := window760Odd0_correct f.basis hbits hf_sc' hf_excl w hw_src hw_rs hw_carry hw_bias hw_quot mt
    rw [run_append, run_take] at hwin2
    have hnx : run [.X L.sigma] (mt.drop (measurementCount (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0)))
        (run window760Odd0 mt w) =
        run [.X L.sigma] (mt.drop (measurementCount window760Odd0)) (run window760Odd0 mt w) :=
      FifthCarry.no_records [.X L.sigma] (by simp [measurementCount]) _ _ _
    rw [hnx, hwin2, hw_eq]
    apply State.extensionality
    · rfl
    · funext q
      have hlr : ∀ i, i < 256 → L.R i ∈ L.r := fun i hi => r_mem L fixed_widths i hi
      by_cases hqh : q = L.h
      · subst hqh
        have hnh13 : L.h ∉ (List.range 13).map L.R := by
          intro hm; obtain ⟨i, hi, he⟩ := List.mem_map.mp hm
          exact source_r_away L fixed_nodup L.h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (he ▸ hlr i (by have := List.mem_range.mp hi; omega))
        simp [L, maskBasis, writeBit, hnh13]
      · by_cases hqr : q ∈ L.r
        · obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hqr
          have hilt : i < 256 := by rw [fixed_widths.2.1] at hi; exact hi
          have hqeq : q = L.R i := by
            rw [← hri]; unfold DecoderLayout.R; rw [List.getD_eq_getElem _ _ hi]
          by_cases h13 : i < 13
          · have hm13 : q ∈ (List.range 13).map L.R :=
              List.mem_map.mpr ⟨i, List.mem_range.mpr h13, hqeq.symm⟩
            simp [L, maskBasis, writeBit, hqh, hqr, hm13]
          · have hm243 : q ∈ (List.range 243).map (fun k => L.R (13 + k)) :=
              List.mem_map.mpr ⟨i - 13, List.mem_range.mpr (by omega), by simpa [show 13 + (i - 13) = i by omega] using hqeq.symm⟩
            have hnm13 : q ∉ (List.range 13).map L.R := by
              intro hm; obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
              have := result_inj L fixed_widths fixed_nodup j i (by have := List.mem_range.mp hj; omega) hilt (he.trans hqeq)
              have := List.mem_range.mp hj; omega
            simp [L, maskBasis, writeBit, hqh, hqr, hnm13, hm243]
        · have hnm13 : q ∉ (List.range 13).map L.R := by
            intro hm; obtain ⟨i, hi, he⟩ := List.mem_map.mp hm
            exact hqr (he ▸ hlr i (by have := List.mem_range.mp hi; omega))
          have hnm243 : q ∉ (List.range 243).map (fun k => L.R (13 + k)) := by
            intro hm; obtain ⟨i, hi, he⟩ := List.mem_map.mp hm
            exact hqr (he ▸ hlr (13 + i) (by have := List.mem_range.mp hi; omega))
          simp [L, maskBasis, writeBit, hqh, hqr, hnm13, hnm243]
  have hzeroR : (⟨f.phase, writeBit (maskBasis L.r f.basis) L.h false⟩ : State) = ⟨s.phase, zeroR L s.basis⟩ := by
    apply State.extensionality
    · exact hf_ph
    · funext q
      by_cases hqh : q = L.h
      · subst hqh
        have hnr : L.h ∉ L.r := source_r_away L fixed_nodup L.h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        have hny : L.h ∉ L.y.take 255 := fun h => flag_y_away L fixed_nodup L.h (by simp) (List.mem_of_mem_take h)
        simp [L, writeBit, zeroR, complementBasis, hnr, hny, hc]
      · by_cases hqr : q ∈ L.r
        · simp [L, writeBit, hqh, maskBasis, hqr, zeroR]
        · by_cases hqy : q ∈ L.y.take 255
          · simp [L, writeBit, hqh, maskBasis, hqr, zeroR, complementBasis, hqy, hf_ytake q hqy]
          · simp [L, writeBit, hqh, maskBasis, hqr, zeroR, complementBasis, hqy, hf_out q hqy hqr hqh]
  -- Assemble all 4 stages and apply `TerminalGraph.back_correct`
  have hfull : run cellDecoderOddLoan m s =
      run (back L) (m2.drop (measurementCount (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0 ++ [.X L.sigma])))
        ⟨s.phase, zeroR L s.basis⟩ := by
    rw [cellDecoderOddLoan_split, run_append, ← hfDef, run_append, ← hwDef, run_append, hwin_loan, hzeroR]
  rw [hfull]
  have hbk := TerminalGraph.back_correct L fixed_widths fixed_nodup s.basis s.phase
    (m2.drop (measurementCount (StairLoan.rebindMany StairBoundaryLoan.exclusiveHoles rHosts44 window760Odd0 ++ [.X L.sigma])))
  exact ⟨hbk.1, hbk.2.1, hbk.2.2.trans ys⟩

private theorem loanWindow_div_eq (g flag c : Wire) (P : Program) :
    ControlLoan1589.loanWindow g flag c P =
      [.CX g flag, .CX flag g] ++ (renameProgram (Equiv.swap c g) P ++ ([.CX flag g] ++ [.measureX flag [] [.Z g]])) := by
  unfold ControlLoan1589.loanWindow; simp only [List.append_assoc, List.cons_append, List.nil_append]

private theorem run_rename_eq_of_outside (f : Equiv.Perm Wire) (P : Program) (R : List Wire)
    (s : State) (m : List Bool)
    (hPull : pullState f s = s)
    (hfix : ∀ q ∈ R, f q = q)
    (hout : ∀ q, q ∉ R → (run P m s).basis q = s.basis q) :
    run (renameProgram f P) m s = run P m s := by
  have hren := run_rename f f.injective P m s
  rw [hPull] at hren
  apply State.extensionality
  · exact congrArg (fun st => st.phase) hren
  · funext q
    have hq := congrFun (congrArg State.basis hren) (f.symm q)
    simp only [pullState, Equiv.apply_symm_apply] at hq
    by_cases hqr : q ∈ R
    · have hf : f.symm q = q := f.symm_apply_eq.mpr (hfix q hqr).symm
      rw [hf] at hq; exact hq
    · have hsr : f.symm q ∉ R := fun mem =>
        hqr (by have := hfix _ mem; rw [Equiv.apply_symm_apply] at this; exact this ▸ mem)
      have hs : s.basis (f.symm q) = s.basis q := by
        have := congrFun (congrArg State.basis hPull) (f.symm q)
        simpa [pullState] using this.symm
      rw [hq, hout _ hsr, hs, hout _ hqr]

theorem endPacket760DivOddLoan_frame (Y : Fp) (s : State) (m : List Bool)
    (clean : Q6EndpointCell.Clean base s.basis)
    (flagIn : s.basis (base 2409) = false)
    (hY : regValue fixedLayout.y s.basis = oddWord Y)
    (hR : regValue fixedLayout.r s.basis = oddWord ((if s.basis (base 510) then 1 else 3) * Y))
    (hPull : pullState (shifted Placement5.pi0) s = s)
    (h760 : s.basis (base 760) = false)
    (h717 : s.basis (base 717) = false) :
    (run endPacket760DivOddLoan m s).phase = s.phase ∧
    regValue fixedLayout.r (run endPacket760DivOddLoan m s).basis = oddWord Y ∧
    ∀ a, a ∉ fixedLayout.r → (run endPacket760DivOddLoan m s).basis a = s.basis a := by
  let L := fixedLayout
  let g := base 510
  let flag := base 2409
  let c := base 719
  let padP := cellDecoderOddLoan ++ List.replicate 507 (Instr.measureX (base 512) [] [])
  have hpad : ∀ (st : State) (rec : List Bool),
      regValue L.y st.basis = oddWord Y →
      regValue L.r st.basis = oddWord ((if st.basis L.sigma then 1 else 3) * Y) →
      Q6EndpointCell.Clean base st.basis →
      (run padP rec st).phase = st.phase ∧
      regValue L.r (run padP rec st).basis = oddWord Y ∧
      ∀ a, a ∉ L.r → (run padP rec st).basis a = st.basis a := by
    intro st rec hYs hRs hcs
    have hch : st.basis L.h = false := hcs _ (by decide +kernel)
    have hcb : st.basis L.bias = false := hcs _ (by decide +kernel)
    have hcc : ∀ q ∈ L.carry, st.basis q = false := by
      have hchk : L.carry.all (fun w => decide (w ∈ Q6EndpointCell.workIds.map base)) = true := by decide +kernel
      intro q hq; exact hcs q (of_decide_eq_true (List.all_eq_true.mp hchk q hq))
    have hh := cellDecoderOddLoan_correct Y (st.basis L.sigma) st (rec.take (measurementCount cellDecoderOddLoan))
      hYs hRs rfl hch hcb hcc
    have h512_r : base 512 ∉ L.r := by decide +kernel
    have h512_0 : (run cellDecoderOddLoan (rec.take (measurementCount cellDecoderOddLoan)) st).basis (base 512) = false :=
      (hh.2.1 _ h512_r).trans (hcs _ (by decide +kernel))
    have hrep : ∀ (k : Nat) (x : State) (r : List Bool), x.basis (base 512) = false →
        run (List.replicate k (Instr.measureX (base 512) [] [])) r x = x := by
      intro k; induction k with
      | zero => intro x r _; simp [run]
      | succ k ih =>
        intro x r hx
        have hstep : run [Instr.measureX (base 512) [] []] r x = x := by
          have hr0 : run [Instr.measureX (base 512) [] []] r x = measureAndCorrect (base 512) [] [] (r.headD false) x := by simp [run]
          rw [hr0]; unfold measureAndCorrect
          cases r.headD false
          · show (⟨x.phase ^^ (false && x.basis (base 512)), writeBit x.basis (base 512) false⟩ : State) = x
            apply State.extensionality
            · simp [hx]
            · funext q; by_cases hq : q = base 512
              · subst q; simp [writeBit, hx]
              · simp [writeBit, hq]
          · show (⟨x.phase ^^ (true && x.basis (base 512)), writeBit x.basis (base 512) false⟩ : State) = x
            apply State.extensionality
            · simp [hx]
            · funext q; by_cases hq : q = base 512
              · subst q; simp [writeBit, hx]
              · simp [writeBit, hq]
        have hcons : List.replicate (k + 1) (Instr.measureX (base 512) [] []) =
            [Instr.measureX (base 512) [] []] ++ List.replicate k (Instr.measureX (base 512) [] []) := rfl
        rw [hcons, run_append, run_take, hstep]; exact ih x _ hx
    show (run (cellDecoderOddLoan ++ List.replicate 507 (Instr.measureX (base 512) [] [])) rec st).phase = _ ∧ _
    rw [run_append, hrep 507 _ _ h512_0]
    exact ⟨hh.1, hh.2.2, hh.2.1⟩
  have hraw : ∀ (rec : List Bool),
      (run (ControlLoan1589.loanWindow g flag c padP) rec s).phase = s.phase ∧
      regValue L.r (run (ControlLoan1589.loanWindow g flag c padP) rec s).basis = oddWord Y ∧
      ∀ a, a ∉ L.r → (run (ControlLoan1589.loanWindow g flag c padP) rec s).basis a = s.basis a := by
    intro rec
    have hgf : g ≠ flag := by decide +kernel
    have hcg : c ≠ g := by decide +kernel
    have hcf : c ≠ flag := by decide +kernel
    have hgR : g ∉ L.r := by decide +kernel
    have hgY : g ∉ L.y := by decide +kernel
    have hfR : flag ∉ L.r := by decide +kernel
    have hfY : flag ∉ L.y := by decide +kernel
    have hcR : c ∉ L.r := by decide +kernel
    have hfl : s.basis flag = false := flagIn
    obtain ⟨u, uDef⟩ : ∃ u : State, u = run ([.CX g flag, .CX flag g] : Program) [] s := ⟨_, rfl⟩
    have hu_eq : u = ⟨s.phase, writeBit (writeBit s.basis flag (s.basis flag ^^ s.basis g)) g (s.basis g ^^ (s.basis flag ^^ s.basis g))⟩ := by
      rw [uDef]; simp [run, writeBit, hgf]
    have ug : u.basis g = false := by
      rw [hu_eq]; simp only [writeBit, Function.update_self, hfl, Bool.false_xor, Bool.xor_self]
    have uf : u.basis flag = s.basis g := by
      rw [hu_eq]; simp only [writeBit, Function.update_of_ne hgf.symm, Function.update_self, hfl, Bool.false_xor]
    have ukeep (q : Wire) (hqg : q ≠ g) (hqf : q ≠ flag) : u.basis q = s.basis q := by
      rw [hu_eq]; simp [writeBit, hqg, hqf]
    have uc : u.basis c = false := (ukeep c hcg hcf).trans (clean c (by decide +kernel))
    have uclean : Q6EndpointCell.Clean base u.basis := by
      intro q hq
      have hchk : (Q6EndpointCell.workIds.map base).all (fun w => decide (w ≠ g ∧ w ≠ flag)) = true := by decide +kernel
      have hne := of_decide_eq_true (List.all_eq_true.mp hchk q hq)
      exact (ukeep q hne.1 hne.2).trans (clean q hq)
    have uY : regValue L.y u.basis = oddWord Y :=
      (regValue_congr _ _ _ (fun q hq => ukeep q (fun e => hgY (e ▸ hq)) (fun e => hfY (e ▸ hq)))).trans hY
    have uR : regValue L.r u.basis = oddWord ((if u.basis L.sigma then 1 else 3) * Y) := by
      have hsig_eq : L.sigma = flag := by decide +kernel
      rw [hsig_eq, uf]
      exact (regValue_congr _ _ _ (fun q hq => ukeep q (fun e => hgR (e ▸ hq)) (fun e => hfR (e ▸ hq)))).trans hR
    have hmid := hpad u rec uY uR uclean
    have hc_out : (run padP rec u).basis c = false := (hmid.2.2 c hcR).trans uc
    have hg_out : (run padP rec u).basis g = false := (hmid.2.2 g hgR).trans ug
    have hreb := FieldFrameOB5.rebind_swap_run c g padP u rec uc ug hc_out hg_out
    have hlw : run (ControlLoan1589.loanWindow g flag c padP) rec s =
        run [.measureX flag [] [.Z g]] (rec.drop (measurementCount (renameProgram (Equiv.swap c g) padP)))
          (run [.CX flag g] [] (run padP rec u)) := by
      rw [loanWindow_div_eq g flag c padP, run_append,
        show measurementCount ([.CX g flag, .CX flag g] : Program) = 0 from by simp [measurementCount],
        List.take_zero, List.drop_zero, ← uDef, run_append, run_take, run_append,
        show measurementCount ([.CX flag g] : Program) = 0 from by simp [measurementCount],
        List.take_zero, List.drop_zero, hreb]
    obtain ⟨w, wDef⟩ : ∃ w : State, w = run padP rec u := ⟨_, rfl⟩
    have hmid' : w.phase = u.phase ∧ regValue L.r w.basis = oddWord Y ∧
        ∀ a, a ∉ L.r → w.basis a = u.basis a := by rw [wDef]; exact hmid
    have hg_out' : w.basis g = false := by rw [wDef]; exact hg_out
    obtain ⟨v, vDef⟩ : ∃ v : State, v = run [.CX flag g] [] w := ⟨_, rfl⟩
    have hv_eq : v = ⟨w.phase, writeBit w.basis g (w.basis g ^^ w.basis flag)⟩ := by rw [vDef]; simp [run]
    have vfg : v.basis flag = v.basis g := by rw [hv_eq]; simp [writeBit, hgf.symm, hg_out']
    have hms := Rolling1588Lifetime.meas_sel flag g hgf.symm v vfg
      (rec.drop (measurementCount (renameProgram (Equiv.swap c g) padP)))
    rw [hlw, ← wDef, ← vDef, hms]
    have hup : u.phase = s.phase := by rw [hu_eq]
    refine ⟨(by rw [hv_eq]; exact hmid'.1.trans hup), ?_, ?_⟩
    · have hvR : regValue L.r (writeBit v.basis flag false) = regValue L.r w.basis := by
        apply regValue_congr; intro q hq
        rw [hv_eq]; simp [writeBit, show q ≠ flag from fun e => hfR (e ▸ hq), show q ≠ g from fun e => hgR (e ▸ hq)]
      rw [hvR, hmid'.2.1]
    · intro a ha
      by_cases af : a = flag
      · subst af; simp [writeBit, hfl]
      · by_cases ag : a = g
        · subst ag
          rw [hv_eq]; simp only [writeBit, Function.update_of_ne hgf, Function.update_self, hg_out', Bool.false_xor]
          exact (hmid'.2.2 flag hfR).trans uf
        · rw [hv_eq]; simp only [writeBit, Function.update_of_ne af, Function.update_of_ne ag]
          exact (hmid'.2.2 a ha).trans (ukeep a ag af)
  let P0 := ControlLoan1589.loanWindow g flag c padP
  have hpi_r : ∀ q ∈ L.r, shifted Placement5.pi0 q = q := by
    intro q hq
    rw [show L.r = (List.range' 2056 256).map base from by decide +kernel] at hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [shifted_base, Placement5.pi0_outside i]
    rintro (hw' | hh')
    · unfold Placement5.workRegion at hw'; omega
    · unfold Placement5.holeRegion at hh'; omega
  have h760_r : base 760 ∉ L.r := by decide +kernel
  have h717_r : base 717 ∉ L.r := by decide +kernel
  have hP1 : run (renameProgram (shifted Placement5.pi0) P0) m s = run P0 m s :=
    run_rename_eq_of_outside (shifted Placement5.pi0) P0 L.r s m hPull hpi_r (hraw m).2.2
  have h760_out : (run (renameProgram (shifted Placement5.pi0) P0) m s).basis (base 760) = false := by
    rw [hP1]; exact ((hraw m).2.2 _ h760_r).trans h760
  have h717_out : (run (renameProgram (shifted Placement5.pi0) P0) m s).basis (base 717) = false := by
    rw [hP1]; exact ((hraw m).2.2 _ h717_r).trans h717
  have hP2 : run endPacket760DivOddLoan m s = run P0 m s := by
    rw [endPacket760DivOddLoan_eq]
    rw [FieldFrameOB5.rebind_swap_run (base 760) (base 717) (renameProgram (shifted Placement5.pi0) P0) s m
      h760 h717 h760_out h717_out, hP1]
  rw [hP2]
  exact hraw m

end

end ECDSAAdd.Entrant.OddFullPass.CompareDecoderOdd
end
end
