import ECDSAAdd.Submission.Entrant.OddFieldB

/-! # Odd-word field replay, part (module split of OddField for replay) -/

-- file-level opens of OddField
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic MappedCompressed
open StairRestSupport ArchiveFieldScratch StairArchiveRelease

section

-- ============================================================================
-- Section 5: Loaned odd-word half-cell and tail groups (`P1LifeLoan`)
--   Includes 5-wire clean hosting on `shortConstAddLoan` (`d -> d - 5` on all
--   170 tail cells, saving 8 T / 9 M per cell = -1,360 T / -1,530 M total).
-- ============================================================================
section
set_option autoImplicit false
set_option maxRecDepth 24000
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.OddFullPass.P1LifeLoan
open Arithmetic Challenge RecordedQuantum MappedCompressed Secp256k1 BalancedField BalancedCircuit
open StairLoan OddFullPass

def orMajor (a b c : Wire) : Program :=
  [.X a, .X b, .CCX a b c, .X c, .X a, .X b]

def orErase (a b c : Wire) : Program :=
  [.measureX c [] [.Z a, .Z b, .CZ a b]]

def p1Seed (L : BalancedCircuit.Layout) : Program :=
  [.CX L.rmsb L.one, .CX (L.ylow.getD 0 0) L.parity,
   .CX L.r0 L.parity, .CX L.sign L.parity, .X L.parity]

def prepareCompare (L : BalancedCircuit.Layout) : Program :=
  rotateLeft L.r ++ [.X L.r0, .CX L.lower L.r0] ++
    signComplement L.sign L.y ++ signComplement L.lower L.y ++
    [.X L.rmsb, .X L.ymsb]

def exposure (L : BalancedCircuit.Layout) : Program :=
  [.X L.lower, .CX L.r0 L.lower]

/-- Clean unused cell wires during `shortConstAddLoan d`:
    - For `d ≤ 41`: all 5 wires `[base 763, base 764, base 1540, base 768, base 1027]`
      are clean (`false`), unused by `shortConstAdd`, and disjoint from `retiredRoles.take d`.
    - For `d = 43`: `base 763 = retiredRoles[42]` is already excluded from `L.carry.take 251`,
      and the remaining 4 wires `[base 764, base 1540, base 768, base 1027]` are clean and free.
    In both cases the effective carry-loan depth drops uniformly to `d - 5`! -/
def shortFreeHosts (d : Nat) : List Wire :=
  if d ≤ 41 then [base 763, base 764, base 1540, base 768, base 1027]
  else [base 764, base 1540, base 768, base 1027]

def shortConstAddLoan (d : Nat) (L : BalancedCircuit.Layout) (k : Nat) : Program :=
  if d < 6 then
    literalConstAddLoan d retiredRoles (L.low.drop 3) (L.carry.take 251)
      (L.low.getD 2 0) L.one (k / 8) ++ [.X (L.low.getD 2 0)]
  else
    let free := shortFreeHosts d
    let dEff := Nat.min d 42 - free.length
    let remRoles := (retiredRoles.take (Nat.min d 42)).drop dEff
    StairLoan.rebindMany remRoles free
      (literalConstAddLoan dEff retiredRoles (L.low.drop 3) (L.carry.take 251)
        (L.low.getD 2 0) L.one (k / 8)) ++ [.X (L.low.getD 2 0)]

def rawAddLoan (d : Nat) (L : BalancedCircuit.Layout) : Program :=
  let ys := L.ylow
  let rs := L.low
  let cs := (Q6Structural.q6Carry L).take 255
  let a := ys.getD 0 0
  let b := rs.getD 0 0
  let c := cs.getD 0 0
  let clear := [Instr.CX L.parity b, .CX a b, .X b]
  signComplement L.sign L.y ++ orMajor a b c ++ clear ++
    Q6LifetimeResearch.move (base 760) b
      (addPrefixLoan d retiredRoles (ys.drop 1) (rs.drop 1) (cs.drop 1)
        L.ymsb L.rmsb L.one c) ++ clear.reverse ++
    orErase a b c ++ [.CX a b, .X b] ++ signComplement L.sign L.y

def foldLoan (d : Nat) (L : BalancedCircuit.Layout) : Program :=
  [.CCX L.parity L.lower L.one, .CX L.lower L.rmsb] ++
    Q6LifetimeResearch.move (base 760) L.rmsb
      (mappedAddLoan d retiredRoles (ShortBiasedFold.lowBits L) L.low
        (L.carry.take 254) L.one) ++
    [.CX L.lower L.rmsb, .CX L.parity L.rmsb, .X L.rmsb,
     .CX L.parity L.lower, .CX L.rmsb L.lower, .X L.lower,
     .measureX L.one [] [.CZ L.parity L.rmsb]]

def unfoldLoan (d : Nat) (L : BalancedCircuit.Layout) : Program :=
  [.CX L.parity L.lower, .CX L.rmsb L.lower, .X L.lower,
   .CCX L.parity L.lower L.one, .CX L.lower L.rmsb,
   .CX L.parity L.rmsb, .X L.rmsb] ++
    Q6LifetimeResearch.move (base 760) L.rmsb
      (mappedSubLoan d retiredRoles (ShortBiasedFold.lowBits L) L.low
        (L.carry.take 254) L.one) ++
    [.CX L.lower L.rmsb, .CX L.rmsb L.lower,
     .measureX L.one [] [.CZ L.parity L.rmsb]]

def compareBlockLoan (d : Nat) (forward : Bool) (L : BalancedCircuit.Layout) : Program :=
  let a := L.r.getD 0 0
  let b := L.y.getD 0 0
  let cs := (Q6Structural.q6Carry L).take 255
  let c := cs.getD 0 0
  let nr := notRegister (L.one :: L.y)
  nr ++ majority a b L.one c ++ [.X L.one] ++
    Q6LifetimeResearch.move (base 760) L.one
      (compareLoan d retiredRoles forward (L.r.drop 1) (L.y.drop 1)
        (cs.drop 1) c L.parity) ++
    [.X L.one] ++ eraseCarry a b L.one c ++ nr

def rawSubLoan (d : Nat) (L : BalancedCircuit.Layout) : Program :=
  let xs := GuardCompression.source L
  let ys := BalancedCircuit.rawTarget L
  let cs := (Q6Structural.q6Carry L).take 255
  let a := xs.getD 0 0
  let b := ys.getD 0 0
  let c := cs.getD 0 0
  signComplement L.sign L.y ++ notRegister ys ++ orMajor a b c ++
    [.X b, .CX L.parity b] ++
    Q6LifetimeResearch.move (base 760) b
      (addTopLoan d retiredRoles (xs.drop 1) (ys.drop 1) (cs.drop 1) c) ++
    [.CX L.parity b, .X b] ++ orErase a b c ++ [.CX a b, .X b] ++
    notRegister ys ++ signComplement L.sign L.y ++
    [.CX b L.parity, .CX (L.ylow.getD 0 0) L.parity, .CX L.sign L.parity,
     .X L.parity, .CX L.rmsb L.one]

def forwardLoan (d : Nat) (L : BalancedCircuit.Layout) : Program :=
  p1Seed L ++ rawAddLoan d L ++ OneReuse.newPrepare L ++
    rotateRight (BalancedCircuit.rawTarget L) ++ foldLoan d L ++
    BalancedCleanup.prepareSign L.toLayout ++ BiasedCircuit.flipBias L ++
    prepareCompare L ++ exposure L ++ compareBlockLoan d true L ++
    (exposure L).reverse ++ (prepareCompare L).reverse ++
    Q6LifetimeResearch.move (base 760) L.rmsb (shortConstAddLoan d L h.toNat) ++
    (BalancedCleanup.prepareSign L.toLayout).reverse

def inverseLoan (d : Nat) (L : BalancedCircuit.Layout) : Program :=
  BalancedCleanup.prepareSign L.toLayout ++
    Q6LifetimeResearch.move (base 760) L.rmsb (shortConstAddLoan d L (encodeWord 255 (-h))) ++
    prepareCompare L ++ exposure L ++ compareBlockLoan d false L ++
    (exposure L).reverse ++ (prepareCompare L).reverse ++ BiasedInverse.unbiasView L ++
    unfoldLoan d L ++ rotateLeft (BalancedCircuit.rawTarget L) ++
    [.CX L.parity L.r0] ++ rawSubLoan d L

def half760OddLoan (d : Nat) (divide : Bool) : Program :=
  let L := Q6EndpointCell.ports base (base 2409)
  [.X (base 2409)] ++ (if divide then forwardLoan d L else inverseLoan d L) ++ [.X (base 2409)]

def halfWindow (divide : Bool) (d j active hole : Nat) : Program :=
  ControlLoan1589.loanWindow (Rolling1588.g j active) (base 2409) (Rolling1588.packetCarry j)
    (renameProgram (Equiv.swap (base 719) (Rolling1588.s j hole)) (half760OddLoan d divide))

def cell (divide : Bool) (d j active hole : Nat) : Program :=
  if divide then
    halfWindow true d j active hole ++
      SW.selW (Rolling1588.s j active) (base 2409) FrontierSW1591.swapBody
  else
    SW.selW (Rolling1588.s j active) (base 2409) FrontierSW1591.swapBody ++
      halfWindow false d j active hole

def basePacket (divide : Bool) (d j : Nat) : Program :=
  Rolling1588.onPacket j (Rolling1588.dp ++ ParityCodec5New.untwist) ++
    (if divide then
      cell true d j 3 2 ++ cell true d j 4 2 ++
      Rolling1588.onPacket j Rolling1588.bridge7 ++
      cell true d j 4 2 ++ cell true d j 3 2 ++
      Rolling1588.onPacket j Rolling1588.bridge5 ++ cell true d j 4 2
    else
      cell false d j 4 2 ++ Rolling1588.onPacket j Rolling1588.bridge5 ++
      cell false d j 3 2 ++ cell false d j 4 2 ++
      Rolling1588.onPacket j Rolling1588.bridge7inv ++
      cell false d j 4 2 ++ cell false d j 3 2) ++
    Rolling1588.onPacket j (ParityCodec5New.twist ++ Rolling1588.ep)

def packet (divide : Bool) (d j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacket divide d j)

def groups (divide : Bool) (d first count : Nat) : Program :=
  PacketSequence.program divide (packet divide d) first count

def placedGroups (divide : Bool) (d first count : Nat) : Program :=
  renameProgram (OB5.sig 511) (groups divide d first count)

def hostedGroup (h : StairHostsSchedule.HostPlan) (divide : Bool)
    (d first count : Nat) : Program :=
  StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
    (h.group divide d first count)
    (placedGroups divide d first count)

def entryTailSuffixOdd (h : StairHostsSchedule.HostPlan) : Program :=
  hostedGroup h true 43 100 2 ++
    renameProgram (OB5.sig 511) CompareDecoderOdd.endPacket760DivOddLoan ++
    HalfFieldOB5.copyN ++ HalfConvertOdd.canon760OddLoan

def exitHeadPrefixOdd (h : StairHostsSchedule.HostPlan) : Program :=
  HalfConvertOdd.center760OddLoan ++ HalfFieldOB5.copyN ++
    renameProgram (OB5.sig 511) InverseTailCOdd.endPacket760OddLoan44 ++
    hostedGroup h false 43 100 2

def entryLowSuffixOdd (h : StairHostsSchedule.HostPlan) : Program :=
  FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (entryTailSuffixOdd h) ++
    FourScratchWindow.unprefix

def exitLowPrefixOdd (h : StairHostsSchedule.HostPlan) : Program :=
  FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (exitHeadPrefixOdd h) ++
    FourScratchWindow.unprefix

/-- Exact Toffoli and measurement counts of `shortConstAddLoan d`:
    `251 + d` for `d < 6` (so `251` at `d = 0`), and uniformly `251 + (d - 5)` for
    every tail depth `d ∈ {13, 22, 30, 36, 41, 43}` (more generally `5 ≤ d ≤ 43` with `d ≠ 42`). -/
theorem shortConstAddLoan_counts (d : Nat) (L : BalancedCircuit.Layout) (hw : L.Widths)
    (k : Nat) (hd : d ≤ 43) (h42 : d ≠ 42) :
    toffoliCount (shortConstAddLoan d L k) = 251 + (if d < 6 then d else d - 5) ∧
    measurementCount (shortConstAddLoan d L k) = 251 + (if d < 6 then d else d - 5) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have hlen : (L.low.drop 3).length = 252 := by simp [w.1]
  have hclen : (L.carry.take 251).length = 251 := by simp [hw.2.2]
  have hlit : ∀ m, m ≤ 42 →
      toffoliCount (literalConstAddLoan m retiredRoles (L.low.drop 3) (L.carry.take 251)
        (L.low.getD 2 0) L.one (k / 8)) = 251 + m ∧
      measurementCount (literalConstAddLoan m retiredRoles (L.low.drop 3) (L.carry.take 251)
        (L.low.getD 2 0) L.one (k / 8)) = 251 + m := by
    intro m hm
    unfold literalConstAddLoan
    split_ifs with h0
    · have hc := literalConstAdd_counts (L.low.drop 3) (L.carry.take 251) (L.low.getD 2 0) L.one (k / 8)
        (by omega)
      exact ⟨by omega, by omega⟩
    · have ha := mappedAddLoan_counts m retiredRoles
        (mappedConstant none (L.low.drop 3).length (k / 8)) (L.low.drop 3) (L.carry.take 251)
        (L.low.getD 2 0) (by simp [mappedConstant_length]) (by omega) (by omega)
      have hm0 := mappedAdd_counts (mappedConstant none (L.low.drop 3).length (k / 8))
        (L.low.drop 3) (L.carry.take 251) (L.low.getD 2 0)
        (by simp [mappedConstant_length]) (by omega)
      exact ⟨by omega, by omega⟩
  unfold shortConstAddLoan
  split_ifs with h5
  · have h := hlit d (by omega)
    simp only [toffoliCount_append, measurementCount_append, h.1, h.2, toffoliCount, measurementCount]
    exact ⟨by omega, by omega⟩
  · have hdeff : Nat.min d 42 - (shortFreeHosts d).length = d - 5 := by
      unfold shortFreeHosts
      by_cases h41 : d ≤ 41
      · simp [h41, Nat.min_def]; split_ifs <;> omega
      · simp [h41, Nat.min_def]; split_ifs <;> omega
    have h := hlit (Nat.min d 42 - (shortFreeHosts d).length) (by omega)
    rw [hdeff] at h
    have hx : toffoliCount ([Instr.X (L.low.getD 2 0)] : Program) = 0 ∧
        measurementCount ([Instr.X (L.low.getD 2 0)] : Program) = 0 := ⟨rfl, rfl⟩
    simp only [hdeff, StairLoan.rebindMany_counts, toffoliCount_append, measurementCount_append,
      h.1, h.2, hx.1, hx.2]
    exact ⟨by omega, by omega⟩

private theorem compareChain_counts_symm (fwd : Bool) :
    ∀ (as bs cs : List Wire) (cin target : Wire), as.length = bs.length →
      toffoliCount (Q6LifetimeResearch.compareChain fwd as bs cs cin target) =
        toffoliCount (Q6LifetimeResearch.compareChain fwd bs as cs cin target) ∧
      measurementCount (Q6LifetimeResearch.compareChain fwd as bs cs cin target) =
        measurementCount (Q6LifetimeResearch.compareChain fwd bs as cs cin target)
  | [], [], _, _, _, _ => ⟨rfl, rfl⟩
  | [_], [_], _, _, _, _ => by cases fwd <;> exact ⟨rfl, rfl⟩
  | a :: a' :: as, b :: b' :: bs, [], cin, target, _ => ⟨rfl, rfl⟩
  | a :: a' :: as, b :: b' :: bs, c :: cs, cin, target, h => by
    have ih := compareChain_counts_symm fwd (a' :: as) (b' :: bs) cs c target (by simp at h ⊢; omega)
    have hm1 : toffoliCount (majority a b cin c) = toffoliCount (majority b a cin c) := rfl
    have hm2 : measurementCount (majority a b cin c) = measurementCount (majority b a cin c) := rfl
    have he1 : toffoliCount (eraseCarry a b cin c) = toffoliCount (eraseCarry b a cin c) := rfl
    have he2 : measurementCount (eraseCarry a b cin c) = measurementCount (eraseCarry b a cin c) := rfl
    cases fwd <;>
      simp only [Q6LifetimeResearch.compareChain, Bool.false_eq_true, if_false, if_true,
        toffoliCount_append, measurementCount_append, hm1, hm2, he1, he2, ih.1, ih.2, and_self]
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | [_], _ :: _ :: _, _, _, _, h => by simp at h
  | _ :: _ :: _, [_], _, _, _, h => by simp at h

private theorem literalConstAddLoan_counts_255 (d : Nat) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (k : Nat) (hd : d ≤ 43) :
    toffoliCount (literalConstAddLoan d retiredRoles L.low (L.carry.take 254) L.lower L.one k) = 254 + d ∧
    measurementCount (literalConstAddLoan d retiredRoles L.low (L.carry.take 254) L.lower L.one k) = 254 + d := by
  have w := BalancedCleanup.widths L.toLayout hw
  have hcl : (L.carry.take 254).length = 254 := by simp [List.length_take, hw.2.2]
  unfold literalConstAddLoan
  split_ifs with h0
  · have hc := literalConstAdd_counts L.low (L.carry.take 254) L.lower L.one k (by omega)
    exact ⟨by omega, by omega⟩
  · have ha := mappedAddLoan_counts d retiredRoles (mappedConstant none L.low.length k)
      L.low (L.carry.take 254) L.lower (by simp [mappedConstant_length]) (by omega) (by omega)
    have hm := mappedAdd_counts (mappedConstant none L.low.length k) L.low (L.carry.take 254) L.lower
      (by simp [mappedConstant_length]) (by omega)
    exact ⟨by omega, by omega⟩

private theorem tc_nil : toffoliCount ([] : Program) = 0 := rfl
private theorem tc_X (a : Wire) (p : Program) : toffoliCount (.X a :: p) = toffoliCount p := rfl
private theorem tc_CX (a b : Wire) (p : Program) : toffoliCount (.CX a b :: p) = toffoliCount p := rfl
private theorem tc_CCX (a b c : Wire) (p : Program) : toffoliCount (.CCX a b c :: p) = 1 + toffoliCount p := rfl
private theorem tc_mx (a : Wire) (b c : List Correction) (p : Program) : toffoliCount (.measureX a b c :: p) = toffoliCount p := rfl
private theorem mc_nil : measurementCount ([] : Program) = 0 := rfl
private theorem mc_X (a : Wire) (p : Program) : measurementCount (.X a :: p) = measurementCount p := rfl
private theorem mc_CX (a b : Wire) (p : Program) : measurementCount (.CX a b :: p) = measurementCount p := rfl
private theorem mc_CCX (a b c : Wire) (p : Program) : measurementCount (.CCX a b c :: p) = measurementCount p := rfl
private theorem mc_mx (a : Wire) (b c : List Correction) (p : Program) : measurementCount (.measureX a b c :: p) = 1 + measurementCount p := rfl

private theorem halfOddLoan_counts_gen (d : Nat) (divide : Bool) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hd : d ≤ 43) (h42 : d ≠ 42) :
    toffoliCount ([.X L.sign] ++ (if divide then forwardLoan d L else inverseLoan d L) ++ [.X L.sign]) +
        (if d < 6 then 3 else 8) =
      toffoliCount (([.X L.sign] ++ (if divide then StairLoan.forwardLoan d L else StairLoan.inverseLoan d L) ++
        [.X L.sign]) ++ (if divide then [] else [.measureX L.one [] []])) ∧
    measurementCount ([.X L.sign] ++ (if divide then forwardLoan d L else inverseLoan d L) ++ [.X L.sign]) +
        (if d < 6 then 4 else 9) =
      measurementCount (([.X L.sign] ++ (if divide then StairLoan.forwardLoan d L else StairLoan.inverseLoan d L) ++
        [.X L.sign]) ++ (if divide then [] else [.measureX L.one [] []])) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have hcs : ((Q6Structural.q6Carry L).take 255).length = 255 := by
    simp [Q6Structural.q6Carry, hw.2.2]
  have hsc1 := shortConstAddLoan_counts d L hw h.toNat hd h42
  have hsc2 := shortConstAddLoan_counts d L hw (encodeWord 255 (-h)) hd h42
  have hl1 := literalConstAddLoan_counts_255 d L hw BalancedCleanup.positiveLiteral hd
  have hl2 := literalConstAddLoan_counts_255 d L hw BalancedCleanup.negativeLiteral hd
  have hcmSym : ∀ fwd, toffoliCount (compareLoan d retiredRoles fwd (L.r.drop 1) (L.y.drop 1)
        (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity) =
      toffoliCount (compareLoan d retiredRoles fwd (L.y.drop 1) (L.r.drop 1)
        (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity) ∧
      measurementCount (compareLoan d retiredRoles fwd (L.r.drop 1) (L.y.drop 1)
        (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity) =
      measurementCount (compareLoan d retiredRoles fwd (L.y.drop 1) (L.r.drop 1)
        (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity) := by
    intro fwd
    have h1 := compareLoan_counts d retiredRoles fwd (L.r.drop 1) (L.y.drop 1)
      (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity
      (by simp [w.2.1, w.2.2.1]) (by simp [w.2.1, hcs]) (by simp [hcs]; omega)
    have h2 := compareLoan_counts d retiredRoles fwd (L.y.drop 1) (L.r.drop 1)
      (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity
      (by simp [w.2.1, w.2.2.1]) (by simp [w.2.2.1, hcs]) (by simp [hcs]; omega)
    have hc := compareChain_counts_symm fwd (L.r.drop 1) (L.y.drop 1)
      (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity
      (by simp [w.2.1, w.2.2.1])
    exact ⟨by omega, by omega⟩
  have hpc : toffoliCount (prepareCompare L) = toffoliCount (BalancedCleanup.prepareCompare L.toLayout) ∧
      measurementCount (prepareCompare L) = measurementCount (BalancedCleanup.prepareCompare L.toLayout) := by
    simp only [prepareCompare, BalancedCleanup.prepareCompare, toffoliCount_append, measurementCount_append,
      (signComplement_counts _ _).1, (signComplement_counts _ _).2,
      tc_nil, tc_X, tc_CX, mc_nil, mc_X, mc_CX, Nat.add_zero, Nat.zero_add, and_self]
  have hex : toffoliCount (exposure L) = toffoliCount (Q6StructuralCell.exposure L) ∧
      measurementCount (exposure L) = measurementCount (Q6StructuralCell.exposure L) := by
    simp only [exposure, Q6StructuralCell.exposure, Q6LowerExposure.expose]; exact ⟨rfl, rfl⟩
  have hsd : toffoliCount (p1Seed L) = toffoliCount (GuardCompression.seed L) ∧
      measurementCount (p1Seed L) = measurementCount (GuardCompression.seed L) := by
    simp only [p1Seed, GuardCompression.seed]; exact ⟨rfl, rfl⟩
  have hnr : toffoliCount (notRegister (L.one :: L.y)) = toffoliCount (notRegister (L.one :: L.r)) ∧
      measurementCount (notRegister (L.one :: L.y)) = measurementCount (notRegister (L.one :: L.r)) := by
    simp only [(notRegister_counts _).1, (notRegister_counts _).2]; exact ⟨trivial, trivial⟩
  have hro : toffoliCount (rawAddLoan d L) = toffoliCount (StairLoan.rawAddLoan d L) ∧
      measurementCount (rawAddLoan d L) = measurementCount (StairLoan.rawAddLoan d L) := by
    simp only [rawAddLoan, StairLoan.rawAddLoan, orMajor, orErase, majority, eraseCarry,
      Q6LifetimeResearch.move, renameProgram_counts, toffoliCount_append, measurementCount_append,
      toffoliCount_reverse, measurementCount_reverse,
      tc_nil, tc_X, tc_CX, tc_CCX, tc_mx, mc_nil, mc_X, mc_CX, mc_CCX, mc_mx]
    exact ⟨trivial, trivial⟩
  have hrs : toffoliCount (rawSubLoan d L) = toffoliCount (StairLoan.rawSubTailLoan d L) ∧
      measurementCount (rawSubLoan d L) = measurementCount (StairLoan.rawSubTailLoan d L) := by
    simp only [rawSubLoan, StairLoan.rawSubTailLoan, orMajor, orErase, majority, eraseCarry,
      Q6LifetimeResearch.move, renameProgram_counts, toffoliCount_append, measurementCount_append,
      toffoliCount_reverse, measurementCount_reverse,
      tc_nil, tc_X, tc_CX, tc_CCX, tc_mx, mc_nil, mc_X, mc_CX, mc_CCX, mc_mx]
    exact ⟨trivial, trivial⟩
  cases divide
  · have hcm := hcmSym false
    simp only [Bool.false_eq_true, if_false, inverseLoan, StairLoan.inverseLoan,
      StairLoan.normalizeLoan, unfoldLoan, StairLoan.unfoldLoan,
      compareBlockLoan, StairLoan.compareBlockLoan,
      Q6LifetimeResearch.move, renameProgram_counts, toffoliCount_append, measurementCount_append,
      toffoliCount_reverse, measurementCount_reverse,
      hsc2.1, hsc2.2, hl2.1, hl2.2, hcm.1, hcm.2, hpc.1, hpc.2, hex.1, hex.2, hnr.1, hnr.2,
      hrs.1, hrs.2, majority, eraseCarry, tc_nil, tc_X, tc_CX, tc_CCX, tc_mx, mc_nil, mc_X, mc_CX, mc_CCX, mc_mx]
    split_ifs <;> exact ⟨by omega, by omega⟩
  · have hcm := hcmSym true
    simp only [if_true, forwardLoan, StairLoan.forwardLoan,
      StairLoan.unnormalizeLoan, foldLoan, StairLoan.foldLoan,
      compareBlockLoan, StairLoan.compareBlockLoan,
      Q6LifetimeResearch.move, renameProgram_counts, toffoliCount_append, measurementCount_append,
      toffoliCount_reverse, measurementCount_reverse,
      hsc1.1, hsc1.2, hl1.1, hl1.2, hcm.1, hcm.2, hpc.1, hpc.2, hex.1, hex.2, hsd.1, hsd.2,
      hnr.1, hnr.2, hro.1, hro.2, majority, eraseCarry, tc_nil, tc_X, tc_CX, tc_CCX, tc_mx, mc_nil, mc_X, mc_CX, mc_CCX, mc_mx]
    split_ifs <;> exact ⟨by omega, by omega⟩

theorem half760OddLoan_counts (d : Nat) (divide : Bool) (hd : d ≤ 43) (h42 : d ≠ 42) :
    toffoliCount (half760OddLoan d divide) + (if d < 6 then 3 else 8) =
      toffoliCount (StairLoan.half760Loan d divide) ∧
    measurementCount (half760OddLoan d divide) + (if d < 6 then 4 else 9) =
      measurementCount (StairLoan.half760Loan d divide) := by
  have h := halfOddLoan_counts_gen d divide (Q6EndpointCell.ports base (base 2409))
    (Q6EndpointCell.ports_widths base (base 2409)) hd h42
  have hs : (Q6EndpointCell.ports base (base 2409)).sign = base 2409 := rfl
  have ho : (Q6EndpointCell.ports base (base 2409)).one = base 1027 := rfl
  rw [hs, ho] at h
  cases divide <;>
    simp only [half760OddLoan, StairLoan.half760Loan, Bool.false_eq_true, if_false, if_true] at h ⊢ <;>
    exact h

theorem packet_counts (divide : Bool) (d j : Nat) (hd : d ≤ 43) (h42 : d ≠ 42) :
    toffoliCount (packet divide d j) + 5 * (if d < 6 then 3 else 8) =
      toffoliCount (StairGroups.packet divide d j) ∧
    measurementCount (packet divide d j) + 5 * (if d < 6 then 4 else 9) =
      measurementCount (StairGroups.packet divide d j) := by
  have hc := half760OddLoan_counts d divide hd h42
  cases divide <;>
    simp only [packet, StairGroups.packet, basePacket, StairGroups.basePacket,
      cell, StairGroups.cell, halfWindow, StairGroups.halfWindow,
      StairLoanAdapter.concreteHalf760Loan,
      ControlLoan1589.loanWindow, Bool.false_eq_true, if_false, if_true,
      renameProgram_counts, toffoliCount_append, measurementCount_append] <;>
    exact ⟨by omega, by omega⟩

theorem hostedGroup_counts (h : StairHostsSchedule.HostPlan) (divide : Bool)
    (d first count : Nat) (hd : d ≤ 43) (h42 : d ≠ 42) :
    toffoliCount (hostedGroup h divide d first count) +
        5 * count * (if d < 6 then 3 else 8) =
      toffoliCount (StairHostsSchedule.hostedGroup h divide d first count) ∧
    measurementCount (hostedGroup h divide d first count) +
        5 * count * (if d < 6 then 4 else 9) =
      measurementCount (StairHostsSchedule.hostedGroup h divide d first count) := by
  simp only [hostedGroup, StairHostsSchedule.hostedGroup, placedGroups,
    StairSchedule.placedGroups, StairConcrete.bestLoans, groups, StairGroups.groups,
    StairLoan.rebindMany_counts, renameProgram_counts]
  induction count generalizing first with
  | zero => simp [PacketSequence.program]
  | succ n ih =>
    have hp := packet_counts divide d first hd h42
    have hr := ih (first + 1)
    cases divide <;>
      simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
        toffoliCount_append, measurementCount_append] <;>
      (split_ifs at * <;> exact ⟨by omega, by omega⟩)

-- Structural gateSlots comparison (`compareLoan` symmetric in `as`/`bs`, `shortConstAddLoan` saves >= 12 slots)
private theorem compareLayers_slots_symm (fwd : Bool) :
    ∀ (as bs cs : List Wire) (cin target : Wire),
      (compareLayers fwd as bs cs cin target).map (fun l => (gateSlots l.up, gateSlots l.erase, gateSlots l.finish)) =
      (compareLayers fwd bs as cs cin target).map (fun l => (gateSlots l.up, gateSlots l.erase, gateSlots l.finish))
  | [], _, _, _, _ => by simp [compareLayers]
  | [a], [], _, _, _ => by simp [compareLayers]
  | [a], [b], _, _, _ => by simp [compareLayers]
  | [a], b :: b' :: bs, _, _, _ => by simp [compareLayers]
  | a :: a' :: as, [], _, _, _ => by simp [compareLayers]
  | a :: a' :: as, [b], _, _, _ => by simp [compareLayers]
  | a :: a' :: as, b :: b' :: bs, [], _, _ => by simp [compareLayers]
  | a :: a' :: as, b :: b' :: bs, c :: cs, cin, target => by
    simp only [compareLayers, List.map_cons]
    refine congrArg₂ List.cons ?_ (compareLayers_slots_symm fwd (a' :: as) (b' :: bs) cs c target)
    cases fwd <;> simp [majority, eraseCarry, gateSlots, instructionSlots]

private theorem emitLoan_slots_of_layer_eq (d : Nat) (roles : List Wire)
    (ls1 ls2 : List StairLoan.CarryLayer) (top1 top2 : Program)
    (hl : ls1.map (fun l => (gateSlots l.up, gateSlots l.erase, gateSlots l.finish)) =
          ls2.map (fun l => (gateSlots l.up, gateSlots l.erase, gateSlots l.finish)))
    (ht : gateSlots top1 = gateSlots top2) :
    gateSlots (StairLoan.emitLoan d roles ls1 top1) = gateSlots (StairLoan.emitLoan d roles ls2 top2) := by
  have hup : ∀ a b : List StairLoan.CarryLayer,
      a.map (fun l => (gateSlots l.up, gateSlots l.erase, gateSlots l.finish)) =
      b.map (fun l => (gateSlots l.up, gateSlots l.erase, gateSlots l.finish)) →
      gateSlots (StairLoan.emitUps a) = gateSlots (StairLoan.emitUps b) ∧
      gateSlots (StairLoan.emitErases a) = gateSlots (StairLoan.emitErases b) ∧
      gateSlots (StairLoan.emitDowns a) = gateSlots (StairLoan.emitDowns b) := by
    intro a; induction a with
    | nil => intro b hb; cases b with | nil => simp [StairLoan.emitUps, StairLoan.emitErases, StairLoan.emitDowns] | cons _ _ => simp at hb
    | cons x xs ih =>
      intro b hb; cases b with
      | nil => simp at hb
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hb
        have hr := ih ys hb.2
        simp only [StairLoan.emitUps, StairLoan.emitErases, StairLoan.emitDowns,
          StairLoan.CarryLayer.down, gateSlots_append]
        exact ⟨by omega, by omega, by omega⟩
  unfold StairLoan.emitLoan
  have h1 := hup (ls1.take (d + 1)) (ls2.take (d + 1)) (by rw [List.map_take, List.map_take, hl])
  have h2 := hup (ls1.take d) (ls2.take d) (by rw [List.map_take, List.map_take, hl])
  have h3 := hup (ls1.drop (d + 1)) (ls2.drop (d + 1)) (by rw [List.map_drop, List.map_drop, hl])
  simp only [StairLoan.emitSweep, OddFullPass.rebindMany_slots, gateSlots_append]
  omega

theorem compareLoan_slots_symm (d : Nat) (roles : List Wire) (fwd : Bool)
    (as bs cs : List Wire) (cin target : Wire) (hab : as.length = bs.length) :
    gateSlots (compareLoan d roles fwd as bs cs cin target) =
      gateSlots (compareLoan d roles fwd bs as cs cin target) := by
  apply emitLoan_slots_of_layer_eq d roles _ _ _ _ (compareLayers_slots_symm fwd as bs cs cin target)
  have htop : ∀ a b : List Wire, a.length = b.length →
      gateSlots (compareTop fwd a b cs cin target) = gateSlots (compareTop fwd b a cs cin target) := by
    intro a; induction a generalizing cs cin with
    | nil => intro b hb; cases b <;> simp [compareTop] at hb ⊢
    | cons x xs ih =>
      intro b hb; cases b with
      | nil => simp at hb
      | cons y ys =>
        cases xs with
        | nil =>
          cases ys with
          | nil => cases fwd <;> rfl
          | cons _ _ => simp at hb
        | cons x' xs' =>
          cases ys with
          | nil => simp at hb
          | cons y' ys' =>
            cases cs with
            | nil => simp [compareTop]
            | cons c cs' => exact ih cs' c (y' :: ys') (by simp only [List.length_cons] at hb ⊢; omega)
  exact htop as bs hab

private theorem shortConstAddLoan_tail_slots_le (d : Nat) (hd6 : 6 ≤ d) (hd : d ≤ 43) (h42 : d ≠ 42) :
    gateSlots (shortConstAddLoan d (Q6EndpointCell.ports base (base 2409)) h.toNat) + 12 ≤
      gateSlots (StairLoan.unnormalizeLoan d (Q6EndpointCell.ports base (base 2409))) ∧
    gateSlots (shortConstAddLoan d (Q6EndpointCell.ports base (base 2409)) (encodeWord 255 (-h))) + 12 ≤
      gateSlots (StairLoan.normalizeLoan d (Q6EndpointCell.ports base (base 2409))) := by
  have hslot_layer (b : Bool) (y cin c : Wire) :
      gateSlots (mappedMajority { wire := none, flip := b } y cin c) = (if b then 3 else 1) ∧
      gateSlots (mappedEraseCarry { wire := none, flip := b } y cin c) = (if b then 4 else 2) ∧
      gateSlots (mappedSum { wire := none, flip := b } y cin) = (if b then 2 else 1) := by
    cases b <;> simp [mappedMajority, mappedEraseCarry, mappedSum, gateSlots, instructionSlots]
  have hsum_fn : ∀ (m : Nat) (bs : List Bool) (ys cs : List Wire) (cin : Wire),
      bs.length = ys.length → cs.length + 1 = ys.length → m ≤ cs.length →
      gateSlots (mappedAddLoan m retiredRoles (bs.map (fun b => { wire := none, flip := b })) ys cs cin) =
        ((bs.take (bs.length - 1)).map (fun b => if b then 9 else 4)).sum +
        (if bs.getLastD false then 2 else 1) +
        ((bs.take m).map (fun b => if b then 7 else 3)).sum := by
    intro m bs ys cs cin hby hcy hm
    have hlayers : ∀ (bs : List Bool) (ys cs : List Wire) (cin : Wire),
        bs.length = ys.length → cs.length + 1 = ys.length →
        (mappedLayers (bs.map (fun b => { wire := none, flip := b })) ys cs cin).map
          (fun l => (gateSlots l.up, gateSlots l.erase, gateSlots l.finish)) =
        (bs.take (bs.length - 1)).map (fun b => if b then (3, 4, 2) else (1, 2, 1)) := by
      intro bs; induction bs with
      | nil => intro ys cs cin _ _; simp [mappedLayers]
      | cons b bs ih =>
        intro ys cs cin hby hcy
        cases bs with
        | nil => cases ys <;> simp [mappedLayers]
        | cons b' bs' =>
          cases ys with
          | nil => simp at hby
          | cons y ys =>
            cases ys with
            | nil => simp at hby
            | cons y' ys' =>
              cases cs with
              | nil => simp at hcy
              | cons c cs' =>
                simp only [List.map_cons, mappedLayers, List.length_cons, Nat.add_sub_cancel,
                  List.take_succ_cons]
                congr 1
                · have hs := hslot_layer b y cin c
                  cases b <;> simp [hs.1, hs.2.1, hs.2.2]
                · exact ih (y' :: ys') cs' c (by simp only [List.length_cons] at hby ⊢; omega) (by simp only [List.length_cons] at hcy ⊢; omega)
    have htop : ∀ (bs : List Bool) (ys cs : List Wire) (cin : Wire) (d0 : Bool),
        bs.length = ys.length → cs.length + 1 = ys.length →
        gateSlots (mappedTop (bs.map (fun b => { wire := none, flip := b })) ys cs cin) =
        (if bs.getLastD d0 then 2 else 1) := by
      intro bs; induction bs with
      | nil => intro ys cs cin d0 hby hcy; cases ys with | nil => simp at hcy | cons _ _ => simp at hby
      | cons b bs ih =>
        intro ys cs cin d0 hby hcy
        cases bs with
        | nil =>
          cases ys with
          | nil => simp at hby
          | cons y ys =>
            cases ys with
            | nil => cases b <;> simp [mappedTop, mappedSum, gateSlots, instructionSlots]
            | cons _ _ => simp at hby
        | cons b' bs' =>
          cases ys with
          | nil => simp at hby
          | cons y ys =>
            cases ys with
            | nil => simp at hby
            | cons y' ys' =>
              cases cs with
              | nil => simp at hcy
              | cons c cs' =>
                rw [List.map_cons, List.map_cons, mappedTop, List.getLastD_cons]
                exact ih (y' :: ys') cs' c b (by simp only [List.length_cons] at hby ⊢; omega) (by simp only [List.length_cons] at hcy ⊢; omega)
    have hfold : ∀ ls : List StairLoan.CarryLayer,
        gateSlots (StairLoan.emitUps ls) = (ls.map (fun l => gateSlots l.up)).sum ∧
        gateSlots (StairLoan.emitErases ls) = (ls.map (fun l => gateSlots l.erase)).sum ∧
        gateSlots (StairLoan.emitDowns ls) = (ls.map (fun l => gateSlots l.erase + gateSlots l.finish)).sum := by
      intro ls; induction ls with
      | nil => simp [StairLoan.emitUps, StairLoan.emitErases, StairLoan.emitDowns, gateSlots]
      | cons l ls ih =>
        simp only [StairLoan.emitUps, StairLoan.emitErases, StairLoan.emitDowns,
          StairLoan.CarryLayer.down, gateSlots_append, List.map_cons, List.sum_cons]
        exact ⟨by omega, by omega, by omega⟩
    have hmap_sum : ∀ (ls : List StairLoan.CarryLayer) (bs' : List Bool),
        ls.map (fun l => (gateSlots l.up, gateSlots l.erase, gateSlots l.finish)) =
        bs'.map (fun b => if b then (3, 4, 2) else (1, 2, 1)) →
        (ls.map (fun l => gateSlots l.up)).sum + (ls.map (fun l => gateSlots l.erase)).sum =
          (bs'.map (fun b => if b then 7 else 3)).sum ∧
        (ls.map (fun l => gateSlots l.up)).sum +
          (ls.map (fun l => gateSlots l.erase + gateSlots l.finish)).sum =
          (bs'.map (fun b => if b then 9 else 4)).sum := by
      intro ls; induction ls with
      | nil => intro bs' hb; cases bs' <;> simp at hb ⊢
      | cons l ls ih =>
        intro bs' hb; cases bs' with
        | nil => simp at hb
        | cons b bs' =>
          simp only [List.map_cons, List.cons.injEq] at hb
          have hr := ih bs' hb.2
          cases b <;> simp only [Bool.false_eq_true, if_false, if_true, Prod.mk.injEq, List.map_cons, List.sum_cons] at hb ⊢ <;>
            exact ⟨by omega, by omega⟩
    have hly := hlayers bs ys cs cin hby hcy
    have htp := htop bs ys cs cin false hby hcy
    unfold mappedAddLoan StairLoan.emitLoan
    have htk : (List.take m (mappedLayers (bs.map (fun b => { wire := none, flip := b })) ys cs cin)).map
        (fun l => (gateSlots l.up, gateSlots l.erase, gateSlots l.finish)) =
        (bs.take m).map (fun b => if b then (3, 4, 2) else (1, 2, 1)) := by
      rw [List.map_take, hly, ← List.map_take, List.take_take, Nat.min_eq_left (by omega)]
    have htk1 : (List.take (m + 1) (mappedLayers (bs.map (fun b => { wire := none, flip := b })) ys cs cin)).map
        (fun l => (gateSlots l.up, gateSlots l.erase, gateSlots l.finish)) =
        ((bs.take (bs.length - 1)).take (m + 1)).map (fun b => if b then (3, 4, 2) else (1, 2, 1)) := by
      rw [List.map_take, hly, ← List.map_take]
    have hdr1 : (List.drop (m + 1) (mappedLayers (bs.map (fun b => { wire := none, flip := b })) ys cs cin)).map
        (fun l => (gateSlots l.up, gateSlots l.erase, gateSlots l.finish)) =
        ((bs.take (bs.length - 1)).drop (m + 1)).map (fun b => if b then (3, 4, 2) else (1, 2, 1)) := by
      rw [List.map_drop, hly, ← List.map_drop]
    have hf1 := hfold (List.take (m + 1) (mappedLayers (bs.map (fun b => { wire := none, flip := b })) ys cs cin))
    have hf2 := hfold (List.take m (mappedLayers (bs.map (fun b => { wire := none, flip := b })) ys cs cin))
    have hf3 := hfold (List.drop (m + 1) (mappedLayers (bs.map (fun b => { wire := none, flip := b })) ys cs cin))
    have hs1 := hmap_sum _ _ htk1
    have hs2 := hmap_sum _ _ htk
    have hs3 := hmap_sum _ _ hdr1
    have hsplit : ((bs.take (bs.length - 1)).map (fun b => if b then 9 else 4)).sum =
        (((bs.take (bs.length - 1)).take (m + 1)).map (fun b => if b then 9 else 4)).sum +
        (((bs.take (bs.length - 1)).drop (m + 1)).map (fun b => if b then 9 else 4)).sum := by
      rw [← List.sum_append, ← List.map_append, List.take_append_drop]
    simp only [StairLoan.emitSweep, OddFullPass.rebindMany_slots, gateSlots_append]
    omega
  have hmc_eq : ∀ (n k : Nat),
      mappedConstant none n k =
      ((List.range n).map (fun i => k.testBit i)).map (fun b => { wire := none, flip := b }) := by
    intro n; induction n with
    | zero => intro k; rfl
    | succ n ih =>
      intro k
      rw [List.range_succ_eq_map, List.map_cons, List.map_cons, mappedConstant, ih (k / 2)]
      congr 1
      · simp only [mappedConstantBit, Option.isNone_none, Nat.testBit_zero]
        by_cases h1 : k % 2 = 1 <;> simp [h1]
      · simp only [List.map_map]
        apply List.map_congr_left
        intro i _
        simp only [Function.comp, Nat.testBit_succ]
  have hL1 : BalancedCleanup.positiveLiteral = 28948022309329048855892746252171976963317496166410141009864396001977208667915 := by
    decide
  have hL2 : h.toNat / 8 = 3618502788666131106986593281521497120414687020801267626233049500247151083489 := by
    decide
  have hL3 : BalancedCleanup.negativeLiteral = 28948022309329048855892746252171976963317496166410141009864396001979356152052 := by
    decide
  have hL4 : encodeWord 255 (-h) / 8 = 3618502788666131106986593281521497120414687020801267626233049500247419519006 := by
    decide
  let bPosOld := (List.range 255).map (fun i => (28948022309329048855892746252171976963317496166410141009864396001977208667915 : Nat).testBit i)
  let bPosNew := (List.range 252).map (fun i => (3618502788666131106986593281521497120414687020801267626233049500247151083489 : Nat).testBit i)
  let bNegOld := (List.range 255).map (fun i => (28948022309329048855892746252171976963317496166410141009864396001979356152052 : Nat).testBit i)
  let bNegNew := (List.range 252).map (fun i => (3618502788666131106986593281521497120414687020801267626233049500247419519006 : Nat).testBit i)
  have hcheck : (List.range' 6 38).all (fun m =>
      let sPosOld : Nat := ((bPosOld.take 254).map (fun b => if b then (9 : Nat) else 4)).sum +
        (if bPosOld.getLastD false then (2 : Nat) else 1) + ((bPosOld.take m).map (fun b => if b then (7 : Nat) else 3)).sum + 2
      let sPosNew : Nat := ((bPosNew.take 251).map (fun b => if b then (9 : Nat) else 4)).sum +
        (if bPosNew.getLastD false then (2 : Nat) else 1) + ((bPosNew.take (m - 5)).map (fun b => if b then (7 : Nat) else 3)).sum + 1
      let sNegOld : Nat := ((bNegOld.take 254).map (fun b => if b then (9 : Nat) else 4)).sum +
        (if bNegOld.getLastD false then (2 : Nat) else 1) + ((bNegOld.take m).map (fun b => if b then (7 : Nat) else 3)).sum
      let sNegNew : Nat := ((bNegNew.take 251).map (fun b => if b then (9 : Nat) else 4)).sum +
        (if bNegNew.getLastD false then (2 : Nat) else 1) + ((bNegNew.take (m - 5)).map (fun b => if b then (7 : Nat) else 3)).sum + 1
      decide (sPosNew + 12 ≤ sPosOld ∧ sNegNew + 12 ≤ sNegOld)) = true := by
    decide +kernel
  have hdm : d ∈ List.range' 6 38 := List.mem_range'_1.mpr ⟨by omega, by omega⟩
  have hok := of_decide_eq_true (List.all_eq_true.mp hcheck d hdm)
  have hw := Q6EndpointCell.ports_widths base (base 2409)
  have w := BalancedCleanup.widths (Q6EndpointCell.ports base (base 2409)).toLayout hw
  have hdeff : Nat.min d 42 - (shortFreeHosts d).length = d - 5 := by
    unfold shortFreeHosts; by_cases h41 : d ≤ 41 <;> simp [h41, Nat.min_def] <;> split_ifs <;> omega
  have hd0 : d ≠ 0 := by omega
  have heff0 : d - 5 ≠ 0 := by omega
  have hxA : gateSlots ([Instr.X ((Q6EndpointCell.ports base (base 2409)).low.getD 2 0)] : Program) = 1 := rfl
  have hxB : gateSlots ([Instr.X (Q6EndpointCell.ports base (base 2409)).one] : Program) = 1 := rfl
  have hxC : gateSlots ([Instr.X (Q6EndpointCell.ports base (base 2409)).one,
      Instr.X (Q6EndpointCell.ports base (base 2409)).one] : Program) = 2 := rfl
  have hxD : gateSlots ([Instr.X (Q6EndpointCell.ports base (base 2409)).lower] : Program) = 1 := rfl
  simp only [shortConstAddLoan, StairLoan.unnormalizeLoan, StairLoan.normalizeLoan,
    literalConstAddLoan, Q6LifetimeResearch.move, OddFullPass.rebindMany_slots,
    ECDSAAdd.Baselines.rename_gateSlots, gateSlots_append, hxA, hxB, hxC, hxD,
    show ¬ d < 6 by omega, if_false, hdeff, hd0, heff0,
    show ((Q6EndpointCell.ports base (base 2409)).low.drop 3).length = 252 by simp [w.1],
    w.1, hmc_eq, hL1, hL2, hL3, hL4]
  rw [hsum_fn (d - 5) _ _ _ _ (by simp [w.1]) (by simp [w.1, hw.2.2]) (by simp [hw.2.2]; omega),
      hsum_fn d _ _ _ _ (by simp [w.1]) (by simp [w.1, hw.2.2]) (by simp [hw.2.2]; omega),
      hsum_fn (d - 5) _ _ _ _ (by simp [w.1]) (by simp [w.1, hw.2.2]) (by simp [hw.2.2]; omega),
      hsum_fn d _ _ _ _ (by simp [w.1]) (by simp [w.1, hw.2.2]) (by simp [hw.2.2]; omega)]
  simp only [List.length_map, List.length_range, Nat.reduceSub]
  dsimp only [bPosOld, bPosNew, bNegOld, bNegNew] at hok
  exact ⟨by omega, by omega⟩

private theorem gs_nil : gateSlots ([] : Program) = 0 := rfl
private theorem gs_X (a : Wire) (p : Program) : gateSlots (.X a :: p) = 1 + gateSlots p := rfl
private theorem gs_CX (a b : Wire) (p : Program) : gateSlots (.CX a b :: p) = 1 + gateSlots p := rfl
private theorem gs_CCX (a b c : Wire) (p : Program) : gateSlots (.CCX a b c :: p) = 1 + gateSlots p := rfl
private theorem gs_mx (a : Wire) (b c : List Correction) (p : Program) :
    gateSlots (.measureX a b c :: p) = 1 + b.length + c.length + gateSlots p := by
  simp [gateSlots, instructionSlots, Nat.add_assoc]

theorem half760OddLoan_slots_le (d : Nat) (divide : Bool) (hd6 : 6 ≤ d) (hd : d ≤ 43) (h42 : d ≠ 42) :
    gateSlots (half760OddLoan d divide) ≤ gateSlots (StairLoan.half760Loan d divide) := by
  let L := Q6EndpointCell.ports base (base 2409)
  have hw := Q6EndpointCell.ports_widths base (base 2409)
  have w := BalancedCleanup.widths L.toLayout hw
  have hcm := compareLoan_slots_symm d retiredRoles divide
    (L.r.drop 1) (L.y.drop 1) (((Q6Structural.q6Carry L).take 255).drop 1)
    (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity (by simp [w.2.1, w.2.2.1])
  have hsc : gateSlots (shortConstAddLoan d L h.toNat) + 12 ≤ gateSlots (StairLoan.unnormalizeLoan d L) ∧
      gateSlots (shortConstAddLoan d L (encodeWord 255 (-h))) + 12 ≤ gateSlots (StairLoan.normalizeLoan d L) :=
    shortConstAddLoan_tail_slots_le d (by omega) hd h42
  have hpc : gateSlots (prepareCompare L) ≤ gateSlots (BalancedCleanup.prepareCompare L.toLayout) := by
    simp only [prepareCompare, BalancedCleanup.prepareCompare, gateSlots_append,
      gs_nil, gs_X, gs_CX, gs_CCX, gs_mx]
    omega
  have hnr : gateSlots (notRegister (L.one :: L.y)) = gateSlots (notRegister (L.one :: L.r)) := by
    have hnrLen : ∀ xs : List Wire, gateSlots (notRegister xs) = xs.length := by
      intro xs; induction xs with
      | nil => rfl
      | cons x xs ih =>
        have h1 : gateSlots (notRegister (x :: xs)) = 1 + gateSlots (notRegister xs) := rfl
        rw [h1, ih]; simp; omega
    simp [hnrLen, w.2.1, w.2.2.1]
  have hro : gateSlots (rawAddLoan d L) ≤ gateSlots (StairLoan.rawAddLoan d L) + 4 := by
    simp only [rawAddLoan, StairLoan.rawAddLoan, orMajor, orErase, majority, eraseCarry,
      Q6LifetimeResearch.move, ECDSAAdd.Baselines.rename_gateSlots, gateSlots_append,
      ExitFusionResearch.slots_reverse, gs_nil, gs_X, gs_CX, gs_CCX, gs_mx, List.length_nil,
      List.length_cons]
    omega
  have hrs : gateSlots (rawSubLoan d L) ≤ gateSlots (StairLoan.rawSubTailLoan d L) + 4 := by
    simp only [rawSubLoan, StairLoan.rawSubTailLoan, orMajor, orErase, majority, eraseCarry,
      Q6LifetimeResearch.move, ECDSAAdd.Baselines.rename_gateSlots, gateSlots_append,
      ExitFusionResearch.slots_reverse, gs_nil, gs_X, gs_CX, gs_CCX, gs_mx, List.length_nil,
      List.length_cons]
    omega
  have hex : gateSlots (exposure L) ≤ gateSlots (Q6StructuralCell.exposure L) := by
    simp only [exposure, Q6StructuralCell.exposure, Q6LowerExposure.expose, gateSlots_append,
      gs_nil, gs_X, gs_CX, gs_CCX, gs_mx]
    omega
  cases divide
  · simp only [half760OddLoan, StairLoan.half760Loan, inverseLoan, StairLoan.inverseLoan,
      unfoldLoan, StairLoan.unfoldLoan, compareBlockLoan, StairLoan.compareBlockLoan,
      majority, eraseCarry,
      Bool.false_eq_true, if_false, Q6LifetimeResearch.move,
      ECDSAAdd.Baselines.rename_gateSlots, gateSlots_append, ExitFusionResearch.slots_reverse,
      gs_nil, gs_X, gs_CX, gs_CCX, gs_mx, List.length_nil, List.length_cons, hcm, hnr]
    dsimp only [L] at hsc hpc hnr hro hrs hex hcm ⊢
    omega
  · simp only [half760OddLoan, StairLoan.half760Loan, forwardLoan, StairLoan.forwardLoan,
      foldLoan, StairLoan.foldLoan, compareBlockLoan, StairLoan.compareBlockLoan,
      p1Seed, GuardCompression.seed, majority, eraseCarry,
      if_true, Q6LifetimeResearch.move,
      ECDSAAdd.Baselines.rename_gateSlots, gateSlots_append, ExitFusionResearch.slots_reverse,
      gs_nil, gs_X, gs_CX, gs_CCX, gs_mx, List.length_nil, List.length_cons, hcm, hnr]
    dsimp only [L] at hsc hpc hnr hro hrs hex hcm ⊢
    omega

theorem hostedGroup_slots_le (h : StairHostsSchedule.HostPlan) (divide : Bool)
    (d first count : Nat) (hd6 : 6 ≤ d) (hd : d ≤ 43) (h42 : d ≠ 42) :
    gateSlots (hostedGroup h divide d first count) ≤
      gateSlots (StairHostsSchedule.hostedGroup h divide d first count) := by
  simp only [hostedGroup, StairHostsSchedule.hostedGroup, placedGroups,
    StairSchedule.placedGroups, StairConcrete.bestLoans, groups, StairGroups.groups,
    OddFullPass.rebindMany_slots, ECDSAAdd.Baselines.rename_gateSlots]
  induction count generalizing first with
  | zero => simp [PacketSequence.program]
  | succ n ih =>
    have hs := half760OddLoan_slots_le d divide hd6 hd h42
    have hr := ih (first + 1)
    cases divide <;>
      simp only [PacketSequence.program, packet, StairGroups.packet, basePacket,
        StairGroups.basePacket, cell, StairGroups.cell, halfWindow, StairGroups.halfWindow,
        StairLoanAdapter.concreteHalf760Loan,
        ControlLoan1589.loanWindow, Bool.false_eq_true, if_false, if_true,
        ECDSAAdd.Baselines.rename_gateSlots, gateSlots_append] at * <;>
      omega

-- Structural wire-inclusion (`wires (half760OddLoan d divide) ⊆ wires (StairLoan.half760Loan d divide)`)
private theorem compareLayers_wires_symm (fwd : Bool) :
    ∀ (as bs cs : List Wire) (cin target : Wire),
      (compareLayers fwd as bs cs cin target).map (fun l => (l.host, wires l.up, wires l.erase, wires l.finish)) =
      (compareLayers fwd bs as cs cin target).map (fun l => (l.host, wires l.up, wires l.erase, wires l.finish))
  | [], _, _, _, _ => by simp [compareLayers]
  | [a], [], _, _, _ => by simp [compareLayers]
  | [a], [b], _, _, _ => by simp [compareLayers]
  | [a], b :: b' :: bs, _, _, _ => by simp [compareLayers]
  | a :: a' :: as, [], _, _, _ => by simp [compareLayers]
  | a :: a' :: as, [b], _, _, _ => by simp [compareLayers]
  | a :: a' :: as, b :: b' :: bs, [], _, _ => by simp [compareLayers]
  | a :: a' :: as, b :: b' :: bs, c :: cs, cin, target => by
    simp only [compareLayers, List.map_cons]
    refine congrArg₂ List.cons ?_ (compareLayers_wires_symm fwd (a' :: as) (b' :: bs) cs c target)
    have hmaj : wires (majority a b cin c) = wires (majority b a cin c) := by
      ext q; simp [majority, wires, Instr.wires]; tauto
    have her : wires (eraseCarry a b cin c) = wires (eraseCarry b a cin c) := by
      ext q; simp [eraseCarry, wires, Instr.wires, correctionWires]; tauto
    cases fwd <;> simp [hmaj, her]

private theorem compareLoan_wires_symm (d : Nat) (roles : List Wire) (fwd : Bool)
    (as bs cs : List Wire) (cin target : Wire) (hab : as.length = bs.length) :
    wires (compareLoan d roles fwd as bs cs cin target) =
      wires (compareLoan d roles fwd bs as cs cin target) := by
  have hl := compareLayers_wires_symm fwd as bs cs cin target
  have hup : ∀ xs ys : List StairLoan.CarryLayer,
      xs.map (fun l => (l.host, wires l.up, wires l.erase, wires l.finish)) =
      ys.map (fun l => (l.host, wires l.up, wires l.erase, wires l.finish)) →
      StairLoan.layerHosts xs = StairLoan.layerHosts ys ∧
      wires (StairLoan.emitUps xs) = wires (StairLoan.emitUps ys) ∧
      wires (StairLoan.emitErases xs) = wires (StairLoan.emitErases ys) ∧
      wires (StairLoan.emitDowns xs) = wires (StairLoan.emitDowns ys) := by
    intro xs; induction xs with
    | nil => intro ys h; cases ys with | nil => simp [StairLoan.layerHosts, StairLoan.emitUps, StairLoan.emitErases, StairLoan.emitDowns] | cons _ _ => simp at h
    | cons x xs ih =>
      intro ys h; cases ys with
      | nil => simp at h
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
        have hr := ih ys h.2
        have hlh : StairLoan.layerHosts (x :: xs) = x.host :: StairLoan.layerHosts xs := rfl
        have hlh2 : StairLoan.layerHosts (y :: ys) = y.host :: StairLoan.layerHosts ys := rfl
        simp only [hlh, hlh2, StairLoan.emitUps, StairLoan.emitErases,
          StairLoan.emitDowns, StairLoan.CarryLayer.down, wires_append, h.1.1, h.1.2.1, h.1.2.2.1,
          h.1.2.2.2, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, and_self]
  have htop : ∀ (a b cs : List Wire) (cin : Wire), a.length = b.length →
      wires (compareTop fwd a b cs cin target) = wires (compareTop fwd b a cs cin target) := by
    clear hl hup hab
    intro a; induction a with
    | nil => intro b cs cin hb; cases b <;> simp [compareTop] at hb ⊢
    | cons x xs ih =>
      intro b cs cin hb; cases b with
      | nil => simp at hb
      | cons y ys =>
        cases xs with
        | nil =>
          cases ys with
          | nil =>
            cases fwd <;> (ext q; simp [OddFullPass.mem_wires_iff_flatMap, compareTop,
              Q6LifetimeResearch.compareLeaf, majority, eraseCarry, OddFullPass.instrWiresList,
              OddFullPass.correctionWiresList]; tauto)
          | cons _ _ => simp at hb
        | cons x' xs' =>
          cases ys with
          | nil => simp at hb
          | cons y' ys' =>
            cases cs with
            | nil => simp [compareTop]
            | cons c cs' => exact ih (y' :: ys') cs' c (by simp only [List.length_cons] at hb ⊢; omega)
  have hrebind : ∀ rs hs P Q, wires P = wires Q →
      wires (StairLoan.rebindMany rs hs P) = wires (StairLoan.rebindMany rs hs Q) := by
    intro rs; induction rs with
    | nil => intro hs P Q h; exact h
    | cons r rs ih =>
      intro hs P Q h; cases hs with
      | nil => exact h
      | cons hh hs =>
        simp only [StairLoan.rebindMany, renameProgram_support, ih hs P Q h]
  unfold compareLoan StairLoan.emitLoan
  have h1 := hup ((compareLayers fwd as bs cs cin target).take (d + 1)) ((compareLayers fwd bs as cs cin target).take (d + 1)) (by rw [List.map_take, List.map_take, hl])
  have h2 := hup ((compareLayers fwd as bs cs cin target).take d) ((compareLayers fwd bs as cs cin target).take d) (by rw [List.map_take, List.map_take, hl])
  have h3 := hup ((compareLayers fwd as bs cs cin target).drop (d + 1)) ((compareLayers fwd bs as cs cin target).drop (d + 1)) (by rw [List.map_drop, List.map_drop, hl])
  simp only [StairLoan.emitSweep, wires_append, h1.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1]
  congr 1; congr 1; congr 1
  apply hrebind
  simp only [StairLoan.emitSweep, wires_append, h3.2.1, h3.2.2.2, htop as bs cs cin hab]

private theorem hyInSC_gen (s : Wire) (ys : List Wire) :
    ∀ q ∈ ys, q ∈ wires (signComplement s ys) := by
  intro q hq; induction ys with
  | nil => simp at hq
  | cons a as ih =>
    simp only [signComplement, List.map_cons, wires, Instr.wires, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at *
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr (ih hq)

private theorem hnrIn_gen (xs : List Wire) : ∀ q ∈ xs, q ∈ wires (notRegister xs) := by
  intro q hq; induction xs with
  | nil => simp at hq
  | cons a as ih =>
    simp only [notRegister, List.map_cons, wires, Instr.wires, Finset.mem_union, Finset.mem_singleton]
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inl rfl
    · exact Or.inr (ih hq)

private theorem horSubMaj_gen (a b s c : Wire) :
    wires (orMajor a b c) ⊆ wires (majority a b s c) ∧
    wires (orErase a b c) ⊆ wires (eraseCarry a b s c) :=
  ⟨fun q hq => by simp [orMajor, majority, wires, Instr.wires] at hq ⊢; tauto,
   fun q hq => by simp [orErase, eraseCarry, wires, Instr.wires, correctionWires] at hq ⊢; tauto⟩

private theorem mem_wires_X_iff (a q : Wire) : q ∈ wires ([Instr.X a] : Program) ↔ q = a := by
  simp [wires, Instr.wires]

private theorem wires_maj_symm (a b s c : Wire) :
    wires (majority a b s c) = wires (majority b a s c) := by
  ext q; simp [majority, wires, Instr.wires]; tauto

private theorem wires_erase_symm (a b s c : Wire) :
    wires (eraseCarry a b s c) = wires (eraseCarry b a s c) := by
  ext q; simp [eraseCarry, wires, Instr.wires, correctionWires]; tauto

private theorem signComplement_sig_mem (s : Wire) (ys : List Wire) (hne : ys ≠ []) :
    s ∈ wires (signComplement s ys) := by
  cases ys with
  | nil => exact absurd rfl hne
  | cons a as => simp [signComplement, List.map_cons, wires, Instr.wires]

/-- Wire envelope of `move (base 760) L.rmsb (shortConstAddLoan d L k)` for all `d ≤ 43`, `d ≠ 42`. -/
private theorem shortConstAddLoan_wires_in (d : Nat) (hd : d ≤ 43) (h42 : d ≠ 42) (k : Nat) :
    let L := Q6EndpointCell.ports base (base 2409)
    wires (Q6LifetimeResearch.move (base 760) L.rmsb (shortConstAddLoan d L k)) ⊆
      (L.low.toFinset ∪ {L.one, L.parity, L.rmsb} ∪
        ((L.carry.take 254).toFinset \ (retiredRoles.take d).toFinset)).erase (base 760) := by
  intro L
  have hw := Q6EndpointCell.ports_widths base (base 2409)
  have w := BalancedCleanup.widths L.toLayout hw
  have hcl : L.carry.length = 256 := hw.2.2
  have hcl251 : (L.carry.take 251).length = 251 := by decide +kernel
  have hndShort : ((L.low.getD 2 0) :: (L.low.drop 3 ++ L.carry.take 251)).Nodup :=
    PeakNodup.nodup_of_mask _ (by decide +kernel)
  have hbase763 : ∀ q ∈ L.carry.take 251, q ≠ retiredRoles.getD 42 0 := by decide +kernel
  have hrole42 : ∀ q ∈ retiredRoles.take 42, q ∉ L.low ∧ q ≠ L.one ∧ q ≠ L.rmsb ∧
      q ∉ (L.carry.take 251).take 43 := by decide +kernel
  have hmcAway : ∀ (n m0 : Nat) (q : Wire), q ∈ mappedWires ((mappedConstant none n (k / 8)).take m0) → False := by
    intro n m0 q hq
    have hm : q ∈ mappedWires (mappedConstant none n (k / 8)) := by
      simp only [mappedWires, List.mem_flatMap] at hq ⊢
      obtain ⟨b, hb, hqb⟩ := hq
      exact ⟨b, List.mem_of_mem_take hb, hqb⟩
    exact absurd (mappedConstant_wires none n (k / 8) q hm) (by simp)
  have hfreeOk : ∀ q ∈ shortFreeHosts d,
      (q = L.one ∨ q = L.parity ∨ (q ∈ L.carry.take 254 ∧ q ∉ retiredRoles.take d)) ∧
      q ≠ base 760 ∧ q ≠ L.rmsb := by
    unfold shortFreeHosts
    by_cases h41 : d ≤ 41
    · rw [if_pos h41]
      have hchk : ([base 763, base 764, base 1540, base 768, base 1027] : List Wire).all (fun q =>
          decide ((q = L.one ∨ q = L.parity ∨ (q ∈ L.carry.take 254 ∧ q ∉ retiredRoles.take 41)) ∧
            q ≠ base 760 ∧ q ≠ L.rmsb)) = true := by decide +kernel
      intro q hq
      have h := of_decide_eq_true (List.all_eq_true.mp hchk q hq)
      refine ⟨?_, h.2.1, h.2.2⟩
      rcases h.1 with h1 | h2 | ⟨h3, h4⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨h3, fun bad => h4 ((List.take_sublist_take_left h41).subset bad)⟩)
    · rw [if_neg h41]
      have hd43 : d = 43 := by omega
      subst hd43
      have hchk : ([base 764, base 1540, base 768, base 1027] : List Wire).all (fun q =>
          decide ((q = L.one ∨ q = L.parity ∨ (q ∈ L.carry.take 254 ∧ q ∉ retiredRoles.take 43)) ∧
            q ≠ base 760 ∧ q ≠ L.rmsb)) = true := by decide +kernel
      intro q hq
      exact of_decide_eq_true (List.all_eq_true.mp hchk q hq)
  have hlitSub : ∀ m, m ≤ 42 →
      wires (literalConstAddLoan m retiredRoles (L.low.drop 3) (L.carry.take 251)
        (L.low.getD 2 0) L.one (k / 8)) ⊆
      (L.low.toFinset ∪ {L.one} ∪ (L.carry.take 251).toFinset) \ (retiredRoles.take m).toFinset := by
    intro m hm
    have hbanks : (retiredRoles.take m ++ (L.carry.take 251).take m).Nodup := by
      have h42nd : (retiredRoles.take 42 ++ (L.carry.take 251).take 42).Nodup := by decide +kernel
      exact h42nd.sublist (List.Sublist.append
        (List.take_sublist_take_left hm) (List.take_sublist_take_left hm))
    unfold literalConstAddLoan
    split_ifs with h0
    · rw [h0, List.take_zero, List.toFinset_nil, Finset.sdiff_empty]
      intro q hq
      have hsup := literalConstAdd_wires (L.low.drop 3) (L.carry.take 251)
        (L.low.getD 2 0) L.one (k / 8) hq
      simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset, List.mem_append,
        List.mem_cons] at hsup ⊢
      rcases hsup with h1 | h2 | h3 | h4
      · exact Or.inl (Or.inr h1)
      · exact Or.inl (Or.inl (by
          have : 2 < L.low.length := by omega
          rw [h2, List.getD_eq_getElem _ _ this]; exact List.getElem_mem this))
      · exact Or.inl (Or.inl (List.mem_of_mem_drop h3))
      · exact Or.inr h4
    · have hlift := StairLoanSupport.mappedAddLoan_support_lift m retiredRoles
        (mappedConstant none (L.low.drop 3).length (k / 8)) (L.low.drop 3) (L.carry.take 251)
        (L.low.getD 2 0)
        (by simp [mappedConstant_length]) (by simp [w.1, hcl251])
        (by rw [hcl251]; omega) (by rw [retiredRoles_length]; omega)
        hndShort (fun q hq => absurd (mappedConstant_wires none _ _ q hq) (by simp)) hbanks
        (fun r hr hm' => by
          have hr42 : r ∈ retiredRoles.take 42 := (List.take_sublist_take_left hm).subset hr
          have ha := hrole42 r hr42
          rw [List.mem_toFinset] at hm'
          simp only [List.mem_append, List.mem_singleton] at hm'
          rcases hm' with ((h1 | h2) | h3) | h4
          · exact hmcAway _ _ r h1
          · exact ha.1 (List.mem_of_mem_drop (List.mem_of_mem_take h2))
          · exact ha.2.2.2 ((List.take_sublist_take_left (by omega)).subset h3)
          · exact ha.1 (by
              have : 2 < L.low.length := by omega
              rw [h4, List.getD_eq_getElem _ _ this]; exact List.getElem_mem this))
      intro q hq
      have hq' := hlift hq
      simp only [Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset] at hq' ⊢
      rcases hq' with ⟨hw0, hnr⟩ | hh
      · refine ⟨?_, hnr⟩
        have maw := mappedAdd_wires_subset _ _ _ _ hw0
        simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at maw
        rcases maw with ((h1 | h2) | h3) | h4
        · exact absurd (mappedConstant_wires none _ _ q h1) (by simp)
        · exact Or.inl (Or.inl (List.mem_of_mem_drop h2))
        · exact Or.inr h3
        · exact Or.inl (Or.inl (by
            have : 2 < L.low.length := by omega
            rw [h4, List.getD_eq_getElem _ _ this]; exact List.getElem_mem this))
      · refine ⟨Or.inr (List.mem_of_mem_take hh), ?_⟩
        intro bad
        exact (List.nodup_append'.mp hbanks).2.2 bad hh
  have hrmsbOut : L.rmsb ∉ L.low ∧ L.rmsb ≠ L.one ∧ L.rmsb ≠ L.parity ∧ L.rmsb ∉ L.carry.take 254 := by
    decide +kernel
  have hinner : wires (shortConstAddLoan d L k) ⊆
      L.low.toFinset ∪ {L.one, L.parity} ∪
        ((L.carry.take 254).toFinset \ (retiredRoles.take d).toFinset) := by
    unfold shortConstAddLoan
    split_ifs with h5
    · intro q hq
      simp only [wires_append, Finset.mem_union] at hq
      rcases hq with hq | hq
      · have hm := Finset.mem_sdiff.mp (hlitSub d (by omega) hq)
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff,
          List.mem_toFinset] at hm ⊢
        rcases hm.1 with (hl | ho) | hc
        · exact Or.inl (Or.inl hl)
        · exact Or.inl (Or.inr (Or.inl ho))
        · exact Or.inr ⟨(List.take_sublist_take_left (by decide : 251 ≤ 254)).subset hc, hm.2⟩
      · have hq2 : q = L.low.getD 2 0 := (mem_wires_X_iff _ _).mp hq
        subst hq2; simp only [Finset.mem_union, List.mem_toFinset]; left; left
        have : 2 < L.low.length := by omega
        rw [List.getD_eq_getElem _ _ this]; exact List.getElem_mem this
    · set free := shortFreeHosts d
      set dEff := Nat.min d 42 - free.length
      set remRoles := (retiredRoles.take (Nat.min d 42)).drop dEff
      have hfl : free.length = if d ≤ 41 then 5 else 4 := by
        unfold free shortFreeHosts; split_ifs <;> rfl
      have hdEff_eq : dEff = d - 5 := by
        unfold dEff; rw [hfl]; unfold Nat.min; split_ifs <;> omega
      have hlenEq : remRoles.length = free.length := by
        simp only [remRoles, List.length_drop, List.length_take, retiredRoles_length]
        rw [hfl, hdEff_eq]; unfold Nat.min; split_ifs <;> omega
      have hndRF : (remRoles ++ free).Nodup := by
        have hrr : (retiredRoles.take 42).Nodup := by decide +kernel
        have hrSub : List.Sublist remRoles (retiredRoles.take 42) :=
          (List.drop_sublist _ _).trans (List.take_sublist_take_left (Nat.min_le_right d 42))
        have hff : free.Nodup := by
          unfold free shortFreeHosts; by_cases h41 : d ≤ 41 <;> simp [h41] <;> decide +kernel
        refine List.Nodup.append (hrr.sublist hrSub) hff ?_
        intro a ha hb
        have ha' : a ∈ retiredRoles.take d :=
          (List.take_sublist_take_left (Nat.min_le_left d 42)).subset (List.mem_of_mem_drop ha)
        have hfb := (hfreeOk a hb).1
        rcases hfb with h1 | h2 | ⟨_, hnr⟩
        · exact (hrole42 a (hrSub.subset ha)).2.1 h1
        · exact absurd h2 (by
            have hnp : ∀ r ∈ retiredRoles.take 42, r ≠ L.parity := by decide +kernel
            exact hnp a (hrSub.subset ha))
        · exact hnr ha'
      intro q hq
      simp only [wires_append, Finset.mem_union] at hq
      rcases hq with hq | hq
      · have hfreeAv : ∀ z ∈ free, z ∉ wires (literalConstAddLoan dEff retiredRoles
            (L.low.drop 3) (L.carry.take 251) (L.low.getD 2 0) L.one (k / 8)) := by
          intro z hz hwz
          have hde0 : dEff ≠ 0 := by rw [hdEff_eq]; omega
          unfold literalConstAddLoan at hwz
          rw [if_neg hde0] at hwz
          have hbanks : (retiredRoles.take dEff ++ (L.carry.take 251).take dEff).Nodup := by
            have h42nd : (retiredRoles.take 42 ++ (L.carry.take 251).take 42).Nodup := by decide +kernel
            exact h42nd.sublist (List.Sublist.append
              (List.take_sublist_take_left (by rw [hdEff_eq]; omega))
              (List.take_sublist_take_left (by rw [hdEff_eq]; omega)))
          have hlift := StairLoanSupport.mappedAddLoan_support_lift dEff retiredRoles
            (mappedConstant none (L.low.drop 3).length (k / 8)) (L.low.drop 3) (L.carry.take 251)
            (L.low.getD 2 0) (by simp [mappedConstant_length]) (by simp [w.1, hcl251])
            (by rw [hcl251, hdEff_eq]; omega) (by rw [retiredRoles_length, hdEff_eq]; omega)
            hndShort (fun q hq => absurd (mappedConstant_wires none _ _ q hq) (by simp)) hbanks
            (fun r hr hm' => by
              have hr42 : r ∈ retiredRoles.take 42 := (List.take_sublist_take_left (by rw [hdEff_eq]; omega)).subset hr
              have ha := hrole42 r hr42
              rw [List.mem_toFinset] at hm'
              simp only [List.mem_append, List.mem_singleton] at hm'
              rcases hm' with ((h1 | h2) | h3) | h4
              · exact hmcAway _ _ r h1
              · exact ha.1 (List.mem_of_mem_drop (List.mem_of_mem_take h2))
              · exact ha.2.2.2 ((List.take_sublist_take_left (by rw [hdEff_eq]; omega)).subset h3)
              · exact ha.1 (by
                  have : 2 < L.low.length := by omega
                  rw [h4, List.getD_eq_getElem _ _ this]; exact List.getElem_mem this)) hwz
          have hzOut : free.all (fun w => decide (w ∉ L.low ∧ w ∉ L.carry.take 251)) = true := by
            unfold free shortFreeHosts; by_cases h41 : d ≤ 41 <;> simp [h41] <;> decide +kernel
          have hzo := of_decide_eq_true (List.all_eq_true.mp hzOut z hz)
          rcases Finset.mem_union.mp hlift with h0 | hh
          · have maw := mappedAdd_wires_subset _ _ _ _ (Finset.mem_sdiff.mp h0).1
            simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at maw
            rcases maw with ((h1 | h2) | h3) | rfl
            · exact absurd (mappedConstant_wires none _ _ z h1) (by simp)
            · exact hzo.1 (List.mem_of_mem_drop h2)
            · exact hzo.2 h3
            · exact hzo.1 (by decide +kernel)
          · exact hzo.2 (List.mem_of_mem_take (List.mem_toFinset.mp hh))
        have hrb := HalfConvertOdd.rebindMany_wires_sub_erase remRoles free _ hlenEq hndRF hfreeAv hq
        simp only [Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset] at hrb
        rcases hrb with ⟨hw0, hnrRem⟩ | hfree
        · have hm := Finset.mem_sdiff.mp (hlitSub dEff (by rw [hdEff_eq]; omega) hw0)
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff,
            List.mem_toFinset] at hm ⊢
          rcases hm.1 with (hl | ho) | hc
          · exact Or.inl (Or.inl hl)
          · exact Or.inl (Or.inr (Or.inl ho))
          · right
            refine ⟨(List.take_sublist_take_left (by decide : 251 ≤ 254)).subset hc, ?_⟩
            intro bad
            have bad42 : q ∈ retiredRoles.take (Nat.min d 42) := by
              by_cases hd43 : d = 43
              · subst hd43
                have htk : retiredRoles.take 43 = retiredRoles.take 42 ++ [retiredRoles.getD 42 0] := by decide +kernel
                rw [htk, List.mem_append, List.mem_singleton] at bad
                rcases bad with h42m | h42eq
                · simpa using h42m
                · exact absurd h42eq (hbase763 q hc)
              · simpa only [Nat.min_eq_left (by omega : d ≤ 42)] using bad
            have hsp : retiredRoles.take (Nat.min d 42) = retiredRoles.take dEff ++ remRoles := by
              have hle : dEff ≤ Nat.min d 42 := by rw [hdEff_eq]; exact Nat.le_min.mpr ⟨by omega, by omega⟩
              rw [show retiredRoles.take dEff = (retiredRoles.take (Nat.min d 42)).take dEff by
                rw [List.take_take, Nat.min_eq_left hle]]
              exact (List.take_append_drop dEff _).symm
            rw [hsp, List.mem_append] at bad42
            rcases bad42 with h1 | h2
            · exact hm.2 h1
            · exact hnrRem h2
        · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff,
            List.mem_toFinset]
          rcases (hfreeOk q hfree).1 with h1 | h2 | ⟨h3, h4⟩
          · exact Or.inl (Or.inr (Or.inl h1))
          · exact Or.inl (Or.inr (Or.inr h2))
          · exact Or.inr ⟨h3, h4⟩
      · have hq2 : q = L.low.getD 2 0 := (mem_wires_X_iff _ _).mp hq
        subst hq2; simp only [Finset.mem_union, List.mem_toFinset]; left; left
        have : 2 < L.low.length := by omega
        rw [List.getD_eq_getElem _ _ this]; exact List.getElem_mem this
  intro q hq
  rw [Q6LifetimeResearch.move, renameProgram_support] at hq
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
  have hrIn := hinner hr
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff,
    List.mem_toFinset] at hrIn
  have hrNeRmsb : r ≠ L.rmsb := by
    rcases hrIn with (hl | ho | hp) | ⟨hc, _⟩
    · exact fun e => hrmsbOut.1 (e ▸ hl)
    · exact fun e => hrmsbOut.2.1 (e.symm.trans ho)
    · exact fun e => hrmsbOut.2.2.1 (e.symm.trans hp)
    · exact fun e => hrmsbOut.2.2.2 (e ▸ hc)
  by_cases h760 : r = base 760
  · subst h760
    rw [Equiv.swap_apply_left]
    refine Finset.mem_erase.mpr ⟨by decide +kernel, ?_⟩
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · rw [Equiv.swap_apply_of_ne_of_ne h760 hrNeRmsb]
    refine Finset.mem_erase.mpr ⟨h760, ?_⟩
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff,
      List.mem_toFinset]
    rcases hrIn with (hl | ho | hp) | ⟨hc, hnr⟩
    · exact Or.inl (Or.inl hl)
    · exact Or.inl (Or.inr (Or.inl ho))
    · exact Or.inl (Or.inr (Or.inr (Or.inl hp)))
    · exact Or.inr ⟨hc, hnr⟩

attribute [local irreducible] wires

private theorem halfOddLoan_wires_sub_gen (d : Nat) (divide : Bool) (L : BalancedCircuit.Layout)
    (hw : L.Widths)
    (hsc : ∀ k, wires (Q6LifetimeResearch.move (base 760) L.rmsb (shortConstAddLoan d L k)) ⊆
      (L.low.toFinset ∪ {L.one, L.parity, L.rmsb} ∪
        ((L.carry.take 254).toFinset \ (retiredRoles.take d).toFinset)).erase (base 760))
    (hfoldCarry : ∀ q ∈ L.carry.take 254, q ∉ retiredRoles.take d → q ≠ base 760 →
      q ∈ wires (Q6LifetimeResearch.move (base 760) L.rmsb
        (mappedAddLoan d retiredRoles (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one))) :
    wires (([Instr.X L.sign] ++ (if divide then forwardLoan d L else inverseLoan d L) ++ [Instr.X L.sign])) ⊆
      wires (([Instr.X L.sign] ++ (if divide then StairLoan.forwardLoan d L else StairLoan.inverseLoan d L) ++
        [Instr.X L.sign]) ++ (if divide then [] else [Instr.measureX L.one [] []])) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have hcmEq := compareLoan_wires_symm d retiredRoles divide (L.r.drop 1) (L.y.drop 1)
    (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0)
    L.parity (by simp [w.2.1, w.2.2.1])
  have hlowInRot : ∀ q ∈ L.low, q ∈ wires (rotateRight (BalancedCircuit.rawTarget L)) ∧
      q ∈ wires (rotateLeft (BalancedCircuit.rawTarget L)) := by
    intro q hq
    have hqT : q ∈ BalancedCircuit.rawTarget L := by
      rw [BalancedCircuit.rawTarget, BalancedCleanup.Layout.r]; simp [hq]
    have hlen : (BalancedCircuit.rawTarget L).length = 257 := by simp [BalancedCircuit.rawTarget, w.2.1]
    have hr := rotate_wires (BalancedCircuit.rawTarget L)
    rw [hr.1, hr.2, if_neg (by rw [hlen]; decide)]
    exact ⟨List.mem_toFinset.mpr hqT, List.mem_toFinset.mpr hqT⟩
  have hyInSC : ∀ q ∈ L.y, q ∈ wires (signComplement L.sign L.y) := hyInSC_gen L.sign L.y
  have horSubMaj : ∀ a b s c, wires (orMajor a b c) ⊆ wires (majority a b s c) ∧
      wires (orErase a b c) ⊆ wires (eraseCarry a b s c) := horSubMaj_gen
  have hsigIn : L.sign ∈ wires (signComplement L.sign L.y) :=
    signComplement_sig_mem L.sign L.y (by intro e; rw [e] at w; simp at w)
  have hr0InLow : L.r0 ∈ L.low := by simp [BalancedCleanup.Layout.low]
  have hymsbInY : L.ymsb ∈ L.y := by simp [BalancedCleanup.Layout.y]
  have hprep : ∀ (P : Program),
      (∀ q ∈ L.low, q ∈ wires P) → (∀ q ∈ L.y, q ∈ wires P) →
      L.lower ∈ wires P → L.rmsb ∈ wires P → L.sign ∈ wires P →
      wires (prepareCompare L) ⊆ wires P := by
    intro P hlo hy hlow hrm hsg q hq
    simp only [prepareCompare, wires_append, Finset.mem_union, or_assoc] at hq
    rcases hq with h | h | h | h | h
    · have hrot := (rotate_wires L.r).2
      rw [hrot, if_neg (by rw [w.2.1]; decide)] at h
      have hqR : q ∈ L.r := List.mem_toFinset.mp h
      rw [BalancedCleanup.Layout.r, List.mem_append, List.mem_singleton] at hqR
      rcases hqR with hl | rfl
      · exact hlo q hl
      · exact hrm
    · simp only [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h
      rcases h with rfl | rfl | rfl
      · exact hlo L.r0 hr0InLow
      · exact hlow
      · exact hlo L.r0 hr0InLow
    · have ht := signComplement_wires_subset L.sign L.y h
      simp only [List.mem_toFinset, List.mem_cons] at ht
      rcases ht with rfl | hqy
      · exact hsg
      · exact hy q hqy
    · have ht := signComplement_wires_subset L.lower L.y h
      simp only [List.mem_toFinset, List.mem_cons] at ht
      rcases ht with rfl | hqy
      · exact hlow
      · exact hy q hqy
    · simp only [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h
      rcases h with rfl | rfl
      · exact hrm
      · exact hy L.ymsb hymsbInY
  have hexp : ∀ (P : Program), (∀ q ∈ L.low, q ∈ wires P) → L.lower ∈ wires P →
      wires (exposure L) ⊆ wires P := by
    intro P hlo hlow q hq
    simp only [exposure, OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hq
    rcases hq with rfl | rfl | rfl
    · exact hlow
    · exact hlo L.r0 hr0InLow
    · exact hlow
  cases divide
  · have hlowIn : ∀ w ∈ L.low, w ∈ wires (StairLoan.inverseLoan d L) := fun q hq => by
      have h := (hlowInRot q hq).2
      simp only [StairLoan.inverseLoan, wires_append, Finset.mem_union, h, true_or, or_true]
    have hyIn : ∀ w ∈ L.y, w ∈ wires (StairLoan.inverseLoan d L) := fun q hq => by
      have h := hyInSC q hq
      simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, h, true_or, or_true]
    have hcarIn : ∀ w ∈ L.carry.take 254, w ∉ retiredRoles.take d → w ≠ base 760 →
        w ∈ wires (StairLoan.inverseLoan d L) := by
      intro q hq hnr h760
      have hm := hfoldCarry q hq hnr h760
      rw [Q6LifetimeResearch.move, renameProgram_support] at hm
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
      have hsub : Equiv.swap (base 760) L.rmsb v ∈ wires (Q6LifetimeResearch.move (base 760) L.rmsb
          (StairLoan.mappedSubLoan d retiredRoles (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one)) := by
        rw [Q6LifetimeResearch.move, renameProgram_support]
        exact Finset.mem_image.mpr ⟨v, by simp only [StairLoan.mappedSubLoan, wires_append, Finset.mem_union, hv, true_or, or_true], rfl⟩
      simp only [StairLoan.inverseLoan, StairLoan.unfoldLoan, wires_append, Finset.mem_union, hsub, true_or, or_true]
    have hflagIn : L.one ∈ wires (StairLoan.inverseLoan d L) ∧
        L.parity ∈ wires (StairLoan.inverseLoan d L) ∧
        L.lower ∈ wires (StairLoan.inverseLoan d L) ∧
        L.rmsb ∈ wires (StairLoan.inverseLoan d L) ∧
        L.sign ∈ wires (StairLoan.inverseLoan d L) := by
      let uPre : Program := [.CX L.parity L.lower, .CX L.rmsb L.lower, .CCX L.parity L.lower L.one,
        .CX L.lower L.rmsb, .CX L.parity L.rmsb]
      have h1 : L.one ∈ wires uPre := by simp [uPre, OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
      have h2 : L.parity ∈ wires uPre := by simp [uPre, OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
      have h3 : L.lower ∈ wires uPre := by simp [uPre, OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
      have h4 : L.rmsb ∈ wires uPre := by simp [uPre, OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [StairLoan.inverseLoan, StairLoan.unfoldLoan, wires_append, Finset.mem_union]
        simp only [uPre] at h1; simp only [h1, true_or, or_true]
      · simp only [StairLoan.inverseLoan, StairLoan.unfoldLoan, wires_append, Finset.mem_union]
        simp only [uPre] at h2; simp only [h2, true_or, or_true]
      · simp only [StairLoan.inverseLoan, StairLoan.unfoldLoan, wires_append, Finset.mem_union]
        simp only [uPre] at h3; simp only [h3, true_or, or_true]
      · simp only [StairLoan.inverseLoan, StairLoan.unfoldLoan, wires_append, Finset.mem_union]
        simp only [uPre] at h4; simp only [h4, true_or, or_true]
      · simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, hsigIn, true_or, or_true]
    have hbodySub : wires (inverseLoan d L) ⊆ wires (StairLoan.inverseLoan d L) := by
      intro q hq
      simp only [inverseLoan, wires_append, Finset.mem_union, or_assoc] at hq
      rcases hq with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
      · simp only [StairLoan.inverseLoan, wires_append, Finset.mem_union, h1, true_or, or_true]
      · have hs2 := Finset.mem_erase.mp (hsc (encodeWord 255 (-h)) h2)
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff,
          List.mem_toFinset] at hs2
        rcases hs2.2 with (hl | ho | hp | hr) | ⟨hc, hnr⟩
        · exact hlowIn q hl
        · subst ho; exact hflagIn.1
        · subst hp; exact hflagIn.2.1
        · subst hr; exact hflagIn.2.2.2.1
        · exact hcarIn q hc hnr hs2.1
      · exact hprep _ hlowIn hyIn hflagIn.2.2.1 hflagIn.2.2.2.1 hflagIn.2.2.2.2 h3
      · exact hexp _ hlowIn hflagIn.2.2.1 h4
      · simp only [compareBlockLoan, wires_append, Finset.mem_union, or_assoc] at h5
        rcases h5 with h | h | h | h | h | h | h
        · rw [notRegister_wires] at h
          simp only [List.mem_toFinset, List.mem_cons] at h
          rcases h with rfl | hy
          · exact hflagIn.1
          · exact hyIn q hy
        · rw [wires_maj_symm] at h; have hm := h
          simp only [StairLoan.inverseLoan, StairLoan.compareBlockLoan, wires_append, Finset.mem_union, hm, true_or, or_true]
        · rw [(mem_wires_X_iff _ _).mp h]; exact hflagIn.1
        · rw [Q6LifetimeResearch.move, renameProgram_support, hcmEq, ← renameProgram_support] at h
          simp only [StairLoan.inverseLoan, StairLoan.compareBlockLoan, Q6LifetimeResearch.move, wires_append, Finset.mem_union, h, true_or, or_true]
        · rw [(mem_wires_X_iff _ _).mp h]; exact hflagIn.1
        · rw [wires_erase_symm] at h; have he := h
          simp only [StairLoan.inverseLoan, StairLoan.compareBlockLoan, wires_append, Finset.mem_union, he, true_or, or_true]
        · rw [notRegister_wires] at h
          simp only [List.mem_toFinset, List.mem_cons] at h
          rcases h with rfl | hy
          · exact hflagIn.1
          · exact hyIn q hy
      · rw [wires_reverse] at h6
        exact hexp _ hlowIn hflagIn.2.2.1 h6
      · rw [wires_reverse] at h7
        exact hprep _ hlowIn hyIn hflagIn.2.2.1 hflagIn.2.2.2.1 hflagIn.2.2.2.2 h7
      · simp only [StairLoan.inverseLoan, wires_append, Finset.mem_union, h8, true_or, or_true]
      · simp only [unfoldLoan, wires_append, Finset.mem_union, or_assoc] at h9
        rcases h9 with h | h | h
        · simp only [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h
          rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact hflagIn.1 | exact hflagIn.2.1 | exact hflagIn.2.2.1 | exact hflagIn.2.2.2.1
        · simp only [StairLoan.inverseLoan, StairLoan.unfoldLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · simp only [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
            OddFullPass.correctionWiresList, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
            List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h
          rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact hflagIn.1 | exact hflagIn.2.1 | exact hflagIn.2.2.1 | exact hflagIn.2.2.2.1
      · simp only [StairLoan.inverseLoan, wires_append, Finset.mem_union, h10, true_or, or_true]
      · simp only [StairLoan.inverseLoan, wires_append, Finset.mem_union, h11, true_or, or_true]
      · simp only [rawSubLoan, wires_append, Finset.mem_union, or_assoc] at h12
        rcases h12 with h | h | h | h | h | h | h | h | h | h | h
        · simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · have hm := (horSubMaj _ _ L.sign _).1 h
          simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, hm, true_or, or_true]
        · simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · have he := (horSubMaj _ _ L.sign _).2 h
          simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, he, true_or, or_true]
        · simp only [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h
          rcases h with rfl | rfl | rfl
          · have ha : (GuardCompression.source L).getD 0 0 ∈ wires ([Instr.CX ((GuardCompression.source L).getD 0 0) ((BalancedCircuit.rawTarget L).getD 0 0), Instr.CX L.sign ((BalancedCircuit.rawTarget L).getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, ha, true_or, or_true]
          · have hb : (BalancedCircuit.rawTarget L).getD 0 0 ∈ wires ([Instr.CX ((GuardCompression.source L).getD 0 0) ((BalancedCircuit.rawTarget L).getD 0 0), Instr.CX L.sign ((BalancedCircuit.rawTarget L).getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, hb, true_or, or_true]
          · have hb : (BalancedCircuit.rawTarget L).getD 0 0 ∈ wires ([Instr.CX ((GuardCompression.source L).getD 0 0) ((BalancedCircuit.rawTarget L).getD 0 0), Instr.CX L.sign ((BalancedCircuit.rawTarget L).getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, hb, true_or, or_true]
        · simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · simp only [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h
          rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · have hb : (BalancedCircuit.rawTarget L).getD 0 0 ∈ wires ([Instr.CX ((BalancedCircuit.rawTarget L).getD 0 0) L.parity, Instr.CX (L.ylow.getD 0 0) L.parity, Instr.CX L.rmsb L.one] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, hb, true_or, or_true]
          · exact hflagIn.2.1
          · have hy0 : L.ylow.getD 0 0 ∈ wires ([Instr.CX ((BalancedCircuit.rawTarget L).getD 0 0) L.parity, Instr.CX (L.ylow.getD 0 0) L.parity, Instr.CX L.rmsb L.one] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.inverseLoan, StairLoan.rawSubTailLoan, wires_append, Finset.mem_union, hy0, true_or, or_true]
          · exact hflagIn.2.1
          · exact hflagIn.2.2.2.2
          · exact hflagIn.2.1
          · exact hflagIn.2.1
          · exact hflagIn.2.2.2.1
          · exact hflagIn.1
    intro q hq
    simp only [Bool.false_eq_true, if_false, wires_append, Finset.mem_union, or_assoc] at hq ⊢
    rcases hq with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (hbodySub h))
    · exact Or.inr (Or.inr (Or.inl h))
  · have hlowIn : ∀ w ∈ L.low, w ∈ wires (StairLoan.forwardLoan d L) := fun q hq => by
      have h := (hlowInRot q hq).1
      simp only [StairLoan.forwardLoan, wires_append, Finset.mem_union, h, true_or, or_true]
    have hyIn : ∀ w ∈ L.y, w ∈ wires (StairLoan.forwardLoan d L) := fun q hq => by
      have h := hyInSC q hq
      simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, h, true_or, or_true]
    have hcarIn : ∀ w ∈ L.carry.take 254, w ∉ retiredRoles.take d → w ≠ base 760 →
        w ∈ wires (StairLoan.forwardLoan d L) := fun q hq hnr h760 => by
      have hm := hfoldCarry q hq hnr h760
      simp only [StairLoan.forwardLoan, StairLoan.foldLoan, wires_append, Finset.mem_union, hm, true_or, or_true]
    have hflagIn : L.one ∈ wires (StairLoan.forwardLoan d L) ∧
        L.parity ∈ wires (StairLoan.forwardLoan d L) ∧
        L.lower ∈ wires (StairLoan.forwardLoan d L) ∧
        L.rmsb ∈ wires (StairLoan.forwardLoan d L) ∧
        L.sign ∈ wires (StairLoan.forwardLoan d L) := by
      have h1 : L.one ∈ wires ([Instr.CCX L.parity L.lower L.one, Instr.CX L.lower L.rmsb] : Program) := by
        simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
      have h2 : L.parity ∈ wires ([Instr.CCX L.parity L.lower L.one, Instr.CX L.lower L.rmsb] : Program) := by
        simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
      have h3 : L.lower ∈ wires ([Instr.CCX L.parity L.lower L.one, Instr.CX L.lower L.rmsb] : Program) := by
        simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
      have h4 : L.rmsb ∈ wires ([Instr.CCX L.parity L.lower L.one, Instr.CX L.lower L.rmsb] : Program) := by
        simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [StairLoan.forwardLoan, StairLoan.foldLoan, wires_append, Finset.mem_union, h1, true_or, or_true]
      · simp only [StairLoan.forwardLoan, StairLoan.foldLoan, wires_append, Finset.mem_union, h2, true_or, or_true]
      · simp only [StairLoan.forwardLoan, StairLoan.foldLoan, wires_append, Finset.mem_union, h3, true_or, or_true]
      · simp only [StairLoan.forwardLoan, StairLoan.foldLoan, wires_append, Finset.mem_union, h4, true_or, or_true]
      · simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, hsigIn, true_or, or_true]
    have hbodySub : wires (forwardLoan d L) ⊆ wires (StairLoan.forwardLoan d L) := by
      intro q hq
      simp only [forwardLoan, wires_append, Finset.mem_union, or_assoc] at hq
      rcases hq with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
      · simp only [p1Seed, OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h1
        have hy0In : L.ylow.getD 0 0 ∈ wires (StairLoan.forwardLoan d L) := by
          have hy0 : L.ylow.getD 0 0 ∈ wires (GuardCompression.seed L) := by
            simp [GuardCompression.seed, OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
          simp only [StairLoan.forwardLoan, wires_append, Finset.mem_union, hy0, true_or, or_true]
        rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact hflagIn.1 | exact hflagIn.2.1 | exact hflagIn.2.2.1 | exact hflagIn.2.2.2.1 |
            exact hflagIn.2.2.2.2 | exact hlowIn L.r0 hr0InLow | exact hy0In
      · simp only [rawAddLoan, wires_append, Finset.mem_union, or_assoc] at h2
        rcases h2 with h | h | h | h | h | h | h | h
        · simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · have hm := (horSubMaj _ _ L.sign _).1 h
          simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, hm, true_or, or_true]
        · simp only [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h
          rcases h with rfl | rfl | rfl | rfl | rfl
          · exact hflagIn.2.1
          · have hb : L.low.getD 0 0 ∈ wires ([Instr.CX L.parity (L.low.getD 0 0), Instr.CX (L.ylow.getD 0 0) (L.low.getD 0 0), Instr.CX L.sign (L.low.getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, hb, true_or, or_true]
          · have ha : L.ylow.getD 0 0 ∈ wires ([Instr.CX L.parity (L.low.getD 0 0), Instr.CX (L.ylow.getD 0 0) (L.low.getD 0 0), Instr.CX L.sign (L.low.getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, ha, true_or, or_true]
          · have hb : L.low.getD 0 0 ∈ wires ([Instr.CX L.parity (L.low.getD 0 0), Instr.CX (L.ylow.getD 0 0) (L.low.getD 0 0), Instr.CX L.sign (L.low.getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, hb, true_or, or_true]
          · have hb : L.low.getD 0 0 ∈ wires ([Instr.CX L.parity (L.low.getD 0 0), Instr.CX (L.ylow.getD 0 0) (L.low.getD 0 0), Instr.CX L.sign (L.low.getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, hb, true_or, or_true]
        · simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · rw [wires_reverse] at h
          simp only [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h
          rcases h with rfl | rfl | rfl | rfl | rfl
          · exact hflagIn.2.1
          · have hb : L.low.getD 0 0 ∈ wires ([Instr.CX L.parity (L.low.getD 0 0), Instr.CX (L.ylow.getD 0 0) (L.low.getD 0 0), Instr.CX L.sign (L.low.getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, hb, true_or, or_true]
          · have ha : L.ylow.getD 0 0 ∈ wires ([Instr.CX L.parity (L.low.getD 0 0), Instr.CX (L.ylow.getD 0 0) (L.low.getD 0 0), Instr.CX L.sign (L.low.getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, ha, true_or, or_true]
          · have hb : L.low.getD 0 0 ∈ wires ([Instr.CX L.parity (L.low.getD 0 0), Instr.CX (L.ylow.getD 0 0) (L.low.getD 0 0), Instr.CX L.sign (L.low.getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, hb, true_or, or_true]
          · have hb : L.low.getD 0 0 ∈ wires ([Instr.CX L.parity (L.low.getD 0 0), Instr.CX (L.ylow.getD 0 0) (L.low.getD 0 0), Instr.CX L.sign (L.low.getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, hb, true_or, or_true]
        · have he := (horSubMaj _ _ L.sign _).2 h
          simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, he, true_or, or_true]
        · simp only [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h
          rcases h with rfl | rfl | rfl
          · have ha : L.ylow.getD 0 0 ∈ wires ([Instr.CX (L.ylow.getD 0 0) (L.low.getD 0 0), Instr.CX L.sign (L.low.getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, ha, true_or, or_true]
          · have hb : L.low.getD 0 0 ∈ wires ([Instr.CX (L.ylow.getD 0 0) (L.low.getD 0 0), Instr.CX L.sign (L.low.getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, hb, true_or, or_true]
          · have hb : L.low.getD 0 0 ∈ wires ([Instr.CX (L.ylow.getD 0 0) (L.low.getD 0 0), Instr.CX L.sign (L.low.getD 0 0)] : Program) := by
              simp [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList]
            simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, hb, true_or, or_true]
        · simp only [StairLoan.forwardLoan, StairLoan.rawAddLoan, wires_append, Finset.mem_union, h, true_or, or_true]
      · simp only [StairLoan.forwardLoan, wires_append, Finset.mem_union, h3, true_or, or_true]
      · simp only [StairLoan.forwardLoan, wires_append, Finset.mem_union, h4, true_or, or_true]
      · simp only [foldLoan, wires_append, Finset.mem_union, or_assoc] at h5
        rcases h5 with h | h | h
        · simp only [StairLoan.forwardLoan, StairLoan.foldLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · simp only [StairLoan.forwardLoan, StairLoan.foldLoan, wires_append, Finset.mem_union, h, true_or, or_true]
        · simp only [OddFullPass.mem_wires_iff_flatMap, OddFullPass.instrWiresList,
            OddFullPass.correctionWiresList, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
            List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h
          rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact hflagIn.1 | exact hflagIn.2.1 | exact hflagIn.2.2.1 | exact hflagIn.2.2.2.1
      · simp only [StairLoan.forwardLoan, wires_append, Finset.mem_union, h6, true_or, or_true]
      · simp only [StairLoan.forwardLoan, wires_append, Finset.mem_union, h7, true_or, or_true]
      · exact hprep _ hlowIn hyIn hflagIn.2.2.1 hflagIn.2.2.2.1 hflagIn.2.2.2.2 h8
      · exact hexp _ hlowIn hflagIn.2.2.1 h9
      · simp only [compareBlockLoan, wires_append, Finset.mem_union, or_assoc] at h10
        rcases h10 with h | h | h | h | h | h | h
        · rw [notRegister_wires] at h
          simp only [List.mem_toFinset, List.mem_cons] at h
          rcases h with rfl | hy
          · exact hflagIn.1
          · exact hyIn q hy
        · rw [wires_maj_symm] at h; have hm := h
          simp only [StairLoan.forwardLoan, StairLoan.compareBlockLoan, wires_append, Finset.mem_union, hm, true_or, or_true]
        · rw [(mem_wires_X_iff _ _).mp h]; exact hflagIn.1
        · rw [Q6LifetimeResearch.move, renameProgram_support, hcmEq, ← renameProgram_support] at h
          simp only [StairLoan.forwardLoan, StairLoan.compareBlockLoan, Q6LifetimeResearch.move, wires_append, Finset.mem_union, h, true_or, or_true]
        · rw [(mem_wires_X_iff _ _).mp h]; exact hflagIn.1
        · rw [wires_erase_symm] at h; have he := h
          simp only [StairLoan.forwardLoan, StairLoan.compareBlockLoan, wires_append, Finset.mem_union, he, true_or, or_true]
        · rw [notRegister_wires] at h
          simp only [List.mem_toFinset, List.mem_cons] at h
          rcases h with rfl | hy
          · exact hflagIn.1
          · exact hyIn q hy
      · rw [wires_reverse] at h11
        exact hexp _ hlowIn hflagIn.2.2.1 h11
      · rw [wires_reverse] at h12
        exact hprep _ hlowIn hyIn hflagIn.2.2.1 hflagIn.2.2.2.1 hflagIn.2.2.2.2 h12
      · have hs13 := Finset.mem_erase.mp (hsc h.toNat h13)
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff,
          List.mem_toFinset] at hs13
        rcases hs13.2 with (hl | ho | hp | hr) | ⟨hc, hnr⟩
        · exact hlowIn q hl
        · subst ho; exact hflagIn.1
        · subst hp; exact hflagIn.2.1
        · subst hr; exact hflagIn.2.2.2.1
        · exact hcarIn q hc hnr hs13.1
      · simp only [StairLoan.forwardLoan, wires_append, Finset.mem_union, h14, true_or, or_true]
    intro q hq
    simp only [if_true, List.append_nil, wires_append, Finset.mem_union, or_assoc] at hq ⊢
    rcases hq with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (hbodySub h))
    · exact Or.inr (Or.inr h)

theorem half760OddLoan_wires_sub (d : Nat) (divide : Bool) (hd : d ≤ 43) (h42 : d ≠ 42) :
    wires (half760OddLoan d divide) ⊆ wires (StairLoan.half760Loan d divide) := by
  let L := Q6EndpointCell.ports base (base 2409)
  have hw := Q6EndpointCell.ports_widths base (base 2409)
  have w := BalancedCleanup.widths L.toLayout hw
  have hcl : L.carry.length = 256 := hw.2.2
  have hcsNd : (L.carry.take 254).Nodup := PeakNodup.nodup_of_mask _ (by decide +kernel)
  have hfoldCarry : ∀ q ∈ L.carry.take 254, q ∉ retiredRoles.take d → q ≠ base 760 →
      q ∈ wires (Q6LifetimeResearch.move (base 760) L.rmsb
        (mappedAddLoan d retiredRoles (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one)) := by
    intro q hq hnr h760
    have hqRmsb : q ≠ L.rmsb := by
      have hro : L.rmsb ∉ L.carry.take 254 := by decide +kernel
      intro e; exact hro (e ▸ hq)
    have hclen : (L.carry.take 254).length = 254 := by decide +kernel
    have hm := OddFullPass.carry_in_mappedAddLoan d retiredRoles (ShortBiasedFold.lowBits L) L.low
      (L.carry.take 254) L.one (by decide +kernel) (by rw [hclen, w.1]) (by rw [hclen]; omega) hcsNd q hq hnr
    rw [Q6LifetimeResearch.move, renameProgram_support]
    exact Finset.mem_image.mpr ⟨q, hm, Equiv.swap_apply_of_ne_of_ne h760 hqRmsb⟩
  have h := halfOddLoan_wires_sub_gen d divide L hw (shortConstAddLoan_wires_in d hd h42) hfoldCarry
  have hs : L.sign = base 2409 := rfl
  have ho : L.one = base 1027 := rfl
  rw [hs, ho] at h
  cases divide <;>
    (simp only [half760OddLoan, StairLoan.half760Loan, Bool.false_eq_true, if_false, if_true] at h ⊢; exact h)

theorem packet_wires_sub (divide : Bool) (d j : Nat) (hd : d ≤ 43) (h42 : d ≠ 42) :
    wires (packet divide d j) ⊆ wires (StairGroups.packet divide d j) := by
  simp only [packet, StairGroups.packet]
  apply StairLoanGroupSupport.rename_sub
  have hw := half760OddLoan_wires_sub d divide hd h42
  have hcell : ∀ a b, wires (cell divide d j a b) ⊆ wires (StairGroups.cell divide d j a b) := by
    intro a b q hq
    have hhw : wires (halfWindow divide d j a b) ⊆ wires (StairGroups.halfWindow divide d j a b) := by
      intro x hx
      simp only [halfWindow, StairGroups.halfWindow, StairLoanAdapter.concreteHalf760Loan,
        ControlLoan1589.loanWindow, wires_append, Finset.mem_union, or_assoc] at hx ⊢
      rcases hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (StairLoanGroupSupport.rename_sub _ _ _ (StairLoanGroupSupport.rename_sub _ _ _ hw) h))
      · exact Or.inr (Or.inr h)
    cases divide <;>
      simp only [cell, StairGroups.cell, Bool.false_eq_true, if_false, if_true,
        wires_append, Finset.mem_union] at hq ⊢
    · rcases hq with h | h; exact Or.inl h; exact Or.inr (hhw h)
    · rcases hq with h | h; exact Or.inl (hhw h); exact Or.inr h
  intro q hq
  cases divide <;>
    simp only [basePacket, StairGroups.basePacket, Bool.false_eq_true, if_false, if_true,
      wires_append, Finset.mem_union, or_assoc] at hq ⊢
  · rcases hq with h | h | h | h | h | h | h | h | h
    · simp only [h, true_or, or_true]
    · have hc := hcell 4 2 h; simp only [hc, true_or, or_true]
    · simp only [h, true_or, or_true]
    · have hc := hcell 3 2 h; simp only [hc, true_or, or_true]
    · have hc := hcell 4 2 h; simp only [hc, true_or, or_true]
    · simp only [h, true_or, or_true]
    · have hc := hcell 4 2 h; simp only [hc, true_or, or_true]
    · have hc := hcell 3 2 h; simp only [hc, true_or, or_true]
    · simp only [h, true_or, or_true]
  · rcases hq with h | h | h | h | h | h | h | h | h
    · simp only [h, true_or, or_true]
    · have hc := hcell 3 2 h; simp only [hc, true_or, or_true]
    · have hc := hcell 4 2 h; simp only [hc, true_or, or_true]
    · simp only [h, true_or, or_true]
    · have hc := hcell 4 2 h; simp only [hc, true_or, or_true]
    · have hc := hcell 3 2 h; simp only [hc, true_or, or_true]
    · simp only [h, true_or, or_true]
    · have hc := hcell 4 2 h; simp only [hc, true_or, or_true]
    · simp only [h, true_or, or_true]

private theorem rebindMany_sub_mono (rs hs : List Wire) (P Q : Program)
    (hsub : wires P ⊆ wires Q) :
    wires (StairLoan.rebindMany rs hs P) ⊆ wires (StairLoan.rebindMany rs hs Q) := by
  induction rs generalizing hs with
  | nil => exact hsub
  | cons r rs ih =>
    cases hs with
    | nil => exact hsub
    | cons hh hs =>
      simp only [StairLoan.rebindMany]
      exact StairLoanGroupSupport.rename_sub _ _ _ (ih hs)

theorem hostedGroup_wires_sub (h : StairHostsSchedule.HostPlan) (divide : Bool)
    (d first count : Nat) (hd : d ≤ 43) (h42 : d ≠ 42) :
    wires (hostedGroup h divide d first count) ⊆
      wires (StairHostsSchedule.hostedGroup h divide d first count) := by
  simp only [hostedGroup, StairHostsSchedule.hostedGroup, placedGroups,
    StairSchedule.placedGroups, StairConcrete.bestLoans, groups, StairGroups.groups]
  apply rebindMany_sub_mono
  apply StairLoanGroupSupport.rename_sub
  apply StairLoanGroupSupport.sequence_sub
  intro k
  exact packet_wires_sub divide d k hd h42

theorem entryTailSuffixOdd_wires_sub (h : StairHostsSchedule.HostPlan) :
    wires (entryTailSuffixOdd h) ⊆ wires (StairHostsSchedule.entryTailSuffix h) := by
  have hg := hostedGroup_wires_sub h true 43 100 2 (by decide) (by decide)
  have hd := StairLoanGroupSupport.rename_sub (OB5.sig 511) _ _
    CompareDecoderOdd.endPacket760DivOddLoan_wires_sub
  have hc := HalfConvertOdd.canon760OddLoan_wires_sub
  have hCan : StairConcrete.bestLoans.canon = StairBoundaryLoan.canon760Loan := rfl
  intro q hq
  simp only [entryTailSuffixOdd, StairHostsSchedule.entryTailSuffix,
    StairConcrete.bestLoans_divEndpoint, hCan, wires_append, Finset.mem_union, or_assoc] at hq ⊢
  rcases hq with h1 | h2 | h3 | h4
  · exact Or.inl (hg h1)
  · exact Or.inr (Or.inl (hd h2))
  · exact Or.inr (Or.inr (Or.inl h3))
  · rcases Finset.mem_union.mp (hc h4) with h4a | h4b
    · exact Or.inr (Or.inr (Or.inr h4a))
    · exact Or.inr (Or.inr (Or.inl h4b))

theorem exitHeadPrefixOdd_wires_sub (h : StairHostsSchedule.HostPlan) :
    wires (exitHeadPrefixOdd h) ⊆ wires (StairHostsSchedule.exitHeadPrefix h) := by
  have hg := hostedGroup_wires_sub h false 43 100 2 (by decide) (by decide)
  have hm := StairLoanGroupSupport.rename_sub (OB5.sig 511) _ _
    InverseTailCOdd.endPacket760OddLoan44_wires_sub
  have hc := HalfConvertOdd.center760OddLoan_wires_sub
  have hCen : StairConcrete.bestLoans.center = StairBoundaryLoan.center760Loan := rfl
  have hEp : StairConcrete.bestLoans.endPacket false 68 = StairEndpointLoan44.endPacket760Loan44 false := rfl
  intro q hq
  simp only [exitHeadPrefixOdd, StairHostsSchedule.exitHeadPrefix,
    StairHostsSchedule.hostedEndpoint, StairSchedule.placedEndPacket,
    hCen, hEp, wires_append, Finset.mem_union, or_assoc] at hq ⊢
  rcases hq with h1 | h2 | h3 | h4
  · rcases Finset.mem_union.mp (hc h1) with h1a | h1b
    · exact Or.inl h1a
    · exact Or.inr (Or.inl h1b)
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl (hm h3)))
  · exact Or.inr (Or.inr (Or.inr (hg h4)))

theorem entryLowSuffixOdd_wires_sub (h : StairHostsSchedule.HostPlan) :
    wires (entryLowSuffixOdd h) ⊆ wires (StairHostsSchedule.entryLowSuffix h) := by
  have ht := StairLoanGroupSupport.rename_sub Prefix1590.borrow _ _ (entryTailSuffixOdd_wires_sub h)
  intro q hq
  simp only [entryLowSuffixOdd, StairHostsSchedule.entryLowSuffix, wires_append, Finset.mem_union, or_assoc] at hq ⊢
  rcases hq with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl (ht h2))
  · exact Or.inr (Or.inr h3)

theorem exitLowPrefixOdd_wires_sub (h : StairHostsSchedule.HostPlan) :
    wires (exitLowPrefixOdd h) ⊆ wires (StairHostsSchedule.exitLowPrefix h) := by
  have ht := StairLoanGroupSupport.rename_sub Prefix1590.borrow _ _ (exitHeadPrefixOdd_wires_sub h)
  intro q hq
  simp only [exitLowPrefixOdd, StairHostsSchedule.exitLowPrefix, wires_append, Finset.mem_union, or_assoc] at hq ⊢
  rcases hq with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl (ht h2))
  · exact Or.inr (Or.inr h3)

private theorem gp_reverse (P : Program) (h : GatePhysical P) : GatePhysical P.reverse :=
  fun g hg => h g (List.mem_reverse.mp hg)

private theorem gp_single (i : Instr) (h : PhysicalInstr (RecordedInstr.gate i)) : GatePhysical [i] := by
  intro g hg; rw [List.mem_singleton.mp hg]; exact h

private theorem gp_cons (i : Instr) (P : Program) (h1 : PhysicalInstr (RecordedInstr.gate i)) (h2 : GatePhysical P) :
    GatePhysical (i :: P) := by
  intro g hg; rcases List.mem_cons.mp hg with rfl | hg; exact h1; exact h2 g hg

private theorem literalConstAdd_phys : ∀ (xs cs : List Wire) (cin one : Wire) (k : Nat),
    (one :: cin :: (xs ++ cs)).Nodup → GatePhysical (literalConstAdd xs cs cin one k)
  | [], _, _, _, _, _ => by simp [literalConstAdd, GatePhysical]
  | [x], _, cin, one, k, hnd => by
    have h1 := List.nodup_cons.mp hnd
    have h2 := List.nodup_cons.mp h1.2
    have hxc : x ≠ cin := fun e => h2.1 (by simp [e])
    by_cases hk : k % 2 = 1
    · simp only [literalConstAdd, hk, decide_true, literalConstSum]
      exact gp_cons _ _ (by simp [PhysicalInstr, ProperGate])
        (gp_single _ (by simp [PhysicalInstr, ProperGate, hxc.symm]))
    · simp only [literalConstAdd, hk, decide_false, literalConstSum]
      exact gp_single _ (by simp [PhysicalInstr, ProperGate, hxc.symm])
  | x :: x' :: xs, [], cin, one, k, _ => by simp [literalConstAdd, GatePhysical]
  | x :: x' :: xs, c :: cs, cin, one, k, hnd => by
    have h1 := List.nodup_cons.mp hnd
    have h2 := List.nodup_cons.mp h1.2
    have h3 := List.nodup_cons.mp h2.2
    have h4' := List.nodup_append'.mp h3.2
    have h5 := List.nodup_cons.mp h4'.2.1
    have h_oc : one ≠ cin := fun e => h1.1 (by simp [e])
    have h_ox : one ≠ x := fun e => h1.1 (by simp [e])
    have h_oc' : one ≠ c := fun e => h1.1 (by simp [e])
    have h_cx : cin ≠ x := fun e => h2.1 (by simp [e])
    have h_cc' : cin ≠ c := fun e => h2.1 (by simp [e])
    have h_xc' : x ≠ c := fun e => h3.1 (by simp [e])
    have hsub : (one :: c :: ((x' :: xs) ++ cs)).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_append'.mpr ⟨h4'.1, h5.2, ?_⟩⟩⟩
      · intro hm; apply h1.1
        simp only [List.mem_cons, List.mem_append] at hm ⊢
        rcases hm with rfl | hx | hcs
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inl (Or.inr hx))
        · exact Or.inr (Or.inr (Or.inr hcs))
      · intro hm; simp only [List.mem_append] at hm
        rcases hm with hx | hcs
        · exact h4'.2.2 hx (List.mem_cons_self)
        · exact h5.1 hcs
      · intro a ha hb; exact h4'.2.2 ha (List.mem_cons_of_mem c hb)
    have hStep : ∀ b, GatePhysical (literalConstStep b x cin c) ∧ GatePhysical (literalConstErase b x cin c one) := by
      intro b; cases b <;>
        simp [literalConstStep, literalConstErase, literalConstSum, literalConstCarry,
          GatePhysical, PhysicalInstr, ProperGate,
          h_oc, h_ox, h_oc', h_cx, h_cc', h_xc',
          h_oc.symm, h_ox.symm, h_oc'.symm, h_cx.symm, h_cc'.symm, h_xc'.symm]
    simp only [literalConstAdd, gatePhysical_append]
    exact ⟨⟨(hStep _).1, literalConstAdd_phys (x' :: xs) cs c one (k / 2) hsub⟩, (hStep _).2⟩

private theorem rename_swap_inv (a b : Wire) (P : Program) :
    renameProgram (Equiv.swap a b) (renameProgram (Equiv.swap a b) P) = P := by
  rw [renameProgram_comp]
  have hf : (Equiv.swap a b ∘ Equiv.swap a b) = id := by funext x; simp
  rw [hf]
  have hc : ∀ l : List Correction, l.map (renameCorrection id) = l := by
    intro l; induction l with | nil => rfl | cons c cs ih => cases c <;> simp [renameCorrection, ih]
  induction P with
  | nil => rfl
  | cons i ps ih =>
    simp only [renameProgram, List.map_cons]
    refine congrArg₂ List.cons ?_ ih
    cases i with
    | X _ => rfl
    | CX _ _ => rfl
    | CCX _ _ _ => rfl
    | measureX t z o => simp [renameInstr, hc]

private theorem compareLoan_phys_symm (d : Nat) (roles : List Wire) (fwd : Bool)
    (as bs cs : List Wire) (cin target : Wire) (hab : as.length = bs.length)
    (hda : ∀ a ∈ as, a ∉ cin :: cs) (hdb : ∀ b ∈ bs, b ∉ cin :: cs)
    (h0 : GatePhysical (compareLoan d roles fwd bs as cs cin target)) :
    GatePhysical (compareLoan d roles fwd as bs cs cin target) := by
  have hmaj : ∀ a b cin c, a ≠ cin → b ≠ cin →
      (GatePhysical (majority a b cin c) ↔ GatePhysical (majority b a cin c)) := by
    intro a b cin c hac hbc
    have hd : ∀ x y z w : Wire, y ≠ z → GatePhysical (majority x y z w) → GatePhysical (majority y x z w) := by
      intro x y z w hyz h
      simp only [majority, GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      intro g hg
      have h1 : x ≠ y := h _ (Or.inl rfl)
      have h3 : y ≠ w ∧ z ≠ w := h _ (Or.inr (Or.inr (Or.inl rfl)))
      have h4 : x ≠ w := h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1.symm
      · exact hyz
      · exact ⟨h4, h3.2⟩
      · exact h3.1
      · exact hyz
      · exact h1.symm
    exact ⟨hd a b cin c hbc, hd b a cin c hac⟩
  have her : ∀ a b cin c, GatePhysical (eraseCarry a b cin c) ↔ GatePhysical (eraseCarry b a cin c) := by
    intro a b cin c
    simp only [eraseCarry, GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨fun _ _ hg => by rcases hg with rfl; trivial, fun _ _ hg => by rcases hg with rfl; trivial⟩
  have hleaf : ∀ a b cin target, a ≠ cin → b ≠ cin →
      (GatePhysical (Q6LifetimeResearch.compareLeaf fwd a b cin target) ↔
       GatePhysical (Q6LifetimeResearch.compareLeaf fwd b a cin target)) := by
    intro a b cin target hac hbc
    cases fwd
    · simp only [Q6LifetimeResearch.compareLeaf, Bool.false_eq_true, if_false, gatePhysical_append, hmaj a b cin target hac hbc]
    · simp only [Q6LifetimeResearch.compareLeaf, if_true, gatePhysical_append, her]
  have hlay : ∀ (xs ys cs : List Wire) (cin : Wire),
      (∀ a ∈ xs, a ∉ cin :: cs) → (∀ b ∈ ys, b ∉ cin :: cs) →
      (compareLayers fwd xs ys cs cin target).map (fun l => (GatePhysical l.up, GatePhysical l.erase, GatePhysical l.finish)) =
      (compareLayers fwd ys xs cs cin target).map (fun l => (GatePhysical l.up, GatePhysical l.erase, GatePhysical l.finish)) := by
    intro xs; induction xs with
    | nil => intro ys cs cin _ _; simp [compareLayers]
    | cons a as ih =>
      intro ys cs cin ha hb
      cases as with
      | nil => cases ys <;> simp [compareLayers]
      | cons a' as' =>
        cases ys with
        | nil => simp [compareLayers]
        | cons b bs =>
          cases bs with
          | nil => simp [compareLayers]
          | cons b' bs' =>
            cases cs with
            | nil => simp [compareLayers]
            | cons c cs' =>
              have hac : a ≠ cin := fun e => ha a List.mem_cons_self (by simp [e])
              have hbc : b ≠ cin := fun e => hb b List.mem_cons_self (by simp [e])
              simp only [compareLayers, List.map_cons]
              refine congrArg₂ List.cons ?_ (ih (b' :: bs') cs' c
                (fun x hx hmem => ha x (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem cin hmem))
                (fun y hy hmem => hb y (List.mem_cons_of_mem b hy) (List.mem_cons_of_mem cin hmem)))
              cases fwd <;> simp [hmaj a b cin c hac hbc, her]
  have htop : ∀ (xs ys cs : List Wire) (cin : Wire), xs.length = ys.length →
      (∀ a ∈ xs, a ∉ cin :: cs) → (∀ b ∈ ys, b ∉ cin :: cs) →
      (GatePhysical (compareTop fwd xs ys cs cin target) ↔ GatePhysical (compareTop fwd ys xs cs cin target)) := by
    intro xs; induction xs with
    | nil => intro ys cs cin h _ _; cases ys <;> simp [compareTop] at h ⊢
    | cons a as ih =>
      intro ys cs cin h ha hb; cases ys with
      | nil => simp at h
      | cons b bs =>
        cases as with
        | nil => cases bs with
          | nil =>
            have hac : a ≠ cin := fun e => ha a List.mem_cons_self (by simp [e])
            have hbc : b ≠ cin := fun e => hb b List.mem_cons_self (by simp [e])
            simpa only [compareTop] using hleaf a b cin target hac hbc
          | cons _ _ => simp at h
        | cons a' as' => cases bs with
          | nil => simp at h
          | cons b' bs' => cases cs with
            | nil => simp [compareTop]
            | cons c cs' =>
              exact ih (b' :: bs') cs' c (by simp only [List.length_cons] at h ⊢; omega)
                (fun x hx hmem => ha x (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem cin hmem))
                (fun y hy hmem => hb y (List.mem_cons_of_mem b hy) (List.mem_cons_of_mem cin hmem))
  have hemit : ∀ xs ys : List StairLoan.CarryLayer,
      xs.map (fun l => (GatePhysical l.up, GatePhysical l.erase, GatePhysical l.finish)) =
      ys.map (fun l => (GatePhysical l.up, GatePhysical l.erase, GatePhysical l.finish)) →
      (GatePhysical (StairLoan.emitUps xs) ↔ GatePhysical (StairLoan.emitUps ys)) ∧
      (GatePhysical (StairLoan.emitErases xs) ↔ GatePhysical (StairLoan.emitErases ys)) ∧
      (GatePhysical (StairLoan.emitDowns xs) ↔ GatePhysical (StairLoan.emitDowns ys)) := by
    intro xs; induction xs with
    | nil => intro ys h; cases ys with | nil => simp [StairLoan.emitUps, StairLoan.emitErases, StairLoan.emitDowns] | cons _ _ => simp at h
    | cons x xs ih =>
      intro ys h; cases ys with
      | nil => simp at h
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
        have hr := ih ys h.2
        simp only [StairLoan.emitUps, StairLoan.emitErases, StairLoan.emitDowns,
          StairLoan.CarryLayer.down, gatePhysical_append, h.1.1, h.1.2.1, h.1.2.2, hr.1, hr.2.1, hr.2.2]
        exact ⟨trivial, trivial, trivial⟩
  have h1 := hemit ((compareLayers fwd as bs cs cin target).take (d + 1)) ((compareLayers fwd bs as cs cin target).take (d + 1))
    (by rw [List.map_take, List.map_take, hlay as bs cs cin hda hdb])
  have h2 := hemit ((compareLayers fwd as bs cs cin target).take d) ((compareLayers fwd bs as cs cin target).take d)
    (by rw [List.map_take, List.map_take, hlay as bs cs cin hda hdb])
  have h3 := hemit ((compareLayers fwd as bs cs cin target).drop (d + 1)) ((compareLayers fwd bs as cs cin target).drop (d + 1))
    (by rw [List.map_drop, List.map_drop, hlay as bs cs cin hda hdb])
  have hrb_drop : ∀ (rs hs : List Wire) (P : Program), GatePhysical (StairLoan.rebindMany rs hs P) → GatePhysical P := by
    intro rs; induction rs with
    | nil => intro _ _ hp; exact hp
    | cons r rs ih => intro hs P hp; cases hs with
      | nil => exact hp
      | cons hh hs =>
        simp only [StairLoan.rebindMany] at hp
        exact ih hs P (by rw [← rename_swap_inv r hh (StairLoan.rebindMany rs hs P)]; exact gatePhysical_rename _ (Equiv.injective _) _ hp)
  unfold compareLoan StairLoan.emitLoan at h0 ⊢
  simp only [gatePhysical_append] at h0 ⊢
  have hcore := hrb_drop _ _ _ h0.1.1.2
  have hcore' : GatePhysical (StairLoan.emitSweep ((compareLayers fwd as bs cs cin target).drop (d + 1))
        (compareTop fwd as bs cs cin target)) := by
    unfold StairLoan.emitSweep at hcore ⊢
    simp only [gatePhysical_append] at hcore ⊢
    exact ⟨⟨h3.1.mpr hcore.1.1, (htop as bs cs cin hab hda hdb).mpr hcore.1.2⟩, h3.2.2.mpr hcore.2⟩
  exact ⟨⟨⟨⟨h1.1.mpr h0.1.1.1.1, h2.2.1.mpr h0.1.1.1.2⟩,
    StairLoan.rebindMany_physical _ _ _ hcore'⟩, h2.1.mpr h0.1.2⟩, h1.2.2.mpr h0.2⟩

/-- Complete `GatePhysical` for `half760OddLoan d divide`. -/
theorem half760OddLoan_physical (d : Nat) (divide : Bool) :
    GatePhysical (half760OddLoan d divide) := by
  let L := Q6EndpointCell.ports base (base 2409)
  have hw := Q6EndpointCell.ports_widths base (base 2409)
  have w := BalancedCleanup.widths L.toLayout hw
  have hstd := StairLoanSupport.half760Loan_physical d divide
  have hscPhys : ∀ k, GatePhysical (Q6LifetimeResearch.move (base 760) L.rmsb (shortConstAddLoan d L k)) := by
    intro k
    have hndLit : (L.one :: L.low.getD 2 0 :: (L.low.drop 3 ++ L.carry.take 251)).Nodup :=
      PeakNodup.nodup_of_mask _ (by decide +kernel)
    have hlit0 : ∀ m, GatePhysical (literalConstAddLoan m retiredRoles (L.low.drop 3) (L.carry.take 251)
        (L.low.getD 2 0) L.one (k / 8)) := by
      intro m
      apply StairLoanSupport.literalConstAddLoan_physical_of_zero m retiredRoles
      · simpa only [literalConstAddLoan, if_pos rfl] using
          literalConstAdd_phys (L.low.drop 3) (L.carry.take 251) (L.low.getD 2 0) L.one (k / 8) hndLit
      · rw [mappedAddLoan_zero]
        apply mappedAdd_physical
        · exact (List.nodup_cons.mp hndLit).2
        · intro b hb q hq
          have impossible := mappedConstant_wires none (L.low.drop 3).length (k / 8) q (by
            simp only [mappedWires, List.mem_flatMap]
            exact ⟨b, hb, by simpa using hq⟩)
          simp at impossible
    rw [Q6LifetimeResearch.move]
    apply gatePhysical_rename _ (Equiv.injective _)
    unfold shortConstAddLoan
    split_ifs
    · exact (gatePhysical_append _ _).mpr ⟨hlit0 d, by simp [GatePhysical, PhysicalInstr, ProperGate]⟩
    · exact (gatePhysical_append _ _).mpr
        ⟨StairLoan.rebindMany_physical _ _ _ (hlit0 _), by simp [GatePhysical, PhysicalInstr, ProperGate]⟩
  have hpcPhys : GatePhysical (prepareCompare L) := by
    have hndR : L.r.Nodup := PeakNodup.nodup_of_mask _ (by decide +kernel)
    have hsy : L.sign ∉ L.y := by decide +kernel
    have hly : L.lower ∉ L.y := by decide +kernel
    have hlr : L.lower ≠ L.r0 := by decide +kernel
    simp only [prepareCompare, gatePhysical_append]
    exact ⟨⟨⟨⟨(rotate_physical L.r hndR).2, by simp [GatePhysical, PhysicalInstr, ProperGate, hlr]⟩,
      signComplement_physical L.sign L.y hsy⟩, signComplement_physical L.lower L.y hly⟩,
      by simp [GatePhysical, PhysicalInstr, ProperGate]⟩
  have hexpPhys : GatePhysical (exposure L) := by
    have hrl : L.r0 ≠ L.lower := by decide +kernel
    simp [exposure, GatePhysical, PhysicalInstr, ProperGate, hrl]
  have hcmpPhys : ∀ fwd,
      GatePhysical (compareLoan d retiredRoles fwd (L.y.drop 1) (L.r.drop 1)
        (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity) →
      GatePhysical (compareBlockLoan d fwd L) := by
    intro fwd hcmOld
    have h1 : L.r.getD 0 0 ≠ L.y.getD 0 0 ∧ L.r.getD 0 0 ≠ L.one ∧ L.r.getD 0 0 ≠ ((Q6Structural.q6Carry L).take 255).getD 0 0 ∧
        L.y.getD 0 0 ≠ L.one ∧ L.y.getD 0 0 ≠ ((Q6Structural.q6Carry L).take 255).getD 0 0 ∧
        L.one ≠ ((Q6Structural.q6Carry L).take 255).getD 0 0 := by decide +kernel
    have hnr : GatePhysical (notRegister (L.one :: L.y)) := by
      intro g hg; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hg; simp [PhysicalInstr, ProperGate]
    have hmaj : GatePhysical (majority (L.r.getD 0 0) (L.y.getD 0 0) L.one (((Q6Structural.q6Carry L).take 255).getD 0 0)) := by
      simp only [majority, GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
      intro g hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1.1
      · exact h1.2.1
      · exact ⟨h1.2.2.2.2.1, h1.2.2.2.2.2⟩
      · exact h1.2.2.1
      · exact h1.2.1
      · exact h1.1
    have her : GatePhysical (eraseCarry (L.r.getD 0 0) (L.y.getD 0 0) L.one (((Q6Structural.q6Carry L).take 255).getD 0 0)) := by
      simp [eraseCarry, GatePhysical, PhysicalInstr, ProperGate]
    have hda : ∀ a ∈ L.r.drop 1,
        a ∉ ((Q6Structural.q6Carry L).take 255).getD 0 0 :: ((Q6Structural.q6Carry L).take 255).drop 1 := by
      have hchk : (L.r.drop 1).all (fun a => decide (a ∉ ((Q6Structural.q6Carry L).take 255).getD 0 0 ::
          ((Q6Structural.q6Carry L).take 255).drop 1)) = true := by decide +kernel
      exact fun a ha => of_decide_eq_true (List.all_eq_true.mp hchk a ha)
    have hdb : ∀ b ∈ L.y.drop 1,
        b ∉ ((Q6Structural.q6Carry L).take 255).getD 0 0 :: ((Q6Structural.q6Carry L).take 255).drop 1 := by
      have hchk : (L.y.drop 1).all (fun b => decide (b ∉ ((Q6Structural.q6Carry L).take 255).getD 0 0 ::
          ((Q6Structural.q6Carry L).take 255).drop 1)) = true := by decide +kernel
      exact fun b hb => of_decide_eq_true (List.all_eq_true.mp hchk b hb)
    have hcmL := compareLoan_phys_symm d retiredRoles fwd (L.r.drop 1) (L.y.drop 1)
      (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0)
      L.parity (by simp [w.2.1, w.2.2.1]) hda hdb hcmOld
    simp only [compareBlockLoan, gatePhysical_append]
    exact ⟨⟨⟨⟨⟨⟨hnr, hmaj⟩, by simp [GatePhysical, PhysicalInstr, ProperGate]⟩,
      gatePhysical_rename _ (Equiv.injective _) _ hcmL⟩,
      by simp [GatePhysical, PhysicalInstr, ProperGate]⟩, her⟩, hnr⟩
  cases divide
  · simp only [StairLoan.half760Loan, Bool.false_eq_true, if_false, gatePhysical_append] at hstd
    have hinv : GatePhysical (StairLoan.inverseLoan d L) := hstd.1.1.2
    simp only [StairLoan.inverseLoan, gatePhysical_append] at hinv
    have hps : GatePhysical (BalancedCleanup.prepareSign L.toLayout) := hinv.1.1.1.1.1.1.1.1.1.1.1
    have hcmBlk : GatePhysical (StairLoan.compareBlockLoan d false L) := hinv.1.1.1.1.1.1.1.2
    have hub : GatePhysical (BiasedInverse.unbiasView L) := hinv.1.1.1.1.2
    have hufBlk : GatePhysical (StairLoan.unfoldLoan d L) := hinv.1.1.1.2
    have hrotL : GatePhysical (rotateLeft (BalancedCircuit.rawTarget L)) := hinv.1.1.2
    have hrsBlk : GatePhysical (StairLoan.rawSubTailLoan d L) := hinv.2
    simp only [StairLoan.compareBlockLoan, Q6LifetimeResearch.move, gatePhysical_append] at hcmBlk
    have hcmOld : GatePhysical (compareLoan d retiredRoles false (L.y.drop 1) (L.r.drop 1)
        (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity) := by
      rw [← rename_swap_inv (base 760) L.one (compareLoan d retiredRoles false (L.y.drop 1) (L.r.drop 1)
        (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity)]
      exact gatePhysical_rename _ (Equiv.injective _) _ hcmBlk.1.1.1.2
    simp only [StairLoan.unfoldLoan, gatePhysical_append] at hufBlk
    have hufMid := hufBlk.1.2
    simp only [StairLoan.rawSubTailLoan, gatePhysical_append] at hrsBlk
    have hsc_y := hrsBlk.1.1.1.1.1.1.1.1.1.1
    have hnr_t := hrsBlk.1.1.1.1.1.1.1.1.1.2
    have haddT := hrsBlk.1.1.1.1.1.1.2
    have hd1 : L.parity ≠ L.lower ∧ L.rmsb ≠ L.lower ∧ L.parity ≠ L.one ∧ L.lower ≠ L.one ∧
        L.lower ≠ L.rmsb ∧ L.parity ≠ L.rmsb := by decide +kernel
    obtain ⟨h_st, h_sc, h_tc, h_tp, h_yp, h_sp, h_ro⟩ :
        (GuardCompression.source L).getD 0 0 ≠ (BalancedCircuit.rawTarget L).getD 0 0 ∧
        (GuardCompression.source L).getD 0 0 ≠ ((Q6Structural.q6Carry L).take 255).getD 0 0 ∧
        (BalancedCircuit.rawTarget L).getD 0 0 ≠ ((Q6Structural.q6Carry L).take 255).getD 0 0 ∧
        (BalancedCircuit.rawTarget L).getD 0 0 ≠ L.parity ∧
        L.ylow.getD 0 0 ≠ L.parity ∧ L.sign ≠ L.parity ∧ L.rmsb ≠ L.one := by decide +kernel
    have huf : GatePhysical (unfoldLoan d L) := by
      simp only [unfoldLoan, gatePhysical_append]
      refine ⟨⟨?_, hufMid⟩, ?_⟩
      · simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
        intro g hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hd1.1
        · exact hd1.2.1
        · trivial
        · exact ⟨hd1.2.2.1, hd1.2.2.2.1⟩
        · exact hd1.2.2.2.2.1
        · exact hd1.2.2.2.2.2
        · trivial
      · simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
        intro g hg; rcases hg with rfl | rfl | rfl
        · exact hd1.2.2.2.2.1
        · exact hd1.2.1
        · trivial
    have hrec : GatePhysical ([.CX L.parity L.r0] : Program) := by
      have hpr : L.parity ≠ L.r0 := by decide +kernel
      simp [GatePhysical, PhysicalInstr, ProperGate, hpr]
    have hrs : GatePhysical (rawSubLoan d L) := by
      simp only [rawSubLoan, orMajor, orErase, gatePhysical_append]
      refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsc_y, hnr_t⟩, ?_⟩, ?_⟩, haddT⟩, ?_⟩, ?_⟩, ?_⟩, hnr_t⟩, hsc_y⟩, ?_⟩
      · simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
        intro g hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
        · trivial
        · trivial
        · exact ⟨h_sc, h_tc⟩
        · trivial
        · trivial
        · trivial
      · simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
        intro g hg; rcases hg with rfl | rfl; trivial; exact h_tp.symm
      · simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
        intro g hg; rcases hg with rfl | rfl; exact h_tp.symm; trivial
      · simp [GatePhysical, PhysicalInstr, ProperGate]
      · simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
        intro g hg; rcases hg with rfl | rfl; exact h_st; trivial
      · simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
        intro g hg; rcases hg with rfl | rfl | rfl | rfl | rfl
        · exact h_tp
        · exact h_yp
        · exact h_sp
        · trivial
        · exact h_ro
    simp only [half760OddLoan, inverseLoan, Bool.false_eq_true, if_false, gatePhysical_append]
    exact ⟨⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
      ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hps, hscPhys (encodeWord 255 (-h))⟩,
        hpcPhys⟩, hexpPhys⟩, hcmpPhys false hcmOld⟩, gp_reverse _ hexpPhys⟩,
        gp_reverse _ hpcPhys⟩, hub⟩, huf⟩, hrotL⟩, hrec⟩, hrs⟩⟩,
      by simp [GatePhysical, PhysicalInstr, ProperGate]⟩
  · simp only [StairLoan.half760Loan, if_true, List.append_nil, gatePhysical_append] at hstd
    have hfwd : GatePhysical (StairLoan.forwardLoan d L) := hstd.1.2
    simp only [StairLoan.forwardLoan, gatePhysical_append] at hfwd
    have hraBlk := hfwd.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    have hnp := hfwd.1.1.1.1.1.1.1.1.1.1.1.1.2
    have hrotR := hfwd.1.1.1.1.1.1.1.1.1.1.1.2
    have hfoBlk := hfwd.1.1.1.1.1.1.1.1.1.1.2
    have hps := hfwd.1.1.1.1.1.1.1.1.1.2
    have hfb := hfwd.1.1.1.1.1.1.1.1.2
    have hcmBlk := hfwd.1.1.1.1.1.2
    have hpsR := hfwd.1.2
    simp only [StairLoan.rawAddLoan, gatePhysical_append] at hraBlk
    have hsc_y := hraBlk.1.1.1.1.1.1.1
    have haddP := hraBlk.1.1.1.1.2
    simp only [StairLoan.foldLoan, gatePhysical_append] at hfoBlk
    have hfoPre := hfoBlk.1.1
    have hfoMid := hfoBlk.1.2
    simp only [StairLoan.compareBlockLoan, Q6LifetimeResearch.move, gatePhysical_append] at hcmBlk
    have hcmOld : GatePhysical (compareLoan d retiredRoles true (L.y.drop 1) (L.r.drop 1)
        (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity) := by
      rw [← rename_swap_inv (base 760) L.one (compareLoan d retiredRoles true (L.y.drop 1) (L.r.drop 1)
        (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity)]
      exact gatePhysical_rename _ (Equiv.injective _) _ hcmBlk.1.1.1.2
    have hd1 : L.rmsb ≠ L.one ∧ L.ylow.getD 0 0 ≠ L.parity ∧ L.r0 ≠ L.parity ∧ L.sign ≠ L.parity := by
      decide +kernel
    have hd2 : L.ylow.getD 0 0 ≠ L.low.getD 0 0 ∧
        L.ylow.getD 0 0 ≠ ((Q6Structural.q6Carry L).take 255).getD 0 0 ∧
        L.low.getD 0 0 ≠ ((Q6Structural.q6Carry L).take 255).getD 0 0 ∧
        L.parity ≠ L.low.getD 0 0 := by decide +kernel
    have hd3 : L.lower ≠ L.rmsb ∧ L.parity ≠ L.rmsb ∧ L.parity ≠ L.lower ∧
        L.rmsb ≠ L.lower ∧ L.parity ≠ L.one ∧ L.rmsb ≠ L.one := by decide +kernel
    have hsd : GatePhysical (p1Seed L) := by
      simp only [p1Seed, GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
      intro g hg; rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact hd1.1
      · exact hd1.2.1
      · exact hd1.2.2.1
      · exact hd1.2.2.2
      · trivial
    have hra : GatePhysical (rawAddLoan d L) := by
      simp only [rawAddLoan, orMajor, orErase, gatePhysical_append]
      refine ⟨⟨⟨⟨⟨⟨⟨hsc_y, ?_⟩, ?_⟩, haddP⟩, ?_⟩, ?_⟩, ?_⟩, hsc_y⟩
      · simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
        intro g hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
        · trivial
        · trivial
        · exact ⟨hd2.2.1, hd2.2.2.1⟩
        · trivial
        · trivial
        · trivial
      · simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
        intro g hg; rcases hg with rfl | rfl | rfl; exact hd2.2.2.2; exact hd2.1; trivial
      · apply gp_reverse
        simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
        intro g hg; rcases hg with rfl | rfl | rfl; exact hd2.2.2.2; exact hd2.1; trivial
      · simp [GatePhysical, PhysicalInstr, ProperGate]
      · simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
        intro g hg; rcases hg with rfl | rfl; exact hd2.1; trivial
    have hfo : GatePhysical (foldLoan d L) := by
      simp only [foldLoan, gatePhysical_append]
      refine ⟨⟨hfoPre, hfoMid⟩, ?_⟩
      simp only [GatePhysical, PhysicalInstr, ProperGate, List.mem_cons, List.not_mem_nil, or_false]
      intro g hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hd3.1
      · exact hd3.2.1
      · trivial
      · exact hd3.2.2.1
      · exact hd3.2.2.2.1
      · trivial
      · trivial
    simp only [half760OddLoan, forwardLoan, if_true, gatePhysical_append]
    exact ⟨⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
      ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsd, hra⟩, hnp⟩, hrotR⟩, hfo⟩, hps⟩, hfb⟩,
        hpcPhys⟩, hexpPhys⟩, hcmpPhys true hcmOld⟩, gp_reverse _ hexpPhys⟩,
        gp_reverse _ hpcPhys⟩, hscPhys h.toNat⟩, hpsR⟩⟩,
      by simp [GatePhysical, PhysicalInstr, ProperGate]⟩

theorem packet_physical (divide : Bool) (d j : Nat) (hj : j < 102) :
    GatePhysical (packet divide d j) := by
  have hbase := StairPhysicalV3.loanBasePacket_physical divide d j hj
  have hcell : ∀ active hole, GatePhysical (StairGroups.cell divide d j active hole) →
      GatePhysical (cell divide d j active hole) := by
    intro active hole hsc
    have hhw : GatePhysical (StairGroups.halfWindow divide d j active hole) →
        GatePhysical (halfWindow divide d j active hole) := by
      intro hsh
      simp only [halfWindow, StairGroups.halfWindow, ControlLoan1589.loanWindow, gatePhysical_append] at hsh ⊢
      exact ⟨⟨hsh.1.1, gatePhysical_rename _ (Equiv.injective _) _
        (gatePhysical_rename _ (Equiv.injective _) _ (half760OddLoan_physical d divide))⟩, hsh.2⟩
    cases divide <;> simp only [cell, StairGroups.cell, Bool.false_eq_true, if_false, if_true, gatePhysical_append] at hsc ⊢
    · exact ⟨hsc.1, hhw hsc.2⟩
    · exact ⟨hhw hsc.1, hsc.2⟩
  simp only [packet]
  apply gatePhysical_rename _ (Equiv.injective _)
  cases divide <;>
    simp only [basePacket, StairGroups.basePacket, Bool.false_eq_true, if_false, if_true,
      gatePhysical_append] at hbase ⊢
  · exact ⟨⟨hbase.1.1, ⟨⟨⟨⟨⟨⟨hcell 4 2 hbase.1.2.1.1.1.1.1.1, hbase.1.2.1.1.1.1.1.2⟩,
      hcell 3 2 hbase.1.2.1.1.1.1.2⟩, hcell 4 2 hbase.1.2.1.1.1.2⟩,
      hbase.1.2.1.1.2⟩, hcell 4 2 hbase.1.2.1.2⟩, hcell 3 2 hbase.1.2.2⟩⟩, hbase.2⟩
  · exact ⟨⟨hbase.1.1, ⟨⟨⟨⟨⟨⟨hcell 3 2 hbase.1.2.1.1.1.1.1.1, hcell 4 2 hbase.1.2.1.1.1.1.1.2⟩,
      hbase.1.2.1.1.1.1.2⟩, hcell 4 2 hbase.1.2.1.1.1.2⟩, hcell 3 2 hbase.1.2.1.1.2⟩,
      hbase.1.2.1.2⟩, hcell 4 2 hbase.1.2.2⟩⟩, hbase.2⟩

theorem hostedGroup_physical (h : StairHostsSchedule.HostPlan) (divide : Bool)
    (d first count : Nat) (hfc : first + count ≤ 102) :
    GatePhysical (hostedGroup h divide d first count) := by
  unfold hostedGroup placedGroups groups
  apply StairLoan.rebindMany_physical
  apply gatePhysical_rename _ (OB5.sig_injective 511 (by decide))
  induction count generalizing first with
  | zero => simp [PacketSequence.program, GatePhysical]
  | succ n ih =>
    have hp := packet_physical divide d first (by omega)
    have hr := ih (first + 1) (by omega)
    cases divide <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
      gatePhysical_append]
    · exact ⟨hr, hp⟩
    · exact ⟨hp, hr⟩

/-- Clean-wire + carry-loan drop for `shortConstAddLoan d`: for every `d ≤ 43` (`d ≠ 42`),
    when `L.carry`, `L.parity`, and `L.one` are clean (`false`), `shortConstAddLoan d L k`
    runs identically to `shortConstAddLoan 0 L k` for independent measurement tapes. -/
theorem shortConstAddLoan_run_eq (d : Nat) (hd : d ≤ 43) (h42 : d ≠ 42) (k : Nat)
    (hk : k / 8 < 2 ^ 252) (s : State) (m n : List Bool)
    (hcar : ∀ q ∈ (Q6EndpointCell.ports base (base 2409)).carry, s.basis q = false)
    (hone : s.basis (Q6EndpointCell.ports base (base 2409)).one = false)
    (hpar : s.basis (Q6EndpointCell.ports base (base 2409)).parity = false) :
    let L := Q6EndpointCell.ports base (base 2409)
    run (shortConstAddLoan d L k) m s = run (shortConstAddLoan 0 L k) n s := by
  intro L
  have hw := Q6EndpointCell.ports_widths base (base 2409)
  have w := BalancedCleanup.widths L.toLayout hw
  have hcl251 : (L.carry.take 251).length = 251 := by decide +kernel
  have hnd : (L.one :: L.low.getD 2 0 :: (L.low.drop 3 ++ L.carry.take 251)).Nodup :=
    PeakNodup.nodup_of_mask _ (by decide +kernel)
  have hlitEq : ∀ m0, m0 ≤ 42 →
      (∀ q ∈ retiredRoles.take m0, q ∈ (L.carry.take 251).drop (m0 + 1)) →
      ∀ a b,
        run (literalConstAddLoan m0 retiredRoles (L.low.drop 3) (L.carry.take 251)
          (L.low.getD 2 0) L.one (k / 8)) a s =
        run (literalConstAdd (L.low.drop 3) (L.carry.take 251)
          (L.low.getD 2 0) L.one (k / 8)) b s := by
    intro m0 hm0 hrt a b
    exact StairLoan.literalConstAddLoan_run_eq m0 retiredRoles (L.low.drop 3) (L.carry.take 251)
      (L.low.getD 2 0) L.one (k / 8) s a b hnd
      (by simp [w.1, hcl251]) (by simpa [w.1] using hk) (by rw [hcl251]; omega)
      hone (fun q hq => hcar q (List.mem_of_mem_take hq)) hrt
  have hrt42 : ∀ m0 ≤ 42, ∀ q ∈ retiredRoles.take m0, q ∈ (L.carry.take 251).drop (m0 + 1) := by
    have hchk : (List.range 43).all (fun m0 =>
        (retiredRoles.take m0).all (fun q => decide (q ∈ (L.carry.take 251).drop (m0 + 1)))) = true := by
      decide +kernel
    intro m0 hm0 q hq
    have hm := List.all_eq_true.mp hchk m0 (List.mem_range.mpr (by omega))
    exact of_decide_eq_true (List.all_eq_true.mp hm q hq)
  have h0eq : shortConstAddLoan 0 L k =
      literalConstAdd (L.low.drop 3) (L.carry.take 251) (L.low.getD 2 0) L.one (k / 8) ++
      [Instr.X (L.low.getD 2 0)] := by
    simp [shortConstAddLoan, literalConstAddLoan]
  rw [h0eq]
  unfold shortConstAddLoan
  split_ifs with h6
  · rw [run_append, run_append,
        hlitEq d (by omega) (hrt42 d (by omega)) _ (n.take _)]
    exact FifthCarry.no_records [.X (L.low.getD 2 0)] rfl _ _ _
  · set free := shortFreeHosts d
    set dEff := Nat.min d 42 - free.length
    set remRoles := (retiredRoles.take (Nat.min d 42)).drop dEff
    have hfl : free.length = if d ≤ 41 then 5 else 4 := by
      unfold free shortFreeHosts; split_ifs <;> rfl
    have hdEff_eq : dEff = d - 5 := by
      unfold dEff; rw [hfl]; unfold Nat.min; split_ifs <;> omega
    have hlenEq : remRoles.length = free.length := by
      simp only [remRoles, List.length_drop, List.length_take, retiredRoles_length]
      rw [hfl, hdEff_eq]; unfold Nat.min; split_ifs <;> omega
    have hndRF : (remRoles ++ free).Nodup := by
      have h41nd : ∀ m0 ≤ 41, ((retiredRoles.take m0).drop (m0 - 5) ++
          [base 763, base 764, base 1540, base 768, base 1027]).Nodup := by
        have hchk : (List.range 42).all (fun m0 =>
            decide (((retiredRoles.take m0).drop (m0 - 5) ++
              [base 763, base 764, base 1540, base 768, base 1027]).Nodup)) = true := by decide +kernel
        intro m0 hm0; exact of_decide_eq_true (List.all_eq_true.mp hchk m0 (List.mem_range.mpr (by omega)))
      by_cases h41 : d ≤ 41
      · simpa only [remRoles, dEff, free, shortFreeHosts, h41, if_true, Nat.min_eq_left (by omega : d ≤ 42)]
          using h41nd d h41
      · have hd43 : d = 43 := by omega
        subst hd43
        simpa only [remRoles, dEff, free, shortFreeHosts] using (by decide +kernel :
          ((retiredRoles.take 42).drop 38 ++ [base 764, base 1540, base 768, base 1027]).Nodup)
    have hremClean : ∀ q ∈ remRoles, s.basis q = false := by
      have hchk : (retiredRoles.take 42).all (fun q => decide (q ∈ L.carry)) = true := by decide +kernel
      intro q hq
      have hq42 : q ∈ retiredRoles.take 42 :=
        (List.take_sublist_take_left (Nat.min_le_right d 42)).subset (List.mem_of_mem_drop hq)
      exact hcar q (of_decide_eq_true (List.all_eq_true.mp hchk q hq42))
    have hfreeClean : ∀ q ∈ free, s.basis q = false := by
      intro q hq
      unfold free shortFreeHosts at hq
      by_cases h41 : d ≤ 41
      · rw [if_pos h41] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        · exact hcar _ (by decide +kernel)
        · exact hcar _ (by decide +kernel)
        · exact hcar _ (by decide +kernel)
        · exact hpar
        · exact hone
      · rw [if_neg h41] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact hcar _ (by decide +kernel)
        · exact hcar _ (by decide +kernel)
        · exact hpar
        · exact hone
    have hfreeAvoid : ∀ q ∈ free, q ∉ wires (literalConstAddLoan dEff retiredRoles
        (L.low.drop 3) (L.carry.take 251) (L.low.getD 2 0) L.one (k / 8)) := by
      intro q hq hw'
      have hde : dEff ≠ 0 := by rw [hdEff_eq]; omega
      have hmcAway : ∀ (n0 m0 : Nat) (z : Wire), z ∈ mappedWires ((mappedConstant none n0 (k / 8)).take m0) → False := by
        intro n0 m0 z hz
        have hm : z ∈ mappedWires (mappedConstant none n0 (k / 8)) := by
          simp only [mappedWires, List.mem_flatMap] at hz ⊢
          obtain ⟨b, hb, hzb⟩ := hz; exact ⟨b, List.mem_of_mem_take hb, hzb⟩
        exact absurd (mappedConstant_wires none n0 (k / 8) z hm) (by simp)
      have hmw : wires (literalConstAddLoan dEff retiredRoles (L.low.drop 3) (L.carry.take 251)
          (L.low.getD 2 0) L.one (k / 8)) ⊆ (L.low.getD 2 0 :: (L.low.drop 3 ++ L.carry.take 251)).toFinset := by
        unfold literalConstAddLoan
        rw [if_neg hde]
        have hlift := StairLoanSupport.mappedAddLoan_support_lift dEff retiredRoles
          (mappedConstant none (L.low.drop 3).length (k / 8)) (L.low.drop 3) (L.carry.take 251)
          (L.low.getD 2 0) (by simp [mappedConstant_length])
          (by simp [w.1, hcl251]) (by rw [hcl251, hdEff_eq]; omega)
          (by rw [retiredRoles_length, hdEff_eq]; omega)
          (List.nodup_cons.mp hnd).2
          (fun z hz => absurd (mappedConstant_wires none _ _ z hz) (by simp))
          (by
            have h42nd : (retiredRoles.take 42 ++ (L.carry.take 251).take 42).Nodup :=
              PeakNodup.nodup_of_mask _ (by decide +kernel)
            exact h42nd.sublist (List.Sublist.append
              (List.take_sublist_take_left (by rw [hdEff_eq]; omega))
              (List.take_sublist_take_left (by rw [hdEff_eq]; omega))))
          (fun r hr hm' => by
            have h42away : (retiredRoles.take 42).all (fun z =>
                decide (z ∉ L.low ∧ z ∉ (L.carry.take 251).take 43)) = true := by decide +kernel
            have ha := of_decide_eq_true (List.all_eq_true.mp h42away r
              ((List.take_sublist_take_left (by rw [hdEff_eq]; omega)).subset hr))
            rw [List.mem_toFinset] at hm'
            simp only [List.mem_append, List.mem_singleton] at hm'
            rcases hm' with ((h1 | h2) | h3) | h4
            · exact hmcAway _ _ r h1
            · exact ha.1 (List.mem_of_mem_drop (List.mem_of_mem_take h2))
            · exact ha.2 ((List.take_sublist_take_left (by rw [hdEff_eq]; omega)).subset h3)
            · exact ha.1 (by rw [h4]; decide +kernel))
        intro z hz
        rcases Finset.mem_union.mp (hlift hz) with hz0 | hh
        · have maw := mappedAdd_wires_subset _ _ _ _ (Finset.mem_sdiff.mp hz0).1
          simp only [List.mem_toFinset, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at maw ⊢
          rcases maw with ((hsrc | hlow) | hcar) | rfl
          · exact absurd (mappedConstant_wires none _ _ z hsrc) (by simp)
          · exact Or.inr (Or.inl hlow)
          · exact Or.inr (Or.inr hcar)
          · exact Or.inl rfl
        · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_append_right _
            (List.mem_of_mem_take (List.mem_toFinset.mp hh))))
      have hfreeOut : free.all (fun z => decide (z ∉ L.low.getD 2 0 :: (L.low.drop 3 ++ L.carry.take 251))) = true := by
        unfold free shortFreeHosts; by_cases h41 : d ≤ 41 <;> simp [h41] <;> decide +kernel
      exact of_decide_eq_true (List.all_eq_true.mp hfreeOut q hq) (List.mem_toFinset.mp (hmw hw'))
    have hrest : ∀ q ∈ remRoles,
        (run (literalConstAddLoan dEff retiredRoles (L.low.drop 3) (L.carry.take 251)
          (L.low.getD 2 0) L.one (k / 8))
          (m.take (measurementCount (StairLoan.rebindMany remRoles free
            (literalConstAddLoan dEff retiredRoles (L.low.drop 3) (L.carry.take 251)
              (L.low.getD 2 0) L.one (k / 8))))) s).basis q = false := by
      intro q hq
      rw [hlitEq dEff (by rw [hdEff_eq]; omega) (hrt42 dEff (by rw [hdEff_eq]; omega)) _ []]
      have hlc := literalConstAdd_correct (L.low.drop 3) (L.carry.take 251) (L.low.getD 2 0) L.one (k / 8)
        hnd (by simp [w.1, hcl251]) s [] hone
        (fun z hz => hcar z (List.mem_of_mem_take hz))
      have hqNotLow : q ∉ L.low.drop 3 := by
        have hchk : (retiredRoles.take 42).all (fun z => decide (z ∉ L.low.drop 3)) = true := by decide +kernel
        exact of_decide_eq_true (List.all_eq_true.mp hchk q
          ((List.take_sublist_take_left (Nat.min_le_right d 42)).subset (List.mem_of_mem_drop hq)))
      exact (hlc.2.1 q hqNotLow).trans (hremClean q hq)
    rw [run_append, run_append,
        HalfConvertOdd.rebindMany_run_eq_of_clean remRoles free _ hlenEq hndRF hfreeAvoid s _ hremClean hfreeClean hrest,
        hlitEq dEff (by rw [hdEff_eq]; omega) (hrt42 dEff (by rw [hdEff_eq]; omega)) _ (n.take _)]
    exact FifthCarry.no_records [.X (L.low.getD 2 0)] rfl _ _ _

section
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Arithmetic Challenge MappedCompressed Secp256k1 BalancedField BalancedCircuit
open StairLoan StairLoanSupport OddFullPass

private abbrev L760 : BalancedCircuit.Layout := Q6EndpointCell.ports base (base 2409)

private theorem retiredRoles_drop1_tail (d : Nat) (hd : d ≤ 68) :
    ∀ q ∈ retiredRoles.take d, q ∈ (((Q6Structural.q6Carry L760).take 255).drop 1).drop (d + 1) :=
  StairLoan.retiredRoles_q6Tail d hd

private theorem retiredRoles_254_tail (d : Nat) (hd : d ≤ 68) :
    ∀ q ∈ retiredRoles.take d, q ∈ (L760.carry.take 254).drop (d + 1) := by
  have h69 : (retiredRoles.take 68).all (fun q => decide (q ∈ (L760.carry.take 254).drop 69)) = true := by
    decide +kernel
  intro q hq
  have h1 : q ∈ (L760.carry.take 254).drop 69 :=
    of_decide_eq_true (List.all_eq_true.mp h69 q ((List.take_sublist_take_left hd).subset hq))
  have hsub : ((L760.carry.take 254).drop 69).Sublist ((L760.carry.take 254).drop (d + 1)) := by
    have hle : d + 1 ≤ 69 := by omega
    rw [show 69 = (d + 1) + (69 - (d + 1)) by omega, ← List.drop_drop]
    exact List.drop_sublist _ _
  exact hsub.subset h1

/-- Loan drop for `addPrefixLoan` inside `rawAddLoan d L760`. -/
theorem addPrefixLoan_760_run_eq (d : Nat) (hd : d ≤ 68) (s : State) (m n : List Bool)
    (top : s.basis L760.one = s.basis L760.rmsb)
    (clean : ∀ q ∈ ((Q6Structural.q6Carry L760).take 255).drop 1 ++ [L760.carry.getD 255 0], s.basis q = false) :
    run (addPrefixLoan d retiredRoles (L760.ylow.drop 1) (L760.low.drop 1)
      (((Q6Structural.q6Carry L760).take 255).drop 1) L760.ymsb L760.rmsb L760.one
      (((Q6Structural.q6Carry L760).take 255).getD 0 0)) m s =
    run (addPrefixLoan 0 retiredRoles (L760.ylow.drop 1) (L760.low.drop 1)
      (((Q6Structural.q6Carry L760).take 255).drop 1) L760.ymsb L760.rmsb L760.one
      (((Q6Structural.q6Carry L760).take 255).getD 0 0)) n s := by
  have hnd : (L760.ylow.drop 1 ++ [L760.ymsb] ++ L760.low.drop 1 ++ [L760.rmsb, L760.one] ++
      ((Q6Structural.q6Carry L760).take 255).drop 1 ++ [L760.carry.getD 255 0, ((Q6Structural.q6Carry L760).take 255).getD 0 0]).Nodup :=
    PeakNodup.nodup_of_mask _ (by decide +kernel)
  have hlen : (((Q6Structural.q6Carry L760).take 255).drop 1).length = 254 := by decide +kernel
  have h1 := StairLoan.addPrefixLoan_run_eq d retiredRoles (L760.ylow.drop 1) (L760.low.drop 1)
    (((Q6Structural.q6Carry L760).take 255).drop 1) L760.ymsb L760.rmsb L760.one (L760.carry.getD 255 0)
    (((Q6Structural.q6Carry L760).take 255).getD 0 0) s m n
    (by decide +kernel) (by decide +kernel) (by omega)
    hnd top clean (retiredRoles_drop1_tail d hd)
  rw [StairLoan.addPrefixLoan_zero]; exact h1

/-- Loan drop for `mappedAddLoan` inside `foldLoan d L760`. -/
theorem mappedAddLoan_760_run_eq (d : Nat) (hd : d ≤ 68) (s : State) (m n : List Bool)
    (clean : ∀ q ∈ L760.carry.take 254, s.basis q = false) :
    run (mappedAddLoan d retiredRoles (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one) m s =
    run (mappedAddLoan 0 retiredRoles (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one) n s := by
  have hnd : (L760.one :: (L760.low ++ L760.carry.take 254)).Nodup :=
    PeakNodup.nodup_of_mask _ (by decide +kernel)
  have haway : ∀ q ∈ mappedWires (ShortBiasedFold.lowBits L760), q ∉ L760.one :: (L760.low ++ L760.carry.take 254) := by
    have hchk : (mappedWires (ShortBiasedFold.lowBits L760)).all
        (fun q => decide (q ∉ L760.one :: (L760.low ++ L760.carry.take 254))) = true := by decide +kernel
    exact fun q hq => of_decide_eq_true (List.all_eq_true.mp hchk q hq)
  have hlen : (L760.carry.take 254).length = 254 := by decide +kernel
  have h1 := StairLoan.mappedAddLoan_run_eq d retiredRoles (ShortBiasedFold.lowBits L760) L760.low
    (L760.carry.take 254) L760.one s m n hnd haway (by decide +kernel) (by decide +kernel)
    (by omega) clean (retiredRoles_254_tail d hd)
  rw [StairLoan.mappedAddLoan_zero]; exact h1

/-- Loan drop for `mappedSubLoan` inside `unfoldLoan d L760`. -/
theorem mappedSubLoan_760_run_eq (d : Nat) (hd : d ≤ 68) (s : State) (m n : List Bool)
    (clean : ∀ q ∈ L760.carry.take 254, s.basis q = false) :
    run (mappedSubLoan d retiredRoles (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one) m s =
    run (mappedSubLoan 0 retiredRoles (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one) n s := by
  have hnd : (L760.one :: (L760.low ++ L760.carry.take 254)).Nodup :=
    PeakNodup.nodup_of_mask _ (by decide +kernel)
  have haway : ∀ q ∈ mappedWires (ShortBiasedFold.lowBits L760), q ∉ L760.one :: (L760.low ++ L760.carry.take 254) := by
    have hchk : (mappedWires (ShortBiasedFold.lowBits L760)).all
        (fun q => decide (q ∉ L760.one :: (L760.low ++ L760.carry.take 254))) = true := by decide +kernel
    exact fun q hq => of_decide_eq_true (List.all_eq_true.mp hchk q hq)
  have hlen : (L760.carry.take 254).length = 254 := by decide +kernel
  have h1 := StairLoan.mappedSubLoan_run_eq d retiredRoles (ShortBiasedFold.lowBits L760) L760.low
    (L760.carry.take 254) L760.one s m n hnd haway (by decide +kernel) (by decide +kernel)
    (by omega) clean (retiredRoles_254_tail d hd)
  rw [StairLoan.mappedSubLoan_zero]; exact h1

/-- Loan drop for `addTopLoan` inside `rawSubLoan d L760`. -/
theorem addTopLoan_760_run_eq (d : Nat) (hd : d ≤ 68) (s : State) (m n : List Bool)
    (clean : ∀ q ∈ ((Q6Structural.q6Carry L760).take 255).drop 1 ++ [L760.carry.getD 255 0], s.basis q = false)
    (post : (run (addInPlace (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb])
        (L760.low.drop 1 ++ [L760.rmsb, L760.one])
        (((Q6Structural.q6Carry L760).take 255).drop 1 ++ [L760.carry.getD 255 0])
        (((Q6Structural.q6Carry L760).take 255).getD 0 0)) n s).basis L760.one =
      (run (addInPlace (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb])
        (L760.low.drop 1 ++ [L760.rmsb, L760.one])
        (((Q6Structural.q6Carry L760).take 255).drop 1 ++ [L760.carry.getD 255 0])
        (((Q6Structural.q6Carry L760).take 255).getD 0 0)) n s).basis L760.rmsb) :
    run (addTopLoan d retiredRoles ((GuardCompression.source L760).drop 1)
      ((BalancedCircuit.rawTarget L760).drop 1)
      (((Q6Structural.q6Carry L760).take 255).drop 1)
      (((Q6Structural.q6Carry L760).take 255).getD 0 0)) m s =
    run (addTopLoan 0 retiredRoles ((GuardCompression.source L760).drop 1)
      ((BalancedCircuit.rawTarget L760).drop 1)
      (((Q6Structural.q6Carry L760).take 255).drop 1)
      (((Q6Structural.q6Carry L760).take 255).getD 0 0)) n s := by
  have hsrc : (GuardCompression.source L760).drop 1 = L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb] := by decide +kernel
  have htgt : (BalancedCircuit.rawTarget L760).drop 1 = L760.low.drop 1 ++ [L760.rmsb, L760.one] := by decide +kernel
  have hnd : (L760.ylow.drop 1 ++ [L760.ymsb] ++ L760.low.drop 1 ++ [L760.rmsb, L760.one] ++
      ((Q6Structural.q6Carry L760).take 255).drop 1 ++ [L760.carry.getD 255 0, ((Q6Structural.q6Carry L760).take 255).getD 0 0]).Nodup :=
    PeakNodup.nodup_of_mask _ (by decide +kernel)
  have hlen : (((Q6Structural.q6Carry L760).take 255).drop 1).length = 254 := by decide +kernel
  rw [hsrc, htgt, StairLoan.addTopLoan_zero]
  exact StairLoanInverse.addTopLoan_run_eq d retiredRoles (L760.ylow.drop 1) (L760.low.drop 1)
    (((Q6Structural.q6Carry L760).take 255).drop 1) L760.ymsb L760.rmsb L760.one (L760.carry.getD 255 0)
    (((Q6Structural.q6Carry L760).take 255).getD 0 0) s m n
    (by decide +kernel) (by decide +kernel) (by omega)
    hnd clean (retiredRoles_drop1_tail d hd) post

/-- Involutive wire permutation swapping `L760.r` (`base 2056..2311`) with
    `L760.y` (`base 770..1025`) while fixing every carry, flag, and retired role wire. -/
private def swapRYNatFn (q : Nat) : Nat :=
  if 770 ≤ q ∧ q < 1026 then q + 1286
  else if 2056 ≤ q ∧ q < 2312 then q - 1286
  else q

private theorem swapRYNatFn_invol (q : Nat) : swapRYNatFn (swapRYNatFn q) = q := by
  simp only [swapRYNatFn]; split_ifs <;> omega

private def swapRYNat : Equiv.Perm Nat :=
  ⟨swapRYNatFn, swapRYNatFn, swapRYNatFn_invol, swapRYNatFn_invol⟩

private def swapRY : Wire ≃ Wire := shifted swapRYNat

private theorem swapRY_invol (q : Wire) : swapRY (swapRY q) = q :=
  Equiv.apply_symm_apply swapRY q

private theorem rename_compareLoan_eq (f : Wire ≃ Wire) (d : Nat) (roles : List Wire) (fwd : Bool)
    (as bs cs : List Wire) (cin target : Wire)
    (hroles : roles.map f = roles) (hcs : cs.map f = cs) (hcin : f cin = cin) (htgt : f target = target) :
    renameProgram f (compareLoan d roles fwd as bs cs cin target) =
      compareLoan d roles fwd (as.map f) (bs.map f) cs cin target := by
  have hrmaj : ∀ a b z w, renameProgram f (majority a b z w) = majority (f a) (f b) (f z) (f w) := fun _ _ _ _ => rfl
  have hrer : ∀ a b z w, renameProgram f (eraseCarry a b z w) = eraseCarry (f a) (f b) (f z) (f w) := fun _ _ _ _ => rfl
  have hrleaf : ∀ a b z w, renameProgram f (Q6LifetimeResearch.compareLeaf fwd a b z w) =
      Q6LifetimeResearch.compareLeaf fwd (f a) (f b) (f z) (f w) := by
    intro a b z w; cases fwd <;> simp [Q6LifetimeResearch.compareLeaf, renameProgram, renameInstr, renameCorrection, majority, eraseCarry]
  have hrlay : ∀ (xs ys zs : List Wire) (z : Wire),
      (compareLayers fwd xs ys zs z target).map (fun l =>
        { host := f l.host, up := renameProgram f l.up, erase := renameProgram f l.erase, finish := renameProgram f l.finish : StairLoan.CarryLayer }) =
      compareLayers fwd (xs.map f) (ys.map f) (zs.map f) (f z) (f target) := by
    intro xs; induction xs with
    | nil => intro ys zs z; simp [compareLayers]
    | cons a as ih =>
      intro ys zs z; cases as with
      | nil => cases ys <;> simp [compareLayers]
      | cons a' as' => cases ys with
        | nil => simp [compareLayers]
        | cons b bs => cases bs with
          | nil => simp [compareLayers]
          | cons b' bs' => cases zs with
            | nil => simp [compareLayers]
            | cons c cs' =>
              simp only [compareLayers, List.map_cons]
              refine congrArg₂ List.cons ?_ (ih (b' :: bs') cs' c)
              cases fwd <;> simp only [hrmaj, hrer] <;> rfl
  have hrtop : ∀ (xs ys zs : List Wire) (z : Wire),
      renameProgram f (compareTop fwd xs ys zs z target) =
      compareTop fwd (xs.map f) (ys.map f) (zs.map f) (f z) (f target) := by
    intro xs; induction xs with
    | nil => intro ys zs z; cases ys <;> simp [compareTop, renameProgram]
    | cons a as ih =>
      intro ys zs z; cases ys with
      | nil => simp [compareTop, renameProgram]
      | cons b bs => cases as with
        | nil => cases bs with
          | nil => simpa [compareTop] using hrleaf a b z target
          | cons _ _ => simp [compareTop, renameProgram]
        | cons a' as' => cases bs with
          | nil => simp [compareTop, renameProgram]
          | cons b' bs' => cases zs with
            | nil => simp [compareTop, renameProgram]
            | cons c cs' => exact ih (b' :: bs') cs' c
  have hmap : ∀ (P Q : Program), renameProgram f (P ++ Q) = renameProgram f P ++ renameProgram f Q :=
    fun _ _ => List.map_append
  have hrups : ∀ ls : List StairLoan.CarryLayer,
      renameProgram f (StairLoan.emitUps ls) =
        StairLoan.emitUps (ls.map (fun l => { host := f l.host, up := renameProgram f l.up, erase := renameProgram f l.erase, finish := renameProgram f l.finish })) := by
    intro ls; induction ls with
    | nil => rfl
    | cons l ls ih => simp only [StairLoan.emitUps, List.map_cons, hmap, ih]
  have hrer' : ∀ ls : List StairLoan.CarryLayer,
      renameProgram f (StairLoan.emitErases ls) =
        StairLoan.emitErases (ls.map (fun l => { host := f l.host, up := renameProgram f l.up, erase := renameProgram f l.erase, finish := renameProgram f l.finish })) := by
    intro ls; induction ls with
    | nil => rfl
    | cons l ls ih => simp only [StairLoan.emitErases, List.map_cons, hmap, ih]
  have hrdns : ∀ ls : List StairLoan.CarryLayer,
      renameProgram f (StairLoan.emitDowns ls) =
        StairLoan.emitDowns (ls.map (fun l => { host := f l.host, up := renameProgram f l.up, erase := renameProgram f l.erase, finish := renameProgram f l.finish })) := by
    intro ls; induction ls with
    | nil => rfl
    | cons l ls ih => simp only [StairLoan.emitDowns, StairLoan.CarryLayer.down, List.map_cons, hmap, ih]
  have hrhosts : ∀ ls : List StairLoan.CarryLayer,
      (StairLoan.layerHosts ls).map f =
        StairLoan.layerHosts (ls.map (fun l => { host := f l.host, up := renameProgram f l.up, erase := renameProgram f l.erase, finish := renameProgram f l.finish })) := by
    intro ls; induction ls with
    | nil => rfl
    | cons l ls ih => simp [StairLoan.layerHosts, ih]
  have hrrbm : ∀ (rs hs : List Wire) (P : Program),
      renameProgram f (StairLoan.rebindMany rs hs P) =
        StairLoan.rebindMany (rs.map f) (hs.map f) (renameProgram f P) := by
    intro rs; induction rs with
    | nil => intro hs P; rfl
    | cons r rs ih =>
      intro hs P; cases hs with
      | nil => rfl
      | cons h hs =>
        simp only [StairLoan.rebindMany, List.map_cons, renameProgram_comp]
        rw [← ih hs P, renameProgram_comp]
        congr 1; funext x
        change f (Equiv.swap r h x) = Equiv.swap (f r) (f h) (f x)
        by_cases hxr : x = r
        · subst hxr; simp
        · by_cases hxh : x = h
          · subst hxh; simp
          · rw [Equiv.swap_apply_of_ne_of_ne hxr hxh,
                Equiv.swap_apply_of_ne_of_ne (f.injective.ne hxr) (f.injective.ne hxh)]
  unfold compareLoan StairLoan.emitLoan StairLoan.emitSweep
  rw [hmap, hmap, hmap, hmap, hrups, hrer', hrrbm, hmap, hmap, hrups, hrtop, hrdns, hrups, hrdns]
  simp only [hrhosts, List.map_take, List.map_drop, hrlay, hcs, hcin, htgt, hroles]

attribute [local irreducible] run StairLoan.compareBlockLoan compareBlockLoan

/-- Loan drop for `compareBlockLoan d fwd L760` (both directions, via `swapRY` + `compareBlockLoan760_run_eq`). -/

theorem compareBlockLoan_760_run_eq (d : Nat) (hd : d ≤ 68) (fwd : Bool) (s : State) (m n : List Bool)
    (oneZero : s.basis L760.one = false)
    (carryZero : ∀ q ∈ L760.carry, s.basis q = false)
    (lowerZero : s.basis L760.lower = false)
    (flag : fwd = true → s.basis L760.parity = decide (regValue L760.r s.basis < regValue L760.y s.basis)) :
    run (compareBlockLoan d fwd L760) m s = run (compareBlockLoan 0 fwd L760) n s := by
  have hmap_r : L760.r.map swapRY = L760.y := by decide +kernel
  have hmap_y : L760.y.map swapRY = L760.r := by decide +kernel
  have hmap_r1 : (L760.r.drop 1).map swapRY = L760.y.drop 1 := by decide +kernel
  have hmap_y1 : (L760.y.drop 1).map swapRY = L760.r.drop 1 := by decide +kernel
  have hmap_cs : (((Q6Structural.q6Carry L760).take 255).drop 1).map swapRY = ((Q6Structural.q6Carry L760).take 255).drop 1 := by decide +kernel
  have hmap_roles : retiredRoles.map swapRY = retiredRoles := by decide +kernel
  have hfix : swapRY L760.one = L760.one ∧ swapRY L760.parity = L760.parity ∧ swapRY L760.lower = L760.lower ∧
      swapRY (base 760) = base 760 ∧
      swapRY (((Q6Structural.q6Carry L760).take 255).getD 0 0) = ((Q6Structural.q6Carry L760).take 255).getD 0 0 ∧
      swapRY (L760.y.getD 0 0) = L760.r.getD 0 0 ∧ swapRY (L760.r.getD 0 0) = L760.y.getD 0 0 := by decide +kernel
  have hren_blk : ∀ k, renameProgram swapRY (StairLoan.compareBlockLoan k fwd L760) = compareBlockLoan k fwd L760 := by
    intro k
    delta StairLoan.compareBlockLoan compareBlockLoan Q6LifetimeResearch.move
    have hmap : ∀ (P Q : Program), renameProgram swapRY (P ++ Q) = renameProgram swapRY P ++ renameProgram swapRY Q :=
      fun _ _ => List.map_append
    repeat rw [hmap]
    have hnr : renameProgram swapRY (notRegister (L760.one :: L760.r)) = notRegister (L760.one :: L760.y) := by
      simp only [notRegister, renameProgram, List.map_cons, renameInstr, hfix.1, ← hmap_r, List.map_map, Function.comp_def]
    have hmv : renameProgram swapRY (renameProgram (Equiv.swap (base 760) L760.one)
        (compareLoan k retiredRoles fwd (L760.y.drop 1) (L760.r.drop 1)
          (((Q6Structural.q6Carry L760).take 255).drop 1) (((Q6Structural.q6Carry L760).take 255).getD 0 0) L760.parity)) =
        renameProgram (Equiv.swap (base 760) L760.one)
          (compareLoan k retiredRoles fwd (L760.r.drop 1) (L760.y.drop 1)
            (((Q6Structural.q6Carry L760).take 255).drop 1) (((Q6Structural.q6Carry L760).take 255).getD 0 0) L760.parity) := by
      have hcomm : (swapRY ∘ Equiv.swap (base 760) L760.one : Wire → Wire) = Equiv.swap (base 760) L760.one ∘ swapRY := by
        funext x; simp only [Function.comp_def]
        by_cases hx1 : x = base 760
        · subst hx1; simp [hfix.2.2.2.1, hfix.1]
        · by_cases hx2 : x = L760.one
          · subst hx2; simp [hfix.2.2.2.1, hfix.1]
          · rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2,
                Equiv.swap_apply_of_ne_of_ne (by intro e; exact hx1 (swapRY.injective (e.trans hfix.2.2.2.1.symm)))
                  (by intro e; exact hx2 (swapRY.injective (e.trans hfix.1.symm)))]
      rw [renameProgram_comp, hcomm, ← renameProgram_comp,
          rename_compareLoan_eq swapRY k retiredRoles fwd (L760.y.drop 1) (L760.r.drop 1)
            (((Q6Structural.q6Carry L760).take 255).drop 1) (((Q6Structural.q6Carry L760).take 255).getD 0 0) L760.parity
            hmap_roles hmap_cs hfix.2.2.2.2.1 hfix.2.1, hmap_y1, hmap_r1]
    rw [hnr, hmv]
    simp only [majority, eraseCarry, renameProgram, List.map_cons, List.map_nil, renameInstr, renameCorrection, hfix.1, hfix.2.2.2.2.1, hfix.2.2.2.2.2.1, hfix.2.2.2.2.2.2]
  rw [← hren_blk d, ← hren_blk 0]
  have h1 := run_rename swapRY swapRY.injective (StairLoan.compareBlockLoan d fwd L760) m s
  have h0 := run_rename swapRY swapRY.injective (StairLoan.compareBlockLoan 0 fwd L760) n s
  have hcarry_fix : ∀ q ∈ L760.carry, swapRY q = q := by
    have hchk : L760.carry.all (fun q => decide (swapRY q = q)) = true := by decide +kernel
    exact fun q hq => of_decide_eq_true (List.all_eq_true.mp hchk q hq)
  have hrv : ∀ (xs : List Wire) (b : BasisState), regValue xs (fun q => b (swapRY q)) = regValue (xs.map swapRY) b := by
    intro xs; induction xs with
    | nil => intro _; rfl
    | cons x xs ih => intro b; change (if b (swapRY x) then 1 else 0) + 2 * regValue xs (fun q => b (swapRY q)) = (if b (swapRY x) then 1 else 0) + 2 * regValue (xs.map swapRY) b; rw [ih]
  have hp_one : (pullState swapRY s).basis L760.one = false := by simp [pullState, hfix.1, oneZero]
  have hp_car : ∀ q ∈ L760.carry, (pullState swapRY s).basis q = false :=
    fun q hq => by simp [pullState, hcarry_fix q hq, carryZero q hq]
  have hp_low : (pullState swapRY s).basis L760.lower = false := by simp [pullState, hfix.2.2.1, lowerZero]
  have hp_flag : fwd = true → (pullState swapRY s).basis L760.parity =
      decide (regValue L760.y (pullState swapRY s).basis < regValue L760.r (pullState swapRY s).basis) := by
    intro hf; simp only [pullState, hfix.2.1, hrv, hmap_y, hmap_r]; exact flag hf
  have hmid := (StairLoanForwardB.compareBlockLoan760_run_eq d hd fwd (pullState swapRY s) m n hp_one hp_car hp_low hp_flag).trans
    (StairLoanForwardB.compareBlockLoan760_run_eq 0 (by decide) fwd (pullState swapRY s) n n hp_one hp_car hp_low hp_flag).symm
  rw [hmid] at h1
  have hpull_eq := h1.trans h0.symm
  apply State.extensionality
  · exact congrArg (fun st => st.phase) hpull_eq
  · funext q
    have hq := congrFun (congrArg State.basis hpull_eq) (swapRY q)
    simp only [pullState, swapRY_invol] at hq
    exact hq

end

end ECDSAAdd.Entrant.OddFullPass.P1LifeLoan
end

end
-- ==== end OddFullPass ====
