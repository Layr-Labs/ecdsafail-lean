import ECDSAAdd.Submission.Entrant.MainP1

/-!
# Odd-word interfaces around the square (converters `canon760OddLoan` / `center760OddLoan` removed)

The division kernel used to end with `canon760OddLoan` (odd word -> canonical value) and the
multiplication kernel used to start with `center760OddLoan` (canonical value -> odd word).  With both
deleted, the slope `λ` stays in odd-word form `oddWord (λ / 2)` on the numerator register from the end
of the division to the start of the multiplication, and the square reads it in that form.

* `EntryCorrectOddNC`  : the division kernel's contract (output in odd-word form).
* `SquareOddNC` : the square variant's contract (input in odd-word form, restored).
* `ExitMatchesOddNC`   : the multiplication kernel's contract (input in odd-word form).
* `PointDialogValuesOdd` : `PointDialogValues` with `y` in odd-word form (outer chain).
-/

section

namespace ECDSAAdd.Entrant.SqOddContract
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open MappedCompressed.LaneA FrontierEntry1591Callers StairSemanticFinal

set_option linter.unusedVariables false in
/-- Division kernel without `canon760OddLoan`: as `OddOuterBridge.EntryCorrectOdd`, but the
    numerator register ends holding `oddWord ((Y / x) / 2)` instead of `(Y / x).val`; every other
    wire (work wires included) ends equal to the canonical source `s`. -/
def EntryCorrectOddNC (K : Program) : Prop :=
  ∀ (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (phase : t.phase = s.phase)
    (same : ∀ q, q ∉ wireBlock base 2056 256 → t.basis q = s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis = EntryFuseOdd.oddWord (Y / 2)),
    let out := run K m t
    out.phase = s.phase ∧
      regValue (wireBlock base 2056 256) out.basis =
        EntryFuseOdd.oddWord (skywalkArithmeticResult true x Y / 2) ∧
      ∀ q, q ∉ wireBlock base 2056 256 → out.basis q = s.basis q

set_option linter.unusedVariables false in
/-- Multiplication kernel without `center760OddLoan`: as `OddOuterBridge.ExitMatchesOdd`, but it
    starts from `t`, which equals the canonical source `s` except on the numerator register, where
    it holds `oddWord (Y / 2)`.  The reference stays the stock `kernelX k` run from `s`. -/
def ExitMatchesOddNC (K : Program) (k : Nat) : Prop :=
  ∀ (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s t : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (phase : t.phase = s.phase)
    (same : ∀ q, q ∉ wireBlock base 2056 256 → t.basis q = s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis = EntryFuseOdd.oddWord (Y / 2)),
    let out := run K m t
    let ref := ParityEven.put (run (ParityXExitInverse23Kernel.kernelX k) m s)
                 ParityXExitInverse23Kernel.pkP (s.basis (base 2400) && decide (k < x))
    out.phase = ref.phase ∧
      regValue (wireBlock base 2056 256) out.basis = EntryFuseOdd.oddWord (Y * (x : Fp) / 2) ∧
      ∀ q, q ∉ wireBlock base 2056 256 → out.basis q = ref.basis q

/-- Square variant reading `λ` as `oddWord (λ / 2)` on `point.y`: from `t`, which equals the stock
    state `s` (values `X, Y = λ, G`) except on `point.y`, it ends equal to the stock square
    `Stair44Square.program k` run from `s` on every wire outside `point.y`, and `point.y` still holds
    `oddWord (Y / 2)`. -/
def SquareOddNC (P : Program) (k : Fp) : Prop :=
  ∀ (X Y : Fp) (G : Bool) (origin : BasisState) (s t : State) (m : List Bool),
    PointDialogValues Baselines.layout X Y G origin s.basis →
    t.phase = s.phase →
    (∀ q, q ∉ Baselines.layout.point.y → t.basis q = s.basis q) →
    regValue Baselines.layout.point.y t.basis = EntryFuseOdd.oddWord (Y / 2) →
    (run P m t).phase = (run (Stair44Square.program k) m s).phase ∧
      regValue Baselines.layout.point.y (run P m t).basis = EntryFuseOdd.oddWord (Y / 2) ∧
      ∀ q, q ∉ Baselines.layout.point.y →
        (run P m t).basis q = (run (Stair44Square.program k) m s).basis q

/-- `PointDialogValues` with the `y` coordinate held as `oddWord (Y / 2)`. -/
structure PointDialogValuesOdd (L : ControlledPointLayout) (X Y : Fp) (G : Bool)
    (origin s : BasisState) : Prop where
  x : regValue L.point.x s = X.val
  y : regValue L.point.y s = EntryFuseOdd.oddWord (Y / 2)
  generic : s L.core.generic = G
  clean : regValue L.dialogPool s = 0
  rest : ∀ q, q ∉ L.point.x ++ L.point.y → s q = origin q

end ECDSAAdd.Entrant.SqOddContract

end

section

namespace ECDSAAdd.Entrant.SqOddContract
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
  StairSquareHolesCore StairEntryRehost
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def e1BY (q : Nat) : Nat :=
  StairPlaceFast.swB 1558 736 (StairPlaceFast.swB 1557 738 (StairPlaceFast.swB 1042 737
    (StairPlaceFast.swB 1813 527 (StairPlaceFast.swB 738 740 (StairPlaceFast.swB 737 739
      (StairPlaceFast.swB 527 741 q))))))

private theorem e1Y_eq (q : Wire) : E1QubitPlacement.sig (E1QubitPlacement.rho q) = e1BY q := by
  unfold E1QubitPlacement.sig E1QubitPlacement.phaseHost E1QubitPlacement.nativeSwap
    E1QubitPlacement.rho e1BY
  simp only [Equiv.trans_apply, StairPlaceFast.swap_eq_sw, StairPlaceFast.swB_eq]
  rfl

private def pmBY (q : Nat) : Nat :=
  StairPlaceFast.pwB (StairPlaceFast.swB 785 1813 (e1BY q) - 16)

private theorem pmapRY_fast (q : Wire) : pmapR Baselines.layout q = pmBY q := by
  show wireFn2 Baselines.layout (E1QubitPlacement.sig (E1QubitPlacement.rho q)) = _
  rw [StairPlaceFast.wireFn2_eqB, e1Y_eq]
  rfl

/-- Outside `Baselines.layout.point.y = [258, 514)`. -/
def offY (q : Nat) : Bool := Nat.blt q 258 || Nat.ble 514 q

private def fastPrefixY (x : Wire) := StairPlaceFast.swB 4840 4627 (pmBY x)
private def fastSuffixY (x : Wire) := StairPlaceFast.swB 4835 4373 (StairPlaceFast.swB 4836 4374
  (StairPlaceFast.swB 4837 4375 (StairPlaceFast.swB 4838 4376 (StairPlaceFast.swB 4839 4377 (pmBY x)))))
private theorem prefixY_eq (x : Wire) : compareWire x = fastPrefixY x := by
  have eq : StairSquareEntryR.entryPairs = [(4840,4627)] := by decide +kernel
  simp only [compareWire,eq,permutation,Equiv.trans_apply,Equiv.refl_apply,fastPrefixY,
    StairPlaceFast.swB_eq,StairPlaceFast.swap_eq_sw,pmapRY_fast]
private theorem suffixY_eq (x : Wire) : suffixWire x = fastSuffixY x := by
  simp only [suffixWire,moves_eq,physicalMoves,permutation,Equiv.trans_apply,Equiv.refl_apply,fastSuffixY,
    StairPlaceFast.swB_eq,StairPlaceFast.swap_eq_sw,pmapRY_fast]
private theorem prefix_offY : (compareLabels base (base 2400)).all
    (fun x => offY (fastPrefixY x)) = true := by decide +kernel
private theorem suffix_offY : (E1Reflected.Square31.mS5 base (base 2400)).all
    (fun x => offY (fastSuffixY x)) = true := by decide +kernel

theorem offY_sound (q : Wire) (h : offY q = true) : q ∉ Baselines.layout.point.y := by
  have hy : Baselines.layout.point.y = List.range' 258 256 := by decide +kernel
  rw [hy, List.mem_range']
  simp only [offY, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  omega

/-- The square's routed tail never touches `point.y` (the `hTy` premise of the square simulation). -/
theorem routed_avoids_y (k : Fp) : ∀ q ∈ wires (StairEntryRehost.routed k), q ∉ Baselines.layout.point.y := by
  intro q hq
  apply offY_sound
  have h := List.mem_toFinset.mp (uses_labels k hq)
  simp only [labels,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with ((⟨x,hx,rfl⟩|⟨x,hx,rfl⟩)|rfl|rfl)
  · rw [prefixY_eq]; exact List.all_eq_true.mp prefix_offY x hx
  · rw [suffixY_eq]; exact List.all_eq_true.mp suffix_offY x hx
  · decide +kernel
  · decide +kernel

end ECDSAAdd.Entrant.SqOddContract

end

section

namespace ECDSAAdd.Entrant.SqOddContract
open ECDSAAdd Arithmetic Secp256k1

/-- The square of the folded odd word: with `w = oddWord (Y / 2)` (two's complement `R`,
    `2R + 1 = Y`), `M = (w ≥ 2^255 ? 2^256 - 1 - w : w)` and `N = 1 + 2M = |2R + 1|`, so
    `N^2 = Y^2 (mod p)`. -/
theorem oddWord_square (Y : Fp) :
    (1 + 2 * (if 2 ^ 255 ≤ EntryFuseOdd.oddWord (Y / 2) then 2 ^ 256 - 1 - EntryFuseOdd.oddWord (Y / 2)
      else EntryFuseOdd.oddWord (Y / 2))) ^ 2 % p = Y.val ^ 2 % p := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hc := BalancedField.constants
  have hb := BalancedField.centerFp_bounds (Y / 2)
  have hcast := BalancedField.centerFp_cast (Y / 2)
  unfold BalancedField.Centered at hb
  generalize hz : BalancedField.centerFp (Y / 2) = z at hb hcast
  have hw : (EntryFuseOdd.oddWord (Y / 2) : Int) =
      (if z < 0 then z + BalancedField.q else z - BalancedField.q - 1) % ((2 ^ 256 : Nat) : Int) := by
    unfold EntryFuseOdd.oddWord EntryFuseOdd.oddRep BalancedField.encodeWord
    rw [hz, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  generalize EntryFuseOdd.oddWord (Y / 2) = w at hw ⊢
  have h255 : ((2 ^ 255 : Nat) : Int) = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    norm_num
  have h256 : ((2 ^ 256 : Nat) : Int) = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num
  rw [h255] at hc
  rw [h256] at hw
  -- the integer value of `N`
  have hN : ((1 + 2 * (if 2 ^ 255 ≤ w then 2 ^ 256 - 1 - w else w) : Nat) : Int) =
      (if z < 0 then 2 * z + (p : Int) else (p : Int) - 2 * z) := by
    have e255 : (2 : Nat) ^ 255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
      norm_num
    have e256 : (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      norm_num
    rw [e255, e256]
    by_cases hneg : z < 0
    · rw [if_pos hneg] at hw ⊢
      have hw' : (w : Int) = z + BalancedField.q := by omega
      have hlt : ¬ (57896044618658097711785492504343953926634992332820282019728792003956564819968 ≤ w) := by
        omega
      rw [if_neg hlt]
      push_cast
      omega
    · rw [if_neg hneg] at hw ⊢
      have hw' : (w : Int) = z - BalancedField.q - 1 + 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
        omega
      have hge : 57896044618658097711785492504343953926634992332820282019728792003956564819968 ≤ w := by
        omega
      rw [if_pos hge]
      have hsub : ((115792089237316195423570985008687907853269984665640564039457584007913129639936 - 1 - w : Nat) : Int) =
          115792089237316195423570985008687907853269984665640564039457584007913129639936 - 1 - (w : Int) := by
        have : w ≤ 115792089237316195423570985008687907853269984665640564039457584007913129639936 - 1 := by omega
        omega
      push_cast [hsub]
      omega
  -- `(N : Fp) = ± Y`
  generalize hM : (1 + 2 * (if 2 ^ 255 ≤ w then 2 ^ 256 - 1 - w else w)) = N at hN ⊢
  have hp0 : ((p : Nat) : Fp) = 0 := ZMod.natCast_self p
  have hY : (2 : Fp) * (z : Fp) = Y := by
    rw [hcast, ← mul_div_assoc, mul_div_cancel_left₀ _ (by decide : (2 : Fp) ≠ 0)]
  have hNF : (N : Fp) = Y ∨ (N : Fp) = -Y := by
    have h1 : ((N : Int) : Fp) = (N : Fp) := by simp
    rw [← h1, hN]
    split_ifs
    · left; push_cast; rw [hp0, add_zero, hY]
    · right; push_cast; rw [hp0, zero_sub, hY]
  rw [← ZMod.val_natCast (n := p) (N ^ 2), ← ZMod.val_natCast (n := p) (Y.val ^ 2)]
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val]
  rcases hNF with h | h <;> rw [h]
  ring

end ECDSAAdd.Entrant.SqOddContract

end
