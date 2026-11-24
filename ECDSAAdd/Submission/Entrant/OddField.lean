import ECDSAAdd.Submission.Entrant.Prelude
import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Framework.WireRenameEquivalence
import ECDSAAdd.Framework.RunAppendAgreement
import ECDSAAdd.Submission.Entrant.BOptimizations
import ECDSAAdd.Submission.Entrant.StairSideA
import ECDSAAdd.Submission.Entrant.Window
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.Stair44Stock
import Mathlib.Tactic
import ECDSAAdd.Framework.Syntax
import ECDSAAdd.Framework.Semantics

/-! # Odd-word field replay (port of dadon 078d2948 onto the release tree) -/

-- file-level opens in effect at this point of 078d LeaveReductions
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic MappedCompressed
open StairRestSupport ArchiveFieldScratch StairArchiveRelease

-- ==== begin OddEntryExit ====
section

/-!
# Odd-word fused Y entry and exit

Direct canonical-to-`oddWord` fused controlled-add-and-halve (`entryYAllOdd`)
and its exact `oddWord`-to-canonical inverse (`exitYAllOdd`) on the existing
`MeasuredCanonicalModLayout` / `ControlledPointLayout` wires.

For `z = (Y + g * k) mod p` and `a_odd = (complement - 1) / 2 = 2^31 + 488`:
- Sign bit `s = decide (z % 2 = 0) = !(Y % 2 ^^ (g && k % 2 = 1) ^^ wrap)`.
- Low 255-bit word `u = z / 2 + (if s then a_odd else 0) < 2^255` never overflows
  and satisfies `u = (Y / 2 + q_sel) mod 2^255` using the same 5-wire XOR table
  structure (`0 T`) as `EntryFuse`.
- Wrap recovery `wrap ↔ u < t` has threshold `t = 0` (`g = false`),
  `t = k / 2` (`g = true, s = false`), `t = (k + 1) / 2 + a_odd` (`g = true, s = true`),
  satisfying `t < 2^255` unconditionally so no high-bit threshold correction is needed.
- Both `k` parities achieve `765 T / 767 M` (`entryYAllOdd`) and `765 T / 766 M`
  (`exitYAllOdd`).
-/

section
namespace ECDSAAdd.Entrant.EntryFuseOdd
open Arithmetic BalancedField Secp256k1 EntryFuseArithmetic EntryFuse

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

-- ============================================================================
-- Section 1: Odd-word representation (matches `P1Life.oddWord` by `rfl`)
-- ============================================================================

def oddRep (x : Fp) : Int :=
  let z := centerFp x
  if z < 0 then z + q else z - q - 1

def oddWord (x : Fp) : Nat := encodeWord 256 (oddRep x)

def offsetOdd : Nat := (complement - 1) / 2

private theorem p_eq :
    p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [p]

private theorem q_eq :
    q = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by
  have hc := constants
  have hp := p_eq
  omega

private theorem pow255_eq :
    (2 : Nat) ^ 255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
  norm_num

private theorem pow256_eq :
    (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  norm_num

private theorem offsetOdd_eq : offsetOdd = 2147484136 := by
  norm_num [offsetOdd, complement]

theorem low_lt_odd (z : Nat) (hz : z < prime) :
    z / 2 + (if z % 2 = 0 then offsetOdd else 0) < halfModulus := by
  norm_num [prime, modulus, complement, halfModulus, offsetOdd] at *
  split_ifs <;> omega

theorem encoding_oddWord (z : Nat) (hz : z < prime) :
    z / 2 + (if z % 2 = 0 then offsetOdd else 0) + (if z % 2 = 0 then 2 ^ 255 else 0) =
      oddWord (((z : Nat) : Fp) / 2) := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let x : Fp := (z : Nat)
  have hzp : z < p := by rwa [← prime_eq_secp]
  have hxv : x.val = z := ZMod.val_natCast_of_lt hzp
  have hhalf := HalfConvert.half_val x
  rw [hxv] at hhalf
  have hp := p_eq
  have hq := q_eq
  have h255 := pow255_eq
  have h256 := pow256_eq
  have hao := offsetOdd_eq
  unfold oddWord oddRep
  have hcenter : centerFp (x / 2) =
      if z % 2 = 0 then ((z / 2 : Nat) : Int) else ((z / 2 : Nat) : Int) - q := by
    unfold centerFp
    rw [hhalf]
    by_cases he : z % 2 = 0
    · rw [if_pos he, if_pos he]
      have hle : ((z / 2 : Nat) : Int) ≤ q := by omega
      simp only [hle, if_true]
    · rw [if_neg he, if_neg he]
      have hgt : ¬ (((z + p) / 2 : Nat) : Int) ≤ q := by omega
      simp only [hgt, if_false]
      omega
  rw [hcenter]
  by_cases he : z % 2 = 0
  · rw [if_pos he, if_pos he, if_pos he]
    have hnn : ¬ (((z / 2 : Nat) : Int) < 0) := by omega
    rw [if_neg hnn]
    have enc := BalancedFold.encode_shift 256 (((z / 2 : Nat) : Int) - q - 1) (by omega)
    have hneg : ((z / 2 : Nat) : Int) - q - 1 < 0 := by omega
    rw [if_pos hneg] at enc
    omega
  · rw [if_neg he, if_neg he, if_neg he]
    have hlt : ((z / 2 : Nat) : Int) - q < 0 := by omega
    rw [if_pos hlt]
    have hsimp : ((z / 2 : Nat) : Int) - q + q = ((z / 2 : Nat) : Int) := by omega
    rw [hsimp]
    have enc := BalancedFold.encode_shift 256 ((z / 2 : Nat) : Int) (by omega)
    have hnn : ¬ (((z / 2 : Nat) : Int) < 0) := by omega
    rw [if_neg hnn] at enc
    omega

-- ============================================================================
-- Section 2: Odd-word fused arithmetic identities
-- ============================================================================

theorem threshold_bounds_odd (k : Nat) (hk : k < prime) :
    k / 2 < halfModulus ∧ (k + 1) / 2 + offsetOdd < halfModulus := by
  norm_num [prime, modulus, complement, halfModulus, offsetOdd] at *
  omega

theorem output_sign_odd_controlled (y k : Nat) (g : Bool) (hy : y < prime) (hk : k < prime) :
    decide (((y + (if g then k else 0)) % prime) % 2 = 0) =
      !(decide (y % 2 = 1) ^^ (g && decide (k % 2 = 1)) ^^
        decide (prime ≤ y + (if g then k else 0))) := by
  have h := output_sign_controlled y k g hy hk
  rw [← h]
  have hm : ((y + (if g then k else 0)) % prime) % 2 < 2 := Nat.mod_lt _ (by decide)
  interval_cases ((y + (if g then k else 0)) % prime) % 2 <;> decide

theorem selected_addend_odd (y k : Nat) (hy : y < prime) (hk : k < prime) :
    let z := (y + k) % prime
    let u := z / 2 + (if z % 2 = 0 then offsetOdd else 0)
    let b := k / 2
    let d := (k + 1) / 2 + offsetOdd
    let e := b + complement
    (if prime ≤ y + k then u + halfModulus else u) =
      y / 2 + (if prime ≤ y + k then (if z % 2 = 0 then e else d)
        else (if z % 2 = 0 then d else b)) := by
  norm_num [prime, modulus, complement, halfModulus, offsetOdd] at *
  by_cases hd : 115792089237316195423570985008687907853269984665640564039457584007908834671663 ≤ y + k
  · have hm : (y + k) % 115792089237316195423570985008687907853269984665640564039457584007908834671663 =
        y + k - 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
      rw [Nat.mod_eq_sub_mod hd, Nat.mod_eq_of_lt (by omega)]
    rw [hm]
    simp only [if_pos hd]
    split <;> omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [if_neg hd]
    split <;> omega

def selectedOdd (g wrap s : Bool) (k : Nat) : Nat :=
  let a := offsetOdd
  let b := k / 2
  let d := (k + 1) / 2 + a
  let e := b + complement
  if g then (if wrap then (if s then e else d) else (if s then d else b))
  else (if s then a else 0)

theorem selectedOdd_math (y k : Nat) (g : Bool) (hy : y < prime) (hk : k < prime) :
    let z := (y + (if g then k else 0)) % prime
    (selectedOdd g (decide (prime ≤ y + (if g then k else 0)))
      (decide (z % 2 = 0)) k % 2 ^ 255 + y / 2) % 2 ^ 255 =
      z / 2 + (if z % 2 = 0 then offsetOdd else 0) := by
  dsimp only
  rw [add_low_mod]
  cases g
  · simp only [Bool.false_eq_true, if_false, Nat.add_zero, Nat.mod_eq_of_lt hy, selectedOdd]
    have hu := low_lt_odd y hy
    have hhm : halfModulus = 2 ^ 255 := rfl
    rw [hhm] at hu
    by_cases he : y % 2 = 0
    · simp only [he, decide_true, if_true] at hu ⊢
      exact Nat.mod_eq_of_lt hu
    · simp only [he, decide_false, Bool.false_eq_true, if_false, Nat.add_zero] at hu ⊢
      exact Nat.mod_eq_of_lt hu
  · simp only [if_true, selectedOdd]
    have h := selected_addend_odd y k hy hk
    have hz : (y + k) % prime < prime := Nat.mod_lt _ (by norm_num [prime, modulus, complement])
    have hu := low_lt_odd ((y + k) % prime) hz
    have hhm : halfModulus = 2 ^ 255 := rfl
    rw [hhm] at h hu
    by_cases hd : prime ≤ y + k
    · simp only [hd, decide_true, if_true] at h ⊢
      by_cases he : ((y + k) % prime) % 2 = 0
      · simp only [he, decide_true, if_true] at h hu ⊢
        rw [← h, Nat.add_mod_right, Nat.mod_eq_of_lt hu]
      · simp only [he, decide_false, Bool.false_eq_true, if_false] at h hu ⊢
        rw [← h, Nat.add_mod_right, Nat.mod_eq_of_lt hu]
    · simp only [hd, decide_false, Bool.false_eq_true, if_false] at h ⊢
      by_cases he : ((y + k) % prime) % 2 = 0
      · simp only [he, decide_true, if_true] at h hu ⊢
        rw [← h, Nat.mod_eq_of_lt hu]
      · simp only [he, decide_false, Bool.false_eq_true, if_false] at h hu ⊢
        rw [← h, Nat.mod_eq_of_lt hu]

theorem wrap_threshold_odd (y k : Nat) (hy : y < prime) (hk : k < prime) :
    let z := (y + k) % prime
    let u := z / 2 + (if z % 2 = 0 then offsetOdd else 0)
    (prime ≤ y + k) ↔ u < (if z % 2 = 0 then (k + 1) / 2 + offsetOdd else k / 2) := by
  norm_num [prime, modulus, complement, offsetOdd] at *
  by_cases hd : 115792089237316195423570985008687907853269984665640564039457584007908834671663 ≤ y + k
  · have hm : (y + k) % 115792089237316195423570985008687907853269984665640564039457584007908834671663 =
        y + k - 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
      rw [Nat.mod_eq_sub_mod hd, Nat.mod_eq_of_lt (by omega)]
    rw [hm]
    split <;> omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    split <;> omega

theorem thresholdOdd_math (y k : Nat) (g : Bool) (hy : y < prime) (hk : k < prime) :
    let z := (y + (if g then k else 0)) % prime
    let u := z / 2 + (if z % 2 = 0 then offsetOdd else 0)
    let b := decide (z % 2 = 0)
    decide (prime ≤ y + (if g then k else 0)) =
      decide (u < (if g then (if b then (k + 1) / 2 + offsetOdd else k / 2) else 0) % 2 ^ 255) := by
  dsimp only
  have hb := threshold_bounds_odd k hk
  have hhm : halfModulus = 2 ^ 255 := rfl
  rw [hhm] at hb
  cases g
  · have hn : ¬ prime ≤ y := by omega
    simp only [Bool.false_eq_true, if_false, Nat.add_zero, hn, decide_false, Nat.zero_mod,
      Nat.not_lt_zero]
  · simp only [if_true]
    have hw := wrap_threshold_odd y k hy hk
    dsimp only at hw
    by_cases he : ((y + k) % prime) % 2 = 0
    · simp only [he, decide_true, if_true, Nat.mod_eq_of_lt hb.2] at hw ⊢
      exact decide_eq_decide.mpr hw
    · simp only [he, decide_false, Bool.false_eq_true, if_false, Nat.mod_eq_of_lt hb.1] at hw ⊢
      exact decide_eq_decide.mpr hw

-- ============================================================================
-- Section 3: Base odd-word entry circuit and semantic correctness
-- ============================================================================

def tableOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  let a := offsetOdd
  let b := k / 2
  let d := (k + 1) / 2 + a
  let e := b + complement
  maskedConstant (sign K) (lowSrc K) a ++
  maskedConstant g (lowSrc K) b ++
  maskedConstant (alpha K) (lowSrc K) (Nat.xor (Nat.xor a b) d) ++
  maskedConstant K.flag (lowSrc K) (Nat.xor b d) ++
  maskedConstant K.high (lowSrc K) (Nat.xor e b)

def untabledOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  let a := offsetOdd
  let b := k / 2
  let d := (k + 1) / 2 + a
  let e := b + complement
  maskedConstant K.high (lowSrc K) (Nat.xor e b) ++
  maskedConstant K.flag (lowSrc K) (Nat.xor b d) ++
  maskedConstant (alpha K) (lowSrc K) (Nat.xor (Nat.xor a b) d) ++
  maskedConstant g (lowSrc K) b ++
  maskedConstant (sign K) (lowSrc K) a

def thresholdOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  let b := k / 2
  let d := (k + 1) / 2 + offsetOdd
  maskedConstant g (lowSrc K) b ++ maskedConstant (alpha K) (lowSrc K) (Nat.xor b d)

def unthresholdOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  let b := k / 2
  let d := (k + 1) / 2 + offsetOdd
  maskedConstant (alpha K) (lowSrc K) (Nat.xor b d) ++ maskedConstant g (lowSrc K) b

def entryMasksOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : List (Wire × Nat) :=
  let a := offsetOdd
  let b := k / 2
  let d := (k + 1) / 2 + a
  let e := b + complement
  [(sign K, a), (g, b), (alpha K, Nat.xor (Nat.xor a b) d),
   (K.flag, Nat.xor b d), (K.high, Nat.xor e b)]

def thresholdMasksOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : List (Wire × Nat) :=
  let b := k / 2
  let d := (k + 1) / 2 + offsetOdd
  [(g, b), (alpha K, Nat.xor b d)]

theorem tableOdd_is_load (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) :
    tableOdd K g k = loadMasks (lowSrc K) (entryMasksOdd K g k) := by
  simp [tableOdd, entryMasksOdd, loadMasks, List.append_assoc]

theorem untabledOdd_is_load (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) :
    untabledOdd K g k = loadMasks (lowSrc K) (entryMasksOdd K g k).reverse := by
  simp [untabledOdd, entryMasksOdd, loadMasks, List.append_assoc]

theorem thresholdOdd_is_load (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) :
    thresholdOdd K g k = loadMasks (lowSrc K) (thresholdMasksOdd K g k) := by
  simp [thresholdOdd, thresholdMasksOdd, loadMasks, List.append_assoc]

theorem unthresholdOdd_is_load (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) :
    unthresholdOdd K g k = loadMasks (lowSrc K) (thresholdMasksOdd K g k).reverse := by
  simp [unthresholdOdd, thresholdMasksOdd, loadMasks, List.append_assoc]

theorem maskOdd_controls (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) :
    (∀ e ∈ entryMasksOdd K g k, e.1 ∈ controls K g) ∧
      (∀ e ∈ thresholdMasksOdd K g k, e.1 ∈ controls K g) := by
  constructor <;> intro e he
  · simp only [entryMasksOdd, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> simp [controls]
  · simp only [thresholdMasksOdd, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [controls]

theorem entryMasksOdd_value (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (s : State)
    (ha : s.basis (alpha K) = (s.basis g && s.basis (sign K)))
    (hb : s.basis K.high = (s.basis K.flag && s.basis (sign K)))
    (hw : s.basis K.flag = true → s.basis g = true) :
    masksValue (lowSrc K) s.basis (entryMasksOdd K g k) =
      selectedOdd (s.basis g) (s.basis K.flag) (s.basis (sign K)) k % 2 ^ (lowSrc K).length := by
  have h := EntryFuseArithmetic.masks offsetOdd (k / 2) ((k + 1) / 2 + offsetOdd) (k / 2 + complement)
    (s.basis g) (s.basis K.flag) (s.basis (sign K)) hw
  have hm := congrArg (fun v : Nat => v % 2 ^ (lowSrc K).length) h
  have hx (a b : Nat) : Nat.xor a b % 2 ^ (lowSrc K).length =
      (a % 2 ^ (lowSrc K).length) ^^^ (b % 2 ^ (lowSrc K).length) := Nat.xor_mod_two_pow
  cases hg : s.basis g <;> cases hd : s.basis K.flag <;> cases hs : s.basis (sign K) <;>
    simp_all [entryMasksOdd, masksValue, selectedOdd, hx, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem thresholdMasksOdd_value (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (s : State)
    (ha : s.basis (alpha K) = (s.basis g && s.basis (sign K))) :
    masksValue (lowSrc K) s.basis (thresholdMasksOdd K g k) =
      (if s.basis g then (if s.basis (sign K) then (k + 1) / 2 + offsetOdd else k / 2) else 0) %
        2 ^ (lowSrc K).length := by
  have hx (a b : Nat) : Nat.xor a b % 2 ^ (lowSrc K).length =
      (a % 2 ^ (lowSrc K).length) ^^^ (b % 2 ^ (lowSrc K).length) := Nat.xor_mod_two_pow
  cases hg : s.basis g <;> cases hs : s.basis (sign K) <;>
    simp_all [thresholdMasksOdd, masksValue, hx, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

def signStageOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  ExitFusionResearch.signStage K g k ++ [.X (sign K)]

def tableAddOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  tableOdd K g k ++ lowAdder K ++ untabledOdd K g k

def addClearBetaOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  tableAddOdd K g k ++ [.measureX K.high [] [.CZ K.flag (sign K)]]

def middleOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  makeFlags K g ++ addClearBetaOdd K g k

def clearWrapOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  thresholdOdd K g k ++
    eraseLtChain (lowOut K) (lowSrc K) (K.carry.take 254) K.cin K.flag ++
    unthresholdOdd K g k ++ [.measureX (alpha K) [] [.CZ g (sign K)]]

def entryMiddleOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  signStageOdd K g k ++ middleOdd K g k

def entryBodyOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  entryMiddleOdd K g k ++ clearWrapOdd K g k

def entryOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  entryCompare K g complement k ++ entryBodyOdd K g k

def recoverWrapOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  [.CCX g (sign K) (alpha K)] ++ thresholdOdd K g k ++
    Arithmetic.ExitFusionResearch.computeLtChain (lowOut K) (lowSrc K) (K.carry.take 254) K.cin K.flag ++
    unthresholdOdd K g k

def tableSubOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  tableOdd K g k ++
    mappedSub (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin ++
    untabledOdd K g k

def undoMiddleOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  [.CCX K.flag (sign K) K.high] ++ tableSubOdd K g k ++
    [.measureX K.high [] [.CZ K.flag (sign K)],
     .measureX (alpha K) [] [.CZ g (sign K)]]

def exitOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  recoverWrapOdd K g k ++ undoMiddleOdd K g k ++
    (signStageOdd K g k).reverse ++ ExitFusionResearch.eraseInputWrap K g complement k

-- ============================================================================
-- Section 4: Semantic correctness of base `entryOdd` and `exitOdd`
-- ============================================================================

attribute [local irreducible] run wires

private theorem run_three (A B C : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 : List Bool, run (A ++ B ++ C) m s = run C m3 (run B m2 (run A m1 s)) :=
  ⟨m.take (measurementCount A), (m.drop (measurementCount A)).take (measurementCount B),
    (m.drop (measurementCount A)).drop (measurementCount B), by simp only [List.append_assoc, run_append]⟩

private theorem run_four (A B C D : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 m4 : List Bool,
      run (A ++ B ++ C ++ D) m s = run D m4 (run C m3 (run B m2 (run A m1 s))) :=
  ⟨m.take (measurementCount A), (m.drop (measurementCount A)).take (measurementCount B),
    ((m.drop (measurementCount A)).drop (measurementCount B)).take (measurementCount C),
    ((m.drop (measurementCount A)).drop (measurementCount B)).drop (measurementCount C),
    by simp only [List.append_assoc, run_append]⟩

theorem tableOdd_load (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (lowSrc K).Nodup) (hc : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowSrc K)
    (s : State) (m : List Bool) :
    let u := run (tableOdd K g k) m s
    u.phase = s.phase ∧ (∀ q, q ∉ lowSrc K → u.basis q = s.basis q) ∧
      regValue (lowSrc K) u.basis = regValue (lowSrc K) s.basis ^^^
        masksValue (lowSrc K) s.basis (entryMasksOdd K g k) := by
  rw [tableOdd_is_load]
  exact loadMasks_correct _ hn _ hc s m

theorem tableOdd_unload (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (lowSrc K).Nodup) (hc : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowSrc K)
    (s : State) (m : List Bool) :
    let u := run (untabledOdd K g k) m s
    u.phase = s.phase ∧ (∀ q, q ∉ lowSrc K → u.basis q = s.basis q) ∧
      regValue (lowSrc K) u.basis = regValue (lowSrc K) s.basis ^^^
        masksValue (lowSrc K) s.basis (entryMasksOdd K g k).reverse := by
  rw [untabledOdd_is_load]
  exact loadMasks_correct _ hn _ (fun e he => hc e (by simpa using he)) s m

theorem thresholdOdd_load (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (lowSrc K).Nodup) (hc : ∀ e ∈ thresholdMasksOdd K g k, e.1 ∉ lowSrc K)
    (s : State) (m : List Bool) :
    let u := run (thresholdOdd K g k) m s
    u.phase = s.phase ∧ (∀ q, q ∉ lowSrc K → u.basis q = s.basis q) ∧
      regValue (lowSrc K) u.basis = regValue (lowSrc K) s.basis ^^^
        masksValue (lowSrc K) s.basis (thresholdMasksOdd K g k) := by
  rw [thresholdOdd_is_load]
  exact loadMasks_correct _ hn _ hc s m

theorem thresholdOdd_unload (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (lowSrc K).Nodup) (hc : ∀ e ∈ thresholdMasksOdd K g k, e.1 ∉ lowSrc K)
    (s : State) (m : List Bool) :
    let u := run (unthresholdOdd K g k) m s
    u.phase = s.phase ∧ (∀ q, q ∉ lowSrc K → u.basis q = s.basis q) ∧
      regValue (lowSrc K) u.basis = regValue (lowSrc K) s.basis ^^^
        masksValue (lowSrc K) s.basis (thresholdMasksOdd K g k).reverse := by
  rw [unthresholdOdd_is_load]
  exact loadMasks_correct _ hn _ (fun e he => hc e (by simpa using he)) s m

theorem tableAddOdd_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hsrc : (lowSrc K).Nodup)
    (hn : (K.cin :: (lowOut K ++ K.carry.take 254)).Nodup)
    (haway : ∀ q ∈ mappedWires (mappedRead (lowSrc K) false),
      q ∉ K.cin :: (lowOut K ++ K.carry.take 254))
    (hlen : (lowSrc K).length = (lowOut K).length)
    (hcarryLen : (K.carry.take 254).length + 1 = (lowOut K).length)
    (hctrlSrc : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowSrc K)
    (hctrlOut : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowOut K)
    (s : State) (m : List Bool)
    (hcarry : ∀ q ∈ K.carry.take 254, s.basis q = false) (hcin : s.basis K.cin = false) :
    let u := run (tableAddOdd K g k) m s
    u.phase = s.phase ∧
    regValue (lowOut K) u.basis =
      ((regValue (lowSrc K) s.basis ^^^ masksValue (lowSrc K) s.basis (entryMasksOdd K g k)) +
        regValue (lowOut K) s.basis) % 2 ^ (lowOut K).length ∧
    ∀ q, q ∉ lowOut K → u.basis q = s.basis q := by
  have srcAway (q : Wire) (hq : q ∈ lowSrc K) : q ∉ K.cin :: (lowOut K ++ K.carry.take 254) :=
    haway q (by simpa only [mappedRead_wires] using hq)
  have srcOut (q : Wire) (hq : q ∈ lowSrc K) : q ∉ lowOut K := fun b => srcAway q hq (by simp [b])
  have outSrc (q : Wire) (hq : q ∈ lowOut K) : q ∉ lowSrc K := fun b => srcOut q b hq
  have cinSrc : K.cin ∉ lowSrc K := fun b => srcAway K.cin b (by simp)
  have carrySrc (q : Wire) (hq : q ∈ K.carry.take 254) : q ∉ lowSrc K :=
    fun b => srcAway q b (by simp [hq])
  obtain ⟨m1, m2, m3, he⟩ := run_three (tableOdd K g k) (lowAdder K) (untabledOdd K g k) m s
  let st1 := run (tableOdd K g k) m1 s
  let s2 := run (lowAdder K) m2 st1
  let s3 := run (untabledOdd K g k) m3 s2
  have first := tableOdd_load K g k hsrc hctrlSrc s m1
  have carry1 : ∀ q ∈ K.carry.take 254, st1.basis q = false :=
    fun q hq => (first.2.1 q (carrySrc q hq)).trans (hcarry q hq)
  have cin1 : st1.basis K.cin = false := (first.2.1 K.cin cinSrc).trans hcin
  have mid := mappedAdd_correct (mappedRead (lowSrc K) false) (lowOut K)
    (K.carry.take 254) K.cin hn haway (by simpa [mappedRead_length] using hlen)
    hcarryLen st1 m2 carry1
  have out1 : regValue (lowOut K) st1.basis = regValue (lowOut K) s.basis :=
    regValue_congr _ _ _ (fun q hq => first.2.1 q (outSrc q hq))
  have src2 : regValue (lowSrc K) s2.basis = regValue (lowSrc K) st1.basis :=
    regValue_congr _ _ _ (fun q hq => mid.2.1 q (srcOut q hq))
  have masks2 : masksValue (lowSrc K) s2.basis (entryMasksOdd K g k) =
      masksValue (lowSrc K) s.basis (entryMasksOdd K g k) :=
    masksValue_congr _ _ _ _ (fun e he' => (mid.2.1 e.1 (hctrlOut e he')).trans (first.2.1 e.1 (hctrlSrc e he')))
  have last := tableOdd_unload K g k hsrc hctrlSrc s2 m3
  have src3 : regValue (lowSrc K) s3.basis = regValue (lowSrc K) s.basis := by
    change regValue (lowSrc K) (run (untabledOdd K g k) m3 s2).basis = _
    rw [last.2.2, src2, first.2.2, masksValue_reverse, masks2]
    simp [Nat.xor_assoc]
  have out3 : regValue (lowOut K) s3.basis = regValue (lowOut K) s2.basis :=
    regValue_congr _ _ _ (fun q hq => last.2.1 q (outSrc q hq))
  have value : regValue (lowOut K) s3.basis =
      ((regValue (lowSrc K) s.basis ^^^ masksValue (lowSrc K) s.basis (entryMasksOdd K g k)) +
        regValue (lowOut K) s.basis) % 2 ^ (lowOut K).length := by
    rw [out3]
    change regValue (lowOut K) (run (mappedAdd (mappedRead (lowSrc K) false) (lowOut K)
      (K.carry.take 254) K.cin) m2 st1).basis = _
    rw [mid.2.2, mappedRead_value, first.2.2, out1, cin1]
    simp
  have frame : ∀ q, q ∉ lowOut K → s3.basis q = s.basis q := by
    intro q hq
    by_cases hqs : q ∈ lowSrc K
    · exact (regValue_eq_iff _ _ _).mp src3 q hqs
    · exact (last.2.1 q hqs).trans ((mid.2.1 q hq).trans (first.2.1 q hqs))
  dsimp only
  rw [show tableAddOdd K g k = tableOdd K g k ++ lowAdder K ++ untabledOdd K g k from rfl, he]
  exact ⟨last.1.trans (mid.1.trans first.1), value, frame⟩

theorem addClearBetaOdd_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hsrc : (lowSrc K).Nodup)
    (hn : (K.cin :: (lowOut K ++ K.carry.take 254)).Nodup)
    (haway : ∀ q ∈ mappedWires (mappedRead (lowSrc K) false),
      q ∉ K.cin :: (lowOut K ++ K.carry.take 254))
    (hlen : (lowSrc K).length = (lowOut K).length)
    (hcarryLen : (K.carry.take 254).length + 1 = (lowOut K).length)
    (hctrlSrc : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowSrc K)
    (hctrlOut : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowOut K)
    (hfOut : K.flag ∉ lowOut K) (hsOut : sign K ∉ lowOut K) (hhOut : K.high ∉ lowOut K)
    (hfHigh : K.flag ≠ K.high) (hsHigh : sign K ≠ K.high)
    (s : State) (m : List Bool) (hzero : regValue (lowSrc K) s.basis = 0)
    (hcarry : ∀ q ∈ K.carry.take 254, s.basis q = false) (hcin : s.basis K.cin = false)
    (hbeta : s.basis K.high = (s.basis K.flag && s.basis (sign K))) :
    let u := run (addClearBetaOdd K g k) m s
    u.phase = s.phase ∧ u.basis K.high = false ∧
      regValue (lowOut K) u.basis =
        (masksValue (lowSrc K) s.basis (entryMasksOdd K g k) + regValue (lowOut K) s.basis) %
          2 ^ (lowOut K).length ∧
      ∀ q, q ∉ lowOut K → q ≠ K.high → u.basis q = s.basis q := by
  let n := measurementCount (tableAddOdd K g k)
  let t := run (tableAddOdd K g k) (m.take n) s
  have first := tableAddOdd_correct K g k hsrc hn haway hlen hcarryLen hctrlSrc hctrlOut
    s (m.take n) hcarry hcin
  have known : t.basis K.high = (t.basis K.flag && t.basis (sign K)) := by
    rw [first.2.2 K.high hhOut, first.2.2 K.flag hfOut, first.2.2 (sign K) hsOut, hbeta]
  have second := erase_and K.flag (sign K) K.high hfHigh hsHigh t (m.drop n) known
  have whole : run (addClearBetaOdd K g k) m s = ⟨t.phase, writeBit t.basis K.high false⟩ := by
    rw [addClearBetaOdd, run_append]; exact second
  have kept : regValue (lowOut K) (writeBit t.basis K.high false) = regValue (lowOut K) t.basis := by
    apply regValue_congr
    intro q hq
    have hq' : q ≠ K.high := fun e => hhOut (e ▸ hq)
    simp [writeBit, Function.update_apply, hq']
  have v := first.2.1
  rw [hzero, Nat.zero_xor] at v
  dsimp only
  rw [whole]
  refine ⟨first.1, by simp [writeBit], kept.trans v, ?_⟩
  intro q hq hqh
  simp only [writeBit, Function.update_apply, hqh, if_false]
  exact first.2.2 q hq

theorem middleOdd_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256) (s : State) (m : List Bool)
    (hzero : regValue (lowSrc K) s.basis = 0) (ha0 : s.basis (alpha K) = false)
    (hh0 : s.basis K.high = false) (hcarry : ∀ q ∈ K.carry.take 254, s.basis q = false)
    (hcin : s.basis K.cin = false) (hwrap : s.basis K.flag = true → s.basis g = true) :
    let v := run (middleOdd K g k) m s
    v.phase = s.phase ∧ v.basis K.high = false ∧
      v.basis (alpha K) = (s.basis g && s.basis (sign K)) ∧
      regValue (lowOut K) v.basis =
        (selectedOdd (s.basis g) (s.basis K.flag) (s.basis (sign K)) k % 2 ^ 255 +
          regValue (lowOut K) s.basis) % 2 ^ 255 ∧
      ∀ q, q ∉ lowOut K → q ≠ alpha K → v.basis q = s.basis q := by
  obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
    controls_distinct K g hn hw
  have low := low_widths K hw
  have cs (q : Wire) (h : q ∈ controls K g) : q ∉ lowSrc K := controls_src K g hn hw q h
  have co (q : Wire) (h : q ∈ controls K g) : q ∉ lowOut K := controls_out K g hn hw q h
  have cc (q : Wire) (h : q ∈ controls K g) : q ∉ K.carry.take 254 := carry_away K g hn hw q h
  have hctrlSrc : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowSrc K :=
    fun e he => cs _ ((maskOdd_controls K g k).1 e he)
  have hctrlOut : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowOut K :=
    fun e he => co _ ((maskOdd_controls K g k).1 e he)
  have haway : ∀ q ∈ mappedWires (mappedRead (lowSrc K) false),
      q ∉ K.cin :: (lowOut K ++ K.carry.take 254) := by
    simpa only [mappedRead_wires] using src_away K g hn hw
  let n := measurementCount (makeFlags K g)
  let t := run (makeFlags K g) (m.take n) s
  have first := makeFlags_correct K g hgA (Ne.symm haS) hfA (Ne.symm hhA) s (m.take n) ha0 hh0
  have tg : t.basis g = s.basis g := first.2.2.2 g hgA hgH
  have tf : t.basis K.flag = s.basis K.flag := first.2.2.2 K.flag hfA hfH
  have ts : t.basis (sign K) = s.basis (sign K) := first.2.2.2 (sign K) (Ne.symm haS) (Ne.symm hhS)
  have ta : t.basis (alpha K) = (t.basis g && t.basis (sign K)) := by rw [tg, ts, first.2.1]
  have tb : t.basis K.high = (t.basis K.flag && t.basis (sign K)) := by rw [tf, ts, first.2.2.1]
  have tw : t.basis K.flag = true → t.basis g = true := by rw [tf, tg]; exact hwrap
  have src0 : regValue (lowSrc K) t.basis = 0 := by
    rw [regValue_congr _ _ _ (fun q hq => first.2.2.2 q
      (fun e => cs (alpha K) (by simp [controls]) (e ▸ hq))
      (fun e => cs K.high (by simp [controls]) (e ▸ hq))), hzero]
  have carry0 : ∀ q ∈ K.carry.take 254, t.basis q = false := fun q hq =>
    (first.2.2.2 q (fun e => cc (alpha K) (by simp [controls]) (e ▸ hq))
      (fun e => cc K.high (by simp [controls]) (e ▸ hq))).trans (hcarry q hq)
  have cin0 : t.basis K.cin = false := (first.2.2.2 K.cin hcA (Ne.symm hhC)).trans hcin
  have second := addClearBetaOdd_correct K g k (lowSrc_nodup K g hn hw) (adder_nodup K g hn hw)
    haway (by rw [low.1, low.2.1]) (by rw [low.2.2, low.2.1]) hctrlSrc hctrlOut
    (co _ (by simp [controls])) (co _ (by simp [controls])) (co _ (by simp [controls]))
    hfH (Ne.symm hhS) t (m.drop n) src0 carry0 cin0 tb
  have mask := entryMasksOdd_value K g k t ta tb tw
  have out0 : regValue (lowOut K) t.basis = regValue (lowOut K) s.basis :=
    regValue_congr _ _ _ (fun q hq => first.2.2.2 q
      (fun e => co (alpha K) (by simp [controls]) (e ▸ hq))
      (fun e => co K.high (by simp [controls]) (e ▸ hq)))
  have mask' : masksValue (lowSrc K) t.basis (entryMasksOdd K g k) =
      selectedOdd (s.basis g) (s.basis K.flag) (s.basis (sign K)) k % 2 ^ 255 := by
    simpa only [tg, tf, ts, low.1] using mask
  dsimp only
  rw [middleOdd, run_append]
  refine ⟨second.1.trans first.1, second.2.1, ?_, ?_, ?_⟩
  · exact (second.2.2.2 (alpha K) (co _ (by simp [controls])) (Ne.symm hhA)).trans first.2.1
  · rw [second.2.2.1, mask', out0, low.2.1]
  · intro q hq hqa
    by_cases hqh : q = K.high
    · subst q; exact second.2.1.trans hh0.symm
    · exact (second.2.2.2 q hq hqh).trans (first.2.2.2 q hqa hqh)

theorem clearWrapOdd_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hsrc : (lowSrc K).Nodup)
    (hnd : (K.flag :: K.cin :: (lowOut K ++ lowSrc K ++ K.carry.take 254)).Nodup)
    (hlen : (lowOut K).length = (lowSrc K).length)
    (hcarryLen : (K.carry.take 254).length + 1 = (lowSrc K).length)
    (haway : ∀ q ∈ K.cin :: (lowOut K ++ K.carry.take 254), q ∉ lowSrc K)
    (hctrl : ∀ e ∈ thresholdMasksOdd K g k, e.1 ∉ lowSrc K)
    (hflagSrc : K.flag ∉ lowSrc K)
    (hgFlag : g ≠ K.flag) (hsFlag : sign K ≠ K.flag) (haFlag : alpha K ≠ K.flag)
    (hgAlpha : g ≠ alpha K) (hsAlpha : sign K ≠ alpha K) (hsSrc : sign K ∉ lowSrc K)
    (s : State) (m : List Bool) (hzero : regValue (lowSrc K) s.basis = 0)
    (hcarry : ∀ q ∈ K.carry.take 254, s.basis q = false) (hcin : s.basis K.cin = false)
    (halpha : s.basis (alpha K) = (s.basis g && s.basis (sign K)))
    (hpred : s.basis K.flag =
      decide (regValue (lowOut K) s.basis < masksValue (lowSrc K) s.basis (thresholdMasksOdd K g k))) :
    let v := run (clearWrapOdd K g k) m s
    v.phase = s.phase ∧ v.basis K.flag = false ∧ v.basis (alpha K) = false ∧
      ∀ q, q ≠ K.flag → q ≠ alpha K → v.basis q = s.basis q := by
  have hgSrc : g ∉ lowSrc K := hctrl (g, k / 2) (by simp [thresholdMasksOdd])
  have haSrc : alpha K ∉ lowSrc K := hctrl
    (alpha K, Nat.xor (k / 2) ((k + 1) / 2 + offsetOdd)) (by simp [thresholdMasksOdd])
  have ctrlFlag : ∀ e ∈ thresholdMasksOdd K g k, e.1 ≠ K.flag := by
    intro e he
    simp only [thresholdMasksOdd, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hgFlag
    · exact haFlag
  have cinSrc : K.cin ∉ lowSrc K := haway K.cin (by simp)
  have outSrc (q : Wire) (hq : q ∈ lowOut K) : q ∉ lowSrc K := haway q (by simp [hq])
  have carrySrc (q : Wire) (hq : q ∈ K.carry.take 254) : q ∉ lowSrc K := haway q (by simp [hq])
  let A := thresholdOdd K g k
  let B := eraseLtChain (lowOut K) (lowSrc K) (K.carry.take 254) K.cin K.flag
  let C := unthresholdOdd K g k
  let D : Program := [.measureX (alpha K) [] [.CZ g (sign K)]]
  obtain ⟨m1, m2, m3, m4, he⟩ := run_four A B C D m s
  let st1 := run A m1 s
  let s2 := run B m2 st1
  let s3 := run C m3 s2
  let s4 := run D m4 s3
  have first := thresholdOdd_load K g k hsrc hctrl s m1
  have src1 : regValue (lowSrc K) st1.basis = masksValue (lowSrc K) s.basis (thresholdMasksOdd K g k) := by
    change regValue (lowSrc K) (run (thresholdOdd K g k) m1 s).basis = _
    rw [first.2.2, hzero]; simp
  have out1 : regValue (lowOut K) st1.basis = regValue (lowOut K) s.basis :=
    regValue_congr _ _ _ (fun q hq => first.2.1 q (outSrc q hq))
  have cin1 : st1.basis K.cin = false := (first.2.1 K.cin cinSrc).trans hcin
  have carry1 : ∀ q ∈ K.carry.take 254, st1.basis q = false :=
    fun q hq => (first.2.1 q (carrySrc q hq)).trans (hcarry q hq)
  have flag1 : st1.basis K.flag = decide (regValue (lowOut K) st1.basis <
      regValue (lowSrc K) st1.basis + (st1.basis K.cin).toNat) := by
    rw [first.2.1 K.flag hflagSrc, out1, src1, cin1]
    simpa using hpred
  have second := eraseLtChain_correct (lowOut K) (lowSrc K) (K.carry.take 254) K.cin K.flag
    hnd hlen hcarryLen st1 m2 carry1 flag1
  change s2 = ⟨st1.phase, writeBit st1.basis K.flag false⟩ at second
  have phase2 : s2.phase = st1.phase := by rw [second]
  have flag2 : s2.basis K.flag = false := by rw [second]; simp [writeBit]
  have outside2 (q : Wire) (hq : q ≠ K.flag) : s2.basis q = st1.basis q := by
    rw [second]; simp [writeBit, Function.update_apply, hq]
  have src2 : regValue (lowSrc K) s2.basis = regValue (lowSrc K) st1.basis :=
    regValue_congr _ _ _ (fun q hq => outside2 q (fun e => hflagSrc (e ▸ hq)))
  have masks2 := masksValue_congr (lowSrc K) (thresholdMasksOdd K g k) s2.basis s.basis
    (fun e he' => (outside2 e.1 (ctrlFlag e he')).trans (first.2.1 e.1 (hctrl e he')))
  have third := thresholdOdd_unload K g k hsrc hctrl s2 m3
  have src3 : regValue (lowSrc K) s3.basis = regValue (lowSrc K) s.basis := by
    change regValue (lowSrc K) (run (unthresholdOdd K g k) m3 s2).basis = _
    rw [third.2.2, src2, src1, masksValue_reverse, masks2]; simp [hzero]
  have flag3 : s3.basis K.flag = false := (third.2.1 K.flag hflagSrc).trans flag2
  have alpha3 : s3.basis (alpha K) = s.basis (alpha K) :=
    (third.2.1 (alpha K) haSrc).trans ((outside2 (alpha K) haFlag).trans (first.2.1 (alpha K) haSrc))
  have g3 : s3.basis g = s.basis g :=
    (third.2.1 g hgSrc).trans ((outside2 g hgFlag).trans (first.2.1 g hgSrc))
  have sign3 : s3.basis (sign K) = s.basis (sign K) :=
    (third.2.1 (sign K) hsSrc).trans ((outside2 (sign K) hsFlag).trans (first.2.1 (sign K) hsSrc))
  have fourth := erase_and g (sign K) (alpha K) hgAlpha hsAlpha s3 m4 (by rw [alpha3, g3, sign3, halpha])
  change s4 = ⟨s3.phase, writeBit s3.basis (alpha K) false⟩ at fourth
  have frame : ∀ q, q ≠ K.flag → q ≠ alpha K → s4.basis q = s.basis q := by
    intro q hqf hqa
    have q4 : s4.basis q = s3.basis q := by rw [fourth]; simp [writeBit, Function.update_apply, hqa]
    rw [q4]
    by_cases hq : q ∈ lowSrc K
    · exact (regValue_eq_iff _ _ _).mp src3 q hq
    · exact (third.2.1 q hq).trans ((outside2 q hqf).trans (first.2.1 q hq))
  dsimp only
  rw [show clearWrapOdd K g k = A ++ B ++ C ++ D from rfl, he]
  have p4 : s4.phase = s3.phase := by rw [fourth]
  have f4 : s4.basis K.flag = false := by
    rw [fourth]; simp [writeBit, Function.update_apply, Ne.symm haFlag, flag3]
  have a4 : s4.basis (alpha K) = false := by rw [fourth]; simp [writeBit]
  exact ⟨p4.trans (third.1.trans (phase2.trans first.1)), f4, a4, frame⟩

theorem signStageOdd_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hh : s.basis K.high = false) :
    let v := run (signStageOdd K g k) m s
    v.phase = s.phase ∧
      regValue (lowOut K) v.basis = regValue K.out s.basis / 2 ∧
      v.basis (sign K) = !(s.basis (lowBit K) ^^ (if k % 2 = 1 then s.basis g else false) ^^ s.basis K.flag) ∧
      v.basis K.high = false ∧
      ∀ q, q ∉ K.out → q ≠ K.high → v.basis q = s.basis q := by
  obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
    controls_distinct K g hn hw
  obtain ⟨rest, hout⟩ := out_shape K hw
  have ho : K.high ∉ K.out := controls_fullOut K g hn hw K.high (by simp [controls]) hhS
  have go : g ∉ K.out := controls_fullOut K g hn hw g (by simp [controls]) hgS
  have fo : K.flag ∉ K.out := controls_fullOut K g hn hw K.flag (by simp [controls]) hfS
  have sLow : sign K ∉ lowOut K := controls_out K g hn hw (sign K) (by simp [controls])
  have sMem : sign K ∈ K.out := by
    rw [show K.out = lowOut K ++ [sign K] from (word_split K.out hw.out).symm]; simp
  have eqS := ExitFusionProof.signStage_eq K g k rest hout
  have zero : measurementCount (ExitFusionResearch.signStage K g k) = 0 :=
    properProgram_measurementCount _ (ExitFusionResearch.signStage_proper K g k hn hw)
  let t := run (ExitFusionResearch.signStage K g k) (m.take 0) s
  have first := signStage_correct (lowBit K) g K.flag K.high rest k
    (by rw [← hout]; exact hw.out) (by rw [← hout]; exact out_nodup K g hn)
    (by rw [← hout]; exact ho) (by rw [← hout]; exact go) (by rw [← hout]; exact fo)
    hgH hfH s (m.take 0) hh
  rw [← eqS, ← hout] at first
  change t.phase = s.phase ∧ regValue (lowOut K) t.basis = regValue K.out s.basis / 2 ∧
    t.basis (sign K) = (s.basis (lowBit K) ^^ (if k % 2 = 1 then s.basis g else false) ^^ s.basis K.flag) ∧
    t.basis K.high = false ∧ ∀ q, q ∉ K.out → q ≠ K.high → t.basis q = s.basis q at first
  have xRun : run [.X (sign K)] (m.drop 0) t = ⟨t.phase, writeBit t.basis (sign K) (!t.basis (sign K))⟩ := by
    simp [run]
  dsimp only
  rw [signStageOdd, run_append, zero]
  change (run [.X (sign K)] (m.drop 0) t).phase = s.phase ∧ _
  rw [xRun]
  refine ⟨first.1, ?_, ?_, ?_, ?_⟩
  · have keep : regValue (lowOut K) (writeBit t.basis (sign K) (!t.basis (sign K))) =
        regValue (lowOut K) t.basis :=
      regValue_congr _ _ _ (fun q hq => by
        have ne : q ≠ sign K := fun e => sLow (e ▸ hq)
        simp [writeBit, Function.update_apply, ne])
    exact keep.trans first.2.1
  · simp [writeBit, first.2.2.1]
  · simp [writeBit, Function.update_apply, hhS, first.2.2.2.1]
  · intro q hq hqh
    have qs : q ≠ sign K := fun e => hq (e ▸ sMem)
    simp only [writeBit, Function.update_apply, qs, if_false]
    exact first.2.2.2.2 q hq hqh

theorem entryMiddleOdd_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hY : regValue K.out s.basis = Y)
    (hy : Y < prime) (hk : k < prime) (hsrc : regValue K.src s.basis = 0)
    (hh : s.basis K.high = false) (hcin : s.basis K.cin = false)
    (hcarry : ∀ q ∈ K.carry, s.basis q = false)
    (hflag : s.basis K.flag = decide (prime ≤ Y + (if s.basis g then k else 0))) :
    let z := (Y + (if s.basis g then k else 0)) % prime
    let u := z / 2 + (if z % 2 = 0 then offsetOdd else 0)
    let b := decide (z % 2 = 0)
    let v := run (entryMiddleOdd K g k) m s
    v.phase = s.phase ∧ regValue (lowOut K) v.basis = u ∧ v.basis (sign K) = b ∧
      v.basis K.flag = s.basis K.flag ∧ v.basis K.high = false ∧
      v.basis (alpha K) = (s.basis g && b) ∧
      ∀ q, q ∉ K.out → q ≠ alpha K → v.basis q = s.basis q := by
  obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
    controls_distinct K g hn hw
  have co (q : Wire) (h : q ∈ controls K g) : q ∉ lowOut K := controls_out K g hn hw q h
  have go : g ∉ K.out := controls_fullOut K g hn hw g (by simp [controls]) hgS
  have fo : K.flag ∉ K.out := controls_fullOut K g hn hw K.flag (by simp [controls]) hfS
  have ao : alpha K ∉ K.out := controls_fullOut K g hn hw (alpha K) (by simp [controls]) haS
  have cio : K.cin ∉ K.out := controls_fullOut K g hn hw K.cin (by simp [controls]) hcS
  have alphaMem : alpha K ∈ K.src := by
    rw [show K.src = lowSrc K ++ [alpha K] from (word_split K.src hw.src).symm]; simp
  have alpha0 : s.basis (alpha K) = false := (regValue_zero K.src s.basis).mp hsrc _ alphaMem
  have bit0 : s.basis (lowBit K) = decide (Y % 2 = 1) := by
    simpa only [lowBit, hY] using word_low_bit K.out s.basis (by rw [hw.out]; decide)
  let n := measurementCount (signStageOdd K g k)
  let st1 := run (signStageOdd K g k) (m.take n) s
  have first := signStageOdd_correct K g k hn hw s (m.take n) hh
  have low1 : regValue (lowOut K) st1.basis = Y / 2 := by rw [first.2.1, hY]
  have high1 : st1.basis K.high = false := first.2.2.2.1
  have frame1 (q : Wire) (hq : q ∉ K.out) : st1.basis q = s.basis q := by
    by_cases hqh : q = K.high
    · subst q; exact high1.trans hh.symm
    · exact first.2.2.2.2 q hq hqh
  have g1 : st1.basis g = s.basis g := frame1 g go
  have flag1 : st1.basis K.flag = s.basis K.flag := frame1 K.flag fo
  let z := (Y + (if s.basis g then k else 0)) % prime
  let u := z / 2 + (if z % 2 = 0 then offsetOdd else 0)
  let b := decide (z % 2 = 0)
  have odd : (if k % 2 = 1 then s.basis g else false) = (s.basis g && decide (k % 2 = 1)) := by
    cases s.basis g <;> by_cases h : k % 2 = 1 <;> simp [h]
  have sign1 : st1.basis (sign K) = b := by
    change (run (signStageOdd K g k) (m.take n) s).basis (sign K) = b
    rw [first.2.2.1, bit0, hflag, odd]
    exact (output_sign_odd_controlled Y k (s.basis g) hy hk).symm
  have src1 : regValue (lowSrc K) st1.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    rw [frame1 q (src_fullOut K g hn q (List.mem_of_mem_take hq))]
    exact (regValue_zero K.src s.basis).mp hsrc q (List.mem_of_mem_take hq)
  have alpha1 : st1.basis (alpha K) = false := (frame1 (alpha K) ao).trans alpha0
  have carry1 : ∀ q ∈ K.carry.take 254, st1.basis q = false := fun q hq =>
    (frame1 q (carry_fullOut K g hn q (List.mem_of_mem_take hq))).trans (hcarry q (List.mem_of_mem_take hq))
  have cin1 : st1.basis K.cin = false := (frame1 K.cin cio).trans hcin
  have wrap1 : st1.basis K.flag = true → st1.basis g = true := by
    rw [flag1, g1, hflag]; exact wrap_implies_control Y k (s.basis g) hy
  let r := run (middleOdd K g k) (m.drop n) st1
  have second := middleOdd_correct K g k hn hw st1 (m.drop n) src1 alpha1 high1 carry1 cin1 wrap1
  have value2 : regValue (lowOut K) r.basis = u := by
    rw [second.2.2.2.1, g1, flag1, hflag, sign1, low1]
    exact selectedOdd_math Y k (s.basis g) hy hk
  have sign2 : r.basis (sign K) = b :=
    (second.2.2.2.2 (sign K) (co _ (by simp [controls])) (Ne.symm haS)).trans sign1
  have flag2 : r.basis K.flag = s.basis K.flag :=
    (second.2.2.2.2 K.flag (co _ (by simp [controls])) hfA).trans flag1
  have alpha2 : r.basis (alpha K) = (s.basis g && b) := by rw [second.2.2.1, g1, sign1]
  have frame2 (q : Wire) (hq : q ∉ K.out) (hqa : q ≠ alpha K) : r.basis q = s.basis q :=
    (second.2.2.2.2 q (fun h => hq (List.mem_of_mem_take h)) hqa).trans (frame1 q hq)
  dsimp only
  rw [entryMiddleOdd, run_append]
  exact ⟨second.1.trans first.1, value2, sign2, flag2, second.2.1, alpha2, frame2⟩

theorem entryBodyOdd_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hY : regValue K.out s.basis = Y)
    (hy : Y < prime) (hk : k < prime) (hsrc : regValue K.src s.basis = 0)
    (hh : s.basis K.high = false) (hcin : s.basis K.cin = false)
    (hcarry : ∀ q ∈ K.carry, s.basis q = false)
    (hflag : s.basis K.flag = decide (prime ≤ Y + (if s.basis g then k else 0))) :
    let z := (Y + (if s.basis g then k else 0)) % prime
    let v := run (entryBodyOdd K g k) m s
    v.phase = s.phase ∧
      regValue K.out v.basis =
        z / 2 + (if z % 2 = 0 then offsetOdd else 0) + (if z % 2 = 0 then 2 ^ 255 else 0) ∧
      v.basis K.flag = false ∧ ∀ q, q ∉ K.out → q ≠ K.flag → v.basis q = s.basis q := by
  obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
    controls_distinct K g hn hw
  have low := low_widths K hw
  have cs (q : Wire) (h : q ∈ controls K g) : q ∉ lowSrc K := controls_src K g hn hw q h
  have co (q : Wire) (h : q ∈ controls K g) : q ∉ lowOut K := controls_out K g hn hw q h
  have cc (q : Wire) (h : q ∈ controls K g) : q ∉ K.carry.take 254 := carry_away K g hn hw q h
  have go : g ∉ K.out := controls_fullOut K g hn hw g (by simp [controls]) hgS
  have cio : K.cin ∉ K.out := controls_fullOut K g hn hw K.cin (by simp [controls]) hcS
  have alphaMem : alpha K ∈ K.src := by
    rw [show K.src = lowSrc K ++ [alpha K] from (word_split K.src hw.src).symm]; simp
  have alpha0 : s.basis (alpha K) = false := (regValue_zero K.src s.basis).mp hsrc _ alphaMem
  have hctrl : ∀ e ∈ thresholdMasksOdd K g k, e.1 ∉ lowSrc K :=
    fun e he => cs _ ((maskOdd_controls K g k).2 e he)
  let n := measurementCount (entryMiddleOdd K g k)
  let t := run (entryMiddleOdd K g k) (m.take n) s
  have first := entryMiddleOdd_correct K g k Y hn hw s (m.take n) hY hy hk hsrc hh hcin hcarry hflag
  let z := (Y + (if s.basis g then k else 0)) % prime
  let u := z / 2 + (if z % 2 = 0 then offsetOdd else 0)
  let b := decide (z % 2 = 0)
  change t.phase = s.phase ∧ regValue (lowOut K) t.basis = u ∧ t.basis (sign K) = b ∧
    t.basis K.flag = s.basis K.flag ∧ t.basis K.high = false ∧
    t.basis (alpha K) = (s.basis g && b) ∧
    ∀ q, q ∉ K.out → q ≠ alpha K → t.basis q = s.basis q at first
  have tg : t.basis g = s.basis g := first.2.2.2.2.2.2 g go hgA
  have ta : t.basis (alpha K) = (t.basis g && t.basis (sign K)) := by
    rw [tg, first.2.2.1, first.2.2.2.2.2.1]
  have src0 : regValue (lowSrc K) t.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    rw [first.2.2.2.2.2.2 q (src_fullOut K g hn q (List.mem_of_mem_take hq))
      (fun e => cs (alpha K) (by simp [controls]) (e ▸ hq))]
    exact (regValue_zero K.src s.basis).mp hsrc q (List.mem_of_mem_take hq)
  have carry0 : ∀ q ∈ K.carry.take 254, t.basis q = false := fun q hq =>
    (first.2.2.2.2.2.2 q (carry_fullOut K g hn q (List.mem_of_mem_take hq))
      (fun e => cc (alpha K) (by simp [controls]) (e ▸ hq))).trans (hcarry q (List.mem_of_mem_take hq))
  have cin0 : t.basis K.cin = false := (first.2.2.2.2.2.2 K.cin cio hcA).trans hcin
  have mask := thresholdMasksOdd_value K g k t ta
  have mask' : masksValue (lowSrc K) t.basis (thresholdMasksOdd K g k) =
      (if s.basis g then (if b then (k + 1) / 2 + offsetOdd else k / 2) else 0) % 2 ^ 255 := by
    simpa only [tg, first.2.2.1, low.1] using mask
  have pred : t.basis K.flag =
      decide (regValue (lowOut K) t.basis < masksValue (lowSrc K) t.basis (thresholdMasksOdd K g k)) := by
    rw [first.2.2.2.1, hflag, first.2.1, mask']
    exact thresholdOdd_math Y k (s.basis g) hy hk
  have second := clearWrapOdd_correct K g k (lowSrc_nodup K g hn hw) (erase_nodup K g hn hw)
    (by rw [low.2.1, low.1]) (by rw [low.2.2, low.1]) (other_away K g hn hw) hctrl
    (cs K.flag (by simp [controls])) hgF (Ne.symm hfS) (Ne.symm hfA)
    hgA (Ne.symm haS) (cs (sign K) (by simp [controls])) t (m.drop n) src0 carry0 cin0 ta pred
  let v := run (clearWrapOdd K g k) (m.drop n) t
  have vlow : regValue (lowOut K) v.basis = u :=
    (regValue_congr _ _ _ (fun q hq => second.2.2.2 q
      (fun e => co K.flag (by simp [controls]) (e ▸ hq))
      (fun e => co (alpha K) (by simp [controls]) (e ▸ hq)))).trans first.2.1
  have vsign : v.basis (sign K) = b :=
    (second.2.2.2 (sign K) (Ne.symm hfS) (Ne.symm haS)).trans first.2.2.1
  have vword : regValue K.out v.basis = u + (if b then 2 ^ 255 else 0) := by
    rw [word_value_split K.out hw.out v.basis]
    change regValue (lowOut K) v.basis + (if v.basis (sign K) then 2 ^ 255 else 0) = _
    rw [vlow, vsign]
  have frame (q : Wire) (hq : q ∉ K.out) (hqf : q ≠ K.flag) : v.basis q = s.basis q := by
    by_cases hqa : q = alpha K
    · subst q; exact second.2.2.1.trans alpha0.symm
    · exact (second.2.2.2 q hqf hqa).trans (first.2.2.2.2.2.2 q hq hqa)
  dsimp only
  rw [entryBodyOdd, run_append]
  refine ⟨second.1.trans first.1, ?_, second.2.1, frame⟩
  simpa only [z, u, b, decide_eq_true_eq] using vword

theorem entryOdd_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hY : regValue K.out s.basis = Y)
    (hy : Y < prime) (hk : k < prime) (hsrc : regValue K.src s.basis = 0)
    (hf : s.basis K.flag = false) (hh : s.basis K.high = false)
    (hcin : s.basis K.cin = false) (hcarry : ∀ q ∈ K.carry, s.basis q = false) :
    let z := (Y + (if s.basis g then k else 0)) % prime
    let v := run (entryOdd K g k) m s
    v.phase = s.phase ∧
      regValue K.out v.basis =
        z / 2 + (if z % 2 = 0 then offsetOdd else 0) + (if z % 2 = 0 then 2 ^ 255 else 0) ∧
      ∀ q, q ∉ K.out → v.basis q = s.basis q := by
  have pc : prime + complement = 2 ^ 256 := by norm_num [prime, modulus, complement]
  let n := measurementCount (entryCompare K g complement k)
  let t := run (entryCompare K g complement k) (m.take n) s
  have initial : FastConst.Frame K s.basis 0 Y false s.basis := ⟨hsrc, hY, hf, fun _ _ => rfl⟩
  have pre := comparePrefix_correct hn 256 hw s.basis hcarry hcin complement prime k Y pc hk hy
    s (m.take n) initial
  have tg : t.basis g = s.basis g := pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have th : t.basis K.high = false :=
    (pre.2.2.2.2 K.high (FastConst.fixed_not_mutable hn K.high (by simp))).trans hh
  have tcin : t.basis K.cin = false :=
    (pre.2.2.2.2 K.cin (FastConst.fixed_not_mutable hn K.cin (by simp))).trans hcin
  have tcarry : ∀ q ∈ K.carry, t.basis q = false := fun q hq =>
    (pre.2.2.2.2 q (FastConst.fixed_not_mutable hn q (by simp [hq]))).trans (hcarry q hq)
  have tflag : t.basis K.flag = decide (prime ≤ Y + (if t.basis g then k else 0)) := by
    rw [tg]
    have h := pre.2.2.2.1
    cases hg : s.basis g <;> simp [hg, show ¬ prime ≤ Y by omega] at h ⊢ <;> exact h
  have body := entryBodyOdd_correct K g k Y hn hw t (m.drop n) pre.2.2.1 hy hk
    pre.2.1 th tcin tcarry tflag
  let v := run (entryBodyOdd K g k) (m.drop n) t
  have frame (q : Wire) (hq : q ∉ K.out) : v.basis q = s.basis q := by
    by_cases hqf : q = K.flag
    · subst q; exact body.2.2.1.trans hf.symm
    · have vq := body.2.2.2 q hq hqf
      by_cases hqs : q ∈ K.src
      · exact vq.trans (((regValue_zero K.src t.basis).mp pre.2.1 q hqs).trans
          ((regValue_zero K.src s.basis).mp hsrc q hqs).symm)
      · exact vq.trans (pre.2.2.2.2 q (by simp [FastConst.mutable, hqs, hq, hqf]))
  dsimp only
  rw [entryOdd, run_append]
  refine ⟨body.1.trans pre.1, ?_, frame⟩
  simpa only [tg] using body.2.1

theorem entryOdd_field_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Fp)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hY : regValue K.out s.basis = Y.val)
    (hsrc : regValue K.src s.basis = 0) (hf : s.basis K.flag = false) (hh : s.basis K.high = false)
    (hcin : s.basis K.cin = false) (hcarry : ∀ q ∈ K.carry, s.basis q = false) :
    let v := run (entryOdd K g k.val) m s
    v.phase = s.phase ∧
      regValue K.out v.basis = oddWord ((Y + (if s.basis g then k else 0)) / 2) ∧
      ∀ q, q ∉ K.out → v.basis q = s.basis q := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hy : Y.val < prime := by rw [prime_eq_secp]; exact ZMod.val_lt Y
  have hk : k.val < prime := by rw [prime_eq_secp]; exact ZMod.val_lt k
  let z := (Y.val + (if s.basis g then k.val else 0)) % prime
  have hz : z < prime := Nat.mod_lt _ (by norm_num [prime, modulus, complement])
  have val : (Y + (if s.basis g then k else 0)).val = z := by
    dsimp [z]
    rw [prime_eq_secp]
    cases hg : s.basis g
    · simp [hg, Nat.mod_eq_of_lt (ZMod.val_lt Y)]
    · simp [hg, ZMod.val_add]
  have field : ((z : Nat) : Fp) = Y + (if s.basis g then k else 0) := by
    rw [← val, ZMod.natCast_zmod_val]
  have h := entryOdd_correct K g k.val Y.val hn hw s m hY hy hk hsrc hf hh hcin hcarry
  refine ⟨h.1, ?_, h.2.2⟩
  rw [h.2.1]
  exact (encoding_oddWord z hz).trans (congrArg (fun a => oddWord (a / 2)) field)

-- ============================================================================
-- Section 5: Exact inversion and field correctness of base `exitOdd`
-- ============================================================================

theorem tableOdd_untabledOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (lowSrc K).Nodup) (hc : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowSrc K)
    (s : State) (m n : List Bool) :
    run (untabledOdd K g k) n (run (tableOdd K g k) m s) = s := by
  rw [tableOdd_is_load, untabledOdd_is_load]
  exact ExitFusionProof.loadMasks_inverse _ _ hn hc s m n

theorem untabledOdd_tableOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (lowSrc K).Nodup) (hc : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowSrc K)
    (s : State) (m n : List Bool) :
    run (tableOdd K g k) n (run (untabledOdd K g k) m s) = s := by
  rw [tableOdd_is_load, untabledOdd_is_load]
  simpa using ExitFusionProof.loadMasks_inverse (lowSrc K) (entryMasksOdd K g k).reverse
    hn (fun e he => hc e (by simpa using he)) s m n

theorem tableSubOdd_tableAddOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hsrc : (lowSrc K).Nodup)
    (hn : (K.cin :: (lowOut K ++ K.carry.take 254)).Nodup)
    (haway : ∀ q ∈ mappedWires (mappedRead (lowSrc K) false), q ∉ K.cin :: (lowOut K ++ K.carry.take 254))
    (hlen : (lowSrc K).length = (lowOut K).length)
    (hcarryLen : (K.carry.take 254).length + 1 = (lowOut K).length)
    (hctrlSrc : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowSrc K)
    (s : State) (m n : List Bool)
    (hcarry : ∀ q ∈ K.carry.take 254, s.basis q = false) (hcin : s.basis K.cin = false) :
    run (tableSubOdd K g k) n (run (tableAddOdd K g k) m s) = s := by
  let A := tableOdd K g k
  let B := untabledOdd K g k
  have za : measurementCount A = 0 := by
    simp [A, tableOdd, measurementCount_append, (maskedConstant_counts _ _ _).2]
  have zb : measurementCount B = 0 := by
    simp [B, untabledOdd, measurementCount_append, (maskedConstant_counts _ _ _).2]
  let t := run A [] s
  have load := tableOdd_load K g k hsrc hctrlSrc s []
  have away (q : Wire) (hq : q ∈ K.cin :: K.carry.take 254) : q ∉ lowSrc K := by
    intro bad
    apply haway q (by simpa only [mappedRead_wires] using bad)
    simp only [List.mem_cons, List.mem_append] at hq ⊢; itauto
  have clean : ∀ q ∈ K.carry.take 254, t.basis q = false :=
    fun q hq => (load.2.1 q (away q (by simp [hq]))).trans (hcarry q hq)
  have cin : t.basis K.cin = false := (load.2.1 _ (away _ (by simp))).trans hcin
  have inv := Arithmetic.ExitFusionResearch.mappedSub_add_inverse (mappedRead (lowSrc K) false) (lowOut K)
    (K.carry.take 254) K.cin hn haway (by simpa only [mappedRead_length] using hlen)
    hcarryLen t m n clean cin
  rw [show tableAddOdd K g k = A ++ lowAdder K ++ B from rfl,
    show tableSubOdd K g k = A ++ mappedSub (mappedRead (lowSrc K) false) (lowOut K)
      (K.carry.take 254) K.cin ++ B from rfl,
    ExitFusionProof.sandwich_expand _ _ _ za zb, ExitFusionProof.sandwich_expand _ _ _ za zb]
  rw [show run A [] (run B [] (run (lowAdder K) m (run A [] s))) =
      run (lowAdder K) m (run A [] s) from
    untabledOdd_tableOdd_inverse K g k hsrc hctrlSrc _ [] []]
  rw [show run (mappedSub (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin) n
      (run (lowAdder K) m (run A [] s)) = run A [] s from inv]
  exact tableOdd_untabledOdd_inverse K g k hsrc hctrlSrc s [] []

theorem undoMiddleOdd_middleOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m n : List Bool)
    (ha0 : s.basis (alpha K) = false) (hh0 : s.basis K.high = false)
    (hcarry : ∀ q ∈ K.carry.take 254, s.basis q = false) (hcin : s.basis K.cin = false) :
    run (undoMiddleOdd K g k) n (run (middleOdd K g k) m s) = s := by
  obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
    controls_distinct K g hn hw
  have low := low_widths K hw
  have cs (q : Wire) (h : q ∈ controls K g) : q ∉ lowSrc K := controls_src K g hn hw q h
  have co (q : Wire) (h : q ∈ controls K g) : q ∉ lowOut K := controls_out K g hn hw q h
  have cc (q : Wire) (h : q ∈ controls K g) : q ∉ K.carry.take 254 := carry_away K g hn hw q h
  have hctrlSrc : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowSrc K :=
    fun e he => cs _ ((maskOdd_controls K g k).1 e he)
  have hctrlOut : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowOut K :=
    fun e he => co _ ((maskOdd_controls K g k).1 e he)
  have haway : ∀ q ∈ mappedWires (mappedRead (lowSrc K) false),
      q ∉ K.cin :: (lowOut K ++ K.carry.take 254) := by
    simpa only [mappedRead_wires] using src_away K g hn hw
  let M := makeFlags K g
  let T := tableAddOdd K g k
  let E : Program := [.measureX K.high [] [.CZ K.flag (sign K)]]
  obtain ⟨m1, m2, m3, forward⟩ := run_three M T E m s
  have mf := makeFlags_correct K g hgA (Ne.symm haS) hfA (Ne.symm hhA) s m1 ha0 hh0
  let st1 := run M m1 s
  let s2 := run T m2 st1
  let s3 := run E m3 s2
  have frame (q : Wire) (hqa : q ≠ alpha K) (hqh : q ≠ K.high) : st1.basis q = s.basis q :=
    mf.2.2.2 q hqa hqh
  have clean : ∀ q ∈ K.carry.take 254, st1.basis q = false := fun q hq =>
    (frame q (fun e => cc (alpha K) (by simp [controls]) (e ▸ hq))
      (fun e => cc K.high (by simp [controls]) (e ▸ hq))).trans (hcarry q hq)
  have ci : st1.basis K.cin = false := (frame _ hcA (Ne.symm hhC)).trans hcin
  have ad := tableAddOdd_correct K g k (lowSrc_nodup K g hn hw) (adder_nodup K g hn hw)
    haway (by rw [low.1, low.2.1]) (by rw [low.2.2, low.2.1]) hctrlSrc hctrlOut st1 m2 clean ci
  have f2 : s2.basis K.flag = s.basis K.flag :=
    (ad.2.2 _ (co _ (by simp [controls]))).trans (frame _ hfA hfH)
  have sg2 : s2.basis (sign K) = s.basis (sign K) :=
    (ad.2.2 _ (co _ (by simp [controls]))).trans (frame _ (Ne.symm haS) (Ne.symm hhS))
  have beta : s2.basis K.high = (s2.basis K.flag && s2.basis (sign K)) := by
    rw [ad.2.2 _ (co _ (by simp [controls])), mf.2.2.1, f2, sg2]
  let A : Program := [.CCX K.flag (sign K) K.high]
  let B := tableSubOdd K g k
  let C : Program := [.measureX K.high [] [.CZ K.flag (sign K)]]
  let D : Program := [.measureX (alpha K) [] [.CZ g (sign K)]]
  obtain ⟨n1, n2, n3, n4, inverse⟩ := run_four A B C D n s3
  have restore : run A n1 s3 = s2 := ExitFusionProof.recompute_measured_and K.flag (sign K) K.high hfH
    (Ne.symm hhS) s2 m3 n1 beta
  have sub := tableSubOdd_tableAddOdd_inverse K g k (lowSrc_nodup K g hn hw) (adder_nodup K g hn hw)
    haway (by rw [low.1, low.2.1]) (by rw [low.2.2, low.2.1]) hctrlSrc st1 m2 n2 clean ci
  have goal : run (A ++ B ++ C ++ D) n (run (M ++ T ++ E) m s) = s := by
    rw [forward]
    change run (A ++ B ++ C ++ D) n s3 = s
    rw [inverse, restore, sub]
    exact ExitFusionProof.cleanup_makeFlags_inverse K g hgA (Ne.symm haS) hfA hgH (Ne.symm hhS) hfH
      (Ne.symm hhA) s m1 n3 n4 ha0 hh0
  simpa only [middleOdd, addClearBetaOdd, undoMiddleOdd, M, T, E, A, B, C, D, List.append_assoc] using goal

theorem recoverWrapOdd_clearWrapOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hsrc : (lowSrc K).Nodup)
    (hnd : (K.flag :: K.cin :: (lowOut K ++ lowSrc K ++ K.carry.take 254)).Nodup)
    (hlen : (lowOut K).length = (lowSrc K).length)
    (hcarryLen : (K.carry.take 254).length + 1 = (lowSrc K).length)
    (haway : ∀ q ∈ K.cin :: (lowOut K ++ K.carry.take 254), q ∉ lowSrc K)
    (hctrl : ∀ e ∈ thresholdMasksOdd K g k, e.1 ∉ lowSrc K)
    (hflagSrc : K.flag ∉ lowSrc K) (hflagOut : K.flag ∉ lowOut K)
    (hflagCarry : K.flag ∉ K.carry.take 254) (hcinFlag : K.cin ≠ K.flag)
    (hgFlag : g ≠ K.flag) (hsFlag : sign K ≠ K.flag) (haFlag : alpha K ≠ K.flag)
    (hgAlpha : g ≠ alpha K) (hsAlpha : sign K ≠ alpha K) (hsSrc : sign K ∉ lowSrc K)
    (s : State) (m n : List Bool) (hzero : regValue (lowSrc K) s.basis = 0)
    (hcarry : ∀ q ∈ K.carry.take 254, s.basis q = false) (hcin : s.basis K.cin = false)
    (halpha : s.basis (alpha K) = (s.basis g && s.basis (sign K)))
    (hpred : s.basis K.flag =
      decide (regValue (lowOut K) s.basis < masksValue (lowSrc K) s.basis (thresholdMasksOdd K g k))) :
    run (recoverWrapOdd K g k) n (run (clearWrapOdd K g k) m s) = s := by
  have old := clearWrapOdd_correct K g k hsrc hnd hlen hcarryLen haway hctrl
    hflagSrc hgFlag hsFlag haFlag hgAlpha hsAlpha hsSrc
    s m hzero hcarry hcin halpha hpred
  let t := run (clearWrapOdd K g k) m s
  let u : State := ⟨s.phase, writeBit s.basis K.flag false⟩
  have uk (q : Wire) (hq : q ≠ K.flag) : u.basis q = s.basis q := by simp [u, writeBit, hq]
  have uf : u.basis K.flag = false := by simp [u, writeBit]
  have tg : t.basis g = s.basis g := old.2.2.2 g hgFlag hgAlpha
  have ts : t.basis (sign K) = s.basis (sign K) := old.2.2.2 _ hsFlag hsAlpha
  have initial (record : List Bool) : run [.CCX g (sign K) (alpha K)] record t = u := by
    simp only [run]
    apply State.extensionality
    · exact old.1
    · funext q
      by_cases qa : q = alpha K
      · subst q
        have az : t.basis (alpha K) = false := old.2.2.1
        simp [writeBit, az, tg, ts, ← halpha, u, haFlag]
      · by_cases qf : q = K.flag
        · subst q; simpa [writeBit, qa, u] using (show t.basis K.flag = false from old.2.1)
        · simp only [writeBit, Function.update_of_ne qa, Function.update_of_ne qf]
          rw [uk q qf]; exact old.2.2.2 q qf qa
  have ctrlFlag : ∀ e ∈ thresholdMasksOdd K g k, e.1 ≠ K.flag := by
    intro e he
    simp only [thresholdMasksOdd, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hgFlag
    · exact haFlag
  have cinSrc : K.cin ∉ lowSrc K := haway K.cin (by simp)
  have outSrc (q : Wire) (hq : q ∈ lowOut K) : q ∉ lowSrc K := haway q (by simp [hq])
  have carrySrc (q : Wire) (hq : q ∈ K.carry.take 254) : q ∉ lowSrc K := haway q (by simp [hq])
  let A := thresholdOdd K g k
  let B := Arithmetic.ExitFusionResearch.computeLtChain (lowOut K) (lowSrc K) (K.carry.take 254) K.cin K.flag
  let C := unthresholdOdd K g k
  let st1 := run A [] u
  let s2 := run B n st1
  let s3 := run C [] s2
  have first := thresholdOdd_load K g k hsrc hctrl u []
  have uSrc : regValue (lowSrc K) u.basis = 0 := by
    rw [regValue_congr _ _ _ (fun q hq => uk q (fun e => hflagSrc (e ▸ hq))), hzero]
  have um : masksValue (lowSrc K) u.basis (thresholdMasksOdd K g k) =
      masksValue (lowSrc K) s.basis (thresholdMasksOdd K g k) :=
    masksValue_congr _ _ _ _ (fun e he => uk _ (ctrlFlag e he))
  have src1 : regValue (lowSrc K) st1.basis = masksValue (lowSrc K) s.basis (thresholdMasksOdd K g k) := by
    change regValue (lowSrc K) (run (thresholdOdd K g k) [] u).basis = _
    rw [first.2.2, uSrc, um]; simp
  have out1 : regValue (lowOut K) st1.basis = regValue (lowOut K) s.basis :=
    regValue_congr _ _ _ (fun q hq => (first.2.1 q (outSrc q hq)).trans (uk q (fun e => hflagOut (e ▸ hq))))
  have ci1 : st1.basis K.cin = false := by rw [first.2.1 _ cinSrc, uk _ hcinFlag, hcin]
  have cl1 : ∀ q ∈ K.carry.take 254, st1.basis q = false := fun q hq => by
    rw [first.2.1 q (carrySrc q hq), uk q (fun e => hflagCarry (e ▸ hq)), hcarry q hq]
  have flag1 : st1.basis K.flag = false := (first.2.1 _ hflagSrc).trans uf
  have second := Arithmetic.ExitFusionResearch.computeLtChain_correct (lowOut K) (lowSrc K)
    (K.carry.take 254) K.cin K.flag hnd hlen hcarryLen st1 n cl1
  change s2 = ⟨st1.phase, writeBit st1.basis K.flag
    (st1.basis K.flag ^^ decide (regValue (lowOut K) st1.basis <
      regValue (lowSrc K) st1.basis + (st1.basis K.cin).toNat))⟩ at second
  have flag2 : s2.basis K.flag = s.basis K.flag := by
    rw [second]
    simp only [writeBit, Function.update_self, flag1, Bool.false_xor, out1, src1, ci1,
      Bool.toNat_false, Nat.add_zero]
    exact hpred.symm
  have keep2 (q : Wire) (hq : q ≠ K.flag) : s2.basis q = st1.basis q := by rw [second]; simp [writeBit, hq]
  have phase2 : s2.phase = st1.phase := by rw [second]
  have src2 : regValue (lowSrc K) s2.basis = masksValue (lowSrc K) s.basis (thresholdMasksOdd K g k) := by
    rw [regValue_congr _ _ _ (fun q hq => keep2 q (fun e => hflagSrc (e ▸ hq))), src1]
  have masks2 := masksValue_congr (lowSrc K) (thresholdMasksOdd K g k) s2.basis s.basis
    (fun e he => (keep2 _ (ctrlFlag e he)).trans ((first.2.1 _ (hctrl e he)).trans (uk _ (ctrlFlag e he))))
  have third := thresholdOdd_unload K g k hsrc hctrl s2 []
  have src3 : regValue (lowSrc K) s3.basis = regValue (lowSrc K) s.basis := by
    change regValue (lowSrc K) (run (unthresholdOdd K g k) [] s2).basis = _
    rw [third.2.2, src2, masksValue_reverse, masks2, hzero]; simp
  have final : s3 = s := by
    apply State.extensionality
    · exact third.1.trans (phase2.trans first.1)
    · funext q
      by_cases hq : q ∈ lowSrc K
      · exact (regValue_eq_iff _ _ _).mp src3 q hq
      · rw [third.2.1 q hq]
        by_cases qf : q = K.flag
        · subst q; exact flag2
        · exact (keep2 q qf).trans ((first.2.1 q hq).trans (uk q qf))
  have zA : measurementCount A = 0 := by simp [A, thresholdOdd, measurementCount_append, (maskedConstant_counts _ _ _).2]
  have zC : measurementCount C = 0 := by simp [C, unthresholdOdd, measurementCount_append, (maskedConstant_counts _ _ _).2]
  change run ([Instr.CCX g (sign K) (alpha K)] ++ A ++ B ++ C) n t = s
  simp only [List.append_assoc, run_append, run_take, measurementCount, List.take_zero, List.drop_zero]
  rw [initial, zA, List.drop_zero]
  simp_rw [ExitFusionProof.zero_records A zA, ExitFusionProof.zero_records C zC]
  exact final

theorem recoverWrapOdd_entryBodyOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m r : List Bool) (hY : regValue K.out s.basis = Y)
    (hy : Y < prime) (hk : k < prime) (hsrc : regValue K.src s.basis = 0)
    (hh : s.basis K.high = false) (hcin : s.basis K.cin = false)
    (hcarry : ∀ q ∈ K.carry, s.basis q = false)
    (hflag : s.basis K.flag = decide (prime ≤ Y + (if s.basis g then k else 0))) :
    run (recoverWrapOdd K g k) r (run (entryBodyOdd K g k) m s) =
      run (entryMiddleOdd K g k) (m.take (measurementCount (entryMiddleOdd K g k))) s := by
  obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
    controls_distinct K g hn hw
  have low := low_widths K hw
  have cs (q : Wire) (h : q ∈ controls K g) : q ∉ lowSrc K := controls_src K g hn hw q h
  have co (q : Wire) (h : q ∈ controls K g) : q ∉ lowOut K := controls_out K g hn hw q h
  have cc (q : Wire) (h : q ∈ controls K g) : q ∉ K.carry.take 254 := carry_away K g hn hw q h
  have go : g ∉ K.out := controls_fullOut K g hn hw g (by simp [controls]) hgS
  have cio : K.cin ∉ K.out := controls_fullOut K g hn hw K.cin (by simp [controls]) hcS
  have hctrl : ∀ e ∈ thresholdMasksOdd K g k, e.1 ∉ lowSrc K :=
    fun e he => cs _ ((maskOdd_controls K g k).2 e he)
  let n := measurementCount (entryMiddleOdd K g k)
  let t := run (entryMiddleOdd K g k) (m.take n) s
  have first := entryMiddleOdd_correct K g k Y hn hw s (m.take n) hY hy hk hsrc hh hcin hcarry hflag
  let z := (Y + (if s.basis g then k else 0)) % prime
  let u := z / 2 + (if z % 2 = 0 then offsetOdd else 0)
  let b := decide (z % 2 = 0)
  change t.phase = s.phase ∧ regValue (lowOut K) t.basis = u ∧ t.basis (sign K) = b ∧
    t.basis K.flag = s.basis K.flag ∧ t.basis K.high = false ∧
    t.basis (alpha K) = (s.basis g && b) ∧
    ∀ q, q ∉ K.out → q ≠ alpha K → t.basis q = s.basis q at first
  have tg : t.basis g = s.basis g := first.2.2.2.2.2.2 g go hgA
  have ta : t.basis (alpha K) = (t.basis g && t.basis (sign K)) := by
    rw [tg, first.2.2.1, first.2.2.2.2.2.1]
  have src0 : regValue (lowSrc K) t.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    rw [first.2.2.2.2.2.2 q (src_fullOut K g hn q (List.mem_of_mem_take hq))
      (fun e => cs (alpha K) (by simp [controls]) (e ▸ hq))]
    exact (regValue_zero K.src s.basis).mp hsrc q (List.mem_of_mem_take hq)
  have carry0 : ∀ q ∈ K.carry.take 254, t.basis q = false := fun q hq =>
    (first.2.2.2.2.2.2 q (carry_fullOut K g hn q (List.mem_of_mem_take hq))
      (fun e => cc (alpha K) (by simp [controls]) (e ▸ hq))).trans (hcarry q (List.mem_of_mem_take hq))
  have cin0 : t.basis K.cin = false := (first.2.2.2.2.2.2 K.cin cio hcA).trans hcin
  have mask := thresholdMasksOdd_value K g k t ta
  have mask' : masksValue (lowSrc K) t.basis (thresholdMasksOdd K g k) =
      (if s.basis g then (if b then (k + 1) / 2 + offsetOdd else k / 2) else 0) % 2 ^ 255 := by
    simpa only [tg, first.2.2.1, low.1] using mask
  have pred : t.basis K.flag =
      decide (regValue (lowOut K) t.basis < masksValue (lowSrc K) t.basis (thresholdMasksOdd K g k)) := by
    rw [first.2.2.2.1, hflag, first.2.1, mask']
    exact thresholdOdd_math Y k (s.basis g) hy hk
  rw [entryBodyOdd, run_append]
  exact recoverWrapOdd_clearWrapOdd_inverse K g k (lowSrc_nodup K g hn hw) (erase_nodup K g hn hw)
    (by rw [low.2.1, low.1]) (by rw [low.2.2, low.1]) (other_away K g hn hw) hctrl
    (cs K.flag (by simp [controls])) (co K.flag (by simp [controls]))
    (cc K.flag (by simp [controls])) (Ne.symm hfC) hgF (Ne.symm hfS) (Ne.symm hfA)
    hgA (Ne.symm haS) (cs (sign K) (by simp [controls])) t (m.drop n) r src0 carry0 cin0 ta pred

theorem signStageOdd_proper (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256) : ProperProgram (signStageOdd K g k) := by
  have p := ExitFusionResearch.signStage_proper K g k hn hw
  intro i hi
  simp only [signStageOdd, List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact p i hi
  · simp [ProperGate]

theorem undo_entryMiddleOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m n r : List Bool) (hsrc : regValue K.src s.basis = 0)
    (hh : s.basis K.high = false) (hcin : s.basis K.cin = false)
    (hcarry : ∀ q ∈ K.carry, s.basis q = false) :
    run (signStageOdd K g k).reverse r
      (run (undoMiddleOdd K g k) n (run (entryMiddleOdd K g k) m s)) = s := by
  obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
    controls_distinct K g hn hw
  have cio : K.cin ∉ K.out := controls_fullOut K g hn hw K.cin (by simp [controls]) hcS
  have am : alpha K ∈ K.src := by
    rw [show K.src = lowSrc K ++ [alpha K] from (word_split K.src hw.src).symm]; simp
  have ao : alpha K ∉ K.out := src_fullOut K g hn _ am
  have a0 : s.basis (alpha K) = false := (regValue_zero K.src s.basis).mp hsrc _ am
  let P := signStageOdd K g k
  have proper := signStageOdd_proper K g k hn hw
  have zero : measurementCount P = 0 := properProgram_measurementCount P proper
  let t := run P [] s
  have first := signStageOdd_correct K g k hn hw s [] hh
  have high : t.basis K.high = false := first.2.2.2.1
  have alphaClean : t.basis (alpha K) = false := (first.2.2.2.2 _ ao (Ne.symm hhA)).trans a0
  have carry : ∀ q ∈ K.carry.take 254, t.basis q = false := fun q hq => by
    have mem := List.mem_of_mem_take hq
    have qh : q ≠ K.high := fun e => carry_away K g hn hw K.high (by simp [controls]) (e ▸ hq)
    exact (first.2.2.2.2 q (carry_fullOut K g hn q mem) qh).trans (hcarry q mem)
  have ci : t.basis K.cin = false := (first.2.2.2.2 _ cio (Ne.symm hhC)).trans hcin
  have mid := undoMiddleOdd_middleOdd_inverse K g k hn hw t m n alphaClean high carry ci
  rw [entryMiddleOdd, run_append, zero, List.take_zero, List.drop_zero]
  rw [mid]
  exact run_reverse_proper P proper s [] r

theorem exitOdd_entryOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m n : List Bool) (hY : regValue K.out s.basis = Y)
    (hy : Y < prime) (hk : k < prime) (hsrc : regValue K.src s.basis = 0)
    (hf : s.basis K.flag = false) (hh : s.basis K.high = false)
    (hcin : s.basis K.cin = false) (hcarry : ∀ q ∈ K.carry, s.basis q = false) :
    run (exitOdd K g k) n (run (entryOdd K g k) m s) = s := by
  have pc : prime + complement = 2 ^ 256 := by norm_num [prime, modulus, complement]
  let m1 := m.take (measurementCount (entryCompare K g complement k))
  let m2 := m.drop (measurementCount (entryCompare K g complement k))
  let t := run (entryCompare K g complement k) m1 s
  have initial : FastConst.Frame K s.basis 0 Y false s.basis := ⟨hsrc, hY, hf, fun _ _ => rfl⟩
  have pre := comparePrefix_correct hn 256 hw s.basis hcarry hcin complement prime k Y pc hk hy s m1 initial
  have tg : t.basis g = s.basis g := pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have th : t.basis K.high = false :=
    (pre.2.2.2.2 K.high (FastConst.fixed_not_mutable hn K.high (by simp))).trans hh
  have tcin : t.basis K.cin = false :=
    (pre.2.2.2.2 K.cin (FastConst.fixed_not_mutable hn K.cin (by simp))).trans hcin
  have tcarry : ∀ q ∈ K.carry, t.basis q = false := fun q hq =>
    (pre.2.2.2.2 q (FastConst.fixed_not_mutable hn q (by simp [hq]))).trans (hcarry q hq)
  have tflag : t.basis K.flag = decide (prime ≤ Y + (if t.basis g then k else 0)) := by
    rw [tg]
    have h := pre.2.2.2.1
    cases hg : s.basis g <;> simp [hg, show ¬ prime ≤ Y by omega] at h ⊢ <;> exact h
  let A := recoverWrapOdd K g k
  let B := undoMiddleOdd K g k
  let C := (signStageOdd K g k).reverse
  let D := ExitFusionResearch.eraseInputWrap K g complement k
  obtain ⟨n1, n2, n3, n4, parts⟩ := run_four A B C D n (run (entryBodyOdd K g k) m2 t)
  have recover : run A n1 (run (entryBodyOdd K g k) m2 t) =
      run (entryMiddleOdd K g k) (m2.take (measurementCount (entryMiddleOdd K g k))) t :=
    recoverWrapOdd_entryBodyOdd K g k Y hn hw t m2 n1 pre.2.2.1 hy hk pre.2.1 th tcin tcarry tflag
  have undo : run C n3 (run B n2
      (run (entryMiddleOdd K g k) (m2.take (measurementCount (entryMiddleOdd K g k))) t)) = t :=
    undo_entryMiddleOdd_inverse K g k hn hw t _ n2 n3 pre.2.1 th tcin tcarry
  have erase : run D n4 t = s :=
    ExitFusionProof.eraseInput_entryCompare_inverse K g k Y hn hw s m1 n4 hY hy hk hsrc hf hcin hcarry
  rw [entryOdd, run_append]
  change run (A ++ B ++ C ++ D) n (run (entryBodyOdd K g k) m2 t) = s
  rw [parts, recover, undo, erase]

theorem exitOdd_field_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k H : Fp)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hH : regValue K.out s.basis = oddWord H)
    (hsrc : regValue K.src s.basis = 0) (hf : s.basis K.flag = false) (hh : s.basis K.high = false)
    (hcin : s.basis K.cin = false) (hcarry : ∀ q ∈ K.carry, s.basis q = false) :
    let v := run (exitOdd K g k.val) m s
    v.phase = s.phase ∧ regValue K.out v.basis = (2 * H - (if s.basis g then k else 0)).val ∧
      ∀ q, q ∉ K.out → v.basis q = s.basis q := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let Y : Fp := 2 * H - (if s.basis g then k else 0)
  let b := run (xorConstant K.out (regValue K.out s.basis)) [] s
  have clear := xorConstant_correct K.out (FastConst.out_nodup hn) (regValue K.out s.basis)
    (regValue_lt K.out s.basis) s []
  have yBound : Y.val < 2 ^ K.out.length := by
    rw [hw.out]; exact Y.isLt.trans (by norm_num [p])
  let a := run (xorConstant K.out Y.val) [] b
  have load := xorConstant_correct K.out (FastConst.out_nodup hn) Y.val yBound b []
  have av : regValue K.out a.basis = Y.val := by rw [load.2.2, clear.2.2]; simp
  have ap : a.phase = s.phase := load.1.trans clear.1
  have outside (q : Wire) (hq : q ∉ K.out) : a.basis q = s.basis q :=
    (load.2.1 q hq).trans (clear.2.1 q hq)
  have aSrc : regValue K.src a.basis = 0 := by
    rw [regValue_congr _ _ _ (fun q hq => outside q (src_fullOut K g hn q hq)), hsrc]
  have fixedOutside (q : Wire) (hq : q ∈ K.carry ++ [K.high, K.cin]) : q ∉ K.out := fun bad =>
    FastConst.fixed_not_mutable hn q hq (by simp [FastConst.mutable, bad])
  have af : a.basis K.flag = false := (outside _ (FastConst.flag_not_out hn)).trans hf
  have ah : a.basis K.high = false := (outside _ (fixedOutside _ (by simp))).trans hh
  have ac : a.basis K.cin = false := (outside _ (fixedOutside _ (by simp))).trans hcin
  have aCarry : ∀ q ∈ K.carry, a.basis q = false :=
    fun q hq => (outside q (fixedOutside q (by simp [hq]))).trans (hcarry q hq)
  have ag : a.basis g = s.basis g := outside g (FastConst.g_not_out hn)
  have fwd := entryOdd_field_correct K g k Y hn hw a [] av aSrc af ah ac aCarry
  have math : (Y + (if a.basis g then k else 0)) / 2 = H := by
    rw [ag]
    dsimp only [Y]
    rw [sub_add_cancel]
    have two : (2 : Fp) ≠ 0 := by decide
    field_simp
  have preimage : run (entryOdd K g k.val) [] a = s := by
    apply State.extensionality
    · exact fwd.1.trans ap
    · funext q
      by_cases hq : q ∈ K.out
      · have val : regValue K.out (run (entryOdd K g k.val) [] a).basis = regValue K.out s.basis := by
          rw [fwd.2.1, math, hH]
        exact (regValue_eq_iff _ _ _).mp val q hq
      · exact (fwd.2.2 q hq).trans (outside q hq)
  have hy : Y.val < prime := by rw [prime_eq_secp]; exact Y.isLt
  have hk : k.val < prime := by rw [prime_eq_secp]; exact k.isLt
  have inv := exitOdd_entryOdd_inverse K g k.val Y.val hn hw a [] m av hy hk aSrc af ah ac aCarry
  rw [preimage] at inv
  dsimp only
  rw [inv]
  exact ⟨ap, av, outside⟩

-- ============================================================================
-- Section 6: Base resource bounds (counts, physicality, wires, slots)
-- ============================================================================

attribute [local irreducible] GatePhysical toffoliCount measurementCount Challenge.gateSlots

theorem entryOdd_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) :
    toffoliCount (entryOdd K g k) = 766 ∧ measurementCount (entryOdd K g k) = 767 := by
  have cmp := compareLt_counts none K.src K.out K.carry K.cin K.flag
    (by rw [hw.src, hw.out]) (by rw [hw.carry, hw.out])
  have ad := mappedAdd_counts (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin
    (by simp [mappedRead_length, lowSrc, lowOut, hw.src, hw.out]) (by simp [hw.carry, lowOut, hw.out])
  have er := eraseLtChain_counts (lowOut K) (lowSrc K) (K.carry.take 254) K.cin K.flag
    (by simp [lowSrc, lowOut, hw.src, hw.out]) (by simp [hw.carry, lowSrc, hw.src])
  have rot := rotate_counts K.out
  simp only [entryOdd, entryCompare, entryBodyOdd, entryMiddleOdd, signStageOdd,
    ExitFusionResearch.signStage, middleOdd, makeFlags, addClearBetaOdd, tableAddOdd, lowAdder,
    tableOdd, untabledOdd, clearWrapOdd, thresholdOdd, unthresholdOdd,
    toffoliCount_append, measurementCount_append,
    (maskedConstant_counts _ _ _).1, (maskedConstant_counts _ _ _).2,
    (notRegister_counts _).1, (notRegister_counts _).2,
    cmp.1, cmp.2.1, ad.1, ad.2, er.1, er.2, rot.1, rot.2.1]
  simp only [lowSrc, lowOut, List.length_take, hw.src, hw.out, Option.isSome_none,
    Bool.false_eq_true, if_false]
  norm_num
  unfold ExitFusionResearch.parityControl
  split_ifs <;> simp [toffoliCount, measurementCount]

theorem exitOdd_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) :
    toffoliCount (exitOdd K g k) = 766 ∧ measurementCount (exitOdd K g k) = 766 := by
  have co := Arithmetic.ExitFusionResearch.computeLtChain_counts (lowOut K) (lowSrc K)
    (K.carry.take 254) K.cin K.flag
    (by simp [lowOut, lowSrc, hw.out, hw.src]) (by simp [lowSrc, hw.src, hw.carry])
  have su := mappedSub_counts (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin
    (by simp [mappedRead_length, lowSrc, lowOut, hw.src, hw.out]) (by simp [hw.carry, lowOut, hw.out])
  have er := eraseLtChain_counts K.src K.out (K.carry.take 255) K.cin K.flag
    (by rw [hw.src, hw.out]) (by simp [hw.carry, hw.out])
  have rot := rotate_counts K.out
  have revT := toffoliCount_reverse (signStageOdd K g k)
  have revM := measurementCount_reverse (signStageOdd K g k)
  simp only [exitOdd, recoverWrapOdd, undoMiddleOdd, tableSubOdd, ExitFusionResearch.eraseInputWrap,
    tableOdd, untabledOdd, thresholdOdd, unthresholdOdd,
    toffoliCount_append, measurementCount_append, co.1, co.2, su.1, su.2, er.1, er.2,
    (maskedConstant_counts _ _ _).1, (maskedConstant_counts _ _ _).2,
    (notRegister_counts _).1, (notRegister_counts _).2, revT, revM]
  simp only [signStageOdd, ExitFusionResearch.signStage, ExitFusionResearch.parityControl,
    toffoliCount_append, measurementCount_append, toffoliCount, measurementCount,
    rot.1, rot.2.1, lowSrc, lowOut, hw.src, hw.out]
  split_ifs <;> simp [toffoliCount, measurementCount, hw.src, hw.out]

theorem entryOdd_physical (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256) : GatePhysical (entryOdd K g k) := by
  have cs (q : Wire) (h : q ∈ controls K g) : q ∉ lowSrc K := controls_src K g hn hw q h
  have masked (q : Wire) (hq : q ∈ controls K g) (v : Nat) :
      GatePhysical (maskedConstant q (lowSrc K) v) := maskedConstant_physical q _ v (cs q hq)
  have old := EntryFuse.entry_physical K g complement k hn hw
  obtain ⟨rest, hout⟩ := out_shape K hw
  rw [entry_decompose K g complement k rest hout] at old
  simp only [middle, addClearBeta, tableAdd, clearWrap, gatePhysical_append] at old
  have signP : GatePhysical (signStageOdd K g k) := by
    simp only [signStageOdd, gatePhysical_append]
    exact ⟨ExitFusionResearch.signStage_physical K g k hn hw,
      by simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]⟩
  have tableP : GatePhysical (tableOdd K g k) := by
    simp only [tableOdd, gatePhysical_append]
    repeat' (first | exact masked _ (by simp [controls]) _ | apply And.intro)
  have untableP : GatePhysical (untabledOdd K g k) := by
    simp only [untabledOdd, gatePhysical_append]
    repeat' (first | exact masked _ (by simp [controls]) _ | apply And.intro)
  have thrP : GatePhysical (thresholdOdd K g k) := by
    simp only [thresholdOdd, gatePhysical_append]
    exact ⟨masked _ (by simp [controls]) _, masked _ (by simp [controls]) _⟩
  have unthrP : GatePhysical (unthresholdOdd K g k) := by
    simp only [unthresholdOdd, gatePhysical_append]
    exact ⟨masked _ (by simp [controls]) _, masked _ (by simp [controls]) _⟩
  simp only [entryOdd, entryBodyOdd, entryMiddleOdd, middleOdd, addClearBetaOdd, tableAddOdd,
    clearWrapOdd, gatePhysical_append]
  exact ⟨old.1.1.1, ⟨⟨signP, ⟨old.1.2.1, ⟨⟨⟨tableP, old.1.2.2.1.1.2⟩, untableP⟩, old.1.2.2.2⟩⟩⟩,
    ⟨⟨⟨thrP, old.2.1.1.2⟩, unthrP⟩, old.2.2⟩⟩⟩

theorem exitOdd_physical (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256) : GatePhysical (exitOdd K g k) := by
  have cs (q : Wire) (h : q ∈ controls K g) : q ∉ lowSrc K := controls_src K g hn hw q h
  have masked (q : Wire) (hq : q ∈ controls K g) (v : Nat) :
      GatePhysical (maskedConstant q (lowSrc K) v) := maskedConstant_physical q _ v (cs q hq)
  have old := ExitFusionResearch.exit_physical K g complement k hn hw
  simp only [ExitFusionResearch.exit, ExitFusionResearch.recoverWrap, ExitFusionResearch.undoMiddle,
    gatePhysical_append] at old
  have signRevP : GatePhysical (signStageOdd K g k).reverse := by
    rw [signStageOdd, List.reverse_append, gatePhysical_append]
    exact ⟨by simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate], old.1.2⟩
  have tableP : GatePhysical (tableOdd K g k) := by
    simp only [tableOdd, gatePhysical_append]
    repeat' (first | exact masked _ (by simp [controls]) _ | apply And.intro)
  have untableP : GatePhysical (untabledOdd K g k) := by
    simp only [untabledOdd, gatePhysical_append]
    repeat' (first | exact masked _ (by simp [controls]) _ | apply And.intro)
  have thrP : GatePhysical (thresholdOdd K g k) := by
    simp only [thresholdOdd, gatePhysical_append]
    exact ⟨masked _ (by simp [controls]) _, masked _ (by simp [controls]) _⟩
  have unthrP : GatePhysical (unthresholdOdd K g k) := by
    simp only [unthresholdOdd, gatePhysical_append]
    exact ⟨masked _ (by simp [controls]) _, masked _ (by simp [controls]) _⟩
  simp only [exitOdd, recoverWrapOdd, undoMiddleOdd, tableSubOdd, gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨old.1.1.1.1.1.1.1, thrP⟩, old.1.1.1.1.1.2⟩, unthrP⟩,
    ⟨⟨old.1.1.2.1.1.1.1, ⟨⟨tableP, old.1.1.2.1.1.2⟩, untableP⟩⟩, old.1.1.2.2⟩⟩, signRevP⟩, old.2⟩

private theorem mask_wires_in (K : MeasuredCanonicalModLayout) (q : Wire) (v : Nat)
    (T : Finset Wire) (hq : q ∈ T) (hsrc : ∀ w ∈ K.src, w ∈ T) :
    wires (maskedConstant q (lowSrc K) v) ⊆ T := by
  intro w hw
  have h := List.mem_toFinset.mp (maskedConstant_wires_subset q (lowSrc K) v hw)
  rcases List.mem_cons.mp h with rfl | h'
  · exact hq
  · exact hsrc w (List.mem_of_mem_take h')

theorem entryOdd_wires (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) :
    wires (entryOdd K g k) ⊆ wires (EntryFuse.entry K g complement k) := by
  obtain ⟨rest, hout⟩ := out_shape K hw
  rw [entry_decompose K g complement k rest hout]
  let T := wires (entryCompare K g complement k ++ signStage (lowBit K) g K.flag K.high rest k ++
    middle K g complement k ++ clearWrap K g complement k)
  have hT_eq : T = wires (entryCompare K g complement k) ∪
      wires (signStage (lowBit K) g K.flag K.high rest k) ∪
      wires (middle K g complement k) ∪ wires (clearWrap K g complement k) := by
    simp only [T, wires_append]
  have hsrc : ∀ w ∈ K.src, w ∈ T := by
    intro w hw'
    rw [hT_eq]
    have hm : w ∈ wires (entryCompare K g complement k) := by
      simp only [entryCompare, wires_append, notRegister_wires, Finset.mem_union, List.mem_toFinset]
      exact Or.inl (Or.inl (Or.inl (Or.inr hw')))
    simp only [Finset.mem_union]; exact Or.inl (Or.inl (Or.inl hm))
  have hmf : ({g, K.flag, K.high, alpha K, sign K} : Finset Wire) ⊆ T := by
    intro w hw'
    rw [hT_eq]
    have hm : w ∈ wires (middle K g complement k) := by
      simp only [middle, makeFlags, wires_append, wires, Instr.wires, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
      rcases hw' with rfl | rfl | rfl | rfl | rfl <;> simp
    simp only [Finset.mem_union]; exact Or.inl (Or.inr hm)
  have hG : g ∈ T := hmf (by simp)
  have hF : K.flag ∈ T := hmf (by simp)
  have hH : K.high ∈ T := hmf (by simp)
  have hA : alpha K ∈ T := hmf (by simp)
  have hS : sign K ∈ T := hmf (by simp)
  have hTable : wires (tableOdd K g k) ⊆ T := by
    simp only [tableOdd, wires_append, Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mask_wires_in K _ _ T hS hsrc, mask_wires_in K _ _ T hG hsrc⟩,
      mask_wires_in K _ _ T hA hsrc⟩, mask_wires_in K _ _ T hF hsrc⟩, mask_wires_in K _ _ T hH hsrc⟩
  have hUntable : wires (untabledOdd K g k) ⊆ T := by
    simp only [untabledOdd, wires_append, Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mask_wires_in K _ _ T hH hsrc, mask_wires_in K _ _ T hF hsrc⟩,
      mask_wires_in K _ _ T hA hsrc⟩, mask_wires_in K _ _ T hG hsrc⟩, mask_wires_in K _ _ T hS hsrc⟩
  have hThr : wires (thresholdOdd K g k) ⊆ T := by
    simp only [thresholdOdd, wires_append, Finset.union_subset_iff]
    exact ⟨mask_wires_in K _ _ T hG hsrc, mask_wires_in K _ _ T hA hsrc⟩
  have hUnthr : wires (unthresholdOdd K g k) ⊆ T := by
    simp only [unthresholdOdd, wires_append, Finset.union_subset_iff]
    exact ⟨mask_wires_in K _ _ T hA hsrc, mask_wires_in K _ _ T hG hsrc⟩
  have hX : wires [.X (sign K)] ⊆ T := by
    intro w hw'; simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, or_false] at hw'; subst hw'; exact hS
  have hSign : wires (signStageOdd K g k) ⊆ T := by
    rw [signStageOdd, ExitFusionProof.signStage_eq K g k rest hout, wires_append, Finset.union_subset_iff]
    refine ⟨?_, hX⟩
    intro w hw'; rw [hT_eq]; simp only [Finset.mem_union]; exact Or.inl (Or.inl (Or.inr hw'))
  have hCmp : wires (entryCompare K g complement k) ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [Finset.mem_union]; exact Or.inl (Or.inl (Or.inl hw'))
  have hMF : wires (makeFlags K g) ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [middle, wires_append, Finset.mem_union]
    exact Or.inl (Or.inr (Or.inl hw'))
  have hAdd : wires (lowAdder K) ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [middle, addClearBeta, tableAdd, wires_append, Finset.mem_union]
    exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr hw')))))
  have hBeta : wires [.measureX K.high [] [.CZ K.flag (sign K)]] ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [middle, addClearBeta, wires_append, Finset.mem_union]
    exact Or.inl (Or.inr (Or.inr (Or.inr hw')))
  have hEr : wires (eraseLtChain (lowOut K) (lowSrc K) (K.carry.take 254) K.cin K.flag) ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [clearWrap, wires_append, Finset.mem_union]
    exact Or.inr (Or.inl (Or.inl (Or.inr hw')))
  have hAlpha : wires [.measureX (alpha K) [] [.CZ g (sign K)]] ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [clearWrap, wires_append, Finset.mem_union]
    exact Or.inr (Or.inr hw')
  change wires (entryOdd K g k) ⊆ T
  simp only [entryOdd, entryBodyOdd, entryMiddleOdd, middleOdd, addClearBetaOdd, tableAddOdd,
    clearWrapOdd, wires_append, Finset.union_subset_iff]
  exact ⟨hCmp, ⟨⟨hSign, ⟨hMF, ⟨⟨⟨hTable, hAdd⟩, hUntable⟩, hBeta⟩⟩⟩, ⟨⟨⟨hThr, hEr⟩, hUnthr⟩, hAlpha⟩⟩⟩

theorem entryOdd_support (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) : wires (entryOdd K g k) ⊆ (g :: K.wires).toFinset :=
  (entryOdd_wires K g k hw).trans (EntryFuse.entry_support K g complement k hw)

theorem exitOdd_wires (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) :
    wires (exitOdd K g k) ⊆ wires (ExitFusionResearch.exit K g complement k) := by
  let T := wires (ExitFusionResearch.exit K g complement k)
  have hT_eq : T = wires (ExitFusionResearch.recoverWrap K g complement k) ∪
      wires (ExitFusionResearch.undoMiddle K g complement k) ∪
      wires (ExitFusionResearch.signStage K g k).reverse ∪
      wires (ExitFusionResearch.eraseInputWrap K g complement k) := by
    simp only [T, ExitFusionResearch.exit, wires_append]
  have hsrc : ∀ w ∈ K.src, w ∈ T := by
    intro w hw'
    rw [hT_eq]
    have hm : w ∈ wires (ExitFusionResearch.eraseInputWrap K g complement k) := by
      simp only [ExitFusionResearch.eraseInputWrap, wires_append, notRegister_wires,
        Finset.mem_union, List.mem_toFinset]
      exact Or.inl (Or.inl (Or.inl (Or.inr hw')))
    simp only [Finset.mem_union]; exact Or.inr hm
  have hCCX1 : wires [.CCX g (sign K) (alpha K)] ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [ExitFusionResearch.recoverWrap, wires_append, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hw'))))))
  have hCCX2 : wires [.CCX K.flag (sign K) K.high] ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [ExitFusionResearch.undoMiddle, wires_append, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl hw'))))))
  have hG : g ∈ T := hCCX1 (by simp [wires, Instr.wires])
  have hS : sign K ∈ T := hCCX1 (by simp [wires, Instr.wires])
  have hA : alpha K ∈ T := hCCX1 (by simp [wires, Instr.wires])
  have hF : K.flag ∈ T := hCCX2 (by simp [wires, Instr.wires])
  have hH : K.high ∈ T := hCCX2 (by simp [wires, Instr.wires])
  have hTable : wires (tableOdd K g k) ⊆ T := by
    simp only [tableOdd, wires_append, Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mask_wires_in K _ _ T hS hsrc, mask_wires_in K _ _ T hG hsrc⟩,
      mask_wires_in K _ _ T hA hsrc⟩, mask_wires_in K _ _ T hF hsrc⟩, mask_wires_in K _ _ T hH hsrc⟩
  have hUntable : wires (untabledOdd K g k) ⊆ T := by
    simp only [untabledOdd, wires_append, Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mask_wires_in K _ _ T hH hsrc, mask_wires_in K _ _ T hF hsrc⟩,
      mask_wires_in K _ _ T hA hsrc⟩, mask_wires_in K _ _ T hG hsrc⟩, mask_wires_in K _ _ T hS hsrc⟩
  have hThr : wires (thresholdOdd K g k) ⊆ T := by
    simp only [thresholdOdd, wires_append, Finset.union_subset_iff]
    exact ⟨mask_wires_in K _ _ T hG hsrc, mask_wires_in K _ _ T hA hsrc⟩
  have hUnthr : wires (unthresholdOdd K g k) ⊆ T := by
    simp only [unthresholdOdd, wires_append, Finset.union_subset_iff]
    exact ⟨mask_wires_in K _ _ T hA hsrc, mask_wires_in K _ _ T hG hsrc⟩
  have hCmp : wires (Arithmetic.ExitFusionResearch.computeLtChain (lowOut K) (lowSrc K)
      (K.carry.take 254) K.cin K.flag) ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [ExitFusionResearch.recoverWrap, wires_append, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hw')))))
  have hSub : wires (mappedSub (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin) ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [ExitFusionResearch.undoMiddle, wires_append, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr hw')))))
  have hMeas : wires [.measureX K.high [] [.CZ K.flag (sign K)],
      .measureX (alpha K) [] [.CZ g (sign K)]] ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [ExitFusionResearch.undoMiddle, wires_append, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr (Or.inr hw')))
  have hSignRev : wires (signStageOdd K g k).reverse ⊆ T := by
    rw [wires_reverse, signStageOdd, wires_append, Finset.union_subset_iff]
    refine ⟨?_, ?_⟩
    · intro w hw'; rw [hT_eq, wires_reverse]; simp only [Finset.mem_union]; exact Or.inl (Or.inr hw')
    · intro w hw'; simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_singleton,
        Finset.notMem_empty, or_false] at hw'; subst hw'; exact hS
  have hEr : wires (ExitFusionResearch.eraseInputWrap K g complement k) ⊆ T := by
    intro w hw'; rw [hT_eq]; simp only [Finset.mem_union]; exact Or.inr hw'
  change wires (exitOdd K g k) ⊆ T
  simp only [exitOdd, recoverWrapOdd, undoMiddleOdd, tableSubOdd, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨hCCX1, hThr⟩, hCmp⟩, hUnthr⟩, ⟨⟨hCCX2, ⟨⟨hTable, hSub⟩, hUntable⟩⟩, hMeas⟩⟩, hSignRev⟩, hEr⟩

theorem exitOdd_support (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) : wires (exitOdd K g k) ⊆ (g :: K.wires).toFinset :=
  (exitOdd_wires K g k).trans (ExitFusionResearch.exit_support K g complement k hw)

theorem entryOdd_gateSlots_le (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) : Challenge.gateSlots (entryOdd K g k) ≤ 24000 := by
  have full := Baselines.maskedConstant_gateSlots_le g K.src (complement + k)
  have a := Baselines.maskedConstant_gateSlots_le (sign K) (lowSrc K) offsetOdd
  have b := Baselines.maskedConstant_gateSlots_le g (lowSrc K) (k / 2)
  have d := Baselines.maskedConstant_gateSlots_le (alpha K) (lowSrc K)
    (Nat.xor (Nat.xor offsetOdd (k / 2)) ((k + 1) / 2 + offsetOdd))
  have e := Baselines.maskedConstant_gateSlots_le K.flag (lowSrc K)
    (Nat.xor (k / 2) ((k + 1) / 2 + offsetOdd))
  have f := Baselines.maskedConstant_gateSlots_le K.high (lowSrc K)
    (Nat.xor (k / 2 + complement) (k / 2))
  have t := Baselines.maskedConstant_gateSlots_le (alpha K) (lowSrc K)
    (Nat.xor (k / 2) ((k + 1) / 2 + offsetOdd))
  have cmp := Baselines.compareLt_gateSlots_le none K.src K.out K.carry K.cin K.flag
  have add := Baselines.mappedAdd_gateSlots_le (mappedRead (lowSrc K) false)
    (lowOut K) (K.carry.take 254) K.cin
  have er := Baselines.eraseLt_gateSlots_le (lowOut K) (lowSrc K) (K.carry.take 254) K.cin K.flag
  have rot := (Baselines.rotate_gateSlots_le K.out).1
  have parity (q : Wire) : Challenge.gateSlots (ExitFusionResearch.parityControl g q k) ≤ 1 := by
    unfold ExitFusionResearch.parityControl
    split <;> simp [Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots]
  have ps := parity (ExitFusionResearch.sign K)
  have ph := parity K.high
  have low := low_widths K hw
  simp only [low.1, hw.src] at full a b d e f t
  simp only [hw.src, hw.out] at cmp
  simp only [mappedRead_length, low.1] at add
  simp only [low.2.1] at er
  simp only [hw.out] at rot
  simp only [entryOdd, entryCompare, entryBodyOdd, entryMiddleOdd, signStageOdd,
    ExitFusionResearch.signStage, middleOdd, makeFlags, addClearBetaOdd, tableAddOdd, lowAdder,
    tableOdd, untabledOdd, clearWrapOdd, thresholdOdd, unthresholdOdd,
    Challenge.gateSlots_append, Baselines.notRegister_gateSlots,
    Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots, hw.src,
    List.length_cons, List.length_nil, Nat.reduceAdd]
  omega

theorem exitOdd_gateSlots_le (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) : Challenge.gateSlots (exitOdd K g k) ≤ 24000 := by
  have full := Baselines.maskedConstant_gateSlots_le g K.src (complement + k)
  have a := Baselines.maskedConstant_gateSlots_le (sign K) (lowSrc K) offsetOdd
  have b := Baselines.maskedConstant_gateSlots_le g (lowSrc K) (k / 2)
  have d := Baselines.maskedConstant_gateSlots_le (alpha K) (lowSrc K)
    (Nat.xor (Nat.xor offsetOdd (k / 2)) ((k + 1) / 2 + offsetOdd))
  have e := Baselines.maskedConstant_gateSlots_le K.flag (lowSrc K)
    (Nat.xor (k / 2) ((k + 1) / 2 + offsetOdd))
  have f := Baselines.maskedConstant_gateSlots_le K.high (lowSrc K)
    (Nat.xor (k / 2 + complement) (k / 2))
  have t := Baselines.maskedConstant_gateSlots_le (alpha K) (lowSrc K)
    (Nat.xor (k / 2) ((k + 1) / 2 + offsetOdd))
  have cmp := Arithmetic.ExitFusionResearch.computeLt_gateSlots_le (lowOut K) (lowSrc K)
    (K.carry.take 254) K.cin K.flag
  have add := Baselines.mappedSub_gateSlots_le (mappedRead (lowSrc K) false)
    (lowOut K) (K.carry.take 254) K.cin
  have er := Baselines.eraseLt_gateSlots_le K.src K.out (K.carry.take 255) K.cin K.flag
  have rot := (Baselines.rotate_gateSlots_le K.out).1
  have parity (q : Wire) : Challenge.gateSlots (ExitFusionResearch.parityControl g q k) ≤ 1 := by
    unfold ExitFusionResearch.parityControl
    split <;> simp [Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots]
  have ps := parity (ExitFusionResearch.sign K)
  have ph := parity K.high
  have low := low_widths K hw
  simp only [low.1, hw.src] at full a b d e f t
  simp only [low.2.1] at cmp
  simp only [mappedRead_length, low.1, low.2.1] at add
  simp only [hw.src] at er
  simp only [hw.out] at rot
  simp only [exitOdd, recoverWrapOdd, undoMiddleOdd, tableSubOdd, ExitFusionResearch.eraseInputWrap,
    signStageOdd, ExitFusionResearch.signStage, ExitFusionResearch.slots_reverse,
    tableOdd, untabledOdd, thresholdOdd, unthresholdOdd,
    Challenge.gateSlots_append, Baselines.notRegister_gateSlots,
    Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots, hw.src,
    List.length_cons, List.length_nil, Nat.reduceAdd]
  omega

-- ============================================================================
-- Section 7: Parity-uniform 765 T entry/exit (`entryAllOdd` and `exitAllOdd`)
-- ============================================================================

def entryOptOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  ParityCarry.comparePrefixNew g K.src K.out K.carry K.cin K.flag (complement + k) ++
    entryBodyOdd K g k

def exitOptOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  recoverWrapOdd K g k ++ undoMiddleOdd K g k ++ (signStageOdd K g k).reverse ++
    ParityCarry.erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag (complement + k)

def evenBodyOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  ParityEven.moveCached K.high (alpha K) ++ signStageOdd K g k ++
    [.CX g (alpha K), .CX K.flag (alpha K), .CCX K.flag (sign K) K.high] ++
    addClearBetaOdd K g k ++ clearWrapOdd K g k

def entryEvenOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  [.CCX g (lowBit K) K.high] ++
    ParityEven.comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag (complement + k) ++
    evenBodyOdd K g k

def undoMiddleKeepOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  [.CCX K.flag (sign K) K.high] ++ tableSubOdd K g k ++
    [.measureX K.high [] [.CZ K.flag (sign K)],
     .CX g (alpha K), .CX K.flag (alpha K), .measureX K.high [] []]

def exitEvenOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  recoverWrapOdd K g k ++ undoMiddleKeepOdd K g k ++
    (signStageOdd K g k).reverse ++ ParityEven.eraseInputMoved K g k

def entryAllOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  if k % 2 = 1 then entryOptOdd K g k else entryEvenOdd K g k

def exitAllOdd (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  if k % 2 = 1 then exitOptOdd K g k else exitEvenOdd K g k

private theorem entryCompare_eq_old (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) :
    entryCompare K g complement k =
      ParityCarry.comparePrefixOld g K.src K.out K.carry K.cin K.flag (complement + k) := by
  simp only [entryCompare, ParityCarry.comparePrefixOld, ParityCarry.loadNot,
    ParityCarry.unloadNot, List.append_assoc]

theorem entryOptOdd_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) (hn : (g :: K.wires).Nodup) (hk : k % 2 = 1)
    (s : State) (m : List Bool) (hs : regValue K.src s.basis = 0) (hi : s.basis K.cin = false) :
    run (entryOptOdd K g k) m s = run (entryOdd K g k) m s := by
  have he : (complement + k) % 2 = 0 := by norm_num [complement, Nat.add_mod, hk]
  rw [entryOptOdd, entryOdd, entryCompare_eq_old]
  exact ParityConvert.prefix_eq _ _ _ s m
    (ParityConvert.compare_layout_counts K g hw (complement + k)).2.1
    (ParityCarry.compare_layout_eq K g hw hn (complement + k) he s m hs hi)

theorem exitOptOdd_entryOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256) (ho : k % 2 = 1)
    (s : State) (m n : List Bool) (hY : regValue K.out s.basis = Y)
    (hy : Y < prime) (hk : k < prime) (hsrc : regValue K.src s.basis = 0)
    (hf : s.basis K.flag = false) (hh : s.basis K.high = false)
    (hcin : s.basis K.cin = false) (hcarry : ∀ q ∈ K.carry, s.basis q = false) :
    run (exitOptOdd K g k) n (run (entryOdd K g k) m s) = s := by
  have pc : prime + complement = 2 ^ 256 := by norm_num [prime, modulus, complement]
  have he : (complement + k) % 2 = 0 := by norm_num [complement, Nat.add_mod, ho]
  let m1 := m.take (measurementCount (entryCompare K g complement k))
  let m2 := m.drop (measurementCount (entryCompare K g complement k))
  let t := run (entryCompare K g complement k) m1 s
  have initial : FastConst.Frame K s.basis 0 Y false s.basis := ⟨hsrc, hY, hf, fun _ _ => rfl⟩
  have pre := comparePrefix_correct hn 256 hw s.basis hcarry hcin complement prime k Y pc hk hy s m1 initial
  have tg : t.basis g = s.basis g := pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have th : t.basis K.high = false :=
    (pre.2.2.2.2 K.high (FastConst.fixed_not_mutable hn K.high (by simp))).trans hh
  have tcin : t.basis K.cin = false :=
    (pre.2.2.2.2 K.cin (FastConst.fixed_not_mutable hn K.cin (by simp))).trans hcin
  have tcarry : ∀ q ∈ K.carry, t.basis q = false := fun q hq =>
    (pre.2.2.2.2 q (FastConst.fixed_not_mutable hn q (by simp [hq]))).trans (hcarry q hq)
  have tflag : t.basis K.flag = decide (prime ≤ Y + (if t.basis g then k else 0)) := by
    rw [tg]
    have h := pre.2.2.2.1
    cases hg : s.basis g <;> simp [hg, show ¬ prime ≤ Y by omega] at h ⊢ <;> exact h
  let A := recoverWrapOdd K g k
  let B := undoMiddleOdd K g k
  let C := (signStageOdd K g k).reverse
  let D := ParityCarry.erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag (complement + k)
  obtain ⟨n1, n2, n3, n4, parts⟩ := run_four A B C D n (run (entryBodyOdd K g k) m2 t)
  have recover : run A n1 (run (entryBodyOdd K g k) m2 t) =
      run (entryMiddleOdd K g k) (m2.take (measurementCount (entryMiddleOdd K g k))) t :=
    recoverWrapOdd_entryBodyOdd K g k Y hn hw t m2 n1 pre.2.2.1 hy hk pre.2.1 th tcin tcarry tflag
  have undo : run C n3 (run B n2
      (run (entryMiddleOdd K g k) (m2.take (measurementCount (entryMiddleOdd K g k))) t)) = t :=
    undo_entryMiddleOdd_inverse K g k hn hw t _ n2 n3 pre.2.1 th tcin tcarry
  have erase : run D n4 t = s := by
    have e1 := ParityCarry.erase_layout_eq K g hw hn (complement + k) he t n4 pre.2.1 tcin
    rw [← ParityConvert.old_erase_split K g k] at e1
    exact e1.trans (ExitFusionProof.eraseInput_entryCompare_inverse K g k Y hn hw s m1 n4 hY hy hk hsrc hf hcin hcarry)
  rw [entryOdd, run_append]
  change run (A ++ B ++ C ++ D) n (run (entryBodyOdd K g k) m2 t) = s
  rw [parts, recover, undo, erase]

private theorem signStageOdd_outside (K : MeasuredCanonicalModLayout) (g q : Wire) (k : Nat)
    (hw : K.Widths 256) (qo : q ∉ K.out) (qg : q ≠ g) (qf : q ≠ K.flag) (qh : q ≠ K.high) :
    q ∉ wires (signStageOdd K g k) := by
  have sm : sign K ∈ K.out := by
    rw [show K.out = lowOut K ++ [sign K] from (word_split K.out hw.out).symm]; simp
  have qs : q ≠ sign K := fun e => qo (e ▸ sm)
  rw [signStageOdd, wires_append, Finset.mem_union]
  rintro (h | h)
  · exact ParityEven.signStage_outside K g q k hw qo qg qf qh h
  · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, or_false] at h
    exact qs h

private theorem cached_flag_odd_eq (g b f a : Wire) (hga : g ≠ a) (hfa : f ≠ a)
    (s : State) (m : List Bool) (A : Bool) (ha : s.basis a = false)
    (hprod : (s.basis g && s.basis b) = (A ^^ s.basis g ^^ s.basis f)) :
    run [.CX g a, .CX f a] m (ParityEven.put s a A) = run [.CCX g b a] m s := by
  apply State.extensionality
  · simp [run, ParityEven.put]
  funext q
  by_cases hq : q = a
  · subst q
    simp [run, ParityEven.put, writeBit, Function.update, hga, hfa, ha, hprod]
  · simp [run, ParityEven.put, writeBit, Function.update, hq]

private theorem cached_stage_odd_eq (S Q : Program) (h a g b f : Wire)
    (hne : a ≠ h) (hga : g ≠ a) (hfa : f ≠ a)
    (s : State) (m : List Bool) (A : Bool) (hh : s.basis h = false) (ha : s.basis a = false)
    (outside : a ∉ wires S)
    (product : ((run S m s).basis g && (run S m s).basis b) =
      (A ^^ (run S m s).basis g ^^ (run S m s).basis f)) :
    run (ParityEven.moveCached h a ++ S ++ [.CX g a, .CX f a] ++ Q) m (ParityEven.put s h A) =
      run (S ++ [.CCX g b a] ++ Q) m s := by
  have kept : (run S m s).basis a = false := (run_preserves_outside S m s a outside).trans ha
  have e : run (ParityEven.moveCached h a ++ S ++ [.CX g a, .CX f a]) m (ParityEven.put s h A) =
      run (S ++ [.CCX g b a]) m s := by
    simp only [List.append_assoc, run_append, run_take]
    have z : measurementCount (ParityEven.moveCached h a) = 0 := by
      simp [ParityEven.moveCached, measurementCount]
    simp only [z, List.drop_zero]
    rw [ParityEven.moveCached_eq h a hne s m A hh ha, ParityEven.run_put S m s a A outside]
    exact cached_flag_odd_eq g b f a hga hfa (run S m s) _ A kept product
  apply ParityEven.append_eq_states _ _ Q (ParityEven.put s h A) s m
  · simp [measurementCount_append, ParityEven.moveCached, measurementCount]
  · exact e

theorem evenBodyOdd_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256)
    (hn : (g :: K.wires).Nodup) (he : k % 2 = 0)
    (s : State) (m : List Bool) (hh : s.basis K.high = false) (ha : regValue K.src s.basis = 0)
    (wrap : s.basis K.flag = true → s.basis g = true) :
    run (evenBodyOdd K g k) m (ParityEven.put s K.high (s.basis g && s.basis (lowBit K))) =
      run (entryBodyOdd K g k) m s := by
  obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
    controls_distinct K g hn hw
  have go : g ∉ K.out := controls_fullOut K g hn hw g (by simp [controls]) hgS
  have fo : K.flag ∉ K.out := controls_fullOut K g hn hw K.flag (by simp [controls]) hfS
  have ao : alpha K ∉ K.out := controls_fullOut K g hn hw (alpha K) (by simp [controls]) haS
  have ac : alpha K ∈ K.src := by
    rw [show K.src = lowSrc K ++ [alpha K] from (word_split K.src hw.src).symm]; simp
  have a0 : s.basis (alpha K) = false := (regValue_zero K.src s.basis).mp ha _ ac
  let S := signStageOdd K g k
  have hSign := signStageOdd_correct K g k hn hw s m hh
  have tg : (run S m s).basis g = s.basis g := hSign.2.2.2.2 g go hgH
  have tf : (run S m s).basis K.flag = s.basis K.flag := hSign.2.2.2.2 K.flag fo hfH
  have ts : (run S m s).basis (sign K) = !(s.basis (lowBit K) ^^ s.basis K.flag) := by
    have ne : ¬ k % 2 = 1 := by omega
    simpa only [S, ne, if_false, Bool.xor_false] using hSign.2.2.1
  have product : ((run S m s).basis g && (run S m s).basis (sign K)) =
      ((s.basis g && s.basis (lowBit K)) ^^ (run S m s).basis g ^^ (run S m s).basis K.flag) := by
    rw [tg, tf, ts]
    cases hg : s.basis g <;> cases hb : s.basis (lowBit K) <;>
      cases hf : s.basis K.flag <;> simp_all
  have outA : alpha K ∉ wires S := signStageOdd_outside K g (alpha K) k hw ao hgA.symm hfA.symm hhA.symm
  have E := cached_stage_odd_eq S
    ([.CCX K.flag (sign K) K.high] ++ addClearBetaOdd K g k ++ clearWrapOdd K g k)
    K.high (alpha K) g (sign K) K.flag hhA.symm hgA hfA s m
    (s.basis g && s.basis (lowBit K)) hh a0 outA product
  simpa only [evenBodyOdd, entryBodyOdd, entryMiddleOdd, middleOdd, makeFlags,
    S, List.append_assoc, List.cons_append, List.nil_append] using E

theorem entryEvenOdd_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat) (hw : K.Widths 256)
    (hn : (g :: K.wires).Nodup) (he : k % 2 = 0) (hy : Y < prime) (hk : k < prime)
    (s : State) (m : List Bool) (hY : regValue K.out s.basis = Y) (hs : regValue K.src s.basis = 0)
    (hf : s.basis K.flag = false) (hh : s.basis K.high = false) (hc : s.basis K.cin = false)
    (carry : ∀ q ∈ K.carry, s.basis q = false) :
    run (entryEvenOdd K g k) m s = run (entryOdd K g k) m s := by
  let P : Program := [.CCX g (lowBit K) K.high] ++
    ParityEven.comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag (complement + k)
  let O := ParityCarry.comparePrefixOld g K.src K.out K.carry K.cin K.flag (complement + k)
  let n := measurementCount O
  let t := run O (m.take n) s
  have cmp : measurementCount P = measurementCount O :=
    ParityEven.cached_prefix_measurements K g hw (complement + k)
  have cp : (complement + k) % 2 = 1 := by
    have cmod : complement % 2 = 1 := by norm_num [complement]
    omega
  have cachedRun : run P (m.take n) s =
      ParityEven.put t K.high (s.basis g && s.basis (lowBit K)) :=
    ParityEven.cachedPrefix_after_compute K g hw hn (complement + k) cp s (m.take n) hs hc hh
  have pc : prime + complement = 2 ^ 256 := by norm_num [prime, modulus, complement]
  have initial : FastConst.Frame K s.basis 0 Y false s.basis := ⟨hs, hY, hf, fun _ _ => rfl⟩
  have pre := comparePrefix_correct hn 256 hw s.basis carry hc complement prime k Y pc hk hy s (m.take n) initial
  have oe : O = comparePrefix K g complement k := by
    simp only [O, ParityCarry.comparePrefixOld, ParityCarry.loadNot, ParityCarry.unloadNot,
      comparePrefix, List.append_assoc]
  rw [← oe] at pre
  change t.phase = s.phase ∧ FastConst.Frame K s.basis 0 Y
    (if s.basis g then decide (prime ≤ Y + k) else false) t.basis at pre
  have tg : t.basis g = s.basis g := pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have th : t.basis K.high = false :=
    (pre.2.2.2.2 K.high (FastConst.fixed_not_mutable hn K.high (by simp))).trans hh
  have wrap : t.basis K.flag = true → t.basis g = true := by
    intro hf'; rw [tg]
    have f := pre.2.2.2.1
    cases hg : s.basis g <;> simp_all
  have lb : lowBit K ∈ K.out := by
    obtain ⟨rest, h⟩ := out_shape K hw; rw [h]; simp
  have tv : t.basis (lowBit K) = s.basis (lowBit K) :=
    (regValue_eq_iff K.out t.basis s.basis).mp (pre.2.2.1.trans hY.symm) _ lb
  rw [← tg, ← tv] at cachedRun
  rw [entryOdd, entryCompare_eq_old]
  change run (P ++ evenBodyOdd K g k) m s = run (O ++ entryBodyOdd K g k) m s
  simp only [run_append, cmp]
  change run (evenBodyOdd K g k) (m.drop n) (run P (m.take n) s) =
    run (entryBodyOdd K g k) (m.drop n) t
  rw [cachedRun]
  exact evenBodyOdd_eq K g k hw hn he t (m.drop n) th pre.2.1 wrap

private theorem retain_product_odd (g b f a h : Wire)
    (ga : g ≠ a) (ba : b ≠ a) (fa : f ≠ a) (ha : h ≠ a)
    (s : State) (m n : List Bool) (hh : s.basis h = false)
    (known : s.basis a = (s.basis g && s.basis b)) :
    run [.CX g a, .CX f a, .measureX h [] []] m s =
      ParityEven.put (run [.measureX a [] [.CZ g b]] n s) a
        ((s.basis g && s.basis b) ^^ s.basis g ^^ s.basis f) := by
  rw [erase_and g b a ga ba s n known]
  apply State.extensionality
  · simp [run, measureAndCorrect, correct, ParityEven.put, writeBit, ha, hh]
  funext q
  by_cases qa : q = a
  · subst q
    simp [run, measureAndCorrect, correct, ParityEven.put, writeBit, Function.update,
      ga, fa, ha, ha.symm, known]
  · by_cases qh : q = h
    · subst q
      simp [run, measureAndCorrect, correct, ParityEven.put, writeBit, Function.update, ha, hh]
    · simp [run, measureAndCorrect, correct, ParityEven.put, writeBit, Function.update, qa, qh]

private theorem cleanup_keep_product_odd (K : MeasuredCanonicalModLayout) (g : Wire)
    (hgA : g ≠ alpha K) (hsA : sign K ≠ alpha K) (hfA : K.flag ≠ alpha K)
    (hgH : g ≠ K.high) (hsH : sign K ≠ K.high) (hfH : K.flag ≠ K.high)
    (haH : alpha K ≠ K.high) (s : State) (m n l : List Bool)
    (ha : s.basis (alpha K) = false) (hh : s.basis K.high = false) :
    run [.CX g (alpha K), .CX K.flag (alpha K), .measureX K.high [] []] l
      (run [.measureX K.high [] [.CZ K.flag (sign K)]] n (run (makeFlags K g) m s)) =
      ParityEven.put s (alpha K) ((s.basis g && s.basis (sign K)) ^^ s.basis g ^^ s.basis K.flag) := by
  let t := run (makeFlags K g) m s
  have mf := makeFlags_correct K g hgA hsA hfA haH s m ha hh
  have tg : t.basis g = s.basis g := mf.2.2.2 g hgA hgH
  have tf : t.basis K.flag = s.basis K.flag := mf.2.2.2 _ hfA hfH
  have ts : t.basis (sign K) = s.basis (sign K) := mf.2.2.2 _ hsA hsH
  have beta : t.basis K.high = (t.basis K.flag && t.basis (sign K)) := by rw [mf.2.2.1, tf, ts]
  have erB := erase_and K.flag (sign K) K.high hfH hsH t n beta
  let u : State := ⟨t.phase, writeBit t.basis K.high false⟩
  have keep (q : Wire) (hq : q ≠ K.high) : u.basis q = t.basis q := by simp [u, writeBit, hq]
  have alphaKnown : u.basis (alpha K) = (u.basis g && u.basis (sign K)) := by
    rw [keep _ haH, keep _ hgH, keep _ hsH, mf.2.1, tg, ts]
  have highZero : u.basis K.high = false := by simp [u, writeBit]
  have eraseAll := ExitFusionProof.cleanup_makeFlags_inverse K g hgA hsA hfA hgH hsH hfH haH s m n l ha hh
  change run _ l (run _ n t) = _ at eraseAll ⊢
  rw [erB] at eraseAll ⊢
  have retain := retain_product_odd g (sign K) K.flag (alpha K) K.high
    hgA hsA hfA haH.symm u l l highZero alphaKnown
  change run _ l u = _ at eraseAll ⊢
  rw [retain, eraseAll, keep _ hgH, keep _ hsH, keep _ hfH, tg, ts, tf]

theorem undoMiddleKeepOdd_middleOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m n : List Bool)
    (ha0 : s.basis (alpha K) = false) (hh0 : s.basis K.high = false)
    (hcarry : ∀ q ∈ K.carry.take 254, s.basis q = false) (hcin : s.basis K.cin = false) :
    run (undoMiddleKeepOdd K g k) n (run (middleOdd K g k) m s) =
      ParityEven.put s (alpha K) ((s.basis g && s.basis (sign K)) ^^ s.basis g ^^ s.basis K.flag) := by
  obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
    controls_distinct K g hn hw
  have low := low_widths K hw
  have cs (q : Wire) (h : q ∈ controls K g) : q ∉ lowSrc K := controls_src K g hn hw q h
  have co (q : Wire) (h : q ∈ controls K g) : q ∉ lowOut K := controls_out K g hn hw q h
  have cc (q : Wire) (h : q ∈ controls K g) : q ∉ K.carry.take 254 := carry_away K g hn hw q h
  have hctrlSrc : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowSrc K :=
    fun e he => cs _ ((maskOdd_controls K g k).1 e he)
  have hctrlOut : ∀ e ∈ entryMasksOdd K g k, e.1 ∉ lowOut K :=
    fun e he => co _ ((maskOdd_controls K g k).1 e he)
  have haway : ∀ q ∈ mappedWires (mappedRead (lowSrc K) false),
      q ∉ K.cin :: (lowOut K ++ K.carry.take 254) := by
    simpa only [mappedRead_wires] using src_away K g hn hw
  let M := makeFlags K g
  let T := tableAddOdd K g k
  let E : Program := [.measureX K.high [] [.CZ K.flag (sign K)]]
  obtain ⟨m1, m2, m3, forward⟩ := run_three M T E m s
  have mf := makeFlags_correct K g hgA (Ne.symm haS) hfA (Ne.symm hhA) s m1 ha0 hh0
  let st1 := run M m1 s
  let s2 := run T m2 st1
  let s3 := run E m3 s2
  have frame (q : Wire) (hqa : q ≠ alpha K) (hqh : q ≠ K.high) : st1.basis q = s.basis q :=
    mf.2.2.2 q hqa hqh
  have clean : ∀ q ∈ K.carry.take 254, st1.basis q = false := fun q hq =>
    (frame q (fun e => cc (alpha K) (by simp [controls]) (e ▸ hq))
      (fun e => cc K.high (by simp [controls]) (e ▸ hq))).trans (hcarry q hq)
  have ci : st1.basis K.cin = false := (frame _ hcA (Ne.symm hhC)).trans hcin
  have ad := tableAddOdd_correct K g k (lowSrc_nodup K g hn hw) (adder_nodup K g hn hw)
    haway (by rw [low.1, low.2.1]) (by rw [low.2.2, low.2.1]) hctrlSrc hctrlOut st1 m2 clean ci
  have f2 : s2.basis K.flag = s.basis K.flag :=
    (ad.2.2 _ (co _ (by simp [controls]))).trans (frame _ hfA hfH)
  have sg2 : s2.basis (sign K) = s.basis (sign K) :=
    (ad.2.2 _ (co _ (by simp [controls]))).trans (frame _ (Ne.symm haS) (Ne.symm hhS))
  have beta : s2.basis K.high = (s2.basis K.flag && s2.basis (sign K)) := by
    rw [ad.2.2 _ (co _ (by simp [controls])), mf.2.2.1, f2, sg2]
  let A : Program := [.CCX K.flag (sign K) K.high]
  let B := tableSubOdd K g k
  let C : Program := [.measureX K.high [] [.CZ K.flag (sign K)]]
  let D : Program := [.CX g (alpha K), .CX K.flag (alpha K), .measureX K.high [] []]
  obtain ⟨n1, n2, n3, n4, inverse⟩ := run_four A B C D n s3
  have restore : run A n1 s3 = s2 := ExitFusionProof.recompute_measured_and K.flag (sign K) K.high hfH
    (Ne.symm hhS) s2 m3 n1 beta
  have sub := tableSubOdd_tableAddOdd_inverse K g k (lowSrc_nodup K g hn hw) (adder_nodup K g hn hw)
    haway (by rw [low.1, low.2.1]) (by rw [low.2.2, low.2.1]) hctrlSrc st1 m2 n2 clean ci
  have goal : run (A ++ B ++ C ++ D) n (run (M ++ T ++ E) m s) =
      ParityEven.put s (alpha K) ((s.basis g && s.basis (sign K)) ^^ s.basis g ^^ s.basis K.flag) := by
    rw [forward]
    change run (A ++ B ++ C ++ D) n s3 = _
    rw [inverse, restore, sub]
    exact cleanup_keep_product_odd K g hgA (Ne.symm haS) hfA hgH (Ne.symm hhS) hfH
      (Ne.symm hhA) s m1 n3 n4 ha0 hh0
  simpa only [middleOdd, addClearBetaOdd, undoMiddleKeepOdd, M, T, E, A, B, C, D, List.append_assoc] using goal

theorem undo_entryMiddleKeepOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256) (he : k % 2 = 0)
    (s : State) (m n r : List Bool) (hsrc : regValue K.src s.basis = 0)
    (hh : s.basis K.high = false) (hcin : s.basis K.cin = false)
    (hcarry : ∀ q ∈ K.carry, s.basis q = false) (wrap : s.basis K.flag = true → s.basis g = true) :
    run (signStageOdd K g k).reverse r
      (run (undoMiddleKeepOdd K g k) n (run (entryMiddleOdd K g k) m s)) =
      ParityEven.put s (alpha K) (s.basis g && s.basis (lowBit K)) := by
  obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
    controls_distinct K g hn hw
  have cio : K.cin ∉ K.out := controls_fullOut K g hn hw K.cin (by simp [controls]) hcS
  have go : g ∉ K.out := controls_fullOut K g hn hw g (by simp [controls]) hgS
  have fo : K.flag ∉ K.out := controls_fullOut K g hn hw K.flag (by simp [controls]) hfS
  have am : alpha K ∈ K.src := by
    rw [show K.src = lowSrc K ++ [alpha K] from (word_split K.src hw.src).symm]; simp
  have ao : alpha K ∉ K.out := src_fullOut K g hn _ am
  have a0 : s.basis (alpha K) = false := (regValue_zero K.src s.basis).mp hsrc _ am
  let P := signStageOdd K g k
  have proper := signStageOdd_proper K g k hn hw
  have zero : measurementCount P = 0 := properProgram_measurementCount P proper
  let t := run P [] s
  have first := signStageOdd_correct K g k hn hw s [] hh
  have high : t.basis K.high = false := first.2.2.2.1
  have alphaClean : t.basis (alpha K) = false := (first.2.2.2.2 _ ao (Ne.symm hhA)).trans a0
  have carry : ∀ q ∈ K.carry.take 254, t.basis q = false := fun q hq => by
    have mem := List.mem_of_mem_take hq
    have qh : q ≠ K.high := fun e => carry_away K g hn hw K.high (by simp [controls]) (e ▸ hq)
    exact (first.2.2.2.2 q (carry_fullOut K g hn q mem) qh).trans (hcarry q mem)
  have ci : t.basis K.cin = false := (first.2.2.2.2 _ cio (Ne.symm hhC)).trans hcin
  have mid := undoMiddleKeepOdd_middleOdd_inverse K g k hn hw t m n alphaClean high carry ci
  rw [entryMiddleOdd, run_append, zero, List.take_zero, List.drop_zero, mid]
  have outA : alpha K ∉ wires P.reverse := by
    rw [wires_reverse]
    exact signStageOdd_outside K g (alpha K) k hw ao hgA.symm hfA.symm hhA.symm
  rw [ParityEven.run_put P.reverse r t (alpha K) _ outA, run_reverse_proper P proper s [] r]
  have tg : t.basis g = s.basis g := first.2.2.2.2 g go hgH
  have tf : t.basis K.flag = s.basis K.flag := first.2.2.2.2 K.flag fo hfH
  have ts : t.basis (sign K) = !(s.basis (lowBit K) ^^ s.basis K.flag) := by
    have ne : ¬ k % 2 = 1 := by omega
    simpa only [ne, if_false, Bool.xor_false] using first.2.2.1
  rw [tg, tf, ts]
  congr 1
  cases hg : s.basis g <;> cases hb : s.basis (lowBit K) <;>
    cases hf : s.basis K.flag <;> simp_all

theorem exitEvenOdd_entryOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256) (he : k % 2 = 0)
    (s : State) (m n : List Bool) (hY : regValue K.out s.basis = Y)
    (hy : Y < prime) (hk : k < prime) (hsrc : regValue K.src s.basis = 0)
    (hf : s.basis K.flag = false) (hh : s.basis K.high = false)
    (hcin : s.basis K.cin = false) (hcarry : ∀ q ∈ K.carry, s.basis q = false) :
    run (exitEvenOdd K g k) n (run (entryOdd K g k) m s) = s := by
  have pc : prime + complement = 2 ^ 256 := by norm_num [prime, modulus, complement]
  let m1 := m.take (measurementCount (entryCompare K g complement k))
  let m2 := m.drop (measurementCount (entryCompare K g complement k))
  let t := run (entryCompare K g complement k) m1 s
  have initial : FastConst.Frame K s.basis 0 Y false s.basis := ⟨hsrc, hY, hf, fun _ _ => rfl⟩
  have pre := comparePrefix_correct hn 256 hw s.basis hcarry hcin complement prime k Y pc hk hy s m1 initial
  change t.phase = s.phase ∧ FastConst.Frame K s.basis 0 Y
    (if s.basis g then decide (prime ≤ Y + k) else false) t.basis at pre
  have tg : t.basis g = s.basis g := pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have th : t.basis K.high = false :=
    (pre.2.2.2.2 K.high (FastConst.fixed_not_mutable hn K.high (by simp))).trans hh
  have tcin : t.basis K.cin = false :=
    (pre.2.2.2.2 K.cin (FastConst.fixed_not_mutable hn K.cin (by simp))).trans hcin
  have tcarry : ∀ q ∈ K.carry, t.basis q = false := fun q hq =>
    (pre.2.2.2.2 q (FastConst.fixed_not_mutable hn q (by simp [hq]))).trans (hcarry q hq)
  have tflag : t.basis K.flag = decide (prime ≤ Y + (if t.basis g then k else 0)) := by
    rw [tg]
    have h := pre.2.2.2.1
    cases hg : s.basis g <;> simp [hg, show ¬ prime ≤ Y by omega] at h ⊢ <;> exact h
  have wrap : t.basis K.flag = true → t.basis g = true := by
    intro f; rw [tg]
    have tf := pre.2.2.2.1
    cases G : s.basis g <;> simp_all
  let A := recoverWrapOdd K g k
  let B := undoMiddleKeepOdd K g k
  let C := (signStageOdd K g k).reverse
  let D := ParityEven.eraseInputMoved K g k
  obtain ⟨n1, n2, n3, n4, parts⟩ := run_four A B C D n (run (entryBodyOdd K g k) m2 t)
  have recover : run A n1 (run (entryBodyOdd K g k) m2 t) =
      run (entryMiddleOdd K g k) (m2.take (measurementCount (entryMiddleOdd K g k))) t :=
    recoverWrapOdd_entryBodyOdd K g k Y hn hw t m2 n1 pre.2.2.1 hy hk pre.2.1 th tcin tcarry tflag
  have undo : run C n3 (run B n2
      (run (entryMiddleOdd K g k) (m2.take (measurementCount (entryMiddleOdd K g k))) t)) =
      ParityEven.put t (alpha K) (t.basis g && t.basis (lowBit K)) :=
    undo_entryMiddleKeepOdd_inverse K g k hn hw he t _ n2 n3 pre.2.1 th tcin tcarry wrap
  have erase : run D n4 (ParityEven.put t (alpha K) (t.basis g && t.basis (lowBit K))) = s :=
    (ParityEven.eraseInputMoved_eq K g hw hn k he t n4 pre.2.1 tcin th tcarry).trans
      (ExitFusionProof.eraseInput_entryCompare_inverse K g k Y hn hw s m1 n4 hY hy hk hsrc hf hcin hcarry)
  rw [entryOdd, run_append]
  change run (A ++ B ++ C ++ D) n (run (entryBodyOdd K g k) m2 t) = s
  rw [parts, recover, undo, erase]

theorem entryAllOdd_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hw : K.Widths 256) (hn : (g :: K.wires).Nodup) (hy : Y < prime) (hk : k < prime)
    (s : State) (m : List Bool) (hY : regValue K.out s.basis = Y) (hs : regValue K.src s.basis = 0)
    (hf : s.basis K.flag = false) (hh : s.basis K.high = false) (hc : s.basis K.cin = false)
    (carry : ∀ q ∈ K.carry, s.basis q = false) :
    run (entryAllOdd K g k) m s = run (entryOdd K g k) m s := by
  unfold entryAllOdd
  split_ifs with he
  · exact entryOptOdd_eq K g k hw hn he s m hs hc
  · exact entryEvenOdd_eq K g k Y hw hn (by omega) hy hk s m hY hs hf hh hc carry

theorem exitAllOdd_entryOdd_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m n : List Bool) (hY : regValue K.out s.basis = Y)
    (hy : Y < prime) (hk : k < prime) (hsrc : regValue K.src s.basis = 0)
    (hf : s.basis K.flag = false) (hh : s.basis K.high = false)
    (hcin : s.basis K.cin = false) (hcarry : ∀ q ∈ K.carry, s.basis q = false) :
    run (exitAllOdd K g k) n (run (entryOdd K g k) m s) = s := by
  unfold exitAllOdd
  split_ifs with he
  · exact exitOptOdd_entryOdd_inverse K g k Y hn hw he s m n hY hy hk hsrc hf hh hcin hcarry
  · exact exitEvenOdd_entryOdd_inverse K g k Y hn hw (by omega) s m n hY hy hk hsrc hf hh hcin hcarry

theorem exitAllOdd_field_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k H : Fp)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hH : regValue K.out s.basis = oddWord H)
    (hsrc : regValue K.src s.basis = 0) (hf : s.basis K.flag = false) (hh : s.basis K.high = false)
    (hcin : s.basis K.cin = false) (hcarry : ∀ q ∈ K.carry, s.basis q = false) :
    let v := run (exitAllOdd K g k.val) m s
    v.phase = s.phase ∧ regValue K.out v.basis = (2 * H - (if s.basis g then k else 0)).val ∧
      ∀ q, q ∉ K.out → v.basis q = s.basis q := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let Y : Fp := 2 * H - (if s.basis g then k else 0)
  let b := run (xorConstant K.out (regValue K.out s.basis)) [] s
  have clear := xorConstant_correct K.out (FastConst.out_nodup hn) (regValue K.out s.basis)
    (regValue_lt K.out s.basis) s []
  have yBound : Y.val < 2 ^ K.out.length := by
    rw [hw.out]; exact Y.isLt.trans (by norm_num [p])
  let a := run (xorConstant K.out Y.val) [] b
  have load := xorConstant_correct K.out (FastConst.out_nodup hn) Y.val yBound b []
  have av : regValue K.out a.basis = Y.val := by rw [load.2.2, clear.2.2]; simp
  have ap : a.phase = s.phase := load.1.trans clear.1
  have outside (q : Wire) (hq : q ∉ K.out) : a.basis q = s.basis q :=
    (load.2.1 q hq).trans (clear.2.1 q hq)
  have aSrc : regValue K.src a.basis = 0 := by
    rw [regValue_congr _ _ _ (fun q hq => outside q (src_fullOut K g hn q hq)), hsrc]
  have fixedOutside (q : Wire) (hq : q ∈ K.carry ++ [K.high, K.cin]) : q ∉ K.out := fun bad =>
    FastConst.fixed_not_mutable hn q hq (by simp [FastConst.mutable, bad])
  have af : a.basis K.flag = false := (outside _ (FastConst.flag_not_out hn)).trans hf
  have ah : a.basis K.high = false := (outside _ (fixedOutside _ (by simp))).trans hh
  have ac : a.basis K.cin = false := (outside _ (fixedOutside _ (by simp))).trans hcin
  have aCarry : ∀ q ∈ K.carry, a.basis q = false :=
    fun q hq => (outside q (fixedOutside q (by simp [hq]))).trans (hcarry q hq)
  have ag : a.basis g = s.basis g := outside g (FastConst.g_not_out hn)
  have fwd := entryOdd_field_correct K g k Y hn hw a [] av aSrc af ah ac aCarry
  have math : (Y + (if a.basis g then k else 0)) / 2 = H := by
    rw [ag]
    dsimp only [Y]
    rw [sub_add_cancel]
    have two : (2 : Fp) ≠ 0 := by decide
    field_simp
  have preimage : run (entryOdd K g k.val) [] a = s := by
    apply State.extensionality
    · exact fwd.1.trans ap
    · funext q
      by_cases hq : q ∈ K.out
      · have val : regValue K.out (run (entryOdd K g k.val) [] a).basis = regValue K.out s.basis := by
          rw [fwd.2.1, math, hH]
        exact (regValue_eq_iff _ _ _).mp val q hq
      · exact (fwd.2.2 q hq).trans (outside q hq)
  have hy : Y.val < prime := by rw [prime_eq_secp]; exact Y.isLt
  have hk : k.val < prime := by rw [prime_eq_secp]; exact k.isLt
  have inv := exitAllOdd_entryOdd_inverse K g k.val Y.val hn hw a [] m av hy hk aSrc af ah ac aCarry
  rw [preimage] at inv
  dsimp only
  rw [inv]
  exact ⟨ap, av, outside⟩

theorem exitAllOdd_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k H : Fp)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256) (s : State) (m n : List Bool)
    (hH : regValue K.out s.basis = oddWord H) (hs : regValue K.src s.basis = 0)
    (hf : s.basis K.flag = false) (hh : s.basis K.high = false) (hc : s.basis K.cin = false)
    (carry : ∀ q ∈ K.carry, s.basis q = false) :
    run (exitAllOdd K g k.val) m s = run (exitOdd K g k.val) n s := by
  have a := exitAllOdd_field_correct K g k H hn hw s m hH hs hf hh hc carry
  have b := exitOdd_field_correct K g k H hn hw s n hH hs hf hh hc carry
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · funext q
    by_cases hq : q ∈ K.out
    · exact (regValue_eq_iff K.out _ _).mp (a.2.1.trans b.2.1.symm) q hq
    · exact (a.2.2 q hq).trans (b.2.2 q hq).symm

-- Resource certificates for `entryAllOdd` and `exitAllOdd`

theorem entryAllOdd_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) :
    toffoliCount (entryAllOdd K g k) = 765 ∧ measurementCount (entryAllOdd K g k) = 767 ∧
      Challenge.gateSlots (entryAllOdd K g k) ≤ 25000 := by
  have base := entryOdd_counts K g k hw
  have bSlots := entryOdd_gateSlots_le K g k hw
  have hSplit : entryOdd K g k =
      ParityCarry.comparePrefixOld g K.src K.out K.carry K.cin K.flag (complement + k) ++
        entryBodyOdd K g k := by
    rw [entryOdd, entryCompare_eq_old]
  have hBT := congrArg toffoliCount hSplit
  have hBM := congrArg measurementCount hSplit
  have hBS := congrArg Challenge.gateSlots hSplit
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append] at hBT hBM hBS
  unfold entryAllOdd
  split_ifs
  · have d := ParityConvert.compare_layout_counts K g hw (complement + k)
    simp only [entryOptOdd, toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
    omega
  · have c := ParityEven.cached_layout_counts K g hw (complement + k)
    dsimp only at c
    have eb : toffoliCount (evenBodyOdd K g k) + 1 = toffoliCount (entryBodyOdd K g k) ∧
        measurementCount (evenBodyOdd K g k) = measurementCount (entryBodyOdd K g k) ∧
        Challenge.gateSlots (evenBodyOdd K g k) = Challenge.gateSlots (entryBodyOdd K g k) + 4 := by
      simp only [evenBodyOdd, entryBodyOdd, entryMiddleOdd, middleOdd, makeFlags,
        toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
      simp only [ParityEven.moveCached, toffoliCount, measurementCount, Challenge.gateSlots,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Challenge.instructionSlots]
      omega
    simp only [entryEvenOdd, toffoliCount_append, measurementCount_append, Challenge.gateSlots_append] at c ⊢
    omega

theorem exitAllOdd_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) :
    toffoliCount (exitAllOdd K g k) = 765 ∧ measurementCount (exitAllOdd K g k) = 766 ∧
      Challenge.gateSlots (exitAllOdd K g k) ≤ 25000 := by
  have base := exitOdd_counts K g k hw
  have bSlots := exitOdd_gateSlots_le K g k hw
  have hSplit : exitOdd K g k =
      recoverWrapOdd K g k ++ undoMiddleOdd K g k ++ (signStageOdd K g k).reverse ++
        ExitFusionResearch.eraseInputWrap K g complement k := rfl
  have hBT := congrArg toffoliCount hSplit
  have hBM := congrArg measurementCount hSplit
  have hBS := congrArg Challenge.gateSlots hSplit
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append] at hBT hBM hBS
  unfold exitAllOdd
  split_ifs
  · have d := ParityConvert.erase_layout_counts K g hw (complement + k)
    rw [← ParityConvert.old_erase_split K g k] at d
    simp only [exitOptOdd, toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
    omega
  · have d := ParityEven.eraseInputMoved_counts K g hw k
    have um : toffoliCount (undoMiddleKeepOdd K g k) = toffoliCount (undoMiddleOdd K g k) ∧
        measurementCount (undoMiddleKeepOdd K g k) = measurementCount (undoMiddleOdd K g k) ∧
        Challenge.gateSlots (undoMiddleKeepOdd K g k) = Challenge.gateSlots (undoMiddleOdd K g k) + 1 := by
      simp only [undoMiddleKeepOdd, undoMiddleOdd, toffoliCount_append, measurementCount_append,
        Challenge.gateSlots_append]
      simp [toffoliCount, measurementCount, Challenge.gateSlots, Challenge.instructionSlots]
    simp only [exitEvenOdd, toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
    omega

theorem entryAllOdd_wires (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) :
    wires (entryAllOdd K g k) ⊆ wires (EntryFuse.entry K g complement k) := by
  have hBase := entryOdd_wires K g k hw
  have hSplit : entryOdd K g k =
      ParityCarry.comparePrefixOld g K.src K.out K.carry K.cin K.flag (complement + k) ++
        entryBodyOdd K g k := by
    rw [entryOdd, entryCompare_eq_old]
  refine Finset.Subset.trans ?_ hBase
  unfold entryAllOdd
  split_ifs
  · rw [hSplit]
    simp only [entryOptOdd, wires_append]
    exact Finset.union_subset_union (ParityConvert.compare_layout_wires K g hw (complement + k))
      (Finset.Subset.refl _)
  · rw [hSplit]
    have hP := ParityEven.compareCached_layout_wires K g hw (complement + k)
    have hMove : wires (ParityEven.moveCached K.high (alpha K)) ⊆ wires (makeFlags K g) := by
      intro q hq
      simp only [ParityEven.moveCached, makeFlags, wires, Instr.wires, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hq ⊢
      itauto
    have hFlags : wires [.CX g (alpha K), .CX K.flag (alpha K), .CCX K.flag (sign K) K.high] ⊆
        wires (makeFlags K g) := by
      intro q hq
      simp only [makeFlags, wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.notMem_empty, or_false] at hq ⊢
      itauto
    have hBody : wires (evenBodyOdd K g k) ⊆ wires (entryBodyOdd K g k) := by
      simp only [evenBodyOdd, entryBodyOdd, entryMiddleOdd, middleOdd, wires_append]
      intro q hq
      have hm := hMove (a := q)
      have hf := hFlags (a := q)
      simp only [Finset.mem_union] at hq hm hf ⊢
      itauto
    have hCtrl : ({g, lowBit K, K.high} : Finset Wire) ⊆ wires (entryBodyOdd K g k) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      simp only [entryBodyOdd, entryMiddleOdd, signStageOdd, ExitFusionResearch.signStage,
        ExitFusionResearch.lowBit, middleOdd, makeFlags, wires_append, wires, Instr.wires,
        Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false]
      change q = g ∨ q = K.out.headD 0 ∨ q = K.high at hq
      itauto
    simp only [entryEvenOdd, wires_append]
    intro q hq
    have hp := hP (a := q)
    have hb := hBody (a := q)
    have hc := hCtrl (a := q)
    have hpre : q ∈ wires [.CCX g (lowBit K) K.high] → q ∈ wires (entryBodyOdd K g k) := by
      intro h; apply hCtrl
      simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, or_false] at h ⊢
      rcases h with rfl | rfl | rfl <;> simp
    have hhi : q = K.high → q ∈ wires (entryBodyOdd K g k) := fun e => hCtrl (by simp [e])
    simp only [Finset.mem_union, Finset.mem_singleton] at hq hp hb ⊢
    itauto

theorem exitAllOdd_wires (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) :
    wires (exitAllOdd K g k) ⊆ wires (ExitFusionResearch.exit K g complement k) := by
  have hBase := exitOdd_wires K g k
  refine Finset.Subset.trans ?_ hBase
  unfold exitAllOdd
  split_ifs
  · have hE := ParityConvert.erase_layout_wires K g hw (complement + k)
    rw [← ParityConvert.old_erase_split K g k] at hE
    simp only [exitOptOdd, exitOdd, wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _) hE
  · have hE := ParityEven.eraseInputMoved_wires K g k hw
    have hTail : wires [.measureX K.high [] [.CZ K.flag (sign K)],
        .CX g (alpha K), .CX K.flag (alpha K), .measureX K.high [] []] ⊆
        wires [.measureX K.high [] [.CZ K.flag (sign K)],
          .measureX (alpha K) [] [.CZ g (sign K)]] := by
      intro q hq
      simp only [wires, Instr.wires, correctionWires, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.notMem_empty, or_false] at hq ⊢
      itauto
    have hU : wires (undoMiddleKeepOdd K g k) ⊆ wires (undoMiddleOdd K g k) := by
      simp only [undoMiddleKeepOdd, undoMiddleOdd, wires_append]
      exact Finset.union_subset_union (Finset.Subset.refl _) hTail
    have hAH : ({alpha K, K.high} : Finset Wire) ⊆ wires (undoMiddleOdd K g k) := by
      intro q hq
      simp only [undoMiddleOdd, wires_append, wires, Instr.wires, correctionWires,
        Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hq ⊢
      rcases hq with rfl | rfl <;> simp
    simp only [exitEvenOdd, exitOdd, wires_append]
    intro q hq
    have he := hE (a := q)
    have hu := hU (a := q)
    have ha := hAH (a := q)
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq he hu ha ⊢
    itauto

theorem entryAllOdd_support (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) : wires (entryAllOdd K g k) ⊆ (g :: K.wires).toFinset :=
  (entryAllOdd_wires K g k hw).trans (EntryFuse.entry_support K g complement k hw)

theorem exitAllOdd_support (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) : wires (exitAllOdd K g k) ⊆ (g :: K.wires).toFinset :=
  (exitAllOdd_wires K g k hw).trans (ExitFusionResearch.exit_support K g complement k hw)

theorem entryAllOdd_physical (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256) : GatePhysical (entryAllOdd K g k) := by
  have old := entryOdd_physical K g k hn hw
  rw [entryOdd, entryCompare_eq_old, gatePhysical_append] at old
  unfold entryAllOdd
  split_ifs
  · simp only [entryOptOdd, gatePhysical_append]
    exact ⟨ParityConvert.compare_layout_physical K g hw (complement + k) old.1, old.2⟩
  · obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
      controls_distinct K g hn hw
    have go : g ∉ K.out := controls_fullOut K g hn hw g (by simp [controls]) hgS
    have ho : K.high ∉ K.out := controls_fullOut K g hn hw K.high (by simp [controls]) hhS
    have lb : lowBit K ∈ K.out := by obtain ⟨rest, h⟩ := out_shape K hw; rw [h]; simp
    have gl : g ≠ lowBit K := fun e => go (e ▸ lb)
    have lh : lowBit K ≠ K.high := fun e => ho (e ▸ lb)
    have pre : GatePhysical [.CCX g (lowBit K) K.high] := by
      simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, gl, hgH, lh]
    have move : GatePhysical (ParityEven.moveCached K.high (alpha K)) := by
      simp [ParityEven.moveCached, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hhA, hhA.symm]
    have flags : GatePhysical [.CX g (alpha K), .CX K.flag (alpha K), .CCX K.flag (sign K) K.high] := by
      simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hgA, hfA, hfS, hfH, hhS.symm]
    have hBody := old.2
    simp only [entryBodyOdd, entryMiddleOdd, middleOdd, gatePhysical_append] at hBody
    simp only [entryEvenOdd, evenBodyOdd, gatePhysical_append]
    exact ⟨⟨pre, ParityEven.compareCached_layout_physical K g hw hn (complement + k) old.1⟩,
      ⟨⟨⟨⟨move, hBody.1.1⟩, flags⟩, hBody.1.2.2⟩, hBody.2⟩⟩

theorem exitAllOdd_physical (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g :: K.wires).Nodup) (hw : K.Widths 256) : GatePhysical (exitAllOdd K g k) := by
  have old := exitOdd_physical K g k hn hw
  simp only [exitOdd, gatePhysical_append] at old
  unfold exitAllOdd
  split_ifs
  · have hE := old.2
    rw [ParityConvert.old_erase_split K g k] at hE
    simp only [exitOptOdd, gatePhysical_append]
    exact ⟨old.1, ParityConvert.erase_layout_physical K g hw (complement + k) hE⟩
  · obtain ⟨hgF, hgH, hgC, hgA, hgS, hfH, hfC, hfA, hfS, hhC, hhA, hhS, hcA, hcS, haS⟩ :=
      controls_distinct K g hn hw
    have tail : GatePhysical [.measureX K.high [] [.CZ K.flag (sign K)],
        .CX g (alpha K), .CX K.flag (alpha K), .measureX K.high [] []] := by
      simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate,
        hfH, hfH.symm, hfS, hfS.symm, hhS, hhS.symm, hgA, hfA]
    have hU := old.1.1.2
    simp only [undoMiddleOdd, gatePhysical_append] at hU
    simp only [exitEvenOdd, undoMiddleKeepOdd, gatePhysical_append]
    exact ⟨⟨⟨old.1.1.1, ⟨hU.1, tail⟩⟩, old.1.2⟩,
      ParityEven.eraseInputMoved_physical K g k hn hw old.2⟩

-- ============================================================================
-- Section 8: ControlledPointLayout entry/exit wrappers (`entryYAllOdd`, `exitYAllOdd`)
-- ============================================================================

def entryYAllOdd (L : ControlledPointLayout) (k : Fp) : Program :=
  entryAllOdd (ParityConvert.yLayout L) L.core.generic k.val

def exitYAllOdd (L : ControlledPointLayout) (k : Fp) : Program :=
  exitAllOdd (ParityConvert.yLayout L) L.core.generic k.val

theorem entryYAllOdd_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y k : Fp) (s : State) (m : List Bool) (hY : regValue L.point.y s.basis = Y.val)
    (hc : regValue L.dialogPool s.basis = 0) :
    let v := run (entryYAllOdd L k) m s
    v.phase = s.phase ∧
      regValue L.point.y v.basis = oddWord ((Y + (if s.basis L.core.generic then k else 0)) / 2) ∧
      ∀ q, q ∉ L.point.y → v.basis q = s.basis q := by
  let K := ParityConvert.yLayout L
  have aux := ParityConvert.y_aux_clean L hw s hc
  have sz : regValue K.src s.basis = 0 := (regValue_zero _ _).mpr (fun q hq => aux q (by simp [K, hq]))
  have hy : Y.val < prime := by rw [prime_eq_secp]; exact Y.isLt
  have hk : k.val < prime := by rw [prime_eq_secp]; exact k.isLt
  have hW := L.recoveryConstant_widths hw L.point.y hw.inputY
  have hN := L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)
  have hEq := entryAllOdd_eq K L.core.generic k.val Y.val hW hN hy hk s m hY sz
    (aux _ (by simp [K])) (aux _ (by simp [K])) (aux _ (by simp [K]))
    (fun q hq => aux q (by simp [K, hq]))
  have hFld := entryOdd_field_correct K L.core.generic k Y hN hW s m hY sz
    (aux _ (by simp [K])) (aux _ (by simp [K])) (aux _ (by simp [K]))
    (fun q hq => aux q (by simp [K, hq]))
  dsimp only
  rw [show entryYAllOdd L k = entryAllOdd K L.core.generic k.val from rfl, hEq]
  exact hFld

theorem exitYAllOdd_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y k : Fp) (s : State) (m : List Bool) (hY : regValue L.point.y s.basis = oddWord Y)
    (hc : regValue L.dialogPool s.basis = 0) :
    let v := run (exitYAllOdd L k) m s
    v.phase = s.phase ∧
      regValue L.point.y v.basis = (2 * Y - (if s.basis L.core.generic then k else 0)).val ∧
      ∀ q, q ∉ L.point.y → v.basis q = s.basis q := by
  let K := ParityConvert.yLayout L
  have aux := ParityConvert.y_aux_clean L hw s hc
  have sz : regValue K.src s.basis = 0 := (regValue_zero _ _).mpr (fun q hq => aux q (by simp [K, hq]))
  have hW := L.recoveryConstant_widths hw L.point.y hw.inputY
  have hN := L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)
  exact exitAllOdd_field_correct K L.core.generic k Y hN hW s m hY sz
    (aux _ (by simp [K])) (aux _ (by simp [K])) (aux _ (by simp [K]))
    (fun q hq => aux q (by simp [K, hq]))

theorem entryYAllOdd_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (entryYAllOdd L k) = 765 ∧ measurementCount (entryYAllOdd L k) = 767 ∧
      Challenge.gateSlots (entryYAllOdd L k) ≤ 25000 :=
  entryAllOdd_counts (ParityConvert.yLayout L) L.core.generic k.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYAllOdd_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (exitYAllOdd L k) = 765 ∧ measurementCount (exitYAllOdd L k) = 766 ∧
      Challenge.gateSlots (exitYAllOdd L k) ≤ 25000 :=
  exitAllOdd_counts (ParityConvert.yLayout L) L.core.generic k.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem entryYAllOdd_wires (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryYAllOdd L k) ⊆ wires (EntryFuse.fusedY L k) :=
  entryAllOdd_wires (ParityConvert.yLayout L) L.core.generic k.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYAllOdd_wires (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (exitYAllOdd L k) ⊆ wires (ExitFusionResearch.exitY L k) :=
  exitAllOdd_wires (ParityConvert.yLayout L) L.core.generic k.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem entryYAllOdd_support (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryYAllOdd L k) ⊆ (L.core.generic :: (L.recoveryConstant L.point.y).wires).toFinset :=
  entryAllOdd_support (ParityConvert.yLayout L) L.core.generic k.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYAllOdd_support (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (exitYAllOdd L k) ⊆ (L.core.generic :: (L.recoveryConstant L.point.y).wires).toFinset :=
  exitAllOdd_support (ParityConvert.yLayout L) L.core.generic k.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem entryYAllOdd_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (entryYAllOdd L k) :=
  entryAllOdd_physical (ParityConvert.yLayout L) L.core.generic k.val
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl))
    (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYAllOdd_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (exitYAllOdd L k) :=
  exitAllOdd_physical (ParityConvert.yLayout L) L.core.generic k.val
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl))
    (L.recoveryConstant_widths hw L.point.y hw.inputY)

private theorem masksOdd_slots_le (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) :
    Challenge.gateSlots (tableOdd K g k) + Challenge.gateSlots (untabledOdd K g k) +
      Challenge.gateSlots (thresholdOdd K g k) + Challenge.gateSlots (unthresholdOdd K g k) ≤ 3570 := by
  have a := Baselines.maskedConstant_gateSlots_le (sign K) (lowSrc K) offsetOdd
  have b := Baselines.maskedConstant_gateSlots_le g (lowSrc K) (k / 2)
  have d := Baselines.maskedConstant_gateSlots_le (alpha K) (lowSrc K)
    (Nat.xor (Nat.xor offsetOdd (k / 2)) ((k + 1) / 2 + offsetOdd))
  have e := Baselines.maskedConstant_gateSlots_le K.flag (lowSrc K)
    (Nat.xor (k / 2) ((k + 1) / 2 + offsetOdd))
  have f := Baselines.maskedConstant_gateSlots_le K.high (lowSrc K)
    (Nat.xor (k / 2 + complement) (k / 2))
  have t := Baselines.maskedConstant_gateSlots_le (alpha K) (lowSrc K)
    (Nat.xor (k / 2) ((k + 1) / 2 + offsetOdd))
  have low := (low_widths K hw).1
  simp only [low] at a b d e f t
  simp only [tableOdd, untabledOdd, thresholdOdd, unthresholdOdd, Challenge.gateSlots_append]
  omega

theorem entryAllOdd_slots_vs_entryAll (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) :
    Challenge.gateSlots (entryAllOdd K g k) ≤
      Challenge.gateSlots (ParityUniform.entryAll K g k) + 3572 := by
  have hm := masksOdd_slots_le K g k hw
  have hout : K.out = lowBit K :: K.out.tail := by
    obtain ⟨rest, h⟩ := out_shape K hw; rw [h]; rfl
  have eqS := ExitFusionProof.signStage_eq K g k K.out.tail hout
  unfold entryAllOdd ParityUniform.entryAll
  split_ifs with hk
  · simp only [entryOptOdd, ParityConvert.entryOpt, hk, if_true,
      entryBodyOdd, entryMiddleOdd, signStageOdd, middleOdd, addClearBetaOdd, tableAddOdd, clearWrapOdd,
      entryBody, entryMiddle, middle, addClearBeta, tableAdd, clearWrap, eqS,
      Challenge.gateSlots_append, Baselines.gateSlots_cons, Baselines.gateSlots_nil,
      Challenge.instructionSlots]
    omega
  · simp only [entryEvenOdd, ParityEven.entryEven, evenBodyOdd, ParityEven.evenBody,
      signStageOdd, addClearBetaOdd, tableAddOdd, clearWrapOdd,
      addClearBeta, tableAdd, clearWrap,
      Challenge.gateSlots_append, Baselines.gateSlots_cons, Baselines.gateSlots_nil,
      Challenge.instructionSlots]
    omega

theorem exitAllOdd_slots_vs_exitAll (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) :
    Challenge.gateSlots (exitAllOdd K g k) ≤
      Challenge.gateSlots (ParityUniform.exitAll K g k) + 3572 := by
  have hm := masksOdd_slots_le K g k hw
  unfold exitAllOdd ParityUniform.exitAll
  split_ifs with hk
  · simp only [exitOptOdd, ParityConvert.exitOpt, ParityConvert.eraseInputOpt, hk, if_true,
      recoverWrapOdd, undoMiddleOdd, tableSubOdd, signStageOdd, ExitFusionResearch.slots_reverse,
      ExitFusionResearch.recoverWrap, ExitFusionResearch.undoMiddle,
      ExitFusionResearch.lowSrc, ExitFusionResearch.lowOut, ExitFusionResearch.sign, ExitFusionResearch.alpha,
      lowSrc, lowOut, sign, alpha,
      Challenge.gateSlots_append, Baselines.gateSlots_cons, Baselines.gateSlots_nil,
      Challenge.instructionSlots, List.length_cons, List.length_nil]
    omega
  · simp only [exitEvenOdd, ParityEven.exitEven, recoverWrapOdd, undoMiddleKeepOdd, tableSubOdd,
      signStageOdd, ExitFusionResearch.slots_reverse,
      ExitFusionResearch.recoverWrap, ParityEven.undoMiddleKeep,
      ExitFusionResearch.lowSrc, ExitFusionResearch.lowOut, ExitFusionResearch.sign, ExitFusionResearch.alpha,
      lowSrc, lowOut, sign, alpha,
      Challenge.gateSlots_append, Baselines.gateSlots_cons, Baselines.gateSlots_nil,
      Challenge.instructionSlots, List.length_cons, List.length_nil]
    omega

theorem entryYAllOdd_slots_vs_entryYAll (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    Challenge.gateSlots (entryYAllOdd L k) ≤
      Challenge.gateSlots (ParityUniform.entryYAll L k) + 3572 :=
  entryAllOdd_slots_vs_entryAll (ParityConvert.yLayout L) L.core.generic k.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYAllOdd_slots_vs_exitYAll (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    Challenge.gateSlots (exitYAllOdd L k) ≤
      Challenge.gateSlots (ParityUniform.exitYAll L k) + 3572 :=
  exitAllOdd_slots_vs_exitAll (ParityConvert.yLayout L) L.core.generic k.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)

end ECDSAAdd.Entrant.EntryFuseOdd
end

end
-- ==== end OddEntryExit ====

-- ==== begin OddPhaseBBridge ====
section

/-!
# Odd-Word Outer Entry/Exit & Kernel-Contract Bridge

Standalone bridge module connecting `EntryFuseOdd` (`entryYAllOdd`, `exitYAllOdd`) to the
outer point-addition dialog (`PointDialogValues`, `Stair44PointMap`, `E1QubitPlacement`),
and lifting odd-word division/multiplication kernel contracts (`EntryCorrectOdd`,
`ExitMatchesOdd`) back to exact canonical `PointDialogValues` at the dialog boundary.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

section

namespace ECDSAAdd.Entrant.OddOuterBridge

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField Baselines
open ControlledPointLayout CompressedPointDialog CompressedAllocation CompressedFieldSupport
open DirectSkywalk EntryFuse EntryFuseFinite ExitFusionResearch
open ParityUniform FlagEntry FlagExit ParityEven ParityXEntry Stair44PointMap
open EntryFuseOdd

attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical

/-! ## Section 1: Outer Y Support, Resource Counts, and Outer Routing -/

theorem pk_not_Y_odd (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Fp) (hg : pkW L ≠ L.core.generic) :
    pkW L ∉ wires (entryYAllOdd L k) := by
  intro h
  have sub := (entryYAllOdd_wires L hw k).trans (EntryFuse.fusedY_support L hw k)
  have h2 := Finset.mem_of_subset sub h
  rcases List.mem_cons.mp (List.mem_toFinset.mp h2) with e | e
  · exact hg e
  · exact FlagEntry.pk_not_K L hw hn e

theorem pk_not_exitY_odd (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Fp) (hg : pkW L ≠ L.core.generic) :
    pkW L ∉ wires (exitYAllOdd L k) := by
  intro h
  have sub := (exitYAllOdd_wires L hw k).trans (ExitFusionResearch.exitY_support L hw k)
  have h2 := Finset.mem_of_subset sub h
  rcases List.mem_cons.mp (List.mem_toFinset.mp h2) with e | e
  · exact hg e
  · exact FlagEntry.pk_not_K L hw hn e

theorem entryYAllOdd_tc_eq (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (entryYAllOdd L k) = toffoliCount (entryYAll L k) := by
  have h1 := (entryYAllOdd_counts L hw k).1
  have h2 := (entryYAll_counts L hw k).1
  omega

theorem entryYAllOdd_mc_eq (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    measurementCount (entryYAllOdd L k) = measurementCount (entryYAll L k) := by
  have h1 := (entryYAllOdd_counts L hw k).2.1
  have h2 := (entryYAll_counts L hw k).2.1
  omega

theorem exitYAllOdd_tc_eq (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (exitYAllOdd L k) = toffoliCount (exitYAll L k) := by
  have h1 := (exitYAllOdd_counts L hw k).1
  have h2 := (exitYAll_counts L hw k).1
  omega

theorem exitYAllOdd_mc_eq (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    measurementCount (exitYAllOdd L k) = measurementCount (exitYAll L k) := by
  have h1 := (exitYAllOdd_counts L hw k).2.1
  have h2 := (exitYAll_counts L hw k).2.1
  omega

theorem outerY_slots_delta (cy : Fp) :
    gateSlots (encodeY (entryYAllOdd layout (-cy))) + gateSlots (encodeY (exitYAllOdd layout cy)) ≤
      gateSlots (encodeY (entryYAll layout (-cy))) + gateSlots (encodeY (exitYAll layout cy)) + 7144 := by
  have h1 := entryYAllOdd_slots_vs_entryYAll layout layout_widths (-cy)
  have h2 := exitYAllOdd_slots_vs_exitYAll layout layout_widths cy
  simp only [encodeY, rename_gateSlots]
  omega

private def poolSite (q : Wire) : Prop := q ∈ layout.dialogPool ∧ q ≠ pkW layout
private theorem yPairs_poolSite : ∀ ab ∈ yPairs, poolSite ab.1 ∧ poolSite ab.2 := by
  unfold poolSite; decide +kernel

private theorem yClean_of_dialogPool (v : State) (flag : Bool)
    (clean : regValue layout.dialogPool v.basis = 0) :
    YClean (put v (pkW layout) flag) := by
  intro ab hab
  have c (q : Wire) (ok : poolSite q) : (put v (pkW layout) flag).basis q = false := by
    have z := (regValue_zero _ _).mp clean q ok.1
    simpa [put, writeBit, Function.update_apply, ok.2] using z
  exact ⟨c _ (yPairs_poolSite ab hab).1, c _ (yPairs_poolSite ab hab).2⟩

private theorem dialogPool_of_keep (s v : State) (clean : regValue layout.dialogPool s.basis = 0)
    (keep : ∀ q, q ∉ layout.point.y → v.basis q = s.basis q) :
    regValue layout.dialogPool v.basis = 0 :=
  (regValue_congr _ _ _ (fun q hq =>
    keep q (((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).2))).trans clean

private theorem flag_away : pkW layout ≠ layout.core.generic := by decide +kernel

theorem outerY_entry_odd (Y k : Fp) (s actual : State) (m : List Bool) (flag : Bool)
    (hy : regValue layout.point.y s.basis = Y.val) (clean : regValue layout.dialogPool s.basis = 0)
    (input : pullState outer actual = put s (pkW layout) flag) :
    pullState outer (run (encodeY (entryYAllOdd layout k)) m actual) =
      run (entryYAllOdd layout k) m (put s (pkW layout) flag) := by
  apply y_round _ actual _ m input (yClean_of_dialogPool s flag clean)
  rw [run_put _ _ _ _ _ (pk_not_Y_odd layout layout_widths layout_nodup k flag_away)]
  have fy := entryYAllOdd_correct layout layout_widths layout_nodup Y k s m hy clean
  exact yClean_of_dialogPool _ flag (dialogPool_of_keep _ _ clean fy.2.2)

theorem outerY_exit_odd (Y k : Fp) (s actual : State) (m : List Bool) (flag : Bool)
    (hy : regValue layout.point.y s.basis = oddWord Y) (clean : regValue layout.dialogPool s.basis = 0)
    (input : pullState outer actual = put s (pkW layout) flag) :
    pullState outer (run (encodeY (exitYAllOdd layout k)) m actual) =
      run (exitYAllOdd layout k) m (put s (pkW layout) flag) := by
  apply y_round _ actual _ m input (yClean_of_dialogPool s flag clean)
  rw [run_put _ _ _ _ _ (pk_not_exitY_odd layout layout_widths layout_nodup k flag_away)]
  have fy := exitYAllOdd_correct layout layout_widths layout_nodup Y k s m hy clean
  exact yClean_of_dialogPool _ flag (dialogPool_of_keep _ _ clean fy.2.2)

/-- Running `exitYAllOdd` on an odd-word state produces the exact same state as running
    `exitYAll` on the matching center-word state (both with `pkW L` set to `flag`). -/
theorem exitYAllOdd_rejoin (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y k : Fp) (sOdd sStd : State) (m : List Bool) (flag : Bool)
    (hg : pkW L ≠ L.core.generic)
    (hPhase : sOdd.phase = sStd.phase)
    (hOut : ∀ q, q ∉ L.point.y → sOdd.basis q = sStd.basis q)
    (hYOdd : regValue L.point.y sOdd.basis = oddWord Y)
    (hYStd : regValue L.point.y sStd.basis = centerWord Y)
    (hClean : regValue L.dialogPool sStd.basis = 0) :
    run (exitYAllOdd L k) m (put sOdd (pkW L) flag) =
      run (exitYAll L k) m (put sStd (pkW L) flag) := by
  have hCleanOdd : regValue L.dialogPool sOdd.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq =>
      hOut q (((E1QubitPlacement.lay L hw hn q).2.1 hq).2))).trans hClean
  rw [run_put _ _ _ _ _ (pk_not_exitY_odd L hw hn k hg),
      run_put _ _ _ _ _ (FlagExit.pk_not_exitY L hw hn k hg),
      exitYAll_eq L hw hn Y k sStd m m hYStd hClean]
  have hOdd := exitYAllOdd_correct L hw hn Y k sOdd m hYOdd hCleanOdd
  have hStd := ExitFusionResearch.exitY_correct L hw hn Y k sStd m hYStd hClean
  have hG : sOdd.basis L.core.generic = sStd.basis L.core.generic :=
    hOut _ (((E1QubitPlacement.lay L hw hn _).2.2 rfl).2)
  congr 1
  apply State.extensionality
  · exact hOdd.1.trans (hPhase.trans hStd.1.symm)
  · funext q
    by_cases hq : q ∈ L.point.y
    · have hEq : regValue L.point.y (run (exitYAllOdd L k) m sOdd).basis =
          regValue L.point.y (run (ExitFusionResearch.exitY L k) m sStd).basis := by
        rw [hOdd.2.1, hStd.2.1, hG]
      exact (regValue_eq_iff _ _ _).mp hEq q hq
    · exact (hOdd.2.2 q hq).trans ((hOut q hq).trans (hStd.2.2 q hq).symm)

theorem outerY_exit_rejoin (Y k : Fp) (sOdd sStd actual : State) (m : List Bool) (flag : Bool)
    (hPhase : sOdd.phase = sStd.phase)
    (hOut : ∀ q, q ∉ layout.point.y → sOdd.basis q = sStd.basis q)
    (hYOdd : regValue layout.point.y sOdd.basis = oddWord Y)
    (hYStd : regValue layout.point.y sStd.basis = centerWord Y)
    (hClean : regValue layout.dialogPool sStd.basis = 0)
    (input : pullState outer actual = put sOdd (pkW layout) flag) :
    pullState outer (run (encodeY (exitYAllOdd layout k)) m actual) =
      run (exitYAll layout k) m (put sStd (pkW layout) flag) := by
  have hCleanOdd : regValue layout.dialogPool sOdd.basis = 0 :=
    dialogPool_of_keep sStd sOdd hClean hOut
  rw [outerY_exit_odd Y k sOdd actual m flag hYOdd hCleanOdd input]
  exact exitYAllOdd_rejoin layout layout_widths layout_nodup Y k sOdd sStd m flag flag_away
    hPhase hOut hYOdd hYStd hClean

/-! ## Section 2: Odd Entry Head Commutation -/

theorem entry1_eq_odd (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k ky : Fp) (s : State) (X : Nat) (hX : X < p) (Y : Fp) (G : Bool)
    (hx : regValue L.point.x s.basis = X) (hy : regValue L.point.y s.basis = Y.val)
    (hg : s.basis L.core.generic = G) (hc : regValue L.dialogPool s.basis = 0)
    (m1 m2 : List Bool) :
    run (entryYAllOdd L ky ++ E1QubitPlacement.entryM L k) m1 s =
      run (fastConstAdd L L.point.x k ++ entryYAllOdd L ky ++ E1QubitPlacement.tickF L) m2 s := by
  have xy (q : Wire) (h : q ∈ L.point.x) : q ∉ L.point.y := (E1QubitPlacement.lay L hw hn q).1 h
  have px (q : Wire) (h : q ∈ L.dialogPool) : q ∉ L.point.x := ((E1QubitPlacement.lay L hw hn q).2.1 h).1
  have py (q : Wire) (h : q ∈ L.dialogPool) : q ∉ L.point.y := ((E1QubitPlacement.lay L hw hn q).2.1 h).2
  have gx : L.core.generic ∉ L.point.x := ((E1QubitPlacement.lay L hw hn _).2.2 rfl).1
  have gy : L.core.generic ∉ L.point.y := ((E1QubitPlacement.lay L hw hn _).2.2 rfl).2
  have fy := entryYAllOdd_correct L hw hn Y ky s (m1.take (measurementCount (entryYAllOdd L ky))) hy hc
  generalize hsy : run (entryYAllOdd L ky) (m1.take (measurementCount (entryYAllOdd L ky))) s = sy at fy
  obtain ⟨py1, py2, py3⟩ := fy
  have syx : regValue L.point.x sy.basis = X := by
    rw [regValue_congr _ _ s.basis (fun q hq => py3 q (xy q hq)), hx]
  have syg : sy.basis L.core.generic = G := (py3 _ gy).trans hg
  have syc : regValue L.dialogPool sy.basis = 0 := by
    rw [regValue_congr _ _ s.basis (fun q hq => py3 q (py q hq)), hc]
  have comm (r0 r1 r2 : List Bool) : run (fastConstAdd L L.point.x k) r0 sy =
      run (entryYAllOdd L ky) r2 (run (fastConstAdd L L.point.x k) r1 s) := by
    have fa := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX sy r0 syg syx syc
    have fc := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX s r1 hg hx hc
    generalize ha : run (fastConstAdd L L.point.x k) r0 sy = a at fa
    generalize hcc : run (fastConstAdd L L.point.x k) r1 s = c at fc
    obtain ⟨a1, a2, a3⟩ := fa
    obtain ⟨c1, c2, c3⟩ := fc
    have cy : regValue L.point.y c.basis = Y.val := by
      rw [regValue_congr _ _ s.basis (fun q hq => c3 q (fun h => xy q h hq)), hy]
    have cc : regValue L.dialogPool c.basis = 0 := by
      rw [regValue_congr _ _ s.basis (fun q hq => c3 q (px q hq)), hc]
    have fb := entryYAllOdd_correct L hw hn Y ky c r2 cy cc
    generalize hb : run (entryYAllOdd L ky) r2 c = b at fb
    obtain ⟨b1, b2, b3⟩ := fb
    have cg : c.basis L.core.generic = s.basis L.core.generic := c3 _ gx
    apply State.extensionality
    · rw [a1, b1, c1, py1]
    · funext q
      by_cases qx : q ∈ L.point.x
      · have e : regValue L.point.x a.basis = regValue L.point.x b.basis := by
          rw [a2, regValue_congr _ _ c.basis (fun q hq => b3 q (xy q hq)), c2]
        exact (regValue_eq_iff _ _ _).mp e q qx
      by_cases qy : q ∈ L.point.y
      · have e : regValue L.point.y a.basis = regValue L.point.y b.basis := by
          rw [regValue_congr _ _ sy.basis (fun q hq => a3 q (fun h => xy q h hq)), py2, b2, cg]
        exact (regValue_eq_iff _ _ _).mp e q qy
      rw [a3 q qx, b3 q qy, c3 q qx, py3 q qy]
  let nA := measurementCount (fastConstAdd L L.point.x k)
  let nY := measurementCount (entryYAllOdd L ky)
  let M := List.replicate nA false ++ m2.drop (nA + nY)
  have lhs : run (entryYAllOdd L ky ++ E1QubitPlacement.entryM L k) m1 s =
      run (E1QubitPlacement.tickF L) (m2.drop (nA + nY))
        (run (fastConstAdd L L.point.x k) (List.replicate nA false) sy) := by
    rw [run_append, hsy, E1QubitPlacement.entry_eq L hw hn k sy X hX G syx syg syc _ M, run_append]
    have t1 : M.take nA = List.replicate nA false := List.take_left' (by simp)
    have t2 : M.drop nA = m2.drop (nA + nY) := List.drop_left' (by simp)
    rw [t1, t2]
  have rhs : run (fastConstAdd L L.point.x k ++ entryYAllOdd L ky ++ E1QubitPlacement.tickF L) m2 s =
      run (E1QubitPlacement.tickF L) (m2.drop (nA + nY))
        (run (entryYAllOdd L ky) ((m2.take (nA + nY)).drop nA)
          (run (fastConstAdd L L.point.x k) ((m2.take (nA + nY)).take nA) s)) := by
    rw [run_append, run_append, measurementCount_append]
  rw [lhs, rhs, comm]

theorem head_eq_odd (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy X Y : Fp) (G : Bool) (s : State) (m : List Bool)
    (hx : regValue L.point.x s.basis = X.val) (hy : regValue L.point.y s.basis = Y.val)
    (hg : s.basis L.core.generic = G) (hc : regValue L.dialogPool s.basis = 0)
    (hpk : pkW L ≠ L.core.generic) :
    let e := if s.basis L.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false
    run (entryYAllOdd L (-cy) ++ entryXNew L (pkW L) (-cx)) m (put s (pkW L) e) =
      run (E1QubitPlacement.tickF L) []
        (run (fastConstAdd L L.point.x (-cx) ++ entryYAllOdd L (-cy)) [] s) := by
  intro e
  let YP := entryYAllOdd L (-cy)
  let t1 := m.take (measurementCount YP)
  let t2 := m.drop (measurementCount YP)
  let u := run YP t1 s
  have fy := entryYAllOdd_correct L hw hn Y (-cy) s t1 hy hc
  have tx : regValue L.point.x u.basis = X.val :=
    (regValue_congr _ _ s.basis (fun q hq => fy.2.2 q ((E1QubitPlacement.lay L hw hn q).1 hq))).trans hx
  have tc : regValue L.dialogPool u.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => fy.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).2))).trans hc
  have tg : u.basis L.core.generic = s.basis L.core.generic :=
    fy.2.2 _ (((E1QubitPlacement.lay L hw hn _).2.2 rfl).2)
  have hput : run YP t1 (put s (pkW L) e) = put u (pkW L) e :=
    run_put _ _ _ _ _ (pk_not_Y_odd L hw hn (-cy) hpk)
  let nCmp := measurementCount (E1Merge.comparePart base (base 2400) (-cx).val)
  have hxRun := FlagEntry.entryXNew_run L hw hn (pkW L) X (-cx) u tx tc
    (FlagEntry.pk_pool L hw) (FlagEntry.pk_ne_flag L hw hn)
    (FlagEntry.pk_ne_high L hw hn) (FlagEntry.pk_ne_x L hw hn)
    (by rw [E1QubitPlacement.pmap_g L hw hn]; exact hpk) t2
  rw [tg] at hxRun
  have hXAll := entryXAll_eq L hw hn X (-cx) u (List.replicate nCmp false ++ t2) tx tc
  have h1 := entry1_eq_odd L hw hn (-cx) (-cy) s X.val X.isLt Y G hx hy hg hc
    (pfx (measurementCount YP) t1 ++ (List.replicate nCmp false ++ t2)) []
  have hTakePfx : (pfx (measurementCount YP) t1 ++ (List.replicate nCmp false ++ t2)).take (measurementCount YP) =
      pfx (measurementCount YP) t1 := List.take_left' (by rw [pfx_length])
  have hDropPfx : (pfx (measurementCount YP) t1 ++ (List.replicate nCmp false ++ t2)).drop (measurementCount YP) =
      List.replicate nCmp false ++ t2 := List.drop_left' (by rw [pfx_length])
  rw [run_append, hTakePfx, hDropPfx, run_pfx] at h1
  rw [run_append, hput, show e = (if s.basis L.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false) from rfl,
      hxRun, hXAll]
  change run (E1QubitPlacement.entryM L (-cx)) (List.replicate nCmp false ++ t2) u = _
  rw [show u = run YP t1 s from rfl, h1, run_append, List.take_nil, List.drop_nil]

theorem prepClean_odd (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (kx ky X Y : Fp) (G : Bool) (s : State)
    (v : PointDialogValues L X Y G s.basis s.basis) :
    regValue L.dialogPool (run (fastConstAdd L L.point.x kx ++ entryYAllOdd L ky) [] s).basis = 0 := by
  let P := fastConstAdd L L.point.x kx
  have u := fastStep_addX L hw hn X Y G s.basis kx s [] v
  have f := entryYAllOdd_correct L hw hn Y ky (run P [] s) [] u.2.y u.2.clean
  rw [run_append, List.take_nil, List.drop_nil]
  exact (regValue_congr _ _ (run P [] s).basis (fun q hq => f.2.2 q
    (((E1QubitPlacement.lay L hw hn q).2.1 hq).2))).trans u.2.clean

def plainOdd (kx ky : Fp) : Program :=
  entryYAllOdd layout ky ++ entryXNew layout (pkW layout) kx

def routedOdd (kx ky : Fp) : Program :=
  encodeY (entryYAllOdd layout ky) ++ switchX (entryXNew layout (pkW layout) kx)

private theorem unpull_perm (f : Equiv.Perm Wire) (s : State) :
    pullState f.symm (pullState f s) = s := by
  apply State.extensionality
  · rfl
  · funext q; exact congrArg s.basis (f.apply_symm_apply q)

theorem encoded_head_odd (X Y kx ky : Fp) (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis = X.val)
    (hy : regValue layout.point.y s.basis = Y.val)
    (clean : regValue layout.dialogPool s.basis = 0)
    (hExec : ∀ (sY : State) (mX : List Bool),
      regValue layout.point.x sY.basis = X.val →
      regValue layout.dialogPool sY.basis = 0 →
      let fX := if sY.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + kx.val) else false
      run (switchX (entryXNew layout (pkW layout) kx)) mX (pullState outer.symm (put sY (pkW layout) fX)) =
        pullState integerFirst.symm (run (entryXNew layout (pkW layout) kx) mX (put sY (pkW layout) fX))) :
    let flag := if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + kx.val) else false
    let initial := put s (pkW layout) flag
    run (routedOdd kx ky) m (pullState outer.symm initial) =
      pullState integerFirst.symm (run (plainOdd kx ky) m initial) := by
  intro flag initial
  let YP := entryYAllOdd layout ky
  let tape := m.take (measurementCount YP)
  let sY := run YP tape s
  have fy := entryYAllOdd_correct layout layout_widths layout_nodup Y ky s tape hy clean
  have same (q : Wire) (hq : q ∉ layout.point.y) : sY.basis q = s.basis q := fy.2.2 q hq
  have xc : regValue layout.point.x sY.basis = X.val :=
    (regValue_congr _ _ s.basis (fun q hq =>
      same q ((E1QubitPlacement.lay layout layout_widths layout_nodup q).1 hq))).trans hx
  have pc : regValue layout.dialogPool sY.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq =>
      same q (((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).2))).trans clean
  have gc := same _ (((E1QubitPlacement.lay layout layout_widths layout_nodup _).2.2 rfl).2)
  have yactual := outerY_entry_odd Y ky s (pullState outer.symm initial) tape flag hy clean
    (unpull_perm outer.symm initial)
  have ystock : run YP tape initial = put sY (pkW layout) flag :=
    run_put _ _ _ _ _ (pk_not_Y_odd layout layout_widths layout_nodup ky flag_away)
  have ey := congrArg (pullState outer.symm) yactual
  rw [unpull_perm, ystock] at ey
  have ex := hExec sY (m.drop (measurementCount YP)) xc pc
  dsimp only at ex
  rw [gc] at ex
  rw [routedOdd, plainOdd, run_append, run_append,
      show measurementCount (encodeY YP) = measurementCount YP from (renameProgram_counts _ _).2]
  change run _ _ (run (encodeY YP) tape _) = pullState integerFirst.symm (run _ _ (run YP tape initial))
  rw [ey, ystock]
  exact ex

/-! ## Section 3: Odd-Word Division Kernel Contract & Dialog Transfer -/

open MappedCompressed.LaneA FrontierEntry1591Callers StairSemanticFinal

set_option linter.unusedVariables false in
/-- Odd-word counterpart of `FrontierEntry1591Callers.EntryCorrect`: accepts `oddWord (Y / 2)`
    on the numerator register and produces the exact canonical quotient `(Y / X).val`. -/
def EntryCorrectOdd (K : Program) : Prop :=
  ∀ (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (phase : t.phase = s.phase)
    (same : ∀ q, q ∉ wireBlock base 2056 256 → t.basis q = s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis = oddWord (Y / 2)),
    let out := run K m t
    out.phase = s.phase ∧ regValue (wireBlock base 2056 256) out.basis = (skywalkArithmeticResult true x Y).val ∧
      ∀ q, q ∉ wireBlock base 2056 256 → out.basis q = s.basis q

/-- State-side premise of `EntryCorrectOdd`, matching `StairConcreteAssembly.EntryFrame`
    with `oddWord (Y / 2)` on the numerator register. -/
structure EntryFrameOdd (t : State) where
  sharedNodup : (skywalkSharedWires base).Nodup
  historyAbove : History5.HistoryAbove base
  selectorsAway : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base
  transcript : MixedTranscriptReplayLayout base (base 2400) (base 2409)
    (base 2410) (mixedTranscriptTape base)
  x : Nat
  Y : Fp
  x_pos : 0 < x
  x_lt : x < p
  source : State
  input : SkywalkArithmeticInput base x Y.val source.basis
  selectorG_zero : source.basis (base 2409) = false
  selectorS_zero : source.basis (base 2410) = false
  phase : t.phase = source.phase
  outsideNumerator : ∀ q, q ∉ wireBlock base 2056 256 → t.basis q = source.basis q
  numerator : regValue (wireBlock base 2056 256) t.basis = oddWord (Y / 2)

private theorem mapped_reg (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀ q ∈ r, logical q = physical (f q)) :
    regValue r logical = regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0) + 2 * regValue rs logical =
      (if physical (f a) then 1 else 0) + 2 * regValue (rs.map f) physical
    rw [h a (by simp), ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

theorem entryTransferOdd (K : Program) (correct : EntryCorrectOdd K)
    (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀ a ∈ domain, ∀ b ∈ domain, f a = f b → a = b)
    (divisorMap : (wireBlock base 770 256).map f = L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f = L.point.y)
    (sharedWork : ∀ q ∈ skywalkSharedWires base, q ∈ domain → q ∉ wireBlock base 770 256 →
      q ∉ wireBlock base 2056 256 → f q ∈ L.dialogPool)
    (selectorG : f (base 2409) ∈ L.dialogPool) (selectorS : f (base 2410) ∈ L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset ⊆ domain)
    (dySites : (wireBlock base 2056 256).toFinset ⊆ domain)
    (sites : wires K ⊆ domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (hX0 : 0 < X) (hX : X < p)
    (s t : State) (m : List Bool)
    (hx : regValue L.point.x s.basis = X) (hy : regValue L.point.y s.basis = Y.val)
    (clean : regValue L.dialogPool s.basis = 0)
    (phase : t.phase = s.phase) (same : ∀ q, q ∉ L.point.y → t.basis q = s.basis q)
    (half : regValue L.point.y t.basis = oddWord (Y / 2)) :
    let out := run (renameProgram f K) m t
    out.phase = s.phase ∧ regValue L.point.y out.basis = (skywalkArithmeticResult true X Y).val ∧
      ∀ q, q ∉ L.point.y → out.basis q = s.basis q := by
  let a := laneLogicalInput domain f s
  let b := laneLogicalInput domain f t
  have aBits (q : Wire) (hq : q ∈ domain) : a.basis q = s.basis (f q) := by
    simp only [a, laneLogicalInput, if_pos hq]
  have bBits (q : Wire) (hq : q ∈ domain) : b.basis q = t.basis (f q) := by
    simp only [b, laneLogicalInput, if_pos hq]
  have zero (q : Wire) (hq : f q ∈ L.dialogPool) : a.basis q = false := by
    change (if q ∈ domain then s.basis (f q) else false) = false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_, ?_, ?_⟩
    · change regValue (wireBlock base 770 256) a.basis = X
      rw [mapped_reg f _ a.basis s.basis (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))), divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis = Y.val
      rw [mapped_reg f _ a.basis s.basis (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))), numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used : q ∈ domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a, laneLogicalInput, if_neg used]
  have outside (q : Wire) (hq : q ∈ domain) (haway : q ∉ wireBlock base 2056 256) : f q ∉ L.point.y := by
    rw [← numeratorMap]
    intro bad
    obtain ⟨r, hr, he⟩ := List.mem_map.mp bad
    have eq : q = r := injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired : ∀ q, q ∉ wireBlock base 2056 256 → b.basis q = a.basis q := by
    intro q hq
    by_cases used : q ∈ domain
    · rw [bBits q used, aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a, b, laneLogicalInput, if_neg used]
  have halfLogical : regValue (wireBlock base 2056 256) b.basis = oddWord (Y / 2) := by
    rw [mapped_reg f _ b.basis t.basis (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))), numeratorMap]
    exact half
  have phases : b.phase = a.phase := phase
  have strong := correct hn hlo ho hf X Y hX0 hX a b m input
    (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer := run_rename_pool f domain injective K sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1, ?_, ?_⟩
  · rw [← numeratorMap]
    exact (mapped_reg f _ (run K m b).basis (run (renameProgram f K) m t).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image : q ∈ domain.image f
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp image
      have away : r ∉ skywalkArithmeticNumerator base := by
        intro mem
        apply hq
        rw [← numeratorMap]
        exact List.mem_map.mpr ⟨r, mem, rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (aBits r hr))
    · exact (run_rename_pool_outside f domain K sites m t q image).trans (same q hq)

theorem entry_correctD_odd (K : Program) (kernelSupport : wires K ⊆ callerDomain)
    (correct : EntryCorrectOdd K)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (hX0 : 0 < X) (hX : X < p)
    (s t : State) (m : List Bool)
    (hx : regValue L.point.x s.basis = X) (hy : regValue L.point.y s.basis = Y.val)
    (clean : regValue L.dialogPool s.basis = 0) (phase : t.phase = s.phase)
    (same : ∀ q, q ∉ L.point.y → t.basis q = s.basis q)
    (half : regValue L.point.y t.basis = oddWord (Y / 2)) :
    let out := run (FrontierEntry1591Callers.entry K L) m t
    out.phase = s.phase ∧ regValue L.point.y out.basis = (skywalkArithmeticResult true X Y).val ∧
      ∀ q, q ∉ L.point.y → out.basis q = s.basis q := by
  rcases placement2 L hw hn with ⟨_, divisor, numerator, _, _, selG, selS, _⟩
  exact entryTransferOdd K correct L (wireFn2 L) callerDomain (wireFn2_injOn_caller L hw hn)
    divisor numerator (sharedWork_caller L hw) selG selS
    divisor_caller numerator_caller kernelSupport
    logicalND hlo logicalAway logicalReplay X Y hX0 hX s t m hx hy clean phase same half

theorem entry_eqD_odd (K : Program) (kernelSupport : wires K ⊆ callerDomain)
    (correct : EntryCorrectOdd K)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (hX0 : 0 < X) (hX : X < p)
    (s t : State) (m : List Bool)
    (hx : regValue L.point.x s.basis = X) (hy : regValue L.point.y s.basis = Y.val)
    (clean : regValue L.dialogPool s.basis = 0) (phase : t.phase = s.phase)
    (same : ∀ q, q ∉ L.point.y → t.basis q = s.basis q)
    (half : regValue L.point.y t.basis = oddWord (Y / 2)) :
    run (FrontierEntry1591Callers.entry K L) m t = run (arithS L false) [] s := by
  have newer := entry_correctD_odd K kernelSupport correct L hw hn logicalND hlo logicalAway
    logicalReplay X Y hX0 hX s t m hx hy clean phase same half
  have older := arithS_correct L hw hn false X Y.val hX hX0 (ZMod.val_lt Y) s [] hx hy clean
  have sameValue : regValue L.point.y (run (FrontierEntry1591Callers.entry K L) m t).basis =
      regValue L.point.y (run (arithS L false) [] s).basis := by
    rw [newer.2.1, older.2.1]
    simp [skywalkArithmeticResult]
  apply State.extensionality
  · exact newer.1.trans older.1.symm
  · funext q
    by_cases hq : q ∈ L.point.y
    · exact (regValue_eq_iff _ _ _).mp sameValue q hq
    · exact (newer.2.2 q hq).trans (older.2.2 q hq).symm

theorem division_stepD_odd (K : Program) (kernelSupport : wires K ⊆ callerDomain)
    (correct : EntryCorrectOdd K)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X ≠ 0) :
    Triple (PointDialogValues L X Y G origin)
      (entryYAllOdd L k ++ FrontierEntry1591Callers.entry K L)
      (PointDialogValues L X ((Y + (if G then k else 0)) / X) G origin) := by
  intro s m v
  let Z : Fp := Y + (if G then k else 0)
  let n := measurementCount (entryYAllOdd L k)
  let a := run (entryYAllOdd L k) (m.take n) s
  let c := run (fastConstAdd L L.point.y k) [] s
  have oldAdd := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt s []
    v.generic v.y v.clean
  have oldStep := fastStep_addY L hw hn X Y G origin k s [] v
  have canonical : PointDialogValues L X Z G origin c.basis := oldStep.2
  have fused := entryYAllOdd_correct L hw hn Y k s (m.take n) v.y v.clean
  change a.phase = s.phase ∧ regValue L.point.y a.basis =
    oddWord ((Y + (if s.basis L.core.generic then k else 0)) / 2) ∧
    ∀ q, q ∉ L.point.y → a.basis q = s.basis q at fused
  change c.phase = s.phase ∧ regValue L.point.y c.basis = (Y.val + (if G then k.val else 0)) % p ∧
    ∀ q, q ∉ L.point.y → c.basis q = s.basis q at oldAdd
  have phase : a.phase = c.phase := fused.1.trans oldAdd.1.symm
  have same (q : Wire) (hq : q ∉ L.point.y) : a.basis q = c.basis q :=
    (fused.2.2 q hq).trans (oldAdd.2.2 q hq).symm
  have half : regValue L.point.y a.basis = oddWord (Z / 2) := by
    simpa only [v.generic, Z] using fused.2.1
  have hp : 0 < X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have equal := entry_eqD_odd K kernelSupport correct L hw hn logicalND hlo logicalAway
    logicalReplay X.val Z hp X.isLt c a (m.drop n)
    canonical.x canonical.y canonical.clean phase same half
  have eqProgram : run (entryYAllOdd L k ++ FrontierEntry1591Callers.entry K L) m s =
      run (arithS L false) [] c := by
    rw [run_append]
    exact equal
  have old := arith3F_step L hw hn X Z G origin false hX c [] canonical
  rw [eqProgram]
  refine ⟨old.1.trans oldStep.1, ?_⟩
  simpa only [Z, Bool.false_eq_true, if_false] using old.2

/-! ## Section 4: Odd-Word Multiplication Kernel Contract & Rejoin Transfer -/

open ParityXExitInverse23Kernel

set_option linter.unusedVariables false in
/-- Odd-word counterpart of `ExitNegCorrect`: kernel `K` matches `put (run (kernelX k) m s) pkP flag`
    on every wire outside the numerator, and stores `oddWord (Y * x / 2)` on the numerator. -/
def ExitMatchesOdd (K : Program) (k : Nat) : Prop :=
  ∀ (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false),
    let out := run K m s
    let ref := put (run (ParityXExitInverse23Kernel.kernelX k) m s)
                 pkP (s.basis (base 2400) && decide (k < x))
    out.phase = ref.phase ∧
      regValue (wireBlock base 2056 256) out.basis = oddWord (Y * (x : Fp) / 2) ∧
      ∀ q, q ∉ wireBlock base 2056 256 → out.basis q = ref.basis q

theorem wordTransferOdd (L : ControlledPointLayout) (f : Wire → Wire) (k : Nat)
    (domain : Finset Wire)
    (injective : ∀ a ∈ domain, ∀ b ∈ domain, f a = f b → a = b)
    (divisorMap : (wireBlock base 770 256).map f = L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f = L.point.y)
    (controlMap : f (base 2400) = L.core.generic)
    (sharedWork : ∀ q ∈ skywalkSharedWires base, q ∈ domain → q ∉ wireBlock base 770 256 →
      q ∉ wireBlock base 2056 256 → f q ∈ L.dialogPool)
    (selectorG : f (base 2409) ∈ L.dialogPool)
    (selectorS : f (base 2410) ∈ L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset ⊆ domain)
    (dySites : (wireBlock base 2056 256).toFinset ⊆ domain)
    (gSite : base 2400 ∈ domain) (pkD : pkP ∈ domain)
    (X : Nat) (Y : Fp)
    (s : State) (m : List Bool)
    (hX : regValue L.point.x s.basis = X) (hY : regValue L.point.y s.basis = Y.val)
    (clean : regValue L.dialogPool s.basis = 0)
    (PN PO : Program) (supN : wires PN ⊆ domain) (supO : wires PO ⊆ domain)
    (P_spec : ∀ (t : State) (records : List Bool),
      SkywalkArithmeticInput base X Y.val t.basis →
      t.basis (base 2409) = false → t.basis (base 2410) = false →
      let out := run PN records t
      let ref := put (run PO records t) pkP (t.basis (base 2400) && decide (k < X))
      out.phase = ref.phase ∧
        regValue (wireBlock base 2056 256) out.basis = oddWord (Y * (X : Fp) / 2) ∧
        ∀ q, q ∉ wireBlock base 2056 256 → out.basis q = ref.basis q) :
    let out := run (renameProgram f PN) m s
    let ref := put (run (renameProgram f PO) m s) (f pkP) (s.basis L.core.generic && decide (k < X))
    out.phase = ref.phase ∧
      regValue L.point.y out.basis = oddWord (Y * (X : Fp) / 2) ∧
      ∀ q, q ∉ L.point.y → out.basis q = ref.basis q := by
  let t := ECDSAAdd.Entrant.selInput domain f s
  have inputBits (q : Wire) (hq : q ∈ domain) : t.basis q = s.basis (f q) := by
    simp only [t, ECDSAAdd.Entrant.selInput, if_pos hq]
  have zero (q : Wire) (hq : f q ∈ L.dialogPool) : t.basis q = false := by
    change (if q ∈ domain then s.basis (f q) else false) = false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val t.basis := by
    refine ⟨?_, ?_, ?_⟩
    · change regValue (wireBlock base 770 256) t.basis = X
      rw [ECDSAAdd.Entrant.selRegMap f _ t.basis s.basis
        (fun q hq => inputBits q (dxSites (List.mem_toFinset.mpr hq))), divisorMap]
      exact hX
    · change regValue (wireBlock base 2056 256) t.basis = Y.val
      rw [ECDSAAdd.Entrant.selRegMap f _ t.basis s.basis
        (fun q hq => inputBits q (dySites (List.mem_toFinset.mpr hq))), numeratorMap]
      exact hY
    · intro q hq hdx hdy
      by_cases used : q ∈ domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [t, ECDSAAdd.Entrant.selInput, if_neg used]
  have pw := P_spec t m input (zero _ selectorG) (zero _ selectorS)
  have trN := run_rename_pool f domain injective PN supN m t s rfl inputBits
  have trO := run_rename_pool f domain injective PO supO m t s rfl inputBits
  have tg : t.basis (base 2400) = s.basis L.core.generic := by rw [inputBits _ gSite, controlMap]
  dsimp only at pw ⊢
  rw [tg] at pw
  refine ⟨trN.1.trans (pw.1.trans trO.1.symm), ?_, ?_⟩
  · rw [← numeratorMap]
    exact (mapped_reg f _ (run PN m t).basis (run (renameProgram f PN) m s).basis
      (fun q hq => (trN.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans pw.2.1
  · intro q hq
    by_cases image : q ∈ domain.image f
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp image
      have away : a ∉ wireBlock base 2056 256 := by
        intro mem
        apply hq
        rw [← numeratorMap]
        exact List.mem_map.mpr ⟨a, mem, rfl⟩
      rw [trN.2 a ha, pw.2.2 a away]
      by_cases e : a = pkP
      · subst e; simp [put, writeBit]
      · have ne : f a ≠ f pkP := fun h => e (injective a ha pkP pkD h)
        simp only [put, writeBit, Function.update_apply, if_neg e, if_neg ne]
        exact (trO.2 a ha).symm
    · have ne : q ≠ f pkP := fun h => image (h ▸ Finset.mem_image_of_mem _ pkD)
      rw [run_rename_pool_outside f domain PN supN m s q image]
      simp only [put, writeBit, Function.update_apply, if_neg ne]
      rw [run_rename_pool_outside f domain PO supO m s q image]

/-- Rejoin lemma for the second stage: if `actual` has `pullState outer actual` matching
    `put plainOut (pkW layout) flag` outside `layout.point.y` and holding `oddWord Y` on
    `layout.point.y`, then `encodeY (exitYAllOdd layout cy)` produces the exact same state as
    `pullState outer.symm (run (exitYAll layout cy) ym (put plainOut (pkW layout) flag))`. -/
theorem pointSecond_rejoin_odd (Y cy : Fp) (plainOut actual : State) (ym : List Bool) (flag : Bool)
    (hYStd : regValue layout.point.y plainOut.basis = centerWord Y)
    (hClean : regValue layout.dialogPool plainOut.basis = 0)
    (hPhase : (pullState outer actual).phase = plainOut.phase)
    (hYOdd : regValue layout.point.y (pullState outer actual).basis = oddWord Y)
    (hOut : ∀ q, q ∉ layout.point.y →
      (pullState outer actual).basis q = (put plainOut (pkW layout) flag).basis q) :
    run (encodeY (exitYAllOdd layout cy)) ym actual =
      pullState outer.symm (run (exitYAll layout cy) ym (put plainOut (pkW layout) flag)) := by
  let sOdd : State := ⟨plainOut.phase, fun q =>
    if q ∈ layout.point.y then (pullState outer actual).basis q else plainOut.basis q⟩
  have hpkNotY : pkW layout ∉ layout.point.y :=
    ((E1QubitPlacement.lay layout layout_widths layout_nodup (pkW layout)).2.1
      (FlagEntry.pk_pool layout layout_widths)).2
  have hPullEq : pullState outer actual = put sOdd (pkW layout) flag := by
    apply State.extensionality
    · exact hPhase
    · funext q
      by_cases hq : q ∈ layout.point.y
      · have hqNe : q ≠ pkW layout := fun e => hpkNotY (e ▸ hq)
        simp only [sOdd, put, writeBit, Function.update_apply, if_neg hqNe, if_pos hq]
      · rw [hOut q hq]
        by_cases he : q = pkW layout
        · subst he; simp [put, writeBit]
        · simp only [sOdd, put, writeBit, Function.update_apply, if_neg he, if_neg hq]
  have hsOddY : regValue layout.point.y sOdd.basis = oddWord Y :=
    (regValue_congr _ _ (pullState outer actual).basis (fun q hq => by simp [sOdd, hq])).trans hYOdd
  have hsOddOut : ∀ q, q ∉ layout.point.y → sOdd.basis q = plainOut.basis q := by
    intro q hq; simp [sOdd, hq]
  have hRej := outerY_exit_rejoin Y cy sOdd plainOut actual ym flag rfl hsOddOut hsOddY hYStd hClean hPullEq
  have hFinal := congrArg (pullState outer.symm) hRej
  rwa [unpull_perm] at hFinal

/-! ## Section 5: Resource Budget & First-Packet Interface Helpers -/

/-- The `+7144` worst-case slot overhead of `entryYAllOdd` + `exitYAllOdd` is strictly
    dominated by the `-7187` slots saved when dropping the `k = 1` boundary conversions
    (`dstartPacket 1` saves `3338`, `mendPacket 1` saves `3849`). -/
theorem outerY_slots_absorbed_by_k1 (a b x y : Nat)
    (hd : a + 3338 ≤ x + 2710000 + 2610000 + 367858)
    (hm : b + 3849 ≤ y + 2710000 + 2610000 + 323189) :
    a + b + 7144 ≤ x + y + 11331047 - 43 := by
  omega

/-- Resource and wire-safety interface expected from the odd first-packet module
    (`placedFirstPacketOdd`) when wired into `WindowCallerCosts`, `WindowSites`,
    `WindowPhysical`, `ExteriorCaller`, and `WindowExteriorFixed`. -/
structure FirstPacketOddContract (placedOdd : Bool → Program) : Prop where
  physical : ∀ d, GatePhysical (placedOdd d)
  wires_sub : ∀ d, wires (placedOdd d) ⊆ wires (Rolling1588.placedFirstPacket d)
  toffoli_le : ∀ d, toffoliCount (placedOdd d) ≤ toffoliCount (Rolling1588.placedFirstPacket d)
  measure_le : ∀ d, measurementCount (placedOdd d) ≤ measurementCount (Rolling1588.placedFirstPacket d)
  slots_le : ∀ d, gateSlots (placedOdd d) ≤ gateSlots (Rolling1588.placedFirstPacket d)

end ECDSAAdd.Entrant.OddOuterBridge
end

end
-- ==== end OddPhaseBBridge ====

-- ==== begin OddFirstPacket ====
section

/-!
# Odd-word joint entry/inverse kernels and first packet (`k = 0`)

Implements the odd-word joint entry (`paddedGD_odd`, `765 T / 509 M`) and joint
inverse (`paddedD_odd`, `509 T / 765 M`) together with the odd-word first packet
(`firstPacketOdd`, `placedFirstPacketOdd`, `hostedFirstPacketOdd`) parametrized
by an odd-word half-cell program.
-/

-- ============================================================================
-- Section 1: Odd-word arithmetic and measurement-based equality/copy primitives
-- ============================================================================
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.JointOdd1588
open ECDSAAdd Arithmetic Challenge Baselines BalancedField Secp256k1 RecordedQuantum

def OddDomain (R : Int) : Prop := -q - 1 ≤ R ∧ R ≤ q - 1

def oddRep (x : Fp) : Int :=
  let z := centerFp x
  if z < 0 then z + q else z - q - 1

def oddWord (x : Fp) : Nat := encodeWord 256 (oddRep x)

def oddDecode (R : Int) : Fp := (R : Fp) + 1 / 2

theorem two_ne_zero : (2 : Fp) ≠ 0 := by decide

theorem q_field : (q : Fp) + 1 / 2 = 0 := by
  have eq := congrArg (fun z : Int => (z : Fp)) constants.2.1
  have qp : (2 : Fp) * (q : Fp) + 1 = 0 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, ZMod.natCast_self] using eq.symm
  apply mul_left_cancel₀ two_ne_zero
  calc
    (2 : Fp) * ((q : Fp) + 1 / 2) = 2 * (q : Fp) + 1 := by field_simp [two_ne_zero]
    _ = 2 * 0 := by simpa using qp

theorem oddRep_bounds (x : Fp) : OddDomain (oddRep x) := by
  have hz := centerFp_bounds x
  unfold Centered at hz
  dsimp only [oddRep, OddDomain]
  split_ifs <;> omega

theorem oddRep_field (x : Fp) : oddDecode (oddRep x) = x := by
  have hq := q_field
  dsimp only [oddDecode, oddRep]
  split_ifs
  · push_cast
    rw [add_assoc, hq, add_zero, centerFp_cast]
  · push_cast
    calc
      (centerFp x : Fp) - (q : Fp) - 1 + 1 / 2 = (centerFp x : Fp) := by
        field_simp [two_ne_zero] at hq ⊢
        linear_combination -hq
      _ = x := centerFp_cast x

theorem oddDomain_unique (R T : Int) (hr : OddDomain R) (ht : OddDomain T)
    (eq : oddDecode R = oddDecode T) : R = T := by
  have fieldEq : ((R + 1 : Int) : Fp) = ((T + 1 : Int) : Fp) := by
    simp only [oddDecode] at eq
    push_cast
    linear_combination eq
  have u := centered_cast_unique (R + 1) (T + 1)
    (by unfold OddDomain at hr; unfold Centered; omega)
    (by unfold OddDomain at ht; unfold Centered; omega) fieldEq
  omega

theorem oddRep_inverse (R : Int) (hr : OddDomain R) : oddRep (oddDecode R) = R :=
  oddDomain_unique _ _ (oddRep_bounds _) hr (oddRep_field _)

theorem oddRep_zero : oddRep 0 = -q - 1 := by
  apply oddDomain_unique _ _ (oddRep_bounds 0)
  · have hc := constants; unfold OddDomain; omega
  · rw [oddRep_field]
    simp only [oddDecode, Int.cast_sub, Int.cast_neg, Int.cast_one]
    have hq := q_field
    calc (0 : Fp) = -((q : Fp) + 1 / 2) := by rw [hq, neg_zero]
      _ = -(q : Fp) - 1 + 1 / 2 := by field_simp [two_ne_zero]; ring

theorem oddWord_lt (x : Fp) : oddWord x < 2 ^ 256 := by
  unfold oddWord encodeWord
  have h := oddRep_bounds x
  have hc := constants
  unfold OddDomain at h
  omega

theorem oddWord_zero_ne : oddWord 0 ≠ 0 := by
  unfold oddWord
  rw [oddRep_zero]
  norm_num [encodeWord, q, p]

theorem oddWord_injective : Function.Injective oddWord := by
  intro a b hab
  have ha := oddRep_bounds a
  have hb := oddRep_bounds b
  have hc := constants
  unfold OddDomain at ha hb
  have hrep : oddRep a = oddRep b := by
    unfold oddWord encodeWord at hab
    omega
  rw [← oddRep_field a, ← oddRep_field b, hrep]

theorem oddRep_neg (Z : Fp) (hZ : Z ≠ 0) : oddRep (-Z) = -oddRep Z - 1 := by
  have hb := oddRep_bounds Z
  unfold OddDomain at hb
  have hne : oddRep Z ≠ -q - 1 := by
    intro eq
    apply hZ
    rw [← oddRep_field Z, eq, ← oddRep_zero, oddRep_field]
  have hd : OddDomain (-oddRep Z - 1) := by unfold OddDomain; omega
  apply oddDomain_unique _ _ (oddRep_bounds _) hd
  rw [oddRep_field]
  simp only [oddDecode, Int.cast_sub, Int.cast_neg, Int.cast_one]
  have hf := oddRep_field Z
  simp only [oddDecode] at hf
  calc -Z = -((oddRep Z : Fp) + 1 / 2) := by rw [hf]
    _ = -(oddRep Z : Fp) - 1 + 1 / 2 := by field_simp [two_ne_zero]; ring

def oddHalfStep : Int := (q + 1) / 2
def oddHalfConst : Nat := oddHalfStep.toNat
def negOddHalfConst : Nat := 2 ^ 256 - oddHalfConst

def oddHalfSigned (w : Int) : Int :=
  w / 2 + if w % 2 ≠ 0 then oddHalfStep else -oddHalfStep

theorem oddHalfStep_facts :
    2 * oddHalfStep = q + 1 ∧
    oddHalfStep % 4 = 0 ∧
    oddHalfConst % 8 = 4 ∧
    negOddHalfConst % 8 = 4 ∧
    oddHalfConst < 2 ^ 255 ∧
    negOddHalfConst < 2 ^ 256 := by
  norm_num [oddHalfStep, oddHalfConst, negOddHalfConst, q, p, Int.toNat]

theorem oddHalfSigned_domain (w : Int) (hw : OddDomain w) :
    OddDomain (oddHalfSigned w) ∧
    oddDecode (oddHalfSigned w) = oddDecode w / 2 ∧
    (oddHalfSigned w < 0 ↔ w % 2 = 0) := by
  have hs := oddHalfStep_facts
  have hc := constants
  unfold OddDomain at hw ⊢
  unfold oddHalfSigned
  refine ⟨?_, ?_, ?_⟩
  · split_ifs <;> omega
  · have hdouble : 2 * (w / 2 + if w % 2 ≠ 0 then oddHalfStep else -oddHalfStep) + 1 =
        if w % 2 ≠ 0 then w + (q + 1) else w - q := by
      split_ifs <;> omega
    have hq := q_field
    have hcast := congrArg (fun z : Int => (z : Fp)) hdouble
    have heq : (2 : Fp) * oddDecode (w / 2 + if w % 2 ≠ 0 then oddHalfStep else -oddHalfStep) =
        oddDecode w := by
      simp only [oddDecode]
      have h2 : (2 : Fp) * (((w / 2 + if w % 2 ≠ 0 then oddHalfStep else -oddHalfStep : Int) : Fp) + 1 / 2) =
          2 * ((w / 2 + if w % 2 ≠ 0 then oddHalfStep else -oddHalfStep : Int) : Fp) + 1 := by
        field_simp [two_ne_zero]
      rw [h2]
      have hcast' : (2 : Fp) * ((w / 2 + if w % 2 ≠ 0 then oddHalfStep else -oddHalfStep : Int) : Fp) + 1 =
          ((if w % 2 ≠ 0 then w + (q + 1) else w - q : Int) : Fp) := by
        simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using hcast
      rw [hcast']
      split_ifs
      · push_cast
        calc (w : Fp) + ((q : Fp) + 1) = (w : Fp) + 1 / 2 + ((q : Fp) + 1 / 2) := by
              field_simp [two_ne_zero]; ring
          _ = (w : Fp) + 1 / 2 := by rw [hq, add_zero]
      · push_cast
        calc (w : Fp) - (q : Fp) = (w : Fp) + 1 / 2 - ((q : Fp) + 1 / 2) := by
              field_simp [two_ne_zero]; ring
          _ = (w : Fp) + 1 / 2 := by rw [hq, sub_zero]
    apply mul_left_cancel₀ two_ne_zero
    rw [heq]
    field_simp [two_ne_zero]
  · split_ifs <;> omega

theorem oddHalfSigned_q : oddHalfSigned q = q ∧ ¬ (q < 0) ∧ q % 2 ≠ 0 := by
  have hs := oddHalfStep_facts
  have hc := constants
  unfold oddHalfSigned
  refine ⟨?_, by omega, by omega⟩
  have hodd : q % 2 ≠ 0 := by norm_num [q, p]
  rw [if_pos hodd]
  omega

theorem encodeWord_complement (z : Int) (hlo : -(2 ^ 255 : Int) ≤ z) (hhi : z < (2 ^ 255 : Int)) :
    2 ^ 256 - 1 - encodeWord 256 z = encodeWord 256 (-z - 1) := by
  unfold encodeWord
  omega

theorem encodeWord_q_eq : encodeWord 256 q = 2 ^ 256 - 1 - oddWord 0 := by
  have hc := constants
  rw [oddWord, oddRep_zero]
  have h := encodeWord_complement (-q - 1) (by omega) (by omega)
  have heq : -(-q - 1) - 1 = q := by omega
  rw [heq] at h
  exact h.symm

theorem encodeWord_testBit255 (z : Int) (hlo : -(2 ^ 255 : Int) ≤ z) (hhi : z < (2 ^ 255 : Int)) :
    (encodeWord 256 z).testBit 255 = decide (z < 0) := by
  unfold encodeWord
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply decide_eq_decide.mpr
  omega

theorem encodeWord_mod2 (z : Int) :
    (encodeWord 256 z % 2 = 1) ↔ z % 2 ≠ 0 := by
  unfold encodeWord
  omega

theorem encodeWord_asr (w : Int) (hlo : -(2 ^ 255 : Int) ≤ w) (hhi : w < (2 ^ 255 : Int)) :
    encodeWord 256 (w / 2) =
      encodeWord 256 w / 2 + if w < 0 then 2 ^ 255 else 0 := by
  unfold encodeWord
  split_ifs <;> omega

theorem oddHalf_mod_eq (w : Int) (hw : -q - 1 ≤ w ∧ w ≤ q) :
    (encodeWord 256 (w / 2) +
      if w % 2 ≠ 0 then oddHalfConst else negOddHalfConst) % 2 ^ 256 =
      encodeWord 256 (oddHalfSigned w) := by
  have hs := oddHalfStep_facts
  have hc := constants
  unfold oddHalfSigned encodeWord negOddHalfConst
  have h1 : (oddHalfConst : Int) = oddHalfStep := by
    unfold oddHalfConst; omega
  split_ifs <;> omega

theorem testBit_complement (n x k : Nat) (hx : x < 2 ^ n) (hk : k < n) :
    (2 ^ n - 1 - x).testBit k = !(x.testBit k) := by
  induction n generalizing x k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      simp only [Nat.testBit_zero]
      have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      cases hx2 : x % 2 with
      | zero => simp [show (2 ^ (n + 1) - 1 - x) % 2 = 1 by rw [Nat.pow_succ]; omega]
      | succ r =>
        have hr : r = 0 := by have := Nat.mod_lt x (by decide : 0 < 2); omega
        subst hr
        simp [show (2 ^ (n + 1) - 1 - x) % 2 = 0 by rw [Nat.pow_succ]; omega]
    | succ k =>
      rw [Nat.testBit_succ, Nat.testBit_succ]
      have hdiv : (2 ^ (n + 1) - 1 - x) / 2 = 2 ^ n - 1 - x / 2 := by
        rw [Nat.pow_succ]; omega
      rw [hdiv]
      exact ih (x / 2) k (by rw [Nat.pow_succ] at hx; omega) (by omega)

theorem negOddHalf_bit_eq (i : Nat) (hi : 3 ≤ i) (h256 : i < 256) :
    negOddHalfConst.testBit i = !(oddHalfConst.testBit i) := by
  have hs := oddHalfStep_facts
  have hcomp : negOddHalfConst / 8 = 2 ^ 253 - 1 - oddHalfConst / 8 := by
    unfold negOddHalfConst; omega
  have shift (n : Nat) : n.testBit i = (n / 8).testBit (i - 3) := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_div_two_pow]
    congr 1; omega
  rw [shift negOddHalfConst, shift oddHalfConst, hcomp]
  exact testBit_complement 253 (oddHalfConst / 8) (i - 3) (by omega) (by omega)

-- ============================================================================
-- Measurement-based equality-toggle (`eqToggle`) and copy erasure (`eraseCopy`)
-- ============================================================================

def andChainStep (acc y a : Wire) (b : Bool) : Program :=
  if b then [.CCX acc y a] else [.X y, .CCX acc y a, .X y]

def eraseAndChainStep (acc y a : Wire) (b : Bool) : Program :=
  if b then [.measureX a [] [.CZ acc y]]
  else [.X y, .measureX a [] [.CZ acc y], .X y]

def andChain (acc : Wire) : List Wire → List Wire → Nat → Program
  | y :: ys, a :: anc, k => andChainStep acc y a (k % 2 = 1) ++ andChain a ys anc (k / 2)
  | _, _, _ => []

def eraseAndChain (acc : Wire) : List Wire → List Wire → Nat → Program
  | y :: ys, a :: anc, k => eraseAndChain a ys anc (k / 2) ++ eraseAndChainStep acc y a (k % 2 = 1)
  | _, _, _ => []

def eqToggle (acc : Wire) (ys anc rs : List Wire) (k : Nat) : Program :=
  andChain acc ys anc k ++ signComplement (anc.getLastD acc) rs ++ eraseAndChain acc ys anc k

def eraseCopy (j : Wire) : List Wire → List Wire → Program
  | x :: xs, y :: ys => [.measureX y [] [.CZ j x]] ++ eraseCopy j xs ys
  | _, _ => []

private theorem nodup_ne_of_count {l : List Wire} (hn : l.Nodup) {a b : Wire}
    (h : a = b → 2 ≤ l.count a) : a ≠ b := by
  intro e
  have c := List.nodup_iff_count.mp hn a
  have h2 := h e
  omega

theorem eraseAnd_single (a b t : Wire) (ha : a ≠ t) (hb : b ≠ t) (s : State) (m : List Bool)
    (ht : s.basis t = (s.basis a && s.basis b)) :
    run [.measureX t [] [.CZ a b]] m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  cases hr : m.head?.getD false <;>
    simp [run, measureAndCorrect, correct, writeBit, ha, hb, ht, hr]

theorem andChainStep_run (acc y a : Wire) (b : Bool)
    (h1 : acc ≠ y) (h2 : acc ≠ a) (h3 : y ≠ a)
    (s : State) (m : List Bool) (ha : s.basis a = false) :
    run (andChainStep acc y a b) m s =
      ⟨s.phase, writeBit s.basis a (s.basis acc && (s.basis y == b))⟩ := by
  have _ := h2
  cases b <;>
    (apply State.extensionality; · simp [andChainStep, run]) <;>
    (funext q; by_cases hqa : q = a
     · subst q; simp [andChainStep, run, writeBit, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, ha]
     · by_cases hqy : q = y
       · subst q; simp [andChainStep, run, writeBit, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]
       · simp [andChainStep, run, writeBit, hqa, hqy])

theorem eraseAndChainStep_run (acc y a : Wire) (b : Bool)
    (h1 : acc ≠ y) (h2 : acc ≠ a) (h3 : y ≠ a)
    (s : State) (m : List Bool)
    (ha : s.basis a = (s.basis acc && (s.basis y == b))) :
    run (eraseAndChainStep acc y a b) m s = ⟨s.phase, writeBit s.basis a false⟩ := by
  cases b
  · let st1 : State := ⟨s.phase, writeBit s.basis y (!s.basis y)⟩
    have hstep1 : run [.X y] [] s = st1 := rfl
    have hmid : run [.measureX a [] [.CZ acc y]] (m.take 1) st1 = ⟨st1.phase, writeBit st1.basis a false⟩ := by
      apply eraseAnd_single acc y a h2 h3 st1 (m.take 1)
      simp [st1, writeBit, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, ha]
    have hsplit : eraseAndChainStep acc y a false = [.X y] ++ ([.measureX a [] [.CZ acc y]] ++ [.X y]) := rfl
    rw [hsplit, run_append, show measurementCount [.X y] = 0 from rfl,
      List.take_zero, List.drop_zero, hstep1, run_append,
      show measurementCount [.measureX a [] [.CZ acc y]] = 1 from rfl, hmid]
    apply State.extensionality
    · rfl
    · funext q
      by_cases hqy : q = y
      · subst q; simp [st1, run, writeBit, h3, Ne.symm h3]
      · by_cases hqa : q = a
        · subst q; simp [st1, run, writeBit, hqy, h3]
        · simp [st1, run, writeBit, hqy, hqa]
  · exact eraseAnd_single acc y a h2 h3 s m (by simpa using ha)

theorem andChain_counts (acc : Wire) (ys anc : List Wire) (k : Nat) (hl : ys.length = anc.length) :
    toffoliCount (andChain acc ys anc k) = ys.length ∧
    measurementCount (andChain acc ys anc k) = 0 := by
  induction ys generalizing acc anc k with
  | nil => cases anc <;> simp [andChain, toffoliCount, measurementCount]
  | cons y ys ih =>
    cases anc with
    | nil => simp at hl
    | cons a anc =>
      have h := ih a anc (k / 2) (by simpa using hl)
      have hs : toffoliCount (andChainStep acc y a (k % 2 = 1)) = 1 ∧
          measurementCount (andChainStep acc y a (k % 2 = 1)) = 0 := by
        cases decide (k % 2 = 1) <;> simp [andChainStep, toffoliCount, measurementCount]
      simp only [andChain, toffoliCount_append, measurementCount_append, hs.1, hs.2, h.1, h.2,
        List.length_cons]
      exact ⟨Nat.add_comm _ _, trivial⟩

theorem eraseAndChain_counts (acc : Wire) (ys anc : List Wire) (k : Nat) (hl : ys.length = anc.length) :
    toffoliCount (eraseAndChain acc ys anc k) = 0 ∧
    measurementCount (eraseAndChain acc ys anc k) = ys.length := by
  induction ys generalizing acc anc k with
  | nil => cases anc <;> simp [eraseAndChain, toffoliCount, measurementCount]
  | cons y ys ih =>
    cases anc with
    | nil => simp at hl
    | cons a anc =>
      have h := ih a anc (k / 2) (by simpa using hl)
      have hs : toffoliCount (eraseAndChainStep acc y a (k % 2 = 1)) = 0 ∧
          measurementCount (eraseAndChainStep acc y a (k % 2 = 1)) = 1 := by
        cases decide (k % 2 = 1) <;> simp [eraseAndChainStep, toffoliCount, measurementCount]
      simp only [eraseAndChain, toffoliCount_append, measurementCount_append, hs.1, hs.2, h.1, h.2,
        List.length_cons]
      exact ⟨trivial, trivial⟩

theorem andChain_slots_le (acc : Wire) (ys anc : List Wire) (k : Nat) :
    gateSlots (andChain acc ys anc k) ≤ 3 * ys.length := by
  induction ys generalizing acc anc k with
  | nil => simp [andChain]
  | cons y ys ih =>
    cases anc with
    | nil => simp [andChain]
    | cons a anc =>
      have h := ih a anc (k / 2)
      have hs : gateSlots (andChainStep acc y a (k % 2 = 1)) ≤ 3 := by
        cases decide (k % 2 = 1) <;>
          simp [andChainStep, gateSlots_cons, gateSlots_nil, instructionSlots]
      simp only [andChain, gateSlots_append, List.length_cons]
      omega

theorem eraseAndChain_slots_le (acc : Wire) (ys anc : List Wire) (k : Nat) :
    gateSlots (eraseAndChain acc ys anc k) ≤ 4 * ys.length := by
  induction ys generalizing acc anc k with
  | nil => simp [eraseAndChain]
  | cons y ys ih =>
    cases anc with
    | nil => simp [eraseAndChain]
    | cons a anc =>
      have h := ih a anc (k / 2)
      have hs : gateSlots (eraseAndChainStep acc y a (k % 2 = 1)) ≤ 4 := by
        cases decide (k % 2 = 1) <;>
          simp [eraseAndChainStep, gateSlots_cons, gateSlots_nil, instructionSlots]
      simp only [eraseAndChain, gateSlots_append, List.length_cons]
      omega

theorem andChain_wires_sub (acc : Wire) (ys anc : List Wire) (k : Nat) :
    wires (andChain acc ys anc k) ⊆ (acc :: (ys ++ anc)).toFinset := by
  induction ys generalizing acc anc k with
  | nil => simp [andChain, wires]
  | cons y ys ih =>
    cases anc with
    | nil => simp [andChain, wires]
    | cons a anc =>
      have hstep : wires (andChainStep acc y a (k % 2 = 1)) ⊆ ({acc, y, a} : Finset Wire) := by
        cases decide (k % 2 = 1) <;>
          (intro q hq; simp [andChainStep, wires, Instr.wires] at hq ⊢; tauto)
      intro q hq
      simp only [andChain, wires_append, Finset.mem_union] at hq
      rcases hq with hq | hq
      · have m := hstep hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at m
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append]; tauto
      · have m := ih a anc (k / 2) hq
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at m ⊢; tauto

theorem eraseAndChain_wires_sub (acc : Wire) (ys anc : List Wire) (k : Nat) :
    wires (eraseAndChain acc ys anc k) ⊆ (acc :: (ys ++ anc)).toFinset := by
  induction ys generalizing acc anc k with
  | nil => simp [eraseAndChain, wires]
  | cons y ys ih =>
    cases anc with
    | nil => simp [eraseAndChain, wires]
    | cons a anc =>
      have hstep : wires (eraseAndChainStep acc y a (k % 2 = 1)) ⊆ ({acc, y, a} : Finset Wire) := by
        cases decide (k % 2 = 1) <;>
          (intro q hq; simp [eraseAndChainStep, wires, Instr.wires, correctionWires] at hq ⊢; tauto)
      intro q hq
      simp only [eraseAndChain, wires_append, Finset.mem_union] at hq
      rcases hq with hq | hq
      · have m := ih a anc (k / 2) hq
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at m ⊢; tauto
      · have m := hstep hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at m
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append]; tauto

private theorem nodup_head3 {acc y a : Wire} {ys anc : List Wire}
    (hn : (acc :: (y :: ys ++ a :: anc)).Nodup) :
    acc ≠ y ∧ acc ≠ a ∧ y ≠ a ∧ (a :: (ys ++ anc)).Nodup := by
  have ct := List.nodup_iff_count.mp hn
  have h1 : acc ≠ y := nodup_ne_of_count hn (by
    intro e; subst e; simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true]; omega)
  have h2 : acc ≠ a := nodup_ne_of_count hn (by
    intro e; subst e; simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true]; omega)
  have h3 : y ≠ a := nodup_ne_of_count hn (by
    intro e; subst e; simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true]; omega)
  have hnd : (a :: (ys ++ anc)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have := ct q; simp only [List.count_cons, List.count_append] at this ⊢; omega
  exact ⟨h1, h2, h3, hnd⟩

theorem andChain_physical (acc : Wire) (ys anc : List Wire) (k : Nat)
    (hn : (acc :: (ys ++ anc)).Nodup) : GatePhysical (andChain acc ys anc k) := by
  induction ys generalizing acc anc k with
  | nil => simp [andChain, GatePhysical]
  | cons y ys ih =>
    cases anc with
    | nil => simp [andChain, GatePhysical]
    | cons a anc =>
      obtain ⟨h1, h2, h3, hnd⟩ := nodup_head3 hn
      have hstep : GatePhysical (andChainStep acc y a (k % 2 = 1)) := by
        cases decide (k % 2 = 1) <;>
          simp [andChainStep, GatePhysical, PhysicalInstr, ProperGate, h1, h2, h3,
            Ne.symm h1, Ne.symm h2, Ne.symm h3]
      simp only [andChain, gatePhysical_append]
      exact ⟨hstep, ih a anc (k / 2) hnd⟩

theorem eraseAndChain_physical (acc : Wire) (ys anc : List Wire) (k : Nat)
    (hn : (acc :: (ys ++ anc)).Nodup) : GatePhysical (eraseAndChain acc ys anc k) := by
  induction ys generalizing acc anc k with
  | nil => simp [eraseAndChain, GatePhysical]
  | cons y ys ih =>
    cases anc with
    | nil => simp [eraseAndChain, GatePhysical]
    | cons a anc =>
      obtain ⟨h1, h2, h3, hnd⟩ := nodup_head3 hn
      have hstep : GatePhysical (eraseAndChainStep acc y a (k % 2 = 1)) := by
        cases decide (k % 2 = 1) <;>
          simp [eraseAndChainStep, GatePhysical, PhysicalInstr, ProperGate, h1, h2, h3,
            Ne.symm h1, Ne.symm h2, Ne.symm h3]
      simp only [eraseAndChain, gatePhysical_append]
      exact ⟨ih a anc (k / 2) hnd, hstep⟩

theorem eqToggle_correct (acc : Wire) (ys anc rs : List Wire) (k : Nat)
    (hl : ys.length = anc.length)
    (hn : (acc :: (ys ++ anc ++ rs)).Nodup)
    (s : State) (m : List Bool) (hclean : ∀ q ∈ anc, s.basis q = false) :
    let out := run (eqToggle acc ys anc rs k) m s
    out.phase = s.phase ∧
    (∀ q, q ∉ rs → out.basis q = s.basis q) ∧
    regValue rs out.basis =
      if s.basis acc && decide (regValue ys s.basis = k % 2 ^ ys.length)
      then 2 ^ rs.length - 1 - regValue rs s.basis
      else regValue rs s.basis := by
  induction ys generalizing acc anc k s m with
  | nil =>
    cases anc with
    | nil =>
      have hndR : rs.Nodup := (List.nodup_cons.mp hn).2
      have haccR : acc ∉ rs := (List.nodup_cons.mp hn).1
      have hsc := signComplement_correct acc rs hndR haccR s m
      simpa only [eqToggle, andChain, eraseAndChain, List.getLastD_nil, List.nil_append,
        List.append_nil, regValue, List.foldr_nil, List.length_nil, pow_zero, Nat.mod_one,
        decide_true, Bool.and_true] using hsc
    | cons a anc => simp at hl
  | cons y ys ih =>
    cases anc with
    | nil => simp at hl
    | cons a anc =>
      have ct := List.nodup_iff_count.mp hn
      have h1 : acc ≠ y := nodup_ne_of_count hn (by
        intro e; subst e; simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true]; omega)
      have h2 : acc ≠ a := nodup_ne_of_count hn (by
        intro e; subst e; simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true]; omega)
      have h3 : y ≠ a := nodup_ne_of_count hn (by
        intro e; subst e; simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true]; omega)
      have hnd' : (a :: (ys ++ anc ++ rs)).Nodup := by
        apply List.nodup_iff_count.mpr
        intro q; have := ct q; simp only [List.count_cons, List.count_append] at this ⊢; omega
      have haR : a ∉ rs := by
        intro bad; have := ct a; have pos := List.count_pos_iff.mpr bad
        simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
      have haccR : acc ∉ rs := by
        intro bad; have := ct acc; have pos := List.count_pos_iff.mpr bad
        simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
      have hyR : y ∉ rs := by
        intro bad; have := ct y; have pos := List.count_pos_iff.mpr bad
        simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
      have haAnc : a ∉ anc := by
        intro bad; have := ct a; have pos := List.count_pos_iff.mpr bad
        simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
      have haYs : a ∉ ys := by
        intro bad; have := ct a; have pos := List.count_pos_iff.mpr bad
        simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
      have hyl : ys.length = anc.length := by simpa using hl
      have hlast : (a :: anc).getLastD acc = anc.getLastD a := by
        cases anc <;> rfl
      have hshape : eqToggle acc (y :: ys) (a :: anc) rs k =
          andChainStep acc y a (k % 2 = 1) ++
            (eqToggle a ys anc rs (k / 2) ++ eraseAndChainStep acc y a (k % 2 = 1)) := by
        simp only [eqToggle, andChain, eraseAndChain, hlast, List.append_assoc]
      have hm1 : measurementCount (andChainStep acc y a (k % 2 = 1)) = 0 := by
        cases decide (k % 2 = 1) <;> rfl
      have hstep1 := andChainStep_run acc y a (k % 2 = 1) h1 h2 h3 s [] (hclean a (by simp))
      let st1 : State := ⟨s.phase, writeBit s.basis a (s.basis acc && (s.basis y == decide (k % 2 = 1)))⟩
      have hclean1 : ∀ q ∈ anc, st1.basis q = false := by
        intro q hq
        have hqa : q ≠ a := fun e => haAnc (e ▸ hq)
        simpa only [st1, writeBit, Function.update_of_ne hqa] using hclean q (by simp [hq])
      let mk := m.take (measurementCount (eqToggle a ys anc rs (k / 2)))
      let mt := m.drop (measurementCount (eqToggle a ys anc rs (k / 2)))
      have hmid := ih a anc (k / 2) hyl hnd' st1 mk hclean1
      let s2 := run (eqToggle a ys anc rs (k / 2)) mk st1
      have hs2_a : s2.basis a = st1.basis a := hmid.2.1 a haR
      have hs2_acc : s2.basis acc = s.basis acc :=
        (hmid.2.1 acc haccR).trans (by simp [st1, writeBit, h2])
      have hs2_y : s2.basis y = s.basis y :=
        (hmid.2.1 y hyR).trans (by simp [st1, writeBit, h3])
      have hs2_rel : s2.basis a = (s2.basis acc && (s2.basis y == decide (k % 2 = 1))) := by
        rw [hs2_a, hs2_acc, hs2_y]
        simp [st1, writeBit]
      have hstep3 := eraseAndChainStep_run acc y a (k % 2 = 1) h1 h2 h3 s2 mt hs2_rel
      have hrun : run (eqToggle acc (y :: ys) (a :: anc) rs k) m s =
          ⟨s2.phase, writeBit s2.basis a false⟩ := by
        rw [hshape, run_append, hm1, List.take_zero, List.drop_zero, hstep1, run_append]
        exact hstep3
      have hy_val : regValue ys st1.basis = regValue ys s.basis := by
        apply regValue_congr
        intro q hq
        simp [st1, writeBit, show q ≠ a from fun e => haYs (e ▸ hq)]
      have hr_val1 : regValue rs st1.basis = regValue rs s.basis := by
        apply regValue_congr
        intro q hq
        simp [st1, writeBit, show q ≠ a from fun e => haR (e ▸ hq)]
      have hr_val3 : regValue rs (writeBit s2.basis a false) = regValue rs s2.basis := by
        apply regValue_congr
        intro q hq
        simp [writeBit, show q ≠ a from fun e => haR (e ▸ hq)]
      have hcond : (st1.basis a && decide (regValue ys st1.basis = (k / 2) % 2 ^ ys.length)) =
          (s.basis acc && decide (regValue (y :: ys) s.basis = k % 2 ^ (y :: ys).length)) := by
        rw [hy_val]
        simp only [st1, writeBit, Function.update_self, Bool.and_assoc]
        congr 1
        have hbit : ((s.basis y == decide (k % 2 = 1)) &&
            decide (regValue ys s.basis = (k / 2) % 2 ^ ys.length)) =
            decide ((s.basis y).toNat + 2 * regValue ys s.basis = k % 2 ^ (ys.length + 1)) := by
          have hlt := regValue_lt ys s.basis
          have hdm : k % 2 ^ (ys.length + 1) = k % 2 + 2 * ((k / 2) % 2 ^ ys.length) := by
            rw [Nat.pow_succ']
            have h1 := Nat.div_add_mod k 2
            have h2 := Nat.div_add_mod (k / 2) (2 ^ ys.length)
            have h3 := Nat.mod_lt k (by decide : 0 < 2)
            have h4 := Nat.mod_lt (k / 2) (Nat.two_pow_pos ys.length)
            have h5 : k = (k % 2 + 2 * ((k / 2) % 2 ^ ys.length)) +
                (2 * 2 ^ ys.length) * (k / 2 / 2 ^ ys.length) := by
              have hmul : (2 * 2 ^ ys.length) * (k / 2 / 2 ^ ys.length) =
                  2 * (2 ^ ys.length * (k / 2 / 2 ^ ys.length)) := by ring
              omega
            conv_lhs => rw [h5]
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
          cases hyb : s.basis y <;> cases hk2 : decide (k % 2 = 1)
          all_goals
            simp only [Bool.toNat_false, Bool.toNat_true, beq_self_eq_true, Bool.true_and,
              Bool.false_and, Bool.not_true, Bool.not_false, decide_eq_true_eq,
              decide_eq_false_iff_not, show (false == true) = false from rfl,
              show (true == false) = false from rfl] at hk2 ⊢
          · apply decide_eq_decide.mpr; omega
          · apply Eq.symm; apply decide_eq_false; omega
          · apply Eq.symm; apply decide_eq_false; omega
          · apply decide_eq_decide.mpr; omega
        simpa only [regValue, List.foldr_cons, List.length_cons, Bool.toNat,
          Bool.cond_eq_ite] using hbit
      dsimp only
      rw [hrun]
      refine ⟨hmid.1, ?_, ?_⟩
      · intro q hqR
        change writeBit s2.basis a false q = s.basis q
        by_cases hqa : q = a
        · subst q; simp [writeBit, hclean a (by simp)]
        · rw [show writeBit s2.basis a false q = s2.basis q by simp [writeBit, hqa]]
          exact (hmid.2.1 q hqR).trans (by simp [st1, writeBit, hqa])
      · rw [hr_val3]
        have hm2 := hmid.2.2
        rw [hr_val1, hcond] at hm2
        exact hm2

theorem eqToggle_counts (acc : Wire) (ys anc rs : List Wire) (k : Nat) (hl : ys.length = anc.length) :
    toffoliCount (eqToggle acc ys anc rs k) = ys.length ∧
    measurementCount (eqToggle acc ys anc rs k) = ys.length := by
  have h1 := andChain_counts acc ys anc k hl
  have h2 := signComplement_counts (anc.getLastD acc) rs
  have h3 := eraseAndChain_counts acc ys anc k hl
  simp only [eqToggle, toffoliCount_append, measurementCount_append, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  omega

theorem eqToggle_slots_le (acc : Wire) (ys anc rs : List Wire) (k : Nat) :
    gateSlots (eqToggle acc ys anc rs k) ≤ 7 * ys.length + rs.length := by
  have h1 := andChain_slots_le acc ys anc k
  have h2 := signComplement_gateSlots (anc.getLastD acc) rs
  have h3 := eraseAndChain_slots_le acc ys anc k
  simp only [eqToggle, gateSlots_append, h2]
  omega

theorem eqToggle_wires_sub (acc : Wire) (ys anc rs : List Wire) (k : Nat) :
    wires (eqToggle acc ys anc rs k) ⊆ (acc :: (ys ++ anc ++ rs)).toFinset := by
  have h1 := andChain_wires_sub acc ys anc k
  have h2 := signComplement_wires_subset (anc.getLastD acc) rs
  have h3 := eraseAndChain_wires_sub acc ys anc k
  have hlast : anc.getLastD acc ∈ acc :: anc := by
    cases anc with
    | nil => simp
    | cons a as =>
      right
      have : (a :: as).getLastD acc = (a :: as).getLast (by simp) := by
        cases as <;> simp [List.getLastD]
      rw [this]
      exact List.getLast_mem _
  intro q hq
  simp only [eqToggle, wires_append, Finset.mem_union] at hq
  rcases hq with (hq | hq) | hq
  · have m := h1 hq; simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at m ⊢; tauto
  · have m := h2 hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at m hlast ⊢
    rcases m with rfl | hqR
    · tauto
    · tauto
  · have m := h3 hq; simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at m ⊢; tauto

theorem eqToggle_physical (acc : Wire) (ys anc rs : List Wire) (k : Nat)
    (hn : (acc :: (ys ++ anc ++ rs)).Nodup) : GatePhysical (eqToggle acc ys anc rs k) := by
  have ct := List.nodup_iff_count.mp hn
  have hnd1 : (acc :: (ys ++ anc)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have := ct q; simp only [List.count_cons, List.count_append] at this ⊢; omega
  have hlast : anc.getLastD acc ∈ acc :: anc := by
    cases anc with
    | nil => simp
    | cons a as =>
      right
      have : (a :: as).getLastD acc = (a :: as).getLast (by simp) := by
        cases as <;> simp [List.getLastD]
      rw [this]
      exact List.getLast_mem _
  have hflagR : anc.getLastD acc ∉ rs := by
    intro bad
    have := ct (anc.getLastD acc)
    have posR := List.count_pos_iff.mpr bad
    rcases List.mem_cons.mp hlast with e | mem
    · rw [e] at this posR
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this
      omega
    · have posA := List.count_pos_iff.mpr mem
      simp only [List.count_cons, List.count_append] at this
      omega
  simp only [eqToggle, gatePhysical_append]
  exact ⟨⟨andChain_physical acc ys anc k hnd1, signComplement_physical _ rs hflagR⟩,
    eraseAndChain_physical acc ys anc k hnd1⟩

theorem eraseCopy_counts (j : Wire) (xs ys : List Wire) (hl : xs.length = ys.length) :
    toffoliCount (eraseCopy j xs ys) = 0 ∧ measurementCount (eraseCopy j xs ys) = xs.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [eraseCopy, toffoliCount, measurementCount]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have h := ih ys (by simpa using hl)
      simp only [eraseCopy, toffoliCount_append, measurementCount_append, toffoliCount,
        measurementCount, h.1, h.2, List.length_cons]
      exact ⟨trivial, Nat.add_comm _ _⟩

theorem eraseCopy_slots (j : Wire) (xs ys : List Wire) (hl : xs.length = ys.length) :
    gateSlots (eraseCopy j xs ys) = 2 * xs.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [eraseCopy]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have h := ih ys (by simpa using hl)
      simp only [eraseCopy, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots,
        h, List.length_cons, List.length_nil]
      omega

theorem eraseCopy_wires_sub (j : Wire) (xs ys : List Wire) :
    wires (eraseCopy j xs ys) ⊆ (j :: (xs ++ ys)).toFinset := by
  induction xs generalizing ys with
  | nil => simp [eraseCopy, wires]
  | cons x xs ih =>
    cases ys with
    | nil => simp [eraseCopy, wires]
    | cons y ys =>
      intro q hq
      simp only [eraseCopy, wires_append, Finset.mem_union] at hq
      rcases hq with hq | hq
      · simp only [wires, Instr.wires, correctionWires, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, Finset.notMem_empty, or_false] at hq
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append]; tauto
      · have m := ih ys hq
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at m ⊢; tauto

theorem eraseCopy_physical (j : Wire) (xs ys : List Wire) (hn : (j :: (xs ++ ys)).Nodup) :
    GatePhysical (eraseCopy j xs ys) := by
  induction xs generalizing ys with
  | nil => simp [eraseCopy, GatePhysical]
  | cons x xs ih =>
    cases ys with
    | nil => simp [eraseCopy, GatePhysical]
    | cons y ys =>
      obtain ⟨hjx, hjy, hxy, _⟩ := nodup_head3 hn
      have ct := List.nodup_iff_count.mp hn
      have hnd' : (j :: (xs ++ ys)).Nodup := by
        apply List.nodup_iff_count.mpr
        intro q; have := ct q; simp only [List.count_cons, List.count_append] at this ⊢; omega
      simp only [eraseCopy, gatePhysical_append]
      exact ⟨by simp [GatePhysical, PhysicalInstr, hjx, hjy, hxy, Ne.symm hjx, Ne.symm hjy, Ne.symm hxy],
        ih ys hnd'⟩

theorem eraseCopy_correct (j : Wire) (xs ys : List Wire) (hl : xs.length = ys.length)
    (hn : (j :: (xs ++ ys)).Nodup) (s : State) (m : List Bool)
    (hval : regValue ys s.basis = if s.basis j then regValue xs s.basis else 0) :
    let out := run (eraseCopy j xs ys) m s
    out.phase = s.phase ∧
    (∀ q, q ∉ ys → out.basis q = s.basis q) ∧
    regValue ys out.basis = 0 := by
  induction xs generalizing ys s m with
  | nil =>
    cases ys with
    | nil => simp [eraseCopy, run, regValue]
    | cons _ _ => simp at hl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      obtain ⟨_, hjy, hxy, _⟩ := nodup_head3 hn
      have ct := List.nodup_iff_count.mp hn
      have hy_ys : y ∉ ys := by
        intro bad; have := ct y; have pos := List.count_pos_iff.mpr bad
        simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
      have hy_xs : y ∉ xs := by
        intro bad; have := ct y; have pos := List.count_pos_iff.mpr bad
        simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
      have hnd' : (j :: (xs ++ ys)).Nodup := by
        apply List.nodup_iff_count.mpr
        intro q; have := ct q; simp only [List.count_cons, List.count_append] at this ⊢; omega
      have hval' : (if s.basis y then 1 else 0) + 2 * regValue ys s.basis =
          if s.basis j then (if s.basis x then 1 else 0) + 2 * regValue xs s.basis else 0 := hval
      have hy_bit : s.basis y = (s.basis j && s.basis x) ∧
          regValue ys s.basis = if s.basis j then regValue xs s.basis else 0 := by
        cases hjb : s.basis j <;> cases hxb : s.basis x <;> cases hyb : s.basis y <;>
          simp [hjb, hxb, hyb] at hval' ⊢ <;> omega
      have hstep1 := eraseAnd_single j x y hjy hxy s (m.take 1) hy_bit.1
      let st1 : State := ⟨s.phase, writeBit s.basis y false⟩
      have hval1 : regValue ys st1.basis = if st1.basis j then regValue xs st1.basis else 0 := by
        rw [show st1.basis j = s.basis j by simp [st1, writeBit, hjy],
          regValue_congr ys st1.basis s.basis (fun q hq => by
            simp [st1, writeBit, show q ≠ y from fun e => hy_ys (e ▸ hq)]),
          regValue_congr xs st1.basis s.basis (fun q hq => by
            simp [st1, writeBit, show q ≠ y from fun e => hy_xs (e ▸ hq)])]
        exact hy_bit.2
      have htail := ih ys (by simpa using hl) hnd' st1 (m.drop 1) hval1
      have hrun : run (eraseCopy j (x :: xs) (y :: ys)) m s = run (eraseCopy j xs ys) (m.drop 1) st1 := by
        simp only [eraseCopy, run_append, show measurementCount [.measureX y [] [.CZ j x]] = 1 from rfl,
          hstep1]
        rfl
      dsimp only
      rw [hrun]
      refine ⟨htail.1, ?_, ?_⟩
      · intro q hq
        have hqy : q ≠ y := fun e => hq (by simp [e])
        have hqys : q ∉ ys := fun e => hq (by simp [e])
        exact (htail.2.1 q hqys).trans (by simp [st1, writeBit, hqy])
      · change (if (run (eraseCopy j xs ys) (m.drop 1) st1).basis y then 1 else 0) +
            2 * regValue ys (run (eraseCopy j xs ys) (m.drop 1) st1).basis = 0
        rw [htail.2.2, htail.2.1 y hy_ys]
        simp [st1, writeBit]

end ECDSAAdd.Entrant.JointOdd1588
end

-- ============================================================================
-- Section 2A: Clean-carry half-step adder and shift/unshift kernels
-- ============================================================================
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.JointOdd1588
open ECDSAAdd Arithmetic Challenge Baselines BalancedCircuit BalancedField Secp256k1 RecordedQuantum
open EntryRetained5 JointInverse1588

/-- The 252 clean carry wires of `L.carry.take 254` excluding indices `4` and `248`. -/
def cleanCarries (L : Layout) : List Wire :=
  L.carry.take 4 ++ (L.carry.drop 5).take 243 ++ (L.carry.drop 249).take 5

/-- The 256 clean work wires (four scalars plus `cleanCarries L`) for `eqToggle`. -/
def eqAncillas (L : Layout) : List Wire :=
  [L.parity, L.lower, L.one, L.sign] ++ cleanCarries L

/-- The 253 mapped constant bits for bits `3..255` of `±(q+1)/2` controlled by `ctl`. -/
def oddHalfBits (ctl : Wire) : List MappedBit :=
  (List.range' 3 253).map fun i => { wire := some ctl, flip := !(oddHalfConst.testBit i) }

/-- Adds `(if L.parity then (q+1)/2 else -(q+1)/2)` mod `2^256` into `L.r` in `252 T / 252 M`. -/
def addHalfOdd (L : Layout) : Program :=
  mappedAdd (oddHalfBits L.parity) (L.r.drop 3) (cleanCarries L) (L.r.getD 2 0) ++
  [.X (L.r.getD 2 0)]

/-- Forward odd-word halving on `L.r`: `w ↦ oddHalfSigned w` for `-q - 1 ≤ w ≤ q`. -/
def shiftHalfOdd (L : Layout) : Program :=
  [.CX L.r0 L.parity, .CX L.parity L.r0] ++
  rotateRight L.r ++
  [.CX (L.r.getD 254 0) L.rmsb] ++
  addHalfOdd L ++
  [.CX L.rmsb L.parity, .X L.parity]

/-- Inverse odd-word unhalving on `L.r`: `oddHalfSigned w ↦ w` for `-q - 1 ≤ w ≤ q`. -/
def unshiftHalfOdd (L : Layout) : Program :=
  [.CX L.rmsb L.parity] ++
  addHalfOdd L ++
  [.X L.parity, .CX (L.r.getD 254 0) L.rmsb] ++
  rotateLeft L.r ++
  [.CX L.parity L.r0, .CX L.r0 L.parity]

theorem cleanCarries_length (L : Layout) (hw : L.Widths) : (cleanCarries L).length = 252 := by
  have hc := hw.2.2
  simp only [cleanCarries, List.length_append, List.length_take, List.length_drop, hc]
  omega

theorem eqAncillas_length (L : Layout) (hw : L.Widths) : (eqAncillas L).length = 256 := by
  simp only [eqAncillas, List.length_append, List.length_cons, List.length_nil,
    cleanCarries_length L hw]

theorem cleanCarries_mem_take254 (L : Layout) (hw : L.Widths) (q : Wire) (hq : q ∈ cleanCarries L) :
    q ∈ L.carry.take 254 := by
  have hc := hw.2.2
  simp only [cleanCarries, List.mem_append] at hq
  rcases hq with (h | h) | h
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    simp only [List.length_take, hc] at hi
    rw [List.getElem_take]
    have hi254 : i < (L.carry.take 254).length := by simp only [List.length_take, hc]; omega
    have eq : L.carry[i] = (L.carry.take 254)[i] := (List.getElem_take (h := hi254)).symm
    rw [eq]; exact List.getElem_mem hi254
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    simp only [List.length_take, List.length_drop, hc] at hi
    rw [List.getElem_take, List.getElem_drop]
    have hi254 : 5 + i < (L.carry.take 254).length := by simp only [List.length_take, hc]; omega
    have eq : L.carry[5 + i] = (L.carry.take 254)[5 + i] := (List.getElem_take (h := hi254)).symm
    rw [eq]; exact List.getElem_mem hi254
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    simp only [List.length_take, List.length_drop, hc] at hi
    rw [List.getElem_take, List.getElem_drop]
    have hi254 : 249 + i < (L.carry.take 254).length := by simp only [List.length_take, hc]; omega
    have eq : L.carry[249 + i] = (L.carry.take 254)[249 + i] := (List.getElem_take (h := hi254)).symm
    rw [eq]; exact List.getElem_mem hi254

theorem cleanCarries_sublist (L : Layout) (hw : L.Widths) : (cleanCarries L).Sublist L.carry := by
  have _ := hw
  have hdrop (a b : Nat) : L.carry.drop a = (L.carry.drop a).take b ++ L.carry.drop (a + b) := by
    have h := (List.take_append_drop b (L.carry.drop a)).symm
    rw [List.drop_drop] at h
    exact h
  have hcarry : L.carry = L.carry.take 4 ++
      ((L.carry.drop 4).take 1 ++ ((L.carry.drop 5).take 243 ++
        ((L.carry.drop 248).take 1 ++ ((L.carry.drop 249).take 5 ++ L.carry.drop 254)))) := by
    conv_lhs =>
      rw [← List.take_append_drop 4 L.carry, hdrop 4 1, hdrop 5 243, hdrop 248 1, hdrop 249 5]
  rw [hcarry, cleanCarries, List.append_assoc]
  refine List.Sublist.append (List.Sublist.refl _) ?_
  refine List.sublist_append_of_sublist_right ?_
  refine List.Sublist.append (List.Sublist.refl _) ?_
  refine List.sublist_append_of_sublist_right ?_
  exact List.sublist_append_left _ _

theorem cleanCarries_nodup (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (cleanCarries L).Nodup :=
  (carry_nodup L hn).sublist (cleanCarries_sublist L hw)

theorem cleanCarries_avoid (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    cLo L ∉ cleanCarries L ∧ cAt L 248 ∉ cleanCarries L ∧ cHi L ∉ cleanCarries L := by
  have hc := hw.2.2
  have nd := carry_nodup L hn
  have aux (k : Nat) (hk : k = 4 ∨ k = 248 ∨ k = 254) : L.carry.getD k 0 ∉ cleanCarries L := by
    intro hmem
    have hlt : k < L.carry.length := by rw [hc]; rcases hk with rfl | rfl | rfl <;> decide
    rw [List.getD_eq_getElem _ _ hlt] at hmem
    simp only [cleanCarries, List.mem_append] at hmem
    rcases hmem with (h | h) | h
    · obtain ⟨i, hi, eq⟩ := List.getElem_of_mem h
      simp only [List.length_take, hc] at hi
      rw [List.getElem_take] at eq
      have := (List.Nodup.getElem_inj_iff nd).mp eq
      omega
    · obtain ⟨i, hi, eq⟩ := List.getElem_of_mem h
      simp only [List.length_take, List.length_drop, hc] at hi
      rw [List.getElem_take, List.getElem_drop] at eq
      have := (List.Nodup.getElem_inj_iff nd).mp eq
      omega
    · obtain ⟨i, hi, eq⟩ := List.getElem_of_mem h
      simp only [List.length_take, List.length_drop, hc] at hi
      rw [List.getElem_take, List.getElem_drop] at eq
      have := (List.Nodup.getElem_inj_iff nd).mp eq
      omega
  exact ⟨aux 4 (Or.inl rfl), aux 248 (Or.inr (Or.inl rfl)), aux 254 (Or.inr (Or.inr rfl))⟩

theorem oddHalfBits_length (ctl : Wire) : (oddHalfBits ctl).length = 253 := by
  simp [oddHalfBits]

theorem oddHalfBits_wires (ctl : Wire) (q : Wire) (hq : q ∈ mappedWires (oddHalfBits ctl)) :
    q = ctl := by
  unfold mappedWires oddHalfBits at hq
  simp only [List.mem_flatMap, List.mem_map, List.mem_range'_1] at hq
  obtain ⟨_, ⟨_, _, rfl⟩, hmem⟩ := hq
  simpa using hmem

private theorem foldr_testBit_range' (m off n : Nat) :
    (List.range' off n).foldr (fun i acc => (m.testBit i).toNat + 2 * acc) 0 =
      (m / 2 ^ off) % 2 ^ n := by
  induction n generalizing off with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [List.range'_succ, List.foldr_cons, ih (off + 1)]
    have hbit : m.testBit off = decide ((m / 2 ^ off) % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
    have hdiv : m / 2 ^ (off + 1) = (m / 2 ^ off) / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    rw [hbit, hdiv, Nat.pow_succ']
    let x := m / 2 ^ off
    have h1 := Nat.div_add_mod x 2
    have h2 := Nat.div_add_mod (x / 2) (2 ^ n)
    have h3 := Nat.mod_lt x (by decide : 0 < 2)
    have h4 := Nat.mod_lt (x / 2) (Nat.two_pow_pos n)
    have hmul : (2 * 2 ^ n) * (x / 2 / 2 ^ n) = 2 * (2 ^ n * (x / 2 / 2 ^ n)) := by ring
    have h5 : x = (x % 2 + 2 * ((x / 2) % 2 ^ n)) + (2 * 2 ^ n) * (x / 2 / 2 ^ n) := by omega
    have h6 : x % (2 * 2 ^ n) = x % 2 + 2 * ((x / 2) % 2 ^ n) := by
      conv_lhs => rw [h5]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [h6]
    cases hx : decide (x % 2 = 1)
    · have hx0 : x % 2 = 0 := by simp only [decide_eq_false_iff_not] at hx; omega
      simp only [Bool.toNat_false, hx0, Nat.zero_add]; rfl
    · have hx1 : x % 2 = 1 := by simpa only [decide_eq_true_eq] using hx
      simp only [Bool.toNat_true, hx1]; rfl

theorem oddHalfBits_value (ctl : Wire) (b : BasisState) :
    mappedValue (oddHalfBits ctl) b = if b ctl then oddHalfConst / 8 else negOddHalfConst / 8 := by
  have hs := oddHalfStep_facts
  have hmap (l : List Nat) :
      mappedValue (l.map fun i => { wire := some ctl, flip := !(oddHalfConst.testBit i) }) b =
      l.foldr (fun i acc =>
        (if b ctl then oddHalfConst.testBit i else !(oddHalfConst.testBit i)).toNat + 2 * acc) 0 := by
    induction l with
    | nil => rfl
    | cons i is ih =>
      simp only [List.map_cons, mappedValue, MappedBit.value, Option.map_some, Option.getD_some,
        List.foldr_cons, ih]
      cases b ctl <;> cases oddHalfConst.testBit i <;> rfl
  rw [oddHalfBits, hmap]
  cases hc : b ctl
  · simp only [Bool.false_eq_true, if_false]
    have hcongr (l : List Nat) (hl : ∀ i ∈ l, 3 ≤ i ∧ i < 256) :
        l.foldr (fun i acc => (!(oddHalfConst.testBit i)).toNat + 2 * acc) 0 =
        l.foldr (fun i acc => (negOddHalfConst.testBit i).toNat + 2 * acc) 0 := by
      induction l with
      | nil => rfl
      | cons i is ih =>
        have hi := hl i (by simp)
        simp only [List.foldr_cons, negOddHalf_bit_eq i hi.1 hi.2,
          ih (fun j hj => hl j (by simp [hj]))]
    rw [hcongr (List.range' 3 253) (fun i hi => by simp only [List.mem_range'_1] at hi; omega),
      foldr_testBit_range', show (2 : Nat) ^ 3 = 8 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [if_true]
    rw [foldr_testBit_range', show (2 : Nat) ^ 3 = 8 from rfl]
    exact Nat.mod_eq_of_lt (by omega)

theorem regValue_testBit (rs : List Wire) (b : BasisState) (i : Nat) (hi : i < rs.length) :
    (regValue rs b).testBit i = b (rs.getD i 0) := by
  induction rs generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [regValue, List.foldr_cons, List.getD_cons_zero, Nat.testBit_zero]
      cases b r <;> simp
    | succ i =>
      change (((if b r then 1 else 0) + 2 * regValue rs b)).testBit (i + 1) = b (rs.getD i 0)
      rw [Nat.testBit_succ]
      have hdiv : ((if b r then 1 else 0) + 2 * regValue rs b) / 2 = regValue rs b := by
        cases b r <;> (simp only [Bool.false_eq_true, if_false, if_true]; omega)
      rw [hdiv]
      exact ih i (by simpa using hi)

theorem regValue_update_at (rs : List Wire) (b : BasisState) (i : Nat)
    (hn : rs.Nodup) (hi : i < rs.length) (v : Bool) :
    regValue rs (writeBit b (rs.getD i 0) v) =
      regValue rs b + (if v then 2 ^ i else 0) - (if b (rs.getD i 0) then 2 ^ i else 0) := by
  induction rs generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    have hnd := List.nodup_cons.mp hn
    cases i with
    | zero =>
      have hsame : regValue rs (writeBit b r v) = regValue rs b :=
        regValue_congr rs _ _ (fun q hq => by
          simp [writeBit, show q ≠ r from fun e => hnd.1 (e ▸ hq)])
      change (if writeBit b r v r then 1 else 0) + 2 * regValue rs (writeBit b r v) =
        (if b r then 1 else 0) + 2 * regValue rs b + (if v then 2 ^ 0 else 0) -
          (if b r then 2 ^ 0 else 0)
      rw [hsame, writeBit, Function.update_self, pow_zero]
      cases v <;> cases b r <;> (simp only [Bool.false_eq_true, if_true, if_false]; omega)
    | succ i =>
      have hi' : i < rs.length := by simpa using hi
      have hmem : rs.getD i 0 ∈ rs := by
        rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi'
      have hne : r ≠ rs.getD i 0 := fun e => hnd.1 (e ▸ hmem)
      have hsub := ih i hnd.2 hi'
      have hbound : (if b (rs.getD i 0) then 2 ^ i else 0) ≤ regValue rs b := by
        cases hb : b (rs.getD i 0)
        · simp
        · have ht := regValue_testBit rs b i hi'
          rw [hb] at ht
          have := Nat.ge_two_pow_of_testBit ht
          simpa using this
      change (if writeBit b (rs.getD i 0) v r then 1 else 0) +
          2 * regValue rs (writeBit b (rs.getD i 0) v) =
        (if b r then 1 else 0) + 2 * regValue rs b + (if v then 2 ^ (i + 1) else 0) -
          (if b (rs.getD i 0) then 2 ^ (i + 1) else 0)
      rw [hsub, writeBit, Function.update_of_ne hne, Nat.pow_succ']
      cases b r <;> cases v <;> cases hbi : b (rs.getD i 0)
      all_goals
        simp only [hbi, Bool.false_eq_true, if_true, if_false] at hbound ⊢
        omega

private theorem short_add_lift (a u k : Nat) (B : Bool) (ha : a < 4) :
    a + 4 * (!B).toNat + 8 * ((u + k + B.toNat) % 2 ^ 253) =
      (a + 4 * B.toNat + 8 * u + (4 + 8 * k)) % 2 ^ 256 := by
  have hp : 2 ^ 256 = 8 * 2 ^ 253 := by decide
  rw [hp]
  cases B
  · simp only [Bool.not_false, Bool.toNat_true, Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    have hlt : a + 4 + 8 * ((u + k) % 2 ^ 253) < 8 * 2 ^ 253 := by
      have := Nat.mod_lt (u + k) (Nat.two_pow_pos 253); omega
    have hEq : a + 8 * u + (4 + 8 * k) = (a + 4 + 8 * ((u + k) % 2 ^ 253)) +
        (8 * 2 ^ 253) * ((u + k) / 2 ^ 253) := by
      have := Nat.div_add_mod (u + k) (2 ^ 253); omega
    conv_rhs => rw [hEq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · simp only [Bool.not_true, Bool.toNat_true, Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    have hlt : a + 8 * ((u + k + 1) % 2 ^ 253) < 8 * 2 ^ 253 := by
      have := Nat.mod_lt (u + k + 1) (Nat.two_pow_pos 253); omega
    have hEq : a + 4 + 8 * u + (4 + 8 * k) = (a + 8 * ((u + k + 1) % 2 ^ 253)) +
        (8 * 2 ^ 253) * ((u + k + 1) / 2 ^ 253) := by
      have := Nat.div_add_mod (u + k + 1) (2 ^ 253); omega
    conv_rhs => rw [hEq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem addHalfOdd_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (addHalfOdd L) = 252 ∧ measurementCount (addHalfOdd L) = 252 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h1 := mappedAdd_counts (oddHalfBits L.parity) (L.r.drop 3) (cleanCarries L) (L.r.getD 2 0)
    (by simp [oddHalfBits_length, len.2.1])
    (by simp [cleanCarries_length L hw, len.2.1])
  simp only [addHalfOdd, toffoliCount_append, measurementCount_append, h1.1, h1.2,
    toffoliCount, measurementCount, List.length_drop, len.2.1]
  exact ⟨trivial, trivial⟩

theorem addHalfOdd_slots_le (L : Layout) : gateSlots (addHalfOdd L) ≤ 4302 := by
  have h1 := mappedAdd_gateSlots_le (oddHalfBits L.parity) (L.r.drop 3) (cleanCarries L) (L.r.getD 2 0)
  rw [oddHalfBits_length] at h1
  simp only [addHalfOdd, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots]
  omega

theorem addHalfOdd_wires_sub (L : Layout) (hw : L.Widths) :
    wires (addHalfOdd L) ⊆ (L.parity :: (L.r ++ cleanCarries L)).toFinset := by
  have len := BalancedCleanup.widths L.toLayout hw
  have hr2 : L.r.getD 2 0 ∈ L.r := by
    rw [List.getD_eq_getElem _ _ (by rw [len.2.1]; decide)]
    exact List.getElem_mem _
  have h1 := mappedAdd_wires_subset (oddHalfBits L.parity) (L.r.drop 3) (cleanCarries L) (L.r.getD 2 0)
  intro q hq
  simp only [addHalfOdd, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · have m := h1 hq
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at m
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    rcases m with ((h | h) | h) | rfl
    · exact Or.inl (oddHalfBits_wires L.parity q h)
    · exact Or.inr (Or.inl (List.mem_of_mem_drop h))
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl hr2)
  · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
      or_false] at hq
    subst q
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl hr2)

theorem addHalfOdd_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (addHalfOdd L) := by
  have len := BalancedCleanup.widths L.toLayout hw
  have ndData : (L.r ++ L.carry).Nodup := by
    have nd := allND L hn
    apply List.nodup_iff_count.mpr
    intro q; have := List.nodup_iff_count.mp nd q
    simp only [List.count_append] at this ⊢; omega
  have hsubR : (L.r.getD 2 0 :: L.r.drop 3).Sublist L.r := by
    match hr : L.r with
    | a :: b :: c :: rest =>
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
      exact List.Sublist.cons a (List.Sublist.cons b (List.Sublist.refl _))
    | [] | [_] | [_, _] => simp [hr] at len
  have hndAdd : (L.r.getD 2 0 :: L.r.drop 3 ++ cleanCarries L).Nodup :=
    ndData.sublist (hsubR.append (cleanCarries_sublist L hw))
  have hparAway : ∀ b ∈ oddHalfBits L.parity, ∀ q ∈ b.wire,
      q ∉ L.r.getD 2 0 :: L.r.drop 3 ++ cleanCarries L := by
    intro b hb q hq bad
    have eq : q = L.parity := by
      simp only [oddHalfBits, List.mem_map] at hb
      obtain ⟨_, _, rfl⟩ := hb; exact (Option.mem_some_iff.mp hq).symm
    subst eq
    have f := flagAway L hn L.parity (by simp)
    have hr2 : L.r.getD 2 0 ∈ L.r := by
      rw [List.getD_eq_getElem _ _ (by rw [len.2.1]; decide)]; exact List.getElem_mem _
    rcases List.mem_append.mp bad with h | h
    · rcases List.mem_cons.mp h with e | h
      · exact f (by rw [e]; exact List.mem_append_left _ (List.mem_append_left _ hr2))
      · exact f (by simp [List.mem_of_mem_drop h])
    · exact f (by simp [(cleanCarries_sublist L hw).subset h])
  simp only [addHalfOdd, gatePhysical_append]
  exact ⟨mappedAdd_physical (oddHalfBits L.parity) (L.r.drop 3) (cleanCarries L) (L.r.getD 2 0)
    hndAdd hparAway, by simp [GatePhysical, PhysicalInstr, ProperGate]⟩

theorem addHalfOdd_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hclean : ∀ q ∈ cleanCarries L, s.basis q = false) :
    let out := run (addHalfOdd L) m s
    out.phase = s.phase ∧
    (∀ q, q ∉ L.r → out.basis q = s.basis q) ∧
    regValue L.r out.basis =
      (regValue L.r s.basis + if s.basis L.parity then oddHalfConst else negOddHalfConst) % 2 ^ 256 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have hs := oddHalfStep_facts
  match hr : L.r with
  | r0 :: r1 :: r2 :: rest =>
    have hrest : rest.length = 253 := by have := len.2.1; rw [hr] at this; simp at this; omega
    have ndData : (L.r ++ L.carry).Nodup := by
      have nd := allND L hn
      apply List.nodup_iff_count.mpr
      intro q; have := List.nodup_iff_count.mp nd q
      simp only [List.count_append] at this ⊢; omega
    have hndAdd : (r2 :: (rest ++ cleanCarries L)).Nodup := by
      have hsub : (r2 :: rest).Sublist (r0 :: r1 :: r2 :: rest) :=
        List.Sublist.cons r0 (List.Sublist.cons r1 (List.Sublist.refl _))
      rw [hr] at ndData
      exact ndData.sublist (hsub.append (cleanCarries_sublist L hw))
    have hparAway : ∀ q ∈ mappedWires (oddHalfBits L.parity), q ∉ r2 :: (rest ++ cleanCarries L) := by
      intro q hq bad
      have eq := oddHalfBits_wires L.parity q hq; subst eq
      have f := flagAway L hn L.parity (by simp)
      rw [hr] at f
      simp only [List.mem_cons, List.mem_append] at bad
      rcases bad with rfl | h | h
      · exact f (by simp)
      · exact f (by simp [h])
      · exact f (by simp [(cleanCarries_sublist L hw).subset h])
    have hma := mappedAdd_correct (oddHalfBits L.parity) rest (cleanCarries L) r2 hndAdd hparAway
      (by rw [oddHalfBits_length, hrest]) (by rw [cleanCarries_length L hw, hrest]) s m hclean
    let st1 := run (mappedAdd (oddHalfBits L.parity) rest (cleanCarries L) r2) m s
    have hrun : run (addHalfOdd L) m s = ⟨st1.phase, writeBit st1.basis r2 (!st1.basis r2)⟩ := by
      have hm := (mappedAdd_counts (oddHalfBits L.parity) rest (cleanCarries L) r2
        (by rw [oddHalfBits_length, hrest]) (by rw [cleanCarries_length L hw, hrest])).2
      simp only [addHalfOdd, hr, List.drop_succ_cons, List.drop_zero, List.getD_cons_succ,
        List.getD_cons_zero, run_append, run_take]
      rfl
    have hndR : (r0 :: r1 :: r2 :: rest).Nodup := by
      rw [← hr]; exact (List.nodup_append'.mp ndData).1
    have hr02 : r0 ≠ r2 := by
      have := List.nodup_cons.mp hndR; intro e; exact this.1 (by simp [e])
    have hr12 : r1 ≠ r2 := by
      have := List.nodup_cons.mp (List.nodup_cons.mp hndR).2; intro e; exact this.1 (by simp [e])
    have hr0rest : r0 ∉ rest := by
      have := List.nodup_cons.mp hndR; intro h; exact this.1 (by simp [h])
    have hr1rest : r1 ∉ rest := by
      have := List.nodup_cons.mp (List.nodup_cons.mp hndR).2; intro h; exact this.1 (by simp [h])
    have hr2rest : r2 ∉ rest :=
      (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hndR).2).2).1
    dsimp only
    rw [hrun]
    refine ⟨hma.1, ?_, ?_⟩
    · intro q hq
      simp only [List.mem_cons, not_or] at hq
      have hqr2 : q ≠ r2 := hq.2.2.1
      have hqrest : q ∉ rest := hq.2.2.2
      change writeBit st1.basis r2 (!st1.basis r2) q = s.basis q
      rw [show writeBit st1.basis r2 (!st1.basis r2) q = st1.basis q by simp [writeBit, hqr2]]
      exact hma.2.1 q hqrest
    · have hs1_0 : st1.basis r0 = s.basis r0 := hma.2.1 r0 hr0rest
      have hs1_1 : st1.basis r1 = s.basis r1 := hma.2.1 r1 hr1rest
      have hs1_2 : st1.basis r2 = s.basis r2 := hma.2.1 r2 hr2rest
      have hs1_rest : regValue rest (writeBit st1.basis r2 (!st1.basis r2)) = regValue rest st1.basis :=
        regValue_congr rest _ _ (fun q hq => by simp [writeBit, show q ≠ r2 from fun e => hr2rest (e ▸ hq)])
      have hval1 : regValue rest st1.basis =
          (regValue rest s.basis + (if s.basis L.parity then oddHalfConst / 8 else negOddHalfConst / 8) +
            (s.basis r2).toNat) % 2 ^ 253 := by
        rw [hma.2.2, oddHalfBits_value, hrest, Nat.add_comm (if s.basis L.parity then _ else _)]
      have hlhs : regValue (r0 :: r1 :: r2 :: rest) (writeBit st1.basis r2 (!st1.basis r2)) =
          ((s.basis r0).toNat + 2 * (s.basis r1).toNat) + 4 * (!(s.basis r2)).toNat +
            8 * regValue rest st1.basis := by
        change (if writeBit st1.basis r2 (!st1.basis r2) r0 then 1 else 0) +
          2 * ((if writeBit st1.basis r2 (!st1.basis r2) r1 then 1 else 0) +
            2 * ((if writeBit st1.basis r2 (!st1.basis r2) r2 then 1 else 0) +
              2 * regValue rest (writeBit st1.basis r2 (!st1.basis r2)))) = _
        rw [hs1_rest]
        simp only [writeBit, Function.update_of_ne hr02, Function.update_of_ne hr12,
          Function.update_self, hs1_0, hs1_1, hs1_2]
        cases s.basis r0 <;> cases s.basis r1 <;> cases s.basis r2 <;> simp <;> omega
      have hsr : regValue (r0 :: r1 :: r2 :: rest) s.basis =
          ((s.basis r0).toNat + 2 * (s.basis r1).toNat) + 4 * (s.basis r2).toNat +
            8 * regValue rest s.basis := by
        change (if s.basis r0 then 1 else 0) +
          2 * ((if s.basis r1 then 1 else 0) +
            2 * ((if s.basis r2 then 1 else 0) + 2 * regValue rest s.basis)) = _
        cases s.basis r0 <;> cases s.basis r1 <;> cases s.basis r2 <;> simp <;> omega
      have haLt : (s.basis r0).toNat + 2 * (s.basis r1).toNat < 4 := by
        cases s.basis r0 <;> cases s.basis r1 <;> decide
      change regValue (r0 :: r1 :: r2 :: rest) (writeBit st1.basis r2 (!st1.basis r2)) = _
      rw [hlhs, hval1, hsr]
      cases hp : s.basis L.parity
      · simp only [Bool.false_eq_true, if_false]
        rw [show negOddHalfConst = 4 + 8 * (negOddHalfConst / 8) by omega]
        exact short_add_lift _ _ (negOddHalfConst / 8) (s.basis r2) haLt
      · simp only [if_true]
        rw [show oddHalfConst = 4 + 8 * (oddHalfConst / 8) by omega]
        exact short_add_lift _ _ (oddHalfConst / 8) (s.basis r2) haLt
  | [] | [_] | [_, _] => have := len.2.1; simp [hr] at this

end ECDSAAdd.Entrant.JointOdd1588
end

-- ============================================================================
-- Section 2B: `shiftHalfOdd`, `unshiftHalfOdd`, `paddedGD_odd`, `paddedD_odd`
-- ============================================================================
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.JointOdd1588
open ECDSAAdd Arithmetic Challenge Baselines BalancedCircuit BalancedField Secp256k1 RecordedQuantum
open EntryRetained5 JointInverse1588 MappedCompressed

theorem rotateRight_physical (xs : List Wire) (hn : xs.Nodup) : GatePhysical (rotateRight xs) := by
  induction xs with
  | nil => simp [rotateRight, GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil => simp [rotateRight, GatePhysical]
    | cons b bs =>
      have hnd := List.nodup_cons.mp hn
      have hab : a ≠ b := fun e => hnd.1 (by simp [e])
      simp only [rotateRight, gatePhysical_append]
      exact ⟨by simp [swapBits, GatePhysical, PhysicalInstr, ProperGate, hab, Ne.symm hab],
        ih hnd.2⟩

theorem rotateLeft_physical (xs : List Wire) (hn : xs.Nodup) : GatePhysical (rotateLeft xs) := by
  induction xs with
  | nil => simp [rotateLeft, GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil => simp [rotateLeft, GatePhysical]
    | cons b bs =>
      have hnd := List.nodup_cons.mp hn
      have hab : a ≠ b := fun e => hnd.1 (by simp [e])
      simp only [rotateLeft, gatePhysical_append]
      exact ⟨ih hnd.2,
        by simp [swapBits, GatePhysical, PhysicalInstr, ProperGate, hab, Ne.symm hab]⟩

theorem r_getD_0 (L : Layout) : L.r.getD 0 0 = L.r0 := rfl

theorem r_getD_255 (L : Layout) (hw : L.Widths) : L.r.getD 255 0 = L.rmsb := by
  have hlow : L.low.length = 255 := (BalancedCleanup.widths L.toLayout hw).1
  change (L.low ++ [L.rmsb]).getD 255 0 = L.rmsb
  rw [List.getD_eq_getElem _ _ (by simp [hlow]), List.getElem_append_right (by omega)]
  simp [hlow]

theorem r_nodup (L : Layout) (hn : L.wires.Nodup) : L.r.Nodup := by
  have nd := (List.nodup_append'.mp (allND L hn)).2.1
  exact (List.nodup_append'.mp (List.nodup_append'.mp nd).1).1

theorem y_nodup (L : Layout) (hn : L.wires.Nodup) : L.y.Nodup := by
  have nd := (List.nodup_append'.mp (allND L hn)).2.1
  exact (List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1

theorem r_254_ne_rmsb (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.r.getD 254 0 ≠ L.rmsb := by
  have len := (BalancedCleanup.widths L.toLayout hw).2.1
  have h255 := r_getD_255 L hw
  rw [← h255]
  intro e
  rw [List.getD_eq_getElem _ _ (by rw [len]; decide),
    List.getD_eq_getElem _ _ (by rw [len]; decide)] at e
  have := (List.Nodup.getElem_inj_iff (r_nodup L hn)).mp e
  omega

theorem r_mem_getD (L : Layout) (hw : L.Widths) (i : Nat) (hi : i < 256) :
    L.r.getD i 0 ∈ L.r := by
  have len := (BalancedCleanup.widths L.toLayout hw).2.1
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

theorem shiftHalfOdd_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (shiftHalfOdd L) = 252 ∧ measurementCount (shiftHalfOdd L) = 252 := by
  have hr := rotate_counts L.r
  have ha := addHalfOdd_counts L hw
  simp only [shiftHalfOdd, toffoliCount_append, measurementCount_append, hr.1, hr.2.1, ha.1, ha.2,
    toffoliCount, measurementCount]
  exact ⟨trivial, trivial⟩

theorem unshiftHalfOdd_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (unshiftHalfOdd L) = 252 ∧ measurementCount (unshiftHalfOdd L) = 252 := by
  have hr := rotate_counts L.r
  have ha := addHalfOdd_counts L hw
  simp only [unshiftHalfOdd, toffoliCount_append, measurementCount_append, hr.2.2.1, hr.2.2.2,
    ha.1, ha.2, toffoliCount, measurementCount]
  exact ⟨trivial, trivial⟩

theorem shiftHalfOdd_slots_le (L : Layout) (hw : L.Widths) :
    gateSlots (shiftHalfOdd L) ≤ 5075 := by
  have len := (BalancedCleanup.widths L.toLayout hw).2.1
  have hr := (rotate_gateSlots_le L.r).1
  rw [len] at hr
  have ha := addHalfOdd_slots_le L
  simp only [shiftHalfOdd, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots]
  omega

theorem unshiftHalfOdd_slots_le (L : Layout) (hw : L.Widths) :
    gateSlots (unshiftHalfOdd L) ≤ 5075 := by
  have len := (BalancedCleanup.widths L.toLayout hw).2.1
  have hr := (rotate_gateSlots_le L.r).2
  rw [len] at hr
  have ha := addHalfOdd_slots_le L
  simp only [unshiftHalfOdd, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots]
  omega

theorem shiftHalfOdd_wires_sub (L : Layout) (hw : L.Widths) :
    wires (shiftHalfOdd L) ⊆ (L.parity :: (L.r ++ cleanCarries L)).toFinset := by
  have hr0 : L.r0 ∈ L.r := by rw [← r_getD_0 L]; exact r_mem_getD L hw 0 (by decide)
  have hr254 : L.r.getD 254 0 ∈ L.r := r_mem_getD L hw 254 (by decide)
  have hrmsb : L.rmsb ∈ L.r := by rw [← r_getD_255 L hw]; exact r_mem_getD L hw 255 (by decide)
  have hrot := (rotate_wires L.r).1
  have ha := addHalfOdd_wires_sub L hw
  intro q hq
  simp only [shiftHalfOdd, wires_append, Finset.mem_union] at hq
  rcases hq with (((hq | hq) | hq) | hq) | hq
  · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, or_false] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    rcases hq with (rfl | rfl) | (rfl | rfl) <;> tauto
  · rw [hrot] at hq
    split_ifs at hq
    · simp at hq
    · simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hq ⊢; tauto
  · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, or_false] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    rcases hq with rfl | rfl <;> tauto
  · exact ha hq
  · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, or_false] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    rcases hq with (rfl | rfl) | rfl <;> tauto

theorem unshiftHalfOdd_wires_sub (L : Layout) (hw : L.Widths) :
    wires (unshiftHalfOdd L) ⊆ (L.parity :: (L.r ++ cleanCarries L)).toFinset := by
  have hr0 : L.r0 ∈ L.r := by rw [← r_getD_0 L]; exact r_mem_getD L hw 0 (by decide)
  have hr254 : L.r.getD 254 0 ∈ L.r := r_mem_getD L hw 254 (by decide)
  have hrmsb : L.rmsb ∈ L.r := by rw [← r_getD_255 L hw]; exact r_mem_getD L hw 255 (by decide)
  have hrot := (rotate_wires L.r).2
  have ha := addHalfOdd_wires_sub L hw
  intro q hq
  simp only [unshiftHalfOdd, wires_append, Finset.mem_union] at hq
  rcases hq with (((hq | hq) | hq) | hq) | hq
  · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, or_false] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    rcases hq with rfl | rfl <;> tauto
  · exact ha hq
  · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, or_false] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    rcases hq with rfl | (rfl | rfl) <;> tauto
  · rw [hrot] at hq
    split_ifs at hq
    · simp at hq
    · simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hq ⊢; tauto
  · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, or_false] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    rcases hq with (rfl | rfl) | (rfl | rfl) <;> tauto

theorem shiftHalfOdd_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (shiftHalfOdd L) := by
  have f := flagAway L hn L.parity (by simp)
  have hr0p : L.r0 ≠ L.parity := fun e => f (by rw [← e]; simp [BalancedCleanup.Layout.r, BalancedCleanup.Layout.low])
  have hrmsbp : L.rmsb ≠ L.parity := fun e => f (by rw [← e]; simp [BalancedCleanup.Layout.r])
  have h254 := r_254_ne_rmsb L hw hn
  simp only [shiftHalfOdd, gatePhysical_append]
  refine ⟨⟨⟨⟨?_, rotateRight_physical L.r (r_nodup L hn)⟩, ?_⟩, addHalfOdd_physical L hw hn⟩, ?_⟩
  · simp [GatePhysical, PhysicalInstr, ProperGate, hr0p, Ne.symm hr0p]
  · simp only [GatePhysical, List.mem_singleton, forall_eq, PhysicalInstr, ProperGate]; exact h254
  · simp [GatePhysical, PhysicalInstr, ProperGate, hrmsbp]

theorem unshiftHalfOdd_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (unshiftHalfOdd L) := by
  have f := flagAway L hn L.parity (by simp)
  have hr0p : L.r0 ≠ L.parity := fun e => f (by rw [← e]; simp [BalancedCleanup.Layout.r, BalancedCleanup.Layout.low])
  have hrmsbp : L.rmsb ≠ L.parity := fun e => f (by rw [← e]; simp [BalancedCleanup.Layout.r])
  have h254 := r_254_ne_rmsb L hw hn
  simp only [unshiftHalfOdd, gatePhysical_append]
  refine ⟨⟨⟨⟨?_, addHalfOdd_physical L hw hn⟩, ?_⟩, rotateLeft_physical L.r (r_nodup L hn)⟩, ?_⟩
  · simp [GatePhysical, PhysicalInstr, ProperGate, hrmsbp]
  · simp only [GatePhysical, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq,
      PhysicalInstr, ProperGate]; exact ⟨trivial, h254, by simp⟩
  · simp [GatePhysical, PhysicalInstr, ProperGate, hr0p, Ne.symm hr0p]

theorem shiftHalfOdd_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (w : Int) (hwB : -q - 1 ≤ w ∧ w ≤ q) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 w)
    (hP : s.basis L.parity = false)
    (hclean : ∀ c ∈ cleanCarries L, s.basis c = false) :
    let out := run (shiftHalfOdd L) m s
    out.phase = s.phase ∧
    (∀ q, q ∉ L.r → out.basis q = s.basis q) ∧
    regValue L.r out.basis = encodeWord 256 (oddHalfSigned w) := by
  have len := (BalancedCleanup.widths L.toLayout hw).2.1
  have hc := constants
  have hndR := r_nodup L hn
  have f := flagAway L hn L.parity (by simp)
  have hpNotR : L.parity ∉ L.r := fun h => f (by simp [h])
  have hr0p : L.r0 ≠ L.parity := fun e => hpNotR (by rw [← e]; exact r_mem_getD L hw 0 (by decide))
  have hrmsbp : L.rmsb ≠ L.parity := fun e => hpNotR (by rw [← e, ← r_getD_255 L hw]; exact r_mem_getD L hw 255 (by decide))
  have h254 := r_254_ne_rmsb L hw hn
  have hparBit : s.basis L.r0 = decide (w % 2 ≠ 0) := by
    have ht := regValue_testBit L.r s.basis 0 (by rw [len]; decide)
    rw [r_getD_0, hR, Nat.testBit_zero] at ht
    rw [← ht]
    exact decide_eq_decide.mpr (encodeWord_mod2 w)
  -- Step 1: [.CX L.r0 L.parity, .CX L.parity L.r0]
  let st1 := run [.CX L.r0 L.parity, .CX L.parity L.r0] [] s
  have hs1_phase : st1.phase = s.phase := rfl
  have hs1_out (u : Wire) (hu1 : u ≠ L.parity) (hu2 : u ≠ L.r0) : st1.basis u = s.basis u := by
    simp [st1, run, writeBit, hu1, hu2]
  have hs1_par : st1.basis L.parity = decide (w % 2 ≠ 0) := by
    simp [st1, run, writeBit, hr0p, Ne.symm hr0p, hP, hparBit]
  have hs1_r0 : st1.basis L.r0 = false := by
    simp [st1, run, writeBit, hr0p, Ne.symm hr0p, hP]
  have hs1_R : regValue L.r st1.basis = encodeWord 256 w - (encodeWord 256 w % 2) := by
    have heq : regValue L.r st1.basis = regValue L.r (writeBit s.basis (L.r.getD 0 0) false) := by
      apply regValue_congr
      intro u hu
      by_cases hu0 : u = L.r0
      · subst u; rw [hs1_r0, r_getD_0]; simp [writeBit]
      · rw [hs1_out u (fun e => hpNotR (e ▸ hu)) hu0, r_getD_0]; simp [writeBit, hu0]
    rw [heq, regValue_update_at L.r s.basis 0 hndR (by rw [len]; decide) false, r_getD_0, hR,
      hparBit, pow_zero]
    have hm2 := encodeWord_mod2 w
    by_cases hodd : w % 2 ≠ 0
    · simp only [decide_eq_true hodd, Bool.false_eq_true, if_false, if_true, Nat.add_zero]
      have h1 : encodeWord 256 w % 2 = 1 := hm2.mpr hodd
      omega
    · simp only [decide_eq_false hodd, Bool.false_eq_true, if_false, Nat.add_zero, Nat.sub_zero]
      have h0 : encodeWord 256 w % 2 = 0 := by
        have := Nat.mod_lt (encodeWord 256 w) (by decide : 0 < 2)
        have : encodeWord 256 w % 2 ≠ 1 := fun e => hodd (hm2.mp e)
        omega
      omega
  -- Step 2: rotateRight L.r
  let s2 := run (rotateRight L.r) [] st1
  have hrot_fr := rotate_frame L.r st1 []
  have hs2_phase : s2.phase = s.phase := hrot_fr.1
  have hs2_out (u : Wire) (hu : u ∉ L.r) : s2.basis u = st1.basis u := hrot_fr.2.1 u hu
  have hs2_R : regValue L.r s2.basis = encodeWord 256 w / 2 := by
    have heven : (encodeWord 256 w - encodeWord 256 w % 2) % 2 = 0 := by omega
    have hsp := rotateRight_spec L.r hndR (encodeWord 256 w - encodeWord 256 w % 2) heven st1 [] hs1_R
    have hdiv : (encodeWord 256 w - encodeWord 256 w % 2) / 2 = encodeWord 256 w / 2 := by omega
    rw [hdiv] at hsp
    exact hsp.2
  have hs2_254 : s2.basis (L.r.getD 254 0) = decide (w < 0) := by
    have ht := regValue_testBit L.r s2.basis 254 (by rw [len]; decide)
    rw [hs2_R, ← Nat.testBit_succ, encodeWord_testBit255 w (by omega) (by omega)] at ht
    exact ht.symm
  have hs2_255 : s2.basis L.rmsb = false := by
    have ht := regValue_testBit L.r s2.basis 255 (by rw [len]; decide)
    rw [r_getD_255 L hw, hs2_R] at ht
    have hlt : encodeWord 256 w / 2 < 2 ^ 255 := by
      unfold encodeWord; omega
    rw [Nat.testBit_lt_two_pow hlt] at ht
    exact ht.symm
  -- Step 3: [.CX (L.r.getD 254 0) L.rmsb]
  let s3 := run [.CX (L.r.getD 254 0) L.rmsb] [] s2
  have hs3_phase : s3.phase = s.phase := hs2_phase
  have hs3_out (u : Wire) (hu : u ∉ L.r) : s3.basis u = st1.basis u := by
    have hne : u ≠ L.rmsb := fun e => hu (by rw [e, ← r_getD_255 L hw]; exact r_mem_getD L hw 255 (by decide))
    change writeBit s2.basis L.rmsb (s2.basis L.rmsb ^^ s2.basis (L.r.getD 254 0)) u = st1.basis u
    rw [writeBit, Function.update_of_ne hne]
    exact hs2_out u hu
  have hs3_R : regValue L.r s3.basis = encodeWord 256 (w / 2) := by
    have hupd : s3.basis = writeBit s2.basis (L.r.getD 255 0) (decide (w < 0)) := by
      change writeBit s2.basis L.rmsb (s2.basis L.rmsb ^^ s2.basis (L.r.getD 254 0)) = _
      rw [r_getD_255 L hw, hs2_255, hs2_254, Bool.false_xor]
    rw [hupd, regValue_update_at L.r s2.basis 255 hndR (by rw [len]; decide) (decide (w < 0)),
      r_getD_255 L hw, hs2_255, hs2_R, encodeWord_asr w (by omega) (by omega)]
    by_cases hneg : w < 0 <;> simp [hneg]
  -- Step 4: addHalfOdd L
  have hclean3 : ∀ c ∈ cleanCarries L, s3.basis c = false := by
    intro c hc'
    have cNotR : c ∉ L.r := carry_not_r L hn c ((cleanCarries_sublist L hw).subset hc')
    have cNeP : c ≠ L.parity := fun e => f (by rw [← e]; simp [(cleanCarries_sublist L hw).subset hc'])
    have cNe0 : c ≠ L.r0 := fun e => cNotR (by rw [e]; exact r_mem_getD L hw 0 (by decide))
    rw [hs3_out c cNotR, hs1_out c cNeP cNe0]
    exact hclean c hc'
  let s4 := run (addHalfOdd L) m s3
  have hadd := addHalfOdd_correct L hw hn s3 m hclean3
  have hs4_par : s4.basis L.parity = decide (w % 2 ≠ 0) :=
    (hadd.2.1 L.parity hpNotR).trans ((hs3_out L.parity hpNotR).trans hs1_par)
  have hs4_R : regValue L.r s4.basis = encodeWord 256 (oddHalfSigned w) := by
    have hr4 := hadd.2.2
    rw [hs3_R, hs3_out L.parity hpNotR, hs1_par] at hr4
    have hmod := oddHalf_mod_eq w hwB
    simp only [decide_eq_true_eq] at hr4
    exact hr4.trans hmod
  have hs4_rmsb : s4.basis L.rmsb = !(decide (w % 2 ≠ 0)) := by
    have ht := regValue_testBit L.r s4.basis 255 (by rw [len]; decide)
    rw [r_getD_255 L hw, hs4_R] at ht
    by_cases hwq : w = q
    · subst hwq
      have hq := oddHalfSigned_q
      rw [hq.1, encodeWord_testBit255 q (by omega) (by omega)] at ht
      simp [hq.2.1, hq.2.2] at ht ⊢
      exact ht
    · have hdom : OddDomain w := ⟨hwB.1, by omega⟩
      have hd := oddHalfSigned_domain w hdom
      have hbd := hd.1
      unfold OddDomain at hbd
      rw [encodeWord_testBit255 _ (by omega) (by omega)] at ht
      rw [← ht]
      by_cases hodd : w % 2 ≠ 0
      · have hnot0 : ¬ w % 2 = 0 := hodd
        have hnotNeg : ¬ oddHalfSigned w < 0 := fun h => hnot0 (hd.2.2.mp h)
        simp [hodd, hnotNeg]
      · have heq0 : w % 2 = 0 := by omega
        have hNeg : oddHalfSigned w < 0 := hd.2.2.mpr heq0
        simp [hodd, hNeg]
  -- Step 5: [.CX L.rmsb L.parity, .X L.parity]
  have hm0_1 : measurementCount [.CX L.r0 L.parity, .CX L.parity L.r0] = 0 := rfl
  have hm0_2 : measurementCount (rotateRight L.r) = 0 := (rotate_counts L.r).2.1
  have hm0_3 : measurementCount [.CX (L.r.getD 254 0) L.rmsb] = 0 := rfl
  have hrun : run (shiftHalfOdd L) m s =
      run [.CX L.rmsb L.parity, .X L.parity] (m.drop (measurementCount (addHalfOdd L))) s4 := by
    simp only [shiftHalfOdd, run_append, measurementCount_append, hm0_1, hm0_2, hm0_3,
      Nat.zero_add, Nat.add_zero, List.take_zero, List.drop_zero, run_take]
    rfl
  dsimp only
  rw [hrun]
  refine ⟨hadd.1.trans hs3_phase, ?_, ?_⟩
  · intro u hu
    by_cases hup : u = L.parity
    · subst u
      simp [run, writeBit, hrmsbp, Ne.symm hrmsbp, hs4_par, hs4_rmsb, hP]
    · change (run [.CX L.rmsb L.parity, .X L.parity] _ s4).basis u = s.basis u
      rw [show (run [.CX L.rmsb L.parity, .X L.parity] _ s4).basis u = s4.basis u by
            simp [run, writeBit, hup]]
      have hu0 : u ≠ L.r0 := fun e => hu (by rw [e]; exact r_mem_getD L hw 0 (by decide))
      exact (hadd.2.1 u hu).trans ((hs3_out u hu).trans (hs1_out u hup hu0))
  · rw [regValue_congr L.r _ s4.basis (fun u hu => by
      have hup : u ≠ L.parity := fun e => hpNotR (e ▸ hu)
      simp [run, writeBit, hup])]
    exact hs4_R

theorem unshiftHalfOdd_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (w : Int) (hwB : -q - 1 ≤ w ∧ w ≤ q) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 (oddHalfSigned w))
    (hP : s.basis L.parity = false)
    (hclean : ∀ c ∈ cleanCarries L, s.basis c = false) :
    let out := run (unshiftHalfOdd L) m s
    out.phase = s.phase ∧
    (∀ q, q ∉ L.r → out.basis q = s.basis q) ∧
    regValue L.r out.basis = encodeWord 256 w := by
  have len := (BalancedCleanup.widths L.toLayout hw).2.1
  have hc := constants
  have hs := oddHalfStep_facts
  have hndR := r_nodup L hn
  have f := flagAway L hn L.parity (by simp)
  have hpNotR : L.parity ∉ L.r := fun h => f (by simp [h])
  have hr0p : L.r0 ≠ L.parity := fun e => hpNotR (by rw [← e]; exact r_mem_getD L hw 0 (by decide))
  have hrmsbp : L.rmsb ≠ L.parity := fun e => hpNotR (by rw [← e, ← r_getD_255 L hw]; exact r_mem_getD L hw 255 (by decide))
  have h254 := r_254_ne_rmsb L hw hn
  have hrmsbBit : s.basis L.rmsb = !(decide (w % 2 ≠ 0)) := by
    have ht := regValue_testBit L.r s.basis 255 (by rw [len]; decide)
    rw [r_getD_255 L hw, hR] at ht
    by_cases hwq : w = q
    · subst hwq
      have hq := oddHalfSigned_q
      rw [hq.1, encodeWord_testBit255 q (by omega) (by omega)] at ht
      simp [hq.2.1, hq.2.2] at ht ⊢
      exact ht
    · have hdom : OddDomain w := ⟨hwB.1, by omega⟩
      have hd := oddHalfSigned_domain w hdom
      have hbd := hd.1
      unfold OddDomain at hbd
      rw [encodeWord_testBit255 _ (by omega) (by omega)] at ht
      rw [← ht]
      by_cases hodd : w % 2 ≠ 0
      · have hnotNeg : ¬ oddHalfSigned w < 0 := fun h => hodd (hd.2.2.mp h)
        simp [hodd, hnotNeg]
      · have hNeg : oddHalfSigned w < 0 := hd.2.2.mpr (by omega)
        simp [hodd, hNeg]
  -- Step 1: [.CX L.rmsb L.parity]
  let st1 := run [.CX L.rmsb L.parity] [] s
  have hs1_out (u : Wire) (hu : u ≠ L.parity) : st1.basis u = s.basis u := by
    simp [st1, run, writeBit, hu]
  have hs1_par : st1.basis L.parity = !(decide (w % 2 ≠ 0)) := by
    simp [st1, run, writeBit, hP, hrmsbBit]
  have hs1_R : regValue L.r st1.basis = encodeWord 256 (oddHalfSigned w) :=
    (regValue_congr L.r _ _ (fun u hu => hs1_out u (fun e => hpNotR (e ▸ hu)))).trans hR
  have hclean1 : ∀ c ∈ cleanCarries L, st1.basis c = false := by
    intro c hc'
    have cNeP : c ≠ L.parity := fun e => f (by rw [← e]; simp [(cleanCarries_sublist L hw).subset hc'])
    exact (hs1_out c cNeP).trans (hclean c hc')
  -- Step 2: addHalfOdd L (cancels oddHalf_mod_eq!)
  let s2 := run (addHalfOdd L) m st1
  have hadd := addHalfOdd_correct L hw hn st1 m hclean1
  have hs2_par : s2.basis L.parity = !(decide (w % 2 ≠ 0)) :=
    (hadd.2.1 L.parity hpNotR).trans hs1_par
  have hs2_R : regValue L.r s2.basis = encodeWord 256 (w / 2) := by
    have hr2 := hadd.2.2
    rw [hs1_R, hs1_par] at hr2
    have hmod := oddHalf_mod_eq w hwB
    have hlt : encodeWord 256 (w / 2) < 2 ^ 256 := by unfold encodeWord; omega
    have hsum : oddHalfConst + negOddHalfConst = 2 ^ 256 := by unfold negOddHalfConst; omega
    rw [hr2, ← hmod]
    by_cases hodd : w % 2 ≠ 0
    · simp only [decide_eq_true hodd, Bool.not_true, Bool.false_eq_true, if_true, if_false]
      rw [if_pos hodd, Nat.mod_add_mod, Nat.add_assoc, hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    · simp only [decide_eq_false hodd, Bool.not_false, Bool.false_eq_true, if_true, if_false]
      rw [if_neg hodd, Nat.mod_add_mod, Nat.add_assoc, Nat.add_comm negOddHalfConst, hsum,
        Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  have hs2_254 : s2.basis (L.r.getD 254 0) = decide (w < 0) := by
    have ht := regValue_testBit L.r s2.basis 254 (by rw [len]; decide)
    rw [hs2_R, encodeWord_asr w (by omega) (by omega)] at ht
    have hlt : encodeWord 256 w / 2 < 2 ^ 255 := by unfold encodeWord; omega
    have hbit : (encodeWord 256 w / 2 + if w < 0 then 2 ^ 255 else 0).testBit 254 =
        (encodeWord 256 w / 2).testBit 254 := by
      by_cases hneg : w < 0
      · simp only [hneg, if_true]
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
        apply decide_eq_decide.mpr
        rw [show (2 ^ 255 : Nat) = 2 * 2 ^ 254 from rfl,
          Nat.add_mul_div_right _ _ (Nat.two_pow_pos 254)]
        omega
      · simp [hneg]
    rw [hbit, ← Nat.testBit_succ, encodeWord_testBit255 w (by omega) (by omega)] at ht
    exact ht.symm
  have hs2_255 : s2.basis L.rmsb = decide (w < 0) := by
    have ht := regValue_testBit L.r s2.basis 255 (by rw [len]; decide)
    rw [r_getD_255 L hw, hs2_R, encodeWord_testBit255 (w / 2) (by omega) (by omega)] at ht
    rw [← ht]
    apply decide_eq_decide.mpr; omega
  -- Step 3: [.X L.parity, .CX (L.r.getD 254 0) L.rmsb]
  let s3 := run [.X L.parity, .CX (L.r.getD 254 0) L.rmsb] [] s2
  have hs3_out (u : Wire) (hu1 : u ≠ L.parity) (hu2 : u ≠ L.rmsb) : s3.basis u = s2.basis u := by
    simp [s3, run, writeBit, hu1, hu2]
  have hs3_par : s3.basis L.parity = decide (w % 2 ≠ 0) := by
    simp [s3, run, writeBit, hrmsbp, Ne.symm hrmsbp, hs2_par]
  have hs3_R : regValue L.r s3.basis = encodeWord 256 w / 2 := by
    have h254p : L.r.getD 254 0 ≠ L.parity :=
      fun e => hpNotR (by rw [← e]; exact r_mem_getD L hw 254 (by decide))
    have heq : regValue L.r s3.basis = regValue L.r (writeBit s2.basis (L.r.getD 255 0) false) := by
      apply regValue_congr
      intro u hu
      have hup : u ≠ L.parity := fun e => hpNotR (e ▸ hu)
      by_cases hur : u = L.rmsb
      · subst u
        rw [r_getD_255 L hw]
        simp only [s3, run, writeBit, Function.update_self, Function.update_of_ne hrmsbp,
          Function.update_of_ne h254p, hs2_254, hs2_255, Bool.xor_self]
      · rw [hs3_out u hup hur, r_getD_255 L hw]; simp [writeBit, hur]
    rw [heq, regValue_update_at L.r s2.basis 255 hndR (by rw [len]; decide) false,
      r_getD_255 L hw, hs2_255, hs2_R, encodeWord_asr w (by omega) (by omega)]
    by_cases hneg : w < 0
    · simp only [decide_eq_true hneg, hneg, Bool.false_eq_true, if_true, if_false, Nat.add_zero]
      exact Nat.add_sub_cancel _ _
    · simp [hneg]
  -- Step 4: rotateLeft L.r
  let s4 := run (rotateLeft L.r) [] s3
  have hrot_fr := rotate_frame L.r s3 []
  have hs4_out (u : Wire) (hu : u ∉ L.r) : s4.basis u = s3.basis u := hrot_fr.2.2.2 u hu
  have hs4_par : s4.basis L.parity = decide (w % 2 ≠ 0) := (hs4_out L.parity hpNotR).trans hs3_par
  have hs4_R : regValue L.r s4.basis = 2 * (encodeWord 256 w / 2) := by
    have hfit : 2 * (encodeWord 256 w / 2) < 2 ^ L.r.length := by
      rw [len]; unfold encodeWord; omega
    exact (rotateLeft_spec L.r hndR (encodeWord 256 w / 2) hfit s3 [] hs3_R).2
  have hs4_r0 : s4.basis L.r0 = false := by
    have ht := regValue_testBit L.r s4.basis 0 (by rw [len]; decide)
    rw [r_getD_0, hs4_R, Nat.testBit_zero] at ht
    simp at ht; exact ht
  -- Step 5: [.CX L.parity L.r0, .CX L.r0 L.parity]
  have hm0_1 : measurementCount [.CX L.rmsb L.parity] = 0 := rfl
  have hm0_3 : measurementCount [.X L.parity, .CX (L.r.getD 254 0) L.rmsb] = 0 := rfl
  have hm0_4 : measurementCount (rotateLeft L.r) = 0 := (rotate_counts L.r).2.2.2
  have hrun : run (unshiftHalfOdd L) m s =
      run [.CX L.parity L.r0, .CX L.r0 L.parity] [] s4 := by
    have hdrop5 (r : List Bool) (t : State) :
        run [.CX L.parity L.r0, .CX L.r0 L.parity] r t =
          run [.CX L.parity L.r0, .CX L.r0 L.parity] [] t := by
      rw [← run_take _ r t]; rfl
    have hdrop4 (r : List Bool) (t : State) : run (rotateLeft L.r) r t = run (rotateLeft L.r) [] t := by
      rw [← run_take _ r t, hm0_4, List.take_zero]
    have hdrop3 (r : List Bool) (t : State) :
        run [.X L.parity, .CX (L.r.getD 254 0) L.rmsb] r t =
          run [.X L.parity, .CX (L.r.getD 254 0) L.rmsb] [] t := by
      rw [← run_take _ r t]; rfl
    simp only [unshiftHalfOdd, run_append, measurementCount_append, hm0_1, hm0_3, hm0_4,
      Nat.zero_add, Nat.add_zero, List.take_zero, List.drop_zero, run_take, hdrop5, hdrop4, hdrop3]
    rfl
  dsimp only
  rw [hrun]
  refine ⟨hrot_fr.2.2.1.trans hadd.1, ?_, ?_⟩
  · intro u hu
    have hu0 : u ≠ L.r0 := fun e => hu (by rw [e]; exact r_mem_getD L hw 0 (by decide))
    have hur : u ≠ L.rmsb := fun e => hu (by rw [e, ← r_getD_255 L hw]; exact r_mem_getD L hw 255 (by decide))
    by_cases hup : u = L.parity
    · subst u
      simp [run, writeBit, hr0p, Ne.symm hr0p, hs4_par, hs4_r0, hP]
    · change (run [.CX L.parity L.r0, .CX L.r0 L.parity] [] s4).basis u = s.basis u
      rw [show (run [.CX L.parity L.r0, .CX L.r0 L.parity] [] s4).basis u = s4.basis u by
            simp [run, writeBit, hup, hu0]]
      exact (hs4_out u hu).trans ((hs3_out u hup hur).trans ((hadd.2.1 u hu).trans (hs1_out u hup)))
  · have heq : regValue L.r (run [.CX L.parity L.r0, .CX L.r0 L.parity] [] s4).basis =
        regValue L.r (writeBit s4.basis (L.r.getD 0 0) (decide (w % 2 ≠ 0))) := by
      apply regValue_congr
      intro u hu
      have hup : u ≠ L.parity := fun e => hpNotR (e ▸ hu)
      by_cases hu0 : u = L.r0
      · subst u; rw [r_getD_0]; simp [run, writeBit, hr0p, Ne.symm hr0p, hs4_par, hs4_r0]
      · rw [r_getD_0]; simp [run, writeBit, hup, hu0]
    rw [heq, regValue_update_at L.r s4.basis 0 hndR (by rw [len]; decide) (decide (w % 2 ≠ 0)),
      r_getD_0, hs4_r0, hs4_R, pow_zero]
    have hm2 := encodeWord_mod2 w
    by_cases hodd : w % 2 ≠ 0
    · have h1 : encodeWord 256 w % 2 = 1 := hm2.mpr hodd
      simp only [decide_eq_true hodd, Bool.false_eq_true, if_true, if_false]; omega
    · have h0 : encodeWord 256 w % 2 = 0 := by
        have := Nat.mod_lt (encodeWord 256 w) (by decide : 0 < 2)
        have : encodeWord 256 w % 2 ≠ 1 := fun e => hodd (hm2.mp e)
        omega
      simp only [decide_eq_false hodd, Bool.false_eq_true, if_false]; omega

-- ============================================================================
-- Forward (`paddedGD_odd`) and inverse (`paddedD_odd`) odd-word joint kernels
-- ============================================================================

def programGD_odd (L : Layout) (J B : Wire) : Program :=
  copyRegister (some J) L.r L.y ++
  [.CCX J B L.lower] ++
  signComplement L.lower L.r ++
  shiftHalfOdd L ++
  [.measureX L.lower [] [.CZ J B]] ++
  eqToggle B L.y (eqAncillas L) L.r (oddWord 0) ++
  [.X J] ++ maskedConstant J L.y (oddWord 0) ++ [.X J]

def jointGD_odd (L : Layout) (J G : Wire) : Program :=
  [.X G] ++ programGD_odd L J G ++ [.X G]

def programD_odd (L : Layout) (J B : Wire) : Program :=
  [.X J] ++ maskedConstant J L.y (oddWord 0) ++ [.X J] ++
  eqToggle B L.y (eqAncillas L) L.r (oddWord 0) ++
  unshiftHalfOdd L ++
  [.CCX J B L.lower] ++
  signComplement L.lower L.r ++
  [.measureX L.lower [] [.CZ J B]] ++
  eraseCopy J L.r L.y

def jointD_odd (L : Layout) (J G : Wire) : Program :=
  [.X G] ++ programD_odd L J G ++ [.X G]

/-- Odd-word forward joint entry on `portsJ` with carry `base 719` hosted on `base 1032`. -/
def paddedGD_odd : Program :=
  renameProgram (Equiv.swap (base 719) (base 1032))
    (jointGD_odd portsJ (base 1028) (base 1))

/-- Odd-word inverse joint entry on `portsJ` with carry `base 719` hosted on `base 1032`. -/
def paddedD_odd : Program :=
  renameProgram (Equiv.swap (base 719) (base 1032))
    (jointD_odd portsJ (base 1028) (base 1))

end ECDSAAdd.Entrant.JointOdd1588
end

-- ============================================================================
-- Section 3: Full specs, resources, support, physicality for `paddedGD_odd` / `paddedD_odd`
-- ============================================================================
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.JointOdd1588
open ECDSAAdd Arithmetic Challenge Baselines BalancedCircuit BalancedField Secp256k1 RecordedQuantum
open EntryRetained5 FirstInverse5 JointInverse1588 MappedCompressed
attribute [local irreducible] run wires gateSlots shiftHalfOdd unshiftHalfOdd eqToggle eraseCopy copyRegister signComplement maskedConstant

private theorem odd_half_spec (U : Bool) (Z : Fp) :
    let z := oddRep Z
    let w := if U then -z - 1 else z
    (-q - 1 ≤ w ∧ w ≤ q) ∧
    (if U && decide (Z = 0)
     then 2 ^ 256 - 1 - encodeWord 256 (oddHalfSigned w)
     else encodeWord 256 (oddHalfSigned w)) =
      oddWord ((if U then -Z else Z) / 2) := by
  have hb := oddRep_bounds Z
  have hc := constants
  unfold OddDomain at hb
  dsimp only
  cases U
  · simp only [Bool.false_eq_true, if_false, Bool.false_and]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hd := oddHalfSigned_domain (oddRep Z) hb
    rw [oddWord, ← oddRep_inverse _ hd.1, hd.2.1, oddRep_field]
  · simp only [if_true, Bool.true_and]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    by_cases hZ : Z = 0
    · subst hZ
      simp only [decide_true, if_true, neg_zero, zero_div]
      rw [oddRep_zero, show -(-q - 1) - 1 = q by omega, oddHalfSigned_q.1, encodeWord_q_eq]
      have hlt := oddWord_lt 0
      omega
    · simp only [decide_eq_false hZ, Bool.false_eq_true, if_false]
      have hneg := oddRep_neg Z hZ
      rw [← hneg]
      have hd := oddHalfSigned_domain (oddRep (-Z)) (oddRep_bounds (-Z))
      rw [oddWord, ← oddRep_inverse _ hd.1, hd.2.1, oddRep_field]

private structure LayoutInfo (L : Layout) (J B : Wire) : Prop where
  eqND : (B :: (L.y ++ eqAncillas L ++ L.r)).Nodup
  copyND : (J :: (L.r ++ L.y)).Nodup
  jb : J ≠ B
  jl : J ≠ L.lower
  bl : B ≠ L.lower
  lr : L.lower ∉ L.r
  ly : L.lower ∉ L.y
  jy : J ∉ L.y
  jr : J ∉ L.r
  br : B ∉ L.r
  by_ : B ∉ L.y

private theorem layout_eq_nodup (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J, B].Nodup) :
    LayoutInfo L J B := by
  have hjb : J ≠ B := by simpa using hJB
  have nd : (J :: B :: L.wires).Nodup :=
    List.nodup_cons.mpr ⟨by simp [hJ, hjb], List.nodup_cons.mpr ⟨hB, hn⟩⟩
  have hndAll := allND L hn
  have hsubC := cleanCarries_sublist L hw
  have hmemW (q : Wire) (hq : q ∈ L.r ∨ q ∈ L.y ∨ q ∈ L.carry ∨ q ∈ [L.parity, L.lower, L.one, L.sign]) :
      q ∈ L.wires := by
    rcases hq with h | h | h | h
    · exact data_member L q (by simp [h])
    · exact data_member L q (by simp [h])
    · exact data_member L q (by simp [h])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp [Layout.wires, BalancedCleanup.Layout.wires]
  have hct := List.nodup_iff_count.mp hndAll
  have hnd1 : (B :: (L.y ++ eqAncillas L ++ L.r)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have cA := hct q
    have cC := hsubC.count_le q
    by_cases hqB : q = B
    · subst q
      have hnot : B ∉ L.y ++ eqAncillas L ++ L.r := by
        intro bad
        simp only [eqAncillas, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at bad
        rcases bad with (h | (e | e | e | e) | h) | h
        · exact hB (hmemW B (Or.inr (Or.inl h)))
        · exact hB (hmemW B (Or.inr (Or.inr (Or.inr (by simp [e])))))
        · exact hB (hmemW B (Or.inr (Or.inr (Or.inr (by simp [e])))))
        · exact hB (hmemW B (Or.inr (Or.inr (Or.inr (by simp [e])))))
        · exact hB (hmemW B (Or.inr (Or.inr (Or.inr (by simp [e])))))
        · exact hB (hmemW B (Or.inr (Or.inr (Or.inl (hsubC.subset h)))))
        · exact hB (hmemW B (Or.inl h))
      have h0 : (L.y ++ eqAncillas L ++ L.r).count B = 0 := List.count_eq_zero.mpr hnot
      simp only [List.count_cons, beq_self_eq_true, if_true, h0]
      omega
    · have hbne : (B == q) = false := beq_false_of_ne (Ne.symm hqB)
      simp only [eqAncillas, List.count_cons, List.count_append, List.count_nil, hbne,
        Bool.false_eq_true, if_false] at cA ⊢
      omega
  have hnd2 : (J :: (L.r ++ L.y)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have cA := hct q
    by_cases hqJ : q = J
    · subst q
      have h0 : (L.r ++ L.y).count J = 0 :=
        List.count_eq_zero.mpr (fun bad => hJ (data_member L J (List.mem_append_left _ bad)))
      simp only [List.count_cons, beq_self_eq_true, if_true, h0]
      omega
    · have hjne : (J == q) = false := beq_false_of_ne (Ne.symm hqJ)
      simp only [List.count_cons, List.count_append, hjne, Bool.false_eq_true, if_false] at cA ⊢
      omega
  have fLow := flagAway L hn L.lower (by simp)
  refine ⟨hnd1, hnd2, hjb,
    fun e => hJ (hmemW J (Or.inr (Or.inr (Or.inr (by simp [e]))))),
    fun e => hB (hmemW B (Or.inr (Or.inr (Or.inr (by simp [e]))))),
    fun h => fLow (by simp [h]),
    fun h => fLow (by simp [h]),
    fun h => hJ (hmemW J (Or.inr (Or.inl h))),
    fun h => hJ (hmemW J (Or.inl h)),
    fun h => hB (hmemW B (Or.inl h)),
    fun h => hB (hmemW B (Or.inr (Or.inl h)))⟩

theorem programGD_odd_counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (programGD_odd L J B) = 765 ∧ measurementCount (programGD_odd L J B) = 509 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h1 := copyRegister_counts (some J) L.r L.y (len.2.1.trans len.2.2.1.symm)
  have h2 := signComplement_counts L.lower L.r
  have h3 := shiftHalfOdd_counts L hw
  have h4 := eqToggle_counts B L.y (eqAncillas L) L.r (oddWord 0)
    (len.2.2.1.trans (eqAncillas_length L hw).symm)
  have h5 := maskedConstant_counts J L.y (oddWord 0)
  simp only [programGD_odd, toffoliCount_append, measurementCount_append,
    h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2,
    len.2.1, len.2.2.1, Option.isSome_some, if_true, toffoliCount, measurementCount]
  exact ⟨trivial, trivial⟩

theorem programD_odd_counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (programD_odd L J B) = 509 ∧ measurementCount (programD_odd L J B) = 765 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h1 := maskedConstant_counts J L.y (oddWord 0)
  have h2 := eqToggle_counts B L.y (eqAncillas L) L.r (oddWord 0)
    (len.2.2.1.trans (eqAncillas_length L hw).symm)
  have h3 := unshiftHalfOdd_counts L hw
  have h4 := signComplement_counts L.lower L.r
  have h5 := eraseCopy_counts J L.r L.y (len.2.1.trans len.2.2.1.symm)
  simp only [programD_odd, toffoliCount_append, measurementCount_append,
    h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2,
    len.2.1, len.2.2.1, toffoliCount, measurementCount]
  exact ⟨trivial, trivial⟩

theorem jointGD_odd_counts (L : Layout) (hw : L.Widths) (J G : Wire) :
    toffoliCount (jointGD_odd L J G) = 765 ∧ measurementCount (jointGD_odd L J G) = 509 := by
  have h := programGD_odd_counts L hw J G
  simp only [jointGD_odd, toffoliCount_append, measurementCount_append, h.1, h.2,
    toffoliCount, measurementCount]
  exact ⟨trivial, trivial⟩

theorem jointD_odd_counts (L : Layout) (hw : L.Widths) (J G : Wire) :
    toffoliCount (jointD_odd L J G) = 509 ∧ measurementCount (jointD_odd L J G) = 765 := by
  have h := programD_odd_counts L hw J G
  simp only [jointD_odd, toffoliCount_append, measurementCount_append, h.1, h.2,
    toffoliCount, measurementCount]
  exact ⟨trivial, trivial⟩

theorem paddedGD_odd_counts :
    toffoliCount paddedGD_odd = 765 ∧ measurementCount paddedGD_odd = 509 := by
  have h := jointGD_odd_counts portsJ portsJ_widths (base 1028) (base 1)
  have r := renameProgram_counts (Equiv.swap (base 719) (base 1032))
    (jointGD_odd portsJ (base 1028) (base 1))
  exact ⟨r.1.trans h.1, r.2.trans h.2⟩

theorem paddedD_odd_counts :
    toffoliCount paddedD_odd = 509 ∧ measurementCount paddedD_odd = 765 := by
  have h := jointD_odd_counts portsJ portsJ_widths (base 1028) (base 1)
  have r := renameProgram_counts (Equiv.swap (base 719) (base 1032))
    (jointD_odd portsJ (base 1028) (base 1))
  exact ⟨r.1.trans h.1, r.2.trans h.2⟩

theorem jointGD_odd_slots (L : Layout) (hw : L.Widths) (J G : Wire) :
    gateSlots (jointGD_odd L J G) ≤ 7900 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h1 := copyRegister_gateSlots (some J) L.r L.y
  have h2 := signComplement_gateSlots L.lower L.r
  have h3 := shiftHalfOdd_slots_le L hw
  have h4 := eqToggle_slots_le G L.y (eqAncillas L) L.r (oddWord 0)
  have h5 := maskedConstant_gateSlots_le J L.y (oddWord 0)
  simp only [jointGD_odd, programGD_odd, gateSlots_append,
    gateSlots_cons, gateSlots_nil, instructionSlots, h1, h2, len.2.1, len.2.2.1,
    List.length_nil, List.length_cons, Nat.min_self] at h3 h4 h5 ⊢
  omega

theorem jointD_odd_slots (L : Layout) (hw : L.Widths) (J G : Wire) :
    gateSlots (jointD_odd L J G) ≤ 8160 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h1 := maskedConstant_gateSlots_le J L.y (oddWord 0)
  have h2 := eqToggle_slots_le G L.y (eqAncillas L) L.r (oddWord 0)
  have h3 := unshiftHalfOdd_slots_le L hw
  have h4 := signComplement_gateSlots L.lower L.r
  have h5 := eraseCopy_slots J L.r L.y (len.2.1.trans len.2.2.1.symm)
  simp only [jointD_odd, programD_odd, gateSlots_append,
    gateSlots_cons, gateSlots_nil, instructionSlots, h4, h5, len.2.1, len.2.2.1,
    List.length_nil, List.length_cons] at h1 h2 h3 ⊢
  omega

theorem paddedGD_odd_slots : gateSlots paddedGD_odd ≤ 7900 := by
  rw [paddedGD_odd, rename_gateSlots]
  exact jointGD_odd_slots portsJ portsJ_widths (base 1028) (base 1)

theorem paddedD_odd_slots : gateSlots paddedD_odd ≤ 8160 := by
  rw [paddedD_odd, rename_gateSlots]
  exact jointD_odd_slots portsJ portsJ_widths (base 1028) (base 1)

theorem jointGD_odd_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J, G].Nodup) :
    GatePhysical (jointGD_odd L J G) := by
  have d := layout_eq_nodup L hw hn J G hJ hG hJG
  have hcp : GatePhysical (copyRegister (some J) L.r L.y) := by
    apply copyRegister_physical (some J) L.r L.y (List.nodup_cons.mp d.copyND).2
    intro c hc; have := Option.mem_some_iff.mp hc; subst this; exact d.jy
  have hccx : GatePhysical [.CCX J G L.lower] := by
    simp [GatePhysical, PhysicalInstr, ProperGate, d.jb, d.jl, d.bl,
      Ne.symm d.jb, Ne.symm d.jl, Ne.symm d.bl]
  have hmx : GatePhysical [.measureX L.lower [] [.CZ J G]] := by
    simp [GatePhysical, PhysicalInstr, d.jb, d.jl, d.bl,
      Ne.symm d.jb, Ne.symm d.jl, Ne.symm d.bl]
  have hx (q : Wire) : GatePhysical [.X q] := by simp [GatePhysical, PhysicalInstr, ProperGate]
  simp only [jointGD_odd, programGD_odd, gatePhysical_append]
  exact ⟨⟨hx G, ⟨⟨⟨⟨⟨⟨⟨⟨hcp, hccx⟩, signComplement_physical L.lower L.r d.lr⟩,
    shiftHalfOdd_physical L hw hn⟩, hmx⟩, eqToggle_physical G L.y (eqAncillas L) L.r (oddWord 0) d.eqND⟩,
    hx J⟩, maskedConstant_physical J L.y (oddWord 0) d.jy⟩, hx J⟩⟩, hx G⟩

theorem jointD_odd_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J, G].Nodup) :
    GatePhysical (jointD_odd L J G) := by
  have d := layout_eq_nodup L hw hn J G hJ hG hJG
  have hccx : GatePhysical [.CCX J G L.lower] := by
    simp [GatePhysical, PhysicalInstr, ProperGate, d.jb, d.jl, d.bl,
      Ne.symm d.jb, Ne.symm d.jl, Ne.symm d.bl]
  have hmx : GatePhysical [.measureX L.lower [] [.CZ J G]] := by
    simp [GatePhysical, PhysicalInstr, d.jb, d.jl, d.bl,
      Ne.symm d.jb, Ne.symm d.jl, Ne.symm d.bl]
  have hx (q : Wire) : GatePhysical [.X q] := by simp [GatePhysical, PhysicalInstr, ProperGate]
  simp only [jointD_odd, programD_odd, gatePhysical_append]
  exact ⟨⟨hx G, ⟨⟨⟨⟨⟨⟨⟨⟨hx J, maskedConstant_physical J L.y (oddWord 0) d.jy⟩, hx J⟩,
    eqToggle_physical G L.y (eqAncillas L) L.r (oddWord 0) d.eqND⟩,
    unshiftHalfOdd_physical L hw hn⟩, hccx⟩, signComplement_physical L.lower L.r d.lr⟩,
    hmx⟩, eraseCopy_physical J L.r L.y d.copyND⟩⟩, hx G⟩

theorem paddedGD_odd_physical : GatePhysical paddedGD_odd :=
  gatePhysical_rename _ (Equiv.swap _ _).injective _
    (jointGD_odd_physical portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
      (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup)

theorem paddedD_odd_physical : GatePhysical paddedD_odd :=
  gatePhysical_rename _ (Equiv.swap _ _).injective _
    (jointD_odd_physical portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
      (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup)

private def oddJointSites (L : Layout) (J G : Wire) : Finset Wire :=
  (L.r ++ L.y ++ cleanCarries L ++ [L.parity, L.lower, L.one, L.sign, J, G]).toFinset

private theorem jointGD_odd_sites (L : Layout) (hw : L.Widths) (J G : Wire) :
    wires (jointGD_odd L J G) ⊆ oddJointSites L J G := by
  have h1 := copyRegister_wires_subset (some J) L.r L.y
  have h2 := signComplement_wires_subset L.lower L.r
  have h3 := shiftHalfOdd_wires_sub L hw
  have h4 := eqToggle_wires_sub G L.y (eqAncillas L) L.r (oddWord 0)
  have h5 := maskedConstant_wires_subset J L.y (oddWord 0)
  intro q hq
  simp only [jointGD_odd, programGD_odd, wires_append, Finset.mem_union] at hq
  simp only [oddJointSites, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hq with (hq | ((((((((hq | hq) | hq) | hq) | hq) | hq) | hq) | hq) | hq)) | hq
  · simp [wires, Instr.wires] at hq; tauto
  · have m := h1 hq; simp only [Option.toList, List.mem_toFinset, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at m; tauto
  · simp [wires, Instr.wires] at hq; tauto
  · have m := h2 hq; simp only [List.mem_toFinset, List.mem_cons] at m; tauto
  · have m := h3 hq; simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at m; tauto
  · simp [wires, Instr.wires, correctionWires] at hq; tauto
  · have m := h4 hq; simp only [eqAncillas, List.mem_toFinset, List.mem_cons, List.mem_append] at m; tauto
  · simp [wires, Instr.wires] at hq; tauto
  · have m := h5 hq; simp only [List.mem_toFinset, List.mem_cons] at m; tauto
  · simp [wires, Instr.wires] at hq; tauto
  · simp [wires, Instr.wires] at hq; tauto

private theorem jointD_odd_sites (L : Layout) (hw : L.Widths) (J G : Wire) :
    wires (jointD_odd L J G) ⊆ oddJointSites L J G := by
  have h1 := maskedConstant_wires_subset J L.y (oddWord 0)
  have h2 := eqToggle_wires_sub G L.y (eqAncillas L) L.r (oddWord 0)
  have h3 := unshiftHalfOdd_wires_sub L hw
  have h4 := signComplement_wires_subset L.lower L.r
  have h5 := eraseCopy_wires_sub J L.r L.y
  intro q hq
  simp only [jointD_odd, programD_odd, wires_append, Finset.mem_union] at hq
  simp only [oddJointSites, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hq with (hq | ((((((((hq | hq) | hq) | hq) | hq) | hq) | hq) | hq) | hq)) | hq
  · simp [wires, Instr.wires] at hq; tauto
  · simp [wires, Instr.wires] at hq; tauto
  · have m := h1 hq; simp only [List.mem_toFinset, List.mem_cons] at m; tauto
  · simp [wires, Instr.wires] at hq; tauto
  · have m := h2 hq; simp only [eqAncillas, List.mem_toFinset, List.mem_cons, List.mem_append] at m; tauto
  · have m := h3 hq; simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at m; tauto
  · simp [wires, Instr.wires] at hq; tauto
  · have m := h4 hq; simp only [List.mem_toFinset, List.mem_cons] at m; tauto
  · simp [wires, Instr.wires, correctionWires] at hq; tauto
  · have m := h5 hq; simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at m; tauto
  · simp [wires, Instr.wires] at hq; tauto

private theorem oddJointSites_portsJ_sub (q : Wire) (hq : q ∈ oddJointSites portsJ (base 1028) (base 1)) :
    q ∈ kernelSites ∧ q ≠ base 0 ∧ q ≠ base 516 ∧ q ≠ base 760 ∧ q ≠ base 1541 ∧ q ≠ base 1032 := by
  have av := cleanCarries_avoid portsJ portsJ_widths portsJ_nodup
  rw [cLo_eq, c248_eq, cHi_eq] at av
  simp only [oddJointSites, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  have hks : q ∈ kernelSites := by
    simp only [kernelSites, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hq with ((h | h) | h) | h | h | h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr (cleanCarries_mem_take254 portsJ portsJ_widths q h))
    all_goals tauto
  have hne (i : Nat) (hi : i = 0 ∨ i = 516 ∨ i = 760 ∨ i = 1541 ∨ i = 1032) : q ≠ base i := by
    intro eq; subst eq
    rcases hq with ((h | h) | h) | h | h | h | h | h | h
    · rw [portsJ_r] at h; exact OwnPlusHost.not_block i 2056 256 (by omega) h
    · rw [portsJ_y] at h; exact OwnPlusHost.not_block i 770 256 (by omega) h
    · rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact (off_ports 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).2.2
          ((cleanCarries_sublist portsJ portsJ_widths).subset h)
      · exact av.1 h
      · exact av.2.1 h
      · exact av.2.2 h
      · exact (off_ports 1032 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).2.2
          ((cleanCarries_sublist portsJ portsJ_widths).subset h)
    all_goals
      simp only [portsJ, Q6EndpointCell.ports, base_injective.eq_iff] at h
      omega
  exact ⟨hks, hne 0 (by simp), hne 516 (by simp), hne 760 (by simp), hne 1541 (by simp),
    hne 1032 (by simp)⟩

private theorem padded_sites_transfer (P : Program)
    (hsub : wires P ⊆ oddJointSites portsJ (base 1028) (base 1)) :
    wires (renameProgram (Equiv.swap (base 719) (base 1032)) P) ⊆ kernelSites ∧
    (∀ i, (i = 0 ∨ i = 516 ∨ i = 719 ∨ i = 1541) →
      base i ∉ wires (renameProgram (Equiv.swap (base 719) (base 1032)) P)) ∧
    base 760 ∉ wires (renameProgram (Equiv.swap (base 719) (base 1032)) P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    have info := oddJointSites_portsJ_sub a (hsub ha)
    by_cases a719 : a = base 719
    · subst a; rw [Equiv.swap_apply_left]; simp [kernelSites]
    · rw [Equiv.swap_apply_of_ne_of_ne a719 info.2.2.2.2.2]; exact info.1
  · intro i hi used
    rw [renameProgram_support] at used
    obtain ⟨a, ha, eq⟩ := Finset.mem_image.mp used
    have info := oddJointSites_portsJ_sub a (hsub ha)
    by_cases a719 : a = base 719
    · subst a; rw [Equiv.swap_apply_left, base_injective.eq_iff] at eq; omega
    · rw [Equiv.swap_apply_of_ne_of_ne a719 info.2.2.2.2.2] at eq
      subst eq
      rcases hi with rfl | rfl | rfl | rfl
      · exact info.2.1 rfl
      · exact info.2.2.1 rfl
      · exact a719 rfl
      · exact info.2.2.2.2.1 rfl
  · intro used
    rw [renameProgram_support] at used
    obtain ⟨a, ha, eq⟩ := Finset.mem_image.mp used
    have info := oddJointSites_portsJ_sub a (hsub ha)
    by_cases a719 : a = base 719
    · subst a; rw [Equiv.swap_apply_left, base_injective.eq_iff] at eq; omega
    · rw [Equiv.swap_apply_of_ne_of_ne a719 info.2.2.2.2.2] at eq
      exact info.2.2.2.1 eq

theorem paddedGD_odd_support : wires paddedGD_odd ⊆ kernelSites :=
  (padded_sites_transfer _ (jointGD_odd_sites portsJ portsJ_widths (base 1028) (base 1))).1

theorem paddedGD_odd_free (i : Nat) (hi : i = 0 ∨ i = 516 ∨ i = 719 ∨ i = 1541) :
    base i ∉ wires paddedGD_odd :=
  (padded_sites_transfer _ (jointGD_odd_sites portsJ portsJ_widths (base 1028) (base 1))).2.1 i hi

theorem paddedGD_odd_760_free : base 760 ∉ wires paddedGD_odd :=
  (padded_sites_transfer _ (jointGD_odd_sites portsJ portsJ_widths (base 1028) (base 1))).2.2

theorem paddedD_odd_support : wires paddedD_odd ⊆ kernelSites :=
  (padded_sites_transfer _ (jointD_odd_sites portsJ portsJ_widths (base 1028) (base 1))).1

theorem paddedD_odd_free (i : Nat) (hi : i = 0 ∨ i = 516 ∨ i = 719 ∨ i = 1541) :
    base i ∉ wires paddedD_odd :=
  (padded_sites_transfer _ (jointD_odd_sites portsJ portsJ_widths (base 1028) (base 1))).2.1 i hi

theorem paddedD_odd_760_free : base 760 ∉ wires paddedD_odd :=
  (padded_sites_transfer _ (jointD_odd_sites portsJ portsJ_widths (base 1028) (base 1))).2.2

private theorem xwrap_run (G : Wire) (P : Program) (m : List Bool) (s : State) :
    run ([.X G] ++ P ++ [.X G]) m s = run [.X G] [] (run P m (run [.X G] [] s)) :=
  JointForward1588.xwrap_run G P m s

private theorem run_X (q : Wire) (s : State) :
    run [.X q] [] s = ⟨s.phase, writeBit s.basis q (!s.basis q)⟩ := by
  simp [run]

private theorem masked_notJ_run (J : Wire) (ys : List Wire) (k : Nat)
    (hnd : ys.Nodup) (hJ : J ∉ ys) (hk : k < 2 ^ ys.length) (s : State) (m : List Bool) :
    let out := run ([.X J] ++ maskedConstant J ys k ++ [.X J]) m s
    out.phase = s.phase ∧
    (∀ q, q ∉ ys → out.basis q = s.basis q) ∧
    regValue ys out.basis = regValue ys s.basis ^^^ (if !s.basis J then k else 0) := by
  let a : State := ⟨s.phase, writeBit s.basis J (!s.basis J)⟩
  have ha_eq : run [.X J] [] s = a := run_X J s
  have hm := maskedConstant_correct J ys k hnd hJ hk a m
  let b := run (maskedConstant J ys k) m a
  have hrun : run ([.X J] ++ maskedConstant J ys k ++ [.X J]) m s =
      ⟨b.phase, writeBit b.basis J (!b.basis J)⟩ := by
    rw [xwrap_run, ha_eq, run_X]
  have hY : regValue ys a.basis = regValue ys s.basis :=
    regValue_congr ys _ _ (fun q hq => by simp [a, writeBit, show q ≠ J from fun e => hJ (e ▸ hq)])
  have hYout : regValue ys (writeBit b.basis J (!b.basis J)) = regValue ys b.basis :=
    regValue_congr ys _ _ (fun q hq => by simp [writeBit, show q ≠ J from fun e => hJ (e ▸ hq)])
  dsimp only
  rw [hrun]
  refine ⟨hm.1, ?_, ?_⟩
  · intro q hq
    change writeBit b.basis J (!b.basis J) q = s.basis q
    by_cases hqJ : q = J
    · subst q; rw [writeBit, Function.update_self, hm.2.1 J hJ]; simp [a, writeBit]
    · rw [writeBit, Function.update_of_ne hqJ, hm.2.1 q hq]; simp [a, writeBit, hqJ]
  · rw [hYout, hm.2.2, hY]
    simp [a, writeBit]

private theorem anc_clean_of_work (L : Layout) (hw : L.Widths) (b : BasisState)
    (hclean : ∀ q ∈ work L, b q = false) (hsign : b L.sign = false) :
    ∀ q ∈ eqAncillas L, b q = false := by
  intro q hq
  simp only [eqAncillas, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with (rfl | rfl | rfl | rfl) | hc
  · exact hclean _ (by simp [work])
  · exact hclean _ (by simp [work])
  · exact hclean _ (by simp [work])
  · exact hsign
  · exact hclean _ (by simp [work, (cleanCarries_sublist L hw).subset hc])

private theorem cond_eq_odd0 (Jv Bv : Bool) (Z : Fp) :
    (Bv && decide ((if Jv then oddWord Z else 0) = oddWord 0 % 2 ^ 256)) =
      (Jv && Bv && decide (Z = 0)) := by
  rw [Nat.mod_eq_of_lt (oddWord_lt 0)]
  cases Jv <;> cases Bv
  · simp
  · simp [oddWord_zero_ne.symm]
  · simp
  · simp only [if_true, Bool.true_and]
    exact decide_eq_decide.mpr ⟨fun h => oddWord_injective h, fun h => h ▸ rfl⟩

theorem programGD_odd_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J, B].Nodup)
    (Jv Bv : Bool) (Z : Fp) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = oddWord Z) (hY : regValue L.y s.basis = 0)
    (hclean : ∀ q ∈ work L, s.basis q = false) (hsign : s.basis L.sign = false)
    (hj : s.basis J = Jv) (hb : s.basis B = Bv) :
    let out := run (programGD_odd L J B) m s
    out.phase = s.phase ∧
    regValue L.r out.basis = oddWord ((if Jv && Bv then -Z else Z) / 2) ∧
    regValue L.y out.basis = oddWord (if Jv then Z else 0) ∧
    (∀ q, q ∉ L.r → q ∉ L.y → out.basis q = s.basis q) := by
  have len := BalancedCleanup.widths L.toLayout hw
  have hc := constants
  have d := layout_eq_nodup L hw hn J B hJ hB hJB
  have hndRY : (L.r ++ L.y).Nodup := (List.nodup_cons.mp d.copyND).2
  have hdisRY : L.r.Disjoint L.y := (List.nodup_append'.mp hndRY).2.2
  have hndR := r_nodup L hn
  have hndY := y_nodup L hn
  have hspec := odd_half_spec (Jv && Bv) Z
  let w : Int := if Jv && Bv then -oddRep Z - 1 else oddRep Z
  -- Step 1: copyRegister (some J) L.r L.y
  let st1 := run (copyRegister (some J) L.r L.y) [] s
  have hc1 := copyRegister_correct (some J) L.r L.y (len.2.1.trans len.2.2.1.symm) hndRY
    (fun c hc => by have := Option.mem_some_iff.mp hc; subst this; exact d.jy) s []
  have hs1_out (q : Wire) (hq : q ∉ L.y) : st1.basis q = s.basis q := hc1.2.1 q hq
  have hs1_R : regValue L.r st1.basis = oddWord Z :=
    (regValue_congr L.r _ _ (fun q hq => hs1_out q (List.disjoint_left.mp hdisRY hq))).trans hR
  have hs1_Y : regValue L.y st1.basis = if Jv then oddWord Z else 0 := by
    rw [hc1.2.2, hY, Nat.zero_xor, copyValue, hj, hR]
  -- Step 2: [.CCX J B L.lower]
  let s2 := run [.CCX J B L.lower] [] st1
  have hs2_out (q : Wire) (hq : q ≠ L.lower) : s2.basis q = st1.basis q := by
    simp [s2, run, writeBit, hq]
  have hs2_low : s2.basis L.lower = (Jv && Bv) := by
    have hlo0 : st1.basis L.lower = false := (hs1_out L.lower d.ly).trans (hclean _ (by simp [work]))
    simp [s2, run, writeBit, hs1_out J d.jy, hs1_out B d.by_, hj, hb, hlo0]
  have hs2_R : regValue L.r s2.basis = oddWord Z :=
    (regValue_congr L.r _ _ (fun q hq => hs2_out q (fun e => d.lr (e ▸ hq)))).trans hs1_R
  -- Step 3: signComplement L.lower L.r
  let s3 := run (signComplement L.lower L.r) [] s2
  have hc3 := signComplement_correct L.lower L.r hndR d.lr s2 []
  have hs3_out (q : Wire) (hq : q ∉ L.r) : s3.basis q = s2.basis q := hc3.2.1 q hq
  have hs3_R : regValue L.r s3.basis = encodeWord 256 w := by
    rw [hc3.2.2, len.2.1, hs2_low, hs2_R]
    have hbd := oddRep_bounds Z; unfold OddDomain at hbd
    cases hU : Jv && Bv
    · simp [w, hU, oddWord]
    · simp only [w, hU, if_true, oddWord]
      exact encodeWord_complement (oddRep Z) (by omega) (by omega)
  -- Step 4: shiftHalfOdd L
  have hparNeLow : L.parity ≠ L.lower := by
    have nd := scalarND L hn
    have ct := List.nodup_iff_count.mp nd L.parity
    intro e; rw [e] at ct; simp [List.count_cons] at ct; omega
  have hparNotR : L.parity ∉ L.r := fun h => flagAway L hn L.parity (by simp) (by simp [h])
  have hparNotY : L.parity ∉ L.y := fun h => flagAway L hn L.parity (by simp) (by simp [h])
  have hs3_par : s3.basis L.parity = false :=
    (hs3_out L.parity hparNotR).trans ((hs2_out L.parity hparNeLow).trans
      ((hs1_out L.parity hparNotY).trans (hclean _ (by simp [work]))))
  have hs3_clean : ∀ c ∈ cleanCarries L, s3.basis c = false := by
    intro c hc'
    have cm := (cleanCarries_sublist L hw).subset hc'
    have cNotR : c ∉ L.r := carry_not_r L hn c cm
    have cNotY : c ∉ L.y := fun h => y_not_carry L hn c h cm
    have cNeLow : c ≠ L.lower := fun e => flagAway L hn L.lower (by simp) (by rw [← e]; simp [cm])
    exact (hs3_out c cNotR).trans ((hs2_out c cNeLow).trans ((hs1_out c cNotY).trans
      (hclean c (by simp [work, cm]))))
  let m4 := m.take (measurementCount (shiftHalfOdd L))
  let s4 := run (shiftHalfOdd L) m4 s3
  have hc4 := shiftHalfOdd_correct L hw hn w hspec.1 s3 m4 hs3_R hs3_par hs3_clean
  have hs4_out (q : Wire) (hq : q ∉ L.r) : s4.basis q = s3.basis q := hc4.2.1 q hq
  -- Step 5: [.measureX L.lower [] [.CZ J B]]
  let m5 := (m.drop (measurementCount (shiftHalfOdd L))).take 1
  let s5 := run [.measureX L.lower [] [.CZ J B]] m5 s4
  have hs4_J : s4.basis J = Jv :=
    (hs4_out J d.jr).trans ((hs3_out J d.jr).trans ((hs2_out J d.jl).trans ((hs1_out J d.jy).trans hj)))
  have hs4_B : s4.basis B = Bv :=
    (hs4_out B d.br).trans ((hs3_out B d.br).trans ((hs2_out B d.bl).trans ((hs1_out B d.by_).trans hb)))
  have hs4_low : s4.basis L.lower = (s4.basis J && s4.basis B) := by
    rw [hs4_J, hs4_B]
    exact (hs4_out L.lower d.lr).trans ((hs3_out L.lower d.lr).trans hs2_low)
  have hs5_eq : s5 = ⟨s4.phase, writeBit s4.basis L.lower false⟩ :=
    eraseAnd_single J B L.lower d.jl d.bl s4 m5 hs4_low
  have hs5_out (q : Wire) (hqR : q ∉ L.r) (hqY : q ∉ L.y) : s5.basis q = s.basis q := by
    rw [hs5_eq]
    change writeBit s4.basis L.lower false q = s.basis q
    by_cases hql : q = L.lower
    · subst q; rw [writeBit, Function.update_self, hclean _ (by simp [work])]
    · rw [writeBit, Function.update_of_ne hql]
      exact (hs4_out q hqR).trans ((hs3_out q hqR).trans ((hs2_out q hql).trans (hs1_out q hqY)))
  have hs5_R : regValue L.r s5.basis = encodeWord 256 (oddHalfSigned w) := by
    rw [hs5_eq]
    exact (regValue_congr L.r _ s4.basis (fun q hq => by
      simp [writeBit, show q ≠ L.lower from fun e => d.lr (e ▸ hq)])).trans hc4.2.2
  have hs5_Y : regValue L.y s5.basis = if Jv then oddWord Z else 0 := by
    rw [hs5_eq]
    exact (regValue_congr L.y _ st1.basis (fun q hq => by
      have qNotR : q ∉ L.r := fun h => List.disjoint_left.mp hdisRY h hq
      have qNeL : q ≠ L.lower := fun e => d.ly (e ▸ hq)
      simp only [writeBit, Function.update_of_ne qNeL]
      exact (hs4_out q qNotR).trans ((hs3_out q qNotR).trans (hs2_out q qNeL)))).trans hs1_Y
  have hs5_anc : ∀ q ∈ eqAncillas L, s5.basis q = false := by
    apply anc_clean_of_work L hw s5.basis
    · intro q hq
      have off := work_no_data L hn q hq
      exact (hs5_out q off.1 off.2).trans (hclean q hq)
    · have sf := flagAway L hn L.sign (by simp)
      exact (hs5_out L.sign (fun h => sf (by simp [h])) (fun h => sf (by simp [h]))).trans hsign
  -- Step 6: eqToggle B L.y (eqAncillas L) L.r (oddWord 0)
  let m6 := (m.drop (measurementCount (shiftHalfOdd L))).drop 1
  let s6 := run (eqToggle B L.y (eqAncillas L) L.r (oddWord 0)) m6 s5
  have hc6 := eqToggle_correct B L.y (eqAncillas L) L.r (oddWord 0)
    (len.2.2.1.trans (eqAncillas_length L hw).symm) d.eqND s5 m6 hs5_anc
  have hs6_R : regValue L.r s6.basis = oddWord ((if Jv && Bv then -Z else Z) / 2) := by
    have h6 := hc6.2.2
    rw [hs5_out B d.br d.by_, hb, hs5_Y, len.2.2.1, len.2.1, hs5_R, cond_eq_odd0] at h6
    exact h6.trans hspec.2
  have hs6_Y : regValue L.y s6.basis = if Jv then oddWord Z else 0 :=
    (regValue_congr L.y _ s5.basis (fun q hq =>
      hc6.2.1 q (fun h => List.disjoint_left.mp hdisRY h hq))).trans hs5_Y
  -- Step 7: [.X J] ++ maskedConstant J L.y (oddWord 0) ++ [.X J]
  have hc7 := masked_notJ_run J L.y (oddWord 0) hndY d.jy (by rw [len.2.2.1]; exact oddWord_lt 0) s6 []
  -- Combine all runs
  have hm1 : measurementCount (copyRegister (some J) L.r L.y) = 0 :=
    (copyRegister_counts (some J) L.r L.y (len.2.1.trans len.2.2.1.symm)).2
  have hm2 : measurementCount [.CCX J B L.lower] = 0 := rfl
  have hm3 : measurementCount (signComplement L.lower L.r) = 0 := (signComplement_counts L.lower L.r).2
  have hm5 : measurementCount [.measureX L.lower [] [.CZ J B]] = 1 := rfl
  have hm7 : measurementCount ([.X J] ++ maskedConstant J L.y (oddWord 0) ++ [.X J]) = 0 := by
    simp [measurementCount_append, (maskedConstant_counts J L.y (oddWord 0)).2, measurementCount]
  have hrun : run (programGD_odd L J B) m s =
      run ([.X J] ++ maskedConstant J L.y (oddWord 0) ++ [.X J]) [] s6 := by
    have hzero (P : Program) (hp : measurementCount P = 0) (r : List Bool) (t : State) :
        run P r t = run P [] t := by rw [← run_take P r t, hp, List.take_zero]
    have hshape : programGD_odd L J B =
        (((copyRegister (some J) L.r L.y ++ [.CCX J B L.lower]) ++ signComplement L.lower L.r) ++
          shiftHalfOdd L) ++ ([.measureX L.lower [] [.CZ J B]] ++
            (eqToggle B L.y (eqAncillas L) L.r (oddWord 0) ++
              ([.X J] ++ maskedConstant J L.y (oddWord 0) ++ [.X J]))) := by
      simp only [programGD_odd, List.append_assoc]
    rw [hshape, run_append]
    simp only [measurementCount_append, hm1, hm2, hm3, Nat.zero_add]
    have hpre : run (((copyRegister (some J) L.r L.y ++ [.CCX J B L.lower]) ++ signComplement L.lower L.r) ++
        shiftHalfOdd L) m4 s = s4 := by
      simp only [run_append, measurementCount_append, hm1, hm2, hm3, Nat.zero_add,
        List.take_zero, List.drop_zero]
      rfl
    rw [hpre, run_append, hm5, run_append, hzero _ hm7, run_take]
  have hs2_ph : s2.phase = st1.phase := by simp [s2, run]
  dsimp only
  rw [hrun]
  refine ⟨hc7.1.trans (hc6.1.trans ((congrArg State.phase hs5_eq).trans
    (hc4.1.trans (hc3.1.trans (hs2_ph.trans hc1.1))))), ?_, ?_, ?_⟩
  · exact (regValue_congr L.r _ s6.basis (fun q hq =>
      hc7.2.1 q (List.disjoint_left.mp hdisRY hq))).trans hs6_R
  · rw [hc7.2.2, hs6_Y, hc6.2.1 J d.jr, hs5_out J d.jr d.jy, hj]
    cases Jv <;> simp
  · intro q hqR hqY
    exact (hc7.2.1 q hqY).trans ((hc6.2.1 q hqR).trans (hs5_out q hqR hqY))

theorem programD_odd_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J, B].Nodup)
    (Jv Bv : Bool) (Z : Fp) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = oddWord ((if Jv && Bv then -Z else Z) / 2))
    (hY : regValue L.y s.basis = oddWord (if Jv then Z else 0))
    (hclean : ∀ q ∈ work L, s.basis q = false) (hsign : s.basis L.sign = false)
    (hj : s.basis J = Jv) (hb : s.basis B = Bv) :
    let out := run (programD_odd L J B) m s
    out.phase = s.phase ∧
    regValue L.r out.basis = oddWord Z ∧
    regValue L.y out.basis = 0 ∧
    (∀ q, q ∉ L.r → q ∉ L.y → out.basis q = s.basis q) := by
  have len := BalancedCleanup.widths L.toLayout hw
  have hc := constants
  have d := layout_eq_nodup L hw hn J B hJ hB hJB
  have hndRY : (L.r ++ L.y).Nodup := (List.nodup_cons.mp d.copyND).2
  have hdisRY : L.r.Disjoint L.y := (List.nodup_append'.mp hndRY).2.2
  have hndR := r_nodup L hn
  have hndY := y_nodup L hn
  have hspec := odd_half_spec (Jv && Bv) Z
  let w : Int := if Jv && Bv then -oddRep Z - 1 else oddRep Z
  -- Step 1: [.X J] ++ maskedConstant J L.y (oddWord 0) ++ [.X J]
  let st1 := run ([.X J] ++ maskedConstant J L.y (oddWord 0) ++ [.X J]) [] s
  have hc1 := masked_notJ_run J L.y (oddWord 0) hndY d.jy (by rw [len.2.2.1]; exact oddWord_lt 0) s []
  have hs1_out (q : Wire) (hq : q ∉ L.y) : st1.basis q = s.basis q := hc1.2.1 q hq
  have hs1_R : regValue L.r st1.basis = oddWord ((if Jv && Bv then -Z else Z) / 2) :=
    (regValue_congr L.r _ _ (fun q hq => hs1_out q (List.disjoint_left.mp hdisRY hq))).trans hR
  have hs1_Y : regValue L.y st1.basis = if Jv then oddWord Z else 0 := by
    rw [hc1.2.2, hY, hj]
    cases Jv <;> simp
  have hs1_anc : ∀ q ∈ eqAncillas L, st1.basis q = false := by
    apply anc_clean_of_work L hw st1.basis
    · intro q hq
      have off := work_no_data L hn q hq
      exact (hs1_out q off.2).trans (hclean q hq)
    · have sf := flagAway L hn L.sign (by simp)
      exact (hs1_out L.sign (fun h => sf (by simp [h]))).trans hsign
  -- Step 2: eqToggle B L.y (eqAncillas L) L.r (oddWord 0)
  let m2 := m.take (measurementCount (eqToggle B L.y (eqAncillas L) L.r (oddWord 0)))
  let s2 := run (eqToggle B L.y (eqAncillas L) L.r (oddWord 0)) m2 st1
  have hc2 := eqToggle_correct B L.y (eqAncillas L) L.r (oddWord 0)
    (len.2.2.1.trans (eqAncillas_length L hw).symm) d.eqND st1 m2 hs1_anc
  have hs2_R : regValue L.r s2.basis = encodeWord 256 (oddHalfSigned w) := by
    have h2 := hc2.2.2
    rw [hs1_out B d.by_, hb, hs1_Y, len.2.2.1, len.2.1, hs1_R, cond_eq_odd0] at h2
    rw [h2, ← hspec.2]
    change (if (Jv && Bv && decide (Z = 0)) = true then
      2 ^ 256 - 1 - (if (Jv && Bv && decide (Z = 0)) = true then
        2 ^ 256 - 1 - encodeWord 256 (oddHalfSigned w) else encodeWord 256 (oddHalfSigned w))
      else (if (Jv && Bv && decide (Z = 0)) = true then
        2 ^ 256 - 1 - encodeWord 256 (oddHalfSigned w) else encodeWord 256 (oddHalfSigned w))) =
      encodeWord 256 (oddHalfSigned w)
    have hlt : encodeWord 256 (oddHalfSigned w) < 2 ^ 256 := by unfold encodeWord; omega
    cases hfl : Jv && Bv && decide (Z = 0)
    · simp only [Bool.false_eq_true, if_false]
    · simp only [if_true]; omega
  -- Step 3: unshiftHalfOdd L
  have hparNotR : L.parity ∉ L.r := fun h => flagAway L hn L.parity (by simp) (by simp [h])
  have hparNotY : L.parity ∉ L.y := fun h => flagAway L hn L.parity (by simp) (by simp [h])
  have hs2_par : s2.basis L.parity = false :=
    (hc2.2.1 L.parity hparNotR).trans ((hs1_out L.parity hparNotY).trans (hclean _ (by simp [work])))
  have hs2_clean : ∀ c ∈ cleanCarries L, s2.basis c = false := by
    intro c hc'
    have cm := (cleanCarries_sublist L hw).subset hc'
    exact (hc2.2.1 c (carry_not_r L hn c cm)).trans
      ((hs1_out c (fun h => y_not_carry L hn c h cm)).trans (hclean c (by simp [work, cm])))
  let mRest := m.drop (measurementCount (eqToggle B L.y (eqAncillas L) L.r (oddWord 0)))
  let m3 := mRest.take (measurementCount (unshiftHalfOdd L))
  let s3 := run (unshiftHalfOdd L) m3 s2
  have hc3 := unshiftHalfOdd_correct L hw hn w hspec.1 s2 m3 hs2_R hs2_par hs2_clean
  -- Step 4: [.CCX J B L.lower]
  let s4 := run [.CCX J B L.lower] [] s3
  have hs3_out (q : Wire) (hqR : q ∉ L.r) (hqY : q ∉ L.y) : s3.basis q = s.basis q :=
    (hc3.2.1 q hqR).trans ((hc2.2.1 q hqR).trans (hs1_out q hqY))
  have hs4_out (q : Wire) (hq : q ≠ L.lower) : s4.basis q = s3.basis q := by
    simp [s4, run, writeBit, hq]
  have hs4_low : s4.basis L.lower = (Jv && Bv) := by
    have hlo0 : s3.basis L.lower = false :=
      (hs3_out L.lower d.lr d.ly).trans (hclean _ (by simp [work]))
    simp [s4, run, writeBit, hs3_out J d.jr d.jy, hs3_out B d.br d.by_, hj, hb, hlo0]
  have hs4_R : regValue L.r s4.basis = encodeWord 256 w :=
    (regValue_congr L.r _ _ (fun q hq => hs4_out q (fun e => d.lr (e ▸ hq)))).trans hc3.2.2
  -- Step 5: signComplement L.lower L.r
  let s5 := run (signComplement L.lower L.r) [] s4
  have hc5 := signComplement_correct L.lower L.r hndR d.lr s4 []
  have hs5_R : regValue L.r s5.basis = oddWord Z := by
    rw [hc5.2.2, len.2.1, hs4_low, hs4_R]
    have hbd := oddRep_bounds Z; unfold OddDomain at hbd
    cases hU : Jv && Bv
    · simp [w, hU, oddWord]
    · simp only [w, hU, if_true, oddWord]
      have h := encodeWord_complement (-oddRep Z - 1) (by omega) (by omega)
      have heq : -(-oddRep Z - 1) - 1 = oddRep Z := by omega
      rw [heq] at h
      exact h
  -- Step 6: [.measureX L.lower [] [.CZ J B]]
  let m6 := (mRest.drop (measurementCount (unshiftHalfOdd L))).take 1
  let s6 := run [.measureX L.lower [] [.CZ J B]] m6 s5
  have hs5_J : s5.basis J = Jv := (hc5.2.1 J d.jr).trans ((hs4_out J d.jl).trans ((hs3_out J d.jr d.jy).trans hj))
  have hs5_B : s5.basis B = Bv := (hc5.2.1 B d.br).trans ((hs4_out B d.bl).trans ((hs3_out B d.br d.by_).trans hb))
  have hs5_low : s5.basis L.lower = (s5.basis J && s5.basis B) := by
    rw [hs5_J, hs5_B]; exact (hc5.2.1 L.lower d.lr).trans hs4_low
  have hs6_eq : s6 = ⟨s5.phase, writeBit s5.basis L.lower false⟩ :=
    eraseAnd_single J B L.lower d.jl d.bl s5 m6 hs5_low
  have hs6_out (q : Wire) (hqR : q ∉ L.r) (hqY : q ∉ L.y) : s6.basis q = s.basis q := by
    rw [hs6_eq]
    change writeBit s5.basis L.lower false q = s.basis q
    by_cases hql : q = L.lower
    · subst q; rw [writeBit, Function.update_self, hclean _ (by simp [work])]
    · rw [writeBit, Function.update_of_ne hql]
      exact (hc5.2.1 q hqR).trans ((hs4_out q hql).trans (hs3_out q hqR hqY))
  have hs6_R : regValue L.r s6.basis = oddWord Z := by
    rw [hs6_eq]
    exact (regValue_congr L.r _ s5.basis (fun q hq => by
      simp [writeBit, show q ≠ L.lower from fun e => d.lr (e ▸ hq)])).trans hs5_R
  have hs6_Y : regValue L.y s6.basis = if s6.basis J then regValue L.r s6.basis else 0 := by
    rw [hs6_out J d.jr d.jy, hj, hs6_R, hs6_eq]
    exact (regValue_congr L.y _ st1.basis (fun q hq => by
      have qNotR : q ∉ L.r := fun h => List.disjoint_left.mp hdisRY h hq
      have qNeL : q ≠ L.lower := fun e => d.ly (e ▸ hq)
      simp only [writeBit, Function.update_of_ne qNeL]
      exact (hc5.2.1 q qNotR).trans ((hs4_out q qNeL).trans ((hc3.2.1 q qNotR).trans (hc2.2.1 q qNotR))))).trans hs1_Y
  -- Step 7: eraseCopy J L.r L.y
  let m7 := (mRest.drop (measurementCount (unshiftHalfOdd L))).drop 1
  have hc7 := eraseCopy_correct J L.r L.y (len.2.1.trans len.2.2.1.symm) d.copyND s6 m7 hs6_Y
  -- Combine all runs
  have hm1 : measurementCount ([.X J] ++ maskedConstant J L.y (oddWord 0) ++ [.X J]) = 0 := by
    simp [measurementCount_append, (maskedConstant_counts J L.y (oddWord 0)).2, measurementCount]
  have hm4 : measurementCount [.CCX J B L.lower] = 0 := rfl
  have hm5 : measurementCount (signComplement L.lower L.r) = 0 := (signComplement_counts L.lower L.r).2
  have hm6 : measurementCount [.measureX L.lower [] [.CZ J B]] = 1 := rfl
  have hrun : run (programD_odd L J B) m s = run (eraseCopy J L.r L.y) m7 s6 := by
    have hshape : programD_odd L J B =
        (([.X J] ++ maskedConstant J L.y (oddWord 0) ++ [.X J]) ++
          eqToggle B L.y (eqAncillas L) L.r (oddWord 0)) ++
        ((unshiftHalfOdd L ++ [.CCX J B L.lower] ++ signComplement L.lower L.r) ++
          ([.measureX L.lower [] [.CZ J B]] ++ eraseCopy J L.r L.y)) := by
      simp only [programD_odd, List.append_assoc]
    rw [hshape, run_append, measurementCount_append, hm1, Nat.zero_add]
    have hpre1 : run (([.X J] ++ maskedConstant J L.y (oddWord 0) ++ [.X J]) ++
        eqToggle B L.y (eqAncillas L) L.r (oddWord 0)) m2 s = s2 := by
      rw [run_append, hm1, List.take_zero, List.drop_zero]
    rw [hpre1, run_append]
    simp only [measurementCount_append, hm4, hm5, Nat.add_zero]
    have hpre2 : run (unshiftHalfOdd L ++ [.CCX J B L.lower] ++ signComplement L.lower L.r) m3 s2 = s5 := by
      have hz (P : Program) (hp : measurementCount P = 0) (r : List Bool) (t : State) :
          run P r t = run P [] t := by rw [← run_take P r t, hp, List.take_zero]
      rw [run_append, run_append, hz _ hm5, hz _ hm4, measurementCount_append, hm4, Nat.add_zero,
        run_take]
      have hm3t : m3.take (measurementCount (unshiftHalfOdd L)) = m3 := by
        simp only [m3, List.take_take, Nat.min_self]
      rw [hm3t]
    rw [hpre2, run_append, hm6]
  have hs4_ph : s4.phase = s3.phase := by simp [s4, run]
  dsimp only
  rw [hrun]
  refine ⟨hc7.1.trans ((congrArg State.phase hs6_eq).trans (hc5.1.trans (hs4_ph.trans (hc3.1.trans (hc2.1.trans hc1.1))))),
    ?_, hc7.2.2, ?_⟩
  · exact (regValue_congr L.r _ s6.basis (fun q hq =>
      hc7.2.1 q (List.disjoint_left.mp hdisRY hq))).trans hs6_R
  · intro q hqR hqY
    exact (hc7.2.1 q hqY).trans (hs6_out q hqR hqY)

theorem jointGD_odd_pair (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J, G].Nodup)
    (origin : BasisState) (clean : ∀ q ∈ work L, origin q = false) (sign : origin L.sign = false)
    (Z : Fp) :
    Triple (PairFrame L.r L.y origin (oddWord Z) 0) (jointGD_odd L J G)
      (PairFrame L.r L.y origin
        (oddWord ((if origin J && !origin G then -Z else Z) / 2))
        (oddWord (if origin J then Z else 0))) := by
  have d := layout_eq_nodup L hw hn J G hJ hG hJG
  have sf := flagAway L hn L.sign (by simp)
  intro s m h
  let a : State := ⟨s.phase, writeBit s.basis G (!s.basis G)⟩
  have keep (q : Wire) (hq : q ≠ G) : a.basis q = s.basis q := by simp [a, writeBit, hq]
  have aR : regValue L.r a.basis = oddWord Z :=
    (regValue_congr L.r _ _ (fun q hq => keep q (fun e => d.br (e ▸ hq)))).trans h.1
  have aY : regValue L.y a.basis = 0 :=
    (regValue_congr L.y _ _ (fun q hq => keep q (fun e => d.by_ (e ▸ hq)))).trans h.2.1
  have ac : ∀ q ∈ work L, a.basis q = false := by
    intro q hq
    have off := work_no_data L hn q hq
    have qG : q ≠ G := fun e => hG (by rw [← e]; simp [Layout.wires, BalancedCleanup.Layout.wires, work] at hq ⊢; tauto)
    exact (keep q qG).trans ((h.2.2 q off.1 off.2).trans (clean q hq))
  have aSign : a.basis L.sign = false := by
    have sG : L.sign ≠ G := fun e => hG (by rw [← e]; simp [Layout.wires, BalancedCleanup.Layout.wires])
    exact (keep L.sign sG).trans ((h.2.2 L.sign (fun h => sf (by simp [h])) (fun h => sf (by simp [h]))).trans sign)
  have aJ : a.basis J = origin J := (keep J d.jb).trans (h.2.2 J d.jr d.jy)
  have aG : a.basis G = !origin G := by
    simp [a, writeBit, h.2.2 G d.br d.by_]
  have res := programGD_odd_frame L hw hn J G hJ hG hJG (origin J) (!origin G) Z a m aR aY ac aSign aJ aG
  let t := run (programGD_odd L J G) m a
  have hrun : run (jointGD_odd L J G) m s = ⟨t.phase, writeBit t.basis G (!t.basis G)⟩ := by
    rw [jointGD_odd, xwrap_run, run_X, run_X]
  rw [hrun]
  refine ⟨res.1, ?_, ?_, ?_⟩
  · exact (regValue_congr L.r _ _ (fun q hq => by
      change writeBit t.basis G (!t.basis G) q = t.basis q
      simp [writeBit, show q ≠ G from fun e => d.br (e ▸ hq)])).trans res.2.1
  · exact (regValue_congr L.y _ _ (fun q hq => by
      change writeBit t.basis G (!t.basis G) q = t.basis q
      simp [writeBit, show q ≠ G from fun e => d.by_ (e ▸ hq)])).trans res.2.2.1
  · intro q qr qy
    change writeBit t.basis G (!t.basis G) q = origin q
    by_cases hqG : q = G
    · subst q; rw [writeBit, Function.update_self, res.2.2.2 G d.br d.by_, aG, Bool.not_not]
    · rw [writeBit, Function.update_of_ne hqG, res.2.2.2 q qr qy, keep q hqG, h.2.2 q qr qy]

theorem jointD_odd_pair (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J, G].Nodup)
    (origin : BasisState) (clean : ∀ q ∈ work L, origin q = false) (sign : origin L.sign = false)
    (Z : Fp) :
    Triple (PairFrame L.r L.y origin
      (oddWord ((if origin J && !origin G then -Z else Z) / 2))
      (oddWord (if origin J then Z else 0))) (jointD_odd L J G)
      (PairFrame L.r L.y origin (oddWord Z) 0) := by
  have d := layout_eq_nodup L hw hn J G hJ hG hJG
  have sf := flagAway L hn L.sign (by simp)
  intro s m h
  let a : State := ⟨s.phase, writeBit s.basis G (!s.basis G)⟩
  have keep (q : Wire) (hq : q ≠ G) : a.basis q = s.basis q := by simp [a, writeBit, hq]
  have aR : regValue L.r a.basis = oddWord ((if origin J && !origin G then -Z else Z) / 2) :=
    (regValue_congr L.r _ _ (fun q hq => keep q (fun e => d.br (e ▸ hq)))).trans h.1
  have aY : regValue L.y a.basis = oddWord (if origin J then Z else 0) :=
    (regValue_congr L.y _ _ (fun q hq => keep q (fun e => d.by_ (e ▸ hq)))).trans h.2.1
  have ac : ∀ q ∈ work L, a.basis q = false := by
    intro q hq
    have off := work_no_data L hn q hq
    have qG : q ≠ G := fun e => hG (by rw [← e]; simp [Layout.wires, BalancedCleanup.Layout.wires, work] at hq ⊢; tauto)
    exact (keep q qG).trans ((h.2.2 q off.1 off.2).trans (clean q hq))
  have aSign : a.basis L.sign = false := by
    have sG : L.sign ≠ G := fun e => hG (by rw [← e]; simp [Layout.wires, BalancedCleanup.Layout.wires])
    exact (keep L.sign sG).trans ((h.2.2 L.sign (fun h => sf (by simp [h])) (fun h => sf (by simp [h]))).trans sign)
  have aJ : a.basis J = origin J := (keep J d.jb).trans (h.2.2 J d.jr d.jy)
  have aG : a.basis G = !origin G := by
    simp [a, writeBit, h.2.2 G d.br d.by_]
  have res := programD_odd_frame L hw hn J G hJ hG hJG (origin J) (!origin G) Z a m aR aY ac aSign aJ aG
  let t := run (programD_odd L J G) m a
  have hrun : run (jointD_odd L J G) m s = ⟨t.phase, writeBit t.basis G (!t.basis G)⟩ := by
    rw [jointD_odd, xwrap_run, run_X, run_X]
  rw [hrun]
  refine ⟨res.1, ?_, ?_, ?_⟩
  · exact (regValue_congr L.r _ _ (fun q hq => by
      change writeBit t.basis G (!t.basis G) q = t.basis q
      simp [writeBit, show q ≠ G from fun e => d.br (e ▸ hq)])).trans res.2.1
  · exact (regValue_congr L.y _ _ (fun q hq => by
      change writeBit t.basis G (!t.basis G) q = t.basis q
      simp [writeBit, show q ≠ G from fun e => d.by_ (e ▸ hq)])).trans res.2.2.1
  · intro q qr qy
    change writeBit t.basis G (!t.basis G) q = origin q
    by_cases hqG : q = G
    · subst q; rw [writeBit, Function.update_self, res.2.2.2 G d.br d.by_, aG, Bool.not_not]
    · rw [writeBit, Function.update_of_ne hqG, res.2.2.2 q qr qy, keep q hqG, h.2.2 q qr qy]

theorem paddedGD_odd_pair (st : BasisState) (clean : ∀ q ∈ BalancedCircuit.work portsJ, st q = false)
    (sign : st (base 2409) = false) (hole : st (base 1032) = false) (Z : Fp) :
    Triple (PairFrame portsJ.r portsJ.y st (oddWord Z) 0) paddedGD_odd
      (PairFrame portsJ.r portsJ.y st
        (oddWord ((if st (base 1028) && !st (base 1) then -Z else Z) / 2))
        (oddWord (if st (base 1028) then Z else 0))) := by
  have j := jointGD_odd_pair portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup st clean
    (by simpa [portsJ_eq] using sign) Z
  intro s m input
  have a719 := off_data 719 (by omega) (by omega)
  have a1032 := off_data 1032 (by omega) (by omega)
  have out := j s m input
  have in719 : s.basis (base 719) = false :=
    (input.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have in1032 : s.basis (base 1032) = false := (input.2.2 _ a1032.1 a1032.2).trans hole
  have o719 : (run (jointGD_odd portsJ (base 1028) (base 1)) m s).basis (base 719) = false :=
    (out.2.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have o1032 : (run (jointGD_odd portsJ (base 1028) (base 1)) m s).basis (base 1032) = false :=
    (out.2.2.2 _ a1032.1 a1032.2).trans hole
  rw [paddedGD_odd, rebind_swap_run _ _ _ s m in719 in1032 o719 o1032]
  exact out

theorem paddedD_odd_pair (st : BasisState) (clean : ∀ q ∈ BalancedCircuit.work portsJ, st q = false)
    (sign : st (base 2409) = false) (hole : st (base 1032) = false) (Z : Fp) :
    Triple (PairFrame portsJ.r portsJ.y st
      (oddWord ((if st (base 1028) && !st (base 1) then -Z else Z) / 2))
      (oddWord (if st (base 1028) then Z else 0))) paddedD_odd
      (PairFrame portsJ.r portsJ.y st (oddWord Z) 0) := by
  have j := jointD_odd_pair portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup st clean
    (by simpa [portsJ_eq] using sign) Z
  intro s m input
  have a719 := off_data 719 (by omega) (by omega)
  have a1032 := off_data 1032 (by omega) (by omega)
  have out := j s m input
  have in719 : s.basis (base 719) = false :=
    (input.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have in1032 : s.basis (base 1032) = false := (input.2.2 _ a1032.1 a1032.2).trans hole
  have o719 : (run (jointD_odd portsJ (base 1028) (base 1)) m s).basis (base 719) = false :=
    (out.2.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have o1032 : (run (jointD_odd portsJ (base 1028) (base 1)) m s).basis (base 1032) = false :=
    (out.2.2.2 _ a1032.1 a1032.2).trans hole
  rw [paddedD_odd, rebind_swap_run _ _ _ s m in719 in1032 o719 o1032]
  exact out

end ECDSAAdd.Entrant.JointOdd1588
end



-- ============================================================================
-- Section 4A: Odd-word first packet definitions, physicality, PieceOK, resources
-- ============================================================================
section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.JointOdd1588
open ECDSAAdd Arithmetic Challenge Baselines BalancedCircuit BalancedField Secp256k1 RecordedQuantum
open MappedCompressed OffsetBorrowedCanonical Rolling1588
open StairWireCheck StairFirstPacketKernel StairFirstPacketHosted

attribute [local irreducible] run wires gateSlots toffoliCount measurementCount paddedGD_odd paddedD_odd

/-- Semantic contract for an odd-word half-cell program `P` on `Q6EndpointCell.ports base (base 2409)`. -/
def OddHalfLaw (P : Program) (divide : Bool) : Prop :=
  ∀ (origin : BasisState), Q6EndpointCell.Clean base origin → ∀ X Y : Fp,
    Triple (PairFrame (Q6EndpointCell.ports base (base 2409)).r
      (Q6EndpointCell.ports base (base 2409)).y origin (oddWord X) (oddWord Y)) P
      (PairFrame (Q6EndpointCell.ports base (base 2409)).r
        (Q6EndpointCell.ports base (base 2409)).y origin
        (oddWord (if divide then (X + (if origin (base 2409) then Y else -Y)) / 2
          else 2 * X + (if origin (base 2409) then -Y else Y))) (oddWord Y))

/-- Support contract for an odd-word half-cell program `P`: all wires lie in the
half-cell envelope `LT48T.env` and avoid the seven omitted wires `LT48T.bad`. -/
def OddHalfSupport (P : Program) : Prop :=
  ∀ q ∈ wires P, q ∈ LT48T.env ∧ q ∉ LT48T.bad

/-- Loaned half-cell window in packet `0` for an arbitrary half-cell program `P`. -/
def halfWindowOdd (P : Program) (active hole : Nat) : Program :=
  ControlLoan1589.loanWindow (g 0 active) (base 2409) (packetCarry 0)
    (renameProgram (Equiv.swap (base 719) (s 0 hole)) P)

/-- Full cell in packet `0` using half-cell program `P`. -/
def cellOdd (divide : Bool) (P : Program) (active hole : Nat) : Program :=
  if divide then
    halfWindowOdd P active hole ++ SW.selW (s 0 active) (base 2409) FrontierSW1591.swapBody
  else
    SW.selW (s 0 active) (base 2409) FrontierSW1591.swapBody ++ halfWindowOdd P active hole

/-- Forward cells 2, 3, 4 of the odd-word first packet. -/
def firstRestZFrontOdd (half : Bool → Program) : Program :=
  triple 2 3 4 d3short ++ triple 1 3 4 e3short ++ cellOdd true (half true) 2 4 ++
  triple 1 3 4 d3 ++ triple 4 1 2 e3 ++ cellOdd true (half true) 3 2 ++
  triple 4 1 2 d3short ++ triple 3 1 2 e3short ++ cellOdd true (half true) 4 2

/-- Forward body prefix of the odd-word first packet (`paddedGD_odd` + S1 swap + cells 2, 3, 4). -/
def firstCellsJFrontOdd (half : Bool → Program) : Program :=
  triple 2 3 4 e3 ++ (paddedGD_odd ++
    (SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody ++ firstRestZFrontOdd half))

/-- Inverse body suffix of the odd-word first packet (cells 4, 3, 2 + S1 swap + `paddedD_odd`). -/
def firstJointBackOdd (half : Bool → Program) : Program :=
  cellOdd false (half false) 4 2 ++
  triple 3 1 2 d3short ++ triple 4 1 2 e3short ++ cellOdd false (half false) 3 2 ++
  triple 4 1 2 d3 ++ triple 1 3 4 e3 ++ cellOdd false (half false) 2 4 ++
  triple 1 3 4 d3short ++ triple 2 3 4 e3short ++
  SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody ++ paddedD_odd ++
  triple 2 3 4 d3

/-- Unshortened odd-word first-packet body model. -/
def firstBodyModelOdd (half : Bool → Program) (divide : Bool) : Program :=
  if divide then firstCellsJFrontOdd half ++ triple 3 1 2 d3
  else triple 3 1 2 e3 ++ firstJointBackOdd half

/-- Shortened odd-word first-packet body (matches `Rolling1588.firstBodyShort`). -/
def firstBodyShortOdd (half : Bool → Program) (divide : Bool) : Program :=
  if divide then firstCellsJFrontOdd half ++ triple 3 1 2 d3short
  else triple 3 1 2 e3short ++ firstJointBackOdd half

/-- Unshortened odd-word first-packet core. -/
def firstCoreModelOdd (half : Bool → Program) (divide : Bool) : Program :=
  Prefix1590.firstDecode ++
    G0CarryLoan5.program (base 1028) (base 0) (base 768) (firstBodyModelOdd half divide) ++
    Prefix1590.firstEncode

/-- Shortened odd-word first-packet core. -/
def firstCoreOdd (half : Bool → Program) (divide : Bool) : Program :=
  (if divide then Prefix1590.firstDecode else firstDecodeShort) ++
    G0CarryLoan5.program (base 1028) (base 0) (base 768) (firstBodyShortOdd half divide) ++
    (if divide then firstEncodeShort else Prefix1590.firstEncode)

/-- Unshortened odd-word first packet before `OB5.sig 511`. -/
def firstPacketModelOdd (half : Bool → Program) (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (firstCoreModelOdd half divide)

/-- Shortened odd-word first packet before `OB5.sig 511`. -/
def firstPacketOdd (half : Bool → Program) (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (firstCoreOdd half divide)

/-- Placed odd-word first packet (after `OB5.sig 511`). -/
def placedFirstPacketOdd (half : Bool → Program) (divide : Bool) : Program :=
  renameProgram (OB5.sig 511) (firstPacketOdd half divide)

/-- Hosted odd-word first packet on `hosts 87` (matches `StairFirstPacketHosted.hostedFirstPacket`). -/
def hostedFirstPacketOdd (half : Bool → Program) (divide : Bool) : Program :=
  StairLoan.rebindMany StairSchedule.exclusiveRoles
    (StairV3Primitives.hostPlan.firstPacket divide)
    (placedFirstPacketOdd half divide)

/-! ### Physicality -/

private theorem selected_physical (src flag : Wire) (P : Program) (hne : src ≠ flag)
    (hP : GatePhysical P) : GatePhysical (SW.selW src flag P) := by
  simp only [SW.selW, gatePhysical_append]
  refine ⟨⟨?_, hP⟩, ?_⟩
  · simp [GatePhysical, PhysicalInstr, ProperGate, hne]
  · simp [GatePhysical, PhysicalInstr, hne]

private theorem halfWindowOdd_physical (P : Program) (active hole : Nat)
    (ha : active < 5) (hP : GatePhysical P) :
    GatePhysical (halfWindowOdd P active hole) := by
  have h1 : g 0 active ≠ base 2409 := HostOB5.host_ne _ _ (by omega)
  have hre : GatePhysical (renameProgram (Equiv.swap (packetCarry 0) (g 0 active))
      (renameProgram (Equiv.swap (base 719) (s 0 hole)) P)) :=
    gatePhysical_rename _ (Equiv.swap _ _).injective _
      (gatePhysical_rename _ (Equiv.swap _ _).injective _ hP)
  simp only [halfWindowOdd, ControlLoan1589.loanWindow, gatePhysical_append]
  refine ⟨⟨?_, hre⟩, ?_⟩
  · simp [GatePhysical, PhysicalInstr, ProperGate, h1, Ne.symm h1]
  · simp [GatePhysical, PhysicalInstr, ProperGate, h1, Ne.symm h1]

private theorem swapBody_physical : GatePhysical FrontierSW1591.swapBody := by
  rw [FrontierSW1591.swapBody]
  have nd := FrontierReplay1591.base_sign_nd
  have hr : (Q6EndpointCell.ports base (base 2409)).r = (balancedSharedPorts base (base 2409)).r := by
    rw [Q6EndpointCell.ports_r]
  have hy : (Q6EndpointCell.ports base (base 2409)).y = (balancedSharedPorts base (base 2409)).y := by
    rw [Q6EndpointCell.ports_y]
  rw [hr, hy] at nd
  exact swapRegisters_physical (base 2409) _ _ nd

private theorem cellOdd_physical (divide : Bool) (P : Program) (active hole : Nat)
    (ha : active < 5) (hP : GatePhysical P) : GatePhysical (cellOdd divide P active hole) := by
  have hsw : GatePhysical (SW.selW (s 0 active) (base 2409) FrontierSW1591.swapBody) :=
    selected_physical _ _ _ (HostOB5.host_ne _ _ (by omega)) swapBody_physical
  have hhw := halfWindowOdd_physical P active hole ha hP
  cases divide <;> simp only [cellOdd, Bool.false_eq_true, if_false, if_true, gatePhysical_append]
  · exact ⟨hsw, hhw⟩
  · exact ⟨hhw, hsw⟩

private theorem triple_physical (a b c : Nat) (ha : a < 5) (hb : b < 5) (hc : c < 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (P : Program) (hsub : wires P ⊆ Finset.range 6) (hP : GatePhysical P) :
    GatePhysical (triple a b c P) := by
  apply gatePhysical_rename_support _ P _ hP
  intro x hx y hy heq
  have hx' : x < 6 := Finset.mem_range.mp (hsub hx)
  have hy' : y < 6 := Finset.mem_range.mp (hsub hy)
  interval_cases x <;> interval_cases y
  all_goals first
    | rfl
    | (simp [tripleMap, g, s, base_injective.eq_iff] at heq; try omega)

private theorem c3_physical_odd :
    GatePhysical e3 ∧ GatePhysical d3 ∧ GatePhysical e3short ∧ GatePhysical d3short := by
  repeat' apply And.intro
  all_goals apply physicalGateCheck_correct
  all_goals decide +kernel

private theorem firstEnds_physical :
    GatePhysical Prefix1590.firstDecode ∧ GatePhysical firstDecodeShort ∧
    GatePhysical Prefix1590.firstEncode ∧ GatePhysical firstEncodeShort := by
  have codecs := ParityCodec5New.first_mapped_physical (History5.historyMap base 0)
    (History5.historyMap_injective base base_pool_nodup 0 (by decide))
  have hds : firstDecodeShort.Sublist Prefix1590.firstDecode := by
    have h1 : (FirstNonzeroCodec.decodeFirst.take 124 ++ FirstNonzeroCodec.decodeFirst.drop 125).Sublist
        FirstNonzeroCodec.decodeFirst := by
      have hlen : 124 < FirstNonzeroCodec.decodeFirst.length := by decide +kernel
      conv_rhs => rw [← List.take_append_drop 124 FirstNonzeroCodec.decodeFirst]
      apply List.Sublist.append (List.Sublist.refl _)
      have hdrop : FirstNonzeroCodec.decodeFirst.drop 124 =
          FirstNonzeroCodec.decodeFirst[124] :: FirstNonzeroCodec.decodeFirst.drop 125 :=
        List.drop_eq_getElem_cons hlen
      rw [hdrop]
      exact List.sublist_cons_self _ _
    exact List.Sublist.map _ (h1.append (List.Sublist.refl _))
  have hes : firstEncodeShort.Sublist Prefix1590.firstEncode := by
    have h1 : (FirstNonzeroCodec.encodeFirst.take 15 ++ FirstNonzeroCodec.encodeFirst.drop 16).Sublist
        FirstNonzeroCodec.encodeFirst := by
      have hlen : 15 < FirstNonzeroCodec.encodeFirst.length := by decide +kernel
      conv_rhs => rw [← List.take_append_drop 15 FirstNonzeroCodec.encodeFirst]
      apply List.Sublist.append (List.Sublist.refl _)
      have hdrop : FirstNonzeroCodec.encodeFirst.drop 15 =
          FirstNonzeroCodec.encodeFirst[15] :: FirstNonzeroCodec.encodeFirst.drop 16 :=
        List.drop_eq_getElem_cons hlen
      rw [hdrop]
      exact List.sublist_cons_self _ _
    exact List.Sublist.map _ ((List.Sublist.refl _).append h1)
  exact ⟨codecs.2, fun i hi => codecs.2 i (hds.subset hi),
    codecs.1, fun i hi => codecs.1 i (hes.subset hi)⟩

theorem firstBodyShortOdd_physical (half : Bool → Program) (divide : Bool)
    (hP : GatePhysical (half divide)) : GatePhysical (firstBodyShortOdd half divide) := by
  have fc := c3_physical_odd
  have fs := Rolling1588.c3_support
  have hsw1 : GatePhysical (SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody) :=
    selected_physical _ _ _ (HostOB5.host_ne _ _ (by omega)) swapBody_physical
  have tr_e3 (a b c : Nat) (ha : a < 5) (hb : b < 5) (hc : c < 5) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) :=
    triple_physical a b c ha hb hc h1 h2 h3 e3 fs.1 fc.1
  have tr_d3 (a b c : Nat) (ha : a < 5) (hb : b < 5) (hc : c < 5) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) :=
    triple_physical a b c ha hb hc h1 h2 h3 d3 fs.2.1 fc.2.1
  have tr_e3s (a b c : Nat) (ha : a < 5) (hb : b < 5) (hc : c < 5) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) :=
    triple_physical a b c ha hb hc h1 h2 h3 e3short fs.2.2.1 fc.2.2.1
  have tr_d3s (a b c : Nat) (ha : a < 5) (hb : b < 5) (hc : c < 5) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) :=
    triple_physical a b c ha hb hc h1 h2 h3 d3short fs.2.2.2 fc.2.2.2
  cases divide
  · simp only [firstBodyShortOdd, firstJointBackOdd, Bool.false_eq_true, if_false, gatePhysical_append]
    exact ⟨tr_e3s 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cellOdd_physical false (half false) 4 2 (by decide) hP,
        tr_d3s 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
        tr_e3s 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
        cellOdd_physical false (half false) 3 2 (by decide) hP⟩,
        tr_d3 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
        tr_e3 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
        cellOdd_physical false (half false) 2 4 (by decide) hP⟩,
        tr_d3s 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
        tr_e3s 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
        hsw1⟩,
        paddedD_odd_physical⟩,
        tr_d3 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩⟩
  · simp only [firstBodyShortOdd, firstCellsJFrontOdd, firstRestZFrontOdd, if_true, gatePhysical_append]
    exact ⟨⟨tr_e3 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      paddedGD_odd_physical,
      hsw1,
      ⟨⟨⟨⟨⟨⟨⟨⟨tr_d3s 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        tr_e3s 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
        cellOdd_physical true (half true) 2 4 (by decide) hP⟩,
        tr_d3 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
        tr_e3 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
        cellOdd_physical true (half true) 3 2 (by decide) hP⟩,
        tr_d3s 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
        tr_e3s 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
        cellOdd_physical true (half true) 4 2 (by decide) hP⟩⟩,
      tr_d3s 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

theorem placedFirstPacketOdd_physical (half : Bool → Program) (divide : Bool)
    (hP : GatePhysical (half divide)) : GatePhysical (placedFirstPacketOdd half divide) := by
  have fe := firstEnds_physical
  have hb : GatePhysical (G0CarryLoan5.program (base 1028) (base 0) (base 768) (firstBodyShortOdd half divide)) :=
    G0CarryLoan5.physical (base 1028) (base 0) (base 768) (firstBodyShortOdd half divide)
      (by decide) (firstBodyShortOdd_physical half divide hP)
  have hc : GatePhysical (firstCoreOdd half divide) := by
    cases divide
    · simp only [firstCoreOdd, Bool.false_eq_true, if_false, gatePhysical_append]
      exact ⟨⟨fe.2.1, hb⟩, fe.2.2.1⟩
    · simp only [firstCoreOdd, if_true, gatePhysical_append]
      exact ⟨⟨fe.1, hb⟩, fe.2.2.2⟩
  exact gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _
    (gatePhysical_rename _ (shifted (Placement5.pi 0)).injective _ hc)

theorem hostedFirstPacketOdd_physical (half : Bool → Program) (divide : Bool)
    (hP : GatePhysical (half divide)) : GatePhysical (hostedFirstPacketOdd half divide) :=
  StairLoan.rebindMany_physical _ _ _ (placedFirstPacketOdd_physical half divide hP)

/-! ### Support & `PieceOK physicalHoles` (`Q = 1,542`) -/

private theorem ok_halfWindowOdd {c : Wire → Bool} (P : Program) (hsup : OddHalfSupport P)
    (a h : Nat) (hg : c (g 0 a) = true) (hf : c (base 2409) = true)
    (hh : LT48T.env.all (fun z => decide (z ∈ LT48T.bad) ||
      c (Equiv.swap (packetCarry 0) (g 0 a) (Equiv.swap (base 719) (s 0 h) z))) = true) :
    LT48T.Ok c (halfWindowOdd P a h) := by
  apply LT48T.ok_loanWindow _ _ _ _ hg hf
  apply LT48T.ok_rename
  intro z hz
  obtain ⟨he, hb⟩ := hsup z hz
  have t := List.all_eq_true.mp hh z he
  simp only [Bool.or_eq_true, decide_eq_true_eq] at t
  exact t.resolve_left hb

private theorem ok_cellOdd {c : Wire → Bool} (divide : Bool) (P : Program) (hsup : OddHalfSupport P)
    (a h : Nat) (hsw : LT48T.Ok c FrontierSW1591.swapBody)
    (hs : c (s 0 a) = true) (hb : c (base 2409) = true) (hg : c (g 0 a) = true)
    (hh : LT48T.env.all (fun z => decide (z ∈ LT48T.bad) ||
      c (Equiv.swap (packetCarry 0) (g 0 a) (Equiv.swap (base 719) (s 0 h) z))) = true) :
    LT48T.Ok c (cellOdd divide P a h) := by
  cases divide
  · exact LT48T.ok_append (LT48T.ok_selW _ _ _ hs hb hsw) (ok_halfWindowOdd P hsup a h hg hb hh)
  · exact LT48T.ok_append (ok_halfWindowOdd P hsup a h hg hb hh) (LT48T.ok_selW _ _ _ hs hb hsw)

private theorem ok_padded_odd {c : Wire → Bool} (P : Program)
    (hsub : wires P ⊆ JointInverse1588.kernelSites)
    (hfree : ∀ i, (i = 0 ∨ i = 516 ∨ i = 719 ∨ i = 1541) → base i ∉ wires P)
    (h760 : base 760 ∉ wires P)
    (h : LT48T.kList.all (fun z => decide (z ∈ LT48T.badP) || c z) = true) :
    LT48T.Ok c P := by
  intro z hz
  have m : z ∈ LT48T.kList := List.mem_toFinset.mp (hsub hz)
  have hb : z ∉ LT48T.badP := by
    intro hb
    simp only [LT48T.badP, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfree 0 (Or.inl rfl) hz
    · exact hfree 516 (Or.inr (Or.inl rfl)) hz
    · exact hfree 719 (Or.inr (Or.inr (Or.inl rfl))) hz
    · exact hfree 1541 (Or.inr (Or.inr (Or.inr rfl))) hz
    · exact h760 hz
  have t := List.all_eq_true.mp h z m
  simp only [Bool.or_eq_true, decide_eq_true_eq] at t
  exact t.resolve_left hb

private theorem mem_q6_ids_r (j : Nat) (h1 : 2056 ≤ j) (h2 : j < 2312) : j ∈ Q6EndpointCell.ids := by
  by_cases h0 : j = 2056
  · subst h0; unfold Q6EndpointCell.ids
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; decide
  · by_cases h1' : j = 2311
    · subst h1'; unfold Q6EndpointCell.ids
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      apply List.mem_append_left; decide
    · unfold Q6EndpointCell.ids
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_range'_1.mpr ⟨by omega, by omega⟩

private theorem mem_q6_ids_y (j : Nat) (h1 : 770 ≤ j) (h2 : j < 1026) : j ∈ Q6EndpointCell.ids := by
  by_cases h1' : j = 1025
  · subst h1'; unfold Q6EndpointCell.ids
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; decide
  · unfold Q6EndpointCell.ids
    apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_range'_1.mpr ⟨by omega, by omega⟩

private theorem mem_q6_ids_carry (j : Nat) (h1 : 512 ≤ j) (h2 : j < 765) : j ∈ Q6EndpointCell.ids := by
  unfold Q6EndpointCell.ids
  apply List.mem_append_left; apply List.mem_append_right
  exact List.mem_range'_1.mpr ⟨by omega, by omega⟩

private theorem swapBody_wires_sub :
    wires FrontierSW1591.swapBody ⊆
      (base 2409 :: ((balancedSharedPorts base (base 2409)).r ++ (balancedSharedPorts base (base 2409)).y)).toFinset := by
  rw [FrontierSW1591.swapBody]
  exact swapRegisters_wires (base 2409) _ _ (by
    rw [balancedSharedPorts_r, balancedSharedPorts_y, wireBlock_length, wireBlock_length])

theorem placedFirstPacketOdd_passSup (half : Bool → Program) (divide : Bool)
    (hsup : OddHalfSupport (half divide)) :
    allSites fpSup (placedFirstPacketOdd half divide) = true := by
  have hG : LT48T.env.all (fun z => LT48T.badB z || LT48T.k6specB z || LT48T.QFB z) = true := by decide +kernel
  have hsw : LT48T.Ok LT48T.QFB FrontierSW1591.swapBody := by
    intro q hq
    have hm := swapBody_wires_sub hq
    rw [balancedSharedPorts_r, balancedSharedPorts_y] at hm
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, wireBlock, List.mem_map,
      List.mem_range'_1] at hm
    have hmem : q ∈ LT48T.env ∧ LT48T.badB q = false ∧ LT48T.k6specB q = false := by
      have hid (j : Nat) (hj : j ∈ Q6EndpointCell.ids) : base j ∈ LT48T.env :=
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
      have hneB (a b : Nat) (h : a ≠ b) : Nat.beq (base a) (base b) = false := by
        rw [LT48T.beqD, decide_eq_false_iff_not]; exact fun e => h (base_injective e)
      have hbad (j : Nat) (h1 : j ≠ 760) (h2 : j ≠ 765) (h3 : j ≠ 766) (h4 : j ≠ 767)
          (h5 : j ≠ 1026) (h6 : j ≠ 1541) (h7 : j ≠ 2312) : LT48T.badB (base j) = false := by
        simp only [LT48T.badB, Bool.or_eq_false_iff]
        exact ⟨⟨⟨⟨⟨⟨hneB j 760 h1, hneB j 765 h2⟩, hneB j 766 h3⟩, hneB j 767 h4⟩,
          hneB j 1026 h5⟩, hneB j 1541 h6⟩, hneB j 2312 h7⟩
      have hk6 (j : Nat) (h1 : j ≠ 516) (h2 : j ≠ 719) (h3 : j ≠ 2) (h4 : j ≠ 3)
          (h5 : j ≠ 4) (h6 : j ≠ 1030) (h7 : j ≠ 1032) : LT48T.k6specB (base j) = false := by
        simp only [LT48T.k6specB, packetCarry, g, s, Nat.mul_zero, Nat.zero_add, Nat.add_zero,
          Bool.or_eq_false_iff]
        exact ⟨hneB j 516 h1, hneB j 719 h2, hneB j 2 h3, hneB j 3 h4, hneB j 4 h5,
          hneB j 1030 h6, hneB j 1032 h7⟩
      rcases hm with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exact ⟨List.mem_cons_self .., hbad 2409 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          hk6 2409 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
      · exact ⟨hid j (mem_q6_ids_r j hj.1 hj.2),
          hbad j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          hk6 j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
      · exact ⟨hid j (mem_q6_ids_y j hj.1 hj.2),
          hbad j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          hk6 j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
    have t := List.all_eq_true.mp hG q hmem.1
    rw [hmem.2.1, hmem.2.2] at t
    exact t
  have hkList : LT48T.kList.all (fun z => decide (z ∈ LT48T.badP) || LT48T.QFB z) = true := by
    rw [LT48T.kList_hyp_eqB]; decide +kernel
  have hcell (a h : Nat) (ha : g 0 a ∈ LT48T.k6S) (hh : s 0 h ∈ LT48T.k6S)
      (hs : LT48T.QFB (s 0 a) = true) (hb : LT48T.QFB (base 2409) = true) (hg : LT48T.QFB (g 0 a) = true)
      (hC : LT48T.k6S.all (fun z => !(LT48T.maskL LT48T.env).testBit z || LT48T.badB z ||
        LT48T.QFB (StairPlaceFast.swB (packetCarry 0) (g 0 a) (StairPlaceFast.swB (base 719) (s 0 h) z))) = true) :
      LT48T.Ok LT48T.QFB (cellOdd divide (half divide) a h) :=
    ok_cellOdd divide (half divide) hsup a h hsw hs hb hg
      (by rw [LT48T.env_hyp_eqB]; exact LT48T.k6_cell a h ha hh hG hC)
  have hbody : LT48T.Ok LT48T.QF (firstBodyShortOdd half divide) := by
    rw [LT48T.QF_eqB]
    have c2 := hcell 2 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    have c3 := hcell 3 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    have c4 := hcell 4 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    have st1 : LT48T.Ok LT48T.QFB (SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody) :=
      LT48T.ok_selW _ _ _ (by decide +kernel) (by decide +kernel) hsw
    cases divide
    · have pD : LT48T.Ok LT48T.QFB paddedD_odd :=
        ok_padded_odd paddedD_odd paddedD_odd_support paddedD_odd_free paddedD_odd_760_free hkList
      simp only [firstBodyShortOdd, firstJointBackOdd, Bool.false_eq_true, if_false]
      exact LT48T.ok_append (LT48T.ok_triple _ _ _ _ (by decide +kernel))
        (LT48T.ok_append (LT48T.ok_append (LT48T.ok_append (LT48T.ok_append (LT48T.ok_append
          (LT48T.ok_append (LT48T.ok_append (LT48T.ok_append (LT48T.ok_append (LT48T.ok_append
            (LT48T.ok_append c4 (LT48T.ok_triple _ _ _ _ (by decide +kernel)))
            (LT48T.ok_triple _ _ _ _ (by decide +kernel))) c3)
            (LT48T.ok_triple _ _ _ _ (by decide +kernel)))
            (LT48T.ok_triple _ _ _ _ (by decide +kernel))) c2)
            (LT48T.ok_triple _ _ _ _ (by decide +kernel)))
            (LT48T.ok_triple _ _ _ _ (by decide +kernel))) st1) pD)
            (LT48T.ok_triple _ _ _ _ (by decide +kernel)))
    · have pGD : LT48T.Ok LT48T.QFB paddedGD_odd :=
        ok_padded_odd paddedGD_odd paddedGD_odd_support paddedGD_odd_free paddedGD_odd_760_free hkList
      simp only [firstBodyShortOdd, firstCellsJFrontOdd, firstRestZFrontOdd, if_true]
      have rz : LT48T.Ok LT48T.QFB (firstRestZFrontOdd half) :=
        LT48T.ok_append (LT48T.ok_append (LT48T.ok_append (LT48T.ok_append (LT48T.ok_append
          (LT48T.ok_append (LT48T.ok_append (LT48T.ok_append
            (LT48T.ok_triple _ _ _ _ (by decide +kernel))
            (LT48T.ok_triple _ _ _ _ (by decide +kernel))) c2)
            (LT48T.ok_triple _ _ _ _ (by decide +kernel)))
            (LT48T.ok_triple _ _ _ _ (by decide +kernel))) c3)
            (LT48T.ok_triple _ _ _ _ (by decide +kernel)))
            (LT48T.ok_triple _ _ _ _ (by decide +kernel))) c4
      exact LT48T.ok_append
        (LT48T.ok_append (LT48T.ok_triple _ _ _ _ (by decide +kernel))
          (LT48T.ok_append pGD (LT48T.ok_append st1 rz)))
        (LT48T.ok_triple _ _ _ _ (by decide +kernel))
  have hloan : LT48T.Ok LT48T.Q (G0CarryLoan5.program (base 1028) (base 0) (base 768)
      (firstBodyShortOdd half divide)) :=
    LT48T.ok_append (LT48T.ok_append (LT48T.ok_of_all (by decide +kernel))
      (LT48T.ok_rename _ _ hbody)) (LT48T.ok_of_all (by decide +kernel))
  have hcore : LT48T.Ok LT48T.Q (firstCoreOdd half divide) := by
    cases divide
    · exact LT48T.ok_append (LT48T.ok_append (LT48T.ok_of_all (by decide +kernel)) hloan)
        (LT48T.ok_of_all (by decide +kernel))
    · exact LT48T.ok_append (LT48T.ok_append (LT48T.ok_of_all (by decide +kernel)) hloan)
        (LT48T.ok_of_all (by decide +kernel))
  exact LT48T.allSites_of_ok (LT48T.ok_rename _ _ (LT48T.ok_rename _ _ hcore))

theorem placedFirstPacketOdd_pass (half : Bool → Program) (divide : Bool)
    (hsup : OddHalfSupport (half divide)) :
    ∀ x ∈ wires (placedFirstPacketOdd half divide), firstCheck x = true := fun x hx =>
  firstCheck_of_sup x (allSites_sound _ _ (placedFirstPacketOdd_passSup half divide hsup) x hx)

theorem placedFirstPacketOdd_hostsFree (half : Bool → Program) (divide : Bool)
    (hsup : OddHalfSupport (half divide)) :
    ∀ q ∈ StairV3Primitives.hostPlan.firstPacket divide,
      q ∉ wires (placedFirstPacketOdd half divide) := by
  rw [hostPlan_firstPacket]
  intro q hq used
  have h := placedFirstPacketOdd_pass half divide hsup q used
  simp only [firstCheck, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact h.1 hq

theorem hostedFirstPacketOdd_avoids (half : Bool → Program) (divide : Bool)
    (hsup : OddHalfSupport (half divide)) :
    ∀ q ∈ StairSchedule.exclusiveRoles, q ∉ wires (hostedFirstPacketOdd half divide) :=
  StairLoan.rebindMany_roles_free _ _ _ (roles_hosts_length divide)
    (roles_hosts_nodup divide) (placedFirstPacketOdd_hostsFree half divide hsup)

theorem hostedFirstPacketOdd_placed (half : Bool → Program) (divide : Bool)
    (hsup : OddHalfSupport (half divide)) :
    ∀ x ∈ wires (hostedFirstPacketOdd half divide),
      lowPlace x ∈ StairHoleSupport.recordArena ∧
      lowPlace x ∉ StairHoleSupport.oldHoles ∧
      lowPlace x ∉ StairPhysicalInventory.physicalHoles := by
  intro x hx
  have avoid := hostedFirstPacketOdd_avoids half divide hsup
  have hx' := hx
  rw [hostedFirstPacketOdd] at hx'
  rcases rebindMany_support _ _ _ x hx' with hh | hr | hp
  · rw [hostPlan_firstPacket] at hh
    exact goodNat_spec (List.all_eq_true.mp hostsGood x hh)
  · exact absurd hx (avoid x hr)
  · have h := placedFirstPacketOdd_pass half divide hsup x hp
    simp only [firstCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h.2 with hr | hg
    · rw [← exclusiveRoles_eq_nat] at hr
      exact absurd hx (avoid x hr)
    · exact goodNat_spec hg

/-- `PieceOK holes lowPlace` for `hostedFirstPacketOdd`, for every hole list inside the
44 physical holes (`Q = 1,542`). -/
theorem hostedFirstPacketOdd_pieceOK (half : Bool → Program)
    (holes : List Wire) (hsub : ∀ q ∈ holes, q ∈ StairPhysicalInventory.physicalHoles)
    (divide : Bool) (hsup : OddHalfSupport (half divide)) :
    (∀ x ∈ wires (hostedFirstPacketOdd half divide),
        lowPlace x ∈ StairHoleSupport.recordArena ∧
          lowPlace x ∉ StairHoleSupport.oldHoles) ∧
      (∀ x ∈ wires (hostedFirstPacketOdd half divide), lowPlace x ∉ holes) := by
  refine ⟨fun x hx => ?_, fun x hx hh => ?_⟩
  · have h := hostedFirstPacketOdd_placed half divide hsup x hx
    exact ⟨h.1, h.2.1⟩
  · exact (hostedFirstPacketOdd_placed half divide hsup x hx).2.2 (hsub _ hh)

/-! ### Exact Resource Theorems (`T`, `M`, `gateSlots`) -/

private theorem selW_counts (src flag : Wire) (P : Program) :
    toffoliCount (SW.selW src flag P) = toffoliCount P ∧
    measurementCount (SW.selW src flag P) = measurementCount P + 1 := by
  simp only [SW.selW, toffoliCount_append, measurementCount_append]
  have h1 : toffoliCount [.CX src flag] = 0 ∧ measurementCount [.CX src flag] = 0 := by
    simp only [toffoliCount, measurementCount]; exact ⟨trivial, trivial⟩
  have h2 : toffoliCount [.measureX flag [] [.Z src]] = 0 ∧
      measurementCount [.measureX flag [] [.Z src]] = 1 := by
    simp only [toffoliCount, measurementCount]; exact ⟨trivial, trivial⟩
  omega

private theorem swapBody_counts :
    toffoliCount FrontierSW1591.swapBody = 256 ∧ measurementCount FrontierSW1591.swapBody = 0 := by
  have a := Rolling1588.cell_resources true 0 3 2
  have b := Rolling1588.halfWindow_counts true 0 3 2
  have c := selW_counts (s 0 3) (base 2409) FrontierSW1591.swapBody
  simp only [Rolling1588.cell, if_true, toffoliCount_append, measurementCount_append] at a
  exact ⟨by omega, by omega⟩

theorem halfWindowOdd_counts (P : Program) (active hole : Nat) :
    toffoliCount (halfWindowOdd P active hole) = toffoliCount P ∧
    measurementCount (halfWindowOdd P active hole) = measurementCount P + 1 := by
  have a := ControlLoan1589.loanWindow_counts (g 0 active) (base 2409) (packetCarry 0)
    (renameProgram (Equiv.swap (base 719) (s 0 hole)) P)
  have b := selW_counts (g 0 active) (base 2409)
    (renameProgram (Equiv.swap (base 719) (s 0 hole)) P)
  simp only [renameProgram_counts] at b
  exact ⟨a.1.trans b.1, a.2.trans b.2⟩

theorem cellOdd_counts (divide : Bool) (P : Program) (active hole : Nat) :
    toffoliCount (cellOdd divide P active hole) = toffoliCount P + 256 ∧
    measurementCount (cellOdd divide P active hole) = measurementCount P + 2 := by
  have a := halfWindowOdd_counts P active hole
  have b := selW_counts (s 0 active) (base 2409) FrontierSW1591.swapBody
  rw [swapBody_counts.1, swapBody_counts.2] at b
  cases divide <;> simp only [cellOdd, Bool.false_eq_true, if_false, if_true,
    toffoliCount_append, measurementCount_append] <;> exact ⟨by omega, by omega⟩

theorem halfWindowOdd_slots (P : Program) (active hole : Nat) :
    gateSlots (halfWindowOdd P active hole) = gateSlots P + 5 := by
  rw [halfWindowOdd, ControlLoan1589.loanWindow_slots, SW.selW_slots, rename_gateSlots]

theorem cellOdd_slots (divide : Bool) (P : Program) (active hole : Nat) :
    gateSlots (cellOdd divide P active hole) = gateSlots P + 776 := by
  have a := halfWindowOdd_slots P active hole
  have sw : gateSlots (SW.selW (s 0 active) (base 2409) FrontierSW1591.swapBody) = 771 := by
    rw [SW.selW_slots, FrontierSW1591.swapBody, swapRegisters_gateSlots,
      balancedSharedPorts_r, balancedSharedPorts_y, wireBlock_length, wireBlock_length]
    decide
  cases divide
  · rw [cellOdd, if_neg (by decide), gateSlots_append, a, sw]; omega
  · rw [cellOdd, if_pos rfl, gateSlots_append, a, sw]

/-- Exact Toffoli and measurement count comparison of `placedFirstPacketOdd half divide`
against `Rolling1588.placedFirstPacket divide`. -/
theorem placedFirstPacketOdd_counts_rel (half : Bool → Program) (divide : Bool) :
    toffoliCount (placedFirstPacketOdd half divide) +
      (if divide then 7 + 3 * 1020 else 8 + 3 * 1020) =
      toffoliCount (Rolling1588.placedFirstPacket divide) + 3 * toffoliCount (half divide) ∧
    measurementCount (placedFirstPacketOdd half divide) + (514 + 3 * 1021) =
      measurementCount (Rolling1588.placedFirstPacket divide) + 3 * measurementCount (half divide) := by
  have c2 := cellOdd_counts divide (half divide) 2 4
  have c3 := cellOdd_counts divide (half divide) 3 2
  have c4 := cellOdd_counts divide (half divide) 4 2
  have r2 := Rolling1588.cell_resources divide 0 2 4
  have r3 := Rolling1588.cell_resources divide 0 3 2
  have r4 := Rolling1588.cell_resources divide 0 4 2
  have g1 := G0CarryLoan5.counts (base 1028) (base 0) (base 768) (firstBodyShortOdd half divide)
  have g2 := G0CarryLoan5.counts (base 1028) (base 0) (base 768) (Rolling1588.firstBodyShort divide)
  simp only [placedFirstPacketOdd, firstPacketOdd, firstCoreOdd,
    Rolling1588.placedFirstPacket, Rolling1588.firstPacket, Rolling1588.firstCore,
    renameProgram_counts, toffoliCount_append, measurementCount_append]
  cases divide
  · have pOdd := paddedD_odd_counts
    have pOld := JointInverse1588.paddedD_counts
    simp only [firstBodyShortOdd, firstJointBackOdd,
      Rolling1588.firstBodyShort, Rolling1588.firstJointBack,
      Bool.false_eq_true, if_false, toffoliCount_append, measurementCount_append] at g1 g2 ⊢
    exact ⟨by omega, by omega⟩
  · have pOdd := paddedGD_odd_counts
    have pOld := JointForward1588.paddedGD_counts
    simp only [firstBodyShortOdd, firstCellsJFrontOdd, firstRestZFrontOdd,
      Rolling1588.firstBodyShort, Rolling1588.firstCellsJFront, Rolling1588.firstRestZFront,
      if_true, toffoliCount_append, measurementCount_append] at g1 g2 ⊢
    exact ⟨by omega, by omega⟩

/-- Exact T/M savings of `placedFirstPacketOdd` when `half` has `1,017 T / 1,017 M`
(`-16 T / -526 M` for `divide = true`, `-17 T / -526 M` for `divide = false`; `-33 T / -1,052 M` combined). -/
theorem placedFirstPacketOdd_counts_delta (half : Bool → Program) (divide : Bool)
    (hT : toffoliCount (half divide) = 1017) (hM : measurementCount (half divide) = 1017) :
    toffoliCount (placedFirstPacketOdd half divide) + (if divide then 16 else 17) =
      toffoliCount (Rolling1588.placedFirstPacket divide) ∧
    measurementCount (placedFirstPacketOdd half divide) + 526 =
      measurementCount (Rolling1588.placedFirstPacket divide) := by
  have rel := placedFirstPacketOdd_counts_rel half divide
  rw [hT, hM] at rel
  cases divide <;> simp only [Bool.false_eq_true, if_false, if_true] at rel ⊢ <;> exact ⟨by omega, by omega⟩

/-- Exact T/M counts of `hostedFirstPacketOdd` equal those of `placedFirstPacketOdd`. -/
theorem hostedFirstPacketOdd_counts (half : Bool → Program) (divide : Bool) :
    toffoliCount (hostedFirstPacketOdd half divide) = toffoliCount (placedFirstPacketOdd half divide) ∧
    measurementCount (hostedFirstPacketOdd half divide) = measurementCount (placedFirstPacketOdd half divide) :=
  StairLoan.rebindMany_counts _ _ _

/-- Exact T/M savings of `hostedFirstPacketOdd` against `StairFirstPacketHosted.hostedFirstPacket`. -/
theorem hostedFirstPacketOdd_counts_delta (half : Bool → Program) (divide : Bool)
    (hT : toffoliCount (half divide) = 1017) (hM : measurementCount (half divide) = 1017) :
    toffoliCount (hostedFirstPacketOdd half divide) + (if divide then 16 else 17) =
      toffoliCount (StairFirstPacketHosted.hostedFirstPacket divide) ∧
    measurementCount (hostedFirstPacketOdd half divide) + 526 =
      measurementCount (StairFirstPacketHosted.hostedFirstPacket divide) := by
  have h1 := hostedFirstPacketOdd_counts half divide
  have h2 := StairLoan.rebindMany_counts StairSchedule.exclusiveRoles
    (StairV3Primitives.hostPlan.firstPacket divide) (Rolling1588.placedFirstPacket divide)
  have d := placedFirstPacketOdd_counts_delta half divide hT hM
  rw [hostedFirstPacket]
  exact ⟨by omega, by omega⟩

/-- `gateSlots` comparison of `placedFirstPacketOdd` against `Rolling1588.placedFirstPacket`:
replaces `paddedGD`/`paddedD` with `paddedGD_odd`/`paddedD_odd` (`≤ 7900` / `≤ 8160` slots)
and the three half-cells with `half divide`. -/
theorem placedFirstPacketOdd_slots_le (half : Bool → Program) (divide : Bool)
    (hS : gateSlots (half divide) ≤ gateSlots (R2Life760.half760 divide)) :
    gateSlots (placedFirstPacketOdd half divide) ≤
      gateSlots (Rolling1588.placedFirstPacket divide) + (if divide then 7900 else 8160) := by
  have c2 := cellOdd_slots divide (half divide) 2 4
  have c3 := cellOdd_slots divide (half divide) 3 2
  have c4 := cellOdd_slots divide (half divide) 4 2
  have oldCell (a h : Nat) :
      gateSlots (Rolling1588.cell divide 0 a h) = gateSlots (R2Life760.half760 divide) + 776 := by
    have hs := cellOdd_slots divide (R2Life760.half760 divide) a h
    have eq : Rolling1588.cell divide 0 a h = cellOdd divide (R2Life760.half760 divide) a h := by
      cases divide <;> rfl
    rw [eq, hs]
  have r2 := oldCell 2 4
  have r3 := oldCell 3 2
  have r4 := oldCell 4 2
  have g1 := G0CarryLoan5.slots (base 1028) (base 0) (base 768) (firstBodyShortOdd half divide)
  have g2 := G0CarryLoan5.slots (base 1028) (base 0) (base 768) (Rolling1588.firstBodyShort divide)
  simp only [placedFirstPacketOdd, firstPacketOdd, firstCoreOdd,
    Rolling1588.placedFirstPacket, Rolling1588.firstPacket, Rolling1588.firstCore,
    rename_gateSlots, gateSlots_append]
  cases divide
  · have pOdd := paddedD_odd_slots
    simp only [firstBodyShortOdd, firstJointBackOdd,
      Rolling1588.firstBodyShort, Rolling1588.firstJointBack,
      Bool.false_eq_true, if_false, gateSlots_append] at g1 g2 ⊢
    omega
  · have pOdd := paddedGD_odd_slots
    simp only [firstBodyShortOdd, firstCellsJFrontOdd, firstRestZFrontOdd,
      Rolling1588.firstBodyShort, Rolling1588.firstCellsJFront, Rolling1588.firstRestZFront,
      if_true, gateSlots_append] at g1 g2 ⊢
    omega

private theorem rebindMany_slots_eq (roles hosts : List Wire) (P : Program) :
    gateSlots (StairLoan.rebindMany roles hosts P) = gateSlots P := by
  induction roles generalizing hosts with
  | nil => rfl
  | cons r roles ih =>
    cases hosts with
    | nil => rfl
    | cons h hosts =>
      simp only [StairLoan.rebindMany, rename_gateSlots, ih]

/-- Exact `gateSlots` preservation under `rebindMany` hosting. -/
theorem hostedFirstPacketOdd_slots (half : Bool → Program) (divide : Bool) :
    gateSlots (hostedFirstPacketOdd half divide) = gateSlots (placedFirstPacketOdd half divide) :=
  rebindMany_slots_eq _ _ _

/-- Exact `gateSlots` relation between `placedFirstPacketOdd` and `Rolling1588.placedFirstPacket`. -/
theorem placedFirstPacketOdd_slots_rel (half : Bool → Program) (divide : Bool) :
    gateSlots (placedFirstPacketOdd half divide) +
      3 * gateSlots (R2Life760.half760 divide) +
      gateSlots (if divide then JointForward1588.paddedGD else JointInverse1588.paddedD) =
      gateSlots (Rolling1588.placedFirstPacket divide) +
      3 * gateSlots (half divide) +
      gateSlots (if divide then paddedGD_odd else paddedD_odd) := by
  have c2 := cellOdd_slots divide (half divide) 2 4
  have c3 := cellOdd_slots divide (half divide) 3 2
  have c4 := cellOdd_slots divide (half divide) 4 2
  have oldCell (a h : Nat) :
      gateSlots (Rolling1588.cell divide 0 a h) = gateSlots (R2Life760.half760 divide) + 776 := by
    have hs := cellOdd_slots divide (R2Life760.half760 divide) a h
    have eq : Rolling1588.cell divide 0 a h = cellOdd divide (R2Life760.half760 divide) a h := by
      cases divide <;> rfl
    rw [eq, hs]
  have r2 := oldCell 2 4
  have r3 := oldCell 3 2
  have r4 := oldCell 4 2
  have g1 := G0CarryLoan5.slots (base 1028) (base 0) (base 768) (firstBodyShortOdd half divide)
  have g2 := G0CarryLoan5.slots (base 1028) (base 0) (base 768) (Rolling1588.firstBodyShort divide)
  simp only [placedFirstPacketOdd, firstPacketOdd, firstCoreOdd,
    Rolling1588.placedFirstPacket, Rolling1588.firstPacket, Rolling1588.firstCore,
    rename_gateSlots, gateSlots_append]
  cases divide
  · simp only [firstBodyShortOdd, firstJointBackOdd,
      Rolling1588.firstBodyShort, Rolling1588.firstJointBack,
      Bool.false_eq_true, if_false, gateSlots_append] at g1 g2 ⊢
    omega
  · simp only [firstBodyShortOdd, firstCellsJFrontOdd, firstRestZFrontOdd,
      Rolling1588.firstBodyShort, Rolling1588.firstCellsJFront, Rolling1588.firstRestZFront,
      if_true, gateSlots_append] at g1 g2 ⊢
    omega

/-- Exact `gateSlots` relation for `hostedFirstPacketOdd` against `StairFirstPacketHosted.hostedFirstPacket`. -/
theorem hostedFirstPacketOdd_slots_rel (half : Bool → Program) (divide : Bool) :
    gateSlots (hostedFirstPacketOdd half divide) +
      3 * gateSlots (R2Life760.half760 divide) +
      gateSlots (if divide then JointForward1588.paddedGD else JointInverse1588.paddedD) =
      gateSlots (StairFirstPacketHosted.hostedFirstPacket divide) +
      3 * gateSlots (half divide) +
      gateSlots (if divide then paddedGD_odd else paddedD_odd) := by
  rw [hostedFirstPacketOdd_slots, StairFirstPacketHosted.hostedFirstPacket, rebindMany_slots_eq]
  exact placedFirstPacketOdd_slots_rel half divide

end ECDSAAdd.Entrant.JointOdd1588
end


-- ============================================================================
-- Section 4B: End-to-end semantics for `firstPacketOdd`, `placedFirstPacketOdd`,
--             and `hostedFirstPacketOdd`
-- ============================================================================
section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.JointOdd1588
open ECDSAAdd Arithmetic Challenge Baselines BalancedCircuit BalancedField Secp256k1 RecordedQuantum
open MappedCompressed OffsetBorrowedCanonical CompressedFieldSupport DirectSkywalk
open Rolling1588 Rolling1588Lifetime
open StairWireCheck StairFirstPacketKernel StairFirstPacketHosted

attribute [local irreducible] run wires measurementCount toffoliCount gateSlots paddedGD_odd paddedD_odd firstBodyModelOdd

abbrev fieldR : List Wire := (balancedSharedPorts base (base 2409)).r
abbrev fieldY : List Wire := (balancedSharedPorts base (base 2409)).y

/-- Encoded frame parametrized by separate word encodings for `R` and `Y`.
Definitionally equal to `RouteA.Rolling1588.CodeFrame`. -/
def CodeFrameOdd (wordR wordY : Fp → Nat) (E : Program) (origin : BasisState)
    (X Y : Fp) (state : State) : Prop :=
  ∃ raw : State, raw.phase = state.phase ∧
    PairFrame fieldR fieldY origin (wordR X) (wordY Y) raw.basis ∧
    state = run E [] raw

/-- Cut frame parametrized by separate word encodings for `R` and `Y`.
Definitionally equal to `RouteA.Rolling1588.CutFrame`. -/
def CutFrameOdd (wordR wordY : Fp → Nat) (cut : Nat) (origin : BasisState)
    (X Y : Fp) (state : State) : Prop :=
  CodeFrameOdd wordR wordY (allEncodeCut base cut 102) origin X Y state

/-- Field frame before `OB5.sig 511` parametrized by separate word encodings for `R` and `Y`. -/
def EncodedFieldFrame5Odd (wordR wordY : Fp → Nat) (isA : Bool) (origin : BasisState)
    (X Y : Fp) (state : State) : Prop :=
  ∃ raw : State, raw.phase = state.phase ∧
    PairFrame fieldR fieldY origin (wordR X) (wordY Y) raw.basis ∧
    state = run (allEncode base isA 102) [] raw

/-- Placed field frame (after `OB5.sig 511`) parametrized by separate word encodings for `R` and `Y`. -/
def EncodedFieldFrameOdd (wordR wordY : Fp → Nat) (isA : Bool) (origin : BasisState)
    (X Y : Fp) (state : State) : Prop :=
  EncodedFieldFrame5Odd wordR wordY isA origin X Y (pullState (OB5.sig 511) state)

/-- The `Y`-register encoding at the entry of `firstPacketOdd` (`centerWord` on `Y = 0` for `divide = true`,
`oddWord` for `divide = false`). -/
def firstYIn (divide : Bool) : Fp → Nat := if divide then centerWord else oddWord

/-- The `Y`-register encoding at the exit of `firstPacketOdd` (`oddWord` for `divide = true`,
`centerWord` on `Y = 0` for `divide = false`). -/
def firstYOut (divide : Bool) : Fp → Nat := if divide then oddWord else centerWord

private theorem codeFrameOdd_arith (wordR wordY outR outY : Fp → Nat) (E : Program)
    (origin : BasisState) (X Y A B : Fp) (before after : State)
    (neutral : MeasuredCodec5.zeroNeutral E = true)
    (disjoint : Disjoint (wires E) (fieldR ++ fieldY).toFinset)
    (input : CodeFrameOdd wordR wordY E origin X Y before) (phase : after.phase = before.phase)
    (step : PairFrame fieldR fieldY before.basis (outR A) (outY B) after.basis) :
    CodeFrameOdd outR outY E origin A B after := by
  obtain ⟨raw, rawPhase, rawFrame, encoded⟩ := input
  let rawOut : State := ⟨after.phase, fun q =>
    if q ∈ fieldR ∨ q ∈ fieldY then after.basis q else raw.basis q⟩
  have away (q : Wire) (used : q ∈ wires E) : q ∉ fieldR ∧ q ∉ fieldY := by
    constructor <;> intro member
    · exact Finset.disjoint_left.mp disjoint used
        (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl member)))
    · exact Finset.disjoint_left.mp disjoint used
        (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inr member)))
  have rawOutFrame : PairFrame fieldR fieldY origin (outR A) (outY B) rawOut.basis := by
    refine ⟨?_, ?_, ?_⟩
    · exact (regValue_congr fieldR _ _ (fun q hq => by simp only [rawOut, if_pos (Or.inl hq)])).trans step.1
    · exact (regValue_congr fieldY _ _ (fun q hq => by simp only [rawOut, if_pos (Or.inr hq)])).trans step.2.1
    · intro q qr qy
      simpa only [rawOut, if_neg (not_or.mpr ⟨qr, qy⟩)] using rawFrame.2.2 q qr qy
  have localRun := run_measured_locality E (wires E) (Finset.Subset.refl _)
    rawOut raw [] (phase.trans rawPhase.symm) (fun q used => by
      have off := away q used
      simp only [rawOut, if_neg (not_or.mpr off)])
  have actual : run E [] rawOut = after := by
    apply State.extensionality
    · exact MeasuredCodec5.zero_phase E neutral rawOut
    · funext q
      by_cases used : q ∈ wires E
      · have off := away q used
        exact (localRun.2 q used).trans
          ((congrArg (fun state : State => state.basis q) encoded.symm).trans
            (step.2.2 q off.1 off.2).symm)
      · rw [run_preserves_outside E [] rawOut q used]
        by_cases arithmetic : q ∈ fieldR ∨ q ∈ fieldY
        · simp only [rawOut, if_pos arithmetic]
        · have off := not_or.mp arithmetic
          simp only [rawOut, if_neg arithmetic]
          exact ((step.2.2 q off.1 off.2).trans
            ((congrArg (fun state : State => state.basis q) encoded).trans
              (run_preserves_outside E [] raw q used))).symm
  exact ⟨rawOut, rfl, rawOutFrame, actual.symm⟩

private theorem oddHalfSupport_away (P : Program) (hsup : OddHalfSupport P) (i : Nat)
    (hi : i < 512 ∨ (1028 ≤ i ∧ i < 1538) ∨ i = 2400) : base i ∉ wires P := by
  intro used
  have hm := (hsup (base i) used).1
  simp only [LT48T.env, List.mem_cons, List.mem_map, Q6EndpointCell.ids, List.mem_append,
    List.mem_range'_1, List.not_mem_nil, or_false, base_injective.eq_iff] at hm
  rcases hm with rfl | ⟨j, hj, rfl⟩
  · omega
  · cases_type* Or
    all_goals omega

private theorem oddHalfSupport_readSites (P : Program) (hsup : OddHalfSupport P) :
    wires P ⊆ FrontierReplay1591.readSites 0 := fun q hq =>
  Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr (hsup q hq).1))

private theorem numeric_away_odd (q : Nat) (hr : q < 2056 ∨ 2312 ≤ q) (hy : q < 770 ∨ 1026 ≤ q) :
    base q ∉ fieldR ∧ base q ∉ fieldY := by
  rw [fieldR, fieldY, balancedSharedPorts_r, balancedSharedPorts_y]
  exact ⟨OwnPlusHost.not_block q 2056 256 (by omega), OwnPlusHost.not_block q 770 256 (by omega)⟩

private theorem pair_compose_odd (a b : BasisState) (x y u v : Nat) (c : BasisState)
    (before : PairFrame fieldR fieldY a x y b) (after : PairFrame fieldR fieldY b u v c) :
    PairFrame fieldR fieldY a u v c :=
  ⟨after.1, after.2.1, fun q qr qy => (after.2.2 q qr qy).trans (before.2.2 q qr qy)⟩

private theorem pair_numeric_odd (a b : BasisState) (x y : Nat) (h : PairFrame fieldR fieldY a x y b)
    (q : Nat) (hr : q < 2056 ∨ 2312 ≤ q) (hy : q < 770 ∨ 1026 ≤ q) : b (base q) = a (base q) :=
  h.2.2 _ (numeric_away_odd q hr hy).1 (numeric_away_odd q hr hy).2

private theorem selected_swap_odd (word : Fp → Nat) (active : Nat) (ha : active < 5)
    (X Y : Fp) (state : State) (records : List Bool)
    (enabled : state.basis (base 2400) = true) (flagIn : state.basis (base 2409) = false)
    (rValue : regValue fieldR state.basis = word X) (yValue : regValue fieldY state.basis = word Y) :
    (run (SW.selW (s 0 active) (base 2409) FrontierSW1591.swapBody) records state).phase = state.phase ∧
    PairFrame fieldR fieldY state.basis
      (word (if state.basis (s 0 active) then Y else X))
      (word (if state.basis (s 0 active) then X else Y))
      (run (SW.selW (s 0 active) (base 2409) FrontierSW1591.swapBody) records state).basis := by
  let origin := mixedTranscriptBase state.basis (base 2400) (s 0 active) (base 2409) false
  let L := Q6EndpointCell.ports base (base 2409)
  have len := BalancedCleanup.widths L.toLayout (Q6EndpointCell.ports_widths base (base 2409))
  have body := OneFlagCell.swap_frame L.r L.y (base 2409)
    (len.2.1.trans len.2.2.1.symm) FrontierReplay1591.base_sign_nd origin (word X) (word Y)
  have flagval : origin (base 2409) = mixedTranscriptBit state.basis (base 2400) (s 0 active) false := by
    simp only [origin, mixedTranscriptBase, writeBit, Function.update_self]
  rw [flagval] at body
  have hctrls : [base 2400, s 0 active, base 2409].Nodup := by
    have a : base 2400 ≠ s 0 active := HostOB5.host_ne _ _ (by omega)
    have b : base 2400 ≠ base 2409 := by decide
    have c : s 0 active ≠ base 2409 := HostOB5.host_ne _ _ (by omega)
    simp [List.nodup_cons, a, b, c]
  have proof := transcriptSelectWindow_pairFrame (base 2400) (s 0 active) (base 2409) false L.r L.y
    hctrls
    (by simpa only [L, Q6EndpointCell.ports_r, Q6EndpointCell.ports_y] using numeric_away_odd 2400 (by omega) (by omega))
    (by simpa only [L, Q6EndpointCell.ports_r, Q6EndpointCell.ports_y] using numeric_away_odd (1028 + active) (by omega) (by omega))
    (by simpa only [L, Q6EndpointCell.ports_r, Q6EndpointCell.ports_y] using numeric_away_odd 2409 (by omega) (by omega))
    state.basis flagIn _ _ _ _ _ body
  have selected := (SW.Sel.refl (base 2400) FrontierSW1591.swapBody
    FrontierSW1591.selSwap_away).window (s 0 active) (base 2409) false hctrls
  rw [(selected.eq records state enabled).1]
  have result := proof state records ⟨rValue, yValue, fun _ _ _ => rfl⟩
  cases e : state.basis (s 0 active) <;>
    simpa only [L, FrontierSW1591.swapBody, Q6EndpointCell.ports_r, Q6EndpointCell.ports_y,
      mixedTranscriptBit, enabled, e, if_true, Bool.false_eq_true, if_false] using result

private theorem halfWindowOdd_frame (P : Program) (divide : Bool)
    (law : OddHalfLaw P divide) (hsup : OddHalfSupport P)
    (active hole : Nat) (ha : active < 5) (hh : hole < 5) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (enabled : state.basis (base 2400) = true) (flagIn : state.basis (base 2409) = false)
    (rValue : regValue fieldR state.basis = oddWord X) (yValue : regValue fieldY state.basis = oddWord Y)
    (holeIn : state.basis (s 0 hole) = false) :
    (run (halfWindowOdd P active hole) records state).phase = state.phase ∧
    PairFrame fieldR fieldY state.basis
      (oddWord (if divide then (X + (if state.basis (g 0 active) then Y else -Y)) / 2
        else 2 * X + (if state.basis (g 0 active) then -Y else Y))) (oddWord Y)
      (run (halfWindowOdd P active hole) records state).basis := by
  let copied := run [.CX (g 0 active) (base 2409)] [] state
  let rebound := renameProgram (Equiv.swap (base 719) (s 0 hole)) P
  have holeFlag : s 0 hole ≠ base 2409 := HostOB5.host_ne _ _ (by omega)
  have holeFree : s 0 hole ∉ wires P := oddHalfSupport_away P hsup (1028 + hole) (Or.inr (Or.inl (by omega)))
  have copiedHole : copied.basis (s 0 hole) = false := by
    have hcx : copied = ⟨state.phase, writeBit state.basis (base 2409)
        (xor (state.basis (base 2409)) (state.basis (g 0 active)))⟩ := by simp [copied, run]
    rw [hcx]; simp only [writeBit, Function.update_of_ne holeFlag, holeIn]
  have copiedClean := copied_work_clean (g 0 active) state clean
  have copiedFrame := copied_self_frame (g 0 active) state (oddWord X) (oddWord Y) rValue yValue
  have member719 : base 719 ∈ Q6EndpointCell.workIds.map base :=
    List.mem_map.mpr ⟨719, by simp [Q6EndpointCell.workIds, List.mem_range'_1], rfl⟩
  have away719 := half_work_away _ member719
  have bodyEq : ∀ m, run rebound m copied = run P m copied := by
    intro m
    have result := law copied.basis copiedClean X Y copied m copiedFrame
    have after : (run P m copied).basis (base 719) = false :=
      (result.2.2.2 _ (by simpa only [Q6EndpointCell.ports_r] using away719.1)
        (by simpa only [Q6EndpointCell.ports_y] using away719.2)).trans (copiedClean _ member719)
    exact NewFieldFrameOB5.rebind_swap_run _ _ _ copied m (copiedClean _ member719) copiedHole after
      ((run_preserves_outside _ m copied _ holeFree).trans copiedHole)
  have oldResult := law copied.basis copiedClean X Y copied records copiedFrame
  have carryMember : packetCarry 0 ∈ Q6EndpointCell.workIds.map base :=
    List.mem_map.mpr ⟨516, by simp [Q6EndpointCell.workIds, List.mem_range'_1], rfl⟩
  have carryAway := half_work_away _ carryMember
  have keep : (run rebound records copied).basis (base 2409) = copied.basis (base 2409) := by
    rw [bodyEq]
    exact oldResult.2.2.2 _
      (by simpa only [Q6EndpointCell.ports_r] using half_flag_away.1)
      (by simpa only [Q6EndpointCell.ports_y] using half_flag_away.2)
  have carryOut : (run rebound records copied).basis (packetCarry 0) = false := by
    rw [bodyEq]
    exact (oldResult.2.2.2 _
      (by simpa only [Q6EndpointCell.ports_r] using carryAway.1)
      (by simpa only [Q6EndpointCell.ports_y] using carryAway.2)).trans (copiedClean _ carryMember)
  have activeFree : g 0 active ∉ wires rebound := by
    rw [renameProgram_support]
    intro used
    obtain ⟨q, hq, eq⟩ := Finset.mem_image.mp used
    have fix : Equiv.swap (base 719) (s 0 hole) (g 0 active) = g 0 active :=
      Equiv.swap_apply_of_ne_of_ne (HostOB5.host_ne _ _ (by omega)) (HostOB5.host_ne _ _ (by omega))
    have same := (Equiv.swap (base 719) (s 0 hole)).injective (eq.trans fix.symm)
    have hga : g 0 active = base active := by simp [g]
    exact oddHalfSupport_away P hsup active (Or.inl (by omega)) (hga ▸ same ▸ hq)
  have loan := ControlLoan1589.loanWindow_eq (g 0 active) (base 2409) (packetCarry 0)
    rebound state records (HostOB5.host_ne _ _ (by omega)) (HostOB5.host_ne _ _ (by omega))
    (HostOB5.host_ne _ _ (by omega)) activeFree flagIn (clean _ carryMember) keep carryOut
  have hselEq : run (halfWindowOdd P active hole) records state =
      run (SW.selW (g 0 active) (base 2409) P) records state := by
    rw [halfWindowOdd, loan]
    have headCount : measurementCount [.CX (g 0 active) (base 2409)] = 0 := by
      simp only [measurementCount]
    simp only [SW.selW, List.append_assoc, run_append, headCount, List.take_zero,
      List.drop_zero, run_take]
    rw [(renameProgram_counts (Equiv.swap (base 719) (s 0 hole)) P).2, bodyEq records]
  rw [hselEq]
  have controls : [base 2400, g 0 active, base 2409].Nodup := by
    have a : base 2400 ≠ g 0 active := HostOB5.host_ne _ _ (by omega)
    have b : base 2400 ≠ base 2409 := by decide
    have c : g 0 active ≠ base 2409 := HostOB5.host_ne _ _ (by omega)
    simp [List.nodup_cons, a, b, c]
  let origin := mixedTranscriptBase state.basis (base 2400) (g 0 active) (base 2409) false
  have flagNotWork : base 2409 ∉ Q6EndpointCell.workIds.map base := by
    intro used
    obtain ⟨i, hi, eq⟩ := List.mem_map.mp used
    have := base_injective eq
    have := Q6EndpointCell.work_bound i hi
    omega
  have cl : Q6EndpointCell.Clean base origin := by
    intro q hq
    have ne : q ≠ base 2409 := fun e => flagNotWork (e ▸ hq)
    simpa only [origin, mixedTranscriptBase, writeBit, Function.update_of_ne ne] using clean q hq
  have body := law origin cl X Y
  simp only [origin, mixedTranscriptBase, writeBit, Function.update_self] at body
  have proof := transcriptSelectWindow_pairFrame (base 2400) (g 0 active) (base 2409) false
    (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y
    controls
    (by simpa only [Q6EndpointCell.ports_r, Q6EndpointCell.ports_y] using numeric_away_odd 2400 (by omega) (by omega))
    (by simpa only [g, Nat.mul_zero, Nat.zero_add, Q6EndpointCell.ports_r, Q6EndpointCell.ports_y] using numeric_away_odd active (by omega) (by omega))
    (by simpa only [Q6EndpointCell.ports_r, Q6EndpointCell.ports_y] using numeric_away_odd 2409 (by omega) (by omega))
    state.basis flagIn _ _ _ _ P body
  have selected := (SW.Sel.refl (base 2400) P
    (oddHalfSupport_away P hsup 2400 (Or.inr (Or.inr rfl)))).window (g 0 active) (base 2409) false controls
  rw [(selected.eq records state enabled).1]
  simpa only [Q6EndpointCell.ports_r, Q6EndpointCell.ports_y, mixedTranscriptBit, enabled, if_true]
    using proof state records ⟨rValue, yValue, fun _ _ _ => rfl⟩

private theorem cellOdd_frame (P : Program) (divide : Bool)
    (law : OddHalfLaw P divide) (hsup : OddHalfSupport P)
    (active hole : Nat) (ha : active < 5) (hh : hole < 5) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (enabled : state.basis (base 2400) = true) (flagIn : state.basis (base 2409) = false)
    (rValue : regValue fieldR state.basis = oddWord X) (yValue : regValue fieldY state.basis = oddWord Y)
    (holeIn : state.basis (s 0 hole) = false) :
    (run (cellOdd divide P active hole) records state).phase = state.phase ∧
    PairFrame fieldR fieldY state.basis
      (oddWord (Q6EndpointCell.payload divide (state.basis (g 0 active)) (state.basis (s 0 active)) (X, Y)).1)
      (oddWord (Q6EndpointCell.payload divide (state.basis (g 0 active)) (state.basis (s 0 active)) (X, Y)).2)
      (run (cellOdd divide P active hole) records state).basis := by
  have cleanOf (a b : BasisState) (x y : Nat) (h : PairFrame fieldR fieldY a x y b)
      (cl : Q6EndpointCell.Clean base a) : Q6EndpointCell.Clean base b := fun q used => by
    have off := half_work_away q used
    exact (h.2.2 q off.1 off.2).trans (cl q used)
  cases divide
  · let head := SW.selW (s 0 active) (base 2409) FrontierSW1591.swapBody
    let before := run head (records.take (measurementCount head)) state
    let A : Fp := if state.basis (s 0 active) then Y else X
    let B : Fp := if state.basis (s 0 active) then X else Y
    have swapped := selected_swap_odd oddWord active ha X Y state
      (records.take (measurementCount head)) enabled flagIn rValue yValue
    have same (q : Nat) (hr : q < 2056 ∨ 2312 ≤ q) (hy : q < 770 ∨ 1026 ≤ q) :=
      pair_numeric_odd _ _ _ _ swapped.2 q hr hy
    have result := halfWindowOdd_frame P false law hsup active hole ha hh A B before
      (records.drop (measurementCount head)) (cleanOf _ _ _ _ swapped.2 clean)
      ((same 2400 (by omega) (by omega)).trans enabled)
      ((same 2409 (by omega) (by omega)).trans flagIn) swapped.2.1 swapped.2.2.1
      ((same (1028 + hole) (by omega) (by omega)).trans holeIn)
    have composed := pair_compose_odd _ _ _ _ _ _ _ swapped.2 result.2
    have gSame : before.basis (g 0 active) = state.basis (g 0 active) := by
      simpa only [g, Nat.mul_zero, Nat.zero_add] using same active (by omega) (by omega)
    simp only [cellOdd, Bool.false_eq_true, if_false, run_append]
    refine ⟨result.1.trans swapped.1, ?_⟩
    cases e : state.basis (s 0 active) <;>
      simpa only [Q6EndpointCell.payload, skywalkPayloadUncell, Bool.false_eq_true, if_false,
        if_true, A, B, gSame, e] using composed
  · let head := halfWindowOdd P active hole
    let before := run head (records.take (measurementCount head)) state
    let A : Fp := (X + (if state.basis (g 0 active) then Y else -Y)) / 2
    have first := halfWindowOdd_frame P true law hsup active hole ha hh X Y state
      (records.take (measurementCount head)) clean enabled flagIn rValue yValue holeIn
    have same (q : Nat) (hr : q < 2056 ∨ 2312 ≤ q) (hy : q < 770 ∨ 1026 ≤ q) :=
      pair_numeric_odd _ _ _ _ first.2 q hr hy
    have result := selected_swap_odd oddWord active ha A Y before
      (records.drop (measurementCount head))
      ((same 2400 (by omega) (by omega)).trans enabled)
      ((same 2409 (by omega) (by omega)).trans flagIn) first.2.1 first.2.2.1
    have composed := pair_compose_odd _ _ _ _ _ _ _ first.2 result.2
    have sSame : before.basis (s 0 active) = state.basis (s 0 active) := same (1028 + active) (by omega) (by omega)
    rw [cellOdd, if_pos rfl, run_append]
    refine ⟨result.1.trans first.1, ?_⟩
    cases e : state.basis (s 0 active) <;>
      simpa only [Q6EndpointCell.payload, skywalkPayloadCell, if_true, A, sSame, e,
        Bool.false_eq_true, if_false] using composed

/-! ### Stage framing for packet 0 (`Rolling1588First` stages with odd words) -/

private abbrev packetMap0 : Fin 10 → Wire := History5.historyMap base 0

private theorem packetMap0_inj : Function.Injective packetMap0 :=
  History5.historyMap_injective base base_pool_nodup 0 (by decide)

private theorem label0_even (k : Nat) (hk : k < 5) :
    MeasuredCodec5.label packetMap0 (2 * k) = g 0 k := by
  have bound : 2 * k < 10 := by omega
  have even : (2 * k) % 2 = 0 := by omega
  have half : (2 * k) / 2 = k := by omega
  simp only [MeasuredCodec5.label, dif_pos bound, packetMap0, History5.historyMap,
    History5.historyId, even, if_pos rfl, if_true, half, g, Nat.mul_zero, Nat.zero_add]

private theorem label0_odd (k : Nat) (hk : k < 5) :
    MeasuredCodec5.label packetMap0 (2 * k + 1) = s 0 k := by
  have bound : 2 * k + 1 < 10 := by omega
  have odd : (2 * k + 1) % 2 = 1 := by omega
  have half : (2 * k + 1) / 2 = k := by omega
  simp only [MeasuredCodec5.label, dif_pos bound, packetMap0, History5.historyMap,
    History5.historyId, odd, if_neg (by decide : ¬(1 : Nat) = 0), half, s, Nat.mul_zero, Nat.add_zero]

private theorem onPacket0_support (P : Program) (support : wires P ⊆ Finset.range 10) :
    wires (onPacket 0 P) ⊆ wires (NewHistory5.encode base 0) := by
  simp only [onPacket, Nat.mul_zero, NewHistory5.encode, ParityCodec5New.encodeAt,
    ParityCodec5New.label, renameProgram_support, ParityCodec5New.support_exact.1]
  exact Finset.image_mono _ support

private theorem history0_index (q : Wire) (used : q ∈ wires (NewHistory5.encode base 0)) :
    ∃ i : Nat, q = base i ∧ (i < 5 ∨ (1028 ≤ i ∧ i < 1033)) := by
  obtain ⟨port, eq⟩ := NewHistory5.history_gate_mem base 0 _ (Or.inl rfl) q used
  refine ⟨History5.historyId 0 port, eq, ?_⟩
  have bound := port.isLt
  unfold History5.historyId
  split_ifs <;> omega

private theorem codec0_not (q : Nat) (lo : 5 ≤ q) (away : q < 1028 ∨ 1033 ≤ q) :
    base q ∉ wires (NewHistory5.encode base 0) := by
  intro used
  obtain ⟨i, eq, bounds⟩ := history0_index _ used
  have := base_injective eq
  omega

private theorem codec0_disjoint (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (P : Program) (support : wires P ⊆ wires (NewHistory5.encode base 0)) :
    Disjoint (wires P) (fieldR ++ fieldY).toFinset := by
  apply Finset.disjoint_left.mpr
  intro q used member
  obtain ⟨port, eq⟩ := NewHistory5.history_gate_mem base 0 _ (Or.inl rfl) q (support used)
  have away := NewHistory5.history_words_away base (base 2409) ctx.hn (ctx.hp _ (by simp)) 0 (by decide) port
  rw [eq] at member
  exact (List.mem_append.mp (List.mem_toFinset.mp member)).elim away.1 away.2

private theorem raw0_legal (wordR wordY : Fp → Nat) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X Y : Fp) (raw : State)
    (frame : PairFrame fieldR fieldY origin (wordR X) (wordY Y) raw.basis) :
    MeasuredCodec5.legalAt packetMap0 raw.basis :=
  (NewHistory5.frame_history_legal base (base 2409) ctx.hn (ctx.hp _ (by simp))
    102 (by decide) origin raw.basis _ _ ctx.legal frame) 0 (by decide)

private theorem stageAt0_neutral (divide : Bool) (k : Nat) (hk : k ≤ 4) :
    MeasuredCodec5.zeroNeutral (Rolling1588First.stageAt divide k) = true := by
  rw [Rolling1588First.stageAt, onPacket, Rolling1588First.zeroNeutral_rename]
  exact Rolling1588First.stage_neutral divide k hk

private theorem stageAt0_correct (divide : Bool) (k : Nat) (hk : k < 4)
    (raw : State) (records : List Bool) (legal : MeasuredCodec5.legalAt packetMap0 raw.basis) :
    (run (Rolling1588First.stageAt divide k) records raw).phase = raw.phase ∧
    (run (Rolling1588First.stageAt divide k) records raw).basis (s 0 (Rolling1588First.hole divide k)) = false ∧
    (run (Rolling1588First.stageAt divide k) records raw).basis (g 0 (Rolling1588First.active divide k)) =
      raw.basis (g 0 (Rolling1588First.active divide k)) ∧
    (run (Rolling1588First.stageAt divide k) records raw).basis (s 0 (Rolling1588First.active divide k)) =
      raw.basis (s 0 (Rolling1588First.active divide k)) := by
  let localState : State := ⟨raw.phase, fun q => raw.basis (MeasuredCodec5.label packetMap0 q)⟩
  have result := Rolling1588First.stage_correct divide k hk localState records legal
  have mapped := run_rename_pool (MeasuredCodec5.label packetMap0) (Finset.range 10)
    (FirstNonzeroCodec.label_inj' packetMap0 packetMap0_inj) (Rolling1588First.stageCode divide k)
    (Rolling1588First.stage_support divide k (by omega)) records localState raw rfl (fun _ _ => rfl)
  have bounds := Rolling1588First.indices divide k hk
  refine ⟨mapped.1.trans result.1, ?_, ?_, ?_⟩
  · simpa only [Rolling1588First.stageAt, onPacket, Nat.mul_zero, label0_odd _ bounds.2.2] using
      (mapped.2 (2 * Rolling1588First.hole divide k + 1) (Finset.mem_range.mpr (by omega))).trans result.2.1
  · simpa only [Rolling1588First.stageAt, onPacket, Nat.mul_zero, label0_even _ bounds.2.1, localState] using
      (mapped.2 (2 * Rolling1588First.active divide k) (Finset.mem_range.mpr (by omega))).trans result.2.2.1
  · simpa only [Rolling1588First.stageAt, onPacket, Nat.mul_zero, label0_odd _ bounds.2.1, localState] using
      (mapped.2 (2 * Rolling1588First.active divide k + 1) (Finset.mem_range.mpr (by omega))).trans result.2.2.2

private theorem stage0_read (wordR wordY : Fp → Nat) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (divide : Bool) (k : Nat) (hk : k ≤ 4)
    (X Y : Fp) (state : State)
    (input : CodeFrameOdd wordR wordY (Rolling1588First.stageAt divide k) origin X Y state) :
    regValue fieldR state.basis = wordR X ∧ regValue fieldY state.basis = wordY Y ∧
    Q6EndpointCell.Clean base state.basis ∧ state.basis (base 2409) = false ∧
      state.basis (base 2400) = origin (base 2400) := by
  obtain ⟨raw, _, frame, encoded⟩ := input
  have support := onPacket0_support (Rolling1588First.stageCode divide k) (Rolling1588First.stage_support divide k hk)
  have disjoint := codec0_disjoint origin ctx _ support
  have fields (q : Wire) (used : q ∈ fieldR ∨ q ∈ fieldY) : state.basis q = raw.basis q := by
    rw [encoded]
    apply run_preserves_outside
    intro member
    exact Finset.disjoint_left.mp disjoint member (List.mem_toFinset.mpr (List.mem_append.mpr used))
  have work := Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity
  refine ⟨(regValue_congr fieldR _ _ (fun q hq => fields q (Or.inl hq))).trans frame.1,
    (regValue_congr fieldY _ _ (fun q hq => fields q (Or.inr hq))).trans frame.2.1, ?_, ?_, ?_⟩
  · intro q used
    have rawAway := half_work_away q used
    have rawZero := (frame.2.2 q rawAway.1 rawAway.2).trans (work q used)
    rw [encoded]
    apply Eq.trans (run_preserves_outside _ [] raw q ?_) rawZero
    intro member
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp used
    obtain ⟨j, eq, bounds⟩ := history0_index _ (support member)
    have same : i = j := base_injective eq
    simp only [Q6EndpointCell.workIds, List.mem_append, List.mem_cons, List.not_mem_nil,
      List.mem_range'_1, or_false] at hi
    omega
  · rw [encoded]
    exact (run_preserves_outside _ [] raw _ (fun h => codec0_not 2409 (by omega) (by omega) (support h))).trans
      ((frame.2.2 _ (numeric_away_odd 2409 (by omega) (by omega)).1
        (numeric_away_odd 2409 (by omega) (by omega)).2).trans ctx.hg0)
  · rw [encoded]
    exact (run_preserves_outside _ [] raw _ (fun h => codec0_not 2400 (by omega) (by omega) (support h))).trans
      (frame.2.2 _ (numeric_away_odd 2400 (by omega) (by omega)).1
        (numeric_away_odd 2400 (by omega) (by omega)).2)

private theorem opening0_frame (wordR wordY : Fp → Nat) (divide : Bool) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X Y : Fp) :
    StateTriple (fun state => PairFrame fieldR fieldY origin (wordR X) (wordY Y) state.basis)
      (Rolling1588First.stageAt divide 0)
      (CodeFrameOdd wordR wordY (Rolling1588First.stageAt divide 0) origin X Y) := by
  intro state records input
  have legal := raw0_legal wordR wordY origin ctx X Y state input
  have correct := stageAt0_correct divide 0 (by decide) state records legal
  have neut := stageAt0_neutral divide 0 (by decide)
  have same : run (Rolling1588First.stageAt divide 0) records state =
      run (Rolling1588First.stageAt divide 0) [] state := by
    let localState : State := ⟨state.phase, fun q => state.basis (MeasuredCodec5.label packetMap0 q)⟩
    have hm1 := run_rename_pool (MeasuredCodec5.label packetMap0) (Finset.range 10)
      (FirstNonzeroCodec.label_inj' packetMap0 packetMap0_inj) (Rolling1588First.stageCode divide 0)
      (Rolling1588First.stage_support divide 0 (by decide)) records localState state rfl (fun _ _ => rfl)
    have hm2 := run_rename_pool (MeasuredCodec5.label packetMap0) (Finset.range 10)
      (FirstNonzeroCodec.label_inj' packetMap0 packetMap0_inj) (Rolling1588First.stageCode divide 0)
      (Rolling1588First.stage_support divide 0 (by decide)) [] localState state rfl (fun _ _ => rfl)
    have heq : run (Rolling1588First.stageCode divide 0) records localState =
        run (Rolling1588First.stageCode divide 0) [] localState := by
      obtain ⟨x, hx, lx, hb⟩ := MeasuredCodec5.local_word localState legal
      have a1 := pool_run_agrees (Rolling1588First.stageCode divide 0) (Finset.range 10)
        (Rolling1588First.stage_support divide 0 (by decide)) records localState ⟨localState.phase, MeasuredCodec5.bitsOf x⟩ rfl hb
      have a2 := pool_run_agrees (Rolling1588First.stageCode divide 0) (Finset.range 10)
        (Rolling1588First.stage_support divide 0 (by decide)) [] localState ⟨localState.phase, MeasuredCodec5.bitsOf x⟩ rfl hb
      have fin := (Rolling1588First.finite_stage divide 0 (by decide) x hx lx).1
      have m1 := MeasuredCodec5.run_sim (Rolling1588First.stageCode divide 0) records localState.phase x
      have m2 := MeasuredCodec5.run_sim (Rolling1588First.stageCode divide 0) [] localState.phase x
      rw [MeasuredCodec5.sim_safe _ x fin] at m1 m2
      apply State.extensionality
      · exact a1.1.trans ((congrArg State.phase (m1.trans m2.symm)).trans a2.1.symm)
      · funext q
        by_cases hq : q ∈ Finset.range 10
        · exact (a1.2 q hq).trans ((congrArg (fun t : State => t.basis q) (m1.trans m2.symm)).trans (a2.2 q hq).symm)
        · exact (run_preserves_outside _ records localState q (fun h => hq (Rolling1588First.stage_support divide 0 (by decide) h))).trans
            (run_preserves_outside _ [] localState q (fun h => hq (Rolling1588First.stage_support divide 0 (by decide) h))).symm
    apply State.extensionality
    · exact hm1.1.trans ((congrArg State.phase heq).trans hm2.1.symm)
    · funext q
      by_cases used : q ∈ (Finset.range 10).image (MeasuredCodec5.label packetMap0)
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp used
        exact (hm1.2 i hi).trans ((congrArg (fun t : State => t.basis i) heq).trans (hm2.2 i hi).symm)
      · have off : q ∉ wires (Rolling1588First.stageAt divide 0) := by
          rw [Rolling1588First.stageAt, onPacket, renameProgram_support]
          intro mem; obtain ⟨i, hi, eq⟩ := Finset.mem_image.mp mem
          exact used (Finset.mem_image.mpr ⟨i, Rolling1588First.stage_support divide 0 (by decide) hi, eq⟩)
        exact (run_preserves_outside _ records state q off).trans (run_preserves_outside _ [] state q off).symm
  exact ⟨correct.1, state, correct.1.symm, input, same⟩

private theorem transition0_stage (wordR wordY : Fp → Nat) (divide : Bool) (k : Nat) (hk : k < 4)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (X Y : Fp) :
    StateTriple (CodeFrameOdd wordR wordY (Rolling1588First.stageAt divide k) origin X Y)
      (Rolling1588First.transitionAt divide k)
      (CodeFrameOdd wordR wordY (Rolling1588First.stageAt divide (k + 1)) origin X Y) := by
  intro state records input
  obtain ⟨raw, rawPhase, rawFrame, encoded⟩ := input
  have legal := raw0_legal wordR wordY origin ctx X Y raw rawFrame
  have same : run (Rolling1588First.transitionAt divide k) records state =
      run (Rolling1588First.stageAt divide (k + 1)) [] raw := by
    rw [encoded]
    exact mapped_composition_eq packetMap0 packetMap0_inj
      (Rolling1588First.stageCode divide k) (Rolling1588First.transition divide k)
      (Rolling1588First.stageCode divide (k + 1))
      (Rolling1588First.stage_support divide k (by omega))
      (Rolling1588First.transition_support divide k hk)
      (Rolling1588First.stage_support divide (k + 1) (by omega))
      (fun st a b c h => Rolling1588First.transition_run divide k hk st a b c h) raw [] records [] legal
  have phase : (run (Rolling1588First.transitionAt divide k) records state).phase = state.phase := by
    rw [same]
    exact (MeasuredCodec5.zero_phase _ (stageAt0_neutral divide (k + 1) (by omega)) raw).trans rawPhase
  exact ⟨phase, raw, rawPhase.trans phase.symm, rawFrame, same⟩

private theorem cellOdd_stage (P : Program) (divide : Bool) (law : OddHalfLaw P divide)
    (hsup : OddHalfSupport P) (k : Nat) (hk : k < 4)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp) :
    StateTriple (CodeFrameOdd oddWord oddWord (Rolling1588First.stageAt divide k) origin X Y)
      (cellOdd divide P (Rolling1588First.active divide k) (Rolling1588First.hole divide k))
      (CodeFrameOdd oddWord oddWord (Rolling1588First.stageAt divide k) origin
        (Rolling1588First.payloadStep divide origin k (X, Y)).1
        (Rolling1588First.payloadStep divide origin k (X, Y)).2) := by
  intro state records input
  have oldInput := input
  obtain ⟨raw, _, rawFrame, encoded⟩ := input
  have legal := raw0_legal oddWord oddWord origin ctx X Y raw rawFrame
  have stage := stageAt0_correct divide k hk raw [] legal
  have bounds := Rolling1588First.indices divide k hk
  have reads := stage0_read oddWord oddWord origin ctx divide k (by omega) X Y state oldInput
  have control (a : Nat) (ha : a < 5) : raw.basis (g 0 a) = origin (g 0 a) ∧
      raw.basis (s 0 a) = origin (s 0 a) := by
    have basic : raw.basis (base a) = origin (base a) ∧
        raw.basis (base (1028 + a)) = origin (base (1028 + a)) :=
      ⟨rawFrame.2.2 _ (numeric_away_odd a (by omega) (by omega)).1 (numeric_away_odd a (by omega) (by omega)).2,
        rawFrame.2.2 _ (numeric_away_odd (1028 + a) (by omega) (by omega)).1 (numeric_away_odd (1028 + a) (by omega) (by omega)).2⟩
    simpa only [g, s, Nat.mul_zero, Nat.zero_add, Nat.add_zero] using basic
  have activeBits : state.basis (g 0 (Rolling1588First.active divide k)) = origin (g 0 (Rolling1588First.active divide k)) ∧
      state.basis (s 0 (Rolling1588First.active divide k)) = origin (s 0 (Rolling1588First.active divide k)) := by
    rw [encoded]
    exact ⟨stage.2.2.1.trans (control _ bounds.2.1).1, stage.2.2.2.trans (control _ bounds.2.1).2⟩
  have holeZero : state.basis (s 0 (Rolling1588First.hole divide k)) = false := by
    rw [encoded]; exact stage.2.1
  have result := cellOdd_frame P divide law hsup (Rolling1588First.active divide k)
    (Rolling1588First.hole divide k) bounds.2.1 bounds.2.2 X Y state records reads.2.2.1
    (reads.2.2.2.2.trans enabled) reads.2.2.2.1 reads.1 reads.2.1 holeZero
  have arithmetic : PairFrame fieldR fieldY state.basis
      (oddWord (Rolling1588First.payloadStep divide origin k (X, Y)).1)
      (oddWord (Rolling1588First.payloadStep divide origin k (X, Y)).2)
      (run (cellOdd divide P (Rolling1588First.active divide k) (Rolling1588First.hole divide k)) records state).basis := by
    simpa only [Rolling1588First.payloadStep, activeBits.1, activeBits.2] using result.2
  exact ⟨result.1, codeFrameOdd_arith oddWord oddWord oddWord oddWord _ origin X Y _ _ state _
    (stageAt0_neutral divide k (by omega))
    (codec0_disjoint origin ctx _ (onPacket0_support _ (Rolling1588First.stage_support divide k (by omega))))
    oldInput result.1 arithmetic⟩

private def segmentOdd (P : Program) (divide : Bool) (k : Nat) : Program :=
  cellOdd divide P (Rolling1588First.active divide k) (Rolling1588First.hole divide k) ++
    Rolling1588First.transitionAt divide k

private theorem segmentOdd_frame (P : Program) (divide : Bool) (law : OddHalfLaw P divide)
    (hsup : OddHalfSupport P) (k : Nat) (hk : k < 4)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (V : Fp × Fp) :
    StateTriple (CodeFrameOdd oddWord oddWord (Rolling1588First.stageAt divide k) origin V.1 V.2)
      (segmentOdd P divide k)
      (CodeFrameOdd oddWord oddWord (Rolling1588First.stageAt divide (k + 1)) origin
        (Rolling1588First.payloadStep divide origin k V).1
        (Rolling1588First.payloadStep divide origin k V).2) :=
  (cellOdd_stage P divide law hsup k hk origin ctx enabled V.1 V.2).seq
    (transition0_stage oddWord oddWord divide k hk origin ctx _ _)

private theorem seq_frame {α : Type} (P : Nat → Program)
    (F : Nat → α → State → Prop) (step : Nat → α → α) (N : Nat)
    (pkt : ∀ j, j < N → ∀ V, StateTriple (F j V) (P j) (F (j + 1) (step j V)))
    (j n : Nat) (bound : j + n ≤ N) (V : α) :
    StateTriple (F j V) (PacketSequence.program true P j n)
      (F (j + n) (PacketSequence.payload true step j n V)) := by
  induction n generalizing j V with
  | zero =>
    intro state records input
    simpa only [PacketSequence.program, PacketSequence.payload, Nat.add_zero, run] using
      And.intro (Eq.refl state.phase) input
  | succ n ih =>
    have first := pkt j (by omega) V
    have rest := ih (j + 1) (by omega) (step j V)
    have idx : j + (n + 1) = (j + 1) + n := by omega
    simpa only [PacketSequence.program, PacketSequence.payload, if_true, idx] using first.seq rest

private theorem triple0_map (a b c : Nat) (ha : a < 5) (hb : b < 5) (hc : c < 5) :
    MeasuredCodec5.label packetMap0 ∘ localTriple a b c = tripleMap a b c := by
  funext i
  let t := if i / 2 = 0 then a else if i / 2 = 1 then b else c
  have ht : t < 5 := by dsimp only [t]; split_ifs <;> assumption
  change MeasuredCodec5.label packetMap0 (2 * t + i % 2) = if i % 2 = 0 then g 0 t else s 0 t
  rcases Nat.mod_two_eq_zero_or_one i with eq | eq
  · simp only [eq, Nat.add_zero, if_pos rfl, if_true, label0_even t ht]
  · simp only [eq, if_neg (by decide : ¬(1 : Nat) = 0), label0_odd t ht]

private theorem onPacket0_triple (a b c : Nat) (ha : a < 5) (hb : b < 5) (hc : c < 5) (P : Program) :
    onPacket 0 (ECDSAAdd.Entrant.Rolling1588First.mappedTriple a b c P) = triple a b c P := by
  simp only [onPacket, ECDSAAdd.Entrant.Rolling1588First.mappedTriple, triple, Nat.mul_zero, renameProgram_comp]
  exact congrArg (fun f => renameProgram f P) (triple0_map a b c ha hb hc)

private theorem onPacket0_append (P Q : Program) :
    onPacket 0 (P ++ Q) = onPacket 0 P ++ onPacket 0 Q := by
  simp only [onPacket, renameProgram, List.map_append]

private theorem onPacket0_label_free (P : Program) (support : wires P ⊆ Finset.range 10)
    (i : Nat) (hi : i ∈ Finset.range 10) (off : i ∉ wires P) :
    MeasuredCodec5.label packetMap0 i ∉ wires (onPacket 0 P) := by
  intro used
  rw [onPacket, renameProgram_support] at used
  obtain ⟨k, hk, eq⟩ := Finset.mem_image.mp used
  have same : k = i := FirstNonzeroCodec.label_inj' packetMap0 packetMap0_inj k (support hk) i hi eq
  exact off (same ▸ hk)

private theorem payload0_eq_rest (divide : Bool) (origin : BasisState)
    (enabled : origin (base 2400) = true) (V : Fp × Fp) :
    PacketSequence.payload true (Rolling1588First.payloadStep divide origin) 0 4 V =
      directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) Replay5.restLetters) V := by
  have letters : Replay5.restLetters = [tapeLetter 1, tapeLetter 2, tapeLetter 3, tapeLetter 4] := rfl
  cases divide <;>
    simp only [PacketSequence.payload, Rolling1588First.payloadStep, Rolling1588First.active,
      Rolling1588First.stageIndex, Q6EndpointCell.payload, Bool.false_eq_true, if_false, if_true,
      Bool.not_false, Bool.not_true, letters, mixedTranscriptControls, List.map_cons, List.map_nil,
      tapeLetter, mixedTape_base_getD 1 (by decide), mixedTape_base_getD 2 (by decide),
      mixedTape_base_getD 3 (by decide), mixedTape_base_getD 4 (by decide),
      mixedTranscriptBit, enabled, g, s, Nat.mul_zero, Nat.zero_add, Nat.add_zero,
      directionalPayload, skywalkPayloadReplay, skywalkPayloadReplayInverse]

private theorem jointD_odd_stage (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X : Fp) :
    StateTriple (CodeFrameOdd oddWord centerWord (Rolling1588First.stageAt true 0) origin X 0)
      (paddedGD_odd ++ SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody)
      (CodeFrameOdd oddWord oddWord (Rolling1588First.stageAt true 0) origin
        (Rolling1588First.payloadStep true origin 0 (if origin (base 1028) then ((0 : Fp), X) else (X, 0))).1
        (Rolling1588First.payloadStep true origin 0 (if origin (base 1028) then ((0 : Fp), X) else (X, 0))).2) := by
  intro state records input
  have oldInput := input
  obtain ⟨raw, _, rawFrame, encoded⟩ := input
  have legal := raw0_legal oddWord centerWord origin ctx X 0 raw rawFrame
  have stage := stageAt0_correct true 0 (by decide) raw [] legal
  have reads := stage0_read oddWord centerWord origin ctx true 0 (by omega) X 0 state oldInput
  have rawAt (a : Nat) (h1 : a < 2056) (h2 : a < 770 ∨ 1026 ≤ a) : raw.basis (base a) = origin (base a) :=
    rawFrame.2.2 _ (numeric_away_odd a (Or.inl h1) h2).1 (numeric_away_odd a (Or.inl h1) h2).2
  have jState : state.basis (base 1028) = origin (base 1028) := by
    have off : base 1028 ∉ wires (Rolling1588First.stageAt true 0) := by
      have h1not : 1 ∉ wires (Rolling1588First.stageCode true 0) := by
        show 1 ∉ wires (renameProgram (localTriple 2 3 4) e3)
        rw [renameProgram_support]
        intro hm; obtain ⟨y, _, eq⟩ := Finset.mem_image.mp hm
        change (2 * (if y / 2 = 0 then 2 else if y / 2 = 1 then 3 else 4) + y % 2 : Nat) = 1 at eq
        split_ifs at eq <;> omega
      have h := onPacket0_label_free (Rolling1588First.stageCode true 0)
        (Rolling1588First.stage_support true 0 (by decide)) 1 (by decide) h1not
      have e : MeasuredCodec5.label packetMap0 1 = base 1028 := label0_odd 0 (by decide)
      rw [e] at h; exact h
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ off).trans (rawAt 1028 (by omega) (Or.inr (by omega)))
  have gState : state.basis (base 1) = origin (base 1) := by
    rw [encoded]; exact stage.2.2.1.trans (rawAt 1 (by omega) (Or.inl (by omega)))
  have sState : state.basis (s 0 1) = origin (s 0 1) := by
    rw [encoded]; exact stage.2.2.2.trans (rawAt 1029 (by omega) (Or.inr (by omega)))
  have holeState : state.basis (base 1032) = false := by rw [encoded]; exact stage.2.1
  have cleanS : ∀ q ∈ BalancedCircuit.work JointInverse1588.portsJ, state.basis q = false := by
    intro q used
    rw [JointInverse1588.portsJ_eq, Q6EndpointCell.ports_work] at used
    exact reads.2.2.1 q used
  have pair := paddedGD_odd_pair state.basis cleanS reads.2.2.2.1 holeState X
  have rX : regValue JointInverse1588.portsJ.r state.basis = oddWord X := by
    rw [JointInverse1588.portsJ_eq, Q6EndpointCell.ports_r]; exact reads.1
  have r0 : regValue JointInverse1588.portsJ.y state.basis = 0 := by
    rw [JointInverse1588.portsJ_eq, Q6EndpointCell.ports_y]
    simpa only [HalfField.centerWord_zero] using reads.2.1
  let mk := records.take (measurementCount paddedGD_odd)
  have out := pair state mk ⟨rX, r0, fun _ _ _ => rfl⟩
  generalize midRun : run paddedGD_odd mk state = mid at out
  rw [jState, gState] at out
  let A : Fp := (if origin (base 1028) && !origin (base 1) then -X else X) / 2
  let B : Fp := if origin (base 1028) then X else 0
  have portR : JointInverse1588.portsJ.r = fieldR := by rw [JointInverse1588.portsJ_eq, Q6EndpointCell.ports_r]
  have portY : JointInverse1588.portsJ.y = fieldY := by rw [JointInverse1588.portsJ_eq, Q6EndpointCell.ports_y]
  have forwardFrame : PairFrame fieldR fieldY state.basis (oddWord A) (oddWord B) mid.basis :=
    JointStageTransport.registers portR portY out.2
  have keepM (q : Wire) (qr : q ∉ fieldR) (qy : q ∉ fieldY) : mid.basis q = state.basis q :=
    forwardFrame.2.2 q qr qy
  have mEnabled : mid.basis (base 2400) = true :=
    (keepM _ (numeric_away_odd 2400 (by omega) (by omega)).1 (numeric_away_odd 2400 (by omega) (by omega)).2).trans
      (reads.2.2.2.2.trans enabled)
  have mFlag : mid.basis (base 2409) = false :=
    (keepM _ (numeric_away_odd 2409 (by omega) (by omega)).1 (numeric_away_odd 2409 (by omega) (by omega)).2).trans
      reads.2.2.2.1
  have mS : mid.basis (s 0 1) = origin (s 0 1) :=
    (keepM _ (numeric_away_odd 1029 (by omega) (by omega)).1 (numeric_away_odd 1029 (by omega) (by omega)).2).trans sState
  let tail := records.drop (measurementCount paddedGD_odd)
  have swapped := selected_swap_odd oddWord 1 (by decide) A B mid tail mEnabled mFlag
    forwardFrame.1 forwardFrame.2.1
  generalize finalRun : run (SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody) tail mid = finalState at swapped
  rw [mS] at swapped
  have joined := JointStageTransport.phase_pair_compose fieldR fieldY state mid finalState
    (oddWord A) (oddWord B)
    (oddWord (if origin (s 0 1) then B else A)) (oddWord (if origin (s 0 1) then A else B))
    out.1 swapped.1 forwardFrame swapped.2
  have cellEq : Rolling1588First.payloadStep true origin 0
      (if origin (base 1028) then ((0 : Fp), X) else (X, 0)) =
      (if origin (s 0 1) then B else A, if origin (s 0 1) then A else B) := by
    simp only [Rolling1588First.payloadStep, Q6EndpointCell.payload, if_true,
      Rolling1588First.active, Rolling1588First.stageIndex, g, s, A, B,
      Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    cases eJ : origin (base 1028) <;> cases eG : origin (base 1) <;> cases eS : origin (base 1029) <;>
      simp [skywalkPayloadCell, eJ, eG, eS]
  have last := codeFrameOdd_arith oddWord centerWord oddWord oddWord
    (Rolling1588First.stageAt true 0) origin X 0
    (if origin (s 0 1) then B else A) (if origin (s 0 1) then A else B) state finalState
    (stageAt0_neutral true 0 (by decide))
    (codec0_disjoint origin ctx _ (onPacket0_support _ (Rolling1588First.stage_support true 0 (by decide))))
    oldInput joined.1 joined.2
  have lastTarget : CodeFrameOdd oddWord oddWord (Rolling1588First.stageAt true 0) origin
      (Rolling1588First.payloadStep true origin 0 (if origin (base 1028) then ((0 : Fp), X) else (X, 0))).1
      (Rolling1588First.payloadStep true origin 0 (if origin (base 1028) then ((0 : Fp), X) else (X, 0))).2 finalState := by
    rw [cellEq]; exact last
  have actual : run (paddedGD_odd ++ SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody) records state = finalState :=
    JointStageTransport.append_states paddedGD_odd (SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody)
      records state mid finalState midRun finalRun
  exact JointStageTransport.close_run _ _ records state finalState actual joined.1 lastTarget

private theorem joint_odd_stage (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp)
    (zero : (if origin (base 1028) then
        2 * (if origin (s 0 1) then Y else X) + (if origin (base 1) then -(if origin (s 0 1) then X else Y)
          else (if origin (s 0 1) then X else Y))
      else (if origin (s 0 1) then X else Y)) = 0) :
    StateTriple (CodeFrameOdd oddWord oddWord (Rolling1588First.stageAt false 3) origin X Y)
      (SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody ++ paddedD_odd)
      (CodeFrameOdd oddWord centerWord (Rolling1588First.stageAt false 3) origin
        (if origin (base 1028) then (if origin (s 0 1) then X else Y) else
          2 * (if origin (s 0 1) then Y else X) + (if origin (base 1) then -(if origin (s 0 1) then X else Y)
            else (if origin (s 0 1) then X else Y))) 0) := by
  intro state records input
  have oldInput := input
  obtain ⟨raw, _, rawFrame, encoded⟩ := input
  have legal := raw0_legal oddWord oddWord origin ctx X Y raw rawFrame
  have stage := stageAt0_correct false 3 (by decide) raw [] legal
  have reads := stage0_read oddWord oddWord origin ctx false 3 (by omega) X Y state oldInput
  have rawAt (a : Nat) (h1 : a < 2056) (h2 : a < 770 ∨ 1026 ≤ a) : raw.basis (base a) = origin (base a) :=
    rawFrame.2.2 _ (numeric_away_odd a (Or.inl h1) h2).1 (numeric_away_odd a (Or.inl h1) h2).2
  have jState : state.basis (base 1028) = origin (base 1028) := by
    have off : base 1028 ∉ wires (Rolling1588First.stageAt false 3) := by
      have h1not : 1 ∉ wires (Rolling1588First.stageCode false 3) := by
        show 1 ∉ wires (renameProgram (localTriple 2 3 4) e3)
        rw [renameProgram_support]
        intro hm; obtain ⟨y, _, eq⟩ := Finset.mem_image.mp hm
        change (2 * (if y / 2 = 0 then 2 else if y / 2 = 1 then 3 else 4) + y % 2 : Nat) = 1 at eq
        split_ifs at eq <;> omega
      have h := onPacket0_label_free (Rolling1588First.stageCode false 3)
        (Rolling1588First.stage_support false 3 (by decide)) 1 (by decide) h1not
      have e : MeasuredCodec5.label packetMap0 1 = base 1028 := label0_odd 0 (by decide)
      rw [e] at h; exact h
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ off).trans (rawAt 1028 (by omega) (Or.inr (by omega)))
  have gState : state.basis (base 1) = origin (base 1) := by
    rw [encoded]; exact stage.2.2.1.trans (rawAt 1 (by omega) (Or.inl (by omega)))
  have sState : state.basis (s 0 1) = origin (s 0 1) := by
    rw [encoded]; exact stage.2.2.2.trans (rawAt 1029 (by omega) (Or.inr (by omega)))
  have holeState : state.basis (base 1032) = false := by rw [encoded]; exact stage.2.1
  let head := SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody
  let before := run head (records.take (measurementCount head)) state
  have swapped := selected_swap_odd oddWord 1 (by decide) X Y state
    (records.take (measurementCount head)) (reads.2.2.2.2.trans enabled) reads.2.2.2.1 reads.1 reads.2.1
  have keepB (q : Wire) (qr : q ∉ fieldR) (qy : q ∉ fieldY) : before.basis q = state.basis q :=
    swapped.2.2.2 q qr qy
  let A : Fp := if origin (s 0 1) then Y else X
  let B : Fp := if origin (s 0 1) then X else Y
  have arith : PairFrame fieldR fieldY state.basis (oddWord A) (oddWord B) before.basis := by
    have h := swapped.2; rw [sState] at h; exact h
  have mid : CodeFrameOdd oddWord oddWord (Rolling1588First.stageAt false 3) origin A B before :=
    codeFrameOdd_arith oddWord oddWord oddWord oddWord (Rolling1588First.stageAt false 3) origin X Y A B
      state before (stageAt0_neutral false 3 (by decide))
      (codec0_disjoint origin ctx _ (onPacket0_support _ (Rolling1588First.stage_support false 3 (by decide))))
      oldInput swapped.1 arith
  have cleanB : ∀ q ∈ BalancedCircuit.work JointInverse1588.portsJ, before.basis q = false := by
    intro q used
    rw [JointInverse1588.portsJ_eq, Q6EndpointCell.ports_work] at used
    have off := half_work_away q used
    exact (keepB q off.1 off.2).trans (reads.2.2.1 q used)
  have signB : before.basis (base 2409) = false :=
    (keepB _ (numeric_away_odd 2409 (by omega) (by omega)).1 (numeric_away_odd 2409 (by omega) (by omega)).2).trans reads.2.2.2.1
  have holeB : before.basis (base 1032) = false :=
    (keepB _ (numeric_away_odd 1032 (by omega) (by omega)).1 (numeric_away_odd 1032 (by omega) (by omega)).2).trans holeState
  have jB : before.basis (base 1028) = origin (base 1028) :=
    (keepB _ (numeric_away_odd 1028 (by omega) (by omega)).1 (numeric_away_odd 1028 (by omega) (by omega)).2).trans jState
  have gB : before.basis (base 1) = origin (base 1) :=
    (keepB _ (numeric_away_odd 1 (by omega) (by omega)).1 (numeric_away_odd 1 (by omega) (by omega)).2).trans gState
  let Z : Fp := if origin (base 1028) then B else 2 * A + (if origin (base 1) then -B else B)
  have matrix := FirstInverse5.matrix_inverse (origin (base 1028)) (origin (base 1)) A B zero
  have pair := paddedD_odd_pair before.basis cleanB signB holeB Z
  rw [jB, gB] at pair
  have mA : A = (if origin (base 1028) && !origin (base 1) then -Z else Z) / 2 := matrix.1
  have mB : B = (if origin (base 1028) then Z else 0) := matrix.2
  rw [← mA, ← mB] at pair
  have rA : regValue JointInverse1588.portsJ.r before.basis = oddWord A := by
    rw [JointInverse1588.portsJ_eq, Q6EndpointCell.ports_r]; exact arith.1
  have rB : regValue JointInverse1588.portsJ.y before.basis = oddWord B := by
    rw [JointInverse1588.portsJ_eq, Q6EndpointCell.ports_y]; exact arith.2.1
  let tail := records.drop (measurementCount head)
  have out := pair before tail ⟨rA, rB, fun _ _ _ => rfl⟩
  have outFrame : PairFrame fieldR fieldY before.basis (oddWord Z) (centerWord (0 : Fp))
      (run paddedD_odd tail before).basis := by
    rw [HalfField.centerWord_zero]
    have h := out.2
    rw [JointInverse1588.portsJ_eq, Q6EndpointCell.ports_r, Q6EndpointCell.ports_y] at h
    exact h
  have last := codeFrameOdd_arith oddWord oddWord oddWord centerWord
    (Rolling1588First.stageAt false 3) origin A B Z 0 before (run paddedD_odd tail before)
    (stageAt0_neutral false 3 (by decide))
    (codec0_disjoint origin ctx _ (onPacket0_support _ (Rolling1588First.stage_support false 3 (by decide))))
    mid out.1 outFrame
  rw [run_append]
  exact ⟨out.1.trans swapped.1, last⟩

theorem firstBodyModelOdd_frame (half : Bool → Program) (divide : Bool)
    (law : OddHalfLaw (half divide) divide) (hsup : OddHalfSupport (half divide))
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp)
    (hz : FirstZero.FirstHyp divide origin X Y) :
    Triple (PairFrame fieldR fieldY origin (oddWord X) (firstYIn divide Y))
      (firstBodyModelOdd half divide)
      (PairFrame fieldR fieldY origin
        (oddWord (Replay5.firstPayload divide origin (X, Y)).1)
        (firstYOut divide (Replay5.firstPayload divide origin (X, Y)).2)) := by
  cases divide
  · have shape : firstBodyModelOdd half false =
        Rolling1588First.stageAt false 0 ++
          PacketSequence.program true (segmentOdd (half false) false) 0 3 ++
          (SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody ++ paddedD_odd ++
            Rolling1588First.transitionAt false 3) := by
      simp [firstBodyModelOdd, firstJointBackOdd, Rolling1588First.stageAt, Rolling1588First.transitionAt,
        Rolling1588First.stageCode, Rolling1588First.stageIndex, Rolling1588First.active,
        Rolling1588First.hole, Rolling1588First.pack, Rolling1588First.unpack,
        Rolling1588First.transition, segmentOdd, PacketSequence.program,
        onPacket0_append, onPacket0_triple, List.append_assoc]
    have hzf : (Replay5.firstPayload false origin (X, Y)).2 = 0 := hz.1 rfl
    have rest := payload0_eq_rest false origin enabled (X, Y)
    simp only [Bool.not_false] at rest
    have four : directionalPayload true (mixedTranscriptControls origin (base 2400) Replay5.restLetters) (X, Y) =
        skywalkPayloadUncell (origin (base 1)) (origin (s 0 1))
          (PacketSequence.payload true (Rolling1588First.payloadStep false origin) 0 3 (X, Y)) := by
      rw [← rest]; rfl
    have bit : mixedTranscriptBit origin (base 2400) (base 1028)
        (mixedTranscriptUnitTrace.getD 0 (false, false)).2 = origin (base 1028) := by
      simp only [mixedTranscriptBit, enabled, if_true]
    have steps := seq_frame (segmentOdd (half false) false)
      (fun k (V : Fp × Fp) => CodeFrameOdd oddWord oddWord (Rolling1588First.stageAt false k) origin V.1 V.2)
      (Rolling1588First.payloadStep false origin) 4
      (fun k hk V => segmentOdd_frame (half false) false law hsup k hk origin ctx enabled V) 0 3 (by decide) (X, Y)
    generalize hV : PacketSequence.payload true (Rolling1588First.payloadStep false origin) 0 3 (X, Y) = V3 at four steps
    obtain ⟨X3, Y3⟩ := V3
    have pay : Replay5.firstPayload false origin (X, Y) =
        if origin (base 1028) then
          ((skywalkPayloadUncell (origin (base 1)) (origin (s 0 1)) (X3, Y3)).2,
            (skywalkPayloadUncell (origin (base 1)) (origin (s 0 1)) (X3, Y3)).1)
        else skywalkPayloadUncell (origin (base 1)) (origin (s 0 1)) (X3, Y3) := by
      simp only [Replay5.firstPayload, Bool.false_eq_true, if_false, four, bit]
    rw [pay] at hzf
    have zero : (if origin (base 1028) then
        2 * (if origin (s 0 1) then Y3 else X3) + (if origin (base 1) then -(if origin (s 0 1) then X3 else Y3)
          else (if origin (s 0 1) then X3 else Y3))
      else (if origin (s 0 1) then X3 else Y3)) = 0 := by
      cases hJ : origin (base 1028) <;> cases hG : origin (base 1) <;> cases hS : origin (s 0 1) <;>
        simp only [hJ, hG, hS, skywalkPayloadUncell, if_true, Bool.false_eq_true, if_false] at hzf ⊢ <;>
        exact hzf
    have final : Replay5.firstPayload false origin (X, Y) =
        ((if origin (base 1028) then (if origin (s 0 1) then X3 else Y3) else
          2 * (if origin (s 0 1) then Y3 else X3) + (if origin (base 1) then -(if origin (s 0 1) then X3 else Y3)
            else (if origin (s 0 1) then X3 else Y3))), 0) := by
      rw [pay]
      cases hJ : origin (base 1028) <;> cases hG : origin (base 1) <;> cases hS : origin (s 0 1) <;>
        simp only [hJ, hG, hS, skywalkPayloadUncell, if_true, Bool.false_eq_true, if_false] at hzf zero ⊢ <;>
        rw [hzf]
    have js := joint_odd_stage origin ctx enabled X3 Y3 zero
    have tr := transition0_stage oddWord centerWord false 3 (by decide) origin ctx
      (if origin (base 1028) then (if origin (s 0 1) then X3 else Y3) else
        2 * (if origin (s 0 1) then Y3 else X3) + (if origin (base 1) then -(if origin (s 0 1) then X3 else Y3)
          else (if origin (s 0 1) then X3 else Y3))) 0
    have chain := ((opening0_frame oddWord oddWord false origin ctx X Y).seq steps).seq (js.seq tr)
    have actual := StateTriple.program_eq shape (by simpa only [List.append_assoc] using chain)
    intro state records input
    have out := actual state records input
    obtain ⟨raw, _, rawFrame, encoded⟩ := out.2
    have closed : Rolling1588First.stageAt false 4 = [] := by
      simp [Rolling1588First.stageAt, Rolling1588First.stageCode, onPacket, renameProgram]
    have same : run (firstBodyModelOdd half false) records state = raw := by
      simpa only [closed, run] using encoded
    refine ⟨out.1, ?_⟩
    rw [same, final]
    exact rawFrame
  · have y0 : Y = 0 := hz.2 rfl
    subst y0
    have shape : firstBodyModelOdd half true =
        Rolling1588First.stageAt true 0 ++
          (paddedGD_odd ++ SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody) ++
          (Rolling1588First.transitionAt true 0 ++
            PacketSequence.program true (segmentOdd (half true) true) 1 3) := by
      simp [firstBodyModelOdd, firstCellsJFrontOdd, firstRestZFrontOdd, Rolling1588First.stageAt,
        Rolling1588First.transitionAt, Rolling1588First.stageCode, Rolling1588First.stageIndex,
        Rolling1588First.active, Rolling1588First.hole, Rolling1588First.pack,
        Rolling1588First.unpack, Rolling1588First.transition, segmentOdd, PacketSequence.program,
        onPacket0_append, onPacket0_triple, List.append_assoc]
    let V0 : Fp × Fp := if origin (base 1028) then ((0 : Fp), X) else (X, 0)
    have js := jointD_odd_stage origin ctx enabled X
    have tr := transition0_stage oddWord oddWord true 0 (by decide) origin ctx
      (Rolling1588First.payloadStep true origin 0 V0).1 (Rolling1588First.payloadStep true origin 0 V0).2
    have steps := seq_frame (segmentOdd (half true) true)
      (fun k (V : Fp × Fp) => CodeFrameOdd oddWord oddWord (Rolling1588First.stageAt true k) origin V.1 V.2)
      (Rolling1588First.payloadStep true origin) 4
      (fun k hk V => segmentOdd_frame (half true) true law hsup k hk origin ctx enabled V) 1 3 (by decide)
      (Rolling1588First.payloadStep true origin 0 V0)
    have chain := ((opening0_frame oddWord centerWord true origin ctx X 0).seq js).seq (tr.seq steps)
    have actual := StateTriple.program_eq shape (by simpa only [List.append_assoc] using chain)
    have bit : mixedTranscriptBit origin (base 2400) (base 1028)
        (mixedTranscriptUnitTrace.getD 0 (false, false)).2 = origin (base 1028) := by
      simp only [mixedTranscriptBit, enabled, if_true]
    have rest := payload0_eq_rest true origin enabled V0
    have one : PacketSequence.payload true (Rolling1588First.payloadStep true origin) 0 4 V0 =
        PacketSequence.payload true (Rolling1588First.payloadStep true origin) 1 3
          (Rolling1588First.payloadStep true origin 0 V0) := by
      simp only [PacketSequence.payload, if_true]
    have pay : Replay5.firstPayload true origin (X, 0) =
        PacketSequence.payload true (Rolling1588First.payloadStep true origin) 1 3
          (Rolling1588First.payloadStep true origin 0 V0) := by
      rw [← one, rest]
      simp only [Replay5.firstPayload, if_true, bit, Bool.not_true, V0]
    intro state records input
    have out := actual state records input
    obtain ⟨raw, _, rawFrame, encoded⟩ := out.2
    have closed : Rolling1588First.stageAt true 4 = [] := by
      simp [Rolling1588First.stageAt, Rolling1588First.stageCode, onPacket, renameProgram]
    have same : run (firstBodyModelOdd half true) records state = raw := by
      simpa only [closed, run] using encoded
    refine ⟨out.1, ?_⟩
    rw [same, pay]
    exact rawFrame

/-! ### Support, `G0CarryLoan5`, and `firstPacketModelOdd_cut_frame` -/

private theorem firstBodyModelOdd_readSites_and_g0 (half : Bool → Program) (divide : Bool)
    (hsup : OddHalfSupport (half divide)) :
    wires (firstBodyModelOdd half divide) ⊆ FrontierReplay1591.readSites 0 ∧
    base 0 ∉ wires (firstBodyModelOdd half divide) := by
  let W := FrontierReplay1591.readSites 0
  have hhist (i : Nat) (hi : i < 5) : g 0 i ∈ W ∧ s 0 i ∈ W := by
    have c := Replay5.history_controls 0 i hi
    rw [← NewHistory5.encode_support_eq] at c
    exact ⟨Finset.mem_union_right _ c.1, Finset.mem_union_right _ c.2⟩
  have hflag : base 2409 ∈ W :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr (by simp)))
  have hid (i : Nat) (hi : i ∈ Q6EndpointCell.ids) : base i ∈ W :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, hi, rfl⟩))))
  have hswW : wires FrontierSW1591.swapBody ⊆ W := by
    intro q hq
    have hm := swapBody_wires_sub hq
    rw [balancedSharedPorts_r, balancedSharedPorts_y] at hm
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, wireBlock, List.mem_map,
      List.mem_range'_1] at hm
    rcases hm with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact hflag
    · exact hid j (mem_q6_ids_r j hj.1 hj.2)
    · exact hid j (mem_q6_ids_y j hj.1 hj.2)
  have hsw0 : base 0 ∉ wires FrontierSW1591.swapBody := by
    intro used
    have m := swapBody_wires_sub used
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at m
    have aw := numeric_away_odd 0 (by omega) (by omega)
    exact m.elim (by decide) (fun h => h.elim aw.1 aw.2)
  have selW_wires (src flag : Wire) (P : Program) :
      wires (SW.selW src flag P) = {src, flag} ∪ wires P := by
    rw [SW.selW, wires_append, wires_append]
    have h1 : wires [.CX src flag] = {src, flag} := by
      simp [wires, Instr.wires]
    have h2 : wires [.measureX flag [] [.Z src]] = {flag, src} := by
      simp [wires, Instr.wires, correctionWires]
    rw [h1, h2]
    ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hselW (a : Nat) (ha : a < 5) :
      wires (SW.selW (s 0 a) (base 2409) FrontierSW1591.swapBody) ⊆ W ∧
      base 0 ∉ wires (SW.selW (s 0 a) (base 2409) FrontierSW1591.swapBody) := by
    rw [selW_wires]
    refine ⟨Finset.union_subset (by
        intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact (hhist a ha).2
        · exact hflag) hswW, ?_⟩
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
    have hne : base 0 ≠ s 0 a := by
      simp only [s, Nat.mul_zero, Nat.add_zero]; exact HostOB5.host_ne 0 (1028 + a) (by omega)
    exact ⟨⟨hne, by decide⟩, hsw0⟩
  have hcell (a h : Nat) (ha : a < 5) (ha0 : a ≠ 0) (hh : h < 5) :
      wires (cellOdd divide (half divide) a h) ⊆ W ∧
      base 0 ∉ wires (cellOdd divide (half divide) a h) := by
    have hP0 : base 0 ∉ wires (half divide) := oddHalfSupport_away _ hsup 0 (Or.inl (by omega))
    have hPW : wires (half divide) ⊆ W := oddHalfSupport_readSites _ hsup
    have h719W : base 719 ∈ W := hid 719 (mem_q6_ids_carry 719 (by omega) (by omega))
    have h516W : packetCarry 0 ∈ W := hid 516 (mem_q6_ids_carry 516 (by omega) (by omega))
    have hrebW : wires (renameProgram (Equiv.swap (base 719) (s 0 h)) (half divide)) ⊆ W := by
      rw [renameProgram_support]
      intro q hq; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      by_cases e1 : x = base 719
      · subst x; rw [Equiv.swap_apply_left]; exact (hhist h hh).2
      · by_cases e2 : x = s 0 h
        · subst x; rw [Equiv.swap_apply_right]; exact h719W
        · rw [Equiv.swap_apply_of_ne_of_ne e1 e2]; exact hPW hx
    have hhwW : wires (halfWindowOdd (half divide) a h) ⊆ W := by
      intro q hq
      rcases Finset.mem_union.mp (ControlLoan1589.loanWindow_support (g 0 a) (base 2409) (packetCarry 0) _ hq) with e | b
      · rcases Finset.mem_insert.mp e with rfl | e
        · exact (hhist a ha).1
        · rw [Finset.mem_singleton.mp e]; exact hflag
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp b
        by_cases e1 : x = packetCarry 0
        · subst x; rw [Equiv.swap_apply_left]; exact (hhist a ha).1
        · by_cases e2 : x = g 0 a
          · subst x; rw [Equiv.swap_apply_right]; exact h516W
          · rw [Equiv.swap_apply_of_ne_of_ne e1 e2]; exact hrebW hx
    have hhw0 : base 0 ∉ wires (halfWindowOdd (half divide) a h) := by
      have h0ga : base 0 ≠ g 0 a := by simp only [g, Nat.mul_zero, Nat.zero_add]; exact HostOB5.host_ne 0 a (by omega)
      have h0sh : base 0 ≠ s 0 h := by simp only [s, Nat.mul_zero, Nat.add_zero]; exact HostOB5.host_ne 0 (1028 + h) (by omega)
      intro used
      rcases Finset.mem_union.mp (ControlLoan1589.loanWindow_support (g 0 a) (base 2409) (packetCarry 0) _ used) with e | b
      · simp only [Finset.mem_insert, Finset.mem_singleton] at e
        exact e.elim h0ga (by decide)
      · obtain ⟨x, hx, eq⟩ := Finset.mem_image.mp b
        have fix1 : Equiv.swap (packetCarry 0) (g 0 a) (base 0) = base 0 :=
          Equiv.swap_apply_of_ne_of_ne (by decide) h0ga
        have h0x := (Equiv.swap (packetCarry 0) (g 0 a)).injective (eq.trans fix1.symm)
        subst h0x
        rw [renameProgram_support] at hx
        obtain ⟨y, hy, eq2⟩ := Finset.mem_image.mp hx
        have fix2 : Equiv.swap (base 719) (s 0 h) (base 0) = base 0 :=
          Equiv.swap_apply_of_ne_of_ne (by decide) h0sh
        have h0y := (Equiv.swap (base 719) (s 0 h)).injective (eq2.trans fix2.symm)
        exact hP0 (h0y ▸ hy)
    cases divide
    · simp only [cellOdd, Bool.false_eq_true, if_false, wires_append, Finset.union_subset_iff,
        Finset.mem_union, not_or]
      exact ⟨⟨(hselW a ha).1, hhwW⟩, (hselW a ha).2, hhw0⟩
    · simp only [cellOdd, if_true, wires_append, Finset.union_subset_iff,
        Finset.mem_union, not_or]
      exact ⟨⟨hhwW, (hselW a ha).1⟩, hhw0, (hselW a ha).2⟩
  have htr (a b c : Nat) (ha : a < 5) (hb : b < 5) (hc : c < 5) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
      (P : Program) : wires (triple a b c P) ⊆ W ∧ base 0 ∉ wires (triple a b c P) := by
    have hmap (y : Wire) : tripleMap a b c y ∈ W ∧ tripleMap a b c y ≠ base 0 := by
      have hm := LT48T.tripleMap_mem a b c y
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with eq | eq | eq | eq | eq | eq <;> rw [eq]
      · exact ⟨(hhist a ha).1, by simp only [g, Nat.mul_zero, Nat.zero_add]; exact HostOB5.host_ne a 0 (by omega)⟩
      · exact ⟨(hhist a ha).2, by simp only [s, Nat.mul_zero, Nat.add_zero]; exact HostOB5.host_ne (1028 + a) 0 (by omega)⟩
      · exact ⟨(hhist b hb).1, by simp only [g, Nat.mul_zero, Nat.zero_add]; exact HostOB5.host_ne b 0 (by omega)⟩
      · exact ⟨(hhist b hb).2, by simp only [s, Nat.mul_zero, Nat.add_zero]; exact HostOB5.host_ne (1028 + b) 0 (by omega)⟩
      · exact ⟨(hhist c hc).1, by simp only [g, Nat.mul_zero, Nat.zero_add]; exact HostOB5.host_ne c 0 (by omega)⟩
      · exact ⟨(hhist c hc).2, by simp only [s, Nat.mul_zero, Nat.add_zero]; exact HostOB5.host_ne (1028 + c) 0 (by omega)⟩
    refine ⟨?_, ?_⟩
    · intro q hq; rw [triple, renameProgram_support] at hq
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hq; exact (hmap y).1
    · intro used; rw [triple, renameProgram_support] at used
      obtain ⟨y, _, eq⟩ := Finset.mem_image.mp used; exact (hmap y).2 eq
  have hker (K : Program) (hsub : wires K ⊆ JointInverse1588.kernelSites) : wires K ⊆ W := by
    intro q used
    have m := List.mem_toFinset.mp (hsub used)
    have field (w : Wire) (hw : w ∈ JointInverse1588.portsJ.wires) : w ∈ W := by
      rw [JointInverse1588.portsJ_eq] at hw
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (List.mem_toFinset.mpr ((Q6EndpointCell.mem_ports_wires base (base 2409) w).mp hw)))
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with ((h | h) | h) | h | h | h | h | h | h | h
    · exact field q (EntryRetained5.data_member _ q (by simp [h]))
    · exact field q (EntryRetained5.data_member _ q (by simp [h]))
    · exact field q (EntryRetained5.data_member _ q (by simp [List.mem_of_mem_take h]))
    · exact field q (by rw [h]; simp [BalancedCircuit.Layout.wires, BalancedCleanup.Layout.wires])
    · exact field q (by rw [h]; simp [BalancedCircuit.Layout.wires, BalancedCleanup.Layout.wires])
    · exact field q (by rw [h]; simp [BalancedCircuit.Layout.wires, BalancedCleanup.Layout.wires])
    · exact field q (by rw [h]; simp [BalancedCircuit.Layout.wires, BalancedCleanup.Layout.wires])
    · rw [h]; exact (hhist 0 (by decide)).2
    · rw [h]; exact (hhist 1 (by decide)).1
    · rw [h]; exact (hhist 4 (by decide)).2
  have c2 := hcell 2 4 (by decide) (by decide) (by decide)
  have c3 := hcell 3 2 (by decide) (by decide) (by decide)
  have c4 := hcell 4 2 (by decide) (by decide) (by decide)
  have st1 := hselW 1 (by decide)
  cases divide
  · have kD := hker paddedD_odd paddedD_odd_support
    have kD0 := paddedD_odd_free 0 (Or.inl rfl)
    simp only [firstBodyModelOdd, firstJointBackOdd, Bool.false_eq_true, if_false,
      wires_append, Finset.union_subset_iff, Finset.mem_union, not_or]
    refine ⟨⟨(htr 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3).1,
      ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c4.1, (htr 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3short).1⟩,
        (htr 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3short).1⟩, c3.1⟩,
        (htr 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3).1⟩,
        (htr 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3).1⟩, c2.1⟩,
        (htr 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3short).1⟩,
        (htr 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3short).1⟩,
        st1.1⟩, kD⟩, (htr 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3).1⟩⟩,
      ⟨(htr 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3).2,
      ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c4.2, (htr 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3short).2⟩,
        (htr 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3short).2⟩, c3.2⟩,
        (htr 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3).2⟩,
        (htr 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3).2⟩, c2.2⟩,
        (htr 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3short).2⟩,
        (htr 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3short).2⟩,
        st1.2⟩, kD0⟩, (htr 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3).2⟩⟩⟩
  · have kGD := hker paddedGD_odd paddedGD_odd_support
    have kGD0 := paddedGD_odd_free 0 (Or.inl rfl)
    simp only [firstBodyModelOdd, firstCellsJFrontOdd, firstRestZFrontOdd, if_true,
      wires_append, Finset.union_subset_iff, Finset.mem_union, not_or]
    refine ⟨⟨⟨(htr 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3).1, kGD, st1.1,
      ⟨⟨⟨⟨⟨⟨⟨⟨(htr 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3short).1,
        (htr 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3short).1⟩, c2.1⟩,
        (htr 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3).1⟩,
        (htr 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3).1⟩, c3.1⟩,
        (htr 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3short).1⟩,
        (htr 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3short).1⟩, c4.1⟩⟩,
      (htr 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3).1⟩,
      ⟨⟨(htr 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3).2, kGD0, st1.2,
      ⟨⟨⟨⟨⟨⟨⟨⟨(htr 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3short).2,
        (htr 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3short).2⟩, c2.2⟩,
        (htr 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3).2⟩,
        (htr 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3).2⟩, c3.2⟩,
        (htr 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3short).2⟩,
        (htr 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e3short).2⟩, c4.2⟩⟩,
      (htr 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3).2⟩⟩

private theorem cut_window_frame_odd (wordR wordY outR outY : Fp → Nat) (cut : Nat)
    (origin : BasisState) (X Y A B : Fp) (body : Program)
    (disjoint : Disjoint (wires (otherEncodeCut base cut 0 102)) (wires body))
    (currentLaw : ∀ state records,
      CodeFrameOdd wordR wordY (encodeGroup base (decide (cut ≤ 0)) 0) origin X Y state →
      (run body records state).phase = state.phase ∧
      CodeFrameOdd outR outY (encodeGroup base (decide (cut ≤ 0)) 0) origin A B (run body records state))
    (state : State) (records : List Bool) (input : CutFrameOdd wordR wordY cut origin X Y state) :
    (run body records state).phase = state.phase ∧
      CutFrameOdd outR outY cut origin A B (run body records state) := by
  obtain ⟨raw, rawPhase, rawFrame, encoded⟩ := input
  let current := run (encodeGroup base (decide (cut ≤ 0)) 0) [] raw
  have currentPhase : current.phase = raw.phase :=
    encodeGroup_zero_phase base (decide (cut ≤ 0)) base_pool_nodup 0 (by omega) raw
  have currentFrame : CodeFrameOdd wordR wordY (encodeGroup base (decide (cut ≤ 0)) 0) origin X Y current :=
    ⟨raw, currentPhase.symm, rawFrame, rfl⟩
  have result := currentLaw current records currentFrame
  obtain ⟨rawOut, _, outFrame, outEncoded⟩ := result.2
  have factor := allEncodeCut_factor base cut base_pool_nodup 102 0 (by decide) (by decide) raw
  have actual : run body records state = run (otherEncodeCut base cut 0 102) []
      (run body records current) := by
    rw [encoded, factor]
    exact (run_disjoint_commute (otherEncodeCut base cut 0 102) body disjoint [] records current).symm
  have afterFactor := allEncodeCut_factor base cut base_pool_nodup 102 0 (by decide) (by decide) rawOut
  have actualOut : run body records state = run (allEncodeCut base cut 102) [] rawOut := by
    rw [actual, outEncoded, ← afterFactor]
  have finalPhase : (run body records state).phase = state.phase :=
    (congrArg State.phase actual).trans
      ((otherEncodeCut_zero_phase base cut 0 base_pool_nodup 102 (by decide) _).trans
        (result.1.trans (currentPhase.trans rawPhase)))
  refine ⟨finalPhase, rawOut, ?_, outFrame, actualOut⟩
  exact ((congrArg State.phase actualOut).trans
    (allEncodeCut_zero_phase base cut base_pool_nodup 102 (by decide) rawOut)).symm

private theorem cutFrameOdd_zero_region (wordR wordY : Fp → Nat) (cut : Nat) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X Y : Fp) (state : State)
    (frame : CutFrameOdd wordR wordY cut origin X Y state) :
    ∀ q, Placement5.zeroRegion q → state.basis (base q) = false := by
  intro q hq
  obtain ⟨raw, _, rawFrame, encoded⟩ := frame
  rcases hq with work | hole
  · have rawEnv := pair_env base (base 2409) ctx.hn origin raw.basis _ _ ctx.env rawFrame
    have zero := OffsetCleanupBorrowedCaller.maskBit_zero base raw.basis rawEnv.1 q
      (by unfold Placement5.workRegion at work; omega) (by unfold Placement5.workRegion at work; omega)
    have support : wires (allEncodeCut base cut 102) ⊆ (wireBlock base 0 512 ++ wireBlock base 1028 512).toFinset := by
      rw [allEncodeCut_support_eq]
      exact NewHistory5.allEncode_history_support base 102 (by decide)
    have away : base q ∉ wires (allEncodeCut base cut 102) := by
      intro used
      have member := support used
      simp only [List.mem_toFinset, List.mem_append] at member
      rcases member with low | high
      · exact OwnPlusHost.not_block q 0 512 (by unfold Placement5.workRegion at work; omega) low
      · exact OwnPlusHost.not_block q 1028 512 (by unfold Placement5.workRegion at work; omega) high
    rw [encoded]
    exact (run_preserves_outside (allEncodeCut base cut 102) [] raw _ away).trans zero
  · have recover := Placement5.hole_recover q hole
    have rawLegal := NewHistory5.frame_history_legal base (base 2409) ctx.hn
      (ctx.hp _ (by simp)) 102 (by decide) origin raw.basis _ _ ctx.legal rawFrame
    rw [encoded, ← recover.2]
    exact allEncodeCut_holes_zero base cut base_pool_nodup raw [] rawLegal _ recover.1

private theorem first_window_frame_odd (wR wY oR oY : Fp → Nat) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X Y A B : Fp) (body : Program)
    (correct : Triple (PairFrame fieldR fieldY origin (wR X) (wY Y)) body
      (PairFrame fieldR fieldY origin (oR A) (oY B)))
    (nonzero : origin (base 0) = true ∨ origin (base 1028) = true) :
    StateTriple (CodeFrameOdd wR wY (NewHistory5.encode base 0) origin X Y)
      (Prefix1590.firstDecode ++ (body ++ Prefix1590.firstEncode))
      (CodeFrameOdd oR oY (NewHistory5.encode base 0) origin A B) := by
  intro state records input
  obtain ⟨raw, rawPhase, rawFrame, encoded⟩ := input
  let bodyRecords := records.drop 2
  let rawOut := run body bodyRecords raw
  have legal := raw0_legal wR wY origin ctx X Y raw rawFrame
  have rawPref (uR uY : Fp → Nat) (a b : Fp) (r : State)
      (fr : PairFrame fieldR fieldY origin (uR a) (uY b) r.basis) (q : Fin 10) :
      r.basis (packetMap0 q) = origin (packetMap0 q) := by
    have aw := NewHistory5.history_words_away base (base 2409) ctx.hn (ctx.hp _ (by simp)) 0 (by decide) q
    exact fr.2.2 _ aw.1 aw.2
  have nonzeroAt : raw.basis (packetMap0 0) = true ∨ raw.basis (packetMap0 1) = true := by
    rw [rawPref _ _ X Y raw rawFrame 0, rawPref _ _ X Y raw rawFrame 1]; exact nonzero
  have result := correct raw bodyRecords rawFrame
  have outLegal := raw0_legal oR oY origin ctx A B rawOut result.2
  have outNonzero : rawOut.basis (packetMap0 0) = true ∨ rawOut.basis (packetMap0 1) = true := by
    rw [rawPref _ _ A B rawOut result.2 0, rawPref _ _ A B rawOut result.2 1]; exact nonzero
  have decoded : run Prefix1590.firstDecode (records.take 2) state = raw := by
    have round := ParityCodec5New.roundtripAtFirst packetMap0 packetMap0_inj raw []
      (records.take 2) legal nonzeroAt
    rw [ParityCodec5New.encodeAt_eq packetMap0 packetMap0_inj raw [] legal nonzeroAt] at round
    rw [encoded]; exact round
  have outEncoded : run Prefix1590.firstEncode (bodyRecords.drop (measurementCount body)) rawOut =
      run (NewHistory5.encode base 0) [] rawOut := by
    rw [show Prefix1590.firstEncode = ParityCodec5New.encodeAtFirst packetMap0 from rfl,
      ParityCodec5New.encodeAt_eq packetMap0 packetMap0_inj rawOut _ outLegal outNonzero]
    exact ParityCodec5New.encodeAt_independent packetMap0 packetMap0_inj rawOut _ [] outLegal
  have decodeM : measurementCount Prefix1590.firstDecode = 2 :=
    (ParityCodec5New.first_countsAt packetMap0).2.2.2
  have actual : run (Prefix1590.firstDecode ++ (body ++ Prefix1590.firstEncode)) records state =
      run (NewHistory5.encode base 0) [] rawOut := by
    rw [Prefix1590.run_three_records, decodeM, decoded, outEncoded]
  have phase := ParityCodec5New.encodeAt_zero_phase packetMap0 packetMap0_inj rawOut
  rw [actual]
  exact ⟨phase.trans (result.1.trans rawPhase), rawOut, phase.symm, result.2, rfl⟩

private theorem first_window_support_odd (body : Program)
    (support : wires body ⊆ NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312}) :
    wires (Prefix1590.firstDecode ++ (body ++ Prefix1590.firstEncode)) ⊆
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} := by
  have encS : wires Prefix1590.firstEncode = wires (NewHistory5.encode base 0) := by
    simpa only [Prefix1590.firstEncode, NewHistory5.encode] using
      (ParityCodec5New.first_mapped_support (History5.historyMap base 0)).1
  have decS : wires Prefix1590.firstDecode = wires (NewHistory5.encode base 0) := by
    rw [Prefix1590.firstDecode, (ParityCodec5New.first_mapped_support _).2, NewHistory5.encode,
      (ParityCodec5New.supportAt_exact _).2, (ParityCodec5New.supportAt_exact _).1]
  have codec : wires (NewHistory5.encode base 0) ⊆
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} :=
    fun _ u => Finset.mem_union_left _ (Finset.mem_union_right _ u)
  simp only [wires_append, Finset.union_subset_iff]
  exact ⟨by rw [decS]; exact codec, support, by rw [encS]; exact codec⟩

private theorem first_cut_window_frame_odd (wR wY oR oY : Fp → Nat) (cut : Nat) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X Y A B : Fp) (body : Program)
    (support : wires body ⊆ NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312})
    (correct : Triple (PairFrame fieldR fieldY origin (wR X) (wY Y)) body
      (PairFrame fieldR fieldY origin (oR A) (oY B)))
    (nonzero : origin (base 0) = true ∨ origin (base 1028) = true) :
    StateTriple (CutFrameOdd wR wY cut origin X Y)
      (Prefix1590.firstDecode ++ (body ++ Prefix1590.firstEncode))
      (CutFrameOdd oR oY cut origin A B) := by
  apply cut_window_frame_odd wR wY oR oY cut origin X Y A B _
    (otherEncodeCut_body_disjoint cut 0 (by decide) origin ctx _ (first_window_support_odd body support))
  simpa only [encodeGroup, if_pos rfl] using first_window_frame_odd wR wY oR oY origin ctx X Y A B body correct nonzero

private theorem place_cut_frame_odd (wR wY oR oY : Fp → Nat) (cut : Nat) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X Y A B : Fp) (body : Program)
    (correct : StateTriple (CutFrameOdd wR wY cut origin X Y) body (CutFrameOdd oR oY cut origin A B)) :
    StateTriple (CutFrameOdd wR wY cut origin X Y) (renameProgram (shifted (Placement5.pi 0)) body)
      (CutFrameOdd oR oY cut origin A B) := by
  intro state records input
  have res := correct state records input
  have same := Replay5.placed_eq (Placement5.pi 0) body
    (fun q hq => Placement5.pi_outside 0 q (by decide) hq) state records
    (cutFrameOdd_zero_region wR wY cut origin ctx X Y state input)
    (cutFrameOdd_zero_region oR oY cut origin ctx A B _ res.2)
  rw [same]; exact res

theorem firstPacketModelOdd_cut_frame (half : Bool → Program) (divide : Bool) (cut : Nat)
    (law : OddHalfLaw (half divide) divide) (hsup : OddHalfSupport (half divide))
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (x : Nat) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)))
    (X Y : Fp) (hz : FirstZero.FirstHyp divide origin X Y) :
    StateTriple (CutFrameOdd oddWord (firstYIn divide) cut origin X Y)
      (firstPacketModelOdd half divide)
      (fun state => let V := Replay5.firstPayload divide origin (X, Y)
        CutFrameOdd oddWord (firstYOut divide) cut origin V.1 V.2 state) := by
  have first := Prefix1590.first_trit_of_trace origin ctx x hx trace
  have bsup := firstBodyModelOdd_readSites_and_g0 half divide hsup
  have bRead : wires (firstBodyModelOdd half divide) ⊆
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} :=
    bsup.1.trans (FrontierReplay1591.readSites_sub 0)
  have borrowSup : wires (G0CarryLoan5.program (base 1028) (base 0) (base 768) (firstBodyModelOdd half divide)) ⊆
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} := by
    let W := NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312}
    have site (q : Fin 10) : History5.historyMap base 0 q ∈ W :=
      Finset.mem_union_left _ (Finset.mem_union_right _ (NewHistory5.history_site_mem base 0 q))
    exact (G0CarryLoan5.support_to _ _ _ _ W bRead (site 1) (site 0)
      (by decide) (by decide) bsup.2).trans (Finset.erase_subset _ _)
  have borrowFrame : Triple (PairFrame fieldR fieldY origin (oddWord X) (firstYIn divide Y))
      (G0CarryLoan5.program (base 1028) (base 0) (base 768) (firstBodyModelOdd half divide))
      (PairFrame fieldR fieldY origin
        (oddWord (Replay5.firstPayload divide origin (X, Y)).1)
        (firstYOut divide (Replay5.firstPayload divide origin (X, Y)).2)) := by
    have correct := firstBodyModelOdd_frame half divide law hsup origin ctx enabled X Y hz
    rw [fieldR, fieldY, balancedSharedPorts_r, balancedSharedPorts_y] at correct
    have away (q : Nat) (hq : q = 0 ∨ q = 768 ∨ q = 1028) :
        base q ∉ wireBlock base 2056 256 ∧ base q ∉ wireBlock base 770 256 :=
      ⟨OwnPlusHost.not_block q 2056 256 (by omega), OwnPlusHost.not_block q 770 256 (by omega)⟩
    have clean : origin (base 768) = false :=
      NewOwnPlusEndpoint.env_zero origin ctx.env ctx.parity 768 (Or.inr rfl)
    simpa only [fieldR, fieldY, balancedSharedPorts_r, balancedSharedPorts_y] using
      G0CarryLoan5.pair_frame (wireBlock base 2056 256) (wireBlock base 770 256) origin
        (oddWord X) (firstYIn divide Y)
        (oddWord (Replay5.firstPayload divide origin (X, Y)).1)
        (firstYOut divide (Replay5.firstPayload divide origin (X, Y)).2)
        (base 1028) (base 0) (base 768) (firstBodyModelOdd half divide) (by decide) (by decide)
        (away 1028 (by simp)) (away 0 (by simp)) (away 768 (by simp))
        bsup.2 clean first.1 first.2 correct
  have current := first_cut_window_frame_odd oddWord (firstYIn divide) oddWord (firstYOut divide)
    cut origin ctx X Y _ _ _ borrowSup borrowFrame first.2
  have placed := place_cut_frame_odd oddWord (firstYIn divide) oddWord (firstYOut divide)
    cut origin ctx X Y _ _ _ current
  apply StateTriple.program_eq _ placed
  simp only [firstPacketModelOdd, firstCoreModelOdd, List.append_assoc]

/-! ### Short-codec equivalence (`firstPacketOdd_run`) -/

private theorem ren_app0 (f : Wire → Wire) (P Q : Program) :
    renameProgram f (P ++ Q) = renameProgram f P ++ renameProgram f Q := by
  simp only [renameProgram, List.map_append]

private theorem prefix_congr0 (X X' Y : Program) (hm : measurementCount X = measurementCount X')
    (h : ∀ m s, run X m s = run X' m s) (m : List Bool) (s : State) :
    run (X ++ Y) m s = run (X' ++ Y) m s := by
  rw [run_append X Y, run_append X' Y, hm, h]

private theorem suffix_congr0 (X Y Y' : Program)
    (h : ∀ m s, run Y m s = run Y' m s) (m : List Bool) (s : State) :
    run (X ++ Y) m s = run (X ++ Y') m s := by
  rw [run_append X Y, run_append X Y', h]

private theorem free_local_eq0 (P Q : Program) (pSupport : wires P ⊆ Finset.range 10)
    (qSupport : wires Q ⊆ Finset.range 10) (pFree : measurementCount P = 0)
    (qFree : measurementCount Q = 0) (law : ∀ x < 1024, MeasuredCodec5.bitRun P x = MeasuredCodec5.bitRun Q x)
    (m : List Bool) (state : State) :
    run (renameProgram (MeasuredCodec5.label packetMap0) P) m state =
      run (renameProgram (MeasuredCodec5.label packetMap0) Q) m state := by
  let lst : State := ⟨state.phase, fun q => state.basis (MeasuredCodec5.label packetMap0 q)⟩
  let x := MeasuredCodec5.pack10 (lst.basis 0) (lst.basis 1) (lst.basis 2) (lst.basis 3) (lst.basis 4)
    (lst.basis 5) (lst.basis 6) (lst.basis 7) (lst.basis 8) (lst.basis 9)
  have xlt : x < 1024 := MeasuredCodec5.pack10_lt _ _ _ _ _ _ _ _ _ _
  have tb : ∀ q ∈ Finset.range 10, lst.basis q = MeasuredCodec5.bitsOf x q := by
    intro q hq
    have hq' : q < 10 := Finset.mem_range.mp hq
    change lst.basis q = x.testBit q
    rw [show x = MeasuredCodec5.pack10 (lst.basis 0) (lst.basis 1) (lst.basis 2) (lst.basis 3)
      (lst.basis 4) (lst.basis 5) (lst.basis 6) (lst.basis 7) (lst.basis 8) (lst.basis 9) from rfl,
      MeasuredCodec5.pack10_bits _ _ _ _ _ _ _ _ _ _ q hq']
    interval_cases q <;> simp [MeasuredCodec5.raw]
  have localEq : run P m lst = run Q m lst := by
    apply FirstNonzeroCodec.run_eq_of_model P Q pSupport qSupport lst m x tb
    rw [MeasuredCodec5.run_sim P m lst.phase x,
      MeasuredCodec5.sim_safe P x (Replay.safe_of_no_measurements P pFree x),
      MeasuredCodec5.run_sim Q m lst.phase x,
      MeasuredCodec5.sim_safe Q x (Replay.safe_of_no_measurements Q qFree x), law x xlt]
  have inj := FirstNonzeroCodec.label_inj' packetMap0 packetMap0_inj
  have pp := run_rename_pool (MeasuredCodec5.label packetMap0) (Finset.range 10)
    inj P pSupport m lst state rfl (fun _ _ => rfl)
  have qq := run_rename_pool (MeasuredCodec5.label packetMap0) (Finset.range 10)
    inj Q qSupport m lst state rfl (fun _ _ => rfl)
  apply State.extensionality
  · exact pp.1.trans ((congrArg State.phase localEq).trans qq.1.symm)
  · funext q
    by_cases used : q ∈ (Finset.range 10).image (MeasuredCodec5.label packetMap0)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp used
      exact (pp.2 i hi).trans ((congrArg (fun t : State => t.basis i) localEq).trans (qq.2 i hi).symm)
    · have off (E : Program) (support : wires E ⊆ Finset.range 10) :
          q ∉ wires (renameProgram (MeasuredCodec5.label packetMap0) E) := by
        rw [renameProgram_support]
        intro member
        obtain ⟨i, hi, eq⟩ := Finset.mem_image.mp member
        exact used (Finset.mem_image.mpr ⟨i, support hi, eq⟩)
      exact (run_preserves_outside _ m state q (off P pSupport)).trans
        (run_preserves_outside _ m state q (off Q qSupport)).symm

private def allCols0 (w : Nat) : CodecBitSliceVerify.Cols := (List.range w).map (CertificateBits.input w)

private theorem allCols0_rel (w x : Nat) (hx : x < 2 ^ w) : CodecBitSliceVerify.Rel (allCols0 w) x x := by
  intro q
  by_cases h : q < w
  · have eq : CodecBitSliceVerify.get (allCols0 w) q = CertificateBits.input w q := by
      simp [CodecBitSliceVerify.get, allCols0, h]
    rw [eq, CertificateBits.input_bit w q x hx]
  · have zero : CodecBitSliceVerify.get (allCols0 w) q = 0 := by
      simp only [CodecBitSliceVerify.get, allCols0, List.getElem?_eq_none
        (by simpa using Nat.le_of_not_gt h : ((List.range w).map (CertificateBits.input w)).length ≤ q),
        Option.getD_none]
    rw [zero, Nat.zero_testBit]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt h)))

private theorem columns_equal0 (w : Nat) (p q : Program)
    (bp : ∀ i ∈ p, CodecBitSliceVerify.target i < (allCols0 w).length)
    (bq : ∀ i ∈ q, CodecBitSliceVerify.target i < (allCols0 w).length)
    (h : (CodecBitSliceVerify.eval (CertificateBits.mask w) p (allCols0 w)).1 = true ∧
         (CodecBitSliceVerify.eval (CertificateBits.mask w) q (allCols0 w)).1 = true ∧
         (CodecBitSliceVerify.eval (CertificateBits.mask w) p (allCols0 w)).2 =
         (CodecBitSliceVerify.eval (CertificateBits.mask w) q (allCols0 w)).2) :
    ∀ x < 2 ^ w, MeasuredCodec5.bitRun p x = MeasuredCodec5.bitRun q x := by
  intro x hx
  have on := CertificateBits.mask_bit w x hx
  have r := allCols0_rel w x hx
  have l := CodecBitSliceVerify.eval_sound _ x on p _ x bp r h.1
  have b := CodecBitSliceVerify.eval_sound _ x on q _ x bq r h.2.1
  apply Nat.eq_of_testBit_eq
  intro k
  exact (l.2 k).trans ((congrArg (fun cs : CodecBitSliceVerify.Cols => (CodecBitSliceVerify.get cs k).testBit x) h.2.2).trans (b.2 k).symm)

private theorem entry_law0 : ∀ x < 1024,
    MeasuredCodec5.bitRun (ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 d3 ++ ([.X 0, .CX 1 0] ++
      (ParityCodec5New.twist ++ FirstNonzeroCodec.encodeFirst.take 16))) x =
    MeasuredCodec5.bitRun (ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 d3short ++ ([.X 0, .CX 1 0] ++
      (ParityCodec5New.twist ++ FirstNonzeroCodec.encodeFirst.take 15))) x :=
  columns_equal0 10 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem exit_law0 : ∀ x < 1024,
    MeasuredCodec5.bitRun ((FirstNonzeroCodec.decodeFirst.drop 124 ++ ParityCodec5New.untwist) ++
      ([.CX 1 0, .X 0] ++ ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 (e3.take 16))) x =
    MeasuredCodec5.bitRun ((FirstNonzeroCodec.decodeFirst.drop 125 ++ ParityCodec5New.untwist) ++
      ([.CX 1 0, .X 0] ++ ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 (e3.take 15))) x :=
  columns_equal0 10 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tail_true0 (m : List Bool) (s : State) :
    run (triple 3 1 2 d3 ++ (G0CarryLoan5.restore (base 1028) (base 0) ++ Prefix1590.firstEncode)) m s =
      run (triple 3 1 2 d3short ++ (G0CarryLoan5.restore (base 1028) (base 0) ++ firstEncodeShort)) m s := by
  have tl (P : Program) : triple 3 1 2 P = renameProgram (MeasuredCodec5.label packetMap0) (ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 P) :=
    (onPacket0_triple 3 1 2 (by decide) (by decide) (by decide) P).symm
  have rl : G0CarryLoan5.restore (base 1028) (base 0) =
      renameProgram (MeasuredCodec5.label packetMap0) [.X 0, .CX 1 0] := by
    simp only [G0CarryLoan5.restore, renameProgram, List.map_cons, List.map_nil, renameInstr,
      label0_even 0 (by decide), label0_odd 0 (by decide), g, Rolling1588.s, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
  have el : Prefix1590.firstEncode =
      renameProgram (MeasuredCodec5.label packetMap0) (ParityCodec5New.twist ++ FirstNonzeroCodec.encodeFirst) := rfl
  let P1 := ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 d3 ++ ([.X 0, .CX 1 0] ++
    (ParityCodec5New.twist ++ FirstNonzeroCodec.encodeFirst.take 16))
  let P2 := ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 d3short ++ ([.X 0, .CX 1 0] ++
    (ParityCodec5New.twist ++ FirstNonzeroCodec.encodeFirst.take 15))
  have old : triple 3 1 2 d3 ++ (G0CarryLoan5.restore (base 1028) (base 0) ++ Prefix1590.firstEncode) =
      renameProgram (MeasuredCodec5.label packetMap0) P1 ++
      renameProgram (MeasuredCodec5.label packetMap0) (FirstNonzeroCodec.encodeFirst.drop 16) := by
    rw [tl, rl, el]
    conv_lhs => rw [← List.take_append_drop 16 FirstNonzeroCodec.encodeFirst]
    simp only [P1, ren_app0, List.append_assoc]
  have new : triple 3 1 2 d3short ++ (G0CarryLoan5.restore (base 1028) (base 0) ++ firstEncodeShort) =
      renameProgram (MeasuredCodec5.label packetMap0) P2 ++
      renameProgram (MeasuredCodec5.label packetMap0) (FirstNonzeroCodec.encodeFirst.drop 16) := by
    rw [tl, rl]
    simp only [P2, firstEncodeShort, ren_app0, List.append_assoc]
  have hm1 : measurementCount P1 = 0 := by unfold P1 measurementCount; decide +kernel
  have hm2 : measurementCount P2 = 0 := by unfold P2 measurementCount; decide +kernel
  have hmc : measurementCount (renameProgram (MeasuredCodec5.label packetMap0) P1) =
      measurementCount (renameProgram (MeasuredCodec5.label packetMap0) P2) := by
    rw [(renameProgram_counts _ P1).2, (renameProgram_counts _ P2).2, hm1, hm2]
  rw [old, new]
  exact prefix_congr0 _ _ _ hmc
    (free_local_eq0 P1 P2 (by unfold P1 wires; decide +kernel) (by unfold P2 wires; decide +kernel)
      hm1 hm2 entry_law0) m s

private theorem tail_false0 (W : Program) (m : List Bool) (s : State) :
    run (Prefix1590.firstDecode ++ (G0CarryLoan5.expose (base 1028) (base 0) ++ (triple 3 1 2 e3 ++ W))) m s =
      run (firstDecodeShort ++ (G0CarryLoan5.expose (base 1028) (base 0) ++ (triple 3 1 2 e3short ++ W))) m s := by
  have tl (P : Program) : triple 3 1 2 P = renameProgram (MeasuredCodec5.label packetMap0) (ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 P) :=
    (onPacket0_triple 3 1 2 (by decide) (by decide) (by decide) P).symm
  have exl : G0CarryLoan5.expose (base 1028) (base 0) =
      renameProgram (MeasuredCodec5.label packetMap0) [.CX 1 0, .X 0] := by
    simp only [G0CarryLoan5.expose, renameProgram, List.map_cons, List.map_nil, renameInstr,
      label0_even 0 (by decide), label0_odd 0 (by decide), g, Rolling1588.s, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
  have dl : Prefix1590.firstDecode =
      renameProgram (MeasuredCodec5.label packetMap0) (FirstNonzeroCodec.decodeFirst ++ ParityCodec5New.untwist) := rfl
  let Q1 := (FirstNonzeroCodec.decodeFirst.drop 124 ++ ParityCodec5New.untwist) ++
    ([.CX 1 0, .X 0] ++ ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 (e3.take 16))
  let Q2 := (FirstNonzeroCodec.decodeFirst.drop 125 ++ ParityCodec5New.untwist) ++
    ([.CX 1 0, .X 0] ++ ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 (e3.take 15))
  have old : Prefix1590.firstDecode ++ (G0CarryLoan5.expose (base 1028) (base 0) ++ (triple 3 1 2 e3 ++ W)) =
      renameProgram (MeasuredCodec5.label packetMap0) (FirstNonzeroCodec.decodeFirst.take 124) ++
      (renameProgram (MeasuredCodec5.label packetMap0) Q1 ++
      (renameProgram (MeasuredCodec5.label packetMap0) (ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 (e3.drop 16)) ++ W)) := by
    rw [dl, exl, tl]
    conv_lhs => rw [← List.take_append_drop 124 FirstNonzeroCodec.decodeFirst, ← List.take_append_drop 16 e3]
    simp only [Q1, ECDSAAdd.Entrant.Rolling1588First.mappedTriple, ren_app0, List.append_assoc]
  have new : firstDecodeShort ++ (G0CarryLoan5.expose (base 1028) (base 0) ++ (triple 3 1 2 e3short ++ W)) =
      renameProgram (MeasuredCodec5.label packetMap0) (FirstNonzeroCodec.decodeFirst.take 124) ++
      (renameProgram (MeasuredCodec5.label packetMap0) Q2 ++
      (renameProgram (MeasuredCodec5.label packetMap0) (ECDSAAdd.Entrant.Rolling1588First.mappedTriple 3 1 2 (e3.drop 16)) ++ W)) := by
    rw [exl, tl]
    simp only [Q2, firstDecodeShort, e3short, ECDSAAdd.Entrant.Rolling1588First.mappedTriple, ren_app0, List.append_assoc]
  have hm1 : measurementCount Q1 = 0 := by unfold Q1 measurementCount; decide +kernel
  have hm2 : measurementCount Q2 = 0 := by unfold Q2 measurementCount; decide +kernel
  have hmc : measurementCount (renameProgram (MeasuredCodec5.label packetMap0) Q1) =
      measurementCount (renameProgram (MeasuredCodec5.label packetMap0) Q2) := by
    rw [(renameProgram_counts _ Q1).2, (renameProgram_counts _ Q2).2, hm1, hm2]
  rw [old, new]
  apply suffix_congr0
  intro m s
  exact prefix_congr0 _ _ _ hmc
    (free_local_eq0 Q1 Q2 (by unfold Q1 wires; decide +kernel) (by unfold Q2 wires; decide +kernel)
      hm1 hm2 exit_law0) m s

theorem firstCoreOdd_run (half : Bool → Program) (divide : Bool) (m : List Bool) (s : State) :
    run (firstCoreOdd half divide) m s = run (firstCoreModelOdd half divide) m s := by
  have sw_triple (P : Program) :
      renameProgram (Equiv.swap (base 768) (base 0)) (triple 3 1 2 P) = triple 3 1 2 P := by
    rw [triple, renameProgram_comp]
    congr 1
    funext y
    have hm := LT48T.tripleMap_mem 3 1 2 y
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with eq | eq | eq | eq | eq | eq <;> rw [Function.comp_apply, eq]
    all_goals exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have sw_d3 := sw_triple d3
  have sw_d3s := sw_triple d3short
  have sw_e3 := sw_triple e3
  have sw_e3s := sw_triple e3short
  cases divide
  · have hc : firstCoreOdd half false = firstDecodeShort ++
        (G0CarryLoan5.expose (base 1028) (base 0) ++ (triple 3 1 2 e3short ++
          (renameProgram (Equiv.swap (base 768) (base 0)) (firstJointBackOdd half) ++
            (G0CarryLoan5.restore (base 1028) (base 0) ++ Prefix1590.firstEncode)))) := by
      simp only [firstCoreOdd, firstBodyShortOdd, Bool.false_eq_true, if_false,
        G0CarryLoan5.program, ren_app0, sw_e3s, List.append_assoc]
    have hm : firstCoreModelOdd half false = Prefix1590.firstDecode ++
        (G0CarryLoan5.expose (base 1028) (base 0) ++ (triple 3 1 2 e3 ++
          (renameProgram (Equiv.swap (base 768) (base 0)) (firstJointBackOdd half) ++
            (G0CarryLoan5.restore (base 1028) (base 0) ++ Prefix1590.firstEncode)))) := by
      simp only [firstCoreModelOdd, firstBodyModelOdd, Bool.false_eq_true, if_false,
        G0CarryLoan5.program, ren_app0, sw_e3, List.append_assoc]
    rw [hc, hm]
    exact (tail_false0 _ m s).symm
  · have hc : firstCoreOdd half true = Prefix1590.firstDecode ++
        (G0CarryLoan5.expose (base 1028) (base 0) ++
          (renameProgram (Equiv.swap (base 768) (base 0)) (firstCellsJFrontOdd half) ++
            (triple 3 1 2 d3short ++ (G0CarryLoan5.restore (base 1028) (base 0) ++ firstEncodeShort)))) := by
      simp only [firstCoreOdd, firstBodyShortOdd, if_true, G0CarryLoan5.program, ren_app0,
        sw_d3s, List.append_assoc]
    have hm : firstCoreModelOdd half true = Prefix1590.firstDecode ++
        (G0CarryLoan5.expose (base 1028) (base 0) ++
          (renameProgram (Equiv.swap (base 768) (base 0)) (firstCellsJFrontOdd half) ++
            (triple 3 1 2 d3 ++ (G0CarryLoan5.restore (base 1028) (base 0) ++ Prefix1590.firstEncode)))) := by
      simp only [firstCoreModelOdd, firstBodyModelOdd, if_true, G0CarryLoan5.program, ren_app0,
        sw_d3, List.append_assoc]
    rw [hc, hm]
    apply suffix_congr0; intro m s
    apply suffix_congr0; intro m s
    apply suffix_congr0; intro m s
    exact (tail_true0 m s).symm

theorem firstPacketOdd_run (half : Bool → Program) (divide : Bool) (m : List Bool) (s : State) :
    run (firstPacketOdd half divide) m s = run (firstPacketModelOdd half divide) m s := by
  let e := shifted (Placement5.pi 0)
  have pull_symm (t : State) : pullState e.symm (pullState e t) = t := by
    apply State.extensionality; · rfl
    · funext q; simp [pullState]
  have a := ECDSAAdd.run_rename e e.injective (firstCoreOdd half divide) m s
  have b := ECDSAAdd.run_rename e e.injective (firstCoreModelOdd half divide) m s
  rw [firstCoreOdd_run half divide m] at a
  calc run (firstPacketOdd half divide) m s
      = pullState e.symm (pullState e (run (renameProgram e (firstCoreOdd half divide)) m s)) := (pull_symm _).symm
    _ = pullState e.symm (pullState e (run (renameProgram e (firstCoreModelOdd half divide)) m s)) := by rw [a.trans b.symm]
    _ = run (firstPacketModelOdd half divide) m s := pull_symm _

/-! ### Top-level semantic theorems -/

theorem firstPacketOdd_cut_frame (half : Bool → Program) (divide : Bool) (cut : Nat)
    (law : OddHalfLaw (half divide) divide) (hsup : OddHalfSupport (half divide))
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (x : Nat) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)))
    (X Y : Fp) (hz : FirstZero.FirstHyp divide origin X Y) :
    StateTriple (CutFrameOdd oddWord (firstYIn divide) cut origin X Y)
      (firstPacketOdd half divide)
      (fun state => let V := Replay5.firstPayload divide origin (X, Y)
        CutFrameOdd oddWord (firstYOut divide) cut origin V.1 V.2 state) := by
  intro state records input
  rw [firstPacketOdd_run half divide records state]
  exact firstPacketModelOdd_cut_frame half divide cut law hsup origin ctx enabled x hx trace X Y hz state records input

theorem firstPacketOdd_frame (half : Bool → Program) (divide isA : Bool)
    (law : OddHalfLaw (half divide) divide) (hsup : OddHalfSupport (half divide))
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (x : Nat) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)))
    (X Y : Fp) (hz : FirstZero.FirstHyp divide origin X Y) :
    StateTriple (EncodedFieldFrame5Odd oddWord (firstYIn divide) isA origin X Y)
      (firstPacketOdd half divide)
      (fun state => let V := Replay5.firstPayload divide origin (X, Y)
        EncodedFieldFrame5Odd oddWord (firstYOut divide) isA origin V.1 V.2 state) := by
  intro state records input
  cases isA
  · have h1 : CutFrameOdd oddWord (firstYIn divide) 102 origin X Y state := by
      simpa only [CutFrameOdd, CodeFrameOdd, EncodedFieldFrame5Odd, allEncodeCut_end base 102 (Nat.le_refl _)] using input
    have res := firstPacketOdd_cut_frame half divide 102 law hsup origin ctx enabled x hx trace X Y hz state records h1
    refine ⟨res.1, ?_⟩
    simpa only [CutFrameOdd, CodeFrameOdd, EncodedFieldFrame5Odd, allEncodeCut_end base 102 (Nat.le_refl _)] using res.2
  · have h1 : CutFrameOdd oddWord (firstYIn divide) 1 origin X Y state := by
      simpa only [CutFrameOdd, CodeFrameOdd, EncodedFieldFrame5Odd, allEncodeCut_one] using input
    have res := firstPacketOdd_cut_frame half divide 1 law hsup origin ctx enabled x hx trace X Y hz state records h1
    refine ⟨res.1, ?_⟩
    simpa only [CutFrameOdd, CodeFrameOdd, EncodedFieldFrame5Odd, allEncodeCut_one] using res.2

theorem placedFirstPacketOdd_frame (half : Bool → Program) (divide isA : Bool)
    (law : OddHalfLaw (half divide) divide) (hsup : OddHalfSupport (half divide))
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (x : Nat) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)))
    (X Y : Fp) (hz : FirstZero.FirstHyp divide origin X Y) :
    StateTriple (EncodedFieldFrameOdd oddWord (firstYIn divide) isA origin X Y)
      (placedFirstPacketOdd half divide)
      (fun state => let V := Replay5.firstPayload divide origin (X, Y)
        EncodedFieldFrameOdd oddWord (firstYOut divide) isA origin V.1 V.2 state) := by
  intro state records input
  have res := firstPacketOdd_frame half divide isA law hsup origin ctx enabled x hx trace X Y hz
    (pullState (OB5.sig 511) state) records input
  have same := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
    (firstPacketOdd half divide) records state
  rw [← same] at res
  exact res

/-- The hosted odd-word first packet runs identically to `placedFirstPacketOdd` whenever all
44 exclusive roles and hosts are zero before and the roles return to zero after. -/
theorem hostedFirstPacketOdd_run_eq (half : Bool → Program) (divide : Bool)
    (hsup : OddHalfSupport (half divide)) (m : List Bool) (s : State)
    (hrolesIn : ∀ q ∈ StairSchedule.exclusiveRoles, s.basis q = false)
    (hhostsIn : ∀ q ∈ StairV3Primitives.hostPlan.firstPacket divide, s.basis q = false)
    (hrolesOut : ∀ q ∈ StairSchedule.exclusiveRoles,
      (run (placedFirstPacketOdd half divide) m s).basis q = false) :
    run (hostedFirstPacketOdd half divide) m s = run (placedFirstPacketOdd half divide) m s := by
  apply StairLoan.rebindMany_run
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact hrolesIn q h
    · exact hhostsIn q h
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact hrolesOut q h
    · exact (run_preserves_outside _ m s q (placedFirstPacketOdd_hostsFree half divide hsup q h)).trans
        (hhostsIn q h)

end ECDSAAdd.Entrant.JointOdd1588
end

end
-- ==== end OddFirstPacket ====

-- ==== begin OddFullPass ====
section

/-!
# Odd-word tail arithmetic and endpoint converters

Extends the odd-word half-cell (`oddWord`) through the loaned staircase tail
(packets `85..101`), the division and multiplication endpoints, and the
halving/canonical converters (`canon760OddLoan` / `center760OddLoan`).

Includes three zero-overhead clean-wire hostings inside the existing 1,543-qubit
envelope:
1. `P1LifeLoan.shortConstAddLoan`: hosts 5 (resp. 4 at depth 43, where `base 763`
   is already unused) retired carry roles in clean unused cell wires
   `[base 763, base 764, base 1540, base 768, base 1027]`, reducing the short
   constant-add depth from `d` to `d - 5` on all 170 tail cells (−850 T / −850 M).
2. `HalfConvertOdd`: hosts all 43 `canonRoles` on clean `Y[3..45]` (`base 773..815`),
   dropping both `canon760OddLoan` and `center760OddLoan` from depth 43 to depth 0
   (−86 T / −86 M).
3. `CompareDecoderOdd`: hosts all 44 `exclusiveHoles` on already-erased `R[13..56]`
   during `window760Odd 0`, dropping `cellDecoderOddLoan` from depth 44 to depth 0
   (−44 T / −44 M, −266 slots).
-/

-- ============================================================================
-- Section 1: Odd-word representation core (matches `P1Life.oddWord` by `rfl`)
-- ============================================================================
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.OddFullPass
open Arithmetic Challenge BalancedField Secp256k1

def OddDomain (R : Int) : Prop := -q - 1 ≤ R ∧ R ≤ q - 1

def oddRep (x : Fp) : Int :=
  let z := centerFp x
  if z < 0 then z + q else z - q - 1

def oddWord (x : Fp) : Nat := encodeWord 256 (oddRep x)

def oddDecode (R : Int) : Fp := (R : Fp) + 1 / 2

theorem two_ne_zero : (2 : Fp) ≠ 0 := by decide

theorem q_field : (q : Fp) + 1 / 2 = 0 := by
  have eq := congrArg (fun z : Int => (z : Fp)) constants.2.1
  have qp : (2 : Fp) * (q : Fp) + 1 = 0 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, ZMod.natCast_self] using eq.symm
  apply mul_left_cancel₀ two_ne_zero
  calc
    (2 : Fp) * ((q : Fp) + 1 / 2) = 2 * (q : Fp) + 1 := by field_simp [two_ne_zero]
    _ = 2 * 0 := by simpa using qp

theorem oddRep_bounds (x : Fp) : OddDomain (oddRep x) := by
  have hz := centerFp_bounds x
  unfold Centered at hz
  dsimp only [oddRep, OddDomain]
  split_ifs <;> omega

theorem oddRep_field (x : Fp) : oddDecode (oddRep x) = x := by
  have hq := q_field
  dsimp only [oddDecode, oddRep]
  split_ifs
  · push_cast
    rw [add_assoc, hq, add_zero, centerFp_cast]
  · push_cast
    calc
      (centerFp x : Fp) - (q : Fp) - 1 + 1 / 2 = (centerFp x : Fp) := by
        field_simp [two_ne_zero] at hq ⊢
        linear_combination -hq
      _ = x := centerFp_cast x

theorem oddDomain_unique (R T : Int) (hr : OddDomain R) (ht : OddDomain T)
    (eq : oddDecode R = oddDecode T) : R = T := by
  have fieldEq : ((R + 1 : Int) : Fp) = ((T + 1 : Int) : Fp) := by
    simp only [oddDecode] at eq
    push_cast
    linear_combination eq
  have u := centered_cast_unique (R + 1) (T + 1)
    (by unfold OddDomain at hr; unfold Centered; omega)
    (by unfold OddDomain at ht; unfold Centered; omega) fieldEq
  omega

theorem oddRep_inverse (R : Int) (hr : OddDomain R) : oddRep (oddDecode R) = R :=
  oddDomain_unique _ _ (oddRep_bounds _) hr (oddRep_field _)

theorem rebindMany_slots (roles hosts : List Wire) (P : Program) :
    gateSlots (StairLoan.rebindMany roles hosts P) = gateSlots P := by
  induction roles generalizing hosts with
  | nil => rfl
  | cons r roles ih =>
    cases hosts with
    | nil => rfl
    | cons h hosts =>
      simp only [StairLoan.rebindMany, ECDSAAdd.Baselines.rename_gateSlots, ih]

/-- Every non-retired carry in `cs` (when `cs.Nodup`) appears in `wires (StairLoan.mappedAddLoan d ...)`. -/
theorem carry_in_mappedAddLoan (d : Nat) (roles : List Wire) (bits : List MappedBit)
    (ys cs : List Wire) (cin : Wire) (hb : bits.length = ys.length) (hc : cs.length + 1 = ys.length)
    (_hd : d ≤ cs.length) (hcsNd : cs.Nodup) :
    ∀ q ∈ cs, q ∉ roles.take d → q ∈ wires (StairLoan.mappedAddLoan d roles bits ys cs cin) := by
  intro q hq hnr
  have hhost : ∀ ls : List StairLoan.CarryLayer, (∀ l ∈ ls, l.host ∈ wires l.up) →
      ∀ l ∈ ls, l.host ∈ wires (StairLoan.emitUps ls) := by
    intro ls hu l hl
    induction ls with
    | nil => simp at hl
    | cons x xs ih =>
      simp only [StairLoan.emitUps, wires_append, Finset.mem_union]
      rcases List.mem_cons.mp hl with rfl | hl
      · exact Or.inl (hu _ (by simp))
      · exact Or.inr (ih (fun y hy => hu y (by simp [hy])) hl)
  have hml : ∀ (bs : List MappedBit) (ys' cs' : List Wire) (c0 : Wire),
      bs.length = ys'.length → cs'.length + 1 = ys'.length →
      (StairLoan.layerHosts (StairLoan.mappedLayers bs ys' cs' c0) = cs') ∧
      (∀ l ∈ StairLoan.mappedLayers bs ys' cs' c0, l.host ∈ wires l.up) := by
    intro bs; induction bs with
    | nil => intro ys' cs' c0 hb' hc'; cases ys' <;> cases cs' <;> simp at hb' hc'
    | cons b bs ih =>
      intro ys' cs' c0 hb' hc'
      cases bs with
      | nil =>
        cases ys' with
        | nil => simp at hb'
        | cons y ys' =>
          cases ys' with
          | nil => cases cs' <;> simp [StairLoan.mappedLayers, StairLoan.layerHosts] at hc' ⊢
          | cons _ _ => simp at hb'
      | cons b' bs' =>
        cases ys' with
        | nil => simp at hb'
        | cons y ys' =>
          cases ys' with
          | nil => simp at hb'
          | cons y' ys'' =>
            cases cs' with
            | nil => simp at hc'
            | cons c cs'' =>
              simp only [List.length_cons] at hb' hc'
              have hr := ih (y' :: ys'') cs'' c (by simp; omega) (by simp; omega)
              have hr1 := hr.1; unfold StairLoan.layerHosts at hr1
              refine ⟨by simp [StairLoan.mappedLayers, StairLoan.layerHosts, hr1], ?_⟩
              intro l hl
              simp only [StairLoan.mappedLayers, List.mem_cons] at hl
              rcases hl with rfl | hl
              · cases b with
                | mk bw bf =>
                  cases bw <;> cases bf <;> simp [mappedMajority, majority, borrowMajority, wires, Instr.wires]
              · exact hr.2 l hl
  have hinf := hml bits ys cs cin hb hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (hinf.1.symm ▸ hq)
  unfold StairLoan.mappedAddLoan StairLoan.emitLoan
  have hsplit : StairLoan.mappedLayers bits ys cs cin =
      (StairLoan.mappedLayers bits ys cs cin).take (d + 1) ++ (StairLoan.mappedLayers bits ys cs cin).drop (d + 1) :=
    (List.take_append_drop (d + 1) _).symm
  have hl' : l ∈ (StairLoan.mappedLayers bits ys cs cin).take (d + 1) ∨
      l ∈ (StairLoan.mappedLayers bits ys cs cin).drop (d + 1) := by
    rw [← List.mem_append, ← hsplit]; exact hl
  rcases hl' with hpre | hsuf
  · simp only [wires_append, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl (hhost _ (fun x hx => hinf.2 x (List.mem_of_mem_take hx)) l hpre))))
  · have hnotinHosts : l.host ∉ StairLoan.layerHosts ((StairLoan.mappedLayers bits ys cs cin).take d) := by
      intro bad
      have hndH : (StairLoan.layerHosts (StairLoan.mappedLayers bits ys cs cin)).Nodup := by
        rw [hinf.1]; exact hcsNd
      rw [hsplit] at hndH
      rw [StairLoan.layerHosts, List.map_append] at hndH
      have h1 : l.host ∈ ((StairLoan.mappedLayers bits ys cs cin).take (d + 1)).map StairLoan.CarryLayer.host :=
        ((List.take_sublist_take_left (Nat.le_succ d)).map _).subset bad
      have h2 : l.host ∈ ((StairLoan.mappedLayers bits ys cs cin).drop (d + 1)).map StairLoan.CarryLayer.host :=
        List.mem_map.mpr ⟨l, hsuf, rfl⟩
      exact (List.nodup_append'.mp hndH).2.2 h1 h2
    have hfix : ∀ rs hs P, l.host ∉ rs → l.host ∉ hs → l.host ∈ wires P →
        l.host ∈ wires (StairLoan.rebindMany rs hs P) := by
      intro rs; induction rs with
      | nil => intro hs P _ _ hp; exact hp
      | cons r rs ih =>
        intro hs P hr hh hp
        cases hs with
        | nil => exact hp
        | cons hh0 hs =>
          simp only [List.mem_cons, not_or] at hr hh
          simp only [StairLoan.rebindMany, renameProgram_support]
          exact Finset.mem_image.mpr ⟨l.host, ih hs P hr.2 hh.2 hp, Equiv.swap_apply_of_ne_of_ne hr.1 hh.1⟩
    simp only [wires_append, Finset.mem_union]
    refine Or.inl (Or.inl (Or.inr (hfix _ _ _ hnr hnotinHosts ?_)))
    simp only [StairLoan.emitSweep, wires_append, Finset.mem_union]
    exact Or.inl (Or.inl (hhost _ (fun x hx => hinf.2 x (List.mem_of_mem_drop hx)) l hsuf))

def correctionWiresList : Correction → List Wire
  | .Z q => [q]
  | .CZ a b => [a, b]

def instrWiresList : Instr → List Wire
  | .X a => [a]
  | .CX a b => [a, b]
  | .CCX a b c => [a, b, c]
  | .measureX a b c => a :: (b.flatMap correctionWiresList ++ c.flatMap correctionWiresList)

theorem mem_correctionWires_flatMap (bs : List Correction) (q : Wire) :
    q ∈ bs.flatMap correctionWiresList ↔ q ∈ correctionWires bs := by
  induction bs with
  | nil => simp [correctionWires]
  | cons c bs ih =>
    cases c <;> simp [correctionWires, correctionWiresList, ih, or_assoc]

theorem mem_instrWiresList_iff (i : Instr) (q : Wire) :
    q ∈ instrWiresList i ↔ q ∈ Instr.wires i := by
  cases i with
  | X a => simp [Instr.wires, instrWiresList]
  | CX a b => simp [Instr.wires, instrWiresList]
  | CCX a b c => simp [Instr.wires, instrWiresList]
  | measureX a b c =>
    simp only [Instr.wires, instrWiresList, Finset.mem_union, Finset.mem_singleton,
      List.mem_cons, List.mem_append, mem_correctionWires_flatMap]
    tauto

theorem mem_wires_iff_flatMap (P : Program) (q : Wire) :
    q ∈ wires P ↔ q ∈ P.flatMap instrWiresList := by
  induction P with
  | nil => simp [wires]
  | cons g P ih =>
    simp only [wires, Finset.mem_union, List.flatMap_cons, List.mem_append,
      mem_instrWiresList_iff, ih]

theorem rebindMany_wires_sub (rs hs : List Wire) (P : Program) :
    wires (StairLoan.rebindMany rs hs P) ⊆ wires P ∪ rs.toFinset ∪ hs.toFinset := by
  induction rs generalizing hs with
  | nil => intro q hq; simp [StairLoan.rebindMany] at hq; exact Finset.mem_union_left _ (Finset.mem_union_left _ hq)
  | cons r rs ih =>
    cases hs with
    | nil => intro q hq; simp [StairLoan.rebindMany] at hq; exact Finset.mem_union_left _ (Finset.mem_union_left _ hq)
    | cons hh hs =>
      intro q hq
      simp only [StairLoan.rebindMany, renameProgram_support] at hq
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
      by_cases hvr : v = r
      · subst hvr; rw [Equiv.swap_apply_left]; simp
      · by_cases hvh : v = hh
        · subst hvh; rw [Equiv.swap_apply_right]; simp
        · rw [Equiv.swap_apply_of_ne_of_ne hvr hvh]
          have h := ih hs hv
          simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons] at h ⊢
          tauto

end ECDSAAdd.Entrant.OddFullPass
end

-- ============================================================================
-- Section 2: Odd-word halving & canonical converters (`HalfConvertOdd`)
--   Hosts all 43 `canonRoles` on clean `Y[3..45]` (`wireBlock base 773 43`),
--   eliminating all 43 + 43 = 86 loan Toffolis and measurements.
-- ============================================================================
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

set_option linter.constructorNameAsVariable false
namespace ECDSAAdd.Entrant.OddFullPass.HalfConvertOdd
open Arithmetic Challenge RecordedQuantum MappedCompressed Secp256k1 BalancedField BalancedConvert
open StairBoundaryLoan OddFullPass

/-- `2^256 - (q + 1) = 2^255 + 2^31 + 488`, the two's-complement offset for
    converting canonical `u` to `oddWord (u / 2)` when `u` is even. -/
def halfCOdd : Nat := 2 ^ 255 + 2 ^ 31 + 488

/-- The 43 clean `Y`-register hosts (`base 773..815`) available during both
    `canon760OddLoan` (after `copyN` zeroes `Y`) and `center760OddLoan` (`Y = 0`). -/
def yHosts43 : List Wire := wireBlock base 773 43

def lowCorrectionOdd (L : BalancedConvert.Layout) : List MappedBit :=
  (List.range 255).map fun i =>
    { wire := if halfCOdd.testBit i then some L.flag else none, flip := false }

/-- Canonical `u` to `oddWord (u / 2)`. -/
def centerOdd (L : BalancedConvert.Layout) : Program :=
  [.CX (HalfConvert.lowBit L) L.flag, .CX L.flag (HalfConvert.lowBit L)] ++
    rotateRight L.word ++ [.X L.flag] ++
    mappedAdd (lowCorrectionOdd L) L.low (L.carry.take 254) L.cin ++
    [.CX L.flag L.msb, .CX L.msb L.flag]

/-- `oddWord (u / 2)` to canonical `u`: exact inverse of `centerOdd`. -/
def canonicalOdd (L : BalancedConvert.Layout) : Program :=
  [.CX L.msb L.flag, .CX L.flag L.msb] ++
    mappedSub (lowCorrectionOdd L) L.low (L.carry.take 254) L.cin ++
    [.X L.flag] ++ rotateLeft L.word ++
    [.CX L.flag (HalfConvert.lowBit L), .CX (HalfConvert.lowBit L) L.flag]

/-- Depth-0 odd-word converters with all 43 `canonRoles` hosted on clean `yHosts43`. -/
def canon760OddLoan : Program :=
  StairLoan.rebindMany canonRoles yHosts43 (canonicalOdd converterLayout760)

def center760OddLoan : Program :=
  StairLoan.rebindMany canonRoles yHosts43 (centerOdd converterLayout760)

theorem lowCorrectionOdd_length (L : BalancedConvert.Layout) :
    (lowCorrectionOdd L).length = 255 := by
  simp [lowCorrectionOdd]

private theorem correctionOdd_list (is : List Nat) (L : BalancedConvert.Layout) (s : BasisState) :
    mappedValue (is.map (fun i =>
      ({ wire := if halfCOdd.testBit i then some L.flag else none, flip := false } : MappedBit))) s =
    is.foldr (fun i n => (if halfCOdd.testBit i then s L.flag else false).toNat + 2 * n) 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, mappedValue, List.foldr_cons, ih]
    cases hi : halfCOdd.testBit i <;> simp [MappedBit.value, hi]

private def lowVirtualOdd (b : Bool) : Nat :=
  (List.range 255).foldr (fun i n => (if halfCOdd.testBit i then b else false).toNat + 2 * n) 0

private theorem lowVirtualOdd_value (b : Bool) :
    lowVirtualOdd b = if b then 2147484136 else 0 := by
  cases b <;> decide

theorem lowCorrectionOdd_value (L : BalancedConvert.Layout) (s : BasisState) :
    mappedValue (lowCorrectionOdd L) s = if s L.flag then 2147484136 else 0 := by
  rw [lowCorrectionOdd, correctionOdd_list]
  exact lowVirtualOdd_value _

theorem lowCorrectionOdd_sources (L : BalancedConvert.Layout) (w : Wire)
    (hw : w ∈ mappedWires (lowCorrectionOdd L)) : w = L.flag := by
  obtain ⟨b, hb, hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
  cases hf : halfCOdd.testBit i
  · simp [hf] at hw
  · simpa [hf] using hw

private theorem p_eq :
    p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [p]

private theorem q_eq :
    q = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by
  norm_num [q, p]

private theorem pow255_eq :
    (2 : Nat) ^ 255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
  norm_num

private theorem pow256_eq :
    (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  norm_num

/-- Arithmetic core of odd-word halving: `oddWord (x / 2)` is `(x / 2)` when `x` is odd,
    and `2^255 + (x / 2 + 2147484136)` when `x` is even. -/
theorem oddWord_half (x : Fp) :
    oddWord (x / 2) =
      (x.val / 2 + (if x.val % 2 = 0 then 2147484136 else 0)) % 2 ^ 255 +
        2 ^ 255 * (decide (x.val % 2 = 0)).toNat := by
  have hv : x.val < p := ZMod.val_lt x
  have hhalf := HalfConvert.half_val x
  have hp := p_eq
  have hq := q_eq
  have h255 := pow255_eq
  have h256 := pow256_eq
  unfold oddWord oddRep
  have hcenter : centerFp (x / 2) =
      if x.val % 2 = 0 then ((x.val / 2 : Nat) : Int) else ((x.val / 2 : Nat) : Int) - q := by
    unfold centerFp
    rw [hhalf]
    by_cases he : x.val % 2 = 0
    · rw [if_pos he, if_pos he]
      have hle : ((x.val / 2 : Nat) : Int) ≤ q := by omega
      simp only [hle, if_true]
    · rw [if_neg he, if_neg he]
      have hgt : ¬ (((x.val + p) / 2 : Nat) : Int) ≤ q := by omega
      simp only [hgt, if_false]
      omega
  rw [hcenter]
  by_cases he : x.val % 2 = 0
  · rw [if_pos he]
    have hnn : ¬ (((x.val / 2 : Nat) : Int) < 0) := by omega
    rw [if_neg hnn]
    have enc := BalancedFold.encode_shift 256 (((x.val / 2 : Nat) : Int) - q - 1) (by omega)
    have hneg : ((x.val / 2 : Nat) : Int) - q - 1 < 0 := by omega
    rw [if_pos hneg] at enc
    have hsmall : x.val / 2 + 2147484136 < 2 ^ 255 := by omega
    simp only [he, if_true, decide_true, Bool.toNat_true, Nat.mul_one, Nat.mod_eq_of_lt hsmall]
    omega
  · rw [if_neg he]
    have hlt : ((x.val / 2 : Nat) : Int) - q < 0 := by omega
    rw [if_pos hlt]
    have hsimp : ((x.val / 2 : Nat) : Int) - q + q = ((x.val / 2 : Nat) : Int) := by omega
    rw [hsimp]
    have enc := BalancedFold.encode_shift 256 ((x.val / 2 : Nat) : Int) (by omega)
    have hnn : ¬ (((x.val / 2 : Nat) : Int) < 0) := by omega
    rw [if_neg hnn] at enc
    have hsmall : x.val / 2 < 2 ^ 255 := by omega
    simp only [he, if_false, decide_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
      Nat.mod_eq_of_lt hsmall]
    omega

private theorem testBit_tail_eq :
    ∀ i ∈ List.range' 1 254, halfCOdd.testBit i = HalfConvert.halfC.testBit i := by
  have h : (List.range' 1 254).all (fun i => halfCOdd.testBit i == HalfConvert.halfC.testBit i) = true := by
    decide +kernel
  intro i hi
  exact beq_iff_eq.mp (List.all_eq_true.mp h i hi)

theorem lowCorrectionOdd_cons (L : BalancedConvert.Layout) :
    lowCorrectionOdd L = { wire := none, flip := false } :: (HalfConvert.lowCorrection L).tail := by
  have hrange : List.range 255 = 0 :: List.range' 1 254 := by decide
  have hb0Odd : halfCOdd.testBit 0 = false := by decide
  have hb0Std : HalfConvert.halfC.testBit 0 = true := by decide
  simp only [lowCorrectionOdd, HalfConvert.lowCorrection, hrange, List.map_cons, List.tail_cons,
    hb0Odd, hb0Std, Bool.false_eq_true, if_false, if_true]
  refine congrArg (_ :: ·) (List.map_congr_left (fun i hi => by simp only [testBit_tail_eq i hi]))

theorem lowCorrection_cons (L : BalancedConvert.Layout) :
    HalfConvert.lowCorrection L = { wire := some L.flag, flip := false } :: (HalfConvert.lowCorrection L).tail := by
  have hrange : List.range 255 = 0 :: List.range' 1 254 := by decide
  have hb0Std : HalfConvert.halfC.testBit 0 = true := by decide
  simp only [HalfConvert.lowCorrection, hrange, List.map_cons, List.tail_cons, hb0Std, if_true]

/-- Depth-0 counts: 254 T and 254 M (saving 43 T and 43 M over `canon760Loan` / `center760Loan`). -/
theorem canon760OddLoan_counts :
    toffoliCount canon760OddLoan = 254 ∧ measurementCount canon760OddLoan = 254 := by
  have len := converterLayout760_facts.widths
  have msub := mappedSub_counts (lowCorrectionOdd converterLayout760) converterLayout760.low
    (converterLayout760.carry.take 254) converterLayout760.cin
    (by rw [lowCorrectionOdd_length, len.1]) (by simp [List.length_take, len.1, len.2])
  have rot := rotate_counts converterLayout760.word
  have rc := StairLoan.rebindMany_counts canonRoles yHosts43 (canonicalOdd converterLayout760)
  rw [canon760OddLoan, rc.1, rc.2]
  simp only [canonicalOdd, toffoliCount_append, measurementCount_append, msub.1, msub.2,
    rot.2.2.1, rot.2.2.2, len.1]
  have h1 : toffoliCount ([Instr.CX converterLayout760.msb converterLayout760.flag,
      Instr.CX converterLayout760.flag converterLayout760.msb] : Program) = 0 ∧
      measurementCount ([Instr.CX converterLayout760.msb converterLayout760.flag,
      Instr.CX converterLayout760.flag converterLayout760.msb] : Program) = 0 := ⟨rfl, rfl⟩
  have h2 : toffoliCount ([Instr.X converterLayout760.flag] : Program) = 0 ∧
      measurementCount ([Instr.X converterLayout760.flag] : Program) = 0 := ⟨rfl, rfl⟩
  have h3 : toffoliCount ([Instr.CX converterLayout760.flag (HalfConvert.lowBit converterLayout760),
      Instr.CX (HalfConvert.lowBit converterLayout760) converterLayout760.flag] : Program) = 0 ∧
      measurementCount ([Instr.CX converterLayout760.flag (HalfConvert.lowBit converterLayout760),
      Instr.CX (HalfConvert.lowBit converterLayout760) converterLayout760.flag] : Program) = 0 := ⟨rfl, rfl⟩
  omega

theorem center760OddLoan_counts :
    toffoliCount center760OddLoan = 254 ∧ measurementCount center760OddLoan = 254 := by
  have len := converterLayout760_facts.widths
  have madd := mappedAdd_counts (lowCorrectionOdd converterLayout760) converterLayout760.low
    (converterLayout760.carry.take 254) converterLayout760.cin
    (by rw [lowCorrectionOdd_length, len.1]) (by simp [List.length_take, len.1, len.2])
  have rot := rotate_counts converterLayout760.word
  have rc := StairLoan.rebindMany_counts canonRoles yHosts43 (centerOdd converterLayout760)
  rw [center760OddLoan, rc.1, rc.2]
  simp only [centerOdd, toffoliCount_append, measurementCount_append, madd.1, madd.2,
    rot.1, rot.2.1, len.1]
  have h1 : toffoliCount ([Instr.CX (HalfConvert.lowBit converterLayout760) converterLayout760.flag,
      Instr.CX converterLayout760.flag (HalfConvert.lowBit converterLayout760)] : Program) = 0 ∧
      measurementCount ([Instr.CX (HalfConvert.lowBit converterLayout760) converterLayout760.flag,
      Instr.CX converterLayout760.flag (HalfConvert.lowBit converterLayout760)] : Program) = 0 := ⟨rfl, rfl⟩
  have h2 : toffoliCount ([Instr.X converterLayout760.flag] : Program) = 0 ∧
      measurementCount ([Instr.X converterLayout760.flag] : Program) = 0 := ⟨rfl, rfl⟩
  have h3 : toffoliCount ([Instr.CX converterLayout760.flag converterLayout760.msb,
      Instr.CX converterLayout760.msb converterLayout760.flag] : Program) = 0 ∧
      measurementCount ([Instr.CX converterLayout760.flag converterLayout760.msb,
      Instr.CX converterLayout760.msb converterLayout760.flag] : Program) = 0 := ⟨rfl, rfl⟩
  omega

private theorem mappedAdd_slots_le_loan (d : Nat) (roles : List Wire)
    (b0 b0' : MappedBit) (b1 : MappedBit) (bs' : List MappedBit) (y0 y1 : Wire) (ys : List Wire)
    (c0 : Wire) (cs : List Wire) (cin : Wire)
    (hd : 1 ≤ d)
    (hup : gateSlots (mappedMajority b0 y0 cin c0) + 3 ≤ gateSlots (mappedMajority b0' y0 cin c0))
    (her : gateSlots (mappedEraseCarry b0 y0 cin c0) + 2 ≤ gateSlots (mappedEraseCarry b0' y0 cin c0))
    (hsum : gateSlots (mappedSum b0 y0 cin) + 1 ≤ gateSlots (mappedSum b0' y0 cin)) :
    gateSlots (mappedAdd (b0 :: b1 :: bs') (y0 :: y1 :: ys) (c0 :: cs) cin) + 4 ≤
      gateSlots (StairLoan.mappedAddLoan d roles (b0' :: b1 :: bs') (y0 :: y1 :: ys) (c0 :: cs) cin) := by
  rw [StairLoan.mappedAdd_as_sweep]
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  have hsplit : ∀ ls : List StairLoan.CarryLayer, ∀ top : Program,
      gateSlots (StairLoan.emitSweep ls top) =
        gateSlots (StairLoan.emitUps (ls.take (d' + 2))) +
        gateSlots (StairLoan.emitSweep (ls.drop (d' + 2)) top) +
        gateSlots (StairLoan.emitDowns (ls.take (d' + 2))) := by
    intro ls top
    have hu : ∀ a b, gateSlots (StairLoan.emitUps (a ++ b)) =
        gateSlots (StairLoan.emitUps a) + gateSlots (StairLoan.emitUps b) := by
      intro a; induction a with
      | nil => intro b; simp [StairLoan.emitUps, gateSlots]
      | cons x xs ih => intro b; simp [StairLoan.emitUps, gateSlots_append, ih b]; omega
    have hd_app : ∀ a b, gateSlots (StairLoan.emitDowns (a ++ b)) =
        gateSlots (StairLoan.emitDowns a) + gateSlots (StairLoan.emitDowns b) := by
      intro a; induction a with
      | nil => intro b; simp [StairLoan.emitDowns, gateSlots]
      | cons x xs ih => intro b; simp [StairLoan.emitDowns, gateSlots_append, ih b]; omega
    have htd : ls = ls.take (d' + 2) ++ ls.drop (d' + 2) := (List.take_append_drop (d' + 2) ls).symm
    conv_lhs => rw [htd]
    simp only [StairLoan.emitSweep, hu, hd_app, gateSlots_append]
    omega
  have hs1 := hsplit (StairLoan.mappedLayers (b0 :: b1 :: bs') (y0 :: y1 :: ys) (c0 :: cs) cin)
    (StairLoan.mappedTop (b0 :: b1 :: bs') (y0 :: y1 :: ys) (c0 :: cs) cin)
  simp only [StairLoan.mappedAddLoan, StairLoan.mappedLayers, StairLoan.mappedTop,
    StairLoan.emitLoan, List.take_succ_cons, List.drop_succ_cons,
    StairLoan.emitUps, StairLoan.emitErases, StairLoan.emitDowns, StairLoan.CarryLayer.down,
    OddFullPass.rebindMany_slots, gateSlots_append] at hs1 ⊢
  omega

/-- Depth-0 odd converters save ≥ 3 slots over `center760Loan` / `canon760Loan`
    (in fact > 400 slots, enough to absorb the +2 slots of `endPacket760OddLoan44`). -/
theorem center760OddLoan_slots_le :
    gateSlots center760OddLoan + 3 ≤ gateSlots center760Loan := by
  have len := converterLayout760_facts.widths
  rcases hlow : converterLayout760.low with _ | ⟨y0, _ | ⟨y1, ys⟩⟩
  · have := len.1; rw [hlow] at this; simp at this
  · have := len.1; rw [hlow] at this; simp at this
  rcases hcar : converterLayout760.carry.take 254 with _ | ⟨c0, cs⟩
  · have : (converterLayout760.carry.take 254).length = 254 := by simp [List.length_take, len.2]
    rw [hcar] at this; simp at this
  rcases htail : (HalfConvert.lowCorrection converterLayout760).tail with _ | ⟨b1, bs'⟩
  · have hl := HalfConvert.lowCorrection_length converterLayout760
    rw [lowCorrection_cons, htail] at hl; simp [len.1] at hl
  have hbit := mappedAdd_slots_le_loan 43 canonRoles
    { wire := none, flip := false } { wire := some converterLayout760.flag, flip := false }
    b1 bs' y0 y1 ys c0 cs converterLayout760.cin
    (by decide)
    (by simp [mappedMajority, majority, gateSlots, instructionSlots])
    (by simp [mappedEraseCarry, eraseCarry, gateSlots, instructionSlots])
    (by simp [mappedSum, gateSlots, instructionSlots])
  rw [center760OddLoan, OddFullPass.rebindMany_slots]
  simp only [centerOdd, center760Loan, centerLoan, gateSlots_append]
  rw [lowCorrectionOdd_cons]
  conv_rhs => rw [lowCorrection_cons]
  rw [htail, hlow, hcar]
  have hx : gateSlots ([.X converterLayout760.flag] : Program) = 1 := rfl
  rw [hx]; omega

theorem canon760OddLoan_slots_le :
    gateSlots canon760OddLoan + 3 ≤ gateSlots canon760Loan := by
  have len := converterLayout760_facts.widths
  rcases hlow : converterLayout760.low with _ | ⟨y0, _ | ⟨y1, ys⟩⟩
  · have := len.1; rw [hlow] at this; simp at this
  · have := len.1; rw [hlow] at this; simp at this
  rcases hcar : converterLayout760.carry.take 254 with _ | ⟨c0, cs⟩
  · have : (converterLayout760.carry.take 254).length = 254 := by simp [List.length_take, len.2]
    rw [hcar] at this; simp at this
  rcases htail : (HalfConvert.lowCorrection converterLayout760).tail with _ | ⟨b1, bs'⟩
  · have hl := HalfConvert.lowCorrection_length converterLayout760
    rw [lowCorrection_cons, htail] at hl; simp [len.1] at hl
  have hbit := mappedAdd_slots_le_loan 43 canonRoles
    { wire := none, flip := false } { wire := some converterLayout760.flag, flip := false }
    b1 bs' y0 y1 ys c0 cs converterLayout760.cin
    (by decide)
    (by simp [mappedMajority, majority, gateSlots, instructionSlots])
    (by simp [mappedEraseCarry, eraseCarry, gateSlots, instructionSlots])
    (by simp [mappedSum, gateSlots, instructionSlots])
  rw [canon760OddLoan, OddFullPass.rebindMany_slots]
  simp only [canonicalOdd, canon760Loan, canonicalLoan, StairLoan.mappedSubLoan, mappedSub, gateSlots_append]
  rw [lowCorrectionOdd_cons]
  conv_rhs => rw [lowCorrection_cons]
  rw [htail, hlow, hcar]
  have hx : gateSlots ([.X converterLayout760.flag] : Program) = 1 := rfl
  rw [hx]; omega

private theorem lowOdd_bits_away :
    ∀ b ∈ lowCorrectionOdd converterLayout760, ∀ q ∈ b.wire,
      q ∉ converterLayout760.cin :: converterLayout760.low ++ converterLayout760.carry.take 254 := by
  intro b hb q hq
  have hqM : q ∈ mappedWires (lowCorrectionOdd converterLayout760) :=
    List.mem_flatMap.mpr ⟨b, hb, by cases bw : b.wire with | none => simp [bw] at hq | some w => simp [bw] at hq; subst hq; simp⟩
  rw [lowCorrectionOdd_sources _ q hqM]
  exact converterLayout760_facts.bitsAway _ (by
    apply List.mem_flatMap.mpr
    refine ⟨⟨some converterLayout760.flag, false⟩, ?_, by simp⟩
    rw [lowCorrection_cons]; exact List.mem_cons_self)

theorem canon760OddLoan_physical : GatePhysical canon760OddLoan := by
  have f := converterLayout760_facts
  have hnr : GatePhysical (notRegister converterLayout760.low) := by
    intro g hg; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hg; simp [PhysicalInstr, ProperGate]
  have ma : GatePhysical (mappedAdd (lowCorrectionOdd converterLayout760)
      converterLayout760.low (converterLayout760.carry.take 254) converterLayout760.cin) :=
    mappedAdd_physical _ _ _ _ f.nodup lowOdd_bits_away
  have ms : GatePhysical (mappedSub (lowCorrectionOdd converterLayout760)
      converterLayout760.low (converterLayout760.carry.take 254) converterLayout760.cin) := by
    simp only [mappedSub, gatePhysical_append]; exact ⟨⟨hnr, ma⟩, hnr⟩
  have hbase := StairBoundaryLoan.record_converters_physical.2
  rw [StairBoundaryLoan.canon760_eq] at hbase
  simp only [HalfConvert.canonical, gatePhysical_append] at hbase
  have hcore : GatePhysical (canonicalOdd converterLayout760) := by
    simp only [canonicalOdd, gatePhysical_append]
    exact ⟨⟨⟨⟨hbase.1.1.1, ms⟩, by simp [GatePhysical, PhysicalInstr, ProperGate]⟩, hbase.1.2⟩, hbase.2⟩
  exact StairLoan.rebindMany_physical canonRoles yHosts43 _ hcore

theorem center760OddLoan_physical : GatePhysical center760OddLoan := by
  have f := converterLayout760_facts
  have ma : GatePhysical (mappedAdd (lowCorrectionOdd converterLayout760)
      converterLayout760.low (converterLayout760.carry.take 254) converterLayout760.cin) :=
    mappedAdd_physical _ _ _ _ f.nodup lowOdd_bits_away
  have hbase := StairBoundaryLoan.record_converters_physical.1
  rw [StairBoundaryLoan.center760_eq] at hbase
  simp only [HalfConvert.center, gatePhysical_append] at hbase
  have hcore : GatePhysical (centerOdd converterLayout760) := by
    simp only [centerOdd, gatePhysical_append]
    exact ⟨⟨⟨⟨hbase.1.1.1, hbase.1.1.2⟩, by simp [GatePhysical, PhysicalInstr, ProperGate]⟩, ma⟩, hbase.2⟩
  exact StairLoan.rebindMany_physical canonRoles yHosts43 _ hcore

theorem yHosts43_in_copyN : ∀ q ∈ yHosts43, q ∈ wires HalfFieldOB5.copyN := by
  have h : yHosts43.all (fun q => decide (q ∈ HalfField.ports.y)) = true := by decide +kernel
  intro q hq
  have hy : q ∈ HalfField.ports.y := of_decide_eq_true (List.all_eq_true.mp h q hq)
  rw [show HalfFieldOB5.copyN = HalfField.copyN from rfl]
  unfold HalfField.copyN
  have hsub : ∀ xs ys : List Wire, xs.length = ys.length →
      ∀ w ∈ ys, w ∈ wires (copyRegister none xs ys) := by
    intro xs; induction xs with
    | nil => intro ys hlen w hw; cases ys <;> simp at hlen hw
    | cons x xs ih =>
      intro ys hlen w hw
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
        rcases List.mem_cons.mp hw with rfl | hw
        · simp [copyRegister, copyGate, wires, Instr.wires]
        · simp only [copyRegister, wires_append, Finset.mem_union]
          exact Or.inr (ih ys (by simp at hlen; omega) w hw)
  exact hsub _ _ (by decide) q hy

theorem yHosts43_disjoint :
    (canonRoles ++ yHosts43).Nodup ∧
    ∀ q ∈ yHosts43, q ∉ converterLayout760.wires := by
  refine ⟨PeakNodup.nodup_of_mask _ (by decide +kernel), ?_⟩
  have hnd : (yHosts43 ++ converterLayout760.wires).Nodup :=
    PeakNodup.nodup_of_mask _ (by decide +kernel)
  exact (List.nodup_append'.mp hnd).2.2

theorem rebindMany_wires_sub_erase (rs hs : List Wire) (P : Program)
    (hlen : rs.length = hs.length) (hnd : (rs ++ hs).Nodup)
    (havoid : ∀ q ∈ hs, q ∉ wires P) :
    wires (StairLoan.rebindMany rs hs P) ⊆ (wires P \ rs.toFinset) ∪ hs.toFinset := by
  induction rs generalizing hs with
  | nil =>
    cases hs with
    | nil => simp [StairLoan.rebindMany]
    | cons _ _ => simp at hlen
  | cons r rs ih =>
    cases hs with
    | nil => simp at hlen
    | cons hh hs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hnd' : (rs ++ hs).Nodup := hnd.sublist (List.Sublist.append
        (List.sublist_cons_self r rs) (List.sublist_cons_self hh hs))
      have hrNe : r ≠ hh := fun e => by
        subst e
        have := List.nodup_cons.mp hnd
        exact this.1 (by simp)
      have hrNotRs : r ∉ rs := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
      have hhNotRs : hh ∉ rs := fun h => by
        have hc := List.nodup_iff_count.mp hnd hh
        have c1 := List.count_pos_iff.mpr h
        simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at hc
        omega
      have hhNotHs : hh ∉ hs := fun h => by
        have hc := List.nodup_iff_count.mp hnd hh
        have c1 := List.count_pos_iff.mpr h
        simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at hc
        omega
      have hrNotHs : r ∉ hs := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
      intro q hq
      simp only [StairLoan.rebindMany, renameProgram_support] at hq
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
      have hv' := ih hs hlen hnd' (fun q hq => havoid q (by simp [hq])) hv
      simp only [Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, List.mem_cons, not_or] at hv' ⊢
      by_cases hvr : v = r
      · subst hvr; rw [Equiv.swap_apply_left]; exact Or.inr (Or.inl rfl)
      · by_cases hvh : v = hh
        · subst hvh
          rcases hv' with ⟨hvp, _⟩ | hh'
          · exact absurd hvp (havoid v (by simp))
          · exact absurd hh' hhNotHs
        · rw [Equiv.swap_apply_of_ne_of_ne hvr hvh]
          rcases hv' with ⟨hvp, hvnr⟩ | hvh'
          · exact Or.inl ⟨hvp, ⟨hvr, hvnr⟩⟩
          · exact Or.inr (Or.inr hvh')

private theorem canonicalOdd_wires_sub_gen (L : BalancedConvert.Layout) (len : L.Widths) :
    wires (canonicalOdd L) ⊆ wires (HalfConvert.canonical L) := by
  rcases hlow : L.low with _ | ⟨y0, _ | ⟨y1, ys⟩⟩
  · have := len.1; rw [hlow] at this; simp at this
  · have := len.1; rw [hlow] at this; simp at this
  rcases hcar : L.carry.take 254 with _ | ⟨c0, cs⟩
  · have : (L.carry.take 254).length = 254 := by simp [List.length_take, len.2]
    rw [hcar] at this; simp at this
  have hsub : wires (mappedSub (lowCorrectionOdd L) L.low (L.carry.take 254) L.cin) ⊆
      wires (mappedSub (HalfConvert.lowCorrection L) L.low (L.carry.take 254) L.cin) := by
    rw [lowCorrectionOdd_cons]
    conv_rhs => rw [lowCorrection_cons]
    rw [hlow, hcar]
    cases hbs : (HalfConvert.lowCorrection L).tail with
    | nil => simp [mappedSub, mappedAdd]
    | cons b1 bs' =>
      intro x hx
      simp only [mappedSub, mappedAdd, wires_append, Finset.mem_union] at hx ⊢
      have hmaj : wires (mappedMajority { wire := none, flip := false } y0 L.cin c0) ⊆
          wires (mappedMajority { wire := some L.flag, flip := false } y0 L.cin c0) := by
        intro z hz; simp [mappedMajority, majority, wires, Instr.wires] at hz ⊢; tauto
      have her : wires (mappedEraseCarry { wire := none, flip := false } y0 L.cin c0) ⊆
          wires (mappedEraseCarry { wire := some L.flag, flip := false } y0 L.cin c0) := by
        intro z hz; simp [mappedEraseCarry, eraseCarry, wires, Instr.wires, correctionWires] at hz ⊢; tauto
      have hsm : wires (mappedSum { wire := none, flip := false } y0 L.cin) ⊆
          wires (mappedSum { wire := some L.flag, flip := false } y0 L.cin) := by
        intro z hz; simp [mappedSum, wires, Instr.wires] at hz ⊢; tauto
      tauto
  intro q hq
  simp only [canonicalOdd, HalfConvert.canonical, wires_append, Finset.mem_union] at hq ⊢
  rcases hq with (((h | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr (hsub h)))
  · have hf : q = L.flag := by simpa [wires, Instr.wires] using h
    subst hf; exact Or.inl (Or.inl (Or.inl (by simp [wires, Instr.wires])))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

private theorem centerOdd_wires_sub_gen (L : BalancedConvert.Layout) (len : L.Widths) :
    wires (centerOdd L) ⊆ wires (HalfConvert.center L) := by
  rcases hlow : L.low with _ | ⟨y0, _ | ⟨y1, ys⟩⟩
  · have := len.1; rw [hlow] at this; simp at this
  · have := len.1; rw [hlow] at this; simp at this
  rcases hcar : L.carry.take 254 with _ | ⟨c0, cs⟩
  · have : (L.carry.take 254).length = 254 := by simp [List.length_take, len.2]
    rw [hcar] at this; simp at this
  have hadd : wires (mappedAdd (lowCorrectionOdd L) L.low (L.carry.take 254) L.cin) ⊆
      wires (mappedAdd (HalfConvert.lowCorrection L) L.low (L.carry.take 254) L.cin) := by
    rw [lowCorrectionOdd_cons]
    conv_rhs => rw [lowCorrection_cons]
    rw [hlow, hcar]
    cases hbs : (HalfConvert.lowCorrection L).tail with
    | nil => simp [mappedAdd]
    | cons b1 bs' =>
      intro x hx
      simp only [mappedAdd, wires_append, Finset.mem_union] at hx ⊢
      have hmaj : wires (mappedMajority { wire := none, flip := false } y0 L.cin c0) ⊆
          wires (mappedMajority { wire := some L.flag, flip := false } y0 L.cin c0) := by
        intro z hz; simp [mappedMajority, majority, wires, Instr.wires] at hz ⊢; tauto
      have her : wires (mappedEraseCarry { wire := none, flip := false } y0 L.cin c0) ⊆
          wires (mappedEraseCarry { wire := some L.flag, flip := false } y0 L.cin c0) := by
        intro z hz; simp [mappedEraseCarry, eraseCarry, wires, Instr.wires, correctionWires] at hz ⊢; tauto
      have hsm : wires (mappedSum { wire := none, flip := false } y0 L.cin) ⊆
          wires (mappedSum { wire := some L.flag, flip := false } y0 L.cin) := by
        intro z hz; simp [mappedSum, wires, Instr.wires] at hz ⊢; tauto
      tauto
  intro q hq
  simp only [centerOdd, HalfConvert.center, wires_append, Finset.mem_union] at hq ⊢
  rcases hq with (((h | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · have hf : q = L.flag := by simpa [wires, Instr.wires] using h
    subst hf; exact Or.inr (by simp [wires, Instr.wires])
  · exact Or.inl (Or.inr (hadd h))
  · exact Or.inr h

private theorem canonical_wires_in_layout (L : BalancedConvert.Layout) (hw : L.Widths) :
    wires (HalfConvert.canonical L) ⊆ L.wires.toFinset := by
  intro q hsub
  rw [List.mem_toFinset]
  simp only [HalfConvert.canonical, wires_append, Finset.mem_union] at hsub
  rcases hsub with ((h | h) | h) | h
  · simp [wires, Instr.wires] at h
    rcases h with (rfl | rfl) | (rfl | rfl) <;> simp [BalancedConvert.Layout.wires, BalancedConvert.Layout.word]
  · have hm := mappedSub_wires_subset _ _ _ _ h
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with ((hsrc | hlow) | hcar) | rfl
    · obtain ⟨b, hb, hbw⟩ := List.mem_flatMap.mp hsrc
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      split_ifs at hbw <;> simp at hbw; subst hbw; simp [BalancedConvert.Layout.wires]
    · simp [BalancedConvert.Layout.wires, BalancedConvert.Layout.word, hlow]
    · simp [BalancedConvert.Layout.wires, List.mem_of_mem_take hcar]
    · simp [BalancedConvert.Layout.wires]
  · rw [(rotate_wires L.word).2, if_neg (by simp [BalancedConvert.Layout.word, hw.1])] at h
    have hqW : q ∈ L.word := List.mem_toFinset.mp h
    simp only [BalancedConvert.Layout.word, List.mem_append, List.mem_singleton] at hqW
    rcases hqW with hl | rfl
    · simp [BalancedConvert.Layout.wires, BalancedConvert.Layout.word, hl]
    · simp [BalancedConvert.Layout.wires, BalancedConvert.Layout.word]
  · simp [wires, Instr.wires] at h
    have hlb : HalfConvert.lowBit L ∈ L.low := by
      have hw1 := hw.1; cases hl : L.low with | nil => rw [hl] at hw1; simp at hw1 | cons a _ => simp [HalfConvert.lowBit, hl]
    rcases h with (rfl | rfl) | (rfl | rfl) <;> simp [BalancedConvert.Layout.wires, BalancedConvert.Layout.word, hlb]

private theorem center_wires_in_layout (L : BalancedConvert.Layout) (hw : L.Widths) :
    wires (HalfConvert.center L) ⊆ L.wires.toFinset := by
  intro q hsub
  rw [List.mem_toFinset]
  simp only [HalfConvert.center, wires_append, Finset.mem_union] at hsub
  rcases hsub with ((h | h) | h) | h
  · simp [wires, Instr.wires] at h
    have hlb : HalfConvert.lowBit L ∈ L.low := by
      have hw1 := hw.1; cases hl : L.low with | nil => rw [hl] at hw1; simp at hw1 | cons a _ => simp [HalfConvert.lowBit, hl]
    rcases h with (rfl | rfl) | (rfl | rfl) <;> simp [BalancedConvert.Layout.wires, BalancedConvert.Layout.word, hlb]
  · rw [(rotate_wires L.word).1, if_neg (by simp [BalancedConvert.Layout.word, hw.1])] at h
    have hqW : q ∈ L.word := List.mem_toFinset.mp h
    simp only [BalancedConvert.Layout.word, List.mem_append, List.mem_singleton] at hqW
    rcases hqW with hl | rfl
    · simp [BalancedConvert.Layout.wires, BalancedConvert.Layout.word, hl]
    · simp [BalancedConvert.Layout.wires, BalancedConvert.Layout.word]
  · have hm := mappedAdd_wires_subset _ _ _ _ h
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with ((hsrc | hlow) | hcar) | rfl
    · obtain ⟨b, hb, hbw⟩ := List.mem_flatMap.mp hsrc
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      split_ifs at hbw <;> simp at hbw; subst hbw; simp [BalancedConvert.Layout.wires]
    · simp [BalancedConvert.Layout.wires, BalancedConvert.Layout.word, hlow]
    · simp [BalancedConvert.Layout.wires, List.mem_of_mem_take hcar]
    · simp [BalancedConvert.Layout.wires]
  · simp [wires, Instr.wires] at h
    rcases h with (rfl | rfl) | (rfl | rfl) <;> simp [BalancedConvert.Layout.wires, BalancedConvert.Layout.word]

private theorem canonical_sdiff_sub_loan (L : BalancedConvert.Layout) (hw : L.Widths)
    (hcsNd : (L.carry.take 254).Nodup) (roles : List Wire) :
    wires (HalfConvert.canonical L) \ (roles.take 43).toFinset ⊆
      wires (canonicalLoan 43 roles L) := by
  intro x hx
  have hx' := Finset.mem_sdiff.mp hx
  simp only [HalfConvert.canonical, canonicalLoan, wires_append, Finset.mem_union] at hx' ⊢
  rcases hx'.1 with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · have hmw := mappedSub_wires_subset _ _ _ _ h
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmw
    rcases hmw with ((hsrc | hlow) | hcar) | rfl
    · have hf : x = L.flag := by
        obtain ⟨b, hb, hz⟩ := List.mem_flatMap.mp hsrc
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
        split_ifs at hz <;> simp at hz; exact hz
      subst hf; exact Or.inl (Or.inl (Or.inl (by simp [wires, Instr.wires])))
    · left; left; right
      simp only [StairLoan.mappedSubLoan, wires_append, Finset.mem_union]
      exact Or.inl (Or.inl (by rw [notRegister_wires]; exact List.mem_toFinset.mpr hlow))
    · left; left; right
      simp only [StairLoan.mappedSubLoan, wires_append, Finset.mem_union]
      exact Or.inl (Or.inr (OddFullPass.carry_in_mappedAddLoan 43 roles _ _ _ _
        (by rw [HalfConvert.lowCorrection_length, hw.1])
        (by simp [List.length_take, hw.1, hw.2])
        (by simp [List.length_take, hw.2]) hcsNd x hcar (List.mem_toFinset.not.mp hx'.2)))
    · left; left; right
      simp only [StairLoan.mappedSubLoan, wires_append, Finset.mem_union]
      refine Or.inl (Or.inr ?_)
      have h0 : L.low.length = 255 := hw.1
      have hc0 : (L.carry.take 254).length = 254 := by simp [List.length_take, hw.2]
      rcases hlow : L.low with _ | ⟨y0, _ | ⟨y1, ys⟩⟩ <;> try (rw [hlow] at h0; simp at h0)
      rcases hcar : L.carry.take 254 with _ | ⟨c0, cs⟩ <;> try (rw [hcar] at hc0; simp at hc0)
      rw [lowCorrection_cons]
      cases hbs : (HalfConvert.lowCorrection L).tail with
      | nil => have hl := HalfConvert.lowCorrection_length L; rw [lowCorrection_cons, hbs] at hl; simp [h0] at hl
      | cons b1 bs' =>
        simp only [StairLoan.mappedAddLoan, StairLoan.mappedLayers, StairLoan.emitLoan,
          List.take_succ_cons, StairLoan.emitUps, wires_append, Finset.mem_union]
        left; left; left; left; left
        simp [mappedMajority, majority, wires, Instr.wires]
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

private theorem center_sdiff_sub_loan (L : BalancedConvert.Layout) (hw : L.Widths)
    (hcsNd : (L.carry.take 254).Nodup) (roles : List Wire) :
    wires (HalfConvert.center L) \ (roles.take 43).toFinset ⊆
      wires (centerLoan 43 roles L) := by
  intro x hx
  have hx' := Finset.mem_sdiff.mp hx
  simp only [HalfConvert.center, centerLoan, wires_append, Finset.mem_union] at hx' ⊢
  rcases hx'.1 with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · have hmw := mappedAdd_wires_subset _ _ _ _ h
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmw
    rcases hmw with ((hsrc | hlow) | hcar) | rfl
    · have hf : x = L.flag := by
        obtain ⟨b, hb, hz⟩ := List.mem_flatMap.mp hsrc
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
        split_ifs at hz <;> simp at hz; exact hz
      subst hf; exact Or.inr (by simp [wires, Instr.wires])
    · left; left; right
      rw [(rotate_wires L.word).1, if_neg (by simp [BalancedConvert.Layout.word, hw.1])]
      exact List.mem_toFinset.mpr (by simp [BalancedConvert.Layout.word, hlow])
    · left; right
      exact OddFullPass.carry_in_mappedAddLoan 43 roles _ _ _ _
        (by rw [HalfConvert.lowCorrection_length, hw.1])
        (by simp [List.length_take, hw.1, hw.2])
        (by simp [List.length_take, hw.2]) hcsNd x hcar (List.mem_toFinset.not.mp hx'.2)
    · left; right
      have h0 : L.low.length = 255 := hw.1
      have hc0 : (L.carry.take 254).length = 254 := by simp [List.length_take, hw.2]
      rcases hlow : L.low with _ | ⟨y0, _ | ⟨y1, ys⟩⟩ <;> try (rw [hlow] at h0; simp at h0)
      rcases hcar : L.carry.take 254 with _ | ⟨c0, cs⟩ <;> try (rw [hcar] at hc0; simp at hc0)
      rw [lowCorrection_cons]
      cases hbs : (HalfConvert.lowCorrection L).tail with
      | nil => have hl := HalfConvert.lowCorrection_length L; rw [lowCorrection_cons, hbs] at hl; simp [h0] at hl
      | cons b1 bs' =>
        simp only [StairLoan.mappedAddLoan, StairLoan.mappedLayers, StairLoan.emitLoan,
          List.take_succ_cons, StairLoan.emitUps, wires_append, Finset.mem_union]
        left; left; left; left; left
        simp [mappedMajority, majority, wires, Instr.wires]
  · exact Or.inr h

attribute [local irreducible] wires

/-- Exact wire envelope: every wire of `canon760OddLoan` avoids `canonRoles` and
    lies inside `wires canon760Loan ∪ wires HalfFieldOB5.copyN`! -/
theorem canon760OddLoan_wires_sub :
    wires canon760OddLoan ⊆ wires canon760Loan ∪ wires HalfFieldOB5.copyN := by
  have havoid : ∀ q ∈ yHosts43, q ∉ wires (canonicalOdd converterLayout760) := fun q hq hw =>
    yHosts43_disjoint.2 q hq (List.mem_toFinset.mp (canonical_wires_in_layout converterLayout760 converterLayout760_facts.widths
      (canonicalOdd_wires_sub_gen converterLayout760 converterLayout760_facts.widths hw)))
  have h1 := rebindMany_wires_sub_erase canonRoles yHosts43 (canonicalOdd converterLayout760)
    (by simp [canonRoles_length, yHosts43, wireBlock, List.length_map, List.length_range']) yHosts43_disjoint.1 havoid
  have hcsNd : (converterLayout760.carry.take 254).Nodup :=
    PeakNodup.nodup_of_mask _ (by decide +kernel)
  have h2 := canonical_sdiff_sub_loan converterLayout760 converterLayout760_facts.widths hcsNd canonRoles
  have htake : canonRoles.take 43 = canonRoles := List.take_of_length_le (le_of_eq canonRoles_length)
  rw [htake] at h2
  intro q hq
  rw [canon760OddLoan] at hq
  rw [canon760Loan]
  rcases Finset.mem_union.mp (h1 hq) with h | hy
  · exact Finset.mem_union_left _ (by
      have hs := Finset.mem_sdiff.mp h
      exact h2 (Finset.mem_sdiff.mpr ⟨canonicalOdd_wires_sub_gen converterLayout760 converterLayout760_facts.widths hs.1, hs.2⟩))
  · exact Finset.mem_union_right _ (yHosts43_in_copyN q (List.mem_toFinset.mp hy))

theorem center760OddLoan_wires_sub :
    wires center760OddLoan ⊆ wires center760Loan ∪ wires HalfFieldOB5.copyN := by
  have havoid : ∀ q ∈ yHosts43, q ∉ wires (centerOdd converterLayout760) := fun q hq hw =>
    yHosts43_disjoint.2 q hq (List.mem_toFinset.mp (center_wires_in_layout converterLayout760 converterLayout760_facts.widths
      (centerOdd_wires_sub_gen converterLayout760 converterLayout760_facts.widths hw)))
  have h1 := rebindMany_wires_sub_erase canonRoles yHosts43 (centerOdd converterLayout760)
    (by simp [canonRoles_length, yHosts43, wireBlock, List.length_map, List.length_range']) yHosts43_disjoint.1 havoid
  have hcsNd : (converterLayout760.carry.take 254).Nodup :=
    PeakNodup.nodup_of_mask _ (by decide +kernel)
  have h2 := center_sdiff_sub_loan converterLayout760 converterLayout760_facts.widths hcsNd canonRoles
  have htake : canonRoles.take 43 = canonRoles := List.take_of_length_le (le_of_eq canonRoles_length)
  rw [htake] at h2
  intro q hq
  rw [center760OddLoan] at hq
  rw [center760Loan]
  rcases Finset.mem_union.mp (h1 hq) with h | hy
  · exact Finset.mem_union_left _ (by
      have hs := Finset.mem_sdiff.mp h
      exact h2 (Finset.mem_sdiff.mpr ⟨centerOdd_wires_sub_gen converterLayout760 converterLayout760_facts.widths hs.1, hs.2⟩))
  · exact Finset.mem_union_right _ (yHosts43_in_copyN q (List.mem_toFinset.mp hy))

/-- Clean-wire equivalence via `StairField13V3.rebindMany_run_eq_of_clean`. -/
theorem rebindMany_run_eq_of_clean (rs hs : List Wire) (P : Program)
    (_hlen : rs.length = hs.length) (_hnd : (rs ++ hs).Nodup)
    (havoid : ∀ q ∈ hs, q ∉ wires P)
    (s : State) (m : List Bool)
    (hrs : ∀ q ∈ rs, s.basis q = false)
    (hhs : ∀ q ∈ hs, s.basis q = false)
    (hrest : ∀ q ∈ rs, (run P m s).basis q = false) :
    run (StairLoan.rebindMany rs hs P) m s = run P m s :=
  StairField13V3.rebindMany_run_eq_of_clean rs hs P m s
    (fun q hq => (List.mem_append.mp hq).elim (hrs q) (hhs q))
    (fun q hq => (List.mem_append.mp hq).elim (hrest q)
      (fun hh => (run_preserves_outside P m s q (havoid q hh)).trans (hhs q hh)))

def convWork (L : BalancedConvert.Layout) : List Wire := L.flag :: L.cin :: L.carry.take 254

private theorem cx_swap_run (a b : Wire) (hab : a ≠ b) (s : State) (hb : s.basis b = false) :
    let t := run [.CX a b, .CX b a] [] s
    t.phase = s.phase ∧ t.basis b = s.basis a ∧ t.basis a = false ∧
    (∀ q, q ≠ a → q ≠ b → t.basis q = s.basis q) := by
  dsimp only
  simp only [run, writeBit, Function.update_apply]
  refine ⟨trivial, ?_, ?_, ?_⟩
  · simp [hab.symm, hb]
  · simp [hab, hb]
  · intro q qa qb; simp [qa, qb]

private theorem x_gate_run (a : Wire) (s : State) :
    let t := run [.X a] [] s
    t.phase = s.phase ∧ t.basis a = !s.basis a ∧ (∀ q, q ≠ a → t.basis q = s.basis q) := by
  have hx := BalancedCleanupOffset.x_run a s []
  refine ⟨by rw [hx], by rw [hx]; simp [writeBit], fun q qa => by rw [hx]; simp [writeBit, qa]⟩

private theorem work_not_word (L : BalancedConvert.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q ∈ convWork L) : q ∉ L.word := by
  intro hw
  have hc := List.nodup_iff_count.mp hn q
  have c1 := List.count_pos_iff.mpr hw
  have c2 : 0 < List.count q (L.flag :: L.cin :: L.carry) := by
    simp only [convWork, List.mem_cons] at hq
    rcases hq with rfl | rfl | hc'
    · exact List.count_pos_iff.mpr (by simp)
    · exact List.count_pos_iff.mpr (by simp)
    · exact List.count_pos_iff.mpr (by simp [List.mem_of_mem_take hc'])
  simp only [BalancedConvert.Layout.wires, BalancedConvert.Layout.word, List.count_cons,
    List.count_append] at hc c1 c2
  omega

/-- Semantic correctness of `centerOdd`: canonical `x.val` to `oddWord (x / 2)`. -/
theorem centerOdd_correct (L : BalancedConvert.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis = x.val)
    (hc : ∀ q ∈ convWork L, s.basis q = false) :
    let t := run (centerOdd L) m s
    t.phase = s.phase ∧ regValue L.word t.basis = oddWord (x / 2) ∧
    (∀ q ∈ convWork L, t.basis q = false) ∧ (∀ q, q ∉ L.word → t.basis q = s.basis q) := by
  have hxv : x.val < p := ZMod.val_lt x
  have hp := p_eq
  have h255 := pow255_eq
  have hflag : s.basis L.flag = false := hc _ (by simp [convWork])
  have hcin : s.basis L.cin = false := hc _ (by simp [convWork])
  have hnd : (L.flag :: L.cin :: (L.word ++ L.carry.take 254)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hc0 := List.nodup_iff_count.mp hn q
    simp only [BalancedConvert.Layout.wires, BalancedConvert.Layout.word, List.count_cons,
      List.count_append] at hc0 ⊢
    have htk := (List.take_sublist 254 L.carry).count_le q
    omega
  have hwnd : L.word.Nodup := (List.nodup_append'.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1
  have hflagWord : L.flag ∉ L.word := work_not_word L hn L.flag (by simp [convWork])
  have hmsbLow : L.msb ∉ L.low := by
    rw [BalancedConvert.Layout.word] at hwnd
    exact fun h => (List.nodup_append'.mp hwnd).2.2 h (by simp)
  have hfm : L.flag ≠ L.msb := fun e => hflagWord (by simp [BalancedConvert.Layout.word, e])
  rcases hlowS : L.low with _ | ⟨a, restLow⟩
  · have := hw.1; rw [hlowS] at this; contradiction
  have hlowBit : HalfConvert.lowBit L = a := by simp [HalfConvert.lowBit, hlowS]
  have hwordS : L.word = a :: (restLow ++ [L.msb]) := by simp [BalancedConvert.Layout.word, hlowS]
  have haWord : a ∈ L.word := by rw [hwordS]; simp
  have hfa : a ≠ L.flag := fun e => hflagWord (e ▸ haWord)
  have haRest : a ∉ restLow ++ [L.msb] := by
    rw [hwordS] at hwnd; exact (List.nodup_cons.mp hwnd).1
  let st1 := run [.CX a L.flag, .CX L.flag a] [] s
  let st2 := run (rotateRight L.word) [] st1
  let st2x := run [.X L.flag] [] st2
  let st3 := run (mappedAdd (lowCorrectionOdd L) L.low (L.carry.take 254) L.cin) m st2x
  let st4 := run [.CX L.flag L.msb, .CX L.msb L.flag] [] st3
  have hrun : run (centerOdd L) m s = st4 := by
    have hmc4 : measurementCount [.CX L.flag L.msb, .CX L.msb L.flag] = 0 := rfl
    simp only [centerOdd, hlowBit, List.append_assoc, run_append, run_take,
      (rotate_counts L.word).2.1, measurementCount, Nat.add_zero, List.drop_zero,
      st4, st3, st2x, st2, st1]
    rw [FifthCarry.no_records [.CX L.flag L.msb, .CX L.msb L.flag] hmc4 _ _ []]
    rfl
  rw [hrun]
  let R := regValue (restLow ++ [L.msb]) s.basis
  have hxvSplit : x.val = (if s.basis a then 1 else 0) + 2 * R := by rw [← hx, hwordS]; rfl
  have hs1 : st1.phase = s.phase ∧ st1.basis L.flag = s.basis a ∧ st1.basis a = false ∧
      (∀ q, q ≠ a → q ≠ L.flag → st1.basis q = s.basis q) :=
    cx_swap_run a L.flag hfa s hflag
  have hv1 : regValue L.word st1.basis = 2 * R := by
    rw [hwordS]
    change (if st1.basis a then 1 else 0) + 2 * regValue (restLow ++ [L.msb]) st1.basis = 2 * R
    rw [hs1.2.2.1]
    have hrest : regValue (restLow ++ [L.msb]) st1.basis = R :=
      regValue_congr _ _ _ (fun q hq => hs1.2.2.2 q (fun e => haRest (e ▸ hq))
        (fun e => hflagWord (by rw [hwordS]; simp [e ▸ hq])))
    rw [hrest]; simp
  have hr2 := rotateRight_spec L.word hwnd (2 * R) (by omega) st1 [] hv1
  have hf2 := (rotate_frame L.word st1 []).2.1
  have hv2 : regValue L.word st2.basis = R := by
    have h := hr2.2; change regValue L.word st2.basis = 2 * R / 2 at h; omega
  have hmsb2 : st2.basis L.msb = false := by
    have hsp : regValue L.word st2.basis = regValue L.low st2.basis + 2 ^ 255 * (if st2.basis L.msb then 1 else 0) := by
      simp only [BalancedConvert.Layout.word, regValue_append, hw.1]; simp [regValue, Nat.mul_comm]
    cases hm : st2.basis L.msb
    · rfl
    · rw [hm, hv2] at hsp; simp at hsp; omega
  have hlow2 : regValue L.low st2.basis = R := by
    have hsp : regValue L.word st2.basis = regValue L.low st2.basis + 2 ^ 255 * (if st2.basis L.msb then 1 else 0) := by
      simp only [BalancedConvert.Layout.word, regValue_append, hw.1]; simp [regValue, Nat.mul_comm]
    rw [hmsb2, hv2] at hsp; simp at hsp; omega
  have hx2 := x_gate_run L.flag st2
  have hflag2x : st2x.basis L.flag = !s.basis a := by
    change (run [.X L.flag] [] st2).basis L.flag = !s.basis a
    rw [hx2.2.1, hf2 _ hflagWord, hs1.2.1]
  have hlow2x : regValue L.low st2x.basis = R := by
    rw [← hlow2]
    exact regValue_congr _ _ _ (fun q hq => hx2.2.2 q (fun e => hflagWord (by simp [BalancedConvert.Layout.word, e ▸ hq])))
  have hmsb2x : st2x.basis L.msb = false := (hx2.2.2 _ hfm.symm).trans hmsb2
  have hclean2x : ∀ q ∈ L.carry.take 254, st2x.basis q = false := by
    intro q hq
    have qf : q ≠ L.flag := fun e => (List.nodup_cons.mp hnd).1 (by simp [e ▸ hq])
    have qw : q ∉ L.word := work_not_word L hn q (by simp [convWork, hq])
    have qa : q ≠ a := fun e => qw (e ▸ haWord)
    rw [hx2.2.2 q qf, hf2 q qw, hs1.2.2.2 q qa qf]
    exact hc q (by simp [convWork, hq])
  have hcin2x : st2x.basis L.cin = false := by
    have cf : L.cin ≠ L.flag := fun e => (List.nodup_cons.mp hnd).1 (by simp [e])
    have cw : L.cin ∉ L.word := work_not_word L hn L.cin (by simp [convWork])
    have ca : L.cin ≠ a := fun e => cw (e ▸ haWord)
    rw [hx2.2.2 _ cf, hf2 _ cw, hs1.2.2.2 _ ca cf, hcin]
  have hlowNd : (L.cin :: (L.low ++ L.carry.take 254)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hc0 := List.nodup_iff_count.mp hnd q
    simp only [BalancedConvert.Layout.word, List.count_cons, List.count_append] at hc0 ⊢; omega
  have hsrcAway : ∀ q ∈ mappedWires (lowCorrectionOdd L), q ∉ L.cin :: (L.low ++ L.carry.take 254) := by
    intro q hq bad
    rw [lowCorrectionOdd_sources L q hq] at bad
    have hc0 := List.nodup_iff_count.mp hnd L.flag
    have cb := List.count_pos_iff.mpr bad
    simp only [BalancedConvert.Layout.word, List.count_cons, List.count_append, beq_self_eq_true, if_true] at hc0 cb
    omega
  have hp3 := mappedAdd_correct (lowCorrectionOdd L) L.low (L.carry.take 254) L.cin
    hlowNd hsrcAway (by rw [lowCorrectionOdd_length, hw.1]) (by simp [List.length_take, hw.1, hw.2])
    st2x m hclean2x
  have hv3 : regValue L.low st3.basis = (if !s.basis a then 2147484136 else 0) + R := by
    rw [hp3.2.2, lowCorrectionOdd_value, hflag2x, hlow2x, hcin2x, hw.1, h255]
    cases hk : s.basis a <;> simp only [hk, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      if_false, if_true, Bool.toNat_false, Nat.add_zero, Nat.zero_add] at hxvSplit ⊢ <;> omega
  have hflag3 : st3.basis L.flag = !s.basis a :=
    (hp3.2.1 _ (fun h => hflagWord (by simp [BalancedConvert.Layout.word, h]))).trans hflag2x
  have hmsb3 : st3.basis L.msb = false := (hp3.2.1 _ hmsbLow).trans hmsb2x
  have hs4 : st4.phase = st3.phase ∧ st4.basis L.msb = st3.basis L.flag ∧ st4.basis L.flag = false ∧
      (∀ q, q ≠ L.flag → q ≠ L.msb → st4.basis q = st3.basis q) :=
    cx_swap_run L.flag L.msb hfm st3 hmsb3
  have hlow4 : regValue L.low st4.basis = regValue L.low st3.basis :=
    regValue_congr _ _ _ (fun q hq => hs4.2.2.2 q
      (fun e => hflagWord (by simp [BalancedConvert.Layout.word, e ▸ hq]))
      (fun e => hmsbLow (e ▸ hq)))
  have hframe : ∀ q, q ∉ L.word → st4.basis q = s.basis q := by
    intro q hq
    by_cases qf : q = L.flag
    · subst q; rw [hs4.2.2.1, hflag]
    · have qa : q ≠ a := fun e => hq (e ▸ haWord)
      have qm : q ≠ L.msb := fun e => hq (by simp [BalancedConvert.Layout.word, e])
      have ql : q ∉ L.low := fun h => hq (by simp [BalancedConvert.Layout.word, h])
      rw [hs4.2.2.2 q qf qm, hp3.2.1 q ql,
        hx2.2.2 q qf,
        hf2 q hq, hs1.2.2.2 q qa qf]
  refine ⟨hs4.1.trans (hp3.1.trans (hr2.1.trans hs1.1)), ?_,
    fun q hq => (hframe q (work_not_word L hn q hq)).trans (hc q hq), hframe⟩
  have hsp : regValue L.word st4.basis = regValue L.low st4.basis + 2 ^ 255 * (if st4.basis L.msb then 1 else 0) := by
    simp only [BalancedConvert.Layout.word, regValue_append, hw.1]; simp [regValue, Nat.mul_comm]
  rw [hsp, hlow4, hv3, hs4.2.1, hflag3, oddWord_half]
  cases hk : s.basis a
  · have he : x.val % 2 = 0 := by simp [hk] at hxvSplit; omega
    have hdiv : x.val / 2 = R := by simp [hk] at hxvSplit; omega
    simp only [hk, Bool.not_false, he, if_true, decide_true, Bool.toNat_true, Nat.mul_one, hdiv]
    have hsm : R + 2147484136 < 2 ^ 255 := by simp [hk] at hxvSplit; omega
    rw [Nat.mod_eq_of_lt hsm]; omega
  · have ho : ¬ (x.val % 2 = 0) := by simp [hk] at hxvSplit; omega
    have hdiv : x.val / 2 = R := by simp [hk] at hxvSplit; omega
    simp only [hk, Bool.not_true, ho, Bool.false_eq_true, if_false, decide_false,
      Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Nat.zero_add, hdiv]
    have hsm : R < 2 ^ 255 := by simp [hk] at hxvSplit; omega
    rw [Nat.mod_eq_of_lt hsm]

/-- Semantic correctness of `canonicalOdd`: `oddWord x` to canonical `(2 * x).val`. -/
theorem canonicalOdd_correct (L : BalancedConvert.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis = oddWord x)
    (hc : ∀ q ∈ convWork L, s.basis q = false) :
    let t := run (canonicalOdd L) m s
    t.phase = s.phase ∧ regValue L.word t.basis = (2 * x).val ∧
    (∀ q ∈ convWork L, t.basis q = false) ∧ (∀ q, q ∉ L.word → t.basis q = s.basis q) := by
  let y : Fp := 2 * x
  have hy : y / 2 = x := by
    change (2 * x) / 2 = x
    rw [mul_comm, mul_div_cancel_right₀ x two_ne_zero]
  have hyv : y.val < p := ZMod.val_lt y
  have hp := p_eq
  have h255 := pow255_eq
  have hflag : s.basis L.flag = false := hc _ (by simp [convWork])
  have hcin : s.basis L.cin = false := hc _ (by simp [convWork])
  have hnd : (L.flag :: L.cin :: (L.word ++ L.carry.take 254)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hc0 := List.nodup_iff_count.mp hn q
    simp only [BalancedConvert.Layout.wires, BalancedConvert.Layout.word, List.count_cons,
      List.count_append] at hc0 ⊢
    have htk := (List.take_sublist 254 L.carry).count_le q
    omega
  have hwnd : L.word.Nodup := (List.nodup_append'.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1
  have hflagWord : L.flag ∉ L.word := work_not_word L hn L.flag (by simp [convWork])
  have hmsbLow : L.msb ∉ L.low := by
    rw [BalancedConvert.Layout.word] at hwnd
    exact fun h => (List.nodup_append'.mp hwnd).2.2 h (by simp)
  have hmf : L.msb ≠ L.flag := fun e => hflagWord (by simp [BalancedConvert.Layout.word, e])
  rcases hlowS : L.low with _ | ⟨a, restLow⟩
  · have := hw.1; rw [hlowS] at this; contradiction
  have hlowBit : HalfConvert.lowBit L = a := by simp [HalfConvert.lowBit, hlowS]
  have hwordS : L.word = a :: (restLow ++ [L.msb]) := by simp [BalancedConvert.Layout.word, hlowS]
  have haWord : a ∈ L.word := by rw [hwordS]; simp
  have hfa : a ≠ L.flag := fun e => hflagWord (e ▸ haWord)
  have haRest : a ∉ restLow ++ [L.msb] := by
    rw [hwordS] at hwnd; exact (List.nodup_cons.mp hwnd).1
  have how : oddWord x = (y.val / 2 + (if y.val % 2 = 0 then 2147484136 else 0)) +
      2 ^ 255 * (decide (y.val % 2 = 0)).toNat := by
    rw [← hy, oddWord_half y]
    have hsm : y.val / 2 + (if y.val % 2 = 0 then 2147484136 else 0) < 2 ^ 255 := by
      split_ifs <;> omega
    rw [Nat.mod_eq_of_lt hsm]
  have hspS : regValue L.word s.basis = regValue L.low s.basis + 2 ^ 255 * (if s.basis L.msb then 1 else 0) := by
    simp only [BalancedConvert.Layout.word, regValue_append, hw.1]; simp [regValue, Nat.mul_comm]
  have hlowLt : regValue L.low s.basis < 2 ^ 255 := by
    have := regValue_lt L.low s.basis; rwa [hw.1] at this
  have hmsbS : s.basis L.msb = decide (y.val % 2 = 0) := by
    rw [hx, how] at hspS
    by_cases he : y.val % 2 = 0 <;> cases hm : s.basis L.msb <;>
      simp [hm, he] at hspS ⊢ <;> omega
  have hlowSVal : regValue L.low s.basis = y.val / 2 + (if y.val % 2 = 0 then 2147484136 else 0) := by
    rw [hx, how, hmsbS] at hspS
    cases he : decide (y.val % 2 = 0) <;> simp [he] at hspS <;> omega
  let st1 := run [.CX L.msb L.flag, .CX L.flag L.msb] [] s
  let st2 := run (mappedSub (lowCorrectionOdd L) L.low (L.carry.take 254) L.cin) m st1
  let st2x := run [.X L.flag] [] st2
  let st3 := run (rotateLeft L.word) [] st2x
  let st4 := run [.CX L.flag a, .CX a L.flag] [] st3
  have hrun : run (canonicalOdd L) m s = st4 := by
    simp only [canonicalOdd, hlowBit, List.append_assoc, run_append, run_take,
      (rotate_counts L.word).2.2.2, measurementCount, Nat.add_zero, List.drop_zero,
      st4, st3, st2x, st2, st1]
    rw [FifthCarry.no_records [.CX L.flag a, .CX a L.flag] rfl _ _ []]
    rfl
  rw [hrun]
  have hs1 : st1.phase = s.phase ∧ st1.basis L.flag = s.basis L.msb ∧ st1.basis L.msb = false ∧
      (∀ q, q ≠ L.msb → q ≠ L.flag → st1.basis q = s.basis q) :=
    cx_swap_run L.msb L.flag hmf s hflag
  have hlow1 : regValue L.low st1.basis = regValue L.low s.basis :=
    regValue_congr _ _ _ (fun q hq => hs1.2.2.2 q (fun e => hmsbLow (e ▸ hq))
      (fun e => hflagWord (by simp [BalancedConvert.Layout.word, e ▸ hq])))
  have hclean1 : ∀ q ∈ L.carry.take 254, st1.basis q = false := by
    intro q hq
    have qw : q ∉ L.word := work_not_word L hn q (by simp [convWork, hq])
    have qf : q ≠ L.flag := fun e => (List.nodup_cons.mp hnd).1 (by simp [e ▸ hq])
    have qm : q ≠ L.msb := fun e => qw (by simp [BalancedConvert.Layout.word, e])
    exact (hs1.2.2.2 q qm qf).trans (hc q (by simp [convWork, hq]))
  have hcin1 : st1.basis L.cin = false := by
    have cw : L.cin ∉ L.word := work_not_word L hn L.cin (by simp [convWork])
    have cf : L.cin ≠ L.flag := fun e => (List.nodup_cons.mp hnd).1 (by simp [e])
    have cm : L.cin ≠ L.msb := fun e => cw (by simp [BalancedConvert.Layout.word, e])
    exact (hs1.2.2.2 _ cm cf).trans hcin
  have hlowNd : (L.cin :: (L.low ++ L.carry.take 254)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hc0 := List.nodup_iff_count.mp hnd q
    simp only [BalancedConvert.Layout.word, List.count_cons, List.count_append] at hc0 ⊢; omega
  have hsrcAway : ∀ q ∈ mappedWires (lowCorrectionOdd L), q ∉ L.cin :: (L.low ++ L.carry.take 254) := by
    intro q hq bad
    rw [lowCorrectionOdd_sources L q hq] at bad
    have hc0 := List.nodup_iff_count.mp hnd L.flag
    have cb := List.count_pos_iff.mpr bad
    simp only [BalancedConvert.Layout.word, List.count_cons, List.count_append, beq_self_eq_true, if_true] at hc0 cb
    omega
  have hp2 := mappedSub_correct (lowCorrectionOdd L) L.low (L.carry.take 254) L.cin
    hlowNd hsrcAway (by rw [lowCorrectionOdd_length, hw.1]) (by simp [List.length_take, hw.1, hw.2])
    st1 m hclean1 hcin1
  have hv2 : regValue L.low st2.basis = y.val / 2 := by
    rw [hp2.2.2, lowCorrectionOdd_value, hs1.2.1, hmsbS, hlow1, hlowSVal, hw.1]
    have hsm : y.val / 2 < 2 ^ 255 := by omega
    by_cases he : y.val % 2 = 0
    · simp only [he, decide_true, if_true]
      rw [show y.val / 2 + 2147484136 + 2 ^ 255 - 2147484136 = y.val / 2 + 2 ^ 255 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hsm]
    · simp only [he, decide_false, Bool.false_eq_true, if_false, Nat.add_zero, Nat.sub_zero]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsm]
  have hmsb2 : st2.basis L.msb = false := (hp2.2.1 _ hmsbLow).trans hs1.2.2.1
  have hx2 := x_gate_run L.flag st2
  have hword2x : regValue L.word st2x.basis = y.val / 2 := by
    have hsp : regValue L.word st2x.basis = regValue L.low st2x.basis + 2 ^ 255 * (if st2x.basis L.msb then 1 else 0) := by
      simp only [BalancedConvert.Layout.word, regValue_append, hw.1]; simp [regValue, Nat.mul_comm]
    have hl : regValue L.low st2x.basis = regValue L.low st2.basis :=
      regValue_congr _ _ _ (fun q hq => hx2.2.2 q (fun e => hflagWord (by simp [BalancedConvert.Layout.word, e ▸ hq])))
    have hm : st2x.basis L.msb = false := (hx2.2.2 _ hmf).trans hmsb2
    rw [hsp, hl, hv2, hm]; simp
  have hflag2x : st2x.basis L.flag = decide (y.val % 2 = 1) := by
    have hf2 : st2.basis L.flag = decide (y.val % 2 = 0) :=
      (hp2.2.1 _ (fun h => hflagWord (by simp [BalancedConvert.Layout.word, h]))).trans (hs1.2.1.trans hmsbS)
    change (run [.X L.flag] [] st2).basis L.flag = _
    rw [hx2.2.1, hf2]
    by_cases he : y.val % 2 = 0
    · simp [he, show ¬ (y.val % 2 = 1) by omega]
    · simp [he, show y.val % 2 = 1 by omega]
  have hr3 := rotateLeft_spec L.word hwnd (y.val / 2)
    (by simp [BalancedConvert.Layout.word, hw.1]; omega) st2x [] hword2x
  have hf3 := (rotate_frame L.word st2x []).2.2.2
  have hv3 : regValue L.word st3.basis = 2 * (y.val / 2) := by
    have h := hr3.2
    change regValue L.word st3.basis = 2 * (y.val / 2) at h
    exact h
  have ha3 : st3.basis a = false := by
    have hsp : regValue L.word st3.basis = (if st3.basis a then 1 else 0) + 2 * regValue (restLow ++ [L.msb]) st3.basis := by
      rw [hwordS]; rfl
    rw [hv3] at hsp
    cases ha : st3.basis a <;> simp [ha] at hsp ⊢; omega
  have hflag3 : st3.basis L.flag = decide (y.val % 2 = 1) := (hf3 _ hflagWord).trans hflag2x
  have hs4 : st4.phase = st3.phase ∧ st4.basis a = st3.basis L.flag ∧ st4.basis L.flag = false ∧
      (∀ q, q ≠ L.flag → q ≠ a → st4.basis q = st3.basis q) :=
    cx_swap_run L.flag a hfa.symm st3 ha3
  have hframe : ∀ q, q ∉ L.word → st4.basis q = s.basis q := by
    intro q hq
    by_cases qf : q = L.flag
    · subst q; rw [hs4.2.2.1, hflag]
    · have qa : q ≠ a := fun e => hq (e ▸ haWord)
      have qm : q ≠ L.msb := fun e => hq (by simp [BalancedConvert.Layout.word, e])
      have ql : q ∉ L.low := fun h => hq (by simp [BalancedConvert.Layout.word, h])
      rw [hs4.2.2.2 q qf qa, hf3 q hq,
        hx2.2.2 q qf,
        hp2.2.1 q ql, hs1.2.2.2 q qm qf]
  refine ⟨hs4.1.trans (hr3.1.trans (hp2.1.trans hs1.1)), ?_,
    fun q hq => (hframe q (work_not_word L hn q hq)).trans (hc q hq), hframe⟩
  have hrest4 : regValue (restLow ++ [L.msb]) st4.basis = regValue (restLow ++ [L.msb]) st3.basis :=
    regValue_congr _ _ _ (fun q hq => hs4.2.2.2 q
      (fun e => hflagWord (by rw [hwordS]; simp [e ▸ hq]))
      (fun e => haRest (e ▸ hq)))
  have hrest3 : 2 * regValue (restLow ++ [L.msb]) st3.basis = 2 * (y.val / 2) := by
    have hsp : regValue L.word st3.basis = (if st3.basis a then 1 else 0) + 2 * regValue (restLow ++ [L.msb]) st3.basis := by
      rw [hwordS]; rfl
    rw [hv3, ha3] at hsp; simp at hsp; omega
  rw [hwordS]
  change (if st4.basis a then 1 else 0) + 2 * regValue (restLow ++ [L.msb]) st4.basis = y.val
  rw [hs4.2.1, hflag3, hrest4, hrest3]
  by_cases ho : y.val % 2 = 1 <;> simp [ho] <;> omega

/-- Clean-wire equivalence for `canon760OddLoan`: when `canonRoles` and `yHosts43` are clean (`false`),
    `canon760OddLoan` runs identically to `canonicalOdd converterLayout760`. -/
theorem canon760OddLoan_run_eq_canonicalOdd (x : Fp) (s : State) (m : List Bool)
    (hx : regValue converterLayout760.word s.basis = oddWord x)
    (hc : ∀ q ∈ convWork converterLayout760, s.basis q = false)
    (hy : ∀ q ∈ yHosts43, s.basis q = false) :
    run canon760OddLoan m s = run (canonicalOdd converterLayout760) m s := by
  have hcr : ∀ q ∈ canonRoles, q ∈ convWork converterLayout760 := by
    have hchk : canonRoles.all (fun q => decide (q ∈ convWork converterLayout760)) = true := by
      decide +kernel
    intro q hq; exact of_decide_eq_true (List.all_eq_true.mp hchk q hq)
  have hcorr := canonicalOdd_correct converterLayout760 converterLayout760_facts.widths
    (PeakNodup.nodup_of_mask _ (by decide +kernel)) x s m hx hc
  have havoid : ∀ q ∈ yHosts43, q ∉ wires (canonicalOdd converterLayout760) :=
    fun q hq hw => yHosts43_disjoint.2 q hq
      (List.mem_toFinset.mp (canonical_wires_in_layout converterLayout760 converterLayout760_facts.widths
        (canonicalOdd_wires_sub_gen converterLayout760 converterLayout760_facts.widths hw)))
  exact rebindMany_run_eq_of_clean canonRoles yHosts43 (canonicalOdd converterLayout760)
    (by simp [canonRoles_length, yHosts43, wireBlock, List.length_map, List.length_range']) yHosts43_disjoint.1
    havoid s m (fun q hq => hc q (hcr q hq)) hy (fun q hq => hcorr.2.2.1 q (hcr q hq))

/-- Clean-wire equivalence for `center760OddLoan`: when `canonRoles` and `yHosts43` are clean (`false`),
    `center760OddLoan` runs identically to `centerOdd converterLayout760`. -/
theorem center760OddLoan_run_eq_centerOdd (x : Fp) (s : State) (m : List Bool)
    (hx : regValue converterLayout760.word s.basis = x.val)
    (hc : ∀ q ∈ convWork converterLayout760, s.basis q = false)
    (hy : ∀ q ∈ yHosts43, s.basis q = false) :
    run center760OddLoan m s = run (centerOdd converterLayout760) m s := by
  have hcr : ∀ q ∈ canonRoles, q ∈ convWork converterLayout760 := by
    have hchk : canonRoles.all (fun q => decide (q ∈ convWork converterLayout760)) = true := by
      decide +kernel
    intro q hq; exact of_decide_eq_true (List.all_eq_true.mp hchk q hq)
  have hcorr := centerOdd_correct converterLayout760 converterLayout760_facts.widths
    (PeakNodup.nodup_of_mask _ (by decide +kernel)) x s m hx hc
  have havoid : ∀ q ∈ yHosts43, q ∉ wires (centerOdd converterLayout760) :=
    fun q hq hw => yHosts43_disjoint.2 q hq
      (List.mem_toFinset.mp (center_wires_in_layout converterLayout760 converterLayout760_facts.widths
        (centerOdd_wires_sub_gen converterLayout760 converterLayout760_facts.widths hw)))
  exact rebindMany_run_eq_of_clean canonRoles yHosts43 (centerOdd converterLayout760)
    (by simp [canonRoles_length, yHosts43, wireBlock, List.length_map, List.length_range']) yHosts43_disjoint.1
    havoid s m (fun q hq => hc q (hcr q hq)) hy (fun q hq => hcorr.2.2.1 q (hcr q hq))

end ECDSAAdd.Entrant.OddFullPass.HalfConvertOdd
end

-- ============================================================================
-- Section 3: Odd-word multiplication endpoint (`InverseTailCOdd`)
-- ============================================================================
section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.OddFullPass.InverseTailCOdd
open Arithmetic Challenge RecordedQuantum MappedCompressed Secp256k1 BalancedField BalancedCircuit
open StairEndpointLoan44 OddFullPass

/-- Preparation for uniform odd-word wrap comparison (`y_norm >= third`). -/
def prepOdd (L : BalancedCircuit.Layout) : Program :=
  copyRegister none L.y L.r ++ signComplement L.ymsb L.ylow ++
    xorConstant L.low InverseTailC.third

def decisionOdd (L : BalancedCircuit.Layout) : Program :=
  prepOdd L ++ compareLt (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity ++
    [.CX L.sign L.parity] ++ (prepOdd L).reverse

def rawOdd (L : BalancedCircuit.Layout) : Program :=
  InverseTailC.double L ++ [.CX L.sign L.r0, .X L.sign] ++
    signedAdd L.sign L.y L.r (L.carry.take 255) ++ [.X L.sign]

def programOdd (L : BalancedCircuit.Layout) : Program :=
  decisionOdd L ++ rawOdd L ++ InverseTailC.correction L ++
    [.CX L.r0 L.parity, .CX (L.ylow.headD L.ymsb) L.parity, .CX L.sign L.parity]

/-- Depth-44 loaned odd-word multiplication endpoint body (reuses all three
    loaned carry sweeps from `StairEndpointLoan44`). -/
def decisionOddLoan44 (L : BalancedCircuit.Layout) : Program :=
  prepOdd L ++ compareLtLoan44 L ++ [.CX L.sign L.parity] ++ (prepOdd L).reverse

def rawOddLoan44 (L : BalancedCircuit.Layout) : Program :=
  InverseTailC.double L ++ [.CX L.sign L.r0, .X L.sign] ++
    signedAddLoan44 L ++ [.X L.sign]

def tailProgramOddLoan44 (L : BalancedCircuit.Layout) : Program :=
  decisionOddLoan44 L ++ rawOddLoan44 L ++ correctionLoan44 L ++
    [.CX L.r0 L.parity, .CX (L.ylow.headD L.ymsb) L.parity, .CX L.sign L.parity]

def tailBorrowedOddLoan44 (L : BalancedCircuit.Layout) : Program :=
  renameProgram (InverseTailC.borrowSwap L) (tailProgramOddLoan44 L)

def halfOddLoan44 (L : BalancedCircuit.Layout) : Program :=
  [.X L.sign] ++ tailBorrowedOddLoan44 L ++ [.X L.sign]

def paddedOddLoan44 (L : BalancedCircuit.Layout) (c : Wire) : Program :=
  halfOddLoan44 L ++ List.replicate 256 (Instr.measureX c [] [])

def endPacket760OddLoan44 : Program :=
  renameProgram (Equiv.swap (base 760) (base 717))
    (renameProgram (shifted Placement5.pi0)
      (ControlLoan1589.loanWindow (base 510) (base 2409) (base 719)
        (paddedOddLoan44 (Q6EndpointCell.ports base (base 2409)) (base 512))))

/-- Uniform odd-word wrap decision: `B && (y_norm ≥ third)`. -/
def reducedFlagOdd (B : Bool) (Y : Int) : Bool :=
  B && decide (InverseTailC.third ≤ (if Y < 0 then (-Y - 1).toNat else Y.toNat))

def rawValueOdd (B : Bool) (Y : Int) : Int :=
  if B then 3 * Y + 1 else Y

def resultValueOdd (B : Bool) (Y : Int) : Int :=
  rawValueOdd B Y + (if reducedFlagOdd B Y then (if Y < 0 then (p : Int) else -(p : Int)) else 0)

theorem resultValueOdd_spec (B : Bool) (Y : Fp) :
    resultValueOdd B (oddRep Y) = oddRep ((if B then 3 else 1) * Y) := by
  have hY := oddRep_bounds Y
  have hq : q = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by
    norm_num [q, p]
  have hp : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
    norm_num [p]
  have ht : InverseTailC.third = 19298681539552699237261830834781317975544997444273427339909597334651472445277 := by
    decide
  apply oddDomain_unique
  · unfold OddDomain at hY ⊢
    unfold resultValueOdd rawValueOdd reducedFlagOdd
    cases B <;> by_cases hlt : oddRep Y < 0 <;>
      simp [hlt, hq, hp, ht] <;> (try split_ifs) <;> omega
  · exact oddRep_bounds _
  · rw [oddRep_field]
    unfold resultValueOdd rawValueOdd oddDecode
    have hf := oddRep_field Y
    unfold oddDecode at hf
    have h3half : (1 : Fp) + 1 / 2 = 3 * (1 / 2) := by decide
    cases B
    · simp only [Bool.false_eq_true, if_false, reducedFlagOdd, Bool.false_and, Int.cast_zero,
        add_zero, one_mul]
      exact hf
    · simp only [if_true]
      split_ifs
      · push_cast; rw [ZMod.natCast_self]; linear_combination 3 * hf + h3half
      · push_cast; rw [ZMod.natCast_self]; linear_combination 3 * hf + h3half
      · push_cast; linear_combination 3 * hf + h3half

private theorem prepOdd_counts (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (prepOdd L) = 0 ∧ measurementCount (prepOdd L) = 0 := by
  have w := BalancedCleanup.widths L.toLayout hw
  have c := copyRegister_counts none L.y L.r (w.2.2.1.trans w.2.1.symm)
  simp only [prepOdd, toffoliCount_append, measurementCount_append, c.1, c.2,
    (signComplement_counts _ _).1, (signComplement_counts _ _).2,
    (xorConstant_counts _ _).1, (xorConstant_counts _ _).2]
  simp

theorem tailProgramOddLoan44_counts (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (tailProgramOddLoan44 L) = toffoliCount (tailProgramLoan44 L) ∧
    measurementCount (tailProgramOddLoan44 L) = measurementCount (tailProgramLoan44 L) := by
  have po := prepOdd_counts L hw
  have ps := StairEndpointLoan44.prep_counts L hw
  have hcx1 : toffoliCount ([Instr.CX L.sign L.r0, Instr.X L.sign] : Program) = 0 ∧
      measurementCount ([Instr.CX L.sign L.r0, Instr.X L.sign] : Program) = 0 := ⟨rfl, rfl⟩
  have hx1 : toffoliCount ([Instr.X L.sign] : Program) = 0 ∧
      measurementCount ([Instr.X L.sign] : Program) = 0 := ⟨rfl, rfl⟩
  have hcx2 : toffoliCount ([Instr.CX L.r0 L.parity, Instr.CX (L.ylow.headD L.ymsb) L.parity, Instr.CX L.sign L.parity] : Program) = 0 ∧
      measurementCount ([Instr.CX L.r0 L.parity, Instr.CX (L.ylow.headD L.ymsb) L.parity, Instr.CX L.sign L.parity] : Program) = 0 := ⟨rfl, rfl⟩
  have hcx3 : toffoliCount ([Instr.CX L.r0 L.parity, Instr.CX (L.ylow.headD L.ymsb) L.parity] : Program) = 0 ∧
      measurementCount ([Instr.CX L.r0 L.parity, Instr.CX (L.ylow.headD L.ymsb) L.parity] : Program) = 0 := ⟨rfl, rfl⟩
  have hcx0 : toffoliCount ([Instr.CX L.sign L.parity] : Program) = 0 ∧
      measurementCount ([Instr.CX L.sign L.parity] : Program) = 0 := ⟨rfl, rfl⟩
  simp only [tailProgramOddLoan44, tailProgramLoan44, decisionOddLoan44, decisionLoan44,
    rawOddLoan44, rawLoan44, toffoliCount_append, measurementCount_append,
    toffoliCount_reverse, measurementCount_reverse, po.1, po.2, ps.1, ps.2,
    hcx0.1, hcx0.2, hcx1.1, hcx1.2, hx1.1, hx1.2, hcx2.1, hcx2.2, hcx3.1, hcx3.2,
    Nat.zero_add, Nat.add_zero, and_self]

theorem endPacket760OddLoan44_counts :
    toffoliCount endPacket760OddLoan44 = toffoliCount (endPacket760Loan44 false) ∧
    measurementCount endPacket760OddLoan44 = measurementCount (endPacket760Loan44 false) := by
  have hw := Q6EndpointCell.ports_widths base (base 2409)
  have hc := tailProgramOddLoan44_counts (Q6EndpointCell.ports base (base 2409)) hw
  simp only [endPacket760OddLoan44, endPacket760Loan44, endPacketLoan44, rawEndLoan44,
    endHalfLoan44, paddedOddLoan44, paddedLoan44, halfOddLoan44, halfLoan44,
    tailBorrowedOddLoan44, tailBorrowedLoan44, Bool.false_eq_true, if_false,
    ControlLoan1589.loanWindow, renameProgram_counts, toffoliCount_append,
    measurementCount_append, hc.1, hc.2, and_self]

theorem tailProgramOddLoan44_slots_le (L : BalancedCircuit.Layout) (hw : L.Widths) :
    gateSlots (tailProgramOddLoan44 L) ≤ gateSlots (tailProgramLoan44 L) + 2 := by
  have w := BalancedCleanup.widths L.toLayout hw
  have hxor : gateSlots (xorConstant L.low InverseTailC.third) =
      gateSlots (xorConstant L.low (InverseTailC.third + 1)) := by
    rcases hlow : L.low with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
    · have := w.1; rw [hlow] at this; simp at this
    · have := w.1; rw [hlow] at this; simp at this
    · have ht0 : InverseTailC.third % 2 = 1 := by decide
      have ht1 : (InverseTailC.third + 1) % 2 = 0 := by decide
      have ht2 : (InverseTailC.third / 2) % 2 = 0 := by decide
      have ht3 : ((InverseTailC.third + 1) / 2) % 2 = 1 := by decide
      have ht4 : InverseTailC.third / 2 / 2 = (InverseTailC.third + 1) / 2 / 2 := by decide
      simp only [xorConstant, ht0, ht1, ht2, ht3, ht4, Nat.zero_ne_one, if_true, if_false, gateSlots_append]
      have hx0 : gateSlots ([Instr.X x0] : Program) = 1 := rfl
      have hx1 : gateSlots ([Instr.X x1] : Program) = 1 := rfl
      have hnil : gateSlots ([] : Program) = 0 := rfl
      rw [hx0, hx1, hnil]; omega
  have hprep : gateSlots (prepOdd L) ≤ gateSlots (InverseTailC.prep L) := by
    simp only [prepOdd, InverseTailC.prep, gateSlots_append, hxor]
    omega
  have hrev : gateSlots (prepOdd L).reverse ≤ gateSlots (InverseTailC.prep L).reverse := by
    rw [ExitFusionResearch.slots_reverse, ExitFusionResearch.slots_reverse]
    exact hprep
  simp only [tailProgramOddLoan44, tailProgramLoan44, decisionOddLoan44, decisionLoan44,
    rawOddLoan44, rawLoan44, gateSlots_append]
  have h1 : gateSlots ([Instr.CX L.sign L.r0, Instr.X L.sign] : Program) = 2 := rfl
  have h2 : gateSlots ([Instr.X L.sign] : Program) = 1 := rfl
  have h3 : gateSlots ([Instr.CX L.r0 L.parity, Instr.CX (L.ylow.headD L.ymsb) L.parity, Instr.CX L.sign L.parity] : Program) = 3 := rfl
  have h4 : gateSlots ([Instr.CX L.r0 L.parity, Instr.CX (L.ylow.headD L.ymsb) L.parity] : Program) = 2 := rfl
  rw [h1, h2, h3, h4]
  omega

theorem endPacket760OddLoan44_slots_le :
    gateSlots endPacket760OddLoan44 ≤ gateSlots (endPacket760Loan44 false) + 2 := by
  have hw := Q6EndpointCell.ports_widths base (base 2409)
  have hs := tailProgramOddLoan44_slots_le (Q6EndpointCell.ports base (base 2409)) hw
  simp only [endPacket760OddLoan44, endPacket760Loan44, endPacketLoan44, rawEndLoan44,
    endHalfLoan44, paddedOddLoan44, paddedLoan44, halfOddLoan44, halfLoan44,
    tailBorrowedOddLoan44, tailBorrowedLoan44, Bool.false_eq_true, if_false,
    ControlLoan1589.loanWindow, ECDSAAdd.Baselines.rename_gateSlots, gateSlots_append]
  omega

theorem prepOdd_support (L : BalancedCircuit.Layout) (hw : L.Widths) :
    wires (prepOdd L) ⊆ wires (InverseTailC.prep L) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have hcp : ∀ xs ys : List Wire, xs.length = ys.length → ∀ z ∈ ys, z ∈ wires (copyRegister none xs ys) := by
    intro xs; induction xs with
    | nil => intro ys hlen z hz; cases ys <;> simp at hlen hz
    | cons x xs ih =>
      intro ys hlen z hz; cases ys with
      | nil => simp at hlen
      | cons y ys =>
        rcases List.mem_cons.mp hz with rfl | hz
        · simp [copyRegister, copyGate, wires, Instr.wires]
        · simp only [copyRegister, wires_append, Finset.mem_union]
          exact Or.inr (ih ys (by simp at hlen; omega) z hz)
  have hxc : ∀ (xs : List Wire) (k : Nat), wires (xorConstant xs k) ⊆ xs.toFinset := by
    intro xs; induction xs with
    | nil => intro k; simp [xorConstant, wires]
    | cons x xs ih =>
      intro k z hz
      simp only [xorConstant, wires_append, Finset.mem_union] at hz
      rcases hz with h0 | h1
      · split_ifs at h0
        · have : z = x := by simpa [wires, Instr.wires] using h0
          subst this; simp
        · simp [wires] at h0
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (ih (k / 2) h1)))
  intro q hq
  simp only [prepOdd, InverseTailC.prep, wires_append, Finset.mem_union] at hq ⊢
  rcases hq with (h | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · have hql : q ∈ L.low := List.mem_toFinset.mp (hxc L.low InverseTailC.third h)
    have hqr : q ∈ L.r := by simp [BalancedCleanup.Layout.r, hql]
    exact Or.inl (Or.inl (Or.inl (hcp L.y L.r (w.2.2.1.trans w.2.1.symm) q hqr)))

theorem tailProgramOddLoan44_wires_sub (L : BalancedCircuit.Layout) (hw : L.Widths) :
    wires (tailProgramOddLoan44 L) ⊆ wires (tailProgramLoan44 L) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have hps := prepOdd_support L hw
  have hrev : wires (prepOdd L).reverse ⊆ wires (InverseTailC.prep L).reverse := by
    simpa only [wires_reverse] using hps
  intro q hq
  simp only [tailProgramOddLoan44, tailProgramLoan44, wires_append, Finset.mem_union] at hq ⊢
  rcases hq with ((hd | hr) | hc) | ht
  · left; left; left
    simp only [decisionOddLoan44, decisionLoan44, wires_append, Finset.mem_union] at hd ⊢
    rcases hd with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl (hps h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (hrev h)
  · left; left; right
    simp only [rawOddLoan44, rawLoan44, wires_append, Finset.mem_union] at hr ⊢
    rcases hr with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · rw [OddFullPass.mem_wires_iff_flatMap] at h
      simp only [List.flatMap_cons, List.flatMap_nil, OddFullPass.instrWiresList,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with (rfl | rfl) | rfl
      · exact Or.inl (Or.inl (Or.inr (by simp [wires, Instr.wires])))
      · left; left; left
        simp only [InverseTailC.double, wires_append, Finset.mem_union]
        right
        rw [(rotate_wires L.r).2, if_neg (by rw [w.2.1]; decide)]
        exact List.mem_toFinset.mpr (by simp [BalancedCleanup.Layout.r, BalancedCleanup.Layout.low])
      · exact Or.inl (Or.inl (Or.inr (by simp [wires, Instr.wires])))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · exact Or.inl (Or.inr hc)
  · rw [OddFullPass.mem_wires_iff_flatMap] at ht
    simp only [List.flatMap_cons, List.flatMap_nil, OddFullPass.instrWiresList,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with (rfl | rfl) | (rfl | rfl) | (rfl | rfl)
    · exact Or.inr (by simp [wires, Instr.wires])
    · exact Or.inr (by simp [wires, Instr.wires])
    · exact Or.inr (by simp [wires, Instr.wires])
    · exact Or.inr (by simp [wires, Instr.wires])
    · left; left; right
      simp only [rawLoan44, wires_append, Finset.mem_union]
      exact Or.inr (by simp [wires, Instr.wires])
    · exact Or.inr (by simp [wires, Instr.wires])

attribute [local irreducible] wires

theorem endPacket760OddLoan44_wires_sub :
    wires endPacket760OddLoan44 ⊆ wires (endPacket760Loan44 false) := by
  have sub := tailProgramOddLoan44_wires_sub (Q6EndpointCell.ports base (base 2409)) (Q6EndpointCell.ports_widths base (base 2409))
  simp only [endPacket760OddLoan44, endPacket760Loan44, endPacketLoan44, rawEndLoan44,
    endHalfLoan44, paddedOddLoan44, paddedLoan44, halfOddLoan44, halfLoan44,
    tailBorrowedOddLoan44, tailBorrowedLoan44, Bool.false_eq_true, if_false,
    ControlLoan1589.loanWindow]
  exact StairLoanGroupSupport.rename_sub _ _ _
    (StairLoanGroupSupport.rename_sub _ _ _
      (StairLoanGroupSupport.append_sub _ _ _ _
        (StairLoanGroupSupport.append_sub _ _ _ _ (Finset.Subset.refl _)
          (StairLoanGroupSupport.rename_sub _ _ _
            (StairLoanGroupSupport.append_sub _ _ _ _
              (StairLoanGroupSupport.append_sub _ _ _ _
                (StairLoanGroupSupport.append_sub _ _ _ _ (Finset.Subset.refl _)
                  (StairLoanGroupSupport.rename_sub _ _ _ sub))
                (Finset.Subset.refl _))
              (Finset.Subset.refl _))))
        (Finset.Subset.refl _)))

theorem endPacket760OddLoan44_physical : GatePhysical endPacket760OddLoan44 := by
  have hn : (Q6EndpointCell.ports base (base 2409)).wires.Nodup :=
    Rolling1588Lifetime.half_ports_nodup
  have hsr : (Q6EndpointCell.ports base (base 2409)).sign ≠
      (Q6EndpointCell.ports base (base 2409)).r0 := by decide +kernel
  have hsp : (Q6EndpointCell.ports base (base 2409)).sign ≠
      (Q6EndpointCell.ports base (base 2409)).parity := by decide +kernel
  have h0 := StairEndpointLoan44.tailProgramLoan44_physical
    (Q6EndpointCell.ports base (base 2409)) (Q6EndpointCell.ports_widths base (base 2409)) hn
  have hrevP : ∀ P : Program, GatePhysical P → GatePhysical P.reverse :=
    fun P hp g hg => hp g (List.mem_reverse.mp hg)
  have hxorP : ∀ (xs : List Wire) (k : Nat), GatePhysical (xorConstant xs k) := by
    intro xs; induction xs with
    | nil => intro k g hg; simp [xorConstant] at hg
    | cons x xs ih =>
      intro k
      simp only [xorConstant, gatePhysical_append]
      refine ⟨?_, ih (k / 2)⟩
      split_ifs
      · intro g hg; simp at hg; subst hg; simp [PhysicalInstr, ProperGate]
      · intro g hg; simp at hg
  have hpp : GatePhysical (prepOdd (Q6EndpointCell.ports base (base 2409))) := by
    have h0' := h0
    simp only [tailProgramLoan44, decisionLoan44, InverseTailC.prep, gatePhysical_append] at h0'
    simp only [prepOdd, gatePhysical_append]
    exact ⟨h0'.1.1.1.1.1.1.1.1, hxorP _ _⟩
  have ht : GatePhysical (tailProgramOddLoan44 (Q6EndpointCell.ports base (base 2409))) := by
    simp only [tailProgramLoan44, decisionLoan44, rawLoan44, gatePhysical_append] at h0
    simp only [tailProgramOddLoan44, decisionOddLoan44, rawOddLoan44, gatePhysical_append]
    refine ⟨⟨⟨⟨⟨⟨hpp, h0.1.1.1.1.1.2⟩, h0.1.1.1.1.2⟩, hrevP _ hpp⟩,
      ⟨⟨⟨h0.1.1.2.1.1.1, ?_⟩, h0.1.1.2.1.2⟩, h0.1.1.2.2⟩⟩, h0.1.2⟩, ?_⟩
    · intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp [PhysicalInstr, ProperGate, hsr]
    · have he := h0.2
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact he _ (List.mem_cons_self)
      · exact he _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · simp [PhysicalInstr, ProperGate, hsp]
  have hfull : GatePhysical (paddedOddLoan44 (Q6EndpointCell.ports base (base 2409)) (base 512)) := by
    simp only [paddedOddLoan44, halfOddLoan44, tailBorrowedOddLoan44, gatePhysical_append]
    refine ⟨⟨⟨?_, gatePhysical_rename _ (Equiv.injective _) _ ht⟩, ?_⟩, ?_⟩
    · intro g hg; simp at hg; subst hg; simp [PhysicalInstr, ProperGate]
    · intro g hg; simp at hg; subst hg; simp [PhysicalInstr, ProperGate]
    · intro g hg; rw [List.mem_replicate] at hg; rw [hg.2]; simp [PhysicalInstr, ProperGate]
  simp only [endPacket760OddLoan44]
  exact gatePhysical_rename _ (Equiv.injective _) _
    (gatePhysical_rename _ (Equiv.injective _) _
      (ControlLoan1589.loanWindow_physical _ _ _ _ (by decide +kernel) hfull))

/-- Loan drop for `decisionOddLoan44` (uses `StairEndpointLoan44.compareLtLoan44_run_eq`). -/
theorem decisionOddLoan44_run_eq (s : State) (a b : List Bool)
    (clean : ∀ q ∈ endpointL.carry.take 255, s.basis q = false) :
    run (decisionOddLoan44 endpointL) a s = run (decisionOdd endpointL) b s := by
  let L := endpointL
  have hw : L.Widths := Q6EndpointCell.ports_widths base (base 2409)
  have prepZero : measurementCount (prepOdd L) = 0 := (prepOdd_counts L hw).2
  let R : Program := [.CX L.sign L.parity] ++ (prepOdd L).reverse
  have tailZero : measurementCount R = 0 := by
    simp only [R, measurementCount_append, measurementCount_reverse, prepZero, measurementCount]
  have keepCarry : ∀ q ∈ L.carry.take 255, (run (prepOdd L) [] s).basis q = false := by
    intro q hq
    have hndC : ((L.carry.take 255) ++ (L.y ++ L.r)).Nodup :=
      PeakNodup.nodup_of_mask _ (by decide +kernel)
    have hdis := (List.nodup_append'.mp hndC).2.2 hq
    have hm : q ∉ L.y ∧ q ∉ L.r ∧ q ∉ L.low ∧ q ≠ L.ymsb :=
      ⟨fun h => hdis (List.mem_append_left _ h),
       fun h => hdis (List.mem_append_right _ h),
       fun h => hdis (List.mem_append_right _ (by simp [BalancedCleanup.Layout.r, h])),
       fun h => hdis (List.mem_append_left _ (by simp [BalancedCleanup.Layout.y, h]))⟩
    have haway : q ∉ wires (prepOdd L) := by
      intro h
      simp only [prepOdd, wires_append, Finset.mem_union] at h
      rcases h with (h1 | h2) | h3
      · have hcp : ∀ xs ys : List Wire, wires (copyRegister none xs ys) ⊆ (xs ++ ys).toFinset := by
          intro xs; induction xs with
          | nil => intro ys; cases ys <;> simp [copyRegister, wires]
          | cons x xs ih =>
            intro ys; cases ys with
            | nil => simp [copyRegister, wires]
            | cons y ys =>
              intro z hz
              rw [OddFullPass.mem_wires_iff_flatMap] at hz
              simp only [copyRegister, copyGate, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
                OddFullPass.instrWiresList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
              rw [← OddFullPass.mem_wires_iff_flatMap] at hz
              rcases hz with (rfl | rfl) | hz'
              · simp
              · simp
              · have := List.mem_toFinset.mp (ih ys hz')
                simp only [List.mem_toFinset, List.mem_append, List.mem_cons] at this ⊢; tauto
        have hc := List.mem_toFinset.mp (hcp L.y L.r h1)
        exact (List.mem_append.mp hc).elim hm.1 hm.2.1
      · have hs := signComplement_wires_subset L.ymsb L.ylow h2
        simp only [List.mem_toFinset, List.mem_cons] at hs
        rcases hs with rfl | hy
        · exact hm.2.2.2 rfl
        · exact hm.1 (by simp [BalancedCleanup.Layout.y, hy])
      · have hxc : ∀ (xs : List Wire) (k : Nat), wires (xorConstant xs k) ⊆ xs.toFinset := by
          intro xs; induction xs with
          | nil => intro k; simp [xorConstant, wires]
          | cons x xs ih =>
            intro k z hz
            simp only [xorConstant, wires_append, Finset.mem_union] at hz
            rcases hz with h0 | h1'
            · rw [OddFullPass.mem_wires_iff_flatMap] at h0
              split_ifs at h0
              · simp [OddFullPass.instrWiresList] at h0; subst h0; simp
              · simp at h0
            · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (ih (k / 2) h1')))
        exact hm.2.2.1 (List.mem_toFinset.mp (hxc L.low InverseTailC.third h3))
    rw [run_preserves_outside (prepOdd L) [] s q haway]
    exact clean q hq
  have mid : ∀ x y,
      run (compareLtLoan44 L) x (run (prepOdd L) [] s) =
        run (compareLt (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity) y
          (run (prepOdd L) [] s) :=
    fun x y => compareLtLoan44_run_eq _ x y keepCarry
  have tail : ∀ x y,
      run R x (run (compareLtLoan44 L) [] (run (prepOdd L) [] s)) =
        run R y (run (compareLtLoan44 L) [] (run (prepOdd L) [] s)) :=
    fun x y => FifthCarry.no_records R tailZero _ x y
  simpa only [decisionOddLoan44, decisionOdd, R, List.append_assoc] using
    StairLoan.run_sandwich_independent (prepOdd L) (compareLtLoan44 L)
      (compareLt (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity)
      R s a b prepZero mid tail

/-- Loan drop for `rawOddLoan44` (uses `StairLoan.mappedAddLoan_run_eq`). -/
theorem rawOddLoan44_run_eq (s : State) (a b : List Bool)
    (clean : ∀ q ∈ endpointL.carry.take 255, s.basis q = false) :
    run (rawOddLoan44 endpointL) a s = run (rawOdd endpointL) b s := by
  let L := endpointL
  have hw : L.Widths := Q6EndpointCell.ports_widths base (base 2409)
  have w := BalancedCleanup.widths L.toLayout hw
  let A : Program := InverseTailC.double L ++ [.CX L.sign L.r0, .X L.sign] ++ signComplement L.sign L.y
  let R : Program := signComplement L.sign L.y ++ [.X L.sign]
  have newShape : rawOddLoan44 L = A ++
      StairLoan.mappedAddLoan 44 roles44 (mappedRead L.y false) L.r (L.carry.take 255) L.sign ++ R := by
    simp only [rawOddLoan44, signedAddLoan44, A, R, List.append_assoc]
  have oldShape : rawOdd L = A ++
      mappedAdd (mappedRead L.y false) L.r (L.carry.take 255) L.sign ++ R := by
    simp only [rawOdd, signedAdd, addInPlace_eq_mapped, A, R, List.append_assoc]
  rw [newShape, oldShape]
  have headZero : measurementCount A = 0 := by
    simp only [A, InverseTailC.double, measurementCount_append,
      (rotate_counts L.r).2.2.2, (signComplement_counts _ _).2, measurementCount]
  have tailZero : measurementCount R = 0 := by
    simp only [R, measurementCount_append, (signComplement_counts _ _).2, measurementCount]
  have cleanA : ∀ q ∈ L.carry.take 255, (run A [] s).basis q = false := by
    intro q hq
    have hndC : ((L.carry.take 255) ++ (L.sign :: (L.r ++ L.y))).Nodup :=
      PeakNodup.nodup_of_mask _ (by decide +kernel)
    have hdis := (List.nodup_append'.mp hndC).2.2 hq
    have hm : q ∉ L.r ∧ q ∉ L.y ∧ q ≠ L.sign :=
      ⟨fun h => hdis (List.mem_cons_of_mem _ (List.mem_append_left _ h)),
       fun h => hdis (List.mem_cons_of_mem _ (List.mem_append_right _ h)),
       fun h => hdis (h ▸ List.mem_cons_self)⟩
    rw [run_preserves_outside A [] s q ?_]
    · exact clean q hq
    intro used
    simp only [A, InverseTailC.double, wires_append, Finset.mem_union] at used
    rcases used with (((cx | rot) | g) | sc)
    · rw [OddFullPass.mem_wires_iff_flatMap] at cx
      simp only [List.flatMap_cons, List.flatMap_nil, OddFullPass.instrWiresList,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at cx
      rcases cx with rfl | rfl
      · exact hm.2.1 (by simp [BalancedCleanup.Layout.y])
      · exact hm.1 (by simp [BalancedCleanup.Layout.r])
    · rw [(rotate_wires L.r).2, if_neg (by rw [w.2.1]; decide)] at rot
      exact hm.1 (List.mem_toFinset.mp rot)
    · rw [OddFullPass.mem_wires_iff_flatMap] at g
      simp only [List.flatMap_cons, List.flatMap_nil, OddFullPass.instrWiresList,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at g
      rcases g with (rfl | rfl) | rfl
      · exact hm.2.2 rfl
      · exact hm.1 (by simp [BalancedCleanup.Layout.r, BalancedCleanup.Layout.low])
      · exact hm.2.2 rfl
    · have hs := signComplement_wires_subset L.sign L.y sc
      simp only [List.mem_toFinset, List.mem_cons] at hs
      exact hs.elim hm.2.2 hm.2.1
  have hnd : (L.sign :: (L.r ++ L.carry.take 255)).Nodup := PeakNodup.nodup_of_mask _ (by decide +kernel)
  have ha : ∀ q ∈ mappedWires (mappedRead L.y false), q ∉ L.sign :: (L.r ++ L.carry.take 255) := by
    have hndY : (L.y ++ (L.sign :: (L.r ++ L.carry.take 255))).Nodup :=
      PeakNodup.nodup_of_mask _ (by decide +kernel)
    intro q hq
    have hy : q ∈ L.y := by
      obtain ⟨b, hb, hbw⟩ := List.mem_flatMap.mp hq
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      simp at hbw; exact hbw ▸ hy
    exact (List.nodup_append'.mp hndY).2.2 hy
  have htail : ∀ q ∈ roles44.take 44, q ∈ (L.carry.take 255).drop (44 + 1) := by
    have hchk : (roles44.take 44).all (fun w => decide (w ∈ (L.carry.take 255).drop 45)) = true := by
      decide +kernel
    intro q hq; exact of_decide_eq_true (List.all_eq_true.mp hchk q hq)
  have mid : ∀ x y,
      run (StairLoan.mappedAddLoan 44 roles44 (mappedRead L.y false) L.r (L.carry.take 255) L.sign) x (run A [] s) =
        run (mappedAdd (mappedRead L.y false) L.r (L.carry.take 255) L.sign) y (run A [] s) :=
    fun x y => StairLoan.mappedAddLoan_run_eq 44 roles44 (mappedRead L.y false) L.r (L.carry.take 255) L.sign
      (run A [] s) x y hnd ha (by simp [mappedRead, w.2.1, w.2.2.1])
      (by simp [List.length_take, w.2.1, hw.2.2]) (by simp [List.length_take, hw.2.2])
      cleanA htail
  have tail : ∀ x y,
      run R x (run (StairLoan.mappedAddLoan 44 roles44 (mappedRead L.y false) L.r (L.carry.take 255) L.sign) [] (run A [] s)) =
        run R y (run (StairLoan.mappedAddLoan 44 roles44 (mappedRead L.y false) L.r (L.carry.take 255) L.sign) [] (run A [] s)) :=
    fun x y => FifthCarry.no_records R tailZero _ x y
  exact StairLoan.run_sandwich_independent A _ _ R s a b headZero mid tail

section
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Arithmetic Challenge MappedCompressed Secp256k1 BalancedField BalancedCircuit
open StairEndpointLoan44 OddFullPass

private theorem sandwich_odd (P Q : Program) (flag : Wire) (hp : ProperProgram P)
    (hfree : flag ∉ wires P) (s : State) (m : List Bool) (b : Bool)
    (hQ : run Q m (run P m s) = run (if b then [.X flag] else []) [] (run P m s)) :
    run (P ++ Q ++ P.reverse) m s = run (if b then [.X flag] else []) [] s := by
  have hm := properProgram_measurementCount P hp
  have dis : Disjoint (wires P.reverse) (wires (if b then [.X flag] else [])) := by
    cases b <;> simp [wires, wires_reverse, Instr.wires, Finset.disjoint_singleton_right, hfree]
  have eq := run_disjoint_commute P.reverse (if b then [.X flag] else []) dis
    (m.drop (measurementCount Q)) [] (run P m s)
  simp only [List.append_assoc, run_append, run_take, hm, List.drop_zero]
  rw [FifthCarry.no_records P hm s (m.take 0) m, hQ, eq,
    run_reverse_proper P hp s m (m.drop (measurementCount Q))]

private theorem prepOdd_proper (L : Layout) (hn : L.wires.Nodup) : ProperProgram (prepOdd L) := by
  have yr := InverseTailC.yrND hn
  have ymAway : L.ymsb ∉ L.ylow := by
    have h := (List.nodup_append'.mp yr).1
    rw [BalancedCleanup.Layout.y] at h
    exact fun bad => List.disjoint_left.mp (List.nodup_append'.mp h).2.2 bad (by simp)
  have disYR : List.Disjoint L.y L.r := (List.nodup_append'.mp yr).2.2
  have cp : ProperProgram (copyRegister none L.y L.r) := by
    have hnd : ∀ (xs ys : List Wire), List.Disjoint xs ys → ProperProgram (copyRegister none xs ys) := by
      intro xs; induction xs with
      | nil => intro ys _; simp [copyRegister, ProperProgram]
      | cons x xs ih =>
        intro ys hdis; cases ys with
        | nil => simp [copyRegister, ProperProgram]
        | cons y ys =>
          have hxy : x ≠ y := fun e =>
            List.disjoint_left.mp hdis (List.mem_cons_self (a := x)) (by simp [e])
          simp only [copyRegister, ProperProgram]
          intro g hg; rcases List.mem_cons.mp hg with rfl | hg
          · exact hxy
          · exact ih ys (fun a ha hb => List.disjoint_left.mp hdis (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb)) g hg
    exact hnd L.y L.r disYR
  have sc : ProperProgram (signComplement L.ymsb L.ylow) := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    exact fun e => ymAway (e ▸ hq)
  have xc : ProperProgram (xorConstant L.low InverseTailC.third) := by
    have hx : ∀ (xs : List Wire) (k : Nat), ProperProgram (xorConstant xs k) := by
      intro xs; induction xs with
      | nil => intro _; simp [xorConstant, ProperProgram]
      | cons x xs ih =>
        intro k; simp only [xorConstant]
        split_ifs
        · intro g hg; rcases List.mem_cons.mp hg with rfl | hg; trivial; exact ih (k / 2) g hg
        · exact ih (k / 2)
    exact hx L.low InverseTailC.third
  intro g hg
  simp only [prepOdd, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact cp g hg
  · exact sc g hg
  · exact xc g hg

private theorem prepOdd_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (a : Wire)
    (ha : a ∈ [L.sign, L.parity, L.one, L.lower] ∨ a ∈ L.carry) : a ∉ wires (prepOdd L) :=
  fun bad => InverseTailC.prep_free L hn a ha (prepOdd_support L hw bad)

private theorem odd_msb (Y : Int) (hy : OddDomain Y) (L : Layout) (hw : L.Widths)
    (u : BasisState) (hY : regValue L.y u = encodeWord 256 Y) :
    u L.ymsb = decide (Y < 0) := by
  have hq : q = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by
    norm_num [q, p]
  unfold OddDomain at hy
  have split := regValue_highBit L.ylow L.ymsb u
  rw [hw.2.1] at split
  change (u L.ymsb = true ↔ 2 ^ 255 ≤ regValue L.y u) at split
  rw [hY] at split
  have enc : ((encodeWord 256 Y : Nat) : Int) = if Y < 0 then Y + 2 ^ 256 else Y := by
    unfold encodeWord
    split_ifs with hlt
    · have e : Y % ((2 ^ 256 : Nat) : Int) = Y + 2 ^ 256 := by norm_num at hq ⊢; omega
      rw [e]; norm_num at hq ⊢; omega
    · have e : Y % ((2 ^ 256 : Nat) : Int) = Y := by
        apply Int.emod_eq_of_lt <;> norm_num at hq ⊢ <;> omega
      rw [e]; omega
  cases hb : u L.ymsb <;> by_cases hlt : Y < 0 <;>
    simp [hb, hlt] at split enc ⊢ <;> norm_num at hq enc split ⊢ <;> omega

private theorem odd_magnitude_word (L : Layout) (hw : L.Widths) (Y : Int) (hy : OddDomain Y)
    (u : BasisState) (hY : regValue L.y u = encodeWord 256 Y) :
    regValue L.ylow (fun a => u a ^^ u L.ymsb) = if Y < 0 then (-Y - 1).toNat else Y.toNat := by
  have hq : q = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by
    norm_num [q, p]
  unfold OddDomain at hy
  have msb := odd_msb Y hy L hw u hY
  rw [InverseTailC.regValue_xor, hw.2.1, msb]
  have split : regValue L.y u = regValue L.ylow u + 2 ^ 255 * (if u L.ymsb then 1 else 0) := by
    rw [BalancedCleanup.Layout.y, regValue_append, hw.2.1]
    cases hb : u L.ymsb <;> simp [regValue, hb]
  have lt := regValue_lt L.ylow u
  rw [hw.2.1] at lt
  have enc : ((encodeWord 256 Y : Nat) : Int) = if Y < 0 then Y + 2 ^ 256 else Y := by
    unfold encodeWord
    split_ifs with hlt
    · have e : Y % ((2 ^ 256 : Nat) : Int) = Y + 2 ^ 256 := by norm_num at hq ⊢; omega
      rw [e]; norm_num at hq ⊢; omega
    · have e : Y % ((2 ^ 256 : Nat) : Int) = Y := by
        apply Int.emod_eq_of_lt <;> norm_num at hq ⊢ <;> omega
      rw [e]; omega
  rw [hY, msb] at split
  by_cases hlt : Y < 0 <;> simp [hlt] at split enc ⊢ <;> norm_num at hq enc split lt ⊢ <;> omega

private theorem prepOdd_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (heq : regValue L.r s.basis = regValue L.y s.basis) :
    (run (prepOdd L) m s).phase = s.phase ∧
    regValue L.ylow (run (prepOdd L) m s).basis = regValue L.ylow (fun a => s.basis a ^^ s.basis L.ymsb) ∧
    regValue L.low (run (prepOdd L) m s).basis = InverseTailC.third := by
  have w := BalancedCleanup.widths L.toLayout hw
  have yr := InverseTailC.yrND hn
  have rn := (List.nodup_append'.mp yr).2.1
  have yn := (List.nodup_append'.mp yr).1
  have lnd : L.low.Nodup := (List.nodup_append'.mp (by simpa [BalancedCleanup.Layout.r] using rn)).1
  have ynd : L.ylow.Nodup := (List.nodup_append'.mp (by simpa [BalancedCleanup.Layout.y] using yn)).1
  have ymAway : L.ymsb ∉ L.ylow := fun bad =>
    List.disjoint_left.mp (List.nodup_append'.mp (by simpa [BalancedCleanup.Layout.y] using yn)).2.2 bad (by simp)
  let u := run (copyRegister none L.y L.r) m s
  let v := run (signComplement L.ymsb L.ylow) m u
  let z := run (xorConstant L.low InverseTailC.third) m v
  have cp := copyRegister_correct none L.y L.r (w.2.2.1.trans w.2.1.symm) yr (by simp) s m
  have ur0 : regValue L.r u.basis = 0 := by
    have hx := cp.2.2
    simp only [copyValue, heq, Nat.xor_self] at hx
    exact hx
  have ulow0 : regValue L.low u.basis = 0 := by
    have hsplit : regValue L.r u.basis = regValue L.low u.basis + 2 ^ 255 * regValue [L.rmsb] u.basis := by
      rw [BalancedCleanup.Layout.r, regValue_append, w.1]
    omega
  have uy : ∀ a ∈ L.y, u.basis a = s.basis a := fun a ha => cp.2.1 a (InverseTailC.y_away_r hn a ha)
  have uym : u.basis L.ymsb = s.basis L.ymsb := uy L.ymsb (by simp [BalancedCleanup.Layout.y])
  have sc := signComplement_correct L.ymsb L.ylow ynd ymAway u m
  have vlow0 : regValue L.low v.basis = 0 := by
    rw [regValue_congr L.low v.basis u.basis (fun a ha => sc.2.1 a (fun bad =>
      InverseTailC.y_away_r hn a (by simp [BalancedCleanup.Layout.y, bad]) (by simp [BalancedCleanup.Layout.r, ha])))]
    exact ulow0
  have vy : regValue L.ylow v.basis = regValue L.ylow (fun a => s.basis a ^^ s.basis L.ymsb) := by
    have h1 := sc.2.2
    rw [uym, hw.2.1] at h1
    rw [h1, InverseTailC.regValue_xor, hw.2.1]
    have hyl : regValue L.ylow u.basis = regValue L.ylow s.basis :=
      regValue_congr L.ylow u.basis s.basis (fun a ha => uy a (by simp [BalancedCleanup.Layout.y, ha]))
    rw [hyl]
  have htlt : InverseTailC.third < 2 ^ L.low.length := by
    rw [w.1]; decide +kernel
  have xc := xorConstant_correct L.low lnd InverseTailC.third htlt v m
  have zl : regValue L.low z.basis = InverseTailC.third := by
    rw [xc.2.2, vlow0, Nat.zero_xor]
  have zy : regValue L.ylow z.basis = regValue L.ylow (fun a => s.basis a ^^ s.basis L.ymsb) := by
    rw [regValue_congr L.ylow z.basis v.basis (fun a ha => xc.2.1 a (fun bad =>
      InverseTailC.y_away_r hn a (by simp [BalancedCleanup.Layout.y, ha]) (by simp [BalancedCleanup.Layout.r, bad])))]
    exact vy
  have actual : run (prepOdd L) m s = z := by
    have mc1 : measurementCount (copyRegister none L.y L.r) = 0 :=
      (copyRegister_counts none L.y L.r (w.2.2.1.trans w.2.1.symm)).2
    have mc2 : measurementCount (signComplement L.ymsb L.ylow) = 0 := (signComplement_counts _ _).2
    simp only [prepOdd, List.append_assoc, run_append, run_take, mc1, mc2, List.drop_zero]
    rw [FifthCarry.no_records _ mc1 s (m.take 0) m, FifthCarry.no_records _ mc2 u (m.take 0) m]
  rw [actual]
  exact ⟨xc.1.trans (sc.1.trans cp.1), zy, zl⟩

theorem decisionOdd_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y : Int) (hy : OddDomain Y) (s : State) (m : List Bool)
    (heq : regValue L.r s.basis = regValue L.y s.basis)
    (hY : regValue L.y s.basis = encodeWord 256 Y)
    (ho : s.basis L.one = false) (hc : ∀ a ∈ L.carry.take 255, s.basis a = false) :
    run (decisionOdd L) m s =
      ⟨s.phase, writeBit s.basis L.parity (s.basis L.parity ^^ reducedFlagOdd (s.basis L.sign) Y)⟩ := by
  let t := run (prepOdd L) m s
  have prepared := prepOdd_correct L hw hn s m heq
  have keep (a : Wire) (ha : a ∈ [L.sign, L.parity, L.one, L.lower] ∨ a ∈ L.carry) : t.basis a = s.basis a :=
    run_preserves_outside (prepOdd L) m s a (prepOdd_free L hw hn a ha)
  have sg : t.basis L.sign = s.basis L.sign := keep L.sign (Or.inl (by simp))
  have cl : t.basis L.one = false := (keep L.one (Or.inl (by simp))).trans ho
  have ci : ∀ a ∈ L.carry.take 255, t.basis a = false :=
    fun a ha => (keep a (Or.inr (List.mem_of_mem_take ha))).trans (hc a ha)
  have dnd : (L.parity :: L.one :: (L.ylow ++ L.low ++ L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr; intro a
    have h := List.nodup_iff_count.mp (InverseTailC.inventoryND hn) a
    simp only [BalancedCleanup.Layout.y, BalancedCleanup.Layout.r, List.count_cons, List.count_append] at h ⊢
    omega
  have ctl : ∀ c ∈ some L.sign, c ∉ L.parity :: L.one :: (L.ylow ++ L.low ++ L.carry.take 255) := by
    intro a ha bad
    simp only [Option.mem_def, Option.some.injEq] at ha; subst a
    have h := List.nodup_iff_count.mp (InverseTailC.inventoryND hn) L.sign
    have b := List.count_pos_iff.mpr bad
    simp only [BalancedCleanup.Layout.y, BalancedCleanup.Layout.r, List.count_cons, List.count_append,
      List.count_nil, beq_self_eq_true, if_true] at h b
    omega
  have w := BalancedCleanup.widths L.toLayout hw
  let C := compareLt (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity
  have cmp := compareLt_correct (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity
    dnd ctl (hw.2.1.trans w.1.symm) (by simp [List.length_take, hw.2.2, w.1]) t m cl ci
  have mag := odd_magnitude_word L hw Y hy s.basis hY
  have v1 : regValue L.ylow t.basis = if Y < 0 then (-Y - 1).toNat else Y.toNat := prepared.2.1.trans mag
  have v2 : regValue L.low t.basis = InverseTailC.third := prepared.2.2
  have ne : L.sign ≠ L.parity := by
    have h := List.nodup_iff_count.mp (InverseTailC.inventoryND hn) L.sign
    intro e; simp only [List.count_cons, ← e, beq_self_eq_true, if_true] at h; omega
  have bvalue : (t.basis L.sign && !decide (regValue L.ylow t.basis < regValue L.low t.basis)) =
      reducedFlagOdd (s.basis L.sign) Y := by
    rw [sg, v1, v2]; unfold reducedFlagOdd
    congr 1
    generalize (if Y < 0 then (-Y - 1).toNat else Y.toNat) = N
    by_cases hlt : N < InverseTailC.third
    · simp [hlt, Nat.not_le_of_lt hlt]
    · simp [hlt, Nat.le_of_not_lt hlt]
  have core : run (C ++ [.CX L.sign L.parity]) m t =
      run (if reducedFlagOdd (s.basis L.sign) Y then [.X L.parity] else []) [] t := by
    rw [run_append, run_take]
    apply State.extensionality
    · cases reducedFlagOdd (s.basis L.sign) Y <;> simpa only [run] using cmp.1
    · funext a
      by_cases ae : a = L.parity
      · subst a
        have keepS := cmp.2.1 L.sign ne
        have tv := cmp.2.2
        simp only [controlValue, Option.map_some, Option.getD_some] at tv
        simp only [run, writeBit, Function.update_self]
        change ((run C m t).basis L.parity ^^ (run C m t).basis L.sign) = _
        rw [tv, keepS, ← bvalue]
        cases hp : t.basis L.parity <;> cases hb : t.basis L.sign <;>
          cases hcd : decide (regValue L.ylow t.basis < regValue L.low t.basis) <;>
          simp [run, writeBit, hp, hb, hcd]
      · change (writeBit (run C m t).basis L.parity _) a = _
        rw [writeBit, Function.update_of_ne ae, cmp.2.1 a ae]
        cases reducedFlagOdd (s.basis L.sign) Y <;> simp [run, writeBit, ae]
  have sand := sandwich_odd (prepOdd L) (C ++ [.CX L.sign L.parity]) L.parity
    (prepOdd_proper L hn) (prepOdd_free L hw hn _ (Or.inl (by simp))) s m (reducedFlagOdd (s.basis L.sign) Y) core
  have assoc : decisionOdd L = prepOdd L ++ (C ++ [.CX L.sign L.parity]) ++ (prepOdd L).reverse := by
    simp only [decisionOdd, C, List.append_assoc]
  rw [assoc, sand]
  cases reducedFlagOdd (s.basis L.sign) Y <;> simp [run, writeBit]

private theorem rawOdd_mod (X H : Nat) (_hh : 0 < H) (hx : X < 2 * H) (B : Bool) :
    (if !B then (2 * (X % H) + 2 * H - X) % (2 * H) else (2 * (X % H) + 1 + X) % (2 * H)) =
      (if B then 3 * X + 1 else X) % (2 * H) := by
  by_cases small : X < H
  · rw [Nat.mod_eq_of_lt small]
    cases B
    · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
      rw [show 2 * X + 2 * H - X = X + 2 * H by omega, Nat.add_mod_right]
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true]
      congr 1; omega
  · have low : X % H = X - H := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [low]
    cases B
    · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
      rw [show 2 * (X - H) + 2 * H - X = X by omega]
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true]
      have e : 3 * X + 1 = (2 * (X - H) + 1 + X) + 2 * H := by omega
      conv_rhs => rw [e, Nat.add_mod_right]

theorem rawOdd_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (heq : regValue L.r s.basis = regValue L.y s.basis)
    (hc : ∀ a ∈ L.carry.take 255, s.basis a = false) :
    (run (rawOdd L) m s).phase = s.phase ∧
    regValue L.r (run (rawOdd L) m s).basis =
      (if s.basis L.sign then 3 * regValue L.y s.basis + 1 else regValue L.y s.basis) % 2 ^ 256 ∧
    ∀ a, a ∉ L.r → (run (rawOdd L) m s).basis a = s.basis a := by
  let u := run (InverseTailC.double L) m s
  let v := run [.CX L.sign L.r0, .X L.sign] m u
  let z := run (signedAdd L.sign L.y L.r (L.carry.take 255)) m v
  let t := run [.X L.sign] m z
  have w := BalancedCleanup.widths L.toLayout hw
  have dc := InverseTailC.double_correct L hw hn s m heq
  have sg : L.sign ∉ L.r := fun h => InverseTailC.flagAway (L := L) hn L.sign (by simp) (by simp [h])
  have sy : L.sign ∉ L.y := fun h => InverseTailC.flagAway (L := L) hn L.sign (by simp) (by simp [h])
  have sr0 : L.sign ≠ L.r0 := fun e => sg (by simp [BalancedCleanup.Layout.r, BalancedCleanup.Layout.low, e])
  have r0NotY : L.r0 ∉ L.y := fun h => InverseTailC.y_away_r hn L.r0 h (by simp [BalancedCleanup.Layout.r, BalancedCleanup.Layout.low])
  have dd : (L.sign :: (L.y ++ L.r ++ L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr; intro a
    have h := List.nodup_iff_count.mp (InverseTailC.inventoryND hn) a
    simp only [List.count_cons, List.count_append] at h ⊢; omega
  have csR (a : Wire) (ha : a ∈ L.carry.take 255) : a ∉ L.r := by
    intro bad; have h := List.nodup_iff_count.mp dd a
    have p1 := List.count_pos_iff.mpr ha; have p2 := List.count_pos_iff.mpr bad
    simp only [List.count_cons, List.count_append] at h; omega
  have csS (a : Wire) (ha : a ∈ L.carry.take 255) : a ≠ L.sign :=
    fun e => InverseTailC.flagAway (L := L) hn L.sign (by simp) (by simp [← e, List.mem_of_mem_take ha])
  have us : u.basis L.sign = s.basis L.sign := dc.2.2 L.sign sg
  have ur0 : u.basis L.r0 = false := by
    have hmod : regValue L.r u.basis % 2 = (u.basis L.r0).toNat := by
      change ((if u.basis L.r0 then 1 else 0) + 2 * regValue (L.rtail ++ [L.rmsb]) u.basis) % 2 = _
      cases u.basis L.r0 <;> simp
    rw [dc.2.1] at hmod
    cases hb : u.basis L.r0 <;> simp [hb] at hmod ⊢
  have rtailAway : L.r0 ∉ L.rtail ++ [L.rmsb] := by
    have rnd := (List.nodup_append'.mp (InverseTailC.yrND hn)).2.1
    exact (List.nodup_cons.mp (by simpa [BalancedCleanup.Layout.r, BalancedCleanup.Layout.low] using rnd)).1
  have vs : v.basis L.sign = !s.basis L.sign := by
    simp only [v, run, writeBit, Function.update_self, Function.update_of_ne sr0, us]
  have vr : regValue L.r v.basis = 2 * (regValue L.y s.basis % 2 ^ 255) + (s.basis L.sign).toNat := by
    have htail : regValue (L.rtail ++ [L.rmsb]) v.basis = regValue (L.rtail ++ [L.rmsb]) u.basis := by
      apply regValue_congr; intro a ha
      have aNeS : a ≠ L.sign := fun e => sg (by simp [BalancedCleanup.Layout.r, BalancedCleanup.Layout.low, e ▸ ha])
      have aNeR0 : a ≠ L.r0 := fun e => rtailAway (e ▸ ha)
      simp [v, run, writeBit, aNeS, aNeR0]
    have vr0 : v.basis L.r0 = s.basis L.sign := by
      simp [v, run, writeBit, sr0.symm, us, ur0]
    have uval : regValue L.r u.basis = 2 * regValue (L.rtail ++ [L.rmsb]) u.basis := by
      change (if u.basis L.r0 then 1 else 0) + 2 * regValue (L.rtail ++ [L.rmsb]) u.basis = _
      simp [ur0]
    change (if v.basis L.r0 then 1 else 0) + 2 * regValue (L.rtail ++ [L.rmsb]) v.basis = _
    rw [htail, vr0, ← uval, dc.2.1]
    cases s.basis L.sign <;> simp [Nat.add_comm]
  have vy : regValue L.y v.basis = regValue L.y s.basis := by
    apply regValue_congr; intro a ha
    have ar := InverseTailC.y_away_r hn a ha
    have asg : a ≠ L.sign := fun e => sy (e ▸ ha)
    have ar0 : a ≠ L.r0 := fun e => r0NotY (e ▸ ha)
    simp only [v, run, writeBit, Function.update_of_ne asg, Function.update_of_ne ar0]
    exact dc.2.2 a ar
  have vc : regValue (L.carry.take 255) v.basis = 0 := by
    apply (regValue_zero _ _).mpr; intro a ha
    have ar0 : a ≠ L.r0 := fun e => csR a ha (by simp [BalancedCleanup.Layout.r, BalancedCleanup.Layout.low, e])
    simp only [v, run, writeBit, Function.update_of_ne (csS a ha), Function.update_of_ne ar0]
    exact (dc.2.2 a (csR a ha)).trans (hc a ha)
  have cl : (L.carry.take 255).length + 1 = L.r.length := by simp [List.length_take, hw.2.2, w.2.1]
  have ad := signedAdd_spec L.sign L.y L.r (L.carry.take 255) dd (w.2.2.1.trans w.2.1.symm) cl
    (!s.basis L.sign) (regValue L.y s.basis)
    (2 * (regValue L.y s.basis % 2 ^ 255) + (s.basis L.sign).toNat) v m ⟨⟨⟨vs, vy⟩, vr⟩, vc⟩
  have frame (a : Wire) (ha : a ∉ L.r) : z.basis a = v.basis a :=
    (signedWord_frame L.sign L.y L.r (L.carry.take 255) dd (w.2.2.1.trans w.2.1.symm) cl
      (!s.basis L.sign) (regValue L.y s.basis)
      (2 * (regValue L.y s.basis % 2 ^ 255) + (s.basis L.sign).toNat) v m vs vy vr vc a ha).1
  have dmc : measurementCount (InverseTailC.double L) = 0 := by
    simp [InverseTailC.double, measurementCount_append, measurementCount, (rotate_counts L.r).2.2.2]
  have actual : run (rawOdd L) m s = t := by
    simp only [rawOdd, List.append_assoc, run_append, run_take, dmc, List.drop_zero]
    rw [FifthCarry.no_records (InverseTailC.double L) dmc s (m.take 0) m]
    simp only [show measurementCount ([Instr.CX L.sign L.r0, Instr.X L.sign] : Program) = 0 from rfl, List.drop_zero]
    change run [.X L.sign] _ z = t
    exact FifthCarry.no_records [.X L.sign] (by simp [measurementCount]) z _ m
  rw [actual]
  refine ⟨ad.1.trans dc.1, ?_, ?_⟩
  · have tr : regValue L.r t.basis = regValue L.r z.basis := by
      apply regValue_congr; intro a ha
      simp [t, run, writeBit, show a ≠ L.sign from fun e => sg (e ▸ ha)]
    rw [tr, ad.2.1.2, w.2.1]
    have hv := regValue_lt L.y s.basis
    rw [w.2.2.1] at hv
    have pow : 2 ^ 256 = 2 * (2 ^ 255) := by rw [show 256 = 255 + 1 from rfl, pow_succ]; omega
    have hm := rawOdd_mod (regValue L.y s.basis) (2 ^ 255) (by positivity) (by omega) (s.basis L.sign)
    cases hsb : s.basis L.sign
    · simpa only [signedWordValue, ← pow, hsb, Bool.toNat_false, Nat.add_zero] using hm
    · simpa only [signedWordValue, ← pow, hsb, Bool.toNat_true, Bool.not_true, Bool.false_eq_true, if_false, if_true] using hm
  · intro a ha
    by_cases ae : a = L.sign
    · subst a
      simp only [t, run, writeBit, Function.update_self]
      rw [ad.2.1.1.1]; simp
    · have ar0 : a ≠ L.r0 := fun e => ha (by simp [BalancedCleanup.Layout.r, BalancedCleanup.Layout.low, e])
      simp only [t, v, run, writeBit, Function.update_of_ne ae, Function.update_of_ne ar0, frame a ha]
      exact dc.2.2 a ha

private theorem resultValueOdd_parity (B F N : Bool) (Y : Int) :
    decide (((if B then 3 * Y + 1 else Y) + (if F then (if N then (p : Int) else -(p : Int)) else 0)) % 2 ≠ Y % 2) =
      (B ^^ F) := by
  have hp2 : (p : Int) % 2 = 1 := by decide
  have hnp2 : (-(p : Int)) % 2 = 1 := by decide
  rcases Int.emod_two_eq_zero_or_one Y with hY | hY <;> cases B <;> cases F <;> cases N <;>
    simp [Int.add_emod, Int.mul_emod, hY, hp2, hnp2]

private theorem sub_encoded_odd (Z : Int) :
    (encodeWord 256 Z + 2 ^ 256 - p) % 2 ^ 256 = encodeWord 256 (Z - (p : Int)) := by
  have hp_lt : p < 2 ^ 256 := by decide
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Nat.cast_sub (by omega), Nat.cast_add, encodeWord_cast, encodeWord_cast]
  simp only [Int.sub_emod, Int.add_emod, Int.emod_emod, Int.emod_self, Int.add_zero]

theorem programOdd_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y : Int) (hy : OddDomain Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 Y)
    (hY : regValue L.y s.basis = encodeWord 256 Y)
    (hc : ∀ a ∈ BalancedCircuit.work L, s.basis a = false) :
    (run (programOdd L) m s).phase = s.phase ∧
    regValue L.r (run (programOdd L) m s).basis = encodeWord 256 (resultValueOdd (s.basis L.sign) Y) ∧
    ∀ a, a ∉ L.r → (run (programOdd L) m s).basis a = s.basis a := by
  have c : ∀ a ∈ L.carry.take 255, s.basis a = false := fun a ha => hc a (by simp [BalancedCircuit.work, List.mem_of_mem_take ha])
  have ho : s.basis L.one = false := hc _ (by simp [BalancedCircuit.work])
  have hp : s.basis L.parity = false := hc _ (by simp [BalancedCircuit.work])
  have pr : L.parity ∉ L.r := fun bad => InverseTailC.flagAway hn L.parity (by simp) (by simp [bad])
  have py : L.parity ∉ L.y := fun bad => InverseTailC.flagAway hn L.parity (by simp) (by simp [bad])
  have sp : L.sign ≠ L.parity := by
    have h := List.nodup_iff_count.mp (InverseTailC.inventoryND hn) L.sign
    intro e; simp only [List.count_cons, ← e, beq_self_eq_true, if_true] at h; omega
  have d_tr : Triple (InverseTailC.Frame L s.basis (encodeWord 256 Y) false) (decisionOdd L)
      (InverseTailC.Frame L s.basis (encodeWord 256 Y) (reducedFlagOdd (s.basis L.sign) Y)) := by
    intro u mu hu
    have y := InverseTailC.frame_y L hn s.basis _ _ u.basis hu
    have sy := InverseTailC.frame_flag L hn s.basis _ _ u.basis hu L.sign (Or.inl (by simp))
    have o := (InverseTailC.frame_flag L hn s.basis _ _ u.basis hu L.one (Or.inl (by simp))).trans ho
    have cu : ∀ a ∈ L.carry.take 255, u.basis a = false :=
      fun a ha => (InverseTailC.frame_flag L hn s.basis _ _ u.basis hu a (Or.inr ha)).trans (c a ha)
    rw [decisionOdd_correct L hw hn Y hy u mu (hu.1.trans (y.trans hY).symm) (y.trans hY) o cu]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · exact (regValue_congr _ _ _ (fun a ha => by simp [writeBit, show a ≠ L.parity from fun e => pr (e ▸ ha)])).trans hu.1
    · simp [writeBit, hu.2.1, sy]
    · intro a ar ap; simpa [writeBit, ap] using hu.2.2 a ar ap
  have r_tr : Triple (InverseTailC.Frame L s.basis (encodeWord 256 Y) (reducedFlagOdd (s.basis L.sign) Y))
      (rawOdd L) (InverseTailC.Frame L s.basis (encodeWord 256 (rawValueOdd (s.basis L.sign) Y)) (reducedFlagOdd (s.basis L.sign) Y)) := by
    intro u mu hu
    have y := InverseTailC.frame_y L hn s.basis _ _ u.basis hu
    have sy := InverseTailC.frame_flag L hn s.basis _ _ u.basis hu L.sign (Or.inl (by simp))
    have cu : ∀ a ∈ L.carry.take 255, u.basis a = false :=
      fun a ha => (InverseTailC.frame_flag L hn s.basis _ _ u.basis hu a (Or.inr ha)).trans (c a ha)
    have rr := rawOdd_correct L hw hn u mu (hu.1.trans (y.trans hY).symm) cu
    refine ⟨rr.1, ?_, (rr.2.2 _ pr).trans hu.2.1, ?_⟩
    · rw [rr.2.1, y, hY, sy]
      cases s.basis L.sign
      · simpa only [rawValueOdd, Bool.false_eq_true, if_false] using Nat.mod_eq_of_lt (encodeWord_bound 256 Y)
      · apply Int.ofNat_inj.mp
        simp only [rawValueOdd, if_true]
        rw [Int.natCast_emod, Nat.cast_add, Nat.cast_mul, encodeWord_cast, encodeWord_cast]
        simp only [Nat.cast_ofNat, Nat.cast_one, Int.add_emod, Int.mul_emod, Int.emod_emod]
    · intro a ar ap; exact (rr.2.2 a ar).trans (hu.2.2 a ar ap)
  have c_tr : Triple (InverseTailC.Frame L s.basis (encodeWord 256 (rawValueOdd (s.basis L.sign) Y)) (reducedFlagOdd (s.basis L.sign) Y))
      (InverseTailC.correction L)
      (InverseTailC.Frame L s.basis (encodeWord 256 (resultValueOdd (s.basis L.sign) Y)) (reducedFlagOdd (s.basis L.sign) Y)) := by
    intro u mu hu
    have y := InverseTailC.frame_y L hn s.basis _ _ u.basis hu
    have o := (InverseTailC.frame_flag L hn s.basis _ _ u.basis hu L.one (Or.inl (by simp))).trans ho
    have cu : ∀ a ∈ L.carry.take 255, u.basis a = false :=
      fun a ha => (InverseTailC.frame_flag L hn s.basis _ _ u.basis hu a (Or.inr ha)).trans (c a ha)
    have msb : u.basis L.ymsb = decide (Y < 0) := odd_msb Y hy L hw u.basis (y.trans hY)
    have cc := InverseTailC.correction_correct L hw hn u mu o cu
    refine ⟨cc.1, ?_, (cc.2.2 _ pr).trans hu.2.1, ?_⟩
    · rw [cc.2.1, msb, hu.1, hu.2.1]
      unfold resultValueOdd InverseTailC.correctionValue InverseTailC.compWord
      by_cases hlt : Y < 0 <;> cases hf : reducedFlagOdd (s.basis L.sign) Y
      · simp only [hlt, decide_true, if_true, Bool.false_eq_true, if_false, Int.add_zero, Nat.sub_zero]
        have hb := encodeWord_bound 256 (rawValueOdd (s.basis L.sign) Y)
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
      · simp only [hlt, decide_true, if_true]
        rw [BalancedCleanup.complement_encoded, sub_encoded_odd, BalancedCleanup.complement_encoded]
        congr 1; ring
      · simp only [hlt, decide_false, Bool.false_eq_true, if_false, Int.add_zero, Nat.sub_zero]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (encodeWord_bound 256 _)]
      · simp only [hlt, decide_false, Bool.false_eq_true, if_false, if_true]
        rw [sub_encoded_odd]; congr 1
    · intro a ar ap; exact (cc.2.2 a ar).trans (hu.2.2 a ar ap)
  have e_tr : Triple (InverseTailC.Frame L s.basis (encodeWord 256 (resultValueOdd (s.basis L.sign) Y)) (reducedFlagOdd (s.basis L.sign) Y))
      [.CX L.r0 L.parity, .CX (L.ylow.headD L.ymsb) L.parity, .CX L.sign L.parity]
      (InverseTailC.Frame L s.basis (encodeWord 256 (resultValueOdd (s.basis L.sign) Y)) false) := by
    intro u mu hu
    have rp : L.r0 ≠ L.parity := fun e => pr (by simp [BalancedCleanup.Layout.r, BalancedCleanup.Layout.low, e])
    have yshape : L.y = (L.ylow.headD L.ymsb) :: (L.ylow.drop 1 ++ [L.ymsb]) := by
      cases e : L.ylow with
      | nil => have ww := hw.2.1; rw [e] at ww; contradiction
      | cons a xs => simp only [BalancedCleanup.Layout.y, e, List.headD_cons, List.drop_succ_cons, List.drop_zero, List.cons_append]
    have yp : L.ylow.headD L.ymsb ≠ L.parity := by
      intro e; apply py; rw [yshape]; exact List.mem_cons.mpr (Or.inl e.symm)
    have hmod : ∀ (a : Wire) (xs : List Wire) (b : BasisState), regValue (a :: xs) b % 2 = (b a).toNat := by
      intro a xs b; change ((if b a then 1 else 0) + 2 * regValue xs b) % 2 = _; cases b a <;> simp
    have rb := hmod L.r0 (L.rtail ++ [L.rmsb]) u.basis
    change regValue L.r u.basis % 2 = (u.basis L.r0).toNat at rb
    have yb := hmod (L.ylow.headD L.ymsb) (L.ylow.drop 1 ++ [L.ymsb]) u.basis
    rw [← yshape, InverseTailC.frame_y L hn s.basis _ _ u.basis hu, hY] at yb
    rw [hu.1] at rb
    have ep : ∀ Z : Int, ((encodeWord 256 Z % 2 : Nat) : Int) = Z % 2 := fun Z => by
      have a := encodeWord_cast 256 Z; norm_num only [Nat.reducePow] at a; omega
    have e1 := ep (resultValueOdd (s.basis L.sign) Y); rw [rb] at e1
    have e2 := ep Y; rw [yb] at e2
    have su : u.basis L.sign = s.basis L.sign := InverseTailC.frame_flag L hn s.basis _ _ u.basis hu L.sign (Or.inl (by simp))
    have hpar_eq := resultValueOdd_parity (s.basis L.sign) (reducedFlagOdd (s.basis L.sign) Y) (decide (Y < 0)) Y
    have hpar_bits : (u.basis L.r0 ^^ u.basis (L.ylow.headD L.ymsb)) = (s.basis L.sign ^^ reducedFlagOdd (s.basis L.sign) Y) := by
      have hres : decide ((resultValueOdd (s.basis L.sign) Y) % 2 ≠ Y % 2) = (s.basis L.sign ^^ reducedFlagOdd (s.basis L.sign) Y) := by
        simpa only [resultValueOdd, rawValueOdd, decide_eq_true_eq] using hpar_eq
      rw [← hres, ← e1, ← e2]
      cases u.basis L.r0 <;> cases u.basis (L.ylow.headD L.ymsb) <;> decide
    have hpar : (u.basis L.parity ^^ u.basis L.r0 ^^ u.basis (L.ylow.headD L.ymsb) ^^ u.basis L.sign) = false := by
      rw [hu.2.1, su]
      have : (reducedFlagOdd (s.basis L.sign) Y ^^ u.basis L.r0 ^^ u.basis (L.ylow.headD L.ymsb) ^^ s.basis L.sign) =
          (reducedFlagOdd (s.basis L.sign) Y ^^ (u.basis L.r0 ^^ u.basis (L.ylow.headD L.ymsb)) ^^ s.basis L.sign) := by
        simp [Bool.xor_assoc]
      rw [this, hpar_bits]
      cases s.basis L.sign <;> cases reducedFlagOdd _ Y <;> decide
    have actual : run [.CX L.r0 L.parity, .CX (L.ylow.headD L.ymsb) L.parity, .CX L.sign L.parity] mu u =
        ⟨u.phase, writeBit u.basis L.parity false⟩ := by
      simp only [run, writeBit, Function.update_of_ne rp, Function.update_of_ne yp, Function.update_of_ne sp]
      apply congrArg (State.mk u.phase); funext a
      by_cases ae : a = L.parity
      · subst a; simp only [Function.update_self]; exact hpar
      · simp [Function.update_of_ne ae]
    rw [actual]
    refine ⟨rfl, ?_, by simp [writeBit], ?_⟩
    · exact (regValue_congr _ _ _ (fun a ha => by simp [writeBit, show a ≠ L.parity from fun e => pr (e ▸ ha)])).trans hu.1
    · intro a ar ap; simpa [writeBit, ap] using hu.2.2 a ar ap
  have all := (show Triple (InverseTailC.Frame L s.basis (encodeWord 256 Y) false) (programOdd L)
      (InverseTailC.Frame L s.basis (encodeWord 256 (resultValueOdd (s.basis L.sign) Y)) false) by
    simpa only [programOdd, List.append_assoc] using ((d_tr.seq r_tr).seq c_tr).seq e_tr) s m ⟨hR, hp, fun _ _ _ => rfl⟩
  refine ⟨all.1, all.2.1, ?_⟩
  intro a ar
  by_cases ap : a = L.parity
  · subst a; exact all.2.2.1.trans hp.symm
  · exact all.2.2.2 a ar ap



section ConcreteEnd44
private theorem tailProgramOddLoan44_eq (X : Layout) :
    tailProgramOddLoan44 X =
      decisionOddLoan44 X ++ rawOddLoan44 X ++ correctionLoan44 X ++
        [.CX X.r0 X.parity, .CX (X.ylow.headD X.ymsb) X.parity, .CX X.sign X.parity] := rfl

private theorem programOdd_eq (X : Layout) :
    programOdd X =
      decisionOdd X ++ rawOdd X ++ InverseTailC.correction X ++
        [.CX X.r0 X.parity, .CX (X.ylow.headD X.ymsb) X.parity, .CX X.sign X.parity] := rfl

private theorem tailBorrowedOddLoan44_eq (X : Layout) :
    tailBorrowedOddLoan44 X =
      renameProgram (Equiv.swap (InverseTailC.last X) X.lower) (tailProgramOddLoan44 X) := rfl

private theorem halfOddLoan44_eq (X : Layout) :
    halfOddLoan44 X = [.X X.sign] ++ (tailBorrowedOddLoan44 X ++ [.X X.sign]) := by
  unfold halfOddLoan44; simp only [List.append_assoc]

private theorem paddedOddLoan44_eq (X : Layout) (z : Wire) :
    paddedOddLoan44 X z = halfOddLoan44 X ++ List.replicate 256 (Instr.measureX z [] []) := rfl

private theorem endPacket760OddLoan44_eq :
    endPacket760OddLoan44 =
      renameProgram (Equiv.swap (base 760) (base 717))
        (renameProgram (shifted Placement5.pi0)
          (ControlLoan1589.loanWindow (base 510) (base 2409) (base 719)
            (paddedOddLoan44 endpointL (base 512)))) := rfl

private theorem loanWindow_eq (g flag c : Wire) (P : Program) :
    ControlLoan1589.loanWindow g flag c P =
      [.CX g flag, .CX flag g] ++ (renameProgram (Equiv.swap c g) P ++ ([.CX flag g] ++ [.measureX flag [] [.Z g]])) := by
  unfold ControlLoan1589.loanWindow; simp only [List.append_assoc, List.cons_append, List.nil_append]

attribute [local irreducible] tailBorrowedOddLoan44 ControlLoan1589.loanWindow
attribute [local irreducible] run measurementCount tailProgramOddLoan44 programOdd halfOddLoan44 paddedOddLoan44 endPacket760OddLoan44 decisionOddLoan44 decisionOdd rawOddLoan44 rawOdd correctionLoan44 InverseTailC.correction

private theorem mem_work_carry (X : Layout) (q : Wire) (hq : q ∈ X.carry.take 255) : q ∈ BalancedCircuit.work X := by
  simp [BalancedCircuit.work, List.mem_of_mem_take hq]
private theorem mem_work_one (X : Layout) : X.one ∈ BalancedCircuit.work X := by simp [BalancedCircuit.work]
private theorem mem_work_parity (X : Layout) : X.parity ∈ BalancedCircuit.work X := by simp [BalancedCircuit.work]
private theorem mem_work_lower (X : Layout) : X.lower ∈ BalancedCircuit.work X := by simp [BalancedCircuit.work]
private theorem mem_work_carry_mem (X : Layout) (q : Wire) (hq : q ∈ X.carry) : q ∈ BalancedCircuit.work X := by
  simp [BalancedCircuit.work, hq]

theorem tailProgramOddLoan44_run_eq
    (Y : Int) (hy : OddDomain Y) (s : State) (fresh old : List Bool)
    (hR : regValue endpointL.r s.basis = encodeWord 256 Y)
    (hY : regValue endpointL.y s.basis = encodeWord 256 Y)
    (hc : ∀ a ∈ BalancedCircuit.work endpointL, s.basis a = false) :
    run (tailProgramOddLoan44 endpointL) fresh s = run (programOdd endpointL) old s := by
  let L := endpointL
  have hw : L.Widths := Q6EndpointCell.ports_widths base (base 2409)
  have hn : L.wires.Nodup := Rolling1588Lifetime.half_ports_nodup
  have c0 : ∀ q ∈ L.carry.take 255, s.basis q = false :=
    fun q hq => hc q (mem_work_carry L q hq)
  have ho : s.basis L.one = false := hc _ (mem_work_one L)
  have hpr : ∀ q ∈ L.carry.take 255, q ≠ L.parity := by
    have hchk : (L.carry.take 255).all (fun q => decide (q ≠ L.parity)) = true := by decide +kernel
    exact fun q hq => of_decide_eq_true (List.all_eq_true.mp hchk q hq)
  have hcr : ∀ q ∈ L.carry.take 255, q ∉ L.r := by
    have hchk : (L.carry.take 255).all (fun q => decide (q ∉ L.r)) = true := by decide +kernel
    exact fun q hq => of_decide_eq_true (List.all_eq_true.mp hchk q hq)
  have dEq : ∀ a b, run (decisionOddLoan44 L) a s = run (decisionOdd L) b s :=
    fun a b => decisionOddLoan44_run_eq s a b c0
  obtain ⟨st1, hs1⟩ : ∃ st1 : State, st1 = run (decisionOdd L) [] s := ⟨_, rfl⟩
  have h1 : st1 = ⟨s.phase, writeBit s.basis L.parity (s.basis L.parity ^^ reducedFlagOdd (s.basis L.sign) Y)⟩ := by
    rw [hs1]; exact decisionOdd_correct L hw hn Y hy s [] (hR.trans hY.symm) hY ho c0
  have c1 : ∀ q ∈ L.carry.take 255, st1.basis q = false := fun q hq => by
    rw [h1]; simp [writeBit, hpr q hq, c0 q hq]
  have rEq : ∀ a b, run (rawOddLoan44 L) a st1 = run (rawOdd L) b st1 :=
    fun a b => rawOddLoan44_run_eq st1 a b c1
  obtain ⟨s2, hs2⟩ : ∃ s2 : State, s2 = run (rawOdd L) [] st1 := ⟨_, rfl⟩
  have h1r : regValue L.r st1.basis = regValue L.y st1.basis := by
    have pr : L.parity ∉ L.r := by decide +kernel
    have py : L.parity ∉ L.y := by decide +kernel
    rw [h1]
    rw [regValue_congr L.r _ s.basis (fun a ha => by simp [writeBit, show a ≠ L.parity from fun e => pr (e ▸ ha)]),
        regValue_congr L.y _ s.basis (fun a ha => by simp [writeBit, show a ≠ L.parity from fun e => py (e ▸ ha)]),
        hR, hY]
  have h2 := rawOdd_correct L hw hn st1 [] h1r c1
  have c2 : ∀ q ∈ L.carry.take 255, s2.basis q = false := by
    intro q hq; rw [hs2]; exact (h2.2.2 q (hcr q hq)).trans (c1 q hq)
  have corrEq : ∀ a b, run (correctionLoan44 L) a s2 = run (InverseTailC.correction L) b s2 :=
    fun a b => correctionLoan44_run_eq s2 a b c2
  let E : Program := [.CX L.r0 L.parity, .CX (L.ylow.headD L.ymsb) L.parity, .CX L.sign L.parity]
  have hE0 : measurementCount E = 0 := by simp [E, measurementCount]
  have hsh1 : tailProgramOddLoan44 endpointL =
      decisionOddLoan44 endpointL ++ rawOddLoan44 endpointL ++ correctionLoan44 endpointL ++ E :=
    tailProgramOddLoan44_eq endpointL
  have hsh2 : programOdd endpointL =
      decisionOdd endpointL ++ rawOdd endpointL ++ InverseTailC.correction endpointL ++ E :=
    programOdd_eq endpointL
  rw [hsh1, hsh2]
  simp only [run_append, run_take]
  have hs1_new : run (decisionOddLoan44 endpointL) fresh s = st1 := (dEq fresh []).trans hs1.symm
  have hs1_old : run (decisionOdd endpointL) old s = st1 :=
    (decisionOdd_correct L hw hn Y hy s old (hR.trans hY.symm) hY ho c0).trans h1.symm
  rw [hs1_new, hs1_old]
  have hs2_new : run (rawOddLoan44 endpointL) (fresh.drop (measurementCount (decisionOddLoan44 endpointL))) st1 = s2 :=
    (rEq _ []).trans hs2.symm
  have hs2_old : run (rawOdd endpointL) (old.drop (measurementCount (decisionOdd endpointL))) st1 = s2 :=
    (rEq [] _).symm.trans ((rEq [] []).trans hs2.symm)
  rw [hs2_new, hs2_old]
  have hs3 : run (correctionLoan44 endpointL)
      (fresh.drop (measurementCount (decisionOddLoan44 endpointL ++ rawOddLoan44 endpointL))) s2 =
      run (InverseTailC.correction endpointL)
      (old.drop (measurementCount (decisionOdd endpointL ++ rawOdd endpointL))) s2 := corrEq _ _
  rw [hs3]
  exact FifthCarry.no_records E hE0 _ _ _

theorem halfOddLoan44_frame (X : Fp) (s : State) (m : List Bool)
    (hR : regValue endpointL.r s.basis = oddWord X)
    (hY : regValue endpointL.y s.basis = oddWord X)
    (hc : ∀ a ∈ BalancedCircuit.work endpointL, s.basis a = false) :
    (run (halfOddLoan44 endpointL) m s).phase = s.phase ∧
    regValue endpointL.r (run (halfOddLoan44 endpointL) m s).basis =
      oddWord ((if s.basis endpointL.sign then 1 else 3) * X) ∧
    ∀ a, a ∉ endpointL.r → (run (halfOddLoan44 endpointL) m s).basis a = s.basis a := by
  let L := endpointL
  have hw : L.Widths := Q6EndpointCell.ports_widths base (base 2409)
  have hn : L.wires.Nodup := Rolling1588Lifetime.half_ports_nodup
  have hsr : L.sign ∉ L.r := fun h => BalancedCircuit.flagAway L hn L.sign (by simp) (by simp [h])
  have hsy : L.sign ∉ L.y := fun h => BalancedCircuit.flagAway L hn L.sign (by simp) (by simp [h])
  obtain ⟨u, huDef⟩ : ∃ u : State, u = run [.X L.sign] [] s := ⟨_, rfl⟩
  have hux : u = ⟨s.phase, writeBit s.basis L.sign (!s.basis L.sign)⟩ := huDef.trans (BalancedCleanupOffset.x_run L.sign s [])
  have uf (q : Wire) (hq : q ≠ L.sign) : u.basis q = s.basis q := by rw [hux]; simp [writeBit, hq]
  have usig : u.basis L.sign = !s.basis L.sign := by rw [hux]; simp [writeBit]
  have ur : regValue L.r u.basis = encodeWord 256 (oddRep X) :=
    (regValue_congr _ _ _ (fun q hq => uf q (fun e => hsr (e ▸ hq)))).trans hR
  have uy : regValue L.y u.basis = encodeWord 256 (oddRep X) :=
    (regValue_congr _ _ _ (fun q hq => uf q (fun e => hsy (e ▸ hq)))).trans hY
  have uc : ∀ a ∈ BalancedCircuit.work L, u.basis a = false := fun a ha => by
    have hns : a ≠ L.sign := fun e => OwnQ6Core5.sign_work L hn (e ▸ ha)
    exact (uf a hns).trans (hc a ha)
  have hb_lo : u.basis L.lower = false := uc _ (mem_work_lower L)
  have hb_c254 : u.basis (L.carry.getD 254 L.lower) = false := by
    have hmem : L.carry.getD 254 L.lower ∈ L.carry := by
      have hlen : 254 < L.carry.length := by rw [hw.2.2]; decide
      rw [List.getD_eq_getElem _ _ hlen]; exact List.getElem_mem hlen
    exact uc _ (mem_work_carry_mem L _ hmem)
  have hb_sw : pullState (InverseTailC.borrowSwap L) u = u := by
    unfold InverseTailC.borrowSwap
    exact NewFieldFrameOB5.pull_swap_zero _ _ u hb_c254 hb_lo
  have hprog := programOdd_correct L hw hn (oddRep X) (oddRep_bounds X) u [] ur uy uc
  have hloan := tailProgramOddLoan44_run_eq (oddRep X) (oddRep_bounds X) u m [] ur uy uc
  have hloR : L.lower ∉ L.r := by decide +kernel
  have hc254R : L.carry.getD 254 L.lower ∉ L.r := by decide +kernel
  have ha_lo : (run (tailProgramOddLoan44 L) m u).basis L.lower = false := by
    rw [hloan]; exact (hprog.2.2 _ hloR).trans hb_lo
  have ha_c254 : (run (tailProgramOddLoan44 L) m u).basis (L.carry.getD 254 L.lower) = false := by
    rw [hloan]; exact (hprog.2.2 _ hc254R).trans hb_c254
  have hbor : run (tailBorrowedOddLoan44 L) m u = run (programOdd L) [] u := by
    have hlast : InverseTailC.last L = L.carry.getD 254 L.lower := by decide +kernel
    have hreb := FieldFrameOB5.rebind_swap_run (L.carry.getD 254 L.lower) L.lower
      (tailProgramOddLoan44 L) u m hb_c254 hb_lo ha_c254 ha_lo
    rw [tailBorrowedOddLoan44_eq L, hlast, hreb, hloan]
  have hrun : run (halfOddLoan44 L) m s = run [.X L.sign] [] (run (programOdd L) [] u) := by
    have hsh : halfOddLoan44 L = [.X L.sign] ++ (tailBorrowedOddLoan44 L ++ [.X L.sign]) :=
      halfOddLoan44_eq L
    rw [hsh, run_append, show measurementCount ([.X L.sign] : Program) = 0 from by simp [measurementCount],
      List.take_zero, List.drop_zero, ← huDef, run_append, run_take, hbor]
    exact FifthCarry.no_records [.X L.sign] (by simp [measurementCount]) _ _ []
  obtain ⟨v, hvDef⟩ : ∃ v : State, v = run (programOdd L) [] u := ⟨_, rfl⟩
  have hprog' : v.phase = u.phase ∧
      regValue L.r v.basis = encodeWord 256 (resultValueOdd (u.basis L.sign) (oddRep X)) ∧
      ∀ a, a ∉ L.r → v.basis a = u.basis a := by rw [hvDef]; exact hprog
  have hxEq : run (halfOddLoan44 L) m s = ⟨v.phase, writeBit v.basis L.sign (!v.basis L.sign)⟩ := by
    rw [hrun, ← hvDef, BalancedCleanupOffset.x_run L.sign v []]
  rw [hxEq]
  refine ⟨hprog'.1.trans (by rw [hux]), ?_, ?_⟩
  · have hr_eq : regValue L.r (writeBit v.basis L.sign (!v.basis L.sign)) = regValue L.r v.basis :=
      regValue_congr _ _ _ (fun q hq => by simp [writeBit, show q ≠ L.sign from fun e => hsr (e ▸ hq)])
    rw [hr_eq, hprog'.2.1, usig, resultValueOdd_spec]
    cases s.basis L.sign <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true, if_false, oddWord]
  · intro a ha
    by_cases ae : a = L.sign
    · subst a; simp only [writeBit, Function.update_self]
      rw [hprog'.2.2 L.sign hsr, usig, Bool.not_not]
    · simp only [writeBit, Function.update_of_ne ae]
      exact (hprog'.2.2 a ha).trans (uf a ae)

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

theorem endPacket760OddLoan44_frame (X : Fp) (s : State) (m : List Bool)
    (clean : Q6EndpointCell.Clean base s.basis)
    (flagIn : s.basis (base 2409) = false)
    (hR : regValue endpointL.r s.basis = oddWord X)
    (hY : regValue endpointL.y s.basis = oddWord X)
    (hPull : pullState (shifted Placement5.pi0) s = s)
    (h760 : s.basis (base 760) = false)
    (h717 : s.basis (base 717) = false) :
    (run endPacket760OddLoan44 m s).phase = s.phase ∧
    regValue endpointL.r (run endPacket760OddLoan44 m s).basis =
      oddWord ((if s.basis (base 510) then 1 else 3) * X) ∧
    ∀ a, a ∉ endpointL.r → (run endPacket760OddLoan44 m s).basis a = s.basis a := by
  let L := endpointL
  let g := base 510
  let flag := base 2409
  let c := base 719
  have hpad : ∀ (st : State) (rec : List Bool),
      regValue L.r st.basis = oddWord X →
      regValue L.y st.basis = oddWord X →
      Q6EndpointCell.Clean base st.basis →
      (run (paddedOddLoan44 L (base 512)) rec st).phase = st.phase ∧
      regValue L.r (run (paddedOddLoan44 L (base 512)) rec st).basis =
        oddWord ((if st.basis L.sign then 1 else 3) * X) ∧
      ∀ a, a ∉ L.r → (run (paddedOddLoan44 L (base 512)) rec st).basis a = st.basis a := by
    intro st rec hRs hYs hcs
    have hwk := Q6EndpointCell.clean_work base (base 2409) st.basis hcs
    have hh := halfOddLoan44_frame X st (rec.take (measurementCount (halfOddLoan44 L))) hRs hYs hwk
    have h512_r : base 512 ∉ L.r := by decide +kernel
    have h512_wk : base 512 ∈ BalancedCircuit.work L := mem_work_carry_mem L (base 512) (by decide +kernel)
    have h512_0 : (run (halfOddLoan44 L) (rec.take (measurementCount (halfOddLoan44 L))) st).basis (base 512) = false :=
      (hh.2.2 _ h512_r).trans (hwk _ h512_wk)
    have hrep : ∀ (k : Nat) (x : State) (r : List Bool), x.basis (base 512) = false →
        run (List.replicate k (Instr.measureX (base 512) [] [])) r x = x := by
      intro k; induction k with
      | zero => intro x r _; simp [run]
      | succ k ih =>
        intro x r hx
        change run (Instr.measureX (base 512) [] [] :: List.replicate k (Instr.measureX (base 512) [] [])) r x = x
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
        have hcons : (Instr.measureX (base 512) [] [] :: List.replicate k (Instr.measureX (base 512) [] [])) =
            [Instr.measureX (base 512) [] []] ++ List.replicate k (Instr.measureX (base 512) [] []) := rfl
        rw [hcons, run_append, run_take, hstep]
        exact ih x _ hx
    have hpSh : paddedOddLoan44 L (base 512) = halfOddLoan44 L ++ List.replicate 256 (Instr.measureX (base 512) [] []) :=
      paddedOddLoan44_eq L (base 512)
    rw [hpSh, run_append, hrep 256 _ _ h512_0]
    exact hh
  -- Lift through loanWindow (base 510) (base 2409) (base 719)
  have hraw : ∀ (rec : List Bool),
      (run (ControlLoan1589.loanWindow g flag c (paddedOddLoan44 L (base 512))) rec s).phase = s.phase ∧
      regValue L.r (run (ControlLoan1589.loanWindow g flag c (paddedOddLoan44 L (base 512))) rec s).basis =
        oddWord ((if s.basis g then 1 else 3) * X) ∧
      ∀ a, a ∉ L.r → (run (ControlLoan1589.loanWindow g flag c (paddedOddLoan44 L (base 512))) rec s).basis a = s.basis a := by
    intro rec
    have hgf : g ≠ flag := by decide +kernel
    have hcg : c ≠ g := by decide +kernel
    have hcf : c ≠ flag := by decide +kernel
    have hgR : g ∉ L.r := by decide +kernel
    have hgY : g ∉ L.y := by decide +kernel
    have hfR : flag ∉ L.r := by decide +kernel
    have hfY : flag ∉ L.y := by decide +kernel
    have hcR : c ∉ L.r := by decide +kernel
    obtain ⟨u, uDef⟩ : ∃ u : State, u = run ([.CX g flag, .CX flag g] : Program) [] s := ⟨_, rfl⟩
    have hu_eq : u = ⟨s.phase, writeBit (writeBit s.basis flag (s.basis flag ^^ s.basis g)) g (s.basis g ^^ (s.basis flag ^^ s.basis g))⟩ := by
      rw [uDef]; simp [run, writeBit, hgf]
    have hfl : s.basis flag = false := flagIn
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
    have uR : regValue L.r u.basis = oddWord X :=
      (regValue_congr _ _ _ (fun q hq => ukeep q (fun e => hgR (e ▸ hq)) (fun e => hfR (e ▸ hq)))).trans hR
    have uY : regValue L.y u.basis = oddWord X :=
      (regValue_congr _ _ _ (fun q hq => ukeep q (fun e => hgY (e ▸ hq)) (fun e => hfY (e ▸ hq)))).trans hY
    have hmid := hpad u rec uR uY uclean
    have hc_out : (run (paddedOddLoan44 L (base 512)) rec u).basis c = false := (hmid.2.2 c hcR).trans uc
    have hg_out : (run (paddedOddLoan44 L (base 512)) rec u).basis g = false := (hmid.2.2 g hgR).trans ug
    have hreb := FieldFrameOB5.rebind_swap_run c g (paddedOddLoan44 L (base 512)) u rec uc ug hc_out hg_out
    have hlw : run (ControlLoan1589.loanWindow g flag c (paddedOddLoan44 L (base 512))) rec s =
        run [.measureX flag [] [.Z g]] (rec.drop (measurementCount (renameProgram (Equiv.swap c g) (paddedOddLoan44 L (base 512)))))
          (run [.CX flag g] [] (run (paddedOddLoan44 L (base 512)) rec u)) := by
      have hlwSh : ControlLoan1589.loanWindow g flag c (paddedOddLoan44 L (base 512)) =
          [.CX g flag, .CX flag g] ++ (renameProgram (Equiv.swap c g) (paddedOddLoan44 L (base 512)) ++ ([.CX flag g] ++ [.measureX flag [] [.Z g]])) :=
        loanWindow_eq g flag c (paddedOddLoan44 L (base 512))
      rw [hlwSh, run_append, show measurementCount ([.CX g flag, .CX flag g] : Program) = 0 from by simp [measurementCount],
        List.take_zero, List.drop_zero, ← uDef, run_append, run_take, run_append,
        show measurementCount ([.CX flag g] : Program) = 0 from by simp [measurementCount], List.take_zero, List.drop_zero]
      rw [hreb]

    obtain ⟨w, wDef⟩ : ∃ w : State, w = run (paddedOddLoan44 L (base 512)) rec u := ⟨_, rfl⟩
    have hmid' : w.phase = u.phase ∧ regValue L.r w.basis = oddWord ((if u.basis L.sign then 1 else 3) * X) ∧
        ∀ a, a ∉ L.r → w.basis a = u.basis a := by rw [wDef]; exact hmid
    have hg_out' : w.basis g = false := by rw [wDef]; exact hg_out
    obtain ⟨v, vDef⟩ : ∃ v : State, v = run [.CX flag g] [] w := ⟨_, rfl⟩
    have hv_eq : v = ⟨w.phase, writeBit w.basis g (w.basis g ^^ w.basis flag)⟩ := by rw [vDef]; simp [run]
    have vfg : v.basis flag = v.basis g := by
      rw [hv_eq]; simp [writeBit, hgf.symm, hg_out']
    have hms := Rolling1588Lifetime.meas_sel flag g hgf.symm v vfg
      (rec.drop (measurementCount (renameProgram (Equiv.swap c g) (paddedOddLoan44 L (base 512)))))
    rw [hlw, ← wDef, ← vDef, hms]
    have hup : u.phase = s.phase := by rw [hu_eq]
    refine ⟨(by rw [hv_eq]; exact hmid'.1.trans hup), ?_, ?_⟩
    · have hvR : regValue L.r (writeBit v.basis flag false) = regValue L.r w.basis := by
        apply regValue_congr; intro q hq
        have qf : q ≠ flag := fun e => hfR (e ▸ hq)
        have qg : q ≠ g := fun e => hgR (e ▸ hq)
        rw [hv_eq]; simp [writeBit, qf, qg]
      have hls : L.sign = flag := rfl
      rw [hvR, hmid'.2.1, hls, uf]
    · intro a ha
      by_cases af : a = flag
      · subst af; simp [writeBit, hfl]
      · by_cases ag : a = g
        · subst ag
          rw [hv_eq]; simp only [writeBit, Function.update_of_ne hgf, Function.update_self, hg_out', Bool.false_xor]
          exact (hmid'.2.2 flag hfR).trans uf
        · rw [hv_eq]; simp only [writeBit, Function.update_of_ne af, Function.update_of_ne ag]
          exact (hmid'.2.2 a ha).trans (ukeep a ag af)
  -- Lift through shifted Placement5.pi0 and swap 760 717
  let P0 := ControlLoan1589.loanWindow g flag c (paddedOddLoan44 L (base 512))
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
  have hP2 : run endPacket760OddLoan44 m s = run P0 m s := by
    have hepSh : endPacket760OddLoan44 = renameProgram (Equiv.swap (base 760) (base 717)) (renameProgram (shifted Placement5.pi0) P0) :=
      endPacket760OddLoan44_eq
    rw [hepSh]
    rw [FieldFrameOB5.rebind_swap_run (base 760) (base 717) (renameProgram (shifted Placement5.pi0) P0) s m
      h760 h717 h760_out h717_out, hP1]
  rw [hP2]
  exact hraw m

end ConcreteEnd44

end

end ECDSAAdd.Entrant.OddFullPass.InverseTailCOdd
end
