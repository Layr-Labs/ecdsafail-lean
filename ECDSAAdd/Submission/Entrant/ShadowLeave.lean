import ECDSAAdd.Submission.Entrant.Window
import ECDSAAdd.Submission.Entrant.ShadowParts
import ECDSAAdd.Submission.Entrant.ShadowGeometry
import ECDSAAdd.Submission.Entrant.ShadowBox2
import ECDSAAdd.Submission.Entrant.ShadowBounds
import ECDSAAdd.Submission.Entrant.ShadowLeaveFacts
import ECDSAAdd.Submission.Entrant.ShadowEntryFacts
import ECDSAAdd.Submission.Entrant.ShadowRoute

/-! Shadow7 leave families: the generic leave proofs (`LeaveJ` and its companions) for the seven-bit shadow.
Generated from the stock families by build-leaves (helpers/shadow-leave/scripts/port.py), then edited where
smallness enters (far-only at the entry cutoff, `Shadow7.SmallIfFar` / `Shadow7.EndSmall`). -/

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
/-- Entry-cutoff smallness at the seven-bit shadow: far-only at entry, both branches at the end of the block. -/
def Small7 (b : Nat) (z : SkywalkNat.State) : Prop := Shadow7.SmallIfFar b 15 z ∧ Shadow7.EndSmall b z
end ECDSAAdd.Entrant.StairPacket.LeaveJ7
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far
open SkywalkNat SkywalkRails IntegerHigh LeaveSelector StairArchiveTrace
theorem orient (b : Nat) (z : SkywalkNat.State) (small : LeaveJ7.Small7 b z) (far : Shadow.far b 15 z) :
    decide (2^b≤z.u)=decide (z.v<z.u) :=
  LeaveTraceHistory.orient b z (small.1 far) far
end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far
open SkywalkNat SkywalkRails IntegerHigh LeaveSelector StairArchiveTrace
theorem certifiedChain (b : Nat) (z : SkywalkNat.State) (g s : Bool)
    (small : LeaveJ7.Small7 b z) (odd : z.v%2=1) (far : Shadow.far b 15 z) :
    chain (decide (2^b≤z.u)) (SkywalkTrace.trace 15 (encode g s z.u z.v)) :=
  LeaveTraceHistory.certifiedChain b z g s (small.1 far) odd far
end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far
open SkywalkNat SkywalkRails IntegerHigh LeaveSelector StairArchiveTrace
theorem firstSwap (b : Nat) (z : SkywalkNat.State) (g s : Bool)
    (small : LeaveJ7.Small7 b z) (odd : z.v%2=1) (far : Shadow.far b 15 z)
    (side : decide (2^b≤z.u)=false) :
    let xs:=SkywalkTrace.trace 15 (encode g s z.u z.v)
    ∀ i (hi : i<xs.length), i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u) :=
  LeaveTraceHistory.firstSwap b z g s (small.1 far) odd far side
end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far
open SkywalkNat IntegerHigh Shadow HighBankSum
theorem far_result (b w : Nat) (z : SkywalkNat.State) (small : LeaveJ7.Small7 b z)
    (far : Shadow.far b 15 z) (odd : z.v%2=1) (enough : high b 15 z+1<2^w) :
    let r:=reduced b 15 z
    let S:=total (step^[15] r)
    let F:=total (step^[15] z)
    let t:=if 2^b≤z.u then 0 else wait 15 z.u
    let d:=S/2^(b+1)/2^t
    let neg:=cross d && (!(decide (2^b≤z.u)) && negative (oddBits (letters 15 r)))
    d=(cross d).toNat+2*(!neg).toNat ∧
      F/2^(b+1)=2^t*HighBankAdjust.adjusted (high b 15 z) w (cross d) neg+S/2^(b+1)%2^t :=
  LeaveShadowRails.far_result b w z (small.1 far) far odd enough
end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror HighBankJoin HighBankReassemble
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

/-- The bank register read by the adjust (dadon's `Leave{s}High.ys`). -/
def ys (j : Fin 23) : List Wire := (List.range (Shadow7.wpP (start j))).map (Shadow7.bankW (start j))
/-- The adjust's carry pool (dadon's `Leave{s}High.carries`). -/
def carries (j : Fin 23) : List Wire := (List.range (Shadow7.wpP (start j) - 1)).map (Shadow7.poolW (start j))
theorem tags_mem (i : Nat) (hi : i < 16) : tagsP.getD i 0 ∈ tagsP := by
  rw [List.getD_eq_getElem _ _ (show i < tagsP.length by simp [tagsP]; omega)]; exact List.getElem_mem _
theorem tags_range' : ∀ q ∈ tagsP, 1556 ≤ q ∧ q ≤ 1576 := by decide

theorem layout (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : HighBankShift.Layout 1613 (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  refine ⟨fun i hi k hk e => Shadow7.bank_inj w1 w2 hi hk e, fun i hi e => ?_⟩
  have r := Shadow7.rail_win w1 w2; have b := Shadow7.bank_cases w1 w2 hi
  unfold Shadow7.wpP bTopP Shadow7.e0P at *; unfold Wire at *; omega

/-! Control: the one-hot tag parity selects the key bits (constant lists, decided once). -/

theorem selection0 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP0 = key.val.testBit 0 := by
  revert key; decide +kernel
theorem selection1 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP1 = key.val.testBit 1 := by
  revert key; decide +kernel
theorem selection2 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP2 = key.val.testBit 2 := by
  revert key; decide +kernel
theorem selection3 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP3 = key.val.testBit 3 := by
  revert key; decide +kernel

theorem controls_range : ∀ xs ∈ [controlsP0, controlsP1, controlsP2, controlsP3], 1613 ∉ xs ∧
    (∀ q ∈ xs, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ xs, q ∈ tagsP := by decide +kernel

theorem controls_out (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (xs : List Wire) (hx : ∀ q ∈ xs, 1556 ≤ q ∧ q ≤ 1576) :
    ∀ q ∈ xs, HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  intro q hq i hi e
  have r := Shadow7.rail_win w1 w2; have b := Shadow7.bank_cases w1 w2 hi; have := hx q hq
  unfold Shadow7.wpP bTopP Shadow7.e0P at *; unfold Wire at *; omega

/-! Barrel: four stages shift the bank by the key (dadon's `Leave{s}Barrel.value`). -/

theorem barrel_shape (s : Nat) : GateMirror.forward (Shadow7.leaveBarrel s) =
    HighBankBarrel.stage 1613 (Shadow7.bankW s) controlsP0 1 (Shadow7.wpP s) ++ HighBankBarrel.stage 1613 (Shadow7.bankW s) controlsP1 2 (Shadow7.wpP s + 1) ++
    HighBankBarrel.stage 1613 (Shadow7.bankW s) controlsP2 4 (Shadow7.wpP s + 3) ++ HighBankBarrel.stage 1613 (Shadow7.bankW s) controlsP3 8 (Shadow7.wpP s + 7) := by
  simp only [Shadow7.leaveBarrel, forward_app, forward_stageG]

/-- dadon's `Leave{s}BarrelBits.byDigits`: the four stages shift by the key read from the control parities. -/
theorem barrel_bits (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^(Shadow7.wpP (start j))) (h : HighBankBarrel.holds (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) x s) (clean : s.basis 1613 = false)
    (bit0 : HighBankControl.parity s.basis controlsP0 = key.val.testBit 0)
    (bit1 : HighBankControl.parity s.basis controlsP1 = key.val.testBit 1)
    (bit2 : HighBankControl.parity s.basis controlsP2 = key.val.testBit 2)
    (bit3 : HighBankControl.parity s.basis controlsP3 = key.val.testBit 3) :
    HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< key.val) s (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) m s) := by
  rw [barrel_shape]
  have L := layout j h0 (by omega)
  obtain ⟨c0, c1, c2, c3⟩ : (1613 ∉ controlsP0 ∧ (∀ q ∈ controlsP0, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP0, q ∈ tagsP) ∧
      (1613 ∉ controlsP1 ∧ (∀ q ∈ controlsP1, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP1, q ∈ tagsP) ∧
      (1613 ∉ controlsP2 ∧ (∀ q ∈ controlsP2, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP2, q ∈ tagsP) ∧
      (1613 ∉ controlsP3 ∧ (∀ q ∈ controlsP3, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP3, q ∈ tagsP) :=
    ⟨controls_range _ (by simp), controls_range _ (by simp), controls_range _ (by simp), controls_range _ (by simp)⟩
  have beginPass : ∀ m, HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< 0) s (run [] m s) := HighBankBarrel.start h
  have p1 : ∀ m, HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< (key.val % 2)) s
      (run ([] ++ HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP0 1 (Shadow7.wpP (start j))) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c0.1 (controls_out j h0 (by omega) _ c0.2.1) clean
      (HighBankBarrel.room small (by omega)) _ beginPass
    rw [bit0]
    exact (by decide +kernel : ∀ key : Fin 16, 0 + (if key.val.testBit 0 then 1 else 0) = (key.val % 2)) key
  have p2 : ∀ m, HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< (key.val % 4)) s
      (run ([] ++ HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP0 1 (Shadow7.wpP (start j)) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP1 2 (Shadow7.wpP (start j) + 1)) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c1.1 (controls_out j h0 (by omega) _ c1.2.1) clean
      (HighBankBarrel.room small (by have := Nat.mod_lt key.val (show 0 < 2 by decide); omega)) _ p1
    rw [bit1]
    exact (by decide +kernel : ∀ key : Fin 16, (key.val % 2) + (if key.val.testBit 1 then 2 else 0) = (key.val % 4)) key
  have p3 : ∀ m, HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< (key.val % 8)) s
      (run ([] ++ HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP0 1 (Shadow7.wpP (start j)) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP1 2 (Shadow7.wpP (start j) + 1) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP2 4 (Shadow7.wpP (start j) + 3)) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c2.1 (controls_out j h0 (by omega) _ c2.2.1) clean
      (HighBankBarrel.room small (by have := Nat.mod_lt key.val (show 0 < 4 by decide); omega)) _ p2
    rw [bit2]
    exact (by decide +kernel : ∀ key : Fin 16, (key.val % 4) + (if key.val.testBit 2 then 4 else 0) = (key.val % 8)) key
  have p4 : ∀ m, HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< key.val) s
      (run ([] ++ HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP0 1 (Shadow7.wpP (start j)) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP1 2 (Shadow7.wpP (start j) + 1) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP2 4 (Shadow7.wpP (start j) + 3) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP3 8 (Shadow7.wpP (start j) + 7)) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c3.1 (controls_out j h0 (by omega) _ c3.2.1) clean
      (HighBankBarrel.room small (by have := Nat.mod_lt key.val (show 0 < 8 by decide); omega)) _ p3
    rw [bit3]
    exact (by decide +kernel : ∀ key : Fin 16, (key.val % 8) + (if key.val.testBit 3 then 8 else 0) = key.val) key
  simpa only [List.nil_append] using p4 m

theorem controls_tags : (∀ q ∈ controlsP0, q ∈ tagsP) ∧ (∀ q ∈ controlsP1, q ∈ tagsP) ∧ (∀ q ∈ controlsP2, q ∈ tagsP) ∧
    (∀ q ∈ controlsP3, q ∈ tagsP) := by decide +kernel

/-- dadon's `Leave{s}Barrel.value`. -/
theorem barrel_value (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^(Shadow7.wpP (start j))) (h : HighBankBarrel.holds (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) x s) (clean : s.basis 1613 = false)
    (tags : ∀ q ∈ tagsP, s.basis q = decide (q = tagsP.getD key 0)) :
    HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< key.val) s (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) m s) := by
  have par : ∀ (xs : List Wire), (∀ q ∈ xs, q ∈ tagsP) →
      HighBankControl.parity s.basis xs = HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) xs :=
    fun xs hx => HighBankBarrel.parity_congr (fun q hq => tags q (hx q hq))
  obtain ⟨t0, t1, t2, t3⟩ := controls_tags
  exact barrel_bits j h0 (by omega) key x s m small h clean ((par _ t0).trans (selection0 key)) ((par _ t1).trans (selection1 key))
    ((par _ t2).trans (selection2 key)) ((par _ t3).trans (selection3 key))

/-! High: the adjust then the barrel (dadon's `Leave{s}High.result`). -/

theorem ys_length (j : Fin 23) : (ys j).length = Shadow7.wpP (start j) := by simp [ys]
theorem ys_getD (j : Fin 23) (i : Nat) (hi : i < Shadow7.wpP (start j)) : (ys j).getD i 0 = Shadow7.bankW (start j) i := by
  simp [ys, List.getD_eq_getElem?_getD, hi]

theorem adjust_nodup (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ((Shadow7.e0P (start j) + 6) :: (ys j ++ carries j)).Nodup := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  rw [List.nodup_cons, List.nodup_append]
  refine ⟨?_, ?_, Shadow7.pool_nodup _ _ w1 w2, ?_⟩
  · intro hm; rcases List.mem_append.mp hm with hm|hm
    · obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
      have b := Shadow7.bank_cases w1 w2 (i := i) (by omega); unfold Wire at *; omega
    · obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
      have p := Shadow7.pool_cases (i := i) w1 w2; unfold Wire at *; omega
  · exact List.Nodup.map_on (fun a ha b hb e => Shadow7.bank_inj w1 w2 (by rw [List.mem_range] at ha; omega)
      (by rw [List.mem_range] at hb; omega) e) List.nodup_range
  · intro a ha b hb e
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_range] at hi hk
    have bb := Shadow7.bank_cases w1 w2 (i := i) (by omega); have p := Shadow7.pool_cases (i := k) w1 w2
    unfold Wire at *; omega

theorem high_bits (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (key : Fin 16) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bit0 : HighBankControl.parity s.basis controlsP0 = key.val.testBit 0)
    (bit1 : HighBankControl.parity s.basis controlsP1 = key.val.testBit 1)
    (bit2 : HighBankControl.parity s.basis controlsP2 = key.val.testBit 2)
    (bit3 : HighBankControl.parity s.basis controlsP3 = key.val.testBit 3) :
    let x := HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (s.basis (Shadow7.e0P (start j) + 6)) (s.basis 1597)
    HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< key.val) s
      (run (GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j))) m s) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  let p := HighBankAdjust.adjust (ys j) (carries j) (Shadow7.e0P (start j) + 6) 1597
  have pe : GateMirror.forward (Shadow7.leaveAdjust (start j)) = p := by
    simp only [Shadow7.leaveAdjust, forward_adjustG, p, ys, carries]
  let t := run p m s
  let x := regValue (ys j) t.basis
  have negOut : (1597:Wire) ∉ ys j := by
    intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega); unfold Wire at *; omega
  have size : (carries j).length + 1 = (ys j).length := by simp [ys, carries]; omega
  have ht := HighBankAdjust.correct (ys j) (carries j) (Shadow7.e0P (start j) + 6) 1597 (adjust_nodup j h0 (by omega)) negOut size s m clean
  have small : x < 2^(Shadow7.wpP (start j)) := by have := regValue_lt (ys j) t.basis; rwa [ys_length] at this
  have notYs : ∀ i, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → Shadow7.bankW (start j) i ∉ ys j := by
    intro i a b hm; obtain ⟨k, hk, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hk
    have := Shadow7.bank_inj w1 w2 (i := k) (k := i) (by omega) b e; omega
  have data : HighBankBarrel.holds (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) x t := by
    intro i hi
    by_cases lo : i < Shadow7.wpP (start j)
    · rw [← ys_getD j i lo]
      exact HighBankAdjust.bit_read (ys j) i t.basis (by rw [ys_length]; exact lo)
    · rw [Nat.testBit_lt_two_pow (small.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
      exact (ht.2.1 _ (notYs i (by omega) hi)).trans (padding i (by omega) hi)
  have t1613 : (1613:Wire) ∉ ys j := by
    intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega); unfold Wire at *; omega
  have cold : t.basis 1613 = false := (ht.2.1 _ t1613).trans selectZero
  have untouched : ∀ q ∈ tagsP, q ∉ ys j := by
    intro q hq hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
    have tr := tags_range' q hq
    unfold Wire at *; omega
  have same : ∀ (xs : List Wire), (∀ q ∈ xs, q ∈ tagsP) →
      HighBankControl.parity t.basis xs = HighBankControl.parity s.basis xs :=
    fun xs hx => HighBankBarrel.parity_congr (fun q hq => ht.2.1 q (untouched q (hx q hq)))
  obtain ⟨t0, t1, t2, t3⟩ := controls_tags
  have action := barrel_bits j h0 (by omega) key x t (m.drop (measurementCount p)) small data cold
    ((same _ t0).trans bit0) ((same _ t1).trans bit1) ((same _ t2).trans bit2) ((same _ t3).trans bit3)
  have initial : x = HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (s.basis (Shadow7.e0P (start j) + 6))
      (s.basis 1597) := by rw [← ys_length j]; exact ht.2.2
  dsimp only
  rw [forward_app, pe, run_append, run_take, ← initial]
  refine ⟨action.bits, action.phase.trans ht.1, fun q h => (action.frame q h).trans (ht.2.1 q ?_)⟩
  intro member
  obtain ⟨i, hi, e⟩ := List.mem_map.mp member; rw [List.mem_range] at hi
  exact h i (by omega) e.symm

/-- dadon's `Leave{s}High.result`. -/
theorem high_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (key : Fin 16) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (one : ∀ q ∈ tagsP, s.basis q = decide (q = tagsP.getD key 0)) :
    let x := HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (s.basis (Shadow7.e0P (start j) + 6)) (s.basis 1597)
    HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< key.val) s
      (run (GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j))) m s) := by
  have par : ∀ (xs : List Wire), (∀ q ∈ xs, q ∈ tagsP) →
      HighBankControl.parity s.basis xs = HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) xs :=
    fun xs hx => HighBankBarrel.parity_congr (fun q hq => one q (hx q hq))
  obtain ⟨t0, t1, t2, t3⟩ := controls_tags
  exact high_bits j h0 (by omega) key s m clean selectZero padding ((par _ t0).trans (selection0 key))
    ((par _ t1).trans (selection1 key)) ((par _ t2).trans (selection2 key)) ((par _ t3).trans (selection3 key))

/-- dadon's `Leave{s}NearHigh.result`: all tags off, no shift. -/
theorem nearHigh_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (off : ∀ q ∈ tagsP, s.basis q = false) :
    let x := HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (s.basis (Shadow7.e0P (start j) + 6)) (s.basis 1597)
    HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) x s
      (run (GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j))) m s) := by
  have quiet : ∀ (xs : List Wire), (∀ q ∈ xs, q ∈ tagsP) → HighBankControl.parity s.basis xs = false := by
    intro xs sub
    induction xs with
    | nil => rfl
    | cons q qs ih =>
      simp only [HighBankControl.parity, off q (sub _ (by simp)), Bool.false_xor,
        ih (fun z h => sub _ (List.mem_cons_of_mem _ h))]
  obtain ⟨t0, t1, t2, t3⟩ := controls_tags
  have h := high_bits j h0 (by omega) 0 s m clean selectZero padding (quiet _ t0) (quiet _ t1) (quiet _ t2) (quiet _ t3)
  simpa only [Fin.val_zero, Nat.shiftLeft_zero] using h

/-! Join and Word: the digit pass and the word reassembly (dadon's `Leave{s}Join` / `Leave{s}Word.combine`). -/

def hot (key : Fin 16) (q : Wire) := decide (q = tagsP.getD key 0)
abbrev cols (j : Fin 23) : List Column := Shadow7.columnsP (start j)
theorem cols_length (j : Fin 23) : (cols j).length = 18 := by simp [cols, Shadow7.columnsP]
/-- dadon's `Leave{s}Word.row`. -/
abbrev row (j : Fin 23) (i : Fin 18) : Column := (cols j)[i.val]'(by rw [cols_length]; exact i.isLt)

theorem row_eq (j : Fin 23) (i : Fin 18) : (row j i).shadow = Shadow7.a0P (start j) + i.val ∧ (row j i).tube = Shadow7.bankW (start j) i.val ∧
    (row j i).low = decide (i.val < Shadow7.lowsP (start j)) ∧ (row j i).hot = if i.val < 16 then some (tagsP.getD i.val 0) else none := by
  simp [row, cols, Shadow7.columnsP]

/-- The schedule only reads the `hot` fields (identical at every block). -/
theorem schedule_hot (ref : BasisState) (key : Nat) : ∀ (a : Bool) (k : Nat) (rs rs' : List Column),
    rs.map (·.hot) = rs'.map (·.hot) → schedule ref key a k rs = schedule ref key a k rs'
  | _, _, [], [], _ => rfl
  | _, _, [], _::_, h => by simp at h
  | _, _, _::_, [], h => by simp at h
  | a, k, r::rs, r'::rs', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [schedule, h.1, schedule_hot ref key _ (k+1) rs rs' h.2]

theorem hots (j : Fin 23) : (cols j).map (·.hot) = (Shadow7.columnsP 225).map (·.hot) := by
  simp only [cols, Shadow7.columnsP, List.map_map]; rfl

theorem schedule_ok (j : Fin 23) (key : Fin 16) : schedule (hot key) key false 0 (cols j) = true := by
  rw [schedule_hot _ _ _ _ _ (Shadow7.columnsP 225) (hots j)]
  revert key; decide +kernel

theorem digitSites (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    DigitLayout (tagsP.getD · 0) (fun i => Shadow7.a0P (start j) + i) (Shadow7.e0P (start j) + 6) 1613 0 16 := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  refine ⟨fun i _ hi => ?_, fun i _ hi k _ hk => ?_⟩
  · have t := tags_range' _ (tags_mem i hi)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or, not_false_eq_true]
    unfold Wire at *; omega
  · have t := tags_range' _ (tags_mem i hi); unfold Wire at *; omega

theorem colSites (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : WellPlaced 1614 (cols j) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  refine ⟨fun c hc => ?_, fun c hc h hh => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
    dsimp only
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or, not_false_eq_true]
    unfold Wire at *; omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    have th : 1556 ≤ h ∧ h ≤ 1576 := by
      simp only at hh; split at hh
      · simp only [Option.mem_def, Option.some.injEq] at hh; subst hh; exact tags_range' _ (tags_mem i (by omega))
      · simp at hh
    refine ⟨by unfold Wire at *; omega, fun v hv => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv; rw [List.mem_range] at hk
    have b := Shadow7.bank_cases w1 w2 (i := k) (by omega)
    dsimp only; unfold Wire at *; omega

theorem disjoint (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : (cols j).Pairwise Apart := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  unfold cols Shadow7.columnsP
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) (List.pairwise_lt_range (n := 18))
  rw [List.mem_range] at ha hb
  have ba := Shadow7.bank_cases w1 w2 (i := a) (by omega); have bb := Shadow7.bank_cases w1 w2 (i := b) (by omega)
  have ne : Shadow7.bankW (start j) a ≠ Shadow7.bankW (start j) b := fun e => by have := Shadow7.bank_inj w1 w2 (by omega) (by omega) e; omega
  unfold Apart; dsimp only
  refine ⟨?_, ?_, ?_, ne⟩ <;> unfold Wire at * <;> omega

theorem join_shape (s : Nat) : GateMirror.forward (Shadow7.leaveJoin s) =
    digits (tagsP.getD · 0) (fun i => Shadow7.a0P s + i) (Shadow7.e0P s + 6) 1613 0 16 ++ word 1614 (Shadow7.columnsP s) := by
  simp only [Shadow7.leaveJoin, forward_app, forward_digitsG, forward_wordG]

theorem combine (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (key : Fin 16) (X H : Nat) (s : State) (m : List Bool)
    (tagsOn : ∀ q ∈ tagsP, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (Shadow7.a0P (start j) + i) = X.testBit i)
    (tube : ∀ i < 18, s.basis (Shadow7.bankW (start j) i) = (2^key.val*H).testBit i)
    (digit : X/2^key.val = (s.basis (Shadow7.e0P (start j) + 6)).toNat + 2*(s.basis 1613).toNat)
    (scratch : s.basis 1614 = false) :
    let out := run (GateMirror.forward (Shadow7.leaveJoin (start j))) m s
    out.phase = s.phase ∧
      (∀ i : Fin 18, out.basis (row j i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row j i).free = false) ∧
      ∀ q, (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) → out.basis q = s.basis q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  let ref := hot key
  let dp := digits (tagsP.getD · 0) (fun i => Shadow7.a0P (start j) + i) (Shadow7.e0P (start j) + 6) 1613 0 16
  let u := run dp m s
  have unique : ∀ i t : Fin 16, hot t (tagsP.getD i 0) = decide (i.val = t.val) := by decide +kernel
  have sel (i : Nat) (_ : 0 ≤ i) (hi : i < 0+16) : s.basis (tagsP.getD i 0) = decide (i = key.val) :=
    (tagsOn _ (tags_mem i hi)).trans (unique ⟨i, hi⟩ key)
  have z := digits_remainder (digitSites j h0 (by omega)) s m key.val (by omega) key.isLt sel X 18 (by decide)
    (fun i _ k _ eq => Nat.add_left_cancel eq) shadow digit
  have hits : ∀ c ∈ cols j, ∀ q ∈ c.hot, q ∈ tagsP := by
    intro c hc q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    simp only at hq; split at hq
    · simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; exact tags_mem i (by omega)
    · simp at hq
  have members : ∀ q ∈ tagsP, ∀ i : Nat, i ≤ 17 → q ≠ Shadow7.a0P (start j) + i := by
    intro q hq i hi; have := tags_range' q hq; unfold Wire at *; omega
  have ctrl : ∀ c ∈ cols j, ∀ q ∈ c.hot, u.basis q = ref q := by
    intro c hc q hq
    have mem := hits c hc q hq
    exact (z.2.2 q (members q mem key.val (by omega)) (members q mem (key.val+1) (by omega))).trans (tagsOn q mem)
  have inputs : columnsRead (cols j) u.basis X H key.val 0 := by
    intro i hi
    rw [cols_length] at hi
    have g := row_eq j ⟨i, hi⟩
    change u.basis (row j ⟨i, hi⟩).shadow = _ ∧ u.basis (row j ⟨i, hi⟩).tube = _
    rw [g.1, g.2.1]
    simp only [Nat.zero_add]
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
    refine ⟨z.2.1 i hi, (z.2.2 _ ?_ ?_).trans (tube i hi)⟩ <;> unfold Wire at * <;> omega
  have rz : u.basis 1614 = false := (z.2.2 _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)).trans scratch
  have word := reassemble 1614 (cols j) ref u m X H key.val (colSites j h0 (by omega)) (disjoint j h0 (by omega)) ctrl rz
    (schedule_ok j key) inputs
  dsimp only
  rw [join_shape, run_append, run_take, show measurementCount dp = 0 from (digits_counts _ _ _ _ _ _).2, List.drop_zero]
  refine ⟨word.1.trans z.1, fun i => word.2.1 i.val (by rw [cols_length]; exact i.isLt), ?_⟩
  intro q away
  have safe (k : Nat) (hk : k < 18) : q ≠ Shadow7.a0P (start j) + k := by
    have g := row_eq j ⟨k, hk⟩
    rw [← g.1]
    exact (away _ (List.getElem_mem _)).1
  exact (word.2.2 q away).trans (z.2.2 _ (safe key.val (by omega)) (safe (key.val+1) (by omega)))



/-- dadon's `Leave{s}NearWord.combine`: no tag hot, the word passes the shadows through. -/
theorem nearWord_combine (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (X : Nat) (bound : X < 2^18) (s : State)
    (m : List Bool) (off : ∀ q ∈ tagsP, s.basis q = false)
    (shadow : ∀ i < 18, s.basis (Shadow7.a0P (start j) + i) = X.testBit i)
    (tube : ∀ i < 18, s.basis (Shadow7.bankW (start j) i) = false)
    (scratch : s.basis 1614 = false) :
    let out := run (GateMirror.forward (Shadow7.leaveJoin (start j))) m s
    out.phase = s.phase ∧
      (∀ i : Fin 18, out.basis (row j i).keep = X.testBit i.val ∧ out.basis (row j i).free = false) ∧
      ∀ q, (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) → out.basis q = s.basis q := by
  let ref : BasisState := fun _ => false
  let dp := digits (tagsP.getD · 0) (fun i => Shadow7.a0P (start j) + i) (Shadow7.e0P (start j) + 6) 1613 0 16
  have none : run dp m s = s := by
    apply digits_quiet (digitSites j h0 (by omega))
    intro i _ hi
    exact off _ (tags_mem i hi)
  have sch : schedule ref 18 false 0 (cols j) = true := by
    rw [schedule_hot _ _ _ _ _ (Shadow7.columnsP 225) (hots j)]; decide +kernel
  have members : ∀ c ∈ cols j, ∀ q ∈ c.hot, q ∈ tagsP := by
    intro c hc q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    simp only at hq; split at hq
    · simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; exact tags_mem i (by omega)
    · simp at hq
  have inputs : columnsRead (cols j) s.basis X 0 18 0 := by
    intro i hi
    rw [cols_length] at hi
    have g := row_eq j ⟨i, hi⟩
    change s.basis (row j ⟨i, hi⟩).shadow = _ ∧ s.basis (row j ⟨i, hi⟩).tube = _
    rw [g.1, g.2.1]
    simp only [Nat.mod_eq_of_lt bound, Nat.zero_add, Nat.mul_zero, Nat.zero_testBit]
    exact ⟨shadow i hi, tube i hi⟩
  have v := reassemble 1614 (cols j) ref s m X 0 18 (colSites j h0 (by omega)) (disjoint j h0 (by omega))
    (fun a ha q h => off q (members a ha q h)) scratch sch inputs
  dsimp only
  rw [join_shape, run_append, run_take, show measurementCount dp = 0 from (digits_counts _ _ _ _ _ _).2, List.drop_zero, none]
  refine ⟨v.1, fun i => ?_, v.2.2⟩
  have hv := v.2.1 i.val (by rw [cols_length]; exact i.isLt)
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt bound] using hv

/-! Middle: adjust, barrel, sign bit, join (dadon's `Leave{s}Middle.result`; `middle` = cuts 8..24). -/

def middleOps (s : Nat) : List Gate := Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++ leaveFix8 s (Shadow7.sbP s) ++ Shadow7.leaveJoin s
theorem fix8_forward (s h : Nat) : GateMirror.forward (leaveFix8 s h) = [.X 1613, .CX 1597 1613] := rfl

theorem middle_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (key : Fin 16) (X : Nat) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (one : ∀ q ∈ tagsP, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (Shadow7.a0P (start j) + i) = X.testBit i)
    (digit : X/2^key.val = (s.basis (Shadow7.e0P (start j) + 6)).toNat + 2*(!s.basis 1597).toNat)
    (scratch : s.basis 1614 = false) :
    let H := HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (s.basis (Shadow7.e0P (start j) + 6)) (s.basis 1597)
    let out := run (GateMirror.forward (middleOps (start j))) m s
    out.phase = s.phase ∧
      (∀ i : Fin 18, out.basis (row j i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row j i).free = false) ∧
      (∀ i : Nat, 18 ≤ i → i < Shadow7.wpP (start j) + 15 → out.basis (Shadow7.bankW (start j) i) = (2^key.val*H).testBit i) ∧
      (∀ q, q ≠ 1613 → HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q → (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) →
        out.basis q = s.basis q) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  let H := HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (s.basis (Shadow7.e0P (start j) + 6)) (s.basis 1597)
  let early := GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j))
  let signBit : Program := [.X 1613, .CX 1597 1613]
  let v := run early m s
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have a := high_result j h0 (by omega) key s m clean selectZero padding one
  have bits (i : Nat) (hi : i < Shadow7.wpP (start j) + 15) : v.basis (Shadow7.bankW (start j) i) = (2^key.val*H).testBit i := by
    rw [Nat.mul_comm (2^key.val) H, ← Nat.shiftLeft_eq]
    exact a.bits i hi
  have unchanged (q : Wire) (ne : q ≠ 1613) : u.basis q = v.basis q := by simp [u, signBit, run, writeBit, Function.update, ne]
  have old (q : Wire) (ne : q ≠ 1613) (ext : HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q) : u.basis q = s.basis q :=
    (unchanged q ne).trans (a.frame q ext)
  have bankOut : ∀ q : Nat, (1556 ≤ q ∧ q ≤ 1597) ∨ (q ≤ 785) ∨ (Shadow7.e0P (start j) + 3 ≤ q ∧ q ≤ Shadow7.e0P (start j) + 9) →
      HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q := by
    intro q hq i hi e
    have b := Shadow7.bank_cases w1 w2 hi
    unfold Wire at *; omega
  have Shadow7.stable : ∀ i, i < Shadow7.wpP (start j) + 15 → (1613:Wire) ≠ Shadow7.bankW (start j) i := fun i hi => (layout j h0 (by omega)).separate i hi
  have readTags (q : Wire) (hq : q ∈ tagsP) : u.basis q = hot key q := by
    have t := tags_range' q hq
    exact (old q (by unfold Wire at *; omega) (bankOut q (Or.inl (by unfold Wire at *; omega)))).trans (one q hq)
  have readShadow (i : Nat) (hi : i < 18) : u.basis (Shadow7.a0P (start j) + i) = X.testBit i :=
    (old _ (by unfold Wire at *; omega) (bankOut _ (Or.inr (Or.inl (by omega))))).trans (shadow i hi)
  have readTube (i : Nat) (hi : i < 18) : u.basis (Shadow7.bankW (start j) i) = (2^key.val*H).testBit i :=
    (unchanged _ (Shadow7.stable i (by omega)).symm).trans (bits i (by omega))
  have select : v.basis 1613 = false := (a.frame _ (layout j h0 (by omega)).separate).trans selectZero
  have neg : v.basis 1597 = s.basis 1597 := a.frame _ (bankOut 1597 (Or.inl (by omega)))
  have d1 : u.basis 1613 = !s.basis 1597 := by
    simp [u, signBit, run, writeBit, Function.update, select, neg]
  have cross := old (Shadow7.e0P (start j) + 6) (by unfold Wire at *; omega) (bankOut _ (Or.inr (Or.inr (by omega))))
  have zero := (old 1614 (by decide) (fun i hi e => by
    have b := Shadow7.bank_cases w1 w2 hi; unfold Wire at *; omega)).trans scratch
  have exactDigit : X / 2^key.val = (u.basis (Shadow7.e0P (start j) + 6)).toNat + 2*(u.basis 1613).toNat := by
    rw [cross, d1]; exact digit
  have word := combine j h0 (by omega) key X H u tape readTags readShadow readTube exactDigit zero
  dsimp only
  have parts : GateMirror.forward (middleOps (start j)) = early ++ (signBit ++ GateMirror.forward (Shadow7.leaveJoin (start j))) := by
    simp only [middleOps, early, signBit, forward_app, fix8_forward, List.append_assoc]
  rw [parts, run_append, run_take, run_append, run_take, show measurementCount signBit = 0 from rfl, List.drop_zero]
  refine ⟨word.1.trans a.phase, word.2.1, ?_, ?_⟩
  · intro i lo hi
    have outsideRows : ∀ c ∈ cols j, Shadow7.bankW (start j) i ≠ c.shadow ∧ Shadow7.bankW (start j) i ≠ c.tube := by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk
      have b := Shadow7.bank_cases w1 w2 hi
      refine ⟨by dsimp only; unfold Wire at *; omega, fun e => ?_⟩
      have := Shadow7.bank_inj w1 w2 hi (by omega) e; omega
    exact (word.2.2 _ outsideRows).trans ((unchanged _ (Shadow7.stable i hi).symm).trans (bits i hi))
  · intro q ne ext away
    exact (word.2.2 q away).trans ((unchanged q ne).trans (a.frame q ext))

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror PortalAnd
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

def longPairs (j : Fin 23) : List (Wire × Wire) := (List.range 18).map (fun i => (Shadow7.b0P (start j) + i, 1557 + i))
def fullA (j : Fin 23) : List Wire := (List.range 18).map (Shadow7.a0P (start j) + ·)
def fullM (j : Fin 23) : List Wire := (List.range 18).map (Shadow7.b0P (start j) + ·)
def fullC : List Wire := (List.range 17).map (1559 + ·)
def smallA (j : Fin 23) : List Wire := (List.range (Shadow7.lowsP (start j))).map (Shadow7.a0P (start j) + ·)
def smallM (j : Fin 23) : List Wire := (List.range (Shadow7.lowsP (start j))).map (Shadow7.b0P (start j) + ·)
def smallC (j : Fin 23) : List Wire := (List.range (Shadow7.lowsP (start j) - 1)).map (1559 + ·)
/-- dadon's `mask`: `[.X 1557, .CX (a0-1) 1557, .CCX (b0-1) 1557 1558]`. -/
def maskP (j : Fin 23) : Program := [.X 1557, .CX (Shadow7.a0P (start j) - 1) 1557, .CCX (Shadow7.b0P (start j) - 1) 1557 1558]

/-- `leaveFix2` = long latch ++ mask ++ companion erase (dadon's cuts 93/169/172/242). -/
theorem fix2_parts : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 →
    GateMirror.forward (leaveFix2 (start j) (Shadow7.sbP (start j))) =
      latch true none 1556 (Shadow7.b0P (start j) - 1) (longPairs j) ++ (maskP j ++
        Companion.erase (fullA j) (fullM j) fullC 1556 1558) := by
  decide +kernel

theorem long_layout : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 →
    (1556 :: (Shadow7.b0P (start j) - 1) :: PortalAnd.sites (longPairs j)).Nodup := by
  decide +kernel

theorem full_geometry : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 →
    Companion.Geometry (fullA j) (fullM j) fullC 1556 1558 := by
  intro j h0 h1
  constructor <;> revert j <;> decide +kernel

/-- dadon's `long_run`. -/
theorem long_run (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (clean : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    run (latch true none 1556 (Shadow7.b0P (start j) - 1) (longPairs j)) m s =
      ⟨s.phase, writeBit s.basis 1556 (s.basis 1556 ^^ ((digits (Shadow7.b0P (start j) - 1) (longPairs j)).any s.basis))⟩ := by
  simpa only [active, Option.elim_none, Bool.true_and] using
    run_latch true none 1556 (Shadow7.b0P (start j) - 1) (longPairs j) (long_layout j h0 (by omega)) (by simp) s m clean

/-- dadon's `erase_run`. -/
theorem erase_run (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (clean : ∀ q ∈ fullC, s.basis q = false)
    (input : (regValue (fullM j) s.basis + (s.basis 1558).toNat) % 2^(fullM j).length =
      copyValue (some 1556) s.basis (regValue (fullA j) s.basis)) :
    let e := Companion.erase (fullA j) (fullM j) fullC 1556 1558
    (run e m s).phase = s.phase ∧ (∀ q, q ∉ fullM j → (run e m s).basis q = s.basis q) ∧
      regValue (fullM j) (run e m s).basis = 0 :=
  Companion.clear (fullA j) (fullM j) fullC 1556 1558 (full_geometry j h0 (by omega)) s m clean input

/-! The low-store restore (generic): `Shadow7.lowRest` = companion restore ++ release mask. -/

def releaseMaskP (j : Fin 23) : Program :=
  [.measureX 1558 [] [.CZ (Shadow7.b0P (start j) - 1) 1557], .CX (Shadow7.a0P (start j) - 1) 1557, .X 1557]

theorem forward_xsG' (xs : List Wire) : GateMirror.forward (xsG xs) = notRegister xs := by
  simp only [xsG, GateMirror.forward, notRegister, List.map_map]; rfl

theorem copy_map (c : Wire) (f g : Nat → Wire) : ∀ xs : List Nat,
    copyRegister (some c) (xs.map f) (xs.map g) = xs.map (fun i => Instr.CCX c (f i) (g i))
  | [] => rfl
  | x::xs => by simp only [List.map_cons, copyRegister, copyGate, copy_map c f g xs]; rfl

theorem lowRest_parts (j : Fin 23) :
    GateMirror.forward (Shadow7.lowRest (start j)) =
      Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558 ++ releaseMaskP j := by
  have hc : GateMirror.forward ((List.range (Shadow7.lowsP (start j))).map
      (fun i => Gate.ccx 1556 (Shadow7.a0P (start j) + i) (Shadow7.b0P (start j) + i))) =
      copyRegister (some 1556) (smallA j) (smallM j) := by
    rw [smallA, smallM, copy_map]; simp only [GateMirror.forward, List.map_map]; rfl
  simp only [Shadow7.lowRest, forward_app, forward_addG, forward_xsG', hc, Companion.restore, HighBankUnit.sub, mappedSub,
    smallM, smallC, List.append_assoc]
  rfl

theorem small_geometry : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 →
    Companion.Geometry (smallA j) (smallM j) (smallC j) 1556 1558 := by
  intro j h0 h1
  constructor <;> revert j <;> decide +kernel

/-- dadon's `restore_run`. -/
theorem restore_run (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (clean : ∀ q ∈ smallC j, s.basis q = false) (input : regValue (smallM j) s.basis = 0) :
    let r := Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558
    (run r m s).phase = s.phase ∧ (∀ q, q ∉ smallM j → (run r m s).basis q = s.basis q) ∧
      regValue (smallM j) (run r m s).basis =
        (copyValue (some 1556) s.basis (regValue (smallA j) s.basis) + 2^(smallM j).length - (s.basis 1558).toNat) %
          2^(smallM j).length :=
  Companion.write (smallA j) (smallM j) (smallC j) 1556 1558 (small_geometry j h0 (by omega)) s m clean input

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror PortalAnd RailPair PortalValues LeaveReadoutFrame LeaveCompanion
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3000000

/-- dadon's `Leave{s}InputScan.pairs`: the 19 low columns `(a0-1+i, b0-1+i)`. -/
def scanPairs (j : Fin 23) : List (Wire × Wire) :=
  (List.range 19).map (fun i => (Shadow7.a0P (start j) - 1 + i, Shadow7.b0P (start j) - 1 + i))

theorem scan_emitted : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 →
    GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j))) =
      scan (Shadow7.a0P (start j) + 17) (Shadow7.b0P (start j) + 17) (start j + 30) (Shadow7.e0P (start j) + 5) (scanPairs j) := by
  decide +kernel

theorem scan_layout : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 →
    ScanGeometry (Shadow7.a0P (start j) + 17) (Shadow7.b0P (start j) + 17) (start j + 30) (Shadow7.e0P (start j) + 5) (scanPairs j) := by
  intro j h0 h1
  constructor <;> revert j <;> decide +kernel

/-- The scan reads the stock packet's ports of block `j` (above bit `sb`). -/
theorem scan_ports : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 →
    (scanPairs j).map Prod.fst = ((IntegerPacket.ports (Shadow7.shape j) 15).a.drop (Shadow7.sbP (start j))).map (windowNet j) ∧
    (scanPairs j).map Prod.snd = ((IntegerPacket.ports (Shadow7.shape j) 15).b.drop (Shadow7.sbP (start j))).map (windowNet j) ∧
    Shadow7.a0P (start j) + 17 = windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).aSign ∧
    Shadow7.b0P (start j) + 17 = windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).bSign ∧
    start j + 30 = windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).previous ∧
    Shadow7.sbP (start j) ≤ (IntegerPacket.ports (Shadow7.shape j) 15).a.length ∧
    Shadow7.sbP (start j) ≤ (IntegerPacket.ports (Shadow7.shape j) 15).b.length := by
  decide +kernel

theorem scanPairs_getD (j : Fin 23) (i : Nat) (hi : i < 19) :
    ((scanPairs j).map Prod.fst).getD i 0 = Shadow7.a0P (start j) - 1 + i ∧
    ((scanPairs j).map Prod.snd).getD i 0 = Shadow7.b0P (start j) - 1 + i := by
  simp [scanPairs, List.getD_eq_getElem?_getD, hi]

/-- dadon's `Leave{s}InputScan.result`. -/
theorem inputScan_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (tape : List Bool) (u v : Nat)
    (G sg : Bool) (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) s.basis) (fresh : s.basis (Shadow7.e0P (start j) + 5) = false) :
    let t := run (GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j)))) tape s
    let e := negative sg u
    t.phase = s.phase ∧ t.basis (Shadow7.e0P (start j) + 5) = e ∧
      (∀ i < 19, t.basis (Shadow7.a0P (start j) - 1 + i) = ((u+v)/2^(Shadow7.sbP (start j))).testBit i ∧
        t.basis (Shadow7.b0P (start j) - 1 + i) = ((u - e.toNat)/2^(Shadow7.sbP (start j))).testBit i) ∧
      ∀ q, q ≠ Shadow7.e0P (start j) + 5 → q ∉ RailPair.sites (scanPairs j) → t.basis q = s.basis q := by
  obtain ⟨pl, pr, pa, pb, pg, la, lb⟩ := scan_ports j h0 (by omega)
  rw [scan_emitted j h0 (by omega)]
  generalize ht : run (scan (Shadow7.a0P (start j) + 17) (Shadow7.b0P (start j) + 17) (start j + 30) (Shadow7.e0P (start j) + 5) (scanPairs j)) tape s = t
  have out := scanRouted_shadow7 j (Shadow7.sbP (start j)) _ _ _ _ (scanPairs j) (scan_layout j h0 (by omega)) pl pr pa pb pg s tape u v G sg ready
    fresh la lb
  have frame := scan_run _ _ _ _ _ (scan_layout j h0 (by omega)) s tape fresh
  rw [ht] at out frame
  refine ⟨frame.1, out.1, ?_, frame.2.2.1⟩
  intro i hi
  have g := scanPairs_getD j i hi
  have len : ((scanPairs j).map Prod.fst).length = 19 ∧ ((scanPairs j).map Prod.snd).length = 19 := by simp [scanPairs]
  rw [← g.1, ← g.2, HighBankAdjust.bit_read ((scanPairs j).map Prod.fst) i t.basis (by rw [len.1]; exact hi),
    HighBankAdjust.bit_read ((scanPairs j).map Prod.snd) i t.basis (by rw [len.2]; exact hi), out.2.1, out.2.2]
  exact ⟨rfl, rfl⟩

/-- dadon's `Leave{s}CompanionInput.decode`. -/
theorem companionInput_decode (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (u v sign : Nat)
    (magFit : (u-sign)/2^(Shadow7.sbP (start j)) < 2^19)
    (bits : ∀ i < 19, s.basis (Shadow7.a0P (start j) - 1 + i) = ((u+v)/2^(Shadow7.sbP (start j))).testBit i ∧
      s.basis (Shadow7.b0P (start j) - 1 + i) = ((u-sign)/2^(Shadow7.sbP (start j))).testBit i) :
    ((digits (Shadow7.b0P (start j) - 1) (longPairs j)).any s.basis = decide (2^(Shadow7.sbP (start j)) ≤ u-sign)) ∧
      (s.basis (Shadow7.b0P (start j) - 1) && !s.basis (Shadow7.a0P (start j) - 1)).toNat = upperBorrow (2^(Shadow7.sbP (start j))) u v sign ∧
      regValue (fullA j) s.basis = ((u+v)/2^(Shadow7.sbP (start j) + 1)) % 2^18 ∧
      regValue (fullM j) s.basis = ((u-sign)/2^(Shadow7.sbP (start j) + 1)) % 2^18 := by
  have dlen : (digits (Shadow7.b0P (start j) - 1) (longPairs j)).length = 19 := by simp [digits, longPairs]
  have mag := EnterProof.value_of_bits (digits (Shadow7.b0P (start j) - 1) (longPairs j)) s.basis ((u-sign)/2^(Shadow7.sbP (start j))) (by
    intro i hi
    rw [dlen] at hi
    have geom : (digits (Shadow7.b0P (start j) - 1) (longPairs j)).getD i 0 = Shadow7.b0P (start j) - 1 + i := by
      rcases i with _ | i
      · simp [digits]
      · have : i < 18 := by omega
        simp [digits, longPairs, List.getD_eq_getElem?_getD, this]
        have r := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
        unfold Wire at *; omega
    rw [geom]; exact (bits i hi).2)
  rw [dlen, Nat.mod_eq_of_lt magFit] at mag
  have pos : 0 < 2^(Shadow7.sbP (start j)) := Nat.two_pow_pos _
  have half2 : ∀ x : Nat, x / 2^(Shadow7.sbP (start j) + 1) = (x / 2^(Shadow7.sbP (start j))) / 2^1 := by
    intro x; rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [any_positive, mag]
    simp only [Nat.div_pos_iff, pos, true_and]
  · have bs := bits 0 (by decide)
    simp only [Nat.add_zero] at bs
    rw [bs.1, bs.2]; exact borrowBit (2^(Shadow7.sbP (start j))) u v sign pos
  · apply EnterProof.value_of_bits (fullA j)
    intro i hi
    have hl : (fullA j).length = 18 := by simp [fullA]
    rw [hl] at hi
    have geom : (fullA j).getD i 0 = Shadow7.a0P (start j) - 1 + (i+1) := by
      simp [fullA, List.getD_eq_getElem?_getD, hi]
      have r := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
      unfold Wire at *; omega
    rw [geom, half2, Nat.testBit_div_two_pow, Nat.add_comm i 1]
    exact (bits (1+i) (show 1 + i < 19 by omega)).1
  · apply EnterProof.value_of_bits (fullM j)
    intro i hi
    have hl : (fullM j).length = 18 := by simp [fullM]
    rw [hl] at hi
    have geom : (fullM j).getD i 0 = Shadow7.b0P (start j) - 1 + (i+1) := by
      simp [fullM, List.getD_eq_getElem?_getD, hi]
      have r := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
      unfold Wire at *; omega
    rw [geom, half2, Nat.testBit_div_two_pow, Nat.add_comm i 1]
    exact (bits (1+i) (show 1 + i < 19 by omega)).2


end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror PortalAnd RailPair PortalValues LeaveReadoutFrame LeaveCompanion
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3000000
attribute [local irreducible] run SkywalkNat.step leaveFix0 leaveFix1 leaveFix2 latch Companion.erase

/-- dadon's `Leave{s}EraseActual.result`: the long latch, the mask and the companion erase (`leaveFix2`). -/
theorem eraseActual_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (tape : List Bool) (u v sign : Nat)
    (se : sign ≤ 1) (su : sign ≤ u) (small : min u v < 2^(Shadow7.sbP (start j))) (magFit : (u-sign)/2^(Shadow7.sbP (start j)) < 2^19)
    (bits : ∀ i < 19, s.basis (Shadow7.a0P (start j) - 1 + i) = ((u+v)/2^(Shadow7.sbP (start j))).testBit i ∧
      s.basis (Shadow7.b0P (start j) - 1 + i) = ((u-sign)/2^(Shadow7.sbP (start j))).testBit i)
    (clean : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temps : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    let t := run (GateMirror.forward (leaveFix2 (start j) (Shadow7.sbP (start j)))) tape s
    t.phase = s.phase ∧ regValue (fullM j) t.basis = 0 ∧ t.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ u-sign) ∧
      (t.basis 1558).toNat = upperBorrow (2^(Shadow7.sbP (start j))) u v sign ∧
      ∀ q, q ∉ 1556::1557::1558::fullM j → t.basis q = s.basis q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have hA : (1556:Nat) ≠ Shadow7.a0P (start j) - 1 ∧ (1557:Nat) ≠ Shadow7.a0P (start j) - 1 ∧ (1558:Nat) ≠ Shadow7.a0P (start j) - 1 ∧
      (1556:Nat) ≠ Shadow7.b0P (start j) - 1 ∧ (1557:Nat) ≠ Shadow7.b0P (start j) - 1 ∧ (1558:Nat) ≠ Shadow7.b0P (start j) - 1 ∧
      Shadow7.a0P (start j) - 1 ≠ Shadow7.b0P (start j) - 1 := by omega
  have d := companionInput_decode j h0 (by omega) s u v sign magFit bits
  dsimp only
  rw [fix2_parts j h0 (by omega), run_append, run_take, run_append, run_take]
  generalize hl : run (latch true none 1556 (Shadow7.b0P (start j) - 1) (longPairs j)) tape s = l
  generalize hs1 : tape.drop (measurementCount (latch true none 1556 (Shadow7.b0P (start j) - 1) (longPairs j))) = s1
  have flag : l = ⟨s.phase, writeBit s.basis 1556 (decide (2^(Shadow7.sbP (start j)) ≤ u-sign))⟩ := by
    rw [← hl, long_run j h0 (by omega) s tape temps, d.1, clean _ (by simp), Bool.false_xor]
  have base (q : Wire) (h : q ≠ 1556) : l.basis q = s.basis q := by rw [flag]; simp [writeBit, h]
  have hlA : l.basis (Shadow7.a0P (start j) - 1) = s.basis (Shadow7.a0P (start j) - 1) := base _ (fun e => hA.1 (by unfold Wire at *; omega))
  have hlB : l.basis (Shadow7.b0P (start j) - 1) = s.basis (Shadow7.b0P (start j) - 1) := base _ (fun e => hA.2.2.2.1 (by unfold Wire at *; omega))
  have nd : [Shadow7.a0P (start j) - 1, Shadow7.b0P (start j) - 1, (1557:Wire), 1558].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or,
      not_false_eq_true]; unfold Wire at *; omega
  have m57 : l.basis 1557 = false := (base _ (by decide)).trans (clean _ (by simp))
  have m58 : l.basis 1558 = false := (base _ (by decide)).trans (clean _ (by simp))
  have mo := mask_open (Shadow7.a0P (start j) - 1) (Shadow7.b0P (start j) - 1) 1557 1558 l s1 nd m57 m58
  rw [show (maskP j) = [.X 1557, .CX (Shadow7.a0P (start j) - 1) 1557, .CCX (Shadow7.b0P (start j) - 1) 1557 1558] from rfl, mo]
  generalize hw : (⟨l.phase, writeBit (writeBit l.basis 1557 (!l.basis (Shadow7.a0P (start j) - 1))) 1558
    (l.basis (Shadow7.b0P (start j) - 1) && !l.basis (Shadow7.a0P (start j) - 1))⟩ : State) = w
  have wphase : w.phase = s.phase := by rw [← hw, flag]
  have kept (q : Wire) (h : q ∉ [1556, 1557, 1558]) : w.basis q = s.basis q := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    rw [← hw]; simp only [writeBit, Function.update, h.2.1, h.2.2, dif_neg, not_false_eq_true]; exact base q h.1
  have isLong : w.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ u-sign) := by
    rw [← hw, flag]; simp [writeBit]
  have borrow : (w.basis 1558).toNat = upperBorrow (2^(Shadow7.sbP (start j))) u v sign := by
    rw [← hw]; simp only [writeBit, Function.update_self, hlA, hlB]; exact d.2.1
  have same (rs : List Wire) (ok : ∀ q ∈ rs, q ∉ [1556, 1557, 1558]) : regValue rs w.basis = regValue rs s.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h => kept _ (ok q h))
  have cOut : ∀ q ∈ fullC, q ∉ [1556, 1557, 1558] := by decide
  have cs : ∀ q ∈ fullC, w.basis q = false := by
    intro q h; rw [kept q (cOut q h)]; exact clean _ (by simp [h])
  have aOut : ∀ q ∈ fullA j, q ∉ [1556, 1557, 1558] := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; unfold Wire at *; omega
  have mOut : ∀ q ∈ fullM j, q ∉ [1556, 1557, 1558] := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; unfold Wire at *; omega
  have mlen : (fullM j).length = 18 := by simp [fullM]
  have condition : (regValue (fullM j) w.basis + (w.basis 1558).toNat) % 2^(fullM j).length =
      copyValue (some 1556) w.basis (regValue (fullA j) w.basis) := by
    rw [same (fullM j) mOut, same (fullA j) aOut, d.2.2.1, d.2.2.2, borrow, mlen]
    have twice : 2*2^(Shadow7.sbP (start j)) = 2^(Shadow7.sbP (start j) + 1) := by rw [Nat.pow_succ]; omega
    have calcValue := upper_clear (2^(Shadow7.sbP (start j))) u v sign (2^18) (Nat.two_pow_pos _) se su small
    rw [twice] at calcValue
    simpa only [copyValue, isLong, decide_eq_true_eq] using calcValue
  have e := erase_run j h0 (by omega) w (s1.drop (measurementCount (maskP j))) cs condition
  have extern (q : Wire) (notM : q ∉ fullM j) :
      (run (Companion.erase (fullA j) (fullM j) fullC 1556 1558) (s1.drop (measurementCount (maskP j))) w).basis q =
        w.basis q := e.2.1 q notM
  refine ⟨e.1.trans wphase, e.2.2, (extern _ (fun h => mOut _ h (by simp))).trans isLong, ?_, ?_⟩
  · have h158 := extern 1558 (fun h => (mOut 1558 h) (by simp))
    simp only [maskP] at h158
    rw [h158]
    exact borrow
  · intro q out
    simp only [List.mem_cons, not_or] at out
    exact (extern _ out.2.2.2).trans (kept _ (by simp [out.1, out.2.1, out.2.2.1]))

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror PortalAnd RailPair PortalValues LeaveReadoutFrame LeaveCompanion LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3000000

/-- dadon's `Leave{s}Front.entry` (= `leave.take 242`). -/
def entryOps (s : Nat) : List Gate := leaveFix0 s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ leaveFix2 s (Shadow7.sbP s)
/-- dadon's `Leave{s}Close.history`: the block's 15 history letters `s+16 .. s+30`. -/
def history (j : Fin 23) : List Wire := (List.range 15).map (start j + 16 + ·)
/-- dadon's `Leave{s}Selector.ports`. -/
def ports (j : Fin 23) : Ports := ⟨start j + 16, Shadow7.a0P (start j), Shadow7.e0P (start j) + 6, Shadow7.e0P (start j) + 7⟩
/-- dadon's `Leave{s}FrontReady.watched`. -/
def watched (j : Fin 23) : List Wire := [Shadow7.e0P (start j) + 6, Shadow7.e0P (start j) + 7] ++ List.range' 1559 39

theorem fix1_forward (s h : Nat) : GateMirror.forward (leaveFix1 s h) = notRegister ((List.range 15).map (s + 16 + ·)) := rfl

/-- Nodup of the history letters, proved outside `entry_core` so `omega` does not see the walk context. -/
theorem history_nodup (j : Fin 23) : ((List.range 15).map (start j + 16 + ·)).Nodup :=
  List.Nodup.map (fun _ _ e => by omega) List.nodup_range

theorem scratchWire_band {q : Nat}
    (h : q ∈ (1556 :: 1557 :: 1558 :: fullC : List Nat)) : 1556 ≤ q ∧ q ≤ 1575 := by
  simp only [List.mem_cons, fullC, List.mem_map, List.mem_range] at h
  rcases h with rfl | rfl | rfl | ⟨i, hi, rfl⟩
  · exact ⟨Nat.le_refl _, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by omega, by omega⟩

theorem longTemp_band (j : Fin 23) {p : Wire × Wire} (h : p ∈ longPairs j) :
    1557 ≤ p.2 ∧ p.2 ≤ 1574 := by
  simp only [longPairs, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  refine ⟨Nat.le_add_right 1557 i, ?_⟩
  exact le_trans (Nat.add_le_add_left (Nat.le_of_lt_succ hi) 1557) (by decide : 1557 + 17 ≤ 1574)

/-! Arithmetic that `entry_core` needs, proved here so `omega` never sees `Shadow7.onRails` or `Shadow7.rail_win`. -/

theorem sb_lo (s : Nat) (hs : s ≤ 375) : 61 ≤ Shadow7.sbP s := by
  simp only [Shadow7.sbP]
  omega

theorem sb_hi (s : Nat) (hs : 90 ≤ s) : Shadow7.sbP s ≤ 204 := by
  simp only [Shadow7.sbP]
  have h := Nat.div_le_div_right (c := 2) (show 513 - s ≤ 423 by omega)
  have e : 423 / 2 = 211 := by decide
  omega

theorem a0_le (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : Shadow7.a0P (start j) ≤ 633 := by
  have w := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  simp only [Shadow7.a0P]
  have sb := sb_hi (start j) w.1
  omega

theorem b0_ge (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : 848 ≤ Shadow7.b0P (start j) := by
  have w := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  simp only [Shadow7.b0P]
  have sb := sb_lo (start j) (by simp only [StairPacket.start]; omega)
  omega

theorem b0_le (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : Shadow7.b0P (start j) ≤ 998 := by
  have w := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  simp only [Shadow7.b0P]
  have sb := sb_hi (start j) w.1
  omega

theorem aCol_above (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) :
    start j + 30 < Shadow7.a0P (start j) - 1 + i := by
  have sb := sb_lo (start j) (by simp only [StairPacket.start]; omega)
  simp only [Shadow7.a0P]
  omega

theorem bCol_above (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) :
    start j + 30 < Shadow7.b0P (start j) - 1 + i := by
  have hb : 848 ≤ Shadow7.b0P (start j) := b0_ge j h0 (by omega)
  have one : 1 ≤ Shadow7.b0P (start j) := le_trans (by decide) hb
  have low : 847 ≤ Shadow7.b0P (start j) - 1 := by simpa using Nat.sub_le_sub_right hb 1
  have base : 847 ≤ Shadow7.b0P (start j) - 1 + i := le_trans low (Nat.le_add_right _ i)
  have top : start j + 30 ≤ 420 := by
    have := (start_win j h0 (by omega)).2
    omega
  exact Nat.lt_of_le_of_lt top (Nat.lt_of_lt_of_le (by decide : (420 : Nat) < 847) base)

theorem flag_ge (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : 1640 ≤ Shadow7.e0P (start j) + 5 := by
  have sb := sb_lo (start j) (by simp only [StairPacket.start]; omega)
  simp only [Shadow7.e0P]
  omega

theorem flag_above (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    start j + 30 < Shadow7.e0P (start j) + 5 := by
  have top : start j + 30 ≤ 420 := by
    have := (start_win j h0 (by omega)).2
    omega
  exact Nat.lt_of_le_of_lt top (Nat.lt_of_lt_of_le (by decide : (420 : Nat) < 1640) (flag_ge j h0 (by omega)))

theorem aCol_le (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) (hi : i < 19) :
    Shadow7.a0P (start j) - 1 + i ≤ 650 := by
  have ile : i ≤ 18 := Nat.le_of_lt_succ hi
  have ha : Shadow7.a0P (start j) ≤ 633 := a0_le j h0 (by omega)
  have one : 1 ≤ Shadow7.a0P (start j) := by
    simp only [Shadow7.a0P]
    exact le_trans (by decide : (1 : Nat) ≤ 32) (Nat.le_add_left 32 (start j + Shadow7.sbP (start j)))
  calc Shadow7.a0P (start j) - 1 + i
      ≤ Shadow7.a0P (start j) - 1 + 18 := Nat.add_le_add_left ile _
    _ = Shadow7.a0P (start j) + 17 := by
        rw [show (18 : Nat) = 1 + 17 from rfl, ← Nat.add_assoc, Nat.sub_add_cancel one]
    _ ≤ 633 + 17 := Nat.add_le_add_right ha 17
    _ = 650 := by decide

theorem aCol_out (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) (hi : i < 19) :
    Shadow7.a0P (start j) - 1 + i ∉ (1556 :: 1557 :: 1558 :: fullM j : List Nat) := by
  intro h
  have up := aCol_le j h0 (by omega) i hi
  have hb := b0_ge j h0 (by omega)
  simp only [List.mem_cons, fullM, List.mem_map, List.mem_range] at h
  rcases h with h1 | h1 | h1 | ⟨k, hk, h1⟩
  · exact absurd h1 (Nat.ne_of_lt (Nat.lt_of_le_of_lt up (by decide : 650 < 1556)))
  · exact absurd h1 (Nat.ne_of_lt (Nat.lt_of_le_of_lt up (by decide : 650 < 1557)))
  · exact absurd h1 (Nat.ne_of_lt (Nat.lt_of_le_of_lt up (by decide : 650 < 1558)))
  · have ge : 848 ≤ Shadow7.b0P (start j) + k := le_trans hb (Nat.le_add_right _ k)
    exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_le_of_lt up (Nat.lt_of_lt_of_le (by decide : 650 < 848) ge)))

theorem flag_out (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    Shadow7.e0P (start j) + 5 ∉ (1556 :: 1557 :: 1558 :: fullM j : List Nat) := by
  intro h
  have ge := flag_ge j h0 (by omega)
  have hb := b0_le j h0 (by omega)
  simp only [List.mem_cons, fullM, List.mem_map, List.mem_range] at h
  rcases h with h1 | h1 | h1 | ⟨k, hk, h1⟩
  · exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 1556 < 1640) ge))
  · exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 1557 < 1640) ge))
  · exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 1558 < 1640) ge))
  · have top : Shadow7.b0P (start j) + k ≤ 1015 :=
      le_trans (Nat.add_le_add hb (Nat.le_of_lt_succ hk)) (by decide : 998 + 17 ≤ 1015)
    exact absurd h1 (Nat.ne_of_lt (Nat.lt_of_le_of_lt top (Nat.lt_of_lt_of_le (by decide : 1015 < 1640) ge)))

theorem scan_lt (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) {q : Nat}
    (hq : q ∈ RailPair.sites (scanPairs j)) : q < 1556 := by
  obtain ⟨p, hp, hq'⟩ := List.mem_flatMap.mp hq
  simp only [scanPairs, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
  have ha := a0_le j h0 (by omega)
  have hb := b0_le j h0 (by omega)
  rcases hq' with rfl | rfl <;> omega

theorem scratch_away (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Nat)
    (hq : 1556 ≤ q ∧ q ≤ 1597) :
    (q < start j + 16 ∨ start j + 30 < q) ∧ q ≠ Shadow7.e0P (start j) + 5 ∧
      q ∉ RailPair.sites (scanPairs j) := by
  have w := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have sb := sb_lo (start j) (by simp only [StairPacket.start]; omega)
  refine ⟨Or.inr (by omega), ?_, ?_⟩
  · simp only [Shadow7.e0P]; omega
  · intro hm
    have := scan_lt j h0 (by omega) hm
    omega

theorem watched_lo (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Nat)
    (hq : (q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7) ∨ (1559 ≤ q ∧ q < 1559 + 39)) :
    1559 ≤ q := by
  rcases hq with (rfl | rfl) | ⟨lo, _⟩
  · exact le_trans (by decide : (1559 : Nat) ≤ 1640)
      (le_trans (flag_ge j h0 (by omega)) (Nat.add_le_add_left (by decide : (5 : Nat) ≤ 6) (Shadow7.e0P (start j))))
  · exact le_trans (by decide : (1559 : Nat) ≤ 1640)
      (le_trans (flag_ge j h0 (by omega)) (Nat.add_le_add_left (by decide : (5 : Nat) ≤ 7) (Shadow7.e0P (start j))))
  · exact lo

theorem watched_side (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Nat)
    (hq : (q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7) ∨ (1559 ≤ q ∧ q < 1559 + 39)) :
    q ∉ (1556 :: 1557 :: 1558 :: fullM j : List Nat) ∧
      (q < start j + 16 ∨ start j + 30 < q) ∧ q ≠ Shadow7.e0P (start j) + 5 ∧
      q ∉ RailPair.sites (scanPairs j) := by
  have lo := watched_lo j h0 (by omega) q hq
  have ge := flag_ge j h0 (by omega)
  have hb := b0_le j h0 (by omega)
  have top : start j + 30 ≤ 420 := by
    have := (start_win j h0 (by omega)).2
    omega
  refine ⟨?_, Or.inr (Nat.lt_of_le_of_lt top (Nat.lt_of_lt_of_le (by decide : (420 : Nat) < 1559) lo)), ?_, ?_⟩
  · intro h
    simp only [List.mem_cons, fullM, List.mem_map, List.mem_range] at h
    have neq {n : Nat} (hn : n < 1559) : q ≠ n := Nat.ne_of_gt (Nat.lt_of_lt_of_le hn lo)
    rcases h with h1 | h1 | h1 | ⟨k, hk, h1⟩
    · exact absurd h1 (neq (by decide))
    · exact absurd h1 (neq (by decide))
    · exact absurd h1 (neq (by decide))
    · have bound : Shadow7.b0P (start j) + k ≤ 1015 :=
        le_trans (Nat.add_le_add hb (Nat.le_of_lt_succ hk)) (by decide : 998 + 17 ≤ 1015)
      exact absurd h1 (neq (Nat.lt_of_le_of_lt bound (by decide : 1015 < 1559))).symm
  · rcases hq with (rfl | rfl) | ⟨_, hi⟩
    · exact Nat.ne_of_gt (Nat.lt_succ_self _)
    · exact Nat.ne_of_gt (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _))
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hi (le_trans (by decide : 1559 + 39 ≤ 1640) ge))
  · intro hm
    exact absurd (scan_lt j h0 (by omega) hm) (Nat.not_lt_of_ge (le_trans (by decide : (1556 : Nat) ≤ 1559) lo))

theorem run_forward_append (a b : List Gate) (m : List Bool) (s : State) :
    run (GateMirror.forward (a ++ b)) m s =
      run (GateMirror.forward b) (m.drop (measurementCount (GateMirror.forward a)))
        (run (GateMirror.forward a) m s) := by
  rw [forward_app, run_append, run_take]

attribute [local irreducible] run SkywalkNat.step leaveFix0 leaveFix1 leaveFix2 latch Companion.erase

theorem flip_dest (s h : Nat) (q : Wire) (hq : q < s + 16 ∨ s + 30 < q) :
    q ∉ (GateMirror.forward (leaveFix1 s h)).map destination := by
  rw [fix1_forward]
  simp only [notRegister, List.map_map, List.mem_map, List.mem_range, not_exists, not_and]
  intro i hi e
  simp only [Function.comp, destination] at e
  unfold Wire at *; omega

/-- The entry run: scan, history flip, erase (the common core of dadon's `Front.result`/`FrontReady.frame`). -/
theorem entry_core (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    let a := SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)
    let e := negative sg a.u
    let out := run (GateMirror.forward (entryOps (start j))) m s
    out.phase = s.phase ∧ regValue (fullM j) out.basis = 0 ∧ out.basis (Shadow7.e0P (start j) + 5) = e ∧
      out.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ a.u - e.toNat) ∧
      (out.basis 1558).toNat = upperBorrow (2^(Shadow7.sbP (start j))) a.u a.v e.toNat ∧
      (∀ i < 19, out.basis (Shadow7.a0P (start j) - 1 + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j))).testBit i) ∧
      ∀ q, q ∉ 1556::1557::1558::fullM j → (q < start j + 16 ∨ start j + 30 < q) → q ≠ Shadow7.e0P (start j) + 5 →
        q ∉ RailPair.sites (scanPairs j) → out.basis q = s.basis q := by
  intro a e out
  have scanActual := inputScan_result j h0 (by omega) s m a.u a.v G sg ready fresh
  generalize hu : run (GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j)))) m s = u at scanActual
  generalize ht : m.drop (measurementCount (GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j))))) = t
  generalize hv : run (GateMirror.forward (leaveFix1 (start j) (Shadow7.sbP (start j)))) t u = v
  have hist (q : Wire) (hq : q < start j + 16 ∨ start j + 30 < q) : v.basis q = u.basis q := by
    rw [← hv]; exact preserved _ _ _ _ (flip_dest _ _ q hq)
  have vphase : v.phase = u.phase := by
    rw [← hv, fix1_forward, notRegister_correct _ (history_nodup j)]
  have outputBits (i : Nat) (hi : i < 19) :
      v.basis (Shadow7.a0P (start j) - 1 + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j))).testBit i ∧
      v.basis (Shadow7.b0P (start j) - 1 + i) = ((a.u - e.toNat)/2^(Shadow7.sbP (start j))).testBit i := by
    rw [hist _ (Or.inr (aCol_above j h0 (by omega) i)), hist _ (Or.inr (bCol_above j h0 (by omega) i))]
    exact scanActual.2.2.1 i hi
  have same (q : Wire) (h1q : q < start j + 16 ∨ start j + 30 < q) (h2q : q ≠ Shadow7.e0P (start j) + 5)
      (h3q : q ∉ RailPair.sites (scanPairs j)) : v.basis q = s.basis q :=
    (hist _ h1q).trans (scanActual.2.2.2 _ h2q h3q)
  have away (q : Nat) (hq : 1556 ≤ q ∧ q ≤ 1597) := scratch_away j h0 (by omega) q hq
  have clean : ∀ q ∈ 1556::1557::1558::fullC, v.basis q = false := by
    intro q h
    have hr : 1556 ≤ q ∧ q ≤ 1597 := by
      have b := scratchWire_band h
      exact ⟨b.1, Nat.le_trans b.2 (by decide)⟩
    obtain ⟨a1, a2, a3⟩ := away q hr
    rw [same q a1 a2 a3]; exact scratch _ h
  have temps : ∀ p ∈ longPairs j, v.basis p.2 = false := by
    intro p h
    have hr : 1556 ≤ p.2 ∧ p.2 ≤ 1597 := by
      have b := longTemp_band j h
      exact ⟨Nat.le_trans (by decide) b.1, Nat.le_trans b.2 (by decide)⟩
    obtain ⟨a1, a2, a3⟩ := away p.2 hr
    rw [same _ a1 a2 a3]; exact temp _ h
  have cap := LeaveShadowRails.inputFit_shadow7 (Shadow7.sbP (start j)) z small.1 small.2
  have fit : (a.u - e.toNat)/2^(Shadow7.sbP (start j)) < 2^19 :=
    lt_of_le_of_lt (Nat.div_le_div_right (Nat.le_trans (Nat.sub_le a.u e.toNat) (Nat.le_add_right a.u a.v))) cap.2
  have se : e.toNat ≤ 1 := by cases e <;> decide
  have su : e.toNat ≤ a.u := by
    by_cases h : 0 < a.u
    · cases e
      · exact Nat.zero_le _
      · exact Nat.succ_le_of_lt h
    · simp [e, negative, h]
  have done := eraseActual_result j h0 (by omega) v (t.drop (measurementCount (GateMirror.forward (leaveFix1 (start j) (Shadow7.sbP (start j))))))
    a.u a.v e.toNat se su cap.1 fit outputBits clean temps
  have splitTape :
      m.drop (measurementCount (GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j)) ++
          leaveFix1 (start j) (Shadow7.sbP (start j))))) =
        t.drop (measurementCount (GateMirror.forward (leaveFix1 (start j) (Shadow7.sbP (start j))))) := by
    rw [forward_app, measurementCount_append, ← List.drop_drop, ht]
  have hout : out = run (GateMirror.forward ((leaveFix0 (start j) (Shadow7.sbP (start j)) ++
        leaveFix1 (start j) (Shadow7.sbP (start j))) ++ leaveFix2 (start j) (Shadow7.sbP (start j)))) m s := rfl
  rw [hout, run_forward_append, run_forward_append, hu, ht, hv, splitTape]
  refine ⟨done.1.trans (vphase.trans scanActual.1), done.2.1, ?_, done.2.2.1, done.2.2.2.1, ?_, ?_⟩
  · exact (done.2.2.2.2 _ (flag_out j h0 (by omega))).trans
      ((hist _ (Or.inr (flag_above j h0 (by omega)))).trans scanActual.2.1)
  · intro i hi
    exact (done.2.2.2.2 _ (aCol_out j h0 (by omega) i hi)).trans (outputBits i hi).1
  · intro q n1 h1q h2q h3q
    exact (done.2.2.2.2 _ n1).trans (same q h1q h2q h3q)



/-- dadon's `Leave{s}FrontReady.frame`: the watched wires survive the entry. -/
theorem frontReady_frame (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    ∀ q ∈ watched j, (run (GateMirror.forward (entryOps (start j))) m s).basis q = s.basis q := by
  have core := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
  intro q hq
  have hr : (q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7) ∨ (1559 ≤ q ∧ q < 1559 + 39) := by
    simpa only [watched, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] using hq
  have side := watched_side j h0 (by omega) q hr
  apply core.2.2.2.2.2.2 q side.1 side.2.1 side.2.2.1 side.2.2.2

/-! EntryAction (dadon's `Leave{s}EntryAction`). -/

/-- dadon's `oddRead`: the history letters, negated. -/
def oddRead (j : Fin 23) (v : BasisState) := (List.range 15).map (fun i => !v ((ports j).g + i))

/-- The scan and the erase never write the history letters (dadon's `historyGeom`). -/
theorem history_untouched : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 → ∀ i < 15,
    start j + 16 + i ∉ (GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j)))).map destination ∧
    start j + 16 + i ∉ (GateMirror.forward (leaveFix2 (start j) (Shadow7.sbP (start j)))).map destination := by
  decide +kernel

/-- dadon's `Leave{s}EntryAction.parity`. -/
theorem entry_parity (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) :
    parityBits (ports j) (run (GateMirror.forward (entryOps (start j))) m s).basis = oddRead j s.basis := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  unfold parityBits oddRead
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [entryOps, forward_app, forward_app, run_append, run_take, run_append, run_take]
  have mem : (ports j).g + i ∈ (List.range 15).map (start j + 16 + ·) := List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  -- fix2 does not touch the history letters
  have after : (ports j).g + i ∉ (GateMirror.forward (leaveFix2 (start j) (Shadow7.sbP (start j)))).map destination :=
    (history_untouched j h0 (by omega) i hi).2
  have before : (ports j).g + i ∉ (GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j)))).map destination :=
    (history_untouched j h0 (by omega) i hi).1
  rw [preserved _ _ _ _ after, fix1_forward, notRegister_correct _ (history_nodup j)]
  dsimp only
  rw [if_pos mem, preserved _ _ _ _ before]

/-- dadon's `Leave{s}EntryAction.upperBits`. -/
theorem upperBits (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (a : SkywalkNat.State) (v : BasisState)
    (bits : ∀ i < 19, v (Shadow7.a0P (start j) - 1 + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j))).testBit i) :
    ∀ i < 18, v (Shadow7.a0P (start j) + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j) + 1)).testBit i := by
  have r := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  intro i hi
  have div : (a.u+a.v)/2^(Shadow7.sbP (start j) + 1) = ((a.u+a.v)/2^(Shadow7.sbP (start j)))/2^1 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [div, Nat.testBit_div_two_pow, show Shadow7.a0P (start j) + i = Shadow7.a0P (start j) - 1 + (i+1) by omega, Nat.add_comm i 1]
  rw [Nat.add_comm 1 i]
  exact bits (i + 1) (Nat.add_lt_add_right hi 1)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror RecordedQuantum HighBankFirstHit LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- dadon's `Leave{s}Hit.swaps`: the block's history cells in the `OB5.sig (s+14)` frame. -/
def swaps (j : Fin 23) (i : Nat) : Wire := OB5.sig (start j + 14) (start j + 1044 + i)

theorem swaps_range (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) (hi : i < 15) :
    (swaps j i : Nat) ≤ 1300 ∨ (Shadow7.e0P (start j) + 10 ≤ swaps j i ∧ (swaps j i : Nat) ≤ 1812) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have e := Shadow7.sig_hist (c := 1044 + i) w1 w2 (by omega) (by omega)
  unfold swaps; rw [show start j + 1044 + i = start j + (1044 + i) by omega]
  unfold Wire at *; omega

theorem swaps_inj (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i k : Nat) (hi : i < 15) (hk : k < 15)
    (e : swaps j i = swaps j k) : i = k := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have a := Shadow7.sig_hist (c := 1044 + i) w1 w2 (by omega) (by omega)
  have b := Shadow7.sig_hist (c := 1044 + k) w1 w2 (by omega) (by omega)
  unfold swaps at e; rw [show start j + 1044 + i = start j + (1044 + i) by omega,
    show start j + 1044 + k = start j + (1044 + k) by omega] at e
  unfold Wire at *; omega

/-- dadon's `Leave{s}Hit.sites`. -/
theorem hit_sites (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : Layout 1560 (swaps j) LeaveSelector.tags 0 15 := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  refine ⟨fun i _ hi => ?_, fun i _ hi k lt hk => ?_⟩
  · have a := swaps_range j h0 (by omega) i (by omega)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or,
      not_false_eq_true, LeaveSelector.tags]
    unfold Wire at *; omega
  · have a := swaps_range j h0 (by omega) k (by omega)
    simp only [LeaveSelector.tags]
    unfold Wire at *; omega

theorem swaps_apart (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) (hi : i < 15) :
    swaps j i ≠ 1559 ∧ swaps j i ≠ 1560 := by
  have r := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  have a := swaps_range j h0 (by omega) i hi
  unfold Wire at *; omega

/-! The selector words. -/

def farOps (j : Fin 23) : List Op := (1559 :: (List.range 5).map (1561 + ·)).map (fun a => .xor a (Shadow7.e0P (start j) + 7))
def zeroOps : List Op := [.xor 1559 1576, .xor 1561 1576]
def suffixOps (j : Fin 23) : List Op :=
  (List.range 12).map (fun i => .save (start j + 29 - i) (if i = 0 then start j + 30 else 1576 + i) (1577 + i))
def selectOps (j : Fin 23) : List Op :=
  [.save 1562 1588 1589, .save 1563 1586 1590, .save 1564 1584 1591, .save 1565 1582 1592, .save 1566 1580 1593,
   .save 1567 1578 1594, .save 1568 (start j + 30) 1595]
def crossOps (j : Fin 23) : List Op :=
  (List.range 16).map (fun i => .mix (tagsP.getD i 0) (Shadow7.a0P (start j) + i) (Shadow7.e0P (start j) + 6))
def signOps : List Op :=
  [.xor 1589 1596, .xor 1590 1596, .xor 1591 1596, .xor 1592 1596, .xor 1593 1596, .xor 1594 1596, .xor 1595 1596,
   .xor 1569 1596, .xor 1570 1596, .xor 1571 1596, .xor 1572 1596, .xor 1573 1596, .xor 1574 1596, .xor 1575 1596,
   .xor 1560 1596]
def productOps (j : Fin 23) : List Op := [.save (Shadow7.e0P (start j) + 6) 1596 1597]
/-- dadon's `Leave{s}Selector.prepare`. -/
def prepare (j : Fin 23) : List Op :=
  farOps j ++ zeroOps ++ suffixOps j ++ selectOps j ++ crossOps j ++ signOps ++ productOps j
/-- dadon's `Leave{s}Selector.retire`. -/
def retire (j : Fin 23) : List Op :=
  (productOps j).reverse ++ signOps ++ (selectOps j).reverse ++ (suffixOps j).reverse ++ zeroOps

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen
open Arithmetic RecordedQuantum
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

abbrev SE := LeaveSelector.Expr
abbrev SOp := LeaveSelector.Op

def rE (σ : Nat → Nat) : SE → SE
  | .bit b => .bit b
  | .wire w => .wire (σ w)
  | .both a b => .both (rE σ a) (rE σ b)
  | .xor a b => .xor (rE σ a) (rE σ b)

def rOp (σ : Nat → Nat) : SOp → SOp
  | .xor a t => .xor (σ a) (σ t)
  | .mix a b t => .mix (σ a) (σ b) (σ t)
  | .save a b t => .save (σ a) (σ b) (σ t)

def EIn (P : Nat → Prop) : SE → Prop
  | .bit _ => True
  | .wire w => P w
  | .both a b => EIn P a ∧ EIn P b
  | .xor a b => EIn P a ∧ EIn P b

def OpIn (P : Nat → Prop) : SOp → Prop
  | .xor a t => P a ∧ P t
  | .mix a b t => P a ∧ P b ∧ P t
  | .save a b t => P a ∧ P b ∧ P t

def InjOn (P : Nat → Prop) (σ : Nat → Nat) : Prop := ∀ a b, P a → P b → σ a = σ b → a = b

/-- `g'` is `g` renamed on the domain. -/
def Rel (P : Nat → Prop) (σ : Nat → Nat) (g' g : LeaveSelector.Sym) : Prop := ∀ q, P q → g' (σ q) = rE σ (g q)
/-- every symbol of `g` on the domain mentions only domain wires. -/
def Good (P : Nat → Prop) (g : LeaveSelector.Sym) : Prop := ∀ q, P q → EIn P (g q)

theorem rE_inj {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) :
    ∀ a b : SE, EIn P a → EIn P b → rE σ a = rE σ b → a = b := by
  intro a
  induction a with
  | bit x =>
    intro b _ _ h
    cases b <;> simp_all [rE]
  | wire w =>
    intro b ha hb h
    cases b with
    | wire v =>
      simp only [rE, LeaveSelector.Expr.wire.injEq] at h
      exact congrArg _ (hσ w v ha hb h)
    | bit _ => simp [rE] at h
    | both _ _ => simp [rE] at h
    | xor _ _ => simp [rE] at h
  | both a1 a2 ih1 ih2 =>
    intro b ha hb h
    cases b with
    | both b1 b2 =>
      simp only [rE, LeaveSelector.Expr.both.injEq] at h
      rw [ih1 b1 ha.1 hb.1 h.1, ih2 b2 ha.2 hb.2 h.2]
    | bit _ => simp [rE] at h
    | wire _ => simp [rE] at h
    | xor _ _ => simp [rE] at h
  | xor a1 a2 ih1 ih2 =>
    intro b ha hb h
    cases b with
    | xor b1 b2 =>
      simp only [rE, LeaveSelector.Expr.xor.injEq] at h
      rw [ih1 b1 ha.1 hb.1 h.1, ih2 b2 ha.2 hb.2 h.2]
    | bit _ => simp [rE] at h
    | wire _ => simp [rE] at h
    | both _ _ => simp [rE] at h

theorem rE_conj (σ : Nat → Nat) (a b : SE) :
    rE σ (LeaveSelector.conj a b) = LeaveSelector.conj (rE σ a) (rE σ b) := by
  rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> rfl

theorem EIn_conj {P : Nat → Prop} (a b : SE) (ha : EIn P a) (hb : EIn P b) : EIn P (LeaveSelector.conj a b) := by
  rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    first | exact trivial | exact ha | exact hb | exact ⟨ha, hb⟩

theorem rE_xor {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) (a b : SE) (ha : EIn P a) (hb : EIn P b) :
    rE σ (LeaveSelector.xor a b) = LeaveSelector.xor (rE σ a) (rE σ b) := by
  unfold LeaveSelector.xor
  by_cases h : a = b
  · subst h; simp [rE]
  · have h' : rE σ a ≠ rE σ b := fun e => h (rE_inj hσ a b ha hb e)
    rw [if_neg h, if_neg h']
    rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> rfl

theorem EIn_xor {P : Nat → Prop} (a b : SE) (ha : EIn P a) (hb : EIn P b) : EIn P (LeaveSelector.xor a b) := by
  unfold LeaveSelector.xor
  split
  · exact trivial
  · rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
      first | exact trivial | exact ha | exact hb | exact ⟨ha, hb⟩

theorem dst_mem {P : Nat → Prop} (o : SOp) (ho : OpIn P o) : P o.dst := by
  cases o with
  | xor a t => exact ho.2
  | mix a b t => exact ho.2.2
  | save a b t => exact ho.2.2

theorem rOp_dst (σ : Nat → Nat) (o : SOp) : (rOp σ o).dst = σ o.dst := by cases o <;> rfl

theorem symbolic_rel {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) (o : SOp) (ho : OpIn P o)
    (g' g : LeaveSelector.Sym) (hg : Good P g) (hr : Rel P σ g' g) :
    Rel P σ (LeaveSelector.symbolic (rOp σ o) g') (LeaveSelector.symbolic o g) := by
  intro q hq
  cases o with
  | xor a t =>
    obtain ⟨ha, ht⟩ := ho
    show (if σ q = σ t then LeaveSelector.xor (g' (σ q)) (g' (σ a)) else g' (σ q)) =
      rE σ (if q = t then LeaveSelector.xor (g q) (g a) else g q)
    by_cases e : q = t
    · rw [if_pos (congrArg σ e), if_pos e, hr q hq, hr a ha, rE_xor hσ _ _ (hg q hq) (hg a ha)]
    · rw [if_neg (fun h => e (hσ _ _ hq ht h)), if_neg e, hr q hq]
  | mix a b t =>
    obtain ⟨ha, hb, ht⟩ := ho
    show (if σ q = σ t then LeaveSelector.xor (g' (σ q)) (LeaveSelector.conj (g' (σ a)) (g' (σ b)))
        else g' (σ q)) =
      rE σ (if q = t then LeaveSelector.xor (g q) (LeaveSelector.conj (g a) (g b)) else g q)
    by_cases e : q = t
    · rw [if_pos (congrArg σ e), if_pos e, hr q hq, hr a ha, hr b hb,
        rE_xor hσ _ _ (hg q hq) (EIn_conj _ _ (hg a ha) (hg b hb)), rE_conj]
    · rw [if_neg (fun h => e (hσ _ _ hq ht h)), if_neg e, hr q hq]
  | save a b t =>
    obtain ⟨ha, hb, ht⟩ := ho
    show (if σ q = σ t then LeaveSelector.xor (g' (σ q)) (LeaveSelector.conj (g' (σ a)) (g' (σ b)))
        else g' (σ q)) =
      rE σ (if q = t then LeaveSelector.xor (g q) (LeaveSelector.conj (g a) (g b)) else g q)
    by_cases e : q = t
    · rw [if_pos (congrArg σ e), if_pos e, hr q hq, hr a ha, hr b hb,
        rE_xor hσ _ _ (hg q hq) (EIn_conj _ _ (hg a ha) (hg b hb)), rE_conj]
    · rw [if_neg (fun h => e (hσ _ _ hq ht h)), if_neg e, hr q hq]

theorem symbolic_good {P : Nat → Prop} (o : SOp) (ho : OpIn P o) (g : LeaveSelector.Sym) (hg : Good P g) :
    Good P (LeaveSelector.symbolic o g) := by
  intro q hq
  cases o with
  | xor a t =>
    show EIn P (if q = t then LeaveSelector.xor (g q) (g a) else g q)
    split
    · exact EIn_xor _ _ (hg q hq) (hg a ho.1)
    · exact hg q hq
  | mix a b t =>
    show EIn P (if q = t then LeaveSelector.xor (g q) (LeaveSelector.conj (g a) (g b)) else g q)
    split
    · exact EIn_xor _ _ (hg q hq) (EIn_conj _ _ (hg a ho.1) (hg b ho.2.1))
    · exact hg q hq
  | save a b t =>
    show EIn P (if q = t then LeaveSelector.xor (g q) (LeaveSelector.conj (g a) (g b)) else g q)
    split
    · exact EIn_xor _ _ (hg q hq) (EIn_conj _ _ (hg a ho.1) (hg b ho.2.1))
    · exact hg q hq

theorem sim_rel {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) :
    ∀ (os : List SOp), (∀ o ∈ os, OpIn P o) → ∀ (g' g : LeaveSelector.Sym), Good P g → Rel P σ g' g →
      Rel P σ (LeaveSelector.sim (os.map (rOp σ)) g') (LeaveSelector.sim os g) ∧ Good P (LeaveSelector.sim os g)
  | [], _, g', g, hg, hr => ⟨hr, hg⟩
  | o :: os, hos, g', g, hg, hr => by
    have h1 : OpIn P o := hos o (by simp)
    exact sim_rel hσ os (fun x hx => hos x (by simp [hx])) _ _ (symbolic_good o h1 g hg)
      (symbolic_rel hσ o h1 g' g hg hr)

/-! Exits: `erase`, `checkExit`, `validExit`, `erased`. -/

theorem erase_rel {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) (o : SOp) (ho : OpIn P o)
    (g' g : LeaveSelector.Sym) (hg : Good P g) (hr : Rel P σ g' g) :
    Rel P σ (LeaveSelector.erase (rOp σ o) g') (LeaveSelector.erase o g) := by
  cases o with
  | xor a t => exact symbolic_rel hσ (.xor a t) ho g' g hg hr
  | mix a b t => exact symbolic_rel hσ (.mix a b t) ho g' g hg hr
  | save a b t =>
    intro q hq
    show (if σ q = σ t then LeaveSelector.Expr.bit false else g' (σ q)) =
      rE σ (if q = t then LeaveSelector.Expr.bit false else g q)
    by_cases e : q = t
    · rw [if_pos (congrArg σ e), if_pos e]; rfl
    · rw [if_neg (fun h => e (hσ _ _ hq ho.2.2 h)), if_neg e, hr q hq]

theorem erase_good {P : Nat → Prop} (o : SOp) (ho : OpIn P o) (g : LeaveSelector.Sym) (hg : Good P g) :
    Good P (LeaveSelector.erase o g) := by
  cases o with
  | xor a t => exact symbolic_good (.xor a t) ho g hg
  | mix a b t => exact symbolic_good (.mix a b t) ho g hg
  | save a b t =>
    intro q hq
    show EIn P (if q = t then LeaveSelector.Expr.bit false else g q)
    split
    · exact trivial
    · exact hg q hq

theorem checkExit_rel {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) (o : SOp) (ho : OpIn P o)
    (g' g : LeaveSelector.Sym) (hg : Good P g) (hr : Rel P σ g' g) :
    LeaveSelector.checkExit g' (rOp σ o) = LeaveSelector.checkExit g o := by
  cases o with
  | xor a t => rfl
  | mix a b t => rfl
  | save a b t =>
    obtain ⟨ha, hb, ht⟩ := ho
    show decide (σ t ≠ σ a ∧ σ t ≠ σ b ∧ g' (σ t) = LeaveSelector.conj (g' (σ a)) (g' (σ b))) =
      decide (t ≠ a ∧ t ≠ b ∧ g t = LeaveSelector.conj (g a) (g b))
    rw [hr t ht, hr a ha, hr b hb, ← rE_conj]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (congrArg σ e), fun e => h2 (congrArg σ e),
        rE_inj hσ _ _ (hg t ht) (EIn_conj _ _ (hg a ha) (hg b hb)) h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (hσ _ _ ht ha e), fun e => h2 (hσ _ _ ht hb e), by rw [h3]⟩

theorem exits_rel {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) :
    ∀ (os : List SOp), (∀ o ∈ os, OpIn P o) → ∀ (g' g : LeaveSelector.Sym), Good P g → Rel P σ g' g →
      LeaveSelector.validExit (os.map (rOp σ)) g' = LeaveSelector.validExit os g ∧
      Rel P σ (LeaveSelector.erased (os.map (rOp σ)) g') (LeaveSelector.erased os g) ∧
      Good P (LeaveSelector.erased os g)
  | [], _, g', g, hg, hr => ⟨rfl, hr, hg⟩
  | o :: os, hos, g', g, hg, hr => by
    have h1 : OpIn P o := hos o (by simp)
    obtain ⟨v, r, gd⟩ := exits_rel hσ os (fun x hx => hos x (by simp [hx])) _ _ (erase_good o h1 g hg)
      (erase_rel hσ o h1 g' g hg hr)
    refine ⟨?_, r, gd⟩
    show (LeaveSelector.checkExit g' (rOp σ o) && LeaveSelector.validExit (os.map (rOp σ)) (LeaveSelector.erase (rOp σ o) g')) =
      (LeaveSelector.checkExit g o && LeaveSelector.validExit os (LeaveSelector.erase o g))
    rw [checkExit_rel hσ o h1 g' g hg hr, v]

theorem all_congr_mem {α : Type} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons]
    rw [h x (by simp), ih (fun a ha => h a (by simp [ha]))]

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen
open Arithmetic RecordedQuantum Partial GateMirror HighBankFirstHit
open ECDSAAdd.Entrant.StairPacket.LeaveJ
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1000000

/-- block 10's selector wires. -/
def D (q : Nat) : Prop :=
  (1559 ≤ q ∧ q ≤ 1597) ∨ (241 ≤ q ∧ q ≤ 255) ∨ (394 ≤ q ∧ q ≤ 409) ∨ q = 1717 ∨ q = 1718
instance (q : Nat) : Decidable (D q) := by unfold D; infer_instance

/-- block 10 → block j. -/
def ren (j : Fin 23) (q : Nat) : Nat :=
  if 241 ≤ q ∧ q ≤ 255 then q - 225 + start j
  else if 394 ≤ q ∧ q ≤ 409 then q - 394 + Shadow7.a0P (start j)
  else if q = 1717 then Shadow7.e0P (start j) + 6
  else if q = 1718 then Shadow7.e0P (start j) + 7
  else q

theorem geo (j : Fin 23) : Shadow7.a0P (start j) = start j + ((513 - start j) / 2 - 7) + 32 ∧
    Shadow7.e0P (start j) = 1574 + ((513 - start j) / 2 - 7) ∧ start j = 75 + 15 * j.val := ⟨rfl, rfl, rfl⟩

theorem ren_inj (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : InjOn D (ren j) := by
  intro a b ha hb h
  obtain ⟨g1, g2, g3⟩ := geo j
  unfold ren at h
  unfold D at ha hb
  split_ifs at h <;> omega

theorem ren_const (j : Fin 23) (q : Nat) (h : 1559 ≤ q ∧ q ≤ 1597) : ren j q = q := by
  unfold ren; split_ifs <;> omega
theorem ren_g (j : Fin 23) (q : Nat) (h : 241 ≤ q ∧ q ≤ 255) : ren j q = q - 225 + start j := by
  unfold ren; rw [if_pos h]
theorem ren_u (j : Fin 23) (q : Nat) (h : 394 ≤ q ∧ q ≤ 409) : ren j q = q - 394 + Shadow7.a0P (start j) := by
  unfold ren; rw [if_neg (by omega), if_pos h]
theorem ren_cross (j : Fin 23) : ren j 1717 = Shadow7.e0P (start j) + 6 := by unfold ren; simp
theorem ren_near (j : Fin 23) : ren j 1718 = Shadow7.e0P (start j) + 7 := by unfold ren; simp

theorem s10 : start 10 = 225 := rfl
theorem a10 : Shadow7.a0P 225 = 394 := rfl
theorem e10 : Shadow7.e0P 225 = 1711 := rfl

/-! `prepare` and `retire` of block j are block 10's, renamed. -/

theorem farOps_ren (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : (farOps 10).map (rOp (ren j)) = farOps j := by
  unfold farOps; rw [List.map_map]; apply List.map_congr_left; intro a ha
  simp only [List.mem_cons, List.mem_map, List.mem_range] at ha
  simp only [Function.comp_apply, rOp, s10, e10, LeaveSelector.Op.xor.injEq]
  refine ⟨?_, ren_near j⟩
  rcases ha with rfl | ⟨x, hx, rfl⟩ <;> exact ren_const j _ (by omega)

theorem zeroOps_ren (j : Fin 23) : zeroOps.map (rOp (ren j)) = zeroOps := by
  simp only [zeroOps, List.map_cons, List.map_nil, rOp, ren_const j 1559 (by omega), ren_const j 1561 (by omega),
    ren_const j 1576 (by omega)]

/-- constant wires are fixed. -/
def C (q : Nat) : Prop := 1559 ≤ q ∧ q ≤ 1597
instance (q : Nat) : Decidable (C q) := by unfold C; infer_instance
instance (P : Nat → Prop) [DecidablePred P] (o : SOp) : Decidable (OpIn P o) := by
  cases o <;> unfold OpIn <;> infer_instance

theorem map_const (j : Fin 23) (l : List SOp) (h : ∀ o ∈ l, OpIn C o) : l.map (rOp (ren j)) = l := by
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro o ho
  have hc := h o ho
  cases o with
  | xor a t => obtain ⟨ha, ht⟩ := hc; simp only [rOp, id, ren_const j a ha, ren_const j t ht]
  | mix a b t => obtain ⟨ha, hb, ht⟩ := hc; simp only [rOp, id, ren_const j a ha, ren_const j b hb, ren_const j t ht]
  | save a b t => obtain ⟨ha, hb, ht⟩ := hc; simp only [rOp, id, ren_const j a ha, ren_const j b hb, ren_const j t ht]

theorem signOps_ren (j : Fin 23) : signOps.map (rOp (ren j)) = signOps :=
  map_const j _ (by decide)

theorem suffixOps_ren (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    (suffixOps 10).map (rOp (ren j)) = suffixOps j := by
  unfold suffixOps; rw [List.map_map]; apply List.map_congr_left; intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp_apply, rOp, s10, LeaveSelector.Op.save.injEq]
  refine ⟨?_, ?_, ren_const j _ (by omega)⟩
  · rw [ren_g j _ (by omega)]; unfold Wire; omega
  · by_cases h : i = 0
    · simp only [h, ↓reduceIte]; rw [ren_g j _ (by omega)]; unfold Wire; omega
    · simp only [h, ↓reduceIte]; exact ren_const j _ (by omega)

theorem selectOps_ren (j : Fin 23) : (selectOps 10).map (rOp (ren j)) = selectOps j := by
  simp only [selectOps, List.map_cons, List.map_nil, rOp, s10, List.cons.injEq, LeaveSelector.Op.save.injEq,
    and_true, ren_const j 1562 (by omega), ren_const j 1563 (by omega), ren_const j 1564 (by omega),
    ren_const j 1565 (by omega), ren_const j 1566 (by omega), ren_const j 1567 (by omega), ren_const j 1568 (by omega),
    ren_const j 1578 (by omega), ren_const j 1580 (by omega), ren_const j 1582 (by omega), ren_const j 1584 (by omega),
    ren_const j 1586 (by omega), ren_const j 1588 (by omega), ren_const j 1589 (by omega), ren_const j 1590 (by omega),
    ren_const j 1591 (by omega), ren_const j 1592 (by omega), ren_const j 1593 (by omega), ren_const j 1594 (by omega),
    ren_const j 1595 (by omega), true_and]
  rw [ren_g j _ (by omega)]; unfold Wire; omega

theorem tags_range : ∀ i < 16, 1559 ≤ tagsP.getD i 0 ∧ tagsP.getD i 0 ≤ 1597 := by decide

theorem crossOps_ren (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    (crossOps 10).map (rOp (ren j)) = crossOps j := by
  unfold crossOps; rw [List.map_map]; apply List.map_congr_left; intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp_apply, rOp, s10, a10, e10, LeaveSelector.Op.mix.injEq]
  refine ⟨ren_const j _ (tags_range i hi), ?_, ren_cross j⟩
  rw [ren_u j _ (by omega)]; unfold Wire; omega

theorem productOps_ren (j : Fin 23) : (productOps 10).map (rOp (ren j)) = productOps j := by
  simp only [productOps, List.map_cons, List.map_nil, rOp, s10, e10, ren_cross j, ren_const j 1596 (by omega),
    ren_const j 1597 (by omega)]

theorem prepare_ren (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    (prepare 10).map (rOp (ren j)) = prepare j := by
  simp only [prepare, List.map_append, farOps_ren j h0 (by omega), zeroOps_ren j, suffixOps_ren j h0 (by omega), selectOps_ren j,
    crossOps_ren j h0 (by omega), signOps_ren j, productOps_ren j]

theorem retire_ren (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    (retire 10).map (rOp (ren j)) = retire j := by
  simp only [retire, List.map_append, List.map_reverse, zeroOps_ren j, suffixOps_ren j h0 (by omega), selectOps_ren j,
    signOps_ren j, productOps_ren j]

/-! Facts at block 10, by `decide` on small closed data. -/

theorem ops10_in : ∀ o ∈ prepare 10 ++ retire 10, OpIn D o := by decide
theorem prep10_in : ∀ o ∈ prepare 10, OpIn D o := fun o h => ops10_in o (List.mem_append_left _ h)
theorem retire10_in : ∀ o ∈ retire 10, OpIn D o := fun o h => ops10_in o (List.mem_append_right _ h)
theorem affected10_in : ∀ q ∈ LeaveSelector.affected (ports 10), D q := by decide

/-! Initial and final symbols. -/

theorem start_good (k : LeaveSelector.Mode) : Good D (LeaveSelector.start (ports 10) false k) := by
  intro q hq
  simp only [LeaveSelector.start, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> first | exact trivial | exact hq

theorem start_rel (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : LeaveSelector.Mode) :
    Rel D (ren j) (LeaveSelector.start (ports j) false k) (LeaveSelector.start (ports 10) false k) := by
  obtain ⟨g1, g2, g3⟩ := geo j
  intro q hq
  unfold D at hq
  rcases hq with hc | hg | hu | rfl | rfl
  · rw [ren_const j q hc]
    simp only [LeaveSelector.start, ports, s10, e10, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · rw [ren_g j q hg]
    simp only [LeaveSelector.start, ports, s10, e10, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | (simp only [rE, ren_g j q hg]; done)
  · rw [ren_u j q hu]
    simp only [LeaveSelector.start, ports, s10, e10, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | (simp only [rE, ren_u j q hu]; done)
  · rw [ren_cross j]
    simp only [LeaveSelector.start, ports, s10, e10, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · rw [ren_near j]
    simp only [LeaveSelector.start, ports, s10, e10, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl

theorem key_le (k : LeaveSelector.Mode) : LeaveSelector.key k ≤ 15 := by
  unfold LeaveSelector.key; have := k.isLt; omega

theorem crossing_ren (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : LeaveSelector.Mode) :
    rE (ren j) (LeaveSelector.crossing (ports 10) k) = LeaveSelector.crossing (ports j) k := by
  unfold LeaveSelector.crossing
  by_cases h : LeaveSelector.enabled k = true
  · simp only [h, ↓reduceIte, rE, ports, s10, a10]
    have := key_le k
    rw [ren_u j _ (by omega), LeaveSelector.Expr.wire.injEq]; unfold Wire; omega
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; rfl

theorem crossing_good (k : LeaveSelector.Mode) : EIn D (LeaveSelector.crossing (ports 10) k) := by
  unfold LeaveSelector.crossing
  split
  · have := key_le k
    show D ((ports 10).u + LeaveSelector.key k)
    simp only [ports, s10, a10]; unfold D; omega
  · exact trivial

theorem suffix_ren (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : ∀ (l : List Nat), (∀ x ∈ l, x < 15) →
    rE (ren j) (l.foldr (fun x rest => LeaveSelector.conj (.wire (start 10 + 16 + x)) rest) (.bit true)) =
      l.foldr (fun x rest => LeaveSelector.conj (.wire (start j + 16 + x)) rest) (.bit true)
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.foldr_cons]
    rw [rE_conj, suffix_ren j h0 (by omega) xs (fun y hy => h y (by simp [hy]))]
    have hx := h x (by simp)
    congr 1
    show LeaveSelector.Expr.wire (ren j (start 10 + 16 + x)) = _
    rw [s10, ren_g j _ (by omega), LeaveSelector.Expr.wire.injEq]; unfold Wire; omega

theorem suffix_good : ∀ (l : List Nat), (∀ x ∈ l, x < 15) →
    EIn D (l.foldr (fun x rest => LeaveSelector.conj (.wire (start 10 + 16 + x)) rest) (.bit true))
  | [], _ => trivial
  | x :: xs, h => by
    simp only [List.foldr_cons]
    have hx := h x (by simp)
    refine EIn_conj _ _ ?_ (suffix_good xs (fun y hy => h y (by simp [hy])))
    show D (start 10 + 16 + x)
    rw [s10]; unfold D; omega

theorem signExpr_ren (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : LeaveSelector.Mode) :
    rE (ren j) (LeaveSelector.signExpr (ports 10) k) = LeaveSelector.signExpr (ports j) k := by
  unfold LeaveSelector.signExpr LeaveSelector.suffixExpr
  by_cases h : (LeaveSelector.right k && decide (0 < LeaveSelector.key k)) = true
  · simp only [h, ↓reduceIte, ports]
    exact suffix_ren j h0 (by omega) _ (fun x hx => List.mem_range.mp (List.mem_of_mem_drop hx))
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; rfl

theorem signExpr_good (k : LeaveSelector.Mode) : EIn D (LeaveSelector.signExpr (ports 10) k) := by
  unfold LeaveSelector.signExpr LeaveSelector.suffixExpr
  split
  · simp only [ports]
    exact suffix_good _ (fun x hx => List.mem_range.mp (List.mem_of_mem_drop hx))
  · exact trivial

theorem cross_eq (j : Fin 23) : ren j (ports 10).crossing = (ports j).crossing := by
  simp only [ports, s10, e10]; exact ren_cross j
theorem near_eq (j : Fin 23) : ren j (ports 10).near = (ports j).near := by
  simp only [ports, s10, e10]; exact ren_near j

theorem cn_iff (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Nat) (hq : D q) :
    (ren j q = (ports j).crossing ∨ ren j q = (ports j).near) ↔ (q = (ports 10).crossing ∨ q = (ports 10).near) := by
  have hσ := ren_inj j h0 (by omega)
  have dc : D (ports 10).crossing := by decide
  have dn : D (ports 10).near := by decide
  rw [← cross_eq j, ← near_eq j]
  constructor
  · rintro (e | e)
    · exact Or.inl (hσ _ _ hq dc e)
    · exact Or.inr (hσ _ _ hq dn e)
  · rintro (e | e)
    · exact Or.inl (congrArg _ e)
    · exact Or.inr (congrArg _ e)

theorem post_good (k : LeaveSelector.Mode) : Good D (LeaveSelector.post (ports 10) (prepare 10) false k) := by
  have hs := (sim_rel (ren_inj 10 (by decide) (by decide)) (prepare 10) prep10_in _ _ (start_good k)
    (start_rel 10 (by decide) (by decide) k)).2
  intro q hq
  simp only [LeaveSelector.post, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  split_ifs
  · exact hq
  · exact EIn_conj _ _ (show D (ports 10).crossing by decide) (signExpr_good k)
  · exact hs q hq

theorem post_rel (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : LeaveSelector.Mode) :
    Rel D (ren j) (LeaveSelector.post (ports j) (prepare j) false k)
      (LeaveSelector.post (ports 10) (prepare 10) false k) := by
  have hσ := ren_inj j h0 (by omega)
  have hs := (sim_rel hσ (prepare 10) prep10_in _ _ (start_good k) (start_rel j h0 (by omega) k)).1
  intro q hq
  have i1 := cn_iff j h0 (by omega) q hq
  have i2 : ren j q = 1597 ↔ q = 1597 := by
    constructor
    · intro e; exact hσ _ _ hq (by decide) (e.trans (ren_const j 1597 (by omega)).symm)
    · intro e; rw [e]; exact ren_const j 1597 (by omega)
  rw [← prepare_ren j h0 (by omega)]
  simp only [LeaveSelector.post, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  by_cases c1 : q = (ports 10).crossing ∨ q = (ports 10).near
  · rw [if_pos (i1.mpr c1), if_pos c1]; rfl
  · rw [if_neg (fun h => c1 (i1.mp h)), if_neg c1]
    by_cases c2 : q = 1597
    · rw [if_pos (i2.mpr c2), if_pos c2, rE_conj, signExpr_ren j h0 (by omega) k]
      simp only [rE, cross_eq j]
    · rw [if_neg (fun h => c2 (i2.mp h)), if_neg c2]
      exact hs q hq

theorem restored_good (k : LeaveSelector.Mode) : Good D (LeaveSelector.restored (ports 10) false k) := by
  intro q hq
  simp only [LeaveSelector.restored, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  split_ifs
  · exact hq
  · exact start_good k q hq

theorem restored_rel (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : LeaveSelector.Mode) :
    Rel D (ren j) (LeaveSelector.restored (ports j) false k) (LeaveSelector.restored (ports 10) false k) := by
  intro q hq
  have i1 := cn_iff j h0 (by omega) q hq
  simp only [LeaveSelector.restored, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  by_cases c1 : q = (ports 10).crossing ∨ q = (ports 10).near
  · rw [if_pos (i1.mpr c1), if_pos c1]; rfl
  · rw [if_neg (fun h => c1 (i1.mp h)), if_neg c1]
    exact start_rel j h0 (by omega) k q hq

theorem affected_ren (j : Fin 23) :
    (LeaveSelector.affected (ports 10)).map (ren j) = LeaveSelector.affected (ports j) := by
  simp only [LeaveSelector.affected, List.map_append, List.map_cons, List.map_nil, cross_eq j, near_eq j]
  congr 1

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen
open Arithmetic RecordedQuantum Partial GateMirror HighBankFirstHit LeaveSelector
open ECDSAAdd.Entrant.StairPacket.LeaveJ
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000



/-! The four symbolic certificates at block 10. -/

theorem cert10_control : ∀ k : Mode,
    reads (ports 10) (sim (prepare 10) (LeaveSelector.start (ports 10) false k)) = controls (ports 10) k := by
  decide +kernel
theorem cert10_clean : ∀ k : Mode, targetCert (ports 10) (prepare 10) (retire 10) false k = true := by
  decide +kernel
theorem cert10_tag : ∀ k : Mode, ∀ i : Fin 16,
    sim (prepare 10) (LeaveSelector.start (ports 10) false k) (tagsP.getD i 0) =
      .bit (enabled k && decide (i.val = key k)) := by
  decide +kernel
theorem cert10_foot : (prepare 10 ++ retire 10).all (fun o => decide (o.dst ∈ affected (ports 10))) = true := by
  decide +kernel

/-! Every block. -/

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.controlCert (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) :
    reads (ports j) (sim (prepare j) (LeaveSelector.start (ports j) false k)) = controls (ports j) k := by
  have hσ := ren_inj j h0 (by omega)
  have hs := (sim_rel hσ (prepare 10) prep10_in _ _ (start_good k) (start_rel j h0 (by omega) k)).1
  have c := cert10_control k
  rw [← prepare_ren j h0 (by omega)]
  simp only [reads, controls, List.cons.injEq] at c ⊢
  obtain ⟨c1, c2, c3, c4, -⟩ := c
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · rw [← near_eq j, hs _ (by decide), c1]; rfl
  · rw [← cross_eq j, hs _ (by decide), c2, crossing_ren j h0 (by omega) k]
  · have e := hs 1596 (by decide)
    rw [ren_const j 1596 (by omega)] at e
    rw [e, c3, signExpr_ren j h0 (by omega) k]
  · have e := hs 1597 (by decide)
    rw [ren_const j 1597 (by omega)] at e
    rw [e, c4, rE_conj, crossing_ren j h0 (by omega) k, signExpr_ren j h0 (by omega) k]

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.cleanCert (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) :
    targetCert (ports j) (prepare j) (retire j) false k = true := by
  have hσ := ren_inj j h0 (by omega)
  obtain ⟨v, r, gd⟩ := exits_rel hσ (retire 10) retire10_in _ _ (post_good k) (post_rel j h0 (by omega) k)
  have c := cert10_clean k
  simp only [targetCert] at c ⊢
  rw [← retire_ren j h0 (by omega), v, ← affected_ren j, List.all_map]
  refine Eq.trans ?_ c
  refine congrArg (and _) ?_
  apply all_congr_mem
  intro q hq
  have hqD : D q := affected10_in q hq
  simp only [Function.comp_apply]
  rw [r q hqD, restored_rel j h0 (by omega) k q hqD]
  apply decide_eq_decide.mpr
  exact ⟨rE_inj hσ _ _ (gd q hqD) (restored_good k q hqD), fun e => by rw [e]⟩

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.tagCertificate (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) (i : Fin 16) :
    sim (prepare j) (LeaveSelector.start (ports j) false k) (tagsP.getD i 0) =
      .bit (enabled k && decide (i.val = key k)) := by
  have hs := (sim_rel (ren_inj j h0 (by omega)) (prepare 10) prep10_in _ _ (start_good k) (start_rel j h0 (by omega) k)).1
  have ht := tags_range i i.isLt
  have e := hs (tagsP.getD i 0) (Or.inl ht)
  rw [ren_const j _ ht] at e
  rw [← prepare_ren j h0 (by omega), e, cert10_tag k i]; rfl

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.foot_ok (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    (prepare j ++ retire j).all (fun o => decide (o.dst ∈ affected (ports j))) = true := by
  have hσ := ren_inj j h0 (by omega)
  rw [← prepare_ren j h0 (by omega), ← retire_ren j h0 (by omega), ← List.map_append, List.all_map, ← cert10_foot]
  apply all_congr_mem
  intro o ho
  have hoD : OpIn D o := ops10_in o ho
  simp only [Function.comp_apply, rOp_dst, ← affected_ren j]
  apply decide_eq_decide.mpr
  constructor
  · intro h
    obtain ⟨x, hx, e⟩ := List.mem_map.mp h
    rw [← hσ x o.dst (affected10_in x hx) (dst_mem o hoD) e]; exact hx
  · intro h; exact List.mem_map.mpr ⟨_, h, rfl⟩

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.witnessCert (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) :
    witnesses (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) (swaps j) k (restored (ports j) false k) := by
  obtain ⟨g1, g2, g3⟩ := geo j
  refine ⟨?_, ?_, ?_, ?_, fun i => ⟨?_, ?_⟩⟩
  · simp only [restored, LeaveSelector.start, ports, Bool.not_false, Bool.true_and, decide_eq_true_eq,
      Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · simp only [restored, LeaveSelector.start, ports, Bool.not_false, Bool.true_and, decide_eq_true_eq,
      Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · simp only [restored, LeaveSelector.start, ports, Bool.not_false, Bool.true_and, decide_eq_true_eq,
      Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · simp only [restored, LeaveSelector.start, ports, Bool.not_false, Bool.true_and, decide_eq_true_eq,
      Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · have hi := i.isLt
    simp only [restored, LeaveSelector.start, ports, LeaveSelector.tags, Bool.not_false, Bool.true_and,
      decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | simp only [Nat.add_sub_cancel_left]
  · have hr := swaps_range j h0 (by omega) i i.isLt
    simp only [restored, LeaveSelector.start, ports, Bool.not_false, Bool.true_and, decide_eq_true_eq,
      Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.prefix_parts : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 →
    GateMirror.forward (leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      leaveFix5 (start j) (Shadow7.sbP (start j))) =
      withHits (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) false (swaps j) ((prepare j).map Op.enter) := by
  decide +kernel

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.retire_parts : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 →
    GateMirror.forward (leaveFix11 (start j) (Shadow7.sbP (start j))) = (retire j).map Op.exit ∧
    GateMirror.forward (leaveFix12 (start j) (Shadow7.sbP (start j))) = dropAll 1560 (swaps j) LeaveSelector.tags 0 15 := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror RecordedQuantum HighBankFirstHit LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-! Selector semantics (dadon's `preparedState`, `selected`, `complete`, `clear`, `retiredFull`). -/

def fullPrefix (j : Fin 23) : List Gate :=
  leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++ leaveFix5 (start j) (Shadow7.sbP (start j))

theorem far_ne (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    (Shadow7.e0P (start j) + 3 : Wire) ≠ 1559 ∧ (Shadow7.e0P (start j) + 3 : Wire) ≠ 1560 := by
  have r := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  unfold Wire; omega

theorem preparedState (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (v : BasisState)
    (small : Nat) (k : Mode) (mode : k = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) small)
    (a : s.basis 1559 = false) (b : s.basis 1560 = false)
    (input : ∀ q, q ≠ 1559 → q ≠ 1560 → s.basis q = (before (ports j) false k q).read v)
    (exchange : right k = true → ∀ i < 15, i ≤ key k → s.basis (swaps j i) = decide (i = key k)) :
    run (GateMirror.forward (fullPrefix j)) m s =
      ⟨s.phase, fun q => (sim (prepare j) (LeaveSelector.start (ports j) false k) q).read v⟩ := by
  rw [fullPrefix, prefix_parts j h0 (by omega)]
  exact allSites (ports j) _ _ false _ (swaps j) (hit_sites j h0 (by omega)) (fun i hi => swaps_apart j h0 (by omega) i hi) s m v small
    (far_ne j h0 (by omega)).1 (far_ne j h0 (by omega)).2 a b k mode input exchange

theorem selected (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (v : BasisState)
    (small : Nat) (k : Mode) (mode : k = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) small)
    (a : s.basis 1559 = false) (b : s.basis 1560 = false)
    (input : ∀ q, q ≠ 1559 → q ≠ 1560 → s.basis q = (before (ports j) false k q).read v)
    (exchange : right k = true → ∀ i < 15, i ≤ key k → s.basis (swaps j i) = decide (i = key k)) (i : Fin 16) :
    (run (GateMirror.forward (fullPrefix j)) m s).basis (tagsP.getD i 0) = (enabled k && decide (i.val = key k)) := by
  rw [preparedState j h0 (by omega) s m v small k mode a b input exchange]
  exact congrArg (Expr.read v) (tagCertificate j h0 (by omega) k i)

theorem complete (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (v : BasisState)
    (small : Nat) (k : Mode) (mode : k = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) small)
    (a : s.basis 1559 = false) (b : s.basis 1560 = false)
    (input : ∀ q, q ≠ 1559 → q ≠ 1560 → s.basis q = (before (ports j) false k q).read v)
    (exchange : right k = true → ∀ i < 15, i ≤ key k → s.basis (swaps j i) = decide (i = key k)) :
    let out := run (GateMirror.forward (fullPrefix j)) m s
    out.phase = s.phase ∧ out.basis (Shadow7.e0P (start j) + 7) = nearby k ∧
      out.basis (Shadow7.e0P (start j) + 6) = (crossing (ports j) k).read v ∧
      out.basis 1596 = (signExpr (ports j) k).read v ∧
      out.basis 1597 = ((crossing (ports j) k).read v && (signExpr (ports j) k).read v) := by
  rw [fullPrefix, prefix_parts j h0 (by omega)]
  exact assembled (ports j) _ _ false _ (swaps j) (hit_sites j h0 (by omega)) (fun i hi => swaps_apart j h0 (by omega) i hi) s m v small
    (far_ne j h0 (by omega)).1 (far_ne j h0 (by omega)).2 a b k mode input exchange (controlCert j h0 (by omega) k)

/-- dadon's `Leave{s}Selector.clear` (forward): the retired selector word Shadow7.restores the selector wires. -/
theorem clear (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀ q, s.basis q = (post (ports j) (prepare j) false k q).read v) :
    run ((retire j).map Op.exit) m s = ⟨s.phase, fun q => (restored (ports j) false k q).read v⟩ :=
  cleanup (ports j) (prepare j) (retire j) false k s m v input (cleanCert j h0 (by omega) k)
    (fun o h => of_decide_eq_true (List.all_eq_true.mp (foot_ok j h0 (by omega)) o h))

/-- dadon's `Leave{s}Selector.retiredFull` (forward): `fix11 ++ fix12 ++ flags` releases the hits and flags. -/
theorem retiredFull (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) (s : State) (m : List Bool)
    (v : BasisState) (input : ∀ q, s.basis q = (post (ports j) (prepare j) false k q).read v)
    (l : left k = (v (Shadow7.e0P (start j) + 3) && v (Shadow7.e0P (start j) + 4)))
    (r : right k = (v (Shadow7.e0P (start j) + 3) && !v (Shadow7.e0P (start j) + 4)))
    (exchange : right k = true → ∀ i < 15, i ≤ key k → v (swaps j i) = decide (i = key k)) :
    run ((retire j).map Op.exit ++ (dropAll 1560 (swaps j) LeaveSelector.tags 0 15 ++
        (flagOps (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) true).reverse.map Op.exit)) m s =
      ⟨s.phase, clearKey (fun q => (restored (ports j) false k q).read v)⟩ := by
  have rr := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  exact full_release _ _ (swaps j) (hit_sites j h0 (by omega))
    (fun i hi k hk e => by have a := swaps_range j h0 (by omega) i hi; simp only [LeaveSelector.tags] at e; unfold Wire at *; omega)
    (by omega) (by omega) true k s m v _ _ (clear j h0 (by omega) k s m v input) (witnessCert j h0 (by omega) k) l r exchange

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror HighBankJoin HighBankReassemble SkywalkNat IntegerHigh Shadow HighBankSum LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}NearMiddle.result`: no tag hot, zero bank, no crossing. -/
theorem nearMiddle_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (X : Nat) (bound : X < 2^18) (s : State)
    (m : List Bool) (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (off : ∀ q ∈ tagsP, s.basis q = false)
    (shadow : ∀ i < 18, s.basis (Shadow7.a0P (start j) + i) = X.testBit i)
    (bank : regValue (ys j) s.basis = 0) (crossZero : s.basis (Shadow7.e0P (start j) + 6) = false)
    (scratch : s.basis 1614 = false) :
    let out := run (GateMirror.forward (middleOps (start j))) m s
    out.phase = s.phase ∧
      (∀ i : Fin 18, out.basis (row j i).keep = X.testBit i ∧ out.basis (row j i).free = false) ∧
      (∀ i : Nat, 18 ≤ i → i < Shadow7.wpP (start j) + 15 → out.basis (Shadow7.bankW (start j) i) = false) ∧
      (∀ q, q ≠ 1613 → HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q →
        (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) → out.basis q = s.basis q) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  let early := GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j))
  let signBit : Program := [.X 1613, .CX 1597 1613]
  have a := nearHigh_result j h0 (by omega) s m clean selectZero padding off
  have bankZero : HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (s.basis (Shadow7.e0P (start j) + 6))
      (s.basis 1597) = 0 := by
    rw [bank, crossZero]; unfold HighBankAdjust.adjusted
    cases s.basis 1597 <;> simp
  generalize hv : run early m s = v at a
  generalize ht : m.drop (measurementCount early) = tape
  generalize hu : run signBit tape v = u
  have bits (i : Nat) (hi : i < Shadow7.wpP (start j) + 15) : v.basis (Shadow7.bankW (start j) i) = false := by
    have := a.bits i hi; rw [bankZero] at this; simpa using this
  have unchanged (q : Wire) (ne : q ≠ 1613) : u.basis q = v.basis q := by
    rw [← hu]; simp [signBit, run, writeBit, Function.update, ne]
  have old (q : Wire) (ne : q ≠ 1613) (ext : HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q) :
      u.basis q = s.basis q := (unchanged q ne).trans (a.frame q ext)
  have bankOut : ∀ q : Nat, (1556 ≤ q ∧ q ≤ 1597) ∨ (q ≤ 785) →
      HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q := by
    intro q hq i hi e
    have b := Shadow7.bank_cases w1 w2 hi
    unfold Wire at *; omega
  have Shadow7.stable : ∀ i, i < Shadow7.wpP (start j) + 15 → (1613:Wire) ≠ Shadow7.bankW (start j) i := fun i hi => (layout j h0 (by omega)).separate i hi
  have readTags (q : Wire) (hq : q ∈ tagsP) : u.basis q = false := by
    have t := tags_range' q hq
    exact (old q (by unfold Wire at *; omega) (bankOut q (Or.inl (by unfold Wire at *; omega)))).trans (off q hq)
  have readShadow (i : Nat) (hi : i < 18) : u.basis (Shadow7.a0P (start j) + i) = X.testBit i :=
    (old _ (by unfold Wire at *; omega) (bankOut _ (Or.inr (by omega)))).trans (shadow i hi)
  have readTube (i : Nat) (hi : i < 18) : u.basis (Shadow7.bankW (start j) i) = false :=
    (unchanged _ (Shadow7.stable i (by omega)).symm).trans (bits i (by omega))
  have zero := (old 1614 (by decide) (fun i hi e => by
    have b := Shadow7.bank_cases w1 w2 hi; unfold Wire at *; omega)).trans scratch
  have word := nearWord_combine j h0 (by omega) X bound u (tape.drop (measurementCount signBit)) readTags readShadow readTube zero
  dsimp only
  have parts : GateMirror.forward (middleOps (start j)) = early ++ (signBit ++ GateMirror.forward (Shadow7.leaveJoin (start j))) := by
    simp only [middleOps, early, signBit, forward_app, fix8_forward, List.append_assoc]
  rw [parts, run_append, run_take, run_append, run_take, hv, ht, hu]
  refine ⟨word.1.trans ((by rw [← hu]; simp [signBit, run] : u.phase = v.phase).trans a.phase), word.2.1, ?_, ?_⟩
  · intro i lo hi
    have outsideRows : ∀ c ∈ cols j, Shadow7.bankW (start j) i ≠ c.shadow ∧ Shadow7.bankW (start j) i ≠ c.tube := by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk
      have b := Shadow7.bank_cases w1 w2 hi
      refine ⟨by dsimp only; unfold Wire at *; omega, fun e => ?_⟩
      have := Shadow7.bank_inj w1 w2 hi (by omega) e; omega
    exact (word.2.2 _ outsideRows).trans ((unchanged _ (Shadow7.stable i hi).symm).trans (bits i hi))
  · intro q ne ext away
    exact (word.2.2 q away).trans ((unchanged q ne).trans (a.frame q ext))

/-! OutputPorts. -/

/-- dadon's `Leave{s}OutputPorts.live`: the output register's wires. -/
def live (j : Fin 23) (i : Nat) : Wire := if i < Shadow7.lowsP (start j) then Shadow7.a0P (start j) + i else Shadow7.bankW (start j) i

theorem live_row (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Fin 18) : live j i.val = (row j i).keep := by
  have g := row_eq j i
  unfold Column.keep live
  rw [g.2.2.1]
  by_cases h : i.val < Shadow7.lowsP (start j)
  · simp [h, g.1]
  · simp [h, g.2.1]

theorem activeBits (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (X H : Nat) (k : Fin 16) (s : State)
    (lo : ∀ i : Fin 18, s.basis (row j i).keep = (2^k.val*H + X%2^k.val).testBit i.val)
    (hi : ∀ i : Nat, 18 ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = (2^k.val*H).testBit i) :
    ∀ i < Shadow7.wpP (start j) + 15, s.basis (live j i) = (2^k.val*H + X%2^k.val).testBit i := by
  have r := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  intro i bound
  by_cases h : i < 18
  · rw [live_row j h0 (by omega) ⟨i, h⟩]; exact lo ⟨i, h⟩
  · have nl : ¬ i < Shadow7.lowsP (start j) := by omega
    rw [live, if_neg nl, hi i (by omega) bound]
    have z := HighBankJoin.merged_bits X H k.val i
    have kval := k.isLt
    have a : (X%2^k.val).testBit i = false := by simpa only [if_pos (show k.val ≤ i by omega)] using z.1
    simpa only [a, Bool.false_xor] using z.2

theorem inactiveBits (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (X : Nat) (small : X < 2^18) (s : State)
    (lo : ∀ i : Fin 18, s.basis (row j i).keep = X.testBit i.val)
    (hi : ∀ i : Nat, 18 ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false) :
    ∀ i < Shadow7.wpP (start j) + 15, s.basis (live j i) = X.testBit i := by
  have r := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  intro i bound
  by_cases h : i < 18
  · rw [live_row j h0 (by omega) ⟨i, h⟩]; exact lo ⟨i, h⟩
  · have nl : ¬ i < Shadow7.lowsP (start j) := by omega
    rw [live, if_neg nl, hi i (by omega) bound,
      Nat.testBit_lt_two_pow (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) (by omega)))]

/-! TrueMiddle (dadon's `Leave{s}TrueMiddle`): the actual word-update values. -/

namespace TrueMiddle
abbrev r (j : Fin 23) (z : SkywalkNat.State) := reduced (Shadow7.sbP (start j)) 15 z
def key (j : Fin 23) (z : SkywalkNat.State) : Fin 16 :=
  ⟨if 2^(Shadow7.sbP (start j)) ≤ z.u then 0 else wait 15 z.u, by have h := wait_le 15 z.u; split <;> omega⟩
def X (j : Fin 23) (z : SkywalkNat.State) := total (step^[15] (r j z)) / 2^(Shadow7.sbP (start j) + 1)
def F (j : Fin 23) (z : SkywalkNat.State) := total (step^[15] z) / 2^(Shadow7.sbP (start j) + 1)
def d (j : Fin 23) (z : SkywalkNat.State) := X j z / 2^(key j z).val
def neg (j : Fin 23) (z : SkywalkNat.State) :=
  cross (d j z) && (!(decide (2^(Shadow7.sbP (start j)) ≤ z.u)) && negative (oddBits (letters 15 (r j z))))
end TrueMiddle

/-- dadon's `Leave{s}TrueMiddle.actual`. -/
theorem trueMiddle_actual (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (z : SkywalkNat.State) (s : State)
    (m : List Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (odd : z.v % 2 = 1)
    (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (tag : ∀ q ∈ tagsP, s.basis q = if far (Shadow7.sbP (start j)) 15 z then hot (TrueMiddle.key j z) q else false)
    (shadow : ∀ i < 18, s.basis (Shadow7.a0P (start j) + i) = (TrueMiddle.X j z).testBit i)
    (bank : regValue (ys j) s.basis = if far (Shadow7.sbP (start j)) 15 z then high (Shadow7.sbP (start j)) 15 z else 0)
    (cin : s.basis (Shadow7.e0P (start j) + 6) = if far (Shadow7.sbP (start j)) 15 z then cross (TrueMiddle.d j z) else false)
    (sign : far (Shadow7.sbP (start j)) 15 z → s.basis 1597 = TrueMiddle.neg j z) (scratch : s.basis 1614 = false) :
    let u := run (GateMirror.forward (middleOps (start j))) m s
    u.phase = s.phase ∧ (∀ i < Shadow7.wpP (start j) + 15, u.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      (∀ i : Fin 18, u.basis (row j i).free = false) ∧
      ∀ q, q ≠ 1613 → HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q →
        (∀ a ∈ cols j, q ≠ a.shadow ∧ q ≠ a.tube) → u.basis q = s.basis q := by
  dsimp only
  by_cases f : far (Shadow7.sbP (start j)) 15 z
  · simp only [if_pos f] at tag bank cin
    have law := LeaveJ7.Far.far_result (Shadow7.sbP (start j)) (Shadow7.wpP (start j)) z small f odd room
    change TrueMiddle.d j z = (cross (TrueMiddle.d j z)).toNat + 2*(!TrueMiddle.neg j z).toNat ∧
      TrueMiddle.F j z = 2^(TrueMiddle.key j z).val * HighBankAdjust.adjusted (high (Shadow7.sbP (start j)) 15 z) (Shadow7.wpP (start j))
        (cross (TrueMiddle.d j z)) (TrueMiddle.neg j z) + TrueMiddle.X j z % 2^(TrueMiddle.key j z).val at law
    rw [← cin, ← sign f, ← bank] at law
    have out := middle_result j h0 (by omega) (TrueMiddle.key j z) (TrueMiddle.X j z) s m clean selectZero padding tag shadow law.1 scratch
    refine ⟨out.1, ?_, fun i => (out.2.1 i).2, out.2.2.2⟩
    rw [law.2]
    exact activeBits j h0 (by omega) _ _ _ _ (fun i => (out.2.1 i).1) out.2.2.1
  · simp only [if_neg f] at tag bank cin
    have law := LeaveShadowRails.near_result (Shadow7.sbP (start j)) z f
    have eq : TrueMiddle.X j z = TrueMiddle.F j z := by unfold TrueMiddle.X TrueMiddle.F TrueMiddle.r; rw [law.1]
    have bound : TrueMiddle.X j z < 2^18 := eq ▸ law.2
    have out := nearMiddle_result j h0 (by omega) (TrueMiddle.X j z) bound s m clean selectZero padding tag shadow bank cin scratch
    refine ⟨out.1, ?_, fun i => (out.2.1 i).2, out.2.2.2⟩
    rw [← eq]
    exact inactiveBits j h0 (by omega) _ bound _ (fun i => (out.2.1 i).1) out.2.2.1


/-! Loaded (dadon's `Leave{s}Loaded`) and SignClose (dadon's `Leave{s}SignClose`). -/

/-- dadon's `Leave{s}RetireActual.prior`: the selector state after the prepared word. -/
def prior (j : Fin 23) (k : Mode) : Sym := sim (prepare j) (LeaveSelector.start (ports j) false k)

theorem tags_inj (i i' : Nat) (hi : i < 16) (hi' : i' < 16) (e : tagsP.getD i 0 = tagsP.getD i' 0) : i = i' := by
  have h : ∀ a b : Fin 16, tagsP.getD a 0 = tagsP.getD b 0 → a = b := by decide
  exact congrArg Fin.val (h ⟨i, hi⟩ ⟨i', hi'⟩ e)

theorem physicalTags (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) (q : Wire) (hq : q ∈ tagsP) :
    prior j k q = .bit (enabled k && decide (q = tagsP.getD (LeaveSelector.key k) 0)) := by
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 16 ∧ tagsP.getD i 0 = q := by
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hq
    exact ⟨i, by simpa [tagsP] using hi, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩
  rw [prior, tagCertificate j h0 (by omega) k ⟨i, hi⟩]
  congr 2
  by_cases hk : LeaveSelector.key k < 16
  · exact Bool.eq_iff_iff.mpr ⟨fun h => by simp_all, fun h => by
      simp only [decide_eq_true_eq] at h ⊢; exact tags_inj _ _ hi hk h⟩
  · have hne : i ≠ LeaveSelector.key k := fun eq => hk (eq ▸ hi)
    have hk' : tagsP.getD (LeaveSelector.key k) 0 = 0 := by
      rw [List.getD_eq_default]
      simp only [tagsP, List.length]
      exact Nat.not_lt.mp hk
    rw [hk']
    have nz : tagsP.getD i 0 ≠ 0 := by
      have t := tags_range' _ (tags_mem i hi)
      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 1556) t.1)
    simp only [decide_eq_false hne, decide_eq_false nz, Bool.and_false]

theorem loaded_tags (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (z : SkywalkNat.State) (v : BasisState) (q : Wire)
    (hq : q ∈ tagsP) :
    (prior j (actualMode (Shadow7.sbP (start j)) z) q).read v =
      if far (Shadow7.sbP (start j)) 15 z then hot (TrueMiddle.key j z) q else false := by
  rw [physicalTags j h0 (by omega) _ _ hq]
  by_cases f : far (Shadow7.sbP (start j)) 15 z
  · rw [if_pos f]
    obtain ⟨idx, _, on⟩ := modeKey (Shadow7.sbP (start j)) z f
    simp only [Expr.read, on, Bool.true_and, idx]
    rfl
  · simp [f, Expr.read, actualMode, farMode, ofFlags, enabled]

theorem controlsAt (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) :
    prior j k (Shadow7.e0P (start j) + 6) = crossing (ports j) k ∧
      prior j k 1597 = conj (crossing (ports j) k) (signExpr (ports j) k) := by
  have h := controlCert j h0 (by omega) k
  simp only [reads, LeaveSelector.controls, List.cons.injEq, and_true] at h
  exact ⟨h.2.1, h.2.2.2⟩

/-- dadon's `Leave{s}Loaded.signed`. -/
theorem loaded_signed (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (z : SkywalkNat.State) (ref : BasisState)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (odd : z.v % 2 = 1)
    (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (bits : ∀ i < 16, ref ((ports j).u + i) = (TrueMiddle.X j z).testBit i)
    (par : parityBits (ports j) ref = oddBits (letters 15 (reduced (Shadow7.sbP (start j)) 15 z))) :
    let k := actualMode (Shadow7.sbP (start j)) z
    let s := fun q => (prior j k q).read ref
    s (Shadow7.e0P (start j) + 6) = (if far (Shadow7.sbP (start j)) 15 z then cross (TrueMiddle.d j z) else false) ∧
      s 1597 = (s (Shadow7.e0P (start j) + 6) && (signExpr (ports j) k).read ref) ∧
      (far (Shadow7.sbP (start j)) 15 z → s 1597 = TrueMiddle.neg j z) := by
  have h := trueControls_shadow7 (Shadow7.sbP (start j)) (Shadow7.wpP (start j)) z small.1 odd room (ports j) ref bits par
  obtain ⟨cx, gate⟩ := controlsAt j h0 (by omega) (actualMode (Shadow7.sbP (start j)) z)
  dsimp only
  rw [cx, gate, read_conj]
  refine ⟨h.1, rfl, ?_⟩
  intro f
  rw [h.1, h.2 f, if_pos f]
  rfl

theorem dest_forward (gs : List Gate) : (GateMirror.forward gs).map LeaveReadoutFrame.destination = gs.map target := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [GateMirror.forward, List.map_cons] at ih ⊢
    rw [ih]; cases g <;> rfl

theorem join_targets (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    AllAT (fun _ => True) (fun t => t ≠ 1613 ∧ t ≠ 1597) (Shadow7.leaveJoin (start j)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  unfold Shadow7.leaveJoin
  refine allAT_append (allAT_digitsG _ _ _ _ trivial trivial _ _ (fun i _ hi => ⟨trivial, ?_, ?_⟩))
    (allAT_wordG _ ⟨trivial, by decide⟩ _ (fun c hc => ?_))
  · dsimp only; unfold Wire at *; omega
  · dsimp only; unfold Wire at *; omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
    exact ⟨fun _ _ => trivial, ⟨trivial, by dsimp only; unfold Wire at *; omega⟩,
      ⟨trivial, by dsimp only; unfold Wire at *; omega⟩⟩

/-- dadon's `Leave{s}SignClose.result`: `middle ++ fix10` closes the sign bit. -/
theorem signClose_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (initial : (run (GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j))) m s).basis 1613 = false) :
    let u := run (GateMirror.forward (middleOps (start j))) m s
    run (GateMirror.forward (middleOps (start j) ++ leaveFix10 (start j) (Shadow7.sbP (start j)))) m s =
      ⟨u.phase, writeBit u.basis 1613 false⟩ := by
  dsimp only
  have fx : GateMirror.forward (leaveFix10 (start j) (Shadow7.sbP (start j))) = [.CX 1597 1613, .X 1613] := rfl
  have notJ : ∀ q, (q = 1613 ∨ q = 1597) → q ∉ (GateMirror.forward (Shadow7.leaveJoin (start j))).map LeaveReadoutFrame.destination := by
    intro q hq hm
    rw [dest_forward] at hm
    obtain ⟨g, hg, e⟩ := List.mem_map.mp hm
    have t := (join_targets j h0 (by omega) g hg).2
    rcases hq with rfl|rfl
    · exact t.1 e
    · exact t.2 e
  have parts : GateMirror.forward (middleOps (start j)) = GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j)) ++
      ([.X 1613, .CX 1597 1613] ++ GateMirror.forward (Shadow7.leaveJoin (start j))) := by
    simp only [middleOps, forward_app, fix8_forward, List.append_assoc]
  generalize hu : run (GateMirror.forward (middleOps (start j))) m s = u
  have hflag : u.basis 1613 = !u.basis 1597 := by
    rw [← hu, parts, run_append, run_take, run_append, run_take,
      LeaveReadoutFrame.preserved _ _ _ _ (notJ _ (Or.inl rfl)), LeaveReadoutFrame.preserved _ _ _ _ (notJ _ (Or.inr rfl))]
    simp [run, writeBit, Function.update, initial]
  rw [forward_app, run_append, run_take, hu, fx]
  simp only [run, writeBit, Function.update]
  cases hb : u.basis 1597 <;> simp [hflag, hb, Bool.xor]

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror HighBankJoin SkywalkNat IntegerHigh Shadow HighBankSum LeaveSelector RecordedQuantum
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}RetireActual.paritySites` (= the history letters). -/
def paritySites (j : Fin 23) : List Wire := List.range' (start j + 16) 15

/-- Destinations of `prepare`, read off the op list. Not a selector simulation. -/
theorem prepare_dst : ∀ (j : Fin 23), 1 ≤ j.val → j.val ≤ 20 →
    ∀ t ∈ (prepare j).map Op.dst, (1559 ≤ t ∧ t ≤ 1597) ∨ t = (ports j).crossing ∨ t = (ports j).near := by
  decide +kernel

/-! The selector word after `prepare` reads only the history letters: an invariant of the symbolic
simulator, proved from the Shadow7.shape of the op list (no simulation, no decide over the modes). -/

/-- The hit and tag bits `1559..1575`. -/
abbrev InBits (q : Nat) : Prop := 1559 ≤ q ∧ q ≤ 1575
/-- The prepared word `1576..1596`. -/
abbrev InBand (q : Nat) : Prop := 1576 ≤ q ∧ q ≤ 1596
/-- The block's history letters. -/
abbrev IsHist (j : Fin 23) (q : Nat) : Prop := start j + 16 ≤ q ∧ q ≤ start j + 30

/-- Wires a band write may read. -/
abbrev ArgOK (j : Fin 23) (a : Nat) : Prop := InBits a ∨ IsHist j a ∨ InBand a

/-- An op does not write the history or the bit wires, and a band write reads only `ArgOK` wires. -/
abbrev OpGood (j : Fin 23) (o : Op) : Prop :=
  ¬ IsHist j o.dst ∧ ¬ InBits o.dst ∧ (InBand o.dst → ∀ a ∈ o.args, ArgOK j a)

structure SelClean (j : Fin 23) (k : Mode) (g : Sym) : Prop where
  bits : ∀ q : Nat, InBits q → g q = LeaveSelector.start (ports j) false k q
  hist : ∀ q : Nat, IsHist j q → g q = .wire q
  band : ∀ q : Nat, InBand q → ∀ r ∈ refs (g q), r ∈ paritySites j

theorem start_bit_refs (p : Ports) (k : Mode) (q : Nat) (h1 : 1559 ≤ q) (h2 : q ≤ 1575) :
    refs (LeaveSelector.start p false k q) = [] := by
  by_cases h : q = 1559
  · simp [LeaveSelector.start, h, refs]
  · by_cases h0 : q = 1560
    · simp [LeaveSelector.start, h, h0, refs]
    · have hr : 1561 ≤ q ∧ q ≤ 1575 := by omega
      simp [LeaveSelector.start, h, h0, hr, refs]

theorem refs_conj_sub {a b : Expr} {q : Wire} (hq : q ∈ refs (conj a b)) : q ∈ refs a ∨ q ∈ refs b := by
  rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    first | exact Or.inr hq | exact Or.inl hq | exact List.mem_append.mp hq

theorem refs_xor_sub {a b : Expr} {q : Wire} (hq : q ∈ refs (LeaveSelector.xor a b)) : q ∈ refs a ∨ q ∈ refs b := by
  unfold LeaveSelector.xor at hq
  split at hq
  · exact absurd hq List.not_mem_nil
  · rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
      first | exact Or.inr hq | exact Or.inl hq | exact List.mem_append.mp hq

theorem refs_foldr (p : Ports) : ∀ xs : List Nat,
    ∀ q ∈ refs (xs.foldr (fun j rest => conj (.wire (p.g + j)) rest) (.bit true)), ∃ t ∈ xs, q = p.g + t := by
  intro xs
  induction xs with
  | nil => intro q hq; exact absurd hq List.not_mem_nil
  | cons j js ih =>
    intro q hq
    rcases refs_conj_sub hq with h | h
    · exact ⟨j, List.mem_cons_self, List.mem_singleton.mp h⟩
    · obtain ⟨t, ht, e⟩ := ih q h
      exact ⟨t, List.mem_cons_of_mem _ ht, e⟩

theorem arg_refs (j : Fin 23) (k : Mode) {g : Sym} (hc : SelClean j k g) {a : Nat} (ha : ArgOK j a) :
    ∀ r ∈ refs (g a), r ∈ paritySites j := by
  intro r hr
  rcases ha with hbit | hh | hin
  · rw [hc.bits a hbit, start_bit_refs _ _ _ hbit.1 hbit.2] at hr
    exact absurd hr List.not_mem_nil
  · rw [hc.hist a hh] at hr
    have e : r = a := List.mem_singleton.mp hr
    rw [e, paritySites, List.mem_range'_1]
    exact ⟨hh.1, Nat.lt_succ_of_le hh.2⟩
  · exact hc.band a hin r hr

theorem symbolic_clean (j : Fin 23) (k : Mode) (o : Op) (g : Sym) (hc : SelClean j k g) (hg : OpGood j o) :
    SelClean j k (symbolic o g) := by
  obtain ⟨nh, nb, hargs⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    have hne : ¬ q = o.dst := fun e => nb (e ▸ hq)
    rw [show symbolic o g q = g q from if_neg hne]
    exact hc.bits q hq
  · intro q hq
    have hne : ¬ q = o.dst := fun e => nh (e ▸ hq)
    rw [show symbolic o g q = g q from if_neg hne]
    exact hc.hist q hq
  · intro q hq r hr
    by_cases hd : q = o.dst
    · cases o with
      | xor a t =>
        have hx : symbolic (.xor a t) g q = LeaveSelector.xor (g q) (g a) := if_pos hd
        rw [hx] at hr
        rcases refs_xor_sub hr with hsub | hsub
        · exact hc.band q hq r hsub
        · exact arg_refs j k hc (hargs (hd ▸ hq) a (by simp [Op.args])) r hsub
      | mix a b t =>
        have hx : symbolic (.mix a b t) g q = LeaveSelector.xor (g q) (conj (g a) (g b)) := if_pos hd
        rw [hx] at hr
        rcases refs_xor_sub hr with hsub | hsub
        · exact hc.band q hq r hsub
        · rcases refs_conj_sub hsub with h2 | h2
          · exact arg_refs j k hc (hargs (hd ▸ hq) a (by simp [Op.args])) r h2
          · exact arg_refs j k hc (hargs (hd ▸ hq) b (by simp [Op.args])) r h2
      | save a b t =>
        have hx : symbolic (.save a b t) g q = LeaveSelector.xor (g q) (conj (g a) (g b)) := if_pos hd
        rw [hx] at hr
        rcases refs_xor_sub hr with hsub | hsub
        · exact hc.band q hq r hsub
        · rcases refs_conj_sub hsub with h2 | h2
          · exact arg_refs j k hc (hargs (hd ▸ hq) a (by simp [Op.args])) r h2
          · exact arg_refs j k hc (hargs (hd ▸ hq) b (by simp [Op.args])) r h2
    · rw [show symbolic o g q = g q from if_neg hd] at hr
      exact hc.band q hq r hr

theorem sim_selClean (j : Fin 23) (k : Mode) : ∀ (os : List Op) (g : Sym),
    SelClean j k g → (∀ o ∈ os, OpGood j o) → SelClean j k (sim os g) := by
  intro os
  induction os with
  | nil => intro g hc _; exact hc
  | cons o os ih =>
    intro g hc ho
    exact ih (symbolic o g) (symbolic_clean j k o g hc (ho o List.mem_cons_self))
      (fun o' h => ho o' (List.mem_cons_of_mem _ h))

theorem start_clean (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) :
    SelClean j k (LeaveSelector.start (ports j) false k) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro q hq
    obtain ⟨a, b⟩ := hq
    have f1 : q ≠ 1559 := by omega
    have f2 : q ≠ 1560 := by omega
    have f3 : ¬ (1561 ≤ q ∧ q ≤ 1575) := by omega
    have f4 : ¬ (1576 ≤ q ∧ q ≤ 1597) := by omega
    have f5 : q ≠ Shadow7.e0P (start j) + 6 := by omega
    have f6 : q ≠ Shadow7.e0P (start j) + 7 := by omega
    simp [LeaveSelector.start, ports, f1, f2, f3, f4, f5, f6]
  · intro q hq r hr
    obtain ⟨a, b⟩ := hq
    have f1 : q ≠ 1559 := by omega
    have f2 : q ≠ 1560 := by omega
    have f3 : ¬ (1561 ≤ q ∧ q ≤ 1575) := by omega
    have f4 : 1576 ≤ q ∧ q ≤ 1597 := by omega
    have e : LeaveSelector.start (ports j) false k q = .bit false := by
      simp [LeaveSelector.start, f1, f2, f3, f4]
    rw [e] at hr
    exact absurd hr List.not_mem_nil

/-- Every op of `prepare` keeps the selector-symbol invariant. Read off the op list, not a simulation. -/
theorem prepare_good : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 → ∀ o ∈ prepare j, OpGood j o := by
  decide +kernel

theorem retireCerts (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) :
    (∀ i : Fin 38, post (ports j) (prepare j) false k (1559 + i.val) = prior j k (1559 + i.val) ∧
      ∀ q ∈ refs (prior j k (1559 + i.val)), q ∈ paritySites j) ∧
    (∀ q ∈ refs (signExpr (ports j) k), q ∈ paritySites j) ∧
    (∀ t ∈ (prepare j).map Op.dst, (1559 ≤ t ∧ t ≤ 1597) ∨ t = (ports j).crossing ∨ t = (ports j).near) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  refine ⟨?_, ?_, prepare_dst j h0 (by omega)⟩
  · intro i
    have hi : i.val < 38 := i.isLt
    have f5 : 1559 + i.val ≠ Shadow7.e0P (start j) + 6 := by omega
    have f6 : 1559 + i.val ≠ Shadow7.e0P (start j) + 7 := by omega
    have f7 : 1559 + i.val ≠ 1597 := by omega
    have peq : post (ports j) (prepare j) false k (1559 + i.val) = prior j k (1559 + i.val) := by
      simp [post, prior, ports, f5, f6, f7]
    refine ⟨peq, ?_⟩
    intro r hr
    have sc := sim_selClean j k (prepare j) (LeaveSelector.start (ports j) false k)
      (start_clean j h0 (by omega) k) (fun o ho => prepare_good j h0 (by omega) o ho)
    by_cases hb : 1559 + i.val ≤ 1575
    · have eq : prior j k (1559 + i.val) = LeaveSelector.start (ports j) false k (1559 + i.val) :=
        sc.bits (1559 + i.val) ⟨by omega, hb⟩
      rw [eq, start_bit_refs _ _ _ (by omega) hb] at hr
      exact absurd hr List.not_mem_nil
    · exact sc.band (1559 + i.val) ⟨by omega, by omega⟩ r hr
  · intro q hq
    unfold signExpr at hq
    split at hq
    · unfold suffixExpr at hq
      obtain ⟨t, ht, e⟩ := refs_foldr (ports j) ((List.range 15).drop _) q hq
      have ht15 : t < 15 := List.mem_range.mp (List.mem_of_mem_drop ht)
      have e' : q = start j + 16 + t := e
      rw [e', paritySites, List.mem_range'_1]
      exact ⟨by omega, by omega⟩
    · exact absurd hq List.not_mem_nil

/-- `fix11 ++ fix12 ++ Shadow7.lowSign` = dadon's `fullPostfix false` (the retired word, the hits, the flags). -/
theorem postfix_parts : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 →
    GateMirror.forward (leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j)) =
      (retire j).map Op.exit ++ (HighBankFirstHit.dropAll 1560 (swaps j) LeaveSelector.tags 0 15 ++
        (flagOps (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) true).reverse.map Op.exit) := by
  decide +kernel

/-- dadon's `Leave{s}RetireActual.result`. -/
theorem retireActual_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) (v : BasisState) (s : State)
    (m : List Bool)
    (bits : ∀ i : Fin 38, s.basis (1559 + i.val) = (prior j k (1559 + i.val)).read v)
    (history : ∀ q ∈ paritySites j, v q = s.basis q)
    (product : s.basis 1597 = (s.basis (Shadow7.e0P (start j) + 6) && (signExpr (ports j) k).read v))
    (l : LeaveSelector.left k = (s.basis (Shadow7.e0P (start j) + 3) && s.basis (Shadow7.e0P (start j) + 4)))
    (r : LeaveSelector.right k = (s.basis (Shadow7.e0P (start j) + 3) && !s.basis (Shadow7.e0P (start j) + 4)))
    (exchange : LeaveSelector.right k = true → ∀ i < 15, i ≤ LeaveSelector.key k →
      s.basis (swaps j i) = decide (i = LeaveSelector.key k)) :
    run (GateMirror.forward (leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++
      Shadow7.lowSign (start j))) m s = ⟨s.phase, cleared s.basis⟩ := by
  have rr := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  obtain ⟨cs, sg, cover⟩ := retireCerts j h0 (by omega) k
  have input (q : Nat) : s.basis q = (post (ports j) (prepare j) false k q).read s.basis := by
    by_cases mid : 1559 ≤ q ∧ q < 1597
    · let i : Fin 38 := ⟨q - 1559, by omega⟩
      have id : 1559 + i.val = q := by dsimp [i]; omega
      rw [← id, (cs i).1]
      exact (bits i).trans (readAgree _ _ _ (fun a h => history _ ((cs i).2 _ h)))
    by_cases exactSite : q = 1597
    · subst q
      have sign := readAgree (signExpr (ports j) k) v s.basis (fun a h => history _ (sg _ h))
      have f5 : (1597 : Nat) ≠ Shadow7.e0P (start j) + 6 := by omega
      have f6 : (1597 : Nat) ≠ Shadow7.e0P (start j) + 7 := by omega
      have form : post (ports j) (prepare j) false k 1597 =
          conj (.wire (Shadow7.e0P (start j) + 6)) (signExpr (ports j) k) := by
        simp [post, ports, f5, f6]
      rw [form, read_conj, ← sign]; exact product
    · have outside : q < 1559 ∨ 1597 < q := by omega
      have plain : post (ports j) (prepare j) false k q = .wire q := by
        apply postOutside _ _ _ _ outside
        intro cx nr member
        rcases cover q member with h|h|h
        · have ha : 1559 ≤ q := h.1
          have hb : q ≤ 1597 := h.2
          omega
        · exact cx h
        · exact nr h
      rw [plain]; rfl
  rw [postfix_parts j h0 (by omega), retiredFull j h0 (by omega) k s m s.basis input l r exchange,
    retiredBasis _ _ _ (by show 1597 < Shadow7.e0P (start j) + 6; omega) (by show 1597 < Shadow7.e0P (start j) + 7; omega)]


/-! Core (dadon's `Leave{s}Core.result`). -/

def workOps (s : Nat) : List Gate :=
  middleOps s ++ leaveFix10 s (Shadow7.sbP s) ++ (leaveFix11 s (Shadow7.sbP s) ++ leaveFix12 s (Shadow7.sbP s) ++ Shadow7.lowSign s)

theorem live_out (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) (hi : i < Shadow7.wpP (start j) + 15) :
    (live j i : Nat) ≠ 1613 ∧ ¬ (1559 ≤ (live j i : Nat) ∧ (live j i : Nat) ≤ 1597) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have b := Shadow7.bank_cases w1 w2 hi
  unfold live; split <;> unfold Wire at * <;> omega

/-- The history cells in the `sig` frame, exactly: on the B rail above every bank wire, or in the pool. -/
theorem swaps_cases (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) (hi : i < 15) :
    ((swaps j i : Nat) = start j + 1044 + i ∧ start j + 1044 + i ≤ 1300) ∨
      (Shadow7.e0P (start j) + 10 ≤ (swaps j i : Nat) ∧ (swaps j i : Nat) ≤ 1812) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have e := Shadow7.sig_hist (c := 1044 + i) w1 w2 (by omega) (by omega)
  unfold swaps; rw [show start j + 1044 + i = start j + (1044 + i) by omega]
  unfold Wire at *; omega

theorem free_out (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Fin 18) :
    ((row j i).free : Nat) ≠ 1613 ∧ ¬ (1559 ≤ ((row j i).free : Nat) ∧ ((row j i).free : Nat) ≤ 1597) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have g := row_eq j i
  have b := Shadow7.bank_cases w1 w2 (i := i.val) (by omega)
  unfold Column.free; rw [g.2.2.1]
  split <;> simp only [g.1, g.2.1] <;> unfold Wire at * <;> omega

/-- The wires the core must not touch (dadon's `Leave{s}Core.watched` facts). -/
theorem core_untouched (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Nat)
    (hq : (1559 ≤ q ∧ q ≤ 1597) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨ q = Shadow7.e0P (start j) + 6 ∨
      q = Shadow7.e0P (start j) + 3 ∨ q = Shadow7.e0P (start j) + 4 ∨ ∃ i < 15, q = swaps j i) :
    q ≠ 1613 ∧ HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q ∧
      ∀ c ∈ cols j, q ≠ c.shadow ∧ q ≠ c.tube := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have sw := swaps_cases j h0 (by omega)
  refine ⟨?_, fun i hi e => ?_, fun c hc => ?_⟩
  · rcases hq with h|h|h|h|h|⟨i, hi, rfl⟩
    all_goals (try (have := sw i hi)); unfold Wire at *; omega
  · have b := Shadow7.bank_cases w1 w2 hi
    rcases hq with h|h|h|h|h|⟨k, hk, rfl⟩
    all_goals (try (have := sw k hk)); unfold Wire at *; omega
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk
    have b := Shadow7.bank_cases w1 w2 (i := k) (by omega)
    rcases hq with h|h|h|h|h|⟨i, hi, rfl⟩
    all_goals (try (have := sw i hi)); dsimp only; unfold Wire at *; omega

theorem core_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (z : SkywalkNat.State) (s : State) (tape : List Bool)
    (k : Mode) (ref : BasisState)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (odd : z.v % 2 = 1)
    (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (tag : ∀ q ∈ tagsP, s.basis q = if far (Shadow7.sbP (start j)) 15 z then hot (TrueMiddle.key j z) q else false)
    (shadow : ∀ i < 18, s.basis (Shadow7.a0P (start j) + i) = (TrueMiddle.X j z).testBit i)
    (bank : regValue (ys j) s.basis = if far (Shadow7.sbP (start j)) 15 z then high (Shadow7.sbP (start j)) 15 z else 0)
    (cin : s.basis (Shadow7.e0P (start j) + 6) = if far (Shadow7.sbP (start j)) 15 z then cross (TrueMiddle.d j z) else false)
    (sign : far (Shadow7.sbP (start j)) 15 z → s.basis 1597 = TrueMiddle.neg j z)
    (bits : ∀ i : Fin 38, s.basis (1559 + i.val) = (prior j k (1559 + i.val)).read ref)
    (parity : ∀ q ∈ paritySites j, ref q = s.basis q)
    (product : s.basis 1597 = (s.basis (Shadow7.e0P (start j) + 6) && (signExpr (ports j) k).read ref))
    (leftFlag : LeaveSelector.left k = (s.basis (Shadow7.e0P (start j) + 3) && s.basis (Shadow7.e0P (start j) + 4)))
    (rightFlag : LeaveSelector.right k = (s.basis (Shadow7.e0P (start j) + 3) && !s.basis (Shadow7.e0P (start j) + 4)))
    (events : LeaveSelector.right k = true → ∀ i < 15, i ≤ LeaveSelector.key k → s.basis (swaps j i) = decide (i = LeaveSelector.key k)) :
    let out := run (GateMirror.forward (workOps (start j))) tape s
    out.phase = s.phase ∧ (∀ i < Shadow7.wpP (start j) + 15, out.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      (∀ i : Fin 18, out.basis (row j i).free = false) ∧ (∀ i : Fin 39, out.basis (1559 + i.val) = false) ∧
      (∀ q, HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q → (∀ a ∈ cols j, q ≠ a.shadow ∧ q ≠ a.tube) →
        out.basis q = cleared s.basis q) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have c1613 : s.basis 1613 = false := clean 1613 (by
    simp only [carries, List.mem_map, List.mem_range]
    exact ⟨15, by omega, by have p := Shadow7.pool_cases (i := 15) w1 w2; unfold Wire at *; omega⟩)
  have c1614 : s.basis 1614 = false := clean 1614 (by
    simp only [carries, List.mem_map, List.mem_range]
    exact ⟨16, by omega, by have p := Shadow7.pool_cases (i := 16) w1 w2; unfold Wire at *; omega⟩)
  have ar := trueMiddle_actual j h0 (by omega) z s tape small odd room clean c1613 padding tag shadow bank cin sign c1614
  have initial : (run (GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j))) tape s).basis 1613 = false := by
    by_cases f : far (Shadow7.sbP (start j)) 15 z
    · simp only [if_pos f] at tag
      exact ((high_result j h0 (by omega) (TrueMiddle.key j z) s tape clean c1613 padding tag).frame _ (layout j h0 (by omega)).separate).trans c1613
    · simp only [if_neg f] at tag
      exact ((nearHigh_result j h0 (by omega) s tape clean c1613 padding tag).frame _ (layout j h0 (by omega)).separate).trans c1613
  have fix := signClose_result j h0 (by omega) s tape initial
  generalize ha : run (GateMirror.forward (middleOps (start j))) tape s = a at ar fix
  generalize ht : run (GateMirror.forward (middleOps (start j) ++ leaveFix10 (start j) (Shadow7.sbP (start j)))) tape s = t at fix
  have saved (q : Nat) (mem : (1559 ≤ q ∧ q ≤ 1597) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨ q = Shadow7.e0P (start j) + 6 ∨
      q = Shadow7.e0P (start j) + 3 ∨ q = Shadow7.e0P (start j) + 4 ∨ ∃ i < 15, q = swaps j i) : t.basis q = s.basis q := by
    obtain ⟨diff, out, cols⟩ := core_untouched j h0 (by omega) q mem
    rw [fix]; simp only [writeBit, Function.update_of_ne diff]
    exact ar.2.2.2 q diff out cols
  have retire := retireActual_result j h0 (by omega) k ref t
    (tape.drop (measurementCount (GateMirror.forward (middleOps (start j) ++ leaveFix10 (start j) (Shadow7.sbP (start j))))))
    (fun i => (saved _ (Or.inl (by omega))).trans (bits i))
    (fun q h => (parity q h).trans (saved _ (Or.inr (Or.inl (by simp only [paritySites, List.mem_range'_1] at h; omega)))).symm)
    (by rw [saved 1597 (Or.inl (by omega)), saved _ (Or.inr (Or.inr (Or.inl rfl)))]; exact product)
    (by rw [saved _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), saved _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact leftFlag)
    (by rw [saved _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), saved _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact rightFlag)
    (fun on i hi h => (saved _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))))).trans (events on i hi h))
  dsimp only
  rw [show workOps (start j) = (middleOps (start j) ++ leaveFix10 (start j) (Shadow7.sbP (start j))) ++
    (leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j)) from by
      simp only [workOps, List.append_assoc]]
  rw [forward_app, run_append, run_take, ht, retire]
  have base (q : Wire) (diff : q ≠ 1613) : t.basis q = a.basis q := by rw [fix]; simp [writeBit, diff]
  have pass (q : Nat) (diff : q ≠ 1613 ∧ ¬ (1559 ≤ q ∧ q ≤ 1597)) : cleared t.basis q = a.basis q := by
    rw [cleared, if_neg diff.2]; exact base _ diff.1
  refine ⟨(congrArg State.phase fix).trans ar.1, ?_, ?_, ?_, ?_⟩
  · intro i h
    exact (pass _ (live_out j h0 (by omega) i h)).trans (ar.2.1 i h)
  · intro i
    exact (pass _ (free_out j h0 (by omega) i)).trans (ar.2.2.1 i)
  · intro i; have h := i.isLt
    change (if 1559 ≤ 1559 + i.val ∧ 1559 + i.val ≤ 1597 then _ else _) = _
    rw [if_pos (by omega)]
  · intro q out cs
    by_cases eq : q = 1613
    · subst q
      change t.basis 1613 = s.basis 1613
      rw [fix, c1613]
      simp [writeBit]
    · show cleared t.basis q = cleared s.basis q
      unfold cleared
      split
      · rfl
      · exact (base _ eq).trans (ar.2.2.2 _ eq out cs)


/-! Routed (dadon's `Leave{s}Routed.result`): `body` = `fullPrefix ++ work` (cuts 5..27). -/

theorem prefix_dest : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 → ∀ q ∈ (GateMirror.forward (fullPrefix j)).map LeaveReadoutFrame.destination,
    (1559 ≤ q ∧ q ≤ 1597) ∨ q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7 := by
  decide +kernel

theorem prefix_keep (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Nat)
    (hq : ¬ ((1559 ≤ q ∧ q ≤ 1597) ∨ q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7)) (s : State) (tape : List Bool) :
    (run (GateMirror.forward (fullPrefix j)) tape s).basis q = s.basis q :=
  LeaveReadoutFrame.preserved _ s tape q (fun h => hq (prefix_dest j h0 (by omega) q h))

def bodyOps (j : Fin 23) : List Gate := fullPrefix j ++ workOps (start j)

theorem routed_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (z : SkywalkNat.State) (s : State) (tape : List Bool)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (odd : z.v % 2 = 1)
    (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (shadow : ∀ i < 18, s.basis (Shadow7.a0P (start j) + i) = (TrueMiddle.X j z).testBit i)
    (bank : regValue (ys j) s.basis = if far (Shadow7.sbP (start j)) 15 z then high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ [(ports j).crossing, (ports j).near] ++ List.range' 1559 39, s.basis q = false)
    (par : parityBits (ports j) s.basis = oddBits (IntegerHigh.letters 15 (reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (swaps j i) = decide (i = LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z))) :
    let out := run (GateMirror.forward (bodyOps j)) tape s
    let t := run (GateMirror.forward (fullPrefix j)) tape s
    out.phase = s.phase ∧ (∀ i < Shadow7.wpP (start j) + 15, out.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      (∀ i : Fin 18, out.basis (row j i).free = false) ∧ (∀ i : Fin 39, out.basis (1559 + i.val) = false) ∧
      (∀ q, HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q → (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) →
        out.basis q = cleared t.basis q) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  let k := actualMode (Shadow7.sbP (start j)) z
  have base : ∀ q : Nat, 1561 ≤ q → q ≤ 1597 → s.basis q = false := by
    intro q lo hi
    apply zero
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q - 1559, by omega, by omega⟩
  have z59 : s.basis 1559 = false := zero _ (by simp)
  have z60 : s.basis 1560 = false := zero _ (by simp)
  have zc : s.basis (ports j).crossing = false := zero _ (by simp)
  have zn : s.basis (ports j).near = false := zero _ (by simp)
  have prepared := preparedState j h0 (by omega) s tape s.basis z.u k mode z59 z60 (beforeFresh _ _ _ base zc zn) events
  generalize ht : run (GateMirror.forward (fullPrefix j)) tape s = t at prepared
  have sym (q : Wire) : t.basis q = (prior j k q).read s.basis := congrArg (fun st : State => st.basis q) prepared
  have keep (q : Nat) (ok : ¬ ((1559 ≤ q ∧ q ≤ 1597) ∨ q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7)) :
      t.basis q = s.basis q := by rw [← ht]; exact prefix_keep j h0 (by omega) q ok s tape
  have math := loaded_signed j h0 (by omega) z s.basis small odd room
    (fun i hi => shadow i (Nat.lt_trans hi (by decide : 16 < 18))) par
  have flags := mode_flags (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4))
    (⟨IntegerHigh.wait 15 z.u, by have h := IntegerHigh.wait_le 15 z.u; omega⟩ : Fin 16)
  have k3 := keep (Shadow7.e0P (start j) + 3) (by omega)
  have k4 := keep (Shadow7.e0P (start j) + 4) (by omega)
  have leftOK : LeaveSelector.left k = (t.basis (Shadow7.e0P (start j) + 3) && t.basis (Shadow7.e0P (start j) + 4)) := by
    rw [k3, k4, show k = _ from mode]; exact flags.1
  have rightOK : LeaveSelector.right k = (t.basis (Shadow7.e0P (start j) + 3) && !t.basis (Shadow7.e0P (start j) + 4)) := by
    rw [k3, k4, show k = _ from mode]; exact flags.2.1
  have kc : ∀ q ∈ carries j, t.basis q = s.basis q := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    have p := Shadow7.pool_cases (i := i) w1 w2; apply keep; unfold Wire at *; omega
  have kp : ∀ i, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → t.basis (Shadow7.bankW (start j) i) = s.basis (Shadow7.bankW (start j) i) := by
    intro i a b; have bc := Shadow7.bank_cases w1 w2 b; apply keep; unfold Wire at *; omega
  have ks : ∀ i : Nat, i < 18 → t.basis (Shadow7.a0P (start j) + i) = s.basis (Shadow7.a0P (start j) + i) := by
    intro i hi; apply keep; omega
  have ky : ∀ q ∈ ys j, t.basis q = s.basis q := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    have bc := Shadow7.bank_cases w1 w2 (i := i) (by omega); apply keep; unfold Wire at *; omega
  have kpa : ∀ q ∈ paritySites j, t.basis q = s.basis q := by
    intro q hq; simp only [paritySites, List.mem_range'_1] at hq; apply keep; omega
  have ksw : ∀ i < 15, t.basis (swaps j i) = s.basis (swaps j i) := by
    intro i hi; have a := swaps_range j h0 h1 i hi; apply keep; unfold Wire at *; omega
  have done := core_result j h0 (by omega) z t (tape.drop (measurementCount (GateMirror.forward (fullPrefix j)))) k s.basis small odd room
    (fun q h => (kc q h).trans (clean q h)) (fun i lo hi => (kp i lo hi).trans (padding i lo hi))
    (fun q h => (sym q).trans (loaded_tags j h0 (by omega) z s.basis q h)) (fun i h => (ks i h).trans (shadow i h))
    (((regValue_eq_iff _ _ _).mpr (fun q h => ky q h)).trans bank)
    ((sym _).trans math.1) (fun far => (sym _).trans (math.2.2 far)) (fun i => sym _)
    (fun q h => (kpa q h).symm) (by rw [sym 1597, sym (Shadow7.e0P (start j) + 6)]; exact math.2.1) leftOK rightOK
    (fun on i hi h => (ksw i hi).trans (events on i hi h))
  dsimp only
  rw [bodyOps, forward_app, run_append, run_take, ht]
  exact ⟨done.1.trans (by rw [prepared]), done.2⟩


/-! Restored / RoutedRestore (dadon's `Leave{s}Restored`, `Leave{s}RoutedRestore`). -/

theorem smallM_length (j : Fin 23) : (smallM j).length = Shadow7.lowsP (start j) := by simp [smallM]

/-- dadon's `Leave{s}OutputPorts.outputRegisters` (low half). -/
theorem outputSmall (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (Z : Nat)
    (bits : ∀ i < Shadow7.wpP (start j) + 15, s.basis (live j i) = Z.testBit i) :
    regValue (smallA j) s.basis = Z % 2^(Shadow7.lowsP (start j)) := by
  have rr := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  have len : (smallA j).length = Shadow7.lowsP (start j) := by simp [smallA]
  rw [← len]
  apply EnterProof.value_of_bits (smallA j)
  intro i hi
  rw [len] at hi
  have g : (smallA j).getD i 0 = live j i := by
    simp [smallA, live, List.getD_eq_getElem?_getD, hi]
  rw [g]; exact bits i (by omega)

/-- dadon's `Leave{s}Restored.result`. -/
theorem restored_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (z : SkywalkNat.State) (sg : Bool) (s : State)
    (m : List Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (clean : ∀ q ∈ smallC j, s.basis q = false)
    (cleared : regValue (smallM j) s.basis = 0)
    (input : let r := step^[15] (reduced (Shadow7.sbP (start j)) 15 z)
      let F := step^[15] z
      let e := (PortalValues.negative sg r.u).toNat
      s.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ r.u - e) ∧
        (s.basis 1558).toNat = LeaveCompanion.upperBorrow (2^(Shadow7.sbP (start j))) r.u r.v e ∧
        regValue (smallA j) s.basis = ((F.u+F.v)/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j))) :
    let F := step^[15] z
    let e := (PortalValues.negative sg F.u).toNat
    let out := run (Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558) m s
    out.phase = s.phase ∧ (∀ q, q ∉ smallM j → out.basis q = s.basis q) ∧
      regValue (smallM j) out.basis = ((F.u - e)/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j)) := by
  have hardware := restore_run j h0 (by omega) s m clean cleared
  refine ⟨hardware.1, hardware.2.1, hardware.2.2.trans ?_⟩
  dsimp only at input ⊢
  have math := LeaveRestoreTruth.restored_shadow7 (Shadow7.sbP (start j)) (Shadow7.lowsP (start j)) z small.1 small.2 sg
  have sign := (LeaveRestoreTruth.truth_shadow7 (Shadow7.sbP (start j)) z small.1 sg).2.2.2
  rw [smallM_length, copyValue, input.1, input.2.1, input.2.2, sign]
  simpa only [decide_eq_true_eq] using math


/-! Target footprint of the Shadow7.body (for the families that read wires the Shadow7.body never writes). -/

/-- Targets of the work part of the Shadow7.body (adjust, barrel, join, the fixed tail): the A word, the B bank, and the
scratch below the anchored block `e0..e0+9` or the pool above it (never `e0+3 .. e0+9`, never the history cells). -/
def workT (j : Fin 23) (t : Nat) : Prop :=
  (Shadow7.a0P (start j) ≤ t ∧ t ≤ Shadow7.a0P (start j) + 17) ∨ (Shadow7.b0P (start j) + 18 ≤ t ∧ t ≤ 1043) ∨
    (1559 ≤ t ∧ (t ≤ Shadow7.e0P (start j) + 2 ∨ (Shadow7.e0P (start j) + 10 ≤ t ∧ t ≤ 1606 + Shadow7.wpP (start j))))
/-- Targets of the body: the work part plus the selector's (`fullPrefix`: `1559..1597`, `e0+6`, `e0+7`). -/
def midT (j : Fin 23) (t : Nat) : Prop := workT j t ∨ t = Shadow7.e0P (start j) + 6 ∨ t = Shadow7.e0P (start j) + 7

theorem bank_workT (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) (hi : i < Shadow7.wpP (start j) + 15) :
    workT j (Shadow7.bankW (start j) i) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have b := Shadow7.bank_cases w1 w2 hi
  unfold workT; unfold Wire at *; omega

theorem middle_targets (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    AllAT (fun _ => True) (workT j) (middleOps (start j)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have big : ∀ t : Nat, 1559 ≤ t → t ≤ Shadow7.e0P (start j) + 2 → workT j t := fun t h h' => Or.inr (Or.inr ⟨h, Or.inl h'⟩)
  unfold middleOps
  refine allAT_append (allAT_append (allAT_append ?_ ?_) ?_) ?_
  · unfold Shadow7.leaveAdjust
    refine allAT_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) trivial trivial
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
      exact ⟨trivial, bank_workT j h0 (by omega) i (by omega)⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have p := Shadow7.pool_cases (i := i) w1 w2
      exact ⟨trivial, by unfold workT; unfold Wire at *; omega⟩
  · unfold Shadow7.leaveBarrel
    have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ Shadow7.wpP (start j) + 15 →
        AllAT (fun _ => True) (workT j) (stageG 1613 (Shadow7.bankW (start j)) xs d n) :=
      fun xs d n hn => allAT_stageG _ _ _ _ _ ⟨trivial, big _ (by omega) (by omega)⟩ (fun _ _ => trivial)
        (fun i hi => ⟨⟨trivial, bank_workT j h0 (by omega) i (by omega)⟩, ⟨trivial, bank_workT j h0 (by omega) (i+d) (by omega)⟩⟩)
    exact allAT_append (allAT_append (allAT_append (st _ _ _ (by omega)) (st _ _ _ (by omega))) (st _ _ _ (by omega)))
      (st _ _ _ (by omega))
  · exact allAT_cons ⟨fun _ _ => trivial, big 1613 (by decide) (by omega)⟩
      (allAT_cons ⟨fun _ _ => trivial, big 1613 (by decide) (by omega)⟩ allAT_nil)
  · unfold Shadow7.leaveJoin
    refine allAT_append (allAT_digitsG _ _ _ _ trivial trivial _ _ (fun i _ hi => ⟨trivial, ?_, ?_⟩))
      (allAT_wordG _ ⟨trivial, big _ (by decide) (by omega)⟩ _ (fun c hc => ?_))
    · dsimp only; unfold workT; omega
    · dsimp only; unfold workT; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      exact ⟨fun _ _ => trivial, ⟨trivial, by dsimp only; unfold workT; omega⟩, ⟨trivial, bank_workT j h0 (by omega) i (by omega)⟩⟩

/-- The fixed tail of the work part writes only scratch below the anchored block (one decide, fixed segments). -/
theorem tail_dest : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 →
    (leaveFix10 (start j) (Shadow7.sbP (start j)) ++ (leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++
      Shadow7.lowSign (start j))).all (fun g => decide (1559 ≤ target g) && decide (target g ≤ Shadow7.e0P (start j) + 2)) = true := by
  decide +kernel

theorem work_dest (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ∀ q ∈ (GateMirror.forward (workOps (start j))).map LeaveReadoutFrame.destination, workT j q := by
  intro q hq
  rw [dest_forward] at hq
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hq
  have t1 := tail_dest j h0 (by omega)
  rw [List.all_eq_true] at t1
  have cv (g : Gate) (h : (decide (1559 ≤ target g) && decide (target g ≤ Shadow7.e0P (start j) + 2)) = true) : workT j (target g) := by
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h; exact Or.inr (Or.inr ⟨h.1, Or.inl h.2⟩)
  unfold workOps at hg
  rcases List.mem_append.mp hg with hg|hg
  · rcases List.mem_append.mp hg with hg|hg
    · exact (middle_targets j h0 (by omega) g hg).2
    · exact cv g (t1 g (List.mem_append_left _ hg))
  · exact cv g (t1 g (List.mem_append_right _ hg))

theorem body_dest (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ∀ q ∈ (GateMirror.forward (bodyOps j)).map LeaveReadoutFrame.destination, midT j q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  intro q hq
  unfold bodyOps at hq
  rw [forward_app, List.map_append, List.mem_append] at hq
  rcases hq with hq|hq
  · rcases prefix_dest j h0 (by omega) q hq with h|h|h
    · exact Or.inl (Or.inr (Or.inr ⟨h.1, Or.inl (by unfold Wire at *; omega)⟩))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (work_dest j h0 (by omega) q hq)

/-- dadon's `Leave{s}RoutedRestore.result`. -/
theorem routedRestore_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (z : SkywalkNat.State) (sg : Bool)
    (s : State) (m m' : List Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (mag0 : regValue (fullM j) s.basis = 0)
    (flags : let a := step^[15] (reduced (Shadow7.sbP (start j)) 15 z)
      let e := (PortalValues.negative sg a.u).toNat
      s.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ a.u - e) ∧
        (s.basis 1558).toNat = LeaveCompanion.upperBorrow (2^(Shadow7.sbP (start j))) a.u a.v e)
    (liveBits : ∀ i < Shadow7.wpP (start j) + 15, (run (GateMirror.forward (bodyOps j)) m s).basis (live j i) = (TrueMiddle.F j z).testBit i)
    (retired : ∀ i : Fin 39, (run (GateMirror.forward (bodyOps j)) m s).basis (1559 + i.val) = false) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let u := run (GateMirror.forward (bodyOps j)) m s
    let v := run (Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558) m' u
    v.phase = u.phase ∧ (∀ q, q ∉ smallM j → v.basis q = u.basis q) ∧
      regValue (smallM j) v.basis = (mag/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j)) ∧
      v.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ mag) ∧
      (∀ i < Shadow7.wpP (start j) + 15, v.basis (live j i) = (TrueMiddle.F j z).testBit i) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  generalize hu : run (GateMirror.forward (bodyOps j)) m s = u at liveBits retired
  have keep (q : Wire) (h : (q : Nat) = 1556 ∨ (q : Nat) = 1558 ∨ (Shadow7.b0P (start j) ≤ q ∧ (q : Nat) < Shadow7.b0P (start j) + 18)) :
      u.basis q = s.basis q := by
    rw [← hu]
    exact LeaveReadoutFrame.preserved _ _ _ q (fun hm => by have := body_dest j h0 (by omega) q hm; unfold midT workT at this; unfold Wire at *; omega)
  have clear : ∀ q ∈ smallC j, u.basis q = false := by
    intro q h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h; rw [List.mem_range] at hi
    exact retired ⟨i, by omega⟩
  have mag : regValue (smallM j) u.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h; rw [List.mem_range] at hi
    refine (keep _ (Or.inr (Or.inr ⟨by show Shadow7.b0P (start j) ≤ Shadow7.b0P (start j) + i; omega,
      by show Shadow7.b0P (start j) + i < Shadow7.b0P (start j) + 18; omega⟩))).trans ((regValue_zero _ _).mp mag0 _ ?_)
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
  have reg := outputSmall j h0 (by omega) u (TrueMiddle.F j z) liveBits
  have old := (keep 1556 (Or.inl rfl)).trans flags.1
  have new := restored_result j h0 (by omega) z sg u m' small clear mag
    ⟨old, (congrArg Bool.toNat (keep 1558 (Or.inr (Or.inl rfl)))).trans flags.2, reg⟩
  have ch := LeaveRestoreTruth.truth_shadow7 (Shadow7.sbP (start j)) z small.1 sg
  refine ⟨new.1, new.2.1, new.2.2, ?_, ?_⟩
  · rw [new.2.1 _ (fun h => by obtain ⟨i, hi, e⟩ := List.mem_map.mp h; rw [List.mem_range] at hi; unfold Wire at *; omega),
      old, ch.1, ch.2.2.2]
  · intro i hi
    have outside : live j i ∉ smallM j := by
      intro h; obtain ⟨k, hk, e⟩ := List.mem_map.mp h; rw [List.mem_range] at hk
      have b := Shadow7.bank_cases w1 w2 hi
      unfold live at e; split at e <;> unfold Wire at * <;> omega
    exact (new.2.1 _ outside).trans (liveBits i hi)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Relocated
open Partial LeaveRelocation
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem flip_ne {a b q : Wire} (ha : q ≠ a) (hb : q ≠ b) : LeaveRelocation.flip a b q = q := by
  unfold LeaveRelocation.flip; rw [if_neg ha, if_neg hb]
theorem flip_fst (a b : Wire) : LeaveRelocation.flip a b a = b := by unfold LeaveRelocation.flip; rw [if_pos rfl]
theorem flip_snd {a b : Wire} (h : b ≠ a) : LeaveRelocation.flip a b b = a := by unfold LeaveRelocation.flip; rw [if_neg h, if_pos rfl]

/-- Peel the last pair of a range-indexed relocation. -/
theorem src_succ (p : Nat → Wire × Wire) (k : Nat) (q : Wire) :
    source ((List.range (k+1)).map p) q = source ((List.range k).map p) (LeaveRelocation.flip (p k).1 (p k).2 q) := by
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, LeaveRelocation.append]
  rfl

theorem src_untouched (p : Nat → Wire × Wire) (k : Nat) (q : Wire) (h : ∀ i < k, q ≠ (p i).1 ∧ q ≠ (p i).2) :
    source ((List.range k).map p) q = q := by
  apply LeaveRelocation.outside
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i (List.mem_range.mp hi)

theorem src_above (p : Nat → Wire × Wire) (k : Nat) (q : Wire) : ∀ n : Nat, k ≤ n →
    (∀ i, k ≤ i → i < n → q ≠ (p i).1 ∧ q ≠ (p i).2) →
    source ((List.range n).map p) q = source ((List.range k).map p) q := by
  intro n
  induction n with
  | zero => intro hk _; rw [Nat.le_zero.mp hk]
  | succ n ih =>
    intro hk h
    by_cases e : k = n + 1
    · rw [e]
    · rw [src_succ, flip_ne (h n (by omega) (by omega)).1 (h n (by omega) (by omega)).2]
      exact ih (by omega) (fun i a b => h i a (by omega))

/-- The bank pairs of `Shadow7.movesP s`. -/
def bankPair (s i : Nat) : Wire × Wire := (Shadow7.bankW s (Shadow7.lowsP s + i), bTopP (s+15) + 4 + i - Shadow7.wpP (s+15))
/-- The six flag pairs of `Shadow7.movesP s`. -/
def flagPairs (s : Nat) : List (Wire × Wire) :=
  [(1557, Shadow7.e0P (s+15) + 3), (1558, Shadow7.e0P (s+15) + 4), (Shadow7.e0P s + 5, Shadow7.e0P (s+15) + 5),
   (Shadow7.e0P s + 3, Shadow7.e0P (s+15) + 6), (Shadow7.e0P s + 7, Shadow7.e0P (s+15) + 7), (Shadow7.e0P s + 6, Shadow7.e0P (s+15) + 8)]

theorem moves_split (s : Nat) :
    Shadow7.movesP s = (List.range (Shadow7.wpP (s+15) - 3)).map (bankPair s) ++ flagPairs s := rfl

/-- Closed forms of the chain (all block facts the proofs below use); `D0 = 805 + Shadow7.sbP (s+15)`,
`n = Shadow7.wpP (s+15) - 3`, `m = Shadow7.wpP s - Shadow7.lowsP s` (the B-branch count). -/
theorem chain_geo {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 375) :
    (∀ i, (bankPair s i).2 = 805 + Shadow7.sbP (s+15) + i) ∧
    (∀ i, i < Shadow7.wpP s - Shadow7.lowsP s → (bankPair s i).1 = 805 + Shadow7.sbP (s+15) + 15 + i) ∧
    (∀ i, Shadow7.wpP s - Shadow7.lowsP s ≤ i → (bankPair s i).1 = 1598 + i - (Shadow7.wpP s - Shadow7.lowsP s)) ∧
    Shadow7.wpP s - Shadow7.lowsP s ≤ Shadow7.wpP (s+15) - 3 ∧ Shadow7.wpP (s+15) - 3 ≤ Shadow7.wpP s - Shadow7.lowsP s + 15 ∧ 15 ≤ Shadow7.wpP (s+15) - 3 ∧
    805 + Shadow7.sbP (s+15) + 14 + (Shadow7.wpP s - Shadow7.lowsP s) = bTopP s ∧ 805 + Shadow7.sbP (s+15) + (Shadow7.wpP (s+15) - 3) = bTopP (s+15) + 1 ∧
    bTopP s ≤ 1043 ∧ bTopP (s+15) ≤ bTopP s ∧ 1613 + 15 ≤ Shadow7.e0P (s+15) ∧ Shadow7.e0P (s+15) + 7 ≤ Shadow7.e0P s ∧
    Shadow7.e0P s ≤ Shadow7.e0P (s+15) + 8 ∧ 805 + Shadow7.sbP (s+15) = Shadow7.b0P s + Shadow7.lowsP s ∧ 10 ≤ Shadow7.lowsP s ∧ Shadow7.lowsP s ≤ 11 ∧
    Shadow7.lowsP s + 3 ≤ Shadow7.wpP s ∧ 805 + Shadow7.sbP (s+15) ≥ 805 + 54 := by
  have r := Shadow7.rail_win h1 (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have hR : railP s ≤ railP (s+15) + 15 := by unfold railP; split_ifs <;> omega
  have hsb : 54 ≤ Shadow7.sbP (s+15) := by unfold Shadow7.sbP; omega
  refine ⟨fun i => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold bankPair; dsimp only; ((try unfold Wire at *); omega)
  · unfold bankPair Shadow7.bankW; dsimp only
    rw [if_neg (by omega), if_pos (by omega)]; ((try unfold Wire at *); omega)
  · unfold bankPair Shadow7.bankW; dsimp only
    rw [if_neg (by omega), if_neg (by omega)]; ((try unfold Wire at *); omega)
  all_goals ((try unfold Wire at *); omega)

/-- dadon's `upperMap` direction: the next tick's B word `D0 + i` takes the bank wire `a i`. -/
theorem src_d (s : Nat) (h1 : 90 ≤ s) (h2 : s ≤ 375) (i : Nat) (hi : i < Shadow7.wpP (s+15) - 3) :
    source (Shadow7.movesP s) (805 + Shadow7.sbP (s+15) + i) = Shadow7.bankW s (Shadow7.lowsP s + i) := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  rw [moves_split, LeaveRelocation.append]
  rw [LeaveRelocation.outside (flagPairs s) (805 + Shadow7.sbP (s+15) + i) (by
    intro p hp
    simp only [flagPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> constructor <;> ((try unfold Wire at *); omega))]
  have ab (k : Nat) :
      ((bankPair s k).1 = 805 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  rw [src_above (bankPair s) (i+1) (805 + Shadow7.sbP (s+15) + i) (Shadow7.wpP (s+15) - 3) (by omega) (by
    intro k a b
    rw [hd k]
    rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rw [e] <;> constructor <;> ((try unfold Wire at *); omega))]
  rw [src_succ, hd i, flip_snd (a := (bankPair s i).1) (b := 805 + Shadow7.sbP (s+15) + i) (by rcases ab i with ⟨e, ei⟩ | ⟨e, ei⟩ <;> rw [e] <;> ((try unfold Wire at *); omega))]
  rw [src_untouched (bankPair s) i (bankPair s i).1 (by
    intro k hk
    rw [hd k]
    rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rcases ab i with ⟨e', ei⟩ | ⟨e', ei⟩ <;> rw [e, e'] <;>
      constructor <;> ((try unfold Wire at *); omega))]
  rfl

/-- The chain down: before pair `i`, the wire `D0 + i` reads `D0 + i % 15`. -/
theorem src_chain (s : Nat) (h1 : 90 ≤ s) (h2 : s ≤ 375) :
    ∀ i, i < Shadow7.wpP (s+15) - 3 →
      source ((List.range i).map (bankPair s)) (805 + Shadow7.sbP (s+15) + i) = 805 + Shadow7.sbP (s+15) + i % 15 := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  have ab (k : Nat) :
      ((bankPair s k).1 = 805 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases small : i < 15
    · rw [src_untouched (bankPair s) i (805 + Shadow7.sbP (s+15) + i) (by
        intro k hk
        rw [hd k]
        rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rw [e] <;> constructor <;> ((try unfold Wire at *); omega))]
      rw [Nat.mod_eq_of_lt small]
    · have kB : i - 15 < Shadow7.wpP s - Shadow7.lowsP s := by omega
      rw [src_above (bankPair s) (i - 15 + 1) (805 + Shadow7.sbP (s+15) + i) i (by omega) (by
        intro k a b
        rw [hd k]
        rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rw [e] <;> constructor <;> ((try unfold Wire at *); omega))]
      rw [src_succ, show 805 + Shadow7.sbP (s+15) + i = (bankPair s (i - 15)).1 by rw [hB _ kB]; omega, flip_fst,
        hd (i - 15), ih (i - 15) (by omega) (by omega)]
      congr 1
      omega

/-- The freed B top and the pool: a bank wire that is no next-tick word reads `D0 + i % 15`. -/
theorem src_top (s : Nat) (h1 : 90 ≤ s) (h2 : s ≤ 375) (i : Nat) (hi : i < Shadow7.wpP (s+15) - 3)
    (top : Shadow7.lowsP s + i < Shadow7.wpP s → Shadow7.wpP (s+15) - 3 ≤ i + 15) :
    source (Shadow7.movesP s) (Shadow7.bankW s (Shadow7.lowsP s + i)) = 805 + Shadow7.sbP (s+15) + i % 15 := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  have ab (k : Nat) :
      ((bankPair s k).1 = 805 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  have top' : Shadow7.wpP (s+15) - 3 ≤ i + 15 ∨ Shadow7.wpP s - Shadow7.lowsP s ≤ i := by
    by_cases b : Shadow7.lowsP s + i < Shadow7.wpP s
    · exact Or.inl (top b)
    · exact Or.inr (by omega)
  have ai : Shadow7.bankW s (Shadow7.lowsP s + i) = (bankPair s i).1 := rfl
  rw [moves_split, LeaveRelocation.append, ai]
  rw [LeaveRelocation.outside (flagPairs s) (bankPair s i).1 (by
    intro p hp
    simp only [flagPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases ab i with ⟨e, ei⟩ | ⟨e, ei⟩ <;> rw [e] <;>
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> constructor <;> ((try unfold Wire at *); omega))]
  rw [src_above (bankPair s) (i+1) (bankPair s i).1 (Shadow7.wpP (s+15) - 3) (by omega) (by
    intro k a b
    rw [hd k]
    rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rcases ab i with ⟨e', ei⟩ | ⟨e', ei⟩ <;> rw [e, e'] <;>
      constructor <;> ((try unfold Wire at *); omega))]
  rw [src_succ, flip_fst, hd i]
  exact src_chain s h1 h2 i hi

/-- The six flag pairs. -/
theorem src_flags (s : Nat) (h1 : 90 ≤ s) (h2 : s ≤ 375) :
    source (Shadow7.movesP s) 1557 = Shadow7.e0P (s+15) + 3 ∧ source (Shadow7.movesP s) 1558 = Shadow7.e0P (s+15) + 4 ∧
    source (Shadow7.movesP s) (Shadow7.e0P s + 5) = Shadow7.e0P (s+15) + 5 ∧ source (Shadow7.movesP s) (Shadow7.e0P s + 3) = Shadow7.e0P (s+15) + 6 ∧
    source (Shadow7.movesP s) (Shadow7.e0P s + 7) = Shadow7.e0P (s+15) + 7 ∧ source (Shadow7.movesP s) (Shadow7.e0P s + 6) = Shadow7.e0P (s+15) + 8 := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  have ab (k : Nat) :
      ((bankPair s k).1 = 805 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  have bankOut (x : Wire) (hx : Shadow7.e0P (s+15) ≤ x) :
      source ((List.range (Shadow7.wpP (s+15) - 3)).map (bankPair s)) x = x := by
    apply src_untouched
    intro k hk
    rw [hd k]
    rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rw [e] <;> constructor <;> ((try unfold Wire at *); omega)
  have fl : ∀ x, source (flagPairs s) x = LeaveRelocation.flip 1557 (Shadow7.e0P (s+15) + 3) (LeaveRelocation.flip 1558 (Shadow7.e0P (s+15) + 4)
      (LeaveRelocation.flip (Shadow7.e0P s + 5) (Shadow7.e0P (s+15) + 5) (LeaveRelocation.flip (Shadow7.e0P s + 3) (Shadow7.e0P (s+15) + 6) (LeaveRelocation.flip (Shadow7.e0P s + 7) (Shadow7.e0P (s+15) + 7)
      (LeaveRelocation.flip (Shadow7.e0P s + 6) (Shadow7.e0P (s+15) + 8) x))))) := fun x => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [moves_split, LeaveRelocation.append, fl]
    simp (disch := ((try unfold Wire at *); omega)) only [flip_ne, flip_fst, flip_snd]
    exact bankOut _ (by omega)

/-- Wires the relocation does not touch. -/
theorem src_out (s : Nat) (h1 : 90 ≤ s) (h2 : s ≤ 375) (q : Wire)
    (bank : q < 805 + Shadow7.sbP (s+15) ∨ (bTopP s < q ∧ q < 1598) ∨ 1598 + (Shadow7.wpP (s+15) - 3) - (Shadow7.wpP s - Shadow7.lowsP s) ≤ q)
    (flags : q ≠ 1557 ∧ q ≠ 1558 ∧ q ≠ Shadow7.e0P s + 3 ∧ q ≠ Shadow7.e0P s + 5 ∧ q ≠ Shadow7.e0P s + 6 ∧ q ≠ Shadow7.e0P s + 7 ∧
      (q < Shadow7.e0P (s+15) + 3 ∨ Shadow7.e0P (s+15) + 8 < q)) :
    source (Shadow7.movesP s) q = q := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  apply LeaveRelocation.outside
  intro p hp
  rw [moves_split, List.mem_append] at hp
  rcases hp with hp | hp
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    rw [List.mem_range] at hk
    rw [hd k]
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · rw [hB k b]; constructor <;> ((try unfold Wire at *); omega)
    · rw [hP k (by omega)]; constructor <;> ((try unfold Wire at *); omega)
  · simp only [flagPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> constructor <;> ((try unfold Wire at *); omega)

/-- dadon's `Leave{s}Relocated.upperMap`, for every window block (for par-c1). -/
theorem upperMapB (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ∀ i : Nat, i < railP (start j + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1) →
      LeaveRelocation.source (Shadow7.movesP (start j)) (Shadow7.b0P (start j) + Shadow7.lowsP (start j) + i) =
        Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) ∧
      LeaveRelocation.source (Shadow7.movesP (start j)) (Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i) =
        Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo w1 w3
  have r := Shadow7.rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  intro i hi
  refine ⟨?_, ?_⟩
  · rw [show Shadow7.b0P (start j) + Shadow7.lowsP (start j) + i = 805 + Shadow7.sbP (start j + 15) + i by omega]
    exact src_d _ w1 w3 i (by omega)
  · -- A addresses are 344..528: below the B chain (805+sb(s+15) ≥ 859) and below every flag (≥ 1557).
    -- Bare `omega` misses this: `Shadow7.lowsP` is a Nat subtraction, so the A wire is not linear until it is cancelled.
    have hsub : Shadow7.sbP (start j) ≤ 18 + Shadow7.sbP (start j + 15) := by omega
    have hid : Shadow7.sbP (start j) + Shadow7.lowsP (start j) = 18 + Shadow7.sbP (start j + 15) := by
      unfold Shadow7.lowsP
      have hc := Nat.sub_add_cancel hsub
      omega
    have qform : Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i =
        start j + (Shadow7.sbP (start j) + Shadow7.lowsP (start j)) + 32 + i := by
      rw [ea]; omega
    have hfit : Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1 ≤ railP (start j + 15) := by
      rw [hid]; omega
    have qlt : Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i < start j + railP (start j + 15) + 31 := by
      rw [qform, hid]; omega
    have hq : Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i < 1557 := by
      have hr : railP (start j + 15) ≤ 258 := by omega
      omega
    have hbank : Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i < 805 + Shadow7.sbP (start j + 15) := by
      have hsb15 : 53 ≤ Shadow7.sbP (start j + 15) := by omega
      omega
    -- `Shadow7.e0P (s+15) = 1574 + sb(s+15)`, so it sits above 1577. `rw [ee']` left this opaque to omega.
    have hflag : (1557 : Nat) < Shadow7.e0P (start j + 15) + 3 := by
      unfold Shadow7.e0P
      calc (1557 : Nat) < 1577 := by decide
           _ ≤ 1574 + Shadow7.sbP (start j + 15) + 3 := by omega
    exact src_out _ w1 w3 _ (Or.inl hbank)
      ⟨Nat.ne_of_lt hq,
       Nat.ne_of_lt (lt_trans hq (by omega : (1557 : Nat) < 1558)),
       Nat.ne_of_lt (lt_trans hq (by rw [ee]; omega)),
       Nat.ne_of_lt (lt_trans hq (by rw [ee]; omega)),
       Nat.ne_of_lt (lt_trans hq (by rw [ee]; omega)),
       Nat.ne_of_lt (lt_trans hq (by rw [ee]; omega)),
       Or.inl (lt_trans hq hflag)⟩

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Relocated

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.WideWords
open Arithmetic MappedCompressed PortalValues LeaveSignedCoordinates Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- dadon's `Leave{s}WideWords.L`: the stock layout of tick s+15. -/
abbrev L (j : Fin 23) := W.compactSkywalkTickLayout MappedCompressed.base (start j + 15)
/-- dadon's `Leave{s}WideWords.shortL`: the block's last packet port. -/
abbrev shortL (j : Fin 23) := IntegerPacket.ports (Shadow7.shape j) 15

/-- The stock rail width at tick s+15 is par-b's `railP (s+15)` (257 at 225). -/
theorem width (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    W.compactSkywalkTickPreWidth (start j + 15) = railP (start j + 15) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  unfold W.compactSkywalkTickPreWidth W.narrowSkywalkRouteWidth railP
  split_ifs <;> omega

theorem wideMapping (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) (hi : i < railP (start j + 15)) :
    (L j).a.getD i 0 = OB5.sig (start j + 14) (start j + 31 + i) ∧
    (L j).b.getD i 0 = OB5.sig (start j + 14) (786 + i) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have hw := width j h0 (by omega)
  have r : railP (start j + 15) ≤ 258 := by unfold railP; split_ifs <;> omega
  have hi' : i < W.compactSkywalkTickPreWidth (start j + 15) := by omega
  rw [W.compactSkywalkTick_a MappedCompressed.base (start j + 15) (by omega),
    W.compactSkywalkTick_b MappedCompressed.base (start j + 15) (by omega),
    W.wireBlock_getD MappedCompressed.base (start j + 15) _ i hi', W.wireBlock_getD MappedCompressed.base 770 _ i hi']
  unfold OB5.sig MappedCompressed.base
  constructor
  · rw [if_neg (by ((try unfold Wire at *); omega))]; ((try unfold Wire at *); omega)
  · rw [if_neg (by ((try unfold Wire at *); omega))]; ((try unfold Wire at *); omega)

theorem shortMapping (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) (hi : i < Shadow7.sbP (start j)) :
    windowNet j ((shortL j).a.getD i 0) = start j + 31 + i ∧
    windowNet j ((shortL j).b.getD i 0) = 786 + i := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have hm : i < Shadow7.smallBits j + 17 + 1 := by unfold Shadow7.smallBits Shadow7.sbP; unfold Shadow7.sbP at hi; omega
  have ga : (shortL j).a.getD i 0 = start j + 31 + i := by
    show ((start j + 15 + 16) :: (List.range' (start j + 15 + 16 + 1) (Shadow7.smallBits j + 17) ++
      [start j + 15 + 16 + (Shadow7.smallBits j + 17 + 1)])).getD i 0 = _
    rcases i with _ | i
    · simp only [List.getD_cons_zero]
    · have hlen : i < (List.range' (start j + 15 + 16 + 1) (Shadow7.smallBits j + 17)).length := by
        rw [List.length_range']; omega
      rw [List.getD_cons_succ, List.getD_append _ _ _ _ hlen, List.getD_eq_getElem?_getD,
        List.getElem?_range' (by omega : i < Shadow7.smallBits j + 17), Option.getD_some]
      omega
  have gb : (shortL j).b.getD i 0 = 786 + i := by
    show (786 :: (List.range' 787 (Shadow7.smallBits j + 17) ++ [786 + (Shadow7.smallBits j + 17 + 1)])).getD i 0 = _
    rcases i with _ | i
    · simp only [List.getD_cons_zero]
    · have hlen : i < (List.range' 787 (Shadow7.smallBits j + 17)).length := by
        rw [List.length_range']; omega
      rw [List.getD_cons_succ, List.getD_append _ _ _ _ hlen, List.getD_eq_getElem?_getD,
        List.getElem?_range' (by omega : i < Shadow7.smallBits j + 17), Option.getD_some]
      omega
  rw [ga, gb]
  unfold windowNet net OB5.sig
  constructor
  · rw [if_neg (by unfold Shadow7.sbP at hi; ((try unfold Wire at *); omega))]
  · rw [if_neg (by unfold Shadow7.sbP at hi; ((try unfold Wire at *); omega))]

/-- dadon's `Leave{s}WideWords.wide`, for every index of the next tick's rails. -/
theorem wide (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (a : SkywalkNat.State) (G sg : Bool) (raw : State)
    (input : SkywalkIntegerInput (L j) (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G
      raw.basis)
    (i : Fin (railP (start j + 15))) :
    let o := pullState (OB5.sig (start j + 14)) raw
    let e := negative sg a.u
    let pos := (a.u+a.v).testBit i.val
    let neg := (a.u-e.toNat).testBit i.val ^^ e
    o.basis (start j + 31 + i.val) = (if G then neg else pos) ∧ o.basis (786 + i.val) = (if G then pos else neg) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have hw := width j h0 (by omega)
  have maxA : railP (start j + 15) ≤ (L j).a.length := by
    rw [W.compactSkywalkTick_a MappedCompressed.base (start j + 15) (by omega), wireBlock_length]; omega
  have maxB : railP (start j + 15) ≤ (L j).b.length := by
    rw [W.compactSkywalkTick_b MappedCompressed.base (start j + 15) (by omega), wireBlock_length]; omega
  have h := LeaveSignedCoordinates.pair (L j) G sg a.u a.v i.val raw.basis input.1 input.2.1 input.2.2.1
    (Nat.lt_of_lt_of_le i.isLt maxA) (Nat.lt_of_lt_of_le i.isLt maxB)
  rw [(wideMapping j h0 (by omega) i.val i.isLt).1, (wideMapping j h0 (by omega) i.val i.isLt).2] at h
  exact h

/-- dadon's `Leave{s}WideWords.short`: the block's own rails read the same signed coordinates. -/
theorem short (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (a : SkywalkNat.State) (G sg : Bool) (s : State)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg a.u a.v) s.basis) (i : Fin (Shadow7.sbP (start j))) :
    let e := negative sg a.u
    let pos := (a.u+a.v).testBit i.val
    let neg := (a.u-e.toNat).testBit i.val ^^ e
    s.basis (start j + 31 + i.val) = (if G then neg else pos) ∧ s.basis (786 + i.val) = (if G then pos else neg) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have maxA : Shadow7.sbP (start j) ≤ (shortL j).a.length := by
    show Shadow7.sbP (start j) ≤ ((start j + 15 + 16) :: (List.range' (start j + 15 + 16 + 1) (Shadow7.smallBits j + 17) ++
      [start j + 15 + 16 + (Shadow7.smallBits j + 17 + 1)])).length
    simp only [List.length_cons, List.length_append, List.length_range', List.length_singleton]
    unfold Shadow7.smallBits Shadow7.sbP; omega
  have maxB : Shadow7.sbP (start j) ≤ (shortL j).b.length := by
    show Shadow7.sbP (start j) ≤ (786 :: (List.range' 787 (Shadow7.smallBits j + 17) ++ [786 + (Shadow7.smallBits j + 17 + 1)])).length
    simp only [List.length_cons, List.length_append, List.length_range', List.length_singleton]
    unfold Shadow7.smallBits Shadow7.sbP; omega
  have prev : mappedBasis j s.basis (shortL j).previous = G := by cases G <;> exact ready.2.2.1
  have h := LeaveSignedCoordinates.pair (shortL j) G sg a.u a.v i.val (mappedBasis j s.basis) ready.1 ready.2.1 prev
    (Nat.lt_of_lt_of_le i.isLt maxA) (Nat.lt_of_lt_of_le i.isLt maxB)
  unfold mappedBasis at h
  dsimp only at h
  rw [(shortMapping j h0 (by omega) i.val i.isLt).1, (shortMapping j h0 (by omega) i.val i.isLt).2] at h
  exact h

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.WideWords

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial SkywalkNat
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The true walk's sum from the first tick on: `u+v ≤ 2^256+2^255` (dadon's `after_first`). -/
theorem sum_early (x p t : Nat) (hx : x < 2^256) (hp : p < 2^256) (ht : 1 ≤ t) :
    (step^[t] (init x p)).u + (step^[t] (init x p)).v ≤ 2^256 + 2^255 := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have h : (step^[k+1] (init x p)).u + (step^[k+1] (init x p)).v ≤ 2^256 + 2^256/2 :=
    LeaveBankEnvelope.after_first x p (2^256) hx.le hp.le k
  have e : (2:Nat)^256/2 = 2^255 := by norm_num
  rw [e] at h
  exact h

set_option exponentiation.threshold 600 in
/-- The true walk's sum at tick `t` for coprime inputs: `u+v ≤ 2^(512-t)` (product bound). -/
theorem sum_late (x p t : Nat) (good : WideReference.Bounds x p) (ht : t ≤ 512) :
    (step^[t] (init x p)).u + (step^[t] (init x p)).v ≤ 2^(512-t) := by
  have hb := iter_product_bound t (init x p)
  have hv := iter_valid t (init x p) good.positive good.odd
  generalize hz : step^[t] (init x p) = z at hb hv ⊢
  have hxp : x * p < 2^512 := by
    calc x * p ≤ x * 2^256 := Nat.mul_le_mul_left _ (Nat.le_of_lt good.cap)
         _ < 2^256 * 2^256 := Nat.mul_lt_mul_of_pos_right (lt_trans good.small good.cap) (by positivity)
         _ = 2^512 := (pow_add (2 : Nat) 256 256).symm
  change 2^t*(z.u*z.v) ≤ x*p at hb
  by_cases hu : z.u = 0
  · have g := hv.2.2
    rw [hu, Nat.gcd_zero_left] at g
    have one : z.v = 1 := g.trans good.coprime
    rw [hu, one]
    have := Nat.one_le_two_pow (n := 512 - t)
    omega
  · have split : (2 : Nat)^512 = 2^t * 2^(512 - t) := by rw [← pow_add, Nat.add_sub_cancel' ht]
    have h2 : 2^t * (z.u * z.v) < 2^t * 2^(512 - t) := by rw [← split]; exact lt_of_le_of_lt hb hxp
    have hprod : z.u * z.v < 2^(512-t) := Nat.lt_of_mul_lt_mul_left h2
    have hu1 : 1 ≤ z.u := Nat.pos_of_ne_zero hu
    have hv1 : 1 ≤ z.v := hv.1
    have hsum : z.u + z.v ≤ z.u * z.v + 1 := by nlinarith
    omega

set_option exponentiation.threshold 600 in
/-- The two envelopes give the bank room and the output bound (`W` = bank width, `e` = limb exponent). -/
theorem env_room {S e W : Nat}
    (case : (257 ≤ W + e ∧ e ≤ 254 ∧ S ≤ 2^256 + 2^255) ∨ (2 ≤ W ∧ S ≤ 2^(W - 1 + e))) :
    S / 2^e + 1 < 2^W ∧ S < 2^(W + e) := by
  rcases case with ⟨hR, he, hS⟩ | ⟨hW, hS⟩
  · have hk : (255 - e) + e = 255 := by omega
    have h255 : (2:Nat)^255 = 2^(255 - e) * 2^e := by rw [← pow_add, hk]
    have h3 : (2:Nat)^256 + 2^255 = 2^e * (3 * 2^(255 - e)) := by
      rw [show (2:Nat)^256 = 2 * 2^255 by norm_num, h255]; ring
    have hdiv : S / 2^e ≤ 3 * 2^(255 - e) := Nat.div_le_of_le_mul (by rw [← h3]; exact hS)
    have h4 : 4 * 2^(255 - e) ≤ 2^W := by
      calc 4 * 2^(255 - e) = 2^(255 - e + 2) := by rw [pow_add]; ring
        _ ≤ 2^W := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h6 : 2 ≤ 2^(255 - e) := by
      calc 2 = 2^1 := by norm_num
        _ ≤ 2^(255 - e) := Nat.pow_le_pow_right (by norm_num) (by omega)
    clear h3 h255
    refine ⟨?_, ?_⟩
    · generalize S / 2^e = D at *
      generalize 2^(255 - e) = X at *
      generalize 2^W = Y at *
      omega
    · calc S ≤ 2^256 + 2^255 := hS
        _ < 2^257 := by norm_num
        _ ≤ 2^(W + e) := Nat.pow_le_pow_right (by norm_num) hR
  · have hdiv : S / 2^e ≤ 2^(W - 1) :=
      Nat.div_le_of_le_mul (by rw [← pow_add, show e + (W - 1) = W - 1 + e by omega]; exact hS)
    have hpow : (2:Nat)^W = 2 * 2^(W - 1) := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ W)]
    have h6 : 2 ≤ 2^(W - 1) := by
      calc 2 = 2^1 := by norm_num
        _ ≤ 2^(W - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨?_, ?_⟩
    · rw [hpow]
      generalize S / 2^e = D at *
      generalize 2^(W - 1) = X at *
      omega
    · calc S ≤ 2^(W - 1 + e) := hS
        _ < 2^(W + e) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- Block geometry used by the envelope (closed forms of par-b's `railP`/`Shadow7.sbP`/`Shadow7.wpP`). -/
theorem env_geo {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 375) :
    Shadow7.wpP s + (Shadow7.sbP s + 15 + 1) = railP s ∧ (s < 257 → 257 ≤ railP s) ∧ (257 ≤ s → railP s = 513 - s) ∧
      Shadow7.sbP s ≤ 204 ∧ 2 ≤ Shadow7.wpP s := by
  unfold Shadow7.wpP railP Shadow7.sbP
  refine ⟨?_, fun h => ?_, fun h => ?_, ?_, ?_⟩ <;> (try split_ifs) <;> omega

set_option exponentiation.threshold 600 in
/-- dadon's `LeaveTerminalBound.fit` (255) / `fit210`: the leave's output word fits the next tick's rail,
`F < 2^(R(s+15) - sb - 1)` (255: 2^113, 210: 2^105, 225: 2^112 = the bank width). -/
theorem terminal_fit (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (x p : Nat) (good : WideReference.Bounds x p) :
    TrueMiddle.F j (step^[start j] (init x p)) < 2^(railP (start j + 15) - (Shadow7.sbP (start j) + 1)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have hx : x < 2^256 := lt_trans good.small good.cap
  have it : step^[15] (step^[start j] (init x p)) = step^[start j + 15] (init x p) := by
    rw [← Function.iterate_add_apply, Nat.add_comm]
  have fits : Shadow7.sbP (start j) + 1 ≤ railP (start j + 15) := by unfold railP Shadow7.sbP; split_ifs <;> omega
  have env : (step^[start j + 15] (init x p)).u + (step^[start j + 15] (init x p)).v < 2^(railP (start j + 15)) := by
    by_cases hs : start j + 15 < 257
    · calc _ ≤ 2^256 + 2^255 := sum_early x p _ hx good.cap (by omega)
        _ < 2^257 := by norm_num
        _ ≤ 2^(railP (start j + 15)) := Nat.pow_le_pow_right (by norm_num) (by unfold railP; split_ifs <;> omega)
    · calc _ ≤ 2^(512 - (start j + 15)) := sum_late x p _ good (by omega)
        _ < 2^(railP (start j + 15)) := Nat.pow_lt_pow_right (by norm_num) (by unfold railP; split_ifs <;> omega)
  unfold TrueMiddle.F
  rw [it, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel fits]
  exact env

namespace Admission

/-- dadon's `Leave{s}Admission.Numeric` (225: sb 144, Wp 97, next sb 136, W 112). -/
structure Numeric (j : Fin 23) (z : SkywalkNat.State) : Prop where
  farSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z
  odd : z.v % 2 = 1
  room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j))
  endSmall : Shadow7.EndSmall (Shadow7.sbP (start j)) z
  nextFarSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 (SkywalkNat.step^[15] z)
  bound : TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)

/-- dadon's `Leave{s}Admission.actualNumbers`, for every window block. Takes `Bounds` (coprime inputs): from
tick 257 on the room comes from the product bound. -/
theorem actualNumbers (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (x p : Nat) (good : WideReference.Bounds x p) :
    Numeric j (SkywalkNat.step^[start j] (SkywalkNat.init x p)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  obtain ⟨g1, g2, g3, g4, g5⟩ := env_geo w1 w3
  have hx : x < 2^256 := lt_trans good.small good.cap
  have env := env_room (S := (step^[start j] (init x p)).u + (step^[start j] (init x p)).v)
    (e := Shadow7.sbP (start j) + 15 + 1) (W := Shadow7.wpP (start j)) (by
      by_cases hs : start j < 257
      · have := g2 hs
        exact Or.inl ⟨by omega, by omega, sum_early x p _ hx good.cap (by omega)⟩
      · have := g3 (by omega)
        refine Or.inr ⟨by omega, ?_⟩
        rw [show Shadow7.wpP (start j) - 1 + (Shadow7.sbP (start j) + 15 + 1) = 512 - start j by omega]
        exact sum_late x p _ good (by omega))
  have it : step^[15] (step^[start j] (init x p)) = step^[start j + 15] (init x p) := by
    rw [← Function.iterate_add_apply, Nat.add_comm]
  have now := Shadow7.Envelope.inputs x p (start j) hx good.cap (by omega)
  refine ⟨now.1, (iter_valid (start j) (init x p) good.positive good.odd).2.1, env.1, now.2,
    Shadow7.Envelope.nextFarSmall x p (start j) hx good.cap (by omega), ?_⟩
  · unfold TrueMiddle.F
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show Shadow7.wpP (start j) + 15 + (Shadow7.sbP (start j) + 1) = Shadow7.wpP (start j) + (Shadow7.sbP (start j) + 15 + 1) by omega]
    exact lt_of_le_of_lt (iter_sum_nonincrease 15 _) env.2

/-- dadon's `Leave{s}Admission.flags` (block-independent). -/
def flags (z : SkywalkNat.State) (g0 s0 : Bool) : Bool × Bool :=
  SharedSigned.flags g0 s0 (SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v))

end Admission

/-- dadon's `carry{s}`: the native carry `1556 .. e0-1` is clean on the rails. -/
theorem native_carryJ (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (z : SkywalkRails.State) (s : State)
    (ready : Shadow7.onRails j 15 z s.basis) : ∀ q : Wire, 1556 ≤ q → q < Shadow7.e0P (start j) → s.basis q = false := by
  intro q lo hi
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  apply Shadow7.native_carry _ _ _ ready
  refine List.mem_map.mpr ⟨q, ?_, ?_⟩
  · simp only [IntegerPacket.ports, Shadow7.shape, List.mem_range'_1]
    unfold Shadow7.smallBits Shadow7.sbP; unfold Shadow7.e0P Shadow7.sbP at hi; ((try unfold Wire at *); omega)
  · unfold windowNet net OB5.sig
    rw [if_neg]
    unfold Shadow7.e0P Shadow7.sbP at hi
    ((try unfold Wire at *); omega)

/-- dadon's `same_c225/240/255`: the block's placement fixes the scratch below its own moved history. -/
theorem sig_carry (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Nat) (lo : 1556 ≤ q) (hi : q + start j ≤ 2054) :
    OB5.sig (start j + 14) q = q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  unfold OB5.sig; rw [if_neg (by (try simp only [Wire] at *); omega)]

namespace Admission

/-- dadon's `Leave{s}Admission.spare`: the two flags `e0+6, e0+7` and the pool overflow `e0+10 ..` (255: 1709,1710,
1713..1718; empty overflow for s ≤ 240). -/
def spare (j : Fin 23) : List Wire :=
  [Shadow7.e0P (start j) + 6, Shadow7.e0P (start j) + 7] ++
    List.range' (Shadow7.e0P (start j) + 10) (Shadow7.wpP (start j) - 1 - (Shadow7.e0P (start j) - 1598))

/-- dadon's `Leave{s}Admission.Inputs`. The `extra` field (dadon's 255 form) is vacuous when the overflow is empty. -/
structure Inputs (j : Fin 23) (s : State) (z : SkywalkNat.State) (g0 s0 : Bool) : Prop extends Numeric j z where
  ready : Shadow7.onRails j 15 (SkywalkRails.encode (flags z g0 s0).1 (flags z g0 s0).2
    (SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
    (SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis
  fresh : s.basis (Shadow7.e0P (start j) + 5) = false
  scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false
  temp : ∀ p ∈ longPairs j, s.basis p.2 = false
  clean : ∀ q ∈ carries j, s.basis q = false
  padding : ∀ t : Nat, Shadow7.wpP (start j) ≤ t → t < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) t) = false
  bank : regValue (ys j) s.basis =
    if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0
  zero : ∀ q ∈ watched j, s.basis q = false
  far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z)
  side : s.basis (Shadow7.e0P (start j) + 4) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u))
  record : IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis) =
    SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  extra : ∀ q, Shadow7.e0P (start j) + 10 ≤ q → q < Shadow7.e0P (start j) + 10 + (Shadow7.wpP (start j) - 1 - (Shadow7.e0P (start j) - 1598)) →
    s.basis q = false

theorem mem_spare (j : Fin 23) (q : Wire) :
    q ∈ spare j ↔ q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7 ∨
      (Shadow7.e0P (start j) + 10 ≤ q ∧ q < Shadow7.e0P (start j) + 10 + (Shadow7.wpP (start j) - 1 - (Shadow7.e0P (start j) - 1598))) := by
  simp only [spare, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1, or_assoc]

/-- dadon's `geometry`: every wire `Inputs` asks to be clean is a native carry wire or a spare. -/
theorem touch_clean (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State)
    (cl : ∀ q : Wire, 1556 ≤ q → q < Shadow7.e0P (start j) → s.basis q = false) (ex : ∀ q ∈ spare j, s.basis q = false) :
    (∀ q ∈ 1556::1557::1558::fullC, s.basis q = false) ∧ (∀ p ∈ longPairs j, s.basis p.2 = false) ∧
      (∀ q ∈ carries j, s.basis q = false) ∧
      (∀ t : Nat, Shadow7.wpP (start j) ≤ t → t < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) t) = false) ∧
      (∀ q ∈ watched j, s.basis q = false) ∧
      (∀ q, Shadow7.e0P (start j) + 10 ≤ q → q < Shadow7.e0P (start j) + 10 + (Shadow7.wpP (start j) - 1 - (Shadow7.e0P (start j) - 1598)) →
        s.basis q = false) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have g := env_geo w1 w3
  have he : Shadow7.e0P (start j) = 1574 + Shadow7.sbP (start j) := rfl
  have sb61 : 61 ≤ Shadow7.sbP (start j) := by unfold Shadow7.sbP; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    simp only [fullC, List.mem_cons, List.mem_map, List.mem_range] at hq
    apply cl <;> (rcases hq with h | h | h | ⟨i, hi, rfl⟩ <;> (try subst h) <;> ((try unfold Wire at *); omega))
  · intro p hp
    simp only [longPairs, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    apply cl <;> ((try unfold Wire at *); (try dsimp only); omega)
  · intro q hq
    simp only [carries, List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    unfold Shadow7.poolW
    split_ifs with h
    · apply cl <;> ((try unfold Wire at *); omega)
    · apply ex; rw [mem_spare]; right; right
      constructor <;> ((try unfold Wire at *); omega)
  · intro t lo hi
    -- `env_geo` only has `2 ≤ wp`. The low branch of `Shadow7.bankW` is `t < 3`, so that is one short:
    -- `t ≥ wp` does not give `¬ t < 3`. On this window `wp ≥ 31`.
    have wp3 : 3 ≤ Shadow7.wpP (start j) := by
      unfold Shadow7.wpP railP Shadow7.sbP; (try split_ifs) <;> omega
    have hb : (Shadow7.bankW (start j) t : Nat) = 1598 + (t - Shadow7.wpP (start j)) := by
      unfold Shadow7.bankW
      rw [if_neg (by omega), if_neg (by omega)]
      exact Nat.add_sub_assoc lo 1598
    rw [hb]
    apply cl <;> ((try unfold Wire at *); omega)
  · intro q hq
    simp only [watched, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hq
    rcases hq with (h | h) | ⟨lo, hi⟩
    · exact ex _ ((mem_spare j q).mpr (Or.inl h))
    · exact ex _ ((mem_spare j q).mpr (Or.inr (Or.inl h)))
    · apply cl <;> ((try unfold Wire at *); omega)
  · intro q lo hi
    exact ex _ ((mem_spare j q).mpr (Or.inr (Or.inr ⟨lo, hi⟩)))

/-- dadon's `Leave{s}Admission.assemble`. -/
theorem assemble (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (numbers : Numeric j z)
    (rails : Shadow7.onRails j 15 (SkywalkTrace.next^[15] (SkywalkRails.encode g0 s0
      (Shadow.reduced (Shadow7.sbP (start j)) 15 z).u (Shadow.reduced (Shadow7.sbP (start j)) 15 z).v)) s.basis)
    (record : IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v))
    (saved : regValue (ys j) s.basis =
        (if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) ∧
      s.basis (Shadow7.e0P (start j) + 5) = false ∧ s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      s.basis (Shadow7.e0P (start j) + 4) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j)) ≤ z.u))
    (ex : ∀ q ∈ spare j, s.basis q = false) : Inputs j s z g0 s0 := by
  have cl := native_carryJ j h0 (by omega) _ s rails
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := touch_clean j h0 (by omega) s cl ex
  refine ⟨numbers, ?_, saved.2.1, c1, c2, c3, c4, saved.1, c5, saved.2.2.1, ?_, record, c6⟩
  · exact (SharedSigned.same_shadow7 _ z numbers.farSmall numbers.odd g0 s0).1 ▸ rails
  · rw [saved.2.2.2]
    by_cases f : Shadow.far (Shadow7.sbP (start j)) 15 z <;> simp [f]

end Admission

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.ReleasedOrigin
open Arithmetic MappedCompressed WideReference Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- dadon's `Leave{s}ReleasedOrigin.releasedSite`: the A wire and B band freed when the rail narrows from `R(s)` to
`R(s+15)`, the sig-moved band `[1301, s+1058]`, and (window390, blocks 375 and 390) the released B-rail wires
`[1302-s, 933]` that host the archive scratch beyond the stock carry: used by the block's loader, blank after it and
clean in the stock state. 210: {498, 1043}; 225, 240: {}; 255: {529, 1029..1042, 1301..1313}. -/
def releasedSite (j : Fin 23) (q : Nat) : Prop :=
  (railP (start j + 15) < railP (start j) ∧ q = start j + 31 + railP (start j + 15)) ∨
  (785 + railP (start j + 15) < q ∧ q ≤ 785 + railP (start j)) ∨ (1301 ≤ q ∧ q ≤ 1058 + start j) ∨
  (369 ≤ start j ∧ 1302 ≤ q + start j ∧ q ≤ 933)
instance (j : Fin 23) (q : Nat) : Decidable (releasedSite j q) := by unfold releasedSite; infer_instance

/-- dadon's `Leave{s}ReleasedOrigin.released`, for every window block. -/
theorem released (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (x p : Nat) (good : Bounds x p)
    (raw history : State) (dom : Domain (start j) x p raw) (q : Nat) (site : releasedSite j q) :
    (origin (start j) raw history).basis q = false := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have hw := LeaveJ7.WideWords.width j h0 (by omega)
  unfold W.compactSkywalkTickPreWidth at hw
  have hR : railP (start j) ≤ 258 ∧ railP (start j + 15) ≤ railP (start j) := by
    unfold railP; constructor <;> split_ifs <;> omega
  unfold releasedSite at site
  rcases site with ⟨shrink, rfl⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨t369, lo, hi⟩
  · exact pool_origin (by omega) good raw history dom _ (by omega) (by omega)
      (Or.inl (poolA_released _ _ (by omega) (by omega) (by omega)))
  · exact pool_origin (by omega) good raw history dom _ (by omega) (by omega)
      (Or.inr (poolB_released _ _ (by omega) (by omega) (by omega)))
  · exact band_origin_wide (by omega) good raw history dom q lo (by omega)
  · have rp : railP (start j + 15) + start j = 498 := by unfold railP; split_ifs <;> omega
    exact pool_origin (by omega) good raw history dom _ (by omega) (by omega)
      (Or.inr (poolB_released _ _ (by omega) (by omega) (by omega)))

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.ReleasedOrigin

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

theorem entry_dest : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 20 → (entryOps (start j)).all (fun g =>
    (decide (Shadow7.a0P (start j) - 1 ≤ target g) && decide (target g ≤ Shadow7.a0P (start j) + 17)) ||
    (decide (Shadow7.b0P (start j) - 1 ≤ target g) && decide (target g ≤ Shadow7.b0P (start j) + 17)) ||
    (decide (start j + 16 ≤ target g) && decide (target g ≤ start j + 30)) ||
    (decide (1556 ≤ target g) && decide (target g ≤ 1575)) || decide (target g = Shadow7.e0P (start j) + 5)) = true := by
  decide +kernel

theorem entry_keep (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Nat)
    (hq : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 17) ∨ (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 17) ∨
      (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨ (1556 ≤ q ∧ q ≤ 1575) ∨ q = Shadow7.e0P (start j) + 5)) (s : State) (m : List Bool) :
    (run (GateMirror.forward (entryOps (start j))) m s).basis q = s.basis q := by
  apply LeaveReadoutFrame.preserved
  intro hm
  rw [dest_forward] at hm
  obtain ⟨g, hg, e⟩ := List.mem_map.mp hm
  have := List.all_eq_true.mp (entry_dest j h0 (by omega)) g hg
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  rw [e] at this
  exact hq (by unfold Wire at *; omega)

/-- dadon's `Leave{s}FullArithmetic.program`. -/
def fullProgram (j : Fin 23) : Program :=
  GateMirror.forward (entryOps (start j) ++ bodyOps j) ++ Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558

/-- The common core of the full arithmetic: the Shadow7.routed Shadow7.body after the entry (dadon's `Leave{s}Routed.result` applied
to `run entry`), as used by FullArithmetic, FlagScratch, CoreCheckpoint, HighZero. -/
theorem full_routed (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (z : SkywalkNat.State) (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (ys j) s.basis = if far (Shadow7.sbP (start j)) 15 z then high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ watched j, s.basis q = false)
    (par : oddRead j s.basis = oddBits (letters 15 (reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (swaps j i) = decide (i = key (actualMode (Shadow7.sbP (start j)) z))) :
    let a := run (GateMirror.forward (entryOps (start j))) m s
    let n := m.drop (measurementCount (GateMirror.forward (entryOps (start j))))
    let out := run (GateMirror.forward (bodyOps j)) n a
    let t := run (GateMirror.forward (fullPrefix j)) n a
    out.phase = a.phase ∧ (∀ i < Shadow7.wpP (start j) + 15, out.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      (∀ i : Fin 18, out.basis (row j i).free = false) ∧ (∀ i : Fin 39, out.basis (1559 + i.val) = false) ∧
      (∀ q, HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q → (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) →
        out.basis q = cleared t.basis q) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have front := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
  have watchedOK := frontReady_frame j h0 (by omega) s m z G sg small ready fresh scratch temp
  intro a n
  have kept (q : Nat) (ok : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 17) ∨
      (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 17) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨
      (1556 ≤ q ∧ q ≤ 1575) ∨ q = Shadow7.e0P (start j) + 5)) : a.basis q = s.basis q := entry_keep j h0 (by omega) q ok s m
  exact routed_result j h0 (by omega) z a n small odd room
    (fun q hq => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
      have p := Shadow7.pool_cases (i := i) w1 w2
      exact (kept _ (by unfold Wire at *; omega)).trans (clean _ hq))
    (fun i lo hi => by
      have b := Shadow7.bank_cases w1 w2 hi
      exact (kept _ (by unfold Wire at *; omega)).trans (padding i lo hi))
    (upperBits j h0 (by omega) _ a.basis front.2.2.2.2.2.1)
    (((regValue_eq_iff _ _ _).mpr (fun q hq => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
      have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
      exact kept _ (by unfold Wire at *; omega))).trans bank)
    (fun q hq => (watchedOK _ hq).trans (zero _ hq))
    ((entry_parity j h0 (by omega) s m).trans par)
    (by rw [kept _ (by omega), kept _ (by omega)]; exact mode)
    (fun on i hi hq => by
      have sw := swaps_cases j h0 (by omega) i hi
      exact (kept _ (by unfold Wire at *; omega)).trans (events on i hi hq))

/-- dadon's `Leave{s}FullArithmetic.result`. -/
theorem fullArithmetic_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (z : SkywalkNat.State) (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (ys j) s.basis = if far (Shadow7.sbP (start j)) 15 z then high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ watched j, s.basis q = false)
    (par : oddRead j s.basis = oddBits (letters 15 (reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (swaps j i) = decide (i = key (actualMode (Shadow7.sbP (start j)) z))) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let out := run (fullProgram j) m s
    out.phase = s.phase ∧ regValue (smallM j) out.basis = (mag/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j)) ∧
      out.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ mag) ∧
      (∀ i < Shadow7.wpP (start j) + 15, out.basis (live j i) = (TrueMiddle.F j z).testBit i) := by
  have front := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
  have used := full_routed j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  generalize ha : run (GateMirror.forward (entryOps (start j))) m s = a at front used
  have restored := routedRestore_result j h0 (by omega) z sg a (m.drop (measurementCount (GateMirror.forward (entryOps (start j)))))
    ((m.drop (measurementCount (GateMirror.forward (entryOps (start j))))).drop
      (measurementCount (GateMirror.forward (bodyOps j)))) small front.2.1 ⟨front.2.2.2.1, front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  dsimp only
  rw [fullProgram, forward_app, List.append_assoc, run_append, run_take, run_append, run_take, ha]
  exact ⟨restored.1.trans (used.1.trans front.1), restored.2.2.1, restored.2.2.2⟩

/-! FlagScratch (dadon's `Leave{s}FlagScratch`). -/

/-- dadon's `LeaveCompanion{s}.pendingPairs` (the StoreMapped chain: top, then the bank above the low columns). -/
def pendingPairs (j : Fin 23) : List (Wire × Wire) :=
  (List.range (Shadow7.wpP (start j) + 15 - Shadow7.lowsP (start j) + 1)).map (fun i =>
    (if i = 0 then Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 else Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i - 1), Shadow7.storeW (start j) (i+1)))
/-- dadon's `LeaveCompanion{s}.clearFlagPairs`. -/
def clearFlagPairs (j : Fin 23) : List (Wire × Wire) :=
  (List.range (Shadow7.lowsP (start j) + 1)).map (fun i => (Shadow7.b0P (start j) - 1 + i, 1559 + i))
/-- dadon's `Leave{s}FlagScratch.targets`. -/
def flagTargets (j : Fin 23) : List Wire := (pendingPairs j ++ clearFlagPairs j).map Prod.snd

theorem flagScratch_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (z : SkywalkNat.State) (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (ys j) s.basis = if far (Shadow7.sbP (start j)) 15 z then high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ watched j, s.basis q = false)
    (par : oddRead j s.basis = oddBits (letters 15 (reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (swaps j i) = decide (i = key (actualMode (Shadow7.sbP (start j)) z))) :
    ∀ q ∈ flagTargets j, (run (fullProgram j) m s).basis q = false := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have front := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
  have used := full_routed j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  generalize ha : run (GateMirror.forward (entryOps (start j))) m s = a at front used
  have restored := routedRestore_result j h0 (by omega) z sg a (m.drop (measurementCount (GateMirror.forward (entryOps (start j)))))
    ((m.drop (measurementCount (GateMirror.forward (entryOps (start j))))).drop
      (measurementCount (GateMirror.forward (bodyOps j)))) small front.2.1 ⟨front.2.2.2.1, front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  intro q hq
  -- geometry: every flag target is a selector wire 1559..1597 or a pool wire above 1612 (below or above the anchor)
  have geo : (1559 ≤ q ∧ q ≤ 1597) ∨ (∃ k, k < Shadow7.wpP (start j) - 1 ∧ q = Shadow7.poolW (start j) k ∧ 1613 ≤ q ∧ (q < Shadow7.e0P (start j) ∨ Shadow7.e0P (start j) + 10 ≤ q)) := by
    simp only [flagTargets, List.map_append, List.mem_append, List.mem_map] at hq
    rcases hq with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
      have sc := Shadow7.storeW_cases (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2 (i+1)
      dsimp only
      by_cases lo : 1558 + (i+1) < 1598
      · left; unfold Wire at *; omega
      · right
        refine ⟨i - 24, by omega, ?_, by unfold Wire at *; omega, by unfold Wire at *; omega⟩
        have pc := Shadow7.pool_cases (i := i - 24) w1 w2
        unfold Wire at *; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
      left
      show 1559 ≤ 1559 + i ∧ 1559 + i ≤ 1597
      (try unfold Wire at *); omega
  have notM : q ∉ smallM j := by
    intro h; obtain ⟨i, hi, e⟩ := List.mem_map.mp h; rw [List.mem_range] at hi
    rcases geo with g|⟨k, _, _, g1, g2⟩ <;> unfold Wire at * <;> omega
  rw [fullProgram, forward_app, List.append_assoc, run_append, run_take, run_append, run_take, ha, restored.2.1 _ notM]
  rcases geo with g|⟨k, hk, e, g1, g2⟩
  · obtain ⟨i, rfl⟩ : ∃ i : Fin 39, q = 1559 + i.val :=
      ⟨⟨q - 1559, by unfold Wire at *; omega⟩, by simp only []; unfold Wire at *; omega⟩
    exact used.2.2.2.1 i
  · have notWire : HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q := by
      intro i hi e'; have b := Shadow7.bank_cases w1 w2 hi; unfold Wire at *; omega
    have notCols : ∀ c ∈ cols j, q ≠ c.shadow ∧ q ≠ c.tube := by
      intro c hc; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
      exact ⟨by dsimp only; unfold Wire at *; omega, by dsimp only; unfold Wire at *; omega⟩
    rw [used.2.2.2.2 q notWire notCols, cleared, if_neg (by unfold Wire at *; omega)]
    rw [prefix_keep j h0 (by omega) q (by unfold Wire at *; omega)]
    have kq : a.basis q = s.basis q := by
      rw [← ha]; exact entry_keep j h0 (by omega) q (by unfold Wire at *; omega) s m
    rw [kq]; exact clean _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, e.symm⟩)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror PortalAnd SkywalkNat IntegerHigh Shadow LeaveCompanion
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-! Gate-level chains are dadon's `PortalAnd.chain`. -/

theorem forward_xsG (xs : List Wire) : GateMirror.forward (xsG xs) = notRegister xs := forward_xsG' xs

theorem forward_cons' (g : Gate) (gs : List Gate) : GateMirror.forward (g :: gs) = front g :: GateMirror.forward gs := rfl
theorem forward_nil' : GateMirror.forward [] = [] := rfl

theorem forward_chainG (c seq : Nat → Wire) (out : Wire) : ∀ (i n : Nat),
    GateMirror.forward (chainG c seq [.cx (c (i+n)) out, .x out] i n) =
      PortalAnd.chain true none out (c i) ((List.range n).map (fun k => (seq (i+k), c (i+k+1))))
  | i, 0 => by simp [chainG, PortalAnd.chain, PortalAnd.target, GateMirror.forward, front]
  | i, n+1 => by
    have ih := forward_chainG c seq out (i+1) n
    rw [show i + 1 + n = i + (n+1) by omega] at ih
    have el : (List.range (n+1)).map (fun k => (seq (i+k), c (i+k+1))) =
        (seq i, c (i+1)) :: (List.range n).map (fun k => (seq (i+1+k), c (i+1+k+1))) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg₂ List.cons rfl (List.map_congr_left (fun k _ => ?_))
      show (seq (i+(k+1)), c (i+(k+1)+1)) = (seq (i+1+k), c (i+1+k+1))
      rw [show i + (k+1) = i + 1 + k by omega]
    show GateMirror.forward (.make (c i) (seq i) (c (i+1)) ::
      (chainG c seq [.cx (c (i+(n+1))) out, .x out] (i+1) n ++ [.pop (c i) (seq i) (c (i+1))])) = _
    rw [forward_cons', forward_app, ih, el]
    rfl

theorem sites_perm : ∀ ps : List (Wire × Wire), (PortalAnd.sites ps).Perm (ps.map Prod.fst ++ ps.map Prod.snd)
  | [] => by simp [PortalAnd.sites]
  | p::ps => by
    have ih := sites_perm ps
    change (p.1 :: p.2 :: PortalAnd.sites ps).Perm (p.1 :: (ps.map Prod.fst ++ p.2 :: ps.map Prod.snd))
    exact (List.Perm.cons _ ((List.Perm.cons _ ih).trans List.perm_middle.symm))

/-- The StoreMapped pairs (dadon's `pendingPairs`, defined in Fam8): first components. -/
theorem pending_fst (j : Fin 23) : (pendingPairs j).map Prod.fst =
    (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) ::
      (List.range (Shadow7.wpP (start j) + 15 - Shadow7.lowsP (start j))).map (fun i => Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i)) := by
  simp only [pendingPairs, List.map_map, Function.comp]
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Function.comp, if_pos, Nat.succ_ne_zero, if_false]
  congr 1

theorem forward_chainG0 (c seq : Nat → Wire) (out : Wire) (n : Nat) :
    GateMirror.forward (chainG c seq [.cx (c n) out, .x out] 0 n) =
      PortalAnd.chain true none out (c 0) ((List.range n).map (fun k => (seq k, c (k+1)))) := by
  have h := forward_chainG c seq out 0 n
  simp only [Nat.zero_add] at h
  exact h

theorem clearFlag_fst (j : Fin 23) :
    (clearFlagPairs j).map Prod.fst = (List.range (Shadow7.lowsP (start j) + 1)).map (Shadow7.b0P (start j) - 1 + ·) := by
  simp only [clearFlagPairs, List.map_map]; rfl

theorem storeW_zero7 (s : Nat) : Shadow7.storeW s 0 = 1558 := by
  simp only [Shadow7.storeW, Partial.storeW, Shadow7.e0P]
  split_ifs <;> ((try unfold Wire at *); omega)

theorem storeMapped_parts (j : Fin 23) :
    GateMirror.forward (Shadow7.leaveStoreMapped (start j)) =
      threshold (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 2) (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 1) 1558 1557 (pendingPairs j) ++
        ([.CCX 1556 1557 1558] ++ latch true none 1556 1558 (clearFlagPairs j)) := by
  have ch1 : GateMirror.forward (chainG (Shadow7.storeW (start j))
      (fun i => if i = 0 then Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 else Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i - 1))
      [.cx (Shadow7.storeW (start j) (Shadow7.wpP (start j) + 15 - Shadow7.lowsP (start j) + 1)) 1557, .x 1557] 0 (Shadow7.wpP (start j) + 15 - Shadow7.lowsP (start j) + 1)) =
      PortalAnd.chain true none 1557 1558 (pendingPairs j) := by
    rw [forward_chainG0, storeW_zero7]; rfl
  have ch2 : GateMirror.forward (chainG (fun i => (1558 + i : Wire)) (fun i => Shadow7.b0P (start j) - 1 + i)
      [.cx (1558 + (Shadow7.lowsP (start j) + 1)) 1556, .x 1556] 0 (Shadow7.lowsP (start j) + 1)) =
      PortalAnd.chain true none 1556 1558 (clearFlagPairs j) := by
    have h := forward_chainG0 (fun i => (1558 + i : Wire)) (fun i => Shadow7.b0P (start j) - 1 + i) 1556 (Shadow7.lowsP (start j) + 1)
    have e : (List.range (Shadow7.lowsP (start j) + 1)).map (fun k => (Shadow7.b0P (start j) - 1 + k, (1558 + (k+1) : Wire))) =
        clearFlagPairs j := by
      simp only [clearFlagPairs]; apply List.map_congr_left; intro k _; simp only [Prod.mk.injEq, true_and]
      unfold Wire; omega
    rw [← e]; exact h
  simp only [Shadow7.leaveStoreMapped, forward_app, forward_xsG, ch1, ch2, threshold, PortalAnd.latch, PortalAnd.digits,
    pending_fst, clearFlag_fst, forward_cons', forward_nil', front, erase, notRegister, List.map_cons, List.map_nil,
    List.map_append, List.reverse_cons, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
    if_true, ↓reduceIte]


/-! The scanned output register (dadon's `OutputPorts.scanned`, `outputRegisters` high part). -/

def scanned (j : Fin 23) : List Wire :=
  (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 2) :: (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 1) :: (pendingPairs j).map Prod.fst

theorem scanned_eq (j : Fin 23) : scanned j =
    (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 2) :: (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 1) :: (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) ::
      (List.range (Shadow7.wpP (start j) + 15 - Shadow7.lowsP (start j))).map (fun i => Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i)) := by
  rw [scanned, pending_fst]

theorem outputScanned (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (Z : Nat)
    (bits : ∀ i < Shadow7.wpP (start j) + 15, s.basis (live j i) = Z.testBit i) :
    regValue (scanned j) s.basis = (Z / 2^(Shadow7.lowsP (start j) - 3)) % 2^(Shadow7.wpP (start j) + 15 - Shadow7.lowsP (start j) + 3) := by
  have rr := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  have len : (scanned j).length = Shadow7.wpP (start j) + 15 - Shadow7.lowsP (start j) + 3 := by
    rw [scanned_eq]; simp
  rw [← len]
  apply EnterProof.value_of_bits (scanned j)
  intro i hi
  rw [len] at hi
  have g : (scanned j).getD i 0 = live j (Shadow7.lowsP (start j) - 3 + i) := by
    rw [scanned_eq]
    rcases i with _ | _ | _ | i
    · simp [live]; rw [if_pos (by omega)]; (try unfold Wire at *); omega
    · simp [live]; rw [if_pos (by omega)]; (try unfold Wire at *); omega
    · simp [live]; rw [if_pos (by omega)]; (try unfold Wire at *); omega
    · simp [live, List.getD_eq_getElem?_getD, show i < Shadow7.wpP (start j) + 15 - Shadow7.lowsP (start j) by omega]
      rw [if_neg (by omega)]; congr 1; omega
  rw [g, Nat.testBit_div_two_pow, Nat.add_comm i]
  exact bits _ (by omega)

/-! The pending threshold (dadon's `LeaveCompanion{s}.pending_three`). -/

theorem pending_layout (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ((Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 2) :: (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 1) :: (1557:Wire) :: (1558:Wire) ::
      PortalAnd.sites (pendingPairs j)).Nodup := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have fst_range : ∀ q ∈ (pendingPairs j).map Prod.fst,
      q = Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 ∨ ∃ i, Shadow7.lowsP (start j) ≤ i ∧ i < Shadow7.wpP (start j) + 15 ∧ q = Shadow7.bankW (start j) i := by
    intro q hq; rw [pending_fst] at hq
    rcases List.mem_cons.mp hq with h|h
    · exact Or.inl h
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h; rw [List.mem_range] at hi
      exact Or.inr ⟨Shadow7.lowsP (start j) + i, by omega, by omega, rfl⟩
  have snd_range : ∀ q ∈ (pendingPairs j).map Prod.snd, ∃ k, 1 ≤ k ∧ k ≤ Shadow7.wpP (start j) + 15 - Shadow7.lowsP (start j) + 1 ∧ q = Shadow7.storeW (start j) k := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
    exact ⟨i+1, by omega, by omega, rfl⟩
  have bankOut : ∀ i, Shadow7.lowsP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → ∀ k, (Shadow7.storeW (start j) k : Nat) ≠ Shadow7.bankW (start j) i ∧
      (Shadow7.bankW (start j) i : Nat) ≠ 1557 ∧ (Shadow7.bankW (start j) i : Nat) ≠ 1558 ∧ (Shadow7.bankW (start j) i : Nat) > Shadow7.a0P (start j) + 20 := by
    intro i a b k
    have bc := Shadow7.bank_cases w1 w2 b; have sc := Shadow7.storeW_cases (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2 k
    unfold Wire at *; omega
  have perm := (((sites_perm (pendingPairs j)).cons (1558:Wire)).cons (1557:Wire)).cons
    (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 1) |>.cons (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 2)
  rw [perm.nodup_iff]
  have topv : Shadow7.a0P (start j) + 18 ≤ 529 := by omega
  have fnd : ((pendingPairs j).map Prod.fst).Nodup := by
    rw [pending_fst, List.nodup_cons]
    refine ⟨fun h => ?_, List.Nodup.map_on (fun x hx y hy e => ?_) List.nodup_range⟩
    · obtain ⟨i, hi, e⟩ := List.mem_map.mp h; rw [List.mem_range] at hi
      have := (bankOut (Shadow7.lowsP (start j) + i) (by omega) (by omega) 0).2.2.2; unfold Wire at *; omega
    · rw [List.mem_range] at hx hy
      have := Shadow7.bank_inj w1 w2 (by omega) (by omega) e; omega
  have snd : ((pendingPairs j).map Prod.snd).Nodup := by
    simp only [pendingPairs, List.map_map]
    refine List.Nodup.map_on (fun x hx y hy e => ?_) List.nodup_range
    have a := Shadow7.storeW_cases (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2 (x+1); have b := Shadow7.storeW_cases (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2 (y+1)
    simp only [Function.comp] at e; unfold Wire at *; omega
  have disj : ∀ a ∈ (pendingPairs j).map Prod.fst, ∀ b ∈ (pendingPairs j).map Prod.snd, a ≠ b := by
    intro a ha b hb e
    obtain ⟨k, k1, k2, rfl⟩ := snd_range b hb
    have sc := Shadow7.storeW_cases (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2 k
    rcases fst_range a ha with rfl|⟨i, i1, i2, rfl⟩
    · unfold Wire at *; omega
    · exact (bankOut i i1 i2 k).1 e.symm
  have notIn : ∀ x : Nat, (x < 1556 ∧ x ≤ Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 1) ∨ x = 1557 ∨ x = 1558 →
      x ∉ (pendingPairs j).map Prod.fst ++ (pendingPairs j).map Prod.snd := by
    intro x hx hm
    rcases List.mem_append.mp hm with h|h
    · rcases fst_range x h with rfl|⟨i, i1, i2, e⟩
      · unfold Wire at *; omega
      · have := bankOut i i1 i2 0; rw [e] at hx; unfold Wire at *; omega
    · obtain ⟨k, k1, k2, e⟩ := snd_range x h
      have sc := Shadow7.storeW_cases (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2 k; rw [e] at hx; unfold Wire at *; omega
  simp only [List.nodup_cons, List.mem_cons, not_or]
  refine ⟨⟨by omega, by omega, by omega, ?_⟩, ⟨by omega, by omega, ?_⟩, ⟨by decide, ?_⟩, ?_, List.nodup_append.mpr ⟨fnd, snd, disj⟩⟩
  · exact notIn (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 2) (Or.inl ⟨by omega, by omega⟩)
  · exact notIn (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 1) (Or.inl ⟨by omega, le_refl _⟩)
  · exact notIn 1557 (Or.inr (Or.inl rfl))
  · exact notIn 1558 (Or.inr (Or.inr rfl))

/-- dadon's `LeaveCompanion{s}.pending_three`. -/
theorem pending_three (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (fresh : s.basis 1558 = false) (clean : ∀ p ∈ pendingPairs j, s.basis p.2 = false) :
    run (threshold (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 2) (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 1) 1558 1557 (pendingPairs j)) m s =
      ⟨s.phase, writeBit s.basis 1557 (s.basis 1557 ^^ decide (3 ≤ regValue (scanned j) s.basis))⟩ := by
  have h := threshold_run _ _ 1558 1557 (pendingPairs j) (pending_layout j h0 (by omega)) s m fresh clean
  have hh := LeaveCompanion.high_three (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 2) (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 1)
    (pendingPairs j) s.basis
  unfold PortalAnd.high at hh
  rw [h, hh]; rfl

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror PortalAnd SkywalkNat IntegerHigh Shadow LeaveCompanion
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-! NextFlagTruth. -/

/-- dadon's `Leave{s}NextFlagTruth.value`: the scanned register holds the next block's high value. -/
theorem nextFlag_value (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (z : SkywalkNat.State) :
    TrueMiddle.F j z / 2^(Shadow7.lowsP (start j) - 3) = Shadow.high (Shadow7.sbP (start j + 15)) 15 (step^[15] z) := by
  have rr := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  unfold TrueMiddle.F Shadow.high limb HighBankSum.total
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 2
  omega

/-- dadon's `Leave{s}NextFlagTruth.boundNear`. -/
theorem nextFlag_boundNear (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (a : SkywalkNat.State) (sign : Nat)
    (near : ¬ far (Shadow7.sbP (start j + 15)) 15 a) :
    a.u - sign < (2 * 2^(Shadow7.sbP (start j))) * 2^(smallM j).length := by
  have rr := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  apply near_bound a.u a.v sign (limb (Shadow7.sbP (start j + 15)) 15) _ (by unfold limb; positivity)
  · rw [smallM_length]; unfold limb
    have e : 2 * 2^(Shadow7.sbP (start j)) * 2^(Shadow7.lowsP (start j)) = 2^(Shadow7.sbP (start j + 15) + 15 + 1) * 2^3 := by
      rw [← Nat.pow_succ', ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [e]; omega
  · simpa only [decide_eq_false_iff_not, far, Shadow.high] using near

/-- dadon's `Leave{s}NextFlagTruth.orientation`. -/
theorem nextFlag_orientation (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (a : SkywalkNat.State) (sign : Nat)
    (bit : sign ≤ 1) (small : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 a) (farA : far (Shadow7.sbP (start j + 15)) 15 a) :
    (2^(Shadow7.sbP (start j)) ≤ a.u - sign) ↔ (2^(Shadow7.sbP (start j + 15)) ≤ a.u) := by
  have small := small farA
  have rr := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  have lower := (Nat.le_div_iff_mul_le (by unfold limb; positivity : 0 < limb (Shadow7.sbP (start j + 15)) 15)).mp farA
  unfold limb at lower
  -- powers in terms of P = 2^sb'
  obtain ⟨d, hd, hdd⟩ : ∃ d, Shadow7.sbP (start j) = Shadow7.sbP (start j + 15) + d ∧ (d = 7 ∨ d = 8) :=
    ⟨Shadow7.sbP (start j) - Shadow7.sbP (start j + 15), by omega, by omega⟩
  have p2 : 2^(Shadow7.sbP (start j + 15) + 15 + 1) = 65536 * 2^(Shadow7.sbP (start j + 15)) := by
    rw [show Shadow7.sbP (start j + 15) + 15 + 1 = Shadow7.sbP (start j + 15) + 16 by omega, Nat.pow_add, Nat.mul_comm]
  rw [p2] at lower
  rcases hdd with rfl | rfl
  · have p1 : 2^(Shadow7.sbP (start j)) = 128 * 2^(Shadow7.sbP (start j + 15)) := by rw [hd, Nat.pow_add, Nat.mul_comm]
    rw [p1]
    generalize 2^(Shadow7.sbP (start j + 15)) = P at *
    constructor <;> intro h <;> omega
  · have p1 : 2^(Shadow7.sbP (start j)) = 256 * 2^(Shadow7.sbP (start j + 15)) := by rw [hd, Nat.pow_add, Nat.mul_comm]
    rw [p1]
    generalize 2^(Shadow7.sbP (start j + 15)) = P at *
    constructor <;> intro h <;> omega

/-! nextU and the clear-flag latch. -/

theorem nextU_run (s : State) (m : List Bool) (fresh : s.basis 1558 = false) :
    run ([.CCX 1556 1557 1558] : Program) m s = ⟨s.phase, writeBit s.basis 1558 (s.basis 1556 && s.basis 1557)⟩ := by
  simp [run, fresh]

theorem clearFlag_layout (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    (1556 :: (1558:Wire) :: PortalAnd.sites (clearFlagPairs j)).Nodup := by
  have rr := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  rw [((sites_perm _).cons _).cons _ |>.nodup_iff]
  simp only [clearFlagPairs, List.map_map, Function.comp, List.nodup_cons, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range, not_or, not_exists, not_and]
  refine ⟨⟨by decide, fun i _ e => by unfold Wire at *; omega, fun i _ e => by unfold Wire at *; omega⟩,
    ⟨fun i _ e => by unfold Wire at *; omega, fun i _ e => by unfold Wire at *; omega⟩,
    List.nodup_append.mpr ⟨List.Nodup.map (fun a b e => by
        have e' : Shadow7.b0P (start j) - 1 + a = Shadow7.b0P (start j) - 1 + b := e
        unfold Wire at *; omega) List.nodup_range,
      List.Nodup.map (fun a b e => by
        have e' : 1559 + a = 1559 + b := e
        unfold Wire at *; omega) List.nodup_range, fun a ha b hb e => ?_⟩⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
  rw [List.mem_range] at hi hk
  have e' : Shadow7.b0P (start j) - 1 + i = 1559 + k := e
  omega

theorem clearFlag_digits (j : Fin 23) : PortalAnd.digits 1558 (clearFlagPairs j) = 1558 :: (Shadow7.b0P (start j) - 1) :: smallM j := by
  simp only [PortalAnd.digits, clearFlagPairs, smallM, List.map_map, Function.comp]
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Function.comp, Nat.add_zero]
  congr 2
  apply List.map_congr_left; intro i _
  show Shadow7.b0P (start j) - 1 + (i + 1) = Shadow7.b0P (start j) + i
  unfold Shadow7.b0P; omega

/-- dadon's `LeaveCompanion{s}.clearFlag_value`. -/
theorem clearFlag_value (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (half mag : Nat)
    (hp : 0 < half) (clean : ∀ p ∈ clearFlagPairs j, s.basis p.2 = false)
    (near : s.basis 1557 = false → mag < (2*half) * 2^(smallM j).length)
    (longBit : s.basis 1556 = decide (half ≤ mag))
    (orientation : s.basis 1558 = (s.basis 1556 && s.basis 1557))
    (bottom : s.basis (Shadow7.b0P (start j) - 1) = decide (half ≤ mag % (2*half)))
    (upper : regValue (smallM j) s.basis = (mag / (2*half)) % 2^(smallM j).length) :
    run (latch true none 1556 1558 (clearFlagPairs j)) m s = ⟨s.phase, writeBit s.basis 1556 false⟩ := by
  have width : half ≤ (2*half) * 2^(smallM j).length := by
    have pow : 1 ≤ 2^(smallM j).length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  have hr := run_latch true none 1556 1558 (clearFlagPairs j) (clearFlag_layout j h0 (by omega)) (by simp) s m clean
  simp only [active, Option.elim_none, Bool.true_and] at hr
  rw [hr, clearFlag_digits]
  simp only [List.any_cons, LeaveCompanion.any_positive, upper, bottom, orientation, longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp, LeaveCompanion.retain_flag half _ mag _ width near]
  simp

/-! TailFlags (dadon's `Leave{s}TailFlags.result`: the StoreMapped segment). -/

theorem tailFlags_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (a : SkywalkNat.State) (s : State)
    (m : List Bool) (sign : Nat) (bit : sign ≤ 1) (small : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 a)
    (x : s.basis 1557 = false) (y : s.basis 1558 = false)
    (scan : regValue (scanned j) s.basis = Shadow.high (Shadow7.sbP (start j + 15)) 15 a)
    (cleanP : ∀ p ∈ pendingPairs j, s.basis p.2 = false)
    (cleanC : ∀ p ∈ clearFlagPairs j, s.basis p.2 = false)
    (long : s.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ a.u - sign))
    (low : s.basis (Shadow7.b0P (start j) - 1) = decide (2^(Shadow7.sbP (start j)) ≤ (a.u - sign) % (2 * 2^(Shadow7.sbP (start j)))))
    (upper : regValue (smallM j) s.basis = ((a.u - sign) / (2 * 2^(Shadow7.sbP (start j)))) % 2^(smallM j).length) :
    let f := decide (far (Shadow7.sbP (start j + 15)) 15 a)
    let u := f && decide (2^(Shadow7.sbP (start j + 15)) ≤ a.u)
    run (GateMirror.forward (Shadow7.leaveStoreMapped (start j))) m s =
      ⟨s.phase, writeBit (writeBit (writeBit s.basis 1557 f) 1558 u) 1556 false⟩ := by
  have rr := Shadow7.rail_win (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2
  intro f u
  generalize hb1 : writeBit s.basis 1557 f = b₁
  generalize hb2 : writeBit b₁ 1558 u = b₂
  have stage : run (threshold (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 2) (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 - 1) 1558 1557
      (pendingPairs j)) m s = ⟨s.phase, b₁⟩ := by
    rw [pending_three j h0 (by omega) s m y cleanP, x, Bool.false_xor, scan, ← hb1]
    rfl
  have side : (s.basis 1556 && f) = u := by
    by_cases fa : far (Shadow7.sbP (start j + 15)) 15 a
    · simp only [f, u, fa, decide_true, Bool.and_true, Bool.true_and, long]
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using nextFlag_orientation j h0 (by omega) a sign bit small fa)
    · simp [f, u, fa]
  have keep (q : Wire) (h : q ≠ 1557 ∧ q ≠ 1558) : b₂ q = s.basis q := by
    rw [← hb2, ← hb1]; simp [writeBit, h.1, h.2]
  have turn (mm : List Bool) : run ([.CCX 1556 1557 1558] : Program) mm ⟨s.phase, b₁⟩ = ⟨s.phase, b₂⟩ := by
    rw [nextU_run _ _ (by rw [← hb1]; simpa [writeBit] using y)]
    rw [← hb2, ← hb1]; simp [writeBit, side]
  have last (mm : List Bool) : run (latch true none 1556 1558 (clearFlagPairs j)) mm ⟨s.phase, b₂⟩ =
      ⟨s.phase, writeBit b₂ 1556 false⟩ := by
    apply clearFlag_value j h0 (by omega) _ _ (2^(Shadow7.sbP (start j))) (a.u - sign) (Nat.two_pow_pos _)
    · intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
      exact (keep _ ⟨by dsimp only; unfold Wire at *; omega, by dsimp only; unfold Wire at *; omega⟩).trans
        (cleanC _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    · intro h
      apply nextFlag_boundNear j h0 (by omega) a sign
      have : b₂ 1557 = f := by rw [← hb2, ← hb1]; simp [writeBit]
      simp only at h; rw [this] at h; simpa [f] using h
    · exact (keep _ ⟨by decide, by decide⟩).trans long
    · change b₂ 1558 = (b₂ 1556 && b₂ 1557)
      rw [← hb2, ← hb1]; simp [writeBit, side]
    · exact (keep _ ⟨by unfold Wire at *; omega, by unfold Wire at *; omega⟩).trans low
    · exact ((regValue_eq_iff _ _ _).mpr (fun q h => keep q (by
        obtain ⟨i, hi, e⟩ := List.mem_map.mp h; rw [List.mem_range] at hi; subst e; constructor <;> (unfold Wire at *; omega)))).trans upper
  rw [storeMapped_parts j, run_append, run_take, stage, run_append, run_take, turn, last]

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-! MaskThrough. -/

/-- The full arithmetic before the mask opens (dadon's `MaskCut.beforeOpen`, cut 169). -/
def beforeOpen (j : Fin 23) : Program :=
  GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j))) ++
    PortalAnd.latch true none 1556 (Shadow7.b0P (start j) - 1) (longPairs j)

/-- The part of the full arithmetic between the mask open and its release (dadon's `MaskThrough.interior`). -/
def interior (j : Fin 23) : Program :=
  Companion.erase (fullA j) (fullM j) fullC 1556 1558 ++ (GateMirror.forward (bodyOps j) ++
    Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558)

/-- dadon's `MaskCut.split`. -/
theorem full_split (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    fullProgram j = beforeOpen j ++ (maskP j ++ interior j) := by
  simp only [fullProgram, beforeOpen, interior, entryOps, forward_app, fix2_parts j h0 (by omega), List.append_assoc]

theorem erase_gates (j : Fin 23) : Companion.erase (fullA j) (fullM j) fullC 1556 1558 =
    GateMirror.forward (addG (fullM j) fullC 1558 ++
      (List.range 18).map (fun i => Gate.ccx 1556 (Shadow7.a0P (start j) + i) (Shadow7.b0P (start j) + i))) := by
  have hc : GateMirror.forward ((List.range 18).map (fun i => Gate.ccx 1556 (Shadow7.a0P (start j) + i) (Shadow7.b0P (start j) + i))) =
      copyRegister (some 1556) (fullA j) (fullM j) := by
    rw [fullA, fullM, copy_map]; simp only [GateMirror.forward, List.map_map]; rfl
  rw [forward_app, forward_addG, hc]; rfl

/-- The companion restore of the low columns as gates (`Shadow7.lowRest` without the mask release). -/
def restoreG (s : Nat) : List Gate :=
  (List.range (Shadow7.lowsP s)).map (fun i => .ccx 1556 (Shadow7.a0P s + i) (Shadow7.b0P s + i)) ++ xsG ((List.range (Shadow7.lowsP s)).map (Shadow7.b0P s + ·)) ++
  addG ((List.range (Shadow7.lowsP s)).map (Shadow7.b0P s + ·)) ((List.range (Shadow7.lowsP s - 1)).map (1559 + ·)) 1558 ++
  xsG ((List.range (Shadow7.lowsP s)).map (Shadow7.b0P s + ·))

theorem restore_gates (j : Fin 23) :
    Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558 = GateMirror.forward (restoreG (start j)) := by
  have h := lowRest_parts j
  have e : Shadow7.lowRest (start j) = restoreG (start j) ++
      [.pop (Shadow7.b0P (start j) - 1) 1557 1558, .cx (Shadow7.a0P (start j) - 1) 1557, .x 1557] := by
    simp only [Shadow7.lowRest, restoreG, List.append_assoc]
  rw [e, forward_app] at h
  exact (List.append_cancel_right h).symm

/-- The companion region: the magnitude limbs and the carries. -/
def compT (j : Fin 23) (t : Nat) : Prop := (Shadow7.b0P (start j) ≤ t ∧ t ≤ Shadow7.b0P (start j) + 17) ∨ (1559 ≤ t ∧ t ≤ 1575)

theorem erase_dest (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ∀ q ∈ (Companion.erase (fullA j) (fullM j) fullC 1556 1558).map LeaveReadoutFrame.destination, compT j q := by
  have ea : AllAT (fun _ => True) (compT j) (addG (fullM j) fullC 1558 ++
      (List.range 18).map (fun i => Gate.ccx 1556 (Shadow7.a0P (start j) + i) (Shadow7.b0P (start j) + i))) := by
    refine allAT_append (allAT_addG _ _ _ (fun y hy => ⟨trivial, ?_⟩) (fun c hc => ⟨trivial, ?_⟩) trivial)
      (allAT_map _ _ (fun i hi => ok_ccx trivial trivial ?_))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; left; unfold Wire at *; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi; right; unfold Wire at *; omega
    · rw [List.mem_range] at hi; left; unfold Wire at *; omega
  intro q h
  rw [erase_gates, dest_forward] at h
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h
  exact (ea g hg).2

theorem restore_dest (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ∀ q ∈ (Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558).map LeaveReadoutFrame.destination, compT j q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have hL : Shadow7.lowsP (start j) ≤ 11 := by omega
  have ra : AllAT (fun _ => True) (compT j) (restoreG (start j)) := by
    have hb : ∀ y ∈ (List.range (Shadow7.lowsP (start j))).map (Shadow7.b0P (start j) + ·), True ∧ compT j y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
      exact ⟨trivial, Or.inl (by (try unfold Wire at *); omega)⟩
    unfold restoreG
    refine allAT_append (allAT_append (allAT_append (allAT_map _ _ (fun i hi => ok_ccx trivial trivial ?_))
      (allAT_xsG _ (fun x hx => (hb x hx).2))) (allAT_addG _ _ _ hb (fun c hc => ⟨trivial, ?_⟩) trivial))
      (allAT_xsG _ (fun x hx => (hb x hx).2))
    · rw [List.mem_range] at hi; left; unfold Wire at *; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi; right; unfold Wire at *; omega
  intro q h
  rw [restore_gates, dest_forward] at h
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h
  exact (ra g hg).2

/-- Where the mask interior writes: the companions (`compT`) and the body's targets (`midT`). -/
theorem interior_dest (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ∀ q ∈ (interior j).map LeaveReadoutFrame.destination, midT j q ∨ compT j q := by
  intro q hq
  unfold interior at hq
  rw [List.map_append, List.map_append] at hq
  simp only [List.mem_append] at hq
  rcases hq with h | h | h
  · exact Or.inr (erase_dest j h0 (by omega) q h)
  · exact Or.inl (body_dest j h0 (by omega) q h)
  · exact Or.inr (restore_dest j h0 (by omega) q h)

/-- dadon's `MaskThrough.layout`: the interior never writes `a0-1`, `b0-1`, `1557`, `1558`. -/
theorem interior_layout (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ∀ q : Wire, (q = Shadow7.a0P (start j) - 1 ∨ q = Shadow7.b0P (start j) - 1 ∨ q = 1557 ∨ q = 1558) →
      q ∉ (interior j).map LeaveReadoutFrame.destination := by
  intro q hq hm
  have d := interior_dest j h0 (by omega) q hm
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  unfold midT workT compT at d
  unfold Wire at *; omega

/-- The mask wires are distinct and away from the companion flag. -/
theorem mask_wires (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    (Shadow7.a0P (start j) - 1 : Wire) ≠ 1557 ∧ (Shadow7.a0P (start j) - 1 : Wire) ≠ 1558 ∧ (Shadow7.b0P (start j) - 1 : Wire) ≠ 1557 ∧
      (Shadow7.b0P (start j) - 1 : Wire) ≠ 1558 ∧ (Shadow7.a0P (start j) - 1 : Wire) ≠ 1556 ∧ (Shadow7.b0P (start j) - 1 : Wire) ≠ 1556 ∧
      [Shadow7.a0P (start j) - 1, Shadow7.b0P (start j) - 1, (1557:Wire), 1558].Nodup := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or,
    not_false_eq_true]
  unfold Wire at *; omega

/-- dadon's `Leave{s}MaskThrough.released`. -/
theorem maskThrough_released (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m₀ m₁ m₂ : List Bool)
    (x : s.basis 1557 = false) (y : s.basis 1558 = false) :
    let u := run (maskP j) m₀ s
    let v := run (interior j) m₁ u
    run (releaseMaskP j) m₂ v = ⟨v.phase, writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  obtain ⟨n1, n2, n3, n4, -, -, nd⟩ := mask_wires j h0 (by omega)
  intro u v
  have fresh : u = ⟨s.phase, writeBit (writeBit s.basis 1557 (!s.basis (Shadow7.a0P (start j) - 1))) 1558
      (s.basis (Shadow7.b0P (start j) - 1) && !s.basis (Shadow7.a0P (start j) - 1))⟩ := LeaveCompanion.mask_open _ _ 1557 1558 s m₀ nd x y
  have kept (q : Wire) (h : q = Shadow7.a0P (start j) - 1 ∨ q = Shadow7.b0P (start j) - 1 ∨ q = 1557 ∨ q = 1558) :
      v.basis q = u.basis q :=
    LeaveReadoutFrame.preserved _ u m₁ q (interior_layout j h0 (by omega) q h)
  unfold releaseMaskP
  apply LeaveCompanion.mask_close _ _ _ _ _ _ nd
  · rw [kept _ (Or.inr (Or.inr (Or.inl rfl))), kept _ (Or.inl rfl), fresh]
    simp [writeBit, Function.update, n1, n2]
  · rw [kept _ (Or.inr (Or.inr (Or.inr rfl))), kept _ (Or.inr (Or.inl rfl)), kept _ (Or.inr (Or.inr (Or.inl rfl))), fresh]
    simp [writeBit, Function.update, n3, n4]

/-! MaskCut. -/

/-- The state after the input scan and the history flip (the prefix of `entry_core`). -/
theorem head_state (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    let a := step^[15] (reduced (Shadow7.sbP (start j)) 15 z)
    let e := PortalValues.negative sg a.u
    let v := run (GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)))) m s
    (∀ i < 19, v.basis (Shadow7.a0P (start j) - 1 + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j))).testBit i ∧
      v.basis (Shadow7.b0P (start j) - 1 + i) = ((a.u - e.toNat)/2^(Shadow7.sbP (start j))).testBit i) ∧
    (∀ q ∈ 1556::1557::1558::fullC, v.basis q = false) ∧ (∀ p ∈ longPairs j, v.basis p.2 = false) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  intro a e
  have scanActual := inputScan_result j h0 (by omega) s m a.u a.v G sg ready fresh
  dsimp only
  rw [forward_app, run_append, run_take]
  generalize hu : run (GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j)))) m s = u at scanActual ⊢
  generalize m.drop (measurementCount (GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j))))) = t
  generalize hv : run (GateMirror.forward (leaveFix1 (start j) (Shadow7.sbP (start j)))) t u = v
  have hist (q : Wire) (hq : q < start j + 16 ∨ start j + 30 < q) : v.basis q = u.basis q := by
    rw [← hv]; exact LeaveReadoutFrame.preserved _ _ _ _ (flip_dest _ _ q hq)
  have outputBits (i : Nat) (hi : i < 19) :
      v.basis (Shadow7.a0P (start j) - 1 + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j))).testBit i ∧
      v.basis (Shadow7.b0P (start j) - 1 + i) = ((a.u - e.toNat)/2^(Shadow7.sbP (start j))).testBit i := by
    rw [hist _ (Or.inr (by unfold Wire at *; omega)), hist _ (Or.inr (by unfold Wire at *; omega))]
    exact scanActual.2.2.1 i hi
  have scanSites : ∀ q, q ∈ RailPair.sites (scanPairs j) →
      (∃ i, i < 19 ∧ (q = Shadow7.a0P (start j) - 1 + i ∨ q = Shadow7.b0P (start j) - 1 + i)) := by
    intro q hq
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ⟨i, hi, hq⟩
  have same (q : Wire) (h1q : q < start j + 16 ∨ start j + 30 < q) (h2q : q ≠ Shadow7.e0P (start j) + 5)
      (h3q : q ∉ RailPair.sites (scanPairs j)) : v.basis q = s.basis q :=
    (hist _ h1q).trans (scanActual.2.2.2 _ h2q h3q)
  have away (q : Nat) (hq : 1556 ≤ q ∧ q ≤ 1597) : (q < start j + 16 ∨ start j + 30 < q) ∧ q ≠ Shadow7.e0P (start j) + 5 ∧
      q ∉ RailPair.sites (scanPairs j) := by
    refine ⟨Or.inr (by omega), by omega, fun hm => ?_⟩
    obtain ⟨i, hi, h|h⟩ := scanSites q hm <;> unfold Wire at * <;> omega
  refine ⟨outputBits, ?_, ?_⟩
  · intro q h
    have hr : 1556 ≤ q ∧ q ≤ 1597 := by
      have h' := h
      simp only [List.mem_cons, fullC, List.mem_map, List.mem_range] at h'
      rcases h' with e | e | e | ⟨a, ha, e⟩
      · rw [e]; exact ⟨by decide, by decide⟩
      · rw [e]; exact ⟨by decide, by decide⟩
      · rw [e]; exact ⟨by decide, by decide⟩
      · rw [← e]; constructor <;> ((try unfold Wire at *); omega)
    obtain ⟨a1, a2, a3⟩ := away q hr
    rw [same q a1 a2 a3]; exact scratch _ h
  · intro p h
    have hr : 1556 ≤ p.2 ∧ p.2 ≤ 1597 := by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h; rw [List.mem_range] at hi; dsimp only; unfold Wire at *; omega
    obtain ⟨a1, a2, a3⟩ := away p.2 hr
    rw [same _ a1 a2 a3]; exact temp _ h

/-- dadon's `Leave{s}MaskCut.result`. -/
theorem maskCut_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (z : SkywalkNat.State) (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let v := run (fullProgram j) m s
    v.basis (Shadow7.b0P (start j) - 1) = decide (2^(Shadow7.sbP (start j)) ≤ mag % (2*2^(Shadow7.sbP (start j)))) ∧
    ∀ mm, run (releaseMaskP j) mm v = ⟨v.phase, writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  obtain ⟨n1, n2, n3, n4, n5, n6, nd⟩ := mask_wires j h0 (by omega)
  have hd := head_state j h0 (by omega) s m z G sg ready fresh scratch temp
  dsimp only at hd
  generalize hv0 : run (GateMirror.forward (leaveFix0 (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)))) m s
    = v0 at hd
  obtain ⟨bits, clean, temps⟩ := hd
  have eq : run (beforeOpen j) m s =
      ⟨v0.phase, writeBit v0.basis 1556 (v0.basis 1556 ^^ ((PortalAnd.digits (Shadow7.b0P (start j) - 1) (longPairs j)).any v0.basis))⟩ := by
    rw [beforeOpen, run_append, run_take, hv0, long_run j h0 (by omega) v0 _ temps]
  generalize he : run (beforeOpen j) m s = e at eq
  have keep (q : Wire) (neq : q ≠ 1556) : e.basis q = v0.basis q := by rw [eq]; simp [writeBit, neq]
  have x : e.basis 1557 = false := (keep _ (by decide)).trans (clean _ (by simp))
  have y : e.basis 1558 = false := (keep _ (by decide)).trans (clean _ (by simp))
  have maskOK : (Shadow7.b0P (start j) - 1 : Wire) ∉ (maskP j).map LeaveReadoutFrame.destination := by
    simp only [maskP, List.map_cons, List.map_nil, LeaveReadoutFrame.destination, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨n3, n3, n4⟩
  generalize hn : m.drop (measurementCount (beforeOpen j)) = n
  have bit (w' : List Bool) : (run (interior j) w' (run (maskP j) n e)).basis (Shadow7.b0P (start j) - 1) = e.basis (Shadow7.b0P (start j) - 1) :=
    (LeaveReadoutFrame.preserved _ _ _ _ (interior_layout j h0 (by omega) _ (Or.inr (Or.inl rfl)))).trans
      (LeaveReadoutFrame.preserved (maskP j) e n _ maskOK)
  have raw : e.basis (Shadow7.b0P (start j) - 1) =
      (((step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u -
        (PortalValues.negative sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u).toNat) / 2^(Shadow7.sbP (start j))).testBit 0 := by
    have b0 := (bits 0 (by decide)).2
    rw [Nat.add_zero] at b0
    rw [keep _ n6, b0]
  have tr := LeaveRestoreTruth.truth_shadow7 (Shadow7.sbP (start j)) z small.1 sg
  dsimp only
  rw [full_split j h0 (by omega), run_append, run_take, run_append, run_take, he, hn]
  constructor
  · rw [bit, raw, LeaveCompanion.thresholdBit _ _ (Nat.two_pow_pos _), tr.2.2.2, tr.2.2.1]
  · exact fun mm => maskThrough_released j h0 (by omega) e n _ mm x y

/-! BeforeStore. -/

theorem live_away (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) (hi : i < Shadow7.wpP (start j) + 15) :
    (live j i : Wire) ≠ 1556 ∧ (live j i : Wire) ≠ 1557 ∧ (live j i : Wire) ≠ 1558 := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have b := Shadow7.bank_cases w1 w2 hi
  unfold live; split <;> unfold Wire at * <;> omega

theorem smallM_away (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ∀ q ∈ smallM j, q ≠ 1556 ∧ q ≠ 1557 ∧ q ≠ 1558 := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
  unfold Wire at *; omega

theorem flagTargets_away (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ∀ q ∈ flagTargets j, q ≠ 1557 ∧ q ≠ 1558 := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  intro q hq
  simp only [flagTargets, List.map_append, List.mem_append, List.mem_map] at hq
  rcases hq with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have sc := Shadow7.storeW_cases (start_win j h0 (by omega)).1 (start_win j h0 (by omega)).2 (i+1)
    dsimp only; unfold Wire at *; omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
    dsimp only; unfold Wire at *; omega

/-- dadon's `Leave{s}BeforeStore.program` (cut 2788 at 225). -/
def beforeStoreProgram (j : Fin 23) : Program :=
  fullProgram j ++ (releaseMaskP j ++ GateMirror.forward (Shadow7.leaveStoreMapped (start j)))

/-- dadon's `Leave{s}BeforeStore.finalBits`. -/
def finalBits (v : BasisState) (f u : Bool) := writeBit (writeBit (writeBit v 1557 f) 1558 u) 1556 false

/-- dadon's `Leave{s}BeforeStore.result`. -/
theorem beforeStore_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (z : SkywalkNat.State) (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ watched j, s.basis q = false)
    (par : oddRead j s.basis = oddBits (letters 15 (reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (swaps j i) = decide (i = key (actualMode (Shadow7.sbP (start j)) z)))
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let f := decide (Shadow.far (Shadow7.sbP (start j + 15)) 15 a)
    let v := run (fullProgram j) m s
    let out := run (beforeStoreProgram j) m s
    out.phase = s.phase ∧ out.basis 1556 = false ∧ out.basis 1557 = f ∧
      out.basis 1558 = (f && decide (2^(Shadow7.sbP (start j + 15)) ≤ a.u)) ∧
      regValue (smallM j) out.basis = (mag/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j)) ∧
      (∀ i < Shadow7.wpP (start j) + 15, out.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      ∀ q, q ≠ 1556 → q ≠ 1557 → q ≠ 1558 → out.basis q = v.basis q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  obtain ⟨n1, n2, n3, n4, n5, n6, nd⟩ := mask_wires j h0 (by omega)
  have ar := fullArithmetic_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events
  have clears := flagScratch_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events
  have mask := maskCut_result j h0 (by omega) s m z G sg small ready fresh scratch temp
  dsimp only at ar mask
  generalize hv : run (fullProgram j) m s = v at ar clears mask
  generalize hn : m.drop (measurementCount (fullProgram j)) = n
  have closed : run (releaseMaskP j) n v = ⟨v.phase, writeBit (writeBit v.basis 1557 false) 1558 false⟩ := mask.2 n
  generalize hu : run (releaseMaskP j) n v = u at closed
  have kept (q : Wire) (h : q ≠ 1557 ∧ q ≠ 1558) : u.basis q = v.basis q := by rw [closed]; simp [writeBit, h.1, h.2]
  have bits : ∀ i < Shadow7.wpP (start j) + 15, u.basis (live j i) = (TrueMiddle.F j z).testBit i := fun i h =>
    (kept _ ⟨(live_away j h0 (by omega) i h).2.1, (live_away j h0 (by omega) i h).2.2⟩).trans (ar.2.2.2 i h)
  have upper : regValue (smallM j) u.basis = regValue (smallM j) v.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h => kept _ ⟨(smallM_away j h0 (by omega) _ h).2.1, (smallM_away j h0 (by omega) _ h).2.2⟩)
  have hL : 3 ≤ Shadow7.lowsP (start j) ∧ Shadow7.lowsP (start j) ≤ Shadow7.wpP (start j) + 15 := by omega
  have scan : regValue (scanned j) u.basis = high (Shadow7.sbP (start j + 15)) 15 (step^[15] z) := by
    rw [outputScanned j h0 (by omega) u _ bits]
    have fit : TrueMiddle.F j z / 2^(Shadow7.lowsP (start j) - 3) < 2^(Shadow7.wpP (start j) + 15 - Shadow7.lowsP (start j) + 3) := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      rw [← Nat.pow_add, show Shadow7.wpP (start j) + 15 - Shadow7.lowsP (start j) + 3 + (Shadow7.lowsP (start j) - 3) = Shadow7.wpP (start j) + 15 by omega]
      exact bound
    rw [Nat.mod_eq_of_lt fit]
    exact nextFlag_value j h0 (by omega) z
  have cleanAt (q : Wire) (h : q ∈ flagTargets j) : u.basis q = false :=
    (kept _ (flagTargets_away j h0 (by omega) _ h)).trans (clears _ h)
  have bit : (PortalValues.negative sg (step^[15] z).u).toNat ≤ 1 := by cases PortalValues.negative sg (step^[15] z).u <;> decide
  have two : 2 * 2^(Shadow7.sbP (start j)) = 2^(Shadow7.sbP (start j) + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have tail := tailFlags_result j h0 (by omega) (step^[15] z) u (n.drop (measurementCount (releaseMaskP j)))
    (PortalValues.negative sg (step^[15] z).u).toNat bit nextSmall.1
    (by rw [closed]; simp [writeBit]) (by rw [closed]; simp [writeBit]) scan
    (fun p h => cleanAt _ (List.mem_map.mpr ⟨p, List.mem_append_left _ h, rfl⟩))
    (fun p h => cleanAt _ (List.mem_map.mpr ⟨p, List.mem_append_right _ h, rfl⟩))
    ((kept _ (by decide)).trans ar.2.2.1) ((kept _ ⟨n3, n4⟩).trans mask.1)
    (by rw [upper, ar.2.1, two, smallM_length])
  dsimp only at tail
  dsimp only
  rw [beforeStoreProgram, run_append, run_take, run_append, run_take, hv, hn, hu, tail]
  generalize hf : decide (Shadow.far (Shadow7.sbP (start j + 15)) 15 (step^[15] z)) = f
  generalize hside : (f && decide (2^(Shadow7.sbP (start j + 15)) ≤ (step^[15] z).u)) = side
  have frame (q : Wire) (hx : q ≠ 1556) (hy : q ≠ 1557) (hz : q ≠ 1558) :
      writeBit (writeBit (writeBit u.basis 1557 f) 1558 side) 1556 false q = v.basis q := by
    simpa [writeBit, hx, hy, hz] using kept q ⟨hy, hz⟩
  refine ⟨(show u.phase = v.phase by rw [closed]).trans ar.1, ?_, ?_, ?_, ?_, ?_, frame⟩
  · simp [writeBit]
  · simp [writeBit]
  · simp [writeBit]
  · exact ((regValue_eq_iff _ _ _).mpr (fun q h => frame q (smallM_away j h0 (by omega) _ h).1 (smallM_away j h0 (by omega) _ h).2.1
      (smallM_away j h0 (by omega) _ h).2.2)).trans ar.2.1
  · intro i h
    exact (frame _ (live_away j h0 (by omega) i h).1 (live_away j h0 (by omega) i h).2.1 (live_away j h0 (by omega) i h).2.2).trans (ar.2.2.2 i h)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- The head of the leave is the entry followed by the body. -/
theorem head_eq (j : Fin 23) : entryOps (start j) ++ bodyOps j = Shadow7.leaveHeadOps (start j) := by
  simp only [entryOps, bodyOps, fullPrefix, workOps, middleOps, Shadow7.leaveHeadOps, List.append_assoc]

namespace CoreCheckpoint

/-- dadon's `Leave{s}CoreCheckpoint.program` (`leave.take 2260`). -/
abbrev program (j : Fin 23) : Program := GateMirror.forward (Shadow7.leaveHeadOps (start j))
/-- dadon's `rawSites`: the pool below the anchored block and the scratch above it. -/
def rawSites (j : Fin 23) : List Wire :=
  List.range' 1613 (Shadow7.e0P (start j) - 1613) ++ List.range' (Shadow7.e0P (start j) + 8) (min 1813 (2055 - start j) - (Shadow7.e0P (start j) + 8))
abbrev magSites (j : Fin 23) : List Wire := LeaveJ7.fullM j
def targets (j : Fin 23) : List Wire :=
  List.range' 1559 39 ++ (List.finRange 18).map (fun i => (LeaveJ7.row j i).free) ++ rawSites j ++ magSites j

theorem raw_range (j : Fin 23) (q : Nat) (hq : q ∈ rawSites j) :
    (1613 ≤ q ∧ q < Shadow7.e0P (start j)) ∨ (Shadow7.e0P (start j) + 8 ≤ q ∧ q ≤ 1812 ∧ q + start j ≤ 2054) := by
  simp only [rawSites, List.mem_append, List.mem_range'_1] at hq
  omega

/-- dadon's `Leave{s}CoreCheckpoint.result`. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z))) :
    let out := run (program j) m s
    (∀ i : Fin 39, out.basis (1559 + i.val) = false) ∧
    (∀ i : Fin 18, out.basis (LeaveJ7.row j i).free = false) ∧
    (∀ q ∈ rawSites j, out.basis q = s.basis q) ∧ (∀ q ∈ magSites j, out.basis q = false) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have front := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
  have used := full_routed j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  generalize ha : run (GateMirror.forward (entryOps (start j))) m s = a at front used
  generalize hn : m.drop (measurementCount (GateMirror.forward (entryOps (start j)))) = n at used
  have other (q : Nat) (hq : (1613 ≤ q ∧ q < Shadow7.e0P (start j)) ∨ (Shadow7.e0P (start j) + 8 ≤ q ∧ q ≤ 1812) ∨
      (Shadow7.b0P (start j) ≤ q ∧ q < Shadow7.b0P (start j) + 18)) :
      (run (GateMirror.forward (bodyOps j)) n a).basis q = a.basis q := by
    have notWire : HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q := by
      intro i hi e'; have b := Shadow7.bank_cases w1 w2 hi; unfold Wire at *; omega
    have notCols : ∀ c ∈ cols j, q ≠ c.shadow ∧ q ≠ c.tube := by
      intro c hc; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
      exact ⟨by dsimp only; unfold Wire at *; omega, by dsimp only; unfold Wire at *; omega⟩
    rw [used.2.2.2.2 q notWire notCols, cleared, if_neg (by omega)]
    exact prefix_keep j h0 (by omega) q (by omega) a n
  dsimp only
  rw [program, ← head_eq, forward_app, run_append, run_take, ha, hn]
  refine ⟨used.2.2.2.1, used.2.2.1, ?_, ?_⟩
  · intro q hq
    have r := raw_range j q hq
    rw [other q (by omega), ← ha]
    exact entry_keep j h0 (by omega) q (by omega) s m
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    have e : (run (GateMirror.forward (bodyOps j)) n a).basis (Shadow7.b0P (start j) + i) = a.basis (Shadow7.b0P (start j) + i) :=
      other (Shadow7.b0P (start j) + i) (by omega)
    exact e.trans ((regValue_zero _ _).mp front.2.1 _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))

/-- dadon's `Leave{s}CoreCheckpoint.oracle`: the five wires the Mirror asks to be clean after the head. -/
theorem oracle (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s out : State)
    (scr : ∀ i : Fin 39, out.basis (1559 + i.val) = false)
    (raw : ∀ q ∈ rawSites j, out.basis q = s.basis q) (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false) :
    ∀ q ∈ coreW, out.basis q = false := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have inRaw : ∀ q : Nat, 1613 ≤ q → q ≤ 1614 → q ∈ rawSites j := by
    intro q a b
    simp only [rawSites, List.mem_append, List.mem_range'_1]
    left; omega
  have inCarries : ∀ k : Nat, 15 ≤ k → k ≤ 16 → (1598 + k : Nat) ∈ carries j := by
    intro k a b
    simp only [carries, List.mem_map, List.mem_range]
    exact ⟨k, by omega, by have p := Shadow7.pool_cases (i := k) w1 w2; unfold Wire at *; omega⟩
  intro q hq
  rw [mem_coreW] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl
  · exact scr ⟨1, by decide⟩
  · exact scr ⟨17, by decide⟩
  · exact scr ⟨37, by decide⟩
  · exact (raw 1613 (inRaw 1613 (by decide) (by decide))).trans (clean 1613 (inCarries 15 (by decide) (by decide)))
  · exact (raw 1614 (inRaw 1614 (by decide) (by decide))).trans (clean 1614 (inCarries 16 (by decide) (by decide)))

end CoreCheckpoint

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

namespace Routed
/-- dadon's `Leave{s}Routed.body`. -/
abbrev body (j : Fin 23) : Program := GateMirror.forward (LeaveJ7.bodyOps j)
end Routed

namespace FullArithmetic
/-- dadon's `Leave{s}FullArithmetic.program`. -/
abbrev program (j : Fin 23) : Program := LeaveJ7.fullProgram j
theorem shape (j : Fin 23) : program j = GateMirror.forward (LeaveJ7.entryOps (start j)) ++ (Routed.body j ++
    Companion.restore (LeaveJ7.smallA j) (LeaveJ7.smallM j) (LeaveJ7.smallC j) 1556 1558) := by
  simp only [program, LeaveJ7.fullProgram, forward_app, List.append_assoc]
theorem restoreShape (j : Fin 23) :
    program j = CoreCheckpoint.program j ++ Companion.restore (LeaveJ7.smallA j) (LeaveJ7.smallM j) (LeaveJ7.smallC j) 1556 1558 := by
  simp only [program, LeaveJ7.fullProgram, CoreCheckpoint.program, head_eq]
end FullArithmetic

namespace BeforeStore
/-- dadon's `Leave{s}BeforeStore.program`. -/
abbrev program (j : Fin 23) : Program :=
  LeaveJ7.fullProgram j ++ (LeaveJ7.releaseMaskP j ++ GateMirror.forward (Shadow7.leaveStoreMapped (start j)))

/-- dadon's `Leave{s}BeforeStore.result`. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z)))
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let far := decide (Shadow.far (Shadow7.sbP (start j + 15)) 15 a)
    let v := run (FullArithmetic.program j) m s
    let out := run (program j) m s
    out.phase = s.phase ∧ out.basis 1556 = false ∧ out.basis 1557 = far ∧
      out.basis 1558 = (far && decide (2^(Shadow7.sbP (start j + 15)) ≤ a.u)) ∧
      regValue (LeaveJ7.smallM j) out.basis = (mag/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j)) ∧
      (∀ i < Shadow7.wpP (start j) + 15, out.basis (LeaveJ7.live j i) = (LeaveJ7.TrueMiddle.F j z).testBit i) ∧
      ∀ q, q ≠ 1556 → q ≠ 1557 → q ≠ 1558 → out.basis q = v.basis q :=
  beforeStore_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
    nextSmall bound
end BeforeStore

namespace StoreMapped
/-- dadon's `Leave{s}StoreMapped.program` (the leave up to the low close). -/
abbrev program (j : Fin 23) : Program := BeforeStore.program j ++ GateMirror.forward (Shadow7.leaveLowClose (start j))
theorem program_eq (j : Fin 23) :
    program j = GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j)) := by
  simp only [program, BeforeStore.program, LeaveJ7.fullProgram, Shadow7.leaveMidOps, forward_app, LeaveJ7.lowRest_parts, ← head_eq,
    List.append_assoc]
end StoreMapped

/-- The low close writes only the history letters and the low columns: never wire 1556. -/
theorem lowClose_keeps (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    AllAT (fun _ => True) (fun t => t ≠ 1556) (Shadow7.leaveLowClose (start j)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  simp only [Shadow7.leaveLowClose]
  refine allAT_append (allAT_append (allAT_xsG _ (fun x hx => ?_))
      (allAT_map _ _ (fun i hi => ok_cx (A := fun _ => True) (T := fun t => t ≠ 1556) trivial ?_)))
    (allAT_flatMap _ _ (fun i hi => allAT_cswapG (A := fun _ => True) (T := fun t => t ≠ 1556) _ _ _ trivial
      ⟨trivial, ?_⟩ ⟨trivial, ?_⟩))
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; rw [List.mem_range] at hi
    show start j + 16 + i ≠ 1556
    omega
  · rw [List.mem_range] at hi
    show Shadow7.b0P (start j) - 1 + i ≠ 1556
    omega
  · rw [List.mem_range] at hi
    show Shadow7.b0P (start j) - 1 + i ≠ 1556
    omega
  · rw [List.mem_range] at hi
    show Shadow7.a0P (start j) - 1 + i ≠ 1556
    omega

namespace Roundtrip
/-- dadon's `Leave{s}Roundtrip.result`. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m n : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z)))
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15))
    (phase : ∀ o, (run (Shadow7.leaveP j) o s).phase = s.phase)
    (initial : ∀ q, 1556 ≤ q → q < Shadow7.e0P (start j) → s.basis q = false)
    (extra : ∀ q, Shadow7.e0P (start j) + 10 ≤ q → q < Shadow7.e0P (start j) + 10 + (Shadow7.wpP (start j) - 1 - (Shadow7.e0P (start j) - 1598)) →
      s.basis q = false) :
    run (Shadow7.leaveInvP j) n (run (Shadow7.leaveP j) m s) = s := by
  have atCore := CoreCheckpoint.result j h0 (by omega) s [] z G sg small ready fresh scratch temp odd room clean padding bank zero
    par mode events
  have core := CoreCheckpoint.oracle j h0 (by omega) s _ atCore.1 atCore.2.2.1 clean
  have bs := beforeStore_result j h0 (by omega) s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode
    events nextSmall bound
  have post : (run (GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j))) [] s).basis 1556 = false := by
    have safe : (1556 : Wire) ∉ (GateMirror.forward (Shadow7.leaveLowClose (start j))).map LeaveReadoutFrame.destination := by
      intro hm
      rw [dest_forward] at hm
      obtain ⟨g, hg, e⟩ := List.mem_map.mp hm
      exact (lowClose_keeps j h0 (by omega) g hg).2 e
    rw [← StoreMapped.program_eq j, StoreMapped.program, run_append, run_take, LeaveReadoutFrame.preserved _ _ _ _ safe]
    exact bs.2.1
  exact Shadow7.leave_inverts j h0 (by omega) s phase initial extra core post m n
end Roundtrip

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector RailPair
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

namespace Close

/-- dadon's `Leave{s}Close.history`. -/
abbrev history (j : Fin 23) : List Wire := LeaveJ7.history j
/-- dadon's `Leave{s}Close.low`: the low columns, A side and B side. -/
def low (j : Fin 23) : List (Wire × Wire) :=
  (List.range (Shadow7.lowsP (start j) + 1)).map (fun i => (Shadow7.a0P (start j) - 1 + i, Shadow7.b0P (start j) - 1 + i))
/-- dadon's `Leave{s}Close.events`. -/
def events (j : Fin 23) : List (Wire × Wire) :=
  [(LeaveJ7.swaps j 0, 1556), (LeaveJ7.swaps j 1, 1559), (LeaveJ7.swaps j 2, 1560), (LeaveJ7.swaps j 3, 1561), (LeaveJ7.swaps j 4, 1562)]
/-- dadon's `Leave{s}Close.afterLow`. -/
abbrev afterLow (j : Fin 23) : Program := GateMirror.forward (Shadow7.leaveClose (start j))

/-- dadon's `Leave{s}Close.lowShape`. -/
theorem lowShape (j : Fin 23) : GateMirror.forward (Shadow7.leaveLowClose (start j)) =
    notRegister (history j) ++ store (start j + 30) (Shadow7.e0P (start j) + 5) (low j) [] := by
  have e1 : GateMirror.forward ((List.range (Shadow7.lowsP (start j) + 1)).map
      (fun i => Gate.cx (Shadow7.e0P (start j) + 5) (Shadow7.b0P (start j) - 1 + i))) =
      signComplement (Shadow7.e0P (start j) + 5) ((low j).map Prod.snd) := by
    simp only [GateMirror.forward, signComplement, low, List.map_map]; rfl
  have e2 : GateMirror.forward ((List.range (Shadow7.lowsP (start j) + 1)).flatMap
      (fun i => cswapG (start j + 30) (Shadow7.b0P (start j) - 1 + i) (Shadow7.a0P (start j) - 1 + i))) =
      exchange (start j + 30) (low j) := by
    simp only [GateMirror.forward, exchange, low, List.map_flatMap, List.flatMap_map]; rfl
  simp only [Shadow7.leaveLowClose, forward_app, forward_xsG', e1, e2, store, transfer, List.flatMap_nil, List.nil_append,
    List.append_assoc]
  rfl

theorem mem_low_sites (j : Fin 23) (q : Wire) : q ∈ RailPair.sites (low j) ↔
    ∃ i, i < Shadow7.lowsP (start j) + 1 ∧ (q = Shadow7.a0P (start j) - 1 + i ∨ q = Shadow7.b0P (start j) - 1 + i) := by
  simp only [RailPair.sites, low, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · rintro ⟨p, ⟨i, hi, rfl⟩, h⟩; exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨_, ⟨i, hi, rfl⟩, h⟩

theorem low_fst (j : Fin 23) : (low j).map Prod.fst = (List.range (Shadow7.lowsP (start j) + 1)).map (fun i => (Shadow7.a0P (start j) - 1 + i : Wire)) := by
  simp only [low, List.map_map]; rfl
theorem low_snd (j : Fin 23) : (low j).map Prod.snd = (List.range (Shadow7.lowsP (start j) + 1)).map (fun i => (Shadow7.b0P (start j) - 1 + i : Wire)) := by
  simp only [low, List.map_map]; rfl

theorem low_fst_nodup (j : Fin 23) : ((low j).map Prod.fst).Nodup := by
  rw [low_fst]
  refine List.Nodup.map_on (fun x _ y _ e => ?_) List.nodup_range
  have e' : Shadow7.a0P (start j) - 1 + x = Shadow7.a0P (start j) - 1 + y := e
  (try unfold Wire at *); omega
theorem low_snd_nodup (j : Fin 23) : ((low j).map Prod.snd).Nodup := by
  rw [low_snd]
  refine List.Nodup.map_on (fun x _ y _ e => ?_) List.nodup_range
  have e' : Shadow7.b0P (start j) - 1 + x = Shadow7.b0P (start j) - 1 + y := e
  (try unfold Wire at *); omega

/-- dadon's `StoreGeometry` of the low close. -/
theorem low_geometry (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    StoreGeometry (start j + 30) (Shadow7.e0P (start j) + 5) (low j) [] := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have away : ∀ q : Nat, (q = start j + 30 ∨ q = Shadow7.e0P (start j) + 5) → (q : Wire) ∉ RailPair.sites (low j) := by
    intro q hq hm
    obtain ⟨i, hi, e⟩ := (mem_low_sites j q).mp hm
    have e' : q = Shadow7.a0P (start j) - 1 + i ∨ q = Shadow7.b0P (start j) - 1 + i := e
    omega
  have perm : (RailPair.sites (low j)).Perm ((low j).map Prod.fst ++ (low j).map Prod.snd) := sites_perm (low j)
  have sitesNodup : (RailPair.sites (low j)).Nodup := by
    rw [perm.nodup_iff]
    refine List.nodup_append.mpr ⟨low_fst_nodup j, low_snd_nodup j, fun a ha b hb e => ?_⟩
    rw [low_fst] at ha; rw [low_snd] at hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_range] at hx hy
    have e' : Shadow7.a0P (start j) - 1 + x = Shadow7.b0P (start j) - 1 + y := e
    omega
  refine ⟨List.nodup_cons.mpr ⟨away _ (Or.inl rfl), sitesNodup⟩, List.nodup_nil, ?_, by simp [RailPair.sites],
    away _ (Or.inr rfl), by simp [RailPair.sites], fun q _ => by simp [RailPair.sites], low_snd_nodup j, ?_⟩
  · show Shadow7.e0P (start j) + 5 ≠ start j + 30
    omega
  · intro p hp hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    rw [low_snd] at hm
    obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
    rw [List.mem_range] at hx hy
    have e' : Shadow7.b0P (start j) - 1 + y = Shadow7.a0P (start j) - 1 + x := e
    omega

/-- dadon's `Leave{s}Close.lowResult`. -/
theorem lowResult (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) :
    let h := fun q => if q ∈ history j then !s.basis q else s.basis q
    let t := run (GateMirror.forward (Shadow7.leaveLowClose (start j))) m s
    t.phase = s.phase ∧ (∀ q, q ∉ RailPair.sites (low j) → t.basis q = h q) ∧
      ∀ p ∈ low j, t.basis p.1 = (if h (start j + 30) then h p.2 ^^ h (Shadow7.e0P (start j) + 5) else h p.1) ∧
        t.basis p.2 = (if h (start j + 30) then h p.1 else h p.2 ^^ h (Shadow7.e0P (start j) + 5)) := by
  dsimp only
  rw [lowShape, run_append, run_take, notRegister_correct (history j) (history_nodup j)]
  have act := store_run (start j + 30) (Shadow7.e0P (start j) + 5) (low j) [] (low_geometry j h0 (by omega))
    ⟨s.phase, fun q => if q ∈ history j then !s.basis q else s.basis q⟩
    (m.drop (measurementCount (notRegister (history j)))) (by simp)
  exact ⟨act.1, fun q no => act.2.1 q no (by simp [RailPair.sites]), act.2.2.2⟩

end Close

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}StoreCoordinates.result`, on `beforeStoreProgram`. -/
theorem storeCoordinates_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (z : SkywalkNat.State) (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ watched j, s.basis q = false)
    (par : oddRead j s.basis = oddBits (letters 15 (reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (swaps j i) = decide (i = key (actualMode (Shadow7.sbP (start j)) z)))
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let out := run (beforeStoreProgram j) m s
    out.basis (Shadow7.e0P (start j) + 5) = PortalValues.negative sg a.u ∧ (∀ q ∈ history j, out.basis q = !s.basis q) ∧
    (∀ i : Fin (Shadow7.lowsP (start j) + 1), out.basis (Shadow7.a0P (start j) - 1 + i.val) = (a.u+a.v).testBit (Shadow7.sbP (start j) + i.val) ∧
        out.basis (Shadow7.b0P (start j) - 1 + i.val) = mag.testBit (Shadow7.sbP (start j) + i.val)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have src := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
  have par0 := entry_parity j h0 (by omega) s m
  have stored := beforeStore_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound
  have lowMag := (maskCut_result j h0 (by omega) s m z G sg small ready fresh scratch temp).1
  have truth := LeaveShadowRails.retainedLow_shadow7 (Shadow7.sbP (start j)) z small.1 sg
  dsimp only at src stored lowMag truth ⊢
  generalize hen : run (GateMirror.forward (entryOps (start j))) m s = en at src par0
  have afterEntry (q : Nat) (hm : ¬ midT j q) (hc : ¬ compT j q) : (run (fullProgram j) m s).basis q = en.basis q := by
    rw [fullProgram, forward_app, List.append_assoc, run_append, run_take, run_append, run_take, hen,
      LeaveReadoutFrame.preserved _ _ _ _ (fun h => hc (restore_dest j h0 (by omega) q h)),
      LeaveReadoutFrame.preserved _ _ _ _ (fun h => hm (body_dest j h0 (by omega) q h))]
  have raw (q : Nat) (h6 : q ≠ 1556) (h7 : q ≠ 1557) (h8 : q ≠ 1558) (hm : ¬ midT j q) (hc : ¬ compT j q) :
      (run (beforeStoreProgram j) m s).basis q = en.basis q :=
    (stored.2.2.2.2.2.2 q h6 h7 h8).trans (afterEntry q hm hc)
  refine ⟨?_, ?_, ?_⟩
  · rw [raw (Shadow7.e0P (start j) + 5) (by omega) (by omega) (by omega) (by unfold midT workT; omega) (by unfold compT; omega)]
    exact src.2.2.1.trans truth.1.symm
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    have e : (run (beforeStoreProgram j) m s).basis (start j + 16 + i) = en.basis (start j + 16 + i) :=
      raw (start j + 16 + i) (by omega) (by omega) (by omega) (by unfold midT workT; omega) (by unfold compT; omega)
    unfold LeaveSelector.parityBits oddRead at par0
    have pe := (List.map_inj_left.mp par0) i (List.mem_range.mpr hi)
    exact e.trans pe
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      have a0 := src.2.2.2.2.2.1 0 (by decide)
      rw [Nat.testBit_div_two_pow] at a0
      have same := congrArg (fun n : Nat => n.testBit (Shadow7.sbP (start j))) truth.2.1
      simp only [Nat.testBit_mod_two_pow, Nat.lt_succ_self, decide_true, Bool.true_and] at same
      have bit := LeaveCompanion.thresholdBit ((step^[15] z).u - (PortalValues.negative sg (step^[15] z).u).toNat)
        (2^(Shadow7.sbP (start j))) (Nat.two_pow_pos _)
      rw [Nat.testBit_div_two_pow] at bit
      simp only [Nat.zero_add, Nat.add_zero] at a0 bit ⊢
      constructor
      · rw [raw (Shadow7.a0P (start j) - 1) (by omega) (by omega) (by omega) (by unfold midT workT; omega) (by unfold compT; omega)]
        exact a0.trans same.symm
      · have b6 : Shadow7.b0P (start j) - 1 ≠ 1556 := by omega
        have b7 : Shadow7.b0P (start j) - 1 ≠ 1557 := by omega
        have b8 : Shadow7.b0P (start j) - 1 ≠ 1558 := by omega
        rw [stored.2.2.2.2.2.2 (Shadow7.b0P (start j) - 1) b6 b7 b8]
        exact lowMag.trans bit.symm
    | succ k =>
      have hk' : k < Shadow7.lowsP (start j) := by omega
      have pos := stored.2.2.2.2.2.1 k (by omega)
      have lk : live j k = Shadow7.a0P (start j) + k := by unfold live; rw [if_pos hk']
      have signedBit := HighBankAdjust.bit_read (smallM j) k (run (beforeStoreProgram j) m s).basis
        (by rw [smallM_length]; exact hk')
      have gk : (smallM j).getD k 0 = Shadow7.b0P (start j) + k := by
        simp [smallM, List.getD_eq_getElem?_getD, hk']
      rw [gk, stored.2.2.2.2.1, Nat.testBit_mod_two_pow, decide_eq_true hk', Bool.true_and, Nat.testBit_div_two_pow]
        at signedBit
      rw [lk] at pos
      unfold TrueMiddle.F HighBankSum.total at pos
      rw [Nat.testBit_div_two_pow] at pos
      have ia : Shadow7.a0P (start j) - 1 + (k+1) = Shadow7.a0P (start j) + k := by omega
      have ib : Shadow7.b0P (start j) - 1 + (k+1) = Shadow7.b0P (start j) + k := by omega
      have ix : Shadow7.sbP (start j) + (k+1) = k + (Shadow7.sbP (start j) + 1) := by omega
      show (run (beforeStoreProgram j) m s).basis (Shadow7.a0P (start j) - 1 + (k+1)) = _ ∧
        (run (beforeStoreProgram j) m s).basis (Shadow7.b0P (start j) - 1 + (k+1)) = _
      rw [ia, ib, ix]
      exact ⟨pos, signedBit⟩

/-- The low close on the stored coordinates (dadon's private `store` of `Leave{s}StoreMapped`). -/
theorem lowClose_store (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s v : State) (m : List Bool) (G sign : Bool)
    (sum mag : Nat) (previous : s.basis (start j + 30) = G) (hist : ∀ q ∈ history j, v.basis q = !s.basis q)
    (signed : v.basis (Shadow7.e0P (start j) + 5) = sign)
    (words : ∀ i : Fin (Shadow7.lowsP (start j) + 1), v.basis (Shadow7.a0P (start j) - 1 + i.val) = sum.testBit (Shadow7.sbP (start j) + i.val) ∧
      v.basis (Shadow7.b0P (start j) - 1 + i.val) = mag.testBit (Shadow7.sbP (start j) + i.val)) :
    let out := run (GateMirror.forward (Shadow7.leaveLowClose (start j))) m v
    out.phase = v.phase ∧ (∀ q ∈ history j, out.basis q = s.basis q) ∧
    (∀ i : Fin (Shadow7.lowsP (start j) + 1), let pos := sum.testBit (Shadow7.sbP (start j) + i.val)
        let neg := mag.testBit (Shadow7.sbP (start j) + i.val) ^^ sign
        out.basis (Shadow7.a0P (start j) - 1 + i.val) = (if G then neg else pos) ∧
        out.basis (Shadow7.b0P (start j) - 1 + i.val) = (if G then pos else neg)) ∧
    ∀ q, q ∉ RailPair.sites (Close.low j) → q ∉ history j → out.basis q = v.basis q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have wrote := Close.lowResult j h0 (by omega) v m
  dsimp only at wrote ⊢
  have inHist : (start j + 30 : Wire) ∈ history j := List.mem_map.mpr ⟨14, List.mem_range.mpr (by decide), rfl⟩
  have notHist (q : Nat) (hq : q < start j + 16 ∨ start j + 30 < q) : (q : Wire) ∉ history j := by
    intro hm
    obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have e' : start j + 16 + i = q := e
    omega
  have sep : ∀ a ∈ history j, a ∉ RailPair.sites (Close.low j) := by
    intro a ha hm
    obtain ⟨i, hi, e⟩ := List.mem_map.mp ha; rw [List.mem_range] at hi
    obtain ⟨k, hk, e2⟩ := (Close.mem_low_sites j a).mp hm
    have e' : start j + 16 + i = a := e
    have e2' : (a : Nat) = Shadow7.a0P (start j) - 1 + k ∨ (a : Nat) = Shadow7.b0P (start j) - 1 + k := e2
    (try unfold Wire at *); omega
  refine ⟨wrote.1, ?_, ?_, ?_⟩
  · intro q hq
    rw [wrote.2.1 q (sep q hq), if_pos hq, hist q hq, Bool.not_not]
  · intro i
    have hi := i.isLt
    have mem : (Shadow7.a0P (start j) - 1 + i.val, Shadow7.b0P (start j) - 1 + i.val) ∈ Close.low j :=
      List.mem_map.mpr ⟨i.val, List.mem_range.mpr hi, rfl⟩
    have l := wrote.2.2 _ mem
    simp only [if_pos inHist, hist _ inHist, Bool.not_not, previous,
      if_neg (notHist (Shadow7.e0P (start j) + 5) (by omega)), signed,
      if_neg (notHist (Shadow7.a0P (start j) - 1 + i.val) (by omega)), if_neg (notHist (Shadow7.b0P (start j) - 1 + i.val) (by omega)),
      (words i).1, (words i).2] at l
    exact l
  · intro q lo hn
    exact (wrote.2.1 q lo).trans (if_neg hn)

namespace StoreCoordinates
/-- dadon's `Leave{s}StoreCoordinates.result`. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z)))
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let out := run (BeforeStore.program j) m s
    out.basis (Shadow7.e0P (start j) + 5) = PortalValues.negative sg a.u ∧ (∀ q ∈ Close.history j, out.basis q = !s.basis q) ∧
    (∀ i : Fin (Shadow7.lowsP (start j) + 1), out.basis (Shadow7.a0P (start j) - 1 + i.val) = (a.u+a.v).testBit (Shadow7.sbP (start j) + i.val) ∧
        out.basis (Shadow7.b0P (start j) - 1 + i.val) = mag.testBit (Shadow7.sbP (start j) + i.val)) :=
  storeCoordinates_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
    nextSmall bound
end StoreCoordinates

namespace StoreMapped
/-- dadon's `Leave{s}StoreMapped.result`. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z)))
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)) :
    let a := step^[15] z
    let sign := PortalValues.negative sg a.u
    let mag := a.u - sign.toNat
    let before := run (BeforeStore.program j) m s
    let out := run (program j) m s
    out.phase = s.phase ∧ (∀ q ∈ Close.history j, out.basis q = s.basis q) ∧
      (∀ i : Fin (Shadow7.lowsP (start j) + 1), let pos := (a.u+a.v).testBit (Shadow7.sbP (start j) + i.val)
        let neg := mag.testBit (Shadow7.sbP (start j) + i.val) ^^ sign
        out.basis (Shadow7.a0P (start j) - 1 + i.val) = (if G then neg else pos) ∧
        out.basis (Shadow7.b0P (start j) - 1 + i.val) = (if G then pos else neg)) ∧
      ∀ q, q ∉ RailPair.sites (Close.low j) → q ∉ Close.history j → out.basis q = before.basis q := by
  have coords := storeCoordinates_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero
    par mode events nextSmall bound
  have prev : s.basis (start j + 30) = G := by
    have h := ready.2.2.1
    rw [(scan_ports j h0 (by omega)).2.2.2.2.1]
    cases G <;> exact h
  have phase := (beforeStore_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound).1
  have done := lowClose_store j h0 (by omega) s _ (m.drop (measurementCount (beforeStoreProgram j))) G _ _ _ prev coords.2.1
    coords.1 coords.2.2
  dsimp only at done phase ⊢
  rw [show program j = beforeStoreProgram j ++ GateMirror.forward (Shadow7.leaveLowClose (start j)) from rfl, run_append, run_take]
  exact ⟨done.1.trans phase, done.2⟩
end StoreMapped

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] run SkywalkNat.step

/-- The history cells in the `sig` frame, exactly (both forms). -/
theorem swaps_exact (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat) (hi : i < 15) :
    ((swaps j i : Nat) = start j + 1044 + i ∧ start j + 1044 + i ≤ 1300) ∨
      ((swaps j i : Nat) = 3113 - (start j + 1044 + i) ∧ Shadow7.e0P (start j) + 10 ≤ 3113 - (start j + 1044 + i) ∧
        3113 - (start j + 1044 + i) ≤ 1812) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have e := Shadow7.sig_hist (c := 1044 + i) w1 w2 (by omega) (by omega)
  unfold swaps; rw [show start j + 1044 + i = start j + (1044 + i) by omega]
  unfold Wire at *; omega

/-- The near flag of the prepared selector word. -/
theorem prior_near (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (k : Mode) :
    prior j k (Shadow7.e0P (start j) + 7) = .bit (nearby k) := by
  have h := controlCert j h0 (by omega) k
  simp only [reads, LeaveSelector.controls, List.cons.injEq, and_true] at h
  exact h.1

namespace PostReady

/-- dadon's `Leave{s}PostReady.result`. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z)))
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)) :
    let out := run (StoreMapped.program j) m s
    let f := decide (Shadow.far (Shadow7.sbP (start j)) 15 z)
    out.basis (Shadow7.e0P (start j) + 3) = s.basis (Shadow7.e0P (start j) + 3) ∧
    out.basis (Shadow7.e0P (start j) + 4) = s.basis (Shadow7.e0P (start j) + 4) ∧
    out.basis (Shadow7.e0P (start j) + 7) = nearby (actualMode (Shadow7.sbP (start j)) z) ∧
    out.basis (Shadow7.e0P (start j) + 6) = (f && HighBankSum.cross (LeaveJ7.TrueMiddle.d j z)) ∧
    (∀ p ∈ Close.events j, out.basis p.1 = s.basis p.1 ∧ out.basis p.2 = false) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have front := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
  have watchedOK := frontReady_frame j h0 (by omega) s m z G sg small ready fresh scratch temp
  have par0 := entry_parity j h0 (by omega) s m
  have store := (StoreMapped.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound).2.2.2
  have flags := beforeStore_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound
  have cleared := flagScratch_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events
  dsimp only at front store flags ⊢
  generalize hen : run (GateMirror.forward (entryOps (start j))) m s = en at front watchedOK par0
  generalize hn : m.drop (measurementCount (GateMirror.forward (entryOps (start j)))) = n
  generalize hk : actualMode (Shadow7.sbP (start j)) z = k at mode events ⊢
  have kept (q : Nat) (ok : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 17) ∨
      (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 17) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨
      (1556 ≤ q ∧ q ≤ 1575) ∨ q = Shadow7.e0P (start j) + 5)) : en.basis q = s.basis q := by
    rw [← hen]; exact entry_keep j h0 (by omega) q ok s m
  -- the selector word after the prefix
  have zeroE : ∀ q ∈ watched j, en.basis q = false := fun q hq => (watchedOK q hq).trans (zero q hq)
  have base : ∀ q : Nat, 1561 ≤ q → q ≤ 1597 → en.basis q = false := by
    intro q lo hi
    apply zeroE
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q - 1559, by omega, by omega⟩
  have z59 : en.basis 1559 = false := zeroE _ (by simp [watched])
  have z60 : en.basis 1560 = false := zeroE _ (by simp [watched])
  have zc : en.basis (ports j).crossing = false := zeroE _ (by simp [watched, ports])
  have zn : en.basis (ports j).near = false := zeroE _ (by simp [watched, ports])
  have modeE : k = farMode (en.basis (Shadow7.e0P (start j) + 3)) (en.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [kept _ (by omega), kept _ (by omega)]; exact mode
  have eventsE : right k = true → ∀ i < 15, i ≤ key k → en.basis (swaps j i) = decide (i = key k) := by
    intro on i hi hq
    have sw := swaps_exact j h0 (by omega) i hi
    exact (kept _ (by unfold Wire at *; omega)).trans (events on i hi hq)
  have prepared := preparedState j h0 (by omega) en n en.basis z.u k modeE z59 z60 (beforeFresh _ _ _ base zc zn) eventsE
  -- frames
  have notLow (q : Nat) (hq : ∀ i, i < Shadow7.lowsP (start j) + 1 → q ≠ Shadow7.a0P (start j) - 1 + i ∧ q ≠ Shadow7.b0P (start j) - 1 + i) :
      (q : Wire) ∉ RailPair.sites (Close.low j) := by
    intro hm
    obtain ⟨i, hi, e⟩ := (Close.mem_low_sites j q).mp hm
    have e' : q = Shadow7.a0P (start j) - 1 + i ∨ q = Shadow7.b0P (start j) - 1 + i := e
    have := hq i hi
    omega
  have notHist (q : Nat) (hq : q < start j + 16 ∨ start j + 30 < q) : (q : Wire) ∉ Close.history j := by
    intro hm
    obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have e' : start j + 16 + i = q := e
    omega
  have fullAt (q : Nat) (hw : ¬ workT j q) (hc : ¬ compT j q) :
      (run (fullProgram j) m s).basis q = (run (GateMirror.forward (fullPrefix j)) n en).basis q := by
    have e1 : run (fullProgram j) m s = run (Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558)
        (n.drop (measurementCount (GateMirror.forward (bodyOps j)))) (run (GateMirror.forward (bodyOps j)) n en) := by
      rw [fullProgram, forward_app, List.append_assoc, run_append, run_take, run_append, run_take, hen, hn]
    have e2 : run (GateMirror.forward (bodyOps j)) n en = run (GateMirror.forward (workOps (start j)))
        (n.drop (measurementCount (GateMirror.forward (fullPrefix j)))) (run (GateMirror.forward (fullPrefix j)) n en) := by
      rw [bodyOps, forward_app, run_append, run_take]
    rw [e1, LeaveReadoutFrame.preserved _ _ _ _ (fun h => hc (restore_dest j h0 (by omega) q h)), e2,
      LeaveReadoutFrame.preserved _ _ _ _ (fun h => hw (work_dest j h0 (by omega) q h))]
  have outAt (q : Nat) (h6 : q ≠ 1556) (h7 : q ≠ 1557) (h8 : q ≠ 1558)
      (hl : ∀ i, i < Shadow7.lowsP (start j) + 1 → q ≠ Shadow7.a0P (start j) - 1 + i ∧ q ≠ Shadow7.b0P (start j) - 1 + i)
      (hh : q < start j + 16 ∨ start j + 30 < q) :
      (run (StoreMapped.program j) m s).basis q = (run (fullProgram j) m s).basis q :=
    (store q (notLow q hl) (notHist q hh)).trans (flags.2.2.2.2.2.2 q h6 h7 h8)
  have hit (q : Nat) (hq : q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7) :
      (run (StoreMapped.program j) m s).basis q = (prior j k q).read en.basis := by
    rw [outAt q (by omega) (by omega) (by omega) (fun i hi => by omega) (by omega),
      fullAt q (by unfold workT; omega) (by unfold compT; omega), prepared]
    rfl
  have plain (q : Nat) (h6 : q ≠ 1556) (h7 : q ≠ 1557) (h8 : q ≠ 1558)
      (hl : ∀ i, i < Shadow7.lowsP (start j) + 1 → q ≠ Shadow7.a0P (start j) - 1 + i ∧ q ≠ Shadow7.b0P (start j) - 1 + i)
      (hh : q < start j + 16 ∨ start j + 30 < q) (hw : ¬ workT j q) (hc : ¬ compT j q)
      (hp : ¬ ((1559 ≤ q ∧ q ≤ 1597) ∨ q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7))
      (he : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 17) ∨
        (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 17) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨
        (1556 ≤ q ∧ q ≤ 1575) ∨ q = Shadow7.e0P (start j) + 5)) :
      (run (StoreMapped.program j) m s).basis q = s.basis q :=
    (outAt q h6 h7 h8 hl hh).trans ((fullAt q hw hc).trans ((prefix_keep j h0 (by omega) q hp en n).trans (kept q he)))
  have plainSwap (i : Nat) (hi : i < 15) :
      (run (StoreMapped.program j) m s).basis (swaps j i) = s.basis (swaps j i) := by
    have sw := swaps_exact j h0 (by omega) i hi
    exact plain (swaps j i) (by unfold Wire at *; omega) (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      (fun x hx => by unfold Wire at *; omega) (by unfold Wire at *; omega) (by unfold workT; unfold Wire at *; omega)
      (by unfold compT; unfold Wire at *; omega) (by unfold Wire at *; omega) (by unfold Wire at *; omega)
  have coldAt (t : Nat) (ht : t = 1556 ∨ (1559 ≤ t ∧ t ≤ 1562)) : (run (StoreMapped.program j) m s).basis t = false := by
    rw [store t (notLow t (fun i hi => by omega)) (notHist t (by omega))]
    rcases ht with rfl | ⟨a, b⟩
    · exact flags.2.1
    · have t6 : t ≠ 1556 := by omega
      have t7 : t ≠ 1557 := by omega
      have t8 : t ≠ 1558 := by omega
      refine (flags.2.2.2.2.2.2 t t6 t7 t8).trans ?_
      apply cleared
      refine List.mem_map.mpr ⟨(Shadow7.b0P (start j) - 1 + (t - 1559), 1559 + (t - 1559)), List.mem_append_right _
        (List.mem_map.mpr ⟨t - 1559, List.mem_range.mpr (by omega), rfl⟩), ?_⟩
      show 1559 + (t - 1559) = t
      omega
  -- the selector's readings
  have act := upperBits j h0 (by omega) _ en.basis front.2.2.2.2.2.1
  have math := loaded_signed j h0 (by omega) z en.basis small odd room (fun i hi => act i (Nat.lt_trans hi (by decide : 16 < 18)))
    (par0.trans par)
  dsimp only at math
  rw [hk] at math
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact plain (Shadow7.e0P (start j) + 3) (by omega) (by omega) (by omega) (fun i hi => by omega) (by omega)
      (by unfold workT; omega) (by unfold compT; omega) (by omega) (by omega)
  · exact plain (Shadow7.e0P (start j) + 4) (by omega) (by omega) (by omega) (fun i hi => by omega) (by omega)
      (by unfold workT; omega) (by unfold compT; omega) (by omega) (by omega)
  · rw [hit _ (Or.inr rfl), prior_near j h0 (by omega) k]; rfl
  · rw [hit _ (Or.inl rfl), math.1]
    by_cases g : Shadow.far (Shadow7.sbP (start j)) 15 z <;> simp [g]
  · intro p hp
    simp only [Close.events, List.mem_cons, List.not_mem_nil, or_false] at hp
    have c56 := coldAt 1556 (Or.inl rfl)
    have c59 := coldAt 1559 (Or.inr ⟨Nat.le_refl _, by omega⟩)
    have c60 := coldAt 1560 (Or.inr ⟨by omega, by omega⟩)
    have c61 := coldAt 1561 (Or.inr ⟨by omega, by omega⟩)
    have c62 := coldAt 1562 (Or.inr ⟨by omega, Nat.le_refl _⟩)
    have s0 := plainSwap 0 (by omega)
    have s1 := plainSwap 1 (by omega)
    have s2 := plainSwap 2 (by omega)
    have s3 := plainSwap 3 (by omega)
    have s4 := plainSwap 4 (by omega)
    rcases hp with e | e | e | e | e <;> rw [e]
    · exact ⟨s0, c56⟩
    · exact ⟨s1, c59⟩
    · exact ⟨s2, c60⟩
    · exact ⟨s3, c61⟩
    · exact ⟨s4, c62⟩

end PostReady

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Relocated
open Partial LeaveRelocation GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

/-- dadon's `Leave{s}Relocated.moves`. -/
abbrev moves (j : Fin 23) : List (Wire × Wire) := Shadow7.movesP (start j)
/-- dadon's `Leave{s}Relocated.lastPart`. -/
abbrev lastPart (j : Fin 23) : Program := GateMirror.forward (swapsG (Shadow7.movesP (start j)))

theorem lastPart_eq (s : Nat) : GateMirror.forward (swapsG (Shadow7.movesP s)) = LeaveRelocation.program (Shadow7.movesP s) := by
  simp only [swapsG, LeaveRelocation.program, GateMirror.forward, List.map_flatMap]; rfl

/-- No move is a self swap. -/
theorem moves_diff (s : Nat) (h1 : 90 ≤ s) (h2 : s ≤ 375) : ∀ p ∈ Shadow7.movesP s, p.1 ≠ p.2 := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  intro p hp
  rw [moves_split, List.mem_append] at hp
  rcases hp with hp | hp
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    rw [List.mem_range] at hk
    rw [hd k]
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · rw [hB k b]; ((try unfold Wire at *); omega)
    · rw [hP k (by omega)]; ((try unfold Wire at *); omega)
  · simp only [flagPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> ((try unfold Wire at *); omega)

/-- dadon's `Leave{s}Relocated.forward`. -/
theorem forward (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (st : State) (m : List Bool) :
    run (lastPart j) m st = ⟨st.phase, fun q => st.basis (LeaveRelocation.source (moves j) q)⟩ := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  rw [lastPart, lastPart_eq]
  exact LeaveRelocation.actual _ (moves_diff (start j) w1 w3) st m

/-- The three flags the next block reads come from the far flag, the near flag and the crossing bit. -/
theorem src_back (s : Nat) (h1 : 90 ≤ s) (h2 : s ≤ 375) :
    source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 6) = Shadow7.e0P s + 3 ∧ source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 7) = Shadow7.e0P s + 7 ∧
    source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 8) = Shadow7.e0P s + 6 := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  have ab (k : Nat) :
      ((bankPair s k).1 = 805 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  have bankOut (x : Wire) (hx : Shadow7.e0P (s+15) ≤ x) :
      source ((List.range (Shadow7.wpP (s+15) - 3)).map (bankPair s)) x = x := by
    apply src_untouched
    intro k hk
    rw [hd k]
    rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rw [e] <;> constructor <;> ((try unfold Wire at *); omega)
  have fl : ∀ x, source (flagPairs s) x = LeaveRelocation.flip 1557 (Shadow7.e0P (s+15) + 3) (LeaveRelocation.flip 1558 (Shadow7.e0P (s+15) + 4)
      (LeaveRelocation.flip (Shadow7.e0P s + 5) (Shadow7.e0P (s+15) + 5) (LeaveRelocation.flip (Shadow7.e0P s + 3) (Shadow7.e0P (s+15) + 6) (LeaveRelocation.flip (Shadow7.e0P s + 7) (Shadow7.e0P (s+15) + 7)
      (LeaveRelocation.flip (Shadow7.e0P s + 6) (Shadow7.e0P (s+15) + 8) x))))) := fun x => rfl
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [moves_split, LeaveRelocation.append, fl]
    simp (disch := ((try unfold Wire at *); omega)) only [flip_ne, flip_fst, flip_snd]
    exact bankOut _ (by omega)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Relocated

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] run SkywalkNat.step

namespace Relocated
/-- dadon's `Leave{s}Relocated.upperMap`. -/
theorem upperMap (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ∀ i : Nat, i < railP (start j + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1) →
      LeaveRelocation.source (moves j) (Shadow7.b0P (start j) + Shadow7.lowsP (start j) + i) = LeaveJ7.live j (Shadow7.lowsP (start j) + i) ∧
      LeaveRelocation.source (moves j) (Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i) = Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i := by
  intro i hi
  have h := upperMapB j h0 (by omega) i hi
  refine ⟨?_, h.2⟩
  rw [h.1]
  unfold LeaveJ7.live
  rw [if_neg (by omega)]
end Relocated

theorem forward_eventsG : ∀ (ps : List (Wire × Wire)) (a out : Wire),
    GateMirror.forward (eventsG a out ps) = LeaveNoSwap.block a out ps
  | [], a, out => rfl
  | (x, t) :: ps, a, out => by
    show GateMirror.forward ([.x x, .make a x t] ++ (eventsG t out ps ++ [.pop a x t, .x x])) = _
    rw [forward_app, forward_app, forward_eventsG ps t out]
    rfl

namespace Close

/-- dadon's `Leave{s}Close.tailShape`. -/
theorem tailShape (j : Fin 23) : afterLow j =
    LeaveNoSwap.block (Shadow7.e0P (start j) + 7) (Shadow7.e0P (start j) + 4) (events j) ++ Relocated.lastPart j := by
  show GateMirror.forward (Shadow7.leaveClose (start j)) = _
  unfold Shadow7.leaveClose
  rw [forward_app, forward_eventsG]
  rfl

theorem events_layout (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    ((Shadow7.e0P (start j) + 4 : Wire) :: (Shadow7.e0P (start j) + 7 : Wire) :: PortalAnd.sites (events j)).Nodup := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have e61 : 1635 ≤ Shadow7.e0P (start j) := by have rr := Shadow7.rail_win w1 w2; omega
  have hf : (events j).map Prod.fst = (List.range 5).map (swaps j) := rfl
  have hs : (events j).map Prod.snd = [1556, 1559, 1560, 1561, 1562] := rfl
  -- a swap cell is on the B rail or in the pool: away from the two flags and from the small scratch
  have away : ∀ i : Nat, i < 5 → (swaps j i : Nat) ≤ 1300 ∨ Shadow7.e0P (start j) + 10 ≤ (swaps j i : Nat) := by
    intro i hi
    have sw := swaps_range j h0 (by omega) i (by omega)
    rcases sw with a | a
    · exact Or.inl a
    · exact Or.inr a.1
  have memF : ∀ q ∈ (events j).map Prod.fst, (q : Nat) ≤ 1300 ∨ Shadow7.e0P (start j) + 10 ≤ (q : Nat) := by
    intro q hq
    rw [hf] at hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    exact away i (List.mem_range.mp hi)
  have memS : ∀ q ∈ (events j).map Prod.snd, 1556 ≤ (q : Nat) ∧ (q : Nat) ≤ 1562 := by
    rw [hs]; decide
  have fnd : ((events j).map Prod.fst).Nodup := by
    rw [hf]
    exact List.Nodup.map_on (fun x hx y hy e => swaps_inj j h0 (by omega) x y
      (by have := List.mem_range.mp hx; omega) (by have := List.mem_range.mp hy; omega) e) List.nodup_range
  have snd : ((events j).map Prod.snd).Nodup := by rw [hs]; decide
  have flagOut : ∀ f : Nat, (f = Shadow7.e0P (start j) + 4 ∨ f = Shadow7.e0P (start j) + 7) →
      (f : Wire) ∉ (events j).map Prod.fst ++ (events j).map Prod.snd := by
    intro f hf' hm
    rcases List.mem_append.mp hm with h | h
    · have a := memF f h
      unfold Wire at *; omega
    · have a := memS f h
      unfold Wire at *; omega
  rw [(((sites_perm (events j)).cons (Shadow7.e0P (start j) + 7 : Wire)).cons (Shadow7.e0P (start j) + 4 : Wire)).nodup_iff]
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨flagOut _ (Or.inr rfl), List.nodup_append.mpr ⟨fnd, snd, ?_⟩⟩⟩
  · intro hm
    rcases List.mem_cons.mp hm with e | hm
    · have e' : Shadow7.e0P (start j) + 4 = Shadow7.e0P (start j) + 7 := e
      omega
    · exact flagOut _ (Or.inl rfl) hm
  · intro a ha b hb e
    have x := memF a ha
    have y := memS b hb
    have e' : (a : Nat) = b := e
    unfold Wire at *; omega

/-- dadon's `Leave{s}Close.after`. -/
theorem after (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (cold : ∀ p ∈ events j, s.basis p.2 = false) :
    let toggled := s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 7) && (events j).all (fun p => !s.basis p.1))
    run (afterLow j) m s =
      ⟨s.phase, fun q => (writeBit s.basis (Shadow7.e0P (start j) + 4) toggled) (LeaveRelocation.source (Relocated.moves j) q)⟩ := by
  dsimp only
  rw [tailShape, run_append, run_take, LeaveNoSwap.action _ _ _ _ _ (events_layout j h0 (by omega)) cold,
    Relocated.forward j h0 (by omega)]

end Close

namespace Posted
open StairArchiveTrace

/-- dadon's `Leave{s}Posted.result`. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (f u c : Bool) (w : Fin 16)
    (xs : List (Bool × Bool)) (len : xs.length = 15) (chainOK : f = true → chain u xs)
    (first : f = true → u = false → ∀ i (h : i < xs.length), i ≤ w.val → xs[i].2 = decide (i = w.val))
    (swaps : (Close.events j).map (fun p => s.basis p.1) = (xs.take 5).map Prod.snd)
    (far : s.basis (Shadow7.e0P (start j) + 3) = f) (old : s.basis (Shadow7.e0P (start j) + 4) = (f && u))
    (suffix : s.basis (Shadow7.e0P (start j) + 7) = nearby (ofFlags f u w))
    (cross : s.basis (Shadow7.e0P (start j) + 6) = (f && c)) (cold : ∀ p ∈ Close.events j, s.basis p.2 = false) :
    let out := run (Close.afterLow j) m s
    out.phase = s.phase ∧ out.basis (Shadow7.e0P (start j + 15) + 6) = f ∧
      out.basis (Shadow7.e0P (start j + 15) + 7) = (f && afterFlags u (xs.take 5)) ∧
      out.basis (Shadow7.e0P (start j + 15) + 8) = (f && c) ∧
      ∀ q, out.basis q = writeBit s.basis (Shadow7.e0P (start j) + 4) false (LeaveRelocation.source (Relocated.moves j) q) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have vp := LeavePendingHistory.pending f u xs w len chainOK first
  have ev : (Close.events j).all (fun p => !s.basis p.1) = !(xs.take 5).any Prod.snd := by
    have mapped : (Close.events j).any (fun p => s.basis p.1) = (xs.take 5).any Prod.snd := by
      simpa only [List.any_map, Function.comp_def, id_eq] using congrArg (List.any · id) swaps
    rw [← mapped]
    simp only [List.all_eq_not_any_not, Bool.not_not]
  have cleared : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 7) &&
      (Close.events j).all (fun p => !s.basis p.1))) = false := by
    rw [old, suffix, ev]; exact vp.2
  have geom := Relocated.src_back (start j) w1 w3
  have wb (q : Nat) (hq : q ≠ Shadow7.e0P (start j) + 4) : writeBit s.basis (Shadow7.e0P (start j) + 4) false q = s.basis q := by
    simp [writeBit, Function.update, hq]
  have a := Close.after j h0 (by omega) s m cold
  dsimp only at a ⊢
  rw [a, cleared]
  refine ⟨rfl, ?_, ?_, ?_, fun _ => rfl⟩
  · show writeBit s.basis (Shadow7.e0P (start j) + 4) false (LeaveRelocation.source (Shadow7.movesP (start j)) (Shadow7.e0P (start j + 15) + 6)) = f
    rw [geom.1, wb _ (by omega)]; exact far
  · show writeBit s.basis (Shadow7.e0P (start j) + 4) false (LeaveRelocation.source (Shadow7.movesP (start j)) (Shadow7.e0P (start j + 15) + 7)) = _
    rw [geom.2.1, wb _ (by omega)]; exact suffix.trans vp.1
  · show writeBit s.basis (Shadow7.e0P (start j) + 4) false (LeaveRelocation.source (Shadow7.movesP (start j)) (Shadow7.e0P (start j + 15) + 8)) = _
    rw [geom.2.2, wb _ (by omega)]; exact cross

end Posted

/-- The leave is the store part followed by the close. -/
theorem leave_split (j : Fin 23) : Shadow7.leaveP j = StoreMapped.program j ++ Close.afterLow j := by
  rw [StoreMapped.program_eq, Shadow7.leaveP, Shadow7.leaveOps_split, forward_app]

namespace Whole

/-- dadon's `Leave{s}Whole.result`. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z)))
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)) (xs : List (Bool × Bool)) (len : xs.length = 15)
    (historyOK : Shadow.far (Shadow7.sbP (start j)) 15 z → StairArchiveTrace.chain (decide (2^(Shadow7.sbP (start j)) ≤ z.u)) xs)
    (first : Shadow.far (Shadow7.sbP (start j)) 15 z → decide (2^(Shadow7.sbP (start j)) ≤ z.u) = false →
      ∀ i (h : i < xs.length), i ≤ IntegerHigh.wait 15 z.u → xs[i].2 = decide (i = IntegerHigh.wait 15 z.u))
    (saved : (Close.events j).map (fun p => s.basis p.1) = (xs.take 5).map Prod.snd)
    (far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
    (side : s.basis (Shadow7.e0P (start j) + 4) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u))) :
    let u := decide (2^(Shadow7.sbP (start j)) ≤ z.u)
    let active := decide (Shadow.far (Shadow7.sbP (start j)) 15 z)
    let v := run (StoreMapped.program j) m s
    let out := run (Shadow7.leaveP j) m s
    out.phase = s.phase ∧ out.basis (Shadow7.e0P (start j + 15) + 6) = active ∧
      out.basis (Shadow7.e0P (start j + 15) + 7) = (active && StairArchiveTrace.afterFlags u (xs.take 5)) ∧
      out.basis (Shadow7.e0P (start j + 15) + 8) = (active && HighBankSum.cross (LeaveJ7.TrueMiddle.d j z)) ∧
      ∀ q, out.basis q = writeBit v.basis (Shadow7.e0P (start j) + 4) false (LeaveRelocation.source (Relocated.moves j) q) := by
  have h := PostReady.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode
    events nextSmall bound
  have pre := (StoreMapped.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound).1
  dsimp only at h pre ⊢
  generalize hv : run (StoreMapped.program j) m s = v at h pre
  have reads : (Close.events j).map (fun p => v.basis p.1) = (xs.take 5).map Prod.snd :=
    (List.map_congr_left (fun p hp => (h.2.2.2.2 p hp).1)).trans saved
  have done := Posted.result j h0 (by omega) v (m.drop (measurementCount (StoreMapped.program j)))
    (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (2^(Shadow7.sbP (start j)) ≤ z.u))
    (HighBankSum.cross (LeaveJ7.TrueMiddle.d j z))
    ⟨IntegerHigh.wait 15 z.u, by have hw := IntegerHigh.wait_le 15 z.u; omega⟩ xs len
    (fun hf => historyOK (of_decide_eq_true hf)) (fun hf hu => first (of_decide_eq_true hf) hu)
    reads (h.1.trans far) (h.2.1.trans side) h.2.2.1 h.2.2.2.1 (fun p hp => (h.2.2.2.2 p hp).2)
  dsimp only at done
  rw [leave_split j, run_append, run_take, hv]
  exact ⟨done.1.trans pre, done.2⟩

end Whole

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial IntegerPacket IntegerHigh SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The packet's 15 history cells as the window reads them: letter `start j+16+i`, swap flag `swaps j i`. -/
theorem cells_eq (j : Fin 23) (h1 : j.val ≤ 20) (v : BasisState) :
    ∀ (a n : Nat), a+n ≤ 15 → readCells (Shadow7.shape j) a n (mappedBasis j v) =
      (List.range' a n).map (fun i => (v (start j+16+i), v (swaps j i)))
  | _, 0, _ => rfl
  | a, n+1, h => by
    rw [readCells, cells_eq j h1 v (a+1) n (by omega), List.range'_succ, List.map_cons]
    congr 1
    simp only [cell, IntegerPacket.ports, mappedBasis, windowNet, net, swaps, Shadow7.shape]
    have e1 : OB5.sig (start j+14) (start j+a+16) = start j+16+a := by
      unfold OB5.sig start; split <;> (try unfold Wire at *) <;> omega
    have e2 : start j+a+16+1028 = start j+1044+a := by omega
    rw [e1, e2]

namespace RecordedParity
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (odd : z.v % 2 = 1)
    (record : IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v)) :
    LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)) := by
  have ports : LeaveJ7.oddRead j s.basis =
      (readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis)).map (fun pair => !pair.1) := by
    rw [cells_eq j h1 s.basis 0 15 (by omega), List.map_map]
    simp only [LeaveJ7.oddRead, LeaveJ7.ports, List.range_eq_range', Function.comp_def]
  rw [ports, record, ←true_records_shadow7 (Shadow7.sbP (start j)) z small.1 odd g sg]
  exact LeaveTraceLetters.parity _ _ _ _ (shadow_odd_shadow7 _ _ small.1 odd)
end RecordedParity

namespace RecordedEvents
open LeaveSelector
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (odd : z.v % 2 = 1)
    (record : IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v)) :
    let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v)
    (Close.events j).map (fun p => s.basis p.1) = (xs.take 5).map Prod.snd ∧
    (LeaveSelector.right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z))) := by
  intro xs
  have cells := cells_eq j h1 s.basis 0 15 (by omega)
  have tape : (List.range 15).map (fun i => s.basis (LeaveJ7.swaps j i)) = xs.map Prod.snd := by
    change _ = (SkywalkTrace.trace 15 _).map _
    rw [←record, cells, List.map_map, List.range_eq_range']
    rfl
  constructor
  · have five : (Close.events j).map (fun p => s.basis p.1) =
        ((List.range 15).map (fun i => s.basis (LeaveJ7.swaps j i))).take 5 := by
      simp only [Close.events, List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append,
        List.cons_append, List.take_succ_cons, List.take_zero]
    rw [five, tape, List.map_take]
  · intro rightSide i hi early
    have far : Shadow.far (Shadow7.sbP (start j)) 15 z := by
      by_contra h
      simp [actualMode,farMode,ofFlags,right,h] at rightSide
    obtain ⟨keyEq,orientation,_⟩ := modeKey (Shadow7.sbP (start j)) z far
    have side : decide (2^(Shadow7.sbP (start j))≤z.u)=false := by rw [orientation] at rightSide; simpa using rightSide
    have keyWait : key (actualMode (Shadow7.sbP (start j)) z)=wait 15 z.u := by
      rw [keyEq,place,if_neg (of_decide_eq_false side)]
    have hlen : i<xs.length := by simpa only [xs,SkywalkTrace.trace_length] using hi
    have phys := congrArg (fun a : List Bool => a[i]?) tape
    have before := LeaveJ7.Far.firstSwap (Shadow7.sbP (start j)) z g sg small odd far side i hlen (keyWait ▸ early)
    rw [keyWait]
    exact Eq.trans (by simpa [List.getElem?_eq_getElem hlen,hi] using phys) before
end RecordedEvents

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial IntegerPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
attribute [local irreducible] Shadow7.leaveP run
namespace PreservedRecords
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool)
    (previous : ∀ q ∈ Close.history j, (run (Shadow7.leaveP j) m s).basis q = s.basis q) :
    IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j (run (Shadow7.leaveP j) m s).basis) =
      IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis) := by
  rw [cells_eq j h1 _ 0 15 (by omega), cells_eq j h1 _ 0 15 (by omega)]
  apply List.map_congr_left
  intro i hi
  have hi' : i < 15 := by simpa using hi
  have port : start j+16+i ∈ Close.history j := by
    simp only [Close.history, LeaveJ7.history, List.mem_map, List.mem_range]; exact ⟨i, hi', rfl⟩
  have hk := Shadow7.swaps_kept j h0 (by omega) i hi' s m
  have hp := previous _ port
  simp only [LeaveJ7.swaps]
  rw [hp, hk]
end PreservedRecords
end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Relocated
open Partial LeaveRelocation
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-- The next block's three flags read the old flag sites (the direction dadon's `EndWords` uses). -/
theorem src_flagsBack (s : Nat) (h1 : 90 ≤ s) (h2 : s ≤ 375) :
    source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 3) = 1557 ∧ source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 4) = 1558 ∧
    source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 5) = Shadow7.e0P s + 5 := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  have ab (k : Nat) :
      ((bankPair s k).1 = 805 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  have bankOut (x : Wire) (hx : x = 1557 ∨ x = 1558 ∨ x = Shadow7.e0P s + 5) :
      source ((List.range (Shadow7.wpP (s+15) - 3)).map (bankPair s)) x = x := by
    apply src_untouched
    intro k hk
    rw [hd k]
    rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rw [e] <;> constructor <;> ((try unfold Wire at *); omega)
  have fl : ∀ x, source (flagPairs s) x = LeaveRelocation.flip 1557 (Shadow7.e0P (s+15) + 3) (LeaveRelocation.flip 1558 (Shadow7.e0P (s+15) + 4)
      (LeaveRelocation.flip (Shadow7.e0P s + 5) (Shadow7.e0P (s+15) + 5) (LeaveRelocation.flip (Shadow7.e0P s + 3) (Shadow7.e0P (s+15) + 6)
      (LeaveRelocation.flip (Shadow7.e0P s + 7) (Shadow7.e0P (s+15) + 7) (LeaveRelocation.flip (Shadow7.e0P s + 6) (Shadow7.e0P (s+15) + 8) x))))) := fun x => rfl
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [moves_split, LeaveRelocation.append, fl]
    simp (disch := ((try unfold Wire at *); omega)) only [flip_ne, flip_fst, flip_snd]
    exact bankOut _ (by simp)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Relocated

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial SkywalkNat LeaveSelector IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
attribute [local irreducible] run SkywalkNat.step

/-- The upper bank wires the relocation reads are neither the side flag, nor a low column, nor a history letter. -/
theorem upper_away (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Nat)
    (hi : i < railP (start j + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1)) :
    (Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) : Nat) ≠ Shadow7.e0P (start j) + 4 ∧
    Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) ∉ RailPair.sites (Close.low j) ∧
    Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) ∉ Close.history j := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have n : Shadow7.lowsP (start j) + i < Shadow7.wpP (start j) + 15 := by ((try unfold Wire at *); omega)
  have bc := Shadow7.bank_cases w1 w2 n
  have hb : (3 ≤ Shadow7.lowsP (start j) + i ∧ Shadow7.lowsP (start j) + i < Shadow7.wpP (start j) ∧
      (Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) : Nat) = bTopP (start j) + 1 + (Shadow7.lowsP (start j) + i) - Shadow7.wpP (start j)) ∨
      ((Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) : Nat) ≥ 1598 ∧ (Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) : Nat) ≤ 1612) := by
    rcases bc with ⟨a, _⟩ | ⟨a, b, c, _, _⟩ | ⟨g, e, f⟩
    · ((try unfold Wire at *); omega)
    · exact Or.inl ⟨a, b, c⟩
    · exact Or.inr ⟨by ((try unfold Wire at *); omega), f⟩
  generalize hq : (Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) : Nat) = q at hb ⊢
  have lowOK : ∀ k, k ≤ Shadow7.lowsP (start j) → q ≠ Shadow7.a0P (start j) - 1 + k ∧ q ≠ Shadow7.b0P (start j) - 1 + k := by
    intro k hk
    rcases hb with ⟨h3, h4, h5⟩ | ⟨h6, h7⟩ <;> constructor <;> ((try unfold Wire at *); omega)
  have histOK : ∀ k, k < 15 → q ≠ start j + 16 + k := by
    intro k hk
    rcases hb with ⟨h3, h4, h5⟩ | ⟨h6, h7⟩ <;> ((try unfold Wire at *); omega)
  refine ⟨by rcases hb with ⟨h3, h4, h5⟩ | ⟨h6, h7⟩ <;> ((try unfold Wire at *); omega), fun h => ?_, fun h => ?_⟩
  · simp only [RailPair.sites, Close.low, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at h
    obtain ⟨p, ⟨k, hk, rfl⟩, e⟩ := h
    have lk := lowOK k (by omega)
    rcases e with e | e
    · exact lk.1 e
    · exact lk.2 e
  · simp only [Close.history, LeaveJ7.history, List.mem_map, List.mem_range] at h
    obtain ⟨k, hk, e⟩ := h
    exact histOK k hk e.symm

namespace EndWords
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z)))
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)) (xs : List (Bool × Bool)) (len : xs.length = 15)
    (historyOK : Shadow.far (Shadow7.sbP (start j)) 15 z → StairArchiveTrace.chain (decide (2^(Shadow7.sbP (start j)) ≤ z.u)) xs)
    (first : Shadow.far (Shadow7.sbP (start j)) 15 z → decide (2^(Shadow7.sbP (start j)) ≤ z.u) = false →
      ∀ i (h : i < xs.length), i ≤ IntegerHigh.wait 15 z.u → xs[i].2 = decide (i = IntegerHigh.wait 15 z.u))
    (saved : (Close.events j).map (fun p => s.basis p.1) = (xs.take 5).map Prod.snd)
    (far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
    (side : s.basis (Shadow7.e0P (start j) + 4) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u))) :
    let a := step^[15] z
    let sign := PortalValues.negative sg a.u
    let mag := a.u - sign.toNat
    let next := decide (Shadow.far (Shadow7.sbP (start j + 15)) 15 a)
    let out := run (Shadow7.leaveP j) m s
    out.basis (Shadow7.e0P (start j + 15) + 3) = next ∧ out.basis (Shadow7.e0P (start j + 15) + 4) = (next && decide (2^(Shadow7.sbP (start j + 15)) ≤ a.u)) ∧
      out.basis (Shadow7.e0P (start j + 15) + 5) = sign ∧
      (∀ q ∈ Close.history j, out.basis q = s.basis q) ∧
      (∀ i : Fin (Shadow7.lowsP (start j) + 1), let pos := (a.u+a.v).testBit (Shadow7.sbP (start j) + i.val)
        let neg := mag.testBit (Shadow7.sbP (start j) + i.val) ^^ sign
        out.basis (Shadow7.a0P (start j) - 1 + i.val) = (if G then neg else pos) ∧
        out.basis (Shadow7.b0P (start j) - 1 + i.val) = (if G then pos else neg)) ∧
      ∀ i : Nat, i < railP (start j + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1) →
        out.basis (Shadow7.b0P (start j) + Shadow7.lowsP (start j) + i) = (a.u+a.v).testBit (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1 + i) := by
  intro a sign mag next out
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := Relocated.chain_geo w1 w3
  have whole := Whole.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode
    events nextSmall bound xs len historyOK first saved far side
  have store := StoreMapped.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound
  have before := BeforeStore.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound
  have coords := StoreCoordinates.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero
    par mode events nextSmall bound
  dsimp only at whole store before coords
  generalize hv : run (StoreMapped.program j) m s = v at whole store
  generalize hb : run (BeforeStore.program j) m s = b at store before coords
  have atSite (q src : Wire) (link : LeaveRelocation.source (Relocated.moves j) q = src) (clear : src ≠ Shadow7.e0P (start j) + 4) :
      out.basis q = v.basis src := by
    show (run (Shadow7.leaveP j) m s).basis q = _
    rw [whole.2.2.2.2, link]; simp [writeBit, clear]
  have flagAt (q src : Wire) (link : LeaveRelocation.source (Relocated.moves j) q = src)
      (outside : src ≠ Shadow7.e0P (start j) + 4 ∧ src ∉ RailPair.sites (Close.low j) ∧ src ∉ Close.history j) :
      out.basis q = b.basis src :=
    (atSite q src link outside.1).trans (store.2.2.2 _ outside.2.1 outside.2.2)
  have lowMem (q : Wire) (h : q ∈ RailPair.sites (Close.low j)) :
      ∃ i, i ≤ Shadow7.lowsP (start j) ∧ (q = Shadow7.a0P (start j) - 1 + i ∨ q = Shadow7.b0P (start j) - 1 + i) := by
    simp only [RailPair.sites, Close.low, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at h
    obtain ⟨p, ⟨i, hi, rfl⟩, hq⟩ := h
    exact ⟨i, by omega, hq⟩
  have histMem (q : Wire) (h : q ∈ Close.history j) : ∃ i, i < 15 ∧ q = start j + 16 + i := by
    simp only [Close.history, LeaveJ7.history, List.mem_map, List.mem_range] at h
    obtain ⟨i, hi, rfl⟩ := h
    exact ⟨i, hi, rfl⟩
  have sb := Relocated.src_flagsBack (start j) w1 w3
  have untouched (q : Nat) (hq : q < 805 + Shadow7.sbP (start j + 15)) (hq2 : start j + 15 ≤ q) :
      LeaveRelocation.source (Relocated.moves j) q = q :=
    Relocated.src_out (start j) w1 w3 q (Or.inl hq) (by ((try unfold Wire at *); omega))
  have notLow (q : Nat) (hq : Shadow7.b0P (start j) + 12 ≤ q) : q ∉ RailPair.sites (Close.low j) := by
    intro h; obtain ⟨i, hi, e⟩ := lowMem _ h
    rcases e with e | e <;> ((try unfold Wire at *); omega)
  have notHist (q : Nat) (hq : start j + 31 ≤ q) : q ∉ Close.history j := by
    intro h; obtain ⟨i, hi, e⟩ := histMem _ h; ((try unfold Wire at *); omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (flagAt _ 1557 sb.1 ⟨by ((try unfold Wire at *); omega), notLow _ (by ((try unfold Wire at *); omega)), notHist _ (by ((try unfold Wire at *); omega))⟩).trans before.2.2.1
  · exact (flagAt _ 1558 sb.2.1 ⟨by ((try unfold Wire at *); omega), notLow _ (by ((try unfold Wire at *); omega)), notHist _ (by ((try unfold Wire at *); omega))⟩).trans before.2.2.2.1
  · refine (flagAt _ (Shadow7.e0P (start j) + 5) sb.2.2 ⟨by ((try unfold Wire at *); omega), notLow _ (by ((try unfold Wire at *); omega)), notHist _ (by ((try unfold Wire at *); omega))⟩).trans ?_
    exact coords.1
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := histMem _ hq
    exact (atSite _ _ (untouched _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (by ((try unfold Wire at *); omega))).trans (store.2.1 _ hq)
  · intro i
    have hi := i.isLt
    have x1 := untouched (Shadow7.a0P (start j) - 1 + i.val) (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
    have x2 := untouched (Shadow7.b0P (start j) - 1 + i.val) (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
    exact ⟨(atSite _ _ x1 (by ((try unfold Wire at *); omega))).trans (store.2.2.1 i).1, (atSite _ _ x2 (by ((try unfold Wire at *); omega))).trans (store.2.2.1 i).2⟩
  · intro i hi
    have up := (Relocated.upperMap j h0 (by omega) i hi).1
    have lv : LeaveJ7.live j (Shadow7.lowsP (start j) + i) = Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) := by
      unfold LeaveJ7.live; rw [if_neg (by ((try unfold Wire at *); omega))]
    rw [lv] at up
    have n : Shadow7.lowsP (start j) + i < Shadow7.wpP (start j) + 15 := by ((try unfold Wire at *); omega)
    have a1 := flagAt _ _ up (upper_away j h0 (by omega) i hi)
    have hb2 := before.2.2.2.2.2.1 _ n
    rw [lv] at hb2
    unfold LeaveJ7.TrueMiddle.F at hb2
    rw [Nat.testBit_div_two_pow] at hb2
    refine a1.trans (hb2.trans ?_)
    congr 1
    omega
end EndWords

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial SkywalkNat GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- A wire outside `Shadow7.leaveBox2` keeps its value through the leave (par-c1's `Shadow7.leaveOps_box2`). -/
theorem leave_keeps (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Wire) (hq : ¬ Shadow7.leaveBox2 (start j) q) (m : List Bool) (s : State) :
    (run (Shadow7.leaveP j) m s).basis q = s.basis q := by
  apply LeaveReadoutFrame.preserved
  unfold Shadow7.leaveP
  rw [dest_forward]
  intro hmem
  obtain ⟨g, hg, e⟩ := List.mem_map.mp hmem
  exact hq (e ▸ Shadow7.leaveOps_box2 j h0 (by omega) g hg (target g) (by rw [GateMirror.Gate.wires_eq]; simp))

/-- The same for the StoreMapped prefix (`Shadow7.leaveHeadOps ++ Shadow7.leaveMidOps`). -/
theorem storeMapped_keeps (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Wire) (hq : ¬ Shadow7.leaveBox2 (start j) q) (m : List Bool) (s : State) :
    (run (StoreMapped.program j) m s).basis q = s.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [StoreMapped.program_eq j, dest_forward]
  intro hmem
  obtain ⟨g, hg, e⟩ := List.mem_map.mp hmem
  have hg' : g ∈ Shadow7.leaveOps (start j) := by rw [Shadow7.leaveOps_split]; exact List.mem_append_left _ hg
  exact hq (e ▸ Shadow7.leaveOps_box2 j h0 (by omega) g hg' (target g) (by rw [GateMirror.Gate.wires_eq]; simp))

/-- The small companion registers sit inside the core checkpoint's cleared sites. -/
theorem smallC_targets (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : ∀ q ∈ LeaveJ7.smallC j, q ∈ CoreCheckpoint.targets j := by
  intro q hq
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  simp only [LeaveJ7.smallC, List.mem_map, List.mem_range] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  simp only [CoreCheckpoint.targets, List.mem_append]
  left; left; left
  exact List.mem_range'_1.mpr ⟨by omega, by unfold Shadow7.lowsP at hi; unfold Shadow7.sbP at *; omega⟩

theorem smallM_mag (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : ∀ q ∈ LeaveJ7.smallM j, q ∈ CoreCheckpoint.magSites j := by
  intro q hq
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  simp only [LeaveJ7.smallM, List.mem_map, List.mem_range] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  simp only [CoreCheckpoint.magSites, LeaveJ7.fullM, List.mem_map, List.mem_range]
  exact ⟨i, by unfold Shadow7.lowsP at hi; unfold Shadow7.sbP at *; omega, rfl⟩

/-- dadon's `zerosAt`/`coreDone`: after the full arithmetic, every core-checkpoint target outside `smallM` is clean. -/
theorem core_done (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z)))
    (quiet : ∀ q ∈ CoreCheckpoint.rawSites j, s.basis q = false) (q : Wire)
    (mem : q ∈ CoreCheckpoint.targets j) (notM : q ∉ LeaveJ7.smallM j) :
    (run (FullArithmetic.program j) m s).basis q = false := by
  have h := CoreCheckpoint.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  dsimp only at h
  generalize hc : run (CoreCheckpoint.program j) m s = c at h
  have zerosAt (q : Wire) (mem : q ∈ CoreCheckpoint.targets j) : c.basis q = false := by
    simp only [CoreCheckpoint.targets, List.mem_append, List.mem_map] at mem
    rcases mem with ((scr | free) | raw) | mag
    · obtain ⟨lo, hi⟩ := List.mem_range'_1.mp scr
      have lim : (q : Nat) - 1559 < 39 := by unfold Wire at *; omega
      have e := h.1 ⟨(q : Nat) - 1559, lim⟩
      have e2 : 1559 + ((q : Nat) - 1559) = q := by unfold Wire at *; omega
      dsimp only at e
      rw [e2] at e
      exact e
    · obtain ⟨k, _, rfl⟩ := free; exact h.2.1 k
    · exact (h.2.2.1 q raw).trans (quiet q raw)
    · exact h.2.2.2 q mag
  have cleanCs : ∀ q ∈ LeaveJ7.smallC j, c.basis q = false := fun q hq => zerosAt _ (smallC_targets j h0 (by omega) q hq)
  have clearM : regValue (LeaveJ7.smallM j) c.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => h.2.2.2 q (smallM_mag j h0 (by omega) q hq))
  have rest := LeaveJ7.restore_run j h0 (by omega) c (m.drop (measurementCount (CoreCheckpoint.program j))) cleanCs clearM
  rw [FullArithmetic.restoreShape j, run_append, run_take, hc, rest.2.1 _ notM]
  exact zerosAt q mem

/-- The free word columns are clean after the full arithmetic (HighZero's lower words). -/
theorem row_done (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z))) (k : Fin 18) (notM : (LeaveJ7.row j k).free ∉ LeaveJ7.smallM j) :
    (run (FullArithmetic.program j) m s).basis (LeaveJ7.row j k).free = false := by
  have h := CoreCheckpoint.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  dsimp only at h
  generalize hc : run (CoreCheckpoint.program j) m s = c at h
  have cleanCs : ∀ q ∈ LeaveJ7.smallC j, c.basis q = false := by
    intro q hq
    obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
    have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
    have rr := Shadow7.rail_win w1 w2
    simp only [LeaveJ7.smallC, List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact h.1 ⟨i, by omega⟩
  have clearM : regValue (LeaveJ7.smallM j) c.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => h.2.2.2 q (smallM_mag j h0 (by omega) q hq))
  have rest := LeaveJ7.restore_run j h0 (by omega) c (m.drop (measurementCount (CoreCheckpoint.program j))) cleanCs clearM
  rw [FullArithmetic.restoreShape j, run_append, run_take, hc, rest.2.1 _ notM]
  exact h.2.1 k

theorem row_free (j : Fin 23) (i : Nat) (hi : i < 18) :
    (LeaveJ7.row j ⟨i, hi⟩).free = if i < Shadow7.lowsP (start j) then Shadow7.bankW (start j) i else Shadow7.a0P (start j) + i := by
  simp only [LeaveJ7.row, LeaveJ7.cols, Shadow7.columnsP, HighBankJoin.Column.free, List.getElem_map, List.getElem_range]
  by_cases h : i < Shadow7.lowsP (start j) <;> simp [h]

theorem not_low (j : Fin 23) (q : Wire)
    (h : (q < Shadow7.a0P (start j) - 1 ∨ Shadow7.a0P (start j) + Shadow7.lowsP (start j) ≤ q) ∧ (q < Shadow7.b0P (start j) - 1 ∨ Shadow7.b0P (start j) + Shadow7.lowsP (start j) ≤ q)) :
    q ∉ RailPair.sites (Close.low j) := by
  intro hm
  obtain ⟨i, hi, e⟩ := (Close.mem_low_sites j q).mp hm
  have ha : 1 ≤ Shadow7.a0P (start j) := by unfold Shadow7.a0P; omega
  have hb : 1 ≤ Shadow7.b0P (start j) := by unfold Shadow7.b0P; omega
  unfold Wire at *
  omega

theorem not_history (j : Fin 23) (q : Wire) (h : q < start j + 16 ∨ start j + 30 < q) : q ∉ Close.history j := by
  intro hm
  simp only [Close.history, LeaveJ7.history, List.mem_map, List.mem_range] at hm
  obtain ⟨i, hi, e⟩ := hm
  ((try unfold Wire at *); omega)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.ActualHistory
open Arithmetic Partial SkywalkNat StairArchiveTrace
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}ActualHistory.result`. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP ((start j) + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15))
    (far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
    (side : s.basis (Shadow7.e0P (start j) + 4) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u))) (g0 s0 : Bool)
    (record : IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)) :
    let out := run (Shadow7.leaveP j) m s
    let cells := IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)
    cells = SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v) ∧
      out.basis (Shadow7.e0P ((start j) + 15) + 6) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      out.basis (Shadow7.e0P ((start j) + 15) + 7) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && afterFlags (decide (z.v < z.u)) (cells.take 5)) ∧
      out.basis (Shadow7.e0P ((start j) + 15) + 8) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && HighBankSum.cross (LeaveJ7.TrueMiddle.d j z)) := by
  let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par := RecordedParity.result j h0 (by omega) s z g0 s0 small odd record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [far, side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j h0 (by omega) s z g0 s0 small odd record
  have all := Whole.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ small odd) (LeaveJ7.Far.firstSwap _ _ _ _ small odd) ev.1 far side
  have words := EndWords.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ small odd) (LeaveJ7.Far.firstSwap _ _ _ _ small odd) ev.1 far side
  have kept := (PreservedRecords.result j h0 (by omega) s m words.2.2.2.1).trans record
  refine ⟨kept, all.2.1, ?_, all.2.2.2.1⟩
  rw [kept, all.2.2.1]
  by_cases active : Shadow.far (Shadow7.sbP (start j)) 15 z
  · rw [LeaveJ7.Far.orient _ _ small active]
  · simp [active]

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.ActualHistory

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.HighZero
open Arithmetic Partial SkywalkNat
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}HighZero.result`: the next tick's upper A words are clean after StoreMapped. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z)))
    (top : ∀ q : Nat, Shadow7.a0P (start j) + 18 ≤ q → q ≤ (start j) + 30 + railP ((start j) + 15) → s.basis q = false)
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP ((start j) + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)) :
    ∀ i : Fin (railP ((start j) + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1)),
      (run (StoreMapped.program j) m s).basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val) = false := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have hR : railP ((start j) + 15) ≤ 258 := by unfold railP; split_ifs <;> omega
  have store := (StoreMapped.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flag := (BeforeStore.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2.2.2.2
  intro i
  have hi := i.isLt
  by_cases ext : Shadow7.a0P (start j) + 18 ≤ Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val
  · rw [storeMapped_keeps j h0 (by omega) (Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val) (by unfold Shadow7.leaveBox2; ((try unfold Wire at *); omega))]
    exact top _ ext (by ((try unfold Wire at *); omega))
  · have lim : Shadow7.lowsP (start j) + i.val < 18 := by omega
    have free : (LeaveJ7.row j ⟨Shadow7.lowsP (start j) + i.val, lim⟩).free = Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val := by
      rw [row_free, if_neg (by omega)]; exact (Nat.add_assoc _ _ _).symm
    rw [store (Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val) (not_low j _ (by ((try unfold Wire at *); omega))) (not_history j _ (by ((try unfold Wire at *); omega))),
      flag (Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val) (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))]
    rw [← free]
    exact row_done j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events ⟨Shadow7.lowsP (start j) + i.val, lim⟩ (by
      rw [free]; simp only [LeaveJ7.smallM, List.mem_map, List.mem_range, not_exists, not_and]
      intro k hk e; ((try unfold Wire at *); omega))

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.HighZero

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.BoundaryRails
open Arithmetic Partial SkywalkNat MappedCompressed
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}BoundaryRails.lowFrame`: the block's short words are not touched by the leave. -/
theorem lowFrame (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (i : Fin (Shadow7.sbP (start j))) (s : State) (m : List Bool) :
    let v := run (Shadow7.leaveP j) m s
    v.basis ((start j) + 31 + i.val) = s.basis ((start j) + 31 + i.val) ∧ v.basis (786 + i.val) = s.basis (786 + i.val) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have hi := i.isLt
  exact ⟨leave_keeps j h0 (by omega) _ (by unfold Shadow7.leaveBox2; ((try unfold Wire at *); omega)) m s,
    leave_keeps j h0 (by omega) _ (by unfold Shadow7.leaveBox2; ((try unfold Wire at *); omega)) m s⟩

/-- dadon's `Leave{s}BoundaryRails.result`: after the leave, the next tick's rails read the stock reference. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z)))
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP ((start j) + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)) (xs : List (Bool × Bool)) (len : xs.length = 15)
    (historyOK : Shadow.far (Shadow7.sbP (start j)) 15 z → StairArchiveTrace.chain (decide (2^(Shadow7.sbP (start j)) ≤ z.u)) xs)
    (first : Shadow.far (Shadow7.sbP (start j)) 15 z → decide (2^(Shadow7.sbP (start j)) ≤ z.u) = false →
      ∀ i (h : i < xs.length), i ≤ IntegerHigh.wait 15 z.u → xs[i].2 = decide (i = IntegerHigh.wait 15 z.u))
    (saved : (Close.events j).map (fun p => s.basis p.1) = (xs.take 5).map Prod.snd)
    (far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
    (side : s.basis (Shadow7.e0P (start j) + 4) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u)))
    (highZero : ∀ q : Nat, Shadow7.a0P (start j) + 18 ≤ q → q ≤ (start j) + 30 + railP ((start j) + 15) → s.basis q = false)
    (raw : State) (input : let a := step^[15] z
       SkywalkIntegerInput (WideWords.L j) (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis) :
    let o := pullState (OB5.sig ((start j) + 14)) raw
    let out := run (Shadow7.leaveP j) m s
    (∀ i : Fin (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1), out.basis ((start j) + 31 + i.val) = o.basis ((start j) + 31 + i.val) ∧
      out.basis (786 + i.val) = o.basis (786 + i.val)) ∧
    ∀ i : Fin (railP ((start j) + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1)), out.basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val) = false ∧
      out.basis (Shadow7.b0P (start j) + Shadow7.lowsP (start j) + i.val) =
        (if o.basis ((start j) + 30) then o.basis (Shadow7.b0P (start j) + Shadow7.lowsP (start j) + i.val) else o.basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have hR : Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1 ≤ railP ((start j) + 15) := by ((try unfold Wire at *); omega)
  let a := step^[15] z
  let h := step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)
  let o := pullState (OB5.sig ((start j) + 14)) raw
  have word := EndWords.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have whole := Whole.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have cleared := HighZero.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events highZero nextSmall bound
  have orient : o.basis ((start j) + 30) = G := by
    have geo : (WideWords.L j).previous = OB5.sig ((start j) + 14) ((start j) + 30) := by
      show MappedCompressed.base (skywalkPoolPreviousId ((start j) + 15)) = _
      unfold skywalkPoolPreviousId MappedCompressed.base OB5.sig
      rw [if_neg (by omega), if_neg (by ((try unfold Wire at *); omega))]
      ((try unfold Wire at *); omega)
    change raw.basis (OB5.sig ((start j) + 14) ((start j) + 30)) = G
    rw [← geo]; exact input.2.2.1
  have law := LeaveShadowRails.retainedLow_shadow7 (Shadow7.sbP (start j)) z small.1 sg
  constructor
  · intro i
    have fit : i.val < railP ((start j) + 15) := by have := i.isLt; omega
    have ref := WideWords.wide j h0 (by omega) a G sg raw input ⟨i.val, fit⟩
    by_cases low : i.val < Shadow7.sbP (start j)
    · have hw := WideWords.short j h0 (by omega) h G sg s ready ⟨i.val, low⟩
      have untouched := lowFrame j h0 (by omega) ⟨i.val, low⟩ s m
      have spos := LeaveSignedCoordinates.sharedDigit _ _ (Shadow7.sbP (start j)) i.val law.2.1 (Nat.le_of_lt low)
      have smag := LeaveSignedCoordinates.sharedDigit _ _ (Shadow7.sbP (start j)) i.val law.2.2 (Nat.le_of_lt low)
      dsimp only at ref hw
      rw [law.1, spos, smag] at ref
      exact ⟨untouched.1.trans (hw.1.trans ref.1.symm), untouched.2.trans (hw.2.trans ref.2.symm)⟩
    · have hk : i.val - Shadow7.sbP (start j) < Shadow7.lowsP (start j) + 1 := by have := i.isLt; omega
      have vals := word.2.2.2.2.1 ⟨i.val - Shadow7.sbP (start j), hk⟩
      dsimp only at ref vals
      rw [show Shadow7.sbP (start j) + (i.val - Shadow7.sbP (start j)) = i.val by omega,
        show Shadow7.a0P (start j) - 1 + (i.val - Shadow7.sbP (start j)) = (start j) + 31 + i.val by omega,
        show Shadow7.b0P (start j) - 1 + (i.val - Shadow7.sbP (start j)) = 786 + i.val by omega] at vals
      exact ⟨vals.1.trans ref.1.symm, vals.2.trans ref.2.symm⟩
  · intro i
    have hi := i.isLt
    have ref := WideWords.wide j h0 (by omega) a G sg raw input ⟨Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1 + i.val, by omega⟩
    dsimp only at ref
    rw [show (start j) + 31 + (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1 + i.val) = Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val by omega,
      show 786 + (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + 1 + i.val) = Shadow7.b0P (start j) + Shadow7.lowsP (start j) + i.val by omega] at ref
    have free : (run (Shadow7.leaveP j) m s).basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val) = false := by
      rw [whole.2.2.2.2, (Relocated.upperMap j h0 (by omega) i.val hi).2]
      exact (Function.update_of_ne (by ((try unfold Wire at *); omega)) _ _).trans (cleared i)
    refine ⟨free, ?_⟩
    change (run (Shadow7.leaveP j) m s).basis (Shadow7.b0P (start j) + Shadow7.lowsP (start j) + i.val) =
      (if o.basis ((start j) + 30) then o.basis (Shadow7.b0P (start j) + Shadow7.lowsP (start j) + i.val) else o.basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val))
    rw [orient, word.2.2.2.2.2 i.val hi]
    cases G <;> simpa only [Bool.false_eq_true, ite_false, ite_true] using (by first | exact ref.1.symm | exact ref.2.symm)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.BoundaryRails

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.BoundaryClean
open Arithmetic Partial SkywalkNat
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}BoundaryClean.zeros` (225: 1556..1712, 1719..1812; 255 adds the freed B top 1029..1042 and
stops below its own moved history at 2055-s). -/
def zeros (j : Fin 23) : List Nat :=
  List.range' 1556 (Shadow7.e0P ((start j) + 15) + 3 - 1556) ++
  List.range' (Shadow7.e0P ((start j) + 15) + 9) (min 1813 (2055 - (start j)) - (Shadow7.e0P ((start j) + 15) + 9)) ++
  List.range' (bTopP ((start j) + 15) + 1) (bTopP (start j) - bTopP ((start j) + 15))

/-- dadon's `retired` (255/210: plus the live bank sites above the next rail, `F < 2^(R(s+15)-sb-1)`). -/
def retired (j : Fin 23) (q : Nat) : Prop :=
  q = Shadow7.e0P (start j) + 4 ∨ (q ≠ Shadow7.e0P (start j) + 4 ∧ q ∉ RailPair.sites (Close.low j) ∧ q ∉ Close.history j ∧
  (q = 1556 ∨ (q ≠ 1556 ∧ q ≠ 1557 ∧ q ≠ 1558 ∧
   ((q ∈ CoreCheckpoint.targets j ∧ q ∉ LeaveJ7.smallM j) ∨
    ∃ i : Fin (railP (start j) - railP ((start j) + 15)), q = LeaveJ7.live j (Shadow7.wpP (start j) + 15 - (railP (start j) - railP ((start j) + 15)) + i.val)))))

/-- Core-checkpoint targets by intervals (scratch, raw sites, the bank head `e0..e0+2`, the B words). -/
theorem mem_targets (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Nat)
    (h : (1559 ≤ q ∧ q < 1598) ∨ (1613 ≤ q ∧ q < Shadow7.e0P (start j) + 3) ∨ (Shadow7.e0P (start j) + 8 ≤ q ∧ q < min 1813 (2055 - (start j))) ∨
      (Shadow7.b0P (start j) ≤ q ∧ q < Shadow7.b0P (start j) + 15 + Shadow7.lowsP (start j))) : q ∈ CoreCheckpoint.targets j := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  simp only [CoreCheckpoint.targets, CoreCheckpoint.rawSites, CoreCheckpoint.magSites, LeaveJ7.fullM, List.mem_append,
    List.mem_range'_1, List.mem_map, List.mem_range, List.mem_finRange, true_and]
  rcases h with h | h | h | h
  · left; left; left; exact ⟨h.1, by first | omega | (unfold Wire; omega)⟩
  · by_cases lo : q < Shadow7.e0P (start j)
    · left; right; left; exact ⟨h.1, by first | omega | (unfold Wire; omega)⟩
    · left; left; right
      refine ⟨⟨q - Shadow7.e0P (start j), by first | omega | (unfold Wire; omega)⟩, ?_⟩
      rw [row_free, if_pos (by first | omega | (unfold Wire; omega))]; unfold Shadow7.bankW; rw [if_pos (by first | omega | (unfold Wire; omega))]; first | omega | (unfold Wire; omega)
  · left; right; right; exact ⟨h.1, by first | omega | (unfold Wire; omega)⟩
  · by_cases lo : q < Shadow7.b0P (start j) + 18
    · right; exact ⟨q - Shadow7.b0P (start j), by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩
    · left; left; right
      refine ⟨⟨q - Shadow7.b0P (start j) - 15, by first | omega | (unfold Wire; omega)⟩, ?_⟩
      rw [row_free, if_pos (by first | omega | (unfold Wire; omega))]; unfold Shadow7.bankW; rw [if_neg (by first | omega | (unfold Wire; omega)), if_pos (by first | omega | (unfold Wire; omega))]
      (first | omega | (unfold Wire; omega))

/-- A retired wire by intervals. -/
theorem retired_of (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Nat)
    (h : (1559 ≤ q ∧ q < 1598) ∨ (1613 ≤ q ∧ q < Shadow7.e0P (start j) + 3) ∨ (Shadow7.e0P (start j) + 8 ≤ q ∧ q < min 1813 (2055 - (start j))) ∨
      (Shadow7.b0P (start j) + Shadow7.lowsP (start j) ≤ q ∧ q < Shadow7.b0P (start j) + 15 + Shadow7.lowsP (start j))) : retired j q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have hne : q ≠ Shadow7.e0P (start j) + 4 := by (first | omega | (unfold Wire; omega))
  refine Or.inr ⟨hne, not_low j q (by (first | omega | (unfold Wire; omega))), not_history j q (by (first | omega | (unfold Wire; omega))),
    Or.inr ⟨by (first | omega | (unfold Wire; omega)), by (first | omega | (unfold Wire; omega)), by (first | omega | (unfold Wire; omega)),
      Or.inl ⟨mem_targets j h0 (by omega) q (by (first | omega | (unfold Wire; omega))), ?_⟩⟩⟩
  simp only [LeaveJ7.smallM, List.mem_map, List.mem_range, not_exists, not_and]
  intro k hk e; (first | omega | (unfold Wire; omega))

/-- dadon's `routed` (a kernel decide per block), from the relocation closed form. -/
theorem routed (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : ∀ (Q : Nat), Q ∈ zeros j → retired j (LeaveRelocation.source (Relocated.moves j) Q) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := Relocated.chain_geo w1 w3
  have hR : railP ((start j) + 15) ≤ railP (start j) ∧ railP (start j) ≤ railP ((start j) + 15) + 15 := by
    unfold railP; constructor <;> split_ifs <;> first | omega | (unfold Wire; omega)
  have fl := Relocated.src_flags _ w1 w3
  intro q hq
  simp only [zeros, List.mem_append, List.mem_range'_1] at hq
  show retired j (LeaveRelocation.source (Shadow7.movesP (start j)) q)
  rcases hq with (⟨lo, hi⟩ | ⟨lo, hi⟩) | ⟨lo, hi⟩
  · -- the scratch below the next tick's flags
    by_cases q1556 : q = 1556
    · subst q1556
      rw [Relocated.src_out _ w1 w3 1556 (Or.inr (Or.inl ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩))
        ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega), Or.inl (by first | omega | (unfold Wire; omega))⟩]
      exact Or.inr ⟨by first | omega | (unfold Wire; omega), not_low j _ (by (first | omega | (unfold Wire; omega))), not_history j _ (by first | omega | (unfold Wire; omega)), Or.inl rfl⟩
    by_cases q1557 : q = 1557
    · subst q1557; rw [fl.1]; exact retired_of j h0 (by omega) _ (Or.inr (Or.inl ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩))
    by_cases q1558 : q = 1558
    · subst q1558; rw [fl.2.1]; exact retired_of j h0 (by omega) _ (Or.inr (Or.inl ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩))
    by_cases pool : 1598 ≤ q ∧ q < 1598 + (Shadow7.wpP ((start j) + 15) - 3) - (Shadow7.wpP (start j) - Shadow7.lowsP (start j))
    · -- a pool bank wire: chain down to the bottom words
      have e : q = Shadow7.bankW (start j) (Shadow7.lowsP (start j) + (q - 1598 + (Shadow7.wpP (start j) - Shadow7.lowsP (start j)))) := by
        rw [show Shadow7.bankW (start j) (Shadow7.lowsP (start j) + (q - 1598 + (Shadow7.wpP (start j) - Shadow7.lowsP (start j)))) =
          (Relocated.bankPair (start j) (q - 1598 + (Shadow7.wpP (start j) - Shadow7.lowsP (start j)))).1 from rfl, hP _ (by first | omega | (unfold Wire; omega))]
        first | omega | (unfold Wire; omega)
      rw [e, Relocated.src_top _ w1 w3 (q - 1598 + (Shadow7.wpP (start j) - Shadow7.lowsP (start j))) (by first | omega | (unfold Wire; omega)) (fun h => by first | omega | (unfold Wire; omega))]
      exact retired_of j h0 (by omega) _ (Or.inr (Or.inr (Or.inr ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩)))
    rw [Relocated.src_out _ w1 w3 q (Or.inr (by first | omega | (unfold Wire; omega))) ⟨q1557, q1558, by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega), Or.inl (by first | omega | (unfold Wire; omega))⟩]
    by_cases live : 1598 ≤ q ∧ q < 1613
    · -- the live bank sites above the next rail (210: 1612; 255: 1599..1612)
      refine Or.inr ⟨by first | omega | (unfold Wire; omega), not_low j _ (by (first | omega | (unfold Wire; omega))), not_history j _ (by first | omega | (unfold Wire; omega)),
        Or.inr ⟨q1556, q1557, q1558, Or.inr ⟨⟨q - 1598 + Shadow7.wpP (start j) - (Shadow7.wpP (start j) + 15 - (railP (start j) - railP ((start j) + 15))), by first | omega | (unfold Wire; omega)⟩, ?_⟩⟩⟩
      unfold LeaveJ7.live Shadow7.bankW
      rw [if_neg (by first | omega | (unfold Wire; omega)), if_neg (by first | omega | (unfold Wire; omega)), if_neg (by first | omega | (unfold Wire; omega))]
      simp only [Fin.val_mk]
      (first | omega | (unfold Wire; omega))
    · exact retired_of j h0 (by omega) _ (by first | omega | (unfold Wire; omega))
  · -- above the next tick's flags
    by_cases f3 : q = Shadow7.e0P (start j) + 3
    · subst f3; rw [fl.2.2.2.1]; exact retired_of j h0 (by omega) _ (Or.inr (Or.inl ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩))
    by_cases f5 : q = Shadow7.e0P (start j) + 5
    · subst f5; rw [fl.2.2.1]; exact retired_of j h0 (by omega) _ (Or.inr (Or.inl ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩))
    by_cases f6 : q = Shadow7.e0P (start j) + 6
    · subst f6; rw [fl.2.2.2.2.2]; exact retired_of j h0 (by omega) _ (Or.inr (Or.inl ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩))
    by_cases f7 : q = Shadow7.e0P (start j) + 7
    · subst f7; rw [fl.2.2.2.2.1]; exact retired_of j h0 (by omega) _ (Or.inr (Or.inl ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩))
    rw [Relocated.src_out _ w1 w3 q (Or.inr (Or.inr (by first | omega | (unfold Wire; omega)))) ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega), f3, f5, f6, f7, Or.inr (by first | omega | (unfold Wire; omega))⟩]
    by_cases f4 : q = Shadow7.e0P (start j) + 4
    · exact Or.inl f4
    · exact retired_of j h0 (by omega) _ (by first | omega | (unfold Wire; omega))
  · -- the freed B top: chain down to the bottom words
    have e : q = Shadow7.bankW (start j) (Shadow7.lowsP (start j) + (q - (805 + Shadow7.sbP ((start j) + 15) + 15))) := by
      rw [show Shadow7.bankW (start j) (Shadow7.lowsP (start j) + (q - (805 + Shadow7.sbP ((start j) + 15) + 15))) =
        (Relocated.bankPair (start j) (q - (805 + Shadow7.sbP ((start j) + 15) + 15))).1 from rfl, hB _ (by first | omega | (unfold Wire; omega))]
      first | omega | (unfold Wire; omega)
    rw [e, Relocated.src_top _ w1 w3 (q - (805 + Shadow7.sbP ((start j) + 15) + 15)) (by first | omega | (unfold Wire; omega)) (fun h => by first | omega | (unfold Wire; omega))]
    exact retired_of j h0 (by omega) _ (Or.inr (Or.inr (Or.inr ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩)))

/-- dadon's `Leave{s}BoundaryClean.result`: the leave hands back a clean scratch. `narrow` is
`LeaveJ7.terminal_fit` (dadon 210/255 only; implied by `bound` when the rail keeps its width). -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::LeaveJ7.fullC, s.basis q = false)
    (temp : ∀ p ∈ LeaveJ7.longPairs j, s.basis p.2 = false)
    (odd : z.v % 2 = 1) (room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ LeaveJ7.carries j, s.basis q = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bank : regValue (LeaveJ7.ys j) s.basis = if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ LeaveJ7.watched j, s.basis q = false)
    (par : LeaveJ7.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) →
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z)))
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP ((start j) + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)) (xs : List (Bool × Bool)) (len : xs.length = 15)
    (historyOK : Shadow.far (Shadow7.sbP (start j)) 15 z → StairArchiveTrace.chain (decide (2^(Shadow7.sbP (start j)) ≤ z.u)) xs)
    (first : Shadow.far (Shadow7.sbP (start j)) 15 z → decide (2^(Shadow7.sbP (start j)) ≤ z.u) = false →
      ∀ i (h : i < xs.length), i ≤ IntegerHigh.wait 15 z.u → xs[i].2 = decide (i = IntegerHigh.wait 15 z.u))
    (saved : (Close.events j).map (fun p => s.basis p.1) = (xs.take 5).map Prod.snd)
    (far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
    (side : s.basis (Shadow7.e0P (start j) + 4) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u)))
    (quiet : ∀ q ∈ CoreCheckpoint.rawSites j, s.basis q = false)
    (narrow : LeaveJ7.TrueMiddle.F j z < 2^(railP ((start j) + 15) - (Shadow7.sbP (start j) + 1))) :
    ∀ q ∈ zeros j, (run (Shadow7.leaveP j) m s).basis q = false := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have hR : railP ((start j) + 15) ≤ railP (start j) := by unfold railP; split_ifs <;> first | omega | (unfold Wire; omega)
  have whole := Whole.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store := (StoreMapped.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags := BeforeStore.result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  intro q hq
  rw [whole.2.2.2.2]
  rcases routed j h0 (by omega) q hq with eq | ⟨diff, out, hist, src⟩
  · rw [eq]; simp [writeBit]
  simp only [writeBit, Function.update_of_ne diff]
  rw [store _ out hist]
  rcases src with eq | ⟨x, y, z', origin⟩
  · rw [eq]; exact flags.2.1
  · rcases origin with ⟨mem, notM⟩ | ⟨i, eq⟩
    · exact (flags.2.2.2.2.2.2 _ x y z').trans
        (core_done j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events quiet _ mem notM)
    · have hi := i.isLt
      rw [eq, flags.2.2.2.2.2.1 (Shadow7.wpP (start j) + 15 - (railP (start j) - railP ((start j) + 15)) + i.val) (by first | omega | (unfold Wire; omega))]
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le narrow (Nat.pow_le_pow_right (by decide) (by first | omega | (unfold Wire; omega)))

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.BoundaryClean

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.AssembleCut
/-- TEMP copy of par-c2's generic `Leave{s}AssembleCut.leftovers` (agreed 23:30Z); delete when par-c2's lands. -/
def leftovers (j : Fin 23) (q : Wire) : Prop :=
  ((start j) + 15 ≤ q ∧ q < (start j) + 31) ∨ (1044 + (start j) ≤ q ∧ q < 1059 + (start j)) ∨ ReleasedOrigin.releasedSite j q ∨
  (2055 ≤ q + (start j) ∧ q + (start j) ≤ 2069 ∧ q ≤ 1812)
end ECDSAAdd.Entrant.StairPacket.LeaveJ7.AssembleCut

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
attribute [local irreducible] run SkywalkNat.step
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

/-- dadon's `Leave{s}FrameHistory.result`: on the leftovers the leave's output equals the stock reference. The
`extra` hypothesis (dadon 210/255) is `ReleasedActual.agree`; the census decide over Fin 1813 is a case split. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (x p : Nat) (good : Bounds x p) (raw s : State) (m : List Bool) (g sg : Bool)
    (domain : Domain (start j) x p raw)
    (input : InputAt (start j) (encode g sg (unsigned (start j) x p).u (unsigned (start j) x p).v) raw)
    (record : Shadow7.physicalCells j s = SkywalkTrace.trace 15 (encode g sg (unsigned (start j) x p).u (unsigned (start j) x p).v))
    (kept : Shadow7.physicalCells j (run (Shadow7.leaveP j) m s) = Shadow7.physicalCells j s)
    (extra : ∀ q : Wire, ReleasedOrigin.releasedSite j q → (run (Shadow7.leaveP j) m s).basis q = (origin (start j) raw s).basis q) :
    ∀ q, AssembleCut.leftovers j q → (run (Shadow7.leaveP j) m s).basis q = (origin (start j) raw s).basis q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  let out := run (Shadow7.leaveP j) m s
  let o := origin (start j) raw s
  have geo : ∀ i : Fin 15, windowNet j (IntegerPacket.ports (Shadow7.shape j) i.val).a0 = (start j) + 16 + i.val ∧
      windowNet j (IntegerPacket.ports (Shadow7.shape j) i.val).history = LeaveJ7.swaps j i.val := by
    intro i
    have hi := i.isLt
    constructor
    · show OB5.sig ((start j) + 14) ((start j) + i.val + 16) = _
      unfold OB5.sig; rw [if_neg (by (first | omega | (unfold Wire; omega)))]; (first | omega | (unfold Wire; omega))
    · show OB5.sig ((start j) + 14) ((start j) + i.val + 16 + 1028) = OB5.sig ((start j) + 14) ((start j) + 1044 + i.val)
      congr 1; first | omega | (unfold Wire; omega)
  have agree (i : Fin 15) : out.basis ((start j) + 16 + i.val) = o.basis ((start j) + 16 + i.val) ∧
      out.basis (LeaveJ7.swaps j i.val) = o.basis (LeaveJ7.swaps j i.val) := by
    have old := recorded_equal (start j) j x p (by first | omega | (unfold Wire; omega)) (places j) good raw s domain g sg input record i
    have now := congrArg (fun a => StairArchiveRaw.read a i.val) kept
    change StairArchiveRaw.read (readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)) i.val =
      StairArchiveRaw.read (readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis)) i.val at now
    rw [read_cells _ _ _ _ _ i.isLt, read_cells _ _ _ _ _ i.isLt, Nat.zero_add] at now
    have eq := now.trans old
    change (out.basis (windowNet j (IntegerPacket.ports (Shadow7.shape j) i.val).a0),
        out.basis (windowNet j (IntegerPacket.ports (Shadow7.shape j) i.val).history)) =
      (o.basis (windowNet j (IntegerPacket.ports (Shadow7.shape j) i.val).a0),
        o.basis (windowNet j (IntegerPacket.ports (Shadow7.shape j) i.val).history)) at eq
    rw [(geo i).1, (geo i).2] at eq
    exact ⟨congrArg Prod.fst eq, congrArg Prod.snd eq⟩
  have inSites : (start j) + 15 ∈ sites (start j) := by
    apply (mem_sites (i := (start j)) (by first | omega | (unfold Wire; omega)) ((start j) + 15)).mpr
    rw [show OB5.sig ((start j) + 14) ((start j) + 15) = (start j) + 15 by
      unfold OB5.sig; rw [if_neg (by (first | omega | (unfold Wire; omega)))]]
    have w := old_window (i := (start j)) (by first | omega | (unfold Wire; omega))
    have c : 1 ≤ oldCount (start j) := by unfold oldCount; split_ifs <;> first | omega | (unfold Wire; omega)
    unfold oldSites
    refine List.mem_flatMap.mpr ⟨(start j) - 1, List.mem_range'_1.mpr ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, MappedCompressed.base]
    first | omega | (unfold Wire; omega)
  have previous : out.basis ((start j) + 15) = o.basis ((start j) + 15) := by
    rw [show o.basis ((start j) + 15) = s.basis ((start j) + 15) from inside _ _ _ _ inSites]
    exact leave_keeps j h0 (by omega) ((start j) + 15) (by unfold Shadow7.leaveBox2; (first | omega | (unfold Wire; omega))) m s
  intro q residual
  unfold AssembleCut.leftovers at residual
  unfold Wire at residual
  rcases residual with ⟨lo, hi⟩ | ⟨lo, hi⟩ | rel | ⟨lo, hi, top⟩
  · by_cases e : (q:Nat) = (start j) + 15
    · rw [e]; exact previous
    · have a := (agree ⟨q - ((start j) + 16), by first | omega | (unfold Wire; omega)⟩).1
      simp only at a
      rwa [show (start j) + 16 + (q - ((start j) + 16)) = q by first | omega | (unfold Wire at *; omega)] at a
  · by_cases moved : 1301 ≤ (q:Nat)
    · exact extra q (by unfold ReleasedOrigin.releasedSite; exact Or.inr (Or.inr (Or.inl ⟨moved, by first | omega | (unfold Wire; omega)⟩)))
    · have a := (agree ⟨q - ((start j) + 1044), by first | omega | (unfold Wire; omega)⟩).2
      simp only at a
      rwa [show LeaveJ7.swaps j (q - ((start j) + 1044)) = q by
        unfold LeaveJ7.swaps OB5.sig; rw [if_neg (by (first | omega | (unfold Wire at *; omega)))]; first | omega | (unfold Wire at *; omega)] at a
  · exact extra q rel
  · have a := (agree ⟨2069 - (start j) - q, by first | omega | (unfold Wire; omega)⟩).2
    simp only at a
    rwa [show LeaveJ7.swaps j (2069 - (start j) - q) = q by
      unfold LeaveJ7.swaps OB5.sig; rw [if_pos (by (first | omega | (unfold Wire; omega)))]; first | omega | (unfold Wire; omega)] at a

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.FrameHistory

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.ReleasedActual
open Arithmetic MappedCompressed WideReference Partial
attribute [local irreducible] run SkywalkNat.step
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

/-- dadon's `Leave{s}ReleasedActual.agree` (210/255), for every window block: on the released sites the leave's
output equals the stock reference. The window side (`pre`: the A top wire and the sig band are clean before the
leave) comes from par-c2's NativeJ facts (dadon: `upper_clear` and the stage fields). -/
theorem agree (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (x p : Nat) (good : Bounds x p) (raw v : State) (dom : Domain (start j) x p raw) (m : List Bool)
    (pre : ∀ q : Wire, (railP ((start j) + 15) < railP (start j) ∧ q = (start j) + 31 + railP ((start j) + 15)) ∨ (1301 ≤ q ∧ q ≤ 1058 + (start j)) ∨
      (369 ≤ start j ∧ 1302 ≤ q + start j ∧ q ≤ 933) → v.basis q = false)
    (clear : ∀ q ∈ BoundaryClean.zeros j, (run (Shadow7.leaveP j) m v).basis q = false) :
    ∀ q : Wire, ReleasedOrigin.releasedSite j q → (run (Shadow7.leaveP j) m v).basis q = (origin (start j) raw v).basis q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have w3 : start j ≤ 375 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have hR : railP ((start j) + 15) ≤ railP (start j) := by unfold railP; split_ifs <;> first | omega | (unfold Wire; omega)
  intro q site
  rw [ReleasedOrigin.released j h0 (by omega) x p good raw v dom q site]
  have site' := site
  unfold ReleasedOrigin.releasedSite at site'
  rcases site' with ⟨shrink, e⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨t369, lo, hi⟩
  · rw [leave_keeps j h0 (by omega) q (by unfold Shadow7.leaveBox2; (first | omega | (unfold Wire; omega))) m v]
    exact pre q (Or.inl ⟨shrink, e⟩)
  · exact clear q (by simp only [BoundaryClean.zeros, List.mem_append, List.mem_range'_1]; (first | omega | (unfold Wire; omega)))
  · rw [leave_keeps j h0 (by omega) q (by unfold Shadow7.leaveBox2; (first | omega | (unfold Wire; omega))) m v]
    exact pre q (Or.inr (Or.inl ⟨lo, hi⟩))
  · rw [leave_keeps j h0 (by omega) q (by unfold Shadow7.leaveBox2; (first | omega | (unfold Wire; omega))) m v]
    exact pre q (Or.inr (Or.inr ⟨t369, lo, hi⟩))

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.ReleasedActual

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission
open Arithmetic Partial SkywalkNat
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}Admission.Inputs.roundtrip`. -/
theorem Inputs.roundtrip {j : Fin 23} (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) {s : State} {z : SkywalkNat.State}
    {g0 s0 : Bool} (h : Inputs j s z g0 s0) (m n : List Bool) : run (Shadow7.leaveInvP j) n (run (Shadow7.leaveP j) m s) = s := by
  let u := flags z g0 s0
  let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par := RecordedParity.result j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have ph (o : List Bool) : (run (Shadow7.leaveP j) o s).phase = s.phase :=
    (Whole.result j h0 (by omega) s o z u.1 u.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank
      h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.bound xs (SkywalkTrace.trace_length _ _)
      (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
      ev.1 h.far h.side).1
  exact Roundtrip.result j h0 (by omega) s m n z u.1 u.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding
    h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.bound ph (native_carryJ j h0 (by omega) _ s h.ready) h.extra

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission

