import ECDSAAdd.Framework.RunAppendAgreement
import ECDSAAdd.Submission.Entrant.BOptimizations
import ECDSAAdd.Submission.Entrant.StairSideA
import ECDSAAdd.Submission.Entrant.Window
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.Stair44Stock
import Mathlib.Tactic
import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Submission.Entrant.CRT
import ECDSAAdd.Submission.Entrant.FredCut
import ECDSAAdd.Submission.Entrant.OddField
import ECDSAAdd.Submission.Entrant.OddFieldC
import ECDSAAdd.Framework.Syntax
import ECDSAAdd.Framework.Semantics
import ECDSAAdd.Framework.RecordedPaths
import ECDSAAdd.Framework.MeasuredLocality

-- ==== b60: field bank 13 (window block at tick 60): `starts` of StairSideA begins at 16; packet 13 is safe too ====
section
namespace ECDSAAdd.Entrant.StairArchiveInactive
open Arithmetic MappedCompressed ArchiveFieldScratch StairPhysicalLayout
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

theorem b60bank : (safe 13 false && safe 13 true) = true := by decide +kernel
def starts60 : List Nat := 13 :: starts

attribute [local irreducible] packet wires preimage cover savedSites

theorem packet_avoids60 (j : Nat) (hj : j∈starts60) (d second : Bool)
    (q : Wire) (save : q∈savedSites j second) :
    q∉wires (packet d (if second then j+1 else j)) := by
  rcases List.mem_cons.mp hj with e | h
  · subst e
    intro used
    have pair := b60bank
    have pass : safe 13 second = true := by
      simp only [Bool.and_eq_true] at pair
      cases second
      · exact pair.1
      · exact pair.2
    let k := if second then 13+1 else 13
    have hk : k<102 := by dsimp only [k]; split <;> omega
    change (savedSites 13 second).all (fun z => decide (preimage k z ∉ cover k)) = true at pass
    have exc : preimage k q ∉ cover k := of_decide_eq_true (List.all_eq_true.mp pass q save)
    exact exc (original d k hk used)
  · exact packet_avoids j h d second q save

end ECDSAAdd.Entrant.StairArchiveInactive
end

-- Field bank 10 (window block at tick 45): packet 10 is safe alongside starts60.
section
namespace ECDSAAdd.Entrant.StairArchiveInactive
open Arithmetic MappedCompressed ArchiveFieldScratch StairPhysicalLayout
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

theorem bank10 : (safe 10 false && safe 10 true) = true := by decide +kernel
def starts10 : List Nat := 10 :: starts60

attribute [local irreducible] packet wires preimage cover savedSites

theorem packet_avoids10 (j : Nat) (hj : j∈starts10) (d second : Bool)
    (q : Wire) (save : q∈savedSites j second) :
    q∉wires (packet d (if second then j+1 else j)) := by
  rcases List.mem_cons.mp hj with e | h
  · subst e
    intro used
    have pair := bank10
    have pass : safe 10 second = true := by
      simp only [Bool.and_eq_true] at pair
      cases second
      · exact pair.1
      · exact pair.2
    let k := if second then 10+1 else 10
    have hk : k<102 := by dsimp only [k]; split <;> omega
    change (savedSites 10 second).all (fun z => decide (preimage k z ∉ cover k)) = true at pass
    have exc : preimage k q ∉ cover k := of_decide_eq_true (List.all_eq_true.mp pass q save)
    exact exc (original d k hk used)
  · exact packet_avoids60 j h d second q save

end ECDSAAdd.Entrant.StairArchiveInactive
end


-- ==== crtf: CRT window ledger, part 1: leave algebra (before CRTWindowFrame and the chain) (staircase82, helpers/staircase82/crtf) ====
section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false



theorem split_ops (s : Nat) :
    Shadow7.leaveMoveOps s = CRTBarrel.beforeReference s ++ (Shadow7.leaveBarrel s ++ CRTBarrel.afterReference s) := by
  simp only [Shadow7.leaveMoveOps, CRTBarrel.beforeReference, CRTBarrel.afterReference, List.append_assoc]

theorem forward_append (a b : List Gate) :
    GateMirror.forward (a ++ b) = GateMirror.forward a ++ GateMirror.forward b := by
  simp only [GateMirror.forward, List.map_append]

theorem inverse_append (a b : List Gate) : inverse (a ++ b) = inverse b ++ inverse a := by
  simp only [inverse, List.map_append, List.reverse_append]

/-- The blocks whose leave is the CRT barrel leave (`CRTBarrel.leave`'s guard): every block 1..22 of the exit-420
window. -/
def crtBlocks (j : Fin 26) : Bool := j.val ≤ 24

theorem inBlocks_iff (j : Fin 26) : crtBlocks j = true ↔ (j.val ≤ 24) := by
  simp only [crtBlocks, decide_eq_true_eq]

/-! Counts. -/

/-- The rebuilt leave's prefix and suffix carry the Shadow7 move leave's counts minus its barrel stage. -/
-- ==== FlagCut57 wired (credited to ercumentyildirim ae9d602d) ====
theorem parts_counts (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (CRTBarrel.before (start j))) +
      toffoliCount (GateMirror.forward (CRTBarrel.afterPart (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3*Shadow7.lowsP (start j) + 97 ∧
    toffoliCount (inverse (CRTBarrel.afterPart (start j))) + toffoliCount (inverse (CRTBarrel.before (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 129 ∧
    measurementCount (GateMirror.forward (CRTBarrel.before (start j))) +
      measurementCount (GateMirror.forward (CRTBarrel.afterPart (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 89 ∧
    measurementCount (inverse (CRTBarrel.afterPart (start j))) +
      measurementCount (inverse (CRTBarrel.before (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 57 ∧
    gateSlots (GateMirror.forward (CRTBarrel.before (start j))) +
      gateSlots (GateMirror.forward (CRTBarrel.afterPart (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 10*Shadow7.lowsP (start j) + 646 + 3*Shadow7.wpP (start j + 15) ∧
    gateSlots (inverse (CRTBarrel.afterPart (start j))) + gateSlots (inverse (CRTBarrel.before (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 11*Shadow7.lowsP (start j) + 614 + 3*Shadow7.wpP (start j + 15) := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := ScanRowGordo.before5Row_counts j (by omega)
  dsimp only [CRTBarrel.before, CRTBarrel.afterPart] at *
  obtain ⟨t1, t2, m1, m2, s1, s2⟩ := Shadow7.leaveMove_counts j (by omega) (by omega)
  obtain ⟨b1, b2, c1, c2, d1, d2⟩ := (Shadow7.counts_leaveBarrel (start j)).programs
  rw [Shadow7.leaveMoveP, split_ops, forward_append, forward_append] at t1 m1 s1
  rw [Shadow7.leaveMoveInvP, split_ops, inverse_append, inverse_append] at t2 m2 s2
  simp only [toffoliCount_append, measurementCount_append, gateSlots_append] at t1 t2 m1 m2 s1 s2
  obtain ⟨f1,f2,g1,g2,h1,h2⟩ := DeadJoin.all_local_deltas57 j (by omega)
  obtain ⟨k1,k2,k3,k4,k5,k6⟩ := DeadJoin.after7K_counts j (by omega)
  have afterEq : DeadJoin.afterReference (start j) = CRTBarrel.afterReference (start j) := by rfl
  rw [afterEq] at f1 f2 g1 g2 h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · clear * - j t1 b1 f1 r1 k1
    omega
  · clear * - j t2 b2 f2 r2 k2
    omega
  · clear * - j m1 c1 g1 r3 k3
    omega
  · clear * - j m2 c2 g2 r4 k4
    omega
  · clear * - j s1 d1 h1 r5 k5
    omega
  · clear * - j s2 d2 h2 r6 k6
    omega

/-- The rebuilt leave and its mirror: the Shadow7 counts with the barrel stage replaced by the CRT barrel. -/
theorem leave_metrics (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    toffoliCount (CRTBarrel.leave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3*Shadow7.lowsP (start j) + 97 + CRTBarrel.barrelT (start j) false ∧
    toffoliCount (CRTBarrel.unleave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 129 + CRTBarrel.barrelT (start j) true ∧
    measurementCount (CRTBarrel.leave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 89 + CRTBarrel.barrelM (start j) false ∧
    measurementCount (CRTBarrel.unleave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 57 + CRTBarrel.barrelM (start j) true ∧
    gateSlots (CRTBarrel.leave j) = 6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 10*Shadow7.lowsP (start j) + 646 +
      3*Shadow7.wpP (start j + 15) + CRTBarrel.barrelSlots (start j) false ∧
    gateSlots (CRTBarrel.unleave j) = 6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 11*Shadow7.lowsP (start j) + 614 +
      3*Shadow7.wpP (start j + 15) + CRTBarrel.barrelSlots (start j) true := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := parts_counts j h0 h1
  obtain ⟨f1, f2, f3⟩ := CRTBarrel.barrel_metrics j h0 h1 false
  obtain ⟨g1, g2, g3⟩ := CRTBarrel.barrel_metrics j h0 h1 true
  simp only [CRTBarrel.leave, CRTBarrel.unleave, h1, ↓reduceIte, toffoliCount_append,
    measurementCount_append, gateSlots_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem leave_other (j : Fin 26) (h : ¬(j.val ≤ 24)) :
    CRTBarrel.leave j = Shadow7.leaveMoveP j ∧ CRTBarrel.unleave j = Shadow7.leaveMoveInvP j := by
  simp only [CRTBarrel.leave, CRTBarrel.unleave, h, ↓reduceIte, and_self]

/-! Coverage and physicality of the rebuilt leaves. -/

theorem barrel_box (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (mir : Bool) :
    ∀ q ∈ wires (CRTBarrel.barrel (start j) mir), leaveBox (start j) q := by
  obtain ⟨w1, w2⟩ := start_win7 j (Nat.zero_le _) (by omega)
  intro q hq
  rcases CRTBarrel.barrel_wires j h0 h1 mir q hq with ⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩ | ht
  · have bc := Shadow7.bank_cases w1 (by omega) hi
    have r := Shadow7.rail_win w1 (by omega)
    unfold leaveBox; ((try unfold Wire at *); omega)
  · have pc := Shadow7.pool_cases (i := 17+k) w1 (by omega)
    unfold leaveBox; ((try unfold Wire at *); omega)
  · have t : ∀ q ∈ tagsP, 1556 ≤ q ∧ q ≤ 1576 := by decide
    have := t q ht; unfold leaveBox; ((try unfold Wire at *); omega)

theorem parts_box (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    AllW (leaveBox (start j)) (CRTBarrel.before (start j)) ∧ AllW (leaveBox (start j)) (CRTBarrel.afterPart (start j)) := by
  have a := Shadow7.allW_leaveMove (start j) (Shadow7.leaveOps_box j (by omega) (by omega))
  rw [split_ops, allW_append_iff, allW_append_iff] at a
  exact ⟨ScanRowGordo.before5Row_allW j h1 (DeadJoin.before5_allW j h1 (show AllW _ (DeadJoin.beforeAll (start j)) from FlagLeave.cut_allW (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 2 (DeadJoin.beforeScan (start j)) (DeadJoin.before_scan_allW _ a.1))),
    DeadJoin.after7K_allW j h1 (show AllW _ (DeadJoin.afterAll (start j)) from FlagLeave.cut_allW (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 1 (DeadJoin.afterShort (start j)) (DeadJoin.after_short_allW j h1 a.2.2))⟩

theorem leave_eq (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    CRTBarrel.leave j = GateMirror.forward (CRTBarrel.before (start j)) ++ CRTBarrel.barrel (start j) false ++
      GateMirror.forward (CRTBarrel.afterPart (start j)) ∧
    CRTBarrel.unleave j = inverse (CRTBarrel.afterPart (start j)) ++ CRTBarrel.barrel (start j) true ++
      inverse (CRTBarrel.before (start j)) := by
  simp only [CRTBarrel.leave, CRTBarrel.unleave, h1, ↓reduceIte, and_self]

/-- `WindowCovered.leaveBox_dom` through block 22 (start 405), as `WindowCovered7.leaveBox_dom405`. -/
theorem cov_of_box {P : Program} {s : Nat} (lo : 45 ≤ s) (hi : s ≤ 405) (h : ∀ q ∈ wires P, leaveBox s q) :
    WindowCovered.CoveredW P := by
  intro q hq
  have b := h q hq
  rw [WindowCovered.dom_iff]; unfold leaveBox at b; omega

theorem leave_cov (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    WindowCovered.CoveredW (CRTBarrel.leave j) ∧ WindowCovered.CoveredW (CRTBarrel.unleave j) := by
  obtain ⟨pb, pa⟩ := parts_box j h0 h1
  obtain ⟨bf, bi⟩ := allW_programs pb
  obtain ⟨af, ai⟩ := allW_programs pa
  obtain ⟨w1, w2⟩ := start_win7 j (Nat.zero_le _) (by omega)
  have cbf := cov_of_box w1 (by omega) bf
  have caf := cov_of_box w1 (by omega) af
  have cbi := cov_of_box w1 (by omega) bi
  have cai := cov_of_box w1 (by omega) ai
  have cb0 := cov_of_box w1 (by omega) (barrel_box j h0 h1 false)
  have cb1 := cov_of_box w1 (by omega) (barrel_box j h0 h1 true)
  rw [(leave_eq j h0 h1).1, (leave_eq j h0 h1).2]
  exact ⟨WindowCovered.appW (WindowCovered.appW cbf cb0) caf, WindowCovered.appW (WindowCovered.appW cai cb1) cbi⟩

def forward45plus1 (d : Bool) : Program := forwardW CRTBarrel.params d first WindowParams7.rest7

def reverse45plus1 (d : Bool) : Program := reverseW CRTBarrel.params d first WindowParams7.rest7

theorem assembly (d : Bool) : forward45plus1 d = forwardW CRTBarrel.params d first WindowParams7.rest7 := rfl

theorem unwind_assembly (d : Bool) : reverse45plus1 d = reverseW CRTBarrel.params d first WindowParams7.rest7 := rfl

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

/- Inlined from ShadowLeaveSuffix; provenance retained from022799f6. -/
section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror RecordedQuantum HighBankFirstHit LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-! Selector semantics (dadon's `preparedState`, `selected`, `complete`, `clear`, `retiredFull`). -/

def fullPrefix (j : Fin 26) : List Gate :=
  leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++ Shadow7.fix5P (start j) (Shadow7.sbP (start j))

theorem far_ne (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (Shadow7.e0P (start j) + 3 : Wire) ≠ 1559 ∧ (Shadow7.e0P (start j) + 3 : Wire) ≠ 1560 := by
  have r := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
  unfold Wire; omega

theorem preparedState (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (v : BasisState)
    (small : Nat) (k : Mode) (mode : k = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) small)
    (a : s.basis 1559 = false) (b : s.basis 1560 = false)
    (input : ∀ q, q ≠ 1559 → q ≠ 1560 → s.basis q = (before (ports j) false k q).read v)
    (exchange : right k = true → ∀ i < 15, i ≤ key k → s.basis (swaps j i) = decide (i = key k)) :
    run (GateMirror.forward (fullPrefix j)) m s =
      ⟨s.phase, fun q => (sim (prepare j) (LeaveSelector.start (ports j) false k) q).read v⟩ := by
  rw [fullPrefix, prefix_parts j h0 (by omega)]
  exact allSites (ports j) _ _ false _ (swaps j) (hit_sites j h0 (by omega)) (fun i hi => swaps_apart j h0 (by omega) i hi) s m v small
    (far_ne j h0 (by omega)).1 (far_ne j h0 (by omega)).2 a b k mode input exchange

theorem selected (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (v : BasisState)
    (small : Nat) (k : Mode) (mode : k = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) small)
    (a : s.basis 1559 = false) (b : s.basis 1560 = false)
    (input : ∀ q, q ≠ 1559 → q ≠ 1560 → s.basis q = (before (ports j) false k q).read v)
    (exchange : right k = true → ∀ i < 15, i ≤ key k → s.basis (swaps j i) = decide (i = key k)) (i : Fin 16) :
    (run (GateMirror.forward (fullPrefix j)) m s).basis (tagsP.getD i 0) = (enabled k && decide (i.val = key k)) := by
  rw [preparedState j h0 (by omega) s m v small k mode a b input exchange]
  exact congrArg (Expr.read v) (tagCertificate j h0 (by omega) k i)

/-- dadon's `Leave{s}Selector.clear` (forward): the retired selector word Shadow7.restores the selector wires. -/
theorem clear (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀ q, s.basis q = (post (ports j) (prepare j) false k q).read v) :
    run ((retire j).map Op.exit) m s = ⟨s.phase, fun q => (restored (ports j) false k q).read v⟩ :=
  cleanup (ports j) (prepare j) (retire j) false k s m v input (cleanCert j h0 (by omega) k)
    (fun o h => of_decide_eq_true (List.all_eq_true.mp (foot_ok j h0 (by omega)) o h))

/-- dadon's `Leave{s}Selector.retiredFull` (forward): `fix11 ++ fix12 ++ flags` releases the hits and flags. -/
theorem retiredFull (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (k : Mode) (s : State) (m : List Bool)
    (v : BasisState) (input : ∀ q, s.basis q = (post (ports j) (prepare j) false k q).read v)
    (l : left k = (v (Shadow7.e0P (start j) + 3) && v (Shadow7.e0P (start j) + 4)))
    (r : right k = (v (Shadow7.e0P (start j) + 3) && !v (Shadow7.e0P (start j) + 4)))
    (exchange : right k = true → ∀ i < 15, i ≤ key k → v (swaps j i) = decide (i = key k)) :
    run ((retire j).map Op.exit ++ (dropAll 1560 (swaps j) LeaveSelector.tags 0 15 ++
        (flagOps (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) true).reverse.map Op.exit)) m s =
      ⟨s.phase, clearKey (fun q => (restored (ports j) false k q).read v)⟩ := by
  have rr := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
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

/-- Glue G3 does nothing when its tag is off (fable-leap, margin 16). -/
theorem run_g3_off (c b x t : Wire) (cb : c ≠ b) (xb : x ≠ b) (tc : t ≠ c) (tb : t ≠ b) (tx : t ≠ x) (m : List Bool)
    (st : State) (off : st.basis x = false) : run [.CX c b, .CCX x b t, .CX c b] m st = st := by
  rw [run_g3 c b x t cb xb tc tb tx m st, off, Bool.false_and, Bool.xor_false]
  show (⟨st.phase, Function.update st.basis t (st.basis t)⟩ : State) = st
  rw [Function.update_eq_self]

/-- dadon's `Leave{s}NearMiddle.result`: no tag hot, zero bank, no crossing. -/
theorem nearMiddle_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (X : Nat) (bound : X < 2^17) (s : State)
    (m : List Bool) (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (off : ∀ q ∈ tagsP, s.basis q = false)
    (shadow : ∀ i < 17, s.basis (Shadow7.a0P (start j) - 1 + i) = X.testBit i)
    (bank : regValue (ys j) s.basis = 0) (crossZero : s.basis (Shadow7.e0P (start j) + 6) = false)
    (farOff : s.basis (Shadow7.e0P (start j) + 3) = false)
    (scratch : s.basis 1614 = false) :
    let out := run (GateMirror.forward (middleOps (start j))) m s
    out.phase = s.phase ∧
      (∀ i : Fin 17, out.basis (row j i).keep = X.testBit i ∧ out.basis (row j i).free = false) ∧
      (∀ i : Nat, 17 ≤ i → i < Shadow7.wpP (start j) + 15 → out.basis (Shadow7.bankW (start j) i) = false) ∧
      (∀ q, q ≠ 1613 → HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q →
        (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) → out.basis q = s.basis q) ∧
      out.basis 1613 = (((s.basis (Shadow7.e0P (start j) + 3) ^^ s.basis (Shadow7.e0P (start j) + 6)) ^^ s.basis 1596) ^^ s.basis 1597) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have n3 : (Shadow7.e0P (start j) + 3 : Wire) ≠ 1613 := by unfold Wire at *; omega
  have n6 : (Shadow7.e0P (start j) + 6 : Wire) ≠ 1613 := by unfold Wire at *; omega
  have n63 : (Shadow7.e0P (start j) + 6 : Wire) ≠ Shadow7.e0P (start j) + 3 := by unfold Wire at *; omega
  obtain ⟨pre, hpre⟩ : ∃ pre : State, pre = ⟨s.phase, writeBit s.basis (Shadow7.e0P (start j) + 3) (s.basis (Shadow7.e0P (start j) + 3) ^^ s.basis (Shadow7.e0P (start j) + 6))⟩ := ⟨_, rfl⟩
  have preq (q : Wire) (ne : q ≠ Shadow7.e0P (start j) + 3) : pre.basis q = s.basis q := by
    rw [hpre]; simp only [writeBit, Function.update_of_ne ne]
  have pre3 : pre.basis (Shadow7.e0P (start j) + 3) = false := by
    rw [hpre]; simp only [writeBit, Function.update_self, farOff, crossZero, Bool.false_xor]
  have preP : pre.phase = s.phase := by rw [hpre]
  have cleanP : ∀ q ∈ carries j, pre.basis q = false := by
    intro q hq
    refine (preq q ?_).trans (clean q hq)
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    have pt := Shadow7.pool_top w1 w2
    have p := Shadow7.pool_cases (i := i) w1 w2; unfold Wire at *; omega
  have selP : pre.basis 1613 = false := (preq _ (Ne.symm n3)).trans selectZero
  have padP : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 →
      pre.basis (Shadow7.bankW (start j) i) = false := by
    intro i lo hi
    have b := Shadow7.bank_cases w1 w2 hi
    exact (preq _ (by unfold Wire at *; omega)).trans (padding i lo hi)
  have offP : ∀ q ∈ tagsP, pre.basis q = false := by
    intro q hq
    have t := tags_range' q hq
    exact (preq q (by unfold Wire at *; omega)).trans (off q hq)
  let early := GateMirror.forward (Shadow7.leaveAdjustCore (start j) ++ Shadow7.leaveBarrel (start j))
  have a := nearHigh_result j h0 (by omega) pre m cleanP selP padP offP
  have bankZero : HighBankAdjust.adjusted (regValue (ys j) pre.basis) (Shadow7.wpP (start j)) (pre.basis (Shadow7.e0P (start j) + 3))
      (pre.basis 1596) = 0 := by
    have y : regValue (ys j) pre.basis = regValue (ys j) s.basis := (regValue_eq_iff _ _ _).mpr (fun q hq => preq q (by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
      have b := Shadow7.bank_cases w1 w2 (i := i) (by omega); unfold Wire at *; omega))
    rw [y, bank, pre3]; unfold HighBankAdjust.adjusted
    cases pre.basis 1596 <;> simp
  generalize hv : run early m pre = v at a
  generalize ht : m.drop (measurementCount early) = tape
  have sg := run_sign8 (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 6) 1596 1597 1613 tape v n3 n6 (by decide) (by decide) n63
  generalize hu : run ([.CX (Shadow7.e0P (start j) + 3) 1613, .CX 1596 1613, .CX 1597 1613, .CX (Shadow7.e0P (start j) + 6) (Shadow7.e0P (start j) + 3)] : Program) tape v = u at sg
  have bits (i : Nat) (hi : i < Shadow7.wpP (start j) + 15) : v.basis (Shadow7.bankW (start j) i) = false := by
    have := a.bits i hi; rw [bankZero] at this; simpa using this
  have unchanged (q : Wire) (ne : q ≠ 1613) (ne3 : q ≠ Shadow7.e0P (start j) + 3) : u.basis q = v.basis q := sg.2.2.2 q ne ne3
  have old (q : Wire) (ne : q ≠ 1613) (ne3 : q ≠ Shadow7.e0P (start j) + 3)
      (ext : HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q) :
      u.basis q = s.basis q := (unchanged q ne ne3).trans ((a.frame q ext).trans (preq q ne3))
  have bankOut : ∀ q : Nat, (1556 ≤ q ∧ q ≤ 1597) ∨ (q ≤ 785) ∨ (Shadow7.e0P (start j) + 3 ≤ q ∧ q ≤ Shadow7.e0P (start j) + 9) →
      HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q := by
    intro q hq i hi e
    have b := Shadow7.bank_cases w1 w2 hi
    unfold Wire at *; omega
  have stable : ∀ i, i < Shadow7.wpP (start j) + 15 → (1613:Wire) ≠ Shadow7.bankW (start j) i := fun i hi => (layout j h0 (by omega)).separate i hi
  have v3 : v.basis (Shadow7.e0P (start j) + 3) = false := (a.frame _ (bankOut _ (Or.inr (Or.inr (by omega))))).trans pre3
  have v6 : v.basis (Shadow7.e0P (start j) + 6) = false :=
    (a.frame _ (bankOut _ (Or.inr (Or.inr (by omega))))).trans ((preq _ n63).trans crossZero)
  have v96 : v.basis 1596 = s.basis 1596 :=
    (a.frame _ (bankOut 1596 (Or.inl (by omega)))).trans (preq _ (by unfold Wire at *; omega))
  have v97 : v.basis 1597 = s.basis 1597 :=
    (a.frame _ (bankOut 1597 (Or.inl (by omega)))).trans (preq _ (by unfold Wire at *; omega))
  have select : v.basis 1613 = false := (a.frame _ (layout j h0 (by omega)).separate).trans selP
  have u13 : u.basis 1613 = (((s.basis (Shadow7.e0P (start j) + 3) ^^ s.basis (Shadow7.e0P (start j) + 6)) ^^ s.basis 1596) ^^ s.basis 1597) := by
    have h := sg.2.1
    rw [select, v3, v96, v97] at h
    rw [farOff, crossZero]
    exact h
  have u3 : u.basis (Shadow7.e0P (start j) + 3) = s.basis (Shadow7.e0P (start j) + 3) := by
    have h := sg.2.2.1
    rw [v3, v6] at h
    exact h.trans farOff.symm
  have readTags (q : Wire) (hq : q ∈ tagsP) : u.basis q = false := by
    have t := tags_range' q hq
    exact (old q (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      (bankOut q (Or.inl (by unfold Wire at *; omega)))).trans (off q hq)
  have readShadow (i : Nat) (hi : i < 17) : u.basis (Shadow7.a0P (start j) - 1 + i) = X.testBit i :=
    (old _ (by unfold Wire at *; omega) (by unfold Wire at *; omega) (bankOut _ (Or.inr (Or.inl (by omega))))).trans (shadow i hi)
  have readTube (i : Nat) (hi : i < 17) : u.basis (Shadow7.bankW (start j) i) = false := by
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
    exact (unchanged _ (stable i (by omega)).symm (by unfold Wire at *; omega)).trans (bits i (by omega))
  have zero := (old 1614 (by decide) (by unfold Wire at *; omega) (fun i hi e => by
    have b := Shadow7.bank_cases w1 w2 hi; unfold Wire at *; omega)).trans scratch
  have word := fun tp => nearWord_combine j h0 (by omega) X bound u tp readTags readShadow readTube zero
  dsimp only
  have parts : GateMirror.forward (middleOps (start j)) =
      Instr.CX (Shadow7.e0P (start j) + 6) (Shadow7.e0P (start j) + 3) ::
        (early ++ (([.CX (Shadow7.e0P (start j) + 3) 1613, .CX 1596 1613, .CX 1597 1613, .CX (Shadow7.e0P (start j) + 6) (Shadow7.e0P (start j) + 3)] : Program) ++ (GateMirror.forward (Shadow7.glueG3 (start j)) ++ GateMirror.forward (Shadow7.leaveJoin (start j))))) := middle_parts (start j)
  have away13 : ∀ c ∈ cols j, (1613 : Wire) ≠ c.shadow ∧ (1613 : Wire) ≠ c.tube := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk
    exact ⟨by dsimp only; unfold Wire at *; omega, by dsimp only; exact stable k (by omega)⟩
  have hg (tp : List Bool) : run (GateMirror.forward (Shadow7.glueG3 (start j))) tp u = u := by
    have t0 := tags_range' _ (tags_mem 0 (by decide))
    have bk := Shadow7.bank_cases w1 w2 (i := 0) (by omega)
    exact run_g3_off (Shadow7.e0P (start j) + 6) (Shadow7.bankW (start j) 0) (tagsP.getD 0 0) (Shadow7.b0P (start j) - 1)
      (by unfold Wire at *; omega) (by unfold Wire at *; omega) (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      (by unfold Wire at *; omega) tp u (readTags _ (tags_mem 0 (by decide)))
  rw [parts, run_cx_cons, ← hpre, run_append, run_take, run_append, run_take, hv, ht, hu, run_append, run_take, hg]
  refine ⟨(word _).1.trans (sg.1.trans (a.phase.trans preP)), (word _).2.1, ?_, ?_, ((word _).2.2 1613 away13).trans u13⟩
  · intro i lo hi
    have outsideRows : ∀ c ∈ cols j, Shadow7.bankW (start j) i ≠ c.shadow ∧ Shadow7.bankW (start j) i ≠ c.tube := by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk
      have b := Shadow7.bank_cases w1 w2 hi
      refine ⟨by dsimp only; unfold Wire at *; omega, fun e => ?_⟩
      have := Shadow7.bank_inj w1 w2 hi (by omega) e; omega
    have b := Shadow7.bank_cases w1 w2 hi
    exact ((word _).2.2 _ outsideRows).trans ((unchanged _ (stable i hi).symm (by unfold Wire at *; omega)).trans (bits i hi))
  · intro q ne ext away
    by_cases e3 : q = Shadow7.e0P (start j) + 3
    · subst e3
      exact ((word _).2.2 _ away).trans u3
    · exact ((word _).2.2 q away).trans (old q ne e3 ext)

/-! OutputPorts. -/

/-- dadon's `Leave{s}OutputPorts.live`: the output register's wires. -/
def live (j : Fin 26) (i : Nat) : Wire := if i < Shadow7.lowsP (start j) then Shadow7.a0P (start j) - 1 + i else Shadow7.bankW (start j) i

theorem live_row (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (i : Fin 17) : live j i.val = (row j i).keep := by
  have g := row_eq j i
  unfold Column.keep live
  rw [g.2.2.1]
  by_cases h : i.val < Shadow7.lowsP (start j)
  · simp [h, g.1]
  · simp [h, g.2.1]

theorem activeBits (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (X H : Nat) (k : Fin 16) (s : State)
    (lo : ∀ i : Fin 17, s.basis (row j i).keep = (2^k.val*H + X%2^k.val).testBit i.val)
    (hi : ∀ i : Nat, 17 ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = (2^k.val*H).testBit i) :
    ∀ i < Shadow7.wpP (start j) + 15, s.basis (live j i) = (2^k.val*H + X%2^k.val).testBit i := by
  have r := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
  intro i bound
  by_cases h : i < 17
  · rw [live_row j h0 (by omega) ⟨i, h⟩]; exact lo ⟨i, h⟩
  · have nl : ¬ i < Shadow7.lowsP (start j) := by omega
    rw [live, if_neg nl, hi i (by omega) bound]
    have z := HighBankJoin.merged_bits X H k.val i
    have kval := k.isLt
    have a : (X%2^k.val).testBit i = false := by simpa only [if_pos (show k.val ≤ i by omega)] using z.1
    simpa only [a, Bool.false_xor] using z.2

theorem inactiveBits (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (X : Nat) (small : X < 2^17) (s : State)
    (lo : ∀ i : Fin 17, s.basis (row j i).keep = X.testBit i.val)
    (hi : ∀ i : Nat, 17 ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false) :
    ∀ i < Shadow7.wpP (start j) + 15, s.basis (live j i) = X.testBit i := by
  have r := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
  intro i bound
  by_cases h : i < 17
  · rw [live_row j h0 (by omega) ⟨i, h⟩]; exact lo ⟨i, h⟩
  · have nl : ¬ i < Shadow7.lowsP (start j) := by omega
    rw [live, if_neg nl, hi i (by omega) bound,
      Nat.testBit_lt_two_pow (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) (by omega)))]

/-- G3's flip turns the reduced bit sb of the magnitude into the true one (fable-leap, margin 16). -/
theorem g3_math (b w : Nat) (z : SkywalkNat.State) (sg : Bool) (small : far b 15 z → min z.u z.v < 2^b)
    (hw : 1 ≤ w) (c n : Bool) :
    ((((step^[15] (reduced b 15 z)).u - (PortalValues.negative sg (step^[15] (reduced b 15 z)).u).toNat) / 2^b).testBit 0 ^^
      (decide (far b 15 z ∧ LeaveShadowRails.farKey b z = 0) &&
        ((HighBankAdjust.adjusted (high b 15 z) w c n).testBit 0 ^^ !c))) =
      (((step^[15] z).u - (PortalValues.negative sg (step^[15] (reduced b 15 z)).u).toNat) / 2^b).testBit 0 := by
  have he : (PortalValues.negative sg (step^[15] (reduced b 15 z)).u).toNat ≤ (step^[15] (reduced b 15 z)).u := by
    by_cases p : 0 < (step^[15] (reduced b 15 z)).u
    · have : (PortalValues.negative sg (step^[15] (reduced b 15 z)).u).toNat ≤ 1 := by
        cases PortalValues.negative sg (step^[15] (reduced b 15 z)).u <;> decide
      omega
    · have n0 : PortalValues.negative sg (step^[15] (reduced b 15 z)).u = false := by
        simp only [PortalValues.negative, decide_eq_false p, Bool.and_false]
      rw [n0]; exact Nat.zero_le _
  have lo17 : ¬(far b 15 z ∧ LeaveShadowRails.farKey b z = 0) → ∀ f : far b 15 z,
      ((step^[15] z).u - (PortalValues.negative sg (step^[15] (reduced b 15 z)).u).toNat) % 2^(b+1) =
        ((step^[15] (reduced b 15 z)).u - (PortalValues.negative sg (step^[15] (reduced b 15 z)).u).toNat) % 2^(b+1) :=
    fun K f => (LeaveShadowRails.retainedLow17 b z (small f) sg K).2.2
  generalize (PortalValues.negative sg (step^[15] (reduced b 15 z)).u).toNat = e at he lo17 ⊢
  simp only [Nat.testBit_zero]
  have W0 : 2^w % 2 = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
    rw [hk, pow_succ]; omega
  have W2 : 2 ≤ 2^w := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^w := Nat.pow_le_pow_right (by norm_num) hw
  have adj : (HighBankAdjust.adjusted (high b 15 z) w c n) % 2 = (high b 15 z + c.toNat) % 2 := by
    unfold HighBankAdjust.adjusted
    have dv : 2 ∣ 2^w := Nat.dvd_of_mod_eq_zero W0
    cases n <;> cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, if_true, if_false, Bool.false_eq_true] <;>
      rw [Nat.mod_mod_of_dvd _ dv] <;> omega
  by_cases K : far b 15 z ∧ LeaveShadowRails.farKey b z = 0
  · obtain ⟨f, k0⟩ := K
    have bits := (LeaveShadowRails.key0Bits b z (small f) f k0 e he).1
    have h2 : 2 ≤ high b 15 z := f
    simp only [decide_eq_true (And.intro f k0), Bool.true_and]
    rw [bits, adj]
    generalize ((step^[15] (reduced b 15 z)).u - e) / 2^b = A
    generalize high b 15 z = Q at h2 ⊢
    have e2 : (A + (Q - 1)) % 2 = (A % 2 + Q % 2 + 1) % 2 := by omega
    have e1 : (Q + c.toNat) % 2 = (Q % 2 + c.toNat) % 2 := by omega
    rw [e1, e2]
    have hα : A % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hκ : Q % 2 < 2 := Nat.mod_lt _ (by norm_num)
    generalize A % 2 = α at hα ⊢
    generalize Q % 2 = κ at hκ ⊢
    interval_cases α <;> interval_cases κ <;> cases c <;> decide
  · simp only [decide_eq_false K, Bool.false_and, Bool.xor_false]
    by_cases f : far b 15 z
    · have key2 : ∀ x : Nat, x / 2^b % 2 = x % 2^(b+1) / 2^b := fun x => by rw [pow_succ, Nat.mod_mul_right_div_self]
      rw [key2 ((step^[15] (reduced b 15 z)).u - e), key2 ((step^[15] z).u - e), lo17 K f]
    · have same : reduced b 15 z = z := by unfold reduced; rw [if_neg f]
      rw [same]

/-- The mask release after the G4 borrow: measured erase of 1558 (phase-clean since 1558 = B && 1557), 1557 back to 0. -/
theorem release_generic (a b : Wire) (ha7 : a ≠ 1557) (ha8 : a ≠ 1558) (hb7 : b ≠ 1557) (hb8 : b ≠ 1558) (v : State)
    (mm : List Bool) (h7 : v.basis 1557 = !v.basis a) (h8 : v.basis 1558 = (v.basis b && v.basis 1557)) :
    run [.measureX 1558 [] [.CZ b 1557], .CX a 1557, .X 1557] mm v =
      ⟨v.phase, writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  obtain ⟨ph, bs⟩ := v
  simp only at h7 h8
  have n78 : (1557 : Wire) ≠ 1558 := by decide
  cases hμ : mm.headD false <;>
  simp only [run, measureAndCorrect, correct, writeBit, hμ, if_true, if_false, Bool.false_and, Bool.true_and,
    Bool.xor_false, Function.update_apply, if_neg hb8, if_neg ha8, if_neg ha7, if_pos rfl, if_neg n78, h8, h7] <;>
  (congr 1; try (cases bs b <;> cases bs a <;> simp)) <;>
  (funext q; by_cases q7 : q = 1557 <;> by_cases q8 : q = 1558 <;> simp [Function.update_apply, q7, q8, h7, ha7, ha8, hb7, hb8])

/-! TrueMiddle (dadon's `Leave{s}TrueMiddle`): the actual word-update values. -/

namespace TrueMiddle
abbrev r (j : Fin 26) (z : SkywalkNat.State) := reduced (Shadow7.sbP (start j)) 15 z
def key (j : Fin 26) (z : SkywalkNat.State) : Fin 16 :=
  ⟨if 2^(Shadow7.sbP (start j)) ≤ z.u then 0 else wait 15 z.u, by have h := wait_le 15 z.u; split <;> omega⟩
def X (j : Fin 26) (z : SkywalkNat.State) := total (step^[15] (r j z)) / 2^(Shadow7.sbP (start j))
def F (j : Fin 26) (z : SkywalkNat.State) := total (step^[15] z) / 2^(Shadow7.sbP (start j))
def d (j : Fin 26) (z : SkywalkNat.State) := X j z / 2^(key j z).val
def neg (j : Fin 26) (z : SkywalkNat.State) :=
  cross17 (d j z) && (!(decide (2^(Shadow7.sbP (start j)) ≤ z.u)) && negative (oddBits (letters 15 (r j z))))
end TrueMiddle

/-- dadon's `Leave{s}TrueMiddle.actual`. -/
theorem trueMiddle_actual (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (z : SkywalkNat.State) (s : State)
    (m : List Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (odd : z.v % 2 = 1)
    (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (tag : ∀ q ∈ tagsP, s.basis q = if far (Shadow7.sbP (start j)) 15 z then hot (TrueMiddle.key j z) q else false)
    (shadow : ∀ i < 17, s.basis (Shadow7.a0P (start j) - 1 + i) = (TrueMiddle.X j z).testBit i)
    (bank : regValue (ys j) s.basis = if far (Shadow7.sbP (start j)) 15 z then high (Shadow7.sbP (start j)) 15 z else 0)
    (cin : s.basis (Shadow7.e0P (start j) + 6) = if far (Shadow7.sbP (start j)) 15 z then !cross17 (TrueMiddle.d j z) else false)
    (sgn : far (Shadow7.sbP (start j)) 15 z → s.basis 1596 =
      (!(decide (2^(Shadow7.sbP (start j)) ≤ z.u)) && negative (oddBits (letters 15 (TrueMiddle.r j z)))))
    (gate : s.basis 1597 = (s.basis (Shadow7.e0P (start j) + 6) && s.basis 1596))
    (farBit : s.basis (Shadow7.e0P (start j) + 3) = decide (far (Shadow7.sbP (start j)) 15 z))
    (scratch : s.basis 1614 = false) :
    let u := run (GateMirror.forward (middleOps (start j))) m s
    u.phase = s.phase ∧ (∀ i < Shadow7.wpP (start j) + 15, u.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      (∀ i : Fin 17, u.basis (row j i).free = false) ∧
      (∀ q, q ≠ 1613 → q ≠ Shadow7.b0P (start j) - 1 → HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q →
        (∀ a ∈ cols j, q ≠ a.shadow ∧ q ≠ a.tube) → u.basis q = s.basis q) ∧
      u.basis 1613 = (((s.basis (Shadow7.e0P (start j) + 3) ^^ s.basis (Shadow7.e0P (start j) + 6)) ^^ s.basis 1596) ^^ s.basis 1597) ∧
      u.basis (Shadow7.b0P (start j) - 1) = (s.basis (Shadow7.b0P (start j) - 1) ^^ (decide (far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0) &&
        ((HighBankAdjust.adjusted (high (Shadow7.sbP (start j)) 15 z) (Shadow7.wpP (start j)) (HighBankSum.cross17 (TrueMiddle.d j z)) (TrueMiddle.neg j z)).testBit 0 ^^
          !HighBankSum.cross17 (TrueMiddle.d j z)))) := by
  dsimp only
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have rw7 := Shadow7.rail_win w1 w2
  by_cases f : far (Shadow7.sbP (start j)) 15 z
  · simp only [if_pos f] at tag bank cin
    have law := LeaveJ7.Far.far_result (Shadow7.sbP (start j)) (Shadow7.wpP (start j)) z small f odd room
    change TrueMiddle.d j z + 1 = (cross17 (TrueMiddle.d j z)).toNat + 2*(!TrueMiddle.neg j z).toNat ∧
      TrueMiddle.F j z = 2^(TrueMiddle.key j z).val * HighBankAdjust.adjusted (high (Shadow7.sbP (start j)) 15 z) (Shadow7.wpP (start j))
        (cross17 (TrueMiddle.d j z)) (TrueMiddle.neg j z) + TrueMiddle.X j z % 2^(TrueMiddle.key j z).val at law
    have c17 : cross17 (TrueMiddle.d j z) = !s.basis (Shadow7.e0P (start j) + 6) := by rw [cin, Bool.not_not]
    have hsg := sgn f
    have negE : TrueMiddle.neg j z = (!s.basis (Shadow7.e0P (start j) + 6) && s.basis 1596) := by
      unfold TrueMiddle.neg; rw [c17, hsg]
    have farOn : s.basis (Shadow7.e0P (start j) + 3) = true := by rw [farBit]; exact decide_eq_true f
    have dg : TrueMiddle.X j z / 2^(TrueMiddle.key j z).val + 1 = (!s.basis (Shadow7.e0P (start j) + 6)).toNat +
        2*(!(!s.basis (Shadow7.e0P (start j) + 6) && s.basis 1596)).toNat := by
      have h := law.1
      rw [negE, c17] at h
      exact h
    have out := middle_result j h0 (by omega) (TrueMiddle.key j z) (TrueMiddle.X j z) s m clean selectZero padding tag shadow
      farOn gate dg scratch
    have hH : HighBankAdjust.adjusted (high (Shadow7.sbP (start j)) 15 z) (Shadow7.wpP (start j)) (cross17 (TrueMiddle.d j z))
        (TrueMiddle.neg j z) = HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j))
          (!s.basis (Shadow7.e0P (start j) + 6)) (s.basis 1596) := by
      rw [negE, c17, bank]
      exact HighBankSum.adjusted_gate _ _ _ _ (by omega)
    refine ⟨out.1, ?_, fun i => (out.2.1 i).2, out.2.2.2.1, out.2.2.2.2.1, ?_⟩
    rotate_left
    · rw [out.2.2.2.2.2]
      by_cases k0 : (TrueMiddle.key j z).val = 0
      · have hk : LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0 := k0
        have hot1 : hot (TrueMiddle.key j z) (tagsP.getD 0 0) = true := by simp [hot, k0]
        rw [hot1, k0, pow_zero, one_mul, ← hH, cin, decide_eq_true (And.intro f hk)]
      · have hot0 : hot (TrueMiddle.key j z) (tagsP.getD 0 0) = false :=
          decide_eq_false (fun h => k0 (congrArg Fin.val
            ((by decide : ∀ a b : Fin 16, tagsP.getD a 0 = tagsP.getD b 0 → a = b) 0 (TrueMiddle.key j z) h)).symm)
        have hdec : decide (far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0) = false :=
          decide_eq_false (fun h => k0 h.2)
        rw [hot0, hdec, Bool.false_and, Bool.false_and]
    rw [law.2, hH]
    exact activeBits j h0 (by omega) _ _ _ _ (fun i => (out.2.1 i).1) out.2.2.1
  · simp only [if_neg f] at tag bank cin
    have farOff : s.basis (Shadow7.e0P (start j) + 3) = false := by rw [farBit]; exact decide_eq_false f
    have law := LeaveShadowRails.near_result (Shadow7.sbP (start j)) z f
    have eq : TrueMiddle.X j z = TrueMiddle.F j z := by unfold TrueMiddle.X TrueMiddle.F TrueMiddle.r; rw [law.1]
    have bound : TrueMiddle.X j z < 2^17 := eq ▸ law.2
    have out := nearMiddle_result j h0 (by omega) (TrueMiddle.X j z) bound s m clean selectZero padding tag shadow bank cin farOff scratch
    refine ⟨out.1, ?_, fun i => (out.2.1 i).2, fun q n13 _ ext away => out.2.2.2.1 q n13 ext away, out.2.2.2.2, ?_⟩
    rotate_left
    · have hdec : decide (far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0) = false :=
        decide_eq_false (fun h => f h.1)
      rw [hdec, Bool.false_and, Bool.xor_false]
      exact out.2.2.2.1 _ (by unfold Wire at *; omega) (fun i hi e => by
        have bk := Shadow7.bank_cases w1 w2 hi; unfold Wire at *; omega)
        (fun c hc => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk
        have bk := Shadow7.bank_cases w1 w2 (i := k) (by omega)
        exact ⟨by dsimp only; unfold Wire at *; omega, by dsimp only; unfold Wire at *; omega⟩)
    rw [← eq]
    exact inactiveBits j h0 (by omega) _ bound _ (fun i => (out.2.1 i).1) out.2.2.1

/-! Loaded (dadon's `Leave{s}Loaded`) and SignClose (dadon's `Leave{s}SignClose`). -/

/-- dadon's `Leave{s}RetireActual.prior`: the selector state after the prepared word. -/
def prior (j : Fin 26) (k : Mode) : Sym := sim (prepare j) (LeaveSelector.start (ports j) false k)

theorem tags_inj (i i' : Nat) (hi : i < 16) (hi' : i' < 16) (e : tagsP.getD i 0 = tagsP.getD i' 0) : i = i' := by
  have h : ∀ a b : Fin 16, tagsP.getD a 0 = tagsP.getD b 0 → a = b := by decide
  exact congrArg Fin.val (h ⟨i, hi⟩ ⟨i', hi'⟩ e)

theorem physicalTags (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (k : Mode) (q : Wire) (hq : q ∈ tagsP) :
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

theorem loaded_tags (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (z : SkywalkNat.State) (v : BasisState) (q : Wire)
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

theorem controlsAt (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (k : Mode) :
    prior j k (Shadow7.e0P (start j) + 6) = crossing (ports j) k ∧
      prior j k 1597 = conj (crossing (ports j) k) (signExpr (ports j) k) := by
  have h := controlCert j h0 (by omega) k
  simp only [reads, LeaveSelector.controls, List.cons.injEq, and_true] at h
  exact ⟨h.2.1, h.2.2.2⟩

/-- The selector's `1596` is the sign expression (third entry of the control certificate). -/
theorem control96 (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (k : Mode) :
    prior j k 1596 = signExpr (ports j) k := by
  have h := controlCert j h0 (by omega) k
  simp only [reads, LeaveSelector.controls, List.cons.injEq, and_true] at h
  exact h.2.2.1

/-- dadon's `Leave{s}Loaded.signed` at margin 17: the crossing wire reads bit 0 of the far digit d ∈ {0,1,2}. -/
theorem loaded_signed (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (z : SkywalkNat.State) (ref : BasisState)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (odd : z.v % 2 = 1)
    (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (bits : ∀ i < 16, ref ((ports j).u + i) = (TrueMiddle.X j z).testBit i)
    (par : parityBits (ports j) ref = oddBits (letters 15 (reduced (Shadow7.sbP (start j)) 15 z))) :
    let k := actualMode (Shadow7.sbP (start j)) z
    let s := fun q => (prior j k q).read ref
    s (Shadow7.e0P (start j) + 6) = (if far (Shadow7.sbP (start j)) 15 z then !cross17 (TrueMiddle.d j z) else false) ∧
      s 1597 = (s (Shadow7.e0P (start j) + 6) && (signExpr (ports j) k).read ref) ∧
      (far (Shadow7.sbP (start j)) 15 z → (signExpr (ports j) k).read ref =
        (!(decide (2^(Shadow7.sbP (start j)) ≤ z.u)) && negative (oddBits (letters 15 (TrueMiddle.r j z))))) := by
  have h := trueControls_shadow7 (Shadow7.sbP (start j)) (Shadow7.wpP (start j)) z small.1 odd room (ports j) ref bits par
  obtain ⟨cx, gate⟩ := controlsAt j h0 (by omega) (actualMode (Shadow7.sbP (start j)) z)
  dsimp only
  rw [cx, gate, read_conj]
  exact ⟨h.1, rfl, fun f => h.2 f⟩

theorem dest_forward (gs : List Gate) : (GateMirror.forward gs).map LeaveReadoutFrame.destination = gs.map target := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [GateMirror.forward, List.map_cons] at ih ⊢
    rw [ih]; cases g <;> rfl

/-- dadon's `Leave{s}SignClose.result`: `middle ++ fix10` closes the sign bit (`1613` holds
`far xor d0 xor signExpr xor (d0 ∧ signExpr)` after the middle). -/
theorem signClose_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (u : State)
    (hu : run (GateMirror.forward (middleOps (start j))) m s = u)
    (flag : u.basis 1613 = (((u.basis (Shadow7.e0P (start j) + 3) ^^ u.basis (Shadow7.e0P (start j) + 6)) ^^ u.basis 1596) ^^ u.basis 1597)) :
    run (GateMirror.forward (middleOps (start j) ++ Shadow7.fix10P (start j) (Shadow7.sbP (start j)))) m s =
      ⟨u.phase, writeBit u.basis 1613 false⟩ := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have n3 : (Shadow7.e0P (start j) + 3 : Wire) ≠ 1613 := by unfold Wire at *; omega
  have n6 : (Shadow7.e0P (start j) + 6 : Wire) ≠ 1613 := by unfold Wire at *; omega
  rw [forward_app, run_append, run_take, hu, fix10_forward]
  have sg := run_sign10 (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 6) 1596 1597 1613
    (m.drop (measurementCount (GateMirror.forward (middleOps (start j))))) u n3 n6 (by decide) (by decide)
  generalize run ([.CX (Shadow7.e0P (start j) + 3) 1613, .CX (Shadow7.e0P (start j) + 6) 1613, .CX 1596 1613, .CX 1597 1613] : Program) (m.drop (measurementCount (GateMirror.forward (middleOps (start j))))) u = t at sg ⊢
  obtain ⟨ph, bs⟩ := t
  obtain ⟨p1, p2, p3⟩ := sg
  have ep : ph = u.phase := p1
  have eb : bs = writeBit u.basis 1613 false := by
    funext q
    by_cases e : q = 1613
    · subst e
      have h : bs 1613 = ((((u.basis 1613 ^^ u.basis (Shadow7.e0P (start j) + 3)) ^^ u.basis (Shadow7.e0P (start j) + 6)) ^^ u.basis 1596) ^^ u.basis 1597) := p2
      rw [h, flag, writeBit, Function.update_self]
      cases u.basis (Shadow7.e0P (start j) + 3) <;> cases u.basis (Shadow7.e0P (start j) + 6) <;> cases u.basis 1596 <;> cases u.basis 1597 <;> rfl
    · have h : bs q = u.basis q := p3 q e
      rw [h, writeBit, Function.update_of_ne e]
  rw [ep, eb]

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
def paritySites (j : Fin 26) : List Wire := List.range' (start j + 16) 15

/-- Destinations of `prepare`, read off the op list. Not a selector simulation. -/
theorem prepare_dst : ∀ (j : Fin 26), 0 ≤ j.val → j.val ≤ 24 →
    ∀ t ∈ (prepare j).map Op.dst, (1559 ≤ t ∧ t ≤ 1597) ∨ t = (ports j).crossing ∨ t = (ports j).near := by
  decide +kernel

/-! The selector word after `prepare` reads only the history letters: an invariant of the symbolic
simulator, proved from the Shadow7.shape of the op list (no simulation, no decide over the modes). -/

/-- The hit and tag bits `1559..1575`. -/
abbrev InBits (q : Nat) : Prop := 1559 ≤ q ∧ q ≤ 1575
/-- The prepared word `1576..1596`. -/
abbrev InBand (q : Nat) : Prop := 1576 ≤ q ∧ q ≤ 1596
/-- The block's history letters. -/
abbrev IsHist (j : Fin 26) (q : Nat) : Prop := start j + 16 ≤ q ∧ q ≤ start j + 30

/-- Wires a band write may read. -/
abbrev ArgOK (j : Fin 26) (a : Nat) : Prop := InBits a ∨ IsHist j a ∨ InBand a

/-- An op does not write the history or the bit wires, and a band write reads only `ArgOK` wires. -/
abbrev OpGood (j : Fin 26) (o : Op) : Prop :=
  ¬ IsHist j o.dst ∧ ¬ InBits o.dst ∧ (InBand o.dst → ∀ a ∈ o.args, ArgOK j a)

structure SelClean (j : Fin 26) (k : Mode) (g : Sym) : Prop where
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

private theorem refs_foldl_aux (p : Ports) : ∀ (xs : List Nat) (acc : Expr),
    ∀ q ∈ refs (xs.foldl (fun rest j => conj rest (.wire (p.g + j))) acc),
      q ∈ refs acc ∨ ∃ t ∈ xs, q = p.g + t
  | [], _, _, hq => Or.inl hq
  | j :: js, acc, q, hq => by
    simp only [List.foldl_cons] at hq
    rcases refs_foldl_aux p js (conj acc (.wire (p.g + j))) q hq with h | ⟨t, ht, e⟩
    · rcases refs_conj_sub h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr ⟨j, List.mem_cons_self, List.mem_singleton.mp h2⟩
    · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, e⟩

theorem refs_foldr (p : Ports) : ∀ xs : List Nat,
    ∀ q ∈ refs (xs.foldl (fun rest j => conj rest (.wire (p.g + j))) (.bit true)), ∃ t ∈ xs, q = p.g + t := fun xs q hq => by
  rcases refs_foldl_aux p xs (.bit true) q hq with h | h
  · exact absurd h List.not_mem_nil
  · exact h

theorem arg_refs (j : Fin 26) (k : Mode) {g : Sym} (hc : SelClean j k g) {a : Nat} (ha : ArgOK j a) :
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

theorem symbolic_clean (j : Fin 26) (k : Mode) (o : Op) (g : Sym) (hc : SelClean j k g) (hg : OpGood j o) :
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

theorem sim_selClean (j : Fin 26) (k : Mode) : ∀ (os : List Op) (g : Sym),
    SelClean j k g → (∀ o ∈ os, OpGood j o) → SelClean j k (sim os g) := by
  intro os
  induction os with
  | nil => intro g hc _; exact hc
  | cons o os ih =>
    intro g hc ho
    exact ih (symbolic o g) (symbolic_clean j k o g hc (ho o List.mem_cons_self))
      (fun o' h => ho o' (List.mem_cons_of_mem _ h))

theorem start_clean (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (k : Mode) :
    SelClean j k (LeaveSelector.start (ports j) false k) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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
theorem prepare_good : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 → ∀ o ∈ prepare j, OpGood j o := by
  decide +kernel

theorem retireCerts (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (k : Mode) :
    (∀ i : Fin 38, post (ports j) (prepare j) false k (1559 + i.val) = prior j k (1559 + i.val) ∧
      ∀ q ∈ refs (prior j k (1559 + i.val)), q ∈ paritySites j) ∧
    (∀ q ∈ refs (signExpr (ports j) k), q ∈ paritySites j) ∧
    (∀ t ∈ (prepare j).map Op.dst, (1559 ≤ t ∧ t ≤ 1597) ∨ t = (ports j).crossing ∨ t = (ports j).near) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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
theorem postfix_parts : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    GateMirror.forward (leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j)) =
      (retire j).map Op.exit ++ (HighBankFirstHit.dropAll 1560 (swaps j) LeaveSelector.tags 0 15 ++
        (flagOps (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) true).reverse.map Op.exit) := by
  decide +kernel

/-- dadon's `Leave{s}RetireActual.result`. -/
theorem retireActual_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (k : Mode) (v : BasisState) (s : State)
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
  have rr := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
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
  middleOps s ++ Shadow7.fix10P s (Shadow7.sbP s) ++ (leaveFix11 s (Shadow7.sbP s) ++ leaveFix12 s (Shadow7.sbP s) ++ Shadow7.lowSign s)

theorem live_out (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (i : Nat) (hi : i < Shadow7.wpP (start j) + 15) :
    (live j i : Nat) ≠ 1613 ∧ ¬ (1559 ≤ (live j i : Nat) ∧ (live j i : Nat) ≤ 1597) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have b := Shadow7.bank_cases w1 w2 hi
  unfold live; split <;> unfold Wire at * <;> omega

/-- The history cells in the `sig` frame, exactly: on the B rail above every bank wire, or in the pool. -/
theorem swaps_cases (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (i : Nat) (hi : i < 15) :
    ((swaps j i : Nat) = start j + 1044 + i ∧ start j + 1044 + i ≤ 1300) ∨
      (Shadow7.e0P (start j) + 10 ≤ (swaps j i : Nat) ∧ (swaps j i : Nat) ≤ 1812) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have e := Shadow7.sig_hist (c := 1044 + i) w1 w2 (by omega) (by omega)
  unfold swaps; rw [show start j + 1044 + i = start j + (1044 + i) by omega]
  unfold Wire at *; omega

theorem free_out (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (i : Fin 17) :
    ((row j i).free : Nat) ≠ 1613 ∧ ¬ (1559 ≤ ((row j i).free : Nat) ∧ ((row j i).free : Nat) ≤ 1597) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have g := row_eq j i
  have b := Shadow7.bank_cases w1 w2 (i := i.val) (by omega)
  unfold Column.free; rw [g.2.2.1]
  split <;> simp only [g.1, g.2.1] <;> unfold Wire at * <;> omega

/-- The wires the core must not touch (dadon's `Leave{s}Core.watched` facts). -/
theorem core_untouched (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Nat)
    (hq : (1559 ≤ q ∧ q ≤ 1597) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨ q = Shadow7.e0P (start j) + 6 ∨
      q = Shadow7.e0P (start j) + 3 ∨ q = Shadow7.e0P (start j) + 4 ∨ ∃ i < 15, q = swaps j i) :
    q ≠ 1613 ∧ HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q ∧
      ∀ c ∈ cols j, q ≠ c.shadow ∧ q ≠ c.tube := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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

/-- The selector / sign wires are never B row -1 (margin-16 glue, fable-leap). -/
theorem core_apart_b (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Nat)
    (hq : (1559 ≤ q ∧ q ≤ 1597) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨ q = Shadow7.e0P (start j) + 6 ∨
      q = Shadow7.e0P (start j) + 3 ∨ q = Shadow7.e0P (start j) + 4 ∨ ∃ i < 15, q = swaps j i) :
    q ≠ Shadow7.b0P (start j) - 1 := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  rcases hq with h | h | h | h | h | ⟨i, hi, h⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · have sw := swaps_cases j h0 h1 i hi
    unfold Wire at *; omega

theorem core_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (z : SkywalkNat.State) (s : State) (tape : List Bool)
    (k : Mode) (ref : BasisState)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (odd : z.v % 2 = 1)
    (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ carries j, s.basis q = false)
    (c1613 : s.basis 1613 = false) (c1614 : s.basis 1614 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (tag : ∀ q ∈ tagsP, s.basis q = if far (Shadow7.sbP (start j)) 15 z then hot (TrueMiddle.key j z) q else false)
    (shadow : ∀ i < 17, s.basis (Shadow7.a0P (start j) - 1 + i) = (TrueMiddle.X j z).testBit i)
    (bank : regValue (ys j) s.basis = if far (Shadow7.sbP (start j)) 15 z then high (Shadow7.sbP (start j)) 15 z else 0)
    (cin : s.basis (Shadow7.e0P (start j) + 6) = if far (Shadow7.sbP (start j)) 15 z then !cross17 (TrueMiddle.d j z) else false)
    (sgn : far (Shadow7.sbP (start j)) 15 z → s.basis 1596 =
      (!(decide (2^(Shadow7.sbP (start j)) ≤ z.u)) && negative (oddBits (letters 15 (TrueMiddle.r j z)))))
    (farBit : s.basis (Shadow7.e0P (start j) + 3) = decide (far (Shadow7.sbP (start j)) 15 z))
    (bits : ∀ i : Fin 38, s.basis (1559 + i.val) = (prior j k (1559 + i.val)).read ref)
    (parity : ∀ q ∈ paritySites j, ref q = s.basis q)
    (product : s.basis 1597 = (s.basis (Shadow7.e0P (start j) + 6) && (signExpr (ports j) k).read ref))
    (leftFlag : LeaveSelector.left k = (s.basis (Shadow7.e0P (start j) + 3) && s.basis (Shadow7.e0P (start j) + 4)))
    (rightFlag : LeaveSelector.right k = (s.basis (Shadow7.e0P (start j) + 3) && !s.basis (Shadow7.e0P (start j) + 4)))
    (events : LeaveSelector.right k = true → ∀ i < 15, i ≤ LeaveSelector.key k → s.basis (swaps j i) = decide (i = LeaveSelector.key k)) :
    let out := run (GateMirror.forward (workOps (start j))) tape s
    out.phase = s.phase ∧ (∀ i < Shadow7.wpP (start j) + 15, out.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      (∀ i : Fin 17, out.basis (row j i).free = false) ∧ (∀ i : Fin 39, out.basis (1559 + i.val) = false) ∧
      (∀ q, q ≠ Shadow7.b0P (start j) - 1 → HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q →
        (∀ a ∈ cols j, q ≠ a.shadow ∧ q ≠ a.tube) → out.basis q = cleared s.basis q) ∧
      out.basis (Shadow7.b0P (start j) - 1) = (s.basis (Shadow7.b0P (start j) - 1) ^^ (decide (far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0) &&
        ((HighBankAdjust.adjusted (high (Shadow7.sbP (start j)) 15 z) (Shadow7.wpP (start j)) (HighBankSum.cross17 (TrueMiddle.d j z)) (TrueMiddle.neg j z)).testBit 0 ^^
          !HighBankSum.cross17 (TrueMiddle.d j z)))) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have s96 : s.basis 1596 = (signExpr (ports j) k).read ref := by
    have h : s.basis 1596 = (prior j k 1596).read ref := bits ⟨37, by decide⟩
    rw [control96 j h0 (by omega) k] at h
    exact h
  have gate : s.basis 1597 = (s.basis (Shadow7.e0P (start j) + 6) && s.basis 1596) := by rw [s96]; exact product
  have ar := trueMiddle_actual j h0 (by omega) z s tape small odd room clean c1613 padding tag shadow bank cin sgn gate farBit c1614
  generalize ha : run (GateMirror.forward (middleOps (start j))) tape s = a at ar
  have keepA (q : Nat) (mem : (1559 ≤ q ∧ q ≤ 1597) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨ q = Shadow7.e0P (start j) + 6 ∨
      q = Shadow7.e0P (start j) + 3 ∨ q = Shadow7.e0P (start j) + 4 ∨ ∃ i < 15, q = swaps j i) : a.basis q = s.basis q := by
    obtain ⟨diff, out, cols⟩ := core_untouched j h0 (by omega) q mem
    exact ar.2.2.2.1 q diff (core_apart_b j h0 h1 q mem) out cols
  have flag : a.basis 1613 = (((a.basis (Shadow7.e0P (start j) + 3) ^^ a.basis (Shadow7.e0P (start j) + 6)) ^^ a.basis 1596) ^^ a.basis 1597) := by
    rw [keepA (Shadow7.e0P (start j) + 3) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), keepA (Shadow7.e0P (start j) + 6) (Or.inr (Or.inr (Or.inl rfl))),
      keepA 1596 (Or.inl (by omega)), keepA 1597 (Or.inl (by omega))]
    exact ar.2.2.2.2.1
  have fix := signClose_result j h0 (by omega) s tape a ha flag
  generalize ht : run (GateMirror.forward (middleOps (start j) ++ Shadow7.fix10P (start j) (Shadow7.sbP (start j)))) tape s = t at fix
  have saved (q : Nat) (mem : (1559 ≤ q ∧ q ≤ 1597) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨ q = Shadow7.e0P (start j) + 6 ∨
      q = Shadow7.e0P (start j) + 3 ∨ q = Shadow7.e0P (start j) + 4 ∨ ∃ i < 15, q = swaps j i) : t.basis q = s.basis q := by
    obtain ⟨diff, out, cols⟩ := core_untouched j h0 (by omega) q mem
    rw [fix]; simp only [writeBit, Function.update_of_ne diff]
    exact ar.2.2.2.1 q diff (core_apart_b j h0 h1 q mem) out cols
  have retire := retireActual_result j h0 (by omega) k ref t
    (tape.drop (measurementCount (GateMirror.forward (middleOps (start j) ++ Shadow7.fix10P (start j) (Shadow7.sbP (start j))))))
    (fun i => (saved _ (Or.inl (by omega))).trans (bits i))
    (fun q h => (parity q h).trans (saved _ (Or.inr (Or.inl (by simp only [paritySites, List.mem_range'_1] at h; omega)))).symm)
    (by rw [saved 1597 (Or.inl (by omega)), saved _ (Or.inr (Or.inr (Or.inl rfl)))]; exact product)
    (by rw [saved _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), saved _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact leftFlag)
    (by rw [saved _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), saved _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact rightFlag)
    (fun on i hi h => (saved _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))))).trans (events on i hi h))
  dsimp only
  rw [show workOps (start j) = (middleOps (start j) ++ Shadow7.fix10P (start j) (Shadow7.sbP (start j))) ++
    (leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j)) from by
      simp only [workOps, List.append_assoc]]
  rw [forward_app, run_append, run_take, ht, retire]
  have base (q : Wire) (diff : q ≠ 1613) : t.basis q = a.basis q := by rw [fix]; simp [writeBit, diff]
  have pass (q : Nat) (diff : q ≠ 1613 ∧ ¬ (1559 ≤ q ∧ q ≤ 1597)) : cleared t.basis q = a.basis q := by
    rw [cleared, if_neg diff.2]; exact base _ diff.1
  refine ⟨(congrArg State.phase fix).trans ar.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h
    exact (pass _ (live_out j h0 (by omega) i h)).trans (ar.2.1 i h)
  · intro i
    exact (pass _ (free_out j h0 (by omega) i)).trans (ar.2.2.1 i)
  · intro i; have h := i.isLt
    change (if 1559 ≤ 1559 + i.val ∧ 1559 + i.val ≤ 1597 then _ else _) = _
    rw [if_pos (by omega)]
  · intro q nb out cs
    by_cases eq : q = 1613
    · subst q
      change t.basis 1613 = s.basis 1613
      rw [fix, c1613]
      simp [writeBit]
    · show cleared t.basis q = cleared s.basis q
      unfold cleared
      split
      · rfl
      · exact (base _ eq).trans (ar.2.2.2.1 _ eq nb out cs)
  · exact (pass (Shadow7.b0P (start j) - 1) ⟨by omega, by omega⟩).trans ar.2.2.2.2.2


/-! Routed (dadon's `Leave{s}Routed.result`): `body` = `fullPrefix ++ work` (cuts 5..27). -/

theorem prefix_dest : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 → ∀ q ∈ (GateMirror.forward (fullPrefix j)).map LeaveReadoutFrame.destination,
    (1559 ≤ q ∧ q ≤ 1597) ∨ q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7 := by
  decide +kernel

theorem prefix_keep (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Nat)
    (hq : ¬ ((1559 ≤ q ∧ q ≤ 1597) ∨ q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7)) (s : State) (tape : List Bool) :
    (run (GateMirror.forward (fullPrefix j)) tape s).basis q = s.basis q :=
  LeaveReadoutFrame.preserved _ s tape q (fun h => hq (prefix_dest j h0 (by omega) q h))

theorem enabled_farMode (f u : Bool) (x : Nat) :
    LeaveSelector.enabled (LeaveSelector.farMode f u x) = f := by
  cases f <;> cases u <;> simp [LeaveSelector.farMode, LeaveSelector.ofFlags, LeaveSelector.enabled]

def bodyOps (j : Fin 26) : List Gate := fullPrefix j ++ workOps (start j)

theorem routed_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (z : SkywalkNat.State) (s : State) (tape : List Bool)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (odd : z.v % 2 = 1)
    (room : high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j)))
    (clean : ∀ q ∈ carries j, s.basis q = false)
    (c1613 : s.basis 1613 = false) (c1614 : s.basis 1614 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (shadow : ∀ i < 17, s.basis (Shadow7.a0P (start j) - 1 + i) = (TrueMiddle.X j z).testBit i)
    (bank : regValue (ys j) s.basis = if far (Shadow7.sbP (start j)) 15 z then high (Shadow7.sbP (start j)) 15 z else 0)
    (zero : ∀ q ∈ [(ports j).crossing, (ports j).near] ++ List.range' 1559 39, s.basis q = false)
    (par : parityBits (ports j) s.basis = oddBits (IntegerHigh.letters 15 (reduced (Shadow7.sbP (start j)) 15 z)))
    (mode : actualMode (Shadow7.sbP (start j)) z = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u)
    (events : LeaveSelector.right (actualMode (Shadow7.sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z) →
      s.basis (swaps j i) = decide (i = LeaveSelector.key (actualMode (Shadow7.sbP (start j)) z))) :
    let out := run (GateMirror.forward (bodyOps j)) tape s
    let t := run (GateMirror.forward (fullPrefix j)) tape s
    out.phase = s.phase ∧ (∀ i < Shadow7.wpP (start j) + 15, out.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      (∀ i : Fin 17, out.basis (row j i).free = false) ∧ (∀ i : Fin 39, out.basis (1559 + i.val) = false) ∧
      (∀ q, q ≠ Shadow7.b0P (start j) - 1 → HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q →
        (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) → out.basis q = cleared t.basis q) ∧
      out.basis (Shadow7.b0P (start j) - 1) = (t.basis (Shadow7.b0P (start j) - 1) ^^ (decide (far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0) &&
        ((HighBankAdjust.adjusted (high (Shadow7.sbP (start j)) 15 z) (Shadow7.wpP (start j)) (HighBankSum.cross17 (TrueMiddle.d j z)) (TrueMiddle.neg j z)).testBit 0 ^^
          !HighBankSum.cross17 (TrueMiddle.d j z)))) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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
    (fun i hi => shadow i (Nat.lt_trans hi (by decide : 16 < 17))) par
  have flags := mode_flags (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4))
    (⟨IntegerHigh.wait 15 z.u, by have h := IntegerHigh.wait_le 15 z.u; omega⟩ : Fin 16)
  have k3 := keep (Shadow7.e0P (start j) + 3) (by omega)
  have k4 := keep (Shadow7.e0P (start j) + 4) (by omega)
  have farS : s.basis (Shadow7.e0P (start j) + 3) = decide (far (Shadow7.sbP (start j)) 15 z) := by
    have e := congrArg LeaveSelector.enabled mode
    rw [enabled_farMode, show actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (decide (far (Shadow7.sbP (start j)) 15 z))
      (decide (2^(Shadow7.sbP (start j)) ≤ z.u)) z.u from rfl, enabled_farMode] at e
    exact e.symm
  have leftOK : LeaveSelector.left k = (t.basis (Shadow7.e0P (start j) + 3) && t.basis (Shadow7.e0P (start j) + 4)) := by
    rw [k3, k4, show k = _ from mode]; exact flags.1
  have rightOK : LeaveSelector.right k = (t.basis (Shadow7.e0P (start j) + 3) && !t.basis (Shadow7.e0P (start j) + 4)) := by
    rw [k3, k4, show k = _ from mode]; exact flags.2.1
  have kc : ∀ q ∈ carries j, t.basis q = s.basis q := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    have p := Shadow7.pool_cases (i := i) w1 w2; apply keep; unfold Wire at *; omega
  have kp : ∀ i, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → t.basis (Shadow7.bankW (start j) i) = s.basis (Shadow7.bankW (start j) i) := by
    intro i a b; have bc := Shadow7.bank_cases w1 w2 b; apply keep; unfold Wire at *; omega
  have ks : ∀ i : Nat, i < 17 → t.basis (Shadow7.a0P (start j) - 1 + i) = s.basis (Shadow7.a0P (start j) - 1 + i) := by
    intro i hi; apply keep; omega
  have ky : ∀ q ∈ ys j, t.basis q = s.basis q := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    have bc := Shadow7.bank_cases w1 w2 (i := i) (by omega); apply keep; unfold Wire at *; omega
  have kpa : ∀ q ∈ paritySites j, t.basis q = s.basis q := by
    intro q hq; simp only [paritySites, List.mem_range'_1] at hq; apply keep; omega
  have ksw : ∀ i < 15, t.basis (swaps j i) = s.basis (swaps j i) := by
    intro i hi; have a := swaps_range j h0 h1 i hi; apply keep; unfold Wire at *; omega
  have done := core_result j h0 (by omega) z t (tape.drop (measurementCount (GateMirror.forward (fullPrefix j)))) k s.basis small odd room
    (fun q h => (kc q h).trans (clean q h)) ((keep 1613 (by omega)).trans c1613) ((keep 1614 (by omega)).trans c1614) (fun i lo hi => (kp i lo hi).trans (padding i lo hi))
    (fun q h => (sym q).trans (loaded_tags j h0 (by omega) z s.basis q h)) (fun i h => (ks i h).trans (shadow i h))
    (((regValue_eq_iff _ _ _).mpr (fun q h => ky q h)).trans bank)
    ((sym _).trans math.1) (fun far => by rw [sym 1596, control96 j h0 (by omega) k]; exact math.2.2 far)
    (k3.trans farS) (fun i => sym _)
    (fun q h => (kpa q h).symm) (by rw [sym 1597, sym (Shadow7.e0P (start j) + 6)]; exact math.2.1) leftOK rightOK
    (fun on i hi h => (ksw i hi).trans (events on i hi h))
  dsimp only
  rw [bodyOps, forward_app, run_append, run_take, ht]
  exact ⟨done.1.trans (by rw [prepared]), done.2⟩


/-! Restored / RoutedRestore (dadon's `Leave{s}Restored`, `Leave{s}RoutedRestore`). -/

theorem smallM_length (j : Fin 26) : (smallM j).length = Shadow7.lowsP (start j) - 1 := by simp [smallM]

/-- dadon's `Leave{s}OutputPorts.outputRegisters` (low half). -/
theorem outputSmall (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (Z : Nat)
    (bits : ∀ i < Shadow7.wpP (start j) + 15, s.basis (live j i) = Z.testBit i) :
    regValue (smallA j) s.basis = (Z / 2) % 2^(Shadow7.lowsP (start j) - 1) := by
  have rr := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
  have len : (smallA j).length = Shadow7.lowsP (start j) - 1 := by simp [smallA]
  rw [← len]
  apply EnterProof.value_of_bits (smallA j)
  intro i hi
  rw [len] at hi
  have a1 : 1 ≤ Shadow7.a0P (start j) := by unfold Shadow7.a0P; omega
  have hl : i + 1 < Shadow7.lowsP (start j) := Nat.lt_sub_iff_add_lt.mp hi
  have hl0 : Shadow7.lowsP (start j) = 17 + Shadow7.sbP (start j + 15) - Shadow7.sbP (start j) := rfl
  have g : (smallA j).getD i 0 = live j (i + 1) := by
    simp [smallA, live, List.getD_eq_getElem?_getD, hi, hl]
    unfold Wire at *; omega
  rw [g, bits (i + 1) (by omega)]; exact Nat.testBit_succ Z i

/-- dadon's `Leave{s}Restored.result`. -/
theorem restored_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (z : SkywalkNat.State) (sg : Bool) (s : State)
    (m : List Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (clean : ∀ q ∈ smallC j, s.basis q = false)
    (cleared : regValue (smallM j) s.basis = 0)
    (input : let F := step^[15] z
      let e := (PortalValues.negative sg F.u).toNat
      s.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ F.u - e) ∧
        (s.basis 1558).toNat = LeaveCompanion.upperBorrow (2^(Shadow7.sbP (start j))) F.u F.v e ∧
        regValue (smallA j) s.basis = ((F.u+F.v)/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j) - 1)) :
    let F := step^[15] z
    let e := (PortalValues.negative sg F.u).toNat
    let out := run (Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558) m s
    out.phase = s.phase ∧ (∀ q, q ∉ smallM j → out.basis q = s.basis q) ∧
      regValue (smallM j) out.basis = ((F.u - e)/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j) - 1) := by
  have hardware := restore_run j h0 (by omega) s m clean cleared
  refine ⟨hardware.1, hardware.2.1, hardware.2.2.trans ?_⟩
  dsimp only at input ⊢
  have math := LeaveRestoreTruth.restored_shadow7 (Shadow7.sbP (start j)) (Shadow7.lowsP (start j) - 1) z small.2 sg
  rw [smallM_length, copyValue, input.1, input.2.1, input.2.2]
  simpa only [decide_eq_true_eq] using math


/-! Target footprint of the Shadow7.body (for the families that read wires the Shadow7.body never writes). -/

/-- Targets of the work part of the Shadow7.body (adjust, barrel, join, the fixed tail): the A word, the B bank, and the
scratch below the anchored block `e0..e0+9` or the pool above it (never `e0+3 .. e0+9`, never the history cells). -/
def workT (j : Fin 26) (t : Nat) : Prop :=
  (Shadow7.a0P (start j) - 1 ≤ t ∧ t ≤ Shadow7.a0P (start j) + 17) ∨ (Shadow7.b0P (start j) + 17 ≤ t ∧ t ≤ 1043) ∨
    t = Shadow7.b0P (start j) - 1 ∨
    (1559 ≤ t ∧ (t ≤ Shadow7.e0P (start j) + 2 ∨ (Shadow7.e0P (start j) + 10 ≤ t ∧ t ≤ 1606 + Shadow7.wpP (start j) ∧ t + start j < 2055))) ∨
    (Shadow7.a0P (start j) + 17 ≤ t ∧ t < Shadow7.a0P (start j) + 17 + min 4 (Shadow7.wpP (start j) + start j - 448))
/-- Targets of the body: the work part plus the selector's (`fullPrefix`: `1559..1597`, `e0+6`, `e0+7`). -/
def midT (j : Fin 26) (t : Nat) : Prop := workT j t ∨ t = Shadow7.e0P (start j) + 6 ∨ t = Shadow7.e0P (start j) + 7 ∨ t = Shadow7.e0P (start j) + 3

theorem bank_workT (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (i : Nat) (hi : i < Shadow7.wpP (start j) + 15) :
    workT j (Shadow7.bankW (start j) i) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have b := Shadow7.bank_cases w1 w2 hi
  unfold workT; unfold Wire at *; omega

theorem middle_targets (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    AllAT (fun _ => True) (fun t => workT j t ∨ t = Shadow7.e0P (start j) + 3) (middleOps (start j)) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have big : ∀ t : Nat, 1559 ≤ t → t ≤ Shadow7.e0P (start j) + 2 → workT j t ∨ t = Shadow7.e0P (start j) + 3 :=
    fun t h h' => Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, Or.inl h'⟩))))
  unfold middleOps
  refine allAT_append (allAT_append (allAT_append (allAT_append ?_ ?_) ?_) ?_) ?_
  · unfold Shadow7.leaveAdjust Shadow7.leaveAdjustCore
    refine allAT_append (a := [Gate.cx (Shadow7.e0P (start j) + 6) (Shadow7.e0P (start j) + 3)]) (allAT_cons (ok_cx (A := fun _ => True) (T := fun t => workT j t ∨ t = Shadow7.e0P (start j) + 3) trivial (Or.inr rfl)) allAT_nil) ?_
    refine allAT_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) trivial trivial
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
      exact ⟨trivial, Or.inl (bank_workT j h0 (by omega) i (by omega))⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have p := Shadow7.pool_cases (i := i) w1 w2
      have pt := Shadow7.pool_top w1 w2
      exact ⟨trivial, Or.inl (by unfold workT; unfold Wire at *; omega)⟩
  · unfold Shadow7.leaveBarrel
    have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ Shadow7.wpP (start j) + 15 →
        AllAT (fun _ => True) (fun t => workT j t ∨ t = Shadow7.e0P (start j) + 3) (stageG 1613 (Shadow7.bankW (start j)) xs d n) :=
      fun xs d n hn => allAT_stageG _ _ _ _ _ ⟨trivial, big _ (by omega) (by omega)⟩ (fun _ _ => trivial)
        (fun i hi => ⟨⟨trivial, Or.inl (bank_workT j h0 (by omega) i (by omega))⟩, ⟨trivial, Or.inl (bank_workT j h0 (by omega) (i+d) (by omega))⟩⟩)
    exact allAT_append (allAT_append (allAT_append (st _ _ _ (by omega)) (st _ _ _ (by omega))) (st _ _ _ (by omega)))
      (st _ _ _ (by omega))
  · exact allAT_cons ⟨fun _ _ => trivial, big 1613 (by decide) (by omega)⟩
      (allAT_cons ⟨fun _ _ => trivial, big 1613 (by decide) (by omega)⟩
        (allAT_cons ⟨fun _ _ => trivial, big 1613 (by decide) (by omega)⟩
          (allAT_cons ⟨fun _ _ => trivial, Or.inr rfl⟩ allAT_nil)))
  · unfold Shadow7.glueG3
    have k0 := bank_workT j h0 (by omega) 0 (by omega)
    exact allAT_cons ⟨fun _ _ => trivial, Or.inl k0⟩ (allAT_cons ⟨fun _ _ => trivial, Or.inl (Or.inr (Or.inr (Or.inl rfl)))⟩
      (allAT_cons ⟨fun _ _ => trivial, Or.inl k0⟩ allAT_nil))
  · unfold Shadow7.leaveJoin
    refine allAT_append (allAT_digitsG _ _ _ _ trivial trivial _ _ (fun i _ hi => ⟨trivial, ?_, ?_⟩))
      (allAT_wordGM _ ⟨trivial, big _ (by decide) (by omega)⟩ _ (fun c hc => ?_))
    · dsimp only; left; unfold workT; omega
    · dsimp only; left; unfold workT; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      exact ⟨fun _ _ => trivial, ⟨trivial, Or.inl (by dsimp only; unfold workT; omega)⟩, ⟨trivial, Or.inl (bank_workT j h0 (by omega) i (by omega))⟩⟩

/-- The fixed tail of the work part writes only scratch below the anchored block (one decide, fixed segments). -/
theorem tail_dest : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    (Shadow7.fix10P (start j) (Shadow7.sbP (start j)) ++ (leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++
      Shadow7.lowSign (start j))).all (fun g => decide (1559 ≤ target g) && decide (target g ≤ Shadow7.e0P (start j) + 2)) = true := by
  decide +kernel

theorem work_dest (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ∀ q ∈ (GateMirror.forward (workOps (start j))).map LeaveReadoutFrame.destination,
      workT j q ∨ q = Shadow7.e0P (start j) + 3 := by
  intro q hq
  rw [dest_forward] at hq
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hq
  have t1 := tail_dest j h0 (by omega)
  rw [List.all_eq_true] at t1
  have cv (g : Gate) (h : (decide (1559 ≤ target g) && decide (target g ≤ Shadow7.e0P (start j) + 2)) = true) : workT j (target g) := by
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, Or.inl h.2⟩)))
  unfold workOps at hg
  rcases List.mem_append.mp hg with hg|hg
  · rcases List.mem_append.mp hg with hg|hg
    · exact (middle_targets j h0 (by omega) g hg).2
    · exact Or.inl (cv g (t1 g (List.mem_append_left _ hg)))
  · exact Or.inl (cv g (t1 g (List.mem_append_right _ hg)))

theorem body_dest (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ∀ q ∈ (GateMirror.forward (bodyOps j)).map LeaveReadoutFrame.destination, midT j q := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  intro q hq
  unfold bodyOps at hq
  rw [forward_app, List.map_append, List.mem_append] at hq
  rcases hq with hq|hq
  · rcases prefix_dest j h0 (by omega) q hq with h|h|h
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, Or.inl (by unfold Wire at *; omega)⟩))))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact (work_dest j h0 (by omega) q hq).elim Or.inl (fun e => Or.inr (Or.inr (Or.inr e)))

theorem routedRestore_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (z : SkywalkNat.State) (sg : Bool)
    (s : State) (m m' : List Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (mag0 : regValue (fullM j) s.basis = 0)
    (flags : let a := step^[15] (reduced (Shadow7.sbP (start j)) 15 z)
      let e := (PortalValues.negative sg a.u).toNat
      s.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ a.u - e ∨
          (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) ∧
        (s.basis 1557 = false ∧ s.basis 1558 = false))
    (liveBits : ∀ i < Shadow7.wpP (start j) + 15, (run (GateMirror.forward (bodyOps j)) m s).basis (live j i) = (TrueMiddle.F j z).testBit i)
    (bm1 : (run (GateMirror.forward (bodyOps j)) m s).basis (Shadow7.b0P (start j) - 1) =
        (((step^[15] z).u - (PortalValues.negative sg (step^[15] z).u).toNat) / 2^(Shadow7.sbP (start j))).testBit 0)
    (retired : ∀ i : Fin 39, (run (GateMirror.forward (bodyOps j)) m s).basis (1559 + i.val) = false) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let u := run (GateMirror.forward (bodyOps j)) m s
    let v := run (borrowG4 j ++ Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558) m' u
    v.phase = u.phase ∧ (∀ q, q ≠ 1557 → q ≠ 1558 → q ∉ smallM j → v.basis q = u.basis q) ∧
      regValue (smallM j) v.basis = (mag/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j) - 1) ∧
      v.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ mag) ∧
      (∀ i < Shadow7.wpP (start j) + 15, v.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      v.basis 1557 = !v.basis (Shadow7.a0P (start j) - 1) ∧
      v.basis 1558 = (v.basis (Shadow7.b0P (start j) - 1) && v.basis 1557) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have ha0 : Shadow7.a0P (start j) = start j + Shadow7.sbP (start j) + 32 := rfl
  have hb0 : Shadow7.b0P (start j) = 787 + Shadow7.sbP (start j) := rfl
  have hl0 : Shadow7.lowsP (start j) = 17 + Shadow7.sbP (start j + 15) - Shadow7.sbP (start j) := rfl
  dsimp only
  generalize hu : run (GateMirror.forward (bodyOps j)) m s = u at liveBits retired bm1 ⊢
  have keep (q : Wire) (h : (q : Nat) = 1556 ∨ (q : Nat) = 1557 ∨ (q : Nat) = 1558 ∨
      (Shadow7.b0P (start j) ≤ q ∧ (q : Nat) < Shadow7.b0P (start j) + 16)) : u.basis q = s.basis q := by
    rw [← hu]
    exact LeaveReadoutFrame.preserved _ _ _ q (fun hm => by
      have := body_dest j h0 (by omega) q hm; unfold midT workT at this; unfold Wire at *; omega)
  -- membership facts
  have notM (q : Wire) (h : (q : Nat) < Shadow7.b0P (start j) ∨ Shadow7.b0P (start j) + 16 ≤ q) : q ∉ smallM j := by
    intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi; unfold Wire at *; omega
  have liveA (i : Nat) (hi : i < Shadow7.wpP (start j) + 15) :
      (live j i : Nat) ≠ 1557 ∧ (live j i : Nat) ≠ 1558 ∧ ((live j i : Nat) < Shadow7.b0P (start j) ∨ Shadow7.b0P (start j) + 16 ≤ live j i) := by
    have b := Shadow7.bank_cases w1 w2 hi
    by_cases hl : i < Shadow7.lowsP (start j)
    · simp only [live, if_pos hl]; unfold Wire at *; omega
    · simp only [live, if_neg hl]; unfold Wire at *; omega
  have hA : u.basis (Shadow7.a0P (start j) - 1) = (TrueMiddle.F j z).testBit 0 := by
    have l0 := liveBits 0 (by omega)
    have e : live j 0 = Shadow7.a0P (start j) - 1 := by
      unfold live; rw [if_pos (by omega)]; rfl
    rwa [e] at l0
  have clear : ∀ q ∈ smallC j, u.basis q = false := by
    intro q h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h; rw [List.mem_range] at hi
    exact retired ⟨i, by omega⟩
  have mag : regValue (smallM j) u.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h; rw [List.mem_range] at hi
    refine (keep _ (Or.inr (Or.inr (Or.inr ⟨by show Shadow7.b0P (start j) ≤ Shadow7.b0P (start j) + i; omega,
      by show Shadow7.b0P (start j) + i < Shadow7.b0P (start j) + 16; omega⟩)))).trans
      ((regValue_zero _ _).mp mag0 _ ?_)
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
  have u57 : u.basis 1557 = false := (keep 1557 (Or.inr (Or.inl rfl))).trans flags.2.1
  have u58 : u.basis 1558 = false := (keep 1558 (Or.inr (Or.inr (Or.inl rfl)))).trans flags.2.2
  -- G4: 1557 := !A(-1), 1558 := B(-1) && !A(-1)
  have na : (Shadow7.a0P (start j) - 1 : Wire) ≠ 1557 ∧ (Shadow7.a0P (start j) - 1 : Wire) ≠ 1558 := by
    unfold Wire at *; omega
  have nb : (Shadow7.b0P (start j) - 1 : Wire) ≠ 1557 ∧ (Shadow7.b0P (start j) - 1 : Wire) ≠ 1558 := by
    unfold Wire at *; omega
  generalize hg : run (borrowG4 j) (m'.take (measurementCount (borrowG4 j))) u = g
  have gph : g.phase = u.phase := by rw [← hg]; simp [borrowG4, run]
  have gq (q : Wire) (n7 : q ≠ 1557) (n8 : q ≠ 1558) : g.basis q = u.basis q := by
    rw [← hg]; simp [borrowG4, run, writeBit, Function.update_apply, n7, n8]
  have g57 : g.basis 1557 = !u.basis (Shadow7.a0P (start j) - 1) := by
    rw [← hg]; simp [borrowG4, run, writeBit, Function.update_apply, na.1, na.1.symm, u57]
  have g58 : g.basis 1558 = (u.basis (Shadow7.b0P (start j) - 1) && !u.basis (Shadow7.a0P (start j) - 1)) := by
    rw [← hg]; simp [borrowG4, run, writeBit, Function.update_apply, na.1, na.2, nb.1, nb.2, na.1.symm, na.2.symm, nb.1.symm, nb.2.symm, u57, u58]
  have ch := LeaveRestoreTruth.truth_shadow7 (Shadow7.sbP (start j)) z small.1 sg
  dsimp only at ch flags
  have latch : g.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ (step^[15] z).u - (PortalValues.negative sg (step^[15] z).u).toNat) := by
    rw [gq 1556 (by decide) (by decide), keep 1556 (Or.inl rfl), flags.1, ch.1, ← ch.2.1]
    simp
  have borrow : (g.basis 1558).toNat = LeaveCompanion.upperBorrow (2^(Shadow7.sbP (start j))) (step^[15] z).u (step^[15] z).v
      (PortalValues.negative sg (step^[15] z).u).toNat := by
    rw [g58, bm1, hA, LeaveShadowRails.borrow_bits _ _ _ _ (Nat.two_pow_pos _), Nat.testBit_zero, Nat.testBit_zero]
    unfold TrueMiddle.F total
    have hX := Nat.mod_two_eq_zero_or_one
      (((step^[15] z).u - (PortalValues.negative sg (step^[15] z).u).toNat) / 2 ^ Shadow7.sbP (start j))
    have hS := Nat.mod_two_eq_zero_or_one (((step^[15] z).u + (step^[15] z).v) / 2 ^ Shadow7.sbP (start j))
    rcases hX with p1 | p1 <;> rcases hS with p2 | p2 <;> simp only [p1, p2] <;> decide
  have reg : regValue (smallA j) g.basis = ((step^[15] z).u + (step^[15] z).v) / 2^(Shadow7.sbP (start j) + 1) %
      2^(Shadow7.lowsP (start j) - 1) := by
    have o := outputSmall j h0 (by omega) g (TrueMiddle.F j z) (fun i hi => by
      obtain ⟨l7, l8, -⟩ := liveA i hi
      rw [gq _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)]; exact liveBits i hi)
    rw [o]; unfold TrueMiddle.F total; rw [Nat.div_div_eq_div_mul, ← pow_succ]
  have clearG : ∀ q ∈ smallC j, g.basis q = false := by
    intro q h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h; rw [List.mem_range] at hi
    rw [gq _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)]; exact clear _ h
  have magG : regValue (smallM j) g.basis = 0 :=
    ((regValue_eq_iff _ _ _).mpr (fun q h => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h; rw [List.mem_range] at hi
      exact gq _ (by unfold Wire at *; omega) (by unfold Wire at *; omega))).trans mag
  have new := restored_result j h0 (by omega) z sg g (m'.drop (measurementCount (borrowG4 j))) small clearG magG
    ⟨latch, borrow, reg⟩
  rw [run_append, hg]
  have vq (q : Wire) (n7 : q ≠ 1557) (n8 : q ≠ 1558) (nm : q ∉ smallM j) :
      (run (Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558) (m'.drop (measurementCount (borrowG4 j))) g).basis q =
        u.basis q := (new.2.1 q nm).trans (gq q n7 n8)
  have v7 := new.2.1 1557 (notM 1557 (Or.inr (by omega)))
  have v8 := new.2.1 1558 (notM 1558 (Or.inr (by omega)))
  have vA := vq _ na.1 na.2 (notM _ (Or.inl (by unfold Wire at *; omega)))
  have vB := vq _ nb.1 nb.2 (notM _ (Or.inl (by unfold Wire at *; omega)))
  refine ⟨new.1.trans gph, vq, new.2.2, ?_, ?_, ?_, ?_⟩
  · rw [vq 1556 (by decide) (by decide) (notM 1556 (Or.inr (by omega)))]
    rw [← gq 1556 (by decide) (by decide)]; exact latch
  · intro i hi
    obtain ⟨l7, l8, lm⟩ := liveA i hi
    rw [vq _ (by unfold Wire at *; omega) (by unfold Wire at *; omega) (notM _ lm)]; exact liveBits i hi
  · rw [v7, vA, g57]
  · rw [v8, vB, v7, g58, g57]

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
def bankPair (s i : Nat) : Wire × Wire := (Shadow7.bankW s (Shadow7.lowsP s + i), bTopP (s+15) + 3 + i - Shadow7.wpP (s+15))
/-- The six flag pairs of `Shadow7.movesP s`. -/
def flagPairs (s : Nat) : List (Wire × Wire) :=
  [(1557, Shadow7.e0P (s+15) + 3), (1558, Shadow7.e0P (s+15) + 4), (Shadow7.e0P s + 5, Shadow7.e0P (s+15) + 5),
   (Shadow7.e0P s + 3, Shadow7.e0P (s+15) + 6), (Shadow7.e0P s + 7, Shadow7.e0P (s+15) + 7), (Shadow7.e0P s + 6, Shadow7.e0P (s+15) + 8)]

theorem moves_split (s : Nat) :
    Shadow7.movesP s = (List.range (Shadow7.wpP (s+15) - 2)).map (bankPair s) ++ flagPairs s := rfl

/-- Closed forms of the chain (all block facts the proofs below use); `D0 = 803 + Shadow7.sbP (s+15)`,
`n = Shadow7.wpP (s+15) - 2`, `m = Shadow7.wpP s - Shadow7.lowsP s` (the B-branch count). -/
theorem chain_geo {s : Nat} (h1 : 45 ≤ s) (h2 : s ≤ 405) :
    (∀ i, (bankPair s i).2 = 803 + Shadow7.sbP (s+15) + i) ∧
    (∀ i, i < Shadow7.wpP s - Shadow7.lowsP s → (bankPair s i).1 = 803 + Shadow7.sbP (s+15) + 15 + i) ∧
    (∀ i, Shadow7.wpP s - Shadow7.lowsP s ≤ i → (bankPair s i).1 = 1598 + i - (Shadow7.wpP s - Shadow7.lowsP s)) ∧
    Shadow7.wpP s - Shadow7.lowsP s ≤ Shadow7.wpP (s+15) - 2 ∧ Shadow7.wpP (s+15) - 2 ≤ Shadow7.wpP s - Shadow7.lowsP s + 15 ∧ 15 ≤ Shadow7.wpP (s+15) - 2 ∧
    803 + Shadow7.sbP (s+15) + 14 + (Shadow7.wpP s - Shadow7.lowsP s) = bTopP s ∧ 803 + Shadow7.sbP (s+15) + (Shadow7.wpP (s+15) - 2) = bTopP (s+15) + 1 ∧
    bTopP s ≤ 1043 ∧ bTopP (s+15) ≤ bTopP s ∧ 1613 ≤ Shadow7.e0P (s+15) ∧ Shadow7.e0P (s+15) + 7 ≤ Shadow7.e0P s ∧
    Shadow7.e0P s ≤ Shadow7.e0P (s+15) + 8 ∧ 803 + Shadow7.sbP (s+15) + 1 = Shadow7.b0P s + Shadow7.lowsP s ∧ 9 ≤ Shadow7.lowsP s ∧ Shadow7.lowsP s ≤ 10 ∧
    Shadow7.lowsP s + 3 ≤ Shadow7.wpP s ∧ 803 + Shadow7.sbP (s+15) ≥ 803 + 39 := by
  have r := Shadow7.rail_win h1 (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have hR : railP s ≤ railP (s+15) + 15 := by unfold railP; split_ifs <;> omega
  have hsb : 39 ≤ Shadow7.sbP (s+15) := by unfold Shadow7.sbP; omega
  refine ⟨fun i => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold bankPair; dsimp only; ((try unfold Wire at *); omega)
  · unfold bankPair Shadow7.bankW; dsimp only
    rw [if_neg (by omega), if_pos (by omega)]; ((try unfold Wire at *); omega)
  · unfold bankPair Shadow7.bankW; dsimp only
    rw [if_neg (by omega), if_neg (by omega)]; ((try unfold Wire at *); omega)
  all_goals ((try unfold Wire at *); omega)

/-- dadon's `upperMap` direction: the next tick's B word `D0 + i` takes the bank wire `a i`. -/
theorem src_d (s : Nat) (h1 : 45 ≤ s) (h2 : s ≤ 405) (i : Nat) (hi : i < Shadow7.wpP (s+15) - 2) :
    source (Shadow7.movesP s) (803 + Shadow7.sbP (s+15) + i) = Shadow7.bankW s (Shadow7.lowsP s + i) := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  rw [moves_split, LeaveRelocation.append]
  rw [LeaveRelocation.outside (flagPairs s) (803 + Shadow7.sbP (s+15) + i) (by
    intro p hp
    simp only [flagPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> constructor <;> ((try unfold Wire at *); omega))]
  have ab (k : Nat) :
      ((bankPair s k).1 = 803 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  rw [src_above (bankPair s) (i+1) (803 + Shadow7.sbP (s+15) + i) (Shadow7.wpP (s+15) - 2) (by omega) (by
    intro k a b
    rw [hd k]
    rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rw [e] <;> constructor <;> ((try unfold Wire at *); omega))]
  rw [src_succ, hd i, flip_snd (a := (bankPair s i).1) (b := 803 + Shadow7.sbP (s+15) + i) (by rcases ab i with ⟨e, ei⟩ | ⟨e, ei⟩ <;> rw [e] <;> ((try unfold Wire at *); omega))]
  rw [src_untouched (bankPair s) i (bankPair s i).1 (by
    intro k hk
    rw [hd k]
    rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rcases ab i with ⟨e', ei⟩ | ⟨e', ei⟩ <;> rw [e, e'] <;>
      constructor <;> ((try unfold Wire at *); omega))]
  rfl

/-- The chain down: before pair `i`, the wire `D0 + i` reads `D0 + i % 15`. -/
theorem src_chain (s : Nat) (h1 : 45 ≤ s) (h2 : s ≤ 405) :
    ∀ i, i < Shadow7.wpP (s+15) - 2 →
      source ((List.range i).map (bankPair s)) (803 + Shadow7.sbP (s+15) + i) = 803 + Shadow7.sbP (s+15) + i % 15 := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  have ab (k : Nat) :
      ((bankPair s k).1 = 803 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases small : i < 15
    · rw [src_untouched (bankPair s) i (803 + Shadow7.sbP (s+15) + i) (by
        intro k hk
        rw [hd k]
        rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rw [e] <;> constructor <;> ((try unfold Wire at *); omega))]
      rw [Nat.mod_eq_of_lt small]
    · have kB : i - 15 < Shadow7.wpP s - Shadow7.lowsP s := by omega
      rw [src_above (bankPair s) (i - 15 + 1) (803 + Shadow7.sbP (s+15) + i) i (by omega) (by
        intro k a b
        rw [hd k]
        rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rw [e] <;> constructor <;> ((try unfold Wire at *); omega))]
      rw [src_succ, show 803 + Shadow7.sbP (s+15) + i = (bankPair s (i - 15)).1 by rw [hB _ kB]; omega, flip_fst,
        hd (i - 15), ih (i - 15) (by omega) (by omega)]
      congr 1
      omega

/-- The freed B top and the pool: a bank wire that is no next-tick word reads `D0 + i % 15`. -/
theorem src_top (s : Nat) (h1 : 45 ≤ s) (h2 : s ≤ 405) (i : Nat) (hi : i < Shadow7.wpP (s+15) - 2)
    (top : Shadow7.lowsP s + i < Shadow7.wpP s → Shadow7.wpP (s+15) - 2 ≤ i + 15) :
    source (Shadow7.movesP s) (Shadow7.bankW s (Shadow7.lowsP s + i)) = 803 + Shadow7.sbP (s+15) + i % 15 := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  have ab (k : Nat) :
      ((bankPair s k).1 = 803 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  have top' : Shadow7.wpP (s+15) - 2 ≤ i + 15 ∨ Shadow7.wpP s - Shadow7.lowsP s ≤ i := by
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
  rw [src_above (bankPair s) (i+1) (bankPair s i).1 (Shadow7.wpP (s+15) - 2) (by omega) (by
    intro k a b
    rw [hd k]
    rcases ab k with ⟨e, ek⟩ | ⟨e, ek⟩ <;> rcases ab i with ⟨e', ei⟩ | ⟨e', ei⟩ <;> rw [e, e'] <;>
      constructor <;> ((try unfold Wire at *); omega))]
  rw [src_succ, flip_fst, hd i]
  exact src_chain s h1 h2 i hi

/-- The six flag pairs. -/
theorem src_flags (s : Nat) (h1 : 45 ≤ s) (h2 : s ≤ 405) :
    source (Shadow7.movesP s) 1557 = Shadow7.e0P (s+15) + 3 ∧ source (Shadow7.movesP s) 1558 = Shadow7.e0P (s+15) + 4 ∧
    source (Shadow7.movesP s) (Shadow7.e0P s + 5) = Shadow7.e0P (s+15) + 5 ∧ source (Shadow7.movesP s) (Shadow7.e0P s + 3) = Shadow7.e0P (s+15) + 6 ∧
    source (Shadow7.movesP s) (Shadow7.e0P s + 7) = Shadow7.e0P (s+15) + 7 ∧ source (Shadow7.movesP s) (Shadow7.e0P s + 6) = Shadow7.e0P (s+15) + 8 := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  have ab (k : Nat) :
      ((bankPair s k).1 = 803 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  have bankOut (x : Wire) (hx : Shadow7.e0P (s+15) ≤ x) :
      source ((List.range (Shadow7.wpP (s+15) - 2)).map (bankPair s)) x = x := by
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
theorem src_out (s : Nat) (h1 : 45 ≤ s) (h2 : s ≤ 405) (q : Wire)
    (bank : q < 803 + Shadow7.sbP (s+15) ∨ (bTopP s < q ∧ q < 1598) ∨ 1598 + (Shadow7.wpP (s+15) - 2) - (Shadow7.wpP s - Shadow7.lowsP s) ≤ q)
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
theorem upperMapB (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ∀ i : Nat, i < railP (start j + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j)) →
      LeaveRelocation.source (Shadow7.movesP (start j)) (Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 + i) =
        Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) ∧
      LeaveRelocation.source (Shadow7.movesP (start j)) (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i) =
        Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo w1 w3
  have r := Shadow7.rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  intro i hi
  refine ⟨?_, ?_⟩
  · rw [show Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 + i = 803 + Shadow7.sbP (start j + 15) + i by omega]
    exact src_d _ w1 w3 i (by omega)
  · -- A addresses are 344..528: below the B chain (803+sb(s+15)) and below every flag (≥ 1557).
    -- Bare `omega` misses this: `Shadow7.lowsP` is a Nat subtraction, so the A wire is not linear until it is cancelled.
    have hsub : Shadow7.sbP (start j) ≤ 17 + Shadow7.sbP (start j + 15) := by omega
    have hid : Shadow7.sbP (start j) + Shadow7.lowsP (start j) = 17 + Shadow7.sbP (start j + 15) := by
      unfold Shadow7.lowsP
      have hc := Nat.sub_add_cancel hsub
      omega
    have qform : Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i =
        start j + (Shadow7.sbP (start j) + Shadow7.lowsP (start j)) + 31 + i := by
      rw [ea]; omega
    have hfit : Shadow7.sbP (start j) + Shadow7.lowsP (start j) ≤ railP (start j + 15) := by
      rw [hid]; omega
    have qlt : Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i < start j + railP (start j + 15) + 31 := by
      rw [qform, hid]; omega
    have hq : Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i < 1557 := by
      have hr : railP (start j + 15) ≤ 258 := by omega
      omega
    have hbank : Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i < 803 + Shadow7.sbP (start j + 15) := by
      have hsb15 : 39 ≤ Shadow7.sbP (start j + 15) := by omega
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
abbrev L (j : Fin 26) := W.compactSkywalkTickLayout MappedCompressed.base (start j + 15)
/-- dadon's `Leave{s}WideWords.shortL`: the block's last packet port. -/
abbrev shortL (j : Fin 26) := IntegerPacket.ports (Shadow7.shape j) 15

/-- The stock rail width at tick s+15 is par-b's `railP (s+15)` (257 at 225). -/
theorem width (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    W.compactSkywalkTickPreWidth (start j + 15) = railP (start j + 15) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  unfold W.compactSkywalkTickPreWidth W.narrowSkywalkRouteWidth railP
  split_ifs <;> omega

theorem wideMapping (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (i : Nat) (hi : i < railP (start j + 15)) :
    (L j).a.getD i 0 = OB5.sig (start j + 14) (start j + 31 + i) ∧
    (L j).b.getD i 0 = OB5.sig (start j + 14) (786 + i) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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

theorem shortMapping (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (i : Nat) (hi : i < Shadow7.sbP (start j)) :
    windowNet j ((shortL j).a.getD i 0) = start j + 31 + i ∧
    windowNet j ((shortL j).b.getD i 0) = 786 + i := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have hm : i < Shadow7.smallBits j + 15 + 1 := by unfold Shadow7.smallBits Shadow7.sbP; unfold Shadow7.sbP at hi; omega
  have ga : (shortL j).a.getD i 0 = start j + 31 + i := by
    show ((start j + 15 + 16) :: (List.range' (start j + 15 + 16 + 1) (Shadow7.smallBits j + 15) ++
      [start j + 15 + 16 + (Shadow7.smallBits j + 15 + 1)])).getD i 0 = _
    rcases i with _ | i
    · simp only [List.getD_cons_zero]
    · have hlen : i < (List.range' (start j + 15 + 16 + 1) (Shadow7.smallBits j + 15)).length := by
        rw [List.length_range']; omega
      rw [List.getD_cons_succ, List.getD_append _ _ _ _ hlen, List.getD_eq_getElem?_getD,
        List.getElem?_range' (by omega : i < Shadow7.smallBits j + 15), Option.getD_some]
      omega
  have gb : (shortL j).b.getD i 0 = 786 + i := by
    show (786 :: (List.range' 787 (Shadow7.smallBits j + 15) ++ [786 + (Shadow7.smallBits j + 15 + 1)])).getD i 0 = _
    rcases i with _ | i
    · simp only [List.getD_cons_zero]
    · have hlen : i < (List.range' 787 (Shadow7.smallBits j + 15)).length := by
        rw [List.length_range']; omega
      rw [List.getD_cons_succ, List.getD_append _ _ _ _ hlen, List.getD_eq_getElem?_getD,
        List.getElem?_range' (by omega : i < Shadow7.smallBits j + 15), Option.getD_some]
      omega
  rw [ga, gb]
  unfold windowNet net OB5.sig
  constructor
  · rw [if_neg (by unfold Shadow7.sbP at hi; ((try unfold Wire at *); omega))]
  · rw [if_neg (by unfold Shadow7.sbP at hi; ((try unfold Wire at *); omega))]

/-- dadon's `Leave{s}WideWords.wide`, for every index of the next tick's rails. -/
theorem wide (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (a : SkywalkNat.State) (G sg : Bool) (raw : State)
    (input : SkywalkIntegerInput (L j) (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G
      raw.basis)
    (i : Fin (railP (start j + 15))) :
    let o := pullState (OB5.sig (start j + 14)) raw
    let e := negative sg a.u
    let pos := (a.u+a.v).testBit i.val
    let neg := (a.u-e.toNat).testBit i.val ^^ e
    o.basis (start j + 31 + i.val) = (if G then neg else pos) ∧ o.basis (786 + i.val) = (if G then pos else neg) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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
theorem short (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (a : SkywalkNat.State) (G sg : Bool) (s : State)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg a.u a.v) s.basis) (i : Fin (Shadow7.sbP (start j))) :
    let e := negative sg a.u
    let pos := (a.u+a.v).testBit i.val
    let neg := (a.u-e.toNat).testBit i.val ^^ e
    s.basis (start j + 31 + i.val) = (if G then neg else pos) ∧ s.basis (786 + i.val) = (if G then pos else neg) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have maxA : Shadow7.sbP (start j) ≤ (shortL j).a.length := by
    show Shadow7.sbP (start j) ≤ ((start j + 15 + 16) :: (List.range' (start j + 15 + 16 + 1) (Shadow7.smallBits j + 15) ++
      [start j + 15 + 16 + (Shadow7.smallBits j + 15 + 1)])).length
    simp only [List.length_cons, List.length_append, List.length_range', List.length_singleton]
    unfold Shadow7.smallBits Shadow7.sbP; omega
  have maxB : Shadow7.sbP (start j) ≤ (shortL j).b.length := by
    show Shadow7.sbP (start j) ≤ (786 :: (List.range' 787 (Shadow7.smallBits j + 15) ++ [786 + (Shadow7.smallBits j + 15 + 1)])).length
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
theorem env_geo {s : Nat} (h1 : 45 ≤ s) (h2 : s ≤ 405) :
    Shadow7.wpP s + (Shadow7.sbP s + 15) = railP s ∧ (s < 257 → 257 ≤ railP s) ∧ (257 ≤ s → railP s = 513 - s) ∧
      Shadow7.sbP s ≤ 226 ∧ 2 ≤ Shadow7.wpP s := by
  unfold Shadow7.wpP railP Shadow7.sbP
  refine ⟨?_, fun h => ?_, fun h => ?_, ?_, ?_⟩ <;> (try split_ifs) <;> omega

set_option exponentiation.threshold 600 in
/-- dadon's `LeaveTerminalBound.fit` (255) / `fit210`: the leave's output word fits the next tick's rail,
`F < 2^(R(s+15) - sb - 1)` (255: 2^113, 210: 2^105, 225: 2^112 = the bank width). -/
theorem terminal_fit (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (x p : Nat) (good : WideReference.Bounds x p) :
    TrueMiddle.F j (step^[start j] (init x p)) < 2^(railP (start j + 15) - Shadow7.sbP (start j)) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have hx : x < 2^256 := lt_trans good.small good.cap
  have it : step^[15] (step^[start j] (init x p)) = step^[start j + 15] (init x p) := by
    rw [← Function.iterate_add_apply, Nat.add_comm]
  have fits : Shadow7.sbP (start j) ≤ railP (start j + 15) := by unfold railP Shadow7.sbP; split_ifs <;> omega
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

set_option exponentiation.threshold 600 in
theorem terminal_fit_early_store (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (x p : Nat) (good : WideReference.Bounds x p) :
    TrueMiddle.F j (step^[start j] (init x p)) < 2^(min 257 (railP (start j + 15)) - Shadow7.sbP (start j)) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have hx : x < 2^256 := lt_trans good.small good.cap
  have it : step^[15] (step^[start j] (init x p)) = step^[start j + 15] (init x p) := by
    rw [← Function.iterate_add_apply, Nat.add_comm]
  have fits : Shadow7.sbP (start j) ≤ min 257 (railP (start j + 15)) := by unfold railP Shadow7.sbP; split_ifs <;> omega
  have env : (step^[start j + 15] (init x p)).u + (step^[start j + 15] (init x p)).v < 2^(min 257 (railP (start j + 15))) := by
    by_cases hs : start j + 15 < 257
    · calc _ ≤ 2^256 + 2^255 := sum_early x p _ hx good.cap (by omega)
        _ < 2^257 := by norm_num
        _ ≤ 2^(min 257 (railP (start j + 15))) := Nat.pow_le_pow_right (by norm_num) (by unfold railP; split_ifs <;> omega)
    · calc _ ≤ 2^(512 - (start j + 15)) := sum_late x p _ good (by omega)
        _ < 2^(min 257 (railP (start j + 15))) := Nat.pow_lt_pow_right (by norm_num) (by unfold railP; split_ifs <;> omega)
  unfold TrueMiddle.F
  rw [it, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel fits]
  exact env

section
set_option exponentiation.threshold 650

private theorem capped_half {bound k n d : Nat} (h : 2^k*n < bound) (hd : d ≤ n) :
    2^(k+1)*(d/2) < bound := by
  rw [pow_succ,Nat.mul_assoc]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (show 2*(d/2) ≤ n by omega)) h

private theorem next_capped {bound : Nat} (z : SkywalkNat.State) (a b : Nat)
    (hu : 2^a*z.u < bound) (hv : 2^b*z.v < bound) :
    ∃ c d : Nat, c+d=a+b+1 ∧ 2^c*(step z).u < bound ∧ 2^d*(step z).v < bound := by
  unfold step
  split_ifs with zero even order
  · exact ⟨a+1,b,by omega,by have hc : 0 < bound := lt_of_le_of_lt (Nat.zero_le _) hu; simpa [zero] using hc,hv⟩
  · exact ⟨a+1,b,by omega,capped_half hu (le_refl _),hv⟩
  · exact ⟨a+1,b,by omega,capped_half hu (Nat.sub_le _ _),hv⟩
  · exact ⟨b+1,a,by omega,capped_half hv (Nat.sub_le _ _),hu⟩

private theorem capped_scales {bound : Nat} (x p t : Nat) (hx : x < bound) (hp : p < bound) :
    let z := step^[t] (init x p)
    ∃ a b : Nat, a+b=t ∧ 2^a*z.u < bound ∧ 2^b*z.v < bound := by
  induction t with
  | zero =>
    exact ⟨0,0,rfl,by simpa [init] using hx,by simpa [init] using hp⟩
  | succ i ih =>
    obtain ⟨a,b,count,hu,hv⟩ := ih
    obtain ⟨c,d,total,nu,nv⟩ := next_capped (step^[i] (init x p)) a b hu hv
    rw [Function.iterate_succ_apply']
    exact ⟨c,d,by omega,nu,nv⟩

private theorem unscale {a u : Nat} (pos : 0 < u) (h : 2^a*u < 2^256) :
    a < 256 ∧ u < 2^(256-a) := by
  have lt : a < 256 := by
    by_contra! lo
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) lo
    have hm := Nat.mul_le_mul_left (2^a) pos
    rw [Nat.mul_one] at hm
    omega
  refine ⟨lt,Nat.lt_of_mul_lt_mul_left (a := 2^a) ?_⟩
  rw [← pow_add,Nat.add_sub_of_le lt.le]
  exact h

theorem scaled_sum_strict (x p t : Nat) (good : WideReference.Bounds x p) (ht : t < 512) :
    (step^[t] (init x p)).u + (step^[t] (init x p)).v < 2^(512-t) := by
  let z := step^[t] (init x p)
  change z.u+z.v < 2^(512-t)
  have valid := iter_valid t (init x p) good.positive good.odd
  change 0<z.v ∧ z.v%2=1 ∧ z.u.gcd z.v=x.gcd p at valid
  by_cases empty : z.u=0
  · have hg := valid.2.2
    rw [empty,Nat.gcd_zero_left] at hg
    have one : z.v=1 := hg.trans good.coprime
    rw [empty,one,Nat.zero_add]
    exact Nat.one_lt_two_pow (by omega)
  · obtain ⟨a,b,total,hu,hv⟩ := capped_scales x p t (lt_trans good.small good.cap) good.cap
    obtain ⟨aa,smallU⟩ := unscale (Nat.pos_of_ne_zero empty) (show 2^a*z.u < 2^256 from hu)
    obtain ⟨bb,smallV⟩ := unscale valid.1 (show 2^b*z.v < 2^256 from hv)
    have bound := Nat.mul_le_mul smallU smallV
    rw [← pow_add,show 256-a+(256-b)=512-t by omega] at bound
    nlinarith only [bound]

private theorem gap_any_small {a v p : Nat} (h : 2^a*v ≤ p) : v ≤ p := by
  have mul := Nat.mul_le_mul_right v (show 1 ≤ 2^a by exact Nat.two_pow_pos _)
  simpa using mul.trans h

private theorem gap_large_exp {a v p : Nat} (ha : 224 ≤ a) (value : 2^a*v ≤ p) (cap : p < 2^256) : v < 2^32 := by
  apply Nat.lt_of_mul_lt_mul_left (a := 2^224)
  have power := Nat.pow_le_pow_right (by decide : 0 < 2) ha
  calc 2^224 * v ≤ 2^a * v := Nat.mul_le_mul_right _ power
       _ ≤ p := value
       _ < 2^224 * 2^32 := by norm_num at cap ⊢; exact cap

private theorem early_ceiling {a b u v p t : Nat} (h : a+b=t) (hu : 2^a*u ≤ p)
    (hv : 2^b*v ≤ p) (cap : p < 2^256) (gap : p+2^32 ≤ 2^256) (ht : 224 ≤ t) : u+v < 2^256 := by
  by_cases az : a=0
  · have small := gap_large_exp (a := b) (by omega) hv cap
    have big := gap_any_small hu
    omega
  by_cases bz : b=0
  · have small := gap_large_exp (a := a) (by omega) hu cap
    have big := gap_any_small hv
    omega
  have ua := Nat.mul_le_mul_right u (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ a))
  have vb := Nat.mul_le_mul_right v (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ b))
  simp only [pow_one] at ua vb
  omega

private theorem gap_one_side {b v p t : Nat} (hb : b+255=t) (hv : 2^b*v ≤ p)
    (gap : p+2^32 ≤ 2^256) (hi : t ≤ 286) : v+1 < 2^(511-t) := by
  have low : 2^b < 2^32 := Nat.pow_lt_pow_right (by decide) (by omega)
  apply Nat.lt_of_mul_lt_mul_left (a := 2^b)
  rw [←pow_add,show b+(511-t)=256 by omega,Nat.mul_add,Nat.mul_one]
  omega

private theorem mid_ceiling {a b u v p t : Nat} (h : a+b=t) (hu : 2^a*u ≤ p)
    (hv : 2^b*v ≤ p) (pu : 0<u) (pv : 0<v) (cap : p < 2^256)
    (gap : p+2^32 ≤ 2^256) (hi : t≤286) : u+v < 2^(511-t) := by
  obtain ⟨aa,smallU⟩ := unscale pu (lt_of_le_of_lt hu cap)
  obtain ⟨bb,smallV⟩ := unscale pv (lt_of_le_of_lt hv cap)
  by_cases ea : a=255
  · have vs := gap_one_side (b := b) (by omega) hv gap hi
    rw [ea] at smallU
    norm_num at smallU
    omega
  by_cases eb : b=255
  · have us := gap_one_side (b := a) (by omega) hu gap hi
    rw [eb] at smallV
    norm_num at smallV
    omega
  have ub := smallU.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 256-a ≤ 510-t))
  have vb := smallV.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 256-b ≤ 510-t))
  rw [show 511-t=(510-t)+1 by omega,pow_succ]
  omega

theorem prime_gap_sum (x p t : Nat) (good : WideReference.Bounds x p) (lo : 224 ≤ t) (hi : t ≤ 286) :
    (step^[t] (init x p)).u + (step^[t] (init x p)).v < 2^(min 256 (511-t)) := by
  let z := step^[t] (init x p)
  change z.u + z.v < 2^(min 256 (511-t))
  obtain ⟨a,b,total,hu,hv⟩ := capped_scales x p t (bound := p+1) (by have := good.small; omega) (by omega)
  have xu : 2^a*z.u ≤ p := Nat.le_of_lt_succ hu
  have xv : 2^b*z.v ≤ p := Nat.le_of_lt_succ hv
  by_cases early : 256 ≤ 511-t
  · rw [Nat.min_eq_left early]
    exact early_ceiling total xu xv good.cap good.gap lo
  rw [Nat.min_eq_right (by omega)]
  have valid := iter_valid t (init x p) good.positive good.odd
  change 0<z.v ∧ z.v%2=1 ∧ z.u.gcd z.v=x.gcd p at valid
  by_cases empty : z.u=0
  · have hg := valid.2.2
    rw [empty,Nat.gcd_zero_left] at hg
    rw [empty,hg.trans good.coprime,Nat.zero_add]
    exact Nat.one_lt_two_pow (by omega)
  exact mid_ceiling total xu xv (Nat.pos_of_ne_zero empty) valid.1 good.cap good.gap hi
end

set_option exponentiation.threshold 600 in
theorem terminal_fit_store (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (x p : Nat) (good : WideReference.Bounds x p) :
    TrueMiddle.F j (step^[start j] (init x p)) < 2^(Shadow7.liveW (start j)) := by
  have limit := (start_win7 j h0 h1).2
  unfold Shadow7.liveW
  have it : step^[15] (step^[start j] (init x p)) = step^[start j+15] (init x p) := by
    rw [← Function.iterate_add_apply,Nat.add_comm]
  split_ifs with mid late
  · have fits : Shadow7.sbP (start j) ≤ min 256 (511-(start j+15)) := by unfold Shadow7.sbP; omega
    unfold TrueMiddle.F
    rw [it,Nat.div_lt_iff_lt_mul (by positivity),← pow_add,Nat.sub_add_cancel fits]
    exact prime_gap_sum x p _ good mid.1 mid.2
  · have fits : Shadow7.sbP (start j) ≤ 512-(start j+15) := by unfold Shadow7.sbP; omega
    unfold TrueMiddle.F
    rw [it,Nat.div_lt_iff_lt_mul (by positivity),← pow_add,Nat.sub_add_cancel fits]
    exact scaled_sum_strict x p _ good (by omega)
  · exact terminal_fit_early_store j h0 h1 x p good

namespace Admission

/-- dadon's `Leave{s}Admission.Numeric` (225: sb 144, Wp 97, next sb 136, W 112). -/
structure Numeric (j : Fin 26) (z : SkywalkNat.State) : Prop where
  farSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z
  odd : z.v % 2 = 1
  room : Shadow.high (Shadow7.sbP (start j)) 15 z + 1 < 2^(Shadow7.wpP (start j))
  endSmall : Shadow7.EndSmall (Shadow7.sbP (start j)) z
  nextFarSmall : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 (SkywalkNat.step^[15] z)
  bound : TrueMiddle.F j z < 2^(Shadow7.wpP (start j) + 15)
  fit : TrueMiddle.F j z < 2^(Shadow7.liveW (start j))

/-- dadon's `Leave{s}Admission.actualNumbers`, for every window block. Takes `Bounds` (coprime inputs): from
tick 257 on the room comes from the product bound. -/
theorem actualNumbers (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (x p : Nat) (good : WideReference.Bounds x p) :
    Numeric j (SkywalkNat.step^[start j] (SkywalkNat.init x p)) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  obtain ⟨g1, g2, g3, g4, g5⟩ := env_geo w1 w3
  have hx : x < 2^256 := lt_trans good.small good.cap
  have env := env_room (S := (step^[start j] (init x p)).u + (step^[start j] (init x p)).v)
    (e := Shadow7.sbP (start j) + 15) (W := Shadow7.wpP (start j)) (by
      by_cases hs : start j < 257
      · have := g2 hs
        exact Or.inl ⟨by omega, by omega, sum_early x p _ hx good.cap (by omega)⟩
      · have := g3 (by omega)
        refine Or.inr ⟨by omega, ?_⟩
        rw [show Shadow7.wpP (start j) - 1 + (Shadow7.sbP (start j) + 15) = 512 - start j by omega]
        exact sum_late x p _ good (by omega))
  have it : step^[15] (step^[start j] (init x p)) = step^[start j + 15] (init x p) := by
    rw [← Function.iterate_add_apply, Nat.add_comm]
  have now := Shadow7.Envelope.inputs x p (start j) hx good.cap (by omega)
  refine ⟨now.1, (iter_valid (start j) (init x p) good.positive good.odd).2.1, env.1, now.2,
    Shadow7.Envelope.nextFarSmall x p (start j) hx good.cap (by omega), ?_, terminal_fit_store j h0 (by omega) x p good⟩
  · unfold TrueMiddle.F
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show Shadow7.wpP (start j) + 15 + Shadow7.sbP (start j) = Shadow7.wpP (start j) + (Shadow7.sbP (start j) + 15) by omega]
    exact lt_of_le_of_lt (iter_sum_nonincrease 15 _) env.2

/-- dadon's `Leave{s}Admission.flags` (block-independent). -/
def flags (z : SkywalkNat.State) (g0 s0 : Bool) : Bool × Bool :=
  SharedSigned.flags g0 s0 (SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v))

end Admission

theorem native_carryJ_lt (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (z : SkywalkRails.State) (s : State)
    (ready : Shadow7.onRails j 15 z s.basis) :
    ∀ q : Wire, 1556 ≤ q → (q : Nat) + 2 < Shadow7.e0P (start j) → s.basis q = false := by
  intro q lo hi
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  apply Shadow7.native_carry _ _ _ ready
  refine List.mem_map.mpr ⟨q, ?_, ?_⟩
  · simp only [IntegerPacket.ports, Shadow7.shape, List.mem_range'_1]
    unfold Shadow7.smallBits Shadow7.sbP; unfold Shadow7.e0P Shadow7.sbP at hi; ((try unfold Wire at *); omega)
  · unfold windowNet net OB5.sig
    rw [if_neg]
    unfold Shadow7.e0P Shadow7.sbP at hi
    ((try unfold Wire at *); omega)

theorem e0P_gt_1615 : ∀ j : Fin 26, j.val ≤ 24 → 1616 < Shadow7.e0P (start j) := by decide

/-- dadon's `carry{s}`: the native carry `1556 .. e0-1` is clean on the rails. -/
theorem native_carryJ (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (z : SkywalkRails.State) (s : State)
    (ready : Shadow7.onRails j 15 z s.basis) (top : s.basis (Shadow7.e0P (start j) - 1) = false)
    (top2 : s.basis (Shadow7.e0P (start j) - 2) = false) :
    ∀ q : Wire, 1556 ≤ q → q < Shadow7.e0P (start j) → s.basis q = false := by
  intro q lo hi0
  by_cases hi : (q : Nat) + 2 < Shadow7.e0P (start j)
  swap
  · by_cases e1 : (q : Nat) = Shadow7.e0P (start j) - 1
    · have e : q = Shadow7.e0P (start j) - 1 := e1
      rw [e]; exact top
    · have e : q = Shadow7.e0P (start j) - 2 := by unfold Wire at *; omega
      rw [e]; exact top2
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  apply Shadow7.native_carry _ _ _ ready
  refine List.mem_map.mpr ⟨q, ?_, ?_⟩
  · simp only [IntegerPacket.ports, Shadow7.shape, List.mem_range'_1]
    unfold Shadow7.smallBits Shadow7.sbP; unfold Shadow7.e0P Shadow7.sbP at hi; ((try unfold Wire at *); omega)
  · unfold windowNet net OB5.sig
    rw [if_neg]
    unfold Shadow7.e0P Shadow7.sbP at hi
    ((try unfold Wire at *); omega)

/-- dadon's `same_c225/240/255`: the block's placement fixes the scratch below its own moved history. -/
theorem sig_carry (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Nat) (lo : 1556 ≤ q) (hi : q + start j ≤ 2054) :
    OB5.sig (start j + 14) q = q := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  unfold OB5.sig; rw [if_neg (by (try simp only [Wire] at *); omega)]

namespace Admission

/-- dadon's `Leave{s}Admission.spare`: the two flags `e0+6, e0+7` and the pool overflow `e0+10 ..` (255: 1709,1710,
1713..1718; empty overflow for s ≤ 240). -/
def spare (j : Fin 26) : List Wire :=
  [Shadow7.e0P (start j) + 6, Shadow7.e0P (start j) + 7] ++
    List.range' (Shadow7.e0P (start j) + 10) (min (Shadow7.wpP (start j) - 1 - (Shadow7.e0P (start j) - 1598)) (2045 - start j - Shadow7.e0P (start j)))

/-- dadon's `Leave{s}Admission.Inputs`. The `extra` field (dadon's 255 form) is vacuous when the overflow is empty. -/
structure Inputs (j : Fin 26) (s : State) (z : SkywalkNat.State) (g0 s0 : Bool) : Prop extends Numeric j z where
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
  extra : ∀ q, Shadow7.e0P (start j) + 10 ≤ q → q < Shadow7.e0P (start j) + 10 + min (Shadow7.wpP (start j) - 1 - (Shadow7.e0P (start j) - 1598)) (2045 - start j - Shadow7.e0P (start j)) →
    s.basis q = false
  reloc : ∀ q, Shadow7.a0P (start j) + 17 ≤ q → q < Shadow7.a0P (start j) + 17 + min 4 (Shadow7.wpP (start j) + start j - 448) → s.basis q = false
  top : s.basis (Shadow7.e0P (start j) - 1) = false
  top2 : s.basis (Shadow7.e0P (start j) - 2) = false
  parked : s.basis (Shadow7.b0P (start j) + 16) = false

theorem mem_spare (j : Fin 26) (q : Wire) :
    q ∈ spare j ↔ q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7 ∨
      (Shadow7.e0P (start j) + 10 ≤ q ∧ q < Shadow7.e0P (start j) + 10 + min (Shadow7.wpP (start j) - 1 - (Shadow7.e0P (start j) - 1598)) (2045 - start j - Shadow7.e0P (start j))) := by
  simp only [spare, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1, or_assoc]

/-- The pool's in-place overflow (e0P+10 ..) and block 22's relocated wires (a0P+17 ..) are carries. -/
theorem carries_cover (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State)
    (clean : ∀ q ∈ carries j, s.basis q = false) :
    (∀ q, Shadow7.e0P (start j) + 10 ≤ q → q < Shadow7.e0P (start j) + 10 + min (Shadow7.wpP (start j) - 1 - (Shadow7.e0P (start j) - 1598)) (2045 - start j - Shadow7.e0P (start j)) → s.basis q = false) ∧
    (∀ q, Shadow7.a0P (start j) + 17 ≤ q → q < Shadow7.a0P (start j) + 17 + min 4 (Shadow7.wpP (start j) + start j - 448) → s.basis q = false) := by
  have pf : 1598 ≤ Shadow7.e0P (start j) ∧ 1 ≤ Shadow7.wpP (start j) ∧ (min 4 (Shadow7.wpP (start j) + start j - 448) = 0 ∨ Shadow7.e0P (start j) + start j ≤ 2045) ∧ Shadow7.wpP (start j) + start j ≤ 452 := (show ∀ k : Fin 26, 0 ≤ k.val → k.val ≤ 24 → 1598 ≤ Shadow7.e0P (start k) ∧ 1 ≤ Shadow7.wpP (start k) ∧ (min 4 (Shadow7.wpP (start k) + start k - 448) = 0 ∨ Shadow7.e0P (start k) + start k ≤ 2045) ∧ Shadow7.wpP (start k) + start k ≤ 452 from by decide) j h0 (by omega)
  obtain ⟨f1, f2, f3, f4⟩ := pf
  constructor
  · intro q lo hi
    apply clean
    simp only [carries, List.mem_map, List.mem_range]
    refine ⟨q - 1608, by omega, ?_⟩
    unfold Shadow7.poolW
    rw [if_neg (by omega), if_pos (by omega)]
    ((try unfold Wire at *); omega)
  · intro q lo hi
    rcases f3 with z | ok
    · omega
    · apply clean
      simp only [carries, List.mem_map, List.mem_range]
      refine ⟨q - Shadow7.a0P (start j) - 17 + 447 - start j, by omega, ?_⟩
      unfold Shadow7.poolW
      rw [if_neg (by omega), if_neg (by omega)]
      ((try unfold Wire at *); omega)

/-- dadon's `geometry`: every wire `Inputs` asks to be clean is a native carry wire or a spare. -/
theorem touch_clean (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State)
    (cl : ∀ q : Wire, 1556 ≤ q → q < Shadow7.e0P (start j) → s.basis q = false) (ex : ∀ q ∈ spare j, s.basis q = false)
    (rl : ∀ q, Shadow7.a0P (start j) + 17 ≤ q → q < Shadow7.a0P (start j) + 17 + min 4 (Shadow7.wpP (start j) + start j - 448) → s.basis q = false) :
    (∀ q ∈ 1556::1557::1558::fullC, s.basis q = false) ∧ (∀ p ∈ longPairs j, s.basis p.2 = false) ∧
      (∀ q ∈ carries j, s.basis q = false) ∧
      (∀ t : Nat, Shadow7.wpP (start j) ≤ t → t < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) t) = false) ∧
      (∀ q ∈ watched j, s.basis q = false) ∧
      (∀ q, Shadow7.e0P (start j) + 10 ≤ q → q < Shadow7.e0P (start j) + 10 + min (Shadow7.wpP (start j) - 1 - (Shadow7.e0P (start j) - 1598)) (2045 - start j - Shadow7.e0P (start j)) →
        s.basis q = false) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have g := env_geo w1 w3
  have he : Shadow7.e0P (start j) = 1574 + Shadow7.sbP (start j) := rfl
  have sb61 : 46 ≤ Shadow7.sbP (start j) := by unfold Shadow7.sbP; omega
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
    have pt := Shadow7.pool_top w1 w3
    unfold Shadow7.poolW
    split_ifs with h h'
    · apply cl <;> ((try unfold Wire at *); omega)
    · apply ex; rw [mem_spare]; right; right
      constructor <;> ((try unfold Wire at *); omega)
    · apply rl <;> ((try unfold Wire at *); omega)
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
theorem assemble (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (numbers : Numeric j z)
    (rails : Shadow7.onRails j 15 (SkywalkTrace.next^[15] (SkywalkRails.encode g0 s0
      (Shadow.reduced (Shadow7.sbP (start j)) 15 z).u (Shadow.reduced (Shadow7.sbP (start j)) 15 z).v)) s.basis)
    (record : IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v))
    (saved : regValue (ys j) s.basis =
        (if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) ∧
      s.basis (Shadow7.e0P (start j) + 5) = false ∧ s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      s.basis (Shadow7.e0P (start j) + 4) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j)) ≤ z.u))
    (ex : ∀ q ∈ spare j, s.basis q = false)
    (rl : ∀ q, Shadow7.a0P (start j) + 17 ≤ q → q < Shadow7.a0P (start j) + 17 + min 4 (Shadow7.wpP (start j) + start j - 448) → s.basis q = false)
    (top : s.basis (Shadow7.e0P (start j) - 1) = false) (top2 : s.basis (Shadow7.e0P (start j) - 2) = false) (parked : s.basis (Shadow7.b0P (start j) + 16) = false) :
    Inputs j s z g0 s0 := by
  have cl := native_carryJ j h0 (by omega) _ s rails top top2
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := touch_clean j h0 (by omega) s cl ex rl
  refine ⟨numbers, ?_, saved.2.1, c1, c2, c3, c4, saved.1, c5, saved.2.2.1, ?_, record, c6, rl, top, top2, parked⟩
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
def releasedSite (j : Fin 26) (q : Nat) : Prop :=
  (railP (start j + 15) < railP (start j) ∧ q = start j + 31 + railP (start j + 15)) ∨
  (785 + railP (start j + 15) < q ∧ q ≤ 785 + railP (start j)) ∨ (1301 ≤ q ∧ q ≤ 1058 + start j) ∨
  (369 ≤ start j ∧ 1302 ≤ q + start j ∧ q ≤ 933)
instance (j : Fin 26) (q : Nat) : Decidable (releasedSite j q) := by unfold releasedSite; infer_instance

/-- dadon's `Leave{s}ReleasedOrigin.released`, for every window block. -/
theorem released (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (x p : Nat) (good : Bounds x p)
    (raw history : State) (dom : Domain (start j) x p raw) (q : Nat) (site : releasedSite j q) :
    (origin (start j) raw history).basis q = false := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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

theorem entry_dest : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 → (entryOps (start j)).all (fun g =>
    (decide (Shadow7.a0P (start j) - 1 ≤ target g) && decide (target g ≤ Shadow7.a0P (start j) + 16)) ||
    (decide (Shadow7.b0P (start j) - 1 ≤ target g) && decide (target g ≤ Shadow7.b0P (start j) + 16)) ||
    (decide (start j + 16 ≤ target g) && decide (target g ≤ start j + 30)) ||
    (decide (1556 ≤ target g) && decide (target g ≤ 1575)) || decide (target g = Shadow7.e0P (start j) + 5)) = true := by
  decide +kernel

theorem entry_keep (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Nat)
    (hq : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 16) ∨ (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 16) ∨
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

/-- The entry never writes the parked wire B row 16 = b0P + 16 (margin 16: the scan and the erase stop at row 15). -/
theorem entry_dest16 : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    (entryOps (start j)).all (fun g => decide (target g ≠ Shadow7.b0P (start j) + 16)) = true := by
  decide +kernel

theorem entry_keeps_parked (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) :
    (run (GateMirror.forward (entryOps (start j))) m s).basis (Shadow7.b0P (start j) + 16) =
      s.basis (Shadow7.b0P (start j) + 16) := by
  apply LeaveReadoutFrame.preserved
  intro hm
  rw [dest_forward] at hm
  obtain ⟨g, hg, e⟩ := List.mem_map.mp hm
  have := List.all_eq_true.mp (entry_dest16 j h0 h1) g hg
  simp only [decide_eq_true_eq] at this
  exact this e

/-- The state after the input scan and the history flip (the prefix of `entry_core`). -/
theorem head_state (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    let a := step^[15] (reduced (Shadow7.sbP (start j)) 15 z)
    let e := PortalValues.negative sg a.u
    let v := run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)))) m s
    (∀ i < 17, v.basis (Shadow7.a0P (start j) - 1 + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j))).testBit i ∧
      v.basis (Shadow7.b0P (start j) - 1 + i) = ((a.u - e.toNat)/2^(Shadow7.sbP (start j))).testBit i) ∧
    (∀ q ∈ 1556::1557::1558::fullC, v.basis q = false) ∧ (∀ p ∈ longPairs j, v.basis p.2 = false) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  intro a e
  have scanActual := inputScan_result j h0 (by omega) s m a.u a.v G sg ready fresh
  dsimp only
  rw [forward_app, run_append, run_take]
  generalize hu : run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) m s = u at scanActual ⊢
  generalize m.drop (measurementCount (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j))))) = t
  generalize hv : run (GateMirror.forward (leaveFix1 (start j) (Shadow7.sbP (start j)))) t u = v
  have hist (q : Wire) (hq : q < start j + 16 ∨ start j + 30 < q) : v.basis q = u.basis q := by
    rw [← hv]; exact LeaveReadoutFrame.preserved _ _ _ _ (flip_dest _ _ q hq)
  have outputBits (i : Nat) (hi : i < 17) :
      v.basis (Shadow7.a0P (start j) - 1 + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j))).testBit i ∧
      v.basis (Shadow7.b0P (start j) - 1 + i) = ((a.u - e.toNat)/2^(Shadow7.sbP (start j))).testBit i := by
    rw [hist _ (Or.inr (by unfold Wire at *; omega)), hist _ (Or.inr (by unfold Wire at *; omega))]
    exact scanActual.2.2.1 i hi
  have scanSites : ∀ q, q ∈ RailPair.sites (scanPairs j) →
      (∃ i, i < 17 ∧ (q = Shadow7.a0P (start j) - 1 + i ∨ q = Shadow7.b0P (start j) - 1 + i)) := by
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

/-- The mask, the companion erase and the G1 release never write B row -1 (fable-leap, margin 16). -/
theorem fix2_tail_keeps_bm1 : ∀ j : Fin 26, j.val ≤ 24 →
    (Shadow7.b0P (start j) - 1 : Wire) ∉
      (maskP j ++ (Companion.eraseM (fullA15 j) (fullM15 j) fullC14 1556 1558 ++ releaseMaskP j)).map
        LeaveReadoutFrame.destination := by
  decide +kernel

/-- After the entry, B row -1 holds bit sb of the REDUCED magnitude: the scan's value, kept by the latch (it only
writes 1556), the mask, the erase and the release. -/
theorem entry_bm1 (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u
        (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    (run (GateMirror.forward (entryOps (start j))) m s).basis (Shadow7.b0P (start j) - 1) =
      (((step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u -
        (PortalValues.negative sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u).toNat) / 2^(Shadow7.sbP (start j))).testBit 0 := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have rr := Shadow7.rail_win w1 w2
  have hne : (Shadow7.b0P (start j) - 1 : Wire) ≠ 1556 := by unfold Wire at *; omega
  have hd := head_state j h0 h1 s m z G sg ready fresh scratch temp
  dsimp only at hd
  rw [entryOps, forward_app, run_append, run_take, fix2_parts15 j h0 h1, run_append,
    LeaveReadoutFrame.preserved _ _ _ _ (fix2_tail_keeps_bm1 j h1)]
  generalize run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)))) m s = v0 at hd ⊢
  obtain ⟨bits, clean, temps⟩ := hd
  have b0 := (bits 0 (by decide)).2
  rw [Nat.add_zero] at b0
  rw [latchG2_run j h0 h1 v0 _ (fun p hp => temps p (longPairs15_sub j hp)) (clean _ (by decide))]
  simp only [writeBit, Function.update_of_ne hne]
  exact b0

/-- The mask release after the G4 borrow (fable-leap, margin 16). -/
theorem release_ok (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (v : State) (mm : List Bool)
    (h7 : v.basis 1557 = !v.basis (Shadow7.a0P (start j) - 1))
    (h8 : v.basis 1558 = (v.basis (Shadow7.b0P (start j) - 1) && v.basis 1557)) :
    run (releaseMaskP j) mm v = ⟨v.phase, writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have ha0 : Shadow7.a0P (start j) = start j + Shadow7.sbP (start j) + 32 := rfl
  have hb0 : Shadow7.b0P (start j) = 787 + Shadow7.sbP (start j) := rfl
  exact release_generic _ _ (by unfold Wire at *; omega) (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    (by unfold Wire at *; omega) v mm h7 h8

/-- dadon's `Leave{s}FullArithmetic.program`. -/
def fullProgram (j : Fin 26) : Program :=
  GateMirror.forward (entryOps (start j) ++ bodyOps j) ++ (borrowG4 j ++ Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558)

/-- Margin-16 glue (fable-leap): `entry_core`'s `hK` for `K := far ∧ farKey = 0` (`LeaveShadowRails.key0EraseBound`). -/
theorem glueBound (j : Fin 26) (z : SkywalkNat.State) (sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) :
    (far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0) →
      ¬ 2^(Shadow7.sbP (start j)) ≤ (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u -
        (PortalValues.negative sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u).toNat →
      (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u + (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).v <
        2*2^(Shadow7.sbP (start j)) := by
  intro K low
  exact LeaveShadowRails.key0EraseBound _ z (small.1 K.1) K.1 K.2 _
    (by cases PortalValues.negative sg (step^[15] (reduced (Shadow7.sbP (start j)) 15 z)).u <;> decide) low

/-- The common core of the full arithmetic: the Shadow7.routed Shadow7.body after the entry (dadon's `Leave{s}Routed.result` applied
to `run entry`), as used by FullArithmetic, FlagScratch, CoreCheckpoint, HighZero. -/
theorem full_routed (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool)
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
      s.basis (swaps j i) = decide (i = key (actualMode (Shadow7.sbP (start j)) z)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let a := run (GateMirror.forward (entryOps (start j))) m s
    let n := m.drop (measurementCount (GateMirror.forward (entryOps (start j))))
    let out := run (GateMirror.forward (bodyOps j)) n a
    let t := run (GateMirror.forward (fullPrefix j)) n a
    out.phase = a.phase ∧ (∀ i < Shadow7.wpP (start j) + 15, out.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      (∀ i : Fin 17, out.basis (row j i).free = false) ∧ (∀ i : Fin 39, out.basis (1559 + i.val) = false) ∧
      (∀ q, q ≠ Shadow7.b0P (start j) - 1 → HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q →
        (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) → out.basis q = cleared t.basis q) ∧
      out.basis (Shadow7.b0P (start j) - 1) = (t.basis (Shadow7.b0P (start j) - 1) ^^ (decide (far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0) &&
        ((HighBankAdjust.adjusted (high (Shadow7.sbP (start j)) 15 z) (Shadow7.wpP (start j)) (HighBankSum.cross17 (TrueMiddle.d j z)) (TrueMiddle.neg j z)).testBit 0 ^^
          !HighBankSum.cross17 (TrueMiddle.d j z)))) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have front := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
    (LeaveJ7.glueBound j z sg small) flag
  have watchedOK := frontReady_frame j h0 (by omega) s m z G sg small ready fresh scratch temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
    (LeaveJ7.glueBound j z sg small) flag
  intro a n
  have kept (q : Nat) (ok : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 16) ∨
      (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 16) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨
      (1556 ≤ q ∧ q ≤ 1575) ∨ q = Shadow7.e0P (start j) + 5)) : a.basis q = s.basis q := entry_keep j h0 (by omega) q ok s m
  exact routed_result j h0 (by omega) z a n small odd room
    (fun q hq => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
      have p := Shadow7.pool_cases (i := i) w1 w2
      exact (kept _ (by unfold Wire at *; omega)).trans (clean _ hq))
    ((kept 1613 (by omega)).trans (native_carryJ_lt j h0 h1 _ s ready 1613 (by decide) (Nat.lt_trans (by decide) (e0P_gt_1615 j h1))))
    ((kept 1614 (by omega)).trans (native_carryJ_lt j h0 h1 _ s ready 1614 (by decide) (e0P_gt_1615 j h1)))
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

/-- B row -1 after the routed body holds bit sb of the TRUE magnitude: the scan's reduced bit plus G3's flip
(`g3_math`; fable-leap, margin 16). -/
theorem full_bm1 (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool)
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
      s.basis (swaps j i) = decide (i = key (actualMode (Shadow7.sbP (start j)) z)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    (run (GateMirror.forward (bodyOps j)) (m.drop (measurementCount (GateMirror.forward (entryOps (start j)))))
      (run (GateMirror.forward (entryOps (start j))) m s)).basis (Shadow7.b0P (start j) - 1) =
      (((step^[15] z).u - (PortalValues.negative sg (step^[15] z).u).toNat) / 2^(Shadow7.sbP (start j))).testBit 0 := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have hb0 : Shadow7.b0P (start j) = 787 + Shadow7.sbP (start j) := rfl
  have e6 := e0P_gt_1615 j h1
  have used := full_routed j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events flag
  have eb := entry_bm1 j h0 h1 s m z G sg ready fresh scratch temp
  have ch := LeaveRestoreTruth.truth_shadow7 (Shadow7.sbP (start j)) z small.1 sg
  have hw : 1 ≤ Shadow7.wpP (start j) := by omega
  dsimp only at used ch
  rw [used.2.2.2.2.2, prefix_keep j h0 (by omega) (Shadow7.b0P (start j) - 1) (by omega), eb,
    g3_math (Shadow7.sbP (start j)) (Shadow7.wpP (start j)) z sg small.1 hw (HighBankSum.cross17 (TrueMiddle.d j z)) (TrueMiddle.neg j z), ch.1]

/-- dadon's `Leave{s}FullArithmetic.result` at margin 16 (fable-leap): entry, routed body, G4 borrow, companion
restore on L-1 rows; plus B row -1 = bit sb of the true magnitude and the clean mask release. -/
theorem fullArithmetic_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool)
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
      s.basis (swaps j i) = decide (i = key (actualMode (Shadow7.sbP (start j)) z)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let out := run (fullProgram j) m s
    out.phase = s.phase ∧ regValue (smallM j) out.basis = (mag/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j) - 1) ∧
      out.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ mag) ∧
      (∀ i < Shadow7.wpP (start j) + 15, out.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      out.basis (Shadow7.b0P (start j) - 1) = decide (2^(Shadow7.sbP (start j)) ≤ mag % (2*2^(Shadow7.sbP (start j)))) ∧
      ∀ mm, run (releaseMaskP j) mm out = ⟨out.phase, writeBit (writeBit out.basis 1557 false) 1558 false⟩ := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have hb0 : Shadow7.b0P (start j) = 787 + Shadow7.sbP (start j) := rfl
  have front := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
    (LeaveJ7.glueBound j z sg small) flag
  have used := full_routed j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events flag
  have bm1 := full_bm1 j h0 h1 s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events flag
  dsimp only at front used
  generalize ha : run (GateMirror.forward (entryOps (start j))) m s = a at front used bm1
  generalize hn : m.drop (measurementCount (GateMirror.forward (entryOps (start j)))) = n at used bm1
  have restored := routedRestore_result j h0 (by omega) z sg a n (n.drop (measurementCount (GateMirror.forward (bodyOps j))))
    small front.2.1 ⟨front.2.2.2.1, front.2.2.2.2.1⟩ used.2.1 bm1 used.2.2.2.1
  dsimp only at restored ⊢
  rw [fullProgram, forward_app, List.append_assoc, run_append, run_take, run_append, run_take, ha, hn]
  have notM : (Shadow7.b0P (start j) - 1 : Wire) ∉ smallM j := by
    intro h; obtain ⟨i, hi, e⟩ := List.mem_map.mp h; rw [List.mem_range] at hi; unfold Wire at *; omega
  refine ⟨restored.1.trans (used.1.trans front.1), restored.2.2.1, restored.2.2.2.1, restored.2.2.2.2.1, ?_,
    fun mm => release_ok j h0 h1 _ mm restored.2.2.2.2.2.1 restored.2.2.2.2.2.2⟩
  rw [restored.2.1 _ (by unfold Wire at *; omega) (by unfold Wire at *; omega) notM, bm1,
    LeaveCompanion.thresholdBit _ _ (Nat.two_pow_pos _)]

/-! FlagScratch (dadon's `Leave{s}FlagScratch`). -/

/-- dadon's `LeaveCompanion{s}.pendingPairs` (the StoreMapped chain: top, then the bank above the low columns). -/
def pendingPairs (j : Fin 26) : List (Wire × Wire) :=
  (List.range (Shadow7.liveW (start j) - Shadow7.lowsP (start j) + 1)).map (fun i =>
    (if i = 0 then Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 else Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i - 1), Shadow7.storeW (start j) (i+1)))
/-- dadon's `LeaveCompanion{s}.clearFlagPairs`. -/
def clearFlagPairs (j : Fin 26) : List (Wire × Wire) :=
  (List.range (Shadow7.lowsP (start j))).map (fun i => (Shadow7.b0P (start j) - 1 + i, 1559 + i))
/-- dadon's `Leave{s}FlagScratch.targets`. -/
def flagTargets (j : Fin 26) : List Wire := (pendingPairs j ++ clearFlagPairs j).map Prod.snd

theorem flagScratch_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool)
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
      s.basis (swaps j i) = decide (i = key (actualMode (Shadow7.sbP (start j)) z)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    ∀ q ∈ flagTargets j, (run (fullProgram j) m s).basis q = false := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have lw := Shadow7.liveW_bounds w1 w2
  have front := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
    (LeaveJ7.glueBound j z sg small) flag
  have used := full_routed j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events flag
  have bm1 := full_bm1 j h0 h1 s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events flag
  generalize ha : run (GateMirror.forward (entryOps (start j))) m s = a at front used bm1
  have restored := routedRestore_result j h0 (by omega) z sg a (m.drop (measurementCount (GateMirror.forward (entryOps (start j)))))
    ((m.drop (measurementCount (GateMirror.forward (entryOps (start j))))).drop
      (measurementCount (GateMirror.forward (bodyOps j)))) small front.2.1 ⟨front.2.2.2.1, front.2.2.2.2.1⟩ used.2.1 bm1 used.2.2.2.1
  intro q hq
  -- geometry: every flag target is a selector wire 1559..1597 or a pool wire above 1612 (below or above the anchor)
  have geo : (1559 ≤ q ∧ q ≤ 1597) ∨ (∃ k, k < Shadow7.wpP (start j) - 1 ∧ q = Shadow7.poolW (start j) k ∧ 1613 ≤ q ∧ (q < Shadow7.e0P (start j) ∨ Shadow7.e0P (start j) + 10 ≤ q)) := by
    simp only [flagTargets, List.map_append, List.mem_append, List.mem_map] at hq
    rcases hq with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
      have sc := Shadow7.storeW_cases (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2 (i+1)
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
  have n78 : q ≠ 1557 ∧ q ≠ 1558 := by
    rcases geo with g|⟨k, _, _, g1, g2⟩ <;> unfold Wire at * <;> omega
  rw [fullProgram, forward_app, List.append_assoc, run_append, run_take, run_append, run_take, ha, restored.2.1 _ n78.1 n78.2 notM]
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
    have hb0 : Shadow7.b0P (start j) = 787 + Shadow7.sbP (start j) := rfl
    rw [used.2.2.2.2.1 q (by unfold Wire at *; omega) notWire notCols, cleared, if_neg (by unfold Wire at *; omega)]
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
theorem pending_fst (j : Fin 26) : (pendingPairs j).map Prod.fst =
    (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2) ::
      (List.range (Shadow7.liveW (start j) - Shadow7.lowsP (start j))).map (fun i => Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i)) := by
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

theorem clearFlag_fst (j : Fin 26) :
    (clearFlagPairs j).map Prod.fst = (List.range (Shadow7.lowsP (start j))).map (Shadow7.b0P (start j) - 1 + ·) := by
  simp only [clearFlagPairs, List.map_map]; rfl

theorem storeW_zero7 (s : Nat) : Shadow7.storeW s 0 = 1558 := by
  simp only [Shadow7.storeW, Partial.storeW, Shadow7.e0P]
  split_ifs <;> ((try unfold Wire at *); omega)

theorem storeMapped_parts (j : Fin 26) :
    GateMirror.forward (Shadow7.leaveStoreMapped (start j)) =
      latch true none 1557 1558 (pendingPairs j) ++
        ([.CCX 1556 1557 1558] ++ latch true none 1556 1558 (clearFlagPairs j)) := by
  have ch1 : GateMirror.forward (chainG (Shadow7.storeW (start j))
      (fun i => if i = 0 then Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 else Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i - 1))
      [.cx (Shadow7.storeW (start j) (Shadow7.liveW (start j) - Shadow7.lowsP (start j) + 1)) 1557, .x 1557] 0 (Shadow7.liveW (start j) - Shadow7.lowsP (start j) + 1)) =
      PortalAnd.chain true none 1557 1558 (pendingPairs j) := by
    rw [forward_chainG0, storeW_zero7]; rfl
  have ch2 : GateMirror.forward (chainG (fun i => (1558 + i : Wire)) (fun i => Shadow7.b0P (start j) - 1 + i)
      [.cx (1558 + Shadow7.lowsP (start j)) 1556, .x 1556] 0 (Shadow7.lowsP (start j))) =
      PortalAnd.chain true none 1556 1558 (clearFlagPairs j) := by
    have h := forward_chainG0 (fun i => (1558 + i : Wire)) (fun i => Shadow7.b0P (start j) - 1 + i) 1556 (Shadow7.lowsP (start j))
    have e : (List.range (Shadow7.lowsP (start j))).map (fun k => (Shadow7.b0P (start j) - 1 + k, (1558 + (k+1) : Wire))) =
        clearFlagPairs j := by
      simp only [clearFlagPairs]; apply List.map_congr_left; intro k _; simp only [Prod.mk.injEq, true_and]
      unfold Wire; omega
    rw [← e]; exact h
  simp only [Shadow7.leaveStoreMapped, forward_app, forward_xsG, ch1, ch2, PortalAnd.latch, PortalAnd.digits,
    pending_fst, clearFlag_fst, forward_cons', forward_nil', front, erase, notRegister, List.map_cons, List.map_nil,
    List.map_append, List.reverse_cons, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
    if_true, ↓reduceIte]


/-! The scanned output register (dadon's `OutputPorts.scanned`, `outputRegisters` high part). -/

def scanned (j : Fin 26) : List Wire :=
  (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 2) :: (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 1) :: (pendingPairs j).map Prod.fst

theorem scanned_eq (j : Fin 26) : scanned j =
    (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 2) :: (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 1) :: (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2) ::
      (List.range (Shadow7.liveW (start j) - Shadow7.lowsP (start j))).map (fun i => Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i)) := by
  rw [scanned, pending_fst]

/-- Margin 17: the scanned register of the pending latch starts one row higher (row `lowsP-2` = bit `sb'+16`). -/
def scanned2 (j : Fin 26) : List Wire :=
  (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 1) :: (pendingPairs j).map Prod.fst

theorem scanned2_eq (j : Fin 26) : scanned2 j =
    (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 1) :: (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2) ::
      (List.range (Shadow7.liveW (start j) - Shadow7.lowsP (start j))).map (fun i => Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i)) := by
  rw [scanned2, pending_fst]

theorem outputScanned2 (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (Z : Nat)
    (bits : ∀ i < Shadow7.wpP (start j) + 15, s.basis (live j i) = Z.testBit i) :
    regValue (scanned2 j) s.basis = (Z / 2^(Shadow7.lowsP (start j) - 2)) % 2^(Shadow7.liveW (start j) - Shadow7.lowsP (start j) + 2) := by
  have rr := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
  have lw := Shadow7.liveW_bounds (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
  have len : (scanned2 j).length = Shadow7.liveW (start j) - Shadow7.lowsP (start j) + 2 := by
    rw [scanned2_eq]; simp
  rw [← len]
  apply EnterProof.value_of_bits (scanned2 j)
  intro i hi
  rw [len] at hi
  have g : (scanned2 j).getD i 0 = live j (Shadow7.lowsP (start j) - 2 + i) := by
    rw [scanned2_eq]
    rcases i with _ | _ | i
    · simp [live]; rw [if_pos (by omega)]; (try unfold Wire at *); omega
    · simp [live]; rw [if_pos (by omega)]; (try unfold Wire at *); omega
    · simp [live, List.getD_eq_getElem?_getD, show i < Shadow7.liveW (start j) - Shadow7.lowsP (start j) by omega]
      rw [if_neg (by omega)]; congr 1; omega
  rw [g, Nat.testBit_div_two_pow, Nat.add_comm i]
  exact bits _ (by omega)

/-! The pending threshold (dadon's `LeaveCompanion{s}.pending_three`). -/

theorem pending_layout (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ((Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 2) :: (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 1) :: (1557:Wire) :: (1558:Wire) ::
      PortalAnd.sites (pendingPairs j)).Nodup := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have lw := Shadow7.liveW_bounds w1 w2
  have fst_range : ∀ q ∈ (pendingPairs j).map Prod.fst,
      q = Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 ∨ ∃ i, Shadow7.lowsP (start j) ≤ i ∧ i < Shadow7.wpP (start j) + 15 ∧ q = Shadow7.bankW (start j) i := by
    intro q hq; rw [pending_fst] at hq
    rcases List.mem_cons.mp hq with h|h
    · exact Or.inl h
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h; rw [List.mem_range] at hi
      exact Or.inr ⟨Shadow7.lowsP (start j) + i, by omega, by omega, rfl⟩
  have snd_range : ∀ q ∈ (pendingPairs j).map Prod.snd, ∃ k, 1 ≤ k ∧ k ≤ Shadow7.liveW (start j) - Shadow7.lowsP (start j) + 1 ∧ q = Shadow7.storeW (start j) k := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
    exact ⟨i+1, by omega, by omega, rfl⟩
  have bankOut : ∀ i, Shadow7.lowsP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → ∀ k, (Shadow7.storeW (start j) k : Nat) ≠ Shadow7.bankW (start j) i ∧
      (Shadow7.bankW (start j) i : Nat) ≠ 1557 ∧ (Shadow7.bankW (start j) i : Nat) ≠ 1558 ∧ (Shadow7.bankW (start j) i : Nat) > Shadow7.a0P (start j) + 20 := by
    intro i a b k
    have bc := Shadow7.bank_cases w1 w2 b; have sc := Shadow7.storeW_cases (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2 k
    unfold Wire at *; omega
  have perm := (((sites_perm (pendingPairs j)).cons (1558:Wire)).cons (1557:Wire)).cons
    (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 1) |>.cons (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 2)
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
    have a := Shadow7.storeW_cases (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2 (x+1); have b := Shadow7.storeW_cases (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2 (y+1)
    simp only [Function.comp] at e; unfold Wire at *; omega
  have disj : ∀ a ∈ (pendingPairs j).map Prod.fst, ∀ b ∈ (pendingPairs j).map Prod.snd, a ≠ b := by
    intro a ha b hb e
    obtain ⟨k, k1, k2, rfl⟩ := snd_range b hb
    have sc := Shadow7.storeW_cases (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2 k
    rcases fst_range a ha with rfl|⟨i, i1, i2, rfl⟩
    · unfold Wire at *; omega
    · exact (bankOut i i1 i2 k).1 e.symm
  have notIn : ∀ x : Nat, (x < 1556 ∧ x ≤ Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 1) ∨ x = 1557 ∨ x = 1558 →
      x ∉ (pendingPairs j).map Prod.fst ++ (pendingPairs j).map Prod.snd := by
    intro x hx hm
    rcases List.mem_append.mp hm with h|h
    · rcases fst_range x h with rfl|⟨i, i1, i2, e⟩
      · unfold Wire at *; omega
      · have := bankOut i i1 i2 0; rw [e] at hx; unfold Wire at *; omega
    · obtain ⟨k, k1, k2, e⟩ := snd_range x h
      have sc := Shadow7.storeW_cases (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2 k; rw [e] at hx; unfold Wire at *; omega
  simp only [List.nodup_cons, List.mem_cons, not_or]
  refine ⟨⟨by omega, by omega, by omega, ?_⟩, ⟨by omega, by omega, ?_⟩, ⟨by decide, ?_⟩, ?_, List.nodup_append.mpr ⟨fnd, snd, disj⟩⟩
  · exact notIn (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 2) (Or.inl ⟨by omega, by omega⟩)
  · exact notIn (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 1) (Or.inl ⟨by omega, le_refl _⟩)
  · exact notIn 1557 (Or.inr (Or.inl rfl))
  · exact notIn 1558 (Or.inr (Or.inr rfl))

/-- Threshold-2 form of `pending_three` (margin 17). Without the `make/pop` of the two rows below `top` the pending
latch reads `[2 ≤ value]` of the scanned register taken from row `lowsP-2` (bit `sb'+16` of the next block), which
is `Shadow.far` of the next block. `1558` is the (clean) chain head. -/
theorem pending_two (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool)
    (fresh : s.basis 1558 = false) (clean : ∀ p ∈ pendingPairs j, s.basis p.2 = false) :
    run (PortalAnd.latch true none 1557 1558 (pendingPairs j)) m s =
      ⟨s.phase, writeBit s.basis 1557 (s.basis 1557 ^^ decide (2 ≤ regValue
        ((Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 1) :: (pendingPairs j).map Prod.fst) s.basis))⟩ := by
  have lay : ((1557:Wire) :: (1558:Wire) :: PortalAnd.sites (pendingPairs j)).Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp (pending_layout j h0 (by omega))).2).2
  have h := PortalAnd.run_latch true none 1557 1558 (pendingPairs j) lay (by simp) s m clean
  have hh : (PortalAnd.digits 1558 (pendingPairs j)).any s.basis = decide (2 ≤ regValue
      ((Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 1) :: (pendingPairs j).map Prod.fst) s.basis) := by
    refine Eq.trans ?_ (PortalValues.aboveFirst _ _ _)
    change (s.basis 1558 || ((pendingPairs j).map Prod.fst).any s.basis) = _
    rw [fresh, Bool.false_or]
  rw [h, hh] <;> first | rfl | simp [PortalAnd.active]

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
theorem nextFlag_value (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (z : SkywalkNat.State) :
    TrueMiddle.F j z / 2^(Shadow7.lowsP (start j) - 2) = Shadow.high (Shadow7.sbP (start j + 15)) 15 (step^[15] z) := by
  have rr := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
  unfold TrueMiddle.F Shadow.high limb HighBankSum.total
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 2
  omega

theorem near_bound17 (u v sign divisor bound : Nat) (dp : 0<divisor) (wide : 2*divisor≤bound)
    (near : ¬ 2≤(u+v)/divisor) : u-sign<bound := by
  have lo : (u+v)/divisor<2 := Nat.lt_of_not_ge near
  have lim := (Nat.div_lt_iff_lt_mul dp).mp lo
  omega

/-- dadon's `Leave{s}NextFlagTruth.boundNear`. -/
theorem nextFlag_boundNear (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (a : SkywalkNat.State) (sign : Nat)
    (near : ¬ far (Shadow7.sbP (start j + 15)) 15 a) :
    a.u - sign < (2 * 2^(Shadow7.sbP (start j))) * 2^(smallM j).length := by
  have rr := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
  apply near_bound17 a.u a.v sign (limb (Shadow7.sbP (start j + 15)) 15) _ (by unfold limb; positivity)
  · rw [smallM_length]; unfold limb
    have e : 2 * 2^(Shadow7.sbP (start j)) * 2^(Shadow7.lowsP (start j) - 1) = 2^(Shadow7.sbP (start j + 15) + 15) * 2^2 := by
      rw [← Nat.pow_succ', ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [e]; omega
  · exact near

/-- dadon's `Leave{s}NextFlagTruth.orientation`. -/
theorem nextFlag_orientation (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (a : SkywalkNat.State) (sign : Nat)
    (bit : sign ≤ 1) (small : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 a) (farA : far (Shadow7.sbP (start j + 15)) 15 a) :
    (2^(Shadow7.sbP (start j)) ≤ a.u - sign) ↔ (2^(Shadow7.sbP (start j + 15)) ≤ a.u) := by
  have small := small farA
  have rr := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
  have lower := (Nat.le_div_iff_mul_le (by unfold limb; positivity : 0 < limb (Shadow7.sbP (start j + 15)) 15)).mp farA
  unfold limb at lower
  -- powers in terms of P = 2^sb'
  obtain ⟨d, hd, hdd⟩ : ∃ d, Shadow7.sbP (start j) = Shadow7.sbP (start j + 15) + d ∧ (d = 7 ∨ d = 8) :=
    ⟨Shadow7.sbP (start j) - Shadow7.sbP (start j + 15), by omega, by omega⟩
  have p2 : 2^(Shadow7.sbP (start j + 15) + 15) = 32768 * 2^(Shadow7.sbP (start j + 15)) := by
    rw [Nat.pow_add, Nat.mul_comm]
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

theorem clearFlag_layout (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (1556 :: (1558:Wire) :: PortalAnd.sites (clearFlagPairs j)).Nodup := by
  have rr := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
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

theorem clearFlag_digits (j : Fin 26) : PortalAnd.digits 1558 (clearFlagPairs j) = 1558 :: (Shadow7.b0P (start j) - 1) :: smallM j := by
  have hL : ∀ j : Fin 26, 1 ≤ Shadow7.lowsP (start j) := by decide
  simp only [PortalAnd.digits, clearFlagPairs, smallM, List.map_map, Function.comp]
  obtain ⟨n, hn⟩ : ∃ n, Shadow7.lowsP (start j) = n + 1 := ⟨Shadow7.lowsP (start j) - 1, by have := hL j; omega⟩
  rw [hn, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Function.comp, Nat.add_zero, Nat.add_sub_cancel]
  congr 2
  apply List.map_congr_left; intro i _
  show Shadow7.b0P (start j) - 1 + (i + 1) = Shadow7.b0P (start j) + i
  unfold Shadow7.b0P; omega

/-- dadon's `LeaveCompanion{s}.clearFlag_value`. -/
theorem clearFlag_value (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (half mag : Nat)
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

theorem tailFlags_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (a : SkywalkNat.State) (s : State)
    (m : List Bool) (sign : Nat) (bit : sign ≤ 1) (small : Shadow7.SmallIfFar (Shadow7.sbP (start j + 15)) 15 a)
    (x : s.basis 1557 = false) (y : s.basis 1558 = false)
    (scan : regValue (scanned2 j) s.basis = Shadow.high (Shadow7.sbP (start j + 15)) 15 a)
    (cleanP : ∀ p ∈ pendingPairs j, s.basis p.2 = false)
    (cleanC : ∀ p ∈ clearFlagPairs j, s.basis p.2 = false)
    (long : s.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ a.u - sign))
    (low : s.basis (Shadow7.b0P (start j) - 1) = decide (2^(Shadow7.sbP (start j)) ≤ (a.u - sign) % (2 * 2^(Shadow7.sbP (start j)))))
    (upper : regValue (smallM j) s.basis = ((a.u - sign) / (2 * 2^(Shadow7.sbP (start j)))) % 2^(smallM j).length) :
    let f := decide (far (Shadow7.sbP (start j + 15)) 15 a)
    let u := f && decide (2^(Shadow7.sbP (start j + 15)) ≤ a.u)
    run (GateMirror.forward (Shadow7.leaveStoreMapped (start j))) m s =
      ⟨s.phase, writeBit (writeBit (writeBit s.basis 1557 f) 1558 u) 1556 false⟩ := by
  have rr := Shadow7.rail_win (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2
  intro f u
  generalize hb1 : writeBit s.basis 1557 f = b₁
  generalize hb2 : writeBit b₁ 1558 u = b₂
  have stage : run (latch true none 1557 1558 (pendingPairs j)) m s = ⟨s.phase, b₁⟩ := by
    have scan' : regValue ((Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2 - 1) :: (pendingPairs j).map Prod.fst) s.basis =
        Shadow.high (Shadow7.sbP (start j + 15)) 15 a := scan
    rw [pending_two j h0 (by omega) s m y cleanP, x, Bool.false_xor, scan', ← hb1]
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

theorem erase_gates (j : Fin 26) : Companion.eraseM (fullA15 j) (fullM15 j) fullC14 1556 1558 =
    GateMirror.forward (addG (fullM15 j) fullC14 1558 ++
      (List.range 14).map (fun i => Gate.pop 1556 (Shadow7.a0P (start j) + i) (Shadow7.b0P (start j) + i))) := by
  have hc : GateMirror.forward ((List.range 14).map (fun i => Gate.pop 1556 (Shadow7.a0P (start j) + i) (Shadow7.b0P (start j) + i))) =
      Companion.popRegister 1556 (fullA15 j) (fullM15 j) := by
    rw [fullA15, fullM15]; exact forward_popsG 1556 _ _ _
  rw [forward_app, forward_addG, hc]; rfl

/-- The companion restore of the low columns as gates (`Shadow7.lowRest` without the mask release). -/
def restoreG (s : Nat) : List Gate :=
  (List.range (Shadow7.lowsP s - 1)).map (fun i => .make 1556 (Shadow7.a0P s + i) (Shadow7.b0P s + i)) ++ xsG ((List.range (Shadow7.lowsP s - 1)).map (Shadow7.b0P s + ·)) ++
  addG ((List.range (Shadow7.lowsP s - 1)).map (Shadow7.b0P s + ·)) ((List.range (Shadow7.lowsP s - 1 - 1)).map (1559 + ·)) 1558 ++
  xsG ((List.range (Shadow7.lowsP s - 1)).map (Shadow7.b0P s + ·))

theorem restore_gates (j : Fin 26) :
    Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558 = GateMirror.forward (restoreG (start j)) := by
  have h := lowRest_parts j
  have e : Shadow7.lowRest (start j) = [.cx (Shadow7.a0P (start j) - 1) 1557, .x 1557, .make (Shadow7.b0P (start j) - 1) 1557 1558] ++
      (restoreG (start j) ++ [.pop (Shadow7.b0P (start j) - 1) 1557 1558, .cx (Shadow7.a0P (start j) - 1) 1557, .x 1557]) := by
    simp only [Shadow7.lowRest, restoreG, List.append_assoc]
  have hg : GateMirror.forward [.cx (Shadow7.a0P (start j) - 1) 1557, .x 1557, .make (Shadow7.b0P (start j) - 1) 1557 1558] =
      borrowG4 j := rfl
  rw [e, forward_app, forward_app, hg] at h
  exact (List.append_cancel_right (List.append_cancel_left h)).symm

/-- The companion region: the magnitude limbs and the carries. -/
def compT (j : Fin 26) (t : Nat) : Prop := (Shadow7.b0P (start j) ≤ t ∧ t ≤ Shadow7.b0P (start j) + 15) ∨ (1559 ≤ t ∧ t ≤ 1575)

theorem erase_dest (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ∀ q ∈ (Companion.eraseM (fullA15 j) (fullM15 j) fullC14 1556 1558).map LeaveReadoutFrame.destination, compT j q := by
  have ea : AllAT (fun _ => True) (compT j) (addG (fullM15 j) fullC14 1558 ++
      (List.range 14).map (fun i => Gate.pop 1556 (Shadow7.a0P (start j) + i) (Shadow7.b0P (start j) + i))) := by
    refine allAT_append (allAT_addG _ _ _ (fun y hy => ⟨trivial, ?_⟩) (fun c hc => ⟨trivial, ?_⟩) trivial)
      (allAT_map _ _ (fun i hi => ok_pop trivial trivial ?_))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; left; unfold Wire at *; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi; right; unfold Wire at *; omega
    · rw [List.mem_range] at hi; left; unfold Wire at *; omega
  intro q h
  rw [erase_gates, dest_forward] at h
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h
  exact (ea g hg).2

theorem restore_dest (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ∀ q ∈ (Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558).map LeaveReadoutFrame.destination, compT j q := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have hL : Shadow7.lowsP (start j) ≤ 11 := by omega
  have ra : AllAT (fun _ => True) (compT j) (restoreG (start j)) := by
    have hb : ∀ y ∈ (List.range (Shadow7.lowsP (start j) - 1)).map (Shadow7.b0P (start j) + ·), True ∧ compT j y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
      exact ⟨trivial, Or.inl (by (try unfold Wire at *); omega)⟩
    unfold restoreG
    refine allAT_append (allAT_append (allAT_append (allAT_map _ _ (fun i hi => ok_make trivial trivial ?_))
      (allAT_xsG _ (fun x hx => (hb x hx).2))) (allAT_addG _ _ _ hb (fun c hc => ⟨trivial, ?_⟩) trivial))
      (allAT_xsG _ (fun x hx => (hb x hx).2))
    · rw [List.mem_range] at hi; left; unfold Wire at *; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi; right; unfold Wire at *; omega
  intro q h
  rw [restore_gates, dest_forward] at h
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h
  exact (ra g hg).2

/-- The mask wires are distinct and away from the companion flag. -/
theorem mask_wires (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (Shadow7.a0P (start j) - 1 : Wire) ≠ 1557 ∧ (Shadow7.a0P (start j) - 1 : Wire) ≠ 1558 ∧ (Shadow7.b0P (start j) - 1 : Wire) ≠ 1557 ∧
      (Shadow7.b0P (start j) - 1 : Wire) ≠ 1558 ∧ (Shadow7.a0P (start j) - 1 : Wire) ≠ 1556 ∧ (Shadow7.b0P (start j) - 1 : Wire) ≠ 1556 ∧
      [Shadow7.a0P (start j) - 1, Shadow7.b0P (start j) - 1, (1557:Wire), 1558].Nodup := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or,
    not_false_eq_true]
  unfold Wire at *; omega

/-! MaskCut. -/

/-- dadon's `Leave{s}MaskCut.result` at margin 16 (fable-leap): B row -1 after the full arithmetic is bit sb of the TRUE
magnitude (G3 fixed it in far key-0 blocks) and the mask releases clean (G4's pair). -/
theorem maskCut_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool)
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
      s.basis (swaps j i) = decide (i = key (actualMode (Shadow7.sbP (start j)) z)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let v := run (fullProgram j) m s
    v.basis (Shadow7.b0P (start j) - 1) = decide (2^(Shadow7.sbP (start j)) ≤ mag % (2*2^(Shadow7.sbP (start j)))) ∧
    ∀ mm, run (releaseMaskP j) mm v = ⟨v.phase, writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  have ar := fullArithmetic_result j h0 h1 s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events flag
  exact ⟨ar.2.2.2.2.1, ar.2.2.2.2.2⟩

/-! BeforeStore. -/

theorem live_away (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (i : Nat) (hi : i < Shadow7.wpP (start j) + 15) :
    (live j i : Wire) ≠ 1556 ∧ (live j i : Wire) ≠ 1557 ∧ (live j i : Wire) ≠ 1558 := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have b := Shadow7.bank_cases w1 w2 hi
  unfold live; split <;> unfold Wire at * <;> omega

theorem smallM_away (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ∀ q ∈ smallM j, q ≠ 1556 ∧ q ≠ 1557 ∧ q ≠ 1558 := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
  unfold Wire at *; omega

theorem flagTargets_away (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ∀ q ∈ flagTargets j, q ≠ 1557 ∧ q ≠ 1558 := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  intro q hq
  simp only [flagTargets, List.map_append, List.mem_append, List.mem_map] at hq
  rcases hq with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have sc := Shadow7.storeW_cases (start_win7 j h0 (by omega)).1 (start_win7 j h0 (by omega)).2 (i+1)
    dsimp only; unfold Wire at *; omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
    dsimp only; unfold Wire at *; omega

/-- dadon's `Leave{s}BeforeStore.program` (cut 2788 at 225). -/
def beforeStoreProgram (j : Fin 26) : Program :=
  fullProgram j ++ (releaseMaskP j ++ GateMirror.forward (Shadow7.leaveStoreMapped (start j)))

/-- dadon's `Leave{s}BeforeStore.result`. -/
theorem beforeStore_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool)
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
    (bound : TrueMiddle.F j z < 2^(Shadow7.liveW (start j)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let f := decide (Shadow.far (Shadow7.sbP (start j + 15)) 15 a)
    let v := run (fullProgram j) m s
    let out := run (beforeStoreProgram j) m s
    out.phase = s.phase ∧ out.basis 1556 = false ∧ out.basis 1557 = f ∧
      out.basis 1558 = (f && decide (2^(Shadow7.sbP (start j + 15)) ≤ a.u)) ∧
      regValue (smallM j) out.basis = (mag/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j) - 1) ∧
      (∀ i < Shadow7.wpP (start j) + 15, out.basis (live j i) = (TrueMiddle.F j z).testBit i) ∧
      ∀ q, q ≠ 1556 → q ≠ 1557 → q ≠ 1558 → out.basis q = v.basis q := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  obtain ⟨n1, n2, n3, n4, n5, n6, nd⟩ := mask_wires j h0 (by omega)
  have ar := fullArithmetic_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events flag
  have clears := flagScratch_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events flag
  have mask := maskCut_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events flag
  dsimp only at ar mask
  generalize hv : run (fullProgram j) m s = v at ar clears mask
  generalize hn : m.drop (measurementCount (fullProgram j)) = n
  have closed : run (releaseMaskP j) n v = ⟨v.phase, writeBit (writeBit v.basis 1557 false) 1558 false⟩ := mask.2 n
  generalize hu : run (releaseMaskP j) n v = u at closed
  have kept (q : Wire) (h : q ≠ 1557 ∧ q ≠ 1558) : u.basis q = v.basis q := by rw [closed]; simp [writeBit, h.1, h.2]
  have bits : ∀ i < Shadow7.wpP (start j) + 15, u.basis (live j i) = (TrueMiddle.F j z).testBit i := fun i h =>
    (kept _ ⟨(live_away j h0 (by omega) i h).2.1, (live_away j h0 (by omega) i h).2.2⟩).trans (ar.2.2.2.1 i h)
  have upper : regValue (smallM j) u.basis = regValue (smallM j) v.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h => kept _ ⟨(smallM_away j h0 (by omega) _ h).2.1, (smallM_away j h0 (by omega) _ h).2.2⟩)
  have lw := Shadow7.liveW_bounds w1 w2
  have hL : 3 ≤ Shadow7.lowsP (start j) ∧ Shadow7.lowsP (start j) ≤ Shadow7.liveW (start j) := by omega
  have scan : regValue (scanned2 j) u.basis = high (Shadow7.sbP (start j + 15)) 15 (step^[15] z) := by
    rw [outputScanned2 j h0 (by omega) u _ bits]
    have fit : TrueMiddle.F j z / 2^(Shadow7.lowsP (start j) - 2) < 2^(Shadow7.liveW (start j) - Shadow7.lowsP (start j) + 2) := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      rw [← Nat.pow_add, show Shadow7.liveW (start j) - Shadow7.lowsP (start j) + 2 + (Shadow7.lowsP (start j) - 2) = Shadow7.liveW (start j) by omega]
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
    exact (frame _ (live_away j h0 (by omega) i h).1 (live_away j h0 (by omega) i h).2.1 (live_away j h0 (by omega) i h).2.2).trans (ar.2.2.2.1 i h)

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
theorem head_eq (j : Fin 26) : entryOps (start j) ++ bodyOps j = Shadow7.leaveHeadOps (start j) := by
  simp only [entryOps, bodyOps, fullPrefix, workOps, middleOps, Shadow7.leaveHeadOps, List.append_assoc]

namespace CoreCheckpoint

/-- dadon's `Leave{s}CoreCheckpoint.program` (`leave.take 2260`). -/
abbrev program (j : Fin 26) : Program := GateMirror.forward (Shadow7.leaveHeadOps (start j))
/-- dadon's `rawSites`: the pool below the anchored block and the scratch above it. -/
def rawSites (j : Fin 26) : List Wire :=
  List.range' 1613 (Shadow7.e0P (start j) - 1613) ++ List.range' (Shadow7.e0P (start j) + 8) (min 1813 (2055 - start j) - (Shadow7.e0P (start j) + 8)) ++
    [Shadow7.b0P (start j) + 16]
abbrev magSites (j : Fin 26) : List Wire := LeaveJ7.fullM j
def targets (j : Fin 26) : List Wire :=
  List.range' 1559 39 ++ (List.finRange 17).map (fun i => (LeaveJ7.row j i).free) ++ rawSites j ++ magSites j

theorem raw_range (j : Fin 26) (q : Nat) (hq : q ∈ rawSites j) :
    (1613 ≤ q ∧ q < Shadow7.e0P (start j)) ∨ (Shadow7.e0P (start j) + 8 ≤ q ∧ q ≤ 1812 ∧ q + start j ≤ 2054) ∨
      q = Shadow7.b0P (start j) + 16 := by
  simp only [rawSites, List.mem_append, List.mem_range'_1, List.mem_singleton] at hq
  omega

/-- dadon's `Leave{s}CoreCheckpoint.result`. -/
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State)
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
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let out := run (program j) m s
    (∀ i : Fin 39, out.basis (1559 + i.val) = false) ∧
    (∀ i : Fin 17, out.basis (LeaveJ7.row j i).free = false) ∧
    (∀ q ∈ rawSites j, out.basis q = s.basis q) ∧ (∀ q ∈ magSites j, out.basis q = false) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have front := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
    (LeaveJ7.glueBound j z sg small) flag
  have used := full_routed j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events flag
  generalize ha : run (GateMirror.forward (entryOps (start j))) m s = a at front used
  generalize hn : m.drop (measurementCount (GateMirror.forward (entryOps (start j)))) = n at used
  have other (q : Nat) (hq : (1613 ≤ q ∧ q < Shadow7.e0P (start j)) ∨ (Shadow7.e0P (start j) + 8 ≤ q ∧ q ≤ 1812) ∨
      (Shadow7.b0P (start j) ≤ q ∧ q < Shadow7.b0P (start j) + 17)) :
      (run (GateMirror.forward (bodyOps j)) n a).basis q = a.basis q := by
    have notWire : HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q := by
      intro i hi e'; have b := Shadow7.bank_cases w1 w2 hi; unfold Wire at *; omega
    have notCols : ∀ c ∈ cols j, q ≠ c.shadow ∧ q ≠ c.tube := by
      intro c hc; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
      exact ⟨by dsimp only; unfold Wire at *; omega, by dsimp only; unfold Wire at *; omega⟩
    rw [used.2.2.2.2.1 q (by unfold Wire at *; omega) notWire notCols, cleared, if_neg (by omega)]
    exact prefix_keep j h0 (by omega) q (by omega) a n
  dsimp only
  rw [program, ← head_eq, forward_app, run_append, run_take, ha, hn]
  refine ⟨used.2.2.2.1, used.2.2.1, ?_, ?_⟩
  · intro q hq
    rcases raw_range j q hq with r | r | r
    · rw [other q (by omega), ← ha]
      exact entry_keep j h0 (by omega) q (by omega) s m
    · rw [other q (by omega), ← ha]
      exact entry_keep j h0 (by omega) q (by omega) s m
    · subst r
      rw [other _ (by omega), ← ha]
      exact entry_keeps_parked j h0 h1 s m
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    have e : (run (GateMirror.forward (bodyOps j)) n a).basis (Shadow7.b0P (start j) + i) = a.basis (Shadow7.b0P (start j) + i) :=
      other (Shadow7.b0P (start j) + i) (by omega)
    exact e.trans ((regValue_zero _ _).mp front.2.1 _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))

/-- The borrow wire 1558 is free after the head (G1 releases it in fix2P; the body never writes it): the `free58`
input of `Shadow7.leave_ready` / `relocated_clean` (fable-leap, margin 16). -/
theorem free58 (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State)
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
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    (run (program j) m s).basis 1558 = false := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have front := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
    (LeaveJ7.glueBound j z sg small) flag
  have used := full_routed j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events flag
  generalize ha : run (GateMirror.forward (entryOps (start j))) m s = a at front used
  generalize hn : m.drop (measurementCount (GateMirror.forward (entryOps (start j)))) = n at used
  rw [program, ← head_eq, forward_app, run_append, run_take, ha, hn]
  have notWire : HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) 1558 := by
    intro i hi e'; have b := Shadow7.bank_cases w1 w2 hi; unfold Wire at *; omega
  have notCols : ∀ c ∈ cols j, (1558 : Wire) ≠ c.shadow ∧ (1558 : Wire) ≠ c.tube := by
    intro c hc; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
    exact ⟨by dsimp only; unfold Wire at *; omega, by dsimp only; unfold Wire at *; omega⟩
  rw [used.2.2.2.2.1 1558 (by unfold Wire at *; omega) notWire notCols, cleared, if_neg (by omega),
    prefix_keep j h0 (by omega) 1558 (by omega) a n]
  exact front.2.2.2.2.1.2

/-- dadon's `Leave{s}CoreCheckpoint.oracle`: the five wires the Mirror asks to be clean after the head. -/
theorem oracle (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s out : State)
    (scr : ∀ i : Fin 39, out.basis (1559 + i.val) = false)
    (raw : ∀ q ∈ rawSites j, out.basis q = s.basis q) (c1613 : s.basis 1613 = false) (c1614 : s.basis 1614 = false) :
    ∀ q ∈ coreW, out.basis q = false := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have inRaw : ∀ q : Nat, 1613 ≤ q → q ≤ 1614 → q ∈ rawSites j := by
    intro q a b
    simp only [rawSites, List.mem_append, List.mem_range'_1]
    left; left; omega
  intro q hq
  rw [mem_coreW] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl
  · exact scr ⟨1, by decide⟩
  · exact scr ⟨17, by decide⟩
  · exact scr ⟨37, by decide⟩
  · exact (raw 1613 (inRaw 1613 (by decide) (by decide))).trans c1613
  · exact (raw 1614 (inRaw 1614 (by decide) (by decide))).trans c1614

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
end Routed

namespace FullArithmetic
/-- dadon's `Leave{s}FullArithmetic.program`. -/
abbrev program (j : Fin 26) : Program := LeaveJ7.fullProgram j
theorem restoreShape (j : Fin 26) :
    program j = CoreCheckpoint.program j ++ (LeaveJ7.borrowG4 j ++ Companion.restore (LeaveJ7.smallA j) (LeaveJ7.smallM j) (LeaveJ7.smallC j) 1556 1558) := by
  simp only [program, LeaveJ7.fullProgram, CoreCheckpoint.program, head_eq]
end FullArithmetic

namespace BeforeStore
/-- dadon's `Leave{s}BeforeStore.program`. -/
abbrev program (j : Fin 26) : Program :=
  LeaveJ7.fullProgram j ++ (LeaveJ7.releaseMaskP j ++ GateMirror.forward (Shadow7.leaveStoreMapped (start j)))

/-- dadon's `Leave{s}BeforeStore.result`. -/
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State)
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
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.liveW (start j)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let far := decide (Shadow.far (Shadow7.sbP (start j + 15)) 15 a)
    let v := run (FullArithmetic.program j) m s
    let out := run (program j) m s
    out.phase = s.phase ∧ out.basis 1556 = false ∧ out.basis 1557 = far ∧
      out.basis 1558 = (far && decide (2^(Shadow7.sbP (start j + 15)) ≤ a.u)) ∧
      regValue (LeaveJ7.smallM j) out.basis = (mag/2^(Shadow7.sbP (start j) + 1)) % 2^(Shadow7.lowsP (start j) - 1) ∧
      (∀ i < Shadow7.wpP (start j) + 15, out.basis (LeaveJ7.live j i) = (LeaveJ7.TrueMiddle.F j z).testBit i) ∧
      ∀ q, q ≠ 1556 → q ≠ 1557 → q ≠ 1558 → out.basis q = v.basis q :=
  beforeStore_result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
    nextSmall bound
end BeforeStore

namespace StoreMapped
/-- dadon's `Leave{s}StoreMapped.program` (the leave up to the low close). -/
abbrev program (j : Fin 26) : Program := BeforeStore.program j ++ GateMirror.forward (Shadow7.leaveLowClose (start j))
theorem program_eq (j : Fin 26) :
    program j = GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j)) := by
  simp only [program, BeforeStore.program, LeaveJ7.fullProgram, Shadow7.leaveMidOps, forward_app, LeaveJ7.lowRest_parts, ← head_eq,
    List.append_assoc]
end StoreMapped

/-- The low close writes only the history letters and the low columns: never wire 1556. -/
theorem lowClose_keeps (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    AllAT (fun _ => True) (fun t => t ≠ 1556) (Shadow7.leaveLowClose (start j)) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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
abbrev history (j : Fin 26) : List Wire := LeaveJ7.history j
/-- dadon's `Leave{s}Close.low`: the low columns, A side and B side. -/
def low (j : Fin 26) : List (Wire × Wire) :=
  (List.range (Shadow7.lowsP (start j))).map (fun i => (Shadow7.a0P (start j) - 1 + i, Shadow7.b0P (start j) - 1 + i))
/-- dadon's `Leave{s}Close.events`. -/
def events (j : Fin 26) : List (Wire × Wire) :=
  [(LeaveJ7.swaps j 0, 1556), (LeaveJ7.swaps j 1, 1559), (LeaveJ7.swaps j 2, 1560), (LeaveJ7.swaps j 3, 1561), (LeaveJ7.swaps j 4, 1562)]
/-- dadon's `Leave{s}Close.afterLow`. -/
abbrev afterLow (j : Fin 26) : Program := GateMirror.forward (Shadow7.leaveClose (start j))

/-- dadon's `Leave{s}Close.lowShape`. -/
theorem lowShape (j : Fin 26) : GateMirror.forward (Shadow7.leaveLowClose (start j)) =
    notRegister (history j) ++ store (start j + 30) (Shadow7.e0P (start j) + 5) (low j) [] := by
  have e1 : GateMirror.forward ((List.range (Shadow7.lowsP (start j))).map
      (fun i => Gate.cx (Shadow7.e0P (start j) + 5) (Shadow7.b0P (start j) - 1 + i))) =
      signComplement (Shadow7.e0P (start j) + 5) ((low j).map Prod.snd) := by
    simp only [GateMirror.forward, signComplement, low, List.map_map]; rfl
  have e2 : GateMirror.forward ((List.range (Shadow7.lowsP (start j))).flatMap
      (fun i => cswapG (start j + 30) (Shadow7.b0P (start j) - 1 + i) (Shadow7.a0P (start j) - 1 + i))) =
      exchange (start j + 30) (low j) := by
    simp only [GateMirror.forward, exchange, low, List.map_flatMap, List.flatMap_map]; rfl
  simp only [Shadow7.leaveLowClose, forward_app, forward_xsG', e1, e2, store, transfer, List.flatMap_nil, List.nil_append,
    List.append_assoc]
  rfl

theorem mem_low_sites (j : Fin 26) (q : Wire) : q ∈ RailPair.sites (low j) ↔
    ∃ i, i < Shadow7.lowsP (start j) ∧ (q = Shadow7.a0P (start j) - 1 + i ∨ q = Shadow7.b0P (start j) - 1 + i) := by
  simp only [RailPair.sites, low, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · rintro ⟨p, ⟨i, hi, rfl⟩, h⟩; exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨_, ⟨i, hi, rfl⟩, h⟩

theorem low_fst (j : Fin 26) : (low j).map Prod.fst = (List.range (Shadow7.lowsP (start j))).map (fun i => (Shadow7.a0P (start j) - 1 + i : Wire)) := by
  simp only [low, List.map_map]; rfl
theorem low_snd (j : Fin 26) : (low j).map Prod.snd = (List.range (Shadow7.lowsP (start j))).map (fun i => (Shadow7.b0P (start j) - 1 + i : Wire)) := by
  simp only [low, List.map_map]; rfl

theorem low_fst_nodup (j : Fin 26) : ((low j).map Prod.fst).Nodup := by
  rw [low_fst]
  refine List.Nodup.map_on (fun x _ y _ e => ?_) List.nodup_range
  have e' : Shadow7.a0P (start j) - 1 + x = Shadow7.a0P (start j) - 1 + y := e
  (try unfold Wire at *); omega
theorem low_snd_nodup (j : Fin 26) : ((low j).map Prod.snd).Nodup := by
  rw [low_snd]
  refine List.Nodup.map_on (fun x _ y _ e => ?_) List.nodup_range
  have e' : Shadow7.b0P (start j) - 1 + x = Shadow7.b0P (start j) - 1 + y := e
  (try unfold Wire at *); omega

/-- dadon's `StoreGeometry` of the low close. -/
theorem low_geometry (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    StoreGeometry (start j + 30) (Shadow7.e0P (start j) + 5) (low j) [] := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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
theorem lowResult (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) :
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

/-- Margin 16: G4 (`borrowG4`, before the restore) writes only 1557 / 1558. -/
theorem g4_off (j : Fin 26) (q : Wire) (h7 : q ≠ 1557) (h8 : q ≠ 1558) :
    q ∉ (LeaveJ7.borrowG4 j).map LeaveReadoutFrame.destination := by
  simp [LeaveJ7.borrowG4, LeaveReadoutFrame.destination, h7, h8]

/-- dadon's `Leave{s}StoreCoordinates.result`, on `beforeStoreProgram`. -/
theorem storeCoordinates_result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool)
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
    (bound : TrueMiddle.F j z < 2^(Shadow7.liveW (start j)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let out := run (beforeStoreProgram j) m s
    out.basis (Shadow7.e0P (start j) + 5) = PortalValues.negative sg a.u ∧ (∀ q ∈ history j, out.basis q = !s.basis q) ∧
    (∀ i : Fin (Shadow7.lowsP (start j)), out.basis (Shadow7.a0P (start j) - 1 + i.val) = (a.u+a.v).testBit (Shadow7.sbP (start j) + i.val) ∧
        out.basis (Shadow7.b0P (start j) - 1 + i.val) = mag.testBit (Shadow7.sbP (start j) + i.val)) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have src := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
    (LeaveJ7.glueBound j z sg small) flag
  have par0 := entry_parity j h0 (by omega) s m
  have stored := beforeStore_result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound
  have lowMag := (maskCut_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events flag).1
  dsimp only at src stored lowMag ⊢
  generalize hen : run (GateMirror.forward (entryOps (start j))) m s = en at src par0
  have afterEntry (q : Nat) (hm : ¬ midT j q) (hc : ¬ compT j q) (h7 : q ≠ 1557) (h8 : q ≠ 1558) :
      (run (fullProgram j) m s).basis q = en.basis q := by
    rw [fullProgram, forward_app, List.append_assoc, run_append, run_take, run_append, run_take, hen,
      LeaveReadoutFrame.preserved (LeaveJ7.borrowG4 j ++ Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558) _ _ q (fun h => by
        rw [List.map_append, List.mem_append] at h
        exact h.elim (g4_off j q h7 h8) (fun h => hc (restore_dest j h0 (by omega) q h))),
      LeaveReadoutFrame.preserved _ _ _ _ (fun h => hm (body_dest j h0 (by omega) q h))]
  have raw (q : Nat) (h6 : q ≠ 1556) (h7 : q ≠ 1557) (h8 : q ≠ 1558) (hm : ¬ midT j q) (hc : ¬ compT j q) :
      (run (beforeStoreProgram j) m s).basis q = en.basis q :=
    (stored.2.2.2.2.2.2 q h6 h7 h8).trans (afterEntry q hm hc h7 h8)
  refine ⟨?_, ?_, ?_⟩
  · rw [raw (Shadow7.e0P (start j) + 5) (by omega) (by omega) (by omega) (by unfold midT workT; omega) (by unfold compT; omega)]
    exact src.2.2.1.trans (LeaveShadowRails.retainedLow_shadow7 (Shadow7.sbP (start j)) z small.1 sg).1.symm
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    have e : (run (beforeStoreProgram j) m s).basis (start j + 16 + i) = en.basis (start j + 16 + i) :=
      raw (start j + 16 + i) (by omega) (by omega) (by omega) (by unfold midT workT; omega) (by unfold compT; omega)
    unfold LeaveSelector.parityBits oddRead at par0
    have pe := (List.map_inj_left.mp par0) i (List.mem_range.mpr hi)
    exact e.trans pe
  · rintro ⟨k, hk⟩
    have posA : (run (beforeStoreProgram j) m s).basis (Shadow7.a0P (start j) - 1 + k) =
        ((step^[15] z).u + (step^[15] z).v).testBit (Shadow7.sbP (start j) + k) := by
      have pos := stored.2.2.2.2.2.1 k (by omega)
      have lk : live j k = Shadow7.a0P (start j) - 1 + k := by unfold live; rw [if_pos hk]
      rw [lk] at pos
      unfold TrueMiddle.F HighBankSum.total at pos
      rw [Nat.testBit_div_two_pow] at pos
      rw [show Shadow7.sbP (start j) + k = k + Shadow7.sbP (start j) by omega]
      exact pos
    refine ⟨posA, ?_⟩
    cases k with
    | zero =>
      have bit := LeaveCompanion.thresholdBit ((step^[15] z).u - (PortalValues.negative sg (step^[15] z).u).toNat)
        (2^(Shadow7.sbP (start j))) (Nat.two_pow_pos _)
      rw [Nat.testBit_div_two_pow] at bit
      simp only [Nat.zero_add, Nat.add_zero] at bit ⊢
      have b6 : Shadow7.b0P (start j) - 1 ≠ 1556 := by omega
      have b7 : Shadow7.b0P (start j) - 1 ≠ 1557 := by omega
      have b8 : Shadow7.b0P (start j) - 1 ≠ 1558 := by omega
      rw [stored.2.2.2.2.2.2 (Shadow7.b0P (start j) - 1) b6 b7 b8]
      exact lowMag.trans bit.symm
    | succ k =>
      have hk' : k < Shadow7.lowsP (start j) - 1 := by omega
      have signedBit := HighBankAdjust.bit_read (smallM j) k (run (beforeStoreProgram j) m s).basis
        (by rw [smallM_length]; exact hk')
      have gk : (smallM j).getD k 0 = Shadow7.b0P (start j) + k := by
        simp [smallM, List.getD_eq_getElem?_getD, hk']
      rw [gk, stored.2.2.2.2.1, Nat.testBit_mod_two_pow, decide_eq_true hk', Bool.true_and, Nat.testBit_div_two_pow]
        at signedBit
      have ib : Shadow7.b0P (start j) - 1 + (k+1) = Shadow7.b0P (start j) + k := by omega
      have ix : Shadow7.sbP (start j) + (k+1) = k + (Shadow7.sbP (start j) + 1) := by omega
      rw [ib, ix]
      exact signedBit

/-- The low close on the stored coordinates (dadon's private `store` of `Leave{s}StoreMapped`). -/
theorem lowClose_store (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s v : State) (m : List Bool) (G sign : Bool)
    (sum mag : Nat) (previous : s.basis (start j + 30) = G) (hist : ∀ q ∈ history j, v.basis q = !s.basis q)
    (signed : v.basis (Shadow7.e0P (start j) + 5) = sign)
    (words : ∀ i : Fin (Shadow7.lowsP (start j)), v.basis (Shadow7.a0P (start j) - 1 + i.val) = sum.testBit (Shadow7.sbP (start j) + i.val) ∧
      v.basis (Shadow7.b0P (start j) - 1 + i.val) = mag.testBit (Shadow7.sbP (start j) + i.val)) :
    let out := run (GateMirror.forward (Shadow7.leaveLowClose (start j))) m v
    out.phase = v.phase ∧ (∀ q ∈ history j, out.basis q = s.basis q) ∧
    (∀ i : Fin (Shadow7.lowsP (start j)), let pos := sum.testBit (Shadow7.sbP (start j) + i.val)
        let neg := mag.testBit (Shadow7.sbP (start j) + i.val) ^^ sign
        out.basis (Shadow7.a0P (start j) - 1 + i.val) = (if G then neg else pos) ∧
        out.basis (Shadow7.b0P (start j) - 1 + i.val) = (if G then pos else neg)) ∧
    ∀ q, q ∉ RailPair.sites (Close.low j) → q ∉ history j → out.basis q = v.basis q := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State)
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
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.liveW (start j)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let a := step^[15] z
    let mag := a.u - (PortalValues.negative sg a.u).toNat
    let out := run (BeforeStore.program j) m s
    out.basis (Shadow7.e0P (start j) + 5) = PortalValues.negative sg a.u ∧ (∀ q ∈ Close.history j, out.basis q = !s.basis q) ∧
    (∀ i : Fin (Shadow7.lowsP (start j)), out.basis (Shadow7.a0P (start j) - 1 + i.val) = (a.u+a.v).testBit (Shadow7.sbP (start j) + i.val) ∧
        out.basis (Shadow7.b0P (start j) - 1 + i.val) = mag.testBit (Shadow7.sbP (start j) + i.val)) :=
  storeCoordinates_result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
    nextSmall bound
end StoreCoordinates

namespace StoreMapped
/-- dadon's `Leave{s}StoreMapped.result`. -/
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State)
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
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.liveW (start j)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let a := step^[15] z
    let sign := PortalValues.negative sg a.u
    let mag := a.u - sign.toNat
    let before := run (BeforeStore.program j) m s
    let out := run (program j) m s
    out.phase = s.phase ∧ (∀ q ∈ Close.history j, out.basis q = s.basis q) ∧
      (∀ i : Fin (Shadow7.lowsP (start j)), let pos := (a.u+a.v).testBit (Shadow7.sbP (start j) + i.val)
        let neg := mag.testBit (Shadow7.sbP (start j) + i.val) ^^ sign
        out.basis (Shadow7.a0P (start j) - 1 + i.val) = (if G then neg else pos) ∧
        out.basis (Shadow7.b0P (start j) - 1 + i.val) = (if G then pos else neg)) ∧
      ∀ q, q ∉ RailPair.sites (Close.low j) → q ∉ Close.history j → out.basis q = before.basis q := by
  have coords := storeCoordinates_result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero
    par mode events nextSmall bound
  have prev : s.basis (start j + 30) = G := by
    have h := ready.2.2.1
    rw [(scan_ports j h0 (by omega)).2.2.2.2.1]
    cases G <;> exact h
  have phase := (beforeStore_result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
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
theorem swaps_exact (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (i : Nat) (hi : i < 15) :
    ((swaps j i : Nat) = start j + 1044 + i ∧ start j + 1044 + i ≤ 1300) ∨
      ((swaps j i : Nat) = 3113 - (start j + 1044 + i) ∧ Shadow7.e0P (start j) + 10 ≤ 3113 - (start j + 1044 + i) ∧
        3113 - (start j + 1044 + i) ≤ 1812) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have e := Shadow7.sig_hist (c := 1044 + i) w1 w2 (by omega) (by omega)
  unfold swaps; rw [show start j + 1044 + i = start j + (1044 + i) by omega]
  unfold Wire at *; omega

/-- The near flag of the prepared selector word. -/
theorem prior_near (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (k : Mode) :
    prior j k (Shadow7.e0P (start j) + 7) = .bit (nearby k) := by
  have h := controlCert j h0 (by omega) k
  simp only [reads, LeaveSelector.controls, List.cons.injEq, and_true] at h
  exact h.1

namespace PostReady

/-- dadon's `Leave{s}PostReady.result`. -/
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State)
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
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.liveW (start j)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let out := run (StoreMapped.program j) m s
    let f := decide (Shadow.far (Shadow7.sbP (start j)) 15 z)
    out.basis (Shadow7.e0P (start j) + 3) = s.basis (Shadow7.e0P (start j) + 3) ∧
    out.basis (Shadow7.e0P (start j) + 4) = s.basis (Shadow7.e0P (start j) + 4) ∧
    out.basis (Shadow7.e0P (start j) + 7) = nearby (actualMode (Shadow7.sbP (start j)) z) ∧
    out.basis (Shadow7.e0P (start j) + 6) = (f && HighBankSum.crossBit (LeaveJ7.TrueMiddle.d j z)) ∧
    (∀ p ∈ Close.events j, out.basis p.1 = s.basis p.1 ∧ out.basis p.2 = false) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have front := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
    (LeaveJ7.glueBound j z sg small) flag
  have watchedOK := frontReady_frame j h0 (by omega) s m z G sg small ready fresh scratch temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
    (LeaveJ7.glueBound j z sg small) flag
  have par0 := entry_parity j h0 (by omega) s m
  have store := (StoreMapped.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound).2.2.2
  have flags := beforeStore_result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound
  have cleared := flagScratch_result j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events flag
  have used := full_routed j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events flag
  dsimp only at front store flags used ⊢
  generalize hen : run (GateMirror.forward (entryOps (start j))) m s = en at front watchedOK par0 used
  generalize hn : m.drop (measurementCount (GateMirror.forward (entryOps (start j)))) = n at used ⊢
  generalize hk : actualMode (Shadow7.sbP (start j)) z = k at mode events ⊢
  have kept (q : Nat) (ok : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 16) ∨
      (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 16) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨
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
  have notLow (q : Nat) (hq : ∀ i, i < Shadow7.lowsP (start j) → q ≠ Shadow7.a0P (start j) - 1 + i ∧ q ≠ Shadow7.b0P (start j) - 1 + i) :
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
  have fullAt (q : Nat) (hw : ¬ workT j q) (h3 : q ≠ Shadow7.e0P (start j) + 3) (hc : ¬ compT j q) (h7 : q ≠ 1557)
      (h8 : q ≠ 1558) :
      (run (fullProgram j) m s).basis q = (run (GateMirror.forward (fullPrefix j)) n en).basis q := by
    have e1 : run (fullProgram j) m s = run (LeaveJ7.borrowG4 j ++ Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558)
        (n.drop (measurementCount (GateMirror.forward (bodyOps j)))) (run (GateMirror.forward (bodyOps j)) n en) := by
      rw [fullProgram, forward_app, List.append_assoc, run_append, run_take, run_append, run_take, hen, hn]
    have e2 : run (GateMirror.forward (bodyOps j)) n en = run (GateMirror.forward (workOps (start j)))
        (n.drop (measurementCount (GateMirror.forward (fullPrefix j)))) (run (GateMirror.forward (fullPrefix j)) n en) := by
      rw [bodyOps, forward_app, run_append, run_take]
    rw [e1, LeaveReadoutFrame.preserved (LeaveJ7.borrowG4 j ++ Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558) _ _ q (fun h => by
        rw [List.map_append, List.mem_append] at h
        exact h.elim (g4_off j q h7 h8) (fun h => hc (restore_dest j h0 (by omega) q h))), e2,
      LeaveReadoutFrame.preserved _ _ _ _ (fun h => (work_dest j h0 (by omega) q h).elim hw h3)]
  -- the far flag e0+3 is written and restored by the middle: its value comes from the routed body
  have fullAt3 : (run (fullProgram j) m s).basis (Shadow7.e0P (start j) + 3) =
      (run (GateMirror.forward (fullPrefix j)) n en).basis (Shadow7.e0P (start j) + 3) := by
    have e1 : run (fullProgram j) m s = run (LeaveJ7.borrowG4 j ++ Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558)
        (n.drop (measurementCount (GateMirror.forward (bodyOps j)))) (run (GateMirror.forward (bodyOps j)) n en) := by
      rw [fullProgram, forward_app, List.append_assoc, run_append, run_take, run_append, run_take, hen, hn]
    obtain ⟨d3, o3, c3⟩ := core_untouched j h0 (by omega) (Shadow7.e0P (start j) + 3) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have nc : ¬ compT j (Shadow7.e0P (start j) + 3) := by unfold compT; omega
    rw [e1, LeaveReadoutFrame.preserved (LeaveJ7.borrowG4 j ++ Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558) _ _ (Shadow7.e0P (start j) + 3) (fun h => by
        rw [List.map_append, List.mem_append] at h
        exact h.elim (g4_off j _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
          (fun h => nc (restore_dest j h0 (by omega) _ h))),
      used.2.2.2.2.1 _ (by omega) o3 c3]
    unfold LeaveSelector.cleared; rw [if_neg (by omega)]
  have outAt (q : Nat) (h6 : q ≠ 1556) (h7 : q ≠ 1557) (h8 : q ≠ 1558)
      (hl : ∀ i, i < Shadow7.lowsP (start j) → q ≠ Shadow7.a0P (start j) - 1 + i ∧ q ≠ Shadow7.b0P (start j) - 1 + i)
      (hh : q < start j + 16 ∨ start j + 30 < q) :
      (run (StoreMapped.program j) m s).basis q = (run (fullProgram j) m s).basis q :=
    (store q (notLow q hl) (notHist q hh)).trans (flags.2.2.2.2.2.2 q h6 h7 h8)
  have hit (q : Nat) (hq : q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7) :
      (run (StoreMapped.program j) m s).basis q = (prior j k q).read en.basis := by
    rw [outAt q (by omega) (by omega) (by omega) (fun i hi => by omega) (by omega),
      fullAt q (by unfold workT; omega) (by omega) (by unfold compT; omega) (by omega) (by omega), prepared]
    rfl
  have plain (q : Nat) (h6 : q ≠ 1556) (h7 : q ≠ 1557) (h8 : q ≠ 1558)
      (hl : ∀ i, i < Shadow7.lowsP (start j) → q ≠ Shadow7.a0P (start j) - 1 + i ∧ q ≠ Shadow7.b0P (start j) - 1 + i)
      (hh : q < start j + 16 ∨ start j + 30 < q) (hw : ¬ workT j q) (h3 : q ≠ Shadow7.e0P (start j) + 3) (hc : ¬ compT j q)
      (hp : ¬ ((1559 ≤ q ∧ q ≤ 1597) ∨ q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7))
      (he : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 16) ∨
        (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 16) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨
        (1556 ≤ q ∧ q ≤ 1575) ∨ q = Shadow7.e0P (start j) + 5)) :
      (run (StoreMapped.program j) m s).basis q = s.basis q :=
    (outAt q h6 h7 h8 hl hh).trans ((fullAt q hw h3 hc h7 h8).trans ((prefix_keep j h0 (by omega) q hp en n).trans (kept q he)))
  have plainSwap (i : Nat) (hi : i < 15) :
      (run (StoreMapped.program j) m s).basis (swaps j i) = s.basis (swaps j i) := by
    have sw := swaps_exact j h0 (by omega) i hi
    exact plain (swaps j i) (by unfold Wire at *; omega) (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      (fun x hx => by unfold Wire at *; omega) (by unfold Wire at *; omega) (by unfold workT; unfold Wire at *; omega)
      (by unfold Wire at *; omega)
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
  have math := loaded_signed j h0 (by omega) z en.basis small odd room (fun i hi => act i (Nat.lt_trans hi (by decide : 16 < 17)))
    (par0.trans par)
  dsimp only at math
  rw [hk] at math
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (outAt (Shadow7.e0P (start j) + 3) (by omega) (by omega) (by omega) (fun i hi => by omega) (by omega)).trans
      (fullAt3.trans ((prefix_keep j h0 (by omega) _ (by omega) en n).trans (kept _ (by omega))))
  · exact plain (Shadow7.e0P (start j) + 4) (by omega) (by omega) (by omega) (fun i hi => by omega) (by omega)
      (by unfold workT; omega) (by omega) (by unfold compT; omega) (by omega) (by omega)
  · rw [hit _ (Or.inr rfl), prior_near j h0 (by omega) k]; rfl
  · rw [hit _ (Or.inl rfl), math.1]
    by_cases g : Shadow.far (Shadow7.sbP (start j)) 15 z <;> simp [g, HighBankSum.crossBit]
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
abbrev moves (j : Fin 26) : List (Wire × Wire) := Shadow7.movesP (start j)
/-- dadon's `Leave{s}Relocated.lastPart`. -/
abbrev lastPart (j : Fin 26) : Program := GateMirror.forward (swapsG (Shadow7.movesP (start j)))

theorem lastPart_eq (s : Nat) : GateMirror.forward (swapsG (Shadow7.movesP s)) = LeaveRelocation.program (Shadow7.movesP s) := by
  simp only [swapsG, LeaveRelocation.program, GateMirror.forward, List.map_flatMap]; rfl

/-- No move is a self swap. -/
theorem moves_diff (s : Nat) (h1 : 45 ≤ s) (h2 : s ≤ 405) : ∀ p ∈ Shadow7.movesP s, p.1 ≠ p.2 := by
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
theorem forward (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (st : State) (m : List Bool) :
    run (lastPart j) m st = ⟨st.phase, fun q => st.basis (LeaveRelocation.source (moves j) q)⟩ := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  rw [lastPart, lastPart_eq]
  exact LeaveRelocation.actual _ (moves_diff (start j) w1 w3) st m

/-- The three flags the next block reads come from the far flag, the near flag and the crossing bit. -/
theorem src_back (s : Nat) (h1 : 45 ≤ s) (h2 : s ≤ 405) :
    source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 6) = Shadow7.e0P s + 3 ∧ source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 7) = Shadow7.e0P s + 7 ∧
    source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 8) = Shadow7.e0P s + 6 := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  have ab (k : Nat) :
      ((bankPair s k).1 = 803 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  have bankOut (x : Wire) (hx : Shadow7.e0P (s+15) ≤ x) :
      source ((List.range (Shadow7.wpP (s+15) - 2)).map (bankPair s)) x = x := by
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
theorem upperMap (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ∀ i : Nat, i < railP (start j + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j)) →
      LeaveRelocation.source (moves j) (Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 + i) = LeaveJ7.live j (Shadow7.lowsP (start j) + i) ∧
      LeaveRelocation.source (moves j) (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i) = Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i := by
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
theorem tailShape (j : Fin 26) : afterLow j =
    GateMirror.forward (Shadow7.parityG (Shadow7.e0P (start j) + 7) (Shadow7.e0P (start j) + 4) 1556
      ((events j).map Prod.fst)) ++ Relocated.lastPart j := by
  show GateMirror.forward (Shadow7.leaveClose (start j)) = _
  unfold Shadow7.leaveClose
  rw [forward_app]
  rfl

theorem events_layout (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ((Shadow7.e0P (start j) + 4 : Wire) :: (Shadow7.e0P (start j) + 7 : Wire) :: PortalAnd.sites (events j)).Nodup := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have e61 : 1620 ≤ Shadow7.e0P (start j) := by have rr := Shadow7.rail_win w1 w2; omega
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

/-- The wires of the flag gadget are pairwise apart (fable-cuts; `events_layout`'s geometry). -/
theorem flag_apart (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (Shadow7.e0P (start j) + 7 : Wire) ≠ 1556 ∧ (Shadow7.e0P (start j) + 7 : Wire) ≠ Shadow7.e0P (start j) + 4 ∧
    (1556 : Wire) ≠ Shadow7.e0P (start j) + 4 ∧ (1556 : Wire) ∉ (events j).map Prod.fst ∧
    (Shadow7.e0P (start j) + 4 : Wire) ∉ (events j).map Prod.fst := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have e61 : 1620 ≤ Shadow7.e0P (start j) := by have rr := Shadow7.rail_win w1 w2; omega
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
  refine ⟨?_, ?_, ?_, fun h => ?_, fun h => ?_⟩
  · ((try unfold Wire at *); omega)
  · ((try unfold Wire at *); omega)
  · ((try unfold Wire at *); omega)
  · have a := memF _ h; ((try unfold Wire at *); omega)
  · have a := memF _ h; ((try unfold Wire at *); omega)

/-- dadon's `Leave{s}Close.after`, with the flag cleared by the parity gadget (fable-cuts): the old orientation flag
`e0+4` holds `e0+7 ∧ ¬ (parity of the first five swap records)`. -/
theorem after (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool)
    (cold : ∀ p ∈ events j, s.basis p.2 = false)
    (value : s.basis (Shadow7.e0P (start j) + 4) =
      (s.basis (Shadow7.e0P (start j) + 7) && !HighBankControl.parity s.basis ((events j).map Prod.fst))) :
    run (afterLow j) m s =
      ⟨s.phase, fun q => (writeBit s.basis (Shadow7.e0P (start j) + 4) false) (LeaveRelocation.source (Relocated.moves j) q)⟩ := by
  obtain ⟨ax, ao, xo, xr, outr⟩ := flag_apart j h0 (by omega)
  have c56 : s.basis 1556 = false := cold (swaps j 0, 1556) (by simp [events])
  rw [tailShape, run_append, run_take, Shadow7.parity_run _ _ _ _ s m ax ao xo xr outr c56 value,
    Relocated.forward j h0 (by omega)]

end Close

namespace Posted
open StairArchiveTrace

/-- dadon's `Leave{s}Posted.result`. -/
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (f u c : Bool) (w : Fin 16)
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
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have vp := LeavePendingHistory.pending f u xs w len chainOK first
  have value : s.basis (Shadow7.e0P (start j) + 4) =
      (s.basis (Shadow7.e0P (start j) + 7) && !HighBankControl.parity s.basis ((Close.events j).map Prod.fst)) := by
    have reads : HighBankControl.parity s.basis ((Close.events j).map Prod.fst) =
        Shadow7.xorBits ((xs.take 5).map Prod.snd) := by
      rw [Shadow7.parity_bits, List.map_map]
      exact congrArg Shadow7.xorBits swaps
    rw [old, suffix, reads]
    cases f with
    | false => first | rfl | simp [nearby, ofFlags, enabled]
    | true =>
      rw [Shadow7.chain_parity 5 u xs (chainOK rfl)]
      have h : ((true && u) ^^ (nearby (ofFlags true u w) && !(xs.take 5).any Prod.snd)) = false := vp.2
      revert h
      generalize (true && u) = A
      generalize (nearby (ofFlags true u w) && !(xs.take 5).any Prod.snd) = B
      cases A <;> cases B <;> decide
  have geom := Relocated.src_back (start j) w1 w3
  have wb (q : Nat) (hq : q ≠ Shadow7.e0P (start j) + 4) : writeBit s.basis (Shadow7.e0P (start j) + 4) false q = s.basis q := by
    simp [writeBit, Function.update, hq]
  have a := Close.after j h0 (by omega) s m cold value
  dsimp only
  rw [a]
  refine ⟨rfl, ?_, ?_, ?_, fun _ => rfl⟩
  · show writeBit s.basis (Shadow7.e0P (start j) + 4) false (LeaveRelocation.source (Shadow7.movesP (start j)) (Shadow7.e0P (start j + 15) + 6)) = f
    rw [geom.1, wb _ (by omega)]; exact far
  · show writeBit s.basis (Shadow7.e0P (start j) + 4) false (LeaveRelocation.source (Shadow7.movesP (start j)) (Shadow7.e0P (start j + 15) + 7)) = _
    rw [geom.2.1, wb _ (by omega)]; exact suffix.trans vp.1
  · show writeBit s.basis (Shadow7.e0P (start j) + 4) false (LeaveRelocation.source (Shadow7.movesP (start j)) (Shadow7.e0P (start j + 15) + 8)) = _
    rw [geom.2.2, wb _ (by omega)]; exact cross

end Posted

/-- The leave is the store part followed by the close. -/
theorem leave_split (j : Fin 26) : Shadow7.leaveP j = StoreMapped.program j ++ Close.afterLow j := by
  rw [StoreMapped.program_eq, Shadow7.leaveP, Shadow7.leaveOps_split, forward_app]

namespace Whole

/-- dadon's `Leave{s}Whole.result`. -/
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State)
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
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.liveW (start j))) (xs : List (Bool × Bool)) (len : xs.length = 15)
    (historyOK : Shadow.far (Shadow7.sbP (start j)) 15 z → StairArchiveTrace.chain (decide (2^(Shadow7.sbP (start j)) ≤ z.u)) xs)
    (first : Shadow.far (Shadow7.sbP (start j)) 15 z → decide (2^(Shadow7.sbP (start j)) ≤ z.u) = false →
      ∀ i (h : i < xs.length), i ≤ IntegerHigh.wait 15 z.u → xs[i].2 = decide (i = IntegerHigh.wait 15 z.u))
    (saved : (Close.events j).map (fun p => s.basis p.1) = (xs.take 5).map Prod.snd)
    (far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
    (side : s.basis (Shadow7.e0P (start j) + 4) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let u := decide (2^(Shadow7.sbP (start j)) ≤ z.u)
    let active := decide (Shadow.far (Shadow7.sbP (start j)) 15 z)
    let v := run (StoreMapped.program j) m s
    let out := run (Shadow7.leaveP j) m s
    out.phase = s.phase ∧ out.basis (Shadow7.e0P (start j + 15) + 6) = active ∧
      out.basis (Shadow7.e0P (start j + 15) + 7) = (active && StairArchiveTrace.afterFlags u (xs.take 5)) ∧
      out.basis (Shadow7.e0P (start j + 15) + 8) = (active && HighBankSum.crossBit (LeaveJ7.TrueMiddle.d j z)) ∧
      ∀ q, out.basis q = writeBit v.basis (Shadow7.e0P (start j) + 4) false (LeaveRelocation.source (Relocated.moves j) q) := by
  have h := PostReady.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode
    events nextSmall bound
  have pre := (StoreMapped.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound).1
  dsimp only at h pre ⊢
  generalize hv : run (StoreMapped.program j) m s = v at h pre
  have reads : (Close.events j).map (fun p => v.basis p.1) = (xs.take 5).map Prod.snd :=
    (List.map_congr_left (fun p hp => (h.2.2.2.2 p hp).1)).trans saved
  have done := Posted.result j h0 (by omega) v (m.drop (measurementCount (StoreMapped.program j)))
    (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (2^(Shadow7.sbP (start j)) ≤ z.u))
    (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d j z))
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
theorem cells_eq (j : Fin 26) (h1 : j.val ≤ 24) (v : BasisState) :
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
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (z : SkywalkNat.State) (g sg : Bool)
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
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (z : SkywalkNat.State) (g sg : Bool)
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
/-- Margin-16 glue (fable-leap): at the leave start the G2 side flag `e0P+4 ^^ (e0P+3 && first swap record)` is
`far ∧ farKey = 0` (`LeaveShadowRails.key0Flag`). Feeds `entry_core`'s `flag` with `K := far ∧ farKey = 0`. -/
theorem glueFlag (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z) (odd : z.v % 2 = 1)
    (record : IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v))
    (far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
    (side : s.basis (Shadow7.e0P (start j) + 4) =
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u))) :
    (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0) := by
  have ev := (result j h0 h1 s z g sg small odd record).1
  have rec0 : s.basis (OB5.sig (start j + 14) (start j + 1044)) =
      ((SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v))[0]?.getD (false, false)).2 := by
    generalize SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v) = xs at ev ⊢
    cases xs with
    | nil => simp [Close.events] at ev
    | cons x xs =>
      have hd := congrArg List.head? ev
      rw [show (x :: xs).take 5 = x :: xs.take 4 from rfl] at hd
      simp only [Close.events, List.map_cons, List.head?_cons, Option.some.injEq] at hd
      simp only [List.getElem?_cons_zero, Option.getD_some]
      exact hd
  rw [side, far, rec0]
  by_cases f : Shadow.far (Shadow7.sbP (start j)) 15 z
  · have k := LeaveShadowRails.key0Flag (Shadow7.sbP (start j)) z g sg (small.1 f) odd f
    simpa [f] using k
  · simp [f]

end RecordedEvents

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial IntegerPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
attribute [local irreducible] Shadow7.leaveP run
namespace PreservedRecords
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool)
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
theorem src_flagsBack (s : Nat) (h1 : 45 ≤ s) (h2 : s ≤ 405) :
    source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 3) = 1557 ∧ source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 4) = 1558 ∧
    source (Shadow7.movesP s) (Shadow7.e0P (s+15) + 5) = Shadow7.e0P s + 5 := by
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := chain_geo h1 h2
  have ab (k : Nat) :
      ((bankPair s k).1 = 803 + Shadow7.sbP (s+15) + 15 + k ∧ k < Shadow7.wpP s - Shadow7.lowsP s) ∨
      ((bankPair s k).1 = 1598 + k - (Shadow7.wpP s - Shadow7.lowsP s) ∧ Shadow7.wpP s - Shadow7.lowsP s ≤ k) := by
    by_cases b : k < Shadow7.wpP s - Shadow7.lowsP s
    · exact Or.inl ⟨hB k b, b⟩
    · exact Or.inr ⟨hP k (by omega), by omega⟩
  have bankOut (x : Wire) (hx : x = 1557 ∨ x = 1558 ∨ x = Shadow7.e0P s + 5) :
      source ((List.range (Shadow7.wpP (s+15) - 2)).map (bankPair s)) x = x := by
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
theorem upper_away (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (i : Nat)
    (hi : i < railP (start j + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j))) :
    (Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) : Nat) ≠ Shadow7.e0P (start j) + 4 ∧
    Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) ∉ RailPair.sites (Close.low j) ∧
    Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i) ∉ Close.history j := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State)
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
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.liveW (start j))) (xs : List (Bool × Bool)) (len : xs.length = 15)
    (historyOK : Shadow.far (Shadow7.sbP (start j)) 15 z → StairArchiveTrace.chain (decide (2^(Shadow7.sbP (start j)) ≤ z.u)) xs)
    (first : Shadow.far (Shadow7.sbP (start j)) 15 z → decide (2^(Shadow7.sbP (start j)) ≤ z.u) = false →
      ∀ i (h : i < xs.length), i ≤ IntegerHigh.wait 15 z.u → xs[i].2 = decide (i = IntegerHigh.wait 15 z.u))
    (saved : (Close.events j).map (fun p => s.basis p.1) = (xs.take 5).map Prod.snd)
    (far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
    (side : s.basis (Shadow7.e0P (start j) + 4) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let a := step^[15] z
    let sign := PortalValues.negative sg a.u
    let mag := a.u - sign.toNat
    let next := decide (Shadow.far (Shadow7.sbP (start j + 15)) 15 a)
    let out := run (Shadow7.leaveP j) m s
    out.basis (Shadow7.e0P (start j + 15) + 3) = next ∧ out.basis (Shadow7.e0P (start j + 15) + 4) = (next && decide (2^(Shadow7.sbP (start j + 15)) ≤ a.u)) ∧
      out.basis (Shadow7.e0P (start j + 15) + 5) = sign ∧
      (∀ q ∈ Close.history j, out.basis q = s.basis q) ∧
      (∀ i : Fin (Shadow7.lowsP (start j)), let pos := (a.u+a.v).testBit (Shadow7.sbP (start j) + i.val)
        let neg := mag.testBit (Shadow7.sbP (start j) + i.val) ^^ sign
        out.basis (Shadow7.a0P (start j) - 1 + i.val) = (if G then neg else pos) ∧
        out.basis (Shadow7.b0P (start j) - 1 + i.val) = (if G then pos else neg)) ∧
      ∀ i : Nat, i < railP (start j + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j)) →
        out.basis (Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 + i) = (a.u+a.v).testBit (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + i) := by
  intro a sign mag next out
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  obtain ⟨hd, hB, hP, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := Relocated.chain_geo w1 w3
  have whole := Whole.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode
    events nextSmall bound xs len historyOK first saved far side
  have store := StoreMapped.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound
  have before := BeforeStore.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par
    mode events nextSmall bound
  have coords := StoreCoordinates.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero
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
  have untouched (q : Nat) (hq : q < 803 + Shadow7.sbP (start j + 15)) (hq2 : start j + 15 ≤ q) :
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
theorem leave_keeps (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Wire) (hq : ¬ Shadow7.leaveBox2 (start j) q) (m : List Bool) (s : State) :
    (run (Shadow7.leaveP j) m s).basis q = s.basis q := by
  apply LeaveReadoutFrame.preserved
  unfold Shadow7.leaveP
  rw [dest_forward]
  intro hmem
  obtain ⟨g, hg, e⟩ := List.mem_map.mp hmem
  exact hq (e ▸ Shadow7.leaveOps_box2 j h0 (by omega) g hg (target g) (by rw [GateMirror.Gate.wires_eq]; simp))

/-- The same for the StoreMapped prefix (`Shadow7.leaveHeadOps ++ Shadow7.leaveMidOps`). -/
theorem storeMapped_keeps (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Wire) (hq : ¬ Shadow7.leaveBox2 (start j) q) (m : List Bool) (s : State) :
    (run (StoreMapped.program j) m s).basis q = s.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [StoreMapped.program_eq j, dest_forward]
  intro hmem
  obtain ⟨g, hg, e⟩ := List.mem_map.mp hmem
  have hg' : g ∈ Shadow7.leaveOps (start j) := by rw [Shadow7.leaveOps_split]; exact List.mem_append_left _ hg
  exact hq (e ▸ Shadow7.leaveOps_box2 j h0 (by omega) g hg' (target g) (by rw [GateMirror.Gate.wires_eq]; simp))

/-- The small companion registers sit inside the core checkpoint's cleared sites. -/
theorem smallC_targets (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) : ∀ q ∈ LeaveJ7.smallC j, q ∈ CoreCheckpoint.targets j := by
  intro q hq
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  simp only [LeaveJ7.smallC, List.mem_map, List.mem_range] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  simp only [CoreCheckpoint.targets, List.mem_append]
  left; left; left
  exact List.mem_range'_1.mpr ⟨by omega, by unfold Shadow7.lowsP at hi; unfold Shadow7.sbP at *; omega⟩

theorem smallM_mag (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) : ∀ q ∈ LeaveJ7.smallM j, q ∈ CoreCheckpoint.magSites j := by
  intro q hq
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  simp only [LeaveJ7.smallM, List.mem_map, List.mem_range] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  simp only [CoreCheckpoint.magSites, LeaveJ7.fullM, List.mem_map, List.mem_range]
  exact ⟨i, by unfold Shadow7.lowsP at hi; unfold Shadow7.sbP at *; omega, rfl⟩

/-- Margin 16: G4 (`borrowG4`, between the core checkpoint and the restore) writes only 1557 / 1558; the row frees,
the core-checkpoint targets and the companion registers avoid both. -/
theorem row_off58 (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (k : Fin 17) :
    (LeaveJ7.row j k).free ≠ 1557 ∧ (LeaveJ7.row j k).free ≠ 1558 := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  obtain ⟨k, hk⟩ := k
  have e : (LeaveJ7.row j ⟨k, hk⟩).free =
      if k < Shadow7.lowsP (start j) then Shadow7.bankW (start j) k else Shadow7.a0P (start j) - 1 + k := by
    simp only [LeaveJ7.row, LeaveJ7.cols, Shadow7.columnsP, HighBankJoin.Column.free, List.getElem_map, List.getElem_range]
    by_cases h : k < Shadow7.lowsP (start j) <;> simp [h]
  rw [e]
  split_ifs with hl
  · rcases Shadow7.bank_cases w1 w2 (i := k) (by omega) with ⟨_, e1⟩ | ⟨_, _, e1, _, _⟩ | ⟨_, e1, _⟩ <;>
      constructor <;> ((try unfold Wire at *); omega)
  · constructor <;> ((try unfold Wire at *); omega)

theorem targets_off58 (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Wire) (mem : q ∈ CoreCheckpoint.targets j) :
    q ≠ 1557 ∧ q ≠ 1558 := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  have e6 := e0P_gt_1615 j h1
  simp only [CoreCheckpoint.targets, List.mem_append, List.mem_map] at mem
  rcases mem with ((scr | ⟨k, _, rfl⟩) | raw) | mag
  · obtain ⟨lo, hi⟩ := List.mem_range'_1.mp scr
    constructor <;> ((try unfold Wire at *); omega)
  · exact row_off58 j h0 h1 k
  · have r := CoreCheckpoint.raw_range j q raw
    constructor <;> ((try unfold Wire at *); omega)
  · simp only [CoreCheckpoint.magSites, LeaveJ7.fullM, List.mem_map, List.mem_range] at mag
    obtain ⟨k, hk, rfl⟩ := mag
    constructor <;> ((try unfold Wire at *); omega)

theorem smallC_off58 (j : Fin 26) (q : Wire) (hq : q ∈ LeaveJ7.smallC j) : q ≠ 1557 ∧ q ≠ 1558 := by
  simp only [LeaveJ7.smallC, List.mem_map, List.mem_range] at hq
  obtain ⟨i, _, rfl⟩ := hq
  constructor <;> ((try unfold Wire at *); omega)

theorem smallM_off58 (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Wire) (hq : q ∈ LeaveJ7.smallM j) :
    q ≠ 1557 ∧ q ≠ 1558 := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have rr := Shadow7.rail_win w1 w2
  simp only [LeaveJ7.smallM, List.mem_map, List.mem_range] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  constructor <;> ((try unfold Wire at *); omega)

/-- dadon's `zerosAt`/`coreDone`: after the full arithmetic, every core-checkpoint target outside `smallM` is clean. -/
theorem core_done (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
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
    (mem : q ∈ CoreCheckpoint.targets j) (notM : q ∉ LeaveJ7.smallM j)
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    (run (FullArithmetic.program j) m s).basis q = false := by
  have h := CoreCheckpoint.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
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
  rw [FullArithmetic.restoreShape j, run_append, run_take, hc, run_append]
  generalize hg : run (LeaveJ7.borrowG4 j) ((m.drop (measurementCount (CoreCheckpoint.program j))).take
    (measurementCount (LeaveJ7.borrowG4 j))) c = g
  have gq (q : Wire) (n : q ≠ 1557 ∧ q ≠ 1558) : g.basis q = c.basis q := by
    rw [← hg]; simp [LeaveJ7.borrowG4, run, writeBit, Function.update_apply, n.1, n.2]
  have cleanG : ∀ q ∈ LeaveJ7.smallC j, g.basis q = false := fun q hq => (gq q (smallC_off58 j q hq)).trans (cleanCs q hq)
  have clearG : regValue (LeaveJ7.smallM j) g.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (gq q (smallM_off58 j h0 h1 q hq)).trans (h.2.2.2 q (smallM_mag j h0 (by omega) q hq)))
  have rest := LeaveJ7.restore_run j h0 (by omega) g ((m.drop (measurementCount (CoreCheckpoint.program j))).drop
    (measurementCount (LeaveJ7.borrowG4 j))) cleanG clearG
  rw [rest.2.1 _ notM, gq q (targets_off58 j h0 h1 q mem)]
  exact zerosAt q mem

/-- The free word columns are clean after the full arithmetic (HighZero's lower words). -/
theorem row_done (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
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
      s.basis (LeaveJ7.swaps j i) = decide (i = LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z))) (k : Fin 17) (notM : (LeaveJ7.row j k).free ∉ LeaveJ7.smallM j)
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    (run (FullArithmetic.program j) m s).basis (LeaveJ7.row j k).free = false := by
  have h := CoreCheckpoint.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  dsimp only at h
  generalize hc : run (CoreCheckpoint.program j) m s = c at h
  have cleanCs : ∀ q ∈ LeaveJ7.smallC j, c.basis q = false := by
    intro q hq
    obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
    have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
    have rr := Shadow7.rail_win w1 w2
    simp only [LeaveJ7.smallC, List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact h.1 ⟨i, by omega⟩
  have clearM : regValue (LeaveJ7.smallM j) c.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => h.2.2.2 q (smallM_mag j h0 (by omega) q hq))
  rw [FullArithmetic.restoreShape j, run_append, run_take, hc, run_append]
  generalize hg : run (LeaveJ7.borrowG4 j) ((m.drop (measurementCount (CoreCheckpoint.program j))).take
    (measurementCount (LeaveJ7.borrowG4 j))) c = g
  have gq (q : Wire) (n : q ≠ 1557 ∧ q ≠ 1558) : g.basis q = c.basis q := by
    rw [← hg]; simp [LeaveJ7.borrowG4, run, writeBit, Function.update_apply, n.1, n.2]
  have cleanG : ∀ q ∈ LeaveJ7.smallC j, g.basis q = false := fun q hq => (gq q (smallC_off58 j q hq)).trans (cleanCs q hq)
  have clearG : regValue (LeaveJ7.smallM j) g.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (gq q (smallM_off58 j h0 h1 q hq)).trans (h.2.2.2 q (smallM_mag j h0 (by omega) q hq)))
  have rest := LeaveJ7.restore_run j h0 (by omega) g ((m.drop (measurementCount (CoreCheckpoint.program j))).drop
    (measurementCount (LeaveJ7.borrowG4 j))) cleanG clearG
  rw [rest.2.1 _ notM, gq _ (row_off58 j h0 h1 k)]
  exact h.2.1 k

theorem row_free (j : Fin 26) (i : Nat) (hi : i < 17) :
    (LeaveJ7.row j ⟨i, hi⟩).free = if i < Shadow7.lowsP (start j) then Shadow7.bankW (start j) i else Shadow7.a0P (start j) - 1 + i := by
  simp only [LeaveJ7.row, LeaveJ7.cols, Shadow7.columnsP, HighBankJoin.Column.free, List.getElem_map, List.getElem_range]
  by_cases h : i < Shadow7.lowsP (start j) <;> simp [h]

theorem not_low (j : Fin 26) (q : Wire)
    (h : (q < Shadow7.a0P (start j) - 1 ∨ Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 ≤ q) ∧ (q < Shadow7.b0P (start j) - 1 ∨ Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 ≤ q)) :
    q ∉ RailPair.sites (Close.low j) := by
  intro hm
  obtain ⟨i, hi, e⟩ := (Close.mem_low_sites j q).mp hm
  have ha : 1 ≤ Shadow7.a0P (start j) := by unfold Shadow7.a0P; omega
  have hb : 1 ≤ Shadow7.b0P (start j) := by unfold Shadow7.b0P; omega
  unfold Wire at *
  omega

theorem not_history (j : Fin 26) (q : Wire) (h : q < start j + 16 ∨ start j + 30 < q) : q ∉ Close.history j := by
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
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
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
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.liveW (start j)))
    (far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
    (side : s.basis (Shadow7.e0P (start j) + 4) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u))) (g0 s0 : Bool)
    (record : IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)) :
    let out := run (Shadow7.leaveP j) m s
    let cells := IntegerPacket.readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)
    cells = SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v) ∧
      out.basis (Shadow7.e0P ((start j) + 15) + 6) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      out.basis (Shadow7.e0P ((start j) + 15) + 7) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && afterFlags (decide (z.v < z.u)) (cells.take 5)) ∧
      out.basis (Shadow7.e0P ((start j) + 15) + 8) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && HighBankSum.crossBit (LeaveJ7.TrueMiddle.d j z)) := by
  let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par := RecordedParity.result j h0 (by omega) s z g0 s0 small odd record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [far, side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j h0 (by omega) s z g0 s0 small odd record
  have flag := RecordedEvents.glueFlag j h0 (by omega) s z g0 s0 small odd record far side
  have all := Whole.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ small odd) (LeaveJ7.Far.firstSwap _ _ _ _ small odd) ev.1 far side
  have words := EndWords.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ small odd) (LeaveJ7.Far.firstSwap _ _ _ _ small odd) ev.1 far side
  have kept := (PreservedRecords.result j h0 (by omega) s m words.2.2.2.1).trans record
  refine ⟨kept, all.2.1, ?_, all.2.2.2.1⟩
  rw [kept, all.2.2.1]
  by_cases active : Shadow.far (Shadow7.sbP (start j)) 15 z
  · rw [LeaveJ7.Far.orient _ _ small active]
  · simp [active]

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.ActualHistory

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
/-- `measureX` writes 0 whatever the outcome and corrections only touch the phase: basis bits never depend on the tape. -/
theorem run_basis_any (p : Program) : ∀ (m n : List Bool) (s s' : State), s.basis = s'.basis →
    (run p m s).basis = (run p n s').basis := by
  induction p with
  | nil => intro m n s s' h; exact h
  | cons i p ih =>
    intro m n s s' h
    cases i <;> simp only [run, measureAndCorrect] <;> apply ih <;> simp [correct_basis, h]
theorem basis_tape (gs : List GateMirror.Gate) (m : List Bool) (s : State) :
    (run (GateMirror.forward gs) m s).basis = (run (GateMirror.forward gs) [] s).basis :=
  run_basis_any _ m [] s s rfl
end ECDSAAdd.Entrant.StairPacket.LeaveJ7

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
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
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
    (top : ∀ q : Nat, Shadow7.a0P (start j) + 16 ≤ q → q ≤ (start j) + 30 + railP ((start j) + 15) → s.basis q = false)
    (topCarry : s.basis (Shadow7.e0P (start j) - 1) = false) (top2 : s.basis (Shadow7.e0P (start j) - 2) = false)
    (nextSmall : Shadow7.SmallIfFar (Shadow7.sbP ((start j) + 15)) 15 (step^[15] z) ∧ Shadow7.EndSmall (Shadow7.sbP (start j)) z)
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.liveW (start j)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    ∀ i : Fin (railP ((start j) + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j))),
      (run (StoreMapped.program j) m s).basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val) = false := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have hR : railP ((start j) + 15) ≤ 258 := by unfold railP; split_ifs <;> omega
  have store := (StoreMapped.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have bflag := (BeforeStore.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2.2.2.2
  intro i
  have hi := i.isLt
  by_cases ext : Shadow7.a0P (start j) + 16 ≤ Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val
  · by_cases rel : Shadow7.a0P (start j) + 17 ≤ Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val ∧
        Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val < Shadow7.a0P (start j) + 17 + min 4 (Shadow7.wpP (start j) + start j - 448)
    · -- block 22's relocated pool wires (a0P+17 ..): the adjust returns them to 0 (MAC's relocated_clean)
      have atCore := CoreCheckpoint.result (flag := flag) j h0 (by omega) s [] z G sg small ready fresh scratch temp odd room clean padding bank zero
        par mode events
      have core := CoreCheckpoint.oracle j h0 h1 s _ atCore.1 atCore.2.2.1
        (native_carryJ_lt j h0 h1 _ s ready 1613 (by decide) (Nat.lt_trans (by decide) (e0P_gt_1615 j h1)))
        (native_carryJ_lt j h0 h1 _ s ready 1614 (by decide) (e0P_gt_1615 j h1))
      have cc := Admission.carries_cover j h0 (by omega) s clean
      rw [StoreMapped.program_eq j, basis_tape]
      exact Shadow7.relocated_clean j h0 (by omega) s (native_carryJ j h0 (by omega) _ s ready topCarry top2) cc.1 cc.2 core (fun k hk => atCore.2.2.2 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩))
        (CoreCheckpoint.free58 j h0 (by omega) s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par
          mode events flag) _ rel.1 rel.2
    · rw [storeMapped_keeps j h0 (by omega) (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val) (by unfold Shadow7.leaveBox2; ((try unfold Wire at *); omega))]
      exact top _ ext (by ((try unfold Wire at *); omega))
  · have lim : Shadow7.lowsP (start j) + i.val < 17 := by omega
    have free : (LeaveJ7.row j ⟨Shadow7.lowsP (start j) + i.val, lim⟩).free = Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val := by
      rw [row_free, if_neg (by omega)]; ((try unfold Wire at *); omega)
    rw [store (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val) (not_low j _ (by ((try unfold Wire at *); omega))) (not_history j _ (by ((try unfold Wire at *); omega))),
      bflag (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val) (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))]
    rw [← free]
    exact row_done (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events ⟨Shadow7.lowsP (start j) + i.val, lim⟩ (by
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
theorem lowFrame (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (i : Fin (Shadow7.sbP (start j))) (s : State) (m : List Bool) :
    let v := run (Shadow7.leaveP j) m s
    v.basis ((start j) + 31 + i.val) = s.basis ((start j) + 31 + i.val) ∧ v.basis (786 + i.val) = s.basis (786 + i.val) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have hi := i.isLt
  exact ⟨leave_keeps j h0 (by omega) _ (by unfold Shadow7.leaveBox2; ((try unfold Wire at *); omega)) m s,
    leave_keeps j h0 (by omega) _ (by unfold Shadow7.leaveBox2; ((try unfold Wire at *); omega)) m s⟩

/-- `LeaveSignedCoordinates.sharedDigit` for a congruence mod `2^b` (margin 16: `retainedLow_shadow7` is mod `2^sb`). -/
theorem sharedDigitLow (x y b i : Nat) (modEq : x % 2^b = y % 2^b) (hi : i < b) : x.testBit i = y.testBit i := by
  have h := congrArg (Nat.testBit · i) modEq
  simpa only [Nat.testBit_mod_two_pow, decide_eq_true_eq.mpr hi, Bool.true_and] using h

/-- dadon's `Leave{s}BoundaryRails.result`: after the leave, the next tick's rails read the stock reference. -/
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
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
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.liveW (start j))) (xs : List (Bool × Bool)) (len : xs.length = 15)
    (historyOK : Shadow.far (Shadow7.sbP (start j)) 15 z → StairArchiveTrace.chain (decide (2^(Shadow7.sbP (start j)) ≤ z.u)) xs)
    (first : Shadow.far (Shadow7.sbP (start j)) 15 z → decide (2^(Shadow7.sbP (start j)) ≤ z.u) = false →
      ∀ i (h : i < xs.length), i ≤ IntegerHigh.wait 15 z.u → xs[i].2 = decide (i = IntegerHigh.wait 15 z.u))
    (saved : (Close.events j).map (fun p => s.basis p.1) = (xs.take 5).map Prod.snd)
    (far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
    (side : s.basis (Shadow7.e0P (start j) + 4) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u)))
    (highZero : ∀ q : Nat, Shadow7.a0P (start j) + 16 ≤ q → q ≤ (start j) + 30 + railP ((start j) + 15) → s.basis q = false)
    (topCarry : s.basis (Shadow7.e0P (start j) - 1) = false) (top2 : s.basis (Shadow7.e0P (start j) - 2) = false)
    (raw : State) (input : let a := step^[15] z
       SkywalkIntegerInput (WideWords.L j) (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis)
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    let o := pullState (OB5.sig ((start j) + 14)) raw
    let out := run (Shadow7.leaveP j) m s
    (∀ i : Fin (Shadow7.sbP (start j) + Shadow7.lowsP (start j)), out.basis ((start j) + 31 + i.val) = o.basis ((start j) + 31 + i.val) ∧
      out.basis (786 + i.val) = o.basis (786 + i.val)) ∧
    ∀ i : Fin (railP ((start j) + 15) - (Shadow7.sbP (start j) + Shadow7.lowsP (start j))), out.basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val) = false ∧
      out.basis (Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 + i.val) =
        (if o.basis ((start j) + 30) then o.basis (Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 + i.val) else o.basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val)) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have hR : Shadow7.sbP (start j) + Shadow7.lowsP (start j) ≤ railP ((start j) + 15) := by ((try unfold Wire at *); omega)
  let a := step^[15] z
  let h := step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)
  let o := pullState (OB5.sig ((start j) + 14)) raw
  have word := EndWords.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have whole := Whole.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have cleared := HighZero.result (flag := flag) (top2 := top2) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events highZero topCarry nextSmall bound
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
      have spos := sharedDigitLow _ _ (Shadow7.sbP (start j)) i.val law.2.1 low
      have smag := sharedDigitLow _ _ (Shadow7.sbP (start j)) i.val law.2.2 low
      dsimp only at ref hw
      rw [law.1, spos, smag] at ref
      exact ⟨untouched.1.trans (hw.1.trans ref.1.symm), untouched.2.trans (hw.2.trans ref.2.symm)⟩
    · have hk : i.val - Shadow7.sbP (start j) < Shadow7.lowsP (start j) := by have := i.isLt; omega
      have vals := word.2.2.2.2.1 ⟨i.val - Shadow7.sbP (start j), hk⟩
      dsimp only at ref vals
      rw [show Shadow7.sbP (start j) + (i.val - Shadow7.sbP (start j)) = i.val by omega,
        show Shadow7.a0P (start j) - 1 + (i.val - Shadow7.sbP (start j)) = (start j) + 31 + i.val by omega,
        show Shadow7.b0P (start j) - 1 + (i.val - Shadow7.sbP (start j)) = 786 + i.val by omega] at vals
      exact ⟨vals.1.trans ref.1.symm, vals.2.trans ref.2.symm⟩
  · intro i
    have hi := i.isLt
    have ref := WideWords.wide j h0 (by omega) a G sg raw input ⟨Shadow7.sbP (start j) + Shadow7.lowsP (start j) + i.val, by omega⟩
    dsimp only at ref
    rw [show (start j) + 31 + (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + i.val) = Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val by omega,
      show 786 + (Shadow7.sbP (start j) + Shadow7.lowsP (start j) + i.val) = Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 + i.val by omega] at ref
    have free : (run (Shadow7.leaveP j) m s).basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val) = false := by
      rw [whole.2.2.2.2, (Relocated.upperMap j h0 (by omega) i.val hi).2]
      exact (Function.update_of_ne (by ((try unfold Wire at *); omega)) _ _).trans (cleared i)
    refine ⟨free, ?_⟩
    change (run (Shadow7.leaveP j) m s).basis (Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 + i.val) =
      (if o.basis ((start j) + 30) then o.basis (Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 + i.val) else o.basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val))
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
def zeros (j : Fin 26) : List Nat :=
  List.range' 1556 (Shadow7.e0P ((start j) + 15) + 3 - 1556) ++
  List.range' (Shadow7.e0P ((start j) + 15) + 9) (min 1813 (2055 - (start j)) - (Shadow7.e0P ((start j) + 15) + 9)) ++
  List.range' (bTopP ((start j) + 15) + 1) (bTopP (start j) - bTopP ((start j) + 15))

/-- dadon's `retired` (255/210: plus the live bank sites above the next rail, `F < 2^(R(s+15)-sb)`). -/
def retired (j : Fin 26) (q : Nat) : Prop :=
  q = Shadow7.e0P (start j) + 4 ∨ (q ≠ Shadow7.e0P (start j) + 4 ∧ q ∉ RailPair.sites (Close.low j) ∧ q ∉ Close.history j ∧
  (q = 1556 ∨ (q ≠ 1556 ∧ q ≠ 1557 ∧ q ≠ 1558 ∧
   ((q ∈ CoreCheckpoint.targets j ∧ q ∉ LeaveJ7.smallM j) ∨
    ∃ i : Fin (railP (start j) - railP ((start j) + 15)), q = LeaveJ7.live j (Shadow7.wpP (start j) + 15 - (railP (start j) - railP ((start j) + 15)) + i.val)))))

/-- Core-checkpoint targets by intervals (scratch, raw sites, the bank head `e0..e0+2`, the B words). -/
theorem mem_targets (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Nat)
    (h : (1559 ≤ q ∧ q < 1598) ∨ (1613 ≤ q ∧ q < Shadow7.e0P (start j) + 3) ∨ (Shadow7.e0P (start j) + 8 ≤ q ∧ q < min 1813 (2055 - (start j))) ∨
      (Shadow7.b0P (start j) ≤ q ∧ q < Shadow7.b0P (start j) + 14 + Shadow7.lowsP (start j))) : q ∈ CoreCheckpoint.targets j := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  simp only [CoreCheckpoint.targets, CoreCheckpoint.rawSites, CoreCheckpoint.magSites, LeaveJ7.fullM, List.mem_append,
    List.mem_range'_1, List.mem_map, List.mem_range, List.mem_finRange, true_and, List.mem_singleton]
  rcases h with h | h | h | h
  · left; left; left; exact ⟨h.1, by first | omega | (unfold Wire; omega)⟩
  · by_cases lo : q < Shadow7.e0P (start j)
    · left; right; left; left; exact ⟨h.1, by first | omega | (unfold Wire; omega)⟩
    · left; left; right
      refine ⟨⟨q - Shadow7.e0P (start j), by first | omega | (unfold Wire; omega)⟩, ?_⟩
      rw [row_free, if_pos (by first | omega | (unfold Wire; omega))]; unfold Shadow7.bankW; rw [if_pos (by first | omega | (unfold Wire; omega))]; first | omega | (unfold Wire; omega)
  · left; right; left; right; exact ⟨h.1, by first | omega | (unfold Wire; omega)⟩
  · by_cases lo : q < Shadow7.b0P (start j) + 16
    · right; exact ⟨q - Shadow7.b0P (start j), by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩
    · by_cases p17 : q = Shadow7.b0P (start j) + 16
      · left; right; right; exact p17
      · left; left; right
        refine ⟨⟨q - Shadow7.b0P (start j) - 14, by first | omega | (unfold Wire; omega)⟩, ?_⟩
        rw [row_free, if_pos (by first | omega | (unfold Wire; omega))]; unfold Shadow7.bankW; rw [if_neg (by first | omega | (unfold Wire; omega)), if_pos (by first | omega | (unfold Wire; omega))]
        (first | omega | (unfold Wire; omega))

/-- A retired wire by intervals. -/
theorem retired_of (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Nat)
    (h : (1559 ≤ q ∧ q < 1598) ∨ (1613 ≤ q ∧ q < Shadow7.e0P (start j) + 3) ∨ (Shadow7.e0P (start j) + 8 ≤ q ∧ q < min 1813 (2055 - (start j))) ∨
      (Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 ≤ q ∧ q < Shadow7.b0P (start j) + 14 + Shadow7.lowsP (start j))) : retired j q := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have hne : q ≠ Shadow7.e0P (start j) + 4 := by (first | omega | (unfold Wire; omega))
  refine Or.inr ⟨hne, not_low j q (by (first | omega | (unfold Wire; omega))), not_history j q (by (first | omega | (unfold Wire; omega))),
    Or.inr ⟨by (first | omega | (unfold Wire; omega)), by (first | omega | (unfold Wire; omega)), by (first | omega | (unfold Wire; omega)),
      Or.inl ⟨mem_targets j h0 (by omega) q (by (first | omega | (unfold Wire; omega))), ?_⟩⟩⟩
  simp only [LeaveJ7.smallM, List.mem_map, List.mem_range, not_exists, not_and]
  intro k hk e; (first | omega | (unfold Wire; omega))

/-- dadon's `routed` (a kernel decide per block), from the relocation closed form. -/
theorem routed (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) : ∀ (Q : Nat), Q ∈ zeros j → retired j (LeaveRelocation.source (Relocated.moves j) Q) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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
    by_cases pool : 1598 ≤ q ∧ q < 1598 + (Shadow7.wpP ((start j) + 15) - 2) - (Shadow7.wpP (start j) - Shadow7.lowsP (start j))
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
    have e : q = Shadow7.bankW (start j) (Shadow7.lowsP (start j) + (q - (803 + Shadow7.sbP ((start j) + 15) + 15))) := by
      rw [show Shadow7.bankW (start j) (Shadow7.lowsP (start j) + (q - (803 + Shadow7.sbP ((start j) + 15) + 15))) =
        (Relocated.bankPair (start j) (q - (803 + Shadow7.sbP ((start j) + 15) + 15))).1 from rfl, hB _ (by first | omega | (unfold Wire; omega))]
      first | omega | (unfold Wire; omega)
    rw [e, Relocated.src_top _ w1 w3 (q - (803 + Shadow7.sbP ((start j) + 15) + 15)) (by first | omega | (unfold Wire; omega)) (fun h => by first | omega | (unfold Wire; omega))]
    exact retired_of j h0 (by omega) _ (Or.inr (Or.inr (Or.inr ⟨by first | omega | (unfold Wire; omega), by first | omega | (unfold Wire; omega)⟩)))

/-- dadon's `Leave{s}BoundaryClean.result`: the leave hands back a clean scratch. `narrow` is
`LeaveJ7.terminal_fit` (dadon 210/255 only; implied by `bound` when the rail keeps its width). -/
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
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
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.liveW (start j))) (xs : List (Bool × Bool)) (len : xs.length = 15)
    (historyOK : Shadow.far (Shadow7.sbP (start j)) 15 z → StairArchiveTrace.chain (decide (2^(Shadow7.sbP (start j)) ≤ z.u)) xs)
    (first : Shadow.far (Shadow7.sbP (start j)) 15 z → decide (2^(Shadow7.sbP (start j)) ≤ z.u) = false →
      ∀ i (h : i < xs.length), i ≤ IntegerHigh.wait 15 z.u → xs[i].2 = decide (i = IntegerHigh.wait 15 z.u))
    (saved : (Close.events j).map (fun p => s.basis p.1) = (xs.take 5).map Prod.snd)
    (far : s.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
    (side : s.basis (Shadow7.e0P (start j) + 4) = (decide (Shadow.far (Shadow7.sbP (start j)) 15 z) && decide (2^(Shadow7.sbP (start j)) ≤ z.u)))
    (quiet : ∀ q ∈ CoreCheckpoint.rawSites j, s.basis q = false)
    (narrow : LeaveJ7.TrueMiddle.F j z < 2^(railP ((start j) + 15) - Shadow7.sbP (start j)))
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    ∀ q ∈ zeros j, (run (Shadow7.leaveP j) m s).basis q = false := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have hR : railP ((start j) + 15) ≤ railP (start j) := by unfold railP; split_ifs <;> first | omega | (unfold Wire; omega)
  have whole := Whole.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store := (StoreMapped.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags := BeforeStore.result (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
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
        (core_done (flag := flag) j h0 (by omega) s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events quiet _ mem notM)
    · have hi := i.isLt
      rw [eq, flags.2.2.2.2.2.1 (Shadow7.wpP (start j) + 15 - (railP (start j) - railP ((start j) + 15)) + i.val) (by first | omega | (unfold Wire; omega))]
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le narrow (Nat.pow_le_pow_right (by decide) (by first | omega | (unfold Wire; omega)))

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.BoundaryClean

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.AssembleCut
/-- TEMP copy of par-c2's generic `Leave{s}AssembleCut.leftovers` (agreed 23:30Z); delete when par-c2's lands. -/
def leftovers (j : Fin 26) (q : Wire) : Prop :=
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
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (x p : Nat) (good : Bounds x p) (raw s : State) (m : List Bool) (g sg : Bool)
    (domain : Domain (start j) x p raw)
    (input : InputAt (start j) (encode g sg (unsigned (start j) x p).u (unsigned (start j) x p).v) raw)
    (record : Shadow7.physicalCells j s = SkywalkTrace.trace 15 (encode g sg (unsigned (start j) x p).u (unsigned (start j) x p).v))
    (kept : Shadow7.physicalCells j (run (Shadow7.leaveP j) m s) = Shadow7.physicalCells j s)
    (extra : ∀ q : Wire, ReleasedOrigin.releasedSite j q → (run (Shadow7.leaveP j) m s).basis q = (origin (start j) raw s).basis q) :
    ∀ q, AssembleCut.leftovers j q → (run (Shadow7.leaveP j) m s).basis q = (origin (start j) raw s).basis q := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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
theorem agree (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (x p : Nat) (good : Bounds x p) (raw v : State) (dom : Domain (start j) x p raw) (m : List Bool)
    (pre : ∀ q : Wire, (railP ((start j) + 15) < railP (start j) ∧ q = (start j) + 31 + railP ((start j) + 15)) ∨ (1301 ≤ q ∧ q ≤ 1058 + (start j)) ∨
      (369 ≤ start j ∧ 1302 ≤ q + start j ∧ q ≤ 933) → v.basis q = false)
    (clear : ∀ q ∈ BoundaryClean.zeros j, (run (Shadow7.leaveP j) m v).basis q = false) :
    ∀ q : Wire, ReleasedOrigin.releasedSite j q → (run (Shadow7.leaveP j) m v).basis q = (origin (start j) raw v).basis q := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
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

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission


end


/- Inlined from ShadowLeaveMove; provenance retained from022799f6. -/
section

/-! Shadow7 move leave (leave-move): c9cc6a76's leaveMove on the generic shadow leave, blocks 1..20 (`j ≤ 20`, as the
LeaveJ7 core). Generated from the stock blocks by helpers/shadow-leave/scripts/port.py (ONLY=W:20905-21130), then edited by
leave-move (footprint via `Shadow7.leaveOps_box2` from ShadowBox2). -/

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror RecordedQuantum HighBankFirstHit LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem moveA_split (s : Nat) : Shadow7.moveA s =
    entryOps s ++ ((leaveFix3 s (Shadow7.sbP s) ++ leaveFix4 s (Shadow7.sbP s)) ++ (Shadow7.fix5P s (Shadow7.sbP s)).take 27) := by
  unfold Shadow7.moveA entryOps; simp only [List.append_assoc]

theorem fullPrefix_split (j : Fin 26) : fullPrefix j =
    ((leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j))) ++
      (Shadow7.fix5P (start j) (Shadow7.sbP (start j))).take 27) ++ (Shadow7.fix5P (start j) (Shadow7.sbP (start j))).drop 27 := by
  unfold fullPrefix; rw [List.append_assoc _ ((Shadow7.fix5P _ _).take 27), List.take_append_drop]

/-- In front of the mux: the crossing wire is still clean (nothing in the selector prefix writes it). -/
theorem prefix302_targets (s h : Nat) : ((leaveFix3 s h ++ leaveFix4 s h) ++ (Shadow7.fix5P s h).take 27).map target =
    [1559, 1560, 1560, 1561, 1560, 1562, 1560, 1563, 1560, 1564, 1560, 1565, 1560, 1566, 1560, 1567, 1560, 1568, 1560,
     1569, 1560, 1570, 1560, 1571, 1560, 1572, 1560, 1573, 1560, 1574, 1560, 1575, 1560,
     h+1581, h+1581, h+1581, h+1581, h+1581, h+1581, 1576, 1576,
     1577, 1578, 1578, 1579, 1580, 1580, 1581, 1582, 1582, 1583, 1584, 1584,
     1585, 1586, 1586, 1587, 1588, 1588, 1589] := rfl

theorem cross_kept (s h : Nat) (hh : 16 ≤ h) (q : Wire) (hq : q = h + 1580) (st : State) (o : List Bool) :
    (run (GateMirror.forward ((leaveFix3 s h ++ leaveFix4 s h) ++ (Shadow7.fix5P s h).take 27)) o st).basis q =
      st.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward, prefix302_targets]
  subst hq
  intro hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  (try unfold Wire at *)
  omega

/-- Behind the mux: the rest of the selector never writes a tag. -/
theorem tags_kept (s h : Nat) (i : Nat) (hi : i < 16) (st : State) (o : List Bool) :
    (run (GateMirror.forward ((Shadow7.fix5P s h).drop 27)) o st).basis (tagsP.getD i 0) = st.basis (tagsP.getD i 0) := by
  have t := tags_range i hi
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  simp only [Shadow7.fix5P, List.drop, List.map_cons, List.map_nil, target, List.mem_cons, List.not_mem_nil, or_false]
  unfold Wire at *
  omega

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission
open Arithmetic Partial GateMirror LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- At the leave input, in front of the mux (gate 302 of every tape): the crossing wire is clean and the hot tags
all select the join cell of the actual key. -/
theorem Inputs.hot {j : Fin 26} (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) {s : State} {z : SkywalkNat.State}
    {g0 s0 : Bool} (h : Inputs j s z g0 s0) (o : List Bool) :
    (run (GateMirror.forward (Shadow7.moveA (start j))) o s).basis (Shadow7.e0P (start j) + 6) = false ∧
    ∀ r ∈ Shadow7.moveRows (start j), (run (GateMirror.forward (Shadow7.moveA (start j))) o s).basis r.1 = true →
      r.2 = Shadow7.a0P (start j) - 1 + key (actualMode (Shadow7.sbP (start j)) z) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have rr := Shadow7.rail_win w1 w2
  let u := flags z g0 s0
  have mode : actualMode (Shadow7.sbP (start j)) z = farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j h0 h1 s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  let A0 := GateMirror.forward (entryOps (start j))
  let o0 := o.take (measurementCount A0)
  let n := o.drop (measurementCount A0)
  let en := run A0 o0 s
  have watchedOK := frontReady_frame j h0 h1 s o0 z u.1 u.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0) (LeaveJ7.glueBound j z u.2 ⟨h.farSmall, h.endSmall⟩)
    (LeaveJ7.RecordedEvents.glueFlag j h0 h1 s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side)
  have zeroE : ∀ q ∈ watched j, en.basis q = false := fun q hq => (watchedOK q hq).trans (h.zero q hq)
  have base : ∀ q : Nat, 1561 ≤ q → q ≤ 1597 → en.basis q = false := by
    intro q lo hi
    apply zeroE
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q - 1559, by omega, by omega⟩
  have z59 : en.basis 1559 = false := zeroE _ (by simp [watched])
  have z60 : en.basis 1560 = false := zeroE _ (by simp [watched])
  have zc : en.basis (ports j).crossing = false := zeroE _ (by simp [watched, ports])
  have zn : en.basis (ports j).near = false := zeroE _ (by simp [watched, ports])
  have kept (q : Nat) (ok : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 16) ∨
      (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 16) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨
      (1556 ≤ q ∧ q ≤ 1575) ∨ q = Shadow7.e0P (start j) + 5)) : en.basis q = s.basis q :=
    entry_keep j h0 h1 q ok s o0
  let k := actualMode (Shadow7.sbP (start j)) z
  have modeE : k = farMode (en.basis (Shadow7.e0P (start j) + 3)) (en.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [kept _ (by omega), kept _ (by omega)]; exact mode
  have eventsE : right k = true → ∀ i < 15, i ≤ key k → en.basis (swaps j i) = decide (i = key k) := by
    intro on i hi hq
    have sw := swaps_exact j h0 h1 i hi
    exact (kept _ (by unfold Wire at *; omega)).trans (ev.2 on i hi hq)
  have sel := selected j h0 h1 en n en.basis z.u k modeE z59 z60 (beforeFresh _ _ _ base zc zn) eventsE
  -- the state in front of the mux
  have split : run (GateMirror.forward (Shadow7.moveA (start j))) o s =
      run (GateMirror.forward ((leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j))) ++
        (Shadow7.fix5P (start j) (Shadow7.sbP (start j))).take 27)) n en := by
    rw [moveA_split, forward_app, run_append]
  rw [split]
  refine ⟨?_, ?_⟩
  · rw [cross_kept (start j) (Shadow7.sbP (start j)) (by omega) _ (by (try unfold Wire at *); unfold Shadow7.e0P; omega)]
    exact zc
  · intro r hr on
    obtain ⟨i, hi, rfl⟩ := Shadow7.mem_moveRows hr
    have tg := sel ⟨i, hi⟩
    rw [fullPrefix_split, forward_app, run_append, run_take, tags_kept _ _ i hi] at tg
    simp only at on
    rw [on] at tg
    have e := (Bool.and_eq_true_iff.mp tg.symm).2
    simp only [decide_eq_true_eq] at e
    simp only [e]; rfl

set_option linter.unnecessarySeqFocus false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- research-far (kept8): a key of at least 8 makes the selector's sign expression the empty suffix (`.bit true`). -/
theorem kept8_signExpr (p : LeaveSelector.Ports) (k : LeaveSelector.Mode) (v : BasisState) (hk : 8 ≤ LeaveSelector.key k) :
    (LeaveSelector.signExpr p k).read v = true := by
  have r : LeaveSelector.right k = true := by
    unfold LeaveSelector.right; unfold LeaveSelector.key at hk; exact decide_eq_true (by omega)
  have hz : decide (0 < LeaveSelector.key k) = true := decide_eq_true (by omega)
  have d : (List.range 15).drop (LeaveSelector.key k + LeaveSelector.key k) = [] :=
    List.drop_of_length_le (by rw [List.length_range]; omega)
  unfold LeaveSelector.signExpr
  rw [if_pos (Bool.and_eq_true_iff.mpr ⟨r, hz⟩)]
  unfold LeaveSelector.suffixExpr
  rw [d]
  rfl

set_option linter.unnecessarySeqFocus false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- research-far (kept8): the carry-in fold, adjust, barrel and `fix8P` in front of the digit pass keep every tag and
leave `1613 = ((e0+3 ^^ e0+6) ^^ 1596) ^^ 1597` of the state in front of them (`middle_result`'s first half). -/
theorem kept8_preJoin (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (t : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, t.basis q = false) (selectZero : t.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → t.basis (Shadow7.bankW (start j) i) = false)
    (tags : (∃ key : Fin 16, ∀ q ∈ tagsP, t.basis q = decide (q = tagsP.getD key 0)) ∨ (∀ q ∈ tagsP, t.basis q = false)) :
    (∀ q ∈ tagsP, (run (GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j) ++
        Shadow7.fix8P (start j) (Shadow7.sbP (start j)))) m t).basis q = t.basis q) ∧
      (run (GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j) ++
        Shadow7.fix8P (start j) (Shadow7.sbP (start j)))) m t).basis 1613 =
        (((t.basis (Shadow7.e0P (start j) + 3) ^^ t.basis (Shadow7.e0P (start j) + 6)) ^^ t.basis 1596) ^^ t.basis 1597) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have r := Shadow7.rail_win w1 w2
  have n3 : (Shadow7.e0P (start j) + 3 : Wire) ≠ 1613 := by unfold Wire at *; omega
  have n6 : (Shadow7.e0P (start j) + 6 : Wire) ≠ 1613 := by unfold Wire at *; omega
  have n63 : (Shadow7.e0P (start j) + 6 : Wire) ≠ Shadow7.e0P (start j) + 3 := by unfold Wire at *; omega
  let pre : State := ⟨t.phase, writeBit t.basis (Shadow7.e0P (start j) + 3)
    (t.basis (Shadow7.e0P (start j) + 3) ^^ t.basis (Shadow7.e0P (start j) + 6))⟩
  have preq (q : Wire) (ne : q ≠ Shadow7.e0P (start j) + 3) : pre.basis q = t.basis q := by
    show writeBit t.basis _ _ q = t.basis q
    simp only [writeBit, Function.update_of_ne ne]
  have pre3 : pre.basis (Shadow7.e0P (start j) + 3) =
      (t.basis (Shadow7.e0P (start j) + 3) ^^ t.basis (Shadow7.e0P (start j) + 6)) := by
    show writeBit t.basis _ _ _ = _
    simp only [writeBit, Function.update_self]
  have cleanP : ∀ q ∈ carries j, pre.basis q = false := by
    intro q hq
    refine (preq q ?_).trans (clean q hq)
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    have pt := Shadow7.pool_top w1 w2
    have p := Shadow7.pool_cases (i := i) w1 w2; unfold Wire at *; omega
  have selP : pre.basis 1613 = false := (preq _ (Ne.symm n3)).trans selectZero
  have padP : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 →
      pre.basis (Shadow7.bankW (start j) i) = false := by
    intro i lo hi
    have b := Shadow7.bank_cases w1 w2 hi
    exact (preq _ (by unfold Wire at *; omega)).trans (padding i lo hi)
  have tagNe : ∀ q ∈ tagsP, q ≠ Shadow7.e0P (start j) + 3 := by
    intro q hq
    have tq := tags_range' q hq
    unfold Wire at *; omega
  let early := GateMirror.forward (Shadow7.leaveAdjustCore (start j) ++ Shadow7.leaveBarrel (start j))
  let signBit : Program := [.CX (Shadow7.e0P (start j) + 3) 1613, .CX 1596 1613, .CX 1597 1613,
    .CX (Shadow7.e0P (start j) + 6) (Shadow7.e0P (start j) + 3)]
  let v := run early m pre
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have frame : ∀ q, HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q →
      v.basis q = pre.basis q := by
    rcases tags with ⟨key, one⟩ | off
    · exact (high_result j h0 (by omega) key pre m cleanP selP padP
        (fun q hq => (preq q (tagNe q hq)).trans (one q hq))).frame
    · exact (nearHigh_result j h0 (by omega) pre m cleanP selP padP
        (fun q hq => (preq q (tagNe q hq)).trans (off q hq))).frame
  have bankOut : ∀ q : Nat, (1556 ≤ q ∧ q ≤ 1597) ∨ (q ≤ 785) ∨
      (Shadow7.e0P (start j) + 3 ≤ q ∧ q ≤ Shadow7.e0P (start j) + 9) →
      HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q := by
    intro q hq i hi e
    have b := Shadow7.bank_cases w1 w2 hi
    unfold Wire at *; omega
  have sg := run_sign8 (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 6) 1596 1597 1613 tape v n3 n6
    (by decide) (by decide) n63
  have unchanged (q : Wire) (ne : q ≠ 1613) (ne3 : q ≠ Shadow7.e0P (start j) + 3) : u.basis q = v.basis q :=
    sg.2.2.2 q ne ne3
  have ext3 := bankOut (Shadow7.e0P (start j) + 3) (Or.inr (Or.inr (by omega)))
  have v3 : v.basis (Shadow7.e0P (start j) + 3) =
      (t.basis (Shadow7.e0P (start j) + 3) ^^ t.basis (Shadow7.e0P (start j) + 6)) := (frame _ ext3).trans pre3
  have v96 : v.basis 1596 = t.basis 1596 :=
    (frame _ (bankOut 1596 (Or.inl (by omega)))).trans (preq _ (by unfold Wire at *; omega))
  have v97 : v.basis 1597 = t.basis 1597 :=
    (frame _ (bankOut 1597 (Or.inl (by omega)))).trans (preq _ (by unfold Wire at *; omega))
  have select : v.basis 1613 = false := (frame _ (layout j h0 (by omega)).separate).trans selP
  have u13 : u.basis 1613 =
      (((t.basis (Shadow7.e0P (start j) + 3) ^^ t.basis (Shadow7.e0P (start j) + 6)) ^^ t.basis 1596) ^^ t.basis 1597) := by
    have h := sg.2.1
    rw [select, v3, v96, v97, Bool.false_xor] at h
    exact h
  have parts0 : GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j) ++
      Shadow7.fix8P (start j) (Shadow7.sbP (start j))) =
      Instr.CX (Shadow7.e0P (start j) + 6) (Shadow7.e0P (start j) + 3) ::
        (GateMirror.forward (Shadow7.leaveAdjustCore (start j) ++ Shadow7.leaveBarrel (start j)) ++
          [.CX (Shadow7.e0P (start j) + 3) 1613, .CX 1596 1613, .CX 1597 1613,
            .CX (Shadow7.e0P (start j) + 6) (Shadow7.e0P (start j) + 3)]) := by
    simp only [forward_app, adjust_forward, fix8_forward, List.append_assoc, List.cons_append]
  have parts : GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j) ++
      Shadow7.fix8P (start j) (Shadow7.sbP (start j))) =
      Instr.CX (Shadow7.e0P (start j) + 6) (Shadow7.e0P (start j) + 3) :: (early ++ signBit) := parts0
  rw [parts, run_cx_cons, run_append, run_take]
  refine ⟨fun q hq => ?_, u13⟩
  have tq := tags_range' q hq
  exact (unchanged q (by unfold Wire at *; omega) (tagNe q hq)).trans
    ((frame q (bankOut q (Or.inl (by unfold Wire at *; omega)))).trans (preq q (tagNe q hq)))

/-- research-far (kept8): the stock prefix in front of the digit pass = entry, full selector prefix, middle head. -/
theorem kept8_moveAB_split (j : Fin 26) :
    Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++ Shadow7.moveB (start j)) =
      entryOps (start j) ++ (fullPrefix j ++ (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j) ++
        Shadow7.fix8P (start j) (Shadow7.sbP (start j)) ++ Shadow7.glueG3 (start j))) := by
  have e : ∀ (l r : List Gate), l.take 27 ++ ((l.drop 27).take 16 ++ (l.drop 43 ++ r)) = l ++ r := by
    intro l r
    have d : l.drop 43 = (l.drop 27).drop 16 := by simp [List.drop_drop]
    rw [d, ← List.append_assoc ((l.drop 27).take 16), List.take_append_drop, ← List.append_assoc,
      List.take_append_drop]
  simp only [Shadow7.moveA, Shadow7.moveMux, Shadow7.moveB, entryOps, fullPrefix, List.append_assoc]
  rw [e]

theorem kept8_moveAB_run (j : Fin 26) (o : List Bool) (s : State) :
    run (GateMirror.forward (Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++ Shadow7.moveB (start j)))) o s =
      run (GateMirror.forward (Shadow7.glueG3 (start j)))
        (((o.drop (measurementCount (GateMirror.forward (entryOps (start j))))).drop
          (measurementCount (GateMirror.forward (fullPrefix j)))).drop (measurementCount (GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j) ++ Shadow7.fix8P (start j) (Shadow7.sbP (start j))))))
        (run (GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j) ++
          Shadow7.fix8P (start j) (Shadow7.sbP (start j))))
        ((o.drop (measurementCount (GateMirror.forward (entryOps (start j))))).drop
          (measurementCount (GateMirror.forward (fullPrefix j))))
        (run (GateMirror.forward (fullPrefix j)) (o.drop (measurementCount (GateMirror.forward (entryOps (start j)))))
          (run (GateMirror.forward (entryOps (start j))) (o.take (measurementCount (GateMirror.forward (entryOps (start j))))) s))) := by
  rw [kept8_moveAB_split j, forward_app (entryOps (start j)), forward_app (fullPrefix j), run_append, run_append,
    run_take (GateMirror.forward (fullPrefix j)),
    forward_app (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j) ++ Shadow7.fix8P (start j) (Shadow7.sbP (start j))),
    run_append, run_take (GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j) ++ Shadow7.fix8P (start j) (Shadow7.sbP (start j))))]

/-- Margin-16 glue G3 sits between `fix8P` and the join; it writes only the bank wire 0 (restored) and B row -1, so
every other wire reads as before it (fable-leap; found by keptparity). -/
theorem kept8_moveAB_basis (j : Fin 26) (o : List Bool) (s : State) (q : Wire)
    (hb : q ≠ Shadow7.b0P (start j) - 1) (hk : q ≠ Shadow7.bankW (start j) 0) :
    (run (GateMirror.forward (Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++ Shadow7.moveB (start j)))) o s).basis q =
      (run (GateMirror.forward (Shadow7.leaveAdjust (start j) ++ Shadow7.leaveBarrel (start j) ++
          Shadow7.fix8P (start j) (Shadow7.sbP (start j))))
        ((o.drop (measurementCount (GateMirror.forward (entryOps (start j))))).drop
          (measurementCount (GateMirror.forward (fullPrefix j))))
        (run (GateMirror.forward (fullPrefix j)) (o.drop (measurementCount (GateMirror.forward (entryOps (start j)))))
          (run (GateMirror.forward (entryOps (start j))) (o.take (measurementCount (GateMirror.forward (entryOps (start j))))) s))).basis q := by
  rw [kept8_moveAB_run j o s]
  apply LeaveReadoutFrame.preserved
  intro hm
  rw [dest_forward] at hm
  simp only [Shadow7.glueG3, List.map_cons, List.map_nil, GateMirror.target, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h
  · exact hk h
  · exact hb h
  · exact hk h

set_option linter.unnecessarySeqFocus false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- research-far (kept8): in front of the digit pass a hot tag `i ≥ 8` sees `1613 = 0`. A tag is hot only when the mode
is enabled (far flag on) at its key; a key `≥ 8` makes `signExpr` the empty suffix, so `1596 = 1`, `1597 = e0+6`, and
`fix8P` leaves `1613 = (1 ^^ e0+6) ^^ 1 ^^ e0+6 = 0`. This is the hypothesis `dead` of `Shadow7.leaveMove_same`. -/
theorem Inputs.keptState {j : Fin 26} (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) {s : State} {z : SkywalkNat.State}
    {g0 s0 : Bool} (h : Inputs j s z g0 s0) (o : List Bool) :
    ∃ (k : LeaveSelector.Mode) (c sg : Bool), (k.val = 0 → c = false ∧ sg = false) ∧ (8 ≤ LeaveSelector.key k → sg = true) ∧
      (run (GateMirror.forward (Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++ Shadow7.moveB (start j)))) o s).basis
        1613 = (((LeaveSelector.enabled k ^^ c) ^^ sg) ^^ (c && sg)) ∧
      ∀ i : Fin 16, (run (GateMirror.forward (Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++
        Shadow7.moveB (start j)))) o s).basis (tagsP.getD i.val 0) = (LeaveSelector.enabled k && decide (i.val = LeaveSelector.key k)) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have rr := Shadow7.rail_win w1 w2
  have bk0 := Shadow7.bank_cases w1 w2 (i := 0) (by omega)
  have glue (q : Wire) (hq : 1556 ≤ q) (hq2 : q ≤ 1613) :=
    kept8_moveAB_basis j o s q (by unfold Wire at *; omega) (by unfold Wire at *; omega)
  let fl := flags z g0 s0
  have mode : actualMode (Shadow7.sbP (start j)) z =
      farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j h0 h1 s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  let A0 := GateMirror.forward (entryOps (start j))
  let o0 := o.take (measurementCount A0)
  let n := o.drop (measurementCount A0)
  let en := run A0 o0 s
  have watchedOK := frontReady_frame j h0 h1 s o0 z fl.1 fl.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0) (LeaveJ7.glueBound j z fl.2 ⟨h.farSmall, h.endSmall⟩)
    (LeaveJ7.RecordedEvents.glueFlag j h0 h1 s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side)
  have zeroE : ∀ q ∈ watched j, en.basis q = false := fun q hq => (watchedOK q hq).trans (h.zero q hq)
  have base : ∀ q : Nat, 1561 ≤ q → q ≤ 1597 → en.basis q = false := by
    intro q lo hi
    apply zeroE
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q - 1559, by omega, by omega⟩
  have z59 : en.basis 1559 = false := zeroE _ (by simp [watched])
  have z60 : en.basis 1560 = false := zeroE _ (by simp [watched])
  have zc : en.basis (ports j).crossing = false := zeroE _ (by simp [watched, ports])
  have zn : en.basis (ports j).near = false := zeroE _ (by simp [watched, ports])
  have kept (q : Nat) (ok : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 16) ∨
      (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 16) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨
      (1556 ≤ q ∧ q ≤ 1575) ∨ q = Shadow7.e0P (start j) + 5)) : en.basis q = s.basis q :=
    entry_keep j h0 h1 q ok s o0
  let k := actualMode (Shadow7.sbP (start j)) z
  have modeE : k = farMode (en.basis (Shadow7.e0P (start j) + 3)) (en.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [kept _ (by omega), kept _ (by omega)]; exact mode
  have eventsE : right k = true → ∀ i < 15, i ≤ key k → en.basis (swaps j i) = decide (i = key k) := by
    intro on' i' hi hq
    have sw := swaps_exact j h0 h1 i' hi
    exact (kept _ (by unfold Wire at *; omega)).trans (ev.2 on' i' hi hq)
  have prepared := preparedState j h0 (by omega) en n en.basis z.u k modeE z59 z60 (beforeFresh _ _ _ base zc zn) eventsE
  let t := run (GateMirror.forward (fullPrefix j)) n en
  have sym (q : Wire) : t.basis q = (prior j k q).read en.basis := congrArg (fun st : State => st.basis q) prepared
  have keepT (q : Nat) (ok1 : ¬ ((1559 ≤ q ∧ q ≤ 1597) ∨ q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7))
      (ok2 : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 16) ∨
        (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 16) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨
        (1556 ≤ q ∧ q ≤ 1575) ∨ q = Shadow7.e0P (start j) + 5)) : t.basis q = s.basis q :=
    (prefix_keep j h0 (by omega) q ok1 en n).trans (kept q ok2)
  have cleanT : ∀ q ∈ carries j, t.basis q = false := by
    intro q hq
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi'
    have p := Shadow7.pool_cases (i := i') w1 w2
    exact (keepT _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)).trans (h.clean _ hq)
  have zeroT : t.basis 1613 = false :=
    (keepT 1613 (by omega) (by omega)).trans
      (native_carryJ_lt j h0 h1 _ s h.ready 1613 (by decide) (by unfold Wire at *; omega))
  have padT : ∀ i' : Nat, Shadow7.wpP (start j) ≤ i' → i' < Shadow7.wpP (start j) + 15 →
      t.basis (Shadow7.bankW (start j) i') = false := by
    intro i' lo hi
    have b := Shadow7.bank_cases w1 w2 hi
    exact (keepT _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)).trans (h.padding i' lo hi)
  have tagsT : (∃ key : Fin 16, ∀ q ∈ tagsP, t.basis q = decide (q = tagsP.getD key 0)) ∨
      (∀ q ∈ tagsP, t.basis q = false) := by
    by_cases f : Shadow.far (Shadow7.sbP (start j)) 15 z
    · exact Or.inl ⟨TrueMiddle.key j z, fun q hq => (sym q).trans
        ((loaded_tags j h0 (by omega) z en.basis q hq).trans (if_pos f))⟩
    · exact Or.inr (fun q hq => (sym q).trans ((loaded_tags j h0 (by omega) z en.basis q hq).trans (if_neg f)))
  have pj := kept8_preJoin j h0 h1 t (n.drop (measurementCount (GateMirror.forward (fullPrefix j)))) cleanT zeroT padT tagsT
  have fe : en.basis (Shadow7.e0P (start j) + 3) = LeaveSelector.enabled k := by
    have e := congrArg LeaveSelector.enabled modeE
    rw [enabled_farMode] at e
    exact e.symm
  have t3 : t.basis (Shadow7.e0P (start j) + 3) = LeaveSelector.enabled k :=
    (prefix_keep j h0 (by omega) _ (by unfold Wire at *; omega) en n).trans fe
  have t6 : t.basis (Shadow7.e0P (start j) + 6) = (crossing (ports j) k).read en.basis := by
    rw [sym, (controlsAt j h0 (by omega) k).1]
  have t96 : t.basis 1596 = (signExpr (ports j) k).read en.basis := by
    rw [sym, control96 j h0 (by omega) k]
  have t97 : t.basis 1597 = ((crossing (ports j) k).read en.basis && (signExpr (ports j) k).read en.basis) := by
    rw [sym, (controlsAt j h0 (by omega) k).2, read_conj]
  refine ⟨k, (crossing (ports j) k).read en.basis, (signExpr (ports j) k).read en.basis, ?_,
    fun hk8 => kept8_signExpr _ _ _ hk8, (glue 1613 (by decide) (by decide)).trans (pj.2.trans (by rw [t3, t6, t96, t97])), ?_⟩
  · intro hk
    have zero : k = 0 := Fin.ext hk
    rw [zero]
    exact ⟨rfl, rfl⟩
  · intro i
    have tq := tags_range' _ (tags_mem i.val i.isLt)
    exact (glue _ tq.1 (le_trans tq.2 (by decide))).trans ((pj.1 _ (tags_mem i.val i.isLt)).trans
      (selected j h0 (by omega) en n en.basis z.u k modeE z59 z60 (beforeFresh _ _ _ base zc zn) eventsE i))

set_option linter.unnecessarySeqFocus false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- research-far (kept8): in front of the digit pass a hot tag `i ≥ 8` sees `1613 = 0`. A tag is hot only when the mode
is enabled (far flag on) at its key; a key `≥ 8` makes `signExpr` the empty suffix, so `1596 = 1`, `1597 = e0+6`, and
`fix8P` leaves `1613 = (1 ^^ e0+6) ^^ 1 ^^ e0+6 = 0`. This is the hypothesis `dead` of `Shadow7.leaveMove_same`. -/
theorem Inputs.dead {j : Fin 26} (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) {s : State} {z : SkywalkNat.State}
    {g0 s0 : Bool} (h : Inputs j s z g0 s0) (o : List Bool) :
    ∀ i, 8 ≤ i → i < 16 →
      (run (GateMirror.forward (Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++ Shadow7.moveB (start j)))) o s).basis
        (tagsP.getD i 0) = true →
      (run (GateMirror.forward (Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++ Shadow7.moveB (start j)))) o s).basis
        1613 = false := by
  intro i i8 i16 hot
  obtain ⟨k, c, sgn, _, high, digit, tags⟩ := h.keptState h0 h1 o
  have tag := (tags (⟨i, i16⟩ : Fin 16)).symm.trans hot
  obtain ⟨en, which⟩ := Bool.and_eq_true_iff.mp tag
  have index : i = LeaveSelector.key k := of_decide_eq_true which
  have sign := high (index ▸ i8)
  rw [digit, en, sign]
  cases c <;> rfl


/-- KeptParity (GordoAR a2ce2c3a): in front of the kept pass of the moved leave the digit `1613` and the tags satisfy
`KeptParity.relation` (the kept pass's row 0 is the parity of rows 1..7). The moved rows only clear cells below 1556. -/
theorem Inputs.movedRelation {j : Fin 26} (lo : 0 ≤ j.val) (hi : j.val ≤ 24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : Inputs j s z g sg) :
    KeptParity.relation (fun i => (run (GateMirror.forward (Shadow7.moveA (start j) ++
      (GateMirror.rowGates (Shadow7.e0P (start j) + 6) (Shadow7.moveRows (start j)) ++ Shadow7.moveB (start j)))) [] s).basis
        (KeptParity.port (start j) i)) := by
  obtain ⟨w1, w2⟩ := start_win7 j lo (by omega)
  obtain ⟨k, c, sgn, inactive, high, digit, tags⟩ := h.keptState lo hi []
  have hot := h.hot lo hi []
  have moved := Shadow7.prefix_rows w1 w2 s [] _ hot.1 hot.2
  have cl := Shadow7.cell_lt w1 w2
  have off (q : Wire) (hq : 1556 ≤ q) : ∀ r ∈ Shadow7.moveRows (start j), q ≠ r.2 := by
    intro r hr
    obtain ⟨i, bound, rfl⟩ := Shadow7.mem_moveRows hr
    dsimp only
    unfold Wire at *
    omega
  have unchanged (q : Wire) (hq : 1556 ≤ q) :
      (run (GateMirror.forward (Shadow7.moveA (start j) ++ (GateMirror.rowGates (Shadow7.e0P (start j) + 6)
        (Shadow7.moveRows (start j)) ++ Shadow7.moveB (start j)))) [] s).basis q =
      (run (GateMirror.forward (Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++ Shadow7.moveB (start j)))) [] s).basis q := by
    rw [forward_app, forward_app, GateMirror.rowGates_forward, moved, Shadow7.clrAll_frame _ _ _ _ (off q hq)]
  apply KeptParity.relationOfMode _ k c sgn inactive high
  · exact (unchanged 1613 (by decide)).trans digit
  · intro i hi8
    have small : (i : Nat) < 8 := hi8
    have lim : (i : Nat) < 16 := Nat.lt_trans small (by decide)
    have hit := tags (⟨i, lim⟩ : Fin 16)
    have bound := tags_range' _ (tags_mem i lim)
    simpa only [KeptParity.port, if_pos small] using (unchanged _ bound.1).trans hit

theorem Inputs.sameMove {j : Fin 26} (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) {s : State} {z : SkywalkNat.State}
    {g0 s0 : Bool} (h : Inputs j s z g0 s0) (m : List Bool) : run (Shadow7.leaveMoveP j) m s = run (Shadow7.leaveP j) m s := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  exact Shadow7.leaveMove_same w1 w2 s m _ (h.hot h0 h1 m).1 (h.hot h0 h1 m).2 (h.dead h0 h1 m)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

namespace Roundtrip
/-- `result` for the move leave (c9cc6a76's `invertsMove`, generic). -/
theorem resultMove (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m n : List Bool) (z : SkywalkNat.State)
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
    (bound : LeaveJ7.TrueMiddle.F j z < 2^(Shadow7.liveW (start j)))
    (phase : ∀ o, (run (Shadow7.leaveP j) o s).phase = s.phase)
    (initial : ∀ q, 1556 ≤ q → q < Shadow7.e0P (start j) → s.basis q = false)
    (extra : ∀ q, Shadow7.e0P (start j) + 10 ≤ q → q < Shadow7.e0P (start j) + 10 + min (Shadow7.wpP (start j) - 1 - (Shadow7.e0P (start j) - 1598)) (2045 - start j - Shadow7.e0P (start j)) →
      s.basis q = false)
    (up : ∀ q, Shadow7.a0P (start j) + 17 ≤ q → q < Shadow7.a0P (start j) + 17 + min 4 (Shadow7.wpP (start j) + start j - 448) → s.basis q = false) (a0 : Wire)
    (hot : ∀ o, (run (GateMirror.forward (Shadow7.moveA (start j))) o s).basis (Shadow7.e0P (start j) + 6) = false ∧
      ∀ r ∈ Shadow7.moveRows (start j), (run (GateMirror.forward (Shadow7.moveA (start j))) o s).basis r.1 = true → r.2 = a0)
    (dead : ∀ o, ∀ i, 8 ≤ i → i < 16 →
      (run (GateMirror.forward (Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++ Shadow7.moveB (start j)))) o s).basis
        (tagsP.getD i 0) = true →
      (run (GateMirror.forward (Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++ Shadow7.moveB (start j)))) o s).basis
        1613 = false)
    (flag : (s.basis (Shadow7.e0P (start j) + 4) ^^ (s.basis (Shadow7.e0P (start j) + 3) &&
      s.basis (OB5.sig (start j + 14) (start j + 1044)))) =
      decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)) :
    run (Shadow7.leaveMoveInvP j) n (run (Shadow7.leaveMoveP j) m s) = s := by
  have atCore := CoreCheckpoint.result j h0 h1 s [] z G sg small ready fresh scratch temp odd room clean padding bank zero
    par mode events flag
  have core := CoreCheckpoint.oracle j h0 h1 s _ atCore.1 atCore.2.2.1
    (initial 1613 (by decide) (by unfold Shadow7.e0P Shadow7.sbP start; omega))
    (initial 1614 (by decide) (by unfold Shadow7.e0P Shadow7.sbP start; omega))
  have bs := beforeStore_result j h0 h1 s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode
    events nextSmall bound (flag := flag)
  have post : (run (GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j))) [] s).basis 1556 = false := by
    have safe : (1556 : Wire) ∉ (GateMirror.forward (Shadow7.leaveLowClose (start j))).map LeaveReadoutFrame.destination := by
      intro hm
      rw [dest_forward] at hm
      obtain ⟨g, hg, e⟩ := List.mem_map.mp hm
      exact (lowClose_keeps j h0 h1 g hg).2 e
    rw [← StoreMapped.program_eq j, StoreMapped.program, run_append, run_take, LeaveReadoutFrame.preserved _ _ _ _ safe]
    exact bs.2.1
  exact Shadow7.leaveMove_inverts j h0 (by omega) s phase initial extra up core (fun i hi => atCore.2.2.2 _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    (CoreCheckpoint.free58 j h0 h1 s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events flag)
    post a0 hot dead m n
end Roundtrip

/-- A wire outside `Shadow7.leaveBox2` keeps its value through the move leave (its operands are the reference leave's). -/
theorem leaveMove_keeps (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Wire) (hq : ¬ Shadow7.leaveBox2 (start j) q)
    (m : List Bool) (s : State) : (run (Shadow7.leaveMoveP j) m s).basis q = s.basis q := by
  apply LeaveReadoutFrame.preserved
  unfold Shadow7.leaveMoveP
  rw [dest_forward]
  intro hmem
  obtain ⟨g, hg, e⟩ := List.mem_map.mp hmem
  exact hq (e ▸ Shadow7.allW_leaveMove (start j) (Shadow7.leaveOps_box2 j h0 (by omega)) g hg (target g) (by rw [GateMirror.Gate.wires_eq]; simp))

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission
open Arithmetic Partial SkywalkNat
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- `Inputs.roundtrip` for the move leave. -/
theorem Inputs.roundtripMove {j : Fin 26} (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) {s : State} {z : SkywalkNat.State}
    {g0 s0 : Bool} (h : Inputs j s z g0 s0) (m n : List Bool) : run (Shadow7.leaveMoveInvP j) n (run (Shadow7.leaveMoveP j) m s) = s := by
  let u := flags z g0 s0
  let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par := RecordedParity.result j h0 h1 s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j h0 h1 s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have ph (o : List Bool) : (run (Shadow7.leaveP j) o s).phase = s.phase :=
    (Whole.result j h0 h1 s o z u.1 u.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank
      h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.fit xs (SkywalkTrace.trace_length _ _)
      (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
      ev.1 h.far h.side (LeaveJ7.RecordedEvents.glueFlag j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
        h.far h.side)).1
  exact Roundtrip.resultMove j h0 h1 s m n z u.1 u.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding
    h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.fit ph (native_carryJ j h0 h1 _ s h.ready h.top h.top2) h.extra h.reloc _ (h.hot h0 h1) (h.dead h0 h1)
    (flag := (LeaveJ7.RecordedEvents.glueFlag j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
        h.far h.side))

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission


end


-- ==== crtf: the CRT leave side (leave-move). CRT barrel leaves on every block 1..22;
-- needs the CRT core (CRT.lean), the LeaveJ7 / LeaveMove / ShadowBox2 parts above and staircase82's EARLY CRTWindow
-- block (split_ops, leave_eq, ...). ====

-- ---- CRTLeaveSplice ----
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
open GateMirror Partial

structure Valid (s : State) (gs : List Gate) : Prop where
  physical : ∀ g ∈ gs, proper g = true
  prepared : Prepared s gs
  ready : Ready s gs

private theorem Valid.tail {s : State} {g : Gate} {gs : List Gate} (v : Valid s (g::gs)) :
    Valid (transition g s) gs :=
  ⟨fun x hx => v.physical x (List.mem_cons_of_mem _ hx),v.prepared.2,v.ready.2⟩

theorem Valid.default_run {s : State} {gs : List Gate} (v : Valid s gs) (m : List Bool) :
    run (GateMirror.forward gs) m s = run (GateMirror.forward gs) [] s := by
  induction gs generalizing s m with
  | nil => rfl
  | cons g gs ih =>
    change run ([front g] ++ GateMirror.forward gs) m s = run ([front g] ++ GateMirror.forward gs) [] s
    simp only [run_append,run_take,List.drop_nil]
    rw [head_default g s v.prepared.1 (v.physical _ (List.mem_cons_self ..))]
    exact ih v.tail _

theorem Valid.parts {s : State} {a b : List Gate} (ok : Valid s (a++b)) :
    Valid s a ∧ Valid (run (GateMirror.forward a) [] s) b := by
  induction a generalizing s with
  | nil => exact ⟨⟨by simp,trivial,trivial⟩,ok⟩
  | cons g gs ih =>
    obtain ⟨left,right⟩ := ih ok.tail
    refine ⟨⟨fun x hx => ok.physical x (List.mem_append_left _ hx),⟨ok.prepared.1,left.prepared⟩,⟨ok.ready.1,left.ready⟩⟩,?_⟩
    change Valid (run ([front g]++GateMirror.forward gs) [] s) b
    simpa only [run_append,run_take,List.drop_nil] using right

theorem Valid.undo_run {s : State} {a : List Gate} (v : Valid s a) (m n : List Bool) :
    run (GateMirror.inverse a) n (run (GateMirror.forward a) m s) = s := invert a s v.physical v.prepared v.ready m n

/-- Replace a measured middle program. The unchanged suffix returns to the same prepared image
before the new inverse runs, regardless of the two independent measurement records. -/
theorem replace (a b c : List Gate) (fwd rev : Program) (s : State) (v : Valid s (a++(b++c)))
    (same : ∀ t, run fwd t (run (GateMirror.forward a) [] s) = run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s))
    (back : ∀ t, run rev t (run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s)) = run (GateMirror.forward a) [] s) :
    (∀ m, run (GateMirror.forward a ++ fwd ++ GateMirror.forward c) m s = run (GateMirror.forward (a++(b++c))) m s) ∧
    (∀ m n, run (GateMirror.inverse c ++ rev ++ GateMirror.inverse a) n (run (GateMirror.forward a ++ fwd ++ GateMirror.forward c) m s) = s) := by
  obtain ⟨va,vbc⟩ := v.parts
  obtain ⟨vb,vc⟩ := vbc.parts
  let u := run (GateMirror.forward a) [] s
  let z := run (GateMirror.forward b) [] u
  have emitted (m : List Bool) : run (GateMirror.forward a ++ fwd ++ GateMirror.forward c) m s = run (GateMirror.forward c) [] z := by
    simp only [run_append,run_take,va.default_run,same]
    exact vc.default_run _
  have old (m : List Bool) : run (GateMirror.forward (a++(b++c))) m s = run (GateMirror.forward c) [] z := by
    simp only [forward_app,run_append,va.default_run,vb.default_run]
    exact vc.default_run _
  refine ⟨fun m => (emitted m).trans (old m).symm,?_⟩
  intro m n
  rw [emitted]
  have undoC (l : List Bool) : run (GateMirror.inverse c) l (run (GateMirror.forward c) [] z) = z := vc.undo_run [] l
  have undoB (l : List Bool) : run rev l z = u := back l
  simp only [run_append,run_take,undoC,undoB]
  exact va.undo_run [] _

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
end

-- ---- CRTLeaveReady ----
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
open Partial GateMirror LeaveJ7 LeaveJ7.Admission SkywalkNat LeaveSelector
attribute [local irreducible] run SkywalkNat.step
set_option maxHeartbeats 2000000

set_option linter.constructorNameAsVariable false in
/-- The moved shadow leave supplies fresh make targets and valid erasures along its entire
canonical trajectory. These facts also hold on each side of the barrel cut. -/
theorem moved_valid {j : Fin 26} (h0 : 0≤j.val) (h1 : j.val≤24) {s : State} {z : SkywalkNat.State}
    {g0 s0 : Bool} (h : Inputs j s z g0 s0) : Valid s (Shadow7.leaveMoveOps (start j)) := by
  let u := LeaveJ7.Admission.flags z g0 s0
  let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par := RecordedParity.result j (by omega) (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j (by omega) (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have ph (o : List Bool) : (run (Shadow7.leaveP j) o s).phase = s.phase :=
    (Whole.result (flag := LeaveJ7.RecordedEvents.glueFlag j (by omega) (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side) j (by omega) (by omega) s o z u.1 u.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank
      h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.fit xs (SkywalkTrace.trace_length _ _)
      (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
      ev.1 h.far h.side).1
  have atCore := CoreCheckpoint.result j (by omega) (by omega) s [] z u.1 u.2 ⟨h.farSmall,h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero
    par mode ev.2 (LeaveJ7.RecordedEvents.glueFlag j (by omega) (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side)
  have core := CoreCheckpoint.oracle j h0 h1 s _ atCore.1 atCore.2.2.1
    (native_carryJ_lt j h0 h1 _ s h.ready 1613 (by decide) (Nat.lt_trans (by decide) (e0P_gt_1615 j h1)))
    (native_carryJ_lt j h0 h1 _ s h.ready 1614 (by decide) (e0P_gt_1615 j h1))
  have bs := beforeStore_result (flag := LeaveJ7.RecordedEvents.glueFlag j (by omega) (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side) j (by omega) (by omega) s [] z u.1 u.2 ⟨h.farSmall,h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode
    ev.2 ⟨h.nextFarSmall,h.endSmall⟩ h.fit
  have post : (run (GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j))) [] s).basis 1556 = false := by
    have safe : (1556 : Wire) ∉ (GateMirror.forward (Shadow7.leaveLowClose (start j))).map LeaveReadoutFrame.destination := by
      intro hm
      rw [dest_forward] at hm
      obtain ⟨g, hg, e⟩ := List.mem_map.mp hm
      exact (lowClose_keeps j (by omega) (by omega) g hg).2 e
    rw [← StoreMapped.program_eq j, StoreMapped.program, run_append, run_take, LeaveReadoutFrame.preserved _ _ _ _ safe]
    exact bs.2.1

  obtain ⟨w1,w2⟩ := start_win7 j (by omega) (by omega)
  obtain ⟨ready,phys⟩ := Shadow7.leave_ready j (by omega) (by omega) s (native_carryJ j (by omega) (by omega) _ s h.ready h.top h.top2) h.extra h.reloc core (fun i hi => atCore.2.2.2 _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩))
    (LeaveJ7.CoreCheckpoint.free58 j (by omega) (by omega) s [] z u.1 u.2 ⟨h.farSmall,h.endSmall⟩ h.ready h.fresh h.scratch h.temp
      h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 (LeaveJ7.RecordedEvents.glueFlag j (by omega) (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side)) post
  let t := start j
  let keyWire := Shadow7.a0P t - 1 + LeaveSelector.key (actualMode (Shadow7.sbP t) z)
  have hot := h.hot (by omega) (by omega) []
  have physM := Shadow7.leaveMove_proper_of w1 (by omega) phys
  have ready' : Ready s (Shadow7.moveA t ++ (Shadow7.moveMux t ++ (Shadow7.moveB t ++ (Shadow7.moveDig t ++ Shadow7.moveC t)))) := by
    rw [←Shadow7.leaveOps_shape]
    exact ready
  have readyM16 := GateMirror.ready_move (Shadow7.e0P t+6) (Shadow7.moveRows t) (Shadow7.moveA t) (Shadow7.moveB t)
    (Shadow7.moveC t) (Shadow7.moveMux t) (Shadow7.moveDig t) (Shadow7.moveKept16 t) s keyWire
    (Shadow7.mux_forward t) (Shadow7.dig_forward t) (kept_plain _ _ _ _ _) (Shadow7.apart_move w1 (by omega))
    (Shadow7.lone_move t) (Shadow7.stillB w1 (by omega)) (Shadow7.calmB w1 (by omega)) (Shadow7.woven_move w1 (by omega)) hot.1 hot.2 ready'
  have readyM := Shadow7.ready_kept8 w1 (by omega) s keyWire hot.1 hot.2 (h.dead (by omega) (by omega) []) readyM16
  rw [←Shadow7.leaveMoveOps_shape] at readyM
  refine ⟨physM,all_prepared _ s physM ?_,readyM⟩
  intro tape
  exact (congrArg State.phase (h.sameMove (by omega) (by omega) tape)).trans (ph tape)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
end

-- ---- CRTLeaveCut ----
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveCut
open Partial GateMirror LeaveJ7
attribute [local irreducible] run
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

def selectorTail (s : Nat) : List Gate :=
  rowGates (Shadow7.e0P s+6) (Shadow7.moveRows s) ++ (Shadow7.fix5P s (Shadow7.sbP s)).drop 43

def head (s : Nat) : List Gate := Shadow7.moveA s ++ selectorTail s

theorem before_shape (s : Nat) : CRTBarrel.beforeReference s = head s ++ Shadow7.leaveAdjust s := by
  simp only [CRTBarrel.beforeReference,head,selectorTail,Shadow7.moveA,Shadow7.leaveFix5Move,List.append_assoc]

theorem move_shape (s : Nat) :
    Shadow7.leaveMoveOps s = CRTBarrel.beforeReference s ++ (Shadow7.leaveBarrel s ++ afterReference s) := by
  simp only [Shadow7.leaveMoveOps,CRTBarrel.beforeReference,afterReference,List.append_assoc]

private theorem head_targets : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    (head (start j)).all (fun g => decide (target g < 1598 ∨
      (Shadow7.e0P (start j) ≤ target g ∧ target g < Shadow7.e0P (start j)+10))) = true := by decide +kernel

private theorem tail_targets : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    (selectorTail (start j)).all (fun g => decide (target g < 1559 ∨ 1576 < target g)) = true := by decide +kernel

private theorem head_keeps (j : Fin 26) (lo : 0≤j.val) (hi : j.val≤24) (s : State) (q : Wire)
    (large : 1598 ≤ q) (apart : q < Shadow7.e0P (start j) ∨ Shadow7.e0P (start j)+10 ≤ q) :
    (run (GateMirror.forward (head (start j))) [] s).basis q = s.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  rintro hit
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hit
  have h := of_decide_eq_true (List.all_eq_true.mp (head_targets j lo (by omega)) g hg)
  unfold Wire at *
  omega

private theorem tail_keeps (j : Fin 26) (lo : 0≤j.val) (hi : j.val≤24) (s : State) (q : Wire)
    (low : 1559 ≤ q) (high : q ≤ 1576) :
    (run (GateMirror.forward (head (start j))) [] s).basis q = (run (GateMirror.forward (Shadow7.moveA (start j))) [] s).basis q := by
  rw [head,forward_app,run_append,run_take,List.drop_nil]
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  rintro hit
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hit
  have h := of_decide_eq_true (List.all_eq_true.mp (tail_targets j lo (by omega)) g hg)
  unfold Wire at *
  omega

/-- The head never targets the high A columns `a0P+17 .. a0P+20` (block 22's relocated carries). -/
private theorem head_up : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    (head (start j)).all (fun g => decide (target g < Shadow7.a0P (start j)+17 ∨
      Shadow7.a0P (start j)+21 ≤ target g)) = true := by decide +kernel

private theorem head_up_keeps (j : Fin 26) (lo : 0≤j.val) (hi : j.val≤24) (s : State) (q : Wire)
    (low : Shadow7.a0P (start j)+17 ≤ q) (high : q < Shadow7.a0P (start j)+21) :
    (run (GateMirror.forward (head (start j))) [] s).basis q = s.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  rintro hit
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hit
  have h := of_decide_eq_true (List.all_eq_true.mp (head_up j lo (by omega)) g hg)
  unfold Wire at *
  omega

theorem tag_lookup : ∀ k : Fin 16, tagsP.getD k.val 1560 = tagsP.getD k.val 0 := by decide +kernel

private theorem tag_bounds : ∀ k : Fin 16, 1559 ≤ tagsP.getD k.val 0 ∧ tagsP.getD k.val 0 ≤ 1576 := by decide +kernel

def Admissible (j : Fin 26) (t : State) : Prop :=
  ∃ (slot : Fin 17) (v : Nat), v < 2^Shadow7.wpP (start j) ∧
    v < 2^(barrelWidth (start j) - (slot.val - 1)) ∧
    HighBankBarrel.holds (Shadow7.bankW (start j)) (Shadow7.wpP (start j)+15) v t ∧
    (∀ k : Fin 16, t.basis (tagsP.getD k.val 1560) = decide (slot.val=k.val+1)) ∧
    (∀ i < 10, t.basis (Shadow7.poolW (start j) (17+i)) = false) ∧ t.basis 1613 = false

theorem selector {j : Fin 26} (_lo : 0≤j.val) (hi : j.val≤24) {s : State}
    {z : SkywalkNat.State} {g sg : Bool} (h : Admission.Inputs j s z g sg) :
    ∃ slot : Fin 17, ∀ k : Fin 16, (run (GateMirror.forward (Shadow7.moveA (start j))) [] s).basis (tagsP.getD k.val 0) =
      decide (slot.val=k.val+1) := by
  classical
  let u := run (GateMirror.forward (Shadow7.moveA (start j))) [] s
  have hot (k : Fin 16) (on : u.basis (tagsP.getD k.val 0) = true) :
      Shadow7.a0P (start j) - 1 + k.val = Shadow7.a0P (start j) - 1 + LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) := by
    apply (h.hot (Nat.zero_le _) (by omega) []).2 (tagsP.getD k.val 0,Shadow7.a0P (start j) - 1 + k.val) _ on
    exact List.mem_map.mpr ⟨k.val,List.mem_range.mpr k.isLt,rfl⟩
  by_cases active : ∃ k : Fin 16, u.basis (tagsP.getD k.val 0) = true
  · obtain ⟨key,hk⟩ := active
    refine ⟨⟨key.val+1,by have := key.isLt; omega⟩,?_⟩
    intro k
    change u.basis (tagsP.getD k.val 0) = decide (key.val+1=k.val+1)
    by_cases e : k=key
    · subst k; simpa using hk
    · have no : u.basis (tagsP.getD k.val 0) ≠ true := by
        intro hOn
        apply e
        exact Fin.ext (Nat.add_left_cancel ((hot k hOn).trans (hot key hk).symm))
      have diff : key.val+1 ≠ k.val+1 := by intro eq; exact e (Fin.ext (by omega))
      rw [decide_eq_false diff]
      exact Bool.eq_false_iff.mpr no
  · refine ⟨0,?_⟩
    intro k
    have off := Bool.eq_false_iff.mpr (fun on => active ⟨k,on⟩)
    simpa [u] using off

private theorem crt_pool_clean : ∀ j : Fin 26, j.val ≤ 24 → ∀ i : Fin 10,
    17 + i.val < Shadow7.wpP (start j) - 1 ∨ 1598 + (17 + i.val) < Shadow7.e0P (start j) := by
  decide +kernel

theorem input {j : Fin 26} (lo : 0≤j.val) (hi : j.val≤24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : Admission.Inputs j s z g sg) :
    Admissible j (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s) := by
  obtain ⟨w1,w2⟩ := start_win7 j (Nat.zero_le _) (by omega)
  have geom := Shadow7.rail_win w1 (by omega)
  have top := Shadow7.pool_top w1 (by omega)
  -- margin 17 (integrate2 FIX-B4): leaveAdjust = CX (e0+6) (e0+3) :: adjust ys carries (e0+3) 1596
  obtain ⟨u, hu⟩ : ∃ u : State, u = run (GateMirror.forward (head (start j))) [] s := ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u' : State, u' = ⟨u.phase, writeBit u.basis (Shadow7.e0P (start j)+3)
      (u.basis (Shadow7.e0P (start j)+3) ^^ u.basis (Shadow7.e0P (start j)+6))⟩ := ⟨_, rfl⟩
  have preq (q : Wire) (ne : q ≠ Shadow7.e0P (start j)+3) : u'.basis q = u.basis q := by
    rw [hu']; simp only [writeBit, Function.update_of_ne ne]
  have uk (q : Wire) (large : 1598 ≤ q) (apart : q < Shadow7.e0P (start j) ∨ Shadow7.e0P (start j)+10 ≤ q) :
      u.basis q = s.basis q := by rw [hu]; exact head_keeps j lo (by omega) s q large apart
  have uup (q : Wire) (low : Shadow7.a0P (start j)+17 ≤ q) (high : q < Shadow7.a0P (start j)+21) :
      u.basis q = s.basis q := by rw [hu]; exact head_up_keeps j lo (by omega) s q low high
  have ut (q : Wire) (low : 1559 ≤ q) (high : q ≤ 1576) :
      u.basis q = (run (GateMirror.forward (Shadow7.moveA (start j))) [] s).basis q := by
    rw [hu]; exact tail_keeps j lo (by omega) s q low high
  let p := HighBankAdjust.adjust (ys j) (carries j) (Shadow7.e0P (start j)+3) 1596
  let t := run p [] u'
  let x := regValue (ys j) t.basis
  have pe : GateMirror.forward (Shadow7.leaveAdjustCore (start j)) = p := by simp only [Shadow7.leaveAdjustCore,forward_adjustG,p,ys,carries]
  have eq : run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s = t := by
    rw [before_shape,forward_app,run_append,run_take,List.drop_nil,← hu,adjust_forward,run_cx_cons,← hu',pe]
  rw [eq]
  have clean (q : Wire) (hq : q ∈ carries j) : u'.basis q = false := by
    -- rebase 0cc07df3 (poolW has wires below 1598 on the late blocks): NOT seen by Lean
    obtain ⟨i,him,rfl⟩ := List.mem_map.mp hq
    have him' := List.mem_range.mp him
    have loc := Shadow7.pool_cases (i := i) w1 (by omega)
    by_cases up : (Shadow7.poolW (start j) i : Nat) < 1598
    · exact (preq _ (by unfold Wire at *; omega)).trans ((uup _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)).trans
        (h.clean _ (by assumption)))
    · exact (preq _ (by unfold Wire at *; omega)).trans ((uk _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)).trans
        (h.clean _ (by assumption)))
  have absent (q : Wire) (qa : 1043 < q) (qb : q < Shadow7.e0P (start j)) : q ∉ ys j := by
    rintro hit
    obtain ⟨i,ii,rfl⟩ := List.mem_map.mp hit
    have lim := List.mem_range.mp ii
    have loc := Shadow7.bank_cases (i := i) w1 (by omega) (by omega)
    unfold Wire at *
    omega
  have len : (carries j).length+1 = (ys j).length := by simp [ys,carries]; omega
  have ht := HighBankAdjust.correct (ys j) (carries j) (Shadow7.e0P (start j)+3) 1596 (adjust_nodup j (Nat.zero_le _) (by omega))
    (absent 1596 (by decide) (by unfold Wire at *; omega)) len u' [] clean
  have small : x < 2^Shadow7.wpP (start j) := by have v := regValue_lt (ys j) t.basis; rwa [ys_length] at v
  have unchanged (q : Wire) (qa : 1598 ≤ q) (qb : q < Shadow7.e0P (start j)) : t.basis q = s.basis q :=
    (ht.2.1 q (absent q (by unfold Wire at *; omega) qb)).trans ((preq q (by unfold Wire at *; omega)).trans (uk q qa (Or.inl qb)))
  obtain ⟨slot,hot⟩ := selector lo (by omega) h
  have narrow : x < 2^(barrelWidth (start j) - (slot.val - 1)) := by
    let D := (Shadow7.fix5P (start j) (Shadow7.sbP (start j))).drop 43
    let a := run (GateMirror.forward (entryOps (start j))) [] s
    let u0 := run (GateMirror.forward (fullPrefix j)) [] a
    have stillD : (Shadow7.moveRows (start j)).all (fun r => (GateMirror.forward D).all (MoveChain.quiet (Shadow7.e0P (start j) + 6) r)) = true := by
      rw [List.all_eq_true]; intro r hr; rw [List.all_eq_true]; intro g hg
      exact List.all_eq_true.mp (List.all_eq_true.mp (Shadow7.stillB w1 (by omega)) r hr) g
        (by simp [Shadow7.moveB, forward_app, D, hg])
    have hotA := h.hot (Nat.zero_le _) (by omega) []
    have hstock : entryOps (start j) ++ fullPrefix j =
        Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++ D) := by
      unfold entryOps fullPrefix Shadow7.moveA Shadow7.moveMux D
      have e5 : Shadow7.fix5P (start j) (Shadow7.sbP (start j)) =
          (Shadow7.fix5P (start j) (Shadow7.sbP (start j))).take 27 ++
          (((Shadow7.fix5P (start j) (Shadow7.sbP (start j))).drop 27).take 16 ++
            (Shadow7.fix5P (start j) (Shadow7.sbP (start j))).drop 43) := rfl
      conv_lhs => rw [e5]
      simp only [List.append_assoc]
    have u_eq_clr : u = MoveChain.clrAll (Shadow7.e0P (start j) + 6) (Shadow7.moveRows (start j)) u0 := by
      rw [hu, head, selectorTail, forward_app, forward_app, rowGates_forward, run_append, run_take,
        List.drop_nil, run_append, run_take, List.drop_nil]
      rw [MoveChain.moved (Shadow7.e0P (start j) + 6) (Shadow7.moveRows (start j)) []
        (run (GateMirror.forward (Shadow7.moveA (start j))) [] s) _
        (Shadow7.apart_move w1 (by omega)) (Shadow7.lone_move (start j)) hotA.1 hotA.2]
      rw [MoveChain.commAll _ _ _ stillD]
      congr 1
      have hu0 : u0 = run (GateMirror.forward (entryOps (start j) ++ fullPrefix j)) [] s := by
        simp only [u0, a, forward_app, run_append, run_take, List.drop_nil]
      rw [hu0, hstock]
      simp only [forward_app, Shadow7.mux_forward, run_append, run_take, List.drop_nil]
    have clrAll_other (rs : List MoveChain.Row) (st : State) (q : Wire) (hq : ∀ r ∈ rs, q ≠ r.2) :
        (MoveChain.clrAll (Shadow7.e0P (start j) + 6) rs st).basis q = st.basis q := by
      induction rs generalizing st with
      | nil => rfl
      | cons r rs ih =>
        show (MoveChain.clrAll _ rs (MoveChain.clr _ r st)).basis q = st.basis q
        rw [ih _ (fun r' hr' => hq r' (List.mem_cons_of_mem _ hr'))]
        exact MoveChain.wb_other _ _ _ _ (hq r List.mem_cons_self)
    have u_eq_u0 (q : Wire) (hq : q < Shadow7.a0P (start j) - 1 ∨ Shadow7.a0P (start j) + 15 ≤ q) :
        u.basis q = u0.basis q := by
      rw [u_eq_clr]
      apply clrAll_other
      intro r hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      rw [List.mem_range] at hi
      dsimp only; unfold Wire at *; omega
    let uFlags := LeaveJ7.Admission.flags z g sg
    have par := RecordedParity.result j (Nat.zero_le _) (by omega) s z g sg ⟨h.farSmall, h.endSmall⟩ h.odd h.record
    have mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z =
        LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
      rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
    have ev := RecordedEvents.result j (Nat.zero_le _) (by omega) s z g sg ⟨h.farSmall, h.endSmall⟩ h.odd h.record
    have front := entry_core j (Nat.zero_le _) (by omega) s [] z uFlags.1 uFlags.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp
      (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
      (LeaveJ7.glueBound j z uFlags.2 ⟨h.farSmall, h.endSmall⟩)
      (LeaveJ7.RecordedEvents.glueFlag j (Nat.zero_le _) (by omega) s z g sg ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side)
    have watchedOK := frontReady_frame j (Nat.zero_le _) (by omega) s [] z uFlags.1 uFlags.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp
      (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
      (LeaveJ7.glueBound j z uFlags.2 ⟨h.farSmall, h.endSmall⟩)
      (LeaveJ7.RecordedEvents.glueFlag j (Nat.zero_le _) (by omega) s z g sg ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side)
    have keptA (q : Nat) (ok : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 16) ∨
        (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 16) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨
        (1556 ≤ q ∧ q ≤ 1575) ∨ q = Shadow7.e0P (start j) + 5)) : a.basis q = s.basis q :=
      entry_keep j (Nat.zero_le _) (by omega) q ok s []
    have zA : ∀ q ∈ watched j, a.basis q = false := fun q hq => (watchedOK _ hq).trans (h.zero _ hq)
    have baseA : ∀ q : Nat, 1561 ≤ q → q ≤ 1597 → a.basis q = false := by
      intro q q1 q2; apply zA; simp only [watched, List.mem_append, List.mem_range'_1]; right; omega
    have z59A : a.basis 1559 = false := zA _ (by simp [watched, List.mem_range'_1])
    have z60A : a.basis 1560 = false := zA _ (by simp [watched, List.mem_range'_1])
    have zcA : a.basis (ports j).crossing = false := zA _ (by simp [watched, ports])
    have znA : a.basis (ports j).near = false := zA _ (by simp [watched, ports])
    have modeA : LeaveSelector.actualMode (Shadow7.sbP (start j)) z =
        LeaveSelector.farMode (a.basis (Shadow7.e0P (start j) + 3)) (a.basis (Shadow7.e0P (start j) + 4)) z.u := by
      rw [keptA _ (by omega), keptA _ (by omega)]; exact mode
    have evA : LeaveSelector.right (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) = true →
        ∀ i < 15, i ≤ LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) →
          a.basis (swaps j i) = decide (i = LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z)) := by
      intro on i hi hk; have sw := swaps_cases j (Nat.zero_le _) (by omega) i hi
      exact (keptA _ (by unfold Wire at *; omega)).trans (ev.2 on i hi hk)
    have prepared := preparedState j (Nat.zero_le _) (by omega) a [] a.basis z.u (LeaveSelector.actualMode (Shadow7.sbP (start j)) z)
      modeA z59A z60A (LeaveSelector.beforeFresh _ _ _ baseA zcA znA) evA
    have sym (q : Wire) : u0.basis q = (prior j (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) q).read a.basis :=
      congrArg (fun st : State => st.basis q) prepared
    have keepU0 (q : Nat) (ok : ¬ ((1559 ≤ q ∧ q ≤ 1597) ∨ q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7)) :
        u0.basis q = a.basis q := prefix_keep j (Nat.zero_le _) (by omega) q ok a []
    have math := loaded_signed j (Nat.zero_le _) (by omega) z a.basis ⟨h.farSmall, h.endSmall⟩ h.odd h.room
      (fun i hi => upperBits j (Nat.zero_le _) (by omega) _ a.basis front.2.2.2.2.2.1 i (Nat.lt_trans hi (by decide : 16 < 17)))
      ((entry_parity j (Nat.zero_le _) (by omega) s []).trans par)
    have yEq : regValue (ys j) u'.basis = regValue (ys j) s.basis := by
      rw [regValue_eq_iff]; intro q hq
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
      have bc := Shadow7.bank_cases (i := i) w1 (by omega) (by omega)
      exact (preq _ (by unfold Wire at *; omega)).trans ((u_eq_u0 _ (by unfold Wire at *; omega)).trans
        ((keepU0 _ (by unfold Wire at *; omega)).trans (keptA _ (by unfold Wire at *; omega))))
    have u3eq : u.basis (Shadow7.e0P (start j) + 3) = decide (Shadow.far (Shadow7.sbP (start j)) 15 z) :=
      (u_eq_u0 _ (by unfold Wire at *; omega)).trans ((keepU0 _ (by omega)).trans ((keptA _ (by omega)).trans h.far))
    have u6eq : u.basis (Shadow7.e0P (start j) + 6) =
        if Shadow.far (Shadow7.sbP (start j)) 15 z then !HighBankSum.cross17 (TrueMiddle.d j z) else false :=
      (u_eq_u0 _ (by unfold Wire at *; omega)).trans ((sym _).trans math.1)
    have u96eq : u'.basis 1596 = (prior j (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) 1596).read a.basis :=
      (preq _ (by unfold Wire at *; omega)).trans ((u_eq_u0 _ (by unfold Wire at *; omega)).trans (sym 1596))
    have xEq : x = HighBankAdjust.adjusted (regValue (ys j) u'.basis) (Shadow7.wpP (start j))
        (u'.basis (Shadow7.e0P (start j) + 3)) (u'.basis 1596) := by
      simpa only [x, t, ys_length] using ht.2.2
    have u'3 : u'.basis (Shadow7.e0P (start j) + 3) = (u.basis (Shadow7.e0P (start j) + 3) ^^ u.basis (Shadow7.e0P (start j) + 6)) := by
      rw [hu']; simp only [writeBit, Function.update_self]
    by_cases hfar : Shadow.far (Shadow7.sbP (start j)) 15 z
    · have u'3v : u'.basis (Shadow7.e0P (start j) + 3) = HighBankSum.cross17 (TrueMiddle.d j z) := by
        rw [u'3, u3eq, u6eq, decide_eq_true hfar, if_pos hfar]
        cases HighBankSum.cross17 (TrueMiddle.d j z) <;> rfl
      have hneg : TrueMiddle.neg j z = (HighBankSum.cross17 (TrueMiddle.d j z) && u'.basis 1596) := by
        unfold TrueMiddle.neg
        rw [u96eq, control96 j (Nat.zero_le _) (by omega), math.2.2 hfar]
      have xAdj : x = HighBankAdjust.adjusted (Shadow.high (Shadow7.sbP (start j)) 15 z) (Shadow7.wpP (start j))
          (HighBankSum.cross17 (TrueMiddle.d j z)) (TrueMiddle.neg j z) := by
        rw [xEq, yEq, h.bank, if_pos hfar, u'3v, hneg]
        exact (HighBankSum.adjusted_gate _ _ _ _ (by have := h.room; omega)).symm
      have law := LeaveJ7.Far.far_result (Shadow7.sbP (start j)) (Shadow7.wpP (start j)) z ⟨h.farSmall, h.endSmall⟩ hfar h.odd h.room
      change TrueMiddle.d j z + 1 = (HighBankSum.cross17 (TrueMiddle.d j z)).toNat + 2*(!TrueMiddle.neg j z).toNat ∧
        TrueMiddle.F j z = 2^(TrueMiddle.key j z).val * HighBankAdjust.adjusted (Shadow.high (Shadow7.sbP (start j)) 15 z) (Shadow7.wpP (start j))
          (HighBankSum.cross17 (TrueMiddle.d j z)) (TrueMiddle.neg j z) + TrueMiddle.X j z % 2^(TrueMiddle.key j z).val at law
      let k0 := TrueMiddle.key j z
      have hslot : slot.val - 1 = k0.val := by
        obtain ⟨tb1, tb2⟩ := tag_bounds k0
        have h1 : u.basis (tagsP.getD k0.val 0) = decide (slot.val = k0.val + 1) :=
          (ut _ tb1 tb2).trans (hot k0)
        have h2 : u.basis (tagsP.getD k0.val 0) = true := by
          rw [u_eq_u0 _ (by unfold Wire at *; omega), sym, loaded_tags j (Nat.zero_le _) (by omega) z a.basis _ (LeaveJ7.tags_mem k0.val k0.isLt), if_pos hfar]
          simp [LeaveJ7.hot, k0]
        have heq : slot.val = k0.val + 1 := of_decide_eq_true (h1.symm.trans h2)
        omega
      have bw15 : 15 ≤ barrelWidth (start j) := (Packed.table_checked _ (usedWidth j lo hi)).1
      have k0lt : k0.val < 16 := k0.isLt
      have hmul : 2^k0.val * x < 2^k0.val * 2^(barrelWidth (start j) - k0.val) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
        have hle : 2^k0.val * x ≤ TrueMiddle.F j z := by rw [law.2, xAdj]; exact Nat.le_add_right _ _
        exact lt_of_le_of_lt hle (by
          have hbw : barrelWidth (start j) = Shadow7.liveW (start j) := rfl
          rw [hbw]; exact h.fit)
      rw [hslot]
      exact Nat.lt_of_mul_lt_mul_left hmul
    · have x0 : x = 0 := by
        rw [xEq, yEq, h.bank, if_neg hfar, u'3, u3eq, u6eq, decide_eq_false hfar, if_neg hfar]
        unfold HighBankAdjust.adjusted
        cases u'.basis 1596 <;> simp
      rw [x0]
      exact Nat.two_pow_pos _
  refine ⟨slot,x,small,narrow,?_,?_,?_,?_⟩
  · intro i ii
    by_cases low : i < Shadow7.wpP (start j)
    · rw [←ys_getD j i low]
      exact HighBankAdjust.bit_read (ys j) i t.basis (by rwa [ys_length])
    · rw [Nat.testBit_lt_two_pow (small.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
      have loc := Shadow7.bank_cases (i := i) w1 (by omega) ii
      exact (unchanged _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)).trans (h.padding i (by omega) ii)
  · intro k
    rw [tag_lookup]
    obtain ⟨a,b⟩ := tag_bounds k
    exact (ht.2.1 (tagsP.getD k.val 0) (absent _ (by unfold Wire at *; omega) (by unfold Wire at *; omega))).trans
      ((preq _ (by unfold Wire at *; omega)).trans ((ut _ a b).trans (hot k)))
  · intro i ii
    have pc := Shadow7.pool_cases (i := 17+i) w1 (by omega)
    have hclean := crt_pool_clean j (by omega) ⟨i, ii⟩
    dsimp only at hclean
    rcases hclean with hmem | hlow
    · have mem : Shadow7.poolW (start j) (17+i) ∈ carries j := by
        simp only [carries, List.mem_map, List.mem_range]
        exact ⟨17+i, hmem, rfl⟩
      refine (ht.2.1 _ ?_).trans (clean _ mem)
      rintro hit
      obtain ⟨k,kk,e⟩ := List.mem_map.mp hit
      have lim := List.mem_range.mp kk
      have loc := Shadow7.bank_cases (i := k) w1 (by omega) (by omega)
      unfold Wire at *
      omega
    · exact (unchanged _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)).trans
        (native_carryJ j (Nat.zero_le _) (by omega) _ s h.ready h.top h.top2 _
          (by unfold Wire at *; omega) (by unfold Wire at *; omega))
  · exact (unchanged 1613 (by decide) (by unfold Wire at *; omega)).trans
      (native_carryJ j (Nat.zero_le _) (by omega) _ s h.ready h.top h.top2 1613 (by decide) (by unfold Wire at *; omega))

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveCut
end

-- ---- CRTLeaveAdapter ----
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveCut
open Partial GateMirror LeaveJ7
attribute [local irreducible] run
set_option maxHeartbeats 1200000

private def pattern (slot : Fin 17) (q : Wire) : Bool :=
  (List.range 16).any (fun k => decide (slot.val=k+1 ∧ q=tagsP.getD k 0))

private theorem at_tag : ∀ slot : Fin 17, ∀ k : Fin 16,
    pattern slot (tagsP.getD k.val 0) = decide (slot.val=k.val+1) := by decide +kernel

private theorem tag_covered : ∀ q ∈ tagsP, ∃ k : Fin 16, q=tagsP.getD k.val 0 := by decide +kernel

private theorem selected_bits : ∀ slot : Fin 17,
    HighBankControl.parity (pattern slot) controlsP0 = (slot.val-1).testBit 0 ∧
    HighBankControl.parity (pattern slot) controlsP1 = (slot.val-1).testBit 1 ∧
    HighBankControl.parity (pattern slot) controlsP2 = (slot.val-1).testBit 2 ∧
    HighBankControl.parity (pattern slot) controlsP3 = (slot.val-1).testBit 3 := by decide +kernel

theorem unique {w : Nat → Wire} {len v : Nat} {s x y : State}
    (a : HighBankBarrel.Result w len v s x) (b : HighBankBarrel.Result w len v s y) : x=y := by
  apply State.extensionality _ _ (a.phase.trans b.phase.symm)
  funext q
  by_cases occurs : ∃ i < len, q=w i
  · obtain ⟨i,hi,rfl⟩ := occurs
    exact (a.bits i hi).trans (b.bits i hi).symm
  · have outer : HighBankBarrel.outside w len q := fun i hi eq => occurs ⟨i,hi,eq⟩
    exact (a.frame q outer).trans (b.frame q outer).symm

/-- A replacement at the prepared cut has the stock forward state and undoes it on every tape. -/
theorem barrel_pair (j : Fin 26) (lo : 0≤j.val) (hi : j.val≤24) (s : State) (h : Admissible j s) :
    (∀ m, run (barrel (start j) false) m s = run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] s) ∧
    (∀ n, run (barrel (start j) true) n (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] s) = s) := by
  obtain ⟨slot,v,small,narrow,bank,tags,scratch,cold⟩ := h
  let key : Fin 16 := ⟨slot.val-1,by have := slot.isLt; omega⟩
  have bw_le : barrelWidth (start j) ≤ Shadow7.wpP (start j) + 15 := barrelWidth_le j lo hi
  have bw15 : 15 ≤ barrelWidth (start j) := (Packed.table_checked _ (usedWidth j lo hi)).1
  have v_lt_bw : v < 2^(barrelWidth (start j)) :=
    lt_of_lt_of_le narrow (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le _ _))
  have vshift_lt_bw : v <<< (slot.val - 1) < 2^(barrelWidth (start j)) := by
    have hsl : slot.val < 17 := slot.isLt
    rw [Nat.shiftLeft_eq]
    calc v * 2^(slot.val - 1) < 2^(barrelWidth (start j) - (slot.val - 1)) * 2^(slot.val - 1) :=
          Nat.mul_lt_mul_of_pos_right narrow (Nat.two_pow_pos _)
      _ = 2^(barrelWidth (start j)) := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have lift (w0 : Nat) (st0 st1 : State) (hw0 : w0 < 2^(barrelWidth (start j)))
      (hi0 : ∀ i, barrelWidth (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → st0.basis (Shadow7.bankW (start j) i) = false)
      (res : HighBankBarrel.Result (Shadow7.bankW (start j)) (barrelWidth (start j)) w0 st0 st1) :
      HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) w0 st0 st1 := by
    obtain ⟨w1, w2⟩ := start_win7 j (Nat.zero_le _) (by omega)
    refine ⟨?_, res.phase, ?_⟩
    · intro i hi'
      by_cases hlt : i < barrelWidth (start j)
      · exact res.bits i hlt
      · have hout : HighBankBarrel.outside (Shadow7.bankW (start j)) (barrelWidth (start j)) (Shadow7.bankW (start j) i) := by
          intro k hk heq
          have := Shadow7.bank_inj w1 (by omega) hi' (Nat.lt_of_lt_of_le hk bw_le) heq
          omega
        rw [res.frame _ hout, hi0 i (by omega) hi',
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hw0 (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    · intro q hq
      exact res.frame q (fun i hi' heq => hq i (Nat.lt_of_lt_of_le hi' bw_le) heq)
  have same (xs : List Wire) (sub : ∀ q∈xs, q∈tagsP) :
      HighBankControl.parity s.basis xs = HighBankControl.parity (pattern slot) xs := by
    apply HighBankBarrel.parity_congr
    intro q hq
    obtain ⟨k,rfl⟩ := tag_covered q (sub q hq)
    rw [←tag_lookup k]
    exact (tags k).trans (by rw [tag_lookup,at_tag])
  obtain ⟨t0,t1,t2,t3⟩ := controls_tags
  obtain ⟨b0,b1,b2,b3⟩ := selected_bits slot
  let out := run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] s
  have old : HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j)+15) (v <<< (slot.val-1)) s out :=
    barrel_bits j (Nat.zero_le _) (by omega) key v s [] small bank cold ((same _ t0).trans b0) ((same _ t1).trans b1)
      ((same _ t2).trans b2) ((same _ t3).trans b3)
  constructor
  · intro m
    have bank_bw : HighBankBarrel.holds (Shadow7.bankW (start j)) (barrelWidth (start j)) (v <<< entryShift false slot.val) s :=
      fun i hi' => by simpa [entryShift] using bank i (Nat.lt_of_lt_of_le hi' bw_le)
    have hi_s : ∀ i, barrelWidth (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false :=
      fun i hge hi' => (bank i hi').trans (Nat.testBit_lt_two_pow (lt_of_lt_of_le v_lt_bw (Nat.pow_le_pow_right (by decide : 0 < 2) hge)))
    have res := barrel_result j lo (by omega) false slot v s m narrow bank_bw tags scratch
    exact unique (lift _ s _ vshift_lt_bw hi_s (by simpa only [exitShift,Bool.false_eq_true,if_false] using res)) old
  · intro n
    obtain ⟨w1,w2⟩ := start_win7 j (Nat.zero_le _) (by omega)
    have geom := Shadow7.rail_win w1 (by omega)
    have away (q : Wire) (l : 1043 < q) (u : q < Shadow7.e0P (start j)) (band : q<1598 ∨ 1612<q) :
        HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j)+15) q := by
      intro i hi eq
      have loc := Shadow7.bank_cases (i := i) w1 (by omega) hi
      unfold Wire at *
      omega
    have ot (k : Fin 16) : out.basis (tagsP.getD k.val 1560) = decide (slot.val=k.val+1) := by
      have bounds := LeaveJ7.tags_range' _ (LeaveJ7.tags_mem k.val k.isLt)
      rw [←tag_lookup k] at bounds
      exact (old.frame (tagsP.getD k.val 1560) (away _ (by unfold Wire at *; omega) (by unfold Wire at *; omega) (Or.inl (by unfold Wire at *; omega)))).trans (tags k)
    have os (i : Nat) (ii : i<10) : out.basis (Shadow7.poolW (start j) (17+i)) = false := by
      have pc := Shadow7.pool_cases (i := 17+i) w1 (by omega)
      refine (old.frame _ ?_).trans (scratch i ii)
      intro k hk e
      have loc := Shadow7.bank_cases (i := k) w1 (by omega) hk
      unfold Wire at *
      omega
    have old_bw : HighBankBarrel.holds (Shadow7.bankW (start j)) (barrelWidth (start j)) (v <<< entryShift true slot.val) out :=
      fun i hi' => by simpa [entryShift] using old.bits i (Nat.lt_of_lt_of_le hi' bw_le)
    have hi_out : ∀ i, barrelWidth (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → out.basis (Shadow7.bankW (start j) i) = false :=
      fun i hge hi' => (old.bits i hi').trans (Nat.testBit_lt_two_pow (lt_of_lt_of_le vshift_lt_bw (Nat.pow_le_pow_right (by decide : 0 < 2) hge)))
    have restored := barrel_result j lo (by omega) true slot v out n narrow old_bw ot os
    have expected : HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j)+15) v out s :=
      ⟨bank,old.phase.symm,fun q hq => (old.frame q hq).symm⟩
    exact unique (lift _ out _ v_lt_bw hi_out (by simpa [exitShift,out] using restored)) expected

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveCut

-- ==== begin DeadJoin bridge (credited to spariev 65b176b3) ====
namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
open CRTBarrel.LeaveSplice
theorem entry_top_zero {j : Fin 26} (hi : j.val≤24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : LeaveJ7.Admission.Inputs j s z g sg) :
    (run (GateMirror.forward (LeaveJ7.entryOps (start j))) [] s).basis (Shadow7.a0P (start j) - 1 + 16) = false := by
  let u := LeaveJ7.Admission.flags z g sg
  have entry := LeaveJ7.entry_core j (Nat.zero_le _) hi s [] z u.1 u.2
    ⟨h.farSmall,h.endSmall⟩ h.ready h.fresh h.scratch h.temp
    (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ LeaveShadowRails.farKey (Shadow7.sbP (start j)) z = 0)
    (LeaveJ7.glueBound j z u.2 ⟨h.farSmall, h.endSmall⟩)
    (LeaveJ7.RecordedEvents.glueFlag j (Nat.zero_le _) hi s z g sg ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side)
  have tight := LeaveShadowRails.inputTight16 (Shadow7.sbP (start j)) z h.farSmall
  have top := entry.2.2.2.2.2.1 16 (by decide)
  rw [Nat.testBit_lt_two_pow tight] at top
  exact top

theorem admitted_scan_eq {j : Fin 26} (hi : j.val≤24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : LeaveJ7.Admission.Inputs j s z g sg) (m : List Bool) :
    run (GateMirror.forward (DeadScan.fix0M (start j) (Shadow7.sbP (start j)))) m s =
      run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s := by
  let u := LeaveJ7.Admission.flags z g sg
  let a := SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)
  exact DeadScan.fix0M_run j (Nat.zero_le _) hi s m a.u a.v u.1 u.2 h.ready


theorem crt_all_pair {j : Fin 26} (hi : j.val≤24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : LeaveJ7.Admission.Inputs j s z g sg)
    (original : Valid s (referenceOps (start j))) :
    (∀ m,run (GateMirror.forward (ScanRowGordo.before5Row (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (after7K (start j))) m s=
      run (GateMirror.forward (referenceOps (start j))) m s) ∧
    (∀ m n,run (GateMirror.inverse (after7K (start j)) ++ CRTBarrel.barrel (start j) true ++
        GateMirror.inverse (ScanRowGordo.before5Row (start j))) n
      (run (GateMirror.forward (ScanRowGordo.before5Row (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (after7K (start j))) m s)=s) := by
  have raw : RawValid s (referenceOps (start j)) := ⟨original.physical,original.prepared,original.ready⟩
  have rel : FlagLeave.Rel (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) (Shadow7.e0P (start j)+6) false s := by
    simp only [FlagLeave.Rel,Bool.false_and,Bool.xor_false]
    rw [h.far,h.side]
    cases decide (Shadow.far (Shadow7.sbP (start j)) 15 z) <;>
      cases decide (2^Shadow7.sbP (start j)≤z.u) <;> rfl
  have zero6 : s.basis (Shadow7.e0P (start j)+6) = false := h.zero _ (by simp [LeaveJ7.watched])
  obtain ⟨bf,br⟩ := CRTBarrel.LeaveCut.barrel_pair j (Nat.zero_le _) hi _
    (CRTBarrel.LeaveCut.input (Nat.zero_le _) hi h)
  have keptRel : KeptParity.relation (fun q => (run (GateMirror.forward (CRTBarrel.beforeReference (start j) ++
      (Shadow7.leaveBarrel (start j) ++ keptHead (start j)))) [] s).basis (KeptParity.port (start j) q)) := by
    have shape : CRTBarrel.beforeReference (start j) ++ (Shadow7.leaveBarrel (start j) ++ keptHead (start j)) =
        Shadow7.moveA (start j) ++ (GateMirror.rowGates (Shadow7.e0P (start j) + 6) (Shadow7.moveRows (start j)) ++
          Shadow7.moveB (start j)) := by
      simp only [CRTBarrel.beforeReference, keptHead, Shadow7.leaveFix5Move, Shadow7.moveA, Shadow7.moveB, List.append_assoc]
    rw [shape]
    exact h.movedRelation (Nat.zero_le _) hi
  obtain ⟨fwd5, rev5⟩ := raw_crt_all_pair57 j hi s raw (pair_zero j hi s (entry_top_zero hi h))
    (admitted_scan_eq hi h) rel zero6 bf br keptRel
  have small := (LeaveShadowRails.inputRow14 (Shadow7.sbP (start j)) z h.farSmall).1
  have hbr : Proper (CRTBarrel.beforeReference (start j)) := by
    intro g hg
    apply original.physical
    have href : referenceOps (start j) = CRTBarrel.beforeReference (start j) ++ (Shadow7.leaveBarrel (start j) ++ afterReference (start j)) := by
      simp only [referenceOps, CRTBarrel.beforeReference, afterReference, List.append_assoc]
    rw [href]
    exact List.mem_append_left _ hg
  have phys5 : ∀ g ∈ before5 (start j), proper g = true :=
    before5_proper j hi (FlagLeave.cut_proper _ _ _ _ _ (before_scan_proper _ hbr))
  exact ScanRowGordo.before5Row_pair j hi s _ _ _ _ h.ready h.fresh small phys5 raw.default_run fwd5 rev5

end ECDSAAdd.Entrant.StairPacket.DeadJoin
-- ==== end DeadJoin bridge ====

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission
open Partial GateMirror CRTBarrel

/-- Forward equality and inverse restoration for the actual moved leave, including its
measurement offsets. The two tapes are independent. -/
theorem Inputs.crt_pair20 {j : Fin 26} (lo : 0≤j.val) (hi : j.val≤24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : Inputs j s z g sg) :
    (∀ m, run (CRTBarrel.leave j) m s = run (Shadow7.leaveP j) m s) ∧
    (∀ m n, run (CRTBarrel.unleave j) n (run (CRTBarrel.leave j) m s) = s) := by
  have original : LeaveSplice.Valid s (DeadJoin.referenceOps (start j)) := by
    change LeaveSplice.Valid s (Shadow7.leaveMoveOps (start j))
    exact LeaveSplice.moved_valid lo hi h
  obtain ⟨f,r⟩ := DeadJoin.crt_all_pair hi h original
  refine ⟨?_,?_⟩
  · intro m
    rw [CRTBarrel.leave,if_pos hi]
    exact (f m).trans (h.sameMove lo hi m)
  · simpa only [CRTBarrel.leave,CRTBarrel.unleave,if_pos hi,CRTBarrel.before,CRTBarrel.afterPart] using r

/-- `crt_pair20` on the whole 24-block window: the CRT barrel leave on every block 0..23. -/
theorem Inputs.crt_pair {j : Fin 26} (lo : 0≤j.val) (hi : j.val≤24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : Inputs j s z g sg) :
    (∀ m, run (CRTBarrel.leave j) m s = run (Shadow7.leaveP j) m s) ∧
    (∀ m n, run (CRTBarrel.unleave j) n (run (CRTBarrel.leave j) m s) = s) :=
  h.crt_pair20 lo hi

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission
end

-- ---- CRTWindowFrame ----
section
/-! The CRT leave's narrow footprint (astra-window's draft, fixed by leave-move): every wire of the placed CRT barrel
is a bank wire, a tag or one of the ten CRT work bits (the pool carries `Shadow7.poolW s (17+k)`), all inside
`Shadow7.leaveBox2`; with the move leave's
footprint around it (`Shadow7.leaveOps_box2` via `allW_leaveMove`), `CRTBarrel.leave` keeps every wire outside the box,
with the signature of `LeaveJ7.leaveMove_keeps`. -/

namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option maxRecDepth 10000

theorem barrel_box2 (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool) :
    ∀ q ∈ wires (CRTBarrel.barrel (start j) mir), Shadow7.leaveBox2 (start j) q := by
  obtain ⟨w1, w2⟩ := start_win7 j (Nat.zero_le _) (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ :=
    Shadow7.rail_win w1 (by omega)
  intro q hq
  rcases CRTBarrel.barrel_wires j lo hi mir q hq with ⟨i, bound, rfl⟩ | ⟨k, hk, rfl⟩ | tag
  · rcases Shadow7.bank_cases w1 (by omega) bound with ⟨a, e⟩ | ⟨a, b, e, c, d⟩ | ⟨a, e, c⟩
    · rw [e]; apply Shadow7.box2_S w1 (by omega) <;> (try unfold Wire at *) <;> omega
    · rw [e]; apply Shadow7.box2_B w1 (by omega) <;> (try unfold Wire at *) <;> omega
    · rw [e]; apply Shadow7.box2_S w1 (by omega) <;> (try unfold Wire at *) <;> omega
  · have pc := Shadow7.pool_cases (i := 17+k) w1 (by omega)
    apply Shadow7.box2_S w1 (by omega) <;> (try unfold Wire at *) <;> omega
  · have bounds : ∀ w ∈ tagsP, 1556 ≤ w ∧ w ≤ 1576 := by decide
    obtain ⟨t1, t2⟩ := bounds q tag
    apply Shadow7.box2_S w1 (by omega) <;> (try unfold Wire at *) <;> omega

/-- `LeaveJ7.leaveMove_keeps` for the CRT leave: a wire outside `Shadow7.leaveBox2` keeps its value. -/
theorem leave_keeps20 (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (q : Wire)
    (outside : ¬ Shadow7.leaveBox2 (start j) q) (m : List Bool) (s : State) :
    (run (CRTBarrel.leave j) m s).basis q = s.basis q := by
  apply run_preserves_outside
  intro hit
  have pieces : AllW (Shadow7.leaveBox2 (start j)) (Shadow7.leaveMoveOps (start j)) :=
    Shadow7.allW_leaveMove (start j) (Shadow7.leaveOps_box2 j (Nat.zero_le _) (by omega))
  rw [split_ops, allW_append_iff, allW_append_iff] at pieces
  have preAll : AllW (Shadow7.leaveBox2 (start j)) (DeadJoin.beforeAll (start j)) :=
    FlagLeave.cut_allW (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 2 (DeadJoin.beforeScan (start j)) (DeadJoin.before_scan_allW _ pieces.1)
  have postAll : AllW (Shadow7.leaveBox2 (start j)) (DeadJoin.afterAll (start j)) :=
    FlagLeave.cut_allW (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 1 (DeadJoin.afterShort (start j)) (DeadJoin.after_short_allW j hi pieces.2.2)
  have pre : ∀ w ∈ wires (GateMirror.forward (CRTBarrel.before (start j))), Shadow7.leaveBox2 (start j) w :=
    (allW_programs (P := Shadow7.leaveBox2 (start j)) (ops := CRTBarrel.before (start j)) (ScanRowGordo.before5Row_allW j hi (DeadJoin.before5_allW j hi preAll))).1
  have post : ∀ w ∈ wires (GateMirror.forward (CRTBarrel.afterPart (start j))), Shadow7.leaveBox2 (start j) w :=
    (allW_programs (P := Shadow7.leaveBox2 (start j)) (ops := CRTBarrel.afterPart (start j)) (DeadJoin.after7K_allW j hi postAll)).1
  have bb : ∀ w ∈ wires (CRTBarrel.barrel (start j) false), Shadow7.leaveBox2 (start j) w :=
    barrel_box2 j lo hi false
  rw [(leave_eq j lo hi).1] at hit
  generalize GateMirror.forward (CRTBarrel.before (start j)) = A at hit pre
  generalize CRTBarrel.barrel (start j) false = B at hit bb
  generalize GateMirror.forward (CRTBarrel.afterPart (start j)) = C at hit post
  rw [wires_append, wires_append] at hit
  rcases Finset.mem_union.mp hit with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact outside (pre q h)
    · exact outside (bb q h)
  · exact outside (post q h)

/-- `leave_keeps20` on the whole 22-block window (`LeaveJ7.leaveMove_keeps` for `CRTBarrel.leave`): the CRT barrel
leave on every block 1..22 (the move-leave branch is vacuous). -/
theorem leave_keeps (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (q : Wire)
    (outside : ¬ Shadow7.leaveBox2 (start j) q) (m : List Bool) (s : State) :
    (run (CRTBarrel.leave j) m s).basis q = s.basis q :=
  leave_keeps20 j lo hi q outside m s

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

/- Inlined from ShadowChain; provenance retained from022799f6. -/
section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveJ7
open Arithmetic Partial

theorem head_port_eq (j : Fin 26) (i : Fin 16) :
    ArchiveJ.codePorts j ⟨i.val, by omega⟩ = ArchiveJ7.codePorts j ⟨i.val, by omega⟩ := by
  have hi : i.val < (cellsRestoreP (start j + 15)).length := by
    have h : (cellsRestoreP (start j + 15)).length = 16 := by simp [cellsRestoreP]
    rw [h]
    exact i.isLt
  simp only [ArchiveJ.codePorts, ArchiveJ7.codePorts, ArchiveJ.code_split, ArchiveJ7.code_split, List.append_assoc]
  rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]

theorem kept_stock (j : Fin 26) (d : Bool) (row : Nat) (s : State)
    (h : Kept (ArchiveJ7.codePorts j) d row s) : Kept (ArchiveJ.codePorts j) d row s := by
  intro i
  rw [head_port_eq j i]
  exact h i

end ECDSAAdd.Entrant.StairPacket.ArchiveJ7
/-! build-chain: Shadow7 renders of the stock window families ArchiveJ, NativeJ, LeaveJ.ArchiveCut, LeaveJ.AssembleCut, LeaveJ.CertifiedCut, LeaveJ.BodyCut, NativeFirstJ, StockWindowW (helpers/build-chain/shadow/render7.py). -/

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw ArchivePortAction
namespace ArchiveJ7
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-- Source and loader blocks: the archive of block `i` is read from block `i`'s first ten ticks and loaded inside
block `i+1` (`next`). -/
def next (i : Fin 26) (hi : i.val≤24) : Fin 26 := ⟨i.val+1,by omega⟩
theorem chronological_all : ∀ i : Fin 26, i.val≤24 → ∀k:Fin 20, rawPorts i ⟨k,by omega⟩=nativeRawPort i k := by
  decide +kernel
theorem observed (i : Fin 26) (hi : i.val≤24) (before now:State)
    (kept:∀q:Fin 20,now.basis (rawPorts i ⟨q,by omega⟩)=before.basis (rawPorts i ⟨q,by omega⟩))
    (far u c:Bool) (tags:now.basis (rawPorts i 20)=far ∧ now.basis (rawPorts i 21)=u ∧ now.basis (rawPorts i 22)=c) :
    let cells:=readCells (Shadow7.shape i) 0 15 (mappedBasis i before.basis)
    ∀k:Fin 157,k.val<23 → now.basis (rawPorts i k)=rawBit (read (cells.drop 5)) far u c k := by
  dsimp only
  intro k bound
  by_cases young:k.val<20
  · let col:Fin 20:=⟨k,young⟩
    refine (kept col).trans ?_
    rw [chronological_all i hi col]
    exact (Shadow7.native_raw_read i before k young).trans (by simp [rawBit,young])
  · have eq:k=20 ∨ k=21 ∨ k=22:=by omega
    rcases eq with rfl|rfl|rfl
    · exact tags.1
    · exact tags.2.1
    · exact tags.2.2
end ArchiveJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Generic native pack of block `j` (par-c2): the stock pack at tick `s-10` (`s = start j`) in the `OB5.sig s`
frame, then the window archive of block `j-1` (`Shadow7.archiveLoadP (prev j)`). dadon's `NativePack{s}` is
`NativeJ` at `j = (s-75)/15`. Valid for `2 ≤ j` (the pack is due: `s-10 ≥ 95`, `s-10 ≡ 0 mod 5`). -/

def prev (j : Fin 26) : Fin 26 := ⟨j.val-1,by omega⟩
def program (j : Fin 26) (d:Bool) := renameProgram (OB5.sig (start j)) (Rolling1588.packAtTick d (start j-10))
def reverse (j : Fin 26) (d:Bool) := renameProgram (OB5.sig (start j)) (Rolling1588.unpackAtTick d (start j-10))
def support (j : Fin 26) :=
  (List.range' (start j-15) 5).flatMap fun v=>[OB5.sig (start j) (base v),OB5.sig (start j) (base (1028+v))]
def history (j : Fin 26) (q:Fin 10) := OB5.sig (start j) (History5.historyMap base (start j-15) q)

theorem due (j : Fin 26) (h : 1≤j.val) : ¬start j-10=5 ∧ History5.packDue (start j-10)=true ∧
    start j-10-5=start j-15 := by
  have hj:=j.isLt
  simp only [History5.packDue,start,decide_eq_true_eq]
  omega

theorem equals (j : Fin 26) (h : 1≤j.val) (d:Bool) :
    program j d=Rolling1588.codeEncodeAt d (history j) ∧ reverse j d=Rolling1588.codeDecodeAt d (history j) := by
  obtain ⟨n5,dueP,sub⟩:=due j (by omega)
  have lab : ∀ q∈Finset.range 10, (OB5.sig (start j) ∘ MeasuredCodec5.label (History5.historyMap base (start j-15))) q=
      MeasuredCodec5.label (history j) q := by
    intro q hq
    have lt:=Finset.mem_range.mp hq
    simp only [Function.comp,MeasuredCodec5.label,history,dif_pos lt]
  constructor
  · unfold program Rolling1588.packAtTick Rolling1588.codeEncodeAt
    rw [if_neg n5,if_pos dueP,sub,renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    rw [(Rolling1588.code_support d).1] at hq
    exact lab q hq
  · unfold reverse Rolling1588.unpackAtTick Rolling1588.codeDecodeAt
    rw [if_neg n5,if_pos dueP,sub,renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    rw [(Rolling1588.code_support d).2] at hq
    exact lab q hq

theorem history_mem (j : Fin 26) (q:Fin 10) : history j q∈support j := by
  have hq:=q.isLt
  simp only [history,support,History5.historyMap,History5.historyId,List.mem_flatMap,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  refine ⟨start j-15+q.val/2,⟨by omega,by omega⟩,?_⟩
  split
  · exact Or.inl rfl
  · right; congr 2; omega

theorem histInj (j : Fin 26) : Function.Injective (history j) := by
  intro a b eq
  have inv:=OB5.sig_invol (start j) (by have:=j.isLt;simp only [start];omega)
  have e:=congrArg (OB5.sig (start j)) eq
  simp only [history,inv,History5.historyMap,History5.historyId,base] at e
  have ha:=a.isLt; have hb:=b.isLt
  apply Fin.ext
  split at e <;> split at e <;> simp only [Wire] at * <;> omega

theorem codes (j : Fin 26) (h : 1≤j.val) (d:Bool) :
    wires (program j d)⊆(support j).toFinset ∧ wires (reverse j d)⊆(support j).toFinset := by
  rw [(equals j (by omega) d).1,(equals j (by omega) d).2,Rolling1588.codeEncodeAt,Rolling1588.codeDecodeAt,
    renameProgram_support,renameProgram_support,(Rolling1588.code_support d).1,(Rolling1588.code_support d).2]
  have img : Finset.image (MeasuredCodec5.label (history j)) (Finset.range 10)⊆(support j).toFinset := by
    intro q hq
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hq
    have lt:=Finset.mem_range.mp hw
    simp only [MeasuredCodec5.label,dif_pos lt,List.mem_toFinset]
    exact history_mem j ⟨w,lt⟩
  exact ⟨img,img⟩

/-- `watchFree_all` per block (one kernel decide each, so the evaluation state is per block). -/
private theorem watchFree_b0 : (Shadow7.watch (0 : Fin 26)).all (fun q=>decide (q∉support (0 : Fin 26))) := by decide +kernel
private theorem watchFree_b1 : (Shadow7.watch (1 : Fin 26)).all (fun q=>decide (q∉support (1 : Fin 26))) := by decide +kernel
private theorem watchFree_b2 : (Shadow7.watch (2 : Fin 26)).all (fun q=>decide (q∉support (2 : Fin 26))) := by decide +kernel
private theorem watchFree_b3 : (Shadow7.watch (3 : Fin 26)).all (fun q=>decide (q∉support (3 : Fin 26))) := by decide +kernel
private theorem watchFree_b4 : (Shadow7.watch (4 : Fin 26)).all (fun q=>decide (q∉support (4 : Fin 26))) := by decide +kernel
private theorem watchFree_b5 : (Shadow7.watch (5 : Fin 26)).all (fun q=>decide (q∉support (5 : Fin 26))) := by decide +kernel
private theorem watchFree_b6 : (Shadow7.watch (6 : Fin 26)).all (fun q=>decide (q∉support (6 : Fin 26))) := by decide +kernel
private theorem watchFree_b7 : (Shadow7.watch (7 : Fin 26)).all (fun q=>decide (q∉support (7 : Fin 26))) := by decide +kernel
private theorem watchFree_b8 : (Shadow7.watch (8 : Fin 26)).all (fun q=>decide (q∉support (8 : Fin 26))) := by decide +kernel
private theorem watchFree_b9 : (Shadow7.watch (9 : Fin 26)).all (fun q=>decide (q∉support (9 : Fin 26))) := by decide +kernel
private theorem watchFree_b10 : (Shadow7.watch (10 : Fin 26)).all (fun q=>decide (q∉support (10 : Fin 26))) := by decide +kernel
private theorem watchFree_b11 : (Shadow7.watch (11 : Fin 26)).all (fun q=>decide (q∉support (11 : Fin 26))) := by decide +kernel
private theorem watchFree_b12 : (Shadow7.watch (12 : Fin 26)).all (fun q=>decide (q∉support (12 : Fin 26))) := by decide +kernel
private theorem watchFree_b13 : (Shadow7.watch (13 : Fin 26)).all (fun q=>decide (q∉support (13 : Fin 26))) := by decide +kernel
private theorem watchFree_b14 : (Shadow7.watch (14 : Fin 26)).all (fun q=>decide (q∉support (14 : Fin 26))) := by decide +kernel
private theorem watchFree_b15 : (Shadow7.watch (15 : Fin 26)).all (fun q=>decide (q∉support (15 : Fin 26))) := by decide +kernel
private theorem watchFree_b16 : (Shadow7.watch (16 : Fin 26)).all (fun q=>decide (q∉support (16 : Fin 26))) := by decide +kernel
private theorem watchFree_b17 : (Shadow7.watch (17 : Fin 26)).all (fun q=>decide (q∉support (17 : Fin 26))) := by decide +kernel
private theorem watchFree_b18 : (Shadow7.watch (18 : Fin 26)).all (fun q=>decide (q∉support (18 : Fin 26))) := by decide +kernel
private theorem watchFree_b19 : (Shadow7.watch (19 : Fin 26)).all (fun q=>decide (q∉support (19 : Fin 26))) := by decide +kernel
private theorem watchFree_b20 : (Shadow7.watch (20 : Fin 26)).all (fun q=>decide (q∉support (20 : Fin 26))) := by decide +kernel
private theorem watchFree_b21 : (Shadow7.watch (21 : Fin 26)).all (fun q=>decide (q∉support (21 : Fin 26))) := by decide +kernel
private theorem watchFree_b22 : (Shadow7.watch (22 : Fin 26)).all (fun q=>decide (q∉support (22 : Fin 26))) := by decide +kernel
private theorem watchFree_b23 : (Shadow7.watch (23 : Fin 26)).all (fun q=>decide (q∉support (23 : Fin 26))) := by decide +kernel
private theorem watchFree_b24 : (Shadow7.watch (24 : Fin 26)).all (fun q=>decide (q∉support (24 : Fin 26))) := by decide +kernel
private theorem watchFree_b25 : (Shadow7.watch (25 : Fin 26)).all (fun q=>decide (q∉support (25 : Fin 26))) := by decide +kernel
theorem watchFree_all : ∀ j : Fin 26, (Shadow7.watch j).all (fun q=>decide (q∉support j)) := by
  intro j
  fin_cases j
  · exact watchFree_b0
  · exact watchFree_b1
  · exact watchFree_b2
  · exact watchFree_b3
  · exact watchFree_b4
  · exact watchFree_b5
  · exact watchFree_b6
  · exact watchFree_b7
  · exact watchFree_b8
  · exact watchFree_b9
  · exact watchFree_b10
  · exact watchFree_b11
  · exact watchFree_b12
  · exact watchFree_b13
  · exact watchFree_b14
  · exact watchFree_b15
  · exact watchFree_b16
  · exact watchFree_b17
  · exact watchFree_b18
  · exact watchFree_b19
  · exact watchFree_b20
  · exact watchFree_b21
  · exact watchFree_b22
  · exact watchFree_b23
  · exact watchFree_b24
  · exact watchFree_b25
theorem disjoint (j : Fin 26) : ∀q∈support j,q∉Shadow7.watch j :=
  fun q hs hw=>(of_decide_eq_true (List.all_eq_true.mp (watchFree_all j) q hw)) hs

theorem retains (j : Fin 26) (h : 1≤j.val) (d back:Bool) (s:State) (m:List Bool) :
    ∀q∈Shadow7.watch j,(run (if back then reverse j d else program j d) m s).basis q=s.basis q:=by
  intro q hq
  apply run_preserves_outside
  intro used
  have seen:q∈(support j).toFinset:=by
    cases back
    · exact (codes j (by omega) d).1 used
    · exact (codes j (by omega) d).2 used
  exact disjoint j _ (List.mem_toFinset.mp seen) hq

theorem source_law (j : Fin 26) (h : 1≤j.val) (d:Bool) (s:State) (m:List Bool)
    (ok:MeasuredCodec5.legalAt (history j) s.basis) :
    (run (program j d) m s).phase=s.phase ∧ ∀t,run (reverse j d) t (run (program j d) m s)=s:=by
  rw [(equals j (by omega) d).1,(equals j (by omega) d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d (history j) (histInj j) s m ok).1,
    fun t=>Rolling1588.codeRoundtripAt d (history j) (histInj j) s m t ok⟩

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Generic first-form native pack (par-c2): the window's first block `j` (`s = start j`) packs the five
pre-window letters at tick `s` (group `s-5`) in the `OB5.sig s` frame; no archive. dadon's `NativePack225`
(first block of 225..270) is `NativeFirstJ7 10`. -/

def program (j : Fin 26) (d:Bool) := renameProgram (OB5.sig (start j)) (Rolling1588.packAtTick d (start j))
def reverse (j : Fin 26) (d:Bool) := renameProgram (OB5.sig (start j)) (Rolling1588.unpackAtTick d (start j))
def support (j : Fin 26) :=
  (List.range' (start j-5) 5).flatMap fun v=>[OB5.sig (start j) (base v),OB5.sig (start j) (base (1028+v))]
def history (j : Fin 26) (q:Fin 10) := OB5.sig (start j) (History5.historyMap base (start j-5) q)

theorem due (j : Fin 26) (h : 0≤j.val) : ¬start j=5 ∧ History5.packDue (start j)=true := by
  have hj:=j.isLt
  simp only [History5.packDue,start,decide_eq_true_eq]
  omega

theorem equals (j : Fin 26) (h : 0≤j.val) (d:Bool) :
    program j d=Rolling1588.codeEncodeAt d (history j) ∧ reverse j d=Rolling1588.codeDecodeAt d (history j) := by
  obtain ⟨n5,dueP⟩:=due j h
  have lab : ∀ q∈Finset.range 10, (OB5.sig (start j) ∘ MeasuredCodec5.label (History5.historyMap base (start j-5))) q=
      MeasuredCodec5.label (history j) q := by
    intro q hq
    have lt:=Finset.mem_range.mp hq
    simp only [Function.comp,MeasuredCodec5.label,history,dif_pos lt]
  constructor
  · unfold program Rolling1588.packAtTick Rolling1588.codeEncodeAt
    rw [if_neg n5,if_pos dueP,renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    rw [(Rolling1588.code_support d).1] at hq
    exact lab q hq
  · unfold reverse Rolling1588.unpackAtTick Rolling1588.codeDecodeAt
    rw [if_neg n5,if_pos dueP,renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    rw [(Rolling1588.code_support d).2] at hq
    exact lab q hq

theorem history_mem (j : Fin 26) (q:Fin 10) : history j q∈support j := by
  have hq:=q.isLt
  simp only [history,support,History5.historyMap,History5.historyId,List.mem_flatMap,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  refine ⟨start j-5+q.val/2,⟨by omega,by omega⟩,?_⟩
  split
  · exact Or.inl rfl
  · right; congr 2; omega

theorem histInj (j : Fin 26) : Function.Injective (history j) := by
  intro a b eq
  have inv:=OB5.sig_invol (start j) (by have:=j.isLt;simp only [start];omega)
  have e:=congrArg (OB5.sig (start j)) eq
  simp only [history,inv,History5.historyMap,History5.historyId,base] at e
  have ha:=a.isLt; have hb:=b.isLt
  apply Fin.ext
  split at e <;> split at e <;> simp only [Wire] at * <;> omega

theorem codes (j : Fin 26) (h : 0≤j.val) (d:Bool) :
    wires (program j d)⊆(support j).toFinset ∧ wires (reverse j d)⊆(support j).toFinset := by
  rw [(equals j h d).1,(equals j h d).2,Rolling1588.codeEncodeAt,Rolling1588.codeDecodeAt,
    renameProgram_support,renameProgram_support,(Rolling1588.code_support d).1,(Rolling1588.code_support d).2]
  have img : Finset.image (MeasuredCodec5.label (history j)) (Finset.range 10)⊆(support j).toFinset := by
    intro q hq
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hq
    have lt:=Finset.mem_range.mp hw
    simp only [MeasuredCodec5.label,dif_pos lt,List.mem_toFinset]
    exact history_mem j ⟨w,lt⟩
  exact ⟨img,img⟩

/-- `watchFree_all` per block (one kernel decide each, so the evaluation state is per block). -/
private theorem watchFree_b0 : (Shadow7.watch (0 : Fin 26)).all (fun q=>decide (q∉support (0 : Fin 26))) := by decide +kernel
private theorem watchFree_b1 : (Shadow7.watch (1 : Fin 26)).all (fun q=>decide (q∉support (1 : Fin 26))) := by decide +kernel
private theorem watchFree_b2 : (Shadow7.watch (2 : Fin 26)).all (fun q=>decide (q∉support (2 : Fin 26))) := by decide +kernel
private theorem watchFree_b3 : (Shadow7.watch (3 : Fin 26)).all (fun q=>decide (q∉support (3 : Fin 26))) := by decide +kernel
private theorem watchFree_b4 : (Shadow7.watch (4 : Fin 26)).all (fun q=>decide (q∉support (4 : Fin 26))) := by decide +kernel
private theorem watchFree_b5 : (Shadow7.watch (5 : Fin 26)).all (fun q=>decide (q∉support (5 : Fin 26))) := by decide +kernel
private theorem watchFree_b6 : (Shadow7.watch (6 : Fin 26)).all (fun q=>decide (q∉support (6 : Fin 26))) := by decide +kernel
private theorem watchFree_b7 : (Shadow7.watch (7 : Fin 26)).all (fun q=>decide (q∉support (7 : Fin 26))) := by decide +kernel
private theorem watchFree_b8 : (Shadow7.watch (8 : Fin 26)).all (fun q=>decide (q∉support (8 : Fin 26))) := by decide +kernel
private theorem watchFree_b9 : (Shadow7.watch (9 : Fin 26)).all (fun q=>decide (q∉support (9 : Fin 26))) := by decide +kernel
private theorem watchFree_b10 : (Shadow7.watch (10 : Fin 26)).all (fun q=>decide (q∉support (10 : Fin 26))) := by decide +kernel
private theorem watchFree_b11 : (Shadow7.watch (11 : Fin 26)).all (fun q=>decide (q∉support (11 : Fin 26))) := by decide +kernel
private theorem watchFree_b12 : (Shadow7.watch (12 : Fin 26)).all (fun q=>decide (q∉support (12 : Fin 26))) := by decide +kernel
private theorem watchFree_b13 : (Shadow7.watch (13 : Fin 26)).all (fun q=>decide (q∉support (13 : Fin 26))) := by decide +kernel
private theorem watchFree_b14 : (Shadow7.watch (14 : Fin 26)).all (fun q=>decide (q∉support (14 : Fin 26))) := by decide +kernel
private theorem watchFree_b15 : (Shadow7.watch (15 : Fin 26)).all (fun q=>decide (q∉support (15 : Fin 26))) := by decide +kernel
private theorem watchFree_b16 : (Shadow7.watch (16 : Fin 26)).all (fun q=>decide (q∉support (16 : Fin 26))) := by decide +kernel
private theorem watchFree_b17 : (Shadow7.watch (17 : Fin 26)).all (fun q=>decide (q∉support (17 : Fin 26))) := by decide +kernel
private theorem watchFree_b18 : (Shadow7.watch (18 : Fin 26)).all (fun q=>decide (q∉support (18 : Fin 26))) := by decide +kernel
private theorem watchFree_b19 : (Shadow7.watch (19 : Fin 26)).all (fun q=>decide (q∉support (19 : Fin 26))) := by decide +kernel
private theorem watchFree_b20 : (Shadow7.watch (20 : Fin 26)).all (fun q=>decide (q∉support (20 : Fin 26))) := by decide +kernel
private theorem watchFree_b21 : (Shadow7.watch (21 : Fin 26)).all (fun q=>decide (q∉support (21 : Fin 26))) := by decide +kernel
private theorem watchFree_b22 : (Shadow7.watch (22 : Fin 26)).all (fun q=>decide (q∉support (22 : Fin 26))) := by decide +kernel
private theorem watchFree_b23 : (Shadow7.watch (23 : Fin 26)).all (fun q=>decide (q∉support (23 : Fin 26))) := by decide +kernel
private theorem watchFree_b24 : (Shadow7.watch (24 : Fin 26)).all (fun q=>decide (q∉support (24 : Fin 26))) := by decide +kernel
private theorem watchFree_b25 : (Shadow7.watch (25 : Fin 26)).all (fun q=>decide (q∉support (25 : Fin 26))) := by decide +kernel
theorem watchFree_all : ∀ j : Fin 26, (Shadow7.watch j).all (fun q=>decide (q∉support j)) := by
  intro j
  fin_cases j
  · exact watchFree_b0
  · exact watchFree_b1
  · exact watchFree_b2
  · exact watchFree_b3
  · exact watchFree_b4
  · exact watchFree_b5
  · exact watchFree_b6
  · exact watchFree_b7
  · exact watchFree_b8
  · exact watchFree_b9
  · exact watchFree_b10
  · exact watchFree_b11
  · exact watchFree_b12
  · exact watchFree_b13
  · exact watchFree_b14
  · exact watchFree_b15
  · exact watchFree_b16
  · exact watchFree_b17
  · exact watchFree_b18
  · exact watchFree_b19
  · exact watchFree_b20
  · exact watchFree_b21
  · exact watchFree_b22
  · exact watchFree_b23
  · exact watchFree_b24
  · exact watchFree_b25
theorem disjoint (j : Fin 26) : ∀q∈support j,q∉Shadow7.watch j :=
  fun q hs hw=>(of_decide_eq_true (List.all_eq_true.mp (watchFree_all j) q hw)) hs

theorem retains (j : Fin 26) (h : 0≤j.val) (d back:Bool) (s:State) (m:List Bool) :
    ∀q∈Shadow7.watch j,(run (if back then reverse j d else program j d) m s).basis q=s.basis q:=by
  intro q hq
  apply run_preserves_outside
  intro used
  have seen:q∈(support j).toFinset:=by
    cases back
    · exact (codes j h d).1 used
    · exact (codes j h d).2 used
  exact disjoint j _ (List.mem_toFinset.mp seen) hq

theorem source_law (j : Fin 26) (h : 0≤j.val) (d:Bool) (s:State) (m:List Bool)
    (ok:MeasuredCodec5.legalAt (history j) s.basis) :
    (run (program j d) m s).phase=s.phase ∧ ∀t,run (reverse j d) t (run (program j d) m s)=s:=by
  rw [(equals j h d).1,(equals j h d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d (history j) (histInj j) s m ok).1,
    fun t=>Rolling1588.codeRoundtripAt d (history j) (histInj j) s m t ok⟩

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket CodecBitSliceVerify ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace ArchiveJ7
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
theorem scratch_code (i : Fin 26) (k : Fin 157) (h : 23≤k.val) : rawPorts i k=codePorts i ⟨k.val-7,by omega⟩ := by
  have a:=raw_scratch i (k:=k.val-23) (by omega)
  have b:=code_scratch i (k:=k.val-23) (by omega)
  rw [show 23+(k.val-23)=k.val by omega] at a
  rw [show 16+(k.val-23)=k.val-7 by omega] at b
  exact a.trans b.symm
/-- `pastFree_all` per block (one kernel decide each, so the evaluation state is per block). -/
private theorem pastFree_b0 : (if hi : (0 : Fin 26).val≤24 then (Shadow7.watch (next (0 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (0 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b1 : (if hi : (1 : Fin 26).val≤24 then (Shadow7.watch (next (1 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (1 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b2 : (if hi : (2 : Fin 26).val≤24 then (Shadow7.watch (next (2 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (2 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b3 : (if hi : (3 : Fin 26).val≤24 then (Shadow7.watch (next (3 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (3 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b4 : (if hi : (4 : Fin 26).val≤24 then (Shadow7.watch (next (4 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (4 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b5 : (if hi : (5 : Fin 26).val≤24 then (Shadow7.watch (next (5 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (5 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b6 : (if hi : (6 : Fin 26).val≤24 then (Shadow7.watch (next (6 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (6 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b7 : (if hi : (7 : Fin 26).val≤24 then (Shadow7.watch (next (7 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (7 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b8 : (if hi : (8 : Fin 26).val≤24 then (Shadow7.watch (next (8 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (8 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b9 : (if hi : (9 : Fin 26).val≤24 then (Shadow7.watch (next (9 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (9 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b10 : (if hi : (10 : Fin 26).val≤24 then (Shadow7.watch (next (10 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (10 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b11 : (if hi : (11 : Fin 26).val≤24 then (Shadow7.watch (next (11 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (11 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b12 : (if hi : (12 : Fin 26).val≤24 then (Shadow7.watch (next (12 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (12 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b13 : (if hi : (13 : Fin 26).val≤24 then (Shadow7.watch (next (13 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (13 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b14 : (if hi : (14 : Fin 26).val≤24 then (Shadow7.watch (next (14 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (14 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b15 : (if hi : (15 : Fin 26).val≤24 then (Shadow7.watch (next (15 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (15 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b16 : (if hi : (16 : Fin 26).val≤24 then (Shadow7.watch (next (16 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (16 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b17 : (if hi : (17 : Fin 26).val≤24 then (Shadow7.watch (next (17 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (17 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b18 : (if hi : (18 : Fin 26).val≤24 then (Shadow7.watch (next (18 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (18 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b19 : (if hi : (19 : Fin 26).val≤24 then (Shadow7.watch (next (19 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (19 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b20 : (if hi : (20 : Fin 26).val≤24 then (Shadow7.watch (next (20 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (20 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b21 : (if hi : (21 : Fin 26).val≤24 then (Shadow7.watch (next (21 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (21 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b22 : (if hi : (22 : Fin 26).val≤24 then (Shadow7.watch (next (22 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (22 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b23 : (if hi : (23 : Fin 26).val≤24 then (Shadow7.watch (next (23 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (23 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b24 : (if hi : (24 : Fin 26).val≤24 then (Shadow7.watch (next (24 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (24 : Fin 26))) else true)=true := by
  decide +kernel
private theorem pastFree_b25 : (if hi : (25 : Fin 26).val≤24 then (Shadow7.watch (next (25 : Fin 26) hi)).all (fun q=>decide (q∉rawHead (25 : Fin 26))) else true)=true := by
  decide +kernel
theorem pastFree_all : ∀ i : Fin 26,
    (if hi : i.val≤24 then (Shadow7.watch (next i hi)).all (fun q=>decide (q∉rawHead i)) else true)=true := by
  intro i
  fin_cases i
  · exact pastFree_b0
  · exact pastFree_b1
  · exact pastFree_b2
  · exact pastFree_b3
  · exact pastFree_b4
  · exact pastFree_b5
  · exact pastFree_b6
  · exact pastFree_b7
  · exact pastFree_b8
  · exact pastFree_b9
  · exact pastFree_b10
  · exact pastFree_b11
  · exact pastFree_b12
  · exact pastFree_b13
  · exact pastFree_b14
  · exact pastFree_b15
  · exact pastFree_b16
  · exact pastFree_b17
  · exact pastFree_b18
  · exact pastFree_b19
  · exact pastFree_b20
  · exact pastFree_b21
  · exact pastFree_b22
  · exact pastFree_b23
  · exact pastFree_b24
  · exact pastFree_b25
theorem past_only (i : Fin 26) (hi : i.val≤24) : ∀k:Fin 23, rawPorts i ⟨k,by omega⟩∉Shadow7.watch (next i hi) := by
  intro k hw
  have all:=pastFree_all i
  rw [dif_pos hi] at all
  have off:=of_decide_eq_true (List.all_eq_true.mp all _ hw)
  apply off
  have e:rawPorts i ⟨k,by omega⟩=(rawHead i).getD k 0:=by
    rw [rawPorts,raw_split,List.getD_append _ _ _ _ (by simp [rawHead,cellsLoadP])]
  rw [e,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp [rawHead,cellsLoadP]),Option.getD_some]
  exact List.getElem_mem _
/-- `ArchiveBoundary{t}.retain_watch`, generic: the load keeps every watched wire of the loader block, given that the
watched scratch wires are clean before the load (dadon: carry wires; late blocks: also future history ports). -/
theorem retain_watch (i : Fin 26) (hi : i.val≤24) (d:Bool) (row:Nat) (s t:State)
    (clean:∀k:Fin 157,23≤k.val → rawPorts i k∈Shadow7.watch (next i hi) → s.basis (rawPorts i k)=false)
    (frame:Frame (codePorts i) (code d) row t)
    (outside:∀q,(∀k,rawPorts i k≠q) → t.basis q=s.basis q) :
    ∀q∈Shadow7.watch (next i hi),t.basis q=s.basis q := by
  intro q h
  by_cases mem:∃k,rawPorts i k=q
  · obtain ⟨k,rfl⟩:=mem
    have hk:23≤ k.val:=by
      by_contra! bad
      exact past_only i hi ⟨k,bad⟩ h
    rw [clean k hk h,scratch_code i k hk,frame,archive_blank _ _ (by dsimp;omega),Nat.zero_testBit]
  · exact outside _ (fun k eq=>mem ⟨k,eq⟩)
end ArchiveJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run Shadow7.unrouted Shadow7.onRails
namespace NativeJ7
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-- Block `j`'s administrative piece: the pack, then the window archive of block `j-1`. -/
def withArchive (j : Fin 26) (d:Bool) := program j d++Shadow7.archiveLoadP (prev j) d
def fromArchive (j : Fin 26) (d:Bool) := Shadow7.archiveRestoreP (prev j) d++reverse j d
theorem next_prev (j : Fin 26) (h3 : 1≤j.val) (h19 : j.val≤24) : ArchiveJ7.next (prev j) (by simp only [prev]; omega)=j := by
  apply Fin.ext; simp only [ArchiveJ7.next,prev]; omega

theorem admin (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State)
    (active:Shadow7.onRails j 1 z s.basis) (ok:MeasuredCodec5.legalAt (history j) s.basis)
    (row:Nat) (limit:row<63145)
    (raw:Frame (ArchiveJ7.rawPorts (prev j)) ArchivePortAction.raw row (run (program j d) m s))
    (clean:∀k:Fin 157,23≤k.val → ArchiveJ7.rawPorts (prev j) k∈Shadow7.watch j →
      (run (program j d) m s).basis (ArchiveJ7.rawPorts (prev j) k)=false) :
    let out:=run (withArchive j d) m s
    Shadow7.AdminResult j (fromArchive j d) s out ∧ Frame (ArchiveJ7.codePorts (prev j)) (code d) row out := by
  have hp:(prev j).val≤23:=by simp only [prev]; omega
  have nx:=next_prev j (by omega) h19
  let p:=run (program j d) m s
  let tape:=m.drop (measurementCount (program j d))
  let a:=run (Shadow7.archiveLoadP (prev j) d) tape p
  have old:=source_law j (by omega) d s m ok
  have stay:=retains j (by omega) d false s m
  have now:=Shadow7.watch_congr j s p stay z active
  have arr:=ArchiveJ7.load_run (prev j) (by omega) d row limit p tape raw
  have untouched:=ArchiveJ7.retain_watch (prev j) (by omega) d row p a (by rw [nx]; exact clean) arr.2.1 arr.2.2
  rw [nx] at untouched
  dsimp only [withArchive,fromArchive]
  simp only [run_append,run_take]
  refine ⟨⟨arr.1.trans old.1,fun q h=>(untouched _ h).trans (stay _ h),?_⟩,arr.2.1⟩
  intro n
  rw [run_append,run_take]
  change run (reverse j d) _ (run (Shadow7.archiveRestoreP (prev j) d) _ a)=s
  rw [ArchiveJ7.roundtrip (prev j) (by omega) d row limit p tape _ raw]
  exact old.2 _
end NativeJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
attribute [local irreducible] run Shadow7.unrouted Shadow7.onRails
namespace NativeJ7
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
def window (j : Fin 26) (d:Bool) := Shadow7.body j (withArchive j d)
def unwind (j : Fin 26) (d:Bool) := Shadow7.unbody j (fromArchive j d)
theorem window_run (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (start0:Shadow7.onRails j 0 z s.basis)
    (legal:MeasuredCodec5.legalAt (history j) (run (Shadow7.routed j 0 1) m s).basis)
    (row:Nat) (limit:row<63145) (frame:Frame (ArchiveJ7.rawPorts (prev j)) ArchivePortAction.raw row
      (run (program j d) (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m s)))
    (clean:∀k:Fin 157,23≤k.val → ArchiveJ7.rawPorts (prev j) k∈Shadow7.watch j →
      (run (program j d) (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m s)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false) :
    let out:=run (window j d) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unwind j d) n out=s := by
  apply Shadow7.body_run _ _ _ _ _ z odd start0
  exact (admin j (by omega) h19 d _ _ (SkywalkTrace.next z) (Shadow7.route_frame j 0 1 (by decide) z odd s m start0).2 legal row limit frame clean).1
end NativeJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed IntegerPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
theorem admin (j : Fin 26) (h : 0≤j.val) (d:Bool) (s:State) (m:List Bool) (ok:MeasuredCodec5.legalAt (history j) s.basis) :
    Shadow7.AdminResult j (reverse j d) s (run (program j d) m s) :=
  ⟨(source_law j h d s m ok).1,retains j h d false s m,(source_law j h d s m ok).2⟩
def window (j : Fin 26) (d:Bool) := Shadow7.body j (program j d)
def unwind (j : Fin 26) (d:Bool) := Shadow7.unbody j (reverse j d)
theorem window_run (j : Fin 26) (h : 0≤j.val) (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (start0:Shadow7.onRails j 0 z s.basis)
    (legal:MeasuredCodec5.legalAt (history j) (run (Shadow7.routed j 0 1) m s).basis) :
    let out:=run (window j d) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unwind j d) n out=s := by
  apply Shadow7.body_run _ _ _ _ _ z odd start0
  exact admin j h d _ _ legal
end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace SkywalkRails Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
namespace NativeJ7
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-! The head of block `j`'s window (`2 ≤ j ≤ 19`): enter, the Shadow7.routed first tick, the pack, then the archive
of block `j-1` read from `j-1`'s records. The archive scratch must be clean after the pack (`scratch`); for
`j ≤ 13` this follows from the rails (`scratch_rails`), later blocks need D2's invariant. -/

theorem rawHead_mem (i : Fin 26) (k : Fin 157) (hk : k.val<23) : ArchiveJ7.rawPorts i k∈ArchiveJ7.rawHead i := by
  have e:ArchiveJ7.rawPorts i k=(ArchiveJ7.rawHead i).getD k 0:=by
    rw [ArchiveJ7.rawPorts,ArchiveJ7.raw_split,List.getD_append _ _ _ _ (by simp [ArchiveJ7.rawHead,Partial.cellsLoadP]; omega)]
  rw [e,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp [ArchiveJ7.rawHead,Partial.cellsLoadP]; omega),
    Option.getD_some]
  exact List.getElem_mem _

theorem forwardTargets : ∀ g∈EnterProof17.forward, CodecBitSliceVerify.target g≠4 ∧
    CodecBitSliceVerify.target g<EnterProof17.width := by decide +kernel
/-- The enter writes only its ports, never its gate wire `s+15` (a control). -/
theorem enterTargets (j : Fin 26) : ∀g∈Shadow7.enterP j,
    CodecBitSliceVerify.target g≠EnterJ7.gate j ∧ CodecBitSliceVerify.target g∈EnterJ7.ports j := by
  intro g hg
  rw [EnterJ7.emitted j,renameProgram,List.mem_map] at hg
  obtain ⟨g0,h0,rfl⟩:=hg
  have t:CodecBitSliceVerify.target (renameInstr (EnterJ7.map j) g0)=EnterJ7.map j (CodecBitSliceVerify.target g0):=by
    cases g0 <;> rfl
  obtain ⟨n8,lt⟩:=forwardTargets g0 h0
  rw [t]
  refine ⟨fun e=>n8 ?_,?_⟩
  · have same:=EnterJ7.inc j ⟨_,lt⟩ ⟨4,by decide⟩ (e.trans (rfl : EnterJ7.gate j=EnterJ7.map j 4))
    exact congrArg Fin.val same
  · rw [EnterJ7.map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [EnterJ7.ports_length]; exact lt),
      Option.getD_some]
    exact List.getElem_mem _
theorem enter_readonly (j : Fin 26) {q : Wire} (h : q∉EnterJ7.ports j ∨ q=EnterJ7.gate j) :
    ∀g∈Shadow7.enterP j,CodecBitSliceVerify.target g≠q := by
  intro g hg eq
  obtain ⟨ng,mp⟩:=enterTargets j g hg
  rcases h with h|h
  · exact h (eq ▸ mp)
  · exact ng (eq.trans h)

/-- Interval form of `Shadow7.firstUnchanged`: the window wire is the previous-tick wire or off tick 0's ports. -/
def FirstFree (j : Fin 26) (r : Wire) : Prop :=
  r=start j+15 ∨ ¬(r=start j+1044 ∨ (start j+16≤r ∧ r≤start j+Shadow7.sbP (start j)+34) ∨ (786≤r ∧ r≤Shadow7.sbP (start j)+803) ∨
    (1556≤r ∧ r≤Shadow7.sbP (start j)+1573))
instance (j : Fin 26) (r : Wire) : Decidable (FirstFree j r) := by unfold FirstFree; infer_instance
theorem firstFree (j : Fin 26) {q : Wire} (h : FirstFree j (windowNet j q)) : Shadow7.firstUnchanged j q := by
  unfold Shadow7.firstUnchanged
  by_cases hp:(windowNet j q:Nat)=start j+15
  · left
    rw [hp]
    show start j+15=start j+0+16-1
    omega
  · right
    intro mem
    rcases h with h|h
    · exact hp h
    · apply h
      simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
        SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at mem
      simp only [Shadow7.sbP,Wire] at *
      omega

theorem heads_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 →
    (∀r:Fin 5,history j ⟨2*r.val,by omega⟩=windowNet (prev j) (IntegerPacket.ports (Shadow7.shape (prev j)) r).a0 ∧
      history j ⟨2*r.val+1,by omega⟩=windowNet (prev j) (IntegerPacket.ports (Shadow7.shape (prev j)) r).history) ∧
    (∀i:Fin 10,FirstFree j (windowNet j (history j i)) ∧ history j i∉EnterJ7.ports j) ∧
    (∀q∈ArchiveJ7.rawHead (prev j),FirstFree j (windowNet j q) ∧ (q∉EnterJ7.ports j ∨ q=EnterJ7.gate j) ∧ q∉support j) := by
  decide +kernel

theorem legal_prefix (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (s t:State)
    (legal:StairArchiveRaw.legal (readCells (Shadow7.shape (prev j)) 0 15 (mappedBasis (prev j) s.basis)))
    (kept:∀i,t.basis (history j i)=s.basis (history j i)) : MeasuredCodec5.legalAt (history j) t.basis := by
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  intro i
  rw [kept,kept,((heads_all j (by omega) h19).1 i).1,((heads_all j (by omega) h19).1 i).2]
  have good:=legal _ (member_cell (Shadow7.shape (prev j)) 15 0 i (mappedBasis (prev j) s.basis) (by have h:=i.isLt;omega))
  apply not_both
  simpa only [Nat.zero_add,cell,mappedBasis] using good
theorem prefix_kept (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (s:State) (e t:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z (run (Shadow7.enterP j) e s).basis) :
    let now:=run (Shadow7.routed j 0 1) t (run (Shadow7.enterP j) e s)
    ∀i,now.basis (history j i)=s.basis (history j i) := by
  dsimp only
  intro i
  obtain ⟨f,no⟩:=(heads_all j (by omega) h19).2.1 i
  exact (Shadow7.first_preserves j _ odd _ t active _ (firstFree j f)).trans (run_preserves_outside _ _ _ _ (EnterJ7.notWire j no))
theorem bank_kept (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (s:State) (e t p:List Bool)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z (run (Shadow7.enterP j) e s).basis) :
    let now:=run (program j d) p (run (Shadow7.routed j 0 1) t (run (Shadow7.enterP j) e s))
    ∀i:Fin 23,now.basis (ArchiveJ7.rawPorts (prev j) ⟨i,by omega⟩)=s.basis (ArchiveJ7.rawPorts (prev j) ⟨i,by omega⟩) := by
  dsimp only
  intro i
  obtain ⟨f,no,sup⟩:=(heads_all j (by omega) h19).2.2 _ (rawHead_mem (prev j) ⟨i,by omega⟩ i.isLt)
  exact (run_preserves_outside _ _ _ _ (fun h=>sup (List.mem_toFinset.mp ((codes j (by omega) d).1 h)))).trans
    ((Shadow7.first_preserves j _ odd _ t active _ (firstFree j f)).trans (preserve_readonly _ _ (enter_readonly j no) s e))

theorem matching (j : Fin 26) (before:State) (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past g sign cross before) :
    let cells:=Shadow7.physicalCells (prev j) before
    let f:=decide (Shadow.far (Shadow7.sbP (start (prev j))) 15 past)
    let u:=f && afterFlags (decide (past.v<past.u)) (cells.take 5)
    ∃row<63145,∀q<23,(rawCol q).testBit row=rawBit (read (cells.drop 5)) f u (f && cross) q :=
  interrupted_row_shadow7 (Shadow7.sbP (start (prev j))) past small odd g sign cross _ (prior.records.trans (true_records_shadow7 _ _ small odd _ _).symm)

theorem frame_for (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (before out:State)
    (scratch:∀k:Fin 157,23≤k.val → out.basis (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past g sign cross before)
    (bk:∀i:Fin 23,out.basis (ArchiveJ7.rawPorts (prev j) ⟨i,by omega⟩)=before.basis (ArchiveJ7.rawPorts (prev j) ⟨i,by omega⟩)) :
    ∃row<63145,ArchivePortAction.Frame (ArchiveJ7.rawPorts (prev j)) raw row out := by
  have hp:(prev j).val≤23:=by simp only [prev]; omega
  let cells:=Shadow7.physicalCells (prev j) before
  let f:=decide (Shadow.far (Shadow7.sbP (start (prev j))) 15 past)
  let u:=f && afterFlags (decide (past.v<past.u)) (cells.take 5)
  let c:=f && cross
  let data:=rawBit (read (cells.drop 5)) f u c
  have tags:out.basis (ArchiveJ7.rawPorts (prev j) 20)=f ∧ out.basis (ArchiveJ7.rawPorts (prev j) 21)=u ∧
      out.basis (ArchiveJ7.rawPorts (prev j) 22)=c:=
    ⟨(bk 20).trans prior.far,(bk 21).trans prior.suffix,(bk 22).trans prior.crossed⟩
  have record:∀i:Fin 157,i.val<23 → out.basis (ArchiveJ7.rawPorts (prev j) i)=data i:=
    ArchiveJ7.observed (prev j) (by omega) before out (fun q=>bk ⟨q,Nat.lt_trans q.isLt (by decide : 20<23)⟩) f u c tags
  obtain ⟨row,lim,matchRow⟩:=matching j before past g sign cross odd small prior
  exact ⟨row,lim,starting_frame (ArchiveJ7.rawPorts (prev j)) out row data matchRow record scratch⟩

theorem completed_head (j : Fin 26) (h2 : 1≤j.val) (d:Bool) (src:State) (first pack:List Bool)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z src.basis) :
    Shadow7.onRails j 1 (SkywalkTrace.next z) (run (program j d) pack (run (Shadow7.routed j 0 1) first src)).basis :=
  Shadow7.ready_after_head j (program j d) src first pack z odd active (fun t=>retains j (by omega) d false t pack)

theorem head_legal (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (before:State) (et first:List Bool)
    (nowZ:SkywalkRails.State) (parity:(nowZ.a+nowZ.b)%2=1)
    (ready:Shadow7.onRails j 0 nowZ (run (Shadow7.enterP j) et before).basis)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past g sign cross before) :
    MeasuredCodec5.legalAt (history j) (run (Shadow7.routed j 0 1) first (run (Shadow7.enterP j) et before)).basis := by
  apply legal_prefix j (by omega) h19 before _ _ (prefix_kept j (by omega) h19 before et first nowZ parity ready)
  change StairArchiveRaw.legal (Shadow7.physicalCells (prev j) before)
  rw [Shadow7.physicalCells_eq, prior.records]
  exact legal_signed 15 past g sign (by omega) odd

theorem admits (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (before:State) (et first pack:List Bool)
    (nowZ:SkywalkRails.State) (parity:(nowZ.a+nowZ.b)%2=1)
    (ready:Shadow7.onRails j 0 nowZ (run (Shadow7.enterP j) et before).basis)
    (scratch:∀k:Fin 157,23≤k.val →
      (run (program j d) pack (run (Shadow7.routed j 0 1) first (run (Shadow7.enterP j) et before))).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past g sign cross before) :
    let src:=run (Shadow7.routed j 0 1) first (run (Shadow7.enterP j) et before)
    let out:=run (program j d) pack src
    MeasuredCodec5.legalAt (history j) src.basis ∧ ∃row<63145,ArchivePortAction.Frame (ArchiveJ7.rawPorts (prev j)) raw row out := by
  dsimp only
  refine ⟨head_legal j (by omega) h19 before et first nowZ parity ready past g sign cross odd prior,?_⟩
  exact frame_for j (by omega) h19 before _ scratch past g sign cross odd small prior (bank_kept j (by omega) h19 d before et first pack nowZ parity ready)
end NativeJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run Shadow7.onRails Shadow7.unrouted
namespace NativeJ7
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-- Block `j`'s window up to its leave: enter, then the window body with the pack and the archive. -/
def nextWindow (j : Fin 26) (d:Bool) := Shadow7.enterP j++window j d
def nextUnwind (j : Fin 26) (d:Bool) := unwind j d++Shadow7.enterInvP j

theorem backward_sub : wires EnterProof17.backward ⊆ Finset.range 13 := by decide +kernel
theorem enterInvCover (j : Fin 26) : wires (Shadow7.enterInvP j) ⊆ (EnterJ7.ports j).toFinset := by
  rw [EnterJ7.emittedInv j,renameProgram_support]
  intro q hq
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hq
  have lt:w<(EnterJ7.ports j).length:=Finset.mem_range.mp (backward_sub hw)
  rw [List.mem_toFinset,EnterJ7.map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem lt,Option.getD_some]
  exact List.getElem_mem lt

theorem next_window (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    let out:=run (nextWindow j d) m s
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] (encode G S T.u T.v)) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      ∀t,run (nextUnwind j d) t out=s := by
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m small cut input hist
  obtain ⟨legal,row,limit,frame⟩:=admits j (by omega) h19 d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity ready.2.1
    scratch past pg ps cross po pm prior
  have all:=window_run j (by omega) h19 d pre tape Z parity ready.2.1 legal row limit frame
    (fun k hk _=>scratch k hk)
  dsimp only [nextWindow,nextUnwind]
  simp only [run_append,run_take]
  refine ⟨all.1.trans ready.1,all.2.1,all.2.2.1.trans (true_records_shadow7 (Shadow7.sbP (start j)) z small odd G S),?_⟩
  intro n
  rw [all.2.2.2 n]
  have free:∀q∈EnterJ7.pending j,q∉wires (Shadow7.enterInvP j):=by
    intro q hq used
    have r:=EnterJ7.portsRegion j (List.mem_toFinset.mp (enterInvCover j used))
    have f:=EnterJ7.frame j
    simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false] at hq
    simp only [Wire] at *
    omega
  apply unmask (Shadow7.enterP j) (Shadow7.enterInvP j) (EnterJ7.pending j) (EnterJ7.avoid_enter j) free
  exact EnterProof17.return_packed (EnterJ7.layout j) (EnterJ7.map j) _ _ (EnterJ7.inc j) (fun _=>rfl) rfl (EnterJ7.emitted j)
    (EnterJ7.emittedInv j) raw _ z G S small cut input _ _
end NativeJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run Shadow7.onRails Shadow7.unrouted
namespace NativeFirstJ7
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-! First-form head (par-c2): the first block's five pre-window letters are legal from the stock stage, and its
window runs from the portal's cut (dadon's `NativePack225.original_legal/history_from_stock`). -/
theorem original_legal (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) (d:Bool) (seed p:Nat) (hp0:0<p) (odd:p%2=1)
    (raw:State) (stage:Rolling1588.Integer.Stage base d seed p (start j) raw.basis) :
    MeasuredCodec5.legalAt (History5.historyMap base (start j-5)) raw.basis := by
  have hj:=j.isLt
  obtain ⟨pre,original,packed⟩:=stage
  rw [packed]
  apply Rolling1588.Integer.prefix_next_legal base d base_pool_nodup (start j) (by simp only [start]; omega)
    (by simp only [History5.packDue,start,decide_eq_true_eq]; omega)
  exact W.stage_group_legal base base_pool_nodup seed p (start j) (start j-5) hp0 odd (by simp only [start]; omega)
    (by simp only [start]; omega) _ original
theorem headF_all : ∀ j : Fin 26, 0≤j.val → j.val≤24 → ∀i:Fin 10,
    NativeJ7.FirstFree j (windowNet j (history j i)) ∧ (history j i∉EnterJ7.ports j ∨ history j i=EnterJ7.gate j) ∧
    history j i≠EnterJ7.flagN j ∧ history j i≠EnterJ7.flagF j ∧ history j i≠EnterJ7.flagU j ∧
    history j i∉RailPair.sites (EnterJ7.upperPairs j) ∧ EnterJ7.pull j (history j i)=History5.historyMap base (start j-5) i := by
  decide +kernel
theorem history_from_stock (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) (raw cut t:State) {neg far long:Bool}
    (frame:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) cut)
    (m n:List Bool) (head:t=run (Shadow7.enterP j) m cut)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (ready:Shadow7.onRails j 0 z t.basis) :
    ∀i,(run (Shadow7.routed j 0 1) n t).basis (history j i)=raw.basis (History5.historyMap base (start j-5) i) := by
  intro i
  obtain ⟨f,no,hn,hf,hu,hh,coord⟩:=headF_all j h1 (by omega) i
  rw [Shadow7.first_preserves j z odd _ _ ready _ (NativeJ7.firstFree j f),head,preserve_readonly _ _ (NativeJ7.enter_readonly j no)]
  exact (frame.unchanged _ hn hf hu hh).trans (congrArg raw.basis coord)

/-- The first block's enter and window (dadon's `NativePack225.firstWindow` without the portal). -/
def enteredWindow (j : Fin 26) (d:Bool) := Shadow7.enterP j++window j d
def enteredUnwind (j : Fin 26) (d:Bool) := unwind j d++Shadow7.enterInvP j
theorem entered_window (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) (d:Bool) (raw v:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) v)
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (legal0:MeasuredCodec5.legalAt (History5.historyMap base (start j-5)) raw.basis) :
    let out:=run (enteredWindow j d) m v
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    out.phase=v.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] (encode G S T.u T.v)) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      ∀t,run (enteredUnwind j d) t out=v := by
  let pre:=run (Shadow7.enterP j) m v
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_from_cut_at j raw v z G S m small cut input hist
  have legal:=legal_congr (history_from_stock j h1 (by omega) raw v pre cut m tape rfl _ parity ready.2) legal0
  have all:=window_run j h1 d pre tape Z parity ready.2 legal
  dsimp only [enteredWindow,enteredUnwind]
  simp only [run_append,run_take]
  refine ⟨all.1.trans ready.1,all.2.1,all.2.2.1.trans (true_records_shadow7 (Shadow7.sbP (start j)) z small odd G S),?_⟩
  intro n
  rw [all.2.2.2 n]
  exact EnterProof17.return_packed (EnterJ7.layout j) (EnterJ7.map j) _ _ (EnterJ7.inc j) (fun _=>rfl) rfl (EnterJ7.emitted j)
    (EnterJ7.emittedInv j) raw _ z G S small cut input _ _
end NativeFirstJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic ArchivePortAction StairArchiveIntegerHook
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
namespace ArchiveJ7
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-- The wires of a swap list are its pairs' ends. -/
theorem moves_wires (ps : List (Wire×Wire)) : ∀q∈wires (moves ps), ∃p∈ps, q=p.1 ∨ q=p.2 := by
  induction ps with
  | nil => intro q h; simp [moves,wires] at h
  | cons p ps ih =>
    intro q h
    obtain ⟨a,b⟩:=p
    simp only [moves,List.flatMap_cons,wires_append,Finset.mem_union] at h
    rcases h with h|h
    · refine ⟨(a,b),List.mem_cons_self,?_⟩
      simp [swapBits,wires,Instr.wires] at h ⊢
      tauto
    · obtain ⟨p',hp',e⟩:=ih q (by simpa [moves] using h)
      exact ⟨p',List.mem_cons_of_mem _ hp',e⟩
theorem load_cover (i : Fin 26) (hi : i.val≤24) (d:Bool) : wires (Shadow7.archiveLoadP i d) ⊆ (rawPortsList i).toFinset := by
  rw [load_program,wires_append,Finset.union_subset_iff]
  constructor
  · rw [placed,renameProgram_support]
    intro q member
    obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp member
    have bound:=Finset.mem_range.mp (sub (op true d) used)
    have small:w<155:=by cases d <;> exact bound
    rw [load_map i ⟨w,small⟩,List.mem_toFinset,rawPorts,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [rawLength]; omega),Option.getD_some]
    exact List.getElem_mem _
  · intro q hq
    obtain ⟨p,hp,e⟩:=moves_wires _ q hq
    obtain ⟨h1,h2,-⟩:=(heads_all i hi).2.2.2.2.2.1 p hp
    rw [List.mem_toFinset,raw_split]
    rcases e with rfl|rfl
    · exact List.mem_append_left _ h1
    · exact List.mem_append_left _ h2
end ArchiveJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction CodecBitSliceVerify EnterProof PortalValues SkywalkRails Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! NativeJ, part 3 (Tail10d9): what block `j`'s window keeps (`2 ≤ j ≤ 19`). -/

theorem codesOld_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 →
    (∀i:Fin 16,oldRange (start j+1) (windowNet j (ArchiveJ7.codePorts (prev j) ⟨i.val,by omega⟩))) ∧
    (∀k:Fin 3,ArchiveJ7.codePorts (prev j) ⟨154+k.val,by omega⟩=Shadow7.sbP (start j)+1580+k.val ∧
      ¬Shadow7.MayTouch j (windowNet j (Shadow7.sbP (start j)+1580+k.val))) := by
  decide +kernel
theorem encoded_outside (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) :
    ∀i:Fin 16,ArchiveJ7.codePorts (prev j) ⟨i.val,by omega⟩∉Shadow7.spanSites j 1 14 :=
  fun i=>Shadow7.old_clear (by decide) ((codesOld_all j (by omega) h19).1 i)
/-- The enter flags and the saved high word, kept through the window. -/
def protectedSites (j : Fin 26) : List Wire := [EnterJ7.flagN j,EnterJ7.flagF j,EnterJ7.flagU j]++EnterJ7.saved j
theorem admin_cover (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) :
    wires (withArchive j d)⊆(support j++ArchiveJ7.rawPortsList (prev j)).toFinset := by
  rw [withArchive,wires_append,List.toFinset_append]
  exact Finset.union_subset_union (codes j (by omega) d).1 (ArchiveJ7.load_cover (prev j) (by simp only [prev]; omega) d)
/-- The protected sites are the flag block `e0..e0+5` and the parked B-side word. -/
theorem protected_band (j : Fin 26) : ∀q∈protectedSites j,
    (Shadow7.sbP (start j)+1574≤q ∧ q≤Shadow7.sbP (start j)+1579) ∨ (Shadow7.sbP (start j)+804≤q ∧ q+3<Shadow7.sbP (start j)+804+Shadow7.wpP (start j)) := by
  intro q hq
  rw [protectedSites,List.mem_append] at hq
  rcases hq with hq|hq
  · simp only [EnterJ7.flagN,EnterJ7.flagF,EnterJ7.flagU,List.mem_cons,List.not_mem_nil,or_false] at hq
    simp only [Wire] at *; omega
  · rw [EnterJ7.saved,List.mem_append] at hq
    rcases hq with hq|hq
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      simp only [Wire] at *; omega
    · simp only [EnterJ7.upperTail,List.map_map,List.mem_map,List.mem_range,Function.comp] at hq
      obtain ⟨i,hi,rfl⟩:=hq
      simp only [Wire] at *; omega
theorem free_native (j : Fin 26) : ∀q∈protectedSites j,¬Shadow7.MayTouch j (windowNet j q) := by
  intro q hq
  have b:=protected_band j q hq
  have f:=EnterJ7.frame j
  have fix:windowNet j q=q:=by
    simp only [windowNet,net,OB5.sig]
    split <;> simp only [Wire] at * <;> omega
  rw [fix]
  unfold Shadow7.MayTouch
  simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *
  simp only [Wire] at *
  omega
theorem adminBand_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 → ∀q∈ArchiveJ7.rawHead (prev j)++support j,
    q<Shadow7.sbP (start j)+804 ∨ (Shadow7.sbP (start j)+801+Shadow7.wpP (start j)≤q ∧ q<Shadow7.sbP (start j)+1574) ∨ Shadow7.sbP (start j)+1579<q := by
  decide +kernel
theorem free_admin (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) :
    ∀q∈protectedSites j,q∉(support j++ArchiveJ7.rawPortsList (prev j)) := by
  intro q hq hm
  have b:=protected_band j q hq
  have f:=EnterJ7.frame j
  have tick:start (prev j)+15=start j:=by simp only [prev,start]; omega
  rw [ArchiveJ7.raw_split,List.mem_append,List.mem_append] at hm
  rcases hm with hm|hm|hm
  · have:=adminBand_all j (by omega) h19 q (List.mem_append_right _ hm); simp only [Wire] at *; omega
  · have:=adminBand_all j (by omega) h19 q (List.mem_append_left _ hm); simp only [Wire] at *; omega
  · obtain ⟨k,hk,eq⟩:=List.mem_map.mp hm
    apply ArchiveJ7.band_off (start (prev j)+15) (ArchiveJ.tick_lt (prev j)) (List.mem_range.mp hk) _ eq
    rw [tick]
    unfold ArchiveJ7.Band
    rcases b with b|b
    · right; right; right; right; refine ⟨q-(Shadow7.sbP (start j)+1574),?_,?_⟩ <;> simp only [Shadow7.e0P,Wire] at * <;> omega
    · left
      have top : start j<369 ∨ Shadow7.wpP (start j)+Shadow7.sbP (start j)+start j≤498 := by
        by_cases h : start j<369
        · exact Or.inl h
        · right
          have r : railP (start j)=513-start j := by unfold railP; rw [if_neg (by omega),if_neg (by omega)]
          have wdef : Shadow7.wpP (start j)=railP (start j)-Shadow7.sbP (start j)-15 := rfl
          omega
      simp only [Wire] at *; omega
theorem keeps_stored (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (s:State) (m:List Bool) (q:Wire)
    (hq:q∈protectedSites j) : (run (Shadow7.body j (withArchive j d)) m s).basis q=s.basis q :=
  Shadow7.body_cover j (withArchive j d) (protectedSites j) (support j++ArchiveJ7.rawPortsList (prev j))
    (free_native j) (free_admin j (by omega) h19) (admin_cover j (by omega) h19 d) s m q hq
theorem source_tags (j : Fin 26) (s:BasisState) (z:SkywalkNat.State) (G S:Bool)
    (hit:∀q∈wires EnterProof17.forward,s (EnterJ7.map j q)=(EnterProof17.shadowRow (Shadow7.sbP (start j)) 15 z G S).testBit q) :
    s (EnterJ7.flagN j)=false ∧ s (EnterJ7.flagF j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      s (EnterJ7.flagU j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u) :=
  (EnterProof17.actual_tags (EnterJ7.ports j) s (Shadow7.sbP (start j)) 15 z G S hit).2
theorem relay (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (s:State) (m:List Bool) (h:Nat) (x y:Bool)
    (high:regValue (EnterJ7.saved j) s.basis=h) (hn:s.basis (EnterJ7.flagN j)=false) (hf:s.basis (EnterJ7.flagF j)=x)
    (hu:s.basis (EnterJ7.flagU j)=y) :
    let out:=run (Shadow7.body j (withArchive j d)) m s
    regValue (EnterJ7.saved j) out.basis=h ∧ out.basis (EnterJ7.flagN j)=false ∧ out.basis (EnterJ7.flagF j)=x ∧
      out.basis (EnterJ7.flagU j)=y :=
  keep_values (EnterJ7.flagN j) (EnterJ7.flagF j) (EnterJ7.flagU j) (EnterJ7.saved j) s (run (Shadow7.body j (withArchive j d)) m s)
    h x y (keeps_stored j (by omega) h19 d s m) high hn hf hu
theorem saved_at_leave (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (raw cut:State) (z:SkywalkNat.State)
    (G S:Bool) (head ticks:List Bool) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (packed:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (negative S z.u) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u)) (pullState (EnterJ7.pull j) raw) cut)
    (input:SkywalkIntegerInput (EnterJ7.lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let out:=run (Shadow7.body j (withArchive j d)) ticks (run (Shadow7.enterP j) head cut)
    regValue (EnterJ7.saved j) out.basis=(if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) ∧
      out.basis (EnterJ7.flagN j)=false ∧ out.basis (EnterJ7.flagF j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      out.basis (EnterJ7.flagU j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u) := by
  let pre:=run (Shadow7.enterP j) head cut
  have high:=EnterJ7.high_from_cut j raw cut z G S head small packed input
  have body0:=EnterJ7.from_full j raw cut z G S head small packed input
  have tags:=source_tags j pre.basis z G S body0.2.1
  exact relay j (by omega) h19 d pre ticks (if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) _ _
    high tags.1 tags.2.1 tags.2.2
theorem protected_bound (j : Fin 26) : ∀q∈protectedSites j,q<Shadow7.sbP (start j)+1580 := by
  have f:=EnterJ7.frame j
  intro q hq
  have:=protected_band j q hq
  simp only [Wire] at *; omega
theorem protected_pending (j : Fin 26) : ∀q∈protectedSites j,q∉EnterJ7.pending j := by
  intro q hq hp
  have b:=protected_bound j q hq
  simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false] at hp
  simp only [Wire] at *
  omega
theorem saved_with_pending (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (raw cut:State)
    (z:SkywalkNat.State) (G S:Bool) (head ticks:List Bool) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (packed:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (negative S z.u) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u)) (pullState (EnterJ7.pull j) raw)
      (eraseSites (EnterJ7.pending j) cut))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let out:=run (Shadow7.body j (withArchive j d)) ticks (run (Shadow7.enterP j) head cut)
    regValue (EnterJ7.saved j) out.basis=(if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) ∧
      out.basis (EnterJ7.flagN j)=false ∧ out.basis (EnterJ7.flagF j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      out.basis (EnterJ7.flagU j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u) := by
  have observed:=saved_at_leave j (by omega) h19 d raw (eraseSites (EnterJ7.pending j) cut) z G S head ticks small packed input
  have eq:=masked_body (Shadow7.enterP j) (Shadow7.body j (withArchive j d)) (protectedSites j) (EnterJ7.pending j) cut head ticks
    (EnterJ7.avoid_enter j) (protected_pending j) (fun s=>keeps_stored j (by omega) h19 d s ticks)
  exact keep_values (EnterJ7.flagN j) (EnterJ7.flagF j) (EnterJ7.flagU j) (EnterJ7.saved j) _ _ _ _ _ eq
    observed.1 observed.2.1 observed.2.2.1 observed.2.2.2

theorem popped (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (src:State) (m:List Bool) (row:Nat)
    (frame:Frame (ArchiveJ7.codePorts (prev j)) (code d) row
      (run (withArchive j d) (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m src))) :
    ∀k:Fin 3,(run (Shadow7.body j (withArchive j d)) m src).basis (Shadow7.sbP (start j)+1580+k.val)=false := by
  intro k
  have phys:=(codesOld_all j (by omega) h19).2 k
  exact Shadow7.after_encoded j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row src m frame ⟨154+k.val,by omega⟩
    (by dsimp;omega) _ phys.1 phys.2
theorem archive_result (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (row:Nat) (lim:row<63145) (s:State)
    (m:List Bool) (raw0:Frame (ArchiveJ7.rawPorts (prev j)) ArchivePortAction.raw row (run (program j d) m s)) :
    Frame (ArchiveJ7.codePorts (prev j)) (code d) row (run (withArchive j d) m s) :=
  from_append (prop:=Frame (ArchiveJ7.codePorts (prev j)) (code d) row)
    (ArchiveJ7.load_run (prev j) (by simp only [prev]; omega) d row lim _ (m.drop (measurementCount (program j d))) raw0).2.1
theorem receipt (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (s:State) (m:List Bool) (row:Nat)
    (lim:row<63145)
    (raw0:Frame (ArchiveJ7.rawPorts (prev j)) ArchivePortAction.raw row
      (run (program j d) (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m s))) :
    Kept (ArchiveJ7.codePorts (prev j)) d row (run (Shadow7.body j (withArchive j d)) m s) ∧
      ∀k:Fin 3,(run (Shadow7.body j (withArchive j d)) m s).basis (Shadow7.sbP (start j)+1580+k.val)=false := by
  have frame:=archive_result j (by omega) h19 d row lim _ _ raw0
  exact ⟨Shadow7.body_keeps j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row s m (encoded_outside j (by omega) h19) frame,
    popped j (by omega) h19 d s m row frame⟩

/-- Hypotheses of block `j`'s window head, as `next_window` takes them. -/
theorem real_receipt (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    let out:=run (nextWindow j d) m s
    ∃row<63145, RowTruth past pg ps row ∧ Kept (ArchiveJ7.codePorts (prev j)) d row out ∧
      ∀k:Fin 3,out.basis (Shadow7.sbP (start j)+1580+k.val)=false := by
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m small cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j (by omega) h19 d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity ready.2.1
    scratch past pg ps cross po pm prior
  have matchRow:=row_truth (prev j) (ArchiveJ7.rawPorts (prev j)) (ArchiveJ7.chronological_all (prev j) (by simp only [prev]; omega))
    row past pg ps s _ prior.records
    (bank_kept j (by omega) h19 d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity ready.2.1) frame
  have final:=receipt j (by omega) h19 d pre tape row limit frame
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨row,limit,matchRow,final⟩

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run measurementCount Shadow7.onRails

/-- dadon's `NativePack{s}.fourHoles`: the four B-side history cells the archive of block `prev j` (at tick
`start j`) frees, i.e. the first four wires of `ArchiveJ7.codeTail (prev j)`. -/
def fourHoles (j : Fin 26) : List Wire := ((ArchiveJ7.codeTail (prev j)).take 4)

theorem fourHoles_eq (j : Fin 26) (h1 : 1 ≤ j.val) : fourHoles j =
    [OB5.sig (start j) (start j+1036), OB5.sig (start j) (start j+1038), OB5.sig (start j) (start j+1041),
      OB5.sig (start j) (start j+1043)] := by
  have e : start (prev j) + 15 = start j := by simp only [prev, start]; omega
  simp only [fourHoles, ArchiveJ7.codeTail, e, List.take_succ_cons, List.take_zero]

/-- dadon's `blank_slots`: every hole is a code port at index ≥ 16 (where the archive code is blank). -/
theorem blank_slots (j : Fin 26) : ∀ q ∈ fourHoles j, ∃ i : Fin 157, 16 ≤ i.val ∧ ArchiveJ7.codePorts (prev j) i = q := by
  have hl : (cellsRestoreP (start (prev j)+15) ++ ArchiveJ7.scratch (prev j)).length = 150 := by
    simp [cellsRestoreP, ArchiveJ7.scratch]
  have key : ∀ c, (hc : c < 4) → ArchiveJ7.codePorts (prev j) ⟨150+c, by omega⟩ = (ArchiveJ7.codeTail (prev j)).getD c 0 := by
    intro c hc
    show (ArchiveJ7.codePortsList (prev j)).getD (150+c) 0 = _
    rw [ArchiveJ7.code_split, List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, show 150+c-150 = c by omega]
  intro q hq
  simp only [fourHoles, ArchiveJ7.codeTail, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl
  · exact ⟨⟨150, by omega⟩, Nat.le_of_lt_succ (by show 16 < 150+1; omega), (key 0 (by omega)).trans rfl⟩
  · exact ⟨⟨151, by omega⟩, Nat.le_of_lt_succ (by show 16 < 151+1; omega), (key 1 (by omega)).trans rfl⟩
  · exact ⟨⟨152, by omega⟩, Nat.le_of_lt_succ (by show 16 < 152+1; omega), (key 2 (by omega)).trans rfl⟩
  · exact ⟨⟨153, by omega⟩, Nat.le_of_lt_succ (by show 16 < 153+1; omega), (key 3 (by omega)).trans rfl⟩

/-- The holes are outside every wire the Shadow7.routed ticks of block `j` may touch. -/
theorem holes_free (j : Fin 26) (h1 : 1 ≤ j.val) (h19 : j.val ≤ 24) : ∀ q ∈ fourHoles j, ¬Shadow7.MayTouch j (windowNet j q) := by
  intro q hq
  have closed : ∀ i : Fin 26, 1 ≤ i.val → i.val ≤ 24 →
      (fourHoles i).all (fun w => decide (¬Shadow7.MayTouch i (windowNet i w))) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (closed j (by omega) h19) q hq)

/-- dadon's `NativePack{s}.cleared_holes`, generic: after block `j`'s window head, the four freed history cells of the
previous block's archive are zero. -/
theorem cleared_holes (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    ∀q∈fourHoles j,(run (nextWindow j d) m s).basis q=false := by
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m small cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j (by omega) (by omega) d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity
    ready.2.1 scratch past pg ps cross po pm prior
  have final:=archive_result j (by omega) (by omega) d row limit _ _ frame
  intro q hq
  obtain ⟨i,hi,slot⟩:=blank_slots j q hq
  rw [nextWindow,run_append,run_take]
  exact Shadow7.after_encoded j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row pre tape final i hi q slot
    (holes_free j (by omega) h19 q hq)

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! The leave of block `j` writes only inside par-c1's box (dadon's `NativePack{s}.writes/exterior`, which
decided 37 leave parts per block); generic from `Shadow7.leaveOps_box`. -/
end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! `NativePack{s}.tailTemps/tail_clean`, generic: after the window head, the wires above the anchored block
(`e0+9 ..`) are clean. From `s ≥ 270` the wires `2055-s..1812` hold the block's own history cells (windowNet
mirror), so the tail stops below them (dadon's 255: `1712..1799`). Late blocks' archive scratch reaches into the
tail; those wires are clean as unused code ports (`Shadow7.after_encoded`). -/
def tailTemps (j : Fin 26) : List Wire :=
  List.range' (Shadow7.e0P (start j)+9) (min 1813 (2055-start j)-(Shadow7.e0P (start j)+9))
theorem tail_mem (j : Fin 26) {q : Wire} (h : q∈tailTemps j) :
    Shadow7.e0P (start j)+9≤q ∧ q≤1812 ∧ q+start j≤2054 := by
  simp only [tailTemps,List.mem_range'_1] at h; simp only [Wire] at *; omega
theorem tail_geometry (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24) {q : Wire} (hq : q∈tailTemps j) :
    windowNet j q=q ∧ EnterJ7.pull j q=q ∧ ¬Shadow7.MayTouch j q ∧ q∉EnterJ7.ports j ∧ q∉EnterJ7.pending j ∧
    q≠EnterJ7.flagN j ∧ q≠EnterJ7.flagF j ∧ q≠EnterJ7.flagU j ∧ q∉RailPair.sites (EnterJ7.upperPairs j) := by
  have t:=tail_mem j hq
  have f:=EnterJ7.frame j
  simp only [Shadow7.e0P] at t
  refine ⟨?_,?_,?_,fun m=>?_,fun m=>?_,?_,?_,?_,fun m=>?_⟩
  · rw [windowNet,net]
    exact Shadow7.sig_tail j h21 q (by have:=t.1; simp only [Shadow7.e0P,Wire] at *; omega) t.2.2 (start j+14) (le_refl _)
  · rw [EnterJ7.pull]
    exact Shadow7.sig_tail j h21 q (by have:=t.1; simp only [Shadow7.e0P,Wire] at *; omega) t.2.2 (start j-1)
      (by have:=EnterJ7.frame j; simp only [Wire] at *; omega)
  · unfold Shadow7.MayTouch; simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *; simp only [Wire] at *; omega
  · have:=EnterJ7.portsRegion j m; simp only [Wire] at *; omega
  · simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false] at m; simp only [Wire] at *; omega
  · simp only [EnterJ7.flagN,Wire]; omega
  · simp only [EnterJ7.flagF,Wire]; omega
  · simp only [EnterJ7.flagU,Wire]; omega
  · have:=EnterJ7.upperSites j m; simp only [Wire] at *; omega
theorem tailHead_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 → ∀q∈ArchiveJ7.rawHead (prev j)++support j,
    q<Shadow7.sbP (start j)+1583 ∨ 2055≤q+start j := by
  decide +kernel
theorem tail_clean (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24) (d:Bool) (x p:Nat) (raw s:State)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (row:Nat) (frame:Frame (ArchiveJ7.codePorts (prev j)) (code d) row
      (run (withArchive j d) (b.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) b (run (Shadow7.enterP j) a s)))) :
    ∀q∈tailTemps j,(run (Shadow7.body j (withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false := by
  intro q hq
  obtain ⟨wn,same,touch,port,pend,hn,hf,hu,hi⟩:=tail_geometry j (by omega) h21 hq
  have t:=tail_mem j hq
  by_cases sc:q∈ArchiveJ7.scratch (prev j)
  · obtain ⟨k,hk,eq⟩:=List.mem_map.mp sc
    have hk':=List.mem_range.mp hk
    have code0:ArchiveJ7.codePorts (prev j) ⟨16+k,by omega⟩=q:=(ArchiveJ7.code_scratch (prev j) hk').trans eq
    exact Shadow7.after_encoded j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row (run (Shadow7.enterP j) a s) b frame
      ⟨16+k,by omega⟩ (by dsimp only; omega) q code0 (by rw [wn]; exact touch)
  · have notAdmin:q∉support j++ArchiveJ7.rawPortsList (prev j):=by
      rw [ArchiveJ7.raw_split,List.mem_append,List.mem_append]
      rintro (h|h|h)
      · have:=tailHead_all j (by omega) h21 q (List.mem_append_right _ h); simp only [Shadow7.e0P,Wire] at *; omega
      · have:=tailHead_all j (by omega) h21 q (List.mem_append_left _ h); simp only [Shadow7.e0P,Wire] at *; omega
      · exact sc h
    have stay:=Shadow7.ext_head (Shadow7.enterP j) j (withArchive j d) (support j++ArchiveJ7.rawPortsList (prev j)) s a b q
      (by rw [wn]; exact touch) (EnterJ7.notWire j port) notAdmin (admin_cover j (by omega) h21 d)
    have read:=cut.unchanged q hn hf hu hi
    have canon:s.basis q=raw.basis q:=by simpa only [pullState,same,eraseSites,if_neg pend] using read
    have zero:raw.basis q=false:=WideReference.domain_carry (by simp only [start]; omega) domain q
      (by simp only [Shadow7.e0P,Wire] at *; omega) t.2.1
    exact stay.trans (canon.trans zero)

/-! Margin 17 (pieces/A): two wires the margin-18 register covered are free now and reach the leave clean:
`e0-1` (the carry row `sb+17`: the leave pool, the archive scratch and the raw sites run through it) and the enter's
parked B wire `sb+804 = b0+17` (a relocation source). -/
theorem topHead_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 → ∀q∈ArchiveJ7.rawHead (prev j)++support j,
    q≠Shadow7.sbP (start j)+1573 ∧ q≠Shadow7.sbP (start j)+803 := by
  decide +kernel
/-- margin 16: the archive head and support also avoid the second spare carry wire `e0P-2`. -/
theorem topHead2_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 → ∀q∈ArchiveJ7.rawHead (prev j)++support j,
    q≠Shadow7.sbP (start j)+1572 := by
  decide +kernel
theorem top_geometry (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) {q : Wire} (hq : (q:Nat)+2=Shadow7.e0P (start j) ∨ (q:Nat)+1=Shadow7.e0P (start j)) :
    windowNet j q=q ∧ EnterJ7.pull j q=q ∧ ¬Shadow7.MayTouch j q ∧ q∉EnterJ7.ports j ∧ q∉EnterJ7.pending j ∧
    q≠EnterJ7.flagN j ∧ q≠EnterJ7.flagF j ∧ q≠EnterJ7.flagU j ∧ q∉RailPair.sites (EnterJ7.upperPairs j) := by
  have f:=EnterJ7.frame j
  have hj:=j.isLt
  simp only [Shadow7.e0P] at hq
  refine ⟨?_,?_,?_,fun m=>?_,fun m=>?_,?_,?_,?_,fun m=>?_⟩
  · show @Eq Nat (OB5.sigNat (start j+14) q) q
    simp only [OB5.sigNat]
    split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | rfl | (simp only [Wire] at *; omega)
  · show @Eq Nat (OB5.sigNat (start j-1) q) q
    simp only [OB5.sigNat]
    split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | rfl | (simp only [Wire] at *; omega)
  · unfold Shadow7.MayTouch; simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *; simp only [Wire] at *; omega
  · have:=EnterJ7.portsRegion j m; simp only [Wire] at *; omega
  · simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false] at m; simp only [Wire] at *; omega
  · simp only [EnterJ7.flagN]; simp only [Wire] at *; omega
  · simp only [EnterJ7.flagF]; simp only [Wire] at *; omega
  · simp only [EnterJ7.flagU]; simp only [Wire] at *; omega
  · have:=EnterJ7.upperSites j m; simp only [Wire] at *; omega
theorem top_first (j : Fin 26) (h21 : j.val≤24) {w : Nat} (lo : w+2=Shadow7.e0P (start j) ∨ w+1=Shadow7.e0P (start j)) :
    Shadow7.firstUnchanged j w := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo
  have key:OB5.sigNat (start j+14) w=w := by
    unfold OB5.sigNat
    simp only [start]
    split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | rfl | omega
  unfold Shadow7.firstUnchanged
  dsimp only
  right
  show OB5.sigNat (start j+14) w∉(IntegerPacket.ports (Shadow7.shape j) 0).wires
  rw [key]
  intro mem
  simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at mem
  omega
theorem top_clean (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24) (d:Bool) (x p:Nat) (raw s:State)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (row:Nat) (frame:Frame (ArchiveJ7.codePorts (prev j)) (code d) row
      (run (withArchive j d) (b.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) b (run (Shadow7.enterP j) a s)))) :
    ∀q:Wire,((q:Nat)+2=Shadow7.e0P (start j) ∨ (q:Nat)+1=Shadow7.e0P (start j)) →
      (run (Shadow7.body j (withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false := by
  intro q hq
  obtain ⟨wn,same,touch,port,pend,hn,hf,hu,hi⟩:=top_geometry j (by omega) h21 hq
  by_cases sc:q∈ArchiveJ7.scratch (prev j)
  · obtain ⟨k,hk,eq⟩:=List.mem_map.mp sc
    have hk':=List.mem_range.mp hk
    have code0:ArchiveJ7.codePorts (prev j) ⟨16+k,by omega⟩=q:=(ArchiveJ7.code_scratch (prev j) hk').trans eq
    exact Shadow7.after_encoded j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row (run (Shadow7.enterP j) a s) b frame
      ⟨16+k,by omega⟩ (by dsimp only; omega) q code0 (by rw [wn]; exact touch)
  · have notAdmin:q∉support j++ArchiveJ7.rawPortsList (prev j):=by
      rw [ArchiveJ7.raw_split,List.mem_append,List.mem_append]
      rintro (h|h|h)
      · have:=(topHead_all j (by omega) h21 q (List.mem_append_right _ h)).1; have:=topHead2_all j (by omega) h21 q (List.mem_append_right _ h)
        simp only [Shadow7.e0P,Wire] at *; omega
      · have:=(topHead_all j (by omega) h21 q (List.mem_append_left _ h)).1; have:=topHead2_all j (by omega) h21 q (List.mem_append_left _ h)
        simp only [Shadow7.e0P,Wire] at *; omega
      · exact sc h
    have stay:=Shadow7.ext_head (Shadow7.enterP j) j (withArchive j d) (support j++ArchiveJ7.rawPortsList (prev j)) s a b q
      (by rw [wn]; exact touch) (EnterJ7.notWire j port) notAdmin (admin_cover j (by omega) h21 d)
    have read:=cut.unchanged q hn hf hu hi
    have canon:s.basis q=raw.basis q:=by simpa only [pullState,same,eraseSites,if_neg pend] using read
    have f:=EnterJ7.frame j
    have zero:raw.basis q=false:=WideReference.domain_carry (by simp only [start]; omega) domain q
      (by simp only [Shadow7.e0P,Wire] at *; omega) (by simp only [Shadow7.e0P,Wire] at *; omega)
    exact stay.trans (canon.trans zero)
theorem parked_free (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) :
    (∀q∈[EnterJ7.parked j],¬Shadow7.MayTouch j (windowNet j q)) ∧
    (∀q∈[EnterJ7.parked j],q∉(support j++ArchiveJ7.rawPortsList (prev j))) ∧ (∀q∈[EnterJ7.parked j],q∉EnterJ7.pending j) := by
  have f:=EnterJ7.frame j
  refine ⟨?_,?_,?_⟩
  · intro q hq
    have b:(q:Nat)=Shadow7.sbP (start j)+803:=by simpa only [EnterJ7.parked,List.mem_singleton] using hq
    have fix:windowNet j q=q:=by
      simp only [windowNet,net,OB5.sig]
      split <;> simp only [Wire] at * <;> omega
    rw [fix]
    unfold Shadow7.MayTouch
    simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *
    simp only [Wire] at *
    omega
  · intro q hq hm
    have b:(q:Nat)=Shadow7.sbP (start j)+803:=by simpa only [EnterJ7.parked,List.mem_singleton] using hq
    have tick:start (prev j)+15=start j:=by simp only [prev,start]; omega
    rw [ArchiveJ7.raw_split,List.mem_append,List.mem_append] at hm
    rcases hm with hm|hm|hm
    · exact (topHead_all j (by omega) h19 q (List.mem_append_right _ hm)).2 b
    · exact (topHead_all j (by omega) h19 q (List.mem_append_left _ hm)).2 b
    · obtain ⟨k,hk,eq⟩:=List.mem_map.mp hm
      apply ArchiveJ7.band_off (start (prev j)+15) (ArchiveJ.tick_lt (prev j)) (List.mem_range.mp hk) _ eq
      rw [tick]
      unfold ArchiveJ7.Band
      left
      refine ⟨?_,Or.inl ?_⟩ <;> (simp only [Wire] at *; omega)
  · intro q hq hp
    have b:(q:Nat)=Shadow7.sbP (start j)+803:=by simpa only [EnterJ7.parked,List.mem_singleton] using hq
    simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false] at hp
    simp only [Wire] at *
    omega
theorem parked_clean (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (raw cut:State)
    (z:SkywalkNat.State) (G S:Bool) (head ticks:List Bool) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (packed:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u)) (pullState (EnterJ7.pull j) raw)
      (eraseSites (EnterJ7.pending j) cut))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    (run (Shadow7.body j (withArchive j d)) ticks (run (Shadow7.enterP j) head cut)).basis (EnterJ7.parked j)=false := by
  obtain ⟨native,admin,pend⟩:=parked_free j (by omega) h19
  have keep (s:State) : ∀q∈[EnterJ7.parked j],(run (Shadow7.body j (withArchive j d)) ticks s).basis q=s.basis q :=
    fun q hq => Shadow7.body_cover j (withArchive j d) [EnterJ7.parked j] (support j++ArchiveJ7.rawPortsList (prev j))
      native admin (admin_cover j (by omega) h19 d) s ticks q hq
  have eq:=masked_body (Shadow7.enterP j) (Shadow7.body j (withArchive j d)) [EnterJ7.parked j] (EnterJ7.pending j) cut head ticks
    (EnterJ7.avoid_enter j) pend keep (EnterJ7.parked j) (List.mem_singleton.mpr rfl)
  rw [eq, keep _ (EnterJ7.parked j) (List.mem_singleton.mpr rfl)]
  have body0:=EnterJ7.from_full j raw (eraseSites (EnterJ7.pending j) cut) z G S head small packed input
  exact EnterProof17.actual_parked (EnterJ7.ports j) _ (Shadow7.sbP (start j)) 15 z G S body0.2.1

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! `NativePack{s}.upperA/upper_clear`, generic: the A rail above the block's own ticks (`s+h+48 .. top`,
`top = min (s+30+R(s+14)) 529`, par-a's exact span top) is clean after the window head: the parked bank's A side is zeroed by the cut, the
wires above the bank (`s+R+16 ..`) are free in the stock domain. -/
theorem upperFree_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 → ∀k:Fin 20,
    start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)+k.val≤min (start j+30+railP (start j+14)) 529 →
    start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)+k.val∈(W.compactSkywalkSignPoolA base (start j)).released ∨
      (start j+274≤start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)+k.val ∧ start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)+k.val<786) := by
  decide +kernel
theorem upperHead_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 → ∀q∈ArchiveJ7.rawHead (prev j)++support j,
    q<start j+Shadow7.sbP (start j)+48 ∨ 1043<q := by
  decide +kernel

theorem upper_clear (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24) (d:Bool) (raw s:State) (x p:Nat)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (q:Nat) (low:start j+Shadow7.sbP (start j)+48≤q) (high:q≤min (start j+30+railP (start j+14)) 529) :
    (run (Shadow7.body j (withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false := by
  have f:=EnterJ7.frame j
  have wn:windowNet j q=q:=by
    rw [windowNet,net]
    exact WideReference.sig_rail j q (le_trans high (min_le_right _ _)) (start j+14) (le_refl _)
  have same:EnterJ7.pull j q=q:=by
    rw [EnterJ7.pull]
    exact WideReference.sig_rail j q (le_trans high (min_le_right _ _)) (start j-1)
      (by have:=EnterJ7.frame j; simp only [Wire] at *; omega)
  have touch:¬Shadow7.MayTouch j (windowNet j q):=by
    rw [wn]; unfold Shadow7.MayTouch; simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *; simp only [Wire] at *; omega
  have port:q∉EnterJ7.ports j:=fun m=>by have:=EnterJ7.portsRegion j m; simp only [Wire] at *; omega
  have pend:q∉EnterJ7.pending j:=by
    simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false,Wire]; omega
  have notAdmin:q∉support j++ArchiveJ7.rawPortsList (prev j):=by
    rw [ArchiveJ7.raw_split,List.mem_append,List.mem_append]
    rintro (h|h|h)
    · have:=upperHead_all j (by omega) h21 q (List.mem_append_right _ h); simp only [Wire] at *; omega
    · have:=upperHead_all j (by omega) h21 q (List.mem_append_left _ h); simp only [Wire] at *; omega
    · obtain ⟨k,hk,eq⟩:=List.mem_map.mp h
      have tl:=ArchiveJ.tick_lt (prev j)
      rcases Shadow7.scratchS_cases _ k tl (List.mem_range.mp hk) with ⟨-,b1,-⟩|⟨-,b1,-⟩ <;>
        simp only [Wire] at * <;> omega
  have normal:=Shadow7.ext_head (Shadow7.enterP j) j (withArchive j d) (support j++ArchiveJ7.rawPortsList (prev j)) s a b q
    touch (EnterJ7.notWire j port) notAdmin (admin_cover j (by omega) h21 d)
  apply normal.trans
  have clean:(eraseSites (EnterJ7.pending j) s).basis q=false:=by
    by_cases inPair:q∈(EnterJ7.upperPairs j).map Prod.fst
    · obtain ⟨pair,hp,rfl⟩:=List.mem_map.mp inPair
      exact (cut.upper _ hp).1
    · have notHi:q∉RailPair.sites (EnterJ7.upperPairs j):=by
        intro m
        rcases EnterJ7.upperSites j m with ⟨u1,u2⟩|⟨u1,u2⟩
        · apply inPair
          simp only [Wire] at u1 u2
          simp only [EnterJ7.upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp]
          exact ⟨q-(start j+Shadow7.sbP (start j)+33),by omega,by omega⟩
        · simp only [Wire] at *; omega
      have above:start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)≤q:=by
        by_contra lo
        simp only [Nat.not_le] at lo
        apply inPair
        simp only [EnterJ7.upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp]
        exact ⟨q-(start j+Shadow7.sbP (start j)+33),by omega,by omega⟩
      have rl:start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)=start j+railP (start j)+16 ∧
          (257≤railP (start j) ∨ start j+railP (start j)=513) ∧ railP (start j+14)≤railP (start j):=by
        have:=j.isLt; simp only [Shadow7.wpP,railP,Shadow7.sbP,start]; split_ifs <;> omega
      have k0:q-(start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j))<20:=by omega
      have free:=upperFree_all j (by omega) h21 ⟨_,k0⟩ (by simp only; omega)
      simp only [show start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)+(q-(start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)))=q by omega] at free
      have hn:q≠EnterJ7.flagN j:=by simp only [EnterJ7.flagN,Wire]; omega
      have hf:q≠EnterJ7.flagF j:=by simp only [EnterJ7.flagF,Wire]; omega
      have hu:q≠EnterJ7.flagU j:=by simp only [EnterJ7.flagU,Wire]; omega
      have src:=WideReference.incoming_free_A (start j) x p (by simp only [start]; omega) raw domain q
        (by omega) (by omega) free
      exact (cut.unchanged q hn hf hu notHi).trans (by simpa only [pullState,same] using src)
  simpa [eraseSites,pend] using clean

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction CodecBitSliceVerify EnterProof PortalValues SkywalkRails Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! First-form window head (par-c2): what the first block's window keeps (pack only, no archive). -/
theorem adminBand_all : ∀ j : Fin 26, 0≤j.val → j.val≤24 → ∀q∈support j,
    q<Shadow7.sbP (start j)+804 ∨ (Shadow7.sbP (start j)+801+Shadow7.wpP (start j)≤q ∧ q<Shadow7.sbP (start j)+1574) ∨ Shadow7.sbP (start j)+1579<q := by
  decide +kernel
theorem free_admin (j : Fin 26) (h2 : 0≤j.val) (h19 : j.val≤24) : ∀q∈NativeJ7.protectedSites j,q∉support j := by
  intro q hq hm
  have b:=NativeJ7.protected_band j q hq
  have f:=EnterJ7.frame j
  have:=adminBand_all j h2 h19 q hm; simp only [Wire] at *; omega
theorem keeps_stored (j : Fin 26) (h2 : 0≤j.val) (h19 : j.val≤24) (d:Bool) (s:State) (m:List Bool) (q:Wire)
    (hq:q∈NativeJ7.protectedSites j) : (run (Shadow7.body j (program j d)) m s).basis q=s.basis q :=
  Shadow7.body_cover j (program j d) (NativeJ7.protectedSites j) (support j)
    (NativeJ7.free_native j) (free_admin j h2 h19) (codes j h2 d).1 s m q hq
theorem source_tags (j : Fin 26) (s:BasisState) (z:SkywalkNat.State) (G S:Bool)
    (hit:∀q∈wires EnterProof17.forward,s (EnterJ7.map j q)=(EnterProof17.shadowRow (Shadow7.sbP (start j)) 15 z G S).testBit q) :
    s (EnterJ7.flagN j)=false ∧ s (EnterJ7.flagF j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      s (EnterJ7.flagU j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u) :=
  (EnterProof17.actual_tags (EnterJ7.ports j) s (Shadow7.sbP (start j)) 15 z G S hit).2
theorem relay (j : Fin 26) (h2 : 0≤j.val) (h19 : j.val≤24) (d:Bool) (s:State) (m:List Bool) (h:Nat) (x y:Bool)
    (high:regValue (EnterJ7.saved j) s.basis=h) (hn:s.basis (EnterJ7.flagN j)=false) (hf:s.basis (EnterJ7.flagF j)=x)
    (hu:s.basis (EnterJ7.flagU j)=y) :
    let out:=run (Shadow7.body j (program j d)) m s
    regValue (EnterJ7.saved j) out.basis=h ∧ out.basis (EnterJ7.flagN j)=false ∧ out.basis (EnterJ7.flagF j)=x ∧
      out.basis (EnterJ7.flagU j)=y :=
  keep_values (EnterJ7.flagN j) (EnterJ7.flagF j) (EnterJ7.flagU j) (EnterJ7.saved j) s (run (Shadow7.body j (program j d)) m s)
    h x y (keeps_stored j h2 h19 d s m) high hn hf hu
theorem saved_at_leave (j : Fin 26) (h2 : 0≤j.val) (h19 : j.val≤24) (d:Bool) (raw cut:State) (z:SkywalkNat.State)
    (G S:Bool) (head ticks:List Bool) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (packed:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (negative S z.u) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u)) (pullState (EnterJ7.pull j) raw) cut)
    (input:SkywalkIntegerInput (EnterJ7.lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let out:=run (Shadow7.body j (program j d)) ticks (run (Shadow7.enterP j) head cut)
    regValue (EnterJ7.saved j) out.basis=(if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) ∧
      out.basis (EnterJ7.flagN j)=false ∧ out.basis (EnterJ7.flagF j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      out.basis (EnterJ7.flagU j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u) := by
  let pre:=run (Shadow7.enterP j) head cut
  have high:=EnterJ7.high_from_cut j raw cut z G S head small packed input
  have body0:=EnterJ7.from_full j raw cut z G S head small packed input
  have tags:=source_tags j pre.basis z G S body0.2.1
  exact relay j h2 h19 d pre ticks (if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) _ _
    high tags.1 tags.2.1 tags.2.2

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! First-form tail and upper rail (par-c2): as `NativeJ7.tail_clean/upper_clear` without archive and pending
(the first block's `e0+6..8` are spare, so its tail starts at `e0+6`, dadon's 225: `1724..1812`). -/
def tailTempsF (j : Fin 26) : List Wire :=
  List.range' (Shadow7.e0P (start j)+6) (min 1813 (2055-start j)-(Shadow7.e0P (start j)+6))
theorem tailF_mem (j : Fin 26) {q : Wire} (h : q∈tailTempsF j) :
    Shadow7.e0P (start j)+6≤q ∧ q≤1812 ∧ q+start j≤2054 := by
  simp only [tailTempsF,List.mem_range'_1] at h; simp only [Wire] at *; omega
theorem tailF_geometry (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) {q : Wire} (hq : q∈tailTempsF j) :
    windowNet j q=q ∧ EnterJ7.pull j q=q ∧ ¬Shadow7.MayTouch j q ∧ q∉EnterJ7.ports j ∧
    q≠EnterJ7.flagN j ∧ q≠EnterJ7.flagF j ∧ q≠EnterJ7.flagU j ∧ q∉RailPair.sites (EnterJ7.upperPairs j) := by
  have t:=tailF_mem j hq
  have f:=EnterJ7.frame j
  simp only [Shadow7.e0P] at t
  refine ⟨?_,?_,?_,fun m=>?_,?_,?_,?_,fun m=>?_⟩
  · rw [windowNet,net]
    exact Shadow7.sig_tail j h21 q (by have:=t.1; simp only [Shadow7.e0P,Wire] at *; omega) t.2.2 (start j+14) (le_refl _)
  · rw [EnterJ7.pull]
    exact Shadow7.sig_tail j h21 q (by have:=t.1; simp only [Shadow7.e0P,Wire] at *; omega) t.2.2 (start j-1)
      (by have:=EnterJ7.frame j; simp only [Wire] at *; omega)
  · unfold Shadow7.MayTouch; simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *; simp only [Wire] at *; omega
  · have:=EnterJ7.portsRegion j m; simp only [Wire] at *; omega
  · simp only [EnterJ7.flagN,Wire]; omega
  · simp only [EnterJ7.flagF,Wire]; omega
  · simp only [EnterJ7.flagU,Wire]; omega
  · have:=EnterJ7.upperSites j m; simp only [Wire] at *; omega
theorem tailFHead_all : ∀ j : Fin 26, 0≤j.val → j.val≤24 → ∀q∈support j,
    q<Shadow7.sbP (start j)+1580 ∨ 2055≤q+start j := by
  decide +kernel
theorem tailF_clean (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) (d:Bool) (x p:Nat) (raw v:State)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) v) :
    ∀q∈tailTempsF j,(run (Shadow7.body j (program j d)) b (run (Shadow7.enterP j) a v)).basis q=false := by
  intro q hq
  obtain ⟨wn,same,touch,port,hn,hf,hu,hi⟩:=tailF_geometry j h1 h21 hq
  have t:=tailF_mem j hq
  have notAdmin:q∉support j:=by
    intro h; have:=tailFHead_all j h1 h21 q h; simp only [Shadow7.e0P,Wire] at *; omega
  have stay:=Shadow7.ext_head (Shadow7.enterP j) j (program j d) (support j) v a b q
    (by rw [wn]; exact touch) (EnterJ7.notWire j port) notAdmin (codes j h1 d).1
  have read:=cut.unchanged q hn hf hu hi
  have canon:v.basis q=raw.basis q:=by simpa only [pullState,same] using read
  have zero:raw.basis q=false:=WideReference.domain_carry (by simp only [start]; omega) domain q
    (by simp only [Shadow7.e0P,Wire] at *; omega) t.2.1
  exact stay.trans (canon.trans zero)
theorem topFHead_all : ∀ j : Fin 26, 0≤j.val → j.val≤24 → ∀q∈support j,
    q≠Shadow7.sbP (start j)+1573 ∧ q≠Shadow7.sbP (start j)+803 := by
  decide +kernel
theorem topFHead2_all : ∀ j : Fin 26, 0≤j.val → j.val≤24 → ∀q∈support j,
    q≠Shadow7.sbP (start j)+1572 := by
  decide +kernel
theorem topF_clean (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) (d:Bool) (x p:Nat) (raw v:State)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) v) :
    ∀q:Wire,((q:Nat)+2=Shadow7.e0P (start j) ∨ (q:Nat)+1=Shadow7.e0P (start j)) →
      (run (Shadow7.body j (program j d)) b (run (Shadow7.enterP j) a v)).basis q=false := by
  intro q hq
  obtain ⟨wn,same,touch,port,pend,hn,hf,hu,hi⟩:=NativeJ7.top_geometry j h1 h21 hq
  have notAdmin:q∉support j:=by
    intro h; have:=(topFHead_all j h1 h21 q h).1; have:=topFHead2_all j h1 h21 q h; simp only [Shadow7.e0P,Wire] at *; omega
  have stay:=Shadow7.ext_head (Shadow7.enterP j) j (program j d) (support j) v a b q
    (by rw [wn]; exact touch) (EnterJ7.notWire j port) notAdmin (codes j h1 d).1
  have read:=cut.unchanged q hn hf hu hi
  have canon:v.basis q=raw.basis q:=by simpa only [pullState,same] using read
  have f:=EnterJ7.frame j
  have zero:raw.basis q=false:=WideReference.domain_carry (by simp only [start]; omega) domain q
    (by simp only [Shadow7.e0P,Wire] at *; omega) (by simp only [Shadow7.e0P,Wire] at *; omega)
  exact stay.trans (canon.trans zero)
theorem parkedF_clean (j : Fin 26) (h2 : 0≤j.val) (h19 : j.val≤24) (d:Bool) (raw cut:State)
    (z:SkywalkNat.State) (G S:Bool) (head ticks:List Bool) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (packed:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u)) (pullState (EnterJ7.pull j) raw) cut)
    (input:SkywalkIntegerInput (EnterJ7.lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    (run (Shadow7.body j (program j d)) ticks (run (Shadow7.enterP j) head cut)).basis (EnterJ7.parked j)=false := by
  have native : ∀q∈[EnterJ7.parked j],¬Shadow7.MayTouch j (windowNet j q) := by
    have f:=EnterJ7.frame j
    intro q hq
    have b:(q:Nat)=Shadow7.sbP (start j)+803:=by simpa only [EnterJ7.parked,List.mem_singleton] using hq
    have fix:windowNet j q=q:=by
      simp only [windowNet,net,OB5.sig]
      split <;> simp only [Wire] at * <;> omega
    rw [fix]
    unfold Shadow7.MayTouch
    simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *
    simp only [Wire] at *
    omega
  have admin:∀q∈[EnterJ7.parked j],q∉support j:=by
    intro q hq hm
    have b:(q:Nat)=Shadow7.sbP (start j)+803:=by simpa only [EnterJ7.parked,List.mem_singleton] using hq
    exact (topFHead_all j h2 h19 q hm).2 b
  rw [Shadow7.body_cover j (program j d) [EnterJ7.parked j] (support j) native admin (codes j h2 d).1 _ ticks
    (EnterJ7.parked j) (List.mem_singleton.mpr rfl)]
  have body0:=EnterJ7.from_full j raw cut z G S head small packed input
  exact EnterProof17.actual_parked (EnterJ7.ports j) _ (Shadow7.sbP (start j)) 15 z G S body0.2.1
theorem upperFreeF_all : ∀ j : Fin 26, 0≤j.val → j.val≤24 → ∀k:Fin 20,
    start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)+k.val≤min (start j+30+railP (start j+14)) 529 →
    start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)+k.val∈(W.compactSkywalkSignPoolA base (start j)).released ∨
      (start j+274≤start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)+k.val ∧ start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)+k.val<786) := by
  decide +kernel
theorem upperFHead_all : ∀ j : Fin 26, 0≤j.val → j.val≤24 → ∀q∈support j,
    q<start j+Shadow7.sbP (start j)+48 ∨ 1043<q := by
  decide +kernel

theorem upperF_clear (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) (d:Bool) (raw s:State) (x p:Nat)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) s)
    (q:Nat) (low:start j+Shadow7.sbP (start j)+48≤q) (high:q≤min (start j+30+railP (start j+14)) 529) :
    (run (Shadow7.body j (program j d)) b (run (Shadow7.enterP j) a s)).basis q=false := by
  have f:=EnterJ7.frame j
  have wn:windowNet j q=q:=by
    rw [windowNet,net]
    exact WideReference.sig_rail j q (le_trans high (min_le_right _ _)) (start j+14) (le_refl _)
  have same:EnterJ7.pull j q=q:=by
    rw [EnterJ7.pull]
    exact WideReference.sig_rail j q (le_trans high (min_le_right _ _)) (start j-1)
      (by have:=EnterJ7.frame j; simp only [Wire] at *; omega)
  have touch:¬Shadow7.MayTouch j (windowNet j q):=by
    rw [wn]; unfold Shadow7.MayTouch; simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *; simp only [Wire] at *; omega
  have port:q∉EnterJ7.ports j:=fun m=>by have:=EnterJ7.portsRegion j m; simp only [Wire] at *; omega
  have notAdmin:q∉support j:=by
    intro h; have:=upperFHead_all j h1 h21 q h; simp only [Wire] at *; omega
  have normal:=Shadow7.ext_head (Shadow7.enterP j) j (program j d) (support j) s a b q
    touch (EnterJ7.notWire j port) notAdmin (codes j h1 d).1
  apply normal.trans
  have clean:s.basis q=false:=by
    by_cases inPair:q∈(EnterJ7.upperPairs j).map Prod.fst
    · obtain ⟨pair,hp,rfl⟩:=List.mem_map.mp inPair
      exact (cut.upper _ hp).1
    · have notHi:q∉RailPair.sites (EnterJ7.upperPairs j):=by
        intro m
        rcases EnterJ7.upperSites j m with ⟨u1,u2⟩|⟨u1,u2⟩
        · apply inPair
          simp only [Wire] at u1 u2
          simp only [EnterJ7.upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp]
          exact ⟨q-(start j+Shadow7.sbP (start j)+33),by omega,by omega⟩
        · simp only [Wire] at *; omega
      have above:start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)≤q:=by
        by_contra lo
        simp only [Nat.not_le] at lo
        apply inPair
        simp only [EnterJ7.upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp]
        exact ⟨q-(start j+Shadow7.sbP (start j)+33),by omega,by omega⟩
      have rl:start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)=start j+railP (start j)+16 ∧
          (257≤railP (start j) ∨ start j+railP (start j)=513) ∧ railP (start j+14)≤railP (start j):=by
        have:=j.isLt; simp only [Shadow7.wpP,railP,Shadow7.sbP,start]; split_ifs <;> omega
      have k0:q-(start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j))<20:=by omega
      have free:=upperFreeF_all j h1 h21 ⟨_,k0⟩ (by simp only; omega)
      simp only [show start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)+(q-(start j+Shadow7.sbP (start j)+31+Shadow7.wpP (start j)))=q by omega] at free
      have hn:q≠EnterJ7.flagN j:=by simp only [EnterJ7.flagN,Wire]; omega
      have hf:q≠EnterJ7.flagF j:=by simp only [EnterJ7.flagF,Wire]; omega
      have hu:q≠EnterJ7.flagU j:=by simp only [EnterJ7.flagU,Wire]; omega
      have src:=WideReference.incoming_free_A (start j) x p (by simp only [start]; omega) raw domain q
        (by omega) (by omega) free
      exact (cut.unchanged q hn hf hu notHi).trans (by simpa only [pullState,same] using src)
  exact clean

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! `NativePack{s}.agree_origin` for an interior block, on wires `OB5.sig (s+14)` does not move.
    The band `[1301,1044+s+14]` is excluded by `still`: `sig` is not the identity there.
    Comparison is `box_origin_j`; the unmoved frame is `sig_fixed`. -/
/-! The first block of the window (`WideReference.firstBlock`) keeps only the last five stock ticks in
    `oldSites`, so the `rawHead`/`support` wires of the ten ticks before those are in neither `Box` nor `sites`.
    Every other block has the full 15. -/
theorem admin_outside (j : Fin 26) (h2 : 1≤j.val) (h21 : j.val≤24) (hne : start j≠WideReference.firstBlock)
    (q : Wire) (hq : q∈ArchiveJ7.rawHead (prev j)++support j) :
    WideReference.Box (start j) q ∨ q∈WideReference.sites (start j) := by
  have f:=EnterJ7.frame j
  have tick:start (prev j)+15=start j:=by simp only [prev,start]; omega
  have s10:(10:Nat)≤(start j:Nat):=by have h:=f.1; simp only [start] at h; omega
  have s15:(15:Nat)≤(start j:Nat):=by have h:=f.1; simp only [start] at h; omega
  have inSites (r:Nat) (hr1:start j-15≤r) (hr2:r<start j) :
      base r∈WideReference.sites (start j) ∧
      OB5.sig (start j) (base (1028+r))∈WideReference.sites (start j) ∧
      OB5.sig (start j) (base r)=base r ∧
      OB5.sig (start j) (base (1028+r))=OB5.sig (start j+14) (base (1028+r)) := by
    have hr:r≤405:=by have:=f; simp only [Wire] at *; omega
    have idA:OB5.sig (start j+14) (base r)=base r:=by
      rw [show base r=r+16 by simp [base]]
      exact WideReference.sig_fixed (by simp only [Wire] at *; omega) (by simp only [Wire] at *; omega)
    have idAs:OB5.sig (start j) (base r)=base r:=by
      rw [show base r=r+16 by simp [base]]
      exact WideReference.sig_fixed (by simp only [Wire] at *; omega) (by simp only [Wire] at *; omega)
    have eqB:OB5.sig (start j) (base (1028+r))=OB5.sig (start j+14) (base (1028+r)):=by
      rw [OB5.sig_base (start j) (1028+r) (by have:=f; simp only [start]; omega),
        OB5.sig_base (start j+14) (1028+r) (by have:=f; simp only [start]; omega)]
      have:=f; simp only [base, Wire] at *; split_ifs <;> omega
    refine ⟨?_,?_,idAs,eqB⟩
    · rw [← idA]; unfold WideReference.sites
      refine List.mem_map.mpr ⟨base r,?_,rfl⟩
      unfold WideReference.oldSites
      rw [WideReference.oldStart_interior hne, WideReference.oldCount_interior hne]
      simp only [List.mem_flatMap, List.mem_cons]
      exact ⟨r, List.mem_range'.mpr ⟨r-(start j-15), by omega, by omega⟩, Or.inl rfl⟩
    · unfold WideReference.sites
      refine List.mem_map.mpr ⟨base (1028+r),?_,eqB.symm⟩
      unfold WideReference.oldSites
      rw [WideReference.oldStart_interior hne, WideReference.oldCount_interior hne]
      simp only [List.mem_flatMap, List.mem_cons]
      exact ⟨r, List.mem_range'.mpr ⟨r-(start j-15), by omega, by omega⟩, Or.inr (Or.inl rfl)⟩
  have flagBox (n:Nat) (hn:n=6 ∨ n=7 ∨ n=8) : WideReference.Box (start j) (Shadow7.e0P (start j)+n) := by
    unfold WideReference.Box
    right; right; left
    have:=f; simp only [Shadow7.e0P, Wire] at *; rcases hn with rfl|rfl|rfl <;> omega
  simp only [List.mem_append, ArchiveJ7.rawHead, support, cellsLoadP, tick] at hq
  rcases hq with hq|hq
  · simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with ⟨k,hk,hq⟩|hq
    · rcases hq with rfl|rfl
      · right
        have cell:=inSites (start j-10+k) (by omega) (by omega)
        have addr:base (start j-10+k)=start j+6+k:=by
          simp only [base, Wire]; omega
        rw [← addr]; exact cell.1
      · right
        have cell:=inSites (start j-10+k) (by omega) (by omega)
        have addr:base (1028+(start j-10+k))=start j+1034+k:=by
          simp only [base, Wire]; omega
        rw [← addr]; exact cell.2.1
    · left
      rcases hq with rfl|rfl|rfl
      · exact flagBox 6 (Or.inl rfl)
      · exact flagBox 7 (Or.inr (Or.inl rfl))
      · exact flagBox 8 (Or.inr (Or.inr rfl))
  · simp only [List.mem_flatMap, List.mem_range', List.mem_cons, List.not_mem_nil, or_false] at hq
    obtain ⟨v,hv,hq⟩:=hq
    obtain ⟨i,hi,hsum⟩:=hv
    have hv1:start j-15≤v:=by simp only [start,Wire] at *; omega
    have hv2:v<start j-10:=by simp only [start,Wire] at *; omega
    right
    rcases hq with rfl|rfl
    · have cell:=inSites v hv1 (by omega)
      rw [cell.2.2.1]; exact cell.1
    · exact (inSites v hv1 (by omega)).2.1
theorem agree_origin (j : Fin 26) (h2 : 1≤j.val) (h21 : j.val≤24) (hne : start j≠WideReference.firstBlock) (d : Bool)
    (raw s : State) (m t : List Bool) (neg far long : Bool)
    (packed : PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j)
      (EnterJ7.flagF j) (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw)
      (eraseSites (EnterJ7.pending j) s))
    (q : Wire) (ext : ¬WideReference.Box (start j) q)
    (still : ¬(1301≤(q:Nat) ∧ (q:Nat)≤1044+(start j+14)))
    (mirror : ¬(2069≤(q:Nat)+(start j+14) ∧ (q:Nat)≤1812))
    (nh : ¬(369≤start j ∧ 1302≤(q:Nat)+start j ∧ (q:Nat)≤933)) :
    let history := run (Shadow7.body j (withArchive j d)) t (run (Shadow7.enterP j) m s)
    history.basis q = (WideReference.origin (start j) raw history).basis q := by
  intro history
  have f := EnterJ7.frame j
  have hw := WideReference.route_width (start j+14) (by have := f; omega)
  have h0 := WideReference.route_width (start j) (by have := f; omega)
  have wdef : Shadow7.wpP (start j) = railP (start j) - Shadow7.sbP (start j) - 15 := rfl
  have rdef : railP (start j) = W.narrowSkywalkRouteWidth (start j) := by
    rw [WideReference.route_eq (start j) (by have := f; omega)]; rfl
  have wn : windowNet j q = q := by
    rw [windowNet, net]; exact WideReference.sig_fixed still mirror
  have pullId : OB5.sig (start j-1) q = q := by
    refine WideReference.sig_fixed ?_ ?_
    · intro h; apply still; simp only [Wire] at *; omega
    · intro h; apply mirror; simp only [Wire] at *; omega
  have notMay : ¬Shadow7.MayTouch j q := by
    intro mt
    apply ext
    unfold Shadow7.MayTouch at mt
    have mid : (Shadow7.shape j).mid = Shadow7.sbP (start j)+15 := rfl
    rw [mid] at mt
    unfold WideReference.Box
    simp only [Wire] at *
    omega
  have free : ¬Shadow7.MayTouch j (windowNet j q) := by rwa [wn]
  have port : q∉EnterJ7.ports j := by
    intro mem
    apply ext
    have r := EnterJ7.portsRegion j mem
    unfold WideReference.Box
    simp only [Wire] at *
    omega
  apply WideReference.box_origin_j j ext raw history
  intro notSite
  have notAdmin : q∉support j++ArchiveJ7.rawPortsList (prev j) := by
    intro mem
    rw [ArchiveJ7.raw_split, List.mem_append, List.mem_append] at mem
    rcases mem with mem|mem|mem
    · rcases admin_outside j (by omega) h21 hne q (List.mem_append_right _ mem) with b|b
      · exact ext b
      · exact notSite b
    · rcases admin_outside j (by omega) h21 hne q (List.mem_append_left _ mem) with b|b
      · exact ext b
      · exact notSite b
    · obtain ⟨k,hk,eq⟩ := List.mem_map.mp mem
      have hk' := List.mem_range.mp hk
      have tick : start (prev j)+15 = start j := by simp only [prev, start]; omega
      have qeq : (q:Nat) = Shadow7.scratchS (start j) k := by simpa only [tick, Wire] using eq.symm
      have still' : ¬(1301 ≤ Shadow7.scratchS (start j) k ∧ Shadow7.scratchS (start j) k ≤ 1044+(start j+14)) := by
        rw [← qeq]; exact still
      have mirror' : ¬(2069 ≤ Shadow7.scratchS (start j) k+(start j+14) ∧ Shadow7.scratchS (start j) k ≤ 1812) := by
        rw [← qeq]; exact mirror
      rcases Shadow7.scratchS_cases (start j) k (by simp only [start]; omega) hk' with ⟨eqs,lo,hi⟩|⟨lo,hi⟩
      · apply ext
        unfold WideReference.Box
        rw [qeq]
        omega
      · exact nh ⟨lo, by rw [qeq]; omega⟩
  have stay := Shadow7.ext_head (Shadow7.enterP j) j (withArchive j d)
      (support j++ArchiveJ7.rawPortsList (prev j)) s m t q free (EnterJ7.notWire j port) notAdmin
      (admin_cover j (by omega) h21 d)
  have hn : q≠EnterJ7.flagN j := by
    intro eq; apply ext; rw [eq]; unfold WideReference.Box EnterJ7.flagN
    simp only [Wire] at *; omega
  have hf : q≠EnterJ7.flagF j := by
    intro eq; apply ext; rw [eq]; unfold WideReference.Box EnterJ7.flagF
    simp only [Wire] at *; omega
  have hu : q≠EnterJ7.flagU j := by
    intro eq; apply ext; rw [eq]; unfold WideReference.Box EnterJ7.flagU
    simp only [Wire] at *; omega
  have hi : q∉RailPair.sites (EnterJ7.upperPairs j) := by
    intro m; apply ext
    have u := EnterJ7.upperSites j m
    unfold WideReference.Box
    simp only [Wire] at *
    omega
  have pend : q∉EnterJ7.pending j := by
    intro mem; apply ext
    simp only [EnterJ7.pending, List.mem_cons, List.not_mem_nil, or_false] at mem
    unfold WideReference.Box
    simp only [Wire] at *
    rcases mem with rfl|rfl|rfl <;> omega
  have old := packed.unchanged q hn hf hu hi
  have same : history.basis q = (pullState (OB5.sig (start j-1)) raw).basis q := by
    rw [stay]
    simpa only [eraseSites, if_neg pend, EnterJ7.pull, pullId] using old
  exact same

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run measurementCount Shadow7.onRails

/-- The entry's saved high word is the leave's bank `ys` (dadon's literal lists agree per block). -/
theorem saved_ys (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) : EnterJ7.saved j = LeaveJ7.ys j := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have r := Shadow7.rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have wp3 : 3 ≤ Shadow7.wpP (start j) := by omega
  have hr : List.range (Shadow7.wpP (start j)) = List.range 3 ++ (List.range (Shadow7.wpP (start j) - 3)).map (3 + ·) := by
    rw [← List.range_add]; congr 1; omega
  rw [LeaveJ7.ys, hr, List.map_append, List.map_map]
  simp only [EnterJ7.saved, EnterJ7.upperTail, List.map_map]
  congr 1
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append,
      Shadow7.bankW, if_pos (show (0:Nat) < 3 by omega), if_pos (show (1:Nat) < 3 by omega), if_pos (show (2:Nat) < 3 by omega)]
    rw [ee]; simp only [List.cons.injEq, and_true]; omega
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp, Shadow7.bankW]
    rw [if_neg (by omega), if_pos (by omega)]
    (try unfold Wire at *); omega

/-- dadon's `NativePack{s}.admitted`, generic: block `j`'s window head delivers the leave's `Admission.Inputs`. -/
theorem admitted (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (x p:Nat) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (numbers:LeaveJ7.Admission.Numeric j z)
    (domain:WideReference.Domain (start j) x p raw)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    LeaveJ7.Admission.Inputs j (run (nextWindow j d) m s) z G S := by
  obtain ⟨w1, w2⟩ := start_win7 j (by omega) (by omega)
  have r := Shadow7.rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  have saved:=saved_with_pending j (by omega) (by omega) d raw s z G S m tape numbers.farSmall cut input
  have all:=next_window j (by omega) (by omega) d raw s m z G S numbers.odd numbers.farSmall cut input hist scratch past pg ps cross
    po pm prior
  obtain ⟨_,_,_,_,tags⟩:=real_receipt j (by omega) (by omega) d raw s m z G S numbers.odd numbers.farSmall cut input hist scratch
    past pg ps cross po pm prior
  -- the archive frame, for the overflow spares (dadon's 255 `extra_clean`)
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z numbers.farSmall numbers.odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m numbers.farSmall cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j (by omega) (by omega) d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity
    ready.2.1 scratch past pg ps cross po pm prior
  have final:=archive_result j (by omega) (by omega) d row limit _ _ frame
  have tail:=tail_clean j (by omega) (by omega) d x p raw s domain m tape _ _ _ cut row final
  have topc:=top_clean j (by omega) (by omega) d x p raw s domain m tape _ _ _ cut row final
  have parkedc:=parked_clean j (by omega) (by omega) d raw s z G S m tape numbers.farSmall cut input
  have runEq : run (nextWindow j d) m s = run (Shadow7.body j (withArchive j d)) tape pre := by
    simp only [nextWindow, window, run_append, run_take, pre, tape]
  apply LeaveJ7.Admission.assemble j (by omega) (by omega) _ z G S numbers all.2.1 all.2.2.1
  · rw [runEq, ←saved_ys j (by omega) (by omega)]
    refine ⟨saved.1, ?_, ?_, ?_⟩
    · have e : Shadow7.e0P (start j) + 5 = EnterJ7.flagN j := by simp only [EnterJ7.flagN, Shadow7.e0P]; omega
      rw [e]; exact saved.2.1
    · have e : Shadow7.e0P (start j) + 3 = EnterJ7.flagF j := by simp only [EnterJ7.flagF, Shadow7.e0P]; omega
      rw [e]; exact saved.2.2.1
    · have e : Shadow7.e0P (start j) + 4 = EnterJ7.flagU j := by simp only [EnterJ7.flagU, Shadow7.e0P]; omega
      rw [e]; exact saved.2.2.2
  · intro q hq
    rw [LeaveJ7.Admission.mem_spare] at hq
    rcases hq with rfl | rfl | ⟨lo, hi⟩
    · have t := tags ⟨0, by omega⟩
      have e : Shadow7.e0P (start j) + 6 = Shadow7.sbP (start j)+1580+0 := by simp only [Shadow7.e0P]; omega
      rw [e]; exact t
    · have t := tags ⟨1, by omega⟩
      have e : Shadow7.e0P (start j) + 7 = Shadow7.sbP (start j)+1580+1 := by simp only [Shadow7.e0P]; omega
      rw [e]; exact t
    · rw [runEq]
      apply tail q
      simp only [tailTemps, List.mem_range'_1]
      (try unfold Wire at *); omega
  · intro q lo hi
    rw [runEq]
    have only405 : ∀ k : Fin 26, 1 ≤ k.val → k.val ≤ 24 → min 4 (Shadow7.wpP (start k) + start k - 448) ≠ 0 → start k = 405 := by
      decide
    by_cases z2 : min 4 (Shadow7.wpP (start j) + start j - 448) = 0
    · omega
    · have e := only405 j (by omega) h19 z2
      have ha : Shadow7.a0P 405 = 483 := by decide
      have hs : Shadow7.sbP 405 = 46 := by decide
      have hw : Shadow7.wpP 405 = 47 := by decide
      have hr : railP (405 + 14) = 94 := by decide
      rw [e] at lo hi
      exact upper_clear j (by omega) (by omega) d raw s x p domain m tape _ _ _ cut q
        (by rw [e, hs]; omega) (by rw [e, hr]; omega)
  · rw [runEq]; exact topc _ (by simp only [Shadow7.e0P]; (try simp only [Wire] at *); omega)
  · rw [runEq]; exact topc _ (by simp only [Shadow7.e0P]; (try simp only [Wire] at *); omega)
  · rw [runEq]
    have e : Shadow7.b0P (start j) + 16 = EnterJ7.parked j := by simp only [EnterJ7.parked, Shadow7.b0P]; omega
    rw [e]; exact parkedc

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step Shadow7.onRails measurementCount

/-- dadon's `NativePack{s}.from_domain_matched`, generic (interior blocks `j ≥ 2`): from the stock-reference domain
at `start j`, the window head admits the leave, keeps the phase, keeps the previous archive at a row matching the
previous block's trace, and unwinds. `scratch` (the archive codec scratch is clean) is par-d2's `scratch_raw_clean`. -/
theorem from_domain_matched (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (m:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (pg ps cross:Bool)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) (unsigned (start (prev j)) x p) pg ps cross s) :
    let out:=run (nextWindow j d) m s
    LeaveJ7.Admission.Inputs j out (unsigned (start j) x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,RowTruth (unsigned (start (prev j)) x p) pg ps row ∧ Kept (ArchiveJ7.codePorts (prev j)) d row out) ∧
    ∀n,run (nextUnwind j d) n out=s:=by
  let z:=unsigned (start j) x p
  let past:=unsigned (start (prev j)) x p
  have nums:=LeaveJ7.Admission.actualNumbers j (by omega) (by omega) x p good
  have old:=LeaveJ7.Admission.actualNumbers (prev j) (by simp only [prev]; omega) (by simp only [prev]; omega) x p good
  have hist:=pulled_history j rfl domain
  have a:=next_window j (by omega) (by omega) d raw s m z G S nums.odd nums.farSmall cut input hist scratch past pg ps cross
    old.odd old.farSmall prior
  obtain ⟨row,limit,truth,code,_⟩:=real_receipt j (by omega) (by omega) d raw s m z G S nums.odd nums.farSmall cut input hist
    scratch past pg ps cross old.odd old.farSmall prior
  exact ⟨admitted j (by omega) (by omega) d x p raw s m z G S nums domain cut input hist scratch past pg ps cross old.odd old.farSmall
    prior,a.1,⟨row,limit,truth,code⟩,a.2.2.2⟩

/-- dadon's `NativePack{s}.from_domain`: `from_domain_matched` without the row's trace. -/
theorem from_domain (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (m:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (pg ps cross:Bool)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) (unsigned (start (prev j)) x p) pg ps cross s) :
    let out:=run (nextWindow j d) m s
    LeaveJ7.Admission.Inputs j out (unsigned (start j) x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,Kept (ArchiveJ7.codePorts (prev j)) d row out) ∧ ∀n,run (nextUnwind j d) n out=s:=by
  obtain ⟨i,ph,⟨row,limit,_,code⟩,un⟩:=from_domain_matched j (by omega) (by omega) d x p good raw s m domain G S cut input scratch pg ps
    cross prior
  exact ⟨i,ph,⟨row,limit,code⟩,un⟩

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2 (job D2): the archive scratch of block `j-1` is clean after block `j`'s head (enter, Shadow7.routed first tick,
pack), for every loader `2 ≤ j ≤ 19`. Each scratch wire `Shadow7.scratchW (start j) kk` is either
- below the live anchored block `e0..e0+9`: a carry wire of block `j`'s tick 1, clean on the rails; or
- above it (`e0+10 .. 1699`, only for loaders from 285 on: the old anchored blocks of blocks 270..j-1): a carry
  wire of the stock tick `start j`. The hand-off cut keeps it at its stock value (`PackedCut.frame`, it is no flag,
  pending flag or rail-pair site), `SkywalkIntegerInput` says that value is zero, and neither the enter, the first
  tick nor the pack touch it.
So no chain invariant is needed: the cut of `At{s}` already carries it. All geometry is `omega` over `j`. -/

theorem prev_tick (j : Fin 26) (h1 : 1≤j.val) : start (prev j)+15=start j := by
  simp only [prev,start]; (try simp only [Wire] at *); omega

/-- Archive scratch port `kk` of the archive loaded in block `j` (`Shadow7.scratchS`: the raw port `Shadow7.scratchW` while it
is a carry wire of the stock tick `start j`, a released B-rail wire beyond; equal to `Shadow7.scratchW` up to 360). -/
def scratchPort (j : Fin 26) (kk : Nat) : Wire := Shadow7.scratchS (start j) kk

theorem scratch_port (j : Fin 26) (h1 : 1≤j.val) (k : Fin 157) (hk : 23≤k.val) :
    ArchiveJ7.rawPorts (prev j) k=scratchPort j (k.val-23) := by
  have a:=ArchiveJ7.raw_scratch (prev j) (k:=k.val-23) (by omega)
  rw [show 23+(k.val-23)=k.val by omega,prev_tick j h1] at a
  rw [ArchiveJ7.rawPorts,a,scratchPort]

/-- Scratch wires below the live block are carry wires of block `j`'s tick 1. -/
theorem lower_carry (j : Fin 26) {kk : Nat} (h : 1556+kk+2<Shadow7.e0P (start j)) :
    1556+kk∈(IntegerPacket.ports (Shadow7.shape j) 1).carry.map (windowNet j) := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at h
  apply List.mem_map.mpr
  refine ⟨1556+kk,?_,?_⟩
  · simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,List.mem_range'_1]; (try simp only [Wire] at *); omega
  · simp only [windowNet,net,OB5.sig_nat,OB5.sigNat,start]
    split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | rfl | omega

theorem upper_enter (j : Fin 26) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) : w∉EnterJ7.ports j := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo
  intro mem
  simp only [EnterJ7.ports,List.mem_cons,List.not_mem_nil,or_false,Shadow7.sbP,start] at mem
  try simp only [Wire] at *
  omega

theorem upper_cut (j : Fin 26) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) :
    w≠EnterJ7.flagN j ∧ w≠EnterJ7.flagF j ∧ w≠EnterJ7.flagU j ∧ w∉EnterJ7.pending j ∧
      w∉RailPair.sites (EnterJ7.lowerPairs j) ∧ w∉RailPair.sites (EnterJ7.upperPairs j) := by
  have hj:=j.isLt
  have wb:Shadow7.wpP (start j)≤258:=by
    simp only [Shadow7.wpP,railP]; split <;> (try split) <;> omega
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo
  simp only [start] at wb
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp only [EnterJ7.flagN,Shadow7.sbP,start]; (try simp only [Wire] at *); omega
  · simp only [EnterJ7.flagF,Shadow7.sbP,start]; (try simp only [Wire] at *); omega
  · simp only [EnterJ7.flagU,Shadow7.sbP,start]; (try simp only [Wire] at *); omega
  · intro mem
    simp only [EnterJ7.pending,Shadow7.sbP,start,List.mem_cons,List.not_mem_nil,or_false] at mem
    try simp only [Wire] at *
    omega
  · intro mem
    simp only [RailPair.sites,EnterJ7.lowerPairs,Shadow7.sbP,start,List.flatMap_cons,List.flatMap_nil,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.append_nil] at mem
    try simp only [Wire] at *
    omega
  · intro mem
    simp only [RailPair.sites,EnterJ7.upperPairs,List.mem_flatMap,List.mem_map,List.mem_range,List.mem_cons,
      List.not_mem_nil,or_false] at mem
    obtain ⟨_,⟨i,hi,rfl⟩,e⟩:=mem
    simp only [Shadow7.sbP,start] at e hi
    try simp only [Wire] at *
    omega


end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2: D2's invariant for the 90..390 target, loaders `2 ≤ j ≤ 21`, for `Shadow7.scratchS` (window390: the
ports beyond the stock carry are re-hosted on released B-rail wires). With `w := Shadow7.scratchW t kk`, `t = start j`:
- `w` below `e0`: a tick-1 carry wire (as in `scratch_clean`).
- `w ≥ e0+10` and `w+t < 2068`: the port is `w`. The cut keeps it at its stock value, and the stock state has
  the whole 257-wire carry `1556..1812` clean (`WideReference.full_carry` from `Domain`).
- `w+t ≥ 2068` (only `t = 375, 390`): the port is the host `w-766 ∈ [1302-t, 933]`, a released wire of the stock
  B rail. The cut keeps it at its stock value, clean by `WideReference.released_clear`.
Enter, first tick and pack never touch these ports. -/

/-- Unwrapped upper ports (`w+t < 2069`) for `j ≤ 21`: untouched by the pack and the first tick. -/
theorem mid_support (j : Fin 26) (h21 : j.val≤24) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (nw : w+start j<2069) :
    w∉support j := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo nw
  intro mem
  simp only [support,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at mem
  obtain ⟨v,⟨v1,v2⟩,e⟩:=mem
  simp only [OB5.sig_nat,OB5.sigNat,base,start] at e v1 v2
  rcases e with e|e <;> split_ifs at e with hc <;> (try rcases hc with hc|hc) <;> omega

theorem mid_first (j : Fin 26) (h21 : j.val≤24) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (nw : w+start j<2069) :
    Shadow7.firstUnchanged j w := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo nw
  have key:OB5.sigNat (start j+14) w=w ∨ (OB5.sigNat (start j+14) w+w=3113 ∧ 1044+start j+1≤OB5.sigNat (start j+14) w) := by
    unfold OB5.sigNat
    simp only [start]
    split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | (left; rfl) | omega
  unfold Shadow7.firstUnchanged
  dsimp only
  right
  show OB5.sigNat (start j+14) w∉(IntegerPacket.ports (Shadow7.shape j) 0).wires
  generalize OB5.sigNat (start j+14) w=r at key ⊢
  intro mem
  simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at mem
  omega

theorem mid_pull (j : Fin 26) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (nw : w+start j<2069) :
    EnterJ7.pull j w=w := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo nw
  show @Eq Nat (OB5.sigNat (start j-1) w) w
  simp only [OB5.sigNat,start]
  split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | rfl | omega

/-- window390: a scratch host `q ∈ [1302-t, 933]` (`t = start j`; loaders at 375 and 390) is a released B-rail wire
above the three park slots: no head piece touches it and it is no flag, pending flag or rail-pair site. -/
theorem host_geometry (j : Fin 26) (h21 : j.val≤24) {q : Nat} (lo : 1302≤q+start j) (hi : q≤933) :
    q∉support j ∧ Shadow7.firstUnchanged j q ∧ q∉EnterJ7.ports j ∧ q≠EnterJ7.flagN j ∧ q≠EnterJ7.flagF j ∧
      q≠EnterJ7.flagU j ∧ q∉EnterJ7.pending j ∧ q∉RailPair.sites (EnterJ7.lowerPairs j) ∧
      q∉RailPair.sites (EnterJ7.upperPairs j) := by
  have hj:=j.isLt
  have wb:Shadow7.wpP (start j)≤258:=by
    simp only [Shadow7.wpP,railP]; split <;> (try split) <;> omega
  have f:=EnterJ7.frame j
  have top:Shadow7.wpP (start j)+Shadow7.sbP (start j)+start j≤498:=by
    have r:railP (start j)=513-start j:=by unfold railP; rw [if_neg (by omega),if_neg (by omega)]
    have wdef:Shadow7.wpP (start j)=railP (start j)-Shadow7.sbP (start j)-15:=rfl
    omega
  simp only [Shadow7.sbP,start] at top
  simp only [start] at lo
  simp only [start] at wb
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro mem
    simp only [support,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at mem
    obtain ⟨v,⟨v1,v2⟩,e⟩:=mem
    simp only [OB5.sig_nat,OB5.sigNat,base,start] at e v1 v2
    rcases e with e|e <;> split_ifs at e with hc <;> (try rcases hc with hc|hc) <;> omega
  · unfold Shadow7.firstUnchanged
    dsimp only
    right
    show OB5.sigNat (start j+14) q∉(IntegerPacket.ports (Shadow7.shape j) 0).wires
    have key:OB5.sigNat (start j+14) q=q:=by
      unfold OB5.sigNat; simp only [start]
      split_ifs with hc <;> (try rcases hc with hc|hc) <;> omega
    rw [key]
    intro mem
    simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
      SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at mem
    omega
  · intro mem
    simp only [EnterJ7.ports,List.mem_cons,List.not_mem_nil,or_false,Shadow7.sbP,start] at mem
    omega
  · simp only [EnterJ7.flagN,Shadow7.sbP,start]; omega
  · simp only [EnterJ7.flagF,Shadow7.sbP,start]; omega
  · simp only [EnterJ7.flagU,Shadow7.sbP,start]; omega
  · intro mem
    simp only [EnterJ7.pending,Shadow7.sbP,start,List.mem_cons,List.not_mem_nil,or_false] at mem
    omega
  · intro mem
    simp only [RailPair.sites,EnterJ7.lowerPairs,Shadow7.sbP,start,List.flatMap_cons,List.flatMap_nil,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.append_nil] at mem
    omega
  · intro mem
    simp only [RailPair.sites,EnterJ7.upperPairs,List.mem_flatMap,List.mem_map,List.mem_range,List.mem_cons,
      List.not_mem_nil,or_false] at mem
    obtain ⟨_,⟨i,hi',rfl⟩,e⟩:=mem
    simp only [Shadow7.sbP,start] at e hi'
    omega

/-- window390: the placement before the block does not move a host. -/
theorem host_pull (j : Fin 26) {q : Nat} (hi : q≤933) : EnterJ7.pull j q=q := by
  have hj:=j.isLt
  show @Eq Nat (OB5.sigNat (start j-1) q) q
  simp only [OB5.sigNat,start]
  split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | rfl | omega

/-- **D2's invariant, 90..390 form.** After block `j`'s head every wrapped archive scratch port is clean, for every
loader `2 ≤ j ≤ 21`. Inputs: `At{s}`'s domain and cut, the bounds, and the rails after the enter. -/
theorem scratch_wire_clean (j : Fin 26) (h2 : 1≤j.val) (h21 : j.val≤24) (d:Bool) (raw s:State) (m:List Bool)
    (x p:Nat) (good:WideReference.Bounds x p) (domain:WideReference.Domain (start j) x p raw)
    (neg far long:Bool) (Z:SkywalkRails.State) (parity:(Z.a+Z.b)%2=1)
    (active:Shadow7.onRails j 0 Z (run (Shadow7.enterP j) m s).basis)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s)) :
    ∀kk<134,
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (scratchPort j kk)=false := by
  intro kk hk
  dsimp only
  have hj:=j.isLt
  have carryTop (r:Nat) (r1:1556≤r) (r2:r≤1812):raw.basis r=false:=by
    have h:=WideReference.full_carry (start j) 0 x p (by simp only [start]; omega) good raw domain [] r r1 r2
    simpa only [WideReference.span,run] using h
  -- the head keeps a port that no head piece touches, and the cut keeps it at its stock value
  have viaCut (q:Wire) (ns:q∉support j) (nf:Shadow7.firstUnchanged j q) (ne:q∉EnterJ7.ports j) (nN:q≠EnterJ7.flagN j)
      (nF:q≠EnterJ7.flagF j) (nU:q≠EnterJ7.flagU j) (nP:q∉EnterJ7.pending j)
      (nLo:q∉RailPair.sites (EnterJ7.lowerPairs j)) (nHi:q∉RailPair.sites (EnterJ7.upperPairs j))
      (clean:raw.basis (EnterJ7.pull j q)=false) :
      (run (program j d) ((m.drop (measurementCount (Shadow7.enterP j))).drop (measurementCount (Shadow7.routed j 0 1)))
        (run (Shadow7.routed j 0 1) (m.drop (measurementCount (Shadow7.enterP j))) (run (Shadow7.enterP j) m s))).basis q=false:=by
    rw [run_preserves_outside _ _ _ _ (fun used=>ns (List.mem_toFinset.mp ((codes j (by omega) d).1 used))),
      Shadow7.first_preserves j Z parity _ _ active _ nf,
      run_preserves_outside _ _ _ _ (EnterJ7.notWire j ne)]
    have f:=cut.frame _ nN nF nU nLo nHi
    simp only [eraseSites,nP,↓reduceIte,pullState] at f
    rw [f]
    exact clean
  by_cases low:1556+kk<Shadow7.e0P (start j)
  · have idp:scratchPort j kk=1556+kk:=by
      show Shadow7.scratchS (start j) kk=1556+kk
      have e0:=Shadow7.scratchW_low (start j) kk low
      rw [Shadow7.scratchS_eq (start j) kk (by simp only [start]; omega)
        (by rw [e0]; simp only [Shadow7.e0P,Shadow7.sbP,start] at low ⊢; omega),e0]
    rw [idp]
    by_cases topw:1556+kk+2=Shadow7.e0P (start j) ∨ 1556+kk+1=Shadow7.e0P (start j)
    · -- margin 17: the wire below the anchored block is no tick-1 carry; the cut keeps it at its (clean) stock value
      have f:=EnterJ7.frame j
      obtain ⟨_,same,_,port,pend,hn,hf,hu,hi⟩:=top_geometry j (by omega) h21 (q:=1556+kk) topw
      have ns:(1556+kk:Wire)∉support j:=fun h=>by
        have:=(topHead_all j (by omega) h21 _ (List.mem_append_right _ h)).1
        have:=topHead2_all j (by omega) h21 _ (List.mem_append_right _ h)
        simp only [Shadow7.e0P] at topw; simp only [Wire] at *; omega
      have nLo:(1556+kk:Wire)∉RailPair.sites (EnterJ7.lowerPairs j):=by
        intro mem
        simp only [RailPair.sites,EnterJ7.lowerPairs,List.flatMap_cons,List.flatMap_nil,List.mem_append,
          List.mem_cons,List.not_mem_nil,or_false,List.append_nil] at mem
        simp only [Shadow7.e0P] at topw
        simp only [Wire] at *
        omega
      apply viaCut _ ns (top_first j h21 topw) port hn hf hu pend nLo hi
      rw [same]
      exact carryTop _ (by omega) (by simp only [Shadow7.e0P] at topw; omega)
    · have on:=completed_head j (by omega) d (run (Shadow7.enterP j) m s) (m.drop (measurementCount (Shadow7.enterP j)))
        ((m.drop (measurementCount (Shadow7.enterP j))).drop (measurementCount (Shadow7.routed j 0 1))) Z parity active
      obtain ⟨c,hc,eq⟩:=List.mem_map.mp (lower_carry j (show 1556+kk+2<Shadow7.e0P (start j) by omega))
      rw [←eq]
      exact (regValue_zero _ _).mp on.2.2.2.1 _ hc
  · have hw:Shadow7.scratchW (start j) kk=1566+kk:=if_neg low
    have lo:Shadow7.e0P (start j)+10≤1566+kk:=by omega
    have hi:1566+kk≤1699:=by omega
    by_cases nw:1566+kk+start j<2068
    · have idp:scratchPort j kk=1566+kk:=by
        show Shadow7.scratchS (start j) kk=1566+kk
        rw [Shadow7.scratchS_eq (start j) kk (by simp only [start]; omega) (by rw [hw]; exact nw),hw]
      rw [idp]
      obtain ⟨nN,nF,nU,nP,nLo,nHi⟩:=upper_cut j lo
      apply viaCut _ (mid_support j h21 lo (by omega)) (mid_first j h21 lo (by omega)) (upper_enter j lo) nN nF nU nP nLo nHi
      rw [mid_pull j lo (by omega)]
      exact carryTop _ (by omega) (by omega)
    · have wr:2068≤1566+kk+start j:=by omega
      have tj:375≤start j ∧ start j≤405:=by simp only [start] at wr ⊢; omega
      have idp:scratchPort j kk=800+kk:=by
        show Shadow7.scratchS (start j) kk=800+kk
        rw [Shadow7.scratchS_high (start j) kk (by omega) hk (by rw [hw]; exact wr),hw]
        omega
      rw [idp]
      have q1:1302≤800+kk+start j:=by omega
      have q2:800+kk≤933:=by omega
      obtain ⟨ns,nf,ne,nN,nF,nU,nP,nLo,nHi⟩:=host_geometry j h21 q1 q2
      apply viaCut _ ns nf ne nN nF nU nP nLo nHi
      rw [host_pull j q2]
      exact WideReference.released_clear (i:=start j) (by omega) (by omega) domain (800+kk) (by omega) (by omega)

/-- The same in `ArchiveJ7.rawPorts` form (`next_window`'s `scratch` hypothesis), for every loader `2 ≤ j ≤ 21`. -/
theorem scratch_raw_clean (j : Fin 26) (h2 : 1≤j.val) (h21 : j.val≤24) (d:Bool) (raw s:State) (m:List Bool)
    (x p:Nat) (good:WideReference.Bounds x p) (domain:WideReference.Domain (start j) x p raw)
    (neg far long:Bool) (Z:SkywalkRails.State) (parity:(Z.a+Z.b)%2=1)
    (active:Shadow7.onRails j 0 Z (run (Shadow7.enterP j) m s).basis)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s)) :
    ∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false := by
  intro k hk
  dsimp only
  rw [scratch_port j (by omega) k hk]
  exact scratch_wire_clean j (by omega) h21 d raw s m x p good domain neg far long Z parity active cut (k.val-23) (by omega)

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}ArchiveCut.result`: the archive facts of the next pack, after the leave. -/
theorem result (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (g sg : Bool) (h : Admission.Inputs j s z g sg) :
    PastFacts j (ArchiveJ7.rawPorts j) (Shadow7.sbP (start j)) z g sg
      (HighBankSum.crossBit (TrueMiddle.d j z)) (run (Shadow7.leaveP j) m s) := by
  let u := Admission.flags z g sg
  let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v)
  have par := RecordedParity.result j h0 (by omega) s z g sg ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z =
      LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j h0 (by omega) s z g sg ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have all := ActualHistory.result j h0 (by omega) s m z u.1 u.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero ⟨h.nextFarSmall, h.endSmall⟩ h.fit h.far h.side g sg h.record
  exact ⟨all.1, all.2.1, all.2.2.1, all.2.2.2⟩

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.ArchiveCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.AssembleCut
open Arithmetic WideReference RailPair Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

/-- The route widths are `railP` on the window. -/
theorem route_rail (k : Nat) (hk : k ≤ 510) : W.narrowSkywalkRouteWidth k = railP k := by
  rw [WideReference.route_eq k hk]; rfl

/-- par-c1's leave box lies inside the wide reference box. -/
theorem box_of_box2 (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (q : Wire)
    (h : Shadow7.leaveBox2 (start j) q) : WideReference.Box (start j) q := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have r14 := Partial.rail14 (start j)
  unfold Shadow7.leaveBox2 at h
  unfold WideReference.Box
  rw [route_rail (start j) (by omega), route_rail (start j+14) (by omega)]
  simp only [Wire] at *
  omega

/-- dadon's `Leave{s}AssembleCut.result`, generic. The frame is split on the wide box: inside it the leftovers
(`left`), the carry scratch (`zs`/`clear` against the origin's clean carry, `carry`) and the next rails
(`low`/`high`); outside it the stock exterior (`ext`) and the older moved history (`mirror`, empty while
`start j ≤ 257`). -/
theorem result (j k : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (hk0 : 1 ≤ k.val) (hk1 : k.val ≤ 25)
    (hs:start k=start j+15) (s o : State) (neg far long : Bool)
    (phase : s.phase=o.phase) (sign : s.basis (EnterJ7.flagN k)=neg) (mode : s.basis (EnterJ7.flagF k)=far)
    (side : s.basis (EnterJ7.flagU k)=long)
    (low : ∀i:Fin (Shadow7.sbP (start k)+17), s.basis (start k+16+i.val)=o.basis (start k+16+i.val) ∧
      s.basis (786+i.val)=o.basis (786+i.val))
    (high : ∀i:Fin (Shadow7.wpP (start k)-2), s.basis (start k+Shadow7.sbP (start k)+33+i.val)=false ∧
      s.basis (Shadow7.sbP (start k)+803+i.val)=(if o.basis (EnterJ7.gate k) then o.basis (Shadow7.sbP (start k)+803+i.val)
        else o.basis (start k+Shadow7.sbP (start k)+33+i.val)))
    (ext : ∀q:Wire,¬WideReference.Box (start j) q → ¬leftovers j q → ¬(2070≤(q:Nat)+start j ∧ (q:Nat)≤1812) →
      s.basis q=o.basis q)
    (mirror : ∀q:Nat,2070≤q+start j → q≤1812 → s.basis q=o.basis q)
    (left : ∀q,leftovers j q → s.basis q=o.basis q)
    (zs : List Wire) (clear : ∀q∈zs,s.basis q=false)
    (zcover : ∀q:Nat,1556≤q → q≤1812 → WideReference.Box (start j) q → ¬leftovers j q → q∉EnterJ7.pending k →
      q≠EnterJ7.flagN k → q≠EnterJ7.flagF k → q≠EnterJ7.flagU k → q∈zs)
    (rails : ∀q:Nat,WideReference.Box (start j) q → ¬leftovers j q → q<1556 →
      (start k+16≤q ∧ q<start k+Shadow7.sbP (start k)+31+Shadow7.wpP (start k)) ∨ (786≤q ∧ q<Shadow7.sbP (start k)+801+Shadow7.wpP (start k)))
    (carry : ∀q:Nat,1556≤q → q+start j≤2054 → q≤1812 → o.basis q=false) :
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k) neg far long o (eraseSites (EnterJ7.pending k) s) := by
  have f:=EnterJ7.frame k
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  have rj := Shadow7.rail_win w1 w2
  have away (q:Wire) (small:q<1556) : (eraseSites (EnterJ7.pending k) s).basis q=s.basis q := by
    have no:q∉EnterJ7.pending k:=by
      simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false]; simp only [Wire] at *; omega
    simp [eraseSites,no]
  have flagOff (q:Wire) (h:q=Shadow7.sbP (start k)+1579 ∨ q=Shadow7.sbP (start k)+1577 ∨ q=Shadow7.sbP (start k)+1578) :
      (eraseSites (EnterJ7.pending k) s).basis q=s.basis q := by
    have no:q∉EnterJ7.pending k:=by
      simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false]; simp only [Wire] at *; omega
    simp [eraseSites,no]
  refine ⟨phase,?_,?_,?_,?_,?_,?_⟩
  · show (eraseSites (EnterJ7.pending k) s).basis (Shadow7.sbP (start k) + 1579) = neg
    rw [flagOff _ (Or.inl rfl)]; exact sign
  · show (eraseSites (EnterJ7.pending k) s).basis (Shadow7.sbP (start k) + 1577) = far
    rw [flagOff _ (Or.inr (Or.inl rfl))]; exact mode
  · show (eraseSites (EnterJ7.pending k) s).basis (Shadow7.sbP (start k) + 1578) = long
    rw [flagOff _ (Or.inr (Or.inr rfl))]; exact side
  · intro pair mem
    simp only [EnterJ7.lowerPairs,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl <;> dsimp only <;>
    · rw [away _ (by simp only [Wire] at *; omega),away _ (by simp only [Wire] at *; omega)]
      first
      | exact (show _ from by have l:=low ⟨Shadow7.sbP (start k)+15,by omega⟩; simp only at l
                              rw [show start k+16+(Shadow7.sbP (start k)+15)=start k+Shadow7.sbP (start k)+31 by omega,
                                show 786+(Shadow7.sbP (start k)+15)=Shadow7.sbP (start k)+801 by omega] at l; exact l)
      | exact (show _ from by have l:=low ⟨Shadow7.sbP (start k)+16,by omega⟩; simp only at l
                              rw [show start k+16+(Shadow7.sbP (start k)+16)=start k+Shadow7.sbP (start k)+32 by omega,
                                show 786+(Shadow7.sbP (start k)+16)=Shadow7.sbP (start k)+802 by omega] at l; exact l)
  · intro pair mem
    simp only [EnterJ7.upperPairs,List.mem_map,List.mem_range] at mem
    obtain ⟨i,hi,rfl⟩:=mem
    dsimp only
    rw [away _ (by simp only [Wire] at *; omega),away _ (by simp only [Wire] at *; omega)]
    exact high ⟨i,hi⟩
  · intro q notN notF notU notLo notHi
    by_cases pend:q∈EnterJ7.pending k
    · have r:1556≤(q:Nat) ∧ (q:Nat)+start j≤2054 ∧ (q:Nat)≤1812:=by
        simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false] at pend
        rw [hs] at pend
        simp only [Wire] at *; omega
      simp [eraseSites,pend,carry q r.1 r.2.1 r.2.2]
    simp only [eraseSites,if_neg pend]
    by_cases lf:leftovers j q
    · exact left q lf
    have lf' := lf
    unfold leftovers ReleasedOrigin.releasedSite at lf'
    simp only [not_or, not_and] at lf'
    by_cases inBox:WideReference.Box (start j) q
    · have inBox' := inBox
      unfold WideReference.Box at inBox'
      rw [route_rail (start j) (by omega), route_rail (start j+14) (by omega)] at inBox'
      have r14 := Partial.rail14 (start j)
      by_cases hc:1556≤(q:Nat)
      · have top:(q:Nat)+start j≤2054 ∧ (q:Nat)≤1812:=by
          simp only [Wire] at *
          rcases inBox' with h|h|h|h <;> omega
        rw [carry q hc top.1 top.2]
        exact clear q (zcover q hc top.2 inBox lf pend notN notF notU)
      · rcases rails q inBox lf (by simp only [Wire] at *; omega) with ⟨a1,a2⟩|⟨b1,b2⟩
        · by_cases lo:(q:Nat)<start k+Shadow7.sbP (start k)+33
          · have l:=(low ⟨q-(start k+16),by simp only [Wire] at *; omega⟩).1; simp only at l
            rw [show start k+16+(q-(start k+16))=(q:Nat) by simp only [Wire] at *; omega] at l; exact l
          · exfalso; apply notHi
            simp only [RailPair.sites,EnterJ7.upperPairs,List.mem_flatMap,List.mem_map,List.mem_range]
            exact ⟨_,⟨q-(start k+Shadow7.sbP (start k)+33),by simp only [Wire] at *; omega,rfl⟩,
              by simp only [List.mem_cons]; left; simp only [Wire] at *; omega⟩
        · by_cases lo:(q:Nat)<Shadow7.sbP (start k)+803
          · have l:=(low ⟨q-786,by simp only [Wire] at *; omega⟩).2; simp only at l
            rw [show 786+(q-786)=(q:Nat) by simp only [Wire] at *; omega] at l; exact l
          · exfalso; apply notHi
            simp only [RailPair.sites,EnterJ7.upperPairs,List.mem_flatMap,List.mem_map,List.mem_range]
            exact ⟨_,⟨q-(Shadow7.sbP (start k)+803),by simp only [Wire] at *; omega,rfl⟩,
              by simp only [List.mem_cons,List.mem_singleton]; right; simp only [Wire] at *; omega⟩
    · by_cases mi:2070≤(q:Nat)+start j ∧ (q:Nat)≤1812
      · exact mirror q mi.1 mi.2
      · exact ext q inBox lf mi

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.AssembleCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl
theorem both (P Q:Prop) [Decidable P] [Decidable Q] : (decide P && decide Q)=decide (P ∧ Q) := by
  by_cases a:P <;> by_cases b:Q <;> simp [a,b]

/-- The rail of a window block narrows by at most one wire per tick, never widens, and when it narrows over the
block it narrows at the block's last tick. -/
theorem rail_step (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    railP (start j+14) ≤ railP (start j+15) + 1 ∧ railP (start j+14) ≤ railP (start j) ∧
    railP (start j+15) ≤ railP (start j) ∧ start j + 30 + railP (start j+15) ≤ 529 ∧
    (railP (start j+15) < railP (start j) → railP (start j+14) = railP (start j+15) + 1 ∧
      start j + 31 + railP (start j+15) ≤ 529) := by
  have e : start j = 45 + 15 * j.val := rfl
  rw [e]
  unfold railP; refine ⟨?_,?_,?_,?_,?_⟩ <;> (try intro) <;> split_ifs at * <;> omega

/-- dadon's `Leave{s}CertifiedCut.result`, generic: the leave's output is the packed cut of the next block `k`
(`start k = start j + 15`). The window side comes in as `ext` (the stock exterior of the wide box), `mirror`
(the older moved history), `upper` (the A rail above the join, dadon's `upper`), `band` (the sig band
`[1301, s+1058]`, empty before 243) and `quiet` (the raw sites). -/
theorem result (j k : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (hk0 : 1 ≤ k.val) (hk1 : k.val ≤ 25)
    (hs : start k = start j + 15)
    (x p : Nat) (good : Bounds x p) (raw s : State) (m : List Bool) (g0 s0 : Bool)
    (h : Admission.Inputs j s (unsigned (start j) x p) g0 s0)
    (dom : Domain (start j) x p raw)
    (input : InputAt (start j) (encode g0 s0 (unsigned (start j) x p).u (unsigned (start j) x p).v) raw)
    (phase : s.phase = (origin (start j) raw s).phase)
    (ext : ∀ q:Wire, ¬WideReference.Box (start j) q → ¬AssembleCut.leftovers j q →
      ¬(2070≤(q:Nat)+start j ∧ (q:Nat)≤1812) → s.basis q = (origin (start j) raw s).basis q)
    (mirror : ∀ q:Nat, 2070≤q+start j → q≤1812 → s.basis q = (origin (start j) raw s).basis q)
    (upper : ∀ q:Nat, Shadow7.a0P (start j)+16 ≤ q → q ≤ min (start j+30+railP (start j+14)) 529 → s.basis q = false)
    (band : ∀ q:Nat, 1301 ≤ q → q ≤ 1058+start j → s.basis q = false)
    (hosts : ∀ q:Nat, 369 ≤ start j → 1302 ≤ q+start j → q ≤ 933 → s.basis q = false)
    (quiet : ∀ q ∈ CoreCheckpoint.rawSites j, s.basis q = false) :
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k) (PortalValues.negative (Admission.flags (unsigned (start j) x p) g0 s0).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k)) ≤ (unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) (endRaw (start j) raw s)) (eraseSites (EnterJ7.pending k) (run (Shadow7.leaveP j) m s)) := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  obtain ⟨st1, st2, st3, st4, st5⟩ := rail_step j h0 (by omega)
  have r14 := Partial.rail14 (start j)
  let z := unsigned (start j) x p
  let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have endpointState : SkywalkNat.step^[15] z = unsigned (start k) x p := by
    show SkywalkNat.step^[15] (SkywalkNat.step^[start j] (SkywalkNat.init x p)) =
      SkywalkNat.step^[start k] (SkywalkNat.init x p)
    rw [hs, Nat.add_comm, Function.iterate_add_apply]
  have par := RecordedParity.result j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z =
      LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have bits := EndWords.result (flag := LeaveJ7.RecordedEvents.glueFlag j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side) j h0 (by omega) s m z
    (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.fit xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
    ev.1 h.far h.side
  have whole := Whole.result (flag := LeaveJ7.RecordedEvents.glueFlag j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side) j h0 (by omega) s m z
    (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.fit xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
    ev.1 h.far h.side
  have carried := StockWindowTicket.stepInput_gen_shadow7 (start j) (Shadow7.sbP (start j)) x p (by omega) (by omega) good raw s
    g0 s0 dom input h.farSmall
  have nextInput : SkywalkIntegerInput (WideWords.L j)
      (SkywalkRails.encode (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 (SkywalkNat.step^[15] z).u
        (SkywalkNat.step^[15] z).v).a
      (SkywalkRails.encode (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 (SkywalkNat.step^[15] z).u
        (SkywalkNat.step^[15] z).v).b (Admission.flags z g0 s0).1 (endRaw (start j) raw s).basis := by
    have c2 := carried.2
    unfold InputAt StockWindowTicket.signedAt at c2
    rw [flagEq] at c2
    have eA : SkywalkNat.step^[15] z = unsigned (start j+15) x p := hs ▸ endpointState
    rw [eA]
    exact c2
  have highZero : ∀ q : Nat, Shadow7.a0P (start j) + 16 ≤ q → q ≤ (start j) + 30 + railP ((start j) + 15) → s.basis q = false :=
    fun q lo hi => upper q lo (Nat.le_min.mpr ⟨by omega, by omega⟩)
  have rails := BoundaryRails.result (flag := LeaveJ7.RecordedEvents.glueFlag j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side) (top2 := h.top2) j h0 (by omega) s m z
    (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.fit xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
    ev.1 h.far h.side highZero h.top (endRaw (start j) raw s) nextInput
  have eo : pullState (OB5.sig (start j + 14)) (endRaw (start j) raw s) = origin (start j) raw s :=
    endpoint (start j) (by omega) raw s
  simp only [eo] at rails
  have kept := PreservedRecords.result j h0 (by omega) s m bits.2.2.2.1
  have clear := BoundaryClean.result (flag := LeaveJ7.RecordedEvents.glueFlag j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record h.far h.side) j h0 (by omega) s m z
    (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.fit xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
    ev.1 h.far h.side quiet (terminal_fit j h0 (by omega) x p good)
  have pre : ∀ q : Wire, (railP ((start j) + 15) < railP (start j) ∧ q = (start j) + 31 + railP ((start j) + 15)) ∨
      (1301 ≤ q ∧ q ≤ 1058 + (start j)) ∨ (369 ≤ start j ∧ 1302 ≤ q + start j ∧ q ≤ 933) → s.basis q = false := by
    intro q hq
    rcases hq with ⟨sh, rfl⟩ | ⟨lo, hi⟩ | ⟨t369, lo, hi⟩
    · have st := st5 sh
      exact upper _ (by omega) (Nat.le_min.mpr ⟨by omega, by omega⟩)
    · exact band q lo hi
    · exact hosts q t369 lo hi
  have rel := ReleasedActual.agree j h0 (by omega) x p good raw s dom m pre clear
  have left := FrameHistory.result j h0 (by omega) x p good raw s m g0 s0 dom input h.record kept rel
  have pk : pullState (EnterJ7.pull k) (endRaw (start j) raw s) = origin (start j) raw s := by
    simp only [EnterJ7.pull]
    rw [hs, show start j + 15 - 1 = start j + 14 by omega]
    exact eo
  rw [pk]
  refine AssembleCut.result j k h0 (by omega) (by omega) (by omega) hs (run (Shadow7.leaveP j) m s) (origin (start j) raw s) _ _ _
    (whole.1.trans phase) ?_ ?_ ?_ ?_ ?_ ?_ ?_ left (BoundaryClean.zeros j) clear ?_ ?_ ?_
  · -- sign
    have e : EnterJ7.flagN k = Shadow7.e0P (start j + 15) + 5 := by
      show Shadow7.sbP (start k) + 1579 = 1574 + Shadow7.sbP (start j + 15) + 5; rw [hs]; omega
    rw [e, ← endpointState]; exact bits.2.2.1
  · -- mode
    have e : EnterJ7.flagF k = Shadow7.e0P (start j + 15) + 3 := by
      show Shadow7.sbP (start k) + 1577 = 1574 + Shadow7.sbP (start j + 15) + 3; rw [hs]; omega
    rw [e, ← endpointState, hs]; exact bits.1
  · -- orientation
    have e : EnterJ7.flagU k = Shadow7.e0P (start j + 15) + 4 := by
      show Shadow7.sbP (start k) + 1578 = 1574 + Shadow7.sbP (start j + 15) + 4; rw [hs]; omega
    rw [e, ← endpointState, hs]; exact bits.2.1.trans (both _ _)
  · -- low rails
    intro i
    have hi := i.isLt
    have e1 : start k + 16 + i.val = start j + 31 + i.val := by omega
    have esb : Shadow7.sbP (start k) = Shadow7.sbP (start j + 15) := by rw [hs]
    rw [e1]
    exact rails.1 ⟨i.val, by unfold Shadow7.lowsP; omega⟩
  · -- high rails
    intro i
    have hi := i.isLt
    have esb : Shadow7.sbP (start k) = Shadow7.sbP (start j + 15) := by rw [hs]
    have ewp : Shadow7.wpP (start k) = Shadow7.wpP (start j + 15) := by rw [hs]
    have r := rails.2 ⟨i.val, by unfold Shadow7.lowsP; omega⟩
    have e1 : start k + Shadow7.sbP (start k) + 33 + i.val = Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1 + i.val := by
      unfold Shadow7.a0P Shadow7.lowsP; omega
    have e2 : Shadow7.sbP (start k) + 803 + i.val = Shadow7.b0P (start j) + Shadow7.lowsP (start j) - 1 + i.val := by
      unfold Shadow7.b0P Shadow7.lowsP; omega
    have e3 : EnterJ7.gate k = start j + 30 := by simp only [EnterJ7.gate]; rw [hs]
    rw [e1, e2, e3]
    exact r
  · -- exterior
    intro q nb nl nm
    rw [leave_keeps j h0 (by omega) q (fun hb => nb (AssembleCut.box_of_box2 j h0 (by omega) q hb)) m s]
    exact ext q nb nl nm
  · -- the older moved history
    intro q lo hi
    rw [leave_keeps j h0 (by omega) q (by unfold Shadow7.leaveBox2; omega) m s]
    exact mirror q lo hi
  · -- zcover
    intro q lo hi inBox lf pend nN nF nU
    unfold WideReference.Box at inBox
    rw [AssembleCut.route_rail (start j) (by omega), AssembleCut.route_rail (start j+14) (by omega)] at inBox
    unfold AssembleCut.leftovers ReleasedOrigin.releasedSite at lf
    simp only [EnterJ7.pending, EnterJ7.flagN, EnterJ7.flagF, EnterJ7.flagU, List.mem_cons, List.not_mem_nil,
      or_false] at pend nN nF nU
    rw [hs] at pend nN nF nU
    simp only [BoundaryClean.zeros, List.mem_append, List.mem_range'_1]
    simp only [Wire] at *
    omega
  · -- rails
    intro q inBox lf lo
    unfold WideReference.Box at inBox
    rw [AssembleCut.route_rail (start j) (by omega), AssembleCut.route_rail (start j+14) (by omega)] at inBox
    unfold AssembleCut.leftovers ReleasedOrigin.releasedSite at lf
    rw [hs]
    unfold Shadow7.wpP
    simp only [Wire] at *
    omega
  · -- carry
    intro q lo hs' hi
    exact carry_origin (i := start j) (upper := min 1812 (2054 - start j)) (by omega) (by omega) good raw s dom
      (fun q' l u => sig_carry j h0 (by omega) q' l (by omega)) q lo (by omega)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.CertifiedCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.BodyCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-- dadon's `At240`/`At255` for any block `k` (the saved keys are `window_strong`'s `Key`). -/
structure AtJ (k : Fin 26) (d:Bool) (x p:Nat) (raw s:State) (g sg pg ps:Bool) : Prop where
  domain : Domain (start k) x p raw
  input : InputAt (start k) (signedAt (start k) x p g sg) raw
  cut : PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k) (flagNeg (start k) x p sg)
      (decide (farAt (Shadow7.sbP (start k)) (start k) x p))
      (decide (farAt (Shadow7.sbP (start k)) (start k) x p ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) raw) (eraseSites (EnterJ7.pending k) s)
  facts : PastFacts (NativeJ7.prev k) (ArchiveJ7.rawPorts (NativeJ7.prev k)) (Shadow7.sbP (start (NativeJ7.prev k)))
      (unsigned (start (NativeJ7.prev k)) x p) pg ps
      (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d (NativeJ7.prev k) (unsigned (start (NativeJ7.prev k)) x p))) s
  pastCanonical : signedAt (start (NativeJ7.prev k)) x p pg ps=WideReference.canonical (start (NativeJ7.prev k)) x p

/-- The hand-off at tick `t` (a block start). -/
def ReadyW (d:Bool) (x p:Nat) (t:Nat) (s:State) : Prop :=
  ∃ k : Fin 26, start k=t ∧ ∃ raw g sg pg ps, AtJ k d x p raw s g sg pg ps

/-- Block `i`'s saved archive key (dadon's `Saved (start i) x p (codePorts) d`). -/
def KeyW (d:Bool) (x p:Nat) (i:Fin 26) (s:State) : Prop :=
  ∃row<63145, Chronology (start i) x p row ∧ Kept (ArchiveJ7.codePorts i) d row s

/-- The window's precondition: the stock walk at tick 120 (dadon's `Before` at 225). -/
def BeforeW (d:Bool) (x p:Nat) (s:State) := ∃raw:State,
  Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis ∧ s=pullState (OB5.sig (start WindowParams.first-1)) raw

/-- par-c2's archive-scratch hypothesis of `NativeJ7.from_domain(_matched)`. -/
def ScratchAt (j : Fin 26) (d:Bool) (m:List Bool) (s:State) : Prop :=
  ∀k:Fin 157,23≤k.val →
    let pre:=run (Shadow7.enterP j) m s
    let tape:=m.drop (measurementCount (Shadow7.enterP j))
    (run (NativeJ7.program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1)))
      (run (Shadow7.routed j 0 1) tape pre)).basis
      (ArchiveJ7.rawPorts (NativeJ7.prev j) k)=false

-- ===== Leaves (statements fixed here; each becomes a theorem) =====

/-- L2: the archive scratch of block `j` is clean after its pack (par-d2's ScratchWrap). -/
abbrev ScratchSpec : Prop :=
  ∀ (j : Fin 26), 1≤j.val → j.val≤24 → ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool)
    (m:List Bool), AtJ j d x p raw s g sg pg ps → ScratchAt j d m s

/-- L3: the (move) leave undoes (GlueB's `Admission.Inputs.roundtrip`, on the window's move leave). -/
abbrev RoundtripSpec : Prop :=
  ∀ (j : Fin 26), 0≤j.val → j.val≤24 → ∀ (v:State) (z:SkywalkNat.State) (G S:Bool),
    LeaveJ7.Admission.Inputs j v z G S → ∀ m n:List Bool, run (CRTBarrel.unleave j) n (run (CRTBarrel.leave j) m v)=v

/-- The block after the window's first block. -/
def firstNext : Fin 26 := ⟨WindowParams.first.val+1,by decide⟩

/-- L9: the first block's endpoint at `start WindowParams.first` (dadon's `NativePack225.stock_endpoint`, first form). -/
abbrev FirstSpec : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m n:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis),
    ∃g s:Bool,
      InputAt (start WindowParams.first) (encode g s (unsigned (start WindowParams.first) x p).u (unsigned (start WindowParams.first) x p).v) raw ∧
      LeaveJ7.Admission.Inputs WindowParams.first
        (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))
        (unsigned (start WindowParams.first) x p) g s ∧
      PackedCut (EnterJ7.lowerPairs firstNext) (EnterJ7.upperPairs firstNext) (EnterJ7.gate firstNext)
        (EnterJ7.flagN firstNext) (EnterJ7.flagF firstNext) (EnterJ7.flagU firstNext)
        (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start WindowParams.first) x p) g s).2 (unsigned (start WindowParams.first+15) x p).u)
        (decide (Shadow.far (Shadow7.sbP (start WindowParams.first+15)) 15 (unsigned (start WindowParams.first+15) x p)))
        (decide (Shadow.far (Shadow7.sbP (start WindowParams.first+15)) 15 (unsigned (start WindowParams.first+15) x p) ∧ 2^(Shadow7.sbP (start WindowParams.first+15))≤(unsigned (start WindowParams.first+15) x p).u))
        (pullState (EnterJ7.pull firstNext)
          (endRaw (start WindowParams.first) raw (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))))
        (eraseSites (EnterJ7.pending firstNext) (run (Shadow7.leaveP WindowParams.first) n
          (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)))) ∧
      PastFacts WindowParams.first (ArchiveJ7.rawPorts WindowParams.first) (Shadow7.sbP (start WindowParams.first)) (unsigned (start WindowParams.first) x p) g s
        (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d WindowParams.first (unsigned (start WindowParams.first) x p)))
        (run (Shadow7.leaveP WindowParams.first) n
          (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)))

/-- L10: the first window (portal 120, enter, pack) keeps the phase and undoes (dadon's `NativePack225.first_window`). -/
abbrev FirstBackSpec : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis),
    (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)).phase=raw.phase ∧
    ∀k, run (NativeFirstJ7.enteredUnwind WindowParams.first d ++ Shadow7.portalInvP (start WindowParams.first)) k
      (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))=
      pullState (OB5.sig (start WindowParams.first-1)) raw

-- ===== Program bridges =====

theorem prev_of (i k : Fin 26) (hk : k.val=i.val+1) : NativeJ7.prev k=i := Fin.ext (by simp only [NativeJ7.prev]; omega)

theorem start_succ (i k : Fin 26) (hk : k.val=i.val+1) : start k=start i+15 := by simp only [StairPacket.start]; omega

theorem next_eq (d:Bool) (i k : Fin 26) (hk : k.val=i.val+1) :
    (nextF CRTBarrel.params d i k).flatten=NativeJ7.nextWindow k d++CRTBarrel.leave k := by
  have e:=prev_of i k hk
  subst e
  simp only [nextF,CRTBarrel.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeJ7.nextWindow,NativeJ7.window,Shadow7.body,NativeJ7.withArchive,NativeJ7.program,List.append_assoc]

theorem nextR_eq (d:Bool) (i k : Fin 26) (hk : k.val=i.val+1) :
    (nextR CRTBarrel.params d i k).flatten=CRTBarrel.unleave k++NativeJ7.nextUnwind k d := by
  have e:=prev_of i k hk
  subst e
  simp only [nextR,CRTBarrel.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeJ7.nextUnwind,NativeJ7.unwind,Shadow7.unbody,NativeJ7.fromArchive,NativeJ7.reverse,List.append_assoc]

theorem first_eq (d:Bool) :
    (CRTBarrel.params.portal (start WindowParams.first) :: firstF CRTBarrel.params d WindowParams.first).flatten=
      (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d)++CRTBarrel.leave WindowParams.first := by
  simp only [firstF,CRTBarrel.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeFirstJ7.enteredWindow,NativeFirstJ7.window,Shadow7.body,NativeFirstJ7.program,List.append_assoc]

theorem firstR_eq (d:Bool) :
    (firstR CRTBarrel.params d WindowParams.first++[CRTBarrel.params.portalInv (start WindowParams.first)]).flatten=
      CRTBarrel.unleave WindowParams.first++(NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) := by
  simp only [firstR,CRTBarrel.params,Shadow7.params,ofParts,List.cons_append,List.nil_append,List.flatten_cons,List.flatten_nil,
    List.append_nil,NativeFirstJ7.enteredUnwind,NativeFirstJ7.unwind,Shadow7.unbody,NativeFirstJ7.reverse,List.append_assoc]


/-- The move leave runs like the reference leave after block `k`'s head, from any hand-off state. -/
theorem sameAt (L2 : ScratchSpec) (k : Fin 26) (h2 : 1≤k.val) (h19 : k.val≤24) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (g sg pg ps:Bool) (m:List Bool) (pre:AtJ k d x p raw s g sg pg ps) (n:List Bool) :
    run (CRTBarrel.leave k) n (run (NativeJ7.nextWindow k d) m s)=run (Shadow7.leaveP k) n (run (NativeJ7.nextWindow k d) m s) := by
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=L2 k (by omega) (by omega) d x p good raw s g sg pg ps m pre
  have native:=NativeJ7.from_domain_matched k (by omega) (by omega) d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  exact (LeaveJ7.Admission.Inputs.crt_pair (by omega) (by omega) native.1).1 n

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

/-- The saved key cells of block `i` are its archive's first 16 code ports. -/
theorem bank_cells (i : Fin 26) (q : Wire) (h : q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i)) :
    q ∈ cellsRestoreP (start i + 15) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
  have hl : (cellsRestoreP (start i + 15)).length = 16 := by simp [cellsRestoreP]
  have hj : j.val < (cellsRestoreP (start i + 15)).length := by rw [hl]; exact j.isLt
  simp only [ArchiveJ7.codePorts, ArchiveJ7.code_split, List.append_assoc]
  rw [List.getD_append _ _ _ _ hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem _

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem scratch : ScratchSpec := by
  intro j h2 h19 d x p good raw s g sg pg ps m pre
  have numbers := LeaveJ7.Admission.actualNumbers j (by omega) (by omega) x p good
  have hist := WideReference.pulled_history j rfl pre.domain
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)
  let Z:=encode g sg T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) (unsigned (start j) x p) numbers.farSmall numbers.odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum g sg _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s (unsigned (start j) x p) g sg m numbers.farSmall pre.cut
    (readInput (start j) x p raw g sg pre.input) hist
  exact NativeJ7.scratch_raw_clean j h2 (by omega) d raw s m x p good pre.domain _ _ _ Z parity ready.2.1 pre.cut

theorem roundtrip : RoundtripSpec := by
  intro j h2 h19 v z G S h m n
  exact (LeaveJ7.Admission.Inputs.crt_pair (by omega) (by omega) h).2 m n

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

abbrev j0 : Fin 26 := ⟨0, by decide⟩

theorem start0 : start j0 = 45 := rfl

/-- The first block's admin (its pack at 45) touches only its five ticks' cells. -/
theorem admin_cover1 (d:Bool) : wires (program j0 d) ⊆ (support j0).toFinset := by
  intro q hq
  rw [program, renameProgram_support] at hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨r, r1, r2, e | e⟩ := (WindowCovered.pack_cells d 45 (by decide) (by decide)).1 w hw <;>
    subst e <;> simp only [support, List.mem_toFinset, List.mem_flatMap, List.mem_range'_1, List.mem_cons,
      List.not_mem_nil, or_false, start0]
  · exact ⟨r, ⟨by omega, by omega⟩, Or.inl rfl⟩
  · exact ⟨r, ⟨by omega, by omega⟩, Or.inr rfl⟩

theorem support_sites : ∀ q ∈ support j0, q ∈ WideReference.sites 45 := by decide

/-- `NativeJ7.agree_origin` for the first block (first form: no archive, the pack at 45 itself). -/
theorem agree_origin1 (d:Bool) (raw s:State) (m t:List Bool) (neg far long:Bool)
    (packed:PackedCut (EnterJ7.lowerPairs j0) (EnterJ7.upperPairs j0) (EnterJ7.gate j0) (EnterJ7.flagN j0)
      (EnterJ7.flagF j0) (EnterJ7.flagU j0) neg far long (pullState (EnterJ7.pull j0) raw) s)
    (q:Wire) (ext:¬WideReference.Box 45 q) :
    (run (Shadow7.body j0 (program j0 d)) t (run (Shadow7.enterP j0) m s)).basis q =
      (WideReference.origin 45 raw (run (Shadow7.body j0 (program j0 d)) t (run (Shadow7.enterP j0) m s))).basis q := by
  have w59 : W.narrowSkywalkRouteWidth (45+14) = 258 :=
    (LeaveJ7.AssembleCut.route_rail (45+14) (by omega)).trans (by decide)
  have w45 : W.narrowSkywalkRouteWidth 45 = 258 := (LeaveJ7.AssembleCut.route_rail 45 (by omega)).trans (by decide)
  unfold WideReference.Box at ext
  rw [w59, w45] at ext
  have wn : windowNet j0 q = q := by
    show OB5.sig 59 q = q
    exact WideReference.sig_fixed (by intro h'; simp only [Wire] at *; omega) (by intro h'; simp only [Wire] at *; omega)
  have pullId : OB5.sig 44 q = q := by
    exact WideReference.sig_fixed (by intro h'; simp only [Wire] at *; omega) (by intro h'; simp only [Wire] at *; omega)
  have notMay : ¬Shadow7.MayTouch j0 q := by
    intro mt
    apply ext
    unfold Shadow7.MayTouch at mt
    have mid : (Shadow7.shape j0).mid = Shadow7.sbP (start j0)+15 := rfl
    rw [mid, start0] at mt
    have sb : Shadow7.sbP 45 = 226 := by decide
    rw [sb] at mt
    simp only [Wire] at *
    omega
  have free : ¬Shadow7.MayTouch j0 (windowNet j0 q) := by rwa [wn]
  have port : q∉EnterJ7.ports j0 := by
    intro mem
    apply ext
    have r := EnterJ7.portsRegion j0 mem
    rw [start0] at r
    have sb : Shadow7.sbP 45 = 226 := by decide
    rw [sb] at r
    simp only [Wire] at *
    omega
  have origin_eq : WideReference.origin 45 raw = WideReference.origin (StairPacket.start j0) raw := rfl
  rw [origin_eq]
  have ext' : ¬WideReference.Box (StairPacket.start j0) q := by
    unfold WideReference.Box; rw [start0, w59, w45]; exact ext
  apply WideReference.box_origin_j j0 ext' raw _
  intro notSite
  have notAdmin : q∉support j0 := fun mem => notSite (support_sites q mem)
  have stay := Shadow7.ext_head (Shadow7.enterP j0) j0 (program j0 d) (support j0) s m t q free (EnterJ7.notWire j0 port)
    notAdmin (admin_cover1 d)
  have sb : Shadow7.sbP 45 = 226 := by decide
  have hn : q≠EnterJ7.flagN j0 := by
    intro eq; apply ext; rw [eq]; unfold EnterJ7.flagN; rw [start0, sb]
    simp only [Wire] at *; omega
  have hf : q≠EnterJ7.flagF j0 := by
    intro eq; apply ext; rw [eq]; unfold EnterJ7.flagF; rw [start0, sb]
    simp only [Wire] at *; omega
  have hu : q≠EnterJ7.flagU j0 := by
    intro eq; apply ext; rw [eq]; unfold EnterJ7.flagU; rw [start0, sb]
    simp only [Wire] at *; omega
  have hi : q∉RailPair.sites (EnterJ7.upperPairs j0) := by
    intro mm; apply ext
    have u := EnterJ7.upperSites j0 mm
    rw [start0, sb] at u
    have wp : Shadow7.wpP 45 = 17 := by decide
    rw [wp] at u
    simp only [Wire] at *
    omega
  have old := packed.unchanged q hn hf hu hi
  rw [stay]
  simpa only [EnterJ7.pull, pullId] using old

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl

/-- Everything the first block at 45 (block 0) gives, from the stock stage at 45. -/
theorem first_core (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) :
    ∃ G S:Bool,
      InputAt 45 (encode G S (unsigned 45 x p).u (unsigned 45 x p).v) raw ∧
      PackedCut (EnterJ7.lowerPairs j0) (EnterJ7.upperPairs j0) (EnterJ7.gate j0) (EnterJ7.flagN j0) (EnterJ7.flagF j0)
        (EnterJ7.flagU j0) (PortalValues.negative S (unsigned 45 x p).u)
        (decide (Shadow.far (Shadow7.sbP (start j0)) 15 (unsigned 45 x p)))
        (decide (Shadow.far (Shadow7.sbP (start j0)) 15 (unsigned 45 x p) ∧ 2^(Shadow7.sbP (start j0))≤(unsigned 45 x p).u))
        (pullState (EnterJ7.pull j0) raw) (run (Shadow7.portalP 45) m (pullState (OB5.sig 44) raw)) ∧
      (∀ q ∈ Portal45Flag7.activeScratch, (pullState (OB5.sig 44) raw).basis q = false) := by
  have small : Shadow7.SmallIfFar 226 15 (unsigned 45 x p) :=
    (Shadow7.Envelope.inputs x p 45 (lt_trans good.small good.cap) good.cap (by decide)).1
  obtain ⟨G,S,input⟩ := PortalValues.real_input d x p 45 good.positive good.nonzero good.odd good.cap good.gap
    good.small good.coprime (by decide) raw stage
  have pcut := Portal45Flag7.physical_frame_for d x p good.positive good.nonzero good.odd good.cap good.gap good.small
    good.coprime raw m stage G S input
  have same : Shadow.far 226 15 (unsigned 45 x p) = (2*2^241≤(unsigned 45 x p).u+(unsigned 45 x p).v) := by
    apply propext; unfold Shadow.far Shadow.high Shadow.limb; exact Nat.le_div_iff_mul_le (by positivity)
  have lo : Portal45Flag7.loPairs = EnterJ7.lowerPairs j0 := by decide
  have hi : Portal45Flag7.hiPairs = EnterJ7.upperPairs j0 := by decide
  have sb : Shadow7.sbP (start j0) = 226 := by decide
  refine ⟨G, S, ?_, ?_, Portal45Flag7.clean_for raw _ G S input⟩
  · unfold InputAt; rw [flagEq]; exact input
  · rw [sb, ← lo, ← hi]
    simpa only [same] using pcut

/-- L9: the first block's endpoint at 45. -/
theorem first : StockWindowW7.FirstSpec := by
  intro d x p good raw m n stage
  obtain ⟨G, S, input, cut0, clean⟩ := first_core d x p good raw m stage
  let origin := pullState (OB5.sig 44) raw
  let cut := run (Shadow7.portalP 45) m origin
  let n0 := m.drop (measurementCount (Shadow7.portalP 45))
  let tape := n0.drop (measurementCount (Shadow7.enterP j0))
  have dom := initial 45 x p (by decide) d raw stage
  have numbers := LeaveJ7.Admission.actualNumbers j0 (by decide) (by decide) x p good
  have hist := WideReference.pulled_history j0 rfl dom
  have legal0 := original_legal j0 (by decide) (by decide) d x p good.positive good.odd raw stage
  have inputL : SkywalkIntegerInput (EnterJ7.lay j0) (encode G S (unsigned 45 x p).u (unsigned 45 x p).v).a
      (encode G S (unsigned 45 x p).u (unsigned 45 x p).v).b G raw.basis := by
    have i2 := input; unfold InputAt at i2; rw [flagEq] at i2; exact i2
  have win := entered_window j0 (by decide) (by decide) d raw cut n0 (unsigned 45 x p) G S numbers.odd numbers.farSmall
    cut0 inputL hist legal0
  have values := saved_at_leave j0 (by decide) (by decide) d raw cut (unsigned 45 x p) G S n0 tape numbers.farSmall cut0
    inputL
  have tail := tailF_clean j0 (by decide) (by decide) d x p raw cut dom n0 tape _ _ _ cut0
  have vEq : run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin = run (Shadow7.body j0 (program j0 d)) tape (run (Shadow7.enterP j0) n0 cut) := by
    simp only [enteredWindow, window, run_append, run_take, cut, n0, tape, origin]
  have vEq' : run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin = run (enteredWindow j0 d) n0 cut := by
    simp only [run_append, run_take, cut, n0, origin]
  have hin : LeaveJ7.Admission.Inputs j0 (run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin) (unsigned 45 x p) G S := by
    apply LeaveJ7.Admission.assemble j0 (by decide) (by decide) _ (unsigned 45 x p) G S numbers
    · rw [vEq']; exact win.2.1
    · rw [vEq']; exact win.2.2.1
    · rw [vEq, ← NativeJ7.saved_ys j0 (by decide) (by decide)]
      refine ⟨values.1, ?_, ?_, ?_⟩
      · have e : Shadow7.e0P (start j0) + 5 = EnterJ7.flagN j0 := by simp only [EnterJ7.flagN, Shadow7.e0P]; omega
        rw [e]; exact values.2.1
      · have e : Shadow7.e0P (start j0) + 3 = EnterJ7.flagF j0 := by simp only [EnterJ7.flagF, Shadow7.e0P]; omega
        rw [e]; exact values.2.2.1
      · have e : Shadow7.e0P (start j0) + 4 = EnterJ7.flagU j0 := by simp only [EnterJ7.flagU, Shadow7.e0P]; omega
        rw [e]; exact values.2.2.2
    · intro q hq
      rw [vEq]
      apply tail q
      have ew : Shadow7.e0P (start j0) = 1800 := by decide
      have ewp : Shadow7.wpP (start j0) = 17 := by decide
      have s3 : start j0 = 45 := rfl
      have en1 : min (Shadow7.wpP (start j0) - 1 - (Shadow7.e0P (start j0) - 1598)) (2045 - start j0 - Shadow7.e0P (start j0)) = 0 := by decide
      have hl : ∀ r : Nat, r ∈ LeaveJ7.Admission.spare j0 → r ∈ tailTempsF j0 := by
        intro r hr
        rw [LeaveJ7.Admission.mem_spare] at hr
        rcases hr with rfl | rfl | ⟨lo, hi⟩ <;> simp only [tailTempsF, List.mem_range'_1] <;>
          simp only [Wire] at * <;> omega
      exact hl q hq
    · intro q lo hi
      have en2 : min 4 (Shadow7.wpP (start j0) + start j0 - 448) = 0 := by decide
      omega
    · rw [vEq]; exact topF_clean j0 (by decide) (by decide) d x p raw cut dom n0 tape _ _ _ cut0 _ (by simp only [Shadow7.e0P]; (try simp only [Wire] at *); omega)
    · rw [vEq]; exact topF_clean j0 (by decide) (by decide) d x p raw cut dom n0 tape _ _ _ cut0 _ (by simp only [Shadow7.e0P]; (try simp only [Wire] at *); omega)
    · rw [vEq]
      have e : Shadow7.b0P (start j0) + 16 = EnterJ7.parked j0 := by simp only [EnterJ7.parked, Shadow7.b0P]; omega
      rw [e]; exact parkedF_clean j0 (by decide) (by decide) d raw cut (unsigned 45 x p) G S n0 tape numbers.farSmall cut0 inputL
  -- the next block's cut
  have ph : (run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin).phase =
      (WideReference.origin 45 raw (run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin)).phase := by
    rw [vEq', win.1, origin_phase 45 x p (by decide) good raw _ dom]
    exact cut0.phase
  have ext : ∀ q:Wire, ¬WideReference.Box (start j0) q → ¬LeaveJ7.AssembleCut.leftovers j0 q →
      ¬(2070≤(q:Nat)+start j0 ∧ (q:Nat)≤1812) → (run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin).basis q =
        (WideReference.origin (start j0) raw (run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin)).basis q := by
    intro q nb _ _
    rw [vEq]
    exact agree_origin1 d raw cut n0 tape _ _ _ cut0 q nb
  have upper : ∀ q:Nat, Shadow7.a0P (start j0)+16 ≤ q → q ≤ min (start j0+30+railP (start j0+14)) 529 →
      (run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin).basis q = false := by
    intro q lo hi
    rw [vEq]
    exact upperF_clear j0 (by decide) (by decide) d raw cut x p dom n0 tape _ _ _ cut0 q (by unfold Shadow7.a0P at lo; omega) hi
  have quiet : ∀ q ∈ LeaveJ7.CoreCheckpoint.rawSites j0, (run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin).basis q = false := by
    intro q hq
    simp only [LeaveJ7.CoreCheckpoint.rawSites, List.mem_append, List.mem_range'_1, List.mem_singleton] at hq
    rcases hq with (⟨lo, hi⟩ | ⟨lo, hi⟩) | p17
    rotate_right
    · rw [p17]; exact hin.parked
    · exact LeaveJ7.native_carryJ j0 (by decide) (by decide) _ _ hin.ready hin.top hin.top2 q (by simp only [Wire] at *; omega)
        (by simp only [Wire] at *; omega)
    · rw [vEq]
      exact tail q (by simp only [tailTempsF, List.mem_range'_1]; simp only [Wire] at *; omega)
  have cutK := LeaveJ7.CertifiedCut.result j0 ⟨1, by decide⟩ (by decide) (by decide) (by decide) (by decide) rfl x p good raw
    (run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin) n G S hin dom input ph ext
    (fun q lo hi => absurd hi (by simp only [start0] at lo; omega)) upper
    (fun q lo hi => absurd hi (by simp only [start0]; omega))
    (fun q t369 _ _ => absurd t369 (by have e1 := start0; omega)) quiet
  refine ⟨G, S, input, hin, cutK, ?_⟩
  exact LeaveJ7.ArchiveCut.result j0 (by decide) (by decide) _ n (unsigned 45 x p) G S hin

/-- L10: the first window keeps the phase and undoes. -/
theorem firstBack : StockWindowW7.FirstBackSpec := by
  intro d x p good raw m stage
  have hf : WindowParams.first = j0 := rfl
  rw [hf]
  simp only [start0]
  obtain ⟨G, S, input, cut0, clean⟩ := first_core d x p good raw m stage
  let origin := pullState (OB5.sig 44) raw
  let cut := run (Shadow7.portalP 45) m origin
  let n0 := m.drop (measurementCount (Shadow7.portalP 45))
  have dom := initial 45 x p (by decide) d raw stage
  have numbers := LeaveJ7.Admission.actualNumbers j0 (by decide) (by decide) x p good
  have hist := WideReference.pulled_history j0 rfl dom
  have legal0 := original_legal j0 (by decide) (by decide) d x p good.positive good.odd raw stage
  have inputL : SkywalkIntegerInput (EnterJ7.lay j0) (encode G S (unsigned 45 x p).u (unsigned 45 x p).v).a
      (encode G S (unsigned 45 x p).u (unsigned 45 x p).v).b G raw.basis := by
    have i2 := input; unfold InputAt at i2; rw [flagEq] at i2; exact i2
  have win := entered_window j0 (by decide) (by decide) d raw cut n0 (unsigned 45 x p) G S numbers.odd numbers.farSmall
    cut0 inputL hist legal0
  have vEq' : run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin = run (enteredWindow j0 d) n0 cut := by
    simp only [run_append, run_take, cut, n0, origin]
  refine ⟨?_, ?_⟩
  · rw [vEq', win.1]; exact cut0.phase
  · intro k
    rw [vEq', run_append, win.2.2.2]
    exact Portal45Flag7.portal_return origin m _ clean (Portal45Flag7.erase_ready _
      (show Shadow7.SmallIfFar 226 15 (unsigned 45 x p) from
        (Shadow7.Envelope.inputs x p 45 (lt_trans good.small good.cap) good.cap (by decide)).1) raw m G S
      (by have i2 := input; unfold InputAt at i2; rw [flagEq] at i2; exact i2))

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

abbrev EndpointUpTo (J : Nat) : Prop :=
  ∀ (j k : Fin 26), k.val=j.val+1 → WindowParams.first.val+1≤j.val → j.val≤J → ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State)
    (m n:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:ScratchAt j d m s) (pg ps cross:Bool)
    (prior:PastFacts (NativeJ7.prev j) (ArchiveJ7.rawPorts (NativeJ7.prev j)) (Shadow7.sbP (start (NativeJ7.prev j)))
      (unsigned (start (NativeJ7.prev j)) x p) pg ps cross s),
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k)
      (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start j) x p) G S).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) (endRaw (start j) raw (run (NativeJ7.nextWindow j d) m s)))
      (eraseSites (EnterJ7.pending k) (run (Shadow7.leaveP j) n (run (NativeJ7.nextWindow j d) m s))) ∧
    PastFacts j (ArchiveJ7.rawPorts j) (Shadow7.sbP (start j)) (unsigned (start j) x p) G S
      (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d j (unsigned (start j) x p)))
      (run (Shadow7.leaveP j) n (run (NativeJ7.nextWindow j d) m s))

abbrev KeepLeaveUpTo (J : Nat) : Prop :=
  ∀ (k : Fin 26), 1≤k.val → k.val≤J → ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts (NativeJ7.prev k)),
    ∀ (v:State) (n:List Bool), (run (CRTBarrel.leave k) n v).basis q=v.basis q

abbrev KeepOlderUpTo (J : Nat) : Prop :=
  ∀ (i k i' : Fin 26), k.val=i.val+1 → 0≤ i'.val → i'.val+2≤k.val → k.val≤J → ∀ (d:Bool),
    ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i'), ∀ (s:State) (m:List Bool),
    (run (nextF CRTBarrel.params d i k).flatten m s).basis q=s.basis q

/-- The leaves of a window whose last block is `J`. -/
structure LeavesUpTo (J : Nat) : Prop where
  endpoint : EndpointUpTo J
  scratch : ScratchSpec
  roundtrip : RoundtripSpec
  keepLeave : KeepLeaveUpTo J
  keepOlder : KeepOlderUpTo J
  first : FirstSpec
  firstBack : FirstBackSpec

/-- The last block's frame at the exit (exit ports `ports`). -/
def LastAt (ports : Ports) (J : Fin 26) (d:Bool) (x p:Nat) (s:State) : Prop :=
  ∃row<63145,Chronology (start J) x p row ∧ Frame ports (code d) row s

/-- The exit of a window whose last block is `J`: its step (from the hand-off at `start J+15` to the last frame) and
the keys it keeps. -/
structure ExitLeaves (J : Fin 26) (ports : Ports) : Prop where
  step : ∀ (d:Bool) (x:Nat), Bounds x p → Checked (exitF CRTBarrel.params d (start J+15)).flatten
    (exitR CRTBarrel.params d (start J+15)).flatten (ReadyW d x p (start J+15)) (LastAt ports J d x p)
  keep : ∀ (i : Fin 26), WindowParams.first.val ≤ i.val → i.val < J.val → ∀ (d:Bool), ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i),
    ∀ (s:State) (m:List Bool), (run (exitF CRTBarrel.params d (start J+15)).flatten m s).basis q=s.basis q

theorem interiorG (J : Nat) (hJ : J ≤ 24) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) (i k : Fin 26) (hk : k.val=i.val+1)
    (h4 : WindowParams.first.val+1≤k.val) (h12 : k.val≤J) :
    Checked (nextF CRTBarrel.params d i k).flatten (nextR CRTBarrel.params d i k).flatten
      (ReadyW d x p (start k)) (ReadyW d x p (start k+15)) := by
  rw [next_eq d i k hk,nextR_eq d i k hk]
  apply pair (F:=NativeJ7.nextWindow k d) (F':=CRTBarrel.leave k) (R:=NativeJ7.nextUnwind k d) (R':=CRTBarrel.unleave k)
  intro s m h
  obtain ⟨k1',e0,raw,g,sg,pg,ps,pre⟩:=h
  have same0:k1'=k:=Fin.ext (by have := e0; simp only [StairPacket.start] at this; omega)
  rw [same0] at pre
  let k0:=k
  let v:=run (NativeJ7.nextWindow k0 d) m s
  let n:=m.drop (measurementCount (NativeJ7.nextWindow k0 d))
  let out:=run (Shadow7.leaveP k0) n v
  let raw':=endRaw (start k0) raw v
  let k1:Fin 26:=⟨k0.val+1,by omega⟩
  have p1:NativeJ7.prev k1=k0:=prev_of k0 k1 rfl
  have s1:start k1=start k0+15:=start_succ k0 k1 rfl
  let flags:=LeaveJ7.Admission.flags (unsigned (start k0) x p) g sg
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have h2 : 1≤k0.val := by omega
  have h19 : k0.val≤24 := by omega
  have curr:=readInput (start k0) x p raw g sg pre.input
  have scr:=L.scratch k0 h2 h19 d x p good raw s g sg pg ps m pre
  have native:=NativeJ7.from_domain_matched k0 h2 h19 d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  obtain ⟨cut,facts⟩:=L.endpoint k0 k1 rfl h4 h12 d x p good raw s m n pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  have hin:=native.1
  have carried:=stepInput_gen_shadow7 (start k0) (Shadow7.sbP (start k0)) x p (by simp only [StairPacket.start]; omega)
    (by simp only [StairPacket.start]; omega) good raw v g sg pre.domain pre.input hin.farSmall
  have lastPhase:out.phase=raw'.phase:=cutPhase cut
  have prevPhase:s.phase=raw.phase:=cutPhase pre.cut
  have ph:=lastPhase.trans ((endRaw_phase (start k0) x p (by simp only [StairPacket.start]; omega) good raw v
    pre.domain).trans prevPhase.symm)
  have canon:=unique_input pre.input (fixed_input _ _ _ (by simp only [StairPacket.start]; omega) good raw pre.domain)
  have same:run (CRTBarrel.leave k0) n v=run (Shadow7.leaveP k0) n v:=(LeaveJ7.Admission.Inputs.crt_pair (by omega) (by omega) hin).1 n
  show (run (CRTBarrel.leave k0) n v).phase=s.phase ∧ ReadyW d x p (start k+15) (run (CRTBarrel.leave k0) n v) ∧
    (∀t,run (CRTBarrel.unleave k0) t (run (CRTBarrel.leave k0) n v)=v) ∧ (∀t,run (NativeJ7.nextUnwind k d) t v=s)
  rw [same]
  refine ⟨ph,⟨k1,s1,raw',flags.1,flags.2,g,sg,?_⟩,fun t=>by rw [← same]; exact L.roundtrip k0 (by omega) h19 v _ g sg hin n t,
    native.2.2.2⟩
  refine ⟨?_,?_,cut,?_,?_⟩
  · rw [s1]; exact carried.1
  · rw [s1]; exact carried.2
  · rw [p1]; exact facts
  · rw [p1]; exact canon

theorem firstStepG (J : Nat) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) :
    Checked (CRTBarrel.params.portal (start WindowParams.first) :: firstF CRTBarrel.params d WindowParams.first).flatten
      (firstR CRTBarrel.params d WindowParams.first++[CRTBarrel.params.portalInv (start WindowParams.first)]).flatten
      (BeforeW d x p) (ReadyW d x p (start WindowParams.first+15)) := by
  rw [first_eq d,firstR_eq d]
  apply pair (F:=Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d) (F':=CRTBarrel.leave WindowParams.first)
    (R:=NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) (R':=CRTBarrel.unleave WindowParams.first)
  intro s m h
  obtain ⟨raw,stage,rfl⟩:=h
  let v:=run (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)
  let n:=m.drop (measurementCount (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d))
  let out:=run (Shadow7.leaveP WindowParams.first) n v
  let raw':=endRaw (start WindowParams.first) raw v
  obtain ⟨g,sg,input,hin,cut,facts⟩:=L.first d x p good raw m n stage
  let flags:=LeaveJ7.Admission.flags (unsigned (start WindowParams.first) x p) g sg
  have dom:=initial (start WindowParams.first) x p (by decide) d raw stage
  have carried:=stepInput_gen_shadow7 (start WindowParams.first) (Shadow7.sbP (start WindowParams.first)) x p (by decide) (by decide) good raw v g sg dom input hin.farSmall
  have base:out.phase=raw'.phase:=cutPhase cut
  have ph:=base.trans (endRaw_phase (start WindowParams.first) x p (by decide) good raw v dom)
  have back:=L.firstBack d x p good raw m stage
  have same:run (CRTBarrel.leave WindowParams.first) n v=run (Shadow7.leaveP WindowParams.first) n v:=
    (LeaveJ7.Admission.Inputs.crt_pair (by decide) (by decide) hin).1 n
  show (run (CRTBarrel.leave WindowParams.first) n v).phase=(pullState (OB5.sig (start WindowParams.first-1)) raw).phase ∧
    ReadyW d x p (start WindowParams.first+15) (run (CRTBarrel.leave WindowParams.first) n v) ∧
    (∀t,run (CRTBarrel.unleave WindowParams.first) t (run (CRTBarrel.leave WindowParams.first) n v)=v) ∧
    (∀t,run (NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) t v=pullState (OB5.sig (start WindowParams.first-1)) raw)
  rw [same]
  exact ⟨ph,⟨firstNext,rfl,raw',flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts,
    unique_input input (fixed_input (start WindowParams.first) x p (by decide) good raw dom)⟩,
    fun t=>by rw [← same]; exact L.roundtrip WindowParams.first (by decide) (by decide) v _ g sg hin n t,back.2⟩

theorem receiptG (J : Nat) (hJ : J ≤ 24) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) (i k : Fin 26) (hk : k.val=i.val+1)
    (h2 : 1≤k.val) (h12 : k.val≤J) :
    ∀ s m, ReadyW d x p (start k) s → KeyW d x p i (run (nextF CRTBarrel.params d i k).flatten m s) := by
  intro s m h
  obtain ⟨k1',e0,raw,g,sg,pg,ps,pre⟩:=h
  have same0:k1'=k:=Fin.ext (by have := e0; simp only [StairPacket.start] at this; omega)
  rw [same0] at pre
  have pk:=prev_of i k hk
  rw [next_eq d i k hk,←pk]
  simp only [run_append,run_take]
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=L.scratch k h2 (by omega) d x p good raw s g sg pg ps m pre
  have native:=NativeJ7.from_domain_matched k h2 (by omega) d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  obtain ⟨row,bound,truth,kept⟩:=native.2.2.1
  have chr:Chronology (start (NativeJ7.prev k)) x p row:=by unfold Chronology;rw [←pre.pastCanonical];exact truth
  exact ⟨row,bound,chr,ArchiveWindowPreserve.keep kept (fun q hq=>L.keepLeave k h2 h12 q hq _ _)⟩

theorem keepG (J : Nat) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (i k : Fin 26) (hk : k.val=i.val+1) (h12 : k.val≤J) :
    ∀ s m, ReadyW d x p (start k) s → ∀ i' : Fin 26, WindowParams.first.val ≤ i'.val → i'.val< i.val → KeyW d x p i' s →
      KeyW d x p i' (run (nextF CRTBarrel.params d i k).flatten m s) := by
  intro s m _ i' h1 h2 key
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  obtain ⟨r,lim,chr,kept⟩:=key
  exact ⟨r,lim,chr,ArchiveWindowPreserve.keep kept (fun q hq=>L.keepOlder i k i' hk (by omega) (by omega) h12 d q hq s m)⟩

/-- The window's stock chain, generic in its last block `J` and its interior list `rest`. -/
theorem checkedG (J : Fin 26) (h4 : WindowParams.first.val+1 ≤ J.val) (hJ : J.val ≤ 24) (ports : Ports) (rest : List (Fin 26))
    (consec : Consec WindowParams.first rest) (mem : ∀ k ∈ rest, WindowParams.first.val+1 ≤ k.val ∧ k.val ≤ J.val)
    (exitT : exitTick WindowParams.first rest = start J+15)
    (L : LeavesUpTo J.val) (X : ExitLeaves J ports) (d:Bool) (x:Nat) (good:Bounds x p) :
    Checked (forwardW CRTBarrel.params d WindowParams.first rest)
      (reverseW CRTBarrel.params d WindowParams.first rest)
      (BeforeW d x p) (FinalW WindowParams.first J ports d x p) := by
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have bl:blockOf (exitTick WindowParams.first rest)=J.val+1:=by rw [exitT]; exact blockOf_next J
  have h:=window_strong CRTBarrel.params d (ReadyW d x p) (KeyW d x p) (BeforeW d x p) (LastAt ports J d x p)
    WindowParams.first rest consec (firstStepG J.val L d x p good)
    (fun i k hm hk=>interiorG J.val (by omega) L d x p good i k hk (mem k hm).1 (mem k hm).2)
    (fun i k hm hk=>receiptG J.val (by omega) L d x p good i k hk (by have := mem k hm; omega) (by have := mem k hm; omega))
    (fun i k hm hk s m r i' h1 h2=>keepG J.val L d x p i k hk (by have := mem k hm; omega) s m r i' (by omega) h2)
    (by rw [exitT]; exact X.step d x good)
    (by
      intro s m _ i h1 h2 key
      rw [bl] at h2
      revert key
      rw [exitT]
      intro key
      obtain ⟨r,lim,chr,kept⟩:=key
      exact ⟨r,lim,chr,ArchiveWindowPreserve.keep kept (fun q hq=>X.keep i (by omega) (by omega) d q hq s m)⟩)
  refine checked_mono h ?_
  intro s ⟨last,saved⟩
  refine ⟨?_, last⟩
  intro k h1 h2
  obtain ⟨r, lim, chr, kept⟩ := saved k h1 (by rw [bl]; omega)
  exact ⟨r, lim, chr, ArchiveJ7.kept_stock k d r s kept⟩

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

theorem sig_moved (i q : Nat) (h : (1301 ≤ q ∧ q ≤ 1044+i) ∨ (2069 ≤ q+i ∧ q ≤ 1812)) :
    OB5.sig i q = 3113 - q := by
  rw [OB5.sig_nat]; unfold OB5.sigNat; rw [if_pos h]

theorem sig_kept (i q : Nat) (h1 : ¬(1301 ≤ q ∧ q ≤ 1044+i)) (h2 : ¬(2069 ≤ q+i ∧ q ≤ 1812)) :
    OB5.sig i q = q := by
  rw [OB5.sig_nat]; unfold OB5.sigNat; rw [if_neg (by omega)]

/-- The admin of block `j` (its pack and the previous block's archive load) never writes the band `[1301, 1058+s]`
nor the older moved history `[2070-s, 1812]`, for `start j ≤ 345` (no scratch is moved before tick 370). -/
theorem admin_away (j : Fin 26) (h2 : 1≤j.val) (h18 : j.val≤24) (q : Wire)
    (hq : (1301 ≤ (q:Nat) ∧ (q:Nat) ≤ 1058+start j) ∨ (2070 ≤ (q:Nat)+start j ∧ (q:Nat) ≤ 1812 ∧
      ¬(2070 ≤ (q:Nat)+start j ∧ (q:Nat)+start j ≤ 2084))) :
    q ∉ support j ++ ArchiveJ7.rawPortsList (prev j) := by
  have hs : 60 ≤ start j ∧ start j ≤ 405 := by simp only [StairPacket.start]; omega
  have tick : start (prev j)+15 = start j := by simp only [prev, StairPacket.start]; omega
  intro mem
  rw [List.mem_append, ArchiveJ7.raw_split, List.mem_append] at mem
  rcases mem with mem | mem | mem
  · simp only [support, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false] at mem
    obtain ⟨v, ⟨v1, v2⟩, e | e⟩ := mem
    · rw [sig_kept _ _ (by simp only [MappedCompressed.base]; omega) (by simp only [MappedCompressed.base]; omega)] at e
      simp only [MappedCompressed.base, Wire] at *; omega
    · by_cases mv : 1301 ≤ 1044 + v
      · rw [sig_moved _ _ (Or.inl ⟨by simp only [MappedCompressed.base]; omega, by simp only [MappedCompressed.base]; omega⟩)] at e
        simp only [MappedCompressed.base, Wire] at *; omega
      · rw [sig_kept _ _ (by simp only [MappedCompressed.base]; omega) (by simp only [MappedCompressed.base]; omega)] at e
        simp only [MappedCompressed.base, Wire] at *; omega
  · simp only [ArchiveJ7.rawHead, cellsLoadP, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false, tick] at mem
    rcases mem with ⟨k, hk, e | e⟩ | e
    · simp only [Wire] at *; omega
    · by_cases mv : 1301 ≤ start j + 1034 + k
      · rw [sig_moved _ _ (Or.inl ⟨mv, by omega⟩)] at e
        simp only [Wire] at *; omega
      · rw [sig_kept _ _ (by omega) (by omega)] at e
        simp only [Wire] at *; omega
    · have eb : Shadow7.e0P (start j) = 1574 + Shadow7.sbP (start j) := rfl
      have sbb := Shadow7.rail_win (show 45 ≤ start j by omega) (show start j ≤ 405 by omega)
      simp only [Wire] at *; omega
  · obtain ⟨k, hk, e⟩ := List.mem_map.mp mem
    have hk' := List.mem_range.mp hk
    rw [tick] at e
    have qv : (q:Nat) = Shadow7.scratchS (start j) k := e.symm
    rcases Shadow7.scratchS_cases (start j) k (by omega) hk' with ⟨eqs, lo, hi⟩ | ⟨lo, hi⟩
    · simp only [Wire] at *; omega
    · simp only [Wire] at *; omega

/-- The older moved history of block `j ≤ 18` agrees with the origin after the head (the block's own fold is a
site of the origin; the older folds are untouched and pulled from the stock state). -/
theorem mirror_origin (j : Fin 26) (h2 : 1≤j.val) (h18 : j.val≤24) (hne : start j≠WideReference.firstBlock) (d : Bool)
    (raw s : State) (m t : List Bool) (neg far long : Bool)
    (packed : PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j)
      (EnterJ7.flagF j) (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw)
      (eraseSites (EnterJ7.pending j) s))
    (q : Wire) (lo : 2070 ≤ (q:Nat)+start j) (hi : (q:Nat) ≤ 1812) :
    let history := run (Shadow7.body j (withArchive j d)) t (run (Shadow7.enterP j) m s)
    history.basis q = (WideReference.origin (start j) raw history).basis q := by
  intro history
  have hs : 60 ≤ start j ∧ start j ≤ 405 := by simp only [StairPacket.start]; omega
  have sb := Shadow7.rail_win (show 45 ≤ start j by omega) (show start j ≤ 405 by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := sb
  have w14 : W.narrowSkywalkRouteWidth (start j+14) = railP (start j+14) :=
    LeaveJ7.AssembleCut.route_rail (start j+14) (by omega)
  have w0 : W.narrowSkywalkRouteWidth (start j) = railP (start j) := LeaveJ7.AssembleCut.route_rail (start j) (by omega)
  have rr : railP (start j+14) ≤ 258 := by unfold railP; split_ifs <;> omega
  have ext : ¬WideReference.Box (start j) q := by
    unfold WideReference.Box; rw [w14, w0]; simp only [Wire] at *; omega
  have wn : windowNet j q = 3113 - q := by
    show OB5.sig (start j+14) q = _
    exact sig_moved _ _ (Or.inr ⟨by simp only [Wire] at *; omega, hi⟩)
  have free : ¬Shadow7.MayTouch j (windowNet j q) := by
    rw [wn]
    unfold Shadow7.MayTouch
    have mid : (Shadow7.shape j).mid = Shadow7.sbP (start j)+15 := rfl
    rw [mid]
    simp only [Wire] at *
    omega
  have port : q∉EnterJ7.ports j := by
    intro mem
    have r := EnterJ7.portsRegion j mem
    simp only [Wire] at *
    omega
  apply WideReference.box_origin_j j ext raw history
  intro notSite
  have notAdmin : q∉support j++ArchiveJ7.rawPortsList (prev j) := by
    intro mem
    rw [List.mem_append] at mem
    have tick : start (prev j)+15 = start j := by simp only [prev, StairPacket.start]; omega
    rcases mem with mem | mem
    · rcases admin_outside j (by omega) (by omega) hne q (List.mem_append_right _ mem) with b|b
      · exact ext b
      · exact notSite b
    · rw [ArchiveJ7.raw_split, List.mem_append] at mem
      rcases mem with mem|mem
      · rcases admin_outside j (by omega) (by omega) hne q (List.mem_append_left _ mem) with b|b
        · exact ext b
        · exact notSite b
      · obtain ⟨k,hk,eq⟩ := List.mem_map.mp mem
        have hk' := List.mem_range.mp hk
        rw [tick] at eq
        have qv : (q:Nat) = Shadow7.scratchS (start j) k := eq.symm
        rcases Shadow7.scratchS_cases (start j) k (by omega) hk' with ⟨eqs,lo',hi'⟩|⟨lo',hi'⟩
        · simp only [Wire] at *; omega
        · simp only [Wire] at *; omega
  have stay := Shadow7.ext_head (Shadow7.enterP j) j (withArchive j d)
      (support j++ArchiveJ7.rawPortsList (prev j)) s m t q free (EnterJ7.notWire j port) notAdmin
      (admin_cover j (by omega) (by omega) d)
  have hn : q≠EnterJ7.flagN j := by intro eq; rw [eq] at lo hi; unfold EnterJ7.flagN at lo hi; simp only [Wire] at *; omega
  have hf : q≠EnterJ7.flagF j := by intro eq; rw [eq] at lo hi; unfold EnterJ7.flagF at lo hi; simp only [Wire] at *; omega
  have hu : q≠EnterJ7.flagU j := by intro eq; rw [eq] at lo hi; unfold EnterJ7.flagU at lo hi; simp only [Wire] at *; omega
  have hi' : q∉RailPair.sites (EnterJ7.upperPairs j) := by
    intro mm
    have u := EnterJ7.upperSites j mm
    simp only [Wire] at *
    omega
  have pend : q∉EnterJ7.pending j := by
    intro mem
    simp only [EnterJ7.pending, List.mem_cons, List.not_mem_nil, or_false] at mem
    simp only [Wire] at *
    rcases mem with rfl|rfl|rfl <;> omega
  have old := packed.unchanged q hn hf hu hi'
  rw [stay]
  simpa only [eraseSites, if_neg pend, EnterJ7.pull] using old


/-- The sig band `[1301, 1058+s]` is clean after the head of block `j ≤ 18`: the head never writes it; below
`1044+s` it holds the stock carry top (moved by the pull), above it the block's own future history. -/
theorem band_clean_gen (j : Fin 26) (h2 : 1 ≤ j.val) (h18 : j.val ≤ 24) (d:Bool) (x p:Nat) (good : Bounds x p)
    (raw s:State) (m:List Bool)
    (domain:Domain (start j) x p raw) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s)) :
    ∀ q:Nat, 1301 ≤ q → q ≤ 1058 + start j → (run (nextWindow j d) m s).basis q = false := by
  intro q lo hi
  have hs : 60 ≤ start j ∧ start j ≤ 405 := by simp only [StairPacket.start]; omega
  have sb := Shadow7.rail_win (show 45 ≤ start j by omega) (show start j ≤ 405 by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := sb
  have split : run (nextWindow j d) m s = run (Shadow7.body j (withArchive j d))
      (m.drop (measurementCount (Shadow7.enterP j))) (run (Shadow7.enterP j) m s) := by
    simp only [nextWindow, window, run_append, run_take]
  rw [split]
  have wn : windowNet j q = 3113 - q := by
    show OB5.sig (start j+14) q = _
    exact sig_moved _ _ (Or.inl ⟨lo, by omega⟩)
  have free : ¬Shadow7.MayTouch j (windowNet j q) := by
    rw [wn]
    unfold Shadow7.MayTouch
    have mid : (Shadow7.shape j).mid = Shadow7.sbP (start j)+15 := rfl
    rw [mid]
    simp only [Wire] at *
    omega
  have port : q∉EnterJ7.ports j := by
    intro mem
    have r := EnterJ7.portsRegion j mem
    simp only [Wire] at *
    omega
  have notAdmin := admin_away j (by omega) h18 q (Or.inl ⟨lo, hi⟩)
  rw [Shadow7.ext_head (Shadow7.enterP j) j (withArchive j d) _ s m _ q free (EnterJ7.notWire j port) notAdmin
      (admin_cover j (by omega) (by omega) d)]
  have hn : q≠EnterJ7.flagN j := by unfold EnterJ7.flagN; simp only [Wire] at *; omega
  have hf : q≠EnterJ7.flagF j := by unfold EnterJ7.flagF; simp only [Wire] at *; omega
  have hu : q≠EnterJ7.flagU j := by unfold EnterJ7.flagU; simp only [Wire] at *; omega
  have hi' : q∉RailPair.sites (EnterJ7.upperPairs j) := by
    intro mm
    have u := EnterJ7.upperSites j mm
    simp only [Wire] at *
    omega
  have pend : q∉EnterJ7.pending j := by
    intro mem
    simp only [EnterJ7.pending, List.mem_cons, List.not_mem_nil, or_false] at mem
    simp only [Wire] at *
    rcases mem with rfl|rfl|rfl <;> omega
  have old := cut.unchanged q hn hf hu hi'
  have e1 : s.basis q = (eraseSites (EnterJ7.pending j) s).basis q := by
    show s.basis q = (if q ∈ EnterJ7.pending j then false else s.basis q)
    rw [if_neg pend]
  rw [e1, old]
  show raw.basis (OB5.sig (start j - 1) q) = false
  by_cases mv : q ≤ 1043 + start j
  · rw [sig_moved _ _ (Or.inl ⟨lo, by omega⟩)]
    have c := WideReference.full_carry (start j) 0 x p (by omega) good raw domain [] (3113 - q) (by omega) (by omega)
    simp only [WideReference.span] at c
    have rn : run [] [] raw = raw := by unfold run; rfl
    rw [rn] at c
    exact c
  · rw [sig_kept _ _ (by omega) (by omega)]
    have qid : q = MappedCompressed.base (1028 + (q - 1044)) := by
      show q = 1028 + (q - 1044) + 16; omega
    rw [qid]
    exact WideReference.future_history (show start j ≤ q - 1044 by omega) (by omega) domain

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}BodyCut.result`, generic for the interior blocks up to 255 (the older moved history is
empty there). `band` is the sig band `[1301, s+1058]` before the leave (empty before 243). -/
theorem resultG (j k : Fin 26) (hk : k.val=j.val+1) (h2 : 1≤j.val) (h12 : j.val≤24)
    (hne : start j≠WideReference.firstBlock) (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (a b m:List Bool)
    (neg far long g0 s0:Bool) (domain:Domain (start j) x p raw)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:InputAt (start j) (encode g0 s0 (unsigned (start j) x p).u (unsigned (start j) x p).v) raw)
    (h:Admission.Inputs j (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s))
      (unsigned (start j) x p) g0 s0)
    (phase:(run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).phase=s.phase)
    (popped:(run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis (Shadow7.e0P (start j)+8)=false)
    (tail:∀q∈NativeJ7.tailTemps j,(run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false)
    (band:∀q:Nat,1301≤q → q≤1058+start j →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false)
    (hosts:∀q:Nat,369≤start j → 1302≤q+start j → q≤933 →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false) :
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k) (PortalValues.negative (Admission.flags (unsigned (start j) x p) g0 s0).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k)) ≤ (unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k)
        (endRaw (start j) raw (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s))))
      (eraseSites (EnterJ7.pending k)
        (run (Shadow7.leaveP j) m (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)))) := by
  obtain ⟨w1, w2⟩ := start_win7 j (by omega) (by omega)
  have hs : start k = start j + 15 := by simp only [StairPacket.start]; omega
  have top : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have ag : ∀ q : Wire, ¬WideReference.Box (start j) q → ¬AssembleCut.leftovers j q →
      ¬(2070≤(q:Nat)+start j ∧ (q:Nat)≤1812) →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q =
        (origin (start j) raw (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s))).basis q := by
    intro q nb nl nm
    unfold AssembleCut.leftovers ReleasedOrigin.releasedSite at nl
    simp only [not_or, not_and] at nl
    exact NativeJ7.agree_origin j (by omega) (by omega) hne d raw s a b neg far long cut q nb
      (by simp only [Wire] at *; omega) (by simp only [Wire] at *; omega) (by simp only [Wire] at *; omega)
  have up : ∀ q:Nat, Shadow7.a0P (start j)+16 ≤ q → q ≤ min (start j+30+railP (start j+14)) 529 →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q = false :=
    fun q lo hi => NativeJ7.upper_clear j (by omega) (by omega) d raw s x p domain a b neg far long cut q
      (by unfold Shadow7.a0P at lo; omega) hi
  have mir : ∀ q:Nat, 2070≤q+start j → q≤1812 →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q =
        (origin (start j) raw (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s))).basis q :=
    fun q lo hi => NativeJ7.mirror_origin j (by omega) (by omega) hne d raw s a b neg far long cut q lo hi
  generalize hv : run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s) = v at h phase popped tail band hosts ag up mir ⊢
  have quiet : ∀ q ∈ CoreCheckpoint.rawSites j, v.basis q = false := by
    intro q hq
    simp only [CoreCheckpoint.rawSites, List.mem_append, List.mem_range'_1, List.mem_singleton] at hq
    rcases hq with (⟨lo, hi⟩ | ⟨lo, hi⟩) | p17
    rotate_right
    · rw [p17]; exact h.parked
    · exact native_carryJ j (by omega) (by omega) _ v h.ready h.top h.top2 q (by simp only [Wire] at *; omega)
        (by simp only [Wire] at *; omega)
    · by_cases e8 : (q:Nat) = Shadow7.e0P (start j) + 8
      · have e8' : q = Shadow7.e0P (start j) + 8 := e8
        rw [e8']; exact popped
      · exact tail q (by simp only [NativeJ7.tailTemps, List.mem_range'_1]; simp only [Wire] at *; omega)
  have ph : v.phase = (origin (start j) raw v).phase :=
    phase.trans (cut.phase.trans (origin_phase (start j) x p (by omega) good raw v domain).symm)
  exact CertifiedCut.result j k (by omega) (by omega) (by omega) (by omega) hs x p good raw v m g0 s0 h domain input ph ag
    mir up band hosts quiet

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.BodyCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `NativePack{s}.stock_endpoint`, generic (interior blocks `2 ≤ j ≤ 12`, next block `k = j+1`): the
leave's output is the next block's packed cut, and the next pack's archive facts hold. -/
theorem stock_endpointG (j k : Fin 26) (hk : k.val=j.val+1) (h2 : 1≤j.val) (h12 : j.val≤24)
    (hne : start j≠WideReference.firstBlock) (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State)
    (m n:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (pg ps cross:Bool)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) (unsigned (start (prev j)) x p) pg ps cross s)
    (band : ∀q:Nat,1301≤q → q≤1058+start j → (run (nextWindow j d) m s).basis q=false) :
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k)
      (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start j) x p) G S).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) (endRaw (start j) raw (run (nextWindow j d) m s)))
      (eraseSites (EnterJ7.pending k) (run (Shadow7.leaveP j) n (run (nextWindow j d) m s))) ∧
    PastFacts j (ArchiveJ7.rawPorts j) (Shadow7.sbP (start j)) (unsigned (start j) x p) G S
      (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d j (unsigned (start j) x p)))
      (run (Shadow7.leaveP j) n (run (nextWindow j d) m s)) := by
  obtain ⟨w1, w2⟩ := start_win7 j (by omega) (by omega)
  have numbers:=LeaveJ7.Admission.actualNumbers j (by omega) (by omega) x p good
  have old:=LeaveJ7.Admission.actualNumbers (prev j) (by simp only [prev]; omega) (by simp only [prev]; omega) x p good
  have hist:=pulled_history j rfl domain
  have native:=from_domain j (by omega) (by omega) d x p good raw s m domain G S cut input scratch pg ps cross prior
  obtain ⟨_,_,_,_,tags⟩:=real_receipt j (by omega) (by omega) d raw s m (unsigned (start j) x p) G S numbers.odd
    numbers.farSmall cut input hist scratch (unsigned (start (prev j)) x p) pg ps cross old.odd old.farSmall prior
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) (unsigned (start j) x p) numbers.farSmall numbers.odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s (unsigned (start j) x p) G S m numbers.farSmall cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j (by omega) (by omega) d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity
    ready.2.1 scratch (unsigned (start (prev j)) x p) pg ps cross old.odd old.farSmall prior
  have final:=archive_result j (by omega) (by omega) d row limit _ _ frame
  have tail:=tail_clean j (by omega) (by omega) d x p raw s domain m tape _ _ _ cut row final
  have runEq : run (nextWindow j d) m s = run (Shadow7.body j (withArchive j d)) tape pre := by
    simp only [nextWindow, window, run_append, run_take, pre, tape]
  have gg (g s:Bool) (u v:Int) : (encode g s u v).g=g:=by cases g <;> rfl
  have orig:InputAt (start j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v) raw:=by
    unfold InputAt;rw [gg];exact input
  have h := native.1
  have ph := native.2.1
  refine ⟨?_, LeaveJ7.ArchiveCut.result j (by omega) (by omega) (run (nextWindow j d) m s) n (unsigned (start j) x p) G S h⟩
  have bit : (run (nextWindow j d) m s).basis (Shadow7.e0P (start j)+8) = false := by
    have t2 := tags ⟨2, by omega⟩
    have e : Shadow7.e0P (start j) + 8 = Shadow7.sbP (start j)+1580+(⟨2, by omega⟩:Fin 3).val := by simp only [Shadow7.e0P]; omega
    rw [e]; exact t2
  have hosts : ∀ q:Nat, 369≤start j → 1302≤q+start j → q≤933 →
      (run (Shadow7.body j (withArchive j d)) tape pre).basis q=false := by
    intro q t369 lo hi
    have tj : start j≤405 := by simp only [start]; omega
    have hk' : q-800<134 := by omega
    have tk : start (prev j)+15=start j := by simp only [prev,start]; omega
    have low : ¬(1556+(q-800)<Shadow7.e0P (start j)) := by simp only [Shadow7.e0P,Shadow7.sbP]; omega
    have hw : Shadow7.scratchW (start j) (q-800)=1566+(q-800) := if_neg low
    have far : 2068≤Shadow7.scratchW (start j) (q-800)+start j := by rw [hw]; omega
    have sv : Shadow7.scratchS (start j) (q-800)=q := by
      rw [Shadow7.scratchS_high (start j) (q-800) (by omega) hk' far,hw]; omega
    have port : ArchiveJ7.codePorts (prev j) ⟨16+(q-800),by omega⟩=q := by
      show (ArchiveJ7.codePortsList (prev j)).getD (16+(q-800)) 0=q
      rw [ArchiveJ7.code_scratch (prev j) hk',tk]; exact sv
    have wn : windowNet j q=q := by
      show OB5.sig (start j+14) q=q
      exact sig_kept _ _ (by omega) (by omega)
    have free : ¬Shadow7.MayTouch j (windowNet j q) := by
      rw [wn]
      unfold Shadow7.MayTouch
      have mid : (Shadow7.shape j).mid=Shadow7.sbP (start j)+15 := rfl
      rw [mid]
      simp only [Shadow7.sbP,Wire] at *
      omega
    exact Shadow7.after_encoded j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row pre tape final
      ⟨16+(q-800),by omega⟩ (by show 16≤16+(q-800); omega) q port free
  rw [runEq] at h ph band bit ⊢
  exact LeaveJ7.BodyCut.resultG j k hk (by omega) (by omega) hne d x p good raw s m tape n _ _ _ G S domain cut orig h ph bit tail band
    hosts

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

/-- One B-side code cell `OB5.sig t (t+1034+c)`, `c ≤ 8`: unmoved below 1301, else in the fold. -/
theorem bcell (t c : Nat) (ht : t ≤ 420) (hc : c ≤ 8) :
    (OB5.sig t (t+1034+c) = t+1034+c ∧ t+1034+c ≤ 1300) ∨
    (OB5.sig t (t+1034+c) = 3113-(t+1034+c) ∧ 1301 ≤ t+1034+c) := by
  by_cases h : 1301 ≤ t+1034+c
  · exact Or.inr ⟨NativeJ7.sig_moved _ _ (Or.inl ⟨h, by omega⟩), h⟩
  · exact Or.inl ⟨NativeJ7.sig_kept _ _ (by omega) (by omega), by omega⟩

/-- The 16 restore cells of tick `t ≤ 405`, sig-aware. -/
theorem cells_rangeG (t : Nat) (ht : t ≤ 420) (q : Nat) (h : q ∈ cellsRestoreP t) :
    (t+6 ≤ q ∧ q ≤ t+15) ∨ (t+1034 ≤ q ∧ q ≤ t+1042 ∧ q ≤ 1300) ∨ (2071 ≤ q+t ∧ q+t ≤ 2079 ∧ q ≤ 1812) := by
  have b0 := bcell t 0 ht (by omega)
  have b1 := bcell t 1 ht (by omega)
  have b3 := bcell t 3 ht (by omega)
  have b5 := bcell t 5 ht (by omega)
  have b6 := bcell t 6 ht (by omega)
  have b8 := bcell t 8 ht (by omega)
  simp only [Nat.add_zero] at b0
  simp only [cellsRestoreP, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  first
  | omega
  | (rcases b0 with ⟨e, l⟩ | ⟨e, l⟩ <;> rw [e] <;> omega)
  | (rcases b1 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1035 = t+1034+1 by omega]; rw [e]) <;> omega)
  | (rcases b3 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1037 = t+1034+3 by omega]; rw [e]) <;> omega)
  | (rcases b5 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1039 = t+1034+5 by omega]; rw [e]) <;> omega)
  | (rcases b6 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1040 = t+1034+6 by omega]; rw [e]) <;> omega)
  | (rcases b8 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1042 = t+1034+8 by omega]; rw [e]) <;> omega)

theorem key_rangeG (i : Fin 26) (hi : i.val ≤ 24) (q : Nat)
    (h : q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i)) :
    (start i+21 ≤ q ∧ q ≤ start i+30) ∨ (start i+1049 ≤ q ∧ q ≤ start i+1057 ∧ q ≤ 1300) ∨
    (2056 ≤ q+start i ∧ q+start i ≤ 2064 ∧ q ≤ 1812) := by
  have c := cells_rangeG (start i + 15) (by simp only [StairPacket.start]; omega) q (bank_cells i q h)
  omega

theorem keepLeaveG : KeepLeaveUpTo 24 := by
  intro k h2 h18 q hq v n
  have c := key_rangeG (NativeJ7.prev k) (by simp only [NativeJ7.prev]; omega) q hq
  have pk : start (NativeJ7.prev k) + 15 = start k := by simp only [NativeJ7.prev, StairPacket.start]; omega
  obtain ⟨w1, w2⟩ := start_win7 k (by omega) (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  exact CRTWindow.leave_keeps k (by omega) (by omega) q (by unfold Shadow7.leaveBox2; simp only [Wire] at *; omega) n v

theorem keepOlderG : KeepOlderUpTo 24 := by
  intro i k i' hk h2 hik h18 d q hq s m
  have hs : start i' + 30 ≤ start k := by simp only [StairPacket.start]; omega
  have c := key_rangeG i' (by omega) q hq
  obtain ⟨w1, w2⟩ := start_win7 k (by omega) (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have sk : start k ≤ 405 := by simp only [StairPacket.start]; omega
  have pk : NativeJ7.prev k = i := Fin.ext (by simp only [NativeJ7.prev]; omega)
  rw [next_eq d i k hk]
  simp only [run_append, run_take]
  rw [CRTWindow.leave_keeps k (by omega) (by omega) q (by unfold Shadow7.leaveBox2; simp only [Wire] at *; omega)]
  simp only [NativeJ7.nextWindow, NativeJ7.window, run_append, run_take]
  have native : ¬Shadow7.MayTouch k (windowNet k q) := by
    have mid : (Shadow7.shape k).mid = Shadow7.sbP (start k)+15 := rfl
    rcases c with c | c | c
    · have fixed : windowNet k q = q := by
        show OB5.sig (start k + 14) q = q
        exact NativeJ7.sig_kept _ _ (by omega) (by omega)
      rw [fixed]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
    · have fixed : windowNet k q = q := by
        show OB5.sig (start k + 14) q = q
        exact NativeJ7.sig_kept _ _ (by omega) (by omega)
      rw [fixed]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
    · have moved : windowNet k q = 3113 - q := by
        show OB5.sig (start k + 14) q = _
        exact NativeJ7.sig_moved _ _ (Or.inr ⟨by omega, by omega⟩)
      rw [moved]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
  have port : q ∉ EnterJ7.ports k := by
    simp only [EnterJ7.ports, List.mem_cons, List.not_mem_nil, or_false]
    simp only [Wire] at *
    omega
  have admin : q ∉ NativeJ7.support k ++ ArchiveJ7.rawPortsList (NativeJ7.prev k) := by
    rw [List.mem_append, ArchiveJ7.raw_split]
    intro mem
    rcases mem with mem | mem
    · simp only [NativeJ7.support, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      obtain ⟨v, ⟨v1, v2⟩, e | e⟩ := mem
      · rw [NativeJ7.sig_kept _ _ (by simp only [MappedCompressed.base, Wire] at *; omega)
          (by simp only [MappedCompressed.base, Wire] at *; omega)] at e
        simp only [MappedCompressed.base, Wire] at *; omega
      · by_cases mv : 1301 ≤ 1044 + v
        · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨by simp only [MappedCompressed.base]; omega,
            by simp only [MappedCompressed.base]; omega⟩)] at e
          simp only [MappedCompressed.base, Wire] at *; omega
        · rw [NativeJ7.sig_kept _ _ (by simp only [MappedCompressed.base]; omega)
            (by simp only [MappedCompressed.base]; omega)] at e
          simp only [MappedCompressed.base, Wire] at *; omega
    · rw [List.mem_append] at mem
      have tk : start (NativeJ7.prev k) + 15 = start k := by simp only [NativeJ7.prev, StairPacket.start]; omega
      rcases mem with mem | mem
      · simp only [ArchiveJ7.rawHead, cellsLoadP, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false, tk] at mem
        rcases mem with ⟨c', hc, e | e⟩ | e
        · simp only [Wire] at *; omega
        · by_cases mv : 1301 ≤ start k + 1034 + c'
          · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨mv, by omega⟩)] at e
            simp only [Wire] at *; omega
          · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)] at e
            simp only [Wire] at *; omega
        · simp only [Shadow7.e0P, Wire] at *; omega
      · obtain ⟨kk, hkk, e⟩ := List.mem_map.mp mem
        have hk' := List.mem_range.mp hkk
        rw [tk] at e
        have qv : (q:Nat) = Shadow7.scratchS (start k) kk := e.symm
        rcases Shadow7.scratchS_cases (start k) kk (by omega) hk' with ⟨-, lo, hi⟩ | ⟨-, lo, hi⟩ <;>
          (simp only [Wire] at *; omega)
  exact Shadow7.ext_head (Shadow7.enterP k) k (NativeJ7.withArchive k d) _ s m _ q native (EnterJ7.notWire k port) admin
    (NativeJ7.admin_cover k (by omega) (by omega) d)
theorem endpoint22 : EndpointUpTo 24 := by
  intro j k hk h4 h18 d x p good raw s m n domain G S cut input scratch pg ps cross prior
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have hne : start j ≠ WideReference.firstBlock := by
    simp only [WideReference.firstBlock, StairPacket.start]; omega
  exact NativeJ7.stock_endpointG j k hk (by omega) h18 hne d x p good raw s m n domain G S cut input scratch pg ps cross
    prior (NativeJ7.band_clean_gen j (by omega) h18 d x p good raw s m domain _ _ _ cut)


/-- Every interior leaf of the window up to block 20 (start 375). -/
theorem leaves22 : LeavesUpTo 24 :=
  ⟨endpoint22, scratch, roundtrip, keepLeaveG, keepOlderG, NativeFirstJ7.first, NativeFirstJ7.firstBack⟩

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false


end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run

/-- The generic hand-off at block 21 is the exit-405 hand-off (pairs, flags, pending, raw ports of block 20). -/
theorem exitBridge420 :
    EnterJ7.lowerPairs ⟨25,by decide⟩=Portal420Flag7.loPairs ∧ EnterJ7.upperPairs ⟨25,by decide⟩=Portal420Flag7.hiPairs ∧
    EnterJ7.gate ⟨25,by decide⟩=435 ∧ EnterJ7.flagN ⟨25,by decide⟩=1618 ∧ EnterJ7.flagF ⟨25,by decide⟩=1616 ∧
    EnterJ7.flagU ⟨25,by decide⟩=1617 ∧ EnterJ7.pending ⟨25,by decide⟩=ParkEndpoint4207.src ∧
    ArchiveJ7.rawPorts ⟨24,by decide⟩ 20=1619 ∧ ArchiveJ7.rawPorts ⟨24,by decide⟩ 21=1620 ∧
    ArchiveJ7.rawPorts ⟨24,by decide⟩ 22=1621 := by
  refine ⟨?_,?_,rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩ <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem exitProg420 (d:Bool) : (exitF CRTBarrel.params d 420).flatten=NativePack4207.lastWindow d ∧
    (exitR CRTBarrel.params d 420).flatten=NativePack4207.lastUnwind d := by
  constructor
  · simp only [exitF,CRTBarrel.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
      NativePack4207.lastWindow,NativePack4207.endSlice,EndTick4207.physP,EndTick4207.P,NativePack4207.program,List.append_assoc]
  · simp only [exitR,CRTBarrel.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
      NativePack4207.lastUnwind,NativePack4207.endUndo,EndTick4207.physQ,EndTick4207.Q,NativePack4207.reverse,List.append_assoc]

/-- The exit at 420 (dadon's `step270` rendered at 420). -/
theorem exitStep420 (d:Bool) (x:Nat) (good:Bounds x p) :
    Checked (exitF CRTBarrel.params d (start ⟨24,by decide⟩+15)).flatten
      (exitR CRTBarrel.params d (start ⟨24,by decide⟩+15)).flatten
      (ReadyW d x p (start ⟨24,by decide⟩+15)) (LastAt ArchiveBoundary4207.codePorts ⟨24,by decide⟩ d x p) := by
  have e420 : start ⟨24,by decide⟩+15=420 := rfl
  rw [e420]
  obtain ⟨ef,er⟩:=exitProg420 d
  rw [ef,er]
  intro s m h
  obtain ⟨k,ek,raw,g,sg,pg,ps,pre⟩:=h
  have k20:k=⟨25,by decide⟩:=Fin.ext (by have := ek; simp only [StairPacket.start] at this; show k.val=25; omega)
  subst k20
  obtain ⟨bl,bu,bg,bn,bf,bu',bp,r20,r21,r22⟩:=exitBridge420
  let z:=unsigned 420 x p
  have short:Shadow7.SmallIfFar 39 15 z:=(Shadow7.Envelope.inputs x p 420 (lt_trans good.small good.cap) good.cap (by decide)).1
  have old:=LeaveJ7.Admission.actualNumbers ⟨24,by decide⟩ (by decide) (by decide) x p good
  have eq:farAt 39 420 x p=(2*2^54≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have cut:=pre.cut
  have e20:start (⟨25,by decide⟩:Fin 26)=420:=rfl
  have sb:Shadow7.sbP 420=39:=by decide
  rw [bl,bu,bg,bn,bf,bu',bp] at cut
  simp only [e20,sb] at cut
  have facts:=pre.facts
  have mode:s.basis 1619=decide (Shadow.far 46 15 (unsigned 405 x p)):=by rw [←r20]; exact facts.far
  have side:s.basis 1620=(decide (Shadow.far 46 15 (unsigned 405 x p)) &&
      StairArchiveTrace.afterFlags (decide ((unsigned 405 x p).v<(unsigned 405 x p).u))
        ((Shadow7.physicalCells ArchiveBoundary4207.sourceIdx s).take 5)):=by rw [←r21]; simpa only [Shadow7.physicalCells_eq] using facts.suffix
  have cross:s.basis 1621=(decide (Shadow.far 46 15 (unsigned 405 x p)) &&
      HighBankSum.crossBit (LeaveJ7.TrueMiddle.d ⟨24,by decide⟩ (unsigned 405 x p))):=by rw [←r22]; exact facts.crossed
  have last:=NativePack4207.matched_from_domain d x good.nonzero good.small raw s m pre.domain z short g sg
    (readInput 420 x p raw g sg pre.input) (by simpa only [eq] using cut) (unsigned 405 x p) pg ps _
    old.odd old.farSmall (by simpa only [Shadow7.physicalCells_eq] using facts.records) mode side cross
  obtain ⟨r,lim,truth,frame⟩:=last.2.1
  have pc:signedAt 405 x p pg ps=WideReference.canonical 405 x p:=pre.pastCanonical
  have chr:Chronology 405 x p r:=by unfold Chronology;rw [←pc];exact truth
  exact ⟨last.1,⟨r,lim,chr,frame⟩,last.2.2⟩


/-- A wire bound for a whole program from a per-instruction check. -/
theorem wires_bound405 (P : Program) (b : Nat) (h : P.all (fun i => decide (∀ q ∈ i.wires, q < b)) = true) :
    ∀ q ∈ wires P, q < b := by
  induction P with
  | nil => intro q hq; simp [wires] at hq
  | cons i p ih =>
    intro q hq
    simp only [wires, Finset.mem_union] at hq
    simp only [List.all_cons, Bool.and_eq_true] at h
    rcases hq with hq | hq
    · exact of_decide_eq_true h.1 q hq
    · exact ih h.2 q hq

theorem portalInv_low420 : ∀ q ∈ wires (Shadow7.portalInvP 420), q < 1640 :=
  wires_bound405 _ _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem park_low420 : ∀ q ∈ wires (Shadow7.parkP 420), q < 1640 :=
  wires_bound405 _ _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem raw420_ranges : ∀ w ∈ ArchiveBoundary4207.rawPortsList,
    (426 ≤ w ∧ w ≤ 435) ∨ (1650 ≤ w ∧ w ≤ 1659) ∨ (879 ≤ w ∧ w ≤ 881) ∨ (1556 ≤ w ∧ w ≤ 1647) ∨
    (882 ≤ w ∧ w ≤ 923) := by
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

/-- The exit pieces at 420 never touch the window's key cells (blocks first..19; first = block 1, tick 90). -/
theorem keepExit420 : ∀ (i : Fin 26), WindowParams.first.val ≤ i.val → i.val < 24 → ∀ (d:Bool),
    ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i), ∀ (s:State) (m:List Bool),
    (run (exitF CRTBarrel.params d (start ⟨24,by decide⟩+15)).flatten m s).basis q=s.basis q := by
  intro i h3 h17 d q hq s m
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have c := key_rangeG i (by omega) q hq
  have si : 45 ≤ start i ∧ start i ≤ 390 := by simp only [StairPacket.start]; omega
  have e420 : start ⟨24,by decide⟩+15=420 := rfl
  rw [e420]
  simp only [exitF, CRTBarrel.params,Shadow7.params, ofParts, List.flatten_cons, List.flatten_nil, List.append_nil, run_append, run_take]
  -- exit archive load
  rw [run_preserves_outside (Shadow7.exitLoadP 420 d) _ _ q (fun hit => by
    have r := raw420_ranges q (List.mem_toFinset.mp (ArchiveBoundary4207.load_cover d hit))
    simp only [Wire] at *; omega)]
  -- stock pack at 410
  rw [run_preserves_outside _ _ _ q (fun hit => by
    rw [renameProgram_support] at hit
    obtain ⟨w, hw, e⟩ := Finset.mem_image.mp hit
    have pc := (WindowCovered.pack_cells d 410 (by decide) (by decide)).1 w hw
    obtain ⟨r, r1, r2, er | er⟩ := pc <;> rw [er, OB5.sig_nat] at e <;> unfold OB5.sigNat at e <;>
      rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩ <;> split_ifs at e <;>
      simp only [MappedCompressed.base, Wire] at * <;> omega)]
  -- the stock tick at 420
  have nt : q ∉ wires (renameProgram (OB5.sig 420) (TickRanges.tick base 420)) :=
    EndTick4207.physical_free EndTick4207.P EndTick4207.supports.1 q (by
      apply WideReference.away (by decide)
      rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
      · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)]
        have hn : ∀ n : Nat, 16 ≤ n → n = n - 16 + 16 := fun n h => by omega
        exact ⟨q - 16, by omega, Or.inl (hn q (by omega))⟩
      · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)]
        have hn : ∀ n : Nat, 1044 ≤ n → n = 1028 + (n - 1044) + 16 := fun n h => by omega
        exact ⟨q - 1044, by omega, Or.inr (hn q (by omega))⟩
      · rw [NativeJ7.sig_moved _ _ (Or.inr ⟨by omega, hh⟩)]
        have hn : ∀ n : Nat, n ≤ 1812 → 1301 ≤ 3113 - n → 3113 - n = 1028 + (2069 - n) + 16 := fun n h h' => by omega
        exact ⟨2069 - q, by omega, Or.inr (hn q hh (by omega))⟩)
  rw [run_preserves_outside _ _ _ q nt]
  -- exit portal (inverse) and park
  rw [run_preserves_outside (Shadow7.portalInvP 420) _ _ q (fun hit => by
    have f := portalInv_low420 q hit
    rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
    all_goals
      have f2 := (Shadow7.portal_wires 420 (by decide) (by decide)).2 q hit
      have hr : railP 420 = 93 := by decide
      unfold footP at f2; rw [hr] at f2; simp only [Wire] at *; omega)]
  rw [run_preserves_outside (Shadow7.parkP 420) _ _ q (fun hit => by
    have f := park_low420 q hit
    rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
    all_goals
      have f2 := (Shadow7.park_wires 420 (by decide) (by decide)).1 q hit
      have hr : railP 420 = 93 := by decide
      unfold parkFootP at f2; rw [hr] at f2; simp only [Wire] at *; omega)]

/-- The exit of the window whose last block is 20 (start 405): the exit at 405. -/
theorem exitLeaves420 : ExitLeaves ⟨24,by decide⟩ ArchiveBoundary4207.codePorts :=
  ⟨exitStep420, keepExit420⟩

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end


section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
end ECDSAAdd.Entrant.StairPacket.Shadow7
end

end


/- Inlined from ShadowCounts; provenance retained from022799f6. -/
section

/-! Shadow7 window counts, slots, coverage and physicality (generated by
helpers/staircase82/shadow/port.py from StairSideA; the Main-side families). -/

section
namespace ECDSAAdd.Entrant.StairPacket.WindowSlots7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Baselines ECDSAAdd.Challenge ECDSAAdd.Entrant.StairPacket.WindowSlots

set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem untickR_slots (p : IntegerPacket.Shape) (i : Nat) :
    gateSlots (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick (IntegerPacket.ports p i)
      (IntegerPacket.ports p i).half.length) ≤ 5000 := by
  have ah : (IntegerPacket.ports p i).ah.length=p.mid+1 := by
    simp [IntegerPacket.ports,SkywalkIntegerLayout.ah]
  have bh : (IntegerPacket.ports p i).bh.length=p.mid+1 := by
    simp [IntegerPacket.ports,SkywalkIntegerLayout.bh]
  have hh : (IntegerPacket.ports p i).half.length=p.mid+2 := by simp [SkywalkIntegerLayout.half,ah]
  have hb : (IntegerPacket.ports p i).b.length=p.mid+2 := by simp [SkywalkIntegerLayout.b,bh]
  have hc : (IntegerPacket.ports p i).carry.length=p.mid+1 := by simp [IntegerPacket.ports]
  have w := p.midBound
  have hw : (narrowSkywalkRecordLayout (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length).Widths
      (IntegerPacket.ports p i).half.length := by
    constructor
    · simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.xp,List.length_append,
        List.length_singleton,List.length_take]
      omega
    · simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.yp,List.length_append,
        List.length_singleton,List.length_take]
      omega
    · simp only [narrowSkywalkRecordLayout,List.length_take]
      omega
  have r := ECDSAAdd.Entrant.W.ReverseCarry.narrowReceiver_slots _ _ hw
  have u := (signedRecord_gateSlots_le
    (narrowSkywalkRecordLayout (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length).sx
    (narrowSkywalkRecordLayout (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length).sy
    (narrowSkywalkRecordLayout (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length).q
    ((narrowSkywalkRecordLayout (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length).x.take
      (IntegerPacket.ports p i).half.length)
    ((narrowSkywalkRecordLayout (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length).y.take
      (IntegerPacket.ports p i).half.length)
    ((narrowSkywalkRecordLayout (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length).carry.take
      ((IntegerPacket.ports p i).half.length-1))).2
  have lx := List.length_take_le (IntegerPacket.ports p i).half.length
    (narrowSkywalkRecordLayout (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length).x
  have ly := List.length_take_le (IntegerPacket.ports p i).half.length
    (narrowSkywalkRecordLayout (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length).y
  have ld : ((narrowSkywalkRecordLayout (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length).y.drop
      (IntegerPacket.ports p i).half.length).length = 0 := by
    simp only [List.length_drop,narrowSkywalkRecordLayout,NarrowSignedRecordLayout.y,NarrowSignedRecordLayout.yp,
      List.length_append,List.length_take,List.length_singleton]
    omega
  simp only [narrowSignedUnrecord,gateSlots_append,signComplement_gateSlots] at r
  simp only [ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick,skywalkSignedHalf,gateSlots_append,
    swapRegisters_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,ah,bh,Nat.min_self]
  omega

theorem route (j : Fin 26) (i n : Nat) : gateSlots (Shadow7.routed j i n) ≤ 5000*n ∧
    gateSlots (Shadow7.unrouted j i n) ≤ 5000*n := by
  induction n generalizing i with
  | zero => exact ⟨by rfl,by rfl⟩
  | succ n ih =>
    have tail := ih (i+1)
    have t := tick (Shadow7.shape j) i
    have u := untickR_slots (Shadow7.shape j) i
    simp only [Shadow7.routed,Shadow7.unrouted,gateSlots_append,rename_gateSlots,Nat.mul_succ]
    exact ⟨by omega,by omega⟩

end ECDSAAdd.Entrant.StairPacket.WindowSlots7
end

section
namespace ECDSAAdd.Entrant.StairPacket.PartialPhysical
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum

private theorem integer_ticks (L : SkywalkIntegerLayout) (hv : L.Valid) :
    GatePhysical (skywalkIntegerTick L) ∧ GatePhysical (skywalkIntegerUntick L) := by
  have enough : 1 ≤ L.half.length := by simp [SkywalkIntegerLayout.half]
  have narrow := narrowTicks_physical L 1 hv (by decide) enough
  simp only [narrowSkywalkTick, narrowSkywalkUntick, gatePhysical_append] at narrow
  obtain ⟨⟨⟨⟨route, half⟩, _⟩, prev⟩, ⟨⟨⟨⟨_, _⟩, _⟩, cx⟩, sw⟩⟩ := narrow
  have nd := L.record_nodup hv
  have fresh := (List.nodup_cons.mp nd).1
  have sx : L.ext ≠ L.history := by
    intro e
    apply fresh
    rw [← e]
    simp [SkywalkIntegerLayout.half]
  have sy : L.bSign ≠ L.history := by
    intro e
    apply fresh
    rw [← e]
    simp [SkywalkIntegerLayout.b, SkywalkIntegerLayout.bh]
  have toggle : GatePhysical (skywalkSignToggle L.ext L.bSign L.history) := by
    simp [skywalkSignToggle, GatePhysical, PhysicalInstr, ProperGate, sx, sy]
  have arithmetic := signedWords_physical L.history L.half L.b L.carry nd
  simp only [skywalkIntegerTick, skywalkIntegerUntick, signedRecord, signedUnrecord,
    gatePhysical_append]
  exact ⟨⟨⟨⟨route, half⟩, ⟨⟨toggle, arithmetic.1⟩, toggle⟩⟩, prev⟩,
    ⟨⟨⟨⟨prev, ⟨⟨toggle, arithmetic.2⟩, toggle⟩⟩, half⟩, cx⟩, sw⟩⟩

end ECDSAAdd.Entrant.StairPacket.PartialPhysical
end

section
namespace ECDSAAdd.Entrant.StairPacket.PartialPhysical7
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum ECDSAAdd.Entrant.StairPacket.PartialPhysical

theorem route (j : Fin 26) (a n : Nat) (h : a+n ≤ 15) :
    GatePhysical (Shadow7.routed j a n) ∧ GatePhysical (Shadow7.unrouted j a n) := by
  induction n generalizing a with
  | zero => simp [Shadow7.routed, Shadow7.unrouted, GatePhysical]
  | succ n ih =>
    have ha : a < 15 := by omega
    have valid := IntegerPacket.ok (Shadow7.shape j) ⟨a, ha⟩
    have tick := integer_ticks (IntegerPacket.ports (Shadow7.shape j) a) valid
    have hn : 0 < (IntegerPacket.ports (Shadow7.shape j) a).half.length := by simp [SkywalkIntegerLayout.half]
    have untick := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_physical (IntegerPacket.ports (Shadow7.shape j) a) _
      valid hn le_rfl
    have range := (Shadow7.shape j).rangeEnd
    change start j + 15 ≤ 510 at range
    have inj := OB5.sig_injective (start j+a) (by omega)
    have tail := ih (a+1) (by omega)
    exact ⟨(gatePhysical_append _ _).2 ⟨gatePhysical_rename _ inj _ tick.1, tail.1⟩,
      (gatePhysical_append _ _).2 ⟨tail.2, gatePhysical_rename _ inj _ untick⟩⟩

end ECDSAAdd.Entrant.StairPacket.PartialPhysical7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowParams7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Baselines ECDSAAdd.Challenge ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.WindowParams

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.exitLoadP Shadow7.exitRestoreP Shadow7.routed Shadow7.unrouted Rolling1588.packAtTick Rolling1588.unpackAtTick
theorem portal_ok : ∀ t < 406, portalTick t=true → 5 ≤ Shadow7.wpP t := by decide

theorem portal_ok' (t : Nat) (h : portalTick t=true) : 5 ≤ Shadow7.wpP t := by
  have lt : t < 406 := by simp only [portalTick,Bool.and_eq_true,decide_eq_true_eq] at h; omega
  exact portal_ok t lt h

def tcV : Pieces Nat where
  enter _ := 6
  enterInv _ := 6
  leave j := if inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+3*Shadow7.lowsP (start j)+113 else toffoliCount (Shadow7.leaveMoveP j)
  leaveInv j := if inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+145 else toffoliCount (Shadow7.leaveMoveInvP j)
  load _ d := if d then 42 else 42
  restore _ d := if d then 50 else 51
  portal t := if portalTick t then 4*Shadow7.wpP t-2 else toffoliCount (Shadow7.portalP t)
  portalInv t := if portalTick t then 5*Shadow7.wpP t-4 else toffoliCount (Shadow7.portalInvP t)
  park _ := 0
  parkInv _ := 0
  exitLoad _ d := if d then 42 else 42
  exitRestore _ d := if d then 50 else 51
  routed j a n := if a+n ≤ 15 then n*(2*(Shadow7.smallBits j+16)) else toffoliCount (Shadow7.routed j a n)
  unrouted j a n := if a+n ≤ 15 then n*(2*(Shadow7.smallBits j+16)-1) else toffoliCount (Shadow7.unrouted j a n)
  pack d s t := if dueTick t then 9 else toffoliCount (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))
  unpack d s t := if dueTick t then 11 else toffoliCount (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))
  tick e := if e < 511 then tickT e else toffoliCount (renameProgram (OB5.sig e) (TickRanges.tick base e))
  receiver e := if e < 511 then recvT e else
    toffoliCount (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))

def mcV : Pieces Nat where
  enter _ := 2
  enterInv _ := 3
  leave j := if inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+Shadow7.lowsP (start j)+90 else measurementCount (Shadow7.leaveMoveP j)
  leaveInv j := if inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+58 else measurementCount (Shadow7.leaveMoveInvP j)
  load _ d := if d then 49 else 49
  restore _ d := if d then 43 else 44
  portal t := if portalTick t then 4*Shadow7.wpP t-7 else measurementCount (Shadow7.portalP t)
  portalInv t := if portalTick t then 3*Shadow7.wpP t-5 else measurementCount (Shadow7.portalInvP t)
  park _ := 0
  parkInv _ := 0
  exitLoad _ d := if d then 49 else 49
  exitRestore _ d := if d then 43 else 44
  routed j a n := if a+n ≤ 15 then n*(Shadow7.smallBits j+16) else measurementCount (Shadow7.routed j a n)
  unrouted j a n := if a+n ≤ 15 then n*(Shadow7.smallBits j+16) else measurementCount (Shadow7.unrouted j a n)
  pack d s t := if dueTick t then 4 else measurementCount (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))
  unpack d s t := if dueTick t then 2 else measurementCount (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))
  tick e := if e < 511 then tickM e else measurementCount (renameProgram (OB5.sig e) (TickRanges.tick base e))
  receiver e := if e < 511 then recvM e else
    measurementCount (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))

end ECDSAAdd.Entrant.StairPacket.WindowParams7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowParams
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Baselines ECDSAAdd.Challenge ECDSAAdd.Entrant.StairArchiveGates

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.exitLoadP Shadow7.exitRestoreP Shadow7.routed Shadow7.unrouted Rolling1588.packAtTick Rolling1588.unpackAtTick
private theorem due_of {t : Nat} (h : dueTick t=true) : t≠5 ∧ History5.packDue t=true := by
  simp only [dueTick,Bool.and_eq_true,bne_iff_ne,ne_eq] at h
  exact h

end ECDSAAdd.Entrant.StairPacket.WindowParams
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowParams7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Baselines ECDSAAdd.Challenge ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.WindowParams

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.exitLoadP Shadow7.exitRestoreP Shadow7.routed Shadow7.unrouted Rolling1588.packAtTick Rolling1588.unpackAtTick
theorem tc_eq : Shadow7.params.map toffoliCount=tcV := by
  simp only [Pieces.map,Shadow7.params,ofParts,tcV]
  congr 1
  · funext j; exact (Shadow7.enter_counts j).1
  · funext j; exact (Shadow7.enter_counts j).2.1
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (Shadow7.leaveMove_counts j (by omega) (by omega)).1
    · rfl
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (Shadow7.leaveMove_counts j (by omega) (by omega)).2.1
    · rfl
  · funext j d; rw [(Shadow7.archive_counts j 0 d).1]; cases d
    · exact PartialCosts.part9.1
    · exact PartialCosts.part25.1
  · funext j d; rw [(Shadow7.archive_counts j 0 d).2.2.2.1]; cases d
    · exact PartialCosts.part43.1
    · exact PartialCosts.part57.1
  · funext t; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).1
    · rfl
  · funext t; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).2.1
    · rfl
  · funext e; exact (Shadow7.park_counts e).1
  · funext e; exact (Shadow7.park_counts e).2.1
  · funext e d; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part9.1
    · exact PartialCosts.part25.1
  · funext e d; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part43.1
    · exact PartialCosts.part57.1
  · funext j a n; split
    · rename_i h; exact (WindowFold7.routed_counts j a n h).1
    · rfl
  · funext j a n; split
    · rename_i h; exact (WindowFold7.routed_counts j a n h).2.2.1
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of h).1 (due_of h).2).1
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of h).1 (due_of h).2).2.2.1
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).1
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).2.2.1
    · rfl

theorem mc_eq : Shadow7.params.map measurementCount=mcV := by
  simp only [Pieces.map,Shadow7.params,ofParts,mcV]
  congr 1
  · funext j; exact (Shadow7.enter_counts j).2.2.1
  · funext j; exact (Shadow7.enter_counts j).2.2.2.1
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (Shadow7.leaveMove_counts j (by omega) (by omega)).2.2.1
    · rfl
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (Shadow7.leaveMove_counts j (by omega) (by omega)).2.2.2.1
    · rfl
  · funext j d; rw [(Shadow7.archive_counts j 0 d).2.1]; cases d
    · exact PartialCosts.part9.2
    · exact PartialCosts.part25.2
  · funext j d; rw [(Shadow7.archive_counts j 0 d).2.2.2.2.1]; cases d
    · exact PartialCosts.part43.2
    · exact PartialCosts.part57.2
  · funext t; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).2.2.1
    · rfl
  · funext t; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).2.2.2.1
    · rfl
  · funext e; exact (Shadow7.park_counts e).2.2.1
  · funext e; exact (Shadow7.park_counts e).2.2.2.1
  · funext e d; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part9.2
    · exact PartialCosts.part25.2
  · funext e d; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part43.2
    · exact PartialCosts.part57.2
  · funext j a n; split
    · rename_i h; exact (WindowFold7.routed_counts j a n h).2.1
    · rfl
  · funext j a n; split
    · rename_i h; exact (WindowFold7.routed_counts j a n h).2.2.2
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of h).1 (due_of h).2).2.1
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of h).1 (due_of h).2).2.2.2
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).2.1
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).2.2.2
    · rfl

/-- `slotsV`: upper bounds of the piece slot counts. Exact closed forms where par-b's count lemmas apply (enter,
leave, portal, park, pack), the record's `WindowSlots` bounds for the archives (`part9/25/43/57`) and for the exit
tick/receiver at 270 (`part20/32`), `5000*n` for the routes (`WindowSlots.route`); the measured piece elsewhere, so
`slots_le` holds for every argument and a window `decide` only evaluates closed forms. -/
def slotsV : Pieces Nat where
  enter _ := 35
  enterInv _ := 36
  leave j := if inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+10*Shadow7.lowsP (start j)+730+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveP j)
  leaveInv j := if inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+11*Shadow7.lowsP (start j)+698+3*Shadow7.wpP (start j+15) else
    gateSlots (Shadow7.leaveMoveInvP j)
  load _ d := if d then 3915 else 3159
  restore _ d := if d then 3482 else 3173
  portal t := if portalTick t then 22*Shadow7.wpP t-9 else gateSlots (Shadow7.portalP t)
  portalInv t := if portalTick t then 21*Shadow7.wpP t-7 else gateSlots (Shadow7.portalInvP t)
  park _ := 9
  parkInv _ := 9
  exitLoad _ d := if d then 3915 else 3159
  exitRestore _ d := if d then 3482 else 3173
  routed _ _ n := 5000*n
  unrouted _ _ n := 5000*n
  pack d s t := if dueTick t then 144+(if d then 24 else 12) else
    gateSlots (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))
  unpack d s t := if dueTick t then 142+(if d then 24 else 12) else
    gateSlots (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))
  tick e := if e = 270 then 6004 else gateSlots (renameProgram (OB5.sig e) (TickRanges.tick base e))
  receiver e := if e = 270 then 6001 else
    gateSlots (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))

theorem slots_le : (Shadow7.params.map gateSlots).Le slotsV := by
  simp only [Pieces.map,Shadow7.params,ofParts,slotsV]
  constructor
  · intro j; exact (Shadow7.enter_counts j).2.2.2.2.1.le
  · intro j; exact (Shadow7.enter_counts j).2.2.2.2.2.le
  · intro j; dsimp only; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h
      exact (Shadow7.leaveMove_counts j (by omega) (by omega)).2.2.2.2.1.le
    · exact Nat.le_refl _
  · intro j; dsimp only; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h
      exact (Shadow7.leaveMove_counts j (by omega) (by omega)).2.2.2.2.2.le
    · exact Nat.le_refl _
  · intro j d; dsimp only; rw [(Shadow7.archive_counts j 0 d).2.2.1]; cases d
    · exact WindowSlots.part9
    · exact WindowSlots.part25
  · intro j d; dsimp only; rw [(Shadow7.archive_counts j 0 d).2.2.2.2.2.1]; cases d
    · exact WindowSlots.part43
    · exact WindowSlots.part57
  · intro t; dsimp only; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).2.2.2.2.1.le
    · exact Nat.le_refl _
  · intro t; dsimp only; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).2.2.2.2.2.le
    · exact Nat.le_refl _
  · intro e; exact (Shadow7.park_counts e).2.2.2.2.1.le
  · intro e; exact (Shadow7.park_counts e).2.2.2.2.2.le
  · intro e d; dsimp only; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.2.2.1]; cases d
    · exact WindowSlots.part9
    · exact WindowSlots.part25
  · intro e d; dsimp only; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.2.2.2.2.2]; cases d
    · exact WindowSlots.part43
    · exact WindowSlots.part57
  · intro j a n; exact (WindowSlots7.route j a n).1
  · intro j a n; exact (WindowSlots7.route j a n).2
  · intro d s t; dsimp only; split
    · rename_i h; exact (pack_slots d s t (due_of h).1 (due_of h).2).1.le
    · exact Nat.le_refl _
  · intro d s t; dsimp only; split
    · rename_i h; exact (pack_slots d s t (due_of h).1 (due_of h).2).2.le
    · exact Nat.le_refl _
  · intro e; dsimp only; split
    · rename_i h; subst h; rw [rename_gateSlots]; exact WindowSlots.part20
    · exact Nat.le_refl _
  · intro e; dsimp only; split
    · rename_i h; subst h; rw [rename_gateSlots]; exact WindowSlots.part32
    · exact Nat.le_refl _

end ECDSAAdd.Entrant.StairPacket.WindowParams7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowCovered7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.WindowCovered

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.exitLoadP Shadow7.exitRestoreP
/-- Window-form archives (flags at `e0(t)+6..8`) for ticks up to 390, on the sharp footprint `archFootW`. -/
theorem archFoot_dom {t q : Nat} (lo : 60 ≤ t) (hi : t ≤ 420) (h : archFootW t (Shadow7.e0P t + 6) q) : domainW q = true := by
  rw [dom_iff]; unfold archFootW Shadow7.e0P Shadow7.sbP at h; omega

/-- The stock footprint, exit footprint and packs up to the block-22 exit tick 420. -/
theorem footP_dom420 {s q : Nat} (lo : 45 ≤ s) (hi : s ≤ 420) (h : footP s q) : domainW q = true := by
  have a := top_A s (by omega); have b := rail_le s
  rw [dom_iff]; unfold footP at h; omega
theorem exitFoot_dom420 {e q : Nat} (lo : 225 ≤ e) (hi : e ≤ 420) (h : archFootW e (bTopP e + 1) q) : domainW q = true := by
  have b : railP e ≤ 257 := by unfold railP; split <;> (try split) <;> omega
  rw [dom_iff]; unfold archFootW bTopP at h; omega
theorem pack_cov420 (d : Bool) (s t : Nat) (lo : 45 ≤ t) (ts : t ≤ s) (hi : s ≤ 420) (t5 : t%5=0) :
    CoveredW (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t)) ∧
    CoveredW (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t)) := by
  have due : History5.packDue t=true := by simp only [History5.packDue,decide_eq_true_eq]; omega
  have c := pack_cells d t (by omega) due
  constructor <;> intro q hq <;> rw [renameProgram_support] at hq <;> obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  · obtain ⟨r,r1,r2,e⟩ := c.1 x hx
    rw [dom_iff]; unfold OB5.sig
    rcases e with rfl|rfl <;> simp only [base,Wire] <;> split <;> omega
  · obtain ⟨r,r1,r2,e⟩ := c.2 x hx
    rw [dom_iff]; unfold OB5.sig
    rcases e with rfl|rfl <;> simp only [base,Wire] <;> split <;> omega

/-- `leaveBox_dom` through block 22 (start 405): the leave box stays in the domain up to `s ≤ 514`. -/
theorem leaveBox_dom405 {s q : Nat} (lo : 45 ≤ s) (hi : s ≤ 405) (h : leaveBox s q) : domainW q = true := by
  rw [dom_iff]; unfold leaveBox at h; omega

theorem enter_cov (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) : CoveredW (Shadow7.enterP j) ∧ CoveredW (Shadow7.enterInvP j) := by
  have w := Shadow7.enter_wires j (by omega) (by omega)
  exact ⟨fun q hq => footP_dom (start_lo j h0) (start_win7 j h0 h1).2 (w.1 q hq),
    fun q hq => footP_dom (start_lo j h0) (start_win7 j h0 h1).2 (w.2 q hq)⟩

attribute [local irreducible] Shadow7.leaveOps Shadow7.leaveMoveOps GateMirror.forward GateMirror.inverse in
theorem leaveMove_cov (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    CoveredW (Shadow7.leaveMoveP j) ∧ CoveredW (Shadow7.leaveMoveInvP j) := by
  obtain ⟨w1, w2⟩ := allW_programs (Shadow7.allW_leaveMove (start j) (Shadow7.leaveOps_box j (by omega) (by omega)))
  constructor
  · intro q hq
    rw [Shadow7.leaveMoveP] at hq
    exact leaveBox_dom405 (start_lo j h0) (start_win7 j h0 h1).2 (w1 q hq)
  · intro q hq
    rw [Shadow7.leaveMoveInvP] at hq
    exact leaveBox_dom405 (start_lo j h0) (start_win7 j h0 h1).2 (w2 q hq)

theorem portal_cov (t : Nat) (lo : 45 ≤ t) (hi : t ≤ 420) : CoveredW (Shadow7.portalP t) ∧ CoveredW (Shadow7.portalInvP t) := by
  have w := Shadow7.portal_wires t (by omega) (by omega)
  exact ⟨fun q hq => footP_dom420 lo hi (w.1 q hq), fun q hq => footP_dom420 lo hi (w.2 q hq)⟩

theorem park_cov (e : Nat) (lo : 225 ≤ e) (hi : e ≤ 420) : CoveredW (Shadow7.parkP e) ∧ CoveredW (Shadow7.parkInvP e) := by
  have w := Shadow7.park_wires e (by omega) hi
  exact ⟨fun q hq => parkFoot_dom lo (w.1 q hq), fun q hq => parkFoot_dom lo (w.2 q hq)⟩

theorem archive_cov (j : Fin 26) (d : Bool) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    CoveredW (Shadow7.archiveLoadP j d) ∧ CoveredW (Shadow7.archiveRestoreP j d) := by
  have lo : 60 ≤ start j+15 := by simp only [start]; omega
  have hi : start j+15 ≤ 420 := by simp only [start]; omega
  exact ⟨fun q hq => archFoot_dom lo hi (Shadow7.archiveLoadP_wiresW j d (by omega) q hq),
    fun q hq => archFoot_dom lo hi (Shadow7.archiveRestoreP_wiresW j d (by omega) q hq)⟩

theorem exitArch_cov (e : Nat) (d : Bool) (lo : 225 ≤ e) (hi : e ≤ 420) :
    CoveredW (Shadow7.exitLoadP e d) ∧ CoveredW (Shadow7.exitRestoreP e d) :=
  ⟨fun q hq => exitFoot_dom420 lo hi (Shadow7.exitLoadP_wiresW e d (by omega) q hq),
    fun q hq => exitFoot_dom420 lo hi (Shadow7.exitRestoreP_wiresW e d (by omega) q hq)⟩

/-- Routed ports of block `j` (dadon's `PartialSites.portsPass` decides, generic). -/
theorem ports_dom {j : Fin 26} (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) {a q : Nat} (ha : a < 15)
    (hq : q∈(IntegerPacket.ports (Shadow7.shape j) a).wires) : domainW (net j a q) = true := by
  have hj := j.isLt
  simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false] at hq
  rw [dom_iff]
  unfold net OB5.sig start
  split
  all_goals
    repeat' first | cases_type And | cases_type Or
    all_goals try simp only [Wire] at *
    all_goals omega

theorem routed_cov (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ∀ (a n : Nat), a+n ≤ 15 → CoveredW (Shadow7.routed j a n) ∧ CoveredW (Shadow7.unrouted j a n) := by
  intro a n bound
  induction n generalizing a with
  | zero => constructor <;> intro q h <;> simp [Shadow7.routed,Shadow7.unrouted,wires] at h
  | succ n ih =>
    have h : a < 15 := by omega
    have step := skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (Shadow7.shape j) ⟨a,h⟩)
    have hn : 0 < (IntegerPacket.ports (Shadow7.shape j) a).half.length := by simp [SkywalkIntegerLayout.half]
    have ustep := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_support (IntegerPacket.ports (Shadow7.shape j) a) _
      (IntegerPacket.ok (Shadow7.shape j) ⟨a,h⟩) hn le_rfl
    have sub := ih (a+1) (by omega)
    have ok (P : Program) (hp : wires P ⊆ (IntegerPacket.ports (Shadow7.shape j) a).wires.toFinset) :
        CoveredW (renameProgram (net j a) P) := by
      intro q hq
      rw [renameProgram_support] at hq
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
      exact ports_dom h0 h1 h (List.mem_toFinset.mp (hp hx))
    exact ⟨appW (ok _ step.1) sub.1, appW sub.2 (ok _ ustep)⟩

theorem exitW420 (d : Bool) :
    CoveredW (renameProgram (OB5.sig 420) (TickRanges.tick base 420)) ∧
    CoveredW (renameProgram (OB5.sig 420) (W.ReverseCarry.compactReceiverTick base 420)) ∧
    CoveredW (Shadow7.exitLoadP 420 d) ∧ CoveredW (Shadow7.exitRestoreP 420 d) := by
  have t := exit_tick 420 (by decide) (by decide +kernel)
  exact ⟨t.1,t.2,(exitArch_cov 420 d (by omega) (by omega)).1,(exitArch_cov 420 d (by omega) (by omega)).2⟩

theorem params_onE (d : Bool) : Shadow7.params.OnE CoveredW d 0 24 where
  block j h0 h1 := by
    have e := enter_cov j h0 (by omega)
    have l := leaveMove_cov j h0 (by omega)
    have r0 := routed_cov j h0 (by omega) 0 1 (by omega)
    have r1 := routed_cov j h0 (by omega) 1 14 (by omega)
    exact ⟨e.1,e.2,l.1,l.2,r0.1,r1.1,r0.2,r1.2⟩
  first j h := by
    have hs : start j = 45 := by simp only [start]; omega
    rw [hs]
    have p := pack_cov d 45 45 (by omega) (by omega) (by omega) (by omega)
    have o := portal_cov 45 (by omega) (by omega)
    exact ⟨p.1,p.2,o.1,o.2⟩
  later j h0 h1 := by
    have lo : 60 ≤ start j := by simp only [start]; omega
    have hi : start j ≤ 405 := by simp only [start]; omega
    have m : (start j-10)%5=0 := by simp only [start]; omega
    have p := pack_cov d (start j) (start j-10) (by omega) (by omega) (by omega) m
    exact ⟨p.1,p.2⟩
  saved j h0 h1 := archive_cov j d h0 (by omega)
  exit j h := by
    have hs : start j = 420 := by simp only [start]; omega
    rw [hs]
    have k := park_cov 420 (by omega) (by omega)
    have o := portal_cov 420 (by omega) (by omega)
    have p := pack_cov420 d 420 410 (by omega) (by omega) (by omega) (by omega)
    have x := exitW420 d
    exact ⟨k.1,k.2,o.1,o.2,x.1,x.2.1,p.1,p.2,x.2.2.1,x.2.2.2⟩

end ECDSAAdd.Entrant.StairPacket.WindowCovered7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowPhysicalW7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.WindowPhysicalW

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1 ReducedWindowArchives.restore0 ReducedWindowArchives.restore1
/-- Every gate of the leave is proper (no control on its target): par-c1's segment lemmas, without the state
hypotheses of `leave_ready`. -/
theorem leave_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) : ∀ g ∈ Shadow7.leaveOps (start j), proper g = true := by
  obtain ⟨w1,w2⟩ := start_win7 j h0 h1
  rw [Shadow7.leaveOps_split, Shadow7.leaveMidOps_eq]
  exact proper_append (proper_append (Shadow7.head_ok j h0 h1).2
    (proper_append (proper_append (Shadow7.lowRest_ok w1 w2).2 (Shadow7.storeMapped_ok w1 w2).2) (Shadow7.lowClose_ok w1 w2).2)) (Shadow7.close_ok w1 w2).2

/-- The move leave (`leaveMoveOps`): every gate is proper. -/
theorem leaveMove_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ∀ g ∈ Shadow7.leaveMoveOps (start j), proper g = true := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 h1
  exact Shadow7.leaveMove_proper_of w1 w2 (leave_proper j h0 h1)

theorem leaveMove_phys (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    GatePhysical (Shadow7.leaveMoveP j) ∧ GatePhysical (Shadow7.leaveMoveInvP j) := by
  rw [Shadow7.leaveMoveP, Shadow7.leaveMoveInvP]; exact physical_of_proper _ (leaveMove_proper j h0 h1)

theorem portal_properW45 : (Shadow7.portalOps 45).all proper = true := by decide +kernel

theorem portal_proper420 : (Shadow7.portalOps 420).all proper = true := by decide +kernel

theorem portal_phys45 : GatePhysical (Shadow7.portalP 45) ∧ GatePhysical (Shadow7.portalInvP 45) :=
  physical_of_proper _ (List.all_eq_true.mp portal_properW45)

theorem portal_phys420 : GatePhysical (Shadow7.portalP 420) ∧ GatePhysical (Shadow7.portalInvP 420) :=
  physical_of_proper _ (List.all_eq_true.mp portal_proper420)

/-- Archive moves up to the block-22 exit tick 420. -/
theorem moveLoad_phys420 (t : Nat) (lo : 60 ≤ t) (hi : t ≤ 420) : GatePhysical (moveLoadP t) := by
  rw [moveLoadP]
  refine (physical_of_proper _ (proper_swapsG _ ?_)).1
  simp only [moveLoadPairs, List.forall_mem_cons, List.forall_mem_nil, and_true, ne_eq, OB5.sig]
  and_intros <;> first | (intro x hx; cases hx) | (unfold Wire; split_ifs <;> omega) | (unfold Wire; omega)
theorem moveRestore_phys420 (t f : Nat) (lo : 60 ≤ t) (hi : t ≤ 420) (hf : 1563 ≤ f ∨ f+3 ≤ 1560) :
    GatePhysical (moveRestoreP t f) := by
  rw [moveRestoreP]
  refine (physical_of_proper _ (proper_swapsG _ ?_)).1
  simp only [moveRestorePairs, List.forall_mem_cons, List.forall_mem_nil, and_true, ne_eq, OB5.sig]
  and_intros <;> first | (intro x hx; cases hx) | (unfold Wire; split_ifs <;> omega) | (unfold Wire; omega)

/-- Window-form archives of block `j` (tick `start j + 15`), every window block up to 20. -/
theorem archive_phys (j : Fin 26) (d : Bool) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    GatePhysical (Shadow7.archiveLoadP j d) ∧ GatePhysical (Shadow7.archiveRestoreP j d) := by
  have lo : 60 ≤ start j+15 := by simp only [start]; omega
  have hi : start j+15 ≤ 420 := by simp only [start]; omega
  have nl : (Shadow7.loadPortsWP (start j+15) (Shadow7.e0P (start j+15)+6)).Nodup :=
    (List.nodup_append.mp (ArchiveJ7.rawNodup j h1)).1
  have nr : (Shadow7.restorePortsWP (start j+15)).Nodup := (List.nodup_append.mp (ArchiveJ7.codeNodup j h1)).1
  have fl : 1563 ≤ Shadow7.e0P (start j+15)+6 ∨ Shadow7.e0P (start j+15)+6+3 ≤ 1560 := Or.inl (by unfold Shadow7.e0P Shadow7.sbP; omega)
  constructor
  · rw [Shadow7.archiveLoadP]
    exact appP (load_codec_phys _ nl (by rw [Shadow7.loadPortsWP_length]) d) (moveLoad_phys420 _ lo hi)
  · rw [Shadow7.archiveRestoreP]
    exact appP (restore_codec_phys _ nr (by rw [Shadow7.restorePortsWP_length]) d) (moveRestore_phys420 _ _ lo hi fl)

/-- Stock-form exit archives at 420 (the two port lists by one decide each). -/
theorem exit_phys420 (d : Bool) : GatePhysical (Shadow7.exitLoadP 420 d) ∧ GatePhysical (Shadow7.exitRestoreP 420 d) := by
  have hb : bTopP 420+1 = 879 := by decide
  have nl : (Shadow7.loadPortsXP 420 879).Nodup := by decide +kernel
  have nr : (Shadow7.restorePortsXP 420).Nodup := by decide +kernel
  constructor
  · rw [Shadow7.exitLoadP, hb]
    exact appP (load_codec_phys _ nl (by rw [Shadow7.loadPortsXP_length]) d) (moveLoad_phys420 _ (by omega) (by omega))
  · rw [Shadow7.exitRestoreP, hb]
    exact appP (restore_codec_phys _ nr (by rw [Shadow7.restorePortsXP_length]) d)
      (moveRestore_phys420 _ _ (by omega) (by omega) (Or.inr (by omega)))

attribute [local irreducible] GatePhysical Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP
  Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP Shadow7.exitLoadP Shadow7.exitRestoreP Shadow7.routed Shadow7.unrouted Rolling1588.packAtTick
  Rolling1588.unpackAtTick in
theorem params_onE_phys (d : Bool) : Shadow7.params.OnE GatePhysical d 0 24 where
  block j h0 h1 := by
    have e := Shadow7.enterP_physical j (by omega) (by omega)
    have l := leaveMove_phys j (by omega) (by omega)
    have r0 := PartialPhysical7.route j 0 1 (by omega)
    have r1 := PartialPhysical7.route j 1 14 (by omega)
    exact ⟨e.1,e.2,l.1,l.2,r0.1,r1.1,r0.2,r1.2⟩
  first j h := by
    have hs : start j = 45 := by simp only [start]; omega
    rw [hs]
    have p := pack_phys d 45 45 (by omega) (by omega) (by omega) (by decide)
    exact ⟨p.1,p.2,portal_phys45.1,portal_phys45.2⟩
  later j h0 h1 := by
    have lo : 60 ≤ start j := by simp only [start]; omega
    have hi : start j ≤ 405 := by simp only [start]; omega
    have due : History5.packDue (start j-10)=true := by
      simp only [History5.packDue,decide_eq_true_eq,start]; omega
    have p := pack_phys d (start j) (start j-10) (by omega) (by omega) (by omega) due
    exact ⟨p.1,p.2⟩
  saved j h0 h1 := archive_phys j d h0 (by omega)
  exit j h := by
    have hs : start j = 420 := by simp only [start]; omega
    rw [hs]
    have k := Shadow7.parkP_physical 420 (by omega) (by omega)
    have p := pack_phys d 420 410 (by omega) (by omega) (by omega) (by decide)
    have t := tick_phys 420 (by omega)
    have x := exit_phys420 d
    exact ⟨k.1,k.2,portal_phys420.1,portal_phys420.2,t.1,t.2,p.1,p.2,x.1,x.2⟩

end ECDSAAdd.Entrant.StairPacket.WindowPhysicalW7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowParams7
open ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Challenge ECDSAAdd.Entrant.StairPacket.WindowParams

end ECDSAAdd.Entrant.StairPacket.WindowParams7
end

-- ==== crtf: CRT window ledger, part 2: ledger, coverage, physicality, walk (staircase82, helpers/staircase82/crtf) ====
section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! The ledger: the Shadow7 closed forms with the 20 window leaves replaced. -/

def tcV : Pieces Nat := { WindowParams7.tcV with
  leave := fun j => if crtBlocks j then
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+3*Shadow7.lowsP (start j)+97+CRTBarrel.barrelT (start j) false
    else if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+3*Shadow7.lowsP (start j)+113 else toffoliCount (Shadow7.leaveMoveP j)
  leaveInv := fun j => if crtBlocks j then
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+129+CRTBarrel.barrelT (start j) true
    else if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+145 else toffoliCount (Shadow7.leaveMoveInvP j) }

def mcV : Pieces Nat := { WindowParams7.mcV with
  leave := fun j => if crtBlocks j then
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+Shadow7.lowsP (start j)+89+CRTBarrel.barrelM (start j) false
    else if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+Shadow7.lowsP (start j)+90 else measurementCount (Shadow7.leaveMoveP j)
  leaveInv := fun j => if crtBlocks j then
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+57+CRTBarrel.barrelM (start j) true
    else if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+58 else measurementCount (Shadow7.leaveMoveInvP j) }

def slotsV : Pieces Nat := { WindowParams7.slotsV with
  leave := fun j => if crtBlocks j then
      6*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+10*Shadow7.lowsP (start j)+646+3*Shadow7.wpP (start j+15)+
        CRTBarrel.barrelSlots (start j) false
    else if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+10*Shadow7.lowsP (start j)+730+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveP j)
  leaveInv := fun j => if crtBlocks j then
      6*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+11*Shadow7.lowsP (start j)+614+3*Shadow7.wpP (start j+15)+
        CRTBarrel.barrelSlots (start j) true
    else if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+11*Shadow7.lowsP (start j)+698+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveInvP j) }

/-! Projections of the structure update, by rewriting (a defeq check of `CRTBarrel.params` against
`Shadow7.params` would unfold the leave programs). -/

theorem params_enter : CRTBarrel.params.enter = Shadow7.params.enter := by simp only [CRTBarrel.params]

theorem params_enterInv : CRTBarrel.params.enterInv = Shadow7.params.enterInv := by simp only [CRTBarrel.params]

theorem params_leave : CRTBarrel.params.leave = CRTBarrel.leave := by simp only [CRTBarrel.params]

theorem params_leaveInv : CRTBarrel.params.leaveInv = CRTBarrel.unleave := by simp only [CRTBarrel.params]

theorem params_load : CRTBarrel.params.load = Shadow7.params.load := by simp only [CRTBarrel.params]

theorem params_restore : CRTBarrel.params.restore = Shadow7.params.restore := by simp only [CRTBarrel.params]

theorem params_portal : CRTBarrel.params.portal = Shadow7.params.portal := by simp only [CRTBarrel.params]

theorem params_portalInv : CRTBarrel.params.portalInv = Shadow7.params.portalInv := by simp only [CRTBarrel.params]

theorem params_park : CRTBarrel.params.park = Shadow7.params.park := by simp only [CRTBarrel.params]

theorem params_parkInv : CRTBarrel.params.parkInv = Shadow7.params.parkInv := by simp only [CRTBarrel.params]

theorem params_exitLoad : CRTBarrel.params.exitLoad = Shadow7.params.exitLoad := by simp only [CRTBarrel.params]

theorem params_exitRestore : CRTBarrel.params.exitRestore = Shadow7.params.exitRestore := by simp only [CRTBarrel.params]

theorem params_routed : CRTBarrel.params.routed = Shadow7.params.routed := by simp only [CRTBarrel.params]

theorem params_unrouted : CRTBarrel.params.unrouted = Shadow7.params.unrouted := by simp only [CRTBarrel.params]

theorem params_pack : CRTBarrel.params.pack = Shadow7.params.pack := by simp only [CRTBarrel.params]

theorem params_unpack : CRTBarrel.params.unpack = Shadow7.params.unpack := by simp only [CRTBarrel.params]

theorem params_tick : CRTBarrel.params.tick = Shadow7.params.tick := by simp only [CRTBarrel.params]

theorem params_receiver : CRTBarrel.params.receiver = Shadow7.params.receiver := by simp only [CRTBarrel.params]

/-- Outside the CRT blocks the leave is the plain Shadow7 move leave, priced by the base's closed forms. -/
theorem base_leave (j : Fin 26) :
    toffoliCount (Shadow7.leaveMoveP j) = (if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+3*Shadow7.lowsP (start j)+113 else toffoliCount (Shadow7.leaveMoveP j)) ∧
    toffoliCount (Shadow7.leaveMoveInvP j) = (if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+145 else toffoliCount (Shadow7.leaveMoveInvP j)) ∧
    measurementCount (Shadow7.leaveMoveP j) = (if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+Shadow7.lowsP (start j)+90 else measurementCount (Shadow7.leaveMoveP j)) ∧
    measurementCount (Shadow7.leaveMoveInvP j) = (if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+58 else measurementCount (Shadow7.leaveMoveInvP j)) ∧
    gateSlots (Shadow7.leaveMoveP j) ≤ (if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+10*Shadow7.lowsP (start j)+730+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveP j)) ∧
    gateSlots (Shadow7.leaveMoveInvP j) ≤ (if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+11*Shadow7.lowsP (start j)+698+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveInvP j)) := by
  by_cases h : WindowParams.inBlocks j = true
  · simp only [h, ↓reduceIte]
    simp only [WindowParams.inBlocks, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨t1, t2, m1, m2, s1, s2⟩ := Shadow7.leaveMove_counts j (by omega) (by omega)
    exact ⟨t1, t2, m1, m2, s1.le, s2.le⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte, le_refl, and_self]

theorem tc_eq : CRTBarrel.params.map toffoliCount = tcV := by
  have h := WindowParams7.tc_eq
  unfold Pieces.map at h ⊢
  simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]
  unfold tcV
  rw [← h]
  dsimp only
  congr 1
  · funext j
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).1
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).1]
      exact (base_leave j).1
  · funext j
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).2.1
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).2]
      exact (base_leave j).2.1

theorem mc_eq : CRTBarrel.params.map measurementCount = mcV := by
  have h := WindowParams7.mc_eq
  unfold Pieces.map at h ⊢
  simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]
  unfold mcV
  rw [← h]
  dsimp only
  congr 1
  · funext j
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).2.2.1
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).1]
      exact (base_leave j).2.2.1
  · funext j
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).2.2.2.1
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).2]
      exact (base_leave j).2.2.2.1

private theorem map_leave_update {α β : Type} (P : Pieces α) (f : α → β)
    (a b : Fin 26 → α) :
    Pieces.map f {P with leave := a, leaveInv := b} =
      {P.map f with leave := fun j => f (a j), leaveInv := fun j => f (b j)} := rfl

private theorem le_leave_update {P V : Pieces Nat} (h : P.Le V)
    {a b x y : Fin 26 → Nat} (forward : ∀ j, a j ≤ x j) (mirror : ∀ j, b j ≤ y j) :
    Pieces.Le {P with leave := a, leaveInv := b} {V with leave := x, leaveInv := y} :=
  ⟨h.enter, h.enterInv, forward, mirror, h.load, h.restore, h.portal, h.portalInv, h.park,
    h.parkInv, h.exitLoad, h.exitRestore, h.routed, h.unrouted, h.pack, h.unpack, h.tick, h.receiver⟩

theorem slots_le : (CRTBarrel.params.map gateSlots).Le slotsV := by
  rw [CRTBarrel.params, map_leave_update]
  unfold slotsV
  refine le_leave_update WindowParams7.slots_le ?_ ?_
  · intro j; dsimp only
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).2.2.2.2.1.le
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).1]
      exact (base_leave j).2.2.2.2.1
  · intro j; dsimp only
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).2.2.2.2.2.le
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).2]
      exact (base_leave j).2.2.2.2.2

theorem counts (d : Bool) (j : Fin 26) (js : List (Fin 26)) :
    toffoliCount (forwardW CRTBarrel.params d j js)=(forwardL tcV d j js).sum ∧
    toffoliCount (reverseW CRTBarrel.params d j js)=(reverseL tcV d j js).sum ∧
    measurementCount (forwardW CRTBarrel.params d j js)=(forwardL mcV d j js).sum ∧
    measurementCount (reverseW CRTBarrel.params d j js)=(reverseL mcV d j js).sum := by
  have f := measure_forward toffoliCount toffoliCount_append CRTBarrel.params d j js
  have r := measure_reverse toffoliCount toffoliCount_append CRTBarrel.params d j js
  have g := measure_forward measurementCount measurementCount_append CRTBarrel.params d j js
  have q := measure_reverse measurementCount measurementCount_append CRTBarrel.params d j js
  change toffoliCount _=(forwardL (CRTBarrel.params.map toffoliCount) d j js).sum at f
  change toffoliCount _=(reverseL (CRTBarrel.params.map toffoliCount) d j js).sum at r
  change measurementCount _=(forwardL (CRTBarrel.params.map measurementCount) d j js).sum at g
  change measurementCount _=(reverseL (CRTBarrel.params.map measurementCount) d j js).sum at q
  rw [tc_eq] at f r
  rw [mc_eq] at g q
  exact ⟨f,r,g,q⟩

/-- The CRT window (blocks 1..22, exit 420; CRT barrel on 1..22): counts by one Nat decide over the closed forms. -/
theorem ship_counts :
    toffoliCount (forwardW CRTBarrel.params true first WindowParams7.rest7)=127306 ∧
    toffoliCount (forwardW CRTBarrel.params false first WindowParams7.rest7)=127306 ∧
    toffoliCount (reverseW CRTBarrel.params true first WindowParams7.rest7)=127723 ∧
    toffoliCount (reverseW CRTBarrel.params false first WindowParams7.rest7)=127748 ∧
    measurementCount (forwardW CRTBarrel.params true first WindowParams7.rest7)=66040 ∧
    measurementCount (forwardW CRTBarrel.params false first WindowParams7.rest7)=66040 ∧
    measurementCount (reverseW CRTBarrel.params true first WindowParams7.rest7)=65322 ∧
    measurementCount (reverseW CRTBarrel.params false first WindowParams7.rest7)=65347 := by
  rw [(counts true first WindowParams7.rest7).1,(counts false first WindowParams7.rest7).1,(counts true first WindowParams7.rest7).2.1,(counts false first WindowParams7.rest7).2.1,
    (counts true first WindowParams7.rest7).2.2.1,(counts false first WindowParams7.rest7).2.2.1,(counts true first WindowParams7.rest7).2.2.2,
    (counts false first WindowParams7.rest7).2.2.2]
  decide +kernel

theorem slot_sums : (forwardL slotsV true first WindowParams7.rest7).sum ≤ 2419094 ∧ (forwardL slotsV false first WindowParams7.rest7).sum ≤ 2419094 ∧
    (reverseL slotsV true first WindowParams7.rest7).sum ≤ 2401121 ∧ (reverseL slotsV false first WindowParams7.rest7).sum ≤ 2401121 := by
  decide +kernel

/-- Slot bounds of the CRT window (upper bounds only; the judge has no slot ceiling). -/
theorem ship_slots : gateSlots (forwardW CRTBarrel.params true first WindowParams7.rest7) ≤ 2419094 ∧
    gateSlots (forwardW CRTBarrel.params false first WindowParams7.rest7) ≤ 2419094 ∧
    gateSlots (reverseW CRTBarrel.params true first WindowParams7.rest7) ≤ 2401121 ∧
    gateSlots (reverseW CRTBarrel.params false first WindowParams7.rest7) ≤ 2401121 := by
  rw [measure_forward gateSlots gateSlots_append, measure_forward gateSlots gateSlots_append,
    measure_reverse gateSlots gateSlots_append, measure_reverse gateSlots gateSlots_append]
  exact ⟨(forwardL_le slots_le true first WindowParams7.rest7).trans slot_sums.1,
    (forwardL_le slots_le false first WindowParams7.rest7).trans slot_sums.2.1,
    (reverseL_le slots_le true first WindowParams7.rest7).trans slot_sums.2.2.1,
    (reverseL_le slots_le false first WindowParams7.rest7).trans slot_sums.2.2.2⟩

theorem parts_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.before (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPart (start j), proper g = true) := by
  have p := WindowPhysicalW7.leaveMove_proper j (by omega) (by omega)
  rw [split_ops] at p
  exact ⟨ScanRowGordo.before5Row_proper j h1 (DeadJoin.before5_proper j h1 (show Proper (DeadJoin.beforeAll (start j)) from FlagLeave.cut_proper (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 2 (DeadJoin.beforeScan (start j)) (DeadJoin.before_scan_proper _ (fun g hg => p g (List.mem_append_left _ hg))))),
    DeadJoin.after7K_proper j h1 (show Proper (DeadJoin.afterAll (start j)) from FlagLeave.cut_proper (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 1 (DeadJoin.afterShort (start j)) (DeadJoin.after_short_proper j h1 (fun g hg => p g (List.mem_append_right _ (List.mem_append_right _ hg)))))⟩

theorem leave_phys (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    GatePhysical (CRTBarrel.leave j) ∧ GatePhysical (CRTBarrel.unleave j) := by
  obtain ⟨pb, pa⟩ := parts_proper j h0 h1
  have b := physical_of_proper _ pb
  have a := physical_of_proper _ pa
  rw [(leave_eq j h0 h1).1, (leave_eq j h0 h1).2]
  exact ⟨WindowPhysicalW.appP (WindowPhysicalW.appP b.1 (CRTBarrel.barrel_phys j h0 h1 false)) a.1,
    WindowPhysicalW.appP (WindowPhysicalW.appP a.2 (CRTBarrel.barrel_phys j h0 h1 true)) b.2⟩

theorem params_onE (d : Bool) : CRTBarrel.params.OnE WindowCovered.CoveredW d 0 24 := by
  have h := WindowCovered7.params_onE d
  constructor
  · intro j h0 h1
    have s := h.block j h0 h1
    simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]
    by_cases hc : j.val ≤ 24
    · have l := leave_cov j (Nat.zero_le _) hc
      exact ⟨s.1, s.2.1, l.1, l.2, s.2.2.2.2⟩
    · have e := leave_other j hc
      rw [e.1, e.2]
      have l := WindowCovered7.leaveMove_cov j h0 h1
      exact ⟨s.1, s.2.1, l.1, l.2, s.2.2.2.2⟩
  · intro j hj; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.first j hj
  · intro j h0 h1; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.later j h0 h1
  · intro j h0 h1; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.saved j h0 h1
  · intro j hj; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.exit j hj

/-- The CRT window (both directions, both kernels) lies in the K2 domain. -/
theorem window_covered (d : Bool) :
    WindowCovered.CoveredW (forwardW CRTBarrel.params d WindowParams.first WindowParams7.rest7) ∧
    WindowCovered.CoveredW (reverseW CRTBarrel.params d WindowParams.first WindowParams7.rest7) :=
  ⟨flatten_of WindowCovered.nilW (fun ha hb => WindowCovered.appW ha hb) _
      (forwardL_onE (params_onE d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide)),
    flatten_of WindowCovered.nilW (fun ha hb => WindowCovered.appW ha hb) _
      (reverseL_onE (params_onE d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide))⟩

theorem params_onE_phys (d : Bool) : CRTBarrel.params.OnE GatePhysical d 0 24 := by
  have h := WindowPhysicalW7.params_onE_phys d
  constructor
  · intro j h0 h1
    have s := h.block j h0 h1
    simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]
    by_cases hc : j.val ≤ 24
    · have l := leave_phys j (Nat.zero_le _) hc
      exact ⟨s.1, s.2.1, l.1, l.2, s.2.2.2.2⟩
    · have e := leave_other j hc
      rw [e.1, e.2]
      have l := WindowPhysicalW7.leaveMove_phys j h0 h1
      exact ⟨s.1, s.2.1, l.1, l.2, s.2.2.2.2⟩
  · intro j hj; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.first j hj
  · intro j h0 h1; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.later j h0 h1
  · intro j h0 h1; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.saved j h0 h1
  · intro j hj; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.exit j hj

/-- The CRT window (both directions, both kernels) is physical. -/
theorem window_physical (d : Bool) :
    GatePhysical (forwardW CRTBarrel.params d WindowParams.first WindowParams7.rest7) ∧
    GatePhysical (reverseW CRTBarrel.params d WindowParams.first WindowParams7.rest7) :=
  ⟨flatten_of WindowPhysicalW.nilP (fun ha hb => WindowPhysicalW.appP ha hb) _
      (forwardL_onE (params_onE_phys d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide)),
    flatten_of WindowPhysicalW.nilP (fun ha hb => WindowPhysicalW.appP ha hb) _
      (reverseL_onE (params_onE_phys d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide))⟩

theorem ship_toffoliF_true : toffoliCount (forwardW CRTBarrel.params true first WindowParams7.rest7) = 127306 :=
  ship_counts.1

theorem ship_toffoliF_false : toffoliCount (forwardW CRTBarrel.params false first WindowParams7.rest7) = 127306 :=
  ship_counts.2.1

theorem ship_toffoliR_true : toffoliCount (reverseW CRTBarrel.params true first WindowParams7.rest7) = 127723 :=
  ship_counts.2.2.1

theorem ship_toffoliR_false : toffoliCount (reverseW CRTBarrel.params false first WindowParams7.rest7) = 127748 :=
  ship_counts.2.2.2.1

theorem ship_measureF : measurementCount (forwardW CRTBarrel.params true first WindowParams7.rest7) = 66040 ∧
    measurementCount (forwardW CRTBarrel.params false first WindowParams7.rest7) = 66040 :=
  ⟨ship_counts.2.2.2.2.1, ship_counts.2.2.2.2.2.1⟩

theorem ship_measureR : measurementCount (reverseW CRTBarrel.params true first WindowParams7.rest7) = 65322 ∧
    measurementCount (reverseW CRTBarrel.params false first WindowParams7.rest7) = 65347 :=
  ship_counts.2.2.2.2.2.2

theorem ship_slotsF : gateSlots (forward45plus1 true) ≤ 2419094 ∧ gateSlots (forward45plus1 false) ≤ 2419094 :=
  ⟨ship_slots.1, ship_slots.2.1⟩

theorem ship_slotsR : gateSlots (reverse45plus1 true) ≤ 2401121 ∧ gateSlots (reverse45plus1 false) ≤ 2401121 :=
  ship_slots.2.2

/-! ### FRED-CUT window (harvest-opus port of ercumentyildirim a7d65b7b): every boundary swap pair cancelled -/

/-- The CRT window walk on the cut pieces `FredCut.Pcut`. -/
def forwardCut (d : Bool) : Program := forwardW FredCut.Pcut d first WindowParams7.rest7

def reverseCut (d : Bool) : Program := reverseW FredCut.Pcut d first WindowParams7.rest7

theorem run_cut (d : Bool) : run (forwardCut d) = run (forwardW CRTBarrel.params d first WindowParams7.rest7) :=
  funext fun m => funext fun s => FredCut.walk_run_eq d m s

theorem run_cut_rev (d : Bool) : run (reverseCut d) = run (reverseW CRTBarrel.params d first WindowParams7.rest7) :=
  funext fun m => funext fun s => FredCut.walk_run_eq_rev d m s

theorem cut_toffoli (d : Bool) :
    toffoliCount (forwardCut d) + 104 = toffoliCount (forwardW CRTBarrel.params d first WindowParams7.rest7) ∧
    toffoliCount (reverseCut d) + 104 = toffoliCount (reverseW CRTBarrel.params d first WindowParams7.rest7) :=
  ⟨(FredCut.fwd_cut d).tc_eq, (FredCut.rev_cut d).tc_eq⟩

theorem cut_measure (d : Bool) :
    measurementCount (forwardCut d) = measurementCount (forwardW CRTBarrel.params d first WindowParams7.rest7) ∧
    measurementCount (reverseCut d) = measurementCount (reverseW CRTBarrel.params d first WindowParams7.rest7) :=
  ⟨FredCut.walk_mc_eq d, FredCut.walk_mc_eq_rev d⟩

section
attribute [local irreducible] wires

theorem cut_covered (d : Bool) : WindowCovered.CoveredW (forwardCut d) ∧ WindowCovered.CoveredW (reverseCut d) :=
  ⟨fun q h => (window_covered d).1 q (FredCut.walk_wires_sub d h),
    fun q h => (window_covered d).2 q (FredCut.walk_wires_sub_rev d h)⟩

end

theorem cut_physical (d : Bool) : GatePhysical (forwardCut d) ∧ GatePhysical (reverseCut d) :=
  ⟨fun i h => (window_physical d).1 i ((FredCut.fwd_cut d).mem i h),
    fun i h => (window_physical d).2 i ((FredCut.rev_cut d).mem i h)⟩

theorem cut_slotsF : gateSlots (forwardCut true) ≤ 2419094 ∧ gateSlots (forwardCut false) ≤ 2419094 :=
  ⟨(FredCut.fwd_cut true).slots_le.trans ship_slots.1, (FredCut.fwd_cut false).slots_le.trans ship_slots.2.1⟩

theorem cut_slotsR : gateSlots (reverseCut true) ≤ 2401121 ∧ gateSlots (reverseCut false) ≤ 2401121 :=
  ⟨(FredCut.rev_cut true).slots_le.trans ship_slots.2.2.1, (FredCut.rev_cut false).slots_le.trans ship_slots.2.2.2⟩

theorem cut_toffoliF : toffoliCount (forwardCut true) = 127202 ∧ toffoliCount (forwardCut false) = 127202 := by
  have a := (cut_toffoli true).1
  have b := (cut_toffoli false).1
  rw [ship_toffoliF_true] at a
  rw [ship_toffoliF_false] at b
  exact ⟨by omega, by omega⟩

theorem cut_toffoliR : toffoliCount (reverseCut true) = 127619 ∧ toffoliCount (reverseCut false) = 127644 := by
  have a := (cut_toffoli true).2
  have b := (cut_toffoli false).2
  rw [ship_toffoliR_true] at a
  rw [ship_toffoliR_false] at b
  exact ⟨by omega, by omega⟩

theorem cut_measureF : measurementCount (forwardCut true) = 66040 ∧ measurementCount (forwardCut false) = 66040 := by
  rw [(cut_measure true).1, (cut_measure false).1]
  exact ship_measureF

theorem cut_measureR : measurementCount (reverseCut true) = 65322 ∧ measurementCount (reverseCut false) = 65347 := by
  rw [(cut_measure true).2, (cut_measure false).2]
  exact ship_measureR

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end
