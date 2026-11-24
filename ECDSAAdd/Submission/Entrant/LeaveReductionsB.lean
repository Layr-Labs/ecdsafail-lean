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
import ECDSAAdd.Challenge.Contract
import ECDSAAdd.Submission.Entrant.LeaveReductionsA


-- ---- CRTLeaveCut ----
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveCut
open Partial GateMirror LeaveJ7
attribute [local irreducible] run
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

def selectorTail (s : Nat) : List Gate :=
  rowGates (Shadow7.e0P s+6) (Shadow7.moveRows s) ++ (leaveFix5 s (Shadow7.sbP s)).drop 43

def head (s : Nat) : List Gate := Shadow7.moveA s ++ selectorTail s

theorem before_shape (s : Nat) : CRTBarrel.before s = head s ++ Shadow7.leaveAdjust s := by
  simp only [CRTBarrel.before,head,selectorTail,Shadow7.moveA,Shadow7.leaveFix5Move,List.append_assoc]

theorem move_shape (s : Nat) :
    Shadow7.leaveMoveOps s = CRTBarrel.before s ++ (Shadow7.leaveBarrel s ++ afterPart s) := by
  simp only [Shadow7.leaveMoveOps,CRTBarrel.before,afterPart,List.append_assoc]

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
    (low : Shadow7.a0P (start j)+17 ≤ q) (high : q < Shadow7.a0P (start j)+20) :
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

private theorem selector {j : Fin 26} (_lo : 0≤j.val) (hi : j.val≤24) {s : State}
    {z : SkywalkNat.State} {g sg : Bool} (h : Admission.Inputs j s z g sg) :
    ∃ slot : Fin 17, ∀ k : Fin 16, (run (GateMirror.forward (Shadow7.moveA (start j))) [] s).basis (tagsP.getD k.val 0) =
      decide (slot.val=k.val+1) := by
  classical
  let u := run (GateMirror.forward (Shadow7.moveA (start j))) [] s
  have hot (k : Fin 16) (on : u.basis (tagsP.getD k.val 0) = true) :
      Shadow7.a0P (start j)+k.val = Shadow7.a0P (start j)+LeaveSelector.key (LeaveSelector.actualMode (Shadow7.sbP (start j)) z) := by
    apply (h.hot (Nat.zero_le _) (by omega) []).2 (tagsP.getD k.val 0,Shadow7.a0P (start j)+k.val) _ on
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
    Admissible j (run (GateMirror.forward (CRTBarrel.before (start j))) [] s) := by
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
  have uup (q : Wire) (low : Shadow7.a0P (start j)+17 ≤ q) (high : q < Shadow7.a0P (start j)+20) :
      u.basis q = s.basis q := by rw [hu]; exact head_up_keeps j lo (by omega) s q low high
  have ut (q : Wire) (low : 1559 ≤ q) (high : q ≤ 1576) :
      u.basis q = (run (GateMirror.forward (Shadow7.moveA (start j))) [] s).basis q := by
    rw [hu]; exact tail_keeps j lo (by omega) s q low high
  let p := HighBankAdjust.adjust (ys j) (carries j) (Shadow7.e0P (start j)+3) 1596
  let t := run p [] u'
  let x := regValue (ys j) t.basis
  have pe : GateMirror.forward (Shadow7.leaveAdjustCore (start j)) = p := by simp only [Shadow7.leaveAdjustCore,forward_adjustG,p,ys,carries]
  have eq : run (GateMirror.forward (CRTBarrel.before (start j))) [] s = t := by
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
    let D := (leaveFix5 (start j) (Shadow7.sbP (start j))).drop 43
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
      conv_lhs => rw [Partial.fix5_split (start j) (Shadow7.sbP (start j))]
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
    have u_eq_u0 (q : Wire) (hq : q < Shadow7.a0P (start j) ∨ Shadow7.a0P (start j) + 16 ≤ q) :
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
    have watchedOK := frontReady_frame j (Nat.zero_le _) (by omega) s [] z uFlags.1 uFlags.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp
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
        (native_carryJ j (Nat.zero_le _) (by omega) _ s h.ready h.top _
          (by unfold Wire at *; omega) (by unfold Wire at *; omega))
  · exact (unchanged 1613 (by decide) (by unfold Wire at *; omega)).trans
      (native_carryJ j (Nat.zero_le _) (by omega) _ s h.ready h.top 1613 (by decide) (by unfold Wire at *; omega))

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

private theorem unique {w : Nat → Wire} {len v : Nat} {s x y : State}
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

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.FlagCut
open Partial GateMirror LeaveJ7 LeaveSplice
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem fwd_cons (g : Gate) (gs : List Gate) : GateMirror.forward (g :: gs) = front g :: GateMirror.forward gs := rfl

theorem inv_cons (g : Gate) (gs : List Gate) : GateMirror.inverse (g :: gs) = GateMirror.inverse gs ++ [back g] := by
  simp only [GateMirror.inverse, List.map_cons, List.reverse_cons]

theorem inv_app (a b : List Gate) : GateMirror.inverse (a ++ b) = GateMirror.inverse b ++ GateMirror.inverse a := by
  simp only [GateMirror.inverse, List.map_append, List.reverse_append]

theorem run_nil_append (x y : List Gate) (t : State) :
    run (GateMirror.forward (x ++ y)) [] t = run (GateMirror.forward y) [] (run (GateMirror.forward x) [] t) := by
  simp only [forward_app, run_append, List.drop_nil, List.take_nil]

/-- A fresh flag made from `a ∧ b` holds `b` when `b` implies `a`. -/
theorem make_flag (a b t : Wire) (u : State) (ht : u.basis t = false) (hbt : b ≠ t)
    (imp : u.basis b = true → u.basis a = true) :
    (run (GateMirror.forward [.make a b t]) [] u).basis t = (run (GateMirror.forward [.make a b t]) [] u).basis b := by
  obtain ⟨ph, f⟩ := u
  simp only at ht imp
  simp only [GateMirror.forward, List.map_cons, List.map_nil, front, run, writeBit, Function.update_apply, if_pos rfl,
    if_neg hbt, ht, Bool.false_xor]
  cases hb : f b
  · simp
  · simp [imp hb]

/-- A CNOT twice is the identity. -/
theorem cx_twice (b t : Wire) (u : State) (hbt : b ≠ t) (tape : List Bool) :
    run [.CX b t] tape (run [.CX b t] [] u) = u := by
  obtain ⟨ph, f⟩ := u
  simp only [run, State.mk.injEq, true_and]
  funext q
  by_cases hq : q = t
  · subst hq
    cases h1 : f q <;> cases h2 : f b <;> simp [writeBit, Function.update_apply, hbt, h1, h2]
  · simp [writeBit, Function.update_apply, hq]

/-- When `b` implies `a`, the product `a ∧ b` is `b`: a Toffoli is a CNOT from `b`. -/
theorem ccx_cx (a b t : Wire) (u : State) (imp : u.basis b = true → u.basis a = true) (tape : List Bool) :
    run [.CX b t] tape u = run [.CCX a b t] [] u := by
  have e : (u.basis a && u.basis b) = u.basis b := by
    cases hb : u.basis b
    · simp
    · simp [imp hb]
  simp only [run, e]

theorem ccx_cx_back (a b t : Wire) (u : State) (hbt : b ≠ t) (imp : u.basis b = true → u.basis a = true)
    (tape : List Bool) : run [.CX b t] tape (run [.CCX a b t] [] u) = u := by
  rw [← ccx_cx a b t u imp []]
  exact cx_twice b t u hbt tape

/-- When the target holds `b`, the erasure is a CNOT from `b`. -/
theorem erase_cx (a b t : Wire) (u : State) (hv : u.basis t = u.basis b) (tape : List Bool) :
    run [.CX b t] tape u = run [GateMirror.erase a b t] [] u := by
  obtain ⟨ph, f⟩ := u
  simp only at hv
  simp [GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, hv]

theorem erase_cx_back (a b t : Wire) (u : State) (hbt : b ≠ t) (hv : u.basis t = u.basis b) (tape : List Bool) :
    run [.CX b t] tape (run [GateMirror.erase a b t] [] u) = u := by
  rw [← erase_cx a b t u hv []]
  exact cx_twice b t u hbt tape

theorem keeps_of_targets (gs : List Gate) (q : Wire) (h : ∀ g ∈ gs, target g ≠ q) (m : List Bool) (t : State) :
    (run (GateMirror.forward gs) m t).basis q = t.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [LeaveJ7.dest_forward]
  intro hit
  obtain ⟨g, hg, e⟩ := List.mem_map.mp hit
  exact h g hg e

/-- `LeaveSplice.replace` with three replaced middles. -/
theorem replace3 (a b1 c b2 d b3 e : List Gate) (f1 r1 f2 r2 f3 r3 : Program) (s : State)
    (v : Valid s (a ++ (b1 ++ (c ++ (b2 ++ (d ++ (b3 ++ e)))))))
    (same1 : ∀ t, run f1 t (run (GateMirror.forward a) [] s) =
      run (GateMirror.forward b1) [] (run (GateMirror.forward a) [] s))
    (back1 : ∀ t, run r1 t (run (GateMirror.forward b1) [] (run (GateMirror.forward a) [] s)) =
      run (GateMirror.forward a) [] s)
    (same2 : ∀ t, run f2 t (run (GateMirror.forward (a ++ (b1 ++ c))) [] s) =
      run (GateMirror.forward b2) [] (run (GateMirror.forward (a ++ (b1 ++ c))) [] s))
    (back2 : ∀ t, run r2 t (run (GateMirror.forward b2) [] (run (GateMirror.forward (a ++ (b1 ++ c))) [] s)) =
      run (GateMirror.forward (a ++ (b1 ++ c))) [] s)
    (same3 : ∀ t, run f3 t (run (GateMirror.forward (a ++ (b1 ++ (c ++ (b2 ++ d))))) [] s) =
      run (GateMirror.forward b3) [] (run (GateMirror.forward (a ++ (b1 ++ (c ++ (b2 ++ d))))) [] s))
    (back3 : ∀ t, run r3 t (run (GateMirror.forward b3) [] (run (GateMirror.forward (a ++ (b1 ++ (c ++ (b2 ++ d))))) [] s)) =
      run (GateMirror.forward (a ++ (b1 ++ (c ++ (b2 ++ d))))) [] s) :
    (∀ m, run (GateMirror.forward a ++ f1 ++ GateMirror.forward c ++ f2 ++ GateMirror.forward d ++ f3 ++
        GateMirror.forward e) m s = run (GateMirror.forward (a ++ (b1 ++ (c ++ (b2 ++ (d ++ (b3 ++ e))))))) m s) ∧
    (∀ m n, run (GateMirror.inverse e ++ r3 ++ GateMirror.inverse d ++ r2 ++ GateMirror.inverse c ++ r1 ++
        GateMirror.inverse a) n (run (GateMirror.forward a ++ f1 ++ GateMirror.forward c ++ f2 ++ GateMirror.forward d ++ f3 ++
        GateMirror.forward e) m s) = s) := by
  simp only [run_nil_append] at same2 back2 same3 back3
  obtain ⟨va, v1⟩ := v.parts
  obtain ⟨vb1, v2⟩ := v1.parts
  obtain ⟨vc, v3⟩ := v2.parts
  obtain ⟨vb2, v4⟩ := v3.parts
  obtain ⟨vd, v5⟩ := v4.parts
  obtain ⟨vb3, ve⟩ := v5.parts
  have emitted (m : List Bool) : run (GateMirror.forward a ++ f1 ++ GateMirror.forward c ++ f2 ++ GateMirror.forward d ++ f3 ++
      GateMirror.forward e) m s = run (GateMirror.forward e) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward d) []
        (run (GateMirror.forward b2) [] (run (GateMirror.forward c) [] (run (GateMirror.forward b1) []
          (run (GateMirror.forward a) [] s)))))) := by
    simp only [run_append, run_take, va.default_run, same1, vc.default_run, same2, vd.default_run, same3]
    exact ve.default_run _
  have old (m : List Bool) : run (GateMirror.forward (a ++ (b1 ++ (c ++ (b2 ++ (d ++ (b3 ++ e))))))) m s =
      run (GateMirror.forward e) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward d) []
        (run (GateMirror.forward b2) [] (run (GateMirror.forward c) [] (run (GateMirror.forward b1) []
          (run (GateMirror.forward a) [] s)))))) := by
    simp only [forward_app, run_append, va.default_run, vb1.default_run, vc.default_run, vb2.default_run, vd.default_run,
      vb3.default_run]
    exact ve.default_run _
  refine ⟨fun m => (emitted m).trans (old m).symm, ?_⟩
  intro m n
  rw [emitted]
  have undoE (l : List Bool) := ve.undo_run [] l
  have undoD (l : List Bool) := vd.undo_run [] l
  have undoC (l : List Bool) := vc.undo_run [] l
  simp only [run_append, run_take, undoE, back3, undoD, back2, undoC, back1]
  exact va.undo_run [] _

private theorem headA_targets : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    (headA (start j)).all (fun g => decide (target g ≠ Shadow7.sbP (start j) + 1577 ∧
      target g ≠ Shadow7.sbP (start j) + 1578)) = true := by decide +kernel

/-- The stage-G barrel targets only the control 1613 and bank wires: never the flag 1559 or the side flag. -/
theorem barrel_targets {s : Nat} (w1 : 45 ≤ s) (w2 : s ≤ 405) :
    ∀ g ∈ Shadow7.leaveBarrel s, target g ≠ 1559 ∧ target g ≠ Shadow7.e0P s + 4 := by
  have r := Shadow7.rail_win w1 w2
  have bank : ∀ i, i < Shadow7.wpP s + 15 → (Shadow7.bankW s i ≠ 1559 ∧ Shadow7.bankW s i ≠ Shadow7.e0P s + 4) := by
    intro i hi
    have bc := Shadow7.bank_cases w1 w2 hi
    unfold Shadow7.e0P at *
    ((try unfold Wire at *); omega)
  have hc : True ∧ ((1613 : Wire) ≠ 1559 ∧ (1613 : Wire) ≠ Shadow7.e0P s + 4) := by
    refine ⟨trivial, by decide, ?_⟩
    unfold Shadow7.e0P at *
    ((try unfold Wire at *); omega)
  have h : AllAT (fun _ => True) (fun q => q ≠ 1559 ∧ q ≠ Shadow7.e0P s + 4) (Shadow7.leaveBarrel s) := by
    unfold Shadow7.leaveBarrel
    refine allAT_append (allAT_append (allAT_append ?_ ?_) ?_) ?_ <;>
      refine allAT_stageG _ _ _ _ _ hc (fun _ _ => trivial) (fun i hi => ⟨⟨trivial, bank i (by omega)⟩, ⟨trivial, bank _ (by omega)⟩⟩)
  intro g hg
  exact (h g hg).2

/-- The adjust targets the far flag, bank wires and pool carries: never the flag 1559 or the side flag. -/
theorem adjust_targets {s : Nat} (w1 : 45 ≤ s) (w2 : s ≤ 405) :
    ∀ g ∈ Shadow7.leaveAdjust s, target g ≠ 1559 ∧ target g ≠ Shadow7.e0P s + 4 := by
  have r := Shadow7.rail_win w1 w2
  have bank : ∀ y ∈ (List.range (Shadow7.wpP s)).map (Shadow7.bankW s), True ∧ (y ≠ 1559 ∧ y ≠ Shadow7.e0P s + 4) := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    rw [List.mem_range] at hi
    have bc := Shadow7.bank_cases (i := i) w1 w2 (by omega)
    refine ⟨trivial, ?_⟩
    unfold Shadow7.e0P at *
    ((try unfold Wire at *); omega)
  have pool : ∀ c ∈ (List.range (Shadow7.wpP s - 1)).map (Shadow7.poolW s), True ∧ (c ≠ 1559 ∧ c ≠ Shadow7.e0P s + 4) := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    rw [List.mem_range] at hi
    have pc := Shadow7.pool_cases (i := i) w1 w2
    refine ⟨trivial, ?_⟩
    unfold Shadow7.e0P Shadow7.a0P at *
    ((try unfold Wire at *); omega)
  have h : AllAT (fun _ => True) (fun q => q ≠ 1559 ∧ q ≠ Shadow7.e0P s + 4) (Shadow7.leaveAdjust s) := by
    unfold Shadow7.leaveAdjust Shadow7.leaveAdjustCore
    refine allAT_append (allAT_cons ⟨fun _ _ => trivial, ?_⟩ allAT_nil) (allAT_adjustG _ _ _ _ bank pool trivial trivial)
    show Shadow7.e0P s + 3 ≠ 1559 ∧ Shadow7.e0P s + 3 ≠ Shadow7.e0P s + 4
    unfold Shadow7.e0P at *
    constructor <;> ((try unfold Wire at *); omega)
  intro g hg
  exact (h g hg).2

private theorem ct_targets : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    (([GateMirror.Gate.cx (Shadow7.sbP (start j) + 1577) 1560, GateMirror.Gate.cx 1559 1560] ++ Partial.leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      Shadow7.leaveFix5Move (start j) (Shadow7.sbP (start j))) ++ tailD (start j)).all
      (fun g => decide (target g ≠ 1559 ∧ target g ≠ Shadow7.e0P (start j) + 4)) = true := by decide +kernel

theorem mid_targets (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) :
    ∀ g ∈ headC (start j) ++ (Shadow7.leaveBarrel (start j) ++ tailD (start j)),
      target g ≠ 1559 ∧ target g ≠ Shadow7.e0P (start j) + 4 := by
  have hct := List.all_eq_true.mp (ct_targets j lo hi)
  obtain ⟨w1, w2⟩ := start_win7 j lo hi
  have hc : headC (start j) = ([GateMirror.Gate.cx (Shadow7.sbP (start j) + 1577) 1560, GateMirror.Gate.cx 1559 1560] ++
      Partial.leaveFix4 (start j) (Shadow7.sbP (start j)) ++ Shadow7.leaveFix5Move (start j) (Shadow7.sbP (start j))) ++
      Shadow7.leaveAdjust (start j) := rfl
  intro g hg
  rw [hc] at hg
  rcases List.mem_append.mp hg with h | h
  · rcases List.mem_append.mp h with h | h
    · exact of_decide_eq_true (hct g (List.mem_append_left _ h))
    · exact adjust_targets w1 w2 g h
  · rcases List.mem_append.mp h with h | h
    · exact barrel_targets w1 w2 g h
    · exact of_decide_eq_true (hct g (List.mem_append_right _ h))

theorem e0P_four (s : Nat) : Shadow7.e0P s + 4 = Shadow7.sbP s + 1578 := by unfold Shadow7.e0P; omega

theorem e0P_three (s : Nat) : Shadow7.e0P s + 3 = Shadow7.sbP s + 1577 := by unfold Shadow7.e0P; omega

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.FlagCut

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.FlagCut4
open Partial GateMirror LeaveJ7 LeaveSplice CRTBarrel.FlagCut
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- An erasure whose target holds the product is the Toffoli. -/
theorem erase_ccx (a b t : Wire) (u : State) (ha : a ≠ t) (hb : b ≠ t) (hv : u.basis t = (u.basis a && u.basis b))
    (tape : List Bool) : run [GateMirror.erase a b t] tape u = run [.CCX a b t] [] u := by
  have d := GateMirror.head_default (.pop a b t) u hv (by simp [GateMirror.proper, ha, hb]) tape
  simp only [front, transition] at d
  rw [d]
  obtain ⟨ph, f⟩ := u
  simp only at hv
  simp [GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, hv]

theorem ccx_twice (a b t : Wire) (u : State) (ha : a ≠ t) (hb : b ≠ t) (tape : List Bool) :
    run [.CCX a b t] tape (run [.CCX a b t] [] u) = u := by
  obtain ⟨ph, f⟩ := u
  simp only [run, State.mk.injEq, true_and]
  funext q
  by_cases hq : q = t
  · subst hq
    cases h1 : f q <;> cases h2 : f a <;> cases h3 : f b <;> simp [writeBit, Function.update_apply, ha, hb, h1, h2, h3]
  · simp [writeBit, Function.update_apply, hq]

/-- `replace3` with a fourth replaced middle in front. -/
theorem replace4 (a0 b0 a1 b1 c b2 d b3 e : List Gate) (f0 r0 f1 r1 f2 r2 f3 r3 : Program) (s : State)
    (v : Valid s (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c ++ (b2 ++ (d ++ (b3 ++ e)))))))))
    (same0 : ∀ t, run f0 t (run (GateMirror.forward a0) [] s) =
      run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s))
    (back0 : ∀ t, run r0 t (run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s)) =
      run (GateMirror.forward a0) [] s)
    (same1 : ∀ t, run f1 t (run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s) =
      run (GateMirror.forward b1) [] (run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s))
    (back1 : ∀ t, run r1 t (run (GateMirror.forward b1) [] (run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s)
    (same2 : ∀ t, run f2 t (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c))))) [] s) =
      run (GateMirror.forward b2) [] (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c))))) [] s))
    (back2 : ∀ t, run r2 t (run (GateMirror.forward b2) [] (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c))))) [] s)
    (same3 : ∀ t, run f3 t (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c ++ (b2 ++ d))))))) [] s) =
      run (GateMirror.forward b3) [] (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c ++ (b2 ++ d))))))) [] s))
    (back3 : ∀ t, run r3 t (run (GateMirror.forward b3) []
      (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c ++ (b2 ++ d))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c ++ (b2 ++ d))))))) [] s) :
    (∀ m, run (GateMirror.forward a0 ++ f0 ++ GateMirror.forward a1 ++ f1 ++ GateMirror.forward c ++ f2 ++
        GateMirror.forward d ++ f3 ++ GateMirror.forward e) m s =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c ++ (b2 ++ (d ++ (b3 ++ e))))))))) m s) ∧
    (∀ m n, run (GateMirror.inverse e ++ r3 ++ GateMirror.inverse d ++ r2 ++ GateMirror.inverse c ++ r1 ++
        GateMirror.inverse a1 ++ r0 ++ GateMirror.inverse a0) n
      (run (GateMirror.forward a0 ++ f0 ++ GateMirror.forward a1 ++ f1 ++ GateMirror.forward c ++ f2 ++
        GateMirror.forward d ++ f3 ++ GateMirror.forward e) m s) = s) := by
  simp only [run_nil_append] at same1 back1 same2 back2 same3 back3
  obtain ⟨va0, v1⟩ := v.parts
  obtain ⟨vb0, v2⟩ := v1.parts
  obtain ⟨va1, v3⟩ := v2.parts
  obtain ⟨vb1, v4⟩ := v3.parts
  obtain ⟨vc, v5⟩ := v4.parts
  obtain ⟨vb2, v6⟩ := v5.parts
  obtain ⟨vd, v7⟩ := v6.parts
  obtain ⟨vb3, ve⟩ := v7.parts
  have emitted (m : List Bool) : run (GateMirror.forward a0 ++ f0 ++ GateMirror.forward a1 ++ f1 ++ GateMirror.forward c ++ f2 ++
      GateMirror.forward d ++ f3 ++ GateMirror.forward e) m s =
      run (GateMirror.forward e) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward d) []
        (run (GateMirror.forward b2) [] (run (GateMirror.forward c) [] (run (GateMirror.forward b1) []
          (run (GateMirror.forward a1) [] (run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s)))))))) := by
    simp only [run_append, run_take, va0.default_run, same0, va1.default_run, same1, vc.default_run, same2, vd.default_run,
      same3]
    exact ve.default_run _
  have old (m : List Bool) : run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c ++ (b2 ++ (d ++ (b3 ++ e))))))))) m s =
      run (GateMirror.forward e) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward d) []
        (run (GateMirror.forward b2) [] (run (GateMirror.forward c) [] (run (GateMirror.forward b1) []
          (run (GateMirror.forward a1) [] (run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s)))))))) := by
    simp only [forward_app, run_append, va0.default_run, vb0.default_run, va1.default_run, vb1.default_run, vc.default_run,
      vb2.default_run, vd.default_run, vb3.default_run]
    exact ve.default_run _
  refine ⟨fun m => (emitted m).trans (old m).symm, ?_⟩
  intro m n
  rw [emitted]
  have undoE (l : List Bool) := ve.undo_run [] l
  have undoD (l : List Bool) := vd.undo_run [] l
  have undoC (l : List Bool) := vc.undo_run [] l
  have undoA1 (l : List Bool) := va1.undo_run [] l
  simp only [run_append, run_take, undoE, back3, undoD, back2, undoC, back1, undoA1, back0]
  exact va0.undo_run [] _

private theorem post_targets : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    ((Shadow7.fix0P (start j) (Shadow7.sbP (start j))).drop 55).all (fun g => decide (target g ≠
      start j + Shadow7.sbP (start j) + 48)) = true := by decide +kernel

/-- Row 17's A cell after the scan's head: the swap Toffoli's target holds `s30 ∧ B17`. -/
theorem row17_value {j : Fin 26} (lo : 0 ≤ j.val) (hi : j.val ≤ 24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : LeaveJ7.Admission.Inputs j s z g sg) :
    (run (GateMirror.forward (headA0 (start j))) [] s).basis (start j + Shadow7.sbP (start j) + 48) =
      ((run (GateMirror.forward (headA0 (start j))) [] s).basis (start j + 30) &&
        (run (GateMirror.forward (headA0 (start j))) [] s).basis (Shadow7.sbP (start j) + 803)) := by
  have scan := LeaveJ7.inputScan_result j lo hi s [] _ _ _ _ h.ready h.fresh
  have row := (scan.2.2.1 17 (by decide)).1
  have tight := LeaveShadowRails.inputTight17 (Shadow7.sbP (start j)) z h.farSmall
  rw [Nat.testBit_lt_two_pow tight] at row
  have idx : Shadow7.a0P (start j) - 1 + 17 = start j + Shadow7.sbP (start j) + 48 := by unfold Shadow7.a0P; omega
  rw [idx, CRTWindow.fix0P_cut, run_nil_append, run_nil_append] at row
  have hP := List.all_eq_true.mp (post_targets j lo hi)
  rw [keeps_of_targets _ _ (fun g hg => of_decide_eq_true (hP g hg))] at row
  have ha : start j + 30 ≠ start j + Shadow7.sbP (start j) + 48 := by omega
  have hb : Shadow7.sbP (start j) + 803 ≠ start j + Shadow7.sbP (start j) + 48 := by
    have := (start_win7 j lo (by omega)).2; unfold start at *; omega
  change (run [.CCX (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] []
    (run (GateMirror.forward (headA0 (start j))) [] s)).basis _ = false at row
  generalize run (GateMirror.forward (headA0 (start j))) [] s = u at row ⊢
  obtain ⟨ph, f⟩ := u
  simp only [run, writeBit, Function.update_apply, if_pos rfl] at row
  simp only
  revert row
  cases f (start j + Shadow7.sbP (start j) + 48) <;> cases f (start j + 30) <;>
    cases f (Shadow7.sbP (start j) + 803) <;> simp

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.FlagCut4

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.FlagCut5
open Partial GateMirror LeaveJ7 LeaveSplice CRTBarrel.FlagCut CRTBarrel.FlagCut4
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- With `y` zero, the controlled swap of `x` and `y` is a fresh product copy plus a CNOT. -/
theorem swap_make (t x y : Wire) (u : State) (hxy : x ≠ y) (htx : t ≠ x) (hty : t ≠ y) (hy : u.basis y = false)
    (tape : List Bool) : run [.CCX t x y, .CX y x] tape u = run [.CX x y, .CCX t y x, .CX x y] [] u := by
  obtain ⟨ph, f⟩ := u
  simp only at hy
  simp only [run, State.mk.injEq, true_and]
  funext q
  by_cases hqx : q = x
  · subst hqx
    cases h1 : f q <;> cases h2 : f t <;>
      simp [writeBit, Function.update_apply, hxy, htx, hty, Ne.symm hxy, Ne.symm htx, Ne.symm hty, h1, h2, hy]
  · by_cases hqy : q = y
    · subst hqy
      cases h1 : f x <;> cases h2 : f t <;>
        simp [writeBit, Function.update_apply, hxy, htx, hty, Ne.symm hxy, Ne.symm htx, Ne.symm hty, h1, h2, hy, hqx]
    · simp [writeBit, Function.update_apply, hqx, hqy]

theorem swap_make_back (t x y : Wire) (u : State) (hxy : x ≠ y) (htx : t ≠ x) (hty : t ≠ y) (hy : u.basis y = false)
    (tape : List Bool) :
    run [.CX y x, GateMirror.erase t x y] tape (run [.CX x y, .CCX t y x, .CX x y] [] u) = u := by
  rw [← swap_make t x y u hxy htx hty hy []]
  have split : run [.CX y x, GateMirror.erase t x y] tape (run [.CCX t x y, .CX y x] [] u) =
      run [GateMirror.erase t x y] tape (run [.CX y x] [] (run [.CCX t x y, .CX y x] [] u)) := by
    rw [show [Instr.CX y x, GateMirror.erase t x y] = [Instr.CX y x] ++ [GateMirror.erase t x y] from rfl, run_append]
    rfl
  rw [split]
  have pr : proper (Gate.pop t x y) = true := by simp [GateMirror.proper, hty, hxy]
  obtain ⟨ph, f⟩ := u
  simp only at hy
  have val : ValueOK (run [.CX y x] [] (run [.CCX t x y, .CX y x] [] ⟨ph, f⟩)) (Gate.pop t x y) := by
    show _ = _
    cases h1 : f x <;> cases h2 : f t <;>
      simp [run, writeBit, Function.update_apply, hxy, htx, hty, Ne.symm hxy, Ne.symm htx, Ne.symm hty, h1, h2, hy]
  have d := head_default (Gate.pop t x y) _ val pr tape
  simp only [front, transition] at d
  rw [d]
  simp only [GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, List.headD, Bool.false_and, Bool.xor_false,
    Bool.false_eq_true, if_false, ite_false, State.mk.injEq, true_and]
  funext q
  by_cases hqx : q = x
  · subst hqx
    cases h1 : f q <;> cases h2 : f t <;>
      simp [writeBit, Function.update_apply, hxy, htx, hty, Ne.symm hxy, Ne.symm htx, Ne.symm hty, h1, h2, hy]
  · by_cases hqy : q = y
    · subst hqy
      cases h1 : f x <;> cases h2 : f t <;>
        simp [writeBit, Function.update_apply, hxy, htx, hty, Ne.symm hxy, Ne.symm htx, Ne.symm hty, h1, h2, hy, hqx]
    · simp [writeBit, Function.update_apply, hqx, hqy]


theorem before_split5 (s : Nat) : CRTBarrel.before s =
    headA0 s ++ ([.ccx (s+30) (Shadow7.sbP s + 803) (s + Shadow7.sbP s + 48)] ++ (headA1 s ++
      ([.make (Shadow7.sbP s + 1577) (Shadow7.sbP s + 1578) 1559] ++ (headC0 s ++
      ([.cx (Shadow7.a0P s + 0) (Shadow7.e0P s + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P s + 6) (Shadow7.a0P s + 0),
        .cx (Shadow7.a0P s + 0) (Shadow7.e0P s + 6)] ++ headC1 s))))) := by
  rw [CRTWindow.before_split4, CRTWindow.headC_cut]

/-- `replace4` with a fifth replaced middle between the flag gate and the barrel. -/
theorem replace5 (a0 b0 a1 b1 c0 bR c1 b2 d b3 e : List Gate) (f0 r0 f1 r1 fR rR f2 r2 f3 r3 : Program) (s : State)
    (v : Valid s (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ (d ++ (b3 ++ e)))))))))))
    (same0 : ∀ t, run f0 t (run (GateMirror.forward a0) [] s) =
      run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s))
    (back0 : ∀ t, run r0 t (run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s)) =
      run (GateMirror.forward a0) [] s)
    (same1 : ∀ t, run f1 t (run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s) =
      run (GateMirror.forward b1) [] (run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s))
    (back1 : ∀ t, run r1 t (run (GateMirror.forward b1) [] (run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s)
    (sameR : ∀ t, run fR t (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c0))))) [] s) =
      run (GateMirror.forward bR) [] (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c0))))) [] s))
    (backR : ∀ t, run rR t (run (GateMirror.forward bR) [] (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c0))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c0))))) [] s)
    (same2 : ∀ t, run f2 t (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ c1))))))) [] s) =
      run (GateMirror.forward b2) [] (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ c1))))))) [] s))
    (back2 : ∀ t, run r2 t (run (GateMirror.forward b2) []
      (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ c1))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ c1))))))) [] s)
    (same3 : ∀ t, run f3 t (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ d))))))))) [] s) =
      run (GateMirror.forward b3) [] (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ d))))))))) [] s))
    (back3 : ∀ t, run r3 t (run (GateMirror.forward b3) []
      (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ d))))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ d))))))))) [] s) :
    (∀ m, run (GateMirror.forward a0 ++ f0 ++ GateMirror.forward a1 ++ f1 ++ GateMirror.forward c0 ++ fR ++
        GateMirror.forward c1 ++ f2 ++ GateMirror.forward d ++ f3 ++ GateMirror.forward e) m s =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ (d ++ (b3 ++ e))))))))))) m s) ∧
    (∀ m n, run (GateMirror.inverse e ++ r3 ++ GateMirror.inverse d ++ r2 ++ GateMirror.inverse c1 ++ rR ++
        GateMirror.inverse c0 ++ r1 ++ GateMirror.inverse a1 ++ r0 ++ GateMirror.inverse a0) n
      (run (GateMirror.forward a0 ++ f0 ++ GateMirror.forward a1 ++ f1 ++ GateMirror.forward c0 ++ fR ++
        GateMirror.forward c1 ++ f2 ++ GateMirror.forward d ++ f3 ++ GateMirror.forward e) m s) = s) := by
  simp only [run_nil_append] at same1 back1 sameR backR same2 back2 same3 back3
  obtain ⟨va0, v1⟩ := v.parts
  obtain ⟨vb0, v2⟩ := v1.parts
  obtain ⟨va1, v3⟩ := v2.parts
  obtain ⟨vb1, v4⟩ := v3.parts
  obtain ⟨vc0, v5⟩ := v4.parts
  obtain ⟨vbR, v6⟩ := v5.parts
  obtain ⟨vc1, v7⟩ := v6.parts
  obtain ⟨vb2, v8⟩ := v7.parts
  obtain ⟨vd, v9⟩ := v8.parts
  obtain ⟨vb3, ve⟩ := v9.parts
  have emitted (m : List Bool) : run (GateMirror.forward a0 ++ f0 ++ GateMirror.forward a1 ++ f1 ++ GateMirror.forward c0 ++ fR ++
      GateMirror.forward c1 ++ f2 ++ GateMirror.forward d ++ f3 ++ GateMirror.forward e) m s =
      run (GateMirror.forward e) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward d) []
        (run (GateMirror.forward b2) [] (run (GateMirror.forward c1) [] (run (GateMirror.forward bR) []
        (run (GateMirror.forward c0) [] (run (GateMirror.forward b1) []
          (run (GateMirror.forward a1) [] (run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s)))))))))) := by
    simp only [run_append, run_take, va0.default_run, same0, va1.default_run, same1, vc0.default_run, sameR,
      vc1.default_run, same2, vd.default_run, same3]
    exact ve.default_run _
  have old (m : List Bool) :
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ (d ++ (b3 ++ e))))))))))) m s =
      run (GateMirror.forward e) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward d) []
        (run (GateMirror.forward b2) [] (run (GateMirror.forward c1) [] (run (GateMirror.forward bR) []
        (run (GateMirror.forward c0) [] (run (GateMirror.forward b1) []
          (run (GateMirror.forward a1) [] (run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s)))))))))) := by
    simp only [forward_app, run_append, va0.default_run, vb0.default_run, va1.default_run, vb1.default_run, vc0.default_run,
      vbR.default_run, vc1.default_run, vb2.default_run, vd.default_run, vb3.default_run]
    exact ve.default_run _
  refine ⟨fun m => (emitted m).trans (old m).symm, ?_⟩
  intro m n
  rw [emitted]
  have undoE (l : List Bool) := ve.undo_run [] l
  have undoD (l : List Bool) := vd.undo_run [] l
  have undoC1 (l : List Bool) := vc1.undo_run [] l
  have undoC0 (l : List Bool) := vc0.undo_run [] l
  have undoA1 (l : List Bool) := va1.undo_run [] l
  simp only [run_append, run_take, undoE, back3, undoD, back2, undoC1, backR, undoC0, back1, undoA1, back0]
  exact va0.undo_run [] _

private theorem pre5_targets : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    (headA0 (start j) ++ ([GateMirror.Gate.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++
      (headA1 (start j) ++ ([GateMirror.Gate.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++
      headC0 (start j))))).all (fun g => decide (target g ≠ Shadow7.e0P (start j) + 6)) = true := by decide +kernel

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.FlagCut5

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.FlagCut6
open Partial GateMirror LeaveJ7 LeaveSplice CRTBarrel.FlagCut CRTBarrel.FlagCut4 CRTBarrel.FlagCut5
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- A high join pair whose shadow cell is zero is the identity. -/
theorem pair_high_id (a sh tb : Wire) (u : State) (hne : sh ≠ tb) (hsh : u.basis sh = false) :
    run (GateMirror.forward (Partial.pairGM false a sh tb)) [] u = u := by
  obtain ⟨ph, f⟩ := u
  simp only at hsh
  simp only [Partial.pairGM, Bool.false_eq_true, if_false, ite_false, GateMirror.forward, List.map_cons, List.map_nil, front,
    GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, List.headD, Bool.false_and, Bool.xor_false,
    State.mk.injEq, true_and]
  funext q
  by_cases hq : q = sh
  · subst hq
    simp [writeBit, Function.update_apply, hne, hsh]
  · by_cases hq2 : q = tb
    · subst hq2
      simp [writeBit, Function.update_apply, hq, Ne.symm hne, hsh]
    · simp [writeBit, Function.update_apply, hq, hq2]


/-- The stage-G barrel never targets row 16's shadow cell `a0P+16`. -/
theorem barrel_targets16 {s : Nat} (w1 : 45 ≤ s) (w2 : s ≤ 405) :
    ∀ g ∈ Shadow7.leaveBarrel s, target g ≠ Shadow7.a0P s + 16 := by
  have r := Shadow7.rail_win w1 w2
  have bank : ∀ i, i < Shadow7.wpP s + 15 → Shadow7.bankW s i ≠ Shadow7.a0P s + 16 := by
    intro i hi
    have bc := Shadow7.bank_cases w1 w2 hi
    unfold Shadow7.e0P Shadow7.a0P at *
    ((try unfold Wire at *); omega)
  have hc : True ∧ ((1613 : Wire) ≠ Shadow7.a0P s + 16) := by
    refine ⟨trivial, ?_⟩
    unfold Shadow7.a0P at *
    ((try unfold Wire at *); omega)
  have h : AllAT (fun _ => True) (fun q => q ≠ Shadow7.a0P s + 16) (Shadow7.leaveBarrel s) := by
    unfold Shadow7.leaveBarrel
    refine allAT_append (allAT_append (allAT_append ?_ ?_) ?_) ?_ <;>
      refine allAT_stageG _ _ _ _ _ hc (fun _ _ => trivial) (fun i hi => ⟨⟨trivial, bank i (by omega)⟩, ⟨trivial, bank _ (by omega)⟩⟩)
  intro g hg
  exact (h g hg).2

/-- The adjust never targets row 16's shadow cell `a0P+16`. -/
theorem adjust_targets16 {s : Nat} (w1 : 45 ≤ s) (w2 : s ≤ 405) :
    ∀ g ∈ Shadow7.leaveAdjust s, target g ≠ Shadow7.a0P s + 16 := by
  have r := Shadow7.rail_win w1 w2
  have bank : ∀ y ∈ (List.range (Shadow7.wpP s)).map (Shadow7.bankW s), True ∧ y ≠ Shadow7.a0P s + 16 := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    rw [List.mem_range] at hi
    have bc := Shadow7.bank_cases (i := i) w1 w2 (by omega)
    refine ⟨trivial, ?_⟩
    unfold Shadow7.e0P Shadow7.a0P at *
    ((try unfold Wire at *); omega)
  have pool : ∀ c ∈ (List.range (Shadow7.wpP s - 1)).map (Shadow7.poolW s), True ∧ c ≠ Shadow7.a0P s + 16 := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    rw [List.mem_range] at hi
    have pc := Shadow7.pool_cases (i := i) w1 w2
    refine ⟨trivial, ?_⟩
    unfold Shadow7.e0P Shadow7.a0P at *
    ((try unfold Wire at *); omega)
  have h : AllAT (fun _ => True) (fun q => q ≠ Shadow7.a0P s + 16) (Shadow7.leaveAdjust s) := by
    unfold Shadow7.leaveAdjust Shadow7.leaveAdjustCore
    refine allAT_append (allAT_cons ⟨fun _ _ => trivial, ?_⟩ allAT_nil) (allAT_adjustG _ _ _ _ bank pool trivial trivial)
    show Shadow7.e0P s + 3 ≠ Shadow7.a0P s + 16
    unfold Shadow7.e0P Shadow7.a0P at *
    ((try unfold Wire at *); omega)
  intro g hg
  exact (h g hg).2

private theorem lit_targets16 : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    ((Partial.leaveFix1 (start j) (Shadow7.sbP (start j)) ++ Shadow7.fix2P (start j) (Shadow7.sbP (start j)) ++
      [GateMirror.Gate.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ headC0 (start j) ++
      [GateMirror.Gate.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6),
        GateMirror.Gate.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0),
        GateMirror.Gate.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++
      (rowGates (Shadow7.e0P (start j) + 6) ((Shadow7.moveRows (start j)).drop 1) ++
        (Partial.leaveFix5 (start j) (Shadow7.sbP (start j))).drop 43)) ++ tailD0 (start j)).all
      (fun g => decide (target g ≠ Shadow7.a0P (start j) + 16)) = true := by decide +kernel

/-- `replace5` with a sixth replaced middle between the barrel and the flag erasure. -/
theorem replace6 (a0 b0 a1 b1 c0 bR c1 b2 d0 bJ d1 b3 e : List Gate) (f0 r0 f1 r1 fR rR f2 r2 fJ rJ f3 r3 : Program)
    (s : State)
    (v : Valid s (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ (d0 ++ (bJ ++ (d1 ++ (b3 ++ e)))))))))))))
    (same0 : ∀ t, run f0 t (run (GateMirror.forward a0) [] s) =
      run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s))
    (back0 : ∀ t, run r0 t (run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s)) =
      run (GateMirror.forward a0) [] s)
    (same1 : ∀ t, run f1 t (run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s) =
      run (GateMirror.forward b1) [] (run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s))
    (back1 : ∀ t, run r1 t (run (GateMirror.forward b1) [] (run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ a1))) [] s)
    (sameR : ∀ t, run fR t (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c0))))) [] s) =
      run (GateMirror.forward bR) [] (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c0))))) [] s))
    (backR : ∀ t, run rR t (run (GateMirror.forward bR) [] (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c0))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ c0))))) [] s)
    (same2 : ∀ t, run f2 t (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ c1))))))) [] s) =
      run (GateMirror.forward b2) [] (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ c1))))))) [] s))
    (back2 : ∀ t, run r2 t (run (GateMirror.forward b2) []
      (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ c1))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ c1))))))) [] s)
    (sameJ : ∀ t, run fJ t (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ d0))))))))) [] s) =
      run (GateMirror.forward bJ) [] (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ d0))))))))) [] s))
    (backJ : ∀ t, run rJ t (run (GateMirror.forward bJ) []
      (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ d0))))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ d0))))))))) [] s)
    (same3 : ∀ t, run f3 t (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ (d0 ++ (bJ ++ d1))))))))))) [] s) =
      run (GateMirror.forward b3) []
        (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ (d0 ++ (bJ ++ d1))))))))))) [] s))
    (back3 : ∀ t, run r3 t (run (GateMirror.forward b3) []
      (run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ (d0 ++ (bJ ++ d1))))))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ (d0 ++ (bJ ++ d1))))))))))) [] s) :
    (∀ m, run (GateMirror.forward a0 ++ f0 ++ GateMirror.forward a1 ++ f1 ++ GateMirror.forward c0 ++ fR ++
        GateMirror.forward c1 ++ f2 ++ GateMirror.forward d0 ++ fJ ++ GateMirror.forward d1 ++ f3 ++ GateMirror.forward e) m s =
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ (d0 ++ (bJ ++ (d1 ++ (b3 ++ e))))))))))))) m s) ∧
    (∀ m n, run (GateMirror.inverse e ++ r3 ++ GateMirror.inverse d1 ++ rJ ++ GateMirror.inverse d0 ++ r2 ++
        GateMirror.inverse c1 ++ rR ++ GateMirror.inverse c0 ++ r1 ++ GateMirror.inverse a1 ++ r0 ++ GateMirror.inverse a0) n
      (run (GateMirror.forward a0 ++ f0 ++ GateMirror.forward a1 ++ f1 ++ GateMirror.forward c0 ++ fR ++
        GateMirror.forward c1 ++ f2 ++ GateMirror.forward d0 ++ fJ ++ GateMirror.forward d1 ++ f3 ++ GateMirror.forward e) m s) = s) := by
  simp only [run_nil_append] at same1 back1 sameR backR same2 back2 sameJ backJ same3 back3
  obtain ⟨va0, v1⟩ := v.parts
  obtain ⟨vb0, v2⟩ := v1.parts
  obtain ⟨va1, v3⟩ := v2.parts
  obtain ⟨vb1, v4⟩ := v3.parts
  obtain ⟨vc0, v5⟩ := v4.parts
  obtain ⟨vbR, v6⟩ := v5.parts
  obtain ⟨vc1, v7⟩ := v6.parts
  obtain ⟨vb2, v8⟩ := v7.parts
  obtain ⟨vd0, v9⟩ := v8.parts
  obtain ⟨vbJ, v10⟩ := v9.parts
  obtain ⟨vd1, v11⟩ := v10.parts
  obtain ⟨vb3, ve⟩ := v11.parts
  have emitted (m : List Bool) : run (GateMirror.forward a0 ++ f0 ++ GateMirror.forward a1 ++ f1 ++ GateMirror.forward c0 ++ fR ++
      GateMirror.forward c1 ++ f2 ++ GateMirror.forward d0 ++ fJ ++ GateMirror.forward d1 ++ f3 ++ GateMirror.forward e) m s =
      run (GateMirror.forward e) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward d1) []
        (run (GateMirror.forward bJ) [] (run (GateMirror.forward d0) []
        (run (GateMirror.forward b2) [] (run (GateMirror.forward c1) [] (run (GateMirror.forward bR) []
        (run (GateMirror.forward c0) [] (run (GateMirror.forward b1) []
          (run (GateMirror.forward a1) [] (run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s)))))))))))) := by
    simp only [run_append, run_take, va0.default_run, same0, va1.default_run, same1, vc0.default_run, sameR,
      vc1.default_run, same2, vd0.default_run, sameJ, vd1.default_run, same3]
    exact ve.default_run _
  have old (m : List Bool) :
      run (GateMirror.forward (a0 ++ (b0 ++ (a1 ++ (b1 ++ (c0 ++ (bR ++ (c1 ++ (b2 ++ (d0 ++ (bJ ++ (d1 ++ (b3 ++ e))))))))))))) m s =
      run (GateMirror.forward e) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward d1) []
        (run (GateMirror.forward bJ) [] (run (GateMirror.forward d0) []
        (run (GateMirror.forward b2) [] (run (GateMirror.forward c1) [] (run (GateMirror.forward bR) []
        (run (GateMirror.forward c0) [] (run (GateMirror.forward b1) []
          (run (GateMirror.forward a1) [] (run (GateMirror.forward b0) [] (run (GateMirror.forward a0) [] s)))))))))))) := by
    simp only [forward_app, run_append, va0.default_run, vb0.default_run, va1.default_run, vb1.default_run, vc0.default_run,
      vbR.default_run, vc1.default_run, vb2.default_run, vd0.default_run, vbJ.default_run, vd1.default_run, vb3.default_run]
    exact ve.default_run _
  refine ⟨fun m => (emitted m).trans (old m).symm, ?_⟩
  intro m n
  rw [emitted]
  have undoE (l : List Bool) := ve.undo_run [] l
  have undoD1 (l : List Bool) := vd1.undo_run [] l
  have undoD0 (l : List Bool) := vd0.undo_run [] l
  have undoC1 (l : List Bool) := vc1.undo_run [] l
  have undoC0 (l : List Bool) := vc0.undo_run [] l
  have undoA1 (l : List Bool) := va1.undo_run [] l
  simp only [run_append, run_take, undoE, back3, undoD1, backJ, undoD0, back2, undoC1, backR, undoC0, back1, undoA1, back0]
  exact va0.undo_run [] _

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.FlagCut6

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.FlagCut7
open Partial GateMirror LeaveJ7 LeaveSplice CRTBarrel.FlagCut
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem lowRest_1558 (s : Nat) (t : State) : (run (GateMirror.forward (Shadow7.lowRest s)) [] t).basis 1558 = false := by
  obtain ⟨X, hX⟩ : ∃ X, Shadow7.lowRest s =
      X ++ [.pop (Shadow7.b0P s - 1) 1557 1558, .cx (Shadow7.a0P s - 1) 1557, .x 1557] := ⟨_, rfl⟩
  rw [hX, run_nil_append]
  generalize run (GateMirror.forward X) [] t = u
  obtain ⟨ph, f⟩ := u
  simp [GateMirror.forward, front, GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, writeBit, Function.update_apply]

/-- `LeaveSplice.replace` with 8 replaced middles. -/
theorem replace8Rows (a0 b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 b6 a6 b7 a7 b8 a8 : List Gate) (f0 r0 f1 r1 f2 r2 f3 r3 f4 r4 fK rK f5 r5 f6 r6 f7 r7 f8 r8 : Program) (s : State)
    (v : Valid s (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8))))))))))))))))))
    (same0 : ∀ t, run f0 t s = run (GateMirror.forward a0) [] s)
    (back0 : ∀ t, run r0 t (run (GateMirror.forward a0) [] s) = s)
    (same1 : ∀ t, run f1 t (run (GateMirror.forward (a0)) [] s) =
      run (GateMirror.forward b1) [] (run (GateMirror.forward (a0)) [] s))
    (back1 : ∀ t, run r1 t (run (GateMirror.forward b1) [] (run (GateMirror.forward (a0)) [] s)) =
      run (GateMirror.forward (a0)) [] s)
    (same2 : ∀ t, run f2 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1)))) [] s) =
      run (GateMirror.forward b2) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1)))) [] s))
    (back2 : ∀ t, run r2 t (run (GateMirror.forward b2) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1)))) [] s)) =
      run (GateMirror.forward (a0 ++ (b1 ++ (a1)))) [] s)
    (same3 : ∀ t, run f3 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2)))))) [] s) =
      run (GateMirror.forward b3) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2)))))) [] s))
    (back3 : ∀ t, run r3 t (run (GateMirror.forward b3) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2)))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2)))))) [] s)
    (same4 : ∀ t, run f4 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3)))))))) [] s) =
      run (GateMirror.forward b4) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3)))))))) [] s))
    (back4 : ∀ t, run r4 t (run (GateMirror.forward b4) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3)))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3)))))))) [] s)
    (sameK : ∀ t, run fK t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4))))))))) [] s) =
      run (GateMirror.forward a4) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4))))))))) [] s))
    (backK : ∀ t, run rK t (run (GateMirror.forward a4) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4))))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4))))))))) [] s)
    (same5 : ∀ t, run f5 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4)))))))))) [] s) =
      run (GateMirror.forward b5) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4)))))))))) [] s))
    (back5 : ∀ t, run r5 t (run (GateMirror.forward b5) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4)))))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4)))))))))) [] s)
    (same6 : ∀ t, run f6 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5)))))))))))) [] s) =
      run (GateMirror.forward b6) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5)))))))))))) [] s))
    (back6 : ∀ t, run r6 t (run (GateMirror.forward b6) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5)))))))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5)))))))))))) [] s)
    (same7 : ∀ t, run f7 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6)))))))))))))) [] s) =
      run (GateMirror.forward b7) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6)))))))))))))) [] s))
    (back7 : ∀ t, run r7 t (run (GateMirror.forward b7) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6)))))))))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6)))))))))))))) [] s)
    (same8 : ∀ t, run f8 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7)))))))))))))))) [] s) =
      run (GateMirror.forward b8) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7)))))))))))))))) [] s))
    (back8 : ∀ t, run r8 t (run (GateMirror.forward b8) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7)))))))))))))))) [] s)) =
      run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7)))))))))))))))) [] s)
    : (∀ m, run (f0 ++ f1 ++ GateMirror.forward a1 ++ f2 ++ GateMirror.forward a2 ++ f3 ++ GateMirror.forward a3 ++ f4 ++ fK ++ f5 ++ GateMirror.forward a5 ++ f6 ++ GateMirror.forward a6 ++ f7 ++ GateMirror.forward a7 ++ f8 ++ GateMirror.forward a8) m s =
      run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8)))))))))))))))))) m s) ∧
    (∀ m n, run (GateMirror.inverse a8 ++ r8 ++ GateMirror.inverse a7 ++ r7 ++ GateMirror.inverse a6 ++ r6 ++ GateMirror.inverse a5 ++ r5 ++ rK ++ r4 ++ GateMirror.inverse a3 ++ r3 ++ GateMirror.inverse a2 ++ r2 ++ GateMirror.inverse a1 ++ r1 ++ r0) n
      (run (f0 ++ f1 ++ GateMirror.forward a1 ++ f2 ++ GateMirror.forward a2 ++ f3 ++ GateMirror.forward a3 ++ f4 ++ fK ++ f5 ++ GateMirror.forward a5 ++ f6 ++ GateMirror.forward a6 ++ f7 ++ GateMirror.forward a7 ++ f8 ++ GateMirror.forward a8) m s) = s) := by
  simp only [run_nil_append] at same2 back2 same3 back3 same4 back4 sameK backK same5 back5 same6 back6 same7 back7 same8 back8
  obtain ⟨va0, w0⟩ := v.parts
  obtain ⟨vb1, w1⟩ := w0.parts
  obtain ⟨va1, w2⟩ := w1.parts
  obtain ⟨vb2, w3⟩ := w2.parts
  obtain ⟨va2, w4⟩ := w3.parts
  obtain ⟨vb3, w5⟩ := w4.parts
  obtain ⟨va3, w6⟩ := w5.parts
  obtain ⟨vb4, w7⟩ := w6.parts
  obtain ⟨va4, w8⟩ := w7.parts
  obtain ⟨vb5, w9⟩ := w8.parts
  obtain ⟨va5, w10⟩ := w9.parts
  obtain ⟨vb6, w11⟩ := w10.parts
  obtain ⟨va6, w12⟩ := w11.parts
  obtain ⟨vb7, w13⟩ := w12.parts
  obtain ⟨va7, w14⟩ := w13.parts
  obtain ⟨vb8, w15⟩ := w14.parts
  have va8 := w15
  have emitted (m : List Bool) : run (f0 ++ f1 ++ GateMirror.forward a1 ++ f2 ++ GateMirror.forward a2 ++ f3 ++ GateMirror.forward a3 ++ f4 ++ fK ++ f5 ++ GateMirror.forward a5 ++ f6 ++ GateMirror.forward a6 ++ f7 ++ GateMirror.forward a7 ++ f8 ++ GateMirror.forward a8) m s =
      (run (GateMirror.forward a8) [] (run (GateMirror.forward b8) [] (run (GateMirror.forward a7) [] (run (GateMirror.forward b7) [] (run (GateMirror.forward a6) [] (run (GateMirror.forward b6) [] (run (GateMirror.forward a5) [] (run (GateMirror.forward b5) [] (run (GateMirror.forward a4) [] (run (GateMirror.forward b4) [] (run (GateMirror.forward a3) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward a2) [] (run (GateMirror.forward b2) [] (run (GateMirror.forward a1) [] (run (GateMirror.forward b1) [] (run (GateMirror.forward a0) [] s))))))))))))))))) := by
    simp only [run_append, run_take, same0, same1, va1.default_run, same2, va2.default_run, same3, va3.default_run, same4, sameK, same5, va5.default_run, same6, va6.default_run, same7, va7.default_run, same8]
    exact va8.default_run _
  have old (m : List Bool) : run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8)))))))))))))))))) m s =
      (run (GateMirror.forward a8) [] (run (GateMirror.forward b8) [] (run (GateMirror.forward a7) [] (run (GateMirror.forward b7) [] (run (GateMirror.forward a6) [] (run (GateMirror.forward b6) [] (run (GateMirror.forward a5) [] (run (GateMirror.forward b5) [] (run (GateMirror.forward a4) [] (run (GateMirror.forward b4) [] (run (GateMirror.forward a3) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward a2) [] (run (GateMirror.forward b2) [] (run (GateMirror.forward a1) [] (run (GateMirror.forward b1) [] (run (GateMirror.forward a0) [] s))))))))))))))))) := by
    simp only [forward_app, run_append, va0.default_run, vb1.default_run, va1.default_run, vb2.default_run, va2.default_run, vb3.default_run, va3.default_run, vb4.default_run, va4.default_run, vb5.default_run, va5.default_run, vb6.default_run, va6.default_run, vb7.default_run, va7.default_run, vb8.default_run]
    exact va8.default_run _
  refine ⟨fun m => (emitted m).trans (old m).symm, ?_⟩
  intro m n
  rw [emitted]
  have undoA8 (l : List Bool) := va8.undo_run [] l
  have undoA7 (l : List Bool) := va7.undo_run [] l
  have undoA6 (l : List Bool) := va6.undo_run [] l
  have undoA5 (l : List Bool) := va5.undo_run [] l
  have undoA3 (l : List Bool) := va3.undo_run [] l
  have undoA2 (l : List Bool) := va2.undo_run [] l
  have undoA1 (l : List Bool) := va1.undo_run [] l
  simp only [run_append, run_take, undoA8, back8, undoA7, back7, undoA6, back6, undoA5, back5, backK, back4, undoA3, back3, undoA2, back2, undoA1, back1]
  exact back0 _


private theorem storeHead_targets : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    ((storeHead (start j)).drop 1).all (fun g => decide (target g ≠ 1558)) = true := by decide +kernel

/-- The store chain below level 0 targets the higher store cells and `1557`, never the carry-in `1558`. -/
theorem chainMid_targets (s : Nat) : ∀ g ∈ chainMid s, target g ≠ 1558 := by
  have hb : AllAT (fun _ => True) (fun q => q ≠ 1558)
      [GateMirror.Gate.cx (Shadow7.storeW s (Shadow7.liveW s - Shadow7.lowsP s + 1)) 1557, GateMirror.Gate.x 1557] :=
    allAT_cons (ok_cx (A := fun _ => True) (T := fun q => q ≠ 1558) trivial (by decide))
      (allAT_cons (ok_x (A := fun _ => True) (T := fun q => q ≠ 1558) (by decide)) allAT_nil)
  have h := allAT_chainG (A := fun _ => True) (T := fun q => q ≠ 1558) (Shadow7.storeW s)
    (fun i => if i = 0 then Shadow7.a0P s + Shadow7.lowsP s - 1 else Shadow7.bankW s (Shadow7.lowsP s + i - 1)) _ hb
    1 (Shadow7.liveW s - Shadow7.lowsP s)
    (fun k h1 h2 => ⟨trivial, fun hk => by
      simp only [Shadow7.storeW, Partial.storeW]; split_ifs <;> ((try unfold Wire at *); omega)⟩)
    (fun _ _ _ => trivial)
  intro g hg
  exact (h g hg).2

/-- After the low store and the store head, the chain's carry-in `1558` is 1. -/
theorem tailE0_1558 (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (t : State) :
    (run (GateMirror.forward (tailE0 (start j))) [] t).basis 1558 = true := by
  have hT := List.all_eq_true.mp (storeHead_targets j lo hi)
  have e : storeHead (start j) = [.x 1558] ++ (storeHead (start j)).drop 1 := rfl
  rw [tailE0, run_nil_append, e, run_nil_append]
  rw [keeps_of_targets _ _ (fun g hg => of_decide_eq_true (hT g hg))]
  have z := lowRest_1558 (start j) t
  generalize run (GateMirror.forward (Shadow7.lowRest (start j))) [] t = u at z ⊢
  obtain ⟨ph, f⟩ := u
  simp only at z
  simp [GateMirror.forward, front, run, writeBit, Function.update_apply, z]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.FlagCut7

namespace ECDSAAdd.Entrant.StairPacket.ScanRow16
open GateMirror MeasuredCodec5

def oldRow : List Gate := [.cx 1 2, .ccx 0 2 1, .cx 1 2]
def newRow : List Gate := [.cx 1 2, .cx 2 1, .cx 3 1, .pop 0 2 1, .cx 3 1, .cx 2 1, .cx 1 2]

private def packed (a b c d : Bool) := a.toNat + 2*b.toNat + 4*c.toNat + 8*d.toNat

private theorem packed_bits : ∀ a b c d : Bool, let x := packed a b c d
    x < 16 ∧ x.testBit 0 = a ∧ x.testBit 1 = b ∧ x.testBit 2 = c ∧ x.testBit 3 = d := by decide

private theorem forward_check : ∀ (x : Fin 16) (p m : Bool),
    (sim (GateMirror.forward oldRow) [] p x.val).2.testBit 2 = x.val.testBit 3 →
    sim (GateMirror.forward newRow) [m] p x.val = sim (GateMirror.forward oldRow) [] p x.val := by decide +kernel

private theorem return_check : ∀ (x : Fin 16) (p : Bool),
    (sim (GateMirror.forward oldRow) [] p x.val).2.testBit 2 = x.val.testBit 3 →
    sim (GateMirror.forward oldRow ++ GateMirror.inverse newRow) [] p x.val = (p,x.val) := by decide +kernel

private abbrev sites : Finset Wire := Finset.range 4
private theorem old_sites : wires (GateMirror.forward oldRow) ⊆ sites := by decide
private theorem new_sites : wires (GateMirror.forward newRow) ⊆ sites := by decide
private theorem return_sites : wires (GateMirror.forward oldRow ++ GateMirror.inverse newRow) ⊆ sites := by decide

theorem placed_pair (f : Wire → Wire) (inj : ∀ a ∈ sites, ∀ b ∈ sites, f a = f b → a=b)
    (s : State) (companion : (run (renameProgram f (GateMirror.forward oldRow)) [] s).basis (f 2) = s.basis (f 3)) :
    (∀ m, run (renameProgram f (GateMirror.forward newRow)) m s = run (renameProgram f (GateMirror.forward oldRow)) [] s) ∧
    (∀ n, run (renameProgram f (GateMirror.inverse newRow)) n (run (renameProgram f (GateMirror.forward oldRow)) [] s) = s) := by
  let x := packed (s.basis (f 0)) (s.basis (f 1)) (s.basis (f 2)) (s.basis (f 3))
  obtain ⟨lt,h0,h1,h2,h3⟩ := packed_bits (s.basis (f 0)) (s.basis (f 1)) (s.basis (f 2)) (s.basis (f 3))
  let t : State := ⟨s.phase, bitsOf x⟩
  have reads : ∀ q ∈ sites, t.basis q = s.basis (f q) := by
    intro q hq
    have hq' : q < 4 := Finset.mem_range.mp hq
    change x.testBit q = s.basis (f q)
    interval_cases q <;> assumption
  have physical := (run_rename_pool f sites inj _ old_sites [] t s rfl reads).2 2 (by decide)
  have allowed : (sim (GateMirror.forward oldRow) [] s.phase x).2.testBit 2 = x.testBit 3 := by
    have eq := physical.symm.trans (companion.trans (reads 3 (by decide)).symm)
    simpa only [t,run_sim,bitsOf] using eq
  constructor
  · intro m
    have trimmed : run (GateMirror.forward newRow) m t = run (GateMirror.forward newRow) [m.headD false] t := by cases m <;> rfl
    apply run_rename_eq_of_eq f sites inj _ _ new_sites old_sites m [] t s rfl reads
    rw [trimmed]
    simpa only [t,run_sim] using congrArg (fun y : Bool × Nat => State.mk y.1 (bitsOf y.2))
      (forward_check ⟨x,lt⟩ s.phase (m.headD false) allowed)
  · intro n
    have local_eq : run (GateMirror.forward oldRow ++ GateMirror.inverse newRow) n t = run [] [] t := by
      have trimmed : run (GateMirror.forward oldRow ++ GateMirror.inverse newRow) n t = run (GateMirror.forward oldRow ++ GateMirror.inverse newRow) [] t := rfl
      rw [trimmed]
      simpa only [t,run_sim,sim] using congrArg (fun y : Bool × Nat => State.mk y.1 (bitsOf y.2))
        (return_check ⟨x,lt⟩ s.phase allowed)
    have eq := run_rename_eq_of_eq f sites inj _ [] return_sites (by decide) n [] t s rfl reads local_eq
    change run (renameProgram f (GateMirror.forward oldRow) ++ renameProgram f (GateMirror.inverse newRow)) n s = s at eq
    rw [run_append] at eq
    exact eq

end ECDSAAdd.Entrant.StairPacket.ScanRow16

namespace ECDSAAdd.Entrant.StairPacket.ScanRow16
open Arithmetic GateMirror Partial
private theorem split_scan (s h : Nat) :
    Shadow7.fix0P s h = firstRows s h ++ (cell s h ++ (suffix s h ++ lastTwo h)) := rfl

private theorem lastTwo_zero (h : Nat) (t : State)
    (clean : (run (GateMirror.forward (lastTwo h)) [] t).basis (h+802) = false) :
    t.basis (h+802) = t.basis (h+1579) := by
  simp [lastTwo, GateMirror.forward, front, run, writeBit] at clean
  cases hb : t.basis (h+802) <;> cases hn : t.basis (h+1579) <;> simp_all

private theorem geometry : ∀ i : Fin 26, i.val ≤ 24 →
      let s := start i
      let h := Shadow7.sbP s
      (suffix s h).all (fun g => decide (target g ≠ h+802)) = true ∧
      (suffix s h).all (fun g => decide (target g ≠ h+1579)) = true ∧
      (cell s h).all (fun g => decide (target g ≠ h+1579)) = true := by decide +kernel

attribute [local irreducible] run GateMirror.forward Shadow7.fix0P firstRows cell suffix lastTwo

/-- The companion after the row-16 swap equals the sign before that swap. -/
theorem companion_eq_sign (j : Fin 26) (hj : j.val ≤ 24) (t : State) (u v : Nat) (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) t.basis)
    (fresh : t.basis (Shadow7.e0P (start j) + 5) = false)
    (small : u < 2^16 * 2^(Shadow7.sbP (start j))) :
    let s := start j
    let h := Shadow7.sbP s
    let before := run (GateMirror.forward (firstRows s h)) [] t
    (run (GateMirror.forward (cell s h)) [] before).basis (h+802) = before.basis (h+1579) := by
  let s := start j
  let h := Shadow7.sbP s
  have scan := ((LeaveJ7.inputScan_result j (Nat.zero_le _) hj t [] u v G sg ready fresh).2.2.1
    16 (by decide)).2
  have pos : Shadow7.b0P (start j) - 1 + 16 = h + 802 := by
    simp only [Shadow7.b0P, h, s]; omega
  have clean : (run (GateMirror.forward (Shadow7.fix0P s h)) [] t).basis (h+802) = false := by
    rw [← pos, scan]
    apply Nat.testBit_lt_two_pow
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (lt_of_le_of_lt (Nat.sub_le _ _) small)
  let before := run (GateMirror.forward (firstRows s h)) [] t
  let after := run (GateMirror.forward (cell s h)) [] before
  let tailState := run (GateMirror.forward (suffix s h)) [] after
  rw [split_scan, CRTBarrel.FlagCut.run_nil_append, CRTBarrel.FlagCut.run_nil_append,
    CRTBarrel.FlagCut.run_nil_append] at clean
  have tailEq := lastTwo_zero h tailState clean
  obtain ⟨clearB, clearN, cellN⟩ := geometry j hj
  have keeps (gs : List Gate) (q : Wire) (a : State)
      (safe : gs.all (fun g => decide (target g ≠ q)) = true) :
      (run (GateMirror.forward gs) [] a).basis q = a.basis q :=
    CRTBarrel.FlagCut.keeps_of_targets gs q
      (fun g hg => of_decide_eq_true ((List.all_eq_true.mp safe) g hg)) [] a
  exact (keeps _ _ after clearB).symm.trans
    (tailEq.trans ((keeps _ _ after clearN).trans (keeps _ _ before cellN)))

end ECDSAAdd.Entrant.StairPacket.ScanRow16

namespace ECDSAAdd.Entrant.StairPacket.ScanRow16
open Arithmetic GateMirror Partial
private theorem ports_injective : ∀ j : Fin 26, j.val ≤ 24 →
    ∀ a ∈ sites, ∀ b ∈ sites,
      port (start j) (Shadow7.sbP (start j)) a = port (start j) (Shadow7.sbP (start j)) b → a = b := by
  have finite : ∀ (j : Fin 26) (a b : Fin 4),
      port (start j) (Shadow7.sbP (start j)) a.val = port (start j) (Shadow7.sbP (start j)) b.val → a = b := by
    decide +kernel
  intro j _ a ha b hb eq
  exact congrArg Fin.val (finite j ⟨a,Finset.mem_range.mp ha⟩ ⟨b,Finset.mem_range.mp hb⟩ eq)

attribute [local irreducible] run firstRows cell shortCell headEnd

theorem head_pair {j : Fin 26} (hi : j.val ≤ 24) {t : State} {z : SkywalkNat.State} {g sg : Bool}
    (h : LeaveJ7.Admission.Inputs j t z g sg) (valid : CRTBarrel.LeaveSplice.Valid t (CRTBarrel.headA0 (start j))) :
    (∀ m, run (GateMirror.forward (headShort (start j))) m t = run (GateMirror.forward (CRTBarrel.headA0 (start j))) [] t) ∧
    (∀ n, run (inverse (headShort (start j))) n (run (GateMirror.forward (CRTBarrel.headA0 (start j))) [] t) = t) := by
  let s := start j
  let b := Shadow7.sbP s
  let before := run (GateMirror.forward (firstRows s b)) [] t
  have small := (LeaveShadowRails.inputRow15 b z h.farSmall).1
  have sign := companion_eq_sign j hi t _ _ _ _ h.ready h.fresh small
  have oldPlaced : renameProgram (port s b) (GateMirror.forward oldRow) = GateMirror.forward (cell s b) := by
    unfold cell; rfl
  have newPlaced : renameProgram (port s b) (GateMirror.forward newRow) = GateMirror.forward (shortCell s b) := by
    unfold shortCell; rfl
  have invPlaced : renameProgram (port s b) (inverse newRow) = inverse (shortCell s b) := by
    unfold shortCell; rfl
  have physical : (run (renameProgram (port s b) (GateMirror.forward oldRow)) [] before).basis (port s b 2) =
      before.basis (port s b 3) := by
    rw [oldPlaced]
    exact sign
  obtain ⟨fwd,rev⟩ := placed_pair (port s b) (ports_injective j hi) before physical
  rw [oldPlaced,newPlaced] at fwd
  rw [oldPlaced,invPlaced] at rev
  have part := valid
  rw [head_shape] at part
  obtain ⟨same,undo⟩ := CRTBarrel.LeaveSplice.replace (firstRows s b) (cell s b) (headEnd s b)
    (GateMirror.forward (shortCell s b)) (inverse (shortCell s b)) t part fwd rev
  have result (m : List Bool) : run (GateMirror.forward (headShort s)) m t = run (GateMirror.forward (CRTBarrel.headA0 s)) m t := by
    simpa only [headShort,head_shape,forward_app,List.append_assoc] using same m
  constructor
  · exact fun m => (result m).trans (valid.default_run m)
  · intro n
    rw [← result []]
    simpa only [headShort,forward_app,CRTBarrel.FlagCut.inv_app,List.append_assoc] using undo [] n

end ECDSAAdd.Entrant.StairPacket.ScanRow16


namespace ECDSAAdd.Entrant.StairPacket.KeptParity
open Arithmetic GateMirror

set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

/-- The digit is active on one of the first eight rows when it is set. -/
def relation (v : BasisState) : Prop :=
  (v 1 && v 0) = (v 0 ^^ (v 2 && v 0) ^^ (v 3 && v 0) ^^ (v 4 && v 0) ^^ (v 5 && v 0) ^^ (v 6 && v 0) ^^ (v 7 && v 0) ^^ (v 8 && v 0))

private def tag (k : LeaveSelector.Mode) (i : Nat) := LeaveSelector.enabled k && decide (i = LeaveSelector.key k)
private def digitBit (k : LeaveSelector.Mode) (cross sign : Bool) :=
  ((LeaveSelector.enabled k ^^ cross) ^^ sign) ^^ (cross && sign)

private theorem finiteModes : ∀ (k : LeaveSelector.Mode) (cross sign : Bool),
    (k.val = 0 → cross = false ∧ sign = false) → (8 ≤ LeaveSelector.key k → sign = true) →
    let digit := digitBit k cross sign
    (tag k 0 && digit) = (digit ^^ (tag k 1 && digit) ^^ (tag k 2 && digit) ^^ (tag k 3 && digit) ^^ (tag k 4 && digit) ^^ (tag k 5 && digit) ^^ (tag k 6 && digit) ^^ (tag k 7 && digit)) := by decide +kernel

theorem relationOfMode (v : BasisState) (k : LeaveSelector.Mode) (cross sign : Bool)
    (inactive : k.val = 0 → cross = false ∧ sign = false) (high : 8 ≤ LeaveSelector.key k → sign = true)
    (digit : v 0 = digitBit k cross sign) (ports : ∀ i, i < 8 → v (i+1) = tag k i) : relation v := by
  unfold relation
  rw [ports 0 (by decide), ports 1 (by decide), ports 2 (by decide), ports 3 (by decide), ports 4 (by decide), ports 5 (by decide), ports 6 (by decide), ports 7 (by decide), digit]
  exact finiteModes k cross sign inactive high

private def shifted (s : State) (x : Bool) : State :=
  ⟨s.phase, writeBit s.basis 9 (s.basis 9 ^^ x)⟩

private def bareStep (h y : Wire) (s : State) : State :=
  ⟨s.phase, writeBit s.basis y (s.basis y ^^ (s.basis h && s.basis 0))⟩

private theorem twice (a b c d : Bool) : (((a ^^ b) ^^ c) ^^ (c ^^ d)) = (a ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem liftedStep (h y : Wire) (hn : h ≠ 9) (yn : y ≠ 9) (s : State) (x : Bool)
    (tail : Program) (m : List Bool) :
    run (.CX y 9 :: .CCX h 0 y :: .CX y 9 :: tail) m (shifted s x) =
      run tail m (shifted (bareStep h y s) (x ^^ (s.basis h && s.basis 0))) := by
  simp only [run]
  apply congrArg (run tail m)
  apply State.extensionality
  · rfl
  funext q
  by_cases endBit : q = 9
  · subst q
    simp [shifted, bareStep, writeBit, Function.update_of_ne, hn, yn, Ne.symm yn, twice]
  · by_cases dataBit : q = y
    · subst q
      simp [shifted, bareStep, writeBit, Function.update_of_ne, hn, yn, Ne.symm yn]
    · simp [shifted, bareStep, writeBit, Function.update_of_ne, endBit, dataBit]

private def bare (i : Nat) (n : Nat) : Program :=
  match n with
  | 0 => []
  | n+1 => .CCX (i+2) 0 (i+10) :: bare (i+1) n

private def lifted (i : Nat) (n : Nat) : Program :=
  match n with
  | 0 => []
  | n+1 => .CX (i+10) 9 :: .CCX (i+2) 0 (i+10) :: .CX (i+10) 9 :: lifted (i+1) n

private def parity (v : BasisState) (i n : Nat) (x : Bool) : Bool :=
  match n with
  | 0 => x
  | n+1 => parity v (i+1) n (x ^^ (v (i+2) && v 0))

private theorem ladder (v : BasisState) (m : List Bool) (i n : Nat) (bound : i+n ≤ 7)
    (s : State) (keep : ∀ q : Nat, q ≤ 8 → s.basis q = v q) (x : Bool) :
    run (lifted i n) m (shifted s x) = shifted (run (bare i n) m s) (parity v i n x) := by
  induction n generalizing i s x with
  | zero => rfl
  | succ n ih =>
    have hn : (i+2 : Wire) ≠ 9 := by unfold Wire at *; omega
    have yn : (i+10 : Wire) ≠ 9 := by unfold Wire at *; omega
    simp only [lifted, bare, parity, liftedStep _ _ hn yn, run]
    rw [← keep (i+2) (by omega), ← keep 0 (by decide)]
    apply ih (i+1) (by omega) (bareStep (i+2) (i+10) s)
    intro q hq
    have ne : (q : Wire) ≠ i+10 := by unfold Wire at *; omega
    simpa [bareStep, writeBit, Function.update_of_ne ne] using keep q hq

private theorem parity_left (v : BasisState) (i n : Nat) (a b : Bool) :
    parity v i n (a ^^ b) = (a ^^ parity v i n b) := by
  induction n generalizing i b with
  | zero => rfl
  | succ n ih => simp only [parity, Bool.xor_assoc, ih]

private theorem shift_shift (s : State) (a b : Bool) : shifted (shifted s a) b = shifted s (a ^^ b) := by
  apply State.extensionality
  · rfl
  funext q
  by_cases h : q = 9
  · subst q; simp [shifted, writeBit, Bool.xor_assoc]
  · simp [shifted, writeBit, Function.update_of_ne h]

private theorem shift_zero (s : State) : shifted s false = s := by
  apply State.extensionality
  · rfl
  funext q
  by_cases h : q = 9
  · subst q; simp [shifted, writeBit]
  · simp [shifted, writeBit, Function.update_of_ne h]

theorem same (s : State) (m : List Bool) (mode : relation s.basis) :
    run (GateMirror.forward replacement) m s = run (GateMirror.forward old) m s := by
  have newProgram : GateMirror.forward replacement = .CX 0 9 :: lifted 0 7 := rfl
  have oldProgram : GateMirror.forward old = .CCX 1 0 9 :: bare 0 7 := rfl
  rw [newProgram, oldProgram]
  let top := s.basis 1 && s.basis 0
  let t := shifted s top
  change run (lifted 0 7) m (shifted s (s.basis 0)) = run (bare 0 7) m t
  have prepared : shifted t (top ^^ s.basis 0) = shifted s (s.basis 0) := by
    rw [show shifted t _ = shifted s (top ^^ (top ^^ s.basis 0)) from shift_shift _ _ _]
    congr 1
    cases top <;> cases s.basis 0 <;> rfl
  have keep (q : Nat) (hq : q ≤ 8) : t.basis q = s.basis q := by
    have ne : (q : Wire) ≠ 9 := by unfold Wire at *; omega
    simp [t, shifted, writeBit, Function.update_of_ne ne]
  have parityEq : parity s.basis 0 7 (s.basis 0) = top := mode.symm
  rw [← prepared, ladder s.basis m 0 7 (by decide) t keep, parity_left, parityEq, Bool.xor_self, shift_zero]

end ECDSAAdd.Entrant.StairPacket.KeptParity

namespace ECDSAAdd.Entrant.StairPacket.KeptParity
open Arithmetic GateMirror Partial
private theorem geometry : ∀ (j : Fin 26) (a b : Fin 17), port (start j) a = port (start j) b → a = b := by
  decide +kernel

set_option maxRecDepth 16000 in
theorem placed_pair (j : Fin 26) (s : State) (h : relation (fun q => s.basis (port (start j) q))) :
    (∀ m, run (GateMirror.forward (placed (start j))) m s = run (GateMirror.forward (Shadow7.moveKept (start j))) [] s) ∧
    (∀ n, run (inverse (placed (start j))) n (run (GateMirror.forward (Shadow7.moveKept (start j))) [] s) = s) := by
  let f := port (start j)
  let t : State := ⟨s.phase, fun q => s.basis (f q)⟩
  have inj (a : Wire) (ha : a ∈ Finset.range 17) (b : Wire) (hb : b ∈ Finset.range 17)
      (eq : f a = f b) : a = b :=
    congrArg Fin.val (geometry j ⟨a, Finset.mem_range.mp ha⟩ ⟨b, Finset.mem_range.mp hb⟩ eq)
  have sameF (m : List Bool) : run (GateMirror.forward (placed (start j))) m s = run (GateMirror.forward (Shadow7.moveKept (start j))) [] s := by
    have eq : run (GateMirror.forward replacement) m t = run (GateMirror.forward old) [] t :=
      (same t m h).trans (run_take (GateMirror.forward old) m t).symm
    have boundedNew : wires (GateMirror.forward replacement) ⊆ Finset.range 17 := by decide
    have boundedOld : wires (GateMirror.forward old) ⊆ Finset.range 17 := by decide
    exact run_rename_eq_of_eq f (Finset.range 17) inj _ _ boundedNew boundedOld m [] t s rfl (fun _ _ => rfl) eq
  refine ⟨sameF, ?_⟩
  intro n
  rw [← sameF []]
  have valid : CRTBarrel.LeaveSplice.Valid s (placed (start j)) := by
    refine ⟨List.all_eq_true.mp (physical j), ?_, ready_plain _ (by rfl) _⟩
    repeat' constructor
  exact valid.undo_run [] n
end ECDSAAdd.Entrant.StairPacket.KeptParity

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission
open Arithmetic Partial GateMirror LeaveSelector KeptParity
def movedKeptPrefix (s : Nat) : List Gate :=
  Shadow7.moveA s ++ (rowGates (Shadow7.e0P s + 6) (Shadow7.moveRows s) ++ Shadow7.moveB s)

theorem Inputs.movedRelation {j : Fin 26} (lo : 0 ≤ j.val) (hi : j.val ≤ 24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : Inputs j s z g sg) (o : List Bool) :
    relation (fun i => (run (GateMirror.forward (movedKeptPrefix (start j))) o s).basis (port (start j) i)) := by
  obtain ⟨w1,w2⟩ := start_win7 j lo hi
  obtain ⟨k,c,sgn,inactive,high,digit,tags⟩ := h.keptState lo hi o
  have hot := h.hot lo hi o
  have moved := Shadow7.prefix_rows w1 w2 s o _ hot.1 hot.2
  have cl := Shadow7.cell_lt w1 w2
  have off (q : Wire) (hq : 1556 ≤ q) : ∀ r ∈ Shadow7.moveRows (start j), q ≠ r.2 := by
    intro r hr
    obtain ⟨i, bound, rfl⟩ := Shadow7.mem_moveRows hr
    dsimp only
    unfold Wire at *
    omega
  have unchanged (q : Wire) (hq : 1556 ≤ q) :
      (run (GateMirror.forward (movedKeptPrefix (start j))) o s).basis q =
      (run (GateMirror.forward (Shadow7.moveA (start j) ++ (Shadow7.moveMux (start j) ++ Shadow7.moveB (start j)))) o s).basis q := by
    rw [movedKeptPrefix, forward_app, forward_app, rowGates_forward, moved, Shadow7.clrAll_frame _ _ _ _ (off q hq)]
  apply relationOfMode _ k c sgn inactive high
  · exact (unchanged 1613 (by decide)).trans digit
  · intro i hi8
    have small : (i : Nat) < 8 := hi8
    have lim : (i : Nat) < 16 := Nat.lt_trans small (by decide)
    have hit := tags (⟨i, lim⟩ : Fin 16)
    have bound := tags_range' _ (tags_mem i lim)
    simpa only [port, if_pos small] using (unchanged _ bound.1).trans hit
end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission

namespace ECDSAAdd.Entrant.StairPacket.KeptParity
open GateMirror CRTBarrel
theorem frontShape (b : Nat) : (before b ++ Shadow7.leaveBarrel b) ++ Shadow7.fix8P b (Shadow7.sbP b) =
    LeaveJ7.Admission.movedKeptPrefix b := by
  rw [LeaveCut.before_shape]
  simp only [LeaveCut.head, LeaveCut.selectorTail, LeaveJ7.Admission.movedKeptPrefix, Shadow7.moveB, List.append_assoc]
end ECDSAAdd.Entrant.StairPacket.KeptParity

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission
open Partial GateMirror CRTBarrel KeptParity
theorem Inputs.keptTailPair {j : Fin 26} (lo : 0 ≤ j.val) (hi : j.val ≤ 24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : Inputs j s z g sg) :
    let b := start j
    let t := run (GateMirror.forward (CRTBarrel.before b ++ Shadow7.leaveBarrel b)) [] s
    (∀ m, run (GateMirror.forward (newTail b)) m t = run (GateMirror.forward (tailD0 b)) [] t) ∧
    (∀ n, run (inverse (newTail b)) n (run (GateMirror.forward (tailD0 b)) [] t) = t) := by
  let b := start j
  let t := run (GateMirror.forward (CRTBarrel.before b ++ Shadow7.leaveBarrel b)) [] s
  have full := LeaveSplice.moved_valid lo hi h
  rw [LeaveCut.move_shape, CRTWindow.after_split, CRTWindow.tailD_cut] at full
  have valid : LeaveSplice.Valid t (tailD0 b) := by
    dsimp only [t]
    rw [FlagCut.run_nil_append]
    exact full.parts.2.parts.2.parts.1.parts.1
  have key := placed_pair j _ (h.movedRelation lo hi [])
  rw [← frontShape, FlagCut.run_nil_append] at key
  obtain ⟨fwd,rev⟩ := LeaveSplice.replace (Shadow7.fix8P b (Shadow7.sbP b)) (Shadow7.moveKept b)
    (wordPre 1614 (colsC b)) (GateMirror.forward (placed b)) (inverse (placed b)) t valid key.1 key.2
  have f (m : List Bool) : run (GateMirror.forward (newTail b)) m t = run (GateMirror.forward (tailD0 b)) [] t := by
    apply Eq.trans _ (valid.default_run m)
    simpa only [newTail,forward_app,List.append_assoc] using fwd m
  refine ⟨f, ?_⟩
  intro n
  change run (inverse (newTail b)) n (run (GateMirror.forward (tailD0 b)) [] t) = t
  rw [← f []]
  simpa only [newTail,forward_app,FlagCut.inv_app,List.append_assoc] using rev [] n
end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission
open Partial GateMirror CRTBarrel

/-- Forward equality and inverse restoration for the actual moved leave, including its
measurement offsets. The two tapes are independent. -/
theorem Inputs.crt_pair20 {j : Fin 26} (lo : 0≤j.val) (hi : j.val≤24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : Inputs j s z g sg) :
    (∀ m, run (CRTBarrel.leave j) m s = run (Shadow7.leaveP j) m s) ∧
    (∀ m n, run (CRTBarrel.unleave j) n (run (CRTBarrel.leave j) m s) = s) := by
  have l16 := CRTWindow.low16_all j lo hi
  have v := LeaveSplice.moved_valid lo (by omega) h
  rw [LeaveCut.move_shape] at v
  obtain ⟨same, back⟩ := LeaveCut.barrel_pair j lo (by omega) _ (LeaveCut.input lo (by omega) h)
  rw [FlagCut5.before_split5] at v same back
  rw [CRTWindow.after_split, CRTWindow.tailD_cut, l16, CRTWindow.tailE_cut] at v
  simp only [List.append_assoc] at v
  have imp0 : s.basis (Shadow7.sbP (start j) + 1578) = true → s.basis (Shadow7.sbP (start j) + 1577) = true := by
    rw [← FlagCut.e0P_four, ← FlagCut.e0P_three, h.side, h.far]
    intro hs
    exact ((Bool.and_eq_true _ _).mp hs).1
  have hA := List.all_eq_true.mp (FlagCut.headA_targets j lo (by omega))
  rw [CRTWindow.headA_cut] at hA
  have k3 := FlagCut.keeps_of_targets (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j)))) (Shadow7.sbP (start j) + 1577)
    (fun g hg => (of_decide_eq_true (hA g hg)).1) [] s
  have k4 := FlagCut.keeps_of_targets (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j)))) (Shadow7.sbP (start j) + 1578)
    (fun g hg => (of_decide_eq_true (hA g hg)).2) [] s
  have imp1 : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j))))) [] s).basis (Shadow7.sbP (start j) + 1578) = true →
      (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j))))) [] s).basis (Shadow7.sbP (start j) + 1577) = true := by
    rw [k3, k4]; exact imp0
  have far_ne : Shadow7.sbP (start j) + 1578 ≠ 1559 := by omega
  have v' : LeaveSplice.Valid s ((headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j)))) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC (start j) ++
      (Shadow7.leaveBarrel (start j) ++ (tailD (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ tailE (start j))))))) := by
    rw [CRTWindow.headC_cut, CRTWindow.tailD_cut, l16, CRTWindow.tailE_cut]
    simpa only [List.append_assoc] using v
  obtain ⟨_, v1⟩ := v'.parts
  obtain ⟨vb1, _⟩ := v1.parts
  have fresh := vb1.ready.1
  simp only [GateMirror.Fresh] at fresh
  have kM (q : Wire) (hq : q = 1559 ∨ q = Shadow7.e0P (start j) + 4) (t : State) :
      (run (GateMirror.forward (headC (start j) ++ (Shadow7.leaveBarrel (start j) ++ tailD (start j)))) [] t).basis q = t.basis q := by
    apply FlagCut.keeps_of_targets
    intro g hg
    have := FlagCut.mid_targets j lo hi g hg
    rcases hq with rfl | rfl
    · exact this.1
    · exact this.2
  have re : headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j))))))))))) = (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j)))) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC (start j) ++ (Shadow7.leaveBarrel (start j) ++ tailD (start j)))) := by
    rw [CRTWindow.headC_cut, CRTWindow.tailD_cut, l16]; simp only [List.append_assoc]
  have hv3 : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j))))))))))))) [] s).basis 1559 =
      (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j))))))))))))) [] s).basis (Shadow7.e0P (start j) + 4) := by
    rw [re, FlagCut.run_nil_append, FlagCut.run_nil_append, kM 1559 (Or.inl rfl), kM _ (Or.inr rfl), FlagCut.e0P_four]
    exact FlagCut.make_flag _ _ _ _ fresh far_ne imp1
  have ne4 : Shadow7.e0P (start j) + 4 ≠ 1559 := by unfold Shadow7.e0P; omega
  have hv0 := FlagCut4.row17_value lo hi h
  have ha0 : start j + 30 ≠ start j + Shadow7.sbP (start j) + 48 := by omega
  have hb0 : Shadow7.sbP (start j) + 803 ≠ start j + Shadow7.sbP (start j) + 48 := by
    have := (start_win7 j lo (by omega)).2; unfold start at *; omega
  have hP := List.all_eq_true.mp (FlagCut5.pre5_targets j lo hi)
  have zero6 : s.basis (Shadow7.e0P (start j) + 6) = false := h.zero _ (by simp [LeaveJ7.watched])
  have hyR := (FlagCut.keeps_of_targets _ (Shadow7.e0P (start j) + 6) (fun g hg => of_decide_eq_true (hP g hg)) [] s).trans zero6
  have win := start_win7 j lo hi
  have rw7 := Shadow7.rail_win win.1 win.2
  have t0 : Partial.tagsP.getD 0 0 = 1576 := rfl
  have hxy : Shadow7.a0P (start j) + 0 ≠ Shadow7.e0P (start j) + 6 := by
    unfold Shadow7.a0P Shadow7.e0P at *; ((try unfold Wire at *); omega)
  have htx : Partial.tagsP.getD 0 0 ≠ Shadow7.a0P (start j) + 0 := by
    rw [t0]; unfold Shadow7.a0P at *; ((try unfold Wire at *); omega)
  have hty : Partial.tagsP.getD 0 0 ≠ Shadow7.e0P (start j) + 6 := by
    rw [t0]; unfold Shadow7.e0P at *; ((try unfold Wire at *); omega)
  have top : (run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s).basis
      (Shadow7.a0P (start j) + 16) = false := by
    have scan := LeaveJ7.inputScan_result j lo hi s [] _ _ _ _ h.ready h.fresh
    have row := (scan.2.2.1 17 (by decide)).1
    have tight := LeaveShadowRails.inputTight17 (Shadow7.sbP (start j)) z h.farSmall
    rw [Nat.testBit_lt_two_pow tight] at row
    have idx : Shadow7.a0P (start j) - 1 + 17 = Shadow7.a0P (start j) + 16 := by unfold Shadow7.a0P; omega
    rw [idx] at row
    exact row
  have hL := List.all_eq_true.mp (FlagCut6.lit_targets16 j lo hi)
  have eqJ : headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j))))))))) = Shadow7.fix0P (start j) (Shadow7.sbP (start j)) ++
      ((Partial.leaveFix1 (start j) (Shadow7.sbP (start j)) ++ Shadow7.fix2P (start j) (Shadow7.sbP (start j)) ++
        [.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ headC0 (start j) ++ [.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (rowGates (Shadow7.e0P (start j) + 6) ((Shadow7.moveRows (start j)).drop 1) ++
        (Partial.leaveFix5 (start j) (Shadow7.sbP (start j))).drop 43)) ++
      (Shadow7.leaveAdjust (start j) ++ (Shadow7.leaveBarrel (start j) ++ tailD0 (start j)))) := by
    have e := CRTWindow.fix0P_cut (start j) (Shadow7.sbP (start j))
    simp only [headA0, headA1, headC1]
    conv_rhs => rw [e]
    simp only [List.append_assoc]
  have hJ : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j))))))))))) [] s).basis (Shadow7.a0P (start j) + 16) = false := by
    rw [eqJ, FlagCut.run_nil_append]
    refine (FlagCut.keeps_of_targets _ _ (fun g hg => ?_) [] _).trans top
    rcases List.mem_append.mp hg with h1 | h1
    · exact of_decide_eq_true (hL g (List.mem_append_left _ h1))
    · rcases List.mem_append.mp h1 with h2 | h2
      · exact FlagCut6.adjust_targets16 win.1 win.2 g h2
      · rcases List.mem_append.mp h2 with h3 | h3
        · exact FlagCut6.barrel_targets16 win.1 win.2 g h3
        · exact of_decide_eq_true (hL g (List.mem_append_right _ h3))
  have hne16 : Shadow7.a0P (start j) + 16 ≠ Shadow7.bankW (start j) 16 := by
    have bc := Shadow7.bank_cases (i := 16) win.1 win.2 (by unfold Shadow7.wpP; omega)
    unfold Shadow7.a0P Shadow7.e0P at *; ((try unfold Wire at *); omega)
  -- the store chain's carry-in 1558 is 1 at its level-0 make and pop
  have eq7 : headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j))))))))))))) = (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559])))))))))))) ++ tailE0 (start j) := by simp only [List.append_assoc]
  have h1558M : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j))))))))))))))) [] s).basis 1558 = true := by
    rw [eq7, FlagCut.run_nil_append]; exact FlagCut7.tailE0_1558 j lo hi _
  have eq8 : headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j))))))))))))))) = (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j)))))))))))))) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ chainMid (start j)) := by simp only [List.append_assoc]
  have h1558P : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j))))))))))))))))) [] s).basis 1558 = true := by
    rw [eq8, FlagCut.run_nil_append, FlagCut.run_nil_append,
      FlagCut.keeps_of_targets _ _ (fun g hg => FlagCut7.chainMid_targets _ g hg)]
    rw [FlagCut.keeps_of_targets [.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] 1558 (fun g hg => by
      simp only [List.mem_singleton] at hg; subst hg; simp [GateMirror.target])]
    exact h1558M
  have v8 : LeaveSplice.Valid s ((headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j)))))))))))))))) ++ ([.pop 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ tailE1 (start j))) := by
    simpa only [List.append_assoc] using v
  obtain ⟨_, w8⟩ := v8.parts
  obtain ⟨vb8, _⟩ := w8.parts
  have val8 := vb8.prepared.1
  simp only [GateMirror.ValueOK] at val8
  have hv8 : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j))))))))))))))))) [] s).basis 1559 = (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j))))))))))))))))) [] s).basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) := by
    rw [val8, h1558P, Bool.true_and]
  have imp7 : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j))))))))))))))) [] s).basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) = true →
      (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j))))))))))))))) [] s).basis 1558 = true := fun _ => h1558M
  have topne : (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) ≠ 1559 := by
    unfold Shadow7.a0P at *; ((try unfold Wire at *); omega)
  have head := ScanRow16.head_pair hi h v8.parts.1.parts.1
  have tail := h.keptTailPair lo hi
  dsimp only at tail
  rw [FlagCut5.before_split5] at tail
  simp only [List.append_assoc] at tail
  obtain ⟨f, r⟩ := FlagCut7.replace8Rows (headA0 (start j)) [.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] (headA1 (start j)) [.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] (headC0 (start j)) [.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] (headC1 (start j)) (Shadow7.leaveBarrel (start j)) (tailD0 (start j)) (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16)) (tailD1 (start j)) [.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] (tailE0 (start j))
    [.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] (chainMid (start j)) [.pop 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] (tailE1 (start j))
    (GateMirror.forward (ScanRow16.headShort (start j))) (inverse (ScanRow16.headShort (start j)))
    [GateMirror.erase (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)]
    [.CCX (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)]
    [.CX (Shadow7.sbP (start j) + 1578) 1559] [.CX (Shadow7.sbP (start j) + 1578) 1559]
    [.CCX (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6),
      .CX (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0)]
    [.CX (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0),
      GateMirror.erase (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)]
    (barrel (start j) false) (barrel (start j) true)
    (GateMirror.forward (KeptParity.newTail (start j))) (inverse (KeptParity.newTail (start j))) [] []
    [.CX (Shadow7.e0P (start j) + 4) 1559] [.CX (Shadow7.e0P (start j) + 4) 1559]
    [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] s v
    head.1 head.2
    (fun t => FlagCut4.erase_ccx _ _ _ _ ha0 hb0 hv0 t)
    (fun t => FlagCut4.ccx_twice _ _ _ _ ha0 hb0 t)
    (fun t => FlagCut.ccx_cx (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559 _ imp1 t)
    (fun t => FlagCut.ccx_cx_back (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559 _ far_ne imp1 t)
    (fun t => FlagCut5.swap_make _ _ _ _ hxy htx hty hyR t)
    (fun t => FlagCut5.swap_make_back _ _ _ _ hxy htx hty hyR t)
    same back
    tail.1 tail.2
    (fun t => (FlagCut6.pair_high_id _ _ _ _ hne16 hJ).symm)
    (fun t => FlagCut6.pair_high_id _ _ _ _ hne16 hJ)
    (fun t => FlagCut.erase_cx (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559 _ hv3 t)
    (fun t => FlagCut.erase_cx_back (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559 _ ne4 hv3 t)
    (fun t => FlagCut.ccx_cx 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559 _ imp7 t)
    (fun t => FlagCut.ccx_cx_back 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559 _ topne imp7 t)
    (fun t => FlagCut.erase_cx 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559 _ hv8 t)
    (fun t => FlagCut.erase_cx_back 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559 _ topne hv8 t)
  have fprog : CRTBarrel.leave j = GateMirror.forward (ScanRow16.headShort (start j)) ++
      [GateMirror.erase (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++
      GateMirror.forward (headA1 (start j)) ++ [.CX (Shadow7.sbP (start j) + 1578) 1559] ++
      GateMirror.forward (headC0 (start j)) ++
      [.CCX (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6),
        .CX (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0)] ++
      GateMirror.forward (headC1 (start j)) ++ barrel (start j) false ++ GateMirror.forward (KeptParity.newTail (start j)) ++ [] ++ GateMirror.forward (tailD1 (start j)) ++
      [.CX (Shadow7.e0P (start j) + 4) 1559] ++ GateMirror.forward (tailE0 (start j)) ++ [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ GateMirror.forward (chainMid (start j)) ++
      [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ GateMirror.forward (tailE1 (start j)) := by
    simp only [CRTBarrel.leave, if_pos hi, beforeRow, beforeRowTail, KeptParity.afterRows, KeptParity.afterTail, forward_app, FlagCut.fwd_cons, front, List.append_assoc,
      List.cons_append, List.nil_append, List.append_nil]
  have uprog : CRTBarrel.unleave j = GateMirror.inverse (tailE1 (start j)) ++ [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ GateMirror.inverse (chainMid (start j)) ++
      [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ GateMirror.inverse (tailE0 (start j)) ++ [.CX (Shadow7.e0P (start j) + 4) 1559] ++
      GateMirror.inverse (tailD1 (start j)) ++ [] ++ GateMirror.inverse (KeptParity.newTail (start j)) ++ barrel (start j) true ++ GateMirror.inverse (headC1 (start j)) ++
      [.CX (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0),
        GateMirror.erase (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++
      GateMirror.inverse (headC0 (start j)) ++
      [.CX (Shadow7.sbP (start j) + 1578) 1559] ++ GateMirror.inverse (headA1 (start j)) ++
      [.CCX (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++
      GateMirror.inverse (ScanRow16.headShort (start j)) := by
    simp only [CRTBarrel.unleave, if_pos hi, beforeRow, beforeRowTail, KeptParity.afterRows, KeptParity.afterTail, FlagCut.inv_app, FlagCut.inv_cons, GateMirror.back,
      List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
  have shape : Shadow7.leaveMoveOps (start j) = headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j) ++ ([.pop 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (tailE1 (start j))))))))))))))))) := by
    rw [LeaveCut.move_shape, FlagCut5.before_split5, CRTWindow.after_split, CRTWindow.tailD_cut, l16, CRTWindow.tailE_cut]
    simp only [List.append_assoc]
  refine ⟨?_, ?_⟩
  · intro m
    rw [fprog, f m, ← shape]
    exact h.sameMove (Nat.zero_le _) (by omega) m
  · intro m n
    rw [uprog, fprog]
    exact r m n

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

private theorem avoidsThree {P : Wire → Prop} {whole a b c : Program}
    (parts : whole = a ++ b ++ c) (ha : ∀ w ∈ wires a, P w)
    (hb : ∀ w ∈ wires b, P w) (hc : ∀ w ∈ wires c, P w) {q : Wire}
    (out : ¬ P q) : q ∉ wires whole := by
  rw [parts, wires_append, wires_append]
  intro hit
  rcases Finset.mem_union.mp hit with ab | cc
  · rcases Finset.mem_union.mp ab with aa | bb
    · exact out (ha q aa)
    · exact out (hb q bb)
  · exact out (hc q cc)

/-- `LeaveJ7.leaveMove_keeps` for the CRT leave: a wire outside `Shadow7.leaveBox2` keeps its value. -/
theorem leave_keeps20 (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (q : Wire)
    (outside : ¬ Shadow7.leaveBox2 (start j) q) (m : List Bool) (s : State) :
    (run (CRTBarrel.leave j) m s).basis q = s.basis q := by
  apply run_preserves_outside
  have pieces : AllW (Shadow7.leaveBox2 (start j)) (Shadow7.leaveMoveOps (start j)) :=
    Shadow7.allW_leaveMove (start j) (Shadow7.leaveOps_box2 j (Nat.zero_le _) (by omega))
  rw [split_ops, allW_append_iff, allW_append_iff] at pieces
  have pre : ∀ w ∈ wires (GateMirror.forward (CRTBarrel.beforeRow (start j))), Shadow7.leaveBox2 (start j) w :=
    (allW_programs (P := Shadow7.leaveBox2 (start j)) (ops := CRTBarrel.beforeRow (start j)) (ScanRow16.beforeRow_allW _ (beforeC5_allW pieces.1))).1
  have post : ∀ w ∈ wires (GateMirror.forward (KeptParity.afterRows (start j))), Shadow7.leaveBox2 (start j) w :=
    (allW_programs (P := Shadow7.leaveBox2 (start j)) (ops := KeptParity.afterRows (start j)) (KeptParity.afterAllW j (afterPartC3_allW pieces.2.2))).1
  exact avoidsThree (leave_eq j lo hi).1 pre (barrel_box2 j lo hi false) post outside

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
  r=start j+15 ∨ ¬(r=start j+1044 ∨ (start j+16≤r ∧ r≤start j+Shadow7.sbP (start j)+35) ∨ (786≤r ∧ r≤Shadow7.sbP (start j)+804) ∨
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
    (Shadow7.sbP (start j)+1574≤q ∧ q≤Shadow7.sbP (start j)+1579) ∨ (Shadow7.sbP (start j)+805≤q ∧ q+3<Shadow7.sbP (start j)+805+Shadow7.wpP (start j)) := by
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
    q<Shadow7.sbP (start j)+805 ∨ (Shadow7.sbP (start j)+802+Shadow7.wpP (start j)≤q ∧ q<Shadow7.sbP (start j)+1574) ∨ Shadow7.sbP (start j)+1579<q := by
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
      have top : start j<369 ∨ Shadow7.wpP (start j)+Shadow7.sbP (start j)+start j≤497 := by
        by_cases h : start j<369
        · exact Or.inl h
        · right
          have r : railP (start j)=513-start j := by unfold railP; rw [if_neg (by omega),if_neg (by omega)]
          have wdef : Shadow7.wpP (start j)=railP (start j)-Shadow7.sbP (start j)-16 := rfl
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
    q≠Shadow7.sbP (start j)+1573 ∧ q≠Shadow7.sbP (start j)+804 := by
  decide +kernel
theorem top_geometry (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) {q : Wire} (hq : (q:Nat)+1=Shadow7.e0P (start j)) :
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
theorem top_first (j : Fin 26) (h21 : j.val≤24) {w : Nat} (lo : w+1=Shadow7.e0P (start j)) :
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
    ∀q:Wire,(q:Nat)+1=Shadow7.e0P (start j) →
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
      · have:=(topHead_all j (by omega) h21 q (List.mem_append_right _ h)).1; simp only [Shadow7.e0P,Wire] at *; omega
      · have:=(topHead_all j (by omega) h21 q (List.mem_append_left _ h)).1; simp only [Shadow7.e0P,Wire] at *; omega
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
    have b:(q:Nat)=Shadow7.sbP (start j)+804:=by simpa only [EnterJ7.parked,List.mem_singleton] using hq
    have fix:windowNet j q=q:=by
      simp only [windowNet,net,OB5.sig]
      split <;> simp only [Wire] at * <;> omega
    rw [fix]
    unfold Shadow7.MayTouch
    simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *
    simp only [Wire] at *
    omega
  · intro q hq hm
    have b:(q:Nat)=Shadow7.sbP (start j)+804:=by simpa only [EnterJ7.parked,List.mem_singleton] using hq
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
    have b:(q:Nat)=Shadow7.sbP (start j)+804:=by simpa only [EnterJ7.parked,List.mem_singleton] using hq
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

/-! `NativePack{s}.upperA/upper_clear`, generic: the A rail above the block's own ticks (`s+h+49 .. top`,
`top = min (s+30+R(s+14)) 529`, par-a's exact span top) is clean after the window head: the parked bank's A side is zeroed by the cut, the
wires above the bank (`s+R+16 ..`) are free in the stock domain. -/
theorem upperFree_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 → ∀k:Fin 20,
    start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val≤min (start j+30+railP (start j+14)) 529 →
    start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val∈(W.compactSkywalkSignPoolA base (start j)).released ∨
      (start j+274≤start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val ∧ start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val<786) := by
  decide +kernel
theorem upperHead_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 → ∀q∈ArchiveJ7.rawHead (prev j)++support j,
    q<start j+Shadow7.sbP (start j)+49 ∨ 1043<q := by
  decide +kernel

theorem upper_clear (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24) (d:Bool) (raw s:State) (x p:Nat)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (q:Nat) (low:start j+Shadow7.sbP (start j)+49≤q) (high:q≤min (start j+30+railP (start j+14)) 529) :
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
          exact ⟨q-(start j+Shadow7.sbP (start j)+34),by omega,by omega⟩
        · simp only [Wire] at *; omega
      have above:start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)≤q:=by
        by_contra lo
        simp only [Nat.not_le] at lo
        apply inPair
        simp only [EnterJ7.upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp]
        exact ⟨q-(start j+Shadow7.sbP (start j)+34),by omega,by omega⟩
      have rl:start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)=start j+railP (start j)+16 ∧
          (257≤railP (start j) ∨ start j+railP (start j)=513) ∧ railP (start j+14)≤railP (start j):=by
        have:=j.isLt; simp only [Shadow7.wpP,railP,Shadow7.sbP,start]; split_ifs <;> omega
      have k0:q-(start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j))<20:=by omega
      have free:=upperFree_all j (by omega) h21 ⟨_,k0⟩ (by simp only; omega)
      simp only [show start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+(q-(start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)))=q by omega] at free
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
    q<Shadow7.sbP (start j)+805 ∨ (Shadow7.sbP (start j)+802+Shadow7.wpP (start j)≤q ∧ q<Shadow7.sbP (start j)+1574) ∨ Shadow7.sbP (start j)+1579<q := by
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
    q≠Shadow7.sbP (start j)+1573 ∧ q≠Shadow7.sbP (start j)+804 := by
  decide +kernel
theorem topF_clean (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) (d:Bool) (x p:Nat) (raw v:State)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) v) :
    ∀q:Wire,(q:Nat)+1=Shadow7.e0P (start j) →
      (run (Shadow7.body j (program j d)) b (run (Shadow7.enterP j) a v)).basis q=false := by
  intro q hq
  obtain ⟨wn,same,touch,port,pend,hn,hf,hu,hi⟩:=NativeJ7.top_geometry j h1 h21 hq
  have notAdmin:q∉support j:=by
    intro h; have:=(topFHead_all j h1 h21 q h).1; simp only [Shadow7.e0P,Wire] at *; omega
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
    have b:(q:Nat)=Shadow7.sbP (start j)+804:=by simpa only [EnterJ7.parked,List.mem_singleton] using hq
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
    have b:(q:Nat)=Shadow7.sbP (start j)+804:=by simpa only [EnterJ7.parked,List.mem_singleton] using hq
    exact (topFHead_all j h2 h19 q hm).2 b
  rw [Shadow7.body_cover j (program j d) [EnterJ7.parked j] (support j) native admin (codes j h2 d).1 _ ticks
    (EnterJ7.parked j) (List.mem_singleton.mpr rfl)]
  have body0:=EnterJ7.from_full j raw cut z G S head small packed input
  exact EnterProof17.actual_parked (EnterJ7.ports j) _ (Shadow7.sbP (start j)) 15 z G S body0.2.1
theorem upperFreeF_all : ∀ j : Fin 26, 0≤j.val → j.val≤24 → ∀k:Fin 20,
    start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val≤min (start j+30+railP (start j+14)) 529 →
    start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val∈(W.compactSkywalkSignPoolA base (start j)).released ∨
      (start j+274≤start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val ∧ start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val<786) := by
  decide +kernel
theorem upperFHead_all : ∀ j : Fin 26, 0≤j.val → j.val≤24 → ∀q∈support j,
    q<start j+Shadow7.sbP (start j)+49 ∨ 1043<q := by
  decide +kernel

theorem upperF_clear (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) (d:Bool) (raw s:State) (x p:Nat)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) s)
    (q:Nat) (low:start j+Shadow7.sbP (start j)+49≤q) (high:q≤min (start j+30+railP (start j+14)) 529) :
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
          exact ⟨q-(start j+Shadow7.sbP (start j)+34),by omega,by omega⟩
        · simp only [Wire] at *; omega
      have above:start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)≤q:=by
        by_contra lo
        simp only [Nat.not_le] at lo
        apply inPair
        simp only [EnterJ7.upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp]
        exact ⟨q-(start j+Shadow7.sbP (start j)+34),by omega,by omega⟩
      have rl:start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)=start j+railP (start j)+16 ∧
          (257≤railP (start j) ∨ start j+railP (start j)=513) ∧ railP (start j+14)≤railP (start j):=by
        have:=j.isLt; simp only [Shadow7.wpP,railP,Shadow7.sbP,start]; split_ifs <;> omega
      have k0:q-(start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j))<20:=by omega
      have free:=upperFreeF_all j h1 h21 ⟨_,k0⟩ (by simp only; omega)
      simp only [show start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+(q-(start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)))=q by omega] at free
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
  have wdef : Shadow7.wpP (start j) = railP (start j) - Shadow7.sbP (start j) - 16 := rfl
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
    have mid : (Shadow7.shape j).mid = Shadow7.sbP (start j)+16 := rfl
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
    have only405 : ∀ k : Fin 26, 1 ≤ k.val → k.val ≤ 24 → min 3 (Shadow7.wpP (start k) + start k - 448) ≠ 0 → start k = 405 := by
      decide
    by_cases z2 : min 3 (Shadow7.wpP (start j) + start j - 448) = 0
    · omega
    · have e := only405 j (by omega) h19 z2
      have ha : Shadow7.a0P 405 = 483 := by decide
      have hs : Shadow7.sbP 405 = 46 := by decide
      have hw : Shadow7.wpP 405 = 46 := by decide
      have hr : railP (405 + 14) = 94 := by decide
      rw [e] at lo hi
      exact upper_clear j (by omega) (by omega) d raw s x p domain m tape _ _ _ cut q
        (by rw [e, hs]; omega) (by rw [e, hr]; omega)
  · rw [runEq]; exact topc _ (by simp only [Shadow7.e0P]; (try simp only [Wire] at *); omega)
  · rw [runEq]
    have e : Shadow7.b0P (start j) + 17 = EnterJ7.parked j := by simp only [EnterJ7.parked, Shadow7.b0P]; omega
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
theorem lower_carry (j : Fin 26) {kk : Nat} (h : 1556+kk+1<Shadow7.e0P (start j)) :
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
  have top:Shadow7.wpP (start j)+Shadow7.sbP (start j)+start j≤497:=by
    have r:railP (start j)=513-start j:=by unfold railP; rw [if_neg (by omega),if_neg (by omega)]
    have wdef:Shadow7.wpP (start j)=railP (start j)-Shadow7.sbP (start j)-16:=rfl
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
    by_cases topw:1556+kk+1=Shadow7.e0P (start j)
    · -- margin 17: the wire below the anchored block is no tick-1 carry; the cut keeps it at its (clean) stock value
      have f:=EnterJ7.frame j
      obtain ⟨_,same,_,port,pend,hn,hf,hu,hi⟩:=top_geometry j (by omega) h21 (q:=1556+kk) topw
      have ns:(1556+kk:Wire)∉support j:=fun h=>
        (topHead_all j (by omega) h21 _ (List.mem_append_right _ h)).1 (by simp only [Shadow7.e0P] at topw; simp only [Wire] at *; omega)
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
      obtain ⟨c,hc,eq⟩:=List.mem_map.mp (lower_carry j (show 1556+kk+1<Shadow7.e0P (start j) by omega))
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
    (low : ∀i:Fin (Shadow7.sbP (start k)+18), s.basis (start k+16+i.val)=o.basis (start k+16+i.val) ∧
      s.basis (786+i.val)=o.basis (786+i.val))
    (high : ∀i:Fin (Shadow7.wpP (start k)-2), s.basis (start k+Shadow7.sbP (start k)+34+i.val)=false ∧
      s.basis (Shadow7.sbP (start k)+804+i.val)=(if o.basis (EnterJ7.gate k) then o.basis (Shadow7.sbP (start k)+804+i.val)
        else o.basis (start k+Shadow7.sbP (start k)+34+i.val)))
    (ext : ∀q:Wire,¬WideReference.Box (start j) q → ¬leftovers j q → ¬(2070≤(q:Nat)+start j ∧ (q:Nat)≤1812) →
      s.basis q=o.basis q)
    (mirror : ∀q:Nat,2070≤q+start j → q≤1812 → s.basis q=o.basis q)
    (left : ∀q,leftovers j q → s.basis q=o.basis q)
    (zs : List Wire) (clear : ∀q∈zs,s.basis q=false)
    (zcover : ∀q:Nat,1556≤q → q≤1812 → WideReference.Box (start j) q → ¬leftovers j q → q∉EnterJ7.pending k →
      q≠EnterJ7.flagN k → q≠EnterJ7.flagF k → q≠EnterJ7.flagU k → q∈zs)
    (rails : ∀q:Nat,WideReference.Box (start j) q → ¬leftovers j q → q<1556 →
      (start k+16≤q ∧ q<start k+Shadow7.sbP (start k)+32+Shadow7.wpP (start k)) ∨ (786≤q ∧ q<Shadow7.sbP (start k)+802+Shadow7.wpP (start k)))
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
      | exact (show _ from by have l:=low ⟨Shadow7.sbP (start k)+16,by omega⟩; simp only at l
                              rw [show start k+16+(Shadow7.sbP (start k)+16)=start k+Shadow7.sbP (start k)+32 by omega,
                                show 786+(Shadow7.sbP (start k)+16)=Shadow7.sbP (start k)+802 by omega] at l; exact l)
      | exact (show _ from by have l:=low ⟨Shadow7.sbP (start k)+17,by omega⟩; simp only at l
                              rw [show start k+16+(Shadow7.sbP (start k)+17)=start k+Shadow7.sbP (start k)+33 by omega,
                                show 786+(Shadow7.sbP (start k)+17)=Shadow7.sbP (start k)+803 by omega] at l; exact l)
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
        · by_cases lo:(q:Nat)<start k+Shadow7.sbP (start k)+34
          · have l:=(low ⟨q-(start k+16),by simp only [Wire] at *; omega⟩).1; simp only at l
            rw [show start k+16+(q-(start k+16))=(q:Nat) by simp only [Wire] at *; omega] at l; exact l
          · exfalso; apply notHi
            simp only [RailPair.sites,EnterJ7.upperPairs,List.mem_flatMap,List.mem_map,List.mem_range]
            exact ⟨_,⟨q-(start k+Shadow7.sbP (start k)+34),by simp only [Wire] at *; omega,rfl⟩,
              by simp only [List.mem_cons]; left; simp only [Wire] at *; omega⟩
        · by_cases lo:(q:Nat)<Shadow7.sbP (start k)+804
          · have l:=(low ⟨q-786,by simp only [Wire] at *; omega⟩).2; simp only at l
            rw [show 786+(q-786)=(q:Nat) by simp only [Wire] at *; omega] at l; exact l
          · exfalso; apply notHi
            simp only [RailPair.sites,EnterJ7.upperPairs,List.mem_flatMap,List.mem_map,List.mem_range]
            exact ⟨_,⟨q-(Shadow7.sbP (start k)+804),by simp only [Wire] at *; omega,rfl⟩,
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
private theorem both (P Q:Prop) [Decidable P] [Decidable Q] : (decide P && decide Q)=decide (P ∧ Q) := by
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
    (upper : ∀ q:Nat, Shadow7.a0P (start j)+17 ≤ q → q ≤ min (start j+30+railP (start j+14)) 529 → s.basis q = false)
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
  have bits := EndWords.result j h0 (by omega) s m z
    (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.fit xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
    ev.1 h.far h.side
  have whole := Whole.result j h0 (by omega) s m z
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
  have highZero : ∀ q : Nat, Shadow7.a0P (start j) + 17 ≤ q → q ≤ (start j) + 30 + railP ((start j) + 15) → s.basis q = false :=
    fun q lo hi => upper q lo (Nat.le_min.mpr ⟨by omega, by omega⟩)
  have rails := BoundaryRails.result j h0 (by omega) s m z
    (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.fit xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
    ev.1 h.far h.side highZero h.top (endRaw (start j) raw s) nextInput
  have eo : pullState (OB5.sig (start j + 14)) (endRaw (start j) raw s) = origin (start j) raw s :=
    endpoint (start j) (by omega) raw s
  simp only [eo] at rails
  have kept := PreservedRecords.result j h0 (by omega) s m bits.2.2.2.1
  have clear := BoundaryClean.result j h0 (by omega) s m z
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
    have e1 : start k + Shadow7.sbP (start k) + 34 + i.val = Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val := by
      unfold Shadow7.a0P Shadow7.lowsP; omega
    have e2 : Shadow7.sbP (start k) + 804 + i.val = Shadow7.b0P (start j) + Shadow7.lowsP (start j) + i.val := by
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
    have mid : (Shadow7.shape j0).mid = Shadow7.sbP (start j0)+16 := rfl
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
    have wp : Shadow7.wpP 45 = 16 := by decide
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
  have same : Shadow.far 226 15 (unsigned 45 x p) = (2*2^242≤(unsigned 45 x p).u+(unsigned 45 x p).v) := by
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
      have ewp : Shadow7.wpP (start j0) = 16 := by decide
      have s3 : start j0 = 45 := rfl
      have en1 : min (Shadow7.wpP (start j0) - 1 - (Shadow7.e0P (start j0) - 1598)) (2045 - start j0 - Shadow7.e0P (start j0)) = 0 := by decide
      have hl : ∀ r : Nat, r ∈ LeaveJ7.Admission.spare j0 → r ∈ tailTempsF j0 := by
        intro r hr
        rw [LeaveJ7.Admission.mem_spare] at hr
        rcases hr with rfl | rfl | ⟨lo, hi⟩ <;> simp only [tailTempsF, List.mem_range'_1] <;>
          simp only [Wire] at * <;> omega
      exact hl q hq
    · intro q lo hi
      have en2 : min 3 (Shadow7.wpP (start j0) + start j0 - 448) = 0 := by decide
      omega
    · rw [vEq]; exact topF_clean j0 (by decide) (by decide) d x p raw cut dom n0 tape _ _ _ cut0 _ (by simp only [Shadow7.e0P]; (try simp only [Wire] at *); omega)
    · rw [vEq]
      have e : Shadow7.b0P (start j0) + 17 = EnterJ7.parked j0 := by simp only [EnterJ7.parked, Shadow7.b0P]; omega
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
  have upper : ∀ q:Nat, Shadow7.a0P (start j0)+17 ≤ q → q ≤ min (start j0+30+railP (start j0+14)) 529 →
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
    · exact LeaveJ7.native_carryJ j0 (by decide) (by decide) _ _ hin.ready hin.top q (by simp only [Wire] at *; omega)
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
    have mid : (Shadow7.shape j).mid = Shadow7.sbP (start j)+16 := rfl
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
    have mid : (Shadow7.shape j).mid = Shadow7.sbP (start j)+16 := rfl
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
  have up : ∀ q:Nat, Shadow7.a0P (start j)+17 ≤ q → q ≤ min (start j+30+railP (start j+14)) 529 →
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
    · exact native_carryJ j (by omega) (by omega) _ v h.ready h.top q (by simp only [Wire] at *; omega)
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
      have mid : (Shadow7.shape j).mid=Shadow7.sbP (start j)+16 := rfl
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
    have mid : (Shadow7.shape k).mid = Shadow7.sbP (start k)+16 := rfl
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
  have eq:farAt 39 420 x p=(2*2^55≤z.u+z.v):=by
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
  leave j := if inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+3*Shadow7.lowsP (start j)+115 else toffoliCount (Shadow7.leaveMoveP j)
  leaveInv j := if inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+147 else toffoliCount (Shadow7.leaveMoveInvP j)
  load _ d := if d then 42 else 42
  restore _ d := if d then 50 else 51
  portal t := if portalTick t then 4*Shadow7.wpP t-2 else toffoliCount (Shadow7.portalP t)
  portalInv t := if portalTick t then 5*Shadow7.wpP t-4 else toffoliCount (Shadow7.portalInvP t)
  park _ := 0
  parkInv _ := 0
  exitLoad _ d := if d then 42 else 42
  exitRestore _ d := if d then 50 else 51
  routed j a n := if a+n ≤ 15 then n*(2*(Shadow7.smallBits j+17)) else toffoliCount (Shadow7.routed j a n)
  unrouted j a n := if a+n ≤ 15 then n*(2*(Shadow7.smallBits j+17)-1) else toffoliCount (Shadow7.unrouted j a n)
  pack d s t := if dueTick t then 9 else toffoliCount (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))
  unpack d s t := if dueTick t then 11 else toffoliCount (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))
  tick e := if e < 511 then tickT e else toffoliCount (renameProgram (OB5.sig e) (TickRanges.tick base e))
  receiver e := if e < 511 then recvT e else
    toffoliCount (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))

def mcV : Pieces Nat where
  enter _ := 2
  enterInv _ := 3
  leave j := if inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+Shadow7.lowsP (start j)+93 else measurementCount (Shadow7.leaveMoveP j)
  leaveInv j := if inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+61 else measurementCount (Shadow7.leaveMoveInvP j)
  load _ d := if d then 49 else 49
  restore _ d := if d then 43 else 44
  portal t := if portalTick t then 4*Shadow7.wpP t-7 else measurementCount (Shadow7.portalP t)
  portalInv t := if portalTick t then 3*Shadow7.wpP t-5 else measurementCount (Shadow7.portalInvP t)
  park _ := 0
  parkInv _ := 0
  exitLoad _ d := if d then 49 else 49
  exitRestore _ d := if d then 43 else 44
  routed j a n := if a+n ≤ 15 then n*(Shadow7.smallBits j+17) else measurementCount (Shadow7.routed j a n)
  unrouted j a n := if a+n ≤ 15 then n*(Shadow7.smallBits j+17) else measurementCount (Shadow7.unrouted j a n)
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
  leave j := if inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+10*Shadow7.lowsP (start j)+746+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveP j)
  leaveInv j := if inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+11*Shadow7.lowsP (start j)+714+3*Shadow7.wpP (start j+15) else
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
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+3*Shadow7.lowsP (start j)+99+CRTBarrel.barrelT (start j) false
    else if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+3*Shadow7.lowsP (start j)+115 else toffoliCount (Shadow7.leaveMoveP j)
  leaveInv := fun j => if crtBlocks j then
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+131+CRTBarrel.barrelT (start j) true
    else if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+147 else toffoliCount (Shadow7.leaveMoveInvP j) }

def mcV : Pieces Nat := { WindowParams7.mcV with
  leave := fun j => if crtBlocks j then
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+Shadow7.lowsP (start j)+92+CRTBarrel.barrelM (start j) false
    else if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+Shadow7.lowsP (start j)+93 else measurementCount (Shadow7.leaveMoveP j)
  leaveInv := fun j => if crtBlocks j then
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+60+CRTBarrel.barrelM (start j) true
    else if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+61 else measurementCount (Shadow7.leaveMoveInvP j) }

def slotsV : Pieces Nat := { WindowParams7.slotsV with
  leave := fun j => if crtBlocks j then
      6*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+10*Shadow7.lowsP (start j)+662+3*Shadow7.wpP (start j+15)+
        CRTBarrel.barrelSlots (start j) false
    else if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+10*Shadow7.lowsP (start j)+746+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveP j)
  leaveInv := fun j => if crtBlocks j then
      6*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+11*Shadow7.lowsP (start j)+630+3*Shadow7.wpP (start j+15)+
        CRTBarrel.barrelSlots (start j) true
    else if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+11*Shadow7.lowsP (start j)+714+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveInvP j) }

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
    toffoliCount (Shadow7.leaveMoveP j) = (if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+3*Shadow7.lowsP (start j)+115 else toffoliCount (Shadow7.leaveMoveP j)) ∧
    toffoliCount (Shadow7.leaveMoveInvP j) = (if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+147 else toffoliCount (Shadow7.leaveMoveInvP j)) ∧
    measurementCount (Shadow7.leaveMoveP j) = (if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+Shadow7.lowsP (start j)+93 else measurementCount (Shadow7.leaveMoveP j)) ∧
    measurementCount (Shadow7.leaveMoveInvP j) = (if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+61 else measurementCount (Shadow7.leaveMoveInvP j)) ∧
    gateSlots (Shadow7.leaveMoveP j) ≤ (if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+10*Shadow7.lowsP (start j)+746+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveP j)) ∧
    gateSlots (Shadow7.leaveMoveInvP j) ≤ (if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+11*Shadow7.lowsP (start j)+714+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveInvP j)) := by
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
    toffoliCount (forwardW CRTBarrel.params true first WindowParams7.rest7)=127986 ∧
    toffoliCount (forwardW CRTBarrel.params false first WindowParams7.rest7)=127986 ∧
    toffoliCount (reverseW CRTBarrel.params true first WindowParams7.rest7)=128403 ∧
    toffoliCount (reverseW CRTBarrel.params false first WindowParams7.rest7)=128428 ∧
    measurementCount (forwardW CRTBarrel.params true first WindowParams7.rest7)=66344 ∧
    measurementCount (forwardW CRTBarrel.params false first WindowParams7.rest7)=66344 ∧
    measurementCount (reverseW CRTBarrel.params true first WindowParams7.rest7)=65626 ∧
    measurementCount (reverseW CRTBarrel.params false first WindowParams7.rest7)=65651 := by
  rw [(counts true first WindowParams7.rest7).1,(counts false first WindowParams7.rest7).1,(counts true first WindowParams7.rest7).2.1,(counts false first WindowParams7.rest7).2.1,
    (counts true first WindowParams7.rest7).2.2.1,(counts false first WindowParams7.rest7).2.2.1,(counts true first WindowParams7.rest7).2.2.2,
    (counts false first WindowParams7.rest7).2.2.2]
  decide +kernel

theorem slot_sums : (forwardL slotsV true first WindowParams7.rest7).sum ≤ 2370994 ∧ (forwardL slotsV false first WindowParams7.rest7).sum ≤ 2370994 ∧
    (reverseL slotsV true first WindowParams7.rest7).sum ≤ 2334224 ∧ (reverseL slotsV false first WindowParams7.rest7).sum ≤ 2334224 := by
  decide +kernel

/-- Slot bounds of the CRT window (upper bounds only; the judge has no slot ceiling). -/
theorem ship_slots : gateSlots (forwardW CRTBarrel.params true first WindowParams7.rest7) ≤ 2370994 ∧
    gateSlots (forwardW CRTBarrel.params false first WindowParams7.rest7) ≤ 2370994 ∧
    gateSlots (reverseW CRTBarrel.params true first WindowParams7.rest7) ≤ 2334224 ∧
    gateSlots (reverseW CRTBarrel.params false first WindowParams7.rest7) ≤ 2334224 := by
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
  exact ⟨fun g hg => p g (List.mem_append_left _ hg),
    fun g hg => p g (List.mem_append_right _ (List.mem_append_right _ hg))⟩

theorem proper_swap (a c : List Gate) (g g' : Gate) (hg : proper g' = true)
    (h : ∀ x ∈ a ++ ([g] ++ c), proper x = true) : ∀ x ∈ a ++ ([g'] ++ c), proper x = true := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ hx)
  · rcases List.mem_append.mp hx with hx | hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact hg
    · exact h x (List.mem_append_right _ (List.mem_append_right _ hx))

theorem partsC_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.beforeC (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPartC (start j), proper g = true) := by
  obtain ⟨pb, pa⟩ := parts_proper j h0 h1
  rw [before_split] at pb
  rw [after_split] at pa
  rw [beforeC_split, afterPartC_split]
  refine ⟨proper_swap _ _ _ _ ?_ pb, proper_swap _ _ _ _ ?_ pa⟩
  · simp only [proper, decide_eq_true_eq]; ((try unfold Wire at *); omega)
  · simp only [proper, decide_eq_true_eq]; unfold Shadow7.e0P; ((try unfold Wire at *); omega)

theorem partsC4_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.beforeC4 (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPartC (start j), proper g = true) := by
  obtain ⟨pb, pa⟩ := partsC_proper j h0 h1
  rw [beforeC_cut] at pb
  rw [beforeC4_split]
  refine ⟨proper_swap _ _ _ _ ?_ pb, pa⟩
  have := (start_win7 j h0 (by omega)).2
  simp only [proper, decide_eq_true_eq]
  unfold start at *
  constructor <;> ((try unfold Wire at *); omega)

theorem proper_swapL (a c b b' : List Gate) (hb : ∀ g ∈ b', proper g = true)
    (h : ∀ x ∈ a ++ (b ++ c), proper x = true) : ∀ x ∈ a ++ (b' ++ c), proper x = true := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ hx)
  · rcases List.mem_append.mp hx with hx | hx
    · exact hb x hx
    · exact h x (List.mem_append_right _ (List.mem_append_right _ hx))

theorem partsC5_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.beforeC5 (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPartC (start j), proper g = true) := by
  obtain ⟨pb, pa⟩ := partsC4_proper j h0 h1
  rw [beforeC4_cut, beforeC5_cut] at pb
  rw [beforeC5_split, beforeC5_cut]
  refine ⟨proper_swapL _ _ _ _ ?_ pb, pa⟩
  have win := start_win7 j h0 h1
  have r := Shadow7.rail_win win.1 win.2
  have t0 : Partial.tagsP.getD 0 0 = 1576 := rfl
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp only [proper, decide_eq_true_eq, t0] <;> unfold Shadow7.a0P Shadow7.e0P at * <;>
    ((try unfold Wire at *); omega)

theorem partsC6_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.beforeC5 (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPartC2 (start j), proper g = true) := by
  obtain ⟨pb, pa⟩ := partsC5_proper j h0 h1
  refine ⟨pb, ?_⟩
  rw [afterPartC_split, tailD_cut] at pa
  simp only [List.append_assoc] at pa
  rw [afterPartC2_split]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact pa x (List.mem_append_left _ hx)
  · exact pa x (List.mem_append_right _ (List.mem_append_right _ hx))

theorem proper_swap2 (a b c : List Gate) (g1 g1' g2 g2' : Gate) (hg1 : proper g1' = true) (hg2 : proper g2' = true)
    (h : ∀ x ∈ a ++ ([g1] ++ (b ++ ([g2] ++ c))), proper x = true) :
    ∀ x ∈ a ++ ([g1'] ++ (b ++ ([g2'] ++ c))), proper x = true := by
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl | hx | rfl | hx
  · exact h x (by simp [hx])
  · exact hg1
  · exact h x (by simp [hx])
  · exact hg2
  · exact h x (by simp [hx])

theorem partsC8_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.beforeC5 (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPartC3 (start j), proper g = true) := by
  obtain ⟨pb, pa⟩ := partsC6_proper j h0 h1
  refine ⟨pb, ?_⟩
  rw [afterPartC2_split, tailE_cut] at pa
  rw [afterPartC3_split]
  have hp : proper (GateMirror.Gate.cx (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559) = true := by
    have win := start_win7 j h0 h1
    have r := Shadow7.rail_win win.1 win.2
    simp only [proper, decide_eq_true_eq]; unfold Shadow7.a0P at *; ((try unfold Wire at *); omega)
  have := proper_swap2 (CRTBarrel.tailD0 (start j) ++ (CRTBarrel.tailD1 (start j) ++
      ([.cx (Shadow7.e0P (start j) + 4) 1559] ++ CRTBarrel.tailE0 (start j))))
    (CRTBarrel.chainMid (start j)) (CRTBarrel.tailE1 (start j)) (.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559) (.cx (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559)
    (.pop 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559) (.cx (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559) hp hp (by simpa only [List.append_assoc] using pa)
  simpa only [List.append_assoc] using this

theorem leave_phys (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    GatePhysical (CRTBarrel.leave j) ∧ GatePhysical (CRTBarrel.unleave j) := by
  obtain ⟨pb, pa⟩ := partsC8_proper j h0 h1
  have b := physical_of_proper _ (ScanRow16.beforeRow_proper j pb)
  have a := physical_of_proper _ (KeptParity.afterProper j pa)
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

theorem ship_toffoliF_true : toffoliCount (forwardW CRTBarrel.params true first WindowParams7.rest7) = 127986 :=
  ship_counts.1

theorem ship_toffoliF_false : toffoliCount (forwardW CRTBarrel.params false first WindowParams7.rest7) = 127986 :=
  ship_counts.2.1

theorem ship_toffoliR_true : toffoliCount (reverseW CRTBarrel.params true first WindowParams7.rest7) = 128403 :=
  ship_counts.2.2.1

theorem ship_toffoliR_false : toffoliCount (reverseW CRTBarrel.params false first WindowParams7.rest7) = 128428 :=
  ship_counts.2.2.2.1

theorem ship_measureF : measurementCount (forwardW CRTBarrel.params true first WindowParams7.rest7) = 66344 ∧
    measurementCount (forwardW CRTBarrel.params false first WindowParams7.rest7) = 66344 :=
  ⟨ship_counts.2.2.2.2.1, ship_counts.2.2.2.2.2.1⟩

theorem ship_measureR : measurementCount (reverseW CRTBarrel.params true first WindowParams7.rest7) = 65626 ∧
    measurementCount (reverseW CRTBarrel.params false first WindowParams7.rest7) = 65651 :=
  ship_counts.2.2.2.2.2.2

theorem ship_slotsF : gateSlots (forward45plus1 true) ≤ 2370994 ∧ gateSlots (forward45plus1 false) ≤ 2370994 :=
  ⟨ship_slots.1, ship_slots.2.1⟩

theorem ship_slotsR : gateSlots (reverse45plus1 true) ≤ 2334224 ∧ gateSlots (reverse45plus1 false) ≤ 2334224 :=
  ship_slots.2.2

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end


end




open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic MappedCompressed
open StairRestSupport ArchiveFieldScratch StairArchiveRelease

namespace ECDSAAdd.Entrant.WindowDomainProof

private theorem fixedSites :
    (base 720 :: ArchiveFieldScratch.indices.map hole).all (fun q => decide (InDom q)) = true := by
  decide +kernel

private theorem payloads :
    [10,13,16,19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73,76,79,82].all
      (fun j => (packetSites j).all (fun q => decide (InDom q))) = true := by
  decide +kernel

theorem fieldSites_ok (j : Nat)
    (hj : j ∈ [10,13,16,19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73,76,79,82]) :
    (fieldSites j).all (fun q => decide (InDom q)) = true := by
  rw [fieldSites, List.all_append, fixedSites, Bool.and_true]
  exact List.all_eq_true.mp payloads j hj

open StairArchiveNativeCut CodecBitSliceVerify ReducedWindowArchives

private theorem get_after (head : Cols) (k q : Nat) (h : head.length ≤ q) :
    get (head ++ List.replicate k 0) q = 0 := by
  change ((head ++ List.replicate k 0)[q]?).getD 0 = 0
  rw [List.getElem?_append_right h, List.getElem?_replicate]
  split <;> rfl

theorem restored (rev : Bool) :
    (List.range' 16 105).all (fun q =>
      get (outputCols (leave rev)) q == get (canonical rev rev) q) = true := by
  refine List.all_eq_true.mpr (fun q hq => ?_)
  have lo : 16 ≤ q := (List.mem_range'_1.mp hq).1
  have bound : (canonical rev rev).length = 16 := by cases rev <;> rfl
  have noEntry : (canonical rev rev)[q]? = none :=
    List.getElem?_eq_none (by omega)
  have canonicalZero : get (canonical rev rev) q = 0 := by
    change ((canonical rev rev)[q]?).getD 0 = 0
    rw [noEntry]
    rfl
  rw [canonicalZero, beq_iff_eq]
  cases rev with
  | false => exact get_after word1 105 q (by exact lo)
  | true => exact get_after word0 97 q (by exact lo)

end ECDSAAdd.Entrant.WindowDomainProof

-- ==== begin CRTBarrel20 ====
section

/-! 21-tag CRT barrel shifter for 20-tick shadow blocks (shifts `0..20` on widths `83, 93, 103, 112, 122`). -/

set_option autoImplicit false

section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Challenge

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel20

structure R8Step where
  tags : List Nat
  pre : List (Nat × Nat)
  src : Nat
  dst : Nat

structure Count where
  t : Nat
  m : Nat
  slots : Nat
  deriving DecidableEq, Repr

def count (p : Program) : Count := ⟨toffoliCount p, measurementCount p, gateSlots p⟩
def cadd (a b : Count) : Count := ⟨a.t + b.t, a.m + b.m, a.slots + b.slots⟩
def cscale (k : Nat) (a : Count) : Count := ⟨k * a.t, k * a.m, k * a.slots⟩
def czero : Count := ⟨0, 0, 0⟩
def csumBy {α : Type} (f : α → Count) : List α → Count
  | [] => czero
  | x :: xs => cadd (f x) (csumBy f xs)

def Fits (P : Wire → Prop) (p : Program) : Prop :=
  ∀ i ∈ p, RecordedQuantum.PhysicalInstr (.gate i) ∧ ∀ q ∈ i.wires, P q

def fieldDegree (p : Nat) : Nat := Nat.log2 p
def selected (n mask : Nat) : List Nat := (List.range n).filter (fun i => mask.testBit i)
def elimStep (n i : Nat) (row : Nat × Nat) : List (Nat × Nat) :=
  (if row.1 < n then [(row.1, i)] else []) ++ (selected n row.2).map (fun j => (i, j))

def schedule20 : Nat → List (Nat × Nat)
  | 83 => [(257,1), (21,1), (31,1), (11,1), (13,1), (19,1), (25,1), (73,1), (37,1), (67,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1)]
  | 93 => [(257,2), (21,1), (31,1), (11,1), (13,1), (19,1), (73,1), (37,1), (67,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1)]
  | 103 => [(257,2), (21,1), (31,1), (11,1), (13,1), (19,1), (73,1), (37,1), (41,1), (47,1), (67,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1)]
  | 112 => [(257,2), (21,1), (31,1), (11,1), (13,1), (19,1), (25,1), (73,1), (37,1), (41,1), (47,1), (55,1), (67,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1)]
  | 122 => [(257,2), (21,1), (31,1), (11,1), (13,1), (19,1), (25,1), (73,1), (37,1), (41,1), (47,1), (55,1), (59,1), (61,1), (67,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1)]
  | _ => []

def pivots20 : Nat → List (Nat × Nat)
  | 83 => [
      (83,153514389792368823439616), (83,460543169377106470318849), (83,767571948961844117198081),
      (83,2302715846885532344057607), (83,2609744626470269325140993), (83,7829233879408813559962643),
      (83,5876498681489133048070421), (83,3867100074355787439895423), (83,6504639501629342111994881),
      (83,5601306490009000542132226), (83,2745261202345044630356229), (83,5489304912540236507214346),
      (83,2519006618447010046764309), (83,4970774799301315832433194), (83,5415962905208338638111041),
      (83,8027780671461342181130882), (83,9150524824274657941164691), (83,1765683397236174373856550),
      (83,3463981414688826769164876), (20,4126657067812608537928493), (21,8252243566941463120725594),
      (83,724321644610508379565977), (25,8833566130779956187739889), (83,9311284004151955521329939),
      (83,7855305613455680091848919), (83,3214012022357320058798510), (28,865070231921115893314563),
      (28,2342064662103304025988101), (83,4118007817162400701484041), (83,6913801098484894000878619),
      (83,2145303942331495737545771), (83,4289667677174129165510742), (83,8577952425003482418073772),
      (83,1968698201753629426185587), (83,3933946637051353379105510), (83,7867837996918475231057356),
      (37,3184675637218349616398259), (83,9550684615707066296631509), (83,7605332664325078568206719),
      (83,3571120882603442433032958), (83,7097379277706449702356476), (44,4919882983743263887783711),
      (83,2891133947230344146262305), (83,8067166640597144376257379), (83,6411594140547467494013176),
      (83,4622698091895842538246185), (83,9159175438695384013578322), (83,3952695710926206670921441),
      (49,7022383834458765784212259), (50,7244559933585242460702278), (51,6850692081128833788251276),
      (52,6296713517118063881427224), (83,8675628082328381096699419), (56,5629326819660021465501431),
      (57,8689686272638955934752238), (56,258432501346042957609948), (83,434168104894457919469496),
      (83,3848830793419631769618357), (83,6178118398261299601884347), (83,1531137735724080228988433),
      (83,4591586393194333569554995), (83,9181807727327212632290406), (83,1694953042209737328847052),
      (83,6609401259453780395260707), (83,5712600994386259723351622), (83,5019003518475241955307633),
      (67,2473261801684310197129363), (68,4946523603368620394258726), (83,2863775177586871659655741),
      (83,1178299896112528568710821), (83,2141732117254488280198474), (83,5815380051704751603647287),
      (83,9666255646535730798397038), (75,3139436324935557243144581), (83,5639904635822836689805270),
      (83,1209245717088712377051647), (83,9286389448034244988855767), (79,4264632184645953166622067),
      (80,8529264369291906333244134), (83,3907068722014563554511039), (83,2566666766705881354098411),
      (83,407025398937976180730435), (83,814050797875952361460870)
    ]
  | 93 => [
      (93,157198735147350435612917760), (93,471596205442051306838753281), (93,785993675736752178064588801),
      (93,2357981027210256532264386567), (93,2672378497504957387665309697), (93,8017135492514840275333152787),
      (93,5045784136045347235816341525), (93,3311466204313815828514668671), (93,9852852041398439126976757761),
      (93,8080721781017763795499417859), (93,6388366880575094629243027717), (93,2298107543161664317672916751),
      (93,2885806947962267767597498641), (93,8375869218071049975636366131), (93,7332049289106299430472324437),
      (93,717170092504071476999061503), (18,1883695130565614084272947201), (19,3767330355329810313316401154),
      (93,7534659826688656811778637828), (93,3354771202617952112229744648), (93,3411330928331527506668879893),
      (93,6819526205196797179085848618), (93,6985123810660922917135843412), (93,7312262806957000465609916584),
      (93,3091652906746360621656375699), (93,5918739661701645046752084774), (93,6578396265812385667364095967),
      (28,7770016955707687581044772397), (93,5471881194780500113915056759), (93,2614057603429441395496662681),
      (31,5190930932927845304020060145), (32,8644764737851935820754358242), (93,6911846346623149199650689062),
      (93,1869068598588978197537122237), (93,2366544800420862018036676355), (93,2763553645555441639895914757),
      (93,5336872364435955842985079306), (93,7733582237964120914005287956), (93,3596909871568852575175755816),
      (93,7193101930997796725830029392), (93,4951323336111738850584809435), (93,9625688440607072536362983350),
      (43,6288665931768822556942364417), (44,5811143459961020075557707266), (93,8472035629032799715165635432),
      (93,6700008166126596424557726679), (93,5508126728614119338076673966), (93,8044658603271860951491817308),
      (49,4314578917662066703398027969), (50,8365558585721731713980597634), (93,6152482909764844704070406911),
      (93,2433542036950272482177313209), (93,4758280464210695196133020530), (93,9394028799126080229468514020),
      (93,2112074346390775892565511624), (56,3287904375178595292387701289), (93,7581494306998659343840214978),
      (93,6567294793602668546925619711), (93,5242664578067433046921106430), (93,9380912476236173818245553661),
      (61,990079641875666258519622139), (93,193414586929003382778837004), (93,1367994873165155504321131029),
      (93,3167591550058157519049856457), (93,9367345747814000265764027995), (66,3968745073167278575754963327),
      (93,9803509152348939997235162696), (68,5039412971418857037989537553), (93,6185106564485503916530138061),
      (93,7159135051960527096674246313), (93,1200815477397326417066484731), (93,2214738578868603755155736566),
      (73,7869476447732916859724517701), (74,2707525917589253316512359050), (93,7291458917771036778188007538),
      (77,6561306697422812754895922751), (77,5229385602854259799488384126), (93,8566500066556721283267926268),
      (79,6079238440951576638942806853), (80,9218369288600375125000193674), (93,3977779616671801595183024096),
      (83,7052330205871056241851402011), (93,377898071753807919552760109), (93,6661427014673074557442727020),
      (85,1594323342762790863662460313), (86,3188646685525581727324920626), (93,3916217385764519511593799417),
      (89,675373358930562978946538813), (90,1350746717861125957893077626), (91,2701493435722251915786155252),
      (92,5402986871444503831572310504), (93,2358930881801390976299383352), (93,4717861763602781952598766704)
    ]
  | 103 => [
      (103,160971504790886863522459877376), (103,482914514372660590567379632129), (103,804857523954434317612299386881),
      (103,2414572571863302952834968780807), (103,2736515581445076679864063623169), (103,8209546744335203232397368492051),
      (103,5166882955310412828107864080405), (103,3390941393217375229811994329215), (103,10089320490391997470454385541121),
      (103,8274659103762194111109627052291), (103,6541687685708876460676109041925), (103,2353262124197538566735348369167),
      (103,2955066314713372003921471537425), (103,8576890079304736570908386464563), (103,7508018472044839712006070408533),
      (103,734382174724156865185939685375), (18,1928903813699193473883008401409), (19,3857746283857728270695049723906),
      (103,7715491662529187753589112569860), (103,3435285711480787961686250225672), (103,3493202870611515610776952176661),
      (103,6983194834121544688268370116650), (103,7152766782116781783229706534996), (103,7487757114323961924825620414632),
      (103,3165852576508251847979242291603), (103,6060789413582480914329121456934), (103,6736277776191890935272685111263),
      (28,7956497362644670318523898990125), (103,5603206343455239534683633422967), (103,2676794985911736477058650945177),
      (31,5315513275318131219450435815409), (32,8852239091560372622649509187554), (103,7077730658942087560337631449126),
      (103,1913926244955132979530791020477), (103,2423341875630971541065218635523), (103,2829878933048781800201557432581),
      (103,5464957301182386430376636690954), (103,7919188211675234478275078349844), (103,3683235708486483922017413679144),
      (103,7365736377341740985338662064208), (103,5070155096178424940163434532827), (103,9856704963181625975476319133622),
      (43,6439593914131268547338282954497), (44,5950610903000073055429695823362), (103,8675364484129579799143273104232),
      (103,6860808362113690870913453591511), (103,1399079541995071719300280818809), (103,9374032084637209568646790591269),
      (103,525586790991246967874941511242), (103,7407430573263676639126038487305), (103,263297045432381183217995624335),
      (103,415179487326880385076913266462), (103,786914119150457710898994789948), (103,1755310038994126552859262127337),
      (103,3506774192169337032395780659666), (103,7520034692848599479960306729781), (103,6958795901632452139749412996714),
      (103,5565693324071379609109729971412), (59,8818310299944161961606800399607), (60,4362324061073356328705268234734),
      (103,6633976870964627639219184078701), (103,9756973934408389137949375334431), (64,8001772958427193636607159441441),
      (64,4766931659592445574627296551036), (103,8204127242038038170698510782662), (103,4607288748173434020062700566869),
      (103,8682034795668027197373605034941), (68,3439823416244449835740458565229), (103,6758328702735974300953746439386),
      (70,4845533013356385979194597260035), (103,1400131494263793194043165782495), (103,2368626853379325027918433048765),
      (103,4466323154713544933437227053434), (103,1633940013719520612453056662607), (103,3264050150442502079680644159646),
      (103,6495893912587560630832528437564), (103,5897285837407854708112806273656), (103,10048341192524997534079626036464),
      (103,1874185059493173780262760843744), (103,3793795843499196578598079747695), (103,7317720758434180257268150414558),
      (103,2617783911459370463982647911181), (103,5193477861583037998618725598746), (103,8442654834589703271107604810804),
      (103,1040263263868827797221172585667), (103,3478938393278482944863535199533), (103,6678102337678469947599868324442),
      (103,5274932098901977460658253714612), (103,502880299587301341227268114673), (103,1005760599174602682454536229346),
      (103,2011521198349205364909072458692), (93,6984362613164584833353600525841), (94,7155103250102436633662421322786),
      (95,7496584523978140234280062916676), (96,6911896471501318034018642899080), (103,5500097986284664876112315632419),
      (103,2703019619745630918500819896579), (98,391725069368622715041239665987), (99,783450138737245430082479331974),
      (100,1566900277474490860164958663948), (101,3133800554948981720329917327896), (102,6267601109897963440659834655792),
      (103,1822318659185337825623334948911)
    ]
  | 112 => [
      (112,82417410452934074131961198215168), (112,247252231358802222395883594645505), (112,412087052264670370659805991075841),
      (112,1236261156794011111979416043847687), (112,1401095977699879260243167996542977), (112,4203287933099610258158660817256467),
      (112,2645444073118932003299772231385109), (112,1736161993327291292376167345225855), (112,5165732091080704100319227706408961),
      (112,4236625461126246618493863865549059), (112,3349344095082949838760157118726405), (112,1204870207589138398332302594410255),
      (112,1512993953133236199281556203831569), (112,4391367720604039177433628746650419), (112,3844105457686969229384289662342485),
      (112,376003673458776641476488431894527), (18,987598752613986204926532671242241), (19,1975166097335154447690196081704962),
      (112,3950331731214955887684284661628932), (112,1758866284278159386113055824805896), (112,1788519869753091343871855877750805),
      (112,3575395755070235503898451415531562), (112,3662216592443796778296243909820500), (112,3833731642533877516083916150669480),
      (112,1620916519172219450664415747309971), (112,3103124179754219937433619391709990), (112,3448974221410245874369712701245407),
      (28,4073726649674084845133224179732013), (112,2868841647849083047130308183265911), (112,1370519032786803568092797872977561),
      (31,2721542796962872938891682367227889), (32,4532346414878913188768058729205730), (112,3623798097378359670487177773944870),
      (112,979930237417013735766770078083005), (112,1240751040323061870310174849742595), (36,1448898013720967761707319326988549),
      (37,2798058138205390343830319345545738), (112,1062225498886347523393788814669848), (112,1984358620546863083640287744065323),
      (112,3295418363441567431791437859225981), (112,4990220028163730933463858184355281), (112,1282385673517122402622006593649570),
      (112,2461208531050079890066744914081604), (112,4921882122095179592695805788810888), (112,3346766373220794443391479540174003),
      (48,1197138969763008477706975212197333), (112,4304795873730836625399695746459417), (112,4409311133643240580533322654974593),
      (112,5046402254497246586041153882922084), (50,2439828255142093781638928583485471), (112,2773955553577225172388375778965537),
      (52,3848818517824418795314105418618973), (53,3560014022699112282420995713347770), (112,2529422976092393220507488320074058),
      (56,2090971046036483161480871427156743), (57,4079261928545818984501181614085646), (112,1422644515332026384875684272974876),
      (112,2014658611707338991267595836918061), (112,845932557138598240680873247392591), (60,1236857575992007229820134996208077),
      (61,2473021901197367424894056894092186), (112,4943916558916405778649656597260084), (63,168186284431533223864918781536165),
      (112,4610297168722078842253242164570238), (65,272818771393785799871677373134867), (112,545609535123788389617995339100198),
      (112,758759903740743443118448348440697), (112,2378471518246509115177133865437357), (112,4320738921707854147072866558822661),
      (112,1328559057351943852254485523122773), (112,3824492006424779344677282186513653), (112,3509245363232115818211979690482154),
      (75,3235256904428012958302969791735499), (75,5146521646311704789998334440544393), (75,1276234751847099446403279593497613),
      (112,2179801726686555070623812359724293), (112,1068280327148108037634713878041819), (112,1904643063644291083207539499056493),
      (112,3809257195275867149109669929908954), (112,3340609103242848502381246259066292), (112,3192633541652285587456297379162984),
      (112,4843237905344080982561906036037328), (83,4130474614115758711031775567372485), (84,1389003873448922446782380241502602),
      (112,145947997916070493130318067933787), (112,2728807354699052921698153110169081), (112,4507760338929973732444988066221042),
      (112,2258079824951093023515874633422820), (90,4380977252607597963388840469678373), (112,2531839280325744742447428110815818),
      (112,1673566734086210813503912832598011), (112,4882179972504408903162363957673997), (112,1083488634645902864875304364933146),
      (112,2166125566544777388121478132400180), (97,1057064293177155821665434771755547), (96,2112464794941512092241405120554038),
      (112,2848950897757006410718861266058817), (112,2363234822770204897679200041603288), (112,270738162619359113027577628523463),
      (112,2592968028651171417655864446953599), (101,3202880454963383642699709078408975), (102,4864297780049240333179427059080734),
      (112,4606340983035670296846937280029218), (112,2683165611330267371119879740847991), (112,4473905200099861243586080425111278),
      (112,2214050411787367906421673423265244), (109,4549414959383762407801901188924353), (108,4965927633041702905125994590422083),
      (112,845335763647457460323620604708998), (112,2894944430745674125060776548031051), (112,11941248326298719625568655278033),
      (112,23882496652597439251137310556066)
    ]
  | 122 => [
      (122,84395428303804491911408779961368576), (122,253186284911413475734226339884105729), (122,421977141519022459557043899806842881),
      (122,1265931424557067378671131697491148807), (122,1434722281164676362493949086970150913), (122,4304166843494006425804297976118247443),
      (122,2708934730873790155480065701155242005), (122,1777829881167140793049801032006303871), (122,5289709661266651725441248298511171585),
      (122,4338304472193274670245160962411659523), (122,3429728353364942518437207824153182469), (122,1233787092571278560857512392613693199),
      (122,1549305808008442254572355391651381521), (122,4496760545898532652288714948407923507), (122,3936363988671442401437881359768294741),
      (122,385027761621776432259796262836994047), (18,1011301122676711165007807656888631297), (19,2022570083671200915145469502043979778),
      (122,4045139692764109682974418630881574916), (122,1801079075100842530205637783822794760), (122,1831444346627160549665867152620847125),
      (122,3661205253191917121156847848986902570), (122,3750109790662450300152601316288626772), (122,3925741201954695374824441119410487464),
      (122,1659818515632357110921289555594379667), (122,3177599160068329269607242615702815526), (122,3531749602724100886444919308574197727),
      (28,4171496089266251451900838474492481069), (122,2937693847397467546892646452047581815), (122,1403411489573692058406742935014553241),
      (31,2786859824089997784459381302761703409), (32,4641122728836004436130657459874467810), (122,3710769251715429260197429055635034150),
      (122,1003448563115032309441454025876596669), (122,1270529065290805171582912554735220483), (36,1483671566050273197138625693712177413),
      (37,2865211533522324972921393253643825674), (122,1087718910859621523225957818364180504), (122,2031983227439998451636667767727423275),
      (122,3374508404164171587930442085773312381), (122,5109985308839666267561609643180850641), (122,1313162929681527538928518457941883810),
      (122,2520277535795277483685433539437393732), (122,5040007293025463511343443525623869064), (122,3427088766178081191086460255207771315),
      (48,1225870305037314335670822247709267413), (122,4408110974700381622628661304694073113), (122,4515134600850684382288211420699984513),
      (122,5167515908605189674675433332267523172), (50,2498384133265498458278777930098796575), (122,2840530486863072112824791244604061729),
      (52,3941190162252201534040659298592069725), (53,3645454359243891924289111815788114106), (122,2590129127518622944439719222636294474),
      (56,2141154351141359428466142513418971911), (57,4177164214830919816327973653458671118), (122,1456787983699997056483233239506267164),
      (122,2063010418388316899369363774340270381), (122,866234938509923279130087052046779215), (60,1266542157815824312565240625097238989),
      (61,2532374426826091569082405195621913498), (122,5062570556330402014679209492305520436), (63,172222755257878197627107349961975717),
      (122,4720944300771408708574234418077231230), (66,279366421907244410321981736736307219), (67,558704163966806099153544451930550310),
      (68,1058994988180780284090248265949438028), (122,2318525512891138426826202162264635531), (122,4871109194850108093982422937131553114),
      (122,4688899586809401301726620757639597053), (122,5114822445431416279815672496715570183), (122,4620595466236754746727468651024724979),
      (122,2951372551040994464902028655047470107), (122,4301804603275138753850737932997482550), (122,3589807770782554813085648526542846865),
      (122,695145379880043312726398912190303411), (122,4947945831326288814776519701162468087), (122,3396138399437866666272317986190687871),
      (122,1182458613852641735907287439083030383), (122,2363062337964499515142834827200794334), (122,1300400523489258527325721843421915379),
      (122,2535341634866716816372452465057419750), (85,3813278937933461757226254660823833305), (85,5162524806989287668156045929510096039),
      (85,2028635649664115821750725596734578779), (122,2820403996600510833580062097009818019), (122,3497966946801414235654541111163283753),
      (122,2758147513425452104599967485877670482), (122,5008445672540140812600381867787329503), (90,559204378308053251708752301881427141),
      (122,98157714204829356573527940012521012), (122,694960886018076154236687505811857703), (122,1690762868987606852977568903010233059),
      (94,5060179368332233024039492138607443749), (122,3130694071704103236183935203952208780), (122,1194743757677905073604276451492976247),
      (97,2637515205841932684823989355882087635), (122,5132724008771319982463598896678740379), (100,3849929880169635366131165831772196419),
      (101,3461262083777748298736259037044055174), (102,3291810589225018378222568515880958220), (122,1525325363195513293843121993144921758),
      (122,4079391063985618442526230936965144935), (122,1287918703378124291813481324125077295), (106,3549024310329648127070067957747594089),
      (107,2802721044436360098438282827147863762), (108,4627992205253538895805699720320044452), (109,2297008545855775062473401735402855240),
      (122,4914726177344146296594075945084716718), (122,275626134984209756692038644404456796), (111,3752582652093884364824579318446248677),
      (112,3932865065515807321220177162389071306), (113,3628815894467195297559469320134544276), (122,3265133884220751811090397897881647478),
      (115,4782889056897449120692956532398294467), (122,2433548999791976869816333032488933741), (118,364547178318337303166315082104323231),
      (119,729094356636674606332630164208646462), (120,1458188713273349212665260328417292924), (121,2916377426546698425330520656834585848),
      (122,1095362181982594506802034255160552712), (122,2190724363965189013604068510321105424)
    ]
  | _ => []

def products20 : Nat → Bool → List (Nat × Nat × Nat)
  | 11, false => [(1,363286,7), (2,957754,5), (4,1915508,1), (3,726572,2), (5,1618274,4), (6,1288014,3)]
  | 11, true => [(1,1717352,7), (2,1519196,5), (4,759598,1), (3,858676,2), (5,1155910,4), (6,1882482,3)]
  | 13, false => [(1,1155910,7), (2,1882482,3), (4,1519196,6), (3,858676,2), (5,429338,4), (6,759598,5)]
  | 13, true => [(1,1618274,7), (2,1288014,3), (4,957754,6), (3,726572,2), (5,1453144,4), (6,1915508,5)]
  | 19, false => [(11,683540,5), (3,1845688,1), (5,341770,10), (4,922844,8), (7,85442,9), (9,1594224,6), (1,293576,2), (14,1274022,15), (8,1509998,4)]
  | 19, true => [(11,1779830,5), (3,662932,1), (5,1462508,10), (4,1325864,8), (7,1655730,9), (9,331466,6), (1,987998,2), (14,484622,15), (8,554576,4)]
  | 25, false => [(14,1655730,9), (12,662932,8), (2,1325864,1), (9,331466,6), (8,987998,4), (13,1779830,10), (10,1462508,5), (7,484622,15), (1,554576,2)]
  | 25, true => [(14,85442,9), (12,1845688,8), (2,922844,1), (9,1594224,6), (8,293576,4), (13,683540,10), (10,341770,5), (7,1274022,15), (1,1509998,2)]
  | 37, false => [(8,1185240,4), (13,1128498,24), (5,1585886,9), (27,376132,13), (16,715900,2), (3,1022530,19), (20,255632,10), (4,1823822,8), (31,1918176,29), (24,1176392,6), (22,1344886,21), (1,1532902,1), (2,1550492,18)]
  | 37, true => [(8,543550,4), (13,1870582,24), (5,793738,9), (27,1943054,13), (16,1527958,2), (3,1700282,19), (20,509674,10), (4,776800,8), (31,179622,29), (24,1019348,6), (22,77048,21), (1,453138,1), (2,1436976,18)]
  | 41, false => [(2,1087100,8), (31,509674,25), (20,718488,7), (24,1980240,14), (16,776800,21), (8,1436976,26), (13,1870582,17), (12,1360328,19), (9,1943054,16), (3,1629506,31), (22,1728740,1), (18,1788956,3), (5,616390,4)]
  | 41, true => [(2,592620,8), (31,255632,25), (20,1003832,7), (24,818386,14), (16,1823822,21), (8,1550492,26), (13,1128498,17), (12,208362,19), (9,376132,16), (3,1777460,31), (22,416724,1), (18,1236642,3), (5,430254,4)]
  | 47, false => [(9,1359064,2), (13,2024116,27), (5,1444074,3), (24,584286,17), (6,959974,6), (30,1547012,1), (23,206812,8), (26,1951080,26), (12,177202,9), (8,1168572,31), (16,1654498,14), (25,354404,22), (10,790996,5)]
  | 47, true => [(9,1911688,2), (13,490648,27), (5,1076468,3), (24,1511532,17), (6,356614,6), (30,1698140,1), (23,312020,8), (26,245324,26), (12,870268,9), (8,755766,31), (16,1874010,14), (25,1483710,22), (10,538234,5)]
  | 55, false => [(16,390768,17), (20,1470676,25), (24,534076,21), (3,195384,18), (27,1252950,7), (2,1848610,1), (8,462152,4), (5,497082,27), (10,1661856,5), (17,711940,2), (13,39154,31), (14,1279652,13), (4,1783914,8)]
  | 55, true => [(16,1024598,17), (20,946082,25), (24,268138,21), (3,2049196,18), (27,1624110,7), (2,801214,1), (8,1107706,4), (5,647968,27), (10,1744434,5), (17,1790918,2), (13,1639898,31), (14,118260,13), (4,1892164,8)]
  | 59, false => [(5,1372560,4), (24,409974,16), (22,1024598,19), (18,1277202,8), (17,2001240,10), (8,946082,15), (14,1125134,25), (20,118260,30), (9,1624110,26), (10,1744434,2), (2,236520,13), (15,914506,6), (1,383646,31)]
  | 59, true => [(5,994164,4), (24,156618,16), (22,390768,19), (18,2018842,8), (17,1146268,10), (8,1470676,15), (14,1346540,25), (20,1279652,30), (9,1252950,26), (10,1661856,2), (2,1688402,13), (15,1028998,6), (1,1810584,31)]
  | 61, false => [(1,134558,2), (16,981296,16), (3,1698140,18), (24,490648,30), (31,1355296,5), (2,1828034,11), (8,624040,17), (5,538234,25), (20,312020,15), (13,111570,24), (22,2041366,13), (4,670692,22), (27,2004420,21)]
  | 61, true => [(1,1066834,2), (16,2060634,16), (3,1547012,18), (24,2024116,30), (31,1388342,5), (2,515158,11), (8,103406,17), (5,790996,25), (20,206812,15), (13,885306,24), (22,326538,13), (4,1857158,22), (27,620976,21)]
  | 67, false => [(25,2032294,42), (56,1534264,9), (33,551838,35), (23,1235176,13), (32,1215520,14), (55,21704,3), (29,86818,34), (30,1350750,16), (3,1429372,50), (19,821612,62), (6,1145158,22), (21,1962026,40), (28,1815708,23), (48,772656,18), (44,1081004,5)]
  | 67, true => [(25,1628740,42), (56,100986,9), (33,1658942,35), (23,2028460,13), (32,1783166,14), (55,378578,3), (29,94644,34), (30,1065748,16), (3,1127072,50), (19,481372,62), (6,719888,22), (21,894028,40), (28,201972,23), (48,876418,18), (44,936822,5)]
  | 87, false => [(41,896918,11), (32,1729696,9), (9,1559350,2), (7,1577912,63), (24,1167320,14), (31,646240,49), (37,2043098,43), (38,606630,23), (3,1469820,60), (11,692468,48), (30,191198,17), (21,555562,33), (52,1648692,22), (16,864848,18), (36,1317476,4)]
  | 87, true => [(41,1736044,11), (32,84374,9), (9,1783034,2), (7,487942,63), (24,457954,14), (31,102116,49), (37,1494334,43), (38,1663140,23), (3,1027482,60), (11,770644,48), (30,2020816,17), (21,1382276,33), (52,722214,22), (16,168748,18), (36,628234,4)]
  | 91, false => [(1,704702,44), (24,882584,9), (25,505638,37), (55,316040,1), (8,538696,14), (63,846528,15), (61,1288962,59), (30,832990,46), (35,2039516,21), (11,1947956,25), (14,653838,40), (5,1327930,49), (44,1844332,3), (32,696224,18), (12,1489868,17)]
  | 91, true => [(1,1653624,44), (24,48938,9), (25,1672274,37), (55,54732,1), (8,1813814,14), (63,1800442,15), (61,974398,59), (30,1034892,46), (35,70834,21), (11,1519754,25), (14,1366160,40), (5,256026,49), (44,849754,3), (32,887054,18), (12,97876,17)]
  | 97, false => [(25,447014,20), (8,1408520,9), (17,1289262,29), (55,1514312,24), (56,841208,14), (15,1822384,22), (45,378578,56), (62,1783166,57), (19,2028460,1), (3,1314748,13), (14,171662,63), (13,1478962,50), (4,1752836,40), (40,403944,18), (44,1873644,58)]
  | 97, true => [(25,1826900,20), (8,193164,9), (17,1643224,29), (55,1578290,24), (56,1876744,14), (15,308794,22), (45,21704,56), (62,1215520,57), (19,1235176,1), (3,237998,13), (14,843172,63), (13,1014794,50), (4,386328,40), (40,907854,18), (44,540502,58)]
  | 103, false => [(17,164142,23), (24,1842072,9), (9,2005686,30), (15,1365424,26), (8,784008,14), (7,2040632,20), (37,384666,1), (62,1252734,44), (27,1491940,45), (59,1280516,33), (46,323694,42), (21,1538666,11), (36,1094308,46), (40,966504,18), (12,1969612,60)]
  | 103, true => [(17,1791582,23), (24,188334,9), (9,1673712,30), (15,471358,26), (8,1873204,14), (7,1811466,20), (37,651482,1), (62,631062,44), (27,20940,45), (59,1415098,33), (46,1567628,42), (21,162870,11), (36,846878,46), (40,611138,18), (12,376668,60)]
  | 109, false => [(41,795286,24), (56,1451064,9), (17,1705646,17), (15,218928,16), (24,963800,14), (23,910312,30), (21,1024106,39), (22,212438,19), (3,826812,52), (51,54732,56), (54,1813814,21), (5,1800442,45), (28,1774108,48), (40,195752,18), (52,1699508,34)]
  | 109, true => [(41,1636068,24), (56,174056,9), (17,1724684,17), (15,1651874,16), (24,1707538,14), (23,211632,30), (21,331982,39), (22,1085874,19), (3,1409404,52), (51,316040,56), (54,538696,21), (5,846528,45), (28,348112,48), (40,744934,18), (52,922166,34)]
  | 115, false => [(57,806790,55), (8,347400,9), (49,590478,62), (7,1885432,11), (16,1201360,14), (23,954408,5), (37,651482,26), (22,631062,41), (51,20940,51), (27,1670052,63), (14,2013390,47), (21,508778,16), (4,1222276,29), (56,753336,18), (60,1693756,15)]
  | 115, true => [(57,1823574,55), (8,241626,9), (49,1604748,62), (7,1914220,11), (16,1768866,14), (23,510158,5), (37,384666,26), (22,1252734,41), (51,1491940,51), (27,211104,63), (14,675590,47), (21,620454,16), (4,483252,29), (56,984806,18), (60,547154,15)]
  | 117, false => [(25,1305446,13), (48,674992,9), (41,1681366,4), (39,1951768,37), (8,1831816,14), (47,408464,43), (45,1334802,42), (46,1111726,59), (3,305340,17), (19,1736044,29), (22,84374,61), (5,1783034,32), (12,1444428,26), (24,337496,18), (20,1256468,8)]
  | 117, true => [(25,1684978,13), (48,216212,9), (41,1767782,4), (39,394478,37), (8,291830,14), (47,161560,43), (45,1187466,42), (46,1924034,59), (3,1000776,17), (19,896918,29), (22,1729696,61), (5,1559350,32), (12,824346,26), (24,432424,18), (20,658738,8)]
  | _, _ => []

def eraseMasks20 : Nat → Bool → List Nat
  | 11, false => [6286535496253689744, 8740294775772435184, 7106578047554856936]
  | 11, true => [3306664050020808936, 7380523699265968952, 6832456473899414640]
  | 13, false => [6887238567363863832, 4407302102528772728, 2868407302305215400]
  | 13, true => [4086913057514466792, 8315443280214808984, 6663993620008738512]
  | 19, false => [15708399374979989322589728, 6137417077740377906166368, 13559611765969500375315904, 7856709018760480490519440]
  | 19, true => [16336307599823951298573712, 9165726439874457696292528, 18326730446011049528429920, 17235088838382178435078848]
  | 21, false => [5065138418545569243182128, 10201389039733906385561712, 6955481312308722906785216, 12772873387331961212820112]
  | 21, true => [6725622185313079605376400, 12318153048361044241050160, 2270376973213991119970784, 3327401988835754959884992]
  | 25, false => [8652907187916169282749744, 18444198688402591924362080, 17616733282506757888354256, 13433528094520111512275600]
  | 25, true => [8386203691543949371964816, 16691850451999419700931120, 12751976892749107918587232, 4795047351482774303241792]
  | 31, false => [743515175706264116778784, 861961832363087465506928, 1064544168978137148692176, 371757587853132058389392]
  | 31, true => [188175415753972119666064, 568658321875080730609328, 1011140793955320828092896, 736173364563230992219712]
  | 37, false => [31611976626554878451695449641056, 22657897352472997885530655662304, 34666332174889870568503627665792, 28808697200333147699604601775872, 15786201219942748506395868056096]
  | 37, true => [17489702065332038324705322772000, 33713031363809694836138317269088, 32941928582062815665887132530368, 25279385228935310464075505396096, 8725063958183919446520281256704]
  | 41, false => [15492231978092928927939150746720, 32290490658673563518911284522176, 25324626044724756393394550397344, 14955116861224702053620633642752, 28642543228849755072497303833120]
  | 41, true => [8198874216854697059506498217504, 17664121200528035399659692574816, 35287351731949250932119159051456, 22638508958457058425116902198144, 4753049483023004500511705338624]
  | 47, false => [4468866481730572223591102192704, 7025562216223311496366054416608, 12141152591549472613104901807520, 21083341913221432807977082267392, 1600587993475165802205731835424]
  | 47, true => [39293249871429952710912677422624, 3848092493835362242973158828640, 31559039293735002127331827676864, 19321407418989220528392105020288, 39909227498129338703539401462528]
  | 55, false => [36759960104316443646229868846144, 5114659223371425638400298493152, 26492308227216509734231221687680, 12380181958126129507558887959328, 18380000018324269825268561694240]
  | 55, true => [12046562202857510064128685696544, 34906696786634060937254668544608, 40021275404533390807268258756288, 38210082209242430105167125866880, 26305710652946168429407209730304]
  | 59, false => [6477276897885912077530994022464, 19195341548093727659176916167872, 39657096965339112407134604679584, 34925015063061452111998291946272, 22887202786315022769629409562144]
  | 59, true => [18975023625235365884022012438048, 22938000089036084796079414651488, 6619682383368809036858110923968, 5734500305315932042648825285504, 10120717519359779759736279494912]
  | 61, false => [40503805796930611104437027278944, 39175141825289211470821610628320, 4106731230730402243891175710112, 31062965758438686639365854572320, 20251903521818257733638703204896]
  | 61, true => [20369680549495502255983804474912, 1481806574352427869632354666592, 23212050936621188334739505575616, 26059104300124145295909805001600, 30487675889066058492651016777984]
  | 67, false => [72322406613806880369993162774917177472, 36851238646781163905601673714725331328, 73722921962423461159528669662575411968, 62375571642563261661781270627101345280, 39680556546266141132852757883133959168, 79361113170522504666879482461375313984]
  | 67, true => [42491422808792068042506936013562386496, 42683710927936577990029171111641163968, 1647151826173011453601385711232242048, 4644300756317572762107621701608317696, 10617824436579720372282009410479932928, 21235324275377615154993391427868855296]
  | 73, false => [6708616229847915152594463391240704192, 14746141006291548698767419701240836480, 29513046208623655497434503354337289024, 53667805497726965499399089620963984896, 23593922742469910743647864382797978624, 45879381605986946170809005095922051136]
  | 73, true => [23282274731900442517406795733575997504, 45256090734658928100940359525678588096, 6770822804232612433993874797059133824, 35473897012432586792445350064922405632, 69618561037706321471001274961837639168, 54166210897246107653079339171216264192]
  | 87, false => [44231012707078745642228041812244721792, 47580577952768866951693540968063340992, 51620724157953357677915333112572498688, 16841623438818680224402864213254387264, 74528550928435186395910130204117113856, 63986185686072320974210772712470231104]
  | 87, true => [2807875681487768400238162534612670528, 9498559180007867819831151752381147328, 16399561144124683918887639657183664512, 34128674802587946933541314226848965376, 64162299700538360325716052964685663744, 44604009923425918352861659645755821056]
  | 91, false => [60966064045822286576151279688646156416, 73621354812929641310690052328883532160, 63501350882802861608770473130104808256, 68239272463720609095781393831101642304, 15231212508072320312127267202380143616, 30483194282806942521649034375343257664]
  | 91, true => [64531220846924929647723428834712033344, 23369706560504006393548554000277383360, 46760506747747998242003833721522901376, 72895611436010063772532521569597369088, 37395501719933653063990207819664739840, 74790683993134645914148056777813429248]
  | 97, false => [80402261976229795642582324272399929536, 75754381962965135346076687305896665472, 65109263727109803952261473359493415680, 43797943533378422245868483903977592320, 2504201708544000972880647028808956992, 83390818556917323410395087874414487616]
  | 97, true => [74050198283406284973960605541381642304, 61721341036852641613099387878713729216, 39700998891285285211595809606547296640, 79381553112471497036751852607113569024, 72384055608367681475514990573499532800, 36350262770375330546864507276909184000]
  | 103, false => [56926863337597143316923808587365511296, 82998080701543248647673990918760862144, 30852743072636095572239042158668366592, 63035033589008364458539280834134447616, 42349477622375406632170923066182151232, 28473818758212580636685783011251861568]
  | 103, true => [60330454193770436967592472462871697472, 73966121894015890528353399684203096256, 4203807143630244365243773188068956544, 8428058957379211811227911366721839872, 18164576802356700789839182130814993920, 72046131299159607534678288367757657088]
  | 109, false => [10016150252225309056169900354415640768, 18703077500039935914569576193681822144, 36788472944179889888132151785329615680, 66229974296193722573585556126768731648, 46059804349071844860551244363182455872, 5008234850088132132359591621396146240]
  | 109, true => [35716967145639053242078850327536670784, 70083937028850226877223071086088429760, 68671364939178730264888670726697212288, 81819753973003349011626934687999830784, 78568916136562965019787333526679668224, 61047846582216574680983977829371839488]
  | 115, false => [36151136825799376982415857576217960576, 58935773410431738144801994780976128384, 32780185901956781075114042821441049344, 64230819289555645037501680225061611072, 79206773345722911329496700559679368256, 59956475149865979422347208087958337600]
  | 115, true => [56299901942095323708846822129251326016, 83653288262819570054728404144071715008, 82214896160019424928396015383813968256, 78009527925157877817051351940891714304, 41511325963084585142094737693838298624, 28160173265873821076078402028398937088]
  | 117, false => [44890557021463559409028033337709314240, 4710197792901206717655159373194363328, 51631024418205400299553102079444472576, 16841784361044685349234716715928696384, 75198159130623839781965789156580604992, 22434893877410300198681842451823863872]
  | 117, true => [4074440117197517875602674798580668480, 9478108228961651908160942740056187072, 16399556002762611656636529749481707904, 34128345151141004769873815997432374016, 65534408635863188359870520572070481408, 44582900517423618559449378899690226688]
  | 257, false => [0, 5709077884439019562983799758531600717661077760, 11440543626367714088625133986720686846379098880, 22881174365021380219906522971377784141828458240, 1512995364689253980630658066051280499544689020672, 3031699807261617732546105412336446310105957932800, 6063422002380719927475600220663250868604903964416, 12126844091873725786711447092672767722612115275520]
  | 257, true => [0, 5709077884439019562983799758531600717661077760, 17149447286234829566296423749379466665899655680, 40007885344622726652920392259354123600390128640, 1541517408021482812163806834101530706126938834944, 3083034816044294872605808187727707701954958856192, 6166069632089924165504259826156020080535541915648, 12332139264181177559004304568185016025725402103808]
  | _, _ => []

def revCore21_20 : Program := [
  .CX 20 16, .CX 38 16, .CX 21 16, .CX 23 16, .CX 35 16, .CX 26 16,
  .CX 27 16, .CX 29 16, .CX 32 16, .CX 33 16, .CX 2 1, .CX 2 0,
  .CX 2 3, .CCX 16 1 2, .CX 2 3, .CX 2 0, .CX 2 1, .CX 19 16,
  .CX 37 16, .CX 20 16, .CX 38 16, .CX 25 16, .CX 26 16, .CX 31 16,
  .CX 32 16, .CX 1 0, .CX 2 0, .CX 3 0, .CCX 16 0 3, .CX 3 0,
  .CX 2 0, .CX 1 0, .CX 20 16, .CX 38 16, .CX 21 16, .CX 23 16,
  .CX 35 16, .CX 26 16, .CX 27 16, .CX 29 16, .CX 32 16, .CX 33 16,
  .CX 3 2, .CX 3 1, .CCX 16 2 3, .CX 3 1, .CX 3 2, .CX 19 16,
  .CX 37 16, .CX 20 16, .CX 38 16, .CX 22 16, .CX 34 16, .CX 23 16,
  .CX 35 16, .CX 25 16, .CX 26 16, .CX 28 16, .CX 29 16, .CX 31 16,
  .CX 32 16, .CX 0 1, .CX 0 2, .CCX 16 3 0, .CX 0 2, .CX 0 1,
  .CX 20 16, .CX 38 16, .CX 21 16, .CX 23 16, .CX 35 16, .CX 26 16,
  .CX 27 16, .CX 29 16, .CX 32 16, .CX 33 16, .CX 0 3, .CCX 16 1 0,
  .CX 0 3, .CX 19 16, .CX 37 16, .CX 21 16, .CX 23 16, .CX 35 16,
  .CX 25 16, .CX 27 16, .CX 29 16, .CX 31 16, .CX 33 16, .CX 2 0,
  .CX 3 0, .CCX 16 0 2, .CX 3 0, .CX 2 0, .CX 20 16, .CX 38 16,
  .CX 21 16, .CX 23 16, .CX 35 16, .CX 26 16, .CX 27 16, .CX 29 16,
  .CX 32 16, .CX 33 16, .CX 2 1, .CCX 16 1 0, .CX 2 1, .CX 19 16,
  .CX 37 16, .CX 21 16, .CX 22 16, .CX 34 16, .CX 25 16, .CX 27 16,
  .CX 28 16, .CX 31 16, .CX 33 16
]

def revCore31_20 : Program := [
  .CX 21 16, .CX 36 16, .CX 26 16, .CX 31 16, .CX 0 1, .CX 0 2,
  .CCX 16 3 0, .CX 0 2, .CX 0 1, .CX 19 16, .CX 34 16, .CX 20 16,
  .CX 35 16, .CX 21 16, .CX 36 16, .CX 24 16, .CX 25 16, .CX 26 16,
  .CX 29 16, .CX 30 16, .CX 31 16, .CX 3 1, .CCX 16 1 3, .CX 3 1,
  .CX 19 16, .CX 34 16, .CX 22 16, .CX 37 16, .CX 24 16, .CX 27 16,
  .CX 29 16, .CX 32 16, .CX 2 1, .CCX 16 1 2, .CX 2 1, .CX 19 16,
  .CX 34 16, .CX 20 16, .CX 35 16, .CX 24 16, .CX 25 16, .CX 29 16,
  .CX 30 16, .CX 1 2, .CX 1 3, .CCX 16 0 1, .CX 1 3, .CX 1 2,
  .CX 19 16, .CX 34 16, .CX 20 16, .CX 35 16, .CX 21 16, .CX 36 16,
  .CX 24 16, .CX 25 16, .CX 26 16, .CX 29 16, .CX 30 16, .CX 31 16,
  .CX 2 0, .CCX 16 0 2, .CX 2 0, .CX 19 16, .CX 34 16, .CX 22 16,
  .CX 37 16, .CX 24 16, .CX 27 16, .CX 29 16, .CX 32 16, .CX 0 2,
  .CX 0 3, .CCX 16 1 0, .CX 0 3, .CX 0 2, .CX 20 16, .CX 35 16,
  .CX 22 16, .CX 37 16, .CX 25 16, .CX 27 16, .CX 30 16, .CX 32 16,
  .CX 3 2, .CCX 16 2 3, .CX 3 2, .CX 19 16, .CX 34 16, .CX 21 16,
  .CX 36 16, .CX 22 16, .CX 37 16, .CX 24 16, .CX 26 16, .CX 27 16,
  .CX 29 16, .CX 31 16, .CX 32 16
]

def orderNineSix20 : Program := [
  .CX 0 1, .CX 0 2, .CX 5 2, .CX 20 16, .CX 38 16, .CX 21 16,
  .CX 24 16, .CX 25 16, .CX 34 16, .CX 29 16, .CX 30 16, .CX 33 16,
  .CCX 16 2 0, .CX 5 2, .CX 0 2, .CX 0 1, .CX 5 2, .CX 5 3,
  .CCX 16 3 5, .CX 5 3, .CX 4 2, .CX 0 2, .CX 21 16, .CX 26 16,
  .CX 35 16, .CX 30 16, .CCX 16 2 1, .CX 0 2, .CX 4 2, .CX 3 2,
  .CX 1 2, .CX 20 16, .CX 38 16, .CX 21 16, .CX 22 16, .CX 23 16,
  .CX 29 16, .CX 30 16, .CX 31 16, .CX 32 16, .CCX 16 2 4, .CX 1 2,
  .CX 3 2, .CX 5 2, .CX 3 4, .CX 3 5, .CX 5 0, .CX 21 16,
  .CX 26 16, .CX 35 16, .CX 30 16, .CCX 16 0 3, .CX 5 0, .CX 3 5,
  .CX 3 4, .CX 2 4, .CX 2 3, .CX 2 0, .CX 21 16, .CX 26 16,
  .CX 35 16, .CX 30 16, .CCX 16 0 2, .CX 2 0, .CX 22 16, .CX 23 16,
  .CX 24 16, .CX 25 16, .CX 34 16, .CX 31 16, .CX 32 16, .CX 33 16,
  .CCX 16 4 2, .CX 2 3, .CX 2 4, .CX 0 1, .CX 0 2, .CX 0 3,
  .CX 19 16, .CX 37 16, .CX 22 16, .CX 25 16, .CX 34 16, .CX 28 16,
  .CX 31 16, .CCX 16 3 0, .CX 0 3, .CX 0 2, .CX 0 1, .CX 4 1,
  .CX 4 5, .CCX 16 5 4, .CX 4 5, .CX 4 1, .CX 1 2, .CX 2 0,
  .CX 3 0, .CX 4 0, .CX 21 16, .CX 26 16, .CX 35 16, .CX 30 16,
  .CCX 16 0 1, .CX 4 0, .CX 3 0, .CX 2 0, .CX 1 3, .CX 20 16,
  .CX 38 16, .CX 22 16, .CX 23 16, .CX 26 16, .CX 35 16, .CX 29 16,
  .CX 31 16, .CX 32 16, .CCX 16 3 1, .CX 1 3, .CX 1 2, .CX 0 4,
  .CX 21 16, .CX 26 16, .CX 35 16, .CX 30 16, .CCX 16 4 0, .CX 0 4,
  .CX 3 1, .CX 5 1, .CX 21 16, .CX 26 16, .CX 35 16, .CX 30 16,
  .CCX 16 1 2, .CX 5 1, .CX 3 1, .CX 19 16, .CX 37 16, .CX 20 16,
  .CX 38 16, .CX 23 16, .CX 25 16, .CX 34 16, .CX 26 16, .CX 35 16,
  .CX 28 16, .CX 29 16, .CX 32 16
]

def primaryShift8_20 : Program := [
  .CX 19 16, .CX 35 16, .CX 21 16, .CX 37 16, .CX 23 16, .CX 25 16,
  .CX 27 16, .CX 29 16, .CX 31 16, .CX 33 16, .CCX 16 0 1, .CCX 16 2 3,
  .CCX 16 4 5, .CCX 16 6 7, .CX 20 16, .CX 36 16, .CX 21 16, .CX 37 16,
  .CX 24 16, .CX 25 16, .CX 28 16, .CX 29 16, .CX 32 16, .CX 33 16,
  .CX 1 0, .CCX 16 0 2, .CX 1 0, .CX 5 4, .CCX 16 4 6, .CX 5 4,
  .CX 19 16, .CX 35 16, .CX 21 16, .CX 37 16, .CX 23 16, .CX 25 16,
  .CX 27 16, .CX 29 16, .CX 31 16, .CX 33 16, .CX 2 3, .CCX 16 1 2,
  .CX 2 3, .CX 6 7, .CCX 16 5 6, .CX 6 7, .CX 19 16, .CX 35 16,
  .CX 22 16, .CX 38 16, .CX 24 16, .CX 25 16, .CX 27 16, .CX 30 16,
  .CX 32 16, .CX 33 16, .CX 1 0, .CX 2 0, .CX 3 0, .CCX 16 0 4,
  .CX 3 0, .CX 2 0, .CX 1 0, .CX 19 16, .CX 35 16, .CX 23 16,
  .CX 27 16, .CX 31 16, .CX 3 1, .CX 4 5, .CCX 16 1 4, .CX 4 5,
  .CX 3 1, .CX 20 16, .CX 36 16, .CX 24 16, .CX 28 16, .CX 32 16,
  .CX 3 2, .CX 4 6, .CCX 16 2 4, .CX 4 6, .CX 3 2, .CX 21 16,
  .CX 37 16, .CX 25 16, .CX 29 16, .CX 33 16, .CX 4 5, .CX 4 6,
  .CX 4 7, .CCX 16 3 4, .CX 4 7, .CX 4 6, .CX 4 5, .CX 22 16,
  .CX 38 16, .CX 23 16, .CX 24 16, .CX 25 16, .CX 30 16, .CX 31 16,
  .CX 32 16, .CX 33 16
]

def pascalR8Steps20 (mir : Bool) : List R8Step :=
  if mir then [
    ⟨[8, 9, 10, 11, 12, 13, 14, 15], [(1,0), (2,0), (3,0), (4,0), (5,0), (6,0), (7,0)], 0, 8⟩,
    ⟨[7, 8, 9, 10, 11, 12, 13, 14], [(3,1), (5,1), (7,1), (8,9)], 1, 8⟩,
    ⟨[6, 7, 8, 9, 10, 11, 12, 13], [(3,2), (6,2), (7,2), (8,10)], 2, 8⟩,
    ⟨[5, 6, 7, 8, 9, 10, 11, 12], [(7,3), (8,9), (8,10), (8,11)], 3, 8⟩,
    ⟨[4, 5, 6, 7, 8, 9, 10, 11, 20], [(5,4), (6,4), (7,4), (8,12)], 4, 8⟩,
    ⟨[3, 4, 5, 6, 7, 8, 9, 10, 19, 20], [(7,5), (8,9), (8,12), (8,13)], 5, 8⟩,
    ⟨[2, 3, 4, 5, 6, 7, 8, 9, 18, 19, 20], [(7,6), (8,10), (8,12), (8,14)], 6, 8⟩,
    ⟨[1, 2, 3, 4, 5, 6, 7, 8, 17, 18, 19, 20], [(8,9), (8,10), (8,11), (8,12), (8,13), (8,14), (8,15)], 7, 8⟩
  ]
  else [
    ⟨[1, 2, 3, 4, 5, 6, 7, 8, 17, 18, 19, 20], [(1,0), (2,0), (3,0), (4,0), (5,0), (6,0), (7,0)], 0, 8⟩,
    ⟨[2, 3, 4, 5, 6, 7, 8, 9, 18, 19, 20], [(3,1), (5,1), (7,1), (8,9)], 1, 8⟩,
    ⟨[3, 4, 5, 6, 7, 8, 9, 10, 19, 20], [(3,2), (6,2), (7,2), (8,10)], 2, 8⟩,
    ⟨[4, 5, 6, 7, 8, 9, 10, 11, 20], [(7,3), (8,9), (8,10), (8,11)], 3, 8⟩,
    ⟨[5, 6, 7, 8, 9, 10, 11, 12], [(5,4), (6,4), (7,4), (8,12)], 4, 8⟩,
    ⟨[6, 7, 8, 9, 10, 11, 12, 13], [(7,5), (8,9), (8,12), (8,13)], 5, 8⟩,
    ⟨[7, 8, 9, 10, 11, 12, 13, 14], [(7,6), (8,10), (8,12), (8,14)], 6, 8⟩,
    ⟨[8, 9, 10, 11, 12, 13, 14, 15], [(8,9), (8,10), (8,11), (8,12), (8,13), (8,14), (8,15)], 7, 8⟩
  ]

def basisNetwork20 (n : Nat) : List (Nat × Nat) :=
  ((pivots20 n).zipIdx.flatMap (fun (row,i) => elimStep n i row)).reverse

def bilinearOp20 (d : Nat) (triple : Nat × Nat × Nat) : Program :=
  let (xm, tm, om) := triple
  let left := (selected d xm).map (fun i => Instr.CX i 16)
  let right := (selected 21 tm).map (fun k => Instr.CX (18 + k) 17)
  let compute := match selected d om with
    | [] => []
    | j0 :: rest =>
      let fan := rest.map (fun j => Instr.CX (8 + j0) (8 + j))
      fan ++ [Instr.CCX 16 17 (8 + j0)] ++ fan.reverse
  left ++ right ++ compute ++ right.reverse ++ left.reverse

def bilinearErase20 (d : Nat) (mask i : Nat) : Instr :=
  let pairs := (List.range 21).flatMap fun k => (List.range d).filterMap fun j =>
    if mask.testBit (k * d + j) then some (Correction.CZ (18 + k) (8 + j)) else none
  Instr.measureX i [] (.Z (8 + i) :: pairs)

def bilinearCore20 (p : Nat) (mirror : Bool) : Program :=
  let d := fieldDegree p
  let copy := (List.range d).map (fun i => Instr.CX i (8 + i))
  let ops := (products20 p mirror).flatMap (bilinearOp20 d)
  let erase := (List.range d).map (fun i => bilinearErase20 d ((eraseMasks20 p mirror).getD i 0) i)
  let move := (List.range d).flatMap (fun i => [Instr.CX (8 + i) i, Instr.CX i (8 + i)])
  copy ++ ops ++ erase ++ move

def fieldCore20 (p : Nat) (mirror : Bool) : Program :=
  if p == 21 then (if mirror then revCore21_20.reverse else revCore21_20)
  else if p == 31 then (if mirror then revCore31_20.reverse else revCore31_20)
  else if p == 73 then (if mirror then orderNineSix20.reverse else orderNineSix20)
  else if p == 257 then (if mirror then primaryShift8_20.reverse else primaryShift8_20)
  else bilinearCore20 p mirror

def fieldPlace20 (n offset q : Nat) : Wire :=
  if q < 8 then offset + q else if q < 18 then n + 21 + (q - 8) else n + (q - 18)

def r8Step20 (n off : Nat) (st : R8Step) : Program :=
  let toggle := st.tags.map (fun k => Instr.CX (n + k) (n + 29))
  let pre := st.pre.map (fun p => Instr.CX (off + p.1) (off + p.2))
  toggle ++ pre ++ [Instr.CCX (n + 29) (off + st.src) (off + st.dst)] ++ pre.reverse ++ toggle.reverse

def pascalR8_20 (n off : Nat) (mir : Bool) : Program :=
  (pascalR8Steps20 mir).flatMap (r8Step20 n off)

def primary20 (n offset p m : Nat) (mirror : Bool) : Program :=
  let d := fieldDegree p
  let scalar := (List.range m).flatMap fun j =>
    renameProgram (fieldPlace20 n (offset + d * j)) (fieldCore20 p mirror)
  let shift := if d == 8 && m == 2 then pascalR8_20 n offset mirror else []
  scalar ++ shift

def components20 (n : Nat) (mirror : Bool) : Nat → List (Nat × Nat) → Program
  | _, [] => []
  | offset, (p,m) :: tail => primary20 n offset p m mirror ++
      components20 n mirror (offset + fieldDegree p * m) tail

def logical20 (n : Nat) (mirror : Bool) : Program :=
  let basis := (basisNetwork20 n).map (fun (i,j) => Instr.CX i j)
  basis ++ components20 n mirror 0 (schedule20 n) ++ basis.reverse

def UsedField20 (p : Nat) : Prop :=
  p = 11 ∨ p = 13 ∨ p = 19 ∨ p = 21 ∨ p = 25 ∨ p = 31 ∨ p = 37 ∨ p = 41 ∨ p = 47 ∨ p = 55 ∨ p = 59 ∨ p = 61 ∨ p = 67 ∨ p = 73 ∨ p = 87 ∨ p = 91 ∨ p = 97 ∨ p = 103 ∨ p = 109 ∨ p = 115 ∨ p = 117 ∨ p = 257

def UsedWidth20 (n : Nat) : Prop :=
  n = 83 ∨ n = 93 ∨ n = 103 ∨ n = 112 ∨ n = 122

def measuredField20 : Nat → Nat × Nat × Nat × Nat
  | 11 => (6,3,272,272)
  | 13 => (6,3,274,274)
  | 19 => (9,4,420,421)
  | 21 => (7,0,117,117)
  | 25 => (9,4,421,420)
  | 31 => (7,0,99,99)
  | 37 => (13,5,666,660)
  | 41 => (13,5,664,674)
  | 47 => (13,5,667,670)
  | 55 => (13,5,647,663)
  | 59 => (13,5,661,675)
  | 61 => (13,5,664,671)
  | 67 => (15,6,882,804)
  | 73 => (13,0,147,147)
  | 87 => (15,6,849,849)
  | 91 => (15,6,839,861)
  | 97 => (15,6,844,874)
  | 103 => (15,6,864,904)
  | 109 => (15,6,865,795)
  | 115 => (15,6,888,896)
  | 117 => (15,6,853,853)
  | 257 => (12,0,104,104)
  | _ => (0,0,0,0)

def measuredCosts20 : Nat → Nat × Nat × Nat × Nat
  | 83 => (187,61,15377,15323)
  | 93 => (213,63,17847,17794)
  | 103 => (239,73,20878,20838)
  | 112 => (261,82,24168,24143)
  | 122 => (287,92,28051,28047)
  | _ => (0,0,0,0)

/-! ## Exact resource counts (symbolic, < 0.2s total) -/

theorem count_append (a b : Program) : count (a ++ b) = cadd (count a) (count b) := by
  simp only [count, cadd, toffoliCount_append, measurementCount_append, gateSlots_append]

private theorem count_reverse_cxs (p : Program) (h : ∀ i ∈ p, match i with | .CX _ _ => True | _ => False) :
    count p.reverse = count p := by
  induction p with
  | nil => rfl
  | cons i tail ih =>
    have hi := h i (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases i with
    | CX c t =>
      rw [List.reverse_cons, count_append, ht]
      simp only [count, cadd, toffoliCount, measurementCount, gateSlots, instructionSlots,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
      congr 1; omega
    | _ => exact hi.elim

theorem count_rename (f : Wire → Wire) (p : Program) : count (renameProgram f p) = count p := by
  have hs : gateSlots (renameProgram f p) = gateSlots p := by
    induction p with
    | nil => rfl
    | cons i tail ih =>
      simp only [renameProgram, List.map_cons, gateSlots, List.sum_cons] at ih ⊢
      have h1 : instructionSlots (renameInstr f i) = instructionSlots i := by
        cases i <;> simp [renameInstr, instructionSlots]
      rw [h1, ih]
  simp only [count, (renameProgram_counts f p).1, (renameProgram_counts f p).2, hs]

private theorem count_map_cx {α : Type} (f g : α → Wire) (xs : List α) :
    count (xs.map (fun x => Instr.CX (f x) (g x))) = ⟨0, 0, xs.length⟩ := by
  induction xs with
  | nil => rfl
  | cons x tail ih =>
    simp only [List.map_cons, count, toffoliCount, measurementCount, gateSlots, instructionSlots,
      List.sum_cons, List.length_cons] at ih ⊢
    obtain ⟨h1, h2, h3⟩ := Count.mk.inj ih
    rw [h1, h2, h3]
    congr 1; omega

private theorem count_map_cx_rev {α : Type} (f g : α → Wire) (xs : List α) :
    count (xs.map (fun x => Instr.CX (f x) (g x))).reverse = ⟨0, 0, xs.length⟩ := by
  rw [count_reverse_cxs _ (fun i hi => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp hi; trivial), count_map_cx]

private theorem count_flatMap {α : Type} (f : α → Program) (g : α → Count)
    (h : ∀ x, count (f x) = g x) (xs : List α) :
    count (xs.flatMap f) = csumBy g xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih =>
    simp only [List.flatMap_cons, csumBy, count_append, h, ih]

private def popCount (n mask : Nat) : Nat := (selected n mask).length

private def bilinearOpPrice (d : Nat) (triple : Nat × Nat × Nat) : Count :=
  let (xm, tm, om) := triple
  let lx := popCount d xm
  let lt := popCount 21 tm
  let lo := popCount d om
  match selected d om with
  | [] => ⟨0, 0, 2 * lx + 2 * lt⟩
  | _ :: _ => ⟨1, 0, 2 * lx + 2 * lt + 2 * (lo - 1) + 1⟩

private theorem bilinearOp20_count (d : Nat) (triple : Nat × Nat × Nat) :
    count (bilinearOp20 d triple) = bilinearOpPrice d triple := by
  obtain ⟨xm, tm, om⟩ := triple
  unfold bilinearOp20 bilinearOpPrice popCount
  rw [count_append, count_append, count_append, count_append,
    count_map_cx, count_map_cx, count_map_cx_rev, count_map_cx_rev]
  cases h : selected d om with
  | nil =>
    simp only [h, count, cadd, toffoliCount, measurementCount, gateSlots, List.map_nil, List.sum_nil]
    congr 1; omega
  | cons j0 rest =>
    rw [count_append, count_append, count_map_cx, count_map_cx_rev]
    have hccx : count [Instr.CCX 16 17 (8 + j0)] = ⟨1, 0, 1⟩ := rfl
    rw [hccx]
    simp only [h, cadd, List.length_cons, Nat.add_sub_cancel]
    congr 1; omega

private def eraseMaskCount (d mask : Nat) : Nat :=
  ((List.range 21).map fun k => ((List.range d).filter fun j => mask.testBit (k * d + j)).length).sum

private theorem filterMap_some_len {α β : Type} (p : α → Bool) (f : α → β) (xs : List α) :
    (xs.filterMap (fun x => if p x then some (f x) else none)).length = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> simp [hp, ih]

private theorem count_measureX (i : Wire) (c2 : List Correction) :
    count [Instr.measureX i [] c2] = ⟨0, 1, 1 + c2.length⟩ := by
  simp [count, toffoliCount, measurementCount, gateSlots, instructionSlots]

private theorem bilinearErase20_count (d : Nat) (masks : List Nat) (xs : List Nat) :
    count (xs.map (fun i => bilinearErase20 d (masks.getD i 0) i)) =
      csumBy (fun i => ⟨0, 1, 2 + eraseMaskCount d (masks.getD i 0)⟩) xs := by
  induction xs with
  | nil => rfl
  | cons i tail ih =>
    have h1 : count [bilinearErase20 d (masks.getD i 0) i] = ⟨0, 1, 2 + eraseMaskCount d (masks.getD i 0)⟩ := by
      unfold bilinearErase20
      rw [count_measureX]
      have hmap : ((List.range 21).flatMap fun k => (List.range d).filterMap fun j =>
          if ((masks.getD i 0)).testBit (k * d + j) then some (Correction.CZ (18 + k) (8 + j)) else none).length =
          eraseMaskCount d (masks.getD i 0) := by
        unfold eraseMaskCount
        rw [List.length_flatMap]
        congr 1
        apply List.map_congr_left
        intro k _
        exact filterMap_some_len _ _ _
      simp only [List.length_cons, hmap]
      exact congrArg (Count.mk 0 1) (by omega)
    change count ([bilinearErase20 d (masks.getD i 0) i] ++ tail.map (fun i => bilinearErase20 d (masks.getD i 0) i)) = _
    rw [count_append, h1, ih]
    rfl

private theorem bilinearCore20_count (p : Nat) (mir : Bool) :
    count (bilinearCore20 p mir) =
      cadd (⟨0, 0, fieldDegree p⟩)
        (cadd (csumBy (bilinearOpPrice (fieldDegree p)) (products20 p mir))
          (cadd (csumBy (fun i => ⟨0, 1, 2 + eraseMaskCount (fieldDegree p) ((eraseMasks20 p mir).getD i 0)⟩)
              (List.range (fieldDegree p)))
            (csumBy (fun _ => ⟨0, 0, 2⟩) (List.range (fieldDegree p))))) := by
  unfold bilinearCore20
  have hmv : count ((List.range (fieldDegree p)).flatMap fun i => [Instr.CX (8 + i) i, Instr.CX i (8 + i)]) =
      csumBy (fun _ => ⟨0, 0, 2⟩) (List.range (fieldDegree p)) :=
    count_flatMap (fun i => [Instr.CX (8 + i) i, Instr.CX i (8 + i)]) (fun _ => ⟨0, 0, 2⟩) (fun _ => rfl) _
  rw [count_append, count_append, count_append, count_map_cx, List.length_range,
    count_flatMap _ _ (bilinearOp20_count _), bilinearErase20_count, hmv]
  simp only [cadd]
  congr 1 <;> omega

def fieldPrice20 (p : Nat) (mir : Bool) : Count :=
  let x := measuredField20 p
  ⟨x.1, x.2.1, if mir then x.2.2.2 else x.2.2.1⟩

def r8StepPrice20 (st : R8Step) : Count :=
  ⟨1, 0, 2 * st.tags.length + 2 * st.pre.length + 1⟩

def r8Price20 (mir : Bool) : Count := csumBy r8StepPrice20 (pascalR8Steps20 mir)

def partsPrice20 (mir : Bool) (parts : List (Nat × Nat)) : Count :=
  csumBy (fun (p,m) =>
    cadd (cscale m (fieldPrice20 p mir))
      (if fieldDegree p == 8 && m == 2 then r8Price20 mir else czero)) parts

def listedPrice20 (n : Nat) (mir : Bool) : Count :=
  let z := measuredCosts20 n
  ⟨z.1, z.2.1, if mir then z.2.2.2 else z.2.2.1⟩

private theorem field20_count_rev (p : Nat) (hp : p = 21 ∨ p = 31 ∨ p = 73 ∨ p = 257) (mir : Bool) :
    count (fieldCore20 p mir) = fieldPrice20 p mir := by
  rcases hp with rfl | rfl | rfl | rfl <;> cases mir <;> decide +kernel

theorem field20_count (p : Nat) (hp : UsedField20 p) (mir : Bool) :
    count (fieldCore20 p mir) = fieldPrice20 p mir := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact field20_count_rev _ (by decide) mir
    | (change count (bilinearCore20 _ mir) = _; rw [bilinearCore20_count]; cases mir <;> decide +kernel)

private theorem r8Step20_count (n off : Nat) (st : R8Step) :
    count (r8Step20 n off st) = r8StepPrice20 st := by
  unfold r8Step20 r8StepPrice20
  have hccx : count [Instr.CCX (n + 29) (off + st.src) (off + st.dst)] = ⟨1, 0, 1⟩ := rfl
  rw [count_append, count_append, count_append, count_append,
    count_map_cx, count_map_cx, count_map_cx_rev, count_map_cx_rev, hccx]
  simp only [cadd]
  congr 1; omega

private theorem pascalR8_20_count (n off : Nat) (mir : Bool) :
    count (pascalR8_20 n off mir) = r8Price20 mir :=
  count_flatMap _ _ (r8Step20_count n off) _

private theorem primary20_count (n off p m : Nat) (mir : Bool)
    (hf : count (fieldCore20 p mir) = fieldPrice20 p mir) :
    count (primary20 n off p m mir) =
      cadd (cscale m (fieldPrice20 p mir))
        (if fieldDegree p == 8 && m == 2 then r8Price20 mir else czero) := by
  have hsc : ∀ (k : Nat) (o : Nat),
      count ((List.range k).flatMap fun j =>
        renameProgram (fieldPlace20 n (o + fieldDegree p * j)) (fieldCore20 p mir)) =
      cscale k (fieldPrice20 p mir) := by
    intro k; induction k with
    | zero => intro _; simp [cscale, count, toffoliCount, measurementCount, gateSlots]
    | succ k ih =>
      intro o
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, count_append, ih, count_rename, hf]
      simp only [cscale, cadd, Nat.succ_mul]
  unfold primary20
  rw [count_append, hsc]
  split_ifs with h
  · rw [pascalR8_20_count]
  · rfl

private theorem components20_count (n : Nat) (mir : Bool) (off : Nat) (parts : List (Nat × Nat))
    (h : ∀ pair ∈ parts, count (fieldCore20 pair.1 mir) = fieldPrice20 pair.1 mir) :
    count (components20 n mir off parts) = partsPrice20 mir parts := by
  induction parts generalizing off with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨p, m⟩ := pair
    simp only [components20, partsPrice20, csumBy, count_append]
    rw [primary20_count n off p m mir (h (p, m) (List.mem_cons_self ..)),
      ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

private theorem schedule20_fields (n : Nat) (hn : UsedWidth20 n) :
    ∀ pair ∈ schedule20 n, UsedField20 pair.1 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
    intro pair hp <;> simp only [schedule20, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [UsedField20]

private theorem elimStep_len (n i : Nat) (row : Nat × Nat) :
    (elimStep n i row).length = (if row.1 < n then 1 else 0) + popCount n row.2 := by
  unfold elimStep popCount
  rw [List.length_append, List.length_map]
  split_ifs <;> simp

private theorem map_zipIdx_fst {α β : Type} (f : α → β) (xs : List α) (k : Nat) :
    (xs.zipIdx k).map (fun x => f x.1) = xs.map f := by
  induction xs generalizing k with
  | nil => rfl
  | cons a xs ih => simp [List.zipIdx_cons, ih]

private theorem basis20_len (n : Nat) :
    (basisNetwork20 n).length =
      ((pivots20 n).map (fun row => (if row.1 < n then 1 else 0) + popCount n row.2)).sum := by
  have hstep : ∀ (xs : List ((Nat × Nat) × Nat)),
      (xs.flatMap (fun x => elimStep n x.2 x.1)).length =
        (xs.map (fun x => (if x.1.1 < n then 1 else 0) + popCount n x.1.2)).sum := by
    intro xs; induction xs with
    | nil => rfl
    | cons x tail ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ih, elimStep_len]
  unfold basisNetwork20
  rw [List.length_reverse]
  exact (hstep ((pivots20 n).zipIdx)).trans
    (congrArg List.sum (map_zipIdx_fst (fun row : Nat × Nat => (if row.1 < n then 1 else 0) + popCount n row.2) (pivots20 n) 0))

theorem logical20_metrics (n : Nat) (hn : UsedWidth20 n) (mir : Bool) :
    count (logical20 n mir) = listedPrice20 n mir := by
  have hc := components20_count n mir 0 (schedule20 n)
    (fun pair hp => field20_count pair.1 (schedule20_fields n hn pair hp) mir)
  have hlog : count (logical20 n mir) =
      cadd ⟨0, 0, (basisNetwork20 n).length⟩
        (cadd (partsPrice20 mir (schedule20 n)) ⟨0, 0, (basisNetwork20 n).length⟩) := by
    unfold logical20
    rw [count_append, count_append, count_map_cx, count_map_cx_rev, hc]
    simp only [cadd]; congr 1; omega
  rw [hlog, basis20_len]
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> cases mir <;> decide +kernel

/-! ## Physical soundness & wire-range bounds (`Fits (· < n + 31)`) -/

def fieldScope20 (d q : Nat) : Prop := q < d ∨ (8 ≤ q ∧ q < 39)

private theorem fits_append {P : Wire → Prop} {a b : Program} (ha : Fits P a) (hb : Fits P b) :
    Fits P (a ++ b) := fun i hi => (List.mem_append.mp hi).elim (ha i) (hb i)

private theorem fits_reverse {P : Wire → Prop} {a : Program} (ha : Fits P a) :
    Fits P a.reverse := fun i hi => ha i (List.mem_reverse.mp hi)

private theorem fits_nil {P : Wire → Prop} : Fits P [] := fun _ h => (List.not_mem_nil h).elim

private theorem fits_flatMap {α : Type} {P : Wire → Prop} {f : α → Program} {xs : List α}
    (h : ∀ x ∈ xs, Fits P (f x)) : Fits P (xs.flatMap f) := by
  intro i hi
  obtain ⟨x, hx, hix⟩ := List.mem_flatMap.mp hi
  exact h x hx i hix

theorem support {S : Wire → Prop} {p : Program} (h : Fits S p) : ∀ q ∈ wires p, S q := by
  induction p with
  | nil => simp [wires]
  | cons i p ih =>
    intro q hq
    rcases Finset.mem_union.mp hq with a | a
    · exact (h i (by simp)).2 q a
    · exact ih (fun j hj => h j (List.mem_cons_of_mem i hj)) q a

theorem fits_rename {P Q : Wire → Prop} {f : Wire → Wire} {pr : Program}
    (hf : Fits P pr) (hmap : ∀ q, P q → Q (f q))
    (hinj : ∀ a, P a → ∀ b, P b → f a = f b → a = b) :
    Fits Q (renameProgram f pr) := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  obtain ⟨hp, hq⟩ := hf j hj
  constructor
  · cases j with
    | X t => trivial
    | measureX t c1 c2 => trivial
    | CX c t =>
      intro heq
      exact hp (hinj c (hq c (by simp [Instr.wires])) t (hq t (by simp [Instr.wires])) heq)
    | CCX a b t =>
      have sa := hq a (by simp [Instr.wires])
      have sb := hq b (by simp [Instr.wires])
      have st := hq t (by simp [Instr.wires])
      exact ⟨fun h => hp.1 (hinj a sa t st h), fun h => hp.2 (hinj b sb t st h)⟩
  · intro q hqm
    rw [renameInstr_support, Finset.mem_image] at hqm
    obtain ⟨w, hw, rfl⟩ := hqm
    exact hmap w (hq w hw)

private theorem mem_selected {n mask q : Nat} (h : q ∈ selected n mask) : q < n ∧ mask.testBit q = true := by
  simp only [selected, List.mem_filter, List.mem_range] at h
  exact h

private theorem correctionWires_forall {P : Wire → Prop} {cs : List Correction}
    (h : ∀ c ∈ cs, match c with | .Z t => P t | .CZ a b => P a ∧ P b) :
    ∀ q ∈ correctionWires cs, P q := by
  induction cs with
  | nil => intro _ hq; simp [correctionWires] at hq
  | cons c tail ih =>
    intro q hq
    have hc := h c (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases c with
    | Z t =>
      simp only [correctionWires, Finset.mem_union, Finset.mem_singleton] at hq
      rcases hq with rfl | hq
      · exact hc
      · exact ht q hq
    | CZ a b =>
      simp only [correctionWires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with (rfl | rfl) | hq
      · exact hc.1
      · exact hc.2
      · exact ht q hq

private theorem bilinearCore20_fits (p : Nat) (hd : fieldDegree p ≤ 8) (mir : Bool) :
    Fits (fieldScope20 (fieldDegree p)) (bilinearCore20 p mir) := by
  set d := fieldDegree p
  have hcopy : Fits (fieldScope20 d) ((List.range d).map (fun i => Instr.CX i (8 + i))) := by
    intro g hg; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg; rw [List.mem_range] at hi
    refine ⟨by simp [RecordedQuantum.PhysicalInstr, ProperGate], fun q hq => ?_⟩
    simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> (unfold fieldScope20; unfold Wire at *; omega)
  have hop : ∀ triple, Fits (fieldScope20 d) (bilinearOp20 d triple) := by
    intro ⟨xm, tm, om⟩
    have hl : Fits (fieldScope20 d) ((selected d xm).map (fun i => Instr.CX i 16)) := by
      intro g hg; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg; have := (mem_selected hi).1
      refine ⟨by simp [RecordedQuantum.PhysicalInstr, ProperGate]; unfold Wire at *; omega, fun q hq => ?_⟩
      simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> (unfold fieldScope20; unfold Wire at *; omega)
    have hr : Fits (fieldScope20 d) ((selected 21 tm).map (fun k => Instr.CX (18 + k) 17)) := by
      intro g hg; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg; have := (mem_selected hk).1
      refine ⟨by simp [RecordedQuantum.PhysicalInstr, ProperGate]; unfold Wire at *; omega, fun q hq => ?_⟩
      simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> (unfold fieldScope20; unfold Wire at *; omega)
    have hc : Fits (fieldScope20 d) (match selected d om with
      | [] => []
      | j0 :: rest =>
        let fan := rest.map (fun j => Instr.CX (8 + j0) (8 + j))
        fan ++ [Instr.CCX 16 17 (8 + j0)] ++ fan.reverse) := by
      have hnd : (selected d om).Nodup := (List.nodup_range).filter _
      cases hs : selected d om with
      | nil => exact fits_nil
      | cons j0 rest =>
        rw [hs, List.nodup_cons] at hnd
        have hj0 : j0 < d := (mem_selected (hs ▸ List.mem_cons_self ..)).1
        have hfan : Fits (fieldScope20 d) (rest.map (fun j => Instr.CX (8 + j0) (8 + j))) := by
          intro g hg; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
          have hjd : j < d := (mem_selected (hs ▸ List.mem_cons_of_mem _ hj)).1
          have hne : j0 ≠ j := fun e => hnd.1 (e ▸ hj)
          refine ⟨by simp [RecordedQuantum.PhysicalInstr, ProperGate]; omega, fun q hq => ?_⟩
          simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl <;> (unfold fieldScope20; unfold Wire at *; omega)
        have hccx : Fits (fieldScope20 d) [Instr.CCX 16 17 (8 + j0)] := by
          intro g hg; simp only [List.mem_singleton] at hg; subst hg
          refine ⟨by simp [RecordedQuantum.PhysicalInstr, ProperGate]; unfold Wire at *; omega, fun q hq => ?_⟩
          simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl <;> (unfold fieldScope20; unfold Wire at *; omega)
        exact fits_append (fits_append hfan hccx) (fits_reverse hfan)
    exact fits_append (fits_append (fits_append (fits_append hl hr) hc) (fits_reverse hr)) (fits_reverse hl)
  have herase : Fits (fieldScope20 d) ((List.range d).map (fun i => bilinearErase20 d ((eraseMasks20 p mir).getD i 0) i)) := by
    intro g hg; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg; rw [List.mem_range] at hi
    unfold bilinearErase20
    refine ⟨trivial, fun q hq => ?_⟩
    simp only [Instr.wires, correctionWires, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | hq
    · exact Or.inl hi
    · unfold fieldScope20; unfold Wire at *; omega
    · refine correctionWires_forall (fun c hc => ?_) q hq
      simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range] at hc
      obtain ⟨k, hk, j, hj, hite⟩ := hc
      split_ifs at hite with hbit
      · simp only [Option.some.injEq] at hite; subst hite
        exact ⟨by unfold fieldScope20; unfold Wire at *; omega, by unfold fieldScope20; unfold Wire at *; omega⟩
  have hmove : Fits (fieldScope20 d) ((List.range d).flatMap (fun i => [Instr.CX (8 + i) i, Instr.CX i (8 + i)])) := by
    apply fits_flatMap; intro i hi; rw [List.mem_range] at hi
    intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · refine ⟨by simp [RecordedQuantum.PhysicalInstr, ProperGate], fun q hq => ?_⟩
      simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> (unfold fieldScope20; unfold Wire at *; omega)
    · refine ⟨by simp [RecordedQuantum.PhysicalInstr, ProperGate], fun q hq => ?_⟩
      simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> (unfold fieldScope20; unfold Wire at *; omega)
  exact fits_append (fits_append (fits_append hcopy (fits_flatMap (fun t _ => hop t))) herase) hmove

private def revCoreGood (d : Nat) (pr : Program) : Bool :=
  pr.all fun i =>
    let okW := fun w => w < d || (8 <= w && w < 39)
    match i with
    | .X t => okW t
    | .CX c t => okW c && okW t && c != t
    | .CCX a b t => okW a && okW b && okW t && a != t && b != t
    | _ => false

private theorem revCores_good :
    revCoreGood 4 revCore21_20 = true ∧
    revCoreGood 4 revCore31_20 = true ∧
    revCoreGood 6 orderNineSix20 = true ∧
    revCoreGood 8 primaryShift8_20 = true := by decide +kernel

private theorem fits_of_revCoreGood {d : Nat} {pr : Program} (h : revCoreGood d pr = true) :
    Fits (fieldScope20 d) pr := by
  have hall := List.all_eq_true.mp h
  intro i hi
  have hg := hall i hi
  have toS : ∀ w, (decide (w < d) || (decide (8 ≤ w) && decide (w < 39))) = true → fieldScope20 d w := by
    intro w hw; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hw; exact hw
  cases i with
  | X t =>
    refine ⟨trivial, fun q hq => ?_⟩
    simp only [Instr.wires, Finset.mem_singleton] at hq; subst hq; exact toS _ hg
  | CX c t =>
    simp only [Bool.and_eq_true, bne_iff_ne] at hg
    refine ⟨hg.2, fun q hq => ?_⟩
    simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact toS _ hg.1.1
    · exact toS _ hg.1.2
  | CCX a b t =>
    simp only [Bool.and_eq_true, bne_iff_ne] at hg
    refine ⟨⟨hg.1.2, hg.2⟩, fun q hq => ?_⟩
    simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact toS _ hg.1.1.1.1
    · exact toS _ hg.1.1.1.2
    · exact toS _ hg.1.1.2
  | measureX _ _ _ => simp at hg

private theorem used_degree20 (p : Nat) (hp : UsedField20 p) : 0 < fieldDegree p ∧ fieldDegree p ≤ 8 := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem fits_core20 (p : Nat) (hp : UsedField20 p) (mir : Bool) :
    Fits (fieldScope20 (fieldDegree p)) (fieldCore20 p mir) := by
  have hd := (used_degree20 p hp).2
  unfold fieldCore20
  by_cases h21 : p = 21
  · subst h21; cases mir
    · exact fits_of_revCoreGood revCores_good.1
    · exact fits_reverse (fits_of_revCoreGood revCores_good.1)
  · by_cases h31 : p = 31
    · subst h31; cases mir
      · exact fits_of_revCoreGood revCores_good.2.1
      · exact fits_reverse (fits_of_revCoreGood revCores_good.2.1)
    · by_cases h73 : p = 73
      · subst h73; cases mir
        · exact fits_of_revCoreGood revCores_good.2.2.1
        · exact fits_reverse (fits_of_revCoreGood revCores_good.2.2.1)
      · by_cases h257 : p = 257
        · subst h257; cases mir
          · exact fits_of_revCoreGood revCores_good.2.2.2
          · exact fits_reverse (fits_of_revCoreGood revCores_good.2.2.2)
        · simp only [beq_iff_eq, h21, h31, h73, h257, ↓reduceIte]
          exact bilinearCore20_fits p hd mir

private theorem fieldPlace20_maps {n off d : Nat} (sd : d ≤ 8) (endp : off + d ≤ n) :
    (∀ q, fieldScope20 d q → fieldPlace20 n off q < n + 31) ∧
    (∀ a, fieldScope20 d a → ∀ b, fieldScope20 d b → fieldPlace20 n off a = fieldPlace20 n off b → a = b) := by
  constructor
  · intro q hq; unfold fieldScope20 at hq; unfold fieldPlace20; unfold Wire at *; split_ifs <;> omega
  · intro a ha b hb heq
    unfold fieldScope20 at ha hb
    unfold fieldPlace20 at heq
    unfold Wire at *
    by_cases ha8 : a < 8 <;> by_cases ha18 : a < 18 <;>
      by_cases hb8 : b < 8 <;> by_cases hb18 : b < 18 <;>
      simp only [ha8, ha18, hb8, hb18, ↓reduceIte] at heq <;> omega

private def r8Step20Good (st : R8Step) : Bool :=
  st.tags.all (· < 21) &&
  st.pre.all (fun p => p.1 < 16 && p.2 < 16 && p.1 != p.2) &&
  st.src < 16 && st.dst < 16 && st.src != st.dst

private theorem pascalR8Steps20_good : ∀ mir : Bool, (pascalR8Steps20 mir).all r8Step20Good = true := by
  decide +kernel

private theorem pascalR8_20_fits (n off : Nat) (mir : Bool) (endp : off + 16 ≤ n) :
    Fits (· < n + 31) (pascalR8_20 n off mir) := by
  apply fits_flatMap
  intro st hst
  have h := List.all_eq_true.mp (pascalR8Steps20_good mir) st hst
  unfold r8Step20Good at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨ht, hpre⟩, hsrc⟩, hdst⟩, hne⟩ := h
  have htog : Fits (· < n + 31) (st.tags.map (fun k => Instr.CX (n + k) (n + 29))) := by
    intro i hi; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi; have := ht k hk
    refine ⟨by change n + k ≠ n + 29; omega, fun q hq => ?_⟩
    simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> (unfold Wire at *; omega)
  have hpr : Fits (· < n + 31) (st.pre.map (fun p => Instr.CX (off + p.1) (off + p.2))) := by
    intro i hi; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi; have := hpre p hp
    refine ⟨by change off + p.1 ≠ off + p.2; omega, fun q hq => ?_⟩
    simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> (unfold Wire at *; omega)
  have hccx : Fits (· < n + 31) [Instr.CCX (n + 29) (off + st.src) (off + st.dst)] := by
    intro i hi; simp only [List.mem_singleton] at hi; subst hi
    refine ⟨⟨by change n + 29 ≠ off + st.dst; omega, by change off + st.src ≠ off + st.dst; omega⟩, fun q hq => ?_⟩
    simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> (unfold Wire at *; omega)
  exact fits_append (fits_append (fits_append (fits_append htog hpr) hccx) (fits_reverse hpr)) (fits_reverse htog)

private def pivots20Good (n : Nat) : Bool :=
  (pivots20 n).length == n &&
  ((pivots20 n).zipIdx).all (fun ((donor, mask), i) =>
    donor <= n && donor != i && !(mask.testBit i))

private theorem pivots20_good_checked (n : Nat) (hn : UsedWidth20 n) : pivots20Good n = true := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem basis20_pairs (n : Nat) (hn : UsedWidth20 n) :
    ∀ o ∈ basisNetwork20 n, o.1 < n ∧ o.2 < n ∧ o.1 ≠ o.2 := by
  have hg := pivots20_good_checked n hn
  unfold pivots20Good at hg
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hg
  obtain ⟨hlen, hall⟩ := hg
  intro o ho
  unfold basisNetwork20 at ho
  rw [List.mem_reverse, List.mem_flatMap] at ho
  obtain ⟨⟨⟨donor, mask⟩, i⟩, hmem, helim⟩ := ho
  have hi : i < n := by
    have hidx := List.mem_zipIdx hmem
    omega
  have hp := hall ((donor, mask), i) hmem
  simp only [decide_eq_true_eq, bne_iff_ne, Bool.not_eq_true'] at hp
  obtain ⟨⟨hdle, hdne⟩, hbit⟩ := hp
  unfold elimStep at helim
  rcases List.mem_append.mp helim with h1 | h2
  · split_ifs at h1 with hlt
    · simp only [List.mem_singleton] at h1; subst h1; exact ⟨hlt, hi, hdne⟩
    · exact (List.not_mem_nil h1).elim
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h2
    obtain ⟨hjlt, hjbit⟩ := mem_selected hj
    refine ⟨hi, hjlt, ?_⟩
    intro heq; dsimp only at heq; subst heq; rw [hbit] at hjbit; cases hjbit

private theorem schedule20_extent (n : Nat) (hn : UsedWidth20 n) :
    ((schedule20 n).map (fun x => fieldDegree x.1 * x.2)).sum = n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide

theorem logical20_fits (n : Nat) (hn : UsedWidth20 n) (mir : Bool) :
    Fits (· < n + 31) (logical20 n mir) := by
  have hb : Fits (· < n + 31) ((basisNetwork20 n).map (fun (i, j) => Instr.CX i j)) := by
    intro i hi; obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hi
    have hp := basis20_pairs n hn o ho
    refine ⟨hp.2.2, fun q hq => ?_⟩
    simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> (unfold Wire at *; omega)
  have hcomp : ∀ (off : Nat) (parts : List (Nat × Nat)),
      off + (parts.map (fun x => fieldDegree x.1 * x.2)).sum ≤ n →
      (∀ pair ∈ parts, UsedField20 pair.1) →
      Fits (· < n + 31) (components20 n mir off parts) := by
    intro off parts
    induction parts generalizing off with
    | nil => intro _ _; exact fits_nil
    | cons pair tail ih =>
      intro hend huf
      obtain ⟨p, m⟩ := pair
      simp only [List.map_cons, List.sum_cons] at hend
      have hp := huf (p, m) (List.mem_cons_self ..)
      have hd := used_degree20 p hp
      have hsc : ∀ (k : Nat) (o : Nat), o + fieldDegree p * k ≤ n →
          Fits (· < n + 31) ((List.range k).flatMap fun j =>
            renameProgram (fieldPlace20 n (o + fieldDegree p * j)) (fieldCore20 p mir)) := by
        intro k; induction k with
        | zero => intro _ _; exact fits_nil
        | succ k ihk =>
          intro o ho
          rw [Nat.mul_succ] at ho
          rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
          refine fits_append (ihk o (by omega)) ?_
          have hm := fieldPlace20_maps hd.2 (show o + fieldDegree p * k + fieldDegree p ≤ n by omega)
          exact fits_rename (fits_core20 p hp mir) hm.1 hm.2
      have hprim : Fits (· < n + 31) (primary20 n off p m mir) := by
        unfold primary20
        refine fits_append (hsc m off (by omega)) ?_
        split_ifs with h8
        · simp only [Bool.and_eq_true, beq_iff_eq] at h8
          exact pascalR8_20_fits n off mir (by rw [h8.1, h8.2] at hend; omega)
        · exact fits_nil
      exact fits_append hprim (ih (off + fieldDegree p * m) (by omega)
        (fun x hx => huf x (List.mem_cons_of_mem _ hx)))
  have hcs := hcomp 0 (schedule20 n) (by rw [Nat.zero_add, schedule20_extent n hn]) (schedule20_fields n hn)
  exact fits_append (fits_append hb hcs) (fits_reverse hb)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel20

end
end
-- ==== end CRTBarrel20 ====

-- ==== begin CRTBarrel20Proof ====
section

/-! Semantic soundness, basis/prototype certificates, and generic physical barrel theorem
    for the 21-tag CRT barrel shifter (`CRTBarrel20`). -/

set_option autoImplicit false

section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Challenge

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel20

/-! ## Linear evaluation & CNOT reversal -/

def rowValue (x : Nat → Bool) (row : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => rowValue x row n ^^ (row.testBit n && x n)

theorem rowValue_xor (x : Nat → Bool) (a b n : Nat) :
    rowValue x (a ^^^ b) n = (rowValue x a n ^^ rowValue x b n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rowValue, ih, Nat.testBit_xor]
    cases rowValue x a n <;> cases rowValue x b n <;> cases a.testBit n <;>
      cases b.testBit n <;> cases x n <;> rfl

theorem rowValue_zero (x : Nat → Bool) (n : Nat) : rowValue x 0 n = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rowValue, ih]

theorem rowValue_congr (x : Nat → Bool) (d a b : Nat) (eq : ∀ i < d, a.testBit i = b.testBit i) :
    rowValue x a d = rowValue x b d := by
  induction d with
  | zero => rfl
  | succ w ih => rw [rowValue, rowValue, eq w (by omega), ih (fun i hi => eq i (by omega))]

def cnotProgram (ops : List (Wire × Wire)) : Program :=
  ops.map fun (a, b) => .CX a b

theorem inverse_cnot (a b : Wire) (hab : a ≠ b) (s : State) (m n : List Bool) :
    run [.CX a b] n (run [.CX a b] m s) = s := by
  cases s with
  | mk ph bits =>
    change State.mk ph _ = State.mk ph bits
    congr 1
    funext q
    by_cases e : q = b
    · subst q; simp [run, writeBit, Function.update_of_ne hab]
    · simp [run, writeBit, Function.update_of_ne e]

theorem reverse_cnots (ops : List (Wire × Wire)) (apart : ∀ p ∈ ops, p.1 ≠ p.2)
    (s : State) (m n : List Bool) :
    run (cnotProgram ops.reverse) n (run (cnotProgram ops) m s) = s := by
  induction ops generalizing s m n with
  | nil => rfl
  | cons p tail ih =>
    obtain ⟨a, b⟩ := p
    have sep := apart (a, b) (by simp)
    have rest : ∀ p ∈ tail, p.1 ≠ p.2 := fun p hp => apart p (List.mem_cons_of_mem _ hp)
    change run (cnotProgram (((a, b) :: tail).reverse)) n
      (run (cnotProgram tail) m (run [.CX a b] m s)) = s
    rw [List.reverse_cons, cnotProgram, List.map_append, run_append, run_take]
    change run [.CX a b] _ (run (cnotProgram tail.reverse) n
      (run (cnotProgram tail) m (run [.CX a b] m s))) = s
    rw [ih rest]
    exact inverse_cnot a b sep s m _

/-! ## Field core bit-slice verification (21 tags in 32 slots, 39 local wires) -/

namespace Field20
open CodecBitSliceVerify

def rowWord (cols : Cols) (row : Nat) : Nat := packBits (cols.map (·.testBit row))

theorem run_columns (P : Program) (input output : Cols) (mask row : Nat)
    (hm : mask.testBit row = true) (hb : ∀ i ∈ P, target i < input.length)
    (checked : eval mask P input = (true, output)) (phase : Bool) (tape : List Bool) :
    run P tape ⟨phase, MeasuredCodec5.bitsOf (rowWord input row)⟩ =
      ⟨phase, MeasuredCodec5.bitsOf (rowWord output row)⟩ := by
  have initial : Rel input (rowWord input row) row := fun q => pack_rows input row q
  have proof := eval_sound mask row hm P input _ hb initial (congrArg Prod.fst checked)
  rw [MeasuredCodec5.run_sim, MeasuredCodec5.sim_safe P _ proof.1]
  apply congrArg (State.mk phase)
  funext q
  change (MeasuredCodec5.bitRun P _).testBit q = (rowWord output row).testBit q
  rw [proof.2 q, checked]
  exact (pack_rows output row q).symm

def tagColumn (d k : Nat) : Nat := CertificateBits.mask d <<< ((k + 1) * 2 ^ d)

def inputColumn20 (d q : Nat) : Nat :=
  if q < d then CertificateBits.input (d + 5) q
  else if 18 ≤ q ∧ q < 39 then tagColumn d (q - 18) else 0

def inputCols20 (d : Nat) : Cols := (List.range 39).map (inputColumn20 d)

def rowMask20 (p : Nat) (mir : Bool) (i : Nat) : Nat := (eraseMasks20 p (!mir)).getD i 0

def outputColumn20 (p : Nat) (mir : Bool) (q : Nat) : Nat :=
  let d := fieldDegree p
  if q < d then
    let extra := (List.range 21).flatMap fun k =>
      (selected d ((rowMask20 p mir q) >>> (k * d))).map fun j =>
        tagColumn d k &&& inputColumn20 d j
    extra.foldl Nat.xor (inputColumn20 d q)
  else inputColumn20 d q

def outputCols20 (p : Nat) (mir : Bool) : Cols := (List.range 39).map (outputColumn20 p mir)

def fieldTest20 (p : Nat) (mir : Bool) : Bool :=
  let P := fieldCore20 p mir
  let d := fieldDegree p
  (P.all (fun i => decide (target i < 39))) &&
    (eval (CertificateBits.mask (d + 5)) P (inputCols20 d) == (true, outputCols20 p mir))

theorem run_field_of_test20 (p : Nat) (mir : Bool) (tested : fieldTest20 p mir = true)
    (row : Nat) (small : row < 2 ^ (fieldDegree p + 5)) (phase : Bool) (m : List Bool) :
    run (fieldCore20 p mir) m ⟨phase, MeasuredCodec5.bitsOf (rowWord (inputCols20 (fieldDegree p)) row)⟩ =
      ⟨phase, MeasuredCodec5.bitsOf (rowWord (outputCols20 p mir) row)⟩ := by
  simp only [fieldTest20, Bool.and_eq_true] at tested
  obtain ⟨bound, check⟩ := tested
  apply run_columns _ _ _ (CertificateBits.mask (fieldDegree p + 5)) row
  · exact CertificateBits.mask_bit _ _ small
  · intro i hi
    simpa [inputCols20] using (of_decide_eq_true (List.all_eq_true.mp bound i hi))
  · exact beq_iff_eq.mp check

set_option maxRecDepth 50000 in
set_option maxHeartbeats 4000000 in
private theorem ft20_257_f : fieldTest20 257 false = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 4000000 in
private theorem ft20_257_t : fieldTest20 257 true = true := by decide +kernel

private theorem ft20_11 : ∀ mir : Bool, fieldTest20 11 mir = true := by decide +kernel
private theorem ft20_13 : ∀ mir : Bool, fieldTest20 13 mir = true := by decide +kernel
private theorem ft20_19 : ∀ mir : Bool, fieldTest20 19 mir = true := by decide +kernel
private theorem ft20_21 : ∀ mir : Bool, fieldTest20 21 mir = true := by decide +kernel
private theorem ft20_25 : ∀ mir : Bool, fieldTest20 25 mir = true := by decide +kernel
private theorem ft20_31 : ∀ mir : Bool, fieldTest20 31 mir = true := by decide +kernel
private theorem ft20_37_f : fieldTest20 37 false = true := by decide +kernel
private theorem ft20_37_t : fieldTest20 37 true = true := by decide +kernel
private theorem ft20_41_f : fieldTest20 41 false = true := by decide +kernel
private theorem ft20_41_t : fieldTest20 41 true = true := by decide +kernel
private theorem ft20_47_f : fieldTest20 47 false = true := by decide +kernel
private theorem ft20_47_t : fieldTest20 47 true = true := by decide +kernel
private theorem ft20_55_f : fieldTest20 55 false = true := by decide +kernel
private theorem ft20_55_t : fieldTest20 55 true = true := by decide +kernel
private theorem ft20_59_f : fieldTest20 59 false = true := by decide +kernel
private theorem ft20_59_t : fieldTest20 59 true = true := by decide +kernel
private theorem ft20_61_f : fieldTest20 61 false = true := by decide +kernel
private theorem ft20_61_t : fieldTest20 61 true = true := by decide +kernel
private theorem ft20_67_f : fieldTest20 67 false = true := by decide +kernel
private theorem ft20_67_t : fieldTest20 67 true = true := by decide +kernel
private theorem ft20_73_f : fieldTest20 73 false = true := by decide +kernel
private theorem ft20_73_t : fieldTest20 73 true = true := by decide +kernel
private theorem ft20_87_f : fieldTest20 87 false = true := by decide +kernel
private theorem ft20_87_t : fieldTest20 87 true = true := by decide +kernel
private theorem ft20_91_f : fieldTest20 91 false = true := by decide +kernel
private theorem ft20_91_t : fieldTest20 91 true = true := by decide +kernel
private theorem ft20_97_f : fieldTest20 97 false = true := by decide +kernel
private theorem ft20_97_t : fieldTest20 97 true = true := by decide +kernel
private theorem ft20_103_f : fieldTest20 103 false = true := by decide +kernel
private theorem ft20_103_t : fieldTest20 103 true = true := by decide +kernel
private theorem ft20_109_f : fieldTest20 109 false = true := by decide +kernel
private theorem ft20_109_t : fieldTest20 109 true = true := by decide +kernel
private theorem ft20_115_f : fieldTest20 115 false = true := by decide +kernel
private theorem ft20_115_t : fieldTest20 115 true = true := by decide +kernel
private theorem ft20_117_f : fieldTest20 117 false = true := by decide +kernel
private theorem ft20_117_t : fieldTest20 117 true = true := by decide +kernel

theorem field_tested20 (p : Nat) (hp : UsedField20 p) (mir : Bool) : fieldTest20 p mir = true := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ft20_11 mir
  · exact ft20_13 mir
  · exact ft20_19 mir
  · exact ft20_21 mir
  · exact ft20_25 mir
  · exact ft20_31 mir
  · cases mir; exact ft20_37_f; exact ft20_37_t
  · cases mir; exact ft20_41_f; exact ft20_41_t
  · cases mir; exact ft20_47_f; exact ft20_47_t
  · cases mir; exact ft20_55_f; exact ft20_55_t
  · cases mir; exact ft20_59_f; exact ft20_59_t
  · cases mir; exact ft20_61_f; exact ft20_61_t
  · cases mir; exact ft20_67_f; exact ft20_67_t
  · cases mir; exact ft20_73_f; exact ft20_73_t
  · cases mir; exact ft20_87_f; exact ft20_87_t
  · cases mir; exact ft20_91_f; exact ft20_91_t
  · cases mir; exact ft20_97_f; exact ft20_97_t
  · cases mir; exact ft20_103_f; exact ft20_103_t
  · cases mir; exact ft20_109_f; exact ft20_109_t
  · cases mir; exact ft20_115_f; exact ft20_115_t
  · cases mir; exact ft20_117_f; exact ft20_117_t
  · cases mir; exact ft20_257_f; exact ft20_257_t

theorem run_field20 (p : Nat) (hp : UsedField20 p) (mir : Bool) (row : Nat)
    (small : row < 2 ^ (fieldDegree p + 5)) (phase : Bool) (m : List Bool) :
    run (fieldCore20 p mir) m ⟨phase, MeasuredCodec5.bitsOf (rowWord (inputCols20 (fieldDegree p)) row)⟩ =
      ⟨phase, MeasuredCodec5.bitsOf (rowWord (outputCols20 p mir) row)⟩ :=
  run_field_of_test20 p mir (field_tested20 p hp mir) row small phase m

def accumulate20 {α : Type} (p : Nat) (mir : Bool) (q : Nat) (combine : α → α → α)
    (source : Nat → α) (term : Nat → Nat → α) : α :=
  let d := fieldDegree p
  ((List.range 21).flatMap fun k =>
    (selected d (rowMask20 p mir q >>> (k * d))).map (term k)).foldl combine (source q)

private theorem map_fold {α β} (f : α → β) (op : α → α → α) (op' : β → β → β)
    (pres : ∀ a b, f (op a b) = op' (f a) (f b)) (xs : List α) (a : α) :
    f (xs.foldl op a) = (xs.map f).foldl op' (f a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons]; rw [ih, pres]

theorem map_accumulate20 {α β} (p : Nat) (mir : Bool) (q : Nat) (f : α → β)
    (op : α → α → α) (op' : β → β → β) (pres : ∀ a b, f (op a b) = op' (f a) (f b))
    (src : Nat → α) (term : Nat → Nat → α) :
    f (accumulate20 p mir q op src term) =
      accumulate20 p mir q op' (fun j => f (src j)) (fun k j => f (term k j)) := by
  unfold accumulate20
  rw [map_fold _ _ _ pres]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

def scalarRow20 (p : Nat) (mir : Bool) (hot : Nat → Bool) (data : Nat → Nat) (q : Nat) : Nat :=
  accumulate20 p mir q Nat.xor data (fun k j => if hot k then data j else 0)

theorem accumulate20_congr {α} (p : Nat) (mir : Bool) (q : Nat) (op : α → α → α)
    (src src' : Nat → α) (a b : Nat → Nat → α) (hs : src q = src' q)
    (ht : ∀ k, ∀ j < fieldDegree p, a k j = b k j) :
    accumulate20 p mir q op src a = accumulate20 p mir q op src' b := by
  have same k : (selected (fieldDegree p) (rowMask20 p mir q >>> (k * fieldDegree p))).map (a k) =
      (selected (fieldDegree p) (rowMask20 p mir q >>> (k * fieldDegree p))).map (b k) := by
    apply List.map_congr_left
    intro j hj
    exact ht k j (List.mem_range.mp (List.mem_filter.mp hj).1)
  unfold accumulate20
  simp only [same, hs]

theorem output_bit20 (p : Nat) (mir : Bool) (q : Nat) (hq : q < fieldDegree p) (row dim : Nat)
    (x : Nat → Bool) (hot : Nat → Bool) (data : Nat → Nat)
    (ht : ∀ k, (tagColumn (fieldDegree p) k).testBit row = hot k)
    (hd : ∀ j < fieldDegree p, (inputColumn20 (fieldDegree p) j).testBit row = rowValue x (data j) dim) :
    (outputColumn20 p mir q).testBit row = rowValue x (scalarRow20 p mir hot data q) dim := by
  simp only [outputColumn20, if_pos hq]
  change ((accumulate20 p mir q Nat.xor (inputColumn20 (fieldDegree p))
    (fun k j => tagColumn (fieldDegree p) k &&& inputColumn20 (fieldDegree p) j))).testBit row = _
  rw [map_accumulate20 p mir q (fun a : Nat => a.testBit row) Nat.xor Bool.xor (fun _ _ => Nat.testBit_xor ..)]
  unfold scalarRow20
  rw [map_accumulate20 p mir q (fun a => rowValue x a dim) Nat.xor Bool.xor (fun a b => rowValue_xor x a b dim)]
  apply accumulate20_congr
  · exact hd q hq
  · intro k j hj
    rw [Nat.testBit_and, ht, hd j hj]
    cases hot k <;> simp [rowValue_zero]

def packedRow (d slot v : Nat) : Nat := v + slot * 2 ^ d

theorem packedRow_lt {d slot v : Nat} (sv : v < 2 ^ d) (ss : slot < 32) : packedRow d slot v < 2 ^ (d + 5) := by
  have h := Nat.mul_le_mul_right (2 ^ d) (show slot + 1 ≤ 32 by omega)
  simp only [Nat.succ_mul] at h
  unfold packedRow
  rw [Nat.pow_add, show 2 ^ 5 = 32 by decide]
  omega

theorem data_bit20 {d q slot v : Nat} (sq : q < d) (sv : v < 2 ^ d) (ss : slot < 32) :
    (inputColumn20 d q).testBit (packedRow d slot v) = v.testBit q := by
  rw [inputColumn20, if_pos sq, CertificateBits.input_bit _ _ _ (packedRow_lt sv ss)]
  have low : packedRow d slot v % 2 ^ d = v := by simp [packedRow, Nat.mod_eq_of_lt sv]
  have bit := congrArg (fun a : Nat => a.testBit q) low
  simpa only [Nat.testBit_mod_two_pow, sq, decide_true, Bool.true_and] using bit

theorem tag_bit {d slot v : Nat} (sv : v < 2 ^ d) (k : Nat) :
    (tagColumn d k).testBit (packedRow d slot v) = decide (slot = k + 1) := by
  let b := 2 ^ d
  change ((2 ^ b - 1) <<< ((k + 1) * b)).testBit (v + slot * b) = _
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  change v < b at sv
  rcases lt_trichotomy slot (k + 1) with low | eq | high
  · have h := Nat.mul_le_mul_right b (show slot + 1 ≤ k + 1 by omega)
    rw [Nat.succ_mul] at h
    simp [show ¬v + slot * b ≥ (k + 1) * b by omega, show slot ≠ k + 1 by omega]
  · subst slot
    simp [sv]
  · have h := Nat.mul_le_mul_right b (show k + 1 + 1 ≤ slot by omega)
    rw [Nat.succ_mul] at h
    simp [show ¬v + slot * b - (k + 1) * b < b by omega, show slot ≠ k + 1 by omega]

end Field20

/-! ## Binary matrix rows & frame semantics -/

namespace Matrix20

abbrev Rows := Array Nat

def read (rows : Rows) (q : Nat) : Nat := (rows[q]?).getD 0

def basis (rows : Rows) (word : Nat → Bool) (dim : Nat) (outside : BasisState) (q : Wire) : Bool :=
  if q < rows.size then rowValue word (read rows q) dim else outside q

def applyPair (rows : Rows) (op : Wire × Wire) : Rows :=
  rows.setIfInBounds op.2 (read rows op.2 ^^^ read rows op.1)

def applyOps (ops : List (Wire × Wire)) (rows : Rows) : Rows := ops.foldl applyPair rows

@[simp] theorem applyPair_size (rows : Rows) (op : Wire × Wire) : (applyPair rows op).size = rows.size := by
  simp [applyPair]

@[simp] theorem applyOps_size (ops : List (Wire × Wire)) (rows : Rows) : (applyOps ops rows).size = rows.size := by
  induction ops generalizing rows with
  | nil => rfl
  | cons op tail ih => exact (ih (applyPair rows op)).trans (applyPair_size rows op)

theorem apply_read (r : Rows) (a b q : Nat) (hb : b < r.size) :
    read (applyPair r (a, b)) q = if q = b then read r b ^^^ read r a else read r q := by
  by_cases e : q = b
  · subst e; simp [read, applyPair, hb]
  · simp [read, applyPair, e, Ne.symm e]

theorem run_ops (ops : List (Wire × Wire)) (rows : Rows) (x : Nat → Bool) (dim : Nat)
    (outside : BasisState) (ph : Bool) (m : List Bool)
    (within : ∀ op ∈ ops, op.1 < rows.size ∧ op.2 < rows.size) :
    run (cnotProgram ops) m ⟨ph, basis rows x dim outside⟩ =
      ⟨ph, basis (applyOps ops rows) x dim outside⟩ := by
  induction ops generalizing rows with
  | nil => rfl
  | cons op tail ih =>
    obtain ⟨a, b⟩ := op
    obtain ⟨ha, hb⟩ := within (a, b) (by simp)
    change a < rows.size at ha
    change b < rows.size at hb
    have step : writeBit (basis rows x dim outside) b
        (basis rows x dim outside b ^^ basis rows x dim outside a) =
        basis (applyPair rows (a, b)) x dim outside := by
      funext q
      by_cases e : q = b
      · subst q
        simp [basis, read, applyPair, writeBit, ha, hb, rowValue_xor]
      · simp [basis, read, applyPair, writeBit, Function.update_of_ne e, Ne.symm e]
    change run (cnotProgram tail) m ⟨ph, _⟩ = _
    rw [step]
    apply ih
    intro op ho
    simpa only [applyPair_size] using within op (List.mem_cons_of_mem _ ho)

theorem apply_map (ops : List (Wire × Wire)) (f : Nat → Nat) (zero : f 0 = 0)
    (linear : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (rows : Rows) :
    applyOps ops (rows.map f) = (applyOps ops rows).map f := by
  have mapRead (r : Rows) (i : Nat) : read (r.map f) i = f (read r i) := by
    unfold read
    rw [Array.getElem?_map]
    cases r[i]? <;> simp [zero]
  have step (r : Rows) (p : Wire × Wire) : applyPair (r.map f) p = (applyPair r p).map f := by
    unfold applyPair
    rw [mapRead, mapRead, ← linear]
    apply Array.ext_getElem?; intro i
    simp only [Array.getElem?_map, Array.getElem?_setIfInBounds, Array.size_map]
    split <;> (try split) <;> rfl
  induction ops generalizing rows with
  | nil => rfl
  | cons op tail ih =>
    change applyOps tail (applyPair (rows.map f) op) = (applyOps tail (applyPair rows op)).map f
    rw [step, ih]

def units (n : Nat) : Rows := Array.ofFn (fun i : Fin n => 2 ^ i.val)

theorem value_unit (x : Nat → Bool) (i dim : Nat) :
    rowValue x (2 ^ i) dim = if i < dim then x i else false := by
  induction dim with
  | zero => simp [rowValue]
  | succ n ih =>
    simp only [rowValue, ih, Nat.testBit_two_pow]
    by_cases e : i = n
    · subst i; simp
    · by_cases h : i < n
      · simp [e, h, show i < n + 1 by omega]
      · simp [e, h, show ¬i < n + 1 by omega]

end Matrix20

open Field20 Matrix20 CodecBitSliceVerify

def flags20 (n slot q : Nat) : Bool := decide (n ≤ q ∧ q < n + 21 ∧ slot = q - n + 1)

def frame20 (rows : Rows) (x : Nat → Bool) (dim slot : Nat) (ph : Bool) : State :=
  ⟨ph, Matrix20.basis rows x dim (flags20 rows.size slot)⟩

def scalarRows20 (rows : Rows) (p : Nat) (mir : Bool) (slot off : Nat) : Rows :=
  Array.ofFn fun q : Fin rows.size =>
    if off ≤ q.val ∧ q.val < off + fieldDegree p then
      scalarRow20 p mir (fun k => decide (slot = k + 1)) (fun j => read rows (off + j)) (q.val - off)
    else read rows q.val

@[simp] theorem scalarRows20_size (r : Rows) (p : Nat) (mir : Bool) (s o : Nat) :
    (scalarRows20 r p mir s o).size = r.size := by simp [scalarRows20]

theorem scalar20_read {r : Rows} {q : Nat} (hq : q < r.size) (p : Nat) (mir : Bool) (slot off : Nat) :
    read (scalarRows20 r p mir slot off) q =
      if off ≤ q ∧ q < off + fieldDegree p then
        scalarRow20 p mir (fun k => decide (slot = k + 1)) (fun j => read r (off + j)) (q - off)
      else read r q := by
  simp [scalarRows20, Matrix20.read, hq]

instance (d q : Nat) : Decidable (fieldScope20 d q) := by unfold fieldScope20; infer_instance

def fieldPool20 (d : Nat) : Finset Wire := (Finset.range 39).filter (fieldScope20 d)

theorem fieldPool20_iff {d q : Nat} (sd : d ≤ 8) : q ∈ fieldPool20 d ↔ fieldScope20 d q := by
  simp only [fieldPool20, Finset.mem_filter, Finset.mem_range]
  unfold fieldScope20; omega

private theorem pack_lt (bs : List Bool) : packBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp [packBits, Nat.bit, Nat.pow_succ] <;> omega

def fieldWord (d : Nat) (getBit : Nat → Bool) : Nat := packBits ((List.range d).map getBit)

theorem fieldWord_small (d : Nat) (v : Nat → Bool) : fieldWord d v < 2 ^ d := by
  simpa [fieldWord] using pack_lt ((List.range d).map v)

theorem fieldWord_bit (d : Nat) (v : Nat → Bool) (q : Nat) (hq : q < d) :
    (fieldWord d v).testBit q = v q := by
  simp [fieldWord, pack_testBit, List.getElem?_map, List.getElem?_range hq]

private theorem column_bit20 (f : Nat → Nat) (row q : Nat) (hq : q < 39) :
    (rowWord ((List.range 39).map f) row).testBit q = (f q).testBit row := by
  rw [rowWord, pack_rows, List.getElem?_map, List.getElem?_range hq]
  rfl

private theorem used_degree20' (p : Nat) (hp : UsedField20 p) : 0 < fieldDegree p ∧ fieldDegree p ≤ 8 := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem fieldPlace20_maps' {n off d : Nat} (sd : d ≤ 8) (endp : off + d ≤ n) :
    (∀ q, fieldScope20 d q → fieldPlace20 n off q < n + 31) ∧
    (∀ a, fieldScope20 d a → ∀ b, fieldScope20 d b → fieldPlace20 n off a = fieldPlace20 n off b → a = b) := by
  constructor
  · intro q hq; unfold fieldScope20 at hq; unfold fieldPlace20; unfold Wire at *; split_ifs <;> omega
  · intro a ha b hb heq
    unfold fieldScope20 at ha hb; unfold fieldPlace20 at heq; unfold Wire at *
    by_cases ha8 : a < 8 <;> by_cases ha18 : a < 18 <;>
      by_cases hb8 : b < 8 <;> by_cases hb18 : b < 18 <;>
      simp only [ha8, ha18, hb8, hb18, ↓reduceIte] at heq <;> omega

theorem frame_field20 (r : Rows) (p : Nat) (hp : UsedField20 p) (mir : Bool) (off slot dim : Nat)
    (small : slot < 32) (endp : off + fieldDegree p ≤ r.size) (x : Nat → Bool) (ph : Bool) (m : List Bool) :
    run (renameProgram (fieldPlace20 r.size off) (fieldCore20 p mir)) m (frame20 r x dim slot ph) =
      frame20 (scalarRows20 r p mir slot off) x dim slot ph := by
  let d := fieldDegree p
  let f := fieldPlace20 r.size off
  let data := fun j => read r (off + j)
  let v := fieldWord d (fun j => rowValue x (data j) dim)
  let row := packedRow d slot v
  have sd := (used_degree20' p hp).2
  have sv : v < 2 ^ d := fieldWord_small _ _
  have val (j : Nat) (hj : j < d) : (inputColumn20 d j).testBit row = rowValue x (data j) dim :=
    (data_bit20 hj sv small).trans (fieldWord_bit _ _ _ hj)
  have tags (k : Nat) : (tagColumn d k).testBit row = decide (slot = k + 1) := tag_bit sv k
  have live := support (fits_core20 p hp mir)
  have sub : wires (fieldCore20 p mir) ⊆ fieldPool20 d := fun _ h => (fieldPool20_iff sd).mpr (live _ h)
  have maps := fieldPlace20_maps' sd endp
  have inj : ∀ a ∈ fieldPool20 d, ∀ b ∈ fieldPool20 d, f a = f b → a = b :=
    fun a ha b hb => maps.2 a ((fieldPool20_iff sd).mp ha) b ((fieldPool20_iff sd).mp hb)
  have point (q : Nat) (hq : fieldScope20 d q) :
      (inputColumn20 d q).testBit row = (frame20 r x dim slot ph).basis (f q) := by
    by_cases left : q < d
    · have lt : q < 8 := by omega
      have inside : off + q < r.size := by omega
      simpa [frame20, Matrix20.basis, f, fieldPlace20, lt, inside, data] using val q left
    · obtain hq := hq.resolve_left left
      by_cases mid : q < 18
      · simp [frame20, Matrix20.basis, f, fieldPlace20, inputColumn20, left, flags20,
          show ¬q < 8 by omega, mid, show ¬18 ≤ q by omega,
          show ¬r.size + 21 + (q - 8) < r.size by omega,
          show ¬r.size + 21 + (q - 8) < r.size + 21 by omega]
      · have inside : r.size + (q - 18) < r.size + 21 := by omega
        simp [frame20, Matrix20.basis, f, fieldPlace20, inputColumn20, left, flags20,
          show ¬q < 8 by omega, mid, show 18 ≤ q by omega, hq.2, inside, tags]
  have rel := run_rename_pool f (fieldPool20 d) inj (fieldCore20 p mir) sub m
    ⟨ph, MeasuredCodec5.bitsOf (rowWord (inputCols20 d) row)⟩ (frame20 r x dim slot ph) rfl (by
      intro q hq
      have bound := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
      exact (column_bit20 (inputColumn20 d) row q bound).trans (point q ((fieldPool20_iff sd).mp hq)))
  rw [run_field20 p hp mir row (packedRow_lt sv small)] at rel
  refine State.extensionality _ _ rel.1 ?_
  funext q
  by_cases inPool : q ∈ (fieldPool20 d).image f
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp inPool
    rw [rel.2 a ha]
    have shape := (fieldPool20_iff sd).mp ha
    have sa := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    change (rowWord (outputCols20 p mir) row).testBit a = _
    rw [show (rowWord (outputCols20 p mir) row).testBit a = (outputColumn20 p mir a).testBit row from
      column_bit20 _ _ _ sa]
    by_cases left : a < d
    · have a8 : a < 8 := by omega
      have inside : off + a < r.size := by omega
      have inSlice : off ≤ off + a ∧ off + a < off + fieldDegree p := ⟨by omega, Nat.add_lt_add_left left _⟩
      rw [output_bit20 p mir a left row dim x _ data tags val]
      simp [frame20, Matrix20.basis, f, fieldPlace20, a8, inside, scalar20_read inside, inSlice, data]
    · rw [outputColumn20, if_neg left, point a shape]
      have edge : r.size ≤ f a := by
        obtain ⟨a8, _⟩ := shape.resolve_left left
        unfold f fieldPlace20; unfold Wire at *
        simp only [show ¬a < 8 by omega, if_false]
        split <;> omega
      simp only [frame20, Matrix20.basis, scalarRows20_size, if_neg (Nat.not_lt_of_ge edge)]
  · rw [run_rename_pool_outside f (fieldPool20 d) (fieldCore20 p mir) sub m _ q inPool]
    by_cases inside : q < r.size
    · have outsideSlice : ¬(off ≤ q ∧ q < off + fieldDegree p) := by
        rintro ⟨lower, upper⟩
        apply inPool
        have sq : q - off < d := (Nat.sub_lt_iff_lt_add lower).mpr (Nat.add_comm off d ▸ upper)
        refine Finset.mem_image.mpr ⟨q - off, (fieldPool20_iff sd).mpr (Or.inl sq), ?_⟩
        simpa only [f, fieldPlace20, if_pos (Nat.lt_of_lt_of_le sq sd)] using Nat.add_sub_of_le lower
      simp [frame20, Matrix20.basis, inside, scalar20_read inside, outsideSlice]
    · simp [frame20, Matrix20.basis, inside]

/-! ## Pascal `(X+1)^8` step semantics (only multiplicity `m = 2` component) -/

def controlled (c : Wire) (pairs : List (Wire × Wire)) : Program :=
  pairs.map (fun (a, b) => Instr.CCX c a b)

theorem run_controlled (c : Wire) (pairs : List (Wire × Wire)) (m : List Bool) (s : State)
    (apart : ∀ p ∈ pairs, p.2 ≠ c) :
    run (controlled c pairs) m s = if s.basis c then run (cnotProgram pairs) m s else s := by
  induction pairs generalizing s with
  | nil => simp [controlled, cnotProgram, run]
  | cons p tail ih =>
    obtain ⟨a, b⟩ := p
    have ne : b ≠ c := apart (a, b) (by simp)
    have rest : ∀ p ∈ tail, p.2 ≠ c := fun p hp => apart p (List.mem_cons_of_mem _ hp)
    cases s with
    | mk ph bits =>
      cases bit : bits c <;>
        simp only [controlled, cnotProgram, List.map_cons, run, bit, Bool.false_and, Bool.xor_false,
          Bool.true_and, Bool.false_eq_true, if_false, if_true]
      · simpa [writeBit, Function.update_eq_self, controlled, cnotProgram, bit] using ih ⟨ph, bits⟩ rest
      · have unchanged : writeBit bits b (bits b ^^ bits a) c = true := by
          simp [writeBit, Function.update_of_ne ne.symm, bit]
        simpa [controlled, cnotProgram, unchanged] using ih ⟨ph, writeBit bits b (bits b ^^ bits a)⟩ rest

def xorAt (bits : BasisState) : List Wire → Bool
  | [] => false
  | w :: ws => bits w ^^ xorAt bits ws

private theorem xorAt_congr (xs : List Wire) (u v : BasisState) (h : ∀ q ∈ xs, u q = v q) :
    xorAt u xs = xorAt v xs := by
  induction xs with
  | nil => rfl
  | cons q xs ih => rw [xorAt, xorAt, h q (by simp), ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

def toggles (xs : List Wire) (t : Wire) : Program := xs.map (fun q => Instr.CX q t)

theorem run_toggles (xs : List Wire) (t : Wire) (sep : t ∉ xs) (m : List Bool) (ph : Bool) (bits : BasisState) :
    run (toggles xs t) m ⟨ph, bits⟩ = ⟨ph, writeBit bits t (bits t ^^ xorAt bits xs)⟩ := by
  induction xs generalizing bits with
  | nil => simp [toggles, xorAt, run, writeBit, Function.update_eq_self]
  | cons q xs ih =>
    have hn : t ∉ xs := fun h => sep (List.mem_cons_of_mem _ h)
    change run (toggles xs t) m ⟨ph, writeBit bits t (bits t ^^ bits q)⟩ = _
    rw [ih hn]
    have same : xorAt (writeBit bits t (bits t ^^ bits q)) xs = xorAt bits xs := by
      apply xorAt_congr
      intro j hj
      have ne : j ≠ t := fun eq => hn (eq ▸ hj)
      simp [writeBit, Function.update_of_ne ne]
    rw [same]
    simp [xorAt, writeBit, Function.update_idem]

def r8Enabled20 (n slot : Nat) (tags : List Nat) : Bool :=
  xorAt (flags20 n slot) (tags.map (n + ·))

def r8Ops (off : Nat) (st : R8Step) : List (Wire × Wire) :=
  let pre := st.pre.map (fun p => (off + p.1, off + p.2))
  pre ++ [(off + st.src, off + st.dst)] ++ pre.reverse

def r8StepRows20 (rows : Rows) (slot off : Nat) (st : R8Step) : Rows :=
  if r8Enabled20 rows.size slot st.tags then applyOps (r8Ops off st) rows else rows

@[simp] theorem r8StepRows20_size (rows : Rows) (s o : Nat) (st : R8Step) :
    (r8StepRows20 rows s o st).size = rows.size := by
  unfold r8StepRows20; split <;> simp

private def r8Step20Good' (st : R8Step) : Bool :=
  st.tags.all (· < 21) &&
  st.pre.all (fun p => p.1 < 16 && p.2 < 16 && p.1 != p.2) &&
  st.src < 16 && st.dst < 16 && st.src != st.dst

private theorem pascalR8Steps20_good' : ∀ mir : Bool, (pascalR8Steps20 mir).all r8Step20Good' = true := by
  decide +kernel

theorem r8Ops_bounds20 (rows : Rows) (off : Nat) (st : R8Step)
    (hg : r8Step20Good' st = true) (endp : off + 16 ≤ rows.size) :
    ∀ p ∈ r8Ops off st, p.1 < rows.size ∧ p.2 < rows.size ∧ p.1 ≠ p.2 := by
  unfold r8Step20Good' at hg
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne] at hg
  obtain ⟨⟨⟨⟨_, hpre⟩, hsrc⟩, hdst⟩, hne⟩ := hg
  intro p hp
  unfold r8Ops at hp
  rcases List.mem_append.mp hp with hp1 | hp2
  · rcases List.mem_append.mp hp1 with hpA | hpB
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpA
      obtain ⟨⟨h1, h2⟩, h3⟩ := hpre q hq
      unfold Wire at *; dsimp only; omega
    · simp only [List.mem_singleton] at hpB; subst hpB
      unfold Wire at *; dsimp only; omega
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hp2)
    obtain ⟨⟨h1, h2⟩, h3⟩ := hpre q hq
    unfold Wire at *; dsimp only; omega

def withR8Tag20 (r : Rows) (x : Nat → Bool) (dim slot : Nat) (tags : List Nat) (ph : Bool) : State :=
  ⟨ph, Matrix20.basis r x dim (writeBit (flags20 r.size slot) (r.size + 29) (r8Enabled20 r.size slot tags))⟩

private theorem toggle_r8_frame20 (r : Rows) (x : Nat → Bool) (dim slot : Nat) (tags : List Nat)
    (htags : ∀ k ∈ tags, k < 21) (ph : Bool) (tape : List Bool) :
    run (toggles (tags.map (r.size + ·)) (r.size + 29)) tape (frame20 r x dim slot ph) =
      withR8Tag20 r x dim slot tags ph := by
  have external (q : Wire) (hq : r.size ≤ q) : (frame20 r x dim slot ph).basis q = flags20 r.size slot q := by
    simp only [frame20, Matrix20.basis, if_neg (Nat.not_lt_of_ge hq)]
  have parity := xorAt_congr (tags.map (r.size + ·)) (frame20 r x dim slot ph).basis (flags20 r.size slot)
    (fun q hq => by obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq; exact external _ (by omega))
  have sep : r.size + 29 ∉ tags.map (r.size + ·) := by
    intro hq; obtain ⟨k, hk, he⟩ := List.mem_map.mp hq; have := htags k hk; unfold Wire at *; omega
  change run _ _ ⟨ph, (frame20 r x dim slot ph).basis⟩ = _
  rw [run_toggles _ _ sep, parity, external _ (by omega)]
  apply congrArg (State.mk ph)
  funext q
  by_cases eq : q = r.size + 29
  · subst q; simp [Matrix20.basis, flags20, writeBit, r8Enabled20]
  · by_cases inside : q < r.size <;> simp [frame20, Matrix20.basis, inside, writeBit, Function.update_of_ne eq]

private theorem tag_r8_restore20 (r : Rows) (x : Nat → Bool) (dim slot : Nat) (tags : List Nat)
    (htags : ∀ k ∈ tags, k < 21) (ph : Bool) (tape : List Bool) :
    run (toggles (tags.map (r.size + ·)) (r.size + 29)).reverse tape (withR8Tag20 r x dim slot tags ph) =
      frame20 r x dim slot ph := by
  let ops := (tags.map (r.size + ·)).map (fun a => (a, r.size + 29))
  have same : cnotProgram ops = toggles (tags.map (r.size + ·)) (r.size + 29) := by
    simp [cnotProgram, ops, toggles, List.map_map, Function.comp_def]
  have inv := reverse_cnots ops (by
    intro pair hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    have := htags k hk; change r.size + k ≠ r.size + 29; unfold Wire at *; omega) (frame20 r x dim slot ph) [] tape
  have rev : cnotProgram ops.reverse = (cnotProgram ops).reverse := List.map_reverse
  rw [rev, same, toggle_r8_frame20 r x dim slot tags htags] at inv
  exact inv

theorem frame_r8Step20 (r : Rows) (off : Nat) (st : R8Step)
    (hg : r8Step20Good' st = true) (endp : off + 16 ≤ r.size)
    (x : Nat → Bool) (dim slot : Nat) (ph : Bool) (tape : List Bool) :
    run (r8Step20 r.size off st) tape (frame20 r x dim slot ph) =
      frame20 (r8StepRows20 r slot off st) x dim slot ph := by
  have hg' := hg
  unfold r8Step20Good' at hg'
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne] at hg'
  obtain ⟨⟨⟨⟨htags, hpre⟩, hsrc⟩, hdst⟩, hne⟩ := hg'
  let prePairs : List (Wire × Wire) := st.pre.map (fun p => (off + p.1, off + p.2))
  have hpreB : ∀ p ∈ prePairs, p.1 < r.size ∧ p.2 < r.size := by
    intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨⟨h1, h2⟩, _⟩ := hpre q hq; unfold Wire at *; dsimp only; omega
  have hpreA : ∀ p ∈ prePairs, p.1 ≠ p.2 := by
    intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨⟨_, _⟩, h3⟩ := hpre q hq; unfold Wire at *; dsimp only; omega
  have hpreRevB : ∀ p ∈ prePairs.reverse, p.1 < r.size ∧ p.2 < r.size :=
    fun p hp => hpreB p (List.mem_reverse.mp hp)
  have shape : r8Step20 r.size off st =
      toggles (st.tags.map (r.size + ·)) (r.size + 29) ++ cnotProgram prePairs ++
      controlled (r.size + 29) [(off + st.src, off + st.dst)] ++ cnotProgram prePairs.reverse ++
      (toggles (st.tags.map (r.size + ·)) (r.size + 29)).reverse := by
    simp [r8Step20, toggles, cnotProgram, controlled, prePairs, List.map_reverse, List.map_map, Function.comp_def]
  rw [shape, run_append, run_take, run_append, run_take, run_append, run_take, run_append, run_take]
  rw [toggle_r8_frame20 r x dim slot st.tags htags]
  have sepC : ∀ p ∈ ([(off + st.src, off + st.dst)] : List (Wire × Wire)), p.2 ≠ r.size + 29 := by
    intro p hp; simp only [List.mem_singleton] at hp; subst hp; unfold Wire at *; dsimp only; omega
  have hpreRun : ∀ t, run (cnotProgram prePairs) t (withR8Tag20 r x dim slot st.tags ph) =
      withR8Tag20 (applyOps prePairs r) x dim slot st.tags ph := fun t => by
    simpa only [withR8Tag20, applyOps_size] using run_ops prePairs r x dim _ ph t hpreB
  cases yes : r8Enabled20 r.size slot st.tags with
  | false =>
    rw [run_controlled _ _ _ _ sepC]
    have bit : ∀ t, (run (cnotProgram prePairs) t (withR8Tag20 r x dim slot st.tags ph)).basis (r.size + 29) = false := fun t => by
      rw [hpreRun]; simp [withR8Tag20, Matrix20.basis, writeBit, yes]
    rw [bit]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [reverse_cnots prePairs hpreA]
    simpa [r8StepRows20, yes] using tag_r8_restore20 r x dim slot st.tags htags ph _
  | true =>
    rw [hpreRun, run_controlled _ _ _ _ sepC]
    have bit : (withR8Tag20 (applyOps prePairs r) x dim slot st.tags ph).basis (r.size + 29) = true := by
      simp [withR8Tag20, Matrix20.basis, writeBit, yes]
    rw [bit]; simp only [↓reduceIte]
    have hmidB : ∀ p ∈ ([(off + st.src, off + st.dst)] : List (Wire × Wire)),
        p.1 < (applyOps prePairs r).size ∧ p.2 < (applyOps prePairs r).size := by
      intro p hp; simp only [List.mem_singleton] at hp; subst hp; rw [applyOps_size]; unfold Wire at *; dsimp only; omega
    have h2 : ∀ t, run (cnotProgram [(off + st.src, off + st.dst)]) t (withR8Tag20 (applyOps prePairs r) x dim slot st.tags ph) =
        withR8Tag20 (applyOps [(off + st.src, off + st.dst)] (applyOps prePairs r)) x dim slot st.tags ph := fun t => by
      simpa only [withR8Tag20, applyOps_size] using run_ops [(off + st.src, off + st.dst)] (applyOps prePairs r) x dim _ ph t hmidB
    rw [h2]
    have hrevB : ∀ p ∈ prePairs.reverse,
        p.1 < (applyOps [(off + st.src, off + st.dst)] (applyOps prePairs r)).size ∧
        p.2 < (applyOps [(off + st.src, off + st.dst)] (applyOps prePairs r)).size := by
      intro p hp; rw [applyOps_size, applyOps_size]; exact hpreRevB p hp
    have h3 : ∀ t, run (cnotProgram prePairs.reverse) t (withR8Tag20 (applyOps [(off + st.src, off + st.dst)] (applyOps prePairs r)) x dim slot st.tags ph) =
        withR8Tag20 (applyOps prePairs.reverse (applyOps [(off + st.src, off + st.dst)] (applyOps prePairs r))) x dim slot st.tags ph := fun t => by
      simpa only [withR8Tag20, applyOps_size] using
        run_ops prePairs.reverse (applyOps [(off + st.src, off + st.dst)] (applyOps prePairs r)) x dim _ ph t hrevB
    rw [h3]
    have hcomb : applyOps prePairs.reverse (applyOps [(off + st.src, off + st.dst)] (applyOps prePairs r)) = applyOps (r8Ops off st) r := by
      simp [r8Ops, applyOps, prePairs, List.foldl_append]
    rw [hcomb]
    simpa only [r8StepRows20, yes, if_true, applyOps_size] using
      tag_r8_restore20 (applyOps (r8Ops off st) r) x dim slot st.tags htags ph _

/-! ## Primary & component row semantics -/

private theorem run_parts20 {α} (xs : List α) (g : α → Program) (next : Rows → α → Rows)
    (n : Nat) (x : Nat → Bool) (dim slot : Nat) (ph : Bool) (m : List Bool) (r : Rows) (size : r.size = n)
    (keep : ∀ r a, (next r a).size = r.size)
    (step : ∀ a ∈ xs, ∀ r : Rows, r.size = n → ∀ m,
      run (g a) m (frame20 r x dim slot ph) = frame20 (next r a) x dim slot ph) :
    run (xs.flatMap g) m (frame20 r x dim slot ph) = frame20 (xs.foldl next r) x dim slot ph := by
  induction xs generalizing r m with
  | nil => rfl
  | cons a xs ih =>
    rw [List.flatMap_cons, run_append, run_take, step a (by simp) r size]
    exact ih _ _ ((keep r a).trans size) (fun y hy => step y (List.mem_cons_of_mem _ hy))

private theorem fold_size {α} (xs : List α) (f : Rows → α → Rows) (r : Rows)
    (h : ∀ r a, (f r a).size = r.size) : (xs.foldl f r).size = r.size := by
  induction xs generalizing r with
  | nil => rfl
  | cons a xs ih => exact (ih (f r a)).trans (h r a)

def scalars20 (r : Rows) (p m off slot : Nat) (mir : Bool) : Rows :=
  (List.range m).foldl (fun a j => scalarRows20 a p mir slot (off + fieldDegree p * j)) r

@[simp] theorem scalars20_size (r : Rows) (p m off slot : Nat) (mir : Bool) :
    (scalars20 r p m off slot mir).size = r.size := fold_size _ _ _ (fun _ _ => scalarRows20_size ..)

def r8Rows20 (r : Rows) (off slot : Nat) (mir : Bool) : Rows :=
  (pascalR8Steps20 mir).foldl (fun a st => r8StepRows20 a slot off st) r

@[simp] theorem r8Rows20_size (r : Rows) (off slot : Nat) (mir : Bool) :
    (r8Rows20 r off slot mir).size = r.size := fold_size _ _ _ (fun _ _ => r8StepRows20_size ..)

def primaryRows20 (r : Rows) (off p m slot : Nat) (mir : Bool) : Rows :=
  let d := fieldDegree p
  if d == 8 && m == 2 then r8Rows20 (scalars20 r p m off slot mir) off slot mir
  else scalars20 r p m off slot mir

@[simp] theorem primaryRows20_size (r : Rows) (off p m slot : Nat) (mir : Bool) :
    (primaryRows20 r off p m slot mir).size = r.size := by
  unfold primaryRows20; dsimp only; split <;> simp

theorem frame_primary20 (r : Rows) (p : Nat) (hp : UsedField20 p) (mir : Bool) (off m slot dim : Nat)
    (small : slot < 32) (endp : off + fieldDegree p * m ≤ r.size) (x : Nat → Bool) (ph : Bool) (tape : List Bool) :
    run (primary20 r.size off p m mir) tape (frame20 r x dim slot ph) =
      frame20 (primaryRows20 r off p m slot mir) x dim slot ph := by
  let d := fieldDegree p
  change off + d * m ≤ r.size at endp
  have scalar := run_parts20 (List.range m)
    (fun j => renameProgram (fieldPlace20 r.size (off + d * j)) (fieldCore20 p mir))
    (fun a j => scalarRows20 a p mir slot (off + d * j)) r.size x dim slot ph tape r rfl
    (fun _ _ => scalarRows20_size ..) (by
      intro j hj a size tape
      have limit := Nat.mul_le_mul_left d (show j + 1 ≤ m from List.mem_range.mp hj)
      rw [Nat.mul_succ] at limit
      rw [← size]
      exact frame_field20 a p hp mir _ _ _ small (by change off + d * j + d ≤ a.size; rw [size]; omega) x ph tape)
  unfold primary20 primaryRows20; dsimp only
  rw [run_append, run_take, scalar]
  by_cases h82 : (fieldDegree p == 8 && m == 2) = true
  · have h82' := h82; simp only [Bool.and_eq_true, beq_iff_eq] at h82'
    have h16 : d * m = 16 := by change fieldDegree p * m = 16; rw [h82'.1, h82'.2]
    rw [if_pos h82, if_pos h82]
    unfold pascalR8_20 r8Rows20
    apply run_parts20 (pascalR8Steps20 mir) (r8Step20 r.size off) (fun a st => r8StepRows20 a slot off st) r.size _ _ _ _ _ _
      (scalars20_size ..) (fun _ _ => r8StepRows20_size ..)
    intro st hst a size tape
    rw [← size]
    exact frame_r8Step20 a off st (List.all_eq_true.mp (pascalR8Steps20_good' mir) st hst)
      (by rw [size]; omega) x dim slot ph tape
  · rw [if_neg h82, if_neg h82]; rfl

def extent20 (parts : List (Nat × Nat)) : Nat :=
  parts.foldr (fun x r => fieldDegree x.1 * x.2 + r) 0

def componentRows20 (mir : Bool) (slot : Nat) : Nat → List (Nat × Nat) → Rows → Rows
  | _, [], r => r
  | off, (p, m) :: ps, r => componentRows20 mir slot (off + fieldDegree p * m) ps (primaryRows20 r off p m slot mir)

@[simp] theorem componentRows20_size (mir : Bool) (slot off : Nat) (parts : List (Nat × Nat)) (r : Rows) :
    (componentRows20 mir slot off parts r).size = r.size := by
  induction parts generalizing off r with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨p, m⟩ := pair
    exact (ih _ _).trans (primaryRows20_size ..)

theorem frame_components20 (r : Rows) (mir : Bool) (off slot dim : Nat) (parts : List (Nat × Nat))
    (small : slot < 32) (endp : off + extent20 parts ≤ r.size) (fields : ∀ pair ∈ parts, UsedField20 pair.1)
    (x : Nat → Bool) (ph : Bool) (tape : List Bool) :
    run (components20 r.size mir off parts) tape (frame20 r x dim slot ph) =
      frame20 (componentRows20 mir slot off parts r) x dim slot ph := by
  induction parts generalizing off r tape with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨p, m⟩ := pair
    change off + (fieldDegree p * m + extent20 tail) ≤ r.size at endp
    rw [components20, run_append, run_take,
      frame_primary20 r p (fields (p, m) (by simp)) mir off m slot dim small (by omega)]
    let new := primaryRows20 r off p m slot mir
    have eq : new.size = r.size := primaryRows20_size ..
    rw [← eq]
    exact ih new _ (by omega) (fun a ha => fields a (List.mem_cons_of_mem _ ha)) _

/-! ## Primary-component coordinate tables (`encoded20`, `basisWord20`, `prototype20`) -/

def encoded20 : Nat → Rows
  | 83 => #[
      9671406556917033397649407, 3223802185639011132549802, 5802843934150220038589644, 644760437127802226509960,
      1137812536107886282076400, 758541690738590854717600, 910250028886309025661120, 606833352590872683774080,
      5219489252939351357461585, 767571948961669317273762, 6140575591693354538190100, 2609744626469675678730792,
      1871885140048458076964401, 3119808566747430128274002, 5615655420145374230893204, 935942570024229038482200,
      6320683025386722614211817, 8833725674034455701790010, 7996044791151878005930612, 8681420058964896120724665,
      7691433561012758843799922, 4340710029482448060362332, 5512645657629304872826257, 6733709805276808982634162,
      3796013053636584567618916, 7592026107273169135237832, 9112674521263969515641585, 8553942485610905633633762,
      7436478414304777869618116, 4556337260631984757820792, 2725406153025543658046017, 5450812306051087316092034,
      1230218055185141234534660, 340675769128192957255752, 681351538256385914511504, 1362703076512771829023008,
      2357795337655473125444897, 4715590675310946250889794, 7548279334894709188917668, 5425152112872384980185928,
      1178897668827736562722448, 3079591498469857435129921, 9163180881436901855144130, 8654955205956770312638852,
      7638503854996507227628296, 5605601153075981057607184, 1539795749234928717564960, 2893054981142187414440257,
      8074683298635864258468802, 8761801784595079112851140, 7852197012273124828052872, 7976818662973321901847120,
      6282230769029610406044832, 3171675611979410262277953, 9222212442615255138255298, 8773018328313476878861188,
      4968601456177162494687304, 3210770542224110914981840, 6421541084448221829963680, 4041765081040201751900097,
      8083530162080403503800194, 6495653767243773609950980, 3319900977570513822252552, 6639801955141027644505104,
      2020882540520100875950048, 6393509830784577442583489, 9492572671734329267696706, 3615600341019968515996484,
      7231200682039937031992968, 4790994807162840666336528, 3196754915392288721291744, 684166619085176170422721,
      1368333238170352340845442, 3416083612762326504416964, 6300305019612057082424392, 2929203482307080767199376,
      5177786588001104784036064, 5323895375436119040118465, 5636754796464513254773570, 1602103036011993111897732,
      3204206072023986223795464, 1409188699116128313693392, 7497650966176576218883936
    ]
  | 93 => #[
      9903520314283042199192993791, 3301173438094347399730997930, 3961408125713216879677197516, 2640938750475477919784798344,
      5243040166385139987808055536, 194186672829079258807705760, 233024007394895110569246912, 155349338263263407046164608,
      9595239526289795749412667136, 3095652912765516433210780160, 3714783495318619719852936192, 2476522330212413146568624128,
      4952893542391496270367748096, 755590166650113847500800, 906708199980136617000960, 604472133320091078000640,
      1571987351473498761776665681, 3143974702946997523553331362, 5344756995009895790040663316, 785993675736749380888332840,
      1916810383409621070811547185, 3194683972349368451352578642, 5750431150228863212434641556, 958405191704810535405773592,
      4522867545105641319316485353, 6082477043417931429425618234, 2261433772552820659658242676, 3587101846118267253251005625,
      7174203692236534506502011250, 1793550923059133626625502812, 2375007252102302487296931217, 2772755985083548360710364850,
      5545511970167096721420729700, 1187503626051151243648465608, 1395407950349078352919560769, 2790815900698156705839121538,
      5581631801396313411678243076, 174425993793634794114945096, 348851987587269588229890192, 697703975174539176459780384,
      3619463847624625963846323489, 7238927695249251927692646978, 1690373020238458520379914660, 3380746040476917040759829320,
      6761492080953834081519658640, 912191807848670996814174273, 2194901062744686449723910338, 4389802125489372899447820676,
      8779604250978745798895641352, 7655688187674449398598288912, 5407856061065856598003584032, 6221607471078794662103009601,
      8722011991080882955540585410, 3799953172096072170991419076, 7599906344192144341982838152, 1555401867769698665525752400,
      3110803735539397331051504800, 7904710832613195696141844289, 3287829035237489576941404610, 6575658070474979153882809220,
      6175325984769244470195009608, 9403817943865580573430206416, 8904115573448118947667419040, 8572907974509531792069275585,
      7242295634736021384945557378, 4581070955189000570698120964, 9162141910378001141396241928, 8420763506472960083599490064,
      4286453987254765896034637792, 431935398335134046939157441, 1141047139831027236792677442, 1928225505167509614648228676,
      3856451010335019229296457352, 7712902020670038458592914704, 5167727856309088123066075616, 6451512340082746452402577857,
      2999504365882450705612161922, 2392253503171269575723820740, 8565495107891186614002150472, 7227469901499331028811307152,
      8177516327182894325797785824, 9705744671963220616882474689, 585921148211486517113738050, 1171842296422973034227476100,
      2343684592845946068454952200, 5098240444194392728874931408, 9804632493123131408037734240, 3738722939082334044764582593,
      7477445878164668089529165186, 8751399291716737680167270852, 7599278269150433161141547912, 8993704031492682709991347664,
      6821121626682688121978788192
    ]
  | 103 => #[
      10141204801825835211973625643007, 3380401600608611737324541881002, 6084722881095501127184175385804, 676080320121722347464908376200,
      8948121883963972245859081449712, 2585012988700703093248179085472, 5130256546806010754292540031168, 39769430595395432203818139776,
      78919881726271091143763623680, 52613254484180727429175749120, 63135905381016872915010898944, 42090603587344581943340599296,
      74277535742372791664718704640, 49518357161581861109812469760, 59422028593898233331774963712, 39614685729265488887849975808,
      6438860191635450928237222630481, 2736515581445066644500819617954, 1609715047908862732059305657620, 3219430095817725464118611315240,
      1962813832611451976511024318001, 3271356387685753294185040530002, 5888441497834355929533072954004, 981406916305725988255512159000,
      3114228246229980891865916536041, 8384460662926871631946698366266, 6627716524027908051919771089524, 8065052637672514617396347952313,
      5988900473519194022819070261618, 9103128719749174914684986797660, 6835804024107401419930462647697, 9728029704611030987968230268594,
      9314854607396226763962834894180, 8488504412966618315952044145352, 714448870578728116694815113793, 1428897741157456233389630227586,
      2857795482314912466779260455172, 5159908509735258620573664710728, 178612217644682029173703778448, 357224435289364058347407556896,
      2865736834675423821530621529377, 5731473669350847643061243058754, 4161168905019116182181437307300, 8322337810038232364362874614600,
      6503470818250629516752123586192, 6666808946375282725123574754977, 3192413090924730238273523866946, 6384826181849460476547047733892,
      9272605837963197090261112921000, 8404006874100558968548600198992, 4135490749192199708185556620705, 7315769034690405667867788394210,
      1000083100829065812561357006948, 3569173887754508730039795565928, 7138347775509017460079591131856, 2922450684521346119758747342913,
      8647968135431840526345207490754, 7154731469037845840716789338500, 4168258136249856469459953033992, 8336516272499712938919906067984,
      6531827743173590665866186492960, 6067176039812300620568215210305, 6792633427274964789402741332930, 8233625334341304139700369260228,
      6326045866856773067427112877448, 6587396410865992761128866624080, 3033588019906150310284107605152, 6930465410516459692932044504897,
      9629509574518354507192531370434, 9117814347210873802411437097860, 3908162329812287870952234563656, 4267917553085573726226417536976,
      8535835106171147452452835073952, 9060390475229210101854465601473, 7979576148632584991735305559938, 5817947495439334771496985476868,
      1494690189052834331020345310728, 2989380378105668662040690621456, 4530195237614605050927232800736, 7140870081996408559665087681473,
      8745949484651757289124206195778, 546621842790734830570262887236, 1093243685581469661140525774472, 2186487371162939322281051548944,
      8641037441911121885819356662240, 8771066990480575092738202083777, 7400929179135314973502778524546, 6687268465644224754030994630340,
      5584247432049243944759657655368, 1027290062272652677545689667728, 9456135896153205152355913863392, 5525966559727617725567380016833,
      6239803719146528072008699827010, 2338402636467220932043774011012, 4676805272934441864087548022024, 4095252130243090820995581367504,
      2762983279863808862783690008416, 1518977331024387790521292632769, 3037954662048775581042585265538, 7575040919403960977863614527940,
      5008877036982086743753603412872, 8664670458714871564804667921872, 5830091066425111501247459137888
    ]
  | 112 => #[
      5192296858534827628530496329220095, 3461531239023218419020330886146730, 4153837486827862102824397063376076, 2769224991218574735216264708917384,
      4886867631562190709205173015736560, 3257911754374793806136782010491040, 3909494105249752567364138412589248, 2606329403499835044909425608392832,
      5172093368812902229197692841557760, 3448062245875268152798461894371840, 4137674695050321783358154273246208, 2758449796700214522238769515497472,
      4867852582412143274539005027348480, 3245235054941428849692670018232320, 3894282065929714619631204021878784, 2596188043953143079754136014585856,
      412087052264668859407182248350801, 824174104529337718814364496701602, 1401095977699874121984419644392724, 2802191955399748243968839288785448,
      2009921364594126823947288901633585, 3349868940990211373245481502722642, 837467235247552843311370375680660, 1004960682297063411973644450816792,
      4292843859418558275556709563528425, 2371285179488346476021801473187130, 4742570358976692952043602946374260, 2330400952255788778159356620201145,
      4660801904511577556318713240402290, 3761348905395308203344926474710620, 726861344953741701470057883301265, 2037968990069778073382693358870194,
      4075937980139556146765386717740388, 2959579101744284665000277106260680, 4592362903445473784674895904938737, 3992428948356119940819295480657378,
      2792561038177412253108094632094660, 4892329880990150706602696117079416, 365797821736308795747745338262081, 731595643472617591495490676524162,
      1463191286945235182990981353048324, 2641873156984452413733716331892808, 91449455434077198936936334565520, 182898910868154397873872669131040,
      5063326932945767194596369817390369, 4934357007356706760662243305560642, 632915866618220899324546227173796, 1265831733236441798649092454347592,
      2531663466472883597298184908695184, 2876627767863086647713659631726241, 560958677191345666896822934232386, 1121917354382691333793645868464772,
      4613379585866892383326287154846632, 4034462313198957138122077980473168, 4598101265976295550732237972903329, 808470948378931387413784214191842,
      3509856944532568049155435829487716, 3745673745761487701948307657835880, 2299050632988147775366118986451664, 2547677238804037100510148180045025,
      2730865831199688315069143793284386, 2288469550850521400082579097618084, 4576939101701042800165158195236168, 3869987048669432364520322254632560,
      4495476177893366345024074907195457, 2087594952509728058980938464307394, 4175189905019456117961876928614788, 3158082951504084607393257528009480,
      1123869044473341586256018726798864, 2247738088946683172512037453597728, 2663062834118181126157658133678401, 2714494315514772966386360788016066,
      2776782536232794317008500169801412, 361268213930761005486504010382728, 3261914137796959095804662698029648, 1331531417059090563078829066839200,
      3627340579662339630367516399058753, 4370347574359627495655851557863874, 3548398290184427362781206786507652, 4851404057602561519194345291921480,
      2204909359549291814724503182069712, 4409818719098583629449006364139424, 4957968333766236793544983779389377, 4723639808997645958559471229558658,
      4254982759460464288588446129897220, 3317668660386100948646395930574344, 1443040462237374268762295531928592, 2478984166883118396772491889694688,
      3566703755522864567962407688377281, 4876524254361052659036464514839618, 1602856980531272698322403114482500, 3205713961062545396644806228965000,
      1219131063590263164759116128709904, 4379500307028846098246452008798688, 525972511883598170903393109877185, 1051945023767196341806786219754370,
      2562270878525754698171384656668356, 4650256046668281771028680202153032, 4108215234801735913526864075085968, 2859134685209212899716944719548640,
      2114896565339501341816081513762497, 3748344375592879721290276562096962, 2304391892650931814050056794973828, 4608783785301863628100113589947656,
      3533234523165633744587817305134288, 1057448282669750670908040756881248, 2648373430607567378115637585457857, 104450002680307127700778841695618,
      2776123951817856973846663415069124, 359951045100886319162830500918152, 3284273821448459645032285750613456, 3920335144571197503323066957338976
    ]
  | 122 => #[
      5316911983139663491615228241121378303, 3544607988759775661076818827414252202, 1063382396627932698323045648224275660, 708921597751955132215363765482850440,
      1251038113679920821556524292028559600, 834025409119947214371016194685706400, 1000830490943936657245219433622847680, 667220327295957771496812955748565120,
      3992856080723560520940618873682591488, 2661904053815707013960412582455060992, 4137674695050321783358154273246208, 2758449796700214522238769515497472,
      4867852582412143274539005027348480, 3245235054941428849692670018232320, 3894282065929714619631204021878784, 2596188043953143079754136014585856,
      1687908566076083648131818489244882001, 3375817132152167296263636978489764002, 421977141519020912032954622311220500, 843954283038041824065909244622441000,
      2058159477344385867722023835272791601, 3430265795573976446203373058787986002, 857566448893494111550843264696996500, 1029079738672192933861011917636395800,
      1214098011898033395723162354271810793, 1632752498759424221834597648848297274, 3265504997518848443669195297696594548, 962905319781198900056301177525918905,
      1925810639562397800112602355051837810, 3139908651460431195835764709323648604, 2550144618885554107309943755530368401, 2977224068930526009221357090001985202,
      637536154721388526827485938882592100, 1275072309442777053654971877765184200, 1609012092190707211000598261633948401, 3218024184381414422001196523267896802,
      1119136385623165352387164805414415300, 804506046095353605500299130816974200, 187288484728990103422845613190185537, 374576969457980206845691226380371074,
      749153938915960413691382452760742148, 1352639056376039635831662761929117768, 2705278112752079271663325523858235536, 93644242364495051711422806595092768,
      2455827444161384407860990637209275681, 4911654888322768815721981274418551362, 3630048419982462733242141480352020900, 1943184856825261974869054719582663496,
      3886369713650523949738109439165326992, 3736138069054404151561140520340975265, 2155364154969144811507052799560572226, 4310728309938289623014105599121144452,
      934034517263601037890285130085243816, 1868069034527202075780570260170487632, 1655748502280051481423430070664893857, 4336376347824960001210378219112972002,
      4946576466269688470410187941247019108, 3072393117139844616163471638226912616, 827874251140025740711715035332446928, 3413886713296185789045046236477648097,
      4919835990863681452533449167564715298, 2608821492535333990922391736366106276, 5217642985070667981844783472732212552, 1706943356648092894522523118238824048,
      1159275048421257389604103509853742433, 1837058039841563744635046890795069346, 3674116079683127489270093781590138692, 1788492505745306809062568782979111912,
      3238093515780460440609665875487560368, 3508660072689301109755860810884575841, 1700408162238938727896493380647773378, 235103281159278270061187515753839588,
      3952325814571479549722407588875306408, 4412786027914482300685544526002977072, 3556026527415715464259883564093741121, 5261884312648290115760373719964264642,
      5206856642156916739905519198807150980, 5096801301174169988195810156492923656, 4876690619208676484776392071864469008, 4436469255277689477937555902607559712,
      2089966399965118887795417182480156993, 3611360810997219974795081309595982786, 1316427887745544184335224071462485700, 2632855775491088368670448142924971400,
      3180947591561111467756468416180728400, 1044983199982559443897708591240078496, 756510385067212345767289484135972673, 2257827184178474818277891258439385538,
      4515654368356949636555782516878771076, 3130614112895568793894553135482419272, 189127596266803086441822371033993168, 378255192533606172883644742067986336,
      4096487892859210408075576091204825025, 2876063802578757324535923941288271746, 435215622017851157456619641455165188, 870431244035702314913239282910330376,
      1740862488071404629826478565820660752, 2048243946429605204037788045602412512, 3176060084320302545600095664841855937, 3514869200623904529545651983067624514,
      4207363312393741651808024429782760260, 3097814641647819812000820618444142216, 878717300155976132386412995766906128, 4246486033729983018607661952981617120,
      4761862191788320533533368527004705217, 4206812400436977575451508812888032130, 2333903560360663359908364236476491460, 124073083792969317227230095774215240,
      248146167585938634454460191548430480, 5039387087463992012574298384063041760, 1549419360408718134643903987621351105, 4645661735905728779627553994884862786,
      3974411488671794067639879748648347268, 2631910994203924643664531256175316232, 3819871425546263940714502619281904848, 774709680204359067321951993810675552,
      3185526347712456903667309887397376705, 1054140712285250315719391533673375106, 5252188247930528589418178452256586180, 5187464512721393687221128663391794056,
      2220395032415819857027554218327594448, 1592763173856228451833654943698688352
    ]
  | _ => #[]

def clipShift (dim k a : Nat) : Nat := (a >>> k) &&& (2 ^ dim - 1)

theorem clip_zero (dim k : Nat) : clipShift dim k 0 = 0 := by simp [clipShift]

theorem clip_xor (dim k a b : Nat) : clipShift dim k (a ^^^ b) = clipShift dim k a ^^^ clipShift dim k b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [clipShift, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_xor]
  cases (2 ^ dim - 1).testBit i <;> simp

def plain20 (n dim k : Nat) : Rows := (units n).map (clipShift dim k)
def coded20 (n dim k : Nat) : Rows := (encoded20 n).map (clipShift dim k)

@[simp] theorem plain20_size (n dim k : Nat) : (plain20 n dim k).size = n := by simp [plain20, units]

theorem encode_of_receipt20 (n dim k : Nat) (h : applyOps (basisNetwork20 n) (units n) = encoded20 n) :
    applyOps (basisNetwork20 n) (plain20 n dim k) = coded20 n dim k := by
  rw [plain20, apply_map _ _ (clip_zero dim k) (clip_xor dim k), h, coded20]

def entryShift (mir : Bool) (slot : Nat) : Nat := if mir then slot - 1 else 0
def exitShift (mir : Bool) (slot : Nat) : Nat := if mir then 0 else slot - 1

def CoordinatesOK20 (n : Nat) : Prop := applyOps (basisNetwork20 n) (units n) = encoded20 n

def ActionOK20 (n slot : Nat) (mir : Bool) : Prop :=
  componentRows20 mir slot 0 (schedule20 n) (coded20 n (n - (slot - 1)) (entryShift mir slot)) =
    coded20 n (n - (slot - 1)) (exitShift mir slot)

private theorem schedule20_extent' (n : Nat) (hn : UsedWidth20 n) : extent20 (schedule20 n) = n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem schedule20_fields' (n : Nat) (hn : UsedWidth20 n) :
    ∀ pair ∈ schedule20 n, UsedField20 pair.1 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
    intro pair hp <;> simp only [schedule20, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [UsedField20]

theorem logical20_action (n : Nat) (hn : UsedWidth20 n) (mir : Bool) (slot : Nat) (small : slot < 32)
    (basisOK : CoordinatesOK20 n) (action : ActionOK20 n slot mir)
    (x : Nat → Bool) (ph : Bool) (tape : List Bool) :
    run (logical20 n mir) tape (frame20 (plain20 n (n - (slot - 1)) (entryShift mir slot)) x (n - (slot - 1)) slot ph) =
      frame20 (plain20 n (n - (slot - 1)) (exitShift mir slot)) x (n - (slot - 1)) slot ph := by
  let dim := n - (slot - 1)
  let ops := basisNetwork20 n
  have bounds : ∀ o ∈ ops, o.1 < n ∧ o.2 < n := fun o ho => ⟨(basis20_pairs n hn o ho).1, (basis20_pairs n hn o ho).2.1⟩
  have apart : ∀ o ∈ ops, o.1 ≠ o.2 := fun o ho => (basis20_pairs n hn o ho).2.2
  have size (k : Nat) : (coded20 n dim k).size = n := by
    rw [← encode_of_receipt20 n dim k basisOK, applyOps_size, plain20_size]
  have fwd (k : Nat) (m : List Bool) : run (cnotProgram ops) m (frame20 (plain20 n dim k) x dim slot ph) =
      frame20 (coded20 n dim k) x dim slot ph := by
    have step := run_ops ops (plain20 n dim k) x dim (flags20 n slot) ph m (by simpa only [plain20_size] using bounds)
    rw [show applyOps ops (plain20 n dim k) = coded20 n dim k from encode_of_receipt20 n dim k basisOK] at step
    simpa only [frame20, plain20_size, size] using step
  have inv (k : Nat) (m : List Bool) : run (cnotProgram ops).reverse m (frame20 (coded20 n dim k) x dim slot ph) =
      frame20 (plain20 n dim k) x dim slot ph := by
    have hr := reverse_cnots ops apart (frame20 (plain20 n dim k) x dim slot ph) [] m
    have rev : cnotProgram ops.reverse = (cnotProgram ops).reverse := List.map_reverse
    rw [rev, fwd] at hr
    exact hr
  have c := frame_components20 (coded20 n dim (entryShift mir slot)) mir 0 slot dim (schedule20 n) small
    (by rw [schedule20_extent' n hn, size]; omega) (schedule20_fields' n hn) x ph
  change run (cnotProgram ops ++ components20 n mir 0 (schedule20 n) ++ (cnotProgram ops).reverse) _ _ = _
  rw [run_append, run_take, run_append, run_take, fwd]
  simp only [size] at c
  rw [c, show componentRows20 mir slot 0 (schedule20 n) (coded20 n dim (entryShift mir slot)) = _ from action, inv]

theorem plain20_bits (n dim k v q : Nat) (small : v < 2 ^ dim) (hq : q < n) :
    rowValue v.testBit (Matrix20.read (plain20 n dim k) q) dim = (v <<< k).testBit q := by
  have rd : Matrix20.read (plain20 n dim k) q = clipShift dim k (2 ^ q) := by
    simp [Matrix20.read, plain20, units, hq]
  rw [rd]
  by_cases fits : k ≤ q
  · have equal := rowValue_congr v.testBit dim (clipShift dim k (2 ^ q)) (2 ^ (q - k)) (by
      intro i hi
      simp only [clipShift, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
        Nat.testBit_two_pow, hi, decide_true, Bool.and_true]
      exact decide_eq_decide.mpr (by omega))
    rw [equal, value_unit, Nat.testBit_shiftLeft]
    by_cases bound : q - k < dim
    · simp [fits, bound]
    · have high := Nat.testBit_lt_two_pow (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : dim ≤ q - k)))
      simp [fits, bound, high]
  · have equal := rowValue_congr v.testBit dim (clipShift dim k (2 ^ q)) 0 (by
      intro i _
      simp [clipShift, Nat.testBit_shiftRight, show q ≠ k + i by omega])
    rw [equal, rowValue_zero, Nat.testBit_shiftLeft]
    simp [fits]

/-! ## Packed basis & prototype certificates (5 widths, 23 primaries, 22 slots) -/

namespace Packed20

def width : Nat := 144

def basisWord20 : Nat → Nat
  | 83 => 2735986936219979538286936004454090525789170290271519617104787732636563415903753784748670318571977899290488326080049261329188699743430656548932560403529818793451095629964983993255138939059221724537373302474617281054815824434612616700252758184150600021022555714742718543178433978701977743156887623871183095829641720224053253985490937977261865011670260534913956434152149338083933357042957738013572823639696902261232603231271301165466274076346907998167801535436995380471025379774810970428232289235403994448232652576975198922043272222265338172425616190341765004088210001236086583417714955189429426100101302189201552931130828273471491168118272371414509636941824210808403514711559911158005467897153083695398066833905426926697320102908764595395955125814632715724560321001589917053279011434448982801419471334764706426123299390766834934730033306878630798947376088877302351952761201066754401534822028590639537603392869133226853194121820506324675435372550764312938440816489002211891332476432950135893015840630064877930867756681843316321028771404847675642849033838023087187362535162941139379087394785090815306114662712769480934904330008428647441083182811277335892994069296871486417825708333052610522608157034730908838212510385865555031787851372918439535822121566918753601358460342259240091947848455433124331498590625594459090408643790299202744134049457996415865349472505215532220012568476416111305854406805957342136059056679613125367422127314987081384391504324469550905829011995052284788354070066390143121018702588405980969529832348846100380018092107863969374861757047687198856189127471045299957658437122538288363917679100177066994911334433216225223357373772739104815338842054960233038519194226344546492412847087128860015977617161992315186743844397290997432457424285822132358607250256339606874640883472930181894997684509648999703053847834014877172831001371712597259796512693243996171102644476327720712431503448623464815211556168535007531986890196745860609270464731570986219952828667105769876703188921552419145295366773520458907314688442859408419782869184230387835517726590544547796385637688668216321139037775667851385174388455433489604820021518195487010548432227391292925425512767111722493256704469761582388982601791648608027970779449369817980563864697511190715686226045600238347132819795841516562932024684587885126905680530736226885513243145253022717206459310439993233789804182628376218586822257688710045757809249610882248305465420155851799684878586529016922839912446780043672265815722390883269801791066318736899433304743349595691601157238451385090125725619124972709464795587001165021879282436889476639590415373992941712628647825594995201368506372111297647232335267290876264229206332984716790336563084508467002108163202168547555734899796420767888324833161716987870134850234874886949133741421849387856401950720573288985621332884745774093701075717261021834455613484224639879664713074340304800207119731491026081662353118808825314613074088088095726572964082910247682524594819158160500615854212963106806614581851197800316932294598437968122833317763880020162387738583043309028341541178178469681482929889116084832969107586095789911577894055025685600078882152933427701013394622817608288238810882861140980548329484442466748531116139828319600686428418528399869457007669130886237718307010225716562087490940094447707137228333862451817110483020037549635698767196257656569055357960529306549799343194043550564076529083771738117968673455338401514029603120501569981293575802476651619510691867355680222808187554371683283299198212502476937587857135226228711888037897428407871419073253221016718781291329325367295
  | 93 => 75724837472024789566986862321972290151572451081732280484272265879406717908187116586371810525597671188613223875931326241826475486760880666596858506687337934079569082595822134642883710731196728020409421839731463669336317037612393322187552422443485153843391404901510495474710998437934011054478285789924191105272871206596439316210003365674976508142983079250872114822066981514549584089042556224607828374201859232295236574681983738013847689207603825435816383520102987545073194242352568799982428157740656856799045665005649203668781782138980721336444685195365786405784099453088466755500460587423712896424562612156126141233874954152140094531245950417128258340051692112993009951303906951855418818591270667809588918171311776880733582131197129262569702173191286259802216121898198366232561079356834909886956229876096132164414818680795980350451739716510921858005313009929836301867045544229818636614254190170333865846369508226854852212241552512859624853952143471471604503715623904214061440271698807533491864132734560113244096936018939058480092267777491004060689020585420691571597269797162149474326801679369431577123417964280898178132136504784773528389774125798257624671596440690083922046995025123300110143811845261166362008478818705609196500002841584927917130984182704719681288772692128251113215308276309098672363936206577861818974043320778876990093153421329284141220877388857560929640891673562729678204145842796335311705606103515702962181525081363214894402631390289216587767189791785705499236007985237793624850578886226784476795929771560463836995413450792798422093543751233321272256815690085229572304553122231939746822987411536507499522306346006595239035557093712851879907525764403522090788105624645675222507167484270069963587071683542456221380939046213372256232520835074190512152566392786272732561442272803832078505820717801630286754499103858712397663052293028374628344398695861617881751559308320497411082201224728769186007445000014538314919624258064921850885398335016470684931656724762044161888734869394273822230832412396494283676514827054796120058513750521420779553290299936074765714596826596538900443054633677908487431716507883970130837816924223417675822633648639001247992134343947669225987047791267045652414296037302714851237545794844869144861077687530795350129259666881635764986011887192163807503994120298206542154530244653427444251736055648671048508540222382243251866617133317286073325184201868453830055899708926512037475610188606236744414096466208451469429756286475329551534560705585017068728024349010832986895611404416912018341698939498105971070622510698451779650978855353142916782695661641065259053264039051060469771317543671905357736085494565692040707136740246509485231125016557531051017816615017251051880644003472222648194993881513296355576920153709397766483182768358290346091636965898127163092666241239686315332443678040896120355783041842631248470883388741085468705535491574071207338055968918155545668970377414274387748844248469858884901586170979457911424343367435596428215579961537500719477962481740664900269420991865944422568883106716823209270152681435587629541235844751300698868282314323354924549645645804478865703900137404687021350729217568706203354568631187916239233231995077061405425586459384458055164891460812182792133768926946503850493896754284144060951796911421723507199594860826563439579298432633192958369195575326375575939841637666875254826227502298945523678585180946890217605037511683162560849348216338338915292868458010517580780129257626507658710830719267739033442414641698027252045139430391890793887270405976263077482826802712052983861634887699736650253932297367651423262009456400914627078931651341219140687034250920930234900128755603204851786629247645629169908657812914898565684654752197111103843704913939341522598152519422443340544859619111327970013118018842226522586674817077908205123340099251701711813240686977339662408734122972254470109341807754561851388408605578587651546837511321297882634819832049154051549175732563494638102290846353723559130620016376199388567879156838297906119176300792880562175
  | 103 => 1969026907953383298339515940734303759448046466878770577939213683733320523308260312026907388664356428353255861781623323349105408749209492230086440053227452959449925057841253648993659828620235717568139665657164622373634944288799847370925595661755299066333409818376078140163407478406539381894374489780652200989076985629178183356385389042940891326600665639305325886258079444128933924902213697578914341498320494032624993171865039105988260512424971210629206527409524175153980603801565301123776932626481950087555134292150661598413027197372774028131876313287939111202386556830891801464790966653213737628096003585576126181832200914360256507767892352132901311808078749405231949020553825214026536755164160007571270699103005997018300989977541598365036361437108801878856871463043570441693456783614238143061611178451848250735649038894052784903936728826783830386278121366172125225126685800370664999237628532213443258814382567206237535825646172779606187883846006551625186212491536022904736746521406353059439881710312742970729074099476852504764101467948417718175169368557140336062441608365145772689004897765972345971190242204983597352416717364716585797341711604830306193074419428202824440982540076446650283164403385731435699432023895021760537731912419050466942901009547667421554409683744256380470219592782253421475348637959515762288472567911029940467809365154590897183945486278497746070559231871621026903478711218791370405893941426295514882829808528590412081038185019779460511371020983370708027552862904044921324474917665806982848461454796220454714697025500898963929917186555728305401103760797987168800832754783619602539088844934718232072255202294916929636019924793126192304560404678870664000564707955265636074633822090141090414233359311508852355797008085785060679287802858306431462072716635653202671041693855758185442041969486820076232457111521514642762600944365619865894424516669809200133828950557844055343119031358005927128264610694791130142464393578076263732949283805319586951279084188086567278023149313998385454984639848548143176342732906265246255208536921974033129068108348393725288992360816736232431255813064775613649338382152493741611316967107777037074812877630042224367843816080150739469092688476787163344347741145817810375633598939221413634882949214539687349548435394557682015919901453923593665869756893712212313173910749264839840948806672254950905247571624896737894004742729157373103169586204719813361358757764251885982856116821133882630265044293964056451237935771775440342480506972622229663700160192627794409980622305389119540776882351121186908015224704048220047554381360638668827893971879129729874042373906193365025672593978299331799806907465014611439584087835808078475580949782939809980433754247444790837387520427316863086392906104718741344030564810204435056821264408479137480760944425923320822881863772826248099278689601887913743782815187297446349156333151800751730616244715922847947297383649299880926505376853655662791383613561101453494457160345512692330096285821158228840246077659008466406572468037766856815802873619555816485359799113985502301718300117995997305319226497283683496615968911870361858100888450694131012285201848097586006176985014289805469307096977354878233101176890256152748503113831375328888940863374522910027032707535925542913760933438985172860087379305753745449630756565316776422788349511980799687064357454492553633600425801216901252285259462483591800920149612445230278912106275240665513852948180223006223528478748389790437485674129016972826140545538857461899112393395528560067309106258588833636153290603232769748845724954883588952371503826473567324298648149776013501133851130972211299665033047866042470919167023477741353414033771281673027489925724482733531827824430491665114969929053952620001228853850468986036402775606562212510233158530426524886939035335563968098589039743025570279146040284144750234267419733650741541610130429259064418622389109295848858970357554611902431037600733333883649615549703737647560965122182405041091417099809058035867913927959808803523776406941031550716618241189453745202720246787888874267956839634987073423816105677931778479852808468101779499924893461587607087662677300572980056492029748006370513498157869579702492648913604727131695071253861629516338562554606298552196108332677718172990916954932939810388591906252134455263382063248628147103908126069621296877698271825277829865896265494206698264033902447389910424615271044781364716643081418498198640838413685978203178094299119739813765911978535628685648592895
  | 112 => 1806233483998725152929641389825925686889996007214794703779321245243591296197779548268628782344625130947143048449981806377705604073563168860307147727928952371591038541534385144806009111939758847428154883299654841779098639039316493589310257993940009960194734197542742397553456308857139716291632269659179565447722434538567719313587232582804191496259184782545022459094899448427914199107820111075489755377473352362682150688189417748281303264688354441902983486256468156600565951955957983272431413271796403854504787720482556552568688559283629329273569979169160681772010155662915079588826281687760841996788874145565390152644899984431029177191965258245793108472190266084218137239405884629238852926675549523576962868236191383913669050154195107382323616181775148939032995643069336427771480813794466953074903159085985675675362162569847527817312827450900349273089652921117132961269668146168946112781364092632904661088655843162919028843799299700425943297693088950519126088669523811184197867940904046685620191532342442678048238996864781264157750928208211260143482010376481145852241118604786351121114543886385569022595660690021908031712228380000806143457209737859921359522294726626653003773162482511360801397754315867064593876111643620031085081538961139800158630251064632439260688126220246882453109019245111536996069418883783541870176191417929427071764696501349401379927017962675876841760746348801174444390995219479193516721637389449550613558826586867169000993691772680590911491052586997480335289140859047035868540609689141831043431211987928474921356794684491763713694773751834660819669406400244867366987735429358496295550220851129820633731482773089280421088503050634938309640566520544420377421717705020499962227706691803685545710470304773856799776934658324298580078878068365515706864199950957066360100488192078104926736858426395243122564962886347359657648160124834062107172648155152313571505252238532384459062258382140680718833852299563319813508775804425107517028241507983657741573834015395204676506615006797090688757634010221066044241416307679020156528116746914447443856251002709932515830252574098820296281630319494933947330269996029778967010129309992286560814362963474620561487294956501876732482794556520917426947387688078180286463296650249748628019722495410900805926808590972385369038853167197190873262439326519660906106139364813659036187747626898429251376323610441533797084380724952669842794791909511135495574492284486377344164121271393750890256207472828045336232069994385797056240981593436052064819801513216448704013070199549782991618390601105472412849846225142157527272576238476200614487694914128220618126633576276430259531025974710396666031429816790921118362630934068941722816475075482599829236956609027897706198331682135050891755337833318775882557839769470919420926560575098967844830095862922487841866508220071111756673751152277229325864345100509993746562182936680445390848783856436552324807488928844921504149161851039634526170658980223279013706402861499507562188785488198909664960413771007839851049692864821937010416516636215352461357268298943460879097914775672299187396136503840167890996381834678421242455333453541896377186400413045242376787426290568979954142463220693506355100988380117202369797004141739298856740677843481889753351415081586846508246690383595106225562829826194512359647019166990311926156795250752694648016955055323428142188600915792556157987595121440452588408163237256015087940632362561098306668011224761716310128662543327666374816977055485753714222068671351752891216499108498584277473788544941292612023829241239387894130083198481933976357038209356137213188797803695161879964063961485139614044300169954597310197305916636817415382250466449244002389170655304568377981449789457280247927621316342128109887648161207055211603907325852705102432577523387698696722160902966074361310005629129120747447365967012193466435817932440884770056265573488973991496494442275473732204805633171472101353472466908697361835240889270966632524608183076606921234929861869081749210479419486150468883686358574316907324059360758334359312900025937551875531005278400659926525662092220208831087430441817799252331383664563049642619660092483670297491295027179896306612715042289825529136021929247218727599827885240284369325227838107583179151491962422314950581807448914466179027220949513754649648087167493081886999678219869215539653337692845074695807006818937314867015989445490604317913877126596989841106550866216809941611985350018395178642935663577283098627938733383761352881887941859004647729063780359518236412566336036374000825147518599530604662456951847085132462067902795557210953612614586090037687137706469180201737167994008835613895197649240022077210463347264017106870459546568986452903963783353079710406616471482948453511577358384040664375827387813382807092704878406890503863011576401053640272973558134973449648039795331918159298042492354103321136827742758893518847
  | 122 => 22325215260204459480086264861233432110215136763842808336351236663373425882893220478165235754895574240006526884645813340805292832885514100195732733780566502332424176603584591594951883932946573249701519157237401195674810759993449445220163922710282257814026621733171213250751183619918960138949135165175199749990784247829625742857146676140863967290140036539685876495475533053266405540926388208575920683220801286326131044983233873549246327403998523078100651813723443685233480408310054755810411991622064677910497479270351216391118508050667176848818308965603363850527848919924502024574482819747068433492748493726337126469710162116337959079998159575365923671065881001880391771074317577784391692474398854000405996994338052534806099722464559473964254849525073106274383781344539077175463937044003421194029797207404822797454671594860832434453978350357184219201310957861042442240957164898555337855402705777600112358322325703995374206674554777386968430851451261236022612129811902479712309112046128680648338652248713749901243847230080549866809529029336796860101451181111712030585314079976597920822713095227674061945232373241570661534537580319505280414099508967858005529797921078934714433463242923066032531515511802689911195653515686315520514765460974662092349217946980319986786670530159043964018396045193888707282102512140968792480961060592836919235789128282353946277392459789686104683929796715134921818570554601565987838648394040578712932038093702385481285368493913140348574883098711655530293314233439910174556913256557175694910796890543057482127921976468173609363134511390010466292310121597100366733417603428354213594727556153533563740697228896779230005028011085622241518375886045348691309852602491393128691340029555249589062833904157977490646934504463714595364267654957421042822858447084810011895037469035412927039767575311408961311556366456252965744376987220761788877455171419072484555356175348919772345543366965627512852299375890000384076885553477688887936654725384155100543374499629705044829100509391038210521907846277318465482312560915241596705154534910685642538847899128088389267068797408851057349690080653402909295812865872326041795429103007656529631061026201256851336083487346526474819192576494233222408659852899003976382754971879299243823988148023876587489169731026828488271121109281227343173310264361134517555883951986847273555630328613996318095386866725309373771721347114781084812855718151462175841390902225597772402027008544906438443648894030096420518090924502990875022275554679610392528630187041596987074915070285988097616752426220238510016924543474686237310791510535821975084835435879461706269824824940892562666345681379526071561925421918782005299800689808435198854625888993031236811163965860034610331378867400432220165391874290947619778714912374815886659092504506645135484206425375615160541545578130206996970784329706491706280519218305352259309524168247336749281057696722753037587632499739376595055458997030080092671605057343399542282431915240316209333648538193935919885596127130011289936574217489541948435813403964785074871265198063186197615701472228456571524112903282893645169724780680568114325361143917329252926543440331482543625329359123408044281339214578214855907309485803803390730408238173996137202945346056719797018689661801974581033284496689990856915644147481582697010311456783133787128164818346838389338285425134616390071585652901727090182689940532592878299072351449293612105717103111176698532548228265614376403796078459125626998642115102418156913796909240983970373109031758292050263342608357318191319511493126763218621206625785663103599136587636486289883598093010078791639555113951179987443479652182494573441372265581913321095239223327924043961568781041578844507199105697305769102075980673557563443915436956511939509875773864113239841954968199656452860023980710556894237549519470326646450863058607783338725179943671577518485875548006428175540268245994789034706972147325997665958225535720131773510195772582362526742774441793195789184673291375084054382007197457147744627113530559008675602757340257129010673992073926740621400179359055000016978978373564350659700956986613514998564197685516205230171289359676824810870932906641573829459830694556253795488038349270120284267920508213466567191255476245740691969174647907964925750179580513953458589087754543267168356886977585777152705003607454680462802632700592132454379525122534451199130675160946418954428312104626918631469219379603792725821291582937383749814318682102007582679271998295116173848232591752563896662598527723459394658313054560979361537597542363905867095561901481702191352293066291138755855792160821120931829752627186933840847344261672823716068473342012376412266077253598367509269953254086543145321624839120230633504764673030867931042542691944949921291420089429435309825630485182488587856851056944580460262547481693667392058086750536886834857072001224453423975434103240662009057413209436819168930000348877006882880243654719841219042577161270782623298107711425725736854868552411768535747391631244975048861391098365282463822322779046420809249756087278306505240041575987538658244643939130020470022185604228076971319923858842933547185331329955259879743684115346039235736451014524086114386725892469641707240124851325532297294635096788696677352178467201873773893228882868805370790265981702389489292768329899339969468563455
  | _ => 0

def digit (w a i : Nat) : Nat := (a / 2 ^ (w * i)) % 2 ^ w

def mark (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, bits => (if bits.testBit 0 then 1 else 0) + 2 ^ w * mark w n (bits >>> 1)

def unitDigits (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, start => 2 ^ start + 2 ^ w * unitDigits w n (start + 1)

def identityWord (w n : Nat) : Nat := unitDigits w n 0

def step (n : Nat) (bits : Nat) (v : (Nat × Nat) × Nat) : Nat :=
  let i := v.2
  let y := bits ^^^ (digit width bits i * mark width n v.1.2)
  if v.1.1 < n then y ^^^ (digit width y v.1.1 <<< (width * i)) else y

def encoding20 (n : Nat) : Nat := (pivots20 n).zipIdx.reverse.foldl (step n) (identityWord width n)

def sweep (r : Rows) (i mask : Nat) : Rows :=
  Array.ofFn fun q : Fin r.size => if mask.testBit q.val then read r q.val ^^^ read r i else read r q.val

@[simp] theorem sweep_size (r : Rows) (i mask : Nat) : (sweep r i mask).size = r.size := by simp [sweep]

def pivotBack (n : Nat) (r : Rows) (v : (Nat × Nat) × Nat) : Rows :=
  let s := sweep r v.2 v.1.2
  if v.1.1 < n then applyPair s (v.1.1, v.2) else s

@[simp] theorem pivotBack_size (n : Nat) (r : Rows) (v : (Nat × Nat) × Nat) :
    (pivotBack n r v).size = r.size := by
  unfold pivotBack; split <;> simp

def fastBasis20 (n : Nat) : Rows := (pivots20 n).zipIdx.reverse.foldl (pivotBack n) (units n)

private theorem backward_row (n i donor mask : Nat) (r : Rows) (size : r.size = n)
    (clean : mask.testBit i = false) :
    applyOps (elimStep n i (donor, mask)).reverse r = pivotBack n r ((donor, mask), i) := by
  let xs := (selected n mask).reverse
  have hnd : xs.Nodup := List.nodup_reverse.mpr (List.nodup_range.filter _)
  have hxs : ∀ j ∈ xs, j < n ∧ mask.testBit j = true ∧ j ≠ i := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := List.mem_filter.mp (List.mem_reverse.mp hj)
    refine ⟨List.mem_range.mp hj1, hj2, ?_⟩
    rintro rfl; rw [clean] at hj2; cases hj2
  have fast : ∀ (ys : List Nat) (a : Rows), a.size = n → ys.Nodup → (∀ j ∈ ys, j < n ∧ j ≠ i) →
      applyOps (ys.map (fun j => (i, j))) a =
        Array.ofFn fun q : Fin a.size => if q.val ∈ ys then read a q.val ^^^ read a i else read a q.val := by
    intro ys; induction ys with
    | nil =>
      intro a _ _ _
      apply Array.ext (by simp)
      intro q _ _
      simp [applyOps, Matrix20.read]
    | cons j ys ih =>
      intro a sz nd good
      obtain ⟨nj, ndy⟩ := List.nodup_cons.mp nd
      obtain ⟨hjlt, hjne⟩ := good j (List.mem_cons_self ..)
      have gy : ∀ k ∈ ys, k < n ∧ k ≠ i := fun k hk => good k (List.mem_cons_of_mem _ hk)
      change applyOps (ys.map (fun k => (i, k))) (applyPair a (i, j)) = _
      rw [ih (applyPair a (i, j)) ((applyPair_size ..).trans sz) ndy gy]
      apply Array.ext (by simp)
      intro q _ h2
      have hqa : q < a.size := by simpa using h2
      have hja : j < a.size := sz ▸ hjlt
      simp only [Array.getElem_ofFn, List.mem_cons, apply_read _ _ _ _ hja]
      by_cases eq : q = j
      · subst eq; simp [nj]
      · simp [eq, hjne.symm]
  have hsw : applyOps (xs.map (fun j => (i, j))) r = sweep r i mask := by
    rw [fast xs r size hnd (fun j hj => ⟨(hxs j hj).1, (hxs j hj).2.2⟩)]
    apply Array.ext (by simp)
    intro q h1 h2
    have hqn : q < n := size ▸ (by simpa using h2)
    have hmem : q ∈ xs ↔ mask.testBit q = true := by
      simp [xs, selected, List.mem_reverse, List.mem_filter, List.mem_range, hqn]
    simp [sweep, hmem]
  unfold elimStep pivotBack
  dsimp only
  rw [List.reverse_append, ← List.map_reverse]
  change applyOps (xs.map (fun j => (i, j)) ++ _) r = _
  rw [show ∀ ys zs (a : Rows), applyOps (ys ++ zs) a = applyOps zs (applyOps ys a) from fun _ _ _ => List.foldl_append, hsw]
  split <;> rfl

private def pivotTest20 (n : Nat) : Bool :=
  (pivots20 n).zipIdx.all fun ((donor, mask), i) =>
    decide (i < n ∧ (donor < n → donor ≠ i) ∧ mask.testBit i = false)

private theorem good_pivots20 (n : Nat) (hn : UsedWidth20 n) : pivotTest20 n = true := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem fast_basis20_correct (n : Nat) (hn : UsedWidth20 n) :
    applyOps (basisNetwork20 n) (units n) = fastBasis20 n := by
  let rows := (pivots20 n).zipIdx
  have all : ∀ v ∈ rows.reverse, v.1.2.testBit v.2 = false := by
    intro v hv
    obtain ⟨⟨donor, mask⟩, i⟩ := v
    exact (of_decide_eq_true (List.all_eq_true.mp (good_pivots20 n hn) _ (List.mem_reverse.mp hv))).2.2
  have fold (xs : List ((Nat × Nat) × Nat)) (r : Rows) (size : r.size = n)
      (h : ∀ v ∈ xs, v.1.2.testBit v.2 = false) :
      applyOps (xs.flatMap (fun (row, i) => (elimStep n i row).reverse)) r = xs.foldl (pivotBack n) r := by
    induction xs generalizing r with
    | nil => rfl
    | cons v xs ih =>
      obtain ⟨⟨donor, mask⟩, i⟩ := v
      rw [List.flatMap_cons]
      unfold applyOps
      rw [List.foldl_append]
      change applyOps _ (applyOps (elimStep n i (donor, mask)).reverse r) = xs.foldl _ _
      rw [backward_row n i donor mask r size (h _ (List.mem_cons_self ..))]
      apply ih _ ((pivotBack_size ..).trans size) (fun z hz => h z (List.mem_cons_of_mem _ hz))
  simpa only [basisNetwork20, fastBasis20, List.reverse_flatMap, Function.comp_def, rows] using
    fold rows.reverse (units n) (by simp [units]) all

theorem digit_bound (w a i : Nat) : digit w a i < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem digit_zero (w lo hi : Nat) (h : lo < 2 ^ w) : digit w (lo + 2 ^ w * hi) 0 = lo := by
  simp [digit, Nat.mod_eq_of_lt h]

theorem digit_succ (w lo hi i : Nat) (h : lo < 2 ^ w) : digit w (lo + 2 ^ w * hi) (i + 1) = digit w hi i := by
  simp only [digit, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * i)) (2 ^ w)]
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt h, Nat.zero_add]

theorem digit_xor (w a b i : Nat) : digit w (a ^^^ b) i = digit w a i ^^^ digit w b i := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [digit, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  cases decide (j < w) <;> simp

theorem digit_mark_mul (w n mask v q : Nat) (sv : v < 2 ^ w) (hq : q < n) :
    digit w (v * mark w n mask) q = if mask.testBit q then v else 0 := by
  induction n generalizing mask q with
  | zero => omega
  | succ n ih =>
    have eq : v * mark w (n + 1) mask = (if mask.testBit 0 then v else 0) + 2 ^ w * (v * mark w n (mask >>> 1)) := by
      rw [mark, Nat.mul_add, Nat.mul_left_comm v (2 ^ w)]
      cases mask.testBit 0 <;> simp
    have low : (if mask.testBit 0 then v else 0) < 2 ^ w := by split <;> first | exact sv | exact Nat.two_pow_pos _
    rw [eq]
    cases q with
    | zero => exact digit_zero _ _ _ low
    | succ q => rw [digit_succ _ _ _ _ low, ih _ _ (by omega), Nat.testBit_shiftRight, Nat.one_add]

theorem digit_single (w v i q : Nat) (sv : v < 2 ^ w) :
    digit w (v <<< (w * i)) q = if q = i then v else 0 := by
  induction i generalizing q with
  | zero =>
    simp only [Nat.mul_zero, Nat.shiftLeft_zero]
    cases q with
    | zero => simp [digit, Nat.mod_eq_of_lt sv]
    | succ q => simpa [digit] using digit_succ w v 0 q sv
  | succ i ih =>
    have e : v <<< (w * (i + 1)) = 0 + 2 ^ w * (v <<< (w * i)) := by
      rw [Nat.mul_succ, Nat.shiftLeft_eq, Nat.pow_add, Nat.shiftLeft_eq, Nat.zero_add]; ac_rfl
    rw [e]
    cases q with
    | zero => simpa using digit_zero w 0 _ (Nat.two_pow_pos w)
    | succ q => simpa only [Nat.succ.injEq, ih] using digit_succ w 0 (v <<< (w * i)) q (Nat.two_pow_pos w)

theorem digit_units (w n start q : Nat) (bound : start + n ≤ w) (hq : q < n) :
    digit w (unitDigits w n start) q = 2 ^ (start + q) := by
  induction n generalizing start q with
  | zero => omega
  | succ n ih =>
    have low : 2 ^ start < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [unitDigits]
    cases q with
    | zero => simpa using digit_zero w (2 ^ start) _ low
    | succ q => rw [digit_succ _ _ _ _ low, ih _ _ (by omega) (by omega), show start + 1 + q = start + (q + 1) by omega]

def Matches (x : Nat) (r : Rows) : Prop := ∀ q < r.size, Matrix20.read r q = digit width x q

theorem matches_step (n : Nat) (x : Nat) (r : Rows) (v : (Nat × Nat) × Nat) (size : r.size = n)
    (hi : v.2 < n) (agree : Matches x r) : Matches (step n x v) (pivotBack n r v) := by
  let i := v.2
  let mask := v.1.2
  let y := x ^^^ (digit width x i * mark width n mask)
  have mid : Matches y (sweep r i mask) := by
    intro q hq
    have sq : q < r.size := by simpa only [sweep_size] using hq
    have si : i < r.size := size ▸ hi
    change Matrix20.read (sweep r i mask) q = digit width (x ^^^ (digit width x i * mark width n mask)) q
    rw [digit_xor, digit_mark_mul _ _ _ _ _ (digit_bound ..) (size ▸ sq)]
    have readRow : Matrix20.read (sweep r i mask) q =
        if mask.testBit q then Matrix20.read r q ^^^ Matrix20.read r i else Matrix20.read r q := by
      simp [sweep, Matrix20.read, sq]
    rw [readRow, agree q sq, agree i si]
    cases mask.testBit q <;> simp
  change Matches (if v.1.1 < n then y ^^^ (digit width y v.1.1 <<< (width * i)) else y)
    (if v.1.1 < n then applyPair (sweep r i mask) (v.1.1, i) else sweep r i mask)
  split
  · rename_i inside
    intro q hq
    have sz : (sweep r i mask).size = n := (sweep_size ..).trans size
    have sq : q < (sweep r i mask).size := by simpa only [applyPair_size] using hq
    rw [apply_read _ _ _ _ (sz ▸ hi), digit_xor, digit_single _ _ _ _ (digit_bound ..),
      mid q sq, mid i (sz ▸ hi), mid v.1.1 (sz ▸ inside)]
    by_cases hit : q = i <;> simp [hit]
  · exact mid

theorem encoding20_matches (n : Nat) (hn : UsedWidth20 n) (bound : n ≤ width) :
    Matches (encoding20 n) (fastBasis20 n) := by
  have fold (xs : List ((Nat × Nat) × Nat)) (x : Nat) (r : Rows) (size : r.size = n)
      (agree : Matches x r) (good : ∀ v ∈ xs, v.2 < n) :
      Matches (xs.foldl (step n) x) (xs.foldl (pivotBack n) r) := by
    induction xs generalizing x r with
    | nil => exact agree
    | cons v xs ih =>
      exact ih (step n x v) (pivotBack n r v) ((pivotBack_size ..).trans size)
        (matches_step n x r v size (good _ (List.mem_cons_self ..)) agree)
        (fun a ha => good a (List.mem_cons_of_mem _ ha))
  apply fold _ _ _ (by simp [units])
  · intro q hq
    have sq : q < n := by simpa [units] using hq
    simpa [units, Matrix20.read, sq, identityWord] using (digit_units width n 0 q (by simpa using bound) sq).symm
  · intro v hv
    obtain ⟨⟨donor, mask⟩, i⟩ := v
    exact (of_decide_eq_true (List.all_eq_true.mp (good_pivots20 n hn) _ (List.mem_reverse.mp hv))).1

def spreadFour (x : Nat) : Nat :=
  let pairs := (x ||| (x <<< (2 * (width - 1)))) &&& (3 ||| (3 <<< (2 * width)))
  (pairs ||| (pairs <<< (width - 1))) &&& (1 ||| (1 <<< width) ||| (1 <<< (2 * width)) ||| (1 <<< (3 * width)))

private theorem four_checked : ∀ a : Fin 16, spreadFour a.val = mark width 4 a.val := by decide +kernel

private theorem mark_congr (n a b : Nat) (eq : ∀ i < n, a.testBit i = b.testBit i) : mark width n a = mark width n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [mark, eq 0 (Nat.zero_lt_succ _)]
    rw [ih (a >>> 1) (b >>> 1) (fun i hi => by simp only [Nat.testBit_shiftRight]; exact eq _ (by omega))]

private theorem four (a : Nat) : mark width 4 a = spreadFour (a % 16) := by
  rw [four_checked ⟨a % 16, Nat.mod_lt _ (by decide)⟩]
  apply mark_congr
  intro i hi
  change a.testBit i = (a % 2 ^ 4).testBit i
  rw [Nat.testBit_mod_two_pow]; simp [hi]

private theorem mark_add (n m bits : Nat) :
    mark width (n + m) bits = mark width n bits + 2 ^ (width * n) * mark width m (bits >>> n) := by
  induction n generalizing bits with
  | zero => simp [mark]
  | succ n ih =>
    rw [Nat.succ_add, mark, ih, mark, ← Nat.shiftRight_add, Nat.one_add, Nat.mul_succ, Nat.pow_add]
    ring

def spreadChunks (r : Nat) : Nat → Nat → Nat
  | 0, a => mark width r a
  | c + 1, a => spreadFour (a % 16) + (spreadChunks r c (a >>> 4) <<< (4 * width))

private theorem spreadChunks_eq (r c bits : Nat) : mark width (4 * c + r) bits = spreadChunks r c bits := by
  induction c generalizing bits with
  | zero => simp [spreadChunks]
  | succ c ih =>
    rw [show 4 * (c + 1) + r = 4 + (4 * c + r) by omega, mark_add, four, ih, spreadChunks, Nat.shiftLeft_eq]
    simp [Nat.mul_comm]

def capture (w value i : Nat) : Nat := (value >>> (w * i)) &&& (2 ^ w - 1)

theorem capture_eq (w value i : Nat) : capture w value i = digit w value i := by
  simp only [capture, digit, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

def quickStep (n : Nat) (bits : Nat) (v : (Nat × Nat) × Nat) : Nat :=
  let i := v.2
  let marks := spreadChunks (n % 4) (n / 4) v.1.2
  let mid := bits ^^^ (capture width bits i * marks)
  if v.1.1 < n then mid ^^^ (capture width mid v.1.1 <<< (width * i)) else mid

private theorem quickStep_eq (n : Nat) : quickStep n = step n := by
  funext bits v
  unfold quickStep step
  simp only [capture_eq, ← spreadChunks_eq, Nat.div_add_mod]

def quickEncoding20 (n : Nat) : Nat := (pivots20 n).zipIdx.reverse.foldl (quickStep n) (identityWord width n)

theorem quickEncoding20_eq (n : Nat) : quickEncoding20 n = encoding20 n := by
  simp only [quickEncoding20, encoding20, quickStep_eq]

private theorem packed_id_83 : quickEncoding20 83 = basisWord20 83 := by decide +kernel
private theorem packed_id_93 : quickEncoding20 93 = basisWord20 93 := by decide +kernel
private theorem packed_id_103 : quickEncoding20 103 = basisWord20 103 := by decide +kernel
private theorem packed_id_112 : quickEncoding20 112 = basisWord20 112 := by decide +kernel
private theorem packed_id_122 : quickEncoding20 122 = basisWord20 122 := by decide +kernel

private theorem packed_identity20 (n : Nat) (hn : UsedWidth20 n) : encoding20 n = basisWord20 n := by
  rw [← quickEncoding20_eq]
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact packed_id_83
  · exact packed_id_93
  · exact packed_id_103
  · exact packed_id_112
  · exact packed_id_122

private theorem recorded20 (n : Nat) (hn : UsedWidth20 n) :
    n ≤ width ∧ (encoded20 n).size = n ∧ ∀ i : Fin n, Matrix20.read (encoded20 n) i.val = digit width (basisWord20 n) i.val := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem coordinates_checked20 (n : Nat) (hn : UsedWidth20 n) : CoordinatesOK20 n := by
  obtain ⟨bound, sz, data⟩ := recorded20 n hn
  have checks := encoding20_matches n hn bound
  rw [packed_identity20 n hn] at checks
  have fs : (fastBasis20 n).size = n := by rw [← fast_basis20_correct n hn, applyOps_size]; simp [units]
  unfold CoordinatesOK20
  rw [fast_basis20_correct n hn]
  apply Array.ext (fs.trans sz.symm)
  intro q hf he
  have equal := (checks q hf).trans (data ⟨q, fs ▸ hf⟩).symm
  simpa only [Matrix20.read, Array.getElem?_eq_getElem hf, Array.getElem?_eq_getElem he, Option.getD_some] using equal

/-! ## Fast scalar & packed word actions -/

def fastScalar20 (p : Nat) (mir : Bool) (slot : Nat) (data : Nat → Nat) (q : Nat) : Nat :=
  if 1 ≤ slot ∧ slot ≤ 21 then
    let d := fieldDegree p
    (selected d (rowMask20 p mir q >>> ((slot - 1) * d))).foldl (fun a j => a ^^^ data j) (data q)
  else data q

private theorem zeros (n a : Nat) : (List.replicate n 0).foldl Nat.xor a = a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldl_cons, show Nat.xor a 0 = a from Nat.xor_zero a, ih]

theorem scalar_fast20 (p : Nat) (mir : Bool) (slot : Nat) (data : Nat → Nat) (q : Nat) :
    scalarRow20 p mir (fun k => decide (slot = k + 1)) data q = fastScalar20 p mir slot data q := by
  let js := fun k => selected (fieldDegree p) (rowMask20 p mir q >>> (k * fieldDegree p))
  have all (ks : List Nat) (nd : ks.Nodup) (a : Nat) :
      (ks.flatMap (fun k => (js k).map fun j => if decide (slot = k + 1) then data j else 0)).foldl Nat.xor a =
      if 1 ≤ slot ∧ slot - 1 ∈ ks then (js (slot - 1)).foldl (fun v j => v ^^^ data j) a else a := by
    induction ks generalizing a with
    | nil => simp
    | cons k ks ih =>
      rw [List.flatMap_cons, List.foldl_append, ih (List.nodup_cons.mp nd).2]
      by_cases eq : slot = k + 1
      · subst slot; simp [List.nodup_cons.mp nd, List.foldl_map]; rfl
      · have no : 1 ≤ slot → slot - 1 ≠ k := by omega
        by_cases low : 1 ≤ slot <;> simp [eq, low, no, zeros]
  unfold scalarRow20 accumulate20 fastScalar20
  change _ = if 1 ≤ slot ∧ slot ≤ 21 then (js (slot - 1)).foldl _ (data q) else data q
  rw [all (List.range 21) List.nodup_range]
  simp only [List.mem_range]
  by_cases valid : 1 ≤ slot ∧ slot ≤ 21
  · rw [if_pos valid, if_pos (by omega)]
  · rw [if_neg valid, if_neg (by omega)]

def pack (w : Nat) : List Nat → Nat
  | [] => 0
  | a :: xs => a + 2 ^ w * pack w xs

def codedWord20 (n dim k : Nat) : Nat := pack width (coded20 n dim k).toList

def put (x q value : Nat) : Nat := x ^^^ ((digit width x q ^^^ value) <<< (width * q))

def replace (x : Nat) (indices : List Nat) (value : Nat → Nat) : Nat :=
  indices.foldl (fun acc q => put acc q (value q)) x

def scalarWord20 (x p : Nat) (mir : Bool) (slot off : Nat) : Nat :=
  let d := fieldDegree p
  let localData := fun j => digit width x (off + j)
  replace x ((List.range d).map (off + ·)) (fun q => fastScalar20 p mir slot localData (q - off))

def cxWord (x : Nat) (op : Wire × Wire) : Nat := x ^^^ (digit width x op.1 <<< (width * op.2))

def r8StepWord20 (n x slot off : Nat) (st : R8Step) : Nat :=
  if r8Enabled20 n slot st.tags then (r8Ops off st).foldl cxWord x else x

def primaryWord20 (n x off p m slot : Nat) (mir : Bool) : Nat :=
  let d := fieldDegree p
  let scalar := (List.range m).foldl (fun a j => scalarWord20 a p mir slot (off + d * j)) x
  if d == 8 && m == 2 then (pascalR8Steps20 mir).foldl (fun a st => r8StepWord20 n a slot off st) scalar
  else scalar

def componentWord20 (n : Nat) (mir : Bool) (slot : Nat) : Nat → List (Nat × Nat) → Nat → Nat
  | _, [], x => x
  | off, (p, m) :: ps, x => componentWord20 n mir slot (off + fieldDegree p * m) ps (primaryWord20 n x off p m slot mir)

def prototype20 : Nat → Rows
  | 11 => #[19891781826937379155528292012389348046057, 26751016939674406450538047878730502544698, 9945890913468689577764146006194674023028, 14335269661968236889415737841593606611112, 3583817415492059222353934460398401652778, 2778256082484571133056277085397870717472]
  | 13 => #[15776240759295162778522438492584655346873, 31552481518590325557044876985169310693746, 7888120379647581389261219246292327673436, 14303366242839227460136622698029229148328, 2945749032911870636771631589110852397090, 736437258227967659192907897277713099272]
  | 19 => #[40006995905761713665020287229952780727697, 10445392358955229623541529622652388974258, 20890784717910459247083059245304777948516, 41781569435820918494166118490609555897032]
  | 21 => #[6913673486647638622747928531947036677201, 13827346973295277245495857063894073354402, 23506489854601971317342957008619924702484, 3456836743323819311373964265973518338600]
  | 25 => #[9167965271024970566755654085954890144497, 18335930542049941133511308171909780288994, 36671861084099882267022616343819560577988, 26362054118452546945033801918610610605432]
  | 31 => #[23885626787740712790203327282952504133169, 25290663657607813542568228887832063199826, 28100737397342015047298032097591181333140, 33720884876810418056757638517109417599768, 723806872355779175460706887362197094944, 3406149987556607884520973587586809858562, 851537496889151971130243396896702464640, 11580909957692466807371310197795153519112]
  | 37 => #[27932194474876813705862654941247809506593, 12308245983873504088413360131229287946818, 8936042180094617128646825586564267571620, 17872084360189234257293651173128535143240, 35744168720378468514587302346257070286480]
  | 41 => #[36094934679621090185235730441252256902817, 28633726393362057047159511131238182739266, 13711309820843990771007072511210034412164, 19912769411375303377136920048129646992296, 39825538822750606754273840096259293984592]
  | 47 => #[30658970243285579744134829468376532194721, 37488565857482452575888569478124830015202, 2147662105671554075591347169113162475620, 29442814043761456597689682242727298581864, 15329485121642789872067414734188266097360]
  | 55 => #[26577339978445334316881955795361126411489, 27966559955322353983857018769224893216034, 36162927218825386740466089659602859951780, 28769711471770650157620229567939388837192, 35066741472162728820096952773313728738928]
  | 59 => #[29302661214131106759681126940329769575777, 41564138030242591077700874207736609271714, 39572133094605058832089798664206887477060, 21280070249030678600253205989750735084520, 14651330607065553379840563470164884787888]
  | 61 => #[12960823162984049230176067084423683502689, 25921646325968098460352134168847367005378, 21198763180058997619339976184866689137636, 30815457268108921413459970064887262578088, 6480411581492024615088033542211841751344]
  | 67 => #[5612898168739760699118325677947147851841, 16508956679978163768089428834160722520258, 33017913359956327536178857668321445040516, 22479683754032531749045765585376559014664, 1403224542184940174779581419486786962960, 2806449084369880349559162838973573925920]
  | 73 => #[5540409574916258348366490672861666378305, 11080819149832516696732981345723332756610, 22161638299665033393465962691446665513220, 6137069067599547708959805053015999680584, 12274138135199095417919610106031999361168, 24548276270398190835839220212063998722336]
  | 87 => #[27362919031636673446739759945993092909377, 38359814407180529648487051612759219067842, 16712370790895707898330997585915954495172, 33424741581791415796661995171831908990344, 6840729757909168361684939986498273227344, 13681459515818336723369879972996546454688]
  | 91 => #[27372219399588054867180962274776991481665, 38305291753722314268414382140296848687554, 33054440541564505213516814529327366308740, 6197333074470603536525635454041888143432, 39510162074307106209279202882143996170192, 35464181182734089095246456013021661274016]
  | 97 => #[38200792174768201734171875260307186560961, 32845441383656280145031800769348042055554, 22134739801432436966751651787429753044740, 713336636984750610191353823593175023112, 1426673273969501220382707647186350046224, 40878467570324162528741912505786758813664]
  | 103 => #[38258357778774199124717167290533158753217, 5681976867193784513574609413500699653186, 27577712907874688609168381682885250644804, 11599282849869253895024813614504170223240, 23198565699738507790049627229008340446480, 40907250372327161224014558520899744909792]
  | 109 => #[38238675932949108488738639650430836089281, 32921208900018093654165329549595341112194, 16718705178551462680998185954322089879236, 6162425061542662956099276761555451669576, 12324850123085325912198553523110903339152, 19119337966474554244369319825215418044640]
  | 115 => #[16494610391059644869125081907946136850113, 27408010022837731364564513908734468641602, 11259877079795339405817078066202606216836, 22519754159590678811634156132405212433672, 17741038247179463671969115915000199926992, 30025376678469884096218515829606233958240]
  | 117 => #[16443077378215551972977953031434699092673, 32886154756431103945955906062869398185346, 38489061122212814880900440187688792750532, 33421979278545506438488930624111254434696, 39554728637608372533982710439920260797904, 29999610172047837648144951391350515079520]
  | 257 => #[43556142965880123323311949751266331066367, 14518714321960041107770649917088777022122, 26133685779528073993987169850759798639820, 2903742864392008221554129983417755404424, 38431890852247167638216426251117350940912, 11102546246204737317706967583656123605152, 22034284088621709445910751050640614539456, 170808403787765189503184116671632670848, 338958311018522360492699998064329424640, 225972207345681573661799998709552949760, 271166648814817888394159998451463539712, 180777765876545258929439998967642359808, 319019586840962221640188233472310046720, 212679724560641481093458822314873364480, 255215669472769777312150586777848037376, 170143779648513184874767057851898691584]
  | _ => #[]

def prototypeWord20 (p m dim k : Nat) : Nat :=
  pack width (((prototype20 p).toList.take (fieldDegree p * m)).map (clipShift dim k))

def prototypeTest20 (p m slot : Nat) (mir : Bool) : Bool :=
  let dim := 135 - (slot - 1)
  primaryWord20 (fieldDegree p * m) (prototypeWord20 p m dim (entryShift mir slot)) 0 p m slot mir ==
    prototypeWord20 p m dim (exitShift mir slot)

def UsedPrimary20 (p m : Nat) : Prop :=
  p = 11 ∧ m = 1 ∨ p = 13 ∧ m = 1 ∨ p = 19 ∧ m = 1 ∨ p = 21 ∧ m = 1 ∨ p = 25 ∧ m = 1 ∨ p = 31 ∧ m = 1 ∨ p = 37 ∧ m = 1 ∨ p = 41 ∧ m = 1 ∨ p = 47 ∧ m = 1 ∨ p = 55 ∧ m = 1 ∨ p = 59 ∧ m = 1 ∨ p = 61 ∧ m = 1 ∨ p = 67 ∧ m = 1 ∨ p = 73 ∧ m = 1 ∨ p = 87 ∧ m = 1 ∨ p = 91 ∧ m = 1 ∨ p = 97 ∧ m = 1 ∨ p = 103 ∧ m = 1 ∨ p = 109 ∧ m = 1 ∨ p = 115 ∧ m = 1 ∨ p = 117 ∧ m = 1 ∨ p = 257 ∧ m = 1 ∨ p = 257 ∧ m = 2

set_option synthInstance.maxSize 1024 in
instance (p m : Nat) : Decidable (UsedPrimary20 p m) := by unfold UsedPrimary20; infer_instance

def tableOK20 (n : Nat) : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | off, (p, m) :: ps => decide (UsedPrimary20 p m) &&
      (List.range (fieldDegree p * m)).all (fun j =>
        Matrix20.read (encoded20 n) (off + j) == (Matrix20.read (prototype20 p) j &&& (2 ^ n - 1))) &&
      tableOK20 n (off + fieldDegree p * m) ps

private theorem pt20_11_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 11 1 s.val b = true := by decide +kernel
private theorem pt20_13_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 13 1 s.val b = true := by decide +kernel
private theorem pt20_19_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 19 1 s.val b = true := by decide +kernel
private theorem pt20_21_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 21 1 s.val b = true := by decide +kernel
private theorem pt20_25_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 25 1 s.val b = true := by decide +kernel
private theorem pt20_31_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 31 1 s.val b = true := by decide +kernel
private theorem pt20_37_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 37 1 s.val b = true := by decide +kernel
private theorem pt20_41_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 41 1 s.val b = true := by decide +kernel
private theorem pt20_47_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 47 1 s.val b = true := by decide +kernel
private theorem pt20_55_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 55 1 s.val b = true := by decide +kernel
private theorem pt20_59_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 59 1 s.val b = true := by decide +kernel
private theorem pt20_61_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 61 1 s.val b = true := by decide +kernel
private theorem pt20_67_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 67 1 s.val b = true := by decide +kernel
private theorem pt20_73_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 73 1 s.val b = true := by decide +kernel
private theorem pt20_87_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 87 1 s.val b = true := by decide +kernel
private theorem pt20_91_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 91 1 s.val b = true := by decide +kernel
private theorem pt20_97_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 97 1 s.val b = true := by decide +kernel
private theorem pt20_103_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 103 1 s.val b = true := by decide +kernel
private theorem pt20_109_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 109 1 s.val b = true := by decide +kernel
private theorem pt20_115_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 115 1 s.val b = true := by decide +kernel
private theorem pt20_117_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 117 1 s.val b = true := by decide +kernel
private theorem pt20_257_1 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 257 1 s.val b = true := by decide +kernel
private theorem pt20_257_2 : ∀ s : Fin 22, ∀ b : Bool, prototypeTest20 257 2 s.val b = true := by decide +kernel

theorem prototype_checked20 (p m : Nat) (hm : UsedPrimary20 p m) (slot : Fin 22) (mir : Bool) :
    prototypeTest20 p m slot.val mir = true := by
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact pt20_11_1 slot mir
  · exact pt20_13_1 slot mir
  · exact pt20_19_1 slot mir
  · exact pt20_21_1 slot mir
  · exact pt20_25_1 slot mir
  · exact pt20_31_1 slot mir
  · exact pt20_37_1 slot mir
  · exact pt20_41_1 slot mir
  · exact pt20_47_1 slot mir
  · exact pt20_55_1 slot mir
  · exact pt20_59_1 slot mir
  · exact pt20_61_1 slot mir
  · exact pt20_67_1 slot mir
  · exact pt20_73_1 slot mir
  · exact pt20_87_1 slot mir
  · exact pt20_91_1 slot mir
  · exact pt20_97_1 slot mir
  · exact pt20_103_1 slot mir
  · exact pt20_109_1 slot mir
  · exact pt20_115_1 slot mir
  · exact pt20_117_1 slot mir
  · exact pt20_257_1 slot mir
  · exact pt20_257_2 slot mir

theorem prototype_size20 (p m : Nat) (hm : UsedPrimary20 p m) : fieldDegree p * m ≤ (prototype20 p).size := by
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide


theorem table_checked20 (n : Nat) (hn : UsedWidth20 n) : 20 ≤ n ∧ n ≤ 135 ∧ tableOK20 n 0 (schedule20 n) = true := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem digit_pack (xs : List Nat) (q : Nat) (hq : q < xs.length)
    (bound : ∀ v ∈ xs, v < 2 ^ width) : digit width (pack width xs) q = (xs[q]?).getD 0 := by
  induction xs generalizing q with
  | nil => simp at hq
  | cons a xs ih =>
    rw [pack]
    have low := bound a (List.mem_cons_self ..)
    cases q with
    | zero => exact digit_zero _ _ _ low
    | succ q => rw [digit_succ _ _ _ _ low]; exact ih _ (by simpa using hq) (fun v hv => bound v (List.mem_cons_of_mem _ hv))

theorem coded20_matches (n dim k : Nat) (hd : dim ≤ width) : Matches (codedWord20 n dim k) (coded20 n dim k) := by
  have bound : ∀ v ∈ (coded20 n dim k).toList, v < 2 ^ width := by
    intro v hv
    simp only [coded20, Array.toList_map, List.mem_map] at hv
    obtain ⟨a, _, rfl⟩ := hv
    exact lt_of_le_of_lt Nat.and_le_right (lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by decide : 0 < 1))
      (Nat.pow_le_pow_right (by decide) hd))
  intro q hq
  simpa only [codedWord20, Matrix20.read, Array.getElem?_toList] using
    (digit_pack (coded20 n dim k).toList q (by simpa using hq) bound).symm

theorem digit_put (x i q v : Nat) (hv : v < 2 ^ width) : digit width (put x i v) q =
    if q = i then v else digit width x q := by
  rw [put, digit_xor, digit_single _ _ _ _ (Nat.xor_lt_two_pow (digit_bound ..) hv)]
  by_cases e : q = i <;> simp [e]

private theorem digit_replace (x q : Nat) (xs : List Nat) (v : Nat → Nat) (bound : ∀ j ∈ xs, v j < 2 ^ width) :
    digit width (replace x xs v) q = if q ∈ xs then v q else digit width x q := by
  induction xs generalizing x with
  | nil => simp [replace]
  | cons a xs ih =>
    change digit width (replace (put x a (v a)) xs v) q = _
    rw [ih _ (fun j hj => bound j (List.mem_cons_of_mem _ hj)), digit_put _ _ _ _ (bound a (List.mem_cons_self ..))]
    by_cases ha : q = a <;> by_cases hx : q ∈ xs <;> simp [ha, hx]

private theorem fast_bound20 (p : Nat) (mir : Bool) (slot : Nat) (v : Nat → Nat) (q : Nat)
    (h : ∀ j, v j < 2 ^ width) : fastScalar20 p mir slot v q < 2 ^ width := by
  have fold (xs : List Nat) (a : Nat) (ha : a < 2 ^ width) : xs.foldl (fun w j => w ^^^ v j) a < 2 ^ width := by
    induction xs generalizing a with
    | nil => exact ha
    | cons j xs ih => exact ih _ (Nat.xor_lt_two_pow ha (h j))
  unfold fastScalar20
  split
  · exact fold _ _ (h q)
  · exact h q

theorem digit_scalar20 (p : Nat) (mir : Bool) (slot off x q : Nat) :
    digit width (scalarWord20 x p mir slot off) q = if off ≤ q ∧ q < off + fieldDegree p then
      fastScalar20 p mir slot (fun j => digit width x (off + j)) (q - off) else digit width x q := by
  unfold scalarWord20
  rw [digit_replace _ _ _ _ (fun j _ => fast_bound20 _ _ _ _ _ (fun _ => digit_bound ..))]
  have within : q ∈ (List.range (fieldDegree p)).map (off + ·) ↔ off ≤ q ∧ q < off + fieldDegree p := by
    constructor
    · rintro hit; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hit
      exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (List.mem_range.mp hj) _⟩
    · rintro ⟨lo, hi⟩
      exact List.mem_map.mpr ⟨q - off, List.mem_range.mpr ((Nat.sub_lt_iff_lt_add lo).mpr (Nat.add_comm off _ ▸ hi)), Nat.add_sub_of_le lo⟩
  simp only [within]

theorem digit_cx (x a b q : Nat) : digit width (cxWord x (a, b)) q =
    if q = b then digit width x q ^^^ digit width x a else digit width x q := by
  rw [cxWord, digit_xor, digit_single _ _ _ _ (digit_bound ..)]
  by_cases eq : q = b <;> simp [eq]

private theorem scalar20_matches (p : Nat) (mir : Bool) (slot off x : Nat) (r : Rows)
    (endp : off + fieldDegree p ≤ r.size) (h : Matches x r) :
    Matches (scalarWord20 x p mir slot off) (scalarRows20 r p mir slot off) := by
  intro q hq
  have sq : q < r.size := by simpa only [scalarRows20_size] using hq
  let d := fieldDegree p
  let data := fun j => digit width x (off + j)
  rw [scalar20_read sq, digit_scalar20]
  split
  · rename_i live
    have jBound : q - off < d := (Nat.sub_lt_iff_lt_add live.1).mpr (Nat.add_comm off d ▸ live.2)
    change scalarRow20 p mir _ _ _ = fastScalar20 p mir slot data (q - off)
    rw [← scalar_fast20]
    apply accumulate20_congr
    · exact h _ (lt_of_lt_of_le (Nat.add_lt_add_left jBound _) endp)
    · intro k j hj; dsimp only
      rw [show Matrix20.read r (off + j) = data j from h _ (lt_of_lt_of_le (Nat.add_lt_add_left hj _) endp)]
  · exact h q sq

private theorem cx_matches (x : Nat) (r : Rows) (p : Wire × Wire) (ha : p.1 < r.size) (hb : p.2 < r.size)
    (h : Matches x r) : Matches (cxWord x p) (applyPair r p) := by
  obtain ⟨a, b⟩ := p
  intro q hq
  have sq : q < r.size := by simpa only [applyPair_size] using hq
  rw [apply_read _ _ _ _ hb, cxWord, digit_xor, digit_single _ _ _ _ (digit_bound ..)]
  by_cases eq : q = b <;> simp [eq, h q sq, h a ha, h b hb]

private theorem fold_matches {α} (xs : List α) (f : Nat → α → Nat) (g : Rows → α → Rows) (n x : Nat) (r : Rows)
    (size : r.size = n) (h : Matches x r) (keep : ∀ r a, (g r a).size = r.size)
    (step : ∀ a ∈ xs, ∀ x r, r.size = n → Matches x r → Matches (f x a) (g r a)) :
    Matches (xs.foldl f x) (xs.foldl g r) := by
  induction xs generalizing x r with
  | nil => exact h
  | cons a xs ih =>
    exact ih _ _ ((keep r a).trans size) (step a (List.mem_cons_self ..) x r size h)
      (fun b hb => step b (List.mem_cons_of_mem _ hb))

private theorem r8Step20_matches (n x slot off : Nat) (st : R8Step) (hg : r8Step20Good' st = true)
    (r : Rows) (size : r.size = n) (endp : off + 16 ≤ n) (agree : Matches x r) :
    Matches (r8StepWord20 n x slot off st) (r8StepRows20 r slot off st) := by
  unfold r8StepWord20 r8StepRows20
  rw [size]
  split
  · apply fold_matches _ _ applyPair n _ _ size agree (fun _ _ => applyPair_size ..)
    intro p hp z a sz matcha
    obtain ⟨ha, hb, _⟩ := r8Ops_bounds20 a off st hg (sz ▸ endp) p hp
    exact cx_matches z a p ha hb matcha
  · exact agree

private theorem primary20_matches (n x off p m slot : Nat) (mir : Bool) (r : Rows) (size : r.size = n)
    (endp : off + fieldDegree p * m ≤ n) (agree : Matches x r) :
    Matches (primaryWord20 n x off p m slot mir) (primaryRows20 r off p m slot mir) := by
  let d := fieldDegree p
  have scalar := fold_matches (List.range m) (fun a j => scalarWord20 a p mir slot (off + d * j))
    (fun a j => scalarRows20 a p mir slot (off + d * j)) n _ _ size agree (fun _ _ => scalarRows20_size ..) (by
      intro j hj z a sz matcha
      have kj := Nat.mul_le_mul_left (fieldDegree p) (show j + 1 ≤ m from List.mem_range.mp hj)
      rw [Nat.mul_succ] at kj
      exact scalar20_matches p mir slot _ _ a (by dsimp [d]; rw [sz]; omega) matcha)
  unfold primaryWord20 primaryRows20; dsimp only
  by_cases h82 : (fieldDegree p == 8 && m == 2) = true
  · have h82' := h82; simp only [Bool.and_eq_true, beq_iff_eq] at h82'
    have h16 : fieldDegree p * m = 16 := by rw [h82'.1, h82'.2]
    rw [if_pos h82, if_pos h82]
    unfold r8Rows20
    apply fold_matches (pascalR8Steps20 mir) (fun a st => r8StepWord20 n a slot off st)
      (fun a st => r8StepRows20 a slot off st) n _ (scalars20 r p m off slot mir) ((scalars20_size ..).trans size) scalar
      (fun _ _ => r8StepRows20_size ..)
    exact fun st hst z a sz ma => r8Step20_matches n z slot off st (List.all_eq_true.mp (pascalR8Steps20_good' mir) st hst) a sz (by omega) ma
  · rw [if_neg h82, if_neg h82]; exact scalar

private theorem components20_match (n x off slot : Nat) (mir : Bool) (ps : List (Nat × Nat)) (r : Rows)
    (size : r.size = n) (endp : off + extent20 ps ≤ n) (agree : Matches x r) :
    Matches (componentWord20 n mir slot off ps x) (componentRows20 mir slot off ps r) := by
  induction ps generalizing x r off with
  | nil => exact agree
  | cons pair tail ih =>
    obtain ⟨p, m⟩ := pair
    change off + (fieldDegree p * m + extent20 tail) ≤ n at endp
    exact ih _ _ _ ((primaryRows20_size ..).trans size) (by omega)
      (primary20_matches n x off p m slot mir r size (by omega) agree)

theorem action_of_digits20 (n slot : Nat) (hn : UsedWidth20 n) (bound : n ≤ width) (mir : Bool)
    (tested : ∀ q < n, digit width (componentWord20 n mir slot 0 (schedule20 n) (codedWord20 n (n - (slot - 1)) (entryShift mir slot))) q =
      digit width (codedWord20 n (n - (slot - 1)) (exitShift mir slot)) q) : ActionOK20 n slot mir := by
  let dim := n - (slot - 1)
  have hdim : dim ≤ width := by omega
  have src (k : Nat) : (coded20 n dim k).size = n := by
    rw [← encode_of_receipt20 n dim k (coordinates_checked20 n hn), applyOps_size, plain20_size]
  let input := coded20 n dim (entryShift mir slot)
  let out := componentRows20 mir slot 0 (schedule20 n) input
  have exactRun : Matches (componentWord20 n mir slot 0 (schedule20 n) (codedWord20 n dim (entryShift mir slot))) out :=
    components20_match n _ 0 slot mir (schedule20 n) input (src _) (by rw [schedule20_extent' n hn]; omega)
      (coded20_matches n dim _ hdim)
  have outSize : out.size = n := (componentRows20_size ..).trans (src _)
  change out = coded20 n dim (exitShift mir slot)
  apply Array.ext (outSize.trans (src _).symm)
  intro q ho he
  have result := (exactRun q ho).trans ((tested q (outSize ▸ ho)).trans (coded20_matches n dim _ hdim q he).symm)
  simpa only [Matrix20.read, Array.getElem?_eq_getElem ho, Array.getElem?_eq_getElem he, Option.getD_some] using result

structure Slice (f : Nat → Nat) (off len original bank block : Nat) : Prop where
  same : ∀ i < len, digit width bank (off + i) = f (digit width block i)
  exterior : ∀ q, (q < off ∨ off + len ≤ q) → digit width bank q = digit width original q

private theorem scalar20_linear (p : Nat) (mir : Bool) (slot i : Nat) (hi : i < fieldDegree p) (f : Nat → Nat)
    (fz : f 0 = 0) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (u v : Nat → Nat)
    (rel : ∀ j < fieldDegree p, u j = f (v j)) :
    fastScalar20 p mir slot u i = f (fastScalar20 p mir slot v i) := by
  rw [← scalar_fast20, ← scalar_fast20]
  unfold scalarRow20
  rw [map_accumulate20 p mir i f Nat.xor Nat.xor fx]
  apply accumulate20_congr
  · exact rel i hi
  · intro k j hj
    by_cases hot : slot = k + 1
    · simpa [hot] using rel j hj
    · simpa [hot] using fz.symm

theorem slice_scalar20 (p : Nat) (mir : Bool) (slot off len j original bank block : Nat) (f : Nat → Nat)
    (fz : f 0 = 0) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (endp : j + fieldDegree p ≤ len)
    (h : Slice f off len original bank block) :
    Slice f off len original (scalarWord20 bank p mir slot (off + j)) (scalarWord20 block p mir slot j) := by
  constructor
  · intro t ht
    rw [digit_scalar20, digit_scalar20]
    by_cases inside : j ≤ t ∧ t < j + fieldDegree p
    · have outer : off + j ≤ off + t ∧ off + t < off + j + fieldDegree p := by omega
      rw [if_pos outer, if_pos inside, show off + t - (off + j) = t - j by omega]
      apply scalar20_linear _ _ _ _ ((Nat.sub_lt_iff_lt_add inside.1).mpr (Nat.add_comm j _ ▸ inside.2)) f fz fx
      intro z hz; rw [Nat.add_assoc]; exact h.same _ (by omega)
    · rw [if_neg inside, if_neg (show ¬(off + j ≤ off + t ∧ off + t < off + j + fieldDegree p) by omega)]
      exact h.same t ht
  · intro q exterior
    rw [digit_scalar20, if_neg (by omega)]
    exact h.exterior q exterior

private theorem slice_cx (f : Nat → Nat) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (off len original bank block a b : Nat) (ha : a < len) (hb : b < len)
    (h : Slice f off len original bank block) :
    Slice f off len original (cxWord bank (off + a, off + b)) (cxWord block (a, b)) := by
  constructor
  · intro q hq
    rw [digit_cx, digit_cx]
    by_cases eq : q = b <;> simp [eq, h.same _ hq, h.same a ha, h.same b hb, fx]
  · intro q external
    rw [digit_cx, if_neg (by omega)]
    exact h.exterior q external

private theorem parity_map20 (xs : List Nat) (n s : Nat) :
    xorAt (flags20 n s) (xs.map (n + ·)) = xorAt (fun k => decide (k < 21 ∧ s = k + 1)) xs := by
  induction xs with
  | nil => rfl
  | cons k xs ih => simp [xorAt, ih, flags20]

theorem r8Enabled20_same (n m slot : Nat) (tags : List Nat) : r8Enabled20 n slot tags = r8Enabled20 m slot tags := by
  simp only [r8Enabled20, parity_map20]

private theorem shift_r8Ops (off : Nat) (st : R8Step) :
    r8Ops off st = (r8Ops 0 st).map (fun (a, b) => (off + a, off + b)) := by
  simp [r8Ops, List.map_append, List.map_reverse]

private theorem slice_r8Step20 (f : Nat → Nat) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (n off original bank block slot : Nat) (st : R8Step) (hg : r8Step20Good' st = true)
    (prev : Slice f off 16 original bank block) :
    Slice f off 16 original (r8StepWord20 n bank slot off st) (r8StepWord20 16 block slot 0 st) := by
  unfold r8StepWord20
  rw [r8Enabled20_same n 16]
  split
  · have bounds : ∀ p ∈ r8Ops 0 st, p.1 < 16 ∧ p.2 < 16 := by
      intro p hp
      obtain ⟨h1, h2, _⟩ := r8Ops_bounds20 (units 16) 0 st hg (by simp [units]) p hp
      simpa [units] using And.intro h1 h2
    rw [shift_r8Ops, List.foldl_map]
    have run (xs : List (Nat × Nat)) (z t : Nat) (hz : Slice f off 16 original z t)
        (loc : ∀ e ∈ xs, e.1 < 16 ∧ e.2 < 16) :
        Slice f off 16 original (xs.foldl (fun acc e => cxWord acc (off + e.1, off + e.2)) z) (xs.foldl cxWord t) := by
      induction xs generalizing z t with
      | nil => exact hz
      | cons e xs ih =>
        obtain ⟨a, b⟩ := e
        obtain ⟨ha, hb⟩ := loc (a, b) (List.mem_cons_self ..)
        exact ih _ _ (slice_cx f fx off 16 original z t a b ha hb hz)
          (fun w hw => loc w (List.mem_cons_of_mem _ hw))
    exact run (r8Ops 0 st) bank block prev bounds
  · exact prev

theorem primary20_slice (f : Nat → Nat) (fz : f 0 = 0) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (n off p m slot original bank block : Nat) (mir : Bool) (prev : Slice f off (fieldDegree p * m) original bank block) :
    Slice f off (fieldDegree p * m) original (primaryWord20 n bank off p m slot mir)
      (primaryWord20 (fieldDegree p * m) block 0 p m slot mir) := by
  let d := fieldDegree p
  have fold {α} (xs : List α) (g u : Nat → α → Nat) (b l : Nat) (rel : Slice f off (d * m) original b l)
      (one : ∀ a ∈ xs, ∀ b l, Slice f off (d * m) original b l → Slice f off (d * m) original (g b a) (u l a)) :
      Slice f off (d * m) original (xs.foldl g b) (xs.foldl u l) := by
    induction xs generalizing b l with
    | nil => exact rel
    | cons a xs ih => exact ih _ _ (one a (List.mem_cons_self ..) b l rel) (fun z hz => one z (List.mem_cons_of_mem _ hz))
  have sc : Slice f off (d * m) original
      ((List.range m).foldl (fun a j => scalarWord20 a p mir slot (off + d * j)) bank)
      ((List.range m).foldl (fun a j => scalarWord20 a p mir slot (0 + d * j)) block) := by
    apply fold _ _ _ _ _ prev
    intro j hj b l carry
    have h := Nat.mul_le_mul_left d (show j + 1 ≤ m from List.mem_range.mp hj)
    rw [Nat.mul_succ] at h
    simpa only [Nat.zero_add] using slice_scalar20 p mir slot off (d * m) (d * j) original b l f fz fx h carry
  unfold primaryWord20; dsimp only
  by_cases h82 : (fieldDegree p == 8 && m == 2) = true
  · have h82' := h82; simp only [Bool.and_eq_true, beq_iff_eq] at h82'
    have h16 : d * m = 16 := by change fieldDegree p * m = 16; rw [h82'.1, h82'.2]
    rw [if_pos h82, if_pos h82]
    apply fold (pascalR8Steps20 mir) (fun a st => r8StepWord20 n a slot off st)
      (fun a st => r8StepWord20 (d * m) a slot 0 st) _ _ sc
    intro st hst b l carry
    rw [h16] at carry ⊢
    exact slice_r8Step20 f fx n off original b l slot st (List.all_eq_true.mp (pascalR8Steps20_good' mir) st hst) carry
  · rw [if_neg h82, if_neg h82]; exact sc

private theorem prototype20_digit (p m dim k : Nat) (use : UsedPrimary20 p m) (hd : dim ≤ width) (q : Nat)
    (hq : q < fieldDegree p * m) :
    digit width (prototypeWord20 p m dim k) q = clipShift dim k (Matrix20.read (prototype20 p) q) := by
  let xs := ((prototype20 p).toList.take (fieldDegree p * m)).map (clipShift dim k)
  have bound : ∀ a ∈ xs, a < 2 ^ width := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact lt_of_le_of_lt Nat.and_le_right (lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by decide : 0 < 1))
      (Nat.pow_le_pow_right (by decide) hd))
  have len : xs.length = fieldDegree p * m := by simp [xs, Nat.min_eq_left (prototype_size20 p m use)]
  have h := digit_pack xs q (len ▸ hq) bound
  have inList : q < (prototype20 p).size := lt_of_lt_of_le hq (prototype_size20 p m use)
  simpa [xs, prototypeWord20, Matrix20.read, List.getElem?_map, List.getElem?_take, hq, inList] using h

private theorem clip_factor (n sh k v : Nat) (high : n ≤ 135) (hk : k ≤ sh) :
    clipShift (n - sh) k (v &&& (2 ^ n - 1)) = clipShift (n - sh) 0 (clipShift (135 - sh) k v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [clipShift, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, Nat.zero_add]
  by_cases h : i < n - sh
  · simp [h, show k + i < n by omega, show i < 135 - sh by omega]
  · simp [h]

private theorem shift_le_slot20 (mir : Bool) (slot : Fin 22) :
    entryShift mir slot.val ≤ slot.val - 1 ∧ exitShift mir slot.val ≤ slot.val - 1 := by
  cases mir <;> simp [entryShift, exitShift]

private theorem digits_source20 (n sh off p m k : Nat) (use : UsedPrimary20 p m) (high : n ≤ 135)
    (sk : k ≤ sh) (size : (coded20 n (n - sh) k).size = n) (endp : off + fieldDegree p * m ≤ n)
    (table : ∀ j < fieldDegree p * m, Matrix20.read (encoded20 n) (off + j) = (Matrix20.read (prototype20 p) j &&& (2 ^ n - 1))) :
    ∀ j < fieldDegree p * m, digit width (codedWord20 n (n - sh) k) (off + j) =
      clipShift (n - sh) 0 (digit width (prototypeWord20 p m (135 - sh) k) j) := by
  intro j hj
  have inner : off + j < n := by omega
  have sz : (encoded20 n).size = n := by simpa only [coded20, Array.size_map] using size
  have h := (coded20_matches n (n - sh) k (by unfold width; omega) (off + j) (by rwa [size])).symm
  rw [h, prototype20_digit p m (135 - sh) k use (by unfold width; omega) j hj]
  have readMap : Matrix20.read (coded20 n (n - sh) k) (off + j) = clipShift (n - sh) k (Matrix20.read (encoded20 n) (off + j)) := by
    simp [Matrix20.read, coded20, show off + j < (encoded20 n).size by rwa [sz]]
  rw [readMap, table j hj, clip_factor n sh k _ high sk]

theorem template_action20 (n : Nat) (hn : UsedWidth20 n) (slot : Fin 22) (mir : Bool) :
    ActionOK20 n slot.val mir := by
  obtain ⟨_low, high, checked⟩ := table_checked20 n hn
  let sh := slot.val - 1
  let dim := n - sh
  let pdim := 135 - sh
  let a := entryShift mir slot.val
  let b := exitShift mir slot.val
  let src := codedWord20 n dim a
  let dst := codedWord20 n dim b
  let crop := clipShift dim 0
  have sz (k : Nat) : (coded20 n dim k).size = n := by
    rw [← encode_of_receipt20 n dim k (coordinates_checked20 n hn), applyOps_size, plain20_size]
  have ks := shift_le_slot20 mir slot
  have sweep (ps : List (Nat × Nat)) (off bank : Nat) (endp : off + extent20 ps = n) (hc : tableOK20 n off ps = true)
      (inv : ∀ q < n, digit width bank q = if q < off then digit width dst q else digit width src q) :
      ∀ q < n, digit width (componentWord20 n mir slot.val off ps bank) q = digit width dst q := by
    induction ps generalizing off bank with
    | nil =>
      change off + 0 = n at endp
      intro q hq
      simpa [componentWord20, show q < off by omega] using inv q hq
    | cons pair tail ih =>
      obtain ⟨p, m⟩ := pair
      let len := fieldDegree p * m
      change off + (len + extent20 tail) = n at endp
      simp only [tableOK20, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
      obtain ⟨⟨use, rows⟩, rest⟩ := hc
      have proto := beq_iff_eq.mp (prototype_checked20 p m use slot mir)
      have startSlice : Slice crop off len bank bank (prototypeWord20 p m pdim a) := by
        constructor
        · intro j hj
          have eq := inv (off + j) (by omega)
          rw [if_neg (by omega)] at eq
          exact eq.trans (digits_source20 n sh off p m a use high ks.1 (sz a) (by omega) rows j hj)
        · intro q _; rfl
      have moved := primary20_slice crop (clip_zero dim 0) (clip_xor dim 0) n off p m slot.val bank bank
        (prototypeWord20 p m pdim a) mir startSlice
      apply ih (off + len) (primaryWord20 n bank off p m slot.val mir) (by omega) rest
      intro q hq
      by_cases low : q < off
      · rw [moved.exterior q (Or.inl low), inv q hq, if_pos low, if_pos (by omega)]
      · by_cases mid : q < off + len
        · have jlt : q - off < len := by omega
          have hqeq : off + (q - off) = q := by omega
          rw [← hqeq, moved.same (q - off) jlt, proto]
          rw [if_pos (by omega)]
          exact (digits_source20 n sh off p m b use high ks.2 (sz b) (by omega) rows (q - off) jlt).symm
        · rw [moved.exterior q (Or.inr (by omega)), inv q hq, if_neg low, if_neg mid]
  apply action_of_digits20 n slot.val hn (by unfold width; omega) mir
  exact sweep (schedule20 n) 0 src (by rw [Nat.zero_add, schedule20_extent' n hn]) checked (by intro q _; simp)

end Packed20

/-! ## Generic physical barrel theorem (decoupled from any caller layout) -/

theorem barrel20_result (n : Nat) (hn : UsedWidth20 n) (mir : Bool) (slot : Fin 22)
    (bank tagW scrW : Nat → Wire) (f : Wire → Wire)
    (hf_bank : ∀ i < n, f i = bank i)
    (hf_tag : ∀ k < 21, f (n + k) = tagW k)
    (hf_scr : ∀ k < 10, f (n + 21 + k) = scrW k)
    (hinj : ∀ a < n + 31, ∀ b < n + 31, f a = f b → a = b)
    (v : Nat) (s : State) (tape : List Bool)
    (small : v < 2 ^ (n - (slot.val - 1)))
    (input : ∀ i < n, s.basis (bank i) = (v <<< entryShift mir slot.val).testBit i)
    (tag : ∀ k < 21, s.basis (tagW k) = decide (slot.val = k + 1))
    (scratch : ∀ k < 10, s.basis (scrW k) = false) :
    let s' := run (renameProgram f (logical20 n mir)) tape s
    (∀ i < n, s'.basis (bank i) = (v <<< exitShift mir slot.val).testBit i) ∧
    s'.phase = s.phase ∧
    (∀ q, (∀ i < n, q ≠ bank i) → s'.basis q = s.basis q) := by
  let dim := n - (slot.val - 1)
  let P := logical20 n mir
  let S := Finset.range (n + 31)
  let before := entryShift mir slot.val
  let after := exitShift mir slot.val
  have scope : wires P ⊆ S := fun _ hw => Finset.mem_range.mpr (support (logical20_fits n hn mir) _ hw)
  have inj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b :=
    fun a ha b hb => hinj a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb)
  have bankBit (k i : Nat) (ik : i < n) :
      (frame20 (plain20 n dim k) v.testBit dim slot.val s.phase).basis i = (v <<< k).testBit i := by
    simpa only [frame20, Matrix20.basis, plain20_size, if_pos ik] using plain20_bits n dim k v i small ik
  have other (k q : Nat) (qn : n ≤ q) (high : q < n + 31) :
      (frame20 (plain20 n dim k) v.testBit dim slot.val s.phase).basis q = s.basis (f q) := by
    have outside : ¬q < n := Nat.not_lt.mpr qn
    simp only [frame20, Matrix20.basis, plain20_size, if_neg outside]
    by_cases mid : q < n + 21
    · have k21 : q - n < 21 := by omega
      have hfq : f q = tagW (q - n) := by
        simpa only [show n + (q - n) = q by omega] using hf_tag (q - n) k21
      rw [hfq, tag (q - n) k21]
      simp [flags20, qn, mid]
    · have pos : q - n - 21 < 10 := by omega
      have hfq : f q = scrW (q - n - 21) := by
        simpa only [show n + 21 + (q - n - 21) = q by omega] using hf_scr (q - n - 21) pos
      rw [hfq, scratch _ pos]
      simp [flags20, mid]
  have result := run_rename_pool f S inj P scope tape
    (frame20 (plain20 n dim before) v.testBit dim slot.val s.phase) s rfl (by
      intro q hq
      by_cases low : q < n
      · rw [bankBit before q low, hf_bank q low]; exact (input q low).symm
      · exact other before q (Nat.le_of_not_lt low) (Finset.mem_range.mp hq))
  have shift := logical20_action n hn mir slot.val (by have := slot.isLt; omega)
    (Packed20.coordinates_checked20 n hn) (Packed20.template_action20 n hn slot mir) v.testBit s.phase tape
  change run P tape (frame20 (plain20 n dim before) _ _ _ _) = frame20 (plain20 n dim after) _ _ _ _ at shift
  rw [shift] at result
  refine ⟨?_, result.1, ?_⟩
  · intro i bound
    have hi : i ∈ S := Finset.mem_range.mpr (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))
    have bit := (result.2 i hi).trans (bankBit after i bound)
    rwa [hf_bank i bound] at bit
  · intro q free
    by_cases hit : q ∈ S.image f
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hit
      have above : n ≤ a := by
        by_contra! low
        exact free a low (hf_bank a low)
      exact Eq.trans (result.2 a ha) (other after a above (Finset.mem_range.mp ha))
    · exact run_rename_pool_outside f S P scope tape s q hit

end ECDSAAdd.Entrant.StairPacket.CRTBarrel20

end
end
-- ==== end CRTBarrel20Proof ====

-- ==== begin Shadow7Wide20Core ====
section

/-!
20-tick shadow blocks (`s ∈ {165, 185, ..., 325}`, margin 22, cutoff `sbP20 s = (492 - s) / 2`):
- `IntegerPacket` routing, counts, physicality, domain coverage, and semantic roundtrip.
- 20-tick shadow envelope (`SmallIfFar`, `EndSmall20`), algebraic reduction, archive suffix row membership
  into the shared 63,145-row 10-tick archive table, and high-bank restoration laws.
- Physical wire geometry and `CRTBarrel20` instantiation for all 9 blocks.
-/

namespace ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.IntegerPacket
open ECDSAAdd.Entrant.StairPacket ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.GateMirror
open ECDSAAdd.Baselines ECDSAAdd.Challenge

set_option maxHeartbeats 2500000
set_option maxRecDepth 25000

/-! ### Section 1: 20-tick integer-packet blocks and routing -/

/-- Start tick of the `j`-th 20-tick block (`165, 185, ..., 325`). -/
def start20 (j : Fin 9) : Nat := 165 + 20 * j.val

/-- Narrowed shadow cutoff for a 20-tick block at start tick `s`. -/
def sbP20 (s : Nat) : Nat := (492 - s) / 2

def smallBits20 (j : Fin 9) : Nat := sbP20 (start20 j)

def shape20 (j : Fin 9) : IntegerPacket.Shape where
  start := start20 j
  length := 20
  mid := smallBits20 j + 21
  rangeEnd := by have h := j.isLt; simp [start20]; omega
  extent := by have h := j.isLt; simp [start20, smallBits20, sbP20]; omega
  midBound := by simp [smallBits20, sbP20, start20]; omega

def net20 (j : Fin 9) (a : Nat) : Wire → Wire := OB5.sig (start20 j + a)

def windowNet20 (j : Fin 9) : Wire → Wire := OB5.sig (start20 j + 19)

def mappedBasis20 (j : Fin 9) (s : BasisState) : BasisState := fun q => s (windowNet20 j q)

def routed20 (j : Fin 9) (a : Nat) : Nat → Program
  | 0 => []
  | n + 1 =>
    renameProgram (net20 j a) (skywalkIntegerTick (IntegerPacket.ports (shape20 j) a)) ++
      routed20 j (a + 1) n

def unrouted20 (j : Fin 9) (a : Nat) : Nat → Program
  | 0 => []
  | n + 1 =>
    unrouted20 j (a + 1) n ++
      renameProgram (net20 j a) (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
        (IntegerPacket.ports (shape20 j) a) (IntegerPacket.ports (shape20 j) a).half.length)

def onRails20 (j : Fin 9) (i : Nat) (z : SkywalkRails.State) (b : BasisState) : Prop :=
  ready (shape20 j) i z (mappedBasis20 j b)

def physicalCells20 (j : Fin 9) (s : State) : List (Bool × Bool) :=
  readCells (shape20 j) 0 20 (mappedBasis20 j s.basis)

theorem net20_injective (j : Fin 9) : Function.Injective (windowNet20 j) := by
  apply OB5.sig_injective
  have h := j.isLt
  simp only [start20]; omega

theorem net20_invol (j : Fin 9) (q : Wire) : windowNet20 j (windowNet20 j q) = q := by
  apply OB5.sig_invol
  have h := j.isLt
  simp only [start20]; omega

theorem stable20 {j : Fin 9} {a q : Nat} (ha : a < 20)
    (hq : q ∈ (IntegerPacket.ports (shape20 j) a).wires) : net20 j a q = windowNet20 j q := by
  have hj := j.isLt
  simp only [IntegerPacket.ports, shape20, smallBits20, sbP20, start20, SkywalkIntegerLayout.wires,
    SkywalkIntegerLayout.ah, SkywalkIntegerLayout.bh, List.mem_append, List.mem_cons,
    List.mem_range'_1, List.not_mem_nil, or_false] at hq
  unfold windowNet20 net20 OB5.sig start20
  split <;> split
  all_goals try rfl
  all_goals
    repeat' first | cases_type And | cases_type Or
    all_goals try simp only [Wire] at *
    all_goals omega

theorem fixed_route20 (j : Fin 9) (a n : Nat) (bound : a + n ≤ 20) :
    routed20 j a n = renameProgram (windowNet20 j) (IntegerPacket.seq (shape20 j) a n) ∧
    unrouted20 j a n = renameProgram (windowNet20 j) (IntegerPacket.backR (shape20 j) a n) := by
  induction n generalizing a with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have ha : a < 20 := by omega
    have h := skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (shape20 j) ⟨a, ha⟩)
    have hn : 0 < (IntegerPacket.ports (shape20 j) a).half.length := by simp [SkywalkIntegerLayout.half]
    have u := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_support (IntegerPacket.ports (shape20 j) a) _
      (IntegerPacket.ok (shape20 j) ⟨a, ha⟩) hn le_rfl
    obtain ⟨f, r⟩ := ih (a + 1) (by omega)
    have app (g : Wire → Wire) (P Q : Program) :
        renameProgram g (P ++ Q) = renameProgram g P ++ renameProgram g Q := List.map_append
    simp only [routed20, unrouted20, IntegerPacket.seq, IntegerPacket.backR, app, f, r]
    constructor
    · exact congrArg (fun P => P ++ _) (renameProgram_congr_support _ _ _ (fun q hq =>
        stable20 ha (List.mem_toFinset.mp (h.1 hq))))
    · exact congrArg (fun P => _ ++ P) (renameProgram_congr_support _ _ _ (fun q hq =>
        stable20 ha (List.mem_toFinset.mp (u hq))))

theorem routed20_counts (j : Fin 9) (a n : Nat) (bound : a + n ≤ 20) :
    toffoliCount (routed20 j a n) = n * (2 * (smallBits20 j + 22)) ∧
    measurementCount (routed20 j a n) = n * (smallBits20 j + 22) ∧
    toffoliCount (unrouted20 j a n) = n * (2 * (smallBits20 j + 22) - 1) ∧
    measurementCount (unrouted20 j a n) = n * (smallBits20 j + 22) := by
  obtain ⟨f, r⟩ := fixed_route20 j a n bound
  have hs := IntegerPacket.metrics (shape20 j) a n bound
  have hr := IntegerPacket.metricsR (shape20 j) a n bound
  have mid : (shape20 j).mid + 1 = smallBits20 j + 22 := rfl
  rw [mid] at hs hr
  rw [f, r, (renameProgram_counts _ _).1, (renameProgram_counts _ _).2,
    (renameProgram_counts _ _).1, (renameProgram_counts _ _).2]
  exact ⟨hs.1, hs.2.1, hr.1, hr.2⟩

private theorem integer_tick_phys (L : SkywalkIntegerLayout) (hv : L.Valid) :
    GatePhysical (skywalkIntegerTick L) := by
  have enough : 1 ≤ L.half.length := by simp [SkywalkIntegerLayout.half]
  have narrow := narrowTicks_physical L 1 hv (by decide) enough
  simp only [narrowSkywalkTick, gatePhysical_append] at narrow
  obtain ⟨⟨⟨⟨route, half⟩, _⟩, prev⟩, _⟩ := narrow
  have nd := L.record_nodup hv
  have fresh := (List.nodup_cons.mp nd).1
  have sx : L.ext ≠ L.history := fun e => fresh (e ▸ by simp [SkywalkIntegerLayout.half])
  have sy : L.bSign ≠ L.history := fun e => fresh (e ▸ by simp [SkywalkIntegerLayout.b, SkywalkIntegerLayout.bh])
  have toggle : GatePhysical (skywalkSignToggle L.ext L.bSign L.history) := by
    simp [skywalkSignToggle, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, sx, sy]
  have arithmetic := signedWords_physical L.history L.half L.b L.carry nd
  simp only [skywalkIntegerTick, signedRecord, gatePhysical_append]
  exact ⟨⟨⟨route, half⟩, ⟨⟨toggle, arithmetic.1⟩, toggle⟩⟩, prev⟩

theorem routed20_phys (j : Fin 9) (a n : Nat) (bound : a + n ≤ 20) :
    GatePhysical (routed20 j a n) ∧ GatePhysical (unrouted20 j a n) := by
  induction n generalizing a with
  | zero => simp [routed20, unrouted20, GatePhysical]
  | succ n ih =>
    have ha : a < 20 := by omega
    have valid := IntegerPacket.ok (shape20 j) ⟨a, ha⟩
    have tick := integer_tick_phys (IntegerPacket.ports (shape20 j) a) valid
    have hn : 0 < (IntegerPacket.ports (shape20 j) a).half.length := by simp [SkywalkIntegerLayout.half]
    have untick := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_physical (IntegerPacket.ports (shape20 j) a) _
      valid hn le_rfl
    have hj := j.isLt
    have inj := OB5.sig_injective (start20 j + a) (by simp only [start20]; omega)
    have tail := ih (a + 1) (by omega)
    exact ⟨(gatePhysical_append _ _).2 ⟨gatePhysical_rename _ inj _ tick, tail.1⟩,
      (gatePhysical_append _ _).2 ⟨tail.2, gatePhysical_rename _ inj _ untick⟩⟩

theorem ports20_dom {j : Fin 9} {a q : Nat} (ha : a < 20)
    (hq : q ∈ (IntegerPacket.ports (shape20 j) a).wires) : WindowCovered.domainW (net20 j a q) = true := by
  have hj := j.isLt
  simp only [IntegerPacket.ports, shape20, smallBits20, sbP20, start20, SkywalkIntegerLayout.wires,
    SkywalkIntegerLayout.ah, SkywalkIntegerLayout.bh, List.mem_append, List.mem_cons,
    List.mem_range'_1, List.not_mem_nil, or_false] at hq
  rw [WindowCovered.dom_iff]
  unfold net20 OB5.sig start20
  split
  all_goals
    repeat' first | cases_type And | cases_type Or
    all_goals try simp only [Wire] at *
    all_goals omega

theorem routed20_cov (j : Fin 9) (a n : Nat) (bound : a + n ≤ 20) :
    WindowCovered.CoveredW (routed20 j a n) ∧ WindowCovered.CoveredW (unrouted20 j a n) := by
  induction n generalizing a with
  | zero => constructor <;> intro q h <;> simp [routed20, unrouted20, wires] at h
  | succ n ih =>
    have ha : a < 20 := by omega
    have step := skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (shape20 j) ⟨a, ha⟩)
    have hn : 0 < (IntegerPacket.ports (shape20 j) a).half.length := by simp [SkywalkIntegerLayout.half]
    have ustep := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_support (IntegerPacket.ports (shape20 j) a) _
      (IntegerPacket.ok (shape20 j) ⟨a, ha⟩) hn le_rfl
    have sub := ih (a + 1) (by omega)
    have ok (P : Program) (hp : wires P ⊆ (IntegerPacket.ports (shape20 j) a).wires.toFinset) :
        WindowCovered.CoveredW (renameProgram (net20 j a) P) := by
      intro q hq
      rw [renameProgram_support] at hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      exact ports20_dom ha (List.mem_toFinset.mp (hp hx))
    exact ⟨WindowCovered.appW (ok _ step.1) sub.1, WindowCovered.appW sub.2 (ok _ ustep)⟩

theorem pull_routed20 (j : Fin 9) (i n : Nat) (bound : i + n ≤ 20) (m : List Bool) (s : State) :
    pullState (windowNet20 j) (run (routed20 j i n) m s) =
      run (IntegerPacket.seq (shape20 j) i n) m (pullState (windowNet20 j) s) := by
  rw [(fixed_route20 j i n bound).1, run_rename _ (net20_injective j)]

theorem route20_frame (j : Fin 9) (i n : Nat) (bound : i + n ≤ 20) (z : SkywalkRails.State)
    (odd : (z.a + z.b) % 2 = 1) :
    Triple (onRails20 j i z) (routed20 j i n) (onRails20 j (i + n) (SkywalkTrace.next^[n] z)) := by
  intro s m hready
  have h := IntegerPacket.semantic (shape20 j) i n bound z odd (pullState (windowNet20 j) s) m hready
  rw [← pull_routed20 j i n bound m s] at h
  exact h

theorem route20_records (j : Fin 9) (i n : Nat) (bound : i + n ≤ 20) (z : SkywalkRails.State)
    (odd : (z.a + z.b) % 2 = 1) (s : State) (m : List Bool) (h : onRails20 j i z s.basis) :
    readCells (shape20 j) i n (mappedBasis20 j (run (routed20 j i n) m s).basis) = SkywalkTrace.trace n z ∧
    ∀ d < i, cell (shape20 j) d (mappedBasis20 j (run (routed20 j i n) m s).basis) =
      cell (shape20 j) d (mappedBasis20 j s.basis) := by
  have hh := IntegerPacket.records (shape20 j) i n bound z odd (pullState (windowNet20 j) s) m h
  rw [← pull_routed20 j i n bound m s] at hh
  exact hh

theorem route20_undo (j : Fin 9) (i n : Nat) (bound : i + n ≤ 20) (z : SkywalkRails.State)
    (odd : (z.a + z.b) % 2 = 1) :
    Restores (onRails20 j i z) (routed20 j i n) (unrouted20 j i n) := by
  intro s m t hready
  have forward := pull_routed20 j i n bound m s
  let actual := run (routed20 j i n) m s
  have bk : pullState (windowNet20 j) (run (unrouted20 j i n) t actual) =
      run (IntegerPacket.backR (shape20 j) i n) t (pullState (windowNet20 j) actual) := by
    rw [(fixed_route20 j i n bound).2, run_rename _ (net20_injective j)]
  have fin := IntegerPacket.roundtripR (shape20 j) i n bound z odd (pullState (windowNet20 j) s) m t hready
  change pullState (windowNet20 j) actual = _ at forward
  rw [forward, fin] at bk
  apply congrArg₂ State.mk (congrArg State.phase bk)
  funext q
  have h := congrArg (fun x : State => x.basis (windowNet20 j q)) bk
  change (run (unrouted20 j i n) t actual).basis (windowNet20 j (windowNet20 j q)) =
    s.basis (windowNet20 j (windowNet20 j q)) at h
  rwa [net20_invol j q] at h

/-! ### Section 2: 20-tick shadow envelope, reduction, archive row & restoration laws -/

section ShadowMath
open SkywalkNat IntegerHigh Shadow HighBankSum
attribute [local irreducible] SkywalkNat.step

def EndSmall20 (b : Nat) (z : SkywalkNat.State) : Prop :=
  min (step^[20] z).u (step^[20] z).v < 2 ^ b

def Small20 (b : Nat) (z : SkywalkNat.State) : Prop :=
  Shadow7.SmallIfFar b 20 z ∧ EndSmall20 b z

theorem inputs20 (x p t : Nat) (hx : x < 2 ^ 256) (hp : p < 2 ^ 256) (ht : t ≤ 492) :
    Small20 (sbP20 t) (step^[t] (init x p)) := by
  have hb : sbP20 t = (492 - t) / 2 := rfl
  refine ⟨?_, ?_⟩
  · intro hfar
    have pos : 0 < limb (sbP20 t) 20 := by unfold limb; exact Nat.two_pow_pos _
    have hf := (Nat.le_div_iff_mul_le pos).mp hfar
    have he : limb (sbP20 t) 20 = 2 * 2 ^ (sbP20 t + 20) := by
      unfold limb
      rw [show sbP20 t + 20 + 1 = (sbP20 t + 20) + 1 by omega, pow_succ]; ring
    rw [he] at hf
    obtain ⟨a, c, hac, hu, hv⟩ := Shadow7.Envelope.budget x p hx hp t
    have hbig : 2 ^ (sbP20 t + 20) ≤ (step^[t] (init x p)).u ∨
        2 ^ (sbP20 t + 20) ≤ (step^[t] (init x p)).v := by omega
    rcases hbig with h | h
    · have ex : sbP20 t + 20 < 256 - a := (Nat.pow_lt_pow_iff_right (by decide)).mp (lt_of_le_of_lt h hu)
      exact lt_of_le_of_lt (min_le_right _ _)
        (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))
    · have ex : sbP20 t + 20 < 256 - c := (Nat.pow_lt_pow_iff_right (by decide)).mp (lt_of_le_of_lt h hv)
      exact lt_of_le_of_lt (min_le_left _ _)
        (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) (by omega)))
  · have h := Shadow7.Envelope.min_lt x p hx hp (20 + t)
    rw [Function.iterate_add_apply] at h
    have e : 256 - (20 + t + 1) / 2 ≤ sbP20 t := by omega
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) e)

theorem scale20 (b : Nat) : limb b 20 = 2 ^ 20 * 2 ^ (b + 1) := by
  rw [limb, show b + 20 + 1 = 20 + (b + 1) by omega, pow_add]

theorem guard_tight20 (b s : Nat) (hs : s < 2 ^ b) : guard 20 s + s ≤ limb b 20 := by
  have a : 2 * s + 1 ≤ 2 * 2 ^ b := by omega
  have mul := Nat.mul_le_mul_left (2 ^ 20) a
  have f := guard_formula 20 s
  have e : limb b 20 = 2 ^ 20 * (2 * 2 ^ b) := by
    rw [scale20, pow_succ 2 b, Nat.mul_comm (2 ^ b) 2]
  rw [f, e]
  exact mul

theorem rail20 (b : Nat) (z : SkywalkNat.State) (small : min z.u z.v < 2 ^ b) (hfar : far b 20 z) :
    let r := reduced b 20 z
    let D := 2 ^ (b + 1) * (high b 20 z - 1)
    (2 ^ b ≤ z.u → r.v = z.v ∧ z.u = r.u + 2 ^ 20 * D ∧ guard 20 r.v ≤ r.u) ∧
    (z.u < 2 ^ b → r.u = z.u ∧ z.v = r.v + 2 ^ 20 * D ∧ guard 20 r.u ≤ r.v) := by
  dsimp only
  have hr := (represented b 20 z small hfar).2.1
  have amount : gap b 20 z = 2 ^ 20 * (2 ^ (b + 1) * (high b 20 z - 1)) := by rw [gap, scale20]; ring
  have hbase : 2 ^ b ≤ limb b 20 := Nat.pow_le_pow_right (by decide) (by omega)
  constructor
  · intro h
    have sh : z.v < 2 ^ b := by omega
    rw [reduced, if_pos hfar, if_pos h] at hr ⊢
    dsimp only at hr ⊢
    exact ⟨rfl, by omega, by have t := guard_tight20 b z.v sh; omega⟩
  · intro h
    rw [reduced, if_pos hfar, if_neg (Nat.not_le.mpr h)] at hr ⊢
    dsimp only at hr ⊢
    exact ⟨rfl, by omega, by have t := guard_tight20 b z.u h; omega⟩

theorem shadow_odd20 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 20 z)
    (odd : z.v % 2 = 1) : (reduced b 20 z).v % 2 = 1 := by
  by_cases f : far b 20 z
  · have h := rail20 b z (small f) f
    by_cases hu : 2 ^ b ≤ z.u
    · rw [(h.1 hu).1]; exact odd
    · have hv := (h.2 (Nat.lt_of_not_ge hu)).2.1
      change z.v = (reduced b 20 z).v + 1048576 * _ at hv
      omega
  · simpa [reduced, f] using odd

theorem true_records20 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 20 z)
    (odd : z.v % 2 = 1) (G S : Bool) :
    let T := reduced b 20 z
    SkywalkTrace.trace 20 (SkywalkRails.encode G S T.u T.v) =
      SkywalkTrace.trace 20 (SkywalkRails.encode G S z.u z.v) := by
  by_cases f : far b 20 z
  · have h := (represented b 20 z (small f) f).1
    have o := shadow_odd20 b z small odd
    exact (IntegerHigh.trace_eq h G S G S (by omega) odd (by omega) o).symm
  · simp [reduced, f]

/-- Every 20-tick block's 10-tick suffix (`cells.drop 10`) plus its 3 shadow flags lands in the
exact same 63,145-row `ReducedWindowArchives` table. -/
theorem interrupted_row20 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 20 z)
    (odd : z.v % 2 = 1) (G S cross : Bool) (cells : List (Bool × Bool))
    (records : let T := reduced b 20 z
      cells = SkywalkTrace.trace 20 (SkywalkRails.encode G S T.u T.v)) :
    let hfar := decide (far b 20 z)
    let u := hfar && StairArchiveTrace.afterFlags (decide (z.v < z.u)) (cells.take 10)
    ∃ row < 63145, ∀ q < 23,
      (StairArchiveRaw.rawCol q).testBit row =
        StairArchiveRaw.rawBit (StairArchiveRaw.read (cells.drop 10)) hfar u (hfar && cross) q := by
  rw [records.trans (true_records20 b z small odd G S)]
  by_cases f : far b 20 z
  · simpa only [f, decide_true, Bool.true_and] using
      StairArchiveTrace.far_suffix 10 (represented b 20 z (small f) f).1 G S cross (by omega) odd
  · simpa only [f, decide_false, Bool.false_and] using
      StairArchiveTrace.near_suffix 10 z G S (by omega) odd

theorem far_result20 (b w : Nat) (z : SkywalkNat.State) (small : Small20 b z)
    (hfar : far b 20 z) (odd : z.v % 2 = 1) (enough : high b 20 z + 1 < 2 ^ w) :
    let r := reduced b 20 z
    let S := total (step^[20] r)
    let F := total (step^[20] z)
    let t := if 2 ^ b ≤ z.u then 0 else wait 20 z.u
    let d := S / 2 ^ (b + 1) / 2 ^ t
    let neg := cross17 d && (!(decide (2 ^ b ≤ z.u)) && negative (oddBits (letters 20 r)))
    d + 1 = (cross17 d).toNat + 2 * (!neg).toNat ∧
      F / 2 ^ (b + 1) = 2 ^ t * HighBankAdjust.adjusted (high b 20 z) w (cross17 d) neg +
        S / 2 ^ (b + 1) % 2 ^ t := by
  let r := reduced b 20 z
  let H := high b 20 z
  let V := 2 ^ (b + 1)
  let D := V * (H - 1)
  have hsm : min z.u z.v < 2 ^ b := small.1 hfar
  have sides := rail20 b z hsm hfar
  have bounds := (represented b 20 z hsm hfar).2
  rw [scale20] at bounds
  have hH : 2 ≤ H := hfar
  have pos : 2 ^ b < V := by dsimp [V]; rw [pow_succ]; have := Nat.two_pow_pos b; omega
  dsimp only
  by_cases h : 2 ^ b ≤ z.u
  · obtain ⟨eqV, eqU, guarded⟩ := sides.1 h
    have shape : z = ⟨r.u + 2 ^ 20 * D, r.v⟩ := SkywalkNat.State.ext eqU eqV.symm
    have short : r.v < V := by dsimp [r]; omega
    have rodd : r.v % 2 = 1 := eqV ▸ odd
    have dcap := left_digit17 20 r.u r.v V guarded rodd short bounds.1 bounds.2
    change total (step^[20] r) / V = 1 ∨ total (step^[20] r) / V = 2 at dcap
    have room : H - 1 + total (step^[20] r) / V < 2 ^ w := by change H + 1 < 2 ^ w at enough; omega
    have outcome := HighBankSum.left17 20 r.u r.v H w (b + 1) guarded rodd short bounds.1 bounds.2 hH room
    rw [← shape] at outcome
    simpa only [if_pos h, decide_eq_true h, Bool.not_true, Bool.false_and, Bool.and_false,
      Bool.not_false, Bool.toNat_true, Nat.mul_one, pow_zero, Nat.div_one, one_mul, Nat.mod_one,
      Nat.add_zero] using outcome
  · obtain ⟨eqU, eqV, guarded⟩ := sides.2 (Nat.lt_of_not_ge h)
    have shape : z = ⟨r.u, r.v + 2 ^ 20 * D⟩ := SkywalkNat.State.ext eqU.symm eqV
    have short : r.u < V := by dsimp [r]; omega
    have rodd : r.v % 2 = 1 := by change z.v = r.v + 1048576 * D at eqV; omega
    have dcap := (right_digit17 20 r.v r.u V guarded rodd short
      (by simpa only [Nat.add_comm r.v r.u] using bounds.1)
      (by simpa only [Nat.add_comm r.v r.u] using bounds.2)).1
    change total (step^[20] r) / (2 ^ (wait 20 r.u) * V) = 0 ∨
      total (step^[20] r) / (2 ^ (wait 20 r.u) * V) = 1 ∨
      total (step^[20] r) / (2 ^ (wait 20 r.u) * V) = 2 at dcap
    rw [Nat.mul_comm (2 ^ _) V, ← Nat.div_div_eq_div_mul] at dcap
    have room : H - 1 + total (step^[20] r) / V / 2 ^ (wait 20 r.u) < 2 ^ w := by
      change H + 1 < 2 ^ w at enough; omega
    have outcome := HighBankSum.right17 20 r.v r.u H w (b + 1) (by decide) guarded rodd short
      (by simpa only [Nat.add_comm r.v r.u] using bounds.1)
      (by simpa only [Nat.add_comm r.v r.u] using bounds.2) hH room
    rw [← shape] at outcome
    have waits : wait 20 z.u = wait 20 r.u := congrArg (wait 20) eqU.symm
    simpa only [if_neg h, decide_eq_false h, Bool.not_false, Bool.true_and, waits] using outcome

theorem near_result20 (b : Nat) (z : SkywalkNat.State) (close : ¬ far b 20 z) :
    reduced b 20 z = z ∧ total (step^[20] z) / 2 ^ (b + 1) < 2 ^ 22 := by
  refine ⟨by simp [reduced, close], ?_⟩
  have lt : (z.u + z.v) / limb b 20 < 2 := Nat.lt_of_not_ge close
  have lim := (Nat.div_lt_iff_lt_mul (by unfold limb; positivity)).mp lt
  rw [scale20] at lim
  have noninc := iter_sum_nonincrease 20 z
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
  dsimp only [total]
  omega

theorem inputTight22 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 20 z) :
    let a := step^[20] (reduced b 20 z)
    (a.u + a.v) / 2 ^ b < 2 ^ 22 := by
  let r := reduced b 20 z
  have upper : r.u + r.v < 2 * limb b 20 := by
    by_cases f : far b 20 z
    · exact (represented b 20 z (small f) f).2.2
    · have low : (z.u + z.v) / limb b 20 < 2 := Nat.lt_of_not_ge f
      simpa only [r, reduced, if_neg f] using (Nat.div_lt_iff_lt_mul (by unfold limb; positivity)).mp low
  dsimp only
  have noninc := iter_sum_nonincrease 20 r
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).mpr
  change (step^[20] r).u + (step^[20] r).v < _
  rw [scale20, pow_succ] at upper
  omega

theorem afterThreshold20 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 20 z)
    (e : Nat) (en : e ≤ 1) :
    let full := step^[20] z
    let r := step^[20] (reduced b 20 z)
    (2 ^ b ≤ full.u - e ↔ 2 ^ b ≤ r.u - e) ∧ (0 < full.u ↔ 0 < r.u) := by
  by_cases f : far b 20 z
  · have rep := represented b 20 z (small f) f
    have cap := rep.2.1
    rw [scale20, pow_succ 2 b] at cap
    have low := LeaveShadowRails.sumLower 20 (2 ^ b * 2) (reduced b 20 z) (by unfold total; omega)
    apply LeaveShadowRails.sameThreshold17 _ _ _ _ (LeaveShadowRails.terminalRel _ _ _ rep.1) en
    unfold total at low
    have h := Nat.two_pow_pos b
    omega
  · simp [reduced, f]

theorem limbGaps20 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 20 z) :
    let full := step^[20] z
    let r := step^[20] (reduced b 20 z)
    ∃ a c : Nat, full.u = r.u + 2 ^ (b + 1) * a ∧ full.v = r.v + 2 ^ (b + 1) * c := by
  by_cases f : far b 20 z
  · let r := reduced b 20 z
    let H := high b 20 z - 1
    let V := 2 ^ (b + 1)
    let D := V * H
    have side := rail20 b z (small f) f
    dsimp only
    by_cases long : 2 ^ b ≤ z.u
    · obtain ⟨rv, fullU, valid⟩ := side.1 long
      have shape : z = ⟨r.u + 2 ^ 20 * D, r.v⟩ := SkywalkNat.State.ext fullU rv.symm
      have result := long_u 20 r.u r.v D valid
      rw [← shape] at result
      rw [result]
      exact ⟨H, 0, rfl, by rw [Nat.mul_zero, Nat.add_zero]⟩
    · obtain ⟨ru, fullV, valid⟩ := side.2 (Nat.lt_of_not_ge long)
      have shape : z = ⟨r.u, r.v + 2 ^ 20 * D⟩ := SkywalkNat.State.ext ru.symm fullV
      have result := long_v 20 r.v r.u D valid
      rw [← shape] at result
      dsimp only at result
      let J := 2 ^ (wait 20 r.u) * H
      have shift : 2 ^ (wait 20 r.u) * D = V * J := by dsimp [D, J]; ring
      rw [shift] at result
      split at result
      · rw [result]; exact ⟨0, J, by rw [Nat.mul_zero, Nat.add_zero], rfl⟩
      · rw [result]; exact ⟨J, 0, rfl, by rw [Nat.mul_zero, Nat.add_zero]⟩
  · refine ⟨0, 0, ?_, ?_⟩ <;> simp [reduced, f]

theorem retainedLow20 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 20 z) (sg : Bool) :
    let F := step^[20] z
    let r := step^[20] (reduced b 20 z)
    let e := PortalValues.negative sg r.u
    let V := 2 ^ (b + 1)
    PortalValues.negative sg F.u = e ∧ (F.u + F.v) % V = (r.u + r.v) % V ∧
      (F.u - e.toNat) % V = (r.u - e.toNat) % V := by
  obtain ⟨a, c, hu, hv⟩ := limbGaps20 b z small
  have pos : 0 < (step^[20] z).u ↔ 0 < (step^[20] (reduced b 20 z)).u :=
    (afterThreshold20 b z small 0 (by decide)).2
  dsimp only at hu hv ⊢
  have negEq : PortalValues.negative sg (step^[20] z).u =
      PortalValues.negative sg (step^[20] (reduced b 20 z)).u := by
    unfold PortalValues.negative
    by_cases h : 0 < (step^[20] (reduced b 20 z)).u
    · rw [decide_eq_true h, decide_eq_true (pos.mpr h)]
    · rw [decide_eq_false h, decide_eq_false (mt pos.mp h)]
  refine ⟨negEq, ?_, ?_⟩
  · have sumEq : (step^[20] z).u + (step^[20] z).v =
        ((step^[20] (reduced b 20 z)).u + (step^[20] (reduced b 20 z)).v) + 2 ^ (b + 1) * (a + c) := by
      rw [hu, hv]; ring
    rw [sumEq, Nat.add_mul_mod_self_left]
  · by_cases h : 0 < (step^[20] (reduced b 20 z)).u
    · have le : (PortalValues.negative sg (step^[20] (reduced b 20 z)).u).toNat ≤
          (step^[20] (reduced b 20 z)).u := by
        cases PortalValues.negative sg (step^[20] (reduced b 20 z)).u
        · exact Nat.zero_le _
        · exact h
      have subEq : (step^[20] z).u - (PortalValues.negative sg (step^[20] (reduced b 20 z)).u).toNat =
          ((step^[20] (reduced b 20 z)).u - (PortalValues.negative sg (step^[20] (reduced b 20 z)).u).toNat) +
            2 ^ (b + 1) * a := by
        rw [hu, Nat.sub_add_comm le]
      rw [subEq, Nat.add_mul_mod_self_left]
    · have h0 : PortalValues.negative sg (step^[20] (reduced b 20 z)).u = false := by
        unfold PortalValues.negative
        rw [decide_eq_false h, Bool.and_false]
      rw [h0]; simp only [Bool.toNat_false, Nat.sub_zero, hu, Nat.add_mul_mod_self_left]

theorem restored20 (b k : Nat) (z : SkywalkNat.State) (small : Small20 b z) (sg : Bool) :
    let F := step^[20] z
    let r := step^[20] (reduced b 20 z)
    let e := (PortalValues.negative sg r.u).toNat
    ((if 2 ^ b ≤ r.u - e then ((F.u + F.v) / 2 ^ (b + 1)) % 2 ^ k else 0) + 2 ^ k -
        LeaveCompanion.upperBorrow (2 ^ b) r.u r.v e) % 2 ^ k =
      ((F.u - e) / 2 ^ (b + 1)) % 2 ^ k := by
  let F := step^[20] z
  let r := step^[20] (reduced b 20 z)
  let e := (PortalValues.negative sg r.u).toNat
  have le : e ≤ 1 := by cases h : PortalValues.negative sg r.u <;> simp [e, h]
  have low := retainedLow20 b z small.1 sg
  have hi := afterThreshold20 b z small.1 e le
  have eu : e ≤ F.u := by
    by_cases h : 0 < F.u
    · omega
    · have no : ¬ 0 < r.u := fun hr => h (hi.2.mpr hr)
      simp [e, PortalValues.negative, no]
  have two : 2 * 2 ^ b = 2 ^ (b + 1) := (Nat.mul_comm _ _).trans (pow_succ 2 b).symm
  have bor : LeaveCompanion.upperBorrow (2 ^ b) r.u r.v e =
      LeaveCompanion.upperBorrow (2 ^ b) F.u F.v e := by
    unfold LeaveCompanion.upperBorrow
    rw [two, low.2.1, low.2.2]
  have out := LeaveCompanion.upper_restore (2 ^ b) F.u F.v e (2 ^ k)
    (Nat.two_pow_pos _) le eu small.2 (Nat.two_pow_pos _)
  have hiff : 2 ^ b ≤ r.u - e ↔ 2 ^ b ≤ F.u - e := hi.1.symm
  change ((if 2 ^ b ≤ r.u - e then ((F.u + F.v) / 2 ^ (b + 1)) % 2 ^ k else 0) + 2 ^ k -
      LeaveCompanion.upperBorrow (2 ^ b) r.u r.v e) % 2 ^ k = _
  simp only [hiff, bor]
  simpa only [two] using out

theorem orient20 (b : Nat) (z : SkywalkNat.State) (small : Small20 b z) (hfar : far b 20 z) :
    decide (2 ^ b ≤ z.u) = decide (z.v < z.u) := by
  have hr := rail20 b z (small.1 hfar) hfar
  by_cases lhs : 2 ^ b ≤ z.u
  · have hv : z.v < 2 ^ b := by have := small.1 hfar; omega
    simp [lhs, show z.v < z.u by omega]
  · obtain ⟨_, _, guarded⟩ := hr.2 (by omega)
    have g := guard_gt 20 (reduced b 20 z).u
    simp [lhs, show ¬ z.v < z.u by omega]

theorem certifiedChain20 (b : Nat) (z : SkywalkNat.State) (g s : Bool)
    (small : Small20 b z) (odd : z.v % 2 = 1) (hfar : far b 20 z) :
    StairArchiveTrace.chain (decide (2 ^ b ≤ z.u)) (SkywalkTrace.trace 20 (SkywalkRails.encode g s z.u z.v)) := by
  rw [orient20 b z small hfar]
  exact StairArchiveTrace.signed (represented b 20 z (small.1 hfar) hfar).1 g s (by omega) odd

end ShadowMath

/-! ### Section 3: Physical wire geometry for the 9 20-tick blocks (`s = 165..325`) -/

def wpP20 (s : Nat) : Nat := railP s - sbP20 s - 21
def e0P20 (s : Nat) : Nat := 1579 + sbP20 s
def a0P20 (s : Nat) : Nat := s + sbP20 s + 37
def b0P20 (s : Nat) : Nat := 787 + sbP20 s

/-- Next block's cutoff: `sbP20 (s+20)` for `s < 325`, handing off to `Shadow7.sbP 345 = 76` at `s = 325`. -/
def nextSb20 (s : Nat) : Nat := if s + 20 < 345 then sbP20 (s + 20) else Shadow7.sbP (s + 20)

def lowsP20 (s : Nat) : Nat := (if s + 20 < 345 then 22 else 17) + nextSb20 s - sbP20 s

def liveW20 (s : Nat) : Nat :=
  (if 224 ≤ s + 20 ∧ s + 20 ≤ 286 then min 256 (511 - (s + 20))
   else if 257 ≤ s + 20 then 512 - (s + 20)
   else min 257 (railP (s + 20))) - (sbP20 s + 1)

/-- 21 one-hot barrel tags for shifts `0..20`: index 0 is `1581`, indices `1..19` are `1562..1580`, index 20 is `1560`. -/
def tagsP20 : List Wire :=
  [1581, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570,
   1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1560]

def bankW20 (s i : Nat) : Wire :=
  if i < 3 then e0P20 s + i
  else if i < wpP20 s then bTopP s + 1 + i - wpP20 s
  else 1603 + i - wpP20 s

/-- Carry & barrel scratch pool for 20-tick blocks (`1603..`, skipping `e0P20 s .. e0P20 s + 9`). -/
def poolW20 (s i : Nat) : Wire :=
  if 1603 + i < e0P20 s then 1603 + i else 1613 + i

def storeW20 (s i : Nat) : Wire :=
  let q := Partial.storeW i
  if q < e0P20 s then q else q + 10

theorem tagsP20_length : tagsP20.length = 21 := rfl

theorem tagsP20_nodup : tagsP20.Nodup := by decide

theorem tagsP20_range : ∀ q ∈ tagsP20, 1560 ≤ q ∧ q ≤ 1581 := by decide

theorem geom20_facts : ∀ j : Fin 9,
    let s := start20 j
    165 ≤ s ∧ s ≤ 325 ∧
    83 ≤ sbP20 s ∧ sbP20 s ≤ 163 ∧
    1662 ≤ e0P20 s ∧ e0P20 s ≤ 1742 ∧
    74 ≤ wpP20 s ∧ wpP20 s ≤ 114 ∧
    10 ≤ lowsP20 s ∧ lowsP20 s ≤ 12 ∧
    CRTBarrel20.UsedWidth20 (liveW20 s) ∧
    liveW20 s ≤ wpP20 s + 20 ∧
    lowsP20 s ≤ liveW20 s ∧
    1613 + wpP20 s + s < 2050 := by
  unfold CRTBarrel20.UsedWidth20
  decide +kernel

theorem bank20_cases (j : Fin 9) {i : Nat} (hi : i < wpP20 (start20 j) + 20) :
    let s := start20 j
    (i < 3 ∧ bankW20 s i = e0P20 s + i) ∨
    (3 ≤ i ∧ i < wpP20 s ∧ bankW20 s i = bTopP s + 1 + i - wpP20 s ∧
      b0P20 s + 22 ≤ bankW20 s i ∧ bankW20 s i ≤ bTopP s) ∨
    (wpP20 s ≤ i ∧ bankW20 s i = 1603 + i - wpP20 s ∧ 1603 ≤ bankW20 s i ∧ bankW20 s i ≤ 1622) := by
  have hg := geom20_facts j
  have hbt : bTopP (start20 j) = 785 + railP (start20 j) := rfl
  have hwp : wpP20 (start20 j) = railP (start20 j) - sbP20 (start20 j) - 21 := rfl
  have hb0 : b0P20 (start20 j) = 787 + sbP20 (start20 j) := rfl
  by_cases h1 : i < 3
  · left; exact ⟨h1, by simp [bankW20, h1]⟩
  · by_cases h2 : i < wpP20 (start20 j)
    · right; left
      refine ⟨by omega, h2, by simp [bankW20, h1, h2], ?_, ?_⟩ <;>
        (simp only [bankW20, h1, h2, if_false, if_true]; unfold Wire; omega)
    · right; right
      refine ⟨by omega, by simp [bankW20, h1, h2], ?_, ?_⟩ <;>
        (simp only [bankW20, h1, h2, if_false]; unfold Wire; omega)

theorem bank20_inj (j : Fin 9) {a b : Nat} (ha : a < wpP20 (start20 j) + 20)
    (hb : b < wpP20 (start20 j) + 20) (e : bankW20 (start20 j) a = bankW20 (start20 j) b) : a = b := by
  have hg := geom20_facts j
  have hbt : bTopP (start20 j) ≤ 1043 := by unfold bTopP railP; split_ifs <;> omega
  have ca := bank20_cases j ha
  have cb := bank20_cases j hb
  rcases ca with ⟨_, ea⟩ | ⟨_, _, ea, _, _⟩ | ⟨_, ea, _, _⟩ <;>
    rcases cb with ⟨_, eb⟩ | ⟨_, _, eb, _, _⟩ | ⟨_, eb, _, _⟩ <;>
    (rw [ea, eb] at e; unfold Wire at *; omega)

theorem pool20_cases (j : Fin 9) (i : Nat) :
    let s := start20 j
    (1603 + i < e0P20 s ∧ poolW20 s i = 1603 + i) ∨
    (e0P20 s ≤ 1603 + i ∧ poolW20 s i = 1613 + i) := by
  by_cases h : 1603 + i < e0P20 (start20 j)
  · left; exact ⟨h, by simp [poolW20, h]⟩
  · right; exact ⟨by omega, by simp [poolW20, h]⟩

theorem tagsP20_inj {a b : Nat} (ha : a < 21) (hb : b < 21)
    (e : tagsP20.getD a 0 = tagsP20.getD b 0) : a = b := by
  have h : ∀ x y : Fin 21, tagsP20.getD x.val 0 = tagsP20.getD y.val 0 → x = y := by decide
  exact congrArg Fin.val (h ⟨a, ha⟩ ⟨b, hb⟩ e)

theorem tagsP20_getD_range {k : Nat} (hk : k < 21) :
    1560 ≤ tagsP20.getD k 0 ∧ tagsP20.getD k 0 ≤ 1581 := by
  rw [List.getD_eq_getElem _ _ (by rw [tagsP20_length]; exact hk)]
  exact tagsP20_range _ (List.getElem_mem _)

/-! ### Section 4: `CRTBarrel20` physical instantiation for all 9 20-tick blocks -/

def place20 (s : Nat) (q : Nat) : Wire :=
  let n := liveW20 s
  if q < n then bankW20 s q
  else if q < n + 21 then tagsP20.getD (q - n) 0
  else poolW20 s (22 + (q - n - 21))

def barrel20 (s : Nat) (mir : Bool) : Program :=
  renameProgram (place20 s) (CRTBarrel20.logical20 (liveW20 s) mir)

def barrel20T (s : Nat) (mir : Bool) : Nat := (CRTBarrel20.listedPrice20 (liveW20 s) mir).t
def barrel20M (s : Nat) (mir : Bool) : Nat := (CRTBarrel20.listedPrice20 (liveW20 s) mir).m
def barrel20Slots (s : Nat) (mir : Bool) : Nat := (CRTBarrel20.listedPrice20 (liveW20 s) mir).slots

theorem place20_inj (j : Fin 9) :
    ∀ a < liveW20 (start20 j) + 31, ∀ b < liveW20 (start20 j) + 31,
      place20 (start20 j) a = place20 (start20 j) b → a = b := by
  have hg := geom20_facts j
  have hbt : bTopP (start20 j) ≤ 1043 := by unfold bTopP railP; split_ifs <;> omega
  have hscr : ∀ k < 10, poolW20 (start20 j) (22 + k) = 1625 + k := by
    intro k hk; unfold poolW20; rw [if_pos (by omega)]; unfold Wire; omega
  have hbank_rng : ∀ i < liveW20 (start20 j),
      (1662 ≤ bankW20 (start20 j) i ∧ bankW20 (start20 j) i ≤ 1744) ∨
      (870 ≤ bankW20 (start20 j) i ∧ bankW20 (start20 j) i ≤ 1043) ∨
      (1603 ≤ bankW20 (start20 j) i ∧ bankW20 (start20 j) i ≤ 1622) := by
    intro i hi
    rcases bank20_cases j (i := i) (by omega) with ⟨_, e⟩ | ⟨_, _, e, _, _⟩ | ⟨_, e, _, _⟩
    · left; rw [e]; unfold Wire at *; omega
    · right; left; have hb0 : b0P20 (start20 j) = 787 + sbP20 (start20 j) := rfl; unfold Wire at *; omega
    · right; right; unfold Wire at *; omega
  intro a ha b hb eq
  unfold place20 at eq
  by_cases ha1 : a < liveW20 (start20 j) <;> by_cases hb1 : b < liveW20 (start20 j)
  · simp only [ha1, hb1, if_true] at eq
    exact bank20_inj j (by omega) (by omega) eq
  · simp only [ha1, hb1, if_true, if_false] at eq
    have ba := hbank_rng a ha1
    by_cases hb2 : b < liveW20 (start20 j) + 21
    · rw [if_pos hb2] at eq
      have tb := tagsP20_getD_range (k := b - liveW20 (start20 j)) (by omega)
      unfold Wire at *; omega
    · rw [if_neg hb2, hscr (b - liveW20 (start20 j) - 21) (by omega)] at eq
      unfold Wire at *; omega
  · simp only [ha1, hb1, if_true, if_false] at eq
    have bb := hbank_rng b hb1
    by_cases ha2 : a < liveW20 (start20 j) + 21
    · rw [if_pos ha2] at eq
      have ta := tagsP20_getD_range (k := a - liveW20 (start20 j)) (by omega)
      unfold Wire at *; omega
    · rw [if_neg ha2, hscr (a - liveW20 (start20 j) - 21) (by omega)] at eq
      unfold Wire at *; omega
  · simp only [ha1, hb1, if_false] at eq
    by_cases ha2 : a < liveW20 (start20 j) + 21 <;> by_cases hb2 : b < liveW20 (start20 j) + 21
    · simp only [ha2, hb2, if_true] at eq
      have := tagsP20_inj (a := a - liveW20 (start20 j)) (b := b - liveW20 (start20 j)) (by omega) (by omega) eq
      omega
    · simp only [ha2, hb2, if_true, if_false] at eq
      have ta := tagsP20_getD_range (k := a - liveW20 (start20 j)) (by omega)
      rw [hscr (b - liveW20 (start20 j) - 21) (by omega)] at eq
      unfold Wire at *; omega
    · simp only [ha2, hb2, if_true, if_false] at eq
      have tb := tagsP20_getD_range (k := b - liveW20 (start20 j)) (by omega)
      rw [hscr (a - liveW20 (start20 j) - 21) (by omega)] at eq
      unfold Wire at *; omega
    · simp only [ha2, hb2, if_false] at eq
      rw [hscr (a - liveW20 (start20 j) - 21) (by omega), hscr (b - liveW20 (start20 j) - 21) (by omega)] at eq
      unfold Wire at *; omega

theorem barrel20_metrics (j : Fin 9) (mir : Bool) :
    toffoliCount (barrel20 (start20 j) mir) = barrel20T (start20 j) mir ∧
    measurementCount (barrel20 (start20 j) mir) = barrel20M (start20 j) mir ∧
    gateSlots (barrel20 (start20 j) mir) = barrel20Slots (start20 j) mir := by
  have hu := (geom20_facts j).2.2.2.2.2.2.2.2.2.2.1
  have hm := CRTBarrel20.logical20_metrics (liveW20 (start20 j)) hu mir
  have hr : CRTBarrel20.count (barrel20 (start20 j) mir) = CRTBarrel20.count (CRTBarrel20.logical20 (liveW20 (start20 j)) mir) :=
    CRTBarrel20.count_rename (place20 (start20 j)) _
  rw [hm] at hr
  exact ⟨congrArg CRTBarrel20.Count.t hr,
    congrArg CRTBarrel20.Count.m hr,
    congrArg CRTBarrel20.Count.slots hr⟩

theorem barrel20_phys (j : Fin 9) (mir : Bool) :
    GatePhysical (barrel20 (start20 j) mir) := by
  have hu := (geom20_facts j).2.2.2.2.2.2.2.2.2.2.1
  have hf := CRTBarrel20.logical20_fits (liveW20 (start20 j)) hu mir
  have hr := CRTBarrel20.fits_rename (Q := fun _ => True) (f := place20 (start20 j)) hf
    (fun _ _ => trivial) (fun a ha b hb => place20_inj j a ha b hb)
  intro g hg
  exact (hr g hg).1

theorem barrel20_wires (j : Fin 9) (mir : Bool) (q : Wire)
    (hq : q ∈ wires (barrel20 (start20 j) mir)) :
    (∃ i < liveW20 (start20 j), q = bankW20 (start20 j) i) ∨
    (∃ k < 10, q = poolW20 (start20 j) (22 + k)) ∨
    q ∈ tagsP20 := by
  have hu := (geom20_facts j).2.2.2.2.2.2.2.2.2.2.1
  have hf := CRTBarrel20.logical20_fits (liveW20 (start20 j)) hu mir
  rw [barrel20, renameProgram_support] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have hxlt : x < liveW20 (start20 j) + 31 := CRTBarrel20.support hf x hx
  unfold place20
  by_cases h1 : x < liveW20 (start20 j)
  · left; rw [if_pos h1]; exact ⟨x, h1, rfl⟩
  · by_cases h2 : x < liveW20 (start20 j) + 21
    · right; right
      rw [if_neg h1, if_pos h2, List.getD_eq_getElem _ _ (by rw [tagsP20_length]; unfold Wire at *; omega)]
      exact List.getElem_mem _
    · right; left
      rw [if_neg h1, if_neg h2]
      exact ⟨x - liveW20 (start20 j) - 21, by unfold Wire at *; omega, rfl⟩

theorem barrel20_cov (j : Fin 9) (mir : Bool) :
    WindowCovered.CoveredW (barrel20 (start20 j) mir) := by
  have hg := geom20_facts j
  have hbt : bTopP (start20 j) ≤ 1043 := by unfold bTopP railP; split_ifs <;> omega
  intro q hq
  rw [WindowCovered.dom_iff]
  rcases barrel20_wires j mir q hq with ⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩ | ht
  · rcases bank20_cases j (i := i) (by omega) with ⟨_, e⟩ | ⟨_, _, e, _, _⟩ | ⟨_, e, _, _⟩
    · rw [e]; unfold Wire at *; omega
    · have hb0 : b0P20 (start20 j) = 787 + sbP20 (start20 j) := rfl; unfold Wire at *; omega
    · unfold Wire at *; omega
  · rcases pool20_cases j (22 + k) with ⟨_, e⟩ | ⟨_, e⟩ <;> (rw [e]; unfold Wire at *; omega)
  · have := tagsP20_range q ht; unfold Wire at *; omega

/-- Physical barrel semantics for all 9 20-tick blocks (`j : Fin 9`), returning `HighBankBarrel.Result`. -/
theorem barrel20_result (j : Fin 9) (mir : Bool) (slot : Fin 22) (v : Nat) (s : State) (tape : List Bool)
    (small : v < 2 ^ (liveW20 (start20 j) - (slot.val - 1)))
    (input : HighBankBarrel.holds (bankW20 (start20 j)) (liveW20 (start20 j))
      (v <<< CRTBarrel20.entryShift mir slot.val) s)
    (tag : ∀ k < 21, s.basis (tagsP20.getD k 0) = decide (slot.val = k + 1))
    (scratch : ∀ k < 10, s.basis (poolW20 (start20 j) (22 + k)) = false) :
    HighBankBarrel.Result (bankW20 (start20 j)) (liveW20 (start20 j))
      (v <<< CRTBarrel20.exitShift mir slot.val) s (run (barrel20 (start20 j) mir) tape s) := by
  have hu := (geom20_facts j).2.2.2.2.2.2.2.2.2.2.1
  have hr := CRTBarrel20.barrel20_result (liveW20 (start20 j)) hu mir slot
    (bankW20 (start20 j)) (fun k => tagsP20.getD k 0) (fun k => poolW20 (start20 j) (22 + k))
    (place20 (start20 j))
    (fun i hi => by simp [place20, hi])
    (fun k hk => by
      unfold place20
      rw [if_neg (by unfold Wire at *; omega), if_pos (by unfold Wire at *; omega)]
      simp only [Nat.add_sub_cancel_left])
    (fun k hk => by
      unfold place20
      rw [if_neg (by unfold Wire at *; omega), if_neg (by unfold Wire at *; omega)]
      congr 1; unfold Wire at *; omega)
    (place20_inj j) v s tape small input tag scratch
  exact ⟨hr.1, hr.2.1, hr.2.2⟩

end ECDSAAdd.Entrant.StairPacket.Shadow20
end
-- ==== end Shadow7Wide20Core ====

-- ==== begin Shadow7Wide20Leave ====
section

/-!
20-tick shadow block circuits (`s ∈ {165, 185, ..., 325}`):
- `enterP20` / `enterInvP20` (reusing `enterFix17 s (sbP20 s + 5)`), exact counts, physicality & coverage.
- `leaveP20` / `leaveInvP20` with direct `CRTBarrel20` and 10-gate `kept10` pass, exact algebraic counts,
  physicality & coverage.
- `archiveLoadP20` / `archiveRestoreP20` (reusing the shared 63,145-row 10-tick codec), exact counts,
  physicality & coverage.
- `LeaveSelector20`: 23-mode symbolic selector certificates (`tags`, `controls`, `cleanup`) and `deadKept10`.
-/

namespace ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.GateMirror
open ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Baselines ECDSAAdd.Challenge

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

/-! ### Section 1: 20-tick block entry (`enterFix17 s (sbP20 s + 5)`) -/

def enterOps20 (s : Nat) : List Gate := Shadow7.enterFix17p s (sbP20 s + 5)

def enterP20 (j : Fin 9) : Program :=
  let s := start20 j
  let h := sbP20 s + 5
  let p := GateMirror.forward (Shadow7.enterFix17p s h)
  p.take 16 ++ [.measureX (h + 803) [] [.CZ 1556 (h + 802), .CZ (h + 1578) (h + 1575)]] ++ p.drop 18

def enterInvP20 (j : Fin 9) : Program := inverse (enterOps20 (start20 j))

theorem enter20_counts (j : Fin 9) :
    toffoliCount (enterP20 j) = 6 ∧ toffoliCount (enterInvP20 j) = 6 ∧
    measurementCount (enterP20 j) = 2 ∧ measurementCount (enterInvP20 j) = 3 ∧
    gateSlots (enterP20 j) = 35 ∧ gateSlots (enterInvP20 j) = 36 := by
  have h : ∀ k : Fin 9,
      toffoliCount (enterP20 k) = 6 ∧ toffoliCount (enterInvP20 k) = 6 ∧
      measurementCount (enterP20 k) = 2 ∧ measurementCount (enterInvP20 k) = 3 ∧
      gateSlots (enterP20 k) = 35 ∧ gateSlots (enterInvP20 k) = 36 := by decide +kernel
  exact h j

private theorem enterOps20_proper : ∀ j : Fin 9, (enterOps20 (start20 j)).all proper = true := by
  decide +kernel

private theorem enterOps20_dom : ∀ j : Fin 9,
    (enterOps20 (start20 j)).all (fun g => g.wires.all WindowCovered.domainW) = true := by
  decide +kernel

theorem enter20_phys (j : Fin 9) :
    GatePhysical (enterP20 j) ∧ GatePhysical (enterInvP20 j) := by
  have good : ∀ k : Fin 9, (enterP20 k).all physicalGateCheck = true := by decide +kernel
  exact ⟨physicalGateCheck_correct _ (good j), (physical_of_proper _ (List.all_eq_true.mp (enterOps20_proper j))).2⟩

theorem enter20_cov (j : Fin 9) :
    WindowCovered.CoveredW (enterP20 j) ∧ WindowCovered.CoveredW (enterInvP20 j) := by
  have hfwd : ∀ k : Fin 9, ∀ q ∈ wires (enterP20 k), WindowCovered.domainW q = true := by decide +kernel
  have hall : AllW (fun q => WindowCovered.domainW q = true) (enterOps20 (start20 j)) := fun g hg q hq =>
    List.all_eq_true.mp (List.all_eq_true.mp (enterOps20_dom j) g hg) q hq
  exact ⟨hfwd j, (allW_programs hall).2⟩

/-! ### Section 2: 20-tick block leave (`leaveP20` / `leaveInvP20`) with direct `CRTBarrel20` + `kept10` -/

/-- Flip `make` ↔ `pop` (used for exact uncompute segments). -/
def flipGate : Gate → Gate
  | .make a b t => .pop a b t
  | .pop a b t => .make a b t
  | g => g

def uncomputeOps (gs : List Gate) : List Gate := (gs.map flipGate).reverse

/-- Segment 0: 23 rows (`-1..21`), signs at `a0P20+21 = s+h+58` and `b0P20+21 = h+808` → `e0P20+5 = h+1584`. -/
def fix0P20 (s h : Nat) : List Gate :=
  [.cx (s + h + 58) (h + 1584), .cx (h + 808) (h + 1584)] ++
  ((List.range 23).flatMap fun i =>
    [.cx (s + h + 36 + i) (h + 786 + i), .ccx (s + 35) (h + 786 + i) (s + h + 36 + i), .cx (s + h + 36 + i) (h + 786 + i)]) ++
  ((List.range 23).map fun i => .cx (h + 1584) (h + 786 + i))

/-- Segment 1: negate all 20 `g` parity wires `s+16..s+35`. -/
def leaveFix1_20 (s : Nat) : List Gate := (List.range 20).map (fun i => .x (s + 16 + i))

/-- Segment 2: long latch, mask, and companion erase over 22 register rows `h+786..h+807`. -/
def fix2P20 (s h : Nat) : List Gate :=
  let bs := (List.range 21).map (h + 786 + ·)
  let latchMake := .make (h + 786) (h + 787) 1557 ::
    ((List.range 19).map fun i => .make (1557 + i) (h + 788 + i) (1558 + i))
  let latchPop := ((List.range 19).map fun i => .pop (1557 + i) (h + 788 + i) (1558 + i)).reverse ++
    [.pop (h + 786) (h + 787) 1557]
  let maskMake := (List.range 20).map fun i => .make (h + 786 + i) (1557 + i) (1558 + i)
  let maskPop := ((List.range 19).map fun i =>
    [.pop (h + 787 + i) (1558 + i) (1559 + i), .cx (1558 + i) (h + 787 + i)]).reverse.flatten
  let erasePop := (List.range 20).map fun i => .pop 1556 (s + h + 37 + i) (h + 787 + i)
  xsG bs ++ latchMake ++ [.cx 1576 1556, .x 1556] ++ latchPop ++ xsG bs.reverse ++
  [.x 1557, .cx (s + h + 36) 1557] ++ maskMake ++ [.cx 1577 (h + 806)] ++ maskPop ++ erasePop

/-- Segment 3: split `far = e0P20+3` and `side = e0P20+4` into `1559` (left rail) and `1560` (right rail). -/
def leaveFix3_20 (h : Nat) : List Gate :=
  [.make (h + 1582) (h + 1583) 1559, .cx (h + 1582) 1560, .cx 1559 1560]

/-- Segment 4: 20 first-swap one-hot hits `1561..1580` (with `1560` holding wait = 20). -/
def leaveFix4_20 (s : Nat) : List Gate :=
  (List.range 20).flatMap fun i =>
    [.make 1560 (OB5.sig (s + 19) (s + 1044 + i)) (1561 + i), .cx (1561 + i) 1560]

/-- 21 `(tag, cell)` pairs for the crossing controlled-swap chain. -/
def moveRows20 (s : Nat) : List MoveChain.Row :=
  (List.range 21).map fun i => (tagsP20.getD i 0, a0P20 s + i)

/-- Segment 5 prefix: `u_after_10` (`e0P20+7`), tag 0 (`1581`), and 18-step rolling AND chain (`1582..1599`). -/
def leaveFix5Pre20 (s : Nat) : List Gate :=
  [.cx 1559 (e0P20 s + 7)] ++
  ((List.range 10).map fun i => .cx (1561 + i) (e0P20 s + 7)) ++
  [.cx 1559 1581, .cx 1561 1581,
   .make 1562 (s + 18) 1582, .make 1582 (s + 19) 1583, .cx 1563 1583,
   .make 1583 (s + 20) 1584, .make 1584 (s + 21) 1585, .cx 1564 1585,
   .make 1585 (s + 22) 1586, .make 1586 (s + 23) 1587, .cx 1565 1587,
   .make 1587 (s + 24) 1588, .make 1588 (s + 25) 1589, .cx 1566 1589,
   .make 1589 (s + 26) 1590, .make 1590 (s + 27) 1591, .cx 1567 1591,
   .make 1591 (s + 28) 1592, .make 1592 (s + 29) 1593, .cx 1568 1593,
   .make 1593 (s + 30) 1594, .make 1594 (s + 31) 1595, .cx 1569 1595,
   .make 1595 (s + 32) 1596, .make 1596 (s + 33) 1597, .cx 1570 1597,
   .make 1597 (s + 34) 1598, .make 1598 (s + 35) 1599]

/-- Segment 5 suffix: `signExpr` (`1601`) and `d0 ∧ signExpr` (`1602`). -/
def leaveFix5Post20 (s : Nat) : List Gate :=
  [.cx 1599 1601] ++
  ((List.range 10).map fun i => .cx (1571 + i) 1601) ++
  [.cx 1560 1601, .make (e0P20 s + 6) 1601 1602]

def leaveFix5Move20 (s : Nat) : List Gate :=
  leaveFix5Pre20 s ++ rowGates (e0P20 s + 6) (moveRows20 s) ++ leaveFix5Post20 s

/-- Segment 6: bank-wide high adjust (`±1` with carry-in `e0P20+3`, sign `1601`). -/
def leaveAdjustCore20 (s : Nat) : List Gate :=
  adjustG ((List.range (wpP20 s)).map (bankW20 s))
    ((List.range (wpP20 s - 1)).map (poolW20 s)) (e0P20 s + 3) 1601

def leaveAdjust20 (s : Nat) : List Gate :=
  [.cx (e0P20 s + 6) (e0P20 s + 3)] ++ leaveAdjustCore20 s

/-- All leave gates before `CRTBarrel20`. -/
def leaveBefore20 (s : Nat) : List Gate :=
  fix0P20 s (sbP20 s) ++ leaveFix1_20 s ++ fix2P20 s (sbP20 s) ++ leaveFix3_20 (sbP20 s) ++
  leaveFix4_20 s ++ leaveFix5Move20 s ++ leaveAdjust20 s

/-- Segment 8: load digit bit 1 onto `1623` and restore `e0P20+3` to `far`. -/
def fix8P20 (s : Nat) : List Gate :=
  [.cx (e0P20 s + 3) 1623, .cx 1601 1623, .cx 1602 1623, .cx (e0P20 s + 6) (e0P20 s + 3)]

/-- 22 join columns (`0..21`, first `lowsP20 s` stay on `a0P20+i`, rest move to `bankW20 i`). -/
def columnsP20 (s : Nat) : List HighBankJoin.Column :=
  (List.range 22).map fun i =>
    ⟨decide (i < lowsP20 s), if i < 21 then some (tagsP20.getD i 0) else none, a0P20 s + i, bankW20 s i⟩


/-! ### KeptParity20: 10->9 CCX parity reduction for 20-tick `keptG` -/

namespace KeptParity20
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.GateMirror
set_option linter.unusedSimpArgs false

def old20 : List Gate :=
  [.ccx 1 0 11, .ccx 2 0 12, .ccx 3 0 13, .ccx 4 0 14, .ccx 5 0 15,
   .ccx 6 0 16, .ccx 7 0 17, .ccx 8 0 18, .ccx 9 0 19, .ccx 10 0 20]

def replacement20 : List Gate :=
  [.cx 0 11,
   .cx 12 11, .ccx 2 0 12, .cx 12 11,
   .cx 13 11, .ccx 3 0 13, .cx 13 11,
   .cx 14 11, .ccx 4 0 14, .cx 14 11,
   .cx 15 11, .ccx 5 0 15, .cx 15 11,
   .cx 16 11, .ccx 6 0 16, .cx 16 11,
   .cx 17 11, .ccx 7 0 17, .cx 17 11,
   .cx 18 11, .ccx 8 0 18, .cx 18 11,
   .cx 19 11, .ccx 9 0 19, .cx 19 11,
   .cx 20 11, .ccx 10 0 20, .cx 20 11]

def port20 (s : Nat) : Wire → Wire
  | 0 => 1623
  | i + 1 => if i < 10 then tagsP20.getD i 0 else a0P20 s + (i - 9)

def placed20 (s : Nat) : List Gate :=
  [.cx (port20 s 0) (port20 s 11),
   .cx (port20 s 12) (port20 s 11), .ccx (port20 s 2) (port20 s 0) (port20 s 12), .cx (port20 s 12) (port20 s 11),
   .cx (port20 s 13) (port20 s 11), .ccx (port20 s 3) (port20 s 0) (port20 s 13), .cx (port20 s 13) (port20 s 11),
   .cx (port20 s 14) (port20 s 11), .ccx (port20 s 4) (port20 s 0) (port20 s 14), .cx (port20 s 14) (port20 s 11),
   .cx (port20 s 15) (port20 s 11), .ccx (port20 s 5) (port20 s 0) (port20 s 15), .cx (port20 s 15) (port20 s 11),
   .cx (port20 s 16) (port20 s 11), .ccx (port20 s 6) (port20 s 0) (port20 s 16), .cx (port20 s 16) (port20 s 11),
   .cx (port20 s 17) (port20 s 11), .ccx (port20 s 7) (port20 s 0) (port20 s 17), .cx (port20 s 17) (port20 s 11),
   .cx (port20 s 18) (port20 s 11), .ccx (port20 s 8) (port20 s 0) (port20 s 18), .cx (port20 s 18) (port20 s 11),
   .cx (port20 s 19) (port20 s 11), .ccx (port20 s 9) (port20 s 0) (port20 s 19), .cx (port20 s 19) (port20 s 11),
   .cx (port20 s 20) (port20 s 11), .ccx (port20 s 10) (port20 s 0) (port20 s 20), .cx (port20 s 20) (port20 s 11)]

theorem counts_placed20 (s : Nat) : Counts (placed20 s) 9 0 0 28 := ⟨rfl, rfl, rfl, rfl⟩

theorem noMake_placed20 (s : Nat) : NoMake (placed20 s) := by
  intro g hg
  simp only [placed20, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem placed20_ok : ∀ j : Fin 9,
    (placed20 (start20 j)).all (fun g => proper g && g.wires.all WindowCovered.domainW) = true := by
  decide +kernel

def relation20 (v : BasisState) : Prop :=
  (v 1 && v 0) =
    (v 0 ^^ (v 2 && v 0) ^^ (v 3 && v 0) ^^ (v 4 && v 0) ^^ (v 5 && v 0) ^^
     (v 6 && v 0) ^^ (v 7 && v 0) ^^ (v 8 && v 0) ^^ (v 9 && v 0) ^^ (v 10 && v 0))

private theorem finiteKey10 : ∀ k : Fin 10,
    decide (0 = k.val) =
      (true ^^ decide (1 = k.val) ^^ decide (2 = k.val) ^^ decide (3 = k.val) ^^
       decide (4 = k.val) ^^ decide (5 = k.val) ^^ decide (6 = k.val) ^^
       decide (7 = k.val) ^^ decide (8 = k.val) ^^ decide (9 = k.val)) := by
  decide +kernel

theorem relation20_of_key (v : BasisState) (en : Bool) (key : Nat)
    (hact : v 0 = true → en = true ∧ key < 10)
    (hports : ∀ i, i < 10 → v (i + 1) = (en && decide (i = key))) : relation20 v := by
  unfold relation20
  cases hv0 : v 0
  · simp
  · obtain ⟨hen, hlt⟩ := hact hv0
    rw [hports 0 (by decide), hports 1 (by decide), hports 2 (by decide), hports 3 (by decide),
      hports 4 (by decide), hports 5 (by decide), hports 6 (by decide), hports 7 (by decide),
      hports 8 (by decide), hports 9 (by decide), hen]
    simp only [Bool.true_and, Bool.and_true]
    exact finiteKey10 ⟨key, hlt⟩

private def shifted20 (s : State) (x : Bool) : State :=
  ⟨s.phase, writeBit s.basis 11 (s.basis 11 ^^ x)⟩

private def bareStep20 (h y : Wire) (s : State) : State :=
  ⟨s.phase, writeBit s.basis y (s.basis y ^^ (s.basis h && s.basis 0))⟩

private theorem twice20 (a b c d : Bool) : (((a ^^ b) ^^ c) ^^ (c ^^ d)) = (a ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem liftedStep20 (h y : Wire) (hn : h ≠ 11) (yn : y ≠ 11) (s : State) (x : Bool)
    (tail : Program) (m : List Bool) :
    run (.CX y 11 :: .CCX h 0 y :: .CX y 11 :: tail) m (shifted20 s x) =
      run tail m (shifted20 (bareStep20 h y s) (x ^^ (s.basis h && s.basis 0))) := by
  simp only [run]
  apply congrArg (run tail m)
  apply State.extensionality
  · rfl
  funext q
  by_cases endBit : q = 11
  · subst q
    simp [shifted20, bareStep20, writeBit, Function.update_of_ne, hn, yn, Ne.symm yn, twice20]
  · by_cases dataBit : q = y
    · subst q
      simp [shifted20, bareStep20, writeBit, Function.update_of_ne, hn, yn, Ne.symm yn]
    · simp [shifted20, bareStep20, writeBit, Function.update_of_ne, endBit, dataBit]

private def bare20 (i : Nat) : Nat → Program
  | 0 => []
  | n + 1 => .CCX (i + 2) 0 (i + 12) :: bare20 (i + 1) n

private def lifted20 (i : Nat) : Nat → Program
  | 0 => []
  | n + 1 => .CX (i + 12) 11 :: .CCX (i + 2) 0 (i + 12) :: .CX (i + 12) 11 :: lifted20 (i + 1) n

private def parity20 (v : BasisState) (i : Nat) : Nat → Bool → Bool
  | 0, x => x
  | n + 1, x => parity20 v (i + 1) n (x ^^ (v (i + 2) && v 0))

private theorem ladder20 (v : BasisState) (m : List Bool) (i n : Nat) (bound : i + n ≤ 9)
    (s : State) (keep : ∀ q : Nat, q ≤ 10 → s.basis q = v q) (x : Bool) :
    run (lifted20 i n) m (shifted20 s x) = shifted20 (run (bare20 i n) m s) (parity20 v i n x) := by
  induction n generalizing i s x with
  | zero => rfl
  | succ n ih =>
    have hn : (i + 2 : Wire) ≠ 11 := by unfold Wire at *; omega
    have yn : (i + 12 : Wire) ≠ 11 := by unfold Wire at *; omega
    simp only [lifted20, bare20, parity20, liftedStep20 _ _ hn yn, run]
    rw [← keep (i + 2) (by omega), ← keep 0 (by decide)]
    apply ih (i + 1) (by omega) (bareStep20 (i + 2) (i + 12) s)
    intro q hq
    have ne : (q : Wire) ≠ i + 12 := by unfold Wire at *; omega
    simpa [bareStep20, writeBit, Function.update_of_ne ne] using keep q hq

private theorem parity20_left (v : BasisState) (i n : Nat) (a b : Bool) :
    parity20 v i n (a ^^ b) = (a ^^ parity20 v i n b) := by
  induction n generalizing i b with
  | zero => rfl
  | succ n ih => simp only [parity20, Bool.xor_assoc, ih]

private theorem shift20_shift (s : State) (a b : Bool) : shifted20 (shifted20 s a) b = shifted20 s (a ^^ b) := by
  apply State.extensionality
  · rfl
  funext q
  by_cases h : q = 11
  · subst q; simp [shifted20, writeBit, Bool.xor_assoc]
  · simp [shifted20, writeBit, Function.update_of_ne h]

private theorem shift20_zero (s : State) : shifted20 s false = s := by
  apply State.extensionality
  · rfl
  funext q
  by_cases h : q = 11
  · subst q; simp [shifted20, writeBit]
  · simp [shifted20, writeBit, Function.update_of_ne h]

theorem same20 (s : State) (m : List Bool) (mode : relation20 s.basis) :
    run (GateMirror.forward replacement20) m s = run (GateMirror.forward old20) m s := by
  have newProgram : GateMirror.forward replacement20 = .CX 0 11 :: lifted20 0 9 := rfl
  have oldProgram : GateMirror.forward old20 = .CCX 1 0 11 :: bare20 0 9 := rfl
  rw [newProgram, oldProgram]
  let top := s.basis 1 && s.basis 0
  let t := shifted20 s top
  change run (lifted20 0 9) m (shifted20 s (s.basis 0)) = run (bare20 0 9) m t
  have prepared : shifted20 t (top ^^ s.basis 0) = shifted20 s (s.basis 0) := by
    rw [show shifted20 t _ = shifted20 s (top ^^ (top ^^ s.basis 0)) from shift20_shift _ _ _]
    congr 1
    cases top <;> cases s.basis 0 <;> rfl
  have keep (q : Nat) (hq : q ≤ 10) : t.basis q = s.basis q := by
    have ne : (q : Wire) ≠ 11 := by unfold Wire at *; omega
    simp [t, shifted20, writeBit, Function.update_of_ne ne]
  have parityEq : parity20 s.basis 0 9 (s.basis 0) = top := mode.symm
  rw [← prepared, ladder20 s.basis m 0 9 (by decide) t keep, parity20_left, parityEq, Bool.xor_self, shift20_zero]

private theorem geometry20 : ∀ (j : Fin 9) (a b : Fin 21), port20 (start20 j) a = port20 (start20 j) b → a = b := by
  decide +kernel

theorem placed20_run_eq (j : Fin 9) (s : State) (m : List Bool)
    (h : relation20 (fun q => s.basis (port20 (start20 j) q))) :
    run (GateMirror.forward (placed20 (start20 j))) m s =
      run (GateMirror.forward (keptG (tagsP20.getD · 0) (fun i => a0P20 (start20 j) + i) 1623 0 10)) m s := by
  let f := port20 (start20 j)
  let t : State := ⟨s.phase, fun q => s.basis (f q)⟩
  have inj (a : Wire) (ha : a ∈ Finset.range 21) (b : Wire) (hb : b ∈ Finset.range 21)
      (eq : f a = f b) : a = b :=
    congrArg Fin.val (geometry20 j ⟨a, Finset.mem_range.mp ha⟩ ⟨b, Finset.mem_range.mp hb⟩ eq)
  have eq : run (GateMirror.forward replacement20) m t = run (GateMirror.forward old20) m t := same20 t m h
  have boundedNew : wires (GateMirror.forward replacement20) ⊆ Finset.range 21 := by decide
  have boundedOld : wires (GateMirror.forward old20) ⊆ Finset.range 21 := by decide
  have hf_new : GateMirror.forward (placed20 (start20 j)) = renameProgram f (GateMirror.forward replacement20) := rfl
  have hf_old : GateMirror.forward (keptG (tagsP20.getD · 0) (fun i => a0P20 (start20 j) + i) 1623 0 10) =
      renameProgram f (GateMirror.forward old20) := rfl
  rw [hf_new, hf_old]
  exact run_rename_eq_of_eq f (Finset.range 21) inj _ _ boundedNew boundedOld m m t s rfl (fun _ _ => rfl) eq

end KeptParity20

/-- Segment 9: 9-CCX `KeptParity20.placed20` pass + `wordGM`. -/
def leaveJoinMove20 (s : Nat) : List Gate :=
  KeptParity20.placed20 s ++ wordGM 1624 (columnsP20 s)

/-- Segment 10: clear `1623`. -/
def fix10P20 (s : Nat) : List Gate :=
  [.cx (e0P20 s + 3) 1623, .cx (e0P20 s + 6) 1623, .cx 1601 1623, .cx 1602 1623]

/-- Segment 11: uncompute `1602, 1601, 1599..1582, 1581`. -/
def leaveFix11_20 (s : Nat) : List Gate :=
  uncomputeOps ((leaveFix5Pre20 s).drop 11 ++ leaveFix5Post20 s)

/-- Segment 12: uncompute first-swap hits `1580..1561`. -/
def leaveFix12_20 (s : Nat) : List Gate := uncomputeOps (leaveFix4_20 s)

/-- Segment 13: low-limb store and sign close. -/
def leaveLowStore20 (s : Nat) : List Gate :=
  let L := lowsP20 s
  let bs := (List.range L).map (b0P20 s + ·)
  [.cx (e0P20 s + 3) 1560, .cx 1559 1560, .pop (e0P20 s + 3) (e0P20 s + 4) 1559] ++
  ((List.range L).map fun i => .make 1556 (a0P20 s + i) (b0P20 s + i)) ++ xsG bs ++
  addG bs ((List.range (L - 1)).map (1559 + ·)) 1558 ++ xsG bs ++
  [.pop (b0P20 s - 1) 1557 1558, .cx (a0P20 s - 1) 1557, .x 1557]

/-- Store carries skipping `1603..1622` (zero-pad of `bankW20`) and `e0P20 s .. e0P20 s + 9`. -/
def storeWire20 (s i : Nat) : Wire :=
  let q := if 1558 + i < 1603 then 1558 + i else 1578 + i
  if q < e0P20 s then q else q + 10

/-- Segment 14: mapped high/low far-flag & side-flag store for the next block. -/
def leaveStoreMapped20 (s : Nat) : List Gate :=
  let L := lowsP20 s
  let top := a0P20 s + L - 1
  let H := liveW20 s - L
  let hi := (List.range H).map fun i => bankW20 s (L + i)
  let seq := fun i => if i = 0 then top else bankW20 s (L + i - 1)
  let seq2 := (List.range (L + 1)).map (b0P20 s - 1 + ·)
  [.x 1558, .x top] ++ xsG hi ++
  chainG (storeWire20 s) seq [.cx (storeWire20 s (H + 1)) 1557, .x 1557] 0 (H + 1) ++
  xsG hi.reverse ++ [.x top, .x 1558, .make 1556 1557 1558, .x 1558] ++
  xsG seq2 ++ chainG (1558 + ·) (b0P20 s - 1 + ·) [.cx (1558 + (L + 1)) 1556, .x 1556] 0 (L + 1) ++
  xsG seq2.reverse ++ [.x 1558]

/-- Segment 15: restore `g` wires and close low A/B rails. -/
def leaveLowClose20 (s : Nat) : List Gate :=
  let L := lowsP20 s
  xsG ((List.range 20).map (s + 16 + ·)) ++
  ((List.range (L + 1)).map fun i => .cx (e0P20 s + 5) (b0P20 s - 1 + i)) ++
  ((List.range (L + 1)).flatMap fun i => cswapG (s + 35) (b0P20 s - 1 + i) (a0P20 s - 1 + i))

def nextE0_20 (s : Nat) : Nat := if s + 20 < 345 then e0P20 (s + 20) else Shadow7.e0P (s + 20)
def nextWp20 (s : Nat) : Nat := if s + 20 < 345 then wpP20 (s + 20) else Shadow7.wpP (s + 20)

def movesP20 (s : Nat) : List (Wire × Wire) :=
  ((List.range (nextWp20 s - 2)).map fun i => (bankW20 s (lowsP20 s + i), bTopP (s + 20) + 3 + i - nextWp20 s)) ++
  [(1557, nextE0_20 s + 3), (1558, nextE0_20 s + 4), (e0P20 s + 5, nextE0_20 s + 5),
   (e0P20 s + 3, nextE0_20 s + 6), (e0P20 s + 7, nextE0_20 s + 7), (e0P20 s + 6, nextE0_20 s + 8)]

/-- Segment 16: uncompute `e0P20+4` via 10 prefix swaps (`[s, s+10)`) and move bank + flags to next block. -/
def closeRecs20 (s : Nat) : List Wire :=
  (List.range 10).map fun i => OB5.sig (s + 19) (s + 1044 + i)

def closeFlag20 (s : Nat) : List Gate :=
  Shadow7.parityG (e0P20 s + 7) (e0P20 s + 4) 1556 (closeRecs20 s)

def leaveClose20 (s : Nat) : List Gate :=
  closeFlag20 s ++ swapsG (movesP20 s)

/-- All leave gates after `CRTBarrel20`. -/
def leaveAfter20 (s : Nat) : List Gate :=
  fix8P20 s ++ leaveJoinMove20 s ++ fix10P20 s ++ leaveFix11_20 s ++ leaveFix12_20 s ++
  leaveLowStore20 s ++ leaveStoreMapped20 s ++ leaveLowClose20 s ++ leaveClose20 s

/-- Full 20-tick forward & inverse leave programs with direct `CRTBarrel20`. -/
def leaveP20 (j : Fin 9) : Program :=
  GateMirror.forward (leaveBefore20 (start20 j)) ++ barrel20 (start20 j) false ++
    GateMirror.forward (leaveAfter20 (start20 j))

def leaveInvP20 (j : Fin 9) : Program :=
  inverse (leaveAfter20 (start20 j)) ++ barrel20 (start20 j) true ++
    inverse (leaveBefore20 (start20 j))

/-! ### Fast algebraic counts of `leaveBefore20`, `leaveAfter20`, and `leaveP20` -/

private theorem counts_uncomputeOps (gs : List Gate) {c m p n : Nat} (h : Counts gs c m p n) :
    Counts (uncomputeOps gs) c p m n := by
  have aux : ∀ l : List Gate,
      (l.map flipGate).countP isCCX = l.countP isCCX ∧
      (l.map flipGate).countP isMake = l.countP isPop ∧
      (l.map flipGate).countP isPop = l.countP isMake ∧
      (l.map flipGate).length = l.length := by
    intro l; induction l with
    | nil => exact ⟨rfl, rfl, rfl, rfl⟩
    | cons g l ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      cases g <;> simp [flipGate, isCCX, isMake, isPop, h1, h2, h3, h4]
  obtain ⟨h1, h2, h3, h4⟩ := aux gs
  exact ⟨by rw [uncomputeOps, List.countP_reverse, h1, h.ccx],
    by rw [uncomputeOps, List.countP_reverse, h2, h.pop],
    by rw [uncomputeOps, List.countP_reverse, h3, h.make],
    by rw [uncomputeOps, List.length_reverse, h4, h.len]⟩

theorem counts_leaveBefore20 (s : Nat) (hw : 1 ≤ wpP20 s) :
    Counts (leaveBefore20 s) 44 (wpP20 s + 79) (wpP20 s + 58) (5 * wpP20 s + 436) := by
  have c0 : Counts (fix0P20 s (sbP20 s)) 23 0 0 94 := ⟨rfl, rfl, rfl, rfl⟩
  have c1 : Counts (leaveFix1_20 s) 0 0 0 20 := ⟨rfl, rfl, rfl, rfl⟩
  have c2 : Counts (fix2P20 s (sbP20 s)) 0 40 59 165 := ⟨rfl, rfl, rfl, rfl⟩
  have c3 : Counts (leaveFix3_20 (sbP20 s)) 0 1 0 3 := ⟨rfl, rfl, rfl, rfl⟩
  have c4 : Counts (leaveFix4_20 s) 0 20 0 40 := ⟨rfl, rfl, rfl, rfl⟩
  have c5a : Counts (leaveFix5Pre20 s) 0 18 0 39 := ⟨rfl, rfl, rfl, rfl⟩
  have c5b : Counts (rowGates (e0P20 s + 6) (moveRows20 s)) 21 0 0 63 := by
    have r := counts_rowGates (e0P20 s + 6) (moveRows20 s)
    have hl : (moveRows20 s).length = 21 := by simp [moveRows20]
    rw [hl] at r; exact r
  have c5c : Counts (leaveFix5Post20 s) 0 1 0 13 := ⟨rfl, rfl, rfl, rfl⟩
  have c5 : Counts (leaveFix5Move20 s) 21 19 0 115 :=
    ((c5a.app c5b).app c5c).congr rfl rfl rfl rfl
  have c6core : Counts (leaveAdjustCore20 s) 0 (wpP20 s - 1) (wpP20 s - 1) (5 * wpP20 s - 2) := by
    unfold leaveAdjustCore20 adjustG
    exact ((counts_cxsG _ _).app ((counts_addG _ _ _ (by simp; omega)).app (counts_cxsG _ _))).congr
      (by simp) (by simp) (by simp) (by simp; omega)
  have c6 : Counts (leaveAdjust20 s) 0 (wpP20 s - 1) (wpP20 s - 1) (5 * wpP20 s - 1) :=
    ((⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx (e0P20 s + 6) (e0P20 s + 3)] 0 0 0 1).app c6core).congr
      (by omega) (by omega) (by omega) (by omega)
  exact ((((((c0.app c1).app c2).app c3).app c4).app c5).app c6).congr
    (by omega) (by omega) (by omega) (by omega)

theorem counts_leaveAfter20 (s : Nat) (hL1 : 1 ≤ lowsP20 s) (hL2 : lowsP20 s ≤ 22)
    (hLW : lowsP20 s ≤ liveW20 s) (hn : 2 ≤ nextWp20 s) :
    Counts (leaveAfter20 s) (lowsP20 s + 10) (liveW20 s + 2 * lowsP20 s + 2)
      (liveW20 s + lowsP20 s + 65) (4 * liveW20 s + 9 * lowsP20 s + 305 + 3 * nextWp20 s) := by
  have c8 : Counts (fix8P20 s) 0 0 0 4 := ⟨rfl, rfl, rfl, rfl⟩
  have c9 : Counts (leaveJoinMove20 s) 9 0 22 (136 - lowsP20 s) := by
    have hw := counts_wordGM 1624 (columnsP20 s)
    have e1 : (columnsP20 s).length = 22 := by simp [columnsP20]
    have e2 : (columnsP20 s).countP (fun r => r.hot.isSome) = 21 := by
      simp only [columnsP20, List.countP_map]
      show (List.range 22).countP (fun i => (if i < 21 then some (tagsP20.getD i 0) else none : Option Wire).isSome) = 21
      decide
    have e3 : (columnsP20 s).countP (fun r => r.low) = lowsP20 s := by
      simp only [columnsP20, List.countP_map]
      show (List.range 22).countP (fun i => decide (i < lowsP20 s)) = lowsP20 s
      rw [countP_range_lt]; omega
    rw [e1, e2, e3] at hw
    exact ((KeptParity20.counts_placed20 s).app hw).congr (by omega) rfl (by omega) (by omega)
  have c10 : Counts (fix10P20 s) 0 0 0 4 := ⟨rfl, rfl, rfl, rfl⟩
  have c11 : Counts (leaveFix11_20 s) 0 0 19 41 := by
    have hpre : Counts ((leaveFix5Pre20 s).drop 11) 0 18 0 28 := ⟨rfl, rfl, rfl, rfl⟩
    have hpost : Counts (leaveFix5Post20 s) 0 1 0 13 := ⟨rfl, rfl, rfl, rfl⟩
    exact counts_uncomputeOps _ ((hpre.app hpost).congr rfl rfl rfl rfl)
  have c12 : Counts (leaveFix12_20 s) 0 0 20 40 :=
    counts_uncomputeOps _ (⟨rfl, rfl, rfl, rfl⟩ : Counts (leaveFix4_20 s) 0 20 0 40)
  have c13 : Counts (leaveLowStore20 s) 0 (2 * lowsP20 s - 1) (lowsP20 s + 1) (6 * lowsP20 s + 4) := by
    unfold leaveLowStore20
    have h1 : Counts [.cx (e0P20 s + 3) 1560, .cx 1559 1560, .pop (e0P20 s + 3) (e0P20 s + 4) 1559] 0 0 1 3 := ⟨rfl, rfl, rfl, rfl⟩
    have h2 := counts_mapG (List.range (lowsP20 s)) (fun i => Gate.make 1556 (a0P20 s + i) (b0P20 s + i))
      false true false (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    have h3 := counts_xsG ((List.range (lowsP20 s)).map (b0P20 s + ·))
    have h4 := counts_addG ((List.range (lowsP20 s - 1)).map (1559 + ·)) ((List.range (lowsP20 s)).map (b0P20 s + ·)) 1558 (by simp; omega)
    have h5 : Counts [.pop (b0P20 s - 1) 1557 1558, .cx (a0P20 s - 1) 1557, .x 1557] 0 0 1 3 := ⟨rfl, rfl, rfl, rfl⟩
    exact (((((h1.app h2).app h3).app h4).app h3).app h5).congr (by simp) (by simp; omega) (by simp; omega) (by simp; omega)
  have c14 : Counts (leaveStoreMapped20 s) 0 (liveW20 s + 3) (liveW20 s + 2) (4 * liveW20 s + 17) := by
    unfold leaveStoreMapped20
    let L := lowsP20 s
    let H := liveW20 s - L
    have h1 : Counts [.x 1558, .x (a0P20 s + L - 1)] 0 0 0 2 := ⟨rfl, rfl, rfl, rfl⟩
    have h2 := counts_xsG ((List.range H).map fun i => bankW20 s (L + i))
    have h3 := counts_chainG (storeWire20 s) (fun i => if i = 0 then a0P20 s + L - 1 else bankW20 s (L + i - 1))
      (⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx (storeWire20 s (H + 1)) 1557, .x 1557] 0 0 0 2) 0 (H + 1)
    have h4 := counts_xsG ((List.range H).map fun i => bankW20 s (L + i)).reverse
    have h5 : Counts [.x (a0P20 s + L - 1), .x 1558, .make 1556 1557 1558, .x 1558] 0 1 0 4 := ⟨rfl, rfl, rfl, rfl⟩
    have h6 := counts_xsG ((List.range (L + 1)).map (b0P20 s - 1 + ·))
    have h7 := counts_chainG (1558 + ·) (b0P20 s - 1 + ·)
      (⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx (1558 + (L + 1)) 1556, .x 1556] 0 0 0 2) 0 (L + 1)
    have h8 := counts_xsG ((List.range (L + 1)).map (b0P20 s - 1 + ·)).reverse
    have h9 : Counts [.x 1558] 0 0 0 1 := ⟨rfl, rfl, rfl, rfl⟩
    have a1 := h1.app h2
    have a2 := a1.app h3
    have a3 := a2.app h4
    have a4 := a3.app h5
    have a5 := a4.app h6
    have a6 := a5.app h7
    have a7 := a6.app h8
    have a8 := a7.app h9
    exact a8.congr (by simp) (by simp [H, L]; omega) (by simp [H, L]; omega) (by simp [H, L]; omega)
  have c15 : Counts (leaveLowClose20 s) (lowsP20 s + 1) 0 0 (4 * lowsP20 s + 24) := by
    unfold leaveLowClose20
    have h1 := counts_xsG ((List.range 20).map (s + 16 + ·))
    have h2 := counts_mapG (List.range (lowsP20 s + 1)) (fun i => .cx (e0P20 s + 5) (b0P20 s - 1 + i))
      false false false (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    have h3 := counts_flatCswap (lowsP20 s + 1) (s + 35) (fun i => b0P20 s - 1 + i) (fun i => a0P20 s - 1 + i)
    exact ((h1.app h2).app h3).congr (by simp) (by simp) (by simp) (by simp; omega)
  have c16 : Counts (leaveClose20 s) 0 0 1 (3 * nextWp20 s + 35) := by
    unfold leaveClose20 closeFlag20
    have h1 := Shadow7.counts_parityG (e0P20 s + 7) (e0P20 s + 4) 1556 (closeRecs20 s)
    have hrlen : (closeRecs20 s).length = 10 := by simp [closeRecs20]
    rw [hrlen] at h1
    have h2 := counts_swapsG (movesP20 s)
    have hlen : (movesP20 s).length = nextWp20 s + 4 := by simp [movesP20]; omega
    rw [hlen] at h2
    exact (h1.app h2).congr (by simp) (by simp) (by simp) (by simp; omega)
  exact ((((((((c8.app c9).app c10).app c11).app c12).app c13).app c14).app c15).app c16).congr
    (by omega) (by omega) (by omega) (by omega)

theorem leave20_counts (j : Fin 9) :
    let s := start20 j
    toffoliCount (leaveP20 j) = wpP20 s + liveW20 s + 3 * lowsP20 s + 135 + barrel20T s false ∧
    toffoliCount (leaveInvP20 j) = wpP20 s + liveW20 s + 2 * lowsP20 s + 177 + barrel20T s true ∧
    measurementCount (leaveP20 j) = wpP20 s + liveW20 s + lowsP20 s + 123 + barrel20M s false ∧
    measurementCount (leaveInvP20 j) = wpP20 s + liveW20 s + 2 * lowsP20 s + 81 + barrel20M s true ∧
    gateSlots (leaveP20 j) = 6 * wpP20 s + 5 * liveW20 s + 10 * lowsP20 s + 864 + 3 * nextWp20 s + barrel20Slots s false ∧
    gateSlots (leaveInvP20 j) = 6 * wpP20 s + 5 * liveW20 s + 11 * lowsP20 s + 822 + 3 * nextWp20 s + barrel20Slots s true := by
  have hg := geom20_facts j
  have hnw : ∀ k : Fin 9, 74 ≤ nextWp20 (start20 k) := by decide
  obtain ⟨bt1, bt2, bm1, bm2, bs1, bs2⟩ := (counts_leaveBefore20 (start20 j) (by omega)).programs
  obtain ⟨at1, at2, am1, am2, as1, as2⟩ :=
    (counts_leaveAfter20 (start20 j) (by omega) (by omega) hg.2.2.2.2.2.2.2.2.2.2.2.2.1 (by have := hnw j; omega)).programs
  obtain ⟨f1, f2, f3⟩ := barrel20_metrics j false
  obtain ⟨g1, g2, g3⟩ := barrel20_metrics j true
  dsimp only
  simp only [leaveP20, leaveInvP20, toffoliCount_append, measurementCount_append, gateSlots_append,
    bt1, bt2, bm1, bm2, bs1, bs2, at1, at2, am1, am2, as1, as2, f1, f2, f3, g1, g2, g3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ### Fast algebraic physicality & domain coverage of `leaveP20` / `leaveInvP20` -/

private theorem proper_flipGate (g : Gate) (h : proper g = true) : proper (flipGate g) = true := by
  cases g <;> exact h

private theorem wires_flipGate (g : Gate) : (flipGate g).wires = g.wires := by
  cases g <;> rfl

private theorem proper_uncomputeOps {gs : List Gate} (h : Proper gs) : Proper (uncomputeOps gs) := by
  intro g hg
  rw [uncomputeOps, List.mem_reverse, List.mem_map] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact proper_flipGate x (h x hx)

private theorem allW_uncomputeOps {P : Wire → Prop} {gs : List Gate} (h : AllW P gs) : AllW P (uncomputeOps gs) := by
  intro g hg q hq
  rw [uncomputeOps, List.mem_reverse, List.mem_map] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  rw [wires_flipGate] at hq
  exact h x hx q hq

private theorem fixed20_ok : ∀ j : Fin 9,
    let s := start20 j
    let h := sbP20 s
    (fix0P20 s h ++ leaveFix1_20 s ++ fix2P20 s h ++ leaveFix3_20 h ++ leaveFix4_20 s ++
     leaveFix5Move20 s ++ fix8P20 s ++ fix10P20 s).all
      (fun g => proper g && g.wires.all WindowCovered.domainW) = true := by
  decide +kernel

private theorem next_geom20 : ∀ j : Fin 9,
    let s := start20 j
    1650 ≤ nextE0_20 s ∧ nextE0_20 s ≤ 1732 ∧
    74 ≤ nextWp20 s ∧ nextWp20 s ≤ 114 ∧
    lowsP20 s + nextWp20 s ≤ wpP20 s + 22 ∧
    bTopP (s + 20) ≤ 1043 ∧
    850 ≤ bTopP (s + 20) + 3 - nextWp20 s ∧
    bTopP s ≤ 1043 ∧
    liveW20 s - lowsP20 s + 1579 < e0P20 s ∧
    a0P20 s + 21 ≤ 529 ∧
    56 ≤ a0P20 s - 1 ∧
    b0P20 s + lowsP20 s ≤ 1045 ∧
    e0P20 s ≠ nextE0_20 s ∧
    e0P20 s + 5 ≠ nextE0_20 s + 5 ∧
    e0P20 s + 3 ≠ nextE0_20 s + 6 ∧
    e0P20 s + 7 ≠ nextE0_20 s + 7 ∧
    e0P20 s + 6 ≠ nextE0_20 s + 8 := by
  decide +kernel

private theorem domA {q : Wire} (h1 : 56 ≤ q) (h2 : q ≤ 529) : WindowCovered.domainW q = true := by
  rw [WindowCovered.dom_iff]; exact Or.inl ⟨h1, h2⟩

private theorem domB {q : Wire} (h1 : 786 ≤ q) (h2 : q ≤ 1045) : WindowCovered.domainW q = true := by
  rw [WindowCovered.dom_iff]; exact Or.inr (Or.inl ⟨h1, h2⟩)

private theorem domC {q : Wire} (h1 : 1556 ≤ q) (h2 : q ≤ 1812) : WindowCovered.domainW q = true := by
  rw [WindowCovered.dom_iff]; exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))

theorem leaveBefore20_ok (j : Fin 9) :
    Proper (leaveBefore20 (start20 j)) ∧
    AllW (fun q => WindowCovered.domainW q = true) (leaveBefore20 (start20 j)) := by
  have hg := geom20_facts j
  have hn := next_geom20 j
  have hf := fixed20_ok j
  have hfp : ∀ g ∈ fix0P20 (start20 j) (sbP20 (start20 j)) ++ leaveFix1_20 (start20 j) ++
      fix2P20 (start20 j) (sbP20 (start20 j)) ++ leaveFix3_20 (sbP20 (start20 j)) ++
      leaveFix4_20 (start20 j) ++ leaveFix5Move20 (start20 j),
      proper g = true ∧ ∀ q ∈ g.wires, WindowCovered.domainW q = true := by
    intro g hg'
    have hmem := List.all_eq_true.mp hf g (List.mem_append_left _ (List.mem_append_left _ hg'))
    obtain ⟨hp, hd⟩ := Bool.and_eq_true_iff.mp hmem
    exact ⟨hp, fun q hq => List.all_eq_true.mp hd q hq⟩
  have hadj_p : Proper (leaveAdjust20 (start20 j)) := by
    unfold leaveAdjust20 leaveAdjustCore20
    refine proper_append (fun g hg' => by simp only [List.mem_singleton] at hg'; subst hg'; simp [proper]) ?_
    refine proper_adjustG _ _ _ _ ?_ ?_ ?_
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
      have bc := bank20_cases j (i := i) (by omega)
      refine ⟨?_, ?_, ?_⟩
      · intro hmem; obtain ⟨k, hk, heq⟩ := List.mem_map.mp hmem; rw [List.mem_range] at hk
        rcases pool20_cases j k with ⟨_, ep⟩ | ⟨_, ep⟩ <;>
          rcases bc with ⟨_, eb⟩ | ⟨_, _, eb, _, _⟩ | ⟨_, eb, _, _⟩ <;>
          (rw [ep, eb] at heq; unfold Wire at *; omega)
      · rcases bc with ⟨_, eb⟩ | ⟨_, _, eb, _, _⟩ | ⟨_, eb, _, _⟩ <;> (rw [eb]; unfold Wire at *; omega)
      · rcases bc with ⟨_, eb⟩ | ⟨_, _, eb, _, _⟩ | ⟨_, eb, _, _⟩ <;> (rw [eb]; unfold Wire at *; omega)
    · intro hmem; obtain ⟨k, hk, heq⟩ := List.mem_map.mp hmem; rw [List.mem_range] at hk
      rcases pool20_cases j k with ⟨_, ep⟩ | ⟨_, ep⟩ <;> (rw [ep] at heq; unfold Wire at *; omega)
    · exact List.Nodup.map_on (fun a _ b _ e => by
        rcases pool20_cases j a with ⟨_, ea⟩ | ⟨_, ea⟩ <;>
          rcases pool20_cases j b with ⟨_, eb⟩ | ⟨_, eb⟩ <;>
          (rw [ea, eb] at e; unfold Wire at *; omega)) List.nodup_range
  have hadj_w : AllW (fun q => WindowCovered.domainW q = true) (leaveAdjust20 (start20 j)) := by
    unfold leaveAdjust20 leaveAdjustCore20
    refine allW_append (fun g hg' q hq => by
      simp only [List.mem_singleton] at hg'; subst hg'
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> exact domC (by unfold Wire; omega) (by unfold Wire; omega)) ?_
    refine allW_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_)
      (domC (by unfold Wire; omega) (by unfold Wire; omega))
      (domC (by decide) (by decide))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
      rcases bank20_cases j (i := i) (by omega) with ⟨_, e⟩ | ⟨_, _, e, _, _⟩ | ⟨_, e, _, _⟩
      · rw [e]; exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      · have hb0 : b0P20 (start20 j) = 787 + sbP20 (start20 j) := rfl
        exact domB (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      · exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk
      rcases pool20_cases j k with ⟨_, e⟩ | ⟨_, e⟩ <;>
        (rw [e]; exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega))
  unfold leaveBefore20
  exact ⟨proper_append (fun g hg' => (hfp g hg').1) hadj_p,
    allW_append (fun g hg' => (hfp g hg').2) hadj_w⟩

private theorem events20_ok : ∀ j : Fin 9,
    (closeFlag20 (start20 j)).all
      (fun g => proper g && g.wires.all WindowCovered.domainW) = true := by
  decide +kernel

private theorem moves20_ok : ∀ j : Fin 9,
    (movesP20 (start20 j)).all (fun p =>
      decide (p.1 ≠ p.2) && WindowCovered.domainW p.1 && WindowCovered.domainW p.2) = true := by
  decide +kernel

theorem leaveAfter20_ok (j : Fin 9) :
    Proper (leaveAfter20 (start20 j)) ∧
    AllW (fun q => WindowCovered.domainW q = true) (leaveAfter20 (start20 j)) := by
  have hg := geom20_facts j
  have hn := next_geom20 j
  have hf := fixed20_ok j
  have ha0 : a0P20 (start20 j) = start20 j + sbP20 (start20 j) + 37 := rfl
  have hb0 : b0P20 (start20 j) = 787 + sbP20 (start20 j) := rfl
  have bankDom : ∀ i < wpP20 (start20 j) + 20, WindowCovered.domainW (bankW20 (start20 j) i) = true := by
    intro i hi
    rcases bank20_cases j (i := i) hi with ⟨_, e⟩ | ⟨_, _, e, _, _⟩ | ⟨_, e, _, _⟩
    · rw [e]; exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    · exact domB (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    · exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega)
  have hfixed_mem : ∀ g ∈ fix8P20 (start20 j) ++ fix10P20 (start20 j) ++
      (leaveFix5Pre20 (start20 j)).drop 11 ++ leaveFix5Post20 (start20 j) ++ leaveFix4_20 (start20 j),
      proper g = true ∧ ∀ q ∈ g.wires, WindowCovered.domainW q = true := by
    intro g hg'
    have hmem : g ∈ fix0P20 (start20 j) (sbP20 (start20 j)) ++ leaveFix1_20 (start20 j) ++
        fix2P20 (start20 j) (sbP20 (start20 j)) ++ leaveFix3_20 (sbP20 (start20 j)) ++
        leaveFix4_20 (start20 j) ++ leaveFix5Move20 (start20 j) ++
        fix8P20 (start20 j) ++ fix10P20 (start20 j) := by
      simp only [List.mem_append] at hg' ⊢
      rcases hg' with (((h | h) | h) | h) | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
      · exact Or.inl (Or.inl (Or.inr (by unfold leaveFix5Move20; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_of_mem_drop h)))))
      · exact Or.inl (Or.inl (Or.inr (by unfold leaveFix5Move20; exact List.mem_append_right _ h)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    obtain ⟨hp, hd⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hf g hmem)
    exact ⟨hp, fun q hq => List.all_eq_true.mp hd q hq⟩
  have h8 : Proper (fix8P20 (start20 j)) ∧ AllW (fun q => WindowCovered.domainW q = true) (fix8P20 (start20 j)) :=
    ⟨fun g h => (hfixed_mem g (by simp [h])).1, fun g h => (hfixed_mem g (by simp [h])).2⟩
  have h10 : Proper (fix10P20 (start20 j)) ∧ AllW (fun q => WindowCovered.domainW q = true) (fix10P20 (start20 j)) :=
    ⟨fun g h => (hfixed_mem g (by simp [h])).1, fun g h => (hfixed_mem g (by simp [h])).2⟩
  have h11 : Proper (leaveFix11_20 (start20 j)) ∧ AllW (fun q => WindowCovered.domainW q = true) (leaveFix11_20 (start20 j)) :=
    ⟨proper_uncomputeOps (fun g h => (hfixed_mem g (by simp only [List.mem_append] at h ⊢; tauto)).1),
     allW_uncomputeOps (fun g h => (hfixed_mem g (by simp only [List.mem_append] at h ⊢; tauto)).2)⟩
  have h12 : Proper (leaveFix12_20 (start20 j)) ∧ AllW (fun q => WindowCovered.domainW q = true) (leaveFix12_20 (start20 j)) :=
    ⟨proper_uncomputeOps (fun g h => (hfixed_mem g (by simp [h])).1),
     allW_uncomputeOps (fun g h => (hfixed_mem g (by simp [h])).2)⟩
  have h9 : Proper (leaveJoinMove20 (start20 j)) ∧ AllW (fun q => WindowCovered.domainW q = true) (leaveJoinMove20 (start20 j)) := by
    unfold leaveJoinMove20
    have hkp := KeptParity20.placed20_ok j
    have hkept_p : Proper (KeptParity20.placed20 (start20 j)) :=
      fun g hg' => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hkp g hg')).1
    have hkept_w : AllW (fun q => WindowCovered.domainW q = true) (KeptParity20.placed20 (start20 j)) :=
      fun g hg' q hq => List.all_eq_true.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hkp g hg')).2 q hq
    have hwm_p : Proper (wordGM 1624 (columnsP20 (start20 j))) := by
      refine proper_wordGM 1624 _ (fun r hr => ?_)
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr; rw [List.mem_range] at hi
      have bc := bank20_cases j (i := i) (by omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro w hw; dsimp only at hw; split at hw
        · cases hw; have tr := tagsP20_getD_range (k := i) (by omega); unfold Wire at *; omega
        · cases hw
      · dsimp only; unfold Wire; omega
      · dsimp only; rcases bc with ⟨_, e⟩ | ⟨_, _, e, _, _⟩ | ⟨_, e, _, _⟩ <;> (rw [e]; unfold Wire at *; omega)
      · dsimp only; rcases bc with ⟨_, e⟩ | ⟨_, _, e, _, _⟩ | ⟨_, e, _, _⟩ <;> (rw [e]; unfold Wire at *; omega)
    have hwm_w : AllW (fun q => WindowCovered.domainW q = true) (wordGM 1624 (columnsP20 (start20 j))) := by
      refine allW_wordGM _ (domC (by decide) (by decide)) _ (fun r hr => ?_)
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr; rw [List.mem_range] at hi
      refine ⟨?_, domA (by dsimp only; unfold Wire at *; omega) (by dsimp only; unfold Wire at *; omega), bankDom i (by omega)⟩
      intro w hw; dsimp only at hw; split at hw
      · cases hw; have tr := tagsP20_getD_range (k := i) (by omega)
        exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      · cases hw
    exact ⟨proper_append hkept_p hwm_p, allW_append hkept_w hwm_w⟩
  have h13 : Proper (leaveLowStore20 (start20 j)) ∧ AllW (fun q => WindowCovered.domainW q = true) (leaveLowStore20 (start20 j)) := by
    unfold leaveLowStore20
    have p1 : Proper [.cx (e0P20 (start20 j) + 3) 1560, .cx 1559 1560, .pop (e0P20 (start20 j) + 3) (e0P20 (start20 j) + 4) 1559] := by
      intro g hg'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl <;> (simp only [proper, decide_eq_true_eq]; unfold Wire; omega)
    have p2 : Proper ((List.range (lowsP20 (start20 j))).map fun i => .make 1556 (a0P20 (start20 j) + i) (b0P20 (start20 j) + i)) := by
      intro g hg'; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg'; rw [List.mem_range] at hi
      simp only [proper, decide_eq_true_eq]; unfold Wire; omega
    have p4 : Proper (addG ((List.range (lowsP20 (start20 j))).map (b0P20 (start20 j) + ·))
        ((List.range (lowsP20 (start20 j) - 1)).map (1559 + ·)) 1558) := by
      refine proper_addG _ _ _ (fun y hy => ?_) ?_ ?_
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
        refine ⟨fun hm => ?_, by unfold Wire; omega⟩
        obtain ⟨k, hk, heq⟩ := List.mem_map.mp hm; rw [List.mem_range] at hk; unfold Wire at *; omega
      · intro hm; obtain ⟨k, hk, heq⟩ := List.mem_map.mp hm; rw [List.mem_range] at hk; unfold Wire at *; omega
      · exact List.Nodup.map_on (fun a _ b _ e => by unfold Wire at *; omega) List.nodup_range
    have p6 : Proper [.pop (b0P20 (start20 j) - 1) 1557 1558, .cx (a0P20 (start20 j) - 1) 1557, .x 1557] := by
      intro g hg'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl
      · simp only [proper, decide_eq_true_eq]; unfold Wire; omega
      · simp only [proper, decide_eq_true_eq]; unfold Wire; omega
      · rfl
    have wbs : ∀ y ∈ (List.range (lowsP20 (start20 j))).map (b0P20 (start20 j) + ·), WindowCovered.domainW y = true := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
      exact domB (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    have wcs : ∀ c ∈ (List.range (lowsP20 (start20 j) - 1)).map (1559 + ·), WindowCovered.domainW c = true := by
      intro c hc; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    refine ⟨proper_append (proper_append (proper_append (proper_append (proper_append p1 p2) (proper_xsG _)) p4) (proper_xsG _)) p6,
      allW_append (allW_append (allW_append (allW_append (allW_append ?_ ?_) (allW_xsG _ wbs))
        (allW_addG _ _ _ wbs wcs (domC (by decide) (by decide)))) (allW_xsG _ wbs)) ?_⟩
    · intro g hg' q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl <;>
        (simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq;
         rcases hq with rfl | rfl | rfl <;> exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega))
    · intro g hg' q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg'; rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact domC (by decide) (by decide)
      · exact domA (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      · exact domB (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    · intro g hg' q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl
      · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact domB (by unfold Wire at *; omega) (by unfold Wire at *; omega)
        · exact domC (by decide) (by decide)
        · exact domC (by decide) (by decide)
      · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact domA (by unfold Wire at *; omega) (by unfold Wire at *; omega)
        · exact domC (by decide) (by decide)
      · simp only [Gate.wires, List.mem_singleton] at hq; subst hq; exact domC (by decide) (by decide)
  have h14 : Proper (leaveStoreMapped20 (start20 j)) ∧ AllW (fun q => WindowCovered.domainW q = true) (leaveStoreMapped20 (start20 j)) := by
    unfold leaveStoreMapped20
    let L := lowsP20 (start20 j)
    let H := liveW20 (start20 j) - L
    have hsw : ∀ i ≤ H + 1, (1558 ≤ storeWire20 (start20 j) i ∧ storeWire20 (start20 j) i ≤ 1602) ∨
        (1623 ≤ storeWire20 (start20 j) i ∧ storeWire20 (start20 j) i < e0P20 (start20 j)) := by
      intro i hi
      unfold storeWire20
      by_cases h1 : 1558 + i < 1603
      · left; dsimp only; rw [if_pos h1, if_pos (by omega)]; unfold Wire; omega
      · right; dsimp only; rw [if_neg h1, if_pos (by omega)]; unfold Wire; omega
    have hsw_inj : ∀ i < H + 1, storeWire20 (start20 j) i ≠ storeWire20 (start20 j) (i + 1) := by
      intro i hi e
      unfold storeWire20 at e; dsimp only at e
      split_ifs at e <;> (unfold Wire at *; omega)
    have hseq_ne : ∀ i < H + 1,
        (if i = 0 then a0P20 (start20 j) + L - 1 else bankW20 (start20 j) (L + i - 1)) ≠ storeWire20 (start20 j) (i + 1) := by
      intro i hi
      have s2 := hsw (i + 1) (by omega)
      by_cases hz : i = 0
      · subst hz; simp only [if_true]; unfold Wire at *; omega
      · simp only [hz, if_false]
        have bc := bank20_cases j (i := L + i - 1) (by omega)
        rcases bc with ⟨_, eb⟩ | ⟨_, _, eb, _, _⟩ | ⟨_, eb, _, _⟩ <;> (rw [eb]; unfold Wire at *; omega)
    have hc1_p : Proper (chainG (storeWire20 (start20 j))
        (fun i => if i = 0 then a0P20 (start20 j) + L - 1 else bankW20 (start20 j) (L + i - 1))
        [.cx (storeWire20 (start20 j) (H + 1)) 1557, .x 1557] 0 (H + 1)) := by
      refine proper_chainG _ _ _ (fun g hg' => ?_) 0 (H + 1) (fun i _ hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl
        · have sH := hsw (H + 1) le_rfl; simp only [proper, decide_eq_true_eq]; unfold Wire at *; omega
        · rfl
      · exact ⟨hsw_inj i (by omega), hseq_ne i (by omega)⟩
    have hc2_p : Proper (chainG (1558 + ·) (b0P20 (start20 j) - 1 + ·)
        [.cx (1558 + (L + 1)) 1556, .x 1556] 0 (L + 1)) := by
      refine proper_chainG _ _ _ (fun g hg' => ?_) 0 (L + 1) (fun i _ hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl
        · simp only [proper, decide_eq_true_eq]; unfold Wire; omega
        · rfl
      · exact ⟨by unfold Wire; omega, by unfold Wire; omega⟩
    have p1 : Proper [.x 1558, .x (a0P20 (start20 j) + L - 1)] := fun g hg' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'; rcases hg' with rfl | rfl <;> rfl
    have p5 : Proper [.x (a0P20 (start20 j) + L - 1), .x 1558, .make 1556 1557 1558, .x 1558] := fun g hg' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl | rfl <;> rfl
    have p9 : Proper [.x 1558] := fun g hg' => by simp only [List.mem_singleton] at hg'; subst hg'; rfl
    have whi : ∀ y ∈ (List.range H).map (fun i => bankW20 (start20 j) (L + i)), WindowCovered.domainW y = true := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bankDom (L + i) (by omega)
    have ws2 : ∀ y ∈ (List.range (L + 1)).map (b0P20 (start20 j) - 1 + ·), WindowCovered.domainW y = true := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
      exact domB (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    have wsw : ∀ i ≤ H + 1, WindowCovered.domainW (storeWire20 (start20 j) i) = true := fun i hi => by
      have st1 := hsw i hi; exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    refine ⟨proper_append (proper_append (proper_append (proper_append (proper_append (proper_append (proper_append
      (proper_append p1 (proper_xsG _)) hc1_p) (proper_xsG _)) p5) (proper_xsG _)) hc2_p) (proper_xsG _)) p9,
      allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append ?_
        (allW_xsG _ whi)) ?_) (allW_xsG _ (fun y hy => whi y (List.mem_reverse.mp hy)))) ?_)
        (allW_xsG _ ws2)) ?_) (allW_xsG _ (fun y hy => ws2 y (List.mem_reverse.mp hy)))) ?_⟩
    · intro g hg' q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl
      · simp only [Gate.wires, List.mem_singleton] at hq; subst hq; exact domC (by decide) (by decide)
      · simp only [Gate.wires, List.mem_singleton] at hq; subst hq; exact domA (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    · refine allW_chainG _ _ _ (fun g hg' q hq => ?_) 0 (H + 1) (fun i _ hi => wsw i (by omega)) (fun i _ hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl
        · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · exact wsw (H + 1) le_rfl
          · exact domC (by decide) (by decide)
        · simp only [Gate.wires, List.mem_singleton] at hq; subst hq; exact domC (by decide) (by decide)
      · by_cases hz : i = 0
        · subst hz; simp only [if_true]; exact domA (by unfold Wire at *; omega) (by unfold Wire at *; omega)
        · simp only [hz, if_false]; exact bankDom (L + i - 1) (by omega)
    · intro g hg' q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl | rfl
      · simp only [Gate.wires, List.mem_singleton] at hq; subst hq; exact domA (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      · simp only [Gate.wires, List.mem_singleton] at hq; subst hq; exact domC (by decide) (by decide)
      · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact domC (by decide) (by decide)
      · simp only [Gate.wires, List.mem_singleton] at hq; subst hq; exact domC (by decide) (by decide)
    · refine allW_chainG _ _ _ (fun g hg' q hq => ?_) 0 (L + 1)
        (fun i _ hi => domC (by unfold Wire at *; omega) (by unfold Wire at *; omega))
        (fun i _ hi => domB (by unfold Wire at *; omega) (by unfold Wire at *; omega))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl <;>
        (simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq;
         rcases hq with rfl | rfl <;> exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega))
    · intro g hg' q hq; simp only [List.mem_singleton] at hg'; subst hg'
      simp only [Gate.wires, List.mem_singleton] at hq; subst hq; exact domC (by decide) (by decide)
  have h15 : Proper (leaveLowClose20 (start20 j)) ∧ AllW (fun q => WindowCovered.domainW q = true) (leaveLowClose20 (start20 j)) := by
    unfold leaveLowClose20
    have p2 : Proper ((List.range (lowsP20 (start20 j) + 1)).map fun i => .cx (e0P20 (start20 j) + 5) (b0P20 (start20 j) - 1 + i)) := by
      intro g hg'; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg'; rw [List.mem_range] at hi
      simp only [proper, decide_eq_true_eq]; unfold Wire; omega
    have p3 : Proper ((List.range (lowsP20 (start20 j) + 1)).flatMap fun i => cswapG (start20 j + 35) (b0P20 (start20 j) - 1 + i) (a0P20 (start20 j) - 1 + i)) := by
      intro g hg'; obtain ⟨i, hi, hg''⟩ := List.mem_flatMap.mp hg'; rw [List.mem_range] at hi
      exact proper_cswapG (by unfold Wire; omega) (by unfold Wire; omega) g hg''
    refine ⟨proper_append (proper_append (proper_xsG _) p2) p3,
      allW_append (allW_append (allW_xsG _ ?_) ?_) ?_⟩
    · intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
      exact domA (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    · intro g hg' q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg'; rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      · exact domB (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    · intro g hg' q hq; obtain ⟨i, hi, hg''⟩ := List.mem_flatMap.mp hg'; rw [List.mem_range] at hi
      simp only [cswapG, List.mem_cons, List.not_mem_nil, or_false] at hg''
      rcases hg'' with rfl | rfl | rfl
      · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact domA (by unfold Wire at *; omega) (by unfold Wire at *; omega)
        · exact domB (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact domA (by unfold Wire at *; omega) (by unfold Wire at *; omega)
        · exact domB (by unfold Wire at *; omega) (by unfold Wire at *; omega)
        · exact domA (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact domA (by unfold Wire at *; omega) (by unfold Wire at *; omega)
        · exact domB (by unfold Wire at *; omega) (by unfold Wire at *; omega)
  have h16 : Proper (leaveClose20 (start20 j)) ∧ AllW (fun q => WindowCovered.domainW q = true) (leaveClose20 (start20 j)) := by
    unfold leaveClose20
    have hev := events20_ok j
    have hmv := moves20_ok j
    refine ⟨proper_append (fun g hg' => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hev g hg')).1)
      (proper_swapsG _ (fun p hp => of_decide_eq_true (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hmv p hp)).1).1)),
      allW_append (fun g hg' q hq => List.all_eq_true.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hev g hg')).2 q hq)
      (allW_swapsG _ (fun p hp => ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hmv p hp)).1).2,
        (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hmv p hp)).2⟩))⟩
  unfold leaveAfter20
  exact ⟨proper_append (proper_append (proper_append (proper_append (proper_append (proper_append (proper_append
    (proper_append h8.1 h9.1) h10.1) h11.1) h12.1) h13.1) h14.1) h15.1) h16.1,
    allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append
    (allW_append h8.2 h9.2) h10.2) h11.2) h12.2) h13.2) h14.2) h15.2) h16.2⟩

theorem leave20_phys (j : Fin 9) :
    GatePhysical (leaveP20 j) ∧ GatePhysical (leaveInvP20 j) := by
  have hb := physical_of_proper _ (leaveBefore20_ok j).1
  have ha := physical_of_proper _ (leaveAfter20_ok j).1
  rw [leaveP20, leaveInvP20]
  exact ⟨WindowPhysicalW.appP (WindowPhysicalW.appP hb.1 (barrel20_phys j false)) ha.1,
    WindowPhysicalW.appP (WindowPhysicalW.appP ha.2 (barrel20_phys j true)) hb.2⟩

theorem leave20_cov (j : Fin 9) :
    WindowCovered.CoveredW (leaveP20 j) ∧ WindowCovered.CoveredW (leaveInvP20 j) := by
  obtain ⟨bf, bi⟩ := allW_programs (leaveBefore20_ok j).2
  obtain ⟨af, ai⟩ := allW_programs (leaveAfter20_ok j).2
  rw [leaveP20, leaveInvP20]
  exact ⟨WindowCovered.appW (WindowCovered.appW bf (barrel20_cov j false)) af,
    WindowCovered.appW (WindowCovered.appW ai (barrel20_cov j true)) bi⟩

/-! ### Stage 6B3: `beforeRow20` / `afterRow20` / `leaveP20Red` (`LeaveReductions` parity on `k = 20`) -/

def firstRows20 (s h : Nat) : List Gate := (fix0P20 s h).take 65

def cell21_20 (s h : Nat) : List Gate :=
  [.cx (s + h + 57) (h + 807), .ccx (s + 35) (h + 807) (s + h + 57), .cx (s + h + 57) (h + 807)]

def shortCell20 (s h : Nat) : List Gate :=
  let a := s + h + 57
  let b := h + 807
  let z := h + 1584
  [.cx a b, .cx b a, .cx z a, .pop (s + 35) b a, .cx z a, .cx b a, .cx a b]

def headEnd20 (s h : Nat) : List Gate := [.cx (s + h + 58) (h + 808)]

def headA1_20 (s : Nat) : List Gate :=
  let h := sbP20 s
  (fix0P20 s h).drop 70 ++ leaveFix1_20 s ++ fix2P20 s h

def headC0_20 (s : Nat) : List Gate :=
  let h := sbP20 s
  [.cx (h + 1582) 1560, .cx 1559 1560] ++ leaveFix4_20 s ++ leaveFix5Pre20 s

def headC1_20 (s : Nat) : List Gate :=
  rowGates (e0P20 s + 6) ((moveRows20 s).drop 1) ++ leaveFix5Post20 s ++ leaveAdjust20 s

def beforeRow20 (s : Nat) : List Gate :=
  let h := sbP20 s
  firstRows20 s h ++ shortCell20 s h ++ headEnd20 s h ++
  [.pop (s + 35) (h + 808) (s + h + 58)] ++ headA1_20 s ++
  [.cx (h + 1583) 1559] ++ headC0_20 s ++
  [.make (tagsP20.getD 0 0) (a0P20 s + 0) (e0P20 s + 6), .cx (e0P20 s + 6) (a0P20 s + 0)] ++
  headC1_20 s

def colsC20 (s : Nat) : List HighBankJoin.Column :=
  (List.range 21).map fun i =>
    ⟨decide (i < lowsP20 s), some (tagsP20.getD i 0), a0P20 s + i, bankW20 s i⟩

def tailD0_20 (s : Nat) : List Gate :=
  fix8P20 s ++ KeptParity20.placed20 s ++ CRTBarrel.wordPre 1624 (colsC20 s)

def tailD1_20 (s : Nat) : List Gate :=
  CRTBarrel.wordPost 1624 (colsC20 s) ++ fix10P20 s ++ leaveFix11_20 s ++ leaveFix12_20 s ++
  [.cx (e0P20 s + 3) 1560, .cx 1559 1560]

def lowRest20_pub (s : Nat) : List Gate :=
  let L := lowsP20 s
  let bs := (List.range L).map (b0P20 s + ·)
  ((List.range L).map fun i => .make 1556 (a0P20 s + i) (b0P20 s + i)) ++ xsG bs ++
  addG bs ((List.range (L - 1)).map (1559 + ·)) 1558 ++ xsG bs ++
  [.pop (b0P20 s - 1) 1557 1558, .cx (a0P20 s - 1) 1557, .x 1557]

def storeHead20 (s : Nat) : List Gate :=
  let L := lowsP20 s
  let top := a0P20 s + L - 1
  let H := liveW20 s - L
  [.x 1558, .x top] ++ xsG ((List.range H).map fun i => bankW20 s (L + i))

def tailE0_20 (s : Nat) : List Gate := lowRest20_pub s ++ storeHead20 s

def chainMid20 (s : Nat) : List Gate :=
  let L := lowsP20 s
  let top := a0P20 s + L - 1
  let H := liveW20 s - L
  chainG (storeWire20 s) (fun i => if i = 0 then top else bankW20 s (L + i - 1))
    [.cx (storeWire20 s (H + 1)) 1557, .x 1557] 1 H

def tailE1_20 (s : Nat) : List Gate :=
  let L := lowsP20 s
  let top := a0P20 s + L - 1
  let H := liveW20 s - L
  let hi := (List.range H).map fun i => bankW20 s (L + i)
  let seq2 := (List.range (L + 1)).map (b0P20 s - 1 + ·)
  xsG hi.reverse ++ [.x top, .x 1558, .make 1556 1557 1558, .x 1558] ++ xsG seq2 ++
  chainG (1558 + ·) (b0P20 s - 1 + ·) [.cx (1558 + (L + 1)) 1556, .x 1556] 0 (L + 1) ++
  xsG seq2.reverse ++ [.x 1558] ++ leaveLowClose20 s ++ leaveClose20 s

def afterRow20 (s : Nat) : List Gate :=
  let top := a0P20 s + lowsP20 s - 1
  tailD0_20 s ++ tailD1_20 s ++ [.cx (e0P20 s + 4) 1559] ++ tailE0_20 s ++
  [.cx top 1559] ++ chainMid20 s ++ [.cx top 1559] ++ tailE1_20 s

def leaveP20Red (j : Fin 9) : Program :=
  GateMirror.forward (beforeRow20 (start20 j)) ++ barrel20 (start20 j) false ++
    GateMirror.forward (afterRow20 (start20 j))

def leaveInvP20Red (j : Fin 9) : Program :=
  inverse (afterRow20 (start20 j)) ++ barrel20 (start20 j) true ++
    inverse (beforeRow20 (start20 j))

theorem fix0P20_split5 (s h : Nat) :
    fix0P20 s h = firstRows20 s h ++ (cell21_20 s h ++ (headEnd20 s h ++
      ([.ccx (s + 35) (h + 808) (s + h + 58)] ++ (fix0P20 s h).drop 70))) := rfl

theorem leaveBefore20_split4 (s : Nat) :
    let h := sbP20 s
    leaveBefore20 s = firstRows20 s h ++ (cell21_20 s h ++ (headEnd20 s h ++
      ([.ccx (s + 35) (h + 808) (s + h + 58)] ++ (headA1_20 s ++
        ([.make (h + 1582) (h + 1583) 1559] ++ (headC0_20 s ++
          ([.cx (a0P20 s + 0) (e0P20 s + 6), .ccx (tagsP20.getD 0 0) (e0P20 s + 6) (a0P20 s + 0),
            .cx (a0P20 s + 0) (e0P20 s + 6)] ++ headC1_20 s))))))) := by
  have h5 : rowGates (e0P20 s + 6) (moveRows20 s) =
      [.cx (a0P20 s + 0) (e0P20 s + 6), .ccx (tagsP20.getD 0 0) (e0P20 s + 6) (a0P20 s + 0),
       .cx (a0P20 s + 0) (e0P20 s + 6)] ++ rowGates (e0P20 s + 6) ((moveRows20 s).drop 1) := rfl
  unfold leaveBefore20 leaveFix3_20 leaveFix5Move20 headA1_20 headC0_20 headC1_20
  dsimp only
  conv_lhs => rw [fix0P20_split5 s (sbP20 s), h5]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

private theorem columnsP20_snoc (s : Nat) (hL : lowsP20 s ≤ 21) :
    columnsP20 s = colsC20 s ++ [⟨false, none, a0P20 s + 21, bankW20 s 21⟩] := by
  unfold columnsP20 colsC20
  rw [show (22 : Nat) = 21 + 1 from rfl, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi; simp [hi]
  · simp [Nat.not_lt.mpr hL]

theorem storeWire20_01 (s : Nat) : storeWire20 s 0 = 1558 ∧ storeWire20 s 1 = 1559 := by
  unfold storeWire20 e0P20; dsimp only; constructor <;> (split_ifs <;> (try unfold Wire at *; omega))

theorem leaveAfter20_split4_red (s : Nat) (hL : lowsP20 s ≤ 21) :
    let top := a0P20 s + lowsP20 s - 1
    leaveAfter20 s = tailD0_20 s ++ (pairGM false 1624 (a0P20 s + 21) (bankW20 s 21) ++
      (tailD1_20 s ++ ([.pop (e0P20 s + 3) (e0P20 s + 4) 1559] ++ (tailE0_20 s ++
        ([.make 1558 top 1559] ++ (chainMid20 s ++ ([.pop 1558 top 1559] ++ tailE1_20 s))))))) := by
  obtain ⟨hsw0, hsw1⟩ := storeWire20_01 s
  have hw : wordGM 1624 (columnsP20 s) = CRTBarrel.wordPre 1624 (colsC20 s) ++
      (pairGM false 1624 (a0P20 s + 21) (bankW20 s 21) ++ CRTBarrel.wordPost 1624 (colsC20 s)) := by
    rw [columnsP20_snoc s hL]
    exact CRTWindow.wordGM_snoc 1624 ⟨false, none, a0P20 s + 21, bankW20 s 21⟩ rfl (colsC20 s)
  have hch : chainG (storeWire20 s) (fun i => if i = 0 then a0P20 s + lowsP20 s - 1 else bankW20 s (lowsP20 s + i - 1))
      [.cx (storeWire20 s (liveW20 s - lowsP20 s + 1)) 1557, .x 1557] 0 (liveW20 s - lowsP20 s + 1) =
      [.make 1558 (a0P20 s + lowsP20 s - 1) 1559] ++ (chainMid20 s ++ [.pop 1558 (a0P20 s + lowsP20 s - 1) 1559]) := by
    simp only [chainG, chainMid20, hsw0, hsw1, Nat.zero_add, ↓reduceIte, List.cons_append, List.nil_append]
  unfold leaveAfter20 leaveJoinMove20 leaveLowStore20 leaveStoreMapped20
    tailD0_20 tailD1_20 tailE0_20 lowRest20_pub storeHead20 tailE1_20
  dsimp only
  rw [hw, hch]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

private theorem counts_beforeRow20 (s : Nat) (hw : 1 ≤ wpP20 s) :
    Counts (beforeRow20 s) 41 (wpP20 s + 79) (wpP20 s + 60) (5 * wpP20 s + 439) := by
  have h0 := counts_leaveBefore20 s hw
  rw [leaveBefore20_split4 s] at h0
  obtain ⟨hc, hm, hp, hl⟩ := h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [beforeRow20, cell21_20, shortCell20, List.countP_append, List.countP_cons, List.countP_nil, isCCX,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add] at hc ⊢; omega
  · simp only [beforeRow20, cell21_20, shortCell20, List.countP_append, List.countP_cons, List.countP_nil, isMake,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add] at hm ⊢; omega
  · simp only [beforeRow20, cell21_20, shortCell20, List.countP_append, List.countP_cons, List.countP_nil, isPop,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add] at hp ⊢; omega
  · simp only [beforeRow20, cell21_20, shortCell20, List.length_append, List.length_cons, List.length_nil] at hl ⊢; omega

private theorem counts_afterRow20 (s : Nat) (hL1 : 1 ≤ lowsP20 s) (hL2 : lowsP20 s ≤ 21)
    (hLW : lowsP20 s ≤ liveW20 s) (hn : 2 ≤ nextWp20 s) :
    Counts (afterRow20 s) (lowsP20 s + 10) (liveW20 s + 2 * lowsP20 s + 1)
      (liveW20 s + lowsP20 s + 62) (4 * liveW20 s + 9 * lowsP20 s + 302 + 3 * nextWp20 s) := by
  have h0 := counts_leaveAfter20 s hL1 (by omega) hLW hn
  rw [leaveAfter20_split4_red s hL2] at h0
  obtain ⟨hc, hm, hp, hl⟩ := h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [afterRow20, pairGM, Bool.false_eq_true, ↓reduceIte, List.countP_append, List.countP_cons, List.countP_nil, isCCX] at hc ⊢; omega
  · simp only [afterRow20, pairGM, Bool.false_eq_true, ↓reduceIte, List.countP_append, List.countP_cons, List.countP_nil, isMake] at hm ⊢; omega
  · simp only [afterRow20, pairGM, Bool.false_eq_true, ↓reduceIte, List.countP_append, List.countP_cons, List.countP_nil, isPop] at hp ⊢; omega
  · simp only [afterRow20, pairGM, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_cons, List.length_nil] at hl ⊢; omega

theorem leave20Red_counts (j : Fin 9) :
    let s := start20 j
    toffoliCount (leaveP20Red j) = wpP20 s + liveW20 s + 3 * lowsP20 s + 131 + barrel20T s false ∧
    toffoliCount (leaveInvP20Red j) = wpP20 s + liveW20 s + 2 * lowsP20 s + 173 + barrel20T s true ∧
    measurementCount (leaveP20Red j) = wpP20 s + liveW20 s + lowsP20 s + 122 + barrel20M s false ∧
    measurementCount (leaveInvP20Red j) = wpP20 s + liveW20 s + 2 * lowsP20 s + 80 + barrel20M s true ∧
    gateSlots (leaveP20Red j) = 6 * wpP20 s + 5 * liveW20 s + 10 * lowsP20 s + 863 + 3 * nextWp20 s + barrel20Slots s false ∧
    gateSlots (leaveInvP20Red j) = 6 * wpP20 s + 5 * liveW20 s + 11 * lowsP20 s + 821 + 3 * nextWp20 s + barrel20Slots s true := by
  have hg := geom20_facts j
  have hnw : ∀ k : Fin 9, 74 ≤ nextWp20 (start20 k) ∧ lowsP20 (start20 k) ≤ 21 := by decide
  obtain ⟨bt1, bt2, bm1, bm2, bs1, bs2⟩ := (counts_beforeRow20 (start20 j) (by omega)).programs
  obtain ⟨at1, at2, am1, am2, as1, as2⟩ :=
    (counts_afterRow20 (start20 j) (by omega) (hnw j).2 hg.2.2.2.2.2.2.2.2.2.2.2.2.1 (by have := (hnw j).1; omega)).programs
  obtain ⟨f1, f2, f3⟩ := barrel20_metrics j false
  obtain ⟨g1, g2, g3⟩ := barrel20_metrics j true
  dsimp only
  simp only [leaveP20Red, leaveInvP20Red, toffoliCount_append, measurementCount_append, gateSlots_append,
    bt1, bt2, bm1, bm2, bs1, bs2, at1, at2, am1, am2, as1, as2, f1, f2, f3, g1, g2, g3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private theorem red20_patches_proper : ∀ j : Fin 9,
    let s := start20 j; let h := sbP20 s; let top := a0P20 s + lowsP20 s - 1
    (shortCell20 s h).all proper = true ∧
    proper (.pop (s + 35) (h + 808) (s + h + 58)) = true ∧
    proper (.cx (h + 1583) 1559) = true ∧
    proper (.make (tagsP20.getD 0 0) (a0P20 s + 0) (e0P20 s + 6)) = true ∧
    proper (.cx (e0P20 s + 6) (a0P20 s + 0)) = true ∧
    proper (.cx (e0P20 s + 4) 1559) = true ∧
    proper (.cx top 1559) = true := by
  decide +kernel

theorem beforeRow20_allW {P : Wire → Prop} (j : Fin 9) (h : AllW P (leaveBefore20 (start20 j))) :
    AllW P (beforeRow20 (start20 j)) := by
  let s := start20 j; let b := sbP20 s
  have hsp : leaveBefore20 s = firstRows20 s b ++ (cell21_20 s b ++ (headEnd20 s b ++
      ([.ccx (s + 35) (b + 808) (s + b + 58)] ++ (headA1_20 s ++
        ([.make (b + 1582) (b + 1583) 1559] ++ (headC0_20 s ++
          ([.cx (a0P20 s + 0) (e0P20 s + 6), .ccx (tagsP20.getD 0 0) (e0P20 s + 6) (a0P20 s + 0),
            .cx (a0P20 s + 0) (e0P20 s + 6)] ++ headC1_20 s))))))) := leaveBefore20_split4 s
  have h1 := h
  rw [hsp] at h1
  simp only [allW_append_iff] at h1
  have hz : P (b + 1584) := h1.1 (.cx (s + b + 58) (b + 1584)) (by simp [firstRows20, fix0P20]) _ (by simp [Gate.wires])
  have hc := h1.2.1 (.ccx (s + 35) (b + 807) (s + b + 57)) (by simp [cell21_20])
  have hs35 : P (s + 35) := hc (s + 35) (by simp [Gate.wires])
  have hb807 : P (b + 807) := hc (b + 807) (by simp [Gate.wires])
  have ha57 : P (s + b + 57) := hc (s + b + 57) (by simp [Gate.wires])
  have hshort : AllW P (shortCell20 s b) := by
    intro g hg q hq; simp only [shortCell20, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl | rfl <;> assumption
  have hpop : AllW P [.pop (s + 35) (b + 808) (s + b + 58)] := by
    intro g hg q hq; simp only [List.mem_singleton] at hg; subst hg
    exact h1.2.2.2.1 (.ccx (s + 35) (b + 808) (s + b + 58)) List.mem_cons_self q hq
  have hflag : AllW P [.cx (b + 1583) 1559] := by
    intro g hg q hq; simp only [List.mem_singleton] at hg; subst hg
    exact h1.2.2.2.2.2.1 (.make (b + 1582) (b + 1583) 1559) List.mem_cons_self q (by simp [Gate.wires] at hq ⊢; tauto)
  have hrow0 : AllW P [.make (tagsP20.getD 0 0) (a0P20 s + 0) (e0P20 s + 6), .cx (e0P20 s + 6) (a0P20 s + 0)] := by
    have hr := h1.2.2.2.2.2.2.2.1 (.ccx (tagsP20.getD 0 0) (e0P20 s + 6) (a0P20 s + 0)) (by simp)
    intro g hg q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl | rfl <;> exact hr _ (by simp [Gate.wires])
  change AllW P (firstRows20 s b ++ shortCell20 s b ++ headEnd20 s b ++
    [.pop (s + 35) (b + 808) (s + b + 58)] ++ headA1_20 s ++ [.cx (b + 1583) 1559] ++ headC0_20 s ++
    [.make (tagsP20.getD 0 0) (a0P20 s + 0) (e0P20 s + 6), .cx (e0P20 s + 6) (a0P20 s + 0)] ++ headC1_20 s)
  simp only [allW_append_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h1.1, hshort⟩, h1.2.2.1⟩, hpop⟩, h1.2.2.2.2.1⟩, hflag⟩, h1.2.2.2.2.2.2.1⟩, hrow0⟩, h1.2.2.2.2.2.2.2.2⟩

theorem afterRow20_allW {P : Wire → Prop} (j : Fin 9) (h : AllW P (leaveAfter20 (start20 j))) :
    AllW P (afterRow20 (start20 j)) := by
  have hL : lowsP20 (start20 j) ≤ 21 := by
    have : ∀ k : Fin 9, lowsP20 (start20 k) ≤ 21 := by decide
    exact this j
  let s := start20 j; let top := a0P20 s + lowsP20 s - 1
  have h1 := h
  rw [leaveAfter20_split4_red s hL] at h1
  simp only [allW_append_iff] at h1
  have hfl : AllW P [.cx (e0P20 s + 4) 1559] := by
    intro g hg q hq; simp only [List.mem_singleton] at hg; subst hg
    exact h1.2.2.2.1 (.pop (e0P20 s + 3) (e0P20 s + 4) 1559) List.mem_cons_self q (by simp [Gate.wires] at hq ⊢; tauto)
  have htop : AllW P [.cx top 1559] := by
    intro g hg q hq; simp only [List.mem_singleton] at hg; subst hg
    exact h1.2.2.2.2.2.1 (.make 1558 top 1559) List.mem_cons_self q (by simp [Gate.wires] at hq ⊢; tauto)
  change AllW P (tailD0_20 s ++ tailD1_20 s ++ [.cx (e0P20 s + 4) 1559] ++ tailE0_20 s ++
    [.cx top 1559] ++ chainMid20 s ++ [.cx top 1559] ++ tailE1_20 s)
  simp only [allW_append_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨h1.1, h1.2.2.1⟩, hfl⟩, h1.2.2.2.2.1⟩, htop⟩, h1.2.2.2.2.2.2.1⟩, htop⟩, h1.2.2.2.2.2.2.2.2⟩

theorem leave20Red_ok (j : Fin 9) :
    Proper (beforeRow20 (start20 j)) ∧ AllW (fun q => WindowCovered.domainW q = true) (beforeRow20 (start20 j)) ∧
    Proper (afterRow20 (start20 j)) ∧ AllW (fun q => WindowCovered.domainW q = true) (afterRow20 (start20 j)) := by
  have hb := leaveBefore20_ok j
  have ha := leaveAfter20_ok j
  obtain ⟨hps, hp1, hp2, hp3, hp4, hp5, hp6⟩ := red20_patches_proper j
  have hL : lowsP20 (start20 j) ≤ 21 := by
    have : ∀ k : Fin 9, lowsP20 (start20 k) ≤ 21 := by decide
    exact this j
  have hbp : Proper (beforeRow20 (start20 j)) := by
    have h0 := hb.1; rw [leaveBefore20_split4 (start20 j)] at h0
    have h0' := List.all_eq_true.mpr h0
    simp only [List.all_append, Bool.and_eq_true] at h0'
    apply List.all_eq_true.mp
    simp only [beforeRow20, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨h0'.1, hps⟩, h0'.2.2.1⟩, hp1⟩, h0'.2.2.2.2.1⟩, hp2⟩,
      h0'.2.2.2.2.2.2.1⟩, ⟨hp3, hp4⟩⟩, h0'.2.2.2.2.2.2.2.2⟩
  have hap : Proper (afterRow20 (start20 j)) := by
    have h0 := ha.1; rw [leaveAfter20_split4_red (start20 j) hL] at h0
    have h0' := List.all_eq_true.mpr h0
    simp only [List.all_append, Bool.and_eq_true] at h0'
    apply List.all_eq_true.mp
    simp only [afterRow20, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨h0'.1, h0'.2.2.1⟩, hp5⟩, h0'.2.2.2.2.1⟩, hp6⟩, h0'.2.2.2.2.2.2.1⟩, hp6⟩,
      h0'.2.2.2.2.2.2.2.2⟩
  exact ⟨hbp, beforeRow20_allW j hb.2, hap, afterRow20_allW j ha.2⟩

theorem leave20Red_phys (j : Fin 9) :
    GatePhysical (leaveP20Red j) ∧ GatePhysical (leaveInvP20Red j) := by
  have ok := leave20Red_ok j
  have pb := physical_of_proper _ ok.1
  have pa := physical_of_proper _ ok.2.2.1
  exact ⟨WindowPhysicalW.appP (WindowPhysicalW.appP pb.1 (barrel20_phys j false)) pa.1,
    WindowPhysicalW.appP (WindowPhysicalW.appP pa.2 (barrel20_phys j true)) pb.2⟩

theorem leave20Red_cov (j : Fin 9) :
    WindowCovered.CoveredW (leaveP20Red j) ∧ WindowCovered.CoveredW (leaveInvP20Red j) := by
  have ok := leave20Red_ok j
  obtain ⟨bf, bi⟩ := allW_programs ok.2.1
  obtain ⟨af, ai⟩ := allW_programs ok.2.2.2
  exact ⟨WindowCovered.appW (WindowCovered.appW bf (barrel20_cov j false)) af,
    WindowCovered.appW (WindowCovered.appW ai (barrel20_cov j true)) bi⟩


/-! ### Section 3: 20-tick block 10-tick archive (`archiveLoadP20` / `archiveRestoreP20`) -/

def archScratch20 (s k : Nat) : Wire :=
  let ne0 := nextE0_20 s
  if 1556 + k < ne0 then 1556 + k else 1566 + k

def loadPorts20 (s : Nat) : List Wire :=
  cellsLoadP (s + 20) ++ [nextE0_20 s + 6, nextE0_20 s + 7, nextE0_20 s + 8] ++
    (List.range 132).map (archScratch20 s)

def restorePorts20 (s : Nat) : List Wire :=
  cellsRestoreP (s + 20) ++ (List.range 134).map (archScratch20 s)

def archiveLoadP20 (j : Fin 9) (d : Bool) : Program :=
  renameProgram (fun q => (loadPorts20 (start20 j)).getD q 0)
    (if d then ReducedWindowArchives.load0 else ReducedWindowArchives.load1) ++ moveLoadP (start20 j + 20)

def archiveRestoreP20 (j : Fin 9) (d : Bool) : Program :=
  renameProgram (fun q => (restorePorts20 (start20 j)).getD q 0)
    (if d then ReducedWindowArchives.restore0 else ReducedWindowArchives.restore1) ++
    moveRestoreP (start20 j + 20) (nextE0_20 (start20 j) + 6)

theorem archive20_counts (j : Fin 9) (d : Bool) :
    toffoliCount (archiveLoadP20 j d) = toffoliCount (archiveLoad240 d) ∧
    measurementCount (archiveLoadP20 j d) = measurementCount (archiveLoad240 d) ∧
    gateSlots (archiveLoadP20 j d) = gateSlots (archiveLoad240 d) ∧
    toffoliCount (archiveRestoreP20 j d) = toffoliCount (archiveRestore240 d) ∧
    measurementCount (archiveRestoreP20 j d) = measurementCount (archiveRestore240 d) ∧
    gateSlots (archiveRestoreP20 j d) = gateSlots (archiveRestore240 d) := by
  have r1 : ∀ (f : Wire → Wire) (p : Program), toffoliCount (renameProgram f p) = toffoliCount p :=
    fun f p => (renameProgram_counts f p).1
  have r2 : ∀ (f : Wire → Wire) (p : Program), measurementCount (renameProgram f p) = measurementCount p :=
    fun f p => (renameProgram_counts f p).2
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := moves_counts (start20 j + 20) (nextE0_20 (start20 j) + 6)
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := moves240_counts
  simp only [archiveLoadP20, archiveRestoreP20, archiveLoad240, archiveRestore240,
    toffoliCount_append, measurementCount_append, gateSlots_append, r1, r2, rename_gateSlots,
    l1, l2, l3, l4, l5, l6, m1, m2, m3, m4, m5, m6, and_self]

private theorem archHeads20_ok : ∀ j : Fin 9,
    let s := start20 j
    let headL := cellsLoadP (s + 20) ++ [nextE0_20 s + 6, nextE0_20 s + 7, nextE0_20 s + 8]
    let headR := cellsRestoreP (s + 20)
    headL.length = 23 ∧ headL.Nodup ∧ headL.all WindowCovered.domainW = true ∧
    headL.all (fun q => decide (q < 1556 ∨ 1700 ≤ q ∨ (nextE0_20 s ≤ q ∧ q < nextE0_20 s + 10))) = true ∧
    headR.length = 16 ∧ headR.Nodup ∧ headR.all WindowCovered.domainW = true ∧
    headR.all (fun q => decide (q < 1556 ∨ 1700 ≤ q ∨ (nextE0_20 s ≤ q ∧ q < nextE0_20 s + 10))) = true ∧
    (swapsG (moveLoadPairs (s + 20))).all (fun g => proper g && g.wires.all WindowCovered.domainW) = true ∧
    (swapsG (moveRestorePairs (s + 20) (nextE0_20 s + 6))).all
      (fun g => proper g && g.wires.all WindowCovered.domainW) = true := by
  decide +kernel

private theorem archScratch20_bounds (j : Fin 9) {k : Nat} (hk : k < 134) :
    let s := start20 j
    1556 ≤ archScratch20 s k ∧ archScratch20 s k < 1700 ∧
    (archScratch20 s k < nextE0_20 s ∨ nextE0_20 s + 10 ≤ archScratch20 s k) := by
  have hn := next_geom20 j
  unfold archScratch20; dsimp only
  split_ifs <;> (unfold Wire; omega)

private theorem archScratch20_inj (j : Fin 9) {a b : Nat} (e : archScratch20 (start20 j) a = archScratch20 (start20 j) b) : a = b := by
  unfold archScratch20 at e; dsimp only at e
  split_ifs at e <;> (unfold Wire at *; omega)

theorem archPorts20_ok (j : Fin 9) :
    let s := start20 j
    (loadPorts20 s).length = 155 ∧ (loadPorts20 s).Nodup ∧
    (∀ q ∈ loadPorts20 s, WindowCovered.domainW q = true) ∧
    (restorePorts20 s).length = 150 ∧ (restorePorts20 s).Nodup ∧
    (∀ q ∈ restorePorts20 s, WindowCovered.domainW q = true) := by
  have hh := archHeads20_ok j
  have hscr_nd : ∀ n, ((List.range n).map (archScratch20 (start20 j))).Nodup := fun n =>
    List.Nodup.map_on (fun a _ b _ e => archScratch20_inj j e) List.nodup_range
  have hscr_dom : ∀ n, ∀ q ∈ (List.range n).map (archScratch20 (start20 j)), n ≤ 134 → WindowCovered.domainW q = true := by
    intro n q hq hn
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hk
    have sb := archScratch20_bounds j (k := k) (by omega)
    exact domC (by unfold Wire at *; omega) (by unfold Wire at *; omega)
  have hdisj : ∀ (hd : List Wire) (n : Nat), n ≤ 134 →
      hd.all (fun q => decide (q < 1556 ∨ 1700 ≤ q ∨ (nextE0_20 (start20 j) ≤ q ∧ q < nextE0_20 (start20 j) + 10))) = true →
      ∀ a ∈ hd, ∀ b ∈ (List.range n).map (archScratch20 (start20 j)), a ≠ b := by
    intro hd n hn hall a ha b hb eq
    subst eq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb; rw [List.mem_range] at hk
    have ha' := of_decide_eq_true (List.all_eq_true.mp hall _ ha)
    have sb := archScratch20_bounds j (k := k) (by omega)
    unfold Wire at *; omega
  refine ⟨by rw [loadPorts20, List.length_append, hh.1]; simp, ?_, ?_,
    by rw [restorePorts20, List.length_append, hh.2.2.2.2.1]; simp, ?_, ?_⟩
  · rw [loadPorts20, List.nodup_append]
    exact ⟨hh.2.1, hscr_nd 132, hdisj _ 132 (by decide) hh.2.2.2.1⟩
  · intro q hq; rw [loadPorts20, List.mem_append] at hq
    rcases hq with hq | hq
    · exact List.all_eq_true.mp hh.2.2.1 q hq
    · exact hscr_dom 132 q hq (by decide)
  · rw [restorePorts20, List.nodup_append]
    exact ⟨hh.2.2.2.2.2.1, hscr_nd 134, hdisj _ 134 (by decide) hh.2.2.2.2.2.2.2.1⟩
  · intro q hq; rw [restorePorts20, List.mem_append] at hq
    rcases hq with hq | hq
    · exact List.all_eq_true.mp hh.2.2.2.2.2.2.1 q hq
    · exact hscr_dom 134 q hq (by decide)

attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1
  ReducedWindowArchives.restore0 ReducedWindowArchives.restore1 in
theorem archive20_phys (j : Fin 9) (d : Bool) :
    GatePhysical (archiveLoadP20 j d) ∧ GatePhysical (archiveRestoreP20 j d) := by
  have h := archPorts20_ok j
  have hh := archHeads20_ok j
  constructor
  · rw [archiveLoadP20]
    exact WindowPhysicalW.appP (WindowPhysicalW.load_codec_phys _ h.2.1 h.1.ge d)
      (physical_of_proper _ (fun g hg => (Bool.and_eq_true_iff.mp
        (List.all_eq_true.mp hh.2.2.2.2.2.2.2.2.1 g hg)).1)).1
  · rw [archiveRestoreP20]
    exact WindowPhysicalW.appP (WindowPhysicalW.restore_codec_phys _ h.2.2.2.2.1 h.2.2.2.1.ge d)
      (physical_of_proper _ (fun g hg => (Bool.and_eq_true_iff.mp
        (List.all_eq_true.mp hh.2.2.2.2.2.2.2.2.2 g hg)).1)).1

attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1
  ReducedWindowArchives.restore0 ReducedWindowArchives.restore1 in
theorem archive20_cov (j : Fin 9) (d : Bool) :
    WindowCovered.CoveredW (archiveLoadP20 j d) ∧ WindowCovered.CoveredW (archiveRestoreP20 j d) := by
  have h := archPorts20_ok j
  have hh := archHeads20_ok j
  have hmvL : AllW (fun q => WindowCovered.domainW q = true) (swapsG (moveLoadPairs (start20 j + 20))) :=
    fun g hg q hq => List.all_eq_true.mp
      (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hh.2.2.2.2.2.2.2.2.1 g hg)).2 q hq
  have hmvR : AllW (fun q => WindowCovered.domainW q = true)
      (swapsG (moveRestorePairs (start20 j + 20) (nextE0_20 (start20 j) + 6))) :=
    fun g hg q hq => List.all_eq_true.mp
      (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hh.2.2.2.2.2.2.2.2.2 g hg)).2 q hq
  constructor
  · rw [archiveLoadP20]
    refine WindowCovered.appW (fun q hq => ?_) (allW_programs hmvL).1
    rw [renameProgram_support] at hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hplt : p < 155 := by cases d; exact Partial.load1_ports p hp; exact Partial.load0_ports p hp
    rw [List.getD_eq_getElem _ _ (by rw [h.1]; exact hplt)]
    exact h.2.2.1 _ (List.getElem_mem _)
  · rw [archiveRestoreP20]
    refine WindowCovered.appW (fun q hq => ?_) (allW_programs hmvR).1
    rw [renameProgram_support] at hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hplt : p < 150 := by cases d; exact Partial.restore1_ports p hp; exact Partial.restore0_ports p hp
    rw [List.getD_eq_getElem _ _ (by rw [h.2.2.2.1]; exact hplt)]
    exact h.2.2.2.2.2 _ (List.getElem_mem _)

/-! ### Section 4: 23-mode symbolic selector certificates (`LeaveSelector20`) & `deadKept10` -/

namespace Selector20
open LeaveSelector

/-- 23 modes: `0` inactive (near), `1` left rail (`2^b ≤ z.u`), `2 + w` right rail at wait `w ∈ 0..20`. -/
abbrev Mode20 := Fin 23
def right20 (k : Mode20) : Bool := decide (2 ≤ k.val)
def left20 (k : Mode20) : Bool := decide (k.val = 1)
def key20 (k : Mode20) : Nat := k.val - 2
def enabled20 (k : Mode20) : Bool := decide (k.val ≠ 0)
def hot20 (k : Mode20) (i : Nat) : Bool := right20 k && decide (key20 k = i)

def crossing20 (p : Ports) (k : Mode20) : Expr :=
  if enabled20 k then .wire (p.u + key20 k) else .bit false

def nearby20 (k : Mode20) : Bool := enabled20 k && decide (key20 k < 10)

def suffixExpr20 (p : Ports) (i : Nat) : Expr :=
  ((List.range 20).drop i).foldl (fun rest j => conj rest (.wire (p.g + j))) (.bit true)

def signExpr20 (p : Ports) (k : Mode20) : Expr :=
  if right20 k && decide (0 < key20 k) then suffixExpr20 p (key20 k + key20 k) else .bit false

/-- Canonical abstract ports disjoint from scratch `1559..1602`: `g = 100..119`, `u = 200..220`, `crossing = 300`, `near = 301`. -/
def canonPorts : Ports := ⟨100, 200, 300, 301⟩

def start20Sel (p : Ports) (k : Mode20) (q : Wire) : Expr :=
  if q = 1559 then .bit (left20 k)
  else if q = 1560 then .bit (hot20 k 20)
  else if 1561 ≤ q ∧ q ≤ 1580 then .bit (hot20 k (q - 1561))
  else if 1581 ≤ q ∧ q ≤ 1602 then .bit false
  else if q = p.crossing then .bit false
  else if q = p.near then .bit false
  else .wire q

def prepOps20 (p : Ports) : List Op :=
  [.xor 1559 p.near] ++
  ((List.range 10).map fun i => .xor (1561 + i) p.near) ++
  [.xor 1559 1581, .xor 1561 1581,
   .save 1562 (p.g + 2) 1582, .save 1582 (p.g + 3) 1583, .xor 1563 1583,
   .save 1583 (p.g + 4) 1584, .save 1584 (p.g + 5) 1585, .xor 1564 1585,
   .save 1585 (p.g + 6) 1586, .save 1586 (p.g + 7) 1587, .xor 1565 1587,
   .save 1587 (p.g + 8) 1588, .save 1588 (p.g + 9) 1589, .xor 1566 1589,
   .save 1589 (p.g + 10) 1590, .save 1590 (p.g + 11) 1591, .xor 1567 1591,
   .save 1591 (p.g + 12) 1592, .save 1592 (p.g + 13) 1593, .xor 1568 1593,
   .save 1593 (p.g + 14) 1594, .save 1594 (p.g + 15) 1595, .xor 1569 1595,
   .save 1595 (p.g + 16) 1596, .save 1596 (p.g + 17) 1597, .xor 1570 1597,
   .save 1597 (p.g + 18) 1598, .save 1598 (p.g + 19) 1599] ++
  ((List.range 21).map fun i => .mix (tagsP20.getD i 0) (p.u + i) p.crossing) ++
  [.xor 1599 1601] ++
  ((List.range 10).map fun i => .xor (1571 + i) 1601) ++
  [.xor 1560 1601, .save p.crossing 1601 1602]

def retireOps20 (p : Ports) : List Op :=
  (([.xor 1559 1581, .xor 1561 1581,
    .save 1562 (p.g + 2) 1582, .save 1582 (p.g + 3) 1583, .xor 1563 1583,
    .save 1583 (p.g + 4) 1584, .save 1584 (p.g + 5) 1585, .xor 1564 1585,
    .save 1585 (p.g + 6) 1586, .save 1586 (p.g + 7) 1587, .xor 1565 1587,
    .save 1587 (p.g + 8) 1588, .save 1588 (p.g + 9) 1589, .xor 1566 1589,
    .save 1589 (p.g + 10) 1590, .save 1590 (p.g + 11) 1591, .xor 1567 1591,
    .save 1591 (p.g + 12) 1592, .save 1592 (p.g + 13) 1593, .xor 1568 1593,
    .save 1593 (p.g + 14) 1594, .save 1594 (p.g + 15) 1595, .xor 1569 1595,
    .save 1595 (p.g + 16) 1596, .save 1596 (p.g + 17) 1597, .xor 1570 1597,
    .save 1597 (p.g + 18) 1598, .save 1598 (p.g + 19) 1599,
    .xor 1599 1601] : List Op) ++
   ((List.range 10).map fun i => Op.xor (1571 + i) 1601) ++
   [Op.xor 1560 1601, Op.save p.crossing 1601 1602]).reverse

def post20 (p : Ports) (k : Mode20) : Sym := fun q =>
  if q = p.crossing ∨ q = p.near then .wire q
  else if q = 1602 then conj (.wire p.crossing) (signExpr20 p k)
  else sim (prepOps20 p) (start20Sel p k) q

def restored20Sel (p : Ports) (k : Mode20) : Sym := fun q =>
  if q = p.crossing ∨ q = p.near then .wire q
  else start20Sel p k q

/-- All 21 one-hot tags, all 4 controls (`near`, `crossing`, `signExpr`, `crossing ∧ signExpr`),
and clean retirement of `1581..1602` verified across all 23 modes! -/
theorem selector20_certs : ∀ k : Mode20,
    let st := sim (prepOps20 canonPorts) (start20Sel canonPorts k)
    (∀ i : Fin 21, st (tagsP20.getD i.val 0) = .bit (enabled20 k && decide (i.val = key20 k))) ∧
    st canonPorts.near = .bit (nearby20 k) ∧
    st canonPorts.crossing = crossing20 canonPorts k ∧
    st 1601 = signExpr20 canonPorts k ∧
    st 1602 = conj (crossing20 canonPorts k) (signExpr20 canonPorts k) ∧
    validExit (retireOps20 canonPorts) (post20 canonPorts k) = true ∧
    (List.range' 1581 22).all (fun q =>
      decide (erased (retireOps20 canonPorts) (post20 canonPorts k) q = restored20Sel canonPorts k q)) = true := by
  decide +kernel

/-- `kept10` soundness: for every mode with `key20 k ≥ 10` (`2 * key ≥ 20`), `signExpr20 = true`,
so wire `1623 = ((far ^^ d0) ^^ signExpr) ^^ (d0 && signExpr) = false` identically! -/
theorem deadKept10 (k : Mode20) (hk : 10 ≤ key20 k) (d0 : Bool) :
    signExpr20 canonPorts k = .bit true ∧
    ((((enabled20 k ^^ d0) ^^ true) ^^ (d0 && true)) = false) := by
  have hk' : 12 ≤ k.val := by unfold key20 at hk; omega
  have h1 : right20 k = true := by simp only [right20, decide_eq_true_eq]; omega
  have h2 : 0 < key20 k := by omega
  have h3 : enabled20 k = true := by simp only [enabled20, decide_eq_true_eq]; omega
  refine ⟨?_, ?_⟩
  · unfold signExpr20 suffixExpr20
    rw [h1, decide_eq_true h2, Bool.and_true, if_pos rfl, List.drop_eq_nil_of_le (by rw [List.length_range]; omega)]
    rfl
  · rw [h3]; cases d0 <;> rfl

end Selector20

end ECDSAAdd.Entrant.StairPacket.Shadow20
end
-- ==== end Shadow7Wide20Leave ====

-- ==== begin Shadow7Wide20Bridge ====
section

/-!
# Mixed 15/20-Tick Shadow Window & 22-Bank Field Bridge

Connects the 9 twenty-tick shadow blocks (`s = 165, 185, ..., 325`) to the surrounding
fifteen-tick shadow blocks (`s = 45..150` and `s = 345..405`, exit at tick `420`):

1. **Transition block `s = 150 -> 165`**: fifteen-tick CRT barrel leave at `s = 150`
   targeting the 20-tick frame at `s = 165` (`lowsP = 7`, `nextE0 = 1742`, `nextWp = 74`),
   plus its archive codec at tick `165` (`flags = 1748..1750`).
2. **`MixedWindow`**: full forward & reverse window assembly over ticks `[45, 420]` with
   exact proven Toffoli & measurement counts (`128262 F / 128601 R` Toffolis, saving
   `224 F + 227 R = 451 T` per kernel vs uniform 15-tick `CRTWindow`'s `128486 F / 128828 R`),
   `GatePhysical`, and `WindowCovered.CoveredW`.
3. **`MixedFieldBanks`**: safety & packet-avoidance proofs for all 22 field archive banks
   (proving the 6 new banks `{35, 39, 47, 51, 59, 63}` plus `{10, 13}`), the 22-bank
   field group fold saving `3 * 112 = 336 T` per kernel (`672 T` across both kernels),
   and the combined `1574 T` net savings theorem across both kernels.
-/

namespace ECDSAAdd.Entrant.StairPacket.Shadow20

open ECDSAAdd.Arithmetic
open ECDSAAdd.Arithmetic.MappedCompressed
open ECDSAAdd.Baselines
open ECDSAAdd.Challenge
open ECDSAAdd.RecordedQuantum
open ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Entrant.StairPacket.Partial
open ECDSAAdd.Entrant.StairPacket.GateMirror
open ECDSAAdd.Entrant.StairPacket.WindowFold

set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### Section 1: Transition block `s = 150 -> 165` -/

def lows150 : Nat := 12

def columnsP150 : List HighBankJoin.Column :=
  (List.range 17).map fun i =>
    ⟨decide (i < lows150), if i < 16 then some (tagsP.getD i 0) else none,
      Shadow7.a0P 150 + i, Shadow7.bankW 150 i⟩

def leaveJoinMove150 : List Gate :=
  KeptParity.placed 150 ++ wordGM 1614 columnsP150

def leaveLowStore150 : List Gate :=
  let L := lows150
  let bs := (List.range L).map (Shadow7.b0P 150 + ·)
  [.cx (Shadow7.e0P 150 + 3) 1560, .cx 1559 1560,
   .pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559] ++
  ((List.range L).map fun i => .make 1556 (Shadow7.a0P 150 + i) (Shadow7.b0P 150 + i)) ++ xsG bs ++
  addG bs ((List.range (L - 1)).map (1559 + ·)) 1558 ++ xsG bs ++
  [.pop (Shadow7.b0P 150 - 1) 1557 1558, .cx (Shadow7.a0P 150 - 1) 1557, .x 1557]

def leaveStoreMapped150 : List Gate :=
  let L := lows150
  let top := Shadow7.a0P 150 + L - 1
  let H := Shadow7.liveW 150 - L
  let hi := (List.range H).map fun i => Shadow7.bankW 150 (L + i)
  let seq := fun i => if i = 0 then top else Shadow7.bankW 150 (L + i - 1)
  let seq2 := (List.range (L + 1)).map (Shadow7.b0P 150 - 1 + ·)
  [.x 1558, .x top] ++ xsG hi ++
  chainG (Shadow7.storeW 150) seq [.cx (Shadow7.storeW 150 (H + 1)) 1557, .x 1557] 0 (H + 1) ++
  xsG hi.reverse ++ [.x top, .x 1558, .make 1556 1557 1558, .x 1558] ++
  xsG seq2 ++ chainG (1558 + ·) (Shadow7.b0P 150 - 1 + ·) [.cx (1558 + (L + 1)) 1556, .x 1556] 0 (L + 1) ++
  xsG seq2.reverse ++ [.x 1558]

def leaveLowClose150 : List Gate :=
  let L := lows150
  xsG ((List.range 15).map (150 + 16 + ·)) ++
  ((List.range (L + 1)).map fun i => .cx (Shadow7.e0P 150 + 5) (Shadow7.b0P 150 - 1 + i)) ++
  ((List.range (L + 1)).flatMap fun i => cswapG (150 + 30) (Shadow7.b0P 150 - 1 + i) (Shadow7.a0P 150 - 1 + i))

def movesP150To20 : List (Wire × Wire) :=
  ((List.range (wpP20 165 - 2)).map fun i => (Shadow7.bankW 150 (lows150 + i), bTopP 165 + 3 + i - wpP20 165)) ++
  [(1557, e0P20 165 + 3), (1558, e0P20 165 + 4), (Shadow7.e0P 150 + 5, e0P20 165 + 5),
   (Shadow7.e0P 150 + 3, e0P20 165 + 6), (Shadow7.e0P 150 + 7, e0P20 165 + 7),
   (Shadow7.e0P 150 + 6, e0P20 165 + 8)]

def leaveClose150To20 : List Gate :=
  Shadow7.closeFlag 150 ++ swapsG movesP150To20

def leaveAfter150To20 : List Gate :=
  Shadow7.fix8P 150 (Shadow7.sbP 150) ++ leaveJoinMove150 ++ Shadow7.fix10P 150 (Shadow7.sbP 150) ++
  leaveFix11 150 (Shadow7.sbP 150) ++ leaveFix12 150 (Shadow7.sbP 150) ++ leaveLowStore150 ++
  leaveStoreMapped150 ++ leaveLowClose150 ++ leaveClose150To20

def leave150To20 : Program :=
  GateMirror.forward (CRTBarrel.before 150) ++ CRTBarrel.barrel 150 false ++
    GateMirror.forward leaveAfter150To20

def leaveInv150To20 : Program :=
  inverse leaveAfter150To20 ++ CRTBarrel.barrel 150 true ++ inverse (CRTBarrel.before 150)

private theorem leave150_sum_counts :
    (CRTBarrel.before 150).countP isCCX + leaveAfter150To20.countP isCCX = 54 ∧
    (CRTBarrel.before 150).countP isMake + leaveAfter150To20.countP isMake = 237 ∧
    (CRTBarrel.before 150).countP isPop + leaveAfter150To20.countP isPop = 257 ∧
    (CRTBarrel.before 150).length + leaveAfter150To20.length = 1577 := by
  decide +kernel

private theorem after150_ok :
    (Shadow7.fix8P 150 (Shadow7.sbP 150)).all (fun g => proper g && g.wires.all WindowCovered.domainW) = true ∧
    leaveJoinMove150.all (fun g => proper g && g.wires.all WindowCovered.domainW) = true ∧
    (Shadow7.fix10P 150 (Shadow7.sbP 150)).all (fun g => proper g && g.wires.all WindowCovered.domainW) = true ∧
    (leaveFix11 150 (Shadow7.sbP 150)).all (fun g => proper g && g.wires.all WindowCovered.domainW) = true ∧
    (leaveFix12 150 (Shadow7.sbP 150)).all (fun g => proper g && g.wires.all WindowCovered.domainW) = true ∧
    leaveLowStore150.all (fun g => proper g && g.wires.all WindowCovered.domainW) = true ∧
    leaveStoreMapped150.all (fun g => proper g && g.wires.all WindowCovered.domainW) = true ∧
    leaveLowClose150.all (fun g => proper g && g.wires.all WindowCovered.domainW) = true ∧
    leaveClose150To20.all (fun g => proper g && g.wires.all WindowCovered.domainW) = true := by
  decide +kernel

private theorem before150_proper_cov :
    (∀ g ∈ CRTBarrel.before 150, proper g = true) ∧
    AllW (fun q => WindowCovered.domainW q = true) (CRTBarrel.before 150) := by
  have hsp : Shadow7.leaveMoveOps 150 =
      CRTBarrel.before 150 ++ (Shadow7.leaveBarrel 150 ++ CRTBarrel.afterPart 150) := by
    simp only [Shadow7.leaveMoveOps, CRTBarrel.before, CRTBarrel.afterPart, List.append_assoc]
  have lp : ∀ g ∈ Shadow7.leaveOps 150, proper g = true := by
    rw [Shadow7.leaveOps_split, Shadow7.leaveMidOps_eq]
    exact proper_append (proper_append (Shadow7.head_ok ⟨7, by decide⟩ (by decide) (by decide)).2
      (proper_append (proper_append (Shadow7.lowRest_ok (s := 150) (by decide) (by decide)).2
        (Shadow7.storeMapped_ok (s := 150) (by decide) (by decide)).2)
        (Shadow7.lowClose_ok (s := 150) (by decide) (by decide)).2))
      (Shadow7.close_ok (s := 150) (by decide) (by decide)).2
  have p := Shadow7.leaveMove_proper_of (s := 150) (by decide) (by decide) lp
  have a := Shadow7.allW_leaveMove 150 (Shadow7.leaveOps_box ⟨7, by decide⟩ (by decide) (by decide))
  rw [hsp] at p a
  refine ⟨fun g hg => p g (List.mem_append_left _ hg), fun g hg q hq => ?_⟩
  have b := a g (List.mem_append_left _ hg) q hq
  rw [show start ⟨7, by decide⟩ = 150 from rfl] at b
  dsimp only; rw [WindowCovered.dom_iff]; unfold leaveBox at b; omega

private theorem leaveAfter150_ok :
    (∀ g ∈ leaveAfter150To20, proper g = true) ∧
    AllW (fun q => WindowCovered.domainW q = true) leaveAfter150To20 := by
  have h := after150_ok
  have mk : ∀ {gs : List Gate}, gs.all (fun g => proper g && g.wires.all WindowCovered.domainW) = true →
      (∀ g ∈ gs, proper g = true) ∧ AllW (fun q => WindowCovered.domainW q = true) gs := fun hh =>
    ⟨fun g hg => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hh g hg)).1,
     fun g hg q hq => List.all_eq_true.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hh g hg)).2 q hq⟩
  have h1 := mk h.1; have h2 := mk h.2.1; have h3 := mk h.2.2.1; have h4 := mk h.2.2.2.1
  have h5 := mk h.2.2.2.2.1; have h6 := mk h.2.2.2.2.2.1; have h7 := mk h.2.2.2.2.2.2.1
  have h8 := mk h.2.2.2.2.2.2.2.1; have h9 := mk h.2.2.2.2.2.2.2.2
  refine ⟨proper_append (proper_append (proper_append (proper_append (proper_append (proper_append
      (proper_append (proper_append h1.1 h2.1) h3.1) h4.1) h5.1) h6.1) h7.1) h8.1) h9.1,
    allW_append (allW_append (allW_append (allW_append (allW_append (allW_append
      (allW_append (allW_append h1.2 h2.2) h3.2) h4.2) h5.2) h6.2) h7.2) h8.2) h9.2⟩

attribute [local irreducible] CRTBarrel.barrel GateMirror.forward inverse toffoliCount measurementCount gateSlots in
theorem leave150To20_counts :
    toffoliCount leave150To20 = 478 ∧
    toffoliCount leaveInv150To20 = 498 ∧
    measurementCount leave150To20 = 294 ∧
    measurementCount leaveInv150To20 = 274 ∧
    gateSlots leave150To20 = 11608 ∧
    gateSlots leaveInv150To20 = 11543 := by
  have hs := leave150_sum_counts
  have cb : Counts (CRTBarrel.before 150) ((CRTBarrel.before 150).countP isCCX)
      ((CRTBarrel.before 150).countP isMake) ((CRTBarrel.before 150).countP isPop)
      (CRTBarrel.before 150).length := ⟨rfl, rfl, rfl, rfl⟩
  have ca : Counts leaveAfter150To20 (leaveAfter150To20.countP isCCX)
      (leaveAfter150To20.countP isMake) (leaveAfter150To20.countP isPop)
      leaveAfter150To20.length := ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨bt1, bm1, bs1, bt2, bm2, bs2⟩ := cb.programs
  obtain ⟨at1, am1, as1, at2, am2, as2⟩ := ca.programs
  obtain ⟨f1, f2, f3⟩ := CRTBarrel.barrel_metrics ⟨7, by decide⟩ (by decide) (by decide) false
  obtain ⟨g1, g2, g3⟩ := CRTBarrel.barrel_metrics ⟨7, by decide⟩ (by decide) (by decide) true
  have hs7 : start ⟨7, by decide⟩ = 150 := rfl
  have hbt0 : CRTBarrel.barrelT 150 false = 187 := by decide
  have hbt1 : CRTBarrel.barrelT 150 true = 187 := by decide
  have hbm0 : CRTBarrel.barrelM 150 false = 37 := by decide
  have hbm1 : CRTBarrel.barrelM 150 true = 37 := by decide
  have hbs0 : CRTBarrel.barrelSlots 150 false = 9774 := by decide
  have hbs1 : CRTBarrel.barrelSlots 150 true = 9729 := by decide
  rw [hs7, hbt0] at f1; rw [hs7, hbm0] at f2; rw [hs7, hbs0] at f3
  rw [hs7, hbt1] at g1; rw [hs7, hbm1] at g2; rw [hs7, hbs1] at g3
  simp only [leave150To20, leaveInv150To20, toffoliCount_append, measurementCount_append, gateSlots_append]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

attribute [local irreducible] CRTBarrel.barrel GateMirror.forward inverse in
theorem leave150To20_phys :
    GatePhysical leave150To20 ∧ GatePhysical leaveInv150To20 := by
  have pb := physical_of_proper _ before150_proper_cov.1
  have pa := physical_of_proper _ leaveAfter150_ok.1
  have bf := CRTBarrel.barrel_phys ⟨7, by decide⟩ (by decide) (by decide) false
  have br := CRTBarrel.barrel_phys ⟨7, by decide⟩ (by decide) (by decide) true
  rw [show start ⟨7, by decide⟩ = 150 from rfl] at bf br
  exact ⟨WindowPhysicalW.appP (WindowPhysicalW.appP pb.1 bf) pa.1,
    WindowPhysicalW.appP (WindowPhysicalW.appP pa.2 br) pb.2⟩

attribute [local irreducible] CRTBarrel.barrel in
private theorem barrel150_cov (mir : Bool) : WindowCovered.CoveredW (CRTBarrel.barrel 150 mir) := by
  intro q hq
  have bw := CRTBarrel.barrel_wires ⟨7, by decide⟩ (by decide) (by decide) mir q hq
  rw [show start ⟨7, by decide⟩ = 150 from rfl] at bw
  rcases bw with ⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩ | ht
  · have bc := Shadow7.bank_cases (s := 150) (by decide) (by decide) hi
    have r := Shadow7.rail_win (s := 150) (by decide) (by decide)
    rw [WindowCovered.dom_iff]; unfold Wire at *; omega
  · have pc := Shadow7.pool_cases (s := 150) (i := 17 + k) (by decide) (by decide)
    rw [WindowCovered.dom_iff]; unfold Wire at *; omega
  · have t : ∀ w ∈ tagsP, WindowCovered.domainW w = true := by decide
    exact t q ht

attribute [local irreducible] CRTBarrel.barrel GateMirror.forward inverse in
theorem leave150To20_cov :
    WindowCovered.CoveredW leave150To20 ∧ WindowCovered.CoveredW leaveInv150To20 := by
  obtain ⟨bf, bi⟩ := allW_programs before150_proper_cov.2
  obtain ⟨af, ai⟩ := allW_programs leaveAfter150_ok.2
  exact ⟨WindowCovered.appW (WindowCovered.appW bf (barrel150_cov false)) af,
    WindowCovered.appW (WindowCovered.appW ai (barrel150_cov true)) bi⟩

/-! ### Stage 6B3: `afterRow150` / `leave150To20Red` (`LeaveReductions` parity on `s = 150 -> 165`) -/

def colsC150 : List HighBankJoin.Column :=
  (List.range 16).map fun i =>
    ⟨decide (i < lows150), some (tagsP.getD i 0), Shadow7.a0P 150 + i, Shadow7.bankW 150 i⟩

def tailD0_150 : List Gate :=
  Shadow7.fix8P 150 (Shadow7.sbP 150) ++ KeptParity.placed 150 ++ CRTBarrel.wordPre 1614 colsC150

def tailD1_150 : List Gate :=
  CRTBarrel.wordPost 1614 colsC150 ++ Shadow7.fix10P 150 (Shadow7.sbP 150) ++
  leaveFix11 150 (Shadow7.sbP 150) ++ leaveFix12 150 (Shadow7.sbP 150) ++
  [.cx (Shadow7.e0P 150 + 3) 1560, .cx 1559 1560]

def lowRest150_pub : List Gate :=
  let L := lows150
  let bs := (List.range L).map (Shadow7.b0P 150 + ·)
  ((List.range L).map fun i => .make 1556 (Shadow7.a0P 150 + i) (Shadow7.b0P 150 + i)) ++ xsG bs ++
  addG bs ((List.range (L - 1)).map (1559 + ·)) 1558 ++ xsG bs ++
  [.pop (Shadow7.b0P 150 - 1) 1557 1558, .cx (Shadow7.a0P 150 - 1) 1557, .x 1557]

def storeHead150 : List Gate :=
  let L := lows150
  let top := Shadow7.a0P 150 + L - 1
  let H := Shadow7.liveW 150 - L
  [.x 1558, .x top] ++ xsG ((List.range H).map fun i => Shadow7.bankW 150 (L + i))

def tailE0_150 : List Gate := lowRest150_pub ++ storeHead150

def chainMid150 : List Gate :=
  let L := lows150
  let top := Shadow7.a0P 150 + L - 1
  let H := Shadow7.liveW 150 - L
  chainG (Shadow7.storeW 150) (fun i => if i = 0 then top else Shadow7.bankW 150 (L + i - 1))
    [.cx (Shadow7.storeW 150 (H + 1)) 1557, .x 1557] 1 H

def tailE1_150 : List Gate :=
  let L := lows150
  let top := Shadow7.a0P 150 + L - 1
  let H := Shadow7.liveW 150 - L
  let hi := (List.range H).map fun i => Shadow7.bankW 150 (L + i)
  let seq2 := (List.range (L + 1)).map (Shadow7.b0P 150 - 1 + ·)
  xsG hi.reverse ++ [.x top, .x 1558, .make 1556 1557 1558, .x 1558] ++ xsG seq2 ++
  chainG (1558 + ·) (Shadow7.b0P 150 - 1 + ·) [.cx (1558 + (L + 1)) 1556, .x 1556] 0 (L + 1) ++
  xsG seq2.reverse ++ [.x 1558] ++ leaveLowClose150 ++ leaveClose150To20

def afterRow150 : List Gate :=
  let top := Shadow7.a0P 150 + lows150 - 1
  tailD0_150 ++ tailD1_150 ++ [.cx (Shadow7.e0P 150 + 4) 1559] ++ tailE0_150 ++
  [.cx top 1559] ++ chainMid150 ++ [.cx top 1559] ++ tailE1_150

def leave150To20Red : Program :=
  GateMirror.forward (CRTBarrel.beforeRow 150) ++ CRTBarrel.barrel 150 false ++
    GateMirror.forward afterRow150

def leaveInv150To20Red : Program :=
  inverse afterRow150 ++ CRTBarrel.barrel 150 true ++ inverse (CRTBarrel.beforeRow 150)

private theorem leave150Red_sum_counts :
    (CRTBarrel.beforeRow 150).countP isCCX + afterRow150.countP isCCX = 51 ∧
    (CRTBarrel.beforeRow 150).countP isMake + afterRow150.countP isMake = 236 ∧
    (CRTBarrel.beforeRow 150).countP isPop + afterRow150.countP isPop = 256 ∧
    (CRTBarrel.beforeRow 150).length + afterRow150.length = 1577 := by
  decide +kernel

private theorem leave150Red_gates_ok :
    (CRTBarrel.beforeRow 150).all (fun g => proper g && g.wires.all WindowCovered.domainW) = true ∧
    afterRow150.all (fun g => proper g && g.wires.all WindowCovered.domainW) = true := by
  decide +kernel

attribute [local irreducible] CRTBarrel.barrel GateMirror.forward inverse toffoliCount measurementCount gateSlots in
theorem leave150To20Red_counts :
    toffoliCount leave150To20Red = 474 ∧
    toffoliCount leaveInv150To20Red = 494 ∧
    measurementCount leave150To20Red = 293 ∧
    measurementCount leaveInv150To20Red = 273 ∧
    gateSlots leave150To20Red = 11607 ∧
    gateSlots leaveInv150To20Red = 11542 := by
  have hs := leave150Red_sum_counts
  have cb : Counts (CRTBarrel.beforeRow 150) ((CRTBarrel.beforeRow 150).countP isCCX)
      ((CRTBarrel.beforeRow 150).countP isMake) ((CRTBarrel.beforeRow 150).countP isPop)
      (CRTBarrel.beforeRow 150).length := ⟨rfl, rfl, rfl, rfl⟩
  have ca : Counts afterRow150 (afterRow150.countP isCCX)
      (afterRow150.countP isMake) (afterRow150.countP isPop)
      afterRow150.length := ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨bt1, bm1, bs1, bt2, bm2, bs2⟩ := cb.programs
  obtain ⟨at1, am1, as1, at2, am2, as2⟩ := ca.programs
  obtain ⟨f1, f2, f3⟩ := CRTBarrel.barrel_metrics ⟨7, by decide⟩ (by decide) (by decide) false
  obtain ⟨g1, g2, g3⟩ := CRTBarrel.barrel_metrics ⟨7, by decide⟩ (by decide) (by decide) true
  have hs7 : start ⟨7, by decide⟩ = 150 := rfl
  have hbt0 : CRTBarrel.barrelT 150 false = 187 := by decide
  have hbt1 : CRTBarrel.barrelT 150 true = 187 := by decide
  have hbm0 : CRTBarrel.barrelM 150 false = 37 := by decide
  have hbm1 : CRTBarrel.barrelM 150 true = 37 := by decide
  have hbs0 : CRTBarrel.barrelSlots 150 false = 9774 := by decide
  have hbs1 : CRTBarrel.barrelSlots 150 true = 9729 := by decide
  rw [hs7, hbt0] at f1; rw [hs7, hbm0] at f2; rw [hs7, hbs0] at f3
  rw [hs7, hbt1] at g1; rw [hs7, hbm1] at g2; rw [hs7, hbs1] at g3
  simp only [leave150To20Red, leaveInv150To20Red, toffoliCount_append, measurementCount_append, gateSlots_append]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

attribute [local irreducible] CRTBarrel.barrel GateMirror.forward inverse in
theorem leave150To20Red_phys :
    GatePhysical leave150To20Red ∧ GatePhysical leaveInv150To20Red := by
  have ok := leave150Red_gates_ok
  have pb := physical_of_proper _ (fun g hg => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp ok.1 g hg)).1)
  have pa := physical_of_proper _ (fun g hg => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp ok.2 g hg)).1)
  have bf := CRTBarrel.barrel_phys ⟨7, by decide⟩ (by decide) (by decide) false
  have br := CRTBarrel.barrel_phys ⟨7, by decide⟩ (by decide) (by decide) true
  rw [show start ⟨7, by decide⟩ = 150 from rfl] at bf br
  exact ⟨WindowPhysicalW.appP (WindowPhysicalW.appP pb.1 bf) pa.1,
    WindowPhysicalW.appP (WindowPhysicalW.appP pa.2 br) pb.2⟩

attribute [local irreducible] CRTBarrel.barrel GateMirror.forward inverse in
theorem leave150To20Red_cov :
    WindowCovered.CoveredW leave150To20Red ∧ WindowCovered.CoveredW leaveInv150To20Red := by
  have ok := leave150Red_gates_ok
  obtain ⟨bf, bi⟩ := allW_programs (fun g hg q hq => List.all_eq_true.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp ok.1 g hg)).2 q hq)
  obtain ⟨af, ai⟩ := allW_programs (fun g hg q hq => List.all_eq_true.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp ok.2 g hg)).2 q hq)
  exact ⟨WindowCovered.appW (WindowCovered.appW bf (barrel150_cov false)) af,
    WindowCovered.appW (WindowCovered.appW ai (barrel150_cov true)) bi⟩


/-! Transition archive at tick `165` (`e0P20 165 = 1742`, flags `1748..1750`). -/

def archScratch150 (k : Nat) : Wire :=
  if 1556 + k < e0P20 165 then 1556 + k else 1566 + k

def loadPorts150 : List Wire :=
  cellsLoadP 165 ++ [e0P20 165 + 6, e0P20 165 + 7, e0P20 165 + 8] ++
    (List.range 132).map archScratch150

def restorePorts150 : List Wire :=
  cellsRestoreP 165 ++ (List.range 134).map archScratch150

def archiveLoad150To20 (d : Bool) : Program :=
  renameProgram (fun q => loadPorts150.getD q 0)
    (if d then ReducedWindowArchives.load0 else ReducedWindowArchives.load1) ++ moveLoadP 165

def archiveRestore150To20 (d : Bool) : Program :=
  renameProgram (fun q => restorePorts150.getD q 0)
    (if d then ReducedWindowArchives.restore0 else ReducedWindowArchives.restore1) ++
    moveRestoreP 165 (e0P20 165 + 6)

private theorem arch150_heads_ok :
    let headL := cellsLoadP 165 ++ [e0P20 165 + 6, e0P20 165 + 7, e0P20 165 + 8]
    let headR := cellsRestoreP 165
    headL.length = 23 ∧ headL.Nodup ∧ headL.all WindowCovered.domainW = true ∧
    headL.all (fun q => decide (q < 1556 ∨ 1700 ≤ q)) = true ∧
    headR.length = 16 ∧ headR.Nodup ∧ headR.all WindowCovered.domainW = true ∧
    headR.all (fun q => decide (q < 1556 ∨ 1700 ≤ q)) = true ∧
    (swapsG (moveLoadPairs 165)).all (fun g => proper g && g.wires.all WindowCovered.domainW) = true ∧
    (swapsG (moveRestorePairs 165 (e0P20 165 + 6))).all
      (fun g => proper g && g.wires.all WindowCovered.domainW) = true := by
  decide +kernel

private theorem arch150_ok :
    loadPorts150.length = 155 ∧ loadPorts150.Nodup ∧ (∀ q ∈ loadPorts150, WindowCovered.domainW q = true) ∧
    restorePorts150.length = 150 ∧ restorePorts150.Nodup ∧ (∀ q ∈ restorePorts150, WindowCovered.domainW q = true) := by
  have hh := arch150_heads_ok
  have hscr_b : ∀ k < 134, 1556 ≤ archScratch150 k ∧ archScratch150 k < 1700 := fun k hk => by
    unfold archScratch150 e0P20 sbP20; split_ifs <;> (unfold Wire; omega)
  have hscr_inj : ∀ a b, archScratch150 a = archScratch150 b → a = b := fun a b e => by
    unfold archScratch150 e0P20 sbP20 at e; split_ifs at e <;> (unfold Wire at *; omega)
  have hscr_nd : ∀ n, ((List.range n).map archScratch150).Nodup := fun n =>
    List.Nodup.map_on (fun a _ b _ e => hscr_inj a b e) List.nodup_range
  have hscr_dom : ∀ n, n ≤ 134 → ∀ q ∈ (List.range n).map archScratch150, WindowCovered.domainW q = true := by
    intro n hn q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hk
    have b := hscr_b k (by omega)
    rw [WindowCovered.dom_iff]; unfold Wire at *; omega
  have hdisj : ∀ (hd : List Wire) (n : Nat), n ≤ 134 →
      hd.all (fun q => decide (q < 1556 ∨ 1700 ≤ q)) = true →
      ∀ a ∈ hd, ∀ b ∈ (List.range n).map archScratch150, a ≠ b := by
    intro hd n hn hall a ha b hb eq; subst eq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb; rw [List.mem_range] at hk
    have ha' := of_decide_eq_true (List.all_eq_true.mp hall _ ha)
    have sb := hscr_b k (by omega)
    unfold Wire at *; omega
  refine ⟨by rw [loadPorts150, List.length_append, hh.1]; simp,
    by rw [loadPorts150, List.nodup_append]; exact ⟨hh.2.1, hscr_nd 132, hdisj _ 132 (by decide) hh.2.2.2.1⟩,
    fun q hq => by
      rw [loadPorts150, List.mem_append] at hq
      rcases hq with hq | hq
      · exact List.all_eq_true.mp hh.2.2.1 q hq
      · exact hscr_dom 132 (by decide) q hq,
    by rw [restorePorts150, List.length_append, hh.2.2.2.2.1]; simp,
    by rw [restorePorts150, List.nodup_append]; exact ⟨hh.2.2.2.2.2.1, hscr_nd 134, hdisj _ 134 (by decide) hh.2.2.2.2.2.2.2.1⟩,
    fun q hq => by
      rw [restorePorts150, List.mem_append] at hq
      rcases hq with hq | hq
      · exact List.all_eq_true.mp hh.2.2.2.2.2.2.1 q hq
      · exact hscr_dom 134 (by decide) q hq⟩

theorem archive150To20_counts (d : Bool) :
    toffoliCount (archiveLoad150To20 d) = 42 ∧
    measurementCount (archiveLoad150To20 d) = 49 ∧
    toffoliCount (archiveRestore150To20 d) = (if d then 50 else 51) ∧
    measurementCount (archiveRestore150To20 d) = (if d then 43 else 44) := by
  have r1 : ∀ (f : Wire → Wire) (p : Program), toffoliCount (renameProgram f p) = toffoliCount p :=
    fun f p => (renameProgram_counts f p).1
  have r2 : ∀ (f : Wire → Wire) (p : Program), measurementCount (renameProgram f p) = measurementCount p :=
    fun f p => (renameProgram_counts f p).2
  obtain ⟨l1, l2, _, l4, l5, _⟩ := moves_counts 165 (e0P20 165 + 6)
  obtain ⟨m1, m2, _, m4, m5, _⟩ := moves240_counts
  have hL : toffoliCount (archiveLoad150To20 d) = toffoliCount (archiveLoad240 d) ∧
      measurementCount (archiveLoad150To20 d) = measurementCount (archiveLoad240 d) := by
    simp only [archiveLoad150To20, archiveLoad240, toffoliCount_append, measurementCount_append, r1, r2, l1, l2, m1, m2, and_self]
  have hR : toffoliCount (archiveRestore150To20 d) = toffoliCount (archiveRestore240 d) ∧
      measurementCount (archiveRestore150To20 d) = measurementCount (archiveRestore240 d) := by
    simp only [archiveRestore150To20, archiveRestore240, toffoliCount_append, measurementCount_append, r1, r2, l4, l5, m4, m5, and_self]
  cases d
  · exact ⟨hL.1.trans PartialCosts.part9.1, hL.2.trans PartialCosts.part9.2,
      hR.1.trans PartialCosts.part43.1, hR.2.trans PartialCosts.part43.2⟩
  · exact ⟨hL.1.trans PartialCosts.part25.1, hL.2.trans PartialCosts.part25.2,
      hR.1.trans PartialCosts.part57.1, hR.2.trans PartialCosts.part57.2⟩

attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1
  ReducedWindowArchives.restore0 ReducedWindowArchives.restore1 in
theorem archive150To20_phys (d : Bool) :
    GatePhysical (archiveLoad150To20 d) ∧ GatePhysical (archiveRestore150To20 d) := by
  have h := arch150_ok
  have hh := arch150_heads_ok
  exact ⟨WindowPhysicalW.appP (WindowPhysicalW.load_codec_phys _ h.2.1 h.1.ge d)
      (physical_of_proper _ (fun g hg => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hh.2.2.2.2.2.2.2.2.1 g hg)).1)).1,
    WindowPhysicalW.appP (WindowPhysicalW.restore_codec_phys _ h.2.2.2.2.1 h.2.2.2.1.ge d)
      (physical_of_proper _ (fun g hg => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hh.2.2.2.2.2.2.2.2.2 g hg)).1)).1⟩

attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1
  ReducedWindowArchives.restore0 ReducedWindowArchives.restore1 in
theorem archive150To20_cov (d : Bool) :
    WindowCovered.CoveredW (archiveLoad150To20 d) ∧ WindowCovered.CoveredW (archiveRestore150To20 d) := by
  have h := arch150_ok
  have hh := arch150_heads_ok
  have hmvL : AllW (fun q => WindowCovered.domainW q = true) (swapsG (moveLoadPairs 165)) :=
    fun g hg q hq => List.all_eq_true.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hh.2.2.2.2.2.2.2.2.1 g hg)).2 q hq
  have hmvR : AllW (fun q => WindowCovered.domainW q = true) (swapsG (moveRestorePairs 165 (e0P20 165 + 6))) :=
    fun g hg q hq => List.all_eq_true.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hh.2.2.2.2.2.2.2.2.2 g hg)).2 q hq
  constructor
  · rw [archiveLoad150To20]
    refine WindowCovered.appW (fun q hq => ?_) (allW_programs hmvL).1
    rw [renameProgram_support] at hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hplt : p < 155 := by cases d; exact Partial.load1_ports p hp; exact Partial.load0_ports p hp
    rw [List.getD_eq_getElem _ _ (by rw [h.1]; exact hplt)]
    exact h.2.2.1 _ (List.getElem_mem _)
  · rw [archiveRestore150To20]
    refine WindowCovered.appW (fun q hq => ?_) (allW_programs hmvR).1
    rw [renameProgram_support] at hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hplt : p < 150 := by cases d; exact Partial.restore1_ports p hp; exact Partial.restore0_ports p hp
    rw [List.getD_eq_getElem _ _ (by rw [h.2.2.2.1]; exact hplt)]
    exact h.2.2.2.2.2 _ (List.getElem_mem _)

/-! ### Section 2: Full Mixed 15/20-Tick Window Fold (`MixedWindow`) -/

namespace MixedWindow

def packW (d : Bool) (s t : Nat) : Program :=
  renameProgram (OB5.sig s) (Rolling1588.packAtTick d t)

def unpackW (d : Bool) (s t : Nat) : Program :=
  renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t)

def tickW (e : Nat) : Program :=
  renameProgram (OB5.sig e) (TickRanges.tick base e)

def recvW (e : Nat) : Program :=
  renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e)

/-- Standard 15-tick prefix blocks `j = 1..6` (`s = 60..135`) and suffix blocks `j = 21..24` (`s = 360..405`). -/
def block15F (d : Bool) (i j : Fin 26) : List Program :=
  [Shadow7.enterP j, Shadow7.routed j 0 1, packW d (start j) (start j - 10),
   Shadow7.archiveLoadP i d, Shadow7.routed j 1 14, CRTBarrel.leave j]

def block15R (d : Bool) (i j : Fin 26) : List Program :=
  [CRTBarrel.unleave j, Shadow7.unrouted j 1 14, Shadow7.archiveRestoreP i d,
   unpackW d (start j) (start j - 10), Shadow7.unrouted j 0 1, Shadow7.enterInvP j]

/-- 20-tick block `j : Fin 9` (`s = 165 + 20*j`): `j = 0` closes `s = 150` (1 pack + transition archive);
`j = 1..8` close `j - 1` (2 five-tick packs + 10-tick archive). -/
def block20F (d : Bool) (j : Fin 9) : List Program :=
  let s := start20 j
  if h : j.val = 0 then
    [enterP20 j, routed20 j 0 1, packW d 165 155, archiveLoad150To20 d, routed20 j 1 19, leaveP20Red j]
  else
    [enterP20 j, routed20 j 0 1, packW d s (s - 15), packW d s (s - 10),
     archiveLoadP20 ⟨j.val - 1, by omega⟩ d, routed20 j 1 19, leaveP20Red j]

def block20R (d : Bool) (j : Fin 9) : List Program :=
  let s := start20 j
  if h : j.val = 0 then
    [leaveInvP20Red j, unrouted20 j 1 19, archiveRestore150To20 d, unpackW d 165 155, unrouted20 j 0 1, enterInvP20 j]
  else
    [leaveInvP20Red j, unrouted20 j 1 19, archiveRestoreP20 ⟨j.val - 1, by omega⟩ d,
     unpackW d s (s - 10), unpackW d s (s - 15), unrouted20 j 0 1, enterInvP20 j]

def prefixPairs : List (Fin 26 × Fin 26) :=
  [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩),
   (⟨2, by decide⟩, ⟨3, by decide⟩), (⟨3, by decide⟩, ⟨4, by decide⟩),
   (⟨4, by decide⟩, ⟨5, by decide⟩), (⟨5, by decide⟩, ⟨6, by decide⟩)]

def suffixPairs : List (Fin 26 × Fin 26) :=
  [(⟨20, by decide⟩, ⟨21, by decide⟩), (⟨21, by decide⟩, ⟨22, by decide⟩),
   (⟨22, by decide⟩, ⟨23, by decide⟩), (⟨23, by decide⟩, ⟨24, by decide⟩)]

def j0 : Fin 26 := ⟨0, by decide⟩
def j6 : Fin 26 := ⟨6, by decide⟩
def j7 : Fin 26 := ⟨7, by decide⟩
def j20 : Fin 26 := ⟨20, by decide⟩
def k8 : Fin 9 := ⟨8, by decide⟩

def forwardL (d : Bool) : List Program :=
  [Shadow7.portalP 45, Shadow7.enterP j0, Shadow7.routed j0 0 1, packW d 45 45,
   Shadow7.routed j0 1 14, CRTBarrel.leave j0] ++
  (prefixPairs.flatMap fun p => block15F d p.1 p.2) ++
  [Shadow7.enterP j7, Shadow7.routed j7 0 1, packW d 150 140,
   Shadow7.archiveLoadP j6 d, Shadow7.routed j7 1 14, leave150To20Red] ++
  ((List.finRange 9).flatMap (block20F d)) ++
  [Shadow7.enterP j20, Shadow7.routed j20 0 1, packW d 345 330, packW d 345 335,
   archiveLoadP20 k8 d, Shadow7.routed j20 1 14, CRTBarrel.leave j20] ++
  (suffixPairs.flatMap fun p => block15F d p.1 p.2) ++
  [Shadow7.parkP 420, Shadow7.portalInvP 420, tickW 420, packW d 420 410, Shadow7.exitLoadP 420 d]

def reverseL (d : Bool) : List Program :=
  [Shadow7.exitRestoreP 420 d, unpackW d 420 410, recvW 420, Shadow7.portalP 420, Shadow7.parkInvP 420] ++
  (suffixPairs.reverse.flatMap fun p => block15R d p.1 p.2) ++
  [CRTBarrel.unleave j20, Shadow7.unrouted j20 1 14, archiveRestoreP20 k8 d,
   unpackW d 345 335, unpackW d 345 330, Shadow7.unrouted j20 0 1, Shadow7.enterInvP j20] ++
  ((List.finRange 9).reverse.flatMap (block20R d)) ++
  [leaveInv150To20Red, Shadow7.unrouted j7 1 14, Shadow7.archiveRestoreP j6 d,
   unpackW d 150 140, Shadow7.unrouted j7 0 1, Shadow7.enterInvP j7] ++
  (prefixPairs.reverse.flatMap fun p => block15R d p.1 p.2) ++
  [CRTBarrel.unleave j0, Shadow7.unrouted j0 1 14, unpackW d 45 45,
   Shadow7.unrouted j0 0 1, Shadow7.enterInvP j0, Shadow7.portalInvP 45]

def forwardMixed (d : Bool) : Program := (forwardL d).flatten
def reverseMixed (d : Bool) : Program := (reverseL d).flatten

/-! Exact counts of 15-tick `CRTBarrel.leave`/`unleave` (standalone, using `Shadow7.leaveMove_counts`). -/

private theorem leave15_counts (j : Fin 26) (hj : j.val ≤ 24) :
    toffoliCount (CRTBarrel.leave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3 * Shadow7.lowsP (start j) + 99 +
        CRTBarrel.barrelT (start j) false ∧
    toffoliCount (CRTBarrel.unleave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2 * Shadow7.lowsP (start j) + 131 +
        CRTBarrel.barrelT (start j) true ∧
    measurementCount (CRTBarrel.leave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 92 +
        CRTBarrel.barrelM (start j) false ∧
    measurementCount (CRTBarrel.unleave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2 * Shadow7.lowsP (start j) + 60 +
        CRTBarrel.barrelM (start j) true := by
  obtain ⟨h1, h2, h3, h4, _, _⟩ := CRTWindow.leave_metrics j (Nat.zero_le _) hj
  exact ⟨h1, h2, h3, h4⟩

private theorem archive15_counts (j : Fin 26) (d : Bool) :
    toffoliCount (Shadow7.archiveLoadP j d) = 42 ∧
    measurementCount (Shadow7.archiveLoadP j d) = 49 ∧
    toffoliCount (Shadow7.archiveRestoreP j d) = (if d then 50 else 51) ∧
    measurementCount (Shadow7.archiveRestoreP j d) = (if d then 43 else 44) := by
  have h := Shadow7.archive_counts j 0 d
  cases d
  · exact ⟨h.1.trans PartialCosts.part9.1, h.2.1.trans PartialCosts.part9.2,
      h.2.2.2.1.trans PartialCosts.part43.1, h.2.2.2.2.1.trans PartialCosts.part43.2⟩
  · exact ⟨h.1.trans PartialCosts.part25.1, h.2.1.trans PartialCosts.part25.2,
      h.2.2.2.1.trans PartialCosts.part57.1, h.2.2.2.2.1.trans PartialCosts.part57.2⟩

private theorem exitArch_counts (e : Nat) (d : Bool) :
    toffoliCount (Shadow7.exitLoadP e d) = 42 ∧
    measurementCount (Shadow7.exitLoadP e d) = 49 ∧
    toffoliCount (Shadow7.exitRestoreP e d) = (if d then 50 else 51) ∧
    measurementCount (Shadow7.exitRestoreP e d) = (if d then 43 else 44) := by
  have h := Shadow7.archive_counts j0 e d
  cases d
  · exact ⟨h.2.2.2.2.2.2.1.trans PartialCosts.part9.1, h.2.2.2.2.2.2.2.1.trans PartialCosts.part9.2,
      h.2.2.2.2.2.2.2.2.2.1.trans PartialCosts.part43.1, h.2.2.2.2.2.2.2.2.2.2.1.trans PartialCosts.part43.2⟩
  · exact ⟨h.2.2.2.2.2.2.1.trans PartialCosts.part25.1, h.2.2.2.2.2.2.2.1.trans PartialCosts.part25.2,
      h.2.2.2.2.2.2.2.2.2.1.trans PartialCosts.part57.1, h.2.2.2.2.2.2.2.2.2.2.1.trans PartialCosts.part57.2⟩

private theorem archive20_tm (j : Fin 9) (d : Bool) :
    toffoliCount (archiveLoadP20 j d) = 42 ∧
    measurementCount (archiveLoadP20 j d) = 49 ∧
    toffoliCount (archiveRestoreP20 j d) = (if d then 50 else 51) ∧
    measurementCount (archiveRestoreP20 j d) = (if d then 43 else 44) := by
  have h := archive20_counts j d
  cases d
  · exact ⟨h.1.trans PartialCosts.part9.1, h.2.1.trans PartialCosts.part9.2,
      h.2.2.2.1.trans PartialCosts.part43.1, h.2.2.2.2.1.trans PartialCosts.part43.2⟩
  · exact ⟨h.1.trans PartialCosts.part25.1, h.2.1.trans PartialCosts.part25.2,
      h.2.2.2.1.trans PartialCosts.part57.1, h.2.2.2.2.1.trans PartialCosts.part57.2⟩

private theorem packW_counts (d : Bool) (s t : Nat) (h5 : t ≠ 5) (hd : History5.packDue t = true) :
    toffoliCount (packW d s t) = 9 ∧ measurementCount (packW d s t) = 4 ∧
    toffoliCount (unpackW d s t) = 11 ∧ measurementCount (unpackW d s t) = 2 :=
  WindowFold.pack_counts d s t h5 hd

private theorem block15F_counts (d : Bool) (i j : Fin 26) (hj : j.val ≤ 24)
    (h5 : start j - 10 ≠ 5) (hd : History5.packDue (start j - 10) = true) :
    ((block15F d i j).map toffoliCount).sum =
      57 + 30 * (Shadow7.smallBits j + 17) +
      (Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3 * Shadow7.lowsP (start j) + 99 +
        CRTBarrel.barrelT (start j) false) ∧
    ((block15F d i j).map measurementCount).sum =
      55 + 15 * (Shadow7.smallBits j + 17) +
      (Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 92 +
        CRTBarrel.barrelM (start j) false) := by
  have e := Shadow7.enter_counts j
  have r0 := WindowFold7.routed_counts j 0 1 (by decide)
  have r1 := WindowFold7.routed_counts j 1 14 (by decide)
  have pk := packW_counts d (start j) (start j - 10) h5 hd
  have ar := archive15_counts i d
  have lv := leave15_counts j hj
  simp only [block15F, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    e.1, e.2.2.1, r0.1, r0.2.1, r1.1, r1.2.1, pk.1, pk.2.1, ar.1, ar.2.1, lv.1, lv.2.2.1]
  exact ⟨by omega, by omega⟩

private theorem block15R_counts (d : Bool) (i j : Fin 26) (hj : j.val ≤ 24)
    (h5 : start j - 10 ≠ 5) (hd : History5.packDue (start j - 10) = true) :
    ((block15R d i j).map toffoliCount).sum =
      (if d then 67 else 68) + 15 * (2 * (Shadow7.smallBits j + 17) - 1) +
      (Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2 * Shadow7.lowsP (start j) + 131 +
        CRTBarrel.barrelT (start j) true) ∧
    ((block15R d i j).map measurementCount).sum =
      (if d then 48 else 49) + 15 * (Shadow7.smallBits j + 17) +
      (Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2 * Shadow7.lowsP (start j) + 60 +
        CRTBarrel.barrelM (start j) true) := by
  have e := Shadow7.enter_counts j
  have r0 := WindowFold7.routed_counts j 0 1 (by decide)
  have r1 := WindowFold7.routed_counts j 1 14 (by decide)
  have pk := packW_counts d (start j) (start j - 10) h5 hd
  have ar := archive15_counts i d
  have lv := leave15_counts j hj
  simp only [block15R, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    e.2.1, e.2.2.2.1, r0.2.2.1, r0.2.2.2, r1.2.2.1, r1.2.2.2, pk.2.2.1, pk.2.2.2, ar.2.2.1, ar.2.2.2,
    lv.2.1, lv.2.2.2]
  cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> exact ⟨by omega, by omega⟩

def b20TF (j : Fin 9) : Nat :=
  let s := start20 j
  (if j.val = 0 then 57 else 66) + 40 * (sbP20 s + 22) +
  (wpP20 s + liveW20 s + 3 * lowsP20 s + 131 + barrel20T s false)

def b20TR (d : Bool) (j : Fin 9) : Nat :=
  let s := start20 j
  (if j.val = 0 then (if d then 67 else 68) else (if d then 78 else 79)) + 20 * (2 * (sbP20 s + 22) - 1) +
  (wpP20 s + liveW20 s + 2 * lowsP20 s + 173 + barrel20T s true)

def b20MF (j : Fin 9) : Nat :=
  let s := start20 j
  (if j.val = 0 then 55 else 59) + 20 * (sbP20 s + 22) +
  (wpP20 s + liveW20 s + lowsP20 s + 122 + barrel20M s false)

def b20MR (d : Bool) (j : Fin 9) : Nat :=
  let s := start20 j
  (if j.val = 0 then (if d then 48 else 49) else (if d then 50 else 51)) + 20 * (sbP20 s + 22) +
  (wpP20 s + liveW20 s + 2 * lowsP20 s + 80 + barrel20M s true)

private theorem block20F_counts (d : Bool) (j : Fin 9) :
    ((block20F d j).map toffoliCount).sum = b20TF j ∧
    ((block20F d j).map measurementCount).sum = b20MF j := by
  have e := enter20_counts j
  have r0 := routed20_counts j 0 1 (by decide)
  have r1 := routed20_counts j 1 19 (by decide)
  have lv := leave20Red_counts j
  by_cases h0 : j.val = 0
  · have pk := packW_counts d 165 155 (by decide) (by decide)
    have ar := archive150To20_counts d
    simp only [block20F, h0, ↓reduceDIte, ↓reduceIte, b20TF, b20MF, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, e.1, e.2.2.1, r0.1, r0.2.1, r1.1, r1.2.1, pk.1, pk.2.1,
      ar.1, ar.2.1, lv.1, lv.2.2.1, smallBits20]
    exact ⟨by omega, by omega⟩
  · have hs1 : start20 j - 15 ≠ 5 := by unfold start20; omega
    have hs2 : start20 j - 10 ≠ 5 := by unfold start20; omega
    have hd1 : History5.packDue (start20 j - 15) = true := by
      simp only [History5.packDue, start20, decide_eq_true_eq]; omega
    have hd2 : History5.packDue (start20 j - 10) = true := by
      simp only [History5.packDue, start20, decide_eq_true_eq]; omega
    have pk1 := packW_counts d (start20 j) (start20 j - 15) hs1 hd1
    have pk2 := packW_counts d (start20 j) (start20 j - 10) hs2 hd2
    have ar := archive20_tm ⟨j.val - 1, by omega⟩ d
    simp only [block20F, h0, ↓reduceDIte, ↓reduceIte, b20TF, b20MF, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, e.1, e.2.2.1, r0.1, r0.2.1, r1.1, r1.2.1,
      pk1.1, pk1.2.1, pk2.1, pk2.2.1, ar.1, ar.2.1, lv.1, lv.2.2.1, smallBits20]
    exact ⟨by omega, by omega⟩

private theorem block20R_counts (d : Bool) (j : Fin 9) :
    ((block20R d j).map toffoliCount).sum = b20TR d j ∧
    ((block20R d j).map measurementCount).sum = b20MR d j := by
  have e := enter20_counts j
  have r0 := routed20_counts j 0 1 (by decide)
  have r1 := routed20_counts j 1 19 (by decide)
  have lv := leave20Red_counts j
  by_cases h0 : j.val = 0
  · have pk := packW_counts d 165 155 (by decide) (by decide)
    have ar := archive150To20_counts d
    simp only [block20R, h0, ↓reduceDIte, ↓reduceIte, b20TR, b20MR, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, e.2.1, e.2.2.2.1, r0.2.2.1, r0.2.2.2, r1.2.2.1, r1.2.2.2,
      pk.2.2.1, pk.2.2.2, ar.2.2.1, ar.2.2.2, lv.2.1, lv.2.2.2.1, smallBits20]
    cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> exact ⟨by omega, by omega⟩
  · have hs1 : start20 j - 15 ≠ 5 := by unfold start20; omega
    have hs2 : start20 j - 10 ≠ 5 := by unfold start20; omega
    have hd1 : History5.packDue (start20 j - 15) = true := by
      simp only [History5.packDue, start20, decide_eq_true_eq]; omega
    have hd2 : History5.packDue (start20 j - 10) = true := by
      simp only [History5.packDue, start20, decide_eq_true_eq]; omega
    have pk1 := packW_counts d (start20 j) (start20 j - 15) hs1 hd1
    have pk2 := packW_counts d (start20 j) (start20 j - 10) hs2 hd2
    have ar := archive20_tm ⟨j.val - 1, by omega⟩ d
    simp only [block20R, h0, ↓reduceDIte, ↓reduceIte, b20TR, b20MR, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, e.2.1, e.2.2.2.1, r0.2.2.1, r0.2.2.2, r1.2.2.1, r1.2.2.2,
      pk1.2.2.1, pk1.2.2.2, pk2.2.2.1, pk2.2.2.2, ar.2.2.1, ar.2.2.2, lv.2.1, lv.2.2.2.1, smallBits20]
    cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> exact ⟨by omega, by omega⟩

def b15TF (j : Fin 26) : Nat :=
  57 + 30 * (Shadow7.smallBits j + 17) +
  (Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3 * Shadow7.lowsP (start j) + 99 +
    CRTBarrel.barrelT (start j) false)

def b15TR (d : Bool) (j : Fin 26) : Nat :=
  (if d then 67 else 68) + 15 * (2 * (Shadow7.smallBits j + 17) - 1) +
  (Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2 * Shadow7.lowsP (start j) + 131 +
    CRTBarrel.barrelT (start j) true)

def b15MF (j : Fin 26) : Nat :=
  55 + 15 * (Shadow7.smallBits j + 17) +
  (Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 92 +
    CRTBarrel.barrelM (start j) false)

def b15MR (d : Bool) (j : Fin 26) : Nat :=
  (if d then 48 else 49) + 15 * (Shadow7.smallBits j + 17) +
  (Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2 * Shadow7.lowsP (start j) + 60 +
    CRTBarrel.barrelM (start j) true)

private theorem sum_flatMap_eq {α : Type} (m : Program → Nat) (f : α → List Program) (g : α → Nat)
    (xs : List α) (h : ∀ a ∈ xs, ((f a).map m).sum = g a) :
    ((xs.flatMap f).map m).sum = (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    rw [h a (by simp), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

private theorem mixed_sum_vals (d : Bool) :
    (4 * Shadow7.wpP 45 - 2 + 6 + 30 * (Shadow7.smallBits j0 + 17) + 9 +
      (Shadow7.wpP 45 + Shadow7.liveW 45 + 3 * Shadow7.lowsP 45 + 99 + CRTBarrel.barrelT 45 false)) +
    (prefixPairs.map (fun p => b15TF p.2)).sum +
    (6 + 30 * (Shadow7.smallBits j7 + 17) + 9 + 42 + 474) +
    ((List.finRange 9).map b20TF).sum +
    (6 + 30 * (Shadow7.smallBits j20 + 17) + 9 + 9 + 42 +
      (Shadow7.wpP 345 + Shadow7.liveW 345 + 3 * Shadow7.lowsP 345 + 99 + CRTBarrel.barrelT 345 false)) +
    (suffixPairs.map (fun p => b15TF p.2)).sum +
    (0 + (5 * Shadow7.wpP 420 - 4) + WindowParams.tickT 420 + 9 + 42) = 127777 ∧
    (4 * Shadow7.wpP 45 - 7 + 2 + 15 * (Shadow7.smallBits j0 + 17) + 4 +
      (Shadow7.wpP 45 + Shadow7.liveW 45 + Shadow7.lowsP 45 + 92 + CRTBarrel.barrelM 45 false)) +
    (prefixPairs.map (fun p => b15MF p.2)).sum +
    (2 + 15 * (Shadow7.smallBits j7 + 17) + 4 + 49 + 293) +
    ((List.finRange 9).map b20MF).sum +
    (2 + 15 * (Shadow7.smallBits j20 + 17) + 4 + 4 + 49 +
      (Shadow7.wpP 345 + Shadow7.liveW 345 + Shadow7.lowsP 345 + 92 + CRTBarrel.barrelM 345 false)) +
    (suffixPairs.map (fun p => b15MF p.2)).sum +
    (0 + (3 * Shadow7.wpP 420 - 5) + WindowParams.tickM 420 + 4 + 49) = 66171 ∧
    ((if d then 50 else 51) + 11 + WindowParams.recvT 420 + (4 * Shadow7.wpP 420 - 2) + 0) +
    (suffixPairs.reverse.map (fun p => b15TR d p.2)).sum +
    ((Shadow7.wpP 345 + Shadow7.liveW 345 + 2 * Shadow7.lowsP 345 + 131 + CRTBarrel.barrelT 345 true) +
      15 * (2 * (Shadow7.smallBits j20 + 17) - 1) + (if d then 50 else 51) + 11 + 11 + 6) +
    ((List.finRange 9).reverse.map (b20TR d)).sum +
    (494 + 15 * (2 * (Shadow7.smallBits j7 + 17) - 1) + (if d then 50 else 51) + 11 + 6) +
    (prefixPairs.reverse.map (fun p => b15TR d p.2)).sum +
    ((Shadow7.wpP 45 + Shadow7.liveW 45 + 2 * Shadow7.lowsP 45 + 131 + CRTBarrel.barrelT 45 true) +
      15 * (2 * (Shadow7.smallBits j0 + 17) - 1) + 11 + 6 + (5 * Shadow7.wpP 45 - 4)) = (if d then 128182 else 128204) ∧
    ((if d then 43 else 44) + 2 + WindowParams.recvM 420 + (4 * Shadow7.wpP 420 - 7) + 0) +
    (suffixPairs.reverse.map (fun p => b15MR d p.2)).sum +
    ((Shadow7.wpP 345 + Shadow7.liveW 345 + 2 * Shadow7.lowsP 345 + 60 + CRTBarrel.barrelM 345 true) +
      15 * (Shadow7.smallBits j20 + 17) + (if d then 43 else 44) + 2 + 2 + 3) +
    ((List.finRange 9).reverse.map (b20MR d)).sum +
    (273 + 15 * (Shadow7.smallBits j7 + 17) + (if d then 43 else 44) + 2 + 3) +
    (prefixPairs.reverse.map (fun p => b15MR d p.2)).sum +
    ((Shadow7.wpP 45 + Shadow7.liveW 45 + 2 * Shadow7.lowsP 45 + 60 + CRTBarrel.barrelM 45 true) +
      15 * (Shadow7.smallBits j0 + 17) + 2 + 3 + (3 * Shadow7.wpP 45 - 5)) = (if d then 65456 else 65478) := by
  cases d <;> decide +kernel

attribute [local irreducible] toffoliCount measurementCount Shadow7.enterP Shadow7.enterInvP
  Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP Shadow7.routed Shadow7.unrouted
  Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.exitLoadP Shadow7.exitRestoreP
  CRTBarrel.leave CRTBarrel.unleave enterP20 enterInvP20 leaveP20Red leaveInvP20Red routed20 unrouted20
  archiveLoadP20 archiveRestoreP20 leave150To20Red leaveInv150To20Red archiveLoad150To20 archiveRestore150To20
  packW unpackW TickRanges.tick W.ReverseCarry.compactReceiverTick in
theorem mixed_counts (d : Bool) :
    toffoliCount (forwardMixed d) = 127777 ∧
    toffoliCount (reverseMixed d) = (if d then 128182 else 128204) ∧
    measurementCount (forwardMixed d) = 66171 ∧
    measurementCount (reverseMixed d) = (if d then 65456 else 65478) := by
  have hfT := measure_flatten toffoliCount toffoliCount_append (forwardL d)
  have hrT := measure_flatten toffoliCount toffoliCount_append (reverseL d)
  have hfM := measure_flatten measurementCount measurementCount_append (forwardL d)
  have hrM := measure_flatten measurementCount measurementCount_append (reverseL d)
  have p45 := Shadow7.portal_counts 45 (by decide)
  have p420 := Shadow7.portal_counts 420 (by decide)
  have pk420 := Shadow7.park_counts 420
  have t420 := WindowParams.tick_closed 420 (by decide)
  have ex := exitArch_counts 420 d
  have e0 := Shadow7.enter_counts j0
  have r0a := WindowFold7.routed_counts j0 0 1 (by decide)
  have r0b := WindowFold7.routed_counts j0 1 14 (by decide)
  have l0 := leave15_counts j0 (by decide)
  have e7 := Shadow7.enter_counts j7
  have r7a := WindowFold7.routed_counts j7 0 1 (by decide)
  have r7b := WindowFold7.routed_counts j7 1 14 (by decide)
  have a6 := archive15_counts j6 d
  have l7 := leave150To20Red_counts
  have e20 := Shadow7.enter_counts j20
  have r20a := WindowFold7.routed_counts j20 0 1 (by decide)
  have r20b := WindowFold7.routed_counts j20 1 14 (by decide)
  have a8 := archive20_tm k8 d
  have l20 := leave15_counts j20 (by decide)
  have pk45 := packW_counts d 45 45 (by decide) (by decide)
  have pk140 := packW_counts d 150 140 (by decide) (by decide)
  have pk330 := packW_counts d 345 330 (by decide) (by decide)
  have pk335 := packW_counts d 345 335 (by decide) (by decide)
  have pk410 := packW_counts d 420 410 (by decide) (by decide)
  have hp15 : ∀ p ∈ prefixPairs, p.2.val ≤ 24 ∧ start p.2 - 10 ≠ 5 ∧ History5.packDue (start p.2 - 10) = true := by decide
  have hs15 : ∀ p ∈ suffixPairs, p.2.val ≤ 24 ∧ start p.2 - 10 ≠ 5 ∧ History5.packDue (start p.2 - 10) = true := by decide
  have hprFT := sum_flatMap_eq toffoliCount (fun p : Fin 26 × Fin 26 => block15F d p.1 p.2) (fun p => b15TF p.2) prefixPairs
    (fun p hp => (block15F_counts d p.1 p.2 (hp15 p hp).1 (hp15 p hp).2.1 (hp15 p hp).2.2).1)
  have hprFM := sum_flatMap_eq measurementCount (fun p : Fin 26 × Fin 26 => block15F d p.1 p.2) (fun p => b15MF p.2) prefixPairs
    (fun p hp => (block15F_counts d p.1 p.2 (hp15 p hp).1 (hp15 p hp).2.1 (hp15 p hp).2.2).2)
  have hsuFT := sum_flatMap_eq toffoliCount (fun p : Fin 26 × Fin 26 => block15F d p.1 p.2) (fun p => b15TF p.2) suffixPairs
    (fun p hp => (block15F_counts d p.1 p.2 (hs15 p hp).1 (hs15 p hp).2.1 (hs15 p hp).2.2).1)
  have hsuFM := sum_flatMap_eq measurementCount (fun p : Fin 26 × Fin 26 => block15F d p.1 p.2) (fun p => b15MF p.2) suffixPairs
    (fun p hp => (block15F_counts d p.1 p.2 (hs15 p hp).1 (hs15 p hp).2.1 (hs15 p hp).2.2).2)
  have hprRT := sum_flatMap_eq toffoliCount (fun p : Fin 26 × Fin 26 => block15R d p.1 p.2) (fun p => b15TR d p.2) prefixPairs.reverse
    (fun p hp => by have h := hp15 p (List.mem_reverse.mp hp); exact (block15R_counts d p.1 p.2 h.1 h.2.1 h.2.2).1)
  have hprRM := sum_flatMap_eq measurementCount (fun p : Fin 26 × Fin 26 => block15R d p.1 p.2) (fun p => b15MR d p.2) prefixPairs.reverse
    (fun p hp => by have h := hp15 p (List.mem_reverse.mp hp); exact (block15R_counts d p.1 p.2 h.1 h.2.1 h.2.2).2)
  have hsuRT := sum_flatMap_eq toffoliCount (fun p : Fin 26 × Fin 26 => block15R d p.1 p.2) (fun p => b15TR d p.2) suffixPairs.reverse
    (fun p hp => by have h := hs15 p (List.mem_reverse.mp hp); exact (block15R_counts d p.1 p.2 h.1 h.2.1 h.2.2).1)
  have hsuRM := sum_flatMap_eq measurementCount (fun p : Fin 26 × Fin 26 => block15R d p.1 p.2) (fun p => b15MR d p.2) suffixPairs.reverse
    (fun p hp => by have h := hs15 p (List.mem_reverse.mp hp); exact (block15R_counts d p.1 p.2 h.1 h.2.1 h.2.2).2)
  have h20FT := sum_flatMap_eq toffoliCount (block20F d) b20TF (List.finRange 9) (fun j _ => (block20F_counts d j).1)
  have h20FM := sum_flatMap_eq measurementCount (block20F d) b20MF (List.finRange 9) (fun j _ => (block20F_counts d j).2)
  have h20RT := sum_flatMap_eq toffoliCount (block20R d) (b20TR d) (List.finRange 9).reverse (fun j _ => (block20R_counts d j).1)
  have h20RM := sum_flatMap_eq measurementCount (block20R d) (b20MR d) (List.finRange 9).reverse (fun j _ => (block20R_counts d j).2)
  have mv := mixed_sum_vals d
  have hs0 : start j0 = 45 := rfl
  have hs20 : start j20 = 345 := rfl
  rw [hs0] at l0; rw [hs20] at l20
  change toffoliCount (tickW 420) = _ ∧ measurementCount (tickW 420) = _ ∧
    toffoliCount (recvW 420) = _ ∧ measurementCount (recvW 420) = _ at t420
  rw [forwardMixed, reverseMixed, hfT, hrT, hfM, hrM]
  simp only [forwardL, reverseL,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hprFT, hprFM, hsuFT, hsuFM, hprRT, hprRM, hsuRT, hsuRM, h20FT, h20FM, h20RT, h20RM,
    p45.1, p45.2.1, p45.2.2.1, p45.2.2.2.1, p420.1, p420.2.1, p420.2.2.1, p420.2.2.2.1,
    pk420.1, pk420.2.1, pk420.2.2.1, pk420.2.2.2.1, t420.1, t420.2.1, t420.2.2.1, t420.2.2.2,
    ex.1, ex.2.1, ex.2.2.1, ex.2.2.2, e0.1, e0.2.1, e0.2.2.1, e0.2.2.2.1,
    r0a.1, r0a.2.1, r0a.2.2.1, r0a.2.2.2, r0b.1, r0b.2.1, r0b.2.2.1, r0b.2.2.2,
    l0.1, l0.2.1, l0.2.2.1, l0.2.2.2, e7.1, e7.2.1, e7.2.2.1, e7.2.2.2.1,
    r7a.1, r7a.2.1, r7a.2.2.1, r7a.2.2.2, r7b.1, r7b.2.1, r7b.2.2.1, r7b.2.2.2,
    a6.1, a6.2.1, a6.2.2.1, a6.2.2.2, l7.1, l7.2.1, l7.2.2.1, l7.2.2.2.1,
    e20.1, e20.2.1, e20.2.2.1, e20.2.2.2.1, r20a.1, r20a.2.1, r20a.2.2.1, r20a.2.2.2,
    r20b.1, r20b.2.1, r20b.2.2.1, r20b.2.2.2, a8.1, a8.2.1, a8.2.2.1, a8.2.2.2,
    l20.1, l20.2.1, l20.2.2.1, l20.2.2.2, pk45.1, pk45.2.1, pk45.2.2.1, pk45.2.2.2,
    pk140.1, pk140.2.1, pk140.2.2.1, pk140.2.2.2, pk330.1, pk330.2.1, pk330.2.2.1, pk330.2.2.2,
    pk335.1, pk335.2.1, pk335.2.2.1, pk335.2.2.2, pk410.1, pk410.2.1, pk410.2.2.1, pk410.2.2.2]
  cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] at mv ⊢ <;> exact ⟨by omega, by omega, by omega, by omega⟩

/-! Physicality and domain coverage of `forwardMixed` and `reverseMixed`. -/

private theorem routed15_phys (j : Fin 26) (a n : Nat) (h : a + n ≤ 15) :
    GatePhysical (Shadow7.routed j a n) ∧ GatePhysical (Shadow7.unrouted j a n) := by
  induction n generalizing a with
  | zero => simp [Shadow7.routed, Shadow7.unrouted, GatePhysical]
  | succ n ih =>
    have ha : a < 15 := by omega
    have valid := IntegerPacket.ok (Shadow7.shape j) ⟨a, ha⟩
    have enough : 1 ≤ (IntegerPacket.ports (Shadow7.shape j) a).half.length := by simp [SkywalkIntegerLayout.half]
    have narrow := narrowTicks_physical (IntegerPacket.ports (Shadow7.shape j) a) 1 valid (by decide) enough
    simp only [narrowSkywalkTick, narrowSkywalkUntick, gatePhysical_append] at narrow
    have nd := (IntegerPacket.ports (Shadow7.shape j) a).record_nodup valid
    have fresh := (List.nodup_cons.mp nd).1
    have sx : (IntegerPacket.ports (Shadow7.shape j) a).ext ≠ (IntegerPacket.ports (Shadow7.shape j) a).history := by
      intro e; apply fresh; rw [← e]; simp [SkywalkIntegerLayout.half]
    have sy : (IntegerPacket.ports (Shadow7.shape j) a).bSign ≠ (IntegerPacket.ports (Shadow7.shape j) a).history := by
      intro e; apply fresh; rw [← e]; simp [SkywalkIntegerLayout.b, SkywalkIntegerLayout.bh]
    have toggle : GatePhysical (skywalkSignToggle (IntegerPacket.ports (Shadow7.shape j) a).ext
        (IntegerPacket.ports (Shadow7.shape j) a).bSign (IntegerPacket.ports (Shadow7.shape j) a).history) := by
      simp [skywalkSignToggle, GatePhysical, PhysicalInstr, ProperGate, sx, sy]
    have arith := signedWords_physical _ _ _ _ nd
    have tick1 : GatePhysical (skywalkIntegerTick (IntegerPacket.ports (Shadow7.shape j) a)) := by
      simp only [skywalkIntegerTick, signedRecord, gatePhysical_append]
      exact ⟨⟨⟨narrow.1.1.1.1, narrow.1.1.1.2⟩, ⟨⟨toggle, arith.1⟩, toggle⟩⟩, narrow.1.2⟩
    have untick := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_physical (IntegerPacket.ports (Shadow7.shape j) a) _
      valid (by simp [SkywalkIntegerLayout.half]) le_rfl
    have range := (Shadow7.shape j).rangeEnd
    change start j + 15 ≤ 510 at range
    have inj := OB5.sig_injective (start j + a) (by omega)
    have tail := ih (a + 1) (by omega)
    exact ⟨(gatePhysical_append _ _).2 ⟨gatePhysical_rename _ inj _ tick1, tail.1⟩,
      (gatePhysical_append _ _).2 ⟨tail.2, gatePhysical_rename _ inj _ untick⟩⟩

private theorem leave15_phys (j : Fin 26) (hj : j.val ≤ 24) :
    GatePhysical (CRTBarrel.leave j) ∧ GatePhysical (CRTBarrel.unleave j) :=
  CRTWindow.leave_phys j (Nat.zero_le _) hj

private theorem leave15_cov (j : Fin 26) (hj : j.val ≤ 24) :
    WindowCovered.CoveredW (CRTBarrel.leave j) ∧ WindowCovered.CoveredW (CRTBarrel.unleave j) :=
  CRTWindow.leave_cov j (Nat.zero_le _) hj

private theorem archive15_phys (j : Fin 26) (hj : j.val ≤ 24) (d : Bool) :
    GatePhysical (Shadow7.archiveLoadP j d) ∧ GatePhysical (Shadow7.archiveRestoreP j d) := by
  have lo : 60 ≤ start j + 15 := by simp only [start]; omega
  have hi : start j + 15 ≤ 420 := by simp only [start]; omega
  have nl : (Shadow7.loadPortsWP (start j + 15) (Shadow7.e0P (start j + 15) + 6)).Nodup :=
    (List.nodup_append.mp (ArchiveJ7.rawNodup j hj)).1
  have nr : (Shadow7.restorePortsWP (start j + 15)).Nodup :=
    (List.nodup_append.mp (ArchiveJ7.codeNodup j hj)).1
  have mL : GatePhysical (moveLoadP (start j + 15)) := by
    rw [moveLoadP]; refine (physical_of_proper _ (proper_swapsG _ ?_)).1
    simp only [moveLoadPairs, List.forall_mem_cons, List.forall_mem_nil, and_true, ne_eq, OB5.sig]
    and_intros <;> first | (intro x hx; cases hx) | (unfold Wire; split_ifs <;> omega)
  have fl : 1563 ≤ Shadow7.e0P (start j + 15) + 6 := by unfold Shadow7.e0P Shadow7.sbP; omega
  have mR : GatePhysical (moveRestoreP (start j + 15) (Shadow7.e0P (start j + 15) + 6)) := by
    rw [moveRestoreP]; refine (physical_of_proper _ (proper_swapsG _ ?_)).1
    simp only [moveRestorePairs, List.forall_mem_cons, List.forall_mem_nil, and_true, ne_eq, OB5.sig]
    and_intros <;> first | (intro x hx; cases hx) | (unfold Wire; split_ifs <;> omega) | (unfold Wire; omega)
  exact ⟨WindowPhysicalW.appP (WindowPhysicalW.load_codec_phys _ nl (by rw [Shadow7.loadPortsWP_length]) d) mL,
    WindowPhysicalW.appP (WindowPhysicalW.restore_codec_phys _ nr (by rw [Shadow7.restorePortsWP_length]) d) mR⟩

private theorem archive15_cov (j : Fin 26) (hj : j.val ≤ 24) (d : Bool) :
    WindowCovered.CoveredW (Shadow7.archiveLoadP j d) ∧ WindowCovered.CoveredW (Shadow7.archiveRestoreP j d) := by
  have lo : 60 ≤ start j + 15 := by simp only [start]; omega
  have hi : start j + 15 ≤ 420 := by simp only [start]; omega
  have dom : ∀ q, archFootW (start j + 15) (Shadow7.e0P (start j + 15) + 6) q → WindowCovered.domainW q = true :=
    fun q h => by rw [WindowCovered.dom_iff]; unfold archFootW Shadow7.e0P Shadow7.sbP at h; omega
  exact ⟨fun q hq => dom q (Shadow7.archiveLoadP_wiresW j d hj q hq),
    fun q hq => dom q (Shadow7.archiveRestoreP_wiresW j d hj q hq)⟩

private theorem routed15_cov (j : Fin 26) (hj : j.val ≤ 24) (a n : Nat) (bound : a + n ≤ 15) :
    WindowCovered.CoveredW (Shadow7.routed j a n) ∧ WindowCovered.CoveredW (Shadow7.unrouted j a n) := by
  induction n generalizing a with
  | zero => constructor <;> intro q h <;> simp [Shadow7.routed, Shadow7.unrouted, wires] at h
  | succ n ih =>
    have ha : a < 15 := by omega
    have step := skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (Shadow7.shape j) ⟨a, ha⟩)
    have ustep := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_support (IntegerPacket.ports (Shadow7.shape j) a) _
      (IntegerPacket.ok (Shadow7.shape j) ⟨a, ha⟩) (by simp [SkywalkIntegerLayout.half]) le_rfl
    have sub := ih (a + 1) (by omega)
    have pdom : ∀ q ∈ (IntegerPacket.ports (Shadow7.shape j) a).wires,
        WindowCovered.domainW (OB5.sig (start j + a) q) = true := by
      intro q hq
      simp only [IntegerPacket.ports, Shadow7.shape, Shadow7.smallBits, Shadow7.sbP, start,
        SkywalkIntegerLayout.wires, SkywalkIntegerLayout.ah, SkywalkIntegerLayout.bh,
        List.mem_append, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hq
      rw [WindowCovered.dom_iff]; unfold OB5.sig start
      split
      all_goals
        repeat' first | cases_type And | cases_type Or
        all_goals try simp only [Wire] at *
        all_goals omega
    have ok : ∀ P : Program, wires P ⊆ (IntegerPacket.ports (Shadow7.shape j) a).wires.toFinset →
        WindowCovered.CoveredW (renameProgram (OB5.sig (start j + a)) P) := by
      intro P hp q hq
      rw [renameProgram_support] at hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      exact pdom x (List.mem_toFinset.mp (hp hx))
    exact ⟨WindowCovered.appW (ok _ step.1) sub.1, WindowCovered.appW sub.2 (ok _ ustep)⟩

private theorem portal45_420_ok :
    (Shadow7.portalOps 45).all proper = true ∧ (Shadow7.portalOps 420).all proper = true ∧
    (Shadow7.loadPortsXP 420 879).Nodup ∧ (Shadow7.restorePortsXP 420).Nodup ∧
    bTopP 420 + 1 = 879 := by
  decide +kernel

private theorem packW_cov420 (d : Bool) (s t : Nat) (lo : 45 ≤ t) (ts : t ≤ s) (hi : s ≤ 420) (t5 : t % 5 = 0) :
    WindowCovered.CoveredW (packW d s t) ∧ WindowCovered.CoveredW (unpackW d s t) := by
  have due : History5.packDue t = true := by simp only [History5.packDue, decide_eq_true_eq]; omega
  have c := WindowCovered.pack_cells d t (by omega) due
  constructor
  · intro q hq; rw [packW, renameProgram_support] at hq; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨r, r1, r2, e⟩ := c.1 x hx
    rw [WindowCovered.dom_iff]; unfold OB5.sig
    rcases e with rfl | rfl <;> simp only [base, Wire] <;> split <;> omega
  · intro q hq; rw [unpackW, renameProgram_support] at hq; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨r, r1, r2, e⟩ := c.2 x hx
    rw [WindowCovered.dom_iff]; unfold OB5.sig
    rcases e with rfl | rfl <;> simp only [base, Wire] <;> split <;> omega

private theorem all_of_list {Q : Program → Prop} (hnil : Q []) (happ : ∀ {a b}, Q a → Q b → Q (a ++ b))
    {L : List Program} (h : ∀ P ∈ L, Q P) : Q L.flatten := by
  induction L with
  | nil => exact hnil
  | cons P L ih => exact happ (h P (by simp)) (ih fun X hX => h X (List.mem_cons_of_mem _ hX))

attribute [local irreducible] GatePhysical
  Shadow7.enterP Shadow7.enterInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.routed Shadow7.unrouted Shadow7.archiveLoadP Shadow7.archiveRestoreP
  CRTBarrel.leave CRTBarrel.unleave enterP20 enterInvP20 leaveP20Red leaveInvP20Red routed20 unrouted20
  archiveLoadP20 archiveRestoreP20 leave150To20Red leaveInv150To20Red archiveLoad150To20 archiveRestore150To20
  Rolling1588.packAtTick Rolling1588.unpackAtTick TickRanges.tick W.ReverseCarry.compactReceiverTick in
theorem mixed_physical (d : Bool) :
    GatePhysical (forwardMixed d) ∧ GatePhysical (reverseMixed d) := by
  have hp := portal45_420_ok
  have p45 := physical_of_proper _ (List.all_eq_true.mp hp.1)
  have p420 := physical_of_proper _ (List.all_eq_true.mp hp.2.1)
  have pk420 := Shadow7.parkP_physical 420 (by decide) (by decide)
  have t420 := WindowPhysicalW.tick_phys 420 (by decide)
  have mL420 : GatePhysical (moveLoadP 420) := by
    rw [moveLoadP]; refine (physical_of_proper _ (proper_swapsG _ ?_)).1
    simp only [moveLoadPairs, List.forall_mem_cons, List.forall_mem_nil, and_true, ne_eq, OB5.sig]
    and_intros <;> first | (intro x hx; cases hx) | (unfold Wire; split_ifs <;> omega)
  have mR420 : GatePhysical (moveRestoreP 420 (bTopP 420 + 1)) := by
    rw [hp.2.2.2.2, moveRestoreP]; refine (physical_of_proper _ (proper_swapsG _ ?_)).1
    simp only [moveRestorePairs, List.forall_mem_cons, List.forall_mem_nil, and_true, ne_eq, OB5.sig]
    and_intros <;> first | (intro x hx; cases hx) | (unfold Wire; split_ifs <;> omega) | (unfold Wire; omega)
  have exL : GatePhysical (Shadow7.exitLoadP 420 d) := by
    rw [Shadow7.exitLoadP, hp.2.2.2.2]
    exact WindowPhysicalW.appP (WindowPhysicalW.load_codec_phys _ hp.2.2.1 (by rw [Shadow7.loadPortsXP_length]) d) mL420
  have exR : GatePhysical (Shadow7.exitRestoreP 420 d) := by
    rw [Shadow7.exitRestoreP]
    exact WindowPhysicalW.appP (WindowPhysicalW.restore_codec_phys _ hp.2.2.2.1 (by rw [Shadow7.restorePortsXP_length]) d) mR420
  have hp15 : ∀ p ∈ prefixPairs, p.1.val ≤ 24 ∧ p.2.val ≤ 24 ∧ 10 ≤ start p.2 - 10 ∧
      start p.2 ≤ 511 ∧ History5.packDue (start p.2 - 10) = true := by decide
  have hs15 : ∀ p ∈ suffixPairs, p.1.val ≤ 24 ∧ p.2.val ≤ 24 ∧ 10 ≤ start p.2 - 10 ∧
      start p.2 ≤ 511 ∧ History5.packDue (start p.2 - 10) = true := by decide
  have b15ok : ∀ i j : Fin 26, i.val ≤ 24 → j.val ≤ 24 → 10 ≤ start j - 10 → start j ≤ 511 →
      History5.packDue (start j - 10) = true →
      (∀ P ∈ block15F d i j, GatePhysical P) ∧ (∀ P ∈ block15R d i j, GatePhysical P) := by
    intro i j hi hj h10 h511 hdue
    have e := Shadow7.enterP_physical j (Nat.zero_le _) hj
    have r0 := routed15_phys j 0 1 (by decide)
    have r1 := routed15_phys j 1 14 (by decide)
    have pk := WindowPhysicalW.pack_phys d (start j) (start j - 10) h511 h10 (by omega) hdue
    have ar := archive15_phys i hi d
    have lv := leave15_phys j hj
    constructor <;> intro P hP <;> simp only [block15F, block15R, List.mem_cons, List.not_mem_nil, or_false] at hP
    · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
      · exact e.1
      · exact r0.1
      · exact pk.1
      · exact ar.1
      · exact r1.1
      · exact lv.1
    · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
      · exact lv.2
      · exact r1.2
      · exact ar.2
      · exact pk.2
      · exact r0.2
      · exact e.2
  have b20ok : ∀ j : Fin 9, (∀ P ∈ block20F d j, GatePhysical P) ∧ (∀ P ∈ block20R d j, GatePhysical P) := by
    intro j
    have e := enter20_phys j
    have r0 := routed20_phys j 0 1 (by decide)
    have r1 := routed20_phys j 1 19 (by decide)
    have lv := leave20Red_phys j
    by_cases h0 : j.val = 0
    · have pk := WindowPhysicalW.pack_phys d 165 155 (by decide) (by decide) (by decide) (by decide)
      have ar := archive150To20_phys d
      constructor <;> intro P hP <;> simp only [block20F, block20R, h0, ↓reduceDIte, List.mem_cons, List.not_mem_nil, or_false] at hP
      · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
        · exact e.1
        · exact r0.1
        · exact pk.1
        · exact ar.1
        · exact r1.1
        · exact lv.1
      · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
        · exact lv.2
        · exact r1.2
        · exact ar.2
        · exact pk.2
        · exact r0.2
        · exact e.2
    · have hs : start20 j ≤ 511 := by unfold start20; omega
      have h10a : 10 ≤ start20 j - 15 := by unfold start20; omega
      have h10b : 10 ≤ start20 j - 10 := by unfold start20; omega
      have hda : History5.packDue (start20 j - 15) = true := by simp only [History5.packDue, start20, decide_eq_true_eq]; omega
      have hdb : History5.packDue (start20 j - 10) = true := by simp only [History5.packDue, start20, decide_eq_true_eq]; omega
      have pk1 := WindowPhysicalW.pack_phys d (start20 j) (start20 j - 15) hs h10a (by omega) hda
      have pk2 := WindowPhysicalW.pack_phys d (start20 j) (start20 j - 10) hs h10b (by omega) hdb
      have ar := archive20_phys ⟨j.val - 1, by omega⟩ d
      constructor <;> intro P hP <;> simp only [block20F, block20R, h0, ↓reduceDIte, List.mem_cons, List.not_mem_nil, or_false] at hP
      · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact e.1
        · exact r0.1
        · exact pk1.1
        · exact pk2.1
        · exact ar.1
        · exact r1.1
        · exact lv.1
      · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact lv.2
        · exact r1.2
        · exact ar.2
        · exact pk2.2
        · exact pk1.2
        · exact r0.2
        · exact e.2
  constructor
  · apply all_of_list WindowPhysicalW.nilP (fun ha hb => WindowPhysicalW.appP ha hb)
    intro P hP
    simp only [forwardL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hP
    rcases hP with ((((((h | ⟨p, hp, h⟩) | h) | ⟨j, _, h⟩) | h) | ⟨p, hp, h⟩) | h)
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact p45.1
      · exact (Shadow7.enterP_physical j0 (by decide) (by decide)).1
      · exact (routed15_phys j0 0 1 (by decide)).1
      · exact (WindowPhysicalW.pack_phys d 45 45 (by decide) (by decide) (by decide) (by decide)).1
      · exact (routed15_phys j0 1 14 (by decide)).1
      · exact (leave15_phys j0 (by decide)).1
    · have x := hp15 p hp; exact (b15ok p.1 p.2 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).1 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (Shadow7.enterP_physical j7 (by decide) (by decide)).1
      · exact (routed15_phys j7 0 1 (by decide)).1
      · exact (WindowPhysicalW.pack_phys d 150 140 (by decide) (by decide) (by decide) (by decide)).1
      · exact (archive15_phys j6 (by decide) d).1
      · exact (routed15_phys j7 1 14 (by decide)).1
      · exact leave150To20Red_phys.1
    · exact (b20ok j).1 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (Shadow7.enterP_physical j20 (by decide) (by decide)).1
      · exact (routed15_phys j20 0 1 (by decide)).1
      · exact (WindowPhysicalW.pack_phys d 345 330 (by decide) (by decide) (by decide) (by decide)).1
      · exact (WindowPhysicalW.pack_phys d 345 335 (by decide) (by decide) (by decide) (by decide)).1
      · exact (archive20_phys k8 d).1
      · exact (routed15_phys j20 1 14 (by decide)).1
      · exact (leave15_phys j20 (by decide)).1
    · have x := hs15 p hp; exact (b15ok p.1 p.2 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).1 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl
      · exact pk420.1
      · exact p420.2
      · exact t420.1
      · exact (WindowPhysicalW.pack_phys d 420 410 (by decide) (by decide) (by decide) (by decide)).1
      · exact exL
  · apply all_of_list WindowPhysicalW.nilP (fun ha hb => WindowPhysicalW.appP ha hb)
    intro P hP
    simp only [reverseL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hP
    rcases hP with ((((((h | ⟨p, hp, h⟩) | h) | ⟨j, _, h⟩) | h) | ⟨p, hp, h⟩) | h)
    · rcases h with rfl | rfl | rfl | rfl | rfl
      · exact exR
      · exact (WindowPhysicalW.pack_phys d 420 410 (by decide) (by decide) (by decide) (by decide)).2
      · exact t420.2
      · exact p420.1
      · exact pk420.2
    · have x := hs15 p (List.mem_reverse.mp hp); exact (b15ok p.1 p.2 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).2 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (leave15_phys j20 (by decide)).2
      · exact (routed15_phys j20 1 14 (by decide)).2
      · exact (archive20_phys k8 d).2
      · exact (WindowPhysicalW.pack_phys d 345 335 (by decide) (by decide) (by decide) (by decide)).2
      · exact (WindowPhysicalW.pack_phys d 345 330 (by decide) (by decide) (by decide) (by decide)).2
      · exact (routed15_phys j20 0 1 (by decide)).2
      · exact (Shadow7.enterP_physical j20 (by decide) (by decide)).2
    · exact (b20ok j).2 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact leave150To20Red_phys.2
      · exact (routed15_phys j7 1 14 (by decide)).2
      · exact (archive15_phys j6 (by decide) d).2
      · exact (WindowPhysicalW.pack_phys d 150 140 (by decide) (by decide) (by decide) (by decide)).2
      · exact (routed15_phys j7 0 1 (by decide)).2
      · exact (Shadow7.enterP_physical j7 (by decide) (by decide)).2
    · have x := hp15 p (List.mem_reverse.mp hp); exact (b15ok p.1 p.2 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).2 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (leave15_phys j0 (by decide)).2
      · exact (routed15_phys j0 1 14 (by decide)).2
      · exact (WindowPhysicalW.pack_phys d 45 45 (by decide) (by decide) (by decide) (by decide)).2
      · exact (routed15_phys j0 0 1 (by decide)).2
      · exact (Shadow7.enterP_physical j0 (by decide) (by decide)).2
      · exact p45.2

attribute [local irreducible]
  Shadow7.enterP Shadow7.enterInvP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.routed Shadow7.unrouted Shadow7.archiveLoadP Shadow7.archiveRestoreP
  Shadow7.exitLoadP Shadow7.exitRestoreP CRTBarrel.leave CRTBarrel.unleave
  enterP20 enterInvP20 leaveP20Red leaveInvP20Red routed20 unrouted20
  archiveLoadP20 archiveRestoreP20 leave150To20Red leaveInv150To20Red archiveLoad150To20 archiveRestore150To20
  Rolling1588.packAtTick Rolling1588.unpackAtTick TickRanges.tick W.ReverseCarry.compactReceiverTick in
theorem mixed_covered (d : Bool) :
    WindowCovered.CoveredW (forwardMixed d) ∧ WindowCovered.CoveredW (reverseMixed d) := by
  have footDom : ∀ {s q : Nat}, 45 ≤ s → s ≤ 420 → footP s q → WindowCovered.domainW q = true := by
    intro s q lo hi h
    have a := WindowCovered.top_A s (by omega); have b := WindowCovered.rail_le s
    rw [WindowCovered.dom_iff]; unfold footP at h; omega
  have enterCov : ∀ j : Fin 26, j.val ≤ 24 → WindowCovered.CoveredW (Shadow7.enterP j) ∧ WindowCovered.CoveredW (Shadow7.enterInvP j) := by
    intro j hj
    have w := Shadow7.enter_wires j (Nat.zero_le _) hj
    have hs := start_win7 j (Nat.zero_le _) hj
    exact ⟨fun q hq => footDom hs.1 (by omega) (w.1 q hq), fun q hq => footDom hs.1 (by omega) (w.2 q hq)⟩
  have p45w := Shadow7.portal_wires 45 (by decide) (by decide)
  have p45 : WindowCovered.CoveredW (Shadow7.portalP 45) ∧ WindowCovered.CoveredW (Shadow7.portalInvP 45) :=
    ⟨fun q hq => footDom (by decide) (by decide) (p45w.1 q hq), fun q hq => footDom (by decide) (by decide) (p45w.2 q hq)⟩
  have p420w := Shadow7.portal_wires 420 (by decide) (by decide)
  have p420 : WindowCovered.CoveredW (Shadow7.portalP 420) ∧ WindowCovered.CoveredW (Shadow7.portalInvP 420) :=
    ⟨fun q hq => footDom (by decide) (by decide) (p420w.1 q hq), fun q hq => footDom (by decide) (by decide) (p420w.2 q hq)⟩
  have pk420w := Shadow7.park_wires 420 (by decide) (by decide)
  have pk420 : WindowCovered.CoveredW (Shadow7.parkP 420) ∧ WindowCovered.CoveredW (Shadow7.parkInvP 420) :=
    ⟨fun q hq => WindowCovered.parkFoot_dom (by decide) (pk420w.1 q hq),
     fun q hq => WindowCovered.parkFoot_dom (by decide) (pk420w.2 q hq)⟩
  have t420 := WindowCovered.exit_tick 420 (by decide) (by decide +kernel)
  have exDom : ∀ q, archFootW 420 (bTopP 420 + 1) q → WindowCovered.domainW q = true := by
    intro q h
    have b : railP 420 ≤ 257 := by decide
    rw [WindowCovered.dom_iff]; unfold archFootW bTopP at h; omega
  have exL : WindowCovered.CoveredW (Shadow7.exitLoadP 420 d) :=
    fun q hq => exDom q (Shadow7.exitLoadP_wiresW 420 d (by decide) q hq)
  have exR : WindowCovered.CoveredW (Shadow7.exitRestoreP 420 d) :=
    fun q hq => exDom q (Shadow7.exitRestoreP_wiresW 420 d (by decide) q hq)
  have hp15 : ∀ p ∈ prefixPairs, p.1.val ≤ 24 ∧ p.2.val ≤ 24 ∧ 45 ≤ start p.2 - 10 ∧
      start p.2 ≤ 420 ∧ (start p.2 - 10) % 5 = 0 := by decide
  have hs15 : ∀ p ∈ suffixPairs, p.1.val ≤ 24 ∧ p.2.val ≤ 24 ∧ 45 ≤ start p.2 - 10 ∧
      start p.2 ≤ 420 ∧ (start p.2 - 10) % 5 = 0 := by decide
  have b15ok : ∀ i j : Fin 26, i.val ≤ 24 → j.val ≤ 24 → 45 ≤ start j - 10 → start j ≤ 420 →
      (start j - 10) % 5 = 0 →
      (∀ P ∈ block15F d i j, WindowCovered.CoveredW P) ∧ (∀ P ∈ block15R d i j, WindowCovered.CoveredW P) := by
    intro i j hi hj h45 h420 hm5
    have e := enterCov j hj
    have r0 := routed15_cov j hj 0 1 (by decide)
    have r1 := routed15_cov j hj 1 14 (by decide)
    have pk := packW_cov420 d (start j) (start j - 10) h45 (by omega) h420 hm5
    have ar := archive15_cov i hi d
    have lv := leave15_cov j hj
    constructor <;> intro P hP <;> simp only [block15F, block15R, List.mem_cons, List.not_mem_nil, or_false] at hP
    · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
      · exact e.1
      · exact r0.1
      · exact pk.1
      · exact ar.1
      · exact r1.1
      · exact lv.1
    · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
      · exact lv.2
      · exact r1.2
      · exact ar.2
      · exact pk.2
      · exact r0.2
      · exact e.2
  have b20ok : ∀ j : Fin 9, (∀ P ∈ block20F d j, WindowCovered.CoveredW P) ∧ (∀ P ∈ block20R d j, WindowCovered.CoveredW P) := by
    intro j
    have e := enter20_cov j
    have r0 := routed20_cov j 0 1 (by decide)
    have r1 := routed20_cov j 1 19 (by decide)
    have lv := leave20Red_cov j
    by_cases h0 : j.val = 0
    · have pk := packW_cov420 d 165 155 (by decide) (by decide) (by decide) (by decide)
      have ar := archive150To20_cov d
      constructor <;> intro P hP <;> simp only [block20F, block20R, h0, ↓reduceDIte, List.mem_cons, List.not_mem_nil, or_false] at hP
      · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
        · exact e.1
        · exact r0.1
        · exact pk.1
        · exact ar.1
        · exact r1.1
        · exact lv.1
      · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
        · exact lv.2
        · exact r1.2
        · exact ar.2
        · exact pk.2
        · exact r0.2
        · exact e.2
    · have hs : start20 j ≤ 420 := by unfold start20; omega
      have pk1 := packW_cov420 d (start20 j) (start20 j - 15) (by unfold start20; omega) (by omega) hs (by unfold start20; omega)
      have pk2 := packW_cov420 d (start20 j) (start20 j - 10) (by unfold start20; omega) (by omega) hs (by unfold start20; omega)
      have ar := archive20_cov ⟨j.val - 1, by omega⟩ d
      constructor <;> intro P hP <;> simp only [block20F, block20R, h0, ↓reduceDIte, List.mem_cons, List.not_mem_nil, or_false] at hP
      · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact e.1
        · exact r0.1
        · exact pk1.1
        · exact pk2.1
        · exact ar.1
        · exact r1.1
        · exact lv.1
      · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact lv.2
        · exact r1.2
        · exact ar.2
        · exact pk2.2
        · exact pk1.2
        · exact r0.2
        · exact e.2
  constructor
  · apply all_of_list WindowCovered.nilW (fun ha hb => WindowCovered.appW ha hb)
    intro P hP
    simp only [forwardL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hP
    rcases hP with ((((((h | ⟨p, hp, h⟩) | h) | ⟨j, _, h⟩) | h) | ⟨p, hp, h⟩) | h)
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact p45.1
      · exact (enterCov j0 (by decide)).1
      · exact (routed15_cov j0 (by decide) 0 1 (by decide)).1
      · exact (packW_cov420 d 45 45 (by decide) (by decide) (by decide) (by decide)).1
      · exact (routed15_cov j0 (by decide) 1 14 (by decide)).1
      · exact (leave15_cov j0 (by decide)).1
    · have x := hp15 p hp; exact (b15ok p.1 p.2 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).1 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (enterCov j7 (by decide)).1
      · exact (routed15_cov j7 (by decide) 0 1 (by decide)).1
      · exact (packW_cov420 d 150 140 (by decide) (by decide) (by decide) (by decide)).1
      · exact (archive15_cov j6 (by decide) d).1
      · exact (routed15_cov j7 (by decide) 1 14 (by decide)).1
      · exact leave150To20Red_cov.1
    · exact (b20ok j).1 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (enterCov j20 (by decide)).1
      · exact (routed15_cov j20 (by decide) 0 1 (by decide)).1
      · exact (packW_cov420 d 345 330 (by decide) (by decide) (by decide) (by decide)).1
      · exact (packW_cov420 d 345 335 (by decide) (by decide) (by decide) (by decide)).1
      · exact (archive20_cov k8 d).1
      · exact (routed15_cov j20 (by decide) 1 14 (by decide)).1
      · exact (leave15_cov j20 (by decide)).1
    · have x := hs15 p hp; exact (b15ok p.1 p.2 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).1 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl
      · exact pk420.1
      · exact p420.2
      · exact t420.1
      · exact (packW_cov420 d 420 410 (by decide) (by decide) (by decide) (by decide)).1
      · exact exL
  · apply all_of_list WindowCovered.nilW (fun ha hb => WindowCovered.appW ha hb)
    intro P hP
    simp only [reverseL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hP
    rcases hP with ((((((h | ⟨p, hp, h⟩) | h) | ⟨j, _, h⟩) | h) | ⟨p, hp, h⟩) | h)
    · rcases h with rfl | rfl | rfl | rfl | rfl
      · exact exR
      · exact (packW_cov420 d 420 410 (by decide) (by decide) (by decide) (by decide)).2
      · exact t420.2
      · exact p420.1
      · exact pk420.2
    · have x := hs15 p (List.mem_reverse.mp hp); exact (b15ok p.1 p.2 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).2 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (leave15_cov j20 (by decide)).2
      · exact (routed15_cov j20 (by decide) 1 14 (by decide)).2
      · exact (archive20_cov k8 d).2
      · exact (packW_cov420 d 345 335 (by decide) (by decide) (by decide) (by decide)).2
      · exact (packW_cov420 d 345 330 (by decide) (by decide) (by decide) (by decide)).2
      · exact (routed15_cov j20 (by decide) 0 1 (by decide)).2
      · exact (enterCov j20 (by decide)).2
    · exact (b20ok j).2 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact leave150To20Red_cov.2
      · exact (routed15_cov j7 (by decide) 1 14 (by decide)).2
      · exact (archive15_cov j6 (by decide) d).2
      · exact (packW_cov420 d 150 140 (by decide) (by decide) (by decide) (by decide)).2
      · exact (routed15_cov j7 (by decide) 0 1 (by decide)).2
      · exact (enterCov j7 (by decide)).2
    · have x := hp15 p (List.mem_reverse.mp hp); exact (b15ok p.1 p.2 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).2 P h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (leave15_cov j0 (by decide)).2
      · exact (routed15_cov j0 (by decide) 1 14 (by decide)).2
      · exact (packW_cov420 d 45 45 (by decide) (by decide) (by decide) (by decide)).2
      · exact (routed15_cov j0 (by decide) 0 1 (by decide)).2
      · exact (enterCov j0 (by decide)).2
      · exact p45.2

end MixedWindow

/-! ### Section 3: 22-Bank Field Schedule (`MixedFieldBanks`) -/

namespace MixedFieldBanks
open ECDSAAdd.Entrant.StairArchiveInactive

def mixedBankList : List Nat :=
  [10, 13, 16, 19, 22, 25, 28, 31, 35, 39, 43, 47, 51, 55, 59, 63, 67, 70, 73, 76, 79, 82]

def mixedBankIds : Finset Nat :=
  {10, 13, 16, 19, 22, 25, 28, 31, 35, 39, 43, 47, 51, 55, 59, 63, 67, 70, 73, 76, 79, 82}

theorem mixedBankIds_card : mixedBankIds.card = 22 := by decide

private theorem bank10_safe : (safe 10 false && safe 10 true) = true := by decide +kernel
private theorem bank13_safe : (safe 13 false && safe 13 true) = true := by decide +kernel
private theorem bank35_safe : (safe 35 false && safe 35 true) = true := by decide +kernel
private theorem bank39_safe : (safe 39 false && safe 39 true) = true := by decide +kernel
private theorem bank47_safe : (safe 47 false && safe 47 true) = true := by decide +kernel
private theorem bank51_safe : (safe 51 false && safe 51 true) = true := by decide +kernel
private theorem bank59_safe : (safe 59 false && safe 59 true) = true := by decide +kernel
private theorem bank63_safe : (safe 63 false && safe 63 true) = true := by decide +kernel

private theorem oldMixedBanks_in_starts :
    ∀ b ∈ [16, 19, 22, 25, 28, 31, 43, 55, 67, 70, 73, 76, 79, 82], b ∈ starts := by
  decide

attribute [local irreducible] packet wires preimage cover savedSites in
private theorem avoids_of_safe {j : Nat} (hj : j < 100) (hs : (safe j false && safe j true) = true)
    (d second : Bool) (q : Wire) (save : q ∈ savedSites j second) :
    q ∉ wires (packet d (if second then j + 1 else j)) := by
  intro used
  simp only [Bool.and_eq_true] at hs
  have pass : safe j second = true := by cases second; exact hs.1; exact hs.2
  let k := if second then j + 1 else j
  have hk : k < 102 := by dsimp only [k]; split <;> omega
  change (savedSites j second).all (fun z => decide (preimage k z ∉ cover k)) = true at pass
  have exc : preimage k q ∉ cover k := of_decide_eq_true (List.all_eq_true.mp pass q save)
  exact exc (original d k hk used)

attribute [local irreducible] packet wires preimage cover savedSites in
theorem packet_avoids_mixed (j : Nat) (hj : j ∈ mixedBankList) (d second : Bool)
    (q : Wire) (save : q ∈ savedSites j second) :
    q ∉ wires (packet d (if second then j + 1 else j)) := by
  simp only [mixedBankList, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact avoids_of_safe (by decide) bank10_safe d second q save
  · exact avoids_of_safe (by decide) bank13_safe d second q save
  · exact packet_avoids 16 (oldMixedBanks_in_starts 16 (by decide)) d second q save
  · exact packet_avoids 19 (oldMixedBanks_in_starts 19 (by decide)) d second q save
  · exact packet_avoids 22 (oldMixedBanks_in_starts 22 (by decide)) d second q save
  · exact packet_avoids 25 (oldMixedBanks_in_starts 25 (by decide)) d second q save
  · exact packet_avoids 28 (oldMixedBanks_in_starts 28 (by decide)) d second q save
  · exact packet_avoids 31 (oldMixedBanks_in_starts 31 (by decide)) d second q save
  · exact avoids_of_safe (by decide) bank35_safe d second q save
  · exact avoids_of_safe (by decide) bank39_safe d second q save
  · exact packet_avoids 43 (oldMixedBanks_in_starts 43 (by decide)) d second q save
  · exact avoids_of_safe (by decide) bank47_safe d second q save
  · exact avoids_of_safe (by decide) bank51_safe d second q save
  · exact packet_avoids 55 (oldMixedBanks_in_starts 55 (by decide)) d second q save
  · exact avoids_of_safe (by decide) bank59_safe d second q save
  · exact avoids_of_safe (by decide) bank63_safe d second q save
  · exact packet_avoids 67 (oldMixedBanks_in_starts 67 (by decide)) d second q save
  · exact packet_avoids 70 (oldMixedBanks_in_starts 70 (by decide)) d second q save
  · exact packet_avoids 73 (oldMixedBanks_in_starts 73 (by decide)) d second q save
  · exact packet_avoids 76 (oldMixedBanks_in_starts 76 (by decide)) d second q save
  · exact packet_avoids 79 (oldMixedBanks_in_starts 79 (by decide)) d second q save
  · exact packet_avoids 82 (oldMixedBanks_in_starts 82 (by decide)) d second q save

/-- Parametric 22-bank field group fold: replaces the 25 `oten` ten-blocks of `WindowFieldCosts.group84`
with the 22 mixed-window archive ten-blocks (3 fewer ten-blocks = `-336 T` per kernel, `-672 T` total). -/
def orderedM (d : Bool) (a b : Program) : Program := if d then a ++ b else b ++ a

def mixedGroup84 (og : Bool → Nat → Nat → Program) (ot : Nat → Bool → Program) (d : Bool) : Program :=
  orderedM d (og d 1 9) (orderedM d (ot 10 (!d)) (orderedM d (og d 12 1) (orderedM d (ot 13 (!d))
  (orderedM d (og d 15 1) (orderedM d (ot 16 (!d)) (orderedM d (og d 18 1) (orderedM d (ot 19 (!d))
  (orderedM d (og d 21 1) (orderedM d (ot 22 (!d)) (orderedM d (og d 24 1) (orderedM d (ot 25 (!d))
  (orderedM d (og d 27 1) (orderedM d (ot 28 (!d)) (orderedM d (og d 30 1) (orderedM d (ot 31 (!d))
  (orderedM d (og d 33 2) (orderedM d (ot 35 (!d)) (orderedM d (og d 37 2) (orderedM d (ot 39 (!d))
  (orderedM d (og d 41 2) (orderedM d (ot 43 (!d)) (orderedM d (og d 45 2) (orderedM d (ot 47 (!d))
  (orderedM d (og d 49 2) (orderedM d (ot 51 (!d)) (orderedM d (og d 53 2) (orderedM d (ot 55 (!d))
  (orderedM d (og d 57 2) (orderedM d (ot 59 (!d)) (orderedM d (og d 61 2) (orderedM d (ot 63 (!d))
  (orderedM d (og d 65 2) (orderedM d (ot 67 (!d)) (orderedM d (og d 69 1) (orderedM d (ot 70 (!d))
  (orderedM d (og d 72 1) (orderedM d (ot 73 (!d)) (orderedM d (og d 75 1) (orderedM d (ot 76 (!d))
  (orderedM d (og d 78 1) (orderedM d (ot 79 (!d)) (orderedM d (og d 81 1) (orderedM d (ot 82 (!d))
  (og d 84 1))))))))))))))))))))))))))))))))))))))))))))

theorem mixedGroup84_measure (m : Program → Nat) (happ : ∀ a b, m (a ++ b) = m a + m b)
    (og : Bool → Nat → Nat → Program) (ot : Nat → Bool → Program) (d : Bool) (delta : Nat)
    (hsplit : ∀ j n k, m (og d j (n + k)) = m (og d j n) + m (og d (j + n) k))
    (hot : ∀ j, m (ot j (!d)) = m (og d j 2) + delta) :
    m (mixedGroup84 og ot d) = m (og d 1 84) + 22 * delta := by
  have hord : ∀ a b, m (orderedM d a b) = m a + m b := fun a b => by
    cases d <;> simp [orderedM, happ, Nat.add_comm]
  have p0 := hsplit 1 9 75; have p1 := hsplit 10 2 73; have p2 := hsplit 12 1 72
  have p3 := hsplit 13 2 70; have p4 := hsplit 15 1 69; have p5 := hsplit 16 2 67
  have p6 := hsplit 18 1 66; have p7 := hsplit 19 2 64; have p8 := hsplit 21 1 63
  have p9 := hsplit 22 2 61; have p10 := hsplit 24 1 60; have p11 := hsplit 25 2 58
  have p12 := hsplit 27 1 57; have p13 := hsplit 28 2 55; have p14 := hsplit 30 1 54
  have p15 := hsplit 31 2 52; have p16 := hsplit 33 2 50; have p17 := hsplit 35 2 48
  have p18 := hsplit 37 2 46; have p19 := hsplit 39 2 44; have p20 := hsplit 41 2 42
  have p21 := hsplit 43 2 40; have p22 := hsplit 45 2 38; have p23 := hsplit 47 2 36
  have p24 := hsplit 49 2 34; have p25 := hsplit 51 2 32; have p26 := hsplit 53 2 30
  have p27 := hsplit 55 2 28; have p28 := hsplit 57 2 26; have p29 := hsplit 59 2 24
  have p30 := hsplit 61 2 22; have p31 := hsplit 63 2 20; have p32 := hsplit 65 2 18
  have p33 := hsplit 67 2 16; have p34 := hsplit 69 1 15; have p35 := hsplit 70 2 13
  have p36 := hsplit 72 1 12; have p37 := hsplit 73 2 10; have p38 := hsplit 75 1 9
  have p39 := hsplit 76 2 7; have p40 := hsplit 78 1 6; have p41 := hsplit 79 2 4
  have p42 := hsplit 81 1 3; have p43 := hsplit 82 2 1
  simp only [mixedGroup84, hord, hot]
  norm_num only [] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43
  omega


end MixedFieldBanks

end ECDSAAdd.Entrant.StairPacket.Shadow20
end
