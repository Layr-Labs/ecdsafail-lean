import ECDSAAdd.Submission.Entrant.ShadowLeave
import ECDSAAdd.Submission.Entrant.ShadowGeometry
import ECDSAAdd.Submission.Entrant.ShadowBox2

/-! Shadow7 move leave (leave-move): c9cc6a76's leaveMove on the generic shadow leave, blocks 1..20 (`j ≤ 20`, as the
LeaveJ7 core). Generated from the stock blocks by helpers/shadow-leave/scripts/port.py (ONLY=W:20905-21130), then edited by
leave-move (footprint via `Shadow7.leaveOps_box2` from ShadowBox2). -/

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror RecordedQuantum HighBankFirstHit LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem moveA_split (s : Nat) : Shadow7.moveA s =
    entryOps s ++ ((leaveFix3 s (Shadow7.sbP s) ++ leaveFix4 s (Shadow7.sbP s)) ++ (leaveFix5 s (Shadow7.sbP s)).take 27) := by
  unfold Shadow7.moveA entryOps; simp only [List.append_assoc]

theorem fullPrefix_split (j : Fin 23) : fullPrefix j =
    ((leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j))) ++
      (leaveFix5 (start j) (Shadow7.sbP (start j))).take 27) ++ (leaveFix5 (start j) (Shadow7.sbP (start j))).drop 27 := by
  unfold fullPrefix; rw [List.append_assoc _ ((leaveFix5 _ _).take 27), List.take_append_drop]

/-- In front of the mux: the crossing wire is still clean (nothing in the selector prefix writes it). -/
theorem prefix302_targets (s h : Nat) : ((leaveFix3 s h ++ leaveFix4 s h) ++ (leaveFix5 s h).take 27).map target =
    [1559, 1560, 1560, 1561, 1560, 1562, 1560, 1563, 1560, 1564, 1560, 1565, 1560, 1566, 1560, 1567, 1560, 1568, 1560,
     1569, 1560, 1570, 1560, 1571, 1560, 1572, 1560, 1573, 1560, 1574, 1560, 1575, 1560,
     h+1581, h+1581, h+1581, h+1581, h+1581, h+1581, 1576, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584,
     1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595] := rfl

theorem cross_kept (s h : Nat) (hh : 16 ≤ h) (q : Wire) (hq : q = h + 1580) (st : State) (o : List Bool) :
    (run (GateMirror.forward ((leaveFix3 s h ++ leaveFix4 s h) ++ (leaveFix5 s h).take 27)) o st).basis q =
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
    (run (GateMirror.forward ((leaveFix5 s h).drop 27)) o st).basis (tagsP.getD i 0) = st.basis (tagsP.getD i 0) := by
  have t := tags_range i hi
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  simp only [leaveFix5, List.drop, List.map_cons, List.map_nil, target, List.mem_cons, List.not_mem_nil, or_false]
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
theorem Inputs.hot {j : Fin 23} (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) {s : State} {z : SkywalkNat.State}
    {g0 s0 : Bool} (h : Inputs j s z g0 s0) (o : List Bool) :
    (run (GateMirror.forward (Shadow7.moveA (start j))) o s).basis (Shadow7.e0P (start j) + 6) = false ∧
    ∀ r ∈ Shadow7.moveRows (start j), (run (GateMirror.forward (Shadow7.moveA (start j))) o s).basis r.1 = true →
      r.2 = Shadow7.a0P (start j) + key (actualMode (Shadow7.sbP (start j)) z) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
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
  have kept (q : Nat) (ok : ¬ ((Shadow7.a0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.a0P (start j) + 17) ∨
      (Shadow7.b0P (start j) - 1 ≤ q ∧ q ≤ Shadow7.b0P (start j) + 17) ∨ (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨
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
        (leaveFix5 (start j) (Shadow7.sbP (start j))).take 27)) n en := by
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

theorem Inputs.sameMove {j : Fin 23} (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) {s : State} {z : SkywalkNat.State}
    {g0 s0 : Bool} (h : Inputs j s z g0 s0) (m : List Bool) : run (Shadow7.leaveMoveP j) m s = run (Shadow7.leaveP j) m s := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  exact Shadow7.leaveMove_same w1 w2 s m _ (h.hot h0 h1 m).1 (h.hot h0 h1 m).2

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
theorem resultMove (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m n : List Bool) (z : SkywalkNat.State)
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
      s.basis q = false) (a0 : Wire)
    (hot : ∀ o, (run (GateMirror.forward (Shadow7.moveA (start j))) o s).basis (Shadow7.e0P (start j) + 6) = false ∧
      ∀ r ∈ Shadow7.moveRows (start j), (run (GateMirror.forward (Shadow7.moveA (start j))) o s).basis r.1 = true → r.2 = a0) :
    run (Shadow7.leaveMoveInvP j) n (run (Shadow7.leaveMoveP j) m s) = s := by
  have atCore := CoreCheckpoint.result j h0 h1 s [] z G sg small ready fresh scratch temp odd room clean padding bank zero
    par mode events
  have core := CoreCheckpoint.oracle j h0 h1 s _ atCore.1 atCore.2.2.1 clean
  have bs := beforeStore_result j h0 h1 s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode
    events nextSmall bound
  have post : (run (GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j))) [] s).basis 1556 = false := by
    have safe : (1556 : Wire) ∉ (GateMirror.forward (Shadow7.leaveLowClose (start j))).map LeaveReadoutFrame.destination := by
      intro hm
      rw [dest_forward] at hm
      obtain ⟨g, hg, e⟩ := List.mem_map.mp hm
      exact (lowClose_keeps j h0 h1 g hg).2 e
    rw [← StoreMapped.program_eq j, StoreMapped.program, run_append, run_take, LeaveReadoutFrame.preserved _ _ _ _ safe]
    exact bs.2.1
  exact Shadow7.leaveMove_inverts j h0 (by omega) s phase initial extra core post a0 hot m n
end Roundtrip

/-- A wire outside `Shadow7.leaveBox2` keeps its value through the move leave (its operands are the reference leave's). -/
theorem leaveMove_keeps (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Wire) (hq : ¬ Shadow7.leaveBox2 (start j) q)
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
theorem Inputs.roundtripMove {j : Fin 23} (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) {s : State} {z : SkywalkNat.State}
    {g0 s0 : Bool} (h : Inputs j s z g0 s0) (m n : List Bool) : run (Shadow7.leaveMoveInvP j) n (run (Shadow7.leaveMoveP j) m s) = s := by
  let u := flags z g0 s0
  let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par := RecordedParity.result j h0 h1 s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z = LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j h0 h1 s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have ph (o : List Bool) : (run (Shadow7.leaveP j) o s).phase = s.phase :=
    (Whole.result j h0 h1 s o z u.1 u.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank
      h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.bound xs (SkywalkTrace.trace_length _ _)
      (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
      ev.1 h.far h.side).1
  exact Roundtrip.resultMove j h0 h1 s m n z u.1 u.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding
    h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.bound ph (native_carryJ j h0 h1 _ s h.ready) h.extra _ (h.hot h0 h1)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission

