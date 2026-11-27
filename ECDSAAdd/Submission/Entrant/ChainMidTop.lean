import ECDSAAdd.Submission.Entrant.Mixed20D
import ECDSAAdd.Submission.Entrant.MainP1

section

namespace ECDSAAdd.Entrant.StairPacket.ChainMidTop

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge
open ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Entrant.StairPacket.Partial
open ECDSAAdd.Entrant.StairPacket.GateMirror
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut
open ECDSAAdd.Entrant.StairPacket.Shadow20.LeaveCut20

set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false


/-! ### 1. Symbolic single-wire tracker for `GateMirror.forward` -/

/-- Symbolic value of wire `w`: `some (fl, none)` means `basis w = fl`;
    `some (fl, some c)` means `c ≠ w ∧ basis w = fl ^^ basis c`. -/
def trackStep (w : Wire) (st : Option (Bool × Option Wire)) (g : Gate) :
    Option (Bool × Option Wire) :=
  match g with
  | .x t =>
    match st with
    | none => none
    | some (fl, none) => if t == w then some (!fl, none) else some (fl, none)
    | some (fl, some c) =>
      if t == w then some (!fl, some c)
      else if t == c then some (!fl, some c)
      else some (fl, some c)
  | .cx a t =>
    match st with
    | none => none
    | some (fl, none) =>
      if t == w then (if a == w then none else some (fl, some a))
      else some (fl, none)
    | some (fl, some c) =>
      if t == w then (if a == c then some (fl, none) else none)
      else if t == c then none
      else some (fl, some c)
  | .ccx _ _ t =>
    match st with
    | none => none
    | some (fl, none) => if t == w then none else some (fl, none)
    | some (fl, some c) => if t == w || t == c then none else some (fl, some c)
  | .make _ _ t =>
    match st with
    | none => none
    | some (fl, none) => if t == w then none else some (fl, none)
    | some (fl, some c) => if t == w || t == c then none else some (fl, some c)
  | .pop _ _ t =>
    if t == w then some (false, none)
    else match st with
    | none => none
    | some (fl, none) => some (fl, none)
    | some (fl, some c) => if t == c then none else some (fl, some c)

def trackList (w : Wire) (st : Option (Bool × Option Wire)) (gs : List Gate) :
    Option (Bool × Option Wire) :=
  gs.foldl (trackStep w) st

def TrackHolds (w : Wire) (s : State) : Option (Bool × Option Wire) → Prop
  | none => True
  | some (fl, none) => s.basis w = fl
  | some (fl, some c) => c ≠ w ∧ s.basis w = (fl ^^ s.basis c)

theorem run_front_basis (g : Gate) (m : List Bool) (s : State) (q : Wire) :
    (run [front g] m s).basis q =
      match g with
      | .x t => if q = t then !s.basis t else s.basis q
      | .cx a t => if q = t then (s.basis t ^^ s.basis a) else s.basis q
      | .ccx a b t => if q = t then (s.basis t ^^ (s.basis a && s.basis b)) else s.basis q
      | .make a b t => if q = t then (s.basis t ^^ (s.basis a && s.basis b)) else s.basis q
      | .pop _ _ t => if q = t then false else s.basis q := by
  cases g <;> simp [front, run, writeBit, Function.update_apply, GateMirror.erase, measureAndCorrect]

theorem trackStep_sound (w : Wire) (s : State) (st : Option (Bool × Option Wire)) (g : Gate)
    (m : List Bool) (h : TrackHolds w s st) : TrackHolds w (run [front g] m s) (trackStep w st g) := by
  rcases st with _ | ⟨fl, _ | c⟩ <;> cases g <;>
    simp only [trackStep, TrackHolds, beq_iff_eq, Bool.or_eq_true] at h ⊢ <;>
    (try split_ifs) <;> simp only [run_front_basis] <;>
    (try split_ifs) <;> (try subst_vars) <;> (try simp_all)

theorem trackList_sound (w : Wire) (gs : List Gate) (s : State) (st : Option (Bool × Option Wire))
    (m : List Bool) (h : TrackHolds w s st) :
    TrackHolds w (run (GateMirror.forward gs) m s) (trackList w st gs) := by
  induction gs generalizing s st m with
  | nil => exact h
  | cons g gs ih =>
    change TrackHolds w (run ([front g] ++ GateMirror.forward gs) m s) (trackList w (trackStep w st g) gs)
    rw [run_append]
    exact ih _ _ _ (trackStep_sound w s st g _ h)

theorem trackList_const (w : Wire) (gs : List Gate) (fl : Bool) (s : State)
    (st : Option (Bool × Option Wire)) (h : TrackHolds w s st)
    (heq : trackList w st gs = some (fl, none)) (m : List Bool := []) :
    (run (GateMirror.forward gs) m s).basis w = fl := by
  have hs := trackList_sound w gs s st m h
  rw [heq] at hs
  exact hs

/-! ### 2. Top-of-chain measured erase for `chainG` inverses -/

/-- Inverse of `chainG c seq [.cx (c (i + n)) out, .x out] i n` with the innermost
    4-gate `[CCX a b z, X out, CX z out, erase a b z]` replaced by `[X out, erase a b out]`. -/
def chainTopInv (c seq : Nat → Wire) (out : Wire) (i : Nat) : Nat → Program
  | 0 => [.X out, .CX (c i) out]
  | 1 => [.X out, GateMirror.erase (c i) (seq i) out]
  | k + 2 => [.CCX (c i) (seq i) (c (i + 1))] ++
      chainTopInv c seq out (i + 1) (k + 1) ++
      [GateMirror.erase (c i) (seq i) (c (i + 1))]

theorem inv_chainG_one (c seq : Nat → Wire) (out : Wire) (i : Nat) :
    GateMirror.inverse (chainG c seq [.cx (c (i + 1)) out, .x out] i 1) =
      [.CCX (c i) (seq i) (c (i + 1)), .X out, .CX (c (i + 1)) out,
       GateMirror.erase (c i) (seq i) (c (i + 1))] := rfl

theorem inv_chainG_step (c seq : Nat → Wire) (out : Wire) (i k : Nat) :
    GateMirror.inverse (chainG c seq [.cx (c (i + (k + 2))) out, .x out] i (k + 2)) =
      [.CCX (c i) (seq i) (c (i + 1))] ++
      GateMirror.inverse (chainG c seq [.cx (c ((i + 1) + (k + 1))) out, .x out] (i + 1) (k + 1)) ++
      [GateMirror.erase (c i) (seq i) (c (i + 1))] := by
  have hi : i + (k + 2) = (i + 1) + (k + 1) := by omega
  rw [hi]
  have hc : chainG c seq [.cx (c ((i + 1) + (k + 1))) out, .x out] i (k + 2) =
      [.make (c i) (seq i) (c (i + 1))] ++
      (chainG c seq [.cx (c ((i + 1) + (k + 1))) out, .x out] (i + 1) (k + 1) ++
       [.pop (c i) (seq i) (c (i + 1))]) := rfl
  rw [hc, FredCut.inv_app, FredCut.inv_app]
  simp only [GateMirror.inverse, GateMirror.back, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc]

theorem chainTopInv_counts (c seq : Nat → Wire) (out : Wire) :
    ∀ (i n : Nat), 1 ≤ n →
      toffoliCount (chainTopInv c seq out i n) + 1 =
        toffoliCount (GateMirror.inverse (chainG c seq [.cx (c (i + n)) out, .x out] i n)) ∧
      measurementCount (chainTopInv c seq out i n) =
        measurementCount (GateMirror.inverse (chainG c seq [.cx (c (i + n)) out, .x out] i n)) ∧
      gateSlots (chainTopInv c seq out i n) + 2 =
        gateSlots (GateMirror.inverse (chainG c seq [.cx (c (i + n)) out, .x out] i n))
  | _, 0, h => by omega
  | i, 1, _ => by
    rw [inv_chainG_one]
    simp [chainTopInv, GateMirror.erase, toffoliCount, measurementCount, gateSlots, instructionSlots]
  | i, k + 2, _ => by
    rw [inv_chainG_step]
    have ih := chainTopInv_counts c seq out (i + 1) (k + 1) (by omega)
    simp only [chainTopInv, toffoliCount_append, measurementCount_append, gateSlots_append]
    exact ⟨by omega, by omega, by omega⟩

theorem chainTopInv_wires_sub (c seq : Nat → Wire) (out : Wire) :
    ∀ (i n : Nat), 1 ≤ n →
      wires (chainTopInv c seq out i n) ⊆
        wires (GateMirror.inverse (chainG c seq [.cx (c (i + n)) out, .x out] i n))
  | _, 0, h => by omega
  | i, 1, _ => by
    rw [inv_chainG_one]
    intro q hq
    simp only [chainTopInv, GateMirror.erase, wires, Instr.wires, correctionWires,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
    tauto
  | i, k + 2, _ => by
    rw [inv_chainG_step]
    have ih := chainTopInv_wires_sub c seq out (i + 1) (k + 1) (by omega)
    intro q hq
    simp only [chainTopInv, wires_append, Finset.mem_union] at hq ⊢
    rcases hq with (h1 | h2) | h3
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (ih h2))
    · exact Or.inr h3

theorem chainTopInv_physical (c seq : Nat → Wire) (out : Wire) :
    ∀ (i n : Nat), 1 ≤ n →
      GatePhysical (GateMirror.inverse (chainG c seq [.cx (c (i + n)) out, .x out] i n)) →
      GatePhysical (chainTopInv c seq out i n)
  | _, 0, h, _ => by omega
  | i, 1, _, _ => by
    intro ins hi
    simp only [chainTopInv, GateMirror.erase, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> trivial
  | i, k + 2, _, hp => by
    rw [inv_chainG_step, gatePhysical_append, gatePhysical_append] at hp
    simp only [chainTopInv, gatePhysical_append]
    exact ⟨⟨hp.1.1, chainTopInv_physical c seq out (i + 1) (k + 1) (by omega) hp.1.2⟩, hp.2⟩

theorem undo_base (a b z out : Wire) (s : State) (r : List Bool)
    (haz : a ≠ z) (hbz : b ≠ z) (hzo : z ≠ out) (hao : a ≠ out) (hbo : b ≠ out)
    (hz : s.basis z = false) (ho : s.basis out = false) :
    run [.X out, GateMirror.erase a b out] r
      (run (GateMirror.forward [.make a b z, .cx z out, .x out, .pop a b z]) [] s) = s := by
  apply State.extensionality
  · rcases r with _ | ⟨_ | _, r⟩ <;> cases hph : s.phase <;> cases ha : s.basis a <;> cases hb : s.basis b <;>
      simp [GateMirror.forward, GateMirror.front, GateMirror.erase, run, measureAndCorrect,
        ECDSAAdd.correct, writeBit, Function.update_apply, haz, hbz, hzo, hao, hbo,
        haz.symm, hbz.symm, hzo.symm, hao.symm, hbo.symm, hz, ho, hph, ha, hb]
  · funext q
    by_cases hqo : q = out
    · subst hqo
      rcases r with _ | ⟨_ | _, r⟩ <;>
        simp [GateMirror.forward, GateMirror.front, GateMirror.erase, run, measureAndCorrect,
          ECDSAAdd.correct, writeBit, Function.update_apply, haz, hbz, hzo, hao, hbo,
          haz.symm, hbz.symm, hzo.symm, hao.symm, hbo.symm, hz, ho]
    · by_cases hqz : q = z
      · subst hqz
        rcases r with _ | ⟨_ | _, r⟩ <;>
          simp [GateMirror.forward, GateMirror.front, GateMirror.erase, run, measureAndCorrect,
            ECDSAAdd.correct, writeBit, Function.update_apply, haz, hbz, hzo, hao, hbo,
            haz.symm, hbz.symm, hzo.symm, hao.symm, hbo.symm, hz, ho]
      · rcases r with _ | ⟨_ | _, r⟩ <;>
          simp [GateMirror.forward, GateMirror.front, GateMirror.erase, run, measureAndCorrect,
            ECDSAAdd.correct, writeBit, Function.update_apply, hqo, hqz]

theorem pop_ccx_cancel (a b z : Wire) (w : State) (haz : a ≠ z) (hbz : b ≠ z)
    (hval : w.basis z = (w.basis a && w.basis b)) :
    run [.CCX a b z] [] (run [GateMirror.erase a b z] [] w) = w := by
  apply State.extensionality
  · simp [GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct]
  · funext q
    by_cases hqz : q = z
    · subst hqz
      simp [GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, writeBit,
        Function.update_apply, haz, hbz, hval]
    · simp [GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, writeBit,
        Function.update_apply, hqz]

theorem ccx_erase_cancel (a b z : Wire) (s : State) (r : List Bool)
    (haz : a ≠ z) (hbz : b ≠ z) (hz : s.basis z = false) :
    run [GateMirror.erase a b z] r (run [.CCX a b z] [] s) = s := by
  apply State.extensionality
  · rcases r with _ | ⟨_ | _, r⟩ <;> cases hph : s.phase <;> cases ha : s.basis a <;> cases hb : s.basis b <;>
      simp [GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, writeBit,
        Function.update_apply, haz, hbz, hz, hph, ha, hb]
  · funext q
    by_cases hqz : q = z
    · subst hqz
      rcases r with _ | ⟨_ | _, r⟩ <;>
        simp [GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, writeBit,
          Function.update_apply, haz, hbz, hz]
    · rcases r with _ | ⟨_ | _, r⟩ <;>
        simp [GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, writeBit,
          Function.update_apply, hqz]

theorem chainTopInv_undo (c seq : Nat → Wire) (out : Wire) :
    ∀ (i n : Nat) (s : State) (m r : List Bool), 1 ≤ n →
      DeadJoin.RawValid s (chainG c seq [.cx (c (i + n)) out, .x out] i n) →
      s.basis out = false →
      (∀ k, i ≤ k → k < i + n → c k ≠ out ∧ seq k ≠ out ∧ c (k + 1) ≠ out) →
      run (chainTopInv c seq out i n) r
        (run (GateMirror.forward (chainG c seq [.cx (c (i + n)) out, .x out] i n)) m s) = s
  | _, 0, _, _, _, h, _, _, _ => by omega
  | i, 1, s, m, r, _, v, ho, hne => by
    rw [v.default_run m]
    have hp1 : c i ≠ c (i + 1) ∧ seq i ≠ c (i + 1) :=
      of_decide_eq_true (v.physical _ List.mem_cons_self)
    have hz : s.basis (c (i + 1)) = false := v.ready.1
    have h0 := hne i (Nat.le_refl _) (by omega)
    exact undo_base (c i) (seq i) (c (i + 1)) out s r hp1.1 hp1.2 h0.2.2 h0.1 h0.2.1 hz ho
  | i, k + 2, s, m, r, _, v, ho, hne => by
    rw [v.default_run m]
    have hi : i + (k + 2) = (i + 1) + (k + 1) := by omega
    have h0 := hne i (Nat.le_refl _) (by omega)
    have hsplit : chainG c seq [.cx (c (i + (k + 2))) out, .x out] i (k + 2) =
        [.make (c i) (seq i) (c (i + 1))] ++
        (chainG c seq [.cx (c ((i + 1) + (k + 1))) out, .x out] (i + 1) (k + 1) ++
         [.pop (c i) (seq i) (c (i + 1))]) := by rw [hi]; rfl
    rw [hsplit] at v ⊢
    obtain ⟨v1, v23⟩ := v.parts
    obtain ⟨v2, v3⟩ := v23.parts
    have hp1 : c i ≠ c (i + 1) ∧ seq i ≠ c (i + 1) :=
      of_decide_eq_true (v1.physical _ List.mem_cons_self)
    have hz : s.basis (c (i + 1)) = false := v1.ready.1
    set u := run (GateMirror.forward [.make (c i) (seq i) (c (i + 1))]) [] s with hu
    have hu_eq : u = run [.CCX (c i) (seq i) (c (i + 1))] [] s := rfl
    have hu_out : u.basis out = false := by
      rw [hu_eq]; simp [run, writeBit, Function.update_apply, h0.2.2.symm, ho]
    set w := run (GateMirror.forward (chainG c seq [.cx (c ((i + 1) + (k + 1))) out, .x out] (i + 1) (k + 1))) [] u
    have hw_val : w.basis (c (i + 1)) = (w.basis (c i) && w.basis (seq i)) := v3.prepared.1
    have hfwd : run (GateMirror.forward ([.make (c i) (seq i) (c (i + 1))] ++
        (chainG c seq [.cx (c ((i + 1) + (k + 1))) out, .x out] (i + 1) (k + 1) ++
         [.pop (c i) (seq i) (c (i + 1))]))) [] s =
        run [GateMirror.erase (c i) (seq i) (c (i + 1))] [] w := by
      simp only [Partial.forward_app, run_append, run_take, List.drop_nil]
      rfl
    rw [hfwd]
    simp only [chainTopInv, List.append_assoc, run_append,
      show measurementCount [Instr.CCX (c i) (seq i) (c (i + 1))] = 0 from rfl,
      List.take_zero, List.drop_zero]
    rw [pop_ccx_cancel (c i) (seq i) (c (i + 1)) w hp1.1 hp1.2 hw_val]
    have ih := chainTopInv_undo c seq out (i + 1) (k + 1) u []
      (r.take (measurementCount (chainTopInv c seq out (i + 1) (k + 1)))) (by omega) v2 hu_out
      (fun j hj1 hj2 => hne j (by omega) (by omega))
    rw [ih, hu_eq]
    exact ccx_erase_cancel (c i) (seq i) (c (i + 1)) s _ hp1.1 hp1.2 hz

/-! ### 3. General helper: replace a `chainMid` inverse inside an already-proven leave/unleave -/

theorem cx_pop_inv (top : Wire) (u : State) (h1558 : u.basis 1558 = true)
    (htop : top ≠ 1559) (hval : u.basis 1559 = (u.basis 1558 && u.basis top)) :
    run [.CX top 1559] [] (run (GateMirror.forward [.pop 1558 top 1559]) [] u) = u := by
  rw [h1558, Bool.true_and] at hval
  apply State.extensionality
  · simp [GateMirror.forward, GateMirror.front, GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct]
  · funext q
    by_cases hq : q = 1559
    · subst hq
      simp [GateMirror.forward, GateMirror.front, GateMirror.erase, run, measureAndCorrect,
        ECDSAAdd.correct, writeBit, Function.update_apply, htop, hval]
    · simp [GateMirror.forward, GateMirror.front, GateMirror.erase, run, measureAndCorrect,
        ECDSAAdd.correct, writeBit, Function.update_apply, hq]

/-! ### 4. Family 1: Narrow 15-tick blocks (`j ≤ 24`) -/

def pre7S (s : Nat) : List Gate :=
  DeadJoin.keptHead s ++ KeptParity.placed s ++ DeadJoin.selPre s ++
  DeadJoin.receiver 1565 false (DeadJoin.selectorSources s) ++
  DeadJoin.selPost s ++ DeadJoin.afterPre7Tail s ++ [.cx (DeadJoin.topW7 s) 1559]

def post7S (s : Nat) : List Gate :=
  [.cx (DeadJoin.topW7 s) 1559] ++ DeadJoin.afterPost7 s

theorem after7S_split_chain (s : Nat) :
    DeadJoin.after7S s = pre7S s ++ (DeadJoin.chainMid7 s ++ post7S s) := by
  rw [DeadJoin.after7S_sel]
  simp only [DeadJoin.selTail, pre7S, post7S, List.append_assoc]

def chainTopInv7 (s : Nat) : Program :=
  let L := Shadow7.lowsP s
  let top := Shadow7.a0P s + L - 2
  let H := Shadow7.liveW s - L
  chainTopInv (Shadow7.storeW s) (fun i => if i = 0 then top else Shadow7.bankW s (L + i - 1)) 1557 1 H

def after7STopInv (s : Nat) : Program :=
  GateMirror.inverse (post7S s) ++ chainTopInv7 s ++ GateMirror.inverse (pre7S s)

def unleave15Top (j : Fin 26) : Program :=
  let s := start j
  if j.val ≤ 24 then
    after7STopInv s ++ CRTBarrel.barrel s true ++ GateMirror.inverse (CRTBarrel.before s)
  else Shadow7.leaveMoveInvP j

def unleave15CTop (j : Fin 26) : Program :=
  if j.val ≤ 24 then
    (unleave15Top j).take (K15 j) ++ (unleave15Top j).drop (K15 j + 6)
  else unleave15Top j

theorem hH7_pos : ∀ j : Fin 26, j.val ≤ 24 →
    1 ≤ Shadow7.liveW (start j) - Shadow7.lowsP (start j) := by decide +kernel

theorem hne7_1557 : ∀ j : Fin 26, (j.val ≤ 6 ∨ (20 ≤ j.val ∧ j.val ≤ 24)) →
    let s := start j
    let L := Shadow7.lowsP s
    let H := Shadow7.liveW s - L
    (List.range H).all (fun d =>
      let k := 1 + d
      Shadow7.storeW s k != 1557 &&
      Shadow7.bankW s (L + k - 1) != 1557 &&
      Shadow7.storeW s (k + 1) != 1557) = true := by decide +kernel

theorem track1557_before5 : ∀ j : Fin 26, (j.val ≤ 6 ∨ (20 ≤ j.val ∧ j.val ≤ 24)) →
    trackList 1557 none (DeadJoin.before5 (start j)) = some (false, none) := by decide +kernel

theorem track1557_barrel7 : ∀ j : Fin 26, (j.val ≤ 6 ∨ (20 ≤ j.val ∧ j.val ≤ 24)) →
    trackList 1557 (some (false, none)) (Shadow7.leaveBarrel (start j)) = some (false, none) := by decide +kernel

theorem track1557_pre7S : ∀ j : Fin 26, (j.val ≤ 6 ∨ (20 ≤ j.val ∧ j.val ≤ 24)) →
    trackList 1557 (some (false, none)) (pre7S (start j)) = some (false, none) := by decide +kernel

theorem unleave15Top_metrics (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (unleave15Top j) + 1 = toffoliCount (CRTBarrel.unleave j) ∧
    measurementCount (unleave15Top j) = measurementCount (CRTBarrel.unleave j) ∧
    gateSlots (unleave15Top j) + 2 = gateSlots (CRTBarrel.unleave j) ∧
    wires (unleave15Top j) ⊆ wires (CRTBarrel.unleave j) ∧
    GatePhysical (unleave15Top j) := by
  have hphys := (CRTWindow.leave_phys j (by omega) hi).2
  have hU : CRTBarrel.unleave j =
      (GateMirror.inverse (post7S (start j)) ++ GateMirror.inverse (DeadJoin.chainMid7 (start j)) ++
        GateMirror.inverse (pre7S (start j))) ++
      CRTBarrel.barrel (start j) true ++ GateMirror.inverse (CRTBarrel.before (start j)) := by
    rw [CRTBarrel.unleave, if_pos hi, CRTBarrel.afterPart, after7S_split_chain]
    simp only [FredCut.inv_app, List.append_assoc]
  have hT : unleave15Top j =
      (GateMirror.inverse (post7S (start j)) ++ chainTopInv7 (start j) ++
        GateMirror.inverse (pre7S (start j))) ++
      CRTBarrel.barrel (start j) true ++ GateMirror.inverse (CRTBarrel.before (start j)) := by
    simp only [unleave15Top, hi, ↓reduceIte, after7STopInv]
  have hcm : DeadJoin.chainMid7 (start j) =
      chainG (Shadow7.storeW (start j))
        (fun i => if i = 0 then Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2
          else Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i - 1))
        [.cx (Shadow7.storeW (start j) (1 + (Shadow7.liveW (start j) - Shadow7.lowsP (start j)))) 1557, .x 1557]
        1 (Shadow7.liveW (start j) - Shadow7.lowsP (start j)) := by
    unfold DeadJoin.chainMid7
    rw [Nat.add_comm 1 (Shadow7.liveW (start j) - Shadow7.lowsP (start j))]
  have hc : toffoliCount (chainTopInv7 (start j)) + 1 =
        toffoliCount (GateMirror.inverse (DeadJoin.chainMid7 (start j))) ∧
      measurementCount (chainTopInv7 (start j)) =
        measurementCount (GateMirror.inverse (DeadJoin.chainMid7 (start j))) ∧
      gateSlots (chainTopInv7 (start j)) + 2 =
        gateSlots (GateMirror.inverse (DeadJoin.chainMid7 (start j))) := by
    rw [hcm]; exact chainTopInv_counts _ _ 1557 1 _ (hH7_pos j hi)
  have hw : wires (chainTopInv7 (start j)) ⊆ wires (GateMirror.inverse (DeadJoin.chainMid7 (start j))) := by
    rw [hcm]; exact chainTopInv_wires_sub _ _ 1557 1 _ (hH7_pos j hi)
  rw [hU] at hphys
  simp only [gatePhysical_append] at hphys
  have hpc : GatePhysical (chainTopInv7 (start j)) := by
    have hp0 := hphys.1.1.1.2
    rw [hcm] at hp0
    exact chainTopInv_physical _ _ 1557 1 _ (hH7_pos j hi) hp0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, hU]; simp only [toffoliCount_append]; omega
  · rw [hT, hU]; simp only [measurementCount_append]; omega
  · rw [hT, hU]; simp only [gateSlots_append]; omega
  · intro q hq
    rw [hT] at hq; rw [hU]
    simp only [wires_append, Finset.mem_union] at hq ⊢
    rcases hq with (((h1 | h2) | h3) | h4) | h5
    · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (hw h2))))
    · exact Or.inl (Or.inl (Or.inr h3))
    · exact Or.inl (Or.inr h4)
    · exact Or.inr h5
  · rw [hT]
    simp only [gatePhysical_append]
    exact ⟨⟨⟨⟨hphys.1.1.1.1, hpc⟩, hphys.1.1.2⟩, hphys.1.2⟩, hphys.2⟩

theorem unleave15Top_undo {j : Fin 26} (hi : j.val ≤ 24) (hu : j.val ≤ 6 ∨ (20 ≤ j.val ∧ j.val ≤ 24)) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : LeaveJ7.Admission.Inputs j s z g sg) (m n : List Bool) :
    run (unleave15Top j) n (run (CRTBarrel.leave j) m s) = s := by
  have hold := (LeaveJ7.Admission.Inputs.crt_pair (Nat.zero_le _) hi h).2 m n
  have original : CRTBarrel.LeaveSplice.Valid s (DeadJoin.referenceOps (start j)) := by
    change CRTBarrel.LeaveSplice.Valid s (Shadow7.leaveMoveOps (start j))
    exact CRTBarrel.LeaveSplice.moved_valid (Nat.zero_le _) hi h
  have raw : DeadJoin.RawValid s (DeadJoin.referenceOps (start j)) :=
    ⟨original.physical, original.prepared, original.ready⟩
  have rel : FlagLeave.Rel (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4)
      (Shadow7.e0P (start j) + 6) false s := by
    simp only [FlagLeave.Rel, Bool.false_and, Bool.xor_false]
    rw [h.far, h.side]
    cases decide (Shadow.far (Shadow7.sbP (start j)) 15 z) <;>
      cases decide (2 ^ Shadow7.sbP (start j) ≤ z.u) <;> rfl
  have zero6 : s.basis (Shadow7.e0P (start j) + 6) = false := h.zero _ (by simp [LeaveJ7.watched])
  have keptRel : KeptParity.relation (fun q => (run (GateMirror.forward (CRTBarrel.beforeReference (start j) ++
      (Shadow7.leaveBarrel (start j) ++ DeadJoin.keptHead (start j)))) [] s).basis (KeptParity.port (start j) q)) := by
    have shape : CRTBarrel.beforeReference (start j) ++ (Shadow7.leaveBarrel (start j) ++ DeadJoin.keptHead (start j)) =
        Shadow7.moveA (start j) ++ (GateMirror.rowGates (Shadow7.e0P (start j) + 6) (Shadow7.moveRows (start j)) ++
          Shadow7.moveB (start j)) := by
      simp only [CRTBarrel.beforeReference, DeadJoin.keptHead, Shadow7.leaveFix5Move,
        Shadow7.moveA, Shadow7.moveB, List.append_assoc]
    rw [shape]
    exact h.movedRelation (Nat.zero_le _) hi
  obtain ⟨valid, _, whole⟩ := DeadJoin.raw_crt_all_valid57 j hi s raw
    (DeadJoin.pair_zero j hi s (DeadJoin.entry_top_zero hi h))
    (DeadJoin.admitted_scan_eq hi h) rel zero6 keptRel (h.zero _ (by simp [LeaveJ7.watched]))
  have hRef : run (CRTBarrel.leave j) m s =
      run (GateMirror.forward (DeadJoin.before5 (start j) ++
        (Shadow7.leaveBarrel (start j) ++ DeadJoin.after7S (start j)))) [] s := by
    have e : run (CRTBarrel.leave j) m s = run (GateMirror.forward (DeadJoin.referenceOps (start j))) m s := by
      have hp := (DeadJoin.crt_all_pair hi h original).1 m
      simpa only [CRTBarrel.leave, hi, ↓reduceIte, CRTBarrel.before, CRTBarrel.afterPart] using hp
    rw [e, ← whole m, valid.default_run m]
  have hshape : DeadJoin.before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ DeadJoin.after7S (start j)) =
      (DeadJoin.before5 (start j) ++ Shadow7.leaveBarrel (start j) ++ pre7S (start j)) ++
      (DeadJoin.chainMid7 (start j) ++ post7S (start j)) := by
    rw [after7S_split_chain]; simp only [List.append_assoc]
  rw [hshape] at valid hRef
  obtain ⟨vPre, vCP⟩ := valid.parts
  obtain ⟨vChain, vPost⟩ := vCP.parts
  set u0 := run (GateMirror.forward (DeadJoin.before5 (start j) ++
      Shadow7.leaveBarrel (start j) ++ pre7S (start j))) [] s with hu0
  set u1 := run (GateMirror.forward (DeadJoin.chainMid7 (start j))) [] u0 with hu1
  have hu0_1557 : u0.basis 1557 = false := by
    rw [hu0]
    simp only [Partial.forward_app, run_append, run_take, List.drop_nil]
    have t1 : (run (GateMirror.forward (DeadJoin.before5 (start j))) [] s).basis 1557 = false :=
      trackList_const 1557 _ false s none trivial (track1557_before5 j hu)
    have t2 : (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) []
        (run (GateMirror.forward (DeadJoin.before5 (start j))) [] s)).basis 1557 = false :=
      trackList_const 1557 _ false _ (some (false, none)) t1 (track1557_barrel7 j hu)
    exact trackList_const 1557 _ false _ (some (false, none)) t2 (track1557_pre7S j hu)
  have hcm : DeadJoin.chainMid7 (start j) =
      chainG (Shadow7.storeW (start j))
        (fun i => if i = 0 then Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2
          else Shadow7.bankW (start j) (Shadow7.lowsP (start j) + i - 1))
        [.cx (Shadow7.storeW (start j) (1 + (Shadow7.liveW (start j) - Shadow7.lowsP (start j)))) 1557, .x 1557]
        1 (Shadow7.liveW (start j) - Shadow7.lowsP (start j)) := by
    unfold DeadJoin.chainMid7
    rw [Nat.add_comm 1 (Shadow7.liveW (start j) - Shadow7.lowsP (start j))]
  have hne : ∀ k, 1 ≤ k → k < 1 + (Shadow7.liveW (start j) - Shadow7.lowsP (start j)) →
      Shadow7.storeW (start j) k ≠ 1557 ∧
      (if k = 0 then Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 2
        else Shadow7.bankW (start j) (Shadow7.lowsP (start j) + k - 1)) ≠ 1557 ∧
      Shadow7.storeW (start j) (k + 1) ≠ 1557 := by
    intro k hk1 hk2
    have hd := List.all_eq_true.mp (hne7_1557 j hu) (k - 1) (List.mem_range.mpr (by omega))
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
    rw [show 1 + (k - 1) = k by omega] at hd
    rw [if_neg (by omega)]
    exact ⟨hd.1.1, hd.1.2, hd.2⟩
  have hbackTop (t : List Bool) : run (chainTopInv7 (start j)) t u1 = u0 := by
    rw [hu1, hcm]
    exact chainTopInv_undo _ _ 1557 1 (Shadow7.liveW (start j) - Shadow7.lowsP (start j))
      u0 [] t (hH7_pos j hi) (hcm ▸ vChain) hu0_1557 hne
  have hbackOld (t : List Bool) : run (GateMirror.inverse (DeadJoin.chainMid7 (start j))) t u1 = u0 := by
    rw [hu1]; exact vChain.undo_run [] t
  have hU : CRTBarrel.unleave j =
      GateMirror.inverse (post7S (start j)) ++ GateMirror.inverse (DeadJoin.chainMid7 (start j)) ++
      (GateMirror.inverse (pre7S (start j)) ++ CRTBarrel.barrel (start j) true ++
        GateMirror.inverse (CRTBarrel.before (start j))) := by
    rw [CRTBarrel.unleave, if_pos hi, CRTBarrel.afterPart, after7S_split_chain]
    simp only [FredCut.inv_app, List.append_assoc]
  have hT : unleave15Top j =
      GateMirror.inverse (post7S (start j)) ++ chainTopInv7 (start j) ++
      (GateMirror.inverse (pre7S (start j)) ++ CRTBarrel.barrel (start j) true ++
        GateMirror.inverse (CRTBarrel.before (start j))) := by
    simp only [unleave15Top, hi, ↓reduceIte, after7STopInv, List.append_assoc]
  have hmc : measurementCount (chainTopInv7 (start j)) =
      measurementCount (GateMirror.inverse (DeadJoin.chainMid7 (start j))) := by
    rw [hcm]; exact (chainTopInv_counts _ _ 1557 1 _ (hH7_pos j hi)).2.1
  have hEnd : run (CRTBarrel.leave j) m s = run (GateMirror.forward (post7S (start j))) [] u1 := by
    rw [hRef, Partial.forward_app (DeadJoin.before5 (start j) ++ Shadow7.leaveBarrel (start j) ++ pre7S (start j))
        (DeadJoin.chainMid7 (start j) ++ post7S (start j)),
      run_append, List.take_nil, List.drop_nil, ← hu0,
      Partial.forward_app (DeadJoin.chainMid7 (start j)) (post7S (start j)),
      run_append, List.take_nil, List.drop_nil, ← hu1]
  rw [hU] at hold
  rw [hT]
  simp only [run_append, measurementCount_append] at hold ⊢
  rw [hEnd, vPost.undo_run [] _, hbackTop]
  rw [hEnd, vPost.undo_run [] _, hbackOld] at hold
  rwa [hmc]

/-! ### 5. Family 2: Transition 150 block (`j7 = ⟨7, _⟩`, `s = 150`) -/

def pre150 : List Gate :=
  tailD0_150 ++ tailD1_150 ++ [.cx (Shadow7.e0P 150 + 4) 1559] ++
  tailE0_150 ++ [.cx (Shadow7.a0P 150 + lows150 - 2) 1559]

def post150 : List Gate :=
  [.cx (Shadow7.a0P 150 + lows150 - 2) 1559] ++ tailE1_150

theorem afterRow150_split_chain :
    afterRow150 = pre150 ++ (chainMid150 ++ post150) := by
  simp only [afterRow150, pre150, post150, List.append_assoc]

def chainTopInv150 : Program :=
  let L := lows150
  let top := Shadow7.a0P 150 + L - 2
  let H := Shadow7.liveW 150 - L
  chainTopInv (Shadow7.storeW 150) (fun i => if i = 0 then top else Shadow7.bankW 150 (L + i - 1)) 1557 1 H

def after150TopInv : Program :=
  GateMirror.inverse post150 ++ chainTopInv150 ++ GateMirror.inverse pre150

def unleave150Top : Program :=
  after150TopInv ++ CRTBarrel.barrel 150 true ++ GateMirror.inverse (CRTBarrel.before 150)

def unleave150CTop : Program :=
  unleave150Top.take K150 ++ unleave150Top.drop (K150 + 6)

theorem hH150_pos : 1 ≤ Shadow7.liveW 150 - lows150 := by decide

theorem hne150_1557 :
    let L := lows150
    let H := Shadow7.liveW 150 - L
    (List.range H).all (fun d =>
      let k := 1 + d
      Shadow7.storeW 150 k != 1557 &&
      Shadow7.bankW 150 (L + k - 1) != 1557 &&
      Shadow7.storeW 150 (k + 1) != 1557) = true := by decide +kernel

theorem track1557_beforeRef150 :
    trackList 1557 none (CRTBarrel.beforeReference 150) = some (false, none) := by decide +kernel

theorem track1557_barrel150 :
    trackList 1557 (some (false, none)) (Shadow7.leaveBarrel 150) = some (false, none) := by decide +kernel

theorem track1557_pre150Ref :
    let top := Shadow7.a0P 150 + lows150 - 2
    trackList 1557 (some (false, none))
      (tailD0_150 ++ pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++
       tailD1_150 ++ [.pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559] ++
       tailE0_150 ++ [.make 1558 top 1559]) = some (false, none) := by decide +kernel

theorem track1558_mid150 :
    let top := Shadow7.a0P 150 + lows150 - 2
    trackList 1558 none (tailE0_150 ++ [.make 1558 top 1559] ++ chainMid150) = some (true, none) := by
  decide +kernel

theorem unleave150Top_metrics :
    toffoliCount unleave150Top + 1 = toffoliCount leaveInv150To20Red ∧
    measurementCount unleave150Top = measurementCount leaveInv150To20Red ∧
    gateSlots unleave150Top + 2 = gateSlots leaveInv150To20Red ∧
    wires unleave150Top ⊆ wires leaveInv150To20Red ∧
    GatePhysical unleave150Top := by
  have hphys := leave150To20Red_phys.2
  have hU : leaveInv150To20Red =
      (GateMirror.inverse post150 ++ GateMirror.inverse chainMid150 ++ GateMirror.inverse pre150) ++
      CRTBarrel.barrel 150 true ++ GateMirror.inverse (CRTBarrel.before 150) := by
    rw [leaveInv150To20Red, afterRow150_split_chain]
    simp only [FredCut.inv_app, List.append_assoc]
  have hT : unleave150Top =
      (GateMirror.inverse post150 ++ chainTopInv150 ++ GateMirror.inverse pre150) ++
      CRTBarrel.barrel 150 true ++ GateMirror.inverse (CRTBarrel.before 150) := by
    simp only [unleave150Top, after150TopInv]
  have hcm : chainMid150 =
      chainG (Shadow7.storeW 150)
        (fun i => if i = 0 then Shadow7.a0P 150 + lows150 - 2
          else Shadow7.bankW 150 (lows150 + i - 1))
        [.cx (Shadow7.storeW 150 (1 + (Shadow7.liveW 150 - lows150))) 1557, .x 1557]
        1 (Shadow7.liveW 150 - lows150) := by
    unfold chainMid150
    rw [Nat.add_comm 1 (Shadow7.liveW 150 - lows150)]
  have hc : toffoliCount chainTopInv150 + 1 = toffoliCount (GateMirror.inverse chainMid150) ∧
      measurementCount chainTopInv150 = measurementCount (GateMirror.inverse chainMid150) ∧
      gateSlots chainTopInv150 + 2 = gateSlots (GateMirror.inverse chainMid150) := by
    rw [hcm]; exact chainTopInv_counts _ _ 1557 1 _ hH150_pos
  have hw : wires chainTopInv150 ⊆ wires (GateMirror.inverse chainMid150) := by
    rw [hcm]; exact chainTopInv_wires_sub _ _ 1557 1 _ hH150_pos
  rw [hU] at hphys
  simp only [gatePhysical_append] at hphys
  have hpc : GatePhysical chainTopInv150 := by
    have hp0 := hphys.1.1.1.2
    rw [hcm] at hp0
    exact chainTopInv_physical _ _ 1557 1 _ hH150_pos hp0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, hU]; simp only [toffoliCount_append]; omega
  · rw [hT, hU]; simp only [measurementCount_append]; omega
  · rw [hT, hU]; simp only [gateSlots_append]; omega
  · rw [hT, hU]
    simp only [wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union
      (Finset.union_subset_union (Finset.Subset.refl _) hw) (Finset.Subset.refl _)) (Finset.Subset.refl _))
      (Finset.Subset.refl _)
  · rw [hT]
    simp only [gatePhysical_append]
    exact ⟨⟨⟨⟨hphys.1.1.1.1, hpc⟩, hphys.1.1.2⟩, hphys.1.2⟩, hphys.2⟩

/-- Core undo helper for transition block 150 (called from `Trans150` in `MainQ1.lean`). -/
theorem unleave150Top_undo_core (s uB : State) (m n : List Bool)
    (h1557_uB : uB.basis 1557 = false)
    (hEnd : run leave150To20Red m s = run (GateMirror.forward leaveAfter150To20) [] uB)
    (vAft : CRTBarrel.LeaveSplice.Valid uB leaveAfter150To20)
    (hSplit : let top := Shadow7.a0P 150 + lows150 - 2
      leaveAfter150To20 = (tailD0_150 ++ pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++
        tailD1_150 ++ [.pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559] ++
        tailE0_150 ++ [.make 1558 top 1559]) ++
      (chainMid150 ++ ([.pop 1558 top 1559] ++ tailE1_150)))
    (hold : run leaveInv150To20Red n (run leave150To20Red m s) = s) :
    run unleave150Top n (run leave150To20Red m s) = s := by
  let top := Shadow7.a0P 150 + lows150 - 2
  let pref := tailD0_150 ++ pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++
      tailD1_150 ++ [.pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559] ++
      tailE0_150 ++ [.make 1558 top 1559]
  have hS : leaveAfter150To20 = pref ++ (chainMid150 ++ ([.pop 1558 top 1559] ++ tailE1_150)) := hSplit
  have vRaw : DeadJoin.RawValid uB (pref ++ (chainMid150 ++ ([.pop 1558 top 1559] ++ tailE1_150))) := by
    rw [← hS]; exact ⟨vAft.physical, vAft.prepared, vAft.ready⟩
  obtain ⟨_, vCP⟩ := vRaw.parts
  obtain ⟨vChain, vPT⟩ := vCP.parts
  obtain ⟨vPop, vTail⟩ := vPT.parts
  set u0 := run (GateMirror.forward pref) [] uB with hu0
  set u1 := run (GateMirror.forward chainMid150) [] u0 with hu1
  have hu0_1557 : u0.basis 1557 = false :=
    trackList_const 1557 pref false uB (some (false, none)) h1557_uB track1557_pre150Ref
  have hu1_1558 : u1.basis 1558 = true := by
    have hpref2 : pref ++ chainMid150 =
        (tailD0_150 ++ pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++
          tailD1_150 ++ [.pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559]) ++
        (tailE0_150 ++ [.make 1558 top 1559] ++ chainMid150) := by
      simp only [pref, List.append_assoc]
    have hu1_eq : u1 = run (GateMirror.forward (pref ++ chainMid150)) [] uB := by
      rw [hu1, hu0, Partial.forward_app pref chainMid150, run_append, List.take_nil, List.drop_nil]
    rw [hu1_eq, hpref2, Partial.forward_app, run_append, List.take_nil, List.drop_nil]
    exact trackList_const 1558 _ true _ none trivial track1558_mid150
  have hcm : chainMid150 =
      chainG (Shadow7.storeW 150)
        (fun i => if i = 0 then Shadow7.a0P 150 + lows150 - 2
          else Shadow7.bankW 150 (lows150 + i - 1))
        [.cx (Shadow7.storeW 150 (1 + (Shadow7.liveW 150 - lows150))) 1557, .x 1557]
        1 (Shadow7.liveW 150 - lows150) := by
    unfold chainMid150
    rw [Nat.add_comm 1 (Shadow7.liveW 150 - lows150)]
  have hne : ∀ k, 1 ≤ k → k < 1 + (Shadow7.liveW 150 - lows150) →
      Shadow7.storeW 150 k ≠ 1557 ∧
      (if k = 0 then Shadow7.a0P 150 + lows150 - 2 else Shadow7.bankW 150 (lows150 + k - 1)) ≠ 1557 ∧
      Shadow7.storeW 150 (k + 1) ≠ 1557 := by
    intro k hk1 hk2
    have hd := List.all_eq_true.mp hne150_1557 (k - 1) (List.mem_range.mpr (by omega))
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
    rw [show 1 + (k - 1) = k by omega] at hd
    rw [if_neg (by omega)]
    exact ⟨hd.1.1, hd.1.2, hd.2⟩
  have hbackTop (t : List Bool) : run chainTopInv150 t u1 = u0 := by
    rw [hu1, hcm]
    exact chainTopInv_undo _ _ 1557 1 (Shadow7.liveW 150 - lows150)
      u0 [] t hH150_pos (hcm ▸ vChain) hu0_1557 hne
  have hbackOld (t : List Bool) : run (GateMirror.inverse chainMid150) t u1 = u0 := by
    rw [hu1]; exact vChain.undo_run [] t
  have hPostUndo (t : List Bool) : run (GateMirror.inverse post150) t (run leave150To20Red m s) = u1 := by
    have hE2 : run leave150To20Red m s =
        run (GateMirror.forward tailE1_150) [] (run (GateMirror.forward [.pop 1558 top 1559]) [] u1) := by
      rw [hEnd, hS, Partial.forward_app pref (chainMid150 ++ ([Gate.pop 1558 top 1559] ++ tailE1_150)),
        run_append, List.take_nil, List.drop_nil, ← hu0,
        Partial.forward_app chainMid150 ([Gate.pop 1558 top 1559] ++ tailE1_150),
        run_append, List.take_nil, List.drop_nil, ← hu1,
        Partial.forward_app [Gate.pop 1558 top 1559] tailE1_150,
        run_append, List.take_nil, List.drop_nil]
    have hPinv : GateMirror.inverse post150 = GateMirror.inverse tailE1_150 ++ [.CX top 1559] := by
      simp only [post150, FredCut.inv_app]; rfl
    rw [hPinv, run_append, hE2, vTail.undo_run [] _]
    rw [show ∀ l, run [Instr.CX top 1559] l = run [Instr.CX top 1559] [] from fun l => rfl]
    exact cx_pop_inv top u1 hu1_1558 (by decide) vPop.prepared.1
  have hU : leaveInv150To20Red =
      GateMirror.inverse post150 ++ GateMirror.inverse chainMid150 ++
      (GateMirror.inverse pre150 ++ CRTBarrel.barrel 150 true ++ GateMirror.inverse (CRTBarrel.before 150)) := by
    rw [leaveInv150To20Red, afterRow150_split_chain]
    simp only [FredCut.inv_app, List.append_assoc]
  have hT : unleave150Top =
      GateMirror.inverse post150 ++ chainTopInv150 ++
      (GateMirror.inverse pre150 ++ CRTBarrel.barrel 150 true ++ GateMirror.inverse (CRTBarrel.before 150)) := by
    simp only [unleave150Top, after150TopInv, List.append_assoc]
  have hmc : measurementCount chainTopInv150 = measurementCount (GateMirror.inverse chainMid150) := by
    rw [hcm]; exact (chainTopInv_counts _ _ 1557 1 _ hH150_pos).2.1
  rw [hU] at hold
  rw [hT]
  simp only [run_append, measurementCount_append] at hold ⊢
  rw [hPostUndo, hbackTop]
  rw [hPostUndo, hbackOld] at hold
  rwa [hmc]

/-! ### 6. Family 3: Wide 20-tick blocks (`j : Fin 9`) -/

def pre20 (s : Nat) : List Gate :=
  WideSelectorNormalized.tailD0 s ++ WideSelectorNormalized.tailD1 s ++
  [.cx (e0P20 s + 4) 1559] ++ tailE0_20 s ++ [.cx (a0P20 s + lowsP20 s - 2) 1559]

def post20 (s : Nat) : List Gate :=
  [.cx (a0P20 s + lowsP20 s - 2) 1559] ++ tailE1_20 s

theorem afterRow20_split_chain (s : Nat) :
    WideSelectorNormalized.afterRow s = pre20 s ++ (chainMid20 s ++ post20 s) := by
  simp only [WideSelectorNormalized.afterRow, pre20, post20, List.append_assoc]

def chainTopInv20 (s : Nat) : Program :=
  let L := lowsP20 s
  let top := a0P20 s + L - 2
  let H := liveW20 s - L
  chainTopInv (storeWire20 s) (fun i => if i = 0 then top else bankW20 s (L + i - 1)) 1557 1 H

def after20TopInv (s : Nat) : Program :=
  GateMirror.inverse (post20 s) ++ chainTopInv20 s ++ GateMirror.inverse (pre20 s)

def unleave20Top (j : Fin 9) : Program :=
  let s := start20 j
  after20TopInv s ++ barrel20 s true ++ GateMirror.inverse (WideSelectorNormalized.beforeRow s)

def unleave20CTop (j : Fin 9) : Program :=
  (unleave20Top j).take (K20 j) ++ (unleave20Top j).drop (K20 j + 6)

theorem hH20_pos : ∀ j : Fin 9, 1 ≤ liveW20 (start20 j) - lowsP20 (start20 j) := by
  decide +kernel

theorem hL20_le21 : ∀ j : Fin 9, lowsP20 (start20 j) ≤ 21 := by decide +kernel

theorem htop20_ne : ∀ j : Fin 9, a0P20 (start20 j) + lowsP20 (start20 j) - 2 ≠ 1559 := by
  decide +kernel

theorem hne20_1557 : ∀ j : Fin 9,
    let s := start20 j
    let L := lowsP20 s
    let H := liveW20 s - L
    (List.range H).all (fun d =>
      let k := 1 + d
      storeWire20 s k != 1557 &&
      bankW20 s (L + k - 1) != 1557 &&
      storeWire20 s (k + 1) != 1557) = true := by decide +kernel

theorem track1557_before20 : ∀ j : Fin 9,
    trackList 1557 none (leaveBefore20 (start20 j)) = some (false, none) := by decide +kernel

theorem track1557_pre20Ref : ∀ j : Fin 9,
    let s := start20 j
    let top := a0P20 s + lowsP20 s - 2
    trackList 1557 (some (false, none))
      (tailD0_20 s ++ pairGM false 1624 (a0P20 s - 1 + 21) (bankW20 s 21) ++
       tailD1_20 s ++ [.pop (e0P20 s + 3) (e0P20 s + 4) 1559] ++
       tailE0_20 s ++ [.make 1558 top 1559]) = some (false, none) := by decide +kernel

theorem track1558_mid20 : ∀ j : Fin 9,
    let s := start20 j
    let top := a0P20 s + lowsP20 s - 2
    trackList 1558 none (tailE0_20 s ++ [.make 1558 top 1559] ++ chainMid20 s) = some (true, none) := by
  decide +kernel

theorem barrel20_no_1557 (j : Fin 9) : (1557 : Wire) ∉ wires (barrel20 (start20 j) false) := by
  have hg := geom20_facts j
  have ha0 : a0P20 (start20 j) = start20 j + sbP20 (start20 j) + 37 := rfl
  have hb0 : b0P20 (start20 j) = 787 + sbP20 (start20 j) := rfl
  have hbt : bTopP (start20 j) ≤ 1043 := by unfold bTopP railP; split_ifs <;> omega
  intro hm
  rcases barrel20_wires j false 1557 hm with ⟨i, hi, e⟩ | ⟨r, hr, e⟩ | ht
  · rcases bank20_cases j (i := i) (by omega) with ⟨_, eb⟩ | ⟨_, _, eb, _, _⟩ | ⟨_, eb, _, _⟩ <;>
      (rw [eb] at e; unfold Wire at *; omega)
  · have hp : poolW20 (start20 j) (22 + r) = 1625 + r := by
      unfold poolW20; rw [if_pos (by omega)]; unfold Wire; omega
    rw [hp] at e; unfold Wire at *; omega
  · have tr := tagsP20_range 1557 ht
    unfold Wire at *; omega

theorem unleave20Top_metrics (j : Fin 9) :
    toffoliCount (unleave20Top j) + 1 = toffoliCount (leaveInvP20Red j) ∧
    measurementCount (unleave20Top j) = measurementCount (leaveInvP20Red j) ∧
    gateSlots (unleave20Top j) + 2 = gateSlots (leaveInvP20Red j) ∧
    wires (unleave20Top j) ⊆ wires (leaveInvP20Red j) ∧
    GatePhysical (unleave20Top j) := by
  have hphys := (leave20Red_phys j).2
  have hU : leaveInvP20Red j =
      (GateMirror.inverse (post20 (start20 j)) ++ GateMirror.inverse (chainMid20 (start20 j)) ++
        GateMirror.inverse (pre20 (start20 j))) ++
      barrel20 (start20 j) true ++ GateMirror.inverse (WideSelectorNormalized.beforeRow (start20 j)) := by
    rw [leaveInvP20Red, afterRow20_split_chain]
    simp only [FredCut.inv_app, List.append_assoc]
  have hT : unleave20Top j =
      (GateMirror.inverse (post20 (start20 j)) ++ chainTopInv20 (start20 j) ++
        GateMirror.inverse (pre20 (start20 j))) ++
      barrel20 (start20 j) true ++ GateMirror.inverse (WideSelectorNormalized.beforeRow (start20 j)) := by
    simp only [unleave20Top, after20TopInv]
  have hcm : chainMid20 (start20 j) =
      chainG (storeWire20 (start20 j))
        (fun i => if i = 0 then a0P20 (start20 j) + lowsP20 (start20 j) - 2
          else bankW20 (start20 j) (lowsP20 (start20 j) + i - 1))
        [.cx (storeWire20 (start20 j) (1 + (liveW20 (start20 j) - lowsP20 (start20 j)))) 1557, .x 1557]
        1 (liveW20 (start20 j) - lowsP20 (start20 j)) := by
    unfold chainMid20
    rw [Nat.add_comm 1 (liveW20 (start20 j) - lowsP20 (start20 j))]
  have hc : toffoliCount (chainTopInv20 (start20 j)) + 1 =
        toffoliCount (GateMirror.inverse (chainMid20 (start20 j))) ∧
      measurementCount (chainTopInv20 (start20 j)) =
        measurementCount (GateMirror.inverse (chainMid20 (start20 j))) ∧
      gateSlots (chainTopInv20 (start20 j)) + 2 = gateSlots (GateMirror.inverse (chainMid20 (start20 j))) := by
    rw [hcm]; exact chainTopInv_counts _ _ 1557 1 _ (hH20_pos j)
  have hw : wires (chainTopInv20 (start20 j)) ⊆ wires (GateMirror.inverse (chainMid20 (start20 j))) := by
    rw [hcm]; exact chainTopInv_wires_sub _ _ 1557 1 _ (hH20_pos j)
  rw [hU] at hphys
  simp only [gatePhysical_append] at hphys
  have hpc : GatePhysical (chainTopInv20 (start20 j)) := by
    have hp0 := hphys.1.1.1.2
    rw [hcm] at hp0
    exact chainTopInv_physical _ _ 1557 1 _ (hH20_pos j) hp0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, hU]; simp only [toffoliCount_append]; omega
  · rw [hT, hU]; simp only [measurementCount_append]; omega
  · rw [hT, hU]; simp only [gateSlots_append]; omega
  · rw [hT, hU]
    simp only [wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union
      (Finset.union_subset_union (Finset.Subset.refl _) hw) (Finset.Subset.refl _)) (Finset.Subset.refl _))
      (Finset.Subset.refl _)
  · rw [hT]
    simp only [gatePhysical_append]
    exact ⟨⟨⟨⟨hphys.1.1.1.1, hpc⟩, hphys.1.1.2⟩, hphys.1.2⟩, hphys.2⟩

theorem unleave20Top_undo (j : Fin 9) (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : Inputs20 j s z g0 s0) (m n : List Bool) :
    run (unleave20Top j) n (run (leaveP20Red j) m s) = s := by
  have hpair := leaveP20Red_pair j s z g0 s0 h
  have hold := hpair.2 m n
  obtain ⟨hbf_ready, _, hbf_prep⟩ := leaveBefore20_valid j s z g0 s0 h
  have vBef : CRTBarrel.LeaveSplice.Valid s (leaveBefore20 (start20 j)) := ⟨(leaveBefore20_ok j).1, hbf_prep, hbf_ready⟩
  let uB := run (GateMirror.forward (leaveBefore20 (start20 j))) [] s
  have hbar := barrel20_mid_rt j s [] z g0 s0 h
  simp only [List.drop_nil] at hbar
  have hbar_def (t : List Bool) : run (barrel20 (start20 j) false) t uB = run (barrel20 (start20 j) false) [] uB :=
    state_eq_of_phase_basis ((hbar t).2.trans (hbar []).2.symm) (run_basis_any20 _ t [] uB uB rfl)
  let uA := run (barrel20 (start20 j) false) [] uB
  obtain ⟨haf_prep, haf_ready⟩ := leaveAfter20_valid j s [] z g0 s0 h
  simp only [List.drop_nil] at haf_prep haf_ready
  have vAft : CRTBarrel.LeaveSplice.Valid uA (leaveAfter20 (start20 j)) := ⟨(leaveAfter20_ok j).1, haf_prep, haf_ready⟩
  have hEnd : run (leaveP20Red j) m s = run (GateMirror.forward (leaveAfter20 (start20 j))) [] uA := by
    rw [hpair.1 m]
    unfold leaveP20; simp only [run_append, run_take]
    rw [vBef.default_run, hbar_def, vAft.default_run]
  let pref := tailD0_20 (start20 j) ++ pairGM false 1624 (a0P20 (start20 j) - 1 + 21) (bankW20 (start20 j) 21) ++
      tailD1_20 (start20 j) ++ [.pop (e0P20 (start20 j) + 3) (e0P20 (start20 j) + 4) 1559] ++
      tailE0_20 (start20 j) ++ [.make 1558 (a0P20 (start20 j) + lowsP20 (start20 j) - 2) 1559]
  have hSplit : leaveAfter20 (start20 j) = pref ++ (chainMid20 (start20 j) ++ ([.pop 1558 (a0P20 (start20 j) + lowsP20 (start20 j) - 2) 1559] ++ tailE1_20 (start20 j))) := by
    rw [leaveAfter20_split4_red (start20 j) (hL20_le21 j)]
    simp only [pref, List.append_assoc]
  have vRaw : DeadJoin.RawValid uA (pref ++ (chainMid20 (start20 j) ++ ([.pop 1558 (a0P20 (start20 j) + lowsP20 (start20 j) - 2) 1559] ++ tailE1_20 (start20 j)))) := by
    rw [← hSplit]; exact ⟨vAft.physical, vAft.prepared, vAft.ready⟩
  obtain ⟨_, vCP⟩ := vRaw.parts
  obtain ⟨vChain, vPT⟩ := vCP.parts
  obtain ⟨vPop, vTail⟩ := vPT.parts
  set u0 := run (GateMirror.forward pref) [] uA with hu0
  set u1 := run (GateMirror.forward (chainMid20 (start20 j))) [] u0 with hu1
  have huB_1557 : uB.basis 1557 = false := by
    simp only [uB]
    exact trackList_const 1557 (leaveBefore20 (start20 j)) false s none trivial (track1557_before20 j)
  have huA_1557 : uA.basis 1557 = false := by
    simp only [uA]
    rw [run_preserves_outside (barrel20 (start20 j) false) [] uB 1557 (barrel20_no_1557 j)]
    exact huB_1557
  have hu0_1557 : u0.basis 1557 = false := by
    rw [hu0]
    exact trackList_const 1557 pref false uA (some (false, none)) huA_1557
      (by simp only [pref]; exact track1557_pre20Ref j)
  have hu1_1558 : u1.basis 1558 = true := by
    have hpref2 : pref ++ chainMid20 (start20 j) =
        (tailD0_20 (start20 j) ++ pairGM false 1624 (a0P20 (start20 j) - 1 + 21) (bankW20 (start20 j) 21) ++
          tailD1_20 (start20 j) ++ [.pop (e0P20 (start20 j) + 3) (e0P20 (start20 j) + 4) 1559]) ++
        (tailE0_20 (start20 j) ++ [.make 1558 (a0P20 (start20 j) + lowsP20 (start20 j) - 2) 1559] ++ chainMid20 (start20 j)) := by
      simp only [pref, List.append_assoc]
    have hu1_eq : u1 = run (GateMirror.forward (pref ++ chainMid20 (start20 j))) [] uA := by
      rw [hu1, hu0, Partial.forward_app pref (chainMid20 (start20 j)), run_append, List.take_nil, List.drop_nil]
    rw [hu1_eq, hpref2, Partial.forward_app, run_append, List.take_nil, List.drop_nil]
    exact trackList_const 1558 _ true _ none trivial (track1558_mid20 j)
  have hcm : chainMid20 (start20 j) =
      chainG (storeWire20 (start20 j))
        (fun i => if i = 0 then a0P20 (start20 j) + lowsP20 (start20 j) - 2 else bankW20 (start20 j) (lowsP20 (start20 j) + i - 1))
        [.cx (storeWire20 (start20 j) (1 + (liveW20 (start20 j) - lowsP20 (start20 j)))) 1557, .x 1557]
        1 (liveW20 (start20 j) - lowsP20 (start20 j)) := by
    unfold chainMid20
    rw [Nat.add_comm 1 (liveW20 (start20 j) - lowsP20 (start20 j))]
  have hne : ∀ k, 1 ≤ k → k < 1 + (liveW20 (start20 j) - lowsP20 (start20 j)) →
      storeWire20 (start20 j) k ≠ 1557 ∧
      (if k = 0 then a0P20 (start20 j) + lowsP20 (start20 j) - 2 else bankW20 (start20 j) (lowsP20 (start20 j) + k - 1)) ≠ 1557 ∧
      storeWire20 (start20 j) (k + 1) ≠ 1557 := by
    intro k hk1 hk2
    have hd := List.all_eq_true.mp (hne20_1557 j) (k - 1) (List.mem_range.mpr (by omega))
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
    rw [show 1 + (k - 1) = k by omega] at hd
    rw [if_neg (by omega)]
    exact ⟨hd.1.1, hd.1.2, hd.2⟩
  have hbackTop (t : List Bool) : run (chainTopInv20 (start20 j)) t u1 = u0 := by
    rw [hu1, hcm]
    exact chainTopInv_undo _ _ 1557 1 (liveW20 (start20 j) - lowsP20 (start20 j))
      u0 [] t (hH20_pos j) (hcm ▸ vChain) hu0_1557 hne
  have hbackOld (t : List Bool) : run (GateMirror.inverse (chainMid20 (start20 j))) t u1 = u0 := by
    rw [hu1]; exact vChain.undo_run [] t
  have hPostUndo (t : List Bool) : run (GateMirror.inverse (post20 (start20 j))) t (run (leaveP20Red j) m s) = u1 := by
    have hE2 : run (leaveP20Red j) m s =
        run (GateMirror.forward (tailE1_20 (start20 j))) [] (run (GateMirror.forward [.pop 1558 (a0P20 (start20 j) + lowsP20 (start20 j) - 2) 1559]) [] u1) := by
      rw [hEnd, hSplit, Partial.forward_app pref (chainMid20 (start20 j) ++ ([Gate.pop 1558 (a0P20 (start20 j) + lowsP20 (start20 j) - 2) 1559] ++ tailE1_20 (start20 j))),
        run_append, List.take_nil, List.drop_nil, ← hu0,
        Partial.forward_app (chainMid20 (start20 j)) ([Gate.pop 1558 (a0P20 (start20 j) + lowsP20 (start20 j) - 2) 1559] ++ tailE1_20 (start20 j)),
        run_append, List.take_nil, List.drop_nil, ← hu1,
        Partial.forward_app [Gate.pop 1558 (a0P20 (start20 j) + lowsP20 (start20 j) - 2) 1559] (tailE1_20 (start20 j)),
        run_append, List.take_nil, List.drop_nil]
    have hPinv : GateMirror.inverse (post20 (start20 j)) = GateMirror.inverse (tailE1_20 (start20 j)) ++ [.CX (a0P20 (start20 j) + lowsP20 (start20 j) - 2) 1559] := by
      simp only [post20, FredCut.inv_app]; rfl
    rw [hPinv, run_append, hE2, vTail.undo_run [] _]
    rw [show ∀ l, run [Instr.CX (a0P20 (start20 j) + lowsP20 (start20 j) - 2) 1559] l = run [Instr.CX (a0P20 (start20 j) + lowsP20 (start20 j) - 2) 1559] [] from fun l => rfl]
    exact cx_pop_inv (a0P20 (start20 j) + lowsP20 (start20 j) - 2) u1 hu1_1558 (htop20_ne j) vPop.prepared.1
  have hU : leaveInvP20Red j =
      GateMirror.inverse (post20 (start20 j)) ++ GateMirror.inverse (chainMid20 (start20 j)) ++
      (GateMirror.inverse (pre20 (start20 j)) ++ barrel20 (start20 j) true ++ GateMirror.inverse (WideSelectorNormalized.beforeRow (start20 j))) := by
    rw [leaveInvP20Red, afterRow20_split_chain]
    simp only [FredCut.inv_app, List.append_assoc]
  have hT : unleave20Top j =
      GateMirror.inverse (post20 (start20 j)) ++ chainTopInv20 (start20 j) ++
      (GateMirror.inverse (pre20 (start20 j)) ++ barrel20 (start20 j) true ++ GateMirror.inverse (WideSelectorNormalized.beforeRow (start20 j))) := by
    simp only [unleave20Top, after20TopInv, List.append_assoc]
  have hmc : measurementCount (chainTopInv20 (start20 j)) = measurementCount (GateMirror.inverse (chainMid20 (start20 j))) := by
    rw [hcm]; exact (chainTopInv_counts _ _ 1557 1 _ (hH20_pos j)).2.1
  rw [hU] at hold
  rw [hT]
  simp only [run_append, measurementCount_append] at hold ⊢
  rw [hPostUndo, hbackTop]
  rw [hPostUndo, hbackOld] at hold
  rwa [hmc]

/-! ### 7. FredCut transport for the 22 top-cut reverse leaves -/

theorem cut_inv_eq (L M D R : Program) (hD : D.length = 6) (hL : L = M ++ (D ++ R)) :
    L.take M.length ++ L.drop (M.length + 6) = M ++ R := by
  rw [hL, List.take_left' rfl, show M.length + 6 = (M ++ D).length by simp [hD],
    ← List.append_assoc, List.drop_left' rfl]

theorem hlen_D15 (s : Nat) : (Dblk15 s).length = 6 := rfl
theorem hlen_D150 : Dblk150.length = 6 := rfl
theorem hlen_D20 (s : Nat) : (Dblk20 s).length = 6 := rfl

theorem hK15 (j : Fin 26) : (GateMirror.inverse (Shadow7.leaveClose (start j))).length = K15 j := by
  simp only [K15, GateMirror.inverse, GateMirror.forward, List.length_reverse, List.length_map]

theorem hK150 : (GateMirror.inverse leaveClose150To20).length = K150 := by
  simp only [K150, GateMirror.inverse, GateMirror.forward, List.length_reverse, List.length_map]

theorem hK20 (j : Fin 9) : (GateMirror.inverse (leaveClose20 (start20 j))).length = K20 j := by
  simp only [K20, GateMirror.inverse, GateMirror.forward, List.length_reverse, List.length_map]

theorem lowClose15_split (s : Nat) (hL : 2 ≤ Shadow7.lowsP s) :
    ∃ V, Shadow7.leaveLowClose s = V ++
      (cswapG (s + 30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 2)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 2)) ++
       cswapG (s + 30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1))) := by
  have hr : List.range (Shadow7.lowsP s) =
      List.range (Shadow7.lowsP s - 2) ++ [Shadow7.lowsP s - 2, Shadow7.lowsP s - 1] := by
    have e := FredCut.range_split2 (Shadow7.lowsP s - 2)
    rwa [show Shadow7.lowsP s - 2 + 2 = Shadow7.lowsP s by omega,
         show Shadow7.lowsP s - 2 + 1 = Shadow7.lowsP s - 1 by omega] at e
  refine ⟨xsG ((List.range 15).map (s + 16 + ·)) ++
      (List.range (Shadow7.lowsP s)).map (fun i => Gate.cx (Shadow7.e0P s + 5) (Shadow7.b0P s - 1 + i)) ++
      (List.range (Shadow7.lowsP s - 2)).flatMap
        (fun i => cswapG (s + 30) (Shadow7.b0P s - 1 + i) (Shadow7.a0P s - 1 + i)), ?_⟩
  unfold Shadow7.leaveLowClose; simp only []
  rw [hr, List.flatMap_append]; simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem post7S_suffix (s : Nat) :
    ∃ Z, post7S s = Z ++ (Shadow7.leaveLowClose s ++ Shadow7.leaveClose s) := by
  refine ⟨[.cx (DeadJoin.topW7 s) 1559] ++
    (let L := Shadow7.lowsP s; let top := Shadow7.a0P s + L - 2; let H := Shadow7.liveW s - L
     let hi := (List.range H).map (fun i => Shadow7.bankW s (L + i))
     let seq2 := (List.range (L - 1)).map (Shadow7.b0P s - 1 + ·)
     xsG hi.reverse ++ [.x top, .x 1558, .make 1556 1557 1558, .x 1558] ++ xsG seq2 ++
       chainG (1558 + ·) (Shadow7.b0P s - 1 + ·) [.cx (1558 + (L - 1)) 1556, .x 1556] 0 (L - 1) ++
       xsG seq2.reverse ++ [.x 1558]), ?_⟩
  simp only [post7S, DeadJoin.afterPost7, List.append_assoc]

theorem unleave15Top_shape (k : Fin 26) (hk : k.val ≤ 24) (hL : 2 ≤ Shadow7.lowsP (start k)) :
    ∃ R, unleave15Top k = GateMirror.inverse (Shadow7.leaveClose (start k)) ++ (Dblk15 (start k) ++ R) := by
  obtain ⟨Z, hZ⟩ := post7S_suffix (start k)
  obtain ⟨V, hV⟩ := lowClose15_split (start k) hL
  let s := start k
  refine ⟨GateMirror.inverse V ++ GateMirror.inverse Z ++ chainTopInv7 s ++
    GateMirror.inverse (pre7S s) ++ CRTBarrel.barrel s true ++ GateMirror.inverse (CRTBarrel.before s), ?_⟩
  simp only [unleave15Top, hk, ↓reduceIte, after7STopInv]
  dsimp only [s] at hZ hV ⊢
  rw [hZ, hV]
  simp only [Dblk15, FredCut.inv_app, List.append_assoc]

theorem unleave15CTop_eq (k : Fin 26) (hk : k.val ≤ 24) (R : Program)
    (hR : unleave15Top k = GateMirror.inverse (Shadow7.leaveClose (start k)) ++ (Dblk15 (start k) ++ R)) :
    unleave15CTop k = GateMirror.inverse (Shadow7.leaveClose (start k)) ++ R := by
  simp only [unleave15CTop, hk, ↓reduceIte]; rw [← hK15 k]; exact cut_inv_eq _ _ _ R (hlen_D15 _) hR

theorem lowClose150_split :
    ∃ V, leaveLowClose150 = V ++
      (cswapG (150 + 30) (Shadow7.b0P 150 - 1 + 10) (Shadow7.a0P 150 - 1 + 10) ++
       cswapG (150 + 30) (Shadow7.b0P 150 - 1 + 11) (Shadow7.a0P 150 - 1 + 11)) := by
  have hr : List.range lows150 = List.range 10 ++ [10, 11] := by decide
  refine ⟨xsG ((List.range 15).map (150 + 16 + ·)) ++
      (List.range lows150).map (fun i => Gate.cx (Shadow7.e0P 150 + 5) (Shadow7.b0P 150 - 1 + i)) ++
      (List.range 10).flatMap
        (fun i => cswapG (150 + 30) (Shadow7.b0P 150 - 1 + i) (Shadow7.a0P 150 - 1 + i)), ?_⟩
  unfold leaveLowClose150; simp only []
  rw [hr, List.flatMap_append]; simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem post150_suffix :
    ∃ Z, post150 = Z ++ (leaveLowClose150 ++ leaveClose150To20) := by
  refine ⟨[.cx (Shadow7.a0P 150 + lows150 - 2) 1559] ++
    (let L := lows150; let top := Shadow7.a0P 150 + L - 2; let H := Shadow7.liveW 150 - L
     let hi := (List.range H).map fun i => Shadow7.bankW 150 (L + i)
     let seq2 := (List.range (L - 1)).map (Shadow7.b0P 150 - 1 + ·)
     xsG hi.reverse ++ [.x top, .x 1558, .make 1556 1557 1558, .x 1558] ++ xsG seq2 ++
       chainG (1558 + ·) (Shadow7.b0P 150 - 1 + ·) [.cx (1558 + (L - 1)) 1556, .x 1556] 0 (L - 1) ++
       xsG seq2.reverse ++ [.x 1558]), ?_⟩
  simp only [post150, tailE1_150, List.append_assoc]

theorem unleave150Top_shape :
    ∃ R, unleave150Top = GateMirror.inverse leaveClose150To20 ++ (Dblk150 ++ R) := by
  obtain ⟨Z, hZ⟩ := post150_suffix
  obtain ⟨V, hV⟩ := lowClose150_split
  refine ⟨GateMirror.inverse V ++ GateMirror.inverse Z ++ chainTopInv150 ++
    GateMirror.inverse pre150 ++ CRTBarrel.barrel 150 true ++ GateMirror.inverse (CRTBarrel.before 150), ?_⟩
  simp only [unleave150Top, after150TopInv]
  rw [hZ, hV]
  simp only [Dblk150, FredCut.inv_app, List.append_assoc]

theorem unleave150CTop_eq (R : Program)
    (hR : unleave150Top = GateMirror.inverse leaveClose150To20 ++ (Dblk150 ++ R)) :
    unleave150CTop = GateMirror.inverse leaveClose150To20 ++ R := by
  unfold unleave150CTop; rw [← hK150]; exact cut_inv_eq _ _ _ R hlen_D150 hR

theorem lowClose20_split (s : Nat) (hL : 2 ≤ lowsP20 s) :
    ∃ V, leaveLowClose20 s = V ++
      (cswapG (s + 35) (b0P20 s - 1 + (lowsP20 s - 2)) (a0P20 s - 1 + (lowsP20 s - 2)) ++
       cswapG (s + 35) (b0P20 s - 1 + (lowsP20 s - 1)) (a0P20 s - 1 + (lowsP20 s - 1))) := by
  have hr : List.range (lowsP20 s) =
      List.range (lowsP20 s - 2) ++ [lowsP20 s - 2, lowsP20 s - 1] := by
    have e := FredCut.range_split2 (lowsP20 s - 2)
    rwa [show lowsP20 s - 2 + 2 = lowsP20 s by omega, show lowsP20 s - 2 + 1 = lowsP20 s - 1 by omega] at e
  refine ⟨xsG ((List.range 20).map (s + 16 + ·)) ++
      (List.range (lowsP20 s)).map (fun i => Gate.cx (e0P20 s + 5) (b0P20 s - 1 + i)) ++
      (List.range (lowsP20 s - 2)).flatMap
        (fun i => cswapG (s + 35) (b0P20 s - 1 + i) (a0P20 s - 1 + i)), ?_⟩
  unfold leaveLowClose20; simp only []
  rw [hr, List.flatMap_append]; simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem post20_suffix (s : Nat) :
    ∃ Z, post20 s = Z ++ (leaveLowClose20 s ++ leaveClose20 s) := by
  refine ⟨[.cx (a0P20 s + lowsP20 s - 2) 1559] ++
    (let L := lowsP20 s; let top := a0P20 s + L - 2; let H := liveW20 s - L
     let hi := (List.range H).map fun i => bankW20 s (L + i)
     let seq2 := (List.range (L - 1)).map (b0P20 s - 1 + ·)
     xsG hi.reverse ++ [.x top, .x 1558, .make 1556 1557 1558, .x 1558] ++ xsG seq2 ++
       chainG (1558 + ·) (b0P20 s - 1 + ·) [.cx (1558 + (L - 1)) 1556, .x 1556] 0 (L - 1) ++
       xsG seq2.reverse ++ [.x 1558]), ?_⟩
  simp only [post20, tailE1_20, List.append_assoc]

theorem unleave20Top_shape (k : Fin 9) (hL : 2 ≤ lowsP20 (start20 k)) :
    ∃ R, unleave20Top k = GateMirror.inverse (leaveClose20 (start20 k)) ++ (Dblk20 (start20 k) ++ R) := by
  obtain ⟨Z, hZ⟩ := post20_suffix (start20 k)
  obtain ⟨V, hV⟩ := lowClose20_split (start20 k) hL
  let s := start20 k
  refine ⟨GateMirror.inverse V ++ GateMirror.inverse Z ++ chainTopInv20 s ++
    GateMirror.inverse (pre20 s) ++ barrel20 s true ++ GateMirror.inverse (WideSelectorNormalized.beforeRow s), ?_⟩
  simp only [unleave20Top, after20TopInv]
  dsimp only [s] at hZ hV ⊢
  rw [hZ, hV]
  simp only [Dblk20, FredCut.inv_app, List.append_assoc]

theorem unleave20CTop_eq (k : Fin 9) (R : Program)
    (hR : unleave20Top k = GateMirror.inverse (leaveClose20 (start20 k)) ++ (Dblk20 (start20 k) ++ R)) :
    unleave20CTop k = GateMirror.inverse (leaveClose20 (start20 k)) ++ R := by
  unfold unleave20CTop; rw [← hK20 k]; exact cut_inv_eq _ _ _ R (hlen_D20 _) hR

/-! ### 8. Cut metrics for `unleave15CTop`, `unleave150CTop`, `unleave20CTop` -/

theorem unleave15CTop_rel (j : Fin 26) (hi : j.val ≤ 24) (hL : 2 ≤ Shadow7.lowsP (start j)) :
    toffoliCount (unleave15CTop j) + 1 = toffoliCount (unleave15C j) ∧
    measurementCount (unleave15CTop j) = measurementCount (unleave15C j) ∧
    gateSlots (unleave15CTop j) + 2 = gateSlots (unleave15C j) ∧
    wires (unleave15CTop j) ⊆ wires (unleave15C j) ∧
    GatePhysical (unleave15CTop j) := by
  have hm := unleave15Top_metrics j hi
  obtain ⟨Z, hZ⟩ := post7S_suffix (start j)
  obtain ⟨V, hV⟩ := lowClose15_split (start j) hL
  let s := start j
  let M := GateMirror.inverse (Shadow7.leaveClose s)
  let D := Dblk15 s
  let A := GateMirror.inverse V ++ GateMirror.inverse Z
  let B := GateMirror.inverse (pre7S s) ++ CRTBarrel.barrel s true ++ GateMirror.inverse (CRTBarrel.before s)
  have hT_full : unleave15Top j = M ++ (D ++ (A ++ chainTopInv7 s ++ B)) := by
    simp only [unleave15Top, hi, ↓reduceIte, after7STopInv, M, D, A, B, s]
    rw [hZ, hV]; simp only [Dblk15, FredCut.inv_app, List.append_assoc]
  have hO_full : CRTBarrel.unleave j = M ++ (D ++ (A ++ GateMirror.inverse (DeadJoin.chainMid7 s) ++ B)) := by
    rw [CRTBarrel.unleave, if_pos hi, CRTBarrel.afterPart, after7S_split_chain]
    simp only [M, D, A, B, s]; rw [hZ, hV]; simp only [Dblk15, FredCut.inv_app, List.append_assoc]
  have hTC : unleave15CTop j = M ++ (A ++ chainTopInv7 s ++ B) := unleave15CTop_eq j hi _ hT_full
  have hOC : unleave15C j = M ++ (A ++ GateMirror.inverse (DeadJoin.chainMid7 s) ++ B) := by
    simp only [unleave15C, hi, ↓reduceIte]; rw [← hK15 j]; exact cut_inv_eq _ _ _ _ (hlen_D15 _) hO_full
  have hcm : DeadJoin.chainMid7 s =
      chainG (Shadow7.storeW s)
        (fun i => if i = 0 then Shadow7.a0P s + Shadow7.lowsP s - 2 else Shadow7.bankW s (Shadow7.lowsP s + i - 1))
        [.cx (Shadow7.storeW s (1 + (Shadow7.liveW s - Shadow7.lowsP s))) 1557, .x 1557]
        1 (Shadow7.liveW s - Shadow7.lowsP s) := by
    unfold DeadJoin.chainMid7; rw [Nat.add_comm 1 (Shadow7.liveW s - Shadow7.lowsP s)]
  have hc : toffoliCount (chainTopInv7 s) + 1 = toffoliCount (GateMirror.inverse (DeadJoin.chainMid7 s)) ∧
      measurementCount (chainTopInv7 s) = measurementCount (GateMirror.inverse (DeadJoin.chainMid7 s)) ∧
      gateSlots (chainTopInv7 s) + 2 = gateSlots (GateMirror.inverse (DeadJoin.chainMid7 s)) := by
    rw [hcm]; exact chainTopInv_counts _ _ 1557 1 _ (hH7_pos j hi)
  have hw : wires (chainTopInv7 s) ⊆ wires (GateMirror.inverse (DeadJoin.chainMid7 s)) := by
    rw [hcm]; exact chainTopInv_wires_sub _ _ 1557 1 _ (hH7_pos j hi)
  have hp := hm.2.2.2.2
  rw [hT_full, gatePhysical_append, gatePhysical_append] at hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hTC, hOC]; simp only [toffoliCount_append]; omega
  · rw [hTC, hOC]; simp only [measurementCount_append]; omega
  · rw [hTC, hOC]; simp only [gateSlots_append]; omega
  · rw [hTC, hOC]
    simp only [wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) hw) (Finset.Subset.refl _))
  · rw [hTC, gatePhysical_append]; exact ⟨hp.1, hp.2.2⟩

theorem unleave150CTop_rel :
    toffoliCount unleave150CTop + 1 = toffoliCount unleave150C ∧
    measurementCount unleave150CTop = measurementCount unleave150C ∧
    gateSlots unleave150CTop + 2 = gateSlots unleave150C ∧
    wires unleave150CTop ⊆ wires unleave150C ∧
    GatePhysical unleave150CTop := by
  have hm := unleave150Top_metrics
  obtain ⟨Z, hZ⟩ := post150_suffix
  obtain ⟨V, hV⟩ := lowClose150_split
  let M := GateMirror.inverse leaveClose150To20
  let D := Dblk150
  let A := GateMirror.inverse V ++ GateMirror.inverse Z
  let B := GateMirror.inverse pre150 ++ CRTBarrel.barrel 150 true ++ GateMirror.inverse (CRTBarrel.before 150)
  have hT_full : unleave150Top = M ++ (D ++ (A ++ chainTopInv150 ++ B)) := by
    simp only [unleave150Top, after150TopInv, M, D, A, B]
    rw [hZ, hV]; simp only [Dblk150, FredCut.inv_app, List.append_assoc]
  have hO_full : leaveInv150To20Red = M ++ (D ++ (A ++ GateMirror.inverse chainMid150 ++ B)) := by
    rw [leaveInv150To20Red, afterRow150_split_chain]
    simp only [M, D, A, B]; rw [hZ, hV]; simp only [Dblk150, FredCut.inv_app, List.append_assoc]
  have hTC : unleave150CTop = M ++ (A ++ chainTopInv150 ++ B) := unleave150CTop_eq _ hT_full
  have hOC : unleave150C = M ++ (A ++ GateMirror.inverse chainMid150 ++ B) := by
    unfold unleave150C; rw [← hK150]; exact cut_inv_eq _ _ _ _ hlen_D150 hO_full
  have hcm : chainMid150 =
      chainG (Shadow7.storeW 150)
        (fun i => if i = 0 then Shadow7.a0P 150 + lows150 - 2 else Shadow7.bankW 150 (lows150 + i - 1))
        [.cx (Shadow7.storeW 150 (1 + (Shadow7.liveW 150 - lows150))) 1557, .x 1557]
        1 (Shadow7.liveW 150 - lows150) := by
    unfold chainMid150; rw [Nat.add_comm 1 (Shadow7.liveW 150 - lows150)]
  have hc : toffoliCount chainTopInv150 + 1 = toffoliCount (GateMirror.inverse chainMid150) ∧
      measurementCount chainTopInv150 = measurementCount (GateMirror.inverse chainMid150) ∧
      gateSlots chainTopInv150 + 2 = gateSlots (GateMirror.inverse chainMid150) := by
    rw [hcm]; exact chainTopInv_counts _ _ 1557 1 _ hH150_pos
  have hw : wires chainTopInv150 ⊆ wires (GateMirror.inverse chainMid150) := by
    rw [hcm]; exact chainTopInv_wires_sub _ _ 1557 1 _ hH150_pos
  have hp := hm.2.2.2.2
  rw [hT_full, gatePhysical_append, gatePhysical_append] at hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hTC, hOC]; simp only [toffoliCount_append]; omega
  · rw [hTC, hOC]; simp only [measurementCount_append]; omega
  · rw [hTC, hOC]; simp only [gateSlots_append]; omega
  · rw [hTC, hOC]
    simp only [wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) hw) (Finset.Subset.refl _))
  · rw [hTC, gatePhysical_append]; exact ⟨hp.1, hp.2.2⟩

theorem unleave20CTop_rel (j : Fin 9) (hL : 2 ≤ lowsP20 (start20 j)) :
    toffoliCount (unleave20CTop j) + 1 = toffoliCount (unleave20C j) ∧
    measurementCount (unleave20CTop j) = measurementCount (unleave20C j) ∧
    gateSlots (unleave20CTop j) + 2 = gateSlots (unleave20C j) ∧
    wires (unleave20CTop j) ⊆ wires (unleave20C j) ∧
    GatePhysical (unleave20CTop j) := by
  have hm := unleave20Top_metrics j
  obtain ⟨Z, hZ⟩ := post20_suffix (start20 j)
  obtain ⟨V, hV⟩ := lowClose20_split (start20 j) hL
  let s := start20 j
  let M := GateMirror.inverse (leaveClose20 s)
  let D := Dblk20 s
  let A := GateMirror.inverse V ++ GateMirror.inverse Z
  let B := GateMirror.inverse (pre20 s) ++ barrel20 s true ++ GateMirror.inverse (WideSelectorNormalized.beforeRow s)
  have hT_full : unleave20Top j = M ++ (D ++ (A ++ chainTopInv20 s ++ B)) := by
    simp only [unleave20Top, after20TopInv, M, D, A, B, s]
    rw [hZ, hV]; simp only [Dblk20, FredCut.inv_app, List.append_assoc]
  have hO_full : leaveInvP20Red j = M ++ (D ++ (A ++ GateMirror.inverse (chainMid20 s) ++ B)) := by
    rw [leaveInvP20Red, afterRow20_split_chain]
    simp only [M, D, A, B, s]; rw [hZ, hV]; simp only [Dblk20, FredCut.inv_app, List.append_assoc]
  have hTC : unleave20CTop j = M ++ (A ++ chainTopInv20 s ++ B) := unleave20CTop_eq j _ hT_full
  have hOC : unleave20C j = M ++ (A ++ GateMirror.inverse (chainMid20 s) ++ B) := by
    unfold unleave20C; rw [← hK20 j]; exact cut_inv_eq _ _ _ _ (hlen_D20 _) hO_full
  have hcm : chainMid20 s =
      chainG (storeWire20 s)
        (fun i => if i = 0 then a0P20 s + lowsP20 s - 2 else bankW20 s (lowsP20 s + i - 1))
        [.cx (storeWire20 s (1 + (liveW20 s - lowsP20 s))) 1557, .x 1557]
        1 (liveW20 s - lowsP20 s) := by
    unfold chainMid20; rw [Nat.add_comm 1 (liveW20 s - lowsP20 s)]
  have hc : toffoliCount (chainTopInv20 s) + 1 = toffoliCount (GateMirror.inverse (chainMid20 s)) ∧
      measurementCount (chainTopInv20 s) = measurementCount (GateMirror.inverse (chainMid20 s)) ∧
      gateSlots (chainTopInv20 s) + 2 = gateSlots (GateMirror.inverse (chainMid20 s)) := by
    rw [hcm]; exact chainTopInv_counts _ _ 1557 1 _ (hH20_pos j)
  have hw : wires (chainTopInv20 s) ⊆ wires (GateMirror.inverse (chainMid20 s)) := by
    rw [hcm]; exact chainTopInv_wires_sub _ _ 1557 1 _ (hH20_pos j)
  have hp := hm.2.2.2.2
  rw [hT_full, gatePhysical_append, gatePhysical_append] at hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hTC, hOC]; simp only [toffoliCount_append]; omega
  · rw [hTC, hOC]; simp only [measurementCount_append]; omega
  · rw [hTC, hOC]; simp only [gateSlots_append]; omega
  · rw [hTC, hOC]
    simp only [wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) hw) (Finset.Subset.refl _))
  · rw [hTC, gatePhysical_append]; exact ⟨hp.1, hp.2.2⟩

/-! ### 9. Full reverse window lists (`reverseL_top`, `reverseLC_top`) and FredCut transport -/

def block15R_top (d : Bool) (i j : Fin 26) : List Program :=
  [unleave15Top j, TickCut.Hosted.unroutedHigh j 1 14, Shadow7.archiveRestoreP i d,
   MixedWindow.unpackW d (start j) (start j - 10), Shadow7.unrouted j 0 1, Shadow7.enterInvP j]

def block15RC_top (d : Bool) (i j : Fin 26) : List Program :=
  [unleave15CTop j, TickCut.Hosted.unroutedHigh j 1 14, Shadow7.archiveRestoreP i d,
   MixedWindow.unpackW d (start j) (start j - 10), Shadow7.unrouted j 0 1, enterInv15C j]

def block20R_top (d : Bool) (j : Fin 9) : List Program :=
  let s := start20 j
  if j.val = 0 then
    [unleave20Top j, TickCut.Wide.unroutedHigh j 1 19, archiveRestore150To20 d,
     MixedWindow.unpackW d 165 155, unrouted20 j 0 1, enterInvP20 j]
  else
    [unleave20Top j, TickCut.Wide.unroutedHigh j 1 19, archiveRestoreP20 ⟨j.val - 1, by omega⟩ d,
     MixedWindow.unpackW d s (s - 10), MixedWindow.unpackW d s (s - 15), unrouted20 j 0 1, enterInvP20 j]

def block20RC_top (d : Bool) (j : Fin 9) : List Program :=
  let s := start20 j
  if j.val = 0 then
    [unleave20CTop j, TickCut.Wide.unroutedHigh j 1 19, archiveRestore150To20 d,
     MixedWindow.unpackW d 165 155, unrouted20 j 0 1, enterInv20C j]
  else
    [unleave20CTop j, TickCut.Wide.unroutedHigh j 1 19, archiveRestoreP20 ⟨j.val - 1, by omega⟩ d,
     MixedWindow.unpackW d s (s - 10), MixedWindow.unpackW d s (s - 15), unrouted20 j 0 1, enterInv20C j]

def reverseL_top (d : Bool) : List Program :=
  [Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410, MixedWindow.recvW 420,
   Shadow7.portalP 420, Shadow7.parkInvP 420] ++
  (MixedWindow.suffixPairs.reverse.flatMap fun p => block15R_top d p.1 p.2) ++
  [unleave15Top MixedWindow.j20, TickCut.Hosted.unroutedHigh MixedWindow.j20 1 14,
   archiveRestoreP20 MixedWindow.k8 d, MixedWindow.unpackW d 345 335, MixedWindow.unpackW d 345 330,
   Shadow7.unrouted MixedWindow.j20 0 1, Shadow7.enterInvP MixedWindow.j20] ++
  ((List.finRange 9).reverse.flatMap (block20R_top d)) ++
  [unleave150Top, TickCut.Hosted.unroutedHigh MixedWindow.j7 1 14,
   Shadow7.archiveRestoreP MixedWindow.j6 d, MixedWindow.unpackW d 150 140,
   Shadow7.unrouted MixedWindow.j7 0 1, Shadow7.enterInvP MixedWindow.j7] ++
  (MixedWindow.prefixPairs.reverse.flatMap fun p => block15R_top d p.1 p.2) ++
  [unleave15Top MixedWindow.j0, TickCut.Hosted.unroutedHigh MixedWindow.j0 1 14,
   MixedWindow.unpackW d 45 45, Shadow7.unrouted MixedWindow.j0 0 1,
   Shadow7.enterInvP MixedWindow.j0, Shadow7.portalInvP 45]

def reverseLC_top (d : Bool) : List Program :=
  [Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410, MixedWindow.recvW 420,
   portalC 420, Shadow7.parkInvP 420] ++
  (MixedWindow.suffixPairs.reverse.flatMap fun p => block15RC_top d p.1 p.2) ++
  [unleave15CTop MixedWindow.j20, TickCut.Hosted.unroutedHigh MixedWindow.j20 1 14,
   archiveRestoreP20 MixedWindow.k8 d, MixedWindow.unpackW d 345 335, MixedWindow.unpackW d 345 330,
   Shadow7.unrouted MixedWindow.j20 0 1, enterInv15C MixedWindow.j20] ++
  ((List.finRange 9).reverse.flatMap (block20RC_top d)) ++
  [unleave150CTop, TickCut.Hosted.unroutedHigh MixedWindow.j7 1 14,
   Shadow7.archiveRestoreP MixedWindow.j6 d, MixedWindow.unpackW d 150 140,
   Shadow7.unrouted MixedWindow.j7 0 1, enterInv15C MixedWindow.j7] ++
  (MixedWindow.prefixPairs.reverse.flatMap fun p => block15RC_top d p.1 p.2) ++
  [unleave15CTop MixedWindow.j0, TickCut.Hosted.unroutedHigh MixedWindow.j0 1 14,
   MixedWindow.unpackW d 45 45, Shadow7.unrouted MixedWindow.j0 0 1,
   enterInv15C MixedWindow.j0, portalInvC 45]

def reverseUncutTop (d : Bool) : Program := (reverseL_top d).flatten
def reverseCutTop (d : Bool) : Program := (reverseLC_top d).flatten

theorem bnd_rev_exit_top
    (htail : (Shadow7.portalP 420).drop ((Shadow7.portalP 420).length - 6) = Eblk15 (start ⟨24, by decide⟩))
    (hL : 2 ≤ Shadow7.lowsP (start ⟨24, by decide⟩))
    (havoid : ∀ q ∈ wires (Eblk15 (start ⟨24, by decide⟩)),
      q ∉ wires ([] ++ (Shadow7.parkInvP 420 ++ GateMirror.inverse (Shadow7.leaveClose (start ⟨24, by decide⟩)))))
    (hsub : wires (Dblk15 (start ⟨24, by decide⟩)) ⊆ wires (Eblk15 (start ⟨24, by decide⟩)))
    (inv : ∀ u (a b : List Bool), run (Dblk15 (start ⟨24, by decide⟩)) b (run (Eblk15 (start ⟨24, by decide⟩)) a u) = u)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n + 1) (Shadow7.portalP 420 :: Shadow7.parkInvP 420 :: unleave15Top ⟨24, by decide⟩ :: ps)
      (portalC 420 :: Shadow7.parkInvP 420 :: unleave15CTop ⟨24, by decide⟩ :: ps') := by
  obtain ⟨R, hR⟩ := unleave15Top_shape ⟨24, by decide⟩ (by decide) hL
  have hC := unleave15CTop_eq ⟨24, by decide⟩ (by decide) R hR
  have h1 : Shadow7.portalP 420 = portalC 420 ++ (Eblk15 (start ⟨24, by decide⟩) ++ []) := by
    rw [← htail]; simp only [portalC, List.append_nil, List.take_append_drop]
  have h2 : portalC 420 = portalC 420 ++ [] := by simp
  rw [h1, hR, hC]; conv_rhs => rw [h2]
  exact Cut.triple _ _ [] (Shadow7.parkInvP 420) _ _ R (wires (Eblk15 (start ⟨24, by decide⟩)))
    (Finset.Subset.refl _) hsub havoid rfl rfl rfl rfl inv h

theorem bnd_rev15_top (k : Nat) (hk : k < 24)
    (htail : (Shadow7.enterInvP ⟨k + 1, by omega⟩).drop ((Shadow7.enterInvP ⟨k + 1, by omega⟩).length - 6) = Dblk15 (start ⟨k, by omega⟩))
    (hL : 2 ≤ Shadow7.lowsP (start ⟨k, by omega⟩))
    (havoid : ∀ q ∈ wires (Dblk15 (start ⟨k, by omega⟩)),
      q ∉ wires ([] ++ GateMirror.inverse (Shadow7.leaveClose (start ⟨k, by omega⟩))))
    (inv : ∀ u (a b : List Bool), run (Dblk15 (start ⟨k, by omega⟩)) b (run (Dblk15 (start ⟨k, by omega⟩)) a u) = u)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n + 1) (Shadow7.enterInvP ⟨k + 1, by omega⟩ :: unleave15Top ⟨k, by omega⟩ :: ps)
      (enterInv15C ⟨k + 1, by omega⟩ :: unleave15CTop ⟨k, by omega⟩ :: ps') := by
  obtain ⟨R, hR⟩ := unleave15Top_shape ⟨k, by omega⟩ (by simp; omega) hL
  have hC := unleave15CTop_eq ⟨k, by omega⟩ (by simp; omega) R hR
  have h1 : Shadow7.enterInvP ⟨k + 1, by omega⟩ = enterInv15C ⟨k + 1, by omega⟩ ++ (Dblk15 (start ⟨k, by omega⟩) ++ []) := by
    rw [← htail]; simp only [enterInv15C, List.append_nil, List.take_append_drop]
  have h2 : enterInv15C ⟨k + 1, by omega⟩ = enterInv15C ⟨k + 1, by omega⟩ ++ [] := by simp
  rw [h1, hR, hC]; conv_rhs => rw [h2]
  exact Cut.pair _ _ [] _ _ R (wires (Dblk15 (start ⟨k, by omega⟩))) (Finset.Subset.refl _) (Finset.Subset.refl _)
    havoid rfl rfl rfl rfl inv h

theorem bnd_rev20To15_top
    (htail : (Shadow7.enterInvP MixedWindow.j20).drop ((Shadow7.enterInvP MixedWindow.j20).length - 6) = Dblk20 (start20 MixedWindow.k8))
    (hL : 2 ≤ lowsP20 (start20 MixedWindow.k8))
    (havoid : ∀ q ∈ wires (Dblk20 (start20 MixedWindow.k8)),
      q ∉ wires ([] ++ GateMirror.inverse (leaveClose20 (start20 MixedWindow.k8))))
    (inv : ∀ u (a b : List Bool), run (Dblk20 (start20 MixedWindow.k8)) b (run (Dblk20 (start20 MixedWindow.k8)) a u) = u)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n + 1) (Shadow7.enterInvP MixedWindow.j20 :: unleave20Top MixedWindow.k8 :: ps)
      (enterInv15C MixedWindow.j20 :: unleave20CTop MixedWindow.k8 :: ps') := by
  obtain ⟨R, hR⟩ := unleave20Top_shape MixedWindow.k8 hL
  have hC := unleave20CTop_eq MixedWindow.k8 R hR
  have h1 : Shadow7.enterInvP MixedWindow.j20 = enterInv15C MixedWindow.j20 ++ (Dblk20 (start20 MixedWindow.k8) ++ []) := by
    rw [← htail]; simp only [enterInv15C, List.append_nil, List.take_append_drop]
  have h2 : enterInv15C MixedWindow.j20 = enterInv15C MixedWindow.j20 ++ [] := by simp
  rw [h1, hR, hC]; conv_rhs => rw [h2]
  exact Cut.pair _ _ [] _ _ R (wires (Dblk20 (start20 MixedWindow.k8))) (Finset.Subset.refl _) (Finset.Subset.refl _)
    havoid rfl rfl rfl rfl inv h

theorem bnd_rev20To20_top (k : Nat) (hk : k < 8)
    (htail : (enterInvP20 ⟨k + 1, by omega⟩).drop ((enterInvP20 ⟨k + 1, by omega⟩).length - 6) = Dblk20 (start20 ⟨k, by omega⟩))
    (hL : 2 ≤ lowsP20 (start20 ⟨k, by omega⟩))
    (havoid : ∀ q ∈ wires (Dblk20 (start20 ⟨k, by omega⟩)),
      q ∉ wires ([] ++ GateMirror.inverse (leaveClose20 (start20 ⟨k, by omega⟩))))
    (inv : ∀ u (a b : List Bool), run (Dblk20 (start20 ⟨k, by omega⟩)) b (run (Dblk20 (start20 ⟨k, by omega⟩)) a u) = u)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n + 1) (enterInvP20 ⟨k + 1, by omega⟩ :: unleave20Top ⟨k, by omega⟩ :: ps)
      (enterInv20C ⟨k + 1, by omega⟩ :: unleave20CTop ⟨k, by omega⟩ :: ps') := by
  obtain ⟨R, hR⟩ := unleave20Top_shape ⟨k, by omega⟩ hL
  have hC := unleave20CTop_eq ⟨k, by omega⟩ R hR
  have h1 : enterInvP20 ⟨k + 1, by omega⟩ = enterInv20C ⟨k + 1, by omega⟩ ++ (Dblk20 (start20 ⟨k, by omega⟩) ++ []) := by
    rw [← htail]; simp only [enterInv20C, List.append_nil, List.take_append_drop]
  have h2 : enterInv20C ⟨k + 1, by omega⟩ = enterInv20C ⟨k + 1, by omega⟩ ++ [] := by simp
  rw [h1, hR, hC]; conv_rhs => rw [h2]
  exact Cut.pair _ _ [] _ _ R (wires (Dblk20 (start20 ⟨k, by omega⟩))) (Finset.Subset.refl _) (Finset.Subset.refl _)
    havoid rfl rfl rfl rfl inv h

theorem bnd_rev150To20_top
    (htail : (enterInvP20 ⟨0, by decide⟩).drop ((enterInvP20 ⟨0, by decide⟩).length - 6) = Dblk150)
    (havoid : ∀ q ∈ wires Dblk150, q ∉ wires ([] ++ GateMirror.inverse leaveClose150To20))
    (inv : ∀ u (a b : List Bool), run Dblk150 b (run Dblk150 a u) = u)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n + 1) (enterInvP20 ⟨0, by decide⟩ :: unleave150Top :: ps)
      (enterInv20C ⟨0, by decide⟩ :: unleave150CTop :: ps') := by
  obtain ⟨R, hR⟩ := unleave150Top_shape
  have hC := unleave150CTop_eq R hR
  have h1 : enterInvP20 ⟨0, by decide⟩ = enterInv20C ⟨0, by decide⟩ ++ (Dblk150 ++ []) := by
    rw [← htail]; simp only [enterInv20C, List.append_nil, List.take_append_drop]
  have h2 : enterInv20C ⟨0, by decide⟩ = enterInv20C ⟨0, by decide⟩ ++ [] := by simp
  rw [h1, hR, hC]; conv_rhs => rw [h2]
  exact Cut.pair _ _ [] _ _ R (wires Dblk150) (Finset.Subset.refl _) (Finset.Subset.refl _)
    havoid rfl rfl rfl rfl inv h

theorem bnd_rev_end_top
    (hhead : (Shadow7.portalInvP 45).take 6 = (Shadow7.enterInvP MixedWindow.j0).drop ((Shadow7.enterInvP MixedWindow.j0).length - 6))
    (inv : ∀ u (a b : List Bool), run ((Shadow7.enterInvP MixedWindow.j0).drop ((Shadow7.enterInvP MixedWindow.j0).length - 6)) b
      (run ((Shadow7.enterInvP MixedWindow.j0).drop ((Shadow7.enterInvP MixedWindow.j0).length - 6)) a u) = u)
    (m0 : measurementCount ((Shadow7.enterInvP MixedWindow.j0).drop ((Shadow7.enterInvP MixedWindow.j0).length - 6)) = 0)
    (t0 : toffoliCount ((Shadow7.enterInvP MixedWindow.j0).drop ((Shadow7.enterInvP MixedWindow.j0).length - 6)) = 2)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n + 1) (Shadow7.enterInvP MixedWindow.j0 :: Shadow7.portalInvP 45 :: ps)
      (enterInv15C MixedWindow.j0 :: portalInvC 45 :: ps') := by
  have h1 : Shadow7.enterInvP MixedWindow.j0 =
      enterInv15C MixedWindow.j0 ++ ((Shadow7.enterInvP MixedWindow.j0).drop ((Shadow7.enterInvP MixedWindow.j0).length - 6) ++ []) := by
    simp only [enterInv15C, List.append_nil, List.take_append_drop]
  have h2 : enterInv15C MixedWindow.j0 = enterInv15C MixedWindow.j0 ++ [] := by simp
  have h3 : Shadow7.portalInvP 45 =
      [] ++ ((Shadow7.enterInvP MixedWindow.j0).drop ((Shadow7.enterInvP MixedWindow.j0).length - 6) ++ portalInvC 45) := by
    rw [← hhead]; simp only [List.nil_append, portalInvC, List.take_append_drop]
  have h4 : portalInvC 45 = [] ++ portalInvC 45 := rfl
  rw [h1, h3]; conv_rhs => rw [h2, h4]
  exact Cut.pair _ _ [] [] _ _ (wires ((Shadow7.enterInvP MixedWindow.j0).drop ((Shadow7.enterInvP MixedWindow.j0).length - 6)))
    (Finset.Subset.refl _) (Finset.Subset.refl _) (by intro q _; simp [wires]) m0 m0 t0 t0 inv h

theorem finRange9_lit : List.finRange 9 =
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩,
     ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩] := by decide

theorem rev_top_cut (d : Bool) : Cut 23 (reverseL_top d) (reverseLC_top d) := by
  simp only [reverseL_top, reverseLC_top, MixedWindow.prefixPairs, MixedWindow.suffixPairs, finRange9_lit,
    List.reverse_cons, List.reverse_nil, block15R_top, block15RC_top, block20R_top, block20RC_top,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_assoc,
    show (0 : Nat) = 0 from rfl, ↓reduceIte,
    show ¬(1 : Nat) = 0 by decide, show ¬(2 : Nat) = 0 by decide, show ¬(3 : Nat) = 0 by decide,
    show ¬(4 : Nat) = 0 by decide, show ¬(5 : Nat) = 0 by decide, show ¬(6 : Nat) = 0 by decide,
    show ¬(7 : Nat) = 0 by decide, show ¬(8 : Nat) = 0 by decide]
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev_exit_top (by decide +kernel) (by decide +kernel)
    (avoid_of_check _ _ (by decide +kernel)) (sub_of_check _ _ (by decide +kernel))
    (inv_swap_of_eq _ _ _ _ _ _ _ (Eblk15_S2 _) (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev15_top 23 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev15_top 22 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev15_top 21 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev15_top 20 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev20To15_top (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev20To20_top 7 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev20To20_top 6 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev20To20_top 5 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev20To20_top 4 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev20To20_top 3 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev20To20_top 2 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev20To20_top 1 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev20To20_top 0 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev150To20_top (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ Dblk150_S2 (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev15_top 6 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev15_top 5 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev15_top 4 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev15_top 3 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev15_top 2 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev15_top 1 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev15_top 0 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev_end_top (by decide +kernel)
    (inv_of_eq _ 60 1028 303 1027 302 (by decide +kernel) (by decide +kernel))
    (S2_measure0 _ 60 1028 303 1027 302 (by decide +kernel)) (by decide +kernel)
  exact Cut.nil

theorem reverse_top_run_eq (d : Bool) : run (reverseCutTop d) = run (reverseUncutTop d) :=
  funext fun m => funext fun s => (rev_top_cut d).run_eq m s

/-! ### 10. Static metrics comparing `reverseCutTop d` against `TickCut.Mixed.reverse d` (-22 T) -/

structure TopRel (k : Nat) (P Q : Program) : Prop where
  tc_eq : toffoliCount P + k = toffoliCount Q
  mc_eq : measurementCount P = measurementCount Q
  slots_le : gateSlots P ≤ gateSlots Q
  wires_sub : wires P ⊆ wires Q
  phys : GatePhysical Q → GatePhysical P

theorem TopRel.refl (P : Program) : TopRel 0 P P where
  tc_eq := Nat.add_zero _
  mc_eq := rfl
  slots_le := Nat.le_refl _
  wires_sub := Finset.Subset.refl _
  phys := id

theorem TopRel.app {k1 k2 : Nat} {P1 Q1 P2 Q2 : Program}
    (h1 : TopRel k1 P1 Q1) (h2 : TopRel k2 P2 Q2) :
    TopRel (k1 + k2) (P1 ++ P2) (Q1 ++ Q2) where
  tc_eq := by simp only [toffoliCount_append]; have := h1.tc_eq; have := h2.tc_eq; omega
  mc_eq := by simp only [measurementCount_append, h1.mc_eq, h2.mc_eq]
  slots_le := by simp only [gateSlots_append]; exact Nat.add_le_add h1.slots_le h2.slots_le
  wires_sub := by
    intro q hq; simp only [wires_append, Finset.mem_union] at hq ⊢
    rcases hq with h | h
    · exact Or.inl (h1.wires_sub h)
    · exact Or.inr (h2.wires_sub h)
  phys hp := by
    rw [gatePhysical_append] at hp ⊢
    exact ⟨h1.phys hp.1, h2.phys hp.2⟩

theorem TopRel.cast {k1 k2 : Nat} {P Q : Program} (h : TopRel k1 P Q) (e : k1 = k2) :
    TopRel k2 P Q := e ▸ h

def LTopRel (k : Nat) (ps qs : List Program) : Prop := TopRel k ps.flatten qs.flatten

theorem LTopRel.refl (ps : List Program) : LTopRel 0 ps ps := TopRel.refl ps.flatten

theorem LTopRel.cons {k1 k2 : Nat} {p q : Program} {ps qs : List Program}
    (h1 : TopRel k1 p q) (h2 : LTopRel k2 ps qs) : LTopRel (k1 + k2) (p :: ps) (q :: qs) := by
  simpa only [LTopRel, List.flatten_cons] using TopRel.app h1 h2

theorem LTopRel.app {k1 k2 : Nat} {ps1 qs1 ps2 qs2 : List Program}
    (h1 : LTopRel k1 ps1 qs1) (h2 : LTopRel k2 ps2 qs2) :
    LTopRel (k1 + k2) (ps1 ++ ps2) (qs1 ++ qs2) := by
  simpa only [LTopRel, List.flatten_append] using TopRel.app h1 h2

theorem LTopRel.cast {k1 k2 : Nat} {ps qs : List Program} (h : LTopRel k1 ps qs) (e : k1 = k2) :
    LTopRel k2 ps qs := e ▸ h

theorem LTopRel.flatMap {α : Type} (xs : List α) (f g : α → List Program) (k : Nat)
    (h : ∀ x ∈ xs, LTopRel k (f x) (g x)) :
    LTopRel (xs.length * k) (xs.flatMap f) (xs.flatMap g) := by
  induction xs with
  | nil => simpa only [List.length_nil, Nat.zero_mul, List.flatMap_nil] using LTopRel.refl []
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact (LTopRel.app h1 h2).cast (by ring)

theorem rel15C (j : Fin 26) (hi : j.val ≤ 24) (hL : 2 ≤ Shadow7.lowsP (start j)) :
    TopRel 1 (unleave15CTop j) (unleave15C j) := by
  obtain ⟨t, m, s, w, p⟩ := unleave15CTop_rel j hi hL
  exact ⟨t, m, by omega, w, fun _ => p⟩

theorem rel150C : TopRel 1 unleave150CTop unleave150C := by
  obtain ⟨t, m, s, w, p⟩ := unleave150CTop_rel
  exact ⟨t, m, by omega, w, fun _ => p⟩

theorem rel20C (j : Fin 9) (hL : 2 ≤ lowsP20 (start20 j)) :
    TopRel 1 (unleave20CTop j) (unleave20C j) := by
  obtain ⟨t, m, s, w, p⟩ := unleave20CTop_rel j hL
  exact ⟨t, m, by omega, w, fun _ => p⟩

theorem lows15_ge2 : ∀ j : Fin 26, j.val ≤ 24 → 2 ≤ Shadow7.lowsP (start j) := by decide +kernel
theorem lows20_ge2 : ∀ j : Fin 9, 2 ≤ lowsP20 (start20 j) := by decide +kernel

theorem block15RC_top_rel (d : Bool) (i j : Fin 26) (hi : j.val ≤ 24) :
    LTopRel 1 (block15RC_top d i j) (TickCut.Mixed.block15RC d i j) := by
  unfold block15RC_top TickCut.Mixed.block15RC
  exact (LTopRel.cons (rel15C j hi (lows15_ge2 j hi)) (LTopRel.refl _)).cast rfl

theorem block20RC_top_rel (d : Bool) (j : Fin 9) :
    LTopRel 1 (block20RC_top d j) (TickCut.Mixed.block20RC d j) := by
  by_cases h0 : j.val = 0
  · simp only [block20RC_top, TickCut.Mixed.block20RC, h0, ↓reduceIte, ↓reduceDIte]
    exact (LTopRel.cons (rel20C j (lows20_ge2 j)) (LTopRel.refl _)).cast rfl
  · simp only [block20RC_top, TickCut.Mixed.block20RC, h0, ↓reduceIte, ↓reduceDIte]
    exact (LTopRel.cons (rel20C j (lows20_ge2 j)) (LTopRel.refl _)).cast rfl

theorem reverseCutTop_metrics (d : Bool) :
    toffoliCount (reverseCutTop d) + 22 = toffoliCount (TickCut.Mixed.reverse d) ∧
    measurementCount (reverseCutTop d) = measurementCount (TickCut.Mixed.reverse d) ∧
    gateSlots (reverseCutTop d) ≤ gateSlots (TickCut.Mixed.reverse d) ∧
    wires (reverseCutTop d) ⊆ wires (TickCut.Mixed.reverse d) ∧
    GatePhysical (reverseCutTop d) := by
  have hrel : LTopRel 22 (reverseLC_top d) (TickCut.Mixed.reverseLC d) := by
    unfold reverseLC_top TickCut.Mixed.reverseLC
    have he := LTopRel.refl [Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410,
      MixedWindow.recvW 420, portalC 420, Shadow7.parkInvP 420]
    have h3 := LTopRel.flatMap MixedWindow.suffixPairs.reverse
      (fun p => block15RC_top d p.1 p.2) (fun p => TickCut.Mixed.block15RC d p.1 p.2) 1
      (fun x hx => block15RC_top_rel d x.1 x.2 (by
        simp only [MixedWindow.suffixPairs, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> decide))
    have h20 : LTopRel 1
        [unleave15CTop MixedWindow.j20, TickCut.Hosted.unroutedHigh MixedWindow.j20 1 14,
          archiveRestoreP20 MixedWindow.k8 d, MixedWindow.unpackW d 345 335, MixedWindow.unpackW d 345 330,
          Shadow7.unrouted MixedWindow.j20 0 1, enterInv15C MixedWindow.j20]
        [unleave15C MixedWindow.j20, TickCut.Hosted.unroutedHigh MixedWindow.j20 1 14,
          archiveRestoreP20 MixedWindow.k8 d, MixedWindow.unpackW d 345 335, MixedWindow.unpackW d 345 330,
          Shadow7.unrouted MixedWindow.j20 0 1, enterInv15C MixedWindow.j20] :=
      (LTopRel.cons (rel15C MixedWindow.j20 (by decide) (by decide)) (LTopRel.refl _)).cast rfl
    have h2 := LTopRel.flatMap (List.finRange 9).reverse
      (block20RC_top d) (TickCut.Mixed.block20RC d) 1 (fun x _ => block20RC_top_rel d x)
    have h7 : LTopRel 1
        [unleave150CTop, TickCut.Hosted.unroutedHigh MixedWindow.j7 1 14,
          Shadow7.archiveRestoreP MixedWindow.j6 d, MixedWindow.unpackW d 150 140,
          Shadow7.unrouted MixedWindow.j7 0 1, enterInv15C MixedWindow.j7]
        [unleave150C, TickCut.Hosted.unroutedHigh MixedWindow.j7 1 14,
          Shadow7.archiveRestoreP MixedWindow.j6 d, MixedWindow.unpackW d 150 140,
          Shadow7.unrouted MixedWindow.j7 0 1, enterInv15C MixedWindow.j7] :=
      (LTopRel.cons rel150C (LTopRel.refl _)).cast rfl
    have h1 := LTopRel.flatMap MixedWindow.prefixPairs.reverse
      (fun p => block15RC_top d p.1 p.2) (fun p => TickCut.Mixed.block15RC d p.1 p.2) 1
      (fun x hx => block15RC_top_rel d x.1 x.2 (by
        simp only [MixedWindow.prefixPairs, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    have h0 : LTopRel 1
        [unleave15CTop MixedWindow.j0, TickCut.Hosted.unroutedHigh MixedWindow.j0 1 14,
          MixedWindow.unpackW d 45 45, Shadow7.unrouted MixedWindow.j0 0 1,
          enterInv15C MixedWindow.j0, portalInvC 45]
        [unleave15C MixedWindow.j0, TickCut.Hosted.unroutedHigh MixedWindow.j0 1 14,
          MixedWindow.unpackW d 45 45, Shadow7.unrouted MixedWindow.j0 0 1,
          enterInv15C MixedWindow.j0, portalInvC 45] :=
      (LTopRel.cons (rel15C MixedWindow.j0 (by decide) (by decide)) (LTopRel.refl _)).cast rfl
    exact ((((((he.app h3).app h20).app h2).app h7).app h1).app h0).cast (by
      simp [MixedWindow.prefixPairs, MixedWindow.suffixPairs])
  exact ⟨hrel.tc_eq, hrel.mc_eq, hrel.slots_le, hrel.wires_sub, hrel.phys (TickCut.Mixed.physical d)⟩

end ECDSAAdd.Entrant.StairPacket.ChainMidTop

end
