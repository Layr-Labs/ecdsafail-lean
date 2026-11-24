import ECDSAAdd.Submission.Entrant.LeaveReductions

/-!
# FRED-CUT core (VAST3, 11-23)

Each window boundary `leave_k → enter_{k+1}` (and `portal → enter_0`, `leave_24 → park → portalInv`) carries the
same two controlled swaps at the tail of the first piece and at the head of the second; the gates between them
never touch the swaps' wires.  The swaps are measurement-free and self-inverse, so both copies can be dropped:
the run is unchanged for every state and tape.
-/

set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairPacket.FredCut
open ECDSAAdd ECDSAAdd.Arithmetic

/-! ## Generic layer -/

/-- One controlled swap `c ? (a ↔ b)` as three CNOT/Toffoli instructions (`GateMirror.cswapG` mirrored). -/
def cs (c a b : Wire) : Program := [.CX b a, .CCX c a b, .CX b a]

theorem cs_measure (c a b : Wire) : measurementCount (cs c a b) = 0 := rfl

theorem cs_run (c a b : Wire) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) (m : List Bool) (t : State) :
    run (cs c a b) m t =
      ⟨t.phase, fun q => if t.basis c then (if q = a then t.basis b else if q = b then t.basis a else t.basis q)
        else t.basis q⟩ := by
  have hba : b ≠ a := Ne.symm hab
  simp only [cs, run, writeBit]
  congr 1
  funext q
  simp only [Function.update_apply, if_neg hba, if_neg hca, if_neg hcb, if_neg hab, if_true]
  by_cases hqa : q = a
  · subst hqa
    simp only [if_true, if_neg hab]
    cases t.basis c <;> cases t.basis q <;> cases t.basis b <;> rfl
  · by_cases hqb : q = b
    · subst hqb
      simp only [if_neg hqa, if_true]
      cases t.basis c <;> cases t.basis a <;> cases t.basis q <;> rfl
    · simp only [if_neg hqa, if_neg hqb]
      cases t.basis c <;> rfl

/-- Two controlled swaps on disjoint pairs under one control. -/
def S2 (c a b a' b' : Wire) : Program := cs c a b ++ cs c a' b'

theorem S2_measure (c a b a' b' : Wire) : measurementCount (S2 c a b a' b') = 0 := rfl

theorem S2_inv (c a b a' b' : Wire) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) (hca' : c ≠ a') (hcb' : c ≠ b')
    (hab' : a' ≠ b') (h1 : a ≠ a') (h2 : a ≠ b') (h3 : b ≠ a') (h4 : b ≠ b')
    (t : State) (m1 m2 : List Bool) : run (S2 c a b a' b') m2 (run (S2 c a b a' b') m1 t) = t := by
  simp only [S2, run_append, cs_measure, List.take_zero, List.drop_zero]
  rw [cs_run c a b hca hcb hab, cs_run c a' b' hca' hcb' hab', cs_run c a b hca hcb hab,
    cs_run c a' b' hca' hcb' hab']
  apply State.extensionality
  · rfl
  · funext q
    have e1 := hca.symm; have e2 := hcb.symm; have e3 := hab.symm; have e4 := hca'.symm; have e5 := hcb'.symm
    have e6 := hab'.symm; have e7 := h1.symm; have e8 := h2.symm; have e9 := h3.symm; have e10 := h4.symm
    by_cases hc : t.basis c
    · by_cases hqa : q = a
      · subst hqa
        simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      · by_cases hqb : q = b
        · subst hqb
          simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hqa]
        · by_cases hqa' : q = a'
          · subst hqa'
            simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hqa,
              hqb]
          · by_cases hqb' : q = b'
            · subst hqb'
              simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
                hqa, hqb, hqa']
            · simp [hc, hca, hcb, hca', hcb', hqa, hqb, hqa', hqb']
    · simp [hc, hca, hcb, hca', hcb']

/-- Cancellation of a measurement-free block pair around a middle `M` that never touches `W ⊇ wires E`: the
middle commutes past `E` (disjoint wires), then `D` undoes `E`. -/
theorem cancel_free (E M D : Program) (W : Finset Wire)
    (hE : wires E ⊆ W) (hM : ∀ q ∈ W, q ∉ wires M)
    (inv : ∀ t (a b : List Bool), run D b (run E a t) = t)
    (x : State) (me mm md : List Bool) :
    run D md (run M mm (run E me x)) = run M mm x := by
  have dis : Disjoint (wires M) (wires E) :=
    Finset.disjoint_left.mpr (fun q hqM hqE => hM q (hE hqE) hqM)
  rw [run_disjoint_commute M E dis mm me x]
  exact inv _ _ _

/-- FRED cancellation: a measurement-free self-inverse block `S` on both sides of a middle `M` that never touches
`wires S` can be dropped, for every state and tape. -/
theorem fred_cancel (S M Y : Program) (hM : ∀ q ∈ wires S, q ∉ wires M)
    (h0 : measurementCount S = 0) (inv : ∀ t (a b : List Bool), run S b (run S a t) = t)
    (m : List Bool) (s : State) :
    run (S ++ (M ++ (S ++ Y))) m s = run (M ++ Y) m s := by
  rw [run_append S, h0, List.take_zero, List.drop_zero, run_append M, run_append S, h0, List.take_zero,
    List.drop_zero, run_append M]
  congr 1
  exact cancel_free S M S (wires S) (Finset.Subset.refl _) hM inv s [] _ []

/-- The same with an arbitrary prefix. -/
theorem fred_cancel_pre (X S M Y : Program) (hM : ∀ q ∈ wires S, q ∉ wires M)
    (h0 : measurementCount S = 0) (inv : ∀ t (a b : List Bool), run S b (run S a t) = t)
    (m : List Bool) (s : State) :
    run (X ++ (S ++ (M ++ (S ++ Y)))) m s = run (X ++ (M ++ Y)) m s := by
  rw [run_append X, run_append X]
  exact fred_cancel S M Y hM h0 inv _ _

/-! ## Piece-list cuts -/

/-- `Cut n ps ps'`: `ps'` is `ps` with `n` boundary block pairs removed (each block 2 Toffolis).  `pair`: the tail block `E` of one piece (followed by
that piece's suffix `M1`) and the head block `D` of the next piece (preceded by its prefix `M2`) cancel around
`M1 ++ M2`; `triple`: the same across one whole intermediate piece `Q`.  Blocks are measurement-free, act inside
`W`, `D` undoes `E`, and the gates between them avoid `W`. -/
inductive Cut : Nat → List Program → List Program → Prop
  | nil : Cut 0 [] []
  | keep (p : Program) {n : Nat} {ps ps' : List Program} : Cut n ps ps' → Cut n (p :: ps) (p :: ps')
  | pair (A E M1 M2 D B : Program) (W : Finset Wire) {n : Nat} {ps ps' : List Program}
      (hE : wires E ⊆ W) (hD : wires D ⊆ W) (hM : ∀ q ∈ W, q ∉ wires (M1 ++ M2))
      (mE : measurementCount E = 0) (mD : measurementCount D = 0)
      (tE : toffoliCount E = 2) (tD : toffoliCount D = 2)
      (inv : ∀ t (a b : List Bool), run D b (run E a t) = t) :
      Cut n ps ps' → Cut (n+1) ((A ++ (E ++ M1)) :: (M2 ++ (D ++ B)) :: ps) ((A ++ M1) :: (M2 ++ B) :: ps')
  | triple (A E M1 Q M2 D B : Program) (W : Finset Wire) {n : Nat} {ps ps' : List Program}
      (hE : wires E ⊆ W) (hD : wires D ⊆ W) (hM : ∀ q ∈ W, q ∉ wires (M1 ++ (Q ++ M2)))
      (mE : measurementCount E = 0) (mD : measurementCount D = 0)
      (tE : toffoliCount E = 2) (tD : toffoliCount D = 2)
      (inv : ∀ t (a b : List Bool), run D b (run E a t) = t) :
      Cut n ps ps' → Cut (n+1) ((A ++ (E ++ M1)) :: Q :: (M2 ++ (D ++ B)) :: ps) ((A ++ M1) :: Q :: (M2 ++ B) :: ps')

theorem app_congr (X T T' : Program) (h : ∀ m s, run T m s = run T' m s) (m : List Bool) (s : State) :
    run (X ++ T) m s = run (X ++ T') m s := by
  rw [run_append, run_append, h]

/-- Core block cancellation with a prefix and a run-equal suffix. -/
theorem block_cancel (A E M D Y Y' : Program) (W : Finset Wire)
    (hE : wires E ⊆ W) (_hD : wires D ⊆ W) (hM : ∀ q ∈ W, q ∉ wires M)
    (mE : measurementCount E = 0) (mD : measurementCount D = 0)
    (inv : ∀ t (a b : List Bool), run D b (run E a t) = t)
    (hY : ∀ m s, run Y' m s = run Y m s) (m : List Bool) (s : State) :
    run (A ++ (M ++ Y')) m s = run (A ++ (E ++ (M ++ (D ++ Y)))) m s := by
  rw [run_append A (M ++ Y'), run_append A (E ++ (M ++ (D ++ Y)))]
  generalize run A (m.take (measurementCount A)) s = t
  generalize m.drop (measurementCount A) = m'
  rw [run_append M Y', run_append E (M ++ (D ++ Y)), mE, List.take_zero, List.drop_zero,
    run_append M (D ++ Y), run_append D Y, mD, List.take_zero, List.drop_zero, hY,
    cancel_free E M D W hE hM inv t [] _ []]

theorem Cut.run_eq {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') (m : List Bool) (s : State) :
    run ps'.flatten m s = run ps.flatten m s := by
  induction h generalizing m s with
  | nil => rfl
  | keep p _ ih =>
    simp only [List.flatten_cons]
    exact app_congr p _ _ (fun m s => ih m s) m s
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, List.append_assoc]
    have h := block_cancel A E (M1 ++ M2) D (B ++ _) (B ++ _) W hE hD hM mE mD inv
      (fun m s => app_congr B _ _ (fun m s => ih m s) m s) m s
    simpa only [List.append_assoc] using h
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, List.append_assoc]
    have h := block_cancel A E (M1 ++ (Q ++ M2)) D (B ++ _) (B ++ _) W hE hD hM mE mD inv
      (fun m s => app_congr B _ _ (fun m s => ih m s) m s) m s
    simpa only [List.append_assoc] using h


theorem Cut.mc_eq {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    measurementCount ps'.flatten = measurementCount ps.flatten := by
  induction h with
  | nil => rfl
  | keep p _ ih => simp only [List.flatten_cons, measurementCount_append, ih]
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, measurementCount_append, ih, mE, mD]; omega
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, measurementCount_append, ih, mE, mD]; omega

theorem Cut.wires_sub {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    wires ps'.flatten ⊆ wires ps.flatten := by
  induction h with
  | nil => exact Finset.Subset.refl _
  | keep p _ ih =>
    simp only [List.flatten_cons, wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _) ih
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    rcases hq with ((hq | hq) | (hq | hq) | hq) <;> tauto
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    rcases hq with ((hq | hq) | hq | (hq | hq) | hq) <;> tauto

/-- Each cancelled pair removes two blocks of two Toffolis. -/
theorem Cut.tc_eq {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    toffoliCount ps'.flatten + 4 * n = toffoliCount ps.flatten := by
  induction h with
  | nil => rfl
  | keep p _ ih => simp only [List.flatten_cons, toffoliCount_append]; omega
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, toffoliCount_append]; omega
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, toffoliCount_append]; omega

/-- Every instruction of the cut list is an instruction of the original. -/
theorem Cut.mem {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    ∀ i ∈ ps'.flatten, i ∈ ps.flatten := by
  induction h with
  | nil => exact fun _ h => h
  | keep p _ ih =>
    intro i hi
    simp only [List.flatten_cons, List.mem_append] at hi ⊢
    have := ih i
    tauto
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    intro i hi
    simp only [List.flatten_cons, List.mem_append] at hi ⊢
    have := ih i
    tauto
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    intro i hi
    simp only [List.flatten_cons, List.mem_append] at hi ⊢
    have := ih i
    tauto

theorem Cut.slots_le {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Challenge.gateSlots ps'.flatten ≤ Challenge.gateSlots ps.flatten := by
  induction h with
  | nil => exact le_refl _
  | keep p _ ih => simp only [List.flatten_cons, Challenge.gateSlots_append]; omega
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, Challenge.gateSlots_append]; omega
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, Challenge.gateSlots_append]; omega

/-- The two swaps in the other order undo the block too. -/
theorem S2_inv_swap (c a b a' b' : Wire) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) (hca' : c ≠ a') (hcb' : c ≠ b')
    (hab' : a' ≠ b') (h1 : a ≠ a') (h2 : a ≠ b') (h3 : b ≠ a') (h4 : b ≠ b')
    (t : State) (m1 m2 : List Bool) : run (S2 c a' b' a b) m2 (run (S2 c a b a' b') m1 t) = t := by
  simp only [S2, run_append, cs_measure, List.take_zero, List.drop_zero]
  rw [cs_run c a b hca hcb hab, cs_run c a' b' hca' hcb' hab', cs_run c a' b' hca' hcb' hab',
    cs_run c a b hca hcb hab]
  apply State.extensionality
  · rfl
  · funext q
    have e1 := hca.symm; have e2 := hcb.symm; have e3 := hab.symm; have e4 := hca'.symm; have e5 := hcb'.symm
    have e6 := hab'.symm; have e7 := h1.symm; have e8 := h2.symm; have e9 := h3.symm; have e10 := h4.symm
    by_cases hc : t.basis c
    · by_cases hqa : q = a
      · subst hqa
        simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      · by_cases hqb : q = b
        · subst hqb
          simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hqa]
        · by_cases hqa' : q = a'
          · subst hqa'
            simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hqa,
              hqb]
          · by_cases hqb' : q = b'
            · subst hqb'
              simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
                hqa, hqb, hqa']
            · simp [hc, hca, hcb, hca', hcb', hqa, hqb, hqa', hqb']
    · simp [hc, hca, hcb, hca', hcb']


/-! ## pp7 shapes -/
/-- The leave's low close ends with the two controlled swaps of its last two rows. -/
theorem lowClose_split (s : Nat) (hL : 1 ≤ Shadow7.lowsP s) :
    ∃ V, Shadow7.leaveLowClose s = V ++
      (Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1)) ++
       Partial.cswapG (s+30) (Shadow7.b0P s - 1 + Shadow7.lowsP s) (Shadow7.a0P s - 1 + Shadow7.lowsP s)) := by
  have hr : List.range (Shadow7.lowsP s + 1) =
      List.range (Shadow7.lowsP s - 1) ++ [Shadow7.lowsP s - 1, Shadow7.lowsP s] := by
    have e : Shadow7.lowsP s + 1 = (Shadow7.lowsP s - 1) + 1 + 1 := by omega
    rw [e, List.range_succ, List.range_succ, List.append_assoc]
    simp only [List.singleton_append, show Shadow7.lowsP s - 1 + 1 = Shadow7.lowsP s by omega]
  refine ⟨Partial.xsG ((List.range 15).map (s+16+·)) ++
      (List.range (Shadow7.lowsP s + 1)).map (fun i => GateMirror.Gate.cx (Shadow7.e0P s + 5) (Shadow7.b0P s - 1 + i)) ++
      (List.range (Shadow7.lowsP s - 1)).flatMap
        (fun i => Partial.cswapG (s+30) (Shadow7.b0P s - 1 + i) (Shadow7.a0P s - 1 + i)), ?_⟩
  unfold Shadow7.leaveLowClose
  simp only []
  rw [hr, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem suffix_after (s : Nat) :
    (Shadow7.leaveLowClose s ++ Shadow7.leaveClose s) <:+ KeptParity.afterRows s := by
  unfold KeptParity.afterRows KeptParity.afterTail CRTBarrel.tailE1
  simp only [List.append_assoc, List.cons_append]
  repeat (first
    | (with_reducible exact List.suffix_refl _)
    | refine List.IsSuffix.trans ?_ (List.suffix_append _ _)
    | refine List.IsSuffix.trans ?_ (List.suffix_cons _ _))

/-- The window leave (CRT barrel leave) as prefix ++ (two controlled swaps ++ leaveClose). -/
theorem leave_shape (k : Fin 26) (hk : k.val ≤ 24) (hL : 1 ≤ Shadow7.lowsP (start k)) :
    ∃ X, CRTBarrel.params.leave k = X ++ (GateMirror.forward
      (Partial.cswapG (start k + 30) (Shadow7.b0P (start k) - 1 + (Shadow7.lowsP (start k) - 1))
          (Shadow7.a0P (start k) - 1 + (Shadow7.lowsP (start k) - 1)) ++
        Partial.cswapG (start k + 30) (Shadow7.b0P (start k) - 1 + Shadow7.lowsP (start k))
          (Shadow7.a0P (start k) - 1 + Shadow7.lowsP (start k))) ++
      GateMirror.forward (Shadow7.leaveClose (start k))) := by
  obtain ⟨Z, hZ⟩ := suffix_after (start k)
  obtain ⟨V, hV⟩ := lowClose_split (start k) hL
  refine ⟨GateMirror.forward (CRTBarrel.beforeRow (start k)) ++ CRTBarrel.barrel (start k) false ++
    GateMirror.forward Z ++ GateMirror.forward V, ?_⟩
  show CRTBarrel.leave k = _
  unfold CRTBarrel.leave
  simp only [if_pos hk]
  rw [← hZ, hV]
  simp only [GateMirror.forward, List.map_append, List.append_assoc]


/-! ## pp7 window pieces -/
open ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

abbrev P : WindowFold.Pieces Program := CRTBarrel.params

def K (j : Fin 26) : Nat := (GateMirror.forward (Shadow7.leaveClose (start j))).length

def leaveC (j : Fin 26) : Program :=
  if j.val ≤ 24 then (P.leave j).take ((P.leave j).length - K j - 6) ++ (P.leave j).drop ((P.leave j).length - K j)
  else P.leave j
def unleaveC (j : Fin 26) : Program :=
  if j.val ≤ 24 then (P.leaveInv j).take (K j) ++ (P.leaveInv j).drop (K j + 6) else P.leaveInv j
def enterC (j : Fin 26) : Program := (P.enter j).drop 6
def enterInvC (j : Fin 26) : Program := (P.enterInv j).take ((P.enterInv j).length - 6)
def portalC (t : Nat) : Program := (P.portal t).take ((P.portal t).length - 6)
def portalInvC (t : Nat) : Program := (P.portalInv t).drop 6

def Pcut : WindowFold.Pieces Program where
  enter := enterC
  enterInv := enterInvC
  leave := leaveC
  leaveInv := unleaveC
  load := P.load
  restore := P.restore
  portal := portalC
  portalInv := portalInvC
  park := P.park
  parkInv := P.parkInv
  exitLoad := P.exitLoad
  exitRestore := P.exitRestore
  routed := P.routed
  unrouted := P.unrouted
  pack := P.pack
  unpack := P.unpack
  tick := P.tick
  receiver := P.receiver

attribute [irreducible] enterC enterInvC leaveC unleaveC portalC portalInvC

theorem Pcut_enter (j : Fin 26) : Pcut.enter j = enterC j := rfl
theorem Pcut_enterInv (j : Fin 26) : Pcut.enterInv j = enterInvC j := rfl
theorem Pcut_leave (j : Fin 26) : Pcut.leave j = leaveC j := rfl
theorem Pcut_leaveInv (j : Fin 26) : Pcut.leaveInv j = unleaveC j := rfl
theorem Pcut_portal (t : Nat) : Pcut.portal t = portalC t := rfl
theorem Pcut_portalInv (t : Nat) : Pcut.portalInv t = portalInvC t := rfl
theorem Pcut_park (t : Nat) : Pcut.park t = P.park t := rfl
theorem Pcut_parkInv (t : Nat) : Pcut.parkInv t = P.parkInv t := rfl

/-- The leave's tail block, as a program. -/
def Eblk (s : Nat) : Program := GateMirror.forward
  (Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1)) ++
   Partial.cswapG (s+30) (Shadow7.b0P s - 1 + Shadow7.lowsP s) (Shadow7.a0P s - 1 + Shadow7.lowsP s))

theorem Eblk_S2 (s : Nat) : Eblk s = S2 (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1))
    (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.b0P s - 1 + Shadow7.lowsP s)
    (Shadow7.a0P s - 1 + Shadow7.lowsP s) := rfl

theorem tc_Eblk (s : Nat) : toffoliCount (Eblk s) = 2 := rfl

theorem leaveC_eq (j : Fin 26) (hj : j.val ≤ 24) (X : Program)
    (hX : P.leave j = X ++ (Eblk (start j) ++ GateMirror.forward (Shadow7.leaveClose (start j)))) :
    Pcut.leave j = X ++ GateMirror.forward (Shadow7.leaveClose (start j)) := by
  rw [Pcut_leave]
  have hE : (Eblk (start j)).length = 6 := rfl
  unfold leaveC
  rw [if_pos hj, hX]
  simp only [List.length_append, hE, K]
  rw [show X.length + (6 + (GateMirror.forward (Shadow7.leaveClose (start j))).length) -
      (GateMirror.forward (Shadow7.leaveClose (start j))).length - 6 = X.length by omega,
    show X.length + (6 + (GateMirror.forward (Shadow7.leaveClose (start j))).length) -
      (GateMirror.forward (Shadow7.leaveClose (start j))).length = X.length + 6 by omega]
  rw [List.take_left' rfl, ← List.append_assoc, List.drop_left' (by simp [hE])]

/-- Forward boundary leave_k → enter_{k+1}. -/
theorem bnd_fwd (k : Nat) (hk : k < 24)
    (hhead : (P.enter ⟨k+1, by omega⟩).take 6 = Eblk (start ⟨k, by omega⟩))
    (hL : 1 ≤ Shadow7.lowsP (start ⟨k, by omega⟩))
    (havoid : ∀ q ∈ wires (Eblk (start ⟨k, by omega⟩)),
      q ∉ wires (GateMirror.forward (Shadow7.leaveClose (start ⟨k, by omega⟩)) ++ []))
    (inv : ∀ t (a b : List Bool), run (Eblk (start ⟨k, by omega⟩)) b (run (Eblk (start ⟨k, by omega⟩)) a t) = t)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.leave ⟨k, by omega⟩ :: P.enter ⟨k+1, by omega⟩ :: ps)
      (Pcut.leave ⟨k, by omega⟩ :: Pcut.enter ⟨k+1, by omega⟩ :: ps') := by
  obtain ⟨X, hX⟩ := leave_shape ⟨k, by omega⟩ (by simp; omega) hL
  have hX' : P.leave ⟨k, by omega⟩ = X ++ (Eblk (start ⟨k, by omega⟩) ++
      GateMirror.forward (Shadow7.leaveClose (start ⟨k, by omega⟩))) := hX
  have hC := leaveC_eq ⟨k, by omega⟩ (by simp; omega) X hX'
  have hEn : P.enter ⟨k+1, by omega⟩ = [] ++ (Eblk (start ⟨k, by omega⟩) ++ enterC ⟨k+1, by omega⟩) := by
    rw [← hhead]; simp only [List.nil_append, enterC, List.take_append_drop]
  have hEnC : Pcut.enter ⟨k+1, by omega⟩ = [] ++ enterC ⟨k+1, by omega⟩ := by
    rw [Pcut_enter, List.nil_append]
  rw [hX', hC, hEn, hEnC]
  exact Cut.pair X _ _ [] _ _ (wires (Eblk (start ⟨k, by omega⟩))) (Finset.Subset.refl _) (Finset.Subset.refl _)
    havoid rfl rfl (tc_Eblk _) (tc_Eblk _) inv h

/-- Forward boundary portal → enter_0. -/
theorem bnd_portal (t : Nat) (j : Fin 26)
    (hhead : (P.enter j).take 6 = (P.portal t).drop ((P.portal t).length - 6))
    (inv : ∀ u (a b : List Bool), run ((P.portal t).drop ((P.portal t).length - 6)) b
      (run ((P.portal t).drop ((P.portal t).length - 6)) a u) = u)
    (m0 : measurementCount ((P.portal t).drop ((P.portal t).length - 6)) = 0)
    (t0 : toffoliCount ((P.portal t).drop ((P.portal t).length - 6)) = 2)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.portal t :: P.enter j :: ps) (Pcut.portal t :: Pcut.enter j :: ps') := by
  have h1 : P.portal t = portalC t ++ ((P.portal t).drop ((P.portal t).length - 6) ++ []) := by
    simp only [portalC, List.append_nil, List.take_append_drop]
  have h2 : Pcut.portal t = portalC t ++ [] := by
    rw [Pcut_portal, List.append_nil]
  have h3 : P.enter j = [] ++ ((P.portal t).drop ((P.portal t).length - 6) ++ enterC j) := by
    rw [← hhead]; simp only [List.nil_append, enterC, List.take_append_drop]
  have h4 : Pcut.enter j = [] ++ enterC j := by
    rw [Pcut_enter, List.nil_append]
  rw [h1, h2, h3, h4]
  exact Cut.pair _ _ [] [] _ _ (wires ((P.portal t).drop ((P.portal t).length - 6))) (Finset.Subset.refl _)
    (Finset.Subset.refl _) (by intro q _; simp [wires]) m0 m0 t0 t0 inv h

/-- Forward exit boundary leave_24 → park → portalInv. -/
theorem bnd_exit (k : Nat) (hk : k ≤ 24) (e : Nat)
    (hL : 1 ≤ Shadow7.lowsP (start ⟨k, by omega⟩))
    (havoid : ∀ q ∈ wires (Eblk (start ⟨k, by omega⟩)),
      q ∉ wires (GateMirror.forward (Shadow7.leaveClose (start ⟨k, by omega⟩)) ++ (P.park e ++ [])))
    (hsub : wires ((P.portalInv e).take 6) ⊆ wires (Eblk (start ⟨k, by omega⟩)))
    (inv : ∀ u (a b : List Bool), run ((P.portalInv e).take 6) b (run (Eblk (start ⟨k, by omega⟩)) a u) = u)
    (mD : measurementCount ((P.portalInv e).take 6) = 0)
    (tD : toffoliCount ((P.portalInv e).take 6) = 2)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.leave ⟨k, by omega⟩ :: P.park e :: P.portalInv e :: ps)
      (Pcut.leave ⟨k, by omega⟩ :: Pcut.park e :: Pcut.portalInv e :: ps') := by
  obtain ⟨X, hX⟩ := leave_shape ⟨k, by omega⟩ (by simp; omega) hL
  have hX' : P.leave ⟨k, by omega⟩ = X ++ (Eblk (start ⟨k, by omega⟩) ++
      GateMirror.forward (Shadow7.leaveClose (start ⟨k, by omega⟩))) := hX
  have hC := leaveC_eq ⟨k, by omega⟩ (by simp; omega) X hX'
  have hPI : P.portalInv e = [] ++ ((P.portalInv e).take 6 ++ portalInvC e) := by
    simp only [List.nil_append, portalInvC, List.take_append_drop]
  have hPIC : Pcut.portalInv e = [] ++ portalInvC e := by
    rw [Pcut_portalInv, List.nil_append]
  have hPark : Pcut.park e = P.park e := Pcut_park e
  rw [hX', hC, hPI, hPIC, hPark]
  exact Cut.triple X _ _ (P.park e) [] _ _ (wires (Eblk (start ⟨k, by omega⟩))) (Finset.Subset.refl _) hsub
    havoid rfl mD (tc_Eblk _) tD inv h

/-- Ends of the reverse walk use the inverse window pieces. -/
theorem inv_app (a b : List GateMirror.Gate) : GateMirror.inverse (a ++ b) = GateMirror.inverse b ++ GateMirror.inverse a := by
  simp only [GateMirror.inverse, List.map_append, List.reverse_append]

/-- The reverse leave: inverse leaveClose, then the swapped block, then the rest. -/
def Dblk (s : Nat) : Program := GateMirror.inverse
  (Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1)) ++
   Partial.cswapG (s+30) (Shadow7.b0P s - 1 + Shadow7.lowsP s) (Shadow7.a0P s - 1 + Shadow7.lowsP s))

theorem tc_Dblk (s : Nat) : toffoliCount (Dblk s) = 2 := rfl

theorem unleave_shape (k : Fin 26) (hk : k.val ≤ 24) (hL : 1 ≤ Shadow7.lowsP (start k)) :
    ∃ R, CRTBarrel.params.leaveInv k = GateMirror.inverse (Shadow7.leaveClose (start k)) ++ (Dblk (start k) ++ R) := by
  obtain ⟨Z, hZ⟩ := suffix_after (start k)
  obtain ⟨V, hV⟩ := lowClose_split (start k) hL
  refine ⟨GateMirror.inverse V ++ GateMirror.inverse Z ++ CRTBarrel.barrel (start k) true ++
    GateMirror.inverse (CRTBarrel.beforeRow (start k)), ?_⟩
  show CRTBarrel.unleave k = _
  unfold CRTBarrel.unleave
  simp only [if_pos hk]
  rw [← hZ, hV]
  simp only [Dblk, inv_app, List.append_assoc]

theorem unleaveC_eq (j : Fin 26) (hj : j.val ≤ 24) (R : Program)
    (hR : P.leaveInv j = GateMirror.inverse (Shadow7.leaveClose (start j)) ++ (Dblk (start j) ++ R)) :
    Pcut.leaveInv j = GateMirror.inverse (Shadow7.leaveClose (start j)) ++ R := by
  rw [Pcut_leaveInv]
  have hD : (Dblk (start j)).length = 6 := rfl
  have hK : (GateMirror.inverse (Shadow7.leaveClose (start j))).length = K j := by
    simp only [K, GateMirror.inverse, GateMirror.forward, List.length_reverse, List.length_map]
  unfold unleaveC
  rw [if_pos hj, hR, ← hK, List.take_left' rfl]
  rw [show (GateMirror.inverse (Shadow7.leaveClose (start j))).length + 6 =
      (GateMirror.inverse (Shadow7.leaveClose (start j)) ++ Dblk (start j)).length by simp [hD]]
  rw [← List.append_assoc, List.drop_left' rfl]

/-- Reverse boundary enterInv_{k+1} → leaveInv_k. -/
theorem bnd_rev (k : Nat) (hk : k < 24)
    (htail : (P.enterInv ⟨k+1, by omega⟩).drop ((P.enterInv ⟨k+1, by omega⟩).length - 6) = Dblk (start ⟨k, by omega⟩))
    (hL : 1 ≤ Shadow7.lowsP (start ⟨k, by omega⟩))
    (havoid : ∀ q ∈ wires (Dblk (start ⟨k, by omega⟩)),
      q ∉ wires ([] ++ GateMirror.inverse (Shadow7.leaveClose (start ⟨k, by omega⟩))))
    (inv : ∀ u (a b : List Bool), run (Dblk (start ⟨k, by omega⟩)) b (run (Dblk (start ⟨k, by omega⟩)) a u) = u)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.enterInv ⟨k+1, by omega⟩ :: P.leaveInv ⟨k, by omega⟩ :: ps)
      (Pcut.enterInv ⟨k+1, by omega⟩ :: Pcut.leaveInv ⟨k, by omega⟩ :: ps') := by
  obtain ⟨R, hR⟩ := unleave_shape ⟨k, by omega⟩ (by simp; omega) hL
  have hR' : P.leaveInv ⟨k, by omega⟩ = GateMirror.inverse (Shadow7.leaveClose (start ⟨k, by omega⟩)) ++
      (Dblk (start ⟨k, by omega⟩) ++ R) := hR
  have hC := unleaveC_eq ⟨k, by omega⟩ (by simp; omega) R hR'
  have h1 : P.enterInv ⟨k+1, by omega⟩ = enterInvC ⟨k+1, by omega⟩ ++ (Dblk (start ⟨k, by omega⟩) ++ []) := by
    rw [← htail]; simp only [enterInvC, List.append_nil, List.take_append_drop]
  have h2 : Pcut.enterInv ⟨k+1, by omega⟩ = enterInvC ⟨k+1, by omega⟩ ++ [] := by
    rw [Pcut_enterInv, List.append_nil]
  rw [h1, h2, hR', hC]
  exact Cut.pair _ _ [] _ _ R (wires (Dblk (start ⟨k, by omega⟩))) (Finset.Subset.refl _) (Finset.Subset.refl _)
    havoid rfl rfl (tc_Dblk _) (tc_Dblk _) inv h

/-- Reverse exit boundary portal → parkInv → leaveInv_24. -/
theorem bnd_rev_exit (k : Nat) (hk : k ≤ 24) (e : Nat)
    (htail : (P.portal e).drop ((P.portal e).length - 6) = Eblk (start ⟨k, by omega⟩))
    (hL : 1 ≤ Shadow7.lowsP (start ⟨k, by omega⟩))
    (havoid : ∀ q ∈ wires (Eblk (start ⟨k, by omega⟩)),
      q ∉ wires ([] ++ (P.parkInv e ++ GateMirror.inverse (Shadow7.leaveClose (start ⟨k, by omega⟩)))))
    (hsub : wires (Dblk (start ⟨k, by omega⟩)) ⊆ wires (Eblk (start ⟨k, by omega⟩)))
    (inv : ∀ u (a b : List Bool), run (Dblk (start ⟨k, by omega⟩)) b (run (Eblk (start ⟨k, by omega⟩)) a u) = u)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.portal e :: P.parkInv e :: P.leaveInv ⟨k, by omega⟩ :: ps)
      (Pcut.portal e :: Pcut.parkInv e :: Pcut.leaveInv ⟨k, by omega⟩ :: ps') := by
  obtain ⟨R, hR⟩ := unleave_shape ⟨k, by omega⟩ (by simp; omega) hL
  have hR' : P.leaveInv ⟨k, by omega⟩ = GateMirror.inverse (Shadow7.leaveClose (start ⟨k, by omega⟩)) ++
      (Dblk (start ⟨k, by omega⟩) ++ R) := hR
  have hC := unleaveC_eq ⟨k, by omega⟩ (by simp; omega) R hR'
  have h1 : P.portal e = portalC e ++ (Eblk (start ⟨k, by omega⟩) ++ []) := by
    rw [← htail]; simp only [portalC, List.append_nil, List.take_append_drop]
  have h2 : Pcut.portal e = portalC e ++ [] := by
    rw [Pcut_portal, List.append_nil]
  have h3 : Pcut.parkInv e = P.parkInv e := Pcut_parkInv e
  rw [h1, h2, h3, hR', hC]
  exact Cut.triple _ _ [] (P.parkInv e) _ _ R (wires (Eblk (start ⟨k, by omega⟩))) (Finset.Subset.refl _) hsub
    havoid rfl rfl (tc_Eblk _) (tc_Dblk _) inv h

/-- Reverse end boundary enterInv_0 → portalInv. -/
theorem bnd_rev_end (j : Fin 26) (t : Nat)
    (hhead : (P.portalInv t).take 6 = (P.enterInv j).drop ((P.enterInv j).length - 6))
    (inv : ∀ u (a b : List Bool), run ((P.enterInv j).drop ((P.enterInv j).length - 6)) b
      (run ((P.enterInv j).drop ((P.enterInv j).length - 6)) a u) = u)
    (m0 : measurementCount ((P.enterInv j).drop ((P.enterInv j).length - 6)) = 0)
    (t0 : toffoliCount ((P.enterInv j).drop ((P.enterInv j).length - 6)) = 2)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.enterInv j :: P.portalInv t :: ps) (Pcut.enterInv j :: Pcut.portalInv t :: ps') := by
  have h1 : P.enterInv j = enterInvC j ++ ((P.enterInv j).drop ((P.enterInv j).length - 6) ++ []) := by
    simp only [enterInvC, List.append_nil, List.take_append_drop]
  have h2 : Pcut.enterInv j = enterInvC j ++ [] := by
    rw [Pcut_enterInv, List.append_nil]
  have h3 : P.portalInv t = [] ++ ((P.enterInv j).drop ((P.enterInv j).length - 6) ++ portalInvC t) := by
    rw [← hhead]; simp only [List.nil_append, portalInvC, List.take_append_drop]
  have h4 : Pcut.portalInv t = [] ++ portalInvC t := by
    rw [Pcut_portalInv, List.nil_append]
  rw [h1, h2, h3, h4]
  exact Cut.pair _ _ [] [] _ _ (wires ((P.enterInv j).drop ((P.enterInv j).length - 6))) (Finset.Subset.refl _)
    (Finset.Subset.refl _) (by intro q _; simp [wires]) m0 m0 t0 t0 inv h


/-! ## List-based wire checks (cheap kernel decides) -/

def cwl : List Correction → List Wire
  | [] => []
  | .Z t :: cs => t :: cwl cs
  | .CZ a b :: cs => a :: b :: cwl cs

def iwl : Instr → List Wire
  | .X t => [t]
  | .CX c t => [c, t]
  | .CCX a b t => [a, b, t]
  | .measureX t c0 c1 => t :: (cwl c0 ++ cwl c1)

def wl : Program → List Wire
  | [] => []
  | i :: p => iwl i ++ wl p

theorem mem_cwl (q : Wire) (cs : List Correction) : q ∈ correctionWires cs ↔ q ∈ cwl cs := by
  induction cs with
  | nil => simp [correctionWires, cwl]
  | cons c cs ih => cases c <;> simp [correctionWires, cwl, ih]

theorem mem_iwl (q : Wire) (i : Instr) : q ∈ i.wires ↔ q ∈ iwl i := by
  cases i <;> simp [Instr.wires, iwl, mem_cwl, or_assoc]

theorem mem_wl (q : Wire) (P : Program) : q ∈ wires P ↔ q ∈ wl P := by
  induction P with
  | nil => simp [wires, wl]
  | cons i p ih => simp [wires, wl, mem_iwl, ih]

theorem avoid_of_check (E M : Program) (h : (wl E).all (fun q => !((wl M).contains q)) = true) :
    ∀ q ∈ wires E, q ∉ wires M := by
  intro q hq hm
  rw [mem_wl] at hq hm
  have h1 := List.all_eq_true.mp h q hq
  have h2 : q ∉ wl M := by simpa using h1
  exact h2 hm

theorem sub_of_check (D E : Program) (h : (wl D).all (fun q => (wl E).contains q) = true) :
    wires D ⊆ wires E := by
  intro q hq
  rw [mem_wl] at hq ⊢
  have h1 := List.all_eq_true.mp h q hq
  simpa using h1

/-! ## Block facts -/

def dist5 (c a b a' b' : Wire) : Prop :=
  c ≠ a ∧ c ≠ b ∧ a ≠ b ∧ c ≠ a' ∧ c ≠ b' ∧ a' ≠ b' ∧ a ≠ a' ∧ a ≠ b' ∧ b ≠ a' ∧ b ≠ b'

instance (c a b a' b' : Wire) : Decidable (dist5 c a b a' b') := by unfold dist5; infer_instance

theorem inv_of_eq (X : Program) (c a b a' b' : Wire) (hX : X = S2 c a b a' b') (hd : dist5 c a b a' b') :
    ∀ t (m1 m2 : List Bool), run X m2 (run X m1 t) = t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hd
  intro t m1 m2; subst hX; exact S2_inv c a b a' b' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 t m1 m2

theorem inv_swap_of_eq (X Y : Program) (c a b a' b' : Wire) (hX : X = S2 c a b a' b') (hY : Y = S2 c a' b' a b)
    (hd : dist5 c a b a' b') : ∀ t (m1 m2 : List Bool), run Y m2 (run X m1 t) = t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hd
  intro t m1 m2; subst hX; subst hY; exact S2_inv_swap c a b a' b' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 t m1 m2

theorem S2_measure0 (X : Program) (c a b a' b' : Wire) (hX : X = S2 c a b a' b') : measurementCount X = 0 := by
  subst hX; rfl

theorem Dblk_S2 (s : Nat) : Dblk s = S2 (s+30) (Shadow7.b0P s - 1 + Shadow7.lowsP s) (Shadow7.a0P s - 1 + Shadow7.lowsP s)
    (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1)) := rfl

theorem rest7_eq : WindowParams7.rest7 = ([⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩] : List (Fin 26)) := by
  decide

set_option maxHeartbeats 4000000 in
theorem fwd_cut (d : Bool) :
    Cut 26 (WindowFold.forwardL P d WindowParams.first WindowParams7.rest7)
      (WindowFold.forwardL Pcut d WindowParams.first WindowParams7.rest7) := by
  rw [rest7_eq]
  simp only [WindowFold.forwardL, WindowFold.firstF, WindowFold.chainF, WindowFold.nextF, WindowFold.exitF,
    List.cons_append, List.nil_append]
  apply bnd_portal (start WindowParams.first) WindowParams.first (by decide +kernel)
    (inv_of_eq _ 60 1028 303 1029 304 (by decide +kernel) (by decide +kernel))
    (S2_measure0 _ 60 1028 303 1029 304 (by decide +kernel)) (by decide +kernel)
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 0 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 1 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 2 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 3 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 4 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 5 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 6 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 7 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 8 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 9 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 10 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 11 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 12 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 13 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 14 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 15 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 16 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 17 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 18 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 19 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 20 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 21 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 22 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 23 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_exit 24 (by decide) _ (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (sub_of_check _ _ (by decide +kernel))
    (inv_swap_of_eq _ _ 435 841 491 842 492 (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (S2_measure0 _ 435 842 492 841 491 (by decide +kernel)) (by decide +kernel)
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  exact Cut.nil

set_option maxHeartbeats 4000000 in
theorem rev_cut (d : Bool) :
    Cut 26 (WindowFold.reverseL P d WindowParams.first WindowParams7.rest7)
      (WindowFold.reverseL Pcut d WindowParams.first WindowParams7.rest7) := by
  rw [rest7_eq]
  simp only [WindowFold.reverseL, WindowFold.exitR, WindowFold.chainR, WindowFold.nextR, WindowFold.firstR,
    List.cons_append, List.nil_append, List.append_assoc]
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev_exit 24 (by decide) _ (by decide +kernel) (by decide +kernel)
    (avoid_of_check _ _ (by decide +kernel)) (sub_of_check _ _ (by decide +kernel)) (inv_swap_of_eq _ _ _ _ _ _ _ (Eblk_S2 _) (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 23 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 22 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 21 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 20 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 19 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 18 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 17 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 16 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 15 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 14 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 13 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 12 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 11 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 10 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 9 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 8 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 7 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 6 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 5 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 4 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 3 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 2 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 1 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 0 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev_end WindowParams.first (start WindowParams.first) (by decide +kernel)
    (inv_of_eq _ 60 1029 304 1028 303 (by decide +kernel) (by decide +kernel))
    (S2_measure0 _ 60 1029 304 1028 303 (by decide +kernel)) (by decide +kernel)
  exact Cut.nil


/-! ## Per-piece count deltas (for the ledger) -/

theorem tc_S2 (c a b a' b' : Wire) : toffoliCount (S2 c a b a' b') = 2 := rfl

theorem tail_counts (X : Program) (hE : ∃ c a b a' b', X.drop (X.length - 6) = S2 c a b a' b') :
    toffoliCount X = toffoliCount (X.take (X.length - 6)) + 2 ∧
      measurementCount X = measurementCount (X.take (X.length - 6)) := by
  obtain ⟨c, a, b, a', b', h⟩ := hE
  have e := List.take_append_drop (X.length - 6) X
  have t1 : toffoliCount X = toffoliCount (X.take (X.length - 6)) + toffoliCount (X.drop (X.length - 6)) := by
    rw [← toffoliCount_append, e]
  have m1 : measurementCount X = measurementCount (X.take (X.length - 6)) +
      measurementCount (X.drop (X.length - 6)) := by
    rw [← measurementCount_append, e]
  rw [h, tc_S2] at t1
  rw [h, S2_measure0 _ c a b a' b' rfl] at m1
  exact ⟨t1, by omega⟩

theorem head_counts (X : Program) (hE : ∃ c a b a' b', X.take 6 = S2 c a b a' b') :
    toffoliCount X = toffoliCount (X.drop 6) + 2 ∧ measurementCount X = measurementCount (X.drop 6) := by
  obtain ⟨c, a, b, a', b', h⟩ := hE
  have e := List.take_append_drop 6 X
  have t1 : toffoliCount X = toffoliCount (X.take 6) + toffoliCount (X.drop 6) := by
    rw [← toffoliCount_append, e]
  have m1 : measurementCount X = measurementCount (X.take 6) + measurementCount (X.drop 6) := by
    rw [← measurementCount_append, e]
  rw [h, tc_S2] at t1
  rw [h, S2_measure0 _ c a b a' b' rfl] at m1
  exact ⟨by omega, by omega⟩


theorem enter_counts (j : Fin 26) (hE : ∃ c a b a' b', (P.enter j).take 6 = S2 c a b a' b') :
    toffoliCount (P.enter j) = toffoliCount (Pcut.enter j) + 2 ∧
      measurementCount (P.enter j) = measurementCount (Pcut.enter j) := by
  rw [Pcut_enter, enterC]
  exact head_counts _ hE

theorem leave_counts (k : Fin 26) (hk : k.val ≤ 24) (hL : 1 ≤ Shadow7.lowsP (start k)) :
    toffoliCount (P.leave k) = toffoliCount (Pcut.leave k) + 2 ∧
      measurementCount (P.leave k) = measurementCount (Pcut.leave k) := by
  obtain ⟨X, hX⟩ := leave_shape k hk hL
  have hX' : P.leave k = X ++ (Eblk (start k) ++ GateMirror.forward (Shadow7.leaveClose (start k))) := hX
  rw [leaveC_eq k hk X hX', hX']
  simp only [toffoliCount_append, measurementCount_append, Eblk_S2, tc_S2,
    S2_measure0 _ _ _ _ _ _ rfl]
  constructor <;> omega

theorem leaveInv_counts (k : Fin 26) (hk : k.val ≤ 24) (hL : 1 ≤ Shadow7.lowsP (start k)) :
    toffoliCount (P.leaveInv k) = toffoliCount (Pcut.leaveInv k) + 2 ∧
      measurementCount (P.leaveInv k) = measurementCount (Pcut.leaveInv k) := by
  obtain ⟨R, hR⟩ := unleave_shape k hk hL
  have hR' : P.leaveInv k = GateMirror.inverse (Shadow7.leaveClose (start k)) ++ (Dblk (start k) ++ R) := hR
  rw [unleaveC_eq k hk R hR', hR']
  simp only [toffoliCount_append, measurementCount_append, Dblk_S2, tc_S2,
    S2_measure0 _ _ _ _ _ _ rfl]
  constructor <;> omega

/-- FRED-CUT on the window walk: the cut walk has the same run as the original, for every state and tape. -/
theorem walk_run_eq (d : Bool) (m : List Bool) (s : State) :
    run (WindowFold.forwardW Pcut d WindowParams.first WindowParams7.rest7) m s =
      run (WindowFold.forwardW P d WindowParams.first WindowParams7.rest7) m s :=
  (fwd_cut d).run_eq m s

theorem walk_run_eq_rev (d : Bool) (m : List Bool) (s : State) :
    run (WindowFold.reverseW Pcut d WindowParams.first WindowParams7.rest7) m s =
      run (WindowFold.reverseW P d WindowParams.first WindowParams7.rest7) m s :=
  (rev_cut d).run_eq m s


theorem walk_mc_eq (d : Bool) :
    measurementCount (WindowFold.forwardW Pcut d WindowParams.first WindowParams7.rest7) =
      measurementCount (WindowFold.forwardW P d WindowParams.first WindowParams7.rest7) :=
  (fwd_cut d).mc_eq

theorem walk_mc_eq_rev (d : Bool) :
    measurementCount (WindowFold.reverseW Pcut d WindowParams.first WindowParams7.rest7) =
      measurementCount (WindowFold.reverseW P d WindowParams.first WindowParams7.rest7) :=
  (rev_cut d).mc_eq

theorem walk_wires_sub (d : Bool) :
    wires (WindowFold.forwardW Pcut d WindowParams.first WindowParams7.rest7) ⊆
      wires (WindowFold.forwardW P d WindowParams.first WindowParams7.rest7) :=
  (fwd_cut d).wires_sub

theorem walk_wires_sub_rev (d : Bool) :
    wires (WindowFold.reverseW Pcut d WindowParams.first WindowParams7.rest7) ⊆
      wires (WindowFold.reverseW P d WindowParams.first WindowParams7.rest7) :=
  (rev_cut d).wires_sub

end ECDSAAdd.Entrant.StairPacket.FredCut

/-! ## The caller's CRT window, with every boundary swap pair cancelled -/

section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams

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

theorem cut_slotsF : gateSlots (forwardCut true) ≤ 2370994 ∧ gateSlots (forwardCut false) ≤ 2370994 :=
  ⟨(FredCut.fwd_cut true).slots_le.trans ship_slots.1, (FredCut.fwd_cut false).slots_le.trans ship_slots.2.1⟩

theorem cut_slotsR : gateSlots (reverseCut true) ≤ 2334224 ∧ gateSlots (reverseCut false) ≤ 2334224 :=
  ⟨(FredCut.rev_cut true).slots_le.trans ship_slots.2.2.1, (FredCut.rev_cut false).slots_le.trans ship_slots.2.2.2⟩

theorem cut_toffoliF : toffoliCount (forwardCut true) = 127882 ∧ toffoliCount (forwardCut false) = 127882 := by
  have a := (cut_toffoli true).1
  have b := (cut_toffoli false).1
  rw [ship_toffoliF_true] at a
  rw [ship_toffoliF_false] at b
  exact ⟨by omega, by omega⟩

theorem cut_toffoliR : toffoliCount (reverseCut true) = 128299 ∧ toffoliCount (reverseCut false) = 128324 := by
  have a := (cut_toffoli true).2
  have b := (cut_toffoli false).2
  rw [ship_toffoliR_true] at a
  rw [ship_toffoliR_false] at b
  exact ⟨by omega, by omega⟩

theorem cut_measureF : measurementCount (forwardCut true) = 66344 ∧ measurementCount (forwardCut false) = 66344 := by
  rw [(cut_measure true).1, (cut_measure false).1]
  exact ship_measureF

theorem cut_measureR : measurementCount (reverseCut true) = 65626 ∧ measurementCount (reverseCut false) = 65651 := by
  rw [(cut_measure true).2, (cut_measure false).2]
  exact ship_measureR

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end
