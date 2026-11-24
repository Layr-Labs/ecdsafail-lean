import ECDSAAdd.Submission.Entrant.LeaveReductions
import ECDSAAdd.Framework.RecordedPaths
import ECDSAAdd.Framework.MeasuredLocality

/-!
# Window boundary swap-pair cancellation

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

-- ==== the packet-cut lemmas (carried in this module so the replay holds one module environment fewer) ====
namespace ECDSAAdd.Entrant.PackCutTrip
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.MeasuredCodec5

/-- The due-tick encode without its trailing `ep`. -/
def E138 : Program := (Rolling1588.codeEncode true).take 138

theorem E138_ep : Rolling1588.codeEncode true = E138 ++ Rolling1588.ep := by
  unfold E138; rw [show Rolling1588.ep = (Rolling1588.codeEncode true).drop 138 by decide]
  exact (List.take_append_drop _ _).symm

set_option maxRecDepth 100000 in
theorem finite_trip : ∀ x < 1024, legalNat x = true →
    (safe E138 x && safe Rolling1588.ep (bitRun E138 x) &&
      safe Rolling1588.dp (bitRun Rolling1588.ep (bitRun E138 x)) &&
      (bitRun Rolling1588.dp (bitRun Rolling1588.ep (bitRun E138 x)) == bitRun E138 x)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem supp : wires E138 ⊆ Finset.range 10 ∧ wires Rolling1588.ep ⊆ Finset.range 10 ∧
    wires Rolling1588.dp ⊆ Finset.range 10 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Local partial trip: on a legal ten-wire word, `dp` undoes `ep` after the shortened encode,
for every tape. -/
theorem local_trip (t : State) (h : legal t.basis) (m0 me md : List Bool) :
    run Rolling1588.dp md (run Rolling1588.ep me (run E138 m0 t)) = run E138 m0 t := by
  obtain ⟨x, hx, lx, hb⟩ := local_word t h
  have fin := finite_trip x hx lx
  simp only [Bool.and_eq_true, beq_iff_eq] at fin
  obtain ⟨⟨⟨s1, s2⟩, s3⟩, e4⟩ := fin
  let u : State := ⟨t.phase, bitsOf x⟩
  -- local runs from u
  have r1 : run E138 m0 u = ⟨t.phase, bitsOf (bitRun E138 x)⟩ := by
    rw [run_sim, sim_safe E138 x s1]
  have r2 : run Rolling1588.ep me (run E138 m0 u) =
      ⟨t.phase, bitsOf (bitRun Rolling1588.ep (bitRun E138 x))⟩ := by
    rw [r1, run_sim, sim_safe _ _ s2]
  have r3 : run Rolling1588.dp md (run Rolling1588.ep me (run E138 m0 u)) = run E138 m0 u := by
    rw [r2, run_sim, sim_safe _ _ s3, e4, r1]
  -- transfer from u to t by locality on the ten wires
  have agree0 : ∀ q ∈ Finset.range 10, t.basis q = u.basis q := fun q hq => hb q hq
  have l1 := run_measured_locality E138 (Finset.range 10) supp.1 t u m0 rfl agree0
  have l2 := run_measured_locality Rolling1588.ep (Finset.range 10) supp.2.1 _ _ me l1.1 l1.2
  have l3 := run_measured_locality Rolling1588.dp (Finset.range 10) supp.2.2 _ _ md l2.1 l2.2
  rw [r3] at l3
  apply State.extensionality
  · exact l3.1.trans l1.1.symm
  · funext q
    by_cases hq : q ∈ Finset.range 10
    · exact (l3.2 q hq).trans (l1.2 q hq).symm
    · rw [run_preserves_outside _ md _ q (fun hh => hq (supp.2.2 hh)),
        run_preserves_outside _ me _ q (fun hh => hq (supp.2.1 hh))]

/-- Placed partial trip (any injective ten-wire placement with legal letters). -/
theorem placed_trip (f : Fin 10 → Wire) (hf : Function.Injective f) (s : State)
    (h : legalAt f s.basis) (m0 me md : List Bool) :
    run (renameProgram (label f) Rolling1588.dp) md
      (run (renameProgram (label f) Rolling1588.ep) me (run (renameProgram (label f) E138) m0 s)) =
      run (renameProgram (label f) E138) m0 s := by
  have inj := FirstNonzeroCodec.label_inj' f hf
  let t : State := ⟨s.phase, fun q => s.basis (label f q)⟩
  have p1 := run_rename_pool (label f) (Finset.range 10) inj E138 supp.1 m0 t s rfl (fun _ _ => rfl)
  let A := run (renameProgram (label f) E138) m0 s
  let Al := run E138 m0 t
  have p2 := run_rename_pool (label f) (Finset.range 10) inj Rolling1588.ep supp.2.1 me Al A
    p1.1.symm (fun q hq => (p1.2 q hq).symm)
  have p3 := run_rename_pool (label f) (Finset.range 10) inj Rolling1588.dp supp.2.2 md
    (run Rolling1588.ep me Al) (run (renameProgram (label f) Rolling1588.ep) me A)
    p2.1.symm (fun q hq => (p2.2 q hq).symm)
  have lt := local_trip t h m0 me md
  have suppE := renameProgram_support (label f) E138
  have suppP := renameProgram_support (label f) Rolling1588.ep
  have suppD := renameProgram_support (label f) Rolling1588.dp
  apply State.extensionality
  · exact p3.1.trans ((congrArg State.phase lt).trans p1.1.symm)
  · funext q
    by_cases hq : q ∈ (Finset.range 10).image (label f)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact (p3.2 i hi).trans ((congrArg (fun st : State => st.basis i) lt).trans (p1.2 i hi).symm)
    · have nE : q ∉ wires (renameProgram (label f) Rolling1588.ep) := by
        rw [suppP]; intro hh; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
        exact hq (Finset.mem_image.mpr ⟨i, supp.2.1 hi, rfl⟩)
      have nD : q ∉ wires (renameProgram (label f) Rolling1588.dp) := by
        rw [suppD]; intro hh; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
        exact hq (Finset.mem_image.mpr ⟨i, supp.2.2 hi, rfl⟩)
      rw [run_preserves_outside _ md _ q nD, run_preserves_outside _ me _ q nE]

end ECDSAAdd.Entrant.PackCutTrip


namespace ECDSAAdd.Entrant.PackCutRow
open ECDSAAdd ECDSAAdd.RecordedQuantum

private theorem xx (p q : Bool) : ((p ^^ q) ^^ q) = p := by cases p <;> cases q <;> rfl
private theorem xxxx (p q w : Bool) : ((((p ^^ q) ^^ w) ^^ p) ^^ q) = w := by
  cases p <;> cases q <;> cases w <;> rfl

/-- An encode tail `E` and a decode head `D` acting only on `W`, around a middle `M` that never touches
`W`: if `D` undoes `E` at `x`, then `E; M; D` acts as `M` alone at `x` (basis and phase, given tapes). -/
theorem cancel_around (E M D : Program) (W : Finset Wire)
    (hE : wires E ⊆ W) (hD : wires D ⊆ W) (hM : ∀ q ∈ W, q ∉ wires M)
    (x : State) (me mm md : List Bool)
    (trip : run D md (run E me x) = x) :
    run D md (run M mm (run E me x)) = run M mm x := by
  -- y : after the encode tail
  have h1 : ∀ q, q ∉ W → (run E me x).basis q = x.basis q := fun q hq =>
    run_preserves_outside E me x q (fun h => hq (hE h))
  let y := run E me x
  let a := y.phase ^^ x.phase
  let y' : State := ⟨x.phase, y.basis⟩
  have hy : y = shiftPhase a y' := by
    apply State.extensionality
    · exact (xx y.phase x.phase).symm
    · rfl
  let u := run M mm y'
  let w := run M mm x
  have loc2 := run_measured_locality M (wires M) (Finset.Subset.refl _) y' x mm rfl
    (fun q hq => h1 q (fun hw => hM q hw hq))
  have hz : run M mm y = shiftPhase a u := by rw [hy]; exact run_shift M mm a y'
  -- z : after the middle; it agrees with y on W
  let z := run M mm y
  have hzW : ∀ q ∈ W, z.basis q = y.basis q := by
    intro q hq
    show (run M mm y).basis q = y.basis q
    exact run_preserves_outside M mm y q (hM q hq)
  let b := z.phase ^^ y.phase
  let z' : State := ⟨y.phase, z.basis⟩
  have hz' : z = shiftPhase b z' := by
    apply State.extensionality
    · exact (xx z.phase y.phase).symm
    · rfl
  have loc3 := run_measured_locality D W hD z' y md rfl (fun q hq => hzW q hq)
  have hr : run D md z = shiftPhase b (run D md z') := by rw [hz']; exact run_shift D md b z'
  rw [trip] at loc3
  change run D md z = w
  rw [hr]
  apply State.extensionality
  · -- phases
    have hzp : z.phase = (a ^^ u.phase) := by
      show (run M mm y).phase = _
      rw [hz]; rfl
    show (b ^^ (run D md z').phase) = w.phase
    rw [loc3.1]
    show ((z.phase ^^ y.phase) ^^ x.phase) = w.phase
    rw [hzp, loc2.1]
    exact xxxx y.phase x.phase w.phase
  · funext q
    show (run D md z').basis q = w.basis q
    by_cases hq : q ∈ W
    · rw [loc3.2 q hq]
      exact (run_preserves_outside M mm x q (hM q hq)).symm
    · rw [run_preserves_outside D md z' q (fun h => hq (hD h))]
      show z.basis q = w.basis q
      have hzu : z.basis q = u.basis q := by
        show (run M mm y).basis q = _
        rw [hz]; rfl
      rw [hzu]
      by_cases hm : q ∈ wires M
      · exact loc2.2 q hm
      · rw [run_preserves_outside M mm y' q hm, run_preserves_outside M mm x q hm]
        exact h1 q hq

theorem run_app_exact (X Y : Program) (tX tY : List Bool) (h : tX.length = measurementCount X)
    (s : State) : run (X ++ Y) (tX ++ tY) s = run Y tY (run X tX s) := by
  rw [run_append, ← h, List.take_left' rfl, List.drop_left' rfl]

/-- PACK-CUT row: deleting an encode tail `E` and its decode head `D` around a middle `M` that never
touches their wires gives, on every tape, the run of the original row on some tape, provided `D`
undoes `E` after `A` (for every tape of `A`, `E` and `D`). -/
theorem row_cut (A E M D B : Program) (W : Finset Wire)
    (hE : wires E ⊆ W) (hD : wires D ⊆ W) (hM : ∀ q ∈ W, q ∉ wires M)
    (s : State) (m : List Bool)
    (trip : ∀ tA me md, run D md (run E me (run A tA s)) = run A tA s) :
    ∃ m', run (A ++ M ++ B) m s = run (A ++ E ++ M ++ D ++ B) m' s := by
  let n := measurementCount A + measurementCount M + measurementCount B
  let p := m ++ List.replicate n false
  let pA := p.take (measurementCount A)
  let pM := (p.drop (measurementCount A)).take (measurementCount M)
  let pB := (p.drop (measurementCount A)).drop (measurementCount M)
  have lenA : pA.length = measurementCount A := by
    simp only [pA, List.length_take, p, List.length_append, List.length_replicate, n]; omega
  have lenM : pM.length = measurementCount M := by
    simp only [pM, List.length_take, List.length_drop, p, List.length_append, List.length_replicate, n]
    omega
  have hp : p = pA ++ (pM ++ pB) := by
    simp only [pA, pM, pB, List.take_append_drop]
  let rE := List.replicate (measurementCount E) false
  let rD := List.replicate (measurementCount D) false
  refine ⟨pA ++ (rE ++ (pM ++ (rD ++ pB))), ?_⟩
  have hcut : run (A ++ M ++ B) m s = run B pB (run M pM (run A pA s)) := by
    rw [← run_pad_false (A ++ M ++ B) m n s]
    change run (A ++ M ++ B) p s = _
    rw [hp, List.append_assoc, run_app_exact A (M ++ B) pA (pM ++ pB) lenA,
      run_app_exact M B pM pB lenM]
  have hold : run (A ++ E ++ M ++ D ++ B) (pA ++ (rE ++ (pM ++ (rD ++ pB)))) s =
      run B pB (run D rD (run M pM (run E rE (run A pA s)))) := by
    simp only [List.append_assoc]
    rw [run_app_exact A _ pA _ lenA, run_app_exact E _ rE _ (by simp [rE]),
      run_app_exact M _ pM _ lenM, run_app_exact D _ rD _ (by simp [rD])]
  rw [hcut, hold, cancel_around E M D W hE hD hM (run A pA s) rE pM rD (trip pA rE rD)]

end ECDSAAdd.Entrant.PackCutRow




namespace ECDSAAdd.Entrant.PackCutShape
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed

theorem movedForward_add (w : Nat → Wire) (i a b : Nat) :
    StairReplay.movedForward w i (a + b) =
      StairReplay.movedForward w i a ++ StairReplay.movedForward w (i + a) b := by
  induction a generalizing i with
  | zero => simp [StairReplay.movedForward]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [StairReplay.movedForward, ih (i + 1), List.append_assoc]
    rw [show i + 1 + a = i + (a + 1) by omega]

/-- Expose tick `i + k` of a moved forward run. -/
theorem movedForward_at (w : Nat → Wire) (i k b : Nat) :
    StairReplay.movedForward w i (k + 1 + b) =
      StairReplay.movedForward w i k ++
        ((ECDSAAdd.Entrant.TickRanges.tick w (i + k) ++
          Rolling1588.Integer.packFirst w true (i + k)) ++
          StairReplay.movedForward w (i + k + 1) b) := by
  rw [movedForward_add w i (k + 1) b, movedForward_add w i k 1]
  simp only [StairReplay.movedForward, List.append_nil, List.append_assoc]
  rw [show i + (k + 1) = i + k + 1 by omega]

/-- At a due tick (not the first packet) the moved write is the placed code encode. -/
theorem packFirst_due (w : Nat → Wire) (i : Nat) (h5 : i ≠ 5) (hdue : History5.packDue i = true)
    (hs : i - 5 ≠ 0) :
    Rolling1588.Integer.packFirst w true i =
      Rolling1588.codeEncodeAt true (History5.historyMap w (i - 5)) := by
  simp only [Rolling1588.Integer.packFirst, h5, if_false, Rolling1588.Integer.packAfter, hdue,
    if_true, Rolling1588.Integer.encode, hs, Rolling1588.encodeAt]

theorem program_true_head (p : Nat → Program) (j c : Nat) :
    PacketSequence.program true p j (c + 1) = p j ++ PacketSequence.program true p (j + 1) c := by
  simp [PacketSequence.program]

theorem program_false_tail (p : Nat → Program) (j c : Nat) :
    PacketSequence.program false p j (c + 1) = PacketSequence.program false p (j + 1) c ++ p j := by
  simp [PacketSequence.program]

theorem rename_app (f : Wire → Wire) (P Q : Program) :
    renameProgram f (P ++ Q) = renameProgram f P ++ renameProgram f Q := by
  simp [renameProgram, List.map_append]

theorem rebindMany_append (rs hs : List Wire) (P Q : Program) :
    StairLoan.rebindMany rs hs (P ++ Q) = StairLoan.rebindMany rs hs P ++ StairLoan.rebindMany rs hs Q := by
  induction rs generalizing hs with
  | nil => simp [StairLoan.rebindMany]
  | cons r rs ih =>
    cases hs with
    | nil => simp [StairLoan.rebindMany]
    | cons h hs => simp only [StairLoan.rebindMany, ih, rename_app]

/-- The entry packet without its leading decode head `dp`. -/
def basePacketTail (d j : Nat) : Program :=
  Rolling1588.onPacket j ParityCodec5New.untwist ++
    (StairGroups.cell true d j 3 2 ++ StairGroups.cell true d j 4 2 ++
      Rolling1588.onPacket j Rolling1588.bridge7 ++
      StairGroups.cell true d j 4 2 ++ StairGroups.cell true d j 3 2 ++
      Rolling1588.onPacket j Rolling1588.bridge5 ++ StairGroups.cell true d j 4 2) ++
    Rolling1588.onPacket j (ParityCodec5New.twist ++ Rolling1588.ep)

theorem basePacket_true_head (d j : Nat) :
    StairGroups.basePacket true d j = Rolling1588.onPacket j Rolling1588.dp ++ basePacketTail d j := by
  simp only [StairGroups.basePacket, basePacketTail, if_true, Rolling1588.onPacket, rename_app,
    List.append_assoc]

open ECDSAAdd.Arithmetic.MappedCompressed in
/-- Entry group head: a hosted entry group starts with the renamed `dp` of its first packet. -/
theorem hostedGroup_true_head (hp : StairHostsSchedule.HostPlan) (d first c : Nat) :
    StairHostsSchedule.hostedGroup hp true d first (c + 1) =
      StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d) (hp.group true d first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.dp))) ++
      StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d) (hp.group true d first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (basePacketTail d first)) ++
         renameProgram (OB5.sig 511) (StairGroups.groups true d (first + 1) c)) := by
  simp only [StairHostsSchedule.hostedGroup, StairSchedule.placedGroups, StairConcrete.bestLoans,
    StairGroups.groups, program_true_head, StairGroups.packet, basePacket_true_head, rename_app,
    rebindMany_append, List.append_assoc]

/-- Entry row shape: the forward segment is `A ++ ep′ ++ M`, with `ep′` the placed codec tail of the
due-tick encode for packet `first` (tick `i* = 5·first+5`). -/
theorem forwardSegment_row (B N s f first : Nat)
    (h1 : s + 1 ≤ 5 * first + 5) (h2 : 5 * first + 5 + 1 ≤ f)
    (h5 : 5 * first + 5 ≠ 5) (hdue : History5.packDue (5 * first + 5) = true) (hf : first ≠ 0) :
    let p := StairConcreteAssembly.checkpointPrimitives
    let w := StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))
    let F := History5.historyMap w (5 * first)
    StairSchedule.forwardSegment p B N s f =
      (p.unpack B ++ p.tickForward s ++
        StairReplay.movedForward w (s + 1) (5 * first + 5 - (s + 1)) ++
        (TickRanges.tick w (5 * first + 5) ++ renameProgram (MeasuredCodec5.label F) PackCutTrip.E138)) ++
      renameProgram (MeasuredCodec5.label F) Rolling1588.ep ++
      (StairReplay.movedForward w (5 * first + 5 + 1) (f - (5 * first + 5) - 1) ++ p.orient f ++
        renameProgram (OB5.sig f) (Rolling1588.Integer.packFirst base true f) ++ p.pack N) := by
  intro p w F
  have hmid : p.middleForward (s + 1) (f - s - 1) = StairReplay.movedForward w (s + 1) (f - s - 1) := rfl
  have hsplit : f - s - 1 = (5 * first + 5 - (s + 1)) + 1 + (f - (5 * first + 5) - 1) := by omega
  have hidx : s + 1 + (5 * first + 5 - (s + 1)) = 5 * first + 5 := by omega
  have hpf := packFirst_due w (5 * first + 5) h5 hdue (by omega)
  have henc : Rolling1588.codeEncodeAt true (History5.historyMap w (5 * first + 5 - 5)) =
      renameProgram (MeasuredCodec5.label F) PackCutTrip.E138 ++
        renameProgram (MeasuredCodec5.label F) Rolling1588.ep := by
    rw [show 5 * first + 5 - 5 = 5 * first by omega]
    simp only [Rolling1588.codeEncodeAt, PackCutTrip.E138_ep, rename_app, F]
  simp only [StairSchedule.forwardSegment, hmid]
  rw [hsplit, movedForward_at, hidx, hpf, henc]
  simp only [List.append_assoc]

end ECDSAAdd.Entrant.PackCutShape



namespace ECDSAAdd.Entrant.PackCutEntry
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open PackCutRow PackCutShape PackCutTrip

/-- One entry row: the forward segment and the hosted group after it, with the packet-`first`
encode tail and decode head deleted. -/
def cutRow (B N s f d first c : Nat) : Program :=
  let p := StairConcreteAssembly.checkpointPrimitives
  let w := StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))
  let F := History5.historyMap w (5 * first)
  let hp := StairConcreteAssembly.hostPlan
  (p.unpack B ++ p.tickForward s ++
      StairReplay.movedForward w (s + 1) (5 * first + 5 - (s + 1)) ++
      (TickRanges.tick w (5 * first + 5) ++ renameProgram (MeasuredCodec5.label F) E138)) ++
    (StairReplay.movedForward w (5 * first + 5 + 1) (f - (5 * first + 5) - 1) ++ p.orient f ++
      renameProgram (OB5.sig f) (Rolling1588.Integer.packFirst base true f) ++ p.pack N) ++
    StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d) (hp.group true d first (c + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
        (basePacketTail d first)) ++
       renameProgram (OB5.sig 511) (StairGroups.groups true d (first + 1) c))

theorem entry_row_cut (B N s f d first c : Nat)
    (h1 : s + 1 ≤ 5 * first + 5) (h2 : 5 * first + 5 + 1 ≤ f)
    (h5 : 5 * first + 5 ≠ 5) (hdue : History5.packDue (5 * first + 5) = true) (hf0 : first ≠ 0)
    (hF : Function.Injective (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first)))
    (hdp : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
        (StairConcreteAssembly.hostPlan.group true d first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.dp))) =
      renameProgram (MeasuredCodec5.label (History5.historyMap
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first)))
        Rolling1588.dp)
    (hdisj : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first))),
      q ∉ wires (StairReplay.movedForward
          (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1)))
          (5 * first + 5 + 1) (f - (5 * first + 5) - 1) ++
        StairConcreteAssembly.checkpointPrimitives.orient f ++
        renameProgram (OB5.sig f) (Rolling1588.Integer.packFirst base true f) ++
        StairConcreteAssembly.checkpointPrimitives.pack N))
    (x0 : State)
    (hlegal : ∀ t1, MeasuredCodec5.legalAt (History5.historyMap
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first))
      (run (StairConcreteAssembly.checkpointPrimitives.unpack B ++
          StairConcreteAssembly.checkpointPrimitives.tickForward s ++
          StairReplay.movedForward
            (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1)))
            (s + 1) (5 * first + 5 - (s + 1)) ++
          TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1)))
            (5 * first + 5)) t1 x0).basis)
    (m : List Bool) :
    ∃ m', run (cutRow B N s f d first c) m x0 =
      run (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives B N s f ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true d first (c + 1)) m' x0 := by
  set w := StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1)) with hw
  set F := History5.historyMap w (5 * first) with hFdef
  set p := StairConcreteAssembly.checkpointPrimitives with hpdef
  let A0 := p.unpack B ++ p.tickForward s ++ StairReplay.movedForward w (s + 1) (5 * first + 5 - (s + 1)) ++
    TickRanges.tick w (5 * first + 5)
  let E138' := renameProgram (MeasuredCodec5.label F) E138
  let ep' := renameProgram (MeasuredCodec5.label F) Rolling1588.ep
  let dp' := renameProgram (MeasuredCodec5.label F) Rolling1588.dp
  let Mrow := StairReplay.movedForward w (5 * first + 5 + 1) (f - (5 * first + 5) - 1) ++ p.orient f ++
    renameProgram (OB5.sig f) (Rolling1588.Integer.packFirst base true f) ++ p.pack N
  let Brow := StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
      (StairConcreteAssembly.hostPlan.group true d first (c + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first)) (basePacketTail d first)) ++
       renameProgram (OB5.sig 511) (StairGroups.groups true d (first + 1) c))
  let W := (Finset.range 10).image (MeasuredCodec5.label F)
  have hshape : StairSchedule.forwardSegment p B N s f ++
      StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true d first (c + 1) =
      (A0 ++ E138') ++ ep' ++ Mrow ++ dp' ++ Brow := by
    rw [forwardSegment_row B N s f first h1 h2 h5 hdue hf0, hostedGroup_true_head, hdp]
    simp only [A0, E138', ep', Mrow, dp', Brow, hpdef, hw, hFdef, List.append_assoc]
  have hcut : cutRow B N s f d first c = (A0 ++ E138') ++ Mrow ++ Brow := by
    simp only [cutRow, A0, E138', Mrow, Brow, hpdef, hw, hFdef, List.append_assoc]
  have hE : wires ep' ⊆ W := by
    intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨i, supp.2.1 hi, rfl⟩
  have hD : wires dp' ⊆ W := by
    intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨i, supp.2.2 hi, rfl⟩
  have trip : ∀ tA me md, run dp' md (run ep' me (run (A0 ++ E138') tA x0)) = run (A0 ++ E138') tA x0 := by
    intro tA me md
    rw [run_append]
    exact placed_trip F hF _ (hlegal _) _ me md
  rw [hshape, hcut]
  exact row_cut (A0 ++ E138') ep' Mrow dp' Brow W hE hD hdisj x0 m trip

end ECDSAAdd.Entrant.PackCutEntry

namespace ECDSAAdd.Entrant.PackCutLegal
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open StairPhysicalLayout StairField2V3Seg

/-- Legality only reads the ten placed wires. -/
theorem legalAt_congr (f : Fin 10 → Wire) (s t : BasisState) (h : ∀ j : Fin 10, s (f j) = t (f j)) :
    MeasuredCodec5.legalAt f s ↔ MeasuredCodec5.legalAt f t := by
  rw [MeasuredCodec5.legalAt_iff, MeasuredCodec5.legalAt_iff]
  constructor <;> intro H i
  · rw [← h, ← h]; exact H i
  · rw [h, h]; exact H i

/-- PACK-CUT legality: the letters of the packet due at tick `i = startFor B + 1 + n` are legal right
after the moved tick `i`, from the segment's own precondition. -/
theorem legal_at_due (B : Nat) (hB : B ∈ budgets) (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p) (u : State)
    (pre1 : ∀ r ∈ futurePayload B, u.basis r = cmpBits B x r)
    (pre2 : ∀ r ∈ rowSites B ++ allBC, r ∉ futurePayload B → u.basis r = false)
    (hsh : ∀ q, base 4000 ≤ q → u.basis q = false)
    (n : Nat) (hn : startFor B + 1 + n + 1 ≤ 512)
    (hdue : History5.packDue (startFor B + 1 + n) = true) (h5 : 5 ≤ startFor B + 1 + n)
    (hvirt : ∀ j : Fin 10, ¬ StairFirstTickV3.virtualSites B
      (History5.historyMap (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n - 5) j))
    (htick : ∀ j : Fin 10, History5.historyMap (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n - 5) j ∉
      wires (TickRanges.tick (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n)))
    (m1 m2 m3 m4 : List Bool) :
    MeasuredCodec5.legalAt (History5.historyMap (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n - 5))
      (run (TickRanges.tick (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n)) m4
        (run (StairPhysicalPrimitives.middleForward (startFor B + 1) n) m3
          (run (StairPhysicalPrimitives.tickForward (startFor B)) m2
            (run (StairPhysicalPrimitives.unpack B) m1 u)))).basis := by
  set w := StairPhysicalPrimitives.midSegmentMap B
  set i := startFor B + 1 + n
  have dec1 := StairField2V3Decode.decoded_after_unpack B hB x hx0 hx u pre1 pre2 hsh m1
  have hreal := StairField2V3Walk.p_hyp x hx0 hx
  obtain ⟨z, -, zag, zst, -⟩ := StairField2V3Walk.walk_full B hB x hreal _ dec1 m2 m3 n (by omega)
  obtain ⟨raw, hraw, hz⟩ := zst
  have hnod := StairPhysicalPrimitives.midSegmentMap_pool_nodup B hB
  obtain ⟨hp0, hodd, -⟩ := StairField2V3Unpack.p_facts
  have lraw := W.stage_group_legal w hnod x ECDSAAdd.p i (i - 5) hp0 hodd (by omega) (by omega)
    raw.basis hraw
  have lz : MeasuredCodec5.legalAt (History5.historyMap w (i - 5)) z.basis := by
    rw [hz]
    exact Rolling1588.Integer.prefix_next_legal w true hnod i (by omega) hdue raw [] lraw
  -- transfer to the real state (packet wires are not virtual), then through the tick (not touched)
  apply (legalAt_congr _ _ _ (fun j => ?_)).mpr lz
  rw [run_preserves_outside _ _ _ _ (htick j)]
  exact zag _ (hvirt j)

end ECDSAAdd.Entrant.PackCutLegal



namespace ECDSAAdd.Entrant.PackCutChain
open ECDSAAdd ECDSAAdd.Entrant StairField2V3Couple

/-- A coupled step survives replacing the actual program by one whose runs are runs of the old program
(with another tape) on every related pair. -/
theorem crel_of_runeq {pre post : State → State → Prop} {P P' Q : Program}
    (h : CRel pre post P Q)
    (e : ∀ s t, pre s t → ∀ fresh, ∃ fresh', run P' fresh s = run P fresh' s) :
    CRel pre post P' Q := by
  intro s t hst fresh
  obtain ⟨f', hf'⟩ := e s t hst fresh
  obtain ⟨o, ho⟩ := h s t hst f'
  exact ⟨o, by rw [hf']; exact ho⟩

/-- Tape-existential run equality extends by a common suffix. -/
theorem runeq_append_right {A A' : Program} (R : Program) (s : State)
    (h : ∀ m, ∃ m', run A' m s = run A m' s) :
    ∀ m, ∃ m', run (A' ++ R) m s = run (A ++ R) m' s := by
  intro m
  obtain ⟨m1, h1⟩ := h (m.take (measurementCount A'))
  let k := measurementCount A
  let pre := m1.take k ++ List.replicate (k - (m1.take k).length) false
  have hlen : pre.length = k := by
    simp only [pre, List.length_append, List.length_replicate, List.length_take]
    omega
  refine ⟨pre ++ m.drop (measurementCount A'), ?_⟩
  rw [run_append A' R, run_append A R, h1, List.take_left' hlen, List.drop_left' hlen]
  congr 1
  rw [run_pad_false, run_take]

/-- Tape-existential run equality lifts through `liftF`. -/
theorem runeq_liftF {A A' : Program} (s : State)
    (h : ∀ m, ∃ m', run A' m (StairField2V3Seg.pullIn s) = run A m' (StairField2V3Seg.pullIn s)) :
    ∀ m, ∃ m', run (StairField2V3Entry.liftF A') m s = run (StairField2V3Entry.liftF A) m' s := by
  intro m
  obtain ⟨m', hm⟩ := h m
  exact ⟨m', by rw [StairField2V3Seg.liftF_run, StairField2V3Seg.liftF_run, hm]⟩

end ECDSAAdd.Entrant.PackCutChain



namespace ECDSAAdd.Entrant.PackCutBridge
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3Delta StairField2V3Seg
open StairField2V3ExitPlanR StairPhysicalLayout StairOuterPlacement StairField2V3EntryPlanR

/-- The entry row relation gives the segment's codec precondition on the pulled state. -/
theorem pre_of_rowrel (x B B' : Nat) (X : Program)
    (rec : ∀ t, ReachEn x X t → ∀ r ∈ scratchT B B', t.basis (fieldPlace r) = false) (s t : State)
    (h : RowRelEn x B X s t) :
    ∃ origin, TraceOK x origin ∧
      (∀ r ∈ futurePayload B, (pullIn s).basis r = cmpBits B x r) ∧
      (∀ r ∈ scratchT B B', (pullIn s).basis r = false) := by
  obtain ⟨⟨⟨_, hout⟩, ⟨origin, hx, hv⟩⟩, hreachX⟩ := h
  have notFut : ∀ r ∈ scratchT B B', r ∉ futurePayload B := by
    intro r hr
    exact of_decide_eq_true (List.mem_filter.mp hr).2
  refine ⟨origin, hx, fun r hr => (hv r hr).2, ?_⟩
  intro r hr
  change s.basis (fieldPlace r) = false
  rw [hout _ (not_mem_Δv B r (notFut r hr))]
  exact rec t hreachX r hr

/-- The basis target of an instruction. -/
def tgtW : Instr → Wire
  | .X t => t
  | .CX _ t => t
  | .CCX _ _ t => t
  | .measureX t _ _ => t

/-- A wire that no instruction targets keeps its basis value (controls and phase corrections only read it). -/
theorem run_keep_nontarget (P : Program) (q : Wire) (h : ∀ i ∈ P, tgtW i ≠ q) (m : List Bool) (s : State) :
    (run P m s).basis q = s.basis q := by
  induction P generalizing m s with
  | nil => rfl
  | cons i p ih =>
    have hi := h i List.mem_cons_self
    have hp : ∀ j ∈ p, tgtW j ≠ q := fun j hj => h j (List.mem_cons_of_mem _ hj)
    cases i with
    | X t =>
      simp only [tgtW] at hi
      simp only [run]; rw [ih hp]
      simp only [writeBit, Function.update_apply, if_neg (Ne.symm hi)]
    | CX c t =>
      simp only [tgtW] at hi
      simp only [run]; rw [ih hp]
      simp only [writeBit, Function.update_apply, if_neg (Ne.symm hi)]
    | CCX a b t =>
      simp only [tgtW] at hi
      simp only [run]; rw [ih hp]
      simp only [writeBit, Function.update_apply, if_neg (Ne.symm hi)]
    | measureX t c0 c1 =>
      simp only [tgtW] at hi
      simp only [run]; rw [ih hp]
      simp only [measureAndCorrect, correct_basis, writeBit, Function.update_apply, if_neg (Ne.symm hi)]

/-- PACK-CUT legality after the due tick: the letters of the packet due at tick `i = startFor B + 1 + n` are
legal right after the moved tick `i` (the tick may read the packet's wires but never targets them). -/
theorem legal_at_due2 (B : Nat) (hB : B ∈ budgets) (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p)
    (u : State)
    (pre1 : ∀ r ∈ futurePayload B, u.basis r = cmpBits B x r)
    (pre2 : ∀ r ∈ rowSites B ++ allBC, r ∉ futurePayload B → u.basis r = false)
    (hsh : ∀ q, base 4000 ≤ q → u.basis q = false)
    (n : Nat) (hn : startFor B + 1 + n + 1 ≤ 512)
    (hdue : History5.packDue (startFor B + 1 + n) = true) (h5 : 5 ≤ startFor B + 1 + n)
    (hvirt : ∀ j : Fin 10, ¬ StairFirstTickV3.virtualSites B
      (History5.historyMap (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n - 5) j))
    (hntgt : ∀ j : Fin 10, ∀ ins ∈ TickRanges.tick (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n),
      tgtW ins ≠ History5.historyMap (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n - 5) j)
    (m1 m2 m3 m4 : List Bool) :
    MeasuredCodec5.legalAt (History5.historyMap (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n - 5))
      (run (TickRanges.tick (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n)) m4
        (run (StairPhysicalPrimitives.middleForward (startFor B + 1) n) m3
          (run (StairPhysicalPrimitives.tickForward (startFor B)) m2
            (run (StairPhysicalPrimitives.unpack B) m1 u)))).basis := by
  set w := StairPhysicalPrimitives.midSegmentMap B
  set i := startFor B + 1 + n
  have dec1 := StairField2V3Decode.decoded_after_unpack B hB x hx0 hx u pre1 pre2 hsh m1
  have hreal := StairField2V3Walk.p_hyp x hx0 hx
  obtain ⟨z, -, zag, zst, -⟩ := StairField2V3Walk.walk_full B hB x hreal _ dec1 m2 m3 n (by omega)
  obtain ⟨raw, hraw, hz⟩ := zst
  have hnod := StairPhysicalPrimitives.midSegmentMap_pool_nodup B hB
  obtain ⟨hp0, hodd, -⟩ := StairField2V3Unpack.p_facts
  have lraw := W.stage_group_legal w hnod x ECDSAAdd.p i (i - 5) hp0 hodd (by omega) (by omega)
    raw.basis hraw
  have lz : MeasuredCodec5.legalAt (History5.historyMap w (i - 5)) z.basis := by
    rw [hz]
    exact Rolling1588.Integer.prefix_next_legal w true hnod i (by omega) hdue raw [] lraw
  apply (PackCutLegal.legalAt_congr _ _ _ (fun j => ?_)).mpr lz
  rw [run_keep_nontarget _ _ (hntgt j)]
  exact zag _ (hvirt j)

/-- Legality of the due packet right after the moved due tick, read off the row relation. -/
theorem legal_prefix (x B B' : Nat) (hpair : (B, B') ∈ StairField2V3Walk.rowPairs) (X : Program)
    (rec : ∀ t, ReachEn x X t → ∀ r ∈ scratchT B B', t.basis (fieldPlace r) = false)
    (s t : State) (h : RowRelEn x B X s t)
    (n : Nat) (hn : startFor B + 1 + n + 1 ≤ 512)
    (hdue : History5.packDue (startFor B + 1 + n) = true) (h5 : 5 ≤ startFor B + 1 + n)
    (hvirt : ∀ j : Fin 10, ¬ StairFirstTickV3.virtualSites B
      (History5.historyMap (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n - 5) j))
    (hntgt : ∀ j : Fin 10, ∀ ins ∈ TickRanges.tick (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n),
      tgtW ins ≠ History5.historyMap (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n - 5) j)
    (hlow : ∀ q ∈ wires (StairPhysicalPrimitives.unpack B ++ StairPhysicalPrimitives.tickForward (startFor B) ++
      StairPhysicalPrimitives.middleForward (startFor B + 1) n ++
      TickRanges.tick (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n)), q < base 4000)
    (hpk : ∀ j : Fin 10, History5.historyMap (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n - 5) j <
      base 4000)
    (t1 : List Bool) :
    MeasuredCodec5.legalAt (History5.historyMap (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n - 5))
      (run (StairPhysicalPrimitives.unpack B ++ StairPhysicalPrimitives.tickForward (startFor B) ++
        StairPhysicalPrimitives.middleForward (startFor B + 1) n ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1 + n)) t1 (pullIn s)).basis := by
  obtain ⟨origin, hx, pre1, pre2⟩ := pre_of_rowrel x B B' X rec s t h
  obtain ⟨hB, -, -⟩ := StairField2V3Walk.pair_mem B B' hpair
  have fLow2 := StairField2V3SegFacts2.FactsLow2_ok B B' hpair
  set u := pullIn s with hu
  have lowFP : ∀ r ∈ futurePayload B, r < base 4000 :=
    fun r hr => fLow2 r (by simp only [List.mem_append, hr, true_or, or_true])
  have lowS : ∀ r ∈ scratchT B B', r < base 4000 :=
    fun r hr => fLow2 r (by simp only [List.mem_append, hr, or_true])
  have zh : ∀ q, q < base 4000 → (StairField2V3SegSpec.zeroHigh u).basis q = u.basis q := by
    intro q hq
    show (if base 4000 ≤ q then false else u.basis q) = u.basis q
    rw [if_neg (Nat.not_le.mpr hq)]
  have pre1' : ∀ r ∈ futurePayload B, (StairField2V3SegSpec.zeroHigh u).basis r = cmpBits B x r :=
    fun r hr => (zh r (lowFP r hr)).trans (pre1 r hr)
  have pre2' : ∀ r ∈ rowSites B ++ allBC, r ∉ futurePayload B →
      (StairField2V3SegSpec.zeroHigh u).basis r = false := by
    intro r hr hf
    have hs : r ∈ scratchT B B' := by
      unfold scratchT
      rw [List.mem_filter]
      refine ⟨?_, decide_eq_true hf⟩
      rcases List.mem_append.mp hr with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_right _ h
    exact (zh r (lowS r hs)).trans (pre2 r hs)
  have hsh : ∀ q, base 4000 ≤ q → (StairField2V3SegSpec.zeroHigh u).basis q = false := by
    intro q hq
    show (if base 4000 ≤ q then false else u.basis q) = false
    rw [if_pos hq]
  have L := fun m1 m2 m3 m4 => legal_at_due2 B hB x hx.1 hx.2.1 (StairField2V3SegSpec.zeroHigh u)
    pre1' pre2' hsh n hn hdue h5 hvirt hntgt m1 m2 m3 m4
  obtain ⟨-, lagree, -⟩ := StairField2V3SegSpec.low_reduce _ hlow t1 u
  refine (PackCutLegal.legalAt_congr _ _ _ (fun j => lagree _ (hpk j))).mpr ?_
  rw [run_append, run_append, run_append]
  exact L _ _ _ _

end ECDSAAdd.Entrant.PackCutBridge



namespace ECDSAAdd.Entrant.PackCutRows
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3Delta StairField2V3Seg
open StairField2V3ExitPlanR StairPhysicalLayout StairOuterPlacement StairField2V3EntryPlanR
open PackCutBridge

theorem label_virt (w : Nat → Wire) (first : Nat) (q : Wire)
    (hq : q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap w (5 * first)))) :
    StairFirstTickV3.VWire w (5 * first + 5) q := by
  simp only [Finset.mem_image, Finset.mem_range] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  refine ⟨History5.historyId (5 * first) ⟨k, hk⟩, ?_, ?_⟩
  · unfold StairFirstTickV3.Virt History5.historyId; split_ifs <;> omega
  · simp [MeasuredCodec5.label, hk, History5.historyMap]

theorem moved_disj (w : Nat → Wire) (hinj : Function.Injective w) (first f : Nat)
    (hf : f ≤ 512) (hlt : 5 * first + 5 < f) :
    ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap w (5 * first))),
      q ∉ wires (StairReplay.movedForward w (5 * first + 5 + 1) (f - (5 * first + 5) - 1)) := by
  intro q hq hm
  exact StairFirstTickV3.movedForward_clean w hinj (5 * first + 5) (by omega) (f - (5 * first + 5) - 1)
    (5 * first + 5 + 1) (by omega) (by omega) (by omega) q hm (label_virt w first q hq)

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
  cases i <;> simp [Instr.wires, iwl, mem_cwl]

theorem mem_wl (q : Wire) (P : Program) : q ∈ wires P ↔ q ∈ wl P := by
  induction P with
  | nil => simp [wires, wl]
  | cons i p ih => simp [wires, wl, mem_iwl, ih]

/-- Ten placed wires avoid a program, from one Bool list check. -/
theorem avoid10 (F : Fin 10 → Wire) (P : Program)
    (h : ((List.finRange 10).map (MeasuredCodec5.label F ∘ Fin.val)).all (fun q => !((wl P).contains q)) = true) :
    ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label F), q ∉ wires P := by
  intro q hq hm
  simp only [Finset.mem_image, Finset.mem_range] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  have hmem : MeasuredCodec5.label F k ∈ (List.finRange 10).map (MeasuredCodec5.label F ∘ Fin.val) :=
    List.mem_map.mpr ⟨⟨k, hk⟩, List.mem_finRange _, rfl⟩
  have h1 := List.all_eq_true.mp h _ hmem
  rw [mem_wl] at hm
  simp at h1
  exact h1 hm


/-! ## Entry row 1 -/

abbrev w87 : Nat → Wire := StairPhysicalPrimitives.midSegmentMap 87

theorem hB87 : 87 ∈ budgets := by decide

theorem hvirt1 : ∀ j : Fin 10, ¬ StairFirstTickV3.virtualSites 87 (History5.historyMap w87 (startFor 87 + 1 + 4 - 5) j) := by
  intro j
  have hinj := StairFirstTickV3.midSegmentMap_injective 87 hB87
  have hs : startFor 87 = 425 := by decide
  show ¬ StairFirstTickV3.VWire w87 (startFor 87) (w87 (History5.historyId (startFor 87 + 1 + 4 - 5) j))
  rw [hs]
  apply StairFirstTickV3.not_vwire w87 hinj 425
  have hj := j.isLt
  unfold StairFirstTickV3.Virt History5.historyId
  split_ifs <;> omega

set_option maxRecDepth 100000 in
theorem hntgt1 : ∀ j : Fin 10, ∀ ins ∈ TickRanges.tick w87 (startFor 87 + 1 + 4),
    tgtW ins ≠ History5.historyMap w87 (startFor 87 + 1 + 4 - 5) j := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hpk1 : ∀ j : Fin 10, History5.historyMap w87 (startFor 87 + 1 + 4 - 5) j < base 4000 := by
  decide +kernel

section
attribute [local irreducible] wires StairPhysicalPrimitives.unpack StairPhysicalPrimitives.tickForward TickRanges.tick StairReplay.movedForward

theorem hlow1 : ∀ q ∈ wires (StairPhysicalPrimitives.unpack 87 ++ StairPhysicalPrimitives.tickForward (startFor 87) ++
      StairPhysicalPrimitives.middleForward (startFor 87 + 1) 4 ++ TickRanges.tick w87 (startFor 87 + 1 + 4)),
      q < base 4000 := by
  intro q hq
  apply StairField2V3SegSpec.seg_low 87 62 (by decide) q
  have hs : startFor 87 = 425 := by decide
  have hN : startFor 62 = 450 := by decide
  rw [StairField2V3SegSpec.segP_eq]
  rw [hs] at hq ⊢
  rw [hN]
  have e1 : StairPhysicalPrimitives.middleForward (425 + 1) 4 = StairReplay.movedForward w87 (425 + 1) 4 := by
    unfold StairPhysicalPrimitives.middleForward; rfl
  have e2 : StairPhysicalPrimitives.middleForward (425 + 1) (450 - 425 - 1) =
      StairReplay.movedForward w87 (425 + 1) (4 + 1 + 19) := by
    unfold StairPhysicalPrimitives.middleForward; rfl
  rw [e1] at hq
  rw [e2, PackCutShape.movedForward_at]
  simp only [wires_append, Finset.mem_union] at hq ⊢
  tauto

end

theorem hF1 : Function.Injective (History5.historyMap
    (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (5 * 85)) := by
  have hseg : StairPhysicalPrimitives.segmentOf (425 + 1) = 87 := by decide
  rw [hseg]
  have hid : Function.Injective (History5.historyId (5 * 85)) := by decide
  exact (StairFirstTickV3.midSegmentMap_injective 87 hB87).comp hid

set_option maxRecDepth 200000 in
theorem hdp1 : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop 13)
      (StairConcreteAssembly.hostPlan.group true 13 85 (4 + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi 85))
        (Rolling1588.onPacket 85 Rolling1588.dp))) =
    renameProgram (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (5 * 85)))
      Rolling1588.dp := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem tail1 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (5 * 85))),
    q ∉ wires (StairConcreteAssembly.checkpointPrimitives.orient 450 ++
      renameProgram (OB5.sig 450) (Rolling1588.Integer.packFirst base true 450) ++
      StairConcreteAssembly.checkpointPrimitives.pack 62) :=
  avoid10 _ _ (by decide +kernel)

theorem hdisj1 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (5 * 85))),
    q ∉ wires (StairReplay.movedForward
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1)))
        (5 * 85 + 5 + 1) (450 - (5 * 85 + 5) - 1) ++
      StairConcreteAssembly.checkpointPrimitives.orient 450 ++
      renameProgram (OB5.sig 450) (Rolling1588.Integer.packFirst base true 450) ++
      StairConcreteAssembly.checkpointPrimitives.pack 62) := by
  intro q hq hm
  have hseg : StairPhysicalPrimitives.segmentOf (425 + 1) = 87 := by decide
  have mv := moved_disj (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1)))
    (by rw [hseg]; exact StairFirstTickV3.midSegmentMap_injective 87 hB87) 85 450 (by decide) (by decide) q hq
  have tl := tail1 q hq
  simp only [List.append_assoc, wires_append, Finset.mem_union] at hm tl
  rcases hm with h | h
  · exact mv h
  · exact tl h

/-- PACK-CUT, entry row 1 (B 87 → 62, group d 13 / first 85 / 5 packets): the cut row has the
original row's run, from the row relation at the segment start. -/
theorem row1_cut (x : Nat) (X : Program) (rec : ∀ t, ReachEn x X t → ∀ r ∈ scratchT 87 62, t.basis (fieldPlace r) = false) (s t : State) (h : RowRelEn x 87 X s t)
    (m : List Bool) :
    ∃ m', run (PackCutEntry.cutRow 87 62 425 450 13 85 4) m (pullIn s) =
      run (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 13 85 (4 + 1)) m' (pullIn s) :=
  PackCutEntry.entry_row_cut 87 62 425 450 13 85 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    hF1 hdp1 hdisj1 (pullIn s)
    (fun t1 => legal_prefix x 87 62 (by decide) X rec s t h 4 (by decide) (by decide) (by decide)
      hvirt1 hntgt1 hlow1 hpk1 t1) m

/-! ## Entry row 2 -/

abbrev w62 : Nat → Wire := StairPhysicalPrimitives.midSegmentMap 62

theorem hB62 : 62 ∈ budgets := by decide

theorem hvirt2 : ∀ j : Fin 10, ¬ StairFirstTickV3.virtualSites 62 (History5.historyMap w62 (startFor 62 + 1 + 4 - 5) j) := by
  intro j
  have hinj := StairFirstTickV3.midSegmentMap_injective 62 hB62
  have hs : startFor 62 = 450 := by decide
  show ¬ StairFirstTickV3.VWire w62 (startFor 62) (w62 (History5.historyId (startFor 62 + 1 + 4 - 5) j))
  rw [hs]
  apply StairFirstTickV3.not_vwire w62 hinj 450
  have hj := j.isLt
  unfold StairFirstTickV3.Virt History5.historyId
  split_ifs <;> omega

set_option maxRecDepth 100000 in
theorem hntgt2 : ∀ j : Fin 10, ∀ ins ∈ TickRanges.tick w62 (startFor 62 + 1 + 4),
    tgtW ins ≠ History5.historyMap w62 (startFor 62 + 1 + 4 - 5) j := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hpk2 : ∀ j : Fin 10, History5.historyMap w62 (startFor 62 + 1 + 4 - 5) j < base 4000 := by
  decide +kernel

section
attribute [local irreducible] wires StairPhysicalPrimitives.unpack StairPhysicalPrimitives.tickForward TickRanges.tick StairReplay.movedForward

theorem hlow2 : ∀ q ∈ wires (StairPhysicalPrimitives.unpack 62 ++ StairPhysicalPrimitives.tickForward (startFor 62) ++
      StairPhysicalPrimitives.middleForward (startFor 62 + 1) 4 ++ TickRanges.tick w62 (startFor 62 + 1 + 4)),
      q < base 4000 := by
  intro q hq
  apply StairField2V3SegSpec.seg_low 62 47 (by decide) q
  have hs : startFor 62 = 450 := by decide
  have hN : startFor 47 = 465 := by decide
  rw [StairField2V3SegSpec.segP_eq]
  rw [hs] at hq ⊢
  rw [hN]
  have e1 : StairPhysicalPrimitives.middleForward (450 + 1) 4 = StairReplay.movedForward w62 (450 + 1) 4 := by
    unfold StairPhysicalPrimitives.middleForward; rfl
  have e2 : StairPhysicalPrimitives.middleForward (450 + 1) (465 - 450 - 1) =
      StairReplay.movedForward w62 (450 + 1) (4 + 1 + 9) := by
    unfold StairPhysicalPrimitives.middleForward; rfl
  rw [e1] at hq
  rw [e2, PackCutShape.movedForward_at]
  simp only [wires_append, Finset.mem_union] at hq ⊢
  tauto

end

theorem hF2 : Function.Injective (History5.historyMap
    (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (5 * 90)) := by
  have hseg : StairPhysicalPrimitives.segmentOf (450 + 1) = 62 := by decide
  rw [hseg]
  have hid : Function.Injective (History5.historyId (5 * 90)) := by decide
  exact (StairFirstTickV3.midSegmentMap_injective 62 hB62).comp hid

set_option maxRecDepth 200000 in
theorem hdp2 : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop 22)
      (StairConcreteAssembly.hostPlan.group true 22 90 (2 + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi 90))
        (Rolling1588.onPacket 90 Rolling1588.dp))) =
    renameProgram (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (5 * 90)))
      Rolling1588.dp := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem tail2 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (5 * 90))),
    q ∉ wires (StairConcreteAssembly.checkpointPrimitives.orient 465 ++
      renameProgram (OB5.sig 465) (Rolling1588.Integer.packFirst base true 465) ++
      StairConcreteAssembly.checkpointPrimitives.pack 47) :=
  avoid10 _ _ (by decide +kernel)

theorem hdisj2 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (5 * 90))),
    q ∉ wires (StairReplay.movedForward
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1)))
        (5 * 90 + 5 + 1) (465 - (5 * 90 + 5) - 1) ++
      StairConcreteAssembly.checkpointPrimitives.orient 465 ++
      renameProgram (OB5.sig 465) (Rolling1588.Integer.packFirst base true 465) ++
      StairConcreteAssembly.checkpointPrimitives.pack 47) := by
  intro q hq hm
  have hseg : StairPhysicalPrimitives.segmentOf (450 + 1) = 62 := by decide
  have mv := moved_disj (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1)))
    (by rw [hseg]; exact StairFirstTickV3.midSegmentMap_injective 62 hB62) 90 465 (by decide) (by decide) q hq
  have tl := tail2 q hq
  simp only [List.append_assoc, wires_append, Finset.mem_union] at hm tl
  rcases hm with h | h
  · exact mv h
  · exact tl h

/-- PACK-CUT, entry row 2 (B 62 → 47, group d 22 / first 90 / 3 packets): the cut row has the
original row's run, from the row relation at the segment start. -/
theorem row2_cut (x : Nat) (X : Program) (rec : ∀ t, ReachEn x X t → ∀ r ∈ scratchT 62 47, t.basis (fieldPlace r) = false) (s t : State) (h : RowRelEn x 62 X s t)
    (m : List Bool) :
    ∃ m', run (PackCutEntry.cutRow 62 47 450 465 22 90 2) m (pullIn s) =
      run (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 22 90 (2 + 1)) m' (pullIn s) :=
  PackCutEntry.entry_row_cut 62 47 450 465 22 90 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    hF2 hdp2 hdisj2 (pullIn s)
    (fun t1 => legal_prefix x 62 47 (by decide) X rec s t h 4 (by decide) (by decide) (by decide)
      hvirt2 hntgt2 hlow2 hpk2 t1) m

/-! ## Entry row 3 -/

abbrev w47 : Nat → Wire := StairPhysicalPrimitives.midSegmentMap 47

theorem hB47 : 47 ∈ budgets := by decide

theorem hvirt3 : ∀ j : Fin 10, ¬ StairFirstTickV3.virtualSites 47 (History5.historyMap w47 (startFor 47 + 1 + 4 - 5) j) := by
  intro j
  have hinj := StairFirstTickV3.midSegmentMap_injective 47 hB47
  have hs : startFor 47 = 465 := by decide
  show ¬ StairFirstTickV3.VWire w47 (startFor 47) (w47 (History5.historyId (startFor 47 + 1 + 4 - 5) j))
  rw [hs]
  apply StairFirstTickV3.not_vwire w47 hinj 465
  have hj := j.isLt
  unfold StairFirstTickV3.Virt History5.historyId
  split_ifs <;> omega

set_option maxRecDepth 100000 in
theorem hntgt3 : ∀ j : Fin 10, ∀ ins ∈ TickRanges.tick w47 (startFor 47 + 1 + 4),
    tgtW ins ≠ History5.historyMap w47 (startFor 47 + 1 + 4 - 5) j := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hpk3 : ∀ j : Fin 10, History5.historyMap w47 (startFor 47 + 1 + 4 - 5) j < base 4000 := by
  decide +kernel

section
attribute [local irreducible] wires StairPhysicalPrimitives.unpack StairPhysicalPrimitives.tickForward TickRanges.tick StairReplay.movedForward

theorem hlow3 : ∀ q ∈ wires (StairPhysicalPrimitives.unpack 47 ++ StairPhysicalPrimitives.tickForward (startFor 47) ++
      StairPhysicalPrimitives.middleForward (startFor 47 + 1) 4 ++ TickRanges.tick w47 (startFor 47 + 1 + 4)),
      q < base 4000 := by
  intro q hq
  apply StairField2V3SegSpec.seg_low 47 32 (by decide) q
  have hs : startFor 47 = 465 := by decide
  have hN : startFor 32 = 480 := by decide
  rw [StairField2V3SegSpec.segP_eq]
  rw [hs] at hq ⊢
  rw [hN]
  have e1 : StairPhysicalPrimitives.middleForward (465 + 1) 4 = StairReplay.movedForward w47 (465 + 1) 4 := by
    unfold StairPhysicalPrimitives.middleForward; rfl
  have e2 : StairPhysicalPrimitives.middleForward (465 + 1) (480 - 465 - 1) =
      StairReplay.movedForward w47 (465 + 1) (4 + 1 + 9) := by
    unfold StairPhysicalPrimitives.middleForward; rfl
  rw [e1] at hq
  rw [e2, PackCutShape.movedForward_at]
  simp only [wires_append, Finset.mem_union] at hq ⊢
  tauto

end

theorem hF3 : Function.Injective (History5.historyMap
    (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (5 * 93)) := by
  have hseg : StairPhysicalPrimitives.segmentOf (465 + 1) = 47 := by decide
  rw [hseg]
  have hid : Function.Injective (History5.historyId (5 * 93)) := by decide
  exact (StairFirstTickV3.midSegmentMap_injective 47 hB47).comp hid

set_option maxRecDepth 200000 in
theorem hdp3 : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop 30)
      (StairConcreteAssembly.hostPlan.group true 30 93 (2 + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi 93))
        (Rolling1588.onPacket 93 Rolling1588.dp))) =
    renameProgram (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (5 * 93)))
      Rolling1588.dp := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem tail3 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (5 * 93))),
    q ∉ wires (StairConcreteAssembly.checkpointPrimitives.orient 480 ++
      renameProgram (OB5.sig 480) (Rolling1588.Integer.packFirst base true 480) ++
      StairConcreteAssembly.checkpointPrimitives.pack 32) :=
  avoid10 _ _ (by decide +kernel)

theorem hdisj3 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (5 * 93))),
    q ∉ wires (StairReplay.movedForward
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1)))
        (5 * 93 + 5 + 1) (480 - (5 * 93 + 5) - 1) ++
      StairConcreteAssembly.checkpointPrimitives.orient 480 ++
      renameProgram (OB5.sig 480) (Rolling1588.Integer.packFirst base true 480) ++
      StairConcreteAssembly.checkpointPrimitives.pack 32) := by
  intro q hq hm
  have hseg : StairPhysicalPrimitives.segmentOf (465 + 1) = 47 := by decide
  have mv := moved_disj (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1)))
    (by rw [hseg]; exact StairFirstTickV3.midSegmentMap_injective 47 hB47) 93 480 (by decide) (by decide) q hq
  have tl := tail3 q hq
  simp only [List.append_assoc, wires_append, Finset.mem_union] at hm tl
  rcases hm with h | h
  · exact mv h
  · exact tl h

/-- PACK-CUT, entry row 3 (B 47 → 32, group d 30 / first 93 / 3 packets): the cut row has the
original row's run, from the row relation at the segment start. -/
theorem row3_cut (x : Nat) (X : Program) (rec : ∀ t, ReachEn x X t → ∀ r ∈ scratchT 47 32, t.basis (fieldPlace r) = false) (s t : State) (h : RowRelEn x 47 X s t)
    (m : List Bool) :
    ∃ m', run (PackCutEntry.cutRow 47 32 465 480 30 93 2) m (pullIn s) =
      run (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 30 93 (2 + 1)) m' (pullIn s) :=
  PackCutEntry.entry_row_cut 47 32 465 480 30 93 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    hF3 hdp3 hdisj3 (pullIn s)
    (fun t1 => legal_prefix x 47 32 (by decide) X rec s t h 4 (by decide) (by decide) (by decide)
      hvirt3 hntgt3 hlow3 hpk3 t1) m

/-! ## Entry row 4 -/

abbrev w32 : Nat → Wire := StairPhysicalPrimitives.midSegmentMap 32

theorem hB32 : 32 ∈ budgets := by decide

theorem hvirt4 : ∀ j : Fin 10, ¬ StairFirstTickV3.virtualSites 32 (History5.historyMap w32 (startFor 32 + 1 + 4 - 5) j) := by
  intro j
  have hinj := StairFirstTickV3.midSegmentMap_injective 32 hB32
  have hs : startFor 32 = 480 := by decide
  show ¬ StairFirstTickV3.VWire w32 (startFor 32) (w32 (History5.historyId (startFor 32 + 1 + 4 - 5) j))
  rw [hs]
  apply StairFirstTickV3.not_vwire w32 hinj 480
  have hj := j.isLt
  unfold StairFirstTickV3.Virt History5.historyId
  split_ifs <;> omega

set_option maxRecDepth 100000 in
theorem hntgt4 : ∀ j : Fin 10, ∀ ins ∈ TickRanges.tick w32 (startFor 32 + 1 + 4),
    tgtW ins ≠ History5.historyMap w32 (startFor 32 + 1 + 4 - 5) j := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hpk4 : ∀ j : Fin 10, History5.historyMap w32 (startFor 32 + 1 + 4 - 5) j < base 4000 := by
  decide +kernel

section
attribute [local irreducible] wires StairPhysicalPrimitives.unpack StairPhysicalPrimitives.tickForward TickRanges.tick StairReplay.movedForward

theorem hlow4 : ∀ q ∈ wires (StairPhysicalPrimitives.unpack 32 ++ StairPhysicalPrimitives.tickForward (startFor 32) ++
      StairPhysicalPrimitives.middleForward (startFor 32 + 1) 4 ++ TickRanges.tick w32 (startFor 32 + 1 + 4)),
      q < base 4000 := by
  intro q hq
  apply StairField2V3SegSpec.seg_low 32 22 (by decide) q
  have hs : startFor 32 = 480 := by decide
  have hN : startFor 22 = 490 := by decide
  rw [StairField2V3SegSpec.segP_eq]
  rw [hs] at hq ⊢
  rw [hN]
  have e1 : StairPhysicalPrimitives.middleForward (480 + 1) 4 = StairReplay.movedForward w32 (480 + 1) 4 := by
    unfold StairPhysicalPrimitives.middleForward; rfl
  have e2 : StairPhysicalPrimitives.middleForward (480 + 1) (490 - 480 - 1) =
      StairReplay.movedForward w32 (480 + 1) (4 + 1 + 4) := by
    unfold StairPhysicalPrimitives.middleForward; rfl
  rw [e1] at hq
  rw [e2, PackCutShape.movedForward_at]
  simp only [wires_append, Finset.mem_union] at hq ⊢
  tauto

end

theorem hF4 : Function.Injective (History5.historyMap
    (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (5 * 96)) := by
  have hseg : StairPhysicalPrimitives.segmentOf (480 + 1) = 32 := by decide
  rw [hseg]
  have hid : Function.Injective (History5.historyId (5 * 96)) := by decide
  exact (StairFirstTickV3.midSegmentMap_injective 32 hB32).comp hid

set_option maxRecDepth 200000 in
theorem hdp4 : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop 36)
      (StairConcreteAssembly.hostPlan.group true 36 96 (1 + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi 96))
        (Rolling1588.onPacket 96 Rolling1588.dp))) =
    renameProgram (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (5 * 96)))
      Rolling1588.dp := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem tail4 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (5 * 96))),
    q ∉ wires (StairConcreteAssembly.checkpointPrimitives.orient 490 ++
      renameProgram (OB5.sig 490) (Rolling1588.Integer.packFirst base true 490) ++
      StairConcreteAssembly.checkpointPrimitives.pack 22) :=
  avoid10 _ _ (by decide +kernel)

theorem hdisj4 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (5 * 96))),
    q ∉ wires (StairReplay.movedForward
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1)))
        (5 * 96 + 5 + 1) (490 - (5 * 96 + 5) - 1) ++
      StairConcreteAssembly.checkpointPrimitives.orient 490 ++
      renameProgram (OB5.sig 490) (Rolling1588.Integer.packFirst base true 490) ++
      StairConcreteAssembly.checkpointPrimitives.pack 22) := by
  intro q hq hm
  have hseg : StairPhysicalPrimitives.segmentOf (480 + 1) = 32 := by decide
  have mv := moved_disj (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1)))
    (by rw [hseg]; exact StairFirstTickV3.midSegmentMap_injective 32 hB32) 96 490 (by decide) (by decide) q hq
  have tl := tail4 q hq
  simp only [List.append_assoc, wires_append, Finset.mem_union] at hm tl
  rcases hm with h | h
  · exact mv h
  · exact tl h

/-- PACK-CUT, entry row 4 (B 32 → 22, group d 36 / first 96 / 2 packets): the cut row has the
original row's run, from the row relation at the segment start. -/
theorem row4_cut (x : Nat) (X : Program) (rec : ∀ t, ReachEn x X t → ∀ r ∈ scratchT 32 22, t.basis (fieldPlace r) = false) (s t : State) (h : RowRelEn x 32 X s t)
    (m : List Bool) :
    ∃ m', run (PackCutEntry.cutRow 32 22 480 490 36 96 1) m (pullIn s) =
      run (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 36 96 (1 + 1)) m' (pullIn s) :=
  PackCutEntry.entry_row_cut 32 22 480 490 36 96 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    hF4 hdp4 hdisj4 (pullIn s)
    (fun t1 => legal_prefix x 32 22 (by decide) X rec s t h 4 (by decide) (by decide) (by decide)
      hvirt4 hntgt4 hlow4 hpk4 t1) m

/-! ## Entry row 5 -/

abbrev w22 : Nat → Wire := StairPhysicalPrimitives.midSegmentMap 22

theorem hB22 : 22 ∈ budgets := by decide

theorem hvirt5 : ∀ j : Fin 10, ¬ StairFirstTickV3.virtualSites 22 (History5.historyMap w22 (startFor 22 + 1 + 4 - 5) j) := by
  intro j
  have hinj := StairFirstTickV3.midSegmentMap_injective 22 hB22
  have hs : startFor 22 = 490 := by decide
  show ¬ StairFirstTickV3.VWire w22 (startFor 22) (w22 (History5.historyId (startFor 22 + 1 + 4 - 5) j))
  rw [hs]
  apply StairFirstTickV3.not_vwire w22 hinj 490
  have hj := j.isLt
  unfold StairFirstTickV3.Virt History5.historyId
  split_ifs <;> omega

set_option maxRecDepth 100000 in
theorem hntgt5 : ∀ j : Fin 10, ∀ ins ∈ TickRanges.tick w22 (startFor 22 + 1 + 4),
    tgtW ins ≠ History5.historyMap w22 (startFor 22 + 1 + 4 - 5) j := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hpk5 : ∀ j : Fin 10, History5.historyMap w22 (startFor 22 + 1 + 4 - 5) j < base 4000 := by
  decide +kernel

section
attribute [local irreducible] wires StairPhysicalPrimitives.unpack StairPhysicalPrimitives.tickForward TickRanges.tick StairReplay.movedForward

theorem hlow5 : ∀ q ∈ wires (StairPhysicalPrimitives.unpack 22 ++ StairPhysicalPrimitives.tickForward (startFor 22) ++
      StairPhysicalPrimitives.middleForward (startFor 22 + 1) 4 ++ TickRanges.tick w22 (startFor 22 + 1 + 4)),
      q < base 4000 := by
  intro q hq
  apply StairField2V3SegSpec.seg_low 22 12 (by decide) q
  have hs : startFor 22 = 490 := by decide
  have hN : startFor 12 = 500 := by decide
  rw [StairField2V3SegSpec.segP_eq]
  rw [hs] at hq ⊢
  rw [hN]
  have e1 : StairPhysicalPrimitives.middleForward (490 + 1) 4 = StairReplay.movedForward w22 (490 + 1) 4 := by
    unfold StairPhysicalPrimitives.middleForward; rfl
  have e2 : StairPhysicalPrimitives.middleForward (490 + 1) (500 - 490 - 1) =
      StairReplay.movedForward w22 (490 + 1) (4 + 1 + 4) := by
    unfold StairPhysicalPrimitives.middleForward; rfl
  rw [e1] at hq
  rw [e2, PackCutShape.movedForward_at]
  simp only [wires_append, Finset.mem_union] at hq ⊢
  tauto

end

theorem hF5 : Function.Injective (History5.historyMap
    (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (5 * 98)) := by
  have hseg : StairPhysicalPrimitives.segmentOf (490 + 1) = 22 := by decide
  rw [hseg]
  have hid : Function.Injective (History5.historyId (5 * 98)) := by decide
  exact (StairFirstTickV3.midSegmentMap_injective 22 hB22).comp hid

set_option maxRecDepth 200000 in
theorem hdp5 : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop 41)
      (StairConcreteAssembly.hostPlan.group true 41 98 (1 + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi 98))
        (Rolling1588.onPacket 98 Rolling1588.dp))) =
    renameProgram (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (5 * 98)))
      Rolling1588.dp := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem tail5 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (5 * 98))),
    q ∉ wires (StairConcreteAssembly.checkpointPrimitives.orient 500 ++
      renameProgram (OB5.sig 500) (Rolling1588.Integer.packFirst base true 500) ++
      StairConcreteAssembly.checkpointPrimitives.pack 12) :=
  avoid10 _ _ (by decide +kernel)

theorem hdisj5 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap
      (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (5 * 98))),
    q ∉ wires (StairReplay.movedForward
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1)))
        (5 * 98 + 5 + 1) (500 - (5 * 98 + 5) - 1) ++
      StairConcreteAssembly.checkpointPrimitives.orient 500 ++
      renameProgram (OB5.sig 500) (Rolling1588.Integer.packFirst base true 500) ++
      StairConcreteAssembly.checkpointPrimitives.pack 12) := by
  intro q hq hm
  have hseg : StairPhysicalPrimitives.segmentOf (490 + 1) = 22 := by decide
  have mv := moved_disj (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1)))
    (by rw [hseg]; exact StairFirstTickV3.midSegmentMap_injective 22 hB22) 98 500 (by decide) (by decide) q hq
  have tl := tail5 q hq
  simp only [List.append_assoc, wires_append, Finset.mem_union] at hm tl
  rcases hm with h | h
  · exact mv h
  · exact tl h

/-- PACK-CUT, entry row 5 (B 22 → 12, group d 41 / first 98 / 2 packets): the cut row has the
original row's run, from the row relation at the segment start. -/
theorem row5_cut (x : Nat) (X : Program) (rec : ∀ t, ReachEn x X t → ∀ r ∈ scratchT 22 12, t.basis (fieldPlace r) = false) (s t : State) (h : RowRelEn x 22 X s t)
    (m : List Bool) :
    ∃ m', run (PackCutEntry.cutRow 22 12 490 500 41 98 1) m (pullIn s) =
      run (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 41 98 (1 + 1)) m' (pullIn s) :=
  PackCutEntry.entry_row_cut 22 12 490 500 41 98 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    hF5 hdp5 hdisj5 (pullIn s)
    (fun t1 => legal_prefix x 22 12 (by decide) X rec s t h 4 (by decide) (by decide) (by decide)
      hvirt5 hntgt5 hlow5 hpk5 t1) m

end ECDSAAdd.Entrant.PackCutRows



set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.PackCutEntryChain
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairField2V3Replay StairField2V3Couple StairField2V3Entry
open StairField2V3ExitPlanR StairField2V3EntryPlanR
open StairLoanField7Transport StairLoanField7Values
open StairField2V3Delta StairField13V3 StairLoanField7RR

abbrev P : StairSchedule.StairPrimitives := StairConcreteAssembly.checkpointPrimitives
abbrev Lb : StairSchedule.StairLoans := StairConcrete.bestLoans

/-- Selected and reference prefixes before entry row `k` (rows start at pieces 4, 6, 8, 10, 12). -/
def selPre1 : Program := prefixW ++ (selJ0 P ++ (firstPkt ++ grpL Lb 0 1 84))
def refPre1 : Program := prefixW ++ (refJ0 ++ (firstPkt ++ grpL Lb 0 1 84))
def selPre2 : Program := selPre1 ++ (seg P 87 62 425 450 ++ grpL Lb 13 85 5)
def refPre2 : Program := refPre1 ++ grpL Lb 13 85 5
def selPre3 : Program := selPre2 ++ (seg P 62 47 450 465 ++ grpL Lb 22 90 3)
def refPre3 : Program := refPre2 ++ grpL Lb 22 90 3
def selPre4 : Program := selPre3 ++ (seg P 47 32 465 480 ++ grpL Lb 30 93 3)
def refPre4 : Program := refPre3 ++ grpL Lb 30 93 3
def selPre5 : Program := selPre4 ++ (seg P 32 22 480 490 ++ grpL Lb 36 96 2)
def refPre5 : Program := refPre4 ++ grpL Lb 36 96 2

theorem pre1 (x : Nat) (plan : EntryPlanR P x) (gsub : EntryGroupSub Lb) : CRel (fun s t => EntryPreX x s ∧ s = t) (RowRelEn x 87 (R1L Lb)) selPre1 refPre1 :=
  crel_append (crel_prefixX x) (crel_append (junctionEn plan.junction)
    (crel_append (sharedEn x 87 firstPkt R0 fp_awayX)
    (sharedEn x 87 _ (R0 ++ firstPkt) (away_of_sub _ _ _ gsub.1 (grp_away 87 (by decide) 1 84 (by decide))))))

theorem pre2 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb) : CRel (fun s t => EntryPreX x s ∧ s = t) (RowRelEn x 62 (R2L Lb)) selPre2 refPre2 :=
  crel_append (pre1 x plan gsub) (crel_sel_cons (stepLn V.r1 plan.seg0)
    (sharedEn x 62 _ (R1L Lb) (away_of_sub _ _ _ gsub.2.1 (grp_away 62 (by decide) 85 5 (by decide)))))

theorem pre3 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb) : CRel (fun s t => EntryPreX x s ∧ s = t) (RowRelEn x 47 (R3L Lb)) selPre3 refPre3 :=
  crel_append (pre2 x plan V gsub) (crel_sel_cons (stepLn V.r2 plan.seg1)
    (sharedEn x 47 _ (R2L Lb) (away_of_sub _ _ _ gsub.2.2.1 (grp_away 47 (by decide) 90 3 (by decide)))))

theorem pre4 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb) : CRel (fun s t => EntryPreX x s ∧ s = t) (RowRelEn x 32 (R4L Lb)) selPre4 refPre4 :=
  crel_append (pre3 x plan V gsub) (crel_sel_cons (stepLn V.r3 plan.seg2)
    (sharedEn x 32 _ (R3L Lb) (away_of_sub _ _ _ gsub.2.2.2.1 (grp_away 32 (by decide) 93 3 (by decide)))))

theorem pre5 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb) : CRel (fun s t => EntryPreX x s ∧ s = t) (RowRelEn x 22 (R5L Lb)) selPre5 refPre5 :=
  crel_append (pre4 x plan V gsub) (crel_sel_cons (stepLn V.r4 plan.seg3)
    (sharedEn x 22 _ (R4L Lb) (away_of_sub _ _ _ gsub.2.2.2.2.1 (grp_away 22 (by decide) 96 2 (by decide)))))


/-! ## Hosted prefixes are logical prefixes -/

abbrev hp : StairHostsSchedule.HostPlan := StairConcreteAssembly.hostPlan

theorem hosted_prefix_eq (pre : State → Prop) (c : EntrySlotsClean P hp pre) (n : Nat) :
    ∀ s, pre s → ∀ m, run (((entryPieces P hp).take n).map Piece.H).flatten m s =
      run (((entryPieces P hp).take n).map Piece.L).flatten m s := by
  apply run_eq_of_index pre ((entryPieces P hp).take n)
    (fun pc hpc => entryPieces_local P hp pc (List.mem_of_mem_take hpc))
  intro j hj
  have hjn : j < n := by simp only [List.length_take] at hj; omega
  have hjl : j < (entryPieces P hp).length := by simp only [List.length_take] at hj; omega
  have e1 : ((entryPieces P hp).take n).take j = (entryPieces P hp).take j := by
    rw [List.take_take]; congr 1; omega
  have e2 : ((entryPieces P hp).take n).take (j + 1) = (entryPieces P hp).take (j + 1) := by
    rw [List.take_take]; congr 1; omega
  have e3 : ((entryPieces P hp).take n)[j] = (entryPieces P hp)[j] := List.getElem_take
  rw [e1, e2, e3]
  exact c j hjl

theorem pref1 : (((entryPieces P hp).take 4).map Piece.L).flatten = selPre1 := by
  simp only [entryPieces, List.take, List.map, List.flatten, common, firstSlot, groupSlot, lowCommon,
    selPre1, prefixW, selJ0, firstPkt, grpL, liftF, ph, StairSchedule.firstPhase, StairSchedule.stackForward6,
    StairSchedule.fieldRename, StairSchedule.parityRename, rename_append', List.append_assoc,
    List.append_eq, List.append_nil]

theorem pref2 : (((entryPieces P hp).take 6).map Piece.L).flatten = selPre2 := by
  simp only [entryPieces, List.take, List.map, List.flatten, common, firstSlot, groupSlot, lowCommon,
    selPre1, selPre2, selPre3, selPre4, selPre5, prefixW, selJ0, firstPkt, grpL, seg, liftF, ph,
    StairSchedule.firstPhase, StairSchedule.stackForward6,
    StairSchedule.fieldRename, StairSchedule.parityRename, rename_append', List.append_assoc,
    List.append_eq, List.append_nil]

theorem pref3 : (((entryPieces P hp).take 8).map Piece.L).flatten = selPre3 := by
  simp only [entryPieces, List.take, List.map, List.flatten, common, firstSlot, groupSlot, lowCommon,
    selPre1, selPre2, selPre3, selPre4, selPre5, prefixW, selJ0, firstPkt, grpL, seg, liftF, ph,
    StairSchedule.firstPhase, StairSchedule.stackForward6,
    StairSchedule.fieldRename, StairSchedule.parityRename, rename_append', List.append_assoc,
    List.append_eq, List.append_nil]

theorem pref4 : (((entryPieces P hp).take 10).map Piece.L).flatten = selPre4 := by
  simp only [entryPieces, List.take, List.map, List.flatten, common, firstSlot, groupSlot, lowCommon,
    selPre1, selPre2, selPre3, selPre4, selPre5, prefixW, selJ0, firstPkt, grpL, seg, liftF, ph,
    StairSchedule.firstPhase, StairSchedule.stackForward6,
    StairSchedule.fieldRename, StairSchedule.parityRename, rename_append', List.append_assoc,
    List.append_eq, List.append_nil]

theorem pref5 : (((entryPieces P hp).take 12).map Piece.L).flatten = selPre5 := by
  simp only [entryPieces, List.take, List.map, List.flatten, common, firstSlot, groupSlot, lowCommon,
    selPre1, selPre2, selPre3, selPre4, selPre5, prefixW, selJ0, firstPkt, grpL, seg, liftF, ph,
    StairSchedule.firstPhase, StairSchedule.stackForward6,
    StairSchedule.fieldRename, StairSchedule.parityRename, rename_append', List.append_assoc,
    List.append_eq, List.append_nil]

/-! ## Row swaps inside the hosted kernel -/

/-- Tape-existential run equality behind a common prefix (the suffix may depend on the prefix's state). -/
theorem runeq_prefix (Pre X X' : Program) (s : State)
    (h : ∀ mP, ∀ m, ∃ m', run X' m (run Pre mP s) = run X m' (run Pre mP s)) :
    ∀ m, ∃ m', run (Pre ++ X') m s = run (Pre ++ X) m' s := by
  intro m
  let k := measurementCount Pre
  let pre := m.take k ++ List.replicate (k - (m.take k).length) false
  have hlen : pre.length = k := by
    simp only [pre, List.length_append, List.length_replicate, List.length_take]
    omega
  obtain ⟨m2, h2⟩ := h (m.take k) (m.drop k)
  refine ⟨pre ++ m2, ?_⟩
  rw [run_append Pre X', run_append Pre X, List.take_left' hlen, List.drop_left' hlen, h2]
  congr 1
  rw [run_pad_false]

theorem rowStart1 (x : Nat) (plan : EntryPlanR P x) (_V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (s : State) (hs : EntryPreX x s) (mP : List Bool) :
    ∃ t, RowRelEn x 87 (R1L Lb) (run (((entryPieces P hp).take 4).map Piece.H).flatten mP s) t := by
  rw [hosted_prefix_eq _ slots 4 s (entryPre_of_x x s hs) mP, pref1]
  obtain ⟨old, h⟩ := (pre1 x plan gsub) s s ⟨hs, rfl⟩ mP
  exact ⟨_, h⟩

theorem swap1 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (Rest : Program) (s : State) (hs : EntryPreX x s) :
    ∀ m, ∃ m', run ((((entryPieces P hp).take 4).map Piece.H).flatten ++
        (liftF (PackCutEntry.cutRow 87 62 425 450 13 85 4) ++ Rest)) m s =
      run ((((entryPieces P hp).take 4).map Piece.H).flatten ++
        (liftF (StairSchedule.forwardSegment P 87 62 425 450 ++
          StairHostsSchedule.hostedGroup hp true 13 85 (4 + 1)) ++ Rest)) m' s := by
  apply runeq_prefix
  intro mP
  obtain ⟨t, hrel⟩ := rowStart1 x plan V gsub slots s hs mP
  apply PackCutChain.runeq_append_right Rest
  apply PackCutChain.runeq_liftF
  intro m
  exact PackCutRows.row1_cut x (R1L Lb)
    (fun t' h' => StairField2V3RecScratch.rec0 t' (reach_of_x x R1 t' (V.r1 t' h'))) _ t hrel m

theorem rowStart2 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (s : State) (hs : EntryPreX x s) (mP : List Bool) :
    ∃ t, RowRelEn x 62 (R2L Lb) (run (((entryPieces P hp).take 6).map Piece.H).flatten mP s) t := by
  rw [hosted_prefix_eq _ slots 6 s (entryPre_of_x x s hs) mP, pref2]
  obtain ⟨old, h⟩ := (pre2 x plan V gsub) s s ⟨hs, rfl⟩ mP
  exact ⟨_, h⟩

theorem swap2 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (Rest : Program) (s : State) (hs : EntryPreX x s) :
    ∀ m, ∃ m', run ((((entryPieces P hp).take 6).map Piece.H).flatten ++
        (liftF (PackCutEntry.cutRow 62 47 450 465 22 90 2) ++ Rest)) m s =
      run ((((entryPieces P hp).take 6).map Piece.H).flatten ++
        (liftF (StairSchedule.forwardSegment P 62 47 450 465 ++
          StairHostsSchedule.hostedGroup hp true 22 90 (2 + 1)) ++ Rest)) m' s := by
  apply runeq_prefix
  intro mP
  obtain ⟨t, hrel⟩ := rowStart2 x plan V gsub slots s hs mP
  apply PackCutChain.runeq_append_right Rest
  apply PackCutChain.runeq_liftF
  intro m
  exact PackCutRows.row2_cut x (R2L Lb)
    (fun t' h' => StairField2V3RecScratch.rec1 t' (reach_of_x x R2 t' (V.r2 t' h'))) _ t hrel m

theorem rowStart3 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (s : State) (hs : EntryPreX x s) (mP : List Bool) :
    ∃ t, RowRelEn x 47 (R3L Lb) (run (((entryPieces P hp).take 8).map Piece.H).flatten mP s) t := by
  rw [hosted_prefix_eq _ slots 8 s (entryPre_of_x x s hs) mP, pref3]
  obtain ⟨old, h⟩ := (pre3 x plan V gsub) s s ⟨hs, rfl⟩ mP
  exact ⟨_, h⟩

theorem swap3 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (Rest : Program) (s : State) (hs : EntryPreX x s) :
    ∀ m, ∃ m', run ((((entryPieces P hp).take 8).map Piece.H).flatten ++
        (liftF (PackCutEntry.cutRow 47 32 465 480 30 93 2) ++ Rest)) m s =
      run ((((entryPieces P hp).take 8).map Piece.H).flatten ++
        (liftF (StairSchedule.forwardSegment P 47 32 465 480 ++
          StairHostsSchedule.hostedGroup hp true 30 93 (2 + 1)) ++ Rest)) m' s := by
  apply runeq_prefix
  intro mP
  obtain ⟨t, hrel⟩ := rowStart3 x plan V gsub slots s hs mP
  apply PackCutChain.runeq_append_right Rest
  apply PackCutChain.runeq_liftF
  intro m
  exact PackCutRows.row3_cut x (R3L Lb)
    (fun t' h' => StairField2V3RecScratch.rec2 t' (reach_of_x x R3 t' (V.r3 t' h'))) _ t hrel m

theorem rowStart4 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (s : State) (hs : EntryPreX x s) (mP : List Bool) :
    ∃ t, RowRelEn x 32 (R4L Lb) (run (((entryPieces P hp).take 10).map Piece.H).flatten mP s) t := by
  rw [hosted_prefix_eq _ slots 10 s (entryPre_of_x x s hs) mP, pref4]
  obtain ⟨old, h⟩ := (pre4 x plan V gsub) s s ⟨hs, rfl⟩ mP
  exact ⟨_, h⟩

theorem swap4 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (Rest : Program) (s : State) (hs : EntryPreX x s) :
    ∀ m, ∃ m', run ((((entryPieces P hp).take 10).map Piece.H).flatten ++
        (liftF (PackCutEntry.cutRow 32 22 480 490 36 96 1) ++ Rest)) m s =
      run ((((entryPieces P hp).take 10).map Piece.H).flatten ++
        (liftF (StairSchedule.forwardSegment P 32 22 480 490 ++
          StairHostsSchedule.hostedGroup hp true 36 96 (1 + 1)) ++ Rest)) m' s := by
  apply runeq_prefix
  intro mP
  obtain ⟨t, hrel⟩ := rowStart4 x plan V gsub slots s hs mP
  apply PackCutChain.runeq_append_right Rest
  apply PackCutChain.runeq_liftF
  intro m
  exact PackCutRows.row4_cut x (R4L Lb)
    (fun t' h' => StairField2V3RecScratch.rec3 t' (reach_of_x x R4 t' (V.r4 t' h'))) _ t hrel m

theorem rowStart5 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (s : State) (hs : EntryPreX x s) (mP : List Bool) :
    ∃ t, RowRelEn x 22 (R5L Lb) (run (((entryPieces P hp).take 12).map Piece.H).flatten mP s) t := by
  rw [hosted_prefix_eq _ slots 12 s (entryPre_of_x x s hs) mP, pref5]
  obtain ⟨old, h⟩ := (pre5 x plan V gsub) s s ⟨hs, rfl⟩ mP
  exact ⟨_, h⟩

theorem swap5 (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (Rest : Program) (s : State) (hs : EntryPreX x s) :
    ∀ m, ∃ m', run ((((entryPieces P hp).take 12).map Piece.H).flatten ++
        (liftF (PackCutEntry.cutRow 22 12 490 500 41 98 1) ++ Rest)) m s =
      run ((((entryPieces P hp).take 12).map Piece.H).flatten ++
        (liftF (StairSchedule.forwardSegment P 22 12 490 500 ++
          StairHostsSchedule.hostedGroup hp true 41 98 (1 + 1)) ++ Rest)) m' s := by
  apply runeq_prefix
  intro mP
  obtain ⟨t, hrel⟩ := rowStart5 x plan V gsub slots s hs mP
  apply PackCutChain.runeq_append_right Rest
  apply PackCutChain.runeq_liftF
  intro m
  exact PackCutRows.row5_cut x (R5L Lb)
    (fun t' h' => StairField2V3RecScratch.rec4 t' (reach_of_x x R5 t' (V.r5 t' h'))) _ t hrel m

/-! ## The cut hosted entry kernel -/

/-- The hosted entry kernel with the five PACK-CUT rows. -/
def cutKernel : Program :=
  (((entryPieces P hp).take 4).map Piece.H).flatten ++
    (liftF (PackCutEntry.cutRow 87 62 425 450 13 85 4) ++
    (liftF (PackCutEntry.cutRow 62 47 450 465 22 90 2) ++
    (liftF (PackCutEntry.cutRow 47 32 465 480 30 93 2) ++
    (liftF (PackCutEntry.cutRow 32 22 480 490 36 96 1) ++
    (liftF (PackCutEntry.cutRow 22 12 490 500 41 98 1) ++
    (((entryPieces P hp).drop 14).map Piece.H).flatten)))))

theorem take_row1 (X : Program) :
    (((entryPieces P hp).take 4).map Piece.H).flatten ++ (liftF (StairSchedule.forwardSegment P 87 62 425 450 ++ StairHostsSchedule.hostedGroup hp true 13 85 (4 + 1)) ++ X) =
      (((entryPieces P hp).take 6).map Piece.H).flatten ++ X := by
  simp only [entryPieces, List.take, List.drop, List.map, List.flatten, common, firstSlot, groupSlot, lowCommon, liftF,
    StairSchedule.fieldRename, StairSchedule.parityRename, rename_append', List.append_assoc, List.append_eq, List.append_nil]

theorem take_row2 (X : Program) :
    (((entryPieces P hp).take 6).map Piece.H).flatten ++ (liftF (StairSchedule.forwardSegment P 62 47 450 465 ++ StairHostsSchedule.hostedGroup hp true 22 90 (2 + 1)) ++ X) =
      (((entryPieces P hp).take 8).map Piece.H).flatten ++ X := by
  simp only [entryPieces, List.take, List.drop, List.map, List.flatten, common, firstSlot, groupSlot, lowCommon, liftF,
    StairSchedule.fieldRename, StairSchedule.parityRename, rename_append', List.append_assoc, List.append_eq, List.append_nil]

theorem take_row3 (X : Program) :
    (((entryPieces P hp).take 8).map Piece.H).flatten ++ (liftF (StairSchedule.forwardSegment P 47 32 465 480 ++ StairHostsSchedule.hostedGroup hp true 30 93 (2 + 1)) ++ X) =
      (((entryPieces P hp).take 10).map Piece.H).flatten ++ X := by
  simp only [entryPieces, List.take, List.drop, List.map, List.flatten, common, firstSlot, groupSlot, lowCommon, liftF,
    StairSchedule.fieldRename, StairSchedule.parityRename, rename_append', List.append_assoc, List.append_eq, List.append_nil]

theorem take_row4 (X : Program) :
    (((entryPieces P hp).take 10).map Piece.H).flatten ++ (liftF (StairSchedule.forwardSegment P 32 22 480 490 ++ StairHostsSchedule.hostedGroup hp true 36 96 (1 + 1)) ++ X) =
      (((entryPieces P hp).take 12).map Piece.H).flatten ++ X := by
  simp only [entryPieces, List.take, List.drop, List.map, List.flatten, common, firstSlot, groupSlot, lowCommon, liftF,
    StairSchedule.fieldRename, StairSchedule.parityRename, rename_append', List.append_assoc, List.append_eq, List.append_nil]

theorem take_row5 (X : Program) :
    (((entryPieces P hp).take 12).map Piece.H).flatten ++ (liftF (StairSchedule.forwardSegment P 22 12 490 500 ++ StairHostsSchedule.hostedGroup hp true 41 98 (1 + 1)) ++ X) =
      (((entryPieces P hp).take 14).map Piece.H).flatten ++ X := by
  simp only [entryPieces, List.take, List.drop, List.map, List.flatten, common, firstSlot, groupSlot, lowCommon, liftF,
    StairSchedule.fieldRename, StairSchedule.parityRename, rename_append', List.append_assoc, List.append_eq, List.append_nil]

theorem hosted_split : StairHostsSchedule.entryKernel P hp =
    (((entryPieces P hp).take 14).map Piece.H).flatten ++ (((entryPieces P hp).drop 14).map Piece.H).flatten := by
  rw [← entryPieces_hosted, ← List.flatten_append, ← List.map_append, List.take_append_drop]

/-- Transitivity of tape-existential run equality. -/
theorem runeq_trans {A B C : Program} {s : State}
    (h1 : ∀ m, ∃ m', run A m s = run B m' s) (h2 : ∀ m, ∃ m', run B m s = run C m' s) :
    ∀ m, ∃ m', run A m s = run C m' s := by
  intro m
  obtain ⟨m1, e1⟩ := h1 m
  obtain ⟨m2, e2⟩ := h2 m1
  exact ⟨m2, e1.trans e2⟩

/-- **PACK-CUT, entry rows, any tail:** behind the hosted pieces 0–3, the five cut rows followed by any `Z` run
like the original rows followed by `Z`, on every pinned entry state. -/
theorem entry_cut_runeq_gen (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (Z : Program) (s : State) (hs : EntryPreX x s) :
    ∀ m, ∃ m', run ((((entryPieces P hp).take 4).map Piece.H).flatten ++
        (liftF (PackCutEntry.cutRow 87 62 425 450 13 85 4) ++ (liftF (PackCutEntry.cutRow 62 47 450 465 22 90 2) ++ (liftF (PackCutEntry.cutRow 47 32 465 480 30 93 2) ++ (liftF (PackCutEntry.cutRow 32 22 480 490 36 96 1) ++ (liftF (PackCutEntry.cutRow 22 12 490 500 41 98 1) ++ Z)))))) m s =
      run ((((entryPieces P hp).take 14).map Piece.H).flatten ++ Z) m' s := by
  have s1 := swap1 x plan V gsub slots (liftF (PackCutEntry.cutRow 62 47 450 465 22 90 2) ++ (liftF (PackCutEntry.cutRow 47 32 465 480 30 93 2) ++ (liftF (PackCutEntry.cutRow 32 22 480 490 36 96 1) ++ (liftF (PackCutEntry.cutRow 22 12 490 500 41 98 1) ++ Z)))) s hs
  have s2 := swap2 x plan V gsub slots (liftF (PackCutEntry.cutRow 47 32 465 480 30 93 2) ++ (liftF (PackCutEntry.cutRow 32 22 480 490 36 96 1) ++ (liftF (PackCutEntry.cutRow 22 12 490 500 41 98 1) ++ Z))) s hs
  have s3 := swap3 x plan V gsub slots (liftF (PackCutEntry.cutRow 32 22 480 490 36 96 1) ++ (liftF (PackCutEntry.cutRow 22 12 490 500 41 98 1) ++ Z)) s hs
  have s4 := swap4 x plan V gsub slots (liftF (PackCutEntry.cutRow 22 12 490 500 41 98 1) ++ Z) s hs
  have s5 := swap5 x plan V gsub slots Z s hs
  rw [take_row1] at s1
  rw [take_row2] at s2
  rw [take_row3] at s3
  rw [take_row4] at s4
  rw [take_row5] at s5
  exact runeq_trans s1 (runeq_trans s2 (runeq_trans s3 (runeq_trans s4 s5)))

/-- **PACK-CUT, entry kernel:** on every pinned entry state the cut hosted kernel runs like the hosted kernel. -/
theorem entry_cut_runeq (x : Nat) (plan : EntryPlanR P x) (V : EntryReachTransportR Lb x) (gsub : EntryGroupSub Lb)
    (slots : EntrySlotsClean P hp StairConcreteAssembly.EntryPre) (s : State) (hs : EntryPreX x s) :
    ∀ m, ∃ m', run cutKernel m s = run (StairHostsSchedule.entryKernel P hp) m' s := by
  rw [hosted_split]
  exact entry_cut_runeq_gen x plan V gsub slots _ s hs

end ECDSAAdd.Entrant.PackCutEntryChain


/-! ## Row counts and wires -/

namespace ECDSAAdd.Entrant.PackCutCounts
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed PackCutRow PackCutShape PackCutTrip PackCutEntry

theorem tc_ep : toffoliCount Rolling1588.ep = 6 := by decide
theorem tc_dp : toffoliCount Rolling1588.dp = 7 := by decide
theorem mc_epdp : measurementCount Rolling1588.ep + measurementCount Rolling1588.dp = 5 := by decide

/-- The original row is the cut row with the placed `ep` (after the due write's prefix) and the placed `dp`
(at the group's head) put back. -/
theorem row_shape (B N s f d first c : Nat)
    (h1 : s + 1 ≤ 5 * first + 5) (h2 : 5 * first + 5 + 1 ≤ f)
    (h5 : 5 * first + 5 ≠ 5) (hdue : History5.packDue (5 * first + 5) = true) (hf0 : first ≠ 0)
    (hdp : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
        (StairConcreteAssembly.hostPlan.group true d first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.dp))) =
      renameProgram (MeasuredCodec5.label (History5.historyMap
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first)))
        Rolling1588.dp) :
    ∃ X M Y : Program,
      StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives B N s f ++
          StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true d first (c + 1) =
        X ++ renameProgram (MeasuredCodec5.label (History5.historyMap
          (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first)))
          Rolling1588.ep ++ M ++
          renameProgram (MeasuredCodec5.label (History5.historyMap
            (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first)))
            Rolling1588.dp ++ Y ∧
      cutRow B N s f d first c = X ++ M ++ Y := by
  let p := StairConcreteAssembly.checkpointPrimitives
  let w := StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))
  let F := History5.historyMap w (5 * first)
  let A0 := p.unpack B ++ p.tickForward s ++ StairReplay.movedForward w (s + 1) (5 * first + 5 - (s + 1)) ++
    TickRanges.tick w (5 * first + 5)
  let E138' := renameProgram (MeasuredCodec5.label F) E138
  let Mrow := StairReplay.movedForward w (5 * first + 5 + 1) (f - (5 * first + 5) - 1) ++ p.orient f ++
    renameProgram (OB5.sig f) (Rolling1588.Integer.packFirst base true f) ++ p.pack N
  let Brow := StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
      (StairConcreteAssembly.hostPlan.group true d first (c + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first)) (basePacketTail d first)) ++
       renameProgram (OB5.sig 511) (StairGroups.groups true d (first + 1) c))
  refine ⟨A0 ++ E138', Mrow, Brow, ?_, ?_⟩
  · rw [forwardSegment_row B N s f first h1 h2 h5 hdue hf0, hostedGroup_true_head, hdp]
    simp only [A0, E138', Mrow, Brow, p, w, F, List.append_assoc]
  · simp only [cutRow, A0, E138', Mrow, Brow, p, w, F, List.append_assoc]

/-- Each cut row has 13 Toffolis (the placed `ep` 6 + `dp` 7) and 5 measurements fewer. -/
theorem row_counts (B N s f d first c : Nat)
    (h1 : s + 1 ≤ 5 * first + 5) (h2 : 5 * first + 5 + 1 ≤ f)
    (h5 : 5 * first + 5 ≠ 5) (hdue : History5.packDue (5 * first + 5) = true) (hf0 : first ≠ 0)
    (hdp : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
        (StairConcreteAssembly.hostPlan.group true d first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.dp))) =
      renameProgram (MeasuredCodec5.label (History5.historyMap
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first)))
        Rolling1588.dp) :
    toffoliCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives B N s f ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true d first (c + 1)) =
      toffoliCount (cutRow B N s f d first c) + 13 ∧
    measurementCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives B N s f ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true d first (c + 1)) =
      measurementCount (cutRow B N s f d first c) + 5 := by
  obtain ⟨X, M, Y, ho, hc⟩ := row_shape B N s f d first c h1 h2 h5 hdue hf0 hdp
  rw [ho, hc]
  simp only [toffoliCount_append, measurementCount_append, (renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2, tc_ep, tc_dp]
  have := mc_epdp
  constructor <;> omega


theorem row1_counts :
    toffoliCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 13 85 (4 + 1)) =
      toffoliCount (cutRow 87 62 425 450 13 85 4) + 13 ∧
    measurementCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 13 85 (4 + 1)) =
      measurementCount (cutRow 87 62 425 450 13 85 4) + 5 :=
  row_counts 87 62 425 450 13 85 4 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp1

theorem row2_counts :
    toffoliCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 22 90 (2 + 1)) =
      toffoliCount (cutRow 62 47 450 465 22 90 2) + 13 ∧
    measurementCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 22 90 (2 + 1)) =
      measurementCount (cutRow 62 47 450 465 22 90 2) + 5 :=
  row_counts 62 47 450 465 22 90 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp2

theorem row3_counts :
    toffoliCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 30 93 (2 + 1)) =
      toffoliCount (cutRow 47 32 465 480 30 93 2) + 13 ∧
    measurementCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 30 93 (2 + 1)) =
      measurementCount (cutRow 47 32 465 480 30 93 2) + 5 :=
  row_counts 47 32 465 480 30 93 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp3

theorem row4_counts :
    toffoliCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 36 96 (1 + 1)) =
      toffoliCount (cutRow 32 22 480 490 36 96 1) + 13 ∧
    measurementCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 36 96 (1 + 1)) =
      measurementCount (cutRow 32 22 480 490 36 96 1) + 5 :=
  row_counts 32 22 480 490 36 96 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp4

theorem row5_counts :
    toffoliCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 41 98 (1 + 1)) =
      toffoliCount (cutRow 22 12 490 500 41 98 1) + 13 ∧
    measurementCount (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 41 98 (1 + 1)) =
      measurementCount (cutRow 22 12 490 500 41 98 1) + 5 :=
  row_counts 22 12 490 500 41 98 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp5

end ECDSAAdd.Entrant.PackCutCounts

/-! ## Sublists: each cut row is a sublist of its original row -/

namespace ECDSAAdd.Entrant.PackCutSub
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed PackCutEntry

theorem wires_sub {P Q : Program} (h : P.Sublist Q) : ∀ q ∈ wires P, q ∈ wires Q := by
  intro q hq
  obtain ⟨i, hi, hw⟩ := (LaneI.mem_wires_iff P q).1 hq
  exact (LaneI.mem_wires_iff Q q).2 ⟨i, h.subset hi, hw⟩

theorem gp_sub {P Q : Program} (h : P.Sublist Q) (hq : GatePhysical Q) : GatePhysical P :=
  fun i hi => hq i (h.subset hi)

theorem sound_sub {P Q : Program} (h : P.Sublist Q) (hq : StairPhysicalV3.Sound Q) :
    StairPhysicalV3.Sound P :=
  ⟨gp_sub h hq.physical, fun q hw => hq.good q (wires_sub h q hw)⟩

theorem rename_sub (f : Wire → Wire) {P Q : Program} (h : P.Sublist Q) :
    (renameProgram f P).Sublist (renameProgram f Q) :=
  h.map _

theorem row_sub (B N s f d first c : Nat)
    (h1 : s + 1 ≤ 5 * first + 5) (h2 : 5 * first + 5 + 1 ≤ f)
    (h5 : 5 * first + 5 ≠ 5) (hdue : History5.packDue (5 * first + 5) = true) (hf0 : first ≠ 0)
    (hdp : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
        (StairConcreteAssembly.hostPlan.group true d first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.dp))) =
      renameProgram (MeasuredCodec5.label (History5.historyMap
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first)))
        Rolling1588.dp) :
    (cutRow B N s f d first c).Sublist
      (StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives B N s f ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true d first (c + 1)) := by
  obtain ⟨X, M, Y, ho, hc⟩ := PackCutCounts.row_shape B N s f d first c h1 h2 h5 hdue hf0 hdp
  rw [ho, hc]
  simp only [List.append_assoc]
  exact (List.Sublist.refl X).append
    (((List.Sublist.refl M).append (List.sublist_append_right _ _)).trans (List.sublist_append_right _ _))

theorem rows_sub0 (Z : Program) :
    (cutRow 87 62 425 450 13 85 4 ++ (cutRow 62 47 450 465 22 90 2 ++ (cutRow 47 32 465 480 30 93 2 ++
      (cutRow 32 22 480 490 36 96 1 ++ (cutRow 22 12 490 500 41 98 1 ++ Z))))).Sublist
    ((StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 13 85 (4 + 1)) ++
      ((StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 22 90 (2 + 1)) ++
      ((StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 30 93 (2 + 1)) ++
      ((StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 36 96 (1 + 1)) ++
      ((StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 41 98 (1 + 1)) ++ Z))))) :=
  (row_sub 87 62 425 450 13 85 4 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp1).append
    ((row_sub 62 47 450 465 22 90 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp2).append
    ((row_sub 47 32 465 480 30 93 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp3).append
    ((row_sub 32 22 480 490 36 96 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp4).append
    ((row_sub 22 12 490 500 41 98 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp5).append
      (List.Sublist.refl Z)))))

theorem rows_sub (A Z : Program) :
    (A ++ (cutRow 87 62 425 450 13 85 4 ++ (cutRow 62 47 450 465 22 90 2 ++ (cutRow 47 32 465 480 30 93 2 ++
      (cutRow 32 22 480 490 36 96 1 ++ (cutRow 22 12 490 500 41 98 1 ++ Z)))))).Sublist
    (A ++ ((StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 13 85 (4 + 1)) ++
      ((StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 22 90 (2 + 1)) ++
      ((StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 30 93 (2 + 1)) ++
      ((StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 36 96 (1 + 1)) ++
      ((StairSchedule.forwardSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500 ++
        StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan true 41 98 (1 + 1)) ++ Z)))))) :=
  (List.Sublist.refl A).append (rows_sub0 Z)

end ECDSAAdd.Entrant.PackCutSub
