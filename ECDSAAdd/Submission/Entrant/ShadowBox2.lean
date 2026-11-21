import ECDSAAdd.Submission.Entrant.ShadowGeometry

/-! Shadow7 leave footprints (leave-move, for build-leaves / build-chain): Window's `Partial` leaveBox2 box and the
swap-cell preservation (`swaps_kept`) at the seven-bit shadow coordinates. Generated from the stock Window blocks
(0a4223d) by helpers/leave-move/shadow/gen_box2.py; statements are the stock ones with `Shadow7.` names. Shadow
changes: the store-chain sites come from `Shadow7.storeW_cases` (three cases, above the anchor when `e0P ≤ 1573+k`),
the adjust's pool is bounded through `Shadow7.pool_cases` (it runs past `e0P+20`: 1725 > 1716 at s = 255), and
`sbP ≥ 54`. Stock helpers reused unchanged: `leaveBox`, `hfree`, `swap_not_free`, `notarget_of_free`, `tgtOK`, `segT`,
`swap_not_ok`, `keep_append`, `rail14`, `allW_iff_flat(2)`, `start_win`, `tags_range`. -/

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open GateMirror Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

/-- The scratch: `1556 .. min 1812 (2069-s)`. -/
theorem box2_S {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (a : 1556 ≤ q) (b : q ≤ 1812) (c : q + s ≤ 2069) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  unfold Shadow7.leaveBox2; omega
/-- The A columns `a0-1 .. a0+17`. -/
theorem box2_A {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (a : Shadow7.a0P s ≤ q + 1) (b : q ≤ Shadow7.a0P s + 17) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  have r14 := rail14 s
  unfold Shadow7.leaveBox2; omega
/-- The B rail from the low columns up: `b0-1 .. 785 + R`. -/
theorem box2_B {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (a : Shadow7.b0P s ≤ q + 1) (b : q ≤ 785 + railP s) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  unfold Shadow7.leaveBox2; omega
/-- The history letters `s+16 .. s+30`. -/
theorem box2_H {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (a : s + 16 ≤ q) (b : q ≤ s + 30) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  have r14 := rail14 s
  unfold Shadow7.leaveBox2; omega
/-- The history cells that the frame does not move: `s+1044 .. s+1058`, at most 1300. -/
theorem box2_C {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (a : 1044 + s ≤ q) (b : q ≤ 1058 + s) (c : q ≤ 1300) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  unfold Shadow7.leaveBox2; omega

/-- Boolean test of the five intervals (scratch first: most wires of the fixed segments are there). -/
def inBox2B (s q : Nat) : Bool :=
  (Nat.ble 1556 q && (Nat.ble q 1812 && Nat.ble (q + s) 2069)) ||
  ((Nat.ble (Shadow7.a0P s) (q + 1) && Nat.ble q (Shadow7.a0P s + 17)) ||
  ((Nat.ble (Shadow7.b0P s) (q + 1) && Nat.ble q (785 + railP s)) ||
  ((Nat.ble (s + 16) q && Nat.ble q (s + 30)) ||
  (Nat.ble (1044 + s) q && (Nat.ble q (1058 + s) && Nat.ble q 1300)))))

theorem inBox2B_sound {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (h : Shadow7.inBox2B s q = true) : Shadow7.leaveBox2 s q := by
  unfold Shadow7.inBox2B at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  rcases h with h | h | h | h | h
  · exact Shadow7.box2_S h1 h2 q h.1 h.2.1 h.2.2
  · exact Shadow7.box2_A h1 h2 q h.1 h.2
  · exact Shadow7.box2_B h1 h2 q h.1 h.2
  · exact Shadow7.box2_H h1 h2 q h.1 h.2
  · exact Shadow7.box2_C h1 h2 q h.1 h.2.1 h.2.2

def segBox2 (s : Nat) (gs : List Gate) : Bool := gs.all (fun g => g.wires.all (Shadow7.inBox2B s))
theorem allW_of_segBox2 {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) {gs : List Gate} (h : Shadow7.segBox2 s gs = true) :
    AllW (Shadow7.leaveBox2 s) gs := by
  intro g hg q hq
  unfold Shadow7.segBox2 at h; rw [List.all_eq_true] at h
  have := h g hg; rw [List.all_eq_true] at this
  exact Shadow7.inBox2B_sound h1 h2 q (this q hq)

theorem sig_box2 {s c : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (hc1 : 1044 ≤ c) (hc2 : c ≤ 1058) :
    Shadow7.leaveBox2 s (OB5.sig (s+14) (s+c)) := by
  have e := Shadow7.sig_hist h1 h2 hc1 hc2
  have r := Shadow7.rail_win h1 h2
  rcases e with ⟨e, le⟩ | ⟨e, lo, hi⟩
  · rw [e]; exact Shadow7.box2_C h1 h2 _ (by omega) (by omega) le
  · rw [e]; exact Shadow7.box2_S h1 h2 _ (by omega) hi (by omega)

theorem fixed_box2 : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    Shadow7.segBox2 (start j) (leaveFix0 (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)) ++
      leaveFix2 (start j) (Shadow7.sbP (start j)) ++ leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      leaveFix5 (start j) (Shadow7.sbP (start j)) ++ leaveFix8 (start j) (Shadow7.sbP (start j)) ++ leaveFix10 (start j) (Shadow7.sbP (start j)) ++
      leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j)) = true := by
  decide +kernel

section Main
attribute [local irreducible] Shadow7.leaveBox2

theorem leaveOps_box2 (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    AllW (Shadow7.leaveBox2 (start j)) (Shadow7.leaveOps (start j)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have fb := Shadow7.allW_of_segBox2 w1 w2 (Shadow7.fixed_box2 j h0 h1)
  simp only [allW_append_iff] at fb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, f4⟩, f5⟩, f8⟩, f10⟩, f11⟩, f12⟩, fl⟩ := fb
  generalize hs : start j = s at *
  have r := Shadow7.rail_win w1 w2
  have r14 := rail14 s
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have hL : 10 ≤ Shadow7.lowsP s ∧ Shadow7.lowsP s ≤ 11 := by ((try unfold Wire at *); omega)
  have boxS : ∀ q : Nat, 1556 ≤ q → q ≤ 1812 → q + s ≤ 2069 → Shadow7.leaveBox2 s q := fun q => Shadow7.box2_S w1 w2 q
  have boxA : ∀ q : Nat, Shadow7.a0P s ≤ q + 1 → q ≤ Shadow7.a0P s + 17 → Shadow7.leaveBox2 s q := fun q => Shadow7.box2_A w1 w2 q
  have boxB : ∀ q : Nat, Shadow7.b0P s ≤ q + 1 → q ≤ 785 + railP s → Shadow7.leaveBox2 s q := fun q => Shadow7.box2_B w1 w2 q
  have boxH : ∀ q : Nat, s + 16 ≤ q → q ≤ s + 30 → Shadow7.leaveBox2 s q := fun q => Shadow7.box2_H w1 w2 q
  have bank : ∀ i, i < Shadow7.wpP s + 15 → Shadow7.leaveBox2 s (Shadow7.bankW s i) := by
    intro i hi
    rcases Shadow7.bank_cases w1 w2 hi with ⟨a, e⟩ | ⟨a, b, e, c, d⟩ | ⟨a, e, c⟩
    · rw [e]; apply boxS <;> omega
    · rw [e]; apply boxB <;> omega
    · rw [e]; apply boxS <;> omega
  have tags : ∀ i, i < 16 → Shadow7.leaveBox2 s (tagsP.getD i 0) := by
    intro i hi; have t := tags_range i hi; apply boxS <;> ((try unfold Wire at *); omega)
  have aside : ∀ i, i ≤ 18 → Shadow7.leaveBox2 s (Shadow7.a0P s - 1 + i) := by intro i hi; apply boxA <;> omega
  have bside : ∀ i, i ≤ 12 → Shadow7.leaveBox2 s (Shadow7.b0P s - 1 + i) := by intro i hi; apply boxB <;> omega
  have scr : ∀ q, 1556 ≤ q → q ≤ Shadow7.e0P s + 20 → Shadow7.leaveBox2 s q := by intro q a b; apply boxS <;> ((try unfold Wire at *); omega)
  have ctl : ∀ (xs : List Wire), (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1614) → ∀ x ∈ xs, Shadow7.leaveBox2 s x :=
    fun xs h x hx => scr x (h x hx).1 (by have := (h x hx).2; (try unfold Wire at *); omega)
  have adj : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveAdjust s) := by
    unfold Shadow7.leaveAdjust
    refine allW_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by ((try unfold Wire at *); omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have p := Shadow7.pool_cases (i := i) w1 w2; apply boxS <;> ((try unfold Wire at *); omega)
  have bar : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveBarrel s) := by
    unfold Shadow7.leaveBarrel
    have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ Shadow7.wpP s + 15 → (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1614) →
        AllW (Shadow7.leaveBox2 s) (stageG 1613 (Shadow7.bankW s) xs d n) :=
      fun xs d n hn hx => allW_stageG _ _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (ctl xs hx)
        (fun i hi => ⟨bank i (by ((try unfold Wire at *); omega)), bank (i+d) (by ((try unfold Wire at *); omega))⟩)
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    exact allW_append (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide)) (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
  have joi : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveJoin s) := by
    unfold Shadow7.leaveJoin
    refine allW_append (allW_digitsG _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ _
      (fun i _ hi => ⟨tags i (by ((try unfold Wire at *); omega)), ?_, ?_⟩)) (allW_wordG _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ (fun r hr => ?_))
    · have := aside (i+1) (by ((try unfold Wire at *); omega)); rwa [show Shadow7.a0P s - 1 + (i+1) = Shadow7.a0P s + i by ((try unfold Wire at *); omega)] at this
    · have := aside (i+2) (by ((try unfold Wire at *); omega)); rwa [show Shadow7.a0P s - 1 + (i+2) = Shadow7.a0P s + (i+1) by ((try unfold Wire at *); omega)] at this
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr; rw [List.mem_range] at hi
      refine ⟨fun w hw => ?_, ?_, bank i (by ((try unfold Wire at *); omega))⟩
      · dsimp only at hw; split at hw
        · cases hw; exact tags i (by ((try unfold Wire at *); omega))
        · cases hw
      · have := aside (i+1) (by ((try unfold Wire at *); omega)); dsimp only; rwa [show Shadow7.a0P s - 1 + (i+1) = Shadow7.a0P s + i by ((try unfold Wire at *); omega)] at this
  have lr : AllW (Shadow7.leaveBox2 s) (Shadow7.lowRest s) := by
    unfold Shadow7.lowRest
    refine allW_append (allW_append (allW_append (allW_append ?_ (allW_xsG _ ?_)) (allW_addG _ _ _ ?_ ?_ ?_))
      (allW_xsG _ ?_)) ?_
    · refine allW_map _ _ (fun i hi q hq => ?_); rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl|rfl <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    all_goals try (intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega)))
    · first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    · rw [allW_iff_flat2]
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
  have sm : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveStoreMapped s) := by
    simp only [Shadow7.leaveStoreMapped]
    have lit : ∀ (gs : List Gate), (∀ q ∈ gs.flatMap Gate.wires, Shadow7.leaveBox2 s q) → AllW (Shadow7.leaveBox2 s) gs :=
      fun gs h => allW_iff_flat2.mpr h
    have hi : ∀ y ∈ (List.range (Shadow7.wpP s + 15 - Shadow7.lowsP s)).map (fun i => Shadow7.bankW s (Shadow7.lowsP s + i)), Shadow7.leaveBox2 s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank _ (by ((try unfold Wire at *); omega))
    have s2 : ∀ y ∈ (List.range (Shadow7.lowsP s + 1)).map (Shadow7.b0P s - 1 + ·), Shadow7.leaveBox2 s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bside i (by ((try unfold Wire at *); omega))
    refine allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append
      ?_ (allW_xsG _ hi)) ?_) (allW_xsG _ (fun y h => hi y (List.mem_reverse.mp h)))) ?_) (allW_xsG _ s2)) ?_)
      (allW_xsG _ (fun y h => s2 y (List.mem_reverse.mp h)))) ?_
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        have sc := Shadow7.storeW_cases w1 w2 (Shadow7.wpP s + 15 - Shadow7.lowsP s + 1)
        split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
      · have sc := Shadow7.storeW_cases w1 w2 k; first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
      · dsimp only; split
        · first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
        · exact bank _ (by ((try unfold Wire at *); omega))
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
      · first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
      · first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
  have lc : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveLowClose s) := by
    simp only [Shadow7.leaveLowClose]
    refine allW_append (allW_append (allW_xsG _ (fun y hy => ?_)) (allW_map _ _ (fun i hi q hq => ?_)))
      (allW_flatMap _ _ (fun i hi => allW_cswapG _ _ _ ?_ ?_ ?_))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    · rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    all_goals (rw [List.mem_range] at hi; first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega)))
  have cl : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveClose s) := by
    unfold Shadow7.leaveClose
    refine allW_append (allW_eventsG _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) ?_) (allW_swapsG _ ?_)
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;>
        exact ⟨Shadow7.sig_box2 w1 w2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)), scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))⟩
    · intro p hp
      unfold Shadow7.movesP at hp
      rcases List.mem_append.mp hp with hp|hp
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
        exact ⟨bank _ (by ((try unfold Wire at *); omega)), by first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> refine ⟨?_, ?_⟩ <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
  rw [Shadow7.leaveOps_split]
  refine allW_append (allW_append ?_ (allW_append (allW_append lr sm) lc)) cl
  unfold Shadow7.leaveHeadOps
  refine allW_append ?_ fl; refine allW_append ?_ f12; refine allW_append ?_ f11; refine allW_append ?_ f10
  refine allW_append ?_ joi; refine allW_append ?_ f8; refine allW_append ?_ bar; refine allW_append ?_ adj
  refine allW_append ?_ f5; refine allW_append ?_ f4; refine allW_append ?_ f3; refine allW_append ?_ f2
  exact allW_append f0 f1

end Main

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open GateMirror Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

theorem gadgets_free (s : Nat) (w1 : 90 ≤ s) (w2 : s ≤ 390) :
    AllW (hfree s) (Shadow7.leaveAdjust s) ∧ AllW (hfree s) (Shadow7.leaveBarrel s) ∧ AllW (hfree s) (Shadow7.leaveJoin s) ∧
    AllW (hfree s) (Shadow7.lowRest s) ∧ AllW (hfree s) (Shadow7.leaveStoreMapped s) ∧ AllW (hfree s) (Shadow7.leaveLowClose s) ∧
    AllW (hfree s) (swapsG (Shadow7.movesP s)) := by
  have e0b : Shadow7.e0P s + 20 + s < 2055 := by unfold Shadow7.e0P Shadow7.sbP; omega
  have e1b : Shadow7.e0P (s+15) + 8 + s < 2055 := by unfold Shadow7.e0P Shadow7.sbP; omega
  have r := Shadow7.rail_win w1 w2
  have r14 : railP (s+15) ≤ railP (s+14) := by unfold railP; split_ifs <;> omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have hL : 10 ≤ Shadow7.lowsP s ∧ Shadow7.lowsP s ≤ 11 := by ((try unfold Wire at *); omega)
  have bank : ∀ i, i < Shadow7.wpP s + 15 → hfree s (Shadow7.bankW s i) := by
    intro i hi; have bc := Shadow7.bank_cases w1 w2 hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have tags : ∀ i, i < 16 → hfree s (tagsP.getD i 0) := by
    intro i hi; have t := tags_range i hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have aside : ∀ i, i ≤ 19 → hfree s (Shadow7.a0P s - 1 + i) := by intro i hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have bside : ∀ i, i ≤ 12 → hfree s (Shadow7.b0P s - 1 + i) := by intro i hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have scr : ∀ q, 1556 ≤ q → q ≤ Shadow7.e0P s + 20 → hfree s q := by intro q a b; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have ehi : 1614 ≤ Shadow7.e0P s + 20 := by omega
  have ctl : ∀ (xs : List Wire), (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1614) → ∀ x ∈ xs, hfree s x :=
    fun xs h x hx => scr x (h x hx).1 (le_trans (h x hx).2 ehi)
  have adj : AllW (hfree s) (Shadow7.leaveAdjust s) := by
    unfold Shadow7.leaveAdjust
    refine allW_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by ((try unfold Wire at *); omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have p := Shadow7.pool_cases (i := i) w1 w2; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have bar : AllW (hfree s) (Shadow7.leaveBarrel s) := by
    unfold Shadow7.leaveBarrel
    have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ Shadow7.wpP s + 15 → (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1614) →
        AllW (hfree s) (stageG 1613 (Shadow7.bankW s) xs d n) :=
      fun xs d n hn hx => allW_stageG _ _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (ctl xs hx)
        (fun i hi => ⟨bank i (by ((try unfold Wire at *); omega)), bank (i+d) (by ((try unfold Wire at *); omega))⟩)
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    exact allW_append (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide)) (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
  have joi : AllW (hfree s) (Shadow7.leaveJoin s) := by
    unfold Shadow7.leaveJoin
    refine allW_append (allW_digitsG _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ _
      (fun i _ hi => ⟨tags i (by ((try unfold Wire at *); omega)), ?_, ?_⟩)) (allW_wordG _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ (fun r hr => ?_))
    · have := aside (i+1) (by ((try unfold Wire at *); omega)); rwa [show Shadow7.a0P s - 1 + (i+1) = Shadow7.a0P s + i by ((try unfold Wire at *); omega)] at this
    · have := aside (i+2) (by ((try unfold Wire at *); omega)); rwa [show Shadow7.a0P s - 1 + (i+2) = Shadow7.a0P s + (i+1) by ((try unfold Wire at *); omega)] at this
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr; rw [List.mem_range] at hi
      refine ⟨fun w hw => ?_, ?_, bank i (by ((try unfold Wire at *); omega))⟩
      · dsimp only at hw; split at hw
        · cases hw; exact tags i (by ((try unfold Wire at *); omega))
        · cases hw
      · have := aside (i+1) (by ((try unfold Wire at *); omega)); dsimp only; rwa [show Shadow7.a0P s - 1 + (i+1) = Shadow7.a0P s + i by ((try unfold Wire at *); omega)] at this
  have lr : AllW (hfree s) (Shadow7.lowRest s) := by
    unfold Shadow7.lowRest
    refine allW_append (allW_append (allW_append (allW_append ?_ (allW_xsG _ ?_)) (allW_addG _ _ _ ?_ ?_ ?_))
      (allW_xsG _ ?_)) ?_
    · refine allW_map _ _ (fun i hi q hq => ?_); rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl|rfl <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
    all_goals try (intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega))
    · ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
    · rw [allW_iff_flat]
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
  have sm : AllW (hfree s) (Shadow7.leaveStoreMapped s) := by
    simp only [Shadow7.leaveStoreMapped]
    have lit : ∀ (gs : List Gate), (∀ q ∈ gs.flatMap Gate.wires, hfree s q) → AllW (hfree s) gs :=
      fun gs h => allW_iff_flat.mpr h
    have hi : ∀ y ∈ (List.range (Shadow7.wpP s + 15 - Shadow7.lowsP s)).map (fun i => Shadow7.bankW s (Shadow7.lowsP s + i)), hfree s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank _ (by ((try unfold Wire at *); omega))
    have s2 : ∀ y ∈ (List.range (Shadow7.lowsP s + 1)).map (Shadow7.b0P s - 1 + ·), hfree s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bside i (by ((try unfold Wire at *); omega))
    refine allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append
      ?_ (allW_xsG _ hi)) ?_) (allW_xsG _ (fun y h => hi y (List.mem_reverse.mp h)))) ?_) (allW_xsG _ s2)) ?_)
      (allW_xsG _ (fun y h => s2 y (List.mem_reverse.mp h)))) ?_
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        have sc := Shadow7.storeW_cases w1 w2 (Shadow7.wpP s + 15 - Shadow7.lowsP s + 1)
        split_ands <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
      · have sc := Shadow7.storeW_cases w1 w2 k; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
      · dsimp only; split
        · ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
        · exact bank _ (by ((try unfold Wire at *); omega))
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        split_ands <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
      · ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
      · ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have lc : AllW (hfree s) (Shadow7.leaveLowClose s) := by
    simp only [Shadow7.leaveLowClose]
    refine allW_append (allW_append (allW_xsG _ (fun y hy => ?_)) (allW_map _ _ (fun i hi q hq => ?_)))
      (allW_flatMap _ _ (fun i hi => allW_cswapG _ _ _ ?_ ?_ ?_))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
    · rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
    all_goals (rw [List.mem_range] at hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega))
  have mv : AllW (hfree s) (swapsG (Shadow7.movesP s)) := by
    refine allW_swapsG _ ?_
    intro p hp
    unfold Shadow7.movesP at hp
    rcases List.mem_append.mp hp with hp|hp
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
      exact ⟨bank _ (by ((try unfold Wire at *); omega)), by ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
  exact ⟨adj, bar, joi, lr, sm, lc, mv⟩

theorem fixed_targets : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    segT (start j) (leaveFix0 (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)) ++
      leaveFix2 (start j) (Shadow7.sbP (start j)) ++ leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      leaveFix5 (start j) (Shadow7.sbP (start j)) ++ leaveFix8 (start j) (Shadow7.sbP (start j)) ++ leaveFix10 (start j) (Shadow7.sbP (start j)) ++
      leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j)) = true := by
  decide +kernel

/-- The event chain of the close flips each of the first five swap cells twice and targets no other. -/
theorem events_parity : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 → ∀ i : Fin 15,
    LeaveSelector.parityAt (OB5.sig (start j+14) (start j+1044+i.val))
      (GateMirror.forward (eventsG (Shadow7.e0P (start j) + 7) (Shadow7.e0P (start j) + 4)
        [(OB5.sig (start j+14) (start j+1044), 1556), (OB5.sig (start j+14) (start j+1045), 1559),
         (OB5.sig (start j+14) (start j+1046), 1560), (OB5.sig (start j+14) (start j+1047), 1561),
         (OB5.sig (start j+14) (start j+1048), 1562)])) = some false := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open GateMirror Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run measurementCount leaveFix0 leaveFix1 leaveFix2 leaveFix3 leaveFix4 leaveFix5 leaveFix8
  leaveFix10 leaveFix11 leaveFix12 Shadow7.lowSign Shadow7.leaveAdjust Shadow7.leaveBarrel Shadow7.leaveJoin Shadow7.lowRest
  Shadow7.leaveStoreMapped Shadow7.leaveLowClose eventsG swapsG Shadow7.movesP

/-- The leave keeps every swap cell. -/
theorem swaps_kept (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (i : Nat) (hi : i < 15) (s : State) (m : List Bool) :
    (run (Shadow7.leaveP j) m s).basis (OB5.sig (start j+14) (start j+1044+i)) = s.basis (OB5.sig (start j+14) (start j+1044+i)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  obtain ⟨adj, bar, joi, lr, sm, lc, mv⟩ := Shadow7.gadgets_free (start j) w1 w2
  have fx := Shadow7.fixed_targets j h0 h1
  have ev := Shadow7.events_parity j h0 h1 ⟨i, hi⟩
  generalize hq : OB5.sig (start j+14) (start j+1044+i) = q at *
  have fixNo : ∀ g ∈ leaveFix0 (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)) ++
      leaveFix2 (start j) (Shadow7.sbP (start j)) ++ leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      leaveFix5 (start j) (Shadow7.sbP (start j)) ++ leaveFix8 (start j) (Shadow7.sbP (start j)) ++ leaveFix10 (start j) (Shadow7.sbP (start j)) ++
      leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j),
      CodecBitSliceVerify.target (front g) ≠ q := by
    intro g hg e
    have t := List.all_eq_true.mp fx g hg
    rw [e, ←hq, swap_not_ok (start j) i w1 w2 hi] at t
    exact Bool.false_ne_true t
  have gad : ∀ {gs : List Gate}, AllW (hfree (start j)) gs → ∀ g ∈ gs, CodecBitSliceVerify.target (front g) ≠ q := by
    intro gs h g hg e
    exact notarget_of_free h w1 w2 i hi _ (List.mem_map.mpr ⟨g, hg, rfl⟩) (e.trans hq.symm)
  -- head ++ mid: no target is q
  have nt_app : ∀ {a b : List Gate}, (∀ g ∈ a, CodecBitSliceVerify.target (front g) ≠ q) →
      (∀ g ∈ b, CodecBitSliceVerify.target (front g) ≠ q) → ∀ g ∈ a ++ b, CodecBitSliceVerify.target (front g) ≠ q := by
    intro a b ha hb g hg
    rcases List.mem_append.mp hg with h|h
    · exact ha g h
    · exact hb g h
  have f0 : ∀ g ∈ leaveFix0 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f1 : ∀ g ∈ leaveFix1 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f2 : ∀ g ∈ leaveFix2 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f3 : ∀ g ∈ leaveFix3 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f4 : ∀ g ∈ leaveFix4 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f5 : ∀ g ∈ leaveFix5 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f8 : ∀ g ∈ leaveFix8 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f10 : ∀ g ∈ leaveFix10 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f11 : ∀ g ∈ leaveFix11 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f12 : ∀ g ∈ leaveFix12 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have fl : ∀ g ∈ Shadow7.lowSign (start j), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have hm' : ∀ g ∈ Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j), CodecBitSliceVerify.target (front g) ≠ q := by
    rw [Shadow7.leaveMidOps_eq]
    refine nt_app ?_ (nt_app (nt_app (gad lr) (gad sm)) (gad lc))
    unfold Shadow7.leaveHeadOps
    refine nt_app ?_ fl; refine nt_app ?_ f12; refine nt_app ?_ f11; refine nt_app ?_ f10
    refine nt_app ?_ (gad joi); refine nt_app ?_ f8; refine nt_app ?_ (gad bar); refine nt_app ?_ (gad adj)
    refine nt_app ?_ f5; refine nt_app ?_ f4; refine nt_app ?_ f3; refine nt_app ?_ f2
    exact nt_app f0 f1
  have hm : ∀ ins ∈ GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j)), CodecBitSliceVerify.target ins ≠ q := by
    intro ins hins
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hins
    exact hm' g hg
  have mvNo : ∀ ins ∈ GateMirror.forward (swapsG (Shadow7.movesP (start j))), CodecBitSliceVerify.target ins ≠ q := by
    intro ins hins
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hins
    exact gad mv g hg
  have A : ∀ m s, (run (GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j))) m s).basis q = s.basis q :=
    fun m s => preserve_readonly _ q hm s m
  have E : ∀ m s, (run (GateMirror.forward (eventsG (Shadow7.e0P (start j) + 7) (Shadow7.e0P (start j) + 4)
        [(OB5.sig (start j+14) (start j+1044), 1556), (OB5.sig (start j+14) (start j+1045), 1559),
         (OB5.sig (start j+14) (start j+1046), 1560), (OB5.sig (start j+14) (start j+1047), 1561),
         (OB5.sig (start j+14) (start j+1048), 1562)])) m s).basis q = s.basis q := by
    intro m s; rw [LeaveSelector.polarity q _ false ev, Bool.xor_false]
  have M : ∀ m s, (run (GateMirror.forward (swapsG (Shadow7.movesP (start j)))) m s).basis q = s.basis q :=
    fun m s => preserve_readonly _ q mvNo s m
  have split : Shadow7.leaveP j = GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j)) ++
      (GateMirror.forward (eventsG (Shadow7.e0P (start j) + 7) (Shadow7.e0P (start j) + 4)
        [(OB5.sig (start j+14) (start j+1044), 1556), (OB5.sig (start j+14) (start j+1045), 1559),
         (OB5.sig (start j+14) (start j+1046), 1560), (OB5.sig (start j+14) (start j+1047), 1561),
         (OB5.sig (start j+14) (start j+1048), 1562)]) ++ GateMirror.forward (swapsG (Shadow7.movesP (start j)))) := by
    rw [Shadow7.leaveP, Shadow7.leaveOps_split, Shadow7.leaveClose, fwAppend, fwAppend, fwAppend]
  rw [split, keep_append _ _ q A (keep_append _ _ q E M)]

end ECDSAAdd.Entrant.StairPacket.Shadow7
end
