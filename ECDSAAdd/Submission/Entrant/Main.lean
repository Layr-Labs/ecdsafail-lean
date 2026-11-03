import ECDSAAdd.Submission.Entrant.MainPart07

set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.

-- ===== merged module ECDSAAdd.Submission.Entrant.InputSentinel =====
namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- First bit below 256 where two words differ (0 when none). -/
def firstDiff (a b : Nat) : Nat :=
  ((List.range 256).find? (fun i => a.testBit i != b.testBit i)).getD 0

theorem firstDiff_spec (a b : Nat) (ha : a < 2^256) (hb : b < 2^256) (hne : a ≠ b) :
    firstDiff a b < 256 ∧ a.testBit (firstDiff a b) ≠ b.testBit (firstDiff a b) := by
  have ex : ∃ i ∈ List.range 256, (a.testBit i != b.testBit i) = true := by
    by_contra h
    push_neg at h
    apply hne
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 256
    · have := h i (List.mem_range.mpr hi)
      simpa using this
    · have h1 : a.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have h2 : b.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [h1, h2]
  obtain ⟨j, hj, hjp⟩ := ex
  have hs : ((List.range 256).find? (fun i => a.testBit i != b.testBit i)).isSome := by
    rw [List.find?_isSome]; exact ⟨j, hj, hjp⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
  have hkm := List.mem_of_find?_eq_some hk
  have hkp := List.find?_some hk
  have hfd : firstDiff a b = k := by simp [firstDiff, hk]
  rw [hfd]
  exact ⟨List.mem_range.mp hkm, by simpa using hkp⟩

/-- The three words the input stage compares `x` with: `C.x`, `(-2C).x` and the sentinel. -/
structure Tri where
  A : Nat
  B : Nat
  S : Nat

namespace Tri
variable (t : Tri)

/-- First pivot: a bit separating `B` from `S`. -/
def r1 : Nat := firstDiff t.B t.S
/-- Role 1: `A` agrees with `S` at the first pivot (otherwise it agrees with `B`). -/
def role1 : Bool := t.A.testBit t.r1 == t.S.testBit t.r1
/-- Second pivot: separates `A` from the word it agrees with at `r1`. -/
def r2 : Nat := if t.role1 then firstDiff t.A t.S else firstDiff t.A t.B

def pat (K : Nat) : Bool × Bool := (K.testBit t.r1, K.testBit t.r2)

/-- Target bit `i` at pivot pattern `p`: the matching word's bit, else the affine completion. -/
def tgt (i : Nat) (p : Bool × Bool) : Bool :=
  if p = t.pat t.A then t.A.testBit i
  else if p = t.pat t.B then t.B.testBit i
  else if p = t.pat t.S then t.S.testBit i
  else t.A.testBit i ^^ t.B.testBit i ^^ t.S.testBit i

structure Valid : Prop where
  hA : t.A < 2^256
  hB : t.B < 2^256
  hS : t.S < 2^256
  AB : t.A ≠ t.B
  AS : t.A ≠ t.S
  BS : t.B ≠ t.S

variable {t}

theorem pivots (v : t.Valid) :
    t.r1 < 256 ∧ t.r2 < 256 ∧ t.r1 ≠ t.r2 ∧
      t.pat t.A ≠ t.pat t.B ∧ t.pat t.A ≠ t.pat t.S ∧ t.pat t.B ≠ t.pat t.S := by
  have h1 := firstDiff_spec t.B t.S v.hB v.hS v.BS
  have hAS := firstDiff_spec t.A t.S v.hA v.hS v.AS
  have hAB := firstDiff_spec t.A t.B v.hA v.hB v.AB
  have er1 : t.r1 = firstDiff t.B t.S := rfl
  by_cases ro : t.role1 = true
  · have er2 : t.r2 = firstDiff t.A t.S := by simp [r2, ro]
    have eq1 : t.A.testBit t.r1 = t.S.testBit t.r1 := by simpa [role1] using ro
    have ne : t.r1 ≠ t.r2 := by
      intro e; rw [er2] at e; rw [e] at eq1; exact hAS.2 eq1
    refine ⟨h1.1, er2 ▸ hAS.1, ne, ?_, ?_, ?_⟩
    · intro e; have := congrArg Prod.fst e; simp only [pat] at this
      exact h1.2 (by rw [← er1, ← this, eq1])
    · intro e; have := congrArg Prod.snd e; simp only [pat] at this
      exact hAS.2 (by rw [er2] at this; exact this)
    · intro e; have := congrArg Prod.fst e; simp only [pat] at this
      exact h1.2 (by rw [← er1]; exact this)
  · have er2 : t.r2 = firstDiff t.A t.B := by simp [r2, ro]
    have ne1 : t.A.testBit t.r1 ≠ t.S.testBit t.r1 := by simpa [role1] using ro
    have eq1 : t.A.testBit t.r1 = t.B.testBit t.r1 := by
      have hb := h1.2; rw [← er1] at hb
      cases hA : t.A.testBit t.r1 <;> cases hB' : t.B.testBit t.r1 <;> cases hS' : t.S.testBit t.r1 <;>
        simp_all
    have ne : t.r1 ≠ t.r2 := by
      intro e; rw [er2] at e; rw [e] at eq1; exact hAB.2 eq1
    refine ⟨h1.1, er2 ▸ hAB.1, ne, ?_, ?_, ?_⟩
    · intro e; have := congrArg Prod.snd e; simp only [pat] at this
      exact hAB.2 (by rw [er2] at this; exact this)
    · intro e; have := congrArg Prod.fst e; simp only [pat] at this
      exact ne1 this
    · intro e; have := congrArg Prod.fst e; simp only [pat] at this
      exact h1.2 (by rw [← er1]; exact this)

private theorem affine4 : ∀ (pA pB pS : Bool × Bool) (a b c : Bool),
    pA ≠ pB → pA ≠ pS → pB ≠ pS →
    let f := fun p : Bool × Bool => if p = pA then a else if p = pB then b else if p = pS then c
      else a ^^ b ^^ c
    f (true, true) = (f (true, false) ^^ f (false, true) ^^ f (false, false)) := by
  decide

theorem tgt_affine (v : t.Valid) (i : Nat) :
    t.tgt i (true, true) = (t.tgt i (true, false) ^^ t.tgt i (false, true) ^^ t.tgt i (false, false)) := by
  have pv := pivots v
  exact affine4 _ _ _ _ _ _ pv.2.2.2.1 pv.2.2.2.2.1 pv.2.2.2.2.2

theorem tgt_A (i : Nat) : t.tgt i (t.pat t.A) = t.A.testBit i := by simp [tgt]
theorem tgt_B (v : t.Valid) (i : Nat) : t.tgt i (t.pat t.B) = t.B.testBit i := by
  have pv := pivots v; simp [tgt, Ne.symm pv.2.2.2.1]
theorem tgt_S (v : t.Valid) (i : Nat) : t.tgt i (t.pat t.S) = t.S.testBit i := by
  have pv := pivots v; simp [tgt, Ne.symm pv.2.2.2.2.1, Ne.symm pv.2.2.2.2.2]

/-- Bits other than the two pivots. -/
def idx : List Nat := (List.range 256).filter (fun i => i ≠ t.r1 ∧ i ≠ t.r2)

/-- A zero test on the remapped non-pivot bits plus a pivot pattern identifies the word. -/
theorem match_iff (v : t.Valid) (X K : Nat) (hX : X < 2^256) (hK : K < 2^256)
    (hKt : ∀ i, t.tgt i (t.pat K) = K.testBit i) :
    ((∀ i ∈ t.idx, X.testBit i = t.tgt i (t.pat X)) ∧ t.pat X = t.pat K) ↔ X = K := by
  have pv := pivots v
  constructor
  · rintro ⟨hall, hp⟩
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 256
    · by_cases h1 : i = t.r1
      · subst h1; exact congrArg Prod.fst hp
      by_cases h2 : i = t.r2
      · subst h2; exact congrArg Prod.snd hp
      have hm : i ∈ t.idx := by simp [idx, hi, h1, h2]
      rw [hall i hm, hp, hKt]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hK (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · rintro rfl
    exact ⟨fun i _ => (hKt i).symm, rfl⟩

end Tri

namespace Tri
variable (t : Tri)

/-- Per-bit remap: XOR the target bit of the current pivot pattern into wire `w`. -/
def remapBit (xr1 xr2 w : Wire) (i : Nat) : Program :=
  (if t.tgt i (false, false) then [.X w] else []) ++
  ((if (t.tgt i (true, false) ^^ t.tgt i (false, false)) then [.CX xr1 w] else []) ++
  (if (t.tgt i (false, true) ^^ t.tgt i (false, false)) then [.CX xr2 w] else []))

def remapList (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) : Program :=
  l.flatMap (fun i => t.remapBit xr1 xr2 (w i) i)

variable {t}

theorem remapBit_run (v : t.Valid) (xr1 xr2 w : Wire) (i : Nat) (h1 : w ≠ xr1) (h2 : w ≠ xr2)
    (m : List Bool) (s : State) :
    run (t.remapBit xr1 xr2 w i) m s =
      ⟨s.phase, writeBit s.basis w (s.basis w ^^ t.tgt i (s.basis xr1, s.basis xr2))⟩ := by
  have aff := tgt_affine v i
  have key : t.tgt i (s.basis xr1, s.basis xr2) =
      (t.tgt i (false, false) ^^ (s.basis xr1 && (t.tgt i (true, false) ^^ t.tgt i (false, false))) ^^
        (s.basis xr2 && (t.tgt i (false, true) ^^ t.tgt i (false, false)))) := by
    have gen : ∀ x1 x2 : Bool, t.tgt i (x1, x2) =
        (t.tgt i (false, false) ^^ (x1 && (t.tgt i (true, false) ^^ t.tgt i (false, false))) ^^
          (x2 && (t.tgt i (false, true) ^^ t.tgt i (false, false)))) := by
      intro x1 x2
      cases x1 <;> cases x2 <;>
      (revert aff
       generalize t.tgt i (true, true) = d
       generalize t.tgt i (false, false) = a
       generalize t.tgt i (true, false) = b
       generalize t.tgt i (false, true) = c
       intro aff; subst aff
       cases a <;> cases b <;> cases c <;> rfl)
    exact gen _ _
  rw [key]
  clear key aff
  unfold remapBit
  generalize t.tgt i (false, false) = a
  generalize t.tgt i (true, false) = b
  generalize t.tgt i (false, true) = c
  obtain ⟨ph, bs⟩ := s
  have w1 : xr1 ≠ w := Ne.symm h1
  have w2 : xr2 ≠ w := Ne.symm h2
  cases a <;> cases b <;> cases c <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true,
      if_false, List.nil_append, List.append_nil, List.cons_append, List.singleton_append] <;>
    simp only [run] <;> congr 1 <;> funext q <;> by_cases hq : q = w <;>
    simp [writeBit, Function.update, hq, w1, w2, Bool.and_false, Bool.and_true, Bool.xor_false,
      Bool.false_xor, Bool.xor_true, Bool.true_xor]

theorem remapList_run (v : t.Valid) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat)
    (hnd : (l.map w).Nodup) (h1 : xr1 ∉ l.map w) (h2 : xr2 ∉ l.map w) (m : List Bool) (s : State) :
    (run (t.remapList xr1 xr2 w l) m s).phase = s.phase ∧
    (∀ q, q ∉ l.map w → (run (t.remapList xr1 xr2 w l) m s).basis q = s.basis q) ∧
    (∀ i ∈ l, (run (t.remapList xr1 xr2 w l) m s).basis (w i) =
      (s.basis (w i) ^^ t.tgt i (s.basis xr1, s.basis xr2))) := by
  induction l generalizing s m with
  | nil => simp [remapList, run]
  | cons i l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd h1 h2
    have hw1 : w i ≠ xr1 := fun e => h1.1 e.symm
    have hw2 : w i ≠ xr2 := fun e => h2.1 e.symm
    have e : t.remapList xr1 xr2 w (i :: l) = t.remapBit xr1 xr2 (w i) i ++ t.remapList xr1 xr2 w l := by
      simp [remapList]
    rw [e, run_append, remapBit_run v xr1 xr2 (w i) i hw1 hw2]
    set s1 : State := ⟨s.phase, writeBit s.basis (w i) (s.basis (w i) ^^ t.tgt i (s.basis xr1, s.basis xr2))⟩
    have ih1 := ih hnd.2 h1.2 h2.2 (m.drop (measurementCount (t.remapBit xr1 xr2 (w i) i))) s1
    have k1 : s1.basis xr1 = s.basis xr1 := by simp [s1, writeBit, Function.update, Ne.symm hw1]
    have k2 : s1.basis xr2 = s.basis xr2 := by simp [s1, writeBit, Function.update, Ne.symm hw2]
    refine ⟨ih1.1, ?_, ?_⟩
    · intro q hq
      simp only [List.map_cons, List.mem_cons, not_or] at hq
      rw [ih1.2.1 q hq.2]
      simp [s1, writeBit, Function.update, hq.1]
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [ih1.2.1 (w j) hnd.1]
        simp [s1, writeBit]
      · rw [ih1.2.2 j hj, k1, k2]
        have hne : w j ≠ w i := fun e => hnd.1 (e ▸ List.mem_map_of_mem hj)
        simp [s1, writeBit, Function.update, hne]

end Tri



/-- `[q = v]` frame: flip `q` when the tested value is `false`. -/
def lit (q : Wire) (v : Bool) : Program := if v then [] else [.X q]

/-! Decode tail on local wires: 0 `h` (zero-test result), 1 `x_r1`, 2 `x_r2`, 3 `y0`, 4 control,
5 finite flag, 6 generic select, 7–9 clean scratch. -/

/-- Pivot role 1: the sentinel and `C.x` share `x_r1 = a1`, `(-2C).x` has the other value. -/
def decode1 (a1 a2 b2 yb : Bool) : Program :=
  lit 1 a1 ++ [.CCX 0 1 7] ++ lit 1 a1 ++
  [.CX 7 0] ++
  lit 2 b2 ++ [.CCX 0 2 8] ++ lit 2 b2 ++
  lit 3 yb ++ [.CCX 8 3 9] ++ lit 3 yb ++
  [.CX 7 9, .X 9, .CCX 4 9 6, .X 9, .CX 7 9] ++
  lit 3 yb ++ [.measureX 9 [] [.CZ 8 3]] ++ lit 3 yb ++
  [.X 5] ++ lit 2 (!a2) ++ [.measureX 5 [] [.CZ 7 2]] ++ lit 2 (!a2) ++
  lit 2 b2 ++ [.measureX 8 [] [.CZ 0 2]] ++ lit 2 b2 ++
  [.CX 7 0] ++
  lit 1 a1 ++ [.measureX 7 [] [.CZ 0 1]] ++ lit 1 a1

/-- Pivot role 2: `C.x` and `(-2C).x` share `x_r1 = b1`, the sentinel has the other value. -/
def decode2 (b1 a2 s2 yb : Bool) : Program :=
  lit 1 b1 ++ [.CCX 0 1 7] ++ lit 1 b1 ++
  lit 2 (!a2) ++ [.CCX 7 2 8] ++ lit 2 (!a2) ++
  lit 3 yb ++ [.CCX 8 3 9] ++ lit 3 yb ++
  [.CX 5 9, .CX 7 9, .CX 8 9, .CCX 4 9 6, .CX 8 9, .CX 7 9, .CX 5 9] ++
  lit 3 yb ++ [.measureX 9 [] [.CZ 8 3]] ++ lit 3 yb ++
  [.CX 7 0, .X 5] ++ lit 2 s2 ++ [.measureX 5 [] [.CZ 0 2]] ++ lit 2 s2 ++ [.CX 7 0] ++
  lit 2 (!a2) ++ [.measureX 8 [] [.CZ 7 2]] ++ lit 2 (!a2) ++
  lit 1 b1 ++ [.measureX 7 [] [.CZ 0 1]] ++ lit 1 b1

/-- The generic flag produced by role 1 from the zero-test bit and the pivot bits. -/
def gen1 (a1 b2 yb : Bool) (x : Nat) : Bool :=
  x.testBit 4 && !((x.testBit 0 && (x.testBit 1 == a1)) ||
    (x.testBit 0 && (x.testBit 1 != a1) && (x.testBit 2 == b2) && (x.testBit 3 == yb)))

def gen2 (b1 a2 yb : Bool) (x : Nat) : Bool :=
  let g1 := x.testBit 0 && (x.testBit 1 == b1)
  x.testBit 4 && (x.testBit 5 ^^ (g1 && (x.testBit 2 == a2)) ^^
    (g1 && (x.testBit 2 != a2) && (x.testBit 3 == yb)))

/-- Output word: finite flag cleared, generic select toggled by `gv`. -/
def out (x : Nat) (gv : Bool) : Nat :=
  x ^^^ (if x.testBit 5 then 32 else 0) ^^^ (if gv then 64 else 0)

def pre1 (a1 a2 : Bool) (x : Nat) : Bool :=
  x.testBit 5 == !(x.testBit 0 && (x.testBit 1 == a1) && (x.testBit 2 == !a2))

def pre2 (b1 s2 : Bool) (x : Nat) : Bool :=
  x.testBit 5 == !(x.testBit 0 && (x.testBit 1 != b1) && (x.testBit 2 == s2))

theorem decode1_ok : ∀ a1 a2 b2 yb : Bool, ∀ x : Fin 128, pre1 a1 a2 x.val = true →
    safe (decode1 a1 a2 b2 yb) x.val = true ∧
      bitRun (decode1 a1 a2 b2 yb) x.val = out x.val (gen1 a1 b2 yb x.val) := by
  decide +kernel

theorem decode2_ok : ∀ b1 a2 s2 yb : Bool, ∀ x : Fin 128, pre2 b1 s2 x.val = true →
    safe (decode2 b1 a2 s2 yb) x.val = true ∧
      bitRun (decode2 b1 a2 s2 yb) x.val = out x.val (gen2 b1 a2 yb x.val) := by
  decide +kernel

theorem decode_counts (a1 a2 b2 yb : Bool) :
    toffoliCount (decode1 a1 a2 b2 yb) = 4 ∧ measurementCount (decode1 a1 a2 b2 yb) = 4 ∧
    toffoliCount (decode2 a1 a2 b2 yb) = 4 ∧ measurementCount (decode2 a1 a2 b2 yb) = 4 := by
  cases a1 <;> cases a2 <;> cases b2 <;> cases yb <;> decide


/-- A safe local program on wires `0..n-1` lifts through an injective port map: the ports end
with the bits of its classical simulation, every other wire is untouched, and the phase is kept. -/
theorem lift_local (n : Nat) (p : Fin n → Wire) (hp : Function.Injective p) (D : Program)
    (hD : wires D ⊆ Finset.range n) (s : State) (m : List Bool) (x : Nat)
    (hx : ∀ q (h : q < n), s.basis (p ⟨q, h⟩) = x.testBit q) (hsafe : safe D x = true) :
    (run (renameProgram (LocalWireModel.label p) D) m s).phase = s.phase ∧
    (∀ q (h : q < n), (run (renameProgram (LocalWireModel.label p) D) m s).basis (p ⟨q, h⟩) =
      (bitRun D x).testBit q) ∧
    (∀ w, (∀ q (h : q < n), w ≠ p ⟨q, h⟩) →
      (run (renameProgram (LocalWireModel.label p) D) m s).basis w = s.basis w) := by
  let t : State := ⟨s.phase, fun q => s.basis (LocalWireModel.label p q)⟩
  have rr := run_rename_pool (LocalWireModel.label p) (Finset.range n)
    (LocalWireModel.label_injective p hp) D hD m t s rfl (fun _ _ => rfl)
  have lab (q : Nat) (h : q < n) : LocalWireModel.label p q = p ⟨q, h⟩ := by
    simp [LocalWireModel.label, h]
  have agree := pool_run_agrees D (Finset.range n) hD m t ⟨s.phase, bitsOf x⟩ rfl (by
    intro q hq
    have h := Finset.mem_range.mp hq
    change s.basis (LocalWireModel.label p q) = x.testBit q
    rw [lab q h, hx q h])
  have sim := run_sim D m s.phase x
  rw [sim_safe D x hsafe m s.phase] at sim
  refine ⟨?_, ?_, ?_⟩
  · rw [rr.1, agree.1, sim]
  · intro q h
    have e := rr.2 q (Finset.mem_range.mpr h)
    rw [lab q h] at e
    rw [e, agree.2 q (Finset.mem_range.mpr h), sim]
    rfl
  · intro w hw
    apply run_rename_pool_outside _ _ D hD m s w
    intro hm
    obtain ⟨q, hq, eq⟩ := Finset.mem_image.mp hm
    have h := Finset.mem_range.mp hq
    exact hw q h (by rw [← lab q h]; exact eq.symm)

theorem out_bit (x : Nat) (gv : Bool) (q : Nat) :
    (out x gv).testBit q = (if q = 5 then false else if q = 6 then (x.testBit 6 ^^ gv) else x.testBit q) := by
  unfold out
  rw [Nat.testBit_xor, Nat.testBit_xor]
  have e1 : Nat.testBit 32 5 = true := by decide
  have e2 : Nat.testBit 64 5 = false := by decide
  have e3 : Nat.testBit 32 6 = false := by decide
  have e4 : Nat.testBit 64 6 = true := by decide
  by_cases h5 : q = 5
  · subst h5; cases hx : x.testBit 5 <;> cases gv <;> simp [hx, e1, e2]
  · by_cases h6 : q = 6
    · subst h6; cases hx : x.testBit 5 <;> cases gv <;> cases x.testBit 6 <;> simp [hx, e3, e4]
    · have a : (if x.testBit 5 then 32 else 0 : Nat).testBit q = false := by
        split_ifs
        · rw [show (32:Nat) = 2^5 by norm_num, Nat.testBit_two_pow]; simp [Ne.symm h5]
        · simp
      have b : (if gv then 64 else 0 : Nat).testBit q = false := by
        split_ifs
        · rw [show (64:Nat) = 2^6 by norm_num, Nat.testBit_two_pow]; simp [Ne.symm h6]
        · simp
      rw [a, b]; simp [h5, h6]

/-- The decode tail for the word triple's pivot role. -/
def decodeT (tr : Tri) (yb : Bool) : Program :=
  if tr.role1 then decode1 (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) (tr.B.testBit tr.r2) yb
  else decode2 (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) (tr.S.testBit tr.r2) yb

/-- Generic flag toggle produced by the tail from the zero-test bit and the read bits. -/
def genOut (tr : Tri) (yb v x1 x2 y c f : Bool) : Bool :=
  if tr.role1 then
    c && !((v && (x1 == tr.A.testBit tr.r1)) ||
      (v && (x1 != tr.A.testBit tr.r1) && (x2 == tr.B.testBit tr.r2) && (y == yb)))
  else
    c && (f ^^ ((v && (x1 == tr.A.testBit tr.r1)) && (x2 == tr.A.testBit tr.r2)) ^^
      ((v && (x1 == tr.A.testBit tr.r1)) && (x2 != tr.A.testBit tr.r2) && (y == yb)))

theorem decodeT_support (tr : Tri) (yb : Bool) : wires (decodeT tr yb) ⊆ Finset.range 10 := by
  unfold decodeT
  split_ifs <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.A.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c; generalize tr.S.testBit tr.r2 = d
    cases a <;> cases b <;> cases c <;> cases d <;> cases yb <;> decide

theorem tail_run (tr : Tri) (v : tr.Valid) (yb : Bool) (h xr1 xr2 y0 c f g g1 wB t : Wire)
    (hnd : [h, xr1, xr2, y0, c, f, g, g1, wB, t].Nodup) (s : State) (m : List Bool)
    (hz : s.basis g1 = false ∧ s.basis wB = false ∧ s.basis t = false)
    (hf : s.basis f = !(s.basis h && decide ((s.basis xr1, s.basis xr2) = tr.pat tr.S))) :
    run (renameProgram (LocalWireModel.label
        (fun q : Fin 10 => [h, xr1, xr2, y0, c, f, g, g1, wB, t].getD q.val 0)) (decodeT tr yb)) m s =
      ⟨s.phase, writeBit (writeBit s.basis f false) g (s.basis g ^^
        genOut tr yb (s.basis h) (s.basis xr1) (s.basis xr2) (s.basis y0) (s.basis c) (s.basis f))⟩ := by
  have hfg : f ≠ g := by intro e; subst e; simp at hnd
  set r : List Wire := [h, xr1, xr2, y0, c, f, g, g1, wB, t] with hr
  have pv := Tri.pivots v
  let x : Nat := regValue r s.basis
  have hx : ∀ q (hq : q < 10), s.basis (r.getD q 0) = x.testBit q := by
    intro q hq
    exact (LocalWireModel.reg_bit r s.basis q (by simpa [hr] using hq)).symm
  have hb (q : Nat) (hq : q < 10) : x.testBit q = s.basis (r.getD q 0) := (hx q hq).symm
  have x7 : x < 2^7 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases h10 : i < 10
    · interval_cases i
      · rw [hb 7 (by decide)]; simpa [hr] using hz.1
      · rw [hb 8 (by decide)]; simpa [hr] using hz.2.1
      · rw [hb 9 (by decide)]; simpa [hr] using hz.2.2
    · have hl : x < 2^10 := by simpa [x, hr] using regValue_lt r s.basis
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hl (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have bits : x.testBit 0 = s.basis h ∧ x.testBit 1 = s.basis xr1 ∧ x.testBit 2 = s.basis xr2 ∧
      x.testBit 3 = s.basis y0 ∧ x.testBit 4 = s.basis c ∧ x.testBit 5 = s.basis f ∧
      x.testBit 6 = s.basis g := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (rw [hb 0 (by decide)]; simp [hr]) | (rw [hb 1 (by decide)]; simp [hr])
      | (rw [hb 2 (by decide)]; simp [hr]) | (rw [hb 3 (by decide)]; simp [hr])
      | (rw [hb 4 (by decide)]; simp [hr]) | (rw [hb 5 (by decide)]; simp [hr])
      | (rw [hb 6 (by decide)]; simp [hr])
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := bits
  have inj := LocalWireModel.listPorts_injective r hnd (n := 10) (by simp [hr])
  -- the classical check for this role
  have core : safe (decodeT tr yb) x = true ∧ bitRun (decodeT tr yb) x =
      out x (genOut tr yb (s.basis h) (s.basis xr1) (s.basis xr2) (s.basis y0) (s.basis c) (s.basis f)) := by
    unfold decodeT genOut
    by_cases ro : tr.role1 = true
    · have eq1 : tr.A.testBit tr.r1 = tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
      have neS : tr.S.testBit tr.r2 = !tr.A.testBit tr.r2 := by
        have er2 : tr.r2 = firstDiff tr.A tr.S := by simp [Tri.r2, ro]
        have d := (firstDiff_spec tr.A tr.S v.hA v.hS v.AS).2
        rw [← er2] at d
        cases hA : tr.A.testBit tr.r2 <;> cases hS : tr.S.testBit tr.r2 <;> simp_all
      have pre : pre1 (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) x = true := by
        simp only [pre1, b0, b1, b2, b5, hf, Tri.pat, eq1, neS, Prod.mk.injEq]
        cases s.basis h <;> cases s.basis xr1 <;> cases s.basis xr2 <;>
          cases tr.S.testBit tr.r1 <;> cases tr.A.testBit tr.r2 <;> decide
      have k := decode1_ok (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) (tr.B.testBit tr.r2) yb ⟨x, x7⟩ pre
      simp only [ro, if_true]
      refine ⟨k.1, ?_⟩
      rw [k.2]
      congr 1
      simp only [gen1, b0, b1, b2, b3, b4]
    · have ro' : tr.role1 = false := by simpa using ro
      have ne1 : tr.S.testBit tr.r1 = !tr.A.testBit tr.r1 := by
        have : tr.A.testBit tr.r1 ≠ tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
        cases hA : tr.A.testBit tr.r1 <;> cases hS : tr.S.testBit tr.r1 <;> simp_all
      have pre : pre2 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) x = true := by
        simp only [pre2, b0, b1, b2, b5, hf, Tri.pat, ne1, Prod.mk.injEq]
        cases s.basis h <;> cases s.basis xr1 <;> cases s.basis xr2 <;>
          cases tr.A.testBit tr.r1 <;> cases tr.S.testBit tr.r2 <;> decide
      have k := decode2_ok (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) (tr.S.testBit tr.r2) yb ⟨x, x7⟩ pre
      simp only [ro', Bool.false_eq_true, if_false]
      refine ⟨k.1, ?_⟩
      rw [k.2]
      congr 1
      simp only [gen2, b0, b1, b2, b3, b4, b5]
  have L := lift_local 10 _ inj (decodeT tr yb) (decodeT_support tr yb) s m x hx core.1
  rw [core.2] at L
  apply State.extensionality
  · exact L.1
  · funext w
    have port (q : Nat) (hq : q < 10) := L.2.1 q hq
    simp only [out_bit] at port
    by_cases wf : w = f
    · subst wf
      have := port 5 (by decide)
      simpa [hr, writeBit, Function.update, hfg] using this
    by_cases wg : w = g
    · subst wg
      have e6 : w = r.getD 6 0 := by simp [hr]
      conv_lhs => rw [e6]
      rw [port 6 (by decide)]
      simp [writeBit, Function.update, b6, ← e6]
    by_cases wr : w ∈ r
    · obtain ⟨q, hq, hqw⟩ : ∃ q, q < 10 ∧ r.getD q 0 = w := by
        obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem wr
        exact ⟨i, by simpa [hr] using hi, by rw [List.getD_eq_getElem _ _ hi]; exact hiw⟩
      have pq := port q hq
      have q5 : q ≠ 5 := by intro e; subst e; apply wf; rw [← hqw]; simp [hr]
      have q6 : q ≠ 6 := by intro e; subst e; apply wg; rw [← hqw]; simp [hr]
      simp only [q5, q6, if_false] at pq
      change (run _ m s).basis (r.getD q 0) = _ at pq
      rw [hqw] at pq
      rw [pq, hb q hq, hqw]
      simp [writeBit, Function.update, wf, wg]
    · rw [L.2.2 w (by
        intro q hq e
        apply wr
        rw [e]
        have hq' : q < r.length := by simpa [hr] using hq
        rw [List.getD_eq_getElem _ _ hq']
        exact List.getElem_mem hq')]
      simp [writeBit, Function.update, wf, wg]

/-- The tail on the chain's last work wire `h`. -/
def tail (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t : Wire) (h : Wire) : Program :=
  renameProgram (LocalWireModel.label
    (fun q : Fin 10 => [h, xr1, xr2, y0, c, f, g, g1, wB, t].getD q.val 0)) (decodeT tr yb)

/-- Tail precondition: clean scratch and the finite flag is the negated sentinel match. -/
def tailPre (tr : Tri) (xr1 xr2 f g1 wB t : Wire) (u : Bool) (st : BasisState) : Prop :=
  st g1 = false ∧ st wB = false ∧ st t = false ∧
    st f = !(u && decide ((st xr1, st xr2) = tr.pat tr.S))

/-- Tail effect: the finite flag is cleared and the generic select is toggled. -/
def tailEff (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g : Wire) (u : Bool) (st : BasisState) : BasisState :=
  writeBit (writeBit st f false) g
    (st g ^^ genOut tr yb u (st xr1) (st xr2) (st y0) (st c) (st f))

theorem chain_run (tr : Tri) (v : tr.Valid) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t : Wire)
    (hused : [xr1, xr2, y0, c, f, g, g1, wB, t].Nodup)
    (c0 : Wire) (bs : List ZeroBit) (hcu : c0 ∉ [xr1, xr2, y0, c, f, g, g1, wB, t])
    (hnd : (c0 :: bs.flatMap ZeroBit.wires).Nodup)
    (hdis : ∀ b ∈ bs, b.input ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, g1, wB, t])
    (s : State) (m : List Bool)
    (hs : tailPre tr xr1 xr2 f g1 wB t (s.basis c0 && bs.all (fun b => !s.basis b.input)) s.basis)
    (hz : ∀ b ∈ bs, s.basis b.work = false) :
    run (zeroWith (tail tr yb xr1 xr2 y0 c f g g1 wB t) c0 bs) m s =
      ⟨s.phase, tailEff tr yb xr1 xr2 y0 c f g (s.basis c0 && bs.all (fun b => !s.basis b.input)) s.basis⟩ := by
  set used : List Wire := [xr1, xr2, y0, c, f, g, g1, wB, t] with hu
  apply zeroWith_effect_runQ used (tailPre tr xr1 xr2 f g1 wB t) (tailEff tr yb xr1 xr2 y0 c f g)
  · intro w hw u st z
    have h1 : w ≠ g1 := fun e => hw (by simp [hu, e])
    have h2 : w ≠ wB := fun e => hw (by simp [hu, e])
    have h3 : w ≠ t := fun e => hw (by simp [hu, e])
    have h4 : w ≠ f := fun e => hw (by simp [hu, e])
    have h5 : w ≠ xr1 := fun e => hw (by simp [hu, e])
    have h6 : w ≠ xr2 := fun e => hw (by simp [hu, e])
    simp [tailPre, writeBit, Function.update, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4,
      Ne.symm h5, Ne.symm h6]
  · intro u st w hw
    have h4 : w ≠ f := fun e => hw (by simp [hu, e])
    have h7 : w ≠ g := fun e => hw (by simp [hu, e])
    simp [tailEff, writeBit, Function.update, h4, h7]
  · intro u st w z hw
    have hs' : ∀ q ∈ used, q ≠ w := fun q hq e => hw (e ▸ hq)
    have h4 : f ≠ w := hs' f (by simp [hu])
    have h7 : g ≠ w := hs' g (by simp [hu])
    have r1 : xr1 ≠ w := hs' xr1 (by simp [hu])
    have r2 : xr2 ≠ w := hs' xr2 (by simp [hu])
    have r3 : y0 ≠ w := hs' y0 (by simp [hu])
    have r4 : c ≠ w := hs' c (by simp [hu])
    unfold tailEff
    simp only [writeBit, Function.update_apply, r1, r2, r3, r4, h4, h7, if_false]
    funext q
    by_cases qg : q = g
    · subst qg; simp [Function.update, h7]
    · by_cases qf : q = f
      · subst qf; simp [Function.update, h4, qg]
      · by_cases qw : q = w
        · subst qw; simp [Function.update, qg, qf]
        · simp [Function.update, qg, qf, qw]
  · intro c' hc' st m' hp
    have hnd' : [c', xr1, xr2, y0, c, f, g, g1, wB, t].Nodup := List.nodup_cons.mpr ⟨hc', hused⟩
    exact tail_run tr v yb c' xr1 xr2 y0 c f g g1 wB t hnd' st m' ⟨hp.1, hp.2.1, hp.2.2.1⟩ hp.2.2.2
  · exact hcu
  · exact hnd
  · exact hdis
  · exact hs
  · exact hz

namespace Tri
variable {t : Tri}

theorem idx_facts (v : t.Valid) :
    t.idx.Nodup ∧ t.idx.length = 254 ∧ t.r1 ∉ t.idx ∧ t.r2 ∉ t.idx ∧ ∀ i ∈ t.idx, i < 256 := by
  have pv := pivots v
  have hnd : t.idx.Nodup := (List.nodup_range).filter _
  refine ⟨hnd, ?_, by simp [idx], by simp [idx], fun i hi => by
    simp only [idx, List.mem_filter, List.mem_range] at hi; exact hi.1⟩
  have e : t.idx.toFinset = Finset.range 256 \ {t.r1, t.r2} := by
    ext i; simp only [idx, List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_sdiff,
      Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, decide_eq_true_eq]; tauto
  rw [← List.toFinset_card_of_nodup hnd, e, Finset.card_sdiff]
  have hsub : ({t.r1, t.r2} : Finset Nat) ∩ Finset.range 256 = {t.r1, t.r2} := by
    apply Finset.inter_eq_left.mpr
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_range.mpr pv.1
    · exact Finset.mem_range.mpr pv.2.1
  rw [hsub, Finset.card_range, Finset.card_pair pv.2.2.1]

end Tri

theorem remapList_mc (tr : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) :
    measurementCount (tr.remapList xr1 xr2 w l) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [Tri.remapList, List.flatMap_cons, measurementCount_append] at ih ⊢
    rw [ih]
    simp only [Tri.remapBit, measurementCount_append]
    split_ifs <;> rfl

theorem tailEff_apply (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g : Wire) (hfg : f ≠ g) (u : Bool)
    (st : BasisState) (q : Wire) :
    tailEff tr yb xr1 xr2 y0 c f g u st q =
      if q = g then (st g ^^ genOut tr yb u (st xr1) (st xr2) (st y0) (st c) (st f))
      else if q = f then false else st q := by
  unfold tailEff
  by_cases hg : q = g
  · subst hg; simp [writeBit]
  · by_cases hf : q = f
    · subst hf; simp [writeBit, Function.update, hg]
    · simp [writeBit, Function.update, hg, hf]

theorem shape_run (tr : Tri) (v : tr.Valid) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t : Wire)
    (w : Nat → Wire) (i0 : Nat) (it : List Nat) (work : List Wire)
    (hPn : ((i0 :: it).map w).Nodup) (x1P : xr1 ∉ (i0 :: it).map w) (x2P : xr2 ∉ (i0 :: it).map w)
    (hused : [xr1, xr2, y0, c, f, g, g1, wB, t].Nodup)
    (hextP : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ (i0 :: it).map w)
    (hwl : (it.map w).length = work.length) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, g1, wB, t])
    (s : State) (m : List Bool)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis g1 = false ∧ s.basis wB = false ∧ s.basis t = false)
    (hf : s.basis f = !(((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) &&
      decide ((s.basis xr1, s.basis xr2) = tr.pat tr.S))) :
    run (tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (tail tr yb xr1 xr2 y0 c f g g1 wB t) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it))))) m s =
      ⟨s.phase, tailEff tr yb xr1 xr2 y0 c f g
        ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis⟩ := by
  have hlw : (i0 :: it).map w = w i0 :: it.map w := rfl
  have p0l : w i0 ∈ (i0 :: it).map w := by simp
  have usedNotP : ∀ q ∈ [xr1, xr2, y0, c, f, g, g1, wB, t], q ∉ (i0 :: it).map w := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | hq
    · exact x1P
    · exact x2P
    · exact hextP q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
  have itNe : ∀ i ∈ it, w i ≠ w i0 := by
    intro i hi e
    rw [hlw] at hPn
    exact (List.nodup_cons.mp hPn).1 (e ▸ List.mem_map_of_mem hi)
  -- step 1: remap
  have R1 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P m s
  rw [LocalWireModel.run_concat, remapList_mc, List.drop_zero, LocalWireModel.run_concat]
  generalize hs1 : run (tr.remapList xr1 xr2 w (i0 :: it)) m s = s1 at R1 ⊢
  -- step 2: X p0
  have e2 : run [Instr.X (w i0)] m s1 = ⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ := by
    simp [run]
  rw [e2]
  generalize hs2 : (⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ : State) = s2
  have s2ph : s2.phase = s.phase := by rw [← hs2]; exact R1.1
  have s2out : ∀ q, q ∉ (i0 :: it).map w → s2.basis q = s.basis q := by
    intro q hq
    have hq0 : q ≠ w i0 := fun e => hq (e ▸ p0l)
    rw [← hs2]; simp [writeBit, Function.update, hq0, R1.2.1 q hq]
  have s2p0 : s2.basis (w i0) = (s.basis (w i0) == tr.tgt i0 (s.basis xr1, s.basis xr2)) := by
    rw [← hs2]; simp only [writeBit, Function.update_self]
    rw [R1.2.2 i0 (by simp)]
    cases s.basis (w i0) <;> cases tr.tgt i0 (s.basis xr1, s.basis xr2) <;> rfl
  have s2it : ∀ i ∈ it, s2.basis (w i) = (s.basis (w i) ^^ tr.tgt i (s.basis xr1, s.basis xr2)) := by
    intro i hi
    rw [← hs2]; simp only [writeBit]
    rw [Function.update_of_ne (itNe i hi), R1.2.2 i (by simp [hi])]
  have k1 : s2.basis xr1 = s.basis xr1 := s2out xr1 x1P
  have k2 : s2.basis xr2 = s.basis xr2 := s2out xr2 x2P
  -- the zero-test value equals the match bit
  have zp := zeroPorts_maps (it.map w) work hwl
  have huV : (s2.basis (w i0) && (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input)) =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    have hall : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
        it.all (fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
      have : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
          ((zeroPorts (it.map w) work).map ZeroBit.input).all (fun q => !s2.basis q) := by
        rw [List.all_map]; rfl
      rw [this, zp.1, List.all_map, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      apply forall₂_congr
      intro i hi
      simp only [Function.comp_apply, s2it i hi]
      cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> simp
    rw [hall, s2p0]
    simp [List.all_cons]
  -- step 3: the zero-test chain with the decode tail
  have hcu : w i0 ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] := fun h => usedNotP _ h p0l
  have hperm := zeroPorts_perm (it.map w) work hwl
  have hnd : (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_append.mp (hperm.mem_iff.mp hm) with h | h
      · obtain ⟨i, hi, e⟩ := List.mem_map.mp h
        exact itNe i hi e
      · exact (hdisj _ h).1 p0l
    · apply hperm.symm.nodup_iff.mp
      apply List.nodup_append.mpr
      refine ⟨(List.nodup_cons.mp (hlw ▸ hPn)).2, hwn, ?_⟩
      intro a ha b hb e
      subst e
      exact (hdisj a hb).1 (by rw [hlw]; exact List.mem_cons_of_mem _ ha)
  have hfg : f ≠ g := by
    intro e; rw [e] at hused; simp at hused
  have hdis' : ∀ b ∈ zeroPorts (it.map w) work, b.input ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] := by
    intro b hb
    have hin : b.input ∈ it.map w := by
      have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    exact ⟨fun h => usedNotP _ h (by rw [hlw]; exact List.mem_cons_of_mem _ hin), (hdisj _ hwk).2⟩
  have hs3 : tailPre tr xr1 xr2 f g1 wB t
      (s2.basis (w i0) && (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input)) s2.basis := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [s2out g1 (usedNotP g1 (by simp))]; exact hz.2.1
    · rw [s2out wB (usedNotP wB (by simp))]; exact hz.2.2.1
    · rw [s2out t (usedNotP t (by simp))]; exact hz.2.2.2
    · rw [s2out f (usedNotP f (by simp)), huV, k1, k2]; exact hf
  have hz3 : ∀ b ∈ zeroPorts (it.map w) work, s2.basis b.work = false := by
    intro b hb
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    rw [s2out _ (hdisj _ hwk).1]; exact hz.1 _ hwk
  rw [LocalWireModel.run_concat, chain_run tr v yb xr1 xr2 y0 c f g g1 wB t hused (w i0) _ hcu hnd hdis'
    s2 _ hs3 hz3, huV, LocalWireModel.run_concat]
  set V := (i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2) with hV
  set T3 := tailEff tr yb xr1 xr2 y0 c f g V s2.basis with hT3
  have e4 : ∀ mm, run [Instr.X (w i0)] mm ⟨s2.phase, T3⟩ = ⟨s2.phase, writeBit T3 (w i0) (!T3 (w i0))⟩ := by
    intro mm; simp [run]
  rw [e4]
  generalize hs4 : (⟨s2.phase, writeBit T3 (w i0) (!T3 (w i0))⟩ : State) = s4
  have T3out : ∀ q, q ∉ (i0 :: it).map w → T3 q = tailEff tr yb xr1 xr2 y0 c f g V s.basis q := by
    intro q hq
    rw [hT3, tailEff_apply tr yb xr1 xr2 y0 c f g hfg, tailEff_apply tr yb xr1 xr2 y0 c f g hfg]
    rw [s2out g (usedNotP g (by simp)), k1, k2, s2out y0 (usedNotP y0 (by simp)),
      s2out c (usedNotP c (by simp)), s2out f (usedNotP f (by simp)), s2out q hq]
  have T3in : ∀ q, q ≠ f → q ≠ g → T3 q = s2.basis q := by
    intro q h1 h2; rw [hT3, tailEff_apply tr yb xr1 xr2 y0 c f g hfg]; simp [h1, h2]
  have s4x1 : s4.basis xr1 = s.basis xr1 := by
    rw [← hs4]; simp only [writeBit]
    rw [Function.update_of_ne (fun e => hcu (by simp [e])), T3in xr1
      (fun e => by rw [e] at hused; simp at hused) (fun e => by rw [e] at hused; simp at hused), k1]
  have s4x2 : s4.basis xr2 = s.basis xr2 := by
    rw [← hs4]; simp only [writeBit]
    rw [Function.update_of_ne (fun e => hcu (by simp [e])), T3in xr2
      (fun e => by rw [e] at hused; simp at hused) (fun e => by rw [e] at hused; simp at hused), k2]
  -- step 5: remap again
  suffices key : ∀ mm, run (tr.remapList xr1 xr2 w (i0 :: it)) mm s4 =
      ⟨s.phase, tailEff tr yb xr1 xr2 y0 c f g V s.basis⟩ from key _
  intro mm
  have R5 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P mm s4
  apply State.extensionality
  · rw [R5.1, ← hs4]; exact s2ph
  · funext q
    by_cases hq : q ∈ (i0 :: it).map w
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      rw [R5.2.2 i hi, s4x1, s4x2]
      have rhs : tailEff tr yb xr1 xr2 y0 c f g V s.basis (w i) = s.basis (w i) := by
        rw [tailEff_apply tr yb xr1 xr2 y0 c f g hfg]
        have h1 : w i ≠ g := fun e => usedNotP g (by simp) (e ▸ hq)
        have h2 : w i ≠ f := fun e => usedNotP f (by simp) (e ▸ hq)
        simp [h1, h2]
      change (s4.basis (w i) ^^ _) = tailEff tr yb xr1 xr2 y0 c f g V s.basis (w i)
      rw [rhs]
      have h1 : w i ≠ g := fun e => usedNotP g (by simp) (e ▸ hq)
      have h2 : w i ≠ f := fun e => usedNotP f (by simp) (e ▸ hq)
      rw [← hs4]; simp only [writeBit]
      rcases List.mem_cons.mp hi with rfl | hit
      · rw [Function.update_self, T3in _ h2 h1, s2p0]
        cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> rfl
      · rw [Function.update_of_ne (itNe i hit), T3in _ h2 h1, s2it i hit]
        cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> rfl
    · rw [R5.2.1 q hq, ← hs4]
      change writeBit T3 (w i0) (!T3 (w i0)) q = tailEff tr yb xr1 xr2 y0 c f g V s.basis q
      simp only [writeBit]
      rw [Function.update_of_ne (fun e : q = w i0 => hq (e ▸ p0l)), T3out q hq]



/-- The merged classifier on the abscissa `xs`: remap, zero-test the non-pivot bits, decode, undo. -/
def classifier (tr : Tri) (yb : Bool) (xs work : List Wire) (y0 c f g g1 wB t : Wire) : Program :=
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  (zeroWith (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work) ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx)))

/-- Zero-test value of the merged classifier. -/
def matchBit (tr : Tri) (xs : List Wire) (st : BasisState) : Bool :=
  tr.idx.all (fun i => st (xs.getD i 0) == tr.tgt i (st (xs.getD tr.r1 0), st (xs.getD tr.r2 0)))

theorem classifier_run (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t : Wire)
    (hxs : xs.Nodup) (hlen : xs.length = 256) (hwl : work.length = 253) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, g1, wB, t].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ xs ∧ q ∉ work)
    (s : State) (m : List Bool)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis g1 = false ∧ s.basis wB = false ∧ s.basis t = false)
    (hf : s.basis f = !(matchBit tr xs s.basis &&
      decide ((s.basis (xs.getD tr.r1 0), s.basis (xs.getD tr.r2 0)) = tr.pat tr.S))) :
    run (classifier tr yb xs work y0 c f g g1 wB t) m s =
      ⟨s.phase, tailEff tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g
        (matchBit tr xs s.basis) s.basis⟩ := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  set w : Nat → Wire := fun i => xs.getD i 0 with hw
  set xr1 := w tr.r1 with hx1
  set xr2 := w tr.r2 with hx2
  set P := tr.idx.map w with hP
  have winj : ∀ i j, i < 256 → j < 256 → w i = w j → i = j := by
    intro i j hi hj e
    simp only [hw] at e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    exact hxs.getElem_inj_iff.mp e
  have wmem : ∀ i, i < 256 → w i ∈ xs := by
    intro i hi; simp only [hw]; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hPn : P.Nodup := by
    apply List.Nodup.map_on _ ix.1
    intro i hi j hj e; exact winj i j (ix.2.2.2.2 i hi) (ix.2.2.2.2 j hj) e
  have memP : ∀ q, q ∈ P ↔ ∃ i ∈ tr.idx, w i = q := by intro q; simp [hP]
  have x1P : xr1 ∉ P := by
    rw [memP]; rintro ⟨i, hi, e⟩
    exact ix.2.2.1 (winj i tr.r1 (ix.2.2.2.2 i hi) pv.1 e ▸ hi)
  have x2P : xr2 ∉ P := by
    rw [memP]; rintro ⟨i, hi, e⟩
    exact ix.2.2.2.1 (winj i tr.r2 (ix.2.2.2.2 i hi) pv.2.1 e ▸ hi)
  have x12 : xr1 ≠ xr2 := fun e => pv.2.2.1 (winj _ _ pv.1 pv.2.1 e)
  have Psub : ∀ q ∈ P, q ∈ xs := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := (memP q).mp hq; exact wmem i (ix.2.2.2.2 i hi)
  have hPl : P.length = 254 := by simp [hP, ix.2.1]
  obtain ⟨i0, it, hidx⟩ : ∃ i0 it, tr.idx = i0 :: it := by
    have hl := ix.2.1
    cases h : tr.idx with
    | nil => rw [h] at hl; simp at hl
    | cons a l => exact ⟨a, l, rfl⟩
  have hP0 : P = w i0 :: it.map w := by simp [hP, hidx]
  set p0 := w i0 with hp0
  have hPt : P.tail = it.map w := by rw [hP0]; rfl
  have hPh : P.headD 0 = p0 := by rw [hP0]; rfl
  have hitl : (it.map w).length = 253 := by
    have := hPl; rw [hP0] at this; simpa using this
  have zp := zeroPorts_maps (it.map w) work (by rw [hitl, hwl])
  -- membership facts for the outside wires
  have extx (q : Wire) (hq : q ∈ [y0, c, f, g, g1, wB, t]) : q ∉ P ∧ q ∉ work ∧ q ≠ xr1 ∧ q ≠ xr2 := by
    have h := hextx q hq
    refine ⟨fun hp => h.1 (Psub q hp), h.2, fun e => h.1 (e ▸ wmem _ pv.1), fun e => h.1 (e ▸ wmem _ pv.2.1)⟩
  have p0P : p0 ∈ P := by rw [hP0]; simp
  have hused : [xr1, xr2, y0, c, f, g, g1, wB, t].Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hext⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨x12, ?_⟩
      have := fun q hq => (extx q hq).2.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      exact ⟨fun e => this y0 (Or.inl rfl) e.symm, fun e => this c (by tauto) e.symm,
        fun e => this f (by tauto) e.symm, fun e => this g (by tauto) e.symm,
        fun e => this g1 (by tauto) e.symm, fun e => this wB (by tauto) e.symm,
        fun e => this t (by tauto) e.symm⟩
    · intro hm
      exact (extx xr2 hm).2.2.2 rfl
  have hlP : (i0 :: it).map w = P := by rw [hP0]; rfl
  have hPn' : ((i0 :: it).map w).Nodup := by rw [hlP]; exact hPn
  have x1P' : xr1 ∉ (i0 :: it).map w := by rw [hlP]; exact x1P
  have x2P' : xr2 ∉ (i0 :: it).map w := by rw [hlP]; exact x2P
  have hextP : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ (i0 :: it).map w := by
    intro q hq; rw [hlP]; exact (extx q hq).1
  have hdisj' : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] := by
    intro q hq
    refine ⟨fun hm => hdisj q hq (Psub q (by rw [← hlP]; exact hm)), ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (e | e | e)
    · exact hdisj q hq (e ▸ wmem _ pv.1)
    · exact hdisj q hq (e ▸ wmem _ pv.2.1)
    · exact (hextx q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)).2 hq
  have hmb : matchBit tr xs s.basis =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    simp only [matchBit, hidx]; rfl
  have hf' : s.basis f = !(((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) &&
      decide ((s.basis xr1, s.basis xr2) = tr.pat tr.S)) := by rw [← hmb]; exact hf
  have run_eq := shape_run tr v yb xr1 xr2 y0 c f g g1 wB t w i0 it work hPn' x1P' x2P' hused hextP
    (by rw [hitl, hwl]) hwn hdisj' s m hz hf'
  rw [hmb]
  have hprog : classifier tr yb xs work y0 c f g g1 wB t =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (tail tr yb xr1 xr2 y0 c f g g1 wB t) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [classifier, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  rw [hprog]
  exact run_eq

section Glue
open Secp256k1

/-- The three compared words for the classical point `C`. -/
def triOf (C : Point) : Tri := ⟨pairCode C, pairCode (dialogExceptionPoint C), FiniteFlagInterval.sentinel⟩

theorem exception_code {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    pairCode (dialogExceptionPoint (.some hc : Point)) =
      (doubleX cx cy).val := by
  have hy : cy ≠ -cy := of_decide_eq_true (cy_ne_neg hc)
  unfold dialogExceptionPoint
  rw [pairCode_neg, ← doublePoint_correct hc hy]
  rfl

theorem triOf_valid {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : (triOf (.some hc)).Valid := by
  have hy : cy ≠ -cy := of_decide_eq_true (cy_ne_neg hc)
  have hd := double_nonsingular hc hy
  have hB := exception_code hc
  have hA : pairCode (.some hc : Point) = cx.val := rfl
  have p256 : p < 2^256 := by norm_num [p]
  refine ⟨pairCode_lt _, pairCode_lt _, lt_trans FiniteFlagInterval.sentinel_lt p256, ?_, ?_, ?_⟩
  · show pairCode (.some hc : Point) ≠ pairCode (dialogExceptionPoint (.some hc : Point))
    rw [hA, hB]; intro e
    exact NoThreeTorsion.double_x_ne hc (ZMod.val_injective _ e.symm)
  · show pairCode (.some hc : Point) ≠ FiniteFlagInterval.sentinel
    rw [hA]; intro e
    exact FiniteFlagInterval.curve_x_not_interval hc (Or.inr (Or.inr (by rw [e]; rfl)))
  · show pairCode (dialogExceptionPoint (.some hc : Point)) ≠ FiniteFlagInterval.sentinel
    rw [hB]; intro e
    exact FiniteFlagInterval.curve_x_not_interval hd (Or.inr (Or.inr (by rw [e]; rfl)))

/-- The decoded flags agree with the dialog classification once `x` carries the sentinel for `O`. -/
theorem glue [DecidableEq Point] {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    let tr := triOf (.some hc)
    let X := if pointFinite R then pointX R else FiniteFlagInterval.sentinel
    let V := tr.idx.all (fun i => X.testBit i == tr.tgt i (X.testBit tr.r1, X.testBit tr.r2))
    pointFinite R = !(V && decide ((X.testBit tr.r1, X.testBit tr.r2) = tr.pat tr.S)) ∧
    genOut tr (yBit (dialogExceptionPoint (.some hc))) V (X.testBit tr.r1) (X.testBit tr.r2)
      (yBit R) b (pointFinite R) = dialogOrdinary b R (.some hc) := by
  intro tr X V
  have v : tr.Valid := triOf_valid hc
  have pv := Tri.pivots v
  have p256 : p < 2^256 := by norm_num [p]
  have hX : X < 2^256 := by
    simp only [X]; split_ifs
    · exact pairCode_lt R
    · exact lt_trans FiniteFlagInterval.sentinel_lt p256
  have hV : V = true ↔ ∀ i ∈ tr.idx, X.testBit i = tr.tgt i (tr.pat X) := by
    simp only [V, List.all_eq_true, beq_iff_eq, Tri.pat]
  have mK : ∀ K, K < 2^256 → (∀ i, tr.tgt i (tr.pat K) = K.testBit i) →
      ((V = true ∧ tr.pat X = tr.pat K) ↔ X = K) := by
    intro K hK hKt
    rw [hV]; exact Tri.match_iff v X K hX hK hKt
  have mA := mK tr.A v.hA (fun i => Tri.tgt_A i)
  have mB := mK tr.B v.hB (Tri.tgt_B v)
  have mS := mK tr.S v.hS (Tri.tgt_S v)
  have epat : tr.pat X = (X.testBit tr.r1, X.testBit tr.r2) := rfl
  -- pattern bits of the three words
  have ePA : tr.pat tr.A = (tr.A.testBit tr.r1, tr.A.testBit tr.r2) := rfl
  have ePB : tr.pat tr.B = (tr.B.testBit tr.r1, tr.B.testBit tr.r2) := rfl
  have ePS : tr.pat tr.S = (tr.S.testBit tr.r1, tr.S.testBit tr.r2) := rfl
  have hBS1 : tr.B.testBit tr.r1 ≠ tr.S.testBit tr.r1 := (firstDiff_spec tr.B tr.S v.hB v.hS v.BS).2
  set x1 := X.testBit tr.r1 with hx1
  set x2 := X.testBit tr.r2 with hx2
  set a1 := tr.A.testBit tr.r1
  set a2 := tr.A.testBit tr.r2
  set b1 := tr.B.testBit tr.r1
  set b2 := tr.B.testBit tr.r2
  set s1 := tr.S.testBit tr.r1
  set s2 := tr.S.testBit tr.r2
  rw [epat] at mA mB mS
  rw [ePA] at mA; rw [ePB] at mB; rw [ePS] at mS
  have eS : (V && decide ((x1, x2) = (s1, s2))) = decide (X = tr.S) := by
    apply Bool.eq_iff_iff.mpr; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact mS
  have dAB : X = tr.A → X ≠ tr.B := fun h e => v.AB (h.symm.trans e)
  have dAS : X = tr.A → X ≠ tr.S := fun h e => v.AS (h.symm.trans e)
  have dBS : X = tr.B → X ≠ tr.S := fun h e => v.BS (h.symm.trans e)
  -- the decoded flag in terms of the three matches
  have key : genOut tr (yBit (dialogExceptionPoint (.some hc))) V x1 x2 (yBit R) b
      (!(decide (X = tr.S))) =
      (b && !(decide (X = tr.A) || decide (X = tr.S) ||
        (decide (X = tr.B) && (yBit R == yBit (dialogExceptionPoint (.some hc)))))) := by
    unfold genOut
    by_cases ro : tr.role1 = true
    · have e1 : a1 = s1 := by simpa [Tri.role1] using ro
      have er2 : tr.r2 = firstDiff tr.A tr.S := by simp [Tri.r2, ro]
      have n2 : a2 ≠ s2 := by
        have d := (firstDiff_spec tr.A tr.S v.hA v.hS v.AS).2; rw [← er2] at d; exact d
      have k1 : (V && (x1 == a1)) = (decide (X = tr.A) || decide (X = tr.S)) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨hv, h1⟩
          by_cases h2 : x2 = a2
          · exact Or.inl (mA.mp ⟨hv, by rw [h1, h2]⟩)
          · have h2' : x2 = s2 := by
              cases hx : x2 <;> cases ha : a2 <;> cases hs : s2 <;> simp_all
            exact Or.inr (mS.mp ⟨hv, by rw [h1, h2', e1]⟩)
        · rintro (h | h)
          · obtain ⟨hv, hp⟩ := mA.mpr h; exact ⟨hv, (Prod.mk.inj hp).1⟩
          · obtain ⟨hv, hp⟩ := mS.mpr h; exact ⟨hv, (Prod.mk.inj hp).1.trans e1.symm⟩
      have k2 : (V && (x1 != a1) && (x2 == b2)) = decide (X = tr.B) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨hv, h1⟩, h2⟩
          have h1' : x1 = b1 := by
            have : b1 ≠ a1 := by rw [e1]; exact hBS1
            cases hx : x1 <;> cases ha : a1 <;> cases hb : b1 <;> simp_all
          exact mB.mp ⟨hv, by rw [h1', h2]⟩
        · intro h
          obtain ⟨hv, hp⟩ := mB.mpr h
          have hb1 : b1 ≠ a1 := by rw [e1]; exact hBS1
          refine ⟨⟨hv, ?_⟩, (Prod.mk.inj hp).2⟩
          rw [(Prod.mk.inj hp).1]; exact hb1
      simp only [ro, if_true]
      rw [k1, show (V && (x1 != a1) && (x2 == b2) &&
          (yBit R == yBit (dialogExceptionPoint (.some hc)))) =
        ((V && (x1 != a1) && (x2 == b2)) && (yBit R == yBit (dialogExceptionPoint (.some hc)))) from rfl, k2]
    · have ro' : tr.role1 = false := by simpa using ro
      have ne1 : a1 ≠ s1 := by simpa [Tri.role1] using ro
      have e1 : a1 = b1 := by
        cases ha : a1 <;> cases hb : b1 <;> cases hs : s1 <;> simp_all
      have er2 : tr.r2 = firstDiff tr.A tr.B := by simp [Tri.r2, ro']
      have n2 : a2 ≠ b2 := by
        have d := (firstDiff_spec tr.A tr.B v.hA v.hB v.AB).2; rw [← er2] at d; exact d
      have k1 : (V && (x1 == a1) && (x2 == a2)) = decide (X = tr.A) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨hv, h1⟩, h2⟩; exact mA.mp ⟨hv, by rw [h1, h2]⟩
        · intro h; obtain ⟨hv, hp⟩ := mA.mpr h; exact ⟨⟨hv, (Prod.mk.inj hp).1⟩, (Prod.mk.inj hp).2⟩
      have k2 : (V && (x1 == a1) && (x2 != a2)) = decide (X = tr.B) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨hv, h1⟩, h2⟩
          have h2' : x2 = b2 := by
            cases hx : x2 <;> cases ha : a2 <;> cases hb : b2 <;> simp_all
          exact mB.mp ⟨hv, by rw [h1, h2', e1]⟩
        · intro h
          obtain ⟨hv, hp⟩ := mB.mpr h
          refine ⟨⟨hv, (Prod.mk.inj hp).1.trans e1.symm⟩, ?_⟩
          rw [(Prod.mk.inj hp).2]; exact Ne.symm n2
      simp only [ro', Bool.false_eq_true, if_false]
      rw [show (V && (x1 == a1) && (x2 != a2) && (yBit R == yBit (dialogExceptionPoint (.some hc)))) =
        ((V && (x1 == a1) && (x2 != a2)) && (yBit R == yBit (dialogExceptionPoint (.some hc)))) from rfl,
        k1, k2]
      by_cases hA : X = tr.A
      · have := dAB hA; have := dAS hA; simp_all
      · by_cases hB : X = tr.B
        · have := dBS hB; simp_all
        · cases decide (X = tr.S) <;> simp_all
  have hC0 : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have fin_iff : pointFinite R = !(decide (X = tr.S)) := by
    cases R with
    | zero =>
      have pf0 : pointFinite (WeierstrassCurve.Affine.Point.zero : Point) = false := rfl
      have hX0 : X = FiniteFlagInterval.sentinel := by simp only [X, pf0, Bool.false_eq_true, if_false]
      rw [pf0, hX0]; simp [tr, triOf]
    | @some rx ry hr =>
      have pf1 : pointFinite (.some hr : Point) = true := rfl
      have hX1 : X = rx.val := by simp only [X, pf1, if_true]; rfl
      have hne : rx.val ≠ FiniteFlagInterval.sentinel := by
        intro e; exact FiniteFlagInterval.curve_x_not_interval hr (Or.inr (Or.inr (by rw [e]; rfl)))
      rw [pf1, hX1]; simp [tr, triOf, hne]
  refine ⟨?_, ?_⟩
  · rw [fin_iff, ePS, ← eS]
  · rw [fin_iff, key]
    apply Bool.eq_iff_iff.mpr
    rw [dialogOrdinary_true b R _ hC0]
    cases R with
    | zero =>
      have pf0 : pointFinite (WeierstrassCurve.Affine.Point.zero : Point) = false := rfl
      have hX0 : X = tr.S := by simp only [X, pf0, Bool.false_eq_true, if_false]; rfl
      rw [hX0]
      constructor
      · intro h; simp at h
      · rintro ⟨_, h, _⟩; exact absurd rfl h
    | @some rx ry hr =>
      have pf1 : pointFinite (.some hr : Point) = true := rfl
      have hX1 : X = pairCode (.some hr : Point) := by simp only [X, pf1, if_true]; rfl
      have hR0 : (.some hr : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hr
      have hne : X ≠ tr.S := by
        rw [hX1]; intro e
        exact FiniteFlagInterval.curve_x_not_interval hr (Or.inr (Or.inr (by
          rw [show rx.val = pairCode (.some hr : Point) from rfl, e]; rfl)))
      have hAeq : X = tr.A ↔ ((.some hr : Point) = .some hc ∨ (.some hr : Point) = -(.some hc : Point)) := by
        rw [hX1, ← sameX_iff_eq_or_neg hr hc]
        constructor
        · intro e; exact ZMod.val_injective _ e
        · intro e; show rx.val = cx.val; rw [e]
      have hBeq : (decide (X = tr.B) && (yBit (.some hr : Point) == yBit (dialogExceptionPoint (.some hc)))) =
          decide ((.some hr : Point) = dialogExceptionPoint (.some hc)) := by
        rw [hX1]
        have := pair_value_eq (.some hr : Point) (dialogExceptionPoint (.some hc))
        rw [show tr.B = pairCode (dialogExceptionPoint (.some hc : Point)) from rfl, this]
        apply Bool.eq_iff_iff.mpr
        rw [pointEqual_true_iff]; simp
      rw [hBeq]
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
        hne, not_false_eq_true, and_true, ne_eq]
      constructor
      · rintro ⟨hb, hA, hE⟩
        refine ⟨hb, hR0, ?_, ?_, hE⟩
        · intro e; exact hA (hAeq.mpr (Or.inl e))
        · intro e; exact hA (hAeq.mpr (Or.inr e))
      · rintro ⟨hb, -, h1, h2, hE⟩
        refine ⟨hb, ?_, hE⟩
        intro hA; rcases hAeq.mp hA with e | e
        · exact h1 e
        · exact h2 e

end Glue

theorem corrections_fix (f : Wire → Wire) (cs : List Correction)
    (h : ∀ w ∈ correctionWires cs, f w = w) : cs.map (renameCorrection f) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | Z t =>
      simp only [correctionWires, Finset.mem_union, Finset.mem_singleton] at h
      simp [renameCorrection, h t (Or.inl rfl), ih (fun w hw => h w (Or.inr hw))]
    | CZ a b =>
      simp only [correctionWires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
      simp [renameCorrection, h a (Or.inl (Or.inl rfl)), h b (Or.inl (Or.inr rfl)),
        ih (fun w hw => h w (Or.inr hw))]

/-- A relabelling that fixes every wire of a program leaves it unchanged. -/
theorem rename_fix (f : Wire → Wire) (P : Program) (h : ∀ w ∈ wires P, f w = w) :
    renameProgram f P = P := by
  induction P with
  | nil => rfl
  | cons i P ih =>
    have hi : ∀ w ∈ i.wires, f w = w := fun w hw => h w (by simp [wires, hw])
    have hP : ∀ w ∈ wires P, f w = w := fun w hw => h w (by simp [wires, hw])
    have e := ih hP
    simp only [renameProgram, List.map_cons] at e ⊢
    rw [e]
    congr 1
    cases i with
    | X t => simp only [Instr.wires, Finset.mem_singleton] at hi; simp [renameInstr, hi t rfl]
    | CX c t =>
      simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hi
      simp [renameInstr, hi c (Or.inl rfl), hi t (Or.inr rfl)]
    | CCX a b t =>
      simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hi
      simp [renameInstr, hi a (Or.inl rfl), hi b (Or.inr (Or.inl rfl)), hi t (Or.inr (Or.inr rfl))]
    | measureX t c0 c1 =>
      simp only [Instr.wires, Finset.mem_union, Finset.mem_singleton] at hi
      simp [renameInstr, hi t (Or.inl (Or.inl rfl)),
        corrections_fix f c0 (fun w hw => hi w (Or.inl (Or.inr hw))),
        corrections_fix f c1 (fun w hw => hi w (Or.inr hw))]

section Stage
open Secp256k1 ControlledPointLayout

/-- The merged input stage: sentinel-code `x`, then the three-word classifier. -/
def stage (L : ControlledPointLayout) (C : Point) : Program :=
  FiniteFlagInterval.zrep L ++
  classifier (triOf C) (yBit (dialogExceptionPoint C)) L.point.x (L.dialogPool.take 253)
    (yLow L) L.control L.point.finite L.genericSelect
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0)

/-- Sentinel-coded abscissa: `x` for a finite point, the sentinel for `O`. -/
def codeX (R : Point) : Nat := if pointFinite R then pointX R else FiniteFlagInterval.sentinel

/-- State after the input stage: `x` sentinel-coded, the finite flag cleared, the generic select set. -/
def Mid (L : ControlledPointLayout) (R : Point) (G : Bool) (s t : State) : Prop :=
  t.phase = s.phase ∧ regValue L.point.x t.basis = codeX R ∧ t.basis L.point.finite = false ∧
    t.basis L.genericSelect = G ∧
    ∀ q, q ∉ L.point.x → q ≠ L.point.finite → q ≠ L.genericSelect → t.basis q = s.basis q

theorem Mid.unique {L : ControlledPointLayout} {R : Point} {G : Bool} {s t u : State}
    (ht : Mid L R G s t) (hu : Mid L R G s u) : t = u := by
  apply State.extensionality
  · exact ht.1.trans hu.1.symm
  · funext q
    by_cases hx : q ∈ L.point.x
    · exact (regValue_eq_iff _ _ _).mp (ht.2.1.trans hu.2.1.symm) q hx
    by_cases hf : q = L.point.finite
    · subst hf; exact ht.2.2.1.trans hu.2.2.1.symm
    by_cases hg : q = L.genericSelect
    · subst hg; exact ht.2.2.2.1.trans hu.2.2.2.1.symm
    exact (ht.2.2.2.2 q hx hf hg).trans (hu.2.2.2.2 q hx hf hg).symm

/-- Wire facts of the dialog layout used by the merged stage. -/
theorem stage_layout (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.point.x.Nodup ∧ L.point.x.length = 256 ∧ (L.dialogPool.take 253).length = 253 ∧
    (L.dialogPool.take 253).Nodup ∧ (∀ q ∈ L.dialogPool.take 253, q ∉ L.point.x) ∧
    [yLow L, L.control, L.point.finite, L.genericSelect,
      L.dialogPool.getD 253 0, L.dialogPool.getD 254 0, L.dialogPool.getD 255 0].Nodup ∧
    (∀ q ∈ [yLow L, L.control, L.point.finite, L.genericSelect,
      L.dialogPool.getD 253 0, L.dialogPool.getD 254 0, L.dialogPool.getD 255 0],
      q ∉ L.point.x ∧ q ∉ L.dialogPool.take 253) := by
  have hD := L.dialogUsed_nodup hn
  have hxl : L.point.x.length = 256 := hw.inputX
  have hyl : L.point.y.length = 256 := hw.inputY
  have hpl := dialogPool_length L hw
  have C : ∀ q, (if q = L.point.finite then 1 else 0) + L.point.x.count q + L.point.y.count q +
      (if q = L.control then 1 else 0) + L.inPlaceFlags.count q + L.dialogPool.count q ≤ 1 := by
    intro q
    have h := List.nodup_iff_count_le_one.mp hD q
    simp only [dialogUsedWires, PointAddLayout.pointWires, List.count_append, List.count_cons,
      List.count_singleton', List.count_nil] at h
    split_ifs at h ⊢ <;> simp_all <;> omega
  have pos (l : List Wire) (q : Wire) (h : q ∈ l) : 1 ≤ l.count q := List.count_pos_iff.mpr h
  have hpn : L.dialogPool.Nodup := List.nodup_iff_count_le_one.mpr (fun q => by have := C q; omega)
  have hxn : L.point.x.Nodup := List.nodup_iff_count_le_one.mpr (fun q => by have := C q; omega)
  have xp : ∀ q, q ∈ L.dialogPool → q ∉ L.point.x := by
    intro q h1 h2; have := C q; have := pos _ _ h1; have := pos _ _ h2; omega
  have pget (i : Nat) (hi : i < 2613) : L.dialogPool.getD i 0 ∈ L.dialogPool := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have takeMem : ∀ q ∈ L.dialogPool.take 253, q ∈ L.dialogPool := fun q h => List.mem_of_mem_take h
  have pnot (i : Nat) (hi : 253 ≤ i) (hi2 : i < 2613) : L.dialogPool.getD i 0 ∉ L.dialogPool.take 253 := by
    intro h
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem h
    rw [List.getElem_take] at e
    rw [List.getD_eq_getElem _ _ (by omega)] at e
    have hj' : j < 253 := by simpa [List.length_take, hpl] using hj
    have := (hpn.getElem_inj_iff).mp e
    omega
  have pne (i j : Nat) (hi : i < 2613) (hj : j < 2613) (hij : i ≠ j) :
      L.dialogPool.getD i 0 ≠ L.dialogPool.getD j 0 := by
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    intro e; exact hij ((hpn.getElem_inj_iff).mp e)
  have yl : yLow L ∈ L.point.y := by
    unfold yLow
    rw [show L.point.y.headD L.control = L.point.y.getD 0 L.control by
      cases L.point.y <;> rfl]
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have gf : L.genericSelect ∈ L.inPlaceFlags := by simp [inPlaceFlags]
  -- region separation from the counts
  have Cq (q : Wire) := C q
  have yx : ∀ q ∈ L.point.y, q ∉ L.point.x := by
    intro q h1 h2; have := Cq q; have := pos _ _ h1; have := pos _ _ h2; omega
  have yfl : ∀ q ∈ L.point.y, q ∉ L.inPlaceFlags := by
    intro q h1 h2; have := Cq q; have := pos _ _ h1; have := pos _ _ h2; omega
  have yp : ∀ q ∈ L.point.y, q ∉ L.dialogPool := by
    intro q h1 h2; have := Cq q; have := pos _ _ h1; have := pos _ _ h2; omega
  have flx : ∀ q ∈ L.inPlaceFlags, q ∉ L.point.x := by
    intro q h1 h2; have := Cq q; have := pos _ _ h1; have := pos _ _ h2; omega
  have flp : ∀ q ∈ L.inPlaceFlags, q ∉ L.dialogPool := by
    intro q h1 h2; have := Cq q; have := pos _ _ h1; have := pos _ _ h2; omega
  have yc : ∀ q ∈ L.point.y, q ≠ L.control := by
    intro q h1 e; subst e; have c := Cq L.control; have hp := pos _ _ h1
    simp only [eq_self_iff_true, if_true] at c; omega
  have yf : ∀ q ∈ L.point.y, q ≠ L.point.finite := by
    intro q h1 e; subst e; have c := Cq L.point.finite; have hp := pos _ _ h1
    simp only [eq_self_iff_true, if_true] at c; omega
  have cx : L.control ∉ L.point.x := by
    intro h; have c := Cq L.control; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have cfl : L.control ∉ L.inPlaceFlags := by
    intro h; have c := Cq L.control; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have cp : L.control ∉ L.dialogPool := by
    intro h; have c := Cq L.control; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have fx : L.point.finite ∉ L.point.x := by
    intro h; have c := Cq L.point.finite; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have ffl : L.point.finite ∉ L.inPlaceFlags := by
    intro h; have c := Cq L.point.finite; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have fp : L.point.finite ∉ L.dialogPool := by
    intro h; have c := Cq L.point.finite; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have cf : L.control ≠ L.point.finite := by
    intro e; have c := Cq L.control; rw [← e] at c; simp only [eq_self_iff_true, if_true] at c; omega
  have p3 := pget 253 (by decide); have p4 := pget 254 (by decide); have p5 := pget 255 (by decide)
  refine ⟨hxn, hxl, by simp [hpl], hpn.sublist (List.take_sublist _ _), fun q h => xp q (takeMem q h),
    ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true]
    refine ⟨⟨yc _ yl, yf _ yl, fun e => yfl _ yl (e ▸ gf), fun e => yp _ yl (e ▸ p3),
        fun e => yp _ yl (e ▸ p4), fun e => yp _ yl (e ▸ p5)⟩,
      ⟨cf, fun e => cfl (e ▸ gf), fun e => cp (e ▸ p3), fun e => cp (e ▸ p4), fun e => cp (e ▸ p5)⟩,
      ⟨fun e => ffl (e ▸ gf), fun e => fp (e ▸ p3), fun e => fp (e ▸ p4), fun e => fp (e ▸ p5)⟩,
      ⟨fun e => flp _ gf (e ▸ p3), fun e => flp _ gf (e ▸ p4), fun e => flp _ gf (e ▸ p5)⟩,
      ⟨pne 253 254 (by decide) (by decide) (by decide), pne 253 255 (by decide) (by decide) (by decide)⟩,
      ⟨pne 254 255 (by decide) (by decide) (by decide), not_false⟩⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨yx _ yl, fun h => yp _ yl (takeMem _ h)⟩
    · exact ⟨cx, fun h => cp (takeMem _ h)⟩
    · exact ⟨fx, fun h => fp (takeMem _ h)⟩
    · exact ⟨flx _ gf, fun h => flp _ gf (takeMem _ h)⟩
    · exact ⟨xp _ p3, pnot 253 le_rfl (by decide)⟩
    · exact ⟨xp _ p4, pnot 254 (by decide) (by decide)⟩
    · exact ⟨xp _ p5, pnot 255 (by decide) (by decide)⟩

theorem y_not_x (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    ∀ q ∈ L.point.y, q ∉ L.point.x := by
  have hD := L.dialogUsed_nodup hn
  intro q h1 h2
  have h := List.nodup_iff_count_le_one.mp hD q
  simp only [dialogUsedWires, PointAddLayout.pointWires, List.count_append, List.count_cons,
    List.count_singleton', List.count_nil] at h
  have c1 : 1 ≤ L.point.y.count q := List.count_pos_iff.mpr h1
  have c2 : 1 ≤ L.point.x.count q := List.count_pos_iff.mpr h2
  split_ifs at h <;> omega

theorem stage_mid [DecidableEq Point] (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary L R b (fun _ => false) s.basis) :
    Mid L R (dialogOrdinary b R (.some hc)) s (run (stage L (.some hc)) m s) := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, hext, hextx⟩ := stage_layout L hw hn
  have hp := (point_holds _ _ _).mp hs.point
  have v := triOf_valid hc
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  have hpl := dialogPool_length L hw
  have Z := FiniteFlagInterval.zrep_run L hw hn s m
  unfold stage
  rw [LocalWireModel.run_concat]
  generalize hs1 : run (FiniteFlagInterval.zrep L) m s = s1 at Z ⊢
  have fx : L.point.finite ∉ L.point.x := (hextx _ (by simp)).1
  have gx : L.genericSelect ∉ L.point.x := (hextx _ (by simp)).1
  have yx : yLow L ∉ L.point.x := (hextx _ (by simp)).1
  have cx' : L.control ∉ L.point.x := (hextx _ (by simp)).1
  have fg : L.point.finite ≠ L.genericSelect := by
    intro e; rw [e] at hext; simp at hext
  have hX : regValue L.point.x s1.basis = codeX R := by
    rw [Z.2.2, hp.2.1, hp.1]
    unfold codeX
    cases hf : pointFinite R
    · have hx0 : pointX R = 0 := by
        cases R with
        | zero => rfl
        | some h => simp [pointFinite] at hf
      simp [hx0]
    · simp
  have xbit : ∀ i, i < 256 → s1.basis (L.point.x.getD i 0) = (codeX R).testBit i := by
    intro i hi
    rw [← hX]; exact (LocalWireModel.reg_bit L.point.x s1.basis i (by rw [hxl]; exact hi)).symm
  have s1f : s1.basis L.point.finite = pointFinite R := (Z.2.1 _ fx).trans hp.1
  have s1g : s1.basis L.genericSelect = false := (Z.2.1 _ gx).trans
    (hs.flags _ (by simp [ControlledPointLayout.inPlaceFlags]))
  have s1c : s1.basis L.control = b := (Z.2.1 _ cx').trans hs.control
  have s1y : s1.basis (yLow L) = yBit R := by
    rw [Z.2.1 _ yx]
    have hyl : L.point.y.length = 256 := hw.inputY
    have e : yLow L = L.point.y.getD 0 0 := by
      unfold yLow
      cases hy : L.point.y with
      | nil => rw [hy] at hyl; simp at hyl
      | cons a l => rfl
    rw [e, ← LocalWireModel.reg_bit L.point.y s.basis 0 (by rw [hyl]; decide), hp.2.2]
    unfold yBit
    rw [Nat.testBit_zero]
  have s1p : ∀ q, q ∈ L.dialogPool → q ∉ L.point.x → s1.basis q = false := by
    intro q hq hx; rw [Z.2.1 _ hx]; exact (regValue_zero _ _).mp hs.clean q hq
  have pget (i : Nat) (hi : i < 2613) : L.dialogPool.getD i 0 ∈ L.dialogPool := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hz : (∀ q ∈ L.dialogPool.take 253, s1.basis q = false) ∧
      s1.basis (L.dialogPool.getD 253 0) = false ∧ s1.basis (L.dialogPool.getD 254 0) = false ∧
      s1.basis (L.dialogPool.getD 255 0) = false :=
    ⟨fun q hq => s1p q (List.mem_of_mem_take hq) (hdisj q hq),
      s1p _ (pget 253 (by decide)) (hextx _ (by simp)).1,
      s1p _ (pget 254 (by decide)) (hextx _ (by simp)).1,
      s1p _ (pget 255 (by decide)) (hextx _ (by simp)).1⟩
  have G := glue hc b R
  have hmb : matchBit (triOf (.some hc)) L.point.x s1.basis =
      (triOf (.some hc)).idx.all (fun i => (codeX R).testBit i ==
        (triOf (.some hc)).tgt i ((codeX R).testBit (triOf (.some hc)).r1,
          (codeX R).testBit (triOf (.some hc)).r2)) := by
    unfold matchBit
    rw [xbit _ pv.1, xbit _ pv.2.1, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    apply forall₂_congr
    intro i hi
    rw [xbit i (ix.2.2.2.2 i hi)]
  have hf' : s1.basis L.point.finite = !(matchBit (triOf (.some hc)) L.point.x s1.basis &&
      decide ((s1.basis (L.point.x.getD (triOf (.some hc)).r1 0),
        s1.basis (L.point.x.getD (triOf (.some hc)).r2 0)) = (triOf (.some hc)).pat (triOf (.some hc)).S)) := by
    rw [s1f, hmb, xbit _ pv.1, xbit _ pv.2.1]
    exact G.1
  have CR := classifier_run (triOf (.some hc)) v (yBit (dialogExceptionPoint (.some hc))) L.point.x
    (L.dialogPool.take 253) (yLow L) L.control L.point.finite L.genericSelect
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0)
    hxn hxl hwl hwn hdisj hext hextx s1 (List.drop (measurementCount (FiniteFlagInterval.zrep L)) m) hz hf'
  rw [CR]
  refine ⟨Z.1, ?_, ?_, ?_, ?_⟩
  · rw [← hX]
    apply regValue_congr
    intro q hq
    dsimp only
    rw [tailEff_apply _ _ _ _ _ _ _ _ fg]
    have hqg : q ≠ L.genericSelect := fun e => gx (e ▸ hq)
    have hqf : q ≠ L.point.finite := fun e => fx (e ▸ hq)
    simp [hqg, hqf]
  · show tailEff _ _ _ _ _ _ _ _ _ s1.basis L.point.finite = false
    rw [tailEff_apply _ _ _ _ _ _ _ _ fg]
    simp [fg]
  · show tailEff _ _ _ _ _ _ _ _ _ s1.basis L.genericSelect = _
    rw [tailEff_apply _ _ _ _ _ _ _ _ fg, if_pos rfl, s1g, xbit _ pv.1, xbit _ pv.2.1, s1y, s1c, s1f, hmb,
      Bool.false_xor]
    exact G.2
  · intro q hx hf hg
    show tailEff _ _ _ _ _ _ _ _ _ s1.basis q = _
    rw [tailEff_apply _ _ _ _ _ _ _ _ fg]
    simp only [hg, hf, if_false]
    exact Z.2.1 q hx

/-- The record's input classification and flag merge leave only the generic select set. -/
theorem equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C = decide (R = C) := by
  simp only [pointEqual, pointCode_injective.eq_iff]

open Classical in
theorem oldPrefix_triple (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointDialogBoundary L R b (fun _ => false))
      (inputClass L (.some hc) cy ++ FusedFlags.prefixProgram L (.some hc))
      (PointDialogBoundary L R b
        (dialogFlagState L false false (dialogOrdinary b R (.some hc)) false false false false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : exceptionBit C = decide (dialogExceptionEnabled C) := by
    simp [exceptionBit,equal_simp,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simp]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,equal_simp]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simp]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,equal_simp]
  have hfin (P : Point) : (b && pointFinite P) = (b ^^ (b && pointEqual P 0)) := by
    rw [pointEqual_zero]; cases b <;> cases pointFinite P <;> rfl
  have hGv : ((((false ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H) = G := by
    rw [hfin, hO]; simp only [G, dialogOrdinary, O, D, I, H, Bool.false_xor]
  have hgen := (dialogOrdinary_true b R C hC)
  have covered : G=true → b=true ∧ pointFinite R=true := by
    intro hg
    obtain ⟨hb,h0,-⟩ := hgen.mp hg
    refine ⟨hb,?_⟩
    cases R with
    | zero => exact False.elim (h0 rfl)
    | some hr => rfl
  have hG1 : (((I ^^ (b && pointFinite R)) ^^ D) ^^ H) = G := by
    rw [← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have h3 := inputClass_flag L hw hn R C cy b false false false false false false false
  rw [hD,hI,hH,Bool.false_xor,Bool.false_xor,Bool.false_xor] at h3
  have h6 := genFlagN_flag L hn R b false D I false false H false
  rw [hG1] at h6
  have hHx : H = true → b = true ∧ D = false := by
    intro h
    dsimp only [H, D, dialogException, dialogDouble] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hb, _, hne, _⟩, hR⟩ := h
    refine ⟨hb, ?_⟩
    simp [hR, hne]
  have hDx : D = true → b = true := by
    intro h
    dsimp only [D, dialogDouble] at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have cls := DHClass.classify hc b R
  dsimp only at cls
  have hKC : decide (cy≠-cy) = decide (C≠-C) := by
    apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact doubling_enabled_iff hc
  have clrD : false = (D ^^ (decide (cy≠-cy) && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R == yBit C))) := by
    rw [hKC]; simp only [D, G, C]; rw [← cls.1, Bool.xor_self]
  have clrH : false = (H ^^ (exceptionBit C && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) != DHClass.cxk C))) := by
    rw [hE]; simp only [H, G, C]; rw [← cls.2, Bool.xor_self]
  have hf1 := clrDH_flag L hw hn C cy R b D G H false false clrD clrH

  have hf1' := FusedFlags.boundary_step L hw hn hc true R b D G H false false covered
    (fun _ => ⟨rfl, rfl⟩) (by simp) hf1
  have h0 : dialogFlagState L false false false false false false false = (fun _ => false) := by
    funext q; simp [dialogFlagState, writeBit, Function.update]
  have trip := Triple.seq h3 (Triple.seq h6 hf1')
  rw [h0] at trip
  intro s m hs
  have e := FusedFlags.same_context (genFlagN L ++ FusedFlags.adapterProgram L (.some hc) true)
    (FusedFlags.prefixProgram L (.some hc)) (inputClass L (.some hc) cy) []
    (FusedFlags.prefix_measurements L (.some hc)) (FusedFlags.prefix_run L hw hn (.some hc)) s m
  simp only [List.append_nil] at e
  rw [← e]
  have t := trip s m hs
  simpa only [List.append_assoc] using t

theorem poolWire_mem (L : ControlledPointLayout) (hw : L.Widths) (i : Nat) (hi : i < 2613) :
    L.core.poolWire i ∈ L.dialogPool := by
  have hpl := dialogPool_length L hw
  have hcore : 2613 ≤ L.core.pool.length := by
    have := hpl; simp only [ControlledPointLayout.dialogPool, List.length_take] at this; omega
  simp only [PointAddLayout.poolWire, ControlledPointLayout.dialogPool]
  rw [List.getD_eq_getElem _ _ (by omega)]
  apply List.mem_iff_getElem.mpr
  refine ⟨i, by simp only [List.length_take]; omega, ?_⟩
  simp [List.getElem_take]

theorem yLow_mem (L : ControlledPointLayout) (hw : L.Widths) : yLow L ∈ L.point.y := by
  have hyl : L.point.y.length = 256 := hw.inputY
  unfold yLow
  cases hy : L.point.y with
  | nil => rw [hy] at hyl; simp at hyl
  | cons a l => simp

theorem sitesN_used (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q ∈ sitesN L, q ∈ L.dialogUsedWires := by
  have hpl := dialogPool_length L hw
  have hcore : 2613 ≤ L.core.pool.length := by
    have := hpl; simp only [ControlledPointLayout.dialogPool, List.length_take] at this; omega
  have pool (i : Nat) (hi : i < 2613) : L.core.poolWire i ∈ L.dialogPool := by
    simp only [PointAddLayout.poolWire, ControlledPointLayout.dialogPool]
    rw [List.getD_eq_getElem _ _ (by omega)]
    apply List.mem_iff_getElem.mpr
    refine ⟨i, by simp only [List.length_take]; omega, ?_⟩
    simp [List.getElem_take]
  intro q hq
  simp only [sitesN, List.mem_append, List.mem_singleton] at hq
  simp only [ControlledPointLayout.dialogUsedWires, List.mem_append, List.mem_singleton]
  rcases hq with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · left; right
    simp only [flagsN, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [ControlledPointLayout.inPlaceFlags, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · right
    simp only [sharedPoolF, wireBlock, List.mem_append, List.mem_map, List.mem_range'_1] at h
    rcases h with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩ <;> exact pool i (by omega)

/-- The record's input stage in its un-relabelled form. -/
def oldStage (L : ControlledPointLayout) (C : Point) (cy : Fp) : Program :=
  inputClass L C cy ++ FusedFlags.prefixProgram L C ++ FiniteFlagInterval.zrep L ++
    CodexYParityProbe.clearF L

theorem dialogFlagState_other (L : ControlledPointLayout) (G : Bool) (q : Wire) (hq : q ≠ L.genericSelect) :
    dialogFlagState L false false G false false false false q = false := by
  simp only [dialogFlagState, writeBit, Function.update]
  split_ifs <;> simp_all

open Classical in
theorem oldStage_mid (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary L R b (fun _ => false) s.basis) :
    Mid L R (dialogOrdinary b R (.some hc)) s (run (oldStage L (.some hc) cy) m s) := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, hext, hextx⟩ := stage_layout L hw hn
  have hD := L.dialogUsed_nodup hn
  have hpl := dialogPool_length L hw
  have used_mem : ∀ q, q ∈ L.dialogUsedWires ↔ q ∈ PointAddLayout.pointWires L.point ∨ q = L.control ∨
      q ∈ L.inPlaceFlags ∨ q ∈ L.dialogPool := by
    intro q; simp only [ControlledPointLayout.dialogUsedWires, List.mem_append, List.mem_singleton]; tauto
  -- support of the record prefix
  have supp : ∀ q, q ∉ L.dialogUsedWires →
      q ∉ wires (inputClass L (.some hc) cy ++ FusedFlags.prefixProgram L (.some hc)) := by
    intro q hq hm
    rw [wires_append, Finset.mem_union] at hm
    rcases hm with h | h
    · have h1 := List.mem_toFinset.mp (inputClass_wires L hw (.some hc) cy h)
      apply hq
      have yl := yLow_mem L hw
      have p514 := poolWire_mem L hw 514 (by decide)
      simp only [List.mem_cons, List.mem_append] at h1
      simp only [ControlledPointLayout.dialogUsedWires, PointAddLayout.pointWires, List.mem_append,
        List.mem_cons, List.mem_singleton, ControlledPointLayout.inPlaceFlags, List.not_mem_nil, or_false]
      rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | h1 | h1
      · tauto
      · tauto
      · tauto
      · tauto
      · tauto
      · tauto
      · have : q ∈ L.point.x := h1
        tauto
      · have : q ∈ L.dialogPool := List.mem_of_mem_take h1
        tauto
    · have h2 := (FusedFlags.part_support L hc).1 h
      rw [wires_append, Finset.mem_union] at h2
      rcases h2 with h3 | h3
      · exact hq (sitesN_used L hw q (List.mem_toFinset.mp (genFlagN_support L h3)))
      · exact hq (sitesN_used L hw q (List.mem_toFinset.mp (clrDH_sitesN L hw _ _ h3)))
  have hp := (point_holds _ _ _).mp hs.point
  -- step 1: the record prefix
  have T := oldPrefix_triple L hw hn R hc b s m hs
  unfold oldStage
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (inputClass L (.some hc) cy ++ FusedFlags.prefixProgram L (.some hc)) m s = t1 at T supp ⊢
  have hp1 := (point_holds _ _ _).mp T.2.point
  have t1out : ∀ q, q ∉ L.dialogUsedWires → t1.basis q = s.basis q := by
    intro q hq; rw [← ht1]; exact run_preserves_outside _ m s q (supp q hq)
  have fx : L.point.finite ∉ L.point.x := (hextx _ (by simp)).1
  have gx : L.genericSelect ∉ L.point.x := (hextx _ (by simp)).1
  have fg : L.point.finite ≠ L.genericSelect := by intro e; rw [e] at hext; simp at hext
  -- step 2: the sentinel coding
  have Z := FiniteFlagInterval.zrep_run L hw hn t1 (List.drop (measurementCount
    (inputClass L (.some hc) cy ++ FusedFlags.prefixProgram L (.some hc))) m)
  generalize ht2 : run (FiniteFlagInterval.zrep L) (List.drop (measurementCount
    (inputClass L (.some hc) cy ++ FusedFlags.prefixProgram L (.some hc))) m) t1 = t2 at Z ⊢
  have hX : regValue L.point.x t2.basis = codeX R := by
    rw [Z.2.2, hp1.2.1, hp1.1]
    unfold codeX
    cases hf : pointFinite R
    · have hx0 : pointX R = 0 := by
        cases R with
        | zero => rfl
        | some h => simp [pointFinite] at hf
      simp [hx0]
    · simp
  have t2f : t2.basis L.point.finite = pointFinite R := (Z.2.1 _ fx).trans hp1.1
  -- step 3: the finite-flag clear
  have hz : regValue (CodexYParityProbe.work L) t2.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have hq' : q ∈ L.dialogPool.take 245 := hq
    have hqx : q ∉ L.point.x := fun h => (stage_layout L hw hn).2.2.2.2.1 q
      (List.mem_take_iff_getElem.mpr (by
        obtain ⟨i, hi, e⟩ := List.mem_take_iff_getElem.mp hq'
        exact ⟨i, by omega, e⟩)) h
    rw [Z.2.1 _ hqx]
    exact (regValue_zero _ _).mp T.2.clean q (List.mem_of_mem_take hq')
  have hY : regValue L.point.y t2.basis = pointY R := by
    rw [← hp1.2.2]; apply regValue_congr; intro q hq
    exact Z.2.1 q (y_not_x L hn q hq)
  have fb : (pointFinite R ^^ CodexYParityProbe.finiteBit (codeX R) (pointY R)) = false := by
    unfold codeX
    cases R with
    | zero =>
      have h0 : pointFinite (WeierstrassCurve.Affine.Point.zero : Point) = false := rfl
      have hy0 : pointY (WeierstrassCurve.Affine.Point.zero : Point) = 0 := rfl
      have eq : FiniteFlagInterval.sentinel = p-1 := by norm_num [FiniteFlagInterval.sentinel, p]
      simp [h0, hy0, CodexYParityProbe.finiteBit, eq, CodexYParityMath.sentinel_matches]
    | @some rx ry hr =>
      have h1 : pointFinite (.some hr : Point) = true := rfl
      have hne : CodexYParityProbe.finiteBit rx.val ry.val = true :=
        decide_eq_true (CodexYParityMath.curve_not_matches hr)
      have e : pointX (.some hr : Point) = rx.val := rfl
      have e' : pointY (.some hr : Point) = ry.val := rfl
      simp [h1, e, e', hne]
  have zero : ∀ mm, (run (CodexYParityProbe.clrF L) mm t2).basis L.point.finite = false := by
    intro mm
    rw [CodexYParityProbe.clrF_run L hw hn _ _ hz, hX, hY, t2f]
    simp only [writeBit, Function.update_self]
    exact fb
  rw [CodexYParityProbe.clearF_eq L hw hn _ _ hz (zero _), CodexYParityProbe.clrF_run L hw hn _ _ hz]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show t2.phase = s.phase
    rw [Z.1]; exact T.1
  · show regValue L.point.x (writeBit t2.basis L.point.finite _) = codeX R
    rw [← hX]; apply regValue_congr; intro q hq
    have hqf : q ≠ L.point.finite := fun e => fx (e ▸ hq)
    simp [writeBit, Function.update, hqf]
  · show writeBit t2.basis L.point.finite _ L.point.finite = false
    simp only [writeBit, Function.update_self]
    rw [hX, hY, t2f]; exact fb
  · show writeBit t2.basis L.point.finite _ L.genericSelect = _
    simp only [writeBit, Function.update_of_ne (Ne.symm fg)]
    rw [Z.2.1 _ gx, T.2.flags _ (by simp [ControlledPointLayout.inPlaceFlags])]
    exact (dialogFlagState_read L hn false false (dialogOrdinary b R (.some hc)) false false false false).2.2.1
  · intro q hx hf hg
    show writeBit t2.basis L.point.finite _ q = s.basis q
    simp only [writeBit, Function.update_of_ne hf]
    rw [Z.2.1 _ hx]
    by_cases hu : q ∈ L.dialogUsedWires
    · rw [used_mem] at hu
      rcases hu with hu | hu | hu | hu
      · simp only [PointAddLayout.pointWires, List.mem_cons, List.mem_append] at hu
        rcases hu with (hu | hu) | hu
        · exact absurd hu hf
        · exact absurd hu hx
        · exact (regValue_eq_iff _ _ _).mp (hp1.2.2.trans hp.2.2.symm) q hu
      · subst hu; exact T.2.control.trans hs.control.symm
      · rw [T.2.flags q hu, hs.flags q hu, dialogFlagState_other L _ q hg]
      · exact (regValue_eq_iff _ _ _).mp (T.2.clean.trans hs.clean.symm) q hu
    · exact t1out q hu

open Classical in
/-- The merged stage and the record stage agree on every dialog boundary state, whatever the
measurement records. -/
theorem stage_run_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m m' : List Bool) (hs : PointDialogBoundary L R b (fun _ => false) s.basis) :
    run (stage L (.some hc)) m' s = run (oldStage L (.some hc) cy) m s :=
  Mid.unique (stage_mid L hw hn hc b R s m' hs) (oldStage_mid L hw hn hc b R s m hs)

end Stage


end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinelAux
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- A wire of one instruction of a program is a wire of the program. -/
theorem mem_wires_of_instr {P : Program} {i : Instr} {q : Wire} (hi : i ∈ P) (hq : q ∈ i.wires) :
    q ∈ wires P := by
  induction P with
  | nil => cases hi
  | cons j P ih =>
    simp only [wires, Finset.mem_union]
    rcases List.mem_cons.mp hi with rfl | h
    · exact Or.inl hq
    · exact Or.inr (ih h)

theorem chainAnd_target (c a t : Wire) : t ∈ wires (chainAnd c a t) :=
  mem_wires_of_instr (i := .CCX c a t) (by simp [chainAnd]) (by simp [Instr.wires])

/-- Every work wire of a zero chain is written by the chain. -/
theorem zeroWith_work_mem (T : Wire → Program) (c : Wire) (bs : List ZeroBit) :
    ∀ b ∈ bs, b.work ∈ wires (zeroWith T c bs) := by
  induction bs generalizing c with
  | nil => intro b hb; cases hb
  | cons b bs ih =>
    intro b' hb'
    simp only [zeroWith, wires_append, Finset.mem_union]
    rcases List.mem_cons.mp hb' with rfl | h
    · exact Or.inl (Or.inl (chainAnd_target _ _ _))
    · exact Or.inl (Or.inr (ih b.work b' h))

/-- A wire the innermost step always touches is a wire of the zero chain. -/
theorem zeroWith_tail_mem (T : Wire → Program) (w : Wire) (hT : ∀ h, w ∈ wires (T h)) (c : Wire)
    (bs : List ZeroBit) : w ∈ wires (zeroWith T c bs) := by
  induction bs generalizing c with
  | nil => simpa [zeroWith] using hT c
  | cons b bs ih =>
    simp only [zeroWith, wires_append, Finset.mem_union]
    exact Or.inl (Or.inr (ih b.work))

theorem affineClassTail_wa_mem (r y t₁ t₂ t₃ wa wb : Wire) (e₁ a₁ e₂ a₂ a₃ : Bool) (h : Wire) :
    wa ∈ wires (affineClassTail r y t₁ t₂ t₃ wa wb e₁ a₁ e₂ a₂ a₃ h) := by
  simp only [affineClassTail, wires_append, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (chainAnd_target _ _ _)))))

/-- Every port's work wire is written by the affine input classifier. -/
theorem affineInputWith_work_mem (y t₁ t₂ t₃ wb : Wire) (e₁ a₁ e₂ a₂ a₃ : Bool) :
    ∀ (bs : List ZeroBit) (c : Wire) (a b : Nat), ∀ p ∈ bs,
      p.work ∈ wires (affineInputWith y t₁ t₂ t₃ wb e₁ a₁ e₂ a₂ a₃ c bs a b) := by
  intro bs
  induction bs with
  | nil => intro c a b p hp; cases hp
  | cons q qs ih =>
    intro c a b p hp
    simp only [affineInputWith, wires_append, Finset.mem_union]
    left; right
    split_ifs with hab
    · simp only [wires_append, Finset.mem_union]
      rcases List.mem_cons.mp hp with rfl | h
      · exact Or.inl (Or.inl (chainAnd_target _ _ _))
      · exact Or.inl (Or.inr (ih q.work (a/2) (b/2) p h))
    · simp only [affineInputSuffix, wires_append, Finset.mem_union]
      left; right
      rcases List.mem_cons.mp hp with rfl | h
      · exact zeroWith_tail_mem _ _ (fun h => affineClassTail_wa_mem _ _ _ _ _ _ _ _ _ _ _ _ h) _ _
      · exact zeroWith_work_mem _ _ _ p h

theorem inputClass_pool_mem (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cy : Fp) :
    ∀ q ∈ L.dialogPool.take 256, q ∈ wires (inputClass L C cy) := by
  intro q hq
  have hmap := (pairPorts_maps L hw).2
  rw [← hmap] at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  unfold inputClass
  split_ifs
  · exact affineInputWith_work_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp
  · simp only [pairEqual, wires_append, Finset.mem_union]
    exact Or.inl (Or.inr (zeroWith_work_mem _ _ _ p hp))

theorem prefix_generic_mem (L : ControlledPointLayout) (C : Point) :
    L.genericSelect ∈ wires (FusedFlags.prefixProgram L C) := by
  unfold FusedFlags.prefixProgram
  rw [renameProgram_support]
  refine Finset.mem_image.mpr ⟨5, ?_, ?_⟩
  · simp only [FusedFlags.clearPrefix, List.cons_append, wires, Finset.mem_union]
    exact Or.inl (by simp [Instr.wires])
  · rfl

theorem inputClass_counts_ge (L : ControlledPointLayout) (hw : L.Widths) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    258 ≤ toffoliCount (inputClass L (.some hc) cy) ∧
      measurementCount (inputClass L (.some hc) cy) = 256 := by
  have tc : tailCost (decide (cy≠-cy)) (yBit (.some hc)) true (yBit (-(.some hc : Point))) = 1 := by
    rw [cy_ne_neg hc,yBit_neg hc]
    cases yBit (.some hc) <;> decide
  unfold inputClass
  split_ifs with enabled
  · have hh := affineInputWith_counts (yLow L) L.doubleSelect L.genericSelect L.core.equalNegY
      (L.core.poolWire 514) (decide (cy≠-cy)) (yBit (.some hc)) true (yBit (-(.some hc : Point)))
      (yBit (dialogExceptionPoint (.some hc))) L.control (pairPorts L) (pairCode (.some hc))
      (pairCode (dialogExceptionPoint (.some hc)))
    rw [pairPorts_length L hw,tc] at hh
    omega
  · exact False.elim (enabled (NoThreeTorsion.enabled hc))


end ECDSAAdd.Entrant.InputSentinelAux

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section ClassifierFacts
open Challenge
/-! ### Static facts of the merged classifier: wire support, physical gates, counts and slots -/

/-- Bool form of `PhysicalInstr` on gates (the record's `ProperGate`; measurements admitted). -/
def physB : Instr → Bool
  | .X _ => true
  | .CX c t => decide (c ≠ t)
  | .CCX a b t => decide (a ≠ t ∧ b ≠ t)
  | .measureX _ _ _ => true

theorem gatePhysical_of_all (p : Program) (h : p.all physB = true) : GatePhysical p := by
  intro i hi
  have hb := List.all_eq_true.mp h i hi
  cases i <;> simp_all [physB, RecordedQuantum.PhysicalInstr, ProperGate]

theorem decode_physical (a1 a2 b2 yb : Bool) :
    GatePhysical (decode1 a1 a2 b2 yb) ∧ GatePhysical (decode2 a1 a2 b2 yb) := by
  constructor <;> apply gatePhysical_of_all <;>
    cases a1 <;> cases a2 <;> cases b2 <;> cases yb <;> decide

theorem decodeT_physical (tr : Tri) (yb : Bool) : GatePhysical (decodeT tr yb) := by
  unfold decodeT
  split_ifs
  · exact (decode_physical _ _ _ _).1
  · exact (decode_physical _ _ _ _).2

theorem decode_slots (a1 a2 b2 yb : Bool) :
    gateSlots (decode1 a1 a2 b2 yb) ≤ 35 ∧ gateSlots (decode2 a1 a2 b2 yb) ≤ 35 := by
  cases a1 <;> cases a2 <;> cases b2 <;> cases yb <;> decide

theorem decodeT_slots (tr : Tri) (yb : Bool) : gateSlots (decodeT tr yb) ≤ 35 := by
  unfold decodeT
  split_ifs
  · exact (decode_slots _ _ _ _).1
  · exact (decode_slots _ _ _ _).2

theorem tail_support (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t h : Wire) :
    wires (tail tr yb xr1 xr2 y0 c f g g1 wB t h) ⊆ {h, xr1, xr2, y0, c, f, g, g1, wB, t} := by
  unfold tail
  rw [renameProgram_support]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  have ha10 : a < 10 := Finset.mem_range.mp (decodeT_support tr yb ha)
  simp only [LocalWireModel.label, dif_pos ha10]
  interval_cases a <;> simp

theorem tail_physical (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t h : Wire)
    (hnd : [h, xr1, xr2, y0, c, f, g, g1, wB, t].Nodup) :
    GatePhysical (tail tr yb xr1 xr2 y0 c f g g1 wB t h) := by
  have inj := LocalWireModel.listPorts_injective [h, xr1, xr2, y0, c, f, g, g1, wB, t] hnd
    (n := 10) (by simp)
  unfold tail
  exact gatePhysical_rename_support _ _ (fun a ha b hb e =>
    LocalWireModel.label_injective _ inj a (decodeT_support tr yb ha) b (decodeT_support tr yb hb) e)
    (decodeT_physical tr yb)

theorem tail_counts (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t h : Wire) :
    toffoliCount (tail tr yb xr1 xr2 y0 c f g g1 wB t h) = 4 ∧
    measurementCount (tail tr yb xr1 xr2 y0 c f g g1 wB t h) = 4 := by
  unfold tail
  rw [(renameProgram_counts _ _).1, (renameProgram_counts _ _).2]
  unfold decodeT
  split_ifs
  · exact ⟨(decode_counts _ _ _ _).1, (decode_counts _ _ _ _).2.1⟩
  · exact ⟨(decode_counts _ _ _ _).2.2.1, (decode_counts _ _ _ _).2.2.2⟩

theorem tail_slots (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t h : Wire) :
    gateSlots (tail tr yb xr1 xr2 y0 c f g g1 wB t h) = gateSlots (decodeT tr yb) := by
  unfold tail
  exact rename_gateSlots _ _

theorem zeroPorts_mem : ∀ (xs ws : List Wire) (b : ZeroBit), b ∈ zeroPorts xs ws →
    b.input ∈ xs ∧ b.work ∈ ws
  | x :: xs, w :: ws, b, hb => by
    simp only [zeroPorts, List.mem_cons] at hb
    rcases hb with rfl | hb
    · simp
    · have h := zeroPorts_mem xs ws b hb
      exact ⟨List.mem_cons_of_mem _ h.1, List.mem_cons_of_mem _ h.2⟩
  | [], _, b, hb => by simp [zeroPorts] at hb
  | _ :: _, [], b, hb => by simp [zeroPorts] at hb

theorem gateSlots_app (p q : Program) : gateSlots (p ++ q) = gateSlots p + gateSlots q := by
  simp [gateSlots, List.map_append, List.sum_append]

theorem remapBit_sub (tr : Tri) (xr1 xr2 w : Wire) (i : Nat) (U : Finset Wire)
    (h1 : xr1 ∈ U) (h2 : xr2 ∈ U) (hw : w ∈ U) : wires (tr.remapBit xr1 xr2 w i) ⊆ U := by
  unfold Tri.remapBit
  split_ifs <;> simp [wires, Instr.wires, Finset.insert_subset_iff, h1, h2, hw]

theorem remapList_sub (tr : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) (U : Finset Wire)
    (h1 : xr1 ∈ U) (h2 : xr2 ∈ U) (hw : ∀ i ∈ l, w i ∈ U) :
    wires (tr.remapList xr1 xr2 w l) ⊆ U := by
  induction l with
  | nil => simp [Tri.remapList, wires]
  | cons i l ih =>
    simp only [Tri.remapList, List.flatMap_cons, wires_append] at ih ⊢
    exact Finset.union_subset (remapBit_sub tr xr1 xr2 (w i) i U h1 h2 (hw i (by simp)))
      (ih (fun j hj => hw j (by simp [hj])))

theorem remapBit_physical (tr : Tri) (xr1 xr2 w : Wire) (i : Nat) (h1 : xr1 ≠ w) (h2 : xr2 ≠ w) :
    GatePhysical (tr.remapBit xr1 xr2 w i) := by
  unfold Tri.remapBit
  split_ifs <;> simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, h1, h2]

theorem remapList_physical (tr : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat)
    (h : ∀ i ∈ l, xr1 ≠ w i ∧ xr2 ≠ w i) : GatePhysical (tr.remapList xr1 xr2 w l) := by
  induction l with
  | nil => simp [Tri.remapList, GatePhysical]
  | cons i l ih =>
    simp only [Tri.remapList, List.flatMap_cons, gatePhysical_append] at ih ⊢
    exact ⟨remapBit_physical tr xr1 xr2 (w i) i (h i (by simp)).1 (h i (by simp)).2,
      ih (fun j hj => h j (by simp [hj]))⟩

theorem remapList_tc (tr : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) :
    toffoliCount (tr.remapList xr1 xr2 w l) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [Tri.remapList, List.flatMap_cons, toffoliCount_append] at ih ⊢
    rw [ih]
    simp only [Tri.remapBit, toffoliCount_append]
    split_ifs <;> rfl

theorem remapBit_slots (tr : Tri) (xr1 xr2 w : Wire) (i : Nat) :
    gateSlots (tr.remapBit xr1 xr2 w i) ≤ 3 := by
  unfold Tri.remapBit
  split_ifs <;> simp [gateSlots, instructionSlots]

theorem remapList_slots (tr : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) :
    gateSlots (tr.remapList xr1 xr2 w l) ≤ 3 * l.length := by
  induction l with
  | nil => simp [Tri.remapList, gateSlots]
  | cons i l ih =>
    simp only [Tri.remapList, List.flatMap_cons, gateSlots_app, List.length_cons] at ih ⊢
    have := remapBit_slots tr xr1 xr2 (w i) i
    omega

/-- A zero chain stays inside any wire set that holds its control, ports and every innermost step. -/
theorem zeroWith_sub (T : Wire → Program) (U : Finset Wire) (hT : ∀ h ∈ U, wires (T h) ⊆ U) :
    ∀ (c : Wire) (bs : List ZeroBit), c ∈ U → (∀ b ∈ bs, b.input ∈ U ∧ b.work ∈ U) →
      wires (zeroWith T c bs) ⊆ U := by
  intro c bs
  induction bs generalizing c with
  | nil => intro hc _; simpa [zeroWith] using hT c hc
  | cons b bs ih =>
    intro hc hb
    have hb0 := hb b (by simp)
    simp only [zeroWith, wires_append]
    refine Finset.union_subset (Finset.union_subset ?_ (ih b.work hb0.2 (fun b' h => hb b' (by simp [h])))) ?_
    · simp [chainAnd, wires, Instr.wires, Finset.insert_subset_iff, hc, hb0.1, hb0.2]
    · simp [chainErase, wires, Instr.wires, correctionWires, Finset.insert_subset_iff, hc, hb0.1, hb0.2]

/-- A zero chain is physical when its chain wires are distinct, each input differs from its work
wire, and every innermost step it can reach is physical. -/
theorem zeroWith_physical (T : Wire → Program) :
    ∀ (c : Wire) (bs : List ZeroBit), (c :: bs.map ZeroBit.work).Nodup → (∀ b ∈ bs, b.input ≠ b.work) →
      (∀ h ∈ c :: bs.map ZeroBit.work, GatePhysical (T h)) → GatePhysical (zeroWith T c bs) := by
  intro c bs
  induction bs generalizing c with
  | nil => intro _ _ hT; simpa [zeroWith] using hT c (by simp)
  | cons b bs ih =>
    intro hn hio hT
    simp only [List.map_cons] at hn hT
    have hcw : c ≠ b.work := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
    have hn' : (b.work :: bs.map ZeroBit.work).Nodup := (List.nodup_cons.mp hn).2
    have hiw := hio b (by simp)
    simp only [zeroWith, gatePhysical_append]
    refine ⟨⟨?_, ih b.work hn' (fun b' h => hio b' (by simp [h]))
      (fun h hh => hT h (List.mem_cons_of_mem _ hh))⟩, ?_⟩
    · simp [chainAnd, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hcw, hiw]
    · simp [chainErase, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]

theorem zeroWith_slots (T : Wire → Program) (n : Nat) (hT : ∀ h, gateSlots (T h) = n) :
    ∀ (c : Wire) (bs : List ZeroBit), gateSlots (zeroWith T c bs) = 7 * bs.length + n := by
  intro c bs
  induction bs generalizing c with
  | nil => simp [zeroWith, hT]
  | cons b bs ih =>
    simp only [zeroWith, gateSlots_app, ih, List.length_cons]
    simp [chainAnd, chainErase, gateSlots, instructionSlots]
    omega

/-- The classifier's index list starts with a non-pivot bit and has 253 more. -/
theorem idx_split (tr : Tri) (v : tr.Valid) : ∃ i0 it, tr.idx = i0 :: it ∧ it.length = 253 := by
  have hl := (Tri.idx_facts v).2.1
  cases h : tr.idx with
  | nil => rw [h] at hl; simp at hl
  | cons a l => rw [h] at hl; exact ⟨a, l, rfl, by simpa using hl⟩

theorem classifier_support (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t : Wire) (hxl : xs.length = 256) (_hwl : work.length = 253) :
    wires (classifier tr yb xs work y0 c f g g1 wB t) ⊆
      xs.toFinset ∪ work.toFinset ∪ {y0, c, f, g, g1, wB, t} := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  let U : Finset Wire := xs.toFinset ∪ work.toFinset ∪ {y0, c, f, g, g1, wB, t}
  have xsU : ∀ i, i < 256 → xs.getD i 0 ∈ U := by
    intro i hi
    have hm : xs.getD i 0 ∈ xs := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    simp only [U, Finset.mem_union, List.mem_toFinset]
    exact Or.inl (Or.inl hm)
  have workU : ∀ q ∈ work, q ∈ U := fun q hq => by simp [U, hq]
  have r1U := xsU _ pv.1
  have r2U := xsU _ pv.2.1
  have idxU : ∀ i ∈ tr.idx, xs.getD i 0 ∈ U := fun i hi => xsU i (ix.2.2.2.2 i hi)
  have PU : ∀ q ∈ tr.idx.map (fun i => xs.getD i 0), q ∈ U := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; exact idxU i hi
  have h0U : (tr.idx.map (fun i => xs.getD i 0)).headD 0 ∈ U := by
    rw [hidx]; exact idxU i0 (by rw [hidx]; simp)
  have portsU : ∀ b ∈ zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work,
      b.input ∈ U ∧ b.work ∈ U := by
    intro b hb
    have hm := zeroPorts_mem _ _ b hb
    exact ⟨PU _ (List.mem_of_mem_tail hm.1), workU _ hm.2⟩
  have extU : ∀ q ∈ ({y0, c, f, g, g1, wB, t} : Finset Wire), q ∈ U := by
    intro q hq; simp only [U, Finset.mem_union]; exact Or.inr hq
  have tailU : ∀ h ∈ U,
      wires (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h) ⊆ U := by
    intro h hh
    refine (tail_support tr yb _ _ y0 c f g g1 wB t h).trans ?_
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hh, r1U, r2U, extU y0 (by simp), extU c (by simp), extU f (by simp), extU g (by simp),
      extU g1 (by simp), extU wB (by simp), extU t (by simp)⟩
  have remapU := remapList_sub tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx U
    r1U r2U idxU
  have zU := zeroWith_sub _ U tailU _ _ h0U portsU
  have xU : wires [Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ⊆ U := by
    generalize (tr.idx.map (fun i => xs.getD i 0)).headD 0 = h0 at h0U ⊢
    intro q hq
    simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_singleton] at hq
    rcases hq with rfl | hq
    · exact h0U
    · simp at hq
  intro q hq
  simp only [classifier, wires_append, Finset.mem_union] at hq
  rcases hq with h | h | h | h | h
  · exact remapU h
  · exact xU h
  · exact zU h
  · exact xU h
  · exact remapU h

theorem classifier_physical (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t : Wire) (hxl : xs.length = 256) (hwl : work.length = 253)
    (hxn : xs.Nodup) (hwn : work.Nodup) (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, g1, wB, t].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ xs ∧ q ∉ work) :
    GatePhysical (classifier tr yb xs work y0 c f g g1 wB t) := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have winj : ∀ i j, i < 256 → j < 256 → xs.getD i 0 = xs.getD j 0 → i = j := by
    intro i j hi hj e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    exact hxn.getElem_inj_iff.mp e
  have wmem : ∀ i, i < 256 → xs.getD i 0 ∈ xs := by
    intro i hi; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hi0 : i0 ∈ tr.idx := by rw [hidx]; simp
  have i0lt := ix.2.2.2.2 i0 hi0
  have i0r1 : i0 ≠ tr.r1 := fun e => ix.2.2.1 (e ▸ hi0)
  have i0r2 : i0 ≠ tr.r2 := fun e => ix.2.2.2.1 (e ▸ hi0)
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  -- the remap's CX controls are the pivot wires, never a remapped wire
  have remapP : GatePhysical (tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx) := by
    apply remapList_physical
    intro i hi
    have hi256 := ix.2.2.2.2 i hi
    refine ⟨fun e => ix.2.2.1 ((winj _ _ pv.1 hi256 e) ▸ hi), fun e => ix.2.2.2.1 ((winj _ _ pv.2.1 hi256 e) ▸ hi)⟩
  -- the zero chain: control `xs[i0]`, inputs the other non-pivot bits, works the pool wires
  have hP0 : (tr.idx.map (fun i => xs.getD i 0)).headD 0 = xs.getD i0 0 := by rw [hidx]; rfl
  have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by rw [hidx]; rfl
  have x0x : xs.getD i0 0 ∈ xs := wmem i0 i0lt
  have hused : [xs.getD tr.r1 0, xs.getD tr.r2 0, y0, c, f, g, g1, wB, t].Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hext⟩⟩
    · simp only [List.mem_cons, not_or]
      refine ⟨fun e => pv.2.2.1 (winj _ _ pv.1 pv.2.1 e), ?_⟩
      have hx1 := wmem _ pv.1
      refine ⟨fun e => (hextx y0 (by simp)).1 (e ▸ hx1), fun e => (hextx c (by simp)).1 (e ▸ hx1),
        fun e => (hextx f (by simp)).1 (e ▸ hx1), fun e => (hextx g (by simp)).1 (e ▸ hx1),
        fun e => (hextx g1 (by simp)).1 (e ▸ hx1), fun e => (hextx wB (by simp)).1 (e ▸ hx1),
        fun e => (hextx t (by simp)).1 (e ▸ hx1), by simp⟩
    · simp only [List.mem_cons, not_or]
      have hx2 := wmem _ pv.2.1
      exact ⟨fun e => (hextx y0 (by simp)).1 (e ▸ hx2), fun e => (hextx c (by simp)).1 (e ▸ hx2),
        fun e => (hextx f (by simp)).1 (e ▸ hx2), fun e => (hextx g (by simp)).1 (e ▸ hx2),
        fun e => (hextx g1 (by simp)).1 (e ▸ hx2), fun e => (hextx wB (by simp)).1 (e ▸ hx2),
        fun e => (hextx t (by simp)).1 (e ▸ hx2), by simp⟩
  -- any chain wire (the control `xs[i0]` or a pool wire) is off the tail's other nine wires
  have hout : ∀ h, (h = xs.getD i0 0 ∨ h ∈ work) → h ∉ [xs.getD tr.r1 0, xs.getD tr.r2 0, y0, c, f, g, g1, wB, t] := by
    intro h hh hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hh with rfl | hw
    · rcases hm with e | e | e | e | e | e | e | e | e
      · exact i0r1 (winj _ _ i0lt pv.1 e)
      · exact i0r2 (winj _ _ i0lt pv.2.1 e)
      all_goals first
        | exact (hextx y0 (by simp)).1 (e ▸ x0x) | exact (hextx c (by simp)).1 (e ▸ x0x)
        | exact (hextx f (by simp)).1 (e ▸ x0x) | exact (hextx g (by simp)).1 (e ▸ x0x)
        | exact (hextx g1 (by simp)).1 (e ▸ x0x) | exact (hextx wB (by simp)).1 (e ▸ x0x)
        | exact (hextx t (by simp)).1 (e ▸ x0x)
    · rcases hm with e | e | e | e | e | e | e | e | e
      · exact hdisj h hw (e ▸ wmem _ pv.1)
      · exact hdisj h hw (e ▸ wmem _ pv.2.1)
      all_goals first
        | exact (hextx y0 (by simp)).2 (e ▸ hw) | exact (hextx c (by simp)).2 (e ▸ hw)
        | exact (hextx f (by simp)).2 (e ▸ hw) | exact (hextx g (by simp)).2 (e ▸ hw)
        | exact (hextx g1 (by simp)).2 (e ▸ hw) | exact (hextx wB (by simp)).2 (e ▸ hw)
        | exact (hextx t (by simp)).2 (e ▸ hw)
  have zP : GatePhysical (zeroWith (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)) := by
    rw [hP0, hPt]
    apply zeroWith_physical
    · rw [zp.2]
      exact List.nodup_cons.mpr ⟨fun hm => hdisj _ hm x0x, hwn⟩
    · intro b hb e
      have hm := zeroPorts_mem _ _ b hb
      obtain ⟨i, hi, hie⟩ := List.mem_map.mp hm.1
      have hit : i ∈ tr.idx := by rw [hidx]; simp [hi]
      exact hdisj _ hm.2 (e ▸ hie ▸ wmem i (ix.2.2.2.2 i hit))
    · intro h hh
      rw [zp.2] at hh
      apply tail_physical
      exact List.nodup_cons.mpr ⟨hout h (by simpa using hh), hused⟩
  have xP : GatePhysical [Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] := by
    simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]
  unfold classifier
  simp only [gatePhysical_append]
  exact ⟨remapP, xP, zP, xP, remapP⟩

theorem classifier_counts (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t : Wire) (hwl : work.length = 253) :
    toffoliCount (classifier tr yb xs work y0 c f g g1 wB t) = 257 ∧
    measurementCount (classifier tr yb xs work y0 c f g g1 wB t) = 257 ∧
    gateSlots (classifier tr yb xs work y0 c f g g1 wB t) ≤ 4000 := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have ix := Tri.idx_facts v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have zc := zeroWith_counts_general (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t) 4 4
    (fun h => tail_counts tr yb _ _ y0 c f g g1 wB t h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zc
  have zs := zeroWith_slots (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t)
    (gateSlots (decodeT tr yb)) (fun h => tail_slots tr yb _ _ y0 c f g g1 wB t h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zs
  have rs := remapList_slots tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  rw [ix.2.1] at rs
  have ds := decodeT_slots tr yb
  have rt := remapList_tc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  have rm := remapList_mc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  unfold classifier
  simp only [toffoliCount_append, measurementCount_append, gateSlots_app, rt, rm, zc.1, zc.2, zs]
  refine ⟨by simp [toffoliCount], by simp [measurementCount], ?_⟩
  simp only [gateSlots, instructionSlots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at rs ds ⊢
  omega

/-- The tightest uniform slot bound: 3 slots a remapped bit twice, the two flips, 7 a chain rung,
and the 35-slot worst decode tail. -/
theorem classifier_slots (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t : Wire) (hwl : work.length = 253) :
    gateSlots (classifier tr yb xs work y0 c f g g1 wB t) ≤ 3332 := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have ix := Tri.idx_facts v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have zs := zeroWith_slots (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t)
    (gateSlots (decodeT tr yb)) (fun h => tail_slots tr yb _ _ y0 c f g g1 wB t h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zs
  have rs := remapList_slots tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  rw [ix.2.1] at rs
  have ds := decodeT_slots tr yb
  unfold classifier
  simp only [gateSlots_app, zs]
  simp only [gateSlots, instructionSlots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at rs ds ⊢
  omega


end ClassifierFacts


end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section Splice
open Secp256k1 ControlledPointLayout

/-- The record generic block after its input clear. -/
def tailGen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (swapF L) (CodexYParityProbe.generic L cx cy) ++ CodexYParityProbe.clrF L ++
    FiniteFlagInterval.zrep L

/-- The part of the finite program after the input stage. -/
def shared (L : ControlledPointLayout) (C : Point) (Gen : Program) : Program :=
  renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) Gen)) ++
    FusedFlags.suffixProgram L C ++
  renameProgram (sigP L) (corners2 L C ++ Edges.sharedM L C) ++
  chainErase L.control L.point.finite L.genericSelect

/-- Finite program with the merged input stage. -/
def finiteProgram' (L : ControlledPointLayout) (C : Point) (Gen : Program) : Program :=
  stage L C ++ shared L C Gen

def wrapper' (L : ControlledPointLayout) (C : Point) (Gen : Program) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgram' L C (renameProgram (Wrapper5.U L) Gen))

theorem gen_split (L : ControlledPointLayout) (cx cy : Fp) :
    CodexYParityProbe.gen L cx cy =
      FiniteFlagInterval.zrep L ++ CodexYParityProbe.clearF L ++ tailGen L cx cy := by
  simp only [CodexYParityProbe.gen, CodexYParityProbe.mid, tailGen, List.append_assoc]

/-- Wire numbers of the relabelled sites in the concrete layout. -/
theorem special_wires :
    (layout.core.poolWire 684 : Nat) = 4799 ∧ (layout.core.poolWire 717 : Nat) = 4832 ∧
    (spareD layout : Nat) = 5655 ∧ (layout.core.generic : Nat) = 4113 ∧
    (layout.genericSelect : Nat) = 9814 ∧ (layout.core.equalNegY : Nat) = 4112 ∧
    (layout.doubleSelect : Nat) = 9815 := by
  decide +kernel

/-- The finite flag, both coordinates and the first 255 pool sites avoid the relabelled sites. -/
theorem fix_range : ∀ w ∈ layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255 ++
    layout.point.y), (w : Nat) < 514 ∨ (4115 ≤ (w : Nat) ∧ (w : Nat) < 4370) := by
  decide +kernel

theorem wire_ne {w k : Nat} (r : w < 514 ∨ (4115 ≤ w ∧ w < 4370))
    (hk : (514 ≤ k ∧ k < 4115) ∨ 4370 ≤ k) : w ≠ k := by
  omega

/-- The four relabellings fix the finite flag, both coordinates and the first 255 pool sites. -/
theorem fix_maps : ∀ w ∈ layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255 ++
    layout.point.y), Wrapper5.U layout w = w ∧ tauM layout w = w ∧ swapE layout w = w ∧
      swapD layout w = w := by
  intro w hw
  have r := fix_range w hw
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := special_wires
  have n1 : w ≠ layout.core.poolWire 684 := wire_ne r (by rw [p1]; decide)
  have n2 : w ≠ layout.core.poolWire 717 := wire_ne r (by rw [p2]; decide)
  have n3 : w ≠ spareD layout := wire_ne r (by rw [p3]; decide)
  have n4 : w ≠ layout.core.generic := wire_ne r (by rw [p4]; decide)
  have n5 : w ≠ layout.genericSelect := wire_ne r (by rw [p5]; decide)
  have n6 : w ≠ layout.core.equalNegY := wire_ne r (by rw [p6]; decide)
  have n7 : w ≠ layout.doubleSelect := wire_ne r (by rw [p7]; decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Wrapper5.U, Equiv.swap_apply_of_ne_of_ne n1 n2]
  · unfold tauM
    rw [if_neg n4, if_neg n5]
  · unfold swapE spareWire
    rw [if_neg n6, if_neg n1]
  · unfold swapD
    rw [if_neg n7, if_neg n3]

theorem fix_sub (P : Program)
    (h : wires P ⊆ (layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255)).toFinset ∪
      layout.point.y.toFinset) :
    renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) P))) = P := by
  have mem : ∀ w ∈ wires P, w ∈ layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255 ++
      layout.point.y) := by
    intro w hw
    rcases Finset.mem_union.mp (h hw) with a | a
    · simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at a ⊢; tauto
    · simp only [List.mem_toFinset] at a
      simp only [List.mem_cons, List.mem_append]; tauto
  have hU : renameProgram (Wrapper5.U layout) P = P :=
    rename_fix _ P (fun w hw => (fix_maps w (mem w hw)).1)
  have hM : renameProgram (tauM layout) P = P :=
    rename_fix _ P (fun w hw => (fix_maps w (mem w hw)).2.1)
  have hE : renameProgram (swapE layout) P = P :=
    rename_fix _ P (fun w hw => (fix_maps w (mem w hw)).2.2.1)
  have hD : renameProgram (swapD layout) P = P :=
    rename_fix _ P (fun w hw => (fix_maps w (mem w hw)).2.2.2)
  rw [hU, hM, hE, hD]

theorem zrep_fixed :
    renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (FiniteFlagInterval.zrep layout)))) =
      FiniteFlagInterval.zrep layout := by
  apply fix_sub
  rw [← FiniteFlagInterval.old_clrF_support layout layout_widths]
  exact (FiniteFlagInterval.zrep_support_old layout layout_widths).trans Finset.subset_union_left

theorem clearF_fixed :
    renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (CodexYParityProbe.clearF layout)))) =
      CodexYParityProbe.clearF layout := by
  apply fix_sub
  rw [← FiniteFlagInterval.old_clrF_support layout layout_widths]
  exact CodexYParityProbe.clearF_support_old layout layout_widths

theorem old_split {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    FusedFlags.finiteProgram layout (.some hc) cy
      (renameProgram (Wrapper5.U layout) (CodexYParityProbe.gen layout cx cy)) =
      oldStage layout (.some hc) cy ++
        shared layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy)) := by
  have hz := zrep_fixed
  have hf := clearF_fixed
  simp only [FusedFlags.rename_append] at hz hf
  rw [gen_split]
  simp only [FusedFlags.finiteProgram, oldStage, shared, FusedFlags.rename_append, hz, hf,
    List.append_assoc]

theorem new_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m' : List Bool)
    (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    run (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) m' s =
      run (FusedFlags.finiteProgram layout (.some hc) cy
        (renameProgram (Wrapper5.U layout) (CodexYParityProbe.gen layout cx cy)))
        (List.replicate (measurementCount (oldStage layout (.some hc) cy)) false ++
          m'.drop (measurementCount (stage layout (.some hc)))) s := by
  have hd : (List.replicate (measurementCount (oldStage layout (.some hc) cy)) false ++
      m'.drop (measurementCount (stage layout (.some hc)))).drop
        (measurementCount (oldStage layout (.some hc) cy)) =
      m'.drop (measurementCount (stage layout (.some hc))) := List.drop_left' (by simp)
  rw [old_split hc, finiteProgram', LocalWireModel.run_concat, LocalWireModel.run_concat, hd,
    stage_run_eq layout layout_widths layout_nodup hc b R s
      (List.replicate (measurementCount (oldStage layout (.some hc) cy)) false ++
        m'.drop (measurementCount (stage layout (.some hc)))) m' hs]

theorem wrapper'_eq {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m' : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    run (wrapper' layout (.some hc) (tailGen layout cx cy)) m' s =
      run (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy))
        (List.replicate (measurementCount (oldStage layout (.some hc) cy)) false ++
          m'.drop (measurementCount (stage layout (.some hc)))) s := by
  have hGen := CodexYParityProbe.genFFused_ok layout layout_widths layout_nodup hc
  have hsI := Edges.finite_specWith layout layout_widths layout_nodup R hc b
    (renameProgram (Wrapper5.U layout) (CodexYParityProbe.gen layout cx cy))
    (Wrapper5.genericOK_relabel layout layout_widths hc _ hGen)
    (FusedFlags.adapterProgram layout (.some hc) true) (FusedFlags.adapterProgram layout (.some hc) false)
    (fun R b D G H cov old => FusedFlags.boundary_step layout layout_widths layout_nodup hc true R b D G H
      false false cov (fun _ => ⟨rfl,rfl⟩) (by simp) old)
    (fun R b G D H cov old => FusedFlags.boundary_step layout layout_widths layout_nodup hc false R b false G
      false D H cov (by simp) (fun _ => ⟨rfl,rfl⟩) old)
  have h := hsI s (List.replicate (measurementCount (oldStage layout (.some hc) cy)) false ++
    m'.drop (measurementCount (stage layout (.some hc)))) hs
  rw [FusedFlags.finite_run layout layout_widths layout_nodup] at h
  have e := new_run hc b R s m' hs
  unfold wrapper' FusedFlags.wrapper
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
      (Wrapper5.U_outside layout layout_widths) (FusedFlags.finiteProgram layout (.some hc) cy
        (renameProgram (Wrapper5.U layout) (CodexYParityProbe.gen layout cx cy))) s _ hs.clean h.2.clean,
    Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
      (Wrapper5.U_outside layout layout_widths) (finiteProgram' layout (.some hc)
        (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) s m' hs.clean (by rw [e]; exact h.2.clean)]
  exact e

theorem full_spec' {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapper' layout (.some hc) (tailGen layout cx cy)
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m' hs
  have hz : regValue layout.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi : PointDialogBoundary layout R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  rw [wrapper'_eq hc b R s m' hi]
  exact FusedFlags.full_spec layout layout_widths layout_nodup R hc b _
    (CodexYParityProbe.genFFused_ok layout layout_widths layout_nodup hc)
    (CodexYParityProbe.gen_sites layout layout_widths layout_nodup cx cy) s _ hs

theorem counts_rel {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        toffoliCount (oldStage layout (.some hc) cy) =
      toffoliCount (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) +
        toffoliCount (stage layout (.some hc)) ∧
    measurementCount (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        measurementCount (oldStage layout (.some hc) cy) =
      measurementCount (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) +
        measurementCount (stage layout (.some hc)) ∧
    Challenge.gateSlots (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        Challenge.gateSlots (oldStage layout (.some hc) cy) =
      Challenge.gateSlots (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) +
        Challenge.gateSlots (stage layout (.some hc)) := by
  unfold wrapper' FusedFlags.wrapper
  rw [old_split hc]
  simp only [renameProgram_counts, rename_gateSlots, finiteProgram', toffoliCount_append,
    measurementCount_append, Challenge.gateSlots_append]
  omega

theorem oldStage_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    503 ≤ toffoliCount (oldStage layout (.some hc) cy) ∧
      measurementCount (oldStage layout (.some hc) cy) = 504 := by
  obtain ⟨i1, i2⟩ := InputSentinelAux.inputClass_counts_ge layout layout_widths hc
  have pr := FusedFlags.counts (DHClass.cxk (.some hc)) (yBit (.some hc))
  have pt := renameProgram_counts (LocalWireModel.label (FusedFlags.ports layout (DHClass.kx (.some hc))))
    (FusedFlags.clearPrefix (DHClass.cxk (.some hc)) (yBit (.some hc)))
  have z := FiniteFlagInterval.zrep_counts layout
  have c := CodexYParityProbe.counts layout layout_widths
  simp only [oldStage, FusedFlags.prefixProgram, toffoliCount_append, measurementCount_append, pt.1, pt.2,
    pr.1, pr.2.2.1, z.1, z.2, c.2.2.1, c.2.2.2, i2]
  exact ⟨by omega, trivial⟩

end Splice

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

section Cert
open Secp256k1 Challenge ControlledPointLayout
attribute [local irreducible] wires

theorem pool_take_mem (i : Nat) (hi : i < 256) : layout.dialogPool.getD i 0 ∈ layout.dialogPool.take 256 := by
  have hpl := dialogPool_length layout layout_widths
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩

theorem stage_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (stage layout (.some hc)) ⊆ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset ∪
      ({layout.genericSelect} ∪ (layout.dialogPool.take 256).toFinset) := by
  have hz : wires (FiniteFlagInterval.zrep layout) ⊆
      (layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255)).toFinset := by
    rw [← FiniteFlagInterval.old_clrF_support layout layout_widths]
    exact FiniteFlagInterval.zrep_support_old layout layout_widths
  have hcl := classifier_support (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
    layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
    layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) layout_widths.inputX (by simp [dialogPool_length layout layout_widths])
  have yl := yLow_mem layout layout_widths
  have hpl := dialogPool_length layout layout_widths
  have tk : ∀ n, n ≤ 256 → ∀ q ∈ layout.dialogPool.take n, q ∈ layout.dialogPool.take 256 := by
    intro n hn q hq
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hq
    simp only [List.length_take] at hi
    rw [List.getElem_take] at e
    rw [← e]
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  intro q hq
  unfold stage at hq
  rw [wires_append, Finset.mem_union] at hq
  simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset, List.mem_append,
    PointAddLayout.pointWires, List.mem_cons, List.mem_singleton]
  rcases hq with h | h
  · have h' := hz h
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at h'
    rcases h' with h' | h' | h'
    · exact Or.inl (Or.inl (Or.inl (Or.inl h')))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h')))
    · exact Or.inr (Or.inr (tk 255 (by decide) q h'))
  · have h' := hcl h
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at h'
    rcases h' with (h' | h') | h' | h' | h' | h' | h' | h' | h'
    · exact Or.inl (Or.inl (Or.inl (Or.inr h')))
    · exact Or.inr (Or.inr (tk 253 (by decide) q h'))
    · subst h'; exact Or.inl (Or.inl (Or.inr yl))
    · exact Or.inl (Or.inr (Or.inl h'))
    · exact Or.inl (Or.inl (Or.inl (Or.inl h')))
    · exact Or.inr (Or.inl h')
    · subst h'; exact Or.inr (Or.inr (pool_take_mem 253 (by decide)))
    · subst h'; exact Or.inr (Or.inr (pool_take_mem 254 (by decide)))
    · subst h'; exact Or.inr (Or.inr (pool_take_mem 255 (by decide)))

theorem stage_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (stage layout (.some hc)) = 257 ∧ measurementCount (stage layout (.some hc)) = 257 ∧
      Challenge.gateSlots (stage layout (.some hc)) ≤ 3590 := by
  have c := classifier_counts (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
    layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
    layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) (by simp [dialogPool_length layout layout_widths])
  have sl := classifier_slots (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
    layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
    layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) (by simp [dialogPool_length layout layout_widths])
  have z := FiniteFlagInterval.zrep_counts layout
  have zs := FiniteFlagInterval.zrep_slots layout layout_widths
  unfold stage
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append, z.1, z.2, c.1, c.2.1]
  exact ⟨trivial, trivial, by omega⟩

theorem stage_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (stage layout (.some hc)) := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, hext, hextx⟩ := stage_layout layout layout_widths layout_nodup
  unfold stage
  rw [gatePhysical_append]
  exact ⟨FiniteFlagInterval.zrep_physical layout layout_nodup,
    classifier_physical (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
      layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
      layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
      (layout.dialogPool.getD 255 0) hxl hwl hxn hwn hdisj hext hextx⟩

theorem io_mem (w : Wire) (h : w ∈ PointAddLayout.pointWires layout.point ++ [layout.control]) :
    w ∈ ioWires := by
  rcases List.mem_append.mp h with hp | hc
  · rw [Baselines.point_wires] at hp
    exact Finset.mem_range.mpr (List.mem_range'_1.mp hp).2
  · rw [List.mem_singleton] at hc
    subst hc
    exact Finset.mem_range.mpr (by decide)

theorem io_not_pool (w : Wire) (h : w ∈ PointAddLayout.pointWires layout.point ++ [layout.control]) :
    w ∉ layout.dialogPool := by
  have hD := layout.dialogUsed_nodup layout_nodup
  intro hp
  have c := List.nodup_iff_count_le_one.mp hD w
  have c1 : 1 ≤ (PointAddLayout.pointWires layout.point ++ [layout.control]).count w :=
    List.count_pos_iff.mpr h
  have c2 : 1 ≤ layout.dialogPool.count w := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.dialogUsedWires, List.count_append] at c c1
  omega

theorem finite_sub {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) ⊆
      wires (FusedFlags.finiteProgram layout (.some hc) cy
        (renameProgram (Wrapper5.U layout) (CodexYParityProbe.gen layout cx cy))) ∪
        (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
  rw [old_split hc, finiteProgram', wires_append, wires_append]
  apply Finset.union_subset
  · intro w hst
    rcases Finset.mem_union.mp (stage_support hc hst) with ht | hx
    · exact Finset.mem_union_right _ ht
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      simp only [oldStage, wires_append, Finset.mem_union]
      rcases Finset.mem_union.mp hx with hg | hp
      · rw [Finset.mem_singleton] at hg
        subst hg
        exact Or.inl (Or.inl (Or.inr (InputSentinelAux.prefix_generic_mem layout _)))
      · exact Or.inl (Or.inl (Or.inl
          (InputSentinelAux.inputClass_pool_mem layout layout_widths _ cy w (List.mem_toFinset.mp hp))))
  · exact fun w h => Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem wrapper'_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper' layout (.some hc) (tailGen layout cx cy)) ⊆
      wires (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) ∪
        (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
  unfold wrapper' FusedFlags.wrapper
  rw [renameProgram_support, renameProgram_support]
  intro q hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (finite_sub hc hw) with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
  · apply Finset.mem_union_right
    rw [Wrapper5.U_outside layout layout_widths w (io_not_pool w (List.mem_toFinset.mp h))]
    exact h

theorem support_used' {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper' layout (.some hc) (tailGen layout cx cy)) ⊆ layout.dialogUsedWires.toFinset := by
  have sites := CodexYParityProbe.gen_sites layout layout_widths layout_nodup cx cy
  have old := ((FusedFlags.wrapper_support layout hc (CodexYParityProbe.gen layout cx cy)).trans
    (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)).trans
      (WrapperOB5.support_used layout layout_widths)
  intro q hq
  rcases Finset.mem_union.mp (wrapper'_support hc hq) with o | t
  · exact old o
  · have t' := List.mem_toFinset.mp t
    apply List.mem_toFinset.mpr
    unfold ControlledPointLayout.dialogUsedWires
    exact List.mem_append_left _ (List.mem_append_left _ t')

theorem wrapper'_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapper' layout (.some hc) (tailGen layout cx cy)) := by
  have old := FusedFlags.wrapper_physical layout layout_widths layout_nodup (.some hc) cy _
    (CodexYParityProbe.gen_physical layout layout_widths layout_nodup cx cy)
  unfold FusedFlags.wrapper at old
  rw [R2SqEp760.gatePhysical_rename_iff, old_split hc, gatePhysical_append] at old
  unfold wrapper'
  rw [R2SqEp760.gatePhysical_rename_iff, finiteProgram', gatePhysical_append]
  exact ⟨stage_physical hc, old.2⟩

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ => wrapper' layout C (tailGen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2150821, 1498623, 1587, 50219722⟩

theorem program_correct (C : Point) (control : Bool) (R : Point) :
    Triple (encodes control R) (program C) (encodes control (if control then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    exact fixed_correct _ control R _ (full_spec' hc control R) (support_used' hc)

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2150821 := by
  cases C with
  | zero => simp [program, toffoliCount]
  | @some cx cy hc =>
    have r := (counts_rel hc).1
    have o := (oldStage_counts hc).1
    have st := (stage_counts hc).1
    have old := CodexYParityProbe.program_toffoli (.some hc)
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) ≤
      2151067 at old
    change toffoliCount (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 2150821
    omega

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1498623 := by
  cases C with
  | zero => simp [program, measurementCount]
  | @some cx cy hc =>
    have r := (counts_rel hc).2.1
    have o := (oldStage_counts hc).2
    have st := (stage_counts hc).2.1
    have old := CodexYParityProbe.program_measurements (.some hc)
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) ≤
      1498870 at old
    change measurementCount (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 1498623
    omega

theorem program_qubits (C : Point) : qubits (program C) ≤ 1587 := by
  cases C with
  | zero => change qubits [] ≤ 1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have sub := wrapper'_support hc
    have old := CodexYParityProbe.program_qubits (.some hc)
    change qubits (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) ≤ 1587 at old
    change qubits (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 1587
    refine le_trans (Finset.card_le_card ?_) old
    intro q hq
    rcases Finset.mem_union.mp hq with io | used
    · exact Finset.mem_union_left _ io
    · rcases Finset.mem_union.mp (sub used) with o | t
      · exact Finset.mem_union_right _ o
      · apply Finset.mem_union_left
        exact io_mem q (List.mem_toFinset.mp t)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program, GatePhysical]
  | @some cx cy hc => exact wrapper'_physical hc

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50219722 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have r := (counts_rel hc).2.2
    have st := (stage_counts hc).2.2
    have old := CodexYParityProbe.program_gateSlots (.some hc)
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) ≤
      50216132 at old
    change gateSlots (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 50219722
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C control R := (normalize_triple _ _ _).mpr (program_correct C control R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1498623
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50219722
    rw [normalize_slots]; exact program_gateSlots C

end Cert

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section OutputGadgets

/-- Little-endian word of a bit list. -/
def ofBits : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * ofBits bs

/-! Corner flag decode on local wires: 0 generic select (left holding the inverse flag), 1 control,
2 `x_r1`, 3 `x_r2`, 4 `y0`, 5 infinity flag, 6 double flag, 7 exception flag. -/

/-- Role 1: `x_r1` isolates `(-2C).x` (value `b1`), then `x_r2` isolates the sentinel (`s2`). -/
def predec1 (b1 s2 yc : Bool) : Program :=
  [.CX 1 0] ++ lit 2 b1 ++ [.CCX 0 2 7] ++ lit 2 b1 ++ [.CX 7 0] ++
  lit 3 s2 ++ [.CCX 0 3 5] ++ lit 3 s2 ++ [.CX 5 0] ++
  lit 4 yc ++ [.CCX 0 4 6] ++ lit 4 yc ++ [.CX 6 0]

/-- Role 2: `x_r1` isolates the sentinel (value `s1`), then `x_r2` isolates `(-2C).x` (`b2`). -/
def predec2 (s1 b2 yc : Bool) : Program :=
  [.CX 1 0] ++ lit 2 s1 ++ [.CCX 0 2 5] ++ lit 2 s1 ++ [.CX 5 0] ++
  lit 3 b2 ++ [.CCX 0 3 7] ++ lit 3 b2 ++ [.CX 7 0] ++
  lit 4 yc ++ [.CCX 0 4 6] ++ lit 4 yc ++ [.CX 6 0]

def predOut1 (b1 s2 yc : Bool) (x : Nat) : Nat :=
  let n := x.testBit 0 ^^ x.testBit 1
  let pB := x.testBit 2 == b1
  let pS := !pB && (x.testBit 3 == s2)
  let yC := x.testBit 4 == yc
  ofBits [n && !pB && !pS && !yC, x.testBit 1, x.testBit 2, x.testBit 3, x.testBit 4,
    n && pS, n && !pB && !pS && yC, n && pB]

def predOut2 (s1 b2 yc : Bool) (x : Nat) : Nat :=
  let n := x.testBit 0 ^^ x.testBit 1
  let pS := x.testBit 2 == s1
  let pB := !pS && (x.testBit 3 == b2)
  let yC := x.testBit 4 == yc
  ofBits [n && !pS && !pB && !yC, x.testBit 1, x.testBit 2, x.testBit 3, x.testBit 4,
    n && pS, n && !pS && !pB && yC, n && pB]

theorem predec1_ok : ∀ b1 s2 yc : Bool, ∀ x : Fin 32,
    safe (predec1 b1 s2 yc) x.val = true ∧ bitRun (predec1 b1 s2 yc) x.val = predOut1 b1 s2 yc x.val := by
  decide +kernel

theorem predec2_ok : ∀ s1 b2 yc : Bool, ∀ x : Fin 32,
    safe (predec2 s1 b2 yc) x.val = true ∧ bitRun (predec2 s1 b2 yc) x.val = predOut2 s1 b2 yc x.val := by
  decide +kernel

/-! Output tail on local wires: 0 `h` (zero-test bit), 1 `x_r1`, 2 `x_r2`, 3 `y0`, 4 control,
5 finite flag (scratch, then restored), 6 inverse flag, 7 infinity flag, 8 double flag,
9 exception flag, 10–12 clean scratch. -/

/-- Erase the corner flags given `x = C.x` on 10 (via 5) and `x = (-2C).x` on 12. -/
def leaves (yc y2c e : Bool) : Program :=
  [.measureX 6 [] [.CZ 4 11]] ++
  [.CCX 4 10 5] ++
  lit 3 yc ++ [.measureX 7 [] [.CZ 5 3]] ++ lit 3 yc ++
  (if e then lit 3 (!yc) ++ [.measureX 9 [] [.CZ 5 3]] ++ lit 3 (!yc) else []) ++
  [.measureX 5 [] [.CZ 4 10]] ++
  [.CCX 4 12 5] ++
  lit 3 y2c ++ [.measureX 8 [] [.CZ 5 3]] ++ lit 3 y2c ++
  [.measureX 5 [] [.CZ 4 12]] ++
  [.X 5, .CX 11 5]

/-- Role 1: `C.x` and the sentinel share `x_r1 = a1`; `x_r2 = s2` isolates the sentinel;
`(-2C).x` has `x_r2 = b2`. -/
def otail1 (a1 s2 b2 yc y2c e : Bool) : Program :=
  lit 1 a1 ++ [.CCX 0 1 10] ++ lit 1 a1 ++ [.CX 10 0] ++
  lit 2 s2 ++ [.CCX 10 2 11] ++ lit 2 s2 ++ [.CX 11 10] ++
  lit 2 b2 ++ [.CCX 0 2 12] ++ lit 2 b2 ++
  leaves yc y2c e ++
  lit 2 b2 ++ [.measureX 12 [] [.CZ 0 2]] ++ lit 2 b2 ++
  [.CX 11 10] ++
  lit 2 s2 ++ [.measureX 11 [] [.CZ 10 2]] ++ lit 2 s2 ++
  [.CX 10 0] ++
  lit 1 a1 ++ [.measureX 10 [] [.CZ 0 1]] ++ lit 1 a1

/-- Role 2: `C.x` and `(-2C).x` share `x_r1 = a1`; `x_r2 = b2` isolates `(-2C).x`;
the sentinel has `x_r2 = s2`. -/
def otail2 (a1 s2 b2 yc y2c e : Bool) : Program :=
  lit 1 a1 ++ [.CCX 0 1 10] ++ lit 1 a1 ++ [.CX 10 0] ++
  lit 2 s2 ++ [.CCX 0 2 11] ++ lit 2 s2 ++
  lit 2 b2 ++ [.CCX 10 2 12] ++ lit 2 b2 ++ [.CX 12 10] ++
  leaves yc y2c e ++
  [.CX 12 10] ++
  lit 2 b2 ++ [.measureX 12 [] [.CZ 10 2]] ++ lit 2 b2 ++
  lit 2 s2 ++ [.measureX 11 [] [.CZ 0 2]] ++ lit 2 s2 ++
  [.CX 10 0] ++
  lit 1 a1 ++ [.measureX 10 [] [.CZ 0 1]] ++ lit 1 a1

/-- Match bits of the three constants from the zero-test bit and the pivots. -/
def oxS1 (a1 s2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 == a1) && (r2 == s2)
def oxA1 (a1 s2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 == a1) && (r2 != s2)
def oxB1 (a1 b2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 != a1) && (r2 == b2)
def oxS2 (a1 s2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 != a1) && (r2 == s2)
def oxA2 (a1 b2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 == a1) && (r2 != b2)
def oxB2 (a1 b2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 == a1) && (r2 == b2)

/-- Tail input word from the free bits `h, x_r1, x_r2, y0, c` (bits 0–4 of `v`). -/
def oin (xS xA xB : Bool) (yc y2c e : Bool) (v : Nat) : Nat :=
  let c := v.testBit 4
  let y0 := v.testBit 3
  ofBits [v.testBit 0, v.testBit 1, v.testBit 2, y0, c, false,
    c && xS, c && xA && (y0 == yc), c && xB && (y0 == y2c), e && c && xA && (y0 != yc),
    false, false, false]

def oout (xS : Bool) (v : Nat) : Nat :=
  ofBits [v.testBit 0, v.testBit 1, v.testBit 2, v.testBit 3, v.testBit 4, !xS,
    false, false, false, false, false, false, false]

theorem otail1_ok : ∀ a1 s2 b2 yc y2c e : Bool, ∀ v : Fin 32,
    let xS := oxS1 a1 s2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xA := oxA1 a1 s2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xB := oxB1 a1 b2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    safe (otail1 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val) = true ∧
      bitRun (otail1 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val) = oout xS v.val := by
  decide +kernel

theorem otail2_ok : ∀ a1 s2 b2 yc y2c e : Bool, ∀ v : Fin 32,
    let xS := oxS2 a1 s2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xA := oxA2 a1 b2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xB := oxB2 a1 b2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    safe (otail2 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val) = true ∧
      bitRun (otail2 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val) = oout xS v.val := by
  decide +kernel

theorem predec_counts (b1 s2 yc : Bool) :
    toffoliCount (predec1 b1 s2 yc) = 3 ∧ measurementCount (predec1 b1 s2 yc) = 0 ∧
    toffoliCount (predec2 b1 s2 yc) = 3 ∧ measurementCount (predec2 b1 s2 yc) = 0 := by
  cases b1 <;> cases s2 <;> cases yc <;> decide

theorem otail_counts (a1 s2 b2 yc y2c e : Bool) :
    toffoliCount (otail1 a1 s2 b2 yc y2c e) = 5 ∧ toffoliCount (otail2 a1 s2 b2 yc y2c e) = 5 ∧
    measurementCount (otail1 a1 s2 b2 yc y2c e) = (if e then 9 else 8) ∧
    measurementCount (otail2 a1 s2 b2 yc y2c e) = (if e then 9 else 8) := by
  cases a1 <;> cases s2 <;> cases b2 <;> cases yc <;> cases y2c <;> cases e <;> decide

end OutputGadgets

section OutputStage
open Secp256k1 ControlledPointLayout

/-- Corner decode for the constants of `tr` (role chosen by the pivots). -/
def predecT (tr : Tri) (yc : Bool) : Program :=
  if tr.role1 then predec1 (tr.B.testBit tr.r1) (tr.S.testBit tr.r2) yc
  else predec2 (tr.S.testBit tr.r1) (tr.B.testBit tr.r2) yc

def predecL (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire) : Program :=
  renameProgram (LocalWireModel.label
    (fun q : Fin 8 => [g, c, xr1, xr2, y0, O, D, H].getD q.val 0)) (predecT tr yc)

/-- Output tail for the constants of `tr`. -/
def otail (tr : Tri) (yc y2c e : Bool) : Program :=
  if tr.role1 then otail1 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) (tr.B.testBit tr.r2) yc y2c e
  else otail2 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) (tr.B.testBit tr.r2) yc y2c e

def otailL (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire) (h : Wire) : Program :=
  renameProgram (LocalWireModel.label
    (fun q : Fin 13 => [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].getD q.val 0)) (otail tr yc y2c e)

/-- Output classifier: the input-stage zero test on the output abscissa with the output tail. -/
def oclassifier (tr : Tri) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) : Program :=
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  (zeroWith (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work) ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx)))

/-- Sentinel-coded corner outputs: `O ↦ C`, `C ↦ 2C`, `-C ↦ O`, `-2C ↦ -C`. -/
def ocorners (L : ControlledPointLayout) (C : Point) : Program :=
  maskedConstant (parkWire L) L.point.x (FiniteFlagInterval.sentinel ^^^ pairCode C) ++
  maskedConstant (parkWire L) L.point.y (pointY C) ++
  maskedConstant L.doubleSelect L.point.x (pairCode C ^^^ pairCode (dialogExceptionPoint C)) ++
  maskedConstant L.doubleSelect L.point.y (pointY C ^^^ pointY (C + C)) ++
  maskedConstant L.genericSelect L.point.x (pairCode C ^^^ FiniteFlagInterval.sentinel) ++
  maskedConstant L.genericSelect L.point.y (pointY (-C)) ++
  maskedConstant L.core.equalNegY L.point.x (pairCode (dialogExceptionPoint C) ^^^ pairCode C) ++
  maskedConstant L.core.equalNegY L.point.y (pointY (dialogExceptionPoint C) ^^^ pointY (-C))

/-- The merged output stage, run after the relabelled generic block on the sentinel-coded point. -/
def outStage (L : ControlledPointLayout) (C : Point) : Program :=
  predecL (triOf C) (yBit C) L.genericSelect L.control (L.point.x.getD (triOf C).r1 0)
    (L.point.x.getD (triOf C).r2 0) (yLow L) (parkWire L) L.doubleSelect L.core.equalNegY ++
  ocorners L C ++
  oclassifier (triOf C) (yBit C) (yBit (C + C)) (exceptionBit C) L.point.x (L.dialogPool.take 253)
    (yLow L) L.control L.point.finite L.genericSelect (parkWire L) L.doubleSelect L.core.equalNegY
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0) ++
  FiniteFlagInterval.zrep L

end OutputStage

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

section OutCorners
open Secp256k1 ControlledPointLayout
attribute [local irreducible] wires

/-! ### The fused suffix touches the double flag, the negation flag and the park wire -/

theorem suffix_mem (L : ControlledPointLayout) (C : Point) :
    L.doubleSelect ∈ wires (FusedFlags.suffixProgram L C) ∧
    L.core.equalNegY ∈ wires (FusedFlags.suffixProgram L C) ∧
    parkWire L ∈ wires (FusedFlags.suffixProgram L C) := by
  unfold FusedFlags.suffixProgram
  rw [renameProgram_support]
  have hmem : ∀ q ∈ ({4, 6, 10} : Finset Wire),
      q ∈ wires (FusedFlags.restoreSuffix (DHClass.cxk C) (yBit C)) := by
    intro q hq
    unfold FusedFlags.restoreSuffix
    rw [wires_append]
    apply Finset.mem_union_right
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> simp [wires, Instr.wires]
  exact ⟨Finset.mem_image.mpr ⟨4, hmem 4 (by simp), rfl⟩,
    Finset.mem_image.mpr ⟨6, hmem 6 (by simp), rfl⟩,
    Finset.mem_image.mpr ⟨10, hmem 10 (by simp), rfl⟩⟩

/-! ### The corner constants -/

/-- The abscissa change of the corner block for corner flags `O D I H`. -/
def cornerX (C : Point) (O D I H : Bool) : Nat :=
  (if O then FiniteFlagInterval.sentinel ^^^ pairCode C else 0) ^^^
  (if D then pairCode C ^^^ pairCode (dialogExceptionPoint C) else 0) ^^^
  (if I then pairCode C ^^^ FiniteFlagInterval.sentinel else 0) ^^^
  (if H then pairCode (dialogExceptionPoint C) ^^^ pairCode C else 0)

/-- The ordinate change of the corner block for corner flags `O D I H`. -/
def cornerY (C : Point) (O D I H : Bool) : Nat :=
  (if O then pointY C else 0) ^^^
  (if D then pointY C ^^^ pointY (C + C) else 0) ^^^
  (if I then pointY (-C) else 0) ^^^
  (if H then pointY (dialogExceptionPoint C) ^^^ pointY (-C) else 0)

theorem point_x_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) : L.point.x.Nodup := by
  have h := L.dialogUsed_nodup hn
  simp only [dialogUsedWires, PointAddLayout.pointWires, List.cons_append, List.append_assoc] at h
  exact (List.nodup_cons.mp h).2.sublist (List.sublist_append_left _ _)

theorem point_y_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) : L.point.y.Nodup := by
  have h := L.dialogUsed_nodup hn
  simp only [dialogUsedWires, PointAddLayout.pointWires, List.cons_append, List.append_assoc] at h
  exact ((List.nodup_cons.mp h).2.sublist (List.sublist_append_right _ _)).sublist
    (List.sublist_append_left _ _)

theorem flag_not_point (L : ControlledPointLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q ∈ L.inPlaceFlags) : q ∉ L.point.x ∧ q ∉ L.point.y := by
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hf := List.count_pos_iff.mpr hq
  simp only [dialogUsedWires, PointAddLayout.pointWires, List.count_append, List.count_cons] at h
  constructor
  · intro hx
    have := List.count_pos_iff.mpr hx
    split_ifs at h <;> omega
  · intro hy
    have := List.count_pos_iff.mpr hy
    split_ifs at h <;> omega

theorem park_not_point (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    parkWire L ∉ L.point.x ∧ parkWire L ∉ L.point.y := by
  have pa := (park_away L hw hn).1
  exact ⟨fun h => pa (by simp [PointAddLayout.pointWires, h]),
    fun h => pa (by simp [PointAddLayout.pointWires, h])⟩

/-- One masked constant on `r`, with `r'` a disjoint register and `c` off both. -/
theorem masked_step (r r' : List Wire) (c : Wire) (k : Nat) (hn : r.Nodup) (hcr : c ∉ r)
    (hcr' : c ∉ r') (hk : k < 2^r.length) (hd : ∀ w ∈ r', w ∉ r) (s t : State) (V V' : Nat)
    (m : List Bool)
    (h : t.phase = s.phase ∧ regValue r t.basis = V ∧ regValue r' t.basis = V' ∧
      ∀ w, w ∉ r → w ∉ r' → t.basis w = s.basis w) :
    (run (maskedConstant c r k) m t).phase = s.phase ∧
    regValue r (run (maskedConstant c r k) m t).basis = V ^^^ (if s.basis c then k else 0) ∧
    regValue r' (run (maskedConstant c r k) m t).basis = V' ∧
    ∀ w, w ∉ r → w ∉ r' → (run (maskedConstant c r k) m t).basis w = s.basis w := by
  obtain ⟨hp, hout, hv⟩ := maskedConstant_correct c r k hn hcr hk t m
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc : t.basis c = s.basis c := h4 c hcr hcr'
  refine ⟨hp.trans h1, by rw [hv, h2, hc], ?_, fun w hw hw' => (hout w hw).trans (h4 w hw hw')⟩
  rw [← h3]
  exact regValue_congr _ _ _ (fun w hw => hout w (hd w hw))

theorem run_masked_append (c : Wire) (r : List Wire) (k : Nat) (q : Program) (m : List Bool)
    (s : State) : run (maskedConstant c r k ++ q) m s = run q m (run (maskedConstant c r k) [] s) := by
  rw [run_append, (maskedConstant_counts c r k).2, List.drop_zero, List.take_zero]

theorem ocorners_run (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    (s : State) (m : List Bool) :
    (run (ocorners L C) m s).phase = s.phase ∧
    regValue L.point.x (run (ocorners L C) m s).basis = regValue L.point.x s.basis ^^^
      cornerX C (s.basis (parkWire L)) (s.basis L.doubleSelect) (s.basis L.genericSelect)
        (s.basis L.core.equalNegY) ∧
    regValue L.point.y (run (ocorners L C) m s).basis = regValue L.point.y s.basis ^^^
      cornerY C (s.basis (parkWire L)) (s.basis L.doubleSelect) (s.basis L.genericSelect)
        (s.basis L.core.equalNegY) ∧
    ∀ q, q ∉ L.point.x → q ∉ L.point.y → (run (ocorners L C) m s).basis q = s.basis q := by
  have hxl : L.point.x.length = 256 := hw.inputX
  have hyl : L.point.y.length = 256 := hw.inputY
  have hxn := point_x_nodup L hn
  have hyn := point_y_nodup L hn
  have hyx : ∀ w ∈ L.point.y, w ∉ L.point.x := y_not_x L hn
  have hxy : ∀ w ∈ L.point.x, w ∉ L.point.y := fun w hx hy => hyx w hy hx
  have hP := park_not_point L hw hn
  have hD := flag_not_point L hn L.doubleSelect (by simp [inPlaceFlags])
  have hG := flag_not_point L hn L.genericSelect (by simp [inPlaceFlags])
  have hH := flag_not_point L hn L.core.equalNegY (by simp [inPlaceFlags])
  have hp256 : p < 2^256 := by norm_num [p]
  have bX : ∀ R : Point, pairCode R < 2^256 := pairCode_lt
  have bY : ∀ R : Point, pointY R < 2^256 := fun R => lt_trans (point_coordinates_lt R).2 hp256
  have bS : FiniteFlagInterval.sentinel < 2^256 := lt_trans FiniteFlagInterval.sentinel_lt hp256
  have kx : ∀ a b : Nat, a < 2^256 → b < 2^256 → a ^^^ b < 2^L.point.x.length := fun a b ha hb => by
    rw [hxl]; exact Nat.xor_lt_two_pow ha hb
  have ky : ∀ a b : Nat, a < 2^256 → b < 2^256 → a ^^^ b < 2^L.point.y.length := fun a b ha hb => by
    rw [hyl]; exact Nat.xor_lt_two_pow ha hb
  have ky1 : ∀ R : Point, pointY R < 2^L.point.y.length := fun R => by rw [hyl]; exact bY R
  have swap : ∀ (t : State), (∀ w, w ∉ L.point.x → w ∉ L.point.y → t.basis w = s.basis w) →
      ∀ w, w ∉ L.point.y → w ∉ L.point.x → t.basis w = s.basis w := fun t h w a b => h w b a
  have swap' : ∀ (t : State), (∀ w, w ∉ L.point.y → w ∉ L.point.x → t.basis w = s.basis w) →
      ∀ w, w ∉ L.point.x → w ∉ L.point.y → t.basis w = s.basis w := fun t h w a b => h w b a
  have h0 : s.phase = s.phase ∧ regValue L.point.x s.basis = regValue L.point.x s.basis ∧
      regValue L.point.y s.basis = regValue L.point.y s.basis ∧
      ∀ w, w ∉ L.point.x → w ∉ L.point.y → s.basis w = s.basis w := ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
  have e1 := masked_step L.point.x L.point.y (parkWire L) (FiniteFlagInterval.sentinel ^^^ pairCode C)
    hxn hP.1 hP.2 (kx _ _ bS (bX C)) hyx s s _ _ [] h0
  have e2 := masked_step L.point.y L.point.x (parkWire L) (pointY C) hyn hP.2 hP.1 (ky1 C) hxy s _ _ _ []
    ⟨e1.1, e1.2.2.1, e1.2.1, swap _ e1.2.2.2⟩
  have e3 := masked_step L.point.x L.point.y L.doubleSelect (pairCode C ^^^ pairCode (dialogExceptionPoint C))
    hxn hD.1 hD.2 (kx _ _ (bX C) (bX (dialogExceptionPoint C))) hyx s _ _ _ []
    ⟨e2.1, e2.2.2.1, e2.2.1, swap' _ e2.2.2.2⟩
  have e4 := masked_step L.point.y L.point.x L.doubleSelect (pointY C ^^^ pointY (C + C))
    hyn hD.2 hD.1 (ky _ _ (bY C) (bY (C + C))) hxy s _ _ _ []
    ⟨e3.1, e3.2.2.1, e3.2.1, swap _ e3.2.2.2⟩
  have e5 := masked_step L.point.x L.point.y L.genericSelect (pairCode C ^^^ FiniteFlagInterval.sentinel)
    hxn hG.1 hG.2 (kx _ _ (bX C) bS) hyx s _ _ _ []
    ⟨e4.1, e4.2.2.1, e4.2.1, swap' _ e4.2.2.2⟩
  have e6 := masked_step L.point.y L.point.x L.genericSelect (pointY (-C)) hyn hG.2 hG.1 (ky1 (-C)) hxy s _ _ _ []
    ⟨e5.1, e5.2.2.1, e5.2.1, swap _ e5.2.2.2⟩
  have e7 := masked_step L.point.x L.point.y L.core.equalNegY (pairCode (dialogExceptionPoint C) ^^^ pairCode C)
    hxn hH.1 hH.2 (kx _ _ (bX (dialogExceptionPoint C)) (bX C)) hyx s _ _ _ []
    ⟨e6.1, e6.2.2.1, e6.2.1, swap' _ e6.2.2.2⟩
  have e8 := masked_step L.point.y L.point.x L.core.equalNegY (pointY (dialogExceptionPoint C) ^^^ pointY (-C))
    hyn hH.2 hH.1 (ky _ _ (bY (dialogExceptionPoint C)) (bY (-C))) hxy s _ _ _ m
    ⟨e7.1, e7.2.2.1, e7.2.1, swap _ e7.2.2.2⟩
  have hrun : run (ocorners L C) m s =
      run (maskedConstant L.core.equalNegY L.point.y (pointY (dialogExceptionPoint C) ^^^ pointY (-C))) m
      (run (maskedConstant L.core.equalNegY L.point.x (pairCode (dialogExceptionPoint C) ^^^ pairCode C)) []
      (run (maskedConstant L.genericSelect L.point.y (pointY (-C))) []
      (run (maskedConstant L.genericSelect L.point.x (pairCode C ^^^ FiniteFlagInterval.sentinel)) []
      (run (maskedConstant L.doubleSelect L.point.y (pointY C ^^^ pointY (C + C))) []
      (run (maskedConstant L.doubleSelect L.point.x (pairCode C ^^^ pairCode (dialogExceptionPoint C))) []
      (run (maskedConstant (parkWire L) L.point.y (pointY C)) []
      (run (maskedConstant (parkWire L) L.point.x (FiniteFlagInterval.sentinel ^^^ pairCode C)) [] s))))))) := by
    simp only [ocorners, List.append_assoc, run_masked_append]
  rw [hrun]
  refine ⟨e8.1, ?_, ?_, swap' _ e8.2.2.2⟩
  · rw [e8.2.2.1]
    simp only [cornerX, Nat.xor_assoc]
  · rw [e8.2.1]
    simp only [cornerY, Nat.xor_assoc]

theorem ocorners_counts (L : ControlledPointLayout) (C : Point) :
    toffoliCount (ocorners L C) = 0 ∧ measurementCount (ocorners L C) = 0 := by
  constructor <;> simp [ocorners, toffoliCount_append, measurementCount_append,
    (maskedConstant_counts _ _ _).1, (maskedConstant_counts _ _ _).2]

theorem ocorners_support (L : ControlledPointLayout) (C : Point) :
    wires (ocorners L C) ⊆
      (L.point.x ++ L.point.y ++ [parkWire L, L.doubleSelect, L.genericSelect, L.core.equalNegY]).toFinset := by
  have hs : ∀ (c : Wire) (r : List Wire) (k : Nat),
      c ∈ [parkWire L, L.doubleSelect, L.genericSelect, L.core.equalNegY] →
      (r = L.point.x ∨ r = L.point.y) → wires (maskedConstant c r k) ⊆
        (L.point.x ++ L.point.y ++ [parkWire L, L.doubleSelect, L.genericSelect, L.core.equalNegY]).toFinset := by
    intro c r k hc hr q hq
    have hm := maskedConstant_wires_subset c r k hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hm hc ⊢
    rcases hm with rfl | hm
    · exact Or.inr hc
    · rcases hr with rfl | rfl
      · exact Or.inl (Or.inl hm)
      · exact Or.inl (Or.inr hm)
  simp only [ocorners, wires_append]
  repeat' apply Finset.union_subset
  all_goals exact hs _ _ _ (by simp) (by simp)

theorem ocorners_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) :
    GatePhysical (ocorners L C) := by
  have hP := park_not_point L hw hn
  have hD := flag_not_point L hn L.doubleSelect (by simp [inPlaceFlags])
  have hG := flag_not_point L hn L.genericSelect (by simp [inPlaceFlags])
  have hH := flag_not_point L hn L.core.equalNegY (by simp [inPlaceFlags])
  simp only [ocorners, List.append_assoc, gatePhysical_append]
  exact ⟨maskedConstant_physical _ _ _ hP.1, maskedConstant_physical _ _ _ hP.2,
    maskedConstant_physical _ _ _ hD.1, maskedConstant_physical _ _ _ hD.2,
    maskedConstant_physical _ _ _ hG.1, maskedConstant_physical _ _ _ hG.2,
    maskedConstant_physical _ _ _ hH.1, maskedConstant_physical _ _ _ hH.2⟩

end OutCorners

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section OutTail
open Challenge

/-! ### Bits of a little-endian word -/

theorem ofBits_testBit : ∀ (bs : List Bool) (q : Nat), (ofBits bs).testBit q = bs.getD q false
  | [], q => by simp [ofBits]
  | b :: bs, q => by
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    cases q with
    | zero =>
      rw [Nat.testBit_zero]
      cases b <;> simp [ofBits, Nat.add_mul_mod_self_left]
    | succ q =>
      rw [Nat.testBit_succ, show ofBits (b :: bs) / 2 = ofBits bs by simp only [ofBits]; omega]
      simpa using ofBits_testBit bs q

/-! ### The output tail's match bits and its two roles -/

/-- A match bit of the output tail: the zero-test bit `h` and the pivot pattern of `K`. -/
def tX (tr : Tri) (K : Nat) (h a b : Bool) : Bool := h && decide ((a, b) = tr.pat K)

theorem role_facts (tr : Tri) (v : tr.Valid) :
    tr.B.testBit tr.r1 = !tr.S.testBit tr.r1 ∧
    (tr.role1 = true → tr.A.testBit tr.r1 = tr.S.testBit tr.r1 ∧ tr.A.testBit tr.r2 = !tr.S.testBit tr.r2) ∧
    (tr.role1 = false → tr.A.testBit tr.r1 = !tr.S.testBit tr.r1 ∧ tr.A.testBit tr.r2 = !tr.B.testBit tr.r2) := by
  have d1 := (firstDiff_spec tr.B tr.S v.hB v.hS v.BS).2
  have er1 : tr.r1 = firstDiff tr.B tr.S := rfl
  rw [← er1] at d1
  refine ⟨?_, ?_, ?_⟩
  · cases hB : tr.B.testBit tr.r1 <;> cases hS : tr.S.testBit tr.r1 <;> simp_all
  · intro ro
    have eq1 : tr.A.testBit tr.r1 = tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
    have er2 : tr.r2 = firstDiff tr.A tr.S := by simp [Tri.r2, ro]
    have d2 := (firstDiff_spec tr.A tr.S v.hA v.hS v.AS).2
    rw [← er2] at d2
    refine ⟨eq1, ?_⟩
    cases hA : tr.A.testBit tr.r2 <;> cases hS : tr.S.testBit tr.r2 <;> simp_all
  · intro ro
    have ne1 : tr.A.testBit tr.r1 ≠ tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
    have er2 : tr.r2 = firstDiff tr.A tr.B := by simp [Tri.r2, ro]
    have d2 := (firstDiff_spec tr.A tr.B v.hA v.hB v.AB).2
    rw [← er2] at d2
    constructor
    · cases hA : tr.A.testBit tr.r1 <;> cases hS : tr.S.testBit tr.r1 <;> simp_all
    · cases hA : tr.A.testBit tr.r2 <;> cases hB : tr.B.testBit tr.r2 <;> simp_all

theorem tX_bridge (tr : Tri) (v : tr.Valid) (hb r1b r2b : Bool) :
    (tr.role1 = true →
      tX tr tr.S hb r1b r2b = oxS1 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) hb r1b r2b ∧
      tX tr tr.A hb r1b r2b = oxA1 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) hb r1b r2b ∧
      tX tr tr.B hb r1b r2b = oxB1 (tr.A.testBit tr.r1) (tr.B.testBit tr.r2) hb r1b r2b) ∧
    (tr.role1 = false →
      tX tr tr.S hb r1b r2b = oxS2 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) hb r1b r2b ∧
      tX tr tr.A hb r1b r2b = oxA2 (tr.A.testBit tr.r1) (tr.B.testBit tr.r2) hb r1b r2b ∧
      tX tr tr.B hb r1b r2b = oxB2 (tr.A.testBit tr.r1) (tr.B.testBit tr.r2) hb r1b r2b) := by
  obtain ⟨fB, f1, f2⟩ := role_facts tr v
  constructor
  · intro ro
    obtain ⟨e1, e2⟩ := f1 ro
    simp only [tX, Tri.pat, oxS1, oxA1, oxB1, Prod.mk.injEq, e1, e2, fB]
    generalize tr.S.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    revert a b c hb r1b r2b; decide
  · intro ro
    obtain ⟨e1, e2⟩ := f2 ro
    simp only [tX, Tri.pat, oxS2, oxA2, oxB2, Prod.mk.injEq, e1, e2, fB]
    generalize tr.S.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    revert a b c hb r1b r2b; decide

/-- The output gadget's classical check in the triple's own terms (either role). -/
theorem otail_core (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (w : Fin 32) :
    safe (otail tr yc y2c e) (oin (tX tr tr.S (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.A (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.B (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)) yc y2c e w.val) = true ∧
    bitRun (otail tr yc y2c e) (oin (tX tr tr.S (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.A (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.B (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)) yc y2c e w.val) =
      oout (tX tr tr.S (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)) w.val := by
  have br := tX_bridge tr v (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)
  unfold otail
  by_cases ro : tr.role1 = true
  · obtain ⟨hS, hA, hB⟩ := br.1 ro
    rw [if_pos ro, hS, hA, hB]
    exact otail1_ok _ _ _ yc y2c e w
  · have ro' : tr.role1 = false := by simpa using ro
    obtain ⟨hS, hA, hB⟩ := br.2 ro'
    rw [if_neg ro, hS, hA, hB]
    exact otail2_ok _ _ _ yc y2c e w

theorem otail_support (tr : Tri) (yc y2c e : Bool) : wires (otail tr yc y2c e) ⊆ Finset.range 13 := by
  unfold otail
  split_ifs <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    cases a <;> cases b <;> cases c <;> cases yc <;> cases y2c <;> cases e <;> decide

theorem otail_physical (tr : Tri) (yc y2c e : Bool) : GatePhysical (otail tr yc y2c e) := by
  unfold otail
  split_ifs <;> apply gatePhysical_of_all <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    cases a <;> cases b <;> cases c <;> cases yc <;> cases y2c <;> cases e <;> decide

theorem otail_slots (tr : Tri) (yc y2c e : Bool) : gateSlots (otail tr yc y2c e) ≤ 45 := by
  unfold otail
  split_ifs <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    cases a <;> cases b <;> cases c <;> cases yc <;> cases y2c <;> cases e <;> decide

theorem otail_counts' (tr : Tri) (yc y2c e : Bool) :
    toffoliCount (otail tr yc y2c e) = 5 ∧ measurementCount (otail tr yc y2c e) = (if e then 9 else 8) := by
  unfold otail
  by_cases ro : tr.role1 = true
  · rw [if_pos ro]
    exact ⟨(otail_counts _ _ _ _ _ _).1, (otail_counts _ _ _ _ _ _).2.2.1⟩
  · rw [if_neg ro]
    exact ⟨(otail_counts _ _ _ _ _ _).2.1, (otail_counts _ _ _ _ _ _).2.2.2⟩

/-! ### The output tail on its thirteen wires -/

theorem otailL_support (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire) :
    wires (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) ⊆
      {h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u} := by
  unfold otailL
  rw [renameProgram_support]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  have ha13 : a < 13 := Finset.mem_range.mp (otail_support tr yc y2c e ha)
  simp only [LocalWireModel.label, dif_pos ha13]
  interval_cases a <;> simp

theorem otailL_physical (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire)
    (hnd : [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup) :
    GatePhysical (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) := by
  have inj := LocalWireModel.listPorts_injective [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] hnd
    (n := 13) (by simp)
  unfold otailL
  exact gatePhysical_rename_support _ _ (fun a ha b hb heq =>
    LocalWireModel.label_injective _ inj a (otail_support tr yc y2c e ha) b (otail_support tr yc y2c e hb) heq)
    (otail_physical tr yc y2c e)

theorem otailL_counts (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire) :
    toffoliCount (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) = 5 ∧
    measurementCount (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) = (if e then 9 else 8) := by
  unfold otailL
  rw [(renameProgram_counts _ _).1, (renameProgram_counts _ _).2]
  exact otail_counts' tr yc y2c e

theorem otailL_slots (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire) :
    gateSlots (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) = gateSlots (otail tr yc y2c e) := by
  unfold otailL
  exact rename_gateSlots _ _

/-- Tail precondition: clean scratch, and the four corner flags hold their match bits. -/
def otailPre (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire) (uu : Bool)
    (st : BasisState) : Prop :=
  st f = false ∧ st t1 = false ∧ st t2 = false ∧ st u = false ∧
  st g = (st c && tX tr tr.S uu (st xr1) (st xr2)) ∧
  st O = (st c && tX tr tr.A uu (st xr1) (st xr2) && (st y0 == yc)) ∧
  st D = (st c && tX tr tr.B uu (st xr1) (st xr2) && (st y0 == y2c)) ∧
  st H = (e && st c && tX tr tr.A uu (st xr1) (st xr2) && (st y0 != yc))

/-- Tail effect: the finite flag takes the negated sentinel match and the four flags are cleared. -/
def otailEff (tr : Tri) (xr1 xr2 f g O D H : Wire) (uu : Bool) (st : BasisState) : BasisState :=
  writeBit (writeBit (writeBit (writeBit (writeBit st f (!tX tr tr.S uu (st xr1) (st xr2))) g false)
    O false) D false) H false

theorem otailEff_apply (tr : Tri) (xr1 xr2 f g O D H : Wire) (uu : Bool) (st : BasisState) (q : Wire) :
    otailEff tr xr1 xr2 f g O D H uu st q =
      if q = H then false else if q = D then false else if q = O then false else if q = g then false
      else if q = f then !tX tr tr.S uu (st xr1) (st xr2) else st q := by
  unfold otailEff
  simp only [writeBit, Function.update_apply]

theorem otail_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (h xr1 xr2 y0 c f g O D H t1 t2 u : Wire)
    (hnd : [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup) (s : State) (m : List Bool)
    (hp : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u (s.basis h) s.basis) :
    run (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) m s =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H (s.basis h) s.basis⟩ := by
  unfold otailPre at hp
  obtain ⟨pf, pt1, pt2, pu, pg, pO, pD, pH⟩ := hp
  set r : List Wire := [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] with hr
  have inj := LocalWireModel.listPorts_injective r hnd (n := 13) (by simp [hr])
  have rne : ∀ i j, i < 13 → j < 13 → i ≠ j → r.getD i 0 ≠ r.getD j 0 := by
    intro i j hi hj hij e
    have hi' : i < r.length := by simp [hr]; omega
    have hj' : j < r.length := by simp [hr]; omega
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at e
    exact hij (hnd.getElem_inj_iff.mp e)
  have n_h_f : h ≠ f := by simpa [hr] using rne 0 5 (by decide) (by decide) (by decide)
  have n_h_g : h ≠ g := by simpa [hr] using rne 0 6 (by decide) (by decide) (by decide)
  have n_h_O : h ≠ O := by simpa [hr] using rne 0 7 (by decide) (by decide) (by decide)
  have n_h_D : h ≠ D := by simpa [hr] using rne 0 8 (by decide) (by decide) (by decide)
  have n_h_H : h ≠ H := by simpa [hr] using rne 0 9 (by decide) (by decide) (by decide)
  have n_xr1_f : xr1 ≠ f := by simpa [hr] using rne 1 5 (by decide) (by decide) (by decide)
  have n_xr1_g : xr1 ≠ g := by simpa [hr] using rne 1 6 (by decide) (by decide) (by decide)
  have n_xr1_O : xr1 ≠ O := by simpa [hr] using rne 1 7 (by decide) (by decide) (by decide)
  have n_xr1_D : xr1 ≠ D := by simpa [hr] using rne 1 8 (by decide) (by decide) (by decide)
  have n_xr1_H : xr1 ≠ H := by simpa [hr] using rne 1 9 (by decide) (by decide) (by decide)
  have n_xr2_f : xr2 ≠ f := by simpa [hr] using rne 2 5 (by decide) (by decide) (by decide)
  have n_xr2_g : xr2 ≠ g := by simpa [hr] using rne 2 6 (by decide) (by decide) (by decide)
  have n_xr2_O : xr2 ≠ O := by simpa [hr] using rne 2 7 (by decide) (by decide) (by decide)
  have n_xr2_D : xr2 ≠ D := by simpa [hr] using rne 2 8 (by decide) (by decide) (by decide)
  have n_xr2_H : xr2 ≠ H := by simpa [hr] using rne 2 9 (by decide) (by decide) (by decide)
  have n_y0_f : y0 ≠ f := by simpa [hr] using rne 3 5 (by decide) (by decide) (by decide)
  have n_y0_g : y0 ≠ g := by simpa [hr] using rne 3 6 (by decide) (by decide) (by decide)
  have n_y0_O : y0 ≠ O := by simpa [hr] using rne 3 7 (by decide) (by decide) (by decide)
  have n_y0_D : y0 ≠ D := by simpa [hr] using rne 3 8 (by decide) (by decide) (by decide)
  have n_y0_H : y0 ≠ H := by simpa [hr] using rne 3 9 (by decide) (by decide) (by decide)
  have n_c_f : c ≠ f := by simpa [hr] using rne 4 5 (by decide) (by decide) (by decide)
  have n_c_g : c ≠ g := by simpa [hr] using rne 4 6 (by decide) (by decide) (by decide)
  have n_c_O : c ≠ O := by simpa [hr] using rne 4 7 (by decide) (by decide) (by decide)
  have n_c_D : c ≠ D := by simpa [hr] using rne 4 8 (by decide) (by decide) (by decide)
  have n_c_H : c ≠ H := by simpa [hr] using rne 4 9 (by decide) (by decide) (by decide)
  have n_f_g : f ≠ g := by simpa [hr] using rne 5 6 (by decide) (by decide) (by decide)
  have n_f_O : f ≠ O := by simpa [hr] using rne 5 7 (by decide) (by decide) (by decide)
  have n_f_D : f ≠ D := by simpa [hr] using rne 5 8 (by decide) (by decide) (by decide)
  have n_f_H : f ≠ H := by simpa [hr] using rne 5 9 (by decide) (by decide) (by decide)
  have n_g_f : g ≠ f := by simpa [hr] using rne 6 5 (by decide) (by decide) (by decide)
  have n_g_O : g ≠ O := by simpa [hr] using rne 6 7 (by decide) (by decide) (by decide)
  have n_g_D : g ≠ D := by simpa [hr] using rne 6 8 (by decide) (by decide) (by decide)
  have n_g_H : g ≠ H := by simpa [hr] using rne 6 9 (by decide) (by decide) (by decide)
  have n_O_f : O ≠ f := by simpa [hr] using rne 7 5 (by decide) (by decide) (by decide)
  have n_O_g : O ≠ g := by simpa [hr] using rne 7 6 (by decide) (by decide) (by decide)
  have n_O_D : O ≠ D := by simpa [hr] using rne 7 8 (by decide) (by decide) (by decide)
  have n_O_H : O ≠ H := by simpa [hr] using rne 7 9 (by decide) (by decide) (by decide)
  have n_D_f : D ≠ f := by simpa [hr] using rne 8 5 (by decide) (by decide) (by decide)
  have n_D_g : D ≠ g := by simpa [hr] using rne 8 6 (by decide) (by decide) (by decide)
  have n_D_O : D ≠ O := by simpa [hr] using rne 8 7 (by decide) (by decide) (by decide)
  have n_D_H : D ≠ H := by simpa [hr] using rne 8 9 (by decide) (by decide) (by decide)
  have n_H_f : H ≠ f := by simpa [hr] using rne 9 5 (by decide) (by decide) (by decide)
  have n_H_g : H ≠ g := by simpa [hr] using rne 9 6 (by decide) (by decide) (by decide)
  have n_H_O : H ≠ O := by simpa [hr] using rne 9 7 (by decide) (by decide) (by decide)
  have n_H_D : H ≠ D := by simpa [hr] using rne 9 8 (by decide) (by decide) (by decide)
  have n_t1_f : t1 ≠ f := by simpa [hr] using rne 10 5 (by decide) (by decide) (by decide)
  have n_t1_g : t1 ≠ g := by simpa [hr] using rne 10 6 (by decide) (by decide) (by decide)
  have n_t1_O : t1 ≠ O := by simpa [hr] using rne 10 7 (by decide) (by decide) (by decide)
  have n_t1_D : t1 ≠ D := by simpa [hr] using rne 10 8 (by decide) (by decide) (by decide)
  have n_t1_H : t1 ≠ H := by simpa [hr] using rne 10 9 (by decide) (by decide) (by decide)
  have n_t2_f : t2 ≠ f := by simpa [hr] using rne 11 5 (by decide) (by decide) (by decide)
  have n_t2_g : t2 ≠ g := by simpa [hr] using rne 11 6 (by decide) (by decide) (by decide)
  have n_t2_O : t2 ≠ O := by simpa [hr] using rne 11 7 (by decide) (by decide) (by decide)
  have n_t2_D : t2 ≠ D := by simpa [hr] using rne 11 8 (by decide) (by decide) (by decide)
  have n_t2_H : t2 ≠ H := by simpa [hr] using rne 11 9 (by decide) (by decide) (by decide)
  have n_u_f : u ≠ f := by simpa [hr] using rne 12 5 (by decide) (by decide) (by decide)
  have n_u_g : u ≠ g := by simpa [hr] using rne 12 6 (by decide) (by decide) (by decide)
  have n_u_O : u ≠ O := by simpa [hr] using rne 12 7 (by decide) (by decide) (by decide)
  have n_u_D : u ≠ D := by simpa [hr] using rne 12 8 (by decide) (by decide) (by decide)
  have n_u_H : u ≠ H := by simpa [hr] using rne 12 9 (by decide) (by decide) (by decide)
  set vv : Nat := ofBits [s.basis h, s.basis xr1, s.basis xr2, s.basis y0, s.basis c] with hvv
  have hv32 : vv < 32 := by
    simp only [hvv, ofBits]
    cases s.basis h <;> cases s.basis xr1 <;> cases s.basis xr2 <;> cases s.basis y0 <;> cases s.basis c <;> simp
  have v0 : vv.testBit 0 = s.basis h := by rw [hvv, ofBits_testBit]; rfl
  have v1 : vv.testBit 1 = s.basis xr1 := by rw [hvv, ofBits_testBit]; rfl
  have v2 : vv.testBit 2 = s.basis xr2 := by rw [hvv, ofBits_testBit]; rfl
  have v3 : vv.testBit 3 = s.basis y0 := by rw [hvv, ofBits_testBit]; rfl
  have v4 : vv.testBit 4 = s.basis c := by rw [hvv, ofBits_testBit]; rfl
  have core := otail_core tr v yc y2c e ⟨vv, hv32⟩
  simp only [v0, v1, v2] at core
  set xS := tX tr tr.S (s.basis h) (s.basis xr1) (s.basis xr2) with hxS
  set xA := tX tr tr.A (s.basis h) (s.basis xr1) (s.basis xr2) with hxA
  set xB := tX tr tr.B (s.basis h) (s.basis xr1) (s.basis xr2) with hxB
  have hx : ∀ q (hq : q < 13), s.basis ((fun q : Fin 13 => r.getD q.val 0) ⟨q, hq⟩) =
      (oin xS xA xB yc y2c e vv).testBit q := by
    intro q hq
    simp only [oin, ofBits_testBit]
    interval_cases q <;> simp [hr, v0, v1, v2, v3, v4, pf, pt1, pt2, pu, pg, pO, pD, pH]
  have L := lift_local 13 _ inj (otail tr yc y2c e) (otail_support tr yc y2c e) s m _ hx core.1
  rw [core.2] at L
  have port : ∀ q (hq : q < 13), (run (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) m s).basis
      (r.getD q 0) = [vv.testBit 0, vv.testBit 1, vv.testBit 2, vv.testBit 3, vv.testBit 4, !xS,
        false, false, false, false, false, false, false].getD q false := by
    intro q hq
    have := L.2.1 q hq
    simp only [oout, ofBits_testBit] at this
    exact this
  apply State.extensionality
  · exact L.1
  · funext w
    show _ = otailEff tr xr1 xr2 f g O D H (s.basis h) s.basis w
    rw [otailEff_apply]
    by_cases wr : w ∈ r
    · obtain ⟨q, hq, hqw⟩ : ∃ q, q < 13 ∧ r.getD q 0 = w := by
        obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem wr
        exact ⟨i, by simpa [hr] using hi, by rw [List.getD_eq_getElem _ _ hi]; exact hiw⟩
      subst hqw
      rw [port q hq]
      interval_cases q <;> simp [hr, hxS, v0, v1, v2, v3, v4, pt1, pt2, pu, n_h_f, n_h_g, n_h_O, n_h_D, n_h_H, n_xr1_f, n_xr1_g, n_xr1_O, n_xr1_D, n_xr1_H, n_xr2_f, n_xr2_g, n_xr2_O, n_xr2_D, n_xr2_H, n_y0_f, n_y0_g, n_y0_O, n_y0_D, n_y0_H, n_c_f, n_c_g, n_c_O, n_c_D, n_c_H, n_f_g, n_f_O, n_f_D, n_f_H, n_g_f, n_g_O, n_g_D, n_g_H, n_O_f, n_O_g, n_O_D, n_O_H, n_D_f, n_D_g, n_D_O, n_D_H, n_H_f, n_H_g, n_H_O, n_H_D, n_t1_f, n_t1_g, n_t1_O, n_t1_D, n_t1_H, n_t2_f, n_t2_g, n_t2_O, n_t2_D, n_t2_H, n_u_f, n_u_g, n_u_O, n_u_D, n_u_H]
    · have nw : ∀ x ∈ r, w ≠ x := fun x hx heq => wr (heq ▸ hx)
      have hout : (run (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) m s).basis w = s.basis w :=
        L.2.2 w (fun q hq heq => wr (by
          rw [heq]
          show r.getD q 0 ∈ r
          rw [List.getD_eq_getElem _ _ (by simpa [hr] using hq)]
          exact List.getElem_mem _))
      rw [hout]
      simp [nw f (by simp [hr]), nw g (by simp [hr]), nw O (by simp [hr]), nw D (by simp [hr]),
        nw H (by simp [hr])]

/-! ### The zero chain with the output tail -/

theorem ochain_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire)
    (hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (c0 : Wire) (bs : List ZeroBit) (hcu : c0 ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u])
    (hnd : (c0 :: bs.flatMap ZeroBit.wires).Nodup)
    (hdis : ∀ b ∈ bs, b.input ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u])
    (s : State) (m : List Bool)
    (hs : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      (s.basis c0 && bs.all (fun b => !s.basis b.input)) s.basis)
    (hz : ∀ b ∈ bs, s.basis b.work = false) :
    run (zeroWith (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) c0 bs) m s =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H (s.basis c0 && bs.all (fun b => !s.basis b.input)) s.basis⟩ := by
  set used : List Wire := [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] with hu
  apply zeroWith_effect_runQ used (otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u)
    (otailEff tr xr1 xr2 f g O D H)
  · intro w hw uu st z
    have n : ∀ x ∈ used, x ≠ w := fun x hx heq => hw (heq ▸ hx)
    have p_xr1 : xr1 ≠ w := n xr1 (by simp [hu])
    have p_xr2 : xr2 ≠ w := n xr2 (by simp [hu])
    have p_y0 : y0 ≠ w := n y0 (by simp [hu])
    have p_c : c ≠ w := n c (by simp [hu])
    have p_f : f ≠ w := n f (by simp [hu])
    have p_g : g ≠ w := n g (by simp [hu])
    have p_O : O ≠ w := n O (by simp [hu])
    have p_D : D ≠ w := n D (by simp [hu])
    have p_H : H ≠ w := n H (by simp [hu])
    have p_t1 : t1 ≠ w := n t1 (by simp [hu])
    have p_t2 : t2 ≠ w := n t2 (by simp [hu])
    have p_u : u ≠ w := n u (by simp [hu])
    simp only [otailPre, writeBit, Function.update_apply, p_xr1, p_xr2, p_y0, p_c, p_f, p_g, p_O, p_D, p_H, p_t1, p_t2, p_u, if_false]
  · intro uu st w hw
    have n : ∀ x ∈ used, w ≠ x := fun x hx heq => hw (heq ▸ hx)
    rw [otailEff_apply]
    simp [n f (by simp [hu]), n g (by simp [hu]), n O (by simp [hu]), n D (by simp [hu]), n H (by simp [hu])]
  · intro uu st w z hw
    have n : ∀ x ∈ used, w ≠ x := fun x hx heq => hw (heq ▸ hx)
    have a1 : writeBit st w z xr1 = st xr1 := by
      simp [writeBit, Function.update, Ne.symm (n xr1 (by simp [hu]))]
    have a2 : writeBit st w z xr2 = st xr2 := by
      simp [writeBit, Function.update, Ne.symm (n xr2 (by simp [hu]))]
    funext q
    rw [otailEff_apply, a1, a2]
    by_cases hq : q = w
    · subst hq
      simp [writeBit, otailEff_apply, n f (by simp [hu]), n g (by simp [hu]), n O (by simp [hu]),
        n D (by simp [hu]), n H (by simp [hu])]
    · simp only [writeBit, Function.update_apply, hq, if_false]
      rw [otailEff_apply]
  · intro c' hc' st m' hp
    exact otail_run tr v yc y2c e c' xr1 xr2 y0 c f g O D H t1 t2 u (List.nodup_cons.mpr ⟨hc', hused⟩) st m' hp
  · exact hcu
  · exact hnd
  · exact hdis
  · exact hs
  · exact hz

/-! ### Remap, zero test with the output tail, undo -/

theorem oshape_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire)
    (w : Nat → Wire) (i0 : Nat) (it : List Nat) (work : List Wire)
    (hPn : ((i0 :: it).map w).Nodup) (x1P : xr1 ∉ (i0 :: it).map w) (x2P : xr2 ∉ (i0 :: it).map w)
    (hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextP : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w)
    (hwl : (it.map w).length = work.length) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u])
    (s : State) (m : List Bool)
    (hz : ∀ q ∈ work, s.basis q = false)
    (hp : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis) :
    run (tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it))))) m s =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H
        ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis⟩ := by
  have hlw : (i0 :: it).map w = w i0 :: it.map w := rfl
  have p0l : w i0 ∈ (i0 :: it).map w := by simp
  have usedNotP : ∀ q ∈ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | hq
    · exact x1P
    · exact x2P
    · exact hextP q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
  have itNe : ∀ i ∈ it, w i ≠ w i0 := by
    intro i hi heq
    rw [hlw] at hPn
    exact (List.nodup_cons.mp hPn).1 (heq ▸ List.mem_map_of_mem hi)
  -- step 1: remap
  have R1 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P m s
  rw [LocalWireModel.run_concat, remapList_mc, List.drop_zero, LocalWireModel.run_concat]
  generalize hs1 : run (tr.remapList xr1 xr2 w (i0 :: it)) m s = s1 at R1 ⊢
  -- step 2: X p0
  have e2 : run [Instr.X (w i0)] m s1 = ⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ := by
    simp [run]
  rw [e2]
  generalize hs2 : (⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ : State) = s2
  have s2ph : s2.phase = s.phase := by rw [← hs2]; exact R1.1
  have s2out : ∀ q, q ∉ (i0 :: it).map w → s2.basis q = s.basis q := by
    intro q hq
    have hq0 : q ≠ w i0 := fun heq => hq (heq ▸ p0l)
    rw [← hs2]; simp [writeBit, Function.update, hq0, R1.2.1 q hq]
  have s2p0 : s2.basis (w i0) = (s.basis (w i0) == tr.tgt i0 (s.basis xr1, s.basis xr2)) := by
    rw [← hs2]; simp only [writeBit, Function.update_self]
    rw [R1.2.2 i0 (by simp)]
    cases s.basis (w i0) <;> cases tr.tgt i0 (s.basis xr1, s.basis xr2) <;> rfl
  have s2it : ∀ i ∈ it, s2.basis (w i) = (s.basis (w i) ^^ tr.tgt i (s.basis xr1, s.basis xr2)) := by
    intro i hi
    rw [← hs2]; simp only [writeBit]
    rw [Function.update_of_ne (itNe i hi), R1.2.2 i (by simp [hi])]
  have k1 : s2.basis xr1 = s.basis xr1 := s2out xr1 x1P
  have k2 : s2.basis xr2 = s.basis xr2 := s2out xr2 x2P
  -- the zero-test value equals the match bit
  have zp := zeroPorts_maps (it.map w) work hwl
  have huV : (s2.basis (w i0) && (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input)) =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    have hall : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
        it.all (fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
      have : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
          ((zeroPorts (it.map w) work).map ZeroBit.input).all (fun q => !s2.basis q) := by
        rw [List.all_map]; rfl
      rw [this, zp.1, List.all_map, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      apply forall₂_congr
      intro i hi
      simp only [Function.comp_apply, s2it i hi]
      cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> simp
    rw [hall, s2p0]
    simp [List.all_cons]
  -- step 3: the zero-test chain with the output tail
  have hcu : w i0 ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := fun h => usedNotP _ h p0l
  have hperm := zeroPorts_perm (it.map w) work hwl
  have hnd : (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_append.mp (hperm.mem_iff.mp hm) with h | h
      · obtain ⟨i, hi, heq⟩ := List.mem_map.mp h
        exact itNe i hi heq
      · exact (hdisj _ h).1 p0l
    · apply hperm.symm.nodup_iff.mp
      apply List.nodup_append.mpr
      refine ⟨(List.nodup_cons.mp (hlw ▸ hPn)).2, hwn, ?_⟩
      intro a ha b hb heq
      subst heq
      exact (hdisj a hb).1 (by rw [hlw]; exact List.mem_cons_of_mem _ ha)
  have hdis' : ∀ b ∈ zeroPorts (it.map w) work, b.input ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
    intro b hb
    have hin : b.input ∈ it.map w := by
      have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    exact ⟨fun h => usedNotP _ h (by rw [hlw]; exact List.mem_cons_of_mem _ hin), (hdisj _ hwk).2⟩
  unfold otailPre at hp
  obtain ⟨pf, pt1, pt2, pu, pg, pO, pD, pH⟩ := hp
  have qq : ∀ x ∈ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u], s2.basis x = s.basis x :=
    fun x hx => s2out x (usedNotP x hx)
  have hs3 : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      (s2.basis (w i0) && (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input)) s2.basis := by
    rw [huV]
    unfold otailPre
    rw [qq f (by simp), qq t1 (by simp), qq t2 (by simp), qq u (by simp), qq g (by simp), qq c (by simp),
      qq O (by simp), qq D (by simp), qq H (by simp), qq y0 (by simp), k1, k2]
    exact ⟨pf, pt1, pt2, pu, pg, pO, pD, pH⟩
  have hz3 : ∀ b ∈ zeroPorts (it.map w) work, s2.basis b.work = false := by
    intro b hb
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    rw [s2out _ (hdisj _ hwk).1]; exact hz _ hwk
  rw [LocalWireModel.run_concat, ochain_run tr v yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u hused (w i0) _ hcu hnd
    hdis' s2 _ hs3 hz3, huV, LocalWireModel.run_concat]
  set V := (i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2) with hV
  set T3 := otailEff tr xr1 xr2 f g O D H V s2.basis with hT3
  have e4 : ∀ mm, run [Instr.X (w i0)] mm ⟨s2.phase, T3⟩ = ⟨s2.phase, writeBit T3 (w i0) (!T3 (w i0))⟩ := by
    intro mm; simp [run]
  rw [e4]
  generalize hs4 : (⟨s2.phase, writeBit T3 (w i0) (!T3 (w i0))⟩ : State) = s4
  have T3out : ∀ q, q ∉ (i0 :: it).map w → T3 q = otailEff tr xr1 xr2 f g O D H V s.basis q := by
    intro q hq
    rw [hT3, otailEff_apply, otailEff_apply, k1, k2, s2out q hq]
  have T3in : ∀ q, q ≠ f → q ≠ g → q ≠ O → q ≠ D → q ≠ H → T3 q = s2.basis q := by
    intro q h1 h2 h3 h4 h5
    rw [hT3, otailEff_apply]
    simp [h1, h2, h3, h4, h5]
  have u_xr1_f : xr1 ≠ f := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_g : xr1 ≠ g := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_O : xr1 ≠ O := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_D : xr1 ≠ D := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_H : xr1 ≠ H := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_f : xr2 ≠ f := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_g : xr2 ≠ g := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_O : xr2 ≠ O := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_D : xr2 ≠ D := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_H : xr2 ≠ H := fun heq => by rw [heq] at hused; simp at hused
  have s4x1 : s4.basis xr1 = s.basis xr1 := by
    rw [← hs4]; simp only [writeBit]
    rw [Function.update_of_ne (fun heq => hcu (by simp [heq])), T3in xr1 u_xr1_f u_xr1_g u_xr1_O u_xr1_D u_xr1_H, k1]
  have s4x2 : s4.basis xr2 = s.basis xr2 := by
    rw [← hs4]; simp only [writeBit]
    rw [Function.update_of_ne (fun heq => hcu (by simp [heq])), T3in xr2 u_xr2_f u_xr2_g u_xr2_O u_xr2_D u_xr2_H, k2]
  -- step 5: remap again
  suffices key : ∀ mm, run (tr.remapList xr1 xr2 w (i0 :: it)) mm s4 =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H V s.basis⟩ from key _
  intro mm
  have R5 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P mm s4
  apply State.extensionality
  · rw [R5.1, ← hs4]; exact s2ph
  · funext q
    by_cases hq : q ∈ (i0 :: it).map w
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      rw [R5.2.2 i hi, s4x1, s4x2]
      have nf : w i ≠ f := fun heq => usedNotP f (by simp) (heq ▸ hq)
      have ng : w i ≠ g := fun heq => usedNotP g (by simp) (heq ▸ hq)
      have nO : w i ≠ O := fun heq => usedNotP O (by simp) (heq ▸ hq)
      have nD : w i ≠ D := fun heq => usedNotP D (by simp) (heq ▸ hq)
      have nH : w i ≠ H := fun heq => usedNotP H (by simp) (heq ▸ hq)
      have rhs : otailEff tr xr1 xr2 f g O D H V s.basis (w i) = s.basis (w i) := by
        rw [otailEff_apply]; simp [nf, ng, nO, nD, nH]
      change (s4.basis (w i) ^^ _) = otailEff tr xr1 xr2 f g O D H V s.basis (w i)
      rw [rhs]
      rw [← hs4]; simp only [writeBit]
      rcases List.mem_cons.mp hi with rfl | hit
      · rw [Function.update_self, T3in _ nf ng nO nD nH, s2p0]
        cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> rfl
      · rw [Function.update_of_ne (itNe i hit), T3in _ nf ng nO nD nH, s2it i hit]
        cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> rfl
    · rw [R5.2.1 q hq, ← hs4]
      change writeBit T3 (w i0) (!T3 (w i0)) q = otailEff tr xr1 xr2 f g O D H V s.basis q
      simp only [writeBit]
      rw [Function.update_of_ne (fun heq : q = w i0 => hq (heq ▸ p0l)), T3out q hq]

/-! ### The output classifier -/

/-- The output classifier's match bit for constant `K`: the zero test and `K`'s pivot pattern. -/
def oX (tr : Tri) (K : Nat) (xs : List Wire) (st : BasisState) : Bool :=
  matchBit tr xs st && decide ((st (xs.getD tr.r1 0), st (xs.getD tr.r2 0)) = tr.pat K)

theorem oclassifier_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire)
    (hxs : xs.Nodup) (hlen : xs.length = 256) (hwl : work.length = 253) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ xs ∧ q ∉ work)
    (s : State) (m : List Bool)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis f = false ∧ s.basis t1 = false ∧
      s.basis t2 = false ∧ s.basis u = false)
    (hfl : s.basis g = (s.basis c && oX tr tr.S xs s.basis) ∧
      s.basis O = (s.basis c && oX tr tr.A xs s.basis && (s.basis y0 == yc)) ∧
      s.basis D = (s.basis c && oX tr tr.B xs s.basis && (s.basis y0 == y2c)) ∧
      s.basis H = (e && s.basis c && oX tr tr.A xs s.basis && (s.basis y0 != yc))) :
    run (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) m s =
      ⟨s.phase, writeBit (writeBit (writeBit (writeBit (writeBit s.basis f (!oX tr tr.S xs s.basis))
        g false) O false) D false) H false⟩ := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  set w : Nat → Wire := fun i => xs.getD i 0 with hw
  set xr1 := w tr.r1 with hx1
  set xr2 := w tr.r2 with hx2
  set P := tr.idx.map w with hP
  have winj : ∀ i j, i < 256 → j < 256 → w i = w j → i = j := by
    intro i j hi hj heq
    simp only [hw] at heq
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at heq
    exact hxs.getElem_inj_iff.mp heq
  have wmem : ∀ i, i < 256 → w i ∈ xs := by
    intro i hi; simp only [hw]; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hPn : P.Nodup := by
    apply List.Nodup.map_on _ ix.1
    intro i hi j hj heq; exact winj i j (ix.2.2.2.2 i hi) (ix.2.2.2.2 j hj) heq
  have memP : ∀ q, q ∈ P ↔ ∃ i ∈ tr.idx, w i = q := by intro q; simp [hP]
  have x1P : xr1 ∉ P := by
    rw [memP]; rintro ⟨i, hi, heq⟩
    exact ix.2.2.1 (winj i tr.r1 (ix.2.2.2.2 i hi) pv.1 heq ▸ hi)
  have x2P : xr2 ∉ P := by
    rw [memP]; rintro ⟨i, hi, heq⟩
    exact ix.2.2.2.1 (winj i tr.r2 (ix.2.2.2.2 i hi) pv.2.1 heq ▸ hi)
  have x12 : xr1 ≠ xr2 := fun heq => pv.2.2.1 (winj _ _ pv.1 pv.2.1 heq)
  have Psub : ∀ q ∈ P, q ∈ xs := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := (memP q).mp hq; exact wmem i (ix.2.2.2.2 i hi)
  have hPl : P.length = 254 := by simp [hP, ix.2.1]
  obtain ⟨i0, it, hidx⟩ : ∃ i0 it, tr.idx = i0 :: it := by
    have hl := ix.2.1
    cases h : tr.idx with
    | nil => rw [h] at hl; simp at hl
    | cons a l => exact ⟨a, l, rfl⟩
  have hP0 : P = w i0 :: it.map w := by simp [hP, hidx]
  have hitl : (it.map w).length = 253 := by
    have := hPl; rw [hP0] at this; simpa using this
  have extx (q : Wire) (hq : q ∈ [y0, c, f, g, O, D, H, t1, t2, u]) :
      q ∉ P ∧ q ∉ work ∧ q ≠ xr1 ∧ q ≠ xr2 := by
    have h := hextx q hq
    exact ⟨fun hp => h.1 (Psub q hp), h.2, fun heq => h.1 (heq ▸ wmem _ pv.1),
      fun heq => h.1 (heq ▸ wmem _ pv.2.1)⟩
  have hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hext⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨x12, ?_⟩
      have := fun q hq => (extx q hq).2.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      exact ⟨fun heq => this y0 (Or.inl rfl) heq.symm, fun heq => this c (by tauto) heq.symm,
        fun heq => this f (by tauto) heq.symm, fun heq => this g (by tauto) heq.symm,
        fun heq => this O (by tauto) heq.symm, fun heq => this D (by tauto) heq.symm,
        fun heq => this H (by tauto) heq.symm, fun heq => this t1 (by tauto) heq.symm,
        fun heq => this t2 (by tauto) heq.symm, fun heq => this u (by tauto) heq.symm⟩
    · intro hm
      exact (extx xr2 hm).2.2.2 rfl
  have hlP : (i0 :: it).map w = P := by rw [hP0]; rfl
  have hPn' : ((i0 :: it).map w).Nodup := by rw [hlP]; exact hPn
  have x1P' : xr1 ∉ (i0 :: it).map w := by rw [hlP]; exact x1P
  have x2P' : xr2 ∉ (i0 :: it).map w := by rw [hlP]; exact x2P
  have hextP : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w := by
    intro q hq; rw [hlP]; exact (extx q hq).1
  have hdisj' : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
    intro q hq
    refine ⟨fun hm => hdisj q hq (Psub q (by rw [← hlP]; exact hm)), ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (heq | heq | heq)
    · exact hdisj q hq (heq ▸ wmem _ pv.1)
    · exact hdisj q hq (heq ▸ wmem _ pv.2.1)
    · exact (hextx q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)).2 hq
  have hmb : matchBit tr xs s.basis =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    simp only [matchBit, hidx]; rfl
  have hoX : ∀ K, oX tr K xs s.basis = tX tr K
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2))
      (s.basis xr1) (s.basis xr2) := by
    intro K; simp only [oX, tX, ← hmb]; rfl
  have hp : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis := by
    unfold otailPre
    rw [← hoX, ← hoX, ← hoX]
    exact ⟨hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2, hfl.1, hfl.2.1, hfl.2.2.1, hfl.2.2.2⟩
  have run_eq := oshape_run tr v yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u w i0 it work hPn' x1P' x2P' hused
    hextP (by rw [hitl, hwl]) hwn hdisj' s m hz.1 hp
  have hprog : oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [oclassifier, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  rw [hprog, run_eq]
  unfold otailEff
  rw [← hoX]

/-! ### Counts, slots, support and physical gates of the output classifier -/

theorem oclassifier_counts (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hwl : work.length = 253) :
    toffoliCount (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) = 258 ∧
    measurementCount (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) = 253 + (if e then 9 else 8) := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have zc := zeroWith_counts_general
    (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u) 5 (if e then 9 else 8)
    (fun h => otailL_counts tr yc y2c e _ _ y0 c f g O D H t1 t2 u h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zc
  have rt := remapList_tc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  have rm := remapList_mc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  unfold oclassifier
  simp only [toffoliCount_append, measurementCount_append, rt, rm, zc.1, zc.2]
  exact ⟨by simp [toffoliCount], by simp [measurementCount]⟩

/-- 3 slots a remapped bit twice, the two flips, 7 a chain rung, and the 45-slot worst output tail. -/
theorem oclassifier_slots (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hwl : work.length = 253) :
    gateSlots (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) ≤ 3342 := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have ix := Tri.idx_facts v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have zs := zeroWith_slots (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
    (gateSlots (otail tr yc y2c e)) (fun h => otailL_slots tr yc y2c e _ _ y0 c f g O D H t1 t2 u h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zs
  have rs := remapList_slots tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  rw [ix.2.1] at rs
  have ds := otail_slots tr yc y2c e
  unfold oclassifier
  simp only [gateSlots_app, zs]
  simp only [gateSlots, instructionSlots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at rs ds ⊢
  omega

theorem oclassifier_support (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hxl : xs.length = 256) (hwl : work.length = 253) :
    wires (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) ⊆
      xs.toFinset ∪ work.toFinset ∪ {y0, c, f, g, O, D, H, t1, t2, u} := by
  have _ := hwl
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  let U : Finset Wire := xs.toFinset ∪ work.toFinset ∪ {y0, c, f, g, O, D, H, t1, t2, u}
  have xsU : ∀ i, i < 256 → xs.getD i 0 ∈ U := by
    intro i hi
    have hm : xs.getD i 0 ∈ xs := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    simp only [U, Finset.mem_union, List.mem_toFinset]
    exact Or.inl (Or.inl hm)
  have workU : ∀ q ∈ work, q ∈ U := fun q hq => by simp [U, hq]
  have r1U := xsU _ pv.1
  have r2U := xsU _ pv.2.1
  have idxU : ∀ i ∈ tr.idx, xs.getD i 0 ∈ U := fun i hi => xsU i (ix.2.2.2.2 i hi)
  have PU : ∀ q ∈ tr.idx.map (fun i => xs.getD i 0), q ∈ U := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; exact idxU i hi
  have h0U : (tr.idx.map (fun i => xs.getD i 0)).headD 0 ∈ U := by
    rw [hidx]; exact idxU i0 (by rw [hidx]; simp)
  have portsU : ∀ b ∈ zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work,
      b.input ∈ U ∧ b.work ∈ U := by
    intro b hb
    have hm := zeroPorts_mem _ _ b hb
    exact ⟨PU _ (List.mem_of_mem_tail hm.1), workU _ hm.2⟩
  have extU : ∀ q ∈ ({y0, c, f, g, O, D, H, t1, t2, u} : Finset Wire), q ∈ U := by
    intro q hq; simp only [U, Finset.mem_union]; exact Or.inr hq
  have tailU : ∀ h ∈ U,
      wires (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u h) ⊆ U := by
    intro h hh
    refine (otailL_support tr yc y2c e _ _ y0 c f g O D H t1 t2 u h).trans ?_
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hh, r1U, r2U, extU y0 (by simp), extU c (by simp), extU f (by simp), extU g (by simp),
      extU O (by simp), extU D (by simp), extU H (by simp), extU t1 (by simp), extU t2 (by simp),
      extU u (by simp)⟩
  have remapU := remapList_sub tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx U
    r1U r2U idxU
  have zU := zeroWith_sub _ U tailU _ _ h0U portsU
  have xU : wires [Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ⊆ U := by
    generalize (tr.idx.map (fun i => xs.getD i 0)).headD 0 = h0 at h0U ⊢
    intro q hq
    simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_singleton] at hq
    rcases hq with rfl | hq
    · exact h0U
    · simp at hq
  intro q hq
  simp only [oclassifier, wires_append, Finset.mem_union] at hq
  rcases hq with h | h | h | h | h
  · exact remapU h
  · exact xU h
  · exact zU h
  · exact xU h
  · exact remapU h

theorem oclassifier_physical (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hxl : xs.length = 256) (hwl : work.length = 253)
    (hxn : xs.Nodup) (hwn : work.Nodup) (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ xs ∧ q ∉ work) :
    GatePhysical (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have winj : ∀ i j, i < 256 → j < 256 → xs.getD i 0 = xs.getD j 0 → i = j := by
    intro i j hi hj heq
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at heq
    exact hxn.getElem_inj_iff.mp heq
  have wmem : ∀ i, i < 256 → xs.getD i 0 ∈ xs := by
    intro i hi; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hi0 : i0 ∈ tr.idx := by rw [hidx]; simp
  have i0lt := ix.2.2.2.2 i0 hi0
  have i0r1 : i0 ≠ tr.r1 := fun heq => ix.2.2.1 (heq ▸ hi0)
  have i0r2 : i0 ≠ tr.r2 := fun heq => ix.2.2.2.1 (heq ▸ hi0)
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have remapP : GatePhysical (tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx) := by
    apply remapList_physical
    intro i hi
    have hi256 := ix.2.2.2.2 i hi
    refine ⟨fun heq => ix.2.2.1 ((winj _ _ pv.1 hi256 heq) ▸ hi), fun heq => ix.2.2.2.1 ((winj _ _ pv.2.1 hi256 heq) ▸ hi)⟩
  have hP0 : (tr.idx.map (fun i => xs.getD i 0)).headD 0 = xs.getD i0 0 := by rw [hidx]; rfl
  have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by rw [hidx]; rfl
  have x0x : xs.getD i0 0 ∈ xs := wmem i0 i0lt
  have ex : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], ∀ a ∈ xs, a ≠ q :=
    fun q hq a ha heq => (hextx q hq).1 (heq ▸ ha)
  have ew : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], ∀ a ∈ work, a ≠ q :=
    fun q hq a ha heq => (hextx q hq).2 (heq ▸ ha)
  -- any chain wire (the control `xs[i0]` or a pool wire) together with the tail's other twelve wires is nodup
  have hlist : ∀ h, (h = xs.getD i0 0 ∨ h ∈ work) →
      [h, xs.getD tr.r1 0, xs.getD tr.r2 0, y0, c, f, g, O, D, H, t1, t2, u].Nodup := by
    intro h hh
    have hx1 := wmem _ pv.1
    have hx2 := wmem _ pv.2.1
    have hxx : xs.getD tr.r1 0 ≠ xs.getD tr.r2 0 := fun heq => pv.2.2.1 (winj _ _ pv.1 pv.2.1 heq)
    have hh1 : h ≠ xs.getD tr.r1 0 := by
      rcases hh with rfl | hw
      · exact fun heq => i0r1 (winj _ _ i0lt pv.1 heq)
      · exact fun heq => hdisj h hw (heq ▸ hx1)
    have hh2 : h ≠ xs.getD tr.r2 0 := by
      rcases hh with rfl | hw
      · exact fun heq => i0r2 (winj _ _ i0lt pv.2.1 heq)
      · exact fun heq => hdisj h hw (heq ▸ hx2)
    have hhe : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], h ≠ q := by
      intro q hq
      rcases hh with rfl | hw
      · exact ex q hq _ x0x
      · exact ew q hq _ hw
    have r1e : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], xs.getD tr.r1 0 ≠ q := fun q hq => ex q hq _ hx1
    have r2e : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], xs.getD tr.r2 0 ≠ q := fun q hq => ex q hq _ hx2
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hhe r1e r2e
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨hh1, hh2, hhe⟩, ⟨hxx, r1e⟩, r2e, ?_⟩
    simpa using hext
  have zP : GatePhysical (zeroWith (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)) := by
    rw [hP0, hPt]
    apply zeroWith_physical
    · rw [zp.2]
      exact List.nodup_cons.mpr ⟨fun hm => hdisj _ hm x0x, hwn⟩
    · intro b hb heq
      have hm := zeroPorts_mem _ _ b hb
      obtain ⟨i, hi, hie⟩ := List.mem_map.mp hm.1
      have hit : i ∈ tr.idx := by rw [hidx]; simp [hi]
      exact hdisj _ hm.2 (heq ▸ hie ▸ wmem i (ix.2.2.2.2 i hit))
    · intro h hh
      rw [zp.2] at hh
      apply otailL_physical
      exact hlist h (by simpa using hh)
  have xP : GatePhysical [Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] := by
    simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]
  unfold oclassifier
  simp only [gatePhysical_append]
  exact ⟨remapP, xP, zP, xP, remapP⟩

end OutTail

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section GenBlock
open Secp256k1 ControlledPointLayout
attribute [local irreducible] wires

theorem pull_pull (f : Wire → Wire) (hf : ∀ q, f (f q) = q) (s : State) :
    pullState f (pullState f s) = s := by
  apply State.extensionality
  · rfl
  · funext q; simp only [pullState, hf]

theorem pull_fixed (f : Wire → Wire) (s : State) (h : ∀ q, s.basis (f q) = s.basis q) :
    pullState f s = s := by
  apply State.extensionality
  · rfl
  · funext q; exact h q

/-- A program relabelled by an involution runs as the original on the pulled state, pulled back. -/
theorem run_rename_invol (f : Wire → Wire) (hf : ∀ q, f (f q) = q) (P : Program) (m : List Bool)
    (s : State) : run (renameProgram f P) m s = pullState f (run P m (pullState f s)) := by
  have hinj : Function.Injective f := fun a b h => by rw [← hf a, ← hf b, h]
  have h := ECDSAAdd.run_rename f hinj P m s
  rw [← h, pull_pull f hf]

/-- Relabelling by an involution is invisible when the state before and after is symmetric. -/
theorem run_rename_noop (f : Wire → Wire) (hf : ∀ q, f (f q) = q) (P : Program) (m : List Bool)
    (s : State) (hs : ∀ q, s.basis (f q) = s.basis q)
    (hr : ∀ q, (run P m s).basis (f q) = (run P m s).basis q) :
    run (renameProgram f P) m s = run P m s := by
  rw [run_rename_invol f hf, pull_fixed f s hs, pull_fixed f _ hr]

/-- A swap of two wires holding equal bits leaves the state unchanged. -/
theorem swap_sym (a b : Wire) (sw : Wire → Wire)
    (hsw : ∀ q, sw q = if q = a then b else if q = b then a else q) (st : BasisState)
    (h : st a = st b) : ∀ q, st (sw q) = st q := by
  intro q
  rw [hsw q]
  by_cases ha : q = a
  · subst ha; simp [h]
  · by_cases hb : q = b
    · subst hb; simp [ha, h]
    · simp [ha, hb]

theorem flags_not_point (q : Wire) (hq : q ∈ layout.inPlaceFlags) :
    q ∉ layout.point.x ++ layout.point.y := by
  have hD := layout.dialogUsed_nodup layout_nodup
  intro hp
  have c := List.nodup_iff_count_le_one.mp hD q
  have c1 : 1 ≤ layout.inPlaceFlags.count q := List.count_pos_iff.mpr hq
  have c2 : 1 ≤ (layout.point.x ++ layout.point.y).count q := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.dialogUsedWires, PointAddLayout.pointWires, List.count_append,
    List.count_cons] at c c2
  split_ifs at c <;> omega

theorem pool_not_point (q : Wire) (hq : q ∈ layout.dialogPool) :
    q ∉ layout.point.x ++ layout.point.y := by
  have hD := layout.dialogUsed_nodup layout_nodup
  intro hp
  have c := List.nodup_iff_count_le_one.mp hD q
  have c1 : 1 ≤ layout.dialogPool.count q := List.count_pos_iff.mpr hq
  have c2 : 1 ≤ (layout.point.x ++ layout.point.y).count q := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.dialogUsedWires, PointAddLayout.pointWires, List.count_append,
    List.count_cons] at c c2
  split_ifs at c <;> omega

theorem pool_not_flag (q : Wire) (hq : q ∈ layout.dialogPool) : q ∉ layout.inPlaceFlags := by
  have hD := layout.dialogUsed_nodup layout_nodup
  intro hp
  have c := List.nodup_iff_count_le_one.mp hD q
  have c1 : 1 ≤ layout.dialogPool.count q := List.count_pos_iff.mpr hq
  have c2 : 1 ≤ layout.inPlaceFlags.count q := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.dialogUsedWires, List.count_append] at c
  omega

theorem finite_not_flag : layout.point.finite ∉ layout.inPlaceFlags ∧
    layout.point.finite ∉ layout.point.x ++ layout.point.y := by
  have hD := layout.dialogUsed_nodup layout_nodup
  have c := List.nodup_iff_count_le_one.mp hD layout.point.finite
  simp only [ControlledPointLayout.dialogUsedWires, PointAddLayout.pointWires, List.count_append,
    List.count_cons, beq_self_eq_true, if_true] at c
  constructor
  · intro hp; have := List.count_pos_iff.mpr hp; omega
  · intro hp; have := List.count_pos_iff.mpr hp
    simp only [List.count_append] at this; omega

section GenRun
attribute [local irreducible] run ReflectionE1TickGapLow48.generic

/-- The relabelled generic block on a sentinel-coded state: only the coordinates move. -/
theorem gen_block_run {cx cy : Fp} (X Y X' Y' : Fp) (G : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues layout X Y G base')
      (ReflectionE1TickGapLow48.generic layout cx cy) (PointDialogValues layout X' Y' G base'))
    (t : State) (m : List Bool)
    (hx : regValue layout.point.x t.basis = X.val) (hy : regValue layout.point.y t.basis = Y.val)
    (hf : t.basis layout.point.finite = false) (hg : t.basis layout.genericSelect = G)
    (hE : t.basis layout.core.equalNegY = false)
    (hD : t.basis layout.doubleSelect = false) (hclean : regValue layout.dialogPool t.basis = 0) :
    (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (ReflectionE1TickGapLow48.generic layout cx cy)))))) m t).phase = t.phase ∧
    regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (ReflectionE1TickGapLow48.generic layout cx cy)))))) m t).basis = X'.val ∧
    regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (ReflectionE1TickGapLow48.generic layout cx cy)))))) m t).basis = Y'.val ∧
    ∀ q, q ∉ layout.point.x ++ layout.point.y →
      (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
          (ReflectionE1TickGapLow48.generic layout cx cy)))))) m t).basis q = t.basis q := by
  have hw := layout_widths
  have hn := layout_nodup
  have tinv := tauM_invol layout hn
  have einv := swapE_invol layout hw hn
  have dinv := swapD_invol layout hw hn
  have uinv : ∀ q, Wrapper5.U layout (Wrapper5.U layout q) = q := fun q => Equiv.swap_apply_self _ _ _
  have gflag : layout.core.generic ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have sflag : layout.genericSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have eflag : layout.core.equalNegY ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have dflag : layout.doubleSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have tauM_def : ∀ q, tauM layout q =
      if q = layout.core.generic then layout.genericSelect else
        if q = layout.genericSelect then layout.core.generic else q := fun q => rfl
  -- tauM fixes everything off the two generic flags
  have tfix : ∀ q, q ≠ layout.core.generic → q ≠ layout.genericSelect → tauM layout q = q := by
    intro q h1 h2; rw [tauM_def q, if_neg h1, if_neg h2]
  have pclean : ∀ q ∈ layout.dialogPool, t.basis q = false :=
    fun q hq => (regValue_zero _ _).mp hclean q hq
  have pne (q : Wire) (hq : q ∈ layout.dialogPool) : q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => pool_not_flag q hq (e ▸ gflag), fun e => pool_not_flag q hq (e ▸ sflag)⟩
  have xyne (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => flags_not_point _ gflag (e ▸ hq), fun e => flags_not_point _ sflag (e ▸ hq)⟩
  have fne : layout.point.finite ≠ layout.core.generic ∧ layout.point.finite ≠ layout.genericSelect :=
    ⟨fun e => finite_not_flag.1 (e ▸ gflag), fun e => finite_not_flag.1 (e ▸ sflag)⟩
  -- the generic block in its own frame
  generalize ht' : pullState (tauM layout) t = t'
  have t'def : ∀ q, t'.basis q = t.basis (tauM layout q) := by intro q; rw [← ht']; rfl
  have t'x : ∀ q ∈ layout.point.x ++ layout.point.y, t'.basis q = t.basis q := by
    intro q hq; rw [t'def, tfix q (xyne q hq).1 (xyne q hq).2]
  have v : PointDialogValues layout X Y G t'.basis t'.basis := by
    refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl⟩
    · rw [← hx]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_left _ hq)
    · rw [← hy]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_right _ hq)
    · rw [t'def, tauM_def, if_pos rfl]; exact hg
    · apply (regValue_zero _ _).mpr
      intro q hq
      rw [t'def, tfix q (pne q hq).1 (pne q hq).2]; exact pclean q hq
  have hb : t'.basis layout.point.finite = false := by
    rw [t'def, tfix _ fne.1 fne.2]; exact hf
  obtain ⟨ph0, v0⟩ := swapF_values layout hw hn (ReflectionE1TickGapLow48.generic layout cx cy)
    X Y X' Y' G t'.basis hP hb t' m v
  generalize hR0 : run (renameProgram (swapF layout) (ReflectionE1TickGapLow48.generic layout cx cy)) m t' = R0
    at ph0 v0
  have R0clean : ∀ q ∈ layout.dialogPool, R0.basis q = false :=
    fun q hq => (regValue_zero _ _).mp v0.clean q hq
  -- U swaps two clean pool sites
  have u684 := Square5Placement.pool_member layout hw 684 (by omega)
  have u717 := Square5Placement.pool_member layout hw 717 (by omega)
  have U_def : ∀ q, Wrapper5.U layout q = if q = layout.core.poolWire 684 then layout.core.poolWire 717
      else if q = layout.core.poolWire 717 then layout.core.poolWire 684 else q := by
    intro q
    show (Equiv.swap _ _) q = _
    rw [Equiv.swap_apply_def]
  have R1 : run (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      (ReflectionE1TickGapLow48.generic layout cx cy))) m t' = R0 := by
    rw [run_rename_noop _ uinv]
    · exact hR0
    · apply swap_sym _ _ _ U_def
      have a : t'.basis (layout.core.poolWire 684) = false := by
        rw [t'def, tfix _ (pne _ u684).1 (pne _ u684).2]; exact pclean _ u684
      have b : t'.basis (layout.core.poolWire 717) = false := by
        rw [t'def, tfix _ (pne _ u717).1 (pne _ u717).2]; exact pclean _ u717
      rw [a, b]
    · rw [hR0]
      apply swap_sym _ _ _ U_def
      rw [R0clean _ u684, R0clean _ u717]
  -- tauM is the real swap between the generic flag and the generic select
  have R2 : run (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      (ReflectionE1TickGapLow48.generic layout cx cy)))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_invol _ tinv, ht', R1]
  -- R0 off the point registers equals the pulled start
  have R0rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → R0.basis q = t'.basis q := v0.rest
  have tq_off : ∀ q, q ∉ layout.point.x ++ layout.point.y → tauM layout q ∉ layout.point.x ++ layout.point.y := by
    intro q hq
    rw [tauM_def]
    split_ifs
    · exact flags_not_point _ sflag
    · exact flags_not_point _ gflag
    · exact hq
  have R2rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → (pullState (tauM layout) R0).basis q = t.basis q := by
    intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, R0rest _ (tq_off q hq), t'def, tinv]
  -- swapE and swapD act on clean wires before and after
  have spE := spare_pool layout hw
  have spD := spareD_pool layout hw
  have E_def : ∀ q, swapE layout q = if q = layout.core.equalNegY then spareWire layout
      else if q = spareWire layout then layout.core.equalNegY else q := fun q => rfl
  have D_def : ∀ q, swapD layout q = if q = layout.doubleSelect then spareD layout
      else if q = spareD layout then layout.doubleSelect else q := fun q => rfl
  have R2E : (pullState (tauM layout) R0).basis layout.core.equalNegY = false := by
    rw [R2rest _ (flags_not_point _ eflag)]; exact hE
  have R2Es : (pullState (tauM layout) R0).basis (spareWire layout) = false := by
    rw [R2rest _ (pool_not_point _ spE)]; exact pclean _ spE
  have R2D : (pullState (tauM layout) R0).basis layout.doubleSelect = false := by
    rw [R2rest _ (flags_not_point _ dflag)]; exact hD
  have R2Ds : (pullState (tauM layout) R0).basis (spareD layout) = false := by
    rw [R2rest _ (pool_not_point _ spD)]; exact pclean _ spD
  have R3 : run (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (ReflectionE1TickGapLow48.generic layout cx cy))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ einv _ _ _ (swap_sym _ _ _ E_def _ (by rw [hE, pclean _ spE]))
      (by rw [R2]; exact swap_sym _ _ _ E_def _ (by rw [R2E, R2Es])), R2]
  have R4 : run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (ReflectionE1TickGapLow48.generic layout cx cy)))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ dinv _ _ _ (swap_sym _ _ _ D_def _ (by rw [hD, pclean _ spD]))
      (by rw [R3]; exact swap_sym _ _ _ D_def _ (by rw [R2D, R2Ds])), R3]
  rw [R4]
  refine ⟨?_, ?_, ?_, R2rest⟩
  · have e1 : (pullState (tauM layout) R0).phase = R0.phase := rfl
    rw [e1, ph0, ← ht']; rfl
  · rw [← v0.x]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_left _ hq)).1 (xyne q (List.mem_append_left _ hq)).2]
  · rw [← v0.y]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_right _ hq)).1 (xyne q (List.mem_append_right _ hq)).2]

end GenRun

end GenBlock

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

section PreDecode
open Secp256k1 ControlledPointLayout

theorem ofBits_bit : ∀ (l : List Bool) (q : Nat), (ofBits l).testBit q = l.getD q false
  | [], q => by simp [ofBits]
  | b :: bs, 0 => by
      simp only [ofBits, List.getD_cons_zero]
      cases b <;> simp [Nat.testBit_zero, Nat.add_mul_mod_self_left]
  | b :: bs, q + 1 => by
      simp only [ofBits, List.getD_cons_succ]
      rw [← ofBits_bit bs q, Nat.testBit_succ]
      congr 1
      cases b <;> simp <;> omega

/-- A safe local program on the ports `r` lifts to the layout. -/
theorem lift_list (n : Nat) (r : List Wire) (hl : r.length = n) (hnd : r.Nodup) (D : Program)
    (hD : wires D ⊆ Finset.range n) (s : State) (m : List Bool)
    (hsafe : safe D (regValue r s.basis) = true) :
    (run (renameProgram (LocalWireModel.label (fun q : Fin n => r.getD q.val 0)) D) m s).phase = s.phase ∧
    (∀ q (_ : q < n), (run (renameProgram (LocalWireModel.label (fun q : Fin n => r.getD q.val 0)) D) m s).basis
      (r.getD q 0) = (bitRun D (regValue r s.basis)).testBit q) ∧
    (∀ w, w ∉ r →
      (run (renameProgram (LocalWireModel.label (fun q : Fin n => r.getD q.val 0)) D) m s).basis w = s.basis w) := by
  have inj := LocalWireModel.listPorts_injective r hnd hl
  have hx : ∀ q (h : q < n), s.basis ((fun q : Fin n => r.getD q.val 0) ⟨q, h⟩) =
      (regValue r s.basis).testBit q := by
    intro q h
    exact (LocalWireModel.reg_bit r s.basis q (by omega)).symm
  have L := lift_local n _ inj D hD s m (regValue r s.basis) hx hsafe
  refine ⟨L.1, fun q hq => L.2.1 q hq, ?_⟩
  intro w hw
  apply L.2.2 w
  intro q hq e
  apply hw
  rw [e]
  show r.getD q 0 ∈ r
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

/-- Corner flags `(O, D, H, I)` from `n = c ∧ ¬G`, the pivot bits and `y0`. -/
def predFlags (tr : Tri) (yc n r1 r2 y0 : Bool) : Bool × Bool × Bool × Bool :=
  if tr.role1 then
    let pB := r1 == tr.B.testBit tr.r1
    let pS := !pB && (r2 == tr.S.testBit tr.r2)
    let yC := y0 == yc
    (n && pS, n && !pB && !pS && yC, n && pB, n && !pB && !pS && !yC)
  else
    let pS := r1 == tr.S.testBit tr.r1
    let pB := !pS && (r2 == tr.B.testBit tr.r2)
    let yC := y0 == yc
    (n && pS, n && !pS && !pB && yC, n && pB, n && !pS && !pB && !yC)

theorem predecT_support (tr : Tri) (yc : Bool) : wires (predecT tr yc) ⊆ Finset.range 8 := by
  unfold predecT
  split_ifs <;>
  · cases tr.B.testBit tr.r1 <;> cases tr.S.testBit tr.r2 <;> cases tr.S.testBit tr.r1 <;>
      cases tr.B.testBit tr.r2 <;> cases yc <;> decide

section PreRun
attribute [local irreducible] run wires
set_option maxHeartbeats 400000

theorem predecL_run (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire)
    (hnd : [g, c, xr1, xr2, y0, O, D, H].Nodup) (s : State) (m : List Bool)
    (hz : s.basis O = false ∧ s.basis D = false ∧ s.basis H = false) :
    run (predecL tr yc g c xr1 xr2 y0 O D H) m s =
      ⟨s.phase, writeBit (writeBit (writeBit (writeBit s.basis g
        (predFlags tr yc (s.basis g ^^ s.basis c) (s.basis xr1) (s.basis xr2) (s.basis y0)).2.2.2) O
        (predFlags tr yc (s.basis g ^^ s.basis c) (s.basis xr1) (s.basis xr2) (s.basis y0)).1) D
        (predFlags tr yc (s.basis g ^^ s.basis c) (s.basis xr1) (s.basis xr2) (s.basis y0)).2.1) H
        (predFlags tr yc (s.basis g ^^ s.basis c) (s.basis xr1) (s.basis xr2) (s.basis y0)).2.2.1⟩ := by
  generalize hpf : predFlags tr yc (s.basis g ^^ s.basis c) (s.basis xr1) (s.basis xr2) (s.basis y0) = pf
  have nd := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or] at nd
  unfold predecL
  set r : List Wire := [g, c, xr1, xr2, y0, O, D, H] with hr
  have hl : r.length = 8 := rfl
  let x := regValue r s.basis
  have hb (q : Nat) (hq : q < 8) : x.testBit q = s.basis (r.getD q 0) :=
    LocalWireModel.reg_bit r s.basis q (by omega)
  have x5 : x < 2^5 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases h8 : i < 8
    · interval_cases i
      · rw [hb 5 (by decide)]; exact hz.1
      · rw [hb 6 (by decide)]; exact hz.2.1
      · rw [hb 7 (by decide)]; exact hz.2.2
    · have hlt : x < 2^8 := by simpa [x, hr] using regValue_lt r s.basis
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have b0 : x.testBit 0 = s.basis g := hb 0 (by decide)
  have b1 : x.testBit 1 = s.basis c := hb 1 (by decide)
  have b2 : x.testBit 2 = s.basis xr1 := hb 2 (by decide)
  have b3 : x.testBit 3 = s.basis xr2 := hb 3 (by decide)
  have b4 : x.testBit 4 = s.basis y0 := hb 4 (by decide)
  have core : safe (predecT tr yc) x = true ∧
      bitRun (predecT tr yc) x = ofBits [pf.2.2.2, s.basis c, s.basis xr1, s.basis xr2, s.basis y0,
        pf.1, pf.2.1, pf.2.2.1] := by
    rw [← hpf]
    unfold predecT
    by_cases ro : tr.role1 = true
    · have k := predec1_ok (tr.B.testBit tr.r1) (tr.S.testBit tr.r2) yc ⟨x, x5⟩
      simp only [ro, if_true]
      refine ⟨k.1, ?_⟩
      rw [k.2]
      simp only [predOut1, b0, b1, b2, b3, b4, predFlags, ro, if_true]
    · have ro' : tr.role1 = false := by simpa using ro
      have k := predec2_ok (tr.S.testBit tr.r1) (tr.B.testBit tr.r2) yc ⟨x, x5⟩
      simp only [ro', Bool.false_eq_true, if_false]
      refine ⟨k.1, ?_⟩
      rw [k.2]
      simp only [predOut2, b0, b1, b2, b3, b4, predFlags, ro', Bool.false_eq_true, if_false]
  have L := lift_list 8 r hl hnd (predecT tr yc) (predecT_support tr yc) s m core.1
  rw [core.2] at L
  generalize hR : run (renameProgram (LocalWireModel.label (fun q : Fin 8 => r.getD q.val 0))
    (predecT tr yc)) m s = R at L ⊢
  apply State.extensionality
  · exact L.1
  · funext w
    have pv (q : Nat) (hq : q < 8) := L.2.1 q hq
    have p0 := pv 0 (by decide)
    have p1 := pv 1 (by decide)
    have p2 := pv 2 (by decide)
    have p3 := pv 3 (by decide)
    have p4 := pv 4 (by decide)
    have p5 := pv 5 (by decide)
    have p6 := pv 6 (by decide)
    have p7 := pv 7 (by decide)
    simp only [ofBits_bit, List.getD_cons_zero, List.getD_cons_succ] at p0 p1 p2 p3 p4 p5 p6 p7
    have e0 : r.getD 0 0 = g := rfl
    have e1 : r.getD 1 0 = c := rfl
    have e2 : r.getD 2 0 = xr1 := rfl
    have e3 : r.getD 3 0 = xr2 := rfl
    have e4 : r.getD 4 0 = y0 := rfl
    have e5 : r.getD 5 0 = O := rfl
    have e6 : r.getD 6 0 = D := rfl
    have e7 : r.getD 7 0 = H := rfl
    rw [e0] at p0; rw [e1] at p1; rw [e2] at p2; rw [e3] at p3; rw [e4] at p4; rw [e5] at p5
    rw [e6] at p6; rw [e7] at p7
    show R.basis w = writeBit (writeBit (writeBit (writeBit s.basis g pf.2.2.2) O pf.1) D pf.2.1) H pf.2.2.1 w
    simp only [writeBit, Function.update_apply]
    by_cases wH : w = H
    · rw [if_pos wH, wH]; exact p7
    by_cases wD : w = D
    · rw [if_neg wH, if_pos wD, wD]; exact p6
    by_cases wO : w = O
    · rw [if_neg wH, if_neg wD, if_pos wO, wO]; exact p5
    by_cases wg : w = g
    · rw [if_neg wH, if_neg wD, if_neg wO, if_pos wg, wg]; exact p0
    rw [if_neg wH, if_neg wD, if_neg wO, if_neg wg]
    by_cases wc : w = c
    · rw [wc]; exact p1
    by_cases w1 : w = xr1
    · rw [w1]; exact p2
    by_cases w2 : w = xr2
    · rw [w2]; exact p3
    by_cases w4 : w = y0
    · rw [w4]; exact p4
    exact L.2.2 w (by simp [hr, wH, wD, wO, wg, wc, w1, w2, w4])

end PreRun

end PreDecode

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section OutLocal
open Challenge

/-! ### Local-wire facts of the decode and predecode gadgets (checked over every parameter) -/

/-- Every decode variant writes local wires 6 (`.CCX 4 9 6`) and 7, 8, 9 (its CCX scratch targets). -/
theorem c2c_decodeT_mem (tr : Tri) (yb : Bool) : ({6, 7, 8, 9} : Finset Nat) ⊆ wires (decodeT tr yb) := by
  unfold decodeT
  split_ifs <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.A.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c; generalize tr.S.testBit tr.r2 = d
    cases a <;> cases b <;> cases c <;> cases d <;> cases yb <;> decide

theorem c2c_predecT_support (tr : Tri) (yc : Bool) : wires (predecT tr yc) ⊆ Finset.range 8 := by
  unfold predecT
  split_ifs <;>
  · generalize tr.B.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.S.testBit tr.r1 = a'; generalize tr.B.testBit tr.r2 = b'
    cases a <;> cases b <;> cases a' <;> cases b' <;> cases yc <;> decide

theorem c2c_predecT_physical (tr : Tri) (yc : Bool) : GatePhysical (predecT tr yc) := by
  unfold predecT
  split_ifs <;> apply gatePhysical_of_all <;>
  · generalize tr.B.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.S.testBit tr.r1 = a'; generalize tr.B.testBit tr.r2 = b'
    cases a <;> cases b <;> cases a' <;> cases b' <;> cases yc <;> decide

theorem c2c_predec_slots (a b yc : Bool) :
    gateSlots (predec1 a b yc) ≤ 13 ∧ gateSlots (predec2 a b yc) ≤ 13 := by
  cases a <;> cases b <;> cases yc <;> decide

end OutLocal

section OutCounts
open Secp256k1 ControlledPointLayout Challenge
attribute [local irreducible] wires

/-! ### Facts of the merged input stage -/

theorem c2c_tail_mem (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t h : Wire) :
    g ∈ wires (tail tr yb xr1 xr2 y0 c f g g1 wB t h) ∧ g1 ∈ wires (tail tr yb xr1 xr2 y0 c f g g1 wB t h) ∧
    wB ∈ wires (tail tr yb xr1 xr2 y0 c f g g1 wB t h) ∧ t ∈ wires (tail tr yb xr1 xr2 y0 c f g g1 wB t h) := by
  have hm := c2c_decodeT_mem tr yb
  unfold tail
  rw [renameProgram_support]
  exact ⟨Finset.mem_image.mpr ⟨6, hm (by simp), rfl⟩, Finset.mem_image.mpr ⟨7, hm (by simp), rfl⟩,
    Finset.mem_image.mpr ⟨8, hm (by simp), rfl⟩, Finset.mem_image.mpr ⟨9, hm (by simp), rfl⟩⟩

theorem c2c_pool256 (q : Wire) (hq : q ∈ layout.dialogPool.take 256) :
    q ∈ layout.dialogPool.take 253 ∨ q = layout.dialogPool.getD 253 0 ∨ q = layout.dialogPool.getD 254 0 ∨
      q = layout.dialogPool.getD 255 0 := by
  have hpl := dialogPool_length layout layout_widths
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  have hi' : i < 256 := by simp at hi; omega
  have hil : i < layout.dialogPool.length := by simp at hi; omega
  rw [List.getElem_take]
  by_cases h253 : i < 253
  · left
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  · right
    have h3 : i = 253 ∨ i = 254 ∨ i = 255 := by omega
    rcases h3 with rfl | rfl | rfl
    · left; rw [List.getD_eq_getElem _ _ hil]
    · right; left; rw [List.getD_eq_getElem _ _ hil]
    · right; right; rw [List.getD_eq_getElem _ _ hil]

theorem stage_wires_mem {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    (∀ q ∈ layout.dialogPool.take 256, q ∈ wires (stage layout (.some hc))) ∧
    layout.genericSelect ∈ wires (stage layout (.some hc)) := by
  have v := triOf_valid hc
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split (triOf (.some hc)) v
  have hpl := dialogPool_length layout layout_widths
  have hwl : (layout.dialogPool.take 253).length = 253 := by simp; omega
  have hPt : ((triOf (.some hc)).idx.map (fun i => layout.point.x.getD i 0)).tail.length = 253 := by
    rw [hidx]; simp [hitl]
  have zp := zeroPorts_maps ((triOf (.some hc)).idx.map (fun i => layout.point.x.getD i 0)).tail
    (layout.dialogPool.take 253) (by rw [hPt, hwl])
  have toStage : ∀ q, q ∈ wires (zeroWith (tail (triOf (.some hc)) (yBit (dialogExceptionPoint (.some hc)))
        (layout.point.x.getD (triOf (.some hc)).r1 0) (layout.point.x.getD (triOf (.some hc)).r2 0)
        (yLow layout) layout.control layout.point.finite layout.genericSelect (layout.dialogPool.getD 253 0)
        (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0))
        (((triOf (.some hc)).idx.map (fun i => layout.point.x.getD i 0)).headD 0)
        (zeroPorts ((triOf (.some hc)).idx.map (fun i => layout.point.x.getD i 0)).tail
          (layout.dialogPool.take 253))) →
      q ∈ wires (stage layout (.some hc)) := by
    intro q hq
    unfold stage classifier
    simp only [wires_append, Finset.mem_union]
    exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
  have tm := fun (w : Wire) (hw : ∀ h, w ∈ wires (tail (triOf (.some hc)) (yBit (dialogExceptionPoint (.some hc)))
        (layout.point.x.getD (triOf (.some hc)).r1 0) (layout.point.x.getD (triOf (.some hc)).r2 0)
        (yLow layout) layout.control layout.point.finite layout.genericSelect (layout.dialogPool.getD 253 0)
        (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) h)) =>
    toStage w (InputSentinelAux.zeroWith_tail_mem _ w hw _ _)
  have ct := fun h => c2c_tail_mem (triOf (.some hc)) (yBit (dialogExceptionPoint (.some hc)))
    (layout.point.x.getD (triOf (.some hc)).r1 0) (layout.point.x.getD (triOf (.some hc)).r2 0)
    (yLow layout) layout.control layout.point.finite layout.genericSelect (layout.dialogPool.getD 253 0)
    (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) h
  refine ⟨?_, tm _ (fun h => (ct h).1)⟩
  intro q hq
  rcases c2c_pool256 q hq with hw | rfl | rfl | rfl
  · have hm : q ∈ (zeroPorts ((triOf (.some hc)).idx.map (fun i => layout.point.x.getD i 0)).tail
        (layout.dialogPool.take 253)).map ZeroBit.work := by rw [zp.2]; exact hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    exact toStage _ (InputSentinelAux.zeroWith_work_mem _ _ _ b hb)
  · exact tm _ (fun h => (ct h).2.1)
  · exact tm _ (fun h => (ct h).2.2.1)
  · exact tm _ (fun h => (ct h).2.2.2)

/-! ### The predecode block on its eight wires -/

theorem predecL_support (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire) :
    wires (predecL tr yc g c xr1 xr2 y0 O D H) ⊆ ([g, c, xr1, xr2, y0, O, D, H] : List Wire).toFinset := by
  unfold predecL
  rw [renameProgram_support]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  have ha8 : a < 8 := Finset.mem_range.mp (c2c_predecT_support tr yc ha)
  simp only [LocalWireModel.label, dif_pos ha8]
  interval_cases a <;> simp

theorem predecL_physical (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire)
    (hnd : [g, c, xr1, xr2, y0, O, D, H].Nodup) : GatePhysical (predecL tr yc g c xr1 xr2 y0 O D H) := by
  have inj := LocalWireModel.listPorts_injective [g, c, xr1, xr2, y0, O, D, H] hnd (n := 8) (by simp)
  unfold predecL
  exact gatePhysical_rename_support _ _ (fun a ha b hb heq =>
    LocalWireModel.label_injective _ inj a (c2c_predecT_support tr yc ha) b (c2c_predecT_support tr yc hb) heq)
    (c2c_predecT_physical tr yc)

/-- Toffolis, measurements and the exact worst slot count (13) over both roles. -/
theorem predecL_counts (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire) :
    toffoliCount (predecL tr yc g c xr1 xr2 y0 O D H) = 3 ∧
    measurementCount (predecL tr yc g c xr1 xr2 y0 O D H) = 0 ∧
    gateSlots (predecL tr yc g c xr1 xr2 y0 O D H) ≤ 13 := by
  unfold predecL
  rw [(renameProgram_counts _ _).1, (renameProgram_counts _ _).2, rename_gateSlots]
  unfold predecT
  by_cases ro : tr.role1 = true
  · rw [if_pos ro]
    exact ⟨(predec_counts _ _ _).1, (predec_counts _ _ _).2.1, (c2c_predec_slots _ _ _).1⟩
  · rw [if_neg ro]
    exact ⟨(predec_counts _ _ _).2.2.1, (predec_counts _ _ _).2.2.2, (c2c_predec_slots _ _ _).2⟩

/-! ### Counts of the merged output stage -/

theorem c2c_ocorners_slots (L : ControlledPointLayout) (hw : L.Widths) (C : Point) :
    gateSlots (ocorners L C) ≤ 2048 := by
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have a1 := maskedConstant_gateSlots_le (parkWire L) L.point.x (FiniteFlagInterval.sentinel ^^^ pairCode C)
  have a2 := maskedConstant_gateSlots_le (parkWire L) L.point.y (pointY C)
  have a3 := maskedConstant_gateSlots_le L.doubleSelect L.point.x (pairCode C ^^^ pairCode (dialogExceptionPoint C))
  have a4 := maskedConstant_gateSlots_le L.doubleSelect L.point.y (pointY C ^^^ pointY (C + C))
  have a5 := maskedConstant_gateSlots_le L.genericSelect L.point.x (pairCode C ^^^ FiniteFlagInterval.sentinel)
  have a6 := maskedConstant_gateSlots_le L.genericSelect L.point.y (pointY (-C))
  have a7 := maskedConstant_gateSlots_le L.core.equalNegY L.point.x (pairCode (dialogExceptionPoint C) ^^^ pairCode C)
  have a8 := maskedConstant_gateSlots_le L.core.equalNegY L.point.y
    (pointY (dialogExceptionPoint C) ^^^ pointY (-C))
  rw [hx] at a1 a3 a5 a7
  rw [hy] at a2 a4 a6 a8
  simp only [ocorners, gateSlots_append]
  omega

/-- 261 Toffolis, 253 + 9 or 8 measurements, and the slot bounds summed:
13 (predecode) + 2048 (corners) + 3342 (output classifier) + 258 (sentinel recode). -/
theorem outStage_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (outStage layout (.some hc)) = 261 ∧
    measurementCount (outStage layout (.some hc)) = 253 + (if exceptionBit (.some hc) then 9 else 8) ∧
    gateSlots (outStage layout (.some hc)) ≤ 5661 := by
  have hpl := dialogPool_length layout layout_widths
  have hwl : (layout.dialogPool.take 253).length = 253 := by simp; omega
  have pc := predecL_counts (triOf (.some hc)) (yBit (.some hc)) layout.genericSelect layout.control
    (layout.point.x.getD (triOf (.some hc)).r1 0) (layout.point.x.getD (triOf (.some hc)).r2 0) (yLow layout)
    (parkWire layout) layout.doubleSelect layout.core.equalNegY
  have oc := ocorners_counts layout (.some hc)
  have os := c2c_ocorners_slots layout layout_widths (.some hc)
  have cc := oclassifier_counts (triOf (.some hc)) (triOf_valid hc) (yBit (.some hc))
    (yBit ((.some hc : Point) + .some hc)) (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253)
    (yLow layout) layout.control layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect
    layout.core.equalNegY (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) hwl
  have cs := oclassifier_slots (triOf (.some hc)) (triOf_valid hc) (yBit (.some hc))
    (yBit ((.some hc : Point) + .some hc)) (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253)
    (yLow layout) layout.control layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect
    layout.core.equalNegY (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) hwl
  have z := FiniteFlagInterval.zrep_counts layout
  have zs := FiniteFlagInterval.zrep_slots layout layout_widths
  unfold outStage
  simp only [toffoliCount_append, measurementCount_append, gateSlots_append, pc.1, pc.2.1, oc.1, oc.2,
    cc.1, cc.2, z.1, z.2]
  have ps := pc.2.2
  refine ⟨?_, ?_, by omega⟩
  all_goals first | trivial | omega

end OutCounts

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

section OutCompose
open Secp256k1 ControlledPointLayout
attribute [local irreducible] wires run

/-- Pivot bits of the three constants in each role. -/
theorem tri_bits (tr : Tri) (v : tr.Valid) :
    (tr.role1 = true → tr.A.testBit tr.r1 = tr.S.testBit tr.r1 ∧ tr.B.testBit tr.r1 = !tr.S.testBit tr.r1 ∧
      tr.A.testBit tr.r2 = !tr.S.testBit tr.r2) ∧
    (tr.role1 = false → tr.A.testBit tr.r1 = tr.B.testBit tr.r1 ∧ tr.S.testBit tr.r1 = !tr.A.testBit tr.r1 ∧
      tr.A.testBit tr.r2 = !tr.B.testBit tr.r2) := by
  have h1 : tr.B.testBit tr.r1 ≠ tr.S.testBit tr.r1 := (firstDiff_spec tr.B tr.S v.hB v.hS v.BS).2
  constructor
  · intro ro
    have eq1 : tr.A.testBit tr.r1 = tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
    have er2 : tr.r2 = firstDiff tr.A tr.S := by simp [Tri.r2, ro]
    have d2 := (firstDiff_spec tr.A tr.S v.hA v.hS v.AS).2
    rw [← er2] at d2
    refine ⟨eq1, ?_, ?_⟩
    · revert h1; cases tr.B.testBit tr.r1 <;> cases tr.S.testBit tr.r1 <;> simp
    · revert d2; cases tr.A.testBit tr.r2 <;> cases tr.S.testBit tr.r2 <;> simp
  · intro ro
    have ne1 : tr.A.testBit tr.r1 ≠ tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
    have er2 : tr.r2 = firstDiff tr.A tr.B := by simp [Tri.r2, ro]
    have d2 := (firstDiff_spec tr.A tr.B v.hA v.hB v.AB).2
    rw [← er2] at d2
    refine ⟨?_, ?_, ?_⟩
    · revert h1 ne1; cases tr.A.testBit tr.r1 <;> cases tr.B.testBit tr.r1 <;> cases tr.S.testBit tr.r1 <;> simp
    · revert ne1; cases tr.A.testBit tr.r1 <;> cases tr.S.testBit tr.r1 <;> simp
    · revert d2; cases tr.A.testBit tr.r2 <;> cases tr.B.testBit tr.r2 <;> simp

/-- The corner decode on a constant word gives its one-hot pattern. -/
theorem predFlags_S (tr : Tri) (v : tr.Valid) (yc n y0 : Bool) :
    predFlags tr yc n (tr.S.testBit tr.r1) (tr.S.testBit tr.r2) y0 = (n, false, false, false) := by
  have tb := tri_bits tr v
  unfold predFlags
  cases ro : tr.role1
  · obtain ⟨_, e2, _⟩ := tb.2 ro
    simp only [Bool.false_eq_true, if_false]
    rw [e2]; cases n <;> cases tr.A.testBit tr.r1 <;> cases (tr.S.testBit tr.r2 == tr.B.testBit tr.r2) <;> simp
  · obtain ⟨_, e2, _⟩ := tb.1 ro
    simp only [if_true]
    rw [e2]; cases n <;> cases tr.S.testBit tr.r1 <;> simp

theorem predFlags_B (tr : Tri) (v : tr.Valid) (yc n y0 : Bool) :
    predFlags tr yc n (tr.B.testBit tr.r1) (tr.B.testBit tr.r2) y0 = (false, false, n, false) := by
  have tb := tri_bits tr v
  unfold predFlags
  cases ro : tr.role1
  · obtain ⟨e1, e2, _⟩ := tb.2 ro
    simp only [Bool.false_eq_true, if_false]
    rw [e2, ← e1]; cases n <;> cases tr.A.testBit tr.r1 <;> simp
  · simp only [if_true]
    cases n <;> simp

theorem predFlags_A (tr : Tri) (v : tr.Valid) (yc n y0 : Bool) :
    predFlags tr yc n (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) y0 =
      (false, n && (y0 == yc), false, n && !(y0 == yc)) := by
  have tb := tri_bits tr v
  unfold predFlags
  cases ro : tr.role1
  · obtain ⟨e1, e2, e3⟩ := tb.2 ro
    simp only [Bool.false_eq_true, if_false]
    rw [e2, e3]; cases n <;> cases tr.A.testBit tr.r1 <;> cases tr.B.testBit tr.r2 <;> cases (y0 == yc) <;> simp
  · obtain ⟨e1, e2, e3⟩ := tb.1 ro
    simp only [if_true]
    rw [e1, e2, e3]; cases n <;> cases tr.S.testBit tr.r1 <;> cases tr.S.testBit tr.r2 <;> cases (y0 == yc) <;> simp

theorem predFlags_zero (tr : Tri) (yc r1 r2 y0 : Bool) :
    predFlags tr yc false r1 r2 y0 = (false, false, false, false) := by
  unfold predFlags; split_ifs <;> simp

theorem pointFinite_of_ne {P : Point} (h : P ≠ 0) : pointFinite P = true := by
  cases P with
  | zero => exact absurd rfl h
  | some _ => rfl

theorem codeX_finite {P : Point} (h : P ≠ 0) : codeX P = pointX P := by
  simp [codeX, pointFinite_of_ne h]

open Classical in
/-- On the post-generic state the corner decode yields the four dialog flags. -/
theorem predFlags_dialog {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    predFlags (triOf (.some hc)) (yBit (.some hc)) (dialogOrdinary b R (.some hc) ^^ b)
      ((codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R)).testBit (triOf (.some hc)).r1)
      ((codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R)).testBit (triOf (.some hc)).r2)
      (yBit (if dialogOrdinary b R (.some hc) then R + .some hc else R)) =
    (dialogInfinity b R, dialogDouble b R (.some hc), dialogException b R (.some hc),
      dialogInversePoint b R (.some hc)) := by
  set C : Point := .some hc with hCdef
  have hC : C ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hnC : -C ≠ 0 := neg_ne_zero.mpr hC
  have hCn : C ≠ -C := (doubling_enabled_iff hc).mp (of_decide_eq_true (cy_ne_neg hc))
  have v := triOf_valid hc
  have eA : (triOf C).A = pointX C := rfl
  have eB : (triOf C).B = pointX (dialogExceptionPoint C) := rfl
  have eS : (triOf C).S = FiniteFlagInterval.sentinel := rfl
  by_cases hg : dialogOrdinary b R C = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R C hC).mp hg
    subst hb
    rw [hg, Bool.xor_self, predFlags_zero]
    simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint, h0, h1, h2, h3]
  · have hg' : dialogOrdinary b R C = false := by simpa using hg
    rw [hg']
    simp only [Bool.false_eq_true, if_false, Bool.false_xor]
    cases b with
    | false =>
      rw [predFlags_zero]
      simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint]
    | true =>
      by_cases h0 : R = 0
      · subst h0
        have e : codeX (0 : Point) = (triOf C).S := rfl
        rw [e, predFlags_S _ v]
        simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint, Ne.symm hC, Ne.symm hnC]
        intro a _ _ e; exact a e.symm
      by_cases h1 : R = C
      · subst h1
        rw [codeX_finite hC, ← eA, predFlags_A _ v]
        simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint, hC, hCn]
        intro _ a _ e; exact a e.symm
      by_cases h2 : R = -C
      · subst h2
        rw [codeX_finite hnC, DHClass.pointX_neg, ← eA, predFlags_A _ v, yBit_neg hc]
        have hn2 : -C ≠ C := fun e => hCn e.symm
        simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint, hnC, hn2]
        exact ⟨rfl, fun _ _ a e => a e.symm, rfl⟩
      have h3 : R = dialogExceptionPoint C := by
        by_contra h3
        exact hg ((dialogOrdinary_true true R C hC).mpr ⟨rfl, h0, h1, h2, h3⟩)
      subst h3
      rw [codeX_finite h0, ← eB, predFlags_B _ v]
      simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint, h0, h1, h2]

theorem xor_cancel (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

open Classical in
/-- The sentinel-coded corner write-back turns `R1` into the output `S`. -/
theorem corners_value {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ^^^
        cornerX (.some hc) (dialogInfinity b R) (dialogDouble b R (.some hc))
          (dialogInversePoint b R (.some hc)) (dialogException b R (.some hc)) =
      codeX (if b then R + .some hc else R) ∧
    pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ^^^
        cornerY (.some hc) (dialogInfinity b R) (dialogDouble b R (.some hc))
          (dialogInversePoint b R (.some hc)) (dialogException b R (.some hc)) =
      pointY (if b then R + .some hc else R) := by
  set C : Point := .some hc with hCdef
  have hC : C ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hnC : -C ≠ 0 := neg_ne_zero.mpr hC
  have hCn : C ≠ -C := (doubling_enabled_iff hc).mp (of_decide_eq_true (cy_ne_neg hc))
  have h2C : C + C ≠ 0 := fun e => hCn (eq_neg_of_add_eq_zero_left e)
  have z0 : cornerX C false false false false = 0 := by simp [cornerX]
  have z1 : cornerY C false false false false = 0 := by simp [cornerY]
  by_cases hg : dialogOrdinary b R C = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R C hC).mp hg
    subst hb
    have f0 : dialogInfinity true R = false := by simp [dialogInfinity, h0]
    have f1 : dialogDouble true R C = false := by simp [dialogDouble, h1]
    have f2 : dialogInversePoint true R C = false := by simp [dialogInversePoint, h2]
    have f3 : dialogException true R C = false := by simp [dialogException, h3]
    rw [hg, f0, f1, f2, f3, z0, z1]
    simp
  · have hg' : dialogOrdinary b R C = false := by simpa using hg
    rw [hg']
    simp only [Bool.false_eq_true, if_false]
    cases b with
    | false =>
      have f0 : dialogInfinity false R = false := rfl
      have f1 : dialogDouble false R C = false := rfl
      have f2 : dialogInversePoint false R C = false := rfl
      have f3 : dialogException false R C = false := rfl
      rw [f0, f1, f2, f3, z0, z1]
      simp
    | true =>
      simp only [if_true]
      by_cases h0 : R = 0
      · subst h0
        have f0 : dialogInfinity true 0 = true := by simp [dialogInfinity]
        have f1 : dialogDouble true 0 C = false := by simp [dialogDouble, Ne.symm hC]
        have f2 : dialogInversePoint true 0 C = false := by simp [dialogInversePoint, Ne.symm hnC]
        rw [f0, f1, f2, dialogException_zero, zero_add]
        have e : codeX (0 : Point) = FiniteFlagInterval.sentinel := rfl
        simp only [cornerX, cornerY, if_true, Bool.false_eq_true, if_false, Nat.xor_zero, e, xor_cancel]
        exact ⟨(codeX_finite hC).symm, by simp [pointY, coordinates]⟩
      by_cases h1 : R = C
      · subst h1
        have f0 : dialogInfinity true C = false := by simp [dialogInfinity, hC]
        have f1 : dialogDouble true C C = true := by simp [dialogDouble, hCn]
        have f2 : dialogInversePoint true C C = false := by simp [dialogInversePoint, hCn]
        have f3 : dialogException true C C = false := by
          simp [dialogException]
          intro _ a _ e; exact a e.symm
        rw [f0, f1, f2, f3]
        simp only [cornerX, cornerY, if_true, Bool.false_eq_true, if_false, Nat.xor_zero, Nat.zero_xor,
          codeX_finite hC, codeX_finite h2C, pairCode, xor_cancel]
        refine ⟨?_, trivial⟩
        unfold dialogExceptionPoint
        rw [DHClass.pointX_neg]
      by_cases h2 : R = -C
      · subst h2
        have f0 : dialogInfinity true (-C) = false := by simp [dialogInfinity, hnC]
        have f1 : dialogDouble true (-C) C = false := by
          simp only [dialogDouble, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          right; intro e; exact hCn e.symm
        have f2 : dialogInversePoint true (-C) C = true := by simp [dialogInversePoint]
        have f3 : dialogException true (-C) C = false := by
          simp [dialogException]
          intro _ _ a e; exact a e.symm
        rw [f0, f1, f2, f3, neg_add_cancel]
        simp only [cornerX, cornerY, if_true, Bool.false_eq_true, if_false, Nat.xor_zero, Nat.zero_xor,
          codeX_finite hnC, pairCode, DHClass.pointX_neg, xor_cancel]
        refine ⟨rfl, ?_⟩
        rw [Nat.xor_self]; rfl
      have h3 : R = dialogExceptionPoint C := by
        by_contra h3
        exact hg ((dialogOrdinary_true true R C hC).mpr ⟨rfl, h0, h1, h2, h3⟩)
      subst h3
      have f0 : dialogInfinity true (dialogExceptionPoint C) = false := by simp [dialogInfinity, h0]
      have f1 : dialogDouble true (dialogExceptionPoint C) C = false := by simp [dialogDouble, h1]
      have f2 : dialogInversePoint true (dialogExceptionPoint C) C = false := by simp [dialogInversePoint, h2]
      have f3 : dialogException true (dialogExceptionPoint C) C = true := by
        simp [dialogException, h0, h1, h2]
      rw [f0, f1, f2, f3, dialog_exception_add]
      simp only [cornerX, cornerY, if_true, Bool.false_eq_true, if_false, Nat.xor_zero, Nat.zero_xor,
        codeX_finite h0, codeX_finite hnC, pairCode, DHClass.pointX_neg, xor_cancel]
      exact ⟨by trivial, by trivial⟩

theorem eq_of_x_ybit {x₁ y₁ x₂ y₂ : Fp} (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂) (hx : x₁.val = x₂.val)
    (hy : yBit (.some h₁ : Point) = yBit (.some h₂)) : (.some h₁ : Point) = .some h₂ := by
  have hxe : x₁ = x₂ := ZMod.val_injective _ hx
  subst hxe
  by_cases hinv : y₁ = -y₂
  · exfalso
    have e : (.some h₁ : Point) = -(.some h₂ : Point) := by
      rw [WeierstrassCurve.Affine.Point.neg_some]
      simp only [WeierstrassCurve.Affine.Point.some.injEq, negY_eq_neg, hinv, and_self]
    rw [e, yBit_neg h₂] at hy
    cases hb : yBit (.some h₂ : Point) <;> simp [hb] at hy
  · have := y_eq_of_x_eq_of_not_inverse h₁ h₂ rfl hinv
    subst this; rfl

theorem curve_x_ne_sentinel {x y : Fp} (h : curve.toAffine.Nonsingular x y) :
    x.val ≠ FiniteFlagInterval.sentinel := by
  intro e
  apply CodexAffineMath.curve_x_not_matches h
  have hs : FiniteFlagInterval.sentinel = p - 1 := by norm_num [FiniteFlagInterval.sentinel, p]
  rw [e, hs]; exact CodexAffineMath.sentinel_matches

/-- A sentinel-coded abscissa and a `y` parity determine a finite point. -/
theorem code_match (S P : Point) (hP : P ≠ 0) :
    (codeX S = pointX P ∧ yBit S = yBit P) ↔ S = P := by
  constructor
  · rintro ⟨hx, hy⟩
    cases P with
    | zero => exact absurd rfl hP
    | @some xp yp hp =>
      cases S with
      | zero =>
        exfalso
        change FiniteFlagInterval.sentinel = xp.val at hx
        exact curve_x_ne_sentinel hp hx.symm
      | @some xs ys hs =>
        change xs.val = xp.val at hx
        exact eq_of_x_ybit hs hp hx hy
  · rintro rfl; exact ⟨codeX_finite hP, rfl⟩

theorem code_sentinel (S : Point) : codeX S = FiniteFlagInterval.sentinel ↔ S = 0 := by
  cases S with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | @some xs ys hs =>
    have e1 : codeX (.some hs : Point) = xs.val := rfl
    rw [e1]
    exact ⟨fun h => absurd h (curve_x_ne_sentinel hs),
      fun h => absurd h (WeierstrassCurve.Affine.Point.some_ne_zero hs)⟩

/-- The output classifier's match bits are equality tests with the three constants. -/
theorem oX_eq (tr : Tri) (v : tr.Valid) (xs : List Wire) (hxl : xs.length = 256) (st : BasisState)
    (K : Nat) (hK : K < 2^256) (hKt : ∀ i, tr.tgt i (tr.pat K) = K.testBit i) :
    oX tr K xs st = decide (regValue xs st = K) := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  have hXlt : regValue xs st < 2^256 := by have := regValue_lt xs st; rwa [hxl] at this
  have xbit : ∀ i, i < 256 → st (xs.getD i 0) = (regValue xs st).testBit i :=
    fun i hi => (LocalWireModel.reg_bit xs st i (by omega)).symm
  have hm : matchBit tr xs st =
      decide (∀ i ∈ tr.idx, (regValue xs st).testBit i = tr.tgt i (tr.pat (regValue xs st))) := by
    unfold matchBit
    rw [xbit _ pv.1, xbit _ pv.2.1]
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true, decide_eq_true_iff]
    apply forall₂_congr
    intro i hi
    rw [xbit i (ix.2.2.2.2 i hi)]
    simp [Tri.pat]
  unfold oX
  rw [hm, xbit _ pv.1, xbit _ pv.2.1]
  have hp : ((regValue xs st).testBit tr.r1, (regValue xs st).testBit tr.r2) = tr.pat (regValue xs st) := rfl
  rw [hp]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  exact Tri.match_iff v _ K hXlt hK hKt

theorem yLow_bit (st : BasisState) : st (yLow layout) = (regValue layout.point.y st).testBit 0 := by
  have hyl : layout.point.y.length = 256 := layout_widths.inputY
  have e : yLow layout = layout.point.y.getD 0 0 := by
    unfold yLow
    cases hy : layout.point.y with
    | nil => rw [hy] at hyl; simp at hyl
    | cons a l => rfl
  rw [e, LocalWireModel.reg_bit layout.point.y st 0 (by rw [hyl]; decide)]

theorem pointY_bit0 (P : Point) : (pointY P).testBit 0 = yBit P := by
  unfold yBit
  rw [Nat.testBit_zero]

/-- Fixed wires of the output stage in the concrete layout. -/
theorem out_fixed :
    [layout.genericSelect, layout.control, yLow layout, parkWire layout, layout.doubleSelect,
      layout.core.equalNegY].Nodup ∧
    (∀ q ∈ [layout.genericSelect, layout.control, yLow layout, parkWire layout, layout.doubleSelect,
      layout.core.equalNegY], q ∉ layout.point.x) ∧
    [yLow layout, layout.control, layout.point.finite, layout.genericSelect, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY, layout.dialogPool.getD 253 0,
      layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0].Nodup ∧
    (∀ q ∈ [yLow layout, layout.control, layout.point.finite, layout.genericSelect, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY, layout.dialogPool.getD 253 0,
      layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0],
      q ∉ layout.point.x ∧ q ∉ layout.dialogPool.take 253) ∧
    parkWire layout ∈ layout.dialogPool ∧ parkWire layout ∉ layout.point.y ∧
    layout.dialogPool.getD 253 0 ∈ layout.dialogPool ∧ layout.dialogPool.getD 254 0 ∈ layout.dialogPool ∧
    layout.dialogPool.getD 255 0 ∈ layout.dialogPool := by
  decide +kernel

open Classical in
theorem exc_bit (C : Point) : exceptionBit C = decide (dialogExceptionEnabled C) := by
  simp [exceptionBit, equal_simp, dialogExceptionEnabled, Bool.and_assoc]


/-- Wires the output stage only reads or rewrites, off the point registers in the concrete layout. -/
theorem out_off : ∀ q ∈ [layout.control, layout.infinitySelect, layout.doubleSelect, layout.core.generic,
    layout.core.equalX, layout.core.equalNegY, layout.core.double, parkWire layout],
    q ∉ layout.point.x ∧ q ∉ layout.point.y ∧ q ≠ layout.point.finite ∧ q ≠ layout.genericSelect := by
  decide +kernel

theorem out_pool_off : ∀ q ∈ layout.dialogPool, q ≠ layout.point.finite ∧ q ≠ layout.genericSelect ∧
    q ≠ layout.doubleSelect ∧ q ≠ layout.core.equalNegY ∧ q ≠ layout.control := by
  decide +kernel

theorem flags_list : layout.inPlaceFlags = [layout.infinitySelect, layout.doubleSelect, layout.genericSelect,
    layout.core.generic, layout.core.equalX, layout.core.equalNegY, layout.core.double] := rfl

theorem gsel_off : layout.genericSelect ∉ layout.point.x ∧ layout.genericSelect ∉ layout.point.y ∧
    layout.genericSelect ≠ layout.point.finite := by
  decide +kernel


theorem out_ne : layout.genericSelect ≠ parkWire layout ∧ layout.genericSelect ≠ layout.doubleSelect ∧
    layout.genericSelect ≠ layout.core.equalNegY ∧ parkWire layout ≠ layout.doubleSelect ∧
    parkWire layout ≠ layout.core.equalNegY ∧ layout.doubleSelect ≠ layout.core.equalNegY := by
  decide +kernel

open Classical in
theorem bool_match (S P : Point) (hP : P ≠ 0) :
    (decide (codeX S = pointX P) && (yBit S == yBit P)) = decide (S = P) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact code_match S P hP


open Classical in
theorem finite_dec (S : Point) : pointFinite S = !decide (S = 0) := by
  cases S with
  | zero =>
    have e : (WeierstrassCurve.Affine.Point.zero : Point) = 0 := rfl
    simp [e, pointFinite, coordinates]
  | some h => simp [pointFinite, coordinates]

open Classical in
theorem code_back (S : Point) :
    codeX S ^^^ (if (!decide (S = 0)) = true then 0 else FiniteFlagInterval.sentinel) = pointX S := by
  cases S with
  | zero =>
    have e : (WeierstrassCurve.Affine.Point.zero : Point) = 0 := rfl
    simp [e, codeX, pointFinite, coordinates, pointX]
  | @some x y h =>
    have hne : (WeierstrassCurve.Affine.Point.some h : Point) ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero h
    simp [hne, codeX_finite hne]

open Classical in
/-- The merged output stage takes the post-generic state to the output boundary. -/
theorem outStage_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s0 : State) (hs : PointDialogBoundary layout R b (fun _ => false) s0.basis) (t : State) (m : List Bool)
    (htx : regValue layout.point.x t.basis =
      codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (hty : regValue layout.point.y t.basis =
      pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (htf : t.basis layout.point.finite = false)
    (htg : t.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (htr : ∀ q, q ∉ layout.point.x → q ∉ layout.point.y → q ≠ layout.point.finite →
      q ≠ layout.genericSelect → t.basis q = s0.basis q) :
    (run (outStage layout (.some hc)) m t).phase = t.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (outStage layout (.some hc)) m t).basis := by
  set C : Point := .some hc with hCdef
  have hC : C ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hnC : -C ≠ 0 := neg_ne_zero.mpr hC
  have hCn : C ≠ -C := (doubling_enabled_iff hc).mp (of_decide_eq_true (cy_ne_neg hc))
  have h2C : C + C ≠ 0 := fun e => hCn (eq_neg_of_add_eq_zero_left e)
  have v : (triOf C).Valid := triOf_valid hc
  have pv := Tri.pivots v
  obtain ⟨fx6n, fx6x, fx10n, fx10x, parkP, parkY, p253, p254, p255⟩ := out_fixed
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, -, -⟩ := stage_layout layout layout_widths layout_nodup
  set xr1 := layout.point.x.getD (triOf C).r1 0 with hxr1
  set xr2 := layout.point.x.getD (triOf C).r2 0 with hxr2
  have x1m : xr1 ∈ layout.point.x := by
    rw [hxr1, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x2m : xr2 ∈ layout.point.x := by
    rw [hxr2, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x12 : xr1 ≠ xr2 := by
    intro e
    rw [hxr1, hxr2, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    exact pv.2.2.1 ((List.Nodup.getElem_inj_iff hxn).mp e)
  have hnd8 : [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY].Nodup := by
    have hperm : [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY].Perm
        ([xr1, xr2] ++ [layout.genericSelect, layout.control, yLow layout, parkWire layout,
          layout.doubleSelect, layout.core.equalNegY]) := by
      show (([layout.genericSelect, layout.control] ++ [xr1, xr2]) ++ [yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY]).Perm
        (([xr1, xr2] ++ [layout.genericSelect, layout.control]) ++ [yLow layout, parkWire layout,
          layout.doubleSelect, layout.core.equalNegY])
      exact List.perm_append_comm.append_right _
    apply hperm.nodup_iff.mpr
    rw [List.nodup_append]
    refine ⟨by simp [x12], fx6n, ?_⟩
    intro a ha b hb e
    subst e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact fx6x _ hb x1m
    · exact fx6x _ hb x2m
  -- reads of the post-generic state
  have off (q : Wire) (hq : q ∈ [layout.control, layout.infinitySelect, layout.doubleSelect, layout.core.generic,
      layout.core.equalX, layout.core.equalNegY, layout.core.double, parkWire layout]) :
      t.basis q = s0.basis q := by
    obtain ⟨a, b', c, d⟩ := out_off q hq
    exact htr q a b' c d
  have flag0 (q : Wire) (hq : q ∈ layout.inPlaceFlags) : s0.basis q = false := hs.flags q hq
  have pool0 (q : Wire) (hq : q ∈ layout.dialogPool) : s0.basis q = false :=
    (regValue_zero _ _).mp hs.clean q hq
  have tpool (q : Wire) (hq : q ∈ layout.dialogPool) : t.basis q = false := by
    obtain ⟨a, b', -, -, -⟩ := out_pool_off q hq
    rw [htr q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) a b']
    exact pool0 q hq
  have hb0 : t.basis layout.control = b := by rw [off _ (by simp)]; exact hs.control
  have hz1 : t.basis (parkWire layout) = false ∧ t.basis layout.doubleSelect = false ∧
      t.basis layout.core.equalNegY = false := by
    refine ⟨tpool _ parkP, ?_, ?_⟩
    · rw [off _ (by simp)]; exact flag0 _ (by simp [flags_list])
    · rw [off _ (by simp)]; exact flag0 _ (by simp [flags_list])
  have hx1v : t.basis xr1 = (codeX (if dialogOrdinary b R C then R + C else R)).testBit (triOf C).r1 := by
    rw [← htx, LocalWireModel.reg_bit _ _ _ (by omega)]
  have hx2v : t.basis xr2 = (codeX (if dialogOrdinary b R C then R + C else R)).testBit (triOf C).r2 := by
    rw [← htx, LocalWireModel.reg_bit _ _ _ (by omega)]
  have hy0v : t.basis (yLow layout) = yBit (if dialogOrdinary b R C then R + C else R) := by
    rw [yLow_bit t.basis, hty, pointY_bit0]
  have pfv : predFlags (triOf C) (yBit C) (t.basis layout.genericSelect ^^ t.basis layout.control)
      (t.basis xr1) (t.basis xr2) (t.basis (yLow layout)) =
      (dialogInfinity b R, dialogDouble b R C, dialogException b R C, dialogInversePoint b R C) := by
    rw [htg, hb0, hx1v, hx2v, hy0v]; exact predFlags_dialog hc b R
  unfold outStage
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat, LocalWireModel.run_concat,
    predecL_run (triOf C) (yBit C) _ _ _ _ _ _ _ _ hnd8 t m hz1, pfv]
  -- stage 2: corners
  generalize ht1 : (⟨t.phase, writeBit (writeBit (writeBit (writeBit t.basis layout.genericSelect
    (dialogInversePoint b R C)) (parkWire layout) (dialogInfinity b R)) layout.doubleSelect
    (dialogDouble b R C)) layout.core.equalNegY (dialogException b R C)⟩ : State) = t1
  obtain ⟨gp, gd, gh, pd, ph, dh⟩ := out_ne
  have t1off (q : Wire) (h1 : q ≠ layout.genericSelect) (h2 : q ≠ parkWire layout) (h3 : q ≠ layout.doubleSelect)
      (h4 : q ≠ layout.core.equalNegY) : t1.basis q = t.basis q := by
    rw [← ht1]; simp [writeBit, Function.update, h1, h2, h3, h4]
  have t1g : t1.basis layout.genericSelect = dialogInversePoint b R C := by
    rw [← ht1]; simp [writeBit, Function.update, gp, gd, gh]
  have t1p : t1.basis (parkWire layout) = dialogInfinity b R := by
    rw [← ht1]; simp [writeBit, Function.update, pd, ph]
  have t1d : t1.basis layout.doubleSelect = dialogDouble b R C := by
    rw [← ht1]; simp [writeBit, Function.update, dh]
  have t1h : t1.basis layout.core.equalNegY = dialogException b R C := by
    rw [← ht1]; simp [writeBit, Function.update]
  have t1ph : t1.phase = t.phase := by rw [← ht1]
  have notw (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.genericSelect ∧ q ≠ parkWire layout ∧ q ≠ layout.doubleSelect ∧ q ≠ layout.core.equalNegY := by
    refine ⟨fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq), fun e => pool_not_point _ parkP (e ▸ hq),
      fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq), fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq)⟩
  have t1x : regValue layout.point.x t1.basis = regValue layout.point.x t.basis := by
    apply regValue_congr; intro q hq
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_left _ hq)
    exact t1off q a b' c d
  have t1y : regValue layout.point.y t1.basis = regValue layout.point.y t.basis := by
    apply regValue_congr; intro q hq
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_right _ hq)
    exact t1off q a b' c d
  -- stage 2: corners
  obtain ⟨c1, c2, c3, c4⟩ := ocorners_run layout layout_widths layout_nodup C t1
    (List.drop (measurementCount (predecL (triOf C) (yBit C) layout.genericSelect layout.control xr1 xr2
      (yLow layout) (parkWire layout) layout.doubleSelect layout.core.equalNegY)) m)
  generalize ht2 : run (ocorners layout C) (List.drop (measurementCount (predecL (triOf C) (yBit C)
    layout.genericSelect layout.control xr1 xr2 (yLow layout) (parkWire layout) layout.doubleSelect
    layout.core.equalNegY)) m) t1 = t2 at c1 c2 c3 c4 ⊢
  have cv := corners_value hc b R
  rw [t1x, htx, t1p, t1d, t1g, t1h, cv.1] at c2
  rw [t1y, hty, t1p, t1d, t1g, t1h, cv.2] at c3
  set S := if b then R + C else R with hSdef
  have t2off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) : t2.basis q = t1.basis q := c4 q hx hy
  have offxy (q : Wire) (hq : q ∈ layout.dialogPool) : q ∉ layout.point.x ∧ q ∉ layout.point.y :=
    ⟨fun h => pool_not_point q hq (List.mem_append_left _ h), fun h => pool_not_point q hq (List.mem_append_right _ h)⟩
  have flxy (q : Wire) (hq : q ∈ layout.inPlaceFlags) : q ∉ layout.point.x ∧ q ∉ layout.point.y :=
    ⟨fun h => flags_not_point q hq (List.mem_append_left _ h), fun h => flags_not_point q hq (List.mem_append_right _ h)⟩
  have t2pool (q : Wire) (hq : q ∈ layout.dialogPool) (hp : q ≠ parkWire layout) : t2.basis q = false := by
    obtain ⟨a, b'⟩ := offxy q hq
    obtain ⟨-, g1, d1, h1, -⟩ := out_pool_off q hq
    rw [t2off q a b', t1off q g1 hp d1 h1]; exact tpool q hq
  have t2ctl : t2.basis layout.control = b := by
    obtain ⟨a, b', -, -⟩ := out_off layout.control (by simp)
    rw [t2off _ a b', t1off _ (by decide) (by decide) (by decide) (by decide)]; exact hb0
  have t2f : t2.basis layout.point.finite = false := by
    have hfx := finite_not_flag.2
    rw [t2off _ (fun h => hfx (List.mem_append_left _ h)) (fun h => hfx (List.mem_append_right _ h)),
      t1off _ (by decide) (by decide) (by decide) (by decide)]; exact htf
  have t2y0 : t2.basis (yLow layout) = yBit S := by rw [yLow_bit t2.basis, c3, pointY_bit0]
  have gF := flxy layout.genericSelect (by simp [flags_list])
  have dF := flxy layout.doubleSelect (by simp [flags_list])
  have hF := flxy layout.core.equalNegY (by simp [flags_list])
  have pF := offxy (parkWire layout) parkP
  have t2g : t2.basis layout.genericSelect = dialogInversePoint b R C := by rw [t2off _ gF.1 gF.2, t1g]
  have t2p : t2.basis (parkWire layout) = dialogInfinity b R := by rw [t2off _ pF.1 pF.2, t1p]
  have t2d : t2.basis layout.doubleSelect = dialogDouble b R C := by rw [t2off _ dF.1 dF.2, t1d]
  have t2h : t2.basis layout.core.equalNegY = dialogException b R C := by rw [t2off _ hF.1 hF.2, t1h]
  -- the match bits on the output abscissa
  have oS : oX (triOf C) (triOf C).S layout.point.x t2.basis = decide (S = 0) := by
    rw [oX_eq _ v _ hxl _ _ v.hS (Tri.tgt_S v), c2]
    exact decide_eq_decide.mpr (code_sentinel S)
  have oA : oX (triOf C) (triOf C).A layout.point.x t2.basis = decide (codeX S = pointX C) := by
    rw [oX_eq _ v _ hxl _ _ v.hA (Tri.tgt_A), c2]; rfl
  have oB : oX (triOf C) (triOf C).B layout.point.x t2.basis = decide (codeX S = pointX (C + C)) := by
    rw [oX_eq _ v _ hxl _ _ v.hB (Tri.tgt_B v), c2]
    have e : (triOf C).B = pointX (C + C) := by
      show pointX (dialogExceptionPoint C) = _
      unfold dialogExceptionPoint; exact DHClass.pointX_neg _
    rw [e]
  have fo := dialogFlags_output b R C
  dsimp only at fo
  have hwl' : (layout.dialogPool.take 253).length = 253 := hwl
  have hfl : t2.basis layout.genericSelect = (t2.basis layout.control && oX (triOf C) (triOf C).S layout.point.x t2.basis) ∧
      t2.basis (parkWire layout) = (t2.basis layout.control && oX (triOf C) (triOf C).A layout.point.x t2.basis &&
        (t2.basis (yLow layout) == yBit C)) ∧
      t2.basis layout.doubleSelect = (t2.basis layout.control && oX (triOf C) (triOf C).B layout.point.x t2.basis &&
        (t2.basis (yLow layout) == yBit (C + C))) ∧
      t2.basis layout.core.equalNegY = (exceptionBit C && t2.basis layout.control &&
        oX (triOf C) (triOf C).A layout.point.x t2.basis && (t2.basis (yLow layout) != yBit C)) := by
    rw [t2g, t2p, t2d, t2h, t2ctl, oS, oA, oB, t2y0]
    have bmC := bool_match S C hC
    have bm2 := bool_match S (C + C) h2C
    have bmN := bool_match S (-C) hnC
    have e1 : (yBit S != yBit C) = (yBit S == yBit (-C)) := by
      rw [yBit_neg hc]; cases yBit S <;> cases yBit (.some hc : Point) <;> rfl
    have e2 : pointX C = pointX (-C) := (DHClass.pointX_neg C).symm
    have hdec : decide (C ≠ -C) = true := decide_eq_true hCn
    refine ⟨fo.2.2.1.symm, ?_, ?_, ?_⟩
    · rw [← fo.1, Bool.and_assoc, bmC]
    · rw [← fo.2.1, hdec, Bool.and_true, Bool.and_assoc, bm2]
    · rw [← fo.2.2.2, e1, e2, exc_bit]
      by_cases hen : dialogExceptionEnabled C
      · have h1 : decide (dialogExceptionEnabled C) = true := decide_eq_true hen
        have h2 : decide (dialogExceptionPoint C ≠ 0 ∧ dialogExceptionPoint C ≠ C ∧
            dialogExceptionPoint C ≠ -C) = true := decide_eq_true hen
        rw [h1, h2, Bool.and_true, Bool.true_and, Bool.and_assoc, bmN]
      · have h1 : decide (dialogExceptionEnabled C) = false := decide_eq_false hen
        have h2 : decide (dialogExceptionPoint C ≠ 0 ∧ dialogExceptionPoint C ≠ C ∧
            dialogExceptionPoint C ≠ -C) = false := decide_eq_false hen
        rw [h1, h2]; simp
  rw [oclassifier_run (triOf C) v (yBit C) (yBit (C + C)) (exceptionBit C) layout.point.x
    (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite layout.genericSelect
    (parkWire layout) layout.doubleSelect layout.core.equalNegY (layout.dialogPool.getD 253 0)
    (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) hxn hxl hwl' hwn hdisj fx10n fx10x t2 _
    ⟨fun q hq => t2pool q (List.mem_of_mem_take hq) (fun e => (fx10x _ (by simp)).2 (e ▸ hq)), t2f,
      t2pool _ p253 (by decide), t2pool _ p254 (by decide), t2pool _ p255 (by decide)⟩ hfl]
  rw [oS]
  -- stage 4: back to the plain abscissa
  generalize ht3 : (⟨t2.phase, writeBit (writeBit (writeBit (writeBit (writeBit t2.basis layout.point.finite
    (!decide (S = 0))) layout.genericSelect false) (parkWire layout) false) layout.doubleSelect false)
    layout.core.equalNegY false⟩ : State) = t3
  have t3ph : t3.phase = t.phase := by rw [← ht3]; show t2.phase = t.phase; rw [c1, t1ph]
  have t3off (q : Wire) (h0 : q ≠ layout.point.finite) (h1 : q ≠ layout.genericSelect) (h2 : q ≠ parkWire layout)
      (h3 : q ≠ layout.doubleSelect) (h4 : q ≠ layout.core.equalNegY) : t3.basis q = t2.basis q := by
    rw [← ht3]; simp [writeBit, Function.update, h0, h1, h2, h3, h4]
  have fG : layout.point.finite ≠ layout.genericSelect := (gsel_off.2.2).symm
  have fP : layout.point.finite ≠ parkWire layout := fun e => (out_pool_off _ parkP).1 e.symm
  have fD : layout.point.finite ≠ layout.doubleSelect :=
    fun e => finite_not_flag.1 (e ▸ (by simp [flags_list] : layout.doubleSelect ∈ layout.inPlaceFlags))
  have fH : layout.point.finite ≠ layout.core.equalNegY :=
    fun e => finite_not_flag.1 (e ▸ (by simp [flags_list] : layout.core.equalNegY ∈ layout.inPlaceFlags))
  have t3f : t3.basis layout.point.finite = !decide (S = 0) := by
    rw [← ht3]; simp [writeBit, Function.update, fG, fP, fD, fH]
  have t3x : regValue layout.point.x t3.basis = codeX S := by
    rw [← c2]; apply regValue_congr; intro q hq
    have hf : q ≠ layout.point.finite := fun e => finite_not_flag.2 (e ▸ List.mem_append_left _ hq)
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_left _ hq)
    exact t3off q hf a b' c d
  have t3y : regValue layout.point.y t3.basis = pointY S := by
    rw [← c3]; apply regValue_congr; intro q hq
    have hf : q ≠ layout.point.finite := fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_right _ hq)
    exact t3off q hf a b' c d
  suffices key : ∀ mm, (run (FiniteFlagInterval.zrep layout) mm t3).phase = t.phase ∧
      PointDialogBoundary layout S b (fun _ => false) (run (FiniteFlagInterval.zrep layout) mm t3).basis by
    exact key _
  intro mm
  obtain ⟨z1, z2, z3⟩ := FiniteFlagInterval.zrep_run layout layout_widths layout_nodup t3 mm
  generalize run (FiniteFlagInterval.zrep layout) mm t3 = t4 at z1 z2 z3 ⊢
  have fx : layout.point.finite ∉ layout.point.x := fun h => finite_not_flag.2 (List.mem_append_left _ h)
  refine ⟨by rw [z1, t3ph], ?_, ?_, ?_, ?_⟩
  · apply (point_holds _ _ _).mpr
    refine ⟨by rw [z2 _ fx, t3f, finite_dec], by rw [z3, t3x, t3f, code_back], ?_⟩
    rw [← t3y]; apply regValue_congr; intro q hq
    exact z2 q (y_not_x layout layout_nodup q hq)
  · obtain ⟨a, -, c, d⟩ := out_off layout.control (by simp)
    rw [z2 _ a, t3off _ c.symm.symm (by decide) (by decide) (by decide) (by decide)]
    · exact t2ctl
  · intro q hq
    rw [z2 q (flags_not_point q hq ∘ List.mem_append_left _)]
    rw [flags_list] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨a, b', c, d⟩ := out_off layout.infinitySelect (by simp)
      rw [t3off _ c (by decide) (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ (by decide) (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
    · rw [← ht3]; simp [writeBit, Function.update, dh]
    · rw [← ht3]; simp [writeBit, Function.update, gp, gd, gh]
    · obtain ⟨a, b', c, d⟩ := out_off layout.core.generic (by simp)
      rw [t3off _ c d (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ d (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
    · obtain ⟨a, b', c, d⟩ := out_off layout.core.equalX (by simp)
      rw [t3off _ c d (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ d (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
    · rw [← ht3]; simp [writeBit, Function.update]
    · obtain ⟨a, b', c, d⟩ := out_off layout.core.double (by simp)
      rw [t3off _ c d (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ d (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
  · apply (regValue_zero _ _).mpr
    intro q hq
    rw [z2 q (fun h => pool_not_point q hq (List.mem_append_left _ h))]
    by_cases hp : q = parkWire layout
    · subst hp; rw [← ht3]; simp [writeBit, Function.update, pd, ph]
    · obtain ⟨f1, g1, d1, h1, -⟩ := out_pool_off q hq
      rw [t3off q f1 g1 hp d1 h1]
      exact t2pool q hq hp

end OutCompose

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

section OutSplice
open Secp256k1 ControlledPointLayout
attribute [local irreducible] wires

/-- The generic block on its own, before the input relabellings. -/
def genBlock (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (renameProgram (swapF L) (ReflectionE1TickGapLow48.generic L cx cy))

/-- Finite program with both merged stages. -/
def finiteProgram2 (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  stage L C ++ renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) (genBlock L cx cy))) ++
    outStage L C

def wrapper2 (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgram2 L C cx cy)

open Classical in
theorem finite2_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteProgram2 layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteProgram2 layout (.some hc) cx cy) m s).basis := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s m hs
  have hp := (point_holds _ _ _).mp hs.point
  unfold finiteProgram2
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (stage layout (.some hc)) m s = t1 at m1 m2 m3 m4 m5 ⊢
  have gsx := gsel_off
  have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
      (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
  have t1y : regValue layout.point.y t1.basis = pointY R := by
    rw [← hp.2.2]; apply regValue_congr; intro q hq
    exact m5 q (y_not_x layout layout_nodup q hq)
      (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
  have hE : t1.basis layout.core.equalNegY = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.core.equalNegY (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hD : t1.basis layout.doubleSelect = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.doubleSelect (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hclean : regValue layout.dialogPool t1.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
    rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
    exact (regValue_zero _ _).mp hs.clean q hq
  -- the generic block moves the coordinates only
  suffices key : ∀ mm, (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlock layout cx cy)))) mm t1).phase = t1.phase ∧
      regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlock layout cx cy)))) mm t1).basis =
        codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlock layout cx cy)))) mm t1).basis =
        pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      ∀ q, q ∉ layout.point.x ++ layout.point.y →
        (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
          (genBlock layout cx cy)))) mm t1).basis q = t1.basis q by
    obtain ⟨k1, k2, k3, k4⟩ := key (List.drop (measurementCount (stage layout (.some hc))) m)
    generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlock layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) m) t1 = t2 at k1 k2 k3 k4 ⊢
    have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
    have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
      simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
    obtain ⟨o1, o2⟩ := outStage_run hc b R s hs t2
      (List.drop (measurementCount (stage layout (.some hc) ++ renameProgram (swapD layout)
        (renameProgram (swapE layout) (renameProgram (tauM layout) (genBlock layout cx cy))))) m)
      k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
      (fun q hx hy hf hg => by
        rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    exact ⟨by rw [o1, k1, m1], o2⟩
  intro mm
  unfold genBlock
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => ReflectionE1TickGapLow48.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => ReflectionE1TickGapLow48.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run x y x y false
        (fun base' => ReflectionE1TickGapLow48.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem wrapper2_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapper2 layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite2_run hc b R s m hs
  unfold wrapper2
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h

/-- Old output parts of the classifier wrapper, in order, and their resource floor. -/
theorem old_out_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    504 ≤ toffoliCount (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (CodexYParityProbe.clrF layout ++ FiniteFlagInterval.zrep layout)))) ++
      FusedFlags.suffixProgram layout (.some hc) ++
      renameProgram (sigP layout) (corners2 layout (.some hc) ++ Edges.sharedM layout (.some hc)) ++
      chainErase layout.control layout.point.finite layout.genericSelect) ∧
    505 ≤ measurementCount (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (CodexYParityProbe.clrF layout ++ FiniteFlagInterval.zrep layout)))) ++
      FusedFlags.suffixProgram layout (.some hc) ++
      renameProgram (sigP layout) (corners2 layout (.some hc) ++ Edges.sharedM layout (.some hc)) ++
      chainErase layout.control layout.point.finite layout.genericSelect) := by
  have c := CodexYParityProbe.counts layout layout_widths
  have z := FiniteFlagInterval.zrep_counts layout
  have sm := Edges.sharedM_counts layout layout_widths hc
  have pr := FusedFlags.counts (DHClass.cxk (.some hc)) (yBit (.some hc))
  have pt := renameProgram_counts (LocalWireModel.label (FusedFlags.ports layout (DHClass.kx (.some hc))))
    (FusedFlags.restoreSuffix (DHClass.cxk (.some hc)) (yBit (.some hc)))
  have ce : measurementCount (chainErase layout.control layout.point.finite layout.genericSelect) = 1 := rfl
  simp only [toffoliCount_append, measurementCount_append, renameProgram_counts, FusedFlags.suffixProgram,
    pt.1, pt.2, c.1, c.2.1, z.1, z.2, sm.1, sm.2, pr.2.1, pr.2.2.2, ce]
  constructor <;> omega

theorem wires_inst {P Q : Program} (h : ∀ i ∈ P, i ∈ Q) : wires P ⊆ wires Q := fun w hw => by
  obtain ⟨i, hi, hq⟩ := (SW.mem_wires_iff _ _).mp hw
  exact (SW.mem_wires_iff _ _).mpr ⟨i, h i hi, hq⟩

/-- Wires of the merged output stage: I/O wires, wires of the merged input stage, or of the fused suffix. -/
theorem outStage_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (outStage layout (.some hc)) ⊆
      (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset ∪
        (wires (stage layout (.some hc)) ∪ wires (FusedFlags.suffixProgram layout (.some hc))) := by
  have sw := stage_wires_mem hc
  have sm := suffix_mem layout (.some hc)
  have hyl := yLow_mem layout layout_widths
  have hxl : layout.point.x.length = 256 := layout_widths.inputX
  have io_x : ∀ q ∈ layout.point.x, q ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
    intro q hq; simp [PointAddLayout.pointWires, hq]
  have io_y : ∀ q ∈ layout.point.y, q ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
    intro q hq; simp [PointAddLayout.pointWires, hq]
  have io_f : layout.point.finite ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
    simp [PointAddLayout.pointWires]
  have io_c : layout.control ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by simp
  have st (q : Wire) (h : q ∈ wires (stage layout (.some hc))) :
      q ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset ∪
        (wires (stage layout (.some hc)) ∪ wires (FusedFlags.suffixProgram layout (.some hc))) :=
    Finset.mem_union_right _ (Finset.mem_union_left _ h)
  have su (q : Wire) (h : q ∈ wires (FusedFlags.suffixProgram layout (.some hc))) :
      q ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset ∪
        (wires (stage layout (.some hc)) ∪ wires (FusedFlags.suffixProgram layout (.some hc))) :=
    Finset.mem_union_right _ (Finset.mem_union_right _ h)
  have tk (n : Nat) (hn : n ≤ 256) (q : Wire) (hq : q ∈ layout.dialogPool.take n) :
      q ∈ layout.dialogPool.take 256 := by
    have hpl := dialogPool_length layout layout_widths
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hq
    simp only [List.length_take] at hi
    rw [List.getElem_take] at e
    rw [← e]
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  intro w hw
  unfold outStage at hw
  simp only [wires_append, Finset.mem_union] at hw
  rcases hw with ((hw | hw) | hw) | hw
  · have h := predecL_support _ _ _ _ _ _ _ _ _ _ hw
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact st _ sw.2
    · exact Finset.mem_union_left _ io_c
    · apply Finset.mem_union_left; apply io_x
      rw [List.getD_eq_getElem _ _ (by have := (Tri.pivots (triOf_valid hc)).1; omega)]
      exact List.getElem_mem _
    · apply Finset.mem_union_left; apply io_x
      rw [List.getD_eq_getElem _ _ (by have := (Tri.pivots (triOf_valid hc)).2.1; omega)]
      exact List.getElem_mem _
    · exact Finset.mem_union_left _ (io_y _ hyl)
    · exact su _ sm.2.2
    · exact su _ sm.1
    · exact su _ sm.2.1
  · have h := ocorners_support layout (.some hc) hw
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with (h | h) | h | h | h | h
    · exact Finset.mem_union_left _ (io_x _ h)
    · exact Finset.mem_union_left _ (io_y _ h)
    · subst h; exact su _ sm.2.2
    · subst h; exact su _ sm.1
    · subst h; exact st _ sw.2
    · subst h; exact su _ sm.2.1
  · have h := oclassifier_support _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hxl
      (by simp [dialogPool_length layout layout_widths]) hw
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with (h | h) | h | h | h | h | h | h | h | h | h | h
    · exact Finset.mem_union_left _ (io_x _ h)
    · exact st _ (sw.1 _ (tk 253 (by decide) _ h))
    · subst h; exact Finset.mem_union_left _ (io_y _ hyl)
    · subst h; exact Finset.mem_union_left _ io_c
    · subst h; exact Finset.mem_union_left _ io_f
    · subst h; exact st _ sw.2
    · subst h; exact su _ sm.2.2
    · subst h; exact su _ sm.1
    · subst h; exact su _ sm.2.1
    · subst h; exact st _ (sw.1 _ (pool_take_mem 253 (by decide)))
    · subst h; exact st _ (sw.1 _ (pool_take_mem 254 (by decide)))
    · subst h; exact st _ (sw.1 _ (pool_take_mem 255 (by decide)))
  · have h : w ∈ (layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255)).toFinset := by
      rw [← FiniteFlagInterval.old_clrF_support layout layout_widths]
      exact FiniteFlagInterval.zrep_support_old layout layout_widths hw
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact Finset.mem_union_left _ io_f
    · exact Finset.mem_union_left _ (io_x _ h)
    · exact st _ (sw.1 _ (tk 255 (by decide) _ h))

theorem finite2_sub {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (finiteProgram2 layout (.some hc) cx cy) ⊆
      wires (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) ∪
        (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
  have hst : wires (stage layout (.some hc)) ⊆
      wires (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) :=
    wires_inst (fun i hi => by unfold finiteProgram'; exact List.mem_append_left _ hi)
  have hsu : wires (FusedFlags.suffixProgram layout (.some hc)) ⊆
      wires (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) :=
    wires_inst (fun i hi => by
      unfold finiteProgram' shared
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hi))))
  have hge : wires (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlock layout cx cy)))) ⊆
      wires (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) :=
    wires_inst (fun i hi => by
      unfold finiteProgram' shared
      apply List.mem_append_right
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      simp only [tailGen, genBlock, FusedFlags.rename_append] at hi ⊢
      exact List.mem_append_left _ (List.mem_append_left _ hi))
  intro w hw
  unfold finiteProgram2 at hw
  simp only [wires_append, Finset.mem_union] at hw
  rcases hw with (hw | hw) | hw
  · exact Finset.mem_union_left _ (hst hw)
  · exact Finset.mem_union_left _ (hge hw)
  · rcases Finset.mem_union.mp (outStage_support hc hw) with h | h
    · exact Finset.mem_union_right _ h
    · rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union_left _ (hst h)
      · exact Finset.mem_union_left _ (hsu h)

theorem wrapper2_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper2 layout (.some hc) cx cy) ⊆
      wires (wrapper' layout (.some hc) (tailGen layout cx cy)) ∪
        (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
  unfold wrapper2 wrapper'
  rw [renameProgram_support, renameProgram_support]
  intro q hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (finite2_sub hc hw) with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
  · apply Finset.mem_union_right
    rw [Wrapper5.U_outside layout layout_widths w (io_not_pool w (List.mem_toFinset.mp h))]
    exact h

theorem support2_used {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper2 layout (.some hc) cx cy) ⊆ layout.dialogUsedWires.toFinset := by
  intro q hq
  rcases Finset.mem_union.mp (wrapper2_support hc hq) with o | t
  · exact support_used' hc o
  · have t' := List.mem_toFinset.mp t
    apply List.mem_toFinset.mpr
    unfold ControlledPointLayout.dialogUsedWires
    exact List.mem_append_left _ (List.mem_append_left _ t')

open Classical in
theorem full_spec2 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapper2 layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz : regValue layout.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi : PointDialogBoundary layout R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  have c2 := wrapper2_spec hc b R s m hi
  have a : (run (wrapper' layout (.some hc) (tailGen layout cx cy)) m s).phase = s.phase ∧
      PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
        (run (wrapper' layout (.some hc) (tailGen layout cx cy)) m s).basis := by
    rw [wrapper'_eq hc b R s m hi]
    exact FusedFlags.wrapper_spec layout layout_widths layout_nodup R hc b _
      (CodexYParityProbe.genFFused_ok layout layout_widths layout_nodup hc) s _ hi
  rw [MeasuredDH.boundary_unique layout _ _ (support2_used hc) (support_used' hc) s m _ b c2.2 a.2
    (c2.1.trans a.1.symm)]
  exact full_spec' hc b R s m hs

/-- Old output parts of the classifier wrapper. -/
def oldOut (L : ControlledPointLayout) (C : Point) : Program :=
  renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L)
    (renameProgram (Wrapper5.U L) (CodexYParityProbe.clrF L ++ FiniteFlagInterval.zrep L)))) ++
  FusedFlags.suffixProgram L C ++
  renameProgram (sigP L) (corners2 L C ++ Edges.sharedM L C) ++
  chainErase L.control L.point.finite L.genericSelect

theorem counts2_rel {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapper2 layout (.some hc) cx cy) + toffoliCount (oldOut layout (.some hc)) =
      toffoliCount (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        toffoliCount (outStage layout (.some hc)) ∧
    measurementCount (wrapper2 layout (.some hc) cx cy) + measurementCount (oldOut layout (.some hc)) =
      measurementCount (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        measurementCount (outStage layout (.some hc)) ∧
    Challenge.gateSlots (wrapper2 layout (.some hc) cx cy) + Challenge.gateSlots (oldOut layout (.some hc)) =
      Challenge.gateSlots (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        Challenge.gateSlots (outStage layout (.some hc)) := by
  unfold wrapper2 wrapper' finiteProgram2 finiteProgram' shared tailGen genBlock oldOut
  simp only [renameProgram_counts, rename_gateSlots, toffoliCount_append, measurementCount_append,
    Challenge.gateSlots_append, CodexYParityProbe.generic]
  omega

theorem nd8 (xr1 xr2 : Wire) (x1m : xr1 ∈ layout.point.x) (x2m : xr2 ∈ layout.point.x) (x12 : xr1 ≠ xr2) :
    [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY].Nodup := by
  obtain ⟨fx6n, fx6x, -, -, -, -, -, -, -⟩ := out_fixed
  have hperm : [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY].Perm
      ([xr1, xr2] ++ [layout.genericSelect, layout.control, yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY]) := by
    show (([layout.genericSelect, layout.control] ++ [xr1, xr2]) ++ [yLow layout, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY]).Perm
      (([xr1, xr2] ++ [layout.genericSelect, layout.control]) ++ [yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY])
    exact List.perm_append_comm.append_right _
  apply hperm.nodup_iff.mpr
  rw [List.nodup_append]
  refine ⟨by simp [x12], fx6n, ?_⟩
  intro a ha b hb e
  subst e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact fx6x _ hb x1m
  · exact fx6x _ hb x2m

theorem outStage_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (outStage layout (.some hc)) := by
  have pv := Tri.pivots (triOf_valid hc)
  obtain ⟨-, -, fx10n, fx10x, -, -, -, -, -⟩ := out_fixed
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, -, -⟩ := stage_layout layout layout_widths layout_nodup
  have x1m : layout.point.x.getD (triOf (.some hc)).r1 0 ∈ layout.point.x := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x2m : layout.point.x.getD (triOf (.some hc)).r2 0 ∈ layout.point.x := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x12 : layout.point.x.getD (triOf (.some hc)).r1 0 ≠ layout.point.x.getD (triOf (.some hc)).r2 0 := by
    intro e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    exact pv.2.2.1 ((List.Nodup.getElem_inj_iff hxn).mp e)
  unfold outStage
  simp only [gatePhysical_append]
  exact ⟨⟨⟨predecL_physical _ _ _ _ _ _ _ _ _ _ (nd8 _ _ x1m x2m x12),
    ocorners_physical layout layout_widths layout_nodup _⟩,
    oclassifier_physical _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hxl hwl hxn hwn hdisj fx10n fx10x⟩,
    FiniteFlagInterval.zrep_physical layout layout_nodup⟩

theorem wrapper2_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapper2 layout (.some hc) cx cy) := by
  have old := wrapper'_physical hc
  unfold wrapper' at old
  rw [R2SqEp760.gatePhysical_rename_iff] at old
  unfold wrapper2
  rw [R2SqEp760.gatePhysical_rename_iff]
  intro i hi
  unfold finiteProgram2 at hi
  rcases List.mem_append.mp hi with hi | hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact stage_physical hc i hi
    · apply old i
      unfold finiteProgram' shared
      apply List.mem_append_right
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      simp only [tailGen, genBlock, FusedFlags.rename_append] at hi ⊢
      exact List.mem_append_left _ (List.mem_append_left _ hi)
  · exact outStage_physical hc i hi

end OutSplice


section OutCert
open Secp256k1 Challenge ControlledPointLayout
attribute [local irreducible] wires

def program2 (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ => wrapper2 layout C cx cy

def entry2 : Challenge.Entry := fun C => normalizeProgram (program2 C)
def bounds2 : Challenge.Bounds := ⟨2150578, 1498380, 1587, 50225383⟩

theorem program2_correct (C : Point) (control : Bool) (R : Point) :
    Triple (encodes control R) (program2 C) (encodes control (if control then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program2,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    exact fixed_correct _ control R _ (full_spec2 hc control R) (support2_used hc)

theorem program2_toffoli (C : Point) : toffoliCount (program2 C) ≤ 2150578 := by
  cases C with
  | zero => simp [program2, toffoliCount]
  | @some cx cy hc =>
    have r := (counts2_rel hc).1
    have o : 504 ≤ toffoliCount (oldOut layout (.some hc)) := (old_out_counts hc).1
    have st := (outStage_counts hc).1
    have old := program_toffoli (.some hc)
    change toffoliCount (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 2150821 at old
    change toffoliCount (wrapper2 layout (.some hc) cx cy) ≤ 2150578
    omega

theorem program2_measurements (C : Point) : measurementCount (program2 C) ≤ 1498380 := by
  cases C with
  | zero => simp [program2, measurementCount]
  | @some cx cy hc =>
    have r := (counts2_rel hc).2.1
    have o : 505 ≤ measurementCount (oldOut layout (.some hc)) := (old_out_counts hc).2
    have st := (outStage_counts hc).2.1
    have old := program_measurements (.some hc)
    change measurementCount (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 1498623 at old
    change measurementCount (wrapper2 layout (.some hc) cx cy) ≤ 1498380
    split_ifs at st <;> omega

theorem program2_qubits (C : Point) : qubits (program2 C) ≤ 1587 := by
  cases C with
  | zero => change qubits [] ≤ 1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have sub := wrapper2_support hc
    have old := program_qubits (.some hc)
    change qubits (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 1587 at old
    change qubits (wrapper2 layout (.some hc) cx cy) ≤ 1587
    refine le_trans (Finset.card_le_card ?_) old
    intro q hq
    rcases Finset.mem_union.mp hq with io | used
    · exact Finset.mem_union_left _ io
    · rcases Finset.mem_union.mp (sub used) with o | t
      · exact Finset.mem_union_right _ o
      · apply Finset.mem_union_left
        exact io_mem q (List.mem_toFinset.mp t)

theorem program2_physical (C : Point) : GatePhysical (program2 C) := by
  cases C with
  | zero => simp [program2, GatePhysical]
  | @some cx cy hc => exact wrapper2_physical hc

theorem program2_gateSlots (C : Point) : gateSlots (program2 C) ≤ 50225383 := by
  cases C with
  | zero => simp [program2]
  | @some cx cy hc =>
    have r := (counts2_rel hc).2.2
    have st := (outStage_counts hc).2.2
    have old := program_gateSlots (.some hc)
    change gateSlots (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 50219722 at old
    change gateSlots (wrapper2 layout (.some hc) cx cy) ≤ 50225383
    omega

theorem certificate2 : Challenge.Certificate entry2 bounds2 where
  correct C control R := (normalize_triple _ _ _).mpr (program2_correct C control R)
  physical C := normalize_physical _ (program2_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program2_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program2 C)) ≤ 1498380
    rw [normalize_measurements]; exact program2_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program2 C)) ≤ 1587
    rw [normalize_qubits]; exact program2_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program2 C)) ≤ 50225383
    rw [normalize_slots]; exact program2_gateSlots C

end OutCert

end ECDSAAdd.Entrant.InputSentinel

-- ===== merged module ECDSAAdd.Submission.Entrant.Main =====
section
namespace ECDSAAdd.Entrant
def program := InputSentinel.program2
def entry := InputSentinel.entry2
def bounds := InputSentinel.bounds2
theorem certificate : Challenge.Certificate entry bounds := InputSentinel.certificate2
end ECDSAAdd.Entrant
end
