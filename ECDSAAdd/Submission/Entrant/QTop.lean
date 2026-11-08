import ECDSAAdd.Submission.Entrant.MainB
import ECDSAAdd.Arithmetic.KnownOutputAdder
import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical
import ECDSAAdd.Arithmetic.SignedTriangularSquareProof
import ECDSAAdd.Baselines.SlotAlgebra
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareProof

-- Public B-body restore from submission 29b8f1b9.
section

section
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace ECDSAAdd.Entrant.KnownTopAdd
open ECDSAAdd ECDSAAdd.Arithmetic Instr

/-- `addInPlace` on `x`, `y` whose carry out already sits on `t`: the top carry is never formed,
and `t` is measured away in its place. -/
def addTop : List Wire → List Wire → List Wire → Wire → Wire → Program
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, cin, t =>
      majority a b cin c ++ addTop (a' :: as) (b' :: bs) cs c t ++
        eraseCarry a b cin c ++ [CX a b, CX cin b]
  | [a], [b], _, cin, t => eraseCarry a b cin t ++ [CX a b, CX cin b]
  | _, _, _, _, _ => []

theorem top_base (a b cin t z k : Wire) (hnd : [a, b, cin, t, z, k].Nodup) (s : State) (m : List Bool)
    (ht : s.basis t = carryBit (s.basis a) (s.basis b) (s.basis cin))
    (hz : s.basis z = false) (hk : s.basis k = false) :
    run (eraseCarry a b cin t ++ [CX a b, CX cin b]) m s =
      run (majority a b cin k ++ [CX z t, CX k t] ++ eraseCarry a b cin k ++ [CX a b, CX cin b]) m s := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at hnd
  obtain ⟨⟨hab, hac, hat, haz, hak⟩, ⟨hbc, hbt, hbz, hbk⟩, ⟨hct, hcz, hck⟩, ⟨htz, htk⟩, hzk⟩ := hnd
  simp only [List.append_assoc]
  rw [run_append (majority a b cin k), majority_correct a b cin k (by simp [*, Ne.symm]) s]
  have h0 : measurementCount (majority a b cin k) = 0 := by simp [majority, measurementCount]
  simp only [h0, List.drop_zero]
  rw [hk, Bool.false_xor, ← ht]
  have hP : measurementCount [CX z t, CX k t] = 0 := by simp [measurementCount]
  rw [run_append [CX z t, CX k t], hP]
  simp only [List.take_zero, List.drop_zero]
  have e2 : run [CX z t, CX k t] [] ⟨s.phase, writeBit s.basis k (s.basis t)⟩ =
      ⟨s.phase, writeBit (writeBit s.basis k (s.basis t)) t false⟩ := by
    simp only [run]
    congr 1
    funext w
    by_cases h1 : w = t
    · subst h1
      simp [writeBit, Function.update, hz, htk, htz, Ne.symm htk, Ne.symm htz, Ne.symm hzk, hzk]
    · by_cases h2 : w = k
      · subst h2
        simp [writeBit, Function.update, h1, hz, Ne.symm htk, hzk, Ne.symm hzk]
      · simp [writeBit, Function.update, h1, h2, hz, hzk, Ne.symm hzk]
  rw [e2]
  have hm : ∀ (x : Bool) (cs : List Correction), measureAndCorrect t [] cs x s =
      measureAndCorrect k [] cs x ⟨s.phase, writeBit (writeBit s.basis k (s.basis t)) t false⟩ := by
    intro x cs
    have hw : writeBit (writeBit (writeBit s.basis k (s.basis t)) t false) k false =
        writeBit s.basis t false := by
      funext w
      by_cases h1 : w = t
      · subst h1; simp [writeBit, Function.update, htk]
      · by_cases h2 : w = k
        · subst h2; simp [writeBit, Function.update, h1, hk]
        · simp [writeBit, Function.update, h1, h2]
    have hv : writeBit (writeBit s.basis k (s.basis t)) t false k = s.basis t := by
      simp [writeBit, Function.update, Ne.symm htk]
    simp only [measureAndCorrect, hw, hv]
  simp only [eraseCarry, List.cons_append, List.nil_append, run, hm]

theorem carry_nat (a b c : Bool) : (if carryBit a b c = true then 1 else 0) =
    ((if a = true then 1 else 0) + (if b = true then 1 else 0) + (if c = true then 1 else 0)) / 2 := by
  cases a <;> cases b <;> cases c <;> decide

theorem addTop_counts (x y cs : List Wire) (cin t z k : Wire)
    (hx : x.length = y.length) (hc : cs.length + 1 = y.length) (h1 : 1 ≤ y.length) :
    measurementCount (addTop x y cs cin t) =
      measurementCount (addInPlace (x ++ [z]) (y ++ [t]) (cs ++ [k]) cin) ∧
    toffoliCount (addTop x y cs cin t) + 1 =
      toffoliCount (addInPlace (x ++ [z]) (y ++ [t]) (cs ++ [k]) cin) := by
  induction y generalizing x cs cin with
  | nil => simp at h1
  | cons b ys ih =>
    cases x with
    | nil => simp at hx
    | cons a xs =>
    cases ys with
    | nil =>
      have : xs = [] := by simpa using hx
      subst this
      have : cs = [] := by simpa using hc
      subst this
      simp [addTop, addInPlace, measurementCount, toffoliCount, eraseCarry, majority]
    | cons b' bs =>
      cases xs with
      | nil => simp at hx
      | cons a' as =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
      have r := ih (a' :: as) cs c (by simpa using hx) (by simpa using hc) (by simp)
      simp only [List.cons_append] at r ⊢
      simp only [addTop, addInPlace, toffoliCount_append, measurementCount_append]
      omega

theorem addTop_run (x y cs : List Wire) (cin t z k : Wire)
    (hx : x.length = y.length) (hc : cs.length + 1 = y.length) (h1 : 1 ≤ y.length)
    (hn : (cin :: t :: z :: k :: (x ++ y ++ cs)).Nodup) (s : State) (m : List Bool)
    (hz : s.basis z = false) (hk : s.basis k = false) (hcs : ∀ q ∈ cs, s.basis q = false)
    (hv : (if s.basis t = true then 1 else 0) =
      (regValue x s.basis + regValue y s.basis + (if s.basis cin = true then 1 else 0)) / 2 ^ y.length) :
    run (addTop x y cs cin t) m s =
      run (addInPlace (x ++ [z]) (y ++ [t]) (cs ++ [k]) cin) m s := by
  induction y generalizing x cs cin s m with
  | nil => simp at h1
  | cons b ys ih =>
    cases x with
    | nil => simp at hx
    | cons a xs =>
    cases ys with
    | nil =>
      have : xs = [] := by simpa using hx
      subst this
      have : cs = [] := by simpa using hc
      subst this
      have nd : [a, b, cin, t, z, k].Nodup := by
        apply List.nodup_iff_count_le_one.mpr
        intro q
        have h := List.nodup_iff_count_le_one.mp hn q
        simp only [List.count_cons, List.count_append, List.count_nil] at h ⊢
        omega
      have ht : s.basis t = carryBit (s.basis a) (s.basis b) (s.basis cin) := by
        have e := carry_nat (s.basis a) (s.basis b) (s.basis cin)
        simp only [regValue, List.foldr_cons, List.foldr_nil, List.length_cons, List.length_nil,
          Nat.zero_add, pow_one, Nat.mul_zero, Nat.add_zero] at hv
        rw [← hv] at e
        cases h : s.basis t <;> cases h2 : carryBit (s.basis a) (s.basis b) (s.basis cin) <;>
          simp [h, h2] at e ⊢
      have := top_base a b cin t z k nd s m ht hz hk
      simpa only [addTop, addInPlace, List.cons_append, List.nil_append] using this
    | cons b' bs =>
      cases xs with
      | nil => simp at hx
      | cons a' as =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
      simp only [List.cons_append] at *
      have cnt := fun q => List.nodup_iff_count_le_one.mp hn q
      simp only [List.count_cons, List.count_append, List.count_nil] at cnt
      have nd4 : [a, b, cin, c].Nodup := by
        apply List.nodup_iff_count_le_one.mpr
        intro q
        have h := cnt q
        simp only [List.count_cons, List.count_nil]
        omega
      have ndr : (c :: t :: z :: k :: (a' :: as ++ b' :: bs ++ cs)).Nodup := by
        apply List.nodup_iff_count_le_one.mpr
        intro q
        have h := cnt q
        simp only [List.count_cons, List.count_append, List.count_nil]
        omega
      have mc0 : measurementCount (majority a b cin c) = 0 := by simp [majority, measurementCount]
      have hcnt := (addTop_counts (a' :: as) (b' :: bs) cs c t z k (by simpa using hx) (by simpa using hc) (by simp)).1
      simp only [List.cons_append] at hcnt
      simp only [addTop, addInPlace, List.append_assoc]
      rw [run_append (majority a b cin c), run_append (majority a b cin c), mc0]
      simp only [List.take_zero, List.drop_zero]
      rw [majority_correct a b cin c nd4]
      rw [run_append (addTop (a' :: as) (b' :: bs) cs c t),
        run_append (addInPlace (a' :: (as ++ [z])) (b' :: (bs ++ [t])) (cs ++ [k]) c), hcnt]
      have c0 : s.basis c = false := hcs c (by simp)
      have nc : ∀ q, q ≠ c → writeBit s.basis c (s.basis c ^^ carryBit (s.basis a) (s.basis b) (s.basis cin)) q =
          s.basis q := fun q h => by simp [writeBit, Function.update, h]
      have cv : writeBit s.basis c (s.basis c ^^ carryBit (s.basis a) (s.basis b) (s.basis cin)) c =
          carryBit (s.basis a) (s.basis b) (s.basis cin) := by simp [writeBit, Function.update, c0]
      have off (l : List Wire) (hl : c ∉ l) :
          regValue l (writeBit s.basis c (s.basis c ^^ carryBit (s.basis a) (s.basis b) (s.basis cin))) =
            regValue l s.basis :=
        regValue_congr _ _ _ (fun q hq => nc q (fun e => hl (e ▸ hq)))
      have nd2 := ndr
      simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at nd2
      have nd1 := hn
      simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at nd1
      have hcx : c ∉ a' :: as := by
        have := List.count_eq_zero.mp (show List.count c (a' :: as) = 0 by
          have h := cnt c
          simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at h ⊢
          omega)
        exact this
      have hcy : c ∉ b' :: bs := by
        have := List.count_eq_zero.mp (show List.count c (b' :: bs) = 0 by
          have h := cnt c
          simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at h ⊢
          omega)
        exact this
      have hcc : c ∉ cs := by
        have := List.count_eq_zero.mp (show List.count c cs = 0 by
          have h := cnt c
          simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at h ⊢
          omega)
        exact this
      have ctz : c ≠ t ∧ c ≠ z ∧ c ≠ k := ⟨nd2.1.1, nd2.1.2.1, nd2.1.2.2.1⟩
      have r := ih (a' :: as) cs c (by simpa using hx) (by simpa using hc) (by simp) ndr
        ⟨s.phase, writeBit s.basis c (s.basis c ^^ carryBit (s.basis a) (s.basis b) (s.basis cin))⟩
        (m.take (measurementCount (addInPlace (a' :: (as ++ [z])) (b' :: (bs ++ [t])) (cs ++ [k]) c)))
        ((nc z (Ne.symm ctz.2.1)).trans hz) ((nc k (Ne.symm ctz.2.2)).trans hk)
        (fun q hq => (nc q (fun e => hcc (e ▸ hq))).trans (hcs q (by simp [hq])))
        (by
          have e1 : regValue (a :: a' :: as) s.basis =
              (if s.basis a = true then 1 else 0) + 2 * regValue (a' :: as) s.basis := rfl
          have e2 : regValue (b :: b' :: bs) s.basis =
              (if s.basis b = true then 1 else 0) + 2 * regValue (b' :: bs) s.basis := rfl
          simp only [nc t (Ne.symm ctz.1), off _ hcx, off _ hcy, cv]
          rw [carry_nat, hv, e1, e2]
          generalize regValue (a' :: as) s.basis = X
          generalize regValue (b' :: bs) s.basis = Y
          generalize (if s.basis a = true then 1 else 0) = A
          generalize (if s.basis b = true then 1 else 0) = B
          generalize (if s.basis cin = true then 1 else 0) = C
          simp only [List.length_cons]
          rw [pow_succ' 2 (bs.length + 1), ← Nat.div_div_eq_div_mul]
          congr 1
          omega)
      simp only [List.cons_append] at r
      rw [r]

theorem noop_run (k : Wire) (P : Program) (m : List Bool) (s : State) (hk : s.basis k = false) :
    run (Instr.measureX k [] [] :: P) m s = run P m.tail s := by
  have e : measureAndCorrect k [] [] (m.headD false) s = s := by
    rcases s with ⟨ph, b⟩
    simp only at hk
    have hb : writeBit b k false = b := by
      funext w
      by_cases h : w = k
      · subst h; simp [writeBit, Function.update, hk]
      · simp [writeBit, Function.update, h]
    simp [measureAndCorrect, correct, hk, hb]
  simp only [run, e]

theorem reg_snoc (r : List Wire) (u : Wire) (t : BasisState) :
    regValue (r ++ [u]) t = regValue r t + 2 ^ r.length * (if t u = true then 1 else 0) := by
  rw [regValue_append]
  simp [regValue]

theorem reg_snoc2 (r : List Wire) (u v : Wire) (t : BasisState) :
    regValue (r ++ [u, v]) t = regValue r t + 2 ^ r.length * (if t u = true then 1 else 0) +
      2 ^ (r.length + 1) * (if t v = true then 1 else 0) := by
  rw [regValue_append]
  simp only [regValue, List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero]
  rw [pow_succ]
  ring

/-- Subtract from a register whose top two bits are clear: both end equal to the borrow. -/
def subTop (h r cs : List Wire) (cin z u v k : Wire) : Program :=
  Instr.measureX k [] [] :: (subInPlace (h ++ [z]) (r ++ [u]) cs cin ++ [CX u v])

/-- Add when the result is known to fit `r`: the top bits are erased, not computed. -/
def addKnown (h r cs : List Wire) (cin z u v k : Wire) : Program :=
  Instr.measureX k [] [] :: (CX u v :: addTop h r cs cin u)

theorem mod4 (T N : Nat) (hN : 0 < N) (h : T < 8 * N) :
    T % (4 * N) = if T < 4 * N then T else T - 4 * N := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem mod2 (T N : Nat) (hN : 0 < N) (h : T < 4 * N) :
    T % (2 * N) = if T < 2 * N then T else T - 2 * N := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem known_top (E S N : Nat) (hN : 0 < N) (hE : E < N) (hS : S < N) (U V : Bool)
    (fit : (E + N * (if U = true then 1 else 0) + 2 * N * (if V = true then 1 else 0) + S) % (4 * N) < N) :
    (if U = true then 1 else 0) = (S + E) / N ∧ V = U ∧
    (E + N * (if U = true then 1 else 0) + S) % (2 * N) =
      (E + N * (if U = true then 1 else 0) + 2 * N * (if V = true then 1 else 0) + S) % (4 * N) := by
  have d : S + E < N → (S + E) / N = 0 := fun h => Nat.div_eq_of_lt h
  have d1 : N ≤ S + E → (S + E) / N = 1 := fun h =>
    Nat.div_eq_of_lt_le (by omega) (by omega)
  cases U <;> cases V <;> simp only [Bool.false_eq_true, if_false, if_true, Nat.mul_zero, Nat.mul_one,
    Nat.add_zero] at fit ⊢
  all_goals
    first
    | rw [mod4 _ N hN (by omega)] at fit
  all_goals
    by_cases hc : S + E < N
    · have := d hc
      rw [mod4 _ N hN (by omega), mod2 _ N hN (by omega)]
      split at fit <;> (try split) <;> (try split) <;> (refine ⟨?_,?_,?_⟩ <;> first | omega | simp_all)
    · have := d1 (by omega)
      rw [mod4 _ N hN (by omega), mod2 _ N hN (by omega)]
      split at fit <;> (try split) <;> (try split) <;> (refine ⟨?_,?_,?_⟩ <;> first | omega | simp_all)

theorem sub_top_arith (E S N A : Nat) (b : Bool) (hN : 0 < N) (hE : E < N) (hS : S < N) (hA : A < N)
    (hv : A + N * (if b = true then 1 else 0) = (E + 2 * N - S) % (2 * N)) :
    A + N * (if b = true then 1 else 0) + 2 * N * (if b = true then 1 else 0) =
      (E + 4 * N - S) % (4 * N) := by
  rw [mod2 _ N hN (by omega)] at hv
  rw [mod4 _ N hN (by omega)]
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true, Nat.mul_zero, Nat.mul_one,
    Nat.add_zero] at hv ⊢ <;> split at hv <;> split <;> omega

theorem subTop_spec (h r cs : List Wire) (cin z u v k : Wire)
    (hn : (cin :: u :: v :: z :: k :: (h ++ r ++ cs)).Nodup)
    (hl : h.length = r.length) (hc : cs.length = r.length) (hr : 1 ≤ r.length)
    (s : State) (m : List Bool) (hk : s.basis k = false) (hz : s.basis z = false)
    (hu : s.basis u = false) (hv : s.basis v = false) (hcin : s.basis cin = false)
    (hcs : regValue cs s.basis = 0) :
    (run (subTop h r cs cin z u v k) m s).phase = s.phase ∧
    regValue (r ++ [u, v]) (run (subTop h r cs cin z u v k) m s).basis =
      (regValue r s.basis + 2 ^ (r.length + 2) - regValue h s.basis) % 2 ^ (r.length + 2) ∧
    ∀ q, q ∉ r → q ≠ u → q ≠ v → (run (subTop h r cs cin z u v k) m s).basis q = s.basis q := by
  have cnt := fun q => List.nodup_iff_count_le_one.mp hn q
  simp only [List.count_cons, List.count_append, List.count_nil] at cnt
  have nd : (cin :: ((h ++ [z]) ++ (r ++ [u]) ++ cs)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := cnt q
    simp only [List.count_cons, List.count_append, List.count_nil]
    omega
  have l1 : (h ++ [z]).length = (r ++ [u]).length := by simp [hl]
  have l2 : cs.length + 1 = (r ++ [u]).length := by simp [hc]
  have vN : v ∉ r ++ [u] := by
    intro hm
    have c := cnt v
    have p := List.count_pos_iff.mpr hm
    simp only [List.count_cons, List.count_append, List.count_nil] at p
    simp only [beq_self_eq_true, if_true] at c p
    omega
  have uv : u ≠ v := by
    have c := cnt u
    intro e
    rw [← e] at c
    simp only [beq_self_eq_true, if_true] at c
    omega
  have vr : v ∉ r := fun x => vN (List.mem_append_left _ x)
  rw [subTop, noop_run _ _ _ _ hk, run_append]
  generalize hmm : m.tail = m'
  have X : regValue (h ++ [z]) s.basis = regValue h s.basis := by rw [reg_snoc]; simp [hz]
  have Y : regValue (r ++ [u]) s.basis = regValue r s.basis := by rw [reg_snoc]; simp [hu]
  have sp := subInPlace_spec (h ++ [z]) (r ++ [u]) cs cin nd l1 l2 _ _ s
    (m'.take (measurementCount (subInPlace (h ++ [z]) (r ++ [u]) cs cin)))
    ⟨⟨⟨rfl, rfl⟩, hcin⟩, hcs⟩
  have fr := subInPlace_frame (h ++ [z]) (r ++ [u]) cs cin nd l1 l2 s
    (m'.take (measurementCount (subInPlace (h ++ [z]) (r ++ [u]) cs cin))) hcin hcs
  have vv : regValue (r ++ [u]) (run (subInPlace (h ++ [z]) (r ++ [u]) cs cin)
      (m'.take (measurementCount (subInPlace (h ++ [z]) (r ++ [u]) cs cin))) s).basis = _ := sp.2.1.1.2
  have ph := sp.1
  generalize run (subInPlace (h ++ [z]) (r ++ [u]) cs cin)
    (m'.take (measurementCount (subInPlace (h ++ [z]) (r ++ [u]) cs cin))) s = a at *
  simp only [run]
  have vz : a.basis v = false := (fr v vN).trans hv
  rw [X, Y, reg_snoc, List.length_append, List.length_singleton] at vv
  have hS : regValue h s.basis < 2 ^ r.length := by rw [← hl]; exact regValue_lt _ _
  have hE : regValue r s.basis < 2 ^ r.length := regValue_lt _ _
  have hA : regValue r a.basis < 2 ^ r.length := regValue_lt _ _
  have p1 : (2 : Nat) ^ (r.length + 1) = 2 * 2 ^ r.length := by rw [pow_succ]; ring
  have p2 : (2 : Nat) ^ (r.length + 2) = 4 * 2 ^ r.length := by rw [pow_add]; ring
  refine ⟨ph, ?_, ?_⟩
  · rw [reg_snoc2]
    have r0 : regValue r (writeBit a.basis v (a.basis v ^^ a.basis u)) = regValue r a.basis :=
      regValue_congr _ _ _ (fun q hq => by
        have : q ≠ v := fun e => vr (e ▸ hq)
        simp [writeBit, Function.update, this])
    have r1 : writeBit a.basis v (a.basis v ^^ a.basis u) u = a.basis u := by
      simp [writeBit, Function.update, uv]
    have r2 : writeBit a.basis v (a.basis v ^^ a.basis u) v = a.basis u := by
      simp [writeBit, Function.update, vz]
    rw [r0, r1, r2, p1, p2]
    rw [p1] at vv
    exact sub_top_arith _ _ _ _ _ (by positivity) hE hS hA vv
  · intro q q1 q2 q3
    have : writeBit a.basis v (a.basis v ^^ a.basis u) q = a.basis q := by
      simp [writeBit, Function.update, q3]
    rw [this]
    exact fr q (by simp [q1, q2])

theorem addKnown_spec (h r cs : List Wire) (cin z u v k : Wire)
    (hn : (cin :: u :: v :: z :: k :: (h ++ r ++ cs)).Nodup)
    (hl : h.length = r.length) (hc : cs.length + 1 = r.length) (hr : 1 ≤ r.length)
    (s : State) (m : List Bool) (hk : s.basis k = false) (hz : s.basis z = false)
    (hcin : s.basis cin = false) (hcs : regValue cs s.basis = 0)
    (fit : (regValue (r ++ [u, v]) s.basis + regValue h s.basis) % 2 ^ (r.length + 2) < 2 ^ r.length) :
    (run (addKnown h r cs cin z u v k) m s).phase = s.phase ∧
    regValue (r ++ [u, v]) (run (addKnown h r cs cin z u v k) m s).basis =
      (regValue (r ++ [u, v]) s.basis + regValue h s.basis) % 2 ^ (r.length + 2) ∧
    ∀ q, q ∉ r → q ≠ u → q ≠ v → (run (addKnown h r cs cin z u v k) m s).basis q = s.basis q := by
  have cnt := fun q => List.nodup_iff_count_le_one.mp hn q
  simp only [List.count_cons, List.count_append, List.count_nil] at cnt
  have ndT : (cin :: u :: z :: k :: (h ++ r ++ cs)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := cnt q
    simp only [List.count_cons, List.count_append, List.count_nil]
    omega
  have nd : (cin :: (h ++ [z]) ++ (r ++ [u]) ++ (cs ++ [k])).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := cnt q
    simp only [List.cons_append, List.count_cons, List.count_append, List.count_nil]
    omega
  have l1 : (h ++ [z]).length = (r ++ [u]).length := by simp [hl]
  have l2 : (cs ++ [k]).length + 1 = (r ++ [u]).length := by simp [hc]
  have vN : v ∉ r ++ [u] ++ h ++ [z] ++ cs ++ [k] ++ [cin] := by
    intro hm
    have c := cnt v
    have p := List.count_pos_iff.mpr hm
    simp only [List.count_cons, List.count_append, List.count_nil] at p
    simp only [beq_self_eq_true, if_true] at c p
    omega
  have vM (q : Wire) (hq : q ∈ r ++ [u] ++ h ++ [z] ++ cs ++ [k] ++ [cin]) : q ≠ v :=
    fun e => vN (e ▸ hq)
  have mm : ∀ q, (q ∈ r ∨ q = u ∨ q ∈ h ∨ q = z ∨ q ∈ cs ∨ q = k ∨ q = cin) →
      q ∈ r ++ [u] ++ h ++ [z] ++ cs ++ [k] ++ [cin] := by
    intro q hq
    simp only [List.mem_append, List.mem_singleton]
    tauto
  have hN : 0 < 2 ^ r.length := by positivity
  have hS : regValue h s.basis < 2 ^ r.length := by rw [← hl]; exact regValue_lt _ _
  have hE : regValue r s.basis < 2 ^ r.length := regValue_lt _ _
  have p1 : (2 : Nat) ^ (r.length + 1) = 2 * 2 ^ r.length := by rw [pow_succ]; ring
  have p2 : (2 : Nat) ^ (r.length + 2) = 4 * 2 ^ r.length := by rw [pow_add]; ring
  rw [reg_snoc2, p1, p2] at fit
  obtain ⟨c1, c2, c3⟩ := known_top _ _ _ hN hE hS (s.basis u) (s.basis v) fit
  generalize hs1 : (⟨s.phase, writeBit s.basis v (s.basis v ^^ s.basis u)⟩ : State) = s1
  have b1 : ∀ q, q ≠ v → s1.basis q = s.basis q := fun q hq => by
    rw [← hs1]; simp [writeBit, Function.update, hq]
  have b2 : s1.basis v = false := by
    rw [← hs1]; simp [writeBit, Function.update, c2]
  have ph1 : s1.phase = s.phase := by rw [← hs1]
  have reg1 (l : List Wire) (hq : ∀ q ∈ l, q ≠ v) : regValue l s1.basis = regValue l s.basis :=
    regValue_congr _ _ _ (fun q h' => b1 q (hq q h'))
  have rv := reg1 r (fun q h' => vM q (mm q (Or.inl h')))
  have hv' := reg1 h (fun q h' => vM q (mm q (Or.inr (Or.inr (Or.inl h')))))
  have hcv := reg1 cs (fun q h' => vM q (mm q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))))
  have uE := b1 u (vM u (mm u (by simp)))
  have zE := b1 z (vM z (mm z (by simp)))
  have kE := b1 k (vM k (mm k (by simp)))
  have cE := b1 cin (vM cin (mm cin (by simp)))
  have cs0 : regValue (cs ++ [k]) s1.basis = 0 := by
    rw [reg_snoc, hcv, hcs, kE, hk]; simp
  have tr := addInPlace_cin_frame cin (h ++ [z]) (r ++ [u]) (cs ++ [k]) nd l1 l2 s1.basis false
    (cE.trans hcin) cs0 (regValue (r ++ [u]) s1.basis) s1 m.tail ⟨rfl, fun _ _ => rfl⟩
  have rn : run (addKnown h r cs cin z u v k) m s =
      run (addInPlace (h ++ [z]) (r ++ [u]) (cs ++ [k]) cin) m.tail s1 := by
    rw [addKnown, noop_run _ _ _ _ hk]
    simp only [run]
    rw [hs1]
    apply addTop_run h r cs cin u z k hl hc hr ndT s1 m.tail (zE.trans hz) (kE.trans hk)
    · intro q hq
      exact (regValue_zero _ _).mp (hcv.trans hcs) q hq
    · rw [hv', rv, uE, cE, hcin]
      simpa using c1
  rw [rn]
  generalize run (addInPlace (h ++ [z]) (r ++ [u]) (cs ++ [k]) cin) m.tail s1 = o at tr
  obtain ⟨tp, tv, tf⟩ := tr
  have vo : o.basis v = false := (tf v (fun x => vN (by
    simp only [List.mem_append] at x ⊢; tauto))).trans b2
  refine ⟨tp.trans ph1, ?_, ?_⟩
  · rw [reg_snoc2 r u v o.basis, vo, reg_snoc2 r u v s.basis, p1, p2]
    rw [reg_snoc, reg_snoc, reg_snoc, rv, uE, hv', zE, hz] at tv
    simp only [List.length_append, List.length_singleton, Bool.false_eq_true, if_false,
      Nat.mul_zero, Nat.add_zero, Bool.toNat_false] at tv ⊢
    rw [tv, p1, c3]
  · intro q q1 q2 q3
    rw [tf q (by simp [q1, q2])]
    exact b1 q q3

theorem addTop_wires_sub (x y cs : List Wire) (cin t : Wire) :
    wires (addTop x y cs cin t) ⊆ (cin :: t :: (x ++ y ++ cs)).toFinset := by
  induction x, y, cs, cin, t using addTop.induct with
  | case1 a a' as b b' bs c cs cin t ih =>
    simp only [addTop, wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq
    have ih' := @ih q
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at ih' ⊢
    rcases hq with ((h|h)|h)|h
    · simp [majority, wires, Instr.wires] at h; tauto
    · have := ih' h; tauto
    · simp [eraseCarry, wires, Instr.wires, correctionWires] at h; tauto
    · simp [wires, Instr.wires] at h; tauto
  | case2 a b cs cin t =>
    simp only [addTop, wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    rcases hq with h|h
    · simp [eraseCarry, wires, Instr.wires, correctionWires] at h; tauto
    · simp [wires, Instr.wires] at h; tauto
  | case3 x y cs cin t h => simp [addTop, wires]

theorem cx2_physical (a b cin : Wire) (h1 : a ≠ b) (h2 : cin ≠ b) :
    GatePhysical [CX a b, CX cin b] := by
  simp [GatePhysical, RecordedQuantum.PhysicalInstr, ECDSAAdd.ProperGate, h1, h2]

theorem addTop_physical (x y cs : List Wire) (cin t : Wire)
    (hn : (cin :: t :: (x ++ y ++ cs)).Nodup) : GatePhysical (addTop x y cs cin t) := by
  induction x, y, cs, cin, t using addTop.induct with
  | case1 a a' as b b' bs c cs cin t ih =>
    have cnt := fun q => List.nodup_iff_count_le_one.mp hn q
    simp only [List.count_cons, List.count_append, List.count_nil] at cnt
    have nd4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count_le_one.mpr; intro q; have h := cnt q
      simp only [List.count_cons, List.count_nil]; omega
    have ndr : (c :: t :: (a' :: as ++ b' :: bs ++ cs)).Nodup := by
      apply List.nodup_iff_count_le_one.mpr; intro q; have h := cnt q
      simp only [List.count_cons, List.count_append, List.count_nil]; omega
    have ab : a ≠ b := by
      intro e; have h := cnt a; rw [← e] at h
      simp only [beq_self_eq_true, if_true] at h; omega
    have cb : cin ≠ b := by
      intro e; have h := cnt cin; rw [← e] at h
      simp only [beq_self_eq_true, if_true] at h; omega
    simp only [addTop, gatePhysical_append]
    exact ⟨⟨⟨majority_physical a b cin c nd4, ih ndr⟩, eraseCarry_physical a b cin c⟩, cx2_physical a b cin ab cb⟩
  | case2 a b cs cin t =>
    have cnt := fun q => List.nodup_iff_count_le_one.mp hn q
    simp only [List.count_cons, List.count_append, List.count_nil] at cnt
    have ab : a ≠ b := by
      intro e; have h := cnt a; rw [← e] at h
      simp only [beq_self_eq_true, if_true] at h; omega
    have cb : cin ≠ b := by
      intro e; have h := cnt cin; rw [← e] at h
      simp only [beq_self_eq_true, if_true] at h; omega
    simp only [addTop, gatePhysical_append]
    exact ⟨eraseCarry_physical a b cin t, cx2_physical a b cin ab cb⟩
  | case3 x y cs cin t h => simp [addTop, GatePhysical]

theorem addTop_gateSlots_le (x y cs : List Wire) (cin t : Wire) :
    Challenge.gateSlots (addTop x y cs cin t) ≤ 12 * x.length := by
  induction x, y, cs, cin, t using addTop.induct with
  | case1 a a' as b b' bs c cs cin t ih =>
    simp only [addTop, Challenge.gateSlots_append, Baselines.majority_gateSlots, Baselines.eraseCarry_gateSlots,
      Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots, List.length_cons] at *
    omega
  | case2 a b cs cin t =>
    simp [addTop, Challenge.gateSlots_append, Baselines.gateSlots_cons, Challenge.instructionSlots]
  | case3 x y cs cin t h => simp [addTop]

theorem addInPlace_slots_eq (x y cs : List Wire) (c : Wire)
    (hx : x.length = y.length) (hc : cs.length + 1 = y.length) :
    Challenge.gateSlots (addInPlace x y cs c) + 10 = 12 * y.length := by
  induction y generalizing x cs c with
  | nil => simp at hc
  | cons b ys ih =>
    cases x with
    | nil => simp at hx
    | cons a xs =>
    cases ys with
    | nil =>
      have : xs = [] := by simpa using hx
      subst this
      simp [addInPlace, Baselines.gateSlots_cons, Challenge.instructionSlots]
    | cons b' bs =>
      cases xs with
      | nil => simp at hx
      | cons a' as =>
      cases cs with
      | nil => simp at hc
      | cons d ds =>
      have r := ih (a' :: as) ds d (by simpa using hx) (by simpa using hc)
      simp only [addInPlace, Challenge.gateSlots_append, Baselines.majority_gateSlots, Baselines.eraseCarry_gateSlots,
        Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots, List.length_cons] at r ⊢
      omega

theorem addTop_slots_eq (x y cs : List Wire) (c t : Wire)
    (hx : x.length = y.length) (hc : cs.length + 1 = y.length) :
    Challenge.gateSlots (addTop x y cs c t) + 6 = 12 * y.length := by
  induction y generalizing x cs c with
  | nil => simp at hc
  | cons b ys ih =>
    cases x with
    | nil => simp at hx
    | cons a xs =>
    cases ys with
    | nil =>
      have : xs = [] := by simpa using hx
      subst this
      simp [addTop, Challenge.gateSlots_append, Baselines.gateSlots_cons, Challenge.instructionSlots]
    | cons b' bs =>
      cases xs with
      | nil => simp at hx
      | cons a' as =>
      cases cs with
      | nil => simp at hc
      | cons d ds =>
      have r := ih (a' :: as) ds d (by simpa using hx) (by simpa using hc)
      simp only [addTop, Challenge.gateSlots_append, Baselines.majority_gateSlots, Baselines.eraseCarry_gateSlots,
        Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots, List.length_cons] at r ⊢
      omega

end ECDSAAdd.Entrant.KnownTopAdd
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KnownTopAdd

def eRlow (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.product.take 128
def eU (L : CuccaroStreamedSquareWideLayout) : Wire := (L.core.product.drop 256).headD 0
def eV (L : CuccaroStreamedSquareWideLayout) : Wire := (L.core.product.drop 256).getD 1 0
def eZ0 (L : CuccaroStreamedSquareWideLayout) : Wire := (eZ L).headD 0
def eKw (L : CuccaroStreamedSquareWideLayout) : Wire := ((eBank L).drop 128).headD 0

/-- `eSub L (b1Src L)` on a value below `2^128`. -/
def eSubK (L : CuccaroStreamedSquareWideLayout) : Program :=
  subTop (hiReg L) (eRlow L) ((eBank L).take 128) L.core.cin (eZ0 L) (eU L) (eV L) (eKw L)
/-- `eAdd L (b1Src L)` when the sum is below `2^128`. -/
def eAddK (L : CuccaroStreamedSquareWideLayout) : Program :=
  addKnown (hiReg L) (eRlow L) ((eBank L).take 127) L.core.cin (eZ0 L) (eU L) (eV L) (eKw L)

theorem eShape (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    eReg L = eRlow L ++ [eU L, eV L] ∧ (∃ z1, eZ L = [eZ0 L, z1]) ∧
      eBank L = (eBank L).take 128 ++ [eKw L] := by
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  refine ⟨?_,?_,?_⟩
  · have l : (L.core.product.drop 256).length=2 := by simp [hw.core.product]
    obtain ⟨u,v,e⟩ := List.length_eq_two.mp l
    simp [eReg,eRlow,eU,eV,e]
  · have l : (eZ L).length=2 := by simp [eZ,fp]
    obtain ⟨u,v,e⟩ := List.length_eq_two.mp l
    exact ⟨v,by simp [eZ0,e]⟩
  · have l : ((eBank L).drop 128).length=1 := by simp [eBank,fp]
    obtain ⟨x,e⟩ := List.length_eq_one_iff.mp l
    have k : eKw L=x := by simp [eKw,e]
    have := List.take_append_drop 128 (eBank L)
    rw [e] at this
    rw [k]
    exact this.symm

theorem eK_nodup (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (j : Nat) (hj : j≤128) :
    (L.core.cin::eU L::eV L::eZ0 L::eKw L::(hiReg L++eRlow L++(eBank L).take j)).Nodup := by
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  have b := eAdder_nodup L hn (b1Src L) (Or.inl rfl)
  rw [b1Src,e1,e2] at b
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have c := List.nodup_iff_count_le_one.mp b q
  have d := congrArg (List.count q) e3
  have f : ((eBank L).take j).count q≤((eBank L).take 128).count q := by
    have : (eBank L).take j=((eBank L).take 128).take j := by
      rw [List.take_take]; congr 1; omega
    rw [this]
    exact (List.take_sublist j _).count_le q
  simp only [List.count_cons,List.count_append,List.count_nil] at c d ⊢
  omega

theorem eK_facts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E A : Nat) (s : BasisState) (h : BState L base O E A s) :
    s (eZ0 L)=false ∧ s (eKw L)=false ∧ s L.core.cin=false ∧
    (∀j,regValue ((eBank L).take j) s=0) ∧ regValue (hiReg L) s=regValue (hiReg L) base := by
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  obtain ⟨_,_,hi,padZ,_⟩ := zero_regs L hn base hc O E A s h
  have zm : eZ0 L∈L.foldPad := by
    have : eZ0 L∈eZ L := by rw [e2]; simp
    exact List.mem_of_mem_drop (List.mem_of_mem_take this)
  have km : eKw L∈L.foldPad := by
    have : eKw L∈eBank L := by rw [e3]; simp
    exact List.mem_of_mem_take this
  refine ⟨padZ _ zm,padZ _ km,hi,?_,?_⟩
  · intro j
    exact (regValue_zero _ _).mpr (fun q hq => padZ q (List.mem_of_mem_take (List.mem_of_mem_take hq)))
  · exact regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E A s h q (Or.inl hq))

theorem eSubK_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E A S : Nat) (hE : E<2^128)
    (hS : regValue (hiReg L) base=S) :
    Triple (BState L base O E A) (eSubK L) (BState L base O ((E+2^130-S)%2^130) A) := by
  apply lift_e L hn base O E A _ (eSubK L)
  intro s m h
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  obtain ⟨f1,f2,f3,f4,f5⟩ := eK_facts L hw hn base hc O E A s.basis h
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have hl : (hiReg L).length=(eRlow L).length := by rw [hiReg_length L hw,rl]
  have bl : ((eBank L).take 128).length=(eRlow L).length := by
    have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
    simp [eBank,fp,rl]
  have hv : regValue (eReg L) s.basis=E := h.2.1
  rw [e1,reg_snoc2,rl] at hv
  have hu : s.basis (eU L)=false := by
    cases e : s.basis (eU L)
    · rfl
    · simp only [e,if_true] at hv
      have : (2:Nat)^128≤E := by omega
      omega
  have hv2 : s.basis (eV L)=false := by
    cases e : s.basis (eV L)
    · rfl
    · simp only [e,if_true] at hv
      norm_num at hv hE
      omega
  have hr : regValue (eRlow L) s.basis=E := by
    simp only [hu,hv2,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at hv
    exact hv
  obtain ⟨p,v,f⟩ := subTop_spec (hiReg L) (eRlow L) ((eBank L).take 128) L.core.cin (eZ0 L) (eU L) (eV L) (eKw L)
    (eK_nodup L hw hn 128 (le_refl _)) hl bl (by omega) s m f2 f1 hu hv2 f3 (f4 128)
  refine ⟨p,?_,?_⟩
  · rw [show run (eSubK L) m s=run (subTop (hiReg L) (eRlow L) ((eBank L).take 128) L.core.cin (eZ0 L) (eU L) (eV L) (eKw L)) m s from rfl]
    rw [e1,v,rl,hr,f5,hS]
  · intro q hq
    rw [e1] at hq
    exact f q (fun x => hq (by simp [x])) (fun x => hq (by simp [x])) (fun x => hq (by simp [x]))

theorem eAddK_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E A S : Nat)
    (hS : regValue (hiReg L) base=S) (fit : (E+S)%2^130<2^128) :
    Triple (BState L base O E A) (eAddK L) (BState L base O ((E+S)%2^130) A) := by
  apply lift_e L hn base O E A _ (eAddK L)
  intro s m h
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  obtain ⟨f1,f2,f3,f4,f5⟩ := eK_facts L hw hn base hc O E A s.basis h
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have hl : (hiReg L).length=(eRlow L).length := by rw [hiReg_length L hw,rl]
  have bl : ((eBank L).take 127).length+1=(eRlow L).length := by
    have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
    simp [eBank,fp,rl]
  have hv : regValue (eReg L) s.basis=E := h.2.1
  rw [e1] at hv
  obtain ⟨p,v,f⟩ := addKnown_spec (hiReg L) (eRlow L) ((eBank L).take 127) L.core.cin (eZ0 L) (eU L) (eV L) (eKw L)
    (eK_nodup L hw hn 127 (by omega)) hl bl (by omega) s m f2 f1 f3 (f4 127)
    (by rw [hv,f5,hS,rl]; exact fit)
  refine ⟨p,?_,?_⟩
  · rw [show run (eAddK L) m s=run (addKnown (hiReg L) (eRlow L) ((eBank L).take 127) L.core.cin (eZ0 L) (eU L) (eV L) (eKw L)) m s from rfl]
    rw [e1,v,hv,f5,hS,rl]
  · intro q hq
    rw [e1] at hq
    exact f q (fun x => hq (by simp [x])) (fun x => hq (by simp [x])) (fun x => hq (by simp [x]))

theorem eSubK_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (eSubK L)+1=toffoliCount (eSub L (b1Src L)) ∧
    measurementCount (eSubK L)=measurementCount (eSub L (b1Src L)) := by
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have ls := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have old := subInPlace_counts (b1Src L) (eReg L) (eBank L) L.core.cin ls.1 ls.2
  have new := subInPlace_counts (hiReg L++[eZ0 L]) (eRlow L++[eU L]) ((eBank L).take 128) L.core.cin
    (by simp [hiReg_length L hw,rl]) (by simp [eBank,fp,rl])
  rw [eReg_length L hw] at old
  simp only [List.length_append,List.length_singleton,rl] at new
  have c1 : ∀ P : Program, toffoliCount (Instr.measureX (eKw L) [] [] :: P)=toffoliCount P ∧
      measurementCount (Instr.measureX (eKw L) [] [] :: P)=measurementCount P+1 := by
    intro P; simp [toffoliCount,measurementCount]; omega
  have c2 : toffoliCount [Instr.CX (eU L) (eV L)]=0 ∧ measurementCount [Instr.CX (eU L) (eV L)]=0 := by
    simp [toffoliCount,measurementCount]
  simp only [eSub,eSubK,subTop,(c1 _).1,(c1 _).2,toffoliCount_append,measurementCount_append,c2.1,c2.2] at old new ⊢
  omega

theorem eAddK_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (eAddK L)+2=toffoliCount (eAdd L (b1Src L)) ∧
    measurementCount (eAddK L)=measurementCount (eAdd L (b1Src L)) := by
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have ls := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have old := addInPlace_counts (b1Src L) (eReg L) (eBank L) L.core.cin ls.1 ls.2
  have t := addTop_counts (hiReg L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L) (eZ0 L) (eKw L)
    (by rw [hiReg_length L hw,rl]) (by simp [eBank,fp,rl]) (by omega)
  have mid := addInPlace_counts (hiReg L++[eZ0 L]) (eRlow L++[eU L]) ((eBank L).take 127++[eKw L]) L.core.cin
    (by simp [hiReg_length L hw,rl]) (by simp [eBank,fp,rl])
  rw [eReg_length L hw] at old
  simp only [List.length_append,List.length_singleton,rl] at mid
  have c1 : ∀ P : Program, toffoliCount (Instr.measureX (eKw L) [] [] :: P)=toffoliCount P ∧
      measurementCount (Instr.measureX (eKw L) [] [] :: P)=measurementCount P+1 := by
    intro P; simp [toffoliCount,measurementCount]; omega
  have c2 : ∀ P : Program, toffoliCount (Instr.CX (eU L) (eV L) :: P)=toffoliCount P ∧
      measurementCount (Instr.CX (eU L) (eV L) :: P)=measurementCount P := by
    intro P; simp [toffoliCount,measurementCount]
  simp only [eAdd,eAddK,addKnown,(c1 _).1,(c1 _).2,(c2 _).1,(c2 _).2] at old ⊢
  omega

theorem eK_mem (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    eKw L∈eBank L ∧ eU L∈eReg L ∧ eV L∈eReg L ∧ eZ0 L∈b1Src L ∧
    (∀q∈eRlow L,q∈eReg L) ∧ (∀q∈hiReg L,q∈b1Src L) := by
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [e3]; simp
  · rw [e1]; simp
  · rw [e1]; simp
  · rw [b1Src,e2]; simp
  · intro q hq; rw [e1]; simp [hq]
  · intro q hq; simp [b1Src,hq]

theorem eSubK_wires (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    wires (eSubK L)⊆wires (eSub L (b1Src L)) := by
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have ls := eSrc_length L hw (b1Src L) (Or.inl rfl)
  obtain ⟨m1,m2,m3,m4,m5,m6⟩ := eK_mem L hw
  rw [show eSubK L=[Instr.measureX (eKw L) [] []]++(subInPlace (hiReg L++[eZ0 L]) (eRlow L++[eU L])
      ((eBank L).take 128) L.core.cin++[Instr.CX (eU L) (eV L)]) from rfl,eSub,
    subInPlace_wires _ _ _ _ ls.1 ls.2,wires_append,wires_append,
    subInPlace_wires _ _ _ _ (by simp [hiReg_length L hw,rl]) (by simp [eBank,fp,rl])]
  intro q hq
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_singleton] at hq ⊢
  simp [wires,Instr.wires,correctionWires] at hq
  have tk : ∀q∈(eBank L).take 128,q∈eBank L := fun q h => List.mem_of_mem_take h
  rcases hq with h|h|h
  all_goals first
    | (subst h; tauto)
    | (rcases h with h|h <;> first | (subst h; tauto) | tauto)
    | (rcases h with h|((h|h)|(h|h))|h
       · exact Or.inl h
       · exact Or.inr (Or.inl (Or.inl (m6 q h)))
       · subst h; exact Or.inr (Or.inl (Or.inl m4))
       · exact Or.inr (Or.inl (Or.inr (m5 q h)))
       · subst h; exact Or.inr (Or.inl (Or.inr m2))
       · exact Or.inr (Or.inr (tk q h)))

theorem eAddK_wires (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    wires (eAddK L)⊆wires (eAdd L (b1Src L)) := by
  have ls := eSrc_length L hw (b1Src L) (Or.inl rfl)
  obtain ⟨m1,m2,m3,m4,m5,m6⟩ := eK_mem L hw
  have tk : ∀q∈(eBank L).take 127,q∈eBank L := fun q h => List.mem_of_mem_take h
  have aw := addTop_wires_sub (hiReg L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L)
  rw [show eAddK L=[Instr.measureX (eKw L) [] []]++([Instr.CX (eU L) (eV L)]++
      addTop (hiReg L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L)) from rfl,eAdd,
    addInPlace_wires _ _ _ _ ls.1 ls.2,wires_append,wires_append]
  intro q hq
  simp only [Finset.mem_union] at hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
  rcases hq with h|h|h
  · simp [wires,Instr.wires,correctionWires] at h; subst h; tauto
  · simp [wires,Instr.wires] at h; rcases h with h|h <;> subst h <;> tauto
  · have h2 := aw h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h2
    rcases h2 with h|h|((h|h)|h)
    · exact Or.inl h
    · subst h; exact Or.inr (Or.inl (Or.inr m2))
    · exact Or.inr (Or.inl (Or.inl (m6 q h)))
    · exact Or.inr (Or.inl (Or.inr (m5 q h)))
    · exact Or.inr (Or.inr (tk q h))

theorem eSubK_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (eSubK L) := by
  have nd := eK_nodup L hw hn 128 (le_refl _)
  have cnt := fun q => List.nodup_iff_count_le_one.mp nd q
  simp only [List.count_cons, List.count_append, List.count_nil] at cnt
  have uv : eU L≠eV L := by
    intro e; have h := cnt (eU L); rw [← e] at h
    simp only [beq_self_eq_true, if_true] at h; omega
  have nd2 : (L.core.cin :: (hiReg L++[eZ0 L]) ++ (eRlow L++[eU L]) ++ (eBank L).take 128).Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have h := cnt q
    simp only [List.cons_append, List.count_cons, List.count_append, List.count_nil]; omega
  rw [show eSubK L=[Instr.measureX (eKw L) [] []]++(subInPlace (hiReg L++[eZ0 L]) (eRlow L++[eU L])
      ((eBank L).take 128) L.core.cin++[Instr.CX (eU L) (eV L)]) from rfl]
  simp only [gatePhysical_append]
  refine ⟨by simp [GatePhysical, RecordedQuantum.PhysicalInstr], subInPlace_physical _ _ _ _ nd2, ?_⟩
  simp [GatePhysical, RecordedQuantum.PhysicalInstr, ECDSAAdd.ProperGate, uv]

theorem eAddK_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (eAddK L) := by
  have nd := eK_nodup L hw hn 127 (by omega)
  have cnt := fun q => List.nodup_iff_count_le_one.mp nd q
  simp only [List.count_cons, List.count_append, List.count_nil] at cnt
  have uv : eU L≠eV L := by
    intro e; have h := cnt (eU L); rw [← e] at h
    simp only [beq_self_eq_true, if_true] at h; omega
  have nd2 : (L.core.cin :: eU L :: (hiReg L ++ eRlow L ++ (eBank L).take 127)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have h := cnt q
    simp only [List.count_cons, List.count_append, List.count_nil]; omega
  rw [show eAddK L=[Instr.measureX (eKw L) [] []]++([Instr.CX (eU L) (eV L)]++
      addTop (hiReg L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L)) from rfl]
  simp only [gatePhysical_append]
  refine ⟨by simp [GatePhysical, RecordedQuantum.PhysicalInstr], ?_, addTop_physical _ _ _ _ _ nd2⟩
  simp [GatePhysical, RecordedQuantum.PhysicalInstr, ECDSAAdd.ProperGate, uv]

theorem eSubK_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (eSubK L)≤Challenge.gateSlots (eSub L (b1Src L)) := by
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have ls := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have old := addInPlace_slots_eq (b1Src L) (eReg L) (eBank L) L.core.cin ls.1 ls.2
  have new := addInPlace_slots_eq (hiReg L++[eZ0 L]) (eRlow L++[eU L]) ((eBank L).take 128) L.core.cin
    (by simp [hiReg_length L hw,rl]) (by simp [eBank,fp,rl])
  rw [eReg_length L hw] at old
  simp only [List.length_append,List.length_singleton,rl] at new
  simp only [eSub,eSubK,subTop,subInPlace,Challenge.gateSlots_append,Baselines.gateSlots_cons,
    Baselines.gateSlots_nil,Baselines.notRegister_gateSlots,Challenge.instructionSlots,List.length_append,
    List.length_singleton,List.length_nil,rl,eReg_length L hw]
  omega

theorem eAddK_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (eAddK L)≤Challenge.gateSlots (eAdd L (b1Src L)) := by
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have ls := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have old := addInPlace_slots_eq (b1Src L) (eReg L) (eBank L) L.core.cin ls.1 ls.2
  have new := addTop_slots_eq (hiReg L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L)
    (by rw [hiReg_length L hw,rl]) (by simp [eBank,fp,rl])
  rw [eReg_length L hw] at old
  rw [rl] at new
  simp only [eAdd,eAddK,addKnown,Baselines.gateSlots_cons,Challenge.instructionSlots,List.length_nil]
  omega

end ECDSAAdd.Entrant.ControlLoan1589BFFold
end

section
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace ECDSAAdd.Entrant.KnownTopAdd
open ECDSAAdd ECDSAAdd.Arithmetic Instr

/-- Subtract when the difference is known to fit `r` and the top wire above `u` is clear:
complement `r`, add with the final borrow hosted on `u`, complement back. -/
def subKnown (h r cs : List Wire) (cin u k : Wire) : Program :=
  Instr.measureX k [] [] :: (notRegister r ++ (addTop h r cs cin u ++ notRegister r))

theorem sub_known_arith (Rl H N U : Nat) (hU : U ≤ 1) (hN : 0 < N) (hR : Rl < N) (hH : H < N)
    (f1 : H ≤ Rl + N * U) (f2 : Rl + N * U - H < N) :
    U = (H + (N - 1 - Rl)) / N ∧
    (N - 1 - Rl + N * U + H) % (2 * N) < N ∧
    N - 1 - (N - 1 - Rl + N * U + H) % (2 * N) = Rl + N * U - H := by
  interval_cases U
  · simp only [Nat.mul_zero, Nat.add_zero] at f1 f2 ⊢
    have lt : H + (N - 1 - Rl) < N := by omega
    refine ⟨(Nat.div_eq_of_lt lt).symm, ?_, ?_⟩
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Nat.mul_one] at f1 f2 ⊢
    have d : (H + (N - 1 - Rl)) / N = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    refine ⟨d.symm, ?_, ?_⟩
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem add_host_arith (Y S N V : Nat) (hV : V ≤ 1) (hN : 0 < N) (hY : Y < 2 * N) (hS : S < N)
    (fit : (Y + 2 * N * V + S) % (4 * N) < 2 * N) : V = (S + Y) / (2 * N) := by
  interval_cases V
  · simp only [Nat.mul_zero, Nat.add_zero] at fit ⊢
    rw [Nat.mod_eq_of_lt (by omega)] at fit
    exact (Nat.div_eq_of_lt (by omega)).symm
  · simp only [Nat.mul_one] at fit ⊢
    by_cases hc : Y + 2 * N + S < 4 * N
    · rw [Nat.mod_eq_of_lt hc] at fit; omega
    · exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm

theorem subKnown_spec (h r cs : List Wire) (cin z u v k : Wire)
    (hn : (cin :: u :: v :: z :: k :: (h ++ r ++ cs)).Nodup)
    (hl : h.length = r.length) (hc : cs.length + 1 = r.length) (hr : 1 ≤ r.length)
    (s : State) (m : List Bool) (hk : s.basis k = false) (hz : s.basis z = false)
    (hcin : s.basis cin = false) (hcs : regValue cs s.basis = 0) (hv : s.basis v = false)
    (f1 : regValue h s.basis ≤ regValue (r ++ [u]) s.basis)
    (f2 : regValue (r ++ [u]) s.basis - regValue h s.basis < 2 ^ r.length) :
    (run (subKnown h r cs cin u k) m s).phase = s.phase ∧
    regValue (r ++ [u, v]) (run (subKnown h r cs cin u k) m s).basis =
      (regValue (r ++ [u, v]) s.basis + 2 ^ (r.length + 2) - regValue h s.basis) % 2 ^ (r.length + 2) ∧
    ∀ q, q ∉ r → q ≠ u → q ≠ v → (run (subKnown h r cs cin u k) m s).basis q = s.basis q := by
  have cnt := fun q => List.nodup_iff_count_le_one.mp hn q
  simp only [List.count_cons, List.count_append, List.count_nil] at cnt
  have ndT : (cin :: u :: z :: k :: (h ++ r ++ cs)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := cnt q
    simp only [List.count_cons, List.count_append, List.count_nil]
    omega
  have nd : (cin :: (h ++ [z]) ++ (r ++ [u]) ++ (cs ++ [k])).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := cnt q
    simp only [List.cons_append, List.count_cons, List.count_append, List.count_nil]
    omega
  have rnd : r.Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := cnt q
    omega
  have notin (q : Wire) (hq : q = cin ∨ q = u ∨ q = v ∨ q = z ∨ q = k ∨ q ∈ h ∨ q ∈ cs) : q ∉ r := by
    intro hm
    have c := cnt q
    have p := List.count_pos_iff.mpr hm
    rcases hq with e|e|e|e|e|e|e
    all_goals first
      | (subst e; simp only [beq_self_eq_true, if_true] at c; omega)
      | (have p2 := List.count_pos_iff.mpr e; omega)
  have vN : v ∉ r ++ [u] ++ h ++ [z] ++ cs ++ [k] ++ [cin] := by
    intro hm
    have c := cnt v
    have p := List.count_pos_iff.mpr hm
    simp only [List.count_cons, List.count_append, List.count_nil] at p
    simp only [beq_self_eq_true, if_true] at c p
    omega
  have uv : u ≠ v := fun e => vN (by simp [e])
  have l1 : (h ++ [z]).length = (r ++ [u]).length := by simp [hl]
  have l2 : (cs ++ [k]).length + 1 = (r ++ [u]).length := by simp [hc]
  have hN : 0 < 2 ^ r.length := by positivity
  have hS : regValue h s.basis < 2 ^ r.length := by rw [← hl]; exact regValue_lt _ _
  have hE : regValue r s.basis < 2 ^ r.length := regValue_lt _ _
  have p1 : (2 : Nat) ^ (r.length + 1) = 2 * 2 ^ r.length := by rw [pow_succ]; ring
  have p2 : (2 : Nat) ^ (r.length + 2) = 4 * 2 ^ r.length := by rw [pow_add]; ring
  rw [reg_snoc] at f1 f2
  obtain ⟨a1, a2, a3⟩ := sub_known_arith (regValue r s.basis) (regValue h s.basis) (2 ^ r.length)
    (if s.basis u = true then 1 else 0) (by split <;> omega) hN hE hS f1 f2
  -- the complemented state
  generalize hs1 : (⟨s.phase, fun w => if w ∈ r then !s.basis w else s.basis w⟩ : State) = s1
  have b1 : ∀ q, q ∉ r → s1.basis q = s.basis q := fun q hq => by rw [← hs1]; simp [hq]
  have ph1 : s1.phase = s.phase := by rw [← hs1]
  have reg1 (l : List Wire) (hq : ∀ q ∈ l, q ∉ r) : regValue l s1.basis = regValue l s.basis :=
    regValue_congr _ _ _ (fun q h' => b1 q (hq q h'))
  have rc : regValue r s1.basis = 2 ^ r.length - 1 - regValue r s.basis := by
    rw [← hs1]
    change regValue r (fun w => if w ∈ r then !s.basis w else s.basis w) = _
    rw [regValue_congr r _ (fun w => !s.basis w) (by intro w hw; simp [hw]), regValue_complement]
  have hv1 := reg1 h (fun q hq => notin q (by tauto))
  have hcs1 := reg1 cs (fun q hq => notin q (by tauto))
  have uE := b1 u (notin u (by tauto))
  have zE := b1 z (notin z (by tauto))
  have kE := b1 k (notin k (by tauto))
  have cE := b1 cin (notin cin (by tauto))
  have vE := b1 v (notin v (by tauto))
  have cs0 : regValue (cs ++ [k]) s1.basis = 0 := by
    rw [reg_snoc, hcs1, hcs, kE, hk]; simp
  have tr := addInPlace_cin_frame cin (h ++ [z]) (r ++ [u]) (cs ++ [k]) nd l1 l2 s1.basis false
    (cE.trans hcin) cs0 (regValue (r ++ [u]) s1.basis)
  rw [subKnown, noop_run _ _ _ _ hk, run_append (notRegister r), (notRegister_counts r).2,
    List.take_zero, List.drop_zero, notRegister_correct r rnd, hs1,
    run_append (addTop h r cs cin u)]
  have ta := addTop_run h r cs cin u z k hl hc hr ndT s1
    (m.tail.take (measurementCount (addTop h r cs cin u))) (zE.trans hz) (kE.trans hk)
    (fun q hq => (regValue_zero _ _).mp (hcs1.trans hcs) q hq)
    (by rw [hv1, rc, uE, cE, hcin]; simpa using a1)
  rw [ta]
  have tr' := tr s1 (m.tail.take (measurementCount (addTop h r cs cin u))) ⟨rfl, fun _ _ => rfl⟩
  generalize run (addInPlace (h ++ [z]) (r ++ [u]) (cs ++ [k]) cin)
    (m.tail.take (measurementCount (addTop h r cs cin u))) s1 = o at tr'
  obtain ⟨tp, tv, tf⟩ := tr'
  rw [notRegister_correct r rnd]
  have vo : o.basis v = false := (tf v (fun x => vN (by
    simp only [List.mem_append] at x ⊢; tauto))).trans (vE.trans hv)
  -- the value after the add
  simp only [reg_snoc] at tv
  rw [hv1, zE, hz, rc, uE] at tv
  simp only [List.length_append, List.length_singleton, Bool.false_eq_true, if_false,
    Nat.mul_zero, Nat.add_zero, Bool.toNat_false, p1] at tv
  have ro : regValue r o.basis < 2 ^ r.length := regValue_lt _ _
  have uo : o.basis u = false := by
    cases e : o.basis u
    · rfl
    · rw [e] at tv; simp only [if_true, Nat.mul_one] at tv; omega
  rw [uo] at tv
  simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at tv
  refine ⟨tp.trans ph1, ?_, ?_⟩
  · rw [reg_snoc2 r u v, reg_snoc2 r u v s.basis]
    simp only [List.mem_append, List.mem_singleton] at notin
    have nu : u ∉ r := notin u (by tauto)
    have nv : v ∉ r := notin v (by tauto)
    simp only [nu, nv, if_false, uo, vo, hv, Bool.false_eq_true, Nat.mul_zero, Nat.add_zero]
    rw [regValue_congr r _ (fun w => !o.basis w) (by intro w hw; simp [hw]), regValue_complement, tv, p2]
    rw [a3]
    have hr2 : regValue r s.basis + 2 ^ r.length * (if s.basis u = true then 1 else 0) - regValue h s.basis
        < 2 ^ r.length := f2
    rw [show regValue r s.basis + 2 ^ r.length * (if s.basis u = true then 1 else 0) + 4 * 2 ^ r.length -
        regValue h s.basis = (regValue r s.basis + 2 ^ r.length * (if s.basis u = true then 1 else 0) -
        regValue h s.basis) + 4 * 2 ^ r.length by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · intro q q1 q2 q3
    simp only [q1, if_false]
    rw [tf q (by simp [q1, q2])]
    exact b1 q q1

theorem subKnown_counts (h r cs : List Wire) (cin z u k : Wire)
    (hx : h.length = r.length) (hc : cs.length + 1 = r.length) (h1 : 1 ≤ r.length) :
    measurementCount (subKnown h r cs cin u k) =
      measurementCount (addInPlace (h ++ [z]) (r ++ [u]) (cs ++ [k]) cin) + 1 ∧
    toffoliCount (subKnown h r cs cin u k) + 1 =
      toffoliCount (addInPlace (h ++ [z]) (r ++ [u]) (cs ++ [k]) cin) := by
  have t := addTop_counts h r cs cin u z k hx hc h1
  have n := notRegister_counts r
  have c1 : toffoliCount [Instr.measureX k [] []] = 0 ∧ measurementCount [Instr.measureX k [] []] = 1 := by
    simp [toffoliCount, measurementCount]
  rw [show subKnown h r cs cin u k = [Instr.measureX k [] []] ++ (notRegister r ++
      (addTop h r cs cin u ++ notRegister r)) from rfl]
  simp only [toffoliCount_append, measurementCount_append, n.1, n.2, c1.1, c1.2]
  omega

theorem subKnown_physical (h r cs : List Wire) (cin u k : Wire)
    (hn : (cin :: u :: (h ++ r ++ cs)).Nodup) : GatePhysical (subKnown h r cs cin u k) := by
  rw [show subKnown h r cs cin u k = [Instr.measureX k [] []] ++ (notRegister r ++
      (addTop h r cs cin u ++ notRegister r)) from rfl]
  simp only [gatePhysical_append]
  exact ⟨by simp [GatePhysical, RecordedQuantum.PhysicalInstr], notRegister_physical r,
    addTop_physical _ _ _ _ _ hn, notRegister_physical r⟩

end ECDSAAdd.Entrant.KnownTopAdd

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KnownTopAdd

def whiLow (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.drop 128

/-- Adding `b1` back to `e = b0 - b1 + x` gives `b0 + x` exactly. -/
theorem back_arith (b0 b1 x : Nat) (h0 : b0 < 2^128) (h1 : b1 < 2^128) (hx : x < 2^35) :
    ((((b0+2^130-b1)%2^130+x)%2^130)+b1)%2^130 = b0+x := by
  omega

theorem back_facts (b0 x : Nat) (h0 : b0 < 2^128) (hx : x < 2^35) :
    b0+x<2^129 ∧ x≤b0+x ∧ b0+x-x<2^128 ∧ (b0+x+2^130-x)%2^130=b0 := by
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [show b0+x+2^130-x = b0+2^130 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- `eAdd L (b1Src L)` when the sum is below `2^129`: the carry into bit 129 is hosted on `v`. -/
def eAddB (L : CuccaroStreamedSquareWideLayout) : Program :=
  addTop (hiReg L ++ [eZ0 L]) (eRlow L ++ [eU L]) ((eBank L).take 128) L.core.cin (eV L)
/-- `eSub L (whiSrc L)` when the difference is below `2^128` and bit 129 is clear. -/
def eSubW (L : CuccaroStreamedSquareWideLayout) : Program :=
  subKnown (whiLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L) (eKw L)
theorem eW_shape (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    ∃ z1, eZ L = [eZ0 L, z1] ∧ whiSrc L = whiLow L ++ [eZ0 L, z1] ∧ b1Src L = hiReg L ++ [eZ0 L, z1] := by
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  exact ⟨z1, e2, by simp [whiSrc, whiLow, e2], by simp [b1Src, e2]⟩

theorem eW_nodup (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (j : Nat) (hj : j≤128) :
    (L.core.cin::eU L::eV L::eZ0 L::eKw L::(whiLow L++eRlow L++(eBank L).take j)).Nodup := by
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  obtain ⟨z1', _, ew, _⟩ := eW_shape L hw
  have b := eAdder_nodup L hn (whiSrc L) (Or.inr rfl)
  rw [ew,e1] at b
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have c := List.nodup_iff_count_le_one.mp b q
  have d := congrArg (List.count q) e3
  have f : ((eBank L).take j).count q≤((eBank L).take 128).count q := by
    have : (eBank L).take j=((eBank L).take 128).take j := by
      rw [List.take_take]; congr 1; omega
    rw [this]
    exact (List.take_sublist j _).count_le q
  simp only [List.count_cons,List.count_append,List.count_nil] at c d ⊢
  omega

theorem eB_nodup (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (z1 : Wire)
    (e2 : eZ L = [eZ0 L, z1]) :
    (L.core.cin :: eV L :: z1 :: eKw L :: ((hiReg L ++ [eZ0 L]) ++ (eRlow L ++ [eU L]) ++
      (eBank L).take 128)).Nodup := by
  obtain ⟨e1,_,e3⟩ := eShape L hw
  have b := eAdder_nodup L hn (b1Src L) (Or.inl rfl)
  rw [b1Src,e1,e2] at b
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have c := List.nodup_iff_count_le_one.mp b q
  have d := congrArg (List.count q) e3
  simp only [List.count_cons,List.count_append,List.count_nil] at c d ⊢
  omega

theorem eAddB_run (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E A S : Nat)
    (hS : regValue (hiReg L) base=S) (fit : (E+S)%2^130<2^129)
    (s : State) (m : List Bool) (h : BState L base O E A s.basis) :
    run (eAddB L) m s = run (eAdd L (b1Src L)) m s := by
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  obtain ⟨f1,f2,f3,f4,f5⟩ := eK_facts L hw hn base hc O E A s.basis h
  obtain ⟨_,_,_,padZ,_⟩ := zero_regs L hn base hc O E A s.basis h
  have z1m : z1 ∈ L.foldPad := by
    have : z1 ∈ eZ L := by rw [e2]; simp
    exact List.mem_of_mem_drop (List.mem_of_mem_take this)
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have hv : regValue (eReg L) s.basis=E := h.2.1
  have ee : eReg L = (eRlow L ++ [eU L]) ++ [eV L] := by rw [e1]; simp
  have bb : eBank L = (eBank L).take 128 ++ [eKw L] := e3
  have xb : b1Src L = (hiReg L ++ [eZ0 L]) ++ [z1] := by simp [b1Src, e2]
  have hy := regValue_lt (eRlow L ++ [eU L]) s.basis
  simp only [List.length_append, List.length_singleton, rl] at hy
  rw [ee, reg_snoc] at hv
  simp only [List.length_append, List.length_singleton, rl] at hv
  have hx : regValue (hiReg L ++ [eZ0 L]) s.basis = S := by
    rw [reg_snoc, f1, f5, hS]; simp
  have hSlt : S < 2^128 := by rw [← hS, ← hiReg_length L hw]; exact regValue_lt _ _
  rw [eAdd, xb, ee, bb]
  apply addTop_run (hiReg L ++ [eZ0 L]) (eRlow L ++ [eU L]) ((eBank L).take 128) L.core.cin (eV L) z1 (eKw L)
    (by simp [hiReg_length L hw, rl]) (by simp [eBank, fp, rl]) (by simp)
    (eB_nodup L hw hn z1 e2) s m (padZ _ z1m) f2
    (fun q hq => (regValue_zero _ _).mp (f4 128) q hq)
  rw [hx, f3]
  simp only [List.length_append, List.length_singleton, rl, Bool.false_eq_true, if_false, Nat.add_zero]
  have k := add_host_arith (regValue (eRlow L ++ [eU L]) s.basis) S (2^128)
    (if s.basis (eV L) = true then 1 else 0) (by split <;> omega) (by positivity) (by norm_num at hy ⊢; omega)
    hSlt (by rw [← hv] at fit; norm_num at fit ⊢; omega)
  rw [k]; norm_num

theorem eAddB_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E A S : Nat)
    (hS : regValue (hiReg L) base=S) (fit : (E+S)%2^130<2^129) :
    Triple (BState L base O E A) (eAddB L) (BState L base O ((E+S)%2^130) A) := by
  intro s m h
  rw [eAddB_run L hw hn base hc O E A S hS fit s m h]
  exact eAdd_step L hw hn base hc (b1Src L) (Or.inl rfl) O E A S
    (fun t h => (b1Src_value L hw hn base hc O E A t h).trans hS) s m h

theorem eSubW_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E A S : Nat)
    (hval : ∀t,BState L base O E A t → regValue (whiSrc L) t=S)
    (hE : E<2^129) (g1 : S≤E) (g2 : E-S<2^128) :
    Triple (BState L base O E A) (eSubW L) (BState L base O ((E+2^130-S)%2^130) A) := by
  apply lift_e L hn base O E A _ (eSubW L)
  intro s m h
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  obtain ⟨z1', e2', ew, _⟩ := eW_shape L hw
  obtain ⟨f1,f2,f3,f4,f5⟩ := eK_facts L hw hn base hc O E A s.basis h
  obtain ⟨_,_,_,padZ,_⟩ := zero_regs L hn base hc O E A s.basis h
  have z1m : z1' ∈ L.foldPad := by
    have : z1' ∈ eZ L := by rw [e2']; simp
    exact List.mem_of_mem_drop (List.mem_of_mem_take this)
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have wl : (whiLow L).length=128 := by simp [whiLow,hw.core.work]
  have hwv : regValue (whiLow L) s.basis = S := by
    have t := hval s.basis h
    rw [ew, regValue_append] at t
    have z0 : regValue [eZ0 L, z1'] s.basis = 0 := by
      simp [regValue, f1, padZ _ z1m]
    rw [z0] at t; simpa using t
  have hv : regValue (eReg L) s.basis=E := h.2.1
  rw [e1,reg_snoc2,rl] at hv
  have hv2 : s.basis (eV L)=false := by
    cases e : s.basis (eV L)
    · rfl
    · simp only [e,if_true] at hv
      norm_num at hv hE
      omega
  have hr : regValue (eRlow L ++ [eU L]) s.basis=E := by
    rw [reg_snoc, rl]
    simp only [hv2,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at hv
    exact hv
  obtain ⟨p,v,f⟩ := subKnown_spec (whiLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eZ0 L) (eU L) (eV L) (eKw L)
    (eW_nodup L hw hn 127 (by omega)) (by rw [wl,rl]) (by simp [eBank,fp,rl]) (by omega)
    s m f2 f1 f3 (f4 127) hv2 (by rw [hwv,hr]; exact g1) (by rw [hwv,hr,rl]; exact g2)
  refine ⟨p,?_,?_⟩
  · rw [show run (eSubW L) m s=run (subKnown (whiLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L) (eKw L)) m s from rfl]
    rw [e1,v,rl,hwv]
    have : regValue (eRlow L ++ [eU L, eV L]) s.basis = E := by rw [← e1]; exact h.2.1
    rw [this]
  · intro q hq
    rw [e1] at hq
    exact f q (fun x => hq (by simp [x])) (fun x => hq (by simp [x])) (fun x => hq (by simp [x]))

theorem eAddB_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (eAddB L)+1=toffoliCount (eAdd L (b1Src L)) ∧
    measurementCount (eAddB L)=measurementCount (eAdd L (b1Src L)) := by
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have t := addTop_counts (hiReg L ++ [eZ0 L]) (eRlow L ++ [eU L]) ((eBank L).take 128) L.core.cin (eV L) z1 (eKw L)
    (by simp [hiReg_length L hw, rl]) (by simp [eBank, fp, rl]) (by simp)
  have ee : eReg L = (eRlow L ++ [eU L]) ++ [eV L] := by rw [e1]; simp
  have xb : b1Src L = (hiReg L ++ [eZ0 L]) ++ [z1] := by simp [b1Src, e2]
  rw [eAdd, xb, ee, e3]
  exact ⟨t.2, t.1⟩

theorem eSubW_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (eSubW L)+2=toffoliCount (eSub L (whiSrc L)) ∧
    measurementCount (eSubW L)=measurementCount (eSub L (whiSrc L)) := by
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have wl : (whiLow L).length=128 := by simp [whiLow,hw.core.work]
  have ls := eSrc_length L hw (whiSrc L) (Or.inr rfl)
  have old := subInPlace_counts (whiSrc L) (eReg L) (eBank L) L.core.cin ls.1 ls.2
  have k := subKnown_counts (whiLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eZ0 L) (eU L) (eKw L)
    (by rw [wl, rl]) (by simp [eBank, fp, rl]) (by omega)
  have mid := addInPlace_counts (whiLow L++[eZ0 L]) (eRlow L++[eU L]) ((eBank L).take 127++[eKw L]) L.core.cin
    (by simp [wl,rl]) (by simp [eBank,fp,rl])
  rw [eReg_length L hw] at old
  simp only [List.length_append,List.length_singleton,rl] at mid
  simp only [eSub, eSubW] at old ⊢
  omega

theorem eW_mem (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀q∈whiLow L,q∈whiSrc L) := by
  obtain ⟨z1, _, ew, _⟩ := eW_shape L hw
  intro q hq; rw [ew]; simp [hq]

theorem eAddB_wires (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    wires (eAddB L)⊆wires (eAdd L (b1Src L)) := by
  have ls := eSrc_length L hw (b1Src L) (Or.inl rfl)
  obtain ⟨m1,m2,m3,m4,m5,m6⟩ := eK_mem L hw
  have tk : ∀q∈(eBank L).take 128,q∈eBank L := fun q h => List.mem_of_mem_take h
  have aw := addTop_wires_sub (hiReg L ++ [eZ0 L]) (eRlow L ++ [eU L]) ((eBank L).take 128) L.core.cin (eV L)
  rw [eAdd, addInPlace_wires _ _ _ _ ls.1 ls.2]
  intro q hq
  have h2 := aw (by simpa [eAddB] using hq)
  have h3 : q = L.core.cin ∨ q = eV L ∨ q ∈ hiReg L ∨ q = eZ0 L ∨ q ∈ eRlow L ∨ q = eU L ∨
      q ∈ (eBank L).take 128 := by
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_singleton,List.not_mem_nil,
      or_false] at h2
    tauto
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
  rcases h3 with h|h|h|h|h|h|h
  · exact Or.inl h
  · subst h; exact Or.inr (Or.inl (Or.inr m3))
  · exact Or.inr (Or.inl (Or.inl (m6 q h)))
  · subst h; exact Or.inr (Or.inl (Or.inl m4))
  · exact Or.inr (Or.inl (Or.inr (m5 q h)))
  · subst h; exact Or.inr (Or.inl (Or.inr m2))
  · exact Or.inr (Or.inr (tk q h))

theorem eSubW_wires (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    wires (eSubW L)⊆wires (eSub L (whiSrc L)) := by
  have ls := eSrc_length L hw (whiSrc L) (Or.inr rfl)
  obtain ⟨m1,m2,m3,m4,m5,m6⟩ := eK_mem L hw
  have m7 := eW_mem L hw
  have tk : ∀q∈(eBank L).take 127,q∈eBank L := fun q h => List.mem_of_mem_take h
  have aw := addTop_wires_sub (whiLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L)
  rw [show eSubW L=[Instr.measureX (eKw L) [] []]++(notRegister (eRlow L)++
      (addTop (whiLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L)++notRegister (eRlow L))) from rfl,
    eSub, subInPlace_wires _ _ _ _ ls.1 ls.2, wires_append, wires_append, wires_append, notRegister_wires]
  intro q hq
  simp only [Finset.mem_union] at hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
  rcases hq with h|h|h|h
  · simp [wires,Instr.wires,correctionWires] at h; subst h; tauto
  · simp only [List.mem_toFinset] at h; exact Or.inr (Or.inl (Or.inr (m5 q h)))
  · have h2 := aw h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h2
    rcases h2 with h|h|((h|h)|h)
    · exact Or.inl h
    · subst h; exact Or.inr (Or.inl (Or.inr m2))
    · exact Or.inr (Or.inl (Or.inl (m7 q h)))
    · exact Or.inr (Or.inl (Or.inr (m5 q h)))
    · exact Or.inr (Or.inr (tk q h))
  · simp only [List.mem_toFinset] at h; exact Or.inr (Or.inl (Or.inr (m5 q h)))

theorem eAddB_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (eAddB L) := by
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  have nd := eB_nodup L hw hn z1 e2
  have cnt := fun q => List.nodup_iff_count_le_one.mp nd q
  simp only [List.count_cons, List.count_append, List.count_nil] at cnt
  have nd2 : (L.core.cin :: eV L :: ((hiReg L ++ [eZ0 L]) ++ (eRlow L ++ [eU L]) ++ (eBank L).take 128)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have h := cnt q
    simp only [List.count_cons, List.count_append, List.count_nil]; omega
  exact addTop_physical _ _ _ _ _ nd2

theorem eSubW_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (eSubW L) := by
  have nd := eW_nodup L hw hn 127 (by omega)
  have cnt := fun q => List.nodup_iff_count_le_one.mp nd q
  simp only [List.count_cons, List.count_append, List.count_nil] at cnt
  have nd2 : (L.core.cin :: eU L :: (whiLow L ++ eRlow L ++ (eBank L).take 127)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have h := cnt q
    simp only [List.count_cons, List.count_append, List.count_nil]; omega
  exact subKnown_physical _ _ _ _ _ _ nd2

theorem eAddB_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (eAddB L)≤Challenge.gateSlots (eAdd L (b1Src L)) := by
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have ls := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have old := addInPlace_slots_eq (b1Src L) (eReg L) (eBank L) L.core.cin ls.1 ls.2
  have new := addTop_slots_eq (hiReg L ++ [eZ0 L]) (eRlow L ++ [eU L]) ((eBank L).take 128) L.core.cin (eV L)
    (by simp [hiReg_length L hw,rl]) (by simp [eBank,fp,rl])
  rw [eReg_length L hw] at old
  simp only [List.length_append, List.length_singleton, rl] at new
  simp only [eAdd,eAddB]
  omega

theorem eSubW_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (eSubW L)≤Challenge.gateSlots (eSub L (whiSrc L)) := by
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have wl : (whiLow L).length=128 := by simp [whiLow,hw.core.work]
  have ls := eSrc_length L hw (whiSrc L) (Or.inr rfl)
  have old := addInPlace_slots_eq (whiSrc L) (eReg L) (eBank L) L.core.cin ls.1 ls.2
  have new := addTop_slots_eq (whiLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L)
    (by rw [wl,rl]) (by simp [eBank,fp,rl])
  rw [eReg_length L hw] at old
  rw [rl] at new
  simp only [eSub,eSubW,subKnown,subInPlace,Challenge.gateSlots_append,Baselines.gateSlots_cons,
    Baselines.gateSlots_nil,Baselines.notRegister_gateSlots,Challenge.instructionSlots,List.length_nil,
    rl,eReg_length L hw]
  omega

end ECDSAAdd.Entrant.ControlLoan1589BFFold
end



-- Consolidated source module: QTop
section

/-!
Output-only `+flag·p` correction for the measured canonical modular fold `qprog`.

The final carry of `mappedConstAdd (some flag) extended …` (into the `high` bit) always
equals `flag` whenever `A<p` and `X<p`, so the correction can run on `out` only and the
top majority becomes a single `CX flag high`.  This file forks every square-stage
declaration whose statement mentions `qprog` (suffix `Tq`), with counts one smaller per call.
-/

section
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout RecordedQuantum
/-- `qprogTq` whose `+flag·p` correction runs on the 256 output bits only.  Under the canonical
preconditions of `qprog_frameTq` the carry out of that correction always equals `flag`, so the high
bit is set by one CNOT from `flag` instead of a 257th majority/erase pair (−1 Toffoli, −1 measurement). -/
def qprogTq (K : MeasuredCanonicalModLayout) (p : Nat) : Program :=
  notRegister K.out++K.sum++[.CX K.high K.flag,.X K.flag]++
    mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p++[.CX K.flag K.high]++
    [.X K.high,.X K.flag]++
    eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag

namespace QCore

/-- The output-only correction: `out += flag·c (mod 2^n)`, then `high ^= flag`. -/
theorem correctionT_frame (K : MeasuredCanonicalModLayout) (n c : Nat) (hw : K.Widths n)
    (hn : K.wires.Nodup) (hcb : c<2^n) (npos : 0<n) (base : BasisState)
    (O : Nat) (H F : Bool) (hc : ∀q∈K.carry,base q=false) (hi : base K.cin=false) :
    Triple (K.Frame base O H F)
      (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin c++[.CX K.flag K.high])
      (K.Frame base (((if F then c else 0)+O)%2^n) (H ^^ F) F) := by
  have away := K.flags_away hn
  have nd : (K.cin::(K.out++K.carry.take (K.out.length-1))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    have takeBound := (List.take_sublist (K.out.length-1) K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have srcAway : ∀q∈some K.flag,q∉K.cin::(K.out++K.carry.take (K.out.length-1)) := by
    intro q hq bad
    have eq : q=K.flag := by simpa [eq_comm] using hq
    subst q
    have h := List.nodup_iff_count.mp hn K.flag
    have pos := List.count_pos_iff.mpr bad
    have takeBound := (List.take_sublist (K.out.length-1) K.carry).count_le K.flag
    simp only [MeasuredCanonicalModLayout.wires,List.count_append,List.count_cons,List.count_nil,
      beq_self_eq_true,if_true] at h pos
    omega
  have carryLen : (K.carry.take (K.out.length-1)).length+1=K.out.length := by
    simp [hw.carry,hw.out]; omega
  have cBound : c<2^K.out.length := by rw [hw.out]; exact hcb
  have s2 := K.cx_high_frame hn base (((if F then c else 0)+O)%2^n) H F
  refine Triple.seq ?_ s2
  intro s m hf
  have clean := MeasuredCanonicalModLayout.Frame.clean K hn base s.basis O H F hf hc hi
  obtain ⟨phase,same,value⟩ := mappedConstAdd_correct (some K.flag) K.out (K.carry.take (K.out.length-1))
    K.cin c nd srcAway carryLen cBound s m (fun q hq => clean.1 q (List.mem_of_mem_take hq))
  refine ⟨phase,?_,?_,?_,?_⟩
  · rw [value,hf.1,clean.2,hw.out]
    simp only [mappedEnabled,Option.map_some,Option.getD_some,hf.2.2.1,Bool.toNat_false,Nat.add_zero]
  · exact (same K.high away.1).trans hf.2.1
  · exact (same K.flag (fun bad => away.2.1 (by simp [MeasuredCanonicalModLayout.extended,bad]))).trans hf.2.2.1
  · intro q hq
    have no : q∉K.out := fun bad => hq (by simp [MeasuredCanonicalModLayout.mutable,bad])
    exact (same q no).trans (hf.2.2.2 q hq)

theorem qprog_frameTq (K : MeasuredCanonicalModLayout) (n c p : Nat) (hw : K.Widths n)
    (hn : K.wires.Nodup) (npos : 0<n) (hpc : p+c=2^n) (hcp : 0<c)
    (base : BasisState) (A X : Nat) (ha : regValue K.src base=A)
    (hA : A<p) (hX : X<p) (hc : ∀q∈K.carry,base q=false) (hi : base K.cin=false) :
    Triple (K.Frame base X false false) (qprogTq K p)
      (K.Frame base ((A+(p-1-X))%p) false false) := by
  have bpos : 0<2^n := by positivity
  have hR : 2^n-1-X=(p-1-X)+c := by omega
  have sumBound : A+(2^n-1-X)<2^(n+1) := by rw [Nat.pow_succ]; omega
  have flagPred : decide (2^n≤A+(2^n-1-X))=decide ((A+(p-1-X))%p<A) := by
    have h := exactFold_recover_flag (p-1-X) A p (by omega) hA
    rw [Nat.add_comm (p-1-X) A] at h
    apply decide_eq_decide.mpr
    rw [h]
    omega
  generalize hr : decide (2^n≤A+(2^n-1-X))=r at flagPred
  have s1 := not_frame K n hw hn base X
  have s2 := K.sum_frame n hw hn base A (2^n-1-X) ha sumBound hc hi
  rw [hr] at s2
  have s3 : Triple (K.Frame base ((A+(2^n-1-X))%2^n) r false) [.CX K.high K.flag]
      (K.Frame base ((A+(2^n-1-X))%2^n) r r) := by
    simpa using K.cx_flag_frame hn base ((A+(2^n-1-X))%2^n) r false
  have s4 := x_flag_frame K hn base ((A+(2^n-1-X))%2^n) r r
  have s5 := correctionT_frame K n p hw hn (by omega) npos base ((A+(2^n-1-X))%2^n) r (!r) hc hi
  have vlow : ((if !r then p else 0)+(A+(2^n-1-X))%2^n)%2^n=(A+(p-1-X))%p := by
    cases r
    · have small : ¬2^n≤A+(2^n-1-X) := by simpa using hr
      have lt : A+(p-1-X)<p := by omega
      simp only [Bool.not_false,if_true]
      rw [Nat.mod_eq_of_lt (show A+(2^n-1-X)<2^n by omega),Nat.mod_eq_of_lt lt,
        show p+(A+(2^n-1-X))=(A+(p-1-X))+2^n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    · have big : 2^n≤A+(2^n-1-X) := by simpa using hr
      have ge : p≤A+(p-1-X) := by omega
      simp only [Bool.not_true,Bool.false_eq_true,if_false,Nat.zero_add]
      rw [Nat.mod_mod,Nat.mod_eq_sub_mod big,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_sub_mod ge,
        Nat.mod_eq_of_lt (by omega)]
      omega
  have hx : (r ^^ !r)=true := by cases r <;> rfl
  rw [vlow,hx] at s5
  have s6 := x_high_frame K hn base ((A+(p-1-X))%p) true (!r)
  have s7 := x_flag_frame K hn base ((A+(p-1-X))%p) (!true) (!r)
  simp only [Bool.not_true,Bool.not_not] at s7
  have s8 := K.erase_frame n hw hn npos base A ((A+(p-1-X))%p) false ha hc hi
  rw [←flagPred] at s8
  have all := ((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8
  simpa only [qprogTq,List.append_assoc,List.cons_append,List.singleton_append] using all

theorem qprog_correctTq (K : MeasuredCanonicalModLayout) (n c p : Nat) (hw : K.Widths n)
    (hn : K.wires.Nodup) (npos : 0<n) (hpc : p+c=2^n) (hcp : 0<c)
    (A X : Nat) (hA : A<p) (hX : X<p) (s : State) (m : List Bool)
    (ha : regValue K.src s.basis=A) (hx : regValue K.out s.basis=X)
    (hh : s.basis K.high=false) (hf : s.basis K.flag=false)
    (hc : ∀q∈K.carry,s.basis q=false) (hi : s.basis K.cin=false) :
    (run (qprogTq K p) m s).phase=s.phase ∧
    regValue K.out (run (qprogTq K p) m s).basis=(A+(p-1-X))%p ∧
    ∀q,q∉K.out → (run (qprogTq K p) m s).basis q=s.basis q := by
  have initial : K.Frame s.basis X false false s.basis := ⟨hx,hh,hf,fun _ _ => rfl⟩
  obtain ⟨phase,post⟩ := qprog_frameTq K n c p hw hn npos hpc hcp s.basis A X ha hA hX hc hi s m initial
  refine ⟨phase,post.1,?_⟩
  intro q hq
  by_cases high : q=K.high
  · subst q; exact post.2.1.trans hh.symm
  by_cases flag : q=K.flag
  · subst q; exact post.2.2.1.trans hf.symm
  exact post.2.2.2 q (by simpa only [MeasuredCanonicalModLayout.mutable,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or] using ⟨hq,high,flag⟩)

theorem qprog_countsTq (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (hn : 0<n) :
    toffoliCount (qprogTq K p)=3*n-2 ∧ measurementCount (qprogTq K p)=3*n-1 := by
  have extendedLength : K.extended.length=n+1 := by simp [MeasuredCanonicalModLayout.extended,hw.out]
  have sourceLength : (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)]).length=n+1 := by
    simp [mappedRead,hw.src]
  have sumCounts := mappedAdd_counts (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)])
    K.extended K.carry K.cin (sourceLength.trans extendedLength.symm)
    (by rw [hw.carry,extendedLength])
  have correction := mappedConstAdd_counts (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p
    (by simp [hw.carry,hw.out]; omega)
  have eraseCounts := eraseLtChain_counts K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
    (hw.out.trans hw.src.symm) (by simp [hw.carry,hw.out,hw.src]; omega)
  have nc := notRegister_counts K.out
  constructor
  · simp only [qprogTq,MeasuredCanonicalModLayout.sum,toffoliCount_append,toffoliCount]
    rw [sumCounts.1,correction.1,eraseCounts.1,nc.1,extendedLength,hw.src,hw.out]
    omega
  · simp only [qprogTq,MeasuredCanonicalModLayout.sum,measurementCount_append,measurementCount]
    rw [sumCounts.2,correction.2,eraseCounts.2,nc.2,extendedLength,hw.src,hw.out]
    omega

theorem qprog_supportTq (K : MeasuredCanonicalModLayout) (p : Nat) :
    ECDSAAdd.wires (qprogTq K p)⊆K.wires.toFinset := by
  have old := ECDSAAdd.Entrant.QCore.qprog_support K p
  simp only [ECDSAAdd.Entrant.qprog,MeasuredCanonicalModLayout.sum,wires_append,Finset.union_subset_iff] at old
  have hm : ECDSAAdd.wires (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p)⊆
      K.wires.toFinset := by
    apply (mappedConstAdd_wires_subset _ _ _ _ _).trans
    intro q hq
    have tk : q∈K.carry.take (K.out.length-1) → q∈K.carry := List.mem_of_mem_take
    simp only [List.mem_toFinset,List.mem_append,Option.toList_some,List.mem_cons,List.not_mem_nil,
      or_false,MeasuredCanonicalModLayout.wires] at hq ⊢
    tauto
  have g : ECDSAAdd.wires [Instr.CX K.flag K.high]⊆K.wires.toFinset := by
    intro q hq; simp [ECDSAAdd.wires,Instr.wires,MeasuredCanonicalModLayout.wires] at hq ⊢; tauto
  simp only [qprogTq,MeasuredCanonicalModLayout.sum,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨old.1.1.1.1.1,old.1.1.1.1.2⟩,old.1.1.1.2⟩,hm⟩,g⟩,old.1.2⟩,old.2⟩

theorem qprog_physicalTq (K : MeasuredCanonicalModLayout) (p : Nat) (hn : K.wires.Nodup) :
    GatePhysical (qprogTq K p) := by
  have old := ECDSAAdd.Entrant.QCore.qprog_physical K p hn
  simp only [ECDSAAdd.Entrant.qprog,gatePhysical_append] at old
  have hf : K.flag≠K.high := fun h => (K.flags_away hn).2.2.2 h.symm
  have nd : (K.cin::K.out++K.carry.take (K.out.length-1)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    have takeBound := (List.take_sublist (K.out.length-1) K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hm : GatePhysical (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p) := by
    apply mappedConstAdd_physical _ _ _ _ _ nd
    intro q hq bad
    have eq : q=K.flag := by simpa [eq_comm] using hq
    subst q
    have h := List.nodup_iff_count.mp hn K.flag
    have pos := List.count_pos_iff.mpr bad
    have takeBound := (List.take_sublist (K.out.length-1) K.carry).count_le K.flag
    simp only [MeasuredCanonicalModLayout.wires,List.count_append,List.count_cons,List.count_nil,
      beq_self_eq_true,if_true] at h pos
    omega
  have g : GatePhysical [Instr.CX K.flag K.high] := by
    simpa [GatePhysical,PhysicalInstr,ProperGate] using hf
  simp only [qprogTq,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨old.1.1.1.1.1,old.1.1.1.1.2⟩,old.1.1.1.2⟩,hm⟩,g⟩,old.1.2⟩,old.2⟩

theorem qprog_gateSlotsTq (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) :
    Challenge.gateSlots (qprogTq K p)≤67*n+41 := by
  have he : K.extended.length = n+1 := by simp [MeasuredCanonicalModLayout.extended, hw.out]
  have hs := Baselines.mappedAdd_gateSlots_le (mappedRead K.src false++[{wire:=none,flip:=false}])
    K.extended K.carry K.cin
  simp only [List.length_append, List.length_cons, List.length_nil, mappedRead_length, hw.src] at hs
  have hm := Baselines.mappedConst_gateSlots_le (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p
  have hb := Baselines.eraseLt_gateSlots_le K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
  rw [hw.out] at hb hm
  simp only [qprogTq,MeasuredCanonicalModLayout.sum,Challenge.gateSlots_append,Baselines.gateSlots_cons,
    Baselines.gateSlots_nil,Challenge.instructionSlots,Baselines.notRegister_gateSlots,hw.out]
  omega

end QCore

namespace QCore
end QCore
def measuredFoldQTq (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold) : Program :=
  copyRegister none f.src (L.foldDestination f)++qprogTq L.measuredCore SquareReduction.p++
    copyRegister none f.src (L.foldDestination f)


theorem qCopiedFold_correctTq (K : MeasuredCanonicalModLayout)
    (n c p : Nat) (hw : K.Widths n) (src : List Wire) (shift : Nat)
    (hn : (src++K.wires).Nodup) (hlen : shift+src.length≤n)
    (npos : 0<n) (hpc : p+c=2^n) (hcpos : 0<c)
    (O : Nat) (hO : O<p) (s : State) (records : List Bool)
    (hcanonical : regValue src s.basis*2^shift<p)
    (hzero : regValue K.src s.basis=0) (ho : regValue K.out s.basis=O)
    (hhigh : s.basis K.high=false) (hmod : s.basis K.flag=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) (hcin : s.basis K.cin=false) :
    (run (copySlice src K.src shift++qprogTq K p++copySlice src K.src shift) records s).phase=s.phase ∧
    regValue K.out (run (copySlice src K.src shift++qprogTq K p++copySlice src K.src shift) records s).basis=
      (regValue src s.basis*2^shift+(p-1-O))%p ∧
    ∀q,q∉K.out → (run (copySlice src K.src shift++qprogTq K p++copySlice src K.src shift) records s).basis q=
      s.basis q := by
  let dst := (K.src.drop shift).take src.length
  let cp := copySlice src K.src shift
  let kernel := qprogTq K p
  let S := regValue src s.basis*2^shift
  let u := run cp [] s
  let v := run kernel (records.take (measurementCount kernel)) u
  let out := run cp (records.drop (measurementCount kernel)) v
  have coreNd : K.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have nd : (src++K.src).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have bound : shift+src.length≤K.src.length := by simpa [hw.src] using hlen
  have len : dst.length=src.length := by simp [dst];omega
  have dstSub (q : Wire) (hq : q∈dst) : q∈K.src :=
    List.mem_of_mem_drop (List.mem_of_mem_take hq)
  have notWork (q : Wire) (hq : q∈src++K.out++K.carry++[K.high,K.cin,K.flag]) : q∉K.src := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have notDst (q : Wire) (hq : q∈src++K.out++K.carry++[K.high,K.cin,K.flag]) : q∉dst :=
    fun bad => notWork q hq (dstSub q bad)
  have notOut (q : Wire) (hq : q∈src++K.src++K.carry++[K.high,K.cin,K.flag]) : q∉K.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have copy := copySlice_zero_correct src K.src shift nd bound s [] hzero
  have first : u.phase=s.phase ∧ regValue K.src u.basis=S ∧
      ∀q,q∉dst → u.basis q=s.basis q := copy
  have cleanCarry : ∀q∈K.carry,u.basis q=false := by
    intro q hq
    exact (first.2.2 q (notDst q (by simp [hq]))).trans (hcarry q hq)
  have keep (q : Wire) (hq : q∈K.out++[K.high,K.cin,K.flag]) : u.basis q=s.basis q :=
    first.2.2 q (notDst q (by simp only [List.mem_append] at hq ⊢; tauto))
  have outU : regValue K.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans ho
  have body := QCore.qprog_correctTq K n c p hw coreNd npos hpc hcpos S O hcanonical hO u
    (records.take (measurementCount kernel)) first.2.1 outU
    ((keep K.high (by simp)).trans hhigh)
    ((keep K.flag (by simp)).trans hmod) cleanCarry ((keep K.cin (by simp)).trans hcin)
  have nd2 : (src++dst).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp nd q
    have ht := (List.take_sublist src.length (K.src.drop shift)).count_le q
    have hd := (List.drop_sublist shift K.src).count_le q
    simp only [List.count_append] at h ⊢
    dsimp only [dst]
    omega
  have dst0 : regValue dst s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hzero q (dstSub q hq))
  have copied := copyRegister_correct none src dst len.symm nd2 (by simp) s []
  have dstU : regValue dst u.basis=regValue src s.basis := by
    simpa [u,cp,copySlice,dst0,copyValue] using copied.2.2
  have dstV : regValue dst v.basis=regValue src s.basis :=
    (regValue_congr _ _ _ (fun q hq => body.2.2 q (notOut q (by simp [dstSub q hq])))).trans dstU
  have srcV : regValue src v.basis=regValue src s.basis := by
    apply regValue_congr
    intro q hq
    exact (body.2.2 q (notOut q (by simp [hq]))).trans (first.2.2 q (notDst q (by simp [hq])))
  have last := copyRegister_correct none src dst len.symm nd2 (by simp) v (records.drop (measurementCount kernel))
  have lastValue : regValue dst out.basis=0 := by
    simpa [out,cp,copySlice,dstV,srcV,copyValue] using last.2.2
  have finalValue : regValue K.out out.basis=(S+(p-1-O))%p :=
    (regValue_congr _ _ _ (fun q hq => last.2.1 q (notDst q (by simp [hq])))).trans body.2.1
  have final : out.phase=s.phase ∧ regValue K.out out.basis=(S+(p-1-O))%p ∧
      ∀q,q∉K.out → out.basis q=s.basis q := by
    refine ⟨last.1.trans (body.1.trans first.1),finalValue,?_⟩
    intro q hq
    by_cases inside : q∈dst
    · exact ((regValue_zero _ _).mp lastValue q inside).trans ((regValue_zero _ _).mp dst0 q inside).symm
    · exact (last.2.1 q inside).trans ((body.2.2 q hq).trans (first.2.2 q inside))
  have cm : measurementCount cp=0 := (copyNone_free src dst).2
  simpa [cp,kernel,u,v,out,S,run_append,cm] using final


theorem measuredFoldQ_eqTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold) :
    measuredFoldQTq L f=copySlice f.src L.measuredCore.src f.shift++qprogTq L.measuredCore SquareReduction.p++
      copySlice f.src L.measuredCore.src f.shift := by
  simp [measuredFoldQTq,foldDestination,copySlice,measuredCore,List.append_assoc]


theorem measuredFoldQ_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (f : MeasuredSquareFold)
    (hv : L.MeasuredFoldView base f) (hcan : f.canonical=true) (hc : L.PairClean base)
    (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (measuredFoldQTq L f)
      (SquareFrame L.core.out base ((measuredFoldPayload base f+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  have away (q : Wire) (hq : q∈f.src) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    have count := hv.count q
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,
      List.count_cons,List.count_nil] at h
    omega
  have inter : (f.src++L.measuredCore.wires).Nodup := by
    have h := L.measuredFold_interfaces hn f.src hv.count
    exact h.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
  intro s m hf
  have source : regValue f.src s.basis=regValue f.src base :=
    regValue_congr _ _ _ (fun q hq => hf.2 q (away q hq))
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  rw [measuredFoldQ_eqTq L hw f]
  have result := qCopiedFold_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p
    (L.measuredCore_widths hw) f.src f.shift inter hv.span (by decide)
    (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    (by norm_num [SquareReduction.c]) O hO s m (by rw [source];exact hv.canonical hcan)
    clean.work hf.1 clean.outHigh clean.modFlag (L.measuredFold_carry_clean s.basis clean) clean.cin
  refine ⟨result.1,?_,?_⟩
  · simpa [measuredFoldPayload,source] using result.2.1
  · intro q hq
    exact (result.2.2 q hq).trans (hf.2 q hq)


theorem measuredFoldQ_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold) :
    toffoliCount (measuredFoldQTq L f)=766 ∧ measurementCount (measuredFoldQTq L f)=767 := by
  have copy := copyNone_free f.src (L.foldDestination f)
  have core := QCore.qprog_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)
  simp only [measuredFoldQTq,toffoliCount_append,measurementCount_append,copy.1,copy.2,core.1,core.2]
  constructor <;> trivial


theorem measuredFoldQ_supportTq (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (f : MeasuredSquareFold) (hs : ∀q∈f.src,q∈L.core.product) :
    ECDSAAdd.wires (measuredFoldQTq L f)⊆(control::L.wires).toFinset := by
  have cp := copyRegister_wires_subset none f.src (L.foldDestination f)
  have embed : (Option.toList (none : Option Wire)++f.src++L.foldDestination f).toFinset⊆
      (control::L.wires).toFinset := by
    intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
    rcases hq with hq|hq
    · have h := hs q hq
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
    · have h := List.mem_of_mem_drop (List.mem_of_mem_take hq)
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
  have copy := cp.trans embed
  have core := (QCore.qprog_supportTq L.measuredCore SquareReduction.p).trans (measuredCore_in L control)
  simp only [measuredFoldQTq,wires_append,Finset.union_subset_iff]
  exact ⟨⟨copy,core⟩,copy⟩


theorem measuredFoldQ_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (f : MeasuredSquareFold)
    (hs : ∀ q, f.src.count q ≤ L.core.product.count q) : GatePhysical (measuredFoldQTq L f) := by
  have inter : (f.src++L.measuredCore.wires).Nodup := by
    have h := L.measuredFold_interfaces hn f.src hs
    exact h.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
  have coreNd : L.measuredCore.wires.Nodup := (List.nodup_append'.mp inter).2.1
  have cp : GatePhysical (copyRegister none f.src (L.foldDestination f)) := by
    apply copyRegister_physical
    · apply List.nodup_iff_count.mpr
      intro q; have h := List.nodup_iff_count.mp inter q
      have ht := (List.take_sublist f.src.length (L.core.work.drop f.shift)).count_le q
      have hd := (List.drop_sublist f.shift L.core.work).count_le q
      simp only [foldDestination,measuredCore,MeasuredCanonicalModLayout.wires,List.count_append] at h ht hd ⊢
      omega
    · simp
  simp only [measuredFoldQTq,gatePhysical_append]
  exact ⟨⟨cp,QCore.qprog_physicalTq _ _ coreNd⟩,cp⟩


theorem measuredFoldQ_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold) :
    Challenge.gateSlots (measuredFoldQTq L f) ≤ 36000 := by
  have hc := QCore.qprog_gateSlotsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw)
  have hd : (L.foldDestination f).length ≤ 256 := by
    simp only [CuccaroStreamedSquareWideLayout.foldDestination, List.length_take, List.length_drop, hw.core.work]; omega
  have hcopy := Nat.min_le_right f.src.length (L.foldDestination f).length
  simp only [measuredFoldQTq, Challenge.gateSlots_append, Baselines.copyRegister_gateSlots]
  omega


def accFoldQTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  fillIn L a++qprogTq L.measuredCore SquareReduction.p++fillOut L a


def accPriceQTq (a : AccItem) : Nat := 4*Acc.sbuildT 33 a.pre+2*Acc.sbuildT 163 a.terms+766+
  (if a.pre=[] then 0 else 4*127)


theorem accFoldQ_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFoldQTq L a)
      (SquareFrame L.core.out base ((Acc.accVal base 0 a.spec+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillIn_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFoldQTq,List.append_assoc,run_append,run_append]
  let mb := measurementCount (fillIn L a)
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let u := run (fillIn L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u.basis q=b0 q :=
    eu.2.2 q (accReg_away L hn q hq)
  have workU : regValue L.core.work u.basis=A := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using eu.2.1
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A<SquareReduction.p := lt_of_lt_of_le hA (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A O hAp hO u ((m.drop mb).take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) ((m.drop mb).take mk) u
  change v.phase=u.phase ∧ regValue L.core.out v.basis=(A+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u.basis q at ek
  let base2 : BasisState := fun q => if q∈L.core.out then v.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have frame2 : SquareFrame (accReg L) base2 A v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans eu.2.1
    · intro q hq
      by_cases ho : q∈L.core.out
      · simp [base2,ho]
      · rw [b2off q ho,ek.2.2 q ho]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := fillOut_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v ((m.drop mb).drop mk) frame2
  refine ⟨eo.1.trans (ek.1.trans eu.1),?_,?_⟩
  · have e : regValue L.core.out (run (fillOut L a) ((m.drop mb).drop mk) v).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq


theorem accFoldQ_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    toffoliCount (accFoldQTq L a)=accPriceQTq a ∧ measurementCount (accFoldQTq L a)=accPriceQTq a+1 := by
  have b := Acc.sbuild_counts (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms
    (fun f hf => fitsLen_of L hw f (ok f hf))
  have w := Acc.sbuild_counts (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre
    (fun f hf => fitsLen33_of L hw f (okP f hf))
  have k := QCore.qprog_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)
  have sp := split_counts L hw a
  simp only [accFoldQTq,fillIn,fillOut,tempIn,tempOut,accPriceQTq,toffoliCount_append,measurementCount_append,
    sp.1.1,sp.1.2,sp.2.1,sp.2.2]
  split <;> omega


theorem accFoldQ_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    ECDSAAdd.wires (accFoldQTq L a)⊆(control::L.wires).toFinset := by
  have full := accFold_support L hw hn control a cnt ok cntP okP
  simp only [accFold,wires_append,Finset.union_subset_iff] at full
  have core := (QCore.qprog_supportTq L.measuredCore SquareReduction.p).trans (measuredCore_in L control)
  simp only [accFoldQTq,wires_append,Finset.union_subset_iff]
  exact ⟨⟨full.1.1,core⟩,full.2⟩


theorem accFoldQ_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQTq L a) := by
  have full := accFold_physical L hw hn a cnt ok cntP okP
  simp only [accFold,gatePhysical_append] at full
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  simp only [accFoldQTq,gatePhysical_append]
  exact ⟨⟨full.1.1,QCore.qprog_physicalTq _ _ coreNd⟩,full.2⟩


theorem accFoldQ_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    Challenge.gateSlots (accFoldQTq L a)≤2*(a.terms.length*(14*163))+4*(a.pre.length*(14*33))+(67*256+41)+7000 := by
  have full := accFold_gateSlots L hw a ok okP
  have k := Baselines.canonicalMod_gateSlots_le L.measuredCore 256 SquareReduction.c SquareReduction.p
    (L.measuredCore_widths hw)
  have q := QCore.qprog_gateSlotsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw)
  have b := Acc.sbuild_gateSlots (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms
    (fun f hf => fitsLen_of L hw f (ok f hf))
  have w := Acc.sbuild_gateSlots (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre
    (fun f hf => fitsLen33_of L hw f (okP f hf))
  have sp := split_gateSlots L hw a
  simp only [accFoldQTq,fillIn,fillOut,tempIn,tempOut,Challenge.gateSlots_append]
  omega


def mixProgQTq (L : CuccaroStreamedSquareWideLayout) : MixItem → Program
  | .inl f => if f.canonical then measuredFoldQTq L f else L.reflectOutput++L.measuredFold f
  | .inr a => accFoldQTq L a


def mixFoldsQTq (L : CuccaroStreamedSquareWideLayout) : Bool → List MixItem → Program
  | _,[] => []
  | o,i::is => (if o=mixNeg i then mixProg L i else mixProgQTq L i)++mixFoldsQTq L (mixNeg i) is


theorem mixProgQ_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (i : MixItem) (hv : MixView L base i) (hc : L.PairClean base)
    (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (mixProgQTq L i)
      (SquareFrame L.core.out base ((mixPayload base i+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  cases i with
  | inl f =>
    by_cases hcan : f.canonical=true
    · simp only [mixProgQTq,hcan,if_true]
      exact measuredFoldQ_frameTq L hw hn base f hv hcan hc O hO
    · simp only [mixProgQTq,hcan,Bool.false_eq_true,if_false]
      have r := L.measuredReflection_frame hw hn base hc O hO
      have f' := L.measuredFold_frame hw hn base f hv hc (SquareReduction.p-1-O) (by omega)
      exact r.seq f'
  | inr a => exact accFoldQ_frameTq L hw hn base a hv hc O hO


theorem mixFoldsQ_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (hc : L.PairClean base)
    (o : Bool) (O : Nat) (hO : O<SquareReduction.p) (items : List MixItem)
    (views : ∀i∈items,MixView L base i) :
    Triple (SquareFrame L.core.out base O) (mixFoldsQTq L o items)
      (SquareFrame L.core.out base (mixValue base o O items)) := by
  induction items generalizing o O with
  | nil => intro s m hf;exact ⟨rfl,hf⟩
  | cons i is ih =>
    let R := if o=mixNeg i then O else SquareReduction.p-1-O
    have step : Triple (SquareFrame L.core.out base O)
        (if o=mixNeg i then mixProg L i else mixProgQTq L i)
        (SquareFrame L.core.out base ((mixPayload base i+R)%SquareReduction.p)) := by
      by_cases same : o=mixNeg i
      · simp only [same,if_true,R]
        exact mixProg_frame L hw hn base i (views i (by simp)) hc O hO
      · simp only [same,if_false,R]
        exact mixProgQ_frameTq L hw hn base i (views i (by simp)) hc O hO
    have ob : (mixPayload base i+R)%SquareReduction.p<SquareReduction.p :=
      Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    have tail := ih (mixNeg i) _ ob (by intro j hj;exact views j (by simp [hj]))
    exact step.seq tail


def mixFoldsQTTq : Bool → List MixItem → Nat
  | _,[] => 0
  | o,i::is => (if o=mixNeg i then
        (match i with
          | .inl f => 1023+(if f.canonical then 0 else 1022)
          | .inr a => accPrice a)
      else
        (match i with
          | .inl f => if f.canonical then 766 else 255+1023+1022
          | .inr a => accPriceQTq a))+mixFoldsQTTq (mixNeg i) is


def mixFoldsQMTq : Bool → List MixItem → Nat
  | _,[] => 0
  | o,i::is => (if o=mixNeg i then
        (match i with
          | .inl f => 1023+(if f.canonical then 0 else 1020)
          | .inr a => accPrice a)
      else
        (match i with
          | .inl f => if f.canonical then 767 else 255+1023+1020
          | .inr a => accPriceQTq a+1))+mixFoldsQMTq (mixNeg i) is


theorem mixFoldsQ_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    toffoliCount (mixFoldsQTq L o items)=mixFoldsQTTq o items ∧
    measurementCount (mixFoldsQTq L o items)=mixFoldsQMTq o items := by
  induction items generalizing o with
  | nil => simp [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,toffoliCount,measurementCount]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have reflect := (L.measured_small_operation_counts hw).2.2
    have hi := hst i (by simp)
    cases i with
    | inl f =>
      have op := L.measuredFold_counts hw f
      have opq := measuredFoldQ_countsTq L hw f
      by_cases same : o=mixNeg (.inl f)
      · simp only [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,same,if_true,mixProg,toffoliCount_append,
          measurementCount_append,op.1,op.2,t.1,t.2]
        exact ⟨trivial,trivial⟩
      · cases hcan : f.canonical
        · simp only [hcan,Bool.false_eq_true,if_false] at op
          simp only [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,same,if_false,mixProgQTq,hcan,Bool.false_eq_true,
            toffoliCount_append,measurementCount_append,op.1,op.2,reflect.1,reflect.2,t.1,t.2]
          first | exact ⟨trivial,trivial⟩ | (constructor <;> omega)
        · simp only [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,same,if_false,mixProgQTq,hcan,
            if_true,toffoliCount_append,measurementCount_append,opq.1,opq.2,t.1,t.2]
          first | exact ⟨trivial,trivial⟩ | (constructor <;> omega)
    | inr a =>
      have op := accFold_counts L hw a hi.2.1 hi.2.2.2
      have opq := accFoldQ_countsTq L hw a hi.2.1 hi.2.2.2
      by_cases same : o=mixNeg (.inr a)
      · simp only [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,same,if_true,mixProg,toffoliCount_append,
          measurementCount_append,op.1,op.2,t.1,t.2]
        exact ⟨trivial,trivial⟩
      · simp only [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,same,if_false,mixProgQTq,toffoliCount_append,
          measurementCount_append,opq.1,opq.2,t.1,t.2]
        first | exact ⟨trivial,trivial⟩ | (constructor <;> omega)


theorem mixFoldsQ_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    ECDSAAdd.wires (mixFoldsQTq L o items)⊆(control::L.wires).toFinset := by
  induction items generalizing o with
  | nil => simp [mixFoldsQTq,ECDSAAdd.wires]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have reflect : ECDSAAdd.wires L.reflectOutput⊆(control::L.wires).toFinset :=
      (L.measured_small_support control).2.2.1
    have hi := hst i (by simp)
    have mem (f : MeasuredSquareFold) (h : ∀q,f.src.count q≤L.core.product.count q) :
        ∀q∈f.src,q∈L.core.product := by
      intro q hq
      have pos := List.count_pos_iff.mpr hq
      have b := h q
      exact List.count_pos_iff.mp (by omega)
    have hprog : ECDSAAdd.wires (mixProg L i)⊆(control::L.wires).toFinset := by
      cases i with
      | inl f => exact L.measuredFold_support control f (mem f hi)
      | inr a => exact accFold_support L hw hn control a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    have hprogQ : ECDSAAdd.wires (mixProgQTq L i)⊆(control::L.wires).toFinset := by
      cases i with
      | inl f =>
        by_cases hcan : f.canonical=true
        · simp only [mixProgQTq,hcan,if_true]
          exact measuredFoldQ_supportTq L control f (mem f hi)
        · simp only [mixProgQTq,hcan,Bool.false_eq_true,if_false,wires_append,Finset.union_subset_iff]
          exact ⟨reflect,L.measuredFold_support control f (mem f hi)⟩
      | inr a => exact accFoldQ_supportTq L hw hn control a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    by_cases same : o=mixNeg i <;>
      simp only [mixFoldsQTq,same,if_false,if_true,wires_append,Finset.union_subset_iff] <;> tauto


theorem mixFoldsQ_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    GatePhysical (mixFoldsQTq L o items) := by
  induction items generalizing o with
  | nil => simp [mixFoldsQTq,GatePhysical]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have hi := hst i (by simp)
    have hprog : GatePhysical (mixProg L i) := by
      cases i with
      | inl f => exact L.measuredFold_physical hw hn f hi
      | inr a => exact accFold_physical L hw hn a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    have hprogQ : GatePhysical (mixProgQTq L i) := by
      cases i with
      | inl f =>
        by_cases hcan : f.canonical=true
        · simp only [mixProgQTq,hcan,if_true]
          exact measuredFoldQ_physicalTq L hw hn f hi
        · simp only [mixProgQTq,hcan,Bool.false_eq_true,if_false,gatePhysical_append]
          exact ⟨L.reflectOutput_physical hn,L.measuredFold_physical hw hn f hi⟩
      | inr a => exact accFoldQ_physicalTq L hw hn a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    simp only [mixFoldsQTq,gatePhysical_append]
    refine ⟨?_,t⟩
    split
    · exact hprog
    · exact hprogQ


theorem mixFoldsQ_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) (B : Nat)
    (hB : ∀i∈items,∀a,i=.inr a → a.terms.length≤B ∧ a.pre.length≤4) :
    Challenge.gateSlots (mixFoldsQTq L o items)≤ items.length*(41000+2*(B*(14*163))+(67*256+41)) := by
  induction items generalizing o with
  | nil => simp [mixFoldsQTq,Challenge.gateSlots]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj])) (fun j hj a e => hB j (by simp [hj]) a e)
    have hr := (Baselines.streamedFrames_gateSlots_le L hw).2.2
    have hi := hst i (by simp)
    have hprog : Challenge.gateSlots (mixProg L i)≤36000+2*(B*(14*163))+(66*256+37) := by
      cases i with
      | inl f => have := Baselines.measuredFold_gateSlots_le L hw f; simp only [mixProg]; omega
      | inr a =>
        have h1 := accFold_gateSlots L hw a hi.2.1 hi.2.2.2
        have h2 := hB (.inr a) (by simp) a rfl
        have h3 : a.terms.length*(14*163)≤B*(14*163) := Nat.mul_le_mul_right _ h2.1
        have h4 : a.pre.length*(14*33)≤4*(14*33) := Nat.mul_le_mul_right _ h2.2
        simp only [mixProg]; omega
    have hprogQ : Challenge.gateSlots (mixProgQTq L i)≤41000+2*(B*(14*163))+(67*256+41) := by
      cases i with
      | inl f =>
        have a1 := Baselines.measuredFold_gateSlots_le L hw f
        have a2 := measuredFoldQ_gateSlotsTq L hw f
        by_cases hcan : f.canonical=true
        · simp only [mixProgQTq,hcan,if_true]; omega
        · simp only [mixProgQTq,hcan,Bool.false_eq_true,if_false,Challenge.gateSlots_append]; omega
      | inr a =>
        have h1 := accFoldQ_gateSlotsTq L hw a hi.2.1 hi.2.2.2
        have h2 := hB (.inr a) (by simp) a rfl
        have h3 : a.terms.length*(14*163)≤B*(14*163) := Nat.mul_le_mul_right _ h2.1
        have h4 : a.pre.length*(14*33)≤4*(14*33) := Nat.mul_le_mul_right _ h2.2
        simp only [mixProgQTq]; omega
    simp only [mixFoldsQTq,Challenge.gateSlots_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    split
    · omega
    · omega


end ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout RecordedQuantum
/-- `qprog4` with the output-only `+flag·p` correction of `qprogTq`. -/
def qprog4Tq (K : MeasuredCanonicalModLayout) (p : Nat) : Program :=
  notRegister K.out++Skip4.addSkip 4 (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)])
    K.extended K.carry K.cin++[.CX K.high K.flag,.X K.flag]++
    mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p++[.CX K.flag K.high]++
    [.X K.high,.X K.flag]++
    Skip4.eraseSkip 4 K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag

namespace Q4

theorem q4_countsTq (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (n5 : 5≤n) :
    toffoliCount (qprog4Tq K p)+8=toffoliCount (qprogTq K p) ∧
    measurementCount (qprog4Tq K p)=measurementCount (qprogTq K p) := by
  have a := Skip4.addSkip_toff 4 (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)])
    K.extended K.carry K.cin (by simp [mappedRead,hw.src]; omega)
    (by simp [MeasuredCanonicalModLayout.extended,hw.out]; omega) (by rw [hw.carry]; omega)
  have e := Skip4.eraseSkip_toff 4 K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
    (by rw [hw.out]; omega) (by rw [hw.src]; omega) (by simp [hw.carry,hw.out]; omega)
  have am := Skip4.addSkip_mc 4 (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)])
    K.extended K.carry K.cin
  have em := Skip4.eraseSkip_mc 4 K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
  simp only [qprog4Tq,qprogTq,MeasuredCanonicalModLayout.sum,toffoliCount_append,measurementCount_append] at a e am em ⊢
  constructor <;> omega

theorem q4_sublistTq (K : MeasuredCanonicalModLayout) (p : Nat) : List.Sublist (qprog4Tq K p) (qprogTq K p) := by
  unfold qprog4Tq qprogTq MeasuredCanonicalModLayout.sum
  exact ((((((List.Sublist.refl _).append (Skip4.addSkip_sublist 4 _ _ _ _)).append (List.Sublist.refl _)).append
    (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)).append
    (Skip4.eraseSkip_sublist 4 _ _ _ _ _)

theorem q4_run_eqTq (K : MeasuredCanonicalModLayout) (n c p : Nat) (hw : K.Widths n)
    (hn : K.wires.Nodup) (n5 : 5≤n) (hpc : p+c=2^n) (hcp : 0<c)
    (A X : Nat) (hA : A<p) (hX : X<p) (s : State) (m : List Bool)
    (ha : regValue K.src s.basis=A) (hx : regValue K.out s.basis=X)
    (hh : s.basis K.high=false) (hf : s.basis K.flag=false)
    (hc : ∀q∈K.carry,s.basis q=false) (hi : s.basis K.cin=false)
    (hlow : ∀q∈K.src.take 4,s.basis q=false) :
    run (qprog4Tq K p) m s=run (qprogTq K p) m s := by
  have npos : 0<n := by omega
  let base := s.basis
  have initial : K.Frame base X false false s.basis := ⟨hx,hh,hf,fun _ _ => rfl⟩
  have bpos : 0<2^n := by positivity
  have sumBound : A+(2^n-1-X)<2^(n+1) := by rw [Nat.pow_succ]; omega
  generalize hr : decide (2^n≤A+(2^n-1-X))=r
  have s1 := QCore.not_frame K n hw hn base X
  have s2 := K.sum_frame n hw hn base A (2^n-1-X) ha sumBound hc hi
  rw [hr] at s2
  have s3 : Triple (K.Frame base ((A+(2^n-1-X))%2^n) r false) [.CX K.high K.flag]
      (K.Frame base ((A+(2^n-1-X))%2^n) r r) := by
    simpa using K.cx_flag_frame hn base ((A+(2^n-1-X))%2^n) r false
  have s4 := QCore.x_flag_frame K hn base ((A+(2^n-1-X))%2^n) r r
  have s5 := QCore.correctionT_frame K n p hw hn (by omega) npos base ((A+(2^n-1-X))%2^n) r (!r) hc hi
  have s6 := QCore.x_high_frame K hn base (((if !r then p else 0)+(A+(2^n-1-X))%2^n)%2^n) (r ^^ !r) (!r)
  have s7 := QCore.x_flag_frame K hn base (((if !r then p else 0)+(A+(2^n-1-X))%2^n)%2^n) (!(r ^^ !r)) (!r)
  let N := notRegister K.out
  let S := MeasuredCanonicalModLayout.sum K
  let S4 := Skip4.addSkip 4 (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)]) K.extended K.carry K.cin
  let Y : Program := [.CX K.high K.flag,.X K.flag]
  let C := mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p++[.CX K.flag K.high]
  let Z : Program := [.X K.high,.X K.flag]
  let E := eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
  let E4 := Skip4.eraseSkip 4 K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
  have e1 : qprog4Tq K p=N++S4++Y++C++Z++E4 := by simp only [qprog4Tq,N,S4,Y,C,Z,E4,List.append_assoc]
  have e2 : qprogTq K p=N++S++Y++C++Z++E := by simp only [qprogTq,N,S,Y,C,Z,E,List.append_assoc]
  have zeroOf (t : BasisState) (O : Nat) (H F : Bool) (ht : K.Frame base O H F t) :
      (∀q∈K.src.take 4,t q=false) ∧ t K.cin=false ∧ (∀q∈K.carry.take 4,t q=false) :=
    ⟨fun q hq => (frame_zero K hn base t O H F ht q (by simp [List.mem_of_mem_take hq])).trans (hlow q hq),
     (frame_zero K hn base t O H F ht K.cin (by simp)).trans hi,
     fun q hq => (frame_zero K hn base t O H F ht q (by simp [List.mem_of_mem_take hq])).trans
       (hc q (List.mem_of_mem_take hq))⟩
  have mS : measurementCount S4=measurementCount S := Skip4.addSkip_mc 4 _ _ _ _
  have stepNS (m' : List Bool) : run (N++S4) m' s=run (N++S) m' s := by
    rw [run_append,run_append]
    have u := (s1 s (m'.take (measurementCount N)) initial).2
    have z := zeroOf _ _ _ _ u
    exact Skip4.addSkip_run 4 _ _ _ _ _ _ (skipOK K n hw hn n5 _ z.1 z.2.1 z.2.2)
  have stepP (m' : List Bool) : run (N++S4++Y++C++Z) m' s=run (N++S++Y++C++Z) m' s := by
    have mNS : measurementCount (N++S4)=measurementCount (N++S) := by simp only [measurementCount_append,mS]
    have h1 := run_congr_left (N++S4) (N++S) Y s mNS stepNS
    have h2 := run_congr_left (N++S4++Y) (N++S++Y) C s (by simp only [measurementCount_append,mS]) h1
    exact run_congr_left (N++S4++Y++C) (N++S++Y++C) Z s (by simp only [measurementCount_append,mS]) h2 m'
  have pre := (((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7
  rw [e1,e2,run_append (N++S4++Y++C++Z) E4,run_append (N++S++Y++C++Z) E]
  have mP : measurementCount (N++S4++Y++C++Z)=measurementCount (N++S++Y++C++Z) := by
    simp only [measurementCount_append,mS]
  rw [mP,stepP]
  have hP : N++S++Y++C++Z=notRegister K.out++K.sum++[.CX K.high K.flag]++[.X K.flag]++
      (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p++[.CX K.flag K.high])++
      [.X K.high]++[.X K.flag] := by
    simp [N,S,Y,C,Z,List.append_assoc]
  have w := (pre s (m.take (measurementCount (N++S++Y++C++Z))) initial).2
  rw [← hP] at w
  have z := zeroOf _ _ _ _ w
  exact Skip4.eraseSkip_run 4 _ _ _ _ _ _ _ (eok K n hw hn n5 _ z.1 z.2.1 z.2.2)

end Q4

namespace Q4
end Q4
def accFoldQ4Tq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  fillIn L a++qprog4Tq L.measuredCore SquareReduction.p++fillOut L a


namespace Q4
theorem accFoldQ4_runTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p)
    (h16 : Acc.accVal base 0 a.spec%16=0)
    (s : State) (m : List Bool) (hf : SquareFrame L.core.out base O s.basis) :
    run (accFoldQ4Tq L a) m s=run (accFoldQTq L a) m s := by
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillIn_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  let mb := measurementCount (fillIn L a)
  let u := run (fillIn L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u.basis q=b0 q :=
    eu.2.2 q (accReg_away L hn q hq)
  have workU : regValue L.core.work u.basis=A := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using eu.2.1
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A<SquareReduction.p := lt_of_lt_of_le hA (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have workLen : L.core.work.length=256 := (L.measuredCore_widths hw).src
  have lowU : ∀q∈L.measuredCore.src.take 4,u.basis q=false := by
    have t := CuccaroStreamedSquareWideLayout.regValue_take_mod L.core.work 4 (by omega) u.basis
    rw [workU] at t
    have z : regValue (L.core.work.take 4) u.basis=0 := by rw [t]; simpa [A] using h16
    exact (regValue_zero _ _).mp z
  rw [accFoldQ4Tq,accFoldQTq,List.append_assoc,List.append_assoc,run_append (fillIn L a),run_append (fillIn L a)]
  have cnt := q4_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by norm_num)
  exact run_congr_left _ _ _ u cnt.2 (fun m' => q4_run_eqTq L.measuredCore 256 SquareReduction.c SquareReduction.p
    (L.measuredCore_widths hw) coreNd (by norm_num) hp (by norm_num [SquareReduction.c]) A O hAp hO u m'
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin) lowU) _


end Q4
end ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Q4
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
theorem accFoldQ4_sublistTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) :
    List.Sublist (accFoldQ4Tq L a) (accFoldQTq L a) :=
  ((List.Sublist.refl _).append (q4_sublistTq _ _)).append (List.Sublist.refl _)


theorem accFoldQ4_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem) :
    toffoliCount (accFoldQ4Tq L a)+8=toffoliCount (accFoldQTq L a) ∧
    measurementCount (accFoldQ4Tq L a)=measurementCount (accFoldQTq L a) := by
  have c := q4_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by norm_num)
  simp only [accFoldQ4Tq,accFoldQTq,toffoliCount_append,measurementCount_append]
  constructor <;> omega


theorem accFoldQ4_wiresTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) :
    ECDSAAdd.wires (accFoldQ4Tq L a)⊆ECDSAAdd.wires (accFoldQTq L a) :=
  Skip4.wires_mono_of_mem _ _ (fun _ hi => (accFoldQ4_sublistTq L a).subset hi)


theorem accFoldQ4_physicalTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem)
    (h : GatePhysical (accFoldQTq L a)) : GatePhysical (accFoldQ4Tq L a) :=
  fun i hi => h i ((accFoldQ4_sublistTq L a).subset hi)


theorem accFoldQ4_slotsTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) :
    Challenge.gateSlots (accFoldQ4Tq L a)≤Challenge.gateSlots (accFoldQTq L a) :=
  Skip4.slots_mono_of_sublist _ _ (accFoldQ4_sublistTq L a)


end ECDSAAdd.Entrant.Q4

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout RecordedQuantum

def accFoldQKTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  OwnDiagAll12Square.fillInK L a++qprogTq L.measuredCore SquareReduction.p++CodexCKAccTail.fillOutTail L a

theorem accFoldQ_frameKTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFoldQKTq L a)
      (SquareFrame L.core.out base ((Acc.accVal base 0 a.spec+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := OwnDiagAll12Square.fillInK_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFoldQKTq,List.append_assoc,run_append,run_append]
  let mb := measurementCount (OwnDiagAll12Square.fillInK L a)
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let u := run (OwnDiagAll12Square.fillInK L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u.basis q=b0 q :=
    eu.2.2 q (accReg_away L hn q hq)
  have workU : regValue L.core.work u.basis=A := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using eu.2.1
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A<SquareReduction.p := lt_of_lt_of_le hA (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A O hAp hO u ((m.drop mb).take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) ((m.drop mb).take mk) u
  change v.phase=u.phase ∧ regValue L.core.out v.basis=(A+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u.basis q at ek
  let base2 : BasisState := fun q => if q∈L.core.out then v.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have frame2 : SquareFrame (accReg L) base2 A v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans eu.2.1
    · intro q hq
      by_cases ho : q∈L.core.out
      · simp [base2,ho]
      · rw [b2off q ho,ek.2.2 q ho]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := CodexCKAccTail.fillOutTail_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v ((m.drop mb).drop mk) frame2
  refine ⟨eo.1.trans (ek.1.trans eu.1),?_,?_⟩
  · have e : regValue L.core.out (run (CodexCKAccTail.fillOutTail L a) ((m.drop mb).drop mk) v).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq



def accFoldQ4KTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  OwnDiagAll12Square.fillInK L a++qprog4Tq L.measuredCore SquareReduction.p++CodexCKAccTail.fillOutTail L a

namespace Q4
theorem accFoldQ4_runKTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p)
    (h16 : Acc.accVal base 0 a.spec%16=0)
    (s : State) (m : List Bool) (hf : SquareFrame L.core.out base O s.basis) :
    run (accFoldQ4KTq L a) m s=run (accFoldQKTq L a) m s := by
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := OwnDiagAll12Square.fillInK_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  let mb := measurementCount (OwnDiagAll12Square.fillInK L a)
  let u := run (OwnDiagAll12Square.fillInK L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u.basis q=b0 q :=
    eu.2.2 q (accReg_away L hn q hq)
  have workU : regValue L.core.work u.basis=A := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using eu.2.1
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A<SquareReduction.p := lt_of_lt_of_le hA (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have workLen : L.core.work.length=256 := (L.measuredCore_widths hw).src
  have lowU : ∀q∈L.measuredCore.src.take 4,u.basis q=false := by
    have t := CuccaroStreamedSquareWideLayout.regValue_take_mod L.core.work 4 (by omega) u.basis
    rw [workU] at t
    have z : regValue (L.core.work.take 4) u.basis=0 := by rw [t]; simpa [A] using h16
    exact (regValue_zero _ _).mp z
  rw [accFoldQ4KTq,accFoldQKTq,List.append_assoc,List.append_assoc,run_append (OwnDiagAll12Square.fillInK L a),run_append (OwnDiagAll12Square.fillInK L a)]
  have cnt := q4_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by norm_num)
  exact run_congr_left _ _ _ u cnt.2 (fun m' => q4_run_eqTq L.measuredCore 256 SquareReduction.c SquareReduction.p
    (L.measuredCore_widths hw) coreNd (by norm_num) hp (by norm_num [SquareReduction.c]) A O hAp hO u m'
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin) lowU) _



theorem accFoldQ4KTq_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) :
    toffoliCount (accFoldQ4KTq L a)≤toffoliCount (accFoldQ4Tq L a) ∧
    measurementCount (accFoldQ4KTq L a)=measurementCount (accFoldQ4Tq L a) ∧
    ECDSAAdd.wires (accFoldQ4KTq L a)⊆ECDSAAdd.wires (accFoldQ4Tq L a) ∧
    Challenge.gateSlots (accFoldQ4KTq L a)≤Challenge.gateSlots (accFoldQ4Tq L a) := by
  have r := CodexCKAccTail.fillTail_rel L hw a ok
  simp only [accFoldQ4KTq,accFoldQ4Tq,toffoliCount_append,measurementCount_append,wires_append,
    Challenge.gateSlots_append]
  refine ⟨by omega,by omega,?_,by omega⟩
  exact Finset.union_subset_union (Finset.union_subset_union r.1.2.2.1 (Finset.Subset.refl _)) r.2.2.2.1

theorem accFoldQ4KTq_counts_early (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (src : List Wire) (hsrc : src.length≤130) (he : a.terms=earlyHTerms src)
    (ok : ∀f∈a.terms,TermOK f) :
    toffoliCount (accFoldQ4KTq L a)+31=toffoliCount (accFoldQ4Tq L a) := by
  have e : a.terms=Acc.earlyTerm src false 4::Acc.earlyTerm src false 10::Acc.earlyTerm src true 6::
      Acc.earlyTerm src false 32::[] := by rw [he]; rfl
  have c := CodexCKAccTail.tail_counts_early (accReg L) (accZ L) (accBank L) L.core.cin src
    (acc_lengths L hw).1 hsrc (Acc.earlyTerm src false 32) []
    (by simp [CKAcc.IsT32,Acc.earlyTerm]) (fun f hf => fitsLen_of L hw f (ok f (by rw [e]; exact hf)))
  rw [← e] at c
  simp only [accFoldQ4KTq,accFoldQ4Tq,OwnDiagAll12Square.fillInK,fillIn,CodexCKAccTail.fillOutTail,fillOut,
    toffoliCount_append]
  omega

theorem accFoldQ4KTq_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQ4KTq L a) := by
  have old := accFoldQ4_physicalTq L a (accFoldQ_physicalTq L hw hn a cnt ok cntP okP)
  have k := CodexCKAccTail.fillTail_physical L hw hn a cnt ok cntP okP
  simp only [accFoldQ4Tq,gatePhysical_append] at old
  simp only [accFoldQ4KTq,gatePhysical_append]
  exact ⟨⟨k.1,old.1.2⟩,k.2⟩

end Q4
end ECDSAAdd.Entrant

namespace ECDSAAdd.Entrant.OwnDiagAll12Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
def accFoldQFTq (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) : Program :=
  fillIn L a++(maskedConstant g (accReg L) cFlipK++(qprogTq L.measuredCore SquareReduction.p++
    (maskedConstant g (accReg L) cFlipK++fillOut L a)))


theorem accFoldQF_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (g : Wire) (hg : g∉L.wires) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFoldQFTq L g a)
      (SquareFrame L.core.out base (((if base g then cFlipK-Acc.accVal base 0 a.spec else Acc.accVal base 0 a.spec)+
        (SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have gAcc : g∉accReg L := fun h => hg (accReg_in L g h)
  have gOut : g∉L.core.out := fun h => hg (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have hAK : A≤cFlipK := by unfold cFlipK; omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^163 := by
    simp only [A']; split
    · unfold cFlipK; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillIn_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFoldQFTq,run_append,run_append,run_append,run_append]
  let mb := measurementCount (fillIn L a)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (fillIn L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u1.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using accU1
  have outU : regValue L.core.out u1.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A'<SquareReduction.p := lt_of_lt_of_le hA' (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u1.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) cFlipK) (m3.take mc) v
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc)
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis else regValue (accReg L) v.basis) at fl2
  rw [gV,accV] at fl2
  have back : (if base g then cFlipK-A' else A')=A := by
    simp only [A']
    cases base g
    · simp
    · simp only [if_true]; omega
  rw [back] at fl2
  let base2 : BasisState := fun q => if q∈L.core.out then v1.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have frame2 : SquareFrame (accReg L) base2 A v1.basis := by
    refine ⟨fl2.2.2,?_⟩
    intro q hq
    by_cases ho : q∈L.core.out
    · simp [base2,ho]
    · rw [b2off q ho,fl2.2.1 q hq,ek.2.2 q ho,fl.2.1 q hq]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := fillOut_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v1 (m3.drop mc) frame2
  refine ⟨eo.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have e : regValue L.core.out (run (fillOut L a) (m3.drop mc) v1).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq,fl2.2.1 q na]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq


theorem accFoldQF_countsTq (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) :
    toffoliCount (accFoldQFTq L g a)=toffoliCount (accFoldQTq L a) ∧
    measurementCount (accFoldQFTq L g a)=measurementCount (accFoldQTq L a) := by
  have k := maskedConstant_counts g (accReg L) cFlipK
  simp only [accFoldQFTq,accFoldQTq,toffoliCount_append,measurementCount_append,k.1,k.2]
  constructor <;> omega


theorem accFoldQF_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    ECDSAAdd.wires (accFoldQFTq L g a)⊆(g::L.wires).toFinset := by
  have full := accFoldQ_supportTq L hw hn g a cnt ok cntP okP
  simp only [accFoldQTq,wires_append,Finset.union_subset_iff] at full
  have mc : ECDSAAdd.wires (maskedConstant g (accReg L) cFlipK)⊆(g::L.wires).toFinset := by
    refine (maskedConstant_wires_subset _ _ _).trans ?_
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq ⊢
    rcases hq with h|h
    · exact Or.inl h
    · exact Or.inr (accReg_in L q h)
  simp only [accFoldQFTq,wires_append,Finset.union_subset_iff]
  exact ⟨full.1.1,mc,full.1.2,mc,full.2⟩


theorem accFoldQF_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQFTq L g a) := by
  have full := accFoldQ_physicalTq L hw hn a cnt ok cntP okP
  simp only [accFoldQTq,gatePhysical_append] at full
  have mc := maskedConstant_physical g (accReg L) cFlipK (fun h => hg (accReg_in L g h))
  simp only [accFoldQFTq,gatePhysical_append]
  exact ⟨full.1.1,mc,full.1.2,mc,full.2⟩


theorem accFoldQF_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    Challenge.gateSlots (accFoldQFTq L g a)≤
      2*(a.terms.length*(14*163))+4*(a.pre.length*(14*33))+(67*256+41)+7000+2*163 := by
  have full := accFoldQ_gateSlotsTq L hw a ok okP
  have mc := Baselines.maskedConstant_gateSlots_le g (accReg L) cFlipK
  rw [(acc_lengths L hw).1] at mc
  simp only [accFoldQTq,Challenge.gateSlots_append] at full
  simp only [accFoldQFTq,Challenge.gateSlots_append]
  omega


open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
def accFoldQFKTq (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) : Program :=
  fillInK L a++(maskedConstant g (accReg L) cFlipK++(qprogTq L.measuredCore SquareReduction.p++
    (maskedConstant g (accReg L) cFlipK++CodexCKAccTail.fillOutTail L a)))


theorem accFoldQFK_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (g : Wire) (hg : g∉L.wires) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFoldQFKTq L g a)
      (SquareFrame L.core.out base (((if base g then cFlipK-Acc.accVal base 0 a.spec else Acc.accVal base 0 a.spec)+
        (SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have gAcc : g∉accReg L := fun h => hg (accReg_in L g h)
  have gOut : g∉L.core.out := fun h => hg (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have hAK : A≤cFlipK := by unfold cFlipK; omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^163 := by
    simp only [A']; split
    · unfold cFlipK; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillInK_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFoldQFKTq,run_append,run_append,run_append,run_append]
  let mb := measurementCount (fillInK L a)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (fillInK L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u1.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using accU1
  have outU : regValue L.core.out u1.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A'<SquareReduction.p := lt_of_lt_of_le hA' (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u1.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) cFlipK) (m3.take mc) v
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc)
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis else regValue (accReg L) v.basis) at fl2
  rw [gV,accV] at fl2
  have back : (if base g then cFlipK-A' else A')=A := by
    simp only [A']
    cases base g
    · simp
    · simp only [if_true]; omega
  rw [back] at fl2
  let base2 : BasisState := fun q => if q∈L.core.out then v1.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have frame2 : SquareFrame (accReg L) base2 A v1.basis := by
    refine ⟨fl2.2.2,?_⟩
    intro q hq
    by_cases ho : q∈L.core.out
    · simp [base2,ho]
    · rw [b2off q ho,fl2.2.1 q hq,ek.2.2 q ho,fl.2.1 q hq]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := CodexCKAccTail.fillOutTail_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v1 (m3.drop mc) frame2
  refine ⟨eo.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have e : regValue L.core.out (run (CodexCKAccTail.fillOutTail L a) (m3.drop mc) v1).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq,fl2.2.1 q na]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq



theorem accFoldQFK_relTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) :
    toffoliCount (accFoldQFKTq L g a)≤toffoliCount (accFoldQFTq L g a) ∧
    measurementCount (accFoldQFKTq L g a)=measurementCount (accFoldQFTq L g a) ∧
    ECDSAAdd.wires (accFoldQFKTq L g a)⊆ECDSAAdd.wires (accFoldQFTq L g a) ∧
    Challenge.gateSlots (accFoldQFKTq L g a)≤Challenge.gateSlots (accFoldQFTq L g a) := by
  have r := CodexCKAccTail.fillTail_rel L hw a ok
  simp only [accFoldQFKTq,accFoldQFTq,toffoliCount_append,measurementCount_append,wires_append,
    Challenge.gateSlots_append]
  refine ⟨by omega,by omega,?_,by omega⟩
  exact Finset.union_subset_union r.1.2.2.1 (Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union (Finset.Subset.refl _) r.2.2.2.1)))


theorem accFoldQFK_countsCTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire)
    (ok : ∀f∈(accCItem L).terms,TermOK f) :
    toffoliCount (accFoldQFKTq L g (accCItem L))+31=toffoliCount (accFoldQFTq L g (accCItem L)) ∧
    measurementCount (accFoldQFKTq L g (accCItem L))=measurementCount (accFoldQFTq L g (accCItem L)) := by
  have r := CodexCKAccTail.fillTail_rel L hw (accCItem L) ok
  have hsrc : (L.core.product.drop 128).length≤130 := by simp [hw.core.product]
  have e : (accCItem L).terms=Acc.earlyTerm (L.core.product.drop 128) false 4::
      Acc.earlyTerm (L.core.product.drop 128) false 10::Acc.earlyTerm (L.core.product.drop 128) true 6::
      Acc.earlyTerm (L.core.product.drop 128) false 32::[posTop L] := by
    simp [accCItem,earlyHTerms]
  have c := CodexCKAccTail.tail_counts_early (accReg L) (accZ L) (accBank L) L.core.cin (L.core.product.drop 128)
    (acc_lengths L hw).1 hsrc (Acc.earlyTerm (L.core.product.drop 128) false 32) [posTop L]
    (by simp [CKAcc.IsT32,Acc.earlyTerm]) (fun f hf => fitsLen_of L hw f (ok f (by rw [e]; exact hf)))
  rw [← e] at c
  have r2 := CKAcc.sbuildK_rel (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 (accCItem L).terms
    (fun f hf => fitsLen_of L hw f (ok f hf))
  have r3 := CodexCKAccTail.sunbuildTail_rel (accReg L) (accZ L) (accBank L) L.core.cin 163
    (acc_lengths L hw).1 (accCItem L).terms (fun f hf => fitsLen_of L hw f (ok f hf))
  simp only [accFoldQFKTq,accFoldQFTq,fillInK,fillIn,CodexCKAccTail.fillOutTail,fillOut,toffoliCount_append,measurementCount_append]
  simp only [accFoldQFKTq,accFoldQFTq,toffoliCount_append,measurementCount_append] at r
  constructor <;> omega


theorem accFoldQFK_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQFKTq L g a) := by
  have old := accFoldQF_physicalTq L hw hn g hg a cnt ok cntP okP
  have k := CodexCKAccTail.fillTail_physical L hw hn a cnt ok cntP okP
  simp only [accFoldQFTq,gatePhysical_append] at old
  simp only [accFoldQFKTq,gatePhysical_append]
  exact ⟨k.1,old.2.1,old.2.2.1,old.2.2.2.1,k.2⟩




def bodyCTq (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  mixFoldsQTq L false [.inl (negRot L)]++accFoldQFTq L g (accCItem L)


theorem bodyC_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (bodyCTq L g)=2388 ∧ measurementCount (bodyCTq L g)=2390 := by
  have st := bodyC_static L hw
  have nR : (negRot L).negative=true := rfl
  have cR : (negRot L).canonical=true := rfl
  have nC : (accCItem L).negative=true := rfl
  have f := mixFoldsQ_countsTq L hw false _ st.1
  have f1 : mixFoldsQTTq false [(.inl (negRot L) : MixItem)]=766 := by simp [mixFoldsQTTq,mixNeg,nR,cR]
  have f2 : mixFoldsQMTq false [(.inl (negRot L) : MixItem)]=767 := by simp [mixFoldsQMTq,mixNeg,nR,cR]
  have q := accFoldQ_countsTq L hw (accCItem L) st.2.2.1 st.2.2.2.2
  have qf := accFoldQF_countsTq L g (accCItem L)
  have pr := (accQ_item_prices L hw).2.2
  rw [accCMix_eq] at pr
  simp [mixFoldsQT,mixFoldsQM,mixNeg,nR,cR,nC] at pr
  have rel : accPriceQTq (accCItem L)+257=accPrice (accCItem L) := by simp only [accPriceQTq,accPrice]; omega
  rw [bodyCTq]
  simp only [toffoliCount_append,measurementCount_append]
  rw [f.1,f.2,qf.1,qf.2,q.1,q.2,f1,f2]
  constructor <;> omega


theorem bodyC_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (g : Wire) :
    ECDSAAdd.wires (bodyCTq L g)⊆(g::L.wires).toFinset := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_supportTq L hw hn g false _ st.1
  have b := accFoldQF_supportTq L hw hn g (accCItem L) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  simp only [bodyCTq,wires_append,Finset.union_subset_iff]
  exact ⟨a,b⟩


theorem bodyC_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires) : GatePhysical (bodyCTq L g) := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_physicalTq L hw hn false _ st.1
  have b := accFoldQF_physicalTq L hw hn g hg (accCItem L) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  simp only [bodyCTq,gatePhysical_append]
  exact ⟨a,b⟩


theorem bodyC_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    Challenge.gateSlots (bodyCTq L g)≤2*(41000+2*(20*(14*163))+(67*256+41)) := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_gateSlotsTq L hw false _ st.1 20 (by intro i hi a e; simp at hi; subst hi; cases e)
  have b := accFoldQF_gateSlotsTq L hw g (accCItem L) st.2.2.1 st.2.2.2.2
  have lt : (accCItem L).terms.length=5 := by simp [accCItem,earlyHTerms]
  have lp : (accCItem L).pre.length=0 := rfl
  rw [lt,lp] at b
  simp only [List.length_singleton] at a
  simp only [bodyCTq,Challenge.gateSlots_append]
  omega


theorem accMiddleCF_bodyTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (M O : Nat) (hO : O<SquareReduction.p)
    (t : State) (m : List Bool) (pv : regValue L.core.product t.basis=M^2)
    (hM : t.basis control=false → M=0)
    (clean : L.PairClean t.basis) (outO : regValue L.core.out t.basis=O) :
    (run (bodyCTq L control) m t).phase=t.phase ∧
    regValue L.core.out (run (bodyCTq L control) m t).basis=resCF (t.basis control) (M^2) O ∧
    ∀q,q∉L.core.out → (run (bodyCTq L control) m t).basis q=t.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have gW : control∉L.wires := (List.nodup_cons.mp hn).1
  have views := accC_views L hw t.basis M pv
  rw [accCMix_eq] at views
  have v1 : ∀i∈[(.inl (negRot L) : MixItem)],MixView L t.basis i := fun i hi => views i (by simp at hi ⊢; exact Or.inl hi)
  have va : AccView L t.basis (accCItem L) := views (.inr (accCItem L)) (by simp)
  let mm := measurementCount (mixFoldsQTq L false [.inl (negRot L)])
  let r1 := run (mixFoldsQTq L false [.inl (negRot L)]) (m.take mm) t
  have e1 := mixFoldsQ_frameTq L hw nd t.basis clean false O hO [.inl (negRot L)] v1 t (m.take mm) ⟨outO,fun _ _ => rfl⟩
  let O1 := mixValue t.basis false O [.inl (negRot L)]
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have e2 := accFoldQF_frameTq L hw nd control gW t.basis (accCItem L) va clean O1 hO1 r1 (m.drop mm) e1.2
  rw [bodyCTq,run_append]
  refine ⟨e2.1.trans e1.1,?_,fun q hq => e2.2.2 q hq⟩
  rw [e2.2.1]
  have nR : (negRot L).negative=true := rfl
  have nC : (accCItem L).negative=true := rfl
  have cast1 := mixValue_cast t.basis false O [.inl (negRot L)] hO
  have sum := (accC_mixSum L hw t.basis).trans (L.measuredC_sum hw t.basis (M^2) pv)
  rw [accCMix_eq] at sum
  simp only [mixFinal,mixNeg,nR,nC,mixSignedSum,mixSignedPayload,mixPayload,↓reduceIte,add_zero] at cast1 sum
  simp only [measuredOrientationCast,↓reduceIte,Bool.false_eq_true] at cast1
  have hA : Acc.accVal t.basis 0 (accCItem L).spec<2^163 := Acc.accVal_lt _ 163 _ 0 (by norm_num) va.specValid
  set A := Acc.accVal t.basis 0 (accCItem L).spec with hAdef
  set O1 := mixValue t.basis false O [.inl (negRot L)] with hO1def
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have hp1 : ((SquareReduction.p : Nat) : ZMod SquareReduction.p)=0 := ZMod.natCast_self _
  have e3 : ((SquareReduction.p-1-O1 : Nat) : ZMod SquareReduction.p)=-1-(O1 : ZMod SquareReduction.p) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one,hp1]; ring
  have target : ((((if t.basis control then cFlipK-A else A)+(SquareReduction.p-1-O1)) : Nat) : ZMod SquareReduction.p)=
      measuredOrientationCast false O+(-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)+
        ((if t.basis control then cFlipK else 0 : Nat) : ZMod SquareReduction.p) := by
    simp only [measuredOrientationCast,Bool.false_eq_true,↓reduceIte]
    cases hg : t.basis control
    · have m0 := hM hg
      have a0 : A=0 := by
        have pz : regValue L.core.product t.basis=0 := by rw [pv,m0]; rfl
        exact accC_zero L t.basis pz
      simp only [Bool.false_eq_true,↓reduceIte]
      rw [Nat.cast_add,e3,a0,Nat.cast_zero]
      rw [a0,Nat.cast_zero] at sum
      linear_combination cast1+sum
    · have hAK : A≤cFlipK := by unfold cFlipK; omega
      simp only [↓reduceIte]
      rw [Nat.cast_add,Nat.cast_sub hAK,e3]
      linear_combination cast1+sum
  unfold resCF ofCast
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [←target,ZMod.val_natCast]



def bodyCKTq (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  mixFoldsQTq L false [.inl (negRot L)]++accFoldQFKTq L g (accCItem L)


theorem bodyCK_relTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (bodyCKTq L g)+31=toffoliCount (bodyCTq L g) ∧
    measurementCount (bodyCKTq L g)=measurementCount (bodyCTq L g) ∧
    ECDSAAdd.wires (bodyCKTq L g)⊆ECDSAAdd.wires (bodyCTq L g) ∧
    Challenge.gateSlots (bodyCKTq L g)≤Challenge.gateSlots (bodyCTq L g) := by
  have st := bodyC_static L hw
  have qk := accFoldQFK_countsCTq L hw g st.2.2.1
  have r := accFoldQFK_relTq L hw g (accCItem L) st.2.2.1
  simp only [bodyCKTq,bodyCTq,toffoliCount_append,measurementCount_append,wires_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,Finset.union_subset_union (Finset.Subset.refl _) r.2.2.1,by omega⟩


theorem bodyCK_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (bodyCKTq L g)=2357 ∧ measurementCount (bodyCKTq L g)=2390 := by
  have r := bodyCK_relTq L hw g
  have c := bodyC_countsTq L hw g
  omega


theorem bodyCK_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (g : Wire) :
    ECDSAAdd.wires (bodyCKTq L g)⊆(g::L.wires).toFinset :=
  (bodyCK_relTq L hw g).2.2.1.trans (bodyC_supportTq L hw hn g)


theorem bodyCK_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires) : GatePhysical (bodyCKTq L g) := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_physicalTq L hw hn false _ st.1
  have b := accFoldQFK_physicalTq L hw hn g hg (accCItem L) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  simp only [bodyCKTq,gatePhysical_append]
  exact ⟨a,b⟩


theorem bodyCK_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    Challenge.gateSlots (bodyCKTq L g)≤2*(41000+2*(20*(14*163))+(67*256+41)) :=
  (bodyCK_relTq L hw g).2.2.2.trans (bodyC_gateSlotsTq L hw g)


theorem accMiddleCFK_bodyTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (M O : Nat) (hO : O<SquareReduction.p)
    (t : State) (m : List Bool) (pv : regValue L.core.product t.basis=M^2)
    (hM : t.basis control=false → M=0)
    (clean : L.PairClean t.basis) (outO : regValue L.core.out t.basis=O) :
    (run (bodyCKTq L control) m t).phase=t.phase ∧
    regValue L.core.out (run (bodyCKTq L control) m t).basis=resCF (t.basis control) (M^2) O ∧
    ∀q,q∉L.core.out → (run (bodyCKTq L control) m t).basis q=t.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have gW : control∉L.wires := (List.nodup_cons.mp hn).1
  have views := accC_views L hw t.basis M pv
  rw [accCMix_eq] at views
  have v1 : ∀i∈[(.inl (negRot L) : MixItem)],MixView L t.basis i := fun i hi => views i (by simp at hi ⊢; exact Or.inl hi)
  have va : AccView L t.basis (accCItem L) := views (.inr (accCItem L)) (by simp)
  let mm := measurementCount (mixFoldsQTq L false [.inl (negRot L)])
  let r1 := run (mixFoldsQTq L false [.inl (negRot L)]) (m.take mm) t
  have e1 := mixFoldsQ_frameTq L hw nd t.basis clean false O hO [.inl (negRot L)] v1 t (m.take mm) ⟨outO,fun _ _ => rfl⟩
  let O1 := mixValue t.basis false O [.inl (negRot L)]
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have e2 := accFoldQFK_frameTq L hw nd control gW t.basis (accCItem L) va clean O1 hO1 r1 (m.drop mm) e1.2
  rw [bodyCKTq,run_append]
  refine ⟨e2.1.trans e1.1,?_,fun q hq => e2.2.2 q hq⟩
  rw [e2.2.1]
  have nR : (negRot L).negative=true := rfl
  have nC : (accCItem L).negative=true := rfl
  have cast1 := mixValue_cast t.basis false O [.inl (negRot L)] hO
  have sum := (accC_mixSum L hw t.basis).trans (L.measuredC_sum hw t.basis (M^2) pv)
  rw [accCMix_eq] at sum
  simp only [mixFinal,mixNeg,nR,nC,mixSignedSum,mixSignedPayload,mixPayload,↓reduceIte,add_zero] at cast1 sum
  simp only [measuredOrientationCast,↓reduceIte,Bool.false_eq_true] at cast1
  have hA : Acc.accVal t.basis 0 (accCItem L).spec<2^163 := Acc.accVal_lt _ 163 _ 0 (by norm_num) va.specValid
  set A := Acc.accVal t.basis 0 (accCItem L).spec with hAdef
  set O1 := mixValue t.basis false O [.inl (negRot L)] with hO1def
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have hp1 : ((SquareReduction.p : Nat) : ZMod SquareReduction.p)=0 := ZMod.natCast_self _
  have e3 : ((SquareReduction.p-1-O1 : Nat) : ZMod SquareReduction.p)=-1-(O1 : ZMod SquareReduction.p) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one,hp1]; ring
  have target : ((((if t.basis control then cFlipK-A else A)+(SquareReduction.p-1-O1)) : Nat) : ZMod SquareReduction.p)=
      measuredOrientationCast false O+(-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)+
        ((if t.basis control then cFlipK else 0 : Nat) : ZMod SquareReduction.p) := by
    simp only [measuredOrientationCast,Bool.false_eq_true,↓reduceIte]
    cases hg : t.basis control
    · have m0 := hM hg
      have a0 : A=0 := by
        have pz : regValue L.core.product t.basis=0 := by rw [pv,m0]; rfl
        exact accC_zero L t.basis pz
      simp only [Bool.false_eq_true,↓reduceIte]
      rw [Nat.cast_add,e3,a0,Nat.cast_zero]
      rw [a0,Nat.cast_zero] at sum
      linear_combination cast1+sum
    · have hAK : A≤cFlipK := by unfold cFlipK; omega
      simp only [↓reduceIte]
      rw [Nat.cast_add,Nat.cast_sub hAK,e3]
      linear_combination cast1+sum
  unfold resCF ofCast
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [←target,ZMod.val_natCast]



end ECDSAAdd.Entrant.OwnDiagAll12Square
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
def wCoreTq (L : CuccaroStreamedSquareWideLayout) : Program := qprogTq (rotWCore L) SquareReduction.p

end ECDSAAdd.Entrant.ControlLoan1589BFFold

/-! ## The B fold without the restore rebuild of `W`

`whi = W/2^128 = u + d` with `u = b1/2^96` (the top 32 wires of `hiReg`) and `d ≤ 976`. The `W` fold
folds `(u + c*d) + 2^128*(W mod 2^128) ≡ 2^128*W` instead of `whi + 2^128*(W mod 2^128)`, so the `e`
register only needs `+u`, which the restore can take back from `hiReg` without rebuilding `W`.
`tFwd` turns `whi` into `u + c*d` in place (bits 128..170 of `work`, scratch in the fold pad) and
`tInv` turns it back before the unbuild. -/

section
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false


section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.WindowBoundsDevelop
-- Arithmetic bounds for the B-body window transform described in the public
-- note of 29b8f1b9-71d3-4471-b4bf-91c413c3935b. No circuit claim is made here.
theorem high_split (b : Nat) (hb : b < 2^128) :
    let u := b / 2^96
    let w := ((2^32+976)*b) / 2^128
    u < 2^32 ∧ u ≤ w ∧ w-u ≤ 976 ∧ w < 2^33 := by
  dsimp
  omega

theorem transformed_bound (u d : Nat) (hu : u < 2^32) (hd : d ≤ 976) :
    u + (2^32+977)*d < 2^42 := by omega

theorem eleven_bit_windows (d : Nat) (hd : d < 2^10) :
    17*d < 2^15 ∧ 81*d < 2^17 ∧ 209*d < 2^18 ∧
    465*d < 2^19 ∧ 977*d < 2^20 := by omega

theorem inverse_window_bounds (d : Nat) (hd : d < 2^10) :
    d < 2^10 ∧ 17*d < 2^15 ∧ 81*d < 2^17 ∧
    209*d < 2^18 ∧ 465*d < 2^19 := by omega


theorem inverse_internal_zeros (d i : Nat) (hd : d ≤ 976) (hlo : 20 ≤ i) (hhi : i < 32) :
    ((2^32+977)*d).testBit i=false := by
  have small : 977*d<2^20 := by omega
  have modlo : ((2^32+977)*d)%2^32=977*d := by omega
  have bitlem := Nat.testBit_mod_two_pow ((2^32+977)*d) 32 i
  simp only [modlo,show decide (i < 32)=true from decide_eq_true hhi,Bool.true_and] at bitlem
  rw [←bitlem]
  apply Nat.testBit_lt_two_pow
  have mono : 2^20≤2^i := Nat.pow_le_pow_right (by decide) hlo
  omega

theorem sparse_977 (d : Nat) (hd : d<2^10) :
    d+2^10*d<2^20 ∧
    d+2^10*d-2^5*d=993*d ∧
    993*d-2^4*d=977*d ∧
    977*d+2^4*d=993*d ∧
    993*d+2^5*d=d+2^10*d := by omega

theorem final_inverse_window (d : Nat) (hd : d<2^10) :
    (d+2^10*d)/2^5=d/2^5+2^5*d ∧
    d/2^5<2^5 ∧ d+2^10*d<2^20 := by omega

theorem forward_window5 (d : Nat) (hd : d<2^10) :
    (1025*d)%2^5+2^5*(((1025*d)/2^5+2^15-d)%2^15)=993*d := by omega

theorem forward_window4 (d : Nat) (hd : d<2^10) :
    (993*d)%2^4+2^4*(((993*d)/2^4+2^16-d)%2^16)=977*d := by omega

theorem inverse_window4 (d : Nat) (hd : d<2^10) :
    (977*d)%2^4+2^4*(((977*d)/2^4+d)%2^16)=993*d := by omega

theorem copy_arith (d : Nat) (hd : d<2^10) :
    d%2^10+2^10*((d/2^10) ^^^ d)=1025*d ∧
    (1025*d)%2^10+2^10*(((1025*d)/2^10) ^^^ d)=d := by
  have dv : d/2^10=0:=Nat.div_eq_of_lt hd
  have dm : d%2^10=d:=Nat.mod_eq_of_lt hd
  have ex : (1025*d)/2^10=d ∧ (1025*d)%2^10=d := by omega
  constructor
  · rw [dv,dm,Nat.zero_xor]
    omega
  · rw [ex.1,ex.2,Nat.xor_self]
    simp

theorem inverse_known_add_value (d : Nat) (hd : d<2^10) :
    (d+(993*d)/2^5)%2^15=d/2^5+2^5*d := by
  change (d+(993*d)/32)%32768=d/32+32*d
  have eq : d+(993*d)/32=d/32+32*d := by
    rw [show 993*d=d+32*(31*d) by omega,Nat.add_mul_div_left _ _ (by decide : 0<32)]
    omega
  rw [eq,Nat.mod_eq_of_lt (by omega)]

theorem inverse_window5 (d : Nat) (hd : d<2^10) :
    (993*d)%2^5+2^5*(((993*d)/2^5+d)%2^15)=1025*d := by omega
#print axioms high_split
#print axioms transformed_bound
#print axioms inverse_internal_zeros
#print axioms sparse_977
#print axioms forward_window5
#print axioms forward_window4
#print axioms inverse_window4
#print axioms inverse_window5
#print axioms copy_arith
#print axioms inverse_known_add_value
end ECDSAAdd.Entrant.WindowBoundsDevelop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Win977Develop
open Arithmetic Arithmetic.KnownOutputAdder
abbrev zero : MappedBit := ⟨none,false⟩
def source (S : List Wire) (k : Nat) : List MappedBit :=
  mappedRead S false++List.replicate (10-k) zero
def add (R S carry : List Wire) (cin : Wire) (k : Nat) : Program :=
  mappedAdd (source S k) (R.drop k) (carry.take (19-k)) cin
def sub (R S carry : List Wire) (cin : Wire) (k : Nat) : Program :=
  notRegister (R.drop k)++add R S carry cin k++notRegister (R.drop k)
def copyHigh (R S : List Wire) : Program := copyRegister none S (R.drop 10)
def forward (R S carry : List Wire) (cin : Wire) : Program :=
  copyHigh R S++sub R S carry cin 5++sub R S carry cin 4
def knownAdd5 (R S carry : List Wire) (cin : Wire) : Program :=
  KnownOutputAdder.program (source S 5) (R.drop 5)
    (mappedRead (S.drop 5++S) false) (carry.take 14) cin
def inverse (R S carry : List Wire) (cin : Wire) : Program :=
  add R S carry cin 4++knownAdd5 R S carry cin++copyHigh R S

theorem add_counts (R S carry : List Wire) (cin : Wire) (k : Nat)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length) (hk : k=4 ∨ k=5) :
    toffoliCount (add R S carry cin k)=19-k ∧
    measurementCount (add R S carry cin k)=19-k := by
  have kl : 4≤k ∧ k≤5 := by rcases hk with rfl|rfl <;> decide
  have a:=mappedAdd_counts (source S k) (R.drop k) (carry.take (19-k)) cin
    (by simp [source,mappedRead,hs,hr];omega)
    (by simp [hr];omega)
  have eq : 20-k-1=19-k := by omega
  simpa only [add,List.length_drop,hr,eq] using a

theorem sub_counts (R S carry : List Wire) (cin : Wire) (k : Nat)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length) (hk : k=4 ∨ k=5) :
    toffoliCount (sub R S carry cin k)=19-k ∧
    measurementCount (sub R S carry cin k)=19-k := by
  have a:=add_counts R S carry cin k hr hs hc hk
  have n:=notRegister_counts (R.drop k)
  simp [sub,toffoliCount_append,measurementCount_append,n.1,n.2,a.1,a.2]

theorem copyHigh_counts (R S : List Wire) (hr : R.length=20) (hs : S.length=10) :
    toffoliCount (copyHigh R S)=0 ∧ measurementCount (copyHigh R S)=0 := by
  have a:=copyRegister_counts none S (R.drop 10) (by simp [hr,hs])
  simpa only [copyHigh] using a

theorem knownAdd5_counts (R S carry : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length) :
    toffoliCount (knownAdd5 R S carry cin)=0 ∧ measurementCount (knownAdd5 R S carry cin)=14 := by
  have a:=KnownOutputAdder.program_counts (source S 5) (mappedRead (S.drop 5++S) false)
    (R.drop 5) (carry.take 14) cin (by simp [source,mappedRead,hr,hs])
    (by simp [mappedRead,hr,hs]) (by simp [hr];omega)
  simpa only [knownAdd5,List.length_drop,hr] using a

theorem forward_counts (R S carry : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length) :
    toffoliCount (forward R S carry cin)=29 ∧ measurementCount (forward R S carry cin)=29 := by
  have c:=copyHigh_counts R S hr hs
  have a:=sub_counts R S carry cin 5 hr hs hc (by simp)
  have b:=sub_counts R S carry cin 4 hr hs hc (by simp)
  simp [forward,toffoliCount_append,measurementCount_append,c.1,c.2,a.1,a.2,b.1,b.2]

theorem inverse_counts (R S carry : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length) :
    toffoliCount (inverse R S carry cin)=15 ∧ measurementCount (inverse R S carry cin)=29 := by
  have c:=copyHigh_counts R S hr hs
  have a:=add_counts R S carry cin 4 hr hs hc (by simp)
  have b:=knownAdd5_counts R S carry cin hr hs hc
  simp [inverse,toffoliCount_append,measurementCount_append,c.1,c.2,a.1,a.2,b.1,b.2]
#print axioms forward_counts
#print axioms inverse_counts
end ECDSAAdd.Entrant.Win977Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Win977Develop
open Arithmetic Arithmetic.KnownOutputAdder Arithmetic.CuccaroStreamedSquareWideLayout

theorem zero_value (n : Nat) (s : BasisState) : mappedValue (List.replicate n zero) s=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,mappedValue,zero,MappedBit.value,ih]

theorem source_value (S : List Wire) (k : Nat) (s : BasisState) :
    mappedValue (source S k) s=regValue S s := by
  simp only [source,mappedValue_append,mappedRead_value,zero_value,Nat.mul_zero,Nat.add_zero]

theorem source_wires (S : List Wire) (k : Nat) : mappedWires (source S k)=S := by
  have app (a b : List MappedBit) : mappedWires (a++b)=mappedWires a++mappedWires b := by
    simp [mappedWires,List.flatMap_append]
  rw [source,app,mappedRead_wires]
  have hz : mappedWires (List.replicate (10-k) zero)=[] := by
    simp [mappedWires,zero,List.flatMap_replicate]
  rw [hz,List.append_nil]

theorem add_run (R S carry : List Wire) (cin : Wire) (k : Nat)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length) (hk : k=4 ∨ k=5)
    (hn : (cin::(R++S++carry)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) (hcin : s.basis cin=false) :
    (run (add R S carry cin k) m s).phase=s.phase ∧
    regValue R (run (add R S carry cin k) m s).basis=
      regValue R s.basis%2^k+2^k*((regValue R s.basis/2^k+regValue S s.basis)%2^(20-k)) ∧
    (∀q,q∉R → (run (add R S carry cin k) m s).basis q=s.basis q) := by
  have kl : 4≤k ∧ k≤5 := by rcases hk with rfl|rfl <;> decide
  have bank (q : Wire) :
      (cin::(R.drop k++carry.take (19-k))).count q+S.count q≤
        (cin::(R++S++carry)).count q := by
    have rd := (List.drop_sublist k R).count_le q
    have ct := (List.take_sublist (19-k) carry).count_le q
    simp only [List.count_cons,List.count_append] at *
    omega
  have nd : (cin::(R.drop k++carry.take (19-k))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have old:=List.nodup_iff_count.mp hn q
    have b:=bank q
    omega
  have outside : ∀q∈S,q∉cin::(R.drop k++carry.take (19-k)) := by
    intro q hq bad
    have a:=List.count_pos_iff.mpr hq
    have b:=List.count_pos_iff.mpr bad
    have old:=List.nodup_iff_count.mp hn q
    have cb:=bank q
    omega
  have a:=mappedAdd_correct (source S k) (R.drop k) (carry.take (19-k)) cin nd
    (by rw [source_wires];exact outside)
    (by simp [source,mappedRead,hs,hr];omega)
    (by simp [hr];omega) s m (fun q hq=>hclean q (List.mem_of_mem_take hq))
  change (run (add R S carry cin k) m s).phase=s.phase ∧
    (∀q,q∉R.drop k → (run (add R S carry cin k) m s).basis q=s.basis q) ∧
    regValue (R.drop k) (run (add R S carry cin k) m s).basis=
      (mappedValue (source S k) s.basis+regValue (R.drop k) s.basis+(s.basis cin).toNat)%2^(R.drop k).length at a
  rw [source_value,hcin,Bool.toNat_false,Nat.add_zero,List.length_drop,hr] at a
  have rn : R.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h
    omega
  have split : (R.take k++R.drop k).Nodup := by simpa using rn
  have dis : List.Disjoint (R.take k) (R.drop k) := by
    intro q hq hd
    exact (List.nodup_append.mp split).2.2 q hq q hd rfl
  have low : regValue (R.take k) (run (add R S carry cin k) m s).basis=
      regValue R s.basis%2^k := by
    exact (regValue_congr (R.take k) _ s.basis (fun q hq=>a.2.1 q (fun ht=>dis hq ht))).trans
      (regValue_take_mod R k (by omega) s.basis)
  have out := regValue_append (R.take k) (R.drop k) (run (add R S carry cin k) m s).basis
  rw [List.take_append_drop,List.length_take,hr,Nat.min_eq_left (by omega),low] at out
  have hi:=regValue_drop_div R k (by omega) s.basis
  refine ⟨a.1,?_,?_⟩
  · rw [out,a.2.2,hi]
    rw [Nat.add_comm (regValue S s.basis)]
  · intro q hq
    exact a.2.1 q (fun hd=>hq (List.mem_of_mem_drop hd))
theorem sub_run (R S carry : List Wire) (cin : Wire) (k : Nat)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length) (hk : k=4 ∨ k=5)
    (hn : (cin::(R++S++carry)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) (hcin : s.basis cin=false) :
    (run (sub R S carry cin k) m s).phase=s.phase ∧
    regValue R (run (sub R S carry cin k) m s).basis=
      regValue R s.basis%2^k+2^k*((regValue R s.basis/2^k+2^(20-k)-regValue S s.basis)%2^(20-k)) ∧
    (∀q,q∉R → (run (sub R S carry cin k) m s).basis q=s.basis q) := by
  have kl : 4≤k ∧ k≤5 := by rcases hk with rfl|rfl <;> decide
  have bank (q : Wire) :
      (cin::(R.drop k++carry.take (19-k))).count q+S.count q≤
        (cin::(R++S++carry)).count q := by
    have rd := (List.drop_sublist k R).count_le q
    have ct := (List.take_sublist (19-k) carry).count_le q
    simp only [List.count_cons,List.count_append] at *
    omega
  have nd : (cin::(R.drop k++carry.take (19-k))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have old:=List.nodup_iff_count.mp hn q
    have b:=bank q
    omega
  have outside : ∀q∈S,q∉cin::(R.drop k++carry.take (19-k)) := by
    intro q hq bad
    have a:=List.count_pos_iff.mpr hq
    have b:=List.count_pos_iff.mpr bad
    have old:=List.nodup_iff_count.mp hn q
    have cb:=bank q
    omega
  have a:=mappedSub_correct (source S k) (R.drop k) (carry.take (19-k)) cin nd
    (by rw [source_wires];exact outside)
    (by simp [source,mappedRead,hs,hr];omega)
    (by simp [hr];omega) s m (fun q hq=>hclean q (List.mem_of_mem_take hq)) hcin
  change (run (sub R S carry cin k) m s).phase=s.phase ∧
    (∀q,q∉R.drop k → (run (sub R S carry cin k) m s).basis q=s.basis q) ∧
    regValue (R.drop k) (run (sub R S carry cin k) m s).basis=
      (regValue (R.drop k) s.basis+2^(R.drop k).length-mappedValue (source S k) s.basis)%2^(R.drop k).length at a
  rw [source_value,List.length_drop,hr] at a
  have rn : R.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h
    omega
  have split : (R.take k++R.drop k).Nodup := by simpa using rn
  have dis : List.Disjoint (R.take k) (R.drop k) := by
    intro q hq hd
    exact (List.nodup_append.mp split).2.2 q hq q hd rfl
  have low : regValue (R.take k) (run (sub R S carry cin k) m s).basis=
      regValue R s.basis%2^k := by
    exact (regValue_congr (R.take k) _ s.basis (fun q hq=>a.2.1 q (fun ht=>dis hq ht))).trans
      (regValue_take_mod R k (by omega) s.basis)
  have out := regValue_append (R.take k) (R.drop k) (run (sub R S carry cin k) m s).basis
  rw [List.take_append_drop,List.length_take,hr,Nat.min_eq_left (by omega),low] at out
  have hi:=regValue_drop_div R k (by omega) s.basis
  refine ⟨a.1,?_,?_⟩
  · rw [out,a.2.2,hi]
  · intro q hq
    exact a.2.1 q (fun hd=>hq (List.mem_of_mem_drop hd))

theorem copy_run (R S : List Wire) (hr : R.length=20) (hs : S.length=10)
    (hn : (R++S).Nodup) (s : State) (m : List Bool) :
    (run (copyHigh R S) m s).phase=s.phase ∧
    regValue R (run (copyHigh R S) m s).basis=
      regValue R s.basis%2^10+2^10*((regValue R s.basis/2^10) ^^^ regValue S s.basis) ∧
    (∀q,q∉R → (run (copyHigh R S) m s).basis q=s.basis q) := by
  have nd : (S++R.drop 10).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp hn q
    have d:=(List.drop_sublist 10 R).count_le q
    simp only [List.count_append] at h ⊢
    omega
  have a:=copyRegister_correct none S (R.drop 10) (by simp [hr,hs]) nd (by simp) s m
  change (run (copyHigh R S) m s).phase=s.phase ∧
    (∀q,q∉R.drop 10 → (run (copyHigh R S) m s).basis q=s.basis q) ∧
    regValue (R.drop 10) (run (copyHigh R S) m s).basis=
      regValue (R.drop 10) s.basis ^^^ regValue S s.basis at a
  have rn:R.Nodup:=(List.nodup_append.mp hn).1
  have split : (R.take 10++R.drop 10).Nodup := by simpa using rn
  have dis : List.Disjoint (R.take 10) (R.drop 10) := by
    intro q hq hd
    exact (List.nodup_append.mp split).2.2 q hq q hd rfl
  have low : regValue (R.take 10) (run (copyHigh R S) m s).basis=regValue R s.basis%2^10 := by
    exact (regValue_congr (R.take 10) _ s.basis (fun q hq=>a.2.1 q (fun ht=>dis hq ht))).trans
      (regValue_take_mod R 10 (by omega) s.basis)
  have out := regValue_append (R.take 10) (R.drop 10) (run (copyHigh R S) m s).basis
  rw [List.take_append_drop,List.length_take,hr,Nat.min_eq_left (by omega),low] at out
  have hi:=regValue_drop_div R 10 (by omega) s.basis
  refine ⟨a.1,?_,?_⟩
  · rw [out,a.2.2,hi]
  · intro q hq
    exact a.2.1 q (fun hd=>hq (List.mem_of_mem_drop hd))
#print axioms add_run
#print axioms sub_run
#print axioms copy_run
end ECDSAAdd.Entrant.Win977Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Win977Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem flat_three (P Q R : Program) (m : List Bool) (s : State) :
    run (P++Q++R) m s=
      run R (m.drop (measurementCount P+measurementCount Q))
        (run Q (m.drop (measurementCount P)) (run P m s)) := by
  rw [run_append,run_take,run_append,run_take,measurementCount_append]

theorem outside_data (R S carry : List Wire) (cin : Wire)
    (hn : (cin::(R++S++carry)).Nodup) (q : Wire) (hq : q∈cin::(S++carry)) : q∉R := by
  have h:=List.nodup_iff_count.mp hn q
  have rest:=List.count_pos_iff.mpr hq
  intro bad
  have pos:=List.count_pos_iff.mpr bad
  simp only [List.count_cons,List.count_append] at h rest
  omega

theorem source_frame (R S carry : List Wire) (cin : Wire)
    (hn : (cin::(R++S++carry)).Nodup) (s t : State)
    (hf : ∀q,q∉R → t.basis q=s.basis q) :
    regValue S t.basis=regValue S s.basis ∧
    (∀q∈carry,t.basis q=s.basis q) ∧ t.basis cin=s.basis cin := by
  refine ⟨regValue_congr S _ _ ?_,?_,?_⟩
  · intro q hq
    exact hf q (outside_data R S carry cin hn q (by simp [hq]))
  · intro q hq
    exact hf q (outside_data R S carry cin hn q (by simp [hq]))
  · exact hf cin (outside_data R S carry cin hn cin (by simp))

theorem forward_run (R S carry : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length)
    (hn : (cin::(R++S++carry)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) (hcin : s.basis cin=false)
    (d : Nat) (hd : d<2^10) (hR : regValue R s.basis=d) (hS : regValue S s.basis=d) :
    (run (forward R S carry cin) m s).phase=s.phase ∧
    regValue R (run (forward R S carry cin) m s).basis=977*d ∧
    (∀q,q∉R → (run (forward R S carry cin) m s).basis q=s.basis q) := by
  have rs : (R++S).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  let u:=run (copyHigh R S) m s
  let m1:=m.drop (measurementCount (copyHigh R S))
  have a:=copy_run R S hr hs rs s m
  change u.phase=s.phase ∧ regValue R u.basis=_ ∧ (∀q,q∉R → u.basis q=s.basis q) at a
  have uR : regValue R u.basis=1025*d := by
    rw [a.2.1,hR,hS]
    exact (WindowBoundsDevelop.copy_arith d hd).1
  have us:=source_frame R S carry cin hn s u a.2.2
  have b:=sub_run R S carry cin 5 hr hs hc (by simp) hn u m1
    (fun q hq=>(us.2.1 q hq).trans (hclean q hq)) (us.2.2.trans hcin)
  let v:=run (sub R S carry cin 5) m1 u
  change v.phase=u.phase ∧ regValue R v.basis=_ ∧ (∀q,q∉R → v.basis q=u.basis q) at b
  have vR : regValue R v.basis=993*d := by
    rw [b.2.1,uR,us.1,hS]
    exact WindowBoundsDevelop.forward_window5 d hd
  have vs:=source_frame R S carry cin hn u v b.2.2
  let m2:=m.drop (measurementCount (copyHigh R S)+measurementCount (sub R S carry cin 5))
  have c:=sub_run R S carry cin 4 hr hs hc (by simp) hn v m2
    (fun q hq=>(vs.2.1 q hq).trans ((us.2.1 q hq).trans (hclean q hq)))
    (vs.2.2.trans (us.2.2.trans hcin))
  have outR : regValue R (run (sub R S carry cin 4) m2 v).basis=977*d := by
    rw [c.2.1,vR,vs.1,us.1,hS]
    exact WindowBoundsDevelop.forward_window4 d hd
  have eq : run (forward R S carry cin) m s=run (sub R S carry cin 4) m2 v :=
    flat_three (copyHigh R S) (sub R S carry cin 5) (sub R S carry cin 4) m s
  rw [eq]
  exact ⟨c.1.trans (b.1.trans a.1),outR,fun q hq=>(c.2.2 q hq).trans ((b.2.2 q hq).trans (a.2.2 q hq))⟩
#print axioms forward_run
end ECDSAAdd.Entrant.Win977Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Win977Develop
open Arithmetic Arithmetic.KnownOutputAdder Arithmetic.CuccaroStreamedSquareWideLayout

theorem knownAdd5_eq (R S carry : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length)
    (hn : (cin::(R++S++carry)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) (hcin : s.basis cin=false)
    (d : Nat) (hd : d<2^10) (hR : regValue R s.basis=993*d) (hS : regValue S s.basis=d) :
    run (knownAdd5 R S carry cin) m s=run (add R S carry cin 5) m s := by
  have bank (q : Wire) :
      (cin::(R.drop 5++carry.take 14)).count q+S.count q≤
        (cin::(R++S++carry)).count q := by
    have rd := (List.drop_sublist 5 R).count_le q
    have ct := (List.take_sublist 14 carry).count_le q
    simp only [List.count_cons,List.count_append] at *
    omega
  have nd : (cin::(R.drop 5++carry.take 14)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have old:=List.nodup_iff_count.mp hn q
    have b:=bank q
    omega
  have outside : ∀q∈S,q∉cin::(R.drop 5++carry.take 14) := by
    intro q hq bad
    have a:=List.count_pos_iff.mpr hq
    have b:=List.count_pos_iff.mpr bad
    have old:=List.nodup_iff_count.mp hn q
    have cb:=bank q
    omega
  have aLen : (source S 5).length=(R.drop 5).length := by simp [source,mappedRead,hr,hs]
  have eLen : (mappedRead (S.drop 5++S) false).length=(R.drop 5).length := by simp [mappedRead,hr,hs]
  have cLen : (carry.take 14).length+1=(R.drop 5).length := by simp [hr];omega
  have ev : mappedValue (mappedRead (S.drop 5++S) false) s.basis=d/2^5+2^5*d := by
    rw [mappedRead_value,regValue_append,regValue_drop_div S 5 (by omega),hS]
    simp only [List.length_drop,hs]
  have rv : regValue (R.drop 5) s.basis=(993*d)/2^5 := by
    rw [regValue_drop_div R 5 (by omega),hR]
  have ready : Arithmetic.KnownOutputAdder.Ready (source S 5)
      (mappedRead (S.drop 5++S) false) (R.drop 5) (s.basis cin) s.basis := by
    apply ready_of_value _ _ _ _ _ aLen eLen
    rw [ev,source_value,hS,rv,hcin,Bool.toNat_false,Nat.add_zero,List.length_drop,hr]
    exact (WindowBoundsDevelop.inverse_known_add_value d hd).symm
  have eq:=program_eq_mappedAdd (source S 5) (mappedRead (S.drop 5++S) false)
    (R.drop 5) (carry.take 14) cin nd (by rw [source_wires];exact outside)
    (by rw [mappedRead_wires];intro q hq;rcases List.mem_append.mp hq with hq|hq
        exact outside q (List.mem_of_mem_drop hq)
        exact outside q hq)
    aLen eLen cLen s m (fun q hq=>hclean q (List.mem_of_mem_take hq)) ready
  exact eq


theorem knownAdd5_run (R S carry : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length)
    (hn : (cin::(R++S++carry)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) (hcin : s.basis cin=false)
    (d : Nat) (hd : d<2^10) (hR : regValue R s.basis=993*d) (hS : regValue S s.basis=d) :
    (run (knownAdd5 R S carry cin) m s).phase=s.phase ∧
    regValue R (run (knownAdd5 R S carry cin) m s).basis=1025*d ∧
    (∀q,q∉R → (run (knownAdd5 R S carry cin) m s).basis q=s.basis q) := by
  rw [knownAdd5_eq R S carry cin hr hs hc hn s m hclean hcin d hd hR hS]
  have a:=add_run R S carry cin 5 hr hs hc (by simp) hn s m hclean hcin
  refine ⟨a.1,?_,a.2.2⟩
  rw [a.2.1,hR,hS]
  exact WindowBoundsDevelop.inverse_window5 d hd

theorem inverse_run (R S carry : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length)
    (hn : (cin::(R++S++carry)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) (hcin : s.basis cin=false)
    (d : Nat) (hd : d<2^10) (hR : regValue R s.basis=977*d) (hS : regValue S s.basis=d) :
    (run (inverse R S carry cin) m s).phase=s.phase ∧
    regValue R (run (inverse R S carry cin) m s).basis=d ∧
    (∀q,q∉R → (run (inverse R S carry cin) m s).basis q=s.basis q) := by
  have rs : (R++S).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  let u:=run (add R S carry cin 4) m s
  let m1:=m.drop (measurementCount (add R S carry cin 4))
  have a:=add_run R S carry cin 4 hr hs hc (by simp) hn s m hclean hcin
  change u.phase=s.phase ∧ regValue R u.basis=_ ∧ (∀q,q∉R → u.basis q=s.basis q) at a
  have uR : regValue R u.basis=993*d := by
    rw [a.2.1,hR,hS]
    exact WindowBoundsDevelop.inverse_window4 d hd
  have us:=source_frame R S carry cin hn s u a.2.2
  have b:=knownAdd5_run R S carry cin hr hs hc hn u m1
    (fun q hq=>(us.2.1 q hq).trans (hclean q hq)) (us.2.2.trans hcin)
    d hd uR (us.1.trans hS)
  let v:=run (knownAdd5 R S carry cin) m1 u
  change v.phase=u.phase ∧ regValue R v.basis=1025*d ∧ (∀q,q∉R → v.basis q=u.basis q) at b
  have vs:=source_frame R S carry cin hn u v b.2.2
  let m2:=m.drop (measurementCount (add R S carry cin 4)+measurementCount (knownAdd5 R S carry cin))
  have c:=copy_run R S hr hs rs v m2
  have outR : regValue R (run (copyHigh R S) m2 v).basis=d := by
    rw [c.2.1,b.2.1,vs.1,us.1,hS]
    exact (WindowBoundsDevelop.copy_arith d hd).2
  have eq : run (inverse R S carry cin) m s=run (copyHigh R S) m2 v :=
    flat_three (add R S carry cin 4) (knownAdd5 R S carry cin) (copyHigh R S) m s
  rw [eq]
  exact ⟨c.1.trans (b.1.trans a.1),outR,fun q hq=>(c.2.2 q hq).trans ((b.2.2 q hq).trans (a.2.2 q hq))⟩
#print axioms knownAdd5_eq
#print axioms knownAdd5_run
#print axioms inverse_run
end ECDSAAdd.Entrant.Win977Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Win977Develop
open Arithmetic Arithmetic.KnownOutputAdder

theorem geometry (R S carry : List Wire) (cin k : Nat)
    (hn : (cin::(R++S++carry)).Nodup) :
    (cin::(R.drop k++carry.take (19-k))).Nodup ∧
    (∀q∈S,q∉cin::(R.drop k++carry.take (19-k))) := by
  have bank (q : Wire) :
      (cin::(R.drop k++carry.take (19-k))).count q+S.count q≤
        (cin::(R++S++carry)).count q := by
    have rd := (List.drop_sublist k R).count_le q
    have ct := (List.take_sublist (19-k) carry).count_le q
    simp only [List.count_cons,List.count_append] at *
    omega
  constructor
  · apply List.nodup_iff_count.mpr
    intro q
    have old:=List.nodup_iff_count.mp hn q
    have b:=bank q
    omega
  · intro q hq bad
    have a:=List.count_pos_iff.mpr hq
    have b:=List.count_pos_iff.mpr bad
    have old:=List.nodup_iff_count.mp hn q
    have cb:=bank q
    omega

theorem source_member (S : List Wire) (k : Nat) (b : MappedBit) (hb : b∈source S k)
    (q : Wire) (hq : q∈b.wire) : q∈S := by
  rw [←source_wires S k]
  apply List.mem_flatMap.mpr
  exact ⟨b,hb,by simpa using hq⟩

theorem add_physical (R S carry : List Wire) (cin k : Nat)
    (hn : (cin::(R++S++carry)).Nodup) : GatePhysical (add R S carry cin k) := by
  have geo:=geometry R S carry cin k hn
  exact mappedAdd_physical _ _ _ _ geo.1
    (fun b hb q hq=>geo.2 q (source_member S k b hb q hq))

theorem sub_physical (R S carry : List Wire) (cin k : Nat)
    (hn : (cin::(R++S++carry)).Nodup) : GatePhysical (sub R S carry cin k) := by
  simp only [sub,gatePhysical_append]
  exact ⟨⟨notRegister_physical _,add_physical R S carry cin k hn⟩,notRegister_physical _⟩

theorem copyHigh_physical (R S carry : List Wire) (cin : Wire)
    (hn : (cin::(R++S++carry)).Nodup) : GatePhysical (copyHigh R S) := by
  apply copyRegister_physical
  · apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp hn q
    have d:=(List.drop_sublist 10 R).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  · simp

theorem knownAdd5_physical (R S carry : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length)
    (hn : (cin::(R++S++carry)).Nodup) : GatePhysical (knownAdd5 R S carry cin) := by
  have geo:=geometry R S carry cin 5 hn
  apply KnownOutputAdder.program_physical
    (source S 5) (mappedRead (S.drop 5++S) false) (R.drop 5) (carry.take 14) cin
    (by simp [source,mappedRead,hr,hs]) (by simp [mappedRead,hr,hs])
    (by simp [hr];omega) geo.1
    (fun b hb q hq=>geo.2 q (source_member S 5 b hb q hq))
  intro b hb q hq
  have mem : q∈mappedWires (mappedRead (S.drop 5++S) false) :=
    List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  rw [mappedRead_wires] at mem
  apply geo.2 q
  rcases List.mem_append.mp mem with h|h
  · exact List.mem_of_mem_drop h
  · exact h

theorem forward_physical (R S carry : List Wire) (cin : Wire)
    (hn : (cin::(R++S++carry)).Nodup) : GatePhysical (forward R S carry cin) := by
  simp only [forward,gatePhysical_append]
  exact ⟨⟨copyHigh_physical R S carry cin hn,sub_physical R S carry cin 5 hn⟩,
    sub_physical R S carry cin 4 hn⟩

theorem inverse_physical (R S carry : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hc : 15≤carry.length)
    (hn : (cin::(R++S++carry)).Nodup) : GatePhysical (inverse R S carry cin) := by
  simp only [inverse,gatePhysical_append]
  exact ⟨⟨add_physical R S carry cin 4 hn,knownAdd5_physical R S carry cin hr hs hc hn⟩,
    copyHigh_physical R S carry cin hn⟩

def ports (R S carry : List Wire) (cin : Wire) : Finset Wire := (R++S++carry++[cin]).toFinset

theorem window_ports (R S carry : List Wire) (cin k : Nat) :
    (S++R.drop k++carry.take (19-k)++[cin]).toFinset⊆ports R S carry cin := by
  intro q hq
  simp only [ports,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq ⊢
  rcases hq with h|h|h|h
  · tauto
  · have old:=List.mem_of_mem_drop h
    tauto
  · have old:=List.mem_of_mem_take h
    tauto
  · tauto

theorem add_support (R S carry : List Wire) (cin k : Nat) :
    wires (add R S carry cin k)⊆ports R S carry cin := by
  have h:=mappedAdd_wires_subset (source S k) (R.drop k) (carry.take (19-k)) cin
  rw [source_wires] at h
  exact h.trans (window_ports R S carry cin k)

theorem sub_support (R S carry : List Wire) (cin k : Nat) :
    wires (sub R S carry cin k)⊆ports R S carry cin := by
  have h:=mappedSub_wires_subset (source S k) (R.drop k) (carry.take (19-k)) cin
  rw [source_wires] at h
  exact h.trans (window_ports R S carry cin k)

theorem copyHigh_support (R S carry : List Wire) (cin : Wire) :
    wires (copyHigh R S)⊆ports R S carry cin := by
  have h:=copyRegister_wires_subset none S (R.drop 10)
  intro q hq
  have mem:=h hq
  simp only [ports,List.mem_toFinset,Option.toList_none,List.nil_append,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,or_assoc] at mem ⊢
  rcases mem with h|h
  · tauto
  · have old:=List.mem_of_mem_drop h
    tauto

theorem knownAdd5_support (R S carry : List Wire) (cin : Wire) :
    wires (knownAdd5 R S carry cin)⊆ports R S carry cin := by
  have h:=KnownOutputAdder.program_support (source S 5) (mappedRead (S.drop 5++S) false)
    (R.drop 5) (carry.take 14) cin
  rw [source_wires,mappedRead_wires] at h
  intro q hq
  have mem:=h hq
  simp only [ports,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at mem ⊢
  rcases mem with h|h|h|h|h|h
  · tauto
  · have old:=List.mem_of_mem_drop h
    tauto
  · tauto
  · have old:=List.mem_of_mem_drop h
    tauto
  · have old:=List.mem_of_mem_take h
    tauto
  · tauto

theorem forward_support (R S carry : List Wire) (cin : Wire) :
    wires (forward R S carry cin)⊆ports R S carry cin := by
  simp only [forward,wires_append,Finset.union_subset_iff]
  exact ⟨⟨copyHigh_support R S carry cin,sub_support R S carry cin 5⟩,sub_support R S carry cin 4⟩

theorem inverse_support (R S carry : List Wire) (cin : Wire) :
    wires (inverse R S carry cin)⊆ports R S carry cin := by
  simp only [inverse,wires_append,Finset.union_subset_iff]
  exact ⟨⟨add_support R S carry cin 4,knownAdd5_support R S carry cin⟩,copyHigh_support R S carry cin⟩
#print axioms forward_physical
#print axioms inverse_physical
#print axioms forward_support
#print axioms inverse_support
end ECDSAAdd.Entrant.Win977Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Win977Develop
open Arithmetic Arithmetic.KnownOutputAdder

theorem prepare_slots (b d : MappedBit) (y c : Wire) : Challenge.gateSlots (prepare b d y c)≤5 := by
  cases hb : b.wire <;> cases hd : d.wire <;> cases fb : b.flip <;> cases fd : d.flip <;>
    simp [prepare,xorBit,hb,hd,fb,fd,Challenge.gateSlots,Challenge.instructionSlots]

theorem known_slots (bits sums : List MappedBit) (ys cs : List Wire) (cin : Wire) :
    Challenge.gateSlots (KnownOutputAdder.program bits ys sums cs cin)≤14*bits.length := by
  induction bits,ys,sums,cs,cin using KnownOutputAdder.program.induct with
  | case1 b b' bs y y' ys d d' ds c cs cin ih =>
    have hp:=prepare_slots b' d' y' c
    have hd:=Baselines.mappedBit_gateSlots_le b y cin c
    simp only [KnownOutputAdder.program,Challenge.gateSlots_append,List.length_cons] at ih ⊢
    omega
  | case2 b y d cs cin =>
    have h:=(Baselines.mappedBit_gateSlots_le b y cin cin).2.2
    simpa only [KnownOutputAdder.program,List.length_singleton] using h.trans (by decide : 3≤14)
  | case3 bits ys sums cs cin other => simp [KnownOutputAdder.program]

theorem source_length (S : List Wire) (k : Nat) (hs : S.length=10) (hk : k=4 ∨ k=5) :
    (source S k).length=20-k := by
  have h : 4≤k ∧ k≤5:=by rcases hk with rfl|rfl <;> decide
  simp only [source,List.length_append,mappedRead,List.length_map,List.length_replicate,hs]
  omega

theorem add_slots (R S carry : List Wire) (cin k : Nat)
    (hs : S.length=10) (hk : k=4 ∨ k=5) : Challenge.gateSlots (add R S carry cin k)≤17*(20-k) := by
  have h:=Baselines.mappedAdd_gateSlots_le (source S k) (R.drop k) (carry.take (19-k)) cin
  simpa only [add,source_length S k hs hk] using h

theorem sub_slots (R S carry : List Wire) (cin k : Nat)
    (hr : R.length=20) (hs : S.length=10) (hk : k=4 ∨ k=5) :
    Challenge.gateSlots (sub R S carry cin k)≤19*(20-k) := by
  have h:=add_slots R S carry cin k hs hk
  simp only [sub,Challenge.gateSlots_append,Baselines.notRegister_gateSlots,List.length_drop,hr]
  omega

theorem knownAdd5_slots (R S carry : List Wire) (cin : Wire) (hs : S.length=10) :
    Challenge.gateSlots (knownAdd5 R S carry cin)≤210 := by
  have h:=known_slots (source S 5) (mappedRead (S.drop 5++S) false) (R.drop 5) (carry.take 14) cin
  simpa only [knownAdd5,source_length S 5 hs (by simp)] using h

theorem forward_slots (R S carry : List Wire) (cin : Wire) (hr : R.length=20) (hs : S.length=10) :
    Challenge.gateSlots (forward R S carry cin)≤599 := by
  have a:=sub_slots R S carry cin 5 hr hs (by simp)
  have b:=sub_slots R S carry cin 4 hr hs (by simp)
  have cp : Challenge.gateSlots (copyHigh R S)=10 := by simp [copyHigh,hr,hs]
  simp only [forward,Challenge.gateSlots_append,cp]
  omega

theorem inverse_slots (R S carry : List Wire) (cin : Wire) (hr : R.length=20) (hs : S.length=10) :
    Challenge.gateSlots (inverse R S carry cin)≤492 := by
  have a:=add_slots R S carry cin 4 hs (by simp)
  have b:=knownAdd5_slots R S carry cin hs
  have cp : Challenge.gateSlots (copyHigh R S)=10 := by simp [copyHigh,hr,hs]
  simp only [inverse,Challenge.gateSlots_append,cp]
  omega
#print axioms forward_slots
#print axioms inverse_slots
end ECDSAAdd.Entrant.Win977Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.MixedLiteralAdderDevelop
open Arithmetic Arithmetic.KnownOutputAdder
def literal (expected : Bool) : MappedBit := ⟨none,expected⟩

def head (expected : Bool) (flag : Bool) (b b' : MappedBit) (y y' cin c : Wire) : Program :=
  if flag then prepare b' (literal expected) y' c else mappedMajority b y cin c

def Ready (expected : Bool) (bits : List MappedBit) (flags : List Bool) (ys : List Wire)
    (cin : Bool) (s : BasisState) : Prop :=
  List.Forall₂ (fun known value => known=true → value=expected) flags (sumBits bits ys cin s)

def program (expected : Bool) : List MappedBit → List Wire → List Bool → List Wire → Wire → Program
  | b::b'::bs,y::y'::ys,_::flag::flags,c::cs,cin =>
      head expected flag b b' y y' cin c++program expected (b'::bs) (y'::ys) (flag::flags) cs c++
        mappedEraseCarry b y cin c++mappedSum b y cin
  | [b],[y],[_],_,cin => mappedSum b y cin
  | _,_,_,_,_ => []

theorem head_counts (expected : Bool) (flag : Bool) (b b' : MappedBit) (y y' cin c : Wire) :
    toffoliCount (head expected flag b b' y y' cin c)=(if flag then 0 else 1) ∧
    measurementCount (head expected flag b b' y y' cin c)=0 := by
  have a:=prepare_counts b' (literal expected) y' c
  have o:=mappedBit_counts b y cin c
  cases flag <;> simp [head,a.1,a.2,o.1,o.2.1]
theorem program_counts (expected : Bool) (bits : List MappedBit) (sums : List Bool) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) :
    toffoliCount (program expected bits ys sums carry cin)=sums.tail.count false ∧
    measurementCount (program expected bits ys sums carry cin)=ys.length-1 := by
  induction ys generalizing bits sums carry cin with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => simp at hs
      | cons d ds =>
        cases ys with
        | nil =>
          have hb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
          have hd : ds=[] := List.eq_nil_of_length_eq_zero (by simpa using hs)
          subst bs; subst ds
          have h := mappedBit_counts b y cin cin
          simpa [program] using And.intro h.2.2.2.2.1 h.2.2.2.2.2
        | cons y' ys =>
          cases bs with
          | nil => simp at hl
          | cons b' bs =>
            cases ds with
            | nil => simp at hs
            | cons d' ds =>
              cases carry with
              | nil => simp at hc
              | cons c cs =>
                have h := head_counts expected d' b b' y y' cin c
                have t := ih (b'::bs) (d'::ds) cs c
                  (by simpa using hl) (by simpa using hs) (by simpa using hc)
                have k := mappedBit_counts b y cin c
                cases d' <;> simp only [program,toffoliCount_append,measurementCount_append,h.1,h.2,
                  t.1,t.2,k.2.2.1,k.2.2.2.1,k.2.2.2.2.1,k.2.2.2.2.2]
                all_goals simp [Nat.add_comm]
private theorem head_source_mem (b : MappedBit) (bs : List MappedBit)
    (q : Wire) (hq : q∈b.wire) : q∈mappedWires (b::bs) := by
  cases hw : b.wire with
  | none => simp [hw] at hq
  | some a =>
    have eq : a=q := by simpa [hw] using hq
    subst a
    simp [mappedWires,hw]

private theorem tail_source_mem (b : MappedBit) (bs : List MappedBit)
    (q : Wire) (hq : q∈mappedWires bs) : q∈mappedWires (b::bs) := by
  exact List.mem_append_right _ hq
theorem affine_literal (a b c expected : Bool) (h : sumBit a b c=expected) : ((b ^^ a) ^^ expected)=c := by
  cases a <;> cases b <;> cases c <;> cases expected <;> simp_all [sumBit]

theorem program_eq_mappedAdd (expected : Bool) (bits : List MappedBit) (sums : List Bool) (ys carry : List Wire)
    (cin : Wire) (hn : (cin::(ys++carry)).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false)
    (ready : Ready expected bits sums ys (s.basis cin) s.basis) :
    run (program expected bits ys sums carry cin) m s=run (mappedAdd bits ys carry cin) m s := by
  induction ys generalizing bits sums carry cin s m with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => simp at hs
      | cons d ds =>
        cases ys with
        | nil =>
          have hb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
          have hd : ds=[] := List.eq_nil_of_length_eq_zero (by simpa using hs)
          subst bs; subst ds
          rfl
        | cons y' ys =>
          cases bs with
          | nil => simp at hl
          | cons b' bs =>
            cases ds with
            | nil => simp at hs
            | cons d' ds =>
              cases carry with
              | nil => simp at hc
              | cons c cs =>
                have cnt := List.nodup_iff_count.mp hn
                have yc : y≠c := by
                  intro bad; have h := cnt c; subst y
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
                  omega
                have yc' : y'≠c := by
                  intro bad; have h := cnt c; subst y'
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
                  omega
                have cc : cin≠c := by
                  intro bad; have h := cnt c; subst cin
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
                  omega
                have ctail : c∉y'::ys := by
                  intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
                  omega
                have ccs : c∉cs := by
                  intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
                  omega
                have three : [y,cin,c].Nodup := by
                  apply List.nodup_iff_count.mpr
                  intro q; have h := cnt q
                  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
                  omega
                have nd : (c::((y'::ys)++cs)).Nodup := by
                  apply List.nodup_iff_count.mpr
                  intro q; have h := cnt q
                  simp only [List.count_cons,List.count_append] at h ⊢
                  omega
                have source : ∀q∈mappedWires (b'::bs),q∉c::((y'::ys)++cs) := by
                  intro q hq bad
                  exact ha q (tail_source_mem b _ q hq)
                    (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have sourceC (q : Wire) (hq : q∈mappedWires (b::b'::bs)) : q≠c := by
                  intro bad; exact ha q hq (by simp [bad])
                let K := carryBit (b.value s.basis) (s.basis y) (s.basis cin)
                let u : State := ⟨s.phase,writeBit s.basis c K⟩
                have clean0 : s.basis c=false := hclean c (by simp)
                have rt : Ready expected (b'::bs) (d'::ds) (y'::ys) K s.basis := by
                  exact (List.forall₂_cons.mp ready).2
                have next : d'=true → sumBit (b'.value s.basis) (s.basis y') K=expected := by
                  exact (List.forall₂_cons.mp rt).1
                have old (mm : List Bool) : run (mappedMajority b y cin c) mm s=u := by
                  rw [mappedMajority_correct b y cin c three]
                  · simp [u,K,clean0]
                  · intro q hq bad
                    exact ha q (head_source_mem b _ q hq)
                      (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have pre (mm : List Bool) : run (head expected d' b b' y y' cin c) mm s=u := by
                  cases flagEq : d' with
                  | false => simpa [head,flagEq] using old mm
                  | true =>
                    have val : sumBit (b'.value s.basis) (s.basis y') K=expected:=next flagEq
                    have affine : ((s.basis y' ^^ b'.value s.basis) ^^ expected)=K := affine_literal _ _ _ expected val
                    change run (prepare b' (literal expected) y' c) mm s=u
                    rw [prepare_correct b' (literal expected) y' c yc'
                      (fun q hq => sourceC q (tail_source_mem b _ q (head_source_mem b' bs q hq)))
                      (by simp [literal]) s mm]
                    have zv : (literal expected).value s.basis=expected:=by simp [literal,MappedBit.value]
                    simp only [clean0,Bool.false_xor,zv,Bool.xor_false,affine]
                    rfl
                have keep (q : Wire) (hne : q≠c) : u.basis q=s.basis q := by
                  simp [u,writeBit,hne]
                have uc : u.basis c=K := by simp [u,writeBit]
                have tailReady : Ready expected (b'::bs) (d'::ds) (y'::ys) (u.basis c) u.basis := by
                  have eq : sumBits (b'::bs) (y'::ys) K u.basis=sumBits (b'::bs) (y'::ys) K s.basis := by
                    apply sumBits_congr
                    · intro q hq
                      exact keep q (sourceC q (tail_source_mem b _ q hq))
                    · intro q hq
                      exact keep q (fun bad=>ctail (bad ▸ hq))
                  unfold Ready
                  rw [uc,eq]
                  exact rt
                have clean : ∀q∈cs,u.basis q=false := by
                  intro q hq
                  rw [keep q (fun bad => ccs (bad ▸ hq))]
                  exact hclean q (by simp [hq])
                have tail (mm : List Bool) := ih (b'::bs) (d'::ds) cs c nd source
                  (by simpa using hl) (by simpa using hs) (by simpa using hc) u mm clean tailReady
                have pc := head_counts expected d' b b' y y' cin c
                have oc := mappedBit_counts b y cin c
                have nc := program_counts expected (b'::bs) (d'::ds) (y'::ys) cs c
                  (by simpa using hl) (by simpa using hs) (by simpa using hc)
                have mc := mappedAdd_counts (b'::bs) (y'::ys) cs c
                  (by simpa using hl) (by simpa using hc)
                rw [program,mappedAdd]
                simp only [List.append_assoc,run_append,run_take,pc.2,oc.2.1,
                  nc.2,mc.2,List.take_zero,List.drop_zero]
                rw [pre,old,tail]

#print axioms program_eq_mappedAdd
end ECDSAAdd.Entrant.MixedLiteralAdderDevelop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.MixedLiteralAdderDevelop
open Arithmetic Arithmetic.KnownOutputAdder

def fullKnown (expected : Bool) (bits : List MappedBit) (ys cs : List Wire) (cin : Wire) : Program :=
  KnownOutputAdder.program bits ys (List.replicate ys.length (literal expected)) cs cin

theorem fullKnown_physical (expected : Bool) (bits : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (hn : (cin::ys++cs).Nodup) (ha : ∀b∈bits,∀q∈b.wire,q∉cin::ys++cs)
    (hl : bits.length=ys.length) (hc : cs.length+1=ys.length) :
    GatePhysical (fullKnown expected bits ys cs cin) := by
  apply KnownOutputAdder.program_physical _ _ _ _ _ hl (by simp) hc hn ha
  intro b hb q hq
  have mem : q∈mappedWires (List.replicate ys.length (literal expected)) :=
    List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  simp [mappedWires,literal,List.flatMap_replicate] at mem

theorem fullKnown_support (expected : Bool) (bits : List MappedBit) (ys cs : List Wire) (cin : Wire) :
    wires (fullKnown expected bits ys cs cin)⊆(mappedWires bits++ys++cs++[cin]).toFinset := by
  have h:=KnownOutputAdder.program_support bits (List.replicate ys.length (literal expected)) ys cs cin
  simpa [fullKnown,mappedWires,literal,List.flatMap_replicate] using h

theorem prepare_slots (expected : Bool) (b : MappedBit) (y c : Wire) :
    Challenge.gateSlots (prepare b (literal expected) y c)≤4 := by
  cases hw : b.wire <;> cases hf : b.flip <;> cases expected <;>
    simp [prepare,xorBit,literal,hw,hf,Challenge.gateSlots,Challenge.instructionSlots]

theorem program_members (expected : Bool) (bits : List MappedBit) (ys : List Wire) (flags : List Bool)
    (cs : List Wire) (cin : Wire) :
    ∀i∈program expected bits ys flags cs cin,
      i∈mappedAdd bits ys cs cin ∨ i∈fullKnown expected bits ys cs cin := by
  induction bits,ys,flags,cs,cin using program.induct with
  | case1 b b' bs y y' ys d flag flags c cs cin ih =>
    intro i hi
    have md:=ih i
    simp only [program,List.mem_append] at hi
    rcases hi with ((hh|hm)|he)|hs
    · cases flag <;> simp only [head,Bool.false_eq_true,if_false,if_true] at hh
      · apply Or.inl
        simp only [mappedAdd,List.mem_append]
        tauto
      · apply Or.inr
        change i∈prepare b' (literal expected) y' c++
          fullKnown expected (b'::bs) (y'::ys) cs c++
          mappedEraseCarry b y cin c++mappedSum b y cin
        simp only [List.mem_append]
        tauto
    · rcases md hm with hm|hm
      · apply Or.inl
        simp only [mappedAdd,List.mem_append]
        tauto
      · apply Or.inr
        change i∈prepare b' (literal expected) y' c++
          fullKnown expected (b'::bs) (y'::ys) cs c++
          mappedEraseCarry b y cin c++mappedSum b y cin
        simp only [List.mem_append]
        tauto
    · apply Or.inl
      simp only [mappedAdd,List.mem_append]
      tauto
    · apply Or.inl
      simp only [mappedAdd,List.mem_append]
      tauto
  | case2 b y d cs cin =>
    intro i hi
    exact Or.inl hi
  | case3 bits ys flags cs cin other =>
    simp only [program]
    simp

theorem program_physical (expected : Bool) (bits : List MappedBit) (ys : List Wire) (flags : List Bool)
    (cs : List Wire) (cin : Wire) (hn : (cin::ys++cs).Nodup)
    (ha : ∀b∈bits,∀q∈b.wire,q∉cin::ys++cs)
    (hl : bits.length=ys.length) (hc : cs.length+1=ys.length) :
    GatePhysical (program expected bits ys flags cs cin) := by
  have old:=mappedAdd_physical bits ys cs cin hn ha
  have kn:=fullKnown_physical expected bits ys cs cin hn ha hl hc
  intro i hi
  rcases program_members expected bits ys flags cs cin i hi with hi|hi
  · exact old i hi
  · exact kn i hi

theorem wire_exists (p : Program) (q : Wire) :
    q∈wires p ↔ ∃i∈p,q∈i.wires := by
  induction p with
  | nil => simp [wires]
  | cons i p ih => simp [wires,ih]

theorem program_support (expected : Bool) (bits : List MappedBit) (ys : List Wire) (flags : List Bool)
    (cs : List Wire) (cin : Wire) :
    wires (program expected bits ys flags cs cin)⊆(mappedWires bits++ys++cs++[cin]).toFinset := by
  intro q hq
  obtain ⟨i,hi,hqi⟩:=(wire_exists _ _).mp hq
  rcases program_members expected bits ys flags cs cin i hi with hi|hi
  · exact mappedAdd_wires_subset bits ys cs cin ((wire_exists _ _).mpr ⟨i,hi,hqi⟩)
  · exact fullKnown_support expected bits ys cs cin ((wire_exists _ _).mpr ⟨i,hi,hqi⟩)

theorem program_slots (expected : Bool) (bits : List MappedBit) (ys : List Wire) (flags : List Bool)
    (cs : List Wire) (cin : Wire) :
    Challenge.gateSlots (program expected bits ys flags cs cin)≤17*bits.length := by
  induction bits,ys,flags,cs,cin using program.induct with
  | case1 b b' bs y y' ys d flag flags c cs cin ih =>
    have hd:=Baselines.mappedBit_gateSlots_le b y cin c
    have hp:=prepare_slots expected b' y' c
    have hh : Challenge.gateSlots (head expected flag b b' y y' cin c)≤8 := by
      cases flag <;> simp only [head,Bool.false_eq_true,if_false,if_true]
      · exact hd.1
      · exact hp.trans (by decide)
    simp only [program,Challenge.gateSlots_append,List.length_cons] at ih ⊢
    omega
  | case2 b y d cs cin =>
    have h:=(Baselines.mappedBit_gateSlots_le b y cin cin).2.2
    simpa only [program,List.length_singleton] using h.trans (by decide : 3≤17)
  | case3 bits ys flags cs cin other => simp [program]
#print axioms program_physical
#print axioms program_support
#print axioms program_slots
end ECDSAAdd.Entrant.MixedLiteralAdderDevelop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.MixedLiteralAdderDevelop
open Arithmetic Arithmetic.KnownOutputAdder

theorem boolValue_bit (xs : List Bool) (i : Nat) :
    (boolValue xs).testBit i=xs.getD i false := by
  induction xs generalizing i with
  | nil => simp [boolValue]
  | cons b bs ih =>
    cases i with
    | zero =>
      cases b <;> simp [boolValue,Nat.testBit_eq_decide_div_mod_eq,Nat.add_mod]
    | succ i =>
      have low : b.toNat<2:=by cases b <;> decide
      have div2 : boolValue (b::bs)/2=boolValue bs := by simp only [boolValue];omega
      rw [Nat.testBit_succ,div2,ih]
      rfl

theorem forall_known_of_bits (expected : Bool) (flags xs : List Bool) (hl : flags.length=xs.length)
    (hv : ∀i,i<flags.length → flags.getD i false=true → xs.getD i false=expected) :
    List.Forall₂ (fun known value=>known=true → value=expected) flags xs := by
  induction flags generalizing xs with
  | nil =>
    have hxs : xs=[]:=List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst xs
    exact List.Forall₂.nil
  | cons f flags ih =>
    cases xs with
    | nil => simp at hl
    | cons x xs =>
      apply List.Forall₂.cons
      · intro hf
        simpa using hv 0 (by simp) (by simpa using hf)
      · apply ih xs (by simpa using hl)
        intro i hi hf
        have h:=hv (i+1) (by simpa using Nat.succ_lt_succ hi) (by simpa using hf)
        simpa using h

theorem ready_of_number (expected : Bool) (bits : List MappedBit) (flags : List Bool) (ys : List Wire)
    (cin : Bool) (s : BasisState) (hl : bits.length=ys.length) (hf : flags.length=ys.length)
    (hv : ∀i,i<flags.length → flags.getD i false=true →
      ((mappedValue bits s+regValue ys s+cin.toNat)%2^ys.length).testBit i=expected) :
    Ready expected bits flags ys cin s := by
  apply forall_known_of_bits expected flags (sumBits bits ys cin s)
    (hf.trans (sumBits_length bits ys cin s hl).symm)
  intro i hi hknown
  rw [←boolValue_bit,sumBits_value bits ys cin s hl]
  exact hv i hi hknown

def mask43 : List Bool := (List.range 43).map (fun i => decide ((20 ≤ i ∧ i < 32) ∨ i = 42))
theorem mask43_count : mask43.tail.count false=29 := by decide +kernel

theorem mask43_bits (i : Nat) (hi : i < 43) :
    mask43.getD i false=true ↔ ((20 ≤ i ∧ i < 32) ∨ i = 42) := by
  interval_cases i <;> decide +kernel

theorem complement_mask43 (d i : Nat) (hd : d ≤ 976) (hi : i < 43)
    (hk : mask43.getD i false=true) :
    (2^43-1-(2^32+977)*d).testBit i=true := by
  have upper : (2^32+977)*d<2^42 := by
    have h:=WindowBoundsDevelop.transformed_bound 0 d (by decide) hd
    simpa using h
  have zeroBit : ((2^32+977)*d).testBit i=false := by
    rcases (mask43_bits i hi).mp hk with h|rfl
    · exact WindowBoundsDevelop.inverse_internal_zeros d i hd h.1 h.2
    · exact Nat.testBit_lt_two_pow upper
  rw [show 2^43-1-(2^32+977)*d=2^43-((2^32+977)*d+1) by omega,
    Nat.testBit_two_pow_sub_succ (show (2^32+977)*d<2^43 by omega)]
  rw [show decide (i < 43)=true from decide_eq_true hi,zeroBit]
  rfl

def upper33 : List Bool := (List.range 33).map (fun i => decide (10 ≤ i))
theorem upper33_count : upper33.tail.count false=9 := by decide +kernel

theorem upper33_bits (i : Nat) (hi : i < 33) : upper33.getD i false=true ↔ 10 ≤ i := by
  interval_cases i <;> decide +kernel

theorem complement_upper33 (d i : Nat) (hd : d < 2^10) (hi : i < 33)
    (hk : upper33.getD i false=true) :
    (2^33-1-d).testBit i=true := by
  have lower : 10 ≤ i :=(upper33_bits i hi).mp hk
  have mono : 2^10≤2^i:=Nat.pow_le_pow_right (by decide) lower
  have zeroBit : d.testBit i=false:=Nat.testBit_lt_two_pow (by omega)
  rw [show 2^33-1-d=2^33-(d+1) by omega,
    Nat.testBit_two_pow_sub_succ (show d<2^33 by omega)]
  rw [show decide (i < 33)=true from decide_eq_true hi,zeroBit]
  rfl
#print axioms boolValue_bit
#print axioms ready_of_number
#print axioms mask43_count
#print axioms complement_mask43
#print axioms upper33_count
#print axioms complement_upper33
end ECDSAAdd.Entrant.MixedLiteralAdderDevelop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.MixedLiteralAdderDevelop
open Arithmetic

def mixedSub (expected : Bool) (bits : List MappedBit) (flags : List Bool)
    (ys cs : List Wire) (cin : Wire) : Program :=
  notRegister ys++program expected bits ys flags cs cin++notRegister ys

def flipped (ys : List Wire) (s : State) : State :=
  ⟨s.phase,fun q=>if q∈ys then !s.basis q else s.basis q⟩

theorem sub_eq (expected : Bool) (bits : List MappedBit) (flags : List Bool)
    (ys cs : List Wire) (cin : Wire) (hn : (cin::ys++cs).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::ys++cs)
    (hl : bits.length=ys.length) (hf : flags.length=ys.length) (hc : cs.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈cs,s.basis q=false)
    (ready : Ready expected bits flags ys ((flipped ys s).basis cin) (flipped ys s).basis) :
    run (mixedSub expected bits flags ys cs cin) m s=run (mappedSub bits ys cs cin) m s := by
  have yn : ys.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h
    omega
  have away (q : Wire) (hq : q∈cs) : q∉ys := by
    intro bad
    have h:=List.nodup_iff_count.mp hn q
    have a:=List.count_pos_iff.mpr hq
    have b:=List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h
    omega
  have clean : ∀q∈cs,(flipped ys s).basis q=false := by
    intro q hq
    simp only [flipped,show q∉ys from away q hq,if_false,hclean q hq]
  have nt (mm : List Bool) : run (notRegister ys) mm s=flipped ys s := notRegister_correct ys yn s mm
  have mid (mm : List Bool) := program_eq_mappedAdd expected bits flags ys cs cin
    hn ha hl hf hc (flipped ys s) mm clean ready
  have nc:=notRegister_counts ys
  have pc:=program_counts expected bits flags ys cs cin hl hf hc
  have mc:=mappedAdd_counts bits ys cs cin hl hc
  rw [mixedSub,mappedSub]
  simp only [List.append_assoc,run_append,run_take,nc.2,pc.2,mc.2,List.take_zero,List.drop_zero]
  rw [nt,mid]

theorem sub_counts (expected : Bool) (bits : List MappedBit) (flags : List Bool)
    (ys cs : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hf : flags.length=ys.length) (hc : cs.length+1=ys.length) :
    toffoliCount (mixedSub expected bits flags ys cs cin)=flags.tail.count false ∧
    measurementCount (mixedSub expected bits flags ys cs cin)=ys.length-1 := by
  have pc:=program_counts expected bits flags ys cs cin hl hf hc
  have nc:=notRegister_counts ys
  simp [mixedSub,toffoliCount_append,measurementCount_append,pc.1,pc.2,nc.1,nc.2]

theorem sub_physical (expected : Bool) (bits : List MappedBit) (flags : List Bool)
    (ys cs : List Wire) (cin : Wire) (hn : (cin::ys++cs).Nodup)
    (ha : ∀b∈bits,∀q∈b.wire,q∉cin::ys++cs)
    (hl : bits.length=ys.length) (hc : cs.length+1=ys.length) :
    GatePhysical (mixedSub expected bits flags ys cs cin) := by
  simp only [mixedSub,gatePhysical_append]
  exact ⟨⟨notRegister_physical ys,program_physical expected bits ys flags cs cin hn ha hl hc⟩,
    notRegister_physical ys⟩
#print axioms sub_eq
#print axioms sub_counts
#print axioms sub_physical
end ECDSAAdd.Entrant.MixedLiteralAdderDevelop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.MixedLiteralAdderDevelop
open Arithmetic

theorem complement_add_value (X Y N : Nat) (hN : 0<N) (hX : X<N) (hY : Y<N) :
    (X+(N-1-Y))%N=N-1-((Y+N-X)%N) := by
  by_cases less : X≤Y
  · rw [Nat.mod_eq_of_lt (show X+(N-1-Y)<N by omega),
      show Y+N-X=(Y-X)+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show X+(N-1-Y)=(X-1-Y)+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show X-1-Y<N by omega),Nat.mod_eq_of_lt (show Y+N-X<N by omega)]
    omega

theorem ready_sub_value (bits : List MappedBit) (flags : List Bool)
    (ys cs : List Wire) (cin : Wire) (hn : (cin::ys++cs).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::ys++cs)
    (hl : bits.length=ys.length) (hf : flags.length=ys.length)
    (s : State) (hcin : s.basis cin=false) (V : Nat)
    (hv : (regValue ys s.basis+2^ys.length-mappedValue bits s.basis)%2^ys.length=V)
    (hk : ∀i,i<flags.length → flags.getD i false=true → (2^ys.length-1-V).testBit i=true) :
    Ready true bits flags ys ((flipped ys s).basis cin) (flipped ys s).basis := by
  have cAway : cin∉ys:=fun h=>(List.nodup_cons.mp hn).1 (by simp [h])
  have ucin : (flipped ys s).basis cin=false := by simp [flipped,cAway,hcin]
  have src : mappedValue bits (flipped ys s).basis=mappedValue bits s.basis := by
    apply mappedValue_congr
    intro q hq
    have off : q∉ys:=fun h=>ha q hq (by simp [h])
    simp [flipped,off]
  have tar : regValue ys (flipped ys s).basis=2^ys.length-1-regValue ys s.basis := by
    rw [regValue_congr ys _ (fun q=>!s.basis q) (by intro q hq;simp [flipped,hq]),regValue_complement]
  have val : (mappedValue bits (flipped ys s).basis+regValue ys (flipped ys s).basis+
      ((flipped ys s).basis cin).toNat)%2^ys.length=2^ys.length-1-V := by
    rw [src,tar,ucin,Bool.toNat_false,Nat.add_zero,complement_add_value _ _ _ (Nat.two_pow_pos _)
      (by simpa only [hl] using mappedValue_lt bits s.basis) (regValue_lt ys s.basis),hv]
  apply ready_of_number true bits flags ys ((flipped ys s).basis cin) (flipped ys s).basis hl hf
  intro i hi hknown
  rw [val]
  exact hk i hi hknown

theorem read_add_eq (x y cs : List Wire) (cin : Wire) :
    mappedAdd (mappedRead x false) y cs cin=addInPlace x y cs cin := by
  induction x generalizing y cs cin with
  | nil => simp [mappedRead,mappedAdd,addInPlace]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases y with
      | nil => simp [mappedRead,mappedAdd,addInPlace]
      | cons b ys => cases ys <;> simp [mappedRead,mappedAdd,addInPlace,mappedSum]
    | cons a' xs =>
      cases y with
      | nil => simp [mappedRead,mappedAdd,addInPlace]
      | cons b ys =>
        cases ys with
        | nil => simp [mappedRead,mappedAdd,addInPlace]
        | cons b' ys =>
          cases cs with
          | nil => simp [mappedRead,mappedAdd,addInPlace]
          | cons c cs =>
            simpa [mappedRead,mappedAdd,addInPlace,mappedMajority,mappedEraseCarry,mappedSum]
              using congrArg (fun p=>majority a b cin c++p++eraseCarry a b cin c++[Instr.CX a b,Instr.CX cin b])
                (ih (b'::ys) cs c)

theorem read_sub_eq (x y cs : List Wire) (cin : Wire) :
    mappedSub (mappedRead x false) y cs cin=subInPlace x y cs cin := by
  rw [mappedSub,subInPlace,read_add_eq]

theorem read_geometry (x y cs : List Wire) (cin : Wire) (hn : (cin::x++y++cs).Nodup) :
    (cin::y++cs).Nodup ∧ (∀q∈x,q∉cin::y++cs) := by
  have cnt:=List.nodup_iff_count.mp hn
  constructor
  · apply List.nodup_iff_count.mpr
    intro q
    have h:=cnt q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  · intro q hx bad
    have h:=cnt q
    have a:=List.count_pos_iff.mpr hx
    have b:=List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h b
    omega

theorem read_sub_replace (x y cs : List Wire) (flags : List Bool) (cin : Wire)
    (hn : (cin::x++y++cs).Nodup) (hx : x.length=y.length) (hf : flags.length=y.length)
    (hc : cs.length+1=y.length) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hcin : s.basis cin=false) (V : Nat)
    (hv : (regValue y s.basis+2^y.length-regValue x s.basis)%2^y.length=V)
    (hk : ∀i,i<flags.length → flags.getD i false=true → (2^y.length-1-V).testBit i=true) :
    run (mixedSub true (mappedRead x false) flags y cs cin) m s=run (subInPlace x y cs cin) m s := by
  have g:=read_geometry x y cs cin hn
  have hl : (mappedRead x false).length=y.length := by simpa [mappedRead] using hx
  have ha : ∀q∈mappedWires (mappedRead x false),q∉cin::y++cs := by
    rw [mappedRead_wires]
    exact g.2
  have ready:=ready_sub_value (mappedRead x false) flags y cs cin g.1 ha hl hf s hcin V
    (by simpa only [mappedRead_value] using hv) hk
  have eq:=sub_eq true (mappedRead x false) flags y cs cin g.1 ha hl hf hc s m hclean ready
  rw [read_sub_eq] at eq
  exact eq
#print axioms ready_sub_value
#print axioms read_sub_eq
#print axioms read_sub_replace
end ECDSAAdd.Entrant.MixedLiteralAdderDevelop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.MixedLiteralAdderDevelop
open Arithmetic

theorem head_read_slots (expected flag : Bool) (a a' y y' cin c : Wire) :
    Challenge.gateSlots (head expected flag ⟨some a,false⟩ ⟨some a',false⟩ y y' cin c)≤6 := by
  cases flag <;> cases expected <;>
    simp [head,Arithmetic.KnownOutputAdder.prepare,Arithmetic.KnownOutputAdder.xorBit,literal,
      mappedMajority,majority,Challenge.gateSlots,Challenge.instructionSlots]

theorem read_slots_le (expected : Bool) (x y : List Wire) (flags : List Bool)
    (cs : List Wire) (cin : Wire) :
    Challenge.gateSlots (program expected (mappedRead x false) y flags cs cin)≤
      Challenge.gateSlots (addInPlace x y cs cin) := by
  induction x generalizing y flags cs cin with
  | nil => simp [mappedRead,program,addInPlace,Challenge.gateSlots]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases y with
      | nil => simp [mappedRead,program,addInPlace,Challenge.gateSlots]
      | cons b ys =>
        cases ys with
        | cons b' ys => simp [mappedRead,program,addInPlace,Challenge.gateSlots]
        | nil =>
          cases flags with
          | nil => simp [mappedRead,program,Challenge.gateSlots]
          | cons d ds => cases ds <;> simp [mappedRead,program,addInPlace,mappedSum,Challenge.gateSlots,Challenge.instructionSlots]
    | cons a' xs =>
      cases y with
      | nil => simp [mappedRead,program,addInPlace,Challenge.gateSlots]
      | cons b ys =>
        cases ys with
        | nil => simp [mappedRead,program,addInPlace,Challenge.gateSlots]
        | cons b' ys =>
          cases cs with
          | nil => simp [mappedRead,program,addInPlace,Challenge.gateSlots]
          | cons c cs =>
            cases flags with
            | nil => simp [mappedRead,program,Challenge.gateSlots]
            | cons d ds =>
              cases ds with
              | nil => simp [mappedRead,program,Challenge.gateSlots]
              | cons flag flags =>
                have hh:=head_read_slots expected flag a a' b b' cin c
                have ht:=ih (b'::ys) (flag::flags) cs c
                change Challenge.gateSlots (head expected flag ⟨some a,false⟩ ⟨some a',false⟩ b b' cin c++
                  program expected (mappedRead (a'::xs) false) (b'::ys) (flag::flags) cs c++
                  eraseCarry a b cin c++[Instr.CX a b,Instr.CX cin b])≤
                  Challenge.gateSlots (majority a b cin c++addInPlace (a'::xs) (b'::ys) cs c++
                    eraseCarry a b cin c++[Instr.CX a b,Instr.CX cin b])
                simp only [Challenge.gateSlots_append,Baselines.majority_gateSlots]
                omega

theorem read_sub_slots_le (expected : Bool) (x y cs : List Wire) (flags : List Bool) (cin : Wire) :
    Challenge.gateSlots (mixedSub expected (mappedRead x false) flags y cs cin)≤
      Challenge.gateSlots (subInPlace x y cs cin) := by
  have h:=read_slots_le expected x y flags cs cin
  simp only [mixedSub,subInPlace,Challenge.gateSlots_append]
  omega
#print axioms read_slots_le
#print axioms read_sub_slots_le
end ECDSAAdd.Entrant.MixedLiteralAdderDevelop
end

namespace ECDSAAdd.Entrant.WinArith
open ECDSAAdd ECDSAAdd.Arithmetic Instr

theorem regValue_take_mod (r : List Wire) (n : Nat) (hn : n ≤ r.length) (s : BasisState) :
    regValue (r.take n) s = regValue r s % 2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hn] at h
  have hl : regValue (r.take n) s < 2^n := by
    simpa only [List.length_take, Nat.min_eq_left hn] using regValue_lt (r.take n) s
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

theorem split3 (R : List Wire) (k n : Nat) (hk : k + n ≤ R.length) (s : BasisState) :
    regValue R s = regValue (R.take k) s +
      2^k * (regValue ((R.drop k).take n) s + 2^n * regValue (R.drop (k+n)) s) := by
  have h1 := regValue_append (R.take k) (R.drop k) s
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left (by omega)] at h1
  have h2 := regValue_append ((R.drop k).take n) ((R.drop k).drop n) s
  rw [List.take_append_drop, List.length_take, List.length_drop, Nat.min_eq_left (by omega),
    List.drop_drop] at h2
  rw [h1, h2]

theorem drop_div (r : List Wire) (n : Nat) (hn : n ≤ r.length) (s : BasisState) :
    regValue (r.drop n) s = regValue r s / 2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hn] at h
  have hl : regValue (r.take n) s < 2^n := by
    simpa only [List.length_take, Nat.min_eq_left hn] using regValue_lt (r.take n) s
  rw [h, Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt hl, Nat.zero_add]

theorem win_mid (R : List Wire) (k n : Nat) (hk : k + n ≤ R.length) (s : BasisState) :
    regValue ((R.drop k).take n) s = (regValue R s / 2^k) % 2^n := by
  rw [regValue_take_mod _ _ (by simp; omega), drop_div _ _ (by omega)]

/-- Wires of `R` outside the window `[k, k+n)`. -/
theorem win_away (R : List Wire) (hR : R.Nodup) (k n : Nat) (w : Wire)
    (hw : w ∈ R.take k ∨ w ∈ R.drop (k+n)) : w ∉ (R.drop k).take n := by
  intro hy
  have c := List.nodup_iff_count_le_one.mp hR w
  have e1 := R.take_append_drop k
  have e2 := (R.drop k).take_append_drop n
  rw [List.drop_drop] at e2
  have cnt : R.count w = (R.take k).count w + ((R.drop k).take n).count w + (R.drop (k+n)).count w := by
    conv_lhs => rw [← e1, ← e2]
    simp only [List.count_append]; omega
  have p1 := List.count_pos_iff.mpr hy
  rcases hw with hw|hw
  · have p2 := List.count_pos_iff.mpr hw; omega
  · have p2 := List.count_pos_iff.mpr hw; omega

theorem win_recombine (R : List Wire) (hR : R.Nodup) (k n : Nat) (hk : k + n ≤ R.length)
    (s t : BasisState) (hsame : ∀ w, w ∉ (R.drop k).take n → t w = s w) (Y' : Nat)
    (hy : regValue ((R.drop k).take n) t = Y') :
    regValue R t = regValue (R.take k) s + 2^k * (Y' + 2^n * regValue (R.drop (k+n)) s) := by
  rw [split3 R k n hk t, hy]
  have a : regValue (R.take k) t = regValue (R.take k) s :=
    regValue_congr _ _ _ (fun w hw => hsame w (win_away R hR k n w (Or.inl hw)))
  have b : regValue (R.drop (k+n)) t = regValue (R.drop (k+n)) s :=
    regValue_congr _ _ _ (fun w hw => hsame w (win_away R hR k n w (Or.inr hw)))
  rw [a, b]

/-- Add `x` into the window `[k, k+n)` of `R` when the window sum does not overflow. -/
theorem win_add (R x cs : List Wire) (cin : Wire) (k n : Nat) (hR : R.Nodup) (hk : k + n ≤ R.length)
    (hnd : (cin :: (x ++ (R.drop k).take n ++ cs)).Nodup) (hx : x.length = n) (hc : cs.length + 1 = n)
    (s : State) (m : List Bool) (hcin : s.basis cin = false) (hcs : ∀ q ∈ cs, s.basis q = false)
    (hfit : (regValue R s.basis / 2^k) % 2^n + regValue x s.basis < 2^n) :
    (run (addInPlace x ((R.drop k).take n) cs cin) m s).phase = s.phase ∧
    (∀ w, w ∉ (R.drop k).take n → (run (addInPlace x ((R.drop k).take n) cs cin) m s).basis w = s.basis w) ∧
    regValue R (run (addInPlace x ((R.drop k).take n) cs cin) m s).basis =
      regValue R s.basis + 2^k * regValue x s.basis := by
  have yl : ((R.drop k).take n).length = n := by simp; omega
  obtain ⟨hp, hsame, hsum⟩ := addInPlace_correct x ((R.drop k).take n) cs cin hnd (by rw [hx, yl])
    (by rw [hc, yl]) s m hcs
  refine ⟨hp, hsame, ?_⟩
  have Y := win_mid R k n hk s.basis
  rw [hcin, yl] at hsum
  simp only [Bool.toNat_false, Nat.add_zero] at hsum
  rw [Nat.mod_eq_of_lt (by rw [Y]; omega)] at hsum
  rw [win_recombine R hR k n hk s.basis _ hsame _ hsum]
  conv_rhs => rw [split3 R k n hk s.basis]
  ring

/-- Subtract `x` from the window `[k, k+n)` of `R` when the window does not underflow. -/
theorem win_sub (R x cs : List Wire) (cin : Wire) (k n : Nat) (hR : R.Nodup) (hk : k + n ≤ R.length)
    (hnd : (cin :: (x ++ (R.drop k).take n ++ cs)).Nodup) (hx : x.length = n) (hc : cs.length + 1 = n)
    (s : State) (m : List Bool) (hcin : s.basis cin = false) (hcs : ∀ q ∈ cs, s.basis q = false)
    (hfit : regValue x s.basis ≤ (regValue R s.basis / 2^k) % 2^n) :
    (run (subInPlace x ((R.drop k).take n) cs cin) m s).phase = s.phase ∧
    (∀ w, w ∉ (R.drop k).take n → (run (subInPlace x ((R.drop k).take n) cs cin) m s).basis w = s.basis w) ∧
    regValue R (run (subInPlace x ((R.drop k).take n) cs cin) m s).basis + 2^k * regValue x s.basis =
      regValue R s.basis := by
  have yl : ((R.drop k).take n).length = n := by simp; omega
  have hcs0 : regValue cs s.basis = 0 := (regValue_zero _ _).mpr hcs
  have sp := subInPlace_spec x ((R.drop k).take n) cs cin hnd (by rw [hx, yl]) (by rw [hc, yl])
    (regValue x s.basis) (regValue ((R.drop k).take n) s.basis) s m ⟨⟨⟨rfl, rfl⟩, hcin⟩, hcs0⟩
  have hsame : ∀ w, w ∉ (R.drop k).take n →
      (run (subInPlace x ((R.drop k).take n) cs cin) m s).basis w = s.basis w :=
    fun w hw => subInPlace_frame x ((R.drop k).take n) cs cin hnd (by rw [hx, yl]) (by rw [hc, yl])
      s m hcin hcs0 w hw
  refine ⟨sp.1, hsame, ?_⟩
  have hsum : regValue ((R.drop k).take n) (run (subInPlace x ((R.drop k).take n) cs cin) m s).basis =
      (regValue ((R.drop k).take n) s.basis + 2^n - regValue x s.basis) % 2^n := by
    have := sp.2.1.1.2; rwa [yl] at this
  have Y := win_mid R k n hk s.basis
  generalize hYv : regValue ((R.drop k).take n) s.basis = Yv at hsum Y
  generalize hXv : regValue x s.basis = Xv at hsum hfit ⊢
  have ylt : Yv < 2^n := by rw [Y]; exact Nat.mod_lt _ (by positivity)
  have le : Xv ≤ Yv := by rw [Y]; exact hfit
  rw [show Yv + 2 ^ n - Xv = (Yv - Xv) + 2^n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)] at hsum
  rw [win_recombine R hR k n hk s.basis _ hsame _ hsum]
  conv_rhs => rw [split3 R k n hk s.basis, hYv]
  obtain ⟨z, rfl⟩ : ∃ z, Yv = Xv + z := ⟨Yv - Xv, by omega⟩
  rw [show Xv + z - Xv = z by omega]
  ring

-- WINEND

/-! ## Transform steps on a register `R` with a scratch register `S` -/

def PS (R S : List Wire) (t : BasisState) (V D : Nat) (s : BasisState) : Prop :=
  regValue R s = V ∧ regValue S s = D ∧ ∀ q, q ∉ R → q ∉ S → s q = t q

theorem mem_win {R : List Wire} {k n : Nat} {w : Wire} (h : w ∈ (R.drop k).take n) : w ∈ R :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem tstep_add (R S x cs : List Wire) (cin : Wire) (k n : Nat) (t : BasisState) (V D X : Nat)
    (hR : R.Nodup) (hk : k + n ≤ R.length) (hnd : (cin :: (x ++ (R.drop k).take n ++ cs)).Nodup)
    (hx : x.length = n) (hc : cs.length + 1 = n) (hSR : ∀ q ∈ S, q ∉ R)
    (hcinR : cin ∉ R) (hcinS : cin ∉ S) (hcsR : ∀ q ∈ cs, q ∉ R) (hcsS : ∀ q ∈ cs, q ∉ S)
    (ht : t cin = false) (htc : ∀ q ∈ cs, t q = false)
    (hX : ∀ s, PS R S t V D s → regValue x s = X)
    (fit : (V / 2^k) % 2^n + X < 2^n) :
    Triple (PS R S t V D) (addInPlace x ((R.drop k).take n) cs cin) (PS R S t (V + 2^k*X) D) := by
  intro s m h
  have c0 : s.basis cin = false := (h.2.2 cin hcinR hcinS).trans ht
  have k0 : ∀ q ∈ cs, s.basis q = false := fun q hq => (h.2.2 q (hcsR q hq) (hcsS q hq)).trans (htc q hq)
  have xv := hX s.basis h
  obtain ⟨hp, hsame, hv⟩ := win_add R x cs cin k n hR hk hnd hx hc s m c0 k0 (by rw [h.1, xv]; exact fit)
  refine ⟨hp, ?_, ?_, ?_⟩
  · rw [hv, h.1, xv]
  · exact (regValue_congr _ _ _ (fun w hw => hsame w (fun hy => hSR w hw (mem_win hy)))).trans h.2.1
  · intro q h1 h2
    exact (hsame q (fun hy => h1 (mem_win hy))).trans (h.2.2 q h1 h2)

theorem tstep_sub (R S x cs : List Wire) (cin : Wire) (k n : Nat) (t : BasisState) (V D X : Nat)
    (hR : R.Nodup) (hk : k + n ≤ R.length) (hnd : (cin :: (x ++ (R.drop k).take n ++ cs)).Nodup)
    (hx : x.length = n) (hc : cs.length + 1 = n) (hSR : ∀ q ∈ S, q ∉ R)
    (hcinR : cin ∉ R) (hcinS : cin ∉ S) (hcsR : ∀ q ∈ cs, q ∉ R) (hcsS : ∀ q ∈ cs, q ∉ S)
    (ht : t cin = false) (htc : ∀ q ∈ cs, t q = false)
    (hX : ∀ s, PS R S t V D s → regValue x s = X)
    (fit : X ≤ (V / 2^k) % 2^n) :
    Triple (PS R S t V D) (subInPlace x ((R.drop k).take n) cs cin) (PS R S t (V - 2^k*X) D) := by
  intro s m h
  have c0 : s.basis cin = false := (h.2.2 cin hcinR hcinS).trans ht
  have k0 : ∀ q ∈ cs, s.basis q = false := fun q hq => (h.2.2 q (hcsR q hq) (hcsS q hq)).trans (htc q hq)
  have xv := hX s.basis h
  obtain ⟨hp, hsame, hv⟩ := win_sub R x cs cin k n hR hk hnd hx hc s m c0 k0 (by rw [h.1, xv]; exact fit)
  refine ⟨hp, ?_, ?_, ?_⟩
  · rw [h.1, xv] at hv; omega
  · exact (regValue_congr _ _ _ (fun w hw => hsame w (fun hy => hSR w hw (mem_win hy)))).trans h.2.1
  · intro q h1 h2
    exact (hsame q (fun hy => h1 (mem_win hy))).trans (h.2.2 q h1 h2)

theorem tcopy_in (R S : List Wire) (k : Nat) (t : BasisState) (V D : Nat)
    (hk : k + 10 ≤ R.length) (hS : S.length = 10) (hnd : ((R.drop k).take 10 ++ S).Nodup)
    (hSR : ∀ q ∈ S, q ∉ R) :
    Triple (PS R S t V D) (copyRegister none ((R.drop k).take 10) S)
      (PS R S t V (D ^^^ ((V / 2^k) % 2^10))) := by
  intro s m h
  have yl : ((R.drop k).take 10).length = S.length := by rw [hS]; simp; omega
  obtain ⟨hp, hsame, hv⟩ := copyRegister_correct none ((R.drop k).take 10) S yl hnd (by simp) s m
  refine ⟨hp, ?_, ?_, ?_⟩
  · exact (regValue_congr _ _ _ (fun w hw => hsame w (fun hs => hSR w hs hw))).trans h.1
  · rw [hv, h.2.1, show copyValue none s.basis (regValue ((R.drop k).take 10) s.basis) =
      regValue ((R.drop k).take 10) s.basis from rfl, win_mid R k 10 hk, h.1]
  · intro q h1 h2
    exact (hsame q h2).trans (h.2.2 q h1 h2)

theorem tcopy_out (R S : List Wire) (k : Nat) (t : BasisState) (V D : Nat) (hR : R.Nodup)
    (hk : k + 10 ≤ R.length) (hS : S.length = 10) (hnd : (S ++ (R.drop k).take 10).Nodup)
    (hSR : ∀ q ∈ S, q ∉ R) :
    Triple (PS R S t V D) (copyRegister none S ((R.drop k).take 10))
      (PS R S t (V % 2^k + 2^k * ((((V / 2^k) % 2^10) ^^^ D) + 2^10 * (V / 2^(k+10)))) D) := by
  intro s m h
  have yl : S.length = ((R.drop k).take 10).length := by rw [hS]; simp; omega
  obtain ⟨hp, hsame, hv⟩ := copyRegister_correct none S ((R.drop k).take 10) yl hnd
    (by simp) s m
  refine ⟨hp, ?_, ?_, ?_⟩
  · have hv' : regValue ((R.drop k).take 10) (run (copyRegister none S ((R.drop k).take 10)) m s).basis =
        ((V / 2^k) % 2^10) ^^^ D := by
      rw [hv, show copyValue none s.basis (regValue S s.basis) = regValue S s.basis from rfl, h.2.1,
        win_mid R k 10 hk, h.1]
    rw [win_recombine R hR k 10 hk s.basis _ hsame _ hv', regValue_take_mod _ _ (by omega),
      drop_div _ _ (by omega), h.1]
  · exact (regValue_congr _ _ _ (fun w hw => hsame w (fun hy => hSR w hw (mem_win hy)))).trans h.2.1
  · intro q h1 h2
    exact (hsame q (fun hy => h1 (mem_win hy))).trans (h.2.2 q h1 h2)

theorem PS_val {R S : List Wire} {t : BasisState} {a b D : Nat} (e : a = b) (s : BasisState)
    (h : PS R S t a D s) : PS R S t b D s := e ▸ h
theorem PS_dval {R S : List Wire} {t : BasisState} {a D E : Nat} (e : D = E) (s : BasisState)
    (h : PS R S t a D s) : PS R S t a E s := e ▸ h

/-- The geometry of the transform: `R` 43 bits, scratch `S` 10, zero pad `Z` 11, carries `cs` 42,
source `U` 32 bits, all distinct. -/
structure Geo (R S Z cs U : List Wire) (cin : Wire) : Prop where
  nd : (cin :: (U ++ R ++ S ++ Z ++ cs)).Nodup
  r : R.length = 43
  s : S.length = 10
  z : Z.length = 11
  c : cs.length = 42
  u : U.length = 32

theorem cT (l : List Wire) (n : Nat) (q : Wire) : (l.take n).count q ≤ l.count q :=
  (List.take_sublist n l).count_le q
theorem cW (l : List Wire) (k n : Nat) (q : Wire) : ((l.drop k).take n).count q ≤ l.count q :=
  ((List.take_sublist n _).trans (List.drop_sublist k l)).count_le q

/-- The lengths of the transform registers. -/
structure Lens (R S Z cs U : List Wire) : Prop where
  r : R.length = 43
  s : S.length = 10
  z : Z.length = 11
  c : cs.length = 42
  u : U.length = 32

theorem Geo.toLens {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) : Lens R S Z cs U :=
  ⟨g.r, g.s, g.z, g.c, g.u⟩

namespace Geo
variable {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
include g

theorem cnt (q : Wire) : (cin :: (U ++ R ++ S ++ Z ++ cs)).count q ≤ 1 :=
  List.nodup_iff_count_le_one.mp g.nd q


theorem rnd : R.Nodup := by
  apply List.nodup_iff_count_le_one.mpr; intro q; have := g.cnt q
  simp only [List.count_cons, List.count_append] at this; omega

theorem ndU (j k n i : Nat) : (cin :: ((U ++ Z.take j) ++ (R.drop k).take n ++ cs.take i)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr; intro q
  have h := g.cnt q; have a := cT Z j q; have b := cW R k n q; have c := cT cs i q
  simp only [List.count_cons, List.count_append] at h ⊢; omega

theorem ndS (j k n i : Nat) : (cin :: ((S ++ Z.take j) ++ (R.drop k).take n ++ cs.take i)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr; intro q
  have h := g.cnt q; have a := cT Z j q; have b := cW R k n q; have c := cT cs i q
  simp only [List.count_cons, List.count_append] at h ⊢; omega

theorem ndUZ (k n i : Nat) : (cin :: ((U ++ Z) ++ (R.drop k).take n ++ cs.take i)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr; intro q
  have h := g.cnt q; have b := cW R k n q; have c := cT cs i q
  simp only [List.count_cons, List.count_append] at h ⊢; omega

theorem ndIn (k : Nat) : ((R.drop k).take 10 ++ S).Nodup := by
  apply List.nodup_iff_count_le_one.mpr; intro q
  have h := g.cnt q; have b := cW R k 10 q
  simp only [List.count_cons, List.count_append] at h ⊢; omega

theorem ndOut (k : Nat) : (S ++ (R.drop k).take 10).Nodup := by
  apply List.nodup_iff_count_le_one.mpr; intro q
  have h := g.cnt q; have b := cW R k 10 q
  simp only [List.count_cons, List.count_append] at h ⊢; omega

theorem away (l1 l2 : List Wire) (q : Wire) (h1 : q ∈ l1) (h2 : q ∈ l2)
    (hc : l1.count q + l2.count q ≤ (cin :: (U ++ R ++ S ++ Z ++ cs)).count q) : False := by
  have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2; have := g.cnt q; omega

theorem SR : ∀ q ∈ S, q ∉ R := fun q h1 h2 => g.away S R q h1 h2 (by simp only [List.count_cons, List.count_append]; omega)
theorem cinR : cin ∉ R := fun h => g.away [cin] R cin (by simp) h (by simp only [List.count_cons, List.count_append, List.count_nil]; omega)
theorem cinS : cin ∉ S := fun h => g.away [cin] S cin (by simp) h (by simp only [List.count_cons, List.count_append, List.count_nil]; omega)
theorem csR (i : Nat) : ∀ q ∈ cs.take i, q ∉ R := fun q h1 h2 =>
  g.away cs R q (List.mem_of_mem_take h1) h2 (by simp only [List.count_cons, List.count_append]; omega)
theorem csS (i : Nat) : ∀ q ∈ cs.take i, q ∉ S := fun q h1 h2 =>
  g.away cs S q (List.mem_of_mem_take h1) h2 (by simp only [List.count_cons, List.count_append]; omega)
theorem UR : ∀ q ∈ U, q ∉ R := fun q h1 h2 => g.away U R q h1 h2 (by simp only [List.count_cons, List.count_append]; omega)
theorem US : ∀ q ∈ U, q ∉ S := fun q h1 h2 => g.away U S q h1 h2 (by simp only [List.count_cons, List.count_append]; omega)
theorem ZR : ∀ q ∈ Z, q ∉ R := fun q h1 h2 => g.away Z R q h1 h2 (by simp only [List.count_cons, List.count_append]; omega)
theorem ZS : ∀ q ∈ Z, q ∉ S := fun q h1 h2 => g.away Z S q h1 h2 (by simp only [List.count_cons, List.count_append]; omega)

end Geo

/-- Zero facts of the frame state `t`. -/
structure Clean (Z cs : List Wire) (cin : Wire) (t : BasisState) : Prop where
  cin : t cin = false
  z : ∀ q ∈ Z, t q = false
  c : ∀ q ∈ cs, t q = false

theorem valUZ {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u : Nat) (hu : regValue U t = u) (j : Nat) (V D : Nat) :
    ∀ s, PS R S t V D s → regValue (U ++ Z.take j) s = u := by
  intro s h
  rw [regValue_append, (regValue_congr U s t (fun q hq => h.2.2 q (g.UR q hq) (g.US q hq))).trans hu,
    (regValue_zero _ _).mpr (fun q hq => (h.2.2 q (g.ZR q (List.mem_of_mem_take hq))
      (g.ZS q (List.mem_of_mem_take hq))).trans (cl.z q (List.mem_of_mem_take hq)))]
  simp

theorem valUZf {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u : Nat) (hu : regValue U t = u) (V D : Nat) :
    ∀ s, PS R S t V D s → regValue (U ++ Z) s = u := by
  intro s h
  have := valUZ g cl u hu 11 V D s h
  rwa [List.take_of_length_le (by rw [g.z])] at this

theorem valSZ {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (j : Nat) (V D : Nat) :
    ∀ s, PS R S t V D s → regValue (S ++ Z.take j) s = D := by
  intro s h
  rw [regValue_append, h.2.1,
    (regValue_zero _ _).mpr (fun q hq => (h.2.2 q (g.ZR q (List.mem_of_mem_take hq))
      (g.ZS q (List.mem_of_mem_take hq))).trans (cl.z q (List.mem_of_mem_take hq)))]
  simp
theorem seqv {P Q Q' T : BasisState → Prop} {c d : Program} (hc : Triple P c Q) (hq : ∀ s, Q s → Q' s)
    (hd : Triple Q' d T) : Triple P (c ++ d) T :=
  (Triple.conseq (fun s h => h) hc hq).seq hd

end ECDSAAdd.Entrant.WinArith

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.WinArithSmallDevelop
open Arithmetic WinArith

def smallF (R S cs : List Wire) (cin : Wire) : Program := Win977Develop.forward (R.take 20) S cs cin
def smallI (R S cs : List Wire) (cin : Wire) : Program := Win977Develop.inverse (R.take 20) S cs cin

theorem smallF_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
    {t : BasisState} (cl : Clean Z cs cin t) (d : Nat) (hd : d≤976) :
    Triple (PS R S t d d) (smallF R S cs cin) (PS R S t (977*d) d) := by
  intro s m h
  have nd : (cin::(R.take 20++S++cs)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have old:=g.cnt q
    have c:=(List.take_sublist 20 R).count_le q
    simp only [List.count_cons,List.count_append] at old ⊢
    omega
  have count : (R.take 20).length=20 := by simp [g.r]
  have rLow : regValue (R.take 20) s.basis=d := by
    rw [WinArith.regValue_take_mod R 20 (by rw [g.r];decide),h.1,Nat.mod_eq_of_lt (by omega)]
  have clean : ∀q∈cs,s.basis q=false := by
    intro q hq
    have r: q∉R:=g.csR cs.length q (by simpa using hq)
    have so:q∉S:=g.csS cs.length q (by simpa using hq)
    exact (h.2.2 q r so).trans (cl.c q hq)
  have cin0 : s.basis cin=false := (h.2.2 cin g.cinR g.cinS).trans cl.cin
  have a:=Win977Develop.forward_run (R.take 20) S cs cin count g.s (by rw [g.c];decide)
    nd s m clean cin0 d (by omega) rLow h.2.1
  change (run (smallF R S cs cin) m s).phase=s.phase ∧
    regValue (R.take 20) (run (smallF R S cs cin) m s).basis=977*d ∧
    (∀q,q∉R.take 20 → (run (smallF R S cs cin) m s).basis q=s.basis q) at a
  have split : (R.take 20++R.drop 20).Nodup := by simpa using g.rnd
  have off (q : Wire) (hq:q∈R.drop 20) : q∉R.take 20 := by
    intro bad
    exact (List.nodup_append.mp split).2.2 q bad q hq rfl
  have high : regValue (R.drop 20) (run (smallF R S cs cin) m s).basis=0 := by
    rw [regValue_congr (R.drop 20) _ s.basis (fun q hq=>a.2.2 q (off q hq)),
      drop_div R 20 (by rw [g.r];decide),h.1,Nat.div_eq_of_lt (by omega)]
  have out:=regValue_append (R.take 20) (R.drop 20) (run (smallF R S cs cin) m s).basis
  rw [List.take_append_drop,a.2.1,high,Nat.mul_zero,Nat.add_zero] at out
  refine ⟨a.1,out,?_,?_⟩
  · exact (regValue_congr S _ s.basis (fun q hq=>a.2.2 q (fun hqR=>g.SR q hq (List.mem_of_mem_take hqR)))).trans h.2.1
  · intro q hq hs
    exact (a.2.2 q (fun hqR=>hq (List.mem_of_mem_take hqR))).trans (h.2.2 q hq hs)
theorem smallI_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
    {t : BasisState} (cl : Clean Z cs cin t) (d : Nat) (hd : d≤976) :
    Triple (PS R S t (977*d) d) (smallI R S cs cin) (PS R S t d d) := by
  intro s m h
  have nd : (cin::(R.take 20++S++cs)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have old:=g.cnt q
    have c:=(List.take_sublist 20 R).count_le q
    simp only [List.count_cons,List.count_append] at old ⊢
    omega
  have count : (R.take 20).length=20 := by simp [g.r]
  have rLow : regValue (R.take 20) s.basis=977*d := by
    rw [WinArith.regValue_take_mod R 20 (by rw [g.r];decide),h.1,Nat.mod_eq_of_lt (by omega)]
  have clean : ∀q∈cs,s.basis q=false := by
    intro q hq
    have r: q∉R:=g.csR cs.length q (by simpa using hq)
    have so:q∉S:=g.csS cs.length q (by simpa using hq)
    exact (h.2.2 q r so).trans (cl.c q hq)
  have cin0 : s.basis cin=false := (h.2.2 cin g.cinR g.cinS).trans cl.cin
  have a:=Win977Develop.inverse_run (R.take 20) S cs cin count g.s (by rw [g.c];decide)
    nd s m clean cin0 d (by omega) rLow h.2.1
  change (run (smallI R S cs cin) m s).phase=s.phase ∧
    regValue (R.take 20) (run (smallI R S cs cin) m s).basis=d ∧
    (∀q,q∉R.take 20 → (run (smallI R S cs cin) m s).basis q=s.basis q) at a
  have split : (R.take 20++R.drop 20).Nodup := by simpa using g.rnd
  have off (q : Wire) (hq:q∈R.drop 20) : q∉R.take 20 := by
    intro bad
    exact (List.nodup_append.mp split).2.2 q bad q hq rfl
  have high : regValue (R.drop 20) (run (smallI R S cs cin) m s).basis=0 := by
    rw [regValue_congr (R.drop 20) _ s.basis (fun q hq=>a.2.2 q (off q hq)),
      drop_div R 20 (by rw [g.r];decide),h.1,Nat.div_eq_of_lt (by omega)]
  have out:=regValue_append (R.take 20) (R.drop 20) (run (smallI R S cs cin) m s).basis
  rw [List.take_append_drop,a.2.1,high,Nat.mul_zero,Nat.add_zero] at out
  refine ⟨a.1,out,?_,?_⟩
  · exact (regValue_congr S _ s.basis (fun q hq=>a.2.2 q (fun hqR=>g.SR q hq (List.mem_of_mem_take hqR)))).trans h.2.1
  · intro q hq hs
    exact (a.2.2 q (fun hqR=>hq (List.mem_of_mem_take hqR))).trans (h.2.2 q hq hs)

theorem smallF_counts {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U) :
    toffoliCount (smallF R S cs cin)=29 ∧ measurementCount (smallF R S cs cin)=29 :=
  Win977Develop.forward_counts (R.take 20) S cs cin (by simp [g.r]) g.s (by rw [g.c];decide)

theorem smallI_counts {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U) :
    toffoliCount (smallI R S cs cin)=15 ∧ measurementCount (smallI R S cs cin)=29 :=
  Win977Develop.inverse_counts (R.take 20) S cs cin (by simp [g.r]) g.s (by rw [g.c];decide)

theorem small_nd {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) :
    (cin::(R.take 20++S++cs)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have old:=g.cnt q
  have c:=(List.take_sublist 20 R).count_le q
  simp only [List.count_cons,List.count_append] at old ⊢
  omega

theorem smallF_physical {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) :
    GatePhysical (smallF R S cs cin) :=
  Win977Develop.forward_physical (R.take 20) S cs cin (small_nd g)

theorem smallI_physical {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) :
    GatePhysical (smallI R S cs cin) :=
  Win977Develop.inverse_physical (R.take 20) S cs cin (by simp [g.r]) g.s (by rw [g.c];decide) (small_nd g)

theorem smallF_slots {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U) :
    Challenge.gateSlots (smallF R S cs cin)≤599 :=
  Win977Develop.forward_slots (R.take 20) S cs cin (by simp [g.r]) g.s

theorem smallI_slots {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U) :
    Challenge.gateSlots (smallI R S cs cin)≤492 :=
  Win977Develop.inverse_slots (R.take 20) S cs cin (by simp [g.r]) g.s

theorem enlarge_ports (R S cs : List Wire) (cin : Wire) :
    Win977Develop.ports (R.take 20) S cs cin⊆(R++S++cs++[cin]).toFinset := by
  intro q hq
  simp only [Win977Develop.ports,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,or_assoc] at hq ⊢
  rcases hq with h|h|h|h
  · exact Or.inl (List.mem_of_mem_take h)
  · tauto
  · tauto
  · tauto

theorem smallF_support (R S cs : List Wire) (cin : Wire) :
    wires (smallF R S cs cin)⊆(R++S++cs++[cin]).toFinset :=
  (Win977Develop.forward_support (R.take 20) S cs cin).trans (enlarge_ports R S cs cin)

theorem smallI_support (R S cs : List Wire) (cin : Wire) :
    wires (smallI R S cs cin)⊆(R++S++cs++[cin]).toFinset :=
  (Win977Develop.inverse_support (R.take 20) S cs cin).trans (enlarge_ports R S cs cin)
#print axioms smallF_spec
#print axioms smallI_spec
#print axioms smallF_counts
#print axioms smallI_counts
#print axioms smallF_physical
#print axioms smallI_physical
#print axioms smallF_support
#print axioms smallI_support
end ECDSAAdd.Entrant.WinArithSmallDevelop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KnownWindowSubDevelop
open Arithmetic WinArith MixedLiteralAdderDevelop

def sub33 (R Z cs U : List Wire) (cin : Wire) : Program :=
  mixedSub true (mappedRead (U++Z.take 1) false) upper33 ((R.drop 0).take 33) (cs.take 32) cin

def sub43 (R Z cs U : List Wire) (cin : Wire) : Program :=
  mixedSub true (mappedRead (U++Z) false) mask43 ((R.drop 0).take 43) (cs.take 42) cin

section Spec
variable {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
  (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t=u) (hu32 : u<2^32) (hd : d≤976)
include g cl hu hu32 hd

theorem sub33_spec : Triple (PS R S t (u+d) 0) (sub33 R Z cs U cin) (PS R S t d 0) := by
  have h33 : u+d<2^33 := by omega
  have normal:=tstep_sub R S (U++Z.take 1) (cs.take 32) cin 0 33 t (u+d) 0 u g.rnd
    (by simp [g.r]) (g.ndU 1 0 33 32) (by simp [g.u,g.z]) (by simp [g.c])
    g.SR g.cinR g.cinS (g.csR 32) (g.csS 32) cl.cin
    (fun q h=>cl.c q (List.mem_of_mem_take h)) (valUZ g cl u hu 1 _ _)
    (by norm_num;omega)
  intro s m h
  let x:=U++Z.take 1
  let y:=(R.drop 0).take 33
  have yl : y.length=33:=by simp [y,g.r]
  have xl : x.length=33:=by simp [x,g.u,g.z]
  have yv : regValue y s.basis=u+d := by
    rw [win_mid R 0 33 (by simp [g.r]),h.1]
    simpa using Nat.mod_eq_of_lt h33
  have xv : regValue x s.basis=u:=valUZ g cl u hu 1 _ _ s.basis h
  have cs0 : ∀q∈cs.take 32,s.basis q=false := by
    intro q hq
    exact (h.2.2 q (g.csR 32 q hq) (g.csS 32 q hq)).trans (cl.c q (List.mem_of_mem_take hq))
  have cin0 : s.basis cin=false := (h.2.2 cin g.cinR g.cinS).trans cl.cin
  have hv : (regValue y s.basis+2^y.length-regValue x s.basis)%2^y.length=d := by
    rw [yv,xv,yl]
    norm_num
    omega
  have known (i : Nat) (hi : i<upper33.length) (hk : upper33.getD i false=true) :
      (2^y.length-1-d).testBit i=true := by
    rw [yl]
    exact complement_upper33 d i (by omega) (by simpa [upper33] using hi) hk
  have eq : run (sub33 R Z cs U cin) m s=run (subInPlace x y (cs.take 32) cin) m s :=
    read_sub_replace x y (cs.take 32) upper33 cin (g.ndU 1 0 33 32)
      (by rw [xl,yl]) (by simp [upper33,yl]) (by simp [g.c,yl])
      s m cs0 cin0 d hv known
  rw [eq]
  have res:=normal s m h
  refine ⟨res.1,PS_val (show u+d-2^0*u=d by norm_num) _ res.2⟩

theorem sub43_spec : Triple (PS R S t (u+4294968273*d) 0) (sub43 R Z cs U cin) (PS R S t (4294968273*d) 0) := by
  have h43 : u+4294968273*d<2^43 := by omega
  have normal:=tstep_sub R S (U++Z) (cs.take 42) cin 0 43 t (u+4294968273*d) 0 u g.rnd
    (by simp [g.r]) (g.ndUZ 0 43 42) (by simp [g.u,g.z]) (by simp [g.c])
    g.SR g.cinR g.cinS (g.csR 42) (g.csS 42) cl.cin
    (fun q h=>cl.c q (List.mem_of_mem_take h)) (valUZf g cl u hu _ _)
    (by norm_num;omega)
  intro s m h
  let x:=U++Z
  let y:=(R.drop 0).take 43
  have yl : y.length=43:=by simp [y,g.r]
  have xl : x.length=43:=by simp [x,g.u,g.z]
  have yv : regValue y s.basis=u+4294968273*d := by
    rw [win_mid R 0 43 (by simp [g.r]),h.1]
    simpa using Nat.mod_eq_of_lt h43
  have xv : regValue x s.basis=u:=valUZf g cl u hu _ _ s.basis h
  have cs0 : ∀q∈cs.take 42,s.basis q=false := by
    intro q hq
    exact (h.2.2 q (g.csR 42 q hq) (g.csS 42 q hq)).trans (cl.c q (List.mem_of_mem_take hq))
  have cin0 : s.basis cin=false := (h.2.2 cin g.cinR g.cinS).trans cl.cin
  have hv : (regValue y s.basis+2^y.length-regValue x s.basis)%2^y.length=4294968273*d := by
    rw [yv,xv,yl]
    norm_num
    omega
  have known (i : Nat) (hi : i<mask43.length) (hk : mask43.getD i false=true) :
      (2^y.length-1-4294968273*d).testBit i=true := by
    rw [yl]
    exact complement_mask43 d i (by omega) (by simpa [mask43] using hi) hk
  have eq : run (sub43 R Z cs U cin) m s=run (subInPlace x y (cs.take 42) cin) m s :=
    read_sub_replace x y (cs.take 42) mask43 cin (g.ndUZ 0 43 42)
      (by rw [xl,yl]) (by simp [mask43,yl]) (by simp [g.c,yl])
      s m cs0 cin0 (4294968273*d) hv known
  rw [eq]
  have res:=normal s m h
  refine ⟨res.1,PS_val (show u+4294968273*d-2^0*u=4294968273*d by norm_num) _ res.2⟩

end Spec

theorem read_physical (expected : Bool) (x y cs : List Wire) (flags : List Bool) (cin : Wire)
    (hn : (cin::x++y++cs).Nodup) (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    GatePhysical (mixedSub expected (mappedRead x false) flags y cs cin) := by
  have g:=read_geometry x y cs cin hn
  apply MixedLiteralAdderDevelop.sub_physical expected (mappedRead x false) flags y cs cin g.1
  · intro b hb q hq
    have mem : q∈mappedWires (mappedRead x false):=List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
    rw [mappedRead_wires] at mem
    exact g.2 q mem
  · simpa [mappedRead] using hx
  · exact hc

theorem read_support (expected : Bool) (x y cs : List Wire) (flags : List Bool) (cin : Wire) :
    wires (mixedSub expected (mappedRead x false) flags y cs cin)⊆(x++y++cs++[cin]).toFinset := by
  have a:=MixedLiteralAdderDevelop.program_support expected (mappedRead x false) y flags cs cin
  rw [mappedRead_wires] at a
  intro q hq
  simp only [mixedSub,wires_append,Finset.mem_union,notRegister_wires] at hq
  rcases hq with (hq|hq)|hq
  · simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  · exact a hq
  · simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto

theorem sub33_counts {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U) :
    toffoliCount (sub33 R Z cs U cin)=9 ∧ measurementCount (sub33 R Z cs U cin)=32 := by
  have a:=MixedLiteralAdderDevelop.sub_counts true (mappedRead (U++Z.take 1) false) upper33
    ((R.drop 0).take 33) (cs.take 32) cin
    (by simp [mappedRead,g.u,g.z,g.r]) (by simp [upper33,g.r]) (by simp [g.c,g.r])
  simpa [sub33,g.r,upper33_count] using a

theorem sub43_counts {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U) :
    toffoliCount (sub43 R Z cs U cin)=29 ∧ measurementCount (sub43 R Z cs U cin)=42 := by
  have a:=MixedLiteralAdderDevelop.sub_counts true (mappedRead (U++Z) false) mask43
    ((R.drop 0).take 43) (cs.take 42) cin
    (by simp [mappedRead,g.u,g.z,g.r]) (by simp [mask43,g.r]) (by simp [g.c,g.r])
  simpa [sub43,g.r,mask43_count] using a

theorem sub33_physical {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) :
    GatePhysical (sub33 R Z cs U cin) :=
  read_physical true (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) upper33 cin
    (g.ndU 1 0 33 32) (by simp [g.u,g.z,g.r]) (by simp [g.c,g.r])

theorem sub43_physical {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) :
    GatePhysical (sub43 R Z cs U cin) :=
  read_physical true (U++Z) ((R.drop 0).take 43) (cs.take 42) mask43 cin
    (g.ndUZ 0 43 42) (by simp [g.u,g.z,g.r]) (by simp [g.c,g.r])

def ports (R Z cs U : List Wire) (cin : Wire) : Finset Wire := (U++Z++R++cs++[cin]).toFinset

theorem sub33_support (R Z cs U : List Wire) (cin : Wire) :
    wires (sub33 R Z cs U cin)⊆ports R Z cs U cin := by
  have a:=read_support true (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) upper33 cin
  intro q hq
  have mem:=a hq
  simp only [ports,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at mem ⊢
  rcases mem with h|h|h|h|h
  · tauto
  · have old:=List.mem_of_mem_take h
    tauto
  · have old:=WinArith.mem_win h
    tauto
  · have old:=List.mem_of_mem_take h
    tauto
  · tauto

theorem sub43_support (R Z cs U : List Wire) (cin : Wire) :
    wires (sub43 R Z cs U cin)⊆ports R Z cs U cin := by
  have a:=read_support true (U++Z) ((R.drop 0).take 43) (cs.take 42) mask43 cin
  intro q hq
  have mem:=a hq
  simp only [ports,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at mem ⊢
  rcases mem with h|h|h|h|h
  · tauto
  · tauto
  · have old:=WinArith.mem_win h
    tauto
  · have old:=List.mem_of_mem_take h
    tauto
  · tauto

theorem sub33_slots {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U) :
    Challenge.gateSlots (sub33 R Z cs U cin)≤462 := by
  have a:=read_sub_slots_le true (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) upper33 cin
  have b:=Baselines.subInPlace_gateSlots_le (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin
  exact a.trans (by simpa [g.u,g.z,g.r] using b)

theorem sub43_slots {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U) :
    Challenge.gateSlots (sub43 R Z cs U cin)≤602 := by
  have a:=read_sub_slots_le true (U++Z) ((R.drop 0).take 43) (cs.take 42) mask43 cin
  have b:=Baselines.subInPlace_gateSlots_le (U++Z) ((R.drop 0).take 43) (cs.take 42) cin
  exact a.trans (by simpa [g.u,g.z,g.r] using b)
#print axioms sub33_spec
#print axioms sub43_spec
#print axioms sub33_counts
#print axioms sub43_counts
#print axioms sub33_physical
#print axioms sub43_physical
#print axioms sub33_support
#print axioms sub43_support
end ECDSAAdd.Entrant.KnownWindowSubDevelop
end

namespace ECDSAAdd.Entrant.WinArith
open ECDSAAdd ECDSAAdd.Arithmetic Instr

/-- `R : u + d ↦ u + c*d` for `d ≤ 976`, `c = 2^32 + 977`, with scratch `S`. -/
def tFwd (R S Z cs U : List Wire) (cin : Wire) : Program :=
  KnownWindowSubDevelop.sub33 R Z cs U cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  (WinArithSmallDevelop.smallF R S cs cin ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (copyRegister none ((R.drop 32).take 10) S ++
  addInPlace (U ++ Z.take 10) ((R.drop 0).take 42) (cs.take 41) cin))))
def tInv (R S Z cs U : List Wire) (cin : Wire) : Program :=
  KnownWindowSubDevelop.sub43 R Z cs U cin ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (WinArithSmallDevelop.smallI R S cs cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  addInPlace (U ++ Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin))))


theorem fitA (V k n X : Nat) (h : V / 2^k + X < 2^n) : (V / 2^k) % 2^n + X < 2^n :=
  lt_of_le_of_lt (Nat.add_le_add_right (Nat.mod_le _ _) _) h
theorem fitS (V k n X : Nat) (h1 : V / 2^k < 2^n) (h2 : X ≤ V / 2^k) : X ≤ (V / 2^k) % 2^n := by
  rw [Nat.mod_eq_of_lt h1]; exact h2

section Spec
variable {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
  (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
include g cl hu hu32 hd
set_option linter.unusedSectionVars false

theorem addS (j k n i V : Nat) (hj : 10 + j = n) (hi : i + 1 = n) (hk : k + n ≤ 43) (hjz : j ≤ 11) (hi42 : i ≤ 42)
    (fit : (V / 2^k) % 2^n + d < 2^n) :
    Triple (PS R S t V d) (addInPlace (S ++ Z.take j) ((R.drop k).take n) (cs.take i) cin)
      (PS R S t (V + 2^k*d) d) :=
  tstep_add R S (S ++ Z.take j) (cs.take i) cin k n t V d d g.rnd (by rw [g.r]; omega) (g.ndS j k n i)
    (by simp [g.s, g.z]; omega) (by simp [g.c]; omega) g.SR g.cinR g.cinS (g.csR i) (g.csS i) cl.cin
    (fun q h => cl.c q (List.mem_of_mem_take h)) (valSZ g cl j V d) fit

theorem subS (j k n i V : Nat) (hj : 10 + j = n) (hi : i + 1 = n) (hk : k + n ≤ 43) (hjz : j ≤ 11) (hi42 : i ≤ 42)
    (fit : d ≤ (V / 2^k) % 2^n) :
    Triple (PS R S t V d) (subInPlace (S ++ Z.take j) ((R.drop k).take n) (cs.take i) cin)
      (PS R S t (V - 2^k*d) d) :=
  tstep_sub R S (S ++ Z.take j) (cs.take i) cin k n t V d d g.rnd (by rw [g.r]; omega) (g.ndS j k n i)
    (by simp [g.s, g.z]; omega) (by simp [g.c]; omega) g.SR g.cinR g.cinS (g.csR i) (g.csS i) cl.cin
    (fun q h => cl.c q (List.mem_of_mem_take h)) (valSZ g cl j V d) fit
theorem tFwd_spec (h35 : u + d < 2^35) :
    Triple (PS R S t (u+d) 0) (tFwd R S Z cs U cin) (PS R S t (u + 4294968273*d) 0) := by
  have s1 := KnownWindowSubDevelop.sub33_spec g cl u d hu hu32 hd
  have s2 := tcopy_in R S 0 t d 0 (by rw [g.r]; omega) g.s (g.ndIn 0) g.SR
  have s3 := WinArithSmallDevelop.smallF_spec g cl d hd
  have s4 := tcopy_out R S 32 t (977*d) d g.rnd (by rw [g.r]; omega) g.s (g.ndOut 32) g.SR
  have s5 := tcopy_in R S 32 t (977*d + 2^32*d) d (by rw [g.r]; omega) g.s (g.ndIn 32) g.SR
  have s6 := tstep_add R S (U ++ Z.take 10) (cs.take 41) cin 0 42 t (977*d + 2^32*d) 0 u g.rnd (by rw [g.r];omega)
    (g.ndU 10 0 42 41) (by simp [g.u,g.z]) (by simp [g.c]) g.SR g.cinR g.cinS (g.csR 41) (g.csS 41) cl.cin
    (fun q h=>cl.c q (List.mem_of_mem_take h)) (valUZ g cl u hu 10 _ _) (fitA _ _ _ _ (by norm_num <;> omega))
  have a4 : 977*d % 2^32 + 2^32*((((977*d) / 2^32) % 2^10 ^^^ d) + 2^10*(977*d / 2^(32+10))) =
      977*d + 2^32*d := by
    have a : 977*d % 2^32 = 977*d := Nat.mod_eq_of_lt (by omega)
    have b : (977*d / 2^32) % 2^10 = 0 := by rw [Nat.div_eq_of_lt (by omega), Nat.zero_mod]
    have c : 977*d / 2^(32+10) = 0 := Nat.div_eq_of_lt (by norm_num <;> omega)
    rw [a, b, c, Nat.zero_xor]; ring
  have a5 : d ^^^ (((977*d + 2^32*d) / 2^32) % 2^10) = 0 := by
    have a : ((977*d + 2^32*d) / 2^32) % 2^10 = d := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), Nat.zero_add,
        Nat.mod_eq_of_lt (by omega)]
    rw [a, Nat.xor_self]
  have a2 : 0 ^^^ ((d / 2^0) % 2^10) = d := by
    rw [Nat.zero_xor]; norm_num; omega
  unfold tFwd
  exact seqv s1 (PS_val (by omega)) (seqv s2 (PS_dval a2)
    (seqv s3 (fun _ h => h) (seqv s4 (PS_val a4) (seqv s5 (PS_dval a5)
    (Triple.conseq (fun s h => h) s6 (PS_val (by omega)))))))

theorem tInv_spec (h35 : u + d < 2^35) :
    Triple (PS R S t (u + 4294968273*d) 0) (tInv R S Z cs U cin) (PS R S t (u+d) 0) := by
  have s1 := KnownWindowSubDevelop.sub43_spec g cl u d hu hu32 hd
  have s2 := tcopy_in R S 32 t (977*d + 2^32*d) 0 (by rw [g.r]; omega) g.s (g.ndIn 32) g.SR
  have s3 := tcopy_out R S 32 t (977*d + 2^32*d) d g.rnd (by rw [g.r]; omega) g.s (g.ndOut 32) g.SR
  have s4 := WinArithSmallDevelop.smallI_spec g cl d hd
  have s5 := tcopy_in R S 0 t d d (by rw [g.r]; omega) g.s (g.ndIn 0) g.SR
  have s6 := tstep_add R S (U ++ Z.take 1) (cs.take 32) cin 0 33 t d 0 u g.rnd (by rw [g.r];omega)
    (g.ndU 1 0 33 32) (by simp [g.u,g.z]) (by simp [g.c]) g.SR g.cinR g.cinS (g.csR 32) (g.csS 32) cl.cin
    (fun q h=>cl.c q (List.mem_of_mem_take h)) (valUZ g cl u hu 1 _ _) (by norm_num at h35 ⊢; omega)
  have a : ((977*d + 2^32*d) / 2^32) % 2^10 = d := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), Nat.zero_add,
      Nat.mod_eq_of_lt (by omega)]
  have a2 : 0 ^^^ (((977*d + 2^32*d) / 2^32) % 2^10) = d := by rw [a, Nat.zero_xor]
  have a3 : (977*d + 2^32*d) % 2^32 + 2^32*((((977*d + 2^32*d) / 2^32) % 2^10 ^^^ d) +
      2^10*((977*d + 2^32*d) / 2^(32+10))) = 977*d := by
    have b : (977*d + 2^32*d) % 2^32 = 977*d := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have c : (977*d + 2^32*d) / 2^(32+10) = 0 := Nat.div_eq_of_lt (by norm_num <;> omega)
    rw [a, b, c, Nat.xor_self]; ring
  have a5 : d ^^^ ((d / 2^0) % 2^10) = 0 := by
    rw [show (d / 2^0) % 2^10 = d by norm_num; omega, Nat.xor_self]
  unfold tInv
  exact seqv s1 (PS_val (by omega)) (seqv s2 (PS_dval a2) (seqv s3 (PS_val a3)
    (seqv s4 (fun _ h => h) (seqv s5 (PS_dval a5)
    (Triple.conseq (fun s h => h) s6 (PS_val (by omega)))))))

end Spec

end ECDSAAdd.Entrant.WinArith

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-! ## The transform registers of the B fold -/

/-- `whi` and its transform: work bits 128..170. -/
def mR (L : CuccaroStreamedSquareWideLayout) : List Wire := (L.core.work.drop 128).take 43
/-- Scratch copy of `d`: fold-pad bits 50..59. -/
def mS (L : CuccaroStreamedSquareWideLayout) : List Wire := (L.foldPad.drop 50).take 10
/-- Zero padding of the transform sources: fold-pad bits 60..70. -/
def mZ (L : CuccaroStreamedSquareWideLayout) : List Wire := (L.foldPad.drop 60).take 11
/-- Carries of the transform adders: fold-pad bits 0..41. -/
def mC (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.take 42
/-- `u = b1 / 2^96`: the top 32 bits of `hiReg`. -/
def mU (L : CuccaroStreamedSquareWideLayout) : List Wire := (hiReg L).drop 96

def wFwd (L : CuccaroStreamedSquareWideLayout) : Program :=
  WinArith.tFwd (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin
def wInv (L : CuccaroStreamedSquareWideLayout) : Program :=
  WinArith.tInv (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin

theorem singles_cin (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    [L.core.cin].count q ≤ [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
      L.core.modFlag,L.core.sumCarry].count q :=
  (List.singleton_sublist.mpr (by simp)).count_le q

theorem pad_pieces (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (mC L).count q + (mS L).count q + (mZ L).count q ≤ L.foldPad.count q := by
  have f1 := congrArg (List.count q) (List.take_append_drop 50 L.foldPad)
  have f2 := congrArg (List.count q) (List.take_append_drop 10 (L.foldPad.drop 50))
  have e60 : (L.foldPad.drop 50).drop 10 = L.foldPad.drop 60 := by rw [List.drop_drop]
  rw [e60] at f2
  have hC : (mC L).count q ≤ (L.foldPad.take 50).count q := by
    have : L.foldPad.take 42 = (L.foldPad.take 50).take 42 := by rw [List.take_take]; rfl
    rw [mC, this]; exact (List.take_sublist _ _).count_le q
  have hZ : (mZ L).count q ≤ (L.foldPad.drop 60).count q := (List.take_sublist _ _).count_le q
  simp only [List.count_append] at f1 f2
  simp only [mS]
  omega

theorem mGeo (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    WinArith.Geo (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin := by
  have fp : L.foldPad.length = 254 := by simp [foldPad, hw.core.pad, hw.overflowPad]
  refine ⟨?_, by simp [mR, hw.core.work], by simp [mS, fp], by simp [mZ, fp], by simp [mC, fp],
    by simp [mU, hiReg_length L hw]⟩
  apply List.nodup_iff_count_le_one.mpr; intro q
  have lc := layoutCount L hn q
  have ps := productSplit L q
  have hU : (mU L).count q ≤ (hiReg L).count q := (List.drop_sublist _ _).count_le q
  have hR : (mR L).count q ≤ L.core.work.count q := WinArith.cW _ _ _ q
  have pp := pad_pieces L q
  have sc := singles_cin L q
  rw [show L.core.cin :: (mU L ++ mR L ++ mS L ++ mZ L ++ mC L) =
    [L.core.cin] ++ (mU L ++ mR L ++ mS L ++ mZ L ++ mC L) from rfl]
  simp only [List.count_append] at lc ⊢
  omega

theorem mLens (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    WinArith.Lens (mR L) (mS L) (mZ L) (mC L) (mU L) := by
  have fp : L.foldPad.length = 254 := by simp [foldPad, hw.core.pad, hw.overflowPad]
  exact ⟨by simp [mR, hw.core.work], by simp [mS, fp], by simp [mZ, fp], by simp [mC, fp],
    by simp [mU, hiReg_length L hw]⟩

theorem mR_work (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q ∈ mR L) : q ∈ L.core.work :=
  WinArith.mem_win h
theorem mS_pad (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q ∈ mS L) : q ∈ L.foldPad :=
  WinArith.mem_win h
theorem mZ_pad (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q ∈ mZ L) : q ∈ L.foldPad :=
  WinArith.mem_win h
theorem mC_pad (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q ∈ mC L) : q ∈ L.foldPad :=
  List.mem_of_mem_take h

/-- Registers of the B-body state that the transform registers avoid. -/
theorem m_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (h : q ∈ mR L ∨ q ∈ mS L) : q ∉ L.core.out ∧ q ∉ eReg L := by
  have lc := layoutCount L hn q
  have ps := productSplit L q
  have ec := eReg_count L q
  have pos : 0 < L.core.work.count q ∨ 0 < L.foldPad.count q := by
    rcases h with h|h
    · exact Or.inl (List.count_pos_iff.mpr (mR_work L q h))
    · exact Or.inr (List.count_pos_iff.mpr (mS_pad L q h))
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have a := List.count_pos_iff.mpr h1; omega
  · have a := List.count_pos_iff.mpr h1; omega

/-- The value of the transform register in the B-body state. -/
theorem mR_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E W : Nat) (s : BasisState) (h : BState L base O E W s) :
    regValue (mR L) s = (W / 2^128) % 2^43 ∧ regValue L.core.work s = W := by
  obtain ⟨_,_,_,_,workZ⟩ := zero_regs L hn base hc O E W s h
  have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) s
  rw [List.take_append_drop] at sp
  have hi : regValue (L.core.work.drop 163) s = 0 := (regValue_zero _ _).mpr workZ
  have wv : regValue L.core.work s = W := by
    rw [sp, hi]; simpa [accReg] using h.2.2.1
  refine ⟨?_, wv⟩
  rw [mR, WinArith.win_mid _ 128 43 (by simp [hw.core.work]) s, wv]

theorem hi96 (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (s : BasisState) :
    regValue (mU L) s = regValue (hiReg L) s / 2^96 :=
  WinArith.drop_div _ _ (by rw [hiReg_length L hw]; omega) s

end ECDSAAdd.Entrant.ControlLoan1589BFFold

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem lay_pos (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) :
    L.core.y.count q+L.core.out.count q+L.core.product.count q+L.foldPad.count q+L.core.work.count q+
      [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag,
        L.core.sumCarry].count q≤1 := layoutCount L hn q

theorem work_out (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) (h : q ∈ L.core.work) :
    q ∉ L.core.out := fun h1 => by
  have := lay_pos L hn q; have a := List.count_pos_iff.mpr h; have b := List.count_pos_iff.mpr h1; omega
theorem work_pad (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) (h : q ∈ L.core.work) :
    q ∉ L.foldPad := fun h1 => by
  have := lay_pos L hn q; have a := List.count_pos_iff.mpr h; have b := List.count_pos_iff.mpr h1; omega
theorem pad_out (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) (h : q ∈ L.foldPad) :
    q ∉ L.core.out := fun h1 => by
  have := lay_pos L hn q; have a := List.count_pos_iff.mpr h; have b := List.count_pos_iff.mpr h1; omega
theorem sing_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (h : q ∈ [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag,
        L.core.sumCarry]) : q ∉ L.core.work ∧ q ∉ L.foldPad ∧ q ∉ L.core.out := by
  have := lay_pos L hn q; have a := List.count_pos_iff.mpr h
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩ <;> (have b := List.count_pos_iff.mpr h1; omega)

theorem whi_split (b1 : Nat) (hb1 : b1 < 2^128) :
    b1/2^96 ≤ 4294968272*b1/2^128 ∧ 4294968272*b1/2^128 - b1/2^96 ≤ 976 ∧ 4294968272*b1/2^128 < 2^35 := by
  norm_num at hb1 ⊢; omega

theorem wMid_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E b1 : Nat) (hb1 : regValue (hiReg L) base = b1)
    (hb1lt : b1 < 2^128) (hO : O < SquareReduction.p) :
    Triple (BState L base O E (4294968272*b1)) (wFwd L ++ (wCoreTq L ++ wInv L))
      (BState L base (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) +
        2^128*((4294968272*b1)%2^128) + (SquareReduction.p-1-O)) % SquareReduction.p) E (4294968272*b1)) := by
  intro s m h
  obtain ⟨ws1, ws2, ws3⟩ := whi_split b1 hb1lt
  generalize hW : 4294968272*b1 = W at h ws1 ws2 ws3 ⊢
  generalize hu : b1/2^96 = u at ws1 ws2 ⊢
  generalize hd : W/2^128 - u = d at ws2 ⊢
  have hWlt : W < 2^163 := by rw [← hW]; norm_num at hb1lt ⊢; omega
  obtain ⟨hz, hb, hi, padZ, workZ⟩ := zero_regs L hn base hc O E W s.basis h
  have g := mGeo L hw hn
  have hRv := mR_value L hw hn base hc O E W s.basis h
  have Rv : regValue (mR L) s.basis = u + d := by rw [hRv.1, Nat.mod_eq_of_lt (by omega)]; omega
  have Sv : regValue (mS L) s.basis = 0 := (regValue_zero _ _).mpr (fun q hq => padZ q (mS_pad L q hq))
  have P0 : WinArith.PS (mR L) (mS L) s.basis (u+d) 0 s.basis := ⟨Rv, Sv, fun _ _ _ => rfl⟩
  have cl : WinArith.Clean (mZ L) (mC L) L.core.cin s.basis :=
    ⟨hi, fun q hq => padZ q (mZ_pad L q hq), fun q hq => padZ q (mC_pad L q hq)⟩
  have hU : regValue (mU L) s.basis = u := by
    rw [hi96 L hw, regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E W s.basis h q (Or.inl hq)), hb1, hu]
  have hu32 : u < 2^32 := by rw [← hu]; norm_num at hb1lt ⊢; omega
  have T1 : Triple (WinArith.PS (mR L) (mS L) s.basis (u+d) 0) (wFwd L)
      (WinArith.PS (mR L) (mS L) s.basis (u + 4294968273*d) 0) :=
    WinArith.tFwd_spec g cl u d hU hu32 ws2 (by omega)
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hX : (u + 4294968273*d) + 2^128*(W%2^128) < SquareReduction.p := by
    have b := Nat.mod_lt W (show 2^128>0 by positivity)
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at b hu32 ws2 ⊢
    omega
  -- frame facts of the start state
  have wnd : L.core.work.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have := lay_pos L hn q; omega
  have keepS (q : Wire) (h1 : q ∉ L.core.out) (h2 : q ∉ eReg L) (h3 : q ∉ accReg L) : s.basis q = base q :=
    h.2.2.2 q h1 h2 h3
  let O' := ((u + 4294968273*d) + 2^128*(W%2^128) + (SquareReduction.p-1-O)) % SquareReduction.p
  let Q2 : BasisState → Prop := fun x => regValue L.core.out x = O' ∧ regValue (mR L) x = u + 4294968273*d ∧
    regValue (mS L) x = 0 ∧ ∀ q, q ∉ L.core.out → q ∉ mR L → q ∉ mS L → x q = s.basis q
  have T2 : Triple (WinArith.PS (mR L) (mS L) s.basis (u + 4294968273*d) 0) (wCoreTq L) Q2 := by
    intro s1 m1 h1
    have keep (q : Wire) (a : q ∉ mR L) (b : q ∉ mS L) : s1.basis q = s.basis q := h1.2.2 q a b
    have outv : regValue L.core.out s1.basis = O :=
      (regValue_congr _ _ _ (fun q hq => keep q (fun hr => (m_away L hn q (Or.inl hr)).1 hq)
        (fun hs => (m_away L hn q (Or.inr hs)).1 hq))).trans h.1
    have sg (q : Wire) (hq : q ∈ [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
        L.core.modFlag,L.core.sumCarry]) : s1.basis q = s.basis q :=
      keep q (fun hr => (sing_away L hn q hq).1 (mR_work L q hr)) (fun hs => (sing_away L hn q hq).2.1 (mS_pad L q hs))
    have bo (q : Wire) (hq : q = L.core.productHigh ∨ q = L.core.outHigh ∨ q = L.core.workHigh ∨ q = L.core.cin ∨
        q = L.core.modFlag) : s.basis q = base q :=
      bstate_other L hn base O E W s.basis h q (Or.inr (Or.inr (Or.inr (by rcases hq with rfl|rfl|rfl|rfl|rfl <;> simp))))
    have padS (q : Wire) (hq : q ∈ L.foldPad) : s1.basis q = false := by
      by_cases hs : q ∈ mS L
      · exact (regValue_zero _ _).mp h1.2.1 q hs
      · exact (keep q (fun hr => work_pad L hn q (mR_work L q hr) hq) hs).trans (padZ q hq)
    have carryZ : ∀q∈(rotWCore L).carry,s1.basis q=false := by
      intro q hq
      simp only [rotWCore,measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq|rfl|rfl
      · exact padS q hq
      · exact ((sg _ (by simp)).trans (bo _ (Or.inl rfl))).trans hc.productHigh
      · exact ((sg _ (by simp)).trans (bo _ (Or.inr (Or.inr (Or.inl rfl))))).trans hc.workHigh
    have srcv : regValue (rotWCore L).src s1.basis = (u + 4294968273*d) + 2^128*(W%2^128) := by
      show regValue (rotWork L) s1.basis = _
      rw [rotWork, regValue_append]
      have l128 : (L.core.work.drop 128).length = 128 := by simp [hw.core.work]
      have hlo : regValue (L.core.work.take 128) s1.basis = W % 2^128 := by
        rw [regValue_congr _ _ (s.basis) (fun q hq => keep q
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
          WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
      have hhi : regValue (L.core.work.drop 128) s1.basis = u + 4294968273*d := by
        have sp := regValue_append ((L.core.work.drop 128).take 43) ((L.core.work.drop 128).drop 43) s1.basis
        rw [List.take_append_drop] at sp
        have z : regValue ((L.core.work.drop 128).drop 43) s1.basis = 0 := by
          apply (regValue_zero _ _).mpr
          intro q hq
          rw [List.drop_drop] at hq
          have hq' : q ∈ L.core.work.drop (128+43) := hq
          rw [keep q (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq') hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_drop hq') (mS_pad L q hs))]
          apply workZ
          have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
          rw [this] at hq'
          exact List.mem_of_mem_drop hq'
        rw [sp, z]; simpa [mR] using h1.1
      rw [hhi, hlo, l128]
    have ek := QCore.qprog_correctTq (rotWCore L) 256 SquareReduction.c SquareReduction.p (rotWCore_widths L hw)
      (rotWCore_nodup L hn) (by decide) hp (by norm_num [SquareReduction.c]) _ O hX hO s1 m1 srcv outv
      (show s1.basis L.core.outHigh = false from
        (sg L.core.outHigh (by simp)).trans ((bo _ (Or.inr (Or.inl rfl))).trans hc.outHigh))
      (show s1.basis L.core.modFlag = false from
        (sg L.core.modFlag (by simp)).trans ((bo _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans hc.modFlag)) carryZ
      (show s1.basis L.core.cin = false from (sg L.core.cin (by simp)).trans hi)
    refine ⟨ek.1, ek.2.1, ?_, ?_, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => ek.2.2 q (m_away L hn q (Or.inl hq)).1)).trans h1.1
    · exact (regValue_congr _ _ _ (fun q hq => ek.2.2 q (m_away L hn q (Or.inr hq)).1)).trans h1.2.1
    · intro q a b c; exact (ek.2.2 q a).trans (keep q b c)
  let Q3 : BasisState → Prop := fun x => regValue L.core.out x = O' ∧ regValue (mR L) x = u + d ∧
    regValue (mS L) x = 0 ∧ ∀ q, q ∉ L.core.out → q ∉ mR L → q ∉ mS L → x q = s.basis q
  have T3 : Triple Q2 (wInv L) Q3 := by
    intro s2 m2 h2
    have k2 (q : Wire) (a : q ∉ L.core.out) (b : q ∉ mR L) (c : q ∉ mS L) : s2.basis q = s.basis q := h2.2.2.2 q a b c
    have cl2 : WinArith.Clean (mZ L) (mC L) L.core.cin s2.basis := by
      refine ⟨?_, fun q hq => ?_, fun q hq => ?_⟩
      · exact (k2 _ (sing_away L hn _ (by simp)).2.2 (fun hr => (sing_away L hn _ (by simp)).1 (mR_work L _ hr))
          (fun hs => (sing_away L hn _ (by simp)).2.1 (mS_pad L _ hs))).trans hi
      · exact (k2 q (pad_out L hn q (mZ_pad L q hq)) (fun hr => work_pad L hn q (mR_work L q hr) (mZ_pad L q hq))
          (fun hs => g.ZS q hq hs)).trans (padZ q (mZ_pad L q hq))
      · exact (k2 q (pad_out L hn q (mC_pad L q hq)) (fun hr => work_pad L hn q (mR_work L q hr) (mC_pad L q hq))
          (fun hs => (g.csS 42) q (by rwa [List.take_of_length_le (by rw [g.c])]) hs)).trans (padZ q (mC_pad L q hq))
    have hU2 : regValue (mU L) s2.basis = u := by
      rw [regValue_congr (mU L) _ (s.basis) (fun q hq => k2 q
        (fun ho => (other_away L hn q (Or.inl (List.mem_of_mem_drop hq))).1 ho) (g.UR q hq) (g.US q hq)), hU]
    have P2 : WinArith.PS (mR L) (mS L) s2.basis (u + 4294968273*d) 0 s2.basis := ⟨h2.2.1, h2.2.2.1, fun _ _ _ => rfl⟩
    obtain ⟨ph, h3⟩ := WinArith.tInv_spec g cl2 u d hU2 hu32 ws2 (by omega) s2 m2 P2
    refine ⟨ph, ?_, h3.1, h3.2.1, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => h3.2.2 q (fun hr => (m_away L hn q (Or.inl hr)).1 hq)
        (fun hs => (m_away L hn q (Or.inr hs)).1 hq))).trans h2.1
    · intro q a b c; exact (h3.2.2 q b c).trans (k2 q a b c)
  obtain ⟨ph, f⟩ := (T1.seq (T2.seq T3)) s m P0
  refine ⟨ph, f.1, ?_, ?_, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => f.2.2.2 q (eReg_away L hn q hq).1
      (fun hr => (m_away L hn q (Or.inl hr)).2 hq) (fun hs => (m_away L hn q (Or.inr hs)).2 hq))).trans h.2.1
  · -- the work register is `W` again
    have wv : regValue L.core.work (run (wFwd L ++ (wCoreTq L ++ wInv L)) m s).basis = W := by
      rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
      have lo : regValue (L.core.work.take 128) (run (wFwd L ++ (wCoreTq L ++ wInv L)) m s).basis = W % 2^128 := by
        rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
          WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
      have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwd L ++ (wCoreTq L ++ wInv L)) m s).basis = 0 := by
        apply (regValue_zero _ _).mpr
        intro q hq
        rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
        apply workZ
        have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
        rw [this] at hq
        exact List.mem_of_mem_drop hq
      have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwd L ++ (wCoreTq L ++ wInv L)) m s).basis = u + d :=
        f.2.1
      rw [lo, mr, hi0]
      omega
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) (run (wFwd L ++ (wCoreTq L ++ wInv L)) m s).basis
    rw [List.take_append_drop] at sp
    rw [accReg, WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), wv, Nat.mod_eq_of_lt hWlt]
  · intro q h1 h2 h3
    by_cases hr : q ∈ mR L
    · -- bits 163..170 of work are clear again
      have wq : q ∈ L.core.work := mR_work L q hr
      have hd163 : q ∈ L.core.work.drop 163 := by
        have e := L.core.work.take_append_drop 163
        rw [← e] at wq
        rcases List.mem_append.mp wq with a|a
        · exact absurd a h3
        · exact a
      have wv : regValue L.core.work (run (wFwd L ++ (wCoreTq L ++ wInv L)) m s).basis = W := by
        rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
        have lo : regValue (L.core.work.take 128) (run (wFwd L ++ (wCoreTq L ++ wInv L)) m s).basis = W % 2^128 := by
          rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
            WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
        have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwd L ++ (wCoreTq L ++ wInv L)) m s).basis = 0 := by
          apply (regValue_zero _ _).mpr
          intro q hq
          rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
          apply workZ
          have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
          rw [this] at hq
          exact List.mem_of_mem_drop hq
        have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwd L ++ (wCoreTq L ++ wInv L)) m s).basis = u + d :=
          f.2.1
        rw [lo, mr, hi0]
        omega
      have z : regValue (L.core.work.drop 163) (run (wFwd L ++ (wCoreTq L ++ wInv L)) m s).basis = 0 := by
        rw [WinArith.drop_div _ _ (by simp [hw.core.work]), wv, Nat.div_eq_of_lt hWlt]
      rw [(regValue_zero _ _).mp z q hd163]
      exact ((regValue_zero _ _).mp hc.work q wq).symm
    by_cases hs : q ∈ mS L
    · rw [(regValue_zero _ _).mp f.2.2.1 q hs]
      exact ((regValue_zero _ _).mp hc.pad q (mS_pad L q hs)).symm
    · exact (f.2.2.2 q h1 hr hs).trans (keepS q h1 h2 h3)

end ECDSAAdd.Entrant.ControlLoan1589BFFold

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KnownTopAdd

/-! ## The `e` adders with source `u` -/

/-- `u` zero-extended to 128 bits with clear work wires. -/
def uLow (L : CuccaroStreamedSquareWideLayout) : List Wire := mU L ++ (L.core.work.drop 128).take 96
def uSrc (L : CuccaroStreamedSquareWideLayout) : List Wire := uLow L ++ eZ L
def eAddU (L : CuccaroStreamedSquareWideLayout) : Program := eAdd L (uSrc L)
/-- `-u` on `e` when the difference is below `2^128` and bit 129 is clear. -/
def eSubU (L : CuccaroStreamedSquareWideLayout) : Program :=
  subKnown (uLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L) (eKw L)
/-- No-op measurements on a clear bank wire: they keep the measurement count of the B body. -/
def padM (L : CuccaroStreamedSquareWideLayout) (n : Nat) : Program := List.replicate n (Instr.measureX (eKw L) [] [])

theorem uSrc_nodup (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
    (L.core.cin::(uSrc L++eReg L++eBank L)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have lc := lay_pos L hn q
  have ps := productSplit L q
  have pd := padSplit L q
  have ec := eReg_count L q
  have sc := singles_cin L q
  have hU : (mU L).count q ≤ (hiReg L).count q := (List.drop_sublist _ _).count_le q
  have hW : ((L.core.work.drop 128).take 96).count q ≤ L.core.work.count q := WinArith.cW _ _ _ q
  rw [show L.core.cin :: (uSrc L ++ eReg L ++ eBank L) = [L.core.cin] ++ (uSrc L ++ eReg L ++ eBank L) from rfl]
  simp only [uSrc, uLow, List.count_append] at lc ⊢
  omega

theorem uSrc_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (uSrc L).length=(eReg L).length ∧ (eBank L).length+1=(eReg L).length := by
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  simp [uSrc, uLow, mU, eZ, eBank, eReg, hiReg, fp, hw.core.product, hw.core.work]

theorem uLow_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) (t : BasisState) (h : BState L base O E 0 t) :
    regValue (uLow L) t = regValue (hiReg L) base / 2^96 := by
  obtain ⟨_,_,_,_,workZ⟩ := zero_regs L hn base hc O E 0 t h
  have wz : regValue L.core.work t = 0 := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) t
    rw [List.take_append_drop] at sp
    rw [sp, (regValue_zero _ _).mpr workZ]; simpa [accReg] using h.2.2.1
  have z : regValue ((L.core.work.drop 128).take 96) t = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp wz q (WinArith.mem_win hq))
  rw [uLow, regValue_append, z, hi96 L hw,
    regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E 0 t h q (Or.inl hq))]
  simp

theorem uSrc_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) (t : BasisState) (h : BState L base O E 0 t) :
    regValue (uSrc L) t = regValue (hiReg L) base / 2^96 := by
  obtain ⟨_,_,_,padZ,_⟩ := zero_regs L hn base hc O E 0 t h
  have z : regValue (eZ L) t = 0 :=
    (regValue_zero _ _).mpr (fun q hq => padZ q (List.mem_of_mem_drop (List.mem_of_mem_take (show q ∈ (L.foldPad.drop 129).take 2 from hq))))
  rw [uSrc, regValue_append, z, uLow_value L hw hn base hc O E t h]
  simp

theorem eAddU_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) :
    Triple (BState L base O E 0) (eAddU L) (BState L base O ((E+regValue (hiReg L) base / 2^96)%2^130) 0) := by
  apply lift_e L hn base O E 0 _ (eAddU L)
  intro s m h
  obtain ⟨_,_,hi,padZ,_⟩ := zero_regs L hn base hc O E 0 s.basis h
  have nd := uSrc_nodup L hn
  have lens := uSrc_length L hw
  have bank0 : regValue (eBank L) s.basis=0 := (regValue_zero _ _).mpr (fun q hq => padZ q (List.mem_of_mem_take hq))
  have tr := addInPlace_cin_frame L.core.cin (uSrc L) (eReg L) (eBank L) nd lens.1 lens.2 s.basis false hi bank0 E
    s m ⟨h.2.1,fun _ _ => rfl⟩
  have hv := tr.2.1
  rw [uSrc_value L hw hn base hc O E s.basis h, eReg_length L hw] at hv
  simp only [Bool.toNat_false,Nat.add_zero] at hv
  exact ⟨tr.1,hv,tr.2.2⟩

theorem eU_nodup (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (j : Nat) (hj : j≤128) :
    (L.core.cin::eU L::eV L::eZ0 L::eKw L::(uLow L++eRlow L++(eBank L).take j)).Nodup := by
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  have b := uSrc_nodup L hn
  rw [uSrc,e1,e2] at b
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have c := List.nodup_iff_count_le_one.mp b q
  have d := congrArg (List.count q) e3
  have f : ((eBank L).take j).count q≤((eBank L).take 128).count q := by
    have : (eBank L).take j=((eBank L).take 128).take j := by
      rw [List.take_take]; congr 1; omega
    rw [this]
    exact (List.take_sublist j _).count_le q
  simp only [List.count_cons,List.count_append,List.count_nil] at c d ⊢
  omega

theorem eSubU_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E S : Nat)
    (hS : regValue (hiReg L) base / 2^96 = S)
    (hE : E<2^129) (g1 : S≤E) (g2 : E-S<2^128) :
    Triple (BState L base O E 0) (eSubU L) (BState L base O ((E+2^130-S)%2^130) 0) := by
  apply lift_e L hn base O E 0 _ (eSubU L)
  intro s m h
  obtain ⟨e1,⟨z1,e2⟩,e3⟩ := eShape L hw
  obtain ⟨f1,f2,f3,f4,f5⟩ := eK_facts L hw hn base hc O E 0 s.basis h
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have wl : (uLow L).length=128 := by simp [uLow,mU,hiReg,hw.core.work,hw.core.product]
  have hwv : regValue (uLow L) s.basis = S := by rw [uLow_value L hw hn base hc O E s.basis h, hS]
  have hv : regValue (eReg L) s.basis=E := h.2.1
  rw [e1,reg_snoc2,rl] at hv
  have hv2 : s.basis (eV L)=false := by
    cases e : s.basis (eV L)
    · rfl
    · simp only [e,if_true] at hv
      norm_num at hv hE
      omega
  have hr : regValue (eRlow L ++ [eU L]) s.basis=E := by
    rw [reg_snoc, rl]
    simp only [hv2,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at hv
    exact hv
  obtain ⟨p,v,f⟩ := subKnown_spec (uLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eZ0 L) (eU L) (eV L) (eKw L)
    (eU_nodup L hw hn 127 (by omega)) (by rw [wl,rl]) (by simp [eBank,fp,rl]) (by omega)
    s m f2 f1 f3 (f4 127) hv2 (by rw [hwv,hr]; exact g1) (by rw [hwv,hr,rl]; exact g2)
  refine ⟨p,?_,?_⟩
  · rw [show run (eSubU L) m s=run (subKnown (uLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L) (eKw L)) m s from rfl]
    rw [e1,v,rl,hwv]
    have : regValue (eRlow L ++ [eU L, eV L]) s.basis = E := by rw [← e1]; exact h.2.1
    rw [this]
  · intro q hq
    rw [e1] at hq
    exact f q (fun x => hq (by simp [x])) (fun x => hq (by simp [x])) (fun x => hq (by simp [x]))

theorem padM_run (k : Wire) (n : Nat) : ∀ (m : List Bool) (s : State), s.basis k = false →
    run (List.replicate n (Instr.measureX k [] [])) m s = s := by
  induction n with
  | zero => intro m s _; rfl
  | succ n ih =>
    intro m s hk
    rw [List.replicate_succ, noop_run k _ m s hk]
    exact ih _ s hk

theorem padM_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E A : Nat) (n : Nat) :
    Triple (BState L base O E A) (padM L n) (BState L base O E A) := by
  intro s m h
  have k := (eK_facts L hw hn base hc O E A s.basis h).2.1
  rw [padM, padM_run (eKw L) n m s k]
  exact ⟨rfl, h⟩

end ECDSAAdd.Entrant.ControlLoan1589BFFold

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem flip_shift (e0 u d : Nat) (he : e0 < 2^128 ∨ (2^130 - 2^128 ≤ e0 ∧ e0 < 2^130)) (hud : u + d < 2^35) :
    flipE true ((e0 + u) % 2^130) = flipE true ((e0 + (u+d)) % 2^130) + d := by
  simp only [flipE, if_true]
  omega

theorem e0_range (b0 b1 : Nat) (h0 : b0 < 2^128) (h1 : b1 < 2^128) :
    (b0+2^130-b1)%2^130 < 2^128 ∨ (2^130 - 2^128 ≤ (b0+2^130-b1)%2^130 ∧ (b0+2^130-b1)%2^130 < 2^130) := by
  omega

/-- Moving `(c-1)·d` from the `e` fold to the `W` fold does not change the B-body result. -/
theorem o4_eq (b0 b1 O2 : Nat) (g : Bool) (h0 : b0 < 2^128) (h1 : b1 < 2^128) (hO2 : O2 < SquareReduction.p)
    (hg : g = false → b1 = 0 ∧ b0 = 0) :
    (4294968272*flipE g (((b0+2^130-b1)%2^130 + b1/2^96)%2^130) + (SquareReduction.p-1-
      (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128) +
        (SquareReduction.p-1-O2)) % SquareReduction.p))) % SquareReduction.p =
    (4294968272*flipE g (((b0+2^130-b1)%2^130 + 4294968272*b1/2^128)%2^130) + (SquareReduction.p-1-
      ((4294968272*b1/2^128 + 2^128*((4294968272*b1)%2^128) + (SquareReduction.p-1-O2)) % SquareReduction.p))) %
        SquareReduction.p := by
  cases g with
  | false =>
    obtain ⟨e1, e0⟩ := hg rfl
    subst e1; subst e0
    norm_num
  | true =>
    obtain ⟨ws1, ws2, ws3⟩ := whi_split b1 h1
    have fs := flip_shift ((b0+2^130-b1)%2^130) (b1/2^96) (4294968272*b1/2^128 - b1/2^96) (e0_range b0 b1 h0 h1)
      (by omega)
    rw [show b1/2^96 + (4294968272*b1/2^128 - b1/2^96) = 4294968272*b1/2^128 by omega] at fs
    rw [fs]
    generalize flipE true (((b0+2^130-b1)%2^130 + 4294968272*b1/2^128)%2^130) = F
    have wl := Nat.mod_lt (4294968272*b1) (show 2^128 > 0 by positivity)
    generalize (4294968272*b1)%2^128 = w at wl ⊢
    generalize hwh : 4294968272*b1/2^128 = wh at ws1 ws2 ws3 ⊢
    generalize b1/2^96 = u at ws1 ws2 ⊢
    norm_num [SquareReduction.p, SquareReduction.B, SquareReduction.c] at hO2 ⊢
    omega

end ECDSAAdd.Entrant.ControlLoan1589BFFold

namespace ECDSAAdd.Entrant.WinArith
open ECDSAAdd ECDSAAdd.Arithmetic Instr

theorem addC (x y cs : List Wire) (cin : Wire) (n : Nat) (hy : y.length = n) (hx : x.length = n)
    (hc : cs.length + 1 = n) :
    toffoliCount (addInPlace x y cs cin) = n - 1 ∧ measurementCount (addInPlace x y cs cin) = n - 1 := by
  have h := addInPlace_counts x y cs cin (by rw [hx, hy]) (by rw [hc, hy])
  rw [hy] at h; exact h

theorem subC (x y cs : List Wire) (cin : Wire) (n : Nat) (hy : y.length = n) (hx : x.length = n)
    (hc : cs.length + 1 = n) :
    toffoliCount (subInPlace x y cs cin) = n - 1 ∧ measurementCount (subInPlace x y cs cin) = n - 1 := by
  have h := subInPlace_counts x y cs cin (by rw [hx, hy]) (by rw [hc, hy])
  rw [hy] at h; exact h

theorem cpC (src dst : List Wire) (hl : src.length = dst.length) :
    toffoliCount (copyRegister none src dst) = 0 ∧ measurementCount (copyRegister none src dst) = 0 := by
  have h := copyRegister_counts none src dst hl
  simpa using h

section Counts
variable {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U)
include g

theorem Lens.lens (k n j i : Nat) (hkn : k + n ≤ 43) (hj : j ≤ 11) (hi : i ≤ 42) :
    ((R.drop k).take n).length = n ∧ (Z.take j).length = j ∧ (cs.take i).length = i ∧
    (S ++ Z.take j).length = 10 + j ∧ (U ++ Z.take j).length = 32 + j ∧ (U ++ Z).length = 43 := by
  refine ⟨by simp [g.r]; omega, by simp [g.z]; omega, by simp [g.c]; omega, by simp [g.s, g.z]; omega,
    by simp [g.u, g.z]; omega, by simp [g.u, g.z]⟩
theorem tFwd_counts :
    toffoliCount (tFwd R S Z cs U cin) = 79 ∧ measurementCount (tFwd R S Z cs U cin) = 102 := by
  have s1 := KnownWindowSubDevelop.sub33_counts (cin:=cin) g
  have c2 := cpC ((R.drop 0).take 10) S (by rw [(g.lens 0 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have sm := WinArithSmallDevelop.smallF_counts (cin:=cin) g
  have c4 := cpC S ((R.drop 32).take 10) (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have c5 := cpC ((R.drop 32).take 10) S (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have s6 := addC (U ++ Z.take 10) ((R.drop 0).take 42) (cs.take 41) cin 42
    (g.lens 0 42 10 41 (by omega) (by omega) (by omega)).1
    (g.lens 0 42 10 41 (by omega) (by omega) (by omega)).2.2.2.2.1
    (by rw [(g.lens 0 42 10 41 (by omega) (by omega) (by omega)).2.2.1])
  simp only [tFwd, toffoliCount_append, measurementCount_append, s1.1, s1.2, c2.1, c2.2, sm.1, sm.2, c4.1, c4.2, c5.1, c5.2, s6.1, s6.2]
  exact ⟨trivial, trivial⟩

theorem tInv_counts :
    toffoliCount (tInv R S Z cs U cin) = 76 ∧ measurementCount (tInv R S Z cs U cin) = 103 := by
  have s1 := KnownWindowSubDevelop.sub43_counts (cin:=cin) g
  have c2 := cpC ((R.drop 32).take 10) S (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have c3 := cpC S ((R.drop 32).take 10) (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have sm := WinArithSmallDevelop.smallI_counts (cin:=cin) g
  have c5 := cpC ((R.drop 0).take 10) S (by rw [(g.lens 0 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have s6 := addC (U ++ Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin 33
    (g.lens 0 33 1 32 (by omega) (by omega) (by omega)).1
    (g.lens 0 33 1 32 (by omega) (by omega) (by omega)).2.2.2.2.1
    (by rw [(g.lens 0 33 1 32 (by omega) (by omega) (by omega)).2.2.1])
  simp only [tInv, sm.1, sm.2, toffoliCount_append, measurementCount_append, s1.1, s1.2, c2.1, c2.2, c3.1, c3.2, c5.1, c5.2, s6.1, s6.2]
  exact ⟨trivial, trivial⟩

end Counts
end ECDSAAdd.Entrant.WinArith

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KnownTopAdd

theorem padM_counts (L : CuccaroStreamedSquareWideLayout) (n : Nat) :
    toffoliCount (padM L n) = 0 ∧ measurementCount (padM L n) = n := by
  induction n with
  | zero => simp [padM, toffoliCount, measurementCount]
  | succ n ih =>
    simp only [padM, List.replicate_succ, toffoliCount, measurementCount] at ih ⊢
    omega

theorem eAddU_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (eAddU L)=129 ∧ measurementCount (eAddU L)=129 := by
  have ls := uSrc_length L hw
  have h := addInPlace_counts (uSrc L) (eReg L) (eBank L) L.core.cin ls.1 ls.2
  rw [eReg_length L hw] at h
  exact ⟨h.1.trans (by norm_num), h.2.trans (by norm_num)⟩

theorem eSubU_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (eSubU L)=127 ∧ measurementCount (eSubU L)=129 := by
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have wl : (uLow L).length=128 := by simp [uLow,mU,hiReg,hw.core.work,hw.core.product]
  have k := subKnown_counts (uLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eZ0 L) (eU L) (eKw L)
    (by rw [wl, rl]) (by simp [eBank, fp, rl]) (by omega)
  have mid := addInPlace_counts (uLow L++[eZ0 L]) (eRlow L++[eU L]) ((eBank L).take 127++[eKw L]) L.core.cin
    (by simp [wl,rl]) (by simp [eBank,fp,rl])
  simp only [List.length_append,List.length_singleton,rl] at mid
  simp only [eSubU]
  omega

theorem wFwd_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (wFwd L)=79 ∧ measurementCount (wFwd L)=102 := WinArith.tFwd_counts (mLens L hw)
theorem wInv_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (wInv L)=76 ∧ measurementCount (wInv L)=103 := WinArith.tInv_counts (mLens L hw)

end ECDSAAdd.Entrant.ControlLoan1589BFFold

namespace ECDSAAdd.Entrant.WinArith
open ECDSAAdd ECDSAAdd.Arithmetic Instr

section Static
variable {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U)
include g

/-- Every wire the transform touches. -/
def Mem (R S Z cs U : List Wire) (cin q : Wire) : Prop :=
  q = cin ∨ q ∈ U ∨ q ∈ R ∨ q ∈ S ∨ q ∈ Z ∨ q ∈ cs

theorem pieceAdd (x y c : List Wire) (hx : x.length = y.length) (hc : c.length + 1 = y.length)
    (hm : ∀ q ∈ x ++ y ++ c, Mem R S Z cs U cin q) :
    ∀ q ∈ wires (addInPlace x y c cin), Mem R S Z cs U cin q := by
  intro q hq
  rw [addInPlace_wires x y c cin hx hc] at hq
  simp only [List.mem_toFinset, List.mem_cons] at hq
  rcases hq with rfl|hq
  · exact Or.inl rfl
  · exact hm q hq

theorem pieceSub (x y c : List Wire) (hx : x.length = y.length) (hc : c.length + 1 = y.length)
    (hm : ∀ q ∈ x ++ y ++ c, Mem R S Z cs U cin q) :
    ∀ q ∈ wires (subInPlace x y c cin), Mem R S Z cs U cin q := by
  intro q hq
  rw [subInPlace_wires x y c cin hx hc] at hq
  simp only [List.mem_toFinset, List.mem_cons] at hq
  rcases hq with rfl|hq
  · exact Or.inl rfl
  · exact hm q hq

theorem pieceCp (x y : List Wire) (hm : ∀ q ∈ x ++ y, Mem R S Z cs U cin q) :
    ∀ q ∈ wires (copyRegister none x y), Mem R S Z cs U cin q := by
  intro q hq
  have h := List.mem_toFinset.mp (copyRegister_wires_subset none x y hq)
  simp only [Option.toList_none, List.nil_append] at h
  exact hm q h

theorem mU' (j : Nat) : ∀ q ∈ U ++ Z.take j, Mem R S Z cs U cin q := by
  intro q h; rcases List.mem_append.mp h with h|h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h)))))
theorem mS' (j : Nat) : ∀ q ∈ S ++ Z.take j, Mem R S Z cs U cin q := by
  intro q h; rcases List.mem_append.mp h with h|h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h)))))
theorem mR' (k n : Nat) : ∀ q ∈ (R.drop k).take n, Mem R S Z cs U cin q :=
  fun q h => Or.inr (Or.inr (Or.inl (mem_win h)))
theorem mC' (i : Nat) : ∀ q ∈ cs.take i, Mem R S Z cs U cin q :=
  fun q h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.mem_of_mem_take h)))))
theorem mSS : ∀ q ∈ S, Mem R S Z cs U cin q := fun q h => Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem tri (a b c : List Wire) (ha : ∀ q ∈ a, Mem R S Z cs U cin q) (hb : ∀ q ∈ b, Mem R S Z cs U cin q)
    (hc : ∀ q ∈ c, Mem R S Z cs U cin q) : ∀ q ∈ a ++ b ++ c, Mem R S Z cs U cin q := by
  intro q h; simp only [List.mem_append] at h; rcases h with (h|h)|h
  · exact ha q h
  · exact hb q h
  · exact hc q h
theorem duo (a b : List Wire) (ha : ∀ q ∈ a, Mem R S Z cs U cin q) (hb : ∀ q ∈ b, Mem R S Z cs U cin q) :
    ∀ q ∈ a ++ b, Mem R S Z cs U cin q := by
  intro q h; rcases List.mem_append.mp h with h|h
  · exact ha q h
  · exact hb q h

theorem uz : ∀ q ∈ U ++ Z, Mem R S Z cs U cin q := by
  intro q h; rcases List.mem_append.mp h with h|h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem tFwd_mem : ∀ q ∈ wires (tFwd R S Z cs U cin), Mem R S Z cs U cin q := by
  have L1 := g.lens
  intro q hq
  simp only [tFwd, wires_append, Finset.mem_union] at hq
  rcases hq with h|h|h|h|h|h
  · have known:=KnownWindowSubDevelop.sub33_support R Z cs U cin h
    simp only [KnownWindowSubDevelop.ports,Mem,List.mem_toFinset,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_assoc] at known ⊢
    tauto
  · exact pieceCp g _ _ (duo g _ _ (mR' g 0 10) (mSS g)) q h
  · have small:=WinArithSmallDevelop.smallF_support R S cs cin h
    simp only [Mem,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at small ⊢
    tauto
  · exact pieceCp g _ _ (duo g _ _ (mSS g) (mR' g 32 10)) q h
  · exact pieceCp g _ _ (duo g _ _ (mR' g 32 10) (mSS g)) q h
  · exact pieceAdd g _ _ _ (by rw [(L1 0 42 10 41 (by omega) (by omega) (by omega)).1,
      (L1 0 42 10 41 (by omega) (by omega) (by omega)).2.2.2.2.1])
      (by rw [(L1 0 42 10 41 (by omega) (by omega) (by omega)).1,
      (L1 0 42 10 41 (by omega) (by omega) (by omega)).2.2.1])
      (tri g _ _ _ (mU' g 10) (mR' g 0 42) (mC' g 41)) q h

theorem tInv_mem : ∀ q ∈ wires (tInv R S Z cs U cin), Mem R S Z cs U cin q := by
  have L1 := g.lens
  intro q hq
  simp only [tInv, wires_append, Finset.mem_union] at hq
  rcases hq with h|h|h|h|h|h
  · have known:=KnownWindowSubDevelop.sub43_support R Z cs U cin h
    simp only [KnownWindowSubDevelop.ports,Mem,List.mem_toFinset,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_assoc] at known ⊢
    tauto
  · exact pieceCp g _ _ (duo g _ _ (mR' g 32 10) (mSS g)) q h
  · exact pieceCp g _ _ (duo g _ _ (mSS g) (mR' g 32 10)) q h
  · have small:=WinArithSmallDevelop.smallI_support R S cs cin h
    simp only [Mem,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at small ⊢
    tauto
  · exact pieceCp g _ _ (duo g _ _ (mR' g 0 10) (mSS g)) q h
  · exact pieceAdd g _ _ _ (by rw [(L1 0 33 1 32 (by omega) (by omega) (by omega)).1,
      (L1 0 33 1 32 (by omega) (by omega) (by omega)).2.2.2.2.1])
      (by rw [(L1 0 33 1 32 (by omega) (by omega) (by omega)).1,
      (L1 0 33 1 32 (by omega) (by omega) (by omega)).2.2.1])
      (tri g _ _ _ (mU' g 1) (mR' g 0 33) (mC' g 32)) q h

theorem tFwd_slots : Challenge.gateSlots (tFwd R S Z cs U cin) ≤ 1640 := by
  have L1 := g.lens
  have sm := WinArithSmallDevelop.smallF_slots (cin:=cin) g
  have s1 := KnownWindowSubDevelop.sub33_slots (cin:=cin) g
  have a6 := Baselines.addInPlace_gateSlots_le (U ++ Z.take 10) ((R.drop 0).take 42) (cs.take 41) cin
  rw [(L1 0 42 10 41 (by omega) (by omega) (by omega)).2.2.2.2.1] at a6
  simp only [tFwd, Challenge.gateSlots_append, Baselines.copyRegister_gateSlots,
    (L1 0 10 0 0 (by omega) (by omega) (by omega)).1, (L1 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s]
  omega

theorem tInv_slots : Challenge.gateSlots (tInv R S Z cs U cin) ≤ 1550 := by
  have L1 := g.lens
  have sm := WinArithSmallDevelop.smallI_slots (cin:=cin) g
  have s1 := KnownWindowSubDevelop.sub43_slots (cin:=cin) g
  have a6 := Baselines.addInPlace_gateSlots_le (U ++ Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin
  rw [(L1 0 33 1 32 (by omega) (by omega) (by omega)).2.2.2.2.1] at a6
  simp only [tInv, Challenge.gateSlots_append, Baselines.copyRegister_gateSlots,
    (L1 0 10 0 0 (by omega) (by omega) (by omega)).1, (L1 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s]
  omega

end Static

section Phys
variable {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
include g

theorem Geo.ndA (j k n i : Nat) : (cin :: (S ++ Z.take j) ++ (R.drop k).take n ++ cs.take i).Nodup := by
  simpa only [List.cons_append, List.append_assoc] using g.ndS j k n i
theorem Geo.ndB (j k n i : Nat) : (cin :: (U ++ Z.take j) ++ (R.drop k).take n ++ cs.take i).Nodup := by
  simpa only [List.cons_append, List.append_assoc] using g.ndU j k n i
theorem Geo.ndC (k n i : Nat) : (cin :: (U ++ Z) ++ (R.drop k).take n ++ cs.take i).Nodup := by
  simpa only [List.cons_append, List.append_assoc] using g.ndUZ k n i
theorem tFwd_physical : GatePhysical (tFwd R S Z cs U cin) := by
  simp only [tFwd,gatePhysical_append]
  exact ⟨KnownWindowSubDevelop.sub33_physical g,copyRegister_physical _ _ _ (g.ndIn 0) (by simp),
    WinArithSmallDevelop.smallF_physical g,copyRegister_physical _ _ _ (g.ndOut 32) (by simp),
    copyRegister_physical _ _ _ (g.ndIn 32) (by simp),addInPlace_physical _ _ _ _ (g.ndB 10 0 42 41)⟩

theorem tInv_physical : GatePhysical (tInv R S Z cs U cin) := by
  simp only [tInv,gatePhysical_append]
  exact ⟨KnownWindowSubDevelop.sub43_physical g,copyRegister_physical _ _ _ (g.ndIn 32) (by simp),
    copyRegister_physical _ _ _ (g.ndOut 32) (by simp),WinArithSmallDevelop.smallI_physical g,
    copyRegister_physical _ _ _ (g.ndIn 0) (by simp),addInPlace_physical _ _ _ _ (g.ndB 1 0 33 32)⟩

end Phys
end ECDSAAdd.Entrant.WinArith

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KnownTopAdd

/-! ## Static facts of the new B body -/

theorem op_slots (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hx : (Acc.tx Z w f).length = (Acc.ty acc f).length) (hc : (Acc.tc bank w f).length + 1 = (Acc.ty acc f).length) :
    Challenge.gateSlots (Acc.op acc Z bank cin w false f) + 10 = 12 * (Acc.ty acc f).length := by
  simp only [Acc.op, Bool.false_eq_true, if_false]
  exact addInPlace_slots_eq _ _ _ _ hx hc

theorem wBuild_slots_ge (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    3076 ≤ Challenge.gateSlots (wBuild L) := by
  have l := acc_lengths L hw
  have hl := hiReg_length L hw
  have a := op_slots ((accReg L).take 139) (accZ L) (accBank L) L.core.cin 139 (Acc.earlyTerm (hiReg L) false 10)
    (by simp [Acc.tx, Acc.ty, Acc.earlyTerm, l.1, l.2.1, hl]) (by simp [Acc.tc, Acc.ty, Acc.earlyTerm, l.1, l.2.2.1])
  have b := op_slots ((accReg L).take 161) (accZ L) (accBank L) L.core.cin 161 (Acc.earlyTerm (hiReg L) false 32)
    (by simp [Acc.tx, Acc.ty, Acc.earlyTerm, l.1, l.2.1, hl]) (by simp [Acc.tc, Acc.ty, Acc.earlyTerm, l.1, l.2.2.1])
  have ya : (Acc.ty ((accReg L).take 139) (Acc.earlyTerm (hiReg L) false 10)).length = 129 := by
    simp [Acc.ty, Acc.earlyTerm, l.1]
  have yb : (Acc.ty ((accReg L).take 161) (Acc.earlyTerm (hiReg L) false 32)).length = 129 := by
    simp [Acc.ty, Acc.earlyTerm, l.1]
  rw [ya] at a; rw [yb] at b
  simp only [wBuild, NarrowAcc.build8, NarrowAcc.pre8, Challenge.gateSlots_append]
  omega

theorem wUnbuild_slots_ge (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    1586 ≤ Challenge.gateSlots (wUnbuild L) := by
  have l := acc_lengths L hw
  have hl := hiReg_length L hw
  have a := op_slots ((accReg L).take 139) (accZ L) (accBank L) L.core.cin 139 (Acc.earlyTerm (hiReg L) true 6)
    (by simp [Acc.tx, Acc.ty, Acc.earlyTerm, l.1, l.2.1, hl]) (by simp [Acc.tc, Acc.ty, Acc.earlyTerm, l.1, l.2.2.1])
  have ya : (Acc.ty ((accReg L).take 139) (Acc.earlyTerm (hiReg L) true 6)).length = 133 := by
    simp [Acc.ty, Acc.earlyTerm, l.1]
  rw [ya] at a
  simp only [wUnbuild, CodexNarrowTail.unbuild8, Challenge.gateSlots_append]
  omega

theorem padM_slots (L : CuccaroStreamedSquareWideLayout) (n : Nat) : Challenge.gateSlots (padM L n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [padM, List.replicate_succ, Baselines.gateSlots_cons, Challenge.instructionSlots, List.length_nil] at ih ⊢
    omega

theorem eAddU_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (eAddU L) = Challenge.gateSlots (eAdd L (whiSrc L)) := by
  have a := uSrc_length L hw
  have b := eSrc_length L hw (whiSrc L) (Or.inr rfl)
  have x := addInPlace_slots_eq (uSrc L) (eReg L) (eBank L) L.core.cin a.1 a.2
  have y := addInPlace_slots_eq (whiSrc L) (eReg L) (eBank L) L.core.cin b.1 b.2
  simp only [eAddU, eAdd]
  omega

theorem eSubU_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (eSubU L)≤Challenge.gateSlots (eSub L (whiSrc L)) := by
  have rl : (eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  have wl : (uLow L).length=128 := by simp [uLow,mU,hiReg,hw.core.work,hw.core.product]
  have ls := eSrc_length L hw (whiSrc L) (Or.inr rfl)
  have old := addInPlace_slots_eq (whiSrc L) (eReg L) (eBank L) L.core.cin ls.1 ls.2
  have new := addTop_slots_eq (uLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L)
    (by rw [wl,rl]) (by simp [eBank,fp,rl])
  rw [eReg_length L hw] at old
  rw [rl] at new
  simp only [eSub,eSubU,subKnown,subInPlace,Challenge.gateSlots_append,Baselines.gateSlots_cons,
    Baselines.gateSlots_nil,Baselines.notRegister_gateSlots,Challenge.instructionSlots,List.length_nil,
    rl,eReg_length L hw]
  omega

/-- The wires of the two `e` adders of the old fold, which host every new wire. -/
def oldE (L : CuccaroStreamedSquareWideLayout) : Finset Wire :=
  wires (eSub L (b1Src L)) ∪ wires (eAdd L (whiSrc L))

theorem win_take {l : List Wire} {a b n : Nat} {q : Wire} (h : q ∈ (l.drop a).take b) (hn : a + b ≤ n) :
    q ∈ l.take n := by
  have e : (l.take (a+b)).drop a = (l.drop a).take b := by rw [List.drop_take]; congr 1; omega
  rw [← e] at h
  have h2 := List.mem_of_mem_drop h
  have e2 : (l.take n).take (a+b) = l.take (a+b) := by rw [List.take_take]; congr 1; omega
  rw [← e2] at h2
  exact List.mem_of_mem_take h2

theorem oldE_mem (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (q : Wire)
    (h : q = L.core.cin ∨ q ∈ hiReg L ∨ q ∈ L.core.work.drop 128 ∨ q ∈ eReg L ∨ q ∈ eBank L ∨ q ∈ eZ L) :
    q ∈ oldE L := by
  have l1 := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have l2 := eSrc_length L hw (whiSrc L) (Or.inr rfl)
  have e1 : wires (eSub L (b1Src L)) = (L.core.cin :: (b1Src L ++ eReg L ++ eBank L)).toFinset :=
    subInPlace_wires _ _ _ _ l1.1 l1.2
  have e2 : wires (eAdd L (whiSrc L)) = (L.core.cin :: (whiSrc L ++ eReg L ++ eBank L)).toFinset :=
    addInPlace_wires _ _ _ _ l2.1 l2.2
  rw [oldE, e1, e2]
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append, b1Src, whiSrc]
  tauto

theorem mem_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (q : Wire)
    (h : WinArith.Mem (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin q) : q ∈ oldE L := by
  apply oldE_mem L hw q
  rcases h with h|h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (List.mem_of_mem_drop h))
  · exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (win_take h (by omega))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (win_take h (by omega))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      have : L.foldPad.take 42 = (L.foldPad.take 129).take 42 := by rw [List.take_take]; rfl
      rw [mC, this] at h; exact List.mem_of_mem_take h)))))

theorem eAddU_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : wires (eAddU L) ⊆ oldE L := by
  have ls := uSrc_length L hw
  intro q hq
  rw [eAddU, eAdd, addInPlace_wires _ _ _ _ ls.1 ls.2] at hq
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, uSrc, uLow, or_assoc] at hq
  apply oldE_mem L hw q
  rcases hq with h|h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (List.mem_of_mem_drop h))
  · exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem eSubU_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : wires (eSubU L) ⊆ oldE L := by
  obtain ⟨m1,m2,m3,m4,m5,m6⟩ := eK_mem L hw
  have tk : ∀q∈(eBank L).take 127,q∈eBank L := fun q h => List.mem_of_mem_take h
  have aw := addTop_wires_sub (uLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L)
  rw [show eSubU L=[Instr.measureX (eKw L) [] []]++(notRegister (eRlow L)++
      (addTop (uLow L) (eRlow L) ((eBank L).take 127) L.core.cin (eU L)++notRegister (eRlow L))) from rfl,
    wires_append, wires_append, wires_append, notRegister_wires]
  intro q hq
  apply oldE_mem L hw q
  simp only [Finset.mem_union] at hq
  rcases hq with h|h|h|h
  · simp [wires,Instr.wires,correctionWires] at h; subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl m1))))
  · simp only [List.mem_toFinset] at h; exact Or.inr (Or.inr (Or.inr (Or.inl (m5 q h))))
  · have h2 := aw h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,uLow,or_assoc] at h2
    rcases h2 with h|h|h|h|h|h
    · exact Or.inl h
    · subst h; exact Or.inr (Or.inr (Or.inr (Or.inl m2)))
    · exact Or.inr (Or.inl (List.mem_of_mem_drop h))
    · exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (m5 q h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (tk q h)))))
  · simp only [List.mem_toFinset] at h; exact Or.inr (Or.inr (Or.inr (Or.inl (m5 q h))))

theorem padM_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (n : Nat) : wires (padM L n) ⊆ oldE L := by
  intro q hq
  apply oldE_mem L hw q
  have m1 := (eK_mem L hw).1
  induction n with
  | zero => simp [padM, wires] at hq
  | succ n ih =>
    simp only [padM, List.replicate_succ] at hq
    rw [show (Instr.measureX (eKw L) [] [] :: List.replicate n (Instr.measureX (eKw L) [] [])) =
      [Instr.measureX (eKw L) [] []] ++ padM L n from rfl, wires_append, Finset.mem_union] at hq
    rcases hq with h|h
    · simp [wires,Instr.wires,correctionWires] at h; subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl m1))))
    · exact ih h

theorem wFwd_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    wires (wFwd L) ⊆ oldE L := fun q hq => mem_oldE L hw q (WinArith.tFwd_mem (mLens L hw) q hq)
theorem wInv_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    wires (wInv L) ⊆ oldE L := fun q hq => mem_oldE L hw q (WinArith.tInv_mem (mLens L hw) q hq)

end ECDSAAdd.Entrant.ControlLoan1589BFFold

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KnownTopAdd

theorem padM_physical (L : CuccaroStreamedSquareWideLayout) (n : Nat) : GatePhysical (padM L n) := by
  intro i hi
  rw [padM] at hi
  rw [List.eq_of_mem_replicate hi]
  simp [RecordedQuantum.PhysicalInstr]

theorem eAddU_physical (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) : GatePhysical (eAddU L) :=
  addInPlace_physical _ _ _ _ (by simpa only [List.cons_append, List.append_assoc] using uSrc_nodup L hn)

theorem eSubU_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (eSubU L) := by
  have h := eU_nodup L hw hn 127 (by omega)
  have sub : List.Sublist (L.core.cin :: eU L :: (uLow L ++ eRlow L ++ (eBank L).take 127))
      (L.core.cin::eU L::eV L::eZ0 L::eKw L::(uLow L++eRlow L++(eBank L).take 127)) :=
    List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (((List.sublist_cons_self _ _).trans
      (List.sublist_cons_self _ _)).trans (List.sublist_cons_self _ _)))
  exact subKnown_physical _ _ _ _ _ _ (h.sublist sub)

end ECDSAAdd.Entrant.ControlLoan1589BFFold

end

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-- The `W` fold with source `(u + c*d) + 2^128*(W mod 2^128)`; `e` gets `-b1` and `+u` after the unbuild. -/
def wFoldTq (L : CuccaroStreamedSquareWideLayout) : Program :=
  wBuild L++((wFwd L++(wCoreTq L++wInv L))++(wUnbuild L++(eSubK L++eAddU L)))

/-- The restore: `+b1` (the sum `b0+u` is below `2^129`), then `-u` (the result `b0` is below `2^128`).
No rebuild of `W`; 571 no-op measurements keep the measurement count of the B body. -/
def wRestoreT (L : CuccaroStreamedSquareWideLayout) : Program :=
  eAddB L++(eSubU L++padM L 571)

def eFoldTq (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  eFlip L c++(accFoldQ4KTq L (eItem L)++eFlip L c)

def bBodyTq (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(wFoldTq L++(eFoldTq L c++wRestoreT L)))


theorem wCore_stepTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E W : Nat) (hO : O<SquareReduction.p) (hW : W<2^163) :
    Triple (BState L base O E W) (wCoreTq L)
      (BState L base ((W/2^128+2^128*(W%2^128)+(SquareReduction.p-1-O))%SquareReduction.p) E W) := by
  apply lift_out L hn base O E W _ (wCoreTq L)
  intro s m h
  obtain ⟨_,_,hi,padZ,workZ⟩ := zero_regs L hn base hc O E W s.basis h
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hR : W/2^128+2^128*(W%2^128)<SquareReduction.p := by
    have a : W/2^128<2^35 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc W<2^163 := hW
        _ = 2^35*2^128 := by norm_num
    have b := Nat.mod_lt W (show 2^128>0 by positivity)
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at a b ⊢
    omega
  have keep (q : Wire) (hq : q=L.core.outHigh ∨ q=L.core.modFlag ∨ q=L.core.productHigh ∨ q=L.core.workHigh) :
      s.basis q=base q :=
    bstate_other L hn base O E W s.basis h q (Or.inr (Or.inr (Or.inr (by rcases hq with rfl|rfl|rfl|rfl <;> simp))))
  have carryZ : ∀q∈(rotWCore L).carry,s.basis q=false := by
    intro q hq
    simp only [rotWCore,measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact padZ q hq
    · exact (keep _ (Or.inr (Or.inr (Or.inl rfl)))).trans hc.productHigh
    · exact (keep _ (Or.inr (Or.inr (Or.inr rfl)))).trans hc.workHigh
  have ek := QCore.qprog_correctTq (rotWCore L) 256 SquareReduction.c SquareReduction.p (rotWCore_widths L hw)
    (rotWCore_nodup L hn) (by decide) hp (by norm_num [SquareReduction.c]) _ O hR hO s m
    (rotWork_value L hw s.basis W h.2.2.1 workZ) h.1
    ((keep _ (Or.inl rfl)).trans hc.outHigh) ((keep _ (Or.inr (Or.inl rfl))).trans hc.modFlag) carryZ hi
  exact ⟨ek.1,ek.2.1,ek.2.2⟩


theorem eCore_stepTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) (hO : O<SquareReduction.p) :
    Triple (BState L base O E 0) (accFoldQ4KTq L (eItem L))
      (BState L base ((4294968272*E+(SquareReduction.p-1-O))%SquareReduction.p) E 0) := by
  apply lift_out L hn base O E 0 _ (accFoldQ4KTq L (eItem L))
  intro s m h
  have e16 : Acc.accVal s.basis 0 (eItem L).spec%16=0 := by
    rw [show (eItem L).spec=earlyHTerms (eReg L) from rfl,accVal_earlyH,h.2.1]
    omega
  rw [Q4.accFoldQ4_runKTq L hw hn s.basis (eItem L) (eItem_view L hw s.basis)
    (bstate_clean L hn base hc O E s.basis h) O hO e16 s m ⟨h.1,fun _ _ => rfl⟩]
  have tr := accFoldQ_frameKTq L hw hn s.basis (eItem L) (eItem_view L hw s.basis)
    (bstate_clean L hn base hc O E s.basis h) O hO s m ⟨h.1,fun _ _ => rfl⟩
  have e : Acc.accVal s.basis 0 (eItem L).spec=4294968272*E := by
    rw [show (eItem L).spec=earlyHTerms (eReg L) from rfl,accVal_earlyH,h.2.1]
  rw [e] at tr
  exact ⟨tr.1,tr.2.1,tr.2.2⟩


theorem bBody_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (bBodyTq L c) (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let P := M^2
  let b0 := P%2^128
  let b1 := P/2^128
  let W := 4294968272*b1
  let g := base c
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have hb1lt : b1<2^128 := by
    show P/2^128<2^128
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hWlt : W<2^163 := by
    show 4294968272*b1<2^163
    norm_num at hb1lt ⊢
    omega
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frameTq L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have e0 : regValue (eReg L) base=b0 := eReg_value L hw base P hP hb
  have a0 : regValue (accReg L) base=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (accReg_work L q hq))
  have hb1 : regValue (hiReg L) base=b1 := by
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have conv1 : ∀s,SquareFrame L.core.out base O2 s → BState L base O2 b0 0 s := by
    intro s hs
    refine ⟨hs.1,?_,?_,fun q h1 _ _ => hs.2 q h1⟩
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (eReg_away L hn q hq).1)).trans e0
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (accReg_out L hn q hq))).trans a0

  let u := b1/2^96
  let d := W/2^128 - u
  let O3 := ((u + 4294968273*d) + 2^128*(W%2^128) + (SquareReduction.p-1-O2)) % SquareReduction.p
  let E1 := ((b0+2^130-b1)%2^130 + u) % 2^130
  let O4 := (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  -- wFoldTq
  have w1 := wBuild_step L hw hn base hc O2 b0
  rw [hb1] at w1
  have wm := wMid_step L hw hn base hc O2 b0 b1 hb1 hb1lt hO2
  have w5 := wUnbuild_step L hw hn base hc O3 b0
  rw [hb1] at w5
  have w3 := eSubK_step L hw hn base hc O3 b0 0 b1 (Nat.mod_lt _ (by positivity)) hb1
  have w4 := eAddU_step L hw hn base hc O3 ((b0+2^130-b1)%2^130)
  rw [hb1] at w4
  have tw : Triple (BState L base O2 b0 0) (wFoldTq L) (BState L base O3 E1 0) :=
    w1.seq (wm.seq (w5.seq (w3.seq w4)))
  -- eFoldTq
  have f1 := eFlip_step L hw hn base c hcw O3 E1 0
  have f2 := eCore_stepTq L hw hn base hc O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn base c hcw O4 (flipE g E1) 0
  rw [flipE_flipE] at f3
  have tf : Triple (BState L base O3 E1 0) (eFoldTq L c) (BState L base O4 E1 0) :=
    f1.seq (f2.seq f3)
  -- wRestoreT
  have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
  have hu35 : u<2^35 := by
    show b1/2^96<2^35
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc b1<2^128 := hb1lt
      _ < 2^35*2^96 := by norm_num
  have back : (E1+b1)%2^130<2^129 ∧ u≤(E1+b1)%2^130 ∧ (E1+b1)%2^130-u<2^128 ∧
      ((E1+b1)%2^130+2^130-u)%2^130=b0 := by
    have key : (E1+b1)%2^130=b0+u := back_arith b0 b1 u hb0 hb1lt hu35
    rw [key]
    exact back_facts b0 u hb0 hu35
  have r2 := eAddB_step L hw hn base hc O4 E1 0 b1 hb1 back.1
  have r3 := eSubU_step L hw hn base hc O4 ((E1+b1)%2^130) u (by rw [hb1]) back.1 back.2.1 back.2.2.1
  rw [back.2.2.2] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 571
  have tr : Triple (BState L base O4 E1 0) (wRestoreT L) (BState L base O4 b0 0) :=
    r2.seq (r3.seq rp)
  have conv2 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
    intro s hs
    refine ⟨hs.1,fun q hq => ?_⟩
    by_cases he : q∈eReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.1.trans e0.symm) q he
    by_cases ha : q∈accReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.2.1.trans a0.symm) q ha
    exact hs.2.2.2 q hq he ha
  have key : O4 = bO4 (M^2) (base c) O := by
    have hg' : g = false → b1 = 0 ∧ b0 = 0 := by
      intro h0
      have : M = 0 := hg h0
      subst this
      simp [b1, b0, P]
    exact o4_eq b0 b1 O2 g hb0 hb1lt hO2 hg'
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tf.seq tr)) conv2))
  rw [key] at all
  exact all


def aFold8Tq (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  wBuild L++(maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK++(qprogTq L.measuredCore SquareReduction.p++
    (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK++wUnbuild L)))


def aBodyTq (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++aFold8Tq L c)


theorem aFold8_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (g : Wire) (hg : g∉L.wires) (base : BasisState)
    (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (aFold8Tq L g)
      (SquareFrame L.core.out base (((if base g then OwnDiagAll12Square.cFlipK-4294968272*regValue (hiReg L) base
        else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have gAcc : g∉accReg L := fun h => hg (OwnDiagAll12Square.accReg_in L g h)
  have gOut : g∉L.core.out := fun h => hg (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := 4294968272*regValue (hiReg L) base
  have hH : regValue (hiReg L) base<2^128 := by
    have h := regValue_lt (hiReg L) base
    rwa [hiReg_length L hw] at h
  have hA : A<2^163 := by
    show 4294968272*regValue (hiReg L) base<2^163
    norm_num at hH ⊢
    omega
  have hAK : A≤OwnDiagAll12Square.cFlipK := by unfold OwnDiagAll12Square.cFlipK; omega
  let A' := if base g then OwnDiagAll12Square.cFlipK-A else A
  have hA' : A'<2^163 := by
    simp only [A']; split
    · unfold OwnDiagAll12Square.cFlipK; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hhi : regValue (hiReg L) b0=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => agree0 q (hiReg_product L q hq))
  have hbuild : Triple (SquareFrame (accReg L) b0 0) (wBuild L) (SquareFrame (accReg L) b0 A) := by
    have h := NarrowAcc.build8_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) b0 hz hb clean.cin
    rw [hhi] at h
    exact h
  rw [aFold8Tq,run_append,run_append,run_append,run_append]
  let mb := measurementCount (wBuild L)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (wBuild L) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK) (m1.take mc) u
  have fl := OwnDiagAll12Square.flip_run L hw hn g gAcc u (m1.take mc)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then OwnDiagAll12Square.cFlipK-regValue (accReg L) u.basis
      else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u1.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using accU1
  have outU : regValue L.core.out u1.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A'<SquareReduction.p := lt_of_lt_of_le hA' (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u1.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK) (m3.take mc) v
  have fl2 := OwnDiagAll12Square.flip_run L hw hn g gAcc v (m3.take mc)
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then OwnDiagAll12Square.cFlipK-regValue (accReg L) v.basis
      else regValue (accReg L) v.basis) at fl2
  rw [gV,accV] at fl2
  have back : (if base g then OwnDiagAll12Square.cFlipK-A' else A')=A := by
    simp only [A']
    cases base g
    · simp
    · simp only [if_true]; omega
  rw [back] at fl2
  let base2 : BasisState := fun q => if q∈L.core.out then v1.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have frame2 : SquareFrame (accReg L) base2 A v1.basis := by
    refine ⟨fl2.2.2,?_⟩
    intro q hq
    by_cases ho : q∈L.core.out
    · simp [base2,ho]
    · rw [b2off q ho,fl2.2.1 q hq,ek.2.2 q ho,fl.2.1 q hq]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hhi2 : regValue (hiReg L) base2=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => (b2off q (prodNotOut q (hiReg_product L q hq))).trans
      (agree0 q (hiReg_product L q hq)))
  have hun : Triple (SquareFrame (accReg L) base2 A) (wUnbuild L) (SquareFrame (accReg L) base2 0) := by
    have h := CodexNarrowTail.unbuild8_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) base2 hz2 hb2 hi2
    rw [hhi2] at h
    exact h
  have eo := hun v1 (m3.drop mc) frame2
  refine ⟨eo.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have e : regValue L.core.out (run (wUnbuild L) (m3.drop mc) v1).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq,fl2.2.1 q na]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq


theorem aBody_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (aBodyTq L c) (SquareFrame L.core.out base (resAF (M^2) O (base c))) := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  let P := M^2
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have v3 : AccView L base (aAcc L) := views (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frameTq L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have hAeq : Acc.accVal base 0 (aAcc L).spec=4294968272*regValue (hiReg L) base := by
    rw [show (aAcc L).spec=earlyHTerms (L.core.product.drop 128) from rfl,accVal_earlyH]
    congr 1
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb,hP]
  have t3 := aFold8_frameTq L hw hn c hcw base hc O2 hO2
  rw [← hAeq] at t3
  have all := t1.seq (t2.seq t3)
  apply Triple.conseq (fun s h => h) all
  intro s hs
  refine ⟨hs.1.trans ?_,hs.2⟩
  -- value
  let A := Acc.accVal base 0 (aAcc L).spec
  have hA : A<2^163 := Acc.accVal_lt base 163 (aAcc L).spec 0 (by norm_num) v3.specValid
  have hsum := (accA_mixSum L hw base).trans (L.measuredA_sum hw base (M^2) hP hb)
  have n1 : mixNeg (.inl (rot128F L) : MixItem)=false := rfl
  have n2 : mixNeg (.inr (aAcc L) : MixItem)=false := rfl
  have n3 : mixNeg (.inl (negP L) : MixItem)=true := rfl
  have e : accAMix L=[.inl (rot128F L),.inr (aAcc L),.inl (negP L)] := rfl
  rw [e] at hsum
  simp only [mixSignedSum,mixSignedPayload,n1,n2,n3,Bool.false_eq_true,if_false,if_true,mixPayload,add_zero,
    pay1,pay2] at hsum
  change ((((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
    (((A : Nat) : ZMod SquareReduction.p)+-((P : Nat) : ZMod SquareReduction.p)))=
      ((P : Nat) : ZMod SquareReduction.p)*2^128-(P : ZMod SquareReduction.p) at hsum
  have bound : ((if base c then OwnDiagAll12Square.cFlipK-A else A)+(SquareReduction.p-1-O2))%SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ pmod
  apply measuredOrientationCast_injective true _ _ bound (ofCast_lt true _)
  refine Eq.trans ?_ (cast_ofCast true (measuredOrientationCast false O+(((M^2 : Nat) : ZMod SquareReduction.p)*2^128-
    ((M^2 : Nat) : ZMod SquareReduction.p)-(if base c then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)))).symm
  simp only [measuredOrientationCast,if_true,Bool.false_eq_true,if_false]
  have c0 := measuredReflection_zmod O hO
  have c1 := measuredReflection_zmod O1 hO1
  have c2 := measuredReflection_zmod O2 hO2
  have k1 : (O1 : ZMod SquareReduction.p)=(P : ZMod SquareReduction.p)+(-1-(O : ZMod SquareReduction.p)) := by
    simp only [O1,ZMod.natCast_mod,Nat.cast_add,c0]
  have k2 : (O2 : ZMod SquareReduction.p)=(((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
      (-1-(O1 : ZMod SquareReduction.p)) := by
    rw [show O2=((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p from rfl,
      ZMod.natCast_mod,Nat.cast_add,c1]
  rw [ZMod.natCast_mod,Nat.cast_add,c2,k2,k1]
  cases hgv : base c
  · have M0 := hg hgv
    have P0 : P=0 := by show M^2=0; rw [M0]; norm_num
    have R0 : (((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)=0 := by rw [P0]; simp
    rw [R0,P0] at hsum
    simp only [Bool.false_eq_true,if_false]
    rw [R0,P0]
    have hM2 : ((M^2 : Nat) : ZMod SquareReduction.p)=0 := by rw [M0]; simp
    rw [hM2]
    simp at hsum ⊢
    linear_combination -hsum
  · simp only [if_true]
    have hAle : A≤OwnDiagAll12Square.cFlipK := by simp only [OwnDiagAll12Square.cFlipK]; omega
    have hoff : ((OwnDiagAll12Square.cFlipK-A : Nat) : ZMod SquareReduction.p)=(OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p)-
        (A : ZMod SquareReduction.p) := by
      rw [Nat.cast_sub hAle]
    rw [hoff]
    linear_combination hsum


end ECDSAAdd.Entrant.ControlLoan1589BFFold
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
theorem aBody_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) : ECDSAAdd.wires (aBodyTq L control)⊆(control::L.wires).toFinset := by
  have wb := wBuild_support L hw hn control
  have memP (f : MeasuredSquareFold) (h : ∀q,f.src.count q≤L.core.product.count q) : ∀q∈f.src,q∈L.core.product :=
    fun q hq => List.count_pos_iff.mp (by have := h q; have := List.count_pos_iff.mpr hq; omega)
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have a1 := measuredFoldQ_supportTq L control (negP L) (memP _ sP)
  have a2 := measuredFoldQ_supportTq L control (rot128F L) (memP _ sR)
  have full := accFoldQ_supportTq L hw hn control (aAcc L) sA.1 sA.2.1 sA.2.2.1 sA.2.2.2
  simp only [accFoldQTq,wires_append,Finset.union_subset_iff] at full
  have mc : ECDSAAdd.wires (maskedConstant control (accReg L) OwnDiagAll12Square.cFlipK)⊆
      (control::L.wires).toFinset := by
    refine (maskedConstant_wires_subset _ _ _).trans ?_
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq ⊢
    rcases hq with h|h
    · exact Or.inl h
    · exact Or.inr (OwnDiagAll12Square.accReg_in L q h)
  simp only [aBodyTq,aFold8Tq,wires_append,Finset.union_subset_iff]
  exact ⟨a1,a2,wb.1,mc,full.1.2,mc,wb.2⟩



theorem eItem_priceTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : accPriceQTq (eItem L)=1554 := by
  have hl := eReg_length L hw
  norm_num [eItem,accPriceQTq,earlyHTerms,Acc.earlyTerm,Acc.sbuildT,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,
    Acc.buildT,hl]


theorem aAcc_priceTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : accPriceQTq (aAcc L)=1554 := by
  norm_num [aAcc,accPriceQTq,earlyHTerms,Acc.earlyTerm,Acc.sbuildT,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,
    Acc.buildT,hw.core.product]


theorem bBody_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (bBodyTq L c)=5225 ∧ measurementCount (bBodyTq L c)=5924 := by
  have q1 := measuredFoldQ_countsTq L hw (negP L)
  have q2 := measuredFoldQ_countsTq L hw (rot128F L)
  have bc := CodexNarrowTail.build8_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_okLen L hw)
  rw [CodexNarrowTail.build8_eq] at bc
  have wb : toffoliCount (wBuild L)=387 ∧ measurementCount (wBuild L)=388 := bc.1
  have wu : toffoliCount (wUnbuild L)=358 ∧ measurementCount (wUnbuild L)=388 := bc.2
  have core := QCore.qprog_countsTq (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)
  have wc : toffoliCount (wCoreTq L)=766 ∧ measurementCount (wCoreTq L)=767 :=
    ⟨core.1.trans (by norm_num),core.2.trans (by norm_num)⟩
  have el := eReg_length L hw
  have l1 := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have s1 : toffoliCount (eSub L (b1Src L))=129 ∧ measurementCount (eSub L (b1Src L))=129 := by
    have h := subInPlace_counts (b1Src L) (eReg L) (eBank L) L.core.cin l1.1 l1.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have a1 : toffoliCount (eAdd L (b1Src L))=129 ∧ measurementCount (eAdd L (b1Src L))=129 := by
    have h := addInPlace_counts (b1Src L) (eReg L) (eBank L) L.core.cin l1.1 l1.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have fl : toffoliCount (eFlip L c)=0 ∧ measurementCount (eFlip L c)=0 :=
    maskedConstant_counts c ((eReg L).take 129) (2^129-1)
  have st := eItem_static L hw
  have ac0 := accFoldQ_countsTq L hw (eItem L) st.2.1 st.2.2.2
  rw [eItem_priceTq L hw] at ac0
  have ac4 := Q4.accFoldQ4_countsTq L hw (eItem L)
  have k4 := Q4.accFoldQ4KTq_counts_early L hw (eItem L) (eReg L) (by simp [eReg,hw.core.product]) rfl st.2.1
  have k4m := (Q4.accFoldQ4KTq_rel L hw (eItem L) st.2.1).2.1
  have ac : toffoliCount (accFoldQ4KTq L (eItem L))=1515 ∧ measurementCount (accFoldQ4KTq L (eItem L))=1555 :=
    ⟨by omega,by omega⟩
  have s1k : toffoliCount (eSubK L)=128 ∧ measurementCount (eSubK L)=129 := by
    have k := eSubK_counts L hw; exact ⟨by omega,by omega⟩
  have a1b : toffoliCount (eAddB L)=128 ∧ measurementCount (eAddB L)=129 := by
    have k := eAddB_counts L hw; exact ⟨by omega,by omega⟩
  have fw := wFwd_counts L hw
  have iv := wInv_counts L hw
  have au := eAddU_counts L hw
  have su := eSubU_counts L hw
  have pd := padM_counts L 571
  simp only [bBodyTq,wFoldTq,eFoldTq,wRestoreT,toffoliCount_append,measurementCount_append,q1.1,q1.2,q2.1,q2.2,
    wb.1,wb.2,wu.1,wu.2,wc.1,wc.2,s1k.1,s1k.2,a1b.1,a1b.2,fl.1,fl.2,ac.1,ac.2,fw.1,fw.2,iv.1,iv.2,au.1,au.2,
    su.1,su.2,pd.1,pd.2]
  exact ⟨trivial,trivial⟩


theorem aBody_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (aBodyTq L c)=3043 ∧ measurementCount (aBodyTq L c)=3077 := by
  have q1 := measuredFoldQ_countsTq L hw (negP L)
  have q2 := measuredFoldQ_countsTq L hw (rot128F L)
  have bc := CodexNarrowTail.build8_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_okLen L hw)
  rw [CodexNarrowTail.build8_eq] at bc
  have wb : toffoliCount (wBuild L)=387 ∧ measurementCount (wBuild L)=388 := bc.1
  have wu : toffoliCount (wUnbuild L)=358 ∧ measurementCount (wUnbuild L)=388 := bc.2
  have k := maskedConstant_counts c (accReg L) OwnDiagAll12Square.cFlipK
  have qc := QCore.qprog_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)
  simp only [aBodyTq,aFold8Tq,toffoliCount_append,measurementCount_append,q1.1,q1.2,q2.1,q2.2,wb.1,wb.2,wu.1,wu.2,
    k.1,k.2,qc.1,qc.2]
  constructor <;> norm_num


theorem bBody_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (hn : (c::L.wires).Nodup) : GatePhysical (bBodyTq L c) := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw := (List.nodup_cons.mp hn).1
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have p1 := measuredFoldQ_physicalTq L hw nd (negP L) sP
  have p2 := measuredFoldQ_physicalTq L hw nd (rot128F L) sR
  have wb := CodexNarrowTail.build8_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_fits L hw nd)
  rw [CodexNarrowTail.build8_eq] at wb
  have wc := QCore.qprog_physicalTq (rotWCore L) SquareReduction.p (rotWCore_nodup L nd)
  have adderNd (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      (L.core.cin::src++eReg L++eBank L).Nodup := by
    have h := eAdder_nodup L nd src hs
    simpa only [List.cons_append,List.append_assoc] using h
  have es (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) : GatePhysical (eSub L src) :=
    subInPlace_physical src (eReg L) (eBank L) L.core.cin (adderNd src hs)
  have ea (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) : GatePhysical (eAdd L src) :=
    addInPlace_physical src (eReg L) (eBank L) L.core.cin (adderNd src hs)
  have hct : c∉(eReg L).take 129 := fun hm => hcw (by
    have := eReg_product L c (List.mem_of_mem_take hm)
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this])
  have fl : GatePhysical (eFlip L c) := maskedConstant_physical c ((eReg L).take 129) (2^129-1) hct
  have st := eItem_static L hw
  have ac := Q4.accFoldQ4KTq_physical L hw nd (eItem L) st.1 st.2.1 st.2.2.1 st.2.2.2
  have g := mGeo L hw nd
  simp only [bBodyTq,wFoldTq,eFoldTq,wRestoreT,gatePhysical_append]
  exact ⟨p1,p2,⟨wb.1,⟨WinArith.tFwd_physical g,wc,WinArith.tInv_physical g⟩,wb.2,eSubK_physical L hw nd,
    eAddU_physical L nd⟩,⟨fl,ac,fl⟩,⟨eAddB_physical L hw nd,eSubU_physical L hw nd,padM_physical L 571⟩⟩


theorem aBody_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (hn : (c::L.wires).Nodup) : GatePhysical (aBodyTq L c) := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw := (List.nodup_cons.mp hn).1
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have p1 := measuredFoldQ_physicalTq L hw nd (negP L) sP
  have p2 := measuredFoldQ_physicalTq L hw nd (rot128F L) sR
  have wb := CodexNarrowTail.build8_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_fits L hw nd)
  rw [CodexNarrowTail.build8_eq] at wb
  have full := accFoldQ_physicalTq L hw nd (aAcc L) sA.1 sA.2.1 sA.2.2.1 sA.2.2.2
  simp only [accFoldQTq,gatePhysical_append] at full
  have mc := maskedConstant_physical c (accReg L) OwnDiagAll12Square.cFlipK
    (fun h => hcw (OwnDiagAll12Square.accReg_in L c h))
  simp only [aBodyTq,aFold8Tq,gatePhysical_append]
  exact ⟨p1,p2,wb.1,mc,full.1.2,mc,wb.2⟩


theorem aBody_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Challenge.gateSlots (aBodyTq L c)≤150000 := by
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have q1 := measuredFoldQ_gateSlotsTq L hw (negP L)
  have q2 := measuredFoldQ_gateSlotsTq L hw (rot128F L)
  have bs := CodexNarrowTail.build8_gateSlots (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_okLen L hw)
  rw [CodexNarrowTail.build8_eq] at bs
  have wb : Challenge.gateSlots (wBuild L)≤4*(14*163) := bs.1
  have wu : Challenge.gateSlots (wUnbuild L)≤4*(14*163) := bs.2
  have mc := Baselines.maskedConstant_gateSlots_le c (accReg L) OwnDiagAll12Square.cFlipK
  rw [(acc_lengths L hw).1] at mc
  have qs := QCore.qprog_gateSlotsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw)
  simp only [aBodyTq,aFold8Tq,Challenge.gateSlots_append]
  omega


end ECDSAAdd.Entrant.ControlLoan1589BFFold

/-! ### Support and gate-slot refinement: every `Tq` body uses a subset of the wires and no more
gate slots than the body it replaces. -/

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout RecordedQuantum

namespace QRel

/-- `P'` refines `P` statically: fewer wires and fewer gate slots. -/
def Le (P' P : Program) : Prop :=
  ECDSAAdd.wires P'⊆ECDSAAdd.wires P ∧ Challenge.gateSlots P'≤Challenge.gateSlots P

theorem Le.rfl' (P : Program) : Le P P := ⟨Finset.Subset.refl _,le_rfl⟩

theorem Le.app {A A' B B' : Program} (h1 : Le A' A) (h2 : Le B' B) : Le (A'++B') (A++B) :=
  ⟨by rw [wires_append,wires_append]; exact Finset.union_subset_union h1.1 h2.1,
   by rw [Challenge.gateSlots_append,Challenge.gateSlots_append]; exact Nat.add_le_add h1.2 h2.2⟩

theorem mappedConstant_snoc (c : Option Wire) (n : Nat) : ∀ k : Nat,
    mappedConstant c (n+1) k=mappedConstant c n k++[mappedConstantBit c (decide ((k/2^n)%2=1))] := by
  induction n with
  | zero => intro k; simp [mappedConstant]
  | succ n ih =>
    intro k
    show mappedConstantBit c (decide (k%2=1))::mappedConstant c (n+1) (k/2)=
      (mappedConstantBit c (decide (k%2=1))::mappedConstant c n (k/2))++_
    rw [ih (k/2),Nat.div_div_eq_div_mul,← pow_succ']
    rfl

theorem majority_slots_pos (b : MappedBit) (y c t : Wire) :
    1≤Challenge.gateSlots (mappedMajority b y c t) := by
  rcases b with ⟨_|a,_|_⟩ <;>
    simp [mappedMajority,majority,borrowMajority,Challenge.gateSlots,Challenge.instructionSlots]

theorem mappedAdd_snoc_le (b : MappedBit) (y : Wire) (xs : List MappedBit) : ∀ (ys cs : List Wire) (c : Wire),
    xs.length=ys.length → 0<xs.length → xs.length≤cs.length →
    ECDSAAdd.wires (mappedAdd xs ys (cs.take (xs.length-1)) c)⊆ECDSAAdd.wires (mappedAdd (xs++[b]) (ys++[y]) cs c) ∧
    Challenge.gateSlots (mappedAdd xs ys (cs.take (xs.length-1)) c)+1≤
      Challenge.gateSlots (mappedAdd (xs++[b]) (ys++[y]) cs c) := by
  induction xs with
  | nil => intro ys cs c _ h _; simp at h
  | cons x0 xs ih =>
    intro ys cs c hl _ hc
    rcases ys with _|⟨y0,ys⟩
    · simp at hl
    rcases cs with _|⟨d,ds⟩
    · simp at hc
    simp only [List.length_cons,Nat.add_right_cancel_iff] at hl hc
    rcases xs with _|⟨x1,xs⟩
    · rcases ys with _|⟨y1,ys⟩
      · have m1 := majority_slots_pos x0 y0 c d
        simp only [List.cons_append,List.nil_append,mappedAdd,List.length_cons,List.length_nil,
          Nat.sub_self,List.take_zero,wires_append,Challenge.gateSlots_append]
        refine ⟨fun q h => ?_,by omega⟩
        simp only [Finset.mem_union]; tauto
      · simp at hl
    · rcases ys with _|⟨y1,ys⟩
      · simp at hl
      · have h := ih (y1::ys) ds d (by simpa using hl) (by simp) (by simp at hc ⊢; omega)
        simp only [List.cons_append,List.length_cons,Nat.add_sub_cancel] at h ⊢
        simp only [List.take_succ_cons,mappedAdd,wires_append,Challenge.gateSlots_append]
        refine ⟨Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union
          (Finset.Subset.refl _) h.1) (Finset.Subset.refl _)) (Finset.Subset.refl _),by omega⟩

theorem const_le (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (hn : 0<n) :
    ECDSAAdd.wires (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p)⊆
      ECDSAAdd.wires (mappedConstAdd (some K.flag) K.extended K.carry K.cin p) ∧
    Challenge.gateSlots (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p)+1≤
      Challenge.gateSlots (mappedConstAdd (some K.flag) K.extended K.carry K.cin p) := by
  have h := mappedAdd_snoc_le (mappedConstantBit (some K.flag) (decide ((p/2^K.out.length)%2=1))) K.high
    (mappedConstant (some K.flag) K.out.length p) K.out K.carry K.cin
    (by simp [mappedConstant_length]) (by simp [mappedConstant_length,hw.out]; omega)
    (by simp [mappedConstant_length,hw.out,hw.carry])
  rw [mappedConstant_length] at h
  have e : mappedConstAdd (some K.flag) K.extended K.carry K.cin p=
      mappedAdd (mappedConstant (some K.flag) K.out.length p++
        [mappedConstantBit (some K.flag) (decide ((p/2^K.out.length)%2=1))]) (K.out++[K.high]) K.carry K.cin := by
    rw [← mappedConstant_snoc]; simp [mappedConstAdd,MeasuredCanonicalModLayout.extended]
  rw [e]; exact h

theorem le_core (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (hn : 0<n) (P1 P3 : Program) :
    Le (P1++([.CX K.high K.flag,.X K.flag]++
        (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p++([.CX K.flag K.high]++P3))))
      (P1++([.CX K.high K.flag,.X K.flag]++(mappedConstAdd (some K.flag) K.extended K.carry K.cin p++P3))) := by
  obtain ⟨hw',hs⟩ := const_le K n p hw hn
  constructor
  · intro q hq
    have hcx : q∈ECDSAAdd.wires [Instr.CX K.flag K.high] →
        q∈ECDSAAdd.wires [Instr.CX K.high K.flag,Instr.X K.flag] := by
      intro h; simp [ECDSAAdd.wires,Instr.wires] at h ⊢; tauto
    have hm : q∈ECDSAAdd.wires (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p) →
        q∈ECDSAAdd.wires (mappedConstAdd (some K.flag) K.extended K.carry K.cin p) := fun h => hw' h
    simp only [wires_append,Finset.mem_union] at hq ⊢
    tauto
  · simp only [Challenge.gateSlots_append]
    have : Challenge.gateSlots [Instr.CX K.flag K.high]=1 := rfl
    omega

theorem qprog_le (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (hn : 0<n) :
    Le (qprogTq K p) (qprog K p) := by
  have g := le_core K n p hw hn (notRegister K.out++K.sum)
    ([.X K.high,.X K.flag]++eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag)
  simpa only [qprogTq,qprog,List.append_assoc] using g

theorem qprog4_le (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (hn : 0<n) :
    Le (qprog4Tq K p) (qprog4 K p) := by
  have g := le_core K n p hw hn (notRegister K.out++Skip4.addSkip 4
      (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)]) K.extended K.carry K.cin)
    ([.X K.high,.X K.flag]++Skip4.eraseSkip 4 K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag)
  simpa only [qprog4Tq,qprog4,List.append_assoc] using g

theorem measuredFoldQ_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold) :
    Le (measuredFoldQTq L f) (measuredFoldQ L f) := by
  unfold measuredFoldQTq measuredFoldQ
  exact Le.app (Le.app (Le.rfl' _)
    (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide))) (Le.rfl' _)

theorem accFoldQ_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem) :
    Le (accFoldQTq L a) (accFoldQ L a) := by
  unfold accFoldQTq accFoldQ
  exact Le.app (Le.app (Le.rfl' _)
    (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide))) (Le.rfl' _)

theorem accFoldQ4_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem) :
    Le (accFoldQ4Tq L a) (accFoldQ4 L a) := by
  unfold accFoldQ4Tq accFoldQ4
  exact Le.app (Le.app (Le.rfl' _)
    (qprog4_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide))) (Le.rfl' _)

theorem accFoldQ4K_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem) :
    Le (accFoldQ4KTq L a) (CodexCKAccTail.accFoldQ4Tail L a) := by
  unfold accFoldQ4KTq CodexCKAccTail.accFoldQ4Tail
  exact Le.app (Le.app (Le.rfl' _)
    (qprog4_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide))) (Le.rfl' _)

theorem mixProgQ_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (i : MixItem) :
    Le (mixProgQTq L i) (mixProgQ L i) := by
  rcases i with f|a
  · by_cases h : f.canonical
    · simp only [mixProgQTq,mixProgQ,h,if_true]; exact measuredFoldQ_le L hw f
    · simp only [mixProgQTq,mixProgQ,h]; exact Le.rfl' _
  · exact accFoldQ_le L hw a

theorem mixFoldsQ_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (o : Bool) (items : List MixItem) :
    Le (mixFoldsQTq L o items) (mixFoldsQ L o items) := by
  induction items generalizing o with
  | nil => exact Le.rfl' _
  | cons i is ih =>
    simp only [mixFoldsQTq,mixFoldsQ]
    refine Le.app ?_ (ih _)
    rcases Decidable.em (o=mixNeg i) with h|h
    · rw [if_pos h,if_pos h]; exact Le.rfl' _
    · rw [if_neg h,if_neg h]; exact mixProgQ_le L hw i

theorem accFoldQF_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) (a : AccItem) :
    Le (OwnDiagAll12Square.accFoldQFTq L g a) (OwnDiagAll12Square.accFoldQF L g a) := by
  unfold OwnDiagAll12Square.accFoldQFTq OwnDiagAll12Square.accFoldQF
  exact Le.app (Le.rfl' _) (Le.app (Le.rfl' _) (Le.app
    (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)) (Le.rfl' _)))

theorem bodyC_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    Le (OwnDiagAll12Square.bodyCTq L g) (OwnDiagAll12Square.bodyC L g) := by
  unfold OwnDiagAll12Square.bodyCTq OwnDiagAll12Square.bodyC
  exact Le.app (mixFoldsQ_le L hw _ _) (accFoldQF_le L hw g _)

theorem accFoldQFK_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) (a : AccItem) :
    Le (OwnDiagAll12Square.accFoldQFKTq L g a) (CodexCKAccTail.accFoldQFTail L g a) := by
  unfold OwnDiagAll12Square.accFoldQFKTq CodexCKAccTail.accFoldQFTail
  exact Le.app (Le.rfl' _) (Le.app (Le.rfl' _) (Le.app
    (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)) (Le.rfl' _)))

theorem bodyCK_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    Le (OwnDiagAll12Square.bodyCKTq L g) (CodexCKAccTail.bodyCTail L g) := by
  unfold OwnDiagAll12Square.bodyCKTq CodexCKAccTail.bodyCTail
  exact Le.app (mixFoldsQ_le L hw _ _) (accFoldQFK_le L hw g _)

theorem eFold_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Le (ControlLoan1589BFFold.eFoldTq L c) (ControlLoan1589BFFold.eFold L c) := by
  unfold ControlLoan1589BFFold.eFoldTq ControlLoan1589BFFold.eFold
  exact Le.app (Le.rfl' _) (Le.app (accFoldQ4K_le L hw _) (Le.rfl' _))

open ControlLoan1589BFFold in
set_option maxRecDepth 400000 in
theorem bBody_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Le (bBodyTq L c) (bBody L c) := by
  unfold bBodyTq bBody
  refine Le.app (measuredFoldQ_le L hw _) (Le.app (measuredFoldQ_le L hw _) ⟨?_, ?_⟩)
  · have wc := (qprog_le (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)).1
    have ef := (eFold_le L hw c).1
    have sk := eSubK_wires L hw
    have ab := eAddB_wires L hw
    have f1 := wFwd_oldE L hw
    have f2 := wInv_oldE L hw
    have f3 := eAddU_oldE L hw
    have f4 := eSubU_oldE L hw
    have f5 := padM_oldE L hw 571
    have ml {A B : Program} {q : Wire} (h : q ∈ wires A) : q ∈ wires (A ++ B) := by
      rw [wires_append]; exact Finset.mem_union_left _ h
    have mr {A B : Program} {q : Wire} (h : q ∈ wires B) : q ∈ wires (A ++ B) := by
      rw [wires_append]; exact Finset.mem_union_right _ h
    have hOE {q : Wire} (h : q ∈ oldE L) : q ∈ wires (wFold L ++ (eFold L c ++ wRestore L)) := by
      rcases Finset.mem_union.mp h with h|h
      · exact ml (mr (mr (ml h)))
      · exact ml (mr (mr (mr (ml h))))
    intro q hq
    simp only [wFoldTq, wRestoreT, wires_append, Finset.mem_union] at hq
    rcases hq with (h | ((h | h | h) | h | h | h)) | h | h | h | h
    · exact ml (ml h)
    · exact hOE (f1 h)
    · exact ml (mr (ml (wc h)))
    · exact hOE (f2 h)
    · exact ml (mr (mr (mr (mr h))))
    · exact ml (mr (mr (ml (sk h))))
    · exact hOE (f3 h)
    · exact mr (ml (ef h))
    · exact mr (mr (mr (mr (ml (ab h)))))
    · exact hOE (f4 h)
    · exact hOE (f5 h)
  · have wc := (qprog_le (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)).2
    have ef := (eFold_le L hw c).2
    have sk := eSubK_slots L hw
    have ab := eAddB_slots L hw
    have f1 := WinArith.tFwd_slots (cin := L.core.cin) (mLens L hw)
    have f2 := WinArith.tInv_slots (cin := L.core.cin) (mLens L hw)
    have f3 := eAddU_slots L hw
    have f4 := eSubU_slots L hw
    have f5 := padM_slots L 571
    have g1 := wBuild_slots_ge L hw
    have g2 := wUnbuild_slots_ge L hw
    simp only [wFoldTq, wRestoreT, wFold, wRestore, wFwd, wInv, wCoreTq, wCore, Challenge.gateSlots_append] at *
    omega

theorem aBody_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Le (ControlLoan1589BFFold.aBodyTq L c) (ControlLoan1589BFFold.aBody L c) := by
  unfold ControlLoan1589BFFold.aBodyTq ControlLoan1589BFFold.aBody ControlLoan1589BFFold.aFold8Tq
    ControlLoan1589BFFold.aFold8
  exact Le.app (measuredFoldQ_le L hw _) (Le.app (measuredFoldQ_le L hw _)
    (Le.app (Le.rfl' _) (Le.app (Le.rfl' _) (Le.app
      (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)) (Le.rfl' _)))))

/-- Counts and static refinement of the three square bodies, as used by the square layers. -/
theorem bodyC_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (OwnDiagAll12Square.bodyCTq L g)+2=toffoliCount (OwnDiagAll12Square.bodyC L g) ∧
    measurementCount (OwnDiagAll12Square.bodyCTq L g)+2=measurementCount (OwnDiagAll12Square.bodyC L g) ∧
    Le (OwnDiagAll12Square.bodyCTq L g) (OwnDiagAll12Square.bodyC L g) := by
  have a := OwnDiagAll12Square.bodyC_countsTq L hw g
  have b := OwnDiagAll12Square.bodyC_counts L hw g
  exact ⟨by omega,by omega,bodyC_le L hw g⟩

theorem bodyCK_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (OwnDiagAll12Square.bodyCKTq L g)+2=toffoliCount (CodexCKAccTail.bodyCTail L g) ∧
    measurementCount (OwnDiagAll12Square.bodyCKTq L g)+2=measurementCount (CodexCKAccTail.bodyCTail L g) ∧
    Le (OwnDiagAll12Square.bodyCKTq L g) (CodexCKAccTail.bodyCTail L g) := by
  have a := OwnDiagAll12Square.bodyCK_countsTq L hw g
  have b := CodexCKAccTail.bodyCTail_counts L hw g
  exact ⟨by omega,by omega,bodyCK_le L hw g⟩

theorem bBody_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (ControlLoan1589BFFold.bBodyTq L c)+598=toffoliCount (ControlLoan1589BFFold.bBody L c) ∧
    measurementCount (ControlLoan1589BFFold.bBodyTq L c)+4=measurementCount (ControlLoan1589BFFold.bBody L c) ∧
    Le (ControlLoan1589BFFold.bBodyTq L c) (ControlLoan1589BFFold.bBody L c) := by
  have a := ControlLoan1589BFFold.bBody_countsTq L hw c
  have b := ControlLoan1589BFFold.bBody_counts L hw c
  exact ⟨by omega,by omega,bBody_le L hw c⟩

theorem aBody_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (ControlLoan1589BFFold.aBodyTq L c)+3=toffoliCount (ControlLoan1589BFFold.aBody L c) ∧
    measurementCount (ControlLoan1589BFFold.aBodyTq L c)+3=measurementCount (ControlLoan1589BFFold.aBody L c) ∧
    Le (ControlLoan1589BFFold.aBodyTq L c) (ControlLoan1589BFFold.aBody L c) := by
  have a := ControlLoan1589BFFold.aBody_countsTq L hw c
  have b := ControlLoan1589BFFold.aBody_counts L hw c
  exact ⟨by omega,by omega,aBody_le L hw c⟩

end QRel
end ECDSAAdd.Entrant

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem bBody_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) : ECDSAAdd.wires (bBodyTq L control)⊆(control::L.wires).toFinset :=
  (QRel.bBody_le L hw control).1.trans (bBody_support L hw hn control)

end ECDSAAdd.Entrant.ControlLoan1589BFFold

end
end
end
