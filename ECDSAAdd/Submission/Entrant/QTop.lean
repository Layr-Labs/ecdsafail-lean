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


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KnownSubDevelop
open Arithmetic MixedLiteralAdderDevelop

def knownSub (bits sums : List MappedBit) (ys cs : List Wire) (cin : Wire) : Program :=
  notRegister ys++Arithmetic.KnownOutputAdder.program bits ys sums cs cin++notRegister ys

theorem sub_eq (bits : List MappedBit) (sums : List MappedBit)
    (ys cs : List Wire) (cin : Wire) (hn : (cin::ys++cs).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::ys++cs)
    (hd : ∀q∈mappedWires sums,q∉cin::ys++cs)
    (hl : bits.length=ys.length) (hf : sums.length=ys.length) (hc : cs.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈cs,s.basis q=false)
    (ready : Arithmetic.KnownOutputAdder.Ready bits sums ys ((flipped ys s).basis cin) (flipped ys s).basis) :
    run (knownSub bits sums ys cs cin) m s=run (mappedSub bits ys cs cin) m s := by
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
  have mid (mm : List Bool) := Arithmetic.KnownOutputAdder.program_eq_mappedAdd bits sums ys cs cin
    hn ha hd hl hf hc (flipped ys s) mm clean ready
  have nc:=notRegister_counts ys
  have pc:=Arithmetic.KnownOutputAdder.program_counts bits sums ys cs cin hl hf hc
  have mc:=mappedAdd_counts bits ys cs cin hl hc
  rw [knownSub,mappedSub]
  simp only [List.append_assoc,run_append,run_take,nc.2,pc.2,mc.2,List.take_zero,List.drop_zero]
  rw [nt,mid]


#print axioms sub_eq
end ECDSAAdd.Entrant.KnownSubDevelop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KnownSubDevelop
open Arithmetic

theorem sub_counts (bits sums : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hf : sums.length=ys.length) (hc : cs.length+1=ys.length) :
    toffoliCount (knownSub bits sums ys cs cin)=0 ∧
    measurementCount (knownSub bits sums ys cs cin)=ys.length-1 := by
  have p:=KnownOutputAdder.program_counts bits sums ys cs cin hl hf hc
  have n:=notRegister_counts ys
  simp [knownSub,toffoliCount_append,measurementCount_append,p.1,p.2,n.1,n.2]

theorem sub_physical (bits sums : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hf : sums.length=ys.length) (hc : cs.length+1=ys.length)
    (hn : (cin::ys++cs).Nodup)
    (ha : ∀b∈bits,∀q∈b.wire,q∉cin::ys++cs)
    (hd : ∀b∈sums,∀q∈b.wire,q∉cin::ys++cs) :
    GatePhysical (knownSub bits sums ys cs cin) := by
  simp only [knownSub,gatePhysical_append]
  exact ⟨⟨notRegister_physical ys,KnownOutputAdder.program_physical bits sums ys cs cin hl hf hc hn ha hd⟩,
    notRegister_physical ys⟩

theorem sub_support (bits sums : List MappedBit) (ys cs : List Wire) (cin : Wire) :
    wires (knownSub bits sums ys cs cin)⊆(mappedWires bits++mappedWires sums++ys++cs++[cin]).toFinset := by
  have p:=KnownOutputAdder.program_support bits sums ys cs cin
  intro q hq
  simp only [knownSub,wires_append,notRegister_wires,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  · exact p h
  · simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto

theorem sub_slots (bits sums : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) : Challenge.gateSlots (knownSub bits sums ys cs cin)≤16*bits.length := by
  have p:=Win977Develop.known_slots bits sums ys cs cin
  simp only [knownSub,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
  omega
#print axioms sub_counts
#print axioms sub_physical
#print axioms sub_support
#print axioms sub_slots
end ECDSAAdd.Entrant.KnownSubDevelop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTail130Develop
open Arithmetic Arithmetic.KnownOutputAdder Arithmetic.CuccaroStreamedSquareWideLayout MixedLiteralAdderDevelop

abbrev one : MappedBit := ⟨none,true⟩
def negDesired (src : List Wire) : List MappedBit := mappedRead (src.drop 6) true++List.replicate 7 one
def program (src Z ys carry : List Wire) (cin : Wire) : Program :=
  KnownSubDevelop.knownSub (mappedRead (src++Z.take 1) false) (negDesired src) ys carry cin

theorem neg_value (src : List Wire) (s : BasisState) (hs : src.length=130) :
    mappedValue (negDesired src) s=2^131-1-regValue src s/64 := by
  rw [negDesired,mappedValue_append,mappedRead_complement,
    regValue_drop_div src 6 (by omega)]
  simp only [mappedRead,List.length_map,List.length_drop,hs]
  norm_num [one,MappedBit.value,mappedValue,List.replicate_succ]
  have h:=regValue_lt src s
  rw [hs] at h
  omega

theorem neg_wires (src : List Wire) : mappedWires (negDesired src)=src.drop 6 := by
  have app (a b : List MappedBit) : mappedWires (a++b)=mappedWires a++mappedWires b := by simp [mappedWires,List.flatMap_append]
  rw [negDesired,app,mappedRead_wires]
  simp [mappedWires,one,List.flatMap_replicate]

theorem arithmetic (H : Nat) (hH : H<2^130) :
    (H+(2^131-1-1040*H/1024))%2^131=2^131-1-H/64 := by
  have eq : 1040*H/1024=H+H/64 := by omega
  rw [eq]
  omega

theorem run_eq_sub (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=130) (hzl : 1≤Z.length) (hy : ys.length=131) (hc : carry.length=130)
    (hn : (cin::((src++Z.take 1)++ys++carry)).Nodup)
    (s : State) (m : List Bool) (hz : ∀q∈Z,s.basis q=false)
    (hcarry : ∀q∈carry,s.basis q=false) (hcin : s.basis cin=false)
    (H : Nat) (hH : H<2^130) (hsrc : regValue src s.basis=H)
    (hys : regValue ys s.basis=1040*H/1024) :
    run (program src Z ys carry cin) m s=run (subInPlace (src++Z.take 1) ys carry cin) m s := by
  have geo:=read_geometry (src++Z.take 1) ys carry cin hn
  have outside (q : Wire) (hq : q∈src++Z.take 1) : q∉ys := by
    intro bad
    exact geo.2 q hq (List.mem_cons_of_mem _ (List.mem_append_left _ bad))
  have srcAway (q : Wire) (hq : q∈src) : q∉ys := outside q (List.mem_append_left _ hq)
  have caway : cin∉ys := by intro bad;exact (List.nodup_cons.mp geo.1).1 (List.mem_append_left _ bad)
  have zv : regValue (Z.take 1) s.basis=0 := (regValue_zero _ _).mpr (fun q hq=>hz q (List.mem_of_mem_take hq))
  have sv : mappedValue (mappedRead (src++Z.take 1) false) (flipped ys s).basis=H := by
    rw [mappedRead_value,regValue_congr (src++Z.take 1) _ s.basis
      (by intro q hq;simp only [flipped,if_neg (outside q hq)]),regValue_append,hsrc,zv,Nat.mul_zero,Nat.add_zero]
  have dv : mappedValue (negDesired src) (flipped ys s).basis=2^131-1-H/64 := by
    rw [neg_value src _ hs,regValue_congr src _ s.basis
      (by intro q hq;simp only [flipped,if_neg (srcAway q hq)]),hsrc]
  have yv : regValue ys (flipped ys s).basis=2^131-1-1040*H/1024 := by
    rw [regValue_congr ys _ (fun q=>!s.basis q) (by intro q hq;simp only [flipped,if_pos hq]),
      regValue_complement,hy,hys]
  have hl : (mappedRead (src++Z.take 1) false).length=ys.length := by simp [mappedRead,hs,hy];omega
  have hd : (negDesired src).length=ys.length := by simp [negDesired,mappedRead,hs,hy]
  have ready : KnownOutputAdder.Ready (mappedRead (src++Z.take 1) false) (negDesired src) ys
      ((flipped ys s).basis cin) (flipped ys s).basis := by
    apply ready_of_value _ _ _ _ _ hl hd
    rw [sv,dv,yv,show (flipped ys s).basis cin=false by simp only [flipped,if_neg caway,hcin],
      Bool.toNat_false,Nat.add_zero,hy]
    exact (arithmetic H hH).symm
  have eq:=KnownSubDevelop.sub_eq (mappedRead (src++Z.take 1) false) (negDesired src) ys carry cin geo.1
    (by rw [mappedRead_wires];exact geo.2)
    (by rw [neg_wires];intro q hq;exact geo.2 q (List.mem_append_left _ (List.mem_of_mem_drop hq)))
    hl hd (by rw [hc,hy]) s m hcarry ready
  exact eq.trans (congrArg (fun p=>run p m s) (read_sub_eq _ _ _ _))
#print axioms neg_value
#print axioms arithmetic
#print axioms run_eq_sub
end ECDSAAdd.Entrant.SourceTail130Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTail130Develop
open Arithmetic

def tail (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  program src Z ((acc.take 141).drop 10) (bank.take 130) cin

theorem tail_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=130)
    (hf : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 10))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (1040*regValue src base)) (tail acc Z bank cin src)
      (SquareFrame acc base (16*regValue src base)) := by
  let f:=Acc.earlyTerm src false 10
  let H:=regValue src base
  have hH : H<2^130 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have old:=Acc.op_prefix_triple acc Z bank cin 163 141 f hacc (by decide) hf
    (by simp [f,Acc.earlyTerm,hsrc]) base hz hb hi true (1040*H)
    (by omega) (by simp only [f,Acc.earlyTerm];dsimp [H];omega)
  have value : Acc.step base true (1040*H) f=16*H := by
    norm_num [Acc.step,f,Acc.earlyTerm]
    dsimp [H]
    omega
  rw [value] at old
  have fit:=Acc.fits_prefix acc Z bank cin 163 141 f (by decide) hf (by simp [f,Acc.earlyTerm,hsrc])
  have len : (acc.take 141).length=141 := by simp [hacc]
  have rawEq : Acc.op (acc.take 141) Z bank cin 141 true f=
      subInPlace (src++Z.take 1) ((acc.take 141).drop 10) (bank.take 130) cin := by
    simp [Acc.op,Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc]
  intro s m hs
  have away (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h:=List.nodup_iff_count.mp hf.nd q
    have a:=List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b:=List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
      omega
  have same (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : s.basis q=base q := hs.2 q (away q hq)
  have pref:=regValue_take_drop_of_lt acc 141 (1040*H) s.basis (by omega) hs.1 (by omega)
  have sy : regValue ((acc.take 141).drop 10) s.basis=1040*H/1024 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
    rfl
  have sh : regValue src s.basis=H := regValue_congr src _ base (fun q hq=>same q (Or.inl (by simp [hq])))
  have sz (q : Wire) (hq : q∈Z) : s.basis q=false :=
    (same q (Or.inl (by simp [hq]))).trans (hz q hq)
  have sb (q : Wire) (hq : q∈bank.take 130) : s.basis q=false :=
    (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
  have si : s.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have nd:=Acc.fits_nodup (acc.take 141) Z bank cin 141 f fit
  have nd' : (cin::((src++Z.take 1)++(acc.take 141).drop 10++bank.take 130)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd
  have zl : 1≤Z.length := by
    have h:=fit.zpad
    simpa [f,Acc.earlyTerm,hsrc] using h
  have bl : (bank.take 130).length=130 := by
    have h:=fit.bankLen
    simp only [f,Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have e:=run_eq_sub src Z ((acc.take 141).drop 10) (bank.take 130) cin hsrc zl
    (by simp [len]) bl nd' s m sz sb si H hH sh sy
  change run (tail acc Z bank cin src) m s=_ at e
  rw [e,←rawEq]
  exact old s m hs
#print axioms tail_triple
end ECDSAAdd.Entrant.SourceTail130Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTail130Develop
open Arithmetic Arithmetic.KnownOutputAdder

theorem prepare_read_slots (a : Wire) (desired : MappedBit) (y c : Wire) :
    Challenge.gateSlots (prepare ⟨some a,false⟩ desired y c)≤4 := by
  cases desired with
  | mk w flip => cases w <;> cases flip <;>
    simp [prepare,xorBit,Challenge.gateSlots,Challenge.instructionSlots]

theorem slots_read (bits sums : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (hRead : ∀b∈bits,∃a,b=({wire:=some a,flip:=false} : MappedBit)) :
    Challenge.gateSlots (KnownOutputAdder.program bits ys sums cs cin)≤10*bits.length := by
  revert hRead
  induction bits,ys,sums,cs,cin using KnownOutputAdder.program.induct with
  | case1 b b' bs y y' ys d d' ds c cs cin ih =>
    intro hb
    have ht : ∀z∈b'::bs,∃a,z=({wire:=some a,flip:=false} : MappedBit) :=
      fun z hz=>hb z (List.mem_cons_of_mem _ hz)
    have it:=ih ht
    obtain ⟨a,rfl⟩:=hb b (by simp)
    obtain ⟨a',rfl⟩:=hb b' (by simp)
    have hp:=prepare_read_slots a' d' y' c
    have he : Challenge.gateSlots (mappedEraseCarry ⟨some a,false⟩ y cin c)=4 := rfl
    have hs : Challenge.gateSlots (mappedSum ⟨some a,false⟩ y cin)=2 := rfl
    simp only [KnownOutputAdder.program,Challenge.gateSlots_append,List.length_cons] at it ⊢
    omega
  | case2 b y d cs cin =>
    intro hb
    obtain ⟨a,rfl⟩:=hb b (by simp)
    simp [KnownOutputAdder.program,mappedSum,Challenge.gateSlots,Challenge.instructionSlots]
  | case3 bits ys sums cs cin other => intro hb;simp [KnownOutputAdder.program]

theorem slots_read_raw (xs ys : List Wire) (sums : List MappedBit) (cs : List Wire) (cin : Wire) :
    Challenge.gateSlots (KnownOutputAdder.program (mappedRead xs false) ys sums cs cin)≤10*xs.length := by
  have h:=slots_read (mappedRead xs false) sums ys cs cin (by
    intro b hb
    change b∈xs.map (fun q=>({wire:=some q,flip:=false} : MappedBit)) at hb
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
    exact ⟨a,rfl⟩)
  simpa [mappedRead] using h

theorem program_slots (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=130) (hz : 1≤Z.length) (hy : ys.length=131) :
    Challenge.gateSlots (program src Z ys carry cin)≤1572 := by
  have hp:=slots_read_raw (src++Z.take 1) ys (negDesired src) carry cin
  have hx : (src++Z.take 1).length=131 := by simp [hs];omega
  rw [hx] at hp
  simp only [program,KnownSubDevelop.knownSub,Challenge.gateSlots_append,Baselines.notRegister_gateSlots,hy]
  omega
#print axioms slots_read
#print axioms program_slots
end ECDSAAdd.Entrant.SourceTail130Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTail130Develop
open Arithmetic

private theorem old_head_relation (low : Nat) (a a' b b' cin c : Wire) :
    Challenge.gateSlots (CodexKnownOnesTail.head low a a' b b' cin c)=
      3*toffoliCount (CodexKnownOnesTail.head low a a' b b' cin c)+3 ∧
    measurementCount (CodexKnownOnesTail.head low a a' b b' cin c)=0 := by
  by_cases h : low≤1 <;>
    simp [CodexKnownOnesTail.head,h,majority,Challenge.gateSlots,Challenge.instructionSlots,toffoliCount,measurementCount]

theorem old_add_relation (low : Nat) (x y carry : List Wire) (cin : Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    Challenge.gateSlots (CodexKnownOnesTail.addTail low x y carry cin)=
      3*toffoliCount (CodexKnownOnesTail.addTail low x y carry cin)+
      9*measurementCount (CodexKnownOnesTail.addTail low x y carry cin)+2 := by
  induction y generalizing low x carry cin with
  | nil => simp at hc
  | cons b ys ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
      cases ys with
      | nil =>
        cases as with
        | nil => simp [CodexKnownOnesTail.addTail,Challenge.gateSlots,Challenge.instructionSlots,toffoliCount,measurementCount]
        | cons a' as => simp at hx
      | cons b' ys =>
        cases as with
        | nil => simp at hx
        | cons a' as =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have it:=ih (low:=low-1) (x:=a'::as) (carry:=cs) (cin:=c)
              (by simp only [List.length_cons] at hx ⊢;omega)
              (by simp only [List.length_cons] at hc ⊢;omega)
            have hd:=old_head_relation low a a' b b' cin c
            have et : toffoliCount (eraseCarry a b cin c)=0 := rfl
            have em : measurementCount (eraseCarry a b cin c)=1 := rfl
            have es : Challenge.gateSlots (eraseCarry a b cin c)=4 := rfl
            have st : toffoliCount [.CX a b,.CX cin b]=0 := rfl
            have sm : measurementCount [.CX a b,.CX cin b]=0 := rfl
            have ss : Challenge.gateSlots [.CX a b,.CX cin b]=2 := rfl
            simp only [CodexKnownOnesTail.addTail,Challenge.gateSlots_append,toffoliCount_append,
              measurementCount_append,hd.2,et,em,es,st,sm,ss]
            omega

theorem old_program_relation (low : Nat) (x y carry : List Wire) (cin : Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    Challenge.gateSlots (CodexKnownOnesTail.program low x y carry cin)=
      3*toffoliCount (CodexKnownOnesTail.program low x y carry cin)+
      9*measurementCount (CodexKnownOnesTail.program low x y carry cin)+2+2*y.length := by
  have h:=old_add_relation low x y carry cin hx hc
  have n:=notRegister_counts y
  simp only [CodexKnownOnesTail.program,Challenge.gateSlots_append,Baselines.notRegister_gateSlots,
    toffoliCount_append,measurementCount_append,n.1,n.2,Nat.zero_add,Nat.add_zero]
  omega

theorem old_program_slots131 (x y carry : List Wire) (cin : Wire)
    (hy : y.length=131) (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    Challenge.gateSlots (CodexKnownOnesTail.program 124 x y carry cin)=1803 := by
  have h:=old_program_relation 124 x y carry cin hx hc
  have count:=CodexKnownOnesTail.counts 129 124 x y carry cin (by rw [hy]) hx hc
  rw [count.1,count.2,hy] at h
  norm_num at h
  exact h
#print axioms old_add_relation
#print axioms old_program_slots131
end ECDSAAdd.Entrant.SourceTail130Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTail130Develop
open Arithmetic

theorem old_add_wires (low : Nat) (x y carry : List Wire) (cin : Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    wires (CodexKnownOnesTail.addTail low x y carry cin)=(cin::(x++y++carry)).toFinset := by
  induction y generalizing low x carry cin with
  | nil => simp at hc
  | cons b ys ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
      cases ys with
      | nil =>
        cases as with
        | nil =>
          have cn : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
          subst carry
          ext q
          simp [CodexKnownOnesTail.addTail,wires,Instr.wires]
        | cons a' as => simp at hx
      | cons b' ys =>
        cases as with
        | nil => simp at hx
        | cons a' as =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have it:=ih (low:=low-1) (x:=a'::as) (carry:=cs) (cin:=c)
              (by simp only [List.length_cons] at hx ⊢;omega)
              (by simp only [List.length_cons] at hc ⊢;omega)
            rw [CodexKnownOnesTail.addTail]
            simp only [wires_append,it]
            ext q
            by_cases h : low≤1 <;>
              simp [CodexKnownOnesTail.head,h,majority,eraseCarry,wires,Instr.wires,correctionWires] <;> tauto

theorem old_program_wires (low : Nat) (x y carry : List Wire) (cin : Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    wires (CodexKnownOnesTail.program low x y carry cin)=(cin::(x++y++carry)).toFinset := by
  rw [CodexKnownOnesTail.program,wires_append,wires_append,notRegister_wires,
    old_add_wires low x y carry cin hx hc]
  ext q
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto
#print axioms old_add_wires
#print axioms old_program_wires
end ECDSAAdd.Entrant.SourceTail130Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTail130Develop
open Arithmetic Arithmetic.KnownOutputAdder

theorem word_length (src Z : List Wire) (hs : src.length=130) (hz : 1≤Z.length) :
    (src++Z.take 1).length=131 := by simp [hs];omega

theorem program_counts (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=130) (hz : 1≤Z.length) (hy : ys.length=131) (hc : carry.length=130) :
    toffoliCount (program src Z ys carry cin)=0 ∧ measurementCount (program src Z ys carry cin)=130 := by
  have p:=KnownSubDevelop.sub_counts (mappedRead (src++Z.take 1) false) (negDesired src) ys carry cin
    (by rw [mappedRead_length,word_length src Z hs hz,hy])
    (by simp [negDesired,mappedRead,hs,hy]) (by rw [hc,hy])
  simpa [program,hy] using p

private theorem bit_member (bits : List MappedBit) (b : MappedBit) (hb : b∈bits)
    (q : Wire) (hq : q∈b.wire) : q∈mappedWires bits := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩

theorem program_physical (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=130) (hz : 1≤Z.length) (hy : ys.length=131) (hc : carry.length=130)
    (hn : (cin::((src++Z.take 1)++ys++carry)).Nodup) : GatePhysical (program src Z ys carry cin) := by
  have g:=MixedLiteralAdderDevelop.read_geometry (src++Z.take 1) ys carry cin hn
  apply KnownSubDevelop.sub_physical _ _ _ _ _
    (by rw [mappedRead_length,word_length src Z hs hz,hy])
    (by simp [negDesired,mappedRead,hs,hy]) (by rw [hc,hy]) g.1
  · intro b hb q hq
    have mem:=bit_member (mappedRead (src++Z.take 1) false) b hb q hq
    rw [mappedRead_wires] at mem
    exact g.2 q mem
  · intro b hb q hq
    have mem:=bit_member (negDesired src) b hb q hq
    rw [neg_wires] at mem
    exact g.2 q (List.mem_append_left _ (List.mem_of_mem_drop mem))

theorem program_support_old (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=130) (hz : 1≤Z.length) (hy : ys.length=131) (hc : carry.length=130) :
    wires (program src Z ys carry cin)⊆wires (CodexKnownOnesTail.program 124 (src++Z.take 1) ys carry cin) := by
  rw [old_program_wires 124 _ _ _ _ (by rw [word_length src Z hs hz,hy]) (by rw [hc,hy])]
  have p:=KnownSubDevelop.sub_support (mappedRead (src++Z.take 1) false) (negDesired src) ys carry cin
  rw [mappedRead_wires,neg_wires] at p
  intro q hq
  have mem:=p hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at mem ⊢
  rcases mem with h|h|h|h|h|h
  · tauto
  · tauto
  · have old:=List.mem_of_mem_drop h
    tauto
  · tauto
  · tauto
  · tauto

theorem program_slots_old (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=130) (hz : 1≤Z.length) (hy : ys.length=131) (hc : carry.length=130) :
    Challenge.gateSlots (program src Z ys carry cin)≤
      Challenge.gateSlots (CodexKnownOnesTail.program 124 (src++Z.take 1) ys carry cin) := by
  rw [old_program_slots131 _ _ _ _ hy (by rw [word_length src Z hs hz,hy]) (by rw [hc,hy])]
  exact (program_slots src Z ys carry cin hs hz hy).trans (by decide : 1572≤1803)

theorem program_resources (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=130) (hz : 1≤Z.length) (hy : ys.length=131) (hc : carry.length=130) :
    toffoliCount (program src Z ys carry cin)+123=toffoliCount (CodexKnownOnesTail.program 124 (src++Z.take 1) ys carry cin) ∧
    measurementCount (program src Z ys carry cin)=measurementCount (CodexKnownOnesTail.program 124 (src++Z.take 1) ys carry cin) ∧
    wires (program src Z ys carry cin)⊆wires (CodexKnownOnesTail.program 124 (src++Z.take 1) ys carry cin) ∧
    Challenge.gateSlots (program src Z ys carry cin)≤Challenge.gateSlots (CodexKnownOnesTail.program 124 (src++Z.take 1) ys carry cin) := by
  have a:=program_counts src Z ys carry cin hs hz hy hc
  have b:=CodexKnownOnesTail.counts 129 124 (src++Z.take 1) ys carry cin (by rw [hy])
    (by rw [word_length src Z hs hz,hy]) (by rw [hc,hy])
  refine ⟨?_,?_,program_support_old src Z ys carry cin hs hz hy hc,program_slots_old src Z ys carry cin hs hz hy hc⟩
  · rw [a.1,b.1]
    rfl
  · rw [a.2,b.2]
#print axioms program_counts
#print axioms program_physical
#print axioms program_resources
end ECDSAAdd.Entrant.SourceTail130Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTail130Develop
open Arithmetic CodexNarrowTail
theorem tail_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=130)
    (hf : Acc.FitsLen Z bank 163 (Acc.earlyTerm src false 10)) :
    toffoliCount (tail acc Z bank cin src)+123=
      toffoliCount (CodexKnownOnesTail.accSub 124 (acc.take 141) Z bank cin 141 (Acc.earlyTerm src false 10)) ∧
    measurementCount (tail acc Z bank cin src)=
      measurementCount (CodexKnownOnesTail.accSub 124 (acc.take 141) Z bank cin 141 (Acc.earlyTerm src false 10)) ∧
    wires (tail acc Z bank cin src)⊆
      wires (CodexKnownOnesTail.accSub 124 (acc.take 141) Z bank cin 141 (Acc.earlyTerm src false 10)) ∧
    Challenge.gateSlots (tail acc Z bank cin src)≤
      Challenge.gateSlots (CodexKnownOnesTail.accSub 124 (acc.take 141) Z bank cin 141 (Acc.earlyTerm src false 10)) := by
  have fit:=CodexNarrowTail.narrowLen Z bank 141 (Acc.earlyTerm src false 10) hf (by decide)
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 1≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 130).length=130 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have h:=program_resources src Z ((acc.take 141).drop 10) (bank.take 130) cin hsrc zl
    (by simp [hacc]) bl
  simpa [tail,CodexKnownOnesTail.accSub,Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using h

theorem tail_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=130)
    (hf : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 10)) :
    GatePhysical (tail acc Z bank cin src) := by
  have fit:=Acc.fits_prefix acc Z bank cin 163 141 (Acc.earlyTerm src false 10) (by decide) hf
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 1≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 130).length=130 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have nd:=Acc.fits_nodup (acc.take 141) Z bank cin 141 (Acc.earlyTerm src false 10) fit
  have nd' : (cin::((src++Z.take 1)++(acc.take 141).drop 10++bank.take 130)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using nd
  exact program_physical src Z ((acc.take 141).drop 10) (bank.take 130) cin hsrc zl (by simp [hacc]) bl nd'


#print axioms tail_resources
#print axioms tail_physical
end ECDSAAdd.Entrant.SourceTail130Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourcePrefix130Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def clearPrefix (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  Acc.op (acc.take 141) Z bank cin 141 false (Acc.earlyTerm src true 6)++
    SourceTail130Develop.tail acc Z bank cin src++Acc.seedOp acc Z 163 (Acc.earlyTerm src false 4)

theorem prefix_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=130)
    (hf4 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 4))
    (hf10 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 10))
    (hf6 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src true 6))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (976*regValue src base)) (clearPrefix acc Z bank cin src)
      (SquareFrame acc base 0) := by
  have hH : regValue src base<2^130 :=
    lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) (by omega))
  generalize hHd : regValue src base = H at hH
  have add : Triple (SquareFrame acc base (976*H))
      (Acc.op (acc.take 141) Z bank cin 141 false (Acc.earlyTerm src true 6))
      (SquareFrame acc base (1040*H)) := by
    have h := Acc.op_prefix_triple acc Z bank cin 163 141 (Acc.earlyTerm src true 6) hacc
      (by decide) hf6 (by simp only [Acc.earlyTerm]; omega) base hz hb hi false (976*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm,hHd] at hH ⊢;omega)
    have value : Acc.step base false (976*H) (Acc.earlyTerm src true 6)=1040*H := by
      norm_num [Acc.step,Acc.earlyTerm,hHd]
      omega
    rw [value] at h
    exact h
  have sub : Triple (SquareFrame acc base (1040*H))
      (SourceTail130Develop.tail acc Z bank cin src)
      (SquareFrame acc base (16*H)) := by
    simpa only [hHd] using SourceTail130Develop.tail_triple acc Z bank cin src hacc hsrc hf10 base hz hb hi
  have seed := Acc.seed_triple acc Z bank cin 163 (Acc.earlyTerm src false 4) hacc hf4 base hz
    (16*H) 0 (Or.inr (by simp [Acc.earlyTerm,hHd,Nat.mul_comm]))
  exact (add.seq sub).seq seed


#print axioms prefix_triple
end ECDSAAdd.Entrant.SourcePrefix130Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.SourcePrefix130Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout CodexCKAccTail OwnDiagAll12Square CKAcc

def prefixAny (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  if src.length=130 then clearPrefix acc Z bank cin src else earlyPrefixClearTail acc Z bank cin src

theorem prefixAny_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length≤130)
    (hf4 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 4))
    (hf10 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 10))
    (hf6 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src true 6))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (976*regValue src base)) (prefixAny acc Z bank cin src)
      (SquareFrame acc base 0) := by
  by_cases h : src.length=130
  · simpa only [prefixAny,if_pos h] using prefix_triple acc Z bank cin src hacc h hf4 hf10 hf6 base hz hb hi
  · simpa only [prefixAny,if_neg h] using earlyPrefixClearTail_triple acc Z bank cin src hacc hsrc hf4 hf10 hf6 base hz hb hi

def earlyUnbuildKnown (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | a::_::_::tail => unbuildTail acc Z bank cin w a.src tail++prefixAny acc Z bank cin a.src
  | _ => []
def sunbuildKnown (acc Z bank : List Wire) (cin : Wire) (w : Nat) (fs : List MeasuredSquareFold) : Program :=
  if Acc.EarlyH w fs then earlyUnbuildKnown acc Z bank cin w fs else Acc.baseUnbuild acc Z bank cin w fs

theorem sunbuildKnown_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Acc.Fits acc Z bank cin w f) (hv : Acc.Valid base w 0 fs) :
    Triple (SquareFrame acc base (Acc.accVal base 0 fs)) (sunbuildKnown acc Z bank cin w fs)
      (SquareFrame acc base 0) := by
  by_cases h : Acc.EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩ := Acc.earlyH_info w fs h
    have hf4 := hf (Acc.earlyTerm src false 4) (by simp)
    have hf10 := hf (Acc.earlyTerm src false 10) (by simp)
    have hf6 := hf (Acc.earlyTerm src true 6) (by simp)
    have vt := hv.2.2.2
    change Acc.Valid base 163
      (Acc.step base true (Acc.step base false (Acc.step base false 0 (Acc.earlyTerm src false 4))
        (Acc.earlyTerm src false 10)) (Acc.earlyTerm src true 6)) tail at vt
    rw [Acc.early_steps] at vt
    have rest := unbuildTail_triple acc Z bank cin src hacc hlen base hz hb hi tail
      (fun f hf' => hf f (by simp [hf'])) vt
    have head := prefixAny_triple acc Z bank cin src hacc hlen hf4 hf10 hf6 base hz hb hi
    rw [sunbuildKnown,if_pos h,earlyUnbuildKnown]
    simpa only [Acc.accVal,Acc.earlyTerm_src,Acc.earlyTerm_negative,Acc.early_steps] using rest.seq head
  · simpa only [sunbuildKnown,if_neg h] using Acc.baseUnbuild_triple acc Z bank cin w hacc base hz hb hi fs hf hv

def fillOutKnown (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  tempIn L a++(splitIn L a++sunbuildKnown (accReg L) (accZ L) (accBank L) L.core.cin 163 a.terms++splitOut L a)++
    tempOut L a

theorem fillOutKnown_triple (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (a : AccItem) (hv : AccView L base a)
    (b : BasisState) (agree : ∀q∈L.core.product,b q=base q)
    (hz : ∀q∈accZ L,b q=false) (hb : ∀q∈accBank L,b q=false) (hi : b L.core.cin=false)
    (hW : ∀q∈wTemp L,b q=false) :
    Triple (SquareFrame (accReg L) b (Acc.accVal base 0 a.spec)) (fillOutKnown L a)
      (SquareFrame (accReg L) b 0) := by
  have lens := acc_lengths L hw
  have fits (f : MeasuredSquareFold) (hf : f∈a.terms) := fits_of L hw hn f (hv.count f hf) (hv.ok f hf)
  apply fill_core L hw hn base a hv b agree hz hb hi hW
  intro t ht hwv tz tb tc
  by_cases hp : a.pre=[]
  · simp only [splitIn,splitOut,if_pos hp,List.nil_append,List.append_nil]
    have val := hv.value t (fun q hq _ => ht q hq)
      (by rw [if_pos hp,Nat.add_zero]; exact regValue_congr _ _ _ (fun q hq => ht q (hiReg_product L q hq))) hwv
    have tr := sunbuildKnown_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 lens.1 t tz tb tc a.terms fits val.1
    rwa [val.2] at tr
  · simp only [splitIn,splitOut,hp,if_false]
    have hH : regValue (hiReg L) t=regValue (hiReg L) base :=
      regValue_congr _ _ _ (fun q hq => ht q (hiReg_product L q hq))
    apply split_mid L hw hn t (Acc.accVal base 0 a.pre) (regValue (hiReg L) base) hv.hiLe hH hwv tz tb tc
    intro u hu hval
    have uprod : ∀q∈L.core.product,q∉hiReg L → u q=base q :=
      fun q hq hh => (hu q hh (product_away L hn q hq).1).trans (ht q hq)
    have val := hv.value u uprod (by simpa only [hp,if_false] using hval)
      ((regValue_congr _ _ _ (fun q hq => hu q (wTemp_not_hi L hn q hq)
        (fun b => acc_temp_disjoint L hn q b hq))).trans hwv)
    have uz : ∀q∈accZ L,u q=false := fun q hq => (hu q (accZ_not_hi L hn q hq) (accZ_away L hn q hq).1).trans (tz q hq)
    have ub : ∀q∈accBank L,u q=false :=
      fun q hq => (hu q (accBank_not_hi L hn q hq) (accBank_away L hn q hq).1).trans (tb q hq)
    have uc : u L.core.cin=false := (hu _ (cin_not_hi L hn) (cin_away L hn).1).trans tc
    have tr := sunbuildKnown_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 lens.1 u uz ub uc a.terms fits val.1
    rwa [val.2] at tr

#print axioms fillOutKnown_triple
end ECDSAAdd.Entrant.SourcePrefix130Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.SourcePrefix130Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout CodexCKAccTail OwnDiagAll12Square CKAcc

def gain (src : List Wire) : Nat := if src.length=130 then 123 else 0

theorem prefix_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=130)
    (hf : Acc.FitsLen Z bank 163 (Acc.earlyTerm src false 10)) :
    toffoliCount (clearPrefix acc Z bank cin src)+123=toffoliCount (earlyPrefixClearTail acc Z bank cin src) ∧
    measurementCount (clearPrefix acc Z bank cin src)=measurementCount (earlyPrefixClearTail acc Z bank cin src) ∧
    wires (clearPrefix acc Z bank cin src)⊆wires (earlyPrefixClearTail acc Z bank cin src) ∧
    Challenge.gateSlots (clearPrefix acc Z bank cin src)≤Challenge.gateSlots (earlyPrefixClearTail acc Z bank cin src) := by
  have h:=SourceTail130Develop.tail_resources acc Z bank cin src hacc hsrc hf
  simp only [clearPrefix,earlyPrefixClearTail,toffoliCount_append,measurementCount_append,wires_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h.2.2.1) (Finset.Subset.refl _),by omega⟩

theorem prefixAny_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hf : Acc.FitsLen Z bank 163 (Acc.earlyTerm src false 10)) :
    toffoliCount (prefixAny acc Z bank cin src)+gain src=toffoliCount (earlyPrefixClearTail acc Z bank cin src) ∧
    measurementCount (prefixAny acc Z bank cin src)=measurementCount (earlyPrefixClearTail acc Z bank cin src) ∧
    wires (prefixAny acc Z bank cin src)⊆wires (earlyPrefixClearTail acc Z bank cin src) ∧
    Challenge.gateSlots (prefixAny acc Z bank cin src)≤Challenge.gateSlots (earlyPrefixClearTail acc Z bank cin src) := by
  by_cases h : src.length=130
  · simpa only [prefixAny,gain,if_pos h] using prefix_resources acc Z bank cin src hacc h hf
  · simp only [prefixAny,gain,if_neg h,Nat.add_zero]
    exact ⟨trivial,trivial,Finset.Subset.refl _,le_rfl⟩

def totalGain (w : Nat) (fs : List MeasuredSquareFold) : Nat :=
  if Acc.EarlyH w fs then match fs with | a::_ => gain a.src | [] => 0 else 0

theorem sunbuild_resources (acc Z bank : List Wire) (cin : Wire) (w : Nat)
    (hacc : acc.length=w) (fs : List MeasuredSquareFold) (hz : 154≤Z.length) (hb : 160≤bank.length) :
    toffoliCount (sunbuildKnown acc Z bank cin w fs)+totalGain w fs=toffoliCount (sunbuildTail acc Z bank cin w fs) ∧
    measurementCount (sunbuildKnown acc Z bank cin w fs)=measurementCount (sunbuildTail acc Z bank cin w fs) ∧
    wires (sunbuildKnown acc Z bank cin w fs)⊆wires (sunbuildTail acc Z bank cin w fs) ∧
    Challenge.gateSlots (sunbuildKnown acc Z bank cin w fs)≤Challenge.gateSlots (sunbuildTail acc Z bank cin w fs) := by
  by_cases h : Acc.EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩:=Acc.earlyH_info w fs h
    have fit : Acc.FitsLen Z bank 163 (Acc.earlyTerm src false 10) := by
      constructor <;> simp only [Acc.earlyTerm] <;> omega
    have p:=prefixAny_resources acc Z bank cin src hacc fit
    simpa only [sunbuildKnown,sunbuildTail,totalGain,if_pos h,earlyUnbuildKnown,earlyUnbuildTail,Acc.earlyTerm_src,
      toffoliCount_append,measurementCount_append,wires_append,Challenge.gateSlots_append] using
      (show toffoliCount (unbuildTail acc Z bank cin 163 src tail)+toffoliCount (prefixAny acc Z bank cin src)+gain src=
          toffoliCount (unbuildTail acc Z bank cin 163 src tail)+toffoliCount (earlyPrefixClearTail acc Z bank cin src) ∧
        measurementCount (unbuildTail acc Z bank cin 163 src tail)+measurementCount (prefixAny acc Z bank cin src)=
          measurementCount (unbuildTail acc Z bank cin 163 src tail)+measurementCount (earlyPrefixClearTail acc Z bank cin src) ∧
        wires (unbuildTail acc Z bank cin 163 src tail)∪wires (prefixAny acc Z bank cin src)⊆
          wires (unbuildTail acc Z bank cin 163 src tail)∪wires (earlyPrefixClearTail acc Z bank cin src) ∧
        Challenge.gateSlots (unbuildTail acc Z bank cin 163 src tail)+Challenge.gateSlots (prefixAny acc Z bank cin src)≤
          Challenge.gateSlots (unbuildTail acc Z bank cin 163 src tail)+Challenge.gateSlots (earlyPrefixClearTail acc Z bank cin src) from
        ⟨by omega,by omega,Finset.union_subset_union (Finset.Subset.refl _) p.2.2.1,by omega⟩)
  · simp only [sunbuildKnown,sunbuildTail,totalGain,if_neg h,Nat.add_zero]
    exact ⟨trivial,trivial,Finset.Subset.refl _,le_rfl⟩

theorem fillOut_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    :
    toffoliCount (fillOutKnown L a)+totalGain 163 a.terms=toffoliCount (fillOutTail L a) ∧
    measurementCount (fillOutKnown L a)=measurementCount (fillOutTail L a) ∧
    wires (fillOutKnown L a)⊆wires (fillOutTail L a) ∧
    Challenge.gateSlots (fillOutKnown L a)≤Challenge.gateSlots (fillOutTail L a) := by
  have p:=sunbuild_resources (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms (by rw [(acc_lengths L hw).2.1]) (by rw [(acc_lengths L hw).2.2.1])
  simp only [fillOutKnown,fillOutTail,toffoliCount_append,measurementCount_append,wires_append,Challenge.gateSlots_append]
  refine ⟨by omega,by omega,?_,by omega⟩
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) p.2.2.1) (Finset.Subset.refl _))) (Finset.Subset.refl _)

#print axioms prefix_resources
#print axioms sunbuild_resources
#print axioms fillOut_resources
end ECDSAAdd.Entrant.SourcePrefix130Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.SourcePrefix130Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout CodexCKAccTail OwnDiagAll12Square CKAcc

theorem prefixAny_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length≤130)
    (hf4 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 4))
    (hf10 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 10))
    (hf6 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src true 6)) :
    GatePhysical (prefixAny acc Z bank cin src) := by
  by_cases hs : src.length=130
  · have old := earlyPrefixClearTail_physical acc Z bank cin src hacc hsrc hf4 hf10 hf6
    simp only [earlyPrefixClearTail,gatePhysical_append] at old
    have p := SourceTail130Develop.tail_physical acc Z bank cin src hacc hs hf10
    simpa only [prefixAny,if_pos hs,clearPrefix,gatePhysical_append] using And.intro (And.intro old.1.1 p) old.2
  · simpa only [prefixAny,if_neg hs] using earlyPrefixClearTail_physical acc Z bank cin src hacc hsrc hf4 hf10 hf6

theorem sunbuildKnown_physical (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Acc.Fits acc Z bank cin w f) :
    GatePhysical (sunbuildKnown acc Z bank cin w fs) := by
  by_cases h : Acc.EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩ := Acc.earlyH_info w fs h
    have p := prefixAny_physical acc Z bank cin src hacc hlen
      (hf _ (by simp)) (hf _ (by simp)) (hf _ (by simp))
    have u := unbuildTail_physical acc Z bank cin src hacc tail (fun f hf' => hf f (by simp [hf']))
    simpa only [sunbuildKnown,if_pos h,earlyUnbuildKnown,gatePhysical_append] using And.intro u p
  · have old := (Acc.sbuild_physical acc Z bank cin w hacc fs hf).2
    simpa only [sunbuildKnown,Acc.sunbuild,if_neg h] using old

theorem fillKnown_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (fillInK L a) ∧ GatePhysical (fillOutKnown L a) := by
  refine ⟨(OwnDiagAll12Square.fillK_physical L hw hn a cnt ok cntP okP).1,?_⟩
  have full := accFoldQ_physical L hw hn a cnt ok cntP okP
  simp only [accFoldQ,gatePhysical_append] at full
  have out := full.2
  simp only [fillOut,gatePhysical_append] at out
  have k := sunbuildKnown_physical (accReg L) (accZ L) (accBank L) L.core.cin 163
    (acc_lengths L hw).1 a.terms (fun f hf => fits_of L hw hn f (cnt f hf) (ok f hf))
  simp only [fillOutKnown,gatePhysical_append]
  exact ⟨⟨out.1.1,⟨⟨out.1.2.1.1,k⟩,out.1.2.2⟩⟩,out.2⟩

#print axioms fillKnown_physical
end ECDSAAdd.Entrant.SourcePrefix130Develop
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourcePrefix130Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout CodexCKAccTail OwnDiagAll12Square CKAcc

theorem fillKnown_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) :
    (toffoliCount (fillInK L a)≤toffoliCount (fillIn L a) ∧ measurementCount (fillInK L a)=measurementCount (fillIn L a) ∧
      wires (fillInK L a)⊆wires (fillIn L a) ∧ Challenge.gateSlots (fillInK L a)≤Challenge.gateSlots (fillIn L a)) ∧
    (toffoliCount (fillOutKnown L a)≤toffoliCount (fillOut L a) ∧ measurementCount (fillOutKnown L a)=measurementCount (fillOut L a) ∧
      wires (fillOutKnown L a)⊆wires (fillOut L a) ∧ Challenge.gateSlots (fillOutKnown L a)≤Challenge.gateSlots (fillOut L a)) := by
  have old:=fillTail_rel L hw a ok
  have p:=fillOut_resources L hw a
  exact ⟨old.1,by omega,by omega,p.2.2.1.trans old.2.2.2.1,by omega⟩

theorem totalGain_early (src : List Wire) (rest : List MeasuredSquareFold) (hs : src.length=130) :
    totalGain 163 (Acc.earlyTerm src false 4::Acc.earlyTerm src false 10::Acc.earlyTerm src true 6::rest)=123 := by
  simp [totalGain,Acc.EarlyH,Acc.earlyTerm,gain,hs]

theorem eItem_gain (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    totalGain 163 (ControlLoan1589BFFold.eItem L).terms=123 := by
  apply totalGain_early
  simp [ControlLoan1589BFFold.eReg,hw.core.product]

theorem cItem_gain (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    totalGain 163 (accCItem L).terms=123 := by
  apply totalGain_early
  simp [hw.core.product]

#print axioms fillKnown_rel
end ECDSAAdd.Entrant.SourcePrefix130Develop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.AffineFirstCarryDevelop
open Arithmetic Arithmetic.KnownOutputAdder RecordedQuantum

def head (b desired : MappedBit) (extra y c : Wire) : Program :=
  prepare b desired y c ++ [.CX extra c]

theorem head_counts (b desired : MappedBit) (extra y c : Wire) :
    toffoliCount (head b desired extra y c)=0 ∧
    measurementCount (head b desired extra y c)=0 := by
  have h:=prepare_counts b desired y c
  simp [head,toffoliCount_append,measurementCount_append,h.1,h.2,toffoliCount,measurementCount]

theorem head_correct (b desired : MappedBit) (extra y c : Wire)
    (hy : y≠c) (he : extra≠c) (hb : ∀q∈b.wire,q≠c) (hd : ∀q∈desired.wire,q≠c)
    (s : State) (m : List Bool) :
    run (head b desired extra y c) m s=
      ⟨s.phase,writeBit s.basis c
        ((((s.basis c ^^ s.basis y) ^^ b.value s.basis) ^^ desired.value s.basis) ^^ s.basis extra)⟩ := by
  have cnt:=prepare_counts b desired y c
  simp only [head,run_append,cnt.2,measurementCount,List.take_zero,List.drop_zero]
  rw [prepare_correct b desired y c hy hb hd]
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=c
  · subst q
    simp [writeBit,he]
  · simp [writeBit,hq,he]

theorem head_eq_majority (b b' desired : MappedBit) (extra y y' cin c : Wire)
    (hn : [y,cin,c].Nodup) (hy : y'≠c) (he : extra≠c)
    (ha : ∀q∈b.wire,q∉[y,cin,c]) (hb : ∀q∈b'.wire,q≠c) (hd : ∀q∈desired.wire,q≠c)
    (s : State) (m : List Bool)
    (ready : sumBit (b'.value s.basis) (s.basis y')
      (carryBit (b.value s.basis) (s.basis y) (s.basis cin))=
      (desired.value s.basis ^^ s.basis extra)) :
    run (head b' desired extra y' c) m s=run (mappedMajority b y cin c) m s := by
  rw [head_correct b' desired extra y' c hy he hb hd,
    mappedMajority_correct b y cin c hn ha]
  apply congrArg (State.mk s.phase)
  congr 1
  have solve (a b k d e : Bool) (h : sumBit a b k=(d ^^ e)) :
      (a ^^ b ^^ (d ^^ e))=k := by
    cases a <;> cases b <;> cases k <;> cases d <;> cases e <;> simp_all [sumBit]
  have a:=solve _ _ _ _ _ ready
  have algebra (a b d e k z : Bool) (h : (a ^^ b ^^ (d ^^ e))=k) :
      ((((z ^^ b) ^^ a) ^^ d) ^^ e)=(z ^^ k) := by
    cases a <;> cases b <;> cases d <;> cases e <;> cases k <;> cases z <;> simp_all
  exact algebra _ _ _ _ _ _ a


def program (b b' : MappedBit) (bs : List MappedBit) (y y' : Wire) (ys : List Wire)
    (c : Wire) (cs : List Wire) (cin : Wire) (desired : MappedBit) (extra : Wire) : Program :=
  head b' desired extra y' c ++ mappedAdd (b'::bs) (y'::ys) cs c ++
    mappedEraseCarry b y cin c ++ mappedSum b y cin

theorem program_eq (b b' : MappedBit) (bs : List MappedBit) (y y' : Wire) (ys : List Wire)
    (c : Wire) (cs : List Wire) (cin : Wire) (desired : MappedBit) (extra : Wire)
    (hn : [y,cin,c].Nodup) (hy : y'≠c) (he : extra≠c)
    (ha : ∀q∈b.wire,q∉[y,cin,c]) (hb : ∀q∈b'.wire,q≠c) (hd : ∀q∈desired.wire,q≠c)
    (s : State) (m : List Bool)
    (ready : sumBit (b'.value s.basis) (s.basis y')
      (carryBit (b.value s.basis) (s.basis y) (s.basis cin))=
      (desired.value s.basis ^^ s.basis extra)) :
    run (program b b' bs y y' ys c cs cin desired extra) m s=
      run (mappedAdd (b::b'::bs) (y::y'::ys) (c::cs) cin) m s := by
  have h:=head_eq_majority b b' desired extra y y' cin c hn hy he ha hb hd s
  have cnt:=head_counts b' desired extra y' c
  have old:=mappedBit_counts b y cin c
  simp only [program,mappedAdd,List.append_assoc,run_append,run_take,cnt.2,old.2.1,
    List.take_zero,List.drop_zero]
  rw [h _ ready]

theorem program_counts (b b' : MappedBit) (bs : List MappedBit) (y y' : Wire) (ys : List Wire)
    (c : Wire) (cs : List Wire) (cin : Wire) (desired : MappedBit) (extra : Wire)
    (hl : bs.length=ys.length) (hc : cs.length=ys.length) :
    toffoliCount (program b b' bs y y' ys c cs cin desired extra)=ys.length ∧
    measurementCount (program b b' bs y y' ys c cs cin desired extra)=ys.length+1 := by
  have h:=head_counts b' desired extra y' c
  have t:=mappedAdd_counts (b'::bs) (y'::ys) cs c (by simp [hl]) (by simp [hc])
  have e:=mappedBit_counts b y cin c
  simp only [program,toffoliCount_append,measurementCount_append,h.1,h.2,t.1,t.2,
    e.2.2.1,e.2.2.2.1,e.2.2.2.2.1,e.2.2.2.2.2,List.length_cons,Nat.add_sub_cancel,
    Nat.zero_add,Nat.add_zero]
  constructor
  · trivial
  · simp [hc]

theorem head_physical (b desired : MappedBit) (extra y c : Wire)
    (hy : y≠c) (he : extra≠c) (hb : ∀q∈b.wire,q≠c) (hd : ∀q∈desired.wire,q≠c) :
    GatePhysical (head b desired extra y c) := by
  rw [head,gatePhysical_append]
  exact ⟨prepare_physical b desired y c hy hb hd,
    by simp [GatePhysical,PhysicalInstr,ProperGate,he]⟩

#print axioms program_counts
#print axioms head_physical

#print axioms program_eq

#print axioms head_correct
#print axioms head_eq_majority
end ECDSAAdd.Entrant.AffineFirstCarryDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KnownAffinePrefixDevelop
open Arithmetic Arithmetic.KnownOutputAdder

def head (last : Bool) (b desired : MappedBit) (extra y c : Wire) : Program :=
  if last then AffineFirstCarryDevelop.head b desired extra y c else prepare b desired y c

theorem head_counts (last : Bool) (b desired : MappedBit) (extra y c : Wire) :
    toffoliCount (head last b desired extra y c)=0 ∧
    measurementCount (head last b desired extra y c)=0 := by
  have h:=AffineFirstCarryDevelop.head_counts b desired extra y c
  have p:=prepare_counts b desired y c
  cases last <;> simp [head,h.1,h.2,p.1,p.2]

theorem head_correct (last : Bool) (b desired : MappedBit) (extra y c : Wire)
    (hy : y≠c) (hb : ∀q∈b.wire,q≠c) (hd : ∀q∈desired.wire,q≠c) (he : extra≠c)
    (s : State) (m : List Bool) :
    run (head last b desired extra y c) m s=
      ⟨s.phase,writeBit s.basis c
        (((s.basis c ^^ s.basis y) ^^ b.value s.basis) ^^
          (if last then desired.value s.basis ^^ s.basis extra else desired.value s.basis))⟩ := by
  cases last
  · simpa [head] using prepare_correct b desired y c hy hb hd s m
  · simpa [head,Bool.xor_assoc] using AffineFirstCarryDevelop.head_correct b desired extra y c hy he hb hd s m

def values (extra : Wire) : List MappedBit → BasisState → List Bool
  | [],_ => []
  | b::bs,s => (if bs.isEmpty then b.value s ^^ s extra else b.value s)::values extra bs s

theorem values_length (extra : Wire) (sums : List MappedBit) (s : BasisState) :
    (values extra sums s).length=sums.length := by
  induction sums with
  | nil => rfl
  | cons b bs ih => simp [values,ih]

theorem values_congr (extra : Wire) (sums : List MappedBit) (s t : BasisState)
    (hw : ∀q∈mappedWires sums,s q=t q) (he : s extra=t extra) :
    values extra sums s=values extra sums t := by
  induction sums with
  | nil => rfl
  | cons b bs ih =>
    have bv : b.value s=b.value t := mappedBit_value_congr b s t (by
      intro q hq
      apply hw q
      change q∈(b::bs).flatMap (fun b=>b.wire.toList)
      exact List.mem_flatMap.mpr ⟨b,by simp,by simpa using hq⟩)
    have bt := ih (fun q hq=>hw q (List.mem_append_right _ hq))
    simp [values,bv,he,bt]

def program (extra : Wire) : List MappedBit → List Wire → List MappedBit → List Wire → Wire → Program
  | b::b'::bs,y::y'::ys,_d::d'::ds,c::cs,cin =>
      head ds.isEmpty b' d' extra y' c++program extra (b'::bs) (y'::ys) (d'::ds) cs c++
        mappedEraseCarry b y cin c++mappedSum b y cin
  | bits,ys,_,carry,cin => mappedAdd bits ys carry cin

def Ready (extra : Wire) (bits sums : List MappedBit) (ys : List Wire) (cin : Bool) (s : BasisState) : Prop :=
  values extra sums s=(sumBits bits ys cin s).take sums.length

theorem program_counts (extra : Wire) (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hs : sums.length≤ys.length)
    (hc : carry.length+1=ys.length) :
    toffoliCount (program extra bits ys sums carry cin)=ys.length-1-(sums.length-1) ∧
    measurementCount (program extra bits ys sums carry cin)=ys.length-1 := by
  induction ys generalizing bits sums carry cin with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil =>
        simpa [program] using mappedAdd_counts (b::bs) (y::ys) carry cin hl hc
      | cons d ds =>
        cases ds with
        | nil =>
          simpa [program] using mappedAdd_counts (b::bs) (y::ys) carry cin hl hc
        | cons d' ds =>
          cases ys with
          | nil => simp at hs
          | cons y' ys =>
            cases bs with
            | nil => simp at hl
            | cons b' bs =>
              cases carry with
              | nil => simp at hc
              | cons c cs =>
                have t:=ih (b'::bs) (d'::ds) cs c (by simpa using hl)
                  (by simpa using hs) (by simpa using hc)
                have h:=head_counts ds.isEmpty b' d' extra y' c
                have e:=mappedBit_counts b y cin c
                simp only [program,toffoliCount_append,measurementCount_append,h.1,h.2,
                  t.1,t.2,e.2.2.1,e.2.2.2.1,e.2.2.2.2.1,e.2.2.2.2.2,List.length_cons] at *
                omega
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

theorem ready_congr (extra : Wire) (bits sums : List MappedBit) (ys : List Wire) (c : Bool)
    (s t : BasisState) (hs : ∀q∈mappedWires bits,s q=t q)
    (hw : ∀q∈mappedWires sums,s q=t q) (hy : ∀q∈ys,s q=t q) (he : s extra=t extra)
    (h : Ready extra bits sums ys c s) : Ready extra bits sums ys c t := by
  have vals := values_congr extra sums s t hw he
  unfold Ready at h ⊢
  rw [←vals,←sumBits_congr bits ys c s t hs hy]
  exact h

theorem program_eq_mappedAdd (extra : Wire) (bits sums : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (hn : (cin::(ys++carry)).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hw : ∀q∈mappedWires sums,q∉cin::(ys++carry))
    (he : extra∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hs : sums.length≤ys.length)
    (hc : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false)
    (ready : Ready extra bits sums ys (s.basis cin) s.basis) :
    run (program extra bits ys sums carry cin) m s=run (mappedAdd bits ys carry cin) m s := by
  induction ys generalizing bits sums carry cin s m with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => cases bs <;> cases ys <;> cases carry <;> rfl
      | cons d ds =>
        cases ys with
        | nil =>
          have hb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
          have hd : ds=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hs;omega)
          subst bs; subst ds
          rfl
        | cons y' ys =>
          cases bs with
          | nil => simp at hl
          | cons b' bs =>
            cases ds with
            | nil => rfl
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
                have witness : ∀q∈mappedWires (d'::ds),q∉c::((y'::ys)++cs) := by
                  intro q hq bad
                  exact hw q (tail_source_mem d _ q hq)
                    (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have sourceC (q : Wire) (hq : q∈mappedWires (b::b'::bs)) : q≠c := by
                  intro bad; exact ha q hq (by simp [bad])
                have witnessC (q : Wire) (hq : q∈mappedWires (d::d'::ds)) : q≠c := by
                  intro bad; exact hw q hq (by simp [bad])
                let K := carryBit (b.value s.basis) (s.basis y) (s.basis cin)
                let u : State := ⟨s.phase,writeBit s.basis c K⟩
                have clean0 : s.basis c=false := hclean c (by simp)
                have rt : Ready extra (b'::bs) (d'::ds) (y'::ys) K s.basis := by
                  exact (List.cons.inj ready).2
                have next : (if ds.isEmpty then d'.value s.basis ^^ s.basis extra else d'.value s.basis)=sumBit (b'.value s.basis) (s.basis y') K := by
                  exact (List.cons.inj rt).1
                have affine : ((s.basis y' ^^ b'.value s.basis) ^^ (if ds.isEmpty then d'.value s.basis ^^ s.basis extra else d'.value s.basis))=K := by
                  rw [next]
                  cases b'.value s.basis <;> cases s.basis y' <;> cases K <;> decide
                have pre (mm : List Bool) : run (head ds.isEmpty b' d' extra y' c) mm s=u := by
                  rw [head_correct ds.isEmpty b' d' extra y' c yc'
                    (fun q hq => sourceC q (tail_source_mem b _ q (head_source_mem b' bs q hq)))
                    (fun q hq => witnessC q (tail_source_mem d _ q (head_source_mem d' ds q hq)))
                    (by intro bad;exact he (by simp [bad])) s mm]
                  simp only [u,clean0,Bool.false_xor,affine]
                have old (mm : List Bool) : run (mappedMajority b y cin c) mm s=u := by
                  rw [mappedMajority_correct b y cin c three]
                  · simp [u,K,clean0]
                  · intro q hq bad
                    exact ha q (head_source_mem b _ q hq)
                      (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have keep (q : Wire) (hne : q≠c) : u.basis q=s.basis q := by
                  simp [u,writeBit,hne]
                have uc : u.basis c=K := by simp [u,writeBit]
                have tailReady : Ready extra (b'::bs) (d'::ds) (y'::ys) (u.basis c) u.basis := by
                  rw [uc]
                  apply ready_congr extra _ _ _ _ s.basis u.basis _ _ _ _ rt
                  · intro q hq
                    exact (keep q (sourceC q (tail_source_mem b _ q hq))).symm
                  · intro q hq
                    exact (keep q (witnessC q (tail_source_mem d _ q hq))).symm
                  · intro q hq
                    exact (keep q (fun bad => ctail (bad ▸ hq))).symm
                  · exact (keep extra (by intro bad;exact he (by simp [bad]))).symm
                have clean : ∀q∈cs,u.basis q=false := by
                  intro q hq
                  rw [keep q (fun bad => ccs (bad ▸ hq))]
                  exact hclean q (by simp [hq])
                have tail (mm : List Bool) := ih (b'::bs) (d'::ds) cs c nd source witness
                  (by intro bad;exact he (by simp only [List.mem_cons,List.mem_append] at bad ⊢;tauto))
                  (by simpa using hl) (by simpa using hs) (by simpa using hc) u mm clean tailReady
                have pc := head_counts ds.isEmpty b' d' extra y' c
                have oc := mappedBit_counts b y cin c
                have nc := program_counts extra (b'::bs) (d'::ds) (y'::ys) cs c
                  (by simpa using hl) (by simpa using hs) (by simpa using hc)
                have mc := mappedAdd_counts (b'::bs) (y'::ys) cs c
                  (by simpa using hl) (by simpa using hc)
                rw [program,mappedAdd]
                simp only [List.append_assoc,run_append,run_take,pc.2,oc.2.1,
                  nc.2,mc.2,List.take_zero,List.drop_zero]
                rw [pre,old,tail]

#print axioms program_counts
#print axioms program_eq_mappedAdd
end ECDSAAdd.Entrant.KnownAffinePrefixDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KnownAffinePrefixDevelop
open Arithmetic Arithmetic.KnownOutputAdder RecordedQuantum
theorem head_physical (last : Bool) (b desired : MappedBit) (extra y c : Wire)
    (hy : y≠c) (hb : ∀q∈b.wire,q≠c) (hd : ∀q∈desired.wire,q≠c) (he : extra≠c) :
    GatePhysical (head last b desired extra y c) := by
  cases last
  · simpa [head] using prepare_physical b desired y c hy hb hd
  · simpa [head] using AffineFirstCarryDevelop.head_physical b desired extra y c hy he hb hd

theorem program_physical (extra : Wire) (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hs : sums.length≤ys.length)
    (hc : carry.length+1=ys.length) (hn : (cin::ys++carry).Nodup)
    (hb : ∀b∈bits,∀q∈b.wire,q∉cin::ys++carry)
    (hd : ∀b∈sums,∀q∈b.wire,q∉cin::ys++carry)
    (he : extra∉cin::ys++carry) :
    GatePhysical (program extra bits ys sums carry cin) := by
  induction ys generalizing bits sums carry cin with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => simpa [program] using mappedAdd_physical _ _ _ _ hn hb
      | cons d ds =>
        have sm : GatePhysical (mappedSum b y cin) := by
          apply mappedSum_physical
          · intro eq; subst cin
            exact (List.nodup_cons.mp hn).1 (by simp)
          · intro q hq eq; subst q
            exact hb b (by simp) y hq (by simp)
        cases ys with
        | nil =>
          have be : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
          have de : ds=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hs;omega)
          subst bs; subst ds
          exact sm
        | cons y' ys =>
          cases bs with
          | nil => simp at hl
          | cons b' bs =>
            cases ds with
            | nil => simpa [program] using mappedAdd_physical _ _ _ _ hn hb
            | cons d' ds =>
              cases carry with
              | nil => simp at hc
              | cons c cs =>
                have tailnd : (c::(y'::ys)++cs).Nodup := by
                  apply List.nodup_iff_count.mpr
                  intro w
                  have h := List.nodup_iff_count.mp hn w
                  simp only [List.count_cons,List.count_append] at h ⊢
                  omega
                have tailbits : ∀z∈b'::bs,∀q∈z.wire,q∉c::(y'::ys)++cs := by
                  intro z hz q hq hm
                  apply hb z (List.mem_cons_of_mem _ hz) q hq
                  simp only [List.mem_cons,List.mem_append] at hm ⊢
                  tauto
                have tailsums : ∀z∈d'::ds,∀q∈z.wire,q∉c::(y'::ys)++cs := by
                  intro z hz q hq hm
                  apply hd z (List.mem_cons_of_mem _ hz) q hq
                  simp only [List.mem_cons,List.mem_append] at hm ⊢
                  tauto
                have py : y'≠c := by
                  intro eq; subst c
                  exact (List.nodup_cons.mp tailnd).1 (by simp)
                have pb : ∀q∈b'.wire,q≠c := by
                  intro q hq eq; subst q
                  exact hb b' (by simp) c hq (by simp)
                have pd : ∀q∈d'.wire,q≠c := by
                  intro q hq eq; subst q
                  exact hd d' (by simp) c hq (by simp)
                have pr := head_physical ds.isEmpty b' d' extra y' c py pb pd
                  (by intro bad;exact he (by simp [bad]))
                have tl := ih (b'::bs) (d'::ds) cs c
                  (by simpa using hl) (by simpa using hs) (by simpa using hc)
                  tailnd tailbits tailsums
                  (by intro bad;exact he (by simp only [List.mem_cons,List.mem_append] at bad ⊢;tauto))
                simp only [program,gatePhysical_append]
                exact ⟨⟨⟨pr,tl⟩,mappedEraseCarry_physical _ _ _ _⟩,sm⟩

#print axioms program_physical
end ECDSAAdd.Entrant.KnownAffinePrefixDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KnownAffinePrefixDevelop
open Arithmetic Arithmetic.KnownOutputAdder

theorem head_support (last : Bool) (b desired : MappedBit) (extra y c : Wire) :
    wires (head last b desired extra y c)⊆
      (b.wire.toList++desired.wire.toList++[extra,y,c]).toFinset := by
  cases last
  · intro q hq
    have h:=prepare_support b desired y c (by simpa [head] using hq)
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  · intro q hq
    simp only [head,Bool.true_eq,if_true,AffineFirstCarryDevelop.head,wires_append,Finset.mem_union] at hq
    rcases hq with hq|hq
    · have h:=prepare_support b desired y c hq
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
    · have h : q=extra ∨ q=c := by simpa [wires,Instr.wires] using hq
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      tauto

theorem program_support (extra : Wire) (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    wires (program extra bits ys sums carry cin)⊆
      (mappedWires bits++mappedWires sums++ys++carry++[cin,extra]).toFinset := by
  induction bits,ys,sums,carry,cin using program.induct with
  | case1 b b' bs y y' ys d d' ds c cs cin ih =>
    intro q hq
    simp only [program,wires_append,Finset.mem_union] at hq
    have p:=head_support ds.isEmpty b' d' extra y' c
    have e:=(mappedBit_wires b y cin c).2.1
    have z:=(mappedBit_wires b y cin c).2.2
    rcases hq with ((hq|hq)|hq)|hq
    · have h:=p hq
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,mappedWires,List.flatMap_cons] at h ⊢
      tauto
    · have h:=ih hq
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,mappedWires,List.flatMap_cons] at h ⊢
      tauto
    · have h:=e hq
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,mappedWires,List.flatMap_cons] at h ⊢
      tauto
    · have h:=z hq
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,mappedWires,List.flatMap_cons] at h ⊢
      tauto
  | case2 bits ys sums carry cin h =>
    intro q hq
    simp only [program] at hq
    have old:=mappedAdd_wires_subset bits ys carry cin hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at old ⊢
    tauto
#print axioms program_support
end ECDSAAdd.Entrant.KnownAffinePrefixDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KnownAffinePrefixDevelop
open Arithmetic Arithmetic.KnownOutputAdder

theorem program_read_slots_le (extra : Wire) (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hs : sums.length≤ys.length)
    (hc : carry.length+1=ys.length)
    (hb : ∀b∈bits,∃a,b=({wire:=some a,flip:=false} : MappedBit))
    (hd : ∀b∈sums,∃a,b=({wire:=some a,flip:=false} : MappedBit)) :
    Challenge.gateSlots (program extra bits ys sums carry cin)≤
      Challenge.gateSlots (mappedAdd bits ys carry cin) := by
  induction ys generalizing bits sums carry cin with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => simp [program]
      | cons d ds =>
        cases ds with
        | nil => simp [program]
        | cons d' ds =>
          cases ys with
          | nil => simp at hs
          | cons y' ys =>
            cases bs with
            | nil => simp at hl
            | cons b' bs =>
              cases carry with
              | nil => simp at hc
              | cons c cs =>
                have it:=ih (b'::bs) (d'::ds) cs c (by simpa using hl)
                  (by simpa using hs) (by simpa using hc)
                  (fun z hz=>hb z (List.mem_cons_of_mem _ hz))
                  (fun z hz=>hd z (List.mem_cons_of_mem _ hz))
                obtain ⟨a,rfl⟩:=hb b (by simp)
                obtain ⟨a',rfl⟩:=hb b' (by simp)
                obtain ⟨w,rfl⟩:=hd d' (by simp)
                have pr : Challenge.gateSlots (head ds.isEmpty ⟨some a',false⟩ ⟨some w,false⟩ extra y' c)≤4 := by
                  cases h : ds.isEmpty <;> simp [head,h,AffineFirstCarryDevelop.head,prepare,xorBit,Challenge.gateSlots,Challenge.instructionSlots]
                have ma : Challenge.gateSlots (mappedMajority ⟨some a,false⟩ y cin c)=6 := rfl
                simp only [program,mappedAdd,Challenge.gateSlots_append,ma,List.length_cons] at *
                omega
#print axioms program_read_slots_le
end ECDSAAdd.Entrant.KnownAffinePrefixDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KnownAffinePrefixDevelop
open Arithmetic Arithmetic.KnownOutputAdder

theorem values_getD (extra : Wire) (sums : List MappedBit) (s : BasisState)
    (i : Nat) (hi : i<sums.length) :
    (values extra sums s).getD i false=
      (if i+1=sums.length then (sums.map (fun b=>b.value s)).getD i false ^^ s extra
       else (sums.map (fun b=>b.value s)).getD i false) := by
  induction sums generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero =>
      cases bs <;> simp [values]
    | succ i =>
      have h:=ih i (by simpa using hi)
      simpa [values,Nat.add_assoc] using h

theorem ready_of_number (extra : Wire) (bits sums : List MappedBit) (ys : List Wire) (cin : Bool)
    (s : BasisState) (hl : bits.length=ys.length) (hs : sums.length≤ys.length)
    (hv : ∀i,i<sums.length →
      (values extra sums s).getD i false=
        ((mappedValue bits s+regValue ys s+cin.toNat)%2^ys.length).testBit i) :
    Ready extra bits sums ys cin s := by
  unfold Ready
  apply List.ext_getElem
    (by simp only [values_length,List.length_take,sumBits_length bits ys cin s hl];omega)
  intro i hi1 hi2
  have hi : i<sums.length := by simpa only [values_length] using hi1
  have full : (sumBits bits ys cin s).getD i false=
      ((mappedValue bits s+regValue ys s+cin.toNat)%2^ys.length).testBit i := by
    rw [←MixedLiteralAdderDevelop.boolValue_bit,sumBits_value bits ys cin s hl]
  have tk : ((sumBits bits ys cin s).take sums.length).getD i false=
      (sumBits bits ys cin s).getD i false := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_take_of_lt hi]
  have h := (hv i hi).trans (full.symm.trans tk.symm)
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi1,
    List.getElem?_eq_getElem hi2,Option.getD_some] using h
#print axioms ready_of_number
end ECDSAAdd.Entrant.KnownAffinePrefixDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.SourceAddLowBitsDevelop

theorem add_window (H : Nat) :
    1040*H/64=16*H+H/4 := by omega

theorem low_four (H : Nat) :
    (1040*H/64)%16=(H/4)%16 := by
  rw [add_window,Nat.add_mod]
  simp

theorem low_bit (H i : Nat) (hi : i<4) :
    (1040*H/64).testBit i=H.testBit (i+2) := by
  have eq := low_four H
  have h := congrArg (fun n : Nat => n.testBit i) eq
  simp only [show 16=2^4 by decide,Nat.testBit_mod_two_pow,hi,decide_true,Bool.true_and] at h
  rw [h]
  change (H/2^2).testBit i=H.testBit (i+2)
  rw [Nat.testBit_div_two_pow]
#print axioms low_bit
end ECDSAAdd.Entrant.SourceAddLowBitsDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.SourceAddFourthBitDevelop

theorem fourth (H : Nat) :
    (1040*H/64).testBit 4=(H.testBit 6 ^^ H.testBit 0) := by
  rw [SourceAddLowBitsDevelop.add_window]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  norm_num only [Nat.reducePow,Nat.div_one]
  have dv : (16*H+H/4)/16=H+H/64 := by omega
  rw [dv]
  have h0 : H%2=0 ∨ H%2=1 := by omega
  have h6 : (H/64)%2=0 ∨ (H/64)%2=1 := by omega
  rcases h0 with h0|h0 <;> rcases h6 with h6|h6 <;> simp [Nat.add_mod,h0,h6]
#print axioms fourth
end ECDSAAdd.Entrant.SourceAddFourthBitDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceAddFourDevelop
open Arithmetic Arithmetic.KnownOutputAdder MixedLiteralAdderDevelop

def desired (src : List Wire) : List MappedBit := mappedRead ((src.drop 2).take 5) false
def program (src Z ys carry : List Wire) (cin : Wire) : Program :=
  KnownAffinePrefixDevelop.program (src.getD 0 0)
    (mappedRead (src++Z.take 5) false) ys (desired src) carry cin

theorem arithmetic (H : Nat) : H+976*H/64=1040*H/64 := by omega
theorem desired_length (src : List Wire) (hs : 7≤src.length) : (desired src).length=5 := by
  simp [desired,mappedRead];omega
theorem desired_source (src : List Wire) (q : Wire) (hq : q∈mappedWires (desired src)) : q∈src := by
  rw [desired,mappedRead_wires] at hq
  exact List.mem_of_mem_drop (List.mem_of_mem_take hq)
theorem extra_mem (src : List Wire) (hs : 0<src.length) : src.getD 0 0∈src := by
  cases src <;> simp_all
theorem extra_bit (src : List Wire) (hs : 0<src.length) (s : BasisState) :
    s (src.getD 0 0)=(regValue src s).testBit 0 := by
  cases src with
  | nil => simp at hs
  | cons a as =>
    cases h : s a <;> simp [regValue,Nat.testBit_eq_decide_div_mod_eq,h,Nat.add_mod]

theorem run_eq_add (src Z ys carry : List Wire) (cin : Wire)
    (hs : 7≤src.length) (hzl : 5≤Z.length)
    (hy : ys.length=src.length+5) (hc : carry.length+1=ys.length)
    (hn : (cin::((src++Z.take 5)++ys++carry)).Nodup)
    (s : State) (m : List Bool) (hz : ∀q∈Z,s.basis q=false)
    (hcarry : ∀q∈carry,s.basis q=false) (hcin : s.basis cin=false)
    (H : Nat) (hsrc : regValue src s.basis=H)
    (hys : regValue ys s.basis=976*H/64) :
    run (program src Z ys carry cin) m s=run (addInPlace (src++Z.take 5) ys carry cin) m s := by
  have geo:=read_geometry (src++Z.take 5) ys carry cin hn
  have zv : regValue (Z.take 5) s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq=>hz q (List.mem_of_mem_take hq))
  have sv : mappedValue (mappedRead (src++Z.take 5) false) s.basis=H := by
    rw [mappedRead_value,regValue_append,hsrc,zv,Nat.mul_zero,Nat.add_zero]
  have hl : (mappedRead (src++Z.take 5) false).length=ys.length := by simp [mappedRead,hy];omega
  have hd:=desired_length src hs
  have he0 : s.basis (src.getD 0 0)=H.testBit 0 := by
    rw [extra_bit src (by omega) s.basis,hsrc]
  have ready : KnownAffinePrefixDevelop.Ready (src.getD 0 0)
      (mappedRead (src++Z.take 5) false) (desired src) ys (s.basis cin) s.basis := by
    apply KnownAffinePrefixDevelop.ready_of_number _ _ _ _ _ _ hl (by omega)
    intro i hi
    have hi5 : i<5 := by omega
    have bv : ((desired src).map (fun b=>b.value s.basis)).getD i false=H.testBit (i+2) := by
      rw [←boolValue_bit,mapped_boolValue,desired,mappedRead_value,
        CuccaroStreamedSquareWideLayout.regValue_take_mod (src.drop 2) 5 (by simp;omega),
        CuccaroStreamedSquareWideLayout.regValue_drop_div src 2 (by omega),hsrc]
      rw [Nat.testBit_mod_two_pow]
      simp only [hi5,decide_true,Bool.true_and]
      rw [Nat.testBit_div_two_pow]
    rw [KnownAffinePrefixDevelop.values_getD _ _ _ i hi,hd,bv,he0]
    rw [sv,hys,hcin,Bool.toNat_false,Nat.add_zero,arithmetic,Nat.testBit_mod_two_pow]
    have hiy : i<ys.length := by omega
    simp only [hiy,decide_true,Bool.true_and,Nat.add_zero]
    by_cases h4 : i=4
    · subst i
      simpa using (SourceAddFourthBitDevelop.fourth H).symm
    · have hi4 : i<4 := by omega
      rw [if_neg (by omega),SourceAddLowBitsDevelop.low_bit H i hi4]
  have eq:=KnownAffinePrefixDevelop.program_eq_mappedAdd (src.getD 0 0)
    (mappedRead (src++Z.take 5) false) (desired src) ys carry cin geo.1
    (by rw [mappedRead_wires];exact geo.2)
    (by intro q hq;exact geo.2 q (List.mem_append_left _ (desired_source src q hq)))
    (geo.2 _ (List.mem_append_left _ (extra_mem src (by omega))))
    hl (by omega) hc s m hcarry ready
  change run (KnownAffinePrefixDevelop.program _ _ _ _ _ _) m s=_
  rw [eq,read_add_eq]
#print axioms extra_bit
#print axioms run_eq_add
end ECDSAAdd.Entrant.SourceAddFourDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceAddFourDevelop
open Arithmetic Arithmetic.KnownOutputAdder MixedLiteralAdderDevelop

theorem read_shape (xs : List Wire) (b : MappedBit) (hb : b∈mappedRead xs false) :
    ∃a,b=({wire:=some a,flip:=false} : MappedBit) := by
  change b∈xs.map (fun a=>({wire:=some a,flip:=false} : MappedBit)) at hb
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
  exact ⟨a,rfl⟩

theorem program_counts (src Z ys carry : List Wire) (cin : Wire)
    (hs : 7≤src.length) (hz : 5≤Z.length)
    (hy : ys.length=src.length+5) (hc : carry.length+1=ys.length) :
    toffoliCount (program src Z ys carry cin)=src.length ∧
    measurementCount (program src Z ys carry cin)=src.length+4 := by
  have hd:=desired_length src hs
  have a:=KnownAffinePrefixDevelop.program_counts (src.getD 0 0) (mappedRead (src++Z.take 5) false)
    (desired src) ys carry cin (by simp [mappedRead,hy];omega) (by omega) hc
  simpa [program,hy,hd] using a

theorem program_physical (src Z ys carry : List Wire) (cin : Wire)
    (hs : 7≤src.length) (hz : 5≤Z.length)
    (hy : ys.length=src.length+5) (hc : carry.length+1=ys.length)
    (hn : (cin::((src++Z.take 5)++ys++carry)).Nodup) :
    GatePhysical (program src Z ys carry cin) := by
  have geo:=read_geometry (src++Z.take 5) ys carry cin hn
  have hd:=desired_length src hs
  apply KnownAffinePrefixDevelop.program_physical (src.getD 0 0) _ _ _ _ _
    (by simp [mappedRead,hy];omega) (by omega) hc geo.1
  · intro b hb q hq
    have mem : q∈mappedWires (mappedRead (src++Z.take 5) false) :=
      List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
    rw [mappedRead_wires] at mem
    exact geo.2 q mem
  · intro b hb q hq
    have mem : q∈mappedWires (desired src) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
    exact geo.2 q (List.mem_append_left _ (desired_source src q mem))
  · exact geo.2 _ (List.mem_append_left _ (extra_mem src (by omega)))

theorem program_support (src Z ys carry : List Wire) (cin : Wire) (hs : 0<src.length) :
    wires (program src Z ys carry cin)⊆(src++Z.take 5++ys++carry++[cin]).toFinset := by
  have h:=KnownAffinePrefixDevelop.program_support (src.getD 0 0) (mappedRead (src++Z.take 5) false) (desired src) ys carry cin
  rw [mappedRead_wires] at h
  intro q hq
  have mem:=h hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at mem ⊢
  rcases mem with h|h|h|h|h|h|h
  · tauto
  · tauto
  · have old:=desired_source src q h;tauto
  · tauto
  · tauto
  · tauto
  · subst q
    have old:=extra_mem src hs
    tauto

theorem program_slots (src Z ys carry : List Wire) (cin : Wire)
    (hs : 7≤src.length) (hz : 5≤Z.length)
    (hy : ys.length=src.length+5) (hc : carry.length+1=ys.length) :
    Challenge.gateSlots (program src Z ys carry cin)≤
      Challenge.gateSlots (addInPlace (src++Z.take 5) ys carry cin) := by
  have hd:=desired_length src hs
  have a:=KnownAffinePrefixDevelop.program_read_slots_le (src.getD 0 0)
    (mappedRead (src++Z.take 5) false) (desired src) ys carry cin
    (by simp [mappedRead,hy];omega) (by omega) hc (read_shape _) (read_shape _)
  simpa only [program,read_add_eq] using a

theorem program_resources (src Z ys carry : List Wire) (cin : Wire)
    (hs : 7≤src.length) (hz : 5≤Z.length)
    (hy : ys.length=src.length+5) (hc : carry.length+1=ys.length) :
    toffoliCount (program src Z ys carry cin)+4=toffoliCount (addInPlace (src++Z.take 5) ys carry cin) ∧
    measurementCount (program src Z ys carry cin)=measurementCount (addInPlace (src++Z.take 5) ys carry cin) ∧
    wires (program src Z ys carry cin)⊆wires (addInPlace (src++Z.take 5) ys carry cin) ∧
    Challenge.gateSlots (program src Z ys carry cin)≤Challenge.gateSlots (addInPlace (src++Z.take 5) ys carry cin) := by
  have hl : (src++Z.take 5).length=ys.length := by simp [hy];omega
  have old:=addInPlace_counts (src++Z.take 5) ys carry cin hl hc
  have new:=program_counts src Z ys carry cin hs hz hy hc
  have sl:=program_slots src Z ys carry cin hs hz hy hc
  refine ⟨by omega,by omega,?_,by omega⟩
  rw [addInPlace_wires _ _ _ _ hl hc]
  intro q hq
  have h:=program_support src Z ys carry cin (by omega) hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h ⊢
  tauto
#print axioms program_counts
#print axioms program_physical
#print axioms program_support
#print axioms program_slots
#print axioms program_resources
end ECDSAAdd.Entrant.SourceAddFourDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceAddFourDevelop
open Arithmetic

def add (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  program src Z ((acc.take 139).drop 6) (bank.take 132) cin

theorem add_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src true 6))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (976*regValue src base)) (add acc Z bank cin src)
      (SquareFrame acc base (1040*regValue src base)) := by
  let f:=Acc.earlyTerm src true 6
  let H:=regValue src base
  have hH : H<2^128 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have old:=Acc.op_prefix_triple acc Z bank cin 163 139 f hacc (by decide) hf
    (by simp [f,Acc.earlyTerm,hsrc]) base hz hb hi false (976*H)
    (by omega) (by simp only [f,Acc.earlyTerm];dsimp [H];omega)
  have value : Acc.step base false (976*H) f=1040*H := by
    norm_num [Acc.step,f,Acc.earlyTerm]
    dsimp [H]
    omega
  rw [value] at old
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 f (by decide) hf (by simp [f,Acc.earlyTerm,hsrc])
  have len : (acc.take 139).length=139 := by simp [hacc]
  have rawEq : Acc.op (acc.take 139) Z bank cin 139 false f=
      addInPlace (src++Z.take 5) ((acc.take 139).drop 6) (bank.take 132) cin := by
    simp [Acc.op,Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc]
  intro s m hs
  have away (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h:=List.nodup_iff_count.mp hf.nd q
    have a:=List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b:=List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
      omega
  have same (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : s.basis q=base q := hs.2 q (away q hq)
  have pref:=regValue_take_drop_of_lt acc 139 (976*H) s.basis (by omega) hs.1 (by omega)
  have sy : regValue ((acc.take 139).drop 6) s.basis=976*H/64 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
    rfl
  have sh : regValue src s.basis=H := regValue_congr src _ base (fun q hq=>same q (Or.inl (by simp [hq])))
  have sz (q : Wire) (hq : q∈Z) : s.basis q=false :=
    (same q (Or.inl (by simp [hq]))).trans (hz q hq)
  have sb (q : Wire) (hq : q∈bank.take 132) : s.basis q=false :=
    (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
  have si : s.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd' : (cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd
  have zl : 5≤Z.length := by
    have h:=fit.zpad
    simpa [f,Acc.earlyTerm,hsrc] using h
  have bl : (bank.take 132).length=132 := by
    have h:=fit.bankLen
    simp only [f,Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have e:=run_eq_add src Z ((acc.take 139).drop 6) (bank.take 132) cin (by omega) zl
    (by simp [len,hsrc]) (by simp [bl,len]) nd' s m sz sb si H sh sy
  change run (add acc Z bank cin src) m s=_ at e
  rw [e,←rawEq]
  exact old s m hs
#print axioms add_triple
end ECDSAAdd.Entrant.SourceAddFourDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceAddFourDevelop
open Arithmetic CodexNarrowTail
theorem add_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : Acc.FitsLen Z bank 163 (Acc.earlyTerm src true 6)) :
    toffoliCount (add acc Z bank cin src)+4=
      toffoliCount (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)) ∧
    measurementCount (add acc Z bank cin src)=
      measurementCount (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)) ∧
    wires (add acc Z bank cin src)⊆
      wires (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)) ∧
    Challenge.gateSlots (add acc Z bank cin src)≤
      Challenge.gateSlots (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)) := by
  have fit:=CodexNarrowTail.narrowLen Z bank 139 (Acc.earlyTerm src true 6) hf (by decide)
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 5≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 132).length=132 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have h:=program_resources src Z ((acc.take 139).drop 6) (bank.take 132) cin (by omega) zl
    (by simp [hacc,hsrc]) (by simp [hacc,bl])
  simpa [add,Acc.op,Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using h

theorem add_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src true 6)) :
    GatePhysical (add acc Z bank cin src) := by
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 (Acc.earlyTerm src true 6) (by decide) hf
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 5≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 132).length=132 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6) fit
  have nd' : (cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using nd
  exact program_physical src Z ((acc.take 139).drop 6) (bank.take 132) cin (by omega) zl (by simp [hacc,hsrc]) (by simp [hacc,bl]) nd'


#print axioms add_resources
#print axioms add_physical
end ECDSAAdd.Entrant.SourceAddFourDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceAddFour130Develop
open Arithmetic SourceAddFourDevelop

def add (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  program src Z ((acc.take 141).drop 6) (bank.take 134) cin

theorem add_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=130)
    (hf : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src true 6))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (976*regValue src base)) (add acc Z bank cin src)
      (SquareFrame acc base (1040*regValue src base)) := by
  let f:=Acc.earlyTerm src true 6
  let H:=regValue src base
  have hH : H<2^130 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have old:=Acc.op_prefix_triple acc Z bank cin 163 141 f hacc (by decide) hf
    (by simp [f,Acc.earlyTerm,hsrc]) base hz hb hi false (976*H)
    (by omega) (by simp only [f,Acc.earlyTerm];dsimp [H];omega)
  have value : Acc.step base false (976*H) f=1040*H := by
    norm_num [Acc.step,f,Acc.earlyTerm]
    dsimp [H]
    omega
  rw [value] at old
  have fit:=Acc.fits_prefix acc Z bank cin 163 141 f (by decide) hf (by simp [f,Acc.earlyTerm,hsrc])
  have len : (acc.take 141).length=141 := by simp [hacc]
  have rawEq : Acc.op (acc.take 141) Z bank cin 141 false f=
      addInPlace (src++Z.take 5) ((acc.take 141).drop 6) (bank.take 134) cin := by
    simp [Acc.op,Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc]
  intro s m hs
  have away (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h:=List.nodup_iff_count.mp hf.nd q
    have a:=List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b:=List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
      omega
  have same (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : s.basis q=base q := hs.2 q (away q hq)
  have pref:=regValue_take_drop_of_lt acc 141 (976*H) s.basis (by omega) hs.1 (by omega)
  have sy : regValue ((acc.take 141).drop 6) s.basis=976*H/64 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
    rfl
  have sh : regValue src s.basis=H := regValue_congr src _ base (fun q hq=>same q (Or.inl (by simp [hq])))
  have sz (q : Wire) (hq : q∈Z) : s.basis q=false :=
    (same q (Or.inl (by simp [hq]))).trans (hz q hq)
  have sb (q : Wire) (hq : q∈bank.take 134) : s.basis q=false :=
    (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
  have si : s.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have nd:=Acc.fits_nodup (acc.take 141) Z bank cin 141 f fit
  have nd' : (cin::((src++Z.take 5)++(acc.take 141).drop 6++bank.take 134)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd
  have zl : 5≤Z.length := by
    have h:=fit.zpad
    simpa [f,Acc.earlyTerm,hsrc] using h
  have bl : (bank.take 134).length=134 := by
    have h:=fit.bankLen
    simp only [f,Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have e:=run_eq_add src Z ((acc.take 141).drop 6) (bank.take 134) cin (by omega) zl
    (by simp [len,hsrc]) (by simp [bl,len]) nd' s m sz sb si H sh sy
  change run (add acc Z bank cin src) m s=_ at e
  rw [e,←rawEq]
  exact old s m hs
#print axioms add_triple
end ECDSAAdd.Entrant.SourceAddFour130Develop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceAddFour130Develop
open Arithmetic CodexNarrowTail SourceAddFourDevelop
theorem add_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=130)
    (hf : Acc.FitsLen Z bank 163 (Acc.earlyTerm src true 6)) :
    toffoliCount (add acc Z bank cin src)+4=
      toffoliCount (Acc.op (acc.take 141) Z bank cin 141 false (Acc.earlyTerm src true 6)) ∧
    measurementCount (add acc Z bank cin src)=
      measurementCount (Acc.op (acc.take 141) Z bank cin 141 false (Acc.earlyTerm src true 6)) ∧
    wires (add acc Z bank cin src)⊆
      wires (Acc.op (acc.take 141) Z bank cin 141 false (Acc.earlyTerm src true 6)) ∧
    Challenge.gateSlots (add acc Z bank cin src)≤
      Challenge.gateSlots (Acc.op (acc.take 141) Z bank cin 141 false (Acc.earlyTerm src true 6)) := by
  have fit:=CodexNarrowTail.narrowLen Z bank 141 (Acc.earlyTerm src true 6) hf (by decide)
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 5≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 134).length=134 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have h:=program_resources src Z ((acc.take 141).drop 6) (bank.take 134) cin (by omega) zl
    (by simp [hacc,hsrc]) (by simp [hacc,bl])
  simpa [add,Acc.op,Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using h

theorem add_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=130)
    (hf : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src true 6)) :
    GatePhysical (add acc Z bank cin src) := by
  have fit:=Acc.fits_prefix acc Z bank cin 163 141 (Acc.earlyTerm src true 6) (by decide) hf
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 5≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 134).length=134 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have nd:=Acc.fits_nodup (acc.take 141) Z bank cin 141 (Acc.earlyTerm src true 6) fit
  have nd' : (cin::((src++Z.take 5)++(acc.take 141).drop 6++bank.take 134)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using nd
  exact program_physical src Z ((acc.take 141).drop 6) (bank.take 134) cin (by omega) zl (by simp [hacc,hsrc]) (by simp [hacc,bl]) nd'


#print axioms add_resources
#print axioms add_physical
end ECDSAAdd.Entrant.SourceAddFour130Develop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceFourPrefix130Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def clearPrefix (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  SourceAddFour130Develop.add acc Z bank cin src++
    SourceTail130Develop.tail acc Z bank cin src++Acc.seedOp acc Z 163 (Acc.earlyTerm src false 4)

theorem prefix_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=130)
    (hf4 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 4))
    (hf10 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 10))
    (hf6 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src true 6))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (976*regValue src base)) (clearPrefix acc Z bank cin src)
      (SquareFrame acc base 0) := by
  have hH : regValue src base<2^130 :=
    lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) (by omega))
  generalize hHd : regValue src base = H at hH
  have ad := SourceAddFour130Develop.add_triple acc Z bank cin src hacc hsrc hf6 base hz hb hi
  rw [hHd] at ad
  change Triple (SquareFrame acc base (976*H)) (SourceAddFour130Develop.add acc Z bank cin src)
    (SquareFrame acc base (1040*H)) at ad
  have sub : Triple (SquareFrame acc base (1040*H))
      (SourceTail130Develop.tail acc Z bank cin src)
      (SquareFrame acc base (16*H)) := by
    simpa only [hHd] using SourceTail130Develop.tail_triple acc Z bank cin src hacc hsrc hf10 base hz hb hi
  have seed := Acc.seed_triple acc Z bank cin 163 (Acc.earlyTerm src false 4) hacc hf4 base hz
    (16*H) 0 (Or.inr (by simp [Acc.earlyTerm,hHd,Nat.mul_comm]))
  exact (ad.seq sub).seq seed


#print axioms prefix_triple
end ECDSAAdd.Entrant.SourceFourPrefix130Develop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.SourceFourPrefix130Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout CodexCKAccTail OwnDiagAll12Square CKAcc

def prefixAny (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  if src.length=130 then clearPrefix acc Z bank cin src else earlyPrefixClearTail acc Z bank cin src

theorem prefixAny_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length≤130)
    (hf4 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 4))
    (hf10 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 10))
    (hf6 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src true 6))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (976*regValue src base)) (prefixAny acc Z bank cin src)
      (SquareFrame acc base 0) := by
  by_cases h : src.length=130
  · simpa only [prefixAny,if_pos h] using prefix_triple acc Z bank cin src hacc h hf4 hf10 hf6 base hz hb hi
  · simpa only [prefixAny,if_neg h] using earlyPrefixClearTail_triple acc Z bank cin src hacc hsrc hf4 hf10 hf6 base hz hb hi

def earlyUnbuildKnown (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | a::_::_::tail => unbuildTail acc Z bank cin w a.src tail++prefixAny acc Z bank cin a.src
  | _ => []
def sunbuildKnown (acc Z bank : List Wire) (cin : Wire) (w : Nat) (fs : List MeasuredSquareFold) : Program :=
  if Acc.EarlyH w fs then earlyUnbuildKnown acc Z bank cin w fs else Acc.baseUnbuild acc Z bank cin w fs

theorem sunbuildKnown_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Acc.Fits acc Z bank cin w f) (hv : Acc.Valid base w 0 fs) :
    Triple (SquareFrame acc base (Acc.accVal base 0 fs)) (sunbuildKnown acc Z bank cin w fs)
      (SquareFrame acc base 0) := by
  by_cases h : Acc.EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩ := Acc.earlyH_info w fs h
    have hf4 := hf (Acc.earlyTerm src false 4) (by simp)
    have hf10 := hf (Acc.earlyTerm src false 10) (by simp)
    have hf6 := hf (Acc.earlyTerm src true 6) (by simp)
    have vt := hv.2.2.2
    change Acc.Valid base 163
      (Acc.step base true (Acc.step base false (Acc.step base false 0 (Acc.earlyTerm src false 4))
        (Acc.earlyTerm src false 10)) (Acc.earlyTerm src true 6)) tail at vt
    rw [Acc.early_steps] at vt
    have rest := unbuildTail_triple acc Z bank cin src hacc hlen base hz hb hi tail
      (fun f hf' => hf f (by simp [hf'])) vt
    have head := prefixAny_triple acc Z bank cin src hacc hlen hf4 hf10 hf6 base hz hb hi
    rw [sunbuildKnown,if_pos h,earlyUnbuildKnown]
    simpa only [Acc.accVal,Acc.earlyTerm_src,Acc.earlyTerm_negative,Acc.early_steps] using rest.seq head
  · simpa only [sunbuildKnown,if_neg h] using Acc.baseUnbuild_triple acc Z bank cin w hacc base hz hb hi fs hf hv

def fillOutKnown (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  tempIn L a++(splitIn L a++sunbuildKnown (accReg L) (accZ L) (accBank L) L.core.cin 163 a.terms++splitOut L a)++
    tempOut L a

theorem fillOutKnown_triple (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (a : AccItem) (hv : AccView L base a)
    (b : BasisState) (agree : ∀q∈L.core.product,b q=base q)
    (hz : ∀q∈accZ L,b q=false) (hb : ∀q∈accBank L,b q=false) (hi : b L.core.cin=false)
    (hW : ∀q∈wTemp L,b q=false) :
    Triple (SquareFrame (accReg L) b (Acc.accVal base 0 a.spec)) (fillOutKnown L a)
      (SquareFrame (accReg L) b 0) := by
  have lens := acc_lengths L hw
  have fits (f : MeasuredSquareFold) (hf : f∈a.terms) := fits_of L hw hn f (hv.count f hf) (hv.ok f hf)
  apply fill_core L hw hn base a hv b agree hz hb hi hW
  intro t ht hwv tz tb tc
  by_cases hp : a.pre=[]
  · simp only [splitIn,splitOut,if_pos hp,List.nil_append,List.append_nil]
    have val := hv.value t (fun q hq _ => ht q hq)
      (by rw [if_pos hp,Nat.add_zero]; exact regValue_congr _ _ _ (fun q hq => ht q (hiReg_product L q hq))) hwv
    have tr := sunbuildKnown_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 lens.1 t tz tb tc a.terms fits val.1
    rwa [val.2] at tr
  · simp only [splitIn,splitOut,hp,if_false]
    have hH : regValue (hiReg L) t=regValue (hiReg L) base :=
      regValue_congr _ _ _ (fun q hq => ht q (hiReg_product L q hq))
    apply split_mid L hw hn t (Acc.accVal base 0 a.pre) (regValue (hiReg L) base) hv.hiLe hH hwv tz tb tc
    intro u hu hval
    have uprod : ∀q∈L.core.product,q∉hiReg L → u q=base q :=
      fun q hq hh => (hu q hh (product_away L hn q hq).1).trans (ht q hq)
    have val := hv.value u uprod (by simpa only [hp,if_false] using hval)
      ((regValue_congr _ _ _ (fun q hq => hu q (wTemp_not_hi L hn q hq)
        (fun b => acc_temp_disjoint L hn q b hq))).trans hwv)
    have uz : ∀q∈accZ L,u q=false := fun q hq => (hu q (accZ_not_hi L hn q hq) (accZ_away L hn q hq).1).trans (tz q hq)
    have ub : ∀q∈accBank L,u q=false :=
      fun q hq => (hu q (accBank_not_hi L hn q hq) (accBank_away L hn q hq).1).trans (tb q hq)
    have uc : u L.core.cin=false := (hu _ (cin_not_hi L hn) (cin_away L hn).1).trans tc
    have tr := sunbuildKnown_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 lens.1 u uz ub uc a.terms fits val.1
    rwa [val.2] at tr

#print axioms fillOutKnown_triple
end ECDSAAdd.Entrant.SourceFourPrefix130Develop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.SourceFourPrefix130Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout CodexCKAccTail OwnDiagAll12Square CKAcc

def gain (src : List Wire) : Nat := if src.length=130 then 127 else 0

theorem prefix_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=130)
    (hf : Acc.FitsLen Z bank 163 (Acc.earlyTerm src false 10))
    (hf6 : Acc.FitsLen Z bank 163 (Acc.earlyTerm src true 6)) :
    toffoliCount (clearPrefix acc Z bank cin src)+127=toffoliCount (earlyPrefixClearTail acc Z bank cin src) ∧
    measurementCount (clearPrefix acc Z bank cin src)=measurementCount (earlyPrefixClearTail acc Z bank cin src) ∧
    wires (clearPrefix acc Z bank cin src)⊆wires (earlyPrefixClearTail acc Z bank cin src) ∧
    Challenge.gateSlots (clearPrefix acc Z bank cin src)≤Challenge.gateSlots (earlyPrefixClearTail acc Z bank cin src) := by
  have h:=SourceTail130Develop.tail_resources acc Z bank cin src hacc hsrc hf
  have a:=SourceAddFour130Develop.add_resources acc Z bank cin src hacc hsrc hf6
  simp only [clearPrefix,earlyPrefixClearTail,toffoliCount_append,measurementCount_append,wires_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,Finset.union_subset_union (Finset.union_subset_union a.2.2.1 h.2.2.1) (Finset.Subset.refl _),by omega⟩

theorem prefixAny_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hf : Acc.FitsLen Z bank 163 (Acc.earlyTerm src false 10))
    (hf6 : src.length=130 → Acc.FitsLen Z bank 163 (Acc.earlyTerm src true 6)) :
    toffoliCount (prefixAny acc Z bank cin src)+gain src=toffoliCount (earlyPrefixClearTail acc Z bank cin src) ∧
    measurementCount (prefixAny acc Z bank cin src)=measurementCount (earlyPrefixClearTail acc Z bank cin src) ∧
    wires (prefixAny acc Z bank cin src)⊆wires (earlyPrefixClearTail acc Z bank cin src) ∧
    Challenge.gateSlots (prefixAny acc Z bank cin src)≤Challenge.gateSlots (earlyPrefixClearTail acc Z bank cin src) := by
  by_cases h : src.length=130
  · simpa only [prefixAny,gain,if_pos h] using prefix_resources acc Z bank cin src hacc h hf (hf6 h)
  · simp only [prefixAny,gain,if_neg h,Nat.add_zero]
    exact ⟨trivial,trivial,Finset.Subset.refl _,le_rfl⟩

def totalGain (w : Nat) (fs : List MeasuredSquareFold) : Nat :=
  if Acc.EarlyH w fs then match fs with | a::_ => gain a.src | [] => 0 else 0

theorem sunbuild_resources (acc Z bank : List Wire) (cin : Wire) (w : Nat)
    (hacc : acc.length=w) (fs : List MeasuredSquareFold) (hz : 154≤Z.length) (hb : 160≤bank.length) :
    toffoliCount (sunbuildKnown acc Z bank cin w fs)+totalGain w fs=toffoliCount (sunbuildTail acc Z bank cin w fs) ∧
    measurementCount (sunbuildKnown acc Z bank cin w fs)=measurementCount (sunbuildTail acc Z bank cin w fs) ∧
    wires (sunbuildKnown acc Z bank cin w fs)⊆wires (sunbuildTail acc Z bank cin w fs) ∧
    Challenge.gateSlots (sunbuildKnown acc Z bank cin w fs)≤Challenge.gateSlots (sunbuildTail acc Z bank cin w fs) := by
  by_cases h : Acc.EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩:=Acc.earlyH_info w fs h
    have fit : Acc.FitsLen Z bank 163 (Acc.earlyTerm src false 10) := by
      constructor <;> simp only [Acc.earlyTerm] <;> omega
    have fit6 : src.length=130 → Acc.FitsLen Z bank 163 (Acc.earlyTerm src true 6) := by
      intro hs
      constructor <;> simp only [Acc.earlyTerm] <;> omega
    have p:=prefixAny_resources acc Z bank cin src hacc fit fit6
    simpa only [sunbuildKnown,sunbuildTail,totalGain,if_pos h,earlyUnbuildKnown,earlyUnbuildTail,Acc.earlyTerm_src,
      toffoliCount_append,measurementCount_append,wires_append,Challenge.gateSlots_append] using
      (show toffoliCount (unbuildTail acc Z bank cin 163 src tail)+toffoliCount (prefixAny acc Z bank cin src)+gain src=
          toffoliCount (unbuildTail acc Z bank cin 163 src tail)+toffoliCount (earlyPrefixClearTail acc Z bank cin src) ∧
        measurementCount (unbuildTail acc Z bank cin 163 src tail)+measurementCount (prefixAny acc Z bank cin src)=
          measurementCount (unbuildTail acc Z bank cin 163 src tail)+measurementCount (earlyPrefixClearTail acc Z bank cin src) ∧
        wires (unbuildTail acc Z bank cin 163 src tail)∪wires (prefixAny acc Z bank cin src)⊆
          wires (unbuildTail acc Z bank cin 163 src tail)∪wires (earlyPrefixClearTail acc Z bank cin src) ∧
        Challenge.gateSlots (unbuildTail acc Z bank cin 163 src tail)+Challenge.gateSlots (prefixAny acc Z bank cin src)≤
          Challenge.gateSlots (unbuildTail acc Z bank cin 163 src tail)+Challenge.gateSlots (earlyPrefixClearTail acc Z bank cin src) from
        ⟨by omega,by omega,Finset.union_subset_union (Finset.Subset.refl _) p.2.2.1,by omega⟩)
  · simp only [sunbuildKnown,sunbuildTail,totalGain,if_neg h,Nat.add_zero]
    exact ⟨trivial,trivial,Finset.Subset.refl _,le_rfl⟩

theorem fillOut_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    :
    toffoliCount (fillOutKnown L a)+totalGain 163 a.terms=toffoliCount (fillOutTail L a) ∧
    measurementCount (fillOutKnown L a)=measurementCount (fillOutTail L a) ∧
    wires (fillOutKnown L a)⊆wires (fillOutTail L a) ∧
    Challenge.gateSlots (fillOutKnown L a)≤Challenge.gateSlots (fillOutTail L a) := by
  have p:=sunbuild_resources (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms (by rw [(acc_lengths L hw).2.1]) (by rw [(acc_lengths L hw).2.2.1])
  simp only [fillOutKnown,fillOutTail,toffoliCount_append,measurementCount_append,wires_append,Challenge.gateSlots_append]
  refine ⟨by omega,by omega,?_,by omega⟩
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) p.2.2.1) (Finset.Subset.refl _))) (Finset.Subset.refl _)

#print axioms prefix_resources
#print axioms sunbuild_resources
#print axioms fillOut_resources
end ECDSAAdd.Entrant.SourceFourPrefix130Develop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.SourceFourPrefix130Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout CodexCKAccTail OwnDiagAll12Square CKAcc

theorem prefixAny_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length≤130)
    (hf4 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 4))
    (hf10 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 10))
    (hf6 : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src true 6)) :
    GatePhysical (prefixAny acc Z bank cin src) := by
  by_cases hs : src.length=130
  · have old := earlyPrefixClearTail_physical acc Z bank cin src hacc hsrc hf4 hf10 hf6
    simp only [earlyPrefixClearTail,gatePhysical_append] at old
    have a := SourceAddFour130Develop.add_physical acc Z bank cin src hacc hs hf6
    have p := SourceTail130Develop.tail_physical acc Z bank cin src hacc hs hf10
    simpa only [prefixAny,if_pos hs,clearPrefix,gatePhysical_append] using And.intro (And.intro a p) old.2
  · simpa only [prefixAny,if_neg hs] using earlyPrefixClearTail_physical acc Z bank cin src hacc hsrc hf4 hf10 hf6

theorem sunbuildKnown_physical (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Acc.Fits acc Z bank cin w f) :
    GatePhysical (sunbuildKnown acc Z bank cin w fs) := by
  by_cases h : Acc.EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩ := Acc.earlyH_info w fs h
    have p := prefixAny_physical acc Z bank cin src hacc hlen
      (hf _ (by simp)) (hf _ (by simp)) (hf _ (by simp))
    have u := unbuildTail_physical acc Z bank cin src hacc tail (fun f hf' => hf f (by simp [hf']))
    simpa only [sunbuildKnown,if_pos h,earlyUnbuildKnown,gatePhysical_append] using And.intro u p
  · have old := (Acc.sbuild_physical acc Z bank cin w hacc fs hf).2
    simpa only [sunbuildKnown,Acc.sunbuild,if_neg h] using old

theorem fillKnown_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (fillInK L a) ∧ GatePhysical (fillOutKnown L a) := by
  refine ⟨(OwnDiagAll12Square.fillK_physical L hw hn a cnt ok cntP okP).1,?_⟩
  have full := accFoldQ_physical L hw hn a cnt ok cntP okP
  simp only [accFoldQ,gatePhysical_append] at full
  have out := full.2
  simp only [fillOut,gatePhysical_append] at out
  have k := sunbuildKnown_physical (accReg L) (accZ L) (accBank L) L.core.cin 163
    (acc_lengths L hw).1 a.terms (fun f hf => fits_of L hw hn f (cnt f hf) (ok f hf))
  simp only [fillOutKnown,gatePhysical_append]
  exact ⟨⟨out.1.1,⟨⟨out.1.2.1.1,k⟩,out.1.2.2⟩⟩,out.2⟩

#print axioms fillKnown_physical
end ECDSAAdd.Entrant.SourceFourPrefix130Develop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceFourPrefix130Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout CodexCKAccTail OwnDiagAll12Square CKAcc

theorem fillKnown_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) :
    (toffoliCount (fillInK L a)≤toffoliCount (fillIn L a) ∧ measurementCount (fillInK L a)=measurementCount (fillIn L a) ∧
      wires (fillInK L a)⊆wires (fillIn L a) ∧ Challenge.gateSlots (fillInK L a)≤Challenge.gateSlots (fillIn L a)) ∧
    (toffoliCount (fillOutKnown L a)≤toffoliCount (fillOut L a) ∧ measurementCount (fillOutKnown L a)=measurementCount (fillOut L a) ∧
      wires (fillOutKnown L a)⊆wires (fillOut L a) ∧ Challenge.gateSlots (fillOutKnown L a)≤Challenge.gateSlots (fillOut L a)) := by
  have old:=fillTail_rel L hw a ok
  have p:=fillOut_resources L hw a
  exact ⟨old.1,by omega,by omega,p.2.2.1.trans old.2.2.2.1,by omega⟩

theorem totalGain_early (src : List Wire) (rest : List MeasuredSquareFold) (hs : src.length=130) :
    totalGain 163 (Acc.earlyTerm src false 4::Acc.earlyTerm src false 10::Acc.earlyTerm src true 6::rest)=127 := by
  simp [totalGain,Acc.EarlyH,Acc.earlyTerm,gain,hs]

theorem eItem_gain (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    totalGain 163 (ControlLoan1589BFFold.eItem L).terms=127 := by
  apply totalGain_early
  simp [ControlLoan1589BFFold.eReg,hw.core.product]

theorem cItem_gain (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    totalGain 163 (accCItem L).terms=127 := by
  apply totalGain_early
  simp [hw.core.product]

#print axioms fillKnown_rel
end ECDSAAdd.Entrant.SourceFourPrefix130Develop
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
  OwnDiagAll12Square.fillInK L a++qprogTq L.measuredCore SquareReduction.p++SourceFourPrefix130Develop.fillOutKnown L a

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
  have hun := SourceFourPrefix130Develop.fillOutKnown_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v ((m.drop mb).drop mk) frame2
  refine ⟨eo.1.trans (ek.1.trans eu.1),?_,?_⟩
  · have e : regValue L.core.out (run (SourceFourPrefix130Develop.fillOutKnown L a) ((m.drop mb).drop mk) v).basis=
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
  OwnDiagAll12Square.fillInK L a++qprog4Tq L.measuredCore SquareReduction.p++SourceFourPrefix130Develop.fillOutKnown L a

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
  have r := SourceFourPrefix130Develop.fillKnown_rel L hw a ok
  simp only [accFoldQ4KTq,accFoldQ4Tq,toffoliCount_append,measurementCount_append,wires_append,
    Challenge.gateSlots_append]
  refine ⟨by omega,by omega,?_,by omega⟩
  exact Finset.union_subset_union (Finset.union_subset_union r.1.2.2.1 (Finset.Subset.refl _)) r.2.2.2.1

theorem accFoldQ4KTq_counts_early (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (src : List Wire) (hsrc : src.length≤130) (he : a.terms=earlyHTerms src)
    (ok : ∀f∈a.terms,TermOK f) :
    toffoliCount (accFoldQ4KTq L a)+31+SourceFourPrefix130Develop.totalGain 163 a.terms=toffoliCount (accFoldQ4Tq L a) := by
  have known:=SourceFourPrefix130Develop.fillOut_resources L hw a
  have e : a.terms=Acc.earlyTerm src false 4::Acc.earlyTerm src false 10::Acc.earlyTerm src true 6::
      Acc.earlyTerm src false 32::[] := by rw [he]; rfl
  have c := CodexCKAccTail.tail_counts_early (accReg L) (accZ L) (accBank L) L.core.cin src
    (acc_lengths L hw).1 hsrc (Acc.earlyTerm src false 32) []
    (by simp [CKAcc.IsT32,Acc.earlyTerm]) (fun f hf => fitsLen_of L hw f (ok f (by rw [e]; exact hf)))
  rw [← e] at c
  simp only [accFoldQ4KTq,accFoldQ4Tq,OwnDiagAll12Square.fillInK,fillIn,SourceFourPrefix130Develop.fillOutKnown,CodexCKAccTail.fillOutTail,fillOut,
    toffoliCount_append] at known ⊢
  omega

theorem accFoldQ4KTq_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQ4KTq L a) := by
  have old := accFoldQ4_physicalTq L a (accFoldQ_physicalTq L hw hn a cnt ok cntP okP)
  have k := SourceFourPrefix130Develop.fillKnown_physical L hw hn a cnt ok cntP okP
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
    (maskedConstant g (accReg L) cFlipK++SourceFourPrefix130Develop.fillOutKnown L a)))


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
  have hun := SourceFourPrefix130Develop.fillOutKnown_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v1 (m3.drop mc) frame2
  refine ⟨eo.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have e : regValue L.core.out (run (SourceFourPrefix130Develop.fillOutKnown L a) (m3.drop mc) v1).basis=
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
  have r := SourceFourPrefix130Develop.fillKnown_rel L hw a ok
  simp only [accFoldQFKTq,accFoldQFTq,toffoliCount_append,measurementCount_append,wires_append,
    Challenge.gateSlots_append]
  refine ⟨by omega,by omega,?_,by omega⟩
  exact Finset.union_subset_union r.1.2.2.1 (Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union (Finset.Subset.refl _) r.2.2.2.1)))


theorem accFoldQFK_countsCTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire)
    (ok : ∀f∈(accCItem L).terms,TermOK f) :
    toffoliCount (accFoldQFKTq L g (accCItem L))+158=toffoliCount (accFoldQFTq L g (accCItem L)) ∧
    measurementCount (accFoldQFKTq L g (accCItem L))=measurementCount (accFoldQFTq L g (accCItem L)) := by
  have known:=SourceFourPrefix130Develop.fillOut_resources L hw (accCItem L)
  rw [SourceFourPrefix130Develop.cItem_gain L hw] at known
  have r := SourceFourPrefix130Develop.fillKnown_rel L hw (accCItem L) ok
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
  simp only [accFoldQFKTq,accFoldQFTq,fillInK,fillIn,SourceFourPrefix130Develop.fillOutKnown,CodexCKAccTail.fillOutTail,fillOut,toffoliCount_append,measurementCount_append] at known ⊢
  simp only [accFoldQFKTq,accFoldQFTq,toffoliCount_append,measurementCount_append] at r
  constructor <;> omega


theorem accFoldQFK_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQFKTq L g a) := by
  have old := accFoldQF_physicalTq L hw hn g hg a cnt ok cntP okP
  have k := SourceFourPrefix130Develop.fillKnown_physical L hw hn a cnt ok cntP okP
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
    toffoliCount (bodyCKTq L g)+158=toffoliCount (bodyCTq L g) ∧
    measurementCount (bodyCKTq L g)=measurementCount (bodyCTq L g) ∧
    ECDSAAdd.wires (bodyCKTq L g)⊆ECDSAAdd.wires (bodyCTq L g) ∧
    Challenge.gateSlots (bodyCKTq L g)≤Challenge.gateSlots (bodyCTq L g) := by
  have st := bodyC_static L hw
  have qk := accFoldQFK_countsCTq L hw g st.2.2.1
  have r := accFoldQFK_relTq L hw g (accCItem L) st.2.2.1
  simp only [bodyCKTq,bodyCTq,toffoliCount_append,measurementCount_append,wires_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,Finset.union_subset_union (Finset.Subset.refl _) r.2.2.1,by omega⟩


theorem bodyCK_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (bodyCKTq L g)=2230 ∧ measurementCount (bodyCKTq L g)=2390 := by
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
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTailDevelop
open Arithmetic Arithmetic.KnownOutputAdder Arithmetic.CuccaroStreamedSquareWideLayout MixedLiteralAdderDevelop

abbrev one : MappedBit := ⟨none,true⟩
def negDesired (src : List Wire) : List MappedBit := mappedRead (src.drop 6) true++List.replicate 7 one
def program (src Z ys carry : List Wire) (cin : Wire) : Program :=
  KnownSubDevelop.knownSub (mappedRead (src++Z.take 1) false) (negDesired src) ys carry cin

theorem neg_value (src : List Wire) (s : BasisState) (hs : src.length=128) :
    mappedValue (negDesired src) s=2^129-1-regValue src s/64 := by
  rw [negDesired,mappedValue_append,mappedRead_complement,
    regValue_drop_div src 6 (by omega)]
  simp only [mappedRead,List.length_map,List.length_drop,hs]
  norm_num [one,MappedBit.value,mappedValue,List.replicate_succ]
  have h:=regValue_lt src s
  rw [hs] at h
  omega

theorem neg_wires (src : List Wire) : mappedWires (negDesired src)=src.drop 6 := by
  have app (a b : List MappedBit) : mappedWires (a++b)=mappedWires a++mappedWires b := by simp [mappedWires,List.flatMap_append]
  rw [negDesired,app,mappedRead_wires]
  simp [mappedWires,one,List.flatMap_replicate]

theorem arithmetic (H : Nat) (hH : H<2^128) :
    (H+(2^129-1-1040*H/1024))%2^129=2^129-1-H/64 := by
  have eq : 1040*H/1024=H+H/64 := by omega
  rw [eq]
  omega

theorem run_eq_sub (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=128) (hzl : 1≤Z.length) (hy : ys.length=129) (hc : carry.length=128)
    (hn : (cin::((src++Z.take 1)++ys++carry)).Nodup)
    (s : State) (m : List Bool) (hz : ∀q∈Z,s.basis q=false)
    (hcarry : ∀q∈carry,s.basis q=false) (hcin : s.basis cin=false)
    (H : Nat) (hH : H<2^128) (hsrc : regValue src s.basis=H)
    (hys : regValue ys s.basis=1040*H/1024) :
    run (program src Z ys carry cin) m s=run (subInPlace (src++Z.take 1) ys carry cin) m s := by
  have geo:=read_geometry (src++Z.take 1) ys carry cin hn
  have outside (q : Wire) (hq : q∈src++Z.take 1) : q∉ys := by
    intro bad
    exact geo.2 q hq (List.mem_cons_of_mem _ (List.mem_append_left _ bad))
  have srcAway (q : Wire) (hq : q∈src) : q∉ys := outside q (List.mem_append_left _ hq)
  have caway : cin∉ys := by intro bad;exact (List.nodup_cons.mp geo.1).1 (List.mem_append_left _ bad)
  have zv : regValue (Z.take 1) s.basis=0 := (regValue_zero _ _).mpr (fun q hq=>hz q (List.mem_of_mem_take hq))
  have sv : mappedValue (mappedRead (src++Z.take 1) false) (flipped ys s).basis=H := by
    rw [mappedRead_value,regValue_congr (src++Z.take 1) _ s.basis
      (by intro q hq;simp only [flipped,if_neg (outside q hq)]),regValue_append,hsrc,zv,Nat.mul_zero,Nat.add_zero]
  have dv : mappedValue (negDesired src) (flipped ys s).basis=2^129-1-H/64 := by
    rw [neg_value src _ hs,regValue_congr src _ s.basis
      (by intro q hq;simp only [flipped,if_neg (srcAway q hq)]),hsrc]
  have yv : regValue ys (flipped ys s).basis=2^129-1-1040*H/1024 := by
    rw [regValue_congr ys _ (fun q=>!s.basis q) (by intro q hq;simp only [flipped,if_pos hq]),
      regValue_complement,hy,hys]
  have hl : (mappedRead (src++Z.take 1) false).length=ys.length := by simp [mappedRead,hs,hy];omega
  have hd : (negDesired src).length=ys.length := by simp [negDesired,mappedRead,hs,hy]
  have ready : KnownOutputAdder.Ready (mappedRead (src++Z.take 1) false) (negDesired src) ys
      ((flipped ys s).basis cin) (flipped ys s).basis := by
    apply ready_of_value _ _ _ _ _ hl hd
    rw [sv,dv,yv,show (flipped ys s).basis cin=false by simp only [flipped,if_neg caway,hcin],
      Bool.toNat_false,Nat.add_zero,hy]
    exact (arithmetic H hH).symm
  have eq:=KnownSubDevelop.sub_eq (mappedRead (src++Z.take 1) false) (negDesired src) ys carry cin geo.1
    (by rw [mappedRead_wires];exact geo.2)
    (by rw [neg_wires];intro q hq;exact geo.2 q (List.mem_append_left _ (List.mem_of_mem_drop hq)))
    hl hd (by rw [hc,hy]) s m hcarry ready
  exact eq.trans (congrArg (fun p=>run p m s) (read_sub_eq _ _ _ _))
#print axioms neg_value
#print axioms arithmetic
#print axioms run_eq_sub
end ECDSAAdd.Entrant.SourceTailDevelop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTailDevelop
open Arithmetic

def tail (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  program src Z ((acc.take 139).drop 10) (bank.take 128) cin

theorem tail_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 10))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (1040*regValue src base)) (tail acc Z bank cin src)
      (SquareFrame acc base (16*regValue src base)) := by
  let f:=Acc.earlyTerm src false 10
  let H:=regValue src base
  have hH : H<2^128 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have old:=Acc.op_prefix_triple acc Z bank cin 163 139 f hacc (by decide) hf
    (by simp [f,Acc.earlyTerm,hsrc]) base hz hb hi true (1040*H)
    (by omega) (by simp only [f,Acc.earlyTerm];dsimp [H];omega)
  have value : Acc.step base true (1040*H) f=16*H := by
    norm_num [Acc.step,f,Acc.earlyTerm]
    dsimp [H]
    omega
  rw [value] at old
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 f (by decide) hf (by simp [f,Acc.earlyTerm,hsrc])
  have len : (acc.take 139).length=139 := by simp [hacc]
  have rawEq : Acc.op (acc.take 139) Z bank cin 139 true f=
      subInPlace (src++Z.take 1) ((acc.take 139).drop 10) (bank.take 128) cin := by
    simp [Acc.op,Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc]
  intro s m hs
  have away (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h:=List.nodup_iff_count.mp hf.nd q
    have a:=List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b:=List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
      omega
  have same (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : s.basis q=base q := hs.2 q (away q hq)
  have pref:=regValue_take_drop_of_lt acc 139 (1040*H) s.basis (by omega) hs.1 (by omega)
  have sy : regValue ((acc.take 139).drop 10) s.basis=1040*H/1024 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
    rfl
  have sh : regValue src s.basis=H := regValue_congr src _ base (fun q hq=>same q (Or.inl (by simp [hq])))
  have sz (q : Wire) (hq : q∈Z) : s.basis q=false :=
    (same q (Or.inl (by simp [hq]))).trans (hz q hq)
  have sb (q : Wire) (hq : q∈bank.take 128) : s.basis q=false :=
    (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
  have si : s.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd' : (cin::((src++Z.take 1)++(acc.take 139).drop 10++bank.take 128)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd
  have zl : 1≤Z.length := by
    have h:=fit.zpad
    simpa [f,Acc.earlyTerm,hsrc] using h
  have bl : (bank.take 128).length=128 := by
    have h:=fit.bankLen
    simp only [f,Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have e:=run_eq_sub src Z ((acc.take 139).drop 10) (bank.take 128) cin hsrc zl
    (by simp [len]) bl nd' s m sz sb si H hH sh sy
  change run (tail acc Z bank cin src) m s=_ at e
  rw [e,←rawEq]
  exact old s m hs
#print axioms tail_triple
end ECDSAAdd.Entrant.SourceTailDevelop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTailDevelop
open Arithmetic CodexNarrowTail

def unbuild (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)++
    Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)++
    tail acc Z bank cin src++Acc.seedOp acc Z 163 (Acc.earlyTerm src false 4)

theorem unbuild_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (4294968272*regValue src base)) (unbuild acc Z bank cin src)
      (SquareFrame acc base 0) := by
  have tm := terms_mem src
  have hf4 := hf _ tm.1
  have hf10 := hf _ tm.2.1
  have hf6 := hf _ tm.2.2.1
  have hf32 := hf _ tm.2.2.2
  let H := regValue src base
  have hH : H<2^128 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have top : Triple (SquareFrame acc base (4294968272*H))
      (CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32))
      (SquareFrame acc base (976*H)) := by
    have h := CodexKnownOnesTail.accSub_prefix_triple acc Z bank cin 163 161 106 (Acc.earlyTerm src false 32) hacc
      (by norm_num [Acc.earlyTerm]) hf32 (by simp only [Acc.earlyTerm]; omega)
      (by norm_num [Acc.earlyTerm]) base hz hb hi (4294968272*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm];dsimp [H];omega)
      (by simpa only [Acc.earlyTerm] using (clear_sub32_range H hH).2.2)
    have value : Acc.step base true (4294968272*H) (Acc.earlyTerm src false 32)=976*H := by
      have e : regValue src base*2^32=4294967296*H := by dsimp only [H]; ring
      simp only [Acc.step,Acc.earlyTerm,if_true]
      rw [e]
      omega
    rw [value] at h
    exact h
  have add : Triple (SquareFrame acc base (976*H))
      (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6))
      (SquareFrame acc base (1040*H)) := by
    have h := Acc.op_prefix_triple acc Z bank cin 163 139 (Acc.earlyTerm src true 6) hacc
      (by norm_num [Acc.earlyTerm]) hf6 (by simp only [Acc.earlyTerm]; omega) base hz hb hi false (976*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm] at hH ⊢;dsimp [H] at *;omega)
    have value : Acc.step base false (976*H) (Acc.earlyTerm src true 6)=1040*H := by
      norm_num [Acc.step,Acc.earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  have sub : Triple (SquareFrame acc base (1040*H)) (tail acc Z bank cin src)
      (SquareFrame acc base (16*H)) := tail_triple acc Z bank cin src hacc hsrc hf10 base hz hb hi
  have seed := Acc.seed_triple acc Z bank cin 163 (Acc.earlyTerm src false 4) hacc hf4 base hz
    (16*H) 0 (Or.inr (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
  exact ((top.seq add).seq sub).seq seed


theorem unbuild_eq_old (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz : ∀q∈Z,s.basis q=false) (hb : ∀q∈bank,s.basis q=false)
    (hi : s.basis cin=false) (ha : regValue acc s.basis=4294968272*regValue src s.basis) :
    run (unbuild acc Z bank cin src) m s=run (CodexNarrowTail.unbuild8 acc Z bank cin src) m s := by
  have start : SquareFrame acc s.basis (4294968272*regValue src s.basis) s.basis := ⟨ha,fun _ _=>rfl⟩
  have a:=unbuild_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s m start
  have b:=CodexNarrowTail.unbuild8_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s m start
  apply State.extensionality _ _
  · exact a.1.trans b.1.symm
  funext q
  by_cases hq : q∈acc
  · exact ((regValue_zero _ _).mp a.2.1 q hq).trans ((regValue_zero _ _).mp b.2.1 q hq).symm
  · exact (a.2.2 q hq).trans (b.2.2 q hq).symm
#print axioms unbuild_triple
#print axioms unbuild_eq_old
end ECDSAAdd.Entrant.SourceTailDevelop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTailDevelop
open Arithmetic Arithmetic.KnownOutputAdder

theorem prepare_read_slots (a : Wire) (desired : MappedBit) (y c : Wire) :
    Challenge.gateSlots (prepare ⟨some a,false⟩ desired y c)≤4 := by
  cases desired with
  | mk w flip => cases w <;> cases flip <;>
    simp [prepare,xorBit,Challenge.gateSlots,Challenge.instructionSlots]

theorem slots_read (bits sums : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (hRead : ∀b∈bits,∃a,b=({wire:=some a,flip:=false} : MappedBit)) :
    Challenge.gateSlots (KnownOutputAdder.program bits ys sums cs cin)≤10*bits.length := by
  revert hRead
  induction bits,ys,sums,cs,cin using KnownOutputAdder.program.induct with
  | case1 b b' bs y y' ys d d' ds c cs cin ih =>
    intro hb
    have ht : ∀z∈b'::bs,∃a,z=({wire:=some a,flip:=false} : MappedBit) :=
      fun z hz=>hb z (List.mem_cons_of_mem _ hz)
    have it:=ih ht
    obtain ⟨a,rfl⟩:=hb b (by simp)
    obtain ⟨a',rfl⟩:=hb b' (by simp)
    have hp:=prepare_read_slots a' d' y' c
    have he : Challenge.gateSlots (mappedEraseCarry ⟨some a,false⟩ y cin c)=4 := rfl
    have hs : Challenge.gateSlots (mappedSum ⟨some a,false⟩ y cin)=2 := rfl
    simp only [KnownOutputAdder.program,Challenge.gateSlots_append,List.length_cons] at it ⊢
    omega
  | case2 b y d cs cin =>
    intro hb
    obtain ⟨a,rfl⟩:=hb b (by simp)
    simp [KnownOutputAdder.program,mappedSum,Challenge.gateSlots,Challenge.instructionSlots]
  | case3 bits ys sums cs cin other => intro hb;simp [KnownOutputAdder.program]

theorem slots_read_raw (xs ys : List Wire) (sums : List MappedBit) (cs : List Wire) (cin : Wire) :
    Challenge.gateSlots (KnownOutputAdder.program (mappedRead xs false) ys sums cs cin)≤10*xs.length := by
  have h:=slots_read (mappedRead xs false) sums ys cs cin (by
    intro b hb
    change b∈xs.map (fun q=>({wire:=some q,flip:=false} : MappedBit)) at hb
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
    exact ⟨a,rfl⟩)
  simpa [mappedRead] using h

theorem program_slots (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=128) (hz : 1≤Z.length) (hy : ys.length=129) :
    Challenge.gateSlots (program src Z ys carry cin)≤1548 := by
  have hp:=slots_read_raw (src++Z.take 1) ys (negDesired src) carry cin
  have hx : (src++Z.take 1).length=129 := by simp [hs];omega
  rw [hx] at hp
  simp only [program,KnownSubDevelop.knownSub,Challenge.gateSlots_append,Baselines.notRegister_gateSlots,hy]
  omega
#print axioms slots_read
#print axioms program_slots
end ECDSAAdd.Entrant.SourceTailDevelop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTailDevelop
open Arithmetic

private theorem old_head_relation (low : Nat) (a a' b b' cin c : Wire) :
    Challenge.gateSlots (CodexKnownOnesTail.head low a a' b b' cin c)=
      3*toffoliCount (CodexKnownOnesTail.head low a a' b b' cin c)+3 ∧
    measurementCount (CodexKnownOnesTail.head low a a' b b' cin c)=0 := by
  by_cases h : low≤1 <;>
    simp [CodexKnownOnesTail.head,h,majority,Challenge.gateSlots,Challenge.instructionSlots,toffoliCount,measurementCount]

theorem old_add_relation (low : Nat) (x y carry : List Wire) (cin : Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    Challenge.gateSlots (CodexKnownOnesTail.addTail low x y carry cin)=
      3*toffoliCount (CodexKnownOnesTail.addTail low x y carry cin)+
      9*measurementCount (CodexKnownOnesTail.addTail low x y carry cin)+2 := by
  induction y generalizing low x carry cin with
  | nil => simp at hc
  | cons b ys ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
      cases ys with
      | nil =>
        cases as with
        | nil => simp [CodexKnownOnesTail.addTail,Challenge.gateSlots,Challenge.instructionSlots,toffoliCount,measurementCount]
        | cons a' as => simp at hx
      | cons b' ys =>
        cases as with
        | nil => simp at hx
        | cons a' as =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have it:=ih (low:=low-1) (x:=a'::as) (carry:=cs) (cin:=c)
              (by simp only [List.length_cons] at hx ⊢;omega)
              (by simp only [List.length_cons] at hc ⊢;omega)
            have hd:=old_head_relation low a a' b b' cin c
            have et : toffoliCount (eraseCarry a b cin c)=0 := rfl
            have em : measurementCount (eraseCarry a b cin c)=1 := rfl
            have es : Challenge.gateSlots (eraseCarry a b cin c)=4 := rfl
            have st : toffoliCount [.CX a b,.CX cin b]=0 := rfl
            have sm : measurementCount [.CX a b,.CX cin b]=0 := rfl
            have ss : Challenge.gateSlots [.CX a b,.CX cin b]=2 := rfl
            simp only [CodexKnownOnesTail.addTail,Challenge.gateSlots_append,toffoliCount_append,
              measurementCount_append,hd.2,et,em,es,st,sm,ss]
            omega

theorem old_program_relation (low : Nat) (x y carry : List Wire) (cin : Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    Challenge.gateSlots (CodexKnownOnesTail.program low x y carry cin)=
      3*toffoliCount (CodexKnownOnesTail.program low x y carry cin)+
      9*measurementCount (CodexKnownOnesTail.program low x y carry cin)+2+2*y.length := by
  have h:=old_add_relation low x y carry cin hx hc
  have n:=notRegister_counts y
  simp only [CodexKnownOnesTail.program,Challenge.gateSlots_append,Baselines.notRegister_gateSlots,
    toffoliCount_append,measurementCount_append,n.1,n.2,Nat.zero_add,Nat.add_zero]
  omega

theorem old_program_slots129 (x y carry : List Wire) (cin : Wire)
    (hy : y.length=129) (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    Challenge.gateSlots (CodexKnownOnesTail.program 122 x y carry cin)=1775 := by
  have h:=old_program_relation 122 x y carry cin hx hc
  have count:=CodexKnownOnesTail.counts 127 122 x y carry cin (by rw [hy]) hx hc
  rw [count.1,count.2,hy] at h
  norm_num at h
  exact h
#print axioms old_add_relation
#print axioms old_program_slots129
end ECDSAAdd.Entrant.SourceTailDevelop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTailDevelop
open Arithmetic

theorem old_add_wires (low : Nat) (x y carry : List Wire) (cin : Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    wires (CodexKnownOnesTail.addTail low x y carry cin)=(cin::(x++y++carry)).toFinset := by
  induction y generalizing low x carry cin with
  | nil => simp at hc
  | cons b ys ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
      cases ys with
      | nil =>
        cases as with
        | nil =>
          have cn : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
          subst carry
          ext q
          simp [CodexKnownOnesTail.addTail,wires,Instr.wires]
        | cons a' as => simp at hx
      | cons b' ys =>
        cases as with
        | nil => simp at hx
        | cons a' as =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have it:=ih (low:=low-1) (x:=a'::as) (carry:=cs) (cin:=c)
              (by simp only [List.length_cons] at hx ⊢;omega)
              (by simp only [List.length_cons] at hc ⊢;omega)
            rw [CodexKnownOnesTail.addTail]
            simp only [wires_append,it]
            ext q
            by_cases h : low≤1 <;>
              simp [CodexKnownOnesTail.head,h,majority,eraseCarry,wires,Instr.wires,correctionWires] <;> tauto

theorem old_program_wires (low : Nat) (x y carry : List Wire) (cin : Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    wires (CodexKnownOnesTail.program low x y carry cin)=(cin::(x++y++carry)).toFinset := by
  rw [CodexKnownOnesTail.program,wires_append,wires_append,notRegister_wires,
    old_add_wires low x y carry cin hx hc]
  ext q
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto
#print axioms old_add_wires
#print axioms old_program_wires
end ECDSAAdd.Entrant.SourceTailDevelop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTailDevelop
open Arithmetic Arithmetic.KnownOutputAdder

theorem word_length (src Z : List Wire) (hs : src.length=128) (hz : 1≤Z.length) :
    (src++Z.take 1).length=129 := by simp [hs];omega

theorem program_counts (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=128) (hz : 1≤Z.length) (hy : ys.length=129) (hc : carry.length=128) :
    toffoliCount (program src Z ys carry cin)=0 ∧ measurementCount (program src Z ys carry cin)=128 := by
  have p:=KnownSubDevelop.sub_counts (mappedRead (src++Z.take 1) false) (negDesired src) ys carry cin
    (by rw [mappedRead_length,word_length src Z hs hz,hy])
    (by simp [negDesired,mappedRead,hs,hy]) (by rw [hc,hy])
  simpa [program,hy] using p

private theorem bit_member (bits : List MappedBit) (b : MappedBit) (hb : b∈bits)
    (q : Wire) (hq : q∈b.wire) : q∈mappedWires bits := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩

theorem program_physical (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=128) (hz : 1≤Z.length) (hy : ys.length=129) (hc : carry.length=128)
    (hn : (cin::((src++Z.take 1)++ys++carry)).Nodup) : GatePhysical (program src Z ys carry cin) := by
  have g:=MixedLiteralAdderDevelop.read_geometry (src++Z.take 1) ys carry cin hn
  apply KnownSubDevelop.sub_physical _ _ _ _ _
    (by rw [mappedRead_length,word_length src Z hs hz,hy])
    (by simp [negDesired,mappedRead,hs,hy]) (by rw [hc,hy]) g.1
  · intro b hb q hq
    have mem:=bit_member (mappedRead (src++Z.take 1) false) b hb q hq
    rw [mappedRead_wires] at mem
    exact g.2 q mem
  · intro b hb q hq
    have mem:=bit_member (negDesired src) b hb q hq
    rw [neg_wires] at mem
    exact g.2 q (List.mem_append_left _ (List.mem_of_mem_drop mem))

theorem program_support_old (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=128) (hz : 1≤Z.length) (hy : ys.length=129) (hc : carry.length=128) :
    wires (program src Z ys carry cin)⊆wires (CodexKnownOnesTail.program 122 (src++Z.take 1) ys carry cin) := by
  rw [old_program_wires 122 _ _ _ _ (by rw [word_length src Z hs hz,hy]) (by rw [hc,hy])]
  have p:=KnownSubDevelop.sub_support (mappedRead (src++Z.take 1) false) (negDesired src) ys carry cin
  rw [mappedRead_wires,neg_wires] at p
  intro q hq
  have mem:=p hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at mem ⊢
  rcases mem with h|h|h|h|h|h
  · tauto
  · tauto
  · have old:=List.mem_of_mem_drop h
    tauto
  · tauto
  · tauto
  · tauto

theorem program_slots_old (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=128) (hz : 1≤Z.length) (hy : ys.length=129) (hc : carry.length=128) :
    Challenge.gateSlots (program src Z ys carry cin)≤
      Challenge.gateSlots (CodexKnownOnesTail.program 122 (src++Z.take 1) ys carry cin) := by
  rw [old_program_slots129 _ _ _ _ hy (by rw [word_length src Z hs hz,hy]) (by rw [hc,hy])]
  exact (program_slots src Z ys carry cin hs hz hy).trans (by decide : 1548≤1775)

theorem program_resources (src Z ys carry : List Wire) (cin : Wire)
    (hs : src.length=128) (hz : 1≤Z.length) (hy : ys.length=129) (hc : carry.length=128) :
    toffoliCount (program src Z ys carry cin)+121=toffoliCount (CodexKnownOnesTail.program 122 (src++Z.take 1) ys carry cin) ∧
    measurementCount (program src Z ys carry cin)=measurementCount (CodexKnownOnesTail.program 122 (src++Z.take 1) ys carry cin) ∧
    wires (program src Z ys carry cin)⊆wires (CodexKnownOnesTail.program 122 (src++Z.take 1) ys carry cin) ∧
    Challenge.gateSlots (program src Z ys carry cin)≤Challenge.gateSlots (CodexKnownOnesTail.program 122 (src++Z.take 1) ys carry cin) := by
  have a:=program_counts src Z ys carry cin hs hz hy hc
  have b:=CodexKnownOnesTail.counts 127 122 (src++Z.take 1) ys carry cin (by rw [hy])
    (by rw [word_length src Z hs hz,hy]) (by rw [hc,hy])
  refine ⟨?_,?_,program_support_old src Z ys carry cin hs hz hy hc,program_slots_old src Z ys carry cin hs hz hy hc⟩
  · rw [a.1,b.1]
    rfl
  · rw [a.2,b.2]
#print axioms program_counts
#print axioms program_physical
#print axioms program_resources
end ECDSAAdd.Entrant.SourceTailDevelop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceTailDevelop
open Arithmetic CodexNarrowTail

theorem tail_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : Acc.FitsLen Z bank 163 (Acc.earlyTerm src false 10)) :
    toffoliCount (tail acc Z bank cin src)+121=
      toffoliCount (CodexKnownOnesTail.accSub 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)) ∧
    measurementCount (tail acc Z bank cin src)=
      measurementCount (CodexKnownOnesTail.accSub 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)) ∧
    wires (tail acc Z bank cin src)⊆
      wires (CodexKnownOnesTail.accSub 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)) ∧
    Challenge.gateSlots (tail acc Z bank cin src)≤
      Challenge.gateSlots (CodexKnownOnesTail.accSub 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)) := by
  have fit:=CodexNarrowTail.narrowLen Z bank 139 (Acc.earlyTerm src false 10) hf (by decide)
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 1≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 128).length=128 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have h:=program_resources src Z ((acc.take 139).drop 10) (bank.take 128) cin hsrc zl
    (by simp [hacc]) bl
  simpa [tail,CodexKnownOnesTail.accSub,Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using h

theorem unbuild_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.FitsLen Z bank 163 f) :
    toffoliCount (unbuild acc Z bank cin src)=237 ∧ measurementCount (unbuild acc Z bank cin src)=388 ∧
    wires (unbuild acc Z bank cin src)⊆wires (CodexNarrowTail.unbuild8 acc Z bank cin src) ∧
    Challenge.gateSlots (unbuild acc Z bank cin src)≤Challenge.gateSlots (CodexNarrowTail.unbuild8 acc Z bank cin src) := by
  have t:=tail_resources acc Z bank cin src hacc hsrc (hf _ (CodexNarrowTail.terms_mem src).2.1)
  have old:=(CodexNarrowTail.build8_counts acc Z bank cin src hacc (by omega) hf).2
  have dt : toffoliCount (unbuild acc Z bank cin src)+121=toffoliCount (CodexNarrowTail.unbuild8 acc Z bank cin src) := by
    simp only [unbuild,CodexNarrowTail.unbuild8,toffoliCount_append]
    omega
  have dm : measurementCount (unbuild acc Z bank cin src)=measurementCount (CodexNarrowTail.unbuild8 acc Z bank cin src) := by
    simp only [unbuild,CodexNarrowTail.unbuild8,measurementCount_append]
    omega
  refine ⟨by omega,by omega,?_,?_⟩
  · simp only [unbuild,CodexNarrowTail.unbuild8,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) t.2.2.1) (Finset.Subset.refl _)
  · simp only [unbuild,CodexNarrowTail.unbuild8,Challenge.gateSlots_append]
    omega

theorem tail_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src false 10)) :
    GatePhysical (tail acc Z bank cin src) := by
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 (Acc.earlyTerm src false 10) (by decide) hf
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 1≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 128).length=128 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10) fit
  have nd' : (cin::((src++Z.take 1)++(acc.take 139).drop 10++bank.take 128)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using nd
  exact program_physical src Z ((acc.take 139).drop 10) (bank.take 128) cin hsrc zl (by simp [hacc]) bl nd'

theorem unbuild_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f) :
    GatePhysical (unbuild acc Z bank cin src) := by
  have old:=(CodexNarrowTail.build8_physical acc Z bank cin src hacc (by omega) hf).2
  have new:=tail_physical acc Z bank cin src hacc hsrc (hf _ (CodexNarrowTail.terms_mem src).2.1)
  simp only [unbuild,CodexNarrowTail.unbuild8,gatePhysical_append] at old ⊢
  exact ⟨⟨⟨old.1.1.1,old.1.1.2⟩,new⟩,old.2⟩
#print axioms tail_resources
#print axioms unbuild_resources
#print axioms unbuild_physical
end ECDSAAdd.Entrant.SourceTailDevelop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceAddFourDevelop
open Arithmetic CodexNarrowTail SourceTailDevelop

def unbuild (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)++
    add acc Z bank cin src++
    SourceTailDevelop.tail acc Z bank cin src++Acc.seedOp acc Z 163 (Acc.earlyTerm src false 4)

theorem unbuild_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (4294968272*regValue src base)) (unbuild acc Z bank cin src)
      (SquareFrame acc base 0) := by
  have tm := terms_mem src
  have hf4 := hf _ tm.1
  have hf10 := hf _ tm.2.1
  have hf6 := hf _ tm.2.2.1
  have hf32 := hf _ tm.2.2.2
  let H := regValue src base
  have hH : H<2^128 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have top : Triple (SquareFrame acc base (4294968272*H))
      (CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32))
      (SquareFrame acc base (976*H)) := by
    have h := CodexKnownOnesTail.accSub_prefix_triple acc Z bank cin 163 161 106 (Acc.earlyTerm src false 32) hacc
      (by norm_num [Acc.earlyTerm]) hf32 (by simp only [Acc.earlyTerm]; omega)
      (by norm_num [Acc.earlyTerm]) base hz hb hi (4294968272*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm];dsimp [H];omega)
      (by simpa only [Acc.earlyTerm] using (clear_sub32_range H hH).2.2)
    have value : Acc.step base true (4294968272*H) (Acc.earlyTerm src false 32)=976*H := by
      have e : regValue src base*2^32=4294967296*H := by dsimp only [H]; ring
      simp only [Acc.step,Acc.earlyTerm,if_true]
      rw [e]
      omega
    rw [value] at h
    exact h
  have ad := add_triple acc Z bank cin src hacc hsrc hf6 base hz hb hi
  change Triple (SquareFrame acc base (976*H)) (add acc Z bank cin src)
    (SquareFrame acc base (1040*H)) at ad
  have sub : Triple (SquareFrame acc base (1040*H)) (SourceTailDevelop.tail acc Z bank cin src)
      (SquareFrame acc base (16*H)) := SourceTailDevelop.tail_triple acc Z bank cin src hacc hsrc hf10 base hz hb hi
  have seed := Acc.seed_triple acc Z bank cin 163 (Acc.earlyTerm src false 4) hacc hf4 base hz
    (16*H) 0 (Or.inr (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
  exact ((top.seq ad).seq sub).seq seed


theorem unbuild_eq_old (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz : ∀q∈Z,s.basis q=false) (hb : ∀q∈bank,s.basis q=false)
    (hi : s.basis cin=false) (ha : regValue acc s.basis=4294968272*regValue src s.basis) :
    run (unbuild acc Z bank cin src) m s=run (CodexNarrowTail.unbuild8 acc Z bank cin src) m s := by
  have start : SquareFrame acc s.basis (4294968272*regValue src s.basis) s.basis := ⟨ha,fun _ _=>rfl⟩
  have a:=unbuild_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s m start
  have b:=CodexNarrowTail.unbuild8_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s m start
  apply State.extensionality _ _
  · exact a.1.trans b.1.symm
  funext q
  by_cases hq : q∈acc
  · exact ((regValue_zero _ _).mp a.2.1 q hq).trans ((regValue_zero _ _).mp b.2.1 q hq).symm
  · exact (a.2.2 q hq).trans (b.2.2 q hq).symm
#print axioms unbuild_triple
#print axioms unbuild_eq_old
end ECDSAAdd.Entrant.SourceAddFourDevelop
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SourceAddFourDevelop
open Arithmetic CodexNarrowTail

theorem unbuild_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.FitsLen Z bank 163 f) :
    toffoliCount (unbuild acc Z bank cin src)=233 ∧ measurementCount (unbuild acc Z bank cin src)=388 ∧
    wires (unbuild acc Z bank cin src)⊆wires (CodexNarrowTail.unbuild8 acc Z bank cin src) ∧
    Challenge.gateSlots (unbuild acc Z bank cin src)≤Challenge.gateSlots (CodexNarrowTail.unbuild8 acc Z bank cin src) := by
  have a:=add_resources acc Z bank cin src hacc hsrc (hf _ (terms_mem src).2.2.1)
  have old:=SourceTailDevelop.unbuild_resources acc Z bank cin src hacc hsrc hf
  have dt : toffoliCount (unbuild acc Z bank cin src)+4=toffoliCount (SourceTailDevelop.unbuild acc Z bank cin src) := by
    simp only [unbuild,SourceTailDevelop.unbuild,toffoliCount_append]
    omega
  have dm : measurementCount (unbuild acc Z bank cin src)=measurementCount (SourceTailDevelop.unbuild acc Z bank cin src) := by
    simp only [unbuild,SourceTailDevelop.unbuild,measurementCount_append]
    omega
  refine ⟨by omega,by omega,?_,?_⟩
  · apply Finset.Subset.trans _ old.2.2.1
    simp only [unbuild,SourceTailDevelop.unbuild,wires_append]
    exact Finset.union_subset_union
      (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) a.2.2.1)
        (Finset.Subset.refl _)) (Finset.Subset.refl _)
  · have h : Challenge.gateSlots (unbuild acc Z bank cin src)≤Challenge.gateSlots (SourceTailDevelop.unbuild acc Z bank cin src) := by
      simp only [unbuild,SourceTailDevelop.unbuild,Challenge.gateSlots_append]
      omega
    exact h.trans old.2.2.2

theorem unbuild_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f) :
    GatePhysical (unbuild acc Z bank cin src) := by
  have old:=SourceTailDevelop.unbuild_physical acc Z bank cin src hacc hsrc hf
  have a:=add_physical acc Z bank cin src hacc hsrc (hf _ (terms_mem src).2.2.1)
  simp only [unbuild,SourceTailDevelop.unbuild,gatePhysical_append] at old ⊢
  exact ⟨⟨⟨old.1.1.1,a⟩,old.1.2⟩,old.2⟩
#print axioms unbuild_resources
#print axioms unbuild_physical
end ECDSAAdd.Entrant.SourceAddFourDevelop
end
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def wUnbuildKnown (L : CuccaroStreamedSquareWideLayout) : Program :=
  SourceAddFourDevelop.unbuild (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)

theorem wUnbuildKnown_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (wUnbuildKnown L)=233 ∧ measurementCount (wUnbuildKnown L)=388 ∧
    wires (wUnbuildKnown L)⊆wires (wUnbuild L) ∧
    Challenge.gateSlots (wUnbuildKnown L)≤Challenge.gateSlots (wUnbuild L) :=
  SourceAddFourDevelop.unbuild_resources (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (hiReg_length L hw) (wTerms_okLen L hw)

theorem wUnbuildKnown_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (wUnbuildKnown L)=233 ∧ measurementCount (wUnbuildKnown L)=388 :=
  ⟨(wUnbuildKnown_resources L hw).1,(wUnbuildKnown_resources L hw).2.1⟩

theorem wUnbuildKnown_wires (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    wires (wUnbuildKnown L)⊆wires (wUnbuild L) := (wUnbuildKnown_resources L hw).2.2.1

theorem wUnbuildKnown_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (wUnbuildKnown L)≤Challenge.gateSlots (wUnbuild L) :=
  (wUnbuildKnown_resources L hw).2.2.2

theorem wUnbuildKnown_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (wUnbuildKnown L) :=
  SourceAddFourDevelop.unbuild_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (hiReg_length L hw) (wTerms_fits L hw hn)

theorem wUnbuildKnown_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) :
    Triple (BState L base O E (4294968272*regValue (hiReg L) base)) (wUnbuildKnown L) (BState L base O E 0) := by
  apply lift_acc L hn base O E _ 0 (wUnbuildKnown L)
  intro s m h
  obtain ⟨hz,hb,hi,_,_⟩ := zero_regs L hn base hc O E _ s.basis h
  have hh : regValue (hiReg L) s.basis=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E _ s.basis h q (Or.inl hq))
  have tr := SourceAddFourDevelop.unbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) s.basis hz hb hi
    s m ⟨by rw [hh]; exact h.2.2.1,fun _ _ => rfl⟩
  exact ⟨tr.1,tr.2.1,tr.2.2⟩


#print axioms wUnbuildKnown_resources
#print axioms wUnbuildKnown_physical
#print axioms wUnbuildKnown_step
end ECDSAAdd.Entrant.ControlLoan1589BFFold

namespace ECDSAAdd.Entrant.Aux3Develop
open Arithmetic Arithmetic.KnownOutputAdder Arithmetic.CuccaroStreamedSquareWideLayout

abbrev zero : MappedBit := ⟨none,false⟩
def source (S : List Wire) : List MappedBit := mappedRead S false++[zero]
def copyLow (T S : List Wire) : Program := copyRegister none S (T.take 10)
def load (T S cs : List Wire) (cin : Wire) : Program :=
  copyLow T S++mappedAdd (source S) (T.drop 1) (cs.take 10) cin

theorem load_arith (d : Nat) (hd : d<2^10) :
    d%2+2*((d/2+d)%2^11)=3*d := by omega

theorem subtract_arith (d : Nat) (hd : d<2^10) :
    (1025*d)%2^4+2^4*(((1025*d)/2^4+2^16-3*d)%2^16)=977*d := by omega

theorem inverse_known_value (d : Nat) (hd : d<2^10) :
    (3*d+(977*d)/2^4)%2^16=d/2^4+2^6*d := by
  change (3*d+(977*d)/16)%65536=d/16+64*d
  have eq : 3*d+(977*d)/16=d/16+64*d := by
    rw [show 977*d=d+16*(61*d) by omega,Nat.add_mul_div_left _ _ (by decide : 0<16)]
    omega
  rw [eq,Nat.mod_eq_of_lt (by omega)]

theorem source_value (S : List Wire) (s : BasisState) : mappedValue (source S) s=regValue S s := by
  simp [source,mappedValue_append,mappedRead_value,mappedValue,zero,MappedBit.value]

theorem source_wires (S : List Wire) : mappedWires (source S)=S := by
  simp [source,mappedWires,mappedRead,List.flatMap_append,List.flatMap_map,zero]

theorem copy_run (T S : List Wire) (ht : T.length=12) (hs : S.length=10)
    (hn : (T++S).Nodup) (s : State) (m : List Bool) :
    (run (copyLow T S) m s).phase=s.phase ∧
    regValue T (run (copyLow T S) m s).basis=
      (regValue T s.basis%2^10 ^^^ regValue S s.basis)+2^10*(regValue T s.basis/2^10) ∧
    (∀q,q∉T → (run (copyLow T S) m s).basis q=s.basis q) := by
  have nd : (S++T.take 10).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp hn q
    have t:=(List.take_sublist 10 T).count_le q
    simp only [List.count_append] at h ⊢
    omega
  have a:=copyRegister_correct none S (T.take 10) (by simp [ht,hs]) nd (by simp) s m
  have low := Arithmetic.CuccaroStreamedSquareWideLayout.regValue_take_mod T 10 (by omega) s.basis
  have tn := (List.nodup_append.mp hn).1
  have recombine := WinArith.win_recombine T tn 0 10 (by omega) s.basis
    (run (copyLow T S) m s).basis
    (by simpa only [List.drop_zero] using a.2.1)
    (regValue (T.take 10) s.basis ^^^ regValue S s.basis)
    (by simpa only [List.drop_zero,copyValue] using a.2.2)
  refine ⟨a.1,?_,?_⟩
  · rw [recombine,low]
    rw [regValue_drop_div T (0+10) (by omega)]
    simp [regValue]
  · intro q hq
    exact a.2.1 q (fun h=>hq (List.mem_of_mem_take h))
#print axioms load_arith
#print axioms inverse_known_value
#print axioms source_wires
#print axioms copy_run
end ECDSAAdd.Entrant.Aux3Develop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Aux3Develop
open Arithmetic Arithmetic.KnownOutputAdder Arithmetic.CuccaroStreamedSquareWideLayout

theorem load_geometry (T S cs : List Wire) (cin : Wire)
    (hn : (cin::(T++S++cs)).Nodup) :
    (cin::(T.drop 1++cs.take 10)).Nodup ∧
    (∀q∈S,q∉cin::(T.drop 1++cs.take 10)) := by
  have bank (q : Wire) :
      (cin::(T.drop 1++cs.take 10)).count q+S.count q≤
        (cin::(T++S++cs)).count q := by
    have td := (List.drop_sublist 1 T).count_le q
    have ct := (List.take_sublist 10 cs).count_le q
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

theorem load_run (T S cs : List Wire) (cin : Wire)
    (ht : T.length=12) (hs : S.length=10) (hc : 10≤cs.length)
    (hn : (cin::(T++S++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hcin : s.basis cin=false)
    (d : Nat) (hd : d<2^10) (hT : regValue T s.basis=0) (hS : regValue S s.basis=d) :
    (run (load T S cs cin) m s).phase=s.phase ∧
    regValue T (run (load T S cs cin) m s).basis=3*d ∧
    (∀q,q∉T → (run (load T S cs cin) m s).basis q=s.basis q) := by
  have ts : (T++S).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  let u:=run (copyLow T S) m s
  let m1:=m.drop (measurementCount (copyLow T S))
  have a:=copy_run T S ht hs ts s m
  change u.phase=s.phase ∧ regValue T u.basis=_ ∧ (∀q,q∉T → u.basis q=s.basis q) at a
  have uT : regValue T u.basis=d := by rw [a.2.1,hT,hS];simp
  have us:=Win977Develop.source_frame T S cs cin hn s u a.2.2
  have geo:=load_geometry T S cs cin hn
  have b:=mappedAdd_correct (source S) (T.drop 1) (cs.take 10) cin geo.1
    (by rw [source_wires];exact geo.2)
    (by simp [source,mappedRead,hs,ht]) (by simp [ht];omega) u m1
    (fun q hq=>(us.2.1 q (List.mem_of_mem_take hq)).trans (hclean q (List.mem_of_mem_take hq)))
  let v:=run (mappedAdd (source S) (T.drop 1) (cs.take 10) cin) m1 u
  change v.phase=u.phase ∧ (∀q,q∉T.drop 1 → v.basis q=u.basis q) ∧
    regValue (T.drop 1) v.basis=_ at b
  have high : regValue (T.drop 1) v.basis=(d+d/2)%2^11 := by
    rw [b.2.2,source_value,us.1,hS,regValue_drop_div T 1 (by omega),uT,
      us.2.2,hcin,Bool.toNat_false,Nat.add_zero,List.length_drop,ht]
    rfl
  have tn : T.Nodup := (List.nodup_append.mp ts).1
  have split : (T.take 1++T.drop 1).Nodup := by rw [List.take_append_drop];exact tn
  have dis : List.Disjoint (T.take 1) (T.drop 1) := by
    intro q hq bad
    exact (List.nodup_append.mp split).2.2 q hq q bad rfl
  have low : regValue (T.take 1) v.basis=d%2 := by
    rw [regValue_congr (T.take 1) _ u.basis
      (fun q hq=>b.2.1 q (fun bad=>dis hq bad)),regValue_take_mod T 1 (by omega),uT]
    rfl
  have out:=regValue_append (T.take 1) (T.drop 1) v.basis
  rw [List.take_append_drop,List.length_take,ht,Nat.min_eq_left (by decide : 1≤12),low,high] at out
  have value : regValue T v.basis=3*d := by
    rw [out,Nat.add_comm d (d/2)]
    exact load_arith d hd
  have eq : run (load T S cs cin) m s=v := by
    simp only [load,run_append,run_take]
    rfl
  rw [eq]
  exact ⟨b.1.trans a.1,value,fun q hq=>(b.2.1 q (fun bad=>hq (List.mem_of_mem_drop bad))).trans (a.2.2 q hq)⟩
#print axioms load_run
end ECDSAAdd.Entrant.Aux3Develop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Aux3Develop
open Arithmetic Arithmetic.KnownOutputAdder Arithmetic.CuccaroStreamedSquareWideLayout MixedLiteralAdderDevelop

abbrev one : MappedBit := ⟨none,true⟩
def negDesired (S : List Wire) : List MappedBit := mappedRead (S.drop 1) true++[one,one]
def unadd (T S cs : List Wire) (cin : Wire) : Program :=
  KnownSubDevelop.knownSub (source S) (negDesired S) (T.drop 1) (cs.take 10) cin
def clear (T S cs : List Wire) (cin : Wire) : Program := unadd T S cs cin++copyLow T S

theorem negDesired_value (S : List Wire) (s : BasisState) (hs : S.length=10) :
    mappedValue (negDesired S) s=2047-regValue S s/2 := by
  rw [negDesired,mappedValue_append,mappedRead_complement,
    regValue_drop_div S 1 (by omega)]
  simp only [mappedRead,List.length_map,List.length_drop,hs]
  norm_num [one,MappedBit.value,mappedValue]
  have h:=regValue_lt S s
  rw [hs] at h
  omega

theorem negDesired_wires (S : List Wire) : mappedWires (negDesired S)=S.drop 1 := by
  have app (a b : List MappedBit) : mappedWires (a++b)=mappedWires a++mappedWires b := by
    simp [mappedWires,List.flatMap_append]
  rw [negDesired,app,mappedRead_wires]
  simp [mappedWires,one]

theorem clear_known_value (d : Nat) (hd : d<2^10) :
    (d+(2^11-1-(3*d)/2))%2^11=2^11-1-d/2 := by
  have eq : (3*d)/2=d/2+d := by
    rw [show 3*d=d+2*d by omega,Nat.add_mul_div_left _ _ (by decide : 0<2)]
  rw [eq]
  omega

theorem unadd_eq (T S cs : List Wire) (cin : Wire)
    (ht : T.length=12) (hs : S.length=10) (hc : 10≤cs.length)
    (hn : (cin::(T++S++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hcin : s.basis cin=false)
    (d : Nat) (hd : d<2^10) (hT : regValue T s.basis=3*d) (hS : regValue S s.basis=d) :
    run (unadd T S cs cin) m s=run (mappedSub (source S) (T.drop 1) (cs.take 10) cin) m s := by
  have geo:=load_geometry T S cs cin hn
  have away (q : Wire) (hq : q∈S) : q∉T.drop 1 := by
    intro bad;exact geo.2 q hq (List.mem_cons_of_mem _ (List.mem_append_left _ bad))
  have caway : cin∉T.drop 1 := by
    intro bad;exact (List.nodup_cons.mp geo.1).1 (List.mem_append_left _ bad)
  have src : mappedValue (source S) (flipped (T.drop 1) s).basis=d := by
    rw [source_value]
    rw [regValue_congr S _ s.basis (by intro q hq;simp only [flipped,if_neg (away q hq)]),hS]
  have des : mappedValue (negDesired S) (flipped (T.drop 1) s).basis=2047-d/2 := by
    rw [negDesired_value S _ hs]
    rw [regValue_congr S _ s.basis (by intro q hq;simp only [flipped,if_neg (away q hq)]),hS]
  have tar : regValue (T.drop 1) (flipped (T.drop 1) s).basis=2^11-1-(3*d)/2 := by
    rw [regValue_congr (T.drop 1) _ (fun q=>!s.basis q) (by intro q hq;simp only [flipped,if_pos hq]),
      regValue_complement,List.length_drop,ht,regValue_drop_div T 1 (by omega),hT]
    rfl
  have ready : Arithmetic.KnownOutputAdder.Ready (source S) (negDesired S) (T.drop 1)
      ((flipped (T.drop 1) s).basis cin) (flipped (T.drop 1) s).basis := by
    apply Arithmetic.KnownOutputAdder.ready_of_value _ _ _ _ _
      (by simp [source,mappedRead,ht,hs]) (by simp [negDesired,mappedRead,ht,hs])
    rw [src,des,tar,show (flipped (T.drop 1) s).basis cin=false by simp only [flipped,if_neg caway,hcin],
      Bool.toNat_false,Nat.add_zero,List.length_drop,ht]
    exact (clear_known_value d hd).symm
  exact KnownSubDevelop.sub_eq (source S) (negDesired S) (T.drop 1) (cs.take 10) cin geo.1
    (by rw [source_wires];exact geo.2)
    (by rw [negDesired_wires];intro q hq;exact geo.2 q (List.mem_of_mem_drop hq))
    (by simp [source,mappedRead,ht,hs]) (by simp [negDesired,mappedRead,ht,hs])
    (by simp [ht];omega) s m (fun q hq=>hclean q (List.mem_of_mem_take hq)) ready
theorem unadd_run (T S cs : List Wire) (cin : Wire)
    (ht : T.length=12) (hs : S.length=10) (hc : 10≤cs.length)
    (hn : (cin::(T++S++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hcin : s.basis cin=false)
    (d : Nat) (hd : d<2^10) (hT : regValue T s.basis=3*d) (hS : regValue S s.basis=d) :
    (run (unadd T S cs cin) m s).phase=s.phase ∧
    regValue T (run (unadd T S cs cin) m s).basis=d ∧
    (∀q,q∉T → (run (unadd T S cs cin) m s).basis q=s.basis q) := by
  rw [unadd_eq T S cs cin ht hs hc hn s m hclean hcin d hd hT hS]
  have geo:=load_geometry T S cs cin hn
  have a:=mappedSub_correct (source S) (T.drop 1) (cs.take 10) cin geo.1
    (by rw [source_wires];exact geo.2) (by simp [source,mappedRead,ht,hs])
    (by simp [ht];omega) s m (fun q hq=>hclean q (List.mem_of_mem_take hq)) hcin
  let v:=run (mappedSub (source S) (T.drop 1) (cs.take 10) cin) m s
  change v.phase=s.phase ∧ (∀q,q∉T.drop 1 → v.basis q=s.basis q) ∧
    regValue (T.drop 1) v.basis=_ at a
  have high : regValue (T.drop 1) v.basis=d/2 := by
    rw [a.2.2,source_value,hS,regValue_drop_div T 1 (by omega),hT,List.length_drop,ht]
    have qeq : (3*d)/2=d/2+d := by
      rw [show 3*d=d+2*d by omega,Nat.add_mul_div_left _ _ (by decide : 0<2)]
    change ((3*d)/2+2048-d)%2048=d/2
    rw [qeq]
    omega
  have tn : T.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have old:=List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at old
    omega
  have split : (T.take 1++T.drop 1).Nodup := by rw [List.take_append_drop];exact tn
  have dis : List.Disjoint (T.take 1) (T.drop 1) := by
    intro q hq bad
    exact (List.nodup_append.mp split).2.2 q hq q bad rfl
  have low : regValue (T.take 1) v.basis=(3*d)%2 := by
    rw [regValue_congr (T.take 1) _ s.basis
      (fun q hq=>a.2.1 q (fun bad=>dis hq bad)),regValue_take_mod T 1 (by omega),hT]
    rfl
  have out:=regValue_append (T.take 1) (T.drop 1) v.basis
  rw [List.take_append_drop,List.length_take,ht,Nat.min_eq_left (by decide : 1≤12),low,high] at out
  have value : regValue T v.basis=d := by rw [out];omega
  exact ⟨a.1,value,fun q hq=>a.2.1 q (fun bad=>hq (List.mem_of_mem_drop bad))⟩

theorem clear_run (T S cs : List Wire) (cin : Wire)
    (ht : T.length=12) (hs : S.length=10) (hc : 10≤cs.length)
    (hn : (cin::(T++S++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hcin : s.basis cin=false)
    (d : Nat) (hd : d<2^10) (hT : regValue T s.basis=3*d) (hS : regValue S s.basis=d) :
    (run (clear T S cs cin) m s).phase=s.phase ∧
    regValue T (run (clear T S cs cin) m s).basis=0 ∧
    (∀q,q∉T → (run (clear T S cs cin) m s).basis q=s.basis q) := by
  let u:=run (unadd T S cs cin) m s
  let m1:=m.drop (measurementCount (unadd T S cs cin))
  have a:=unadd_run T S cs cin ht hs hc hn s m hclean hcin d hd hT hS
  change u.phase=s.phase ∧ regValue T u.basis=d ∧ (∀q,q∉T → u.basis q=s.basis q) at a
  have ts : (T++S).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have us:=Win977Develop.source_frame T S cs cin hn s u a.2.2
  have b:=copy_run T S ht hs ts u m1
  have value : regValue T (run (copyLow T S) m1 u).basis=0 := by
    rw [b.2.1,a.2.1,us.1,hS,Nat.mod_eq_of_lt hd,Nat.div_eq_of_lt hd,Nat.xor_self]
    rfl
  have eq : run (clear T S cs cin) m s=run (copyLow T S) m1 u := by
    simp only [clear,run_append,run_take]
    rfl
  rw [eq]
  exact ⟨b.1.trans a.1,value,fun q hq=>(b.2.2 q hq).trans (a.2.2 q hq)⟩
#print axioms unadd_run
#print axioms clear_run

#print axioms negDesired_value
#print axioms clear_known_value
#print axioms unadd_eq
end ECDSAAdd.Entrant.Aux3Develop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace ECDSAAdd.Entrant.Aux3Develop
open Arithmetic

def T (cs : List Wire) : List Wire := (cs.drop 15).take 12
def C (cs : List Wire) : List Wire := cs.take 15
def X (Z cs : List Wire) : List Wire := T cs++Z.take 4

structure Geo (R S Z cs : List Wire) (cin : Wire) : Prop where
  r : R.length=20
  s : S.length=10
  z : Z.length=11
  c : cs.length=42
  nd : (cin::(R++S++Z++cs)).Nodup

namespace Geo
variable {R S Z cs : List Wire} {cin : Wire} (g : Geo R S Z cs cin)
include g

theorem tlen : (T cs).length=12 := by simp [T,g.c]
theorem clen : (C cs).length=15 := by simp [C,g.c]
theorem xlen : (X Z cs).length=16 := by simp [X,g.tlen,g.z]

theorem tmem {q : Wire} (h : q∈T cs) : q∈cs := List.mem_of_mem_drop (List.mem_of_mem_take h)
theorem cmem {q : Wire} (h : q∈C cs) : q∈cs := List.mem_of_mem_take h

theorem tc_count (q : Wire) : (T cs).count q+(C cs).count q≤cs.count q := by
  have h:=(List.take_sublist 27 cs).count_le q
  have e : cs.take 27=cs.take 15++(cs.drop 15).take 12 := List.take_add (i:=15) (j:=12) (l:=cs)
  rw [e,List.count_append] at h
  simpa only [T,C,Nat.add_comm] using h

theorem aux_nd : (cin::(T cs++S++C cs)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have old:=List.nodup_iff_count.mp g.nd q
  have tc:=g.tc_count q
  simp only [List.count_cons,List.count_append] at old ⊢
  omega

theorem main_nd : (cin::(X Z cs++(R.drop 4).take 16++C cs)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have old:=List.nodup_iff_count.mp g.nd q
  have tc:=g.tc_count q
  have zt:=(List.take_sublist 4 Z).count_le q
  have rt:=((List.take_sublist 16 (R.drop 4)).trans (List.drop_sublist 4 R)).count_le q
  simp only [X,List.count_cons,List.count_append] at old ⊢
  omega

theorem rs_nd : (R++S).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have old:=List.nodup_iff_count.mp g.nd q
  simp only [List.count_cons,List.count_append] at old ⊢
  omega

theorem rnd : R.Nodup := (List.nodup_append.mp g.rs_nd).1

theorem cs_R (q : Wire) (hq : q∈cs) : q∉R := by
  intro bad
  have h:=List.nodup_iff_count.mp g.nd q
  have a:=List.count_pos_iff.mpr hq
  have b:=List.count_pos_iff.mpr bad
  simp only [List.count_cons,List.count_append] at h
  omega

theorem T_R (q : Wire) (hq : q∈T cs) : q∉R := g.cs_R q (g.tmem hq)
theorem C_R (q : Wire) (hq : q∈C cs) : q∉R := g.cs_R q (g.cmem hq)

theorem S_R (q : Wire) (hq : q∈S) : q∉R := by
  intro bad
  have h:=List.nodup_iff_count.mp g.nd q
  have a:=List.count_pos_iff.mpr hq
  have b:=List.count_pos_iff.mpr bad
  simp only [List.count_cons,List.count_append] at h
  omega

theorem Z_R (q : Wire) (hq : q∈Z) : q∉R := by
  intro bad
  have h:=List.nodup_iff_count.mp g.nd q
  have a:=List.count_pos_iff.mpr hq
  have b:=List.count_pos_iff.mpr bad
  simp only [List.count_cons,List.count_append] at h
  omega

theorem Z_T (q : Wire) (hq : q∈Z) : q∉T cs := by
  intro bad
  have h:=List.nodup_iff_count.mp g.nd q
  have a:=List.count_pos_iff.mpr hq
  have b:=List.count_pos_iff.mpr (g.tmem bad)
  simp only [List.count_cons,List.count_append] at h
  omega

theorem cin_R : cin∉R := by
  intro bad
  exact (List.nodup_cons.mp g.nd).1 (by simp only [List.mem_append];tauto)

theorem C_T (q : Wire) (hq : q∈C cs) : q∉T cs :=
  Win977Develop.outside_data (T cs) S (C cs) cin g.aux_nd q (by simp [hq])

theorem cin_T : cin∉T cs :=
  Win977Develop.outside_data (T cs) S (C cs) cin g.aux_nd cin (by simp)
end Geo
#print axioms Geo.aux_nd
#print axioms Geo.main_nd
end ECDSAAdd.Entrant.Aux3Develop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Aux3Develop
open Arithmetic Arithmetic.KnownOutputAdder Arithmetic.CuccaroStreamedSquareWideLayout

def knownLift (R S Z cs : List Wire) (cin : Wire) : Program :=
  KnownOutputAdder.program (mappedRead (X Z cs) false) ((R.drop 4).take 16)
    (mappedRead (S.drop 4++S) false) (C cs) cin

theorem Geo.main_S {R S Z cs : List Wire} {cin : Wire} (g : Geo R S Z cs cin)
    (q : Wire) (hq : q∈S) : q∉cin::(X Z cs++(R.drop 4).take 16++C cs) := by
  intro bad
  have old:=List.nodup_iff_count.mp g.nd q
  have tc:=g.tc_count q
  have zt:=(List.take_sublist 4 Z).count_le q
  have rt:=((List.take_sublist 16 (R.drop 4)).trans (List.drop_sublist 4 R)).count_le q
  have a:=List.count_pos_iff.mpr hq
  have b:=List.count_pos_iff.mpr bad
  simp only [X,List.count_cons,List.count_append] at old b
  omega

theorem x_value (Z cs : List Wire) (s : BasisState) (v : Nat)
    (ht : regValue (T cs) s=v) (hz : ∀q∈Z,s q=false) : regValue (X Z cs) s=v := by
  have zero : regValue (Z.take 4) s=0 := (regValue_zero _ _).mpr
    (fun q hq=>hz q (List.mem_of_mem_take hq))
  rw [X,regValue_append,ht,zero,Nat.mul_zero,Nat.add_zero]

theorem knownLift_eq {R S Z cs : List Wire} {cin : Wire} (g : Geo R S Z cs cin)
    (s : State) (m : List Bool) (hclean : ∀q∈C cs,s.basis q=false) (hcin : s.basis cin=false)
    (d : Nat) (hd : d<2^10) (hR : regValue R s.basis=977*d)
    (hS : regValue S s.basis=d) (hT : regValue (T cs) s.basis=3*d)
    (hZ : ∀q∈Z,s.basis q=false) :
    run (knownLift R S Z cs cin) m s=
      run (addInPlace (X Z cs) ((R.drop 4).take 16) (C cs) cin) m s := by
  have bank:=MixedLiteralAdderDevelop.read_geometry (X Z cs) ((R.drop 4).take 16) (C cs) cin g.main_nd
  have yslen : ((R.drop 4).take 16).length=16 := by simp [g.r]
  have sx : regValue (X Z cs) s.basis=3*d := x_value Z cs s.basis _ hT hZ
  have yr := WinArith.win_mid R 4 16 (by rw [g.r]) s.basis
  rw [hR,Nat.mod_eq_of_lt (show (977*d)/2^4<2^16 by omega)] at yr
  have ev : mappedValue (mappedRead (S.drop 4++S) false) s.basis=d/2^4+2^6*d := by
    rw [mappedRead_value,regValue_append,regValue_drop_div S 4 (by rw [g.s];decide),hS]
    simp only [List.length_drop,g.s]
  have ready : KnownOutputAdder.Ready (mappedRead (X Z cs) false)
      (mappedRead (S.drop 4++S) false) ((R.drop 4).take 16) (s.basis cin) s.basis := by
    apply ready_of_value _ _ _ _ _ (by simp [mappedRead,g.xlen,yslen])
      (by simp [mappedRead,g.s,yslen])
    rw [ev,mappedRead_value,sx,yr,hcin,Bool.toNat_false,Nat.add_zero,yslen]
    exact (inverse_known_value d hd).symm
  have sumsAway : ∀q∈mappedWires (mappedRead (S.drop 4++S) false),
      q∉cin::(((R.drop 4).take 16)++C cs) := by
    rw [mappedRead_wires]
    intro q hq bad
    have hqS : q∈S := by
      rcases List.mem_append.mp hq with h|h
      · exact List.mem_of_mem_drop h
      · exact h
    exact g.main_S q hqS (by simp only [List.mem_cons,List.mem_append] at bad ⊢;tauto)
  have eq:=KnownOutputAdder.program_eq_mappedAdd (mappedRead (X Z cs) false)
    (mappedRead (S.drop 4++S) false) ((R.drop 4).take 16) (C cs) cin bank.1
    (by rw [mappedRead_wires];exact bank.2) sumsAway
    (by simp [mappedRead,g.xlen,yslen]) (by simp [mappedRead,g.s,yslen])
    (by rw [g.clen,yslen]) s m hclean ready
  change run (KnownOutputAdder.program _ _ _ _ _) m s=_
  rw [eq,MixedLiteralAdderDevelop.read_add_eq]
#print axioms knownLift_eq
end ECDSAAdd.Entrant.Aux3Develop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Aux3Develop
open Arithmetic

def forward (R S Z cs : List Wire) (cin : Wire) : Program :=
  Win977Develop.copyHigh R S++(load (T cs) S (C cs) cin++
    (subInPlace (X Z cs) ((R.drop 4).take 16) (C cs) cin++clear (T cs) S (C cs) cin))

theorem forward_run {R S Z cs : List Wire} {cin : Wire} (g : Geo R S Z cs cin)
    (s : State) (m : List Bool) (hclean : ∀q∈cs,s.basis q=false)
    (hZ : ∀q∈Z,s.basis q=false) (hcin : s.basis cin=false)
    (d : Nat) (hd : d<2^10) (hR : regValue R s.basis=d) (hS : regValue S s.basis=d) :
    (run (forward R S Z cs cin) m s).phase=s.phase ∧
    regValue R (run (forward R S Z cs cin) m s).basis=977*d ∧
    (∀q,q∉R → (run (forward R S Z cs cin) m s).basis q=s.basis q) := by
  have rT (q : Wire) (hq : q∈R) : q∉T cs := fun bad=>g.T_R q bad hq
  let u:=run (Win977Develop.copyHigh R S) m s
  let m1:=m.drop (measurementCount (Win977Develop.copyHigh R S))
  have a:=Win977Develop.copy_run R S g.r g.s g.rs_nd s m
  change u.phase=s.phase ∧ regValue R u.basis=_ ∧ (∀q,q∉R → u.basis q=s.basis q) at a
  have uR : regValue R u.basis=1025*d := by
    rw [a.2.1,hR,hS]
    exact (WindowBoundsDevelop.copy_arith d hd).1
  have uS : regValue S u.basis=d :=
    (regValue_congr S _ s.basis (fun q hq=>a.2.2 q (g.S_R q hq))).trans hS
  have uT : regValue (T cs) u.basis=0 := (regValue_zero _ _).mpr
    (fun q hq=>(a.2.2 q (g.T_R q hq)).trans (hclean q (g.tmem hq)))
  have uC (q : Wire) (hq : q∈C cs) : u.basis q=false :=
    (a.2.2 q (g.C_R q hq)).trans (hclean q (g.cmem hq))
  have uZ (q : Wire) (hq : q∈Z) : u.basis q=false := (a.2.2 q (g.Z_R q hq)).trans (hZ q hq)
  have ui : u.basis cin=false := (a.2.2 cin g.cin_R).trans hcin
  have b:=load_run (T cs) S (C cs) cin g.tlen g.s (by rw [g.clen];decide) g.aux_nd
    u m1 uC ui d hd uT uS
  let v:=run (load (T cs) S (C cs) cin) m1 u
  let m2:=m1.drop (measurementCount (load (T cs) S (C cs) cin))
  change v.phase=u.phase ∧ regValue (T cs) v.basis=3*d ∧ (∀q,q∉T cs → v.basis q=u.basis q) at b
  have vR : regValue R v.basis=1025*d := (regValue_congr R _ u.basis (fun q hq=>b.2.2 q (rT q hq))).trans uR
  have vs:=Win977Develop.source_frame (T cs) S (C cs) cin g.aux_nd u v b.2.2
  have vS : regValue S v.basis=d := vs.1.trans uS
  have vC (q : Wire) (hq : q∈C cs) : v.basis q=false := (b.2.2 q (g.C_T q hq)).trans (uC q hq)
  have vZ (q : Wire) (hq : q∈Z) : v.basis q=false := (b.2.2 q (g.Z_T q hq)).trans (uZ q hq)
  have vi : v.basis cin=false := (b.2.2 cin g.cin_T).trans ui
  have vX : regValue (X Z cs) v.basis=3*d := x_value Z cs v.basis _ b.2.1 vZ
  have fit : regValue (X Z cs) v.basis≤(regValue R v.basis/2^4)%2^16 := by
    rw [vX,vR,Nat.mod_eq_of_lt (show (1025*d)/2^4<2^16 by omega)]
    omega
  have c:=WinArith.win_sub R (X Z cs) (C cs) cin 4 16 g.rnd (by rw [g.r]) g.main_nd
    g.xlen (by rw [g.clen]) v m2 vi vC fit
  let w:=run (subInPlace (X Z cs) ((R.drop 4).take 16) (C cs) cin) m2 v
  let m3:=m2.drop (measurementCount (subInPlace (X Z cs) ((R.drop 4).take 16) (C cs) cin))
  change w.phase=v.phase ∧ (∀q,q∉(R.drop 4).take 16 → w.basis q=v.basis q) ∧
    regValue R w.basis+2^4*regValue (X Z cs) v.basis=regValue R v.basis at c
  have wR : regValue R w.basis=977*d := by have eq:=c.2.2;rw [vX,vR] at eq;omega
  have wframe (q : Wire) (hq : q∉R) : w.basis q=v.basis q := c.2.1 q (fun h=>hq (WinArith.mem_win h))
  have wT : regValue (T cs) w.basis=3*d :=
    (regValue_congr (T cs) _ v.basis (fun q hq=>wframe q (g.T_R q hq))).trans b.2.1
  have wS : regValue S w.basis=d := (regValue_congr S _ v.basis (fun q hq=>wframe q (g.S_R q hq))).trans vS
  have wC (q : Wire) (hq : q∈C cs) : w.basis q=false := (wframe q (g.C_R q hq)).trans (vC q hq)
  have wi : w.basis cin=false := (wframe cin g.cin_R).trans vi
  have e:=clear_run (T cs) S (C cs) cin g.tlen g.s (by rw [g.clen];decide) g.aux_nd
    w m3 wC wi d hd wT wS
  let z:=run (clear (T cs) S (C cs) cin) m3 w
  change z.phase=w.phase ∧ regValue (T cs) z.basis=0 ∧ (∀q,q∉T cs → z.basis q=w.basis q) at e
  have zR : regValue R z.basis=977*d := (regValue_congr R _ w.basis (fun q hq=>e.2.2 q (rT q hq))).trans wR
  have eq : run (forward R S Z cs cin) m s=z := by
    unfold forward
    rw [run_append,run_take]
    change run (load (T cs) S (C cs) cin++(subInPlace (X Z cs) ((R.drop 4).take 16) (C cs) cin++clear (T cs) S (C cs) cin)) m1 u=z
    rw [run_append,run_take]
    change run (subInPlace (X Z cs) ((R.drop 4).take 16) (C cs) cin++clear (T cs) S (C cs) cin) m2 v=z
    rw [run_append,run_take]
  rw [eq]
  refine ⟨e.1.trans (c.1.trans (b.1.trans a.1)),zR,?_⟩
  intro q hq
  by_cases qt : q∈T cs
  · have out : z.basis q=false := (regValue_zero _ _).mp e.2.1 q qt
    exact out.trans (hclean q (g.tmem qt)).symm
  · exact (e.2.2 q qt).trans ((wframe q hq).trans ((b.2.2 q qt).trans (a.2.2 q hq)))
#print axioms forward_run
end ECDSAAdd.Entrant.Aux3Develop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Aux3Develop
open Arithmetic

def inverse (R S Z cs : List Wire) (cin : Wire) : Program :=
  load (T cs) S (C cs) cin++(knownLift R S Z cs cin++
    (clear (T cs) S (C cs) cin++Win977Develop.copyHigh R S))

theorem inverse_run {R S Z cs : List Wire} {cin : Wire} (g : Geo R S Z cs cin)
    (s : State) (m : List Bool) (hclean : ∀q∈cs,s.basis q=false)
    (hZ : ∀q∈Z,s.basis q=false) (hcin : s.basis cin=false)
    (d : Nat) (hd : d<2^10) (hR : regValue R s.basis=977*d) (hS : regValue S s.basis=d) :
    (run (inverse R S Z cs cin) m s).phase=s.phase ∧
    regValue R (run (inverse R S Z cs cin) m s).basis=d ∧
    (∀q,q∉R → (run (inverse R S Z cs cin) m s).basis q=s.basis q) := by
  have rT (q : Wire) (hq : q∈R) : q∉T cs := fun bad=>g.T_R q bad hq
  have cleanT : regValue (T cs) s.basis=0 := (regValue_zero _ _).mpr (fun q hq=>hclean q (g.tmem hq))
  have cleanC (q : Wire) (hq : q∈C cs) : s.basis q=false := hclean q (g.cmem hq)
  have a:=load_run (T cs) S (C cs) cin g.tlen g.s (by rw [g.clen];decide) g.aux_nd
    s m cleanC hcin d hd cleanT hS
  let u:=run (load (T cs) S (C cs) cin) m s
  let m1:=m.drop (measurementCount (load (T cs) S (C cs) cin))
  change u.phase=s.phase ∧ regValue (T cs) u.basis=3*d ∧ (∀q,q∉T cs → u.basis q=s.basis q) at a
  have uR : regValue R u.basis=977*d := (regValue_congr R _ s.basis (fun q hq=>a.2.2 q (rT q hq))).trans hR
  have us:=Win977Develop.source_frame (T cs) S (C cs) cin g.aux_nd s u a.2.2
  have uS : regValue S u.basis=d := us.1.trans hS
  have uC (q : Wire) (hq : q∈C cs) : u.basis q=false := (a.2.2 q (g.C_T q hq)).trans (cleanC q hq)
  have uZ (q : Wire) (hq : q∈Z) : u.basis q=false := (a.2.2 q (g.Z_T q hq)).trans (hZ q hq)
  have ui : u.basis cin=false := (a.2.2 cin g.cin_T).trans hcin
  have uX : regValue (X Z cs) u.basis=3*d := x_value Z cs u.basis _ a.2.1 uZ
  have fit : (regValue R u.basis/2^4)%2^16+regValue (X Z cs) u.basis<2^16 := by
    rw [uX,uR,Nat.mod_eq_of_lt (show (977*d)/2^4<2^16 by omega)]
    omega
  have ke:=knownLift_eq g u m1 uC ui d hd uR uS a.2.1 uZ
  have b:=WinArith.win_add R (X Z cs) (C cs) cin 4 16 g.rnd (by rw [g.r]) g.main_nd
    g.xlen (by rw [g.clen]) u m1 ui uC fit
  rw [←ke] at b
  let v:=run (knownLift R S Z cs cin) m1 u
  let m2:=m1.drop (measurementCount (knownLift R S Z cs cin))
  change v.phase=u.phase ∧ (∀q,q∉(R.drop 4).take 16 → v.basis q=u.basis q) ∧
    regValue R v.basis=regValue R u.basis+2^4*regValue (X Z cs) u.basis at b
  have vR : regValue R v.basis=1025*d := by rw [b.2.2,uR,uX];omega
  have vframe (q : Wire) (hq : q∉R) : v.basis q=u.basis q := b.2.1 q (fun h=>hq (WinArith.mem_win h))
  have vT : regValue (T cs) v.basis=3*d :=
    (regValue_congr (T cs) _ u.basis (fun q hq=>vframe q (g.T_R q hq))).trans a.2.1
  have vS : regValue S v.basis=d := (regValue_congr S _ u.basis (fun q hq=>vframe q (g.S_R q hq))).trans uS
  have vC (q : Wire) (hq : q∈C cs) : v.basis q=false := (vframe q (g.C_R q hq)).trans (uC q hq)
  have vi : v.basis cin=false := (vframe cin g.cin_R).trans ui
  have c:=clear_run (T cs) S (C cs) cin g.tlen g.s (by rw [g.clen];decide) g.aux_nd
    v m2 vC vi d hd vT vS
  let w:=run (clear (T cs) S (C cs) cin) m2 v
  let m3:=m2.drop (measurementCount (clear (T cs) S (C cs) cin))
  change w.phase=v.phase ∧ regValue (T cs) w.basis=0 ∧ (∀q,q∉T cs → w.basis q=v.basis q) at c
  have wR : regValue R w.basis=1025*d := (regValue_congr R _ v.basis (fun q hq=>c.2.2 q (rT q hq))).trans vR
  have ws:=Win977Develop.source_frame (T cs) S (C cs) cin g.aux_nd v w c.2.2
  have wS : regValue S w.basis=d := ws.1.trans vS
  have e:=Win977Develop.copy_run R S g.r g.s g.rs_nd w m3
  let z:=run (Win977Develop.copyHigh R S) m3 w
  change z.phase=w.phase ∧ regValue R z.basis=_ ∧ (∀q,q∉R → z.basis q=w.basis q) at e
  have zR : regValue R z.basis=d := by
    rw [e.2.1,wR,wS]
    exact (WindowBoundsDevelop.copy_arith d hd).2
  have eq : run (inverse R S Z cs cin) m s=z := by
    unfold inverse
    rw [run_append,run_take]
    change run (knownLift R S Z cs cin++(clear (T cs) S (C cs) cin++Win977Develop.copyHigh R S)) m1 u=z
    rw [run_append,run_take]
    change run (clear (T cs) S (C cs) cin++Win977Develop.copyHigh R S) m2 v=z
    rw [run_append,run_take]
  rw [eq]
  refine ⟨e.1.trans (c.1.trans (b.1.trans a.1)),zR,?_⟩
  intro q hq
  by_cases qt : q∈T cs
  · have out : w.basis q=false := (regValue_zero _ _).mp c.2.1 q qt
    exact (e.2.2 q hq).trans (out.trans (hclean q (g.tmem qt)).symm)
  · exact (e.2.2 q hq).trans ((c.2.2 q qt).trans ((vframe q hq).trans (a.2.2 q qt)))
#print axioms inverse_run
end ECDSAAdd.Entrant.Aux3Develop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.Aux3Develop
open Arithmetic Arithmetic.KnownOutputAdder

theorem copy_counts (T S : List Wire) (ht : T.length=12) (hs : S.length=10) :
    toffoliCount (copyLow T S)=0 ∧ measurementCount (copyLow T S)=0 := by
  exact copyRegister_counts none S (T.take 10) (by simp [ht,hs])

theorem load_counts (T S cs : List Wire) (cin : Wire)
    (ht : T.length=12) (hs : S.length=10) (hc : 10≤cs.length) :
    toffoliCount (load T S cs cin)=10 ∧ measurementCount (load T S cs cin)=10 := by
  have a:=copy_counts T S ht hs
  have b:=mappedAdd_counts (source S) (T.drop 1) (cs.take 10) cin
    (by simp [source,mappedRead,ht,hs]) (by simp [ht];omega)
  simp only [load,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,
    List.length_drop,ht,Nat.zero_add] <;> norm_num

theorem unadd_counts (T S cs : List Wire) (cin : Wire)
    (ht : T.length=12) (hs : S.length=10) (hc : 10≤cs.length) :
    toffoliCount (unadd T S cs cin)=0 ∧ measurementCount (unadd T S cs cin)=10 := by
  have a:=KnownSubDevelop.sub_counts (source S) (negDesired S) (T.drop 1) (cs.take 10) cin
    (by simp [source,mappedRead,ht,hs]) (by simp [negDesired,mappedRead,ht,hs])
    (by simp [ht];omega)
  simpa [unadd,ht] using a

theorem clear_counts (T S cs : List Wire) (cin : Wire)
    (ht : T.length=12) (hs : S.length=10) (hc : 10≤cs.length) :
    toffoliCount (clear T S cs cin)=0 ∧ measurementCount (clear T S cs cin)=10 := by
  have a:=unadd_counts T S cs cin ht hs hc
  have b:=copy_counts T S ht hs
  simp [clear,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]

theorem copy_slots (T S : List Wire) (hs : S.length=10) : Challenge.gateSlots (copyLow T S)≤10 := by
  simp [copyLow,hs]

theorem load_slots (T S cs : List Wire) (cin : Wire) (hs : S.length=10) :
    Challenge.gateSlots (load T S cs cin)≤197 := by
  have a:=copy_slots T S hs
  have b:=Baselines.mappedAdd_gateSlots_le (source S) (T.drop 1) (cs.take 10) cin
  have len : (source S).length=11 := by simp [source,mappedRead,hs]
  rw [len] at b
  simp only [load,Challenge.gateSlots_append]
  omega

theorem unadd_slots (T S cs : List Wire) (cin : Wire) (ht : T.length=12) (hs : S.length=10) :
    Challenge.gateSlots (unadd T S cs cin)≤176 := by
  have a:=KnownSubDevelop.sub_slots (source S) (negDesired S) (T.drop 1) (cs.take 10) cin
    (by simp [source,mappedRead,ht,hs])
  simpa [unadd,source,mappedRead,hs] using a

theorem clear_slots (T S cs : List Wire) (cin : Wire) (ht : T.length=12) (hs : S.length=10) :
    Challenge.gateSlots (clear T S cs cin)≤186 := by
  have a:=unadd_slots T S cs cin ht hs
  have b:=copy_slots T S hs
  simp only [clear,Challenge.gateSlots_append]
  omega
#print axioms load_counts
#print axioms clear_counts
#print axioms load_slots
#print axioms clear_slots
end ECDSAAdd.Entrant.Aux3Develop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Aux3Develop
open Arithmetic Arithmetic.KnownOutputAdder

theorem knownLift_counts (R S Z cs : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hz : Z.length=11) (hc : cs.length=42) :
    toffoliCount (knownLift R S Z cs cin)=0 ∧ measurementCount (knownLift R S Z cs cin)=15 := by
  have a:=KnownOutputAdder.program_counts (mappedRead (X Z cs) false)
    (mappedRead (S.drop 4++S) false) ((R.drop 4).take 16) (C cs) cin
    (by simp [mappedRead,X,T,hr,hz,hc]) (by simp [mappedRead,hs,hr]) (by simp [C,hc,hr])
  simpa [knownLift,hr] using a

theorem forward_counts (R S Z cs : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hz : Z.length=11) (hc : cs.length=42) :
    toffoliCount (forward R S Z cs cin)=25 ∧ measurementCount (forward R S Z cs cin)=35 := by
  have tl : (T cs).length=12 := by simp [T,hc]
  have cl : (C cs).length=15 := by simp [C,hc]
  have xl : (X Z cs).length=16 := by simp [X,tl,hz]
  have yl : ((R.drop 4).take 16).length=16 := by simp [hr]
  have a:=Win977Develop.copyHigh_counts R S hr hs
  have b:=load_counts (T cs) S (C cs) cin tl hs (by rw [cl];decide)
  have c:=subInPlace_counts (X Z cs) ((R.drop 4).take 16) (C cs) cin (by rw [xl,yl]) (by rw [cl,yl])
  have e:=clear_counts (T cs) S (C cs) cin tl hs (by rw [cl];decide)
  simp only [forward,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,e.1,e.2,yl]
  norm_num

theorem inverse_counts (R S Z cs : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hz : Z.length=11) (hc : cs.length=42) :
    toffoliCount (inverse R S Z cs cin)=10 ∧ measurementCount (inverse R S Z cs cin)=35 := by
  have tl : (T cs).length=12 := by simp [T,hc]
  have cl : (C cs).length=15 := by simp [C,hc]
  have a:=load_counts (T cs) S (C cs) cin tl hs (by rw [cl];decide)
  have b:=knownLift_counts R S Z cs cin hr hs hz hc
  have c:=clear_counts (T cs) S (C cs) cin tl hs (by rw [cl];decide)
  have e:=Win977Develop.copyHigh_counts R S hr hs
  simp only [inverse,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,e.1,e.2]
  norm_num

theorem knownLift_slots (R S Z cs : List Wire) (cin : Wire) (hz : Z.length=11) (hc : cs.length=42) :
    Challenge.gateSlots (knownLift R S Z cs cin)≤224 := by
  have h:=Win977Develop.known_slots (mappedRead (X Z cs) false)
    (mappedRead (S.drop 4++S) false) ((R.drop 4).take 16) (C cs) cin
  have len : (mappedRead (X Z cs) false).length=16 := by simp [mappedRead,X,T,hz,hc]
  rw [len] at h
  exact h

theorem forward_slots (R S Z cs : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hz : Z.length=11) (hc : cs.length=42) :
    Challenge.gateSlots (forward R S Z cs cin)≤617 := by
  have cp : Challenge.gateSlots (Win977Develop.copyHigh R S)=10 := by simp [Win977Develop.copyHigh,hr,hs]
  have a:=load_slots (T cs) S (C cs) cin hs
  have b:=Baselines.subInPlace_gateSlots_le (X Z cs) ((R.drop 4).take 16) (C cs) cin
  have xl : (X Z cs).length=16 := by simp [X,T,hz,hc]
  have yl : ((R.drop 4).take 16).length=16 := by simp [hr]
  rw [xl,yl] at b
  have e:=clear_slots (T cs) S (C cs) cin (by simp [T,hc]) hs
  simp only [forward,Challenge.gateSlots_append,cp]
  omega

theorem inverse_slots (R S Z cs : List Wire) (cin : Wire)
    (hr : R.length=20) (hs : S.length=10) (hz : Z.length=11) (hc : cs.length=42) :
    Challenge.gateSlots (inverse R S Z cs cin)≤617 := by
  have a:=load_slots (T cs) S (C cs) cin hs
  have b:=knownLift_slots R S Z cs cin hz hc
  have e:=clear_slots (T cs) S (C cs) cin (by simp [T,hc]) hs
  have cp : Challenge.gateSlots (Win977Develop.copyHigh R S)=10 := by simp [Win977Develop.copyHigh,hr,hs]
  simp only [inverse,Challenge.gateSlots_append,cp]
  omega
#print axioms forward_counts
#print axioms inverse_counts
#print axioms forward_slots
#print axioms inverse_slots
end ECDSAAdd.Entrant.Aux3Develop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Aux3Develop
open Arithmetic Arithmetic.KnownOutputAdder

private theorem bit_member (bits : List MappedBit) (b : MappedBit) (hb : b∈bits)
    (q : Wire) (hq : q∈b.wire) : q∈mappedWires bits :=
  List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩

theorem copy_physical (T S cs : List Wire) (cin : Wire)
    (hn : (cin::(T++S++cs)).Nodup) : GatePhysical (copyLow T S) := by
  apply copyRegister_physical
  · apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp hn q
    have t:=(List.take_sublist 10 T).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  · simp

theorem load_physical (T S cs : List Wire) (cin : Wire)
    (hn : (cin::(T++S++cs)).Nodup) : GatePhysical (load T S cs cin) := by
  have geo:=load_geometry T S cs cin hn
  simp only [load,gatePhysical_append]
  refine ⟨copy_physical T S cs cin hn,mappedAdd_physical _ _ _ _ geo.1 ?_⟩
  intro b hb q hq
  have mem:=bit_member (source S) b hb q hq
  rw [source_wires] at mem
  exact geo.2 q mem

theorem unadd_physical (T S cs : List Wire) (cin : Wire)
    (ht : T.length=12) (hs : S.length=10) (hc : 10≤cs.length)
    (hn : (cin::(T++S++cs)).Nodup) : GatePhysical (unadd T S cs cin) := by
  have geo:=load_geometry T S cs cin hn
  apply KnownSubDevelop.sub_physical _ _ _ _ _
    (by simp [source,mappedRead,ht,hs]) (by simp [negDesired,mappedRead,ht,hs])
    (by simp [ht];omega) geo.1
  · intro b hb q hq
    have mem:=bit_member (source S) b hb q hq
    rw [source_wires] at mem
    exact geo.2 q mem
  · intro b hb q hq
    have mem:=bit_member (negDesired S) b hb q hq
    rw [negDesired_wires] at mem
    exact geo.2 q (List.mem_of_mem_drop mem)

theorem clear_physical (T S cs : List Wire) (cin : Wire)
    (ht : T.length=12) (hs : S.length=10) (hc : 10≤cs.length)
    (hn : (cin::(T++S++cs)).Nodup) : GatePhysical (clear T S cs cin) := by
  simp only [clear,gatePhysical_append]
  exact ⟨unadd_physical T S cs cin ht hs hc hn,copy_physical T S cs cin hn⟩

def auxPorts (T S cs : List Wire) (cin : Wire) : Finset Wire := (T++S++cs++[cin]).toFinset

theorem copy_support (T S cs : List Wire) (cin : Wire) :
    wires (copyLow T S)⊆auxPorts T S cs cin := by
  have h:=copyRegister_wires_subset none S (T.take 10)
  intro q hq
  have mem:=h hq
  simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at mem
  simp only [auxPorts,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases mem with h|h
  · tauto
  · have old:=List.mem_of_mem_take h
    tauto

theorem load_support (T S cs : List Wire) (cin : Wire) :
    wires (load T S cs cin)⊆auxPorts T S cs cin := by
  have cp:=copy_support T S cs cin
  have md:=mappedAdd_wires_subset (source S) (T.drop 1) (cs.take 10) cin
  rw [source_wires] at md
  intro q hq
  simp only [load,wires_append,Finset.mem_union] at hq
  rcases hq with h|h
  · exact cp h
  · have mem:=md h
    simp only [auxPorts,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at mem ⊢
    rcases mem with h|h|h|h
    · tauto
    · have old:=List.mem_of_mem_drop h
      tauto
    · have old:=List.mem_of_mem_take h
      tauto
    · tauto

theorem unadd_support (T S cs : List Wire) (cin : Wire) :
    wires (unadd T S cs cin)⊆auxPorts T S cs cin := by
  have md:=KnownSubDevelop.sub_support (source S) (negDesired S) (T.drop 1) (cs.take 10) cin
  rw [source_wires,negDesired_wires] at md
  intro q hq
  have mem:=md hq
  simp only [auxPorts,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at mem ⊢
  rcases mem with h|h|h|h|h
  · tauto
  · have old:=List.mem_of_mem_drop h
    tauto
  · have old:=List.mem_of_mem_drop h
    tauto
  · have old:=List.mem_of_mem_take h
    tauto
  · tauto

theorem clear_support (T S cs : List Wire) (cin : Wire) :
    wires (clear T S cs cin)⊆auxPorts T S cs cin := by
  simp only [clear,wires_append,Finset.union_subset_iff]
  exact ⟨unadd_support T S cs cin,copy_support T S cs cin⟩

theorem knownLift_physical {R S Z cs : List Wire} {cin : Wire} (g : Geo R S Z cs cin) :
    GatePhysical (knownLift R S Z cs cin) := by
  have bank:=MixedLiteralAdderDevelop.read_geometry (X Z cs) ((R.drop 4).take 16) (C cs) cin g.main_nd
  have yl : ((R.drop 4).take 16).length=16 := by simp [g.r]
  apply KnownOutputAdder.program_physical _ _ _ _ _
    (by simp [mappedRead,g.xlen,yl]) (by simp [mappedRead,g.s,yl])
    (by rw [g.clen,yl]) bank.1
  · intro b hb q hq
    have mem:=bit_member (mappedRead (X Z cs) false) b hb q hq
    rw [mappedRead_wires] at mem
    exact bank.2 q mem
  · intro b hb q hq bad
    have mem:=bit_member (mappedRead (S.drop 4++S) false) b hb q hq
    rw [mappedRead_wires] at mem
    have old : q∈S := by
      rcases List.mem_append.mp mem with h|h
      · exact List.mem_of_mem_drop h
      · exact h
    exact g.main_S q old (by simp only [List.mem_cons,List.mem_append] at bad ⊢;tauto)

#print axioms load_physical
#print axioms clear_physical
#print axioms load_support
#print axioms clear_support
#print axioms knownLift_physical
end ECDSAAdd.Entrant.Aux3Develop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Aux3Develop
open Arithmetic

theorem Geo.noZ_nd {R S Z cs : List Wire} {cin : Wire} (g : Geo R S Z cs cin) :
    (cin::(R++S++cs)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h:=List.nodup_iff_count.mp g.nd q
  simp only [List.count_cons,List.count_append] at h ⊢
  omega

theorem forward_physical {R S Z cs : List Wire} {cin : Wire} (g : Geo R S Z cs cin) :
    GatePhysical (forward R S Z cs cin) := by
  simp only [forward,gatePhysical_append]
  exact ⟨Win977Develop.copyHigh_physical R S cs cin g.noZ_nd,
    load_physical (T cs) S (C cs) cin g.aux_nd,
    subInPlace_physical _ _ _ _ g.main_nd,
    clear_physical (T cs) S (C cs) cin g.tlen g.s (by rw [g.clen];decide) g.aux_nd⟩

theorem inverse_physical {R S Z cs : List Wire} {cin : Wire} (g : Geo R S Z cs cin) :
    GatePhysical (inverse R S Z cs cin) := by
  simp only [inverse,gatePhysical_append]
  exact ⟨load_physical (T cs) S (C cs) cin g.aux_nd,knownLift_physical g,
    clear_physical (T cs) S (C cs) cin g.tlen g.s (by rw [g.clen];decide) g.aux_nd,
    Win977Develop.copyHigh_physical R S cs cin g.noZ_nd⟩

def bigPorts (R S Z cs : List Wire) (cin : Wire) : Finset Wire := (R++S++Z++cs++[cin]).toFinset

theorem aux_ports (R S Z cs : List Wire) (cin : Wire) :
    auxPorts (T cs) S (C cs) cin⊆bigPorts R S Z cs cin := by
  intro q hq
  simp only [auxPorts,bigPorts,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq ⊢
  rcases hq with h|h|h|h
  · have old:=List.mem_of_mem_drop (List.mem_of_mem_take h)
    tauto
  · tauto
  · have old:=List.mem_of_mem_take h
    tauto
  · tauto

theorem copy_ports (R S Z cs : List Wire) (cin : Wire) :
    Win977Develop.ports R S cs cin⊆bigPorts R S Z cs cin := by
  intro q hq
  simp only [Win977Develop.ports,bigPorts,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
  tauto

theorem main_ports (R S Z cs : List Wire) (cin : Wire) :
    (X Z cs++(R.drop 4).take 16++C cs++[cin]).toFinset⊆bigPorts R S Z cs cin := by
  intro q hq
  simp only [X,bigPorts,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq ⊢
  rcases hq with h|h|h|h|h
  · have old:=List.mem_of_mem_drop (List.mem_of_mem_take h)
    tauto
  · have old:=List.mem_of_mem_take h
    tauto
  · have old:=WinArith.mem_win h
    tauto
  · have old:=List.mem_of_mem_take h
    tauto
  · tauto

theorem mainSub_support (R S Z cs : List Wire) (cin : Wire) :
    wires (subInPlace (X Z cs) ((R.drop 4).take 16) (C cs) cin)⊆bigPorts R S Z cs cin := by
  rw [←MixedLiteralAdderDevelop.read_sub_eq]
  have h:=mappedSub_wires_subset (mappedRead (X Z cs) false) ((R.drop 4).take 16) (C cs) cin
  rw [mappedRead_wires] at h
  exact h.trans (main_ports R S Z cs cin)

theorem knownLift_support (R S Z cs : List Wire) (cin : Wire) :
    wires (knownLift R S Z cs cin)⊆bigPorts R S Z cs cin := by
  have h:=KnownOutputAdder.program_support (mappedRead (X Z cs) false)
    (mappedRead (S.drop 4++S) false) ((R.drop 4).take 16) (C cs) cin
  rw [mappedRead_wires,mappedRead_wires] at h
  intro q hq
  have mem:=h hq
  simp only [X,bigPorts,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at mem ⊢
  rcases mem with h|h|h|h|h|h|h
  · have old:=List.mem_of_mem_drop (List.mem_of_mem_take h)
    tauto
  · have old:=List.mem_of_mem_take h
    tauto
  · have old:=List.mem_of_mem_drop h
    tauto
  · tauto
  · have old:=WinArith.mem_win h
    tauto
  · have old:=List.mem_of_mem_take h
    tauto
  · tauto

theorem forward_support (R S Z cs : List Wire) (cin : Wire) :
    wires (forward R S Z cs cin)⊆bigPorts R S Z cs cin := by
  simp only [forward,wires_append,Finset.union_subset_iff]
  exact ⟨(Win977Develop.copyHigh_support R S cs cin).trans (copy_ports R S Z cs cin),
    (load_support (T cs) S (C cs) cin).trans (aux_ports R S Z cs cin),
    mainSub_support R S Z cs cin,
    (clear_support (T cs) S (C cs) cin).trans (aux_ports R S Z cs cin)⟩

theorem inverse_support (R S Z cs : List Wire) (cin : Wire) :
    wires (inverse R S Z cs cin)⊆bigPorts R S Z cs cin := by
  simp only [inverse,wires_append,Finset.union_subset_iff]
  exact ⟨(load_support (T cs) S (C cs) cin).trans (aux_ports R S Z cs cin),knownLift_support R S Z cs cin,
    (clear_support (T cs) S (C cs) cin).trans (aux_ports R S Z cs cin),
    (Win977Develop.copyHigh_support R S cs cin).trans (copy_ports R S Z cs cin)⟩
#print axioms forward_physical
#print axioms inverse_physical
#print axioms forward_support
#print axioms inverse_support
end ECDSAAdd.Entrant.Aux3Develop

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.WinArithAux3SmallDevelop
open Arithmetic WinArith

def zeroR (R : List Wire) : List Wire := (R.drop 20).take 11
def smallF (R S cs : List Wire) (cin : Wire) : Program := Aux3Develop.forward (R.take 20) S (zeroR R) cs cin
def smallI (R S cs : List Wire) (cin : Wire) : Program := Aux3Develop.inverse (R.take 20) S (zeroR R) cs cin

theorem small_geo {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) :
    Aux3Develop.Geo (R.take 20) S (zeroR R) cs cin := by
  refine ⟨by simp [g.r],g.s,by simp [zeroR,g.r],g.c,?_⟩
  apply List.nodup_iff_count.mpr
  intro q
  have h:=g.cnt q
  have used : (R.take 20).count q+(zeroR R).count q≤R.count q := by
    have bound:=(List.take_sublist 31 R).count_le q
    have eq : R.take 31=R.take 20++(R.drop 20).take 11 := List.take_add (i:=20) (j:=11) (l:=R)
    rw [eq,List.count_append] at bound
    exact bound
  simp only [List.count_cons,List.count_append] at h ⊢
  omega

theorem zeroR_zero (R : List Wire) (s : BasisState) (hr : R.length=43) (V : Nat)
    (hv : regValue R s=V) (hfit : V<2^20) : ∀q∈zeroR R,s q=false := by
  have high : regValue (R.drop 20) s=0 := by
    rw [drop_div R 20 (by rw [hr];decide),hv,Nat.div_eq_of_lt hfit]
  intro q hq
  exact (regValue_zero _ _).mp high q (List.mem_of_mem_take hq)

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
  have a:=Aux3Develop.forward_run (small_geo g) s m clean
    (zeroR_zero R s.basis g.r d h.1 (by omega)) cin0 d (by omega) rLow h.2.1
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
  have a:=Aux3Develop.inverse_run (small_geo g) s m clean
    (zeroR_zero R s.basis g.r (977*d) h.1 (by omega)) cin0 d (by omega) rLow h.2.1
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
    toffoliCount (smallF R S cs cin)=25 ∧ measurementCount (smallF R S cs cin)=35 :=
  Aux3Develop.forward_counts (R.take 20) S (zeroR R) cs cin (by simp [g.r]) g.s (by simp [zeroR,g.r]) g.c

theorem smallI_counts {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U) :
    toffoliCount (smallI R S cs cin)=10 ∧ measurementCount (smallI R S cs cin)=35 :=
  Aux3Develop.inverse_counts (R.take 20) S (zeroR R) cs cin (by simp [g.r]) g.s (by simp [zeroR,g.r]) g.c

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
  Aux3Develop.forward_physical (small_geo g)

theorem smallI_physical {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) :
    GatePhysical (smallI R S cs cin) :=
  Aux3Develop.inverse_physical (small_geo g)

theorem smallF_slots {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U) :
    Challenge.gateSlots (smallF R S cs cin)≤617 :=
  Aux3Develop.forward_slots (R.take 20) S (zeroR R) cs cin (by simp [g.r]) g.s (by simp [zeroR,g.r]) g.c

theorem smallI_slots {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U) :
    Challenge.gateSlots (smallI R S cs cin)≤617 :=
  Aux3Develop.inverse_slots (R.take 20) S (zeroR R) cs cin (by simp [g.r]) g.s (by simp [zeroR,g.r]) g.c

theorem enlarge_ports (R S cs : List Wire) (cin : Wire) :
    Aux3Develop.bigPorts (R.take 20) S (zeroR R) cs cin⊆(R++S++cs++[cin]).toFinset := by
  intro q hq
  simp only [Aux3Develop.bigPorts,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,or_assoc] at hq ⊢
  rcases hq with h|h|h|h|h
  · exact Or.inl (List.mem_of_mem_take h)
  · tauto
  · have old:=List.mem_of_mem_drop (List.mem_of_mem_take h)
    tauto
  · tauto
  · tauto

theorem smallF_support (R S cs : List Wire) (cin : Wire) :
    wires (smallF R S cs cin)⊆(R++S++cs++[cin]).toFinset :=
  (Aux3Develop.forward_support (R.take 20) S (zeroR R) cs cin).trans (enlarge_ports R S cs cin)

theorem smallI_support (R S cs : List Wire) (cin : Wire) :
    wires (smallI R S cs cin)⊆(R++S++cs++[cin]).toFinset :=
  (Aux3Develop.inverse_support (R.take 20) S (zeroR R) cs cin).trans (enlarge_ports R S cs cin)
#print axioms smallF_spec
#print axioms smallI_spec
#print axioms smallF_counts
#print axioms smallI_counts
#print axioms smallF_physical
#print axioms smallI_physical
#print axioms smallF_support
#print axioms smallI_support
end ECDSAAdd.Entrant.WinArithAux3SmallDevelop

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
  (WinArithAux3SmallDevelop.smallF R S cs cin ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (copyRegister none ((R.drop 32).take 10) S ++
  addInPlace (U ++ Z.take 10) ((R.drop 0).take 42) (cs.take 41) cin))))
def tInv (R S Z cs U : List Wire) (cin : Wire) : Program :=
  KnownWindowSubDevelop.sub43 R Z cs U cin ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (WinArithAux3SmallDevelop.smallI R S cs cin ++
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
  have s3 := WinArithAux3SmallDevelop.smallF_spec g cl d hd
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
  have s4 := WinArithAux3SmallDevelop.smallI_spec g cl d hd
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
    toffoliCount (tFwd R S Z cs U cin) = 75 ∧ measurementCount (tFwd R S Z cs U cin) = 108 := by
  have s1 := KnownWindowSubDevelop.sub33_counts (cin:=cin) g
  have c2 := cpC ((R.drop 0).take 10) S (by rw [(g.lens 0 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have sm := WinArithAux3SmallDevelop.smallF_counts (cin:=cin) g
  have c4 := cpC S ((R.drop 32).take 10) (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have c5 := cpC ((R.drop 32).take 10) S (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have s6 := addC (U ++ Z.take 10) ((R.drop 0).take 42) (cs.take 41) cin 42
    (g.lens 0 42 10 41 (by omega) (by omega) (by omega)).1
    (g.lens 0 42 10 41 (by omega) (by omega) (by omega)).2.2.2.2.1
    (by rw [(g.lens 0 42 10 41 (by omega) (by omega) (by omega)).2.2.1])
  simp only [tFwd, toffoliCount_append, measurementCount_append, s1.1, s1.2, c2.1, c2.2, sm.1, sm.2, c4.1, c4.2, c5.1, c5.2, s6.1, s6.2]
  exact ⟨trivial, trivial⟩

theorem tInv_counts :
    toffoliCount (tInv R S Z cs U cin) = 71 ∧ measurementCount (tInv R S Z cs U cin) = 109 := by
  have s1 := KnownWindowSubDevelop.sub43_counts (cin:=cin) g
  have c2 := cpC ((R.drop 32).take 10) S (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have c3 := cpC S ((R.drop 32).take 10) (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have sm := WinArithAux3SmallDevelop.smallI_counts (cin:=cin) g
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
    toffoliCount (wFwd L)=75 ∧ measurementCount (wFwd L)=108 := WinArith.tFwd_counts (mLens L hw)
theorem wInv_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (wInv L)=71 ∧ measurementCount (wInv L)=109 := WinArith.tInv_counts (mLens L hw)

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
  · have small:=WinArithAux3SmallDevelop.smallF_support R S cs cin h
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
  · have small:=WinArithAux3SmallDevelop.smallI_support R S cs cin h
    simp only [Mem,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at small ⊢
    tauto
  · exact pieceCp g _ _ (duo g _ _ (mR' g 0 10) (mSS g)) q h
  · exact pieceAdd g _ _ _ (by rw [(L1 0 33 1 32 (by omega) (by omega) (by omega)).1,
      (L1 0 33 1 32 (by omega) (by omega) (by omega)).2.2.2.2.1])
      (by rw [(L1 0 33 1 32 (by omega) (by omega) (by omega)).1,
      (L1 0 33 1 32 (by omega) (by omega) (by omega)).2.2.1])
      (tri g _ _ _ (mU' g 1) (mR' g 0 33) (mC' g 32)) q h

theorem tFwd_slots : Challenge.gateSlots (tFwd R S Z cs U cin) ≤ 1658 := by
  have L1 := g.lens
  have sm := WinArithAux3SmallDevelop.smallF_slots (cin:=cin) g
  have s1 := KnownWindowSubDevelop.sub33_slots (cin:=cin) g
  have a6 := Baselines.addInPlace_gateSlots_le (U ++ Z.take 10) ((R.drop 0).take 42) (cs.take 41) cin
  rw [(L1 0 42 10 41 (by omega) (by omega) (by omega)).2.2.2.2.1] at a6
  simp only [tFwd, Challenge.gateSlots_append, Baselines.copyRegister_gateSlots,
    (L1 0 10 0 0 (by omega) (by omega) (by omega)).1, (L1 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s]
  omega

theorem tInv_slots : Challenge.gateSlots (tInv R S Z cs U cin) ≤ 1675 := by
  have L1 := g.lens
  have sm := WinArithAux3SmallDevelop.smallI_slots (cin:=cin) g
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
    WinArithAux3SmallDevelop.smallF_physical g,copyRegister_physical _ _ _ (g.ndOut 32) (by simp),
    copyRegister_physical _ _ _ (g.ndIn 32) (by simp),addInPlace_physical _ _ _ _ (g.ndB 10 0 42 41)⟩

theorem tInv_physical : GatePhysical (tInv R S Z cs U cin) := by
  simp only [tInv,gatePhysical_append]
  exact ⟨KnownWindowSubDevelop.sub43_physical g,copyRegister_physical _ _ _ (g.ndIn 32) (by simp),
    copyRegister_physical _ _ _ (g.ndOut 32) (by simp),WinArithAux3SmallDevelop.smallI_physical g,
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


-- Low-window `+u` / `-u` on `e` with the carry hosted on `eU`
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KnownTopAdd

/-! ## Low-window `+u` / `-u` on `e` with the carry hosted on `eU` -/

/-- The low 32 bits of `e`. -/
def eLo (L : CuccaroStreamedSquareWideLayout) : List Wire := (eRlow L).take 32
/-- The high 96 bits of the low 128 bits of `e`. -/
def eMid (L : CuccaroStreamedSquareWideLayout) : List Wire := (eRlow L).drop 32

/-- `e_lo + u` in a 33-bit window whose top bit is `eU`. -/
def eAddLo (L : CuccaroStreamedSquareWideLayout) : Program :=
  addInPlace (mU L ++ [eZ0 L]) (eLo L ++ [eU L]) ((eBank L).take 32) L.core.cin
/-- `eU ^= [e_lo < u]`: clears the carry that `eAddLo` left on `eU`. -/
def kapClr (L : CuccaroStreamedSquareWideLayout) : Program :=
  compareLt none (eLo L) (mU L) ((eBank L).take 32) L.core.cin (eU L)
/-- `e_lo - u` modulo `2^32`. -/
def eSubLo (L : CuccaroStreamedSquareWideLayout) : Program :=
  subInPlace (mU L) (eLo L) ((eBank L).take 31) L.core.cin

theorem eLo_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (eLo L).length = 32 := by
  simp [eLo, eRlow, hw.core.product]

theorem mU_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (mU L).length = 32 := by
  simp [mU, hiReg_length L hw]

theorem eBank_take_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (j : Nat) (hj : j ≤ 129) :
    ((eBank L).take j).length = j := by
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  simp [eBank, fp]; omega

/-- `eReg = eLo ++ eMid ++ [eU, eV]` as values. -/
theorem eReg_split (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    regValue (eReg L) t = regValue (eLo L) t + 2^32 * regValue (eMid L) t +
      2^128 * (if t (eU L) = true then 1 else 0) + 2^129 * (if t (eV L) = true then 1 else 0) := by
  obtain ⟨e1, _, _⟩ := eShape L hw
  have rl : (eRlow L).length = 128 := by simp [eRlow, hw.core.product]
  rw [e1, reg_snoc2, rl]
  have sp := regValue_append (eLo L) (eMid L) t
  rw [show eLo L ++ eMid L = eRlow L from List.take_append_drop 32 _, eLo_length L hw] at sp
  rw [sp]

theorem eMid_lt (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    regValue (eMid L) t < 2^96 := by
  have h := regValue_lt (eMid L) t
  have : (eMid L).length = 96 := by simp [eMid, eRlow, hw.core.product]
  rwa [this] at h

theorem eLo_lt (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    regValue (eLo L) t < 2^32 := by
  have h := regValue_lt (eLo L) t
  rwa [eLo_length L hw] at h

/-- The wires of the low-window programs, as one duplicate-free list. -/
theorem lo_nodup (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (j : Nat) (hj : j ≤ 128) :
    (L.core.cin :: eU L :: eZ0 L :: (mU L ++ eLo L ++ (eBank L).take j)).Nodup := by
  have b := eK_nodup L hw hn j hj
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have c := List.nodup_iff_count_le_one.mp b q
  have f1 : (mU L).count q ≤ (hiReg L).count q := (List.drop_sublist 96 _).count_le q
  have f2 : (eLo L).count q ≤ (eRlow L).count q := (List.take_sublist 32 _).count_le q
  simp only [List.count_cons, List.count_append] at c ⊢
  omega

/-- After `eAddLo`: `e = 2^32*(b0/2^32) + (b0%2^32+u)%2^32 + 2^128*kap`, `kap = (b0%2^32+u)/2^32`. -/
theorem eAddLo_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O A b0 : Nat) (hb0 : b0 < 2^128) :
    Triple (BState L base O b0 A) (eAddLo L)
      (BState L base O (2^32*(b0/2^32) + (b0%2^32 + regValue (hiReg L) base / 2^96)%2^32 +
        2^128*((b0%2^32 + regValue (hiReg L) base / 2^96)/2^32)) A) := by
  apply lift_e L hn base O b0 A _ (eAddLo L)
  intro s m h
  obtain ⟨f1, f2, f3, f4, f5⟩ := eK_facts L hw hn base hc O b0 A s.basis h
  let u := regValue (hiReg L) base / 2^96
  have hu : regValue (mU L) s.basis = u := by rw [hi96 L hw, f5]
  have hu32 : u < 2^32 := by rw [← hu]; have := regValue_lt (mU L) s.basis; rwa [mU_length L hw] at this
  have hv := eReg_split L hw s.basis
  rw [h.2.1] at hv
  have hl := eLo_lt L hw s.basis
  have hm := eMid_lt L hw s.basis
  have hU : s.basis (eU L) = false := by
    cases e : s.basis (eU L)
    · rfl
    · simp only [e, if_true] at hv; omega
  have hV : s.basis (eV L) = false := by
    cases e : s.basis (eV L)
    · rfl
    · simp only [e, if_true] at hv; omega
  simp only [hU, hV, Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at hv
  have lo : regValue (eLo L) s.basis = b0 % 2^32 := by omega
  have mid : regValue (eMid L) s.basis = b0 / 2^32 := by omega
  have nd := lo_nodup L hw hn 32 (by omega)
  have nd2 : (L.core.cin :: ((mU L ++ [eZ0 L]) ++ (eLo L ++ [eU L]) ++ (eBank L).take 32)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := List.nodup_iff_count_le_one.mp nd q
    simp only [List.count_cons, List.count_append, List.count_nil] at c ⊢
    omega
  have lx : (mU L ++ [eZ0 L]).length = (eLo L ++ [eU L]).length := by
    simp [mU_length L hw, eLo_length L hw]
  have lk : ((eBank L).take 32).length + 1 = (eLo L ++ [eU L]).length := by
    simp [eBank_take_length L hw 32 (by omega), eLo_length L hw]
  have xv : regValue (mU L ++ [eZ0 L]) s.basis = u := by
    rw [reg_snoc, hu]; simp [f1]
  have yv : regValue (eLo L ++ [eU L]) s.basis = b0 % 2^32 := by
    rw [reg_snoc, lo]; simp [hU]
  obtain ⟨p, ⟨⟨⟨xv', yv'⟩, cv'⟩, kv'⟩⟩ := addInPlace_spec (mU L ++ [eZ0 L]) (eLo L ++ [eU L]) ((eBank L).take 32)
    L.core.cin nd2 lx lk u (b0 % 2^32) false s m ⟨⟨⟨xv, yv⟩, f3⟩, f4 32⟩
  have wl : (eLo L ++ [eU L]).length = 33 := by simp [eLo_length L hw]
  rw [wl] at yv'
  simp only [Bool.toNat_false, Nat.add_zero] at yv'
  have fr : ∀ q, q ∉ eLo L ++ [eU L] → (run (eAddLo L) m s).basis q = s.basis q := by
    intro q hq
    by_cases hx1 : q ∈ mU L ++ [eZ0 L]
    · exact (regValue_eq_iff _ _ _).mp (xv'.trans xv.symm) q hx1
    by_cases hx2 : q ∈ (eBank L).take 32
    · exact (regValue_eq_iff _ _ _).mp (kv'.trans (f4 32).symm) q hx2
    by_cases hx3 : q = L.core.cin
    · subst hx3; exact cv'.trans f3.symm
    apply run_preserves_outside
    rw [eAddLo, addInPlace_wires _ _ _ _ lx lk]
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, not_or] at hx1 hx2 hx3 hq ⊢
    tauto
  -- eMid and eV are outside the window
  have midAway : ∀ q ∈ eMid L, q ∉ eLo L ++ [eU L] := by
    intro q hq hin
    have c := List.nodup_iff_count_le_one.mp (eK_nodup L hw hn 0 (by omega)) q
    have sp := congrArg (List.count q) (List.take_append_drop 32 (eRlow L))
    have pos : 0 < (eMid L).count q := List.count_pos_iff.mpr hq
    simp only [List.mem_append, List.mem_singleton] at hin
    simp only [List.count_cons, List.count_append, List.count_nil] at c sp
    rcases hin with h1 | h1
    · have : 0 < (eLo L).count q := List.count_pos_iff.mpr h1
      simp only [eLo, eMid] at this pos; omega
    · subst h1; simp only [eMid] at pos; simp at c; omega
  have vAway : eV L ∉ eLo L ++ [eU L] := by
    intro hin
    have c := List.nodup_iff_count_le_one.mp (eK_nodup L hw hn 0 (by omega)) (eV L)
    simp only [List.mem_append, List.mem_singleton] at hin
    rcases hin with h1 | h1
    · have : 0 < (eRlow L).count (eV L) := List.count_pos_iff.mpr (List.mem_of_mem_take h1)
      simp only [List.count_cons, List.count_append, List.count_nil] at c; simp at c; omega
    · have nk := eK_nodup L hw hn 0 (by omega)
      rw [List.nodup_cons, List.nodup_cons] at nk
      exact nk.2.1 (by simp [h1])
  refine ⟨p, ?_, ?_⟩
  · have hs := eReg_split L hw (run (eAddLo L) m s).basis
    have mid' : regValue (eMid L) (run (eAddLo L) m s).basis = b0 / 2^32 := by
      rw [← mid]; exact regValue_congr _ _ _ (fun q hq => fr q (midAway q hq))
    have v' : (run (eAddLo L) m s).basis (eV L) = false := (fr _ vAway).trans hV
    have win : regValue (eLo L ++ [eU L]) (run (eAddLo L) m s).basis = (u + b0 % 2^32) % 2^33 := yv'
    rw [reg_snoc, eLo_length L hw] at win
    have hl' := eLo_lt L hw (run (eAddLo L) m s).basis
    rw [hs, mid', v']
    simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero]
    have hb : b0 % 2^32 + u < 2^33 := by omega
    rw [Nat.mod_eq_of_lt (by omega : u + b0 % 2^32 < 2^33)] at win
    cases e : (run (eAddLo L) m s).basis (eU L) <;> simp only [e, Bool.false_eq_true, if_false, if_true] at win ⊢ <;> omega
  · intro q hq
    apply fr
    intro hm2
    apply hq
    obtain ⟨e1, _, _⟩ := eShape L hw
    rw [e1]
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm2 ⊢
    rcases hm2 with h1 | h1
    · exact Or.inl (List.mem_of_mem_take h1)
    · exact Or.inr (Or.inl h1)

/-- `eMid` and `eV` miss every wire of the low-window programs. -/
theorem lo_away (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (q : Wire)
    (hq : q ∈ eMid L ∨ q = eV L) :
    q ≠ L.core.cin ∧ q ≠ eU L ∧ q ≠ eZ0 L ∧ q ∉ eLo L ∧ q ∉ mU L ∧ q ∉ (eBank L).take 32 := by
  have nk := eK_nodup L hw hn 32 (by omega)
  obtain ⟨a1, nk1⟩ := List.nodup_cons.mp nk
  obtain ⟨a2, nk2⟩ := List.nodup_cons.mp nk1
  obtain ⟨a3, nk3⟩ := List.nodup_cons.mp nk2
  obtain ⟨a4, nk4⟩ := List.nodup_cons.mp nk3
  obtain ⟨_, nk5⟩ := List.nodup_cons.mp nk4
  rcases hq with hq | hq
  · have hr : q ∈ eRlow L := List.mem_of_mem_drop hq
    have c := List.nodup_iff_count_le_one.mp nk5 q
    have sp := congrArg (List.count q) (List.take_append_drop 32 (eRlow L))
    have f1 : (mU L).count q ≤ (hiReg L).count q := (List.drop_sublist 96 _).count_le q
    have pos : 0 < (eMid L).count q := List.count_pos_iff.mpr hq
    simp only [List.count_append] at c sp
    simp only [eMid] at pos
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; rw [e] at hr; exact a1 (by simp [hr])
    · intro e; rw [e] at hr; exact a2 (by simp [hr])
    · intro e; rw [e] at hr; exact a4 (by simp [hr])
    · intro h; have := List.count_pos_iff.mpr h; simp only [eLo] at this; omega
    · intro h; have := List.count_pos_iff.mpr h; omega
    · intro h; have := List.count_pos_iff.mpr h; omega
  · subst hq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; exact a1 (by simp [← e])
    · intro e; exact a2 (by simp [e])
    · intro e; exact a3 (by simp [e])
    · intro h; exact a3 (by simp [List.mem_of_mem_take h])
    · intro h; exact a3 (by simp [List.mem_of_mem_drop h])
    · intro h; exact a3 (by simp [h])

/-- `kapClr` clears `eU` when it holds `[e_lo < u]`. -/
theorem kapClr_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O A H l : Nat) (hH : H < 2^96) (hl : l < 2^32) :
    Triple (BState L base O (2^32*H + l + 2^128*(if l < regValue (hiReg L) base / 2^96 then 1 else 0)) A) (kapClr L)
      (BState L base O (2^32*H + l) A) := by
  apply lift_e L hn base O _ A _ (kapClr L)
  intro s m h
  obtain ⟨f1, f2, f3, f4, f5⟩ := eK_facts L hw hn base hc O _ A s.basis h
  set u := regValue (hiReg L) base / 2^96 with hudef
  have hu : regValue (mU L) s.basis = u := by rw [hi96 L hw, f5]
  have hv := eReg_split L hw s.basis
  rw [h.2.1] at hv
  have hl0 := eLo_lt L hw s.basis
  have hm := eMid_lt L hw s.basis
  have key : regValue (eLo L) s.basis = l ∧ regValue (eMid L) s.basis = H ∧
      s.basis (eU L) = decide (l < u) ∧ s.basis (eV L) = false := by
    by_cases hlu : l < u
    · rw [if_pos hlu] at hv
      cases e1 : s.basis (eU L) <;> cases e2 : s.basis (eV L) <;>
        simp only [e1, e2, Bool.false_eq_true, if_false, if_true] at hv <;>
        first | omega | (refine ⟨by omega, by omega, by simp [hlu], rfl⟩)
    · rw [if_neg hlu] at hv
      cases e1 : s.basis (eU L) <;> cases e2 : s.basis (eV L) <;>
        simp only [e1, e2, Bool.false_eq_true, if_false, if_true] at hv <;>
        first | omega | (refine ⟨by omega, by omega, by simp [hlu], rfl⟩)
  obtain ⟨k1, k2, k3, k4⟩ := key
  have nd := lo_nodup L hw hn 32 (by omega)
  have nd2 : (eU L :: L.core.cin :: (eLo L ++ mU L ++ (eBank L).take 32)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := List.nodup_iff_count_le_one.mp nd q
    simp only [List.count_cons, List.count_append, List.count_nil] at c ⊢
    omega
  have lx : (eLo L).length = (mU L).length := by rw [eLo_length L hw, mU_length L hw]
  have lk : ((eBank L).take 32).length = (mU L).length := by rw [eBank_take_length L hw 32 (by omega), mU_length L hw]
  obtain ⟨p, ⟨⟨⟨⟨xv', yv'⟩, kv'⟩, cv'⟩, tv'⟩⟩ := compareLt_spec (eLo L) (mU L) ((eBank L).take 32) L.core.cin (eU L)
    nd2 lx lk l u (decide (l < u)) s m ⟨⟨⟨⟨k1, hu⟩, f4 32⟩, f3⟩, k3⟩
  have fr : ∀ q, q ≠ eU L → (run (kapClr L) m s).basis q = s.basis q := by
    intro q hq
    by_cases hx1 : q ∈ eLo L
    · exact (regValue_eq_iff _ _ _).mp (xv'.trans k1.symm) q hx1
    by_cases hx2 : q ∈ mU L
    · exact (regValue_eq_iff _ _ _).mp (yv'.trans hu.symm) q hx2
    by_cases hx3 : q ∈ (eBank L).take 32
    · exact (regValue_eq_iff _ _ _).mp (kv'.trans (f4 32).symm) q hx3
    by_cases hx4 : q = L.core.cin
    · subst hx4; exact cv'.trans f3.symm
    apply run_preserves_outside
    rw [kapClr, (compareLt_wires none _ _ _ _ _ lx lk).1]
    simp only [Option.toList, List.nil_append, List.mem_toFinset, List.mem_cons, List.mem_append, not_or]
    exact ⟨hq, hx4, ⟨hx1, hx2⟩, hx3⟩
  refine ⟨p, ?_, ?_⟩
  · have hs := eReg_split L hw (run (kapClr L) m s).basis
    have lo' : regValue (eLo L) (run (kapClr L) m s).basis = l := xv'
    have mid' : regValue (eMid L) (run (kapClr L) m s).basis = H := by
      rw [← k2]; exact regValue_congr _ _ _ (fun q hq => fr q (lo_away L hw hn q (Or.inl hq)).2.1)
    have v' : (run (kapClr L) m s).basis (eV L) = false := (fr _ (lo_away L hw hn _ (Or.inr rfl)).2.1).trans k4
    have u' : (run (kapClr L) m s).basis (eU L) = false := by
      have : (run (kapClr L) m s).basis (eU L) = (decide (l < u) ^^ decide (l < u)) := tv'
      simpa using this
    rw [hs, lo', mid', v', u']
    simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero]
    omega
  · intro q hq
    apply fr
    intro e; apply hq; subst e
    obtain ⟨e1, _, _⟩ := eShape L hw
    rw [e1]; simp

/-- `eSubLo`: `e = 2^32*H + l ↦ 2^32*H + (l - u) mod 2^32`. -/
theorem eSubLo_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O A H l : Nat) (hH : H < 2^96) (hl : l < 2^32) :
    Triple (BState L base O (2^32*H + l) A) (eSubLo L)
      (BState L base O (2^32*H + (l + 2^32 - regValue (hiReg L) base / 2^96) % 2^32) A) := by
  apply lift_e L hn base O _ A _ (eSubLo L)
  intro s m h
  obtain ⟨f1, f2, f3, f4, f5⟩ := eK_facts L hw hn base hc O _ A s.basis h
  let u := regValue (hiReg L) base / 2^96
  have hu : regValue (mU L) s.basis = u := by rw [hi96 L hw, f5]
  have hv := eReg_split L hw s.basis
  rw [h.2.1] at hv
  have hl0 := eLo_lt L hw s.basis
  have hm := eMid_lt L hw s.basis
  have key : regValue (eLo L) s.basis = l ∧ regValue (eMid L) s.basis = H ∧
      s.basis (eU L) = false ∧ s.basis (eV L) = false := by
    cases e1 : s.basis (eU L) <;> cases e2 : s.basis (eV L) <;>
      simp only [e1, e2, Bool.false_eq_true, if_false, if_true] at hv <;>
      first | omega | (exact ⟨by omega, by omega, rfl, rfl⟩)
  obtain ⟨k1, k2, k3, k4⟩ := key
  have nd := lo_nodup L hw hn 31 (by omega)
  have nd2 : (L.core.cin :: (mU L ++ eLo L ++ (eBank L).take 31)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := List.nodup_iff_count_le_one.mp nd q
    simp only [List.count_cons, List.count_append, List.count_nil] at c ⊢
    omega
  have lx : (mU L).length = (eLo L).length := by rw [eLo_length L hw, mU_length L hw]
  have lk : ((eBank L).take 31).length + 1 = (eLo L).length := by rw [eBank_take_length L hw 31 (by omega), eLo_length L hw]
  obtain ⟨p, ⟨⟨⟨xv', yv'⟩, cv'⟩, kv'⟩⟩ := subInPlace_spec (mU L) (eLo L) ((eBank L).take 31) L.core.cin
    nd2 lx lk u l s m ⟨⟨⟨hu, k1⟩, f3⟩, f4 31⟩
  have fr : ∀ q, q ∉ eLo L → (run (eSubLo L) m s).basis q = s.basis q := by
    intro q hq
    by_cases hx1 : q ∈ mU L
    · exact (regValue_eq_iff _ _ _).mp (xv'.trans hu.symm) q hx1
    by_cases hx2 : q ∈ (eBank L).take 31
    · exact (regValue_eq_iff _ _ _).mp (kv'.trans (f4 31).symm) q hx2
    by_cases hx3 : q = L.core.cin
    · subst hx3; exact cv'.trans f3.symm
    apply run_preserves_outside
    rw [eSubLo, subInPlace_wires _ _ _ _ lx lk]
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, not_or]
    exact ⟨hx3, ⟨hx1, hq⟩, hx2⟩
  have b31 : ∀ q ∈ (eBank L).take 31, q ∈ (eBank L).take 32 := by
    intro q hq
    have : (eBank L).take 31 = ((eBank L).take 32).take 31 := by rw [List.take_take]; rfl
    rw [this] at hq; exact List.mem_of_mem_take hq
  refine ⟨p, ?_, ?_⟩
  · have hs := eReg_split L hw (run (eSubLo L) m s).basis
    have lo' : regValue (eLo L) (run (eSubLo L) m s).basis = (l + 2^32 - u) % 2^32 := by
      have : regValue (eLo L) (run (eSubLo L) m s).basis = (l + 2^(eLo L).length - u) % 2^(eLo L).length := yv'
      rwa [eLo_length L hw] at this
    have mid' : regValue (eMid L) (run (eSubLo L) m s).basis = H := by
      rw [← k2]; exact regValue_congr _ _ _ (fun q hq => fr q (lo_away L hw hn q (Or.inl hq)).2.2.2.1)
    have v' : (run (eSubLo L) m s).basis (eV L) = false := (fr _ (lo_away L hw hn _ (Or.inr rfl)).2.2.2.1).trans k4
    have u' : (run (eSubLo L) m s).basis (eU L) = false := by
      rw [fr _ ?_, k3]
      intro hin
      have nk := lo_nodup L hw hn 0 (by omega)
      rw [List.nodup_cons, List.nodup_cons] at nk
      exact nk.2.1 (by simp [hin])
    rw [hs, lo', mid', v', u']
    simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero]
    omega
  · intro q hq
    apply fr
    intro hin; apply hq
    obtain ⟨e1, _, _⟩ := eShape L hw
    rw [e1]; exact List.mem_append_left _ (List.mem_of_mem_take hin)

theorem lo_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (eAddLo L) = 32 ∧ measurementCount (eAddLo L) = 32 ∧
    toffoliCount (kapClr L) = 32 ∧ measurementCount (kapClr L) = 32 ∧
    toffoliCount (eSubLo L) = 31 ∧ measurementCount (eSubLo L) = 31 := by
  have lx : (mU L ++ [eZ0 L]).length = (eLo L ++ [eU L]).length := by
    simp [mU_length L hw, eLo_length L hw]
  have lk : ((eBank L).take 32).length + 1 = (eLo L ++ [eU L]).length := by
    simp [eBank_take_length L hw 32 (by omega), eLo_length L hw]
  have a := addInPlace_counts _ _ _ L.core.cin lx lk
  have w33 : (eLo L ++ [eU L]).length = 33 := by simp [eLo_length L hw]
  have lx2 : (eLo L).length = (mU L).length := by rw [eLo_length L hw, mU_length L hw]
  have lk2 : ((eBank L).take 32).length = (mU L).length := by rw [eBank_take_length L hw 32 (by omega), mU_length L hw]
  have b := compareLt_counts none (eLo L) (mU L) ((eBank L).take 32) L.core.cin (eU L) lx2 lk2
  have lx3 : (mU L).length = (eLo L).length := lx2.symm
  have lk3 : ((eBank L).take 31).length + 1 = (eLo L).length := by rw [eBank_take_length L hw 31 (by omega), eLo_length L hw]
  have c := subInPlace_counts _ _ _ L.core.cin lx3 lk3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eAddLo, a.1, w33]
  · rw [eAddLo, a.2, w33]
  · rw [kapClr, b.1, mU_length L hw]; rfl
  · rw [kapClr, b.2.1, mU_length L hw]
  · rw [eSubLo, c.1, eLo_length L hw]
  · rw [eSubLo, c.2, eLo_length L hw]

end ECDSAAdd.Entrant.ControlLoan1589BFFold

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

set_option maxHeartbeats 4000000 in
theorem kap_flip_core (H l u b1 k r : Nat) (hH : H < 2^96) (hl : l < 2^32) (hu : u < 2^32) (h1 : b1 < 2^128)
    (hr : r < 2^32) (hk : l + u = 2^32*k + r) :
    flipE true ((2^32*H + r + 2^130 - b1) % 2^130) =
      flipE true (((2^32*H + l + 2^130 - b1)%2^130 + u)%2^130) + 2^32*k := by
  have k1 : k ≤ 1 := by omega
  simp only [flipE, if_true]
  by_cases hb : b1 ≤ 2^32*H + l
  · have e1 : (2^32*H + l + 2^130 - b1) % 2^130 = 2^32*H + l - b1 := by omega
    rw [e1]
    by_cases hk0 : k = 0
    · subst hk0
      have e2 : (2^32*H + r + 2^130 - b1) % 2^130 = 2^32*H + l + u - b1 := by omega
      have e3 : (2^32*H + l - b1 + u) % 2^130 = 2^32*H + l + u - b1 := by omega
      rw [e2, e3]; omega
    · have hk1 : k = 1 := by omega
      subst hk1
      by_cases hc : b1 ≤ 2^32*H + r
      · have e2 : (2^32*H + r + 2^130 - b1) % 2^130 = 2^32*H + r - b1 := by omega
        have e3 : (2^32*H + l - b1 + u) % 2^130 = 2^32*H + l + u - b1 := by omega
        rw [e2, e3]; omega
      · have e2 : (2^32*H + r + 2^130 - b1) % 2^130 = 2^32*H + r + 2^130 - b1 := by omega
        have e3 : (2^32*H + l - b1 + u) % 2^130 = 2^32*H + l + u - b1 := by omega
        rw [e2, e3]; omega
  · have e1 : (2^32*H + l + 2^130 - b1) % 2^130 = 2^32*H + l + 2^130 - b1 := by omega
    rw [e1]
    by_cases hw : 2^32*H + l + 2^130 - b1 + u < 2^130
    · have e3 : (2^32*H + l + 2^130 - b1 + u) % 2^130 = 2^32*H + l + 2^130 - b1 + u := by omega
      have e2 : (2^32*H + r + 2^130 - b1) % 2^130 = 2^32*H + r + 2^130 - b1 := by omega
      rw [e2, e3]; omega
    · have e3 : (2^32*H + l + 2^130 - b1 + u) % 2^130 = 2^32*H + l + u - b1 := by omega
      by_cases hc : b1 ≤ 2^32*H + r
      · have e2 : (2^32*H + r + 2^130 - b1) % 2^130 = 2^32*H + r - b1 := by omega
        rw [e2, e3]; omega
      · have e2 : (2^32*H + r + 2^130 - b1) % 2^130 = 2^32*H + r + 2^130 - b1 := by omega
        rw [e2, e3]; omega

/-- The low-window `+u` lowers `e` by `2^32*kap`; the flipped fold value rises by the same amount. -/
theorem kap_flip (b0 b1 u : Nat) (h0 : b0 < 2^128) (h1 : b1 < 2^128) (hu : u < 2^32) :
    flipE true ((2^32*(b0/2^32) + (b0%2^32+u)%2^32 + 2^130 - b1) % 2^130) =
      flipE true (((b0+2^130-b1)%2^130 + u)%2^130) + 2^32*((b0%2^32+u)/2^32) := by
  have hb : b0 = 2^32*(b0/2^32) + b0%2^32 := (Nat.div_add_mod b0 (2^32)).symm
  have := kap_flip_core (b0/2^32) (b0%2^32) u b1 ((b0%2^32+u)/2^32) ((b0%2^32+u)%2^32)
    (by omega) (Nat.mod_lt _ (by positivity)) hu h1 (Nat.mod_lt _ (by positivity))
    (Nat.div_add_mod _ _).symm
  rw [← hb] at this
  exact this

set_option maxHeartbeats 4000000 in
/-- Moving `(c-1)*2^32*kap` from the `e` fold to the `W` fold does not change the B-body result. -/
theorem o4K (b0 b1 O2 X : Nat) (g : Bool) (h0 : b0 < 2^128) (h1 : b1 < 2^128) (hO2 : O2 < SquareReduction.p)
    (hg : g = false → b1 = 0 ∧ b0 = 0) :
    (4294968272*flipE g ((2^32*(b0/2^32) + (b0%2^32+b1/2^96)%2^32 + 2^130 - b1) % 2^130) + (SquareReduction.p-1-
      ((X + 4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p))) % SquareReduction.p =
    (4294968272*flipE g (((b0+2^130-b1)%2^130 + b1/2^96)%2^130) + (SquareReduction.p-1-
      ((X + (SquareReduction.p-1-O2)) % SquareReduction.p))) % SquareReduction.p := by
  cases g with
  | false =>
    obtain ⟨e1, e0⟩ := hg rfl
    subst e1; subst e0
    norm_num
  | true =>
    have hu : b1/2^96 < 2^32 := by omega
    rw [kap_flip b0 b1 (b1/2^96) h0 h1 hu]
    generalize flipE true (((b0+2^130-b1)%2^130 + b1/2^96)%2^130) = F
    generalize (b0%2^32+b1/2^96)/2^32 = k
    norm_num [SquareReduction.p, SquareReduction.B, SquareReduction.c] at hO2 ⊢
    omega

end ECDSAAdd.Entrant.ControlLoan1589BFFold

namespace ECDSAAdd.Entrant.WinArith
open ECDSAAdd ECDSAAdd.Arithmetic Instr

/-! ## The `976*2^32*kap` pattern on the zero pad `Z` -/

theorem list11 {α : Type} (Z : List α) (h : Z.length = 11) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10, Z = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] := by
  rcases Z with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ |
    ⟨a9, _ | ⟨a10, _ | ⟨a11, Z⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, rfl⟩

/-- The pad wires of bits 4, 6, 7, 8, 9 (`976 = 2^4+2^6+2^7+2^8+2^9`). -/
def zpat (Z : List Wire) : List Wire := [Z.getD 4 0, Z.getD 6 0, Z.getD 7 0, Z.getD 8 0, Z.getD 9 0]
/-- `Z ^= 976*kap` on a clear pad. -/
def kpat (k : Wire) (Z : List Wire) : Program :=
  [.CX k (Z.getD 4 0), .CX k (Z.getD 6 0), .CX k (Z.getD 7 0), .CX k (Z.getD 8 0), .CX k (Z.getD 9 0)]
/-- The frame with the pattern applied. -/
def kz (t : BasisState) (k : Wire) (Z : List Wire) : BasisState :=
  fun q => if q ∈ zpat Z then (t q ^^ t k) else t q

theorem zpat_sub (Z : List Wire) (hz : Z.length = 11) : ∀ q ∈ zpat Z, q ∈ Z := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, rfl⟩ := list11 Z hz
  intro q hq; simp [zpat] at hq ⊢; tauto

theorem kpat_run (k : Wire) (Z : List Wire) (hz : Z.length = 11) (hZ : Z.Nodup) (hk : k ∉ Z)
    (m : List Bool) (s : State) :
    run (kpat k Z) m s = ⟨s.phase, fun q => if q ∈ zpat Z then (s.basis q ^^ s.basis k) else s.basis q⟩ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, rfl⟩ := list11 Z hz
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hZ hk
  simp only [kpat, zpat, List.getD_cons_succ, List.getD_cons_zero, run]
  congr 1
  funext q
  simp only [writeBit, Function.update_apply, List.mem_cons, List.not_mem_nil, or_false]
  by_cases q4 : q = a4 <;> by_cases q6 : q = a6 <;> by_cases q7 : q = a7 <;> by_cases q8 : q = a8 <;>
    by_cases q9 : q = a9 <;> simp_all

theorem kpat_PS {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) (k : Wire)
    (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (t : BasisState) (V D : Nat) :
    Triple (PS R S t V D) (kpat k Z) (PS R S (kz t k Z) V D) := by
  have zn : Z.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have := g.cnt q
    simp only [List.count_cons, List.count_append] at this; omega
  intro s m h
  rw [kpat_run k Z g.z zn hkZ m s]
  have zR : ∀ q ∈ zpat Z, q ∉ R := fun q hq => g.ZR q (zpat_sub Z g.z q hq)
  have zS : ∀ q ∈ zpat Z, q ∉ S := fun q hq => g.ZS q (zpat_sub Z g.z q hq)
  have same : ∀ q, q ∉ zpat Z → (if q ∈ zpat Z then (s.basis q ^^ s.basis k) else s.basis q) = s.basis q := by
    intro q hq; simp [hq]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => same q (fun hz => zR q hz hq))).trans h.1
  · exact (regValue_congr _ _ _ (fun q hq => same q (fun hz => zS q hz hq))).trans h.2.1
  · intro q h1 h2
    have sk : s.basis k = t k := h.2.2 k hkR hkS
    simp only [kz]
    by_cases hq : q ∈ zpat Z
    · simp only [hq, if_true, h.2.2 q h1 h2, sk]
    · simp only [hq, if_false, h.2.2 q h1 h2]

theorem kz_kz (t : BasisState) (k : Wire) (Z : List Wire) (hz : Z.length = 11) (hk : k ∉ Z) :
    kz (kz t k Z) k Z = t := by
  funext q
  have kn : k ∉ zpat Z := fun h => hk (zpat_sub Z hz k h)
  simp only [kz, kn, if_false]
  by_cases hq : q ∈ zpat Z <;> simp [hq]

theorem kpat_masked (k : Wire) (Z : List Wire) (hz : Z.length = 11) : kpat k Z = maskedConstant k Z 976 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, rfl⟩ := list11 Z hz
  simp [kpat, maskedConstant]

/-- In the patterned frame, the source `U ++ Z.take 11` holds `u + 2^32*976*kap`. -/
theorem valK {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u : Nat) (hu : regValue U t = u) (k : Wire) (hkZ : k ∉ Z) (V D : Nat) :
    ∀ s, PS R S (kz t k Z) V D s → regValue (U ++ Z.take 11) s = u + 2^32*(976*(if t k then 1 else 0)) := by
  intro s h
  have zn : Z.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have := g.cnt q
    simp only [List.count_cons, List.count_append] at this; omega
  have uz : ∀ q ∈ U, q ∉ Z := fun q h1 h2 => g.away U Z q h1 h2 (by simp only [List.count_cons, List.count_append]; omega)
  have uv : regValue U s = u := by
    rw [← hu]
    apply regValue_congr
    intro q hq
    rw [h.2.2 q (g.UR q hq) (g.US q hq)]
    simp only [kz]
    have : q ∉ zpat Z := fun hz => uz q hq (zpat_sub Z g.z q hz)
    simp [this]
  have e1 : regValue Z s = regValue Z (kz t k Z) :=
    regValue_congr _ _ _ (fun q hq => h.2.2 q (g.ZR q hq) (g.ZS q hq))
  have e2 : kz t k Z = (run (kpat k Z) [] (⟨false, t⟩ : State)).basis := by
    rw [kpat_run k Z g.z zn hkZ]; rfl
  have mc := maskedConstant_correct k Z 976 zn hkZ (by rw [g.z]; norm_num) (⟨false, t⟩ : State) []
  rw [← kpat_masked k Z g.z, ← e2] at mc
  have z0 : regValue Z t = 0 := (regValue_zero _ _).mpr cl.z
  have zv : regValue Z s = if t k then 976 else 0 := by
    rw [e1, mc.2.2]; simp only [z0, Nat.zero_xor]
  rw [regValue_append, uv, g.u, List.take_of_length_le (by rw [g.z]), zv]
  cases t k <;> simp

/-- `R : u + d ↦ u + c*d + 976*2^32*kap`: `tFwd` with the pattern of `k` added in its last step. -/
def tFwdK (R S Z cs U : List Wire) (cin k : Wire) : Program :=
  KnownWindowSubDevelop.sub33 R Z cs U cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  (WinArithAux3SmallDevelop.smallF R S cs cin ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (kpat k Z ++ (addInPlace (U ++ Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin ++ kpat k Z))))))

theorem tFwdK_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (h35 : u + d < 2^35) :
    Triple (PS R S t (u+d) 0) (tFwdK R S Z cs U cin k)
      (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) := by
  have s1 := KnownWindowSubDevelop.sub33_spec g cl u d hu hu32 hd
  have s2 := tcopy_in R S 0 t d 0 (by rw [g.r]; omega) g.s (g.ndIn 0) g.SR
  have s3 := WinArithAux3SmallDevelop.smallF_spec g cl d hd
  have s4 := tcopy_out R S 32 t (977*d) d g.rnd (by rw [g.r]; omega) g.s (g.ndOut 32) g.SR
  have s5 := tcopy_in R S 32 t (977*d + 2^32*d) d (by rw [g.r]; omega) g.s (g.ndIn 32) g.SR
  have p1 := kpat_PS g k hkR hkS hkZ t (977*d + 2^32*d) 0
  have cinZ : cin ∉ Z := fun h => g.away [cin] Z cin (by simp) h
    (by simp only [List.count_cons, List.count_append, List.count_nil]; omega)
  have csZ : ∀ q ∈ cs, q ∉ Z := fun q h1 h2 => g.away cs Z q h1 h2
    (by simp only [List.count_cons, List.count_append]; omega)
  have kzc : kz t k Z cin = false := by
    have : cin ∉ zpat Z := fun h => cinZ (zpat_sub Z g.z cin h)
    simp [kz, this, cl.cin]
  have kzs : ∀ q ∈ cs.take 42, kz t k Z q = false := by
    intro q hq
    have hq' := List.mem_of_mem_take hq
    have : q ∉ zpat Z := fun h => csZ q hq' (zpat_sub Z g.z q h)
    simp [kz, this, cl.c q hq']
  have s6 := tstep_add R S (U ++ Z.take 11) (cs.take 42) cin 0 43 (kz t k Z) (977*d + 2^32*d) 0
    (u + 2^32*(976*(if t k then 1 else 0))) g.rnd (by simp [g.r])
    (g.ndU 11 0 43 42) (by simp [g.u, g.z]) (by simp [g.c]) g.SR g.cinR g.cinS (g.csR 42) (g.csS 42) kzc
    kzs (valK g cl u hu k hkZ _ _) (by
      have hv : 977*d + 2^32*d < 2^42 := by omega
      rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt (by omega : 977*d + 2^32*d < 2^43)]
      cases t k <;> simp <;> omega)
  have p2 := kpat_PS g k hkR hkS hkZ (kz t k Z) (977*d + 2^32*d + 2^0*(u + 2^32*(976*(if t k then 1 else 0)))) 0
  rw [kz_kz t k Z g.z hkZ] at p2
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
  unfold tFwdK
  exact seqv s1 (PS_val (by omega)) (seqv s2 (PS_dval a2)
    (seqv s3 (fun _ h => h) (seqv s4 (PS_val a4) (seqv s5 (PS_dval a5)
    (seqv p1 (fun _ h => h) (seqv s6 (fun _ h => h)
    (Triple.conseq (fun s h => h) p2 (PS_val (by cases t k <;> simp <;> omega)))))))))

/-- `sub43` in the patterned frame: subtracts `u + 976*2^32*kap`, leaving `c*d`. -/
theorem sub43K_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (k : Wire) (hkZ : k ∉ Z) :
    Triple (PS R S (kz t k Z) (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0)
      (KnownWindowSubDevelop.sub43 R Z cs U cin) (PS R S (kz t k Z) (4294968273*d) 0) := by
  let X := u + 2^32*(976*(if t k then 1 else 0))
  have h43 : u + 4294968273*d + 2^32*(976*(if t k then 1 else 0)) < 2^43 := by cases t k <;> simp <;> omega
  have cinZ : cin ∉ Z := fun h => g.away [cin] Z cin (by simp) h
    (by simp only [List.count_cons, List.count_append, List.count_nil]; omega)
  have csZ : ∀ q ∈ cs, q ∉ Z := fun q h1 h2 => g.away cs Z q h1 h2
    (by simp only [List.count_cons, List.count_append]; omega)
  have kzc : kz t k Z cin = false := by
    have : cin ∉ zpat Z := fun h => cinZ (zpat_sub Z g.z cin h)
    simp [kz, this, cl.cin]
  have kzs : ∀ q ∈ cs.take 42, kz t k Z q = false := by
    intro q hq
    have hq' := List.mem_of_mem_take hq
    have : q ∉ zpat Z := fun h => csZ q hq' (zpat_sub Z g.z q h)
    simp [kz, this, cl.c q hq']
  have valf : ∀ s, PS R S (kz t k Z) (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0 s →
      regValue (U ++ Z) s = X := by
    intro s h
    have := valK g cl u hu k hkZ _ _ s h
    rwa [List.take_of_length_le (by rw [g.z])] at this
  have normal := tstep_sub R S (U++Z) (cs.take 42) cin 0 43 (kz t k Z)
    (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0 X g.rnd
    (by simp [g.r]) (g.ndUZ 0 43 42) (by simp [g.u,g.z]) (by simp [g.c])
    g.SR g.cinR g.cinS (g.csR 42) (g.csS 42) kzc kzs valf (by
      rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt h43]; simp only [X]; omega)
  intro s m h
  let x := U++Z
  let y := (R.drop 0).take 43
  have yl : y.length=43 := by simp [y,g.r]
  have xl : x.length=43 := by simp [x,g.u,g.z]
  have yv : regValue y s.basis = u + 4294968273*d + 2^32*(976*(if t k then 1 else 0)) := by
    rw [win_mid R 0 43 (by simp [g.r]),h.1]
    simpa using Nat.mod_eq_of_lt h43
  have xv : regValue x s.basis = X := valf s.basis h
  have cs0 : ∀q∈cs.take 42,s.basis q=false := by
    intro q hq
    exact (h.2.2 q (g.csR 42 q hq) (g.csS 42 q hq)).trans (kzs q hq)
  have cin0 : s.basis cin=false := (h.2.2 cin g.cinR g.cinS).trans kzc
  have hv : (regValue y s.basis+2^y.length-regValue x s.basis)%2^y.length=4294968273*d := by
    rw [yv,xv,yl]
    simp only [X]
    cases t k <;> norm_num <;> omega
  have known (i : Nat) (hi : i<MixedLiteralAdderDevelop.mask43.length)
      (hk : MixedLiteralAdderDevelop.mask43.getD i false=true) :
      (2^y.length-1-4294968273*d).testBit i=true := by
    rw [yl]
    exact MixedLiteralAdderDevelop.complement_mask43 d i (by omega)
      (by simpa [MixedLiteralAdderDevelop.mask43] using hi) hk
  have eq : run (KnownWindowSubDevelop.sub43 R Z cs U cin) m s=run (subInPlace x y (cs.take 42) cin) m s :=
    MixedLiteralAdderDevelop.read_sub_replace x y (cs.take 42) MixedLiteralAdderDevelop.mask43 cin (g.ndUZ 0 43 42)
      (by rw [xl,yl]) (by simp [MixedLiteralAdderDevelop.mask43,yl]) (by simp [g.c,yl])
      s m cs0 cin0 (4294968273*d) hv known
  rw [eq]
  have res := normal s m h
  refine ⟨res.1, PS_val (show u + 4294968273*d + 2^32*(976*(if t k then 1 else 0)) - 2^0*X = 4294968273*d by
    simp only [X]; cases t k <;> simp <;> omega) _ res.2⟩

/-- `tInv` with the pattern of `k` removed in its first step. -/
def tInvK (R S Z cs U : List Wire) (cin k : Wire) : Program :=
  kpat k Z ++ (KnownWindowSubDevelop.sub43 R Z cs U cin ++ (kpat k Z ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (WinArithAux3SmallDevelop.smallI R S cs cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  addInPlace (U ++ Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin))))))

theorem tInvK_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (h35 : u + d < 2^35) :
    Triple (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) (tInvK R S Z cs U cin k)
      (PS R S t (u+d) 0) := by
  have p1 := kpat_PS g k hkR hkS hkZ t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0
  have s1 := sub43K_spec g cl u d hu hu32 hd k hkZ
  have p2 := kpat_PS g k hkR hkS hkZ (kz t k Z) (4294968273*d) 0
  rw [kz_kz t k Z g.z hkZ] at p2
  have s2 := tcopy_in R S 32 t (977*d + 2^32*d) 0 (by rw [g.r]; omega) g.s (g.ndIn 32) g.SR
  have s3 := tcopy_out R S 32 t (977*d + 2^32*d) d g.rnd (by rw [g.r]; omega) g.s (g.ndOut 32) g.SR
  have s4 := WinArithAux3SmallDevelop.smallI_spec g cl d hd
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
  unfold tInvK
  exact seqv p1 (fun _ h => h) (seqv s1 (fun _ h => h) (seqv p2 (PS_val (by ring))
    (seqv s2 (PS_dval a2) (seqv s3 (PS_val a3)
    (seqv s4 (fun _ h => h) (seqv s5 (PS_dval a5)
    (Triple.conseq (fun s h => h) s6 (PS_val (by omega)))))))))

end ECDSAAdd.Entrant.WinArith

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-! ## The `W` fold with the carry `kap` of the low-window `+u` -/

/-- Bit 64 of the high work half (bit 64 of the `W`-core source). -/
def w192 (L : CuccaroStreamedSquareWideLayout) : Wire := ((L.core.work.drop 128).drop 43).getD 21 0
/-- `w192 ^= kap`. -/
def kw (L : CuccaroStreamedSquareWideLayout) : Program := [Instr.CX (eU L) (w192 L)]
def wFwdK (L : CuccaroStreamedSquareWideLayout) : Program :=
  WinArith.tFwdK (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L)
def wInvK (L : CuccaroStreamedSquareWideLayout) : Program :=
  WinArith.tInvK (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L)
/-- The `W` core with `2^64*kap` added to its source. -/
def wCoreK (L : CuccaroStreamedSquareWideLayout) : Program := kw L ++ (wCoreTq L ++ kw L)

theorem eU_mem_prod (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : eU L ∈ L.core.product := by
  have l : (L.core.product.drop 256).length = 2 := by simp [hw.core.product]
  obtain ⟨a, b, e⟩ := List.length_eq_two.mp l
  have h1 : eU L = a := by simp [eU, e]
  have h2 : a ∈ L.core.product.drop 256 := by rw [e]; simp
  rw [h1]; exact List.mem_of_mem_drop h2

theorem eU_away (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    eU L ∉ L.foldPad ∧ eU L ∉ L.core.work ∧ eU L ∉ L.core.out := by
  have c := lay_pos L hn (eU L)
  have a := List.count_pos_iff.mpr (eU_mem_prod L hw)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> (have b := List.count_pos_iff.mpr h; omega)

theorem tail_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    ((L.core.work.drop 128).drop 43).length = 85 := by simp [hw.core.work]

theorem w192_tail (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    w192 L ∈ (L.core.work.drop 128).drop 43 := by
  unfold w192
  rw [List.getD_eq_getElem _ _ (by rw [tail_length L hw]; omega)]
  exact List.getElem_mem _

theorem w192_facts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    w192 L ∈ L.core.work ∧ w192 L ∈ L.core.work.drop 163 ∧ w192 L ∉ mR L ∧ w192 L ∉ mS L ∧
      w192 L ∉ L.core.out ∧ w192 L ≠ eU L ∧ w192 L ∉ mZ L := by
  have wnd : L.core.work.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have := lay_pos L hn q; omega
  have t := w192_tail L hw
  have t' : w192 L ∈ L.core.work.drop (128+43) := by rw [← List.drop_drop]; exact t
  have hw1 : w192 L ∈ L.core.work := List.mem_of_mem_drop t'
  have h163 : w192 L ∈ L.core.work.drop 163 := by
    have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
    rw [this] at t'; exact List.mem_of_mem_drop t'
  refine ⟨hw1, h163, fun hr => WinArith.win_away L.core.work wnd 128 43 _ (Or.inr t') hr,
    fun hs => work_pad L hn _ hw1 (mS_pad L _ hs), work_out L hn _ hw1, fun e => ?_,
    fun hz => work_pad L hn _ hw1 (mZ_pad L _ hz)⟩
  exact (eU_away L hw hn).2.1 (e ▸ hw1)

/-- The tail of the high work half holds `2^21*K` when only `w192` may be set. -/
theorem tail_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (st : BasisState) (K : Nat) (hK : K ≤ 1) (hk : st (w192 L) = decide (K = 1))
    (hz : ∀ q ∈ (L.core.work.drop 128).drop 43, q ≠ w192 L → st q = false) :
    regValue ((L.core.work.drop 128).drop 43) st = 2^21 * K := by
  have wnd : L.core.work.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have := lay_pos L hn q; omega
  set T := (L.core.work.drop 128).drop 43 with hT
  have tl : T.length = 85 := tail_length L hw
  have tnd : T.Nodup := (wnd.sublist (List.drop_sublist _ _)).sublist (List.drop_sublist _ _)
  have e1 : T = T.take 21 ++ T.drop 21 := (List.take_append_drop 21 T).symm
  have e2 : T.drop 21 = T[21]'(by omega) :: T.drop 22 := List.drop_eq_getElem_cons (by omega)
  have g21 : T[21]'(by omega) = w192 L := by
    simp only [w192, hT]; rw [List.getD_eq_getElem _ _ (by rw [← hT, tl]; omega)]
  rw [g21] at e2
  have nd2 : (T.take 21 ++ (w192 L :: T.drop 22)).Nodup := by rw [← e2, ← e1]; exact tnd
  have hnot1 : w192 L ∉ T.take 21 := by
    intro h
    have c := List.nodup_iff_count_le_one.mp nd2 (w192 L)
    have a := List.count_pos_iff.mpr h
    simp only [List.count_append, List.count_cons_self] at c; omega
  have hnot2 : w192 L ∉ T.drop 22 := by
    rw [List.nodup_append] at nd2
    exact (List.nodup_cons.mp nd2.2.1).1
  have z1 : regValue (T.take 21) st = 0 :=
    (regValue_zero _ _).mpr (fun q hq => hz q (List.mem_of_mem_take hq) (fun e => hnot1 (e ▸ hq)))
  have z2 : regValue (T.drop 22) st = 0 :=
    (regValue_zero _ _).mpr (fun q hq => hz q (List.mem_of_mem_drop hq) (fun e => hnot2 (e ▸ hq)))
  rw [e1, e2, regValue_append, z1]
  have l21 : (T.take 21).length = 21 := by simp [tl]
  rw [l21]
  simp only [regValue, List.foldr_cons] at z2 ⊢
  rw [z2, hk]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hK with h | h <;> subst h <;> simp

end ECDSAAdd.Entrant.ControlLoan1589BFFold

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

end ECDSAAdd.Entrant.ControlLoan1589BFFold

namespace ECDSAAdd.Entrant.WinArith
open ECDSAAdd ECDSAAdd.Arithmetic Instr

/-! ## Static facts of the patterned transforms -/

theorem kpat_counts (k : Wire) (Z : List Wire) : toffoliCount (kpat k Z) = 0 ∧ measurementCount (kpat k Z) = 0 := by
  simp [kpat, toffoliCount, measurementCount]

theorem kpat_slots (k : Wire) (Z : List Wire) : Challenge.gateSlots (kpat k Z) = 5 := by
  simp [kpat, Challenge.gateSlots, Challenge.instructionSlots]

theorem kpat_wires (k : Wire) (Z : List Wire) (hz : Z.length = 11) : ∀ q ∈ wires (kpat k Z), q = k ∨ q ∈ Z := by
  intro q hq
  rw [kpat_masked k Z hz] at hq
  have h := List.mem_toFinset.mp (maskedConstant_wires_subset k Z 976 hq)
  simpa using h

section CountsK
variable {R S Z cs U : List Wire} {cin : Wire} (g : Lens R S Z cs U)
include g

theorem tFwdK_counts (k : Wire) :
    toffoliCount (tFwdK R S Z cs U cin k) = 76 ∧ measurementCount (tFwdK R S Z cs U cin k) = 109 := by
  have s1 := KnownWindowSubDevelop.sub33_counts (cin:=cin) g
  have c2 := cpC ((R.drop 0).take 10) S (by rw [(g.lens 0 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have sm := WinArithAux3SmallDevelop.smallF_counts (cin:=cin) g
  have c4 := cpC S ((R.drop 32).take 10) (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have c5 := cpC ((R.drop 32).take 10) S (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have s6 := addC (U ++ Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin 43
    (g.lens 0 43 11 42 (by omega) (by omega) (by omega)).1
    (g.lens 0 43 11 42 (by omega) (by omega) (by omega)).2.2.2.2.1
    (by rw [(g.lens 0 43 11 42 (by omega) (by omega) (by omega)).2.2.1])
  have kp := kpat_counts k Z
  simp only [tFwdK, toffoliCount_append, measurementCount_append, s1.1, s1.2, c2.1, c2.2, sm.1, sm.2, c4.1, c4.2,
    c5.1, c5.2, s6.1, s6.2, kp.1, kp.2]
  exact ⟨trivial, trivial⟩

theorem tInvK_counts (k : Wire) :
    toffoliCount (tInvK R S Z cs U cin k) = 71 ∧ measurementCount (tInvK R S Z cs U cin k) = 109 := by
  have s1 := KnownWindowSubDevelop.sub43_counts (cin:=cin) g
  have c2 := cpC ((R.drop 32).take 10) S (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have c3 := cpC S ((R.drop 32).take 10) (by rw [(g.lens 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have sm := WinArithAux3SmallDevelop.smallI_counts (cin:=cin) g
  have c5 := cpC ((R.drop 0).take 10) S (by rw [(g.lens 0 10 0 0 (by omega) (by omega) (by omega)).1, g.s])
  have s6 := addC (U ++ Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin 33
    (g.lens 0 33 1 32 (by omega) (by omega) (by omega)).1
    (g.lens 0 33 1 32 (by omega) (by omega) (by omega)).2.2.2.2.1
    (by rw [(g.lens 0 33 1 32 (by omega) (by omega) (by omega)).2.2.1])
  have kp := kpat_counts k Z
  simp only [tInvK, sm.1, sm.2, toffoliCount_append, measurementCount_append, s1.1, s1.2, c2.1, c2.2, c3.1, c3.2,
    c5.1, c5.2, s6.1, s6.2, kp.1, kp.2]
  exact ⟨trivial, trivial⟩

theorem tFwdK_mem (k : Wire) : ∀ q ∈ wires (tFwdK R S Z cs U cin k), Mem R S Z cs U cin q ∨ q = k := by
  have L1 := g.lens
  intro q hq
  have kz : ∀ q ∈ wires (kpat k Z), Mem R S Z cs U cin q ∨ q = k := by
    intro q h
    rcases kpat_wires k Z g.z q h with e | e
    · exact Or.inr e
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
  have old : ∀ q ∈ wires (tFwd R S Z cs U cin), Mem R S Z cs U cin q := tFwd_mem g
  simp only [tFwdK, wires_append, Finset.mem_union] at hq
  simp only [tFwd, wires_append, Finset.mem_union] at old
  rcases hq with h|h|h|h|h|h|h|h
  · exact Or.inl (old q (Or.inl h))
  · exact Or.inl (old q (Or.inr (Or.inl h)))
  · exact Or.inl (old q (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (old q (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (old q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact kz q h
  · exact Or.inl (pieceAdd g _ _ _ (by rw [(L1 0 43 11 42 (by omega) (by omega) (by omega)).1,
      (L1 0 43 11 42 (by omega) (by omega) (by omega)).2.2.2.2.1])
      (by rw [(L1 0 43 11 42 (by omega) (by omega) (by omega)).1,
      (L1 0 43 11 42 (by omega) (by omega) (by omega)).2.2.1])
      (tri g _ _ _ (mU' g 11) (mR' g 0 43) (mC' g 42)) q h)
  · exact kz q h

theorem tInvK_mem (k : Wire) : ∀ q ∈ wires (tInvK R S Z cs U cin k), Mem R S Z cs U cin q ∨ q = k := by
  intro q hq
  have kz : ∀ q ∈ wires (kpat k Z), Mem R S Z cs U cin q ∨ q = k := by
    intro q h
    rcases kpat_wires k Z g.z q h with e | e
    · exact Or.inr e
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
  have old : ∀ q ∈ wires (tInv R S Z cs U cin), Mem R S Z cs U cin q := tInv_mem g
  simp only [tInvK, wires_append, Finset.mem_union] at hq
  simp only [tInv, wires_append, Finset.mem_union] at old
  rcases hq with h|h|h|h|h|h|h|h
  · exact kz q h
  · exact Or.inl (old q (Or.inl h))
  · exact kz q h
  · exact Or.inl (old q (Or.inr (Or.inl h)))
  · exact Or.inl (old q (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (old q (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (old q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inl (old q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem tFwdK_slots (k : Wire) : Challenge.gateSlots (tFwdK R S Z cs U cin k) ≤ 1680 := by
  have L1 := g.lens
  have sm := WinArithAux3SmallDevelop.smallF_slots (cin:=cin) g
  have s1 := KnownWindowSubDevelop.sub33_slots (cin:=cin) g
  have a6 := Baselines.addInPlace_gateSlots_le (U ++ Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin
  rw [(L1 0 43 11 42 (by omega) (by omega) (by omega)).2.2.2.2.1] at a6
  have kp := kpat_slots k Z
  simp only [tFwdK, Challenge.gateSlots_append, Baselines.copyRegister_gateSlots, kp,
    (L1 0 10 0 0 (by omega) (by omega) (by omega)).1, (L1 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s]
  have old := tFwd_slots (cin := cin) g
  have a6o := Baselines.addInPlace_gateSlots_le (U ++ Z.take 10) ((R.drop 0).take 42) (cs.take 41) cin
  rw [(L1 0 42 10 41 (by omega) (by omega) (by omega)).2.2.2.2.1] at a6o
  simp only [tFwd, Challenge.gateSlots_append, Baselines.copyRegister_gateSlots,
    (L1 0 10 0 0 (by omega) (by omega) (by omega)).1, (L1 32 10 0 0 (by omega) (by omega) (by omega)).1, g.s] at old
  omega

theorem tInvK_slots (k : Wire) : Challenge.gateSlots (tInvK R S Z cs U cin k) ≤ 1685 := by
  have old := tInv_slots (cin := cin) g
  have kp := kpat_slots k Z
  simp only [tInv, Challenge.gateSlots_append] at old
  simp only [tInvK, Challenge.gateSlots_append, kp]
  omega

end CountsK

section PhysK
variable {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
include g

theorem kpat_physical (k : Wire) (hkZ : k ∉ Z) : GatePhysical (kpat k Z) := by
  rw [kpat_masked k Z g.z]; exact maskedConstant_physical k Z 976 hkZ

theorem tFwdK_physical (k : Wire) (hkZ : k ∉ Z) : GatePhysical (tFwdK R S Z cs U cin k) := by
  simp only [tFwdK,gatePhysical_append]
  exact ⟨KnownWindowSubDevelop.sub33_physical g,copyRegister_physical _ _ _ (g.ndIn 0) (by simp),
    WinArithAux3SmallDevelop.smallF_physical g,copyRegister_physical _ _ _ (g.ndOut 32) (by simp),
    copyRegister_physical _ _ _ (g.ndIn 32) (by simp), kpat_physical g k hkZ,
    addInPlace_physical _ _ _ _ (g.ndB 11 0 43 42), kpat_physical g k hkZ⟩

theorem tInvK_physical (k : Wire) (hkZ : k ∉ Z) : GatePhysical (tInvK R S Z cs U cin k) := by
  simp only [tInvK,gatePhysical_append]
  exact ⟨kpat_physical g k hkZ, KnownWindowSubDevelop.sub43_physical g, kpat_physical g k hkZ,
    copyRegister_physical _ _ _ (g.ndIn 32) (by simp),
    copyRegister_physical _ _ _ (g.ndOut 32) (by simp),WinArithAux3SmallDevelop.smallI_physical g,
    copyRegister_physical _ _ _ (g.ndIn 0) (by simp),addInPlace_physical _ _ _ _ (g.ndB 1 0 33 32)⟩

end PhysK
end ECDSAAdd.Entrant.WinArith

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-! ## Static facts of the new B-body pieces -/

theorem eLo_eReg (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (q : Wire) (h : q ∈ eLo L) : q ∈ eReg L :=
  (eK_mem L hw).2.2.2.2.1 q (List.mem_of_mem_take h)
theorem bank_take (L : CuccaroStreamedSquareWideLayout) (j : Nat) (q : Wire) (h : q ∈ (eBank L).take j) :
    q ∈ eBank L := List.mem_of_mem_take h
theorem mU_hi (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q ∈ mU L) : q ∈ hiReg L := List.mem_of_mem_drop h
theorem eZ0_eZ (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : eZ0 L ∈ eZ L := by
  obtain ⟨_, ⟨z1, e2⟩, _⟩ := eShape L hw
  rw [e2]; simp

theorem eAddLo_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : wires (eAddLo L) ⊆ oldE L := by
  have lx : (mU L ++ [eZ0 L]).length = (eLo L ++ [eU L]).length := by simp [mU_length L hw, eLo_length L hw]
  have lk : ((eBank L).take 32).length + 1 = (eLo L ++ [eU L]).length := by
    simp [eBank_take_length L hw 32 (by omega), eLo_length L hw]
  intro q hq
  rw [eAddLo, addInPlace_wires _ _ _ _ lx lk] at hq
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq
  apply oldE_mem L hw q
  rcases hq with h|((h|h)|(h|h))|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (mU_hi L q h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h ▸ eZ0_eZ L hw)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (eLo_eReg L hw q h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h ▸ (eK_mem L hw).2.1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (bank_take L 32 q h)))))

theorem kapClr_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : wires (kapClr L) ⊆ oldE L := by
  have lx : (eLo L).length = (mU L).length := by rw [eLo_length L hw, mU_length L hw]
  have lk : ((eBank L).take 32).length = (mU L).length := by rw [eBank_take_length L hw 32 (by omega), mU_length L hw]
  intro q hq
  rw [kapClr, (compareLt_wires none _ _ _ _ _ lx lk).1] at hq
  simp only [Option.toList, List.nil_append, List.mem_toFinset, List.mem_cons, List.mem_append] at hq
  apply oldE_mem L hw q
  rcases hq with h|h|(h|h)|h
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h ▸ (eK_mem L hw).2.1))))
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl (eLo_eReg L hw q h))))
  · exact Or.inr (Or.inl (mU_hi L q h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (bank_take L 32 q h)))))

theorem eSubLo_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : wires (eSubLo L) ⊆ oldE L := by
  have lx : (mU L).length = (eLo L).length := by rw [eLo_length L hw, mU_length L hw]
  have lk : ((eBank L).take 31).length + 1 = (eLo L).length := by rw [eBank_take_length L hw 31 (by omega), eLo_length L hw]
  intro q hq
  rw [eSubLo, subInPlace_wires _ _ _ _ lx lk] at hq
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hq
  apply oldE_mem L hw q
  rcases hq with h|(h|h)|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (mU_hi L q h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (eLo_eReg L hw q h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (bank_take L 31 q h)))))

theorem kw_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : wires (kw L) ⊆ oldE L := by
  intro q hq
  simp only [kw, wires, Instr.wires, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    Finset.mem_insert, Finset.mem_singleton, List.foldr_cons, List.foldr_nil, Finset.union_empty, Finset.mem_union] at hq
  apply oldE_mem L hw q
  have w1 : w192 L ∈ L.core.work.drop 128 := List.mem_of_mem_drop (w192_tail L hw)
  rcases hq with h|h
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h ▸ (eK_mem L hw).2.1))))
  · exact Or.inr (Or.inr (Or.inl (h ▸ w1)))

theorem wFwdK_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : wires (wFwdK L) ⊆ oldE L := by
  intro q hq
  rcases WinArith.tFwdK_mem (mLens L hw) (eU L) q hq with h|h
  · exact mem_oldE L hw q h
  · exact oldE_mem L hw q (Or.inr (Or.inr (Or.inr (Or.inl (h ▸ (eK_mem L hw).2.1)))))
theorem wInvK_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : wires (wInvK L) ⊆ oldE L := by
  intro q hq
  rcases WinArith.tInvK_mem (mLens L hw) (eU L) q hq with h|h
  · exact mem_oldE L hw q h
  · exact oldE_mem L hw q (Or.inr (Or.inr (Or.inr (Or.inl (h ▸ (eK_mem L hw).2.1)))))

theorem kw_counts (L : CuccaroStreamedSquareWideLayout) : toffoliCount (kw L) = 0 ∧ measurementCount (kw L) = 0 := by
  simp [kw, toffoliCount, measurementCount]
theorem kw_slots (L : CuccaroStreamedSquareWideLayout) : Challenge.gateSlots (kw L) = 1 := by
  simp [kw, Challenge.gateSlots, Challenge.instructionSlots]
theorem kw_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (kw L) := by
  have ne : eU L ≠ w192 L := fun e => (w192_facts L hw hn).2.2.2.2.2.1 e.symm
  intro i hi
  simp only [kw, List.mem_singleton] at hi
  subst hi
  exact ne

theorem eAddLo_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : Challenge.gateSlots (eAddLo L) ≤ 396 := by
  have a := Baselines.addInPlace_gateSlots_le (mU L ++ [eZ0 L]) (eLo L ++ [eU L]) ((eBank L).take 32) L.core.cin
  simp only [List.length_append, mU_length L hw, List.length_singleton] at a
  exact a
theorem kapClr_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : Challenge.gateSlots (kapClr L) ≤ 388 := by
  have a := Baselines.compareLt_gateSlots_le none (eLo L) (mU L) ((eBank L).take 32) L.core.cin (eU L)
  rw [eLo_length L hw, mU_length L hw] at a
  exact a
theorem eSubLo_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : Challenge.gateSlots (eSubLo L) ≤ 448 := by
  have a := Baselines.subInPlace_gateSlots_le (mU L) (eLo L) ((eBank L).take 31) L.core.cin
  rw [eLo_length L hw, mU_length L hw] at a
  exact a

theorem eAddLo_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (eAddLo L) := by
  apply addInPlace_physical
  have nd := lo_nodup L hw hn 32 (by omega)
  apply List.nodup_iff_count_le_one.mpr; intro q
  have c := List.nodup_iff_count_le_one.mp nd q
  simp only [List.cons_append, List.count_cons, List.count_append, List.count_nil] at c ⊢
  omega
theorem kapClr_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (kapClr L) := by
  apply compareLt_physical
  · have nd := lo_nodup L hw hn 32 (by omega)
    apply List.nodup_iff_count_le_one.mpr; intro q
    have c := List.nodup_iff_count_le_one.mp nd q
    simp only [List.cons_append, List.count_cons, List.count_append, List.count_nil] at c ⊢
    omega
  · intro c hc; simp at hc
theorem eSubLo_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (eSubLo L) := by
  apply subInPlace_physical
  have nd := lo_nodup L hw hn 31 (by omega)
  apply List.nodup_iff_count_le_one.mpr; intro q
  have c := List.nodup_iff_count_le_one.mp nd q
  simp only [List.cons_append, List.count_cons, List.count_append, List.count_nil] at c ⊢
  omega

end ECDSAAdd.Entrant.ControlLoan1589BFFold

end


section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.KnownSecondCarryDevelop
open Arithmetic

def head (expected : Bool) (a b c : Wire) : Program :=
  [.CX a c,.CX b c]++(if expected then [.X c] else [])

theorem head_correct (expected : Bool) (a b c : Wire) (hb:b≠c)
    (s : State) (m : List Bool) :
    run (head expected a b c) m s=
      ⟨s.phase,writeBit s.basis c (((s.basis c ^^ s.basis a) ^^ s.basis b) ^^ expected)⟩ := by
  cases expected <;> simp only [head,Bool.false_eq_true,if_false,if_true,List.cons_append,List.nil_append,run]
  all_goals
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq:q=c <;> simp [writeBit,Function.update,hq,hb]

theorem head_eq_majority (expected : Bool) (a b a' b' cin c : Wire)
    (hn:[a,b,cin,c].Nodup) (hb:b'≠c)
    (s : State) (m : List Bool)
    (ready:sumBit (s.basis a') (s.basis b') (carryBit (s.basis a) (s.basis b) (s.basis cin))=expected) :
    run (head expected a' b' c) m s=run (majority a b cin c) m s := by
  rw [head_correct expected a' b' c hb,majority_correct a b cin c hn]
  have solve (x y z k d : Bool) (h:sumBit x y k=d) : (((z ^^ x) ^^ y) ^^ d)=(z ^^ k) := by
    cases x <;> cases y <;> cases z <;> cases k <;> cases d <;> simp_all [sumBit]
  rw [solve _ _ _ _ _ ready]

theorem head_counts (expected : Bool) (a b c : Wire) :
    toffoliCount (head expected a b c)=0 ∧ measurementCount (head expected a b c)=0 := by
  cases expected <;> simp [head,toffoliCount,measurementCount]

theorem head_physical (expected : Bool) (a b c : Wire) (ha:a≠c) (hb:b≠c) :
    GatePhysical (head expected a b c) := by
  cases expected <;> simp [head,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ha,hb]

#print axioms head_eq_majority
#print axioms head_physical
end ECDSAAdd.Entrant.KnownSecondCarryDevelop
end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.KnownSecondAddDevelop
open Arithmetic Instr KnownSecondCarryDevelop

def add (expected : Bool) (x y cs : List Wire) (cin : Wire) : Program :=
  match x,y,cs with
  | a::a'::as,b::b'::bs,c::cs =>
    head expected a' b' c ++ Arithmetic.addInPlace (a'::as) (b'::bs) cs c ++
      eraseCarry a b cin c ++ [CX a b,CX cin b]
  | _,_,_ => Arithmetic.addInPlace x y cs cin

theorem add_eq (expected : Bool) (a a' b b' c cin : Wire)
    (as bs cs : List Wire) (hn:[a,b,cin,c].Nodup) (hb:b'≠c)
    (s : State) (m : List Bool)
    (ready:sumBit (s.basis a') (s.basis b') (carryBit (s.basis a) (s.basis b) (s.basis cin))=expected) :
    run (add expected (a::a'::as) (b::b'::bs) (c::cs) cin) m s =
      run (Arithmetic.addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) m s := by
  simp only [add,Arithmetic.addInPlace,List.append_assoc]
  rw [run_append (head expected a' b' c),run_append (majority a b cin c)]
  have hm : measurementCount (head expected a' b' c)=measurementCount (majority a b cin c) := by
    simp [head_counts,majority,measurementCount]
  rw [hm,head_eq_majority expected a b a' b' cin c hn hb _ _ ready]

theorem add_counts (expected : Bool) (a a' b b' c cin : Wire)
    (as bs cs : List Wire) :
    toffoliCount (add expected (a::a'::as) (b::b'::bs) (c::cs) cin)+1 =
      toffoliCount (Arithmetic.addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) ∧
    measurementCount (add expected (a::a'::as) (b::b'::bs) (c::cs) cin) =
      measurementCount (Arithmetic.addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  simp only [add,Arithmetic.addInPlace,toffoliCount_append,measurementCount_append]
  have h:=head_counts expected a' b' c
  simp [h,majority,toffoliCount,measurementCount]
  omega

#print axioms add_eq
#print axioms add_counts
end ECDSAAdd.Entrant.KnownSecondAddDevelop
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.KnownSecondValueDevelop
open Arithmetic

theorem second (a a' b b' : Wire) (as bs : List Wire) (s : BasisState) :
    (sumBit (s a') (s b') (carryBit (s a) (s b) false)).toNat =
      (regValue (a::a'::as) s+regValue (b::b'::bs) s)/2%2 := by
  cases ha:s a <;> cases hb:s b <;> cases ha':s a' <;> cases hb':s b' <;>
    simp [regValue,ha,hb,ha',hb',sumBit,carryBit] <;> omega

theorem ready_true (a a' b b' cin : Wire) (as bs : List Wire) (s : BasisState)
    (hc:s cin=false)
    (h:(regValue (a::a'::as) s+regValue (b::b'::bs) s)/2%2=1) :
    sumBit (s a') (s b') (carryBit (s a) (s b) (s cin))=true := by
  rw [hc]
  have e := second a a' b b' as bs s
  rw [h] at e
  cases he:sumBit (s a') (s b') (carryBit (s a) (s b) false) <;> simp_all

#print axioms ready_true
end ECDSAAdd.Entrant.KnownSecondValueDevelop
end

section
namespace ECDSAAdd.Entrant.KnownSecondAddDevelop
open Arithmetic Instr KnownSecondCarryDevelop
set_option autoImplicit false

theorem add_physical (expected : Bool) (a a' b b' c cin : Wire)
    (as bs cs : List Wire) (ha:a'≠c) (hb:b'≠c)
    (old:GatePhysical (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin)) :
    GatePhysical (add expected (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  simp only [addInPlace,gatePhysical_append] at old
  simp only [add,gatePhysical_append]
  exact ⟨⟨⟨head_physical expected a' b' c ha hb,old.1.1.2⟩,old.1.2⟩,old.2⟩

theorem add_slots (expected : Bool) (a a' b b' c cin : Wire)
    (as bs cs : List Wire) :
    Challenge.gateSlots (add expected (a::a'::as) (b::b'::bs) (c::cs) cin) ≤
      Challenge.gateSlots (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  cases expected <;> simp [add,addInPlace,head,majority,Challenge.gateSlots,Challenge.instructionSlots] <;> omega

#print axioms add_physical
#print axioms add_slots
end ECDSAAdd.Entrant.KnownSecondAddDevelop
end

section
namespace ECDSAAdd.Entrant.KnownSecondAddDevelop
open Arithmetic Instr KnownSecondCarryDevelop
set_option autoImplicit false

theorem add_support (expected : Bool) (a a' b b' c cin : Wire)
    (as bs cs : List Wire) (hx:(a::a'::as).length=(b::b'::bs).length)
    (hc:(c::cs).length+1=(b::b'::bs).length) :
    wires (add expected (a::a'::as) (b::b'::bs) (c::cs) cin) ⊆
      wires (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  have tail:=addInPlace_wires (a'::as) (b'::bs) cs c (by simpa using hx) (by simpa using hc)
  have hs:wires (head expected a' b' c)⊆wires (addInPlace (a'::as) (b'::bs) cs c) := by
    rw [tail]
    cases expected <;> intro q hq <;>
      simp [head,wires,Instr.wires] at hq ⊢ <;> tauto
  simp only [add,addInPlace,wires_append]
  intro q hq
  simp only [Finset.mem_union] at hq ⊢
  rcases hq with ((h|h)|h)|h
  · exact Or.inl (Or.inl (Or.inr (hs h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

#print axioms add_support
end ECDSAAdd.Entrant.KnownSecondAddDevelop
end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.KnownSecondSubDevelop
open Arithmetic Instr

def sub (x y cs : List Wire) (cin : Wire) : Program :=
  notRegister y ++ KnownSecondAddDevelop.add true x y cs cin ++ notRegister y

theorem complement32 (a u : Nat) (hbit:a/2%2=0) :
    (u+(2^32-1-(a+u)%2^32))/2%2=1 := by
  have h:(a+u)%2^32<2^32 := Nat.mod_lt _ (by decide)
  omega

theorem square_second32 (M : Nat) : (M^2%2^32)/2%2=0 := by
  have h:M%4=0 ∨ M%4=1 ∨ M%4=2 ∨ M%4=3 := by omega
  have h4:M^2%4=0 ∨ M^2%4=1 := by
    rcases h with h|h|h|h <;> simp [Nat.pow_mod,h]
  have mod4:(M^2%2^32)%4=M^2%4 := Nat.mod_mod_of_dvd _ (by decide)
  rcases h4 with h4|h4 <;> omega

theorem sub_eq (a a' b b' c cin : Wire) (as bs cs : List Wire)
    (hn:(cin::((a::a'::as)++(b::b'::bs)++(c::cs))).Nodup)
    (hl:(b::b'::bs).length=32) (v u : Nat) (hbit:v/2%2=0)
    (s : State) (m : List Bool) (hc:s.basis cin=false)
    (hx:regValue (a::a'::as) s.basis=u)
    (hy:regValue (b::b'::bs) s.basis=(v+u)%2^32) :
    run (sub (a::a'::as) (b::b'::bs) (c::cs) cin) m s =
      run (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) m s := by
  have cnt:=fun q=>List.nodup_iff_count_le_one.mp hn q
  have yn:(b::b'::bs).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have h:=cnt q
    simp only [List.count_cons,List.count_append,beq_iff_eq] at h ⊢
    omega
  have off (q : Wire) (hq:q=cin ∨ q∈a::a'::as ∨ q=c) : q∉b::b'::bs := by
    intro hy
    have h:=cnt q
    have pos:=List.count_pos_iff.mpr hy
    simp only [List.count_cons,beq_iff_eq] at pos
    simp only [List.count_cons,List.count_append,beq_iff_eq] at h
    rcases hq with rfl|hx|rfl
    · simp only [if_true] at h pos
      omega
    · have x:=List.count_pos_iff.mpr hx
      simp only [List.count_cons,beq_iff_eq] at x
      omega
    · simp only [if_true] at h pos
      omega
  have small:[a,b,cin,c].Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have h:=cnt q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have bc:b'≠c := by intro he;apply off c (Or.inr (Or.inr rfl));simp [←he]
  simp only [sub,subInPlace,List.append_assoc]
  rw [run_append (notRegister (b::b'::bs)),run_append (notRegister (b::b'::bs))]
  rw [run_append (KnownSecondAddDevelop.add true (a::a'::as) (b::b'::bs) (c::cs) cin),
    run_append (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin)]
  have cm:measurementCount (KnownSecondAddDevelop.add true (a::a'::as) (b::b'::bs) (c::cs) cin)=
      measurementCount (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) :=
    (KnownSecondAddDevelop.add_counts true a a' b b' c cin as bs cs).2
  rw [cm]
  apply congrArg (fun st=>run (notRegister (b::b'::bs)) _ st)
  apply KnownSecondAddDevelop.add_eq true a a' b b' c cin as bs cs small bc
  apply KnownSecondValueDevelop.ready_true a a' b b' cin as bs
  · rw [notRegister_correct _ yn]
    simpa [off cin (Or.inl rfl)] using hc
  · rw [notRegister_correct _ yn]
    have xv:regValue (a::a'::as) (fun w=>if w∈b::b'::bs then !s.basis w else s.basis w)=u := by
      rw [←hx]
      apply regValue_congr
      intro q hq
      simp [off q (Or.inr (Or.inl hq))]
    have yv:regValue (b::b'::bs) (fun w=>if w∈b::b'::bs then !s.basis w else s.basis w)=2^32-1-(v+u)%2^32 := by
      rw [regValue_congr (b::b'::bs) _ (fun w=> !s.basis w) (by intro q hq;simp [hq]),regValue_complement,hl,hy]
    rw [xv,yv]
    exact complement32 v u hbit

#print axioms sub_eq
#print axioms square_second32
end ECDSAAdd.Entrant.KnownSecondSubDevelop
end

section
namespace ECDSAAdd.Entrant.KnownSecondSubDevelop
open Arithmetic Instr
set_option autoImplicit false

theorem sub_counts (a a' b b' c cin : Wire) (as bs cs : List Wire) :
    toffoliCount (sub (a::a'::as) (b::b'::bs) (c::cs) cin)+1 =
      toffoliCount (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) ∧
    measurementCount (sub (a::a'::as) (b::b'::bs) (c::cs) cin) =
      measurementCount (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  have h:=KnownSecondAddDevelop.add_counts true a a' b b' c cin as bs cs
  simp only [sub,subInPlace,toffoliCount_append,measurementCount_append,
    (notRegister_counts _).1,(notRegister_counts _).2,Nat.zero_add,Nat.add_zero]
  exact h

theorem sub_physical (a a' b b' c cin : Wire) (as bs cs : List Wire)
    (ha:a'≠c) (hb:b'≠c)
    (old:GatePhysical (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin)) :
    GatePhysical (sub (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  simp only [subInPlace,gatePhysical_append] at old
  simp only [sub,gatePhysical_append]
  exact ⟨⟨old.1.1,KnownSecondAddDevelop.add_physical true a a' b b' c cin as bs cs ha hb old.1.2⟩,old.2⟩

theorem sub_support (a a' b b' c cin : Wire) (as bs cs : List Wire)
    (hx:(a::a'::as).length=(b::b'::bs).length)
    (hc:(c::cs).length+1=(b::b'::bs).length) :
    wires (sub (a::a'::as) (b::b'::bs) (c::cs) cin) ⊆
      wires (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  have h:=KnownSecondAddDevelop.add_support true a a' b b' c cin as bs cs hx hc
  simp only [sub,subInPlace,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)

theorem sub_slots (a a' b b' c cin : Wire) (as bs cs : List Wire) :
    Challenge.gateSlots (sub (a::a'::as) (b::b'::bs) (c::cs) cin) ≤
      Challenge.gateSlots (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  have h:=KnownSecondAddDevelop.add_slots true a a' b b' c cin as bs cs
  simp only [sub,subInPlace,Challenge.gateSlots_append]
  omega

#print axioms sub_counts
#print axioms sub_physical
#print axioms sub_support
#print axioms sub_slots
end ECDSAAdd.Entrant.KnownSecondSubDevelop
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.KnownSecondSubDevelop
open Arithmetic

theorem shape (x : List Wire) (h:2≤x.length) : ∃a b xs,x=a::b::xs := by
  cases x with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs => exact ⟨a,b,xs,rfl⟩

theorem lists_eq (x y cs : List Wire) (cin : Wire)
    (hn:(cin::x++y++cs).Nodup) (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31)
    (v u : Nat) (hbit:v/2%2=0) (s : State) (m : List Bool) (hc:s.basis cin=false)
    (hx:regValue x s.basis=u) (hy:regValue y s.basis=(v+u)%2^32) :
    run (sub x y cs cin) m s=run (subInPlace x y cs cin) m s := by
  obtain ⟨a,a',as,rfl⟩:=shape x (by omega)
  obtain ⟨b,b',bs,rfl⟩:=shape y (by omega)
  cases cs with
  | nil => simp at lc
  | cons c cs => exact sub_eq a a' b b' c cin as bs cs hn ly v u hbit s m hc hx hy

theorem lists_resources (x y cs : List Wire) (cin : Wire)
    (hn:(cin::x++y++cs).Nodup) (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31)
    (old:GatePhysical (subInPlace x y cs cin)) :
    toffoliCount (sub x y cs cin)+1=toffoliCount (subInPlace x y cs cin) ∧
    measurementCount (sub x y cs cin)=measurementCount (subInPlace x y cs cin) ∧
    GatePhysical (sub x y cs cin) ∧ wires (sub x y cs cin)⊆wires (subInPlace x y cs cin) ∧
    Challenge.gateSlots (sub x y cs cin)≤Challenge.gateSlots (subInPlace x y cs cin) := by
  obtain ⟨a,a',as,rfl⟩:=shape x (by omega)
  obtain ⟨b,b',bs,rfl⟩:=shape y (by omega)
  cases cs with
  | nil => simp at lc
  | cons c cs =>
    have cnt:=fun q=>List.nodup_iff_count_le_one.mp hn q
    have ac:a'≠c := by
      intro he
      have h:=cnt c
      simp only [List.count_cons,List.count_append,beq_iff_eq] at h
      simp only [he,if_true] at h
      omega
    have bc:b'≠c := by
      intro he
      have h:=cnt c
      simp only [List.count_cons,List.count_append,beq_iff_eq] at h
      simp only [he,if_true] at h
      omega
    exact ⟨(sub_counts a a' b b' c cin as bs cs).1,(sub_counts a a' b b' c cin as bs cs).2,
      sub_physical a a' b b' c cin as bs cs ac bc old,
      sub_support a a' b b' c cin as bs cs (by omega) (by simp_all),
      sub_slots a a' b b' c cin as bs cs⟩

#print axioms lists_eq
#print axioms lists_resources
end ECDSAAdd.Entrant.KnownSecondSubDevelop
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.KnownSecondSubDevelop
open Arithmetic

theorem lists_static (x y cs : List Wire) (cin : Wire)
    (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31) :
    toffoliCount (sub x y cs cin)+1=toffoliCount (subInPlace x y cs cin) ∧
    measurementCount (sub x y cs cin)=measurementCount (subInPlace x y cs cin) ∧
    wires (sub x y cs cin)⊆wires (subInPlace x y cs cin) ∧
    Challenge.gateSlots (sub x y cs cin)≤Challenge.gateSlots (subInPlace x y cs cin) := by
  obtain ⟨a,a',as,rfl⟩:=shape x (by omega)
  obtain ⟨b,b',bs,rfl⟩:=shape y (by omega)
  cases cs with
  | nil => simp at lc
  | cons c cs =>
    exact ⟨(sub_counts a a' b b' c cin as bs cs).1,(sub_counts a a' b b' c cin as bs cs).2,
      sub_support a a' b b' c cin as bs cs (by omega) (by simp_all),
      sub_slots a a' b b' c cin as bs cs⟩

#print axioms lists_static
end ECDSAAdd.Entrant.KnownSecondSubDevelop
end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def eSubLoSq (L : CuccaroStreamedSquareWideLayout) : Program :=
  KnownSecondSubDevelop.sub (mU L) (eLo L) ((eBank L).take 31) L.core.cin

theorem eSubLoSq_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O A H l : Nat) (hH : H < 2^96) (hl : l < 2^32)
    (hbit:((l+2^32-regValue (hiReg L) base/2^96)%2^32)/2%2=0) :
    Triple (BState L base O (2^32*H + l) A) (eSubLoSq L)
      (BState L base O (2^32*H + (l + 2^32 - regValue (hiReg L) base / 2^96) % 2^32) A) := by
  intro s m h
  obtain ⟨_, _, f3, _, f5⟩ := eK_facts L hw hn base hc O _ A s.basis h
  let u := regValue (hiReg L) base / 2^96
  have hu : regValue (mU L) s.basis = u := by rw [hi96 L hw, f5]
  have hv := eReg_split L hw s.basis
  rw [h.2.1] at hv
  have hl0 := eLo_lt L hw s.basis
  have hm := eMid_lt L hw s.basis
  have key : regValue (eLo L) s.basis = l ∧ regValue (eMid L) s.basis = H ∧
      s.basis (eU L) = false ∧ s.basis (eV L) = false := by
    cases e1 : s.basis (eU L) <;> cases e2 : s.basis (eV L) <;>
      simp only [e1, e2, Bool.false_eq_true, if_false, if_true] at hv <;>
      first | omega | (exact ⟨by omega, by omega, rfl, rfl⟩)
  obtain ⟨k1, k2, k3, k4⟩ := key
  have nd := lo_nodup L hw hn 31 (by omega)
  have nd2 : (L.core.cin :: (mU L ++ eLo L ++ (eBank L).take 31)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := List.nodup_iff_count_le_one.mp nd q
    simp only [List.count_cons, List.count_append] at c ⊢
    omega
  have hu32:u<2^32 := by
    rw [←hu]
    have z:=regValue_lt (mU L) s.basis
    rwa [mU_length L hw] at z
  have restore:(((l+2^32-u)%2^32)+u)%2^32=l := by omega
  have eq:=KnownSecondSubDevelop.lists_eq (mU L) (eLo L) ((eBank L).take 31) L.core.cin nd2
    (mU_length L hw) (eLo_length L hw) (eBank_take_length L hw 31 (by omega))
    ((l+2^32-u)%2^32) u hbit s m f3 hu (by rw [restore];exact k1)
  change run (eSubLoSq L) m s=run (eSubLo L) m s at eq
  rw [eq]
  exact eSubLo_step L hw hn base hc O A H l hH hl s m h

#print axioms eSubLoSq_step
end ECDSAAdd.Entrant.ControlLoan1589BFFold
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem eSubLoSq_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    toffoliCount (eSubLoSq L)=30 ∧ measurementCount (eSubLoSq L)=31 ∧
    GatePhysical (eSubLoSq L) ∧ wires (eSubLoSq L)⊆oldE L ∧
    Challenge.gateSlots (eSubLoSq L)≤448 := by
  have nd := lo_nodup L hw hn 31 (by omega)
  have nd2 : (L.core.cin :: (mU L ++ eLo L ++ (eBank L).take 31)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := List.nodup_iff_count_le_one.mp nd q
    simp only [List.count_cons,List.count_append] at c ⊢
    omega
  have rr:=KnownSecondSubDevelop.lists_resources (mU L) (eLo L) ((eBank L).take 31) L.core.cin nd2
    (mU_length L hw) (eLo_length L hw) (eBank_take_length L hw 31 (by omega)) (eSubLo_physical L hw hn)
  change toffoliCount (eSubLoSq L)+1=toffoliCount (eSubLo L) ∧
    measurementCount (eSubLoSq L)=measurementCount (eSubLo L) ∧ GatePhysical (eSubLoSq L) ∧
    wires (eSubLoSq L)⊆wires (eSubLo L) ∧ Challenge.gateSlots (eSubLoSq L)≤Challenge.gateSlots (eSubLo L) at rr
  have counts:=lo_counts L hw
  exact ⟨by omega,by omega,rr.2.2.1,rr.2.2.2.1.trans (eSubLo_oldE L hw),
    rr.2.2.2.2.trans (eSubLo_slots L hw)⟩

#print axioms eSubLoSq_resources
end ECDSAAdd.Entrant.ControlLoan1589BFFold
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem eSubLoSq_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (eSubLoSq L)=30 ∧ measurementCount (eSubLoSq L)=31 ∧
    wires (eSubLoSq L)⊆oldE L ∧ Challenge.gateSlots (eSubLoSq L)≤448 := by
  have rr:=KnownSecondSubDevelop.lists_static (mU L) (eLo L) ((eBank L).take 31) L.core.cin
    (mU_length L hw) (eLo_length L hw) (eBank_take_length L hw 31 (by omega))
  change toffoliCount (eSubLoSq L)+1=toffoliCount (eSubLo L) ∧
    measurementCount (eSubLoSq L)=measurementCount (eSubLo L) ∧
    wires (eSubLoSq L)⊆wires (eSubLo L) ∧ Challenge.gateSlots (eSubLoSq L)≤Challenge.gateSlots (eSubLo L) at rr
  have counts:=lo_counts L hw
  exact ⟨by omega,by omega,rr.2.2.1.trans (eSubLo_oldE L hw),
    rr.2.2.2.trans (eSubLo_slots L hw)⟩

theorem eSubLoSq_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (eSubLoSq L) := (eSubLoSq_resources L hw hn).2.2.1

theorem eSubLoSq_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    wires (eSubLoSq L)⊆oldE L := (eSubLoSq_static L hw).2.2.1

theorem eSubLoSq_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (eSubLoSq L)≤448 := (eSubLoSq_static L hw).2.2.2

#print axioms eSubLoSq_static
#print axioms eSubLoSq_physical
end ECDSAAdd.Entrant.ControlLoan1589BFFold
end
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-- The `W` fold with the low-window `+u` on `e`: `kap` rides on `eU` through the fold and is cleared after it. -/
def wFoldTq (L : CuccaroStreamedSquareWideLayout) : Program :=
  eAddLo L++(wBuild L++((wFwdK L++(wCoreK L++wInvK L))++(wUnbuildKnown L++(kapClr L++eSubK L))))

/-- The restore: `+b1`, then the low-window `-u`.
No rebuild of `W`; 721 no-op measurements keep the measurement count of the B body. -/
def wRestoreT (L : CuccaroStreamedSquareWideLayout) : Program :=
  eAddB L++(eSubLoSq L++padM L 721)

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


set_option maxHeartbeats 2000000 in
def aFold8Tq (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  wBuild L++(maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK++(qprogTq L.measuredCore SquareReduction.p++
    (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK++wUnbuildKnown L)))


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
  have hun : Triple (SquareFrame (accReg L) base2 A) (wUnbuildKnown L) (SquareFrame (accReg L) base2 0) := by
    have h := SourceAddFourDevelop.unbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) base2 hz2 hb2 hi2
    rw [hhi2] at h
    exact h
  have eo := hun v1 (m3.drop mc) frame2
  refine ⟨eo.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have e : regValue L.core.out (run (wUnbuildKnown L) (m3.drop mc) v1).basis=
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
  exact ⟨a1,a2,wb.1,mc,full.1.2,mc,(wUnbuildKnown_wires L hw).trans wb.2⟩



theorem eItem_priceTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : accPriceQTq (eItem L)=1554 := by
  have hl := eReg_length L hw
  norm_num [eItem,accPriceQTq,earlyHTerms,Acc.earlyTerm,Acc.sbuildT,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,
    Acc.buildT,hl]


theorem aAcc_priceTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : accPriceQTq (aAcc L)=1554 := by
  norm_num [aAcc,accPriceQTq,earlyHTerms,Acc.earlyTerm,Acc.sbuildT,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,
    Acc.buildT,hw.core.product]


theorem bBody_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (bBodyTq L c)=4803 ∧ measurementCount (bBodyTq L c)=5924 := by
  have q1 := measuredFoldQ_countsTq L hw (negP L)
  have q2 := measuredFoldQ_countsTq L hw (rot128F L)
  have bc := CodexNarrowTail.build8_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_okLen L hw)
  rw [CodexNarrowTail.build8_eq] at bc
  have wb : toffoliCount (wBuild L)=387 ∧ measurementCount (wBuild L)=388 := bc.1
  have wu := wUnbuildKnown_counts L hw
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
  rw [SourceFourPrefix130Develop.eItem_gain L hw] at k4
  have k4m := (Q4.accFoldQ4KTq_rel L hw (eItem L) st.2.1).2.1
  have ac : toffoliCount (accFoldQ4KTq L (eItem L))=1388 ∧ measurementCount (accFoldQ4KTq L (eItem L))=1555 :=
    ⟨by omega,by omega⟩
  have s1k : toffoliCount (eSubK L)=128 ∧ measurementCount (eSubK L)=129 := by
    have k := eSubK_counts L hw; exact ⟨by omega,by omega⟩
  have a1b : toffoliCount (eAddB L)=128 ∧ measurementCount (eAddB L)=129 := by
    have k := eAddB_counts L hw; exact ⟨by omega,by omega⟩
  have fw : toffoliCount (wFwdK L)=76 ∧ measurementCount (wFwdK L)=109 := WinArith.tFwdK_counts (mLens L hw) (eU L)
  have iv : toffoliCount (wInvK L)=71 ∧ measurementCount (wInvK L)=109 := WinArith.tInvK_counts (mLens L hw) (eU L)
  have kc := kw_counts L
  have lc := lo_counts L hw
  have sq := eSubLoSq_static L hw
  have pd := padM_counts L 721
  simp only [bBodyTq,wFoldTq,wCoreK,eFoldTq,wRestoreT,toffoliCount_append,measurementCount_append,q1.1,q1.2,q2.1,q2.2,
    wb.1,wb.2,wu.1,wu.2,wc.1,wc.2,s1k.1,s1k.2,a1b.1,a1b.2,fl.1,fl.2,ac.1,ac.2,fw.1,fw.2,iv.1,iv.2,kc.1,kc.2,
    lc.1,lc.2.1,lc.2.2.1,lc.2.2.2.1,sq.1,sq.2.1,pd.1,pd.2]
  exact ⟨trivial,trivial⟩

theorem aBody_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (aBodyTq L c)=2918 ∧ measurementCount (aBodyTq L c)=3077 := by
  have q1 := measuredFoldQ_countsTq L hw (negP L)
  have q2 := measuredFoldQ_countsTq L hw (rot128F L)
  have bc := CodexNarrowTail.build8_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_okLen L hw)
  rw [CodexNarrowTail.build8_eq] at bc
  have wb : toffoliCount (wBuild L)=387 ∧ measurementCount (wBuild L)=388 := bc.1
  have wu := wUnbuildKnown_counts L hw
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
  have hct : c∉(eReg L).take 129 := fun hm => hcw (by
    have := eReg_product L c (List.mem_of_mem_take hm)
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this])
  have fl : GatePhysical (eFlip L c) := maskedConstant_physical c ((eReg L).take 129) (2^129-1) hct
  have st := eItem_static L hw
  have ac := Q4.accFoldQ4KTq_physical L hw nd (eItem L) st.1 st.2.1 st.2.2.1 st.2.2.2
  have g := mGeo L hw nd
  have heZ : eU L ∉ mZ L := fun hz => (eU_away L hw nd).1 (mZ_pad L _ hz)
  simp only [bBodyTq,wFoldTq,wCoreK,eFoldTq,wRestoreT,gatePhysical_append]
  exact ⟨p1,p2,⟨eAddLo_physical L hw nd,wb.1,⟨WinArith.tFwdK_physical g (eU L) heZ,⟨kw_physical L hw nd,wc,
    kw_physical L hw nd⟩,WinArith.tInvK_physical g (eU L) heZ⟩,wUnbuildKnown_physical L hw nd,kapClr_physical L hw nd,eSubK_physical L hw nd⟩,
    ⟨fl,ac,fl⟩,⟨eAddB_physical L hw nd,eSubLoSq_physical L hw nd,padM_physical L 721⟩⟩

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
  exact ⟨p1,p2,wb.1,mc,full.1.2,mc,wUnbuildKnown_physical L hw nd⟩


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
  have wun := wUnbuildKnown_slots L hw
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
  have known:=SourceFourPrefix130Develop.fillOut_resources L hw a
  unfold accFoldQ4KTq CodexCKAccTail.accFoldQ4Tail
  exact Le.app (Le.app (Le.rfl' _)
    (qprog4_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide))) ⟨known.2.2.1,known.2.2.2⟩

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
  have known:=SourceFourPrefix130Develop.fillOut_resources L hw a
  unfold OwnDiagAll12Square.accFoldQFKTq CodexCKAccTail.accFoldQFTail
  exact Le.app (Le.rfl' _) (Le.app (Le.rfl' _) (Le.app
    (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)) (Le.app (Le.rfl' _) ⟨known.2.2.1,known.2.2.2⟩)))

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
set_option maxRecDepth 5000000 in
theorem bBody_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    QRel.Le (bBodyTq L c) (bBody L c) := by
  unfold bBodyTq bBody
  refine QRel.Le.app (QRel.measuredFoldQ_le L hw _) (QRel.Le.app (QRel.measuredFoldQ_le L hw _) ⟨?_, ?_⟩)
  · have wc := (QRel.qprog_le (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)).1
    have ef := (QRel.eFold_le L hw c).1
    have sk := eSubK_wires L hw
    have ab := eAddB_wires L hw
    have ml {A B : Program} {q : Wire} (h : q ∈ wires A) : q ∈ wires (A ++ B) := by
      rw [wires_append]; exact Finset.mem_union_left _ h
    have mr {A B : Program} {q : Wire} (h : q ∈ wires B) : q ∈ wires (A ++ B) := by
      rw [wires_append]; exact Finset.mem_union_right _ h
    have hOE {q : Wire} (h : q ∈ oldE L) : q ∈ wires (wFold L ++ (eFold L c ++ wRestore L)) := by
      rcases Finset.mem_union.mp h with h|h
      · exact ml (mr (mr (ml h)))
      · exact ml (mr (mr (mr (ml h))))
    intro q hq
    simp only [wFoldTq, wCoreK, wRestoreT, wires_append, Finset.mem_union] at hq
    rcases hq with (h | h | (h | (h | h | h) | h) | h | h | h) | h | h | h | h
    · exact hOE (eAddLo_oldE L hw h)
    · exact ml (ml h)
    · exact hOE (wFwdK_oldE L hw h)
    · exact hOE (kw_oldE L hw h)
    · exact ml (mr (ml (wc h)))
    · exact hOE (kw_oldE L hw h)
    · exact hOE (wInvK_oldE L hw h)
    · exact ml (mr (mr (mr (mr (wUnbuildKnown_wires L hw h)))))
    · exact hOE (kapClr_oldE L hw h)
    · exact ml (mr (mr (ml (sk h))))
    · exact mr (ml (ef h))
    · exact mr (mr (mr (mr (ml (ab h)))))
    · exact hOE (eSubLoSq_oldE L hw h)
    · exact hOE (padM_oldE L hw 721 h)
  · have wc := (QRel.qprog_le (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)).2
    have ef := (QRel.eFold_le L hw c).2
    have sk := eSubK_slots L hw
    have ab := eAddB_slots L hw
    have f1 := WinArith.tFwdK_slots (cin := L.core.cin) (mLens L hw) (eU L)
    have f2 := WinArith.tInvK_slots (cin := L.core.cin) (mLens L hw) (eU L)
    have f5 := padM_slots L 721
    have g1 := wBuild_slots_ge L hw
    have wun := wUnbuildKnown_slots L hw
    have g2 := wUnbuild_slots_ge L hw
    have known := wUnbuildKnown_slots L hw
    have k1 := kw_slots L
    have e1 := eAddLo_slots L hw
    have e2 := kapClr_slots L hw
    have e3 := eSubLoSq_slots L hw
    have l2 := eSrc_length L hw (whiSrc L) (Or.inr rfl)
    have wa := KnownTopAdd.addInPlace_slots_eq (whiSrc L) (eReg L) (eBank L) L.core.cin l2.1 l2.2
    rw [eReg_length L hw] at wa
    simp only [wFoldTq, wRestoreT, wCoreK, wFold, wRestore, wFwdK, wInvK, wCoreTq, wCore, eAdd,
      Challenge.gateSlots_append] at *
    omega

theorem aBody_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Le (ControlLoan1589BFFold.aBodyTq L c) (ControlLoan1589BFFold.aBody L c) := by
  unfold ControlLoan1589BFFold.aBodyTq ControlLoan1589BFFold.aBody ControlLoan1589BFFold.aFold8Tq
    ControlLoan1589BFFold.aFold8
  exact Le.app (measuredFoldQ_le L hw _) (Le.app (measuredFoldQ_le L hw _)
    (Le.app (Le.rfl' _) (Le.app (Le.rfl' _) (Le.app
      (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)) (Le.app (Le.rfl' _) ⟨ControlLoan1589BFFold.wUnbuildKnown_wires L hw,ControlLoan1589BFFold.wUnbuildKnown_slots L hw⟩)))))

/-- Counts and static refinement of the three square bodies, as used by the square layers. -/
theorem bodyC_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (OwnDiagAll12Square.bodyCTq L g)+2=toffoliCount (OwnDiagAll12Square.bodyC L g) ∧
    measurementCount (OwnDiagAll12Square.bodyCTq L g)+2=measurementCount (OwnDiagAll12Square.bodyC L g) ∧
    Le (OwnDiagAll12Square.bodyCTq L g) (OwnDiagAll12Square.bodyC L g) := by
  have a := OwnDiagAll12Square.bodyC_countsTq L hw g
  have b := OwnDiagAll12Square.bodyC_counts L hw g
  exact ⟨by omega,by omega,bodyC_le L hw g⟩

theorem bodyCK_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (OwnDiagAll12Square.bodyCKTq L g)+129=toffoliCount (CodexCKAccTail.bodyCTail L g) ∧
    measurementCount (OwnDiagAll12Square.bodyCKTq L g)+2=measurementCount (CodexCKAccTail.bodyCTail L g) ∧
    Le (OwnDiagAll12Square.bodyCKTq L g) (CodexCKAccTail.bodyCTail L g) := by
  have a := OwnDiagAll12Square.bodyCK_countsTq L hw g
  have b := CodexCKAccTail.bodyCTail_counts L hw g
  exact ⟨by omega,by omega,bodyCK_le L hw g⟩

theorem bBody_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (ControlLoan1589BFFold.bBodyTq L c)+1020=toffoliCount (ControlLoan1589BFFold.bBody L c) ∧
    measurementCount (ControlLoan1589BFFold.bBodyTq L c)+4=measurementCount (ControlLoan1589BFFold.bBody L c) ∧
    Le (ControlLoan1589BFFold.bBodyTq L c) (ControlLoan1589BFFold.bBody L c) := by
  have a := ControlLoan1589BFFold.bBody_countsTq L hw c
  have b := ControlLoan1589BFFold.bBody_counts L hw c
  exact ⟨by omega,by omega,bBody_le L hw c⟩

theorem aBody_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (ControlLoan1589BFFold.aBodyTq L c)+128=toffoliCount (ControlLoan1589BFFold.aBody L c) ∧
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

-- Consolidated source module: KnownFirstRow
section

namespace ECDSAAdd.Entrant.KnownFirstRow
open Arithmetic

/-- The receiver needs only a specification of the ordinary adder's output. -/
theorem receive_of_output (bits sums : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (hn : (cin::(ys++carry)).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hw : ∀q∈mappedWires sums,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false)
    (output : regValue ys (run (mappedAdd bits ys carry cin) [] s).basis =
      mappedValue sums s.basis) :
    run (KnownOutputAdder.program bits ys sums carry cin) m s =
      run (mappedAdd bits ys carry cin) m s := by
  have old := mappedAdd_correct bits ys carry cin hn ha hl hc s [] hclean
  have value : mappedValue sums s.basis =
      (mappedValue bits s.basis+regValue ys s.basis+(s.basis cin).toNat)%2^ys.length :=
    output.symm.trans old.2.2
  exact KnownOutputAdder.program_eq_mappedAdd bits sums ys carry cin hn ha hw hl hs hc s m
    hclean (KnownOutputAdder.ready_of_value bits sums ys (s.basis cin) s.basis hl hs value)

/-- After a signed-row clear's adder, its low bits equal the original row control,
while its top bit is true. The first carry is handled outside this receiver. -/
def expected (control : Wire) (n : Nat) : List MappedBit :=
  List.replicate (n-1) ⟨some control,false⟩ ++ [⟨none,true⟩]

theorem expected_length (control : Wire) (n : Nat) (hn : 0<n) :
    (expected control n).length=n := by simp [expected]; omega

theorem expected_sources (control : Wire) (n : Nat) :
    ∀q∈mappedWires (expected control n),q=control := by
  intro q hq
  simp only [mappedWires,expected,List.flatMap_append,List.mem_append,List.flatMap_replicate,
    List.flatMap_cons,List.flatMap_nil,List.not_mem_nil,or_false] at hq
  simp_all

theorem expected_value (control top : Wire) (low : List Wire) (s : BasisState)
    (hlo : ∀q∈low,s q=s control) (ht : s top=true) :
    mappedValue (List.replicate low.length (⟨some control,false⟩ : MappedBit) ++ [⟨none,true⟩]) s =
      regValue (low++[top]) s := by
  induction low with
  | nil => simp [mappedValue,regValue,MappedBit.value,ht]
  | cons q low ih =>
    simp only [List.length_cons,List.replicate_succ,List.cons_append,mappedValue,regValue]
    rw [ih (fun q hq => hlo q (by simp [hq]))]
    cases hs : s control <;> simp [MappedBit.value,hlo q (by simp),hs,regValue,ht]

theorem post_recovers_bits (control top : Wire) (low : List Wire) (s : State)
    (hn : (low++[top]).Nodup) (hc : control∉low++[top])
    (hz : regValue (low++[top])
      (run (notRegister (low++[top]) ++ xorWhenFalse control low) [] s).basis=0) :
    (∀q∈low,s.basis q=s.basis control) ∧ s.basis top=true := by
  have hl : low.Nodup := (List.nodup_append.mp hn).1
  have ht : top∉low := by
    have h := (List.nodup_append.mp hn).2.2
    exact fun hq => h top hq top (by simp) rfl
  have hcl : control∉low := fun hq => hc (by simp [hq])
  simp only [run_append,List.take_nil,List.drop_nil] at hz
  rw [notRegister_correct _ hn, xorWhenFalse_correct control low hl hcl] at hz
  have bits := (regValue_zero _ _).mp hz
  constructor
  · intro q hq
    have e := bits q (by simp [hq])
    simp only [xorFalseBasis,if_pos hq,show q∈low++[top] from by simp [hq],if_pos,
      if_neg hc] at e
    have eq : ∀a b : Bool, (!a ^^ !b)=false → a=b := by decide
    exact eq _ _ e
  · have e := bits top (by simp)
    simp only [xorFalseBasis,if_neg ht,show top∈low++[top] from by simp,if_pos] at e
    simpa using e

theorem post_recovers_expected (control top : Wire) (low : List Wire) (s : State)
    (hn : (low++[top]).Nodup) (hc : control∉low++[top])
    (hz : regValue (low++[top])
      (run (notRegister (low++[top]) ++ xorWhenFalse control low) [] s).basis=0) :
    mappedValue (List.replicate low.length (⟨some control,false⟩ : MappedBit) ++ [⟨none,true⟩]) s.basis =
      regValue (low++[top]) s.basis := by
  have h := post_recovers_bits control top low s hn hc hz
  exact expected_value control top low s.basis h.1 h.2


theorem read_add (xs ys carry : List Wire) (cin : Wire) :
    mappedAdd (mappedRead xs false) ys carry cin=addInPlace xs ys carry cin := by
  induction xs generalizing ys carry cin with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases xs with
    | nil => cases ys with
      | nil => rfl
      | cons y ys => cases ys <;> rfl
    | cons a' xs =>
      cases ys with
      | nil => rfl
      | cons b ys =>
        cases ys with
        | nil => rfl
        | cons b' ys =>
          cases carry with
          | nil => rfl
          | cons c cs =>
            simp only [mappedRead,List.map_cons,mappedAdd,mappedMajority,
              mappedEraseCarry,mappedSum,Bool.false_eq_true,if_false,addInPlace]
            rw [←ih (b'::ys) cs c]
            rfl


theorem read_sources (xs : List Wire) : mappedWires (mappedRead xs false)=xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [mappedRead,mappedWires] using congrArg (List.cons a) ih

def tailReceiver (xs ys carry : List Wire) (cin control : Wire) : Program :=
  KnownOutputAdder.program (mappedRead xs false) ys (expected control ys.length) carry cin

theorem tailReceiver_counts (xs ys carry : List Wire) (cin control : Wire)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    toffoliCount (tailReceiver xs ys carry cin control)=0 ∧
    measurementCount (tailReceiver xs ys carry cin control)=ys.length-1 := by
  exact KnownOutputAdder.program_counts _ _ _ _ _ (by simpa [mappedRead] using hl)
    (expected_length _ _ (by omega)) hc

theorem tailReceiver_eq (xs ys carry : List Wire) (cin control : Wire)
    (hn : (cin::ys++carry).Nodup)
    (ha : ∀q∈xs,q∉cin::ys++carry)
    (hw : control∉cin::ys++carry)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (clean : ∀q∈carry,s.basis q=false)
    (output : regValue ys (run (addInPlace xs ys carry cin) [] s).basis =
      mappedValue (expected control ys.length) s.basis) :
    run (tailReceiver xs ys carry cin control) m s = run (addInPlace xs ys carry cin) m s := by
  have source := read_sources xs
  have e := receive_of_output (mappedRead xs false) (expected control ys.length) ys carry cin hn
    (by simpa only [source] using ha)
    (fun q hq => (expected_sources control ys.length q hq) ▸ hw)
    (by simpa [mappedRead] using hl) (expected_length _ _ (by omega)) hc s m clean
    (by simpa only [read_add] using output)
  simpa only [tailReceiver,read_add] using e

def dropKnown (a b c control : Wire) (xs ys cs : List Wire) : Program :=
  [.CX a c] ++ tailReceiver xs ys cs c control ++ [.CX a c,.CX a b,.CX control b]

def dropOrdinary (a b c control : Wire) (xs ys cs : List Wire) : Program :=
  [.CX a c] ++ addInPlace xs ys cs c ++ [.CX a c,.CX a b,.CX control b]

theorem dropKnown_counts (a b c control : Wire) (xs ys cs : List Wire)
    (hl : xs.length=ys.length) (hc : cs.length+1=ys.length) :
    toffoliCount (dropKnown a b c control xs ys cs)=0 ∧
    measurementCount (dropKnown a b c control xs ys cs)=
      measurementCount (dropOrdinary a b c control xs ys cs) := by
  have kn := tailReceiver_counts xs ys cs c control hl hc
  have old := addInPlace_counts xs ys cs c hl hc
  simp only [dropKnown,dropOrdinary,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,kn.1,kn.2,old.2]
  trivial

theorem dropKnown_eq (a b c control : Wire) (xs ys cs : List Wire)
    (hn : (c::ys++cs).Nodup) (ha : ∀q∈xs,q∉c::ys++cs)
    (hw : control∉c::ys++cs) (hl : xs.length=ys.length) (hc : cs.length+1=ys.length)
    (s : State) (m : List Bool)
    (clean : ∀q∈cs,(run [.CX a c] [] s).basis q=false)
    (output : regValue ys (run (addInPlace xs ys cs c) [] (run [.CX a c] [] s)).basis =
      mappedValue (expected control ys.length) (run [.CX a c] [] s).basis) :
    run (dropKnown a b c control xs ys cs) m s =
      run (dropOrdinary a b c control xs ys cs) m s := by
  have e := tailReceiver_eq xs ys cs c control hn ha hw hl hc
    (run [.CX a c] [] s) (m.take (ys.length-1)) clean output
  have kn := (tailReceiver_counts xs ys cs c control hl hc).2
  have old := (addInPlace_counts xs ys cs c hl hc).2
  simp only [dropKnown,dropOrdinary,run_append,measurementCount_append,
    measurementCount,kn,old,List.take_zero,List.drop_zero,Nat.zero_add]
  rw [e]


def rowPost (control : Wire) (low : List Wire) (top : Wire) : Program :=
  notRegister (low++[top]) ++ xorWhenFalse control low

theorem dropKnown_post_eq (a b c control top : Wire) (xs low cs : List Wire)
    (hn : (c::(low++[top])++cs).Nodup)
    (ha : ∀q∈xs,q∉c::(low++[top])++cs)
    (hw : control∉c::(low++[top])++cs)
    (hb : b∉low++[top]) (hbc : control≠b)
    (hd : (b::low++[top]).Nodup)
    (hl : xs.length=(low++[top]).length) (hc : cs.length+1=(low++[top]).length)
    (s : State) (m : List Bool)
    (clean : ∀q∈cs,(run [.CX a c] [] s).basis q=false)
    (zero : regValue (b::low++[top])
      (run (dropOrdinary a b c control xs (low++[top]) cs ++ rowPost control (b::low) top) [] s).basis=0) :
    run (dropKnown a b c control xs (low++[top]) cs ++ rowPost control (b::low) top) m s =
    run (dropOrdinary a b c control xs (low++[top]) cs ++ rowPost control (b::low) top) m s := by
  let u := run [.CX a c] [] s
  let t := run (addInPlace xs (low++[top]) cs c) [] u
  let finish : Program := [.CX a c,.CX a b,.CX control b]
  let v := run finish [] t
  have cv : control≠c := fun e => hw (by simp [e])
  have used (q : Wire) (hq : q∈low++[top]) : q∈c::(low++[top])++cs :=
    List.mem_append_left cs (List.mem_cons_of_mem c hq)
  have out : ∀q∈low++[top],q≠c := by
    intro q hq eq
    subst q
    exact (List.nodup_cons.mp hn).1 (List.mem_append_left cs hq)
  have kept (q : Wire) (hq : q≠c ∧ q≠b) : v.basis q=t.basis q := by
    simp [v,finish,run,writeBit,hq.1,hq.2]
  have vctl : v.basis control=t.basis control := kept control ⟨cv,hbc⟩
  have z : regValue ((b::low)++[top]) (run (rowPost control (b::low) top) [] v).basis=0 := by
    rw [run_append] at zero
    simp only [List.take_nil,List.drop_nil] at zero
    unfold dropOrdinary at zero
    rw [run_append,run_append] at zero
    simpa only [List.take_nil,List.drop_nil,u,t,finish,v,List.cons_append] using zero
  have controlAway : control∉(b::low)++[top] := by
    intro hq
    rcases List.mem_cons.mp hq with eq | hq
    · exact hbc eq
    · exact hw (used control hq)
  have recov := post_recovers_bits control top (b::low) v hd controlAway z
  have lo : ∀q∈low,t.basis q=t.basis control := by
    intro q hq
    rw [←kept q ⟨out q (by simp [hq]),fun e => hb (by simp [←e,hq])⟩,←vctl]
    exact recov.1 q (by simp [hq])
  have topTrue : t.basis top=true := by
    rw [←kept top ⟨out top (by simp),fun e => hb (by simp [←e])⟩]
    exact recov.2
  have expectedOut := expected_value control top low t.basis lo topTrue
  have stable : t.basis control=u.basis control := by
    have keep := (mappedAdd_correct (mappedRead xs false) (low++[top]) cs c hn
      (by simpa only [read_sources] using ha) (by simpa [mappedRead] using hl) hc u [] clean).2.1
      control (fun hq => hw (used control hq))
    simpa only [read_add] using keep
  have value : regValue (low++[top]) t.basis =
      mappedValue (expected control (low++[top]).length) u.basis := by
    calc
      _ = mappedValue (expected control (low++[top]).length) t.basis := by
        simpa only [expected,List.length_append,List.length_singleton,Nat.add_sub_cancel] using expectedOut.symm
      _ = _ := mappedValue_congr _ _ _ (fun q hq => by
        rw [expected_sources control _ q hq]; exact stable)
  have eq (r : List Bool) := dropKnown_eq a b c control xs (low++[top]) cs hn ha hw hl hc s r clean value
  have mc := (dropKnown_counts a b c control xs (low++[top]) cs hl hc).2
  simp only [run_append]
  rw [mc,eq]


theorem first_copy_of_known_output (a a' b b' cin : Wire) (xs ys carry : List Wire)
    (hn : (cin::(b::b'::ys)++carry).Nodup)
    (ha : ∀q∈a::a'::xs,q∉cin::(b::b'::ys)++carry)
    (hl : (a::a'::xs).length=(b::b'::ys).length)
    (hc : carry.length+1=(b::b'::ys).length)
    (s : State) (clean : ∀q∈carry,s.basis q=false)
    (output : regValue (b::b'::ys) (run (addInPlace (a::a'::xs) (b::b'::ys) carry cin) [] s).basis =
      mappedValue (expected cin (b::b'::ys).length) s.basis) :
    ((s.basis b ^^ s.basis a) && (s.basis cin ^^ s.basis a))=false := by
  have old := mappedAdd_correct (mappedRead (a::a'::xs) false) (b::b'::ys) carry cin hn
    (by simpa only [read_sources] using ha) (by simpa [mappedRead] using hl) hc s [] clean
  have ready := KnownOutputAdder.ready_of_value (mappedRead (a::a'::xs) false)
    (expected cin (b::b'::ys).length) (b::b'::ys) (s.basis cin) s.basis
    (by simpa [mappedRead] using hl) (expected_length _ _ (by simp))
    ((by simpa only [read_add] using output.symm.trans (by simpa only [read_add] using old.2.2)))
  simp only [KnownOutputAdder.Ready,expected,List.length_cons,Nat.succ_sub_succ_eq_sub,
    Nat.sub_zero,List.replicate_succ,List.cons_append,List.map_cons,mappedRead,
    KnownOutputAdder.sumBits] at ready
  have head := (List.cons.inj ready).1
  simp only [MappedBit.value,Option.map_some,Option.getD_some,Bool.false_xor] at head
  have eq : ∀x y z : Bool,z=sumBit x y z → x=y := by decide
  have same := eq _ _ _ head
  rw [same]
  simp


theorem tailReceiver_physical (xs ys carry : List Wire) (cin control : Wire)
    (hn : (cin::ys++carry).Nodup)
    (ha : ∀q∈xs,q∉cin::ys++carry) (hw : control∉cin::ys++carry)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    GatePhysical (tailReceiver xs ys carry cin control) := by
  apply KnownOutputAdder.program_physical _ _ _ _ _
    (by simpa [mappedRead] using hl) (expected_length _ _ (by omega)) hc hn
  · intro b hb q hq
    apply ha q
    rw [←read_sources xs]
    apply List.mem_flatMap.mpr
    exact ⟨b,hb,by simpa using hq⟩
  · intro b hb q hq
    have mem : q∈mappedWires (expected control ys.length) :=
      List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
    rw [expected_sources control _ q mem]
    exact hw

theorem tailReceiver_support (xs ys carry : List Wire) (cin control : Wire) :
    wires (tailReceiver xs ys carry cin control) ⊆ (xs++[control]++ys++carry++[cin]).toFinset := by
  intro q hq
  have sup := KnownOutputAdder.program_support (mappedRead xs false) (expected control ys.length) ys
    carry cin hq
  by_contra away
  have neq : q≠control := fun eq => away (by simp [eq])
  have notWitness : q∉mappedWires (expected control ys.length) :=
    fun mem => neq (expected_sources control _ q mem)
  simp only [read_sources,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at sup away
  tauto


theorem adder_output_from_post_zero (xs low carry : List Wire) (top control : Wire)
    (hn : (control::(low++[top])++carry).Nodup)
    (ha : ∀q∈xs,q∉control::(low++[top])++carry)
    (hl : xs.length=(low++[top]).length) (hc : carry.length+1=(low++[top]).length)
    (s : State) (clean : ∀q∈carry,s.basis q=false)
    (zero : regValue (low++[top])
      (run (addInPlace xs (low++[top]) carry control ++ rowPost control low top) [] s).basis=0) :
    regValue (low++[top]) (run (addInPlace xs (low++[top]) carry control) [] s).basis =
      mappedValue (expected control (low++[top]).length) s.basis := by
  let t := run (addInPlace xs (low++[top]) carry control) [] s
  have hd : (low++[top]).Nodup := (List.nodup_append.mp (List.nodup_cons.mp hn).2).1
  have away : control∉low++[top] := fun mem =>
    (List.nodup_cons.mp hn).1 (List.mem_append_left carry mem)
  rw [run_append] at zero
  simp only [List.take_nil,List.drop_nil] at zero
  have result := post_recovers_expected control top low t hd away zero
  have old := mappedAdd_correct (mappedRead xs false) (low++[top]) carry control hn
    (by simpa only [read_sources] using ha) (by simpa [mappedRead] using hl) hc s [] clean
  have stable : t.basis control=s.basis control := by
    simpa only [read_add] using old.2.1 control away
  calc
    _ = mappedValue (expected control (low++[top]).length) t.basis := by
      simpa only [expected,List.length_append,List.length_singleton,Nat.add_sub_cancel] using result.symm
    _ = _ := mappedValue_congr _ _ _ (fun q hq => by
      rw [expected_sources control _ q hq]; exact stable)


theorem tailReceiver_support_old (xs ys carry : List Wire) (cin control : Wire)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    wires (tailReceiver xs ys carry cin control) ⊆ wires (addInPlace xs ys carry cin) ∪ {control} := by
  intro q hq
  have h := tailReceiver_support xs ys carry cin control hq
  rw [addInPlace_wires xs ys carry cin hl hc]
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    Finset.mem_union,Finset.mem_singleton] at h ⊢
  tauto

theorem dropKnown_support (a b c control : Wire) (xs ys cs : List Wire)
    (hl : xs.length=ys.length) (hc : cs.length+1=ys.length) :
    wires (dropKnown a b c control xs ys cs) ⊆ wires (dropOrdinary a b c control xs ys cs) := by
  have ctl : control∈wires (dropOrdinary a b c control xs ys cs) := by
    simp [dropOrdinary,wires_append,wires,Instr.wires]
  intro q hq
  simp only [dropKnown,wires_append,Finset.mem_union] at hq
  simp only [dropOrdinary,wires_append]
  rcases hq with (pre | mid) | post
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ pre)
  · rcases Finset.mem_union.mp (tailReceiver_support_old xs ys cs c control hl hc mid) with old | eq
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ old)
    · have e := Finset.mem_singleton.mp eq
      rw [e]
      simpa only [dropOrdinary,wires_append] using ctl
  · exact Finset.mem_union_right _ post

theorem dropKnown_physical (a b c control : Wire) (xs ys cs : List Wire)
    (hn : (c::ys++cs).Nodup) (ha : ∀q∈xs,q∉c::ys++cs)
    (hw : control∉c::ys++cs) (hl : xs.length=ys.length) (hc : cs.length+1=ys.length)
    (old : GatePhysical (dropOrdinary a b c control xs ys cs)) :
    GatePhysical (dropKnown a b c control xs ys cs) := by
  simp only [dropOrdinary,gatePhysical_append] at old
  simp only [dropKnown,gatePhysical_append]
  exact ⟨⟨old.1.1,tailReceiver_physical xs ys cs c control hn ha hw hl hc⟩,old.2⟩

end ECDSAAdd.Entrant.KnownFirstRow

#print axioms ECDSAAdd.Entrant.KnownFirstRow.dropKnown_post_eq
#print axioms ECDSAAdd.Entrant.KnownFirstRow.tailReceiver_eq
#print axioms ECDSAAdd.Entrant.KnownFirstRow.first_copy_of_known_output
end

-- Consolidated source module: KnownLastCarry
section

namespace ECDSAAdd.Entrant.KnownLastCarry
open Arithmetic

def topBit : MappedBit := ⟨none,true⟩

def two (b b' : MappedBit) (y y' c cin : Wire) : Program :=
  KnownOutputAdder.prepare b' topBit y' c ++ mappedSum b' y' c ++
    mappedEraseCarry b y cin c ++ mappedSum b y cin

theorem two_eq (b b' : MappedBit) (y y' c cin : Wire)
    (hn : [cin,y,y',c].Nodup)
    (ha : ∀q∈mappedWires [b,b'],q∉[cin,y,y',c])
    (s : State) (m : List Bool) (clean : s.basis c=false)
    (top : sumBit (b'.value s.basis) (s.basis y')
      (carryBit (b.value s.basis) (s.basis y) (s.basis cin))=true) :
    run (two b b' y y' c cin) m s=run (mappedAdd [b,b'] [y,y'] [c] cin) m s := by
  let low : MappedBit := ⟨none,sumBit (b.value s.basis) (s.basis y) (s.basis cin)⟩
  have ready : KnownOutputAdder.Ready [b,b'] [low,topBit] [y,y'] (s.basis cin) s.basis := by
    simp only [KnownOutputAdder.Ready,KnownOutputAdder.sumBits,List.map_cons,List.map_nil,
      List.cons.injEq,low,topBit,MappedBit.value,Option.map_none,Option.getD_none,Bool.xor_false]
    exact ⟨trivial,top.symm,trivial⟩
  have eq := KnownOutputAdder.program_eq_mappedAdd [b,b'] [low,topBit] [y,y'] [c] cin
    hn ha (by simp [low,topBit,mappedWires]) rfl rfl rfl s m
    (by simpa using clean) ready
  simpa only [KnownOutputAdder.program,two,List.append_assoc] using eq

theorem two_counts (b b' : MappedBit) (y y' c cin : Wire) :
    toffoliCount (two b b' y y' c cin)=0 ∧ measurementCount (two b b' y y' c cin)=1 := by
  have cnt := KnownOutputAdder.program_counts [b,b'] [topBit,topBit] [y,y'] [c] cin rfl rfl rfl
  simpa only [KnownOutputAdder.program,two,List.append_assoc] using cnt

theorem two_physical (b b' : MappedBit) (y y' c cin : Wire)
    (hn : [cin,y,y',c].Nodup)
    (ha : ∀q∈mappedWires [b,b'],q∉[cin,y,y',c]) :
    GatePhysical (two b b' y y' c cin) := by
  have p := KnownOutputAdder.program_physical [b,b'] [topBit,topBit] [y,y'] [c] cin
    rfl rfl rfl hn (by
      intro bit hbit q hq
      apply ha q
      exact List.mem_flatMap.mpr ⟨bit,hbit,by simpa using hq⟩) (by simp [topBit])
  simpa only [KnownOutputAdder.program,two,List.append_assoc] using p

/-- Ordinary adder until its two-bit tail, where the top output is known. -/
def program : List Wire → List Wire → List Wire → Wire → Program
  | [a,a'],[b,b'],[c],cin => two ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin
  | a::a'::as,b::b'::bs,c::cs,cin =>
      majority a b cin c ++ program (a'::as) (b'::bs) cs c ++
        eraseCarry a b cin c ++ [.CX a b,.CX cin b]
  | [a],[b],[],cin => [.CX a b,.CX cin b]
  | _,_,_,_ => []

theorem program_counts (xs ys carry : List Wire) (cin : Wire)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    toffoliCount (program xs ys carry cin)=ys.length-2 ∧
    measurementCount (program xs ys carry cin)=ys.length-1 := by
  induction xs generalizing ys carry cin with
  | nil => simp at hl hc;omega
  | cons a xs ih =>
    cases xs with
    | nil =>
      obtain ⟨b,rfl⟩ : ∃b,ys=[b] := by
        cases ys with
        | nil => simp at hl
        | cons b ys => have e : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm);subst ys;exact ⟨b,rfl⟩
      have e : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst carry
      simp [program,toffoliCount,measurementCount]
    | cons a' as =>
      obtain ⟨b,b',bs,rfl⟩ : ∃b b' bs,ys=b::b'::bs := by
        match ys,hl with
        | b::b'::bs,_ => exact ⟨b,b',bs,rfl⟩
        | [],h => simp at h
        | [_],h => simp at h
      obtain ⟨c,cs,rfl⟩ : ∃c cs,carry=c::cs := by
        match carry,hc with
        | c::cs,_ => exact ⟨c,cs,rfl⟩
        | [],h => simp at h
      cases as with
      | nil =>
        have eb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hc hl;omega)
        subst bs;subst cs
        simpa only [program,List.length_cons,List.length_nil] using two_counts ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin
      | cons a'' as =>
        have hi := ih (b'::bs) cs c (by simpa using hl) (by simpa using hc)
        have cap : 2≤(b'::bs).length := by simp only [List.length_cons] at hl ⊢;omega
        simp only [program,toffoliCount_append,measurementCount_append,
          hi.1,hi.2]
        simp only [majority,eraseCarry,toffoliCount,measurementCount,List.length_cons]
        simp only [List.length_cons] at hl hc cap
        constructor <;> omega

theorem sumBits_congr (xs ys : List Wire) (cin : Bool) (s t : BasisState)
    (hx : ∀q∈xs,s q=t q) (hy : ∀q∈ys,s q=t q) :
    KnownOutputAdder.sumBits (mappedRead xs false) ys cin s=
      KnownOutputAdder.sumBits (mappedRead xs false) ys cin t := by
  induction xs generalizing ys cin with
  | nil => rfl
  | cons a xs ih =>
    cases ys with
    | nil => rfl
    | cons b ys =>
      have aeq := hx a (by simp)
      have beq := hy b (by simp)
      simp only [mappedRead,List.map_cons,KnownOutputAdder.sumBits,MappedBit.value,
        Option.map_some,Option.getD_some,Bool.false_xor]
      rw [aeq,beq]
      congr 1
      exact ih ys _ (fun q hq => hx q (by simp [hq])) (fun q hq => hy q (by simp [hq]))

theorem read_add (xs ys carry : List Wire) (cin : Wire) :
    mappedAdd (mappedRead xs false) ys carry cin=addInPlace xs ys carry cin := by
  induction xs generalizing ys carry cin with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases xs with
    | nil => cases ys with
      | nil => rfl
      | cons y ys => cases ys <;> rfl
    | cons a' xs =>
      cases ys with
      | nil => rfl
      | cons b ys =>
        cases ys with
        | nil => rfl
        | cons b' ys =>
          cases carry with
          | nil => rfl
          | cons c cs =>
            simp only [mappedRead,List.map_cons,mappedAdd,mappedMajority,
              mappedEraseCarry,mappedSum,Bool.false_eq_true,if_false,addInPlace]
            rw [←ih (b'::ys) cs c]
            rfl

theorem program_eq (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (clean : ∀q∈carry,s.basis q=false)
    (top : (KnownOutputAdder.sumBits (mappedRead xs false) ys (s.basis cin) s.basis).getLastD false=true) :
    run (program xs ys carry cin) m s=run (addInPlace xs ys carry cin) m s := by
  induction xs generalizing ys carry cin s m with
  | nil => simp at hl hc;omega
  | cons a xs ih =>
    cases xs with
    | nil =>
      obtain ⟨b,rfl⟩ : ∃b,ys=[b] := by
        cases ys with
        | nil => simp at hl
        | cons b ys => have e : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm);subst ys;exact ⟨b,rfl⟩
      have e : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst carry
      rfl
    | cons a' as =>
      obtain ⟨b,b',bs,rfl⟩ : ∃b b' bs,ys=b::b'::bs := by
        match ys,hl with
        | b::b'::bs,_ => exact ⟨b,b',bs,rfl⟩
        | [],h => simp at h
        | [_],h => simp at h
      obtain ⟨c,cs,rfl⟩ : ∃c cs,carry=c::cs := by
        match carry,hc with
        | c::cs,_ => exact ⟨c,cs,rfl⟩
        | [],h => simp at h
      have cnt (q : Wire) := List.nodup_iff_count.mp hn q
      cases as with
      | nil =>
        have eb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hc hl;omega)
        subst bs;subst cs
        have nd : [cin,b,b',c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have away : ∀q∈mappedWires [⟨some a,false⟩,⟨some a',false⟩],q∉[cin,b,b',c] := by
          intro q hq bad
          have l : q∈[a,a'] := by simpa [mappedWires] using hq
          have h := cnt q
          have lp := List.count_pos_iff.mpr l
          have rp := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,List.count_nil] at h lp rp
          omega
        have tp : sumBit (s.basis a') (s.basis b') (carryBit (s.basis a) (s.basis b) (s.basis cin))=true := by
          simpa [mappedRead,KnownOutputAdder.sumBits,MappedBit.value] using top
        have leaf := two_eq ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin nd away s m
          (clean c (by simp)) (by simpa [MappedBit.value] using tp)
        change run (two _ _ _ _ _ _) _ _=_
        rw [←read_add]
        exact leaf
      | cons a'' as =>
        have nd : (c::(a'::a''::as)++(b'::bs)++cs).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        have nd4 : [a,b,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have fresh (q : Wire) (hq : q∈(a'::a''::as)++(b'::bs)++cs) : q≠c := by
          intro eq
          have p := List.count_pos_iff.mpr hq
          have h := cnt q
          subst q
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h p
          omega
        let K := carryBit (s.basis a) (s.basis b) (s.basis cin)
        let u : State := ⟨s.phase,writeBit s.basis c K⟩
        have keep (q : Wire) (hq : q∈(a'::a''::as)++(b'::bs)++cs) : u.basis q=s.basis q := by
          simp [u,writeBit,fresh q hq]
        have cu : u.basis c=K := by simp [u,writeBit]
        have preRun (r : List Bool) : run (majority a b cin c) r s=u := by
          rw [majority_correct _ _ _ _ nd4]
          simp [u,K,clean c (by simp)]
        have tailTop : (KnownOutputAdder.sumBits (mappedRead (a'::a''::as) false)
            (b'::bs) (u.basis c) u.basis).getLastD false=true := by
          rw [cu,sumBits_congr _ _ _ u.basis s.basis
            (fun q hq => keep q (by simp only [List.mem_append,List.mem_cons] at hq ⊢;tauto))
            (fun q hq => keep q (by simp only [List.mem_append,List.mem_cons] at hq ⊢;tauto))]
          simpa only [mappedRead,List.map_cons,KnownOutputAdder.sumBits,MappedBit.value,
            Option.map_some,Option.getD_some,Bool.false_xor,List.getLastD_cons,K] using top
        have tc : ∀q∈cs,u.basis q=false := by
          intro q hq
          rw [keep q (by simp [hq])]
          exact clean q (by simp [hq])
        have tail (r : List Bool) := ih (b'::bs) cs c nd (by simpa using hl) (by simpa using hc) u r tc tailTop
        have nm := (program_counts (a'::a''::as) (b'::bs) cs c (by simpa using hl) (by simpa using hc)).2
        have om := (addInPlace_counts (a'::a''::as) (b'::bs) cs c (by simpa using hl) (by simpa using hc)).2
        have zero : measurementCount (majority a b cin c)=0 := rfl
        rw [program,addInPlace]
        simp only [List.append_assoc,run_append,run_take,zero,nm,om,List.take_zero,List.drop_zero]
        simp only [preRun,tail]
        all_goals simp

theorem two_resources (a a' b b' c cin : Wire) :
    wires (two ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin) ⊆
      wires (addInPlace [a,a'] [b,b'] [c] cin) ∧
    Challenge.gateSlots (two ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin) ≤
      Challenge.gateSlots (addInPlace [a,a'] [b,b'] [c] cin) := by
  constructor
  · intro q hq
    simp only [two,topBit,KnownOutputAdder.prepare,KnownOutputAdder.xorBit,
      mappedSum,mappedEraseCarry,Bool.false_eq_true,if_false,if_true,
      addInPlace,majority,eraseCarry,wires_append,wires,Instr.wires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] at hq ⊢
    tauto
  · simp [two,topBit,KnownOutputAdder.prepare,KnownOutputAdder.xorBit,
      mappedSum,mappedEraseCarry,addInPlace,majority,eraseCarry,
      Challenge.gateSlots,Challenge.instructionSlots]

theorem program_resources (xs ys carry : List Wire) (cin : Wire)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    wires (program xs ys carry cin) ⊆ wires (addInPlace xs ys carry cin) ∧
    Challenge.gateSlots (program xs ys carry cin) ≤ Challenge.gateSlots (addInPlace xs ys carry cin) := by
  induction xs generalizing ys carry cin with
  | nil => simp at hl hc;omega
  | cons a xs ih =>
    cases xs with
    | nil =>
      obtain ⟨b,rfl⟩ : ∃b,ys=[b] := by
        cases ys with
        | nil => simp at hl
        | cons b ys => have e : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm);subst ys;exact ⟨b,rfl⟩
      have e : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst carry
      simp [program,addInPlace]
    | cons a' as =>
      obtain ⟨b,b',bs,rfl⟩ : ∃b b' bs,ys=b::b'::bs := by
        match ys,hl with
        | b::b'::bs,_ => exact ⟨b,b',bs,rfl⟩
        | [],h => simp at h
        | [_],h => simp at h
      obtain ⟨c,cs,rfl⟩ : ∃c cs,carry=c::cs := by
        match carry,hc with
        | c::cs,_ => exact ⟨c,cs,rfl⟩
        | [],h => simp at h
      cases as with
      | nil =>
        have eb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hc hl;omega)
        subst bs;subst cs
        exact two_resources a a' b b' c cin
      | cons a'' as =>
        have side := ih (b'::bs) cs c (by simpa using hl) (by simpa using hc)
        rw [program,addInPlace]
        constructor
        · simp only [wires_append]
          exact Finset.union_subset_union (Finset.union_subset_union
            (Finset.union_subset_union (Finset.Subset.refl _) side.1) (Finset.Subset.refl _)) (Finset.Subset.refl _)
        · simp only [Challenge.gateSlots_append]
          have le := side.2
          omega
        all_goals simp

theorem program_physical (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    GatePhysical (program xs ys carry cin) := by
  induction xs generalizing ys carry cin with
  | nil => simp at hl hc;omega
  | cons a xs ih =>
    cases xs with
    | nil =>
      obtain ⟨b,rfl⟩ : ∃b,ys=[b] := by
        cases ys with
        | nil => simp at hl
        | cons b ys => have e : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm);subst ys;exact ⟨b,rfl⟩
      have e : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst carry
      exact addInPlace_physical [a] [b] [] cin hn
    | cons a' as =>
      obtain ⟨b,b',bs,rfl⟩ : ∃b b' bs,ys=b::b'::bs := by
        match ys,hl with
        | b::b'::bs,_ => exact ⟨b,b',bs,rfl⟩
        | [],h => simp at h
        | [_],h => simp at h
      obtain ⟨c,cs,rfl⟩ : ∃c cs,carry=c::cs := by
        match carry,hc with
        | c::cs,_ => exact ⟨c,cs,rfl⟩
        | [],h => simp at h
      have cnt (q : Wire) := List.nodup_iff_count.mp hn q
      cases as with
      | nil =>
        have eb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hc hl;omega)
        subst bs;subst cs
        have nd : [cin,b,b',c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have away : ∀q∈mappedWires [⟨some a,false⟩,⟨some a',false⟩],q∉[cin,b,b',c] := by
          intro q hq bad
          have l : q∈[a,a'] := by simpa [mappedWires] using hq
          have h := cnt q
          have lp := List.count_pos_iff.mpr l
          have rp := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,List.count_nil] at h lp rp
          omega
        exact two_physical ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin nd away
      | cons a'' as =>
        have nd : (c::(a'::a''::as)++(b'::bs)++cs).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        have tail := ih (b'::bs) cs c nd (by simpa using hl) (by simpa using hc)
        have old := addInPlace_physical (a::a'::a''::as) (b::b'::bs) (c::cs) cin hn
        rw [program]
        · simp only [addInPlace,gatePhysical_append] at old ⊢
          tauto
        · simp

theorem boolValue_read (xs : List Wire) (s : BasisState) :
    KnownOutputAdder.boolValue (xs.map s)=regValue xs s := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : s a <;> simp [KnownOutputAdder.boolValue,regValue,ih,h]

theorem sumBits_output (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (clean : ∀q∈carry,s.basis q=false) :
    KnownOutputAdder.sumBits (mappedRead xs false) ys (s.basis cin) s.basis=
      ys.map (run (addInPlace xs ys carry cin) [] s).basis := by
  have old := addInPlace_correct xs ys carry cin hn hl hc s [] clean
  apply KnownOutputAdder.boolValue_injective
  · simp only [List.length_map]
    exact KnownOutputAdder.sumBits_length (mappedRead xs false) ys (s.basis cin) s.basis (by simpa [mappedRead] using hl)
  · rw [KnownOutputAdder.sumBits_value (mappedRead xs false) ys (s.basis cin) s.basis (by simpa [mappedRead] using hl),boolValue_read,mappedRead_value,old.2.2]

theorem program_eq_of_top_output (xs low carry : List Wire) (top cin : Wire)
    (hn : (cin::xs++(low++[top])++carry).Nodup)
    (hl : xs.length=(low++[top]).length) (hc : carry.length+1=(low++[top]).length)
    (s : State) (m : List Bool) (clean : ∀q∈carry,s.basis q=false)
    (ht : (run (addInPlace xs (low++[top]) carry cin) [] s).basis top=true) :
    run (program xs (low++[top]) carry cin) m s=run (addInPlace xs (low++[top]) carry cin) m s := by
  apply program_eq xs (low++[top]) carry cin hn hl hc s m clean
  rw [sumBits_output xs (low++[top]) carry cin hn hl hc s clean]
  simpa using ht

end ECDSAAdd.Entrant.KnownLastCarry
#print axioms ECDSAAdd.Entrant.KnownLastCarry.two_eq

#print axioms ECDSAAdd.Entrant.KnownLastCarry.program_eq

#print axioms ECDSAAdd.Entrant.KnownLastCarry.program_physical
end

-- Consolidated source module: KnownLastRow
section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KnownLastRow
open Arithmetic

def normalizedRecords : Program → List Bool → List Bool
  | [], _ => []
  | .measureX _ _ _ :: p, [] => false::normalizedRecords p []
  | .measureX _ _ _ :: p, b::bs => b::normalizedRecords p bs
  | _::p, m => normalizedRecords p m

theorem run_append_normalized (p q : Program) (m₁ m₂ : List Bool) (s : State) :
    run (p++q) (normalizedRecords p m₁++m₂) s=run q m₂ (run p m₁ s) := by
  induction p generalizing m₁ s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [normalizedRecords,List.cons_append,run]
    all_goals try exact ih m₁ _
    cases m₁ <;> simp [normalizedRecords,ih]

theorem signedRow_restore (control : Wire) (xs dst pad carry : List Wire)
    (hn : (control::xs++dst++pad++carry).Nodup) (hd : dst.length=xs.length+1)
    (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (s : State) (bound : regValue dst s.basis<2^xs.length)
    (work : regValue (pad++carry) s.basis=0) (forward backward : List Bool) :
    run (signedSquareRowClear control xs dst pad carry) backward
      (run (signedSquareRow control xs dst pad carry) forward s)=s := by
  let F := signedSquareRow control xs dst pad carry
  let B := signedSquareRowClear control xs dst pad carry
  have round := signedSquareRow_roundtrip control xs dst pad carry hn hd hp hc s.basis work _
    bound s (normalizedRecords F forward++backward)
    (And.intro rfl (fun _ _ => rfl))
  rw [run_append_normalized F B forward backward s] at round
  apply State.extensionality
  · exact round.1
  · funext q
    by_cases mem : q∈dst
    · exact (regValue_eq_iff dst _ _).mp round.2.1 q mem
    · exact round.2.2 q mem

theorem post_recovers_top (control top : Wire) (low : List Wire) (s : State)
    (hn : (low++[top]).Nodup) (hc : control∉low++[top])
    (hz : (run (KnownFirstRow.rowPost control low top) [] s).basis top=false) :
    s.basis top=true := by
  have hl : low.Nodup := (List.nodup_append.mp hn).1
  have ht : top∉low := by
    have h := (List.nodup_append.mp hn).2.2
    exact fun hq => h top hq top (by simp) rfl
  have hcl : control∉low := fun hq => hc (by simp [hq])
  simp only [KnownFirstRow.rowPost,run_append,List.take_nil,List.drop_nil] at hz
  rw [notRegister_correct _ hn,xorWhenFalse_correct control low hl hcl] at hz
  simp only [xorFalseBasis,if_neg ht,show top∈low++[top] from by simp,if_pos] at hz
  simpa using hz

/-- Last-carry receiver in an otherwise ordinary inverse signed row. -/
def rowClear (control : Wire) (xs dst pad carry : List Wire) : Program :=
  xorWhenFalse control dst ++ (notRegister dst ++
    (KnownLastCarry.program (xs++pad.take 1) dst (carry.take xs.length) control ++
      (notRegister dst ++ xorWhenFalse control (dst.take xs.length))))

theorem adder_restore_of_top (xs low carry : List Wire) (top cin : Wire)
    (hn : (cin::xs++(low++[top])++carry).Nodup)
    (hl : xs.length=(low++[top]).length) (hc : carry.length+1=(low++[top]).length)
    (s target : State) (clean : ∀q∈carry,s.basis q=false)
    (targetTop : target.basis top=false)
    (restore : ∀r,run (addInPlace xs (low++[top]) carry cin++KnownFirstRow.rowPost cin low top) r s=target)
    (m : List Bool) :
    run (KnownLastCarry.program xs (low++[top]) carry cin++KnownFirstRow.rowPost cin low top) m s=target := by
  have nd : (low++[top]).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have away : cin∉low++[top] := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (List.mem_append_left carry (List.mem_append_right xs bad))
  have zero : (run (KnownFirstRow.rowPost cin low top) []
      (run (addInPlace xs (low++[top]) carry cin) [] s)).basis top=false := by
    have h := (congrArg (fun t : State => t.basis top) (restore [])).trans targetTop
    simpa only [run_append,List.take_nil,List.drop_nil] using h
  have topKnown := post_recovers_top cin top low _ nd away zero
  have eq (r : List Bool) := KnownLastCarry.program_eq_of_top_output xs low carry top cin hn hl hc s r clean topKnown
  have old := (addInPlace_counts xs (low++[top]) carry cin hl hc).2
  have new := (KnownLastCarry.program_counts xs (low++[top]) carry cin hl hc).2
  have result := restore m
  simp only [run_append,old] at result
  simpa only [run_append,new,eq] using result

theorem rowClear_on_image (control top pad : Wire) (xs low carry : List Wire)
    (hn : (control::xs++(low++[top])++[pad]++carry).Nodup)
    (hl : low.length=xs.length) (hc : carry.length=xs.length)
    (s : State) (topZero : s.basis top=false)
    (work : regValue ([pad]++carry) s.basis=0) (forward backward : List Bool) :
    run (rowClear control xs (low++[top]) [pad] carry) backward
      (run (signedSquareRow control xs (low++[top]) [pad] carry) forward s)=s := by
  let D := low++[top]
  let F := signedSquareRow control xs D [pad] carry
  let Pre := xorWhenFalse control D++notRegister D
  let Post := KnownFirstRow.rowPost control low top
  let f := run F forward s
  let u := run Pre [] f
  have cnt (q : Wire) := List.nodup_iff_count.mp hn q
  have hd : D.length=xs.length+1 := by simp [D,hl]
  have ndD : D.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := cnt q
    simp only [D,List.count_cons,List.count_append] at h ⊢
    omega
  have ctl : control∉D := by
    intro bad
    have h := cnt control
    have p := List.count_pos_iff.mpr bad
    simp only [D,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h p
    omega
  have away (q : Wire) (hq : q∈carry) : q∉D := by
    intro bad
    have h := cnt q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [D,List.count_cons,List.count_append] at h b
    omega
  have bound : regValue D s.basis<2^xs.length := by
    have b := regValue_lt low s.basis
    simpa [D,regValue_append,regValue,topZero,hl] using b
  have frame := signedSquareRow_frame control xs D [pad] carry hn hd (by simp) hc.ge
    s.basis (s.basis control) rfl work (regValue D s.basis) (regValue_lt D s.basis)
    s forward (And.intro rfl (fun _ _ => rfl))
  have fKeep (q : Wire) (hq : q∉D) : f.basis q=s.basis q := frame.2.2 q hq
  have uKeep (q : Wire) (hq : q∉D) : u.basis q=s.basis q := by
    dsimp only [u,Pre]
    rw [run_append]
    simp only [List.take_nil,List.drop_nil]
    rw [xorWhenFalse_correct control D ndD ctl,notRegister_correct D ndD]
    simp only [if_neg hq,xorFalseBasis,if_neg hq]
    exact fKeep q hq
  have clean : ∀q∈carry,u.basis q=false := by
    intro q hq
    rw [uKeep q (away q hq)]
    exact (regValue_zero _ _).mp work q (List.mem_append_right [pad] hq)
  have preM : measurementCount Pre=0 := by
    simp [Pre,measurementCount_append,xorWhenFalse_measurementCount,(notRegister_counts D).2]
  have takeC : carry.take xs.length=carry := by rw [←hc];exact List.take_length
  have takeD : D.take xs.length=low := by rw [←hl];exact List.take_left
  have oldShape : signedSquareRowClear control xs D [pad] carry=
      Pre++(addInPlace (xs++[pad]) D carry control++Post) := by
    simp [signedSquareRowClear,Pre,Post,KnownFirstRow.rowPost,takeC,takeD,List.append_assoc,D]
  have newShape : rowClear control xs D [pad] carry=
      Pre++(KnownLastCarry.program (xs++[pad]) D carry control++Post) := by
    simp [rowClear,Pre,Post,KnownFirstRow.rowPost,takeC,takeD,List.append_assoc,D]
  have restore (r : List Bool) : run (addInPlace (xs++[pad]) D carry control++Post) r u=s := by
    have h := signedRow_restore control xs D [pad] carry hn hd (by simp) hc.ge s bound work forward r
    rw [oldShape,run_append,preM,List.take_zero,List.drop_zero] at h
    exact h
  have ndReceiver : (control::(xs++[pad])++D++carry).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := cnt q
    simp only [D,List.count_cons,List.count_append] at h ⊢
    omega
  have result := adder_restore_of_top (xs++[pad]) low carry top control ndReceiver
    (by simp [hl]) (by simp [hc,hl]) u s clean topZero restore backward
  rw [newShape,run_append,preM,List.take_zero,List.drop_zero]
  exact result

theorem rowClear_resources (control : Wire) (xs dst pad carry : List Wire)
    (hx : 1≤xs.length) (hd : dst.length=xs.length+1)
    (hp : 1≤pad.length) (hc : xs.length≤carry.length) :
    toffoliCount (rowClear control xs dst pad carry)+1=toffoliCount (signedSquareRowClear control xs dst pad carry) ∧
    measurementCount (rowClear control xs dst pad carry)=measurementCount (signedSquareRowClear control xs dst pad carry) ∧
    wires (rowClear control xs dst pad carry) ⊆ wires (signedSquareRowClear control xs dst pad carry) ∧
    Challenge.gateSlots (rowClear control xs dst pad carry)≤Challenge.gateSlots (signedSquareRowClear control xs dst pad carry) := by
  have hl : (xs++pad.take 1).length=dst.length := by
    simp only [List.length_append,List.length_take,Nat.min_eq_left hp]
    omega
  have hcl : (carry.take xs.length).length+1=dst.length := by
    simp only [List.length_take,Nat.min_eq_left hc]
    omega
  have n := KnownLastCarry.program_counts (xs++pad.take 1) dst (carry.take xs.length) control hl hcl
  have o := addInPlace_counts (xs++pad.take 1) dst (carry.take xs.length) control hl hcl
  have side := KnownLastCarry.program_resources (xs++pad.take 1) dst (carry.take xs.length) control hl hcl
  have nt (r : List Wire) := (notRegister_counts r).1
  have nm (r : List Wire) := (notRegister_counts r).2
  refine ⟨?_,?_,?_,?_⟩
  · simp only [rowClear,signedSquareRowClear,toffoliCount_append,
      xorWhenFalse_toffoliCount,nt,n.1,o.1,Nat.zero_add,Nat.add_zero]
    omega
  · simp only [rowClear,signedSquareRowClear,measurementCount_append,
      xorWhenFalse_measurementCount,nm,n.2,o.2]
  · simp only [rowClear,signedSquareRowClear,wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union
      (Finset.Subset.refl _) (Finset.union_subset_union side.1 (Finset.Subset.refl _)))
  · simp only [rowClear,signedSquareRowClear,Challenge.gateSlots_append]
    have le := side.2
    omega

theorem rowClear_physical (control : Wire) (xs dst pad carry : List Wire)
    (hn : (control::xs++dst++pad++carry).Nodup)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (old : GatePhysical (signedSquareRowClear control xs dst pad carry)) :
    GatePhysical (rowClear control xs dst pad carry) := by
  have hl : (xs++pad.take 1).length=dst.length := by
    simp only [List.length_append,List.length_take,Nat.min_eq_left hp]
    omega
  have hcl : (carry.take xs.length).length+1=dst.length := by
    simp only [List.length_take,Nat.min_eq_left hc]
    omega
  have nd : (control::(xs++pad.take 1)++dst++carry.take xs.length).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have p := (List.take_sublist 1 pad).count_le q
    have c := (List.take_sublist xs.length carry).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have receiver := KnownLastCarry.program_physical (xs++pad.take 1) dst (carry.take xs.length) control nd hl hcl
  simp only [rowClear,signedSquareRowClear,gatePhysical_append] at old ⊢
  tauto

theorem rowClear_on_image_general (control top : Wire) (xs low pad carry : List Wire)
    (hn : (control::xs++(low++[top])++pad++carry).Nodup)
    (hl : low.length=xs.length) (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (s : State) (topZero : s.basis top=false)
    (work : regValue (pad++carry) s.basis=0) (forward backward : List Bool) :
    run (rowClear control xs (low++[top]) pad carry) backward
      (run (signedSquareRow control xs (low++[top]) pad carry) forward s)=s := by
  obtain ⟨p,ps,rfl⟩ : ∃p ps,pad=p::ps := by
    match pad,hp with
    | p::ps,_ => exact ⟨p,ps,rfl⟩
    | [],h => simp at h
  let cy := carry.take xs.length
  have cylen : cy.length=xs.length := by
    simp only [cy,List.length_take,Nat.min_eq_left hc]
  have takeC : cy.take xs.length=cy := by rw [←cylen];exact List.take_length
  have nd : (control::xs++(low++[top])++[p]++cy).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have le := (List.take_sublist xs.length carry).count_le q
    simp only [cy,List.count_cons,List.count_append,List.count_nil] at h le ⊢
    omega
  have localWork : regValue ([p]++cy) s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    apply (regValue_zero _ _).mp work q
    rcases List.mem_append.mp hq with first | second
    · have eq : q=p := by simpa using first
      subst q
      exact List.mem_append_left carry (by simp : p∈p::ps)
    · exact List.mem_append_right (p::ps) (List.mem_of_mem_take second)
  have front : signedSquareRow control xs (low++[top]) (p::ps) carry=
      signedSquareRow control xs (low++[top]) [p] cy := by
    simp only [signedSquareRow,takeC,List.take_succ_cons,List.take_zero]
    rfl
  have back : rowClear control xs (low++[top]) (p::ps) carry=
      rowClear control xs (low++[top]) [p] cy := by
    simp only [rowClear,takeC,List.take_succ_cons,List.take_zero]
    rfl
  rw [back,front]
  exact rowClear_on_image control top p xs low cy nd hl cylen s topZero localWork forward backward

theorem row_value_bound (dst : List Wire) (n : Nat) (hn : 1≤n)
    (hd : dst.length=2*n) (s : BasisState)
    (hhi : regValue (dst.drop n) s=0) :
    regValue ((dst.drop 1).take n) s<2^(n-1) := by
  have cap : n≤dst.length := by omega
  have capDrop : n≤(dst.drop 1).length := by simp only [List.length_drop];omega
  have split := regValue_append (dst.take n) (dst.drop n) s
  rw [List.take_append_drop,hhi,Nat.mul_zero,Nat.add_zero] at split
  have b := regValue_lt (dst.take n) s
  rw [List.length_take,Nat.min_eq_left cap] at b
  have full : regValue dst s<2^n := by omega
  have pow : 2^n=2^(n-1)*2 := by
    conv_lhs => rw [show n=(n-1)+1 by omega,Nat.pow_succ]
  have small : regValue dst s/2<2^(n-1) := by omega
  rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ capDrop,
    CuccaroStreamedSquareWideLayout.regValue_drop_div dst 1 (by omega)]
  exact (Nat.mod_le _ _).trans_lt small

theorem top_zero_of_bound (low : List Wire) (top : Wire) (s : BasisState)
    (bound : regValue (low++[top]) s<2^low.length) : s top=false := by
  cases h : s top with
  | false => rfl
  | true =>
    rw [regValue_append] at bound
    have one : regValue [top] s=1 := by simp [regValue,h]
    rw [one,Nat.mul_one] at bound
    omega

theorem split_last (r : List Wire) (h : r≠[]) : ∃ low top,r=low++[top] := by
  induction r with
  | nil => exact False.elim (h rfl)
  | cons a r ih =>
    cases r with
    | nil => exact ⟨[],a,rfl⟩
    | cons b r =>
      obtain ⟨low,top,eq⟩ := ih (by simp)
      exact ⟨a::low,top,by rw [eq];rfl⟩

theorem rowClear_on_image_of_bound (control : Wire) (xs dst pad carry : List Wire)
    (hn : (control::xs++dst++pad++carry).Nodup)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (s : State) (bound : regValue dst s.basis<2^xs.length)
    (work : regValue (pad++carry) s.basis=0) (forward backward : List Bool) :
    run (rowClear control xs dst pad carry) backward
      (run (signedSquareRow control xs dst pad carry) forward s)=s := by
  have nonempty : dst≠[] := by intro eq;simp [eq] at hd
  obtain ⟨low,top,rfl⟩ := split_last dst nonempty
  have len : low.length=xs.length := by simpa using hd
  exact rowClear_on_image_general control top xs low pad carry hn len hp hc s
    (top_zero_of_bound low top s.basis (by simpa only [len] using bound)) work forward backward

end ECDSAAdd.Entrant.KnownLastRow
#print axioms ECDSAAdd.Entrant.KnownLastRow.signedRow_restore
#print axioms ECDSAAdd.Entrant.KnownLastRow.post_recovers_top

#print axioms ECDSAAdd.Entrant.KnownLastRow.adder_restore_of_top

#print axioms ECDSAAdd.Entrant.KnownLastRow.rowClear_on_image

#print axioms ECDSAAdd.Entrant.KnownLastRow.rowClear_resources

#print axioms ECDSAAdd.Entrant.KnownLastRow.rowClear_physical

#print axioms ECDSAAdd.Entrant.KnownLastRow.rowClear_on_image_general

#print axioms ECDSAAdd.Entrant.KnownLastRow.row_value_bound

#print axioms ECDSAAdd.Entrant.KnownLastRow.rowClear_on_image_of_bound
end


-- Carry host component: ParkCarryGeometryDevelop3
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

def restWires (L : CuccaroStreamedSquareWideLayout) : List Wire :=
  L.core.y++L.core.out++L.core.product++L.core.pad++L.core.work++L.overflowPad++
    [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]

theorem sumCarry_away (L : CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
    L.core.sumCarry∉restWires L := by
  intro hm
  have pos:=List.count_pos_iff.mpr hm
  have nd:=List.nodup_iff_count_le_one.mp hn L.core.sumCarry
  simp only [restWires,CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at pos nd
  simp only [beq_self_eq_true,if_true] at nd
  omega

theorem sumCarry_off_regs (L : CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
    L.core.sumCarry∉L.core.out ∧ L.core.sumCarry∉eReg L ∧ L.core.sumCarry∉accReg L := by
  have off:=sumCarry_away L hn
  have out:L.core.sumCarry∉L.core.out := by intro h;apply off;simp [restWires,h]
  have product:L.core.sumCarry∉L.core.product := by intro h;apply off;simp [restWires,h]
  have work:L.core.sumCarry∉L.core.work := by intro h;apply off;simp [restWires,h]
  refine ⟨out,?_,?_⟩
  · intro h;exact product (eReg_product L _ h)
  · intro h;exact work (List.mem_of_mem_take h)

theorem reg_update_off (xs : List Wire) (s : BasisState) (q : Wire) (v : Bool) (hq:q∉xs) :
    regValue xs (writeBit s q v)=regValue xs s := by
  apply regValue_congr
  intro x hx
  have hn:x≠q := by intro h;exact hq (h ▸ hx)
  simp [writeBit,Function.update,hn]

def program (a q : Wire) : Program := [.CX a q,.CX q a]

theorem program_correct (a q : Wire) (ha:a≠q) (s : State) (m : List Bool) (hq:s.basis q=false) :
    run (program a q) m s=⟨s.phase,writeBit (writeBit s.basis q (s.basis a)) a false⟩ := by
  simp only [program,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw:w=a
  · subst w;simp [writeBit,Function.update,ha,hq]
  · by_cases hwq:w=q
    · subst w;simp [writeBit,Function.update,Ne.symm ha,hq]
    · simp [writeBit,Function.update,hw,hwq]

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: ParkCarryBaseDevelop2
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem base_clean (L : CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup)
    (base : BasisState) (hc:L.PairClean base) (v : Bool) :
    L.PairClean (writeBit base L.core.sumCarry v) := by
  have away:=sumCarry_away L hn
  have off (xs : List Wire) (sub:∀q∈xs,q∈restWires L) : L.core.sumCarry∉xs :=
    fun h=>away (sub _ h)
  have ne (x : Wire) (hx:x∈restWires L) : x≠L.core.sumCarry := by
    intro h;apply away;simpa [h] using hx
  constructor
  · rw [reg_update_off _ _ _ _ (off L.foldPad (by intro q h;simp only [foldPad,List.mem_append] at h;rcases h with h|h <;> simp [restWires,h]))]
    exact hc.pad
  · rw [reg_update_off _ _ _ _ (off L.core.work (by intro q h;simp [restWires,h]))]
    exact hc.work
  · simpa [writeBit,Function.update,ne L.core.productHigh (by simp [restWires])] using hc.productHigh
  · simpa [writeBit,Function.update,ne L.core.outHigh (by simp [restWires])] using hc.outHigh
  · simpa [writeBit,Function.update,ne L.core.workHigh (by simp [restWires])] using hc.workHigh
  · simpa [writeBit,Function.update,ne L.core.cin (by simp [restWires])] using hc.cin
  · simpa [writeBit,Function.update,ne L.core.normFlag (by simp [restWires])] using hc.normFlag
  · simpa [writeBit,Function.update,ne L.core.modFlag (by simp [restWires])] using hc.modFlag

theorem bstate_update (L : CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup)
    (base s : BasisState) (O E A : Nat) (v : Bool) (hs:BState L base O E A s) :
    BState L (writeBit base L.core.sumCarry v) O E A (writeBit s L.core.sumCarry v) := by
  obtain ⟨o,e,a⟩:=sumCarry_off_regs L hn
  refine ⟨?_,?_,?_,?_⟩
  · rw [reg_update_off _ _ _ _ o];exact hs.1
  · rw [reg_update_off _ _ _ _ e];exact hs.2.1
  · rw [reg_update_off _ _ _ _ a];exact hs.2.2.1
  · intro q qo qe qa
    by_cases hq:q=L.core.sumCarry
    · subst q;simp [writeBit]
    · simpa [writeBit,Function.update,hq] using hs.2.2.2 q qo qe qa

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: ParkCarryStepDevelop4
section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold KnownTopAdd

theorem park_step (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (base : BasisState) (hb:base L.core.sumCarry=false) (O E A : Nat) (hE:E<2^128) (kap : Bool) :
    Triple (BState L base O (E+2^128*kap.toNat) A) (program (eU L) L.core.sumCarry)
      (BState L (writeBit base L.core.sumCarry kap) O E A) := by
  intro s m h
  obtain ⟨qo,qe,qa⟩:=sumCarry_off_regs L hn
  have e1: eReg L=eRlow L++[eU L,eV L] := (eShape L hw).1
  have um:eU L∈eReg L := by rw [e1];simp
  have vm:eV L∈eReg L := by rw [e1];simp
  have uq:eU L≠L.core.sumCarry := by intro he;exact qe (he ▸ um)
  have vq:eV L≠L.core.sumCarry := by intro he;exact qe (he ▸ vm)
  have sq:s.basis L.core.sumCarry=false := (h.2.2.2 _ qo qe qa).trans hb
  have rl:(eRlow L).length=128 := by simp [eRlow,hw.core.product]
  have hv:=h.2.1
  rw [e1,reg_snoc2,rl] at hv
  have low:=regValue_lt (eRlow L) s.basis
  rw [rl] at low
  have key:s.basis (eU L)=kap ∧ s.basis (eV L)=false ∧ regValue (eRlow L) s.basis=E := by
    cases kap <;> cases su:s.basis (eU L) <;> cases sv:s.basis (eV L) <;>
      simp only [su,sv,Bool.toNat_false,Bool.toNat_true,Bool.false_eq_true,if_false,if_true,
        Nat.mul_zero,Nat.mul_one,Nat.add_zero] at hv <;>
      first | omega | exact ⟨rfl,rfl,by omega⟩
  obtain ⟨su,sv,sl⟩:=key
  have nd:=eK_nodup L hw hn 0 (by omega)
  have uoff:eU L∉eRlow L := by
    intro he
    have cn:=List.nodup_iff_count_le_one.mp nd (eU L)
    have pos:=List.count_pos_iff.mpr he
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at cn
    omega
  have vu:eV L≠eU L := by
    intro he
    have cn:=List.nodup_iff_count_le_one.mp nd (eU L)
    simp only [List.count_cons,List.count_append,he,beq_self_eq_true,if_true] at cn
    omega
  have qoff:L.core.sumCarry∉eRlow L := by intro he;exact qe (by rw [e1];simp [he])
  have uo:eU L∉L.core.out := (eU_away L hw hn).2.2
  have ua:eU L∉accReg L := by intro he;exact (eU_away L hw hn).2.1 (List.mem_of_mem_take he)
  rw [program_correct (eU L) L.core.sumCarry uq s m sq,su]
  let R:=writeBit (writeBit s.basis L.core.sumCarry kap) (eU L) false
  change s.phase=s.phase ∧ BState L (writeBit base L.core.sumCarry kap) O E A R
  refine ⟨rfl,?_,?_,?_,?_⟩
  · rw [show regValue L.core.out R=regValue L.core.out s.basis by
      dsimp [R];rw [reg_update_off _ _ _ _ uo,reg_update_off _ _ _ _ qo]]
    exact h.1
  · have rlow:regValue (eRlow L) R=E := by
      dsimp [R];rw [reg_update_off _ _ _ _ uoff,reg_update_off _ _ _ _ qoff];exact sl
    rw [e1,reg_snoc2,rl,rlow]
    have ru:R (eU L)=false := by simp [R,writeBit]
    have rv:R (eV L)=false := by simp [R,writeBit,Function.update,vu,vq,sv]
    simp [ru,rv]
  · rw [show regValue (accReg L) R=regValue (accReg L) s.basis by
      dsimp [R];rw [reg_update_off _ _ _ _ ua,reg_update_off _ _ _ _ qa]]
    exact h.2.2.1
  · intro x xo xe xa
    by_cases xq:x=L.core.sumCarry
    · subst x;simp [R,writeBit,Function.update,Ne.symm uq]
    · have xu:x≠eU L := by intro he;exact xe (he ▸ um)
      simpa [R,writeBit,Function.update,xq,xu] using h.2.2.2 x xo xe xa

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: KnownSecondTopDevelop3
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.KnownSecondTopDevelop
open Arithmetic Instr KnownSecondCarryDevelop

def addTop (expected : Bool) (x y cs : List Wire) (cin t : Wire) : Program :=
  match x,y,cs with
  | a::a'::as,b::b'::bs,c::cs =>
    head expected a' b' c ++ KnownTopAdd.addTop (a'::as) (b'::bs) cs c t ++
      eraseCarry a b cin c ++ [CX a b,CX cin b]
  | _,_,_ => KnownTopAdd.addTop x y cs cin t

theorem addTop_eq (expected : Bool) (a a' b b' c cin t : Wire)
    (as bs cs : List Wire) (hn:[a,b,cin,c].Nodup) (hb:b'≠c)
    (s : State) (m : List Bool)
    (ready:sumBit (s.basis a') (s.basis b') (carryBit (s.basis a) (s.basis b) (s.basis cin))=expected) :
    run (addTop expected (a::a'::as) (b::b'::bs) (c::cs) cin t) m s =
      run (KnownTopAdd.addTop (a::a'::as) (b::b'::bs) (c::cs) cin t) m s := by
  simp only [addTop,KnownTopAdd.addTop,List.append_assoc]
  rw [run_append (head expected a' b' c),run_append (majority a b cin c)]
  have hm : measurementCount (head expected a' b' c)=measurementCount (majority a b cin c) := by
    simp [head_counts,majority,measurementCount]
  rw [hm,head_eq_majority expected a b a' b' cin c hn hb _ _ ready]

theorem addTop_counts (expected : Bool) (a a' b b' c cin t : Wire)
    (as bs cs : List Wire) :
    toffoliCount (addTop expected (a::a'::as) (b::b'::bs) (c::cs) cin t)+1 =
      toffoliCount (KnownTopAdd.addTop (a::a'::as) (b::b'::bs) (c::cs) cin t) ∧
    measurementCount (addTop expected (a::a'::as) (b::b'::bs) (c::cs) cin t) =
      measurementCount (KnownTopAdd.addTop (a::a'::as) (b::b'::bs) (c::cs) cin t) := by
  simp only [addTop,KnownTopAdd.addTop,toffoliCount_append,measurementCount_append]
  have h:=head_counts expected a' b' c
  simp [h,majority,toffoliCount,measurementCount]
  omega

end ECDSAAdd.Entrant.KnownSecondTopDevelop
end


-- Carry host component: HostedSquareSubListsDevelop
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.HostedSquareSubDevelop
open Arithmetic Instr

def oldSub (x y cs : List Wire) (cin top : Wire) : Program :=
  notRegister y ++ KnownTopAdd.addTop x y cs cin top ++ notRegister y

def sub (x y cs : List Wire) (cin top : Wire) : Program :=
  notRegister y ++ KnownSecondTopDevelop.addTop true x y cs cin top ++ notRegister y

theorem complement32 (a u : Nat) (hbit:a/2%2=0) :
    (u+(2^32-1-(a+u)%2^32))/2%2=1 := by
  have h:(a+u)%2^32<2^32 := Nat.mod_lt _ (by decide)
  omega

theorem square_second32 (M : Nat) : (M^2%2^32)/2%2=0 := by
  have h:M%4=0 ∨ M%4=1 ∨ M%4=2 ∨ M%4=3 := by omega
  have h4:M^2%4=0 ∨ M^2%4=1 := by
    rcases h with h|h|h|h <;> simp [Nat.pow_mod,h]
  have mod4:(M^2%2^32)%4=M^2%4 := Nat.mod_mod_of_dvd _ (by decide)
  rcases h4 with h4|h4 <;> omega

theorem sub_eq (a a' b b' c cin top : Wire) (as bs cs : List Wire)
    (hn:(cin::((a::a'::as)++(b::b'::bs)++(c::cs))).Nodup)
    (hl:(b::b'::bs).length=32) (v u : Nat) (hbit:v/2%2=0)
    (s : State) (m : List Bool) (hc:s.basis cin=false)
    (hx:regValue (a::a'::as) s.basis=u)
    (hy:regValue (b::b'::bs) s.basis=(v+u)%2^32) :
    run (sub (a::a'::as) (b::b'::bs) (c::cs) cin top) m s =
      run (oldSub (a::a'::as) (b::b'::bs) (c::cs) cin top) m s := by
  have cnt:=fun q=>List.nodup_iff_count_le_one.mp hn q
  have yn:(b::b'::bs).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have h:=cnt q
    simp only [List.count_cons,List.count_append,beq_iff_eq] at h ⊢
    omega
  have off (q : Wire) (hq:q=cin ∨ q∈a::a'::as ∨ q=c) : q∉b::b'::bs := by
    intro hy
    have h:=cnt q
    have pos:=List.count_pos_iff.mpr hy
    simp only [List.count_cons,beq_iff_eq] at pos
    simp only [List.count_cons,List.count_append,beq_iff_eq] at h
    rcases hq with rfl|hx|rfl
    · simp only [if_true] at h pos
      omega
    · have x:=List.count_pos_iff.mpr hx
      simp only [List.count_cons,beq_iff_eq] at x
      omega
    · simp only [if_true] at h pos
      omega
  have small:[a,b,cin,c].Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have h:=cnt q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have bc:b'≠c := by intro he;apply off c (Or.inr (Or.inr rfl));simp [←he]
  simp only [sub,oldSub,List.append_assoc]
  rw [run_append (notRegister (b::b'::bs)),run_append (notRegister (b::b'::bs))]
  rw [run_append (KnownSecondTopDevelop.addTop true (a::a'::as) (b::b'::bs) (c::cs) cin top),
    run_append (KnownTopAdd.addTop (a::a'::as) (b::b'::bs) (c::cs) cin top)]
  have cm:measurementCount (KnownSecondTopDevelop.addTop true (a::a'::as) (b::b'::bs) (c::cs) cin top)=
      measurementCount (KnownTopAdd.addTop (a::a'::as) (b::b'::bs) (c::cs) cin top) :=
    (KnownSecondTopDevelop.addTop_counts true a a' b b' c cin top as bs cs).2
  rw [cm]
  apply congrArg (fun st=>run (notRegister (b::b'::bs)) _ st)
  apply KnownSecondTopDevelop.addTop_eq true a a' b b' c cin top as bs cs small bc
  apply KnownSecondValueDevelop.ready_true a a' b b' cin as bs
  · rw [notRegister_correct _ yn]
    simpa [off cin (Or.inl rfl)] using hc
  · rw [notRegister_correct _ yn]
    have xv:regValue (a::a'::as) (fun w=>if w∈b::b'::bs then !s.basis w else s.basis w)=u := by
      rw [←hx]
      apply regValue_congr
      intro q hq
      simp [off q (Or.inr (Or.inl hq))]
    have yv:regValue (b::b'::bs) (fun w=>if w∈b::b'::bs then !s.basis w else s.basis w)=2^32-1-(v+u)%2^32 := by
      rw [regValue_congr (b::b'::bs) _ (fun w=> !s.basis w) (by intro q hq;simp [hq]),regValue_complement,hl,hy]
    rw [xv,yv]
    exact complement32 v u hbit

end ECDSAAdd.Entrant.HostedSquareSubDevelop

namespace ECDSAAdd.Entrant.HostedSquareSubDevelop
open Arithmetic

theorem shape (x : List Wire) (h:2≤x.length) : ∃a b xs,x=a::b::xs := by
  cases x with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs => exact ⟨a,b,xs,rfl⟩

theorem lists_eq (x y cs : List Wire) (cin top : Wire)
    (hn:(cin::x++y++cs).Nodup) (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31)
    (v u : Nat) (hbit:v/2%2=0) (s : State) (m : List Bool) (hc:s.basis cin=false)
    (hx:regValue x s.basis=u) (hy:regValue y s.basis=(v+u)%2^32) :
    run (sub x y cs cin top) m s=run (oldSub x y cs cin top) m s := by
  obtain ⟨a,a',as,rfl⟩:=shape x (by omega)
  obtain ⟨b,b',bs,rfl⟩:=shape y (by omega)
  cases cs with
  | nil => simp at lc
  | cons c cs => exact sub_eq a a' b b' c cin top as bs cs hn ly v u hbit s m hc hx hy

end ECDSAAdd.Entrant.HostedSquareSubDevelop
end


-- Carry host component: HostedRestoreDevelop2
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic KnownTopAdd ControlLoan1589BFFold

theorem host_restore (x y cs : List Wire) (cin q v z k : Wire)
    (hn:(cin::q::v::z::k::(x++y++cs)).Nodup)
    (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31)
    (a u : Nat) (ha:a<2^32) (s : State) (m : List Bool)
    (hx:regValue x s.basis=u) (hy:regValue (y++[q]) s.basis=a+u)
    (hk:s.basis k=false) (hz:s.basis z=false) (hcin:s.basis cin=false)
    (hcs:regValue cs s.basis=0) (hv:s.basis v=false) :
    let t:=run (subKnown x y cs cin q k) m s
    t.phase=s.phase ∧ regValue y t.basis=a ∧ t.basis q=false ∧ t.basis v=false ∧
    ∀ r, r∉y → r≠q → r≠v → t.basis r=s.basis r := by
  obtain ⟨phase,value,frame⟩:=subKnown_spec x y cs cin z q v k hn (by omega) (by omega) (by omega)
    s m hk hz hcin hcs hv (by rw [hx,hy];omega) (by rw [hx,hy,ly];omega)
  have initial:regValue (y++[q,v]) s.basis=a+u := by
    rw [reg_snoc2,ly]
    have yy:=hy
    rw [reg_snoc,ly] at yy
    simp only [hv,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero]
    exact yy
  rw [initial,ly,hx] at value
  have arith:(a+u+2^(32+2)-u)%2^(32+2)=a := by omega
  rw [arith,reg_snoc2,ly] at value
  have low:=regValue_lt y (run (subKnown x y cs cin q k) m s).basis
  rw [ly] at low
  have qs:(run (subKnown x y cs cin q k) m s).basis q=false := by
    cases eq:(run (subKnown x y cs cin q k) m s).basis q
    · rfl
    · simp only [eq,if_true] at value;omega
  have vs:(run (subKnown x y cs cin q k) m s).basis v=false := by
    cases eq:(run (subKnown x y cs cin q k) m s).basis v
    · rfl
    · simp only [eq,if_true] at value;omega
  refine ⟨phase,?_,qs,vs,frame⟩
  simp only [qs,vs,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at value
  exact value

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: HostedRestoreEqDevelop4
section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic KnownTopAdd ControlLoan1589BFFold

theorem host_eq_mod (x y cs : List Wire) (cin q v z k : Wire)
    (hn:(cin::q::v::z::k::(x++y++cs)).Nodup)
    (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31)
    (a u : Nat) (ha:a<2^32) (s : State) (m : List Bool)
    (hx:regValue x s.basis=u) (hy:regValue (y++[q]) s.basis=a+u)
    (hk:s.basis k=false) (hz:s.basis z=false) (hcin:s.basis cin=false)
    (hcs:regValue cs s.basis=0) (hv:s.basis v=false) :
    run (subKnown x y cs cin q k) m s=
      ⟨s.phase,writeBit (run (subInPlace x y cs cin) m s).basis q false⟩ := by
  obtain ⟨hp,hy',hq',hv',hf⟩:=host_restore x y cs cin q v z k hn lx ly lc a u ha s m hx hy hk hz hcin hcs hv
  have cnt:=fun w=>List.nodup_iff_count_le_one.mp hn w
  have nd:(cin::x++y++cs).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro w
    have h:=cnt w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have old:=subInPlace_spec x y cs cin nd (by omega) (by omega) u (regValue y s.basis) s m
    ⟨⟨⟨hx,rfl⟩,hcin⟩,hcs⟩
  have target:(regValue y s.basis+2^y.length-u)%2^y.length=a := by
    rw [ly]
    rw [reg_snoc,ly] at hy
    cases bit:s.basis q <;> simp only [bit,Bool.false_eq_true,if_false,if_true] at hy <;> omega
  have oldY:regValue y (run (subInPlace x y cs cin) m s).basis=a := old.2.1.1.2.trans target
  have frame:∀w,w∉y→(run (subInPlace x y cs cin) m s).basis w=s.basis w := by
    intro w wy
    by_cases wx:w∈x
    · exact (regValue_eq_iff _ _ _).mp (old.2.1.1.1.trans hx.symm) w wx
    by_cases wc:w∈cs
    · exact (regValue_eq_iff _ _ _).mp (old.2.2.trans hcs.symm) w wc
    by_cases wi:w=cin
    · subst w;exact old.2.1.2.trans hcin.symm
    apply run_preserves_outside
    rw [subInPlace_wires _ _ _ _ (by omega) (by omega)]
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,not_or]
    exact ⟨wi,⟨wx,wy⟩,wc⟩
  apply State.extensionality _ (⟨s.phase,writeBit (run (subInPlace x y cs cin) m s).basis q false⟩ : State) hp
  funext w
  change (run (subKnown x y cs cin q k) m s).basis w=writeBit (run (subInPlace x y cs cin) m s).basis q false w
  by_cases wq:w=q
  · subst w;simp [hq',writeBit]
  have update:writeBit (run (subInPlace x y cs cin) m s).basis q false w=
      (run (subInPlace x y cs cin) m s).basis w := by simp [writeBit,Function.update,wq]
  rw [update]
  by_cases wy:w∈y
  · exact (regValue_eq_iff _ _ _).mp (hy'.trans oldY.symm) w wy
  by_cases wv:w=v
  · subst w;exact hv'.trans ((frame v wy).trans hv).symm
  exact (hf w wy wq wv).trans (frame w wy).symm

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: HostedSquareRestoreEqDevelop2
section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic KnownTopAdd ControlLoan1589BFFold

def hostSquare (x y cs : List Wire) (cin q k : Wire) : Program :=
  Instr.measureX k [] [] :: (notRegister y ++
    (KnownSecondTopDevelop.addTop true x y cs cin q ++ notRegister y))

theorem hostSquare_eq (x y cs : List Wire) (cin q v z k : Wire)
    (hn:(cin::q::v::z::k::(x++y++cs)).Nodup)
    (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31)
    (a u : Nat) (ha:a<2^32) (hbit:a/2%2=0) (s : State) (m : List Bool)
    (hx:regValue x s.basis=u) (hy:regValue (y++[q]) s.basis=a+u)
    (hk:s.basis k=false) (hz:s.basis z=false) (hcin:s.basis cin=false)
    (hcs:regValue cs s.basis=0) (hv:s.basis v=false) :
    run (hostSquare x y cs cin q k) m s=
      ⟨s.phase,writeBit (run (KnownSecondSubDevelop.sub x y cs cin) m s).basis q false⟩ := by
  have nd:(cin::x++y++cs).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro w
    have h:=List.nodup_iff_count_le_one.mp hn w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have low:=regValue_lt y s.basis
  rw [ly] at low
  have yy:regValue y s.basis=(a+u)%2^32 := by
    rw [reg_snoc,ly] at hy
    cases b:s.basis q <;> simp only [b,Bool.false_eq_true,if_false,if_true] at hy <;> omega
  have bare:=HostedSquareSubDevelop.lists_eq x y cs cin q nd lx ly lc a u hbit s m.tail hcin hx yy
  have headEq:run (hostSquare x y cs cin q k) m s=run (subKnown x y cs cin q k) m s := by
    simp only [hostSquare,subKnown]
    rw [noop_run k _ m s hk,noop_run k _ m s hk]
    simpa only [HostedSquareSubDevelop.sub,HostedSquareSubDevelop.oldSub,List.append_assoc] using bare
  have whole:=host_eq_mod x y cs cin q v z k hn lx ly lc a u ha s m hx hy hk hz hcin hcs hv
  have modEq:=KnownSecondSubDevelop.lists_eq x y cs cin nd lx ly lc a u hbit s m hcin hx yy
  rw [←modEq] at whole
  exact headEq.trans whole

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: HostedRestoreGeometryDevelop2
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem host_nodup (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    (L.core.cin::L.core.sumCarry::eV L::eZ0 L::eKw L::
      (mU L++eLo L++(eBank L).take 31)).Nodup := by
  let rest:=L.core.cin::eV L::eZ0 L::eKw L::(mU L++eLo L++(eBank L).take 31)
  have rn:rest.Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro w
    have nd:=List.nodup_iff_count_le_one.mp (eK_nodup L hw hn 31 (by omega)) w
    have mx:(mU L).count w≤(hiReg L).count w := (List.drop_sublist 96 _).count_le w
    have my:(eLo L).count w≤(eRlow L).count w := (List.take_sublist 32 _).count_le w
    simp only [rest,List.count_cons,List.count_append] at nd ⊢
    omega
  have product {w : Wire} (h:w∈L.core.product) : w∈restWires L := by simp [restWires,h]
  have pad {w : Wire} (h:w∈L.foldPad) : w∈restWires L := by
    simp only [foldPad,List.mem_append] at h
    rcases h with h|h <;> simp [restWires,h]
  have qo:L.core.sumCarry∉rest := by
    intro hm
    apply sumCarry_away L hn
    simp only [rest,List.mem_cons,List.mem_append,or_assoc] at hm
    rcases hm with h|h|h|h|h|h|h
    · rw [h];simp [restWires]
    · rw [h];exact product (eReg_product L _ (eK_mem L hw).2.2.1)
    · rw [h];exact pad (List.mem_of_mem_drop (List.mem_of_mem_take (eZ0_eZ L hw)))
    · rw [h];exact pad (List.mem_of_mem_take (eK_mem L hw).1)
    · exact product (List.mem_of_mem_take (List.mem_of_mem_drop (mU_hi L _ h)))
    · exact product (eReg_product L _ (eLo_eReg L hw _ h))
    · exact pad (List.mem_of_mem_take (List.mem_of_mem_take h))
  have nn:(L.core.sumCarry::rest).Nodup := List.nodup_cons.mpr ⟨qo,rn⟩
  apply List.nodup_iff_count_le_one.mpr
  intro w
  have cn:=List.nodup_iff_count_le_one.mp nn w
  simp only [rest,List.count_cons] at cn ⊢
  omega

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: HostedRestoreStepDevelop2
section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold KnownTopAdd

def restore (L : CuccaroStreamedSquareWideLayout) : Program :=
  hostSquare (mU L) (eLo L) ((eBank L).take 31) L.core.cin L.core.sumCarry (eKw L)

theorem restore_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O A H l a : Nat) (hH : H<2^96) (hl : l<2^32)
    (ha:a<2^32) (hbit:a/2%2=0)
    (total:l+2^32*(base L.core.sumCarry).toNat=a+regValue (hiReg L) base/2^96) :
    Triple (BState L base O (2^32*H+l) A) (restore L)
      (BState L (writeBit base L.core.sumCarry false) O (2^32*H+a) A) := by
  intro s m h
  obtain ⟨f1, f2, f3, f4, f5⟩ := eK_facts L hw hn base hc O _ A s.basis h
  let u := regValue (hiReg L) base / 2^96
  have hu : regValue (mU L) s.basis = u := by rw [hi96 L hw, f5]
  have hv := eReg_split L hw s.basis
  rw [h.2.1] at hv
  have hl0 := eLo_lt L hw s.basis
  have hm := eMid_lt L hw s.basis
  have key : regValue (eLo L) s.basis = l ∧ regValue (eMid L) s.basis = H ∧
      s.basis (eU L) = false ∧ s.basis (eV L) = false := by
    cases e1 : s.basis (eU L) <;> cases e2 : s.basis (eV L) <;>
      simp only [e1, e2, Bool.false_eq_true, if_false, if_true] at hv <;>
      first | omega | (exact ⟨by omega, by omega, rfl, rfl⟩)
  obtain ⟨k1, k2, k3, k4⟩ := key
  obtain ⟨qo,qe,qa⟩:=sumCarry_off_regs L hn
  have sq:s.basis L.core.sumCarry=base L.core.sumCarry := h.2.2.2 _ qo qe qa
  have target:regValue (eLo L++[L.core.sumCarry]) s.basis=a+u := by
    rw [reg_snoc,eLo_length L hw,k1,sq]
    change l+2^32*(base L.core.sumCarry).toNat=a+u at total
    cases cap:base L.core.sumCarry <;> simpa [cap] using total
  have hu32:u<2^32 := by
    rw [←hu]
    have z:=regValue_lt (mU L) s.basis
    rwa [mU_length L hw] at z
  have diff:(l+2^32-u)%2^32=a := by
    change l+2^32*(base L.core.sumCarry).toNat=a+u at total
    cases cap:base L.core.sumCarry <;> simp only [cap,Bool.toNat_false,Bool.toNat_true] at total <;> omega
  have eq:=hostSquare_eq (mU L) (eLo L) ((eBank L).take 31) L.core.cin L.core.sumCarry (eV L) (eZ0 L) (eKw L)
    (host_nodup L hw hn) (mU_length L hw) (eLo_length L hw) (eBank_take_length L hw 31 (by omega))
    a u ha hbit s m hu target f2 f1 f3 (f4 31) k4
  change run (restore L) m s=⟨s.phase,writeBit (run (eSubLoSq L) m s).basis L.core.sumCarry false⟩ at eq
  have old:=eSubLoSq_step L hw hn base hc O A H l hH hl (by rw [diff];exact hbit) s m h
  change (run (eSubLoSq L) m s).phase=s.phase ∧ BState L base O (2^32*H+(l+2^32-u)%2^32) A
    (run (eSubLoSq L) m s).basis at old
  rw [diff] at old
  have update:=bstate_update L hn base (run (eSubLoSq L) m s).basis O (2^32*H+a) A false old.2
  rw [eq]
  exact ⟨rfl,update⟩

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: ParkCarryBodyDevelop2
section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

def fold (L : CuccaroStreamedSquareWideLayout) : Program :=
  eAddLo L++(wBuild L++((wFwdK L++(wCoreK L++wInvK L))++
    (wUnbuildKnown L++(program (eU L) L.core.sumCarry++eSubK L))))

def rebuild (L : CuccaroStreamedSquareWideLayout) : Program :=
  eAddB L++(restore L++padM L 751)

def body (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(fold L++(eFoldTq L c++rebuild L)))

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: KnownSecondTopResourcesDevelop2
section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.KnownSecondTopDevelop
open Arithmetic Instr KnownSecondCarryDevelop

theorem physical (expected : Bool) (a a' b b' c cin top : Wire) (as bs cs : List Wire)
    (hn:(cin::top::(a::a'::as)++(b::b'::bs)++(c::cs)).Nodup) :
    GatePhysical (addTop expected (a::a'::as) (b::b'::bs) (c::cs) cin top) := by
  have cnt:=fun q=>List.nodup_iff_count_le_one.mp hn q
  have ac:a'≠c := by
    intro he
    have h:=cnt c
    simp only [List.count_cons,List.count_append,he,beq_self_eq_true,if_true] at h
    omega
  have bc:b'≠c := by
    intro he
    have h:=cnt c
    simp only [List.count_cons,List.count_append,he,beq_self_eq_true,if_true] at h
    omega
  have old:=KnownTopAdd.addTop_physical (a::a'::as) (b::b'::bs) (c::cs) cin top hn
  simp only [KnownTopAdd.addTop,gatePhysical_append] at old
  simp only [addTop,gatePhysical_append]
  exact ⟨⟨⟨head_physical expected a' b' c ac bc,old.1.1.2⟩,old.1.2⟩,old.2⟩

theorem support (expected : Bool) (a a' b b' c cin top : Wire) (as bs cs : List Wire) :
    wires (addTop expected (a::a'::as) (b::b'::bs) (c::cs) cin top)⊆
      (cin::top::(a::a'::as)++(b::b'::bs)++(c::cs)).toFinset := by
  have tail:=KnownTopAdd.addTop_wires_sub (a'::as) (b'::bs) cs c top
  intro q hq
  simp only [addTop,wires_append,Finset.mem_union] at hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at tail ⊢
  rcases hq with ((h|h)|h)|h
  · cases expected <;> simp [head,wires,Instr.wires] at h <;> tauto
  · have h':=tail h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h'
    tauto
  · simp [eraseCarry,wires,Instr.wires,correctionWires] at h;tauto
  · simp [wires,Instr.wires] at h;tauto

theorem slots (expected : Bool) (a a' b b' c cin top : Wire) (as bs cs : List Wire) :
    Challenge.gateSlots (addTop expected (a::a'::as) (b::b'::bs) (c::cs) cin top)≤
      Challenge.gateSlots (KnownTopAdd.addTop (a::a'::as) (b::b'::bs) (c::cs) cin top) := by
  cases expected <;> simp [addTop,KnownTopAdd.addTop,head,majority,Challenge.gateSlots,Challenge.instructionSlots] <;> omega

end ECDSAAdd.Entrant.KnownSecondTopDevelop
end


-- Carry host component: HostedSquareResourcesDevelop4
section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic KnownTopAdd

theorem hostSquare_resources (x y cs : List Wire) (cin q k : Wire)
    (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31) :
    toffoliCount (hostSquare x y cs cin q k)=30 ∧
    measurementCount (hostSquare x y cs cin q k)=33 ∧
    wires (hostSquare x y cs cin q k)⊆(cin::q::k::x++y++cs).toFinset ∧
    Challenge.gateSlots (hostSquare x y cs cin q k)≤443 := by
  obtain ⟨a,a',as,rfl⟩:=HostedSquareSubDevelop.shape x (by omega)
  obtain ⟨b,b',bs,rfl⟩:=HostedSquareSubDevelop.shape y (by omega)
  cases cs with
  | nil => simp at lc
  | cons c cs =>
    let xs:=a::a'::as
    let ys:=b::b'::bs
    have sx:xs.length=32 := lx
    have sy:ys.length=32 := ly
    change toffoliCount (hostSquare xs ys (c::cs) cin q k)=30 ∧
      measurementCount (hostSquare xs ys (c::cs) cin q k)=33 ∧
      wires (hostSquare xs ys (c::cs) cin q k)⊆(cin::q::k::xs++ys++(c::cs)).toFinset ∧
      Challenge.gateSlots (hostSquare xs ys (c::cs) cin q k)≤443
    have subCount:=subKnown_counts xs ys (c::cs) cin 0 q k (by omega) (by simp only [List.length_cons] at lc ⊢;omega) (by omega)
    have fullCount:=addInPlace_counts (xs++[0]) (ys++[q]) ((c::cs)++[k]) cin
      (by simp only [List.length_append,List.length_singleton];omega) (by simp only [List.length_append,List.length_cons];simp only [List.length_cons] at lc;omega)
    have n:=notRegister_counts ys
    have headCount:=KnownSecondTopDevelop.addTop_counts true a a' b b' c cin q as bs cs
    change toffoliCount (KnownSecondTopDevelop.addTop true xs ys (c::cs) cin q)+1=toffoliCount (KnownTopAdd.addTop xs ys (c::cs) cin q) ∧
      measurementCount (KnownSecondTopDevelop.addTop true xs ys (c::cs) cin q)=measurementCount (KnownTopAdd.addTop xs ys (c::cs) cin q) at headCount
    have counts:toffoliCount (hostSquare xs ys (c::cs) cin q k)+1=toffoliCount (subKnown xs ys (c::cs) cin q k) ∧
      measurementCount (hostSquare xs ys (c::cs) cin q k)=measurementCount (subKnown xs ys (c::cs) cin q k) := by
      change toffoliCount ([Instr.measureX k [] []]++(notRegister ys++(KnownSecondTopDevelop.addTop true xs ys (c::cs) cin q++notRegister ys)))+1=
        toffoliCount ([Instr.measureX k [] []]++(notRegister ys++(KnownTopAdd.addTop xs ys (c::cs) cin q++notRegister ys))) ∧
        measurementCount ([Instr.measureX k [] []]++(notRegister ys++(KnownSecondTopDevelop.addTop true xs ys (c::cs) cin q++notRegister ys)))=
        measurementCount ([Instr.measureX k [] []]++(notRegister ys++(KnownTopAdd.addTop xs ys (c::cs) cin q++notRegister ys)))
      simp only [toffoliCount_append,measurementCount_append,n.1,n.2]
      have noopCounts:toffoliCount [Instr.measureX k [] []]=0 ∧ measurementCount [Instr.measureX k [] []]=1 := by
        simp [toffoliCount,measurementCount]
      simp only [noopCounts.1,noopCounts.2,Nat.zero_add,Nat.add_zero]
      exact ⟨headCount.1,by omega⟩
    simp only [List.length_append,List.length_singleton,sy] at fullCount
    have bound:=KnownSecondTopDevelop.slots true a a' b b' c cin q as bs cs
    change Challenge.gateSlots (KnownSecondTopDevelop.addTop true xs ys (c::cs) cin q)≤Challenge.gateSlots (KnownTopAdd.addTop xs ys (c::cs) cin q) at bound
    have oldSlots:=KnownTopAdd.addTop_slots_eq xs ys (c::cs) cin q (by omega) (by simp only [List.length_cons] at lc ⊢;omega)
    have slots:Challenge.gateSlots (hostSquare xs ys (c::cs) cin q k)≤443 := by
      change Challenge.gateSlots ([Instr.measureX k [] []]++(notRegister ys++(KnownSecondTopDevelop.addTop true xs ys (c::cs) cin q++notRegister ys)))≤443
      simp only [Challenge.gateSlots_append,Baselines.notRegister_gateSlots,sy]
      have pfxSlots:Challenge.gateSlots [Instr.measureX k [] []]=1 := rfl
      rw [pfxSlots]
      rw [sy] at oldSlots
      omega
    refine ⟨by omega,by omega,?_,slots⟩
    have tail:=KnownSecondTopDevelop.support true a a' b b' c cin q as bs cs
    intro w hw
    change w∈wires ([Instr.measureX k [] []]++(notRegister ys++(KnownSecondTopDevelop.addTop true xs ys (c::cs) cin q++notRegister ys))) at hw
    simp only [wires_append,Finset.mem_union,notRegister_wires,List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢
    rcases hw with h|h|h|h
    · simp [wires,Instr.wires] at h;tauto
    · simp only [xs,ys,List.mem_cons] at h ⊢;tauto
    · have hh:=tail h
      simp only [xs,ys,List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
      tauto
    · simp only [xs,ys,List.mem_cons] at h ⊢;tauto

theorem hostSquare_physical (x y cs : List Wire) (cin q k : Wire)
    (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31)
    (hn:(cin::q::k::x++y++cs).Nodup) : GatePhysical (hostSquare x y cs cin q k) := by
  obtain ⟨a,a',as,rfl⟩:=HostedSquareSubDevelop.shape x (by omega)
  obtain ⟨b,b',bs,rfl⟩:=HostedSquareSubDevelop.shape y (by omega)
  cases cs with
  | nil => simp at lc
  | cons c cs =>
    have nd:(cin::q::(a::a'::as)++(b::b'::bs)++(c::cs)).Nodup := by
      apply List.nodup_iff_count_le_one.mpr
      intro w
      have cnt:=List.nodup_iff_count_le_one.mp hn w
      simp only [List.count_cons,List.count_append] at cnt ⊢
      omega
    have ph:=KnownSecondTopDevelop.physical true a a' b b' c cin q as bs cs nd
    have no:GatePhysical [Instr.measureX k [] []] := by simp [GatePhysical,RecordedQuantum.PhysicalInstr]
    change GatePhysical ([Instr.measureX k [] []]++(notRegister (b::b'::bs)++
      (KnownSecondTopDevelop.addTop true (a::a'::as) (b::b'::bs) (c::cs) cin q++notRegister (b::b'::bs))))
    simp only [gatePhysical_append]
    exact ⟨no,notRegister_physical _,ph,notRegister_physical _⟩

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: ParkCarryRestoreResourcesDevelop2
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem restore_resources (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) :
    toffoliCount (restore L)=30 ∧ measurementCount (restore L)=33 ∧
    wires (restore L)⊆insert L.core.sumCarry (oldE L) ∧ Challenge.gateSlots (restore L)≤443 := by
  have r:=hostSquare_resources (mU L) (eLo L) ((eBank L).take 31) L.core.cin L.core.sumCarry (eKw L)
    (mU_length L hw) (eLo_length L hw) (eBank_take_length L hw 31 (by omega))
  refine ⟨r.1,r.2.1,?_,r.2.2.2⟩
  intro w hw'
  have h:=r.2.2.1 hw'
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h|h|h
  · apply Finset.mem_insert_of_mem
    exact oldE_mem L hw w (Or.inl h)
  · exact Finset.mem_insert.mpr (Or.inl h)
  · apply Finset.mem_insert_of_mem
    apply oldE_mem L hw w
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h ▸ (eK_mem L hw).1)))))
  · apply Finset.mem_insert_of_mem
    exact oldE_mem L hw w (Or.inr (Or.inl (mU_hi L w h)))
  · apply Finset.mem_insert_of_mem
    exact oldE_mem L hw w (Or.inr (Or.inr (Or.inr (Or.inl (eLo_eReg L hw w h)))))
  · apply Finset.mem_insert_of_mem
    exact oldE_mem L hw w (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (bank_take L 31 w h))))))

theorem restore_physical (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    GatePhysical (restore L) := by
  have nd:=host_nodup L hw hn
  have small:(L.core.cin::L.core.sumCarry::eKw L::(mU L++eLo L++(eBank L).take 31)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro w
    have cnt:=List.nodup_iff_count_le_one.mp nd w
    simp only [List.count_cons,List.count_append] at cnt ⊢
    omega
  exact hostSquare_physical _ _ _ _ _ _ (mU_length L hw) (eLo_length L hw) (eBank_take_length L hw 31 (by omega)) small

theorem program_counts (a q : Wire) : toffoliCount (program a q)=0 ∧ measurementCount (program a q)=0 := by
  simp [program,toffoliCount,measurementCount]

theorem program_slots (a q : Wire) : Challenge.gateSlots (program a q)=2 := rfl

theorem program_physical (a q : Wire) (ha:a≠q) : GatePhysical (program a q) := by
  simp [program,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ha,Ne.symm ha]

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: ParkCarryBodyResourcesDevelop
section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem body_counts (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire) :
    toffoliCount (body L c)=4771 ∧ measurementCount (body L c)=5924 := by
  have old:=bBody_countsTq L hw c
  have lc:=lo_counts L hw
  have newRest:=restore_resources L hw
  have oldRest:=eSubLoSq_static L hw
  have newPad:=padM_counts L 751
  have oldPad:=padM_counts L 721
  have pk:=program_counts (eU L) L.core.sumCarry
  simp only [body,fold,rebuild,bBodyTq,wFoldTq,wRestoreT,
    toffoliCount_append,measurementCount_append,newRest.1,newRest.2.1,oldRest.1,oldRest.2.1,
    newPad.1,newPad.2,oldPad.1,oldPad.2,pk.1,pk.2,lc.2.2.1,lc.2.2.2.1] at old ⊢
  constructor <;> omega


theorem body_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (hn : (c::L.wires).Nodup) : GatePhysical (body L c) := by
  have nd := (List.nodup_cons.mp hn).2
  have uq:eU L≠L.core.sumCarry := by
    intro he
    exact (sumCarry_off_regs L nd).2.1 (he ▸ (eK_mem L hw).2.1)
  have hcw := (List.nodup_cons.mp hn).1
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have p1 := measuredFoldQ_physicalTq L hw nd (negP L) sP
  have p2 := measuredFoldQ_physicalTq L hw nd (rot128F L) sR
  have wb := CodexNarrowTail.build8_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_fits L hw nd)
  rw [CodexNarrowTail.build8_eq] at wb
  have wc := QCore.qprog_physicalTq (rotWCore L) SquareReduction.p (rotWCore_nodup L nd)
  have hct : c∉(eReg L).take 129 := fun hm => hcw (by
    have := eReg_product L c (List.mem_of_mem_take hm)
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this])
  have fl : GatePhysical (eFlip L c) := maskedConstant_physical c ((eReg L).take 129) (2^129-1) hct
  have st := eItem_static L hw
  have ac := Q4.accFoldQ4KTq_physical L hw nd (eItem L) st.1 st.2.1 st.2.2.1 st.2.2.2
  have g := mGeo L hw nd
  have heZ : eU L ∉ mZ L := fun hz => (eU_away L hw nd).1 (mZ_pad L _ hz)
  simp only [body,fold,wCoreK,eFoldTq,rebuild,gatePhysical_append]
  exact ⟨p1,p2,⟨eAddLo_physical L hw nd,wb.1,⟨WinArith.tFwdK_physical g (eU L) heZ,⟨kw_physical L hw nd,wc,
    kw_physical L hw nd⟩,WinArith.tInvK_physical g (eU L) heZ⟩,wUnbuildKnown_physical L hw nd,program_physical (eU L) L.core.sumCarry uq,eSubK_physical L hw nd⟩,
    ⟨fl,ac,fl⟩,⟨eAddB_physical L hw nd,restore_physical L hw nd,padM_physical L 751⟩⟩

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: ExtraWireRelationDevelop
section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic

def ExtraLe (q : Wire) (P Q : Program) : Prop :=
  wires P⊆insert q (wires Q) ∧ Challenge.gateSlots P≤Challenge.gateSlots Q

theorem ExtraLe.ofLe (q : Wire) {P Q : Program} (h:QRel.Le P Q) : ExtraLe q P Q := by
  refine ⟨?_,h.2⟩
  intro x hx
  exact Finset.mem_insert_of_mem (h.1 hx)

theorem ExtraLe.app {q : Wire} {P Q R S : Program} (h:ExtraLe q P Q) (k:ExtraLe q R S) :
    ExtraLe q (P++R) (Q++S) := by
  refine ⟨?_,?_⟩
  · rw [wires_append,wires_append]
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · rcases Finset.mem_insert.mp (h.1 hx) with he|he
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ he)
    · rcases Finset.mem_insert.mp (k.1 hx) with he|he
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ he)
  · simp only [Challenge.gateSlots_append]
    exact Nat.add_le_add h.2 k.2

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: ParkCarryBodyRelationDevelop3
section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 5000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic ControlLoan1589BFFold

theorem body_le_extra (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    ExtraLe L.core.sumCarry (body L c) (bBody L c) := by
  unfold body bBody
  refine ExtraLe.app (ExtraLe.ofLe _ (QRel.measuredFoldQ_le L hw _)) (ExtraLe.app (ExtraLe.ofLe _ (QRel.measuredFoldQ_le L hw _)) ⟨?_, ?_⟩)
  · have wc := (QRel.qprog_le (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)).1
    have ef := (QRel.eFold_le L hw c).1
    have sk := eSubK_wires L hw
    have ab := eAddB_wires L hw
    have ml {A B : Program} {q : Wire} (h : q ∈ wires A) : q ∈ wires (A ++ B) := by
      rw [wires_append]; exact Finset.mem_union_left _ h
    have mr {A B : Program} {q : Wire} (h : q ∈ wires B) : q ∈ wires (A ++ B) := by
      rw [wires_append]; exact Finset.mem_union_right _ h
    have hOE {q : Wire} (h : q ∈ oldE L) : q ∈ wires (wFold L ++ (eFold L c ++ wRestore L)) := by
      rcases Finset.mem_union.mp h with h|h
      · exact ml (mr (mr (ml h)))
      · exact ml (mr (mr (mr (ml h))))
    intro q hq
    by_cases spare:q=L.core.sumCarry
    · exact Finset.mem_insert.mpr (Or.inl spare)
    apply Finset.mem_insert_of_mem
    simp only [fold, wCoreK, rebuild, wires_append, Finset.mem_union] at hq
    rcases hq with (h | h | (h | (h | h | h) | h) | h | h | h) | h | h | h | h
    · exact hOE (eAddLo_oldE L hw h)
    · exact ml (ml h)
    · exact hOE (wFwdK_oldE L hw h)
    · exact hOE (kw_oldE L hw h)
    · exact ml (mr (ml (wc h)))
    · exact hOE (kw_oldE L hw h)
    · exact hOE (wInvK_oldE L hw h)
    · exact ml (mr (mr (mr (mr (wUnbuildKnown_wires L hw h)))))
    · have hh:q=eU L ∨ q=L.core.sumCarry := by simpa [program,wires,Instr.wires,or_comm] using h
      rcases hh with hh|hh
      · apply hOE
        exact oldE_mem L hw q (Or.inr (Or.inr (Or.inr (Or.inl (hh ▸ (eK_mem L hw).2.1)))))
      · exact False.elim (spare hh)
    · exact ml (mr (mr (ml (sk h))))
    · exact mr (ml (ef h))
    · exact mr (mr (mr (mr (ml (ab h)))))
    · have hh:=(restore_resources L hw).2.2.1 h
      rcases Finset.mem_insert.mp hh with hh|hh
      · exact False.elim (spare hh)
      · exact hOE hh
    · exact hOE (padM_oldE L hw 751 h)
  · have wc := (QRel.qprog_le (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)).2
    have ef := (QRel.eFold_le L hw c).2
    have sk := eSubK_slots L hw
    have ab := eAddB_slots L hw
    have f1 := WinArith.tFwdK_slots (cin := L.core.cin) (mLens L hw) (eU L)
    have f2 := WinArith.tInvK_slots (cin := L.core.cin) (mLens L hw) (eU L)
    have f5 := padM_slots L 751
    have g1 := wBuild_slots_ge L hw
    have wun := wUnbuildKnown_slots L hw
    have g2 := wUnbuild_slots_ge L hw
    have known := wUnbuildKnown_slots L hw
    have k1 := kw_slots L
    have e1 := eAddLo_slots L hw
    have e2 := program_slots (eU L) L.core.sumCarry
    have e3 := (restore_resources L hw).2.2.2
    have l2 := eSrc_length L hw (whiSrc L) (Or.inr rfl)
    have wa := KnownTopAdd.addInPlace_slots_eq (whiSrc L) (eReg L) (eBank L) L.core.cin l2.1 l2.2
    rw [eReg_length L hw] at wa
    simp only [fold, rebuild, wCoreK, wFold, wRestore, wFwdK, wInvK, wCoreTq, wCore, eAdd,
      Challenge.gateSlots_append] at *
    omega


theorem body_rel (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire) :
    toffoliCount (body L c)+1052=toffoliCount (bBody L c) ∧
    measurementCount (body L c)+4=measurementCount (bBody L c) ∧
    ExtraLe L.core.sumCarry (body L c) (bBody L c) := by
  have current:=body_counts L hw c
  have preceding:=bBody_countsTq L hw c
  have old:=QRel.bBody_rel L hw c
  exact ⟨by omega,by omega,body_le_extra L hw c⟩

theorem body_support (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (hn:L.wires.Nodup) (c : Wire) : wires (body L c)⊆(c::L.wires).toFinset := by
  intro q hq
  have h:=(body_le_extra L hw c).1 hq
  rcases Finset.mem_insert.mp h with h|h
  · simp only [List.mem_toFinset,List.mem_cons]
    right
    rw [h]
    simp [Arithmetic.CuccaroStreamedSquareWideLayout.wires,Arithmetic.CuccaroStreamedSquareLayout.wires]
  · exact (bBody_support L hw hn c) h

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: BBodySumCarryFreeDevelop2
section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem bBody_sumCarry_replace (L : CuccaroStreamedSquareWideLayout) (c q : Wire) :
    bBodyTq {L with core:={L.core with sumCarry:=q} } c=bBodyTq L c := by rfl

end ECDSAAdd.Entrant.ControlLoan1589BFFold
end


-- Carry host component: HostedBodyPlacementDevelop
section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

def hostLayout (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) : CuccaroStreamedSquareWideLayout :=
  {L with core:={L.core with sumCarry:=rho.symm L.core.sumCarry} }

def hostedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
  body (hostLayout L rho) c

theorem host_widths (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho : Equiv.Perm Wire) :
    (hostLayout L rho).Widths := by
  exact ⟨⟨hw.core.y,hw.core.out,hw.core.product,hw.core.pad,hw.core.work⟩,hw.overflowPad⟩

theorem oldBody_host (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) :
    bBody (hostLayout L rho) c=bBody L c := by rfl

theorem hosted_rel (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho : Equiv.Perm Wire) (c : Wire) :
    toffoliCount (hostedBody L rho c)+1052=toffoliCount (bBody L c) ∧
    measurementCount (hostedBody L rho c)+4=measurementCount (bBody L c) ∧
    ExtraLe (rho.symm L.core.sumCarry) (hostedBody L rho c) (bBody L c) := by
  have h:=body_rel (hostLayout L rho) (host_widths L hw rho) c
  simpa only [hostedBody,oldBody_host,hostLayout] using h

theorem host_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire)
    (h:rho L.core.sumCarry=L.core.sumCarry) : hostLayout L rho=L := by
  have hi:rho.symm L.core.sumCarry=L.core.sumCarry := by
    apply rho.injective
    simpa only [Equiv.apply_symm_apply] using h.symm
  simp only [hostLayout,hi]

theorem hosted_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire)
    (h:rho L.core.sumCarry=L.core.sumCarry) : hostedBody L rho c=body L c := by
  rw [hostedBody,host_eq L rho h]

end ECDSAAdd.Entrant.ParkCarryDevelop
end


-- Carry host component: HostedBodySlotsDevelop2
section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic ControlLoan1589BFFold

theorem hostSquare_slots_independent (x y cs : List Wire) (cin q q' k : Wire)
    (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31) :
    Challenge.gateSlots (hostSquare x y cs cin q k)=Challenge.gateSlots (hostSquare x y cs cin q' k) := by
  obtain ⟨a,a',as,rfl⟩:=HostedSquareSubDevelop.shape x (by omega)
  obtain ⟨b,b',bs,rfl⟩:=HostedSquareSubDevelop.shape y (by omega)
  cases cs with
  | nil => simp at lc
  | cons c cs =>
    have h:=KnownTopAdd.addTop_slots_eq (a'::as) (b'::bs) cs c q (by simp only [List.length_cons] at lx ly ⊢;omega) (by simp only [List.length_cons] at lc ly ⊢;omega)
    have h':=KnownTopAdd.addTop_slots_eq (a'::as) (b'::bs) cs c q' (by simp only [List.length_cons] at lx ly ⊢;omega) (by simp only [List.length_cons] at lc ly ⊢;omega)
    change Challenge.gateSlots ([Instr.measureX k [] []]++(notRegister (b::b'::bs)++(KnownSecondTopDevelop.addTop true (a::a'::as) (b::b'::bs) (c::cs) cin q++notRegister (b::b'::bs))))=Challenge.gateSlots ([Instr.measureX k [] []]++(notRegister (b::b'::bs)++(KnownSecondTopDevelop.addTop true (a::a'::as) (b::b'::bs) (c::cs) cin q'++notRegister (b::b'::bs))))
    simp only [KnownSecondTopDevelop.addTop,Challenge.gateSlots_append]
    omega

theorem hosted_slots (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho : Equiv.Perm Wire) (c : Wire) :
    Challenge.gateSlots (hostedBody L rho c)=Challenge.gateSlots (body L c) := by
  have hr:Challenge.gateSlots (restore (hostLayout L rho))=Challenge.gateSlots (restore L) :=
    hostSquare_slots_independent (mU L) (eLo L) ((eBank L).take 31) L.core.cin
      (rho.symm L.core.sumCarry) L.core.sumCarry (eKw L)
      (mU_length L hw) (eLo_length L hw) (eBank_take_length L hw 31 (by omega))
  have hp:Challenge.gateSlots (program (eU (hostLayout L rho)) (hostLayout L rho).core.sumCarry)=
      Challenge.gateSlots (program (eU L) L.core.sumCarry) := rfl
  simp only [hostedBody,body,fold,rebuild,Challenge.gateSlots_append,hr,hp]
  rfl

theorem hosted_counts (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho : Equiv.Perm Wire) (c : Wire) :
    toffoliCount (hostedBody L rho c)=4771 ∧ measurementCount (hostedBody L rho c)=5924 :=
  body_counts (hostLayout L rho) (host_widths L hw rho) c

end ECDSAAdd.Entrant.ParkCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
namespace ECDSAAdd.Entrant.InverseCarryDevelop

theorem run_update_outside (P : Program) (q : Wire) (v : Bool) (hq:q∉wires P)
    (s : State) (m : List Bool) :
    run P m ⟨s.phase,writeBit s.basis q v⟩=
      ⟨(run P m s).phase,writeBit (run P m s).basis q v⟩ := by
  have eq:=run_measured_locality P (wires P) (Finset.Subset.refl _) s
    ⟨s.phase,writeBit s.basis q v⟩ m rfl (by
      intro w hw
      have ne:w≠q := by intro e;exact hq (e ▸ hw)
      simp [writeBit,Function.update,ne])
  apply State.extensionality (run P m ⟨s.phase,writeBit s.basis q v⟩)
    (⟨(run P m s).phase,writeBit (run P m s).basis q v⟩ : State) eq.1.symm
  funext w
  change (run P m ⟨s.phase,writeBit s.basis q v⟩).basis w=writeBit (run P m s).basis q v w
  by_cases wq:w=q
  · subst w
    rw [run_preserves_outside P m _ q hq]
    simp [writeBit]
  · have up:writeBit (run P m s).basis q v w=(run P m s).basis w := by
      simp [writeBit,Function.update,wq]
    rw [up]
    by_cases hw:w∈wires P
    · exact (eq.2 w hw).symm
    · rw [run_preserves_outside P m _ w hw,run_preserves_outside P m _ w hw]
      simp [writeBit,Function.update,wq]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def move (q c : Wire) : Program := [.CX q c,.CX c q]

theorem move_correct (q c : Wire) (ne:q≠c) (s : State) (m : List Bool) (hc:s.basis c=false) :
    run (move q c) m s=⟨s.phase,writeBit (writeBit s.basis c (s.basis q)) q false⟩ := by
  simp only [move,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw:w=q
  · subst w;simp [writeBit,Function.update,ne,hc]
  · by_cases hwc:w=c
    · subst w;simp [writeBit,Function.update,Ne.symm ne,hc]
    · simp [writeBit,Function.update,hw,hwc]

theorem consume_eq_majority (a b cin c q : Wire) (hn:[a,b,cin,c].Nodup) (ne:q≠c)
    (s : State) (m : List Bool) (hc:s.basis c=false)
    (ready:s.basis q=carryBit (s.basis a) (s.basis b) (s.basis cin)) :
    run (move q c) m s=
      ⟨(run (majority a b cin c) m s).phase,writeBit (run (majority a b cin c) m s).basis q false⟩ := by
  rw [move_correct q c ne s m hc,majority_correct a b cin c hn s m]
  simp only [hc,Bool.false_xor,ready]

def produce (a b cin c q : Wire) : Program := majority a b cin c++[.CX c q]

theorem produce_correct (a b cin c q : Wire) (hn:[a,b,cin,c].Nodup) (ne:q≠c)
    (s : State) (m : List Bool) (hc:s.basis c=false) (hq:s.basis q=false) :
    run (produce a b cin c q) m s=
      ⟨s.phase,writeBit (writeBit s.basis c (carryBit (s.basis a) (s.basis b) (s.basis cin))) q
        (carryBit (s.basis a) (s.basis b) (s.basis cin))⟩ := by
  have mc:measurementCount (majority a b cin c)=0 := rfl
  rw [produce,run_append,mc]
  simp only [List.take_zero,List.drop_zero]
  rw [majority_correct a b cin c hn s []]
  simp only [hc,Bool.false_xor,run]
  congr 1
  simp [writeBit,Function.update,ne,hq]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def carryPrefix : Nat → List Wire → List Wire → List Wire → Wire → Program
  | n+1,a::as,b::bs,c::cs,cin => majority a b cin c++carryPrefix n as bs cs c
  | _,_,_,_,_ => []

def prefixState : Nat → List Wire → List Wire → List Wire → Wire → State → State
  | n+1,a::as,b::bs,c::cs,cin,s => prefixState n as bs cs c
      ⟨s.phase,writeBit s.basis c (s.basis c ^^ carryBit (s.basis a) (s.basis b) (s.basis cin))⟩
  | _,_,_,_,_,s => s

theorem prefix_head_nd (a b c cin : Wire) (as bs cs : List Wire)
    (hn:(cin::((a::as)++(b::bs)++(c::cs))).Nodup) : [a,b,cin,c].Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro w
  have h:=List.nodup_iff_count_le_one.mp hn w
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem prefix_tail_nd (a b c cin : Wire) (as bs cs : List Wire)
    (hn:(cin::((a::as)++(b::bs)++(c::cs))).Nodup) : (c::(as++bs++cs)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro w
  have h:=List.nodup_iff_count_le_one.mp hn w
  simp only [List.count_cons,List.count_append] at h ⊢
  omega

theorem carryPrefix_run (n : Nat) (xs ys cs : List Wire) (cin : Wire)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State) (m : List Bool) :
    run (carryPrefix n xs ys cs cin) m s=prefixState n xs ys cs cin s := by
  induction n generalizing xs ys cs cin s with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons a as =>
      cases ys with
      | nil => rfl
      | cons b bs =>
        cases cs with
        | nil => rfl
        | cons c cs =>
          have nd:=prefix_head_nd a b c cin as bs cs hn
          have tail:=prefix_tail_nd a b c cin as bs cs hn
          have mc:measurementCount (majority a b cin c)=0 := rfl
          simp only [carryPrefix,prefixState,run_append,mc,List.take_zero,List.drop_zero]
          rw [majority_correct a b cin c nd s []]
          exact ih as bs cs c tail _

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def addKTSuffix (r : Bool) : Nat → List Wire → List Wire → List Wire → Wire → Program
  | n+1,a::as,b::bs,c::cs,cin => addKTSuffix r n as bs cs c++eraseCarry a b cin c++[.CX a b,.CX cin b]
  | _,x,y,cs,cin => CodexNarrowKnownTop.addKT r x y cs cin

theorem addKT_split (r : Bool) (n : Nat) (x y cs : List Wire) (cin : Wire)
    (hx:x.length=y.length) (hc:cs.length+1=y.length) (hlen:n+2≤y.length) :
    CodexNarrowKnownTop.addKT r x y cs cin=
      carryPrefix n x y cs cin++addKTSuffix r n x y cs cin := by
  induction n generalizing x y cs cin with
  | zero => rfl
  | succ n ih =>
    cases x with
    | nil => simp only [List.length_nil] at hx hlen; omega
    | cons a as =>
      cases y with
      | nil => simp only [List.length_cons,List.length_nil] at hx hlen ; omega
      | cons b bs =>
        cases as with
        | nil => simp only [List.length_cons,List.length_nil] at hx hlen ; omega
        | cons a' as =>
          cases bs with
          | nil => simp only [List.length_cons,List.length_nil] at hx hlen ; omega
          | cons b' bs =>
            cases cs with
            | nil => simp only [List.length_cons,List.length_nil] at hc hlen ; omega
            | cons c cs =>
              have nonempty:as≠[] := by intro h;subst as;simp only [List.length_cons,List.length_nil] at hx hlen ; omega
              have tail:=ih (a'::as) (b'::bs) cs c (by simpa using hx)
                (by simp only [List.length_cons] at hc ⊢;omega)
                (by simp only [List.length_cons] at hlen ⊢;omega)
              simp only [CodexNarrowKnownTop.addKT,if_neg nonempty,carryPrefix,addKTSuffix]
              rw [tail]
              simp only [List.append_assoc]

theorem carryPrefix_length (n : Nat) (x y cs : List Wire) (cin : Wire)
    (hx:n≤x.length) (hy:n≤y.length) (hc:n≤cs.length) :
    (carryPrefix n x y cs cin).length=6*n := by
  induction n generalizing x y cs cin with
  | zero => rfl
  | succ n ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
      cases y with
      | nil => simp at hy
      | cons b bs =>
        cases cs with
        | nil => simp at hc
        | cons c cs =>
          have tail:=ih as bs cs c (by simpa using hx) (by simpa using hy) (by simpa using hc)
          simp only [carryPrefix,List.length_append,tail]
          have h:(majority a b cin c).length=6 := rfl
          rw [h]
          omega

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def insertCopy (pre post : Program) (c q : Wire) : Program := pre++([.CX c q]++post)

theorem copy_correct (c q : Wire) (s : State) (m : List Bool) (hq:s.basis q=false) :
    run [.CX c q] m s=⟨s.phase,writeBit s.basis q (s.basis c)⟩ := by
  simp only [run,hq,Bool.false_xor]

theorem insertCopy_correct (pre post : Program) (c q : Wire)
    (hqpre:q∉wires pre) (hqpost:q∉wires post)
    (s : State) (m : List Bool) (hq:s.basis q=false) :
    run (insertCopy pre post c q) m s=
      ⟨(run (pre++post) m s).phase,writeBit (run (pre++post) m s).basis q
        ((run pre (m.take (measurementCount pre)) s).basis c)⟩ := by
  have hqt:(run pre (m.take (measurementCount pre)) s).basis q=false :=
    (run_preserves_outside pre _ s q hqpre).trans hq
  simp only [insertCopy,run_append]
  have mc:measurementCount [.CX c q]=0 := rfl
  simp only [mc,List.take_zero,List.drop_zero]
  rw [copy_correct c q _ _ hqt]
  exact run_update_outside post q _ hqpost _ _

theorem consume_tail_eq (a b cin c q : Wire) (hn:[a,b,cin,c].Nodup) (ne:q≠c)
    (post : Program) (hpost:q∉wires post) (s : State) (m : List Bool)
    (hc:s.basis c=false) (ready:s.basis q=carryBit (s.basis a) (s.basis b) (s.basis cin)) :
    run (move q c++post) m s=
      ⟨(run (majority a b cin c++post) m s).phase,
        writeBit (run (majority a b cin c++post) m s).basis q false⟩ := by
  have mm:measurementCount (move q c)=0 := rfl
  have mo:measurementCount (majority a b cin c)=0 := rfl
  simp only [run_append,mm,mo,List.take_zero,List.drop_zero]
  rw [consume_eq_majority a b cin c q hn ne s [] hc ready]
  exact run_update_outside post q false hpost _ _

theorem insertCopy_counts (pre post : Program) (c q : Wire) :
    toffoliCount (insertCopy pre post c q)=toffoliCount (pre++post) ∧
    measurementCount (insertCopy pre post c q)=measurementCount (pre++post) ∧
    Challenge.gateSlots (insertCopy pre post c q)=Challenge.gateSlots (pre++post)+1 := by
  simp [insertCopy,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,Challenge.gateSlots,Challenge.instructionSlots,Nat.add_assoc,Nat.add_comm]

theorem consume_counts (a b cin c q : Wire) :
    toffoliCount (move q c)+1=toffoliCount (majority a b cin c) ∧
    measurementCount (move q c)=measurementCount (majority a b cin c) ∧
    Challenge.gateSlots (move q c)+4=Challenge.gateSlots (majority a b cin c) := by
  exact ⟨rfl,rfl,rfl⟩

theorem insertCopy_support (pre post : Program) (c q : Wire) (hc:c∈wires (pre++post)) :
    wires (insertCopy pre post c q)⊆insert q (wires (pre++post)) := by
  rw [wires_append] at hc ⊢
  intro x hx
  simp only [insertCopy,wires_append,Finset.mem_union] at hx
  rcases hx with hx|(hx|hx)
  · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
  · have h:x=c ∨ x=q := by simpa [wires,Instr.wires] using hx
    rcases h with h|h
    · exact Finset.mem_insert_of_mem (h ▸ hc)
    · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)

theorem insertCopy_physical (pre post : Program) (c q : Wire)
    (hp:GatePhysical pre) (ht:GatePhysical post) (ne:c≠q) :
    GatePhysical (insertCopy pre post c q) := by
  simp only [insertCopy,gatePhysical_append]
  exact ⟨hp,by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ne],ht⟩

theorem consume_support (a b cin c q : Wire) :
    wires (move q c)⊆insert q (wires (majority a b cin c)) := by
  intro x hx
  have h:x=q ∨ x=c := by simpa [move,wires,Instr.wires,or_comm] using hx
  rcases h with h|h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · apply Finset.mem_insert_of_mem
    subst x
    simp [majority,wires,Instr.wires]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem carryPrefix_measurements (n : Nat) (x y cs : List Wire) (cin : Wire) :
    measurementCount (carryPrefix n x y cs cin)=0 := by
  induction n generalizing x y cs cin with
  | zero => rfl
  | succ n ih =>
    cases x with
    | nil => rfl
    | cons a as =>
      cases y with
      | nil => rfl
      | cons b bs =>
        cases cs with
        | nil => rfl
        | cons c cs =>
          have h:measurementCount (majority a b cin c)=0 := rfl
          simp only [carryPrefix,measurementCount_append,h,ih,Nat.zero_add]

def subPre (x y cs : List Wire) (cin : Wire) : Program :=
  notRegister y++carryPrefix 5 x y cs cin

def subPost (x y cs : List Wire) (cin : Wire) : Program :=
  addKTSuffix true 5 x y cs cin++notRegister y

def cachedSub (x y cs : List Wire) (cin q : Wire) : Program :=
  insertCopy (subPre x y cs cin) (subPost x y cs cin) (cs.getD 4 0) q

theorem sub_split (x y cs : List Wire) (cin : Wire)
    (hx:x.length=y.length) (hc:cs.length+1=y.length) (hy:7≤y.length) :
    subPre x y cs cin++subPost x y cs cin=CodexNarrowSub.program x y cs cin := by
  rw [CodexNarrowSub.program,addKT_split true 5 x y cs cin hx hc hy]
  simp only [subPre,subPost,List.append_assoc]

theorem cachedSub_frame (x y cs : List Wire) (cin q : Wire)
    (hx:x.length=y.length) (hc:cs.length+1=y.length) (hy:7≤y.length)
    (hq:q∉wires (CodexNarrowSub.program x y cs cin)) (s : State) (m : List Bool)
    (hz:s.basis q=false) :
    run (cachedSub x y cs cin q) m s=
      ⟨(run (CodexNarrowSub.program x y cs cin) m s).phase,
        writeBit (run (CodexNarrowSub.program x y cs cin) m s).basis q
          ((run (subPre x y cs cin) [] s).basis (cs.getD 4 0))⟩ := by
  have split:=sub_split x y cs cin hx hc hy
  have off:q∉wires (subPre x y cs cin++subPost x y cs cin) := by rw [split];exact hq
  rw [wires_append,Finset.mem_union,not_or] at off
  have mc:measurementCount (subPre x y cs cin)=0 := by
    simp only [subPre,measurementCount_append,(notRegister_counts y).2,carryPrefix_measurements,Nat.zero_add]
  have h:=insertCopy_correct (subPre x y cs cin) (subPost x y cs cin) (cs.getD 4 0) q off.1 off.2 s m hz
  simpa only [cachedSub,split,mc,List.take_zero] using h

theorem cachedSub_counts (x y cs : List Wire) (cin q : Wire)
    (hx:x.length=y.length) (hc:cs.length+1=y.length) (hy:7≤y.length) :
    toffoliCount (cachedSub x y cs cin q)=toffoliCount (CodexNarrowSub.program x y cs cin) ∧
    measurementCount (cachedSub x y cs cin q)=measurementCount (CodexNarrowSub.program x y cs cin) ∧
    Challenge.gateSlots (cachedSub x y cs cin q)=Challenge.gateSlots (CodexNarrowSub.program x y cs cin)+1 := by
  simpa only [cachedSub,sub_split x y cs cin hx hc hy] using
    insertCopy_counts (subPre x y cs cin) (subPost x y cs cin) (cs.getD 4 0) q

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def word5 (a0 a1 a2 a3 a4 : Bool) : Nat :=
  a0.toNat+2*a1.toNat+4*a2.toNat+8*a3.toNat+16*a4.toNat

def carry5 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool) : Bool :=
  carryBit a4 b4 (carryBit a3 b3 (carryBit a2 b2 (carryBit a1 b1 (carryBit a0 b0 false))))

theorem carry5_value : ∀a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
    (carry5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).toNat=
      (word5 a0 a1 a2 a3 a4+word5 b0 b1 b2 b3 b4)/32 := by decide +kernel

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem carryPrefix_five (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 cin : Wire) (as bs cs : List Wire)
    (hn:(cin::(([a0,a1,a2,a3,a4]++as)++([b0,b1,b2,b3,b4]++bs)++([c0,c1,c2,c3,c4]++cs))).Nodup) (s : State) (m : List Bool)
    (hz:∀q∈[c0,c1,c2,c3,c4],s.basis q=false) (hi:s.basis cin=false) :
    (run (carryPrefix 5 ([a0,a1,a2,a3,a4]++as) ([b0,b1,b2,b3,b4]++bs) ([c0,c1,c2,c3,c4]++cs) cin) m s).basis c4 =
      carry5 (s.basis a0) (s.basis a1) (s.basis a2) (s.basis a3) (s.basis a4) (s.basis b0) (s.basis b1) (s.basis b2) (s.basis b3) (s.basis b4) := by
  rw [carryPrefix_run 5 ([a0,a1,a2,a3,a4]++as) ([b0,b1,b2,b3,b4]++bs) ([c0,c1,c2,c3,c4]++cs) cin hn s m]
  have hzc0:s.basis c0=false := hz c0 (by simp)
  have hzc1:s.basis c1=false := hz c1 (by simp)
  have hzc2:s.basis c2=false := hz c2 (by simp)
  have hzc3:s.basis c3=false := hz c3 (by simp)
  have hzc4:s.basis c4=false := hz c4 (by simp)
  have small:[a0,a1,a2,a3,a4,b0,b1,b2,b3,b4,c0,c1,c2,c3,c4,cin].Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro w
    have h:=List.nodup_iff_count_le_one.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have getNe (i j : Nat) (hi:i<16) (hj:j<16) (hne:i≠j) :
      ([a0,a1,a2,a3,a4,b0,b1,b2,b3,b4,c0,c1,c2,c3,c4,cin][i]'hi)≠([a0,a1,a2,a3,a4,b0,b1,b2,b3,b4,c0,c1,c2,c3,c4,cin][j]'hj) := by
    intro e
    exact hne ((List.Nodup.getElem_inj_iff small).mp e)
  have ne0_10:a0≠c0 := getNe 0 10 (by decide) (by decide) (by decide)
  have ne0_11:a0≠c1 := getNe 0 11 (by decide) (by decide) (by decide)
  have ne0_12:a0≠c2 := getNe 0 12 (by decide) (by decide) (by decide)
  have ne0_13:a0≠c3 := getNe 0 13 (by decide) (by decide) (by decide)
  have ne0_14:a0≠c4 := getNe 0 14 (by decide) (by decide) (by decide)
  have ne1_10:a1≠c0 := getNe 1 10 (by decide) (by decide) (by decide)
  have ne1_11:a1≠c1 := getNe 1 11 (by decide) (by decide) (by decide)
  have ne1_12:a1≠c2 := getNe 1 12 (by decide) (by decide) (by decide)
  have ne1_13:a1≠c3 := getNe 1 13 (by decide) (by decide) (by decide)
  have ne1_14:a1≠c4 := getNe 1 14 (by decide) (by decide) (by decide)
  have ne2_10:a2≠c0 := getNe 2 10 (by decide) (by decide) (by decide)
  have ne2_11:a2≠c1 := getNe 2 11 (by decide) (by decide) (by decide)
  have ne2_12:a2≠c2 := getNe 2 12 (by decide) (by decide) (by decide)
  have ne2_13:a2≠c3 := getNe 2 13 (by decide) (by decide) (by decide)
  have ne2_14:a2≠c4 := getNe 2 14 (by decide) (by decide) (by decide)
  have ne3_10:a3≠c0 := getNe 3 10 (by decide) (by decide) (by decide)
  have ne3_11:a3≠c1 := getNe 3 11 (by decide) (by decide) (by decide)
  have ne3_12:a3≠c2 := getNe 3 12 (by decide) (by decide) (by decide)
  have ne3_13:a3≠c3 := getNe 3 13 (by decide) (by decide) (by decide)
  have ne3_14:a3≠c4 := getNe 3 14 (by decide) (by decide) (by decide)
  have ne4_10:a4≠c0 := getNe 4 10 (by decide) (by decide) (by decide)
  have ne4_11:a4≠c1 := getNe 4 11 (by decide) (by decide) (by decide)
  have ne4_12:a4≠c2 := getNe 4 12 (by decide) (by decide) (by decide)
  have ne4_13:a4≠c3 := getNe 4 13 (by decide) (by decide) (by decide)
  have ne4_14:a4≠c4 := getNe 4 14 (by decide) (by decide) (by decide)
  have ne5_10:b0≠c0 := getNe 5 10 (by decide) (by decide) (by decide)
  have ne5_11:b0≠c1 := getNe 5 11 (by decide) (by decide) (by decide)
  have ne5_12:b0≠c2 := getNe 5 12 (by decide) (by decide) (by decide)
  have ne5_13:b0≠c3 := getNe 5 13 (by decide) (by decide) (by decide)
  have ne5_14:b0≠c4 := getNe 5 14 (by decide) (by decide) (by decide)
  have ne6_10:b1≠c0 := getNe 6 10 (by decide) (by decide) (by decide)
  have ne6_11:b1≠c1 := getNe 6 11 (by decide) (by decide) (by decide)
  have ne6_12:b1≠c2 := getNe 6 12 (by decide) (by decide) (by decide)
  have ne6_13:b1≠c3 := getNe 6 13 (by decide) (by decide) (by decide)
  have ne6_14:b1≠c4 := getNe 6 14 (by decide) (by decide) (by decide)
  have ne7_10:b2≠c0 := getNe 7 10 (by decide) (by decide) (by decide)
  have ne7_11:b2≠c1 := getNe 7 11 (by decide) (by decide) (by decide)
  have ne7_12:b2≠c2 := getNe 7 12 (by decide) (by decide) (by decide)
  have ne7_13:b2≠c3 := getNe 7 13 (by decide) (by decide) (by decide)
  have ne7_14:b2≠c4 := getNe 7 14 (by decide) (by decide) (by decide)
  have ne8_10:b3≠c0 := getNe 8 10 (by decide) (by decide) (by decide)
  have ne8_11:b3≠c1 := getNe 8 11 (by decide) (by decide) (by decide)
  have ne8_12:b3≠c2 := getNe 8 12 (by decide) (by decide) (by decide)
  have ne8_13:b3≠c3 := getNe 8 13 (by decide) (by decide) (by decide)
  have ne8_14:b3≠c4 := getNe 8 14 (by decide) (by decide) (by decide)
  have ne9_10:b4≠c0 := getNe 9 10 (by decide) (by decide) (by decide)
  have ne9_11:b4≠c1 := getNe 9 11 (by decide) (by decide) (by decide)
  have ne9_12:b4≠c2 := getNe 9 12 (by decide) (by decide) (by decide)
  have ne9_13:b4≠c3 := getNe 9 13 (by decide) (by decide) (by decide)
  have ne9_14:b4≠c4 := getNe 9 14 (by decide) (by decide) (by decide)
  have ne15_10:cin≠c0 := getNe 15 10 (by decide) (by decide) (by decide)
  have ne15_11:cin≠c1 := getNe 15 11 (by decide) (by decide) (by decide)
  have ne15_12:cin≠c2 := getNe 15 12 (by decide) (by decide) (by decide)
  have ne15_13:cin≠c3 := getNe 15 13 (by decide) (by decide) (by decide)
  have ne15_14:cin≠c4 := getNe 15 14 (by decide) (by decide) (by decide)
  have ne11_10:c1≠c0 := getNe 11 10 (by decide) (by decide) (by decide)
  have ne12_10:c2≠c0 := getNe 12 10 (by decide) (by decide) (by decide)
  have ne12_11:c2≠c1 := getNe 12 11 (by decide) (by decide) (by decide)
  have ne13_10:c3≠c0 := getNe 13 10 (by decide) (by decide) (by decide)
  have ne13_11:c3≠c1 := getNe 13 11 (by decide) (by decide) (by decide)
  have ne13_12:c3≠c2 := getNe 13 12 (by decide) (by decide) (by decide)
  have ne14_10:c4≠c0 := getNe 14 10 (by decide) (by decide) (by decide)
  have ne14_11:c4≠c1 := getNe 14 11 (by decide) (by decide) (by decide)
  have ne14_12:c4≠c2 := getNe 14 12 (by decide) (by decide) (by decide)
  have ne14_13:c4≠c3 := getNe 14 13 (by decide) (by decide) (by decide)
  clear hn small getNe hz
  simp_all [prefixState,writeBit,Function.update,carry5]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem shape5 (xs : List Wire) (h:5≤xs.length) :
    ∃a b c d e tail,xs=a::b::c::d::e::tail := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      cases xs with
      | nil => simp at h
      | cons c xs =>
        cases xs with
        | nil => simp at h
        | cons d xs =>
          cases xs with
          | nil => simp at h
          | cons e xs =>
            exact ⟨a,b,c,d,e,xs,rfl⟩

theorem carryPrefix_value5 (xs ys cs : List Wire) (cin : Wire)
    (hx:5≤xs.length) (hy:5≤ys.length) (hc:5≤cs.length)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State) (m : List Bool)
    (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false) :
    ((run (carryPrefix 5 xs ys cs cin) m s).basis (cs.getD 4 0)).toNat=
      (regValue (xs.take 5) s.basis+regValue (ys.take 5) s.basis)/32 := by
  obtain ⟨a0,a1,a2,a3,a4,as,rfl⟩:=shape5 xs hx
  obtain ⟨b0,b1,b2,b3,b4,bs,rfl⟩:=shape5 ys hy
  obtain ⟨c0,c1,c2,c3,c4,cs,rfl⟩:=shape5 cs hc
  have zeros:∀q∈[c0,c1,c2,c3,c4],s.basis q=false := by
    intro q hq
    exact hz q (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using
      (show q=c0 ∨ q=c1 ∨ q=c2 ∨ q=c3 ∨ q=c4 ∨ q∈cs from by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
        tauto))
  have v:=congrArg Bool.toNat (carryPrefix_five a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 cin as bs cs hn s m zeros hi)
  rw [carry5_value] at v
  simpa [regValue,word5,Bool.toNat,Bool.cond_eq_ite,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] using v

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem subPre_value5 (xs ys cs : List Wire) (cin : Wire)
    (hx:5≤xs.length) (hy:5≤ys.length) (hc:5≤cs.length)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State)
    (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false) :
    ((run (subPre xs ys cs cin) [] s).basis (cs.getD 4 0)).toNat=
      (regValue (xs.take 5) s.basis+(31-regValue (ys.take 5) s.basis))/32 := by
  have nd:=List.nodup_cons.mp hn
  have split:=List.nodup_append'.mp nd.2
  have xy:=List.nodup_append'.mp split.1
  have xAway:∀q∈xs,q∉ys := by
    intro q hq bad
    exact List.disjoint_left.mp xy.2.2 hq bad
  have cAway:∀q∈cs,q∉ys := by
    intro q hq bad
    exact List.disjoint_left.mp split.2.2 (List.mem_append_right _ bad) hq
  have cinAway:cin∉ys := by
    intro bad
    exact nd.1 (List.mem_append_left _ (List.mem_append_right _ bad))
  let t:=run (notRegister ys) [] s
  have nr:=notRegister_correct ys xy.2.1 s []
  have zt:∀q∈cs,t.basis q=false := by
    intro q hq
    change (run (notRegister ys) [] s).basis q=false
    rw [nr]
    simpa [cAway q hq] using hz q hq
  have it:t.basis cin=false := by
    change (run (notRegister ys) [] s).basis cin=false
    rw [nr]
    simpa [cinAway] using hi
  have xv:regValue (xs.take 5) t.basis=regValue (xs.take 5) s.basis := by
    apply regValue_congr
    intro q hq
    change (run (notRegister ys) [] s).basis q=s.basis q
    rw [nr]
    simp [xAway q (List.mem_of_mem_take hq)]
  have yv:regValue (ys.take 5) t.basis=31-regValue (ys.take 5) s.basis := by
    have e:regValue (ys.take 5) t.basis=regValue (ys.take 5) (fun q=>!s.basis q) := by
      apply regValue_congr
      intro q hq
      change (run (notRegister ys) [] s).basis q= !s.basis q
      rw [nr]
      simp [List.mem_of_mem_take hq]
    rw [e,regValue_complement]
    have len:(ys.take 5).length=5 := by simp [hy]
    rw [len]
    norm_num
  have val:=carryPrefix_value5 xs ys cs cin hx hy hc hn t [] zt it
  rw [xv,yv] at val
  have count:measurementCount (notRegister ys)=0 := (notRegister_counts ys).2
  simpa only [subPre,run_append,count,List.take_zero,List.drop_zero] using val

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop

theorem carry_return32 (X A : Nat) (hX:X<32) (hA:A<32) :
    (X+(A+32-X)%32)/32=(if A<X then 1 else 0) := by
  split_ifs <;> omega

theorem carry_return_w64 (H : Nat) :
    (H%32+(976*H/64)%32)/32 =
      (if (1040*H/64)%32<H%32 then 1 else 0) := by
  have sum:H+976*H/64=1040*H/64 := by omega
  have back:((1040*H/64)%32+32-H%32)%32=(976*H/64)%32 := by omega
  rw [←back]
  exact carry_return32 _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))

theorem sub_add_carry32 (X A : Nat) (hX:X<32) (hA:A<32) :
    (X+(31-A))/32=(X+(A+32-X)%32)/32 := by
  rw [carry_return32 X A hX hA]
  split_ifs <;> omega

theorem sub_add_carry_w64 (H : Nat) :
    (H%32+(31-(1040*H/64)%32))/32=(H%32+(976*H/64)%32)/32 := by
  have sub:(H%32+(31-(1040*H/64)%32))/32=(if (1040*H/64)%32<H%32 then 1 else 0) := by
    split_ifs <;> omega
  exact sub.trans (carry_return_w64 H).symm

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def cacheBit (H : Nat) : Bool := decide ((1040*H/64)%32<H%32)

theorem bool_nat_injective (a b : Bool) (h:a.toNat=b.toNat) : a=b := by
  cases a <;> cases b <;> simp_all

theorem cacheBit_value (H : Nat) : (cacheBit H).toNat=(if (1040*H/64)%32<H%32 then 1 else 0) := by
  by_cases h:(1040*H/64)%32<H%32 <;> simp [cacheBit,h]

theorem cachedSub_known_frame (xs ys cs : List Wire) (cin q : Wire)
    (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7≤ys.length)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State) (m : List Bool)
    (hz:∀w∈cs,s.basis w=false) (hi:s.basis cin=false)
    (hq:q∉wires (CodexNarrowSub.program xs ys cs cin)) (hq0:s.basis q=false)
    (H : Nat) (source:regValue xs s.basis=H) (target:regValue ys s.basis=1040*H/64) :
    run (cachedSub xs ys cs cin q) m s=
      ⟨(run (CodexNarrowSub.program xs ys cs cin) m s).phase,
        writeBit (run (CodexNarrowSub.program xs ys cs cin) m s).basis q (cacheBit H)⟩ := by
  have v:=subPre_value5 xs ys cs cin (by omega) (by omega) (by omega) hn s hz hi
  rw [regValue_take_mod xs 5 (by omega) s.basis,regValue_take_mod ys 5 (by omega) s.basis,
    source,target] at v
  norm_num only [show 2^5=32 by decide] at v
  rw [sub_add_carry_w64 H,carry_return_w64 H] at v
  have bit:(run (subPre xs ys cs cin) [] s).basis (cs.getD 4 0)=cacheBit H :=
    bool_nat_injective _ _ (v.trans (cacheBit_value H).symm)
  rw [cachedSub_frame xs ys cs cin q hx hc hy hq s m hq0,bit]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem carryPrefix_carry_mem (n : Nat) (xs ys cs : List Wire) (cin : Wire)
    (hx:n≤xs.length) (hy:n≤ys.length) (hc:n≤cs.length) (q : Wire) (hq:q∈cs.take n) :
    q∈wires (carryPrefix n xs ys cs cin) := by
  induction n generalizing xs ys cs cin with
  | zero => simp at hq
  | succ n ih =>
    cases xs with
    | nil => simp at hx
    | cons a as =>
      cases ys with
      | nil => simp at hy
      | cons b bs =>
        cases cs with
        | nil => simp at hc
        | cons c cs =>
          simp only [List.take_succ_cons,List.mem_cons] at hq
          rw [carryPrefix,wires_append]
          rcases hq with hq|hq
          · subst q
            apply Finset.mem_union_left
            simp [majority,wires,Instr.wires]
          · apply Finset.mem_union_right
            exact ih as bs cs c (by simpa using hx) (by simpa using hy) (by simpa using hc) hq

theorem carryPrefix_fifth_mem (xs ys cs : List Wire) (cin : Wire)
    (hx:5≤xs.length) (hy:5≤ys.length) (hc:5≤cs.length) :
    cs.getD 4 0∈wires (carryPrefix 5 xs ys cs cin) := by
  apply carryPrefix_carry_mem 5 xs ys cs cin hx hy hc
  obtain ⟨c0,c1,c2,c3,c4,cs,rfl⟩:=shape5 cs hc
  simp

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem cachedSub_resources (x y cs : List Wire) (cin q : Wire)
    (hx:x.length=y.length) (hc:cs.length+1=y.length) (hy:7≤y.length)
    (hq:q∉wires (CodexNarrowSub.program x y cs cin))
    (hp:GatePhysical (CodexNarrowSub.program x y cs cin)) :
    wires (cachedSub x y cs cin q)⊆insert q (wires (CodexNarrowSub.program x y cs cin)) ∧
    GatePhysical (cachedSub x y cs cin q) := by
  have split:=sub_split x y cs cin hx hc hy
  have cused:cs.getD 4 0∈wires (subPre x y cs cin++subPost x y cs cin) := by
    rw [wires_append,subPre,wires_append]
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (carryPrefix_fifth_mem x y cs cin (by omega) (by omega) (by omega)))
  have hs:=insertCopy_support (subPre x y cs cin) (subPost x y cs cin) (cs.getD 4 0) q cused
  have pp:GatePhysical (subPre x y cs cin++subPost x y cs cin) := by rw [split];exact hp
  rw [gatePhysical_append] at pp
  have ne:cs.getD 4 0≠q := by
    intro e
    apply hq
    rw [←split]
    exact e ▸ cused
  exact ⟨by simpa only [cachedSub,split] using hs,
    insertCopy_physical _ _ _ _ pp.1 pp.2 ne⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def buildPre (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  Acc.seedOp acc Z 163 (Acc.earlyTerm src false 4)++
    Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src false 10)

def buildPost (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  Acc.op (acc.take 161) Z bank cin 161 false (Acc.earlyTerm src false 32)

def buildCached (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire) : Program :=
  buildPre acc Z bank cin src++
    cachedSub (Acc.tx Z 139 (Acc.earlyTerm src true 6))
      (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6))
      (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q++buildPost acc Z bank cin src

theorem build_split (acc Z bank : List Wire) (cin : Wire) (src : List Wire) :
    NarrowAcc.build8 acc Z bank cin src=buildPre acc Z bank cin src++
      CodexNarrowSub.accSub (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6)++buildPost acc Z bank cin src := rfl

theorem sub6_lengths (acc Z bank : List Wire) (src : List Wire)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    (Acc.tx Z 139 (Acc.earlyTerm src true 6)).length=133 ∧
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)).length=133 ∧
    (Acc.tc bank 139 (Acc.earlyTerm src true 6)).length=132 := by
  simp [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,ha,hs,Nat.min_eq_left hz,Nat.min_eq_left hb]

theorem buildCached_counts (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    toffoliCount (buildCached acc Z bank cin src q)=toffoliCount (NarrowAcc.build8 acc Z bank cin src) ∧
    measurementCount (buildCached acc Z bank cin src q)=measurementCount (NarrowAcc.build8 acc Z bank cin src) ∧
    Challenge.gateSlots (buildCached acc Z bank cin src q)=Challenge.gateSlots (NarrowAcc.build8 acc Z bank cin src)+1 := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have count:=cachedSub_counts (Acc.tx Z 139 (Acc.earlyTerm src true 6))
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q
    (by omega) (by omega) (by omega)
  simp only [buildCached,build_split,CodexNarrowSub.accSub,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem buildPre_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc:acc.length=163) (hsrc:src.length≤128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (base : BasisState) (hz:∀q∈Z,base q=false) (hb:∀q∈bank,base q=false) (hi:base cin=false) :
    Triple (SquareFrame acc base 0) (buildPre acc Z bank cin src)
      (SquareFrame acc base (1040*regValue src base)) := by
  have tm := NarrowAcc.terms_mem src
  have hf4 := hf _ tm.1
  have hf10 := hf _ tm.2.1
  let H := regValue src base
  have hH : H<2^128 := lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) hsrc)
  have seed := Acc.seed_triple acc Z bank cin 163 (Acc.earlyTerm src false 4) hacc hf4 base hz
    0 (16*H) (Or.inl (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
  have add : Triple (SquareFrame acc base (16*H))
      (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src false 10))
      (SquareFrame acc base (1040*H)) := by
    have h := Acc.op_prefix_triple acc Z bank cin 163 139 (Acc.earlyTerm src false 10) hacc
      (by norm_num [Acc.earlyTerm]) hf10 (by simp only [Acc.earlyTerm]; omega) base hz hb hi false (16*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm] at hH ⊢;dsimp [H] at *;omega)
    have value : Acc.step base false (16*H) (Acc.earlyTerm src false 10)=1040*H := by
      norm_num [Acc.step,Acc.earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  exact seed.seq add

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop

def setWire (s : State) (q : Wire) (v : Bool) : State := ⟨s.phase,writeBit s.basis q v⟩

theorem run_setWire (P : Program) (q : Wire) (v : Bool) (hq:q∉wires P) (s : State) (m : List Bool) :
    run P m (setWire s q v)=setWire (run P m s) q v := run_update_outside P q v hq s m

theorem setWire_restore (s : State) (q : Wire) (v : Bool) (h:s.basis q=false) :
    setWire (setWire s q v) q false=s := by
  apply State.extensionality (setWire (setWire s q v) q false) s rfl
  funext w
  change writeBit (writeBit s.basis q v) q false w=s.basis w
  by_cases eq:w=q
  · subst w;simp [writeBit,h]
  · simp [writeBit,Function.update,eq]

theorem run_three (A W C : Program) (s : State) (m : List Bool) :
    run (A++W++C) m s=run C (m.drop (measurementCount A+measurementCount W))
      (run W ((m.drop (measurementCount A)).take (measurementCount W)) (run A (m.take (measurementCount A)) s)) := by
  simp only [run_append,measurementCount_append]
  have e1:List.take (measurementCount A) (List.take (measurementCount A+measurementCount W) m)=List.take (measurementCount A) m := by
    rw [List.take_take];congr 1;omega
  have e2:List.drop (measurementCount A) (List.take (measurementCount A+measurementCount W) m)=List.take (measurementCount W) (List.drop (measurementCount A) m) := by
    rw [List.drop_take];congr 1;omega
  rw [e1,e2]

theorem modify_inside (pre old new post : Program) (q : Wire) (v : Bool)
    (sameM:measurementCount new=measurementCount old) (hpost:q∉wires post)
    (s : State) (m : List Bool)
    (change:run new ((m.drop (measurementCount pre)).take (measurementCount old))
      (run pre (m.take (measurementCount pre)) s)=
      setWire (run old ((m.drop (measurementCount pre)).take (measurementCount old))
        (run pre (m.take (measurementCount pre)) s)) q v) :
    run (pre++new++post) m s=setWire (run (pre++old++post) m s) q v := by
  simp only [run_three,sameM]
  rw [change,run_setWire post q v hpost]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem buildCached_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (hq:s.basis q=false)
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (NarrowAcc.build8 acc Z bank cin src)) :
    run (buildCached acc Z bank cin src q) m s=
      setWire (run (NarrowAcc.build8 acc Z bank cin src) m s) q (cacheBit (regValue src s.basis)) := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (buildPre acc Z bank cin src) (m.take (measurementCount (buildPre acc Z bank cin src))) s
  have preFrame:=buildPre_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s
    (m.take (measurementCount (buildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have len:(acc.take 139).length=139 := by simp [hacc]
  have lens:=Acc.fits_lengths (acc.take 139) Z bank cin 139 f len fit.toFitsLen
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have window:(Acc.ty (acc.take 139) f).length=133 := by simpa [f,Acc.earlyTerm] using lens.2.2
  have xv:regValue (Acc.tx Z 139 f) t.basis=H := by
    have zero:regValue (Z.take (139-f.shift-f.src.length)) t.basis=0 := (regValue_zero _ _).mpr (by
      intro w hw
      exact (same w (Or.inl (by simp [List.mem_of_mem_take hw]))).trans (hz w (List.mem_of_mem_take hw)))
    have srcv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
    change regValue (src++Z.take (139-6-src.length)) t.basis=H
    change regValue (Z.take (139-6-src.length)) t.basis=0 at zero
    rw [regValue_append,srcv,zero,Nat.mul_zero,Nat.add_zero]
  have pref:=regValue_take_drop_of_lt acc 139 (1040*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue (Acc.ty (acc.take 139) f) t.basis=1040*H/64 := by
    rw [Acc.ty,regValue_drop_div _ _ (by simp [f,Acc.earlyTerm,len]),pref.1]
    simp [f,Acc.earlyTerm]
  have clean:∀w∈Acc.tc bank 139 f,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=false := (preFrame.2.2 q qacc).trans hq
  have pieces:=off
  rw [build_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have count:=cachedSub_counts (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q lens.1 lens.2.1 (by omega)
  have changed:=cachedSub_known_frame (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q
    lens.1 lens.2.1 (by omega) nd t
    ((m.drop (measurementCount (buildPre acc Z bank cin src))).take (measurementCount (CodexNarrowSub.accSub (acc.take 139) Z bank cin 139 f)))
    clean iv pieces.1.2 qt H xv yv
  have result:=modify_inside (buildPre acc Z bank cin src) (CodexNarrowSub.accSub (acc.take 139) Z bank cin 139 f)
    (cachedSub (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q)
    (buildPost acc Z bank cin src) q (cacheBit H) count.2.1 pieces.2 s m changed
  simpa only [buildCached,build_split,f] using result

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.KnownOutputAdder KnownAffinePrefixDevelop

def knownPrefix (extra : Wire) : List MappedBit → List Wire → List MappedBit → List Wire → Wire → Program
  | _b::b'::bs,_y::y'::ys,_d::d'::ds,c::cs,_cin =>
      head ds.isEmpty b' d' extra y' c++knownPrefix extra (b'::bs) (y'::ys) (d'::ds) cs c
  | _,_,_,_,_ => []

def mappedPrefix : Nat → List MappedBit → List Wire → List Wire → Wire → Program
  | n+1,b::bs,y::ys,c::cs,cin => mappedMajority b y cin c++mappedPrefix n bs ys cs c
  | _,_,_,_,_ => []

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

theorem knownPrefix_eq_mappedPrefix (extra : Wire) (bits sums : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (hn : (cin::(ys++carry)).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hw : ∀q∈mappedWires sums,q∉cin::(ys++carry))
    (he : extra∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hs : sums.length≤ys.length)
    (hc : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false)
    (ready : Ready extra bits sums ys (s.basis cin) s.basis) :
    run (knownPrefix extra bits ys sums carry cin) m s=run (mappedPrefix (sums.length-1) bits ys carry cin) m s := by
  induction ys generalizing bits sums carry cin s m with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => cases bs <;> cases ys <;> cases carry <;> rfl
      | cons d ds =>
        cases ys with
        | nil =>
          have hb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
          have hd : ds=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hs;omega)
          subst bs; subst ds
          rfl
        | cons y' ys =>
          cases bs with
          | nil => simp at hl
          | cons b' bs =>
            cases ds with
            | nil => rfl
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
                have witness : ∀q∈mappedWires (d'::ds),q∉c::((y'::ys)++cs) := by
                  intro q hq bad
                  exact hw q (tail_source_mem d _ q hq)
                    (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have sourceC (q : Wire) (hq : q∈mappedWires (b::b'::bs)) : q≠c := by
                  intro bad; exact ha q hq (by simp [bad])
                have witnessC (q : Wire) (hq : q∈mappedWires (d::d'::ds)) : q≠c := by
                  intro bad; exact hw q hq (by simp [bad])
                let K := carryBit (b.value s.basis) (s.basis y) (s.basis cin)
                let u : State := ⟨s.phase,writeBit s.basis c K⟩
                have clean0 : s.basis c=false := hclean c (by simp)
                have rt : Ready extra (b'::bs) (d'::ds) (y'::ys) K s.basis := by
                  exact (List.cons.inj ready).2
                have next : (if ds.isEmpty then d'.value s.basis ^^ s.basis extra else d'.value s.basis)=sumBit (b'.value s.basis) (s.basis y') K := by
                  exact (List.cons.inj rt).1
                have affine : ((s.basis y' ^^ b'.value s.basis) ^^ (if ds.isEmpty then d'.value s.basis ^^ s.basis extra else d'.value s.basis))=K := by
                  rw [next]
                  cases b'.value s.basis <;> cases s.basis y' <;> cases K <;> decide
                have pre (mm : List Bool) : run (head ds.isEmpty b' d' extra y' c) mm s=u := by
                  rw [head_correct ds.isEmpty b' d' extra y' c yc'
                    (fun q hq => sourceC q (tail_source_mem b _ q (head_source_mem b' bs q hq)))
                    (fun q hq => witnessC q (tail_source_mem d _ q (head_source_mem d' ds q hq)))
                    (by intro bad;exact he (by simp [bad])) s mm]
                  simp only [u,clean0,Bool.false_xor,affine]
                have old (mm : List Bool) : run (mappedMajority b y cin c) mm s=u := by
                  rw [mappedMajority_correct b y cin c three]
                  · simp [u,K,clean0]
                  · intro q hq bad
                    exact ha q (head_source_mem b _ q hq)
                      (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have keep (q : Wire) (hne : q≠c) : u.basis q=s.basis q := by
                  simp [u,writeBit,hne]
                have uc : u.basis c=K := by simp [u,writeBit]
                have tailReady : Ready extra (b'::bs) (d'::ds) (y'::ys) (u.basis c) u.basis := by
                  rw [uc]
                  apply ready_congr extra _ _ _ _ s.basis u.basis _ _ _ _ rt
                  · intro q hq
                    exact (keep q (sourceC q (tail_source_mem b _ q hq))).symm
                  · intro q hq
                    exact (keep q (witnessC q (tail_source_mem d _ q hq))).symm
                  · intro q hq
                    exact (keep q (fun bad => ctail (bad ▸ hq))).symm
                  · exact (keep extra (by intro bad;exact he (by simp [bad]))).symm
                have clean : ∀q∈cs,u.basis q=false := by
                  intro q hq
                  rw [keep q (fun bad => ccs (bad ▸ hq))]
                  exact hclean q (by simp [hq])
                have tail (mm : List Bool) := ih (b'::bs) (d'::ds) cs c nd source witness
                  (by intro bad;exact he (by simp only [List.mem_cons,List.mem_append] at bad ⊢;tauto))
                  (by simpa using hl) (by simpa using hs) (by simpa using hc) u mm clean tailReady
                have pc := head_counts ds.isEmpty b' d' extra y' c
                have oc := mappedBit_counts b y cin c
                change run (head ds.isEmpty b' d' extra y' c++knownPrefix extra (b'::bs) (y'::ys) (d'::ds) cs c) m s=
                  run (mappedMajority b y cin c++mappedPrefix ((d'::ds).length-1) (b'::bs) (y'::ys) cs c) m s
                simp only [run_append,pc.2,oc.2.1,List.take_zero,List.drop_zero]
                rw [pre,old]
                exact tail m

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.KnownOutputAdder KnownAffinePrefixDevelop

def knownSuffix (extra : Wire) : List MappedBit → List Wire → List MappedBit → List Wire → Wire → Program
  | b::b'::bs,y::y'::ys,_d::d'::ds,c::cs,cin =>
      knownSuffix extra (b'::bs) (y'::ys) (d'::ds) cs c++mappedEraseCarry b y cin c++mappedSum b y cin
  | bits,ys,_,carry,cin => mappedAdd bits ys carry cin

theorem known_program_split (extra : Wire) (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    KnownAffinePrefixDevelop.program extra bits ys sums carry cin=
      knownPrefix extra bits ys sums carry cin++knownSuffix extra bits ys sums carry cin := by
  induction ys generalizing bits sums carry cin with
  | nil => cases bits with
    | nil => rfl
    | cons b bs => cases bs <;> rfl
  | cons y ys ih =>
    cases bits with
    | nil => rfl
    | cons b bs =>
      cases ys with
      | nil => cases bs <;> rfl
      | cons y' ys =>
        cases bs with
        | nil => rfl
        | cons b' bs =>
          cases sums with
          | nil => rfl
          | cons d ds =>
            cases ds with
            | nil => rfl
            | cons d' ds =>
              cases carry with
              | nil => rfl
              | cons c cs =>
                change head ds.isEmpty b' d' extra y' c++KnownAffinePrefixDevelop.program extra (b'::bs) (y'::ys) (d'::ds) cs c++mappedEraseCarry b y cin c++mappedSum b y cin=
                  (head ds.isEmpty b' d' extra y' c++knownPrefix extra (b'::bs) (y'::ys) (d'::ds) cs c)++
                    (knownSuffix extra (b'::bs) (y'::ys) (d'::ds) cs c++mappedEraseCarry b y cin c++mappedSum b y cin)
                rw [ih]
                simp only [List.append_assoc]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic SourceAddFourDevelop

theorem source_suffix_head (src Z ys carry : List Wire) (cin : Wire)
    (hs:7≤src.length) (hy:ys.length=src.length+5) (hc:5≤carry.length) :
    (knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin).take 6=
      majority ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0) := by
  obtain ⟨a0,a1,a2,a3,a4,as,rfl⟩:=shape5 src (by omega)
  cases as with
  | nil => simp only [List.length_cons,List.length_nil] at hs;omega
  | cons a5 as =>
    cases as with
    | nil => simp only [List.length_cons,List.length_nil] at hs;omega
    | cons a6 as =>
      obtain ⟨b0,b1,b2,b3,b4,bs,rfl⟩:=shape5 ys (by simp only [List.length_cons] at hy;omega)
      cases bs with
      | nil => simp only [List.length_cons,List.length_nil] at hy;omega
      | cons b5 bs =>
        obtain ⟨c0,c1,c2,c3,c4,cs,rfl⟩:=shape5 carry hc
        change _=majority a4 b4 c3 c4
        simp [knownSuffix,desired,mappedRead,mappedAdd,mappedMajority,majority,List.append_assoc]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.KnownOutputAdder KnownAffinePrefixDevelop

theorem knownPrefix_counts (extra : Wire) (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    toffoliCount (knownPrefix extra bits ys sums carry cin)=0 ∧
    measurementCount (knownPrefix extra bits ys sums carry cin)=0 := by
  induction ys generalizing bits sums carry cin with
  | nil => cases bits with
    | nil => exact ⟨rfl,rfl⟩
    | cons b bs => cases bs <;> exact ⟨rfl,rfl⟩
  | cons y ys ih =>
    cases bits with
    | nil => exact ⟨rfl,rfl⟩
    | cons b bs =>
      cases ys with
      | nil => cases bs <;> exact ⟨rfl,rfl⟩
      | cons y' ys =>
        cases bs with
        | nil => exact ⟨rfl,rfl⟩
        | cons b' bs =>
          cases sums with
          | nil => exact ⟨rfl,rfl⟩
          | cons d ds =>
            cases ds with
            | nil => exact ⟨rfl,rfl⟩
            | cons d' ds =>
              cases carry with
              | nil => exact ⟨rfl,rfl⟩
              | cons c cs =>
                have count:=KnownAffinePrefixDevelop.head_counts ds.isEmpty b' d' extra y' c
                change toffoliCount (head ds.isEmpty b' d' extra y' c++knownPrefix extra (b'::bs) (y'::ys) (d'::ds) cs c)=0 ∧
                  measurementCount (head ds.isEmpty b' d' extra y' c++knownPrefix extra (b'::bs) (y'::ys) (d'::ds) cs c)=0
                have tail:=ih (b'::bs) (d'::ds) cs c
                simp only [toffoliCount_append,measurementCount_append,count.1,count.2,tail.1,tail.2,Nat.zero_add,and_self]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic SourceAddFourDevelop

def addPre (src Z ys carry : List Wire) (cin : Wire) : Program :=
  knownPrefix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin

def addPost (src Z ys carry : List Wire) (cin : Wire) : Program :=
  (knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin).drop 6

def consumedAdd (src Z ys carry : List Wire) (cin q : Wire) : Program :=
  addPre src Z ys carry cin++(move q (carry.getD 4 0)++addPost src Z ys carry cin)

theorem add_split (src Z ys carry : List Wire) (cin : Wire)
    (hs:7≤src.length) (hy:ys.length=src.length+5) (hc:5≤carry.length) :
    SourceAddFourDevelop.program src Z ys carry cin=
      addPre src Z ys carry cin++
        (majority ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0)++addPost src Z ys carry cin) := by
  rw [SourceAddFourDevelop.program,known_program_split]
  have split:=List.take_append_drop 6 (knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin)
  rw [source_suffix_head src Z ys carry cin hs hy hc] at split
  exact congrArg (fun p=>addPre src Z ys carry cin++p) split.symm

theorem consumedAdd_counts (src Z ys carry : List Wire) (cin q : Wire)
    (hs:7≤src.length) (hy:ys.length=src.length+5) (hc:5≤carry.length) :
    toffoliCount (consumedAdd src Z ys carry cin q)+1=toffoliCount (SourceAddFourDevelop.program src Z ys carry cin) ∧
    measurementCount (consumedAdd src Z ys carry cin q)=measurementCount (SourceAddFourDevelop.program src Z ys carry cin) ∧
    Challenge.gateSlots (consumedAdd src Z ys carry cin q)+4=Challenge.gateSlots (SourceAddFourDevelop.program src Z ys carry cin) := by
  have count:=consume_counts ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0) q
  simp only [consumedAdd,add_split src Z ys carry cin hs hy hc,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.KnownOutputAdder SourceAddFourDevelop MixedLiteralAdderDevelop

theorem source_ready (src Z ys : List Wire) (cin : Wire)
    (hs:7≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5)
    (t : BasisState) (hz:∀q∈Z,t q=false) (hcin:t cin=false)
    (H : Nat) (hsrc:regValue src t=H) (hys:regValue ys t=976*H/64) :
    KnownAffinePrefixDevelop.Ready (src.getD 0 0)
      (mappedRead (src++Z.take 5) false) (desired src) ys (t cin) t := by
  have zv : regValue (Z.take 5) t=0 := (regValue_zero _ _).mpr
    (fun q hq=>hz q (List.mem_of_mem_take hq))
  have sv : mappedValue (mappedRead (src++Z.take 5) false) t=H := by
    rw [mappedRead_value,regValue_append,hsrc,zv,Nat.mul_zero,Nat.add_zero]
  have hl : (mappedRead (src++Z.take 5) false).length=ys.length := by simp [mappedRead,hy];omega
  have hd:=desired_length src hs
  have he0 : t (src.getD 0 0)=H.testBit 0 := by
    rw [extra_bit src (by omega) t,hsrc]
  have ready : KnownAffinePrefixDevelop.Ready (src.getD 0 0)
      (mappedRead (src++Z.take 5) false) (desired src) ys (t cin) t := by
    apply KnownAffinePrefixDevelop.ready_of_number _ _ _ _ _ _ hl (by omega)
    intro i hi
    have hi5 : i<5 := by omega
    have bv : ((desired src).map (fun b=>b.value t)).getD i false=H.testBit (i+2) := by
      rw [←boolValue_bit,mapped_boolValue,desired,mappedRead_value,
        CuccaroStreamedSquareWideLayout.regValue_take_mod (src.drop 2) 5 (by simp;omega),
        CuccaroStreamedSquareWideLayout.regValue_drop_div src 2 (by omega),hsrc]
      rw [Nat.testBit_mod_two_pow]
      simp only [hi5,decide_true,Bool.true_and]
      rw [Nat.testBit_div_two_pow]
    rw [KnownAffinePrefixDevelop.values_getD _ _ _ i hi,hd,bv,he0]
    rw [sv,hys,hcin,Bool.toNat_false,Nat.add_zero,arithmetic,Nat.testBit_mod_two_pow]
    have hiy : i<ys.length := by omega
    simp only [hiy,decide_true,Bool.true_and,Nat.add_zero]
    by_cases h4 : i=4
    · subst i
      simpa using (SourceAddFourthBitDevelop.fourth H).symm
    · have hi4 : i<4 := by omega
      rw [if_neg (by omega),SourceAddLowBitsDevelop.low_bit H i hi4]
  exact ready

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem mappedPrefix_read (n : Nat) (xs ys cs : List Wire) (cin : Wire) :
    mappedPrefix n (mappedRead xs false) ys cs cin=carryPrefix n xs ys cs cin := by
  induction n generalizing xs ys cs cin with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons a as =>
      cases ys with
      | nil => rfl
      | cons b bs =>
        cases cs with
        | nil => rfl
        | cons c cs =>
          change majority a b cin c++mappedPrefix n (mappedRead as false) bs cs c=
            majority a b cin c++carryPrefix n as bs cs c
          rw [ih]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.KnownOutputAdder SourceAddFourDevelop MixedLiteralAdderDevelop

theorem source_prefix_eq (src Z ys carry : List Wire) (cin : Wire)
    (hs:7≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5)
    (hc:carry.length+1=ys.length)
    (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
    (s : State) (m : List Bool) (hz:∀q∈Z,s.basis q=false)
    (hclean:∀q∈carry,s.basis q=false) (hcin:s.basis cin=false)
    (H : Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64) :
    run (knownPrefix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin) m s=
      run (carryPrefix 4 (src++Z.take 5) ys carry cin) m s := by
  have geo:=read_geometry (src++Z.take 5) ys carry cin hn
  have hl:(mappedRead (src++Z.take 5) false).length=ys.length := by
    simp only [mappedRead,List.length_map,List.length_append,List.length_take,Nat.min_eq_left hzl]
    omega
  have ready:=source_ready src Z ys cin hs hzl hy s.basis hz hcin H hsrc hys
  have eq:=knownPrefix_eq_mappedPrefix (src.getD 0 0)
    (mappedRead (src++Z.take 5) false) (desired src) ys carry cin geo.1
    (by rw [mappedRead_wires];exact geo.2)
    (by intro q hq;exact geo.2 q (List.mem_append_left _ (desired_source src q hq)))
    (geo.2 _ (List.mem_append_left _ (extra_mem src (by omega))))
    hl (by rw [desired_length src hs];omega) hc s m hclean ready
  simpa only [desired_length src hs,show (5:Nat)-1=4 by decide,mappedPrefix_read] using eq

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem prefixState_preserves (n : Nat) (xs ys cs : List Wire) (cin : Wire) (s : State) (q : Wire)
    (hq:q∉cs.take n) : (prefixState n xs ys cs cin s).basis q=s.basis q := by
  induction n generalizing xs ys cs cin s with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons a as =>
      cases ys with
      | nil => rfl
      | cons b bs =>
        cases cs with
        | nil => rfl
        | cons c cs =>
          simp only [List.take_succ_cons,List.mem_cons,not_or] at hq
          rw [prefixState,ih as bs cs c _ hq.2]
          simp [writeBit,Function.update,hq.1]

theorem carryPrefix_preserves (n : Nat) (xs ys cs : List Wire) (cin : Wire)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State) (m : List Bool) (q : Wire)
    (hq:q∉cs.take n) : (run (carryPrefix n xs ys cs cin) m s).basis q=s.basis q := by
  rw [carryPrefix_run n xs ys cs cin hn s m]
  exact prefixState_preserves n xs ys cs cin s q hq

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem carryPrefix_next_value5 (xs ys carry : List Wire) (cin : Wire)
    (hx:5≤xs.length) (hy:5≤ys.length) (hc:5≤carry.length)
    (hn:(cin::(xs++ys++carry)).Nodup) (s : State)
    (hz:∀q∈carry,s.basis q=false) (hi:s.basis cin=false) :
    (carryBit
      ((run (carryPrefix 4 xs ys carry cin) [] s).basis (xs.getD 4 0))
      ((run (carryPrefix 4 xs ys carry cin) [] s).basis (ys.getD 4 0))
      ((run (carryPrefix 4 xs ys carry cin) [] s).basis (carry.getD 3 0))).toNat=
      (regValue (xs.take 5) s.basis+regValue (ys.take 5) s.basis)/32 := by
  obtain ⟨a0,a1,a2,a3,a4,as,rfl⟩:=shape5 xs hx
  obtain ⟨b0,b1,b2,b3,b4,bs,rfl⟩:=shape5 ys hy
  obtain ⟨c0,c1,c2,c3,c4,cs,rfl⟩:=shape5 carry hc
  let xs:=a0::a1::a2::a3::a4::as
  let ys:=b0::b1::b2::b3::b4::bs
  let carry:=c0::c1::c2::c3::c4::cs
  let t:=run (carryPrefix 4 xs ys carry cin) [] s
  have nd4:[a4,b4,c3,c4].Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro w
    have h:=List.nodup_iff_count_le_one.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ndcs:carry.Nodup := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
  have off:c4∉carry.take 4 := by
    change c4∉[c0,c1,c2,c3]
    intro mem
    have pos:=List.count_pos_iff.mpr mem
    have bound:=List.nodup_iff_count_le_one.mp ndcs c4
    simp only [carry,List.count_cons,List.count_nil] at pos bound
    simp only [beq_self_eq_true,if_true] at bound
    omega
  have clean:t.basis c4=false :=
    (carryPrefix_preserves 4 xs ys carry cin hn s [] c4 off).trans (hz c4 (by simp))
  have split:carryPrefix 5 xs ys carry cin=carryPrefix 4 xs ys carry cin++majority a4 b4 c3 c4 := by
    simp [xs,ys,carry,carryPrefix,List.append_assoc]
  have run5:run (carryPrefix 5 xs ys carry cin) [] s=run (majority a4 b4 c3 c4) [] t := by
    rw [split,run_append]
    simp only [List.take_nil,List.drop_nil,t]
  have v:=carryPrefix_value5 xs ys carry cin hx hy hc hn s [] hz hi
  rw [run5,majority_correct a4 b4 c3 c4 nd4 t [],clean] at v
  change (carryBit (t.basis a4) (t.basis b4) (t.basis c3)).toNat=_
  have get:carry.getD 4 0=c4 := rfl
  rw [get] at v
  simpa only [writeBit,Function.update_self,Bool.false_xor] using v

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem fifth_not_take4 (carry : List Wire) (hc:5≤carry.length) (hn:carry.Nodup) :
    carry.getD 4 0∉carry.take 4 := by
  obtain ⟨c0,c1,c2,c3,c4,cs,rfl⟩:=shape5 carry hc
  change c4∉[c0,c1,c2,c3]
  intro mem
  have pos:=List.count_pos_iff.mpr mem
  have bound:=List.nodup_iff_count_le_one.mp hn c4
  simp only [List.count_cons,List.count_nil] at pos bound
  simp only [beq_self_eq_true,if_true] at bound
  omega

theorem fifth_majority_nd (xs ys carry : List Wire) (cin : Wire)
    (hx:5≤xs.length) (hy:5≤ys.length) (hc:5≤carry.length)
    (hn:(cin::(xs++ys++carry)).Nodup) :
    [xs.getD 4 0,ys.getD 4 0,carry.getD 3 0,carry.getD 4 0].Nodup := by
  obtain ⟨a0,a1,a2,a3,a4,as,rfl⟩:=shape5 xs hx
  obtain ⟨b0,b1,b2,b3,b4,bs,rfl⟩:=shape5 ys hy
  obtain ⟨c0,c1,c2,c3,c4,cs,rfl⟩:=shape5 carry hc
  change [a4,b4,c3,c4].Nodup
  apply List.nodup_iff_count_le_one.mpr
  intro w
  have h:=List.nodup_iff_count_le_one.mp hn w
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.KnownOutputAdder SourceAddFourDevelop Arithmetic.CuccaroStreamedSquareWideLayout

theorem source_prefix_consume_ready (src Z ys carry : List Wire) (cin q : Wire)
    (hs:7≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5)
    (hc:carry.length+1=ys.length)
    (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
    (s : State) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
    (hcin:s.basis cin=false) (H : Nat) (hsrc:regValue src s.basis=H)
    (hys:regValue ys s.basis=976*H/64) (hq:q∉carry) (saved:s.basis q=cacheBit H) :
    let u:=run (knownPrefix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin) [] s
    u.basis (carry.getD 4 0)=false ∧
    u.basis q=carryBit (u.basis ((src++Z.take 5).getD 4 0)) (u.basis (ys.getD 4 0)) (u.basis (carry.getD 3 0)) := by
  let xs:=src++Z.take 5
  let u:=run (knownPrefix (src.getD 0 0) (mappedRead xs false) ys (desired src) carry cin) [] s
  have eu:u=run (carryPrefix 4 xs ys carry cin) [] s := source_prefix_eq src Z ys carry cin hs hzl hy hc hn s [] hz hclean hcin H hsrc hys
  have ndcs:carry.Nodup := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
  have enough:5≤carry.length := by omega
  have member:carry.getD 4 0∈carry := by
    obtain ⟨c0,c1,c2,c3,c4,cs,rfl⟩:=shape5 carry enough
    simp
  have clean:u.basis (carry.getD 4 0)=false := by
    rw [eu]
    exact (carryPrefix_preserves 4 xs ys carry cin hn s [] _ (fifth_not_take4 carry enough ndcs)).trans (hclean _ member)
  have keep:u.basis q=cacheBit H := by
    rw [eu]
    exact (carryPrefix_preserves 4 xs ys carry cin hn s [] q (fun h=>hq (List.mem_of_mem_take h))).trans saved
  have xlen:5≤xs.length := by simp only [xs,List.length_append];omega
  have val:=carryPrefix_next_value5 xs ys carry cin xlen (by omega) enough hn s hclean hcin
  simp only [←eu] at val
  have xvalue:regValue xs s.basis=H := by
    have zv:regValue (Z.take 5) s.basis=0 := (regValue_zero _ _).mpr (fun w hw=>hz w (List.mem_of_mem_take hw))
    simp only [xs,regValue_append,zv,hsrc,Nat.mul_zero,Nat.add_zero]
  rw [regValue_take_mod xs 5 xlen s.basis,regValue_take_mod ys 5 (by omega) s.basis,xvalue,hys] at val
  norm_num only [show 2^5=32 by decide] at val
  rw [carry_return_w64 H] at val
  have known:carryBit (u.basis (xs.getD 4 0)) (u.basis (ys.getD 4 0)) (u.basis (carry.getD 3 0))=cacheBit H :=
    bool_nat_injective _ _ (val.trans (cacheBit_value H).symm)
  exact ⟨clean,keep.trans known.symm⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic SourceAddFourDevelop

theorem consumedAdd_frame (src Z ys carry : List Wire) (cin q : Wire)
    (hs:7≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5) (hc:carry.length+1=ys.length)
    (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
    (hcin:s.basis cin=false) (H : Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64)
    (fresh:q∉carry) (hq:q∉wires (SourceAddFourDevelop.program src Z ys carry cin))
    (saved:s.basis q=cacheBit H) :
    run (consumedAdd src Z ys carry cin q) m s=
      ⟨(run (SourceAddFourDevelop.program src Z ys carry cin) m s).phase,
        writeBit (run (SourceAddFourDevelop.program src Z ys carry cin) m s).basis q false⟩ := by
  have enough:5≤carry.length := by omega
  have split:=add_split src Z ys carry cin hs hy enough
  have off:q∉wires (addPre src Z ys carry cin++
      (majority ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0)++addPost src Z ys carry cin)) := by
    rw [←split]
    exact hq
  simp only [wires_append,Finset.mem_union,not_or] at off
  have nd:=fifth_majority_nd (src++Z.take 5) ys carry cin (by simp only [List.length_append];omega) (by omega) enough hn
  have member:carry.getD 4 0∈carry := by
    obtain ⟨c0,c1,c2,c3,c4,cs,rfl⟩:=shape5 carry enough
    simp
  have ne:q≠carry.getD 4 0 := by intro e;exact fresh (e.symm ▸ member)
  have ready:=source_prefix_consume_ready src Z ys carry cin q hs hzl hy hc hn s hz hclean hcin H hsrc hys fresh saved
  let u:=run (addPre src Z ys carry cin) [] s
  have step:=consume_tail_eq ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0) q nd ne
    (addPost src Z ys carry cin) off.2.2 u m ready.1 ready.2
  have preM:measurementCount (addPre src Z ys carry cin)=0 :=
    (knownPrefix_counts _ _ _ _ _ _).2
  have mm:measurementCount (move q (carry.getD 4 0))=0 := rfl
  have mo:measurementCount (majority ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0))=0 := rfl
  simpa only [consumedAdd,split,run_append,preM,mm,mo,List.take_zero,List.drop_zero,u] using step

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem consumedAdd_resources (src Z ys carry : List Wire) (cin q : Wire)
    (hs:7≤src.length) (hy:ys.length=src.length+5) (hc:5≤carry.length)
    (hq:q∉wires (SourceAddFourDevelop.program src Z ys carry cin))
    (hp:GatePhysical (SourceAddFourDevelop.program src Z ys carry cin)) :
    wires (consumedAdd src Z ys carry cin q)⊆insert q (wires (SourceAddFourDevelop.program src Z ys carry cin)) ∧
    GatePhysical (consumedAdd src Z ys carry cin q) := by
  have split:=add_split src Z ys carry cin hs hy hc
  have cused:carry.getD 4 0∈wires (SourceAddFourDevelop.program src Z ys carry cin) := by
    rw [split,wires_append,wires_append]
    apply Finset.mem_union_right
    apply Finset.mem_union_left
    simp [majority,wires,Instr.wires]
  have ne:q≠carry.getD 4 0 := by intro e;exact hq (e.symm ▸ cused)
  have pp:=hp
  rw [split,gatePhysical_append,gatePhysical_append] at pp
  refine ⟨?_,?_⟩
  · intro x hx
    by_cases eq:x=q
    · exact Finset.mem_insert.mpr (Or.inl eq)
    apply Finset.mem_insert_of_mem
    simp only [consumedAdd,wires_append,Finset.mem_union] at hx
    simp only [split,wires_append,Finset.mem_union]
    rcases hx with hx|(hx|hx)
    · exact Or.inl hx
    · have h:=(consume_support ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0) q) hx
      rcases Finset.mem_insert.mp h with h|h
      · exact False.elim (eq h)
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr hx)
  · simp only [consumedAdd,gatePhysical_append]
    refine ⟨pp.1,?_,pp.2.2⟩
    simp only [move,GatePhysical,List.mem_cons,List.not_mem_nil,or_false]
    intro i hi
    rcases hi with rfl|rfl
    · exact ne
    · exact Ne.symm ne

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def unbuildPre (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)

def unbuildPost (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  SourceTailDevelop.tail acc Z bank cin src++Acc.seedOp acc Z 163 (Acc.earlyTerm src false 4)

def unbuildConsumed (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire) : Program :=
  unbuildPre acc Z bank cin src++consumedAdd src Z ((acc.take 139).drop 6) (bank.take 132) cin q++unbuildPost acc Z bank cin src

theorem unbuild_split (acc Z bank : List Wire) (cin : Wire) (src : List Wire) :
    SourceAddFourDevelop.unbuild acc Z bank cin src=
      unbuildPre acc Z bank cin src++SourceAddFourDevelop.add acc Z bank cin src++unbuildPost acc Z bank cin src := by
  simp only [SourceAddFourDevelop.unbuild,unbuildPre,unbuildPost,List.append_assoc]

theorem unbuildConsumed_counts (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length) :
    toffoliCount (unbuildConsumed acc Z bank cin src q)+1=toffoliCount (SourceAddFourDevelop.unbuild acc Z bank cin src) ∧
    measurementCount (unbuildConsumed acc Z bank cin src q)=measurementCount (SourceAddFourDevelop.unbuild acc Z bank cin src) ∧
    Challenge.gateSlots (unbuildConsumed acc Z bank cin src q)+4=Challenge.gateSlots (SourceAddFourDevelop.unbuild acc Z bank cin src) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:5≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have count:=consumedAdd_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q (by omega) hy hc
  simp only [unbuildConsumed,unbuild_split,SourceAddFourDevelop.add,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic CodexNarrowTail

theorem unbuildPre_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (base : BasisState) (hz:∀q∈Z,base q=false) (hb:∀q∈bank,base q=false) (hi:base cin=false) :
    Triple (SquareFrame acc base (4294968272*regValue src base)) (unbuildPre acc Z bank cin src)
      (SquareFrame acc base (976*regValue src base)) := by
  have tm := NarrowAcc.terms_mem src
  have hf32 := hf _ tm.2.2.2
  let H := regValue src base
  have hH : H<2^128 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have top : Triple (SquareFrame acc base (4294968272*H))
      (CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32))
      (SquareFrame acc base (976*H)) := by
    have h := CodexKnownOnesTail.accSub_prefix_triple acc Z bank cin 163 161 106 (Acc.earlyTerm src false 32) hacc
      (by norm_num [Acc.earlyTerm]) hf32 (by simp only [Acc.earlyTerm]; omega)
      (by norm_num [Acc.earlyTerm]) base hz hb hi (4294968272*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm];dsimp [H];omega)
      (by simpa only [Acc.earlyTerm] using (clear_sub32_range H hH).2.2)
    have value : Acc.step base true (4294968272*H) (Acc.earlyTerm src false 32)=976*H := by
      have e : regValue src base*2^32=4294967296*H := by dsimp only [H]; ring
      simp only [Acc.step,Acc.earlyTerm,if_true]
      rw [e]
      omega
    rw [value] at h
    exact h
  exact top

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem unbuildConsumed_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=4294968272*regValue src s.basis)
    (saved:s.basis q=cacheBit (regValue src s.basis))
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src)) :
    run (unbuildConsumed acc Z bank cin src q) m s=
      setWire (run (SourceAddFourDevelop.unbuild acc Z bank cin src) m s) q false := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (unbuildPre acc Z bank cin src) (m.take (measurementCount (unbuildPre acc Z bank cin src))) s
  have preFrame:=unbuildPre_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s
    (m.take (measurementCount (unbuildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have nd0:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd:(cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa only [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd0
  have bankLen:132≤bank.length := by
    have h:=hf6.bankLen
    norm_num [f,Acc.earlyTerm] at h
    omega
  have zlen:5≤Z.length := by
    have h:=hf6.zpad
    norm_num [f,Acc.earlyTerm,hsrc] at h
    omega
  have sv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
  have pref:=regValue_take_drop_of_lt acc 139 (976*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue ((acc.take 139).drop 6) t.basis=976*H/64 := by
    rw [regValue_drop_div _ 6 (by simp [hacc]),pref.1]
    norm_num
  have zt:∀w∈Z,t.basis w=false := by
    intro w hw
    exact (same w (Or.inl (by simp [hw]))).trans (hz w hw)
  have clean:∀w∈bank.take 132,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=cacheBit H := (preFrame.2.2 q qacc).trans saved
  have qbank:q∉bank.take 132 := by intro bad;exact fresh (by simp [List.mem_of_mem_take bad])
  have pieces:=off
  rw [unbuild_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [hacc,hsrc]
  have hc:(bank.take 132).length+1=((acc.take 139).drop 6).length := by simp [hacc,Nat.min_eq_left bankLen]
  have count:=consumedAdd_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q (by omega) hy (by simp [Nat.min_eq_left bankLen])
  have changed:=consumedAdd_frame src Z ((acc.take 139).drop 6) (bank.take 132) cin q (by omega) zlen hy hc nd t
    ((m.drop (measurementCount (unbuildPre acc Z bank cin src))).take (measurementCount (SourceAddFourDevelop.add acc Z bank cin src)))
    zt clean iv H sv yv qbank pieces.1.2 qt
  have result:=modify_inside (unbuildPre acc Z bank cin src) (SourceAddFourDevelop.add acc Z bank cin src)
    (consumedAdd src Z ((acc.take 139).drop 6) (bank.take 132) cin q) (unbuildPost acc Z bank cin src)
    q false count.2.1 pieces.2 s m changed
  simpa only [unbuildConsumed,unbuild_split] using result

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop

def middleState (F M : Program) (s : State) (tape : List Bool) : State :=
  run M ((tape.drop (measurementCount F)).take (measurementCount M))
    (run F (tape.take (measurementCount F)) s)

theorem cached_pair_eq (F newF M I newI : Program) (q : Wire) (v : Bool)
    (sameM:measurementCount newF=measurementCount F)
    (offF:q∉wires F) (offM:q∉wires M) (offI:q∉wires I)
    (s : State) (tape : List Bool) (zero:s.basis q=false)
    (forward:run newF (tape.take (measurementCount F)) s=
      setWire (run F (tape.take (measurementCount F)) s) q v)
    (inverse:run newI (tape.drop (measurementCount F+measurementCount M)) (setWire (middleState F M s tape) q v)=
      setWire (run I (tape.drop (measurementCount F+measurementCount M)) (setWire (middleState F M s tape) q v)) q false) :
    run (newF++M++newI) tape s=run (F++M++I) tape s := by
  let u:=middleState F M s tape
  let last:=run I (tape.drop (measurementCount F+measurementCount M)) u
  have lastZero:last.basis q=false := by
    dsimp only [last,u,middleState]
    rw [run_preserves_outside I _ _ q offI,run_preserves_outside M _ _ q offM,
      run_preserves_outside F _ _ q offF]
    exact zero
  simp only [run_three,sameM]
  rw [forward,run_setWire M q v offM]
  change run newI (tape.drop (measurementCount F+measurementCount M)) (setWire (middleState F M s tape) q v)=
    run I (tape.drop (measurementCount F+measurementCount M)) (middleState F M s tape)
  rw [inverse,run_setWire I q v offI]
  exact setWire_restore last q v lastZero

theorem cached_pair_counts (F newF M I newI : Program)
    (ft:toffoliCount newF=toffoliCount F) (fm:measurementCount newF=measurementCount F)
    (fs:Challenge.gateSlots newF=Challenge.gateSlots F+1)
    (it:toffoliCount newI+1=toffoliCount I) (im:measurementCount newI=measurementCount I)
    (is:Challenge.gateSlots newI+4=Challenge.gateSlots I) :
    toffoliCount (newF++M++newI)+1=toffoliCount (F++M++I) ∧
    measurementCount (newF++M++newI)=measurementCount (F++M++I) ∧
    Challenge.gateSlots (newF++M++newI)+3=Challenge.gateSlots (F++M++I) := by
  simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem setWire_regValue (xs : List Wire) (s : State) (q : Wire) (v : Bool) (hq:q∉xs) :
    regValue xs (setWire s q v).basis=regValue xs s.basis := by
  apply regValue_congr
  intro w hw
  have ne:w≠q := by intro e;exact hq (e ▸ hw)
  simp [setWire,writeBit,Function.update,ne]

theorem cached_wloop_eq (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire) (middle : Program)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false)
    (fresh:q∉cin::(src++acc++Z++bank))
    (offF:q∉wires (NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
    (offI:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
    (good:let u:=middleState (NarrowAcc.build8 acc Z bank cin src) middle s m
      regValue acc u.basis=4294968272*regValue src s.basis ∧ regValue src u.basis=regValue src s.basis ∧
      (∀w∈Z,u.basis w=false) ∧ (∀w∈bank,u.basis w=false) ∧ u.basis cin=false) :
    run (buildCached acc Z bank cin src q++middle++unbuildConsumed acc Z bank cin src q) m s=
      run (NarrowAcc.build8 acc Z bank cin src++middle++SourceAddFourDevelop.unbuild acc Z bank cin src) m s := by
  let H:=regValue src s.basis
  let u:=middleState (NarrowAcc.build8 acc Z bank cin src) middle s m
  let t:=setWire u q (cacheBit H)
  have qs:q∉src := by intro bad;exact fresh (by simp [bad])
  have qa:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qz:q∉Z := by intro bad;exact fresh (by simp [bad])
  have qb:q∉bank := by intro bad;exact fresh (by simp [bad])
  have qi:cin≠q := by intro e;exact fresh (by simp [←e])
  have keep (w : Wire) (ne:w≠q) : t.basis w=u.basis w := by simp [t,setWire,writeBit,Function.update,ne]
  have sv:regValue src t.basis=H := (setWire_regValue src u q _ qs).trans good.2.1
  have av:regValue acc t.basis=4294968272*regValue src t.basis := by
    rw [show regValue acc t.basis=regValue acc u.basis from setWire_regValue acc u q _ qa,sv]
    exact good.1
  have zt:∀w∈Z,t.basis w=false := by
    intro w hw
    exact (keep w (by intro e;exact qz (e ▸ hw))).trans (good.2.2.1 w hw)
  have bt:∀w∈bank,t.basis w=false := by
    intro w hw
    exact (keep w (by intro e;exact qb (e ▸ hw))).trans (good.2.2.2.1 w hw)
  have it:t.basis cin=false := (keep cin qi).trans good.2.2.2.2
  have saved:t.basis q=cacheBit (regValue src t.basis) := by
    rw [sv]
    simp only [t,setWire,writeBit,Function.update_self]
  have fwd:=buildCached_frame acc Z bank cin src q hacc hsrc hf s
    (m.take (measurementCount (NarrowAcc.build8 acc Z bank cin src))) hz hb hi ha zero fresh offF
  have inv:=unbuildConsumed_frame acc Z bank cin src q hacc hsrc hf t
    (m.drop (measurementCount (NarrowAcc.build8 acc Z bank cin src)+measurementCount middle)) zt bt it av saved fresh offI
  have hf6:=hf _ (NarrowAcc.terms_mem src).2.2.1
  have zl:5≤Z.length := by have h:=hf6.zpad;norm_num [Acc.earlyTerm,hsrc] at h;omega
  have bl:132≤bank.length := by have h:=hf6.bankLen;norm_num [Acc.earlyTerm] at h;omega
  have count:=buildCached_counts acc Z bank cin src q hacc hsrc zl bl
  exact cached_pair_eq _ _ middle _ _ q (cacheBit H) count.2.1 offF offM offI s m zero fwd inv

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem sumCarry_fresh_domain (L : CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
    L.core.sumCarry∉L.core.cin::(hiReg L++accReg L++accZ L++accBank L) := by
  have off:=ParkCarryDevelop.sumCarry_away L hn
  intro h
  apply off
  simp only [List.mem_cons,List.mem_append] at h
  rcases h with h|(((h|h)|h)|h)
  · simp [ParkCarryDevelop.restWires,h]
  · have hp:=List.mem_of_mem_take (List.mem_of_mem_drop h)
    simp [ParkCarryDevelop.restWires,hp]
  · have hp:=accReg_work L _ h
    simp [ParkCarryDevelop.restWires,hp]
  · rcases accZ_mem L _ h with h|h
    · simp only [foldPad,List.mem_append] at h
      rcases h with h|h <;> simp [ParkCarryDevelop.restWires,h]
    · have hp:=List.mem_of_mem_drop h
      simp [ParkCarryDevelop.restWires,hp]
  · have hp:=List.mem_of_mem_take h
    simp only [foldPad,List.mem_append] at hp
    rcases hp with h|h <;> simp [ParkCarryDevelop.restWires,h]

theorem cached_wloop_bstate_eq (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (base : BasisState) (hc:L.PairClean base) (O E O' : Nat) (middle : Program)
    (mid:Triple (BState L base O E (4294968272*regValue (hiReg L) base)) middle
      (BState L base O' E (4294968272*regValue (hiReg L) base)))
    (offF:L.core.sumCarry∉wires (wBuild L)) (offM:L.core.sumCarry∉wires middle)
    (offI:L.core.sumCarry∉wires (wUnbuildKnown L))
    (s : State) (m : List Bool) (hs:BState L base O E 0 s.basis) (zero:s.basis L.core.sumCarry=false) :
    run (buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++middle++
      unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) m s=
      run (wBuild L++middle++wUnbuildKnown L) m s := by
  obtain ⟨hz,hb,hi,_,_⟩:=zero_regs L hn base hc O E 0 s.basis hs
  have source0:regValue (hiReg L) s.basis=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq=>bstate_other L hn base O E 0 s.basis hs q (Or.inl hq))
  apply cached_wloop_eq _ _ _ _ _ _ middle (acc_lengths L hw).1 (hiReg_length L hw)
    (wTerms_fits L hw hn) s m hz hb hi hs.2.2.1 zero (sumCarry_fresh_domain L hn) offF offM offI
  let first:=run (wBuild L) (m.take (measurementCount (wBuild L))) s
  have firstGood:= (wBuild_step L hw hn base hc O E) s (m.take (measurementCount (wBuild L))) hs
  have midGood:=mid first ((m.drop (measurementCount (wBuild L))).take (measurementCount middle)) firstGood.2
  obtain ⟨mz,mb,mi,_,_⟩:=zero_regs L hn base hc O' E _ _ midGood.2
  have source1:=regValue_congr (hiReg L) _ base
    (fun q hq=>bstate_other L hn base O' E _ _ midGood.2 q (Or.inl hq))
  exact ⟨midGood.2.2.2.1.trans (by rw [source0]),source1.trans source0.symm,mz,mb,mi⟩

theorem cached_wloop_bstate_step (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (base : BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
    (O E O' : Nat) (middle : Program)
    (mid:Triple (BState L base O E (4294968272*regValue (hiReg L) base)) middle
      (BState L base O' E (4294968272*regValue (hiReg L) base)))
    (offF:L.core.sumCarry∉wires (wBuild L)) (offM:L.core.sumCarry∉wires middle)
    (offI:L.core.sumCarry∉wires (wUnbuildKnown L)) :
    Triple (BState L base O E 0)
      (buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++middle++
      unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
      (BState L base O' E 0) := by
  intro s m hs
  have away:=ParkCarryDevelop.sumCarry_off_regs L hn
  have zero:s.basis L.core.sumCarry=false := (hs.2.2.2 _ away.1 away.2.1 away.2.2).trans hsum
  rw [cached_wloop_bstate_eq L hw hn base hc O E O' middle mid offF offM offI s m hs zero]
  have old:Triple (BState L base O E 0) (wBuild L++middle++wUnbuildKnown L) (BState L base O' E 0) :=
    ((wBuild_step L hw hn base hc O E).seq mid).seq (wUnbuildKnown_step L hw hn base hc O' E)
  exact old s m hs

end ECDSAAdd.Entrant.InverseCarryDevelop
end



section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem cachedSub_support (x y cs : List Wire) (cin q : Wire)
    (hx:x.length=y.length) (hc:cs.length+1=y.length) (hy:7≤y.length) :
    wires (cachedSub x y cs cin q)⊆insert q (wires (CodexNarrowSub.program x y cs cin)) := by
  have split:=sub_split x y cs cin hx hc hy
  have cused:cs.getD 4 0∈wires (subPre x y cs cin++subPost x y cs cin) := by
    rw [wires_append,subPre,wires_append]
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (carryPrefix_fifth_mem x y cs cin (by omega) (by omega) (by omega)))
  have hs:=insertCopy_support (subPre x y cs cin) (subPost x y cs cin) (cs.getD 4 0) q cused
  simpa only [cachedSub,split] using hs

theorem consumedAdd_support (src Z ys carry : List Wire) (cin q : Wire)
    (hs:7≤src.length) (hy:ys.length=src.length+5) (hc:5≤carry.length) :
    wires (consumedAdd src Z ys carry cin q)⊆insert q (wires (SourceAddFourDevelop.program src Z ys carry cin)) := by
  have split:=add_split src Z ys carry cin hs hy hc
  intro x hx
  by_cases eq:x=q
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [consumedAdd,wires_append,Finset.mem_union] at hx
  simp only [split,wires_append,Finset.mem_union]
  rcases hx with hx|(hx|hx)
  · exact Or.inl hx
  · have h:=(consume_support ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0) q) hx
    rcases Finset.mem_insert.mp h with h|h
    · exact False.elim (eq h)
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hx)

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem buildCached_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    wires (buildCached acc Z bank cin src q)⊆insert q (wires (NarrowAcc.build8 acc Z bank cin src)) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have sub:=cachedSub_support (Acc.tx Z 139 (Acc.earlyTerm src true 6))
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q
    (by omega) (by omega) (by omega)
  intro w hw
  by_cases eq:w=q
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [buildCached,wires_append,Finset.mem_union] at hw
  simp only [build_split,CodexNarrowSub.accSub,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

theorem unbuildConsumed_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length) :
    wires (unbuildConsumed acc Z bank cin src q)⊆insert q (wires (SourceAddFourDevelop.unbuild acc Z bank cin src)) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:5≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have sub:=consumedAdd_support src Z ((acc.take 139).drop 6) (bank.take 132) cin q (by omega) hy hc
  intro w hw
  by_cases eq:w=q
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [unbuildConsumed,wires_append,Finset.mem_union] at hw
  simp only [unbuild_split,SourceAddFourDevelop.add,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

theorem buildCached_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length)
    (off:q∉wires (NarrowAcc.build8 acc Z bank cin src))
    (physical:GatePhysical (NarrowAcc.build8 acc Z bank cin src)) :
    GatePhysical (buildCached acc Z bank cin src q) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have pp:=physical
  rw [build_split,gatePhysical_append,gatePhysical_append] at pp
  have qo:q∉wires (CodexNarrowSub.program (Acc.tx Z 139 (Acc.earlyTerm src true 6))
      (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin) := by
    intro h;apply off
    simp only [build_split,CodexNarrowSub.accSub,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=cachedSub_resources _ _ _ cin q (by omega) (by omega) (by omega) qo pp.1.2
  simp only [buildCached,gatePhysical_append]
  exact ⟨⟨pp.1.1,sub.2⟩,pp.2⟩

theorem unbuildConsumed_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length)
    (off:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
    (physical:GatePhysical (SourceAddFourDevelop.unbuild acc Z bank cin src)) :
    GatePhysical (unbuildConsumed acc Z bank cin src q) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:5≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have pp:=physical
  rw [unbuild_split,gatePhysical_append,gatePhysical_append] at pp
  have qo:q∉wires (SourceAddFourDevelop.program src Z ((acc.take 139).drop 6) (bank.take 132) cin) := by
    intro h;apply off
    simp only [unbuild_split,SourceAddFourDevelop.add,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=consumedAdd_resources src Z ((acc.take 139).drop 6) (bank.take 132) cin q (by omega) hy hc qo pp.1.2
  simp only [unbuildConsumed,gatePhysical_append]
  exact ⟨⟨pp.1.1,sub.2⟩,pp.2⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

def aMiddle (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK++
    (qprogTq L.measuredCore SquareReduction.p++maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK)

theorem a_middle_good (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) (base : BasisState) (hc:L.PairClean base) (O : Nat) (hO:O<SquareReduction.p)
    (s : State) (m : List Bool) (hf:SquareFrame L.core.out base O s.basis) :
    let u:=middleState (wBuild L) (aMiddle L g) s m
    regValue (accReg L) u.basis=4294968272*regValue (hiReg L) s.basis ∧
    regValue (hiReg L) u.basis=regValue (hiReg L) s.basis ∧
    (∀w∈accZ L,u.basis w=false) ∧ (∀w∈accBank L,u.basis w=false) ∧ u.basis L.core.cin=false := by
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
  have offAcc (q : Wire) (hq:q∈hiReg L ∨ q∈L.foldPad ∨ q∈L.core.work.drop 163 ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉accReg L := by
    apply (other_away L hn q ?_).2.2
    tauto
  have source:regValue (hiReg L) v1.basis=regValue (hiReg L) base :=
    (regValue_congr _ _ _ (fun q hq=>frame2.2 q (offAcc q (Or.inl hq)))).trans hhi2
  have zv:∀q∈accZ L,v1.basis q=false := by
    intro q hq
    have na:q∉accReg L := by
      rcases accZ_mem L q hq with h|h
      · exact offAcc q (Or.inr (Or.inl h))
      · apply offAcc q
        have hd:(L.core.work.drop 163).drop 33=L.core.work.drop 196 := by simp [List.drop_drop]
        rw [←hd] at h
        exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h)))
    exact (frame2.2 q na).trans (hz2 q hq)
  have bv:∀q∈accBank L,v1.basis q=false := by
    intro q hq
    exact (frame2.2 q (offAcc q (Or.inr (Or.inl (List.mem_of_mem_take hq))))).trans (hb2 q hq)
  have iv:v1.basis L.core.cin=false :=
    (frame2.2 _ (offAcc _ (by simp))).trans hi2
  have midEq:middleState (wBuild L) (aMiddle L g) s m=v1 := by
    simp only [middleState,aMiddle,run_append,measurementCount_append,
      (maskedConstant_counts _ _ _).2,Nat.zero_add,Nat.add_zero,List.take_zero,List.drop_zero,List.drop_drop]
    dsimp only [v1,v,u1,u,m3,m2,m1,mc,mb,mk]
    simp only [(maskedConstant_counts _ _ _).2,List.take_zero,List.drop_zero,Nat.add_zero,List.take_take,Nat.min_self,List.drop_take,Nat.sub_self]
  rw [midEq]
  exact ⟨frame2.1.trans (by rw [hhi]),source.trans hhi.symm,zv,bv,iv⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem aBody_sumCarry_replace (L : CuccaroStreamedSquareWideLayout) (c q : Wire) :
    aBodyTq {L with core:={L.core with sumCarry:=q} } c=aBodyTq L c := by rfl

theorem aBody_sumCarry_free (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn:L.wires.Nodup) (c : Wire) (hc:c∉L.wires) : L.core.sumCarry∉wires (aBodyTq L c) := by
  let N:CuccaroStreamedSquareWideLayout:={L with core:={L.core with sumCarry:=c} }
  have zm:L.core.sumCarry∈L.wires := by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
  have cz:c≠L.core.sumCarry := by intro h;apply hc;simpa [h] using zm
  have cw:(L.wires).count c=0 := List.count_eq_zero.mpr hc
  have nd:N.wires.Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have old:=List.nodup_iff_count_le_one.mp hn q
    simp only [N,CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil,beq_iff_eq] at cw old ⊢
    by_cases h:q=c
    · subst q
      simp only [if_true] at cw ⊢
      omega
    · simp only [if_neg (Ne.symm h)]
      omega
  have nw: L.core.sumCarry∉N.wires := by
    intro hm
    have pos:=List.count_pos_iff.mpr hm
    have old:=List.nodup_iff_count_le_one.mp hn L.core.sumCarry
    simp only [N,CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil,beq_iff_eq] at pos old
    simp only [if_true,if_neg cz] at pos old
    omega
  have wn:N.Widths := ⟨⟨hw.core.y,hw.core.out,hw.core.product,hw.core.pad,hw.core.work⟩,hw.overflowPad⟩
  have support:=aBody_supportTq N wn nd c
  change wires (aBodyTq {L with core:={L.core with sumCarry:=c} } c)⊆(c::N.wires).toFinset at support
  rw [aBody_sumCarry_replace] at support
  intro hm
  have h:=support hm
  simp only [List.mem_toFinset,List.mem_cons] at h
  exact h.elim (fun h=>cz h.symm) nw

theorem a_wloop_sumCarry_free (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (hn:L.wires.Nodup) (c : Wire) (hc:c∉L.wires) :
    L.core.sumCarry∉wires (wBuild L) ∧
    L.core.sumCarry∉wires (maskedConstant c (accReg L) OwnDiagAll12Square.cFlipK++
      (qprogTq L.measuredCore SquareReduction.p++maskedConstant c (accReg L) OwnDiagAll12Square.cFlipK)) ∧
    L.core.sumCarry∉wires (wUnbuildKnown L) := by
  have h:=aBody_sumCarry_free L hw hn c hc
  simp only [aBodyTq,aFold8Tq,wires_append,Finset.mem_union,not_or] at h ⊢
  tauto

end ECDSAAdd.Entrant.ControlLoan1589BFFold
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

def aFoldCached (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++aMiddle L g++
    unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry

theorem aFoldCached_eq (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) (base : BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
    (O : Nat) (hO:O<SquareReduction.p) (s : State) (m : List Bool) (hf:SquareFrame L.core.out base O s.basis) :
    run (aFoldCached L g) m s=run (aFold8Tq L g) m s := by
  have clean:=L.squareFrame_clean hn base s.basis O hf hc
  have lens:=acc_lengths L hw
  have hz:∀q∈accZ L,s.basis q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact (regValue_zero _ _).mp clean.pad q h
    · exact (regValue_zero _ _).mp clean.work q (List.mem_of_mem_drop h)
  have hb:∀q∈accBank L,s.basis q=false := fun q hq =>
    (regValue_zero _ _).mp clean.pad q (List.mem_of_mem_take hq)
  have ha:regValue (accReg L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp clean.work q (accReg_work L q hq))
  have away:=ParkCarryDevelop.sumCarry_off_regs L hn
  have zero:s.basis L.core.sumCarry=false := (hf.2 _ away.1).trans hsum
  have off:=a_wloop_sumCarry_free L hw hn g hg
  have eq:=cached_wloop_eq (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (aMiddle L g)
    lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) s m hz hb clean.cin ha zero
    (sumCarry_fresh_domain L hn) off.1 off.2.1 off.2.2 (a_middle_good L hw hn g hg base hc O hO s m hf)
  simpa only [aFoldCached,aFold8Tq,aMiddle,List.append_assoc] using eq

theorem aFoldCached_frame (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) (base : BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
    (O : Nat) (hO:O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (aFoldCached L g)
      (SquareFrame L.core.out base (((if base g then OwnDiagAll12Square.cFlipK-4294968272*regValue (hiReg L) base
        else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hs
  rw [aFoldCached_eq L hw hn g hg base hc hsum O hO s m hs]
  exact aFold8_frameTq L hw hn g hg base hc O hO s m hs

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

def aBodyCached (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++aFoldCached L c)

theorem aBodyCached_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hzero:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (aBodyCached L c) (SquareFrame L.core.out base (resAF (M^2) O (base c))) := by
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
  have t3 := aFoldCached_frame L hw hn c hcw base hc hzero O2 hO2
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

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic ParkCarryDevelop

theorem cached_wloop_le (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire) (middle : Program)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    ExtraLe q (buildCached acc Z bank cin src q++middle++unbuildConsumed acc Z bank cin src q)
      (NarrowAcc.build8 acc Z bank cin src++middle++SourceAddFourDevelop.unbuild acc Z bank cin src) := by
  have b:=buildCached_support acc Z bank cin src q ha hs hz hb
  have u:=unbuildConsumed_support acc Z bank cin src q ha hs hb
  have bc:=buildCached_counts acc Z bank cin src q ha hs hz hb
  have uc:=unbuildConsumed_counts acc Z bank cin src q ha hs hb
  constructor
  · intro w hw
    by_cases eq:w=q
    · exact Finset.mem_insert.mpr (Or.inl eq)
    apply Finset.mem_insert_of_mem
    simp only [wires_append,Finset.mem_union] at hw ⊢
    rcases hw with (hw|hw)|hw
    · have h:=Finset.mem_insert.mp (b hw)
      exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inl h))
    · exact Or.inl (Or.inr hw)
    · have h:=Finset.mem_insert.mp (u hw)
      exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inr h)
  · simp only [Challenge.gateSlots_append]
    omega

theorem extraLe_refl (q : Wire) (P : Program) : ExtraLe q P P :=
  ⟨fun _ h=>Finset.mem_insert_of_mem h,le_refl _⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop

theorem aBodyCached_counts (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire) :
    toffoliCount (aBodyCached L c)=2917 ∧ measurementCount (aBodyCached L c)=3077 := by
  have old:=aBody_countsTq L hw c
  have lens:=acc_lengths L hw
  have wb:=buildCached_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
    lens.1 (hiReg_length L hw) (by omega) (by omega)
  have wu:=unbuildConsumed_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
    lens.1 (hiReg_length L hw) (by omega)
  simp only [aBodyCached,aFoldCached,aMiddle,aBodyTq,aFold8Tq,wBuild,wUnbuildKnown,
    toffoliCount_append,measurementCount_append] at old ⊢
  constructor <;> omega

theorem aBodyCached_le (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire) :
    ExtraLe L.core.sumCarry (aBodyCached L c) (aBodyTq L c) := by
  have lens:=acc_lengths L hw
  have loop:=cached_wloop_le (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (aMiddle L c)
    lens.1 (hiReg_length L hw) (by omega) (by omega)
  have all:=ExtraLe.app (extraLe_refl L.core.sumCarry (measuredFoldQTq L (negP L)))
    (ExtraLe.app (extraLe_refl L.core.sumCarry (measuredFoldQTq L (rot128F L))) loop)
  simpa only [aBodyCached,aFoldCached,aMiddle,aBodyTq,aFold8Tq,wBuild,wUnbuildKnown,List.append_assoc] using all

theorem aBodyCached_rel (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire) :
    toffoliCount (aBodyCached L c)+129=toffoliCount (aBody L c) ∧
    measurementCount (aBodyCached L c)+3=measurementCount (aBody L c) ∧
    ExtraLe L.core.sumCarry (aBodyCached L c) (aBody L c) := by
  have count:=aBodyCached_counts L hw c
  have old:=aBody_countsTq L hw c
  have rel:=QRel.aBody_rel L hw c
  have le:=aBodyCached_le L hw c
  refine ⟨by omega,by omega,?_,le.2.trans rel.2.2.2⟩
  intro q hq
  have h:=Finset.mem_insert.mp (le.1 hq)
  exact h.elim (fun e=>Finset.mem_insert.mpr (Or.inl e)) (fun h=>Finset.mem_insert_of_mem (rel.2.2.1 h))

theorem aBodyCached_physical (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire)
    (hn:(c::L.wires).Nodup) : GatePhysical (aBodyCached L c) := by
  have nd:=(List.nodup_cons.mp hn).2
  have hc:=(List.nodup_cons.mp hn).1
  have off:=a_wloop_sumCarry_free L hw nd c hc
  have lens:=acc_lengths L hw
  have wb:=CodexNarrowTail.build8_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw nd)
  rw [CodexNarrowTail.build8_eq] at wb
  have bp:=buildCached_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
    lens.1 (hiReg_length L hw) (by omega) (by omega) off.1 wb.1
  have up:=unbuildConsumed_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
    lens.1 (hiReg_length L hw) (by omega) off.2.2 (wUnbuildKnown_physical L hw nd)
  have old:=aBody_physicalTq L hw c hn
  simp only [aBodyCached,aFoldCached,aMiddle,aBodyTq,aFold8Tq,gatePhysical_append] at old ⊢
  tauto

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop

def hostedA (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
  aBodyCached (hostLayout L rho) c

theorem oldA_host (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) :
    aBody (hostLayout L rho) c=aBody L c := by rfl

theorem hostedA_rel (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho : Equiv.Perm Wire) (c : Wire) :
    toffoliCount (hostedA L rho c)+129=toffoliCount (aBody L c) ∧
    measurementCount (hostedA L rho c)+3=measurementCount (aBody L c) ∧
    ExtraLe (rho.symm L.core.sumCarry) (hostedA L rho c) (aBody L c) := by
  have h:=aBodyCached_rel (hostLayout L rho) (host_widths L hw rho) c
  simpa only [hostedA,oldA_host,hostLayout] using h

theorem hostedA_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire)
    (h:rho L.core.sumCarry=L.core.sumCarry) : hostedA L rho c=aBodyCached L c := by
  rw [hostedA,host_eq L rho h]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem bBody_sumCarry_free (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn:L.wires.Nodup) (c : Wire) (hc:c∉L.wires) : L.core.sumCarry∉wires (bBodyTq L c) := by
  let N:CuccaroStreamedSquareWideLayout:={L with core:={L.core with sumCarry:=c} }
  have zm:L.core.sumCarry∈L.wires := by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
  have cz:c≠L.core.sumCarry := by intro h;apply hc;simpa [h] using zm
  have cw:(L.wires).count c=0 := List.count_eq_zero.mpr hc
  have nd:N.wires.Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have old:=List.nodup_iff_count_le_one.mp hn q
    simp only [N,CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil,beq_iff_eq] at cw old ⊢
    by_cases h:q=c
    · subst q
      simp only [if_true] at cw ⊢
      omega
    · simp only [if_neg (Ne.symm h)]
      omega
  have nw: L.core.sumCarry∉N.wires := by
    intro hm
    have pos:=List.count_pos_iff.mpr hm
    have old:=List.nodup_iff_count_le_one.mp hn L.core.sumCarry
    simp only [N,CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil,beq_iff_eq] at pos old
    simp only [if_true,if_neg cz] at pos old
    omega
  have wn:N.Widths := ⟨⟨hw.core.y,hw.core.out,hw.core.product,hw.core.pad,hw.core.work⟩,hw.overflowPad⟩
  have support:=bBody_supportTq N wn nd c
  change wires (bBodyTq {L with core:={L.core with sumCarry:=c} } c)⊆(c::N.wires).toFinset at support
  rw [bBody_sumCarry_replace] at support
  intro hm
  have h:=support hm
  simp only [List.mem_toFinset,List.mem_cons] at h
  exact h.elim (fun h=>cz h.symm) nw

end ECDSAAdd.Entrant.ControlLoan1589BFFold
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem b_wloop_sumCarry_free (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (hn:L.wires.Nodup) (c : Wire) (hc:c∉L.wires) :
    L.core.sumCarry∉wires (wBuild L) ∧
    L.core.sumCarry∉wires (wFwdK L++(wCoreK L++wInvK L)) ∧
    L.core.sumCarry∉wires (wUnbuildKnown L) := by
  have h:=bBody_sumCarry_free L hw hn c hc
  simp only [bBodyTq,wFoldTq,wires_append,Finset.mem_union,not_or] at h ⊢
  tauto

end ECDSAAdd.Entrant.ControlLoan1589BFFold
end
