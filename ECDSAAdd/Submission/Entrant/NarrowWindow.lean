import ECDSAAdd.Submission.Entrant.QTop
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
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

set_option maxHeartbeats 1000000 in
theorem wMidK_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E b1 : Nat) (hb1 : regValue (hiReg L) base = b1)
    (hb1lt : b1 < 2^128) (hO : O < SquareReduction.p)
    (H l K : Nat) (hH : H < 2^96) (hl : l < 2^32) (hK : K ≤ 1) (hE : E = 2^32*H + l + 2^128*K) :
    Triple (BState L base O E (4294968272*b1)) (wFwdK L ++ (wCoreK L ++ wInvK L))
      (BState L base (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 4294968272*2^32*K +
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
  have eA := eU_away L hw hn
  have heR : eU L ∉ mR L := fun hr => eA.2.1 (mR_work L _ hr)
  have heS : eU L ∉ mS L := fun hs => eA.1 (mS_pad L _ hs)
  have heZ : eU L ∉ mZ L := fun hz => eA.1 (mZ_pad L _ hz)
  have wf := w192_facts L hw hn
  have key : (if s.basis (eU L) = true then 1 else 0) = K := by
    have hv := eReg_split L hw s.basis
    rw [h.2.1, hE] at hv
    have a1 := eLo_lt L hw s.basis
    have a2 := eMid_lt L hw s.basis
    cases e1 : s.basis (eU L) <;> cases e2 : s.basis (eV L) <;>
      simp only [e1, e2, Bool.false_eq_true, if_false, if_true] at hv ⊢ <;> omega
  have hkU : s.basis (eU L) = decide (K = 1) := by
    cases e : s.basis (eU L) <;> simp only [e, Bool.false_eq_true, if_false, if_true] at key <;> simp <;> omega
  have T1 : Triple (WinArith.PS (mR L) (mS L) s.basis (u+d) 0) (wFwdK L)
      (WinArith.PS (mR L) (mS L) s.basis (u + 4294968273*d + 2^32*(976*K)) 0) := by
    have := WinArith.tFwdK_spec g cl u d hU hu32 ws2 (eU L) heR heS heZ (by omega)
    rw [key] at this; exact this
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hX : (u + 4294968273*d + 4294968272*2^32*K) + 2^128*(W%2^128) < SquareReduction.p := by
    have b := Nat.mod_lt W (show 2^128>0 by positivity)
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at b hu32 ws2 ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hK with hk | hk <;> subst hk <;> omega
  -- frame facts of the start state
  have wnd : L.core.work.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have := lay_pos L hn q; omega
  have keepS (q : Wire) (h1 : q ∉ L.core.out) (h2 : q ∉ eReg L) (h3 : q ∉ accReg L) : s.basis q = base q :=
    h.2.2.2 q h1 h2 h3
  let O' := ((u + 4294968273*d) + 4294968272*2^32*K + 2^128*(W%2^128) + (SquareReduction.p-1-O)) % SquareReduction.p
  let Q2 : BasisState → Prop := fun x => regValue L.core.out x = O' ∧ regValue (mR L) x = u + 4294968273*d + 2^32*(976*K) ∧
    regValue (mS L) x = 0 ∧ ∀ q, q ∉ L.core.out → q ∉ mR L → q ∉ mS L → x q = s.basis q
  have T2 : Triple (WinArith.PS (mR L) (mS L) s.basis (u + 4294968273*d + 2^32*(976*K)) 0) (wCoreK L) Q2 := by
    intro s1 m1 h1
    have keep0 (q : Wire) (a : q ∉ mR L) (b : q ∉ mS L) : s1.basis q = s.basis q := h1.2.2 q a b
    have w0 : s1.basis (w192 L) = false := (keep0 _ wf.2.2.1 wf.2.2.2.1).trans (workZ _ wf.2.1)
    have ek1 : s1.basis (eU L) = decide (K = 1) := (keep0 _ heR heS).trans hkU
    let s1' : State := ⟨s1.phase, writeBit s1.basis (w192 L) (s1.basis (w192 L) ^^ s1.basis (eU L))⟩
    have r1 : ∀ mm, run (kw L) mm s1 = s1' := by intro mm; simp [kw, run, s1']
    have b1' : ∀ q, q ≠ w192 L → s1'.basis q = s1.basis q := by
      intro q hq; simp [s1', writeBit, Function.update_apply, hq]
    have bw : s1'.basis (w192 L) = decide (K = 1) := by simp [s1', writeBit, w0, ek1]
    have keep (q : Wire) (a : q ∉ mR L) (b : q ∉ mS L) (c : q ≠ w192 L) : s1'.basis q = s.basis q :=
      (b1' q c).trans (keep0 q a b)
    have nw_out (q : Wire) (hq : q ∈ L.core.out) : q ≠ w192 L := fun e => wf.2.2.2.2.1 (e ▸ hq)
    have nw_pad (q : Wire) (hq : q ∈ L.foldPad) : q ≠ w192 L := fun e => work_pad L hn _ wf.1 (e ▸ hq)
    have nw_lo (q : Wire) (hq : q ∈ L.core.work.take 128) : q ≠ w192 L := by
      intro e
      have c := List.nodup_iff_count_le_one.mp wnd q
      have sp := congrArg (List.count q) (List.take_append_drop 128 L.core.work)
      have a1 := List.count_pos_iff.mpr hq
      have a2 : 0 < (L.core.work.drop 128).count q := by
        rw [e]; exact List.count_pos_iff.mpr (List.mem_of_mem_drop (w192_tail L hw))
      simp only [List.count_append] at sp; omega
    have nw_R (q : Wire) (hq : q ∈ mR L) : q ≠ w192 L := fun e => wf.2.2.1 (e ▸ hq)
    have outv : regValue L.core.out s1'.basis = O :=
      (regValue_congr _ _ _ (fun q hq => keep q (fun hr => (m_away L hn q (Or.inl hr)).1 hq)
        (fun hs => (m_away L hn q (Or.inr hs)).1 hq) (nw_out q hq))).trans h.1
    have sg (q : Wire) (hq : q ∈ [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
        L.core.modFlag,L.core.sumCarry]) : s1'.basis q = s.basis q :=
      keep q (fun hr => (sing_away L hn q hq).1 (mR_work L q hr)) (fun hs => (sing_away L hn q hq).2.1 (mS_pad L q hs))
        (fun e => (sing_away L hn q hq).1 (e ▸ wf.1))
    have bo (q : Wire) (hq : q = L.core.productHigh ∨ q = L.core.outHigh ∨ q = L.core.workHigh ∨ q = L.core.cin ∨
        q = L.core.modFlag) : s.basis q = base q :=
      bstate_other L hn base O E W s.basis h q (Or.inr (Or.inr (Or.inr (by rcases hq with rfl|rfl|rfl|rfl|rfl <;> simp))))
    have padS (q : Wire) (hq : q ∈ L.foldPad) : s1'.basis q = false := by
      rw [b1' q (nw_pad q hq)]
      by_cases hs : q ∈ mS L
      · exact (regValue_zero _ _).mp h1.2.1 q hs
      · exact (keep0 q (fun hr => work_pad L hn q (mR_work L q hr) hq) hs).trans (padZ q hq)
    have carryZ : ∀q∈(rotWCore L).carry,s1'.basis q=false := by
      intro q hq
      simp only [rotWCore,measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq|rfl|rfl
      · exact padS q hq
      · exact ((sg _ (by simp)).trans (bo _ (Or.inl rfl))).trans hc.productHigh
      · exact ((sg _ (by simp)).trans (bo _ (Or.inr (Or.inr (Or.inl rfl))))).trans hc.workHigh
    have srcv : regValue (rotWCore L).src s1'.basis = (u + 4294968273*d + 4294968272*2^32*K) + 2^128*(W%2^128) := by
      show regValue (rotWork L) s1'.basis = _
      rw [rotWork, regValue_append]
      have l128 : (L.core.work.drop 128).length = 128 := by simp [hw.core.work]
      have hlo : regValue (L.core.work.take 128) s1'.basis = W % 2^128 := by
        rw [regValue_congr _ _ (s.basis) (fun q hq => keep q
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs)) (nw_lo q hq)),
          WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
      have hhi : regValue (L.core.work.drop 128) s1'.basis = u + 4294968273*d + 4294968272*2^32*K := by
        have sp := regValue_append ((L.core.work.drop 128).take 43) ((L.core.work.drop 128).drop 43) s1'.basis
        rw [List.take_append_drop] at sp
        have z : regValue ((L.core.work.drop 128).drop 43) s1'.basis = 2^21 * K := by
          apply tail_value L hw hn s1'.basis K hK bw
          intro q hq hne
          have hq0 := hq
          rw [List.drop_drop] at hq
          have hq' : q ∈ L.core.work.drop (128+43) := hq
          rw [keep q (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq') hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_drop hq') (mS_pad L q hs)) hne]
          apply workZ
          have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
          rw [this] at hq'
          exact List.mem_of_mem_drop hq'
        have rv : regValue ((L.core.work.drop 128).take 43) s1'.basis = u + 4294968273*d + 2^32*(976*K) := by
          show regValue (mR L) s1'.basis = _
          rw [regValue_congr _ _ s1.basis (fun q hq => b1' q (nw_R q hq))]
          exact h1.1
        rw [sp, z, rv]
        have : ((L.core.work.drop 128).take 43).length = 43 := by simp [hw.core.work]
        rw [this]; ring
      rw [hhi, hlo, l128]
    have mk0 : measurementCount (kw L) = 0 := by simp [kw, measurementCount]
    rw [wCoreK, run_append, r1, mk0, List.drop_zero, run_append]
    rw [show wCoreTq L = qprogTq (rotWCore L) SquareReduction.p from rfl]
    have ek := QCore.qprog_correctTq (rotWCore L) 256 SquareReduction.c SquareReduction.p (rotWCore_widths L hw)
      (rotWCore_nodup L hn) (by decide) hp (by norm_num [SquareReduction.c]) _ O hX hO s1'
      (m1.take (measurementCount (qprogTq (rotWCore L) SquareReduction.p))) srcv outv
      (show s1'.basis L.core.outHigh = false from
        (sg L.core.outHigh (by simp)).trans ((bo _ (Or.inr (Or.inl rfl))).trans hc.outHigh))
      (show s1'.basis L.core.modFlag = false from
        (sg L.core.modFlag (by simp)).trans ((bo _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans hc.modFlag)) carryZ
      (show s1'.basis L.core.cin = false from (sg L.core.cin (by simp)).trans hi)
    generalize hr : run (qprogTq (rotWCore L) SquareReduction.p)
      (m1.take (measurementCount (qprogTq (rotWCore L) SquareReduction.p))) s1' = r at ek ⊢
    have rw' : r.basis (w192 L) = decide (K = 1) := (ek.2.2 _ wf.2.2.2.2.1).trans bw
    have re : r.basis (eU L) = decide (K = 1) := by
      rw [ek.2.2 _ eA.2.2, b1' _ (fun e => wf.2.2.2.2.2.1 e.symm), ek1]
    have fin : ∀ mm, run (kw L) mm r = ⟨r.phase, writeBit r.basis (w192 L) false⟩ := by
      intro mm; simp [kw, run, rw', re]
    rw [fin]
    have fb : ∀ q, q ≠ w192 L → (writeBit r.basis (w192 L) false) q = r.basis q := by
      intro q hq; simp [writeBit, Function.update_apply, hq]
    refine ⟨ek.1, ?_, ?_, ?_, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => fb q (nw_out q hq))).trans ek.2.1
    · rw [regValue_congr _ _ r.basis (fun q hq => fb q (nw_R q hq))]
      exact (regValue_congr _ _ _ (fun q hq => (ek.2.2 q (m_away L hn q (Or.inl hq)).1).trans
        (b1' q (nw_R q hq)))).trans h1.1
    · rw [regValue_congr _ _ r.basis (fun q hq => fb q (fun e => wf.2.2.2.1 (e ▸ hq)))]
      exact (regValue_congr _ _ _ (fun q hq => (ek.2.2 q (m_away L hn q (Or.inr hq)).1).trans
        (b1' q (fun e => wf.2.2.2.1 (e ▸ hq))))).trans h1.2.1
    · intro q a b c
      by_cases hq : q = w192 L
      · subst hq; simp [writeBit]; exact workZ _ wf.2.1
      · show writeBit r.basis (w192 L) false q = s.basis q
        rw [fb q hq, ek.2.2 q a, b1' q hq]; exact keep0 q b c
  let Q3 : BasisState → Prop := fun x => regValue L.core.out x = O' ∧ regValue (mR L) x = u + d ∧
    regValue (mS L) x = 0 ∧ ∀ q, q ∉ L.core.out → q ∉ mR L → q ∉ mS L → x q = s.basis q
  have T3 : Triple Q2 (wInvK L) Q3 := by
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
    have ke : (if s2.basis (eU L) = true then 1 else 0) = K := by
      rw [k2 _ eA.2.2 heR heS]; exact key
    have P2 : WinArith.PS (mR L) (mS L) s2.basis
        (u + 4294968273*d + 2^32*(976*(if s2.basis (eU L) = true then 1 else 0))) 0 s2.basis :=
      ⟨by rw [ke]; exact h2.2.1, h2.2.2.1, fun _ _ _ => rfl⟩
    obtain ⟨ph, h3⟩ := WinArith.tInvK_spec g cl2 u d hU2 hu32 ws2 (eU L) heR heS heZ (by omega) s2 m2 P2
    refine ⟨ph, ?_, h3.1, h3.2.1, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => h3.2.2 q (fun hr => (m_away L hn q (Or.inl hr)).1 hq)
        (fun hs => (m_away L hn q (Or.inr hs)).1 hq))).trans h2.1
    · intro q a b c; exact (h3.2.2 q b c).trans (k2 q a b c)
  obtain ⟨ph, f⟩ := (T1.seq (T2.seq T3)) s m P0
  refine ⟨ph, f.1, ?_, ?_, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => f.2.2.2 q (eReg_away L hn q hq).1
      (fun hr => (m_away L hn q (Or.inl hr)).2 hq) (fun hs => (m_away L hn q (Or.inr hs)).2 hq))).trans h.2.1
  · -- the work register is `W` again
    have wv : regValue L.core.work (run (wFwdK L ++ (wCoreK L ++ wInvK L)) m s).basis = W := by
      rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
      have lo : regValue (L.core.work.take 128) (run (wFwdK L ++ (wCoreK L ++ wInvK L)) m s).basis = W % 2^128 := by
        rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
          WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
      have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdK L ++ (wCoreK L ++ wInvK L)) m s).basis = 0 := by
        apply (regValue_zero _ _).mpr
        intro q hq
        rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
        apply workZ
        have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
        rw [this] at hq
        exact List.mem_of_mem_drop hq
      have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdK L ++ (wCoreK L ++ wInvK L)) m s).basis = u + d :=
        f.2.1
      rw [lo, mr, hi0]
      omega
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) (run (wFwdK L ++ (wCoreK L ++ wInvK L)) m s).basis
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
      have wv : regValue L.core.work (run (wFwdK L ++ (wCoreK L ++ wInvK L)) m s).basis = W := by
        rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
        have lo : regValue (L.core.work.take 128) (run (wFwdK L ++ (wCoreK L ++ wInvK L)) m s).basis = W % 2^128 := by
          rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
            WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
        have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdK L ++ (wCoreK L ++ wInvK L)) m s).basis = 0 := by
          apply (regValue_zero _ _).mpr
          intro q hq
          rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
          apply workZ
          have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
          rw [this] at hq
          exact List.mem_of_mem_drop hq
        have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdK L ++ (wCoreK L ++ wInvK L)) m s).basis = u + d :=
          f.2.1
        rw [lo, mr, hi0]
        omega
      have z : regValue (L.core.work.drop 163) (run (wFwdK L ++ (wCoreK L ++ wInvK L)) m s).basis = 0 := by
        rw [WinArith.drop_div _ _ (by simp [hw.core.work]), wv, Nat.div_eq_of_lt hWlt]
      rw [(regValue_zero _ _).mp z q hd163]
      exact ((regValue_zero _ _).mp hc.work q wq).symm
    by_cases hs : q ∈ mS L
    · rw [(regValue_zero _ _).mp f.2.2.1 q hs]
      exact ((regValue_zero _ _).mp hc.pad q (mS_pad L q hs)).symm
    · exact (f.2.2.2 q h1 hr hs).trans (keepS q h1 h2 h3)



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


namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
def wFoldN (L : CuccaroStreamedSquareWideLayout) : Program :=
  eAddLo L++(wBuild L++((wFwdK L++(wCoreK L++wInvK L))++(wUnbuildKnown L++(kapClr L++eSubK L))))

/-- The restore: `+b1`, then the low-window `-u`.
No rebuild of `W`; 733 no-op measurements keep the measurement count of the B body. -/
def wRestoreN (L : CuccaroStreamedSquareWideLayout) : Program :=
  eAddB L++(eSubLo L++padM L 721)

def bBodyN (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(wFoldN L++(eFoldTq L c++wRestoreN L)))


theorem bBodyN_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (bBodyN L c) (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
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
  let H := b0/2^32
  let l' := (b0%2^32 + u)%2^32
  let K := (b0%2^32 + u)/2^32
  let O3 := ((u + 4294968273*d) + 4294968272*2^32*K + 2^128*(W%2^128) + (SquareReduction.p-1-O2)) % SquareReduction.p
  let E1 := (2^32*H + l' + 2^130 - b1) % 2^130
  let O4 := (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
  have hu32 : u < 2^32 := by
    show b1/2^96 < 2^32
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc b1<2^128 := hb1lt
      _ = 2^32*2^96 := by norm_num
  have hH : H < 2^96 := by show b0/2^32 < 2^96; omega
  have hl' : l' < 2^32 := Nat.mod_lt _ (by positivity)
  have hK : K ≤ 1 := by show (b0%2^32 + u)/2^32 ≤ 1; omega
  have hKif : (if l' < u then 1 else 0) = K := by
    show (if (b0%2^32 + u)%2^32 < u then 1 else 0) = (b0%2^32 + u)/2^32
    by_cases hc' : (b0%2^32 + u)%2^32 < u
    · rw [if_pos hc']; omega
    · rw [if_neg hc']; omega
  -- wFoldN
  have k1 := eAddLo_step L hw hn base hc O2 0 b0 hb0
  rw [hb1] at k1
  have w1 := wBuild_step L hw hn base hc O2 (2^32*H + l' + 2^128*K)
  rw [hb1] at w1
  have wm := wMidK_step L hw hn base hc O2 (2^32*H + l' + 2^128*K) b1 hb1 hb1lt hO2 H l' K hH hl' hK rfl
  have w5 := wUnbuildKnown_step L hw hn base hc O3 (2^32*H + l' + 2^128*K)
  rw [hb1] at w5
  have kc := kapClr_step L hw hn base hc O3 0 H l' hH hl'
  rw [hb1] at kc
  change Triple (BState L base O3 (2^32*H + l' + 2^128*(if l' < u then 1 else 0)) 0) (kapClr L)
    (BState L base O3 (2^32*H + l') 0) at kc
  rw [hKif] at kc
  have w3 := eSubK_step L hw hn base hc O3 (2^32*H + l') 0 b1 (by omega) hb1
  have tw : Triple (BState L base O2 b0 0) (wFoldN L) (BState L base O3 E1 0) :=
    k1.seq (w1.seq (wm.seq (w5.seq (kc.seq w3))))
  -- eFoldTq
  have f1 := eFlip_step L hw hn base c hcw O3 E1 0
  have f2 := eCore_stepTq L hw hn base hc O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn base c hcw O4 (flipE g E1) 0
  rw [flipE_flipE] at f3
  have tf : Triple (BState L base O3 E1 0) (eFoldTq L c) (BState L base O4 E1 0) :=
    f1.seq (f2.seq f3)
  -- wRestoreN
  have bk : (E1+b1)%2^130 = 2^32*H + l' := by show ((2^32*H + l' + 2^130 - b1) % 2^130 + b1) % 2^130 = _; omega
  have r2 := eAddB_step L hw hn base hc O4 E1 0 b1 hb1 (by rw [bk]; omega)
  rw [bk] at r2
  have r3 := eSubLo_step L hw hn base hc O4 0 H l' hH hl'
  rw [hb1] at r3
  have bb : 2^32*H + (l' + 2^32 - u) % 2^32 = b0 := by
    show 2^32*(b0/2^32) + ((b0%2^32 + u)%2^32 + 2^32 - u) % 2^32 = b0; omega
  rw [bb] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 721
  have tr : Triple (BState L base O4 E1 0) (wRestoreN L) (BState L base O4 b0 0) :=
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
    have e3 : O3 = (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p := by
      simp only [O3, u, d, K, W]
      congr 1; ring
    have e4 : O4 = (4294968272*flipE g ((2^32*(b0/2^32) + (b0%2^32+b1/2^96)%2^32 + 2^130 - b1) % 2^130) +
        (SquareReduction.p-1-((((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p))) % SquareReduction.p := by
      show (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p = _
      rw [e3]
    rw [e4, o4K b0 b1 O2 _ g hb0 hb1lt hO2 hg']
    exact o4_eq b0 b1 O2 g hb0 hb1lt hO2 hg'
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tf.seq tr)) conv2))
  rw [key] at all
  exact all

theorem bBodyN_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (bBodyN L c)=4804 ∧ measurementCount (bBodyN L c)=5924 := by
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
  have pd := padM_counts L 721
  simp only [bBodyN,wFoldN,wCoreK,eFoldTq,wRestoreN,toffoliCount_append,measurementCount_append,q1.1,q1.2,q2.1,q2.2,
    wb.1,wb.2,wu.1,wu.2,wc.1,wc.2,s1k.1,s1k.2,a1b.1,a1b.2,fl.1,fl.2,ac.1,ac.2,fw.1,fw.2,iv.1,iv.2,kc.1,kc.2,
    lc.1,lc.2.1,lc.2.2.1,lc.2.2.2.1,lc.2.2.2.2.1,lc.2.2.2.2.2,pd.1,pd.2]
  exact ⟨trivial,trivial⟩

theorem bBodyN_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (hn : (c::L.wires).Nodup) : GatePhysical (bBodyN L c) := by
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
  simp only [bBodyN,wFoldN,wCoreK,eFoldTq,wRestoreN,gatePhysical_append]
  exact ⟨p1,p2,⟨eAddLo_physical L hw nd,wb.1,⟨WinArith.tFwdK_physical g (eU L) heZ,⟨kw_physical L hw nd,wc,
    kw_physical L hw nd⟩,WinArith.tInvK_physical g (eU L) heZ⟩,wUnbuildKnown_physical L hw nd,kapClr_physical L hw nd,eSubK_physical L hw nd⟩,
    ⟨fl,ac,fl⟩,⟨eAddB_physical L hw nd,eSubLo_physical L hw nd,padM_physical L 721⟩⟩

theorem bBodyN_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    QRel.Le (bBodyN L c) (bBody L c) := by
  unfold bBodyN bBody
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
    simp only [wFoldN, wCoreK, wRestoreN, wires_append, Finset.mem_union] at hq
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
    · exact hOE (eSubLo_oldE L hw h)
    · exact hOE (padM_oldE L hw 721 h)
  · have wc := (QRel.qprog_le (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)).2
    have ef := (QRel.eFold_le L hw c).2
    have sk := eSubK_slots L hw
    have ab := eAddB_slots L hw
    have f1 := WinArith.tFwdK_slots (cin := L.core.cin) (mLens L hw) (eU L)
    have f2 := WinArith.tInvK_slots (cin := L.core.cin) (mLens L hw) (eU L)
    have f5 := padM_slots L 721
    have g1 := wBuild_slots_ge L hw
    have g2 := wUnbuild_slots_ge L hw
    have wun := wUnbuildKnown_slots L hw
    have k1 := kw_slots L
    have e1 := eAddLo_slots L hw
    have e2 := kapClr_slots L hw
    have e3 := eSubLo_slots L hw
    have l2 := eSrc_length L hw (whiSrc L) (Or.inr rfl)
    have wa := KnownTopAdd.addInPlace_slots_eq (whiSrc L) (eReg L) (eBank L) L.core.cin l2.1 l2.2
    rw [eReg_length L hw] at wa
    simp only [wFoldN, wRestoreN, wCoreK, wFold, wRestore, wFwdK, wInvK, wCoreTq, wCore, eAdd,
      Challenge.gateSlots_append] at *
    omega


theorem bBodyN_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (c : Wire) :
 ECDSAAdd.wires (bBodyN L c)⊆(c::L.wires).toFinset := (bBodyN_le L hw c).1.trans (bBody_support L hw hn c)
theorem bBodyN_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (bBodyN L c)+1019=toffoliCount (bBody L c) ∧
 measurementCount (bBodyN L c)+4=measurementCount (bBody L c) ∧ QRel.Le (bBodyN L c) (bBody L c) := by
 have a:=bBodyN_counts L hw c
 have b:=bBody_counts L hw c
 exact ⟨by omega,by omega,bBodyN_le L hw c⟩

end ECDSAAdd.Entrant.ControlLoan1589BFFold
