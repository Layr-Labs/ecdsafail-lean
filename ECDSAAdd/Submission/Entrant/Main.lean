import ECDSAAdd.Submission.Entrant.Fast12
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
section
namespace ECDSAAdd.Entrant.ZeroFill
open Arithmetic
section Shape
open InputSentinel ParityEven

/-- Write `g ∧ [x > A]` into `pk`, leaving everything else as it was. -/
def extract (tr : Tri) (xs work : List Wire) (one U V F pk g : Wire) : Program :=
  preOf tr xs work one U V F ++ (.CCX g F pk :: (preOf tr xs work one U V F).reverse)

/-- The classifier with the comparison extracted from its chain. -/
def classifierF (tr : Tri) (yb : Bool) (xs work : List Wire) (y0 c f g g1 wB t one U V F pk : Wire) :
    Program :=
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  (zeroWith (fun h => tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h ++
        extract tr xs work one U V F pk g)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work) ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx)))

theorem remapList_not (t : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) (q : Wire)
    (h1 : q ≠ xr1) (h2 : q ≠ xr2) (h3 : q ∉ l.map w) : q ∉ wires (t.remapList xr1 xr2 w l) := by
  induction l with
  | nil => simp [Tri.remapList, wires]
  | cons i l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h3
    have hr := ih h3.2
    have hb : q ∉ wires (t.remapBit xr1 xr2 (w i) i) := by
      simp only [Tri.remapBit, wires_append, Finset.mem_union, not_or]
      refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> simp [wires, Instr.wires, h1, h2, h3.1]
    simp only [Tri.remapList, List.flatMap_cons, wires_append, Finset.mem_union, not_or] at hr ⊢
    exact ⟨hb, hr⟩

theorem classifierF_run (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire)
    (hxs : xs.Nodup) (hlen : xs.length = 256) (hwl : work.length = 253) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, g1, wB, t].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ xs ∧ q ∉ work)
    (htmp : [one, U, V, F, pk].Nodup)
    (htx : ∀ q ∈ [one, U, V, F, pk], q ∉ xs ∧ q ∉ work ∧ q ≠ g)
    (s : State) (m : List Bool)
    (hg : s.basis g = false)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis g1 = false ∧ s.basis wB = false ∧ s.basis t = false)
    (hf : s.basis f = !(matchBit tr xs s.basis &&
      decide ((s.basis (xs.getD tr.r1 0), s.basis (xs.getD tr.r2 0)) = tr.pat tr.S)))
    (hto : ∀ q ∈ [one, U, V, F, pk], q ≠ f → s.basis q = false)
    (x : Nat) (hx : x < 2^256) (xbit : ∀ i, i < 256 → s.basis (xs.getD i 0) = x.testBit i) :
    run (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) m s =
      put (run (classifier tr yb xs work y0 c f g g1 wB t) m s) pk
        ((run (classifier tr yb xs work y0 c f g g1 wB t) m s).basis g && decide (tr.A < x)) := by
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
  have hitl : (it.map w).length = 253 := by
    have := hPl; rw [hP0] at this; simpa using this
  have zp := zeroPorts_maps (it.map w) work (by rw [hitl, hwl])
  have extx (q : Wire) (hq : q ∈ [y0, c, f, g, g1, wB, t]) : q ∉ P ∧ q ∉ work ∧ q ≠ xr1 ∧ q ≠ xr2 := by
    have h := hextx q hq
    refine ⟨fun hp => h.1 (Psub q hp), h.2, fun e => h.1 (e ▸ wmem _ pv.1), fun e => h.1 (e ▸ wmem _ pv.2.1)⟩
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
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      have h2 := fun q hq => (extx q hq).2.2.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases hm with e | e | e | e | e | e | e
      · exact h2 y0 (Or.inl rfl) e.symm
      · exact h2 c (by tauto) e.symm
      · exact h2 f (by tauto) e.symm
      · exact h2 g (by tauto) e.symm
      · exact h2 g1 (by tauto) e.symm
      · exact h2 wB (by tauto) e.symm
      · exact h2 t (by tauto) e.symm
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
  obtain ⟨B, s2, s2ph, s2out, s2p0, s2it, Boff, Bph, Bf, chnd, chz, Bg, main⟩ :=
    shape_state tr v yb xr1 xr2 y0 c f g g1 wB t w i0 it work hPn' x1P' x2P' hused hextP
      (by rw [hitl, hwl]) hwn hdisj' s hg hz hf'
  have oldrun := classifier_run tr v yb xs work y0 c f g g1 wB t hxs hlen hwl hwn hdisj hext hextx s m hg hz hf
  have hG : (run (classifier tr yb xs work y0 c f g g1 wB t) m s).basis g = B.basis g := by
    rw [oldrun, Bg, hmb]
    simp only [tailEff, writeBit, Function.update_self]
    rfl
  set bs := zeroPorts (it.map w) work with hbs
  -- list structure
  have tmpM (q : Wire) (hq : q ∈ [one, U, V, F, pk]) (i : Nat) (hi : i < 256) : q ≠ w i :=
    fun e => (htx q hq).1 (e ▸ wmem i hi)
  have bsW : ∀ b ∈ bs, b.work ∈ work := by
    intro b hb
    have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
  have bsI : ∀ b ∈ bs, b.input ∈ it.map w := by
    intro b hb
    have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
  have hlenbs : it.length = bs.length := by
    have h1 : (bs.map ZeroBit.input).length = (it.map w).length := by rw [zp.1]
    simpa using h1.symm
  have hT : triples xs work one tr.idx = (i0, one, p0) :: tri p0 it bs := by rw [hidx]; rfl
  set T := triples xs work one tr.idx with hTdef
  have hsplit := idx_cat tr pv.2.2.1 pv.1 pv.2.1
  have hTm : T.map (·.1) = tr.topL ++ (tr.midL ++ tr.lowL) := by
    rw [← hsplit, hT, hidx, List.map_cons, tri_fst p0 it bs hlenbs]
  set Tt := T.take tr.topL.length with hTt
  set Tm := (T.drop tr.topL.length).take tr.midL.length with hTmm
  set Tl := T.drop (tr.topL.length + tr.midL.length) with hTl
  have mt : Tt.map (·.1) = tr.topL := by
    rw [hTt, List.map_take, hTm, List.take_left' rfl]
  have mm : Tm.map (·.1) = tr.midL := by
    rw [hTmm, List.map_take, List.map_drop, hTm, List.drop_left' rfl, List.take_left' rfl]
  have ml : Tl.map (·.1) = tr.lowL := by
    rw [hTl, List.map_drop, hTm, ← List.drop_drop, List.drop_left' rfl, List.drop_left' rfl]
  have cat : Tt ++ (Tm ++ Tl) = T := by
    have e1 : Tm ++ Tl = T.drop tr.topL.length := by
      rw [hTl, ← List.drop_drop]; exact List.take_append_drop _ _
    rw [e1]; exact List.take_append_drop _ _
  have memT : ∀ y ∈ Tt ++ Tm ++ Tl, y ∈ T := by
    intro y hy; rw [← cat]; simpa [List.append_assoc] using hy
  -- all chain wires
  have triW : ∀ y ∈ T, (y.2.1 = one ∨ y.2.1 = p0 ∨ y.2.1 ∈ work) ∧ (y.2.2 = p0 ∨ y.2.2 ∈ work) := by
    intro y hy
    rw [hT] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · obtain ⟨h1, b, hb, h2⟩ := tri_wires _ _ _ y hy
      refine ⟨?_, Or.inr (h2 ▸ bsW b hb)⟩
      rcases h1 with e | ⟨d, hd, e⟩
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (e ▸ bsW d hd))
  have p0x : p0 ∈ xs := wmem i0 (ix.2.2.2.2 i0 (by rw [hidx]; simp))
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true, and_self] at htmp
  obtain ⟨⟨oU, oV, oF, oP⟩, ⟨UV, UF, UP⟩, ⟨VF, VP⟩, FP⟩ := htmp
  have tmp1 : ∀ q ∈ [U, V, F, pk], q ≠ one := by
    intro q hq e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with e1 | e1 | e1 | e1
    · exact oU (e.symm.trans e1)
    · exact oV (e.symm.trans e1)
    · exact oF (e.symm.trans e1)
    · exact oP (e.symm.trans e1)
  have tmpIn : ∀ q ∈ [U, V, F, pk], q ∈ [one, U, V, F, pk] := fun q hq => List.mem_cons_of_mem _ hq
  have offT : ∀ q ∈ [U, V, F, pk], ∀ y ∈ T, y.2.1 ≠ q ∧ y.2.2 ≠ q := by
    intro q hq y hy
    obtain ⟨h1, h2⟩ := triW y hy
    have a1 := (htx q (tmpIn q hq)).1
    have a2 := (htx q (tmpIn q hq)).2.1
    refine ⟨?_, ?_⟩
    · rcases h1 with e | e | e
      · rw [e]; exact (tmp1 q hq).symm
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
    · rcases h2 with e | e
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
  have gnot := extx g (by simp)
  have gone : g ≠ one := fun e => (htx one (by simp)).2.2 e.symm
  have offG : ∀ y ∈ T, y.2.1 ≠ g ∧ y.2.2 ≠ g := by
    intro y hy
    obtain ⟨h1, h2⟩ := triW y hy
    have a1 := (hextx g (by simp)).1
    have a2 := gnot.2.1
    refine ⟨?_, ?_⟩
    · rcases h1 with e | e | e
      · rw [e]; exact gone.symm
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
    · rcases h2 with e | e
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
  have endOff : ∀ (A : List (Nat × Wire × Wire)) (p q : Wire), (∀ y ∈ A, y ∈ T) → p ≠ q →
      (∀ y ∈ T, y.2.1 ≠ q ∧ y.2.2 ≠ q) → endW p A ≠ q := by
    intro A p q hA hp hy
    rcases endW_mem p A with e | ⟨y, h, e⟩
    · rw [e]; exact hp
    · rw [e]; exact (hy y (hA y h)).2
  have inTt : ∀ y ∈ Tt, y ∈ T := fun y h => List.mem_of_mem_take h
  have inTm : ∀ y ∈ Tm, y ∈ T := fun y h => List.mem_of_mem_drop (List.mem_of_mem_take h)
  have mU : U ∈ [U, V, F, pk] := by simp
  have mV : V ∈ [U, V, F, pk] := by simp
  have mF : F ∈ [U, V, F, pk] := by simp
  have mP : pk ∈ [U, V, F, pk] := by simp
  have h1l : tr.lo < 256 := by simp only [Tri.lo]; omega
  have h1h : tr.hi < 256 := by simp only [Tri.hi]; omega
  have nx (q : Wire) (hq : q ∈ [U, V, F, pk]) (i : Nat) (hi : i < 256) : w i ≠ q :=
    (tmpM q (tmpIn q hq) i hi).symm
  have eO := fun (q : Wire) (hq : q ∈ [U, V, F, pk]) =>
    endOff Tt one q inTt (tmp1 q hq).symm (offT q hq)
  have eM := fun (q : Wire) (hq : q ∈ [U, V, F, pk]) =>
    endOff Tm (endW one Tt) q inTm (eO q hq) (offT q hq)
  have hTall : ∀ y ∈ Tt ++ Tm ++ Tl, (y.2.1 ≠ U ∧ y.2.2 ≠ U) ∧ (y.2.1 ≠ V ∧ y.2.2 ≠ V) ∧
      (y.2.1 ≠ F ∧ y.2.2 ≠ F) := fun y hy =>
    ⟨offT U mU y (memT y hy), offT V mV y (memT y hy), offT F mF y (memT y hy)⟩
  have Pp : ProperProgram (preOf tr xs work one U V F) :=
    pre_proper _ _ _ _ _ _ _ _ _ _ _ _ _ _ (nx V mV _ h1l) UV (nx F mF _ h1h) VF (eM U mU) (eO V mV) hTall
  have pkNot : pk ∉ wires (preOf tr xs work one U V F) := by
    apply pre_not
    · exact ⟨tmp1 pk mP, Ne.symm UP, Ne.symm VP, Ne.symm FP, (nx pk mP _ h1l).symm, (nx pk mP _ h1h).symm,
        (eM pk mP).symm, (eO pk mP).symm⟩
    · intro y hy
      have := offT pk mP y (memT y hy)
      exact ⟨this.1.symm, this.2.symm⟩
  have gNot : g ∉ wires (preOf tr xs work one U V F) := by
    have gU : g ≠ U := fun e => (htx U (by simp)).2.2 e.symm
    have gV : g ≠ V := fun e => (htx V (by simp)).2.2 e.symm
    have gF : g ≠ F := fun e => (htx F (by simp)).2.2 e.symm
    apply pre_not
    · refine ⟨gone, gU, gV, gF, ?_, ?_, ?_, ?_⟩
      · exact fun e => (hextx g (by simp)).1 (e ▸ wmem _ h1l)
      · exact fun e => (hextx g (by simp)).1 (e ▸ wmem _ h1h)
      · exact (endOff Tm (endW one Tt) g inTm (endOff Tt one g inTt gone.symm offG) offG).symm
      · exact (endOff Tt one g inTt gone.symm offG).symm
    · intro y hy
      have := offG y (memT y hy)
      exact ⟨this.1.symm, this.2.symm⟩
  have wNot : ∀ q, q ∉ work → ∀ b ∈ bs, b.work ≠ q := fun q hq b hb e => hq (e ▸ bsW b hb)
  have tmpP : ∀ q ∈ [one, U, V, F, pk], q ∉ (i0 :: it).map w := fun q hq h =>
    (htx q hq).1 (Psub q (by rw [← hlP]; exact h))
  have Bt : ∀ q ∈ [one, U, V, F, pk], B.basis q = false := by
    intro q hq
    by_cases qf : q = f
    · rw [qf]; exact Bf
    · rw [Boff q qf (htx q hq).2.2, fill_outside _ _ _ q (wNot q (htx q hq).2.1),
        s2out q (tmpP q hq)]
      exact hto q hq qf
  have pivB (i : Nat) (hi : i = tr.r1 ∨ i = tr.r2) : B.basis (w i) = x.testBit i := by
    have hi256 : i < 256 := by rcases hi with rfl | rfl <;> [exact pv.1; exact pv.2.1]
    have nP : w i ∉ (i0 :: it).map w := by
      rcases hi with rfl | rfl <;> [exact x1P'; exact x2P']
    have nW : w i ∉ work := fun h => hdisj _ h (wmem i hi256)
    have nf : w i ≠ f := fun e => (hextx f (by simp)).1 (e ▸ wmem i hi256)
    have ng : w i ≠ g := fun e => (hextx g (by simp)).1 (e ▸ wmem i hi256)
    rw [Boff _ nf ng, fill_outside _ _ _ _ (wNot _ nW), s2out _ nP]
    exact xbit i hi256
  have hiP : tr.hi = tr.r1 ∨ tr.hi = tr.r2 := by simp only [Tri.hi]; omega
  have loP : tr.lo = tr.r1 ∨ tr.lo = tr.r2 := by simp only [Tri.lo]; omega
  have hxr1 : s.basis xr1 = x.testBit tr.r1 := xbit _ pv.1
  have hxr2 : s.basis xr2 = x.testBit tr.r2 := xbit _ pv.2.1
  let mtf : Nat → Bool := fun i => x.testBit i == tr.tgt i (x.testBit tr.r1, x.testBit tr.r2)
  have i0m : i0 ∈ tr.idx := by rw [hidx]; simp
  have itm : ∀ i ∈ it, i ∈ tr.idx := fun i hi => by rw [hidx]; simp [hi]
  have p0ne : one ≠ p0 := fun e => (htx one (by simp)).1 (e ▸ p0x)
  have p0f : p0 ≠ f := fun e => (hextx f (by simp)).1 (e ▸ p0x)
  have p0g : p0 ≠ g := fun e => (hextx g (by simp)).1 (e ▸ p0x)
  have p0W : p0 ∉ work := fun h => hdisj _ h p0x
  have hc0 : s2.basis p0 = mtf i0 := by
    rw [s2p0, hxr1, hxr2, xbit i0 (ix.2.2.2.2 i0 i0m)]
  have hchain : Chain (writeBit B.basis one true) mtf true (Tt ++ (Tm ++ Tl)) := by
    rw [cat, hT]
    refine ⟨by simp [writeBit], ?_, ?_⟩
    · simp only [writeBit, Function.update_apply, Ne.symm p0ne, if_false, Bool.true_and]
      rw [Boff _ p0f p0g, fill_outside _ _ _ _ (wNot _ p0W), hc0]
    · have hmt : ∀ k (hk : k < it.length), mtf it[k] = !s2.basis (bs[k]'(hlenbs ▸ hk)).input := by
        intro k hk
        have hin : (bs[k]'(hlenbs ▸ hk)).input = w it[k] := by
          have e1 : (bs.map ZeroBit.input)[k]'(by simpa using hlenbs ▸ hk) = (bs[k]'(hlenbs ▸ hk)).input := by
            simp
          have e2 : (it.map w)[k]'(by simpa using hk) = w it[k] := by simp
          rw [← e1, ← e2]
          exact List.getElem_of_eq zp.1 _
        have im : it[k] ∈ it := List.getElem_mem _
        rw [hin, s2it _ im, hxr1, hxr2, xbit _ (ix.2.2.2.2 _ (itm _ im))]
        simp only [mtf]
        cases x.testBit it[k] <;> cases tr.tgt it[k] (x.testBit tr.r1, x.testBit tr.r2) <;> rfl
      have cf := chain_fill mtf p0 it bs s2.basis (true && mtf i0) hlenbs chnd chz (by simpa using hc0) hmt
      apply chain_congr _ _ _ _ _ _ cf
      intro y hy
      have hyw := tri_wires _ _ _ y hy
      have side : ∀ q, (q = p0 ∨ ∃ b ∈ bs, q = b.work) →
          fill p0 bs s2.basis q = writeBit B.basis one true q := by
        intro q hq
        have qx : q ∈ xs ∨ q ∈ work := by
          rcases hq with e | ⟨b, hb, e⟩
          · exact Or.inl (e ▸ p0x)
          · exact Or.inr (e ▸ bsW b hb)
        have nf : q ≠ f := by
          intro e
          rcases qx with h | h
          · exact (hextx f (by simp)).1 (e ▸ h)
          · exact (hextx f (by simp)).2 (e ▸ h)
        have ng : q ≠ g := by
          intro e
          rcases qx with h | h
          · exact (hextx g (by simp)).1 (e ▸ h)
          · exact (hextx g (by simp)).2 (e ▸ h)
        have no : q ≠ one := by
          intro e
          rcases qx with h | h
          · exact (htx one (by simp)).1 (e ▸ h)
          · exact (htx one (by simp)).2.1 (e ▸ h)
        simp only [writeBit, Function.update_apply, no, if_false]
        exact (Boff q nf ng).symm
      exact ⟨side _ hyw.1, side _ (Or.inr hyw.2)⟩
  have nlo (q : Wire) (hq : q ∈ [U, V, F, pk]) : w tr.lo ≠ q := nx q hq _ h1l
  have nhi (q : Wire) (hq : q ∈ [U, V, F, pk]) : w tr.hi ≠ q := nx q hq _ h1h
  have FV := F_value tr v pv.2.2.1 x hx one U V F (w tr.hi) (w tr.lo) Tt Tm Tl mt mm ml UV UF VF
    (nlo U mU) (nlo V mV) (nlo F mF) (nhi U mU) (nhi V mV) (nhi F mF)
    (eM U mU) (eM V mV) (eM F mF) (eO U mU) (eO V mV) (eO F mF) oU oV oF
    (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1l)) (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1h))
    hTall B (Bt U (by simp)) (Bt V (by simp)) (Bt F (by simp)) (Bt one (by simp))
    (pivB _ hiP) (pivB _ loP) hchain
  have gpk : g ≠ pk := fun e => (htx pk (by simp)).2.2 e.symm
  have hE : ∀ m', run (extract tr xs work one U V F pk g) m' B =
      put B pk (B.basis pk ^^ ((run (preOf tr xs work one U V F) [] B).basis g &&
        (run (preOf tr xs work one U V F) [] B).basis F)) :=
    fun m' => sandwich _ Pp g F pk pkNot gpk FP B m'
  have hRg : (run (preOf tr xs work one U V F) [] B).basis g = B.basis g :=
    run_preserves_outside _ [] B g gNot
  have hval : (B.basis pk ^^ ((run (preOf tr xs work one U V F) [] B).basis g &&
      (run (preOf tr xs work one U V F) [] B).basis F)) = (B.basis g && decide (tr.A < x)) := by
    have e : (run (preOf tr xs work one U V F) [] B).basis F = decide (tr.A < x) := FV
    rw [Bt pk (by simp), hRg, e, Bool.false_xor]
  rw [hval] at hE
  have hpk1 : pk ∉ (p0 :: bs.flatMap ZeroBit.wires) := by
    intro h
    rcases List.mem_cons.mp h with e | h
    · exact (htx pk (by simp)).1 (e ▸ p0x)
    · obtain ⟨b, hb, hw'⟩ := List.mem_flatMap.mp h
      simp only [ZeroBit.wires, List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with e | e
      · obtain ⟨i, hi, e2⟩ := List.mem_map.mp (bsI b hb)
        exact (htx pk (by simp)).1 (e ▸ e2 ▸ wmem i (ix.2.2.2.2 i (itm i hi)))
      · exact (htx pk (by simp)).2.1 (e ▸ bsW b hb)
  have hpk2 : pk ∉ wires ([.X p0] ++ tr.remapList xr1 xr2 w (i0 :: it)) := by
    rw [wires_append]
    simp only [Finset.mem_union, not_or]
    refine ⟨?_, remapList_not tr xr1 xr2 w _ pk (nx pk mP _ pv.1).symm (nx pk mP _ pv.2.1).symm (tmpP pk (by simp))⟩
    have np : pk ≠ p0 := (nx pk mP i0 (ix.2.2.2.2 i0 i0m)).symm
    simp [wires, Instr.wires, np]
  have M := main (extract tr xs work one U V F pk g) pk _ hE hpk1 hpk2 m
  have hprog : classifier tr yb xs work y0 c f g g1 wB t =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (tail tr yb xr1 xr2 y0 c f g g1 wB t) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [classifier, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  have hprogF : classifierF tr yb xs work y0 c f g g1 wB t one U V F pk =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (fun h => tail tr yb xr1 xr2 y0 c f g g1 wB t h ++ extract tr xs work one U V F pk g)
        (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [classifierF, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  rw [hG, hprogF, hprog]
  exact M

theorem toffoli_reverse (p : Program) : toffoliCount p.reverse = toffoliCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    rw [List.reverse_cons, toffoliCount_append, ih]
    cases i <;> simp [toffoliCount]
    omega

theorem slots_reverse (p : Program) : Challenge.gateSlots p.reverse = Challenge.gateSlots p := by
  simp [Challenge.gateSlots, List.sum_reverse, List.map_reverse]

theorem triples_length (xs work : List Wire) (one : Wire) (l : List Nat) :
    (triples xs work one l).length ≤ l.length := by
  cases l with
  | nil => simp [triples]
  | cons i0 it =>
    have h : ∀ (c : Wire) (l : List Nat) (bs : List ZeroBit), (tri c l bs).length ≤ l.length := by
      intro c l bs
      induction l generalizing c bs with
      | nil => cases bs <;> simp [tri]
      | cons i l ih =>
        cases bs with
        | nil => simp [tri]
        | cons b bs =>
          simp only [tri, List.length_cons]
          have := ih b.work bs
          omega
    simp only [triples, List.length_cons]
    have := h (xs.getD i0 0) it (zeroPorts (it.map (fun i => xs.getD i 0)) work)
    omega

theorem extract_counts (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F pk g : Wire) :
    toffoliCount (extract tr xs work one U V F pk g) ≤ 5 ∧
    measurementCount (extract tr xs work one U V F pk g) = 0 ∧
    Challenge.gateSlots (extract tr xs work one U V F pk g) ≤ 1037 := by
  have ix := Tri.idx_facts v
  have pc := pre_counts tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F (xs.getD tr.lo 0)
    (xs.getD tr.hi 0)
    (endW (endW one ((triples xs work one tr.idx).take tr.topL.length))
      (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length))
    (endW one ((triples xs work one tr.idx).take tr.topL.length))
    ((triples xs work one tr.idx).take tr.topL.length)
    (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length)
    ((triples xs work one tr.idx).drop (tr.topL.length + tr.midL.length))
  have hl := triples_length xs work one tr.idx
  rw [ix.2.1] at hl
  have lsum : ((triples xs work one tr.idx).take tr.topL.length).length +
      (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length).length +
      ((triples xs work one tr.idx).drop (tr.topL.length + tr.midL.length)).length ≤ 254 := by
    simp only [List.length_take, List.length_drop]
    omega
  change toffoliCount (preOf tr xs work one U V F) ≤ 2 ∧ measurementCount (preOf tr xs work one U V F) = 0 ∧
    Challenge.gateSlots (preOf tr xs work one U V F) ≤ _ at pc
  unfold extract
  refine ⟨?_, ?_, ?_⟩
  · rw [toffoliCount_append]
    simp only [toffoliCount]
    rw [toffoli_reverse]
    omega
  · rw [measurementCount_append]
    simp only [measurementCount]
    rw [measurementCount_reverse]
    omega
  · rw [Challenge.gateSlots_append]
    have e : Challenge.gateSlots (Instr.CCX g F pk :: (preOf tr xs work one U V F).reverse) =
        1 + Challenge.gateSlots (preOf tr xs work one U V F) := by
      rw [← slots_reverse (preOf tr xs work one U V F)]
      simp [Challenge.gateSlots, Challenge.instructionSlots]
    rw [e]
    omega

theorem classifierF_counts (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire) (hwl : work.length = 253) :
    toffoliCount (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) ≤ 261 ∧
    measurementCount (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) = 257 ∧
    Challenge.gateSlots (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) ≤ 3361 + 1037 := by
  obtain ⟨i0, it, hidx, hitl⟩ := InputSentinel.idx_split tr v
  have ix := Tri.idx_facts v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have ec := extract_counts tr v xs work one U V F pk g
  have zc := zeroWith_counts_general
    (fun h => tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h ++
      extract tr xs work one U V F pk g) (3 + toffoliCount (extract tr xs work one U V F pk g)) 4
    (fun h => by
      have tc := InputSentinel.tail_counts tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h
      rw [toffoliCount_append, measurementCount_append, tc.1, tc.2, ec.2.1]
      exact ⟨rfl, rfl⟩)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zc
  have zs := InputSentinel.zeroWith_slots
    (fun h => tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h ++
      extract tr xs work one U V F pk g)
    (Challenge.gateSlots (decodeT tr yb) + Challenge.gateSlots (extract tr xs work one U V F pk g))
    (fun h => by
      rw [Challenge.gateSlots_append, InputSentinel.tail_slots])
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zs
  have rs := InputSentinel.remapList_slots tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  rw [ix.2.1] at rs
  have ds := InputSentinel.decodeT_slots tr yb
  have rt := InputSentinel.remapList_tc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  have rm := remapList_mc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  unfold classifierF
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append, rt, rm, zc.1, zc.2, zs]
  refine ⟨?_, by simp [measurementCount], ?_⟩
  · have := ec.1
    simp [toffoliCount]
    omega
  · have := ec.2.2
    simp only [Challenge.gateSlots, Challenge.instructionSlots, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at rs ds this ⊢
    omega

theorem triples_wires (xs work : List Wire) (one : Wire) (l : List Nat) (hl : ∀ i ∈ l, i < 256)
    (hlen : xs.length = 256) :
    ∀ y ∈ triples xs work one l, (y.2.1 = one ∨ y.2.1 ∈ xs ∨ y.2.1 ∈ work) ∧ (y.2.2 ∈ xs ∨ y.2.2 ∈ work) := by
  cases l with
  | nil => simp [triples]
  | cons i0 it =>
    have p0x : xs.getD i0 0 ∈ xs := by
      have := hl i0 (by simp)
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    intro y hy
    simp only [triples, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨Or.inl rfl, Or.inl p0x⟩
    · obtain ⟨h1, b, hb, h2⟩ := tri_wires _ _ _ y hy
      have w1 := (zeroPorts_mem _ _ b hb).2
      refine ⟨?_, Or.inr (h2 ▸ w1)⟩
      rcases h1 with e | ⟨d, hd, e⟩
      · exact Or.inr (Or.inl (e ▸ p0x))
      · exact Or.inr (Or.inr (e ▸ (zeroPorts_mem _ _ d hd).2))

/-- Facts every wire of the chain shares with a wire off the chain. -/
theorem preOf_off (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F q : Wire)
    (hlen : xs.length = 256) (hx : q ∉ xs) (hw : q ∉ work) (ho : q ≠ one) :
    let T := triples xs work one tr.idx
    (∀ y ∈ T, q ≠ y.2.1 ∧ q ≠ y.2.2) ∧
    q ≠ endW one (T.take tr.topL.length) ∧
    q ≠ endW (endW one (T.take tr.topL.length)) ((T.drop tr.topL.length).take tr.midL.length) ∧
    q ≠ xs.getD tr.lo 0 ∧ q ≠ xs.getD tr.hi 0 := by
  intro T
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  have tw := triples_wires xs work one tr.idx ix.2.2.2.2 hlen
  have off : ∀ y ∈ T, q ≠ y.2.1 ∧ q ≠ y.2.2 := by
    intro y hy
    obtain ⟨a, b⟩ := tw y hy
    refine ⟨?_, ?_⟩
    · rcases a with e | e | e
      · rw [e]; exact ho
      · exact fun E => hx (E ▸ e)
      · exact fun E => hw (E ▸ e)
    · rcases b with e | e
      · exact fun E => hx (E ▸ e)
      · exact fun E => hw (E ▸ e)
  have e1 : q ≠ endW one (T.take tr.topL.length) := by
    rcases endW_mem one (T.take tr.topL.length) with e | ⟨y, h, e⟩
    · rw [e]; exact ho
    · rw [e]; exact (off y (List.mem_of_mem_take h)).2
  have e2 : q ≠ endW (endW one (T.take tr.topL.length)) ((T.drop tr.topL.length).take tr.midL.length) := by
    rcases endW_mem (endW one (T.take tr.topL.length)) ((T.drop tr.topL.length).take tr.midL.length) with
      e | ⟨y, h, e⟩
    · rw [e]; exact e1
    · rw [e]; exact (off y (List.mem_of_mem_drop (List.mem_of_mem_take h))).2
  have mem (i : Nat) (hi : i < 256) : xs.getD i 0 ∈ xs := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hlo : tr.lo < 256 := by simp only [Tri.lo]; have := pv.1; have := pv.2.1; omega
  have hhi : tr.hi < 256 := by simp only [Tri.hi]; have := pv.1; have := pv.2.1; omega
  exact ⟨off, e1, e2, fun E => hx (E ▸ mem _ hlo), fun E => hx (E ▸ mem _ hhi)⟩

theorem preOf_proper (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F : Wire)
    (hlen : xs.length = 256) (hU : U ∉ xs ∧ U ∉ work ∧ U ≠ one) (hV : V ∉ xs ∧ V ∉ work ∧ V ≠ one)
    (hF : F ∉ xs ∧ F ∉ work ∧ F ≠ one) (UV : U ≠ V) (VF : V ≠ F) :
    ProperProgram (preOf tr xs work one U V F) := by
  obtain ⟨u1, u2, u3, u4, u5⟩ := preOf_off tr v xs work one U V F U hlen hU.1 hU.2.1 hU.2.2
  obtain ⟨v1, v2, v3, v4, v5⟩ := preOf_off tr v xs work one U V F V hlen hV.1 hV.2.1 hV.2.2
  obtain ⟨f1, f2, f3, f4, f5⟩ := preOf_off tr v xs work one U V F F hlen hF.1 hF.2.1 hF.2.2
  have memT : ∀ y ∈ ((triples xs work one tr.idx).take tr.topL.length) ++
      (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length) ++
      ((triples xs work one tr.idx).drop (tr.topL.length + tr.midL.length)),
      y ∈ triples xs work one tr.idx := by
    intro y hy
    simp only [List.mem_append] at hy
    rcases hy with (h | h) | h
    · exact List.mem_of_mem_take h
    · exact List.mem_of_mem_drop (List.mem_of_mem_take h)
    · exact List.mem_of_mem_drop h
  exact pre_proper _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Ne.symm v4) UV (Ne.symm f5) VF (Ne.symm u3) (Ne.symm v2)
    (fun y hy => ⟨⟨Ne.symm (u1 y (memT y hy)).1, Ne.symm (u1 y (memT y hy)).2⟩,
      ⟨Ne.symm (v1 y (memT y hy)).1, Ne.symm (v1 y (memT y hy)).2⟩,
      ⟨Ne.symm (f1 y (memT y hy)).1, Ne.symm (f1 y (memT y hy)).2⟩⟩)

theorem preOf_sub (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F : Wire)
    (hlen : xs.length = 256) (W : Finset Wire) (hx : ∀ q ∈ xs, q ∈ W) (hw : ∀ q ∈ work, q ∈ W)
    (h1 : one ∈ W) (h2 : U ∈ W) (h3 : V ∈ W) (h4 : F ∈ W) :
    wires (preOf tr xs work one U V F) ⊆ W := by
  intro q hq
  apply Classical.byContradiction
  intro hn
  have nx : q ∉ xs := fun h => hn (hx q h)
  have nw : q ∉ work := fun h => hn (hw q h)
  have no : q ≠ one := fun e => hn (e ▸ h1)
  obtain ⟨o1, o2, o3, o4, o5⟩ := preOf_off tr v xs work one U V F q hlen nx nw no
  have memT : ∀ y ∈ ((triples xs work one tr.idx).take tr.topL.length) ++
      (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length) ++
      ((triples xs work one tr.idx).drop (tr.topL.length + tr.midL.length)),
      y ∈ triples xs work one tr.idx := by
    intro y hy
    simp only [List.mem_append] at hy
    rcases hy with (h | h) | h
    · exact List.mem_of_mem_take h
    · exact List.mem_of_mem_drop (List.mem_of_mem_take h)
    · exact List.mem_of_mem_drop h
  exact pre_not _ _ _ _ _ _ _ _ _ _ _ _ _ _ q
    ⟨no, fun e => hn (e ▸ h2), fun e => hn (e ▸ h3), fun e => hn (e ▸ h4), o4, o5, o3, o2⟩
    (fun y hy => o1 y (memT y hy)) hq

theorem extract_sub (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F pk g : Wire)
    (hlen : xs.length = 256) (W : Finset Wire) (hx : ∀ q ∈ xs, q ∈ W) (hw : ∀ q ∈ work, q ∈ W)
    (h1 : one ∈ W) (h2 : U ∈ W) (h3 : V ∈ W) (h4 : F ∈ W) (h5 : pk ∈ W) (h6 : g ∈ W) :
    wires (extract tr xs work one U V F pk g) ⊆ W := by
  have P := preOf_sub tr v xs work one U V F hlen W hx hw h1 h2 h3 h4
  unfold extract
  rw [wires_append]
  refine Finset.union_subset P ?_
  have e : (Instr.CCX g F pk :: (preOf tr xs work one U V F).reverse) =
      [Instr.CCX g F pk] ++ (preOf tr xs work one U V F).reverse := rfl
  rw [e, wires_append, wires_reverse]
  refine Finset.union_subset ?_ P
  simp [wires, Instr.wires, Finset.insert_subset_iff, h4, h5, h6]

theorem zeroWith_app_physical (T : Wire → Program) (E : Program) (hE : GatePhysical E) :
    ∀ (c : Wire) (bs : List ZeroBit), GatePhysical (zeroWith T c bs) →
      GatePhysical (zeroWith (fun h => T h ++ E) c bs) := by
  intro c bs
  induction bs generalizing c with
  | nil =>
    intro h
    simp only [zeroWith, gatePhysical_append] at h ⊢
    exact ⟨h, hE⟩
  | cons b bs ih =>
    intro h
    simp only [zeroWith, gatePhysical_append] at h ⊢
    exact ⟨⟨h.1.1, ih b.work h.1.2⟩, h.2⟩

theorem zeroWith_app_wires (T : Wire → Program) (E : Program) :
    ∀ (c : Wire) (bs : List ZeroBit),
      wires (zeroWith (fun h => T h ++ E) c bs) ⊆ wires (zeroWith T c bs) ∪ wires E := by
  intro c bs
  induction bs generalizing c with
  | nil => simp [zeroWith, wires_append]
  | cons b bs ih =>
    simp only [zeroWith, wires_append]
    intro q hq
    have i := ih b.work (a := q)
    simp only [Finset.mem_union] at hq i ⊢
    tauto

theorem classifierF_physical (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire) (hlen : xs.length = 256)
    (hU : U ∉ xs ∧ U ∉ work ∧ U ≠ one) (hV : V ∉ xs ∧ V ∉ work ∧ V ≠ one)
    (hF : F ∉ xs ∧ F ∉ work ∧ F ≠ one) (UV : U ≠ V) (VF : V ≠ F) (Fp : F ≠ pk) (gp : g ≠ pk)
    (old : GatePhysical (classifier tr yb xs work y0 c f g g1 wB t)) :
    GatePhysical (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) := by
  have Pp := preOf_proper tr v xs work one U V F hlen hU hV hF UV VF
  have hE : GatePhysical (extract tr xs work one U V F pk g) := by
    have hp : ProperProgram (extract tr xs work one U V F pk g) := by
      unfold extract
      rw [properProgram_append]
      refine ⟨Pp, ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact ⟨gp, Fp⟩
      · exact Pp i (List.mem_reverse.mp h)
    intro i hi
    have := hp i hi
    cases i <;> simp_all [RecordedQuantum.PhysicalInstr, ProperGate]
  unfold classifier at old
  simp only [gatePhysical_append] at old
  unfold classifierF
  simp only [gatePhysical_append]
  exact ⟨old.1, old.2.1, zeroWith_app_physical _ _ hE _ _ old.2.2.1, old.2.2.2⟩

theorem classifierF_wires (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire) (hlen : xs.length = 256) (W : Finset Wire)
    (hc : wires (classifier tr yb xs work y0 c f g g1 wB t) ⊆ W)
    (hx : ∀ q ∈ xs, q ∈ W) (hw : ∀ q ∈ work, q ∈ W)
    (h1 : one ∈ W) (h2 : U ∈ W) (h3 : V ∈ W) (h4 : F ∈ W) (h5 : pk ∈ W) (h6 : g ∈ W) :
    wires (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) ⊆ W := by
  have E := extract_sub tr v xs work one U V F pk g hlen W hx hw h1 h2 h3 h4 h5 h6
  unfold classifier at hc
  simp only [wires_append, Finset.union_subset_iff] at hc
  unfold classifierF
  simp only [wires_append, Finset.union_subset_iff]
  exact ⟨hc.1, hc.2.1, (zeroWith_app_wires _ _ _ _).trans (Finset.union_subset hc.2.2.1 E), hc.2.2.2⟩


def extractFast_research (tr : Tri) (xs work : List Wire) (one U V F pk g : Wire) : Program :=
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  fastExtract tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl

def classifierFast_research (tr : Tri) (yb : Bool) (xs work : List Wire) (y0 c f g g1 wB t one U V F pk : Wire) :
    Program :=
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  (zeroWith (fun h => tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h ++
        extractFast_research tr xs work one U V F pk g)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work) ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx)))

theorem classifierFast_run_research (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire)
    (hxs : xs.Nodup) (hlen : xs.length = 256) (hwl : work.length = 253) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, g1, wB, t].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ xs ∧ q ∉ work)
    (htmp : [one, U, V, F, pk].Nodup)
    (htx : ∀ q ∈ [one, U, V, F, pk], q ∉ xs ∧ q ∉ work ∧ q ≠ g)
    (s : State) (m : List Bool)
    (hg : s.basis g = false)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis g1 = false ∧ s.basis wB = false ∧ s.basis t = false)
    (hf : s.basis f = !(matchBit tr xs s.basis &&
      decide ((s.basis (xs.getD tr.r1 0), s.basis (xs.getD tr.r2 0)) = tr.pat tr.S)))
    (hto : ∀ q ∈ [one, U, V, F, pk], q ≠ f → s.basis q = false)
    (x : Nat) (hx : x < 2^256) (xbit : ∀ i, i < 256 → s.basis (xs.getD i 0) = x.testBit i) :
    run (classifierFast_research tr yb xs work y0 c f g g1 wB t one U V F pk) m s =
      put (run (classifier tr yb xs work y0 c f g g1 wB t) m s) pk
        ((run (classifier tr yb xs work y0 c f g g1 wB t) m s).basis g && decide (tr.A < x)) := by
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
  have hitl : (it.map w).length = 253 := by
    have := hPl; rw [hP0] at this; simpa using this
  have zp := zeroPorts_maps (it.map w) work (by rw [hitl, hwl])
  have extx (q : Wire) (hq : q ∈ [y0, c, f, g, g1, wB, t]) : q ∉ P ∧ q ∉ work ∧ q ≠ xr1 ∧ q ≠ xr2 := by
    have h := hextx q hq
    refine ⟨fun hp => h.1 (Psub q hp), h.2, fun e => h.1 (e ▸ wmem _ pv.1), fun e => h.1 (e ▸ wmem _ pv.2.1)⟩
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
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      have h2 := fun q hq => (extx q hq).2.2.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases hm with e | e | e | e | e | e | e
      · exact h2 y0 (Or.inl rfl) e.symm
      · exact h2 c (by tauto) e.symm
      · exact h2 f (by tauto) e.symm
      · exact h2 g (by tauto) e.symm
      · exact h2 g1 (by tauto) e.symm
      · exact h2 wB (by tauto) e.symm
      · exact h2 t (by tauto) e.symm
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
  obtain ⟨B, s2, s2ph, s2out, s2p0, s2it, Boff, Bph, Bf, chnd, chz, Bg, main⟩ :=
    shape_state tr v yb xr1 xr2 y0 c f g g1 wB t w i0 it work hPn' x1P' x2P' hused hextP
      (by rw [hitl, hwl]) hwn hdisj' s hg hz hf'
  have oldrun := classifier_run tr v yb xs work y0 c f g g1 wB t hxs hlen hwl hwn hdisj hext hextx s m hg hz hf
  have hG : (run (classifier tr yb xs work y0 c f g g1 wB t) m s).basis g = B.basis g := by
    rw [oldrun, Bg, hmb]
    simp only [tailEff, writeBit, Function.update_self]
    rfl
  set bs := zeroPorts (it.map w) work with hbs
  -- list structure
  have tmpM (q : Wire) (hq : q ∈ [one, U, V, F, pk]) (i : Nat) (hi : i < 256) : q ≠ w i :=
    fun e => (htx q hq).1 (e ▸ wmem i hi)
  have bsW : ∀ b ∈ bs, b.work ∈ work := by
    intro b hb
    have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
  have bsI : ∀ b ∈ bs, b.input ∈ it.map w := by
    intro b hb
    have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
  have hlenbs : it.length = bs.length := by
    have h1 : (bs.map ZeroBit.input).length = (it.map w).length := by rw [zp.1]
    simpa using h1.symm
  have hT : triples xs work one tr.idx = (i0, one, p0) :: tri p0 it bs := by rw [hidx]; rfl
  set T := triples xs work one tr.idx with hTdef
  have hsplit := idx_cat tr pv.2.2.1 pv.1 pv.2.1
  have hTm : T.map (·.1) = tr.topL ++ (tr.midL ++ tr.lowL) := by
    rw [← hsplit, hT, hidx, List.map_cons, tri_fst p0 it bs hlenbs]
  set Tt := T.take tr.topL.length with hTt
  set Tm := (T.drop tr.topL.length).take tr.midL.length with hTmm
  set Tl := T.drop (tr.topL.length + tr.midL.length) with hTl
  have mt : Tt.map (·.1) = tr.topL := by
    rw [hTt, List.map_take, hTm, List.take_left' rfl]
  have mm : Tm.map (·.1) = tr.midL := by
    rw [hTmm, List.map_take, List.map_drop, hTm, List.drop_left' rfl, List.take_left' rfl]
  have ml : Tl.map (·.1) = tr.lowL := by
    rw [hTl, List.map_drop, hTm, ← List.drop_drop, List.drop_left' rfl, List.drop_left' rfl]
  have cat : Tt ++ (Tm ++ Tl) = T := by
    have e1 : Tm ++ Tl = T.drop tr.topL.length := by
      rw [hTl, ← List.drop_drop]; exact List.take_append_drop _ _
    rw [e1]; exact List.take_append_drop _ _
  have memT : ∀ y ∈ Tt ++ Tm ++ Tl, y ∈ T := by
    intro y hy; rw [← cat]; simpa [List.append_assoc] using hy
  -- all chain wires
  have triW : ∀ y ∈ T, (y.2.1 = one ∨ y.2.1 = p0 ∨ y.2.1 ∈ work) ∧ (y.2.2 = p0 ∨ y.2.2 ∈ work) := by
    intro y hy
    rw [hT] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · obtain ⟨h1, b, hb, h2⟩ := tri_wires _ _ _ y hy
      refine ⟨?_, Or.inr (h2 ▸ bsW b hb)⟩
      rcases h1 with e | ⟨d, hd, e⟩
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (e ▸ bsW d hd))
  have p0x : p0 ∈ xs := wmem i0 (ix.2.2.2.2 i0 (by rw [hidx]; simp))
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true, and_self] at htmp
  obtain ⟨⟨oU, oV, oF, oP⟩, ⟨UV, UF, UP⟩, ⟨VF, VP⟩, FP⟩ := htmp
  have tmp1 : ∀ q ∈ [U, V, F, pk], q ≠ one := by
    intro q hq e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with e1 | e1 | e1 | e1
    · exact oU (e.symm.trans e1)
    · exact oV (e.symm.trans e1)
    · exact oF (e.symm.trans e1)
    · exact oP (e.symm.trans e1)
  have tmpIn : ∀ q ∈ [U, V, F, pk], q ∈ [one, U, V, F, pk] := fun q hq => List.mem_cons_of_mem _ hq
  have offT : ∀ q ∈ [U, V, F, pk], ∀ y ∈ T, y.2.1 ≠ q ∧ y.2.2 ≠ q := by
    intro q hq y hy
    obtain ⟨h1, h2⟩ := triW y hy
    have a1 := (htx q (tmpIn q hq)).1
    have a2 := (htx q (tmpIn q hq)).2.1
    refine ⟨?_, ?_⟩
    · rcases h1 with e | e | e
      · rw [e]; exact (tmp1 q hq).symm
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
    · rcases h2 with e | e
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
  have gnot := extx g (by simp)
  have gone : g ≠ one := fun e => (htx one (by simp)).2.2 e.symm
  have offG : ∀ y ∈ T, y.2.1 ≠ g ∧ y.2.2 ≠ g := by
    intro y hy
    obtain ⟨h1, h2⟩ := triW y hy
    have a1 := (hextx g (by simp)).1
    have a2 := gnot.2.1
    refine ⟨?_, ?_⟩
    · rcases h1 with e | e | e
      · rw [e]; exact gone.symm
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
    · rcases h2 with e | e
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
  have endOff : ∀ (A : List (Nat × Wire × Wire)) (p q : Wire), (∀ y ∈ A, y ∈ T) → p ≠ q →
      (∀ y ∈ T, y.2.1 ≠ q ∧ y.2.2 ≠ q) → endW p A ≠ q := by
    intro A p q hA hp hy
    rcases endW_mem p A with e | ⟨y, h, e⟩
    · rw [e]; exact hp
    · rw [e]; exact (hy y (hA y h)).2
  have inTt : ∀ y ∈ Tt, y ∈ T := fun y h => List.mem_of_mem_take h
  have inTm : ∀ y ∈ Tm, y ∈ T := fun y h => List.mem_of_mem_drop (List.mem_of_mem_take h)
  have mU : U ∈ [U, V, F, pk] := by simp
  have mV : V ∈ [U, V, F, pk] := by simp
  have mF : F ∈ [U, V, F, pk] := by simp
  have mP : pk ∈ [U, V, F, pk] := by simp
  have h1l : tr.lo < 256 := by simp only [Tri.lo]; omega
  have h1h : tr.hi < 256 := by simp only [Tri.hi]; omega
  have nx (q : Wire) (hq : q ∈ [U, V, F, pk]) (i : Nat) (hi : i < 256) : w i ≠ q :=
    (tmpM q (tmpIn q hq) i hi).symm
  have eO := fun (q : Wire) (hq : q ∈ [U, V, F, pk]) =>
    endOff Tt one q inTt (tmp1 q hq).symm (offT q hq)
  have eM := fun (q : Wire) (hq : q ∈ [U, V, F, pk]) =>
    endOff Tm (endW one Tt) q inTm (eO q hq) (offT q hq)
  have hTall : ∀ y ∈ Tt ++ Tm ++ Tl, (y.2.1 ≠ U ∧ y.2.2 ≠ U) ∧ (y.2.1 ≠ V ∧ y.2.2 ≠ V) ∧
      (y.2.1 ≠ F ∧ y.2.2 ≠ F) := fun y hy =>
    ⟨offT U mU y (memT y hy), offT V mV y (memT y hy), offT F mF y (memT y hy)⟩
  have Pp : ProperProgram (preOf tr xs work one U V F) :=
    pre_proper _ _ _ _ _ _ _ _ _ _ _ _ _ _ (nx V mV _ h1l) UV (nx F mF _ h1h) VF (eM U mU) (eO V mV) hTall
  have pkNot : pk ∉ wires (preOf tr xs work one U V F) := by
    apply pre_not
    · exact ⟨tmp1 pk mP, Ne.symm UP, Ne.symm VP, Ne.symm FP, (nx pk mP _ h1l).symm, (nx pk mP _ h1h).symm,
        (eM pk mP).symm, (eO pk mP).symm⟩
    · intro y hy
      have := offT pk mP y (memT y hy)
      exact ⟨this.1.symm, this.2.symm⟩
  have gNot : g ∉ wires (preOf tr xs work one U V F) := by
    have gU : g ≠ U := fun e => (htx U (by simp)).2.2 e.symm
    have gV : g ≠ V := fun e => (htx V (by simp)).2.2 e.symm
    have gF : g ≠ F := fun e => (htx F (by simp)).2.2 e.symm
    apply pre_not
    · refine ⟨gone, gU, gV, gF, ?_, ?_, ?_, ?_⟩
      · exact fun e => (hextx g (by simp)).1 (e ▸ wmem _ h1l)
      · exact fun e => (hextx g (by simp)).1 (e ▸ wmem _ h1h)
      · exact (endOff Tm (endW one Tt) g inTm (endOff Tt one g inTt gone.symm offG) offG).symm
      · exact (endOff Tt one g inTt gone.symm offG).symm
    · intro y hy
      have := offG y (memT y hy)
      exact ⟨this.1.symm, this.2.symm⟩
  have wNot : ∀ q, q ∉ work → ∀ b ∈ bs, b.work ≠ q := fun q hq b hb e => hq (e ▸ bsW b hb)
  have tmpP : ∀ q ∈ [one, U, V, F, pk], q ∉ (i0 :: it).map w := fun q hq h =>
    (htx q hq).1 (Psub q (by rw [← hlP]; exact h))
  have Bt : ∀ q ∈ [one, U, V, F, pk], B.basis q = false := by
    intro q hq
    by_cases qf : q = f
    · rw [qf]; exact Bf
    · rw [Boff q qf (htx q hq).2.2, fill_outside _ _ _ q (wNot q (htx q hq).2.1),
        s2out q (tmpP q hq)]
      exact hto q hq qf
  have pivB (i : Nat) (hi : i = tr.r1 ∨ i = tr.r2) : B.basis (w i) = x.testBit i := by
    have hi256 : i < 256 := by rcases hi with rfl | rfl <;> [exact pv.1; exact pv.2.1]
    have nP : w i ∉ (i0 :: it).map w := by
      rcases hi with rfl | rfl <;> [exact x1P'; exact x2P']
    have nW : w i ∉ work := fun h => hdisj _ h (wmem i hi256)
    have nf : w i ≠ f := fun e => (hextx f (by simp)).1 (e ▸ wmem i hi256)
    have ng : w i ≠ g := fun e => (hextx g (by simp)).1 (e ▸ wmem i hi256)
    rw [Boff _ nf ng, fill_outside _ _ _ _ (wNot _ nW), s2out _ nP]
    exact xbit i hi256
  have hiP : tr.hi = tr.r1 ∨ tr.hi = tr.r2 := by simp only [Tri.hi]; omega
  have loP : tr.lo = tr.r1 ∨ tr.lo = tr.r2 := by simp only [Tri.lo]; omega
  have hxr1 : s.basis xr1 = x.testBit tr.r1 := xbit _ pv.1
  have hxr2 : s.basis xr2 = x.testBit tr.r2 := xbit _ pv.2.1
  let mtf : Nat → Bool := fun i => x.testBit i == tr.tgt i (x.testBit tr.r1, x.testBit tr.r2)
  have i0m : i0 ∈ tr.idx := by rw [hidx]; simp
  have itm : ∀ i ∈ it, i ∈ tr.idx := fun i hi => by rw [hidx]; simp [hi]
  have p0ne : one ≠ p0 := fun e => (htx one (by simp)).1 (e ▸ p0x)
  have p0f : p0 ≠ f := fun e => (hextx f (by simp)).1 (e ▸ p0x)
  have p0g : p0 ≠ g := fun e => (hextx g (by simp)).1 (e ▸ p0x)
  have p0W : p0 ∉ work := fun h => hdisj _ h p0x
  have hc0 : s2.basis p0 = mtf i0 := by
    rw [s2p0, hxr1, hxr2, xbit i0 (ix.2.2.2.2 i0 i0m)]
  have hchain : Chain (writeBit B.basis one true) mtf true (Tt ++ (Tm ++ Tl)) := by
    rw [cat, hT]
    refine ⟨by simp [writeBit], ?_, ?_⟩
    · simp only [writeBit, Function.update_apply, Ne.symm p0ne, if_false, Bool.true_and]
      rw [Boff _ p0f p0g, fill_outside _ _ _ _ (wNot _ p0W), hc0]
    · have hmt : ∀ k (hk : k < it.length), mtf it[k] = !s2.basis (bs[k]'(hlenbs ▸ hk)).input := by
        intro k hk
        have hin : (bs[k]'(hlenbs ▸ hk)).input = w it[k] := by
          have e1 : (bs.map ZeroBit.input)[k]'(by simpa using hlenbs ▸ hk) = (bs[k]'(hlenbs ▸ hk)).input := by
            simp
          have e2 : (it.map w)[k]'(by simpa using hk) = w it[k] := by simp
          rw [← e1, ← e2]
          exact List.getElem_of_eq zp.1 _
        have im : it[k] ∈ it := List.getElem_mem _
        rw [hin, s2it _ im, hxr1, hxr2, xbit _ (ix.2.2.2.2 _ (itm _ im))]
        simp only [mtf]
        cases x.testBit it[k] <;> cases tr.tgt it[k] (x.testBit tr.r1, x.testBit tr.r2) <;> rfl
      have cf := chain_fill mtf p0 it bs s2.basis (true && mtf i0) hlenbs chnd chz (by simpa using hc0) hmt
      apply chain_congr _ _ _ _ _ _ cf
      intro y hy
      have hyw := tri_wires _ _ _ y hy
      have side : ∀ q, (q = p0 ∨ ∃ b ∈ bs, q = b.work) →
          fill p0 bs s2.basis q = writeBit B.basis one true q := by
        intro q hq
        have qx : q ∈ xs ∨ q ∈ work := by
          rcases hq with e | ⟨b, hb, e⟩
          · exact Or.inl (e ▸ p0x)
          · exact Or.inr (e ▸ bsW b hb)
        have nf : q ≠ f := by
          intro e
          rcases qx with h | h
          · exact (hextx f (by simp)).1 (e ▸ h)
          · exact (hextx f (by simp)).2 (e ▸ h)
        have ng : q ≠ g := by
          intro e
          rcases qx with h | h
          · exact (hextx g (by simp)).1 (e ▸ h)
          · exact (hextx g (by simp)).2 (e ▸ h)
        have no : q ≠ one := by
          intro e
          rcases qx with h | h
          · exact (htx one (by simp)).1 (e ▸ h)
          · exact (htx one (by simp)).2.1 (e ▸ h)
        simp only [writeBit, Function.update_apply, no, if_false]
        exact (Boff q nf ng).symm
      exact ⟨side _ hyw.1, side _ (Or.inr hyw.2)⟩
  have nlo (q : Wire) (hq : q ∈ [U, V, F, pk]) : w tr.lo ≠ q := nx q hq _ h1l
  have nhi (q : Wire) (hq : q ∈ [U, V, F, pk]) : w tr.hi ≠ q := nx q hq _ h1h
  have FV := F_value tr v pv.2.2.1 x hx one U V F (w tr.hi) (w tr.lo) Tt Tm Tl mt mm ml UV UF VF
    (nlo U mU) (nlo V mV) (nlo F mF) (nhi U mU) (nhi V mV) (nhi F mF)
    (eM U mU) (eM V mV) (eM F mF) (eO U mU) (eO V mV) (eO F mF) oU oV oF
    (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1l)) (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1h))
    hTall B (Bt U (by simp)) (Bt V (by simp)) (Bt F (by simp)) (Bt one (by simp))
    (pivB _ hiP) (pivB _ loP) hchain
  have gpk : g ≠ pk := fun e => (htx pk (by simp)).2.2 e.symm
  have hE : ∀ m', run (extractFast_research tr xs work one U V F pk g) m' B =
      put B pk (B.basis pk ^^ ((run (preOf tr xs work one U V F) [] B).basis g &&
        (run (preOf tr xs work one U V F) [] B).basis F)) :=
    by
      intro m'
      have htpk : ∀ z ∈ correctionWires tr.A Tt, z ≠ pk := by
        apply correctionWires_off_research
        intro y hy
        exact offT pk mP y (inTt y hy)
      have hmpk : ∀ z ∈ correctionWires tr.A Tm, z ≠ pk := by
        apply correctionWires_off_research
        intro y hy
        exact offT pk mP y (inTm y hy)
      have hlpk : ∀ y ∈ Tl, y.2.1 ≠ pk ∧ y.2.2 ≠ pk := by
        intro y hy
        exact offT pk mP y (memT y (by simp [hy]))
      have fast := fastExtract_semantics tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi)
        one U V F (w tr.lo) (w tr.hi) (endW (endW one Tt) Tm) (endW one Tt) Tt Tm Tl g pk
        FP VP UP (nlo pk mP) (nhi pk mP) (eM pk mP) (eO pk mP) htpk hmpk oP hlpk UV UF VF
        (nlo U mU) (nlo V mV) (nlo F mF) (nhi U mU) (nhi V mV) (nhi F mF)
        (eM U mU) (eM V mV) (eM F mF) (eO U mU) (eO V mV) (eO F mF) oU oV oF
        (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1l))
        (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1h)) hTall B m'
        (Bt U (by simp)) (Bt V (by simp)) (Bt F (by simp))
      simpa only [extractFast_research, preOf, hTt, hTmm, hTl, hTdef, hw, put] using fast
  have hRg : (run (preOf tr xs work one U V F) [] B).basis g = B.basis g :=
    run_preserves_outside _ [] B g gNot
  have hval : (B.basis pk ^^ ((run (preOf tr xs work one U V F) [] B).basis g &&
      (run (preOf tr xs work one U V F) [] B).basis F)) = (B.basis g && decide (tr.A < x)) := by
    have e : (run (preOf tr xs work one U V F) [] B).basis F = decide (tr.A < x) := FV
    rw [Bt pk (by simp), hRg, e, Bool.false_xor]
  rw [hval] at hE
  have hpk1 : pk ∉ (p0 :: bs.flatMap ZeroBit.wires) := by
    intro h
    rcases List.mem_cons.mp h with e | h
    · exact (htx pk (by simp)).1 (e ▸ p0x)
    · obtain ⟨b, hb, hw'⟩ := List.mem_flatMap.mp h
      simp only [ZeroBit.wires, List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with e | e
      · obtain ⟨i, hi, e2⟩ := List.mem_map.mp (bsI b hb)
        exact (htx pk (by simp)).1 (e ▸ e2 ▸ wmem i (ix.2.2.2.2 i (itm i hi)))
      · exact (htx pk (by simp)).2.1 (e ▸ bsW b hb)
  have hpk2 : pk ∉ wires ([.X p0] ++ tr.remapList xr1 xr2 w (i0 :: it)) := by
    rw [wires_append]
    simp only [Finset.mem_union, not_or]
    refine ⟨?_, remapList_not tr xr1 xr2 w _ pk (nx pk mP _ pv.1).symm (nx pk mP _ pv.2.1).symm (tmpP pk (by simp))⟩
    have np : pk ≠ p0 := (nx pk mP i0 (ix.2.2.2.2 i0 i0m)).symm
    simp [wires, Instr.wires, np]
  have M := main (extractFast_research tr xs work one U V F pk g) pk _ hE hpk1 hpk2 m
  have hprog : classifier tr yb xs work y0 c f g g1 wB t =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (tail tr yb xr1 xr2 y0 c f g g1 wB t) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [classifier, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  have hprogF : classifierFast_research tr yb xs work y0 c f g g1 wB t one U V F pk =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (fun h => tail tr yb xr1 xr2 y0 c f g g1 wB t h ++ extractFast_research tr xs work one U V F pk g)
        (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [classifierFast_research, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  rw [hG, hprogF, hprog]
  exact M





theorem extractFast_counts_research (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F pk g : Wire) :
    toffoliCount (extractFast_research tr xs work one U V F pk g) ≤ 3 ∧
    measurementCount (extractFast_research tr xs work one U V F pk g) = 2 ∧
    Challenge.gateSlots (extractFast_research tr xs work one U V F pk g) ≤ 1035 := by
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  have hcounts := fastExtract_counts tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl
  have hslots := fastExtract_slots_research tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl
  have ix := Tri.idx_facts v
  have hl := triples_length xs work one tr.idx
  rw [ix.2.1] at hl
  have hsum : Tt.length + Tm.length + Tl.length ≤ 254 := by
    dsimp [Tt,Tm,Tl,T]
    simp only [List.length_take, List.length_drop]
    omega
  let P := fastExtract tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl
  change Challenge.gateSlots P ≤ 4 * (Tt.length + Tm.length + Tl.length) + 19 at hslots
  change toffoliCount P ≤ 3 ∧ measurementCount P = 2 ∧ Challenge.gateSlots P ≤ 1035
  exact ⟨hcounts.1, hcounts.2, by omega⟩
theorem classifierFast_researchast_counts_research (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire) (hwl : work.length = 253) :
    toffoliCount (classifierFast_research tr yb xs work y0 c f g g1 wB t one U V F pk) ≤ 259 ∧
    measurementCount (classifierFast_research tr yb xs work y0 c f g g1 wB t one U V F pk) = 259 ∧
    Challenge.gateSlots (classifierFast_research tr yb xs work y0 c f g g1 wB t one U V F pk) ≤ 3361 + 1035 := by
  obtain ⟨i0, it, hidx, hitl⟩ := InputSentinel.idx_split tr v
  have ix := Tri.idx_facts v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have ec := extractFast_counts_research tr v xs work one U V F pk g
  have zc := zeroWith_counts_general
    (fun h => tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h ++
      extractFast_research tr xs work one U V F pk g) (3 + toffoliCount (extractFast_research tr xs work one U V F pk g)) 6
    (fun h => by
      have tc := InputSentinel.tail_counts tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h
      rw [toffoliCount_append, measurementCount_append, tc.1, tc.2, ec.2.1]
      exact ⟨rfl, rfl⟩)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zc
  have zs := InputSentinel.zeroWith_slots
    (fun h => tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h ++
      extractFast_research tr xs work one U V F pk g)
    (Challenge.gateSlots (decodeT tr yb) + Challenge.gateSlots (extractFast_research tr xs work one U V F pk g))
    (fun h => by
      rw [Challenge.gateSlots_append, InputSentinel.tail_slots])
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zs
  have rs := InputSentinel.remapList_slots tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  rw [ix.2.1] at rs
  have ds := InputSentinel.decodeT_slots tr yb
  have rt := InputSentinel.remapList_tc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  have rm := remapList_mc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  unfold classifierFast_research
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append, rt, rm, zc.1, zc.2, zs]
  refine ⟨?_, by simp [measurementCount], ?_⟩
  · have := ec.1
    simp [toffoliCount]
    omega
  · have := ec.2.2
    simp only [Challenge.gateSlots, Challenge.instructionSlots, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at rs ds this ⊢
    omega





theorem extractFast_physical_research (tr : Tri) (v : tr.Valid) (xs work : List Wire)
    (one U V F pk g : Wire) (hlen : xs.length = 256)
    (hU : U ∉ xs ∧ U ∉ work ∧ U ≠ one) (hV : V ∉ xs ∧ V ∉ work ∧ V ≠ one)
    (hF : F ∉ xs ∧ F ∉ work ∧ F ≠ one) (UV : U ≠ V) (VF : V ≠ F) (Fp : F ≠ pk) (gp : g ≠ pk) :
    GatePhysical (extractFast_research tr xs work one U V F pk g) := by
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  have Pp := preOf_proper tr v xs work one U V F hlen hU hV hF UV VF
  have off := (preOf_off tr v xs work one U V F U hlen hU.1 hU.2.1 hU.2.2).1
  have hLow : ∀ x ∈ Tl, x.2.1 ≠ U ∧ x.2.2 ≠ U := by
    intro x hx
    have h := off x (List.mem_of_mem_drop hx)
    exact ⟨h.1.symm, h.2.symm⟩
  have hPre : ProperProgram (pre tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) Tt Tm Tl) := by
    exact Pp
  change GatePhysical (fastExtract tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl)
  exact fastExtract_physical _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPre gp Fp hLow

theorem classifierFast_researchast_physical_research (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire) (hlen : xs.length = 256)
    (hU : U ∉ xs ∧ U ∉ work ∧ U ≠ one) (hV : V ∉ xs ∧ V ∉ work ∧ V ≠ one)
    (hF : F ∉ xs ∧ F ∉ work ∧ F ≠ one) (UV : U ≠ V) (VF : V ≠ F) (Fp : F ≠ pk) (gp : g ≠ pk)
    (old : GatePhysical (classifier tr yb xs work y0 c f g g1 wB t)) :
    GatePhysical (classifierFast_research tr yb xs work y0 c f g g1 wB t one U V F pk) := by
  have hE := extractFast_physical_research tr v xs work one U V F pk g hlen hU hV hF UV VF Fp gp
  unfold classifier at old
  simp only [gatePhysical_append] at old
  unfold classifierFast_research
  simp only [gatePhysical_append]
  exact ⟨old.1, old.2.1, zeroWith_app_physical _ _ hE _ _ old.2.2.1, old.2.2.2⟩





theorem correctionWires_in_research (a : Nat) (ts : List (Nat × Wire × Wire)) (W : Finset Wire)
    (h : ∀ x ∈ ts, x.2.1 ∈ W ∧ x.2.2 ∈ W) : ∀ w ∈ correctionWires a ts, w ∈ W := by
  induction ts with
  | nil => simp [correctionWires]
  | cons x xs ih =>
    obtain ⟨i,p,c⟩ := x
    have hp := h (i,p,c) (by simp)
    have hr : ∀ x ∈ xs, x.2.1 ∈ W ∧ x.2.2 ∈ W := by intro x hx; exact h x (by simp [hx])
    intro w hw
    cases hb : a.testBit i
    · simp [correctionWires, hb] at hw
      rcases hw with rfl | rfl | hw
      · exact hp.1
      · exact hp.2
      · exact ih hr w hw
    · simp [correctionWires, hb] at hw
      exact ih hr w hw

theorem zCorrections_sub_research (ws : List Wire) (W : Finset Wire) (h : ∀ w ∈ ws, w ∈ W) :
    ECDSAAdd.correctionWires (ws.map Correction.Z) ⊆ W := by
  induction ws with
  | nil => simp [ECDSAAdd.correctionWires]
  | cons w ws ih =>
    have hw : w ∈ W := h w (by simp)
    have hr : ∀ x ∈ ws, x ∈ W := by intro x hx; exact h x (by simp [hx])
    simp only [List.map_cons, ECDSAAdd.correctionWires, Finset.union_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hw, ih hr⟩

theorem compareCorrections_sub_research (bit : Bool) (x v e : Wire) (ws : List Wire) (W : Finset Wire)
    (hx : x ∈ W) (hv : v ∈ W) (he : e ∈ W) (hws : ∀ w ∈ ws, w ∈ W) :
    ECDSAAdd.correctionWires (compareCorrections bit x v e ws) ⊆ W := by
  have hz := zCorrections_sub_research ws W hws
  cases bit <;> simp [compareCorrections, ECDSAAdd.correctionWires, Finset.union_subset_iff,
    Finset.insert_subset_iff, hx, hv, he, hz]

theorem clearFV_sub_research (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh : Wire)
    (top mid : List (Nat × Wire × Wire)) (W : Finset Wire)
    (hU : U ∈ W) (hV : V ∈ W) (hF : F ∈ W) (hlo : xlo ∈ W) (hhi : xhi ∈ W)
    (hel : el ∈ W) (heh : eh ∈ W)
    (htop : ∀ x ∈ top, x.2.1 ∈ W ∧ x.2.2 ∈ W) (hmid : ∀ x ∈ mid, x.2.1 ∈ W ∧ x.2.2 ∈ W) :
    wires (clearFV a aL aH U V F xlo xhi el eh top mid) ⊆ W := by
  have ht := compareCorrections_sub_research aH xhi V eh (correctionWires a top) W hhi hV heh
    (correctionWires_in_research a top W htop)
  have hm := compareCorrections_sub_research aL xlo U el (correctionWires a mid) W hlo hU hel
    (correctionWires_in_research a mid W hmid)
  simp [clearFV, wires, Instr.wires, ECDSAAdd.correctionWires, Finset.union_subset_iff,
    Finset.insert_subset_iff, hF, hV, ht, hm]

theorem xorAcc_sub_research (a : Nat) (U : Wire) (ts : List (Nat × Wire × Wire)) (W : Finset Wire)
    (hU : U ∈ W) (hT : ∀ x ∈ ts, x.2.1 ∈ W ∧ x.2.2 ∈ W) : wires (xorAcc a U ts) ⊆ W := by
  intro q hq
  apply Classical.byContradiction
  intro hn
  have qu : q ≠ U := fun e => hn (e ▸ hU)
  have ht : ∀ x ∈ ts, q ≠ x.2.1 ∧ q ≠ x.2.2 := by
    intro x hx
    exact ⟨fun e => hn (e ▸ (hT x hx).1), fun e => hn (e ▸ (hT x hx).2)⟩
  exact xorAcc_not a U q ts qu ht hq

theorem finishUOne_sub_research (a : Nat) (one U : Wire) (low : List (Nat × Wire × Wire)) (W : Finset Wire)
    (hone : one ∈ W) (hU : U ∈ W) (hlow : ∀ x ∈ low, x.2.1 ∈ W ∧ x.2.2 ∈ W) :
    wires (finishUOne a one U low) ⊆ W := by
  unfold finishUOne
  rw [wires_append]
  exact Finset.union_subset (xorAcc_sub_research a U low W hU hlow) (by simp [wires, Instr.wires, hone])
theorem extractFast_sub_research (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F pk g : Wire)
    (hlen : xs.length = 256) (W : Finset Wire) (hx : ∀ q ∈ xs, q ∈ W) (hw : ∀ q ∈ work, q ∈ W)
    (h1 : one ∈ W) (h2 : U ∈ W) (h3 : V ∈ W) (h4 : F ∈ W) (h5 : pk ∈ W) (h6 : g ∈ W) :
    wires (extractFast_research tr xs work one U V F pk g) ⊆ W := by
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  have ix := Tri.idx_facts v
  have pv := Tri.pivots v
  have hAll : ∀ y ∈ T, y.2.1 ∈ W ∧ y.2.2 ∈ W := by
    intro y hy
    have h := triples_wires xs work one tr.idx ix.2.2.2.2 hlen y hy
    constructor
    · rcases h.1 with e | e | e
      · rw [e]; exact h1
      · exact hx _ e
      · exact hw _ e
    · rcases h.2 with e | e
      · exact hx _ e
      · exact hw _ e
  have htop : ∀ y ∈ Tt, y.2.1 ∈ W ∧ y.2.2 ∈ W := fun y hy => hAll y (List.mem_of_mem_take hy)
  have hmid : ∀ y ∈ Tm, y.2.1 ∈ W ∧ y.2.2 ∈ W := fun y hy => hAll y (List.mem_of_mem_drop (List.mem_of_mem_take hy))
  have hlow : ∀ y ∈ Tl, y.2.1 ∈ W ∧ y.2.2 ∈ W := fun y hy => hAll y (List.mem_of_mem_drop hy)
  have heh : endW one Tt ∈ W := by
    rcases endW_mem one Tt with e | ⟨y, hy, e⟩
    · rw [e]; exact h1
    · rw [e]; exact (htop y hy).2
  have hel : endW (endW one Tt) Tm ∈ W := by
    rcases endW_mem (endW one Tt) Tm with e | ⟨y, hy, e⟩
    · rw [e]; exact heh
    · rw [e]; exact (hmid y hy).2
  have hloN : tr.lo < 256 := by simp only [Tri.lo]; omega
  have hhiN : tr.hi < 256 := by simp only [Tri.hi]; omega
  have hlo : xs.getD tr.lo 0 ∈ W := by
    apply hx
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hhi : xs.getD tr.hi 0 ∈ W := by
    apply hx
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hpre : wires (pre tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) Tt Tm Tl) ⊆ W := by
    exact preOf_sub tr v xs work one U V F hlen W hx hw h1 h2 h3 h4
  have hcc : wires [.CCX g F pk] ⊆ W := by simp [wires, Instr.wires, Finset.insert_subset_iff, h4, h5, h6]
  have hclear := clearFV_sub_research tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) Tt Tm W h2 h3 h4 hlo hhi hel heh htop hmid
  have hfinish := finishUOne_sub_research tr.A one U Tl W h1 h2 hlow
  change wires (fastExtract tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl) ⊆ W
  simp only [fastExtract, wires_append, Finset.union_subset_iff]
  exact ⟨hpre, ⟨⟨hcc, hclear⟩, hfinish⟩⟩

theorem classifierFast_researchast_wires_research (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire) (hlen : xs.length = 256) (W : Finset Wire)
    (hc : wires (classifier tr yb xs work y0 c f g g1 wB t) ⊆ W)
    (hx : ∀ q ∈ xs, q ∈ W) (hw : ∀ q ∈ work, q ∈ W)
    (h1 : one ∈ W) (h2 : U ∈ W) (h3 : V ∈ W) (h4 : F ∈ W) (h5 : pk ∈ W) (h6 : g ∈ W) :
    wires (classifierFast_research tr yb xs work y0 c f g g1 wB t one U V F pk) ⊆ W := by
  have E := extractFast_sub_research tr v xs work one U V F pk g hlen W hx hw h1 h2 h3 h4 h5 h6
  unfold classifier at hc
  simp only [wires_append, Finset.union_subset_iff] at hc
  unfold classifierFast_research
  simp only [wires_append, Finset.union_subset_iff]
  exact ⟨hc.1, hc.2.1, (zeroWith_app_wires _ _ _ _).trans (Finset.union_subset hc.2.2.1 E), hc.2.2.2⟩


/-- The extraction with the copy into `pk` replaced by an X measurement of `pk`.
It is only for a `pk` that already holds `g & F`: the copy would clear it, and so does the
measurement, whose outcome-1 phase `pk` the correction `CZ g F` cancels. -/
def fastClear (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) : Program :=
  pre a aL aH one U V F xlo xhi el eh top mid low ++
    ([Instr.measureX pk [] [Correction.CZ g F]] ++ clearFV a aL aH U V F xlo xhi el eh top mid ++
      finishUOne a one U low)

def extractClear_research (tr : Tri) (xs work : List Wire) (one U V F pk g : Wire) : Program :=
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  fastClear tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl

theorem xor_false_eq {a b : Bool} (h : (a ^^ b) = false) : a = b := by
  revert h; cases a <;> cases b <;> decide

theorem clear_swap (P C D : Program) (g F pk : Wire) (hp : measurementCount P = 0)
    (hg : g ≠ pk) (hF : F ≠ pk) (s : State) (m : List Bool)
    (hv : (run P [] s).basis pk = ((run P [] s).basis g && (run P [] s).basis F)) :
    run (P ++ (([Instr.measureX pk [] [Correction.CZ g F]] ++ C) ++ D)) m s =
      run (P ++ (([Instr.CCX g F pk] ++ C) ++ D)) (m.drop 1) s := by
  obtain ⟨r, hr⟩ : ∃ r, r = run P [] s := ⟨_, rfl⟩
  rw [← hr] at hv
  have e1 := eraseOneProductLinear g F pk [] hg hF (by simp) r (m.take 1)
    (by simpa [ECDSAAdd.parityAt] using hv)
  simp only [List.map_nil, List.append_nil] at e1
  have e2 : run [Instr.CCX g F pk] [] r = ⟨r.phase, writeBit r.basis pk false⟩ := by
    simp only [run]
    rw [hv]
    simp
  have c1 : measurementCount ([Instr.measureX pk [] [Correction.CZ g F]] : Program) = 1 := rfl
  have c2 : measurementCount ([Instr.CCX g F pk] : Program) = 0 := rfl
  rw [run_append P _ m s, run_append P _ (m.drop 1) s]
  simp only [hp, List.take_zero, List.drop_zero, ← hr]
  rw [List.append_assoc, List.append_assoc, run_append _ (C ++ D) m r,
    run_append _ (C ++ D) (m.drop 1) r, c1, c2]
  simp only [List.take_zero, List.drop_zero]
  rw [e1, e2]

theorem fastClear_run (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) (s : State) (m : List Bool)
    (hg : g ≠ pk) (hF : F ≠ pk)
    (hv : (run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis pk =
      ((run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis g &&
        (run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis F)) :
    run (fastClear a aL aH one U V F xlo xhi el eh g pk top mid low) m s =
      run (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) (m.drop 1) s := by
  unfold fastClear fastExtract
  exact clear_swap _ _ _ g F pk (pre_counts a aL aH one U V F xlo xhi el eh top mid low).2.1
    hg hF s m hv

theorem fastClear_counts (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) :
    toffoliCount (fastClear a aL aH one U V F xlo xhi el eh g pk top mid low) + 1 =
      toffoliCount (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) ∧
    measurementCount (fastClear a aL aH one U V F xlo xhi el eh g pk top mid low) =
      measurementCount (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) + 1 ∧
    Challenge.gateSlots (fastClear a aL aH one U V F xlo xhi el eh g pk top mid low) =
      Challenge.gateSlots (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) + 1 := by
  have t1 : toffoliCount ([Instr.measureX pk [] [Correction.CZ g F]] : Program) = 0 := rfl
  have t2 : toffoliCount ([Instr.CCX g F pk] : Program) = 1 := rfl
  have m1 : measurementCount ([Instr.measureX pk [] [Correction.CZ g F]] : Program) = 1 := rfl
  have m2 : measurementCount ([Instr.CCX g F pk] : Program) = 0 := rfl
  have s1 : Challenge.gateSlots ([Instr.measureX pk [] [Correction.CZ g F]] : Program) = 2 := by
    simp [Challenge.gateSlots, Challenge.instructionSlots]
  have s2 : Challenge.gateSlots ([Instr.CCX g F pk] : Program) = 1 := by
    simp [Challenge.gateSlots, Challenge.instructionSlots]
  simp only [fastClear, fastExtract, toffoliCount_append, measurementCount_append,
    Challenge.gateSlots_append, t1, t2, m1, m2, s1, s2]
  omega

theorem fastClear_physical (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (h : Arithmetic.GatePhysical (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low)) :
    Arithmetic.GatePhysical (fastClear a aL aH one U V F xlo xhi el eh g pk top mid low) := by
  simp only [fastExtract, Arithmetic.gatePhysical_append] at h
  simp only [fastClear, Arithmetic.gatePhysical_append]
  exact ⟨h.1, ⟨by simp [Arithmetic.GatePhysical, RecordedQuantum.PhysicalInstr], h.2.1.2⟩, h.2.2⟩

theorem fastClear_wires (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) :
    wires (fastClear a aL aH one U V F xlo xhi el eh g pk top mid low) =
      wires (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) := by
  have e : wires ([Instr.measureX pk [] [Correction.CZ g F]] : Program) =
      wires ([Instr.CCX g F pk] : Program) := by
    ext q
    simp [wires, Instr.wires, ECDSAAdd.correctionWires]; tauto
  simp only [fastClear, fastExtract, wires_append, e]

theorem extractClear_run_research (tr : Tri) (xs work : List Wire) (one U V F pk g : Wire)
    (s : State) (m : List Bool) (hg : g ≠ pk) (hF : F ≠ pk)
    (hv : (run (preOf tr xs work one U V F) [] s).basis pk =
      ((run (preOf tr xs work one U V F) [] s).basis g &&
        (run (preOf tr xs work one U V F) [] s).basis F)) :
    run (extractClear_research tr xs work one U V F pk g) m s =
      run (extractFast_research tr xs work one U V F pk g) (m.drop 1) s := by
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  exact fastClear_run tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl s m hg hF hv

theorem extractClear_counts_research (tr : Tri) (v : tr.Valid) (xs work : List Wire)
    (one U V F pk g : Wire) :
    toffoliCount (extractClear_research tr xs work one U V F pk g) ≤ 2 ∧
    measurementCount (extractClear_research tr xs work one U V F pk g) = 3 ∧
    Challenge.gateSlots (extractClear_research tr xs work one U V F pk g) ≤ 1036 := by
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  have h := extractFast_counts_research tr v xs work one U V F pk g
  have c : toffoliCount (extractClear_research tr xs work one U V F pk g) + 1 =
        toffoliCount (extractFast_research tr xs work one U V F pk g) ∧
      measurementCount (extractClear_research tr xs work one U V F pk g) =
        measurementCount (extractFast_research tr xs work one U V F pk g) + 1 ∧
      Challenge.gateSlots (extractClear_research tr xs work one U V F pk g) =
        Challenge.gateSlots (extractFast_research tr xs work one U V F pk g) + 1 :=
    fastClear_counts tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
      (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl
  omega

theorem extractClear_physical_research (tr : Tri) (v : tr.Valid) (xs work : List Wire)
    (one U V F pk g : Wire) (hlen : xs.length = 256)
    (hU : U ∉ xs ∧ U ∉ work ∧ U ≠ one) (hV : V ∉ xs ∧ V ∉ work ∧ V ≠ one)
    (hF : F ∉ xs ∧ F ∉ work ∧ F ≠ one) (UV : U ≠ V) (VF : V ≠ F) (Fp : F ≠ pk) (gp : g ≠ pk) :
    GatePhysical (extractClear_research tr xs work one U V F pk g) := by
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  exact fastClear_physical tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl
    (extractFast_physical_research tr v xs work one U V F pk g hlen hU hV hF UV VF Fp gp)

theorem extractClear_sub_research (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F pk g : Wire)
    (hlen : xs.length = 256) (W : Finset Wire) (hx : ∀ q ∈ xs, q ∈ W) (hw : ∀ q ∈ work, q ∈ W)
    (h1 : one ∈ W) (h2 : U ∈ W) (h3 : V ∈ W) (h4 : F ∈ W) (h5 : pk ∈ W) (h6 : g ∈ W) :
    wires (extractClear_research tr xs work one U V F pk g) ⊆ W := by
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  have e : wires (extractClear_research tr xs work one U V F pk g) =
      wires (extractFast_research tr xs work one U V F pk g) :=
    fastClear_wires tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
      (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl
  rw [e]
  exact extractFast_sub_research tr v xs work one U V F pk g hlen W hx hw h1 h2 h3 h4 h5 h6

end Shape

end ECDSAAdd.Entrant.ZeroFill

end

section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FlagEntry
open Arithmetic Challenge RecordedQuantum NativeFirstDirect MappedCompressed
open ParityXEntry E1Merge E1WholeKAdd52Research Secp256k1 ControlledPointLayout
open ParityCarry ParityConvert ParityEven EntryFuseArithmetic ParityUniform

/-- Two CNOTs moving a set bit from `pk` to the clean wire `a`. -/
def swp (pk a : Wire) : Program := [.CX pk a, .CX a pk]

theorem swp_run (pk a : Wire) (hne : pk ≠ a) (s : State) (m : List Bool)
    (ha : s.basis a = false) :
    run (swp pk a) m s = put (put s pk false) a (s.basis pk) := by
  apply State.extensionality
  · rfl
  · funext q
    by_cases q1 : q = pk
    · subst q1; simp [swp, run, put, writeBit, hne, ha]
    · by_cases q2 : q = a
      · subst q2; simp [swp, run, put, writeBit, Ne.symm hne, ha]
      · simp [swp, run, put, writeBit, q1, q2]

/-- Two renamed runs agree when their pulled runs agree and the states agree off the image. -/
theorem rename_eq2 (f : Wire → Wire) (S : Finset Wire) (inj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b)
    (P Q : Program) (hP : wires P ⊆ S) (hQ : wires Q ⊆ S) (a b ta tb : State) (m1 m2 : List Bool)
    (hpa : ta.phase = a.phase) (hma : ∀ q ∈ S, ta.basis q = a.basis (f q))
    (hpb : tb.phase = b.phase) (hmb : ∀ q ∈ S, tb.basis q = b.basis (f q))
    (eq : run P m1 ta = run Q m2 tb) (hout : ∀ q, q ∉ S.image f → a.basis q = b.basis q) :
    run (renameProgram f P) m1 a = run (renameProgram f Q) m2 b := by
  have A := run_rename_pool f S inj P hP m1 ta a hpa hma
  have B := run_rename_pool f S inj Q hQ m2 tb b hpb hmb
  rw [eq] at A
  apply State.extensionality
  · exact A.1.trans B.1.symm
  funext q
  by_cases im : q ∈ S.image f
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp im
    exact (A.2 c hc).trans (B.2 c hc).symm
  · rw [run_rename_pool_outside f S P hP m1 a q im, run_rename_pool_outside f S Q hQ m2 b q im]
    exact hout q im

/-- The comparison leaves the flag and nothing else. -/
theorem compare_post (k X : Nat) (hk : k < ECDSAAdd.p) (hX : X < ECDSAAdd.p) (s : State) (m : List Bool)
    (hx : regValue (xR base) s.basis = X) (hs : regValue (srcR base) s.basis = 0)
    (hf : s.basis (base 514) = false) (hc : s.basis (base 513) = false)
    (hcarry : ∀ q ∈ cR base, s.basis q = false) :
    run (comparePart base (base 2400) k) m s =
      put s (base 514) (if s.basis (base 2400) then decide (EntryFuseArithmetic.prime ≤ X + k) else false) := by
  let K := compareLayout base
  have hw := compareLayout_widths base
  have hn := compareLayout_nodup
  have primeBound : X < EntryFuseArithmetic.prime := by rw [EntryFuse.prime_eq_secp]; exact hX
  have kBound : k < EntryFuseArithmetic.prime := by rw [EntryFuse.prime_eq_secp]; exact hk
  have pc : EntryFuseArithmetic.prime + complement = 2^256 := by
    norm_num [EntryFuseArithmetic.prime, modulus, complement]
  have initial : FastConst.Frame K s.basis 0 X false s.basis := ⟨hs, hx, hf, by intro q hq; rfl⟩
  have pre := EntryFuse.comparePrefix_correct hn 256 hw s.basis hcarry hc complement
    EntryFuseArithmetic.prime k X pc kBound primeBound s m initial
  have oe : comparePart base (base 2400) k = EntryFuse.comparePrefix K (base 2400) complement k := by
    rw [comparePart_eq]
    simp only [K, comparePrefixOld, loadNot, unloadNot, EntryFuse.comparePrefix, List.append_assoc]
  rw [oe]
  obtain ⟨ph, fr1, fr2, fr3, fr4⟩ := pre
  apply State.extensionality
  · exact ph
  · funext q
    by_cases q1 : q = base 514
    · subst q1
      have : (run (EntryFuse.comparePrefix K (base 2400) complement k) m s).basis K.flag = _ := fr3
      simpa [put, writeBit, K, compareLayout] using this
    · have r : (put s (base 514) (if s.basis (base 2400) then decide (EntryFuseArithmetic.prime ≤ X + k) else false)).basis q = s.basis q := by
        simp [put, writeBit, q1]
      rw [r]
      by_cases q2 : q ∈ K.src
      · exact (regValue_eq_iff K.src _ _).mp (fr1.trans hs.symm) q q2
      by_cases q3 : q ∈ K.out
      · exact (regValue_eq_iff K.out _ _).mp (fr2.trans hx.symm) q q3
      apply fr4
      simp only [FastConst.mutable, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨q2, q3⟩, q1⟩

/-- The X entry with the comparison replaced by reading the flag from `pk`. -/
def entryXNew (L : ControlledPointLayout) (pk : Wire) (k : Fp) : Program :=
  if k.val % 2 = 1 then
    swp pk (E1QubitPlacement.pmapR L (base 514)) ++
      renameProgram (E1QubitPlacement.pmapR L) (tailX base (base 2400) k.val)
  else
    renameProgram (E1QubitPlacement.pmapR L) [.CCX (base 2400) (base 770) (base 721)] ++
      (swp pk (E1QubitPlacement.pmapR L (base 514)) ++
        renameProgram (E1QubitPlacement.pmapR L) (evenTail k.val))

/-- Facts about the pulled state that the X entry needs. -/
structure Pulled (t : State) (X : Nat) : Prop where
  xval : regValue (xR base) t.basis = X
  src : regValue (srcR base) t.basis = 0
  f514 : t.basis (base 514) = false
  f513 : t.basis (base 513) = false
  f721 : t.basis (base 721) = false
  f1028 : t.basis (base 1028) = false
  carry : ∀ q ∈ cR base, t.basis q = false

theorem tailX_S (k : Nat) : wires (tailX base (base 2400) k) ⊆ E1QubitPlacement.S := by
  have h := E1QubitPlacement.merged_S k
  rw [merged_split, wires_append] at h
  exact Finset.union_subset_right h

theorem compare_S (k : Nat) : wires (comparePart base (base 2400) k) ⊆ E1QubitPlacement.S := by
  have h := E1QubitPlacement.merged_S k
  rw [merged_split, wires_append] at h
  exact Finset.union_subset_left h

theorem evenTail_S (k : Nat) : wires (evenTail k) ⊆ E1QubitPlacement.S :=
  (evenTail_wires k).trans (tailX_S k)

theorem run_pad (A B : Program) (m : List Bool) (s : State) :
    run (A ++ B) (List.replicate (measurementCount A) false ++ m) s =
      run B m (run A (List.replicate (measurementCount A) false) s) := by
  rw [run_append]
  congr 1
  · simp
  · rw [← run_take A _ s]
    congr 1
    simp

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pulled_facts (X : Fp) (u : State) (hx : regValue L.point.x u.basis = X.val)
    (hc : regValue L.dialogPool u.basis = 0) :
    Pulled (pullState (E1QubitPlacement.pmapR L) u) X.val := by
  have pool := E1QubitPlacement.pmap_pool L hw hn
  have hzero := (regValue_zero _ _).mp hc
  let F := E1QubitPlacement.pmapR L
  let t := pullState F u
  have clean (q : Wire) (hq : q ∈ E1QubitPlacement.S) (notx : q ∉ wireBlock base 770 256)
      (notg : q ≠ base 2400) : t.basis q = false := hzero _ (pool q hq notx notg)
  have inS (i : Nat) (hi : i < 515 ∨ i = 721 ∨ i = 1028) : base i ∈ E1QubitPlacement.S :=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i (by omega))
  have notx (i : Nat) (hi : i < 770 ∨ 1026 ≤ i) : base i ∉ wireBlock base 770 256 := by
    intro H
    obtain ⟨j, hj, e⟩ := List.mem_map.mp H
    have E := base_injective e
    simp only [List.mem_range'_1] at hj
    omega
  have cl (i : Nat) (hi : i < 515 ∨ i = 721 ∨ i = 1028) : t.basis (base i) = false :=
    clean _ (inS i hi) (notx i (by omega)) (fun E => by have e := base_injective E; omega)
  refine ⟨?_, ?_, cl 514 (by omega), cl 513 (by omega), cl 721 (by simp), cl 1028 (by simp), ?_⟩
  · change regValue (wireBlock base 770 256) (fun q => u.basis (F q)) = X.val
    rw [E1QubitPlacement.regValue_pull, E1QubitPlacement.pmap_x L hw hn, hx]
  · apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (Or.inl (by omega))
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (Or.inl (by omega))

/-- Renamed comparison: only the flag wire changes. -/
theorem compare_rename (X k : Fp) (u : State) (hx : regValue L.point.x u.basis = X.val)
    (hc : regValue L.dialogPool u.basis = 0) (m : List Bool) :
    run (renameProgram (E1QubitPlacement.pmapR L) (comparePart base (base 2400) k.val)) m u =
      put u (E1QubitPlacement.pmapR L (base 514))
        (if u.basis L.core.generic then decide (prime ≤ X.val + k.val) else false) := by
  have P := pulled_facts L hw hn X u hx hc
  have inj := E1QubitPlacement.pmap_inj L hw hn
  let F := E1QubitPlacement.pmapR L
  let t := pullState F u
  have s514 : base 514 ∈ E1QubitPlacement.S :=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) 514 (by omega))
  have C := compare_post k.val X.val k.isLt X.isLt t m P.xval P.src P.f514 P.f513 P.carry
  have tg : t.basis (base 2400) = u.basis L.core.generic := by
    change u.basis (F (base 2400)) = _
    have e : F (base 2400) = L.core.generic := E1QubitPlacement.pmap_g L hw hn
    rw [e]
  rw [tg] at C
  have A := run_rename_pool F E1QubitPlacement.S inj _ (compare_S k.val) m t u rfl (by intro q hq; rfl)
  rw [C] at A
  apply State.extensionality
  · exact A.1
  funext q
  by_cases im : q ∈ E1QubitPlacement.S.image F
  · obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp im
    rw [A.2 c hc']
    by_cases e : c = base 514
    · subst e; simp [put, writeBit, F]
    · have ne : F c ≠ F (base 514) := fun E => e (inj _ hc' _ s514 E)
      simp only [put, writeBit, Function.update_apply, e, if_false]
      show u.basis (F c) = _
      simp [F, ne]
  · rw [run_rename_pool_outside F E1QubitPlacement.S _ (compare_S k.val) m u q im]
    have ne : q ≠ F (base 514) := fun e => im (e ▸ Finset.mem_image_of_mem F s514)
    simp [put, writeBit, F] at ne ⊢
    simp [ne]

theorem entryXNew_run (pk : Wire) (X k : Fp) (u : State)
    (hx : regValue L.point.x u.basis = X.val) (hc : regValue L.dialogPool u.basis = 0)
    (hpk : pk ∈ L.dialogPool) (h514 : pk ≠ E1QubitPlacement.pmapR L (base 514))
    (h721 : pk ≠ E1QubitPlacement.pmapR L (base 721))
    (h770 : pk ≠ E1QubitPlacement.pmapR L (base 770))
    (h2400 : pk ≠ E1QubitPlacement.pmapR L (base 2400)) (m : List Bool) :
    run (entryXNew L pk k) m
        (put u pk (if u.basis L.core.generic then decide (prime ≤ X.val + k.val) else false)) =
      run (entryXAll L k)
        (List.replicate (measurementCount (comparePart base (base 2400) k.val)) false ++ m) u := by
  have inj := E1QubitPlacement.pmap_inj L hw hn
  have P := pulled_facts L hw hn X u hx hc
  set F := E1QubitPlacement.pmapR L with hFdef
  set f : Bool := if u.basis L.core.generic then decide (prime ≤ X.val + k.val) else false with hf
  let n := measurementCount (comparePart base (base 2400) k.val)
  let W := put u (F (base 514)) f
  have upk : u.basis pk = false := (regValue_zero _ _).mp hc pk hpk
  have u514 : u.basis (F (base 514)) = false := P.f514
  have u721 : u.basis (F (base 721)) = false := P.f721
  have u1028 : u.basis (F (base 1028)) = false := P.f1028
  have s514 : base 514 ∈ E1QubitPlacement.S :=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) 514 (by omega))
  have s721 : base 721 ∈ E1QubitPlacement.S :=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) 721 (by omega))
  have s1028 : base 1028 ∈ E1QubitPlacement.S :=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) 1028 (by omega))
  have ctl := (tail_control_wires k.val).trans (tailX_S k.val)
  have s2400 : base 2400 ∈ E1QubitPlacement.S := ctl (by simp)
  have s770 : base 770 ∈ E1QubitPlacement.S := ctl (by simp)
  have Fne (i j : Nat) (hi : base i ∈ E1QubitPlacement.S) (hj : base j ∈ E1QubitPlacement.S)
      (hij : i ≠ j) : F (base i) ≠ F (base j) :=
    fun E => hij (base_injective (inj _ hi _ hj E))
  -- the old side
  have old : run (entryXAll L k) (List.replicate n false ++ m) u =
      run (renameProgram F (tailX base (base 2400) k.val)) m W := by
    rw [entryXAll_eq L hw hn X k u _ hx hc]
    change run (renameProgram F (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val)) _ u = _
    rw [merged_split]
    have e : renameProgram F (comparePart base (base 2400) k.val ++ tailX base (base 2400) k.val) =
        renameProgram F (comparePart base (base 2400) k.val) ++
          renameProgram F (tailX base (base 2400) k.val) := by
      simp [renameProgram, List.map_append]
    have cnt : measurementCount (renameProgram F (comparePart base (base 2400) k.val)) = n :=
      (renameProgram_counts _ _).2
    rw [e]
    have pad := run_pad (renameProgram F (comparePart base (base 2400) k.val))
      (renameProgram F (tailX base (base 2400) k.val)) m u
    rw [cnt] at pad
    rw [pad, compare_rename L hw hn X k u hx hc]
  rw [old]
  unfold entryXNew
  simp only [← hFdef]
  have mz : measurementCount (swp pk (F (base 514))) = 0 := by simp [swp, measurementCount]
  by_cases he : k.val % 2 = 1
  · rw [if_pos he, run_append, run_take]
    rw [mz, List.drop_zero]
    congr 1
    rw [swp_run pk _ h514 _ _ (by simpa [put, writeBit, Ne.symm h514] using u514)]
    apply State.extensionality
    · rfl
    funext q
    by_cases q1 : q = F (base 514)
    · subst q1; simp [put, writeBit, W, h514]
    · by_cases q2 : q = pk
      · subst q2; simp [put, writeBit, W, q1, upk]
      · simp [put, writeBit, W, q1, q2]
  · rw [if_neg he]
    have even : k.val % 2 = 0 := by omega
    let A := u.basis (F (base 2400)) && u.basis (F (base 770))
    let v := put u pk f
    have n7a : F (base 514) ≠ F (base 721) := Fne 514 721 s514 s721 (by decide)
    have n7b : F (base 514) ≠ F (base 2400) := Fne 514 2400 s514 s2400 (by decide)
    have n7c : F (base 514) ≠ F (base 770) := Fne 514 770 s514 s770 (by decide)
    have n7d : F (base 514) ≠ F (base 1028) := Fne 514 1028 s514 s1028 (by decide)
    have n7e : F (base 721) ≠ F (base 2400) := Fne 721 2400 s721 s2400 (by decide)
    have n7f : F (base 721) ≠ F (base 770) := Fne 721 770 s721 s770 (by decide)
    have c1 : ∀ mm, run (renameProgram F [.CCX (base 2400) (base 770) (base 721)]) mm v =
        put v (F (base 721)) A := by
      intro mm
      apply State.extensionality
      · rfl
      funext q
      by_cases q1 : q = F (base 721)
      · subst q1
        simp [renameProgram, renameInstr, run, put, writeBit, v, A, u721, Ne.symm h721, n7e, n7f,
          Ne.symm h2400, Ne.symm h770, h721, h2400, h770]
      · simp [renameProgram, renameInstr, run, put, writeBit, v, q1]
    have mc1 : measurementCount (renameProgram F [.CCX (base 2400) (base 770) (base 721)]) = 0 := by
      simp [renameProgram, renameInstr, measurementCount]
    rw [run_append, run_take, mc1, List.drop_zero, c1, run_append, run_take, mz, List.drop_zero]
    rw [swp_run pk _ h514 _ _ (by simp [put, writeBit, v, Ne.symm h514, n7a, u514])]
    have s3 : put (put (put v (F (base 721)) A) pk false) (F (base 514))
        ((put v (F (base 721)) A).basis pk) = put W (F (base 721)) A := by
      apply State.extensionality
      · rfl
      funext q
      by_cases q1 : q = F (base 514)
      · subst q1; simp [put, writeBit, W, v, h721, n7a, h514]
      · by_cases q2 : q = pk
        · subst q2; simp [put, writeBit, W, v, q1, upk, h721]
        · by_cases q3 : q = F (base 721)
          · subst q3; simp [put, writeBit, W, v, q1, q2]
          · simp [put, writeBit, W, v, q1, q2, q3]
    rw [s3]
    let tW := pullState F W
    have tg : tW.basis (base 2400) = u.basis (F (base 2400)) := by
      change W.basis (F (base 2400)) = _
      simp [W, put, writeBit, Ne.symm n7b]
    have tx : tW.basis (base 770) = u.basis (F (base 770)) := by
      change W.basis (F (base 770)) = _
      simp [W, put, writeBit, Ne.symm n7c]
    have ta : tW.basis (base 721) = false := by
      change W.basis (F (base 721)) = _
      simp [W, put, writeBit, Ne.symm n7a, u721]
    have tp : tW.basis (base 1028) = false := by
      change W.basis (F (base 1028)) = _
      simp [W, put, writeBit, Ne.symm n7d, u1028]
    have t514 : tW.basis (base 514) = f := by
      change W.basis (F (base 514)) = _
      simp [W, put, writeBit]
    have gen : F (base 2400) = L.core.generic := E1QubitPlacement.pmap_g L hw hn
    have wrap : tW.basis (base 514) = true → tW.basis (base 2400) = true := by
      intro h
      rw [t514] at h
      rw [tg, gen]
      cases hg : u.basis L.core.generic
      · simp [hf, hg] at h
      · rfl
    have key := evenTail_eq k.val even tW m ta tp wrap
    rw [tg, tx] at key
    symm
    apply rename_eq2 F E1QubitPlacement.S inj _ _ (tailX_S k.val) (evenTail_S k.val) W
      (put W (F (base 721)) A) tW (put tW (base 721) A) m m rfl (fun q _ => rfl) rfl
    · intro q hq
      by_cases e : q = base 721
      · subst e; simp [put, writeBit]
      · have ne : F q ≠ F (base 721) := fun E => e (inj _ hq _ s721 E)
        simp only [put, writeBit, Function.update_apply, e, ne, if_false]
        rfl
    · exact key.symm
    · intro q hq
      have ne : q ≠ F (base 721) := fun e => hq (e ▸ Finset.mem_image_of_mem F s721)
      simp [put, writeBit, ne]

end

/-- The new program from `s'` tracks the old one from `s` under the padded measurement list. -/
structure Pad (P' P : Program) (s' s : State) (pad : List Bool → List Bool) : Prop where
  run_eq : ∀ d, run P' d s' = run P (pad d) s
  drop_eq : ∀ d, (pad d).drop (measurementCount P) = d.drop (measurementCount P')

theorem run_false (p : Program) (m : List Bool) (j : Nat) (s : State) :
    run p (m ++ List.replicate j false) s = run p m s := by
  induction p generalizing m j s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X t => simp only [run]; exact ih _ _ _
    | CX c t => simp only [run]; exact ih _ _ _
    | CCX a b t => simp only [run]; exact ih _ _ _
    | measureX t c₀ c₁ =>
      simp only [run]
      cases m with
      | nil =>
        cases j with
        | zero => rfl
        | succ j =>
          simp only [List.nil_append, List.replicate_succ, List.headD_cons, List.tail_cons,
            List.headD_nil, List.tail_nil]
          exact (ih [] j _)
      | cons b m =>
        simp only [List.cons_append, List.headD_cons, List.tail_cons]
        exact ih m j _

/-- Exactly `c` entries that act like `d` on a program with `c` measurements. -/
def pfx (c : Nat) (d : List Bool) : List Bool := (d ++ List.replicate c false).take c

theorem pfx_length (c : Nat) (d : List Bool) : (pfx c d).length = c := by
  simp [pfx]

theorem run_pfx (p : Program) (d : List Bool) (s : State) :
    run p (pfx (measurementCount p) d) s = run p d s := by
  rw [pfx, run_take, run_false]

theorem Pad.append {P' P : Program} {s' s : State} {pad : List Bool → List Bool}
    (h : Pad P' P s' s pad) (B : Program) : Pad (P' ++ B) (P ++ B) s' s pad := by
  constructor
  · intro d
    rw [run_append, run_take, run_append, run_take, h.drop_eq, h.run_eq]
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, h.drop_eq, List.drop_drop]

theorem Pad.prefix (A' A P' P : Program) (s' s : State) (pad : List Bool → List Bool)
    (hc : measurementCount A' = measurementCount A)
    (h : ∀ d, Pad P' P (run A' d s') (run A d s) pad) :
    Pad (A' ++ P') (A ++ P) s' s
      (fun d => pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))) := by
  have tk : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))).take
      (measurementCount A) = pfx (measurementCount A) d := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))).drop
      (measurementCount A) = pad (d.drop (measurementCount A)) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, run_append A, tk, dr, run_pfx, hc]
    exact (h d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h d).drop_eq, hc,
      List.drop_drop]

theorem Pad.prefix_general (A' A P' P : Program) (s' s : State) (pad : List Bool → List Bool)
    (h : ∀ d, Pad P' P (run A' d s') (run A d s) pad) :
    Pad (A' ++ P') (A ++ P) s' s
      (fun d => pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))) := by
  have tk : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))).take
      (measurementCount A) = pfx (measurementCount A) d := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))).drop
      (measurementCount A) = pad (d.drop (measurementCount A')) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, run_append A, tk, dr, run_pfx]
    exact (h d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h d).drop_eq, List.drop_drop]

/-- Renaming carries a padded run when the extra wire is fixed. -/
theorem Pad.rename (f : Wire → Wire) (inj : Function.Injective f) (pk : Wire) (hfix : f pk = pk)
    (P' P : Program) (hw : pk ∈ wires P') (t : State) (v : Bool) (pad : List Bool → List Bool)
    (h : Pad P' P (put (pullState f t) pk v) (pullState f t) pad) :
    Pad (renameProgram f P') (renameProgram f P) (put t pk v) t pad := by
  constructor
  · intro d
    apply rename_eq2 f (wires P' ∪ wires P) (fun a _ b _ e => inj e) P' P
      Finset.subset_union_left Finset.subset_union_right (put t pk v) t
      (put (pullState f t) pk v) (pullState f t) d (pad d) rfl ?_ rfl (fun _ _ => rfl) (h.run_eq d)
    · intro q hq
      have ne : q ≠ pk := by
        intro e; subst e
        exact hq (Finset.mem_image.mpr ⟨q, Finset.mem_union_left _ hw, hfix⟩)
      simp [put, writeBit, ne]
    · intro q _
      by_cases e : q = pk
      · subst e; simp [put, writeBit, hfix]
      · have ne : f q ≠ pk := fun E => e (inj (E.trans hfix.symm))
        simp only [put, writeBit, Function.update_apply, e, ne, if_false]
        rfl
  · intro d
    rw [(renameProgram_counts _ _).2, (renameProgram_counts _ _).2]
    exact h.drop_eq d

/-- The pool site that holds the comparison flag between the input stage and the X entry. -/
def pkW (L : ControlledPointLayout) : Wire := L.core.poolWire 724

def genericNew (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ((entryYAll L (-cy) ++ entryXNew L (pkW L) (-cx)) ++ ParityStageBothInverse23.restEntry L) ++
    ParityStageBothInverse23.secondStageAll L (ReflectionE1.correction cx) cy cx

theorem entryXNew_measure (L : ControlledPointLayout) (pk : Wire) (k : Fp) :
    measurementCount (entryXAll L k) =
      measurementCount (comparePart base (base 2400) k.val) + measurementCount (entryXNew L pk k) := by
  have o := (entryXAll_counts L k).2.1
  have e : measurementCount (E1QubitPlacement.entryM L k) =
      measurementCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val) := by
    unfold E1QubitPlacement.entryM
    exact (renameProgram_counts _ _).2
  rw [o, e, merged_split, measurementCount_append]
  unfold entryXNew
  have sw0 : ∀ a, measurementCount (swp pk a) = 0 := by intro a; simp [swp, measurementCount]
  split_ifs
  · rw [measurementCount_append, sw0, (renameProgram_counts _ _).2]; omega
  · rw [measurementCount_append, measurementCount_append, sw0, (renameProgram_counts _ _).2,
      (renameProgram_counts _ _).2, (evenTail_counts _).2.1]
    simp [measurementCount]

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
theorem pk_pool : pkW L ∈ L.dialogPool := Square5Placement.pool_member L hw 724 (by omega)

theorem pool_take (n i : Nat) (hn' : n ≤ 2613) (hi : n ≤ i) (hi2 : i < 2613) :
    L.core.poolWire i ∉ L.dialogPool.take n := by
  rw [pool_block L hw n hn']
  intro h
  obtain ⟨j, hj, e⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  have := pool_inj L hw hn j i (by omega) hi2 e
  omega

theorem pk_not_K : pkW L ∉ (L.recoveryConstant L.point.y).wires := by
  have hp := pk_pool L hw
  have not512 : pkW L ∉ L.dialogPool.take 512 := pool_take L hw hn 512 724 (by omega) (by omega) (by omega)
  have split : L.dialogPool.take 512 = L.dialogPool.take 256 ++ (L.dialogPool.drop 256).take 256 := by
    rw [show (512:Nat) = 256 + 256 from rfl, List.take_add]
  rw [split] at not512
  simp only [List.mem_append, not_or] at not512
  have ne (i : Nat) (hi : i < 2613) (hne : i ≠ 724) : pkW L ≠ L.core.poolWire i :=
    fun e => hne (pool_inj L hw hn i 724 hi (by omega) e.symm)
  intro h3
  change pkW L ∈ L.dialogPool.take 256 ++ L.point.y ++ (L.dialogPool.drop 256).take 256 ++
    [L.core.poolWire 512, L.core.poolWire 513, L.core.poolWire 514] at h3
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h3
  rcases h3 with ((e | e) | e) | e | e | e
  · exact not512.1 e
  · exact ((E1QubitPlacement.lay L hw hn _).2.1 hp).2 e
  · exact not512.2 e
  · exact ne 512 (by omega) (by omega) e
  · exact ne 513 (by omega) (by omega) e
  · exact ne 514 (by omega) (by omega) e

theorem pk_not_Y (k : Fp) (hg : pkW L ≠ L.core.generic) : pkW L ∉ wires (entryYAll L k) := by
  intro h
  have sub := (entryYAll_wires L hw k).trans (EntryFuse.fusedY_support L hw k)
  have h2 := Finset.mem_of_subset sub h
  rcases List.mem_cons.mp (List.mem_toFinset.mp h2) with e | e
  · exact hg e
  · exact pk_not_K L hw hn e

theorem pk_ne_flag : pkW L ≠ E1QubitPlacement.pmapR L (base 514) := by
  have e : E1QubitPlacement.pmapR L (base 514) = L.core.poolWire 514 := by
    unfold E1QubitPlacement.pmapR E1QubitPlacement.pmap
    rw [E1QubitPlacement.rho_base, E1QubitPlacement.sig_base]
    rfl
  rw [e]
  exact fun E => absurd (pool_inj L hw hn 724 514 (by omega) (by omega) E) (by omega)

theorem pk_ne_high : pkW L ≠ E1QubitPlacement.pmapR L (base 721) := by
  have e : E1QubitPlacement.pmapR L (base 721) = L.core.poolWire 723 := by
    unfold E1QubitPlacement.pmapR E1QubitPlacement.pmap
    rw [E1QubitPlacement.rho_base, E1QubitPlacement.sig_base]
    rfl
  rw [e]
  exact fun E => absurd (pool_inj L hw hn 724 723 (by omega) (by omega) E) (by omega)

theorem pk_ne_x : pkW L ≠ E1QubitPlacement.pmapR L (base 770) := by
  have hp := pk_pool L hw
  intro E
  apply ((E1QubitPlacement.lay L hw hn _).2.1 hp).1
  rw [E, ← E1QubitPlacement.pmap_x L hw hn]
  exact List.mem_map.mpr ⟨base 770, List.mem_map.mpr ⟨770, by simp [List.mem_range'_1], rfl⟩, rfl⟩

theorem generic_pad (cx cy X Y : Fp) (s : State)
    (hX : regValue L.point.x s.basis = X.val) (hY : regValue L.point.y s.basis = Y.val)
    (hc : regValue L.dialogPool s.basis = 0) (hg : pkW L ≠ L.core.generic) :
    Pad (genericNew L cx cy) (ParityStageBothInverse23.genericAll L cx cy)
      (put s (pkW L) (if s.basis L.core.generic then decide (prime ≤ X.val + (-cx).val) else false)) s
      (fun d => pfx (measurementCount (entryYAll L (-cy))) d ++
        (List.replicate (measurementCount (comparePart base (base 2400) (-cx).val)) false ++
          d.drop (measurementCount (entryYAll L (-cy))))) := by
  have inner := Pad.prefix (entryYAll L (-cy)) (entryYAll L (-cy)) (entryXNew L (pkW L) (-cx))
    (entryXAll L (-cx))
    (put s (pkW L) (if s.basis L.core.generic then decide (prime ≤ X.val + (-cx).val) else false)) s
    (fun d => List.replicate (measurementCount (comparePart base (base 2400) (-cx).val)) false ++ d) rfl (by
      intro d
      rw [run_put _ _ _ _ _ (pk_not_Y L hw hn _ hg)]
      have eY := entryYAll_eq L hw hn Y (-cy) s d hY hc
      have fy := EntryFuse.fusedY_correct L hw hn Y (-cy) s d hY hc
      rw [eY]
      generalize hu : run (EntryFuse.fusedY L (-cy)) d s = u at fy
      have tx : regValue L.point.x u.basis = X.val := by
        rw [regValue_congr _ _ s.basis (fun q hq => fy.2.2 q ((E1QubitPlacement.lay L hw hn q).1 hq)), hX]
      have tc : regValue L.dialogPool u.basis = 0 := by
        rw [regValue_congr _ _ s.basis (fun q hq => fy.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).2)), hc]
      have tg : u.basis L.core.generic = s.basis L.core.generic :=
        fy.2.2 _ ((E1QubitPlacement.lay L hw hn _).2.2 rfl).2
      rw [← tg]
      constructor
      · intro d'
        exact entryXNew_run L hw hn (pkW L) X (-cx) u tx tc (pk_pool L hw) (pk_ne_flag L hw hn)
          (pk_ne_high L hw hn) (pk_ne_x L hw hn)
          (by rw [E1QubitPlacement.pmap_g L hw hn]; exact hg) d'
      · intro d'
        rw [entryXNew_measure L (pkW L) (-cx), ← List.drop_drop, List.drop_left' (by simp)])
  exact (inner.append _).append _

end

end ECDSAAdd.Entrant.FlagEntry

namespace ECDSAAdd.Entrant.FlagTop
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out

attribute [local irreducible] layout

/-- The composite wire map of the generic block. -/
def rho (L : ControlledPointLayout) (q : Wire) : Wire :=
  swapD L (swapE L (tauM L (Wrapper5.U L (swapF L q))))

theorem ren_eq (L : ControlledPointLayout) (P : Program) :
    renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L)
      (renameProgram (Wrapper5.U L) (renameProgram (swapF L) P)))) = renameProgram (rho L) P := by
  simp only [renameProgram_comp]
  rfl

theorem rho_injective : Function.Injective (rho layout) := by
  have hw := layout_widths
  have hn := layout_nodup
  intro a b e
  exact swapF_injective layout hw hn ((Wrapper5.U layout).injective
    (tauM_injective layout hn (swapE_injective layout hw hn (swapD_injective layout hw hn e))))

theorem flags_nodup : layout.inPlaceFlags.Nodup := by
  have hD := layout.dialogUsed_nodup layout_nodup
  unfold ControlledPointLayout.dialogUsedWires at hD
  exact (List.nodup_append.mp (List.nodup_append.mp hD).1).2.1

theorem U_apply (q : Wire) : Wrapper5.U layout q =
    if q = layout.core.poolWire 684 then layout.core.poolWire 717
    else if q = layout.core.poolWire 717 then layout.core.poolWire 684 else q := by
  show (Equiv.swap _ _) q = _
  rw [Equiv.swap_apply_def]

theorem tauM_apply (q : Wire) : tauM layout q =
    if q = layout.core.generic then layout.genericSelect else
      if q = layout.genericSelect then layout.core.generic else q := rfl
theorem E_apply (q : Wire) : swapE layout q =
    if q = layout.core.equalNegY then spareWire layout
    else if q = spareWire layout then layout.core.equalNegY else q := rfl
theorem D_apply (q : Wire) : swapD layout q =
    if q = layout.doubleSelect then spareD layout
    else if q = spareD layout then layout.doubleSelect else q := rfl
theorem F_apply (q : Wire) : swapF layout q =
    if q = layout.point.finite then finSpare layout
    else if q = finSpare layout then layout.point.finite else q := rfl

/-- Off the wires the five swaps move, `rho` is the identity. -/
theorem rho_fix (q : Wire) (h1 : q ≠ layout.point.finite) (h2 : q ≠ finSpare layout)
    (h3 : q ≠ layout.core.poolWire 684) (h4 : q ≠ layout.core.poolWire 717)
    (h5 : q ≠ layout.core.generic) (h6 : q ≠ layout.genericSelect)
    (h7 : q ≠ layout.core.equalNegY) (h8 : q ≠ layout.doubleSelect) (h9 : q ≠ spareD layout) :
    rho layout q = q := by
  have h3' : q ≠ spareWire layout := h3
  unfold rho
  rw [F_apply, if_neg h1, if_neg h2, U_apply, if_neg h3, if_neg h4, tauM_apply, if_neg h5, if_neg h6,
    E_apply, if_neg h7, if_neg h3', D_apply, if_neg h8, if_neg h9]

theorem point_fix (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) : rho layout q = q := by
  have hw := layout_widths
  have flag (w : Wire) (hw' : w ∈ layout.inPlaceFlags) : q ≠ w := fun e => flags_not_point _ hw' (e ▸ hq)
  have pool (w : Wire) (hw' : w ∈ layout.dialogPool) : q ≠ w := fun e => pool_not_point _ hw' (e ▸ hq)
  apply rho_fix
  · exact fun e => finite_not_flag.2 (e ▸ hq)
  · exact pool _ (finSpare_pool layout hw)
  · exact pool _ (Square5Placement.pool_member layout hw 684 (by omega))
  · exact pool _ (Square5Placement.pool_member layout hw 717 (by omega))
  · exact flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact pool _ (spareD_pool layout hw)

theorem rho_generic : rho layout layout.core.generic = layout.genericSelect := by
  have hw := layout_widths
  have hn := layout_nodup
  have fn := flags_nodup
  simp only [ControlledPointLayout.inPlaceFlags, List.nodup_cons, List.mem_cons, not_or,
    List.not_mem_nil, or_false] at fn
  have gp (q : Wire) (hq : q ∈ layout.dialogPool) : layout.core.generic ≠ q :=
    fun e => pool_not_flag _ hq (e ▸ by simp [ControlledPointLayout.inPlaceFlags])
  have sp (q : Wire) (hq : q ∈ layout.dialogPool) : layout.genericSelect ≠ q :=
    fun e => pool_not_flag _ hq (e ▸ by simp [ControlledPointLayout.inPlaceFlags])
  unfold rho
  rw [F_apply, if_neg (Ne.symm (fin_ne_generic layout hn)),
    if_neg (gp _ (finSpare_pool layout hw)),
    U_apply, if_neg (gp _ (Square5Placement.pool_member layout hw 684 (by omega))),
    if_neg (gp _ (Square5Placement.pool_member layout hw 717 (by omega))),
    tauM_apply, if_pos rfl, E_apply, if_neg (by tauto), if_neg (sp _ (spare_pool layout hw)),
    D_apply, if_neg (by tauto), if_neg (sp _ (spareD_pool layout hw))]

/-- Pool sites pull back to the clean flags and pool sites. -/
theorem rho_pool (t : State) (hf : t.basis layout.point.finite = false)
    (hE : t.basis layout.core.equalNegY = false) (hD : t.basis layout.doubleSelect = false)
    (hclean : regValue layout.dialogPool t.basis = 0) (q : Wire) (hq : q ∈ layout.dialogPool) :
    t.basis (rho layout q) = false := by
  have hw := layout_widths
  have hn := layout_nodup
  have pc : ∀ a ∈ layout.dialogPool, t.basis a = false := fun a ha => (regValue_zero _ _).mp hclean a ha
  have fn := flags_nodup
  simp only [ControlledPointLayout.inPlaceFlags, List.nodup_cons, List.mem_cons, not_or,
    List.not_mem_nil, or_false] at fn
  have pf (a : Wire) (ha : a ∈ layout.dialogPool) (b : Wire) (hb : b ∈ layout.inPlaceFlags) : a ≠ b :=
    fun e => pool_not_flag a ha (e ▸ hb)
  have pfin (a : Wire) (ha : a ∈ layout.dialogPool) : a ≠ layout.point.finite :=
    fun e => (out_pool_off a ha).1 e
  have fl (b : Wire) (hb : b ∈ layout.inPlaceFlags) : layout.point.finite ≠ b :=
    fun e => finite_not_flag.1 (e ▸ hb)
  have mE : layout.core.equalNegY ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have mD : layout.doubleSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have mG : layout.core.generic ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have mS : layout.genericSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have s1 := finSpare_pool layout hw
  have s2 := Square5Placement.pool_member layout hw 684 (by omega)
  have s3 := Square5Placement.pool_member layout hw 717 (by omega)
  have s4 := spareD_pool layout hw
  have s5 := spare_pool layout hw
  -- the last three swaps on a pool site
  have last (a : Wire) (ha : a ∈ layout.dialogPool) :
      t.basis (swapD layout (swapE layout (tauM layout a))) = false := by
    rw [tauM_apply, if_neg (pf a ha _ mG), if_neg (pf a ha _ mS), E_apply, if_neg (pf a ha _ mE)]
    by_cases e1 : a = spareWire layout
    · rw [if_pos e1, D_apply, if_neg (by tauto), if_neg (Ne.symm (pf _ s4 _ mE))]
      exact hE
    · rw [if_neg e1, D_apply, if_neg (pf a ha _ mD)]
      by_cases e2 : a = spareD layout
      · rw [if_pos e2]; exact hD
      · rw [if_neg e2]; exact pc a ha
  unfold rho
  rw [F_apply, if_neg (pfin q hq)]
  by_cases e0 : q = finSpare layout
  · rw [if_pos e0, U_apply, if_neg (fun e => pfin _ s2 e.symm), if_neg (fun e => pfin _ s3 e.symm),
      tauM_apply, if_neg (fl _ mG), if_neg (fl _ mS), E_apply, if_neg (fl _ mE),
      if_neg (fun e => pfin _ s5 e.symm), D_apply, if_neg (fl _ mD), if_neg (fun e => pfin _ s4 e.symm)]
    exact hf
  · rw [if_neg e0]
    have ua : Wrapper5.U layout q ∈ layout.dialogPool := by
      rw [U_apply]
      split_ifs
      · exact s3
      · exact s2
      · exact hq
    exact last _ ua

theorem pk_ne_pool (i : Nat) (hi : i < 2613) (hne : i ≠ 724) : pkW layout ≠ layout.core.poolWire i :=
  fun e => hne (pool_inj layout layout_widths layout_nodup i 724 hi (by omega) e.symm)

theorem pk_flag (b : Wire) (hb : b ∈ layout.inPlaceFlags) : pkW layout ≠ b :=
  fun e => pool_not_flag _ (pk_pool layout layout_widths) (e ▸ hb)

theorem rho_pk : rho layout (pkW layout) = pkW layout := by
  apply rho_fix
  · exact (out_pool_off _ (pk_pool layout layout_widths)).1
  · exact pk_ne_pool 1400 (by omega) (by omega)
  · exact pk_ne_pool 684 (by omega) (by omega)
  · exact pk_ne_pool 717 (by omega) (by omega)
  · exact pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact pk_ne_pool 1540 (by omega) (by omega)

/-- Everything `genericNew` needs of the pulled state. -/
theorem pulled_values (t : State) (X Y : Fp) (G : Bool)
    (hx : regValue layout.point.x t.basis = X.val) (hy : regValue layout.point.y t.basis = Y.val)
    (hf : t.basis layout.point.finite = false) (hg : t.basis layout.genericSelect = G)
    (hE : t.basis layout.core.equalNegY = false) (hD : t.basis layout.doubleSelect = false)
    (hclean : regValue layout.dialogPool t.basis = 0) :
    regValue layout.point.x (pullState (rho layout) t).basis = X.val ∧
    regValue layout.point.y (pullState (rho layout) t).basis = Y.val ∧
    (pullState (rho layout) t).basis layout.core.generic = G ∧
    regValue layout.dialogPool (pullState (rho layout) t).basis = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hx]; apply regValue_congr; intro q hq
    change t.basis (rho layout q) = _
    rw [point_fix q (List.mem_append_left _ hq)]
  · rw [← hy]; apply regValue_congr; intro q hq
    change t.basis (rho layout q) = _
    rw [point_fix q (List.mem_append_right _ hq)]
  · change t.basis (rho layout _) = _
    rw [rho_generic, hg]
  · apply (regValue_zero _ _).mpr
    intro q hq
    exact rho_pool t hf hE hD hclean q hq

end ECDSAAdd.Entrant.FlagTop

end

section
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FlagTop
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out ZeroFill ParityEven
  ParityUniform E1Merge NativeFirstDirect MappedCompressed ParityXEntry

attribute [local irreducible] layout

/-- The input stage with the comparison flag extracted into `pk`. -/
def stageNew (L : ControlledPointLayout) (C : Point) (pk : Wire) : Program :=
  FiniteFlagInterval.zrep L ++
  classifierFast_research (triOf C) (yBit (dialogExceptionPoint C)) L.point.x (L.dialogPool.take 253)
    (yLow L) L.control L.point.finite L.genericSelect
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0)
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0) L.point.finite pk

theorem stageNew_run [DecidableEq Point] (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary L R b (fun _ => false) s.basis)
    (pk : Wire) (hpP : pk ∈ L.dialogPool) (hpW : pk ∉ L.dialogPool.take 253)
    (h3 : pk ≠ L.dialogPool.getD 253 0) (h4 : pk ≠ L.dialogPool.getD 254 0)
    (h5 : pk ≠ L.dialogPool.getD 255 0) (h6 : pk ≠ L.point.finite) (h7 : pk ≠ L.genericSelect)
    (h8 : pk ∉ L.point.x) :
    run (stageNew L (.some hc) pk) m s =
      put (run (stage L (.some hc)) m s) pk
        ((run (stage L (.some hc)) m s).basis L.genericSelect &&
          decide ((triOf (.some hc)).A < codeX R)) := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, hext, hextx⟩ := stage_layout L hw hn
  have hp := (point_holds _ _ _).mp hs.point
  have v := triOf_valid hc
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  have hpl := dialogPool_length L hw
  have Z := FiniteFlagInterval.zrep_run L hw hn s m
  unfold stageNew stage
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize hs1 : run (FiniteFlagInterval.zrep L) m s = s1 at Z ⊢
  have fx : L.point.finite ∉ L.point.x := (hextx _ (by simp)).1
  have gx : L.genericSelect ∉ L.point.x := (hextx _ (by simp)).1
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
  have s1p : ∀ q, q ∈ L.dialogPool → q ∉ L.point.x → s1.basis q = false := by
    intro q hq hx; rw [Z.2.1 _ hx]; exact (regValue_zero _ _).mp hs.clean q hq
  have pget (i : Nat) (hi : i < 2613) : L.dialogPool.getD i 0 ∈ L.dialogPool := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hz : (∀ q ∈ L.dialogPool.take 253, s1.basis q = false) ∧
      s1.basis (L.dialogPool.getD 253 0) = false ∧ s1.basis (L.dialogPool.getD 254 0) = false ∧
      s1.basis (L.dialogPool.getD 255 0) = false :=
    ⟨fun q hq => s1p q (List.mem_of_mem_take hq) (hdisj q hq),
      s1p _ (pget 253 (by omega)) (hextx _ (by simp)).1,
      s1p _ (pget 254 (by omega)) (hextx _ (by simp)).1,
      s1p _ (pget 255 (by omega)) (hextx _ (by simp)).1⟩
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
  have hx256 : codeX R < 2^256 := by
    unfold codeX
    split_ifs
    · exact pairCode_lt R
    · exact lt_trans FiniteFlagInterval.sentinel_lt (by norm_num [p])
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true, and_self] at hext
  obtain ⟨-, -, ⟨f1, f2, f3, f4⟩, ⟨g2, g3, g4⟩, ⟨a1, a2⟩, a3⟩ := hext
  have htmp : [L.dialogPool.getD 253 0, L.dialogPool.getD 254 0, L.dialogPool.getD 255 0,
      L.point.finite, pk].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true, and_self]
    exact ⟨⟨a1, a2, Ne.symm f2, Ne.symm h3⟩, ⟨a3, Ne.symm f3, Ne.symm h4⟩, ⟨Ne.symm f4, Ne.symm h5⟩,
      Ne.symm h6⟩
  have htx : ∀ q ∈ [L.dialogPool.getD 253 0, L.dialogPool.getD 254 0, L.dialogPool.getD 255 0,
      L.point.finite, pk], q ∉ L.point.x ∧ q ∉ L.dialogPool.take 253 ∧ q ≠ L.genericSelect := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, Ne.symm g2⟩
    · exact ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, Ne.symm g3⟩
    · exact ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, Ne.symm g4⟩
    · exact ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, f1⟩
    · exact ⟨h8, hpW, h7⟩
  have hto : ∀ q ∈ [L.dialogPool.getD 253 0, L.dialogPool.getD 254 0, L.dialogPool.getD 255 0,
      L.point.finite, pk], q ≠ L.point.finite → s1.basis q = false := by
    intro q hq hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hz.2.1
    · exact hz.2.2.1
    · exact hz.2.2.2
    · exact absurd rfl hne
    · exact s1p _ hpP h8
  exact classifierFast_run_research (triOf (.some hc)) v _ L.point.x (L.dialogPool.take 253) (yLow L) L.control
    L.point.finite L.genericSelect _ _ _ _ _ _ _ pk hxn hxl hwl hwn hdisj
    (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
        and_true, not_false_eq_true, and_self]
      have e := (stage_layout L hw hn).2.2.2.2.2.1
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
        and_true, not_false_eq_true, and_self] at e
      exact e)
    hextx htmp htx s1 _ s1g hz hf' hto (codeX R) hx256 xbit

/-- The comparison flag of the X entry, in the classifier's terms. -/
theorem flag_eq [DecidableEq Point] {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (R : Point) (X : Fp) (hX : X.val = codeX R) :
    (dialogOrdinary b R (.some hc) && decide ((triOf (.some hc)).A < codeX R)) =
      (if dialogOrdinary b R (.some hc) then
        decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false) := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have hxv : codeX (.some hr : Point) = x.val := rfl
      have hA : (triOf (.some hc)).A = cx.val := rfl
      have ne : x.val ≠ cx.val := fun e => den.1 (ZMod.val_injective _ e)
      have c0 : cx ≠ 0 := curve_x_ne_zero hc
      have nv : (-cx).val = p - cx.val := by
        rw [ZMod.neg_val, if_neg c0]
      have clt : cx.val < p := cx.isLt
      rw [hG, if_pos rfl, Bool.true_and, hxv, hA, hX, hxv, nv, EntryFuse.prime_eq_secp]
      apply decide_eq_decide.mpr
      omega
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp

theorem stageNew_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (pk : Wire) :
    toffoliCount (stageNew layout (.some hc) pk) ≤ 259 ∧
    measurementCount (stageNew layout (.some hc) pk) = 259 ∧
    Challenge.gateSlots (stageNew layout (.some hc) pk) ≤ 3619 + 1035 := by
  have c := classifierFast_researchast_counts_research (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
    layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
    layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) layout.point.finite pk (by simp [dialogPool_length layout layout_widths])
  have z := FiniteFlagInterval.zrep_counts layout
  have zs := FiniteFlagInterval.zrep_slots layout layout_widths
  unfold stageNew
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append, z.1, z.2]
  have c1 := c.1
  have c2 := c.2.1
  have c3 := c.2.2
  refine ⟨by omega, by omega, by omega⟩

def finiteNew (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  stageNew L C (pkW L) ++ renameProgram (rho L) (genericNew L cx cy) ++ OutputOpt.outStage L C

def wrapperNew (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteNew L C cx cy)

theorem pk_wires (cx cy : Fp) : pkW layout ∈ wires (genericNew layout cx cy) := by
  have h : pkW layout ∈ wires (entryXNew layout (pkW layout) (-cx)) := by
    unfold entryXNew
    split_ifs
    · rw [wires_append]
      exact Finset.mem_union_left _ (by simp [swp, wires, Instr.wires])
    · rw [wires_append, wires_append]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (by simp [swp, wires, Instr.wires]))
  unfold genericNew
  simp only [wires_append, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr h))

theorem pk_stage :
    pkW layout ∈ layout.dialogPool ∧ pkW layout ∉ layout.dialogPool.take 253 ∧
    pkW layout ≠ layout.dialogPool.getD 253 0 ∧ pkW layout ≠ layout.dialogPool.getD 254 0 ∧
    pkW layout ≠ layout.dialogPool.getD 255 0 ∧ pkW layout ≠ layout.point.finite ∧
    pkW layout ≠ layout.genericSelect ∧ pkW layout ∉ layout.point.x := by
  have hw := layout_widths
  have hn := layout_nodup
  have hp := pk_pool layout hw
  have n256 : pkW layout ∉ layout.dialogPool.take 256 :=
    pool_take layout hw hn 256 724 (by omega) (by omega) (by omega)
  have ne (i : Nat) (hi : i < 256) : pkW layout ≠ layout.dialogPool.getD i 0 :=
    fun e => n256 (e ▸ pool_take_mem i hi)
  have tk : pkW layout ∉ layout.dialogPool.take 253 :=
    pool_take layout hw hn 253 724 (by omega) (by omega) (by omega)
  refine ⟨hp, tk, ne 253 (by omega), ne 254 (by omega), ne 255 (by omega),
    (out_pool_off _ hp).1, (out_pool_off _ hp).2.1, ?_⟩
  exact fun h => pool_not_point _ hp (List.mem_append_left _ h)

open Classical in
theorem finite_pad {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    ∃ pad, Pad (finiteNew layout (.some hc) cx cy) (finiteProgramOpt layout (.some hc) cx cy) s s pad := by
  have hgen : pkW layout ≠ layout.core.generic :=
    pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  have key : ∀ d, Pad (renameProgram (rho layout) (genericNew layout cx cy))
      (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (genBlockOpt layout cx cy))))
      (run (stageNew layout (.some hc) (pkW layout)) d s) (run (stage layout (.some hc)) d s)
      (fun d => pfx (measurementCount (entryYAll layout (-cy))) d ++
        (List.replicate (measurementCount (comparePart base (base 2400) (-cx).val)) false ++
          d.drop (measurementCount (entryYAll layout (-cy))))) := by
    intro d
    obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s d hs
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := pk_stage
    rw [stageNew_run layout layout_widths layout_nodup hc b R s d hs (pkW layout) p1 p2 p3 p4 p5 p6 p7 p8]
    have hp := (point_holds _ _ _).mp hs.point
    generalize ht1 : run (stage layout (.some hc)) d s = t1 at m1 m2 m3 m4 m5 ⊢
    have gsx := gsel_off
    have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
        (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
    have t1y : regValue layout.point.y t1.basis = pointY R := by
      rw [← hp.2.2]; apply regValue_congr; intro q hq
      exact m5 q (y_not_x layout layout_nodup q hq)
        (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
    have hE : t1.basis layout.core.equalNegY = false := by
      obtain ⟨a, b', c, d'⟩ := out_off layout.core.equalNegY (by simp)
      rw [t1off _ a b' c d']; exact hs.flags _ (by simp [flags_list])
    have hD : t1.basis layout.doubleSelect = false := by
      obtain ⟨a, b', c, d'⟩ := out_off layout.doubleSelect (by simp)
      rw [t1off _ a b' c d']; exact hs.flags _ (by simp [flags_list])
    have hclean : regValue layout.dialogPool t1.basis = 0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
      rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
        (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
      exact (regValue_zero _ _).mp hs.clean q hq
    obtain ⟨X, Y, hXv, hYv⟩ : ∃ X Y : Fp, X.val = codeX R ∧ Y.val = pointY R := by
      cases R with
      | zero => exact ⟨(FiniteFlagInterval.sentinel : Fp), 0, FiniteFlagInterval.sentinel_val, rfl⟩
      | @some x y hr => exact ⟨x, y, rfl, rfl⟩
    rw [m4, flag_eq hc b R X hXv]
    unfold genBlockOpt
    rw [ren_eq]
    apply Pad.rename (rho layout) rho_injective (pkW layout) rho_pk _ _ (pk_wires cx cy)
    have pvv := pulled_values t1 X Y (dialogOrdinary b R (.some hc)) (m2.trans hXv.symm)
      (t1y.trans hYv.symm) m3 m4 hE hD hclean
    have gp := generic_pad layout layout_widths layout_nodup cx cy X Y _ pvv.1 pvv.2.1 pvv.2.2.2 hgen
    rw [pvv.2.2.1] at gp
    exact gp
  have h := Pad.prefix_general _ _ _ _ s s _ key
  exact ⟨_, h.append (OutputOpt.outStage layout (.some hc))⟩

open Classical in
theorem finite_run_new {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteNew layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteNew layout (.some hc) cx cy) m s).basis := by
  obtain ⟨pad, h⟩ := finite_pad hc b R s hs
  rw [h.run_eq m]
  exact finite_run hc b R s (pad m) hs

open Classical in
theorem wrapper_spec_new {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapperNew layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite_run_new hc b R s m hs
  unfold wrapperNew
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h

theorem pk_eq (L : ControlledPointLayout) : pkW L = E1QubitPlacement.pmapR L (base 722) := by
  unfold E1QubitPlacement.pmapR E1QubitPlacement.pmap
  rw [E1QubitPlacement.rho_base, E1QubitPlacement.sig_base]
  rfl

theorem tailX_flags (k : Nat) : base 514 ∈ wires (tailX base (base 2400) k) ∧
    base 722 ∈ wires (tailX base (base 2400) k) := by
  simp only [tailX, prodPart, wires_append, Finset.mem_union]
  simp [wires, Instr.wires]

theorem evenTail_flags (k : Nat) : base 514 ∈ wires (evenTail k) ∧ base 722 ∈ wires (evenTail k) := by
  simp only [evenTail, wires_append, Finset.mem_union]
  simp [wires, Instr.wires]

theorem entryXNew_wires (L : ControlledPointLayout) (k : Fp) :
    wires (entryXNew L (pkW L) k) ⊆ wires (entryXAll L k) := by
  set F := E1QubitPlacement.pmapR L with hF
  have img : ∀ a, a ∈ wires (mergedAll k.val) → F a ∈ wires (entryXAll L k) := by
    intro a ha
    unfold entryXAll
    rw [renameProgram_support]
    exact Finset.mem_image_of_mem _ ha
  have sub : ∀ P : Program, wires P ⊆ wires (mergedAll k.val) →
      wires (renameProgram F P) ⊆ wires (entryXAll L k) := by
    intro P hP q hq
    rw [renameProgram_support] at hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact img a (hP ha)
  have swW : ∀ a b : Wire, a ∈ wires (entryXAll L k) → b ∈ wires (entryXAll L k) →
      wires (swp a b) ⊆ wires (entryXAll L k) := by
    intro a b ha hb
    simp [swp, wires, Instr.wires, Finset.insert_subset_iff, ha, hb]
  unfold entryXNew
  split_ifs with he
  · have inc : wires (tailX base (base 2400) k.val) ⊆ wires (mergedAll k.val) := by
      unfold mergedAll mergedOdd
      rw [if_pos he, if_pos he, wires_append]
      exact Finset.subset_union_right
    have f := tailX_flags k.val
    rw [wires_append]
    refine Finset.union_subset (swW _ _ ?_ (img _ (inc f.1))) (sub _ inc)
    rw [pk_eq L]
    exact img _ (inc f.2)
  · have inc : wires (evenTail k.val) ⊆ wires (mergedAll k.val) := by
      unfold mergedAll
      rw [if_neg he]
      unfold mergedEven
      rw [wires_append]
      exact Finset.subset_union_right
    have inc0 : wires [Instr.CCX (base 2400) (base 770) (base 721)] ⊆ wires (mergedAll k.val) := by
      unfold mergedAll
      rw [if_neg he]
      unfold mergedEven
      rw [wires_append, wires_append]
      exact Finset.subset_union_left.trans Finset.subset_union_left
    have f := evenTail_flags k.val
    rw [wires_append, wires_append]
    refine Finset.union_subset (sub _ inc0) (Finset.union_subset (swW _ _ ?_ (img _ (inc f.1))) (sub _ inc))
    rw [pk_eq L]
    exact img _ (inc f.2)

theorem genericNew_wires (L : ControlledPointLayout) (cx cy : Fp) :
    wires (genericNew L cx cy) ⊆ wires (ParityStageBothInverse23.genericAll L cx cy) := by
  simp only [genericNew, ParityStageBothInverse23.genericAll, ParityStageBothInverse23.entryStageAll,
    wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _) (entryXNew_wires L (-cx))) (Finset.Subset.refl _))
    (Finset.Subset.refl _)

theorem entryXNew_toffoli (L : ControlledPointLayout) (pk : Wire) (k : Fp) :
    toffoliCount (entryXNew L pk k) + 255 = toffoliCount (entryXAll L k) := by
  have o := (entryXAll_counts L k).1
  have e : toffoliCount (E1QubitPlacement.entryM L k) =
      toffoliCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val) := by
    unfold E1QubitPlacement.entryM
    exact (renameProgram_counts _ _).1
  have cp : toffoliCount (comparePart base (base 2400) k.val) = 256 := by
    have c := (compareLt_counts none (srcR base) (xR base) (cR base) (base 513) (base 514)
      (by simp [srcR, xR, wireBlock_length]) (by simp [cR, xR, wireBlock_length])).1
    have lx : (xR base).length = 256 := by simp [xR, wireBlock_length]
    rw [lx] at c
    simp only [comparePart, toffoliCount_append, (maskedConstant_counts _ _ _).1,
      (notRegister_counts _).1, c]
    rfl
  rw [e, merged_split, toffoliCount_append, cp] at o
  have sw0 : toffoliCount (swp pk (E1QubitPlacement.pmapR L (base 514))) = 0 := by
    simp [swp, toffoliCount]
  unfold entryXNew
  split_ifs
  · rw [toffoliCount_append, sw0, (renameProgram_counts _ _).1]; omega
  · rw [toffoliCount_append, toffoliCount_append, sw0, (renameProgram_counts _ _).1,
      (renameProgram_counts _ _).1]
    have t := (evenTail_counts k.val).1
    have c1 : toffoliCount [Instr.CCX (base 2400) (base 770) (base 721)] = 1 := by simp [toffoliCount]
    omega

theorem entryXNew_slots (L : ControlledPointLayout) (pk : Wire) (k : Fp) :
    Challenge.gateSlots (entryXNew L pk k) ≤ Challenge.gateSlots (entryXAll L k) + 2 := by
  have sw2 : Challenge.gateSlots (swp pk (E1QubitPlacement.pmapR L (base 514))) = 2 := by
    simp [swp, Challenge.gateSlots, Challenge.instructionSlots]
  have eo : Challenge.gateSlots (entryXAll L k) = Challenge.gateSlots (mergedAll k.val) := by
    unfold entryXAll
    exact rename_gateSlots _ _
  rw [eo]
  unfold entryXNew mergedAll
  split_ifs with he
  · unfold mergedOdd
    rw [if_pos he, Challenge.gateSlots_append, Challenge.gateSlots_append, sw2, rename_gateSlots]
    omega
  · unfold mergedEven
    rw [Challenge.gateSlots_append, Challenge.gateSlots_append, Challenge.gateSlots_append,
      Challenge.gateSlots_append, sw2, rename_gateSlots, rename_gateSlots]
    omega

theorem entryXNew_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (pk : Wire) (k : Fp) (h514 : pk ≠ E1QubitPlacement.pmapR L (base 514)) :
    GatePhysical (entryXNew L pk k) := by
  have inj := E1QubitPlacement.pmap_inj L hw hn
  have old := E1AffineEndpoints52Research.Forward.merged_physical base (base 2400)
    base_pool_nodup E1QubitPlacement.g2400 k.val
  rw [merged_split, gatePhysical_append] at old
  have tP := old.2
  have swP : GatePhysical (swp pk (E1QubitPlacement.pmapR L (base 514))) := by
    simp [swp, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, h514, Ne.symm h514]
  have lift : ∀ P : Program, wires P ⊆ E1QubitPlacement.S → GatePhysical P →
      GatePhysical (renameProgram (E1QubitPlacement.pmapR L) P) := by
    intro P hP hp
    exact gatePhysical_rename_support _ P (fun a ha b hb e => inj a (hP ha) b (hP hb) e) hp
  have ctl := (tail_control_wires k.val).trans (tailX_S k.val)
  unfold entryXNew
  split_ifs
  · rw [gatePhysical_append]
    exact ⟨swP, lift _ (tailX_S k.val) tP⟩
  · simp only [gatePhysical_append]
    refine ⟨lift _ ?_ ?_, swP, lift _ (evenTail_S k.val) (evenTail_physical k.val tP)⟩
    · simp only [wires, Instr.wires, Finset.union_empty]
      exact ctl
    · simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, base]

abbrev ioSet : Finset Wire := (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset

theorem finiteOpt_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (finiteProgramOpt layout (.some hc) cx cy) =
      wires (stage layout (.some hc)) ∪
        wires (renameProgram (rho layout) (ParityStageBothInverse23.genericAll layout cx cy)) ∪
        wires (OutputOpt.outStage layout (.some hc)) := by
  unfold finiteProgramOpt genBlockOpt
  rw [ren_eq, wires_append, wires_append]

/-- Every wire of the new input stage is an input wire or already in the old program. -/
theorem stageNew_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (stageNew layout (.some hc) (pkW layout)) ⊆
      ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
  have st := stage_support hc
  have mem := stage_wires_mem hc
  have hstage : wires (stage layout (.some hc)) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    intro q hq
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inl (Or.inl hq))
  have pkIn : pkW layout ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    refine Or.inr (Or.inl (Or.inr ?_))
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_of_subset (genericNew_wires layout cx cy) (pk_wires cx cy), rho_pk⟩
  have mx : ∀ q ∈ layout.point.x, q ∈ ioSet := by
    intro q hq
    simp [ioSet, PointAddLayout.pointWires, hq]
  have mf : layout.point.finite ∈ ioSet := by simp [ioSet, PointAddLayout.pointWires]
  have tk : ∀ q ∈ layout.dialogPool.take 253, q ∈ layout.dialogPool.take 256 := by
    intro q hq
    have hpl := dialogPool_length layout layout_widths
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hq
    simp only [List.length_take] at hi
    rw [List.getElem_take] at e
    rw [← e]
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  have pool256 : ∀ q ∈ layout.dialogPool.take 256,
      q ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) :=
    fun q hq => hstage (mem.1 q hq)
  have gsel : layout.genericSelect ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) :=
    hstage mem.2
  have hcl : wires (classifier (triOf (.some hc)) (yBit (dialogExceptionPoint (.some hc))) layout.point.x
      (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite layout.genericSelect
      (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)) ⊆
      ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    intro q hq
    apply hstage
    unfold stage
    rw [wires_append]
    exact Finset.mem_union_right _ hq
  have hz : wires (FiniteFlagInterval.zrep layout) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    intro q hq
    apply hstage
    unfold stage
    rw [wires_append]
    exact Finset.mem_union_left _ hq
  unfold stageNew
  rw [wires_append]
  refine Finset.union_subset hz ?_
  exact classifierFast_researchast_wires_research _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ layout_widths.inputX _ hcl
    (fun q hq => Finset.mem_union_left _ (mx q hq)) (fun q hq => pool256 q (tk q hq))
    (pool256 _ (pool_take_mem 253 (by omega))) (pool256 _ (pool_take_mem 254 (by omega)))
    (pool256 _ (pool_take_mem 255 (by omega))) (Finset.mem_union_left _ mf) pkIn gsel

theorem finiteNew_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (finiteNew layout (.some hc) cx cy) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
  have s := stageNew_wires (cx := cx) (cy := cy) hc
  unfold finiteNew
  rw [wires_append, wires_append]
  refine Finset.union_subset (Finset.union_subset s ?_) ?_
  · intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    refine Or.inr (Or.inl (Or.inr ?_))
    rw [renameProgram_support]
    exact Finset.mem_image_of_mem _ (Finset.mem_of_subset (genericNew_wires layout cx cy) ha)
  · intro q hq
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inr hq)

theorem wrapperNew_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperNew layout (.some hc) cx cy) ⊆ ioSet ∪ wires (wrapperOpt layout (.some hc) cx cy) := by
  have k := finiteNew_wires (cx := cx) (cy := cy) hc
  have hw := layout_widths
  have fixIO : ∀ q ∈ ioSet, Wrapper5.U layout q = q := by
    intro q hq
    have hq' := List.mem_toFinset.mp hq
    have np := io_not_pool q hq'
    have n1 : q ≠ layout.core.poolWire 684 := by
      intro e; apply np; rw [e]; exact Square5Placement.pool_member layout hw 684 (by omega)
    have n2 : q ≠ layout.core.poolWire 717 := by
      intro e; apply np; rw [e]; exact Square5Placement.pool_member layout hw 717 (by omega)
    rw [U_apply, if_neg n1, if_neg n2]
  unfold wrapperNew wrapperOpt
  rw [renameProgram_support, renameProgram_support]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (k ha) with h | h
  · rw [fixIO a h]; exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

theorem support_used_new {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperNew layout (.some hc) cx cy) ⊆ layout.dialogUsedWires.toFinset := by
  refine (wrapperNew_wires hc).trans (Finset.union_subset ?_ (support_used hc))
  intro q hq
  apply List.mem_toFinset.mpr
  unfold ControlledPointLayout.dialogUsedWires
  simp only [List.mem_append]
  have := List.mem_toFinset.mp hq
  simp only [List.mem_append] at this
  tauto

theorem stageNew_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (stageNew layout (.some hc) (pkW layout)) := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, hext, hextx⟩ := stage_layout layout layout_widths layout_nodup
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := pk_stage
  have old := classifier_physical (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
    layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
    layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) hxl hwl hxn hwn hdisj hext hextx
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true, and_self] at hext
  obtain ⟨-, -, ⟨f1, f2, f3, f4⟩, -, ⟨a1, a2⟩, a3⟩ := hext
  unfold stageNew
  rw [gatePhysical_append]
  refine ⟨FiniteFlagInterval.zrep_physical layout layout_nodup, ?_⟩
  exact classifierFast_researchast_physical_research _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hxl
    ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, Ne.symm a1⟩
    ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, Ne.symm a2⟩
    ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, f2⟩ a3 (Ne.symm f4) (Ne.symm p6) (Ne.symm p7) old

theorem wrapper_physical_new {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapperNew layout (.some hc) cx cy) := by
  have old : GatePhysical (ParityStageBothInverse23.genericRef layout cx cy) := by
    rw [reference_eq]
    exact Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p0 := ParityStageBothInverse23.generic_physical layout layout_widths layout_nodup cx cy old
  simp only [ParityStageBothInverse23.genericAll, ParityStageBothInverse23.entryStageAll,
    gatePhysical_append] at p0
  have g : GatePhysical (genericNew layout cx cy) := by
    simp only [genericNew, gatePhysical_append]
    exact ⟨⟨⟨p0.1.1.1, entryXNew_physical layout layout_widths layout_nodup _ _
      (pk_ne_flag layout layout_widths layout_nodup)⟩, p0.1.2⟩, p0.2⟩
  unfold wrapperNew
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteNew, gatePhysical_append]
  exact ⟨⟨stageNew_physical hc, gatePhysical_rename _ rho_injective _ g⟩, OutputOpt.outStage_physical hc⟩

theorem genericNew_counts (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (genericNew L cx cy) + 255 = toffoliCount (ParityStageBothInverse23.genericAll L cx cy) ∧
    measurementCount (genericNew L cx cy) ≤ measurementCount (ParityStageBothInverse23.genericAll L cx cy) ∧
    Challenge.gateSlots (genericNew L cx cy) ≤
      Challenge.gateSlots (ParityStageBothInverse23.genericAll L cx cy) + 2 := by
  have t := entryXNew_toffoli L (pkW L) (-cx)
  have m := entryXNew_measure L (pkW L) (-cx)
  have s := entryXNew_slots L (pkW L) (-cx)
  simp only [genericNew, ParityStageBothInverse23.genericAll, ParityStageBothInverse23.entryStageAll,
    toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
  omega

theorem wrapperNew_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperNew layout (.some hc) cx cy) + 252 ≤
      toffoliCount (wrapperOpt layout (.some hc) cx cy) ∧
    measurementCount (wrapperNew layout (.some hc) cx cy) ≤
      measurementCount (wrapperOpt layout (.some hc) cx cy) + 2 ∧
    Challenge.gateSlots (wrapperNew layout (.some hc) cx cy) ≤
      Challenge.gateSlots (wrapperOpt layout (.some hc) cx cy) + 4658 := by
  have g := genericNew_counts layout cx cy
  have s := stageNew_counts hc (pkW layout)
  have o := stage_counts hc
  simp only [wrapperNew, wrapperOpt, finiteNew, finiteProgramOpt, genBlockOpt,
    toffoliCount_append, measurementCount_append, Challenge.gateSlots_append,
    (renameProgram_counts _ _).1, (renameProgram_counts _ _).2, rename_gateSlots]
  omega

open Classical in
theorem full_spec_new {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperNew layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz:regValue layout.work s.basis=0:=hs.2
  have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
  have a:=wrapper_spec_new hc b R s m hi
  have old:=InputSentinel530.wrapper530_spec hc b R s m hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used_new hc) (InputSentinel530.support_used530 hc)
    s m _ b a.2 old.2 (a.1.trans old.1.symm)]
  exact InputSentinel530.full_spec530 hc b R s m hs

def programNew (C : Point) : Program :=
  match C with
  | .zero=>[]
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperNew layout C cx cy

def entryNew : Challenge.Entry := fun C=>normalizeProgram (programNew C)
def boundsNew : Challenge.Bounds := ⟨2150029,1498372,1587,50255906⟩

theorem program_correct_new (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programNew C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programNew,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec_new hc b R) (support_used_new hc)

theorem program_toffoli_new (C : Point) : toffoliCount (programNew C)≤2150029 := by
  cases C with
  | zero=>simp [programNew,toffoliCount]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_toffoli (.some hc)
    have delta:=(wrapperNew_metrics hc).1
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤_ at old
    change toffoliCount (wrapperNew layout (.some hc) cx cy)≤2150029
    omega

theorem program_measurements_new (C : Point) : measurementCount (programNew C)≤1498372 := by
  cases C with
  | zero=>simp [programNew,measurementCount]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_measurements (.some hc)
    have delta:=(wrapperNew_metrics hc).2.1
    change measurementCount (wrapperOpt layout (.some hc) cx cy)≤1498370 at old
    change measurementCount (wrapperNew layout (.some hc) cx cy)≤1498372
    omega

theorem program_qubits_new (C : Point) : qubits (programNew C)≤1587 := by
  cases C with
  | zero=>change qubits []≤1587;rw [qubits_empty];decide
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_qubits (.some hc)
    change qubits (wrapperOpt layout (.some hc) cx cy)≤1587 at old
    change qubits (wrapperNew layout (.some hc) cx cy)≤1587
    apply le_trans (Finset.card_le_card ?_) old
    intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact Finset.mem_union_left _ h
    · rcases Finset.mem_union.mp (wrapperNew_wires hc h) with e | e
      · exact Finset.mem_union_left _ (io_mem q (List.mem_toFinset.mp e))
      · exact Finset.mem_union_right _ e

theorem program_physical_new (C : Point) : GatePhysical (programNew C) := by
  cases C with
  | zero=>simp [programNew,GatePhysical]
  | @some cx cy hc=>exact wrapper_physical_new hc

theorem program_slots_new (C : Point) : Challenge.gateSlots (programNew C)≤50255906 := by
  cases C with
  | zero=>simp [programNew]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_slots (.some hc)
    have delta:=(wrapperNew_metrics hc).2.2
    change Challenge.gateSlots (wrapperOpt layout (.some hc) cx cy)≤50251248 at old
    change Challenge.gateSlots (wrapperNew layout (.some hc) cx cy)≤50255906
    omega

theorem certificateNew : Challenge.Certificate entryNew boundsNew where
  correct C b R:=(normalize_triple _ _ _).mpr (program_correct_new C b R)
  physical C:=normalize_physical _ (by simpa only [GatePhysical] using program_physical_new C)
  toffoli_le C:=(normalize_toffoli _).trans (program_toffoli_new C)
  measurements_le C:=by
    change measurementCount (normalizeProgram (programNew C))≤1498372
    rw [normalize_measurements];exact program_measurements_new C
  qubits_le C:=by
    change qubits (normalizeProgram (programNew C))≤1587
    rw [normalize_qubits];exact program_qubits_new C
  gateSlots_le C:=by
    change Challenge.gateSlots (normalizeProgram (programNew C))≤50255906
    rw [normalize_slots];exact program_slots_new C

end ECDSAAdd.Entrant.FlagTop

end

section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
section
namespace ECDSAAdd.Entrant.ParityXExit
open Arithmetic Challenge RecordedQuantum NativeFirstDirect MappedCompressed E1Merge ExitMerge ParityCarry ParityConvert ParityEven
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The X exit up to the flag erase, the same for both parities of `k`. -/
def prefixAll (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  ExitMerge.fPart w g k++ExitMerge.eraseH w++ExitMerge.addPart w g k++
    rotateLeft (kR w)++ExitMerge.parBack w g k

/-- The X exit with the flag parked instead of erased. -/
def programN (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  prefixAll w g k++ECDSAAdd.Entrant.FlagEntry.swp (w 514) (w 722)

theorem prefixAll_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hac : ∀q∈aC base,b0 q=false) (h1797 : b0 (base 1797)=false) :
    let G := b0 (base 2400)
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let Y := if G then (k+p-X)%p else X
    Triple (MF base b0 (2*H+(!par).toNat) K 0 par false false false) (prefixAll base (base 2400) k)
      (MF base b0 0 Y 0 false (G && decide (k<X)) false false) := by
  intro G par H K Y
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  obtain ⟨a1,a2,a3,a5,a6,a7,a8⟩ := archX k X hk hX G
  let f := G && decide (k<X)
  change H<2^256 at a1
  change (dInv par+H)%2^257=K%2^257 at a2
  change f=(decide (H<thrX k G par) ^^ G) at a3
  change ((if G then 2^258-1-K else K)+tkX k G f par)%2^258=Y/2 at a5
  change Y<p at a6
  change decide (Y%2=1)=(par ^^ (G && decide (k%2=1)) ^^ f) at a7
  have gm := g_mut base (base 2400) hn hg
  have hp' := p_val
  have hfg : f=true → G=true := by
    intro hf; simp only [f,Bool.and_eq_true] at hf; exact hf.1
  have hKlt : K<2^258 := Nat.mod_lt _ (by norm_num)
  have hpb : (!par).toNat<2 := Bool.toNat_lt _
  have s1 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par false false false (base 2400) (base 1028) 721 (by omega) G par
    (g_ne base hn (base 2400) hg 721 (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s1
  have s2 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K 0 hk par false (G && par) false hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,ltvX_eq] at s2
  have s3 := stepCmpH base hn b0 H (!par).toNat K (thrX k G par) par (G && par) false a1 hpb hac h1797
  have s4 := stepFlagCX base hn b0 (2*H+(!par).toNat) K (thrX k G par) par (decide (H<thrX k G par))
    (G && par) false (base 2400) G (g_ne base hn (base 2400) hg 514 (by omega)) (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm)
  rw [←a3] at s4
  have s5 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K (thrX k G par) hk par f (G && par) false hg
  rw [show b0 (base 2400)=G from rfl,ltvX_eq,Nat.xor_self] at s5
  have s6 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par f (G && par) false (base 514) (base 1028) 722 (by omega) f par
    (w_ne base hn _ _ (by omega) (by omega) (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s6
  have s7 := stepW0Back base hn b0 H K 0 par f (G && par) (f && par)
  have s8 := stepKnownH base hn b0 H K 0 par f (G && par) (f && par) (by omega) a2 hac h1797
  have s9 := stepCopyBack base hn b0 K 0 par f (G && par) (f && par)
  have s10 := stepNegK base (base 2400) hn b0 0 K 0 par f (G && par) (f && par) hKlt hg
  have s11 := stepLoadKX base (base 2400) hn b0 k 0 (if G then 2^258-1-K else K) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg] at s11
  have kWord : (tkX k G f par+(if G then 2^258-1-K else K))%2^258=Y/2 := by
    rw [Nat.add_comm]; exact a5
  have s12 := stepKAddZero4 base hn b0 (tkX k G f par) (if G then 2^258-1-K else K) 0 par f (G && par) (f && par)
    hac h1797 Y a6 kWord
  rw [kWord] at s12
  have s13 := stepLoadKX base (base 2400) hn b0 k (tkX k G f par) (Y/2) 0 par f (G && par) (f && par) hg
  rw [show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg,Nat.xor_self] at s13
  have s14 := stepMeasFp base hn b0 0 (Y/2) 0 par f (G && par)
  have s15 := stepMeasGp base (base 2400) hn b0 0 (Y/2) 0 par f false gm (g_ne base hn (base 2400) hg 721 (by omega))
  have s16 := stepRotL base hn b0 0 (Y/2) 0 par f false false (by rw [p_val] at a6; omega)
  have s17 := stepParBack base (base 2400) hn b0 k (Y/2) par f hg
  rw [show b0 (base 2400)=G from rfl,←a7,show 2*(Y/2)+(decide (Y%2=1)).toNat=Y by
    rcases Nat.mod_two_eq_zero_or_one Y with hy|hy <;> simp [hy] <;> omega] at s17
  have t:=s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq
    (s12.seq (s13.seq (s14.seq (s15.seq (s16.seq s17)))))))))))))))
  unfold prefixAll ExitMerge.fPart ExitMerge.eraseH ExitMerge.addPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

theorem MF_put_fp (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (b : BasisState) (H X T : Nat)
    (par f gp fp v : Bool) (s : State) (hs : MF w b H X T par f gp fp s.basis) :
    MF w b H X T par f gp v (put s (w 722) v).basis := by
  have h := stepBit w hn b H X T par f gp fp s (put s (w 722) v) 722 (by omega) hs
    (fun q hq => by simp [put,writeBit,hq])
  simpa [put,writeBit] using h

theorem MF_put_f (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (b : BasisState) (H X T : Nat)
    (par f gp fp v : Bool) (s : State) (hs : MF w b H X T par f gp fp s.basis) :
    MF w b H X T par v gp fp (put s (w 514) v).basis := by
  have h := stepBit w hn b H X T par f gp fp s (put s (w 514) v) 514 (by omega) hs
    (fun q hq => by simp [put,writeBit,hq])
  simpa [put,writeBit] using h

theorem swpStep (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (b0 : BasisState) (H X T : Nat)
    (par f : Bool) :
    Triple (MF w b0 H X T par f false false)
      (ECDSAAdd.Entrant.FlagEntry.swp (w 514) (w 722))
      (MF w b0 H X T par false false f) := by
  intro s m hs
  have ne : w 514≠w 722 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  rw [ECDSAAdd.Entrant.FlagEntry.swp_run _ _ ne s m hs.2.2.2.2.2.2.1]
  have h1 := MF_put_f w hn b0 H X T par f false false false s hs
  have h2 := MF_put_fp w hn b0 H X T par false false false (s.basis (w 514)) _ h1
  rw [hs.2.2.2.2.1] at h2 ⊢
  exact ⟨rfl,h2⟩

theorem programN_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hac : ∀q∈aC base,b0 q=false) (h1797 : b0 (base 1797)=false) :
    let G := b0 (base 2400)
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let Y := if G then (k+p-X)%p else X
    Triple (MF base b0 (2*H+(!par).toNat) K 0 par false false false) (programN base (base 2400) k)
      (MF base b0 0 Y 0 false false false (G && decide (k<X))) := by
  intro G par H K Y
  exact (prefixAll_triple k hk b0 X hX hac h1797).seq (swpStep base base_pool_nodup b0 0 Y 0 false _)

/-- The parked exit ends in the old exit's state plus the flag on `w 722`. -/
theorem programN_pw (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (initial field : State) (mF m m' : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed base) 0 X initial.basis)
    (ht : regValue (tR base) initial.basis=0) (h514 : initial.basis (base 514)=false)
    (h721 : initial.basis (base 721)=false) (h722 : initial.basis (base 722)=false)
    (hphase : field.phase=(run (NativeFirstDirect.forward base) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires base,
      field.basis q=(run (NativeFirstDirect.forward base) mF initial).basis q) :
    run (programN base (base 2400) k) m field =
      put (run (programAll base (base 2400) k) m' field) (base 722)
        (field.basis (base 2400) && decide (k<X)) := by
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec base hn X hX initial mF hin
  have e770 : initial.basis (base 770)=decide (X%2=1) := by
    have sp := kR_split base hn initial.basis
    have hb : regValue (kR base) initial.basis=X := hin.b
    rw [hb] at sp
    cases h : initial.basis (base 770) <;> simp [h] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  have inPool (a n : Nat) (ha : a+n≤1798) : ∀q∈wireBlock base a n,q∈skywalkPoolWires base :=
    blk_sub base a n 0 1798 (by omega) ha
  have wPool (i : Nat) (hi : i<1798) : base i∈skywalkPoolWires base :=
    List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  have keepI (i : Nat) (hi : i < 1798) (h1 : 257 ≤ i) (h2 : i < 770 ∨ 1028 < i) :
      field.basis (base i)=initial.basis (base i) := by
    rw [hpool _ (wPool i hi)]
    apply zrest
    simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
    exact ⟨⟨nb base hn i 0 257 hi (by omega) (by omega),nb base hn i 770 258 hi (by omega) (by omega)⟩,
      w_ne base hn i 1028 hi (by omega) (by omega)⟩
  have hR0 : regValue (hR base) field.basis=
      2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat := by
    rw [regValue_congr (hR base) field.basis _ (fun q hq => hpool q (inPool 0 258 (by omega) q hq))]
    exact zh
  have kR0 : regValue (kR base) field.basis=(X/2+kConstant false (decide (X%2=1)))%2^258 := by
    rw [regValue_congr (kR base) field.basis _ (fun q hq => hpool q (inPool 770 258 (by omega) q hq))]
    exact zk
  have tR0 : regValue (tR base) field.basis=0 := by
    rw [regValue_congr (tR base) field.basis initial.basis (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact keepI i (by omega) (by omega) (by omega))]
    exact ht
  have f1028 : field.basis (base 1028)=decide (X%2=1) := (hpool _ (wPool 1028 (by omega))).trans z1028
  have f514 : field.basis (base 514)=false := (keepI 514 (by omega) (by omega) (by omega)).trans h514
  have f721 : field.basis (base 721)=false := (keepI 721 (by omega) (by omega) (by omega)).trans h721
  have f722 : field.basis (base 722)=false := (keepI 722 (by omega) (by omega) (by omega)).trans h722
  have hac : ∀q∈aC base,field.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [keepI i (by omega) (by omega) (by omega)]
    exact (regValue_zero _ _).mp hin.carry _ hq
  have h1797 : field.basis (base 1797)=false := (keepI 1797 (by omega) (by omega) (by omega)).trans hin.cin
  have mf0 : MF base field.basis (2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat)
      ((X/2+kConstant false (decide (X%2=1)))%2^258) 0 (decide (X%2=1)) false false false field.basis :=
    ⟨hR0,kR0,tR0,f1028,f514,f721,f722,fun _ _ => rfl⟩
  obtain ⟨n1,n2⟩ := programN_triple k hk field.basis X hX hac h1797 field m mf0
  obtain ⟨o1,o2⟩ := programAll_triple k hk field.basis X hX hac h1797 field m' mf0
  have o4 := MF_put_fp base hn field.basis _ _ _ _ _ _ _ (field.basis (base 2400) && decide (k<X)) _ o2
  apply State.extensionality
  · exact n1.trans o1.symm
  · exact MF_unique base _ _ _ _ _ _ _ _ _ _ n2 o4

theorem fPart_g (w : Nat → Wire) (g : Wire) (k : Nat) : g ∈ wires (ExitMerge.fPart w g k) := by
  have h : g ∈ wires [Instr.CCX g (w 1028) (w 721)] := by simp [wires,Instr.wires]
  unfold ExitMerge.fPart
  simp only [wires_append,Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))

theorem fin_add {P M X Y G : Finset Wire} (m : M ⊆ (X ∪ Y) ∪ G) : P ∪ M ⊆ ((P ∪ X) ∪ Y) ∪ G := by
  intro q h
  have m' := @m q
  simp only [Finset.mem_union] at h m' ⊢
  tauto

theorem fin_pre {A B C D E K R G : Finset Wire} (a : C ⊆ K ∪ G) (z : G ⊆ A) :
    (((A ∪ B) ∪ C) ∪ D) ∪ E ⊆ ((((A ∪ B) ∪ K) ∪ D) ∪ E) ∪ R := by
  intro q h
  have a' := @a q
  have z' := @z q
  simp only [Finset.mem_union] at h a' ⊢
  tauto

theorem meas_sub (a b c d g : Wire) :
    wires [Instr.measureX a [] [Correction.CZ b c], Instr.measureX d [] [Correction.CZ g c]] ⊆
      (wires [Instr.measureX a [] [Correction.CZ b c]] ∪ wires [Instr.CX b d, Instr.measureX a [] []]) ∪ {g} := by
  intro q h
  simp [wires,Instr.wires,correctionWires] at h ⊢
  tauto

theorem addPart_sub (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (ExitMerge.addPart w g k) ⊆ wires (addPartKeep w g k) ∪ {g} := by
  simp only [ExitMerge.addPart,addPartKeep,wires_append]
  exact fin_add (meas_sub (w 722) (w 514) (w 1028) (w 721) g)

theorem prefix_sub (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (prefixAll w g k) ⊆ wires (programAll w g k) := by
  unfold programAll
  split_ifs with he
  · simp only [programOdd,prefixAll,wires_append]
    exact Finset.subset_union_left
  · simp only [prefixAll,programEven,wires_append]
    exact fin_pre (addPart_sub w g k) (Finset.singleton_subset_iff.mpr (fPart_g w g k))

theorem eraseF_toffoli (w : Nat → Wire) (g : Wire) (k : Nat) : toffoliCount (eraseF w g k) = 255 := by
  have e1 := eraseLtChain_counts (tR w) (xR w) (hC3 w) (w 1797) (w 514)
    (by simp [xR,tR,wireBlock_length]) (by simp [hC3,xR,wireBlock_length])
  have lx : (xR w).length=256 := by simp [xR,wireBlock_length]
  rw [lx] at e1
  simp only [eraseF,toffoliCount_append,(maskedConstant_counts _ _ _).1,(notRegister_counts _).1,e1.1]

theorem programN_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (programN w g k) + 254 = toffoliCount (programAll w g k) ∧
    measurementCount (programN w g k) ≤ measurementCount (programAll w g k) ∧
    gateSlots (programN w g k) ≤ gateSlots (programAll w g k) + 2 := by
  have sw1 : toffoliCount (ECDSAAdd.Entrant.FlagEntry.swp (w 514) (w 722)) = 0 := by
    simp [ECDSAAdd.Entrant.FlagEntry.swp,toffoliCount]
  have sw2 : measurementCount (ECDSAAdd.Entrant.FlagEntry.swp (w 514) (w 722)) = 0 := by
    simp [ECDSAAdd.Entrant.FlagEntry.swp,measurementCount]
  have sw3 : gateSlots (ECDSAAdd.Entrant.FlagEntry.swp (w 514) (w 722)) = 2 := by
    simp [ECDSAAdd.Entrant.FlagEntry.swp,gateSlots,instructionSlots]
  have f := eraseF_toffoli w g k
  have a := addPartKeep_counts w g k
  have o := eraseOdd_counts w g k
  have ev := eraseEven_counts w g k
  unfold programAll programN
  split_ifs
  · simp only [programOdd,prefixAll,toffoliCount_append,measurementCount_append,gateSlots_append,sw1,sw2,sw3]
    omega
  · simp only [programEven,prefixAll,toffoliCount_append,measurementCount_append,gateSlots_append,sw1,sw2,sw3]
    omega

theorem programN_physical (k : Nat) : GatePhysical (programN base (base 2400) k) := by
  have old:=ExitMerge.program_physical base (base 2400) base_pool_nodup E1QubitPlacement.g2400 k
  simp only [ExitMerge.program,gatePhysical_append] at old
  have hn := base_pool_nodup
  have ne : base 514≠base 722 := w_ne base hn _ _ (by omega) (by omega) (by omega)
  have sw : GatePhysical (ECDSAAdd.Entrant.FlagEntry.swp (base 514) (base 722)) := by
    simp [ECDSAAdd.Entrant.FlagEntry.swp,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ne,Ne.symm ne]
  simp only [programN,prefixAll,gatePhysical_append]
  exact ⟨old.1,sw⟩

end ECDSAAdd.Entrant.ParityXExit
end

section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ParityXExitInverse23Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Rolling1588Lifetime BalancedField
  ControlledPointLayout CompressedPointDialog ParityEven
attribute [local irreducible] run wires InverseFive23.stackReverse15 InverseFour15.stackReverse15 InverseFive23.lastPhase15

/-- The merged exit with the flag parked, placed like `x1`. -/
def x1N (k : Nat) : Program := renameProgram pi (ParityXExit.programN base (base 2400) k)

def lastXN (k : Nat) : Program :=
  skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true ++ x1N k

/-- Where the parked flag sits in the unhosted coordinates. -/
def pkP : Wire := base 724

theorem pi_722 : pi (base 722) = pkP := by
  rw [pi_base]; rfl

theorem x1N_pw (k : Nat) (hk : k < p) (x y : Nat) (hx : x < p) (s v : State) (mn r r' : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis)
    (hphase : v.phase=(run (FrontierEntry1591Native.forward base) mn s).phase)
    (hpool : ∀q∈skywalkPoolWires base,v.basis q=(run (FrontierEntry1591Native.forward base) mn s).basis q) :
    run (x1N k) r v = put (run (x1 k) r' v) pkP (v.basis (base 2400) && decide (k<x)) := by
  have fr := run_rename pi pi.injective (NativeFirstDirect.forward base) mn s
  rw [←forward_placed] at fr
  have sh : (i : Nat) → (hi : i < 2314) → (hdx : ¬(770 ≤ i ∧ i < 1026)) → (hdy : ¬(2056 ≤ i ∧ i < 2312)) →
      s.basis (base i)=false := by
    intro i hi hdx hdy
    apply input.2.2
    · exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
    · intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
      simp only [List.mem_range'_1] at hj
      have := base_injective e; omega
    · intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
      simp only [List.mem_range'_1] at hj
      have := base_injective e; omega
  have izero (i : Nat) (hi : i < 1798) (hx' : ¬(770 ≤ i ∧ i < 1026)) : (pullState pi s).basis (base i)=false := by
    rw [pull_basis,pi_base]
    have h1 := piN_lt i hi
    apply sh _ (by omega) _ (by omega)
    unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega
  have blk0 (a n : Nat) (h : a+n ≤ 1798) (hd : a+n ≤ 770 ∨ 1026 ≤ a) :
      regValue (wireBlock base a n) (pullState pi s).basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact izero i (by omega) (by omega)
  have hxr : regValue (wireBlock base 770 256) (pullState pi s).basis=x := by
    rw [regValue_congr _ _ s.basis (fun q hq => by
      rw [pull_basis,pi_kR q (E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) q hq)])]
    exact input.1
  have seed : LiteralSkywalkSeedValues (literalSkywalkPoolSeed base) 0 x (pullState pi s).basis := by
    refine ⟨blk0 0 258 (by omega) (by omega),?_,blk0 1540 257 (by omega) (by omega),
      izero 1797 (by omega) (by omega),izero 1028 (by omega) (by omega),izero 1797 (by omega) (by omega)⟩
    change regValue (E1Merge.kR base) (pullState pi s).basis=x
    rw [E1Merge.kR_x base base_pool_nodup,show E1Merge.xR base=wireBlock base 770 256 from rfl,hxr,
      blk0 1026 2 (by omega) (by omega)]
    simp
  have fpool : ∀q∈skywalkPoolWires base,
      (pullState pi v).basis q=(run (NativeFirstDirect.forward base) mn (pullState pi s)).basis q := by
    intro q hq
    rw [←fr,pull_basis,pull_basis]
    exact hpool _ (pi_pool q hq)
  have fphase : (pullState pi v).phase=(run (NativeFirstDirect.forward base) mn (pullState pi s)).phase := by
    rw [←fr,pull_phase,pull_phase]; exact hphase
  have pr := ParityXExit.programN_pw k hk x hx
    (pullState pi s) (pullState pi v) mn r r' seed (blk0 1029 256 (by omega) (by omega))
    (izero 514 (by omega) (by omega)) (izero 721 (by omega) (by omega)) (izero 722 (by omega) (by omega))
    fphase fpool
  have rrN := run_rename pi pi.injective (ParityXExit.programN base (base 2400) k) r v
  have rrO := run_rename pi pi.injective (ParityXExit.programAll base (base 2400) k) r' v
  rw [←rrN,←rrO,pull_basis,pi_fix 2400 (by omega)] at pr
  change pullState pi (run (x1N k) r v) = put (pullState pi (run (x1 k) r' v)) (base 722) _ at pr
  apply State.extensionality
  · have h0 := congrArg State.phase pr
    exact h0
  · funext q
    have h := congrFun (congrArg State.basis pr) (pi.symm q)
    rw [pull_basis,Equiv.apply_symm_apply] at h
    rw [h]
    by_cases e : q = pkP
    · subst e
      have e2 : pi.symm pkP = base 722 := by rw [←pi_722]; simp
      simp [put,writeBit,e2]
    · have e2 : pi.symm q ≠ base 722 := fun h' => e (by rw [←pi_722,←h']; simp)
      simp [put,writeBit,e,e2,pull_basis]

theorem rawN (F : Program) (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m : List Bool) (value : Nat) (input : SkywalkArithmeticInput base x y s.basis)
    (fieldResult : ∀mp mf,
      let beforeA := run (Rolling1588.firstPhase false) mp s
      let beforeB := run (Rolling1588.firstPhase true) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastXN k)) m s =
      put (run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s) pkP
        (s.basis (base 2400) && decide (k<x)) := by
  obtain ⟨mp,mf,mr,eqN,eqO⟩ : ∃ mp mf mr,
      run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastXN k)) m s=
        run (lastXN k) mr (run F mf (run (Rolling1588.firstPhase false) mp s)) ∧
      run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s=
        run (lastX k) mr (run F mf (run (Rolling1588.firstPhase false) mp s)) :=
    ⟨_,_,_,by rw [FrontierEntry1591Native.kernel,run_append,run_append],
      by rw [FrontierEntry1591Native.kernel,run_append,run_append]⟩
  obtain ⟨r1,r2,r3⟩ := fieldResult mp mf
  rw [eqN,eqO]
  generalize hAfter : run F mf (run (Rolling1588.firstPhase false) mp s)=after at r1 r2 r3 ⊢
  generalize hBefore : run (Rolling1588.firstPhase true) mp s=beforeB at r1 r2 r3
  rw [show lastXN k=(skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)++x1N k from rfl,
    show lastX k=(skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)++x1 k from rfl,
    run_append (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true),
    run_append (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)]
  have agree := pool_run_agrees (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)
    (skywalkPoolWires base).toFinset prefix_pool
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true))) after beforeB r1
    (fun q hq => r3 q (num_not_pool q (List.mem_toFinset.mp hq)))
  generalize hv : run (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true))) after=v
    at agree ⊢
  have vB := prefix_roundtrip hn hlo x y hx0 hx s mp
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true))) input
  rw [hBefore] at vB
  rw [vB] at agree
  have offA (q : Wire) (hq : q∉skywalkPoolWires base) : v.basis q=after.basis q := by
    rw [←hv]
    exact run_preserves_outside _ _ after q (fun h => hq (List.mem_toFinset.mp (prefix_pool h)))
  have offB (q : Wire) (hq : q∉skywalkPoolWires base) : beforeB.basis q=s.basis q := by
    rw [←hBefore]
    exact run_preserves_outside _ _ s q (fun h => hq (List.mem_toFinset.mp (first_pool true h)))
  have g2056 : base 2400∉wireBlock base 2056 256 := by
    intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj; have := base_injective e; omega
  have gv : v.basis (base 2400)=s.basis (base 2400) := by
    rw [offA _ g_not_pool,r3 _ g2056,offB _ g_not_pool]
  rw [←gv]
  exact x1N_pw k hk x y hx s v _ _ _ input agree.1 (fun q hq => agree.2 q (List.mem_toFinset.mpr hq))

theorem programN_sub (k : Nat) :
    wires (ParityXExit.programN base (base 2400) k) ⊆ wires (ParityXExit.programAll base (base 2400) k) := by
  have pre := ParityXExit.prefix_sub base (base 2400) k
  have f514 : base 514 ∈ wires (ExitMerge.fPart base (base 2400) k) := by
    simp only [ExitMerge.fPart,wires_append,Finset.mem_union]
    right
    simp [wires,Instr.wires]
  have f722 : base 722 ∈ wires (ExitMerge.fPart base (base 2400) k) := by
    simp only [ExitMerge.fPart,wires_append,Finset.mem_union]
    right
    simp [wires,Instr.wires]
  have fp : wires (ExitMerge.fPart base (base 2400) k) ⊆ wires (ParityXExit.prefixAll base (base 2400) k) := by
    simp only [ParityXExit.prefixAll,wires_append]
    intro q hq
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl hq)))
  unfold ParityXExit.programN
  rw [wires_append]
  refine Finset.union_subset pre ?_
  intro q hq
  have hq' : q = base 722 ∨ q = base 514 := by
    simpa [ECDSAAdd.Entrant.FlagEntry.swp,wires,Instr.wires] using hq
  rcases hq' with rfl | rfl
  · exact pre (fp f722)
  · exact pre (fp f514)

theorem x1N_sub (k : Nat) : wires (x1N k) ⊆ wires (x1 k) := by
  rw [x1N,x1,renameProgram_support,renameProgram_support]
  exact Finset.image_subset_image (programN_sub k)

theorem lastXN_sub (k : Nat) : wires (lastXN k) ⊆ wires (lastX k) := by
  simp only [lastXN,lastX,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (x1N_sub k)

theorem kernelXN_sub_aux (k : Nat) :
    wires (renameProgram phaseHost (lastXN k)) ⊆ wires (renameProgram phaseHost (lastX k)) := by
  rw [renameProgram_support,renameProgram_support]
  exact Finset.image_subset_image (lastXN_sub k)

def kernelXN (k : Nat) : Program :=
  renameProgram phaseHost (Rolling1588TickGap.firstPhase false)++
    (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastXN k))

theorem kernelXN_sub (k : Nat) : wires (kernelXN k) ⊆ wires (kernelX k) := by
  simp only [kernelXN,kernelX,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (Finset.Subset.refl _) (kernelXN_sub_aux k))

theorem pk_not_sites : pkP∉phaseSites := by
  intro hq
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,pkP] at hq
  rcases hq with e|e|e|e|e|e <;> have := base_injective e <;> omega

private theorem phase_sites_splitN : phaseSites=FrontierEntry1591Native.workSites∪phaseHosts := by
  ext q
  simp only [phaseSites,phaseHosts,FrontierEntry1591Native.workSites,Finset.mem_union,
    List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem rebindN (P F Q : Program) (s : State) (m : List Bool)
    (input : ∀q∈phaseSites,s.basis q=false)
    (firstFree : ∀q∈phaseHosts,q∉wires P)
    (firstClean : ∀records,∀q∈FrontierEntry1591Native.workSites,
      (run P records s).basis q=false)
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (lastFree : ∀q∈phaseHosts,q∉wires Q)
    (output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel P F Q) m s).basis q=false) :
    run (renameProgram phaseHost P++(F++renameProgram phaseHost Q)) m s=
      run (FrontierEntry1591Native.kernel P F Q) m s := by
  let mp := m.take (measurementCount P)
  let rest := m.drop (measurementCount P)
  let mf := rest.take (measurementCount F)
  let mr := rest.drop (measurementCount F)
  let before := run P mp s
  let after := run F mf before
  have finalClean : ∀q∈phaseSites,(run Q mr after).basis q=false := by
    simpa only [FrontierEntry1591Native.kernel,run_append] using output
  have lastInput : ∀q∈phaseSites,after.basis q=false := by
    intro q hq
    rw [phase_sites_splitN] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact (run_preserves_outside F mf before q (fieldFree q work)).trans (firstClean mp q work)
    · exact (run_preserves_outside Q mr after q (lastFree q host)).symm.trans
        (finalClean q (by rw [phase_sites_splitN];exact Finset.mem_union_right _ host))
  have firstOutput : ∀q∈phaseSites,(run P mp s).basis q=false := by
    intro q hq
    rw [phase_sites_splitN] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact firstClean mp q work
    · exact (run_preserves_outside P mp s q (firstFree q host)).trans
        (input q (by rw [phase_sites_splitN];exact Finset.mem_union_right _ host))
  have first := phase_run_eq P s mp input firstOutput
  have last := phase_run_eq Q after mr lastInput finalClean
  simp only [FrontierEntry1591Native.kernel,run_append,(renameProgram_counts _ _).2]
  rw [first]
  exact last

theorem hostedN (F : Program) (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m : List Bool) (value : Nat) (input : SkywalkArithmeticInput base x y s.basis)
    (integerBoundary : ∀mn mf,
      run (Rolling1588.stackForward false) mf (run (FrontierEntry1591Native.forward base) mn s)=
        pullState (OB5.sig 511) (run (Rolling1588.allEncode base false 102) []
          (run (W.compactSkywalkForward base 1 511) []
            (run (FrontierEntry1591Native.forward base) mn s))))
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (fieldResult : ∀mp mf,
      let beforeA := run (Rolling1588.firstPhase false) mp s
      let beforeB := run (Rolling1588.firstPhase true) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    run (renameProgram phaseHost (Rolling1588.firstPhase false)++
        (F++renameProgram phaseHost (lastXN k))) m s =
      put (run (renameProgram phaseHost (Rolling1588.firstPhase false)++
        (F++renameProgram phaseHost (lastX k))) m s) pkP (s.basis (base 2400) && decide (k<x)) := by
  have raw := rawX F k hk hn hlo x y hx0 hx s m value input fieldResult
  have rn := rawN F k hk hn hlo x y hx0 hx s m value input fieldResult
  have clean := caller_phase_clean x y s input
  obtain ⟨o1,o2,o3,o4⟩ := raw
  have output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s).basis q=false := by
    intro q hq
    have hq' := hq
    simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq'
    by_cases h26 : q=base 1026
    · subst h26
      apply top_zero _ (by rw [o3]; exact (negDiv_lt k x _ hx).trans p_lt)
      exact List.mem_map.mpr ⟨1026,by simp only [List.mem_range'_1]; omega,rfl⟩
    · rw [o4 q (sites_not_num q hq) (sites_not_kR q hq h26)]
      exact clean q hq
  have outputN : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastXN k)) m s).basis q=false := by
    intro q hq
    have ne : q≠pkP := fun e => pk_not_sites (e ▸ hq)
    rw [rn]
    simpa [put,writeBit,ne] using output q hq
  have sameO := rebindN (Rolling1588.firstPhase false) F (lastX k) s m clean (first_hosts_free false)
    (fun records => first_clean_of_boundary false hn x y hx0 hx s records input integerBoundary)
    fieldFree (lastX_hosts_free k) output
  have sameN := rebindN (Rolling1588.firstPhase false) F (lastXN k) s m clean (first_hosts_free false)
    (fun records => first_clean_of_boundary false hn x y hx0 hx s records input integerBoundary)
    fieldFree (fun q hq h => lastX_hosts_free k q hq (lastXN_sub k h)) outputN
  rw [sameN,sameO,rn]

private theorem append_run_eqN (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem kernelXN_pw (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg : s.basis (base 2409)=false) (hs : s.basis (base 2410)=false) :
    run (kernelXN k) m s = put (run (kernelX k) m s) pkP (s.basis (base 2400) && decide (k<x)) := by
  have records : measurementCount (renameProgram phaseHost (Rolling1588TickGap.firstPhase false))=
      measurementCount (renameProgram phaseHost (Rolling1588.firstPhase false)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(Rolling1588TickGap.first_metrics false).2.1]
  have eqO := append_run_eqN _ _ (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k)) s m records
    (fun r => Rolling1588TickGap.first_hosted_run_eq false hn x Y.val hx0 hx s r input)
  have eqN := append_run_eqN _ _ (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastXN k)) s m records
    (fun r => Rolling1588TickGap.first_hosted_run_eq false hn x Y.val hx0 hx s r input)
  have res := hostedN Rolling1588.exitFieldHosted k hk hn hlo x Y.val hx0 hx s m (centerWord (Y*(x:Fp)/2)) input
    (fun mn mf => Rolling1588.stackForward_boundary false hn hlo x hx0 hx _ mf
      (FrontierEntry1591Native.caller_first_stageW base hn x Y.val hx0 hx s mn input))
    Rolling1588.exitFieldHosted_work_free
    (fun mp mf => Rolling1588.exit_boundary hn hlo ho hf x Y hx0 hx s mp mf input hg hs)
  rw [kernelXN,kernelX,eqN,eqO]
  exact res

theorem kernelXN_support (k : Nat) : wires (kernelXN k)⊆OB5Support.logicalSites :=
  (kernelXN_sub k).trans (kernelX_support k)

theorem wordTransferN (L : ControlledPointLayout) (f : Wire → Wire) (k : Nat)
    (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool)
    (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain)
    (gSite : base 2400∈domain) (pkD : pkP∈domain)
    (X : Nat) (Y : Fp)
    (s : State) (m : List Bool)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (PN PO : Program) (supN : wires PN⊆domain) (supO : wires PO⊆domain)
    (P_spec : ∀(t : State)(records : List Bool),
      SkywalkArithmeticInput base X Y.val t.basis →
      t.basis (base 2409)=false → t.basis (base 2410)=false →
      run PN records t = put (run PO records t) pkP (t.basis (base 2400) && decide (k<X))) :
    run (renameProgram f PN) m s =
      put (run (renameProgram f PO) m s) (f pkP) (s.basis L.core.generic && decide (k<X)) := by
  let t := ECDSAAdd.Entrant.selInput domain f s
  have inputBits (q : Wire) (hq : q∈domain) : t.basis q=s.basis (f q) := by
    simp only [t,ECDSAAdd.Entrant.selInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : t.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val t.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) t.basis=X
      rw [ECDSAAdd.Entrant.selRegMap f _ t.basis s.basis
        (fun q hq => inputBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hX
    · change regValue (wireBlock base 2056 256) t.basis=Y.val
      rw [ECDSAAdd.Entrant.selRegMap f _ t.basis s.basis
        (fun q hq => inputBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hY
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [t,ECDSAAdd.Entrant.selInput,if_neg used]
  have pw := P_spec t m input (zero _ selectorG) (zero _ selectorS)
  have trN := run_rename_pool f domain injective PN supN m t s rfl inputBits
  have trO := run_rename_pool f domain injective PO supO m t s rfl inputBits
  have tg : t.basis (base 2400)=s.basis L.core.generic := by rw [inputBits _ gSite,controlMap]
  rw [tg] at pw
  apply State.extensionality
  · rw [trN.1,pw]; exact trO.1.symm
  · funext q
    by_cases image : q∈domain.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      rw [trN.2 a ha,pw]
      by_cases e : a=pkP
      · subst e; simp [put,writeBit]
      · have ne : f a≠f pkP := fun h => e (injective a ha pkP pkD h)
        simp only [put,writeBit,Function.update_apply,if_neg e,if_neg ne]
        exact (trO.2 a ha).symm
    · have ne : q≠f pkP := fun h => image (h ▸ Finset.mem_image_of_mem _ pkD)
      rw [run_rename_pool_outside f domain PN supN m s q image]
      simp only [put,writeBit,Function.update_apply,if_neg ne]
      rw [run_rename_pool_outside f domain PO supO m s q image]

theorem exitN_pw (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k < p) (X Y : Nat) (hX : X < p) (hX0 : 0 < X) (hY : Y < p)
    (s : State) (m : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    run (FrontierEntry1591Callers.exit (kernelXN k) L) m s =
      put (run (FrontierEntry1591Callers.exit (kernelX k) L) m s) (wireFn2 L pkP)
        (s.basis L.core.generic && decide (k<X)) := by
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  rcases placement2 L hw hn with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,
    selectorG,selectorS,zeroFlag⟩
  have dx : (wireBlock base 770 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have dy : (wireBlock base 2056 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have gSite : base 2400∈OB5Support.logicalSites := by
    have := E1QubitPlacement.sw_logical 2400 (by unfold E1QubitPlacement.Rng; omega)
    simpa [E1QubitPlacement.sw] using this
  have pkD : pkP∈OB5Support.logicalSites := by
    have := E1QubitPlacement.sw_logical 724 (by unfold E1QubitPlacement.Rng; omega)
    simpa [E1QubitPlacement.sw,pkP] using this
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have result := wordTransferN L (wireFn2 L) k OB5Support.logicalSites
    (fun a ha b hb eq => injective a (ArithmeticOB5.logical_sub_old ha) b
      (ArithmeticOB5.logical_sub_old hb) eq)
    divisorMap numeratorMap controlMap
    (fun q hq used hx hy => sharedWork q hq (ArithmeticOB5.logical_sub_old used) hx hy)
    selectorG selectorS dx dy gSite pkD X (Y:Fp) s m hx (hy.trans yValue.symm) hc
    (kernelXN k) (kernelX k) (kernelXN_support k) (kernelX_support k)
    (fun t records input hg hs => kernelXN_pw k hk
      config.1 above config.2.1 config.2.2 X (Y:Fp) hX0 hX t records input hg hs)
  simpa only [FrontierEntry1591Callers.exit] using result

def restXXN (L : ControlledPointLayout) (k : Nat) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase false)++
      (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastXN k)))

theorem exit_splitN (L : ControlledPointLayout) (k : Nat) :
    FrontierEntry1591Callers.exit (kernelXN k) L=E1QubitPlacement.tickF L++restXXN L k := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,kernelXN,Rolling1588TickGap.firstPhase,restXXN,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem pk_wire (L : ControlledPointLayout) : wireFn2 L pkP = ECDSAAdd.Entrant.FlagEntry.pkW L := by
  rw [ECDSAAdd.Entrant.FlagTop.pk_eq L]
  unfold E1QubitPlacement.pmapR E1QubitPlacement.pmap
  rw [E1QubitPlacement.rho_base,E1QubitPlacement.sig_base]
  rfl

theorem x1N_counts (k : Nat) :
    toffoliCount (x1N k) + 254 = toffoliCount (x1 k) ∧ measurementCount (x1N k) ≤ measurementCount (x1 k) ∧
    Challenge.gateSlots (x1N k) ≤ Challenge.gateSlots (x1 k) + 2 := by
  have h := ParityXExit.programN_counts base (base 2400) k
  simp only [x1N,x1,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  exact h

theorem restXXN_counts (L : ControlledPointLayout) (k : Nat) :
    toffoliCount (restXXN L k) + 254 = toffoliCount (restXX L k) ∧
    measurementCount (restXXN L k) ≤ measurementCount (restXX L k) ∧
    Challenge.gateSlots (restXXN L k) ≤ Challenge.gateSlots (restXX L k) + 2 := by
  have h := x1N_counts k
  simp only [restXXN,restXX,lastXN,lastX,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    Baselines.rename_gateSlots]
  omega

theorem restXXN_sub (L : ControlledPointLayout) (k : Nat) : wires (restXXN L k) ⊆ wires (restXX L k) := by
  simp only [restXXN,restXX,wires_append,renameProgram_support]
  apply Finset.image_subset_image
  apply Finset.union_subset_union (Finset.Subset.refl _)
  apply Finset.union_subset_union (Finset.Subset.refl _)
  exact Finset.image_subset_image (lastXN_sub k)

theorem x1N_physical (k : Nat) : GatePhysical (x1N k) :=
  gatePhysical_rename pi pi.injective _ (ParityXExit.programN_physical k)

theorem kernelXN_physical (k : Nat) : GatePhysical (kernelXN k) := by
  have old := Rolling1588TickGap.exitKernel_physical
  simp only [Rolling1588TickGap.exitKernel,Rolling1588TickGap.kernel,gatePhysical_append] at old
  have last := InverseFive23.last_physical15 true
  simp only [InverseFive23.lastPhase15,gatePhysical_append] at last
  have lx : GatePhysical (lastXN k) := by
    simp only [lastXN,gatePhysical_append]; exact ⟨last.1,x1N_physical k⟩
  simp only [kernelXN,gatePhysical_append]
  exact ⟨old.1,old.2.1,gatePhysical_rename phaseHost phaseHost.injective _ lx⟩

theorem restXXN_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Nat) :
    GatePhysical (restXXN L k) := by
  have physical := FrontierEntry1591Native.placed_physical L hw hn (kernelXN k) (kernelXN_support k)
    (kernelXN_physical k)
  have e : GatePhysical (FrontierEntry1591Callers.exit (kernelXN k) L) := by
    unfold FrontierEntry1591Callers.exit; exact physical
  rw [exit_splitN,gatePhysical_append] at e
  exact e.2

end ECDSAAdd.Entrant.ParityXExitInverse23Kernel
end

section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.FlagExit
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out ParityEven ParityUniform

/-- The new program from `s'` ends in the old program's state from `s`, plus one write. -/
structure PadP (P' P : Program) (s' s : State) (pad : List Bool → List Bool) (w : Wire) (v : Bool) : Prop where
  run_eq : ∀ d, run P' d s' = put (run P (pad d) s) w v
  drop_eq : ∀ d, (pad d).drop (measurementCount P) = d.drop (measurementCount P')

theorem PadP.of_same {P' P : Program} {s' s : State} {w : Wire} {v : Bool}
    (h : ∀ r, run P' r s' = put (run P r s) w v) :
    PadP P' P s' s (fun r => pfx (measurementCount P) r ++ r.drop (measurementCount P')) w v := by
  have tk : ∀ (r x : List Bool), (pfx (measurementCount P) r ++ x).take (measurementCount P) =
      pfx (measurementCount P) r := by
    intro r x
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ (r x : List Bool), (pfx (measurementCount P) r ++ x).drop (measurementCount P) = x := by
    intro r x
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    have e : run P (pfx (measurementCount P) d ++ d.drop (measurementCount P')) s = run P d s := by
      rw [← run_take, tk, run_pfx]
    rw [h d, e]
  · intro d
    exact dr _ _

theorem Pad.of_same {P' P : Program} {s' s : State}
    (h : ∀ r, run P' r s' = run P r s) :
    Pad P' P s' s (fun r => pfx (measurementCount P) r ++ r.drop (measurementCount P')) := by
  have tk : ∀ (r x : List Bool), (pfx (measurementCount P) r ++ x).take (measurementCount P) =
      pfx (measurementCount P) r := by
    intro r x
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ (r x : List Bool), (pfx (measurementCount P) r ++ x).drop (measurementCount P) = x := by
    intro r x
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    have e : run P (pfx (measurementCount P) d ++ d.drop (measurementCount P')) s = run P d s := by
      rw [← run_take, tk, run_pfx]
    rw [h d, e]
  · intro d
    exact dr _ _

theorem PadP.append {P' P : Program} {s' s : State} {pad : List Bool → List Bool} {w : Wire} {v : Bool}
    (h : PadP P' P s' s pad w v) (R : Program) (hw : w ∉ wires R) :
    PadP (P' ++ R) (P ++ R) s' s pad w v := by
  constructor
  · intro d
    rw [run_append, run_take, h.run_eq, run_put _ _ _ _ _ hw, run_append, run_take, h.drop_eq]
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, h.drop_eq, List.drop_drop]

theorem PadP.prefix (A' A P' P : Program) (s' s : State) (pad : List Bool → List Bool) (w : Wire) (v : Bool)
    (hc : measurementCount A' = measurementCount A)
    (h : ∀ d, PadP P' P (run A' d s') (run A d s) pad w v) :
    PadP (A' ++ P') (A ++ P) s' s
      (fun d => pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))) w v := by
  have tk : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))).take
      (measurementCount A) = pfx (measurementCount A) d := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))).drop
      (measurementCount A) = pad (d.drop (measurementCount A)) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, run_append A, tk, dr, run_pfx, hc]
    exact (h d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h d).drop_eq, hc,
      List.drop_drop]

theorem PadP.prefix_general (A' A P' P : Program) (s' s : State) (pad : List Bool → List Bool) (w : Wire) (v : Bool)
    (h : ∀ d, PadP P' P (run A' d s') (run A d s) pad w v) :
    PadP (A' ++ P') (A ++ P) s' s
      (fun d => pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))) w v := by
  have tk : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))).take
      (measurementCount A) = pfx (measurementCount A) d := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))).drop
      (measurementCount A) = pad (d.drop (measurementCount A')) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, run_append A, tk, dr, run_pfx]
    exact (h d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h d).drop_eq,
      List.drop_drop]

/-- A padded head followed by a written tail. -/
theorem PadP.cat {A' A B' B : Program} {s' s : State} {pad1 pad2 : List Bool → List Bool} {w : Wire} {v : Bool}
    (h1 : Pad A' A s' s pad1)
    (h3 : ∀ d, PadP B' B (run A' d s') (run A (pad1 d) s) pad2 w v) :
    PadP (A' ++ B') (A ++ B) s' s
      (fun d => pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))) w v := by
  have tk : ∀ d, (pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))).take
      (measurementCount A) = pfx (measurementCount A) (pad1 d) := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))).drop
      (measurementCount A) = pad2 (d.drop (measurementCount A')) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, run_append A, tk, dr, run_pfx]
    exact (h3 d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h3 d).drop_eq,
      List.drop_drop]

/-- A written head followed by a tail that consumes the write. -/
theorem Pad.ofP {A' A B' B : Program} {s' s : State} {pad1 pad2 : List Bool → List Bool} {w : Wire} {v : Bool}
    (h1 : PadP A' A s' s pad1 w v)
    (h2 : ∀ d, Pad B' B (put (run A (pad1 d) s) w v) (run A (pad1 d) s) pad2) :
    Pad (A' ++ B') (A ++ B) s' s
      (fun d => pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))) := by
  have tk : ∀ d, (pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))).take
      (measurementCount A) = pfx (measurementCount A) (pad1 d) := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))).drop
      (measurementCount A) = pad2 (d.drop (measurementCount A')) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, h1.run_eq, run_append A, tk, dr, run_pfx]
    exact (h2 d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h2 d).drop_eq,
      List.drop_drop]

/-- Renaming carries a written run when the written wire is fixed. -/
theorem PadP.rename (f : Wire → Wire) (inj : Function.Injective f) (pk : Wire) (hfix : f pk = pk)
    (P' P : Program) (hw : pk ∈ wires P') (t : State) (e v : Bool) (pad : List Bool → List Bool)
    (h : PadP P' P (put (pullState f t) pk e) (pullState f t) pad pk v) :
    PadP (renameProgram f P') (renameProgram f P) (put t pk e) t pad pk v := by
  constructor
  · intro d
    have S := wires P' ∪ wires P
    have A := run_rename_pool f (wires P' ∪ wires P) (fun a _ b _ eq => inj eq) P' Finset.subset_union_left d
      (put (pullState f t) pk e) (put t pk e) rfl (by
        intro q _
        by_cases eq : q = pk
        · subst eq; simp [put, writeBit, hfix]
        · have ne : f q ≠ pk := fun E => eq (inj (E.trans hfix.symm))
          simp only [put, writeBit, Function.update_apply, eq, ne, if_false]
          rfl)
    have B := run_rename_pool f (wires P' ∪ wires P) (fun a _ b _ eq => inj eq) P Finset.subset_union_right
      (pad d) (pullState f t) t rfl (fun _ _ => rfl)
    rw [h.run_eq d] at A
    apply State.extensionality
    · exact A.1.trans B.1.symm
    funext q
    by_cases im : q ∈ (wires P' ∪ wires P).image f
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp im
      rw [A.2 c hc]
      by_cases eq : c = pk
      · subst eq; simp [put, writeBit, hfix]
      · have ne : f c ≠ pk := fun E => eq (inj (E.trans hfix.symm))
        simp only [put, writeBit, Function.update_apply, eq, ne, if_false]
        exact (B.2 c hc).symm
    · have ne : q ≠ pk := by
        intro E; subst E
        exact im (Finset.mem_image.mpr ⟨q, Finset.mem_union_left _ hw, hfix⟩)
      rw [run_rename_pool_outside f (wires P' ∪ wires P) P' Finset.subset_union_left d _ q im]
      simp only [put, writeBit, Function.update_apply, ne, if_false]
      rw [run_rename_pool_outside f (wires P' ∪ wires P) P Finset.subset_union_right (pad d) t q im]
  · intro d
    rw [(renameProgram_counts _ _).2, (renameProgram_counts _ _).2]
    exact h.drop_eq d

theorem flag_out (a b : Fp) : decide (a.val < b.val) = decide (a.val < (a-b).val) := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  have sv : (a-b).val=(a.val+p-b.val)%p := by
    rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
    rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt b))]
  have ha : a.val < p := ZMod.val_lt a
  have hb : b.val < p := ZMod.val_lt b
  rw [sv]
  apply decide_eq_decide.mpr
  by_cases h : a.val < b.val
  · have e : (a.val+p-b.val)%p = a.val+p-b.val := Nat.mod_eq_of_lt (by omega)
    rw [e]; omega
  · have e : (a.val+p-b.val)%p = a.val-b.val := by
      have e2 : a.val+p-b.val = (a.val-b.val)+p := by omega
      rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e]; omega

theorem run_pre (A B : Program) (r : List Bool) (w : State) :
    run (A ++ B) (pfx (measurementCount A) [] ++ r) w = run B r (run A [] w) := by
  rw [run_append,
    List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length]),
    List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length]),
    run_pfx]
  rfl

section Second
open ParityXExitInverse23Kernel ParityStageBothInverse23 ReflectionE1TickGapLow48 ParityXEntry
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pk_not_exitY (k : Fp) (hg : pkW L ≠ L.core.generic) : pkW L ∉ wires (exitYAll L k) := by
  intro h
  have sub := (exitYAll_wires L hw k).trans (ExitFusionResearch.exitY_support L hw k)
  have h2 := Finset.mem_of_subset sub h
  rcases List.mem_cons.mp (List.mem_toFinset.mp h2) with e | e
  · exact hg e
  · exact pk_not_K L hw hn e

theorem rest_pw (k cx X Y : Fp) (G : Bool) (origin : BasisState) (s : State)
    (hs : PointDialogValues L X Y G origin s.basis)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) (d r : List Bool) :
    run (restXXN L cx.val) r (run (squareEntry L k) d s) =
      put (run (restXX L cx.val) r (run (squareEntry L k) d s)) (pkW L)
        (G && decide (cx.val < (X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
          (if G then k else 0)).val)) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  obtain ⟨-,vW⟩ := (square.seq add) s [] hs
  generalize hwd : run (SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k) [] s = w at vW
  have eu : run (squareEntry L k) d s = run (E1QubitPlacement.tickF L) [] w := by
    rw [squareEntry_base L hw hn k X Y G origin s d [] hs, run_append, ← hwd]
    simp only [List.take_nil, List.drop_nil]
  have hpos : 0 < (Z+(if G then k else 0)).val :=
    Nat.pos_of_ne_zero (fun hz => hx ((ZMod.val_eq_zero _).mp hz))
  have e1 := exitN_pw L hw hn cx.val cx.isLt (Z+(if G then k else 0)).val Y.val (ZMod.val_lt _) hpos
    (ZMod.val_lt _) w (pfx (measurementCount (E1QubitPlacement.tickF L)) [] ++ r) vW.x vW.y vW.clean
  rw [exit_splitN,exit_splitX,run_pre,run_pre,← eu,vW.generic,pk_wire] at e1
  exact e1

def restPad (L : ControlledPointLayout) (k : Nat) : List Bool → List Bool :=
  fun r => pfx (measurementCount (restXX L k)) r ++ r.drop (measurementCount (restXXN L k))

def secondStageN (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  squareEntry L k ++ restXXN L cx.val ++ exitYAll L cy

def padS (L : ControlledPointLayout) (k cx : Fp) : List Bool → List Bool :=
  fun d => pfx (measurementCount (squareEntry L k)) d ++
    restPad L cx.val (d.drop (measurementCount (squareEntry L k)))

theorem second_padp (k cy cx X Y : Fp) (G : Bool) (origin : BasisState) (s : State)
    (hs : PointDialogValues L X Y G origin s.basis) (hg : pkW L ≠ L.core.generic)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    PadP (secondStageN L k cy cx) (secondStageAll L k cy cx) s s (padS L k cx) (pkW L)
      (G && decide (cx.val < (X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
        (if G then k else 0)).val)) := by
  have h := PadP.prefix (squareEntry L k) (squareEntry L k) (restXXN L cx.val) (restXX L cx.val) s s
    (restPad L cx.val) (pkW L) _ rfl
    (fun d => PadP.of_same (fun r => rest_pw L hw hn k cx X Y G origin s hs hx d r))
  exact h.append (exitYAll L cy) (pk_not_exitY L hw hn cy hg)

def genericN (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ((entryYAll L (-cy) ++ entryXNew L (pkW L) (-cx)) ++ restEntry L) ++
    secondStageN L (ReflectionE1.correction cx) cy cx

def padE (L : ControlledPointLayout) (cy cx : Fp) : List Bool → List Bool :=
  fun d => pfx (measurementCount (entryYAll L (-cy))) d ++
    (List.replicate (measurementCount (E1Merge.comparePart MappedCompressed.base (MappedCompressed.base 2400) (-cx).val)) false ++
      d.drop (measurementCount (entryYAll L (-cy))))

theorem head_pad (cx cy X Y : Fp) (s : State)
    (hX : regValue L.point.x s.basis = X.val) (hY : regValue L.point.y s.basis = Y.val)
    (hc : regValue L.dialogPool s.basis = 0) (hg : pkW L ≠ L.core.generic) :
    Pad ((entryYAll L (-cy) ++ entryXNew L (pkW L) (-cx)) ++ restEntry L)
      (entryStageAll L (-cx) (-cy))
      (put s (pkW L) (if s.basis L.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false)) s
      (padE L cy cx) := by
  have inner := Pad.prefix (entryYAll L (-cy)) (entryYAll L (-cy)) (entryXNew L (pkW L) (-cx))
    (entryXAll L (-cx))
    (put s (pkW L) (if s.basis L.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false)) s
    (fun d => List.replicate (measurementCount (E1Merge.comparePart MappedCompressed.base (MappedCompressed.base 2400) (-cx).val)) false ++ d) rfl (by
      intro d
      rw [run_put _ _ _ _ _ (pk_not_Y L hw hn _ hg)]
      have eY := entryYAll_eq L hw hn Y (-cy) s d hY hc
      have fy := EntryFuse.fusedY_correct L hw hn Y (-cy) s d hY hc
      rw [eY]
      generalize hu : run (EntryFuse.fusedY L (-cy)) d s = u at fy
      have tx : regValue L.point.x u.basis = X.val := by
        rw [regValue_congr _ _ s.basis (fun q hq => fy.2.2 q ((E1QubitPlacement.lay L hw hn q).1 hq)), hX]
      have tc : regValue L.dialogPool u.basis = 0 := by
        rw [regValue_congr _ _ s.basis (fun q hq => fy.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).2)), hc]
      have tg : u.basis L.core.generic = s.basis L.core.generic :=
        fy.2.2 _ ((E1QubitPlacement.lay L hw hn _).2.2 rfl).2
      rw [← tg]
      constructor
      · intro d'
        exact entryXNew_run L hw hn (pkW L) X (-cx) u tx tc (pk_pool L hw) (pk_ne_flag L hw hn)
          (pk_ne_high L hw hn) (pk_ne_x L hw hn)
          (by rw [E1QubitPlacement.pmap_g L hw hn]; exact hg) d'
      · intro d'
        rw [entryXNew_measure L (pkW L) (-cx), ← List.drop_drop, List.drop_left' (by simp)])
  exact inner.append _

def padG (L : ControlledPointLayout) (cx cy : Fp) : List Bool → List Bool :=
  fun d => pfx (measurementCount (entryStageAll L (-cx) (-cy))) (padE L cy cx d) ++
    padS L (ReflectionE1.correction cx) cx
      (d.drop (measurementCount ((entryYAll L (-cy) ++ entryXNew L (pkW L) (-cx)) ++ restEntry L)))

theorem generic_padp_true (X Y cx cy : Fp) (s : State) (e : Bool)
    (hv : PointDialogValues L X Y true s.basis s.basis)
    (he : e = (if s.basis L.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))
    (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) (hg : pkW L ≠ L.core.generic) :
    PadP (genericN L cx cy) (genericAll L cx cy) (put s (pkW L) e) s (padG L cx cy) (pkW L)
      (decide (cx.val < (genericX X Y cx cy).val)) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hvv:=generic_inplace_values X Y cx cy hX
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) true s.basis
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hvv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have head := head_pad L hw hn cx cy X Y s hv.x hv.y hv.clean hg
  rw [← he] at head
  have hc := PadP.cat (B' := secondStageN L (ReflectionE1.correction cx) cy cx)
    (B := secondStageAll L (ReflectionE1.correction cx) cy cx) (pad2 := padS L (ReflectionE1.correction cx) cx)
    (w := pkW L) (v := decide (cx.val < d.val)) head (by
      intro q
      rw [head.run_eq q]
      obtain ⟨-,v1⟩ := first s (padE L cy cx q) hv
      have sp := second_padp L hw hn (ReflectionE1.correction cx) cy cx (X-cx) a true s.basis _ v1 hg
        (by simpa only [if_true,hd4] using hd)
      simp only [if_true,hd4,Bool.true_and] at sp
      exact sp)
  have fo := flag_out cx d
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at fo
  rw [← fo]
  exact hc

theorem generic_padp_false (X Y cx cy : Fp) (s : State) (e : Bool)
    (hv : PointDialogValues L X Y false s.basis s.basis)
    (he : e = (if s.basis L.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))
    (hX : X≠0) (hg : pkW L ≠ L.core.generic) :
    PadP (genericN L cx cy) (genericAll L cx cy) (put s (pkW L) e) s (padG L cx cy) (pkW L) false := by
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) false s.basis
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  simp only [Bool.false_eq_true,if_false,add_zero] at first
  have head := head_pad L hw hn cx cy X Y s hv.x hv.y hv.clean hg
  rw [← he] at head
  exact PadP.cat (B' := secondStageN L (ReflectionE1.correction cx) cy cx)
    (B := secondStageAll L (ReflectionE1.correction cx) cy cx) (pad2 := padS L (ReflectionE1.correction cx) cx)
    (w := pkW L) (v := false) head (by
      intro q
      rw [head.run_eq q]
      obtain ⟨-,v1⟩ := first s (padE L cy cx q) hv
      have sp := second_padp L hw hn (ReflectionE1.correction cx) cy cx X (Y/X) false s.basis _ v1 hg
        (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
      simpa only [Bool.false_and] using sp)

end Second

end ECDSAAdd.Entrant.FlagExit
end

section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.OutFlag
open Arithmetic Challenge RecordedQuantum MeasuredCodec5 Baselines InputSentinel Secp256k1 ControlledPointLayout
  ZeroFill OutputOpt ParityEven

theorem zeroWith_extract_pre (T : Wire → Program) (E : Program) (c : Wire) (bs : List ZeroBit)
    (hnd : (c :: bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (hz : ∀ b ∈ bs, s.basis b.work = false) (B : State)
    (hB : ∀ m', run (T (lastWire c bs)) m' ⟨s.phase, fill c bs s.basis⟩ = B)
    (hkeep : ∀ q ∈ c :: bs.flatMap ZeroBit.wires, B.basis q = fill c bs s.basis q)
    (P : Wire) (v : Bool)
    (hE : ∀ m', run E m' ⟨s.phase, fill c bs s.basis⟩ = put ⟨s.phase, fill c bs s.basis⟩ P v)
    (hT : P ∉ wires (T (lastWire c bs)))
    (hP : P ∉ c :: bs.flatMap ZeroBit.wires) :
    run (zeroWith (fun w => E ++ T w) c bs) m s =
      ⟨(run (zeroWith T c bs) m s).phase, writeBit (run (zeroWith T c bs) m s).basis P v⟩ := by
  have ho := zeroWith_fill T c bs hnd s m hz B hB hkeep
  have hw : ∀ b ∈ bs, b.work ≠ P := by
    intro b hb e
    apply hP
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires, e]⟩
  have hn := zeroWith_fill (fun w => E ++ T w) c bs hnd s m hz ⟨B.phase, writeBit B.basis P v⟩
    (by
      intro m'
      show run (E ++ T (lastWire c bs)) m' _ = _
      rw [run_append, hE, run_put _ _ _ _ _ hT, hB]
      rfl)
    (by
      intro q hq
      have hne : q ≠ P := fun e => hP (e ▸ hq)
      simpa [writeBit, hne] using hkeep q hq)
  rw [hn, ho]
  simp only [clear_write bs _ P v hw]

theorem oshape_state (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire)
    (w : Nat → Wire) (i0 : Nat) (it : List Nat) (work : List Wire)
    (hPn : ((i0 :: it).map w).Nodup) (x1P : xr1 ∉ (i0 :: it).map w) (x2P : xr2 ∉ (i0 :: it).map w)
    (hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextP : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w)
    (hwl : (it.map w).length = work.length) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u])
    (s : State)
    (hz : ∀ q ∈ work, s.basis q = false)
    (hp : OutputOpt.otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis) :
    ∃ s2 : State,
      s2.phase = s.phase ∧ (∀ q, q ∉ (i0 :: it).map w → s2.basis q = s.basis q) ∧
      s2.basis (w i0) = (s.basis (w i0) == tr.tgt i0 (s.basis xr1, s.basis xr2)) ∧
      (∀ i ∈ it, s2.basis (w i) = (s.basis (w i) ^^ tr.tgt i (s.basis xr1, s.basis xr2))) ∧
      (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires).Nodup ∧
      (∀ b ∈ zeroPorts (it.map w) work, s2.basis b.work = false) ∧
      ∀ (E : Program) (pk : Wire) (val : Bool),
        (∀ m', run E m' ⟨s2.phase, fill (w i0) (zeroPorts (it.map w) work) s2.basis⟩ =
          put ⟨s2.phase, fill (w i0) (zeroPorts (it.map w) work) s2.basis⟩ pk val) →
        pk ∉ (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires) →
        pk ∉ wires ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)) →
        pk ∉ wires (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
          (lastWire (w i0) (zeroPorts (it.map w) work))) → ∀ m,
        run (tr.remapList xr1 xr2 w (i0 :: it) ++ ([Instr.X (w i0)] ++
          (zeroWith (fun h => E ++ OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) (w i0)
            (zeroPorts (it.map w) work) ++
          ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it))))) m s =
        put (run (tr.remapList xr1 xr2 w (i0 :: it) ++ ([Instr.X (w i0)] ++
          (zeroWith (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) (zeroPorts (it.map w) work) ++
          ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it))))) m s) pk val := by
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
    intro i hi e
    rw [hlw] at hPn
    exact (List.nodup_cons.mp hPn).1 (e ▸ List.mem_map_of_mem hi)
  have R1 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P [] s
  generalize hs1 : run (tr.remapList xr1 xr2 w (i0 :: it)) [] s = s1 at R1
  have e2 : run [Instr.X (w i0)] [] s1 = ⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ := by
    simp [run]
  generalize hs2 : (⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ : State) = s2 at e2
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
  have hcu : w i0 ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := fun h => usedNotP _ h p0l
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
  have hdis' : ∀ b ∈ zeroPorts (it.map w) work, b.input ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
    intro b hb
    have hin : b.input ∈ it.map w := by
      have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    exact ⟨fun h => usedNotP _ h (by rw [hlw]; exact List.mem_cons_of_mem _ hin), (hdisj _ hwk).2⟩
  have hz3 : ∀ b ∈ zeroPorts (it.map w) work, s2.basis b.work = false := by
    intro b hb
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    rw [s2out _ (hdisj _ hwk).1]; exact hz _ hwk
  set bs := zeroPorts (it.map w) work with hbs
  set V := (i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2) with hV
  set last := lastWire (w i0) bs with hlast
  set st := fill (w i0) bs s2.basis with hst
  have lastU : last ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
    rcases lastWire_mem (w i0) bs with e | ⟨b, hb, e⟩
    · rw [hlast, e]; exact hcu
    · rw [hlast, e]; exact (hdis' b hb).2
  have stU : ∀ q ∈ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u], st q = s.basis q := by
    intro q hq
    rw [hst, fill_outside (w i0) bs _ q (fun b hb e => (hdis' b hb).2 (e ▸ hq)), s2out q (usedNotP q hq)]
  have stL : st last = V := by
    rw [hst, hlast, fill_last (w i0) bs _ hnd hz3, huV]
  have hnd10 : [last, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup := List.nodup_cons.mpr ⟨lastU, hused⟩
  have hnd13 : [last, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup := List.nodup_cons.mpr ⟨lastU, hused⟩
  have hp' : OutputOpt.otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u (st last) st := by
    rw [stL]
    unfold OutputOpt.otailPre at hp ⊢
    rw [stU f (by simp), stU t1 (by simp), stU t2 (by simp), stU u (by simp), stU g (by simp),
      stU c (by simp), stU O (by simp), stU D (by simp), stU H (by simp), stU y0 (by simp),
      stU xr1 (by simp), stU xr2 (by simp)]
    exact hp
  let B : State := ⟨s2.phase, OutputOpt.otailEff tr xr1 xr2 f g O D H (st last) st⟩
  have hB : ∀ m', run (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u last) m' ⟨s2.phase, st⟩ = B :=
    fun m' => OutputOpt.otail_run tr v yc y2c e last xr1 xr2 y0 c f g O D H t1 t2 u hnd13 ⟨s2.phase, st⟩ m' hp'
  refine ⟨s2, s2ph, s2out, s2p0, s2it, hnd, hz3, ?_⟩
  intro E pk val hE hpk hsuf hT m
  have hkeep : ∀ q ∈ w i0 :: bs.flatMap ZeroBit.wires, B.basis q = st q := by
    intro q hq
    have hqu : q ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
      rcases List.mem_cons.mp hq with e | h
      · rw [e]; exact hcu
      · obtain ⟨b, hb, hw⟩ := List.mem_flatMap.mp h
        simp only [ZeroBit.wires, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with e | e
        · rw [e]; exact (hdis' b hb).1
        · rw [e]; exact (hdis' b hb).2
    show OutputOpt.otailEff tr xr1 xr2 f g O D H (st last) st q = st q
    rw [OutputOpt.otailEff_apply]
    have n1 : q ≠ H := fun e => hqu (by simp [e])
    have n2 : q ≠ D := fun e => hqu (by simp [e])
    have n3 : q ≠ O := fun e => hqu (by simp [e])
    have n4 : q ≠ g := fun e => hqu (by simp [e])
    have n5 : q ≠ f := fun e => hqu (by simp [e])
    simp [n1, n2, n3, n4, n5]
  have Z := zeroWith_extract_pre (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) E (w i0) bs hnd s2 m hz3
    B hB hkeep pk val hE hT hpk
  have mR : measurementCount (tr.remapList xr1 xr2 w (i0 :: it)) = 0 := remapList_mc _ _ _ _ _
  have mX : measurementCount [Instr.X (w i0)] = 0 := rfl
  have mS : measurementCount ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)) = 0 := by
    rw [measurementCount_append, mX, mR]
  rw [wrap_run _ _ _ _ mR mX, wrap_run _ _ _ _ mR mX, hs1, e2]
  change run (zeroWith (fun h => E ++ OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) (w i0) bs) m s2 =
    put (run (zeroWith (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) bs) m s2) pk val at Z
  rw [Z, run_no_measure _ mS (List.drop _ m), run_no_measure _ mS (List.drop _ m), run_put _ _ _ _ _ hsuf]

def Gc (c g O D H W : Wire) : Program := [.CX c W, .CX g W, .CX O W, .CX D W, .CX H W]

theorem Gc_run (c g O D H W : Wire) (h1 : c ≠ W) (h2 : g ≠ W) (h3 : O ≠ W) (h4 : D ≠ W) (h5 : H ≠ W)
    (s : State) (m : List Bool) :
    run (Gc c g O D H W) m s =
      put s W (s.basis W ^^ (s.basis c ^^ s.basis g ^^ s.basis O ^^ s.basis D ^^ s.basis H)) := by
  apply State.extensionality
  · rfl
  funext q
  by_cases e : q = W
  · subst e
    simp [Gc, run, put, writeBit, Function.update_apply, h1, h2, h3, h4, h5]
  · simp [Gc, run, put, writeBit, Function.update_apply, e]

/-- The output classifier with the wrap flag cleared from its chain. -/
def oclassifierF (tr : Tri) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire) : Program :=
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx ++
  ([Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  (zeroWith (fun h => (Gc c g O D H W ++ (extractClear_research tr xs work one U V F pk W ++ Gc c g O D H W)) ++
        OutputOpt.otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u h)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work) ++
  ([Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx)))

theorem oclassifierFast_run_research (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire)
    (hxs : xs.Nodup) (hlen : xs.length = 256) (hwl : work.length = 253) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ xs ∧ q ∉ work)
    (htmp : [one, U, V, F, pk].Nodup)
    (htx : ∀ q ∈ [one, U, V, F, pk], q ∉ xs ∧ q ∉ work ∧ q ≠ W)
    (hWx : W ∉ xs ∧ W ∉ work) (hWe : c ≠ W ∧ g ≠ W ∧ O ≠ W ∧ D ≠ W ∧ H ≠ W)
    (hpkE : pk ∉ [y0, c, f, g, O, D, H, t1, t2, u])
    (s : State) (m : List Bool)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis f = false ∧ s.basis t1 = false ∧
      s.basis t2 = false ∧ s.basis u = false)
    (hfl : s.basis g = (s.basis c && oX tr tr.S xs s.basis) ∧
      s.basis O = (s.basis c && oX tr tr.A xs s.basis && (s.basis y0 == yc)) ∧
      s.basis D = (s.basis c && oX tr tr.B xs s.basis && (s.basis y0 == y2c)) ∧
      s.basis H = (e && s.basis c && oX tr tr.A xs s.basis && (s.basis y0 != yc)))
    (hto : ∀ q ∈ [one, U, V, F], s.basis q = false) (hW0 : s.basis W = false)
    (x : Nat) (hx : x < 2^256) (xbit : ∀ i, i < 256 → s.basis (xs.getD i 0) = x.testBit i)
    (hpkv : s.basis pk = ((s.basis c ^^ s.basis g ^^ s.basis O ^^ s.basis D ^^ s.basis H) &&
      decide (tr.A < x))) :
    run (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) m s =
      put (run (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) m s) pk
        (s.basis pk ^^ ((s.basis c ^^ s.basis g ^^ s.basis O ^^ s.basis D ^^ s.basis H) &&
          decide (tr.A < x))) := by
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
  have hp : OutputOpt.otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis := by
    unfold OutputOpt.otailPre
    rw [← hoX, ← hoX, ← hoX]
    exact ⟨hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2, hfl.1, hfl.2.1, hfl.2.2.1, hfl.2.2.2⟩
  obtain ⟨s2, s2ph, s2out, s2p0, s2it, chnd, chz, main⟩ :=
    oshape_state tr v yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u w i0 it work hPn' x1P' x2P' hused hextP
      (by rw [hitl, hwl]) hwn hdisj' s hz.1 hp
  have zp := zeroPorts_maps (it.map w) work (by rw [hitl, hwl])
  set p0 := w i0 with hp0
  set Gv := (s.basis c ^^ s.basis g ^^ s.basis O ^^ s.basis D ^^ s.basis H) with hGv
  set bs := zeroPorts (it.map w) work with hbs
  obtain ⟨F0, hF0⟩ : ∃ F0 : State, F0 = ⟨s2.phase, fill p0 bs s2.basis⟩ := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : State, B = put F0 W Gv := ⟨_, rfl⟩
  have Boff : ∀ q, q ≠ W → B.basis q = fill p0 bs s2.basis q := by
    intro q hq; rw [hBd, hF0]; simp [put, writeBit, hq]
  have tmpM (q : Wire) (hq : q ∈ [one, U, V, F, pk]) (i : Nat) (hi : i < 256) : q ≠ w i :=
    fun e => (htx q hq).1 (e ▸ wmem i hi)
  have bsW : ∀ b ∈ bs, b.work ∈ work := by
    intro b hb
    have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
  have bsI : ∀ b ∈ bs, b.input ∈ it.map w := by
    intro b hb
    have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
  have hlenbs : it.length = bs.length := by
    have h1 : (bs.map ZeroBit.input).length = (it.map w).length := by rw [zp.1]
    simpa using h1.symm
  have hT : triples xs work one tr.idx = (i0, one, p0) :: tri p0 it bs := by rw [hidx]; rfl
  set T := triples xs work one tr.idx with hTdef
  have hsplit := idx_cat tr pv.2.2.1 pv.1 pv.2.1
  have hTm : T.map (·.1) = tr.topL ++ (tr.midL ++ tr.lowL) := by
    rw [← hsplit, hT, hidx, List.map_cons, tri_fst p0 it bs hlenbs]
  set Tt := T.take tr.topL.length with hTt
  set Tm := (T.drop tr.topL.length).take tr.midL.length with hTmm
  set Tl := T.drop (tr.topL.length + tr.midL.length) with hTl
  have mt : Tt.map (·.1) = tr.topL := by
    rw [hTt, List.map_take, hTm, List.take_left' rfl]
  have mm : Tm.map (·.1) = tr.midL := by
    rw [hTmm, List.map_take, List.map_drop, hTm, List.drop_left' rfl, List.take_left' rfl]
  have ml : Tl.map (·.1) = tr.lowL := by
    rw [hTl, List.map_drop, hTm, ← List.drop_drop, List.drop_left' rfl, List.drop_left' rfl]
  have cat : Tt ++ (Tm ++ Tl) = T := by
    have e1 : Tm ++ Tl = T.drop tr.topL.length := by
      rw [hTl, ← List.drop_drop]; exact List.take_append_drop _ _
    rw [e1]; exact List.take_append_drop _ _
  have memT : ∀ y ∈ Tt ++ Tm ++ Tl, y ∈ T := by
    intro y hy; rw [← cat]; simpa [List.append_assoc] using hy
  -- all chain wires
  have triW : ∀ y ∈ T, (y.2.1 = one ∨ y.2.1 = p0 ∨ y.2.1 ∈ work) ∧ (y.2.2 = p0 ∨ y.2.2 ∈ work) := by
    intro y hy
    rw [hT] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · obtain ⟨h1, b, hb, h2⟩ := tri_wires _ _ _ y hy
      refine ⟨?_, Or.inr (h2 ▸ bsW b hb)⟩
      rcases h1 with e | ⟨d, hd, e⟩
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (e ▸ bsW d hd))
  have p0x : p0 ∈ xs := wmem i0 (ix.2.2.2.2 i0 (by rw [hidx]; simp))
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true, and_self] at htmp
  obtain ⟨⟨oU, oV, oF, oP⟩, ⟨UV, UF, UP⟩, ⟨VF, VP⟩, FP⟩ := htmp
  have tmp1 : ∀ q ∈ [U, V, F, pk], q ≠ one := by
    intro q hq e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with e1 | e1 | e1 | e1
    · exact oU (e.symm.trans e1)
    · exact oV (e.symm.trans e1)
    · exact oF (e.symm.trans e1)
    · exact oP (e.symm.trans e1)
  have tmpIn : ∀ q ∈ [U, V, F, pk], q ∈ [one, U, V, F, pk] := fun q hq => List.mem_cons_of_mem _ hq
  have offT : ∀ q ∈ [U, V, F, pk], ∀ y ∈ T, y.2.1 ≠ q ∧ y.2.2 ≠ q := by
    intro q hq y hy
    obtain ⟨h1, h2⟩ := triW y hy
    have a1 := (htx q (tmpIn q hq)).1
    have a2 := (htx q (tmpIn q hq)).2.1
    refine ⟨?_, ?_⟩
    · rcases h1 with e | e | e
      · rw [e]; exact (tmp1 q hq).symm
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
    · rcases h2 with e | e
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
  have gone : W ≠ one := fun e => (htx one (by simp)).2.2 e.symm
  have offG : ∀ y ∈ T, y.2.1 ≠ W ∧ y.2.2 ≠ W := by
    intro y hy
    obtain ⟨h1, h2⟩ := triW y hy
    have a1 := hWx.1
    have a2 := hWx.2
    refine ⟨?_, ?_⟩
    · rcases h1 with e | e | e
      · rw [e]; exact gone.symm
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
    · rcases h2 with e | e
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
  have endOff : ∀ (A : List (Nat × Wire × Wire)) (p q : Wire), (∀ y ∈ A, y ∈ T) → p ≠ q →
      (∀ y ∈ T, y.2.1 ≠ q ∧ y.2.2 ≠ q) → endW p A ≠ q := by
    intro A p q hA hp hy
    rcases endW_mem p A with e | ⟨y, h, e⟩
    · rw [e]; exact hp
    · rw [e]; exact (hy y (hA y h)).2
  have inTt : ∀ y ∈ Tt, y ∈ T := fun y h => List.mem_of_mem_take h
  have inTm : ∀ y ∈ Tm, y ∈ T := fun y h => List.mem_of_mem_drop (List.mem_of_mem_take h)
  have mU : U ∈ [U, V, F, pk] := by simp
  have mV : V ∈ [U, V, F, pk] := by simp
  have mF : F ∈ [U, V, F, pk] := by simp
  have mP : pk ∈ [U, V, F, pk] := by simp
  have h1l : tr.lo < 256 := by simp only [Tri.lo]; omega
  have h1h : tr.hi < 256 := by simp only [Tri.hi]; omega
  have nx (q : Wire) (hq : q ∈ [U, V, F, pk]) (i : Nat) (hi : i < 256) : w i ≠ q :=
    (tmpM q (tmpIn q hq) i hi).symm
  have eO := fun (q : Wire) (hq : q ∈ [U, V, F, pk]) =>
    endOff Tt one q inTt (tmp1 q hq).symm (offT q hq)
  have eM := fun (q : Wire) (hq : q ∈ [U, V, F, pk]) =>
    endOff Tm (endW one Tt) q inTm (eO q hq) (offT q hq)
  have hTall : ∀ y ∈ Tt ++ Tm ++ Tl, (y.2.1 ≠ U ∧ y.2.2 ≠ U) ∧ (y.2.1 ≠ V ∧ y.2.2 ≠ V) ∧
      (y.2.1 ≠ F ∧ y.2.2 ≠ F) := fun y hy =>
    ⟨offT U mU y (memT y hy), offT V mV y (memT y hy), offT F mF y (memT y hy)⟩
  have Pp : ProperProgram (preOf tr xs work one U V F) :=
    pre_proper _ _ _ _ _ _ _ _ _ _ _ _ _ _ (nx V mV _ h1l) UV (nx F mF _ h1h) VF (eM U mU) (eO V mV) hTall
  have pkNot : pk ∉ wires (preOf tr xs work one U V F) := by
    apply pre_not
    · exact ⟨tmp1 pk mP, Ne.symm UP, Ne.symm VP, Ne.symm FP, (nx pk mP _ h1l).symm, (nx pk mP _ h1h).symm,
        (eM pk mP).symm, (eO pk mP).symm⟩
    · intro y hy
      have := offT pk mP y (memT y hy)
      exact ⟨this.1.symm, this.2.symm⟩
  have gNot : W ∉ wires (preOf tr xs work one U V F) := by
    have gU : W ≠ U := fun e => (htx U (by simp)).2.2 e.symm
    have gV : W ≠ V := fun e => (htx V (by simp)).2.2 e.symm
    have gF : W ≠ F := fun e => (htx F (by simp)).2.2 e.symm
    apply pre_not
    · refine ⟨gone, gU, gV, gF, ?_, ?_, ?_, ?_⟩
      · exact fun e => hWx.1 (e ▸ wmem _ h1l)
      · exact fun e => hWx.1 (e ▸ wmem _ h1h)
      · exact (endOff Tm (endW one Tt) W inTm (endOff Tt one W inTt gone.symm offG) offG).symm
      · exact (endOff Tt one W inTt gone.symm offG).symm
    · intro y hy
      have := offG y (memT y hy)
      exact ⟨this.1.symm, this.2.symm⟩
  have wNot : ∀ q, q ∉ work → ∀ b ∈ bs, b.work ≠ q := fun q hq b hb e => hq (e ▸ bsW b hb)
  have tmpP : ∀ q ∈ [one, U, V, F, pk], q ∉ (i0 :: it).map w := fun q hq h =>
    (htx q hq).1 (Psub q (by rw [← hlP]; exact h))
  have Bt : ∀ q ∈ [one, U, V, F], B.basis q = false := by
    intro q hq
    have hq' : q ∈ [one, U, V, F, pk] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with h | h | h | h <;> simp [h]
    rw [Boff q (htx q hq').2.2, fill_outside _ _ _ q (wNot q (htx q hq').2.1), s2out q (tmpP q hq')]
    exact hto q hq
  have pivB (i : Nat) (hi : i = tr.r1 ∨ i = tr.r2) : B.basis (w i) = x.testBit i := by
    have hi256 : i < 256 := by rcases hi with rfl | rfl <;> [exact pv.1; exact pv.2.1]
    have nP : w i ∉ (i0 :: it).map w := by
      rcases hi with rfl | rfl <;> [exact x1P'; exact x2P']
    have nW : w i ∉ work := fun h => hdisj _ h (wmem i hi256)
    have ng : w i ≠ W := fun e => hWx.1 (e ▸ wmem i hi256)
    rw [Boff _ ng, fill_outside _ _ _ _ (wNot _ nW), s2out _ nP]
    exact xbit i hi256
  have hiP : tr.hi = tr.r1 ∨ tr.hi = tr.r2 := by simp only [Tri.hi]; omega
  have loP : tr.lo = tr.r1 ∨ tr.lo = tr.r2 := by simp only [Tri.lo]; omega
  have hxr1 : s.basis xr1 = x.testBit tr.r1 := xbit _ pv.1
  have hxr2 : s.basis xr2 = x.testBit tr.r2 := xbit _ pv.2.1
  let mtf : Nat → Bool := fun i => x.testBit i == tr.tgt i (x.testBit tr.r1, x.testBit tr.r2)
  have i0m : i0 ∈ tr.idx := by rw [hidx]; simp
  have itm : ∀ i ∈ it, i ∈ tr.idx := fun i hi => by rw [hidx]; simp [hi]
  have p0ne : one ≠ p0 := fun e => (htx one (by simp)).1 (e ▸ p0x)
  have p0g : p0 ≠ W := fun e => hWx.1 (e ▸ p0x)
  have p0W : p0 ∉ work := fun h => hdisj _ h p0x
  have hc0 : s2.basis p0 = mtf i0 := by
    rw [s2p0, hxr1, hxr2, xbit i0 (ix.2.2.2.2 i0 i0m)]
  have hchain : Chain (writeBit B.basis one true) mtf true (Tt ++ (Tm ++ Tl)) := by
    rw [cat, hT]
    refine ⟨by simp [writeBit], ?_, ?_⟩
    · simp only [writeBit, Function.update_apply, Ne.symm p0ne, if_false, Bool.true_and]
      rw [Boff _ p0g, fill_outside _ _ _ _ (wNot _ p0W), hc0]
    · have hmt : ∀ k (hk : k < it.length), mtf it[k] = !s2.basis (bs[k]'(hlenbs ▸ hk)).input := by
        intro k hk
        have hin : (bs[k]'(hlenbs ▸ hk)).input = w it[k] := by
          have e1 : (bs.map ZeroBit.input)[k]'(by simpa using hlenbs ▸ hk) = (bs[k]'(hlenbs ▸ hk)).input := by
            simp
          have e2 : (it.map w)[k]'(by simpa using hk) = w it[k] := by simp
          rw [← e1, ← e2]
          exact List.getElem_of_eq zp.1 _
        have im : it[k] ∈ it := List.getElem_mem _
        rw [hin, s2it _ im, hxr1, hxr2, xbit _ (ix.2.2.2.2 _ (itm _ im))]
        simp only [mtf]
        cases x.testBit it[k] <;> cases tr.tgt it[k] (x.testBit tr.r1, x.testBit tr.r2) <;> rfl
      have cf := chain_fill mtf p0 it bs s2.basis (true && mtf i0) hlenbs chnd chz (by simpa using hc0) hmt
      apply chain_congr _ _ _ _ _ _ cf
      intro y hy
      have hyw := tri_wires _ _ _ y hy
      have side : ∀ q, (q = p0 ∨ ∃ b ∈ bs, q = b.work) →
          fill p0 bs s2.basis q = writeBit B.basis one true q := by
        intro q hq
        have qx : q ∈ xs ∨ q ∈ work := by
          rcases hq with e | ⟨b, hb, e⟩
          · exact Or.inl (e ▸ p0x)
          · exact Or.inr (e ▸ bsW b hb)
        have ng : q ≠ W := by
          intro e
          rcases qx with h | h
          · exact hWx.1 (e ▸ h)
          · exact hWx.2 (e ▸ h)
        have no : q ≠ one := by
          intro e
          rcases qx with h | h
          · exact (htx one (by simp)).1 (e ▸ h)
          · exact (htx one (by simp)).2.1 (e ▸ h)
        simp only [writeBit, Function.update_apply, no, if_false]
        exact (Boff q ng).symm
      exact ⟨side _ hyw.1, side _ (Or.inr hyw.2)⟩
  have nlo (q : Wire) (hq : q ∈ [U, V, F, pk]) : w tr.lo ≠ q := nx q hq _ h1l
  have nhi (q : Wire) (hq : q ∈ [U, V, F, pk]) : w tr.hi ≠ q := nx q hq _ h1h
  have FV := F_value tr v pv.2.2.1 x hx one U V F (w tr.hi) (w tr.lo) Tt Tm Tl mt mm ml UV UF VF
    (nlo U mU) (nlo V mV) (nlo F mF) (nhi U mU) (nhi V mV) (nhi F mF)
    (eM U mU) (eM V mV) (eM F mF) (eO U mU) (eO V mV) (eO F mF) oU oV oF
    (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1l)) (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1h))
    hTall B (Bt U (by simp)) (Bt V (by simp)) (Bt F (by simp)) (Bt one (by simp))
    (pivB _ hiP) (pivB _ loP) hchain
  have gpk : W ≠ pk := fun e => (htx pk (by simp)).2.2 e.symm
  have hE : ∀ m', run (extractFast_research tr xs work one U V F pk W) m' B =
      put B pk (B.basis pk ^^ ((run (preOf tr xs work one U V F) [] B).basis W &&
        (run (preOf tr xs work one U V F) [] B).basis F)) :=
    by
      intro m'
      have htpk : ∀ z ∈ ZeroFill.correctionWires tr.A Tt, z ≠ pk := by
        apply correctionWires_off_research
        intro y hy
        exact offT pk mP y (inTt y hy)
      have hmpk : ∀ z ∈ ZeroFill.correctionWires tr.A Tm, z ≠ pk := by
        apply correctionWires_off_research
        intro y hy
        exact offT pk mP y (inTm y hy)
      have hlpk : ∀ y ∈ Tl, y.2.1 ≠ pk ∧ y.2.2 ≠ pk := by
        intro y hy
        exact offT pk mP y (memT y (by simp [hy]))
      have fast := fastExtract_semantics tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi)
        one U V F (w tr.lo) (w tr.hi) (endW (endW one Tt) Tm) (endW one Tt) Tt Tm Tl W pk
        FP VP UP (nlo pk mP) (nhi pk mP) (eM pk mP) (eO pk mP) htpk hmpk oP hlpk UV UF VF
        (nlo U mU) (nlo V mV) (nlo F mF) (nhi U mU) (nhi V mV) (nhi F mF)
        (eM U mU) (eM V mV) (eM F mF) (eO U mU) (eO V mV) (eO F mF) oU oV oF
        (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1l))
        (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1h)) hTall B m'
        (Bt U (by simp)) (Bt V (by simp)) (Bt F (by simp))
      simpa only [extractFast_research, preOf, hTt, hTmm, hTl, hTdef, hw, put] using fast
  have FVe : (run (preOf tr xs work one U V F) [] B).basis F = decide (tr.A < x) := FV
  have hRW : (run (preOf tr xs work one U V F) [] B).basis W = Gv := by
    rw [run_preserves_outside _ [] B W gNot, hBd]; simp [put, writeBit]
  simp only [FVe, hRW] at hE
  have rd (q : Wire) (hx' : q ∉ xs) (hw' : q ∉ work) : F0.basis q = s.basis q := by
    rw [hF0]
    show fill p0 bs s2.basis q = s.basis q
    rw [fill_outside _ _ _ q (wNot q hw'), s2out q (fun h => hx' (Psub q (by rw [← hlP]; exact h)))]
  have rq (q : Wire) (hq : q ∈ [y0, c, f, g, O, D, H, t1, t2, u]) : F0.basis q = s.basis q := rd q (hextx q hq).1 (hextx q hq).2
  have pkx := htx pk (by simp)
  have Wf : F0.basis W = false := by rw [rd W hWx.1 hWx.2]; exact hW0
  have Pf : F0.basis pk = s.basis pk := rd pk pkx.1 pkx.2.1
  have pkW : pk ≠ W := pkx.2.2
  obtain ⟨eC, eG, eO, eD, eH⟩ := hWe
  have cpk : c ≠ pk := fun e => hpkE (by simp [e])
  have gpk' : g ≠ pk := fun e => hpkE (by simp [e])
  have Opk : O ≠ pk := fun e => hpkE (by simp [e])
  have Dpk : D ≠ pk := fun e => hpkE (by simp [e])
  have Hpk : H ≠ pk := fun e => hpkE (by simp [e])
  have bpk0 : B.basis pk = s.basis pk := by rw [← Pf, hBd]; simp [put, writeBit, pkW]
  have hE2 : ∀ m', run (extractClear_research tr xs work one U V F pk W) m' B =
      put B pk (B.basis pk ^^ (Gv && decide (tr.A < x))) := by
    intro m'
    have hv0 : (run (preOf tr xs work one U V F) [] B).basis pk =
        ((run (preOf tr xs work one U V F) [] B).basis W &&
          (run (preOf tr xs work one U V F) [] B).basis F) := by
      rw [FVe, hRW, run_preserves_outside _ [] B pk pkNot, bpk0]
      exact hpkv
    rw [extractClear_run_research tr xs work one U V F pk W B m' gpk FP hv0]
    exact hE _
  set val := (s.basis pk ^^ (Gv && decide (tr.A < x))) with hval
  have hEf : ∀ m', run (Gc c g O D H W ++ (extractClear_research tr xs work one U V F pk W ++ Gc c g O D H W)) m' F0 =
      put F0 pk val := by
    intro m'
    rw [run_append, Gc_run c g O D H W eC eG eO eD eH, run_append]
    have e1 : (put F0 W (F0.basis W ^^ (F0.basis c ^^ F0.basis g ^^ F0.basis O ^^ F0.basis D ^^ F0.basis H))) = B := by
      rw [Wf, rq c (by simp), rq g (by simp), rq O (by simp), rq D (by simp), rq H (by simp),
        Bool.false_xor, hBd]
    rw [e1, hE2, Gc_run c g O D H W eC eG eO eD eH]
    have bpk : B.basis pk = s.basis pk := by rw [← Pf, hBd]; simp [put, writeBit, pkW]
    rw [bpk]
    apply State.extensionality
    · rw [hBd]; rfl
    funext q
    by_cases q1 : q = W
    · subst q1
      rw [hBd]
      simp [put, writeBit, Function.update_apply, Ne.symm pkW, eC, eG, eO, eD, eH, cpk, gpk', Opk, Dpk, Hpk,
        rq c (by simp), rq g (by simp), rq O (by simp), rq D (by simp), rq H (by simp), Wf, hGv]
    · by_cases q2 : q = pk
      · subst q2; rw [hBd]; simp [put, writeBit, q1, hval]
      · rw [hBd]; simp [put, writeBit, q1, q2]
  have hpk1 : pk ∉ (p0 :: bs.flatMap ZeroBit.wires) := by
    intro h
    rcases List.mem_cons.mp h with e | h
    · exact pkx.1 (e ▸ p0x)
    · obtain ⟨b, hb, hw'⟩ := List.mem_flatMap.mp h
      simp only [ZeroBit.wires, List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with e | e
      · obtain ⟨i, hi, e2⟩ := List.mem_map.mp (bsI b hb)
        exact pkx.1 (e ▸ e2 ▸ wmem i (ix.2.2.2.2 i (itm i hi)))
      · exact pkx.2.1 (e ▸ bsW b hb)
  have hpk2 : pk ∉ wires ([Instr.X p0] ++ tr.remapList xr1 xr2 w (i0 :: it)) := by
    rw [wires_append]
    simp only [Finset.mem_union, not_or]
    refine ⟨?_, remapList_not tr xr1 xr2 w _ pk (nx pk mP _ pv.1).symm (nx pk mP _ pv.2.1).symm (tmpP pk (by simp))⟩
    have np : pk ≠ p0 := (nx pk mP i0 (ix.2.2.2.2 i0 i0m)).symm
    simp [wires, Instr.wires, np]
  have hpk3 : pk ∉ wires (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u (lastWire p0 bs)) := by
    intro h
    have hm := OutputOpt.otailL_support tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u _ h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with e1 | e1 | e1 | hm
    · apply hpk1
      rcases lastWire_mem p0 bs with e2 | ⟨b, hb, e2⟩
      · rw [e1, e2]; exact List.mem_cons_self
      · rw [e1, e2]
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩)
    · exact (nx pk mP _ pv.1) e1.symm
    · exact (nx pk mP _ pv.2.1) e1.symm
    · exact hpkE (by simpa using hm)
  rw [hF0] at hEf
  have M := main _ pk val hEf hpk1 hpk2 hpk3 m
  have hprog : OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([Instr.X (w i0)] ++
      (zeroWith (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) (zeroPorts (it.map w) work) ++
      ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [OutputOpt.oclassifier, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  have hprogF : oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([Instr.X (w i0)] ++
      (zeroWith (fun h => (Gc c g O D H W ++ (extractClear_research tr xs work one U V F pk W ++ Gc c g O D H W)) ++
          OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h)
        (w i0) (zeroPorts (it.map w) work) ++
      ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [oclassifierF, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  rw [hprogF, hprog]
  exact M

theorem pf_sum (tr : Tri) (yc n r1 r2 y0 : Bool) :
    ((predFlags tr yc n r1 r2 y0).1 ^^ (predFlags tr yc n r1 r2 y0).2.1 ^^
      (predFlags tr yc n r1 r2 y0).2.2.1 ^^ (predFlags tr yc n r1 r2 y0).2.2.2) = n := by
  unfold predFlags
  split_ifs
  · dsimp only
    generalize (r1 == tr.B.testBit tr.r1) = a
    generalize (r2 == tr.S.testBit tr.r2) = b
    generalize (y0 == yc) = c
    cases n <;> cases a <;> cases b <;> cases c <;> rfl
  · dsimp only
    generalize (r1 == tr.S.testBit tr.r1) = a
    generalize (r2 == tr.B.testBit tr.r2) = b
    generalize (y0 == yc) = c
    cases n <;> cases a <;> cases b <;> cases c <;> rfl

/-- The pool site that carries the generic flag while the wrap flag is cleared. -/
def wW (L : ControlledPointLayout) : Wire := L.core.poolWire 723

theorem out_flag_wires :
    [layout.dialogPool.getD 253 0, layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0,
      layout.point.finite, FlagEntry.pkW layout].Nodup ∧
    (∀ q ∈ [layout.dialogPool.getD 253 0, layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0,
      layout.point.finite, FlagEntry.pkW layout],
      q ∉ layout.point.x ∧ q ∉ layout.dialogPool.take 253 ∧ q ≠ wW layout) ∧
    (wW layout ∉ layout.point.x ∧ wW layout ∉ layout.dialogPool.take 253) ∧
    (layout.control ≠ wW layout ∧ layout.genericSelect ≠ wW layout ∧ parkWire layout ≠ wW layout ∧
      layout.doubleSelect ≠ wW layout ∧ layout.core.equalNegY ≠ wW layout) ∧
    FlagEntry.pkW layout ∉ [yLow layout, layout.control, layout.point.finite, layout.genericSelect,
      parkWire layout, layout.doubleSelect, layout.core.equalNegY, layout.dialogPool.getD 253 0,
      layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0] ∧
    FlagEntry.pkW layout ∈ layout.dialogPool ∧ wW layout ∈ layout.dialogPool ∧
    FlagEntry.pkW layout ≠ parkWire layout ∧ wW layout ≠ parkWire layout ∧
    layout.dialogPool.getD 253 0 ≠ parkWire layout ∧ layout.dialogPool.getD 254 0 ≠ parkWire layout ∧
    layout.dialogPool.getD 255 0 ≠ parkWire layout := by
  decide +kernel

open Classical in
/-- The state the old output stage hands to its classifier. -/
theorem out_mid {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s0 : State) (hs : PointDialogBoundary layout R b (fun _ => false) s0.basis) (t : State) (m : List Bool)
    (htx : regValue layout.point.x t.basis =
      codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (hty : regValue layout.point.y t.basis =
      pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (htf : t.basis layout.point.finite = false)
    (htg : t.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (htr : ∀ q, q ∉ layout.point.x → q ∉ layout.point.y → q ≠ layout.point.finite →
      q ≠ layout.genericSelect → t.basis q = s0.basis q) :
    ∃ u : State, u = run (ocorners layout (.some hc))
        (List.drop (measurementCount (predecL (triOf (.some hc)) (yBit (.some hc)) layout.genericSelect
          layout.control (layout.point.x.getD (triOf (.some hc)).r1 0)
          (layout.point.x.getD (triOf (.some hc)).r2 0) (yLow layout) (parkWire layout)
          layout.doubleSelect layout.core.equalNegY)) m)
        (run (predecL (triOf (.some hc)) (yBit (.some hc)) layout.genericSelect
          layout.control (layout.point.x.getD (triOf (.some hc)).r1 0)
          (layout.point.x.getD (triOf (.some hc)).r2 0) (yLow layout) (parkWire layout)
          layout.doubleSelect layout.core.equalNegY) m t) ∧
      regValue layout.point.x u.basis = codeX (if b then R + .some hc else R) ∧
      (∀ q ∈ layout.dialogPool, q ≠ parkWire layout → u.basis q = false) ∧
      u.basis layout.point.finite = false ∧
      (u.basis layout.genericSelect = (u.basis layout.control &&
          oX (triOf (.some hc)) (triOf (.some hc)).S layout.point.x u.basis) ∧
        u.basis (parkWire layout) = (u.basis layout.control &&
          oX (triOf (.some hc)) (triOf (.some hc)).A layout.point.x u.basis &&
          (u.basis (yLow layout) == yBit (.some hc))) ∧
        u.basis layout.doubleSelect = (u.basis layout.control &&
          oX (triOf (.some hc)) (triOf (.some hc)).B layout.point.x u.basis &&
          (u.basis (yLow layout) == yBit ((.some hc : Point) + .some hc))) ∧
        u.basis layout.core.equalNegY = (exceptionBit (.some hc) && u.basis layout.control &&
          oX (triOf (.some hc)) (triOf (.some hc)).A layout.point.x u.basis &&
          (u.basis (yLow layout) != yBit (.some hc)))) ∧
      dialogOrdinary b R (.some hc) = (u.basis layout.control ^^ u.basis layout.genericSelect ^^
        u.basis (parkWire layout) ^^ u.basis layout.doubleSelect ^^ u.basis layout.core.equalNegY) := by
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
  rw [predecL_run (triOf C) (yBit C) _ _ _ _ _ _ _ _ hnd8 t m hz1, pfv]
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
  refine ⟨t2, rfl, c2, t2pool, t2f, hfl, ?_⟩
  have hsum := pf_sum (triOf C) (yBit C) (t.basis layout.genericSelect ^^ t.basis layout.control)
    (t.basis xr1) (t.basis xr2) (t.basis (yLow layout))
  rw [pfv, htg, hb0] at hsum
  dsimp only at hsum
  rw [t2ctl, t2g, t2p, t2d, t2h]
  revert hsum
  generalize dialogOrdinary b R C = G0
  generalize dialogInfinity b R = a0
  generalize dialogDouble b R C = a1
  generalize dialogException b R C = a2
  generalize dialogInversePoint b R C = a3
  cases G0 <;> cases b <;> cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> decide

theorem oX_congr (tr : Tri) (v : tr.Valid) (K : Nat) (xs : List Wire) (hlen : xs.length = 256)
    (st st' : BasisState) (h : ∀ q ∈ xs, st q = st' q) : oX tr K xs st = oX tr K xs st' := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  have mem (i : Nat) (hi : i < 256) : xs.getD i 0 ∈ xs := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have e1 := h _ (mem _ pv.1)
  have e2 := h _ (mem _ pv.2.1)
  unfold oX matchBit
  rw [e1, e2]
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  apply forall₂_congr
  intro i hi
  rw [h _ (mem i (ix.2.2.2.2 i hi))]

/-- The output stage with the wrap flag cleared from its chain. -/
def outNew (L : ControlledPointLayout) (C : Point) : Program :=
  predecL (triOf C) (yBit C) L.genericSelect L.control (L.point.x.getD (triOf C).r1 0)
    (L.point.x.getD (triOf C).r2 0) (yLow L) (parkWire L) L.doubleSelect L.core.equalNegY ++
  ocorners L C ++
  oclassifierF (triOf C) (yBit C) (yBit (C + C)) (exceptionBit C) L.point.x (L.dialogPool.take 253)
    (yLow L) L.control L.point.finite L.genericSelect (parkWire L) L.doubleSelect L.core.equalNegY
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0) (wW L)
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0) L.point.finite
    (FlagEntry.pkW L) ++
  FiniteFlagInterval.zrep L

theorem oclassifierFast_researchast_counts_research (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire) (hwl : work.length = 253) :
    toffoliCount (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) ≤
      toffoliCount (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) + 2 ∧
    measurementCount (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) =
      measurementCount (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) + 3 := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have ec := extractClear_counts_research tr v xs work one U V F pk W
  have gt : toffoliCount (Gc c g O D H W) = 0 := by simp [Gc, toffoliCount]
  have gm : measurementCount (Gc c g O D H W) = 0 := by simp [Gc, measurementCount]
  have zo := zeroWith_counts_general
    (OutputOpt.otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u) (if e then 3 else 5) 8
    (fun h => OutputOpt.otailL_counts tr yc y2c e _ _ y0 c f g O D H t1 t2 u h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  have zc := zeroWith_counts_general
    (fun h => (Gc c g O D H W ++ (extractClear_research tr xs work one U V F pk W ++ Gc c g O D H W)) ++
      OutputOpt.otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u h)
    (toffoliCount (extractClear_research tr xs work one U V F pk W) + (if e then 3 else 5)) 11
    (fun h => by
      have tc := OutputOpt.otailL_counts tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u h
      simp only [toffoliCount_append, measurementCount_append, ec.2.1, gt, gm]
      exact ⟨by rw [tc.1]; omega, by rw [tc.2]⟩)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zc zo
  have rt := remapList_tc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  have rm := remapList_mc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  unfold oclassifierF OutputOpt.oclassifier
  simp only [toffoliCount_append, measurementCount_append, rt, rm, zc.1, zc.2, zo.1, zo.2]
  have e9 := ec.1
  refine ⟨by omega, by simp [measurementCount]⟩

open Classical in
theorem out_pad {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s0 : State) (hs : PointDialogBoundary layout R b (fun _ => false) s0.basis) (t : State)
    (htx : regValue layout.point.x t.basis =
      codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (hty : regValue layout.point.y t.basis =
      pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (htf : t.basis layout.point.finite = false)
    (htg : t.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (htr : ∀ q, q ∉ layout.point.x → q ∉ layout.point.y → q ≠ layout.point.finite →
      q ≠ layout.genericSelect → t.basis q = s0.basis q)
    (v : Bool) (hv : v = (dialogOrdinary b R (.some hc) &&
      decide ((triOf (.some hc)).A < codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R)))) :
    FlagEntry.Pad (outNew layout (.some hc)) (OutputOpt.outStage layout (.some hc))
      (put t (FlagEntry.pkW layout) v) t
      (fun d => FlagEntry.pfx (measurementCount (OutputOpt.outStage layout (.some hc))) d ++
        d.drop (measurementCount (outNew layout (.some hc)))) := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have tv : (triOf (.some hc)).Valid := triOf_valid hc
  have pv := Tri.pivots tv
  obtain ⟨fx6n, fx6x, fx10n, fx10x, parkP, parkY, p253, p254, p255⟩ := out_fixed
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, -, -⟩ := stage_layout layout layout_widths layout_nodup
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12⟩ := out_flag_wires
  have mcC := (oclassifierFast_researchast_counts_research (triOf (.some hc)) tv (yBit (.some hc)) (yBit ((.some hc : Point) + .some hc))
    (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control
    layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect layout.core.equalNegY
    (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) (wW layout)
    (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)
    layout.point.finite (FlagEntry.pkW layout) hwl).2
  set pk := FlagEntry.pkW layout with hpk
  have pknX : pk ∉ layout.point.x := (w2 pk (by simp)).1
  have pknY : pk ∉ layout.point.y := fun h => pool_not_point pk w6 (List.mem_append_right _ h)
  have pkE := w5
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at pkE
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := pkE
  have pk0 : pk ∉ wires (predecL (triOf (.some hc)) (yBit (.some hc)) layout.genericSelect
      layout.control (layout.point.x.getD (triOf (.some hc)).r1 0)
      (layout.point.x.getD (triOf (.some hc)).r2 0) (yLow layout) (parkWire layout)
      layout.doubleSelect layout.core.equalNegY) := by
    intro h
    have hm := Finset.mem_of_subset (predecL_support _ _ _ _ _ _ _ _ _ _) h
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hm
    have x1 : layout.point.x.getD (triOf (.some hc)).r1 0 ∈ layout.point.x := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    have x2 : layout.point.x.getD (triOf (.some hc)).r2 0 ∈ layout.point.x := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    rcases hm with e | e | e | e | e | e | e | e
    · exact n4 e
    · exact n2 e
    · exact pknX (e ▸ x1)
    · exact pknX (e ▸ x2)
    · exact n1 e
    · exact n5 e
    · exact n6 e
    · exact n7 e
  have pk1 : pk ∉ wires (ocorners layout (.some hc)) := by
    intro h
    have hm := Finset.mem_of_subset (ocorners_support layout (.some hc)) h
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with (e | e) | e | e | e | e
    · exact pknX e
    · exact pknY e
    · exact n5 e
    · exact n6 e
    · exact n4 e
    · exact n7 e
  have pk2 : pk ∉ wires (OutputOpt.oclassifier (triOf (.some hc)) (yBit (.some hc)) (yBit ((.some hc : Point) + .some hc))
      (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control
      layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect layout.core.equalNegY
      (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)) := by
    intro h
    have hm := Finset.mem_of_subset (OutputOpt.oclassifier_support _ tv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hxl hwl) h
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with (e | e) | e
    · exact pknX e
    · exact (w2 pk (by simp)).2.1 e
    · rcases e with e | e | e | e | e | e | e | e | e | e
      · exact n1 e
      · exact n2 e
      · exact n3 e
      · exact n4 e
      · exact n5 e
      · exact n6 e
      · exact n7 e
      · exact n8 e
      · exact n9 e
      · exact n10 e
  apply FlagExit.Pad.of_same
  intro d
  obtain ⟨u, hu, ux, upool, uf, ufl, uG⟩ := out_mid hc b R s0 hs t d htx hty htf htg htr
  unfold outNew OutputOpt.outStage
  simp only [← hpk]
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat, LocalWireModel.run_concat,
    LocalWireModel.run_concat, LocalWireModel.run_concat, LocalWireModel.run_concat,
    run_put _ _ _ _ _ pk0, run_put _ _ _ _ _ pk1, ← hu]
  have xbit : ∀ i, i < 256 → u.basis (layout.point.x.getD i 0) =
      (codeX (if b then R + .some hc else R)).testBit i := by
    intro i hi
    rw [← ux]; exact (LocalWireModel.reg_bit layout.point.x u.basis i (by rw [hxl]; exact hi)).symm
  have hx256 : codeX (if b then R + .some hc else R) < 2^256 := by
    rw [← ux, ← hxl]; exact regValue_lt _ _
  have same (q : Wire) (hq : q ≠ pk) : (put u pk v).basis q = u.basis q := by simp [put, writeBit, hq]
  have pkx := (w2 pk (by simp)).1
  have sameX : ∀ q ∈ layout.point.x, (put u pk v).basis q = u.basis q :=
    fun q hq => same q (fun e => pkx (e ▸ hq))
  have ne (q : Wire) (hq : q ∈ [yLow layout, layout.control, layout.point.finite, layout.genericSelect,
      parkWire layout, layout.doubleSelect, layout.core.equalNegY, layout.dialogPool.getD 253 0,
      layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0]) : q ≠ pk :=
    fun e => w5 (e ▸ hq)
  have oxe (K : Nat) := oX_congr (triOf (.some hc)) tv K layout.point.x hxl _ _ sameX
  have hfl' := ufl
  have vx : (v ^^ (dialogOrdinary b R (.some hc) &&
      decide ((triOf (.some hc)).A < codeX (if b then R + .some hc else R)))) = false := by
    rw [hv]
    by_cases hG : dialogOrdinary b R (.some hc) = true
    · have hb := ((dialogOrdinary_true b R _ hC).mp hG).1
      rw [hG, hb]; simp
    · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
      rw [hG']; simp
  have ge : ((put u pk v).basis layout.control ^^ (put u pk v).basis layout.genericSelect ^^
      (put u pk v).basis (parkWire layout) ^^ (put u pk v).basis layout.doubleSelect ^^
      (put u pk v).basis layout.core.equalNegY) = dialogOrdinary b R (.some hc) := by
    rw [same _ (ne _ (by simp)), same _ (ne _ (by simp)), same _ (ne _ (by simp)),
      same _ (ne _ (by simp)), same _ (ne _ (by simp))]
    exact uG.symm
  have pv0 : (put u pk v).basis pk = v := by simp [put, writeBit]
  have run1 := fun mm => oclassifierFast_run_research (triOf (.some hc)) tv (yBit (.some hc)) (yBit ((.some hc : Point) + .some hc))
    (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control
    layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect layout.core.equalNegY
    (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) (wW layout)
    (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)
    layout.point.finite pk hxn hxl hwl hwn hdisj fx10n fx10x w1 w2 w3 w4 w5 (put u pk v)
    mm
    ⟨fun q hq => by
      have hqp : q ≠ pk := fun e => (w2 pk (by simp)).2.1 (e ▸ hq)
      rw [same q hqp]
      exact upool q (List.mem_of_mem_take hq) (fun e => (fx10x _ (by simp)).2 (e ▸ hq)),
      by rw [same _ (ne _ (by simp))]; exact uf,
      by rw [same _ (ne _ (by simp))]; exact upool _ p253 w10,
      by rw [same _ (ne _ (by simp))]; exact upool _ p254 w11,
      by rw [same _ (ne _ (by simp))]; exact upool _ p255 w12⟩
    (by
      rw [same _ (ne _ (by simp)), same _ (ne _ (by simp)), same _ (ne _ (by simp)),
        same _ (ne _ (by simp)), same _ (ne _ (by simp)), same _ (ne _ (by simp)), oxe, oxe, oxe]
      exact ufl)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · rw [same _ (ne _ (by simp))]; exact upool _ p253 w10
      · rw [same _ (ne _ (by simp))]; exact upool _ p254 w11
      · rw [same _ (ne _ (by simp))]; exact upool _ p255 w12
      · rw [same _ (ne _ (by simp))]; exact uf)
    (by
      rw [same _ (Ne.symm (w2 pk (by simp)).2.2)]
      exact upool _ w7 w9)
    _ hx256
    (fun i hi => by
      rw [sameX _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)]
      exact xbit i hi)
    (by rw [ge, pv0]; exact ECDSAAdd.Entrant.ZeroFill.xor_false_eq vx)
  have upk : u.basis pk = false := upool pk w6 w8
  have clr : ∀ (o : State), o.basis pk = false → put (put o pk v) pk false = o := by
    intro o ho
    apply State.extensionality
    · rfl
    funext q
    by_cases e : q = pk
    · subst e; simp [put, writeBit, ho]
    · simp [put, writeBit, e]
  have run2 : ∀ mm, run (oclassifierF (triOf (.some hc)) (yBit (.some hc)) (yBit ((.some hc : Point) + .some hc))
      (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control
      layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect layout.core.equalNegY
      (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) (wW layout)
      (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)
      layout.point.finite pk) mm (put u pk v) =
      run (OutputOpt.oclassifier (triOf (.some hc)) (yBit (.some hc)) (yBit ((.some hc : Point) + .some hc))
        (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control
        layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect layout.core.equalNegY
        (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)) mm u := by
    intro mm
    rw [run1 mm, ge, pv0, vx, run_put _ _ _ _ _ pk2]
    exact clr _ ((run_preserves_outside _ _ u pk pk2).trans upk)
  rw [run2]
  simp only [measurementCount_append, mcC]
  simp only [run_no_measure _ (FiniteFlagInterval.zrep_counts layout).2]

end ECDSAAdd.Entrant.OutFlag
end

section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.FlagTop2
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out FlagTop FlagExit OutFlag ParityEven ParityUniform

attribute [local irreducible] layout

def finiteN (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  stageNew L C (pkW L) ++ renameProgram (rho L) (genericN L cx cy) ++ outNew L C

def wrapperN (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteN L C cx cy)

theorem pkN_wires (cx cy : Fp) : pkW layout ∈ wires (genericN layout cx cy) := by
  have h : pkW layout ∈ wires (entryXNew layout (pkW layout) (-cx)) := by
    unfold entryXNew
    split_ifs
    · rw [wires_append]
      exact Finset.mem_union_left _ (by simp [swp, wires, Instr.wires])
    · rw [wires_append, wires_append]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (by simp [swp, wires, Instr.wires]))
  unfold genericN
  simp only [wires_append, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr h))

open Classical in
/-- The value of the parked wrap flag at the end of the generic block. -/
noncomputable def vB {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) : Bool :=
  dialogOrdinary b R (.some hc) &&
    decide ((triOf (.some hc)).A < codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R))

open Classical in
theorem blk_values {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (t1 : State) (m2 : regValue layout.point.x t1.basis = codeX R)
    (t1y : regValue layout.point.y t1.basis = pointY R)
    (m3 : t1.basis layout.point.finite = false)
    (m4 : t1.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (hE : t1.basis layout.core.equalNegY = false) (hD : t1.basis layout.doubleSelect = false)
    (hclean : regValue layout.dialogPool t1.basis = 0) (mm : List Bool) :
    (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) mm t1).phase = t1.phase ∧
    regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
      codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
    regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
      pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
    ∀ q, q ∉ layout.point.x ++ layout.point.y →
      (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (genBlockOpt layout cx cy)))) mm t1).basis q = t1.basis q := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  unfold genBlockOpt
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run (ParityStageBothInverse23.genericAll layout cx cy) x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => ParityStageBothInverse23.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run (ParityStageBothInverse23.genericAll layout cx cy) (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => ParityStageBothInverse23.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run (ParityStageBothInverse23.genericAll layout cx cy) x y x y false
        (fun base' => ParityStageBothInverse23.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem finite_padN {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    ∃ pad, Pad (finiteN layout (.some hc) cx cy) (finiteProgramOpt layout (.some hc) cx cy) s s pad := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hgen : pkW layout ≠ layout.core.generic :=
    pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  have hp := (point_holds _ _ _).mp hs.point
  have gsx := gsel_off
  have pre : ∀ (t1 : State), (∀ q, q ∉ layout.point.x → q ≠ layout.point.finite → q ≠ layout.genericSelect →
      t1.basis q = s.basis q) →
      regValue layout.point.y t1.basis = pointY R ∧ t1.basis layout.core.equalNegY = false ∧
      t1.basis layout.doubleSelect = false ∧ regValue layout.dialogPool t1.basis = 0 := by
    intro t1 m5
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hp.2.2]; apply regValue_congr; intro q hq
      exact m5 q (y_not_x layout layout_nodup q hq)
        (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
    · obtain ⟨a, b', c, d'⟩ := out_off layout.core.equalNegY (by simp)
      rw [m5 _ a c d']; exact hs.flags _ (by simp [flags_list])
    · obtain ⟨a, b', c, d'⟩ := out_off layout.doubleSelect (by simp)
      rw [m5 _ a c d']; exact hs.flags _ (by simp [flags_list])
    · apply (regValue_zero _ _).mpr
      intro q hq
      obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
      rw [m5 q (fun h => pool_not_point q hq (List.mem_append_left _ h)) f1 g1]
      exact (regValue_zero _ _).mp hs.clean q hq
  have key : ∀ d, PadP (renameProgram (rho layout) (genericN layout cx cy))
      (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (genBlockOpt layout cx cy))))
      (run (stageNew layout (.some hc) (pkW layout)) d s) (run (stage layout (.some hc)) d s)
      (padG layout cx cy) (pkW layout) (vB hc b R) := by
    intro d
    obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s d hs
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := pk_stage
    rw [stageNew_run layout layout_widths layout_nodup hc b R s d hs (pkW layout) p1 p2 p3 p4 p5 p6 p7 p8]
    generalize ht1 : run (stage layout (.some hc)) d s = t1 at m1 m2 m3 m4 m5 ⊢
    obtain ⟨t1y, hE, hD, hclean⟩ := pre t1 m5
    rw [m4]
    unfold genBlockOpt
    rw [ren_eq]
    have wrap : ∀ (X Y : Fp), X.val = codeX R → Y.val = pointY R →
        (PointDialogValues layout X Y (dialogOrdinary b R (.some hc))
            (pullState (rho layout) t1).basis (pullState (rho layout) t1).basis →
          PadP (genericN layout cx cy) (ParityStageBothInverse23.genericAll layout cx cy)
            (put (pullState (rho layout) t1) (pkW layout)
              (if dialogOrdinary b R (.some hc) then
                decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))
            (pullState (rho layout) t1) (padG layout cx cy) (pkW layout) (vB hc b R)) →
        PadP (renameProgram (rho layout) (genericN layout cx cy))
          (renameProgram (rho layout) (ParityStageBothInverse23.genericAll layout cx cy))
          (put t1 (pkW layout) (dialogOrdinary b R (.some hc) &&
            decide ((triOf (.some hc)).A < codeX R))) t1 (padG layout cx cy) (pkW layout) (vB hc b R) := by
      intro X Y hXv hYv h
      have pvv := pulled_values t1 X Y (dialogOrdinary b R (.some hc)) (m2.trans hXv.symm)
        (t1y.trans hYv.symm) m3 m4 hE hD hclean
      rw [flag_eq hc b R X hXv]
      apply PadP.rename (rho layout) rho_injective (pkW layout) rho_pk _ _ (pkN_wires cx cy)
      exact h ⟨pvv.1, pvv.2.1, pvv.2.2.1, pvv.2.2.2, fun _ _ => rfl⟩
    by_cases hG : dialogOrdinary b R (.some hc) = true
    · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
      cases R with
      | zero => exact absurd rfl h0
      | @some x y hr =>
        have den := dialog_denominators_ne_zero hr hc h1 h2 h3
        apply wrap x y rfl rfl
        intro hv
        have ve : vB hc b (.some hr) = decide (cx.val < (genericX x y cx cy).val) := by
          unfold vB
          rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1, Bool.true_and]
          rfl
        rw [ve]
        rw [hG] at hv
        exact generic_padp_true layout layout_widths layout_nodup x y cx cy _ _ hv
          (by rw [hv.generic, hG]) den.1 den.2 hgen
    · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
      have ve : vB hc b R = false := by unfold vB; rw [hG']; rfl
      cases R with
      | zero =>
        apply wrap (FiniteFlagInterval.sentinel : Fp) 0 FiniteFlagInterval.sentinel_val rfl
        intro hv
        rw [ve]
        rw [hG'] at hv
        exact generic_padp_false layout layout_widths layout_nodup _ 0 cx cy _ _ hv
          (by rw [hv.generic, hG']) FiniteFlagInterval.sentinel_ne_zero hgen
      | @some x y hr =>
        apply wrap x y rfl rfl
        intro hv
        rw [ve]
        rw [hG'] at hv
        exact generic_padp_false layout layout_widths layout_nodup x y cx cy _ _ hv
          (by rw [hv.generic, hG']) (curve_x_ne_zero hr) hgen
  have h1 := PadP.prefix_general _ _ _ _ s s _ _ _ key
  unfold finiteN finiteProgramOpt
  refine ⟨_, Pad.ofP (pad2 := fun d => pfx (measurementCount (OutputOpt.outStage layout (.some hc))) d ++ d.drop (measurementCount (outNew layout (.some hc)))) (B' := outNew layout (.some hc)) (B := OutputOpt.outStage layout (.some hc))
    h1 (fun d => ?_)⟩
  rw [run_append]
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s
    (List.take (measurementCount (stage layout (.some hc))) _) hs
  generalize run (stage layout (.some hc)) (List.take (measurementCount (stage layout (.some hc))) _) s = t1
    at m1 m2 m3 m4 m5 ⊢
  obtain ⟨t1y, hE, hD, hclean⟩ := pre t1 m5
  obtain ⟨k1, k2, k3, k4⟩ := blk_values hc b R t1 m2 t1y m3 m4 hE hD hclean
    (List.drop (measurementCount (stage layout (.some hc))) _)
  generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
    (genBlockOpt layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) _) t1 = t2
    at k1 k2 k3 k4 ⊢
  have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
  have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
    simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
  exact out_pad hc b R s hs t2 k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
    (fun q hx hy hf hg => by
      rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    _ rfl

open Classical in
theorem finite_run_N {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteN layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteN layout (.some hc) cx cy) m s).basis := by
  obtain ⟨pad, h⟩ := finite_padN hc b R s hs
  rw [h.run_eq m]
  exact finite_run hc b R s (pad m) hs

open Classical in
theorem wrapper_spec_N {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapperN layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite_run_N hc b R s m hs
  unfold wrapperN
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h

end ECDSAAdd.Entrant.FlagTop2
end

end

section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.OutFlag
open Arithmetic Challenge RecordedQuantum MeasuredCodec5 Baselines InputSentinel Secp256k1 ControlledPointLayout
  ZeroFill OutputOpt ParityEven

theorem zeroWith_pre_physical (T : Wire → Program) (E : Program) (hE : GatePhysical E) :
    ∀ (c : Wire) (bs : List ZeroBit), GatePhysical (zeroWith T c bs) →
      GatePhysical (zeroWith (fun h => E ++ T h) c bs) := by
  intro c bs
  induction bs generalizing c with
  | nil =>
    intro h
    simp only [zeroWith, gatePhysical_append] at h ⊢
    exact ⟨hE, h⟩
  | cons b bs ih =>
    intro h
    simp only [zeroWith, gatePhysical_append] at h ⊢
    exact ⟨⟨h.1.1, ih b.work h.1.2⟩, h.2⟩

theorem zeroWith_pre_wires (T : Wire → Program) (E : Program) :
    ∀ (c : Wire) (bs : List ZeroBit),
      wires (zeroWith (fun h => E ++ T h) c bs) ⊆ wires (zeroWith T c bs) ∪ wires E := by
  intro c bs
  induction bs generalizing c with
  | nil =>
    simp only [zeroWith, wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    tauto
  | cons b bs ih =>
    simp only [zeroWith, wires_append]
    intro q hq
    have i := @ih b.work q
    simp only [Finset.mem_union] at hq i ⊢
    tauto

theorem Gc_physical (c g O D H W : Wire) (h1 : c ≠ W) (h2 : g ≠ W) (h3 : O ≠ W) (h4 : D ≠ W) (h5 : H ≠ W) :
    GatePhysical (Gc c g O D H W) := by
  simp [Gc, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, h1, h2, h3, h4, h5]

theorem oclassifierFast_researchast_physical_research (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire) (hlen : xs.length = 256)
    (hU : U ∉ xs ∧ U ∉ work ∧ U ≠ one) (hV : V ∉ xs ∧ V ∉ work ∧ V ≠ one)
    (hF : F ∉ xs ∧ F ∉ work ∧ F ≠ one) (UV : U ≠ V) (VF : V ≠ F) (Fp : F ≠ pk) (gp : W ≠ pk)
    (h1 : c ≠ W) (h2 : g ≠ W) (h3 : O ≠ W) (h4 : D ≠ W) (h5 : H ≠ W)
    (old : GatePhysical (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u)) :
    GatePhysical (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) := by
  have hE := extractClear_physical_research tr v xs work one U V F pk W hlen hU hV hF UV VF Fp gp
  have hG := Gc_physical c g O D H W h1 h2 h3 h4 h5
  have hE3 : GatePhysical (Gc c g O D H W ++ (extractClear_research tr xs work one U V F pk W ++ Gc c g O D H W)) := by
    simp only [gatePhysical_append]
    exact ⟨hG, hE, hG⟩
  unfold OutputOpt.oclassifier at old
  simp only [gatePhysical_append] at old
  unfold oclassifierF
  simp only [gatePhysical_append]
  exact ⟨old.1, old.2.1, zeroWith_pre_physical _ _ hE3 _ _ old.2.2.1, old.2.2.2⟩

theorem oclassifierFast_researchast_wires_research (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire) (hlen : xs.length = 256) (Wf : Finset Wire)
    (hc : wires (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) ⊆ Wf)
    (hx : ∀ q ∈ xs, q ∈ Wf) (hw : ∀ q ∈ work, q ∈ Wf)
    (h1 : one ∈ Wf) (h2 : U ∈ Wf) (h3 : V ∈ Wf) (h4 : F ∈ Wf) (h5 : pk ∈ Wf) (h6 : W ∈ Wf)
    (m1 : c ∈ Wf) (m2 : g ∈ Wf) (m3 : O ∈ Wf) (m4 : D ∈ Wf) (m5 : H ∈ Wf) :
    wires (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) ⊆ Wf := by
  have E := extractClear_sub_research tr v xs work one U V F pk W hlen Wf hx hw h1 h2 h3 h4 h5 h6
  have G : wires (Gc c g O D H W) ⊆ Wf := by
    simp [Gc, wires, Instr.wires, Finset.insert_subset_iff, m1, m2, m3, m4, m5, h6]
  have E3 : wires (Gc c g O D H W ++ (extractClear_research tr xs work one U V F pk W ++ Gc c g O D H W)) ⊆ Wf := by
    simp only [wires_append, Finset.union_subset_iff]
    exact ⟨G, E, G⟩
  unfold OutputOpt.oclassifier at hc
  simp only [wires_append, Finset.union_subset_iff] at hc
  unfold oclassifierF
  simp only [wires_append, Finset.union_subset_iff]
  exact ⟨hc.1, hc.2.1, (zeroWith_pre_wires _ _ _ _).trans (Finset.union_subset hc.2.2.1 E3), hc.2.2.2⟩

theorem oclassifierF_slots (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire) :
    Challenge.gateSlots (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) ≤
      Challenge.gateSlots (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) + 1046 := by
  have ec := extractClear_counts_research tr v xs work one U V F pk W
  have gs : Challenge.gateSlots (Gc c g O D H W) = 5 := by
    simp [Gc, Challenge.gateSlots, Challenge.instructionSlots]
  have zo := InputSentinel.zeroWith_slots
    (OutputOpt.otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
    (Challenge.gateSlots (OutputOpt.otail tr yc y2c e))
    (fun h => OutputOpt.otailL_slots tr yc y2c e _ _ y0 c f g O D H t1 t2 u h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  have zc := InputSentinel.zeroWith_slots
    (fun h => (Gc c g O D H W ++ (extractClear_research tr xs work one U V F pk W ++ Gc c g O D H W)) ++
      OutputOpt.otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u h)
    (5 + (Challenge.gateSlots (extractClear_research tr xs work one U V F pk W) + 5) +
      Challenge.gateSlots (OutputOpt.otail tr yc y2c e))
    (fun h => by
      simp only [Challenge.gateSlots_append, gs]
      rw [OutputOpt.otailL_slots])
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  have e3 := ec.2.2
  unfold oclassifierF OutputOpt.oclassifier
  simp only [Challenge.gateSlots_append, zc, zo]
  omega

theorem predec_mem (tr : Tri) (yc : Bool) (i : Nat) (hi : i = 0 ∨ i = 1 ∨ i = 5 ∨ i = 6 ∨ i = 7) :
    i ∈ wires (predecT tr yc) := by
  unfold predecT
  split_ifs <;>
  · generalize tr.B.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.S.testBit tr.r1 = a'; generalize tr.B.testBit tr.r2 = b'
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    cases a <;> cases b <;> cases a' <;> cases b' <;> cases yc <;> decide

theorem predecL_mem (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire) :
    g ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) ∧ c ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) ∧
    O ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) ∧ D ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) ∧
    H ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) := by
  have key : ∀ i, (i = 0 ∨ i = 1 ∨ i = 5 ∨ i = 6 ∨ i = 7) →
      ([g, c, xr1, xr2, y0, O, D, H] : List Wire).getD i 0 ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) := by
    intro i hi
    unfold predecL
    rw [renameProgram_support]
    refine Finset.mem_image.mpr ⟨i, predec_mem tr yc i hi, ?_⟩
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [LocalWireModel.label]
  exact ⟨key 0 (by simp), key 1 (by simp), key 5 (by simp), key 6 (by simp), key 7 (by simp)⟩

theorem outNew_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (outNew layout (.some hc)) ≤ toffoliCount (OutputOpt.outStage layout (.some hc)) + 2 ∧
    measurementCount (outNew layout (.some hc)) = measurementCount (OutputOpt.outStage layout (.some hc)) + 3 ∧
    Challenge.gateSlots (outNew layout (.some hc)) ≤
      Challenge.gateSlots (OutputOpt.outStage layout (.some hc)) + 1046 := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, -, -⟩ := stage_layout layout layout_widths layout_nodup
  have c := oclassifierFast_researchast_counts_research (triOf (.some hc)) (triOf_valid hc) (yBit (.some hc))
    (yBit ((.some hc : Point) + .some hc)) (exceptionBit (.some hc)) layout.point.x
    (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite layout.genericSelect
    (parkWire layout) layout.doubleSelect layout.core.equalNegY (layout.dialogPool.getD 253 0)
    (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) (wW layout)
    (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)
    layout.point.finite (FlagEntry.pkW layout) hwl
  have s := oclassifierF_slots (triOf (.some hc)) (triOf_valid hc) (yBit (.some hc))
    (yBit ((.some hc : Point) + .some hc)) (exceptionBit (.some hc)) layout.point.x
    (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite layout.genericSelect
    (parkWire layout) layout.doubleSelect layout.core.equalNegY (layout.dialogPool.getD 253 0)
    (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) (wW layout)
    (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)
    layout.point.finite (FlagEntry.pkW layout)
  unfold outNew OutputOpt.outStage
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
  omega

theorem outNew_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (outNew layout (.some hc)) := by
  have old := OutputOpt.outStage_physical hc
  unfold OutputOpt.outStage at old
  simp only [gatePhysical_append] at old
  obtain ⟨⟨⟨A, B⟩, D⟩, E⟩ := old
  obtain ⟨hnd, hmem, -, ⟨c1, c2, c3, c4, c5⟩, -⟩ := out_flag_wires
  obtain ⟨-, hxl, -⟩ := stage_layout layout layout_widths layout_nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true, and_self] at hnd
  obtain ⟨⟨a12, a13, a14, -⟩, ⟨a23, -, -⟩, ⟨a34, -⟩, a45⟩ := hnd
  unfold outNew
  simp only [gatePhysical_append]
  refine ⟨⟨⟨A, B⟩, ?_⟩, E⟩
  exact oclassifierFast_researchast_physical_research _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hxl
    ⟨(hmem _ (by simp)).1, (hmem _ (by simp)).2.1, Ne.symm a12⟩
    ⟨(hmem _ (by simp)).1, (hmem _ (by simp)).2.1, Ne.symm a13⟩
    ⟨(hmem _ (by simp)).1, (hmem _ (by simp)).2.1, Ne.symm a14⟩ a23 a34 a45
    (Ne.symm (hmem _ (by simp)).2.2) c1 c2 c3 c4 c5 D

end ECDSAAdd.Entrant.OutFlag
end

section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.FlagTop2
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out FlagTop FlagExit OutFlag ZeroFill ParityEven
  ParityUniform E1Merge NativeFirstDirect MappedCompressed ParityXEntry

attribute [local irreducible] layout

theorem wW_eq (L : ControlledPointLayout) : wW L = E1QubitPlacement.pmapR L (base 721) := by
  unfold E1QubitPlacement.pmapR E1QubitPlacement.pmap
  rw [E1QubitPlacement.rho_base, E1QubitPlacement.sig_base]
  rfl

theorem tailX_721 (k : Nat) : base 721 ∈ wires (tailX base (base 2400) k) := by
  simp only [tailX, prodPart, wires_append, Finset.mem_union]
  simp [wires, Instr.wires]

theorem evenTail_721 (k : Nat) : base 721 ∈ wires (evenTail k) := by
  simp only [evenTail, wires_append, Finset.mem_union]
  simp [wires, Instr.wires]

theorem entryX_W (L : ControlledPointLayout) (k : Fp) : wW L ∈ wires (entryXAll L k) := by
  rw [wW_eq L]
  unfold entryXAll
  rw [renameProgram_support]
  apply Finset.mem_image_of_mem
  unfold mergedAll
  split_ifs with he
  · unfold mergedOdd
    rw [if_pos he, wires_append]
    exact Finset.mem_union_right _ (tailX_721 k.val)
  · unfold mergedEven
    rw [wires_append]
    exact Finset.mem_union_right _ (evenTail_721 k.val)

theorem generic_W (cx cy : Fp) : wW layout ∈ wires (ParityStageBothInverse23.genericAll layout cx cy) := by
  have h := entryX_W layout (-cx)
  simp only [ParityStageBothInverse23.genericAll, ParityStageBothInverse23.entryStageAll, wires_append,
    Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr h))

theorem W_pool : wW layout ∈ layout.dialogPool :=
  Square5Placement.pool_member layout layout_widths 723 (by omega)

theorem W_ne_pool (i : Nat) (hi : i < 2613) (hne : i ≠ 723) : wW layout ≠ layout.core.poolWire i :=
  fun e => hne (pool_inj layout layout_widths layout_nodup i 723 hi (by omega) e.symm)

theorem W_flag (b : Wire) (hb : b ∈ layout.inPlaceFlags) : wW layout ≠ b :=
  fun e => pool_not_flag _ W_pool (e ▸ hb)

theorem rho_W : rho layout (wW layout) = wW layout := by
  apply rho_fix
  · exact (out_pool_off _ W_pool).1
  · exact W_ne_pool 1400 (by omega) (by omega)
  · exact W_ne_pool 684 (by omega) (by omega)
  · exact W_ne_pool 717 (by omega) (by omega)
  · exact W_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact W_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact W_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact W_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact W_ne_pool 1540 (by omega) (by omega)

theorem genericN_wires (L : ControlledPointLayout) (cx cy : Fp) :
    wires (genericN L cx cy) ⊆ wires (genericNew L cx cy) := by
  simp only [genericN, genericNew, secondStageN, ParityStageBothInverse23.secondStageAll, wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _)
      (ParityXExitInverse23Kernel.restXXN_sub L _)) (Finset.Subset.refl _))

theorem genericN_counts (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (genericN L cx cy) + 254 = toffoliCount (genericNew L cx cy) ∧
    measurementCount (genericN L cx cy) ≤ measurementCount (genericNew L cx cy) ∧
    Challenge.gateSlots (genericN L cx cy) ≤ Challenge.gateSlots (genericNew L cx cy) + 2 := by
  have r := ParityXExitInverse23Kernel.restXXN_counts L cx.val
  simp only [genericN, genericNew, secondStageN, ParityStageBothInverse23.secondStageAll,
    toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
  omega

theorem genericN_physical (cx cy : Fp) : GatePhysical (genericN layout cx cy) := by
  have old : GatePhysical (ParityStageBothInverse23.genericRef layout cx cy) := by
    rw [reference_eq]
    exact Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p0 := ParityStageBothInverse23.generic_physical layout layout_widths layout_nodup cx cy old
  simp only [ParityStageBothInverse23.genericAll, ParityStageBothInverse23.entryStageAll,
    ParityStageBothInverse23.secondStageAll, gatePhysical_append] at p0
  simp only [genericN, secondStageN, gatePhysical_append]
  exact ⟨⟨⟨p0.1.1.1, entryXNew_physical layout layout_widths layout_nodup _ _
      (pk_ne_flag layout layout_widths layout_nodup)⟩, p0.1.2⟩,
    ⟨p0.2.1.1, ParityXExitInverse23Kernel.restXXN_physical layout layout_widths layout_nodup _⟩, p0.2.2⟩

theorem outNew_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (outNew layout (.some hc)) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
  have mem := stage_wires_mem hc
  have hstage : wires (stage layout (.some hc)) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    intro q hq
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inl (Or.inl hq))
  have hOut : wires (OutputOpt.outStage layout (.some hc)) ⊆
      ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    intro q hq
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inr hq)
  have pkIn : pkW layout ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    refine Or.inr (Or.inl (Or.inr ?_))
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨_, genericNew_wires layout cx cy (pk_wires cx cy), rho_pk⟩
  have wIn : wW layout ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    refine Or.inr (Or.inl (Or.inr ?_))
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨_, generic_W cx cy, rho_W⟩
  have mx : ∀ q ∈ layout.point.x, q ∈ ioSet := by
    intro q hq
    simp [ioSet, PointAddLayout.pointWires, hq]
  have mf : layout.point.finite ∈ ioSet := by simp [ioSet, PointAddLayout.pointWires]
  have tk : ∀ q ∈ layout.dialogPool.take 253, q ∈ layout.dialogPool.take 256 := by
    intro q hq
    have hpl := dialogPool_length layout layout_widths
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hq
    simp only [List.length_take] at hi
    rw [List.getElem_take] at e
    rw [← e]
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  have pool256 : ∀ q ∈ layout.dialogPool.take 256,
      q ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) :=
    fun q hq => hstage (mem.1 q hq)
  have hO := hOut
  unfold OutputOpt.outStage at hO
  simp only [wires_append, Finset.union_subset_iff] at hO
  obtain ⟨⟨⟨hA, hB⟩, hD⟩, hE⟩ := hO
  obtain ⟨n1, n2, n3, n4, n5⟩ := predecL_mem (triOf (.some hc)) (yBit (.some hc)) layout.genericSelect
    layout.control (layout.point.x.getD (triOf (.some hc)).r1 0) (layout.point.x.getD (triOf (.some hc)).r2 0)
    (yLow layout) (parkWire layout) layout.doubleSelect layout.core.equalNegY
  unfold outNew
  simp only [wires_append, Finset.union_subset_iff]
  refine ⟨⟨⟨hA, hB⟩, ?_⟩, hE⟩
  exact oclassifierFast_researchast_wires_research _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    layout_widths.inputX _ hD
    (fun q hq => Finset.mem_union_left _ (mx q hq)) (fun q hq => pool256 q (tk q hq))
    (pool256 _ (pool_take_mem 253 (by omega))) (pool256 _ (pool_take_mem 254 (by omega)))
    (pool256 _ (pool_take_mem 255 (by omega))) (Finset.mem_union_left _ mf) pkIn wIn
    (hA n2) (hA n1) (hA n3) (hA n4) (hA n5)

theorem finiteN_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (finiteN layout (.some hc) cx cy) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
  have s := stageNew_wires (cx := cx) (cy := cy) hc
  have o := outNew_wires (cx := cx) (cy := cy) hc
  unfold finiteN
  rw [wires_append, wires_append]
  refine Finset.union_subset (Finset.union_subset s ?_) o
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  rw [finiteOpt_wires hc]
  simp only [Finset.mem_union]
  refine Or.inr (Or.inl (Or.inr ?_))
  rw [renameProgram_support]
  exact Finset.mem_image_of_mem _ (genericNew_wires layout cx cy (genericN_wires layout cx cy ha))

theorem wrapperN_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperN layout (.some hc) cx cy) ⊆ ioSet ∪ wires (wrapperOpt layout (.some hc) cx cy) := by
  have k := finiteN_wires (cx := cx) (cy := cy) hc
  have hw := layout_widths
  have fixIO : ∀ q ∈ ioSet, Wrapper5.U layout q = q := by
    intro q hq
    have hq' := List.mem_toFinset.mp hq
    have np := io_not_pool q hq'
    have n1 : q ≠ layout.core.poolWire 684 := by
      intro e; apply np; rw [e]; exact Square5Placement.pool_member layout hw 684 (by omega)
    have n2 : q ≠ layout.core.poolWire 717 := by
      intro e; apply np; rw [e]; exact Square5Placement.pool_member layout hw 717 (by omega)
    rw [U_apply, if_neg n1, if_neg n2]
  unfold wrapperN wrapperOpt
  rw [renameProgram_support, renameProgram_support]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (k ha) with h | h
  · rw [fixIO a h]; exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

theorem support_used_N {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperN layout (.some hc) cx cy) ⊆ layout.dialogUsedWires.toFinset := by
  refine (wrapperN_wires hc).trans (Finset.union_subset ?_ (support_used hc))
  intro q hq
  apply List.mem_toFinset.mpr
  unfold ControlledPointLayout.dialogUsedWires
  simp only [List.mem_append]
  have := List.mem_toFinset.mp hq
  simp only [List.mem_append] at this
  tauto

theorem wrapper_physical_N {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapperN layout (.some hc) cx cy) := by
  unfold wrapperN
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteN, gatePhysical_append]
  exact ⟨⟨stageNew_physical hc, gatePhysical_rename _ rho_injective _ (genericN_physical cx cy)⟩,
    outNew_physical hc⟩

theorem wrapperN_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperN layout (.some hc) cx cy) + 504 ≤
      toffoliCount (wrapperOpt layout (.some hc) cx cy) ∧
    measurementCount (wrapperN layout (.some hc) cx cy) ≤
      measurementCount (wrapperOpt layout (.some hc) cx cy) + 5 ∧
    Challenge.gateSlots (wrapperN layout (.some hc) cx cy) ≤
      Challenge.gateSlots (wrapperOpt layout (.some hc) cx cy) + 5707 := by
  have gN := genericN_counts layout cx cy
  have g := genericNew_counts layout cx cy
  have s := stageNew_counts hc (pkW layout)
  have o := stage_counts hc
  have u := outNew_counts hc
  simp only [wrapperN, wrapperOpt, finiteN, finiteProgramOpt, genBlockOpt,
    toffoliCount_append, measurementCount_append, Challenge.gateSlots_append,
    (renameProgram_counts _ _).1, (renameProgram_counts _ _).2, rename_gateSlots]
  omega

open Classical in
theorem full_spec_N {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperN layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz:regValue layout.work s.basis=0:=hs.2
  have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
  have a:=wrapper_spec_N hc b R s m hi
  have old:=InputSentinel530.wrapper530_spec hc b R s m hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used_N hc) (InputSentinel530.support_used530 hc)
    s m _ b a.2 old.2 (a.1.trans old.1.symm)]
  exact InputSentinel530.full_spec530 hc b R s m hs

def programB (C : Point) : Program :=
  match C with
  | .zero=>[]
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperN layout C cx cy

def entryB : Challenge.Entry := fun C=>normalizeProgram (programB C)
def boundsB : Challenge.Bounds := ⟨2149777,1498375,1587,50256955⟩

theorem program_correct_B (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programB C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programB,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec_N hc b R) (support_used_N hc)

theorem program_toffoli_B (C : Point) : toffoliCount (programB C)≤2149777 := by
  cases C with
  | zero=>simp [programB,toffoliCount]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_toffoli (.some hc)
    have delta:=(wrapperN_metrics hc).1
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤_ at old
    change toffoliCount (wrapperN layout (.some hc) cx cy)≤2149777
    omega

theorem program_measurements_B (C : Point) : measurementCount (programB C)≤1498375 := by
  cases C with
  | zero=>simp [programB,measurementCount]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_measurements (.some hc)
    have delta:=(wrapperN_metrics hc).2.1
    change measurementCount (wrapperOpt layout (.some hc) cx cy)≤1498370 at old
    change measurementCount (wrapperN layout (.some hc) cx cy)≤1498375
    omega

theorem program_qubits_B (C : Point) : qubits (programB C)≤1587 := by
  cases C with
  | zero=>change qubits []≤1587;rw [qubits_empty];decide
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_qubits (.some hc)
    change qubits (wrapperOpt layout (.some hc) cx cy)≤1587 at old
    change qubits (wrapperN layout (.some hc) cx cy)≤1587
    apply le_trans (Finset.card_le_card ?_) old
    intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact Finset.mem_union_left _ h
    · rcases Finset.mem_union.mp (wrapperN_wires hc h) with e | e
      · exact Finset.mem_union_left _ (io_mem q (List.mem_toFinset.mp e))
      · exact Finset.mem_union_right _ e

theorem program_physical_B (C : Point) : GatePhysical (programB C) := by
  cases C with
  | zero=>simp [programB,GatePhysical]
  | @some cx cy hc=>exact wrapper_physical_N hc

theorem program_slots_B (C : Point) : Challenge.gateSlots (programB C)≤50256955 := by
  cases C with
  | zero=>simp [programB]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_slots (.some hc)
    have delta:=(wrapperN_metrics hc).2.2
    change Challenge.gateSlots (wrapperOpt layout (.some hc) cx cy)≤50251248 at old
    change Challenge.gateSlots (wrapperN layout (.some hc) cx cy)≤50256955
    omega

theorem certificateB : Challenge.Certificate entryB boundsB where
  correct C b R:=(normalize_triple _ _ _).mpr (program_correct_B C b R)
  physical C:=normalize_physical _ (by simpa only [GatePhysical] using program_physical_B C)
  toffoli_le C:=(normalize_toffoli _).trans (program_toffoli_B C)
  measurements_le C:=by
    change measurementCount (normalizeProgram (programB C))≤1498375
    rw [normalize_measurements];exact program_measurements_B C
  qubits_le C:=by
    change qubits (normalizeProgram (programB C))≤1587
    rw [normalize_qubits];exact program_qubits_B C
  gateSlots_le C:=by
    change Challenge.gateSlots (normalizeProgram (programB C))≤50256955
    rw [normalize_slots];exact program_slots_B C

end ECDSAAdd.Entrant.FlagTop2
end

end

namespace ECDSAAdd.Entrant
def program := FlagTop2.programB
def entry := FlagTop2.entryB
def bounds := FlagTop2.boundsB
theorem certificate : Challenge.Certificate entry bounds := FlagTop2.certificateB
end ECDSAAdd.Entrant
