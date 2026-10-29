import ECDSAAdd.Submission.Entrant.ZeroWith

/-! Two point tests sharing one AND chain.

The chain runs over the `x`-part (with the finite flag) and then over the
`y`-part of a register XOR-ed with a classical code.  The `x`-part link `e`
and the final link `u` are both live in the middle, where two flag targets are
updated: `tk ^= k ∧ ((kSplit ∧ e) ⊕ u)` and `tc ^= (cSplit ∧ e) ⊕ u`. -/
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic

def upd2 (B : BasisState) (tk tc : Wire) (vk vc : Bool) : BasisState :=
  writeBit (writeBit B tk (B tk ^^ vk)) tc (B tc ^^ vc)

def innerMid (k u tk tc : Wire) : Program := [.CCX k u tk, .CX u tc]

def preMid (k e tk tc : Wire) (kSplit cSplit : Bool) : Program :=
  (if cSplit then [.CX e tc] else []) ++ (if kSplit then [.CCX k e tk] else [])

def sharedBlock (c k tk tc : Wire) (XB YB : List ZeroBit) (kx ky : Nat)
    (kSplit cSplit : Bool) : Program :=
  xorConstant (XB.map ZeroBit.input) kx ++ xorConstant (YB.map ZeroBit.input) ky ++
  zeroWith (preMid k (chainLast c XB) tk tc kSplit cSplit ++
    zeroWith (innerMid k (chainLast (chainLast c XB) YB) tk tc) (chainLast c XB) YB) c XB ++
  xorConstant (YB.map ZeroBit.input) ky ++ xorConstant (XB.map ZeroBit.input) kx

theorem upd2_apply (B : BasisState) (tk tc : Wire) (vk vc : Bool) (htc : tk ≠ tc) (q : Wire) :
    upd2 B tk tc vk vc q =
      if q = tc then B tc ^^ vc else if q = tk then B tk ^^ vk else B q := by
  by_cases h1 : q = tc
  · subst q; simp [upd2, writeBit]
  · by_cases h2 : q = tk
    · subst q; simp [upd2, writeBit, htc]
    · simp [upd2, writeBit, h1, h2]

theorem innerMid_run (k u tk tc : Wire) (hut : u ≠ tk) (htc : tk ≠ tc) (s : State) (m : List Bool) :
    run (innerMid k u tk tc) m s = ⟨s.phase, upd2 s.basis tk tc (s.basis k && s.basis u) (s.basis u)⟩ := by
  simp only [innerMid, run, upd2]
  congr 1
  funext q
  by_cases h1 : q = tc
  · subst q; simp [writeBit, hut, htc.symm]
  · by_cases h2 : q = tk
    · subst q; simp [writeBit, htc]
    · simp [writeBit, h1, h2]

theorem preMid_run (k e tk tc : Wire) (kSplit cSplit : Bool) (hec : e ≠ tc)
    (hkc : k ≠ tc) (htc : tk ≠ tc) (s : State) (m : List Bool) :
    run (preMid k e tk tc kSplit cSplit) m s =
      ⟨s.phase, upd2 s.basis tk tc (kSplit && s.basis k && s.basis e) (cSplit && s.basis e)⟩ := by
  have het : True := trivial
  have base : ∀ B : BasisState, upd2 B tk tc false false = B := by
    intro B; funext q; simp [upd2, writeBit]
  cases cSplit <;> cases kSplit
  · simp only [preMid, Bool.false_eq_true, if_false, List.append_nil, run, Bool.false_and, base]
  · simp only [preMid, Bool.false_eq_true, if_false, if_true, List.nil_append, run, Bool.true_and,
      Bool.false_and]
    congr 1; funext q
    by_cases h1 : q = tc
    · subst q; simp [upd2, writeBit, htc.symm]
    · by_cases h2 : q = tk
      · subst q; simp [upd2, writeBit, htc]
      · simp [upd2, writeBit, h1, h2]
  · simp only [preMid, Bool.false_eq_true, if_false, if_true, List.append_nil, run, Bool.true_and,
      Bool.false_and]
    congr 1; funext q
    by_cases h1 : q = tc
    · subst q; simp [upd2, writeBit, htc.symm]
    · by_cases h2 : q = tk
      · subst q; simp [upd2, writeBit, htc]
      · simp [upd2, writeBit, h1, h2]
  · simp only [preMid, if_true, List.singleton_append, run, Bool.true_and]
    congr 1; funext q
    by_cases h1 : q = tc
    · subst q; simp [upd2, writeBit, htc.symm, hkc, hec]
    · by_cases h2 : q = tk
      · subst q; simp [upd2, writeBit, htc, hkc, hec]
      · simp [upd2, writeBit, h1, h2]

theorem zeroBit_count' (bs : List ZeroBit) (w : Wire) :
    (bs.flatMap ZeroBit.wires).count w =
      (bs.map ZeroBit.input).count w + (bs.map ZeroBit.work).count w := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons,ZeroBit.wires,List.map_cons,List.count_append,
      List.count_cons,List.count_nil,ih]
    omega

theorem inputs_sublist (bs : List ZeroBit) :
    (bs.map ZeroBit.input).Sublist (bs.flatMap ZeroBit.wires) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.flatMap_cons, ZeroBit.wires, List.cons_append, List.nil_append]
    exact (ih.cons b.work).cons₂ b.input

/-- Distinctness package for a shared block. -/
structure SharedNames (c k tk tc : Wire) (XB YB : List ZeroBit) : Prop where
  nodup : (k::tk::tc::(chainWires c XB ++ YB.flatMap ZeroBit.wires)).Nodup
  xne : XB ≠ []
  yne : YB ≠ []

theorem sharedBlock_run (c k tk tc : Wire) (XB YB : List ZeroBit) (kx ky : Nat)
    (kSplit cSplit : Bool) (hn : SharedNames c k tk tc XB YB)
    (hkx : kx < 2^XB.length) (hky : ky < 2^YB.length)
    (s : State) (m : List Bool)
    (hzx : ∀ b ∈ XB, s.basis b.work = false) (hzy : ∀ b ∈ YB, s.basis b.work = false) :
    let ex := s.basis c && decide (regValue (XB.map ZeroBit.input) s.basis = kx)
    let ey := decide (regValue (YB.map ZeroBit.input) s.basis = ky)
    run (sharedBlock c k tk tc XB YB kx ky kSplit cSplit) m s =
      ⟨s.phase, upd2 s.basis tk tc (s.basis k && ((kSplit && ex) ^^ (ex && ey)))
        ((cSplit && ex) ^^ (ex && ey))⟩ := by
  intro ex ey
  -- names
  set e := chainLast c XB with he
  set u := chainLast e YB with hu
  have nd := hn.nodup
  have n1 := List.nodup_cons.mp nd
  have n2 := List.nodup_cons.mp n1.2
  have n3 := List.nodup_cons.mp n2.2
  have ndXY := n3.2
  have mem1 : ∀ q, q ∈ chainWires c XB ++ YB.flatMap ZeroBit.wires →
      q ∈ tk :: tc :: (chainWires c XB ++ YB.flatMap ZeroBit.wires) :=
    fun q h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  have hkS : k ∉ chainWires c XB := fun h => n1.1 (mem1 _ (List.mem_append_left _ h))
  have hkY : k ∉ YB.flatMap ZeroBit.wires := fun h => n1.1 (mem1 _ (List.mem_append_right _ h))
  have hktk : k ≠ tk := fun h => n1.1 (h ▸ List.mem_cons_self ..)
  have hktc : k ≠ tc := fun h => n1.1 (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have htS : tk ∉ chainWires c XB := fun h => n2.1 (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  have htY : tk ∉ YB.flatMap ZeroBit.wires := fun h => n2.1 (List.mem_cons_of_mem _ (List.mem_append_right _ h))
  have htc : tk ≠ tc := fun h => n2.1 (h ▸ List.mem_cons_self ..)
  have hcS : tc ∉ chainWires c XB := fun h => n3.1 (List.mem_append_left _ h)
  have hcY : tc ∉ YB.flatMap ZeroBit.wires := fun h => n3.1 (List.mem_append_right _ h)
  have ndX : (chainWires c XB).Nodup := (List.nodup_append.mp ndXY).1
  have ndY0 : (YB.flatMap ZeroBit.wires).Nodup := (List.nodup_append.mp ndXY).2.1
  have disXY : ∀ a ∈ (chainWires c XB), ∀ b ∈ YB.flatMap ZeroBit.wires, a ≠ b := (List.nodup_append.mp ndXY).2.2
  have heX : e ∈ (chainWires c XB) := chainLast_mem c XB
  have hework : e ∈ XB.map ZeroBit.work := by
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hn.xne
    exact chainLast_work c b bs
  have hYwires : ∀ q ∈ (chainWires e YB), q = e ∨ q ∈ YB.flatMap ZeroBit.wires := by
    intro q hq; simpa [chainWires] using hq
  have heY : e ∉ YB.flatMap ZeroBit.wires := fun h => disXY e heX e h rfl
  have ndY : (chainWires e YB).Nodup := List.nodup_cons.mpr ⟨heY, ndY0⟩
  have huY : u ∈ (chainWires e YB) := chainLast_mem e YB
  have hk_SY : k ∉ (chainWires e YB) := by
    intro h; rcases hYwires k h with h | h
    · exact hkS (h ▸ heX)
    · exact hkY h
  have htk_SY : tk ∉ (chainWires e YB) := by
    intro h; rcases hYwires tk h with h | h
    · exact htS (h ▸ heX)
    · exact htY h
  have htc_SY : tc ∉ (chainWires e YB) := by
    intro h; rcases hYwires tc h with h | h
    · exact hcS (h ▸ heX)
    · exact hcY h
  have hut : u ≠ tk := fun h => htk_SY (h ▸ huY)
  have huc : u ≠ tc := fun h => htc_SY (h ▸ huY)
  have het : e ≠ tk := fun h => htS (h ▸ heX)
  have hec : e ≠ tc := fun h => hcS (h ▸ heX)
  have hke : k ≠ e := fun h => hkS (h ▸ heX)
  have hku : k ≠ u := fun h => hk_SY (h ▸ huY)
  -- inner chain
  let Fin : BasisState → BasisState := fun B => upd2 B tk tc (B k && B u) (B u)
  have innerRun : ∀ (t : State) (m' : List Bool), (∀ b ∈ YB, t.basis b.work = false) →
      run (zeroWith (innerMid k u tk tc) e YB) m' t =
        ⟨t.phase, upd2 t.basis tk tc (t.basis k && (t.basis e && YB.all (fun b => !t.basis b.input)))
          (t.basis e && YB.all (fun b => !t.basis b.input))⟩ := by
    intro t m' hz
    have h := zeroWith_run (innerMid k u tk tc) Fin (fun _ => True) e YB ndY
      (fun s m _ => innerMid_run k u tk tc hut htc s m) (fun _ _ _ _ => trivial)
      (by
        intro B q hq
        have h1 : q ≠ tc := fun h => htc_SY (h ▸ hq)
        have h2 : q ≠ tk := fun h => htk_SY (h ▸ hq)
        simp [Fin, upd2_apply _ _ _ _ _ htc, h1, h2])
      (by
        intro B B' hBB hl q hq
        simp only [Fin, upd2_apply _ _ _ _ _ htc]
        rw [← hu] at hl
        rw [hBB k hk_SY, hBB tc htc_SY, hBB tk htk_SY, hl, hBB q hq])
      t m' hz trivial
    rw [h]
    congr 1
    funext q
    rw [← hu]
    simp only [Fin, upd2_apply _ _ _ _ _ htc, writeBit, Function.update_apply]
    by_cases h1 : q = tc
    · subst q; simp [huc.symm, hku]
    · by_cases h2 : q = tk
      · subst q; simp [h1, hut.symm, hku]
      · by_cases h3 : q = u
        · subst q; simp [h1, h2]
        · simp [h1, h2, h3]
  -- outer middle
  let Fout : BasisState → BasisState := fun B =>
    upd2 B tk tc ((kSplit && B k && B e) ^^ (B k && (B e && YB.all (fun b => !B b.input))))
      ((cSplit && B e) ^^ (B e && YB.all (fun b => !B b.input)))
  have hYin : ∀ b ∈ YB, b.input ∉ (chainWires c XB) := by
    intro b hb h
    exact disXY _ h _ (List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩) rfl
  have hYwk : ∀ b ∈ YB, b.work ∉ (chainWires c XB) := by
    intro b hb h
    exact disXY _ h _ (List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩) rfl
  have outerQ : ∀ (t : State) (m' : List Bool), (∀ b ∈ YB, t.basis b.work = false) →
      run (preMid k e tk tc kSplit cSplit ++ zeroWith (innerMid k u tk tc) e YB) m' t =
        ⟨t.phase, Fout t.basis⟩ := by
    intro t m' hz
    rw [run_append, run_take, preMid_run k e tk tc kSplit cSplit hec hktc htc]
    have hz' : ∀ b ∈ YB, (upd2 t.basis tk tc (kSplit && t.basis k && t.basis e) (cSplit && t.basis e)) b.work = false := by
      intro b hb
      have h1 : b.work ≠ tc := fun h => hcY (h ▸ List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩)
      have h2 : b.work ≠ tk := fun h => htY (h ▸ List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩)
      simp [upd2_apply _ _ _ _ _ htc, h1, h2, hz b hb]
    rw [innerRun _ _ hz']
    congr 1
    have hall : YB.all (fun b => !(upd2 t.basis tk tc (kSplit && t.basis k && t.basis e) (cSplit && t.basis e)) b.input) =
        YB.all (fun b => !t.basis b.input) := by
      apply all_congr'
      intro b hb
      have h1 : b.input ≠ tc := fun h => hcY (h ▸ List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩)
      have h2 : b.input ≠ tk := fun h => htY (h ▸ List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩)
      simp [upd2_apply _ _ _ _ _ htc, h1, h2]
    rw [hall]
    funext q
    simp only [Fout, upd2_apply _ _ _ _ _ htc, Ne.symm hec, Ne.symm het, Ne.symm hktc, Ne.symm hktk,
      if_false]
    by_cases h1 : q = tc
    · subst q; simp [htc.symm, Bool.xor_assoc, hec, het, hktc, hktk]
    · by_cases h2 : q = tk
      · subst q; simp [htc, Bool.xor_assoc, hec, het, hktc, hktk]
      · simp [h1, h2]
  -- XOR boundary
  let XI := XB.map ZeroBit.input
  let YI := YB.map ZeroBit.input
  have ndXI : XI.Nodup := (inputs_sublist XB).nodup (List.nodup_cons.mp ndX).2
  have ndYI : YI.Nodup := (inputs_sublist YB).nodup ndY0
  have hXIS : ∀ q ∈ XI, q ∈ chainWires c XB := by
    intro q hq
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩)
  have hYIS : ∀ q ∈ YI, q ∈ YB.flatMap ZeroBit.wires := by
    intro q hq
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
    exact List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩
  have hXY : ∀ q ∈ XI, q ∉ YI := fun q hx hy => disXY q (hXIS q hx) q (hYIS q hy) rfl
  have hcXI : c ∉ XI := by
    intro h
    have hm := hXIS c h
    have nd0 := List.nodup_cons.mp ndX
    obtain ⟨b, hb, he⟩ := List.mem_map.mp h
    exact nd0.1 (he ▸ List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩)
  have hcYI : c ∉ YI := fun h => disXY c (List.mem_cons_self ..) c (hYIS c h) rfl
  have hkXI : k ∉ XI := fun h => hkS (hXIS k h)
  have hkYI : k ∉ YI := fun h => hkY (hYIS k h)
  have htkXI : tk ∉ XI := fun h => htS (hXIS tk h)
  have htkYI : tk ∉ YI := fun h => htY (hYIS tk h)
  have htcXI : tc ∉ XI := fun h => hcS (hXIS tc h)
  have htcYI : tc ∉ YI := fun h => hcY (hYIS tc h)
  have heXI : e ∉ XI := by
    intro h
    obtain ⟨b, hb, he'⟩ := List.mem_map.mp hework
    obtain ⟨b', hb', hi⟩ := List.mem_map.mp h
    have nd0 := (List.nodup_cons.mp ndX).2
    have hw : b.work ∈ XB.flatMap ZeroBit.wires := List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩
    -- the work of b equals the input of b'
    have := List.nodup_iff_count.mp nd0 b.work
    have c1 : 1 ≤ (XB.map ZeroBit.work).count b.work := List.count_pos_iff.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
    have c2 : 1 ≤ (XB.map ZeroBit.input).count b.work := List.count_pos_iff.mpr (List.mem_map.mpr ⟨b', hb', hi.trans he'.symm⟩)
    have hc := zeroBit_count' XB b.work
    omega
  have heYI : e ∉ YI := fun h => heY (hYIS e h)
  have hworkX : ∀ b ∈ XB, b.work ∉ XI ∧ b.work ∉ YI := by
    intro b hb
    constructor
    · intro h
      obtain ⟨b', hb', hi⟩ := List.mem_map.mp h
      have nd0 := (List.nodup_cons.mp ndX).2
      have := List.nodup_iff_count.mp nd0 b.work
      have c1 : 1 ≤ (XB.map ZeroBit.work).count b.work := List.count_pos_iff.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
      have c2 : 1 ≤ (XB.map ZeroBit.input).count b.work := List.count_pos_iff.mpr (List.mem_map.mpr ⟨b', hb', hi⟩)
      have hc := zeroBit_count' XB b.work
      omega
    · intro h
      exact disXY b.work (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩))
        b.work (hYIS _ h) rfl
  have hworkY : ∀ b ∈ YB, b.work ∉ XI ∧ b.work ∉ YI := by
    intro b hb
    constructor
    · intro h
      exact disXY b.work (hXIS _ h) b.work (List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩) rfl
    · intro h
      obtain ⟨b', hb', hi⟩ := List.mem_map.mp h
      have := List.nodup_iff_count.mp ndY0 b.work
      have c1 : 1 ≤ (YB.map ZeroBit.work).count b.work := List.count_pos_iff.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
      have c2 : 1 ≤ (YB.map ZeroBit.input).count b.work := List.count_pos_iff.mpr (List.mem_map.mpr ⟨b', hb', hi⟩)
      have hc := zeroBit_count' YB b.work
      omega
  -- first two XORs
  obtain ⟨p1, o1, v1⟩ := xorConstant_correct XI ndXI kx (by simpa [XI] using hkx) s m
  set u1 := run (xorConstant XI kx) m s with hu1
  obtain ⟨p2, o2, v2⟩ := xorConstant_correct YI ndYI ky (by simpa [YI] using hky) u1 m
  set u2 := run (xorConstant YI ky) m u1 with hu2
  have u2out : ∀ q, q ∉ XI → q ∉ YI → u2.basis q = s.basis q := fun q hx hy => (o2 q hy).trans (o1 q hx)
  have u2X : regValue XI u2.basis = regValue XI s.basis ^^^ kx := by
    rw [← v1]; apply regValue_congr; intro q hq; exact o2 q (hXY q hq)
  have u2Y : regValue YI u2.basis = regValue YI s.basis ^^^ ky := by
    rw [v2]; congr 1; apply regValue_congr; intro q hq; exact o1 q (fun h => hXY q h hq)
  have hzx2 : ∀ b ∈ XB, u2.basis b.work = false := fun b hb =>
    (u2out _ (hworkX b hb).1 (hworkX b hb).2).trans (hzx b hb)
  have hzy2 : ∀ b ∈ YB, u2.basis b.work = false := fun b hb =>
    (u2out _ (hworkY b hb).1 (hworkY b hb).2).trans (hzy b hb)
  have allX : XB.all (fun b => !u2.basis b.input) = decide (regValue XI s.basis = kx) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true, decide_eq_true_eq]
    have : (∀ b ∈ XB, (!u2.basis b.input) = true) ↔ regValue XI u2.basis = 0 := by
      rw [regValue_zero]; simp [XI]
    rw [this, u2X]
    constructor
    · intro h; exact Nat.xor_eq_zero_iff.mp h
    · intro h; rw [h, Nat.xor_self]
  have allY : YB.all (fun b => !u2.basis b.input) = decide (regValue YI s.basis = ky) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true, decide_eq_true_eq]
    have : (∀ b ∈ YB, (!u2.basis b.input) = true) ↔ regValue YI u2.basis = 0 := by
      rw [regValue_zero]; simp [YI]
    rw [this, u2Y]
    constructor
    · intro h; exact Nat.xor_eq_zero_iff.mp h
    · intro h; rw [h, Nat.xor_self]
  -- the middle
  have midRun := zeroWith_run _ Fout (fun B => ∀ b ∈ YB, B b.work = false) c XB ndX
    (fun t m' h => outerQ t m' h)
    (by
      intro B B' hBB h b hb
      rw [← hBB b.work (fun hh => disXY _ hh _ (List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩) rfl)]
      exact h b hb)
    (by
      intro B q hq
      have h1 : q ≠ tc := fun h => hcS (h ▸ hq)
      have h2 : q ≠ tk := fun h => htS (h ▸ hq)
      simp [Fout, upd2_apply _ _ _ _ _ htc, h1, h2])
    (by
      intro B B' hBB hl q hq
      rw [← he] at hl
      have hall : YB.all (fun b => !B b.input) = YB.all (fun b => !B' b.input) := by
        apply all_congr'; intro b hb; rw [hBB b.input (hYin b hb)]
      simp only [Fout, upd2_apply _ _ _ _ _ htc, hall, hl, hBB k hkS, hBB tk htS, hBB tc hcS, hBB q hq])
    u2 m hzx2 hzy2
  rw [← he] at midRun
  have hVc : u2.basis c = s.basis c := u2out c hcXI hcYI
  have hVk : u2.basis k = s.basis k := u2out k hkXI hkYI
  have hVtk : u2.basis tk = s.basis tk := u2out tk htkXI htkYI
  have hVtc : u2.basis tc = s.basis tc := u2out tc htcXI htcYI
  have hYall : YB.all (fun b => !(writeBit u2.basis e (u2.basis c && XB.all (fun b => !u2.basis b.input))) b.input) =
      YB.all (fun b => !u2.basis b.input) := by
    apply all_congr'; intro b hb
    have hne : b.input ≠ e := fun h => heY (h ▸ List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩)
    simp [writeBit, hne]
  have midState : run (zeroWith (preMid k e tk tc kSplit cSplit ++ zeroWith (innerMid k u tk tc) e YB) c XB) m u2 =
      ⟨u2.phase, upd2 u2.basis tk tc ((kSplit && s.basis k && ex) ^^ (s.basis k && (ex && ey)))
        ((cSplit && ex) ^^ (ex && ey))⟩ := by
    have hYall2 : ∀ V : Bool, (YB.all fun b => !if b.input = e then V else u2.basis b.input) =
        decide (regValue YI s.basis = ky) := by
      intro V; rw [← allY]; apply all_congr'; intro b hb
      have hne : b.input ≠ e := fun h => heY (h ▸ List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩)
      simp [hne]
    rw [midRun]
    congr 1
    funext q
    simp only [Fout, hYall, allX, allY, hVc]
    simp only [upd2_apply _ _ _ _ _ htc, writeBit, Function.update_apply, hke, het.symm, hec.symm,
      if_false, hVk]
    by_cases h1 : q = tc
    · subst q; simp [hec.symm, Ne.symm hec, hVk, ex, ey, hYall2, XI, YI]
    · by_cases h2 : q = tk
      · subst q; simp [het.symm, Ne.symm het, h1, hVk, ex, ey, hYall2, XI, YI]
      · by_cases h3 : q = e
        · subst q; simp [h1, h2]
        · simp [h1, h2, h3]
  -- assemble
  have runR : ∀ (P : Program) (r : List Wire) (kk : Nat) (st : State),
      run (P ++ xorConstant r kk) m st = run (xorConstant r kk) m (run P m st) := by
    intro P r kk st
    rw [run_append, run_take]
    have h0 : measurementCount (xorConstant r kk) = 0 := (xorConstant_counts r kk).2
    rw [← run_take (xorConstant r kk) (m.drop _), ← run_take (xorConstant r kk) m, h0]
    simp
  have runL : ∀ (P : Program) (r : List Wire) (kk : Nat) (st : State),
      run (xorConstant r kk ++ P) m st = run P m (run (xorConstant r kk) m st) := by
    intro P r kk st
    rw [run_append]
    have h0 : measurementCount (xorConstant r kk) = 0 := (xorConstant_counts r kk).2
    rw [h0, List.drop_zero, ← run_take (xorConstant r kk) m, h0]
  have assemble : run (sharedBlock c k tk tc XB YB kx ky kSplit cSplit) m s =
      run (xorConstant XI kx) m (run (xorConstant YI ky) m
        (run (zeroWith (preMid k e tk tc kSplit cSplit ++ zeroWith (innerMid k u tk tc) e YB) c XB) m u2)) := by
    rw [sharedBlock, runR, runR, List.append_assoc, runL, runL]
  rw [assemble, midState]
  set w : State := ⟨u2.phase, upd2 u2.basis tk tc ((kSplit && s.basis k && ex) ^^ (s.basis k && (ex && ey)))
        ((cSplit && ex) ^^ (ex && ey))⟩ with hw
  obtain ⟨p3, o3, v3⟩ := xorConstant_correct YI ndYI ky (by simpa [YI] using hky) w m
  set w3 := run (xorConstant YI ky) m w with hw3
  obtain ⟨p4, o4, v4⟩ := xorConstant_correct XI ndXI kx (by simpa [XI] using hkx) w3 m
  have wX : ∀ q ∈ XI, w.basis q = u2.basis q := by
    intro q hq
    have h1 : q ≠ tc := fun h => htcXI (h ▸ hq)
    have h2 : q ≠ tk := fun h => htkXI (h ▸ hq)
    simp [w, upd2_apply _ _ _ _ _ htc, h1, h2]
  have wY : ∀ q ∈ YI, w.basis q = u2.basis q := by
    intro q hq
    have h1 : q ≠ tc := fun h => htcYI (h ▸ hq)
    have h2 : q ≠ tk := fun h => htkYI (h ▸ hq)
    simp [w, upd2_apply _ _ _ _ _ htc, h1, h2]
  have finX : regValue XI (run (xorConstant XI kx) m w3).basis = regValue XI s.basis := by
    rw [v4, show regValue XI w3.basis = regValue XI w.basis from
      regValue_congr _ _ _ (fun q hq => o3 q (hXY q hq)),
      regValue_congr _ _ _ wX, u2X, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have finY : regValue YI (run (xorConstant XI kx) m w3).basis = regValue YI s.basis := by
    rw [regValue_congr _ _ _ (fun q hq => o4 q (fun h => hXY q h hq)), v3,
      regValue_congr _ _ _ wY, u2Y, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  apply (show ∀ a b : State, a.phase = b.phase → a.basis = b.basis → a = b from
    fun ⟨ap, ab⟩ ⟨bp, bb⟩ hp hb => by cases hp; cases hb; rfl)
  · rw [p4, p3]; exact p2.trans p1
  · funext q
    by_cases hqx : q ∈ XI
    · rw [(regValue_eq_iff XI _ _).mp finX q hqx]
      have h1 : q ≠ tc := fun h => htcXI (h ▸ hqx)
      have h2 : q ≠ tk := fun h => htkXI (h ▸ hqx)
      simp [upd2_apply _ _ _ _ _ htc, h1, h2]
    · by_cases hqy : q ∈ YI
      · rw [(regValue_eq_iff YI _ _).mp finY q hqy]
        have h1 : q ≠ tc := fun h => htcYI (h ▸ hqy)
        have h2 : q ≠ tk := fun h => htkYI (h ▸ hqy)
        simp [upd2_apply _ _ _ _ _ htc, h1, h2]
      · rw [o4 q hqx, o3 q hqy]
        simp only [w, upd2_apply _ _ _ _ _ htc]
        rw [u2out q hqx hqy]
        by_cases h1 : q = tc
        · subst q; rw [hVtc]; simp
        · by_cases h2 : q = tk
          · subst q; rw [hVtk]; simp [h1]; cases kSplit <;> cases s.basis tk <;> cases s.basis k <;> simp
          · simp [h1, h2]

end ECDSAAdd.Entrant
