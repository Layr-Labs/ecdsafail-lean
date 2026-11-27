import ECDSAAdd.Submission.Entrant.MainP1
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed

/-! Generic: renaming that may merge wires, as long as no gate writes a merged wire. -/
namespace ECDSAAdd.Entrant.SquareOdd
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-- The wire an instruction writes (the measured wire for `measureX`). -/
def tgt : Instr → Wire
  | .X t => t
  | .CX _ t => t
  | .CCX _ _ t => t
  | .measureX t _ _ => t

theorem pullState_write_at (f : Wire → Wire) (t : Wire) (ht : ∀ q, f q = f t → q = t)
    (ph : Bool) (bits : BasisState) (v : Bool) :
    pullState f ⟨ph, writeBit bits (f t) v⟩ = ⟨ph, writeBit (fun j => bits (f j)) t v⟩ := by
  unfold pullState
  congr 1
  funext j
  simp only [writeBit, Function.update]
  by_cases h : j = t
  · subst h; simp
  · have hne : f j ≠ f t := fun e => h (ht j e)
    simp [h, hne]

theorem pullState_measure_at (f : Wire → Wire) (t : Wire) (ht : ∀ q, f q = f t → q = t)
    (c0 c1 : List Correction) (m : Bool) (s : State) :
    pullState f (measureAndCorrect (f t)
      (c0.map (renameCorrection f)) (c1.map (renameCorrection f)) m s) =
      measureAndCorrect t c0 c1 m (pullState f s) := by
  cases m <;> simp only [measureAndCorrect, Bool.false_eq_true, if_false, if_true]
  all_goals
    rw [pullState_correct, pullState_write_at f t ht]
    rfl

/-- Renaming may merge wires as long as every written wire has a singleton preimage. -/
theorem run_rename_at (f : Wire → Wire) (p : Program)
    (hp : ∀ i ∈ p, ∀ q, f q = f (tgt i) → q = tgt i) (m : List Bool) (s : State) :
    pullState f (run (renameProgram f p) m s) = run p m (pullState f s) := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    have hi := hp i (by simp)
    have ht : ∀ j ∈ p, ∀ q, f q = f (tgt j) → q = tgt j := fun j hj => hp j (List.mem_cons_of_mem _ hj)
    cases i <;> simp only [tgt] at hi <;> simp only [renameProgram, List.map_cons, renameInstr, run]
    all_goals change pullState f (run (renameProgram f p) _ _) = _
    all_goals rw [ih ht]
    all_goals first
      | rw [pullState_write_at f _ hi]; rfl
      | rw [pullState_measure_at f _ hi]

theorem renameProgram_append' (f : Wire → Wire) (p q : Program) :
    renameProgram f (p ++ q) = renameProgram f p ++ renameProgram f q := by
  simp [renameProgram]

theorem rename_copyRegister (f : Wire → Wire) (c : Wire) (src dst : List Wire) :
    renameProgram f (copyRegister (some c) src dst) = copyRegister (some (f c)) (src.map f) (dst.map f) := by
  induction src generalizing dst with
  | nil => cases dst <;> rfl
  | cons a src ih =>
    cases dst with
    | nil => rfl
    | cons b dst =>
      simp only [copyRegister, List.map_cons, copyGate]
      rw [renameProgram_append', ← ih dst]
      rfl

theorem rename_eraseMask (f : Wire → Wire) (c : Wire) (src dst : List Wire) :
    renameProgram f (eraseMask c src dst) = eraseMask (f c) (src.map f) (dst.map f) := by
  induction src generalizing dst with
  | nil => cases dst <;> rfl
  | cons a src ih =>
    cases dst with
    | nil => rfl
    | cons b dst =>
      simp only [eraseMask, List.map_cons]
      change renameInstr f _ :: renameProgram f (eraseMask c src dst) = _
      rw [ih dst]
      rfl

theorem copyRegister_tgt (c : Wire) (src dst : List Wire) :
    ∀ i ∈ copyRegister (some c) src dst, tgt i ∈ dst := by
  induction src generalizing dst with
  | nil => cases dst <;> simp [copyRegister]
  | cons a src ih =>
    cases dst with
    | nil => simp [copyRegister]
    | cons b dst =>
      intro i hi
      simp only [copyRegister, copyGate, List.singleton_append, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp [tgt]
      · exact List.mem_cons_of_mem _ (ih dst i hi)

theorem eraseMask_tgt (c : Wire) (src dst : List Wire) :
    ∀ i ∈ eraseMask c src dst, tgt i ∈ dst := by
  induction src generalizing dst with
  | nil => cases dst <;> simp [eraseMask]
  | cons a src ih =>
    cases dst with
    | nil => simp [eraseMask]
    | cons b dst =>
      intro i hi
      simp only [eraseMask, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp [tgt]
      · exact List.mem_cons_of_mem _ (ih dst i hi)

/-- A program changes only the wires it writes. -/
theorem run_keeps_untargeted (p : Program) (m : List Bool) (s : State) (w : Wire)
    (hw : ∀ i ∈ p, tgt i ≠ w) : (run p m s).basis w = s.basis w := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    have hi := hw i (by simp)
    have hp : ∀ j ∈ p, tgt j ≠ w := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hne : w ≠ tgt i := Ne.symm hi
    cases i <;> simp only [tgt] at hne <;> simp only [run] <;> rw [ih _ _ hp] <;>
      simp [measureAndCorrect, writeBit, Function.update, hne]


/-! ## The aliased square core -/

open Secp256k1 Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout StairSquareContract
  StairSquareAssembly PDSplitLeafSquare
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open private withSplitPark_correct cfgA_geom cfgC_geom cfg128_zeros cfgC_zeros e0_dis_bodyA e0_dis_bodyC
  eU_zero_of_prod0 prod_eq_of_take256 state_eq_of_out parkHostsA8 parkHostsA8_length parkHostsA8_sub
  perm_fixes_allowed withSplitPark_support_aux rename_wires_pad from ECDSAAdd.Submission.Entrant.OddField

/-- The square's input register with bit 0 read from the generic flag `G0`. -/
def srcA : List Wire := G0 :: K0.core.low.tail
/-- A fresh wire (no square wire is `≥ 20000`), used only in the proofs. -/
def tW : Wire := 30000
def srcT : List Wire := tW :: K0.core.low.tail
def cfgAo : SplitCfg := { cfgA with src := srcA }
def cfgAt : SplitCfg := { cfgA with src := srcT }
def parkA8 : List Wire := (ParkCopy.hosts E0).take 7 ++ [ControlLoan1589BFFold.eU K0]
theorem parkA8_eq : parkA8 = parkHostsA8 := rfl
/-- Branch A of the square, reading bit 0 of its input from `G0`. -/
def brAo : Program := withSplitPark cfgAo 120 parkA8 bodyA
def brAt : Program := withSplitPark cfgAt 120 parkA8 bodyA

theorem low_eq : K0.core.low = List.range' 258 128 := by decide +kernel
theorem G0_val : G0 = 4113 := by decide +kernel
theorem cfgAt_valid : CfgValid cfgAt :=
  ⟨cfgA_valid.hn, cfgA_valid.realNd, cfgA_valid.realLt, cfgA_valid.realAllowed, cfgA_valid.bankLen,
    cfgA_valid.dstLen, cfgA_valid.sLen, cfgA_valid.tLen, cfgA_valid.z4Len, cfgA_valid.carryLen,
    cfgA_valid.padLen, cfgA_valid.t1Len, cfgA_valid.t2Len, cfgA_valid.t5Len⟩

theorem cfgAo_valid : CfgValid cfgAo :=
  ⟨cfgA_valid.hn, cfgA_valid.realNd, cfgA_valid.realLt, cfgA_valid.realAllowed, cfgA_valid.bankLen,
    cfgA_valid.dstLen, cfgA_valid.sLen, cfgA_valid.tLen, cfgA_valid.z4Len, cfgA_valid.carryLen,
    cfgA_valid.padLen, cfgA_valid.t1Len, cfgA_valid.t2Len, cfgA_valid.t5Len⟩

theorem real_lt (q : Wire) (hq : q ∈ cfgA.realAll) : q < 20000 := cfgA_valid.realLt q hq
theorem tW_ne_of_lt (q : Wire) (hq : q < 20000) : q ≠ tW := by
  show q ≠ 30000
  intro h; rw [h] at hq; exact absurd hq (by decide)

theorem srcT_len : srcT.length = cfgA.n := by
  have h := (cfgA_geom).2.1
  change K0.core.low.length = 128 at h
  simp only [srcT, List.length_cons, List.length_tail, h]; rfl

theorem hosts10_lt : ∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h < 20000 := by
  intro h hh
  rcases (cfgA_geom).2.2.2.1 h hh with hE | rfl
  · rw [E0_eq] at hE; simp only [E0F, List.mem_append, List.mem_range'_1] at hE
    rcases hE with (hE | hE) | hE <;> exact lt_of_lt_of_le hE.2 (by norm_num)
  · decide +kernel

theorem tW_notin_low : tW ∉ K0.core.low.tail := by rw [low_eq]; decide

theorem notin_srcT (q : Wire) (hq : q < 20000) (hl : q ∉ cfgA.src) : q ∉ srcT := by
  intro h
  rcases List.mem_cons.mp h with h | h
  · exact tW_ne_of_lt q hq h
  · exact hl (List.mem_of_mem_tail h)


theorem bank_real (q : Wire) (hq : q ∈ cfgA.bank) : q ∈ cfgA.realAll := by
  unfold SplitCfg.realAll; simp only [List.mem_cons, List.mem_append]; tauto
theorem dst_real (q : Wire) (hq : q ∈ cfgA.dst) : q ∈ cfgA.realAll := by
  unfold SplitCfg.realAll; simp only [List.mem_cons, List.mem_append]; tauto
theorem live_real (q : Wire) (hq : q ∈ cfgA.liveT) : q ∈ cfgA.realAll := by
  unfold SplitCfg.liveT at hq; unfold SplitCfg.realAll; simp only [List.mem_cons, List.mem_append] at hq ⊢; tauto
theorem sc_real (q : Wire) (hq : q ∈ cfgA.cleanScratch) : q ∈ cfgA.realAll := by
  unfold SplitCfg.cleanScratch at hq; unfold SplitCfg.realAll
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq ⊢; tauto
theorem out_lt (q : Wire) (hq : q ∈ K0.core.out) : q < 20000 := by
  have e : K0.core.out = List.range' 2 256 := by decide +kernel
  rw [e, List.mem_range'_1] at hq
  exact lt_of_lt_of_le hq.2 (by norm_num)
theorem low_cons : K0.core.low = 258 :: List.range' 259 127 := by rw [low_eq]; rfl
theorem tW_notin_rest : tW ∉ List.range' 259 127 := by
  rw [List.mem_range'_1]; show ¬(259 ≤ 30000 ∧ 30000 < 259 + 127); omega
theorem G0_notin_rest : G0 ∉ List.range' 259 127 := by
  rw [List.mem_range'_1, G0_val]; omega

theorem cfgAt_geom :
    118 + (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).length = cfgAt.n ∧
    cfgAt.src.length = cfgAt.n ∧
    (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).Nodup ∧
    (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ∉ cfgAt.bank ∧ h ∉ cfgAt.src ∧ h ∉ cfgAt.dst ∧
      h ∉ K0.core.out ∧ h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0) ∧
    (G0 :: cfgAt.src ++ cfgAt.bank).Nodup ∧
    (∀ q ∈ E0, q ∉ cfgAt.bank) ∧
    (∀ q ∈ cfgAt.workT, q ∈ K0.core.work) ∧
    (∀ q ∈ cfgAt.liveT, (q ∈ E0 ∨ q ∈ cfgAt.workT) ∧ q ∉ cfgAt.bank ∧ q ∉ cfgAt.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgAt.cleanScratch, (q ∈ K0.foldPad ∨ q ∈ K0.core.work) ∧ q ∉ cfgAt.bank ∧ q ∉ cfgAt.src ∧
      q ∉ K0.core.out ∧ q ∉ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) ∧
    (∀ q ∈ cfgAt.dst, q ∉ cfgAt.bank ∧ q ∉ cfgAt.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgAt.bank, q ∉ K0.core.out) ∧
    (∀ q ∈ cfgAt.src, q ∉ K0.core.out) ∧
    (G0 ∉ cfgAt.bank ∧ G0 ∉ cfgAt.dst ∧ G0 ∉ cfgAt.liveT ∧ G0 ∉ cfgAt.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgAt.dst = cfgAt.dst.headD 0 ∧
    (E0.getD 130 0 ∉ cfgAt.dst ∧ E0.getD 130 0 ∉ cfgAt.liveT ∧ E0.getD 131 0 ∉ cfgAt.dst ∧ E0.getD 131 0 ∉ cfgAt.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ cfgAt.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgAt.liveT) ∧
    (cfgAt.T5.getD 0 0 = E0.getD 231 0 ∧ cfgAt.T5.getD 66 0 = E0.getD 298 0 ∧ cfgAt.T5.getD 67 0 = E0.getD 299 0) := by
  have g := cfgA_geom
  have srcSub : ∀ q ∈ cfgAt.src, q = tW ∨ q ∈ cfgA.src := by
    intro q hq; rcases List.mem_cons.mp hq with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_of_mem_tail h)
  refine ⟨g.1, srcT_len, g.2.2.1, g.2.2.2.1, ?_, g.2.2.2.2.2.1, ?_, g.2.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2.2.1, ?_, ?_, ?_,
    g.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · intro h hh
    have a := g.2.2.2.2.1 h hh
    exact ⟨a.1, notin_srcT h (hosts10_lt h hh) a.2.1, a.2.2⟩
  · have nd := g.2.2.2.2.2.2.1
    have hs : cfgAt.src = tW :: List.range' 259 127 := by
      show tW :: K0.core.low.tail = _; rw [low_cons]; rfl
    have hs0 : cfgA.src = 258 :: List.range' 259 127 := low_cons
    rw [hs]; rw [hs0] at nd
    have hb : tW ∉ cfgA.bank := fun h => tW_ne_of_lt tW (real_lt tW (bank_real tW h)) rfl
    simp only [List.cons_append, List.nodup_cons, List.mem_cons, List.mem_append, not_or] at nd ⊢
    refine ⟨⟨?_, G0_notin_rest, nd.1.2.2⟩, ⟨tW_notin_rest, hb⟩, nd.2.2⟩
    rw [G0_val]; decide
  · intro q hq
    have a := g.2.2.2.2.2.2.2.2.2.1 q hq
    exact ⟨a.1, a.2.1, notin_srcT q (real_lt q (live_real q hq)) a.2.2.1, a.2.2.2⟩
  · intro q hq
    have a := g.2.2.2.2.2.2.2.2.2.2.1 q hq
    exact ⟨a.1, a.2.1, notin_srcT q (real_lt q (sc_real q hq)) a.2.2.1, a.2.2.2⟩
  · intro q hq
    have a := g.2.2.2.2.2.2.2.2.2.2.2.1 q hq
    exact ⟨a.1, notin_srcT q (real_lt q (dst_real q hq)) a.2.1, a.2.2⟩
  · intro q hq hout
    rcases srcSub q hq with rfl | h
    · exact tW_ne_of_lt tW (out_lt tW hout) rfl
    · exact g.2.2.2.2.2.2.2.2.2.2.2.2.2.1 q h hout

open private cfgA_fast cfgC_fast from ECDSAAdd.Submission.Entrant.OddField
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  Challenge.gateSlots GatePhysical LocalRebuild.improved

/-- Branch A on the fresh-wire configuration: the exact frame of `withSplitPark_correct`. -/
theorem brAt_frame (t : State) (m : List Bool) (pre : BranchPre t) :
    (run brAt m t).phase = t.phase ∧
    regValue K0.core.out (run brAt m t).basis =
      A161Low4Offsets.resAFlow ((if t.basis G0 then regValue srcT t.basis else 0) ^ 2)
        (regValue K0.core.out t.basis) (t.basis G0) ∧
    ∀ q, q ∉ K0.core.out → (run brAt m t).basis q = t.basis q := by
  have g := cfgAt_geom
  have h128 : regValue srcT t.basis < 2 ^ 128 := by
    have := regValue_lt srcT t.basis
    rwa [srcT_len] at this
  let M := if t.basis G0 then regValue srcT t.basis else 0
  let O := regValue K0.core.out t.basis
  let V := A161Low4Offsets.resAFlow (M ^ 2) O (t.basis G0)
  have hMlt : M < 2 ^ 128 := by dsimp only [M]; split_ifs <;> omega
  have hNew := withSplitPark_correct cfgAt cfgAt_valid 120 parkHostsA8 bodyA V
    (by rw [parkHostsA8_length]; rfl) (by decide) g.2.1 (g.2.2.1.sublist parkHostsA8_sub)
    (fun h hh => g.2.2.2.1 h (parkHostsA8_sub.subset hh))
    (fun h hh => (g.2.2.2.2.1 h (parkHostsA8_sub.subset hh)).1) (fun h hh => (g.2.2.2.2.1 h (parkHostsA8_sub.subset hh)).2.1)
    (fun h hh => (g.2.2.2.2.1 h (parkHostsA8_sub.subset hh)).2.2.1) (fun h hh => (g.2.2.2.2.1 h (parkHostsA8_sub.subset hh)).2.2.2.1)
    (fun hh => g.2.2.2.2.2.1 (parkHostsA8_sub.subset hh)) (fun h hh => (g.2.2.2.2.1 h (parkHostsA8_sub.subset hh)).2.2.2.2) g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.1
    (fun q hq => Or.inl (g.2.2.2.2.2.2.2.2.1 q hq)) e0_dis_bodyA bodyA_avoids_workTA (fun _ => bodyA_ok.eUfree)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.1)
    (fun q hq hp => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.2 (parkHostsA8_sub.subset hp))
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2) g.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun s0 m0 hd0 hT0 hSc0 hi0 heu0 he0 =>
      cfg128_zeros cfgAt cfgAt_valid rfl g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        (by simp [SplitCfg.T, cfgAt, cfgA, List.take_take]) rfl rfl _
        (fun h hh => by simp only [parkHostsA8, List.mem_append, List.mem_singleton] at hh; exact hh)
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2⟩
        s0 m0 hd0 hT0 hSc0 hi0 heu0 he0)
    t m pre.clean
    ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp pre.prod0 q (List.mem_of_mem_take hq)))
    pre.ext0 pre.d0 (fun _ => eU_zero_of_prod0 t.basis pre.prod0)
    (fun t' m' hdst hkeep => by
      have h256_dis : ∀ q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh, K0.core.workHigh,
          K0.core.cin, K0.core.normFlag, K0.core.modFlag, K0.core.product.getD 256 0, K0.core.product.getD 257 0,
          K0.core.sumCarry, D0, G0], q ∉ cfgA.dst :=
        StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [cfgA_fast, K0_eq, D0_eq, G0_eq]; decide +kernel)
      have h256_in : K0.core.product.getD 256 0 ∈ K0.core.product ∧ K0.core.product.getD 257 0 ∈ K0.core.product :=
        ⟨DiagSq.getD_in _ 256 (by rw [hwK.core.product]; decide), DiagSq.getD_in _ 257 (by rw [hwK.core.product]; decide)⟩
      have hprod : regValue K0.core.product t'.basis = M ^ 2 := by
        rw [prod_eq_of_take256 t'.basis
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.1))
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.2))]
        exact hdst
      have hpc : K0.PairClean t'.basis := ⟨
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.pad,
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.work,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.productHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.outHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.workHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.cin,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.normFlag,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.modFlag⟩
      have hG : t'.basis G0 = t.basis G0 := hkeep G0 (h256_dis _ (by simp))
      have hout : regValue K0.core.out t'.basis = O :=
        regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.2 hq))
      have hfr := bodyA_ok.frame t'.basis M hMlt hprod hpc ((hkeep _ (h256_dis _ (by simp))).trans pre.sum0) O pre.outLt
        (fun hg => by rw [hG] at hg; simp [M, hg]) ((hkeep _ (h256_dis _ (by simp))).trans pre.d0)
        t' m' ⟨hout, fun _ _ => rfl⟩
      rw [hG] at hfr
      exact ⟨hfr.1, hfr.2.1, hfr.2.2⟩)
  exact ⟨hNew.1, hNew.2.1, hNew.2.2⟩

/-! ### Every wire of branch A is below `20000` -/

theorem allowed_lt : ∀ q ∈ allowedWires, q < 20000 := by
  have h : allowedWires.all (fun q => decide (q < 20000)) = true := by rw [allowedWires_eq]; decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem G0_allowed : G0 ∈ allowedWires := by rw [allowedWires_eq, G0_val]; decide +kernel

theorem K0wires_lt : ∀ q ∈ G0 :: K0.wires ++ E0 ++ [D0], q < 20000 := by
  have h : (G0 :: K0.wires ++ E0 ++ [D0]).all (fun q => decide (q < 20000)) = true := by
    rw [K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem swap_lt (a b x : Wire) (ha : a < 20000) (hb : b < 20000) (hx : x < 20000) :
    Equiv.swap a b x < 20000 := by
  rw [Equiv.swap_apply_def]; split_ifs <;> assumption

theorem bodyA_body_lt :
    ∀ q ∈ wires (renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 bodyA)), q < 20000 := by
  have hFoldPerm : LowZero18Square.foldPerm K0 E0 = Equiv.swap 4834 5093 := by
    ext x; rw [StairSquareSites.LT48K.foldPerm_eq, Equiv.swap_apply_def]; rfl
  have hSqSwap : R2SqEp760.sqSwap K0 E0 = Equiv.swap 4875 5478 := by
    ext x; rw [StairSquareSites.LT48K.sqSwap_eq, Equiv.swap_apply_def]; rfl
  intro q hq
  rw [R2SqEp760.bodySwap, renameProgram_support, renameProgram_support, Finset.mem_image] at hq
  obtain ⟨y, hy, rfl⟩ := hq
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hx' : x < 20000 := by
    rcases Finset.mem_insert.mp (bodyA_ok.support hx) with rfl | h
    · exact K0wires_lt _ (by simp)
    · exact K0wires_lt _ (by simp only [List.mem_toFinset] at h; simp [List.mem_cons] at h ⊢; tauto)
  rw [hFoldPerm, hSqSwap]
  exact swap_lt _ _ _ (by norm_num) (by norm_num) (swap_lt _ _ _ (by norm_num) (by norm_num) hx')

theorem srcA_allowed : ∀ q ∈ cfgAo.src, q ∈ allowedWires := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | h
  · exact G0_allowed
  · exact perm_fixes_allowed.2.2.2.1 q (List.mem_of_mem_tail h)

theorem brAo_lt : ∀ q ∈ wires brAo, q < 20000 := by
  have pa := perm_fixes_allowed
  have hsup := withSplitPark_support_aux cfgAo cfgAo_valid 120 parkHostsA8 bodyA srcA_allowed
    (fun q hq => pa.2.2.2.2.2.2.1 q (parkHostsA8_sub.subset hq)) pa.2.2.2.2.2.2.2.2.2.1
  intro q hq
  rcases Finset.mem_union.mp (hsup hq) with h | h
  · exact bodyA_body_lt q h
  · exact allowed_lt q (List.mem_toFinset.mp h)

/-! ### Branch A with bit 0 on `G0`: simulation of the fresh-wire branch -/

/-- Merge the fresh wire `tW` into `G0`. -/
def fA (q : Wire) : Wire := if q = tW then G0 else q

theorem G0_ne_tW : G0 ≠ tW := by rw [G0_val]; decide

theorem fA_ne (q : Wire) (h : q ≠ tW) : fA q = q := by unfold fA; exact if_neg h
theorem fA_G0 : fA G0 = G0 := fA_ne G0 G0_ne_tW
theorem fA_tW : fA tW = G0 := by unfold fA; exact if_pos rfl

theorem tgt_mem (i : Instr) : tgt i ∈ i.wires := by
  cases i <;> simp [tgt, Instr.wires]

theorem renameProgram_fix (f : Wire → Wire) (P : Program) (h : ∀ q ∈ wires P, f q = q) :
    renameProgram f P = P := by
  induction P with
  | nil => rfl
  | cons i P ih =>
    have hi : ∀ q ∈ i.wires, f q = q := fun q hq => h q (by simp [wires, hq])
    have hP : ∀ q ∈ wires P, f q = q := fun q hq => h q (by simp [wires, hq])
    have hc : ∀ cs : List Correction, (∀ q ∈ correctionWires cs, f q = q) → cs.map (renameCorrection f) = cs := by
      intro cs hcs
      induction cs with
      | nil => rfl
      | cons c cs ihc =>
        cases c with
        | Z t =>
          simp only [List.map_cons, renameCorrection]
          rw [hcs t (by simp [correctionWires]), ihc (fun q hq => hcs q (by simp [correctionWires, hq]))]
        | CZ a b =>
          simp only [List.map_cons, renameCorrection]
          rw [hcs a (by simp [correctionWires]), hcs b (by simp [correctionWires]),
            ihc (fun q hq => hcs q (by simp [correctionWires, hq]))]
    change renameInstr f i :: renameProgram f P = i :: P
    rw [ih hP]
    cases i with
    | X t => simp only [renameInstr]; rw [hi t (by simp [Instr.wires])]
    | CX c t => simp only [renameInstr]; rw [hi c (by simp [Instr.wires]), hi t (by simp [Instr.wires])]
    | CCX a b t =>
      simp only [renameInstr]
      rw [hi a (by simp [Instr.wires]), hi b (by simp [Instr.wires]), hi t (by simp [Instr.wires])]
    | measureX t c0 c1 =>
      simp only [renameInstr]
      rw [hi t (by simp [Instr.wires]), hc c0 (fun q hq => hi q (by simp [Instr.wires, hq])),
        hc c1 (fun q hq => hi q (by simp [Instr.wires, hq]))]

theorem tgt_mem_wires (P : Program) (i : Instr) (hi : i ∈ P) : tgt i ∈ wires P := by
  induction P with
  | nil => simp at hi
  | cons j P ih =>
    simp only [wires, Finset.mem_union]
    rcases List.mem_cons.mp hi with rfl | hj
    · exact Or.inl (tgt_mem i)
    · exact Or.inr (ih hj)

/-- A program that touches neither `tW` nor `G0` commutes with the merge. -/
theorem pull_fA_free (P : Program) (htW : tW ∉ wires P) (hG : G0 ∉ wires P) (m : List Bool) (s : State) :
    pullState fA (run P m s) = run P m (pullState fA s) := by
  have hfix : renameProgram fA P = P :=
    renameProgram_fix fA P (fun q hq => fA_ne q (fun e => htW (e ▸ hq)))
  have h := run_rename_at fA P (fun i hi q hq => by
    have ht := tgt_mem_wires P i hi
    have htne : tgt i ≠ tW := fun e => htW (e ▸ ht)
    rw [fA_ne _ htne] at hq
    by_cases hqt : q = tW
    · rw [hqt, fA_tW] at hq
      exact absurd (hq ▸ ht) hG
    · rw [fA_ne q hqt] at hq; exact hq) m s
  rw [hfix] at h
  exact h

/-- Targets inside a list that avoids `tW` and `G0` have a singleton preimage under the merge. -/
theorem fA_fiber (t : Wire) (ht : t ≠ tW) (hg : t ≠ G0) : ∀ q, fA q = fA t → q = t := by
  intro q hq
  rw [fA_ne t ht] at hq
  by_cases hqt : q = tW
  · rw [hqt, fA_tW] at hq; exact absurd hq.symm hg
  · rwa [fA_ne q hqt] at hq

theorem bank_lt (q : Wire) (hq : q ∈ cfgA.bank) : q < 20000 := real_lt q (bank_real q hq)
theorem G0_notin_bank : G0 ∉ cfgA.bank := (cfgA_geom).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1

theorem bank_fiber : ∀ i ∈ copyRegister (some G0) srcT cfgA.bank, ∀ q, fA q = fA (tgt i) → q = tgt i := by
  intro i hi
  have h := copyRegister_tgt G0 srcT cfgA.bank i hi
  exact fA_fiber _ (tW_ne_of_lt _ (bank_lt _ h)) (fun e => G0_notin_bank (e ▸ h))

theorem erase_fiber (src : List Wire) (k : Nat) :
    ∀ i ∈ eraseMask G0 src (cfgA.bank.take k), ∀ q, fA q = fA (tgt i) → q = tgt i := by
  intro i hi
  have h := List.mem_of_mem_take (eraseMask_tgt G0 src _ i hi)
  exact fA_fiber _ (tW_ne_of_lt _ (bank_lt _ h)) (fun e => G0_notin_bank (e ▸ h))

theorem map_fA_id (l : List Wire) (h : ∀ q ∈ l, q ≠ tW) : l.map fA = l :=
  (List.map_congr_left (fun q hq => fA_ne q (h q hq))).trans (List.map_id l)

theorem srcT_map : srcT.map fA = srcA := by
  have h : K0.core.low.tail.map fA = K0.core.low.tail := map_fA_id _ (fun q hq e => by
    rw [low_cons, List.tail_cons] at hq; exact tW_notin_rest (e ▸ hq))
  simp only [srcT, srcA, List.map_cons, fA_tW, h]

theorem bank_map : cfgA.bank.map fA = cfgA.bank :=
  map_fA_id _ (fun q hq => tW_ne_of_lt _ (bank_lt _ hq))

/-! ### The five pieces of branch A -/

def pAo : Program := copyRegister (some G0) srcA cfgA.bank
def pAt : Program := copyRegister (some G0) srcT cfgA.bank
def pE1o : Program := eraseMask G0 (srcA.take 120) (cfgA.bank.take 120)
def pE1t : Program := eraseMask G0 (srcT.take 120) (cfgA.bank.take 120)
def pEo : Program := eraseMask G0 srcA cfgA.bank
def pEt : Program := eraseMask G0 srcT cfgA.bank
def restA : Program :=
  ParkCopy.dummies parkHostsA8 ++ ParkCopy.move (cfgA.bank.drop 120) parkHostsA8 ++
  renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 bodyA) ++
  CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 cfgA.dst) (srcA.take 120) (cfgA.bank.take 120) ++
  ParkCopy.move parkHostsA8 (cfgA.bank.drop 120) ++ cfgA.clear

theorem cached_head (c k a a' : Wire) (l d : List Wire) :
    CachedSquareCopy.copy c k (a :: l) d = CachedSquareCopy.copy c k (a' :: l) d := by
  cases d <;> rfl

theorem brAo_split : brAo = (((pAo ++ cfgA.make) ++ pE1o) ++ restA) ++ pEo := by
  simp only [brAo, withSplitPark, pAo, pE1o, restA, pEo, List.append_assoc]; rfl

theorem brAt_split : brAt = (((pAt ++ cfgA.make) ++ pE1t) ++ restA) ++ pEt := by
  have hc : CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 cfgA.dst) (srcT.take 120) (cfgA.bank.take 120) =
      CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 cfgA.dst) (srcA.take 120) (cfgA.bank.take 120) := by
    simp only [srcT, srcA, List.take_succ_cons]; exact cached_head _ _ _ _ _ _
  simp only [brAt, withSplitPark, pAt, pE1t, restA, pEt, List.append_assoc]
  rw [← hc]; rfl

theorem pAo_eq : pAo = renameProgram fA pAt := by
  rw [pAt, rename_copyRegister, fA_G0, srcT_map, bank_map]; rfl
theorem pE1o_eq : pE1o = renameProgram fA pE1t := by
  rw [pE1t, rename_eraseMask, fA_G0, List.map_take, List.map_take, srcT_map, bank_map]; rfl
theorem pEo_eq : pEo = renameProgram fA pEt := by
  rw [pEt, rename_eraseMask, fA_G0, srcT_map, bank_map]; rfl

theorem erase_fiber' (src dst : List Wire) (hd : ∀ q ∈ dst, q ∈ cfgA.bank) :
    ∀ i ∈ eraseMask G0 src dst, ∀ q, fA q = fA (tgt i) → q = tgt i := by
  intro i hi
  have h := hd _ (eraseMask_tgt G0 src dst i hi)
  exact fA_fiber _ (tW_ne_of_lt _ (bank_lt _ h)) (fun e => G0_notin_bank (e ▸ h))

theorem cin_mem : K0.core.cin ∈ K0.wires := by
  simp [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires]

theorem G0_ne_cin : G0 ≠ K0.core.cin := fun h => (List.nodup_cons.mp controlND).1 (h ▸ cin_mem)

theorem real_split (c : SplitCfg) (x : Wire) (hx : x ∈ c.realAll) :
    x = K0.core.cin ∨ x ∈ c.bank ∨ x ∈ c.dst ∨ x ∈ c.liveT ∨ x ∈ c.cleanScratch := by
  unfold SplitCfg.realAll at hx
  unfold SplitCfg.liveT SplitCfg.cleanScratch
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx ⊢
  tauto

theorem G0_notin_real : G0 ∉ cfgA.realAll := by
  have g := (cfgA_geom).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro h
  rcases real_split cfgA G0 h with h | h | h | h | h
  · exact G0_ne_cin h
  · exact g.1 h
  · exact g.2.1 h
  · exact g.2.2.1 h
  · exact g.2.2.2.1 h

theorem make_free : tW ∉ wires cfgA.make ∧ G0 ∉ wires cfgA.make := by
  have hs := (cfg_support cfgA cfgA_valid).1
  exact ⟨fun h => tW_ne_of_lt tW (real_lt tW (List.mem_toFinset.mp (hs h))) rfl,
    fun h => G0_notin_real (List.mem_toFinset.mp (hs h))⟩

theorem restA_tW : tW ∉ wires restA := by
  intro h
  have hsub : wires restA ⊆ wires brAo := by
    rw [brAo_split]; intro q hq; simp only [wires_append, Finset.mem_union]; tauto
  exact tW_ne_of_lt tW (brAo_lt tW (hsub h)) rfl

/-! ### Simulation: branch A with bit 0 on `G0` runs the fresh-wire branch -/

theorem kseq2 (P P' Q Q' : Program) (hc : measurementCount P = measurementCount P') (m : List Bool)
    (s s' : State) :
    ∃ m1 m2, run (P ++ Q) m s = run Q m2 (run P m1 s) ∧ run (P' ++ Q') m s' = run Q' m2 (run P' m1 s') :=
  ⟨m.take (measurementCount P), m.drop (measurementCount P), run_append P Q m s, by rw [run_append, ← hc]⟩

theorem pullState_phase (f : Wire → Wire) (s : State) : (pullState f s).phase = s.phase := rfl
theorem pullState_basis (f : Wire → Wire) (s : State) (q : Wire) : (pullState f s).basis q = s.basis (f q) := rfl

theorem pull_fA_basis (s : State) (q : Wire) (hq : q ≠ tW) : (pullState fA s).basis q = s.basis q := by
  show s.basis (fA q) = s.basis q; rw [fA_ne q hq]

theorem K0mem_lt (q : Wire) (hq : q ∈ K0.wires) : q < 20000 := K0wires_lt q (by simp [hq])

theorem pre_congr (t t' : State) (hp : t'.phase = t.phase) (h : ∀ q, q < 20000 → t'.basis q = t.basis q)
    (pre : BranchPre t) : BranchPre t' := by
  have hK : ∀ q ∈ K0.wires, t'.basis q = t.basis q := fun q hq => h q (K0mem_lt q hq)
  have reg : ∀ R : List Wire, (∀ q ∈ R, q ∈ K0.wires) → regValue R t'.basis = regValue R t.basis :=
    fun R hR => regValue_congr _ _ _ (fun q hq => hK q (hR q hq))
  have W : ∀ q, q ∈ K0.core.out ∨ q ∈ K0.core.product ∨ q ∈ K0.foldPad ∨ q ∈ K0.core.work ∨
      q = K0.core.productHigh ∨ q = K0.core.outHigh ∨ q = K0.core.workHigh ∨ q = K0.core.cin ∨
      q = K0.core.normFlag ∨ q = K0.core.modFlag ∨ q = K0.core.sumCarry → q ∈ K0.wires := by
    intro q hq
    simp only [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires,
      CuccaroStreamedSquareWideLayout.foldPad, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    tauto
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [reg _ (fun q hq => W q (by tauto))]; exact pre.outLt
  · rw [reg _ (fun q hq => W q (by tauto))]; exact pre.prod0
  · rw [reg _ (fun q hq => W q (by tauto))]; exact pre.clean.pad
  · rw [reg _ (fun q hq => W q (by tauto))]; exact pre.clean.work
  · rw [hK _ (W _ (by tauto))]; exact pre.clean.productHigh
  · rw [hK _ (W _ (by tauto))]; exact pre.clean.outHigh
  · rw [hK _ (W _ (by tauto))]; exact pre.clean.workHigh
  · rw [hK _ (W _ (by tauto))]; exact pre.clean.cin
  · rw [hK _ (W _ (by tauto))]; exact pre.clean.normFlag
  · rw [hK _ (W _ (by tauto))]; exact pre.clean.modFlag
  · rw [hK _ (W _ (by tauto))]; exact pre.sum0
  · rw [regValue_congr _ _ _ (fun q hq => h q (K0wires_lt q (by simp [hq])))]; exact pre.ext0
  · rw [h _ (K0wires_lt _ (by simp))]; exact pre.d0

theorem G0_notin_out : G0 ∉ K0.core.out := (cfgA_geom).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2

theorem brAo_sim (r : State) (m : List Bool) (pre : BranchPre r) :
    pullState fA (run brAo m r) = run brAt m (pullState fA r) := by
  have preU : BranchPre (pullState fA r) :=
    pre_congr r _ rfl (fun q hq => pull_fA_basis r q (tW_ne_of_lt q hq)) pre
  have fin := brAt_frame (pullState fA r) m preU
  have cA : measurementCount pAo = measurementCount pAt := by rw [pAo_eq]; exact (renameProgram_counts _ _).2
  have cE1 : measurementCount pE1o = measurementCount pE1t := by
    rw [pE1o_eq]; exact (renameProgram_counts _ _).2
  rw [brAo_split, brAt_split]
  rw [brAt_split] at fin
  obtain ⟨x4, m5, e5o, e5t⟩ := kseq2 (((pAo ++ cfgA.make) ++ pE1o) ++ restA) (((pAt ++ cfgA.make) ++ pE1t) ++ restA)
    pEo pEt (by simp only [measurementCount_append, cA, cE1]) m r (pullState fA r)
  obtain ⟨x3, m4, e4o, e4t⟩ := kseq2 ((pAo ++ cfgA.make) ++ pE1o) ((pAt ++ cfgA.make) ++ pE1t) restA restA
    (by simp only [measurementCount_append, cA, cE1]) x4 r (pullState fA r)
  obtain ⟨x2, m3, e3o, e3t⟩ := kseq2 (pAo ++ cfgA.make) (pAt ++ cfgA.make) pE1o pE1t
    (by simp only [measurementCount_append, cA]) x3 r (pullState fA r)
  obtain ⟨m1, m2, e2o, e2t⟩ := kseq2 pAo pAt cfgA.make cfgA.make cA x2 r (pullState fA r)
  rw [e5o, e4o, e3o, e2o, e5t, e4t, e3t, e2t]
  rw [e5t, e4t, e3t, e2t] at fin
  have h1 : pullState fA (run pAo m1 r) = run pAt m1 (pullState fA r) := by
    rw [pAo_eq]; exact run_rename_at fA pAt bank_fiber m1 r
  have h2 : pullState fA (run cfgA.make m2 (run pAo m1 r)) = run cfgA.make m2 (run pAt m1 (pullState fA r)) := by
    rw [← h1]; exact pull_fA_free _ make_free.1 make_free.2 m2 _
  have h3 : pullState fA (run pE1o m3 (run cfgA.make m2 (run pAo m1 r))) =
      run pE1t m3 (run cfgA.make m2 (run pAt m1 (pullState fA r))) := by
    rw [pE1o_eq, ← h2]
    exact run_rename_at fA pE1t (erase_fiber' _ _ (fun q hq => List.mem_of_mem_take hq)) m3 _
  -- `G0` after the first three pieces on the real side
  have gr3 : (run pE1o m3 (run cfgA.make m2 (run pAo m1 r))).basis G0 = r.basis G0 := by
    rw [run_keeps_untargeted pE1o m3 _ G0 (fun i hi e => G0_notin_bank (e ▸
        List.mem_of_mem_take (eraseMask_tgt G0 _ _ i hi))),
      run_preserves_outside _ _ _ G0 make_free.2,
      run_keeps_untargeted pAo m1 r G0 (fun i hi e => G0_notin_bank (e ▸ copyRegister_tgt G0 _ _ i hi))]
  generalize hr3 : run pE1o m3 (run cfgA.make m2 (run pAo m1 r)) = r3 at h3 gr3 ⊢
  generalize hu3 : run pE1t m3 (run cfgA.make m2 (run pAt m1 (pullState fA r))) = u3 at h3 fin ⊢
  -- the middle pieces run identically off `tW`
  have agree : (run restA m4 r3).phase = (run restA m4 u3).phase ∧
      ∀ q, q ≠ tW → (run restA m4 r3).basis q = (run restA m4 u3).basis q := by
    have eq : ∀ w, w ≠ tW → r3.basis w = u3.basis w := fun w hw => by
      rw [← h3, pull_fA_basis _ _ hw]
    have loc := pool_run_agrees restA (wires restA) (Finset.Subset.refl _) m4 r3 u3 (by rw [← h3, pullState_phase])
      (fun w hw => eq w (fun e => restA_tW (e ▸ hw)))
    refine ⟨loc.1, fun q hq => ?_⟩
    by_cases hw : q ∈ wires restA
    · exact loc.2 q hw
    · rw [run_preserves_outside _ _ _ _ hw, run_preserves_outside _ _ _ _ hw]; exact eq q hq
  have gu : (run restA m4 u3).basis G0 = (pullState fA r).basis G0 := by
    rw [← fin.2.2 G0 G0_notin_out]
    exact (run_keeps_untargeted pEt m5 _ G0 (fun i hi e => G0_notin_bank (e ▸ eraseMask_tgt G0 _ _ i hi))).symm
  have h4 : pullState fA (run restA m4 r3) = run restA m4 u3 := by
    apply State.extensionality
    · rw [pullState_phase]; exact agree.1
    · funext q
      by_cases hq : q = tW
      · subst hq
        rw [pullState_basis, fA_tW, agree.2 G0 G0_ne_tW, gu, pull_fA_basis _ _ G0_ne_tW, ← gr3,
          run_preserves_outside _ _ _ _ restA_tW, ← h3, pullState_basis, fA_tW]
      · rw [pullState_basis, fA_ne q hq]; exact agree.2 q hq
  rw [pEo_eq, ← h4]
  exact run_rename_at fA pEt (erase_fiber' _ _ (fun q hq => hq)) m5 _

theorem regValue_pull (f : Wire → Wire) (l : List Wire) (s : State) :
    regValue l (pullState f s).basis = regValue (l.map f) s.basis := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [regValue, List.foldr_cons, List.map_cons] at ih ⊢
    rw [ih]; rfl

theorem tW_notin_brAo : tW ∉ wires brAo := fun h => tW_ne_of_lt tW (brAo_lt tW h) rfl

/-- **Branch A with bit 0 on `G0`**: the frame of the stock branch with input
`if G0 then srcA else 0`, i.e. `G0 + 2 * low.tail` when generic. -/
theorem brAo_frame (r : State) (m : List Bool) (pre : BranchPre r) :
    (run brAo m r).phase = r.phase ∧
    regValue K0.core.out (run brAo m r).basis =
      A161Low4Offsets.resAFlow ((if r.basis G0 then regValue srcA r.basis else 0) ^ 2)
        (regValue K0.core.out r.basis) (r.basis G0) ∧
    ∀ q, q ∉ K0.core.out → (run brAo m r).basis q = r.basis q := by
  have sim := brAo_sim r m pre
  have preU : BranchPre (pullState fA r) :=
    pre_congr r _ rfl (fun q hq => pull_fA_basis r q (tW_ne_of_lt q hq)) pre
  have fin := brAt_frame (pullState fA r) m preU
  have outNe : ∀ q ∈ K0.core.out, q ≠ tW := fun q hq => tW_ne_of_lt q (out_lt q hq)
  have hG : (pullState fA r).basis G0 = r.basis G0 := pull_fA_basis r G0 G0_ne_tW
  have hO : regValue K0.core.out (pullState fA r).basis = regValue K0.core.out r.basis :=
    regValue_congr _ _ _ (fun q hq => pull_fA_basis r q (outNe q hq))
  have hS : regValue srcT (pullState fA r).basis = regValue srcA r.basis := by
    rw [regValue_pull, srcT_map]
  refine ⟨?_, ?_, ?_⟩
  · rw [← pullState_phase fA (run brAo m r), sim, fin.1, pullState_phase]
  · rw [← regValue_congr _ _ _ (fun q hq => pull_fA_basis (run brAo m r) q (outNe q hq)), sim, fin.2.1, hG, hO, hS]
  · intro q hq
    by_cases ht : q = tW
    · subst ht; exact run_preserves_outside _ _ _ _ tW_notin_brAo
    · rw [← pull_fA_basis (run brAo m r) q ht, sim, fin.2.2 q hq, pull_fA_basis r q ht]

/-! ## Branch C with bit 0 on `G0` -/

def sumSrcO : List Wire := srcA ++ [K0.core.pad.getD 0 0]
def gPrepO : Program := addInPlace sumSrcO K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
def gClearO : Program := subInPlace sumSrcO K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
/-- Branch C of the square, reading bit 0 of its input from `G0`. -/
def brCo : Program := gPrepO ++ withSplitPark cfgC 124 (ParkCopyS.hostsS E0) bodyC ++ gClearO

theorem srcA_len : srcA.length = 128 := by simp [srcA, low_cons]

theorem srcA_out (q : Wire) (hq : q ∈ srcA) : q ∉ K0.core.out := by
  rcases List.mem_cons.mp hq with rfl | h
  · exact G0_notin_out
  · exact (cfgA_geom).2.2.2.2.2.2.2.2.2.2.2.2.2.1 q (List.mem_of_mem_tail h)

theorem G0_notin_wires : G0 ∉ K0.wires := (List.nodup_cons.mp controlND).1

theorem sumO_nodup : (K0.core.cin :: (sumSrcO ++ K0.core.sum ++ OwnDiagAll12Square.sumBank K0)).Nodup := by
  have nd := OwnDiagAll12Square.sum_nodup K0 hwK ndK
  have hs : OwnDiagAll12Square.sumSrc K0 = 258 :: (List.range' 259 127 ++ [K0.core.pad.getD 0 0]) := by
    rw [OwnDiagAll12Square.sumSrc, low_cons]; rfl
  have ho : sumSrcO = G0 :: (List.range' 259 127 ++ [K0.core.pad.getD 0 0]) := by
    rw [sumSrcO, srcA, low_cons]; rfl
  rw [hs] at nd; rw [ho]
  simp only [List.cons_append, List.nodup_cons, List.mem_cons, not_or] at nd ⊢
  have memY : ∀ q ∈ K0.core.y, q ∈ K0.wires := fun q h => by
    simp [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, h]
  have memP : ∀ q ∈ K0.core.pad, q ∈ K0.wires := fun q h => by
    simp [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, h]
  have memK : ∀ q ∈ K0.core.work, q ∈ K0.wires := fun q h => by
    simp [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, h]
  have inW : ∀ q, q ∈ List.range' 259 127 ++ [K0.core.pad.getD 0 0] ++ K0.core.sum ++
      OwnDiagAll12Square.sumBank K0 → q ∈ K0.wires ∨ q ∈ K0.core.sum := by
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with ((h | h) | h) | h
    · left; apply memY
      have hl : q ∈ K0.core.low := by rw [low_cons]; exact List.mem_cons_of_mem _ h
      exact List.mem_of_mem_take hl
    · left; rw [h]; exact memP _ (OwnDiagAll12Square.sumPad_mem K0 hwK)
    · right; exact h
    · left; exact memK _ (List.mem_of_mem_take h)
  refine ⟨⟨fun e => G0_ne_cin e.symm, nd.1.2⟩, ?_, nd.2.2⟩
  intro hG
  rcases inW G0 (by simpa [List.append_assoc] using hG) with h | h
  · exact G0_notin_wires h
  · rcases List.mem_cons.mp (OwnDiagAll12Square.sum_in K0 K0.core.cin G0 h) with e | h'
    · exact G0_ne_cin e
    · exact G0_notin_wires h'

theorem sumSrcO_len : sumSrcO.length = 129 := by simp [sumSrcO, srcA_len]

theorem sumSrcO_value (base : BasisState) (A : Nat) (hA : regValue srcA base = A)
    (hpad : regValue K0.core.pad base = 0) : regValue sumSrcO base = A := by
  have bit0 : base (K0.core.pad.getD 0 0) = false :=
    (regValue_zero _ _).mp hpad _ (OwnDiagAll12Square.sumPad_mem K0 hwK)
  rw [sumSrcO, regValue_append, hA]
  have hz : regValue [K0.core.pad.getD 0 0] base = 0 := by
    change (if base (K0.core.pad.getD 0 0) then 1 else 0) = 0
    rw [bit0]; rfl
  rw [hz, Nat.mul_zero, Nat.add_zero]

theorem gPrepO_frame (base : BasisState) (A B : Nat)
    (hA : regValue srcA base = A) (hbound : A + B < 2^129) (hpad : regValue K0.core.pad base = 0)
    (hcin : base K0.core.cin = false) (hwork : regValue K0.core.work base = 0) :
    Triple (SquareFrame K0.core.sum base B) gPrepO (SquareFrame K0.core.sum base (A + B)) := by
  have lens := OwnDiagAll12Square.sum_lengths K0 hwK
  have add := addInPlace_cin_frame K0.core.cin sumSrcO K0.core.sum (OwnDiagAll12Square.sumBank K0)
    sumO_nodup (sumSrcO_len.trans lens.2.1.symm) (by rw [lens.2.2, lens.2.1]) base false hcin
    (OwnDiagAll12Square.sumBank_zero K0 base hwork) B
  have val : (B + regValue sumSrcO base + false.toNat) % 2 ^ K0.core.sum.length = A + B := by
    rw [sumSrcO_value base A hA hpad, lens.2.1]
    simp only [Bool.toNat_false, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  rw [val] at add
  exact add

theorem gClearO_frame (base : BasisState) (A B : Nat)
    (hA : regValue srcA base = A) (hbound : A + B < 2^129) (hpad : regValue K0.core.pad base = 0)
    (hcin : base K0.core.cin = false) (hwork : regValue K0.core.work base = 0) :
    Triple (SquareFrame K0.core.sum base (A + B)) gClearO (SquareFrame K0.core.sum base B) := by
  have lens := OwnDiagAll12Square.sum_lengths K0 hwK
  have nd := sumO_nodup
  have dis (w : Wire) (hw' : w ∈ K0.core.cin :: (sumSrcO ++ OwnDiagAll12Square.sumBank K0)) : w ∉ K0.core.sum := by
    intro hdw
    have hn := List.nodup_iff_count.mp nd w
    have h1 := List.count_pos_iff.mpr hw'
    have h2 := List.count_pos_iff.mpr hdw
    simp only [List.count_cons, List.count_append] at hn h1
    omega
  intro s m h
  unfold gClearO
  have sv : regValue sumSrcO s.basis = A :=
    (regValue_congr _ _ _ (fun w hw' => h.2 w (dis w (by simp [hw'])))).trans
      (sumSrcO_value base A hA hpad)
  have kv : regValue (OwnDiagAll12Square.sumBank K0) s.basis = 0 :=
    (regValue_congr _ _ _ (fun w hw' => h.2 w (dis w (by simp [hw'])))).trans
      (OwnDiagAll12Square.sumBank_zero K0 base hwork)
  have cv : s.basis K0.core.cin = false := (h.2 _ (dis _ (by simp))).trans hcin
  have hx : sumSrcO.length = K0.core.sum.length := sumSrcO_len.trans lens.2.1.symm
  have hc : (OwnDiagAll12Square.sumBank K0).length + 1 = K0.core.sum.length := by rw [lens.2.2, lens.2.1]
  have spec := subInPlace_spec sumSrcO K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin nd hx hc A (A + B) s m
    ⟨⟨⟨sv, h.1⟩, cv⟩, kv⟩
  have hv : regValue K0.core.sum (run (subInPlace sumSrcO K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin) m s).basis =
      (A + B + 2^K0.core.sum.length - A) % 2^K0.core.sum.length := spec.2.1.1.2
  refine ⟨spec.1, ?_, ?_⟩
  · rw [hv, lens.2.1, show A + B + 2^129 - A = B + 2^129 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · intro w hw'
    exact (subInPlace_frame sumSrcO K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin nd hx hc s m cv kv w hw').trans
      (h.2 w hw')

theorem brCo_frame (t : State) (m : List Bool) (pre : BranchPre t) :
    (run brCo m t).phase = t.phase ∧
    regValue K0.core.out (run brCo m t).basis =
      C163Low4Offsets.resCFlow (t.basis G0)
        ((if t.basis G0 then regValue srcA t.basis + regValue K0.core.sum t.basis else 0) ^ 2)
        (regValue K0.core.out t.basis) ∧
    ∀ q, q ∉ K0.core.out → (run brCo m t).basis q = t.basis q := by
  have g := cfgC_geom
  have nd := (List.nodup_cons.mp controlND).2
  have dis := K0.measured_sum_disjoint nd
  have ctrlAway : G0 ∉ K0.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp controlND G0
    have pos := List.count_pos_iff.mpr bad
    have sumBound := K0.measured_sum_count G0
    simp only [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, List.count_append, List.count_cons,
      List.count_nil, beq_self_eq_true, if_true] at h sumBound
    omega
  set A := regValue srcA t.basis
  set B := regValue K0.core.sum t.basis
  set O := regValue K0.core.out t.basis
  have hLowLt : A < 2 ^ 128 := by
    have h := regValue_lt srcA t.basis
    rwa [srcA_len] at h
  have hSumEq : B = regValue K0.core.high t.basis := by
    simp [B, CuccaroStreamedSquareLayout.sum, regValue_append, regValue, pre.sum0]
  have hHiLt : regValue K0.core.high t.basis < 2 ^ 128 := by
    simpa [K0.core.high_length hwK.core] using regValue_lt K0.core.high t.basis
  have hSumBd : A + B < 2 ^ 129 := by rw [hSumEq]; omega
  let midNew := withSplitPark cfgC 124 (ParkCopyS.hostsS E0) bodyC
  obtain ⟨r1, mC, eC⟩ := kseq (gPrepO ++ midNew) gClearO m t
  obtain ⟨mP, mM, eM⟩ := kseq gPrepO midNew r1 t
  have hbrC : run brCo m t = run gClearO mC (run midNew mM (run gPrepO mP t)) := by
    change run ((gPrepO ++ midNew) ++ gClearO) m t = _
    rw [eC, eM]
  have hprep := gPrepO_frame t.basis A B rfl hSumBd
    (PairClean.corePad K0 t.basis pre.clean) pre.clean.cin pre.clean.work t mP ⟨rfl, fun _ _ => rfl⟩
  generalize hu : run gPrepO mP t = u at hbrC hprep ⊢
  have u_prod0 : regValue K0.core.product u.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans pre.prod0
  have u_out : regValue K0.core.out u.basis = O :=
    regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))
  have u_ctrl : u.basis G0 = t.basis G0 := hprep.2.2 G0 ctrlAway
  have u_clean : K0.PairClean u.basis := by
    have keep (q : Wire) (hq : q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh,
        K0.core.workHigh, K0.core.cin, K0.core.normFlag, K0.core.modFlag]) : u.basis q = t.basis q :=
      hprep.2.2 q (K0.measured_sum_aux_away nd q hq)
    exact ⟨(regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans pre.clean.pad,
      (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans pre.clean.work,
      (keep _ (by simp)).trans pre.clean.productHigh, (keep _ (by simp)).trans pre.clean.outHigh,
      (keep _ (by simp)).trans pre.clean.workHigh, (keep _ (by simp)).trans pre.clean.cin,
      (keep _ (by simp)).trans pre.clean.normFlag, (keep _ (by simp)).trans pre.clean.modFlag⟩
  have u_ext0 : regValue E0 u.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => hext.away q hq (OwnDiagAll12Square.sum_in K0 G0 q bad)))).trans pre.ext0
  have u_d0 : u.basis D0 = false :=
    (hprep.2.2 D0 (fun bad => (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (OwnDiagAll12Square.sum_in K0 G0 D0 bad))).trans pre.d0
  let M := if t.basis G0 then A + B else 0
  let V := C163Low4Offsets.resCFlow (t.basis G0) (M ^ 2) O
  have hM_eq : (if u.basis G0 = true then regValue cfgC.src u.basis else 0) = M := by
    change (if u.basis G0 = true then regValue K0.core.sum u.basis else 0) = M
    rw [u_ctrl, hprep.2.1]
  have used := withSplitPark_correct cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC V
    g.1 (by decide) g.2.1 g.2.2.1 g.2.2.2.1
    (fun h hh => (g.2.2.2.2.1 h hh).1) (fun h hh => (g.2.2.2.2.1 h hh).2.1)
    (fun h hh => (g.2.2.2.2.1 h hh).2.2.1) (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.1)
    g.2.2.2.2.2.1 (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.2) g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.1
    (fun q hq => Or.inl (g.2.2.2.2.2.2.2.2.1 q hq)) e0_dis_bodyC bodyC_avoids_workTC
    (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2) g.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    cfgC_zeros u mM u_clean u_prod0 u_ext0 u_d0
    (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (fun t' m' hdst hkeep => by
      have haux : ∀ q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh, K0.core.workHigh,
            K0.core.cin, K0.core.normFlag, K0.core.modFlag, D0, G0], q ∉ cfgC.dst :=
        StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [cfgC_fast, K0_eq, D0_eq, G0_eq]; decide +kernel)
      have hpc : K0.PairClean t'.basis := ⟨
        (regValue_congr _ _ _ (fun q hq => hkeep q (haux q (by simp [hq])))).trans u_clean.pad,
        (regValue_congr _ _ _ (fun q hq => hkeep q (haux q (by simp [hq])))).trans u_clean.work,
        (hkeep _ (haux _ (by simp))).trans u_clean.productHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.outHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.workHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.cin,
        (hkeep _ (haux _ (by simp))).trans u_clean.normFlag,
        (hkeep _ (haux _ (by simp))).trans u_clean.modFlag⟩
      have hG : t'.basis G0 = t.basis G0 := (hkeep G0 (haux _ (by simp))).trans u_ctrl
      have hout : regValue K0.core.out t'.basis = O :=
        (regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.2 hq))).trans u_out
      have hdstM : regValue K0.core.product t'.basis = M ^ 2 := by rw [← hM_eq]; exact hdst
      have hfr := bodyC_ok.frame t'.basis M hdstM hpc (fun hg => by rw [hG] at hg; simp [M, hg])
        ((hkeep _ (haux _ (by simp))).trans u_d0) O pre.outLt t' m' ⟨hout, fun _ _ => rfl⟩
      rw [hG] at hfr
      exact ⟨hfr.1, hfr.2.1, hfr.2.2⟩)
  change (run midNew mM u).phase = u.phase ∧ regValue K0.core.out (run midNew mM u).basis = V ∧
    ∀ q, q ∉ K0.core.out → (run midNew mM u).basis q = u.basis q at used
  generalize hv : run midNew mM u = v at hbrC used ⊢
  let restoreBase : BasisState := fun q => if q ∈ K0.core.out then v.basis q else t.basis q
  have lowRestore : regValue srcA restoreBase = A :=
    regValue_congr _ _ _ (fun q hq => by simp [restoreBase, srcA_out q hq])
  have padRestore : regValue K0.core.pad restoreBase = 0 :=
    (regValue_congr _ _ _ (fun q hq => by
      have away := (K0.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad, hq])).2
      simp [restoreBase, away])).trans (PairClean.corePad K0 t.basis pre.clean)
  have cinRestore : restoreBase K0.core.cin = false := by
    have away := (K0.pairAuxAway nd K0.core.cin (by simp)).2
    simp [restoreBase, away, pre.clean.cin]
  have workRestore : regValue K0.core.work restoreBase = 0 :=
    (regValue_congr _ _ _ (fun q hq => by
      have away := (K0.pairAuxAway nd q (by simp [hq])).2
      simp [restoreBase, away])).trans pre.clean.work
  have clearPre : SquareFrame K0.core.sum restoreBase (A + B) v.basis := by
    refine ⟨(regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans hprep.2.1, ?_⟩
    intro q hq
    by_cases outSite : q ∈ K0.core.out
    · simp [restoreBase, outSite]
    · simp only [restoreBase, if_neg outSite]
      exact (used.2.2 q outSite).trans (hprep.2.2 q hq)
  have cleared := gClearO_frame restoreBase A B lowRestore hSumBd padRestore cinRestore workRestore v mC clearPre
  generalize hout : run gClearO mC v = out at hbrC cleared ⊢
  have hNew : out.phase = t.phase ∧ regValue K0.core.out out.basis = V ∧ ∀ q, q ∉ K0.core.out → out.basis q = t.basis q := by
    refine ⟨cleared.1.trans (used.1.trans hprep.1), ?_, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => by
        have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
        simpa [restoreBase, hq] using same)).trans used.2.1
    · intro q hq
      by_cases sumSite : q ∈ K0.core.sum
      · exact (regValue_eq_iff K0.core.sum out.basis t.basis).mp cleared.2.1 q sumSite
      · have same := cleared.2.2 q sumSite
        simpa [restoreBase, hq] using same
  rw [hbrC]
  exact ⟨hNew.1, hNew.2.1, hNew.2.2⟩

/-! ## The square core with bit 0 of its input on `G0` -/

def coreO : Program := coreN brCo brB brAo

/-- The square core with bit 0 of its input on `G0`: the stock core contract for the input
`Y = srcA + 2^128 * high` (bit 0 is the generic flag). -/
theorem coreO_correct (O : Nat) (hO : O < SquareReduction.p) (s : State) (records : List Bool)
    (ho : regValue K0.core.out s.basis = O)
    (hp0 : regValue K0.core.product s.basis = 0) (hs0 : s.basis K0.core.sumCarry = false)
    (hc : K0.PairClean s.basis) (hz : regValue E0 s.basis = 0) (hd0 : s.basis D0 = false) :
    (run coreO records s).phase = s.phase ∧
    regValue K0.core.out (run coreO records s).basis =
      SquareReduction.p - 1 -
        (((O + SquareReduction.p - (if s.basis G0 then
            (regValue srcA s.basis + 2^128 * regValue K0.core.high s.basis)^2 else 0) % SquareReduction.p) %
            SquareReduction.p +
          (if s.basis G0 then C163Low4Offsets.squareK else 0)) % SquareReduction.p) ∧
    ∀ q, q ∉ K0.core.out → (run coreO records s).basis q = s.basis q := by
  let Y := regValue srcA s.basis + 2^128 * regValue K0.core.high s.basis
  have hw := hwK
  have hn := controlND
  have he := hext
  have nd := (List.nodup_cons.mp hn).2
  have disInput := K0.measured_input_out_disjoint nd
  have disProduct := K0.product_out_disjoint nd
  have ctrlAway : G0 ∉ K0.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by
      simp [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, bad])
  let A := regValue srcA s.basis
  let B := regValue K0.core.high s.basis
  let enabled := s.basis G0
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := C163Low4Offsets.resCFlow enabled PC O
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := A161Low4Offsets.resAFlow PA OB enabled
  have lowAway (q : Wire) (hq : q ∈ K0.core.low) : q ∉ K0.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q ∈ K0.core.high) : q ∉ K0.core.out :=
    List.disjoint_left.mp disInput
      (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q ∈ K0.core.sum) : q ∉ K0.core.out :=
    List.disjoint_left.mp (K0.measured_sum_disjoint nd).2 hq
  have sumB : regValue K0.core.sum s.basis = B := by
    simp [CuccaroStreamedSquareLayout.sum, regValue_append, regValue, hs0, B]
  have ab : A < 2^128 := by
    have h := regValue_lt srcA s.basis
    rwa [srcA_len] at h
  have bb : B < 2^128 := by
    simpa [B, K0.core.high_length hw.core] using regValue_lt K0.core.high s.basis
  have sumBound : A + B < 2^129 := by norm_num at ab bb ⊢; omega
  have low (X : Nat) (t : BasisState) (hf : SquareFrame K0.core.out s.basis X t) :
      regValue srcA t = A := regValue_congr _ _ _ (fun q hq => hf.2 q (srcA_out q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame K0.core.out s.basis X t) :
      regValue K0.core.high t = B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame K0.core.out s.basis X t) :
      regValue K0.core.sum t = B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame K0.core.out s.basis X t) :
      regValue K0.core.product t = 0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame K0.core.out s.basis X t) :
      regValue E0 t = 0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out K0 G0 E0 he q hq))).trans hz
  have dAway : D0 ∉ K0.core.out := fun bad => hdW (List.mem_cons_of_mem G0 (by
    simp [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, bad]))
  have sumOff : K0.core.sumCarry ∉ K0.core.out := (ParkCarryDevelop.sumCarry_off_regs K0 nd).1
  have dT (X : Nat) (t : BasisState) (hf : SquareFrame K0.core.out s.basis X t) : t D0 = false :=
    (hf.2 D0 dAway).trans hd0
  have pre (X : Nat) (hX : X < SquareReduction.p) (t : State)
      (hf : SquareFrame K0.core.out s.basis X t.basis) : BranchPre t :=
    ⟨by rw [hf.1]; exact hX, prod _ _ hf, K0.squareFrame_clean nd s.basis t.basis X hf hc,
      (hf.2 _ sumOff).trans hs0, extZ _ _ hf, dT _ _ hf⟩
  have stepC : Triple (SquareFrame K0.core.out s.basis O) brCo (SquareFrame K0.core.out s.basis OC) := by
    intro t m hf
    have h := brCo_frame t m (pre O hO t hf)
    rw [hf.2 G0 ctrlAway, low _ _ hf, sum _ _ hf, hf.1] at h
    exact ⟨h.1, h.2.1, fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have ocLt : OC < SquareReduction.p := by
    dsimp only [OC, C163Low4Offsets.resCFlow, C163Low4Body.resCFK]; exact ofCast_lt _ _
  have stepB : Triple (SquareFrame K0.core.out s.basis OC) brB (SquareFrame K0.core.out s.basis OB) := by
    intro t m hf
    have e := brB_run_eq t m (pre OC ocLt t hf)
    have h := recBrB_correct bodyB bodyB_ok B OC ocLt t m (high _ _ hf) hf.1 (prod _ _ hf)
      (K0.squareFrame_clean nd s.basis t.basis OC hf hc) ((hf.2 _ sumOff).trans hs0) (extZ _ _ hf)
    rw [← e, hf.2 G0 ctrlAway] at h
    exact ⟨h.1, h.2.1, fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have obLt : OB < SquareReduction.p := ofCast_lt _ _
  have stepA : Triple (SquareFrame K0.core.out s.basis OB) brAo (SquareFrame K0.core.out s.basis OA) := by
    intro t m hf
    have h := brAo_frame t m (pre OB obLt t hf)
    rw [hf.2 G0 ctrlAway, low _ _ hf, hf.1] at h
    exact ⟨h.1, h.2.1, fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := (stepC.seq stepB).seq stepA
  obtain ⟨phase, value, frame⟩ := all s records ⟨ho, fun _ _ => rfl⟩
  have split : A + 2^128 * B = Y := rfl
  have exactResult := C163Low4Offsets.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  have oaLt : OA < SquareReduction.p := ofCast_lt _ _
  have reflected : OA = SquareReduction.p - 1 -
      (((O + SquareReduction.p - (if s.basis G0 then Y^2 else 0) % SquareReduction.p) %
          SquareReduction.p +
        (if s.basis G0 then C163Low4Offsets.squareK else 0)) % SquareReduction.p) := by
    change SquareReduction.p - 1 - OA =
      (((O + SquareReduction.p - (if s.basis G0 then Y^2 else 0) % SquareReduction.p) %
          SquareReduction.p +
        (if s.basis G0 then C163Low4Offsets.squareK else 0)) % SquareReduction.p) at exactResult
    omega
  exact ⟨phase, value.trans reflected, frame⟩


/-! ## Lifting to the dialog layout -/

/-- The core preconditions follow from a clean dialog pool (from `fastG_correct`). -/
theorem pool_pre (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (s : State)
    (hc : regValue L.dialogPool s.basis = 0) :
    regValue L.dialogStreamedSquareWide.core.product s.basis = 0 ∧
    s.basis L.dialogStreamedSquareWide.core.sumCarry = false ∧
    L.dialogStreamedSquareWide.PairClean s.basis ∧
    regValue (OwnDiagAll12Square.kext L) s.basis = 0 ∧
    s.basis (L.core.poolWire 1540) = false := by
  let K := L.dialogStreamedSquareWide
  have auxZero (q : Wire)
      (hq : q ∈ K.core.product ++ K.core.pad ++ K.core.work ++
        [K.core.productHigh, K.core.outHigh, K.core.workHigh, K.core.cin,
          K.core.normFlag, K.core.modFlag, K.core.sumCarry] ++ K.overflowPad) :
      s.basis q = false := by
    change q ∈ L.dialogStreamedSquareWide.core.product ++
      L.dialogStreamedSquareWide.core.pad ++ L.dialogStreamedSquareWide.core.work ++
      [L.dialogStreamedSquareWide.core.productHigh, L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh, L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag, L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry] ++ L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad, List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry = false := auxZero _ (by simp)
  have hp : SquareReduction.p = p := by
    norm_num [SquareReduction.p, SquareReduction.B, SquareReduction.c, p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis = 0 :=
    (regValue_zero _ _).mpr
      (fun q hq => (regValue_zero _ _).mp hc q (OwnDiagAll12Square.kext_mem L hw q hq))
  exact ⟨prod0, sum0, clean, hz, (regValue_zero _ _).mp hc _ (B3CarryPort.pool1540_facts L hw hn).2.2⟩

/-- `fastG_correct` for the core with bit 0 of its input on `G0`. -/
theorem fastO_correct (X : Nat) (Bc : Bool) (hX : X < p)
    (s : State) (m : List Bool) (hb : s.basis L0.core.generic = Bc)
    (hx : regValue L0.point.x s.basis = X)
    (hc : regValue L0.dialogPool s.basis = 0) :
    (run coreO m s).phase = s.phase ∧
    regValue L0.point.x (run coreO m s).basis =
      p - 1 - (((X + p - (if Bc then (regValue srcA s.basis + 2^128 * regValue K0.core.high s.basis) *
          (regValue srcA s.basis + 2^128 * regValue K0.core.high s.basis) else 0) % p) % p +
        (if Bc then C163Low4Offsets.squareK else 0)) % p) ∧
    ∀ q, q ∉ L0.point.x → (run coreO m s).basis q = s.basis q := by
  have pp := pool_pre L0 hw0 hn0 s hc
  have hp : SquareReduction.p = p := by
    norm_num [SquareReduction.p, SquareReduction.B, SquareReduction.c, p]
  have kernel := coreO_correct X (by simpa only [hp] using hX) s m hx pp.1 pp.2.1 pp.2.2.1 pp.2.2.2.1 pp.2.2.2.2
  simpa only [hb, hp, pow_two] using kernel


/-! ## The register: fan-out of the sign and rotation of `point.y`

`point.y = [258, …, 513]` holds `oddWord (Y/2)`. The fan-out XORs the sign (wire 513) into
wires `258 … 512`, leaving `M` (`2M+1 = ±(2R+1)`) there. The core is renamed by the rotation
`258+j ↦ 257+j` (`258 ↦ 513`), so it sees bits `1 … 255` of its input on `M` and bit 0 on `G0`. -/

def rotF (q : ℕ) : ℕ := if 259 ≤ q ∧ q ≤ 513 then q - 1 else if q = 258 then 513 else q
def rotB (q : ℕ) : ℕ := if 258 ≤ q ∧ q ≤ 512 then q + 1 else if q = 513 then 258 else q
theorem rotB_rotF (q : ℕ) : rotB (rotF q) = q := by unfold rotF rotB; split_ifs <;> omega
theorem rotF_rotB (q : ℕ) : rotF (rotB q) = q := by unfold rotF rotB; split_ifs <;> omega
/-- Rotation of `point.y` by one place. -/
def rotY : Equiv.Perm Wire := ⟨rotF, rotB, rotB_rotF, rotF_rotB⟩

theorem rotY_apply (q : Wire) : rotY q = rotF q := rfl
theorem rotY_symm_apply (q : Wire) : rotY.symm q = rotB q := rfl
theorem rotF_fix (q : ℕ) (h : q < 258 ∨ 513 < q) : rotF q = q := by unfold rotF; split_ifs <;> omega
theorem rotB_fix (q : ℕ) (h : q < 258 ∨ 513 < q) : rotB q = q := by unfold rotB; split_ifs <;> omega

theorem y_eq : L0.point.y = List.range' 258 256 := by decide +kernel
theorem x_eq : L0.point.x = List.range' 2 256 := by decide +kernel
theorem high_eq : K0.core.high = List.range' 386 128 := by decide +kernel

theorem off_y (q : ℕ) (hq : q ∉ L0.point.y) : q < 258 ∨ 513 < q := by
  rw [y_eq, List.mem_range'_1] at hq; omega

theorem rotF_mid (a : ℕ) (h1 : 259 ≤ a) (h2 : a ≤ 513) : rotF a = a - 1 := by
  unfold rotF; exact if_pos ⟨h1, h2⟩

theorem map_rot (n a : ℕ) (h1 : 259 ≤ a) (h2 : a + n ≤ 514) :
    (List.range' a n).map rotY = List.range' (a - 1) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have e : a - 1 + 1 = a + 1 - 1 := by omega
    rw [List.range'_succ, List.range'_succ, List.map_cons, ih (a + 1) (by omega) (by omega), rotY_apply,
      rotF_mid a h1 (by omega), e]

/-- The 255 sign fan-out gates. -/
def fanY : Program := (List.range' 258 255).map (fun q => Instr.CX 513 q)

theorem fan_run (c : Wire) (l : List Wire) (hnd : l.Nodup) (hc : c ∉ l) (m : List Bool) (s : State) :
    run (l.map (fun q => Instr.CX c q)) m s =
      ⟨s.phase, fun q => if q ∈ l then (s.basis q ^^ s.basis c) else s.basis q⟩ := by
  induction l generalizing s with
  | nil => apply State.extensionality <;> simp [run]
  | cons a l ih =>
    have ha : a ∉ l := (List.nodup_cons.mp hnd).1
    have hca : c ≠ a := fun e => hc (by simp [e])
    have hcl : c ∉ l := fun h => hc (List.mem_cons_of_mem _ h)
    simp only [List.map_cons, run]
    rw [ih (List.nodup_cons.mp hnd).2 hcl]
    apply State.extensionality
    · rfl
    · funext q
      simp only [writeBit, Function.update, List.mem_cons]
      by_cases h1 : q = a
      · subst h1; simp [ha, hca]
      · by_cases h2 : q ∈ l <;> simp [h1, h2, hca]

theorem fan_nd : (List.range' 258 255).Nodup := List.nodup_range'
theorem fan_c : (513 : ℕ) ∉ List.range' 258 255 := by rw [List.mem_range'_1]; omega

theorem fanY_run (m : List Bool) (s : State) :
    run fanY m s = ⟨s.phase, fun q => if q ∈ List.range' 258 255 then (s.basis q ^^ s.basis 513) else s.basis q⟩ :=
  fan_run 513 _ fan_nd fan_c m s

theorem fanY_phase (m : List Bool) (s : State) : (run fanY m s).phase = s.phase := by
  rw [fanY_run]

theorem fanY_basis (m : List Bool) (s : State) (q : Wire) :
    (run fanY m s).basis q = if q ∈ List.range' 258 255 then (s.basis q ^^ s.basis 513) else s.basis q := by
  rw [fanY_run]

theorem fanY_twice (m1 m2 : List Bool) (s : State) : run fanY m2 (run fanY m1 s) = s := by
  rw [fanY_run, fanY_run]
  apply State.extensionality
  · rfl
  · funext q
    have h513 : (513 : Wire) ∉ List.range' 258 255 := fan_c
    by_cases hq : q ∈ List.range' 258 255 <;> simp [hq, h513]

theorem fanY_off (m : List Bool) (s : State) (q : Wire) (hq : q ∉ L0.point.y) :
    (run fanY m s).basis q = s.basis q := by
  rw [fanY_run]
  have hq' := off_y q hq
  have : q ∉ List.range' 258 255 := by rw [List.mem_range'_1]; omega
  simp [this]

theorem cx_counts (c : Wire) (l : List Wire) :
    toffoliCount (l.map (fun q => Instr.CX c q)) = 0 ∧ measurementCount (l.map (fun q => Instr.CX c q)) = 0 := by
  induction l with
  | nil => exact ⟨by simp [toffoliCount], by simp [measurementCount]⟩
  | cons a l ih => exact ⟨by simpa [toffoliCount] using ih.1, by simpa [measurementCount] using ih.2⟩

theorem fanY_counts : toffoliCount fanY = 0 ∧ measurementCount fanY = 0 := cx_counts 513 _

/-- Value of the low 255 bits after the fan-out, in terms of the whole word `w`. -/
theorem fan_value (m : List Bool) (s : State) :
    let w := regValue L0.point.y s.basis
    regValue (List.range' 258 255) (run fanY m s).basis = if 2^255 ≤ w then 2^256 - 1 - w else w := by
  intro w
  have split : regValue L0.point.y s.basis =
      regValue (List.range' 258 255) s.basis + 2^255 * (if s.basis 513 then 1 else 0) := by
    have e : List.range' 258 256 = List.range' 258 255 ++ [513] := by decide
    rw [y_eq, e, regValue_append]
    simp [regValue]
  have lo := regValue_lt (List.range' 258 255) s.basis
  simp only [List.length_range'] at lo
  rw [fanY_run]
  have hv : regValue (List.range' 258 255) (fun q => if q ∈ List.range' 258 255 then (s.basis q ^^ s.basis 513) else s.basis q) =
      regValue (List.range' 258 255) (fun q => s.basis q ^^ s.basis 513) :=
    regValue_congr _ _ _ (fun q hq => by simp [hq])
  change regValue (List.range' 258 255) (fun q => if q ∈ List.range' 258 255 then (s.basis q ^^ s.basis 513) else s.basis q) = _
  rw [hv]
  cases hb : s.basis 513
  · simp only [Bool.xor_false]
    have : w = regValue (List.range' 258 255) s.basis := by simp [w, split, hb]
    rw [this, if_neg (by omega)]
  · simp only [Bool.xor_true]
    rw [regValue_complement, List.length_range']
    have : w = regValue (List.range' 258 255) s.basis + 2^255 := by simp [w, split, hb]
    rw [this, if_pos (by omega)]
    omega

theorem srcA_lit : srcA = G0 :: List.range' 259 127 := by rw [srcA, low_cons]; rfl
theorem G0_far : (G0 : ℕ) < 258 ∨ 513 < (G0 : ℕ) := by rw [G0_val]; decide

/-- The core's input, read through the rotation, is `G0 + 2 * M` with `M` the low 255 bits. -/
theorem virtual_value (t1 : State) :
    regValue srcA (pullState rotY t1).basis + 2^128 * regValue K0.core.high (pullState rotY t1).basis =
      (if t1.basis G0 then 1 else 0) + 2 * regValue (List.range' 258 255) t1.basis := by
  rw [regValue_pull, regValue_pull, srcA_lit, high_eq, List.map_cons, map_rot 127 259 (by omega) (by omega),
    map_rot 128 386 (by omega) (by omega), rotY_apply, rotF_fix _ G0_far]
  have e : List.range' 258 255 = List.range' 258 127 ++ List.range' 385 128 := by decide
  rw [e, regValue_append, List.length_range']
  show (if t1.basis G0 then 1 else 0) + 2 * regValue (List.range' 258 127) t1.basis +
      2 ^ 128 * regValue (List.range' 385 128) t1.basis = _
  ring

def placedO : Program := SquareCarryLoan719BF.place L0 coreO
theorem placedO_def : placedO = SquareCarryLoan719BF.place L0 coreO := rfl
theorem placedN_def : placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA =
    SquareCarryLoan719BF.place L0 (coreN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA) := rfl

/-- The square with its input in odd-word form. -/
def program (k : Fp) : Program :=
  fanY ++ renameProgram rotY placedO ++ fanY ++ StairEntryRehost.routed (k - (C163Low4Offsets.delta : Fp))

theorem pull_pull (f g : Wire → Wire) (s : State) : pullState g (pullState f s) = pullState (f ∘ g) s := rfl

theorem run_rotY (P : Program) (m : List Bool) (s : State) :
    run (renameProgram rotY P) m s = pullState rotY.symm (run P m (pullState rotY s)) := by
  rw [← run_rename rotY rotY.injective P m s, pull_pull]
  have : (⇑rotY ∘ ⇑rotY.symm) = id := by funext q; simp
  rw [this]; rfl


/-! ## Counts: the same Toffolis and measurements as the stock square -/

open private addInPlace_slots_eq from ECDSAAdd.Submission.Entrant.OddField

def gA (q : Wire) : Wire := if q = tW then 258 else q
theorem gA_ne (q : Wire) (h : q ≠ tW) : gA q = q := by unfold gA; exact if_neg h
theorem gA_tW : gA tW = 258 := by unfold gA; exact if_pos rfl

theorem map_gA_id (l : List Wire) (h : ∀ q ∈ l, q ≠ tW) : l.map gA = l :=
  (List.map_congr_left (fun q hq => gA_ne q (h q hq))).trans (List.map_id l)

theorem rest_ne_tW : ∀ q ∈ List.range' 259 127, q ≠ tW := fun q hq e => tW_notin_rest (e ▸ hq)

theorem srcT_map_gA : srcT.map gA = K0.core.low := by
  rw [low_cons]
  simp only [srcT, List.map_cons, gA_tW, low_cons, List.tail_cons, map_gA_id _ rest_ne_tW]

theorem bank_map_gA : cfgA.bank.map gA = cfgA.bank :=
  map_gA_id _ (fun q hq => tW_ne_of_lt _ (bank_lt _ hq))

theorem G0_gA : gA G0 = G0 := gA_ne G0 G0_ne_tW

theorem brA_split : PDSplitLeafSquare.brA =
    (((copyRegister (some G0) K0.core.low cfgA.bank ++ cfgA.make) ++
      eraseMask G0 (K0.core.low.take 120) (cfgA.bank.take 120)) ++ restA) ++ eraseMask G0 K0.core.low cfgA.bank := by
  have hc : CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 cfgA.dst) (K0.core.low.take 120) (cfgA.bank.take 120) =
      CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 cfgA.dst) (srcA.take 120) (cfgA.bank.take 120) := by
    rw [low_cons]; simp only [srcA, low_cons, List.tail_cons, List.take_succ_cons]; exact cached_head _ _ _ _ _ _
  simp only [PDSplitLeafSquare.brA, withSplitPark, restA, List.append_assoc]
  rw [← hc]; rfl

theorem make_fix (f : Wire → Wire) (hf : ∀ q, q ≠ tW → f q = q) : renameProgram f cfgA.make = cfgA.make :=
  renameProgram_fix f _ (fun q hq => hf q (fun e => make_free.1 (e ▸ hq)))
theorem restA_fix (f : Wire → Wire) (hf : ∀ q, q ≠ tW → f q = q) : renameProgram f restA = restA :=
  renameProgram_fix f _ (fun q hq => hf q (fun e => restA_tW (e ▸ hq)))

theorem brA_eq : PDSplitLeafSquare.brA = renameProgram gA brAt := by
  rw [brA_split, brAt_split]
  simp only [renameProgram_append', make_fix gA gA_ne, restA_fix gA gA_ne, pAt, pE1t, pEt,
    rename_copyRegister, rename_eraseMask, G0_gA, List.map_take, srcT_map_gA, bank_map_gA]

theorem brAo_eq : brAo = renameProgram fA brAt := by
  rw [brAo_split, brAt_split]
  simp only [renameProgram_append', make_fix fA fA_ne, restA_fix fA fA_ne, ← pAo_eq, ← pE1o_eq, ← pEo_eq]

theorem brAo_counts : toffoliCount brAo = toffoliCount PDSplitLeafSquare.brA ∧
    measurementCount brAo = measurementCount PDSplitLeafSquare.brA ∧
    Challenge.gateSlots brAo = Challenge.gateSlots PDSplitLeafSquare.brA := by
  rw [brAo_eq, brA_eq]
  exact ⟨by rw [(renameProgram_counts _ _).1, (renameProgram_counts _ _).1],
    by rw [(renameProgram_counts _ _).2, (renameProgram_counts _ _).2],
    by rw [Baselines.rename_gateSlots, Baselines.rename_gateSlots]⟩

theorem sumSrc_len : (OwnDiagAll12Square.sumSrc K0).length = 129 := (OwnDiagAll12Square.sum_lengths K0 hwK).1

theorem gPrep_counts : toffoliCount gPrepO = toffoliCount (OwnDiagAll12Square.gPrep K0) ∧
    measurementCount gPrepO = measurementCount (OwnDiagAll12Square.gPrep K0) ∧
    Challenge.gateSlots gPrepO = Challenge.gateSlots (OwnDiagAll12Square.gPrep K0) := by
  have lens := OwnDiagAll12Square.sum_lengths K0 hwK
  have a := addInPlace_counts sumSrcO K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (sumSrcO_len.trans lens.2.1.symm) (by rw [lens.2.2, lens.2.1])
  have b := addInPlace_counts (OwnDiagAll12Square.sumSrc K0) K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (lens.1.trans lens.2.1.symm) (by rw [lens.2.2, lens.2.1])
  have sa := addInPlace_slots_eq sumSrcO K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (sumSrcO_len.trans lens.2.1.symm) (by rw [sumSrcO_len, lens.2.2]) (by rw [sumSrcO_len]; omega)
  have sb := addInPlace_slots_eq (OwnDiagAll12Square.sumSrc K0) K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (lens.1.trans lens.2.1.symm) (by rw [lens.1, lens.2.2]) (by rw [lens.1]; omega)
  refine ⟨?_, ?_, ?_⟩
  · show toffoliCount (addInPlace _ _ _ _) = toffoliCount (addInPlace _ _ _ _); rw [a.1, b.1]
  · show measurementCount (addInPlace _ _ _ _) = measurementCount (addInPlace _ _ _ _); rw [a.2, b.2]
  · show Challenge.gateSlots (addInPlace _ _ _ _) = Challenge.gateSlots (addInPlace _ _ _ _)
    rw [sa, sb, sumSrcO_len, lens.1]

theorem gClear_counts : toffoliCount gClearO = toffoliCount (OwnDiagAll12Square.gClear K0) ∧
    measurementCount gClearO = measurementCount (OwnDiagAll12Square.gClear K0) ∧
    Challenge.gateSlots gClearO = Challenge.gateSlots (OwnDiagAll12Square.gClear K0) := by
  have lens := OwnDiagAll12Square.sum_lengths K0 hwK
  have a := subInPlace_counts sumSrcO K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (sumSrcO_len.trans lens.2.1.symm) (by rw [lens.2.2, lens.2.1])
  have b := subInPlace_counts (OwnDiagAll12Square.sumSrc K0) K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (lens.1.trans lens.2.1.symm) (by rw [lens.2.2, lens.2.1])
  have sa := addInPlace_slots_eq sumSrcO K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (sumSrcO_len.trans lens.2.1.symm) (by rw [sumSrcO_len, lens.2.2]) (by rw [sumSrcO_len]; omega)
  have sb := addInPlace_slots_eq (OwnDiagAll12Square.sumSrc K0) K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (lens.1.trans lens.2.1.symm) (by rw [lens.1, lens.2.2]) (by rw [lens.1]; omega)
  refine ⟨?_, ?_, ?_⟩
  · show toffoliCount (subInPlace _ _ _ _) = toffoliCount (subInPlace _ _ _ _); rw [a.1, b.1]
  · show measurementCount (subInPlace _ _ _ _) = measurementCount (subInPlace _ _ _ _); rw [a.2, b.2]
  · show Challenge.gateSlots (subInPlace _ _ _ _) = Challenge.gateSlots (subInPlace _ _ _ _)
    simp only [subInPlace, Challenge.gateSlots_append, sa, sb, sumSrcO_len, lens.1]

theorem brCo_counts : toffoliCount brCo = toffoliCount PDSplitLeafSquare.brC ∧
    measurementCount brCo = measurementCount PDSplitLeafSquare.brC ∧
    Challenge.gateSlots brCo = Challenge.gateSlots PDSplitLeafSquare.brC := by
  have hC : PDSplitLeafSquare.brC = OwnDiagAll12Square.gPrep K0 ++ withSplitPark cfgC 124 (ParkCopyS.hostsS E0) bodyC ++
      OwnDiagAll12Square.gClear K0 := rfl
  rw [hC, brCo]
  refine ⟨?_, ?_, ?_⟩
  · simp only [toffoliCount_append, gPrep_counts.1, gClear_counts.1]
  · simp only [measurementCount_append, gPrep_counts.2.1, gClear_counts.2.1]
  · simp only [Challenge.gateSlots_append, gPrep_counts.2.2, gClear_counts.2.2]

theorem place_counts (P : Program) : toffoliCount (SquareCarryLoan719BF.place L0 P) = toffoliCount P ∧
    measurementCount (SquareCarryLoan719BF.place L0 P) = measurementCount P ∧
    Challenge.gateSlots (SquareCarryLoan719BF.place L0 P) = Challenge.gateSlots P := by
  simp only [SquareCarryLoan719BF.place, (renameProgram_counts _ _).1, (renameProgram_counts _ _).2,
    Baselines.rename_gateSlots]
  exact ⟨trivial, trivial, trivial⟩

theorem placedO_counts : toffoliCount placedO =
      toffoliCount (placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA) ∧
    measurementCount placedO =
      measurementCount (placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA) ∧
    Challenge.gateSlots placedO =
      Challenge.gateSlots (placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA) := by
  have a := place_counts coreO
  have b := place_counts (coreN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA)
  have hp : placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA =
    SquareCarryLoan719BF.place L0 (coreN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA) := rfl
  rw [placedO, hp, a.1, a.2.1, a.2.2, b.1, b.2.1, b.2.2, coreO, coreN, coreN]
  exact ⟨by simp only [toffoliCount_append, brCo_counts.1, brAo_counts.1],
    by simp only [measurementCount_append, brCo_counts.2.1, brAo_counts.2.1],
    by simp only [Challenge.gateSlots_append, brCo_counts.2.2, brAo_counts.2.2]⟩

/-! ## The square with its input in odd-word form -/

theorem run_mc0 (P : Program) (h : measurementCount P = 0) (m m' : List Bool) (s : State) :
    run P m s = run P m' s := by
  rw [← run_take P m s, ← run_take P m' s, h]; rfl

theorem run_take' (P : Program) (m : List Bool) (s : State) (k : Nat) (hk : k = measurementCount P) :
    run P (m.take k) s = run P m s := by rw [hk]; exact run_take P m s

theorem x_not_y (q : ℕ) (hq : q ∈ L0.point.x) : q ∉ L0.point.y := by
  rw [x_eq, List.mem_range'_1] at hq; rw [y_eq, List.mem_range'_1]; omega

theorem pool_off (q : Wire) (hq : q ∈ L0.dialogPool) : q ∉ L0.point.x ∧ q ∉ L0.point.y :=
  (E1QubitPlacement.lay L0 hw0 hn0 q).2.1 hq

theorem G0_off_y : G0 ∉ L0.point.y := ((E1QubitPlacement.lay L0 hw0 hn0 _).2.2 rfl).2

theorem rot_off (q : Wire) (hq : q ∉ L0.point.y) : rotY q = q ∧ rotY.symm q = q :=
  ⟨by rw [rotY_apply]; exact rotF_fix q (off_y q hq), by rw [rotY_symm_apply]; exact rotB_fix q (off_y q hq)⟩

theorem rot_y (q : Wire) (hq : q ∈ L0.point.y) : rotY.symm q ∈ L0.point.y := by
  rw [rotY_symm_apply]; rw [y_eq, List.mem_range'_1] at hq ⊢; unfold rotB; split_ifs <;> omega

section MainRun
attribute [local irreducible] fanY placedO coreO placedN coreN StairEntryRehost.routed PDSplitLeafSquare.brA
  PDSplitLeafSquare.brB PDSplitLeafSquare.brC brAo brCo SquareCarryLoan719BF.place

/-- **The square, input in odd-word form** (the shape of `SqOddContract.SquareOddNC`), given the
two side facts `halg` (the odd-word algebra) and `hTy` (the routed tail avoids `point.y`). -/
theorem program_run (k : Fp)
    (halg : ∀ Y : Fp, (1 + 2 * (if 2 ^ 255 ≤ EntryFuseOdd.oddWord (Y / 2) then
      2 ^ 256 - 1 - EntryFuseOdd.oddWord (Y / 2) else EntryFuseOdd.oddWord (Y / 2))) ^ 2 % p = Y.val ^ 2 % p)
    (hTy : ∀ q ∈ wires (StairEntryRehost.routed (k - (C163Low4Offsets.delta : Fp))), q ∉ L0.point.y)
    (hmc : measurementCount placedO =
      measurementCount (placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA))
    (X Y : Fp) (G : Bool) (origin : BasisState) (s t : State) (m : List Bool)
    (v : PointDialogValues L0 X Y G origin s.basis) (hph : t.phase = s.phase)
    (hag : ∀ q, q ∉ L0.point.y → t.basis q = s.basis q)
    (hy : regValue L0.point.y t.basis = EntryFuseOdd.oddWord (Y / 2)) :
    (run (program k) m t).phase = (run (Stair44Square.program k) m s).phase ∧
    regValue L0.point.y (run (program k) m t).basis = EntryFuseOdd.oddWord (Y / 2) ∧
    ∀ q, q ∉ L0.point.y → (run (program k) m t).basis q = (run (Stair44Square.program k) m s).basis q := by
  let T := StairEntryRehost.routed (k - (C163Low4Offsets.delta : Fp))
  let core := coreN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA
  let n := measurementCount placedO
  have hn : measurementCount (fanY ++ renameProgram rotY placedO ++ fanY) = n := by
    rw [measurementCount_append, measurementCount_append, fanY_counts.2, (renameProgram_counts rotY placedO).2,
      Nat.zero_add, Nat.add_zero]
  have hold : Stair44Square.program k = placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA ++ T := rfl
  have hnew : program k = (fanY ++ renameProgram rotY placedO ++ fanY) ++ T := rfl
  have hrunOld : run (placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA ++ T) m s =
      run T (m.drop n) (run (placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA) (m.take n) s) := by
    rw [run_append, ← hmc]
  have hrunNew : run ((fanY ++ renameProgram rotY placedO ++ fanY) ++ T) m t =
      run T (m.drop n) (run (fanY ++ renameProgram rotY placedO ++ fanY) (m.take n) t) := by
    rw [run_append, hn]
  rw [hold, hnew, hrunOld, hrunNew]
  -- the new run up to the tail
  let mt := m.take n
  have e1 : run (fanY ++ renameProgram rotY placedO ++ fanY) mt t =
      run fanY [] (run (renameProgram rotY placedO) mt (run fanY [] t)) := by
    rw [run_append, run_mc0 fanY fanY_counts.2 _ [], run_append, run_mc0 fanY fanY_counts.2 _ [],
      fanY_counts.2, List.drop_zero,
      run_take' (renameProgram rotY placedO) mt _ (measurementCount (fanY ++ renameProgram rotY placedO))
        (by rw [measurementCount_append, fanY_counts.2, Nat.zero_add]), List.take_zero]
  rw [e1]
  generalize ht1 : run fanY [] t = t1
  have t1_off : ∀ q, q ∉ L0.point.y → t1.basis q = s.basis q := fun q hq => by
    rw [← ht1, fanY_off _ _ _ hq, hag q hq]
  have t1_ph : t1.phase = s.phase := by rw [← ht1, fanY_phase]; exact hph
  rw [run_rotY]
  -- the core on the rotated state
  generalize hW : pullState rotY t1 = w0
  have w0_off : ∀ q, q ∉ L0.point.y → w0.basis q = s.basis q := fun q hq => by
    rw [← hW, pullState_basis, (rot_off q hq).1, t1_off q hq]
  have w0_ph : w0.phase = s.phase := by rw [← hW, pullState_phase, t1_ph]
  have w0_clean : regValue L0.dialogPool w0.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => w0_off q (pool_off q hq).2)).trans v.clean
  have w0_x : regValue L0.point.x w0.basis = X.val :=
    (regValue_congr _ _ _ (fun q hq => w0_off q (x_not_y q hq))).trans v.x
  have w0_g : w0.basis L0.core.generic = G := (w0_off _ G0_off_y).trans v.generic
  have fN := fastO_correct X.val G X.isLt w0 mt w0_g w0_x w0_clean
  have pN : run placedO mt w0 = run coreO mt w0 := by
    rw [placedO_def]
    exact ReflectionE1Square.place_run_eq L0 hw0 coreO w0 mt w0_clean
      ((regValue_congr _ _ _ (fun q hq => fN.2.2 q (pool_off q hq).1)).trans w0_clean)
  -- the stock core on the canonical state
  have fO := fastG_correct L0 hw0 hn0 core Stair44Square.coreOK X.val Y.val G X.isLt s mt v.generic v.x v.y v.clean
  have pO : run (placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA) mt s = run core mt s := by
    rw [placedN_def]
    exact ReflectionE1Square.place_run_eq L0 hw0 core s mt v.clean
      ((regValue_congr _ _ _ (fun q hq => fO.2.2 q (pool_off q hq).1)).trans v.clean)
  rw [pN, pO]
  -- both cores write the same value into `point.x`
  have ax : regValue L0.point.x (run coreO mt w0).basis = regValue L0.point.x (run core mt s).basis := by
    rw [fN.2.1, fO.2.1]
    cases G
    · simp
    · simp only [if_true]
      have hv := virtual_value t1
      rw [hW] at hv
      have hG1 : t1.basis G0 = true := (t1_off _ G0_off_y).trans v.generic
      have hM := fan_value [] t
      rw [ht1, hy] at hM
      have hsq : (regValue srcA w0.basis + 2^128 * regValue K0.core.high w0.basis) *
          (regValue srcA w0.basis + 2^128 * regValue K0.core.high w0.basis) % p = Y.val * Y.val % p := by
        rw [hv, hG1, hM, if_pos rfl, ← pow_two, ← pow_two]; exact halg Y
      rw [hsq]
  -- the states before the tail
  have oN := fN.2.2
  have oO := fO.2.2
  have phN := fN.1
  have phO := fO.1
  generalize hcN : run coreO mt w0 = cN at ax oN phN
  generalize hcO : run core mt s = cO at ax oO phO
  have zA : (run fanY [] (pullState rotY.symm cN)).phase = cO.phase := by
    rw [fanY_phase, pullState_phase, phN, w0_ph, phO]
  have zB : ∀ q, q ∉ L0.point.y → (run fanY [] (pullState rotY.symm cN)).basis q = cO.basis q := by
    intro q hq
    rw [fanY_off _ _ _ hq, pullState_basis, (rot_off q hq).2]
    by_cases hx : q ∈ L0.point.x
    · exact (regValue_eq_iff _ _ _).mp ax q hx
    · rw [oN q hx, oO q hx, w0_off q hq]
  have uY : ∀ q, q ∈ L0.point.y → (pullState rotY.symm cN).basis q = t1.basis q := by
    intro q hq
    have hr := rot_y q hq
    rw [pullState_basis, oN _ (fun hx => x_not_y _ hx hr), ← hW, pullState_basis, Equiv.apply_symm_apply]
  have zC : ∀ q, q ∈ L0.point.y → (run fanY [] (pullState rotY.symm cN)).basis q = t.basis q := by
    intro q hq
    have h513 : (513 : Wire) ∈ L0.point.y := by rw [y_eq, List.mem_range'_1]; omega
    have e : (run fanY [] (pullState rotY.symm cN)).basis q = (run fanY [] t1).basis q := by
      rw [fanY_basis, fanY_basis, uY q hq, uY 513 h513]
    rw [e, ← ht1, fanY_twice]
  -- the tail avoids `point.y`
  generalize hz : run fanY [] (pullState rotY.symm cN) = z at zA zB zC
  have loc := pool_run_agrees T (wires T) (Finset.Subset.refl _) (m.drop n) z cO zA
    (fun w hw => zB w (hTy w hw))
  refine ⟨loc.1, ?_, ?_⟩
  · rw [regValue_congr L0.point.y _ t.basis (fun q hq => by
      rw [run_preserves_outside _ _ _ _ (fun hw => hTy q hw hq)]; exact zC q hq)]
    exact hy
  · intro q hq
    by_cases hw : q ∈ wires T
    · exact loc.2 q hw
    · rw [run_preserves_outside _ _ _ _ hw, run_preserves_outside _ _ _ _ hw]; exact zB q hq

end MainRun

/-! ## Wires, sites and physical validity of the new square -/

theorem wires_fanY : ∀ x ∈ wires fanY, x ∈ L0.point.y := by
  have h : ∀ l : List Wire, (∀ q ∈ l, q ∈ L0.point.y) → (513 : Wire) ∈ L0.point.y →
      ∀ x ∈ wires (l.map (fun q => Instr.CX 513 q)), x ∈ L0.point.y := by
    intro l hl h513 x hx
    induction l with
    | nil => simp [wires] at hx
    | cons a l ih =>
      simp only [List.map_cons, wires, Finset.mem_union, Instr.wires, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with (rfl | rfl) | hx
      · exact h513
      · exact hl _ (by simp)
      · exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hx
  apply h
  · intro q hq; rw [y_eq, List.mem_range'_1] at *; omega
  · rw [y_eq, List.mem_range'_1]; omega

theorem wires_brAo : ∀ x ∈ wires brAo, x ∈ wires PDSplitLeafSquare.brA ∨ x = G0 := by
  intro x hx
  rw [brAo_eq, renameProgram_support, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  by_cases h : y = tW
  · right; rw [h, fA_tW]
  · left; rw [fA_ne y h, brA_eq, renameProgram_support, Finset.mem_image]; exact ⟨y, hy, gA_ne y h⟩

theorem sumSrcO_sub : ∀ x ∈ sumSrcO, x ∈ OwnDiagAll12Square.sumSrc K0 ∨ x = G0 := by
  intro x hx
  rw [sumSrcO, srcA_lit, List.cons_append, List.mem_cons] at hx
  rcases hx with h | h
  · exact Or.inr h
  · left; rw [OwnDiagAll12Square.sumSrc, low_cons, List.cons_append]; exact List.mem_cons_of_mem _ h

theorem wires_brCo : ∀ x ∈ wires brCo, x ∈ wires PDSplitLeafSquare.brC ∨ x = G0 := by
  have lens := OwnDiagAll12Square.sum_lengths K0 hwK
  have hx1 : sumSrcO.length = K0.core.sum.length := sumSrcO_len.trans lens.2.1.symm
  have hx2 : (OwnDiagAll12Square.sumSrc K0).length = K0.core.sum.length := lens.1.trans lens.2.1.symm
  have hc : (OwnDiagAll12Square.sumBank K0).length + 1 = K0.core.sum.length := by rw [lens.2.2, lens.2.1]
  have hC : PDSplitLeafSquare.brC = OwnDiagAll12Square.gPrep K0 ++ withSplitPark cfgC 124 (ParkCopyS.hostsS E0) bodyC ++
      OwnDiagAll12Square.gClear K0 := rfl
  have key : ∀ x ∈ (K0.core.cin :: (sumSrcO ++ K0.core.sum ++ OwnDiagAll12Square.sumBank K0)),
      x ∈ (K0.core.cin :: (OwnDiagAll12Square.sumSrc K0 ++ K0.core.sum ++ OwnDiagAll12Square.sumBank K0)) ∨ x = G0 := by
    intro x hx
    simp only [List.mem_cons, List.mem_append] at hx ⊢
    rcases hx with h | (h | h) | h
    · exact Or.inl (Or.inl h)
    · rcases sumSrcO_sub x h with h' | h'
      · exact Or.inl (Or.inr (Or.inl (Or.inl h')))
      · exact Or.inr h'
    · exact Or.inl (Or.inr (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inr (Or.inr h))
  intro x hx
  rw [brCo, wires_append, wires_append, Finset.mem_union, Finset.mem_union] at hx
  rw [hC, wires_append, wires_append, Finset.mem_union, Finset.mem_union]
  rcases hx with (h | h) | h
  · rw [gPrepO, addInPlace_wires _ _ _ _ hx1 hc, List.mem_toFinset] at h
    rcases key x h with h' | h'
    · left; left; left; rw [OwnDiagAll12Square.gPrep, addInPlace_wires _ _ _ _ hx2 hc, List.mem_toFinset]; exact h'
    · exact Or.inr h'
  · exact Or.inl (Or.inl (Or.inr h))
  · rw [gClearO, subInPlace_wires _ _ _ _ hx1 hc, List.mem_toFinset] at h
    rcases key x h with h' | h'
    · left; right; rw [OwnDiagAll12Square.gClear, subInPlace_wires _ _ _ _ hx2 hc, List.mem_toFinset]; exact h'
    · exact Or.inr h'

theorem wires_coreO : ∀ x ∈ wires coreO,
    x ∈ wires (coreN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA) ∨ x = G0 := by
  intro x hx
  simp only [coreO, coreN, wires_append, Finset.mem_union] at hx ⊢
  rcases hx with (h | h) | h
  · rcases wires_brCo x h with h' | h'
    · exact Or.inl (Or.inl (Or.inl h'))
    · exact Or.inr h'
  · exact Or.inl (Or.inl (Or.inr h))
  · rcases wires_brAo x h with h' | h'
    · exact Or.inl (Or.inr h')
    · exact Or.inr h'

theorem placeFn_G0 : placeFn G0 = G0 := by rw [StairSquareSites.LT48K.placeFn_eq, G0_val]; decide +kernel

theorem wires_placedO : ∀ x ∈ wires placedO,
    x ∈ wires (placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA) ∨ x = G0 := by
  intro x hx
  rw [placedO, placed_wires, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rcases wires_coreO y hy with h | rfl
  · left; unfold placedN; rw [placed_wires, Finset.mem_image]; exact ⟨y, h, rfl⟩
  · right; exact placeFn_G0

/-- Every wire of the new square is a wire of the stock square, of `point.y`, or `G0`. -/
theorem wires_program (k : Fp) : ∀ x ∈ wires (program k),
    x ∈ wires (Stair44Square.program k) ∨ x ∈ L0.point.y ∨ x = G0 := by
  have hold : Stair44Square.program k = placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA ++
      StairEntryRehost.routed (k - (C163Low4Offsets.delta : Fp)) := rfl
  intro x hx
  rw [program, wires_append, wires_append, wires_append, Finset.mem_union, Finset.mem_union, Finset.mem_union] at hx
  rw [hold, wires_append, Finset.mem_union]
  rcases hx with ((h | h) | h) | h
  · exact Or.inr (Or.inl (wires_fanY x h))
  · rw [renameProgram_support, Finset.mem_image] at h
    obtain ⟨y, hy, rfl⟩ := h
    by_cases hyy : y ∈ L0.point.y
    · right; left; rw [rotY_apply]
      have := hyy; rw [y_eq, List.mem_range'_1] at this ⊢; unfold rotF; split_ifs <;> omega
    · rw [(rot_off y hyy).1]
      rcases wires_placedO y hy with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr (Or.inr h')
  · exact Or.inr (Or.inl (wires_fanY x h))
  · exact Or.inl (Or.inr h)

theorem fanY_physical : GatePhysical fanY := by
  unfold GatePhysical
  intro i hi
  simp only [fanY, List.mem_map] at hi
  obtain ⟨q, hq, rfl⟩ := hi
  show (513 : Wire) ≠ q
  intro e; rw [← e] at hq; exact fan_c hq

theorem srcA_bank_nodup : (srcA ++ cfgA.bank).Nodup := by
  have nd := (cfgA_geom).2.2.2.2.2.2.1
  change (G0 :: K0.core.low ++ cfgA.bank).Nodup at nd
  rw [low_cons] at nd
  rw [srcA_lit]
  simp only [List.cons_append, List.nodup_cons, List.mem_cons, List.mem_append, not_or] at nd ⊢
  exact ⟨⟨nd.1.2.1, nd.1.2.2⟩, nd.2.2⟩

theorem brAo_physical : GatePhysical brAo := by
  have hA := PDSplitLeafSquare.brA_physical
  rw [brA_split, gatePhysical_append, gatePhysical_append, gatePhysical_append, gatePhysical_append] at hA
  rw [brAo_split, gatePhysical_append, gatePhysical_append, gatePhysical_append, gatePhysical_append]
  refine ⟨⟨⟨⟨?_, hA.1.1.1.2⟩, eraseMask_physical _ _ _⟩, hA.1.2⟩, eraseMask_physical _ _ _⟩
  exact copyRegister_physical (some G0) srcA cfgA.bank srcA_bank_nodup
    (fun c hc => by cases Option.some.inj hc; exact G0_notin_bank)

theorem brCo_physical : GatePhysical brCo := by
  have hC := PDSplitLeafSquare.brC_physical
  have hCe : PDSplitLeafSquare.brC = OwnDiagAll12Square.gPrep K0 ++ withSplitPark cfgC 124 (ParkCopyS.hostsS E0) bodyC ++
      OwnDiagAll12Square.gClear K0 := rfl
  rw [hCe, gatePhysical_append, gatePhysical_append] at hC
  have nd : (K0.core.cin :: sumSrcO ++ K0.core.sum ++ OwnDiagAll12Square.sumBank K0).Nodup := by
    simpa [List.append_assoc] using sumO_nodup
  rw [brCo, gatePhysical_append, gatePhysical_append]
  exact ⟨⟨addInPlace_physical _ _ _ _ nd, hC.1.2⟩, subInPlace_physical _ _ _ _ nd⟩

theorem placedO_physical : GatePhysical placedO := by
  rw [placedO, R2SqEp760.place_physical_iff, coreO, coreN, gatePhysical_append, gatePhysical_append]
  exact ⟨⟨brCo_physical, PDSplitLeafSquare.brB_physical⟩, brAo_physical⟩

theorem program_physical (k : Fp) : GatePhysical (program k) := by
  have old := Stair44Square.physical k
  have hold : Stair44Square.program k = placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA ++
      StairEntryRehost.routed (k - (C163Low4Offsets.delta : Fp)) := rfl
  rw [hold, gatePhysical_append] at old
  rw [program, gatePhysical_append, gatePhysical_append, gatePhysical_append]
  exact ⟨⟨⟨fanY_physical, gatePhysical_rename _ rotY.injective _ placedO_physical⟩, fanY_physical⟩, old.2⟩

open private good_sites from ECDSAAdd.Submission.Entrant.MainP1

theorem yG_good : ∀ q ∈ G0 :: L0.point.y, Stair44TailBounds.good (StairPlaceFast.ugB q) = true := by
  have h : (G0 :: L0.point.y).all (fun q => Stair44TailBounds.good (StairPlaceFast.ugB q)) = true := by
    rw [y_eq, G0_val]; decide +kernel
  exact fun q hq => List.all_eq_true.mp h q hq

/-- The new square sits on sites of the stock square, `point.y` and `G0` only. -/
theorem program_sites (k : Fp) : StairSiteAvoidance.PieceOK Stair44Release.holes StairSiteAvoidance.UG (program k) := by
  have old := Stair44Release.squareSites k
  have hsub : ∀ q ∈ Stair44Release.holes, q ∈ Stair44Square.hs := by
    change ∀ q ∈ StairPhysicalInventory.physicalHoles, _
    rw [StairPhysicalLayout.physicalHoles_eq_nat, Stair44Square.hs_eq]
    decide +kernel
  have extra (q : Wire) (hq : q ∈ G0 :: L0.point.y) :
      (StairSiteAvoidance.UG q ∈ StairHoleSupport.recordArena ∧ StairSiteAvoidance.UG q ∉ StairHoleSupport.oldHoles) ∧
        StairSiteAvoidance.UG q ∉ Stair44Release.holes := by
    have g := good_sites _ (yG_good q hq)
    have maps : StairSiteAvoidance.UG q = StairPlaceFast.ugB q := StairPlaceFast.ug_eqB q
    rw [maps]
    exact ⟨⟨g.1, g.2.1⟩, fun h => g.2.2 (hsub _ h)⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases wires_program k x hx with h | h | h
    · exact old.1 x h
    · exact (extra x (List.mem_cons_of_mem _ h)).1
    · exact (extra x (by rw [h]; exact List.mem_cons_self)).1
  · rcases wires_program k x hx with h | h | h
    · exact old.2 x h
    · exact (extra x (List.mem_cons_of_mem _ h)).2
    · exact (extra x (by rw [h]; exact List.mem_cons_self)).2

/-- Same Toffoli and measurement counts as the stock square; 510 more gate slots (the fan-outs). -/
theorem program_counts (k : Fp) :
    toffoliCount (program k) = toffoliCount (Stair44Square.program k) ∧
    measurementCount (program k) = measurementCount (Stair44Square.program k) ∧
    Challenge.gateSlots (program k) = Challenge.gateSlots (Stair44Square.program k) + 510 := by
  have hold : Stair44Square.program k = placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA ++
      StairEntryRehost.routed (k - (C163Low4Offsets.delta : Fp)) := rfl
  have fs : Challenge.gateSlots fanY = 255 := by
    show Challenge.gateSlots ((List.range' 258 255).map (fun q => Instr.CX 513 q)) = 255
    have h : ∀ l : List Wire, Challenge.gateSlots (l.map (fun q => Instr.CX 513 q)) = l.length := by
      intro l; induction l with
      | nil => simp [Baselines.gateSlots_nil]
      | cons a l ih => simp only [List.map_cons, Baselines.gateSlots_cons, Challenge.instructionSlots, ih,
          List.length_cons]; omega
    rw [h, List.length_range']
  have pc := placedO_counts
  rw [program, hold]
  refine ⟨?_, ?_, ?_⟩
  · rw [toffoliCount_append, toffoliCount_append, toffoliCount_append, toffoliCount_append, fanY_counts.1,
      (renameProgram_counts rotY placedO).1, pc.1]; omega
  · rw [measurementCount_append, measurementCount_append, measurementCount_append, measurementCount_append,
      fanY_counts.2, (renameProgram_counts rotY placedO).2, pc.2.1]; omega
  · rw [Challenge.gateSlots_append, Challenge.gateSlots_append, Challenge.gateSlots_append,
      Challenge.gateSlots_append, fs, Baselines.rename_gateSlots, pc.2.2]; omega

/-! ## One repeated control (`CCX G0 G0 _`), removed by the entry's normalization -/

theorem rc_append (p q : Program) :
    Baselines.repeatedControls (p ++ q) = Baselines.repeatedControls p + Baselines.repeatedControls q := by
  induction p with
  | nil => simp [Baselines.repeatedControls]
  | cons i p ih =>
    cases i <;> (simp only [List.cons_append, Baselines.repeatedControls, ih]; try omega)

theorem rc_rename (f : Wire → Wire) (p : Program) :
    Baselines.repeatedControls p ≤ Baselines.repeatedControls (renameProgram f p) := by
  induction p with
  | nil => exact Nat.le_refl _
  | cons i p ih =>
    have e : renameProgram f (i :: p) = renameInstr f i :: renameProgram f p := rfl
    rw [e]
    cases i with
    | CCX a b t =>
      simp only [renameInstr, Baselines.repeatedControls]
      by_cases h : a = b
      · subst h; simp only [if_true]; omega
      · simp only [h, if_false]; split <;> omega
    | X t => simpa only [renameInstr, Baselines.repeatedControls] using ih
    | CX c t => simpa only [renameInstr, Baselines.repeatedControls] using ih
    | measureX t c0 c1 => simpa only [renameInstr, Baselines.repeatedControls] using ih

theorem rc_place (L : ControlledPointLayout) (P : Program) :
    Baselines.repeatedControls P ≤ Baselines.repeatedControls (SquareCarryLoan719BF.place L P) := by
  dsimp only [SquareCarryLoan719BF.place]
  repeat refine le_trans ?_ (rc_rename _ _)
  exact le_refl _

theorem pAo_rc : 1 ≤ Baselines.repeatedControls pAo := by
  obtain ⟨b, bs, hb⟩ : ∃ b bs, cfgA.bank = b :: bs := by
    cases h : cfgA.bank with
    | nil =>
      have h1 := cfgA_valid.bankLen
      have h2 : cfgA.n = 128 := rfl
      rw [h, h2] at h1; simp at h1
    | cons b bs => exact ⟨b, bs, rfl⟩
  rw [pAo, srcA_lit, hb]
  simp only [copyRegister, copyGate, List.singleton_append, Baselines.repeatedControls, if_true]
  omega

theorem program_rc (k : Fp) : 1 ≤ Baselines.repeatedControls (program k) := by
  have a := pAo_rc
  have hb : Baselines.repeatedControls pAo ≤ Baselines.repeatedControls brAo := by
    rw [brAo_split, rc_append, rc_append, rc_append, rc_append]; omega
  have hc : Baselines.repeatedControls brAo ≤ Baselines.repeatedControls coreO := by
    rw [coreO, coreN, rc_append, rc_append]; omega
  have hp : Baselines.repeatedControls coreO ≤ Baselines.repeatedControls placedO := by
    rw [placedO_def]; exact rc_place L0 coreO
  have hr := rc_rename rotY placedO
  rw [program, rc_append, rc_append, rc_append]
  omega

end ECDSAAdd.Entrant.SquareOdd
