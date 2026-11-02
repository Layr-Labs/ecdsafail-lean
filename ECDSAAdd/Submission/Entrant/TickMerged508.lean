import ECDSAAdd.Submission.Entrant.FusedFlags

/-! Reverse ticks 510, 509 and 508 as one forced block (9 Toffolis instead of 11 for the
merged ticks 510/509 followed by tick 508).  The circuit was found by exhaustive search
over the forced states at tick 508 (`u+v ≤ 8`, terminating within three more steps) and is
checked here on every forced state and every measurement record.  Builds on the 509/510
merge of terrapinelf (f753049b), ported by e-man07 (e1b7db22, a6dcb576). -/

section

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 History5

/-- Gate list of repairedTick base 508. -/
def tick508ExF : Program :=
  [.CX 787 525, .CX 788 526, .CX 789 527, .CCX 524 525 787, .CCX 524 526 788, .CCX 524 527 789,
    .CX 787 525, .CX 788 526, .CX 789 527, .CX 528 790, .measureX 528 [] [.CZ 523 790],
    .CX 790 528, .CX 528 790, .CX 789 790, .CX 789 528, .CX 524 786, .CX 528 529, .X 1552,
    .CX 528 1552, .CX 789 1552, .CX 1552 525, .CX 1552 526, .CX 1552 527, .CX 1552 528,
    .CX 525 786, .CX 525 1552, .CCX 786 1552 1556, .CX 525 1556, .CX 525 1552, .CX 525 786,
    .CX 526 787, .CX 526 1556, .CCX 787 1556 1557, .CX 526 1557, .CX 526 1556, .CX 526 787,
    .CX 527 788, .CX 527 1557, .CCX 788 1557 1558, .CX 527 1558, .CX 527 1557, .CX 527 788,
    .CX 528 789, .CX 1558 789, .measureX 1558 [] [.CZ 527 788, .CZ 527 1557, .CZ 788 1557],
    .CX 527 788, .CX 1557 788, .measureX 1557 [] [.CZ 526 787, .CZ 526 1556, .CZ 787 1556],
    .CX 526 787, .CX 1556 787, .measureX 1556 [] [.CZ 525 786, .CZ 525 1552, .CZ 786 1552],
    .CX 525 786, .CX 1552 786, .CX 1552 525, .CX 1552 526, .CX 1552 527, .CX 1552 528, .X 1552,
    .CX 528 1552, .CX 789 1552, .CX 1552 790, .CX 523 524, .CX 528 529, .CX 789 790]

/-- Gate list of compactReceiverTick base 508. -/
def tick508ExR : Program :=
  [.CX 789 790, .CX 528 529, .CX 523 524, .CX 1552 790, .X 1552, .CX 528 1552, .CX 789 1552,
    .X 786, .X 787, .X 788, .X 789, .CX 1552 525, .CX 1552 526, .CX 1552 527, .CX 1552 528,
    .CX 525 786, .CX 525 1552, .CCX 786 1552 1556, .CX 525 1556, .CX 525 1552, .CX 525 786,
    .CX 526 787, .CX 526 1556, .CCX 787 1556 1557, .CX 526 1557, .CX 526 1556, .CX 526 787,
    .measureX 789 [] [.CZ 527 788, .CZ 527 1557, .CZ 788 1557], .CX 528 789, .CX 527 788,
    .CX 1557 788, .measureX 1557 [] [.CZ 526 787, .CZ 526 1556, .CZ 787 1556], .CX 526 787,
    .CX 1556 787, .measureX 1556 [] [.CZ 525 786, .CZ 525 1552, .CZ 786 1552], .CX 525 786,
    .CX 1552 786, .CX 1552 525, .CX 1552 526, .CX 1552 527, .CX 1552 528, .X 786, .X 787, .X 788,
    .X 789, .X 1552, .CX 528 1552, .CX 789 1552, .CX 528 529, .CX 524 786, .CX 787 525,
    .CX 788 526, .CX 789 527, .CX 790 528, .CCX 524 525 787, .CCX 524 526 788, .CCX 524 527 789,
    .CCX 524 528 790, .CX 787 525, .CX 788 526, .CX 789 527, .CX 790 528]

/-- Reverse ticks 510, 509 and 508 on the forward outputs of ticks 508-510. -/
def tickMR8 : Program :=
  [.CX 1553 1552, .CX 1554 1552, .CCX 523 1552 528, .CX 1554 1553, .X 1553, .CX 526 525,
    .CCX 1553 525 529, .CX 525 524, .CX 526 524, .CX 529 526, .CX 1554 526, .X 526,
    .CCX 524 526 787, .CX 529 525, .CX 1552 525, .CX 1553 525, .CX 1554 525, .CX 525 529,
    .CX 787 529, .CX 1552 529, .CX 1553 529, .CX 1554 529, .CCX 525 529 788, .CX 525 524,
    .CX 526 524, .CX 529 524, .CX 787 524, .CX 1552 524, .CX 1553 524, .X 524, .CX 524 525,
    .CX 526 525, .CX 529 525, .CX 787 525, .CX 788 525, .CX 1552 525, .CX 1553 525, .X 525,
    .CCX 524 525 789, .CX 525 524, .CX 789 524, .CCX 523 524 790, .X 1552, .CX 788 525,
    .CCX 1552 525 1556, .CX 524 523, .CX 525 523, .CX 529 523, .CX 787 523, .CX 788 523,
    .CX 789 523, .CX 1556 526, .X 526, .CCX 523 526 1557, .CX 525 523, .CX 529 523, .CX 787 523,
    .CX 526 525, .CX 529 525, .CX 787 525, .CX 788 525, .CX 1552 525, .CX 1553 525, .CX 1554 525,
    .CCX 523 525 1558, .X 786, .CX 527 786, .X 789, .CX 524 789, .CX 527 789, .CX 788 789,
    .CX 1558 1557, .CX 1558 1556, .CX 1558 790, .CX 1558 789, .CX 1558 787, .CX 1558 524,
    .CX 1557 1556, .CX 1557 1554, .CX 1557 527, .CX 1557 523, .CX 1556 1558, .CX 1556 1557,
    .CX 1556 790, .CX 1556 789, .CX 1556 788, .CX 1556 529, .CX 1556 524, .CX 1554 1556,
    .CX 1554 1553, .CX 1554 788, .CX 1554 787, .CX 1554 527, .CX 1554 523, .CX 1556 1554,
    .CX 1553 1558, .CX 1553 1557, .CX 1553 1554, .CX 1553 790, .CX 1553 789, .CX 1553 788,
    .CX 1553 787, .CX 1553 529, .CX 1553 527, .CX 1553 524, .CX 1553 523, .CX 1554 1553,
    .CX 1552 1558, .CX 1552 789, .CX 1552 525, .CX 790 1558, .CX 790 1554, .CX 790 1553,
    .CX 790 1552, .CX 790 789, .CX 790 788, .CX 790 787, .CX 790 524, .CX 1552 790, .CX 789 1558,
    .CX 1558 789, .CX 788 1554, .CX 788 529, .CX 788 527, .CX 788 523, .CX 1554 788, .CX 787 1556,
    .CX 787 788, .CX 787 527, .CX 787 525, .CX 787 523, .CX 788 787, .CX 529 1557, .CX 529 1553,
    .CX 529 788, .CX 529 527, .CX 529 525, .CX 529 523, .CX 528 1554, .CX 528 1552, .CX 528 790,
    .CX 528 789, .CX 528 529, .CX 528 524, .CX 527 1557, .CX 527 1554, .CX 527 1553, .CX 527 788,
    .CX 527 787, .CX 527 524, .CX 527 523, .CX 526 1557, .CX 526 1554, .CX 526 788, .CX 526 787,
    .CX 526 525, .CX 787 526, .CX 525 1557, .CX 525 1554, .CX 525 1552, .CX 525 529, .CX 525 527,
    .CX 525 526, .CX 525 524, .CX 526 525, .CX 524 1554, .CX 524 1552, .CX 524 788, .CX 524 527,
    .CX 524 526, .CX 526 524, .CX 523 1554, .CX 523 1552, .CX 523 789, .CX 523 788, .CX 523 787,
    .CX 523 527, .CX 523 526, .CX 523 525, .CX 523 524, .X 523, .X 526, .X 529, .X 787, .X 788,
    .X 790, .X 1552, .X 1553, .X 1554,
    .measureX 1557 [] [.Z 523, .Z 524, .Z 525, .Z 527, .Z 528, .Z 787, .Z 789, .Z 529, .Z 1552, .CZ 524 525, .CZ 524 787],
    .measureX 1557 [] [], .X 1556,
    .measureX 1556 [] [.Z 524, .Z 525, .Z 527, .Z 528, .Z 787, .Z 789, .Z 529, .Z 1552, .Z 1554, .CZ 523 526, .CZ 523 787, .CZ 523 788, .CZ 523 529, .CZ 523 1552, .CZ 524 527, .CZ 524 787, .CZ 524 529, .CZ 524 1552],
    .X 1554,
    .measureX 1554 [] [.Z 523, .Z 524, .Z 525, .Z 527, .Z 787, .Z 790, .Z 529, .Z 1552, .CZ 524 526, .CZ 524 788],
    .measureX 1553 [] [.Z 527, .Z 790, .Z 529, .Z 1552, .CZ 523 526, .CZ 523 787, .CZ 523 788, .CZ 523 529, .CZ 523 1552, .CZ 524 526, .CZ 524 527, .CZ 524 787, .CZ 524 788, .CZ 524 529, .CZ 524 1552, .CZ 525 787],
    .measureX 1552 [] [.Z 523, .Z 528, .Z 788, .CZ 523 524, .CZ 523 525, .CZ 523 526, .CZ 523 788, .CZ 524 526, .CZ 524 527, .CZ 524 787, .CZ 524 529, .CZ 525 788, .CZ 525 789, .CZ 525 529, .CZ 526 790, .CZ 526 529, .CZ 527 787, .CZ 527 788, .CZ 527 790, .CZ 527 529],
    .measureX 529 [] [.Z 523, .Z 524, .Z 525, .Z 526, .Z 527, .Z 528, .Z 787, .CZ 523 526, .CZ 523 788, .CZ 524 526, .CZ 524 788, .CZ 525 789, .CZ 525 790, .CZ 526 789, .CZ 527 787, .CZ 527 788, .CZ 528 787],
    .CX 524 786, .X 786]

/-- The eighteen physical wires of ticks 508 to 510. -/
def sitesT8 : List Wire :=
  [523, 524, 525, 526, 527, 528, 529, 786, 787, 788, 789, 790, 1552, 1553, 1554, 1556, 1557, 1558]

/-- The wires of tick 508 itself. -/
def sites508 : List Wire :=
  [523, 524, 525, 526, 527, 528, 529, 786, 787, 788, 789, 790, 1552, 1556, 1557, 1558]

/-- The coprime pairs `(u,v)` with odd `v`, `u+v ≤ 8`, that terminate within three steps. -/
def pairs508 : List (Nat × Nat) :=
  [(0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (1, 3), (2, 3), (5, 3), (1, 5),
   (3, 5), (1, 7)]

/-- Forced input of tick 508: orientation `G`, five-bit rails `encode G S u v`. -/
def pre508 (G S : Bool) (u v : Nat) : BasisState := fun q =>
  if q = 523 then G
  else if q = 524 then decide ((SkywalkRails.encode G S (u : Int) (v : Int)).a % 2 = 1)
  else if q = 525 then decide ((SkywalkRails.encode G S (u : Int) (v : Int)).a / 2 % 2 = 1)
  else if q = 526 then decide ((SkywalkRails.encode G S (u : Int) (v : Int)).a / 4 % 2 = 1)
  else if q = 527 then decide ((SkywalkRails.encode G S (u : Int) (v : Int)).a / 8 % 2 = 1)
  else if q = 528 then decide ((SkywalkRails.encode G S (u : Int) (v : Int)).a < 0)
  else if q = 786 then decide ((SkywalkRails.encode G S (u : Int) (v : Int)).b % 2 = 1)
  else if q = 787 then decide ((SkywalkRails.encode G S (u : Int) (v : Int)).b / 2 % 2 = 1)
  else if q = 788 then decide ((SkywalkRails.encode G S (u : Int) (v : Int)).b / 4 % 2 = 1)
  else if q = 789 then decide ((SkywalkRails.encode G S (u : Int) (v : Int)).b / 8 % 2 = 1)
  else if q = 790 then decide ((SkywalkRails.encode G S (u : Int) (v : Int)).b < 0)
  else false

theorem tick508ExF_explicit : W.repairedTick base 508 = tick508ExF := by decide +kernel
theorem tick508ExR_explicit : W.ReverseCarry.compactReceiverTick base 508 = tick508ExR := by
  decide +kernel

/-- Forward ticks 508 to 510. -/
abbrev tripF : Program := tick508ExF ++ tick509ExF ++ tick510ExF
/-- Reverse ticks 510, 509, 508. -/
abbrev tripR : Program := tick510ExR ++ tick509ExR ++ tick508ExR

theorem tripF_wires : wires tripF ⊆ sitesT8.toFinset := by decide +kernel
theorem tripR_wires : wires tripR ⊆ sitesT8.toFinset := by decide +kernel
theorem tickMR8_wires : wires tickMR8 ⊆ sitesT8.toFinset := by decide +kernel
theorem sitesT8_pool : ∀ q ∈ sitesT8, q ∈ skywalkPoolWires base := by decide +kernel
theorem tick508_wires : wires tick508ExF ⊆ sites508.toFinset := by decide +kernel
theorem sites508_tick : ∀ q ∈ sites508, q ∈ wires (W.compactSkywalkTick base 508) := by
  decide +kernel

theorem tickN_counts :
    toffoliCount tickMR8 = 9 ∧ measurementCount tickMR8 = 7 ∧
    toffoliCount tripR = 13 ∧ measurementCount tripR = 7 := by decide +kernel

theorem tickN_physical : GatePhysical tickMR8 := by
  simp (config := { maxSteps := 4000000 }) [tickMR8, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]


/-! Compact simulation: the basis state is a single natural number (bit `q` is wire `q`), so the
kernel evaluates gates with GMP arithmetic instead of nested `Function.update` closures.
`run_sim_t8` proves once that this simulation is faithful. -/

def tbN_t8 (b : Nat) : BasisState := fun q => b.testBit q

def corrP_t8 : List Correction → Bool → Nat → Bool
  | [], ph, _ => ph
  | .Z t :: cs, ph, b => corrP_t8 cs (ph ^^ b.testBit t) b
  | .CZ x y :: cs, ph, b => corrP_t8 cs (ph ^^ (b.testBit x && b.testBit y)) b

def flipN_t8 (b t : Nat) (c : Bool) : Nat := if c then b ^^^ 2^t else b

def runN_t8 : Program → List Bool → Bool × Nat → Bool × Nat
  | [], _, s => s
  | .X t :: p, m, s => runN_t8 p m (s.1, s.2 ^^^ 2^t)
  | .CX c t :: p, m, s => runN_t8 p m (s.1, flipN_t8 s.2 t (s.2.testBit c))
  | .CCX a b t :: p, m, s => runN_t8 p m (s.1, flipN_t8 s.2 t (s.2.testBit a && s.2.testBit b))
  | .measureX t c₀ c₁ :: p, m, s =>
      runN_t8 p m.tail
        (corrP_t8 (if m.headD false then c₁ else c₀) (s.1 ^^ (m.headD false && s.2.testBit t))
          (flipN_t8 s.2 t (s.2.testBit t)),
         flipN_t8 s.2 t (s.2.testBit t))

theorem testBit_flipN_t8 (b t q : Nat) (c : Bool) :
    (flipN_t8 b t c).testBit q = (b.testBit q ^^ (c && decide (t = q))) := by
  cases c <;> simp [flipN_t8, Nat.testBit_xor, Nat.testBit_two_pow]

theorem writeBit_tbN_t8 (b t : Nat) (c : Bool) :
    writeBit (tbN_t8 b) t (tbN_t8 b t ^^ c) = tbN_t8 (flipN_t8 b t c) := by
  funext q
  by_cases h : q = t
  · subst h; simp [writeBit, tbN_t8, testBit_flipN_t8]
  · have h' : ¬ (t = q) := fun e => h e.symm
    simp [writeBit, tbN_t8, testBit_flipN_t8, Function.update, h, h']

theorem corr_sim_t8 (cs : List Correction) (ph : Bool) (b : Nat) :
    correct cs ⟨ph, tbN_t8 b⟩ = ⟨corrP_t8 cs ph b, tbN_t8 b⟩ := by
  induction cs generalizing ph with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [correct, corrP_t8, ih, tbN_t8]

theorem run_sim_t8 (P : Program) (m : List Bool) (ph : Bool) (b : Nat) :
    run P m ⟨ph, tbN_t8 b⟩ = ⟨(runN_t8 P m (ph, b)).1, tbN_t8 (runN_t8 P m (ph, b)).2⟩ := by
  induction P generalizing m ph b with
  | nil => rfl
  | cons i P ih =>
    cases i with
    | X t =>
      have e : writeBit (tbN_t8 b) t (!tbN_t8 b t) = tbN_t8 (b ^^^ 2^t) := by
        funext q
        by_cases h : q = t
        · subst h; simp [writeBit, tbN_t8, Nat.testBit_xor, Nat.testBit_two_pow]
        · have h' : ¬ (t = q) := fun e => h e.symm
          simp [writeBit, tbN_t8, Nat.testBit_xor, Nat.testBit_two_pow, Function.update, h, h']
      simp only [run, runN_t8, e]; exact ih _ _ _
    | CX c t =>
      have e := writeBit_tbN_t8 b t (tbN_t8 b c)
      simp only [run, runN_t8]
      have e2 : writeBit (tbN_t8 b) t (tbN_t8 b t ^^ tbN_t8 b c) = tbN_t8 (flipN_t8 b t (b.testBit c)) := e
      simp only [e2]; exact ih _ _ _
    | CCX x y t =>
      have e := writeBit_tbN_t8 b t (tbN_t8 b x && tbN_t8 b y)
      simp only [run, runN_t8]
      have e2 : writeBit (tbN_t8 b) t (tbN_t8 b t ^^ (tbN_t8 b x && tbN_t8 b y)) =
          tbN_t8 (flipN_t8 b t (b.testBit x && b.testBit y)) := e
      simp only [e2]; exact ih _ _ _
    | measureX t c₀ c₁ =>
      have e2 : writeBit (tbN_t8 b) t false = tbN_t8 (flipN_t8 b t (b.testBit t)) := by
        funext q
        by_cases h : q = t
        · subst h; simp [writeBit, tbN_t8, testBit_flipN_t8]
        · have h' : ¬ (t = q) := fun e => h e.symm
          simp [writeBit, tbN_t8, testBit_flipN_t8, Function.update, h, h']
      simp only [run, runN_t8, measureAndCorrect, e2, corr_sim_t8]
      generalize m.headD false = mm
      cases mm <;> exact ih _ _ _

def encN_t8 (f : BasisState) (l : List Wire) : Nat :=
  l.foldl (fun a w => if f w then a ||| 2^w else a) 0

theorem foldl_tb_t8 (f : BasisState) (l : List Wire) (a q : Nat) :
    (l.foldl (fun a w => if f w then a ||| 2^w else a) a).testBit q =
      (a.testBit q || (decide (q ∈ l) && f q)) := by
  induction l generalizing a with
  | nil => simp
  | cons w l ih =>
    simp only [List.foldl, ih]
    by_cases hf : f w = true
    · by_cases hq : q = w
      · subst hq; simp [hf, Nat.testBit_or, Nat.testBit_two_pow]
      · have hq' : ¬ (w = q) := fun e => hq e.symm
        simp [hf, Nat.testBit_or, Nat.testBit_two_pow, hq, hq']
    · simp [hf]
      by_cases hq : q = w
      · subst hq; simp [hf]
      · simp [hq]

theorem tb_enc_t8 (f : BasisState) (l : List Wire) (h : ∀ q, f q = true → q ∈ l) :
    f = tbN_t8 (encN_t8 f l) := by
  funext q
  simp only [tbN_t8, encN_t8, foldl_tb_t8, Nat.zero_testBit, Bool.false_or]
  cases hf : f q
  · simp
  · simp [h q hf]

theorem pre508_supp (G S : Bool) (u v : Nat) : ∀ q, pre508 G S u v q = true → q ∈ sitesT8 := by
  intro q h
  unfold pre508 at h
  split_ifs at h <;> (subst_vars; simp [sitesT8])

def padk_t8 : Nat → List Bool → List Bool
  | 0, _ => []
  | k+1, m => m.headD false :: padk_t8 k m.tail

def runAll_t8 : Program → Bool × Nat → List (List Bool × (Bool × Nat))
  | [], s => [([], s)]
  | .X t :: p, s => runAll_t8 p (s.1, s.2 ^^^ 2^t)
  | .CX c t :: p, s => runAll_t8 p (s.1, flipN_t8 s.2 t (s.2.testBit c))
  | .CCX a b t :: p, s => runAll_t8 p (s.1, flipN_t8 s.2 t (s.2.testBit a && s.2.testBit b))
  | .measureX t c₀ c₁ :: p, s =>
      (runAll_t8 p (corrP_t8 c₀ (s.1 ^^ (false && s.2.testBit t)) (flipN_t8 s.2 t (s.2.testBit t)),
          flipN_t8 s.2 t (s.2.testBit t))).map (fun rx => (false :: rx.1, rx.2)) ++
      (runAll_t8 p (corrP_t8 c₁ (s.1 ^^ (true && s.2.testBit t)) (flipN_t8 s.2 t (s.2.testBit t)),
          flipN_t8 s.2 t (s.2.testBit t))).map (fun rx => (true :: rx.1, rx.2))

theorem runAll_spec1_t8 (P : Program) (m : List Bool) (s : Bool × Nat) :
    (padk_t8 (measurementCount P) m, runN_t8 P m s) ∈ runAll_t8 P s := by
  induction P generalizing m s with
  | nil => simp [runAll_t8, runN_t8, padk_t8, measurementCount]
  | cons i P ih =>
    cases i with
    | X t => simp only [measurementCount, runAll_t8, runN_t8]; exact ih _ _
    | CX c t => simp only [measurementCount, runAll_t8, runN_t8]; exact ih _ _
    | CCX a b t => simp only [measurementCount, runAll_t8, runN_t8]; exact ih _ _
    | measureX t c₀ c₁ =>
      simp only [measurementCount]
      rw [show 1 + measurementCount P = measurementCount P + 1 by omega]
      simp only [padk_t8, runAll_t8, runN_t8, List.mem_append, List.mem_map]
      cases hm : m.headD false
      · left
        exact ⟨_, ih m.tail _, by simp⟩
      · right
        exact ⟨_, ih m.tail _, by simp⟩

theorem runAll_spec2_t8 (P : Program) (m : List Bool) (s : Bool × Nat) (r : List Bool)
    (x : Bool × Nat) (h : (r, x) ∈ runAll_t8 P s) (hr : padk_t8 (measurementCount P) m = r) :
    x = runN_t8 P m s := by
  induction P generalizing m s r x with
  | nil => simp [runAll_t8, runN_t8] at h ⊢; exact h.2
  | cons i P ih =>
    cases i with
    | X t => simp only [measurementCount, runAll_t8, runN_t8] at h hr ⊢; exact ih _ _ _ _ h hr
    | CX c t => simp only [measurementCount, runAll_t8, runN_t8] at h hr ⊢; exact ih _ _ _ _ h hr
    | CCX a b t => simp only [measurementCount, runAll_t8, runN_t8] at h hr ⊢; exact ih _ _ _ _ h hr
    | measureX t c₀ c₁ =>
      simp only [measurementCount] at hr
      rw [show 1 + measurementCount P = measurementCount P + 1 by omega] at hr
      simp only [padk_t8] at hr
      simp only [runAll_t8, List.mem_append, List.mem_map] at h
      simp only [runN_t8]
      rcases h with ⟨⟨r', y⟩, hy, he⟩ | ⟨⟨r', y⟩, hy, he⟩
      · simp only [Prod.mk.injEq] at he
        obtain ⟨he1, he2⟩ := he
        subst he2; subst he1
        simp only [List.cons.injEq] at hr
        obtain ⟨hr1, hr2⟩ := hr
        rw [hr1]
        exact ih _ _ _ _ hy hr2
      · simp only [Prod.mk.injEq] at he
        obtain ⟨he1, he2⟩ := he
        subst he2; subst he1
        simp only [List.cons.injEq] at hr
        obtain ⟨hr1, hr2⟩ := hr
        rw [hr1]
        exact ih _ _ _ _ hy hr2

theorem runN_eq_of_all_t8 (P Q : Program) (s : Bool × Nat)
    (hk : measurementCount P = measurementCount Q)
    (h : decide (runAll_t8 P s = runAll_t8 Q s) = true) (m : List Bool) :
    runN_t8 P m s = runN_t8 Q m s := by
  have h' : runAll_t8 P s = runAll_t8 Q s := of_decide_eq_true h
  have mem := runAll_spec1_t8 P m s
  rw [h'] at mem
  exact runAll_spec2_t8 Q m s _ _ mem (by rw [hk])

def chkT_t8 (P Q F : Program) (e : Nat) : Bool :=
  decide (runAll_t8 P (false, (runN_t8 F [] (false, e)).2) = runAll_t8 Q (false, (runN_t8 F [] (false, e)).2))

theorem conc_nat_t8 (P Q F : Program) (sites : List Wire) (e : Nat)
    (hk : measurementCount P = measurementCount Q) (h : chkT_t8 P Q F e = true) (c : List Bool) :
    (run P c ⟨false, (run F [] ⟨false, tbN_t8 e⟩).basis⟩).phase =
      (run Q c ⟨false, (run F [] ⟨false, tbN_t8 e⟩).basis⟩).phase ∧
    ∀ q ∈ sites,
      (run P c ⟨false, (run F [] ⟨false, tbN_t8 e⟩).basis⟩).basis q =
        (run Q c ⟨false, (run F [] ⟨false, tbN_t8 e⟩).basis⟩).basis q := by
  have eq := runN_eq_of_all_t8 P Q (false, (runN_t8 F [] (false, e)).2) hk h c
  rw [run_sim_t8 F [] false e]
  simp only [run_sim_t8]
  rw [eq]
  exact ⟨rfl, fun _ _ => rfl⟩

def chkPair_t8 (uv : Nat × Nat) : Bool :=
  [false, true].all fun G => [false, true].all fun S =>
    chkT_t8 tripR tickMR8 tripF (encN_t8 (pre508 G S uv.1 uv.2) sitesT8)

theorem chkP_0_1 : chkPair_t8 (0, 1) = true := by decide +kernel
theorem chkP_1_1 : chkPair_t8 (1, 1) = true := by decide +kernel
theorem chkP_2_1 : chkPair_t8 (2, 1) = true := by decide +kernel
theorem chkP_3_1 : chkPair_t8 (3, 1) = true := by decide +kernel
theorem chkP_4_1 : chkPair_t8 (4, 1) = true := by decide +kernel
theorem chkP_5_1 : chkPair_t8 (5, 1) = true := by decide +kernel
theorem chkP_6_1 : chkPair_t8 (6, 1) = true := by decide +kernel
theorem chkP_7_1 : chkPair_t8 (7, 1) = true := by decide +kernel
theorem chkP_1_3 : chkPair_t8 (1, 3) = true := by decide +kernel
theorem chkP_2_3 : chkPair_t8 (2, 3) = true := by decide +kernel
theorem chkP_5_3 : chkPair_t8 (5, 3) = true := by decide +kernel
theorem chkP_1_5 : chkPair_t8 (1, 5) = true := by decide +kernel
theorem chkP_3_5 : chkPair_t8 (3, 5) = true := by decide +kernel
theorem chkP_1_7 : chkPair_t8 (1, 7) = true := by decide +kernel

theorem chkAll_true_t8 : pairs508.all chkPair_t8 = true := by
  simp only [pairs508, List.all_cons, List.all_nil, Bool.and_true, chkP_0_1, chkP_1_1, chkP_2_1, chkP_3_1, chkP_4_1, chkP_5_1, chkP_6_1, chkP_7_1, chkP_1_3, chkP_2_3, chkP_5_3, chkP_1_5, chkP_3_5, chkP_1_7]

theorem concMR8 : ∀ G S : Bool, ∀ uv ∈ pairs508, ∀ c ∈ recsUpTo 7,
    (run tripR c ⟨false, (run tripF [] ⟨false, pre508 G S uv.1 uv.2⟩).basis⟩).phase =
      (run tickMR8 c ⟨false, (run tripF [] ⟨false, pre508 G S uv.1 uv.2⟩).basis⟩).phase ∧
    ∀ q ∈ sitesT8,
      (run tripR c ⟨false, (run tripF [] ⟨false, pre508 G S uv.1 uv.2⟩).basis⟩).basis q =
        (run tickMR8 c ⟨false, (run tripF [] ⟨false, pre508 G S uv.1 uv.2⟩).basis⟩).basis q := by
  intro G S uv huv c _
  have h := chkAll_true_t8
  simp only [List.all_eq_true] at h
  have h1 := h uv huv
  simp only [chkPair_t8, List.all_eq_true] at h1
  have h1 := h1 G (by cases G <;> simp) S (by cases S <;> simp)
  have hk : measurementCount tripR = measurementCount tickMR8 := by
    obtain ⟨_, c2, _, c4⟩ := tickN_counts
    exact c4.trans c2.symm
  rw [tb_enc_t8 (pre508 G S uv.1 uv.2) sitesT8 (pre508_supp G S uv.1 uv.2)]
  exact conc_nat_t8 _ _ _ _ _ hk h1 c

theorem signed5_cases (a b c d e : Wire) (s : BasisState) (v : Int)
    (h : signedRegValue [a, b, c, d, e] s = v) :
    s a = decide (v % 2 = 1) ∧ s b = decide (v / 2 % 2 = 1) ∧ s c = decide (v / 4 % 2 = 1) ∧
      s d = decide (v / 8 % 2 = 1) ∧ s e = decide (v < 0) := by
  unfold signedRegValue signedDecode at h
  simp only [regValue, List.length] at h
  cases ha : s a <;> cases hb : s b <;> cases hc : s c <;> cases hd : s d <;> cases he : s e <;>
    simp [ha, hb, hc, hd, he] at h <;> subst h <;> decide

theorem pairs508_of (z : SkywalkNat.State) (hs : z.u + z.v ≤ 8) (h0 : 0 < z.v) (h1 : z.v % 2 = 1)
    (hg : z.u.gcd z.v = 1) (ht : (SkywalkNat.step^[3] z).u = 0) : (z.u, z.v) ∈ pairs508 := by
  obtain ⟨u, v⟩ := z
  simp only at hs h0 h1 hg ht ⊢
  have hv : v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7 := by omega
  rcases hv with rfl | rfl | rfl | rfl <;>
  · have hu : u ≤ 7 := by omega
    clear hs h0 h1
    interval_cases u <;> revert hg ht <;> decide

theorem retainedA508 :
    (W.compactSkywalkSignPoolA base 508).retained =
      [base 508, base 509, base 510, base 511, base 512] := by
  decide +kernel
theorem retainedB508 :
    (W.compactSkywalkSignPoolB base 508).retained =
      [base 770, base 771, base 772, base 773, base 774] := by
  decide +kernel
theorem releasedA508 : base 513 ∈ (W.compactSkywalkSignPoolA base 508).released := by
  decide +kernel

theorem sites509_sub : ∀ q ∈ [1553], q ∈ wires (W.compactSkywalkTick base 509) := by
  decide +kernel
theorem sites510_sub : ∀ q ∈ [1554], q ∈ wires (W.compactSkywalkTick base 510) := by
  decide +kernel

attribute [local irreducible] run W.compactSkywalkStageVirtual SkywalkTrace.next Nat.iterate
  W.compactSkywalkTick History5.encodePrefix

/-- The compressed stage before tick 508 pins the eighteen wires of ticks 508 to 510 to one
of the forced inputs. -/
theorem stage508_bits (x : Nat) (hx0 : 0 < x) (hx : x < p) (s : State)
    (stage : W.CompressedCompactStage5 base x p 508 s.basis) :
    ∃ G S : Bool, ∃ uv ∈ pairs508, ∀ q ∈ sitesT8, s.basis q = pre508 G S uv.1 uv.2 q := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := (StackOB5.prime_facts x hx0 hx).2.2.2
  obtain ⟨raw, hraw, hbits⟩ := stage
  have fields := (W.compactSkywalkStage_fields_iff base _ 508 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨readA, readB, prev, -, future, carry, -, cleanA, -⟩ := fields
  obtain ⟨G, S, encoded⟩ := SkywalkTrace.iter_encoded 508 false false (SkywalkNat.init x p) hp0 hpo
  have sum := W.iter_sum_width x p 508 hp0 hx0 hpo hp hx cop (by omega)
  have valid := SkywalkNat.iter_valid 508 (SkywalkNat.init x p) hp0 hpo
  have term := (SkywalkNat.terminates_511 p x hp0 hx0 hpo hp hx cop).1
  have split : SkywalkNat.step^[511] (SkywalkNat.init x p) =
      SkywalkNat.step^[3] (SkywalkNat.step^[508] (SkywalkNat.init x p)) := by
    rw [← Function.iterate_add_apply]
  rw [split] at term
  change (SkywalkNat.step^[508] (SkywalkNat.init x p)).u+
    (SkywalkNat.step^[508] (SkywalkNat.init x p)).v ≤ 2^(511-508) at sum
  change SkywalkTrace.next^[508] (SkywalkRails.encode false false (x : Int) (p : Int)) =
    SkywalkRails.encode G S ((SkywalkNat.step^[508] (SkywalkNat.init x p)).u : Int)
      ((SkywalkNat.step^[508] (SkywalkNat.init x p)).v : Int) at encoded
  generalize SkywalkNat.step^[508] (SkywalkNat.init x p) = z at encoded sum valid term
  have eight : (2:Nat)^(511-508) = 8 := by norm_num
  rw [eight] at sum
  have mem := pairs508_of z sum valid.1 valid.2.1 (valid.2.2.trans cop) term
  rw [encoded, retainedA508] at readA
  rw [encoded, retainedB508] at readB
  rw [encoded] at prev
  have bA := signed5_cases _ _ _ _ _ raw.basis _ readA
  have bB := signed5_cases _ _ _ _ _ raw.basis _ readB
  have f8 := future 508 (le_refl _) (by omega)
  have f9 := future 509 (by omega) (by omega)
  have f10 := future 510 (by omega) (by omega)
  have c1540 : raw.basis (base 1540) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1540, by simp, rfl⟩)
  have c1541 : raw.basis (base 1541) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1541, by simp, rfl⟩)
  have c1542 : raw.basis (base 1542) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1542, by simp, rfl⟩)
  have c513 : raw.basis (base 513) = false := cleanA _ releasedA508
  have prev' : raw.basis (base 507) = G := by
    have h : skywalkPoolPreviousId 508 = 507 := rfl
    rw [h] at prev
    cases G <;> simpa [SkywalkRails.encode] using prev
  refine ⟨G, S, _, mem, ?_⟩
  have d8 := W.prefix_disjoint_compactTick base base_pool_nodup
    (by intro j hj; change 10≤j+16; omega) 508 508 (le_refl _) (by omega)
  have d9 := W.prefix_disjoint_compactTick base base_pool_nodup
    (by intro j hj; change 10≤j+16; omega) 508 509 (by omega) (by omega)
  have d10 := W.prefix_disjoint_compactTick base base_pool_nodup
    (by intro j hj; change 10≤j+16; omega) 508 510 (by omega) (by omega)
  have keep8 : ∀ q ∈ sites508, s.basis q = raw.basis q := by
    intro q hq
    rw [hbits]
    apply run_preserves_outside
    exact fun h => Finset.disjoint_left.mp d8 h (sites508_tick q hq)
  have keep9 : s.basis 1553 = raw.basis 1553 := by
    rw [hbits]
    apply run_preserves_outside
    exact fun h => Finset.disjoint_left.mp d9 h (sites509_sub 1553 (by simp))
  have keep10 : s.basis 1554 = raw.basis 1554 := by
    rw [hbits]
    apply run_preserves_outside
    exact fun h => Finset.disjoint_left.mp d10 h (sites510_sub 1554 (by simp))
  intro q hq
  simp only [sitesT8, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · rw [keep8 _ (by decide)]; exact prev'
  · rw [keep8 _ (by decide)]; exact bA.1
  · rw [keep8 _ (by decide)]; exact bA.2.1
  · rw [keep8 _ (by decide)]; exact bA.2.2.1
  · rw [keep8 _ (by decide)]; exact bA.2.2.2.1
  · rw [keep8 _ (by decide)]; exact bA.2.2.2.2
  · rw [keep8 _ (by decide)]; exact c513
  · rw [keep8 _ (by decide)]; exact bB.1
  · rw [keep8 _ (by decide)]; exact bB.2.1
  · rw [keep8 _ (by decide)]; exact bB.2.2.1
  · rw [keep8 _ (by decide)]; exact bB.2.2.2.1
  · rw [keep8 _ (by decide)]; exact bB.2.2.2.2
  · rw [keep8 _ (by decide)]; exact f8.2
  · rw [keep9]; exact f9.2
  · rw [keep10]; exact f10.2
  · rw [keep8 _ (by decide)]; exact c1540
  · rw [keep8 _ (by decide)]; exact c1541
  · rw [keep8 _ (by decide)]; exact c1542

theorem tickMR8_records : measurementCount tickMR8=
    measurementCount (W.ReverseCarry.compactReceiverTick base 510)+
      measurementCount (W.ReverseCarry.compactReceiverTick base 509)+
        measurementCount (W.ReverseCarry.compactReceiverTick base 508) := by
  obtain ⟨_,c2,_,c4⟩ := tickN_counts
  rw [tick510ExR_explicit,tick509ExR_explicit,tick508ExR_explicit,←measurementCount_append,
    ←measurementCount_append]
  exact c2.trans c4.symm

end ECDSAAdd.Entrant
end
