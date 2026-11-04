import ECDSAAdd.Submission.Entrant.MainPart06
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed
namespace ECDSAAdd.Entrant.InverseFour15
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
def sites15 : List Wire := MorningFour.sites ++ [530]
def candidate15 : Program := [
  .X 527,
  .CX 526 527,
  .CX 526 786,
  .X 1551,
  .CX 1552 1551,
  .CX 1553 1551,
  .CX 1554 1551,
  .CCX 522 1551 527,
  .CX 1554 1551,
  .CX 1553 1551,
  .CX 1552 1551,
  .X 1551,
  .CX 526 525,
  .X 526,
  .CX 525 526,
  .CX 1553 526,
  .CX 1554 526,
  .CCX 525 526 528,
  .CX 1554 526,
  .CX 1553 526,
  .CX 525 526,
  .X 526,
  .CX 526 525,
  .CX 525 524,
  .CX 526 524,
  .X 528,
  .CX 524 528,
  .CX 1552 528,
  .CX 1554 528,
  .CCX 524 528 529,
  .CX 1554 528,
  .CX 1552 528,
  .CX 524 528,
  .X 528,
  .CX 526 524,
  .CX 525 524,
  .CX 526 524,
  .CX 528 524,
  .CX 1552 524,
  .CX 1553 524,
  .CX 524 528,
  .CX 1552 528,
  .CX 1553 528,
  .CCX 524 528 786,
  .CX 1553 528,
  .CX 1552 528,
  .CX 524 528,
  .CX 1553 524,
  .CX 1552 524,
  .CX 528 524,
  .CX 526 524,
  .CX 526 523,
  .CX 523 524,
  .CX 526 524,
  .CX 786 524,
  .CX 1552 524,
  .CCX 523 524 787,
  .CX 1552 524,
  .CX 786 524,
  .CX 526 524,
  .CX 523 524,
  .CX 526 523,
  .CX 528 524,
  .CX 1553 524,
  .CX 1554 524,
  .CX 524 525,
  .CX 526 525,
  .CX 529 525,
  .CX 786 525,
  .CX 1553 525,
  .CX 1554 525,
  .CCX 524 525 788,
  .CX 1554 525,
  .CX 1553 525,
  .CX 786 525,
  .CX 529 525,
  .CX 526 525,
  .CX 524 525,
  .CX 1554 524,
  .CX 1553 524,
  .CX 528 524,
  .measureX 528 [] [.Z 523, .Z 524, .Z 526, .Z 529, .Z 786, .Z 787, .Z 788, .CZ 523 524, .CZ 523 526, .CZ 523 786, .CZ 523 1552, .CZ 524 529, .CZ 524 1553, .CZ 525 529, .CZ 525 786, .CZ 525 1554],
  .CX 525 524,
  .CX 788 524,
  .CCX 523 524 528,
  .CX 788 524,
  .CX 525 524,
  .X 523,
  .CX 524 523,
  .CX 525 523,
  .CX 528 523,
  .CX 788 523,
  .CX 1551 523,
  .CX 1552 523,
  .CX 1553 523,
  .CX 1554 523,
  .CCX 522 523 789,
  .CX 1554 523,
  .CX 1553 523,
  .CX 1552 523,
  .CX 1551 523,
  .CX 788 523,
  .CX 528 523,
  .CX 525 523,
  .CX 524 523,
  .X 523,
  .CX 524 523,
  .X 1551,
  .CX 1552 1551,
  .CX 1553 1551,
  .CX 1554 1551,
  .CCX 523 1551 790,
  .CX 1554 1551,
  .CX 1553 1551,
  .CX 1552 1551,
  .X 1551,
  .CX 524 523,
  .X 526,
  .CX 529 526,
  .CX 786 526,
  .CX 1551 526,
  .CX 1552 526,
  .CX 1553 526,
  .CX 525 523,
  .CCX 526 523 791,
  .CX 525 523,
  .CX 1553 526,
  .CX 1552 526,
  .CX 1551 526,
  .CX 786 526,
  .CX 529 526,
  .X 526,
  .CX 523 522,
  .X 526,
  .CX 529 526,
  .CX 786 526,
  .CX 790 526,
  .CX 1554 526,
  .CCX 522 526 1556,
  .CX 1554 526,
  .CX 790 526,
  .CX 786 526,
  .CX 529 526,
  .X 526,
  .CX 523 522,
  .CX 523 522,
  .CX 522 525,
  .CX 529 525,
  .CX 788 525,
  .CX 790 525,
  .CX 791 525,
  .CX 1551 525,
  .CX 1552 525,
  .CX 1554 525,
  .CCX 522 525 1557,
  .CX 1554 525,
  .CX 1552 525,
  .CX 1551 525,
  .CX 791 525,
  .CX 790 525,
  .CX 788 525,
  .CX 529 525,
  .CX 522 525,
  .CX 523 522,
  .CX 524 522,
  .CX 529 526,
  .CX 786 526,
  .CX 790 526,
  .CX 1551 526,
  .CX 1552 526,
  .CX 1553 526,
  .CCX 522 526 1558,
  .CX 1553 526,
  .CX 1552 526,
  .CX 1551 526,
  .CX 790 526,
  .CX 786 526,
  .CX 529 526,
  .CX 524 522,
  .X 525,
  .CX 526 525,
  .CX 786 525,
  .CX 788 525,
  .CX 1551 525,
  .CX 1552 525,
  .CX 527 523,
  .CX 528 523,
  .CX 787 523,
  .CX 788 523,
  .CX 791 523,
  .CX 1556 523,
  .CX 1558 523,
  .CCX 525 523 530,
  .CX 1558 523,
  .CX 1556 523,
  .CX 791 523,
  .CX 788 523,
  .CX 787 523,
  .CX 528 523,
  .CX 527 523,
  .CX 1552 525,
  .CX 1551 525,
  .CX 788 525,
  .CX 786 525,
  .CX 526 525,
  .X 525,
  .CX 1551 529,
  .CX 1551 787,
  .CX 1551 790,
  .CX 1551 1552,
  .CX 1551 530,
  .CX 523 522,
  .X 523,
  .CX 522 523,
  .CX 525 523,
  .CX 526 523,
  .CX 528 523,
  .CX 786 523,
  .CX 788 523,
  .CX 791 523,
  .CX 1552 523,
  .CX 1556 523,
  .CX 530 523,
  .CCX 522 523 1551,
  .CX 530 523,
  .CX 1556 523,
  .CX 1552 523,
  .CX 791 523,
  .CX 788 523,
  .CX 786 523,
  .CX 528 523,
  .CX 526 523,
  .CX 525 523,
  .CX 522 523,
  .X 523,
  .CX 523 522,
  .X 788,
  .X 787,
  .X 529,
  .CX 530 1553,
  .CX 530 1552,
  .CX 530 1551,
  .CX 530 790,
  .CX 530 788,
  .CX 530 787,
  .CX 530 529,
  .CX 530 528,
  .CX 1558 1553,
  .CX 1558 1552,
  .CX 1558 790,
  .CX 1558 788,
  .CX 1558 786,
  .CX 1558 525,
  .CX 530 1558,
  .CX 1558 530,
  .CX 530 1558,
  .CX 1557 530,
  .CX 1557 1552,
  .CX 1557 791,
  .CX 1557 789,
  .CX 1557 787,
  .CX 1557 786,
  .CX 1557 526,
  .CX 1557 525,
  .CX 1558 1557,
  .CX 1557 1558,
  .CX 1558 1557,
  .CX 1556 1558,
  .CX 1556 1554,
  .CX 1556 1553,
  .CX 1556 1552,
  .CX 1556 1551,
  .CX 1556 791,
  .CX 1556 789,
  .CX 1556 788,
  .CX 1556 787,
  .CX 1556 786,
  .CX 1556 525,
  .CX 1556 524,
  .CX 1554 1552,
  .CX 1554 786,
  .CX 1558 1554,
  .CX 1554 1558,
  .CX 1558 1554,
  .CX 1553 1552,
  .CX 1553 786,
  .CX 1553 529,
  .CX 530 1553,
  .CX 1553 530,
  .CX 530 1553,
  .CX 1552 530,
  .CX 1552 1557,
  .CX 1552 1554,
  .CX 1552 1551,
  .CX 1552 791,
  .CX 1552 790,
  .CX 1552 788,
  .CX 1552 787,
  .CX 1552 529,
  .CX 1552 528,
  .CX 1553 1552,
  .CX 1552 1553,
  .CX 1553 1552,
  .CX 1551 790,
  .CX 1551 787,
  .CX 1551 529,
  .CX 1556 1551,
  .CX 1551 1556,
  .CX 1556 1551,
  .CX 791 530,
  .CX 791 786,
  .CX 791 529,
  .CX 1554 791,
  .CX 791 1554,
  .CX 1554 791,
  .CX 790 1558,
  .CX 790 1552,
  .CX 790 529,
  .CX 1551 790,
  .CX 790 1551,
  .CX 1551 790,
  .CX 789 1553,
  .CX 789 1552,
  .CX 789 1551,
  .CX 789 786,
  .CX 789 528,
  .CX 789 526,
  .CX 791 789,
  .CX 789 791,
  .CX 791 789,
  .CX 788 1557,
  .CX 788 787,
  .CX 788 529,
  .CX 788 528,
  .CX 788 526,
  .CX 1553 788,
  .CX 788 1553,
  .CX 1553 788,
  .CX 787 1556,
  .CX 787 1554,
  .CX 787 1553,
  .CX 787 786,
  .CX 787 526,
  .CX 786 530,
  .CX 786 1556,
  .CX 786 526,
  .CX 1553 786,
  .CX 786 1553,
  .CX 1553 786,
  .CX 529 530,
  .CX 529 1556,
  .CX 529 1553,
  .CX 529 526,
  .CX 786 529,
  .CX 529 786,
  .CX 786 529,
  .CX 528 1558,
  .CX 528 1557,
  .CX 528 1554,
  .CX 528 1553,
  .CX 528 787,
  .CX 528 529,
  .CX 527 1553,
  .CX 527 1552,
  .CX 527 1551,
  .CX 527 791,
  .CX 527 789,
  .CX 528 527,
  .CX 527 528,
  .CX 528 527,
  .CX 526 530,
  .CX 526 1556,
  .CX 526 1553,
  .CX 526 786,
  .CX 529 526,
  .CX 526 529,
  .CX 529 526,
  .CX 525 530,
  .CX 525 1558,
  .CX 525 1556,
  .CX 525 527,
  .CX 525 526,
  .CX 524 1553,
  .CX 524 1552,
  .CX 524 1551,
  .CX 524 786,
  .CX 524 529,
  .CX 524 527,
  .CX 524 526,
  .CX 524 525,
  .CX 523 530,
  .CX 523 791,
  .CX 523 529,
  .CX 523 527,
  .CX 523 524,
  .CX 522 1557,
  .CX 522 1553,
  .CX 522 789,
  .CX 522 528,
  .CX 522 523,
  .measureX 530 [] [.Z 528, .Z 529, .Z 788, .Z 790, .Z 1554, .Z 1556, .Z 1557, .CZ 522 524, .CZ 522 526, .CZ 522 529, .CZ 522 1552, .CZ 522 1553, .CZ 522 1554, .CZ 522 1556, .CZ 522 1558, .CZ 523 525, .CZ 523 526, .CZ 523 786, .CZ 523 1553, .CZ 523 1554, .CZ 523 1556, .CZ 523 1558, .CZ 524 525, .CZ 524 526, .CZ 524 527, .CZ 524 791, .CZ 524 1551, .CZ 524 1558, .CZ 525 526, .CZ 525 529, .CZ 525 786, .CZ 525 788, .CZ 525 789, .CZ 525 791, .CZ 525 1551, .CZ 525 1552, .CZ 525 1553, .CZ 525 1556, .CZ 526 527, .CZ 526 789, .CZ 526 1551, .CZ 526 1556, .CZ 526 1557, .CZ 526 1558, .CZ 527 529, .CZ 527 786, .CZ 527 787, .CZ 527 1552, .CZ 527 1558, .CZ 528 787, .CZ 529 1551, .CZ 786 1557, .CZ 790 1558],
  .X 1558,
  .measureX 1558 [] [.Z 522, .Z 523, .Z 524, .Z 525, .Z 526, .Z 527, .Z 528, .Z 787, .Z 788, .Z 789, .Z 1554, .Z 1557, .CZ 522 791, .CZ 522 1551, .CZ 522 1552, .CZ 523 525, .CZ 523 786, .CZ 523 1551, .CZ 523 1552, .CZ 524 787, .CZ 524 788, .CZ 524 791, .CZ 524 1551, .CZ 524 1552, .CZ 524 1554, .CZ 524 1557, .CZ 525 527, .CZ 525 529, .CZ 525 786, .CZ 525 787, .CZ 525 790, .CZ 525 1551, .CZ 525 1552, .CZ 525 1553, .CZ 525 1554, .CZ 525 1557, .CZ 526 527, .CZ 526 787, .CZ 526 791, .CZ 526 1551, .CZ 526 1552, .CZ 526 1557, .CZ 527 529, .CZ 527 789, .CZ 527 791, .CZ 527 1551, .CZ 527 1552, .CZ 528 786, .CZ 529 787, .CZ 529 788, .CZ 529 1554, .CZ 786 787, .CZ 786 788, .CZ 786 791, .CZ 786 1551, .CZ 786 1552, .CZ 786 1553, .CZ 786 1554, .CZ 787 1551, .CZ 787 1552],
  .measureX 1557 [] [.CZ 522 525, .CZ 522 526, .CZ 522 791, .CZ 522 1552, .CZ 522 1553, .CZ 522 1556, .CZ 523 527, .CZ 523 786, .CZ 523 787, .CZ 523 1553, .CZ 523 1556, .CZ 524 527, .CZ 527 790],
  .measureX 1556 [] [.CZ 522 526, .CZ 522 529, .CZ 522 790, .CZ 522 1552, .CZ 522 1553, .CZ 522 1554, .CZ 523 524, .CZ 523 525, .CZ 523 526, .CZ 523 527, .CZ 523 786, .CZ 523 1553, .CZ 523 1554, .CZ 524 786, .CZ 524 787, .CZ 524 788, .CZ 524 789, .CZ 524 791, .CZ 524 1551, .CZ 524 1552, .CZ 524 1554, .CZ 525 526, .CZ 525 527, .CZ 525 529, .CZ 525 786, .CZ 525 787, .CZ 525 788, .CZ 525 1551, .CZ 525 1552, .CZ 525 1553, .CZ 525 1554, .CZ 526 527, .CZ 526 786, .CZ 526 789, .CZ 526 791, .CZ 526 1551, .CZ 526 1552, .CZ 526 1554, .CZ 527 787, .CZ 527 789, .CZ 527 791, .CZ 527 1551, .CZ 527 1552, .CZ 528 529, .CZ 528 786, .CZ 528 787, .CZ 529 787, .CZ 529 788, .CZ 529 1554, .CZ 786 787, .CZ 786 788, .CZ 786 1551, .CZ 786 1552, .CZ 786 1553, .CZ 786 1554, .CZ 787 791, .CZ 787 1552, .CZ 1551 1554],
  .measureX 1554 [] [.CZ 522 526, .CZ 522 529, .CZ 522 786, .CZ 522 787, .CZ 522 790, .CZ 522 1551, .CZ 522 1553, .CZ 523 524, .CZ 523 525, .CZ 523 527, .CZ 523 1551, .CZ 523 1553, .CZ 524 525, .CZ 524 527, .CZ 524 786, .CZ 524 788, .CZ 524 791, .CZ 524 1551, .CZ 524 1552, .CZ 525 527, .CZ 525 529, .CZ 525 789, .CZ 525 790, .CZ 525 791, .CZ 525 1551, .CZ 525 1552, .CZ 525 1553, .CZ 526 527, .CZ 526 787, .CZ 526 789, .CZ 526 1551, .CZ 526 1552, .CZ 527 787, .CZ 527 789, .CZ 527 791, .CZ 527 1552, .CZ 528 787, .CZ 529 791, .CZ 786 791, .CZ 786 1551, .CZ 786 1552, .CZ 786 1553, .CZ 787 1551, .CZ 787 1552, .CZ 788 1551],
  .measureX 1553 [] [.CZ 522 529, .CZ 522 786, .CZ 522 790, .CZ 522 791, .CZ 523 524, .CZ 523 527, .CZ 523 786, .CZ 523 1552, .CZ 524 525, .CZ 525 527, .CZ 525 790, .CZ 525 791, .CZ 525 1551, .CZ 525 1552, .CZ 527 1551, .CZ 527 1552, .CZ 529 791, .CZ 791 1551, .CZ 791 1552],
  .measureX 1552 [] [.CZ 523 525, .CZ 523 526, .CZ 523 786, .CZ 523 787, .CZ 524 527, .CZ 524 788, .CZ 524 791, .CZ 525 790, .CZ 529 791, .CZ 786 790],
  .measureX 1551 [] [.CZ 523 526, .CZ 523 787, .CZ 524 529],
  .measureX 791 [] [.CZ 523 525, .CZ 523 527, .CZ 523 786, .CZ 523 788],
  .measureX 790 [] [.CZ 523 524, .CZ 523 529],
  .X 791,
  .CX 791 790,
  .CX 790 791,
  .CX 791 790,
  .CX 791 789,
  .CX 789 791,
  .CX 791 789,
  .CX 790 788,
  .CX 788 790,
  .CX 790 788,
  .CX 789 787,
  .CX 787 789,
  .CX 789 787,
  .CX 788 786,
  .CX 786 788,
  .CX 788 786,
  .CX 787 529,
  .CX 529 787,
  .CX 787 529,
  .CX 523 786
]

def safe15 : Program → Nat → Bool
  | [], _ => true
  | (.measureX t c0 c1)::rest, b =>
    let b' := flipN_t8 b t (b.testBit t)
    c0.isEmpty && (corrP_t8 c1 false b' == b.testBit t) && safe15 rest b'
  | i::rest, b => safe15 rest (runN_t8 [i] [] (false,b)).2

def check15 (uv : Nat × Nat) : Bool :=
  [false,true].all fun g => [false,true].all fun s =>
    let pre := MorningFour.pre507 g s uv.1 uv.2
    let e := encN_t8 pre sites15
    let b := (runN_t8 (MorningFour.tick507 ++ tripF) [] (false,e)).2
    safe15 candidate15 b && ((runN_t8 candidate15 [] (false,b)).2 == e)

theorem check15_all : MorningFour.pairs.all check15 = true := by decide +kernel

theorem corr_add (cs : List Correction) (ph : Bool) (b : Nat) :
    corrP_t8 cs ph b = (ph ^^ corrP_t8 cs false b) := by
  induction cs generalizing ph with
  | nil => cases ph <;> rfl
  | cons c cs ih =>
    cases c with
    | Z t => cases ph <;> cases hb : b.testBit t <;> simp only [corrP_t8, hb, Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false] <;> (first | rfl | (rw [ih true]; cases corrP_t8 cs false b <;> rfl))
    | CZ x y => cases ph <;> cases hx : b.testBit x <;> cases hy : b.testBit y <;> simp only [corrP_t8, hx, hy, Bool.false_and, Bool.true_and, Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false] <;> (first | rfl | (rw [ih true]; cases corrP_t8 cs false b <;> rfl))

theorem safe_sound (P : Program) (b : Nat) (h : safe15 P b = true) (m : List Bool) (ph : Bool) :
  runN_t8 P m (ph,b) = (ph, (runN_t8 P [] (false,b)).2) := by
  induction P generalizing b m ph with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | X t => simp only [safe15,runN_t8,Prod.snd] at h ⊢; exact ih _ h _ _
    | CX c t => simp only [safe15,runN_t8,Prod.snd] at h ⊢; exact ih _ h _ _
    | CCX a b' t => simp only [safe15,runN_t8,Prod.snd] at h ⊢; exact ih _ h _ _
    | measureX t c0 c1 =>
      simp only [safe15,Bool.and_eq_true,beq_iff_eq] at h
      obtain ⟨⟨hc0,hc1⟩,hr⟩ := h
      have hz : c0 = [] := by simpa using hc0
      subst c0
      cases m with
      | nil => simpa [runN_t8, corrP_t8] using ih _ hr [] ph
      | cons z zs =>
        cases z with
        | false => simpa [runN_t8, corrP_t8] using ih _ hr zs ph
        | true =>
          have eq : corrP_t8 c1 (ph ^^ b.testBit t) (flipN_t8 b t (b.testBit t)) = ph := by
            rw [corr_add, hc1]
            cases ph <;> cases b.testBit t <;> rfl
          simpa [runN_t8, corrP_t8, eq] using ih _ hr zs ph


theorem candidate_sample (g s : Bool) (uv : Nat × Nat) (h : uv ∈ MorningFour.pairs)
    (m : List Bool) (ph : Bool) :
    let e := encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15
    let b := (runN_t8 (MorningFour.tick507 ++ tripF) [] (false,e)).2
    runN_t8 candidate15 m (ph,b) = (ph,e) := by
  have t := check15_all
  simp only [List.all_eq_true] at t
  have row := t uv h
  simp only [check15,List.all_eq_true] at row
  have z := row g (by cases g <;> simp) s (by cases s <;> simp)
  simp only [Bool.and_eq_true, beq_iff_eq] at z
  exact (safe_sound candidate15 _ z.1 m ph).trans (by rw [z.2])

def old15 : Program := tickMR8 ++ W.ReverseCarry.compactReceiverTick base 507

def oldCheck15 (uv : Nat × Nat) : Bool :=
  [false,true].all fun g => [false,true].all fun s =>
    let e := encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15
    let b := (runN_t8 (MorningFour.tick507 ++ tripF) [] (false,e)).2
    phaseClean508 old15 b == some e

theorem old_all15 : MorningFour.pairs.all oldCheck15 = true := by decide +kernel

theorem candidate_support15 : wires candidate15 ⊆ sites15.toFinset := by decide +kernel
theorem old_support15 : wires old15 ⊆ sites15.toFinset := by decide +kernel

theorem old_sample15 (g s : Bool) (uv : Nat × Nat) (h : uv ∈ MorningFour.pairs) (m : List Bool) :
    let e := encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15
    let b := (runN_t8 (MorningFour.tick507 ++ tripF) [] (false,e)).2
    runN_t8 old15 m (false,b) = (false,e) := by
  have t := old_all15
  simp only [List.all_eq_true] at t
  have row := t uv h
  simp only [oldCheck15,List.all_eq_true] at row
  have z := row g (by cases g <;> simp) s (by cases s <;> simp)
  simp only [beq_iff_eq] at z
  exact phaseClean508_sound old15 _ _ z m

theorem replace_sample15 (g s : Bool) (uv : Nat × Nat) (h : uv ∈ MorningFour.pairs)
    (state : State) (m n : List Bool)
    (agree : ∀ q ∈ sites15,
      state.basis q = tbN_t8 ((runN_t8 (MorningFour.tick507 ++ tripF) []
        (false,encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15)).2) q) :
    run candidate15 m state = run old15 n state := by
  apply Stack5.local_replace candidate15 old15 sites15.toFinset
    candidate_support15 old_support15 state
      ⟨false,tbN_t8 ((runN_t8 (MorningFour.tick507 ++ tripF) []
        (false,encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15)).2)⟩ m n
  · intro q hq
    exact agree q (List.mem_toFinset.mp hq)
  · rw [run_sim_t8,run_sim_t8,candidate_sample g s uv h m false, old_sample15 g s uv h n]

theorem resources : toffoliCount candidate15 = 15 ∧ measurementCount candidate15 = 11 ∧ Challenge.gateSlots candidate15 = 714 := by decide +kernel
theorem physical : GatePhysical candidate15 := by
  simp (config := {maxSteps := 4000000}) [candidate15, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]
open ECDSAAdd.Secp256k1 ECDSAAdd.Entrant.Rolling1588.Integer ECDSAAdd.Entrant.History5 ECDSAAdd.Entrant.OB5
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward Rolling1588.Integer.regularForward
theorem forward_support : wires (MorningFour.tick507 ++ tripF) ⊆ sites15.toFinset := by decide +kernel

theorem local_stage15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a state : State) (stage : Stage base isA x p 507 a.basis) (m n : List Bool)
    (agree : ∀ q ∈ sites15,
      state.basis q = (run (MorningFour.tick507 ++ tripF) [] a).basis q) :
    run candidate15 m state = run old15 n state := by
  obtain ⟨raw,hraw,hbits⟩ := stage
  obtain ⟨g,s,uv,mem,reads⟩ := MorningFour.raw507 x hx0 hx raw hraw
  have fields := (W.compactSkywalkStage_fields_iff base _ 507 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨_,_,_,_,_,_,_,cleanA,_⟩ := fields
  have free530 : raw.basis 530 = false := cleanA _ (by decide +kernel)
  have used530 : 530 ∈ (W.compactSkywalkTickLayout base 511).wires.toFinset := by decide +kernel
  have kept530 : (run (Rolling1588.Integer.encodePrefix base isA 507) [] raw).basis 530 = raw.basis 530 := by
    apply run_preserves_outside
    intro used
    exact Finset.disjoint_left.mp
      (prefix_disjoint_layout base isA base_pool_nodup 507 511 (by omega) (by omega)) used used530
  have pre : ∀ q ∈ sites15, a.basis q = MorningFour.pre507 g s uv.1 uv.2 q := by
    intro q hq
    have hq' : q ∈ MorningFour.sites ∨ q = 530 := by simpa [sites15] using hq
    rcases hq' with hq | rfl
    · rw [hbits, ←reads q hq]
      apply run_preserves_outside
      rcases MorningPlacement.layouts q hq with h|h|h|h
      all_goals
        exact fun hh => Finset.disjoint_left.mp
          (prefix_disjoint_layout base isA base_pool_nodup 507 _ (by omega) (by omega)) hh h
    · rw [hbits,kept530,free530]
      rfl
  apply replace_sample15 g s uv mem state m n
  intro q hq
  rw [agree q hq]
  rw [site_run (MorningFour.tick507 ++ tripF) sites15 forward_support a
    ⟨false,MorningFour.pre507 g s uv.1 uv.2⟩ pre [] q hq]
  have support : ∀ q, MorningFour.pre507 g s uv.1 uv.2 q = true → q ∈ sites15 := by
    intro q hq
    have old : q ∈ MorningFour.sites := by
      by_contra hn
      have z := MorningFour.pre_supp g s uv.1 uv.2 q hn
      rw [z] at hq
      exact Bool.noConfusion hq
    change q ∈ MorningFour.sites ++ [530]
    exact List.mem_append.mpr (Or.inl old)
  let e := encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15
  have encoded : MorningFour.pre507 g s uv.1 uv.2 = tbN_t8 e := tb_enc_t8 _ _ support
  calc
    (run (MorningFour.tick507 ++ tripF) [] ⟨false,MorningFour.pre507 g s uv.1 uv.2⟩).basis q =
        (run (MorningFour.tick507 ++ tripF) [] ⟨false,tbN_t8 e⟩).basis q := by rw [←encoded]
    _ = _ := congrArg (fun t : State => t.basis q) (run_sim_t8 _ [] false e)


theorem codec_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a t : State) (stage : Stage base isA x p 507 a.basis) (codec : Program) (m : List Bool)
    (agree : ∀ q ∈ sites15,
      (run codec (m.take (measurementCount codec)) t).basis q =
        (run (MorningFour.tick507 ++ tripF) [] a).basis q) :
    run (codec ++ candidate15) m t = run (codec ++ old15) m t := by
  rw [run_append,run_append]
  exact local_stage15 isA x hx0 hx a _ stage _ _ agree

theorem placed_codec_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a t : State) (stage : Stage base isA x p 507 a.basis) (codec : Program) (m : List Bool)
    (agree : ∀ q ∈ sites15,
      (run codec (m.take (measurementCount codec)) t).basis q =
        (run (MorningFour.tick507 ++ tripF) [] a).basis q) :
    run (renameProgram (sig 510) (codec ++ candidate15)) m (pullState (sig 510) t) =
    run (renameProgram (sig 510) (codec ++ old15)) m (pullState (sig 510) t) := by
  rw [OB5.run_rename 510 (by omega), OB5.run_rename 510 (by omega),
    codec_replace15 isA x hx0 hx a t stage codec m agree]
theorem same50715 : renameProgram (sig 507) (W.ReverseCarry.compactReceiverTick base 507) =
    renameProgram (sig 510) (W.ReverseCarry.compactReceiverTick base 507) := by decide +kernel

theorem unpack50715 (isA : Bool) : unpackFirst base isA 507 = [] := by
  simp only [unpackFirst,show ¬(507:Nat)=5 from by decide,if_false,Rolling1588.Integer.decodeBefore,
    show History5.packDue 507=false from by decide,Bool.false_eq_true,if_false]

theorem reverse_shape15 (isA : Bool) :
    Rolling1588.stackReverse isA = renameProgram (sig 511) tickR ++
      (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15) ++
        Rolling1588.reverse isA 1 506) := by
  have shape := reverse_snoc isA 1 506
  rw [show (1:Nat)+506=507 by rfl,unpack50715,List.nil_append,
    reverse_eq_packets,same50715] at shape
  rw [reverse_eq_packets] at shape
  rw [Rolling1588.stackReverse,shape]
  simp only [old15,renameProgram,List.map_append,List.append_assoc]

theorem pack_inverse15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool) :
    run (Rolling1588.Integer.decodeBefore base isA 510) mD
      (run (packAfter base isA 510) mE (run (MorningFour.tick507 ++ tripF) [] a)) =
        run (MorningFour.tick507 ++ tripF) [] a := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  let b8 := run (W.repairedTick base 507) [] a
  let b9 := run (W.repairedTick base 508) [] b8
  let b10 := run (W.repairedTick base 509) [] b9
  let b11 := run (W.repairedTick base 510) [] b10
  have s8 : Stage base isA x p 508 b8.basis := by
    have h := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 507 hp0 hx0 hpo hp gap hx cop (by omega) a [] stage).2
    simpa only [MorningPlacement.pack507,List.append_nil,b8] using h
  have s9 : Stage base isA x p 509 b9.basis := by
    have h := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 508 hp0 hx0 hpo hp gap hx cop (by omega) b8 [] s8).2
    simpa only [pack508,List.append_nil,b9] using h
  have s10 : Stage base isA x p 510 b10.basis := by
    have h := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 509 hp0 hx0 hpo hp gap hx cop (by omega) b9 [] s9).2
    simpa only [pack509,List.append_nil,b10] using h
  have rep : W.repairedTick base 510=W.compactSkywalkTick base 510 := by
    rw [tick510ExF_explicit,tick510ExF_compact]
  have legal := tick_pack_legal base isA base_pool_nodup x p 510 hp0 hx0 hpo hp gap hx cop
    (by omega) b10 [] s10 (by decide)
  rw [←rep] at legal
  have dp : run (Rolling1588.Integer.decodeBefore base isA 510) mD
      (run (packAfter base isA 510) mE b11)=b11 := by
    simpa only [Rolling1588.Integer.packAfter,Rolling1588.Integer.decodeBefore,show History5.packDue 510=true from by decide,if_true,b11] using
      encode_decode_roundtrip base isA base_pool_nodup (510-5) (by omega) b11 mE mD legal
  have eq : run (MorningFour.tick507 ++ tripF) [] a = b11 := by
    simp only [tripF,←MorningFour.explicit507,←tick508ExF_explicit,←tick509ExF_explicit,
      ←tick510ExF_explicit,List.append_assoc,run_append,List.take_nil,List.drop_nil,b8,b9,b10,b11]
  rw [eq,dp]

theorem decoded_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool) :
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ candidate15) mD
      (run (packAfter base isA 510) mE (run (MorningFour.tick507 ++ tripF) [] a)) =
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ old15) mD
      (run (packAfter base isA 510) mE (run (MorningFour.tick507 ++ tripF) [] a)) := by
  rw [run_append (Rolling1588.Integer.decodeBefore base isA 510) candidate15,
    run_append (Rolling1588.Integer.decodeBefore base isA 510) old15,
    pack_inverse15 isA x hx0 hx a stage mE]
  exact local_stage15 isA x hx0 hx a _ stage _ _ (fun _ _ => rfl)

theorem sites_pool15 : sites15.toFinset ⊆ (skywalkPoolWires base).toFinset := by
  have layout : sites15 = ([506,507,508,509,510,511,512,513,770,771,772,773,774,775,1535,1536,1537,1538,1540,1541,1542,1543,514] : List Nat).map base := by decide +kernel
  intro q hq
  have member : q ∈ sites15 := List.mem_toFinset.mp hq
  rw [layout] at member
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
  apply List.mem_toFinset.mpr
  apply OB5.base_pool i
  have bound : ∀ i ∈ ([506,507,508,509,510,511,512,513,770,771,772,773,774,775,1535,1536,1537,1538,1540,1541,1542,1543,514] : List Nat), i < 1798 := by decide
  exact bound i hi

theorem decoded_replace_pool15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool)
    (agree : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) mE a).basis q) :
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ candidate15) mD u =
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ old15) mD u := by
  let f := MorningFour.tick507 ++ tripF
  let codec := Rolling1588.Integer.decodeBefore base isA 510
  let ref := run (packAfter base isA 510) mE (run f [] a)
  have dec : wires codec ⊆ (skywalkPoolWires base).toFinset := by
    have d := (History5.pack_support5 base 510 (by omega)).2.trans (History5.integerSites5_pool base)
    rw [←decodeBefore_support_eq base isA 510] at d
    exact d
  have supportC : wires (codec ++ candidate15) ⊆ (skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,candidate_support15.trans sites_pool15⟩
  have supportO : wires (codec ++ old15) ⊆ (skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,old_support15.trans sites_pool15⟩
  apply Stack5.local_replace _ _ _ supportC supportO u ref mD mD
  · intro q hq
    have eq1 := congrFun (run_basis_records (f ++ packAfter base isA 510) a a mE [] rfl) q
    have eq2 := congrFun (run_basis_records (packAfter base isA 510) (run f [] a) (run f [] a) [] mE rfl) q
    have eq3 : (run (f ++ packAfter base isA 510) [] a).basis q =
        (run (packAfter base isA 510) [] (run f [] a)).basis q := by
      rw [run_append]; simp only [List.take_nil,List.drop_nil]
    exact (agree q (List.mem_toFinset.mp hq)).trans (eq1.trans (eq3.trans eq2))
  · exact decoded_replace15 isA x hx0 hx a stage mE mD

def reverseTail15 (isA : Bool) : Program :=
  renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ candidate15) ++
    Rolling1588.reverse isA 1 506

theorem unpack51015 (isA : Bool) :
    Rolling1588.unpackAtTick isA 510 = Rolling1588.Integer.decodeBefore base isA 510 := by
  have h := unpackFirst_base isA 510
  simpa only [unpackFirst,show ¬(510:Nat)=5 from by decide,if_false] using h.symm

theorem old_records15 : measurementCount old15 = 11 := by decide +kernel

theorem placed_block15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool)
    (agree : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) mE a).basis q) :
    run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ candidate15)) mD
      (pullState (sig 510) u) =
    run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15)) mD
      (pullState (sig 510) u) := by
  rw [unpack51015, OB5.run_rename 510 (by omega), OB5.run_rename 510 (by omega),
    decoded_replace_pool15 isA x hx0 hx a u stage mE mD agree]

theorem tail_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool)
    (agree : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) mE a).basis q) :
    run (reverseTail15 isA) mD (pullState (sig 510) u) =
      run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15) ++
        Rolling1588.reverse isA 1 506) mD (pullState (sig 510) u) := by
  have count : measurementCount (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ candidate15)) =
      measurementCount (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,
      measurementCount_append,measurementCount_append,resources.2.1,old_records15]
  rw [reverseTail15,run_append,run_append, count,
    placed_block15 isA x hx0 hx a u stage mE _ agree]


theorem tail_actual15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (u : State) (hu : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run (regularForward base isA 1 510) mE s1).basis q) (mD : List Bool) :
    run (reverseTail15 isA) mD (pullState (sig 510) u) =
      run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15) ++
        Rolling1588.reverse isA 1 506) mD (pullState (sig 510) u) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  let k := measurementCount (regularForward base isA 1 506)
  have stage0 : Stage base isA x p 507
      (run (regularForward base isA 1 506)
        (mE.take (measurementCount (regularForward base isA 1 506))) s1).basis :=
    ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p 1 506
      hp0 hx0 hpo hp gap hx cop (by omega)) s1 _ (stage_one base isA x p s1 first)).2
  change Stage base isA x p 507 (run (regularForward base isA 1 506) (mE.take k) s1).basis at stage0
  obtain ⟨a,ha⟩ : ∃ a : State,run (regularForward base isA 1 506) (mE.take k) s1 = a := ⟨_,rfl⟩
  rw [ha] at stage0
  have fwdP : regularForward base isA 1 510 = regularForward base isA 1 506 ++
      ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) := by
    rw [regularForward_snoc base isA 1 509,show (1:Nat)+509=510 by rfl,
      regularForward_snoc base isA 1 508,show (1:Nat)+508=509 by rfl,
      regularForward_snoc base isA 1 507,show (1:Nat)+507=508 by rfl,
      regularForward_snoc base isA 1 506,show (1:Nat)+506=507 by rfl,
      MorningPlacement.pack507,pack508,pack509,
      MorningFour.explicit507,tick508ExF_explicit,tick509ExF_explicit,tick510ExF_explicit]
    simp only [tripF,List.append_assoc,List.append_nil]
  have agre : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) (mE.drop k) a).basis q := by
    intro q hq
    rw [hu q hq,fwdP,run_append,←show measurementCount (regularForward base isA 1 506)=k from rfl,ha]
  exact tail_replace15 isA x hx0 hx a u stage0 (mE.drop k) mD agre

attribute [local irreducible] Stage
def stackReverse15 (isA : Bool) : Program := renameProgram (sig 511) tickR ++ reverseTail15 isA

theorem reverse_actual15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (t5 : State) (agree : ∀q∈skywalkPoolWires base,
      t5.basis q=(run (regularForward base isA 1 511) mE s1).basis q) (mD : List Bool) :
    run (stackReverse15 isA) mD (pullState (sig 511) t5)=
      run (Rolling1588.stackReverse isA) mD (pullState (sig 511) t5) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  have aStage : Stage base isA x p 511
      (run (regularForward base isA 1 510)
        (mE.take (measurementCount (regularForward base isA 1 510))) s1).basis :=
    ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p 1 510
      hp0 hx0 hpo hp hgap hx cop (by omega)) s1 _ (stage_one base isA x p s1 first)).2
  have whole : run (regularForward base isA 1 510)
      (mE.take (measurementCount (regularForward base isA 1 510))) s1=
        run (regularForward base isA 1 510) mE s1 := run_take _ mE s1
  have last : run (regularForward base isA 1 511) mE s1=
      run (W.repairedTick base 511) (mE.drop (measurementCount (regularForward base isA 1 510)))
        (run (regularForward base isA 1 510)
          (mE.take (measurementCount (regularForward base isA 1 510))) s1) := by
    rw [regularForward_snoc base isA 1 510,show (1:Nat)+510=511 by rfl,regular_pack511,List.append_nil,run_append]
  rw [last] at agree
  generalize run (regularForward base isA 1 510)
    (mE.take (measurementCount (regularForward base isA 1 510))) s1=a at aStage whole agree
  obtain ⟨G,bits⟩ := stage511_bits isA x hx0 hx a aStage
  rw [repaired511_forced G a bits] at agree
  have post : ∀q∈tickSites,t5.basis q=postBits G q := by
    intro q hq
    rw [agree q (tickSites_pool q hq)]
    exact tickF_post G a bits q hq
  have uAgree : ∀q∈skywalkPoolWires base,(run tickR [] t5).basis q=a.basis q := by
    intro q hq
    by_cases ht : q∈tickSites
    · rw [site_run tickR tickSites tickR_wires t5 ⟨false,postBits G⟩ post [] q ht,tickR_pre G q ht]
      exact (bits q ht).symm
    · have hr : q∉wires tickR := fun h => ht (List.mem_toFinset.mp (tickR_wires h))
      have hf : q∉wires tickF := fun h => ht (List.mem_toFinset.mp (tickF_wires h))
      rw [run_preserves_outside tickR [] t5 q hr,agree q hq,run_preserves_outside tickF [] a q hf]
  have z := stage_zero isA x 511 (by omega) a.basis aStage
  have move : pullState (sig 511) (run tickR [] t5)=pullState (sig 510) (run tickR [] t5) :=
    (OB5.pull_step 511 (by omega) _
      ((uAgree _ (StackOB5Base.base_pool _ (by omega))).trans z.1)
      (fun big => (uAgree _ (StackOB5Base.base_pool _ (by omega))).trans (z.2 big))).symm
  have cn : measurementCount (renameProgram (sig 511) tickR)=0 :=
    (renameProgram_counts (sig 511) tickR).2.trans tickR_counts.2
  rw [stackReverse15,reverse_shape15,run_append,run_append,cn]
  simp only [List.take_zero,List.drop_zero]
  rw [OB5.run_rename 511 (by omega),tickR_run,move]
  exact tail_actual15 isA x hx0 hx s1 mE first _
    (fun q hq => (uAgree q hq).trans (congrArg (fun st : State => st.basis q) whole)) mD

theorem stack_roundtrip15 (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackReverse15 isA) mD (run (Rolling1588TickGap.stackForward isA) mE s)=s := by
  have fwd : run (Rolling1588TickGap.stackForward isA) mE s =
      pullState (sig 511) (run (regularForward base isA 1 511) mE s) := by
    rw [Rolling1588TickGap.stackForward_run_eq isA x hx0 hx s mE first,
      ←Rolling1588.Integer.stackForward_eq_packets,Rolling1588.Integer.stackForwardT_run isA hn hlo x hx0 hx s mE first,
      Rolling1588.Integer.forward_run isA x hx0 hx s mE first]
  rw [fwd, reverse_actual15 isA x hx0 hx s mE first _ (fun _ _ => rfl) mD,←fwd]
  exact Rolling1588TickGap.stack_roundtrip isA hn hlo x hx0 hx s mE mD first

open ECDSAAdd.Arithmetic.DirectSkywalk
def lastPhase15 (isA : Bool) : Program :=
  skywalkArithmeticClear base ++ stackReverse15 isA ++ FrontierEntry1591NativeH.inverse base

private theorem compose_roundtrip15 (N F C R I : Program) (s : State) (mp mr : List Bool)
    (clearM : measurementCount C=0)
    (twice : ∀ (t : State) mc,run C [] (run C mc t)=t)
    (stack : ∀mn mf md,run R md (run F mf (run N mn s))=run N mn s)
    (native : ∀mn mi,run I mi (run N mn s)=s) :
    run (C++(R++I)) mr (run (N++(F++C)) mp s)=s := by
  simp only [run_append,clearM,List.take_zero,List.drop_zero]
  rw [twice,stack]
  exact native _ _

theorem phases_roundtrip15 (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (mp mr : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (lastPhase15 isA) mr (run (Rolling1588TickGap.firstPhase isA) mp s)=s := by
  have clearM : measurementCount (skywalkArithmeticClear base)=0 := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,measurementCount]
  have twice (t : State) (mc : List Bool) : run (skywalkArithmeticClear base) []
      (run (skywalkArithmeticClear base) mc t)=t := by
    simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
      (base 511) (base 512) (base 770) (arith_clear_gates base hn) t mc []
  have stack (mn mf md : List Bool) :
      run (stackReverse15 isA) md (run (Rolling1588TickGap.stackForward isA) mf
        (run (FrontierEntry1591Native.forward base) mn s))=
      run (FrontierEntry1591Native.forward base) mn s :=
    stack_roundtrip15 isA hn hlo x hx0 hx _ mf md
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [Rolling1588TickGap.firstPhase,Rolling1588TickGap.tailPhase,lastPhase15,List.append_assoc] using
    compose_roundtrip15 (FrontierEntry1591Native.forward base) (Rolling1588TickGap.stackForward isA)
      (skywalkArithmeticClear base) (stackReverse15 isA)
      (FrontierEntry1591NativeH.inverse base) s mp mr clearM twice stack
      (fun mn mi=>FrontierEntry1591NativeH.inverse_roundtrip base hn x y hx s mn mi input)

attribute [local irreducible] Rolling1588.stackReverse Rolling1588.lastPhase stackReverse15 reverseTail15 lastPhase15 candidate15 old15
theorem cand_extra15 : wires (renameProgram (sig 510) candidate15) ⊆
    wires (renameProgram (sig 510) old15) ∪ {530} := by
  have parts : MorningFour.sites.toFinset ⊆ wires old15 ∪ {1559} := by decide +kernel
  have absent : (1559:Wire) ∉ wires candidate15 := by decide +kernel
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  have member : v ∈ sites15 := List.mem_toFinset.mp (candidate_support15 hv)
  have cases : v ∈ MorningFour.sites ∨ v=530 := by simpa [sites15] using member
  rcases cases with oldsite | extra
  · have member := parts (List.mem_toFinset.mpr oldsite)
    rcases Finset.mem_union.mp member with old | extra
    · apply Finset.mem_union_left
      rw [renameProgram_support]
      exact Finset.mem_image.mpr ⟨v,old,rfl⟩
    · simp only [Finset.mem_singleton] at extra
      exact False.elim (absent (extra ▸ hv))
  · subst v
    apply Finset.mem_union_right
    simp only [Finset.mem_singleton]
    decide +kernel

theorem last_extra15 (isA : Bool) : wires (lastPhase15 isA) ⊆
    wires (Rolling1588.lastPhase isA) ∪ {530} := by
  have ren (p q : Program) : renameProgram (sig 510) (p ++ q) =
      renameProgram (sig 510) p ++ renameProgram (sig 510) q := by simp only [renameProgram,List.map_append]
  have hsub := cand_extra15
  intro q h
  simp only [lastPhase15,stackReverse15,reverseTail15,ren,wires_append,
    Finset.mem_union] at h
  rw [Rolling1588.lastPhase,reverse_shape15]
  simp only [ren,wires_append,Finset.mem_union,Finset.mem_singleton] at h ⊢
  have hh : q ∈ wires (renameProgram (sig 510) candidate15) →
      q ∈ wires (renameProgram (sig 510) old15) ∨ q=530 := by
    intro hc
    have z := hsub hc
    simpa only [Finset.mem_union,Finset.mem_singleton] using z
  rcases h with ((hc | ht | (hcodec | hcand) | hrest) | hinv)
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr (Or.inl ht)))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl hcodec)))))
  · rcases hh hcand with hold | hextra
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr hold)))))
    · exact Or.inr hextra
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr hrest))))
  · exact Or.inl (Or.inr hinv)

theorem extra_pool15 : 530 ∈ (skywalkPoolWires base).toFinset := by
  have h := OB5.base_pool 514 (by decide)
  exact List.mem_toFinset.mpr (by simpa only [show base 514 = 530 from by decide +kernel] using h)

theorem last_pool15 (isA : Bool) : wires (lastPhase15 isA) ⊆ (skywalkPoolWires base).toFinset := by
  intro q h
  rcases Finset.mem_union.mp (last_extra15 isA h) with old | extra
  · exact ((Rolling1588Lifetime.last_support_sub isA).trans FrontierEntry1591Kernel.last_pool) old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact extra_pool15

theorem last_hosts_free15 (isA : Bool) (q : Wire) (hq : q ∈ Rolling1588Lifetime.phaseHosts) :
    q ∉ wires (lastPhase15 isA) := by
  intro h
  rcases Finset.mem_union.mp (last_extra15 isA h) with old | extra
  · exact Rolling1588Lifetime.last_hosts_free isA q hq old
  · simp only [Finset.mem_singleton] at extra
    subst q
    have no : (530:Wire) ∉ Rolling1588Lifetime.phaseHosts := by decide +kernel
    exact no hq

open ECDSAAdd.Entrant.Rolling1588Lifetime
private theorem phase_sites_split :
    phaseSites=FrontierEntry1591Native.workSites∪phaseHosts := by
  ext q
  simp only [phaseSites,phaseHosts,FrontierEntry1591Native.workSites,Finset.mem_union,
    List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem phase_kernel_rebind (P F Q : Program) (s : State) (m : List Bool)
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
    rw [phase_sites_split] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact (run_preserves_outside F mf before q (fieldFree q work)).trans (firstClean mp q work)
    · exact (run_preserves_outside Q mr after q (lastFree q host)).symm.trans
        (finalClean q (by rw [phase_sites_split];exact Finset.mem_union_right _ host))
  have firstOutput : ∀q∈phaseSites,(run P mp s).basis q=false := by
    intro q hq
    rw [phase_sites_split] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact firstClean mp q work
    · exact (run_preserves_outside P mp s q (firstFree q host)).trans
        (input q (by rw [phase_sites_split];exact Finset.mem_union_right _ host))
  have first := phase_run_eq P s mp input firstOutput
  have last := phase_run_eq Q after mr lastInput finalClean
  simp only [FrontierEntry1591Native.kernel,run_append,(renameProgram_counts _ _).2]
  rw [first]
  exact last


private theorem phase_numerator_away (q : Wire) (hq : q∈phaseSites) :
    q∉wireBlock base 2056 256 := by
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact OwnPlusHost.not_block _ 2056 256 (by omega)

/-- The field changes A into B. Its output is compared with a B encoding
of the same raw integer history before the B inverse is applied. -/
theorem raw_result_of_roundtrip (a b : Bool) (F : Program) (s : State) (m : List Bool)
    (value : Nat)
    (roundtrip : ∀mp mr,run (lastPhase15 b) mr (run (firstPhase b) mp s)=s)
    (fieldResult : ∀mp mf,
      let beforeA := run (firstPhase a) mp s
      let beforeB := run (firstPhase b) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (FrontierEntry1591Native.kernel (firstPhase a) F (lastPhase15 b)) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have firstPool : wires (firstPhase b)⊆(skywalkPoolWires base).toFinset := by
    rw [first_support_eq]
    exact FrontierEntry1591Kernel.first_pool
  have lastPool : wires (lastPhase15 b)⊆(skywalkPoolWires base).toFinset :=
    last_pool15 b
  have all := run_three_states (firstPhase a) F (lastPhase15 b)
    (fun initial out=>initial=s → out.phase=s.phase ∧
      regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q) (by
      intro initial beforeA after out mp mf mr h1 h2 h3 eq
      subst initial
      have result := fieldResult mp mf
      dsimp only at result
      rw [h1,h2] at result
      exact FrontierEntry1591Kernel.sandwich_states (firstPhase b) (lastPhase15 b) firstPool lastPool s
        (run (firstPhase b) mp s) after out mp mr value rfl h3 (roundtrip mp mr) result) s m
  simpa only [FrontierEntry1591Native.kernel,List.append_assoc] using all rfl



theorem kernel_result15 (a b : Bool) (F : Program) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool) (value : Nat)
    (input : SkywalkArithmeticInput base x y s.basis)
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (fieldResult : ∀mp mf,
      let beforeA := run (firstPhase a) mp s
      let beforeB := run (firstPhase b) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (renameProgram phaseHost (firstPhase a)++
      (F++renameProgram phaseHost (lastPhase15 b))) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have rt (mp mr : List Bool) : run (lastPhase15 b) mr (run (firstPhase b) mp s)=s := by
    rw [←Rolling1588TickGap.first_run_eq b hn x y hx0 hx s mp input]
    exact phases_roundtrip15 b hn hlo x y hx0 hx s mp mr input
  have raw := raw_result_of_roundtrip a b F s m value rt fieldResult
  have clean := caller_phase_clean x y s input
  have output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel (firstPhase a) F (lastPhase15 b)) m s).basis q=false := by
    intro q hq
    exact (raw.2.2 q (phase_numerator_away q hq)).trans (clean q hq)
  have same := phase_kernel_rebind (firstPhase a) F (lastPhase15 b) s m clean
    (first_hosts_free a) (fun records => Rolling1588Lifetime.first_clean a hn hlo x y hx0 hx s records input)
    fieldFree (last_hosts_free15 b) output
  dsimp only
  rw [same]
  exact raw

open ECDSAAdd.Entrant.Rolling1588 ECDSAAdd.Entrant.FrontierEntry1591Callers ECDSAAdd.Arithmetic.BalancedField
def oldKernel15 (a b : Bool) (F : Program) : Program :=
  renameProgram phaseHost (Rolling1588.firstPhase a) ++
    (F ++ renameProgram phaseHost (lastPhase15 b))
def kernel15 (a b : Bool) (F : Program) : Program :=
  renameProgram phaseHost (Rolling1588TickGap.firstPhase a) ++
    (F ++ renameProgram phaseHost (lastPhase15 b))
def entryKernel15 : Program := kernel15 true false entryFieldHosted
def exitKernel15 : Program := kernel15 false true exitFieldHosted

theorem old_entry_correct15 : EntryCorrect (oldKernel15 true false entryFieldHosted) := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  obtain ⟨out,outEq⟩ : ∃out : State,run (oldKernel15 true false entryFieldHosted) m t=out := ⟨_,rfl⟩
  have actualInput := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  have result := kernel_result15 true false entryFieldHosted hn hlo
    x _ hx0 hx t m (Y/(x:Fp)).val actualInput entryFieldHosted_work_free
    (fun mp mf=>entry_boundary hn hlo ho hf x Y hx0 hx s t mp mf input hg hs phase same half)
  change (run (oldKernel15 true false entryFieldHosted) m t).phase=t.phase ∧
    regValue (wireBlock base 2056 256) (run (oldKernel15 true false entryFieldHosted) m t).basis=(Y/(x:Fp)).val ∧
    ∀q,q∉wireBlock base 2056 256 → (run (oldKernel15 true false entryFieldHosted) m t).basis q=t.basis q at result
  rw [outEq] at result
  have conclusion : out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(Y/(x:Fp)).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q :=
    ⟨result.1.trans phase,result.2.1,fun q hq=>(result.2.2 q hq).trans (same q hq)⟩
  dsimp only
  rw [outEq]
  simpa only [skywalkArithmeticResult,if_true] using conclusion

theorem old_exit_correct15 : ExitCorrect (oldKernel15 false true exitFieldHosted) := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  have result := kernel_result15 false true exitFieldHosted hn hlo
    x Y.val hx0 hx s m (centerWord (Y*(x:Fp)/2)) input exitFieldHosted_work_free
    (fun mp mf=>exit_boundary hn hlo ho hf x Y hx0 hx s mp mf input hg hs)
  simpa only [oldKernel15,skywalkArithmeticNumerator] using result

theorem kernel_first_eq15 (a b : Bool) (F : Program)
    (hn : (skywalkSharedWires base).Nodup) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (kernel15 a b F) m s = run (oldKernel15 a b F) m s := by
  have records : measurementCount (renameProgram phaseHost (Rolling1588TickGap.firstPhase a)) =
      measurementCount (renameProgram phaseHost (Rolling1588.firstPhase a)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(Rolling1588TickGap.first_metrics a).2.1]
  rw [kernel15,oldKernel15,
    run_append (renameProgram phaseHost (Rolling1588TickGap.firstPhase a)),
    run_append (renameProgram phaseHost (Rolling1588.firstPhase a)),records,
    Rolling1588TickGap.first_hosted_run_eq a hn x y hx0 hx s _ input]

theorem entry_correct15 : EntryCorrect entryKernel15 := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actual := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  rw [entryKernel15,kernel_first_eq15 true false entryFieldHosted hn x _ hx0 hx t m actual]
  exact old_entry_correct15 hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half

theorem exit_correct15 : ExitCorrect exitKernel15 := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  rw [exitKernel15,kernel_first_eq15 false true exitFieldHosted hn x _ hx0 hx s m input]
  exact old_exit_correct15 hn hlo ho hf x Y hx0 hx s m input hg hs

theorem last_physical15 (isA : Bool) : GatePhysical (lastPhase15 isA) := by
  have old := Rolling1588.lastPhase_physical isA
  rw [Rolling1588.lastPhase,reverse_shape15] at old
  have ren (p q : Program) : renameProgram (sig 510) (p ++ q) =
      renameProgram (sig 510) p ++ renameProgram (sig 510) q := by simp only [renameProgram,List.map_append]
  simp only [gatePhysical_append,ren] at old
  rw [lastPhase15,stackReverse15,reverseTail15,ren]
  simp only [gatePhysical_append]
  exact ⟨⟨old.1.1,old.1.2.1,⟨old.1.2.2.1.1,
    gatePhysical_rename _ (sig_injective 510 (by omega)) _ physical⟩,old.1.2.2.2⟩,old.2⟩

theorem kernel_physical15 (a b : Bool) (F : Program) (field : GatePhysical F) :
    GatePhysical (kernel15 a b F) := by
  simpa only [kernel15,gatePhysical_append] using
    And.intro (Rolling1588Lifetime.phase_physical _ (Rolling1588TickGap.first_physical a))
      (And.intro field (Rolling1588Lifetime.phase_physical _ (last_physical15 b)))

theorem entry_physical15 : GatePhysical entryKernel15 := by
  simpa only [entryKernel15] using
    kernel_physical15 true false Rolling1588.entryFieldHosted Rolling1588.entryFieldHosted_physical

theorem exit_physical15 : GatePhysical exitKernel15 := by
  simpa only [exitKernel15] using
    kernel_physical15 false true Rolling1588.exitFieldHosted Rolling1588.exitFieldHosted_physical

theorem hosted_extra530 (b : Bool) :
    wires (renameProgram phaseHost (lastPhase15 b)) ⊆
      wires (renameProgram phaseHost (Rolling1588.lastPhase b)) ∪ {530} := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (last_extra15 b hv) with old | extra
  · apply Finset.mem_union_left
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨v,old,rfl⟩
  · simp only [Finset.mem_singleton] at extra
    subst v
    apply Finset.mem_union_right
    simp only [Finset.mem_singleton]
    decide +kernel

theorem kernel_extra530 (a b : Bool) (F : Program) :
    wires (kernel15 a b F) ⊆ wires (Rolling1588TickGap.kernel a b F) ∪ {530} := by
  have hsub := hosted_extra530 b
  intro q h
  simp only [kernel15,wires_append,Finset.mem_union] at h
  simp only [Rolling1588TickGap.kernel,wires_append,Finset.mem_union,Finset.mem_singleton]
  rcases h with hfirst | hfield | hlast
  · exact Or.inl (Or.inl hfirst)
  · exact Or.inl (Or.inr (Or.inl hfield))
  · rcases Finset.mem_union.mp (hsub hlast) with hold | hextra
    · exact Or.inl (Or.inr (Or.inr hold))
    · exact Or.inr (Finset.mem_singleton.mp hextra)

theorem extra_logical530 : (530:Wire) ∈ OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨514,?_,by decide +kernel⟩
  simp [OB5Support.logicalIndices]

theorem entry_support530 : wires entryKernel15 ⊆ OB5Support.logicalSites := by
  intro q hq
  have h := kernel_extra530 true false Rolling1588.entryFieldHosted hq
  rcases Finset.mem_union.mp h with old | extra
  · exact Rolling1588TickGap.entryKernel_support old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact extra_logical530

theorem exit_support530 : wires exitKernel15 ⊆ OB5Support.logicalSites := by
  intro q hq
  have h := kernel_extra530 false true Rolling1588.exitFieldHosted hq
  rcases Finset.mem_union.mp h with old | extra
  · exact Rolling1588TickGap.exitKernel_support old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact extra_logical530

end ECDSAAdd.Entrant.InverseFour15
