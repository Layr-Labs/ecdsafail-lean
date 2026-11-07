import ECDSAAdd.Submission.Entrant.FrontierMain
namespace ECDSAAdd.Entrant.TriFourthPatternBridge
open ECDSAAdd Arithmetic Secp256k1
open ECDSAAdd.Entrant.InputSentinel
-- Source-only preparation: no circuit or selected entry changes.
def fourth (t : Tri) : Nat := (t.A ^^^ t.B) ^^^ t.S
private theorem pair_xor_other : ∀ (a b c : Bool × Bool),
    a ≠ b → a ≠ c → b ≠ c →
    (a.1 ^^ b.1 ^^ c.1, a.2 ^^ b.2 ^^ c.2) ≠ a ∧
    (a.1 ^^ b.1 ^^ c.1, a.2 ^^ b.2 ^^ c.2) ≠ b ∧
    (a.1 ^^ b.1 ^^ c.1, a.2 ^^ b.2 ^^ c.2) ≠ c := by decide
 theorem fourth_pat (t : Tri) :
    t.pat (fourth t) =
      ((t.pat t.A).1 ^^ (t.pat t.B).1 ^^ (t.pat t.S).1,
       (t.pat t.A).2 ^^ (t.pat t.B).2 ^^ (t.pat t.S).2) := by
  simp only [Tri.pat, fourth, Nat.testBit_xor]
 theorem fourth_pat_distinct (t : Tri) (v : t.Valid) :
    t.pat (fourth t) ≠ t.pat t.A ∧ t.pat (fourth t) ≠ t.pat t.B ∧
      t.pat (fourth t) ≠ t.pat t.S := by
  rw [fourth_pat]
  have pv := Tri.pivots v
  exact pair_xor_other _ _ _ pv.2.2.2.1 pv.2.2.2.2.1 pv.2.2.2.2.2
 theorem fourth_tgt (t : Tri) (v : t.Valid) (i : Nat) :
    t.tgt i (t.pat (fourth t)) = (fourth t).testBit i := by
  have h := fourth_pat_distinct t v
  rw [Tri.tgt, if_neg h.1, if_neg h.2.1, if_neg h.2.2]
  simp only [fourth, Nat.testBit_xor]
 theorem remap_fourth_iff (t : Tri) (v : t.Valid) (X : Nat)
    (hX : X < 2^256) (hN : fourth t < 2^256) :
    ((∀ i ∈ t.idx, X.testBit i = t.tgt i (t.pat X)) ∧
      t.pat X = t.pat (fourth t)) ↔ X = fourth t :=
  Tri.match_iff v X (fourth t) hX hN (fourth_tgt t v)
end ECDSAAdd.Entrant.TriFourthPatternBridge
