import ECDSAAdd.Arithmetic.Copy
import ECDSAAdd.Framework.GateInverse

namespace ECDSAAdd.Arithmetic.Paper935

/-- Author engine.py:3026–3028: the zero-target first Horner round is
exactly a fan of CCX gates, in increasing word order. -/
def hornerCopy (bit : Wire) (y out : List Wire) : Program :=
  copyRegister (some bit) y out

/-- All input data, the control and phase are retained; only the target
word is XORed. This statement also covers nonzero target inputs. -/
theorem hornerCopy_run (bit : Wire) (y out : List Wire)
    (len : y.length=out.length) (distinct : (bit::(y++out)).Nodup)
    (s : State) (m : List Bool) :
    let t := run (hornerCopy bit y out) m s
    t.phase=s.phase ∧ (∀q,q∉out → t.basis q=s.basis q) ∧
      regValue out t.basis=regValue out s.basis ^^^
        (if s.basis bit then regValue y s.basis else 0) := by
  exact copyRegister_correct (some bit) y out len (List.nodup_cons.mp distinct).2
    (by simpa using (show bit∉out from fun h =>
      (List.nodup_cons.mp distinct).1 (List.mem_append_right y h))) s m

/-- engine.py:3014–3016: the zero-target rewrite produces the selected
multiplicand, before the unconditional halve. -/
theorem hornerCopy_zero (bit : Wire) (y out : List Wire)
    (len : y.length=out.length) (distinct : (bit::(y++out)).Nodup)
    (s : State) (m : List Bool) (zero : regValue out s.basis=0) :
    regValue out (run (hornerCopy bit y out) m s).basis=
      if s.basis bit then regValue y s.basis else 0 := by
  simpa [zero] using (hornerCopy_run bit y out len distinct s m).2.2

/-- engine.py:3033–3036 emits the same increasing-order fan at inverse
exit. Its inverse proof therefore uses XOR semantics, not list reversal. -/
theorem hornerCopy_roundtrip (bit : Wire) (y out : List Wire)
    (len : y.length=out.length) (distinct : (bit::(y++out)).Nodup)
    (s : State) (m n : List Bool) :
    run (hornerCopy bit y out) n (run (hornerCopy bit y out) m s)=s := by
  let t := run (hornerCopy bit y out) m s
  have first := hornerCopy_run bit y out len distinct s m
  have second := hornerCopy_run bit y out len distinct t n
  have apart := (List.nodup_append'.mp (List.nodup_cons.mp distinct).2).2.2
  have bitAway : bit∉out := fun h =>
    (List.nodup_cons.mp distinct).1 (List.mem_append_right y h)
  have ySame : regValue y t.basis=regValue y s.basis :=
    regValue_congr _ _ _ (fun q h => first.2.1 q (List.disjoint_left.mp apart h))
  have value : regValue out (run (hornerCopy bit y out) n t).basis=regValue out s.basis := by
    rw [second.2.2,ySame,first.2.1 bit bitAway,first.2.2]
    simp
  have basis : (run (hornerCopy bit y out) n t).basis=s.basis := by
    funext q
    by_cases h : q∈out
    · exact (regValue_eq_iff _ _ _).mp value q h
    · exact (second.2.1 q h).trans (first.2.1 q h)
  have phase := second.1.trans first.1
  generalize h : run (hornerCopy bit y out) n t=u at basis phase ⊢
  cases u
  cases s
  congr

theorem hornerCopy_counts (bit : Wire) (y out : List Wire) (len : y.length=out.length) :
    toffoliCount (hornerCopy bit y out)=y.length ∧
    measurementCount (hornerCopy bit y out)=0 :=
  copyRegister_counts (some bit) y out len

theorem hornerCopy_support (bit : Wire) (y out : List Wire) (len : y.length=out.length) :
    wires (hornerCopy bit y out)=if y.isEmpty then ∅ else (bit::(y++out)).toFinset := by
  simpa [hornerCopy] using copyRegister_wires (some bit) y out len

end ECDSAAdd.Arithmetic.Paper935
