import ECDSAAdd.Arithmetic.Paper935.Lift24Word
import ECDSAAdd.Framework.WireRename

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] lift24Program

/-- The author's separately compiled minus-one routine undoes plus-one on
all window values, using fresh arbitrary measurement records for each run. -/
theorem lift24Program_roundtrip (s : State) (m n : List Bool)
    (ready : Lift24Ready 0 s.basis) :
    run (lift24Program true) n (run (lift24Program false) m s)=s := by
  let t := run (lift24Program false) m s
  let u := run (lift24Program true) n t
  have fwd := lift24Program_contract false s m ready
  have inv := lift24Program_contract true t n fwd.2.1
  have word : regValue lift24Word u.basis=regValue lift24Word s.basis := by
    have hf := fwd.1
    have hi := inv.1
    change regValue lift24Word t.basis=_ at hf
    change regValue lift24Word u.basis=_ at hi
    have hc := fwd.2.2.1
    change t.basis 0=s.basis 0 at hc
    rw [hc] at hi
    have bound := regValue_lt lift24Word s.basis
    have len : lift24Word.length=58 := rfl
    rw [len] at bound
    norm_num only [Nat.reducePow] at bound
    cases h : s.basis 0 <;> simp [h,lift24Literal] at hf hi <;> omega
  apply State.extensionality
  · exact inv.2.2.2.trans fwd.2.2.2
  · change u.basis=s.basis
    funext q
    dsimp only [Wire] at q
    by_cases zero : q=0
    · subst q
      exact inv.2.2.1.trans fwd.2.2.1
    by_cases data : q<59
    · exact (regValue_eq_iff lift24Word _ _).mp word q (by
        exact List.mem_range'.mpr ⟨q-1,by omega,by omega⟩)
    by_cases pool : q<83
    · have hq : 59+(q-59)=q := by omega
      rw [←hq,inv.2.1 (q-59) (by omega) (by omega),ready (q-59) (by omega) (by omega)]
    · have away (b : Bool) : q∉wires (lift24Program b) := by
        intro mem
        have := lift24Program_support b mem
        simp only [Finset.mem_range] at this
        omega
      exact (run_preserves_outside _ n t q (away true)).trans
        (run_preserves_outside _ m s q (away false))

end ECDSAAdd.Arithmetic.Paper935
