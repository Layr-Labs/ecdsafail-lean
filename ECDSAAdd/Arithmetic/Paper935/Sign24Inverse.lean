import ECDSAAdd.Arithmetic.Paper935.Sign24Word
import ECDSAAdd.Framework.WireRename

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] sign24Program

/-- The author's separately compiled negative-constant routine undoes positive-constant on
all window values, using fresh arbitrary measurement records for each run. -/
theorem sign24Program_roundtrip (s : State) (m n : List Bool)
    (ready : Sign24Ready 0 s.basis) :
    run (sign24Program true) n (run (sign24Program false) m s)=s := by
  let t := run (sign24Program false) m s
  let u := run (sign24Program true) n t
  have fwd := sign24Program_contract false s m ready
  have inv := sign24Program_contract true t n fwd.2.1
  have word : regValue sign24Word u.basis=regValue sign24Word s.basis := by
    have hf := fwd.1
    have hi := inv.1
    change regValue sign24Word t.basis=_ at hf
    change regValue sign24Word u.basis=_ at hi
    have hc := fwd.2.2.1
    change t.basis 0=s.basis 0 at hc
    rw [hc] at hi
    have bound := regValue_lt sign24Word s.basis
    have len : sign24Word.length=58 := rfl
    rw [len] at bound
    norm_num only [Nat.reducePow] at bound
    cases h : s.basis 0 <;> simp [h,sign24Literal] at hf hi <;> omega
  apply State.extensionality
  · exact inv.2.2.2.trans fwd.2.2.2
  · change u.basis=s.basis
    funext q
    dsimp only [Wire] at q
    by_cases zero : q=0
    · subst q
      exact inv.2.2.1.trans fwd.2.2.1
    by_cases data : q<59
    · exact (regValue_eq_iff sign24Word _ _).mp word q (by
        exact List.mem_range'.mpr ⟨q-1,by omega,by omega⟩)
    by_cases pool : q<83
    · have hq : 59+(q-59)=q := by omega
      rw [←hq,inv.2.1 (q-59) (by omega) (by omega),ready (q-59) (by omega) (by omega)]
    · have away (b : Bool) : q∉wires (sign24Program b) := by
        intro mem
        have := sign24Program_support b mem
        simp only [Finset.mem_range] at this
        omega
      exact (run_preserves_outside _ n t q (away true)).trans
        (run_preserves_outside _ m s q (away false))

theorem sign24Program_roundtrip_reverse (s : State) (m n : List Bool)
    (ready : Sign24Ready 0 s.basis) :
    run (sign24Program false) n (run (sign24Program true) m s)=s := by
  let t := run (sign24Program true) m s
  let u := run (sign24Program false) n t
  have fwd := sign24Program_contract true s m ready
  have inv := sign24Program_contract false t n fwd.2.1
  have word : regValue sign24Word u.basis=regValue sign24Word s.basis := by
    have hf := fwd.1
    have hi := inv.1
    change regValue sign24Word t.basis=_ at hf
    change regValue sign24Word u.basis=_ at hi
    have hc := fwd.2.2.1
    change t.basis 0=s.basis 0 at hc
    rw [hc] at hi
    have bound := regValue_lt sign24Word s.basis
    have len : sign24Word.length=58 := rfl
    rw [len] at bound
    norm_num only [Nat.reducePow] at bound
    cases h : s.basis 0 <;> simp [h,sign24Literal] at hf hi <;> omega
  apply State.extensionality
  · exact inv.2.2.2.trans fwd.2.2.2
  · change u.basis=s.basis
    funext q
    dsimp only [Wire] at q
    by_cases zero : q=0
    · subst q
      exact inv.2.2.1.trans fwd.2.2.1
    by_cases data : q<59
    · exact (regValue_eq_iff sign24Word _ _).mp word q (by
        exact List.mem_range'.mpr ⟨q-1,by omega,by omega⟩)
    by_cases pool : q<83
    · have hq : 59+(q-59)=q := by omega
      rw [←hq,inv.2.1 (q-59) (by omega) (by omega),ready (q-59) (by omega) (by omega)]
    · have away (b : Bool) : q∉wires (sign24Program b) := by
        intro mem
        have := sign24Program_support b mem
        simp only [Finset.mem_range] at this
        omega
      exact (run_preserves_outside _ n t q (away false)).trans
        (run_preserves_outside _ m s q (away true))


end ECDSAAdd.Arithmetic.Paper935
