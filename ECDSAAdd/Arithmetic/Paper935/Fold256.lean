import ECDSAAdd.Arithmetic.Paper935.Fold16Word
import ECDSAAdd.Arithmetic.Paper935.FoldHalfMath
import ECDSAAdd.Framework.WireRename

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Keep the low window fixed, moving the sixteen pool lines above the
256-bit data register. The reference control remains wire zero. -/
def fold256Place (q : Wire) : Wire := if q<59 then q else q+198

def fold256Program (subtract : Bool) : Program := renameProgram fold256Place (fold16Program subtract)
def fold256Word : List Wire := List.range' 1 256
def Fold256Ready (s : BasisState) : Prop := ∀ i<16,s (257+i)=false

theorem fold256Place_injective : Function.Injective fold256Place := by
  intro a b h
  simp only [fold256Place] at h
  dsimp only [Wire] at *
  split_ifs at h <;> omega

private theorem pull_word (s : State) :
    regValue fold16Word (pullState fold256Place s).basis=regValue fold16Word s.basis := by
  apply regValue_congr
  intro q hq
  have small : q<59 := by
    simp only [fold16Word,List.mem_range'] at hq
    dsimp only [Wire]
    omega
  simp only [pullState,fold256Place,if_pos small]

/-- Relocation preserves the complete fold contract while making room for
the upper 198 data bits. -/
theorem fold256_low_contract (subtract : Bool) (s : State) (m : List Bool)
    (ready : Fold256Ready s.basis) :
    let out := run (fold256Program subtract) m s
    regValue fold16Word out.basis=
      (regValue fold16Word s.basis+(if s.basis 0 then fold16Literal subtract else 0))%2^58 ∧
    Fold256Ready out.basis ∧ out.basis 0=s.basis 0 ∧ out.phase=s.phase := by
  have clean : Fold16Ready 0 (pullState fold256Place s).basis := by
    intro i hi lower
    simpa only [pullState,fold256Place,show ¬59+i<59 by omega,if_false,
      show 59+i+198=257+i by omega] using ready i hi
  have contract := fold16Program_contract subtract (pullState fold256Place s) m clean
  have execution := run_rename fold256Place fold256Place_injective (fold16Program subtract) m s
  dsimp only at contract
  rw [←execution,pull_word,pull_word] at contract
  refine ⟨contract.1,?_,contract.2.2.1,contract.2.2.2⟩
  intro i hi
  have h := contract.2.1 i hi (by omega)
  simpa only [pullState,fold256Place,show ¬59+i<59 by (try dsimp only [Wire]); omega,if_false,
    show 59+i+198=257+i by (try dsimp only [Wire]); omega] using h

theorem fold256_frame (subtract : Bool) (s : State) (m : List Bool) (q : Wire)
    (outside : (59≤q ∧ q<257) ∨ 273≤q) :
    (run (fold256Program subtract) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro member
  rw [fold256Program,renameProgram_support] at member
  obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp member
  have bound := Finset.mem_range.mp (fold16Program_support subtract ha)
  simp only [fold256Place] at eq
  dsimp only [Wire] at *
  split_ifs at eq <;> omega

private theorem word_split : fold256Word=fold16Word++List.range' 59 198 := by
  exact (List.range'_append_1 (s:=1) (m:=58) (n:=198)).symm

/-- Exact 256-bit truncated-window arithmetic. The high word is physically
untouched; no no-borrow assumption is needed for this modular-window result. -/
theorem fold256_word (subtract : Bool) (s : State) (m : List Bool)
    (ready : Fold256Ready s.basis) :
    regValue fold256Word (run (fold256Program subtract) m s).basis=
      (regValue fold256Word s.basis/2^58)*2^58+
      (regValue fold256Word s.basis%2^58+(if s.basis 0 then fold16Literal subtract else 0))%2^58 := by
  have low := (fold256_low_contract subtract s m ready).1
  have high : regValue (List.range' 59 198) (run (fold256Program subtract) m s).basis=
      regValue (List.range' 59 198) s.basis := by
    apply regValue_congr
    intro q hq
    simp only [List.mem_range'] at hq
    apply fold256_frame subtract s m q (Or.inl ?_)
    dsimp only [Wire]
    omega
  have bound : regValue fold16Word s.basis<2^58 := by
    simpa only [fold16Word,List.length_range'] using regValue_lt fold16Word s.basis
  rw [word_split]
  simp only [regValue_append,fold16Word,List.length_range'] at low bound ⊢
  rw [high,low,Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt bound,
    Nat.zero_add,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]
  omega

/-- The subtraction branch is exactly the numerical windowSubtract used
by the author-halving failure event, under its actual control bit. -/
theorem fold256_subtract (s : State) (m : List Bool) (ready : Fold256Ready s.basis) :
    regValue fold256Word (run (fold256Program true) m s).basis=
      if s.basis 0 then windowSubtract 58 (2^32+976) (regValue fold256Word s.basis)
      else regValue fold256Word s.basis := by
  rw [fold256_word true s m ready]
  generalize regValue fold256Word s.basis=r
  cases s.basis 0 with
  | false =>
    simp only [Bool.false_eq_true,if_false,Nat.add_zero,Nat.mod_mod]
    omega
  | true =>
    simp only [if_true,fold16Literal,windowSubtract]
    rw [show r%2^58+(2^58-(2^32+976))=r%2^58+2^58-(2^32+976) by omega]

private theorem low_bit (s : BasisState) : (s 1).toNat=regValue fold16Word s%2 := by
  change (s 1).toNat=((if s 1 then 1 else 0)+2*regValue (List.range' 2 57) s)%2
  cases s 1 <;> simp

/-- The author's fold literal is even in either direction, so mint/kill
can reuse the original low bit after the measured fold. -/
theorem fold256_low_bit (subtract : Bool) (s : State) (m : List Bool)
    (ready : Fold256Ready s.basis) :
    (run (fold256Program subtract) m s).basis 1=s.basis 1 := by
  have value := (fold256_low_contract subtract s m ready).1
  have before := low_bit s.basis
  have after := low_bit (run (fold256Program subtract) m s).basis
  have even : fold16Literal subtract%2=0 := by cases subtract <;> decide
  have selected : (if s.basis 0 then fold16Literal subtract else 0)%2=0 := by
    cases s.basis 0 <;> simp [even]
  have parity : ((run (fold256Program subtract) m s).basis 1).toNat=(s.basis 1).toNat := by omega
  cases h : (run (fold256Program subtract) m s).basis 1 <;> cases k : s.basis 1 <;>
    simp only [h,k,Bool.toNat_false,Bool.toNat_true] at parity <;> first | rfl | omega

end ECDSAAdd.Arithmetic.Paper935
