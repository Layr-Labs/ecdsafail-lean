import ECDSAAdd.Arithmetic.Paper935.Fold256

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Source unconditional mint/fold/kill prefix, before the cyclic rotation.
Wire zero is the fresh parity copy; the same sixteen fold lines are reused. -/
def foldParityProgram : Program := [.CX 1 0]++fold256Program true++[.CX 1 0]

private theorem word_update (s : BasisState) (v : Bool) :
    regValue fold256Word (writeBit s 0 v)=regValue fold256Word s := by
  apply regValue_congr
  intro q hq
  have away : q≠0 := by
    simp only [fold256Word,List.mem_range'] at hq
    dsimp only [Wire]
    omega
  exact Function.update_of_ne away _ _

private theorem word_parity (s : BasisState) : s 1=decide (regValue fold256Word s%2=1) := by
  change s 1=decide (((if s 1 then 1 else 0)+2*regValue (List.range' 2 255) s)%2=1)
  cases s 1 <;> simp

/-- The parity copy is released against the unchanged low data bit. No
measurement cleanup premise is supplied by the caller. -/
theorem foldParity_contract (s : State) (m : List Bool)
    (ready : Fold256Ready s.basis) (zero : s.basis 0=false) :
    let out := run foldParityProgram m s
    regValue fold256Word out.basis=
      (if regValue fold256Word s.basis%2=1 then windowSubtract 58 (2^32+976) (regValue fold256Word s.basis)
        else regValue fold256Word s.basis) ∧
    Fold256Ready out.basis ∧ out.basis 0=false ∧ out.phase=s.phase := by
  let minted : State := ⟨s.phase,writeBit s.basis 0 (s.basis 1)⟩
  have first : run [.CX 1 0] m s=minted := by simp [run,zero,minted]
  have mintedReady : Fold256Ready minted.basis := by
    intro i hi
    simpa only [minted,writeBit,Function.update_of_ne (show (257+i:Wire)≠0 by dsimp only [Wire]; omega)] using ready i hi
  let tape := m.drop (measurementCount (fold256Program true))
  have contract := fold256_low_contract true minted m mintedReady
  have value := fold256_subtract minted m mintedReady
  have lowbit := fold256_low_bit true minted m mintedReady
  dsimp only at contract
  generalize hfold : run (fold256Program true) m minted=folded at contract value lowbit
  have foldedControl : folded.basis 0=s.basis 1 := by
    exact contract.2.2.1.trans (by simp [minted,writeBit])
  have foldedLow : folded.basis 1=s.basis 1 := by
    exact lowbit.trans (by simp [minted,writeBit])
  have last : run [.CX 1 0] tape folded=⟨folded.phase,writeBit folded.basis 0 false⟩ := by
    simp only [run,foldedControl,foldedLow,Bool.xor_self]
  have execution : run foldParityProgram m s=⟨folded.phase,writeBit folded.basis 0 false⟩ := by
    rw [foldParityProgram,run_append,run_take,run_append,run_take,first]
    change run [.CX 1 0] (m.drop (measurementCount (fold256Program true))) (run (fold256Program true) m minted)=_
    rw [hfold]
    exact last
  dsimp only
  rw [execution]
  refine ⟨?_,?_,by simp [writeBit],contract.2.2.2⟩
  · rw [word_update]
    have sourceWord : regValue fold256Word minted.basis=regValue fold256Word s.basis := word_update s.basis _
    rw [sourceWord] at value
    have sourceControl : minted.basis 0=s.basis 1 := by simp [minted,writeBit]
    rw [sourceControl,word_parity s.basis] at value
    simpa only [decide_eq_true_eq] using value
  · intro i hi
    simpa only [writeBit,Function.update_of_ne (show (257+i:Wire)≠0 by dsimp only [Wire]; omega)] using contract.2.1 i hi

end ECDSAAdd.Arithmetic.Paper935
