import ECDSAAdd.Arithmetic.Paper935.SignCoreValue

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] sign24Program signWindow signComplement signPayload

private theorem low_mod (s : BasisState) :
    regValue sign24Word s=regValue signPayload s%2^58 := by
  have split : signPayload=sign24Word++List.range' 59 198 := by decide +kernel
  have small : regValue sign24Word s<2^58 := by
    simpa only [sign24Word,List.length_range'] using regValue_lt sign24Word s
  rw [split,regValue_append]
  change _=(_+2^58*_)%2^58
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small]

private theorem window_subtract (s : State) (m : List Bool)
    (ready : SignReady s.basis)
    (noborrow : s.basis 0=true → 2^32+976≤regValue sign24Word s.basis) :
    regValue signPayload (run (signWindow true) m s).basis=
      regValue signPayload s.basis-(if s.basis 0 then 2^32+976 else 0) := by
  have low := (signWindow_contract true s m ready).1
  have small : regValue sign24Word s.basis<2^58 := by
    simpa only [sign24Word,List.length_range'] using regValue_lt sign24Word s.basis
  have lv : regValue sign24Word (run (signWindow true) m s).basis=
      regValue sign24Word s.basis-(if s.basis 0 then 2^32+976 else 0) := by
    rw [low]
    cases h : s.basis 0 with
    | false => simpa only [Bool.false_eq_true,if_false,Nat.add_zero,Nat.sub_zero] using Nat.mod_eq_of_lt small
    | true =>
      have ge := noborrow h
      simp only [if_true,sign24Literal]
      have eq : regValue sign24Word s.basis+(2^58-(2^32+976))=
          2^58+(regValue sign24Word s.basis-(2^32+976)) := by omega
      rw [eq,Nat.add_mod]
      omega
  have high : regValue (List.range' 59 198) (run (signWindow true) m s).basis=
      regValue (List.range' 59 198) s.basis := by
    apply regValue_congr
    intro q hq
    simp only [List.mem_range'] at hq
    obtain ⟨i,hi,rfl⟩ := hq
    exact signWindow_high_frame true s m _ (by dsimp only [Wire]; omega)
      (by dsimp only [Wire] at *; omega)
  have split : signPayload=sign24Word++List.range' 59 198 := by decide +kernel
  rw [split,regValue_append,regValue_append,lv,high]
  cases h : s.basis 0 with
  | false => simp
  | true =>
    have ge := noborrow h
    simp only [if_true]
    omega

/-- Arithmetic value of the actual sign core. The no-borrow condition is
separate from scratch cleanup and from the caller's negate-control encoding. -/
theorem signCore_value (s : State) (m : List Bool) (ready : SignReady s.basis)
    (noborrow : s.basis 0=true →
      2^32+976≤(2^256-1-regValue signPayload s.basis)%2^58) :
    regValue signPayload (run (signCore false) m s).basis=
      if s.basis 0 then fold32Prime-regValue signPayload s.basis
      else regValue signPayload s.basis := by
  have len : signPayload.length=256 := by simp [signPayload]
  let t := run (signComplement 0 signPayload) m s
  have comp := signComplement_correct 0 signPayload
    (by unfold signPayload; exact List.nodup_range') (by simp [signPayload]) s m
  have control : t.basis 0=s.basis 0 := comp.2.1 0 (by simp [signPayload])
  have clean : SignReady t.basis := by
    intro i hi
    rw [comp.2.1 (257+i) (by simp [signPayload])]
    exact ready i hi
  have window : t.basis 0=true → 2^32+976≤regValue sign24Word t.basis := by
    intro enabled
    have hs := control.symm.trans enabled
    rw [low_mod,comp.2.2]
    simpa only [hs,if_true,len] using noborrow hs
  have result := window_subtract t m clean window
  simp only [signCore,Bool.false_eq_true,if_false,run_append,run_take]
  simp only [(signComplement_counts 0 signPayload).2,List.drop_zero]
  rw [result,comp.2.2,control]
  rw [len]
  cases s.basis 0 <;> simp only [Bool.false_eq_true,if_false,if_true,Nat.sub_zero]
  norm_num [fold32Prime]
  omega

end ECDSAAdd.Arithmetic.Paper935
