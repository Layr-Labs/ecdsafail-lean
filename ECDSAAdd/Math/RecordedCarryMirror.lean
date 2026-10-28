import Mathlib

namespace ECDSAAdd.Math.RecordedCarryMirror

/-- Adding the unchanged source to the complemented output reproduces the
original carry at each binary prefix. This is why Apply must use the saved
Defer outcome, rather than a fresh inverse measurement. -/
theorem complement_mirror_carry (A B cin M : Nat) (hM : 0<M) (hB : B<M) :
    (A+(M-1-(A+B+cin)%M)+cin)/M=(A+B+cin)/M := by
  let S := (A+B+cin)%M
  let Q := (A+B+cin)/M
  have hs : S<M := Nat.mod_lt _ hM
  have split : S+M*Q=A+B+cin := Nat.mod_add_div _ _
  have decomposition : A+(M-1-S)+cin=(M-1-B)+M*Q := by omega
  rw [decomposition,Nat.add_mul_div_left _ _ hM,Nat.div_eq_of_lt (by omega),Nat.zero_add]

/-- The same mirror restores the complemented original target, independently
of the initial carry-in. No width or input-distribution approximation enters. -/
theorem complement_mirror_value (A B cin M : Nat) (hM : 0<M) (hB : B<M) :
    (A+(M-1-(A+B+cin)%M)+cin)%M=M-1-B := by
  let S := (A+B+cin)%M
  let Q := (A+B+cin)/M
  have hs : S<M := Nat.mod_lt _ hM
  have split : S+M*Q=A+B+cin := Nat.mod_add_div _ _
  have decomposition : A+(M-1-S)+cin=(M-1-B)+M*Q := by omega
  rw [decomposition,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega)]

end ECDSAAdd.Math.RecordedCarryMirror
#print axioms ECDSAAdd.Math.RecordedCarryMirror.complement_mirror_carry
#print axioms ECDSAAdd.Math.RecordedCarryMirror.complement_mirror_value
