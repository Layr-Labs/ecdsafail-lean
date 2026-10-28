import ECDSAAdd.Math.SquareReduction

namespace ECDSAAdd.Arithmetic

def compactNegateValue (N p c X : Nat) (enabled : Bool) : Nat :=
  ((if enabled && decide (X=0) then c else 0)+
    ((if enabled then p+1 else 0)+(if enabled then N-1-X else X))%N)%N

theorem compactNegateValue_exact (N p c X : Nat) (enabled : Bool)
    (hpc : p+c=N) (hc : 1<c) (hX : X<p) :
    compactNegateValue N p c X enabled=(if enabled then (p-X)%p else X) := by
  have hp : 0<p := by omega
  have hn : X<N := by omega
  cases enabled
  · simp [compactNegateValue,Nat.mod_eq_of_lt hn]
  · by_cases zero : X=0
    · subst X
      have pb : p<N := by omega
      have sum : p+1+(N-1)=p+N := by omega
      simp only [compactNegateValue,if_true,Bool.true_and,decide_true,Nat.sub_zero]
      rw [sum,Nat.add_mod_right,Nat.mod_eq_of_lt pb,show c+p=N by omega,Nat.mod_self,Nat.mod_self]
    · have pn : p-X<N := by omega
      have pp : p-X<p := by omega
      have sum : p+1+(N-1-X)=N+(p-X) := by omega
      simp only [compactNegateValue,if_true,Bool.true_and,zero,decide_false,Bool.false_eq_true,if_false,Nat.zero_add]
      rw [sum,Nat.add_mod_left,Nat.mod_eq_of_lt pn,Nat.mod_eq_of_lt pn,Nat.mod_eq_of_lt pp]

theorem compactNegateValue_zero (N p c X : Nat) (enabled : Bool)
    (hpc : p+c=N) (hc : 1<c) (hX : X<p) :
    (enabled && decide (compactNegateValue N p c X enabled=0))=(enabled && decide (X=0)) := by
  rw [compactNegateValue_exact N p c X enabled hpc hc hX]
  cases enabled
  · rfl
  · by_cases zero : X=0
    · simp [zero]
    · have pp : p-X<p := by omega
      have nonzero : p-X≠0 := by omega
      simp [zero,Nat.mod_eq_of_lt pp,nonzero]

end ECDSAAdd.Arithmetic
