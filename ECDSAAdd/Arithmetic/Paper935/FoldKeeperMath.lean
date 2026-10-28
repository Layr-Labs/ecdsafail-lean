import ECDSAAdd.Arithmetic.Paper935.FoldHalfMath

namespace ECDSAAdd.Arithmetic.Paper935

/-- Recover an emitted block carry by borrowing the same literal and incoming
carry from the already written modular sum. -/
theorem foldKeeper_borrow (width a k : Nat) (cin : Bool)
    (ha : a<2^width) (hk : k<2^width) :
    (a+k+cin.toNat)%2^width<k+cin.toNat ↔ 2^width≤a+k+cin.toNat := by
  have hc : cin.toNat≤1 := by cases cin <;> decide
  by_cases lower : 2^width≤a+k+cin.toNat
  · rw [Nat.mod_eq_sub_mod lower,Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The author's controlled keeper erasure also handles disabled lanes: their
incoming carries are zero, so both the saved carry and erase toggle vanish. -/
theorem foldKeeper_controlled (width a k : Nat) (control cin : Bool)
    (ha : a<2^width) (hk : k<2^width) (inactive : control=false → cin=false) :
    decide (2^width≤a+(if control then k else 0)+cin.toNat)=
      (control && decide ((a+(if control then k else 0)+cin.toNat)%2^width<k+cin.toNat)) := by
  cases control with
  | false => simp [inactive rfl,show ¬2^width≤a by omega]
  | true =>
    simp only [ite_true,Bool.true_and]
    simp only [←foldKeeper_borrow width a k cin ha hk]

end ECDSAAdd.Arithmetic.Paper935
