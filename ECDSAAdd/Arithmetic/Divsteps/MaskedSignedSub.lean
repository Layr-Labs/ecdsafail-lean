import ECDSAAdd.Arithmetic.MeasuredMaskedAdder
import ECDSAAdd.Arithmetic.SignedWordBits

namespace ECDSAAdd.Arithmetic.Divsteps

/-- The existing measured mask subtractor is exact on signed words whenever the
result fits; the temporary mask, carry-in, carries and phase are restored. -/
theorem maskedSub_signed_spec (c cin : Wire) (src mask y carry : List Wire)
    (hn : (c::cin::(src++mask++y++carry)).Nodup)
    (hs : src.length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length) (C : Bool) (A B : Int)
    (hlo : -((2^(y.length-1):Nat):Int) ≤ B-(if C then A else 0))
    (hhi : B-(if C then A else 0) < ((2^(y.length-1):Nat):Int)) :
    Triple (fun s => s c=C ∧ signedRegValue src s=A ∧ regValue mask s=0 ∧
      signedRegValue y s=B ∧ s cin=false ∧ regValue carry s=0)
      (measuredMaskedSubInPlace c src mask y carry cin)
      (fun s => s c=C ∧ signedRegValue src s=A ∧ regValue mask s=0 ∧
        signedRegValue y s=B-(if C then A else 0) ∧ s cin=false ∧ regValue carry s=0) := by
  intro s m h
  let X := regValue src s.basis
  let Y := regValue y s.basis
  have hw : src.length=y.length := hs.trans ht
  have hX : X<2^y.length := by simpa [X,hw] using regValue_lt src s.basis
  have hA : signedDecode y.length X=A := by simpa [signedRegValue,hw,X] using h.2.1
  have hB : signedDecode y.length Y=B := h.2.2.2.1
  have hZ : signedDecode y.length (if C then X else 0)=(if C then A else 0) := by
    cases C
    · simp [signedDecode]
    · simpa using hA
  have hval := signedWordValue_lift y.length true (if C then X else 0) Y
    (by omega) (by cases C <;> simp [hX])
    (by simpa [signedIntegerValue,hZ,hB] using hlo)
    (by simpa [signedIntegerValue,hZ,hB] using hhi)
  simp only [signedWordValue,signedIntegerValue,if_true,hZ,hB] at hval
  obtain ⟨hp,ho⟩ := measuredMaskedSubInPlace_spec c cin src mask y carry hn hs ht hc C X Y s m
    ⟨⟨⟨⟨⟨h.1,rfl⟩,h.2.2.1⟩,rfl⟩,h.2.2.2.2.1⟩,h.2.2.2.2.2⟩
  simp only [Holds.holds] at ho
  refine ⟨hp,ho.1.1.1.1.1,?_,ho.1.1.1.2,?_,ho.1.2,ho.2⟩
  · unfold signedRegValue
    rw [ho.1.1.1.1.2,hw]
    exact hA
  · unfold signedRegValue
    rw [ho.1.1.2]
    exact hval

end ECDSAAdd.Arithmetic.Divsteps
