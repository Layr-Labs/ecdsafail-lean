import ECDSAAdd.Arithmetic.SignedWordBits

set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.NearestLift

/-- Recover a small centered-modulus quotient from one near-boundary test.
The modulus is exactly M-F; no high comparison bit is truncated. -/
theorem correction (M F A S k H R : Int)
    (hM : 0 < M) (hF : 0 < F) (hsmall : 7*F < M)
    (hEven : M%2=0) (hOdd : F%2=1)
    (hA : -(M-F-1)/2 ≤ A ∧ A ≤ (M-F-1)/2)
    (hk : -3 ≤ k ∧ k ≤ 3) (hH : -3 ≤ H ∧ H ≤ 3)
    (hS : S=A+k*(M-F)) (hWord : S+M/2=H*M+R)
    (hR : 0 ≤ R ∧ R < M) :
    k=H+(if S<0 then -1 else 1)*
      (if (if S<0 then R else M-1-R) <
        |H| * F+(F-1)/2+(if S<0 then 1 else 0) then 1 else 0) := by
  obtain ⟨hk0,hk1⟩ := hk
  obtain ⟨hH0,hH1⟩ := hH
  interval_cases k <;> interval_cases H <;> norm_num at *
  all_goals split_ifs <;> omega

/-- The near-boundary threshold has only 34 bits for secp256k1.
This licenses an exact high-zero prefix plus a 34-bit low comparison. -/
theorem secp_threshold_bound (H : Int) (hH : -3 ≤ H ∧ H ≤ 3) (b : Bool) :
    0 ≤ |H| * (2^32+977)+(2^32+976)/2+b.toNat ∧
    |H| * (2^32+977)+(2^32+976)/2+b.toNat < 2^34 := by
  obtain ⟨h0,h1⟩ := hH
  interval_cases H <;> cases b <;> norm_num

end ECDSAAdd.Arithmetic.NearestLift
#print axioms ECDSAAdd.Arithmetic.NearestLift.correction
#print axioms ECDSAAdd.Arithmetic.NearestLift.secp_threshold_bound
