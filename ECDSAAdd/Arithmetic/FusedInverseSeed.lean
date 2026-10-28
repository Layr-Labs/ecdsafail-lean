import ECDSAAdd.Arithmetic.FusedRetainedThreshold
import ECDSAAdd.Math.FusedSignedHalfInverse

namespace ECDSAAdd.Arithmetic

/-- The exact comparator-and-X stream toggles normalized parity for either
incoming flag value. It is a fresh forward measurement program in both uses. -/
theorem fusedHalfParityToggle_correct (x T carry : List Wire) (cin q : Wire)
    (hn : (q::cin::(x++T++carry)).Nodup) (hx : 3≤x.length)
    (hT : T.length=x.length) (hc : carry.length=x.length)
    (hK : FusedSignedHalf.halfThreshold p<2^x.length) (s : State) (m : List Bool)
    (hT0 : regValue T s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi : s.basis cin=false) :
    (run (fusedHalfParityClear x T carry cin q) m s).phase=s.phase ∧
    (∀ w,w≠q → (run (fusedHalfParityClear x T carry cin q) m s).basis w=s.basis w) ∧
    (run (fusedHalfParityClear x T carry cin q) m s).basis q=
      (s.basis q ^^ decide (FusedSignedHalf.halfThreshold p≤regValue x s.basis)) := by
  let progCmp := compareLtMultipleEight x T carry cin q (FusedSignedHalf.halfThreshold p)
  let t := run progCmp m s
  have hcmp := compareLtMultipleEight_correct x T carry cin q
    (FusedSignedHalf.halfThreshold p) hn hx hT hc hK
    FusedSignedHalf.secp_halfThreshold_multiple_eight s m hT0 hc0 hi
  have hqt : t.basis q=(s.basis q ^^ decide (regValue x s.basis<FusedSignedHalf.halfThreshold p)) :=
    hcmp.2.2
  rw [fusedHalfParityClear,run_append,run_take]
  change t.phase=s.phase ∧
    (∀ w,w≠q → (writeBit t.basis q (!t.basis q)) w=s.basis w) ∧
    (writeBit t.basis q (!t.basis q)) q=
      (s.basis q ^^ decide (FusedSignedHalf.halfThreshold p≤regValue x s.basis))
  refine ⟨hcmp.1,?_,?_⟩
  · intro w hw
    simpa [writeBit,hw] using hcmp.2.1 w hw
  · simp only [writeBit,Function.update_self,hqt]
    by_cases hlt : regValue x s.basis<FusedSignedHalf.halfThreshold p
    · have hnot : ¬FusedSignedHalf.halfThreshold p≤regValue x s.basis := by omega
      cases s.basis q <;> simp [hlt,hnot]
    · have hle : FusedSignedHalf.halfThreshold p≤regValue x s.basis := by omega
      cases s.basis q <;> simp [hlt,hle]

/-- Seed the normalized parity from a clean flag with full scratch, frame and
phase restoration for every independent measurement record. -/
theorem fusedHalfParitySeed_correct (x T carry : List Wire) (cin q : Wire)
    (hn : (q::cin::(x++T++carry)).Nodup) (hx : 3≤x.length)
    (hT : T.length=x.length) (hc : carry.length=x.length)
    (hK : FusedSignedHalf.halfThreshold p<2^x.length) (s : State) (m : List Bool)
    (hT0 : regValue T s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi : s.basis cin=false) (hq : s.basis q=false) :
    (run (fusedHalfParityClear x T carry cin q) m s).phase=s.phase ∧
    (∀ w,w≠q → (run (fusedHalfParityClear x T carry cin q) m s).basis w=s.basis w) ∧
    (run (fusedHalfParityClear x T carry cin q) m s).basis q=
      decide (FusedSignedHalf.halfThreshold p≤regValue x s.basis) := by
  have hh := fusedHalfParityToggle_correct x T carry cin q hn hx hT hc hK s m hT0 hc0 hi
  simpa only [hq,Bool.false_xor] using hh

end ECDSAAdd.Arithmetic
