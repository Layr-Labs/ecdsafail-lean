import ECDSAAdd.Arithmetic.BalancedSharedPorts
import ECDSAAdd.Arithmetic.ConditionalXor

set_option maxHeartbeats 500000
namespace ECDSAAdd.Arithmetic

private theorem bounded_high (M low value : Nat) (bit : Bool)
    (h : low+M*bit.toNat=value) (hv : value<M) : low=value ∧ bit=false := by
  cases bit <;> simp at h ⊢ <;> omega

/-- A canonical field value in a 257-bit word has a zero extension bit. -/
theorem balancedCanonical_high_zero (low : List Wire) (high : Wire) (base : BasisState)
    (value : Nat) (hv : value<2^low.length) (he : regValue (low++[high]) base=value) :
    regValue low base=value ∧ base high=false := by
  have h := (regValue_append low [high] base).symm.trans he
  have b : regValue [high] base=(base high).toNat := by
    cases hb : base high <;> simp [regValue,hb]
  rw [b] at h
  exact bounded_high _ _ _ _ h hv

/-- Narrow the two data ports while retaining the extension bits in the
caller frame. This is a register identity, independent of input sampling. -/
theorem balancedPair_narrow (r y : List Wire) (rh yh : Wire) (base st : BasisState)
    (X Y : Nat) (hx : X<2^r.length) (hy : Y<2^y.length)
    (h : PairFrame (r++[rh]) (y++[yh]) base X Y st)
    (hbaseR : base rh=false) (hbaseY : base yh=false) : PairFrame r y base X Y st := by
  have vr := balancedCanonical_high_zero r rh st X hx h.1
  have vy := balancedCanonical_high_zero y yh st Y hy h.2.1
  refine ⟨vr.1,vy.1,?_⟩
  intro q hr hy
  by_cases er : q=rh
  · subst q
    exact vr.2.trans hbaseR.symm
  by_cases ey : q=yh
  · subst q
    exact vy.2.trans hbaseY.symm
  exact h.2.2 q (by simp [hr,er]) (by simp [hy,ey])

/-- Extend a verified low-word pair result using the preserved zero high
sites. Both sites must lie outside the two mutable 256-bit words. -/
theorem balancedPair_widen (r y : List Wire) (rh yh : Wire) (base st : BasisState)
    (X Y : Nat) (h : PairFrame r y base X Y st)
    (hr : rh∉r ∧ rh∉y) (hy : yh∉r ∧ yh∉y)
    (hbaseR : base rh=false) (hbaseY : base yh=false) :
    PairFrame (r++[rh]) (y++[yh]) base X Y st := by
  have er : st rh=false := (h.2.2 rh hr.1 hr.2).trans hbaseR
  have ey : st yh=false := (h.2.2 yh hy.1 hy.2).trans hbaseY
  refine ⟨?_,?_,?_⟩
  · rw [regValue_append,h.1]
    simp [regValue,er]
  · rw [regValue_append,h.2.1]
    simp [regValue,ey]
  · intro q hqr hqy
    exact h.2.2 q (fun hq => hqr (List.mem_append_left _ hq))
      (fun hq => hqy (List.mem_append_left _ hq))

end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.balancedPair_narrow
#print axioms ECDSAAdd.Arithmetic.balancedPair_widen
