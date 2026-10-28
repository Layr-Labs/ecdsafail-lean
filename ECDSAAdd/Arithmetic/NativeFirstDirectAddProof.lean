import ECDSAAdd.Arithmetic.NativeFirstDirectValues
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] mappedAdd run

/-- Actual H emission, all records and incoming phases; carry cleaning follows
from the complete outside-target frame. -/
theorem hAdd_spec (w : Nat → Wire) (inverse : Bool) (s : State) (m : List Bool)
    (hn : (w 1797::(wireBlock w 4 253++wireBlock w 1540 252)).Nodup)
    (hs : ∀q∈mappedWires (hBits w inverse),
      q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252))
    (hc : ∀q∈wireBlock w 1540 252,s.basis q=false) :
    (run (hAdd w inverse) m s).phase=s.phase ∧
    (∀q,q∉wireBlock w 4 253 → (run (hAdd w inverse) m s).basis q=s.basis q) ∧
    regValue (wireBlock w 4 253) (run (hAdd w inverse) m s).basis=
      ((if s.basis (w 1028) then (if inverse then 2^256-hConstant else hConstant)/8 else 0)+
        regValue (wireBlock w 4 253) s.basis+(s.basis (w 1797)).toNat)%2^253 := by
  have a := mappedAdd_correct (hBits w inverse) (wireBlock w 4 253)
    (wireBlock w 1540 252) (w 1797) hn hs
    (by simp [hBits_length,wireBlock_length]) (by simp [wireBlock_length]) s m hc
  simpa only [hAdd,hBits_value,wireBlock_length] using a

def kTail (w : Nat → Wire) (inverse : Bool) : Program :=
  mappedAdd (kBits w inverse) (wireBlock w 771 257) (wireBlock w 1540 256) (w 770)

/-- The head is an immutable carry-in for the actual emitted K tail. -/
theorem kTail_spec (w : Nat → Wire) (inverse : Bool) (s : State) (m : List Bool)
    (hn : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hs : ∀q∈mappedWires (kBits w inverse),
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false) :
    (run (kTail w inverse) m s).phase=s.phase ∧
    (∀q,q∉wireBlock w 771 257 → (run (kTail w inverse) m s).basis q=s.basis q) ∧
    regValue (wireBlock w 771 257) (run (kTail w inverse) m s).basis=
      (kConstant inverse (s.basis (w 1028))/2+
        regValue (wireBlock w 771 257) s.basis+(s.basis (w 770)).toNat)%2^257 := by
  have a := mappedAdd_correct (kBits w inverse) (wireBlock w 771 257)
    (wireBlock w 1540 256) (w 770) hn hs
    (by simp [kBits_length,wireBlock_length]) (by simp [wireBlock_length]) s m hc
  simpa only [kTail,kBits_value,wireBlock_length] using a

theorem kAdd_run (w : Nat → Wire) (inverse : Bool) (s : State) (m : List Bool) :
    run (kAdd w inverse) m s=
      let u := run (kTail w inverse) (m.take (measurementCount (kTail w inverse))) s
      ⟨u.phase,writeBit u.basis (w 770) (!(u.basis (w 770)))⟩ := by
  rw [kAdd,run_append]
  simp only [run,kTail]

theorem kAdd_phase (w : Nat → Wire) (inverse : Bool) (s : State) (m : List Bool)
    (hn : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hs : ∀q∈mappedWires (kBits w inverse),
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false) :
    (run (kAdd w inverse) m s).phase=s.phase := by
  rw [kAdd_run]
  exact (kTail_spec w inverse s _ hn hs hc).1

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.hAdd_spec
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kTail_spec
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kAdd_run
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kAdd_phase
