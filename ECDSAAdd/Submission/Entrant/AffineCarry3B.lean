import ECDSAAdd.Submission.Entrant.AffineCarry3A

set_option maxHeartbeats 16000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option linter.unusedVariables false

namespace Verifier.Leaf3
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge
open ECDSAAdd.Entrant.AdderSpineBridgeResearch ECDSAAdd.Entrant.KAddCallerBridgeResearch

section Exit3Opaque
attribute [local irreducible] ECDSAAdd.wires
set_option maxHeartbeats 16000000 in
theorem exit3_run_eq_split (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean5 : s.basis (w 1795)=false) (clean6 : s.basis (w 1796)=false)
    (topB  : (run (P3 w++oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)
                (w 1795) (w 1796)++R3 w) [] s).basis (w 1026)=false)
    (topB' : (run (P3 w++oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)
                (w 1795) (w 1796)++R3 w) [] s).basis (w 1027)=false) :
    run (P3 w++oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)
          (w 1795) (w 1796)++R3 w) m s
      = run (P3 w++newLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)++R3 w) m s := by
  exact whole_zero3 (P3 w) (R3 w) (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)
    (w 1795) (w 1796) (tail3_nd w hinj) s m clean5 clean6
    (P3_avoid w hinj 1795 (Or.inl rfl)) (P3_avoid w hinj 1796 (Or.inr (Or.inl rfl)))
    (R3_avoid w hinj 1026 (Or.inr (Or.inr (Or.inl rfl))))
    (R3_avoid w hinj 1027 (Or.inr (Or.inr (Or.inr rfl)))) topB topB'
end Exit3Opaque

/-- Same bridge, stated on the literal adder. The module boundary keeps `P3`/`R3` opaque. -/
theorem exit3_run_eq (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean5 : s.basis (w 1795)=false) (clean6 : s.basis (w 1796)=false)
    (topB  : (run (literalKAdd w) [] s).basis (w 1026)=false)
    (topB' : (run (literalKAdd w) [] s).basis (w 1027)=false) :
    run (literalKAdd w) m s=run (zero3KAdd w) m s := by
  rw [literal_split3] at topB topB'
  rw [literal_split3, zero3KAdd]
  exact exit3_run_eq_split w hinj s m clean5 clean6 topB topB'

#print axioms exit3_run_eq
end Verifier.Leaf3
