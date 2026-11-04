import ECDSAAdd.Submission.Entrant.AffineCarry4A

set_option maxHeartbeats 16000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 400

namespace Verifier.Leaf4
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge
open ECDSAAdd.Entrant.AdderSpineBridgeResearch ECDSAAdd.Entrant.KAddCallerBridgeResearch

section Exit4Opaque
attribute [local irreducible] ECDSAAdd.wires
set_option maxHeartbeats 16000000 in
theorem exit4_run_eq_split (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean4 : s.basis (w 1794)=false) (clean5 : s.basis (w 1795)=false)
    (clean6 : s.basis (w 1796)=false)
    (topB   : (run (P4 w++oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
                (w 257) (w 1027) (w 1794) (w 1795) (w 1796)++R4 w) [] s).basis (w 1025)=false)
    (topB'  : (run (P4 w++oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
                (w 257) (w 1027) (w 1794) (w 1795) (w 1796)++R4 w) [] s).basis (w 1026)=false)
    (topB'' : (run (P4 w++oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
                (w 257) (w 1027) (w 1794) (w 1795) (w 1796)++R4 w) [] s).basis (w 1027)=false) :
    run (P4 w++oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
          (w 257) (w 1027) (w 1794) (w 1795) (w 1796)++R4 w) m s
      = run (P4 w++newLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
          (w 257) (w 1027)++R4 w) m s := by
  exact whole_zero4 (P4 w) (R4 w) (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
    (w 257) (w 1027) (w 1794) (w 1795) (w 1796) (tail4_nd w hinj) s m clean4 clean5 clean6
    (P4_avoid w hinj 1794 (Or.inl rfl))
    (P4_avoid w hinj 1795 (Or.inr (Or.inl rfl)))
    (P4_avoid w hinj 1796 (Or.inr (Or.inr (Or.inl rfl))))
    (R4_avoid w hinj 1025 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (R4_avoid w hinj 1026 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (R4_avoid w hinj 1027 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    topB topB' topB''
end Exit4Opaque

/-- Same bridge, stated on the literal adder. The module boundary keeps `P4`/`R4` opaque. -/
theorem exit4_run_eq (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean4 : s.basis (w 1794)=false) (clean5 : s.basis (w 1795)=false)
    (clean6 : s.basis (w 1796)=false)
    (topB   : (run (literalKAdd w) [] s).basis (w 1025)=false)
    (topB'  : (run (literalKAdd w) [] s).basis (w 1026)=false)
    (topB'' : (run (literalKAdd w) [] s).basis (w 1027)=false) :
    run (literalKAdd w) m s=run (zero4KAdd w) m s := by
  rw [literal_split4] at topB topB' topB''
  rw [literal_split4, zero4KAdd]
  exact exit4_run_eq_split w hinj s m clean4 clean5 clean6 topB topB' topB''

#print axioms exit4_run_eq
end Verifier.Leaf4
