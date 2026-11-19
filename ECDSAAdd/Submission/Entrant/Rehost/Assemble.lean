import ECDSAAdd.Submission.Entrant.Rehost.Final
import ECDSAAdd.Submission.Entrant.Rehost.CleanS2
import ECDSAAdd.Submission.Entrant.Rehost.CleanExitS2
import ECDSAAdd.Submission.Entrant.Rehost.StaticsS2
import ECDSAAdd.Submission.Entrant.Rehost.KernelS2
/-!
# S2 rehost: every field of `Facts`, and the Q = 1545 certificate

The only input not proved here is the square's: p6 never touches 4839 (proof-s2-square,
`StairSquareFinal.squareEntryHL_avoids4839`, on the S2 square). Every other field is a theorem of the
`Rehost` modules, checked against S1.
-/
set_option autoImplicit false

namespace ECDSAAdd.Entrant.Rehost
open ECDSAAdd Arithmetic Challenge Secp256k1 MappedCompressed
open StairConcreteAssembly

/-- The square's deliverable (statement of `StairSquareFinal.squareEntryHL_avoids4839`) is `Facts.e6`. -/
theorem e6_of_square (h : ∀ k : Fp, (4839 : Wire) ∉ wires (renameProgram StairSiteAvoidance.UG
    (StairSquareFinal.squareEntryHL StairSqLoopA.holes Baselines.layout k))) :
    ∀ cx, wE ∉ wires (p6 cx) :=
  fun cx => h (ReflectionE1.correction cx)

/-- All facts, given the square's. -/
theorem facts_of_square (e6 : ∀ cx, wE ∉ wires (p6 cx)) : Facts where
  z0 := notIn0_wZ
  z1 := notIn1_wZ
  z2 := notIn2_wZ
  z3 := notIn3_wZ
  z4 := notIn4_wZ
  z8 := notIn8_wZ
  a9 := notIn9_wA
  a10 := notIn10_wA
  a11 := notIn11_wA
  a12 := notIn12_wA
  a13 := notIn13_wA
  e5 := notIn5_wE
  e6 := e6
  e7 := notIn7_wE
  clean4 := CleanS2.clean4
  clean8 := CleanS2.clean8
  zClean8 := fun hc => clean8_wZ_of hc (notIn8_wZ _)

/-- S2's certificate: the tree's own 40-hole certificate (any bounds ⟨T, M, Q, S⟩) becomes
⟨T, M, 1545, S⟩ for `rehostEntry`. In Main:
`rehost_certificate_S2 (e6_of_square StairSquareFinal.squareEntryHL_avoids4839) certificate40`. -/
theorem rehost_certificate_S2 (e6 : ∀ cx, wE ∉ wires (p6 cx)) {T M Q S : Nat}
    (base : Challenge.Certificate (StairCertificate.stairEntry concreteAssembly) ⟨T, M, Q, S⟩) :
    Challenge.Certificate rehostEntry ⟨T, M, 1545, S⟩ :=
  rehost_certificate (facts_of_square e6) base
    (StairOpenWiring.stairOpen_of_remaining StairOpenWiring.remaining).site_avoidance

end ECDSAAdd.Entrant.Rehost
