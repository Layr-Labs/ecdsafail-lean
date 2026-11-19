import ECDSAAdd.Submission.Entrant.Rehost.Assemble
/-!
# The public entry (S2: Q 1545)

`StairMain` holds the staircase entry with 40 retired pool sites (`entry40`, `bounds40`, `certificate40`,
Q 1546). The `Rehost` modules re-host pool 724 (physical wire 4839) of that program at top level and turn
its certificate into one with Q 1545 for `Rehost.rehostEntry`; the square's own fact that it never touches
4839 is `StairSquareFinal.squareEntryHL_avoids4839`. Counts (T, M, slots) are those of `entry40`.
-/

namespace ECDSAAdd.Entrant

/-- The staircase entry with pool 724 re-hosted at top level (41 retired sites). -/
def entry : Challenge.Entry := Rehost.rehostEntry

/-- Literal bounds ⟨T, M, Q, slots⟩. -/
def bounds : Challenge.Bounds := ⟨2168165, 1521500, 1545, 51155937⟩

theorem certificate : Challenge.Certificate entry bounds :=
  Rehost.rehost_certificate_S2 (Rehost.e6_of_square StairSquareFinal.squareEntryHL_avoids4839) certificate40

end ECDSAAdd.Entrant

#print axioms ECDSAAdd.Entrant.entry
#print axioms ECDSAAdd.Entrant.bounds
#print axioms ECDSAAdd.Entrant.certificate
