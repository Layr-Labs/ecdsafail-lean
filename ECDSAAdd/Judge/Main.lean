import ECDSAAdd.Challenge.Contract
namespace ECDSAAdd.Judge
/-- Acceptance has no numeric policy limit until organizers choose one.
Metrics are certified uniform bounds, not necessarily exact counts. -/
def acceptance (entry : Challenge.Entry) (bounds : Challenge.Bounds) : Prop :=
  Challenge.Certificate entry bounds
end ECDSAAdd.Judge
