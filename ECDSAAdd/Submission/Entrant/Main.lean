import ECDSAAdd.Baselines.SkywalkCertificate

/-! Reference entrant: replace declarations in this editable directory to compete.
All semantics and metric definitions remain in the protected challenge.
The shipped default entrant is the certified Skywalk baseline
(`Baselines.normalizedSkywalk`, `Baselines.skywalkBounds`, `Baselines.skywalkCertificate`).
An alternative certified baseline is ValueWalk (`Baselines.normalizedValueWalk`,
`Baselines.valueWalkBounds`, `Baselines.valueWalkCertificate` in
`ECDSAAdd.Baselines.ValueWalkCertificate`). -/
namespace ECDSAAdd.Entrant

def entry : Challenge.Entry := Baselines.normalizedSkywalk
def bounds : Challenge.Bounds := Baselines.skywalkBounds

theorem certificate : Challenge.Certificate entry bounds := Baselines.skywalkCertificate

end ECDSAAdd.Entrant
