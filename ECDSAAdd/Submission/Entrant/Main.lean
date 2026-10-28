import ECDSAAdd.Baselines.ValueWalkCertificate

/-! Reference entrant: replace declarations in this editable directory to compete.
All semantics and metric definitions remain in the protected challenge. -/
namespace ECDSAAdd.Entrant

def entry : Challenge.Entry := Baselines.normalizedValueWalk
def bounds : Challenge.Bounds := Baselines.valueWalkBounds

theorem certificate : Challenge.Certificate entry bounds := Baselines.valueWalkCertificate

end ECDSAAdd.Entrant
