import ECDSAAdd.Baselines.SkywalkCertificate
import ECDSAAdd.Submission.Entrant.CodexAffineMath
import ECDSAAdd.Submission.Entrant.CodexAffineGadget

namespace ECDSAAdd.Entrant
def entry := Baselines.normalizedSkywalk
def bounds := Baselines.skywalkBounds
theorem certificate : Challenge.Certificate entry bounds := Baselines.skywalkCertificate
end ECDSAAdd.Entrant
