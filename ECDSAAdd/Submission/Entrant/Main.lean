import ECDSAAdd.Submission.Entrant.CodexAffineProbe

namespace ECDSAAdd.Entrant
def program := CodexAffineProbe.program
def entry := CodexAffineProbe.entry
def bounds := CodexAffineProbe.bounds
theorem certificate : Challenge.Certificate entry bounds := CodexAffineProbe.certificate
end ECDSAAdd.Entrant
