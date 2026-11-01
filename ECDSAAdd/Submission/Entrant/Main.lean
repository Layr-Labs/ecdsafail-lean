import ECDSAAdd.Submission.Entrant.FusedBoundaryFinal

namespace ECDSAAdd.Entrant
def program := FusedBoundaryFinal.program
def entry := FusedBoundaryFinal.entry
def bounds := FusedBoundaryFinal.bounds
theorem certificate : Challenge.Certificate entry bounds := FusedBoundaryFinal.certificate
end ECDSAAdd.Entrant
