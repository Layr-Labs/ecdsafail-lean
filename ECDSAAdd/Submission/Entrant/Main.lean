import ECDSAAdd.Submission.Entrant.SharedErase

namespace ECDSAAdd.Entrant
def program := SharedErase.program
def entry := SharedErase.entry
def bounds := SharedErase.bounds
theorem certificate : Challenge.Certificate entry bounds := SharedErase.certificate
end ECDSAAdd.Entrant
