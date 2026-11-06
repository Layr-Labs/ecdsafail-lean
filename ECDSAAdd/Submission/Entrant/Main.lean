import ECDSAAdd.Submission.Entrant.ParityFinalBothInverse23Out

namespace ECDSAAdd.Entrant

def program := ParityFinalBothInverse23Out.programOpt
def entry := ParityFinalBothInverse23Out.entryOpt
def bounds := ParityFinalBothInverse23Out.boundsOpt
theorem certificate : Challenge.Certificate entry bounds := ParityFinalBothInverse23Out.certificateOpt

end ECDSAAdd.Entrant
