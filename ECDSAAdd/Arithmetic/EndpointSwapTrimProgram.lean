import ECDSAAdd.Arithmetic.OffsetBorrowedFieldProgram
import ECDSAAdd.Arithmetic.OffsetBorrowedInverseParity
import ECDSAAdd.Arithmetic.TranscriptSelectFlag

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.EndpointSwapTrim

/-- Final forward cell: keep the actual G-selected kernel; retire no data
or transcript and omit only the S window proved identity at the endpoint. -/
def forward (w : Nat → Wire) (b g flag : Wire) (ig : Bool) : Program :=
  transcriptSelectWindow b g flag ig
    ([.X flag]++OffsetBorrowedField.program w flag++[.X flag])

/-- First inverse cell: its input words are equal, so the original preceding
S window is unnecessary. The inverse kernel has independent measurements. -/
def inverse (w : Nat → Wire) (b g flag : Wire) (ig : Bool) : Program :=
  transcriptSelectWindow b g flag ig
    ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])

theorem counts (w : Nat → Wire) (b g flag : Wire) (ig : Bool) :
    toffoliCount (forward w b g flag ig)=1023 ∧
    measurementCount (forward w b g flag ig)=1024 ∧
    toffoliCount (inverse w b g flag ig)=1024 ∧
    measurementCount (inverse w b g flag ig)=1024 := by
  have f := OffsetBorrowedField.counts w flag
  have i := OffsetBorrowedInverse.counts w flag
  have fw := transcriptSelectWindow_counts b g flag ig
    ([.X flag]++OffsetBorrowedField.program w flag++[.X flag])
  have iv := transcriptSelectWindow_counts b g flag ig
    ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])
  simp only [forward,inverse,fw.1,fw.2,iv.1,iv.2,
    toffoliCount_append,measurementCount_append,f.1,f.2,i.1,i.2]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.EndpointSwapTrim
#print axioms ECDSAAdd.Arithmetic.EndpointSwapTrim.counts
