import ECDSAAdd.Submission.Entrant.FrontierEntryFieldTransfer
import ECDSAAdd.Submission.Entrant.FrontierEntryKernelResources
import ECDSAAdd.Submission.Entrant.FrontierEntryKernelCosts
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntryKernel
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5
attribute [local irreducible] run wires kernel5S baseKernel hostField5S

theorem kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=base_kernel5S_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have shape6 : Q6FusionPhase.kernel hostField5S=baseKernel := by
    simpa only [baseKernel] using Q6FusionGeometry.old_shape hostField5S
  have frame6 : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel hostField5S) m t).basis q=s.basis q := by
    simpa only [shape6] using old.2.2
  have eq6:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m hostField5S hin same
    hostField5S_1541_free frame6
  have shape7 : Q7FusionPhase.kernel hostField5S=Q6FusionPhase.relocated hostField5S :=
    Q7FusionPhase.old_shape hostField5S
  have frame7 : ∀q,q∉wireBlock base 2056 256 →
      (run (Q7FusionPhase.kernel hostField5S) m t).basis q=s.basis q := by
    simpa only [shape7,eq6,shape6] using old.2.2
  have eq7:=Q7FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m hostField5S hin same
    hostField5S_1542_free frame7
  simpa only [kernel5S,eq7,shape7,eq6,shape6] using old
end ECDSAAdd.Entrant.FrontierEntryKernel
