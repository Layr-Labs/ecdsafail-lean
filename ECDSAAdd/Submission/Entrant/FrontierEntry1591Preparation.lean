import ECDSAAdd.Submission.Entrant.FrontierEntry1591Forward
import ECDSAAdd.Submission.Entrant.FrontierEntry1591Native
import ECDSAAdd.Submission.Entrant.NewFieldFrameOB5

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 History5
attribute [local irreducible] run wires NewStackOB5.stackForwardT
  NewStackOB5.regularForward NativeFirstDirect.forward FrontierEntry1591Native.forward

theorem preparation_placed (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (m1 m2 m3 : List Bool) (input : SkywalkArithmeticInput base x Y.val s.basis) :
    let a1 := run (FrontierEntry1591Native.forward base) m1 s
    let a2 := run NewStackOB5.stackForwardT m2 a1
    let a3 := run (skywalkArithmeticClear base) m3 a2
    ∃origin : State,PreparationFacts x Y s origin ∧ History5.RawLegal base 102 origin.basis ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3 := by
  let a1 := run (FrontierEntry1591Native.forward base) m1 s
  let a2 := run NewStackOB5.stackForwardT m2 a1
  let a3 := run (skywalkArithmeticClear base) m3 a2
  let t2 := run (NewStackOB5.regularForward base 1 511) m2 a1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  have h1 : run (NativeFirstDirect.forward base) m1 s=a1 :=
    (FrontierEntry1591Native.forward_run_eq base hn x Y.val hx s m1 input).symm
  have first := FrontierEntry1591Native.caller_first_stage base hn x Y.val hx0 hx s m1 input
  have firstW := FrontierEntry1591Native.caller_first_stageW base hn x Y.val hx0 hx s m1 input
  have e2 : a2=pullState (OB5.sig 511) t2 :=
    (NewStackOB5.stackForwardT_run hn hlo x hx0 hx a1 m2 firstW).trans
      (NewStackOB5.forward_run x hx0 hx a1 m2 firstW)
  have e3 : a3=pullState (OB5.sig 511) t3 := by
    change run (skywalkArithmeticClear base) m3 a2=_
    rw [e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,_,frame⟩ := NewStackOB5.preparation_facts hn hlo ho x Y hx0 hx s
    m1 m2 m3 input a1 t2 t3 h1 rfl rfl first
  refine ⟨origin,facts,legal,?_⟩
  change NewHistory5.EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) a3)
  rw [e3,OB5.pull_invol 511 (by decide)]
  exact frame

end ECDSAAdd.Entrant.FrontierEntry1591Kernel
