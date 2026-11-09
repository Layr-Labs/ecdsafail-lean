import ECDSAAdd.Submission.Entrant.ParkAInputFast
import ECDSAAdd.Submission.Entrant.ParkAChain
import ECDSAAdd.Submission.Entrant.ParkCarry10
import ECDSAAdd.Submission.Entrant.BThreeData
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace ECDSAAdd.Entrant.BThreeStaged301
open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
open ControlLoan1589BFFold ZeroReadDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
open LowBitCarryDevelop
/-- Proof-local constructor replacement, with the original old compiler unchanged. -/
def coreFast (L : CuccaroStreamedSquareWideLayout) : Program :=
  kw L ++ (ParkAInputFast.qprogFast (rotWCore L) SquareReduction.p ++ kw L)

theorem coreFast_eq (L : CuccaroStreamedSquareWideLayout) : coreFast L = wCoreK L := by
  simp only [coreFast, ParkAInputFast.qprogFast_eq, wCoreK, wCoreTq]

def middleFast (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
 prepare4L c (bit1 L.core.high) (L.core.high.headD 0) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L)) ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L) ++
 ((wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0) ++ (coreFast L ++ wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0))) ++
 finish4L c (bit1 L.core.high) (L.core.high.headD 0) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L)) ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L))

/-- Exact ordered Program syntax for arbitrary layouts and controls; not just isSome equality. -/
theorem middleFast_eq (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
    middleFast L c = LowBitCarryDevelop.wMidFullCCC0 L c := by
  simp only [middleFast, coreFast_eq, LowBitCarryDevelop.wMidFullCCC0]


def L : CuccaroStreamedSquareWideLayout := Baselines.layout.dialogStreamedSquareWide
def c : Wire := Baselines.layout.core.generic
theorem input_bool : ParkAProgramBool.programEq BData301.p0 (middleFast L c)=true := by decide +kernel
theorem input_fast_eq : BData301.p0 = middleFast L c := ParkAProgramBool.programEq_sound _ _ input_bool
theorem input_eq : BData301.p0 = LowBitCarryDevelop.wMidFullCCC0 L c := input_fast_eq.trans (middleFast_eq L c)

theorem step0_bool : ParkAOptionBool.optionEq ((compileChunked? 4672 BData301.p0).map (fun c => c.out)) (some BData301.p1)=true := by decide +kernel
theorem step0_eq : (compileChunked? 4672 BData301.p0).map (fun c => c.out)=some BData301.p1 := ParkAOptionBool.optionEq_sound _ _ step0_bool

theorem step1_bool : ParkAOptionBool.optionEq ((compileChunked? 4673 BData301.p1).map (fun c => c.out)) (some BData301.p2)=true := by decide +kernel
theorem step1_eq : (compileChunked? 4673 BData301.p1).map (fun c => c.out)=some BData301.p2 := ParkAOptionBool.optionEq_sound _ _ step1_bool

theorem step2_bool : ParkAOptionBool.optionEq ((compileChunked? 4674 BData301.p2).map (fun c => c.out)) (some BData301.p3)=true := by decide +kernel
theorem step2_eq : (compileChunked? 4674 BData301.p2).map (fun c => c.out)=some BData301.p3 := ParkAOptionBool.optionEq_sound _ _ step2_bool

theorem chain : ParkAChain.Steps [4672,4673,4674] BData301.p0 BData301.p3 :=
 .cons 4672 _ _ _ _ step0_eq (.cons 4673 _ _ _ _ step1_eq (.cons 4674 _ _ _ _ step2_eq (.nil _)))
theorem compilerSome_transport (qs : List Wire) (p q : Program) (e : p = q)
 (h : (compileManyChunked? qs p).isSome=true) : (compileManyChunked? qs q).isSome=true := e ▸ h
theorem actual_compiled : (compileManyChunked? [4672,4673,4674] (LowBitCarryDevelop.wMidFullCCC0 L c)).isSome=true :=
 compilerSome_transport _ _ _ input_eq (ParkAChain.isSome _ _ _ chain)
/-- Only literal input membership is evaluated here; the whole B body is never constructed. -/
theorem data_uses_r : FourthASavedCarryDevelop.hasWire BData301.p0 4672=true := by decide +kernel
theorem data_uses_p : FourthASavedCarryDevelop.hasWire BData301.p0 4673=true := by decide +kernel
theorem data_uses_u : FourthASavedCarryDevelop.hasWire BData301.p0 4674=true := by decide +kernel
end ECDSAAdd.Entrant.BThreeStaged301
