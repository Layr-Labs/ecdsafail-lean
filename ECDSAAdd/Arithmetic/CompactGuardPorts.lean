import ECDSAAdd.Arithmetic.CompactGuardFront
import ECDSAAdd.Arithmetic.FusedShared
import ECDSAAdd.Arithmetic.FusedInversePacked

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

/-- One overflow guard, with the second target/constant guards retained as
separate late flag ports. The public payload still has all 256 field bits. -/
def compactSource (L : FusedHalfPorts) := (L.e::L.yTail)++[L.yg0]
def compactTarget (L : FusedHalfPorts) := L.targetLow++[L.qOut]
def compactConstant (L : FusedHalfPorts) := L.C++[L.t]
def compactCarry (L : FusedHalfPorts) := L.carry.take (L.A.length+1)

theorem compact_widths (L : FusedHalfPorts) (hw : L.Widths) :
    L.compactSource.length=L.A.length+1 ∧ L.compactTarget.length=L.A.length+1 ∧
    L.compactConstant.length=L.A.length+1 ∧ L.compactCarry.length=L.A.length+1 := by
  simp only [compactSource,compactTarget,compactConstant,compactCarry,targetLow,
    List.length_append,List.length_cons,hw.source,hw.target,
    hw.constant,List.length_take,hw.carry]
  simp

def compactForwardProgram (L : FusedHalfPorts) : Program :=
  compactSignedHalfFront L.b L.cin L.low L.a L.h L.j L.l L.m
    L.compactSource L.compactTarget L.compactConstant L.compactCarry p ++
    fusedFlagsMove L.a L.h L.qOut L.hOut ++
    fusedSignedHalfRetainedBack L.b L.cin L.qOut L.hOut L.t L.d L.e
      L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length)

def compactInverseProgram (L : FusedHalfPorts) : Program :=
  fusedInverseFlagSeed L.b L.cin L.qOut L.hOut L.t L.d L.e
    L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length) ++
    fusedInverseFlagsMove L.a L.h L.qOut L.hOut ++
    fusedSignedHalfUnfront L.b L.cin L.low L.a L.h L.j L.l L.m
      L.compactSource L.compactTarget L.compactConstant L.compactCarry p

theorem compact_forward_counts (L : FusedHalfPorts) (hw : L.Widths) :
    toffoliCount L.compactForwardProgram=6*L.A.length+2 ∧
    measurementCount L.compactForwardProgram=6*L.A.length+2 := by
  have hc := L.compact_widths hw
  have hl := L.widths hw
  have hf := compactSignedHalfFront_counts L.b L.cin L.low L.a L.h L.j L.l L.m
    L.compactSource L.compactTarget L.compactConstant L.compactCarry p
    (hc.1.trans hc.2.1.symm) (hc.2.2.1.trans hc.2.1.symm)
    (hc.2.2.2.trans hc.2.1.symm) (by rw [hc.2.1]; omega)
  have hm := fusedFlagsMove_counts L.a L.h L.qOut L.hOut
  have hb := fusedSignedHalfRetainedBack_counts L.b L.cin L.qOut L.hOut L.t L.d L.e
    L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length)
    (hl.2.2.2.1.trans hl.2.2.2.2.symm) hl.2.2.2.2.symm
    (hw.constant.trans hl.2.2.2.2.symm) (by simp [hw.carry,hl.2.2.2.2])
    (by rw [hl.2.2.2.2]; exact hw.min)
  simp only [compactForwardProgram,toffoliCount_append,measurementCount_append,
    hf.1,hf.2,hm.1,hm.2,hb.1,hb.2,hc.2.1,hl.2.2.2.2,Nat.add_zero]
  have hn := hw.min
  constructor <;> omega

theorem compact_inverse_counts (L : FusedHalfPorts) (hw : L.Widths) :
    toffoliCount L.compactInverseProgram=6*L.A.length+2 ∧
    measurementCount L.compactInverseProgram=6*L.A.length+2 := by
  have hc := L.compact_widths hw
  have hl := L.widths hw
  have hs := fusedInverseFlagSeed_counts L.b L.cin L.qOut L.hOut L.t L.d L.e
    L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length)
    (hl.2.2.2.1.trans hl.2.2.2.2.symm) hl.2.2.2.2.symm
    (hw.constant.trans hl.2.2.2.2.symm) (by simp [hw.carry,hl.2.2.2.2])
    (by rw [hl.2.2.2.2]; exact hw.min)
  have hm := fusedInverseFlagsMove_counts L.a L.h L.qOut L.hOut
  have hf := fusedSignedHalfUnfront_counts L.b L.cin L.low L.a L.h L.j L.l L.m
    L.compactSource L.compactTarget L.compactConstant L.compactCarry p
    (hc.1.trans hc.2.1.symm) (hc.2.2.1.trans hc.2.1.symm)
    (hc.2.2.2.trans hc.2.1.symm) (by rw [hc.2.1]; omega)
  simp only [compactInverseProgram,toffoliCount_append,measurementCount_append,
    hs.1,hs.2,hm.1,hm.2,hf.1,hf.2,hc.2.1,hl.2.2.2.2,Nat.add_zero]
  have hn := hw.min
  constructor <;> omega

end FusedHalfPorts

theorem compactShared_forward_counts (w : Nat → Wire) (g : Wire) :
    toffoliCount (fusedSharedPorts w g).compactForwardProgram=1538 ∧
    measurementCount (fusedSharedPorts w g).compactForwardProgram=1538 := by
  have h := (fusedSharedPorts w g).compact_forward_counts (fusedSharedPorts_widths w g)
  have ha : (fusedSharedPorts w g).A.length=256 := wireBlock_length w 512 256
  simpa only [ha,Nat.reduceMul,Nat.reduceAdd] using h

theorem compactShared_inverse_counts (w : Nat → Wire) (g : Wire) :
    toffoliCount (fusedSharedPorts w g).compactInverseProgram=1538 ∧
    measurementCount (fusedSharedPorts w g).compactInverseProgram=1538 := by
  have h := (fusedSharedPorts w g).compact_inverse_counts (fusedSharedPorts_widths w g)
  have ha : (fusedSharedPorts w g).A.length=256 := wireBlock_length w 512 256
  simpa only [ha,Nat.reduceMul,Nat.reduceAdd] using h

end ECDSAAdd.Arithmetic
