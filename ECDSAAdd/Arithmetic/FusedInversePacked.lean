import ECDSAAdd.Arithmetic.FusedInverseFront
import ECDSAAdd.Arithmetic.FusedShared

namespace ECDSAAdd.Arithmetic

/-- Independently emitted Clifford transfer from target guards back to early
flags. Only this measurement-free transfer changes operation order. -/
def fusedInverseFlagsMove (a h qOut hOut : Wire) : Program :=
  swapBits h hOut ++ swapBits a qOut ++ [.CX h a]

theorem fusedInverseFlagsMove_counts (a h qOut hOut : Wire) :
    toffoliCount (fusedInverseFlagsMove a h qOut hOut)=0 ∧
    measurementCount (fusedInverseFlagsMove a h qOut hOut)=0 := by
  constructor <;> rfl

theorem fusedInverseFlagsMove_correct (a h qOut hOut : Wire)
    (hn : [a,h,qOut,hOut].Nodup) (Q H : Bool) (s : State) (record : List Bool)
    (ha0 : s.basis a=false) (hh0 : s.basis h=false)
    (hq : s.basis qOut=Q) (ho : s.basis hOut=H) :
    (run (fusedInverseFlagsMove a h qOut hOut) record s).phase=s.phase ∧
    (∀ w,w≠a → w≠h → w≠qOut → w≠hOut →
      (run (fusedInverseFlagsMove a h qOut hOut) record s).basis w=s.basis w) ∧
    (run (fusedInverseFlagsMove a h qOut hOut) record s).basis a=(Q^^H) ∧
    (run (fusedInverseFlagsMove a h qOut hOut) record s).basis h=H ∧
    (run (fusedInverseFlagsMove a h qOut hOut) record s).basis qOut=false ∧
    (run (fusedInverseFlagsMove a h qOut hOut) record s).basis hOut=false := by
  have dif := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at dif
  have ah : a≠h := by tauto
  have aq : a≠qOut := by tauto
  have ao : a≠hOut := by tauto
  have hq' : h≠qOut := by tauto
  have ho' : h≠hOut := by tauto
  have qo : qOut≠hOut := by tauto
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · intro w hwa hwh hwq hwo
    simp [fusedInverseFlagsMove,swapBits,run,writeBit,hwa,hwh,hwq,hwo]
  all_goals cases Q <;> cases H <;>
    simp [fusedInverseFlagsMove,swapBits,run,writeBit,ha0,hh0,hq,ho,
      ah,aq,ao,hq',ho',qo,Ne.symm ah,Ne.symm aq,Ne.symm ao,Ne.symm hq',Ne.symm ho',Ne.symm qo]

namespace FusedHalfPorts

/-- Candidate packed inverse stream. Count and component proofs are separate
from the full packed-port semantics and shared-pool integration obligations. -/
def inverseProgram (L : FusedHalfPorts) : Program :=
  fusedInverseFlagSeed L.b L.cin L.qOut L.hOut L.t L.d L.e
    L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length) ++
    fusedInverseFlagsMove L.a L.h L.qOut L.hOut ++
    fusedSignedHalfUnfront L.b L.cin L.low L.a L.h L.j L.l L.m
      L.source L.target L.constant L.carry p

theorem inverse_counts (L : FusedHalfPorts) (hw : L.Widths) :
    toffoliCount L.inverseProgram=6*L.A.length+5 ∧
    measurementCount L.inverseProgram=6*L.A.length+5 := by
  have hl := L.widths hw
  have hs := fusedInverseFlagSeed_counts L.b L.cin L.qOut L.hOut L.t L.d L.e
    L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length)
    (hl.2.2.2.1.trans hl.2.2.2.2.symm) hl.2.2.2.2.symm
    (hw.constant.trans hl.2.2.2.2.symm) (by simp [hw.carry,hl.2.2.2.2])
    (by rw [hl.2.2.2.2]; exact hw.min)
  have hm := fusedInverseFlagsMove_counts L.a L.h L.qOut L.hOut
  have hf := fusedSignedHalfUnfront_counts L.b L.cin L.low L.a L.h L.j L.l L.m
    L.source L.target L.constant L.carry p (hl.1.trans hl.2.1.symm)
    (hl.2.2.1.trans hl.2.1.symm) (hw.carry.trans hl.2.1.symm)
    (by rw [hl.2.1]; omega)
  simp only [inverseProgram,toffoliCount_append,measurementCount_append,
    hs.1,hs.2,hm.1,hm.2,hf.1,hf.2,hl.2.1,hl.2.2.2.2,Nat.add_zero]
  have hn := hw.min
  constructor <;> omega

end FusedHalfPorts

theorem fusedSharedInverseKernel_counts (w : Nat → Wire) (g : Wire) :
    toffoliCount (fusedSharedPorts w g).inverseProgram=1541 ∧
    measurementCount (fusedSharedPorts w g).inverseProgram=1541 := by
  have hc := (fusedSharedPorts w g).inverse_counts (fusedSharedPorts_widths w g)
  have ha : (fusedSharedPorts w g).A.length=256 := wireBlock_length w 512 256
  simpa only [ha,Nat.reduceMul,Nat.reduceAdd] using hc

end ECDSAAdd.Arithmetic
