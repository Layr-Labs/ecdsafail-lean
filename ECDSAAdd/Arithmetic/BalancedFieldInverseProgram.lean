import ECDSAAdd.Arithmetic.BalancedFieldCircuitProgram
import ECDSAAdd.Arithmetic.MappedSubtract
import ECDSAAdd.Arithmetic.BalancedCleanupCircuitProof

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit

/-- Reuse the forward, independently measured XOR oracle to reconstruct
parity. No measurement instruction is reversed. -/
def recoverParity (L : Layout) : Program := BalancedCleanup.program L.toLayout

/-- Dual of the former minus-selector measurement: its quadratic predicate
is A XOR (A AND sign(R)). The remaining operations undo Clifford views. -/
def recoverSelectors (L : Layout) : Program :=
  [.CX L.parity L.minus,.CCX L.parity L.rmsb L.minus,
    .CX L.minus L.plus,.CX L.parity L.plus,
    .CX L.rmsb L.lower,.CX L.parity L.lower]

/-- Arithmetic inverse of the mapped addition, including the original
quantum carry-in. This is a fresh measured subtraction, not reversed MX. -/
def undoFold (L : Layout) : Program :=
  [.CX L.minus L.cout]++mappedSub (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity

/-- The prepared AND has known pre-target zero, so its inverse is one
measurement with the exact CZ correction, rather than a reversed CCX. -/
def undoPreparation (L : Layout) : Program :=
  [.CX L.parity L.r0,.CX L.parity L.one,
    .CX L.minus L.plus,.CX L.parity L.plus,
    .measureX L.minus [] [.CZ L.parity L.lower],.CX L.one L.lower]

def rawSubtract (L : Layout) : Program :=
  signComplement L.sign (rawSource L)++
  subInPlace (rawSource L) (rawTarget L) L.carry L.sign++
  signComplement L.sign (rawSource L)

/-- Actual independently emitted inverse candidate. Only the seed's CX
stream is reversed; every arithmetic and cleanup measurement runs forward. -/
def program (L : Layout) : Program :=
  [.CX L.ymsb L.sourceGuard]++recoverParity L++recoverSelectors L++
  rotateLeft (rawTarget L)++undoFold L++undoPreparation L++rawSubtract L++(seedViews L).reverse

/-- Honest counts of this DSL emission. The prototype's1276 estimate is
not imposed on the current independently measured primitive recipes. -/
theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=1277 ∧ measurementCount (program L)=1277 := by
  have w := BalancedCircuit.widths L hw
  have ra := subInPlace_counts (rawSource L) (rawTarget L) L.carry L.sign
    (by omega) (by omega)
  have fa := mappedSub_counts (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
    (by omega) (by omega)
  have cm := signComplement_counts L.sign (rawSource L)
  have ro := rotate_counts (rawTarget L)
  have cl := BalancedCleanup.counts L.toLayout hw
  simp only [program,recoverParity,recoverSelectors,undoFold,undoPreparation,rawSubtract,
    toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    ra.1,ra.2,fa.1,fa.2,cm.1,cm.2,ro.2.2.1,ro.2.2.2,cl.1,cl.2]
  simp only [w.2.1,w.2.2.1,seedViews]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.BalancedInverse

#print axioms ECDSAAdd.Arithmetic.BalancedInverse.counts
