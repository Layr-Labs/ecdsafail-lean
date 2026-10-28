import ECDSAAdd.Arithmetic.BalancedCleanupCircuitProgram
import ECDSAAdd.Arithmetic.MappedAdder
import ECDSAAdd.Arithmetic.InPlaceAdder

set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open Secp256k1

/-- Two centered field words, one shared carry ladder, and eight scalar
positions. The sign is an input control; all other scalar work starts clean. -/
structure Layout extends BalancedCleanup.Layout where
  sourceGuard : Wire
  cout : Wire
  minus : Wire
  plus : Wire

def Layout.wires (L : Layout) := [L.sourceGuard,L.cout,L.minus,L.plus]++L.toLayout.wires
def Layout.Widths (L : Layout) := L.toLayout.Widths

def rawSource (L : Layout) := L.toLayout.y++[L.sourceGuard]
def rawTarget (L : Layout) := L.toLayout.r++[L.one]
def foldTarget (L : Layout) := L.rtail++[L.rmsb,L.one]
def sparseF : Nat := 2^32+977

/-- For odd f, the upper bits of f and -f are complementary. Each
position therefore reads one of two immutable selectors, without a bank. -/
def foldBits (L : Layout) : List MappedBit :=
  (List.range 256).map (fun i =>
    {wire:=some (if sparseF.testBit (i+1) then L.plus else L.minus),flip:=false})++
    [{wire:=none,flip:=false}]

def seedViews (L : Layout) : Program :=
  [.CX L.ymsb L.sourceGuard,.CX L.rmsb L.one,
    .CX (L.ylow.getD 0 0) L.parity,.CX L.r0 L.parity]

def rawAdd (L : Layout) : Program :=
  signComplement L.sign (rawSource L)++
  addInPlace (rawSource L) (rawTarget L) L.carry L.sign++
  signComplement L.sign (rawSource L)

def prepareFold (L : Layout) : Program :=
  [.CX L.one L.lower,.CCX L.parity L.lower L.minus,
    .CX L.parity L.plus,.CX L.minus L.plus,
    .CX L.parity L.one,.CX L.parity L.r0]

def fold (L : Layout) : Program :=
  mappedAdd (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity++[.CX L.minus L.cout]

def releaseSelectors (L : Layout) : Program :=
  [.CX L.parity L.lower,.CX L.rmsb L.lower,
    .CX L.parity L.plus,.CX L.minus L.plus,
    .measureX L.minus [] [.Z L.parity,.CZ L.parity L.rmsb]]

/-- The complete candidate emission. Resource theorems do not assert
functional correctness; full gate-level composition is still required. -/
def program (L : Layout) : Program :=
  seedViews L++rawAdd L++prepareFold L++fold L++rotateRight (rawTarget L)++
    releaseSelectors L++BalancedCleanup.program L.toLayout++[.CX L.ymsb L.sourceGuard]

theorem widths (L : Layout) (hw : L.Widths) :
    (rawSource L).length=257 ∧ (rawTarget L).length=257 ∧
    (foldTarget L++[L.cout]).length=257 ∧ (foldBits L).length=257 ∧ L.carry.length=256 := by
  have w := BalancedCleanup.widths L.toLayout hw
  simp [rawSource,rawTarget,foldTarget,foldBits,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,hw.1,hw.2.1,hw.2.2]

theorem declaredSites (L : Layout) (hw : L.Widths) : L.wires.length=776 := by
  simp [Layout.wires,BalancedCleanup.Layout.wires,hw.1,hw.2.1,hw.2.2]

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=1277 ∧ measurementCount (program L)=1277 := by
  have w := widths L hw
  have ra := addInPlace_counts (rawSource L) (rawTarget L) L.carry L.sign
    (by omega) (by omega)
  have fa := mappedAdd_counts (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
    (by omega) (by omega)
  have cm := signComplement_counts L.sign (rawSource L)
  have ro := rotate_counts (rawTarget L)
  have cl := BalancedCleanup.counts L.toLayout hw
  simp only [program,seedViews,rawAdd,prepareFold,fold,releaseSelectors,
    toffoliCount_append,measurementCount_append,ra.1,ra.2,fa.1,fa.2,cm.1,cm.2,ro.1,ro.2.1,cl.1,cl.2]
  simp only [w.2.1,w.2.2.1]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.BalancedCircuit

#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.counts
