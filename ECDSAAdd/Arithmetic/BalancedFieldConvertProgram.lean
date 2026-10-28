import ECDSAAdd.Arithmetic.BalancedFoldMath
import ECDSAAdd.Arithmetic.MappedSubtract

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
namespace ECDSAAdd.Arithmetic.BalancedConvert
open BalancedField BalancedCircuit

/-- A single field word and a shared carry ladder. No constant word bank. -/
structure Layout where
  low : List Wire
  msb : Wire
  carry : List Wire
  cin : Wire
  one : Wire
  flag : Wire

def Layout.word (L : Layout) := L.low++[L.msb]
def Layout.wires (L : Layout) := [L.cin,L.one,L.flag,L.msb]++L.low++L.carry
def Layout.Widths (L : Layout) := L.low.length=255 ∧ L.carry.length=255

def bias : Nat := (sparseF-1)/2
def inverseBias : Nat := 2^256-bias

def correction (L : Layout) : List MappedBit :=
  (List.range 256).map fun i =>
    {wire:=if sparseF.testBit i then some L.flag else none,flip:=false}

/-- The exact threshold predicate is copied from a biased word's top bit.
Both adders run forward, with independent measurement cleanup. -/
def predicate (L : Layout) : Program :=
  literalConstAdd L.word L.carry L.cin L.one bias++[.CX L.msb L.flag]++
    literalConstAdd L.word L.carry L.cin L.one inverseBias

/-- Convert canonical x to two's-complement centerFp(x). Functional
composition is a separate proof obligation; these are actual instructions. -/
def center (L : Layout) : Program :=
  predicate L++mappedAdd (correction L) L.word L.carry L.cin++[.CX L.msb L.flag]

/-- Independently emitted inverse: subtract the selected sparse correction
and XOR the exact canonical threshold predicate back into the flag. -/
def canonical (L : Layout) : Program :=
  [.CX L.msb L.flag]++mappedSub (correction L) L.word L.carry L.cin++predicate L

theorem predicate_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (predicate L)=510 ∧ measurementCount (predicate L)=510 := by
  have w : L.word.length=256 := by simp [Layout.word,hw.1]
  have cy : L.carry.length=255 := hw.2
  have a := literalConstAdd_counts L.word L.carry L.cin L.one bias (by omega)
  have b := literalConstAdd_counts L.word L.carry L.cin L.one inverseBias (by omega)
  simp [predicate,a.1,a.2,b.1,b.2,w,toffoliCount,measurementCount]

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (center L)=765 ∧ measurementCount (center L)=765 ∧
    toffoliCount (canonical L)=765 ∧ measurementCount (canonical L)=765 := by
  have w : L.word.length=256 := by simp [Layout.word,hw.1]
  have cy : L.carry.length=255 := hw.2
  have len : (correction L).length=L.word.length := by simp [correction,w]
  have hc : L.carry.length+1=L.word.length := by omega
  have a := mappedAdd_counts (correction L) L.word L.carry L.cin len hc
  have b := mappedSub_counts (correction L) L.word L.carry L.cin len hc
  have p := predicate_counts L hw
  simp [center,canonical,a.1,a.2,b.1,b.2,p.1,p.2,w,toffoliCount,measurementCount]

theorem declaredSites (L : Layout) (hw : L.Widths) : L.wires.length=514 := by
  simp [Layout.wires,hw.1,hw.2]

end ECDSAAdd.Arithmetic.BalancedConvert

#print axioms ECDSAAdd.Arithmetic.BalancedConvert.counts
