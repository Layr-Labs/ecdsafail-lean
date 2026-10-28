import ECDSAAdd.Arithmetic.Paper935.WideCoefficientInclusive
import ECDSAAdd.Arithmetic.Paper935.ScalingNoBorrow

namespace ECDSAAdd.Arithmetic.Paper935

/-- Mathematical call input for engine.py:3254 row_mul and :3174 sign_fix.
The caller supplies values from original labels, never measured register data. -/
structure FusedCall where
  enabled : Bool
  coefficient : Int
  multiplier : Nat
  negate : Bool

/-- engine.py:3296 _row_lift: complement the 280-bit payload and add one
through the 58-bit window. The minimum negative payload is an explicit escape. -/
def FusedCall.LiftGood (call : FusedCall) : Prop :=
  call.coefficient.natAbs<2^280 ∧
    (call.coefficient<0 →
      (call.coefficient.natAbs-1)%2^58+1<2^58)

/-- engine.py:2948 row_reduce keeps high bits and wraps the low word.
Only no-wrap inputs identify that word with the full mathematical fold. -/
def FusedCall.RowGood (call : FusedCall) : Prop :=
  wideMagnitudeFold call.coefficient.natAbs<2^256

/-- engine.py:2948 row_reduce's low-word value, as a mathematical model. -/
def FusedCall.scanWord (call : FusedCall) : Nat :=
  wideMagnitudeFold call.coefficient.natAbs%2^256

/-- luo_core.py:1341 gc_lazy_cma, before its truncated fold and comparison:
full-width sum, then a full (untruncated) carry correction. Not canonical mod p. -/
def fusedLazyAdd (y r : Nat) : Nat :=
  let s := r+y
  (s%2^256 + if 2^256≤s then 2^32+977 else 0)%2^256

/-- luo_core.py:1341, :1106, :1150: successful low-window correction and
flag erasure. The comparator uses the author's top 27 bits (engine.py:2271).
This checks the actual Boolean comparison, rather than excluding all ties. -/
def FusedAddGood (y r : Nat) : Prop :=
  y<2^256 ∧ r<2^256 ∧
  (2^256≤r+y → (r+y)%2^256%2^58+(2^32+977)<2^58) ∧
  (decide (fusedLazyAdd y r / 2^(256-27)<y/2^(256-27)) =
    decide (fusedLazyAdd y r<y)) ∧
  (decide (fusedLazyAdd y r<y)=decide (2^256≤r+y))

/-- engine.py:2999: first round copies into zero; later set bits add y.
The recurrence is evaluated on mathematical intermediate values. -/
def fusedHornerInput (call : FusedCall) (k r : Nat) : Nat :=
  if k=0 then (if call.scanWord.testBit k then call.multiplier else 0)
  else if call.scanWord.testBit k then fusedLazyAdd call.multiplier r else r

/-- engine.py:2999: every round ends with one exact mathematical halve. -/
def fusedHornerState (call : FusedCall) : Nat → Nat
  | 0 => 0
  | k+1 => halveMod fold32Prime (fusedHornerInput call k (fusedHornerState call k))

/-- engine.py:2999 and :3260–3287: 256 scanning rounds, then 242 halves.
All low-window checks use the corresponding mathematical input value. -/
def FusedCall.HornerGood (call : FusedCall) : Prop :=
  call.multiplier<2^256 ∧
  (∀ k<256,
    (0<k → call.scanWord.testBit k=true →
      FusedAddGood call.multiplier (fusedHornerState call k)) ∧
    FoldNoBorrow 58 (2^32+977)
      (fusedHornerInput call k (fusedHornerState call k))) ∧
  ScalingNoBorrow fold32Prime 58 (2^32+977) (List.replicate 242 true)
    (fusedHornerState call 256)

/-- engine.py:3254: output of the fixed 498-halving row-multiply schedule,
before the residue sign correction and later data-dependent rider. -/
def FusedCall.beforeSign (call : FusedCall) : Nat :=
  (halveMod fold32Prime)^[242] (fusedHornerState call 256)

/-- engine.py:3174: negate via complement then subtract c-1. The bound and
no-borrow condition are explicit, including the zero and noncanonical cases. -/
def FusedCall.SignGood (call : FusedCall) : Prop :=
  call.beforeSign<2^256 ∧ (call.negate=true →
    call.beforeSign≤fold32Prime ∧
    2^32+976≤(2^256-1-call.beforeSign)%2^58)

/-- engine.py:2948: no low-word overflow identifies the scan word with the
full fold. This is a mathematical equality, not a circuit implementation. -/
theorem FusedCall.scanWord_eq (call : FusedCall) (good : call.RowGood) :
    call.scanWord=wideMagnitudeFold call.coefficient.natAbs :=
  Nat.mod_eq_of_lt good

/-- engine.py:2999: the copying first round has no modular-add obligation. -/
theorem fusedHornerState_first (call : FusedCall) :
    fusedHornerState call 1=halveMod fold32Prime
      (if call.scanWord.testBit 0 then call.multiplier else 0) := by
  simp [fusedHornerState,fusedHornerInput]

/-- engine.py:2999: later rounds take their addend/halve input from the
previous mathematical round, rather than restarting from the initial seed. -/
theorem fusedHornerState_step (call : FusedCall) (k : Nat) :
    fusedHornerState call (k+1)=
      halveMod fold32Prime (fusedHornerInput call k (fusedHornerState call k)) := rfl

end ECDSAAdd.Arithmetic.Paper935
