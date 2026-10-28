# Fused endpoint mathematical calls and failure ledger

Source pin: `andigu/uncompute@64b5a13aa249f1360846657392e6c66817b26d0f`.
References below are to `tasks/modinv-point-add/circuits/divsteps/engine.py`
and `tasks/modinv-point-add/circuits/_shared/luo_core.py` at that revision.
This is the route-A mathematical event model. It does not emit a circuit or
prove the proposed numerical checks sufficient for the actual gate programs.
Those correspondence proofs belong to the lift/fold and fused-scan work.

## Mathematical invocation values

`FusedCallSites.lean` defines a separate three-site enumeration; it does not
reuse the four invocations of the closed-XOR-inverse reference adapters.
For an enabled ordinary addition by C=(cx,cy), let
`d1=X-cx`, `a=(Y-cy)/d1`, and `d2=cx-genericX X Y cx cy`.

| row_mul site | Denominator for the divstep trajectory | Multiplier at scan entry |
|---|---|---|
| s2 apply, engine.py:3882 | d1 | Y-cy |
| s6 recompute, :3936 | d2 | d2*a, after forward walk-C rider halvings |
| s6 erase, :3945 | d2 | Same mathematical value as s6 recompute |

`fusedProductOperand` starts from the canonical field product and applies
`halveActive` using the forward armed-stage activity sequence (the reverse
of `authorRiderActivities`). The proved iteration formula counts these
active halvings; the operand is neither the unscaled slope nor the unscaled
product. Each coefficient and negate flag is derived from the original
input's mathematical `pinWalk` exit, with negate = sign(f) XOR sign(fv).

The s6 inverse call shares the corresponding forward trace; it is not a new
random input. Infinite fixed points and disabled/nonordinary labels have no
modeled fused call. A physical implementation must establish this guarding,
operand binding and trajectory correspondence. These definitions do not
establish them by assuming measured register values as event inputs.

## Four new causes

`FusedEndpointModel.lean` records source locations alongside each model.
All intermediate values are deterministic functions of a mathematical call.

1. **Row fold overflow** (engine.py:2948): the full magnitude fold is not below
   2^256. The actual row reducer retains the high bits and wraps the low word.
   `scanWord_eq` identifies the low scan word with the full fold only when
   this event is absent.
2. **Magnitude lift failure** (:3296): magnitude is outside the representable
   payload, or the complement-plus-one crosses the 58-bit lift window.
   The negative minimum -2^280 is included in this event, although the earlier
   pure mathematical `_le` fold theorems correctly accept its magnitude.
3. **Horner arithmetic checks** (:2999 and :3254; luo_core.py:1341, :1106,
   :1150): first-round copying, later conditional lazy addition, then halving
   at every round. The trace has 256 rounds followed by 242 extra halves.
   Active additions check the low-window carry correction, agreement between
   top-27-bit and full comparisons, and that the comparison clears the carry
   flag. Every halving checks its low-window no-borrow condition. Trace values
   use full arithmetic corrections, not canonicalization after every add;
   lazy representatives must not be silently replaced by canonical residues.
4. **Sign correction checks** (engine.py:3174): the input fits the target word;
   when negate is enabled it is at most p and complement-minus-(c-1) has no
   low-window borrow. Zero and noncanonical inputs are not implicitly omitted.

These are failures of explicit candidate success conditions. They are not
claimed to be a minimal characterization of all physical errors. Before
using this ledger in a circuit budget, actual forward and inverse routines,
phase correction, and pool cleanup must be proved correct under the checks.
The events here cover the modeled row_mul/sign_fix sites, not automatically
the separate s2 recomputation multiplier, s4 square, or all point-add stages.
The preexisting scaling event must likewise be bound to the appropriate
fused-route seam/rider inputs; the reference adapter's four-call seed ledger
is not automatically a fused-route fifth-event instance.

## Unchanged old ledger and exact symbolic mass

For an original label type X, `fusedFailures` aggregates the enabled modeled
calls without introducing independent label spaces. Given the old four-cause
`FailureEvents` and its fifth scaling set, `exclusiveAfter` subtracts their
union from every new cause and also subtracts earlier new causes, in the
listed order. The old five definitions remain unchanged.

`FusedFailures.partition` preserves the full bad union. The new cells are
pairwise disjoint and disjoint from the old union; `fused_nine_pairwise` proves
the nine-cell statement. `fused_nine_mass` gives their exact sum under the
same arbitrary `InputLaw`. No numerical mass, uniformity or independence
assumption is introduced. `fusedFailures_good` exposes all four checks for
every enabled modeled call outside the new union.
