# Physical endpoint closer and permission-checked release

The actual seeded author walk now has a physical endpoint closer. On the
existing successful trajectory and coprime-input premises, its terminal bank
satisfies g = 0, |f| = 1, and gv = f*p. The last identity is derived from the
reference walk's determinant invariant and the compiled interpreter theorem;
it is not an additional endpoint assumption.

`closerProgram` clears the f, g and gv payloads and the gv sign. It preserves
fv, the f sign, every other physical bit, and the phase for every tape. Its
proper Clifford gates have zero Toffoli and zero measurement count and remain
inside the owned bank. `closerProgram_roundtrip` proves that reversing these
Clifford gates restores the entire input state. This inverse applies to the
closer's output state: a caller that reuses freed sites must restore that
state, or prove a relocated uncloser contract, before invoking it. No measured
forward walk is reversed gatewise.

The fixed source is [engine.py at 64b5a13](https://github.com/andigu/uncompute/blob/64b5a13aa249f1360846657392e6c66817b26d0f/tasks/modinv-point-add/circuits/divsteps/engine.py),
`_gv_fan` and the clearing portion of `closer` near lines 1142–1180.
The source calls `_repack` after clearing; that host-specific relocation is
not included here. The proved 620 count is before repacking and does not
specify which host supplies the next output word. The implementation groups commuting
independent-target CX gates before X gates. Its full-width affine fans include
the high-bit sign-extension cancellation performed by source `shrink_to`:
f uses the two payload encodings of +/-1; gv uses those of +/-p. The final CX
cancels gv's sign against f's sign. The g shrink is inactive because g = 0.

`closerProgram_release` applies `Arena.release` only after proving the actual
output bits zero; it also proves the retired arena Ready. The compiler's exit
ownership theorem, 907 live count, and actual widths (3,4,280,280) give a release
of exactly 3+4+280 = 287 payload sites. All four sign sites remain owned.
`compileAuthorWalk_closed_card` and `compileAuthorWalk_closed_free` prove 620
live and 315 free for this arena. `seededAuthorWalk_closer_release` combines the
actual interpreter execution, endpoint facts, physical clearing, successful
release, Ready invariant and 620 count in one theorem.

This is an endpoint component, not a proof of the complete point-addition
circuit or its 935-wire peak. The 315 free sites do not by themselves provide
an allocated output/work layout. Rebinding the author's hosts, fused row_mul,
Horner arithmetic, delayed row_unpark, measurement/recomputation, and their
additional failure events remain unproved here. The current independent
closed-inverse/Montgomery route is a different design. Route-specific wiring
awaits the project owner's choice; this closer is shared work.

Dependencies supplied by other components: `compileAuthorWalk_exit_widths`
(PR179), `compileAuthorWalk_exit_card` (PR178), and `seededAuthorWalk_run`.
The closer adds no probabilistic numerical bound and does not extend the
existing fifth failure event to the author's fused endpoint arithmetic.

## Caller-facing uncloser precondition

`UncloserReady bank before reused` makes the restoration obligation explicit:

- Every released f/g/gv payload bit is zero again, and the still-owned gv sign
  also has its cleared value zero.
- Every other physical bit equals its value in `before`, the state immediately
  before the closer. This includes fv, f's sign, metadata, history, and wires
  outside the bank.
- The phase equals `before.phase`; cleaning bits alone is insufficient.

The condition does not assume an equality to an interpreter output.
`UncloserReady.eq_closer` derives that equality using the established endpoint
facts, and `closerProgram_unclose` then proves full-state recovery for any
uncloser tape. This is an exact full-state interface: a client wishing to keep
changes outside the bank needs a separate frame-preserving interface rather
than claiming this theorem restores a modified outside state.

Ownership is a separate obligation. At this boundary the caller must return
to the retired arena, after finishing any extra reservations it made.
`closer_reclaim` proves that reserving exactly the released payloads in that
arena succeeds and recovers the original arena. It reserves no still-live
sign, coefficient or history wire. `closerProgram_reclaim_unclose` combines
restored-bit readiness, successful reservation, full-state recovery, and the
original arena's Ready invariant. It assumes the original arena was Ready
and the bank was owned, and retains the same explicit endpoint hypotheses.
It does not prove that an arbitrary intervening caller program fulfills
`UncloserReady` or returns its allocations; those remain caller obligations.
No host relocation or endpoint route is selected by this interface.
