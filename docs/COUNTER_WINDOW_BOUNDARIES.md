# Distribution-free counter and window boundaries

The seven-site signed counter and author row windows do **not** cover every
canonical nonzero secp256k1 field input. `CounterBoundaries.lean` proves a concrete
counterexample with kernel reduction, without increased verification limits or
native evaluation axioms:

- Input `x = 2^64` satisfies `0 < x < p` for the repository's secp256k1 modulus.
- At mathematical pinned-walk prefix 64, `z = 64`. Seven signed sites represent
  `[-64,64)`, so `CounterFailure 498 533 7 p x` holds.
- At prefix 25, `f = p`. The exit window at zero-based index 24 has `f` payload
  width 255, and `p >= 2^255`, so `WindowFailure 498 authorWindows p x` holds.

Initially `g = 2^64`. Repeated even steps halve `g` while retaining `f` and
incrementing `z`; the freeze detector is not armed at these early stages. The
counterexample uses a canonical nonzero input, so excluding the zero input does
not repair either all-input claim. These are statements about the declared
integer trajectory and failure events, not a claim that an overflowing physical
circuit continues to implement that trajectory correctly.

For arbitrary integer inputs, `pinWalk_counter_bounds` proves `-t <= z_t <= t`.
It uses the actual pinStep recurrence, including freezing. This coarse bound
implies `no_counter_failure_eleven`: eleven total signed sites suffice through
533 steps. It does not justify the current seven-site layout. No circuit is
widened, and this observation makes no claim that a wider counter fits the
935-site allocation.

`counterWitness_mass_lower` shows that each event has at least the weight of
any original input label mapping to this witness. `counterWitness_constant_mass`
shows both events have mass one under a law whose arithmetic argument is always
this witness. This is a counterexample to a uniform-over-all-laws small bound;
it is **not** an assumption about the actual distribution of point-add arguments.

These are expected failure modes of Route A's probability-budget approach:
windowing intentionally accepts some input-dependent failures. The counterexample
is not evidence of an implementation bug. It rules out silently replacing these
failure events by empty sets while retaining the same specifications.

The two events overlap here. `counterWitness_exclusive` proves that the existing
ordered partition assigns this input to **counter**, the first category, and
excludes it from exclusive history, deadline and window. This classification is
independent of the history capacity schedule. Their lower bounds must not be added, and this
result does not show how much remains after excluding other failure causes
(such as the conservative early-zero/deadline event). Existing union accounting
and the exclusive partition remain unchanged. A useful epsilon for the actual
application therefore still needs the actual input law and strict bounds, or a
proved inclusion into other already-budgeted events. Neither counter nor window
mass can simply be replaced by zero for every canonical nonzero field input.

Sampling proportions are not upper bounds. Concrete epsilon must be justified
by strict counting or analytic bounds under the actual input law (or by proved
event inclusions that reuse such bounds), not by treating these nonempty events
as distribution-free zero mass.
