# Trajectory failure events and probability accounting

This application layer uses the existing `FailureBudget`/`FailureAssembly`
interfaces. It supplies mathematical events instead of another probabilistic
framework. It does not certify a numerical success probability for the complete
533-step circuit.

## Existing evidence checked

| Existing source | What it proves | What it does not prove |
| --- | --- | --- |
| `AuthorSchedule` | 533 exit windows, freeze start 498, six-bit counter, history request at most 60 | Probability that a trajectory fits those windows or history requests |
| `WindowHeadroom.addPad_step_fits` | Addition/shift headroom follows from entry-window fits | Success of the next exit shrinkage |
| `History.pushHistory_spec` | Exact finite push when `2*history+bit < 2^width` | That the premise holds on most inputs |
| `FreezePin.author_stop_offset_fits` | Every prefix's freeze offset is at most 35 and fits six bits | Six-bit signed **z** counter safety or timely termination |
| `BlockedZero.run_eq` | Every tape gives the exact full-state controlled zero test | Scratch cleanliness or layout validity of an arbitrary caller |

The public census/window tables are parameters, not probability certificates.

## New mathematical events

`TrajectoryFailures` starts from the same original finite input labels `X` and an
explicit arithmetic argument `input : X → Int`. It uses `pinWalk`, the model
with omitted early tests and frozen lanes, rather than silently replacing it
with the ideal walk.

- `WindowFailure`: seed representation failure or any exit-window failure.
- `CounterFailure`: signed-counter range failure at any prefix, including zero.
  Its width includes the sign bit.
- `HistoryFailure`: a selected push fails its finite width inequality. The
  reference stack `trajectoryHistory` is unbounded, so earlier modular wrap
  cannot hide a first overflow. The selector reads the **post-slot** frozen
  flag, z and fv; the stored parity comes from the **pre-slot** g.
- `StopFailure`: early zero or failure to freeze by the deadline. Including
  `EarlyZero` is conservative and supplies the existing `pinWalk_agrees`
  exclusion; it is not a proof every early-zero input physically fails.

`trajectoryEvents` installs these in the existing `FailureEvents` categories.
`trajectory_good` exposes all four numerical obligations outside their union.
`trajectory_push_fit` and `trajectory_push_value` connect the history event to
the actual finite push network, assuming the current state encoding, selector,
parity, and physical width match the mathematical reference.

Depth and the history-capacity function remain explicit public parameters. The
caller must bind depth to its coefficient prefix length plus one and capacity
to the actual allocated register at each step. This file does not guess that
mapping from the census spans. For a 533-step instantiation, use `authorSteps`,
`authorFreezeStart`, `authorCounterWidth`, and `authorWindows`; the full compiler
must still establish all physical/schedule correspondences.

## Exact mass and no double counting

`FailureEvents.exclusive` partitions the same union by first category: counter,
then history not already in counter, then stopping not in either, then remaining
window failures. `exclusive_bad` proves the bad set unchanged;
`mass_exclusive` gives an exact sum with overlaps counted once.
`trajectoryBounds` packages these masses into existing `FailureBounds`, and
`trajectoryBounds_total` identifies the total with the original union's mass.
No independence or uniformity assumption is made. Existing
`budget_of_failureBounds` and `error_of_failureBounds` apply after actual-circuit
agreement and a bound below one have been proved; the exact symbolic mass alone
is not such a numerical certificate.

`BlockedZeroFailure` defines failure as the existence of a phase/tape violating
the independently specified controlled zero-test state. Valid layout and clean
scratch make this event empty, hence its mass is exactly **0** for every input
law. If cleanliness is established only outside an existing bad set, the
failure event is a subset of that set; adjoining it does not increase mass.
This also preserves phase and all scratch, rather than only the tested bit.

`offsetOverflowEvent_empty` and `offsetOverflow_mass_zero` give the other exact
numerical result: freeze-offset overflow has mass **0** for all prefixes up to
533, without assumptions about counter or termination success.

## Remaining numerical and implementation obligations

No nontrivial numerical upper bound is claimed here for window, signed-counter,
history, early-zero, or deadline failure. Required inputs are:

1. The actual original input law and arithmetic-argument map for each call.
   Point-add denominators must not be assumed independently uniform.
2. The compiled step count, prefix depth, and physical history-capacity schedule.
3. Proved weighted counts or analytic bounds for the induced events under that
   law. Sampling proportions are not certified upper bounds.
4. Full-walk correspondence and allocation: layout validity, scratch ownership,
   finite views, measurement record references, and all-tape state/phase
   correctness on the good set. Resource allocation failure is not automatically
   covered by a numerical row-window event.

The initial domain (including zero denominators), inverse endpoint, and point-add
boundary cases remain the caller's responsibility. The four-category union is
not asserted to exhaust every possible implementation failure before that
correspondence is proved.
