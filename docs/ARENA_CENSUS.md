# Composing declared live-set censuses

This is the route-neutral preparation for task #53. It does not instantiate
or certify a complete source circuit and does not establish its 935-wire bound.

`liveCensus` takes arbitrary finite wire sets, without an Arena or a fixed
capacity. `livePeak` is the maximum of their cardinalities (zero for an empty
trace). `livePeak_append` and `livePeak_stages` prove that sequential stages
compose by maximum. `livePeak_le_iff` reduces a bound to every declared snapshot.
Simultaneous components instead add their sizes only under proved disjointness,
as stated by `census_disjoint`.

For successful Arena operations, `reserve_card` proves the exact increase and
`release_card` proves the exact decrease. Release still requires the existing
allocator's zero-wire check; this is not a reset. `reserve_release_peak` proves
that the three-snapshot stage peaks at its reserved state. `borrowMany_census`
computes the peak for a successful n-wire reservation.

`Arena.withinBudget` is a new **arithmetic budget check**, not an allocator or
semantic checker. It checks `live.card + n ≤ budget` for an arbitrary budget.
`borrowMany_withinBudget_iff` relates it to the actual two-snapshot peak only with a
successful `borrowMany` equation. A passing arithmetic check alone does not
supply an allocation, clean wires or program correctness.

`arenaChain_peak` specializes sequential composition to any list of Arena
stage traces. Although the existing Arena type carries its own physical bound,
none of these cardinality/max equations uses that fixed number as a premise
or conclusion. The underlying Finset theorems also work outside that Arena.

To apply these results to the full point-add program, each stage must supply
all interior live sets and prove they correspond to the actual allocation and
release sequence. Merely listing initial/final sets can miss an interior peak.
Boundary compatibility, program support, semantic cleanup, completeness of the
trace, and the concrete census values remain implementation obligations.

## Executable allocation-log validation

`ArenaLogAction` records either a reservation or a release with a supplied
boundary basis-state sample. `checkArenaLog` executes each operation through
`Arena.reserve` / `Arena.release`, fails on an invalid operation, and generates
the entire list of intermediate live sets. It does not accept a manually
supplied list of occupancy counts. A log of n actions produces n+1 snapshots,
including both the initial and terminal states.

`checkArenaLog_iff` proves acceptance exactly matches the inductive valid-log
relation, whose transitions require successful allocator equations.
`checkedArenaPeak_sound` returns that relation and the exact maximum of all
generated counts. `checkedArenaPeak_bound` equates an arbitrary budget bound
with the bound on every generated snapshot. Reservations cannot overlap live
wires; releases require ownership and zero values in the supplied sample.
Kernel-checked examples cover an interior peak that disappears after release,
overlapping reservations, and rejection of a dirty release sample.

This checker validates **the given log**. It does not prove that the log contains
all allocations emitted by the source program, that its initial Arena is the
actual initial ownership, or that a release sample is the actual program state.
Those three correspondence obligations must be discharged before its peak can
be attributed to the circuit. In particular, passing a made-up all-zero sample
does not prove that a cleaning circuit ran. The validator does not interpret
quantum gates, establish phase cancellation, or reset a released qubit.

## PR210 export and checker compatibility

The exporter at PR210 `738b690` uses `live_before` and `live_after` lists of
half-open `[lo, hi)` intervals. `arenaIntervalSet` has exactly the corresponding
set semantics (including deduplication); its membership theorem is
`∃ (lo,hi) in intervals, lo ≤ q ∧ q < hi`.

`checkArenaStage` matches the supplied initial Arena to `live_before`, runs the
existing allocation-log checker, and matches its final Arena to `live_after`.
`checkedArenaStagePeak` still uses **every** generated snapshot, not the maximum
of just the two boundary sets. Acceptance yields the valid allocator chain,
its exact length, both boundary matches and the exact peak. Kernel examples
check an interior peak with empty endpoints, a half-open endpoint mismatch,
and overlapping intervals without double-counting.

| Export/producer item | Integration |
| --- | --- |
| `events: {kind: take, wire: q}` | `ArenaLogAction.reserve {q}`; this calls the existing `Arena.reserve`. |
| `events: {kind: give, wire: q}` | `ArenaLogAction.release {q} sample`; the exporter does not provide the required actual quantum state. Supply and prove that boundary-state binding separately. |
| `Arena.checkBorrow n work` success (PR210) | Reuse its `checkBorrow_contract` to obtain the existing `reserve work.toFinset` equation plus length and Nodup. No second ordered-work checker is defined here. If the source allocates wires individually, retain those individual events for trace correspondence. |
| `Arena.checkRepack` / compiled repack log | Keep the existing checker and expand its internal reserve/retire or proved release transitions when constructing a peak trace. Treating an entire repack as a single boundary change can omit its temporary occupancy. |
| `compileHmr*Log` output | Reuse the producer's emitted event order and checker certificates; this module does not implement a competing compiler. |

This is a Lean interval/boundary adapter, not a JSON parser or a completed
PR210 instance. JSON-to-Lean transcription, ordered-work checker invocation,
repack expansion, and the source/execution correspondence must still be supplied
at integration. PR210's `checkBorrow` is not yet imported into this main-based
branch; its implementation and declarations are not copied or redefined here.
