# Parameterized recorded endpoint slot

`endpointSlot_certified` proves one conditional restoration certificate for:

```
seededAuthorWalkProgram
  ++ embedRecorded closerProgram
  ++ E
  ++ embedRecorded closerProgram.reverse
  ++ seededAuthorWalkReverse (actualHistoryDecoder ...)
```

`E` is an arbitrary `RecordedProgram`, with an explicit `EndpointContract` at
the actual closer output. No E, host layout, or endpoint route is implemented.
The certificate includes full State recovery (all wires and phase), record
well-formedness, addresses below 935, additive Toffoli/measurement counts,
actual closer release and Ready, a paired E allocation transaction, the Ready
invariant after E, and reclamation of the original walk arena.

The inherited premises are `p < 2^256`, odd p, the existing good trajectory,
`seedBefore.Ready`, actual input encoding and successful compilation. The
additional `Int.gcd p (input x) = 1` is explicit: odd p and a good trajectory
do not establish the unit f endpoint. At a point-addition call site, deriving
this from prime p and an enabled nonzero denominator is the caller's task.

## Record cursors and costs

Let W denote the seeded forward walk, R its actual decoder-based reverse,
C the closer, and k the initial cursor. `endpointCursor` is
`k + recordedMeasurementCount W`. Both C and C.reverse consume zero records.
E starts at endpointCursor; its explicit `RecordedWellFormedAt` premise is at
that same cursor. R starts at
`endpointCursor + recordedMeasurementCount E`. Its saved forward-record
indices are still based on k; E does not shift or overwrite these identifiers.
All stages use one fixed tape. Arbitrary finite tapes, including default reads
past the end, are covered by the existing interpreter semantics.

`endpointSlot_wellFormed` derives the full record-access condition. It does
not ask E to prove reverse-walk well-formedness. `endpointSlot_counts` gives:

- Toffoli: T(W) + T(E) + T(R).
- Measurements: M(W) + M(E) + M(R).

These are exact additive counts; the two closer terms are zero by
`closerProgram_counts` and reversal invariance. They are not numeric estimates
for any unimplemented E.

## Physical and allocation boundary

Forward support comes from the compiler resource checks underlying
`authorWalk_realized`, applied to the actual returned slots. Reverse support
is newly assembled from the checked inverse arithmetic, history recovery
support, and the already proved actual history-decoder support. The seed and
unseed support is included. No forward/reverse arena assumption is passed to E.

E supplies a borrowed set qs and a during-execution Arena with actual
`reserve` and output-state `release` equalities. qs must be contained in
`arenaWires \ authorClosedArena.live`; E's support must be owned during
execution. The certificate derives `qs.card <= 315` directly from
`compileAuthorWalk_closed_free` and the during arena's bound of 935. The
initial release is justified on the actual closer output, and the final
reclaim reserves exactly the closer's released payload set. A nested allocator
schedule inside E remains a caller obligation; this interface certifies its
enclosing transaction, not an invented internal allocation trace.

Address bounds and record well-formedness alone do not establish ordinary-gate
legality of an arbitrary E. An E used as a physical quantum circuit must also
supply that legality in its subsequent realization proof. This certificate
does not assert a typed quantum realization for an unchecked E.

## Route obligations

Every row identifies which side supplies the proof. A and B remain alternatives;
no implementation of either is chosen here.

| Responsibility | Route A: author fused endpoint | Route B: closed inverse / Montgomery |
|---|---|---|
| Proved by skeleton | Actual seeded walk, closer clearing/release, uncloser and actual decoder reverse compose to full State recovery when E's contract holds. | The same conditional composition. |
| Proved by skeleton | E begins after W's measurements; R follows E's measured count while retaining original saved-record identifiers. | The same cursor and reference guarantees. |
| Proved by skeleton | All composed addresses are below 935 given E's arena premise; qs has at most 315 sites by the existing exact free-count theorem. | The same conditional bounds, without promising a feasible concrete layout. |
| Proved by skeleton | Costs are the actual forward/reverse counts plus E's counts; the closer pair adds zero. | The same symbolic counts. |
| E/caller must supply | Existing walk input/good-event premises and coprimality, at the actual invocation. | The same premises for the chosen inverse invocation. |
| E must supply | A recorded program and well-formed references implementing the intended compute/cleanup capsule, including any fused Horner, delayed recovery and phase corrections it uses. | A recorded compute/cleanup capsule for the intended normalization, inverse and Montgomery components. |
| E must supply | Actual borrowed sites, reserve/release equalities, owned support, and recovery of any relocated hosts; no source lifecycle is assumed. | Actual borrowed sites and equalities for its own layout; the author's resource number is not transferred to it. |
| E must supply | `UncloserReady`: released payloads and gv sign zero, all other bits and phase restored. Extra failure conditions needed to establish this must be proved explicitly. | The same exact restoration contract, including auxiliary/output cleanup and any needed numerical conditions. |
| E must supply | Physical gate legality and any quantum/epsilon contract needed beyond this basis-state restoration certificate. | The same obligations for its different circuit. |

In particular, current `UncloserReady` restores **every** outside bit, including
any output word. Thus this is a restoration loop, not a theorem that retains
an endpoint result, implements a nontrivial point-addition output, or preserves
arbitrary changes outside the walk bank. Such use needs a separate framed
contract. No new failure-event inclusion or numerical epsilon bound is proved.
