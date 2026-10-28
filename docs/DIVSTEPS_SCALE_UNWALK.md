# Scale removal followed by the actual inverse walk

`ScaleUnwalk.lean` defines `walkScaleUnwalk`: the actual coherent forward walk,
the physical activity-controlled modular-halving stage, then the actual
inverse walk. The accumulator and its workspace are disjoint from the walk
allocation. The program restores every bit outside the accumulator target
word, including the original walk data and all history/work bits, while keeping
the scale stage's accumulator output. It also restores the initial phase.

## Why uncompute remains valid

Scale removal changes the accumulator, so the state entering the inverse walk
is not the original forward endpoint. `Framework/MeasuredLocality.lean` proves
support locality for arbitrary measured programs with the same measurement
tape, including all immediate Z/CZ correction inputs. States agreeing on the
program support and in phase remain equal there after execution, even when
bits outside the support differ.

The scale stage preserves the walk support and phase. Comparing its subsequent
inverse execution with the already-proved inverse-after-forward execution
therefore restores the walk. The inverse's support excludes the accumulator,
so it preserves the accumulator's value and clean workspace. The proof covers
independent forward, scale and inverse measurement tapes, and then specializes
to the actual concatenated program's tape slices.

## Contracts and resources

`walkScaleUnwalk_run` assumes valid walk/accumulator layouts, their separation,
sufficient history, all numeric fits, the initial walk encoding, a canonical
input accumulator r, and clean accumulator workspace. It proves exact halving
by the actual reverse activity schedule, initial phase restoration, clean
accumulator workspace, and pointwise restoration of all non-output bits.

`walkScaleUnwalk_remove_scale` additionally uses an explicit first stopping
index and the field relation r=target·2^t to identify the final field output.
`walkScaleUnwalk590_run` discharges all per-step numeric fits for odd p<2^256,
canonical 0≤x≤p, walk widths 258/592/11 and modular-halving width parameter 256.
It does not assume or prove that 590 slots terminate.

The exact counts for this complete program are:

- `2N(5n+5v+k−4) + N(3a+2)` Toffolis;
- `2N(4n+3v+k−5) + N(2a)` measurements.

At N=590, n/v/k=258/592/11 and a=256, these are 5,477,560 Toffolis and 3,622,600
measurements. Support is contained in `L.used ++ U.wires`, giving a qubit bound
of their summed lengths. The extra accumulator is included in this support
contract; the shared-swap schedule's 4,337-wire bound does not apply here.

## Scope

The scaled accumulator r is supplied as an input; this does not construct or
copy it from the endpoint coefficient. The program still retains coherent
activity/parity/swap histories until uncompute. It is not the measured
shared-swap reverse schedule, a termination proof, a complete division provider,
or point-addition integration. No 2,613-wire or net-resource claim is made;
parent checklist items remain open.
