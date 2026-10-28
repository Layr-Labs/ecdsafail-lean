# Finite physical divsteps walk

`PhysicalWalk.lean` connects the width-parametric `StepLayout` to the actual
forward and constructive inverse programs. The schedule is a finite gate list,
not a semantic inverse oracle or a sampled execution.

`L.walk N` executes `(L.at i).program` for `i = 0,...,N-1`.
`L.unwalk N` executes the corresponding constructive inverses in the opposite
order. Each step uses its original wire view and retained active/parity/swap
controls. Measurement records may differ independently between forward and
inverse execution.

## Semantic contract

`LayoutSemantics.lean` derives the arithmetic separation conditions from the
single duplicate-free allocation, allowing all three arithmetic operations to
reuse prefixes of one mask pool and one carry pool. `Encodes` interprets the
five signed rows; `Ready` additionally requires clean reusable workspace,
clean current controls, and clean reserved future controls.

`program_spec` connects the actual forward program to the next layout's
encoding of `zSlot`, preserving phase and workspace cleanliness. `undo_after`
restores the entire original state, including the three current controls.

`walk_spec` proves that the actual finite program produces all five fields of
`zWalk p x N`, preserving phase and clean reusable workspace. The next layout
contains a fresh control triple. `unwalk_after` and `walk_roundTrip` prove
full-state restoration for the actual inverse schedule. All record choices
are universally quantified.

The semantic contracts require `N ≤ L.future.length`. This deliberately
reserves one unused endpoint triple: N executed steps use the initial current
triple and N−1 future triples, while the final layout is itself `Ready`.
Execution never silently reuses an exhausted history slot. Past history stays
allocated until inverse cleanup.

## All-input capacity and resources

`walk_fits` discharges every step's numeric condition from the existing
all-input bounds `|f|,|g| ≤ p`, `|z| ≤ i`, and `|fv|,|gv| ≤ 2^i`.
For canonical inputs `0 ≤ x ≤ p` with odd nonnegative p, sufficient uniform
capacities are:

- integer width n: `2p < 2^(n−1)`;
- coefficient width v: `2^N < 2^(v−1)`;
- counter width k: `N+1 < 2^(k−1)`.

`walk590_spec` specializes this to widths 258/592/11 and every odd modulus
`p < 2^256`. It proves safe execution of 590 slots and agreement with the
integer walk. **It does not prove that the final g is zero.**

The same actual program has exact forward costs
`N(5n+5v+k−4)` Toffolis and `N(4n+3v+k−5)` measurements, with equal inverse
costs. At 590 slots and widths 258/592/11, each direction uses 2,511,630
Toffolis and 1,660,260 measurements. Frozen slots still incur the statically
allocated detection and arithmetic program costs.

The complete forward/inverse pair uses at most `L.used.length` wires. This
includes all retained and reserved history and counts shared mask/carry pools
once. No production allocation fitting 2613 wires, paper space bound, or net
resource improvement is claimed.

## Remaining integration

This is a conservative coherent-history baseline. It does not yet implement
cross-step deferred branch measurements, history compression, reverse active
scale removal, a modular division provider, or complete point addition using
this provider. Those require their own same-program correctness and resource
proofs. Full 590-step all-input termination certification remains separate.
