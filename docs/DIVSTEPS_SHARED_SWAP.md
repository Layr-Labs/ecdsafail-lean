# One physical swap wire across the finite walk

`SharedSwapLayout.lean` and `SharedSwapWalk.lean` implement the actual deferred
swap schedule with a single physical swap address. Every forward step measures
that address back to zero before the next step uses it. On the reverse pass,
the restored updated coefficient and retained activity control reconstruct
swap; the original absolute measurement outcome corrects its phase.

## Layout and state contracts

`L.sharedAt i` takes the arithmetic views and activity/parity addresses from
`L.at i`, uses `L.history.swap` at every index, and removes the local past/future
lists. `sharedAt_valid` proves the original single-step uniqueness and capacity
contracts for every such view. The global history queue remains in `L` and is
tracked by the schedule rather than inserted into local uniqueness.

`SharedReady` requires the current arithmetic encoding, clean arithmetic
workspace, clean current controls, and clean still-unused activity/parity
controls. It imposes no condition on the removed future swap addresses.
`shared_step` proves that the actual forward program followed by swap
measurement establishes the next `SharedReady`, provided the history queue
is not exhausted. In particular, the shared swap is actually zero at this
boundary; reuse is not an abstract freshness assumption.

`sharedSwaps_correct` proves full-state restoration for the concrete nested
forward/reverse program, including arbitrary phase, measurement tape, and
starting cursor. Each inner schedule restores the complete post-measurement
state before the outer decoder runs. `sharedSwaps_wellFormed` proves that
record references point to earlier measurements.

The 590-slot specialization uses the existing all-input capacity proof for
widths 258/592/11, odd nonnegative p below 2^256, and 0 ≤ x ≤ p. No terminal
g=0 assumption or theorem is included.

## Resources of this same program

The exact complete-round-trip counts remain:

- `N(2(5n+5v+k−4)+1)` Toffolis;
- `N(2(4n+3v+k−5)+1)` measurements.

At 590 slots and widths 258/592/11 these are 5,023,850 Toffolis and 3,321,110
measurements, equal to the distinct-swap measured schedule.

`sharedSwaps_support` bounds the physical support by `sharedUsed`: arithmetic
data/work, one swap, and the current/future activity/parity pairs. This list
is duplicate-free and has length

`3n + 2v + k + mask.length + carry.length + 5 + 2*future.length`.

`sharedUsed_saving` compares explicit allocation bounds: the old bound exceeds
this one by `3*past.length + future.length`. It does not assert that the exact
touched-wire cardinalities differ by that amount. With no past histories,
590 future slots, mask capacity 592 and carry capacity 591, the new bound is
4,337 wires, versus 4,927 for the old allocation. `sharedSwaps590_qubits`
proves this conditional bound for any valid layout satisfying these capacities;
the theorem itself does not construct a numerical allocator at these widths.
The subsequent [numeric allocator](DIVSTEPS_LINEAR_LAYOUT.md) supplies one
and specializes the same program without an abstract layout parameter.

The concrete small `sharedSwapExample` supplies two fresh transitions, uses
swap address 23 throughout, and proves a 28-wire bound versus the original
30-wire allocation. Removed swap addresses 26 and 29 are absent from the
new allocation.

## Remaining work

Activity and parity histories remain retained. The allocation includes an
unused endpoint pair and has not been optimized to the paper's space target.
This is not a 2,613-wire construction, a modular division provider, reverse
scale removal, complete point-addition integration, or a global 590-step
termination proof. The parent checklist items remain open.
