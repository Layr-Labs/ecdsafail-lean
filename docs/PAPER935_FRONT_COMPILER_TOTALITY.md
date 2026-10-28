# Static totality of the actual arithmetic front

`compileSlotFront_checked_exists` proves that the actual arithmetic-front compiler
returns a plan and passes all its physical checks from public row widths, separated
owned addresses and three capacity inequalities. It requires neither a successful
compiler result nor an input-state execution premise. An external owned address
list remains separated from the output bank, so callers can preserve history and
other persistent registers.

Let A be the initial live-wire count, B the initial payload total, M the padded
payload total and E the exit payload total. Write growth(X,Y) for the sum of the
four positive payload-width increases. The sufficient budgets are:

- A + growth(before,add) ≤ 935;
- (A + M - B) + growth(add,exit) ≤ 935;
- (A + E - B) + (2 * counter.length - 1) ≤ 935.

The padded row pairs must have matching widths and positive arithmetic widths.
The counter must be nonempty and the exit fv payload positive. The theorem
returns the actual exit widths, address separation and ownership, and the exact
balance `exitArena.live.card + B = A + E`.

The proof follows the actual sequential allocator. `planWindowRows_exists`
discharges its initial and final ownership checks while retaining an arbitrary
external frame. `planRowResize_card` and `planWindowRows_card` account exactly for
freed and allocated payload wires. `compileBankResize_static_exists` packs the
actual planner output, and routed-bank geometry preserves the address multiset.
`SlotFront.Compiled.checks_of_geometry` derives all arithmetic, counter and
retirement gate/address checks from those intermediate layouts.

The row-layout helper specializes the already proved resize correctness theorem
to an explicitly constructed zero state, which fits every width; it introduces
no input-state oracle. The positive-growth bounds are sufficient and can be
conservative when one row shrinks before another grows.

This is a local front-compiler result. It does not prove the capacity inequalities
for the complete author schedule, whole historical-walk compilation, its arithmetic
or stack-value invariant, reverse history recovery, the inverse endpoint, a whole
point-addition 935-wire bound, or a numerical failure probability. All public
theorems enter the existing exact axiom audit. Verification limits and allowed
axioms are unchanged.
