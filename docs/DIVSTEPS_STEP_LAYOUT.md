# Width-parametric step layout

`Arithmetic/Divsteps/StepLayout.lean` packages the physical parameters of
`ForwardStep` into a concrete layout and proves structural invariants for reuse
across a finite walk. It does not choose a production allocation or prove that
one fits the point-addition interface's 2613-wire workspace.

## Rows, reusable workspace and retained history

`StepRow` has explicit low, middle and sign wires. Integer f/g, coefficient
fv/gv, and counter z widths are independently chosen; `Sized n v k` records
those choices. `Valid` requires equal widths within each arithmetic pair,
adequate mask/carry lengths, and uniqueness of the combined physical allocation.

All three arithmetic components take prefixes of **one mask pool and one carry
pool**. Integer n, coefficient v, and counter k use n/v/k mask bits and n−1/v−1/k−1
carry bits. These views intentionally overlap. Uniqueness counts each physical
pool once, rather than demanding disjoint copies. Detection has its own work
wire per physical g wire; one and carry-in are also explicit clean wires.

`Clean` describes reusable zero workspace. `Fresh` separately requires the
current active/parity/swap triple to be zero. `past`, `history`, and `future`
are finite lists/current slots of retained control history. Data, reusable work,
and history are disjoint; arithmetic, routing, branch and detection calls have
explicit derived uniqueness lemmas.

`stepLayoutExample_valid` is a kernel-checked concrete allocation with integer
width 2, coefficient width 3, counter width 2 and two separate history slots.
`stepLayoutExample_reuses_prefixes` proves that the narrower arithmetic actually
uses prefixes of the wider workspace. This is an instantiability witness, not a
cryptographic-size layout.

## View and history transition

`StepRow.halfView_wires` equals the existing `skywalkHalfView` exactly. The view
is a permutation of the same physical row; its length, support and uniqueness
are preserved. Detection pairs follow physical wires, so their reordering does
not allocate new detection scratch.

`next` rotates g's view and advances the finite history queue, preserving the
old current triple in `past`. It does not erase history. Theorems `next_valid`,
`next_support`, `next_g` and `next_sized` provide the next structural layout.
`at` iterates this layout transition, with validity, support, widths and exact
remaining-history length proved. `at_can_advance` gives the finite-index
condition for a fresh next slot. After history is exhausted, the total layout
function keeps the last current slot; execution must not reuse that slot as
fresh. `next_fresh` therefore explicitly requires nonempty future history.

## Actual program contract

`program` is the existing `ForwardStep` with fields and shared prefixes supplied.
`program_current_support` proves it touches only data, reusable work and the
current history triple. `reserved_frame` proves every past/future history wire
is unchanged for arbitrary states and measurement records. `next_fresh` proves
that initially zero future slots stay zero and the selected next triple is fresh.

`program_counts` derives exact costs for this same program:

- Toffoli: 5n + 5v + k − 4.
- Measurements: 4n + 3v + k − 5.
- Static support: at most `used.length`, which equals
  3n + 2v + k + mask.length + carry.length + 5
  + 3(past.length + future.length).

This is a conservative explicit allocation, including all reserved history,
not the paper's space figure or a net qubit reduction. The layout provides
structural, freshness and support contracts; encoding integer states and
instantiating the complete forward/inverse walk semantic theorem remain the
walk integration's responsibility. Numeric arithmetic bounds, oddness,
termination certificates and provider contracts are not discharged by a layout.
