# Conditional arithmetic provider and complete point-add consumer

The existing `RecordedPointArithmeticBackend` requires correct arithmetic on
all valid operands. It cannot represent an implementation that is allowed to
fail on a small, identified input set. The new `ConditionalPointArithmeticBackend`
adds a tape-independent `safe multiply X Y control` predicate. Its correctness
field is required only when that predicate holds; support and record-reference
validity remain unconditional.

No failure is discarded or postselected. Correctness still means arbitrary
incoming phase and arbitrary measurement tape, the intended output value,
and every non-output wire restored. `ofExact` embeds existing providers with
`safe = True`; `program_ofExact` proves equality of the complete emitted program
with the existing exact consumer.

## Actual arithmetic operands

The ordinary point-add path uses two calls. For input coordinates `(X,Y)` and
constant `(cx,cy)`, let `a = (Y-cy)/(X-cx)` and
`d = cx - genericX X Y cx cy`.

1. Division is called on denominator `X-cx` and numerator `Y-cy`.
2. Multiplication is called on denominator `d` and numerator `a`.

`GenericSafe` requires the provider's corresponding two predicates. On disabled
paths both calls instead receive the unchanged `(X,Y)` with control false.
`Safe` pulls these conditions back to the original control and input point,
after the actual exceptional-branch classification. Addition of infinity emits
an empty program and needs no arithmetic condition. The existing curve proofs
establish nonzero denominators on enabled ordinary calls; the inactive provider
must still preserve arbitrary operands, including zero, under its safe contract.

The two calls are not treated as independent, nor are their operands assigned
fresh uniform distributions. A concrete trace-based exceptional set must cover
failure of either call under the original input law.

## Completed conditional theorems

- `add_spec`: complete controlled point addition for every input and constant
  point satisfying `Safe`, including infinity, doubling and exceptional cases;
  the original control and entire allocated workspace are restored.
- `add_frame`: every non-point wire is restored, including unused ancillas.
- `recorded_agreement`: the full emitted program has the required all-phase,
  all-tape state equality outside a supplied original-input exceptional set.
- `pointAddPerm`: independent mathematical controlled translation by the fixed
  point, with controlled subtraction as inverse.
- `pointAdd_budget`: the typed physical circuit realizing this same emitted
  program satisfies the measured `QuantumBudget` relative to that permutation.
  It requires the concrete clean-state encoding, its non-point frame property,
  a specified original input law and exceptional mass bound, and safe-call
  proofs on good inputs. The standard `QuantumBudget.error_le` then gives
  `2 * sqrt epsilon` for matching normalized input states.

These are proved conditional statements, with no admitted provider correctness.
The remaining provider implementation must prove its `correct`, `support` and
`wellFormed` fields and establish `Safe` outside actual failure events.

## Resource boundary

This consumer reuses the existing point-add layout and fixed arithmetic stages,
including their existing large workspace. It is **not** a 935-qubit circuit or a
proof that the compact inverse can fit that entire pipeline into 935 live wires.
The compact arena, schedule, inverse/walk implementation, numerical event bounds
and resource proofs remain separate implementation obligations. Existing exact
specifications and programs are unchanged.


## Concrete clean encoding

`PointInputEncoding.basis` constructs the actual point bits and control value,
with every other wire zero. Constant XOR from a temporary true control defines
this mathematical bit string; those initialization gates are not added to the
point-add execution. The point is read back correctly, and the encoding is
injective. A proved finite-wire restriction yields `encoding : (Bool × Point) ↪
Bits n` whenever the point and control wires lie below `n`.

`encoding_boundary` discharges the clean-input hypothesis, and `encoding_frame`
proves that the independent controlled translation leaves every non-point wire
unchanged. `PointInputEncoding.budget` instantiates the earlier quantum theorem
with this encoding, removing those two assumptions from the consumer interface.
`pointFintype` derives finiteness from the injective 513-bit point code; it does
not assume a curve group-order theorem. The actual circuit, conditional provider
and failure-budget obligations described above remain unchanged.

## XOR inverse to in-place quotient

`InverseQuotientCore.program` emits a concrete controlled Montgomery product-add,
low-256-bit swap, and product-subtract. Given a separately computed inverse, it
replaces the numerator Y by Y/X and restores every other basis bit and the phase.
The temporary holding the old numerator is cleared using X*(Y/X)=Y. Disabled
control preserves Y, including when X=0; enabled control requires X≠0.

`InverseQuotientRecorded.program` surrounds that core with two calls to the same
closed recorded inverse program. Its `InverseContract` requires arbitrary-target
XOR with the controlled inverse, a clean declared workspace, and preservation of
all other wires and the phase for every tape. The second call clears the inverse;
no reversal of measurement gates is assumed. Record references are relocated by
`recordedThen`. The workspace must avoid the numerator and inverse output but
may overlap the core's restored temporary workspace. The success predicate is
on X and the control, so it is unchanged when Y becomes Y/X.

The wrapper proves full phase/state correctness, valid record references from
those of the inverse endpoint, exact support union, and resource counts of two
inverse calls plus the explicit core. This is a large Montgomery reference
adapter, not a 935-qubit implementation. The actual compact inverse endpoint,
physical placement in the point backend, compact multiplication, numerical
failure bounds, and the complete 935-space schedule remain separate obligations.

### Concrete reference point placement

`PointInverseEndpoint.backend` binds the inverse endpoint to the existing point
caller. The denominator is the caller's 256-bit X register plus a clean padding
bit at pool offset 2341. Product work occupies offsets 0–1826, the inverse
occupies 1827–2083, and the temporary occupies 2084–2340. Width, nonaliasing,
clean initial values and support within the declared point pool are proved from
the existing point layout. This is an actual placement, not a capacity estimate.

The resulting `ConditionalPointArithmeticBackend` uses the recorded quotient
adapter for division and the existing exact Skywalk reference for multiplication.
It can be passed directly to `ConditionalPointDialog` and `PointInputEncoding.budget`.
Only the division call inherits the inverse success predicate. An endpoint still
must supply its actual recorded program, arbitrary-target XOR correctness, valid
record references, support, and a clean workspace avoiding the numerator and
inverse output. No endpoint existence, numerical success probability, or 935-space
bound follows from this constructor.

`PointInverseEndpoint.callInput` identifies the actual denominator/control pair
for each original controlled point input (and `none` for addition of infinity).
The enabled denominator is proved nonzero. `bad_mass` pushes the original point
law through this map exactly; it never substitutes a uniform inverse-input law.
`budget` and `budget_of_events` feed that bound into the full encoded point-add
quantum theorem, with the four event bounds and their coverage still explicit.
`enabled_zero_mass` proves that enabled zero-denominator calls have zero mass.
Numerical bounds for counter/history overflow, freeze deadline and width-window
failures are not supplied here.

### Physical validity of the quotient adapter

`InverseQuotientRecorded.realize` now constructs a coherent circuit typing for
the actual recorded quotient program from the inverse endpoint's physical
validity, record validity and finite support. The quotient core's ordinary gate
target/control conditions are proved from the register layout, including all
Montgomery lookup, measured addition/subtraction, normalization, rotation and
cleanup stages. These conditions hold on every input, including failed inputs;
they are not inferred from good-input arithmetic correctness.

`RecordedPhysical` supplies relocation/composition lemmas that preserve ordinary
gate validity. Measurements remain explicit typed constructors, with their saved
records relocated normally. Full point-program physical validity (including the
legacy multiplication arm and other point stages) is still a separate obligation.


## Both arithmetic calls from the inverse endpoint

`PointInverseEndpoint.bothBackend` replaces both division and multiplication.
The product adapter runs the same XOR inverse endpoint twice, clearing the
inverse register after an actual Montgomery core. It swaps the core's factor
and denominator views: division by the computed inverse implements multiplication.
The generalized core theorem permits an arbitrary canonical factor when disabled;
its original quotient interface is preserved. All other wires and the phase are
restored for every measurement tape. Physical validity and a typed `Circuit` for
the product adapter follow from the supplied endpoint's physical/record/support
obligations, as for the quotient adapter.

Use `twoCalls_budget` or `twoCalls_budget_of_events` with `backend := ep.bothBackend`
and the defining equality of its safety predicate. The first inverse input is
`callInput C`, the second is `productCallInput C`: on the ordinary branch these
are respectively `X-cx` and `cx-genericX X Y cx cy`. Each is proved nonzero when
enabled. Disabled calls retain their actual X input and must satisfy the
endpoint's disabled safety predicate. Both input laws are pushforwards of the
same original point law. The resulting budget is the sum of their bounds;
independence and uniformity are not assumed. Repeating the XOR endpoint to clear
its output does not require another input failure event, since its contract is
valid for every target state and every tape on the same good input.

The older `ep.backend` and its one-call budget remain available for the mixed
reference implementation. Do not apply that one-call budget to `ep.bothBackend`.
Neither backend supplies the compact inverse or a 935-qubit theorem. The full
point program still requires physical validity of its fixed non-backend stages.


## Constructing the whole point-add circuit

`ConditionalPointDialog.program_physical` proves physical validity for every
fixed stage of the actual point program: measured streamed square (including its
pool permutation), canonical constant addition, reflection/recovery, zero tests,
classification flags, and exceptional-point writes. Its only remaining gate
validity input concerns the two replaceable arithmetic calls. The proof follows
actual gate lists and layouts; it does not infer local gate validity from a
high-level functional specification. Source registers in mapped arithmetic may
repeat read-only wires; they must stay disjoint from mutable data and carries.

`PointInverseEndpoint.point_realize` instantiates both calls with the inverse
adapters and constructs a typed `Circuit` for the complete recorded point-add
program. The supplied endpoint must itself be physically valid. Its recorded
reference validity, support, and success-conditional full-state contract are
already fields of `PointInverseEndpoint`.

`PointInverseEndpoint.point_budget` combines that construction with the two
induced-input bounds and the clean point encoding. It returns the actual circuit,
its equality to the implemented point program, and a `QuantumBudget` with total
failure bound `ε₁ + ε₂` (hence the framework's `2√(ε₁ + ε₂)` vector error bound).
A separate assumption that the full point program has a circuit realization is
no longer needed. The ideal operation remains the independent mathematical
controlled point-add permutation.

This closes the caller's physical-realization obligation for the reference
layout. It does not construct the compact inverse endpoint, supply numerical
failure estimates, replace the large reference arithmetic pool, or establish the
935-qubit bound. Those inputs and resource obligations remain explicit.
