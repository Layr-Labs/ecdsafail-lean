# Finite signed divsteps counter

`Arithmetic/Divsteps/CounterUpdate.lean` implements the z-counter update with
actual ordinary `Program` gates. It is an independent component; it does not
compute active/swap predicates, assemble the full finite walk, prove termination,
or instantiate the point arithmetic provider.

## Physical interface

Inputs are distinct `active` and `swap` wires, an n-bit target `z`, an n-bit clean
`zero` source and n−1 clean `carry` bits. The combined list must be duplicate-free.
The two physical controls satisfy `swap = true → active = true`.

The circuit is `signComplement swap z ++ addInPlace zero z carry active`:

| active | swap | output |
|---|---|---|
| false | false | z |
| true | false | z+1 |
| true | true | −z |

The swap branch complements every target bit and adds the carry-in 1, performing
two's-complement negation. The other active branch adds 1 directly. The inactive
branch does neither. There is no additional control ancilla or second adder.

`counterUpdate_spec` proves the modular action even for the excluded control
combination. `counterUpdate_int_spec` proves the signed action under explicit
output-range bounds. Both hold for every measurement record and preserve phase,
controls, the zero source and all carries. `counterUpdate_frame` restores every
bit outside z; `counterUpdate_frozen` proves equality of the entire final and
initial states when both controls are false. A frozen run still has the static
adder gate/measurement schedule; the state identity is not a zero-cost claim.

## Width and integration

`counterNext_bounds` derives absence of overflow from −t ≤ z ≤ t and
`t+1 < 2^(n−1)`. `counter_width_before` establishes this at each t<T when
`T < 2^(n−1)`. `counter_width_590` proves 11 bits suffice before step 590.
This is a conservative capacity theorem, not a termination theorem and not a
proof that six bits suffice.

`counterUpdate_walk_spec` connects the actual gate program directly to the
canonical integer `zWalk` transition using its proved `zWalk_bounds`. The caller
supplies the physical controls equal to `g ≠ 0` and
`g ≠ 0 && (0 ≤ z && g % 2 = 1)`. These controls retain their pre-step values;
computing and later uncomputing them remains the surrounding circuit's job.

## Resources

The very same program has exactly n−1 Toffoli gates and n−1 measurements.
Its static support is contained in the two controls, target and two scratch rows,
so it uses at most 3n+1 wires. For n=11 this is 10 Toffoli, 10 measurements and
at most 34 wires, including the target and both controls; 21 bits are clean
source/carry workspace that can be shared with neighboring arithmetic.
These are component costs, not full-walk or point-addition resource claims.

All 14 public theorem entry points are included in `scripts/verify.sh` and checked
against the existing exact axiom whitelist. Independent review is still required.
