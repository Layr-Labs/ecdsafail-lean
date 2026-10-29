# Editable entrant

The candidate extends the paired-comparison Skywalk entrant from promoted submission
`d64584fc-6971-4979-8d02-eca5a6563024`. It replaces the two remaining standalone
258-bit point comparisons with 257-bit comparisons of `x` and the low bit of `y`.

`CompressedMath.lean` proves that this comparison distinguishes every valid
secp256k1 point, including infinity. In particular, it proves that 7 is a quadratic
nonresidue modulo the protected prime, so a finite curve point cannot have `x = 0`.
The public point encoding is unchanged.

`CompressedEqual.lean` proves the comparator's boundary behavior, physicality,
support, and resource counts. `CompressedFlags.lean` connects it to the dialog
flags, and `Program.lean` composes the complete circuit. The inherited
`PairEqual.lean`, `ShortEqual.lean`, and `ZeroFlag.lean` retain the earlier optimizations.

The locally kernel-verified uniform bounds are:

| Metric | Bound |
|---|---:|
| Toffolis | 2,214,316 |
| Measurements | 1,554,852 |
| Static qubits, including I/O | 1,899 |
| Syntax slots | 47,000,000 |
| Q × T | 4,204,986,084 |

The protected benchmark runner accepted these bounds after a fresh build and kernel replay of all eight entrant modules.
The original Skywalk reference has Q × T = 4,210,816,014; the paired-comparison
predecessor has Q × T = 4,204,989,882.

Run from the benchmark work directory:

```sh
LEAN_NUM_THREADS=2 yukon setup --track lean
LEAN_NUM_THREADS=2 yukon run --track lean
```

`Main.lean` must export `entry`, `bounds`, and
`certificate : ECDSAAdd.Challenge.Certificate entry bounds`.
The protected contract covers all addends and valid input points, both controls,
arbitrary phase and measurement records, and complete non-I/O workspace cleanup.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed by the judge.
