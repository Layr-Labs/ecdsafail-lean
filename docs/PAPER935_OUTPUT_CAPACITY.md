# Outputs retained across the return program

For a successfully compiled author walk, define the return program as the physical uncloser followed by the actual seeded reverse walk, including its history decoder and all recorded corrections. `retainedOutputSpace` is the arena minus the union of the persistent exit live set and this return program's quantum support.

`retainedOutputSpace_card_le` proves that this space contains **at most 28 wires**. It reuses the proved 907-site persistent exit allocation and the 935-site arena. Removing wires touched by the return program can only decrease the 28 exit-free sites. `retainedOutputSpace_no_word` consequently rules out a 256-wire output subset of this space.

`retainedOutputSpace_card` gives the exact accounting identity:

```
retained space = 28 − |return support \ exit live|
```

The numeral 28 is the original upper bound. The subsequent kernel-checked theorem `retainedOutputSpace_card_zero` proves the exact capacity is **0**, using a full counter allocation and reverse-support coverage. See [the exact-capacity proof](PAPER935_ZERO_OUTPUT_SPACE.md).

This applies to the proposed **syntactic isolation contract**: output wires must be outside both the exit live set and every wire the return program touches. Under that contract, neither a 256-bit inverse nor a 256-bit copy can remain during the return program. Moving or copying it requires an actual permitted layout; it cannot create 256 additional isolated wires in this arena.

An endpoint using this interface must consume a full inverse before the return program, or adopt a different interface. This result does not prove that all implementations must do so: a program may temporarily touch an output and eventually preserve it, but that needs a stronger semantic frame theorem and compatible ownership proof. Those are not supplied here. Consuming an inverse inside the endpoint also does not by itself prove that the resulting point-addition coordinates survive the return program.

No endpoint route, output host, multiplication implementation, failure probability, or whole point-addition resource conclusion is supplied by this capacity certificate.
