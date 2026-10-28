# Conditional endpoint slot with retained outputs

`endpointSlot_output_certified` extends the full-restoration slot with a declared output set `O` and output basis values `v`. The actual program remains:

```
seeded author walk → closer → E → uncloser → actual seeded reverse
```

The final state is exactly `withOutput O v s`: the input phase is restored, every bit outside O is restored, and each bit in O equals its declared value. `endpointSlot_output_bits` states these three conclusions explicitly. This is a pointwise interpreter certificate; no endpoint implementation, concrete output placement, or arbitrary-E quantum realization is supplied.

## Caller obligations

`EndpointOutputContract` is evaluated on E's actual execution from the real closer output, at the absolute cursor following the forward walk. The caller supplies:

- O is contained in `retainedOutputSpace`: it is inside the 935-site arena, outside the exit live set, and disjoint from the actual uncloser and reverse program support. This also excludes the owned closer payloads and gv sign. Exit freedom by itself is insufficient.
- E's recorded references are well formed at that cursor, and its support is inside the arena.
- E restores the pre-closer phase, keeps the cleared payloads and gv sign zero, and restores all other bits outside O to the pre-closer values.
- E's actual result on O equals the declared `v`.
- The allocator first reserves O from the closed arena, then reserves temporary workspace. E uses only the resulting owned set, returns the temporary workspace clean, and **does not release O**.

The existing input hypotheses remain, including coprimality, the good trajectory, successful compilation, seed readiness, input encoding, and the modulus bounds. The slot does not derive new failure probabilities or ordinary-gate legality for arbitrary E.

## Proved by the certificate

The frame lemma `runWithTape_withOutput` handles ordinary gates, X measurements, immediate corrections, and corrections from previously saved records. Disjoint outputs neither influence these operations nor incur phase debt. It supplies the semantic link through the actual return program; no return-program equality is assumed from the caller.

The composed recorded program has valid record references and addresses below 935. Its Toffoli and measurement counts are forward + E + reverse; the closer and uncloser contribute zero. The reverse starts after E's actual measurement count while saved references retain their original absolute ordinals.

`endpointOutputBorrow_ready` proves that E's resulting retained arena is Ready from actual support and execution, that O remains owned, and that temporary workspace is disjoint from O. `endpointOutputBorrow_capacity` proves `|O| + |temporary| ≤ 315` and a during-E live-set bound of 935. The final basis is clean outside `seedBefore.live ∪ O`.

These are actual E-boundary reserve/release transactions plus interpreter and support facts. They do not synthesize a complete ownership schedule for the eventual point-addition consumer. That consumer must explicitly handle the retained output and own its eventual release; no implicit measurement, reset, or free copy is inserted.

## Capacity and route limits

The certificate proves `|O| ≤ 28` using the separate capacity theorem. No 256-bit output can instantiate this syntactic-isolation interface, including a copy of such an output. The subsequent theorem `retainedOutputSet_empty` proves that, for this successfully compiled walk, this fresh isolated output set must in fact be empty. The interface remains a conditional frame theorem, but supplies no nonempty fresh output for this walk. See [the exact-capacity proof](PAPER935_ZERO_OUTPUT_SPACE.md).

Both the author's fused endpoint route and an inverse-plus-Montgomery route must supply their own E, layout, mathematical output specification, and consumer. If either route needs the return program to touch output wires and nevertheless preserve their values, this interface does not cover it: a stronger semantic frame theorem and compatible ownership argument are required. Consuming an inverse within E alone does not prove that the resulting point-addition coordinates survive the return program.
