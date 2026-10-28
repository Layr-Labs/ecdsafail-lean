# Physical inverse of the divsteps counter

`Arithmetic/Divsteps/CounterUpdateInverse.lean` adds an independent inverse
component without changing the forward counter or other arithmetic proofs.
It uses a new actual ripple adder, not a reversed measurement-containing gate list:

```
negateSigned active zero z carry
++ signComplement active z
++ signComplement swap z
```

The physical `active` and `swap` inputs are retained history and must obey
`swap ⇒ active`. With both false, the inverse preserves z. With only active true,
negation followed by complement subtracts one. With both true, the two final
complements cancel and the result is negation. The controls, n-bit zero source
and n−1 carry bits are restored; all wires outside the n-bit target are restored.
The entire interface wire list must be duplicate-free.

## Proven contracts

- `counterUpdateInverse_spec`: modular action, phase and clean workspace for
  every measurement record, even when the excluded control combination occurs.
- `counterUpdateInverse_int_spec`: output is −z, z−1, or z according to the
  retained controls, provided that integer result is in the signed n-bit range.
  In particular, negating the minimum-negative word is not treated as an exact
  integer operation.
- `counterUpdateInverse_after_forward`: the complete state after forward then
  inverse equals the initial state, including phase and every bit. The forward
  and inverse may use entirely independent arbitrary measurement records. The
  theorem requires initial source/carries zero and consistent controls, but no
  signed no-overflow premise: the modular round trip includes wraparound.
- `counterUpdate_roundTrip`: the same equality for the concatenated physical
  program, with measurement records consumed according to the normal semantics.
- `counterUpdateInverse_frozen`: standalone inverse is the full-state identity
  when both controls are false. Its static gate schedule remains present.

The inverse costs exactly n−1 Toffoli and n−1 measurements, and at most 3n+1
wires, including both controls and scratch. The full forward/inverse pair costs
2(n−1) of each and shares that same support bound. For the conservative 11-bit
counter, the inverse costs 10 Toffoli and 10 measurements on at most 34 wires.

## Integration boundary

The caller must retain the original controls, not recompute them from the
post-step arithmetic state. This inverse restores only the counter; row-kernel
and halving inverses, history cleanup, the full walk, concrete layout, termination,
and the arithmetic provider remain separate obligations. The full-state theorem
composes directly when intervening operations have restored the counter's
forward output and clean source/carries before this inverse executes.

All 12 public theorem entry points are included in the full verification script
and its existing exact axiom whitelist. Acceptance requires independent review.
