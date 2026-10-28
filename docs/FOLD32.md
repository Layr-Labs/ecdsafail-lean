# 257-bit controlled addition with a 32-wire pool

This component implements a controlled odd literal addition modulo 2^257.
It does not instantiate an endpoint, prove canonical reduction modulo p,
or establish a complete 935-wire circuit.

The literal is specified by `bits : Nat → Bool`, with bit zero forced to
true. `fold32Literal` is the independent sum of the ten weighted block
literals. The block widths are 22,30,29,28,27,26,25,24,23,23 and their
starts are 0,22,52,81,109,136,162,187,211,234. Thus these blocks cover
exactly 257 consecutive bits.

The reference layout uses control 0, data 1 through 257, and pool 258
through 289. Every pool line must initially be zero. Nine forward blocks
save their outgoing carries in the same pool; the final block discards
its overflow. Nine reverse comparator sweeps erase the saved carries.
The odd first literal supplies the initial carry chain without an extra
incoming carry wire.

`fold32Program_contract` proves the numeric sum modulo 2^257, zero pool,
unchanged control and unchanged phase for every measurement tape.
`fold32Program_physical` establishes ordinary gate legality, and
`fold32Program_support` bounds every emitted address by 290.
These are reference addresses, not a placement into the author arena.

Next obligations include concrete Nat literal correspondence, even
constants, exact modular reduction, relocation, actual caller readiness,
and restoration of any borrowed registers before the closer inverse.
