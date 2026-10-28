# Exact bounded reduction with retained comparison

This component is not connected to an endpoint route. It gives canonical
reduction for a bounded 257-bit word, retaining the comparison information
needed to distinguish inputs with the same remainder. It is not a complete
935-wire implementation or a placement into the author arena.

The modulus `fold32Prime` is exactly 2^256 - 2^32 - 977. Kernel proofs connect
the existing odd-bit-literal adder to the concrete constants 1, p and 2^257-p.
The reference layout uses control 0, data 1–257, shared pool 258–289, and
comparison flag 290. Control must start true, the pool and flag zero, and
the input value x must satisfy x < 2p.

The actual program subtracts p modulo 2^257, copies its actual high bit
into the flag, and restores p controlled by that flag. The second adder
is obtained by an injective wire permutation exchanging controls 0 and 290
while fixing every data and pool address. The comparison is derived from
the actual first execution, rather than supplied as a correctness premise.

For every measurement tape, `fold32Reduce_contract` proves output x mod p,
a clean 32-wire pool, flag [x < p], and unchanged phase. Separate theorems
establish unchanged original control, a zero high data bit, ordinary gate
legality, support in range 291, and preservation of all outside addresses.
`fold32Reduce_reconstruct` proves x = output + (if flag then 0 else p).
This reconstruction statement also underlies the actual restoration program
described below.

The comparison flag remains live and is not part of the cleared pool.
A caller must retain it or prove a valid uncomputation strategy; it cannot
simply be erased. Inputs outside [0,2p) and initially dirty auxiliary bits
are not covered. Wider signed coefficient normalization, repeated reduction,
physical relocation, input range derivation from the actual endpoint,
comparison cleanup after an intervening computation, and complete resource accounting
remain separate obligations. No new failure events or numerical failure
bounds are asserted here.

## Actual restoration and whole-state round trip

`fold32Unreduce` uses the retained flag to subtract p from the canonical
remainder, clears the flag by XOR with the resulting actual high bit, then
adds p unconditionally (using the original true control). Its preconditions
are a canonical remainder y < p, a clean pool, and control 0 true. Either
value of the incoming flag is permitted. It returns y if the flag was true,
and y+p otherwise, with the pool and flag zero and phase/control unchanged.
It has the same range-291 address bound and ordinary gate legality.

`fold32Reduce_roundtrip` proves equality of the entire State, including all
outside wires and phase, after reduction followed by restoration. The two
programs may use arbitrary independent measurement tapes.
`fold32Reduce_append_unreduce` gives the corresponding concatenated-program
statement. The forward hypotheses remain x < 2p, true control, and initially
zero flag and pool. This is not an inverse claim for arbitrary dirty states.

A caller that modifies the remainder, flag, or borrowed pool between these
programs must first restore their required values; the theorem does not
clear a comparison bit after arbitrary intervening computation. No endpoint
placement, wide signed-coefficient normalization, or full 935-wire bound is
added by this restoration component.

## Injective host placement

`fold32PlacedReduce f` and `fold32PlacedUnreduce f` rename the actual programs
with an injective map f on wire addresses. Their contracts refer directly
to the physical mapped data word, control, flag, and 32 pool hosts; they
preserve the numeric result, clean-pool guarantee, flag behavior and phase.
`fold32Placed_roundtrip` restores the complete ambient State, including
addresses outside the image of f. The proof does not require f to be
surjective.

No endpoint route is selected and no hosts are allocated.
`fold32Placed_support_image` identifies each program's support exactly as
the image of the original support.

`fold32Footprint f` declares all 291 reference hosts. Its cardinality is 291
for an injective f, both programs are supported within it, ordinary gate
legality is preserved, and Toffoli/measurement counts are unchanged.
`fold32Placed_in_arena` requires the caller to prove that all these hosts
belong to its arena. It does not reserve wires or establish allocation
success, nor does footprint cardinality assert a live-ancilla peak.

This is a placement interface, not a chosen endpoint layout. The caller
must supply an injective map, ownership/separation evidence, mapped clean
pool and comparison flag, true control, the actual input value/range, and
any restoration required by surrounding code. In particular, no embedding
into the closer's 315 free wires or the author fv register is assumed or
claimed here. The interface is not connected to an endpoint route.
