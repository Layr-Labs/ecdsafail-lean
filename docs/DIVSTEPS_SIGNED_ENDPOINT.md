# Signed coefficient reduction into the scale accumulator

`endpointSigned` reads an actual little-endian two's-complement row and writes
its canonical residue modulo `p` into a zero `ModUnaryLayout` accumulator.
It uses the weighted constant circuit from PR101, with weights `2^i mod p` for
the low bits and `(-2^lowWidth) mod p` for the sign bit. The constants are classical
program parameters; there is no quantum weight table or extra coefficient copy.

`endpointSignedTerms_value` connects these physical source bits to
`signedRegValue`. `endpointSigned_run` proves the output is less than `p` and has
the correct field value. `endpointSigned_remainder` strengthens this to the exact
integer remainder `signedRegValue row input % p`, including negative inputs.
No sampled width bound, successful-input premise, or externally supplied scaled
accumulator value is used for this reduction.

Requirements are `0 < p < 2^n`, the accumulator widths and unique allocation,
source/accumulator disjointness, and a zero accumulator and workspace initially.
The result holds for arbitrary source values, input phases and measurement tapes.
Every nonoutput bit, including the entire source row, is restored. All accumulator
work is zero at completion.

## Resource accounting

For a source of `w` bits and accumulator width parameter `n`, the emitted circuit
uses `w*(4*n-1)` Toffolis and the same number of measurements. Its support is
contained in the source row plus `U.wires`; its qubit count is bounded by
`w + U.wires.length`. The program reuses the existing accumulator mask/core.

For the current conservative 592-bit coefficient and `n=256`, this reduction
adds **605,616 Toffolis and 605,616 measurements**. This is endpoint preparation
cost, not a net saving. The source row and U are existing allocations in the
planned composition; no combined walk/preparation support theorem is claimed
here. The 4337-wire walk allocation has not been reduced by this component.

## Remaining checklist scope

This implements the signed-coefficient reduction portion of original checklist
item 7. It does not yet account for the endpoint `f` sign, insert the preparation
into the shared-swap walk, construct the full inverse provider, or integrate it
into controlled point addition. Items 4 and 7 remain incomplete. Global 590-step
termination and the target compact-space layout remain separate obligations.
All 12 public theorem entry points are audited under the existing exact whitelist;
no proof-resource limit is increased.
