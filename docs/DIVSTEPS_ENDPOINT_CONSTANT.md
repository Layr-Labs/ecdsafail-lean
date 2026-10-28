# Weighted constant accumulation for endpoint preparation

`endpointConstant` and `endpointWeighted` provide the physical modular additions
needed to reduce a wide endpoint coefficient into the separate accumulator.
They use the same `ModUnaryLayout` as `reverseHalf`, borrowing its existing mask
as a temporary controlled source. The mask is uncomputed after each addition;
no additional register is allocated by these programs.

`endpointConstant_run` proves that a canonical accumulator `r` becomes
`(r + (if control then k else 0)) % p`. It requires `0 < p < 2^n`, `k < p`,
`r < p`, clean accumulator work, correct widths, and distinct wiring. The phase
and every nonoutput bit are restored, including the source control and the full
mask/carry/constant/flag workspace.

`endpointWeighted_run` scans a finite list of `(sourceWire, canonicalWeight)`
pairs. Its output is `(r + sum of enabled weights) % p`, reading the original
source bits. It preserves input phase and all nonoutput bits, and leaves its
work clean. Source wires may repeat; each must be disjoint from the accumulator
allocation. The result holds for arbitrary measurement tapes and input phase.

Each term uses `4*n - 1` Toffoli gates and the same number of measurements.
The complete scan uses `terms.length * (4*n - 1)` of each. Quantum support is
contained in the listed source wires plus `U.wires`; these are bounds for the
actual emitted programs.

This component accepts canonical weights. It does **not yet construct or prove**
the weight table for a two's-complement coefficient, apply the endpoint f sign,
insert a preparation stage into the shared-swap walk, or connect the arithmetic
to an inverse provider. Those remain subsequent work. It supplies no termination
or paper-space claim. All six public theorem entry points are in the exact axiom
whitelist audit; no proof-resource limit has been raised.
