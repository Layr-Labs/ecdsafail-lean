# Exact measured terminal normalization checkpoint

The complete controlled finite-addend point-addition circuit passed verification at source commit `82a69cb65caad4f8e04fabca37078f5b6b621485`.

| Scope | Static Toffolis | Measurement instructions | Logical allocation ceiling |
| --- | ---: | ---: | ---: |
| Stage 2 division | 1,054,004 | 724,538 | ≤1,899 |
| Stage 5 multiplication | 1,054,514 | 724,538 | ≤1,899 |
| Complete finite-addend controlled point addition | 2,217,894 | 1,557,932 | ≤1,899 |

The new forward field cell uses 1,022 Toffolis and 1,023 measurements. Its existing normalization flag already equals the complement of the terminal comparison majority. Flipping and measuring that flag directly, with the actual three CZ corrections, avoids computing another copy of the majority. The source, controls, phase and all workspace are restored for every independent measurement record. The matching flag is derived from the old canonical cleanup’s zero-output contract, not imposed on callers as a new input premise.

The change saves one Toffoli in each of 510 forward field cells, reducing Stage 2 and the full point program by 510 Toffolis. Stage 5 reconstructs parity coherently for inverse arithmetic and retains its implementation and count. Measurement count and the certified support/allocation ceiling remain unchanged. The ceiling includes resident point/control sites. It is not an independently measured exact peak-live count or a globally minimal allocation.

All Lean execution occurred on the CPU pod. The successful full incremental library build passed 3,982 jobs in 1,373 seconds. The separate audit passed 1,592 public transitive axiom queries, representing 1,591 distinct declarations, in 245 seconds. The successful attempt took 1,618 seconds (26m58s). Queue and verifier setup time were zero. Source preparation, transfer and failed-attempt repair time were not separately measured and are excluded. Five earlier full attempts failed before the audit and remain recorded: 408s, 1s, 15s, 302s and 919s. Their times are not reported as a fresh successful build.

All 885 selected committed Lean source hashes matched before and after the successful check. The protected point specifications and affine formula are byte-identical to the earlier protected checkpoint. All audited closures use only `propext`, `Classical.choice`, and `Quot.sound`. The correctness and resource theorems use the original monomial semantics and exact all-valid-input contract. No correctness sampling, approximations, short GCD horizon or clipped comparison windows justify this checkpoint.

Reproduce the build and public audit with `bash scripts/verify.sh` or `bash scripts/verify_timed.sh <log-directory>` in the configured Lean environment. See the adjacent machine-readable receipt for exact successful-attempt timestamps.

The Stage 2/5 targets of ≤1,297 peak-live logical qubits and <600,000 Toffolis remain open. The campaign continues. The unsigned GCD product bound does not transfer directly to the signed native representation: for divisor 2²⁵⁵, step256 has 256 unsigned logical bits but 512 native signed bits. A changed representation needs a complete reversible circuit and whole-stage price.
