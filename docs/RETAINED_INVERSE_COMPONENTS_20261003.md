# Exact retained inverse endpoint, component verification

Latest integrated result: **2,856,381 Toffolis / 2,197,177 measurements / ≤2,994 static sites**, verified with 727 public audits. See [the complete retained arithmetic record](RETAINED_BOTH_EXACT_20261003.md). The checkpoint below is retained as historical component/integration evidence.

The independently emitted packed inverse endpoint is verified at **1,541 Toffolis and 1,541 measurements** for a 256-bit field value. Its semantic proof covers every canonical input and independent measurement record, with phase, controls, all non-target bits, full carry arrays and selector workspace restored.

The physical shared-pool wrapper also passes: the output is framed against the original 257-bit target, including restoration of the additional borrowed guard. The sign-convention bridge identifies its output exactly with the existing Skywalk inverse field arithmetic.

Only Clifford flag transfer and rotation use the opposite operation order. Measured arithmetic uses newly emitted forward subtraction and comparison streams with fresh arbitrary records. The old input-side signed guard is unavailable at the inverse endpoint, so a new explicit AND costs one more Toffoli than the forward packed kernel.

| Verified component | Toffolis | Measurements |
|---|---:|---:|
| Parity and reduction flag reconstruction, 256 bits | 766 | 766 |
| Clifford guard-to-early flag transfer | 0 | 0 |
| Arithmetic inverse front, 258 physical bits | 775 | 775 |
| Complete packed inverse kernel | **1,541** | **1,541** |

The combined CPU-pod check passed all **28 public transitive axiom audits** across nine modules. Only `propext`, `Classical.choice`, and `Quot.sound` were permitted. The final cached dependency build and audit took **13 seconds**, split into **4 seconds build and 9 seconds audit**. Component development checks are recorded separately, including failed attempts and exact phase start/end times.

The 256-Toffoli existing controlled swap would make the inverse field cell cost 1,797 Toffolis. Relative to 2,302 in the current multiplication path, its projected 512-cell saving is **258,560 Toffolis**, yielding a projected full-point count of **2,856,381**.

Those point-circuit savings are not promoted. The verified integrated full point circuit remains **3,114,941 Toffolis / 2,455,737 measurements / ≤2,994 static logical wire sites** at `3ab4332`.

Remaining integration obligations:

1. Connect swap undo and the physical inverse kernel to the existing all-record inverse cell interface.
2. Compose all 512 inverse replay cells and prove the multiplication endpoint.
3. Prove actual instruction support within the existing shared pool.
4. Integrate the endpoint into the complete controlled point program and run the full strict pod build and transitive axiom audit with matching source hashes and unchanged protected specification.

Authoritative combined logs: `/root/ecdsadd-exact/logs/retained-inverse-components-v1`. The campaign preserves the source manifest and all per-attempt diagnostics under `skywalk/retained-inverse/`. All Lean execution remains on the CPU pod.
