# Exact known-output native inverse checkpoint

The full controlled finite-addend point-addition circuit at source `a782d1342f771ee880398572cfb971eeaf7dcf44` passed the CPU-pod Lean build and complete transitive axiom audit. It uses the original monomial semantics and protected all-valid-input specifications. Input sampling was not used for correctness.

| Resource | Stage 2 | Stage 5 | Full point addition |
| --- | ---: | ---: | ---: |
| Static Toffolis | 1,053,750 | 1,054,260 | 2,217,386 |
| Measurement instructions | 724,536 | 724,536 | 1,557,928 |
| Certified logical allocation/support ceiling | ≤1,899 | ≤1,899 | ≤1,899 |

The full six-stage subtotal is 2,213,282 Toffolis and 1,553,824 measurements. Exact input/corner classification contributes another 4,104 of each. The full circuit saves 504 Toffolis from `092e87c`, and 4,990,480 (69.24%) from the original 7,207,866 baseline. Measurement instructions and the Q ceiling are unchanged. These Q certificates bound distinct logical sites plus residents; the exact runtime peak is not separately measured. The ≤1,297 Q / <600K T per-stage objective remains open.

## Construction and proof

`KnownOutputAdder.program` infers each carry from a physical known sum, computes the required affine bit view with Clifford gates, and uses the existing measured carry cleanup. Its theorem proves complete State equality with the ordinary mapped adder for arbitrary independent measurement records under the actual known-sum, clean-bank and non-aliasing premises.

The native H inverse uses the restored B slice at indices 774–1025 plus a literal zero as that sum. `NativeFirstKnownFrame.front_known_sum` proves the existing clean forward copy supplies the witness. `hReceiver_after_forward`, `NativeFirstKnownInverse.inverse_roundtrip` and `inverse_restore_after_outside` discharge the clean caller boundary, phase, integer-pool restoration and changed field-spectator preservation. No copied original-x bank or new public arithmetic assumption is introduced. The generic native inverse for arbitrary A remains unchanged.

Both the active mapped kernel and the native caller kernel use the specialized inverse. The receiver costs 0 Toffolis / 252 measurements on the original bank, replacing 252 Toffolis per stage. The independent inverse costs 256 Toffolis / 508 measurements. All original point/control/exception obligations remain in the full proof.

A checked executable wrapper packages the receiver as `certifiedProgram : {Q : Program // Q = P}`. Its body is `⟨P, rfl⟩`; equality transports semantics, counts and support. It introduces no axiom or alternate extraction. The finite-support point-transfer proof now takes its program and support set as private parameters, then instantiates them with the actual circuit and its proved contract. Its public statement is unchanged. This avoids expanding the concrete support set during kernel checking.

## Full verification evidence

Completed 2026-10-07 18:19:49 UTC:

- 3,988 build jobs passed under `lake --wfail build`.
- All 1,616 public transitive axiom queries (1,615 distinct declarations) passed the unchanged whitelist: `propext`, `Classical.choice`, `Quot.sound`.
- All 895 selected committed files, including 891 Lean sources, matched before and after.
- Successful cached incremental build: 17 seconds; separate audit: 241 seconds; total: 258 seconds (4m18s).
- Verifier setup and queue: zero. Source development, repairs and transfers are excluded.
- Separate earlier attempts: 601 seconds failed in kernel memory; 397 seconds stopped an obsolete transfer process after the generic-domain repair passed; 94 seconds failed on a stale generic resource subtotal. None is included in the successful check time.

The original controlled-point, point-addition and affine formula specifications and generic native program retain their bytes. Independent review reconciled the actual resource leaves, exact query order/multiplicity, whitelist and source/log hashes.

Evidence hashes:

| Evidence | SHA-256 |
| --- | --- |
| Source manifest | `8b7748c73167227129a449561edef177659131e5bad4e7497a03614a907d994d` |
| Build log | `04c0f84bc9bcd61a69641923de7df5df3c3ac701ecf6ac2ebbf61efeb38672e3` |
| Axiom log | `ee66c1e97a046b43700276a40cc74f89321b1b5cf2473b43eebbe941df3d07a7` |
| Timing receipt | `bcec542e66c0127944f6c467ee4ca0729ba1c709184a4856de358b7cc09f5dcc` |
| Independent promotion receipt | `751a9323215138cfc61097a11174235fe873844a3dcecf45427acd359f7aae81` |
| Independent promotion review | `d1e6e0c4a4ddd4c4603e624edf94ea5b1ab9b50cc70274173fbdd402219d19f9` |

Remote attempt folder: `/root/ecdsadd-exact/logs/native-known-full-point-v4`. Reproduce the complete public audit with `bash scripts/verify.sh` on the CPU pod. All Lean execution in this campaign remains on that pod.
