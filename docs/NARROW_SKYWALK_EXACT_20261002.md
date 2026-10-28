# Exact narrowed Skywalk point circuit, October 2, 2026

The complete controlled point-addition circuit is Lean-verified with **3,505,085 static Toffolis**, **2,713,789 measurements**, and **≤2,994 distinct static logical wire sites** for a finite classical addend. The identity-addend program is empty. Static support is an upper bound, not a peak-live or physical-qubit count.

This replaces the preceding exact Skywalk checkpoint's 3,636,669 Toffolis and 2,845,373 measurements, saving exactly **131,584 of each**. The original `ControlledPointAddSpec.lean` is byte-identical. All valid point inputs, disabled control, identity/inverse/doubling corner cases, arbitrary measurement records, phase restoration and full allocated-work cleanup retain the original contract.

## Exact mechanism

The signed record adder uses a public width `n_i = min(258, 513-i)` for each of the same 512 rounds. The widths come from universal coprime sum/product bounds, including terminal states; they are not fitted to a sampled corpus. The full-width route and halving remain. Only after these operations do strict bounds on the odd source and halved even operand justify narrower two's-complement addition. Clifford operations restore all higher sign bits, and every carry is restored clean. The inverse is a separately emitted forward measured program with an independent arbitrary record list.

`SkywalkSumWidth`, `NarrowSignedRecord`, `NarrowSkywalkTick`, `NarrowSkywalkLoopCore` and `NarrowSkywalkLoop` prove these interfaces. The complete original physical Stage assertion, all 512 transcript entries, support inside the 1,798-site integer pool and restoration after external numerator changes are preserved. The controlled inactive branch uses safe divisor 1, satisfying the new internal coprimality/positivity premises without strengthening the public point specification.

## Same-program counts

Each old native direction used 263,168 T / 131,584 M. Each new direction uses 230,272 T / 98,688 M: the unchanged routing contributes 512×257 T and the adder contributes sum(n_i−1)=98,688 T/M. This saves 32,896 T/M per direction. Recording and unrecording occur in both division and multiplication, so the complete point program saves four times that amount. There is no narrower-routing or additional wire reduction credited.

The actual arithmetic kernels now cost 1,640,705 T / 1,246,465 M for division and 1,640,194 T / 1,245,954 M for multiplication. The controlled port adds 512 T per call, yielding 1,641,217 and 1,640,706 T. All resource theorems count the actual modified program; these are not budgets subtracted only in documentation.

## Verification

All Lean ran on the user-authorized 32-vCPU/64-GB CPU pod, never locally, with pinned Lean 4.28.0 and Mathlib. The complete warnings-as-errors build passed **3,480 jobs**. The public transitive audit passed **528 checks covering 527 distinct declarations**, preserving the old duplicate query. Allowed axioms remain `propext`, `Classical.choice`, and `Quot.sound`; no new axioms, `sorry`, or `native_decide` were introduced.

Verification took **294 seconds: 202 seconds build and 92 seconds axiom audit**. All 369 captured project-file hashes matched between local candidate and pod at verification; the immutable source manifest and logs are retained in the campaign evidence. Subsequent changes only synchronize Markdown documentation with this result. An independent source review separately recomputed the savings and checked the stronger internal premises, sign extension, phase and full-pool restoration.

The construction credits Matt Zweil and the ECDSA.Fail challenge contributors for Skywalk. Latest reference commit `799153a` reports 1,174 peak qubits and 944,124.323 average executed Toffolis, but includes approximate fit/fold/compare recipes. Those recipes are excluded. Its exact Boolean and scheduling ideas require proofs against our actual prefix and allocation. The 1.5-million Toffoli target remains unachieved; fused field arithmetic and retained-carry reuse are still separate unconnected candidates.
