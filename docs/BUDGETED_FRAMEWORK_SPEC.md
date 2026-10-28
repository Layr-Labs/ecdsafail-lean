# Budgeted specification: approved Framework design

This is the approved Framework contract for a complete controlled point-add implementation with a failure budget. It does not change `controlledPointAdd_spec`, certify the 935-wire circuit, or establish a numerical failure probability. The owner explicitly approved adoption on 2026-10-19 after technical review. This approval accepts the contract and its proof obligations; it does not certify any concrete circuit or numerical error bound.

## The promise to a caller

Fix the complete circuit, its physical quantum semantics, the ideal mathematical controlled point-add, and an input distribution **before** proving the contract. For an accepted normalized input vector, including arbitrary relative phases:

1. Outside an explicitly defined exceptional input event, the complete output is the correct controlled point-add, with the required phase and clean auxiliary storage. The event must cover all exceptional trajectories, not just history exhaustion.
2. The input's squared amplitude on that event is at most `epsilon`, with `0 <= epsilon < 1` and an application-chosen small numerical target.
3. The distance in vector norm between the complete actual and ideal coherent outputs is at most `2 * sqrt(epsilon)`. Failed branches are included. There is no postselection, renormalization, or assumption that a failure flag is available to the user.
4. Independently, the entire concrete physical schedule, including coordinates, all ancillas and any coherent record storage, must obey the 935-wire limit. A failure branch may not allocate a larger fallback outside the budget. This document does not prove that resource obligation.

This is a distribution-dependent guarantee. It is not a worst-case diamond-norm guarantee for every possible input state. A state concentrated entirely on a bad input can have failure mass one even if the uniform-input failure rate is tiny. Such a state does not satisfy a small-budget contract. Changing the input distribution requires a new bound or a proved domination/transport argument.

## Definitions in Framework

`FailureBudget.lean` defines a normalized finite `InputLaw`, explicit finite exceptional events, their probability mass, a canonical `traceEvent`, and `CoversFailure`. It proves monotonicity, the union bound and its finite-list extension. `CertifiedEvent` requires a bound below one, ruling out declaring every input bad to obtain a vacuous success statement.

`RecordedAgreement` is the existing interpreter-level part of the proposal. For each good input label, each incoming phase and **every** finite measurement tape, execution equals the full specified final `State`. The input/output encodings contain the entire wire state, not only the result coordinates. A concrete circuit must also prove `RecordedWellFormedAt 0 program` (or the appropriate enclosing cursor contract); interpreter equality does not legalize dangling or future record references. Labels must faithfully represent distinct valid encoded inputs in a concrete application. The ideal output must be fixed by the mathematical point-add definition, including disabled control, identity and exceptional point cases; it cannot be chosen after seeing the implementation.

`RecordedAgreement.seq` composes two closed recorded programs using proper record relocation. It uses the union of the two failure events **expressed on the same original input labels**. The second event must be pulled back along the intended intermediate execution. It is unsound to use an unrelated uniform distribution for every arithmetic call without proving that it is the induced distribution.

`CoherentFailure.lean` supplies the independent quantum part. Vectors are complex Euclidean spaces, with an orthogonal `badPart` obtained by keeping only exceptional-label amplitudes. `amplitudeLaw` has weights `||psi(x)||^2`. `badPart_norm_sq` identifies its event mass with the squared norm of that projection.

`QuantumBudget actual ideal mu bad epsilon` is the proposed overall **semantic** contract, with actual and ideal maps fixed as parameters. It requires:

- the stated event-probability bound;
- norm-preserving actual and ideal maps into the same complete output space;
- agreement on the entire good subspace, not merely agreement on output bit values.

The auxiliary `CoherentAgreement` error lemma works for contractions; `QuantumBudget` additionally demands isometries, so discarding failed branches or returning a zero vector does not satisfy the overall physical contract.

**The missing program-to-quantum bridge is explicit.** `runWithTape` is a Boolean-state/symbolic-phase interpreter; it does not assign Born probabilities or amplitudes to tapes. Its results alone do not establish `QuantumBudget`. A concrete implementation must construct the actual coherent dilation of its measured circuit (including record/environment registers), and prove that it realizes the code and agrees on the good subspace. An arbitrary map chosen merely to make `QuantumBudget` true is not a circuit certificate. This design does not add an axiom or a permissive `Realizes` relation to hide that obligation.

For the ideal dilation, the complete result is the ideal point-add output with zero workspace and an environment state independent of the input. The actual dilation must match this on the good subspace. Residual record information that reveals which good input was used is not allowed merely because basis output bits are correct. This prevents unnoticed dephasing of superpositions. Classical measurement-record memory and coherent environment dimensions are not automatically counted as free physical qubits: the resource model must say which records are classical and establish the implemented measurement/feed-forward semantics.

## What the quantum bound proves

Write `psi = good + bad`, where `bad` is the orthogonal input projection. If actual evolution `A` and ideal evolution `I` agree on the good subspace, then

```
A psi - I psi = A bad - I bad
||A psi - I psi|| <= ||A bad|| + ||I bad||
                  <= 2 ||bad||
                  = 2 sqrt(Pr_mu[bad event]).
```

These inequalities are proved in `CoherentAgreement.error_le`, `error_le_of_mass`, and `error_le_of_law`. The final theorem requires the input state's squared amplitudes to match the stated law. It allows arbitrary complex phases with those magnitudes.

The model also permits a finite reference register by using joint labels `(input, reference)`. Lift a bad input event to `bad × all_reference`; `InputLaw.mass_product` proves that its mass equals the bad-event mass under the marginal input law. Applying the same coherent theorem then treats entangled inputs, provided the physical maps are extended by identity on the reference and good-subspace agreement is proved for that extension. Those extensions are obligations, not an automatic diamond-norm result. A purification of a mixed state can be treated this way, but this PR does not prove a partial-trace/trace-distance conversion theorem.

For successive approximate calls, `composed_error_le` proves the triangle/telescoping rule: vector-norm errors add along **ideal intermediate states**, because actual subsequent evolution is contractive. With per-call budgets `epsilon_i`, this yields the conservative sum `sum_i 2 sqrt(epsilon_i)` by repeated application, after proving the relevant intermediate input laws. Do not substitute `2 sqrt(sum epsilon_i)` for this sequential bound. The latter bound is available only if a single global good-subspace agreement theorem is established for the complete circuit and a union bound controls its global exceptional event.

## How the failure probability will be calculated

The probability is a mathematical sum over a named distribution, not the proportion of failures in a benchmark:

```
Pr_mu[B] = sum_{x in B} mu(x).
```

For a **proved** uniform law over a finite admissible input set `D`, this becomes `number_of_bad_inputs / |D|`. A census is usable as a theorem only if its coverage, its tested predicate and its exact count are formally verified. Random samples can inform engineering but are not a certified upper bound. A statistical confidence statement, if wanted separately, would need its own sampling assumptions and confidence parameter; none is silently promoted to this contract.

The implementation must supply a deterministic, input-indexed trajectory of the chosen allocation/arithmetic policy, or a sound bad-input envelope covering all relevant random outcomes. A measurement-dependent failure event instead needs the actual joint input/outcome distribution and its quantum interpretation; **arbitrary interpreter tapes are not uniformly random samples**.

The 935 implementation's event ledger must include at least:

| Event | Required evidence for a bound |
|---|---|
| Packed-row overlap or discarded significant bits | Actual row-width evolution and all values that exceed it |
| Signed arithmetic overflow | Value bounds for the implemented width at each relevant stage |
| Counter overflow | Actual counter trajectory and encoding range |
| History capacity exhaustion | Actual stack policy and all inputs exceeding capacity (author `Cr=60` is a parameter, not a proof) |
| Failure to freeze by the allocated deadline | The actual freeze test, start window and slot budget |
| Other contract failures | Explicit coverage of incorrect release, unresolved phase debt and omitted control/corner cases, or exact proofs that these cannot happen |

Each event is pulled back to original inputs. Establish a rigorous upper bound `epsilon_j` for each, then use the union bound `Pr[any event] <= sum_j epsilon_j`; overlap makes this conservative, not invalid. No independence assumption is needed. Alternatively, prove the exact union count or a tighter partition. A clean-release proof or a correct phase-cleanup theorem can establish that the corresponding event is empty rather than charging it to a probability budget. Do not charge proof gaps to a small budget without bounding their events.

The author's 533 slots, 6-bit counter, history capacity 60, depth threshold 5 and freeze tests beginning at slot 498 are proposed implementation parameters, not certified probability statements. The older 590-step certificate effort does not by itself justify the new cutoff or capacities. No numerical `epsilon` for the new circuit is established here.

## Relation to the old specification and remaining design choices

The old unconditional theorem remains unchanged for its old program. At interpreter level, an empty exceptional event recovers the exact all-input obligation (`recordedAgreement_empty_iff`). At coherent-map level, an exact norm-preserving ideal map satisfies `QuantumBudget` with empty bad event and zero budget (`quantumBudget_exact`). This is an embedding of exact correctness into the weaker contract, not a proof that the new 935 program satisfies the old theorem. A zero event mass under a law with zero-weight inputs is also not an all-input theorem.

Before the proposal can be used as the final point-add specification, the design approval must settle or explicitly leave as separate acceptance obligations:

1. The caller's valid input domain and distribution (including the control and, where relevant, a reference system), and the application-wide acceptable vector-norm error. Uniform input is not assumed by default.
2. The exact ideal controlled-point-add encoding and the physical measured-circuit dilation bridge.
3. The concrete trajectory and complete failure-event ledger, with numerical bounds proved for the chosen policy and all calls in the application.
4. The full 935-address stage schedule and failure-path resource proof.

This PR provides the proposed definitions and generic metatheorems for review. It leaves these concrete obligations open rather than substituting capacity assumptions, sampled rates, or an arbitrary success predicate. Technical review precedes the owner's explicit approval; no circuit is certified against this proposal in this PR.
