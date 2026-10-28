# Exact finite quantum semantics for measurement-free programs

## What is now proved

For a program of proper X, CX, and CCX gates whose wires all lie in `Fin n`,
`FiniteUnitary.unitary` is a complex linear isometric equivalence on the
2^n-dimensional state space. It is constructed from the program interpreter,
not supplied as a separate function by the caller.

On each computational basis vector, it acts exactly as `run`. It preserves
norm, composes in program order, and is inverted by the reversed program.
The three single-gate basis-action theorems give the usual X, CNOT, and
Toffoli bit updates. Control-target aliasing is excluded by `ProperProgram`.
The two controls of CCX may coincide, consistently with the existing interpreter.

This supplies a quantum interpretation for the current measurement-free gate
language. It does not interpret measurement, immediate or delayed phase
corrections, or a circuit's interaction with a measurement environment.

## Construction and interpreter connection

`Bits n := Fin n → Bool` labels the computational basis.
`extend` puts zero outside these n wires.
`eval n p` restricts the output of `run p []` back to those wires.

The finite projection does not discard changed bits. `extend_eval` proves
that extending the result recovers the entire interpreter output because
the program does not touch wires outside the range.
`reverse_eval` proves the two-sided inverse from the existing
`run_reverse_proper` theorem.
`permutation` packages these functions into a basis equivalence.
`unitary` uses mathlib's `LinearIsometryEquiv.piLpCongrLeft` to extend it
linearly to complex amplitudes.

`run_eq` proves the full State equality for every initial Boolean phase and
every tape. `run_basis_phase` proves that the basis action is independent of
both. These programs cannot introduce a sign phase; arbitrary complex
relative phases in the input are nevertheless preserved by the linear map.

The essential equation is:

```text
unitary(p) |x⟩ = |eval(p,x)⟩
```

Equivalently, output amplitude at y equals the input amplitude at the basis
label obtained by running the reversed program on y.
`unitary_append` proves U(p ++ q)ψ = U(q)(U(p)ψ).
`unitary_reverse` proves U(reverse p)(U(p)ψ) = ψ.

The finite register contains all program wires, including scratch qubits.
The zero extension is a boundary convention for the infinite Boolean
interpreter. It does not count as additional qubits.

## Connection to the approved error contract

`good_subspace_of_basis` proves a general linear-algebra fact: if two
continuous linear maps agree on each good basis vector, they agree on
every superposition supported on good labels. The proof expands the vector
in the orthonormal computational basis; coefficients at bad labels vanish.

`budget_of_basis` fixes the actual map to `linear n p hp hw`, the continuous
linear version of `unitary`. Given a norm-preserving ideal map, good-basis
agreement, and an explicit failure-mass bound, it constructs
`FailureBudget.QuantumBudget`.

`budget_of_recorded` makes the interpreter connection direct for embedded
measurement-free programs. Its relevant inputs are:

```lean
hp : ProperProgram p
hw : wires p ⊆ Finset.range n
e : Bits n ≃ Bits n
μ : FailureBudget.InputLaw (Bits n)
bad : Finset (Bits n)
he : 0 ≤ ε
hlt : ε < 1
hm : μ.mass bad ≤ ε
hr : FailureBudget.RecordedAgreement (embedRecorded p)
  extend (fun x => extend (e x)) bad
```

Its conclusion is:

```lean
FailureBudget.QuantumBudget
  (linear n p hp hw) (idealLinear e) μ bad ε
```

Here e is the ideal basis permutation specified by the mathematical operation.
It must be chosen independently of the implementation.
The actual map is fixed by p and cannot be selected to satisfy the theorem.
No assumption that the actual quantum maps already agree is needed:
`hr` supplies interpreter equality, and the new proof lifts that equality.

The existing `QuantumBudget.error_le` then gives

```text
‖actual ψ − ideal ψ‖ ≤ 2√ε
```

for normalized ψ with squared amplitudes μ. No postselection is used.

The label type in this theorem includes all n register bits. For an
application requiring clean ancillas, the caller must place probability
mass on valid input encodings and supply a good-input set with the required
interpreter theorem. This patch does not infer that distribution or a
reversible extension of the intended operation to all bitstrings.

## What this does not prove

- No measured-program theorem follows from `budget_of_recorded`.
  Its program is explicitly `embedRecorded p` with `ProperProgram p`.
- No Born weights for measurement tapes are assigned.
- No physical noise model or hardware calibration is specified.
- No concrete point-add distribution, numerical failure bound, or complete
  935-qubit schedule is supplied.
- No claim is made that every existing exact Hoare theorem automatically
  gives a quantum theorem. The complete state agreement and gate conditions
  must be provided.
- This patch does not add gates or change existing circuit costs.

For measured programs, the next separate obligation is a linear isometry
that retains the measurement record/environment and proves correspondence
to each interpreter branch with the correct amplitude and phase. A
Boolean all-tape equality alone cannot prove that obligation.

## Validation

The public metatheorems are included in the repository's exact axiom
whitelist audit. The proof uses existing mathlib finite Hilbert-space
definitions and the existing interpreter inverse theorem. It introduces no
axioms, admitted proofs, native evaluation, or proof-limit changes.
