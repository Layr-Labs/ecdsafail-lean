# Shared-carry inverse row arithmetic

`Paper935.rowSub` reverses the measurement-free `rowAdd` gate stream. `rowAdd_proper` proves that every gate has distinct controls and target before applying the existing inverse theorem. This argument is restricted to the author's k=0 shared-carry path; it does not justify reversing measurement-based adaptive adders.

For disjoint, equally sized rows, `rowSub_run` preserves phase and every non-target bit, including source, control and carry. With input values A,B and carry K, its output T satisfies `(A + T + K) % 2^n = B` when controlled, and T=B otherwise. `rowSub_unique` proves this relation determines the unique n-bit output. Thus the primitive is controlled modular subtraction, including nonzero incoming carry. Both operation orders restore the complete state for independent measurement tapes. Clean input carry is returned clean.

The same physical rows, control and single carry are used: 3n−2 Toffolis (zero for n=0), zero measurements, no new workspace. `rowSub_in_arena` inherits the 935 arena address obligation from its wiring. This is a local support result, not a full point-add peak certificate. A signed subtraction caller must still establish its chosen no-overflow window; no such condition is inferred from the arena size.

This component is independent of the pending overall failure specification. It neither adopts a new Framework specification nor claims a failure probability or complete compact walk.
