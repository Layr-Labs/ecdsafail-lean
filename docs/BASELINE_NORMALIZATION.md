# Normalized baseline programs

The challenge-facing entries are `Baselines.normalizedSkywalk` and
`Baselines.normalizedValueWalk`. They apply two local rewrites to the original
programs: same-wire `CZ a a` becomes `Z a`, and repeated-control `CCX a a t`
becomes `CX a t`. The original submission definitions are preserved.

`normalize_run` proves equality of signed-basis execution for every state and
measurement tape. The transformation preserves the exact wire support, number
of measurements, and total gate slots (including both correction lists).
`normalize_toffoli_exact` gives the exact accounting identity:

    normalized Toffoli count + original repeated-control CCX count
      = original Toffoli count.

The fixed-interface correctness and qubit bounds apply to the normalized
entries. These are component proofs, not complete challenge Certificates:
whole-program target/control separation and a uniform total-slot bound are
still required. `normalize_physical` explicitly retains the old physical-gate
premise; correctness alone does not discharge it.

The generic transformation does not establish whether a particular original
program contains repeated ports. Numerical counts for actual baseline
instances must be reported separately, and evaluation at one public constant
must not be presented as a proof for every public constant.
