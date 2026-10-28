# Exact direct-divisor candidate

Production remains the complete point-addition source `9ea2e58e077e02b0525cb3947492d3246b2b18fd`: 2,740,035 static Toffolis, 2,081,591 static measurement instructions, and at most 2,579 allocated logical sites. No result below is promoted.

The new executable `DirectSkywalkArithmetic` uses the original divisor register during the integer walk and restores it after the field update. Two external flags select the actual GCD transcript when enabled and the exact divisor-one transcript otherwise. This implements the inactive identity without a 256-bit safe-divisor copy. `DirectZeroControlled` repairs a zero divisor to one with a retained zero flag, then restores the original word and clears the flag.

## Verified scope

- Complete compressed integer forward/reverse subsystem: strict component build54.30s plus45 public axiom queries9.54s. Current source hashes match its saved manifest.
- Mixed field replay and division/multiplication endpoints: all24 public declarations audited during strict compilation. Final checks9s,7s,7s; separate inline-audit elapsed time is not measured.
- Direct nonzero-divisor arithmetic kernel: current strict kernel compilation7s and separate36-theorem axiom audit12s. Copied preparation/restoration infrastructure has separate component receipts. Both control branches, incoming phases, independent measurement records, numerator values, original divisor restoration, and all outside-numerator wires are covered.
- Concrete caller selector separation and zero wrapper:48 current contract queries passed in12.86s with source hashes matched. The complete guarded caller replacement is under development/verification separately.

No new axioms or sorry are permitted. Audits allow only the project foundational whitelist (`propext`, `Classical.choice`, `Quot.sound`). All Lean execution is on the authorized CPU pod.

## Why this does not reduce Toffolis yet

The direct-divisor kernel still uses the existing512 retained field cells. Each signed core costs `6*256+2=1538` Toffolis, with another256 for conditional routing. Selecting the effective transcript adds2 per cell. Removing the safe-divisor copy addresses storage, rather than this arithmetic cost.

| Component in guarded division candidate | Static Toffolis |
|---|---:|
| Integer forward/reverse passes |395,264|
|512 signed field cores |787,456|
|512 controlled routing operations |131,072|
|512 pairs of transcript selectors |1,024|
|Seed, endpoint and zero-repair glue |1,537|
|Total (caller verification pending) |1,316,353|

Multiplication differs by one Toffoli. These totals describe the new candidate program and must not replace the promoted stage totals until its caller and full point integration pass verification.

The direct layout declares2,326 resident-plus-workspace sites. This is a layout-capacity theorem, not an integrated stage support theorem or minimum peak-live measurement. It does not meet the1,297 target.

## Remaining work

Finish the guarded caller contract, prove physical program support, integrate compressed/interleaved replay and safely reuse released sites. Replace the current canonical field kernel with sparse-modulus fused arithmetic and exact full-width cleanup. Reducing integer work and routing is also necessary for the600K target: even hypothetical255-Toffoli signed updates would leave658,433 Toffolis in the old512-step stage.

The incumbent’s compressed tape, carry retention and interleaving are reusable exact mechanisms. Its shortened comparisons and393/392-round envelopes cannot be substituted directly into the present all-nonzero-divisor theorem. Exact recurrence witnesses include `x=2^255` (511 steps) and `x=p-1` (480 steps). Exact replacements or a proved fallback are required.
