# Exact compact raw-guard offer

Historical checkpoint/component record. Compact guards are now integrated and fully verified at **2,853,821 Toffolis / 2,194,105 measurements / ≤2,994 static sites**. See [the current integration record](COMPACT_GUARD_EXACT_20261003.md).

The raw signed machine word can use 257 bits for a 256-bit field value if the signed-guard AND is reconstructed explicitly from sign control and normalization. The required bound is `2*p < 2^257`, rather than the old stronger sign-read bound `2*p < 2^256`. The latter is false for secp256k1, so simply treating the 257th bit as an arithmetic sign would be invalid for positive sums near `2*p`.

`CompactGuardFront.lean` proves the independently emitted forward front with explicit three-AND selector seed, and generalizes the independent inverse front to the true full-word bound. Both preserve phase and the required non-target workspace for every measurement record and every canonical input. Field registers still contain all 256 bits; only an overflow guard is removed.

`CompactGuardPorts.lean` defines compact source/target/constant/carry views and proves their exact instruction counts. At 256 field bits, either assembled compact stream costs **1,538 Toffolis and 1,538 measurements**. The forward stream saves two Toffolis and three measurements versus the promoted kernel; the inverse saves three of each.

The candidate's projected full-point saving is **2,560 Toffolis and 3,072 measurements** over all 512 forward and 512 inverse cells. It remains unintegrated. The verified production full point stays at **2,856,381 Toffolis / 2,197,177 measurements / ≤2,994 static sites**.

All eight public component audits passed on the CPU pod. The generalized front development check took 101s (96s build +5s audit); the final combined cached component check took 14s (8s build +6s audit). Allowed axioms are unchanged.

Remaining obligations: complete compact packed endpoint semantics with explicit clean external flag ports, original-target shared-pool mapping, actual support containment, replay/point integration and full remote verification. Count the explicit reconstructed AND; do not infer the old zero-cost guard copy remains available.
