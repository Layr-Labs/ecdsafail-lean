# Exact compact integer caller integration

Verified source: `342524423bcdbd95435cb3e54c46b98cc553aacb`.

The complete exact controlled finite-addend point circuit uses **2,222,891 Toffolis / 1,564,447 measurement instructions / ≤2,068 static logical sites**. The identity-addend circuit remains empty. Q is the certified support/allocation ceiling, not a separately measured exact peak-live value.

The compact forward and independently emitted reverse integer passes now replace the earlier passes inside both arithmetic callers. Their complete physical-state equivalence and caller contracts cover the original valid-input domain, controls, arbitrary incoming phase, all independent measurement records, and full workspace restoration. Original point-addition specification sources are byte-identical.

| Stage | Toffolis | Measurements | Q ceiling including residents |
| --- | ---: | ---: | ---: |
| Division | 1,056,757 | 727,795 | ≤2,068 |
| Multiplication | 1,056,758 | 727,796 | ≤2,068 |

Each stage removes 510 measurements. Toffoli and Q totals are unchanged. The ≤1,297-Q and <600,000-Toffoli stage targets remain open.

## Verification

CPU-pod attempt: `compact-offset-full-point-v1`.

- Full Lean build: 356 seconds, 3,766 jobs.
- Transitive public axiom audit: 184 seconds, 1,319 queries / 1,318 distinct declarations.
- Total: 540 seconds. Setup and queue: 0 seconds each.
- All 662 source hashes matched before and after verification.
- Exact whitelist: `propext`, `Classical.choice`, `Quot.sound`.
- Source preparation and transfer were not separately timed and are excluded.

The compact integer caller repair passed its isolated strict Lean check in 10 seconds. Complete arithmetic caller state, executable contract/resource, support, and guarded point-port checks then passed in 7, 6, 5, and 10 seconds respectively. Failed intermediate checks are preserved in the campaign logs.

## Remaining optimization

The exact quotient-erasure helper now uses a 259-site bank, but its complete two-cell parent still costs 3,144 Toffolis versus the current 2,566. It is rejected. A sparse-offset binary-borrow shortcut also fails on valid inputs with a 223-bit high propagation chain. Neither diagnostic changes production resource results.

The next candidate streams the virtual numerator into exact quotient cleanup. Its complete arithmetic, phase corrections, lifetime schedule, and resource cost must be emitted and checked before formal integration.
