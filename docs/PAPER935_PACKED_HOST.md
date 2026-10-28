# Checked two-ended payload hosts

`PackedHost.lean` generates concrete payload addresses in a bounded physical interval. The left payload is ascending from the low end; the right payload is descending from the high end. Each payload is in least-significant-first view order. Independent sign wires are excluded from these payload widths and must be accounted for separately.

`packedHost` checks both the arena bound and the sum of payload widths. Its success theorem is an equivalence, so invalid capacities cannot silently produce a layout. `pairedHosts` uses the two 256-site bands at offsets 0 and 256 for `(f, gv)` and `(g, fv)` payloads. It succeeds exactly when `f + gv <= 256` and `g + fv <= 256`.

The proofs establish exact lengths, duplicate freedom across both views, support inside the host and arena, exact live cardinality, and that the free interval is precisely the host minus its live payloads. Either side's next growth site lies in this interval if capacity remains. Ordered non-overlapping hosts have disjoint live sets.

`PackedHost.grow_payload` connects a gap site to the actual single-CX sign-extension circuit, using `Arena.reserve` and the existing row-growth proof. It derives clean reservation, output readiness, preservation of the signed integer, and physical support inside the arena. The surrounding arena may also own signs, coordinates, and other registers. Its gap must really be unowned; host geometry alone does not authorize overwriting another register.

This is a concrete checked layout primitive, not a complete initialization or trajectory certificate. It does not establish that all divsteps widths fit these hosts, allocate spills, initialize arithmetic values, or implement quantum-data-dependent address selection. Empty payloads are allowed; signs remain separate. No complete 935-qubit point-add resource claim or probability bound follows from these layout facts, and the pending Framework specification is not adopted.
