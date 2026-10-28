# Public 935 configuration tables and numeric window obligations

The exact author JSON is pinned with source attribution in `data/paper935`. `scripts/paper935/generate_schedule.py` deterministically translates its four exit-width tables and history reach table into `AuthorSchedule.lean`. Its `--check` mode rejects drift between the JSON and generated Lean source. The verifier runs this check before building.

The kernel checks the finite tables with ordinary `decide`, without `native_decide`, extra axioms, or heartbeat-limit changes:

| Parameter or table fact | Checked value/bound |
|---|---:|
| Exit windows / reach entries | 533 each |
| Freeze-start dial | 498 |
| z-width dial | 6 |
| History capacity dial | 60 |
| Arena ceiling dial | 935 |
| Each of the four exit payload widths | at least 1 |
| Sum of exit payload widths | at most 582 |
| Sum of pair-padded, add-headroom payload widths | at most 588 |
| Reach table entry | at most 59 |

These are properties of supplied public parameters, not proofs that runtime values fit them. Payload counts exclude separate signs, the third word, retained unused host sites, counters, records, and transient scratch. They are not a full live-space certificate.

`windowBefore` uses the actual seed widths `(256,256,1,1)` at step zero and the previous exit thereafter. `RowWindow.pairPad` matches `Schedule.fg_pair/v_pair`: each pair grows to its previous maximum. `addPad` matches `_fwd_add`: every payload receives one additional high bit. `_fwd_shift_exit` reuses this space; it does not append a second headroom bit for fv. Lookup and previous-window bounds are proved without out-of-range defaults. `historyRequest` matches `min(min(reach,t)+1,60)` and proves the resulting physical request is at most 60, not that all lane histories fit it.

`WindowSchedule.lean` defines signed payload fit as `-2^W <= x < 2^W`, where the sign wire is separate. It proves monotonicity under padding and exact integer addition/subtraction within one added payload bit. These mathematical bounds support later arithmetic wiring; they do not establish the compiled step's correctness by themselves.

`ExitWindowFailure` is an explicit exit-window event on an integer trace: some listed window does not contain the four fields at its corresponding next state. Its complement theorem exposes all per-exit obligations. The trace remains an explicit argument. In particular, the older `zWalk` freezes whenever g=0, while the author's circuit omits early freeze detection; equating them requires a separate no-early-stop argument. The predicate is not the complete failure set: intermediate arithmetic, counter overflow, history, termination, cleanup, and the physical execution correspondence remain to be attached.

No input distribution, numeric failure probability, or quantum error bound is claimed here. The sampled author tables remain parameters. The pending Framework budget specification is not adopted by this independent data/math component.
