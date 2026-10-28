# Exit capacity blocks a separate fresh output

The actual compiled author walk exits with **907 live wires and 28 free wires**
in its 935-wire arena, **before a separate closer stage**. Preserving that entire live set while allocating a new
256-bit normalized output and 17 new scaling auxiliaries is impossible. Even
the separate output alone does not fit. This rules out that allocation scheme,
not all possible reversible implementations within 935 wires.

`compileHistoricalWalk_exit_card` derives the persistent exit cardinality from
the actual compiler. Each step uses the existing static compilation theorem,
exit bank widths, history growth, and retained ownership geometry. The scalar
recurrence includes row resizing and the increase in the running maximum
history length. It does not count temporary slot scratch as retained live data.

`authorExitLiveCount` checks the public scalar schedule in the kernel, yielding
907. `compileAuthorWalk_exit_card` connects that number to every successful
`compileAuthorWalk = some slots`. `compileAuthorWalk_free_card` derives 28 by
finite-set subtraction; `compileAuthorWalk_no_fresh_output` proves that any new
set of wires inside the arena, disjoint from the complete exit live set, has
cardinality at most 28. No evaluation of an entire 533-slot gate list or native
proof oracle is used.

The relevant allocation is `walkExitArena walkSeedArena slots`. Its Ready
property describes the wires in `arenaWires \ exitArena.live`; it does not
permit releasing a live register just because its current numerical value is
zero. Rows, history, and controls needed by reverse execution need a proved
restoration strategy before they may be reused.

The next design must explicitly choose an existing register to reuse or prove
a reversible release of enough live storage. In-place normalization also needs
to retain sufficient information to recover the original signed coefficient;
modular reduction alone is not injective on a wide signed word. That design,
its actual circuit, the 17-wire scaling pool placement, and the four compact
inverse call sites remain open. This result is a capacity obstruction, not a
completion of compact normalization.

## Planned closer handoff

Lamport owns the proposed actual closer which clears/releases g, the f payload,
and gv while retaining the f sign and fv. This requires the actual endpoint
facts g=0 and |f|=1, plus a separately proved gv=f*p invariant. Its inverse must
restore those rows before reverse walk execution and account for phase.
The projected post-closer live count 620 is **an estimate, not a theorem in
this PR**. No allocation proof here treats that space as released. The future
compiler must prove its actual exit live set and the peak after adding output
and scaling scratch. Deutsch owns the normalization using that eventual
interface. Thus the obstruction proved here identifies a missing reversible
release stage; it does not prohibit a later closer-based design.

`ExitWidths.lean` exports `compileAuthorWalk_exit_widths`: for the same actual
compiled slot list the final bank has payload widths `(3,4,280,280)`.
`compileHistoricalWalk_exit_widths` derives this by following actual slots;
`authorExitWindow` kernel-checks the last public window. These are payload
lengths, so each signed row also has its separate sign wire. The closer can
reuse this interface without recomputing the compiler or treating the last
requested window as an unproved actual-layout fact.
