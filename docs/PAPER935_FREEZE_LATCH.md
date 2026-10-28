# Physical freeze latch

FreezeLatch.lean implements the local F7 stop-record operation from the author
engine pinned in PAPER935_AUTHOR_SCHEDULE.md. Given a zero-test witness zf,
mintFire uses X/CCX/X to compute fire XOR (zf AND NOT frozen).
recordToggle applies CX to frozen and masked CXs to the public offset bits.
With fire initially zero, frozen becomes frozen OR zf and the record is XORed
with k exactly when the latch fires. Phase and every unrelated bit are preserved.

freezeLatch_model connects the physical flag/offset to an armed, active pinStep
at k=t+1-Tmin. It explicitly requires the post-arithmetic zero witness,
zero initial record, and sufficient record width. FreezePin separately proves
the author offset is at most 35, so a six-bit record suffices.

freezeUnlatch reverses these two blocks. freezeLatch_roundtrip restores the
entire input State for arbitrary initial fire/record values under the stated
nonaliasing and width premises. Both directions use one Toffoli and no
measurements. Support is confined to the declared witness, flag, fire and
record wires; arena containment requires their explicit membership.

This is a local reversible latch, not the full author reverse schedule:
fire remains live until this inverse or a separately proved cleanup.
The author F16 measured fire cleanup, zero-test production from the actual g
row, stop-offset comparator for reverse unfreezing, arithmetic gate bridge,
full 935-wire schedule, counter safety, and numerical failure probability
remain open. No Framework specification is adopted here.
