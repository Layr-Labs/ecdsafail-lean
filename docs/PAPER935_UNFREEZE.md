# Reverse stop-record recovery

Unfreeze.lean implements the reverse record detection and local retirement
of fireR. The forward fire bit may already be zero. The strict previous-offset
bound proves that the post-state condition frozen AND (record=k) recovers
exactly the firing decision, without reading the zero-test witness.
Earlier frozen lanes have a different record and do not unfreeze.

remintFire_run uses equalConstant to recover the erased bit and restore all
comparison work. unfreezeRecord then toggles frozen and the public offset,
after that comparison work has been cleared. The complete state is exactly
the state before the forward record write, including phase and all scratch.

eraseFire performs the negative-AND measurement cleanup using X on frozen,
a measured AND with CZ correction, and X to restore frozen.
The zero witness is required here, as in the author's R13 retirement.
mintFire_eraseFire proves full-state restoration for arbitrary outcomes.

unfreeze_roundtrip combines these actual reverse gates. Starting from a
forward latch whose fire has been cleared, the entire original State is
restored. FireCleanup supplies that cleared-state result under its own
freshness/layout premises. The reverse theorem explicitly requires clean
comparison work in the post-latch state; it does not silently infer allocator
freshness. It covers a local record roundtrip, without intervening arithmetic.

For six record bits, unfreezeRecord costs six Toffolis and six measurements;
eraseFire adds zero Toffolis and one measurement. Support includes all record
inputs and comparison work, plus the zero witness for retirement.
Arena containment remains conditional on these declared wires being in the
arena; no whole-execution peak is inferred.

The author executes additional R2–R12 stages between reverse detection and
retirement. Their invariants, actual g zero-test production/cleanup, complete
forward/reverse schedule, z-counter safety, and numerical failure bound remain
open. These results use the existing basis/phase interpreter, not a newly
adopted Framework specification or an amplitude-level bridge.
