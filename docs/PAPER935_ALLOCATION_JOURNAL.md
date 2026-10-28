# Public allocation journals

`AllocationJournal.lean` compiles a finite list of public `(source, destination bands)` requests. `planMove` checks source ownership and calls the existing band-priority allocator. `planJournal` threads the resulting live set into the next request and returns a concrete relocation journal and final arena. Missing sources and exhausted bands return `none`. Choices do not inspect a basis state and are not quantum measurements.

Metadata retirement is not a reset. `planMove_sound` proves that the physical three-CX swap clears the old site, that the actual `Arena.release` succeeds, and that readiness is restored. Its transient arena contains both source and destination and has cardinality at most 935. The generated `AllocatedJournal` certificate retains these obligations for every step.

`planJournal_correct` derives final readiness, signed row-view preservation, full-state forward/inverse roundtrip, and at most 935 physical wires for the emitted `repack` program from compiler success and initial readiness. Distinct endpoints and arena membership are derived from allocation, not separate caller hypotheses. `planJournal_prefix_ready` makes readiness and live-cardinality bounds available at every public prefix. The inherited repack count theorems give zero Toffolis and measurements.

`planMove_fallback` proves one-step allocation success when the source is live, the entire arena is an offered fallback, and fewer than 935 sites are live. It does not prove that arbitrary request lists succeed. Requests use physical addresses; a later request must name the current physical source, not an outdated logical row label.

This is a verified public relocation compiler, not the author's complete data-dependent packing strategy. It supplies neither a complete point-add schedule nor a numeric failure probability, and does not adopt the pending Framework budget specification. The 935-wire theorem applies only to the emitted relocation program. Dynamic or coherent width/placement choices remain separate work.
