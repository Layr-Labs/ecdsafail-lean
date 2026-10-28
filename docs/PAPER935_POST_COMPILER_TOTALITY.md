# Static compilation of the actual shared zero probe and freeze post-stage

The actual `List.toChunks` implementation uses arrays and a tail-recursive
accumulator. `probeChunks_flatten` proves that it preserves every input address,
and `probeChunks_lengths` proves each resulting chunk fits a positive public
width. These are symbolic proofs of the implementation, not computed examples.

`chunks_valid_of_distinct` derives every local blocked-zero validity condition
from distinct controls, flags, input chunks and one shared scratch pool. Reusing
the scratch between sequential blocks is permitted. `compileProbe_exists` and
`compileBorrowedProbe_exists` use these results to prove successful compilation
of the actual probe from input separation, arena ownership and capacity for
`width + (inputs.toChunks width).length` work wires.

`postCandidate_valid`, `compilePost_exists` and `compileBorrowedPost_exists`
prove the same for the actual freeze post-stage. Probe and offset comparison
share a pool of size

```
max (width + (inputs.toChunks width).length) (record.length + 1).
```

Persistent control, row-input and offset-record addresses must be separated and
owned. The public width must be positive; the enabled offset must fit the actual
record length. No input-state value, successful execution, or post-compilation
oracle is assumed.

`compileBorrowedPost_ports` bounds the complete physical port set by the actual
allocated arena. `compileCheckedPublicSlot_armed_exists` uses it to discharge the
post resource checks. `compileCheckedPublicSlot_unarmed_exists` preserves the
special early path: three retirement gates with no borrowed pool, no probe-width
premise and no offset-size premise.

Both public-slot theorems still require the arithmetic front to compile and pass
its static checks. This change does not prove whole-walk compilation or the
533-step arithmetic/history invariant, reverse history recovery, the inverse
endpoint, whole point-addition peak, or a numerical failure probability. The
six modules' public theorems are included in the existing exact axiom audit;
verification limits and the axiom whitelist are unchanged.
