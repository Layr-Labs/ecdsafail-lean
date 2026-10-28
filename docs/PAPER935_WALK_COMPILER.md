# Actual finite historical walk compiler

`compileHistoricalWalk` threads actual row addresses, post-growth history registers
and released arenas from each checked slot into the next. `compileAuthorWalk`
instantiates all 533 stages with the author's windows and requests, enabling the
freeze test at index 498. Physical exit coefficient rows retain at least seven
payload bits; the existing resize circuit emits real sign extension for early
short rows. Kernel-checked table bounds remain 582 exit payload sites and 588
arithmetic payload sites.

Contracts prove the number of returned slots, the running-max history capacity,
per-index compilation with the exact public parameters, and physicality, support
within the 935-address arena and record well-formedness of the actual concatenated
program. Successful compilation therefore gives a typed measured-circuit
representation. The concrete shared-host seed and metadata circuit supply the
initial row encoding, zero counter, clean metadata and free-arena invariant.

`authorHistoryCapacityAt` is derived from the same running-max recurrence as the
allocator. `compileAuthorWalk_capacity_at` binds it to the actual compiled record
at an index. The request bound proves that these capacities never exceed 60.

An execution diagnostic of the actual compiler returned 533 slots and a final
60-bit history. `scripts/paper935/check_walk_compilation.lean` reproduces the
compilation and additionally reports the maximum of its stored stage allocations.
This executable result is not a kernel proof that the concrete compiler succeeds.
Theorems still explicitly require successful compilation; there is no native
computation axiom or raised verification limit. Full arithmetic semantics across
all stages, reverse history recovery, the inverse endpoint, the whole point-add
resource certificate and numerical failure bounds remain unfinished.
