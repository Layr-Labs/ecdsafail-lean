# Kernel conversion memory and CI verification

The dual-submission integration initially passed local verification but did not finish on the hosted Linux runner. These are separate results: a local pass is not a CI pass.

## Observed runner failures

- At head `2da6a58`, run `38023468407` ended with exit 143. Its final sample showed 434 MiB available out of 15,989 MiB RAM and all 3,071 MiB swap occupied. No Lean error or explicit source of the termination signal was recorded.
- After adding 48 GiB swap, run `38025997508` hit the original 40-minute job timeout, with 17.7 GiB swap occupied.
- With one Lean worker and a 120-minute job budget, run `38028452202` reached build item 3,948/4,011, then timed out while checking `MappedCompressedTailFrame`. That process occupied about 14 GiB physical memory while the host used another 10.6 GiB swap.

The workflow retains the full verifier, one worker, temporary swap and resource diagnostics. The job timeout is a wall-clock allowance; no Lean heartbeat, recursion, kernel memory, axiom or theorem restrictions were relaxed by these fixes.

- At head `87f023e`, [push run 38036388815](https://github.com/VerifiedQC/ECDSAAdd/actions/runs/38036388815) passed the full 4,011-job build and 1,639-entry axiom audit. The parallel PR run still reached the 120-minute timeout in `PenultimateMappedInverse`. Even the successful runner spent 1,718 seconds in that module.

## Proof-only changes

`MappedCompressedTailFrame` now proves the two-cell replay identity for symbolic indices before instantiating 510 and 511. `EntryMappedFieldSegmentTrimForward` proves encoded-state transport and prefix replacement on arbitrary programs before specializing to the concrete circuits. `EntryMappedFieldSegmentTrimTerminal` uses the same form of private prefix lemma. `EntryInverseFirstGroupFrame` similarly uses symbolic encoded-state transport. `PenultimateMappedInverse` now also applies the symbolic prefix lemma instead of constructing its record-transport proof directly on the concrete head. This avoids reducing large concrete gate lists and measurement-record expressions during kernel conversion.

All existing public theorem statements and circuit definitions are unchanged. The added lemmas are private and kernel checked; there are no new axioms or trusted evaluators.

Local diagnostic runs used Lean v4.28.0 and `/usr/bin/time -l lake env lean`, with compiled imports present:

| Module | Before: wall time / maximum RSS | After: wall time / maximum RSS |
| --- | --- | --- |
| Tail frame | 64.60 s / 23,300,947,968 bytes | 4.81 s / 3,238,903,808 bytes |
| Forward entry | 219.64 s / 38,764,576,768 bytes | 5.52 s / 3,263,578,112 bytes |

The [selected profiler and resource output](verification/kernel-memory-20261010/profile-summary.log) is preserved. These are diagnostic observations, not controlled performance benchmarks: a temporary probe overlapped part of the forward baseline. The profiler attributed 55.2 seconds to the original tail identity kernel check, and 57.6 plus 156.2 seconds to the original forward entry kernel checks. Rebuilding the actual modified forward and terminal modules succeeded in 4.5 and 3.5 seconds respectively. The inverse entry module separately passed in 5.44 seconds with 3,239,854,080 bytes maximum RSS. The final penultimate inverse fix passed in 5.86 seconds with 3,251,535,872 bytes maximum RSS; its earlier local rebuild had taken 58 seconds.

The complete post-change build and transitive axiom audit are recorded in `verification/dual-submissions-20261010/`. Remote CI status must be read from the current PR checks.
