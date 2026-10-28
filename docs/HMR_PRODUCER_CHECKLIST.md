# HMR producer handoff to task #51

Task #49/#50 supplies the items below for the selected `circuit.py` HMR
configuration. PR211 supplies conditional consumers; **none of these source
instances is supplied by those consumers**. This page is the delivery contract,
not a completion claim. Source references are pinned to
`engine.py@64b5a13aa249f1360846657392e6c66817b26d0f`: `halve_horner_scan`
2999, `sign_fix` 3174, `row_mul` 3254, `_row_lift` 3301, `_row_reduce` 3312,
`row_unpark` 3326, and HMR plateau constants 3490/3492. See the
[reference-to-caller port table](FUSED_CALL_LAYOUT.md#reference-to-caller-maps)
for the exact lift/fold/Horner wire roles. Definitions live in `HmrRowMulSpec.lean` and
`HmrLifecycleInput.lean`; usage is described in [the consumer guide](HMR_ROW_MUL_CONSUMER.md).

## Physical views and actual programs

- Supply the actual recorded programs H (forward), U (s2 unpark), R (s6 erase),
  their intervening K segments, and the s2-to-s6 program J. Prove any decomposition
  used by a consumer against the emitted program; do not substitute a model K.
- Supply `HmrRowMulLayout`: signed row payload 280, multiplier/output 256 each,
  anc 24, flags, widths, data/anc distinctness and flag/data separation. Bind
  row/sign addresses to the **new HMR** exit/retirement result and the concrete
  repack journal. Old mixed-walk capacities do not identify these views.
- Establish initial `HmrRowMulPre`: coefficient from the physical signed row,
  multiplier value, zero output/scratch, and LiftGood/RowGood/HornerGood. For s6,
  the original input is the actual s2+J result at its accumulated tape cursor.

## Three execution certificates

| Instance | Fields to provide and prove |
| --- | --- |
| `HmrRowMulSpec L H` | `scanAndHalves`; `program_eq` with placed lift/fold prefix; `legalCursor`, `wellFormed`; quantum `support`; computed `rowMulPhaseDebt`; `run` proving output `call.beforeSign`, unchanged multiplier/sign, payload equal to actual `L.parked`, zero scratch and exact phase equation. Forward leaves the row parked. |
| `HmrRowUnparkSpec L U` | Lifecycle `pre`, `wellFormed`, `support`, computed `phaseDebt`; `run` restoring all original row bits, zeroing the demolished multiplier, preserving output, cleaning scratch and proving the phase equation. |
| `HmrRowMulInvSpec L R` | Separate lifecycle `pre`, `wellFormed`, `support`, computed `phaseDebt`; `run` restoring original row bits, preserving multiplier, zeroing output, cleaning scratch and proving the phase equation. Do not implement inverse measurements by reversing an instruction list. |

These `run` fields quantify over the actual tape/cursor and arbitrary permitted
input phase. Numeric output congruence alone is not their bitwise postcondition.
Ordinary gate nonaliasing and a typed quantum-circuit instance remain separate
obligations; these structures do not assert them.

## Input rules and K-side facts

- Instantiate `HmrUnparkInputRule` / `HmrEraseInputRule`: define `records` and prove
  `accepts` from `HmrRowMulPre L call original`, its record condition and the declared boundary to the **existing
  pre itself**. Respect the universal quantifiers of these fields. Then prove
  `records` at the actual start/end cursors; an empty/vacuous rule is insufficient.
- Unpark boundary: original sign, actual parked payload, zero scratch, and zero
  demolished multiplier. Erase boundary instead requires original multiplier
  bits and output `call.beforeSign`. Supply the actual K post-state facts.
- Either prove the final bitwise frame directly, or use `hmr_frame_after` with
  disjointness from **hmrBasisWrites**. Controls and phase-correction operands may
  overlap retained data. Temporary writes later restored require the direct frame;
  mutation-footprint exclusion is only a sufficient condition.
- To use `hmr_unpark_input_of_demolition`, prove K is the stated destructive-X
  word plus tail, its row/scratch mutation exclusion, and tail exclusion from
  the demolished word. The erase corollary similarly needs the stated footprint
  exclusion. These facts do not prove phase restoration.

## Records, phase, ownership, and final integration

- Prove forward `legalCursor` and rule `records` at every actual boundary;
  preserve absolute measurement ordinals on the same tape. Show deferred
  corrections reference earlier measurements and realize the specified phase debt.
- Discharge the concrete whole-caller cancellation equation exposed by
  `hmrThreeCallDebt_zero_iff`, using actual states. A restored basis or clean
  multiplier is not a phase proof; local debts may cancel across stages.
- Provide both `HmrArenaLease` reservations/supports and the actual
  `HmrArenaTransfer` precondition/readiness across J. Retain the s2 pool until
  unpark and the s6 pool across apply/erase; neither is released early.
- Hand off these instances with source configuration, Lean names and validation.
  Task #51 then binds all three calls, point-addition encoding and
  RecordedAgreement. Complete stage censuses and the 935 bound belong to task #53;
  this checklist and the generic peak lemmas do not discharge them.
