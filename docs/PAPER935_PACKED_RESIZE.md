# Physical resizing with updated host metadata

`PackedResize.lean` connects the checked two-ended host layout to its actual enlarged payload views. `growLeft` and `growRight` require one spare site and increase exactly one width. The corresponding view is the old least-significant-first payload with one new high bit appended; the opposite view is unchanged. The new live set is exactly the old set with the boundary site inserted.

`growLeft_run` and `growRight_run` reserve that boundary site and execute the single-CX sign-extension circuit. They prove ownership of the entire updated host layout, readiness of the resulting arena, and preservation of the signed row value when read through the updated view. The surrounding arena must own the payloads and sign, and leave the host gap genuinely unowned.

`reserve_resize_release` executes growth and its physical inverse, proves full-state restoration, and then proves that releasing the cleared site returns the exact original arena, including its live set. `shrink_reserved_run` also handles arbitrary wider states whose represented integer fits the narrower signed window: the numeric bound derives redundant-sign equality, the CX clears the returned bit, and release returns the original ownership and readiness while preserving the signed value. Thus shrink is not restricted to immediately undoing a growth operation.

The existing resize support and cost theorems still apply: one CX per resize, zero Toffolis and measurements, and support only on the sign and boundary site. Signs and any other live registers are separately owned and counted.

These are local resize transitions. They do not provide a complete divsteps width schedule, a coherent quantum-data-dependent choice of widths, spill management, initialization, or a numeric failure bound. The pending Framework specification is not adopted, and no whole-point-add 935-qubit claim is made.
