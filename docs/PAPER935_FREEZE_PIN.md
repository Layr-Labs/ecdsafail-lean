# Omitted early freeze detection: integer-model bridge

`FreezePin.lean` models the author's armed post-step freeze check. `PinState` explicitly stores five integer fields, a frozen flag, and a stop offset. An unfrozen step runs `zStep`; only when `Tmin <= t` does a zero result freeze the state and write `t + 1 - Tmin`. A frozen state is unchanged. This follows the control order in `engine.py`'s `HmrWalk.step_fwd`, including the post-arithmetic F7 test.

`EarlyZero Tmin p x` means the ideal `zWalk` has g=0 at some state index at or before Tmin. The endpoint is inclusive: with Tmin=498, a first zero at state 498 arises in unarmed step 497 and was not detected. A first zero at state 499 is detected by armed step 498. Zero input is therefore in this early event; its behavior is not silently equated to nonzero inversion.

`pinWalk_agrees` proves that absence of this event gives equality of all five integer fields at every step, and that the explicit frozen flag equals the ideal g=0 test. The premise is not assumed to hold for all inputs. A kernel-checked zero-input counterexample demonstrates a real difference: the undetected first step increments z to 1 while the ideal frozen walk retains 0.

`pinWalk_first_zero` proves the exact recorded offset on first arrival at zero. `pinWalk_frozen_tail` proves subsequent complete control states remain unchanged. `pinWalk_record` independently proves that the record is positive exactly when frozen and never exceeds `t - Tmin`. Specializing only the public schedule length and start dial gives an offset at most 35 and therefore below 2^6 for all prefixes through 533 steps. This verifies the stop-record range, **not** the unrelated six-bit z-counter range or termination within 533 steps.

`pin_exit_failure_iff` transports the exit-window event between the pinned integer model and `zWalk` under the explicit no-early-zero premise. It supplies no probability bound for that premise or event.

This is an integer-level bridge. Actual compiled gates, finite-width overflow, zero-test correctness, measured phase/record behavior, reverse unfreezing, and the complete allocation schedule remain to be attached. No pending Framework budget specification is adopted, and no 935-qubit whole-circuit or numerical failure claim is made.
