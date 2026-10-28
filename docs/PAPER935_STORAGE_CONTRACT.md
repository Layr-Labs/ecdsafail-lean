# 935-wire storage contract and first row primitive

The target is a complete point-add circuit with at most 935 simultaneously live quantum wires, including the two 256-bit point coordinates. This change provides a contract and one arithmetic primitive; it does **not** instantiate the complete circuit or establish that target.

## Physical arena and ownership

`arenaWires = range 935`. The proposed initial hosts are x=[0,256), y=[256,512), A=[512,768). Their union has 768 wires, leaving 167 for signs, counters, history, spills, frozen-state records and scratch. There is no external scratch arena. Host addresses can change logical role only through an explicit stage contract.

`Arena.live` denotes owned wires, not merely nonzero wires. `Ready` requires all unowned arena wires to be zero. `reserve` succeeds exactly for a disjoint in-arena claim and proves the borrowed wires zero. `release` succeeds only for currently owned wires that are zero; it is a proof-side permission check, **not** a measurement, reset instruction or physical zero test. Failure returns `none`; it never expands the pool or overwrites live data. An implementation must translate the resource checks into its allocation/control policy.

`StageContract` declares before/during/after ownership, borrowed/released sets, writable wires, actual program support, a state precondition, preservation of non-writable wires, and release cleanliness for every measurement tape. `ready_after` composes these obligations; `peak` bounds the three declared live sets. Every internal allocation change must be a separate stage, or its wires must be included in `during`. `schedule_peak` bounds a supplied list of arenas. Neither theorem constructs the author's schedule: their use as a full resource certificate requires actual program coverage and complete stage enumeration.

Read-only coordinates may be in program support as controls, but their restoration is a semantic obligation in `frame`. The contract imposes no phase-preservation axiom: delayed measurement phases need the recorded-program semantics and an additional phase-debt contract before walk integration. This first interface uses ordinary `Program` and is not yet the deferred-measurement walk interface.

## Intended stage permissions (not yet instantiated)

See [the concrete seed inventory](PAPER935_HOST_ACCOUNTING.md) for the 794 owned
addresses and the outstanding host-role binding. In particular, the table
below retains y during the first walk, whereas the concrete seed retains A;
the [explicit y/A placement permutation](PAPER935_HOST_RENAMING.md) now transports
the complete endpoint certificates between these layouts, including entry conditions
and retained output ownership. This is relabeling, not a data-moving caller stage.

| Stage | Host ownership and permitted reuse | Required release evidence |
|---|---|---|
| Input differences | x,y hold coordinate differences; A starts clean | Only proven zero temporary wires return to pool |
| Walk A | x and A pack the four integer/coefficient rows; y retained | Row shrinking and repacking must preserve values and clear released high wires |
| Endpoint seam | Form product in A, consume/recover y as specified, move surviving f/gv into y | Measurement phase debt and host cleaning explicitly tracked |
| Walk B and scale removal | Reverse history; halve A at active reverse steps | Old records and row storage restored or zeroed before release |
| Recompute and swap | Recompute to correct phase, erase temporary y, exchange y/A roles | No loan of y until its zero proof |
| Square and multiply | Temporarily loan clean A to arithmetic, then form A=x*y | Serial product workspace clean before reuse; multiplier pool unavailable during walks |
| Walk C, second seam, Walk D | Reuse x/y row hosts with A scaling; restore records | Same cleanliness and phase obligations as first walk pair |
| Final coordinate operations | Return x,y as output, clear ancillary storage | Full point-add value/phase specification and all workspace zero |

This table follows source commit `64b5a13aa249f1360846657392e6c66817b26d0f` in the author implementation; it is an implementation plan, not a Lean schedule instance. No stage may borrow the preserved coordinate merely because it has spare addresses.

## Capacity and failure obligations

The proposed author parameters (533 slots, 6-bit counter, deep-history capacity 60, depth threshold 5, freeze tests armed from slot 498) are not accepted correctness assumptions by this change. Packed-row overlap, counter overflow, history exhaustion and failure to freeze within the slot budget must be explicit failure events. Each call site must prove its success conditions or account for the event in an explicitly stated input distribution and failure budget. The allocator alone does not prove a probability bound. No sampled statistic is promoted to one, and no all-input theorem from the 4337-wire reference is transferred to this circuit.

## First concrete primitive

`rowAdd` implements the author's shared-carry (k=0) controlled ripple path: one carry wire, no row mask and no carry chain. For equal-width disjoint rows, `rowAdd_run` proves modular addition when controlled, unchanged target otherwise, restoration of source/control/carry, and phase preservation for every measurement tape. `rowAdd_signed` gives signed addition under explicit no-overflow bounds and clean input carry. Costs are 3n−2 Toffolis (zero at n=0), zero measurements, and support within two rows plus control and carry. The adaptive k>0 measured path is not implemented here.

The local workspace reduction is concrete; it is not a full-walk or full-point-add saving. Packed row views, deep history, counter/freeze policy, adaptive arithmetic, endpoint product, reverse scaling, full schedule and failure analysis remain outstanding.
