# Divsteps attribution

Adapted from https://github.com/andigu/uncompute/tree/64b5a13aa249f1360846657392e6c66817b26d0f/lean/divsteps (Gu, Kemeny, Yelin and Lukin, 2026), distributed under Apache-2.0. Its computational definitions and convex-hull proof follow Pieter Wuille's safegcd-bounds (MIT). The original license texts are retained alongside this file.

Changes: namespace/import paths adapted for ECDSAAdd and compatibility with Lean/Mathlib4.28.0. The checker uses structural insertion sort rather than merge sort, with its soundness proofs adapted accordingly. Additional exact-width and circuit proofs are identified separately. The native_decide certificate is deliberately not imported; generic termination theorems remain conditional on a checked certificate until a kernel-checked instance is provided. This mathematical development is not by itself a new complete point-addition submission.
