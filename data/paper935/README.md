# Pinned author parameters

`author-constants.json` is copied byte-for-byte from `tasks/modinv-point-add/circuits/divsteps/constants.json` in [andigu/uncompute, commit 64b5a13aa249f1360846657392e6c66817b26d0f](https://github.com/andigu/uncompute/tree/64b5a13aa249f1360846657392e6c66817b26d0f). Copyright Gu, Kemeny, Yelin and Lukin (2026), Apache-2.0. The retained license is [LICENSE-uncompute](../../ECDSAAdd/Math/Divsteps/LICENSE-uncompute).

The JSON is unmodified. The Lean translation and extraction script are new. The generated file records the SHA256 of the source bytes; `python3 scripts/paper935/generate_schedule.py --check` verifies exact reproducibility and is run by `scripts/verify.sh`.

These are sampled/fitted parameter tables. Importing them does not certify their claimed error budget or the safety of every trajectory.
