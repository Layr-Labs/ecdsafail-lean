# Editable entrant directory

The shipped `Main.lean` is the complete `Skywalk` reference entrant (`Baselines.normalizedSkywalk`). Replace it with declarations in namespace `ECDSAAdd.Entrant`:

- `entry : ECDSAAdd.Challenge.Entry`
- `bounds : ECDSAAdd.Challenge.Bounds`
- `certificate : ECDSAAdd.Challenge.Certificate entry bounds`

Import the protected `ECDSAAdd.Challenge.Contract`. Do not import `Judge`.
The shipped `Skywalk` reference certificate covers every public addend, with upper bounds of
2,217,386 Toffoli, 1,557,928 measurements, 1,899 distinct wires (including I/O),
and 47,000,000 total syntax slots (`4,210,816,014 Q×T`). An alternative certified baseline is
`ValueWalk` (`ECDSAAdd.Baselines.ValueWalkCertificate`: 6,286,806 Toffoli, 3,779,274 measurements,
3,134 distinct wires, 61,000,000 syntax slots, `19,702,850,004 Q×T`). The slot bound is conservative;
it is not the exact count from a particular addend.
Missing `Main`/`certificate` is rejected. All classical addends including infinity
are covered; the encoding and every non-I/O zero bit are fixed by the contract.
