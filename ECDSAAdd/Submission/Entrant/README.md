# Editable entrant directory

The shipped `Main.lean` is a complete ValueWalk reference entrant. Replace it with declarations in namespace `ECDSAAdd.Entrant`:

- `entry : ECDSAAdd.Challenge.Entry`
- `bounds : ECDSAAdd.Challenge.Bounds`
- `certificate : ECDSAAdd.Challenge.Certificate entry bounds`

Import the protected `ECDSAAdd.Challenge.Contract`. Do not import Judge.
The reference certificate covers every public addend, with upper bounds of
6,286,806 Toffoli, 3,779,274 measurements, 3,134 distinct wires (including I/O),
and 61,000,000 total syntax slots. The slot bound is conservative; it is not
the exact count from a particular addend.
Missing Main/certificate is rejected. All classical addends including infinity
are covered; the encoding and every non-I/O zero bit are fixed by the contract.
