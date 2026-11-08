import ECDSAAdd.Submission.Entrant.MainPart07Core

section
section

-- ===== Six505: six-tick forward window (tick 505 + ticks 506..510) =====
section

/-! Six-tick forward window (tick 505 + the Five506 window) re-synthesized jointly on the reachable
stage-505 domain: 31 Toffolis instead of 12 + 20. The history pack due after tick 505 moves after the
block: it only shares wire 520 with tick 505 and is disjoint from ticks 506..510. Scratch wires are
released pool-B wires 794..799, so no new wire is used. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.Six505
open Arithmetic MappedCompressed Secp256k1 History5

def tick505 : Program := [
  .CX 787 522,
  .CX 788 523,
  .CX 789 524,
  .CX 790 525,
  .CX 791 526,
  .CX 792 527,
  .CCX 521 522 787,
  .CCX 521 523 788,
  .CCX 521 524 789,
  .CCX 521 525 790,
  .CCX 521 526 791,
  .CCX 521 527 792,
  .CX 787 522,
  .CX 788 523,
  .CX 789 524,
  .CX 790 525,
  .CX 791 526,
  .CX 792 527,
  .CX 528 793,
  .measureX 528 [] [.CZ 520 793],
  .CX 793 528,
  .CX 528 793,
  .CX 792 793,
  .CX 792 528,
  .CX 521 786,
  .CX 528 529,
  .X 1549,
  .CX 528 1549,
  .CX 792 1549,
  .CX 1549 522,
  .CX 1549 523,
  .CX 1549 524,
  .CX 1549 525,
  .CX 1549 526,
  .CX 1549 527,
  .CX 1549 528,
  .CX 522 786,
  .CX 522 1549,
  .CCX 786 1549 1556,
  .CX 522 1556,
  .CX 522 1549,
  .CX 522 786,
  .CX 523 787,
  .CX 523 1556,
  .CCX 787 1556 1557,
  .CX 523 1557,
  .CX 523 1556,
  .CX 523 787,
  .CX 524 788,
  .CX 524 1557,
  .CCX 788 1557 1558,
  .CX 524 1558,
  .CX 524 1557,
  .CX 524 788,
  .CX 525 789,
  .CX 525 1558,
  .CCX 789 1558 1559,
  .CX 525 1559,
  .CX 525 1558,
  .CX 525 789,
  .CX 526 790,
  .CX 526 1559,
  .CCX 790 1559 1560,
  .CX 526 1560,
  .CX 526 1559,
  .CX 526 790,
  .CX 527 791,
  .CX 527 1560,
  .CCX 791 1560 1561,
  .CX 527 1561,
  .CX 527 1560,
  .CX 527 791,
  .CX 528 792,
  .CX 1561 792,
  .measureX 1561 [] [.CZ 527 791, .CZ 527 1560, .CZ 791 1560],
  .CX 527 791,
  .CX 1560 791,
  .measureX 1560 [] [.CZ 526 790, .CZ 526 1559, .CZ 790 1559],
  .CX 526 790,
  .CX 1559 790,
  .measureX 1559 [] [.CZ 525 789, .CZ 525 1558, .CZ 789 1558],
  .CX 525 789,
  .CX 1558 789,
  .measureX 1558 [] [.CZ 524 788, .CZ 524 1557, .CZ 788 1557],
  .CX 524 788,
  .CX 1557 788,
  .measureX 1557 [] [.CZ 523 787, .CZ 523 1556, .CZ 787 1556],
  .CX 523 787,
  .CX 1556 787,
  .measureX 1556 [] [.CZ 522 786, .CZ 522 1549, .CZ 786 1549],
  .CX 522 786,
  .CX 1549 786,
  .CX 1549 522,
  .CX 1549 523,
  .CX 1549 524,
  .CX 1549 525,
  .CX 1549 526,
  .CX 1549 527,
  .CX 1549 528,
  .X 1549,
  .CX 528 1549,
  .CX 792 1549,
  .CX 1549 793,
  .CX 520 521,
  .CX 528 529,
  .CX 792 793]

def block0 : Program := [
  .CX 787 522,
  .CCX 521 522 529,
  .CX 523 524,
  .CX 523 525,
  .CX 523 526,
  .CX 523 527,
  .CX 523 528,
  .CX 523 529,
  .CX 523 787,
  .CX 523 788,
  .CX 523 789,
  .CX 523 790,
  .CX 523 791,
  .CX 523 792,
  .CX 523 793,
  .measureX 523 [] [.Z 528, .Z 792, .Z 793, .CZ 520 527, .CZ 520 792],
  .CX 524 789,
  .CX 789 788,
  .CCX 786 788 524,
  .CX 788 525,
  .CX 789 525,
  .CX 790 525,
  .CCX 786 525 523,
  .CX 523 790,
  .measureX 523 [] [.Z 525, .CZ 521 525],
  .CX 788 526,
  .CX 789 526,
  .CX 791 526,
  .CCX 786 526 523,
  .CX 523 791,
  .measureX 523 [] [.Z 526, .CZ 521 526],
  .CX 792 528]

def block1 : Program := [
  .CX 529 522,
  .CX 787 522,
  .CCX 528 522 523,
  .CX 788 527,
  .CX 789 527,
  .CX 792 527,
  .CCX 786 527 1549,
  .CX 529 787,
  .CX 529 792,
  .CX 529 793,
  .CX 529 1549,
  .measureX 529 [] [.Z 527, .Z 1549, .CZ 521 527],
  .CX 792 793,
  .CX 792 1549,
  .CX 527 522,
  .CX 787 522,
  .CX 788 522,
  .CX 789 522,
  .CX 527 521,
  .CX 787 521,
  .CX 788 521,
  .CX 789 521,
  .CCX 522 521 792,
  .CX 522 792,
  .CX 521 522,
  .CX 521 523,
  .CX 521 787,
  .measureX 521 [] [.Z 523, .Z 528, .CZ 522 528, .CZ 528 786],
  .CX 786 523,
  .CX 792 527,
  .CX 1549 527,
  .CCX 523 527 521]

def block2 : Program := [
  .CX 527 524,
  .CX 528 524,
  .CX 786 524,
  .CX 787 524,
  .CX 788 524,
  .CX 792 524,
  .CX 793 524,
  .CX 1549 524,
  .CX 527 521,
  .CX 528 521,
  .CX 788 521,
  .CX 789 521,
  .CX 793 521,
  .CCX 524 521 529,
  .CX 528 524,
  .CX 786 524,
  .CX 787 524,
  .CX 789 524,
  .CX 790 524,
  .CX 529 527,
  .CX 788 527,
  .CX 792 527,
  .CX 793 527,
  .CX 1549 527,
  .CCX 524 527 1550,
  .CX 527 525,
  .CX 529 525,
  .CX 788 525,
  .CX 790 525,
  .CX 791 525,
  .CX 793 525,
  .CX 790 527]

def block3 : Program := [
  .CX 791 527,
  .CX 1550 527,
  .CCX 525 527 526,
  .CX 525 526,
  .CX 525 527,
  .CX 525 1550,
  .measureX 525 [] [.Z 521, .Z 527, .Z 528, .Z 529, .Z 789, .Z 790, .Z 791, .Z 793, .CZ 521 528, .CZ 521 786, .CZ 521 787, .CZ 521 793, .CZ 524 528, .CZ 524 529, .CZ 524 789],
  .CX 524 529,
  .CX 524 788,
  .CX 524 789,
  .measureX 524 [] [.Z 529, .CZ 521 528, .CZ 521 786, .CZ 521 787, .CZ 521 789, .CZ 521 790],
  .CX 526 788,
  .CX 526 790,
  .CX 526 791,
  .CX 526 1549,
  .measureX 526 [] [.Z 521, .Z 527, .Z 792, .Z 793, .Z 1549, .CZ 523 528, .CZ 523 788, .CZ 523 789, .CZ 523 792, .CZ 523 1549, .CZ 527 528, .CZ 527 786, .CZ 527 787],
  .CX 527 520,
  .CX 529 520,
  .CX 787 520,
  .CX 789 520,
  .CX 790 520,
  .CX 791 520,
  .CX 793 520,
  .CX 1550 520,
  .CX 788 529,
  .CX 790 529,
  .CX 791 529,
  .CX 1550 529,
  .CCX 520 529 524,
  .CX 787 522,
  .CX 788 522,
  .CX 789 522]

def block4 : Program := [
  .CX 792 522,
  .CX 1549 522,
  .CX 788 527,
  .CX 789 527,
  .CX 793 527,
  .CCX 522 527 525,
  .CX 527 528,
  .CX 527 529,
  .CX 527 788,
  .CX 527 789,
  .CX 527 793,
  .CX 527 1550,
  .measureX 527 [] [.Z 528, .Z 529, .CZ 528 786, .CZ 529 786, .CZ 786 793],
  .CX 788 789,
  .CX 788 790,
  .CX 788 1550,
  .CX 524 522,
  .CX 786 522,
  .CX 787 522,
  .CX 789 522,
  .CX 792 522,
  .CX 1549 522,
  .CX 528 521,
  .CX 529 521,
  .CX 789 521,
  .CX 790 521,
  .CX 791 521,
  .CX 793 521,
  .CX 1550 521,
  .CCX 522 521 788,
  .CX 790 791,
  .CX 524 522]

def block5 : Program := [
  .CX 789 529,
  .CCX 522 529 790,
  .CX 790 792,
  .CX 790 1549,
  .CX 524 523,
  .CX 528 523,
  .CX 529 523,
  .CX 792 523,
  .CX 1549 523,
  .CX 787 786,
  .CX 789 786,
  .CX 792 786,
  .CX 1549 786,
  .CCX 523 786 790,
  .CX 523 525,
  .CX 523 790,
  .measureX 523 [] [.Z 525, .CZ 522 528, .CZ 522 529, .CZ 522 789, .CZ 528 786, .CZ 529 786, .CZ 786 789],
  .CX 790 791,
  .CX 790 792,
  .CX 790 1549,
  .CX 790 1550,
  .CX 791 521,
  .CX 793 521,
  .CX 1550 521,
  .CCX 522 521 790,
  .CX 524 522,
  .CX 525 522,
  .CX 528 522,
  .CX 786 522,
  .CX 789 522,
  .CX 792 522,
  .CX 793 522]

def block6 : Program := [
  .CX 1549 522,
  .CX 525 521,
  .CX 528 521,
  .CX 790 521,
  .CX 792 521,
  .CX 1549 521,
  .CCX 522 521 523,
  .CX 522 523,
  .CX 786 528,
  .CX 788 528,
  .CX 789 528,
  .CX 791 528,
  .CX 792 528,
  .CX 793 528,
  .CX 1549 528,
  .CX 1550 528,
  .CX 523 522,
  .CX 525 522,
  .CX 789 522,
  .CX 790 522,
  .CX 792 522,
  .CX 793 522,
  .CX 1549 522,
  .CCX 528 522 526,
  .CX 522 524,
  .CX 522 528,
  .CX 522 787,
  .CX 522 789,
  .measureX 522 [] [.Z 520, .Z 524, .CZ 520 524, .CZ 520 528, .CZ 520 788, .CZ 520 791, .CZ 520 1550],
  .CX 523 528,
  .CX 523 788,
  .CX 523 790]

def block7 : Program := [
  .measureX 523 [] [.Z 520, .Z 524, .Z 528, .Z 529, .Z 786, .Z 788, .Z 789, .Z 790, .Z 791, .Z 793, .Z 1550, .CZ 520 524, .CZ 520 528, .CZ 520 788, .CZ 520 791, .CZ 520 1550, .CZ 521 524, .CZ 521 525, .CZ 521 528, .CZ 521 529, .CZ 521 786, .CZ 521 788, .CZ 521 789, .CZ 521 790, .CZ 521 791, .CZ 521 793, .CZ 521 1550, .CZ 524 525, .CZ 525 528, .CZ 525 788, .CZ 525 791, .CZ 525 1550],
  .CX 788 529,
  .CX 790 529,
  .CX 791 529,
  .CX 788 526,
  .CX 790 526,
  .CX 793 526,
  .CX 1550 526,
  .CCX 529 526 522,
  .CX 524 520,
  .CX 528 520,
  .CX 529 520,
  .CX 786 520,
  .CX 789 520,
  .CX 793 520,
  .CX 1550 520,
  .CX 526 522,
  .CX 529 522,
  .CX 788 522,
  .CX 790 522,
  .CX 791 522,
  .CCX 520 522 523,
  .CX 528 524,
  .CX 786 524,
  .CX 788 524,
  .CX 789 524,
  .CX 790 524,
  .CX 791 524,
  .CX 792 524,
  .CX 793 524,
  .CX 1549 524,
  .CX 1550 524]

def block8 : Program := [
  .CX 528 525,
  .CX 529 525,
  .CX 786 525,
  .CX 789 525,
  .CX 793 525,
  .CX 1550 525,
  .CCX 524 525 527,
  .CX 528 526,
  .CX 529 526,
  .CX 786 526,
  .CX 788 526,
  .CX 789 526,
  .CX 790 526,
  .CX 791 526,
  .CX 792 526,
  .CX 793 526,
  .CX 1549 526,
  .CX 1550 526,
  .CCX 524 526 1551,
  .CX 524 1551,
  .CX 524 521,
  .CX 525 521,
  .CX 528 521,
  .CX 529 521,
  .CX 786 521,
  .CX 790 521,
  .CX 792 521,
  .CX 1549 521,
  .CX 1550 521,
  .CX 525 522,
  .CX 528 522,
  .CX 788 522]

def block9 : Program := [
  .CX 791 522,
  .CX 1550 522,
  .CCX 521 522 1552,
  .CX 524 522,
  .CX 525 522,
  .CX 528 522,
  .CX 529 522,
  .CX 789 522,
  .CX 1550 522,
  .CX 528 527,
  .CX 529 527,
  .CX 786 527,
  .CX 788 527,
  .CX 790 527,
  .CX 791 527,
  .CX 792 527,
  .CX 1549 527,
  .CX 1552 527,
  .CCX 522 527 1553,
  .CX 527 521,
  .CX 524 522,
  .CX 525 522,
  .CX 527 522,
  .CX 528 522,
  .CX 529 522,
  .CX 789 522,
  .CX 1550 522,
  .CX 1553 522,
  .CCX 521 522 1554,
  .CX 521 1554,
  .CX 523 521,
  .CX 524 521]

def block10 : Program := [
  .CX 527 521,
  .CX 529 521,
  .CX 788 521,
  .CX 789 521,
  .CX 791 521,
  .CX 793 521,
  .CX 529 525,
  .CX 786 525,
  .CX 788 525,
  .CX 790 525,
  .CX 791 525,
  .CX 792 525,
  .CX 1549 525,
  .CX 1553 525,
  .CX 1554 525,
  .CCX 521 525 794,
  .CX 521 520,
  .CX 523 520,
  .CX 527 520,
  .CX 789 520,
  .CX 790 520,
  .CX 791 520,
  .CX 793 520,
  .CX 1549 520,
  .CX 522 521,
  .CX 523 521,
  .CX 524 521,
  .CX 525 521,
  .CX 526 521,
  .CX 527 521,
  .CX 788 521,
  .CX 790 521]

def block11 : Program := [
  .CX 793 521,
  .CX 1550 521,
  .CX 1551 521,
  .CX 1552 521,
  .CX 1553 521,
  .CX 794 521,
  .CCX 520 521 795,
  .CX 521 528,
  .CX 521 529,
  .CX 521 788,
  .CX 521 789,
  .CX 521 791,
  .CX 521 792,
  .CX 521 793,
  .CX 521 1550,
  .CX 521 1551,
  .measureX 521 [] [.Z 524, .Z 529, .Z 788, .Z 789, .Z 791, .Z 793, .Z 795, .CZ 520 524, .CZ 520 529, .CZ 520 788, .CZ 520 789, .CZ 520 791, .CZ 520 793],
  .CX 788 789,
  .CX 788 1549,
  .CX 788 1550,
  .measureX 788 [] [.Z 520, .Z 523, .Z 524, .Z 525, .Z 527, .Z 529, .Z 790, .Z 1550, .Z 1552, .Z 794, .CZ 520 522, .CZ 520 523, .CZ 520 526, .CZ 520 528, .CZ 520 790, .CZ 520 793, .CZ 520 1550, .CZ 520 1552, .CZ 520 1553, .CZ 522 524, .CZ 522 789, .CZ 522 791, .CZ 522 793, .CZ 522 1551, .CZ 522 795, .CZ 524 528, .CZ 524 786, .CZ 524 789, .CZ 524 792, .CZ 524 793, .CZ 524 1553, .CZ 524 795, .CZ 525 528, .CZ 525 786, .CZ 525 789, .CZ 525 790, .CZ 525 792, .CZ 525 1550, .CZ 525 1551, .CZ 526 528, .CZ 526 529, .CZ 527 528, .CZ 528 529, .CZ 529 790, .CZ 529 793, .CZ 529 1550, .CZ 786 789, .CZ 786 790, .CZ 789 791, .CZ 789 792, .CZ 790 791, .CZ 790 792],
  .CX 529 789,
  .CX 529 1549,
  .measureX 529 [] [.Z 522, .Z 527, .Z 791, .Z 793, .Z 1551, .Z 1552, .Z 1553, .Z 795, .CZ 520 522, .CZ 520 524, .CZ 520 525, .CZ 520 526, .CZ 520 789, .CZ 520 790, .CZ 520 1552, .CZ 520 1553, .CZ 520 1554, .CZ 522 524, .CZ 522 790, .CZ 522 791, .CZ 522 793, .CZ 522 1552, .CZ 522 1553, .CZ 524 527, .CZ 524 789, .CZ 524 791, .CZ 524 793, .CZ 525 526, .CZ 525 791, .CZ 525 1550, .CZ 525 1551, .CZ 526 528, .CZ 527 789, .CZ 527 790, .CZ 528 789, .CZ 528 790, .CZ 789 790, .CZ 789 791, .CZ 789 793, .CZ 789 1551, .CZ 789 1554, .CZ 789 795, .CZ 790 791, .CZ 790 793, .CZ 790 1551, .CZ 790 1554, .CZ 790 795],
  .CX 528 789,
  .CX 528 791,
  .CX 528 792,
  .measureX 528 [] [.Z 520, .Z 522, .Z 527, .Z 789, .Z 791, .Z 793, .Z 1551, .Z 1553, .Z 1554, .CZ 520 522, .CZ 520 524, .CZ 520 525, .CZ 520 789, .CZ 520 791, .CZ 520 793, .CZ 520 1552, .CZ 520 1553, .CZ 520 1554, .CZ 522 524, .CZ 522 525, .CZ 522 789, .CZ 522 791, .CZ 522 793, .CZ 522 1552, .CZ 522 1553, .CZ 524 525, .CZ 524 790, .CZ 524 793, .CZ 524 1550, .CZ 524 1553, .CZ 524 1554, .CZ 525 526, .CZ 525 789, .CZ 525 790, .CZ 525 791, .CZ 525 1550, .CZ 525 1551, .CZ 526 790, .CZ 526 793, .CZ 526 1550],
  .CX 525 789,
  .CX 525 791,
  .CX 525 792,
  .CX 525 1550]

def block12 : Program := [
  .CX 525 1551,
  .CX 525 1554,
  .CX 525 794,
  .measureX 525 [] [.Z 526, .Z 789, .Z 790, .Z 791, .Z 1550, .Z 1551, .Z 1552, .Z 1553, .Z 1554, .Z 794, .CZ 522 526, .CZ 522 789, .CZ 522 790, .CZ 522 791, .CZ 522 1550, .CZ 522 1551, .CZ 522 1552, .CZ 522 1553, .CZ 522 794],
  .CX 522 520,
  .CX 524 520,
  .CX 526 520,
  .CX 786 520,
  .CX 790 520,
  .CX 792 520,
  .CX 1551 520,
  .CX 794 520,
  .CX 793 790,
  .CX 1550 790,
  .CX 1551 790,
  .CX 1552 790,
  .CX 1553 790,
  .CX 1554 790,
  .CX 794 790,
  .CX 795 790,
  .CCX 520 790 521,
  .CX 520 521,
  .CX 793 527,
  .CX 1549 527,
  .CX 1550 527,
  .CX 1551 527,
  .CX 1552 527,
  .CX 1553 527,
  .CX 526 522,
  .CX 789 522,
  .CX 791 522,
  .CX 1549 522]

def block13 : Program := [
  .CX 1550 522,
  .CX 1551 522,
  .CX 1553 522,
  .CX 1554 522,
  .CX 795 522,
  .CCX 527 522 525,
  .CX 522 520,
  .CX 523 520,
  .CX 527 520,
  .CX 786 520,
  .CX 790 520,
  .CX 792 520,
  .CX 793 520,
  .CX 1550 520,
  .CX 1552 520,
  .CX 1554 520,
  .CX 794 520,
  .CX 524 523,
  .CX 525 523,
  .CX 789 523,
  .CX 791 523,
  .CX 793 523,
  .CX 1551 523,
  .CX 1552 523,
  .CX 1553 523,
  .CX 794 523,
  .CCX 520 523 528,
  .CX 527 528,
  .CX 527 787,
  .CX 527 792,
  .CX 527 793,
  .CX 527 1550]

def block14 : Program := [
  .CX 527 1551,
  .CX 527 1552,
  .CX 527 1553,
  .CX 527 794,
  .CX 527 795,
  .measureX 527 [] [.Z 528, .CZ 520 523],
  .CX 520 521,
  .CX 520 522,
  .CX 520 523,
  .CX 520 526,
  .CX 520 1552,
  .CX 520 1553,
  .CX 520 794,
  .CX 520 795,
  .measureX 520 [] [.Z 521, .Z 524, .Z 525, .Z 526, .Z 528, .Z 786, .Z 790, .Z 791, .Z 792, .Z 1552, .Z 1553, .Z 1554, .Z 794, .CZ 521 522, .CZ 521 523, .CZ 521 525, .CZ 521 786, .CZ 521 790, .CZ 521 791, .CZ 521 792, .CZ 521 793, .CZ 521 1549, .CZ 521 1550, .CZ 521 1553, .CZ 521 1554, .CZ 522 523, .CZ 522 525, .CZ 522 528, .CZ 522 793, .CZ 522 1549, .CZ 522 1550, .CZ 522 1553, .CZ 522 794, .CZ 523 524, .CZ 523 786, .CZ 523 789, .CZ 523 790, .CZ 523 792, .CZ 523 793, .CZ 523 1552, .CZ 523 1554, .CZ 523 794, .CZ 524 525, .CZ 524 526, .CZ 524 528, .CZ 524 790, .CZ 524 793, .CZ 524 1549, .CZ 524 1550, .CZ 524 1551, .CZ 524 1552, .CZ 524 1553, .CZ 525 526, .CZ 525 528, .CZ 525 793, .CZ 525 1549, .CZ 525 1550, .CZ 526 528, .CZ 526 790],
  .CX 521 526,
  .CX 521 787,
  .CX 521 789,
  .CX 521 791,
  .CX 521 792,
  .CX 521 793,
  .CX 521 1549,
  .measureX 521 [] [.Z 522, .Z 525, .Z 528, .Z 1554, .CZ 522 523, .CZ 522 789, .CZ 522 790, .CZ 522 1550, .CZ 522 1551, .CZ 522 1552, .CZ 522 1553, .CZ 522 794, .CZ 523 524, .CZ 523 528, .CZ 523 790, .CZ 523 1552, .CZ 523 794, .CZ 524 525, .CZ 524 526, .CZ 524 528, .CZ 524 786, .CZ 524 789, .CZ 524 790, .CZ 524 792, .CZ 524 1549, .CZ 524 1550, .CZ 524 1551, .CZ 525 791, .CZ 525 793, .CZ 525 1550, .CZ 526 528, .CZ 526 789, .CZ 526 791, .CZ 526 793, .CZ 526 1551, .CZ 526 1552, .CZ 526 1554, .CZ 526 794, .CZ 528 790, .CZ 528 1552],
  .CX 523 528,
  .CX 523 789,
  .CX 523 791,
  .CX 523 792,
  .CX 523 1550,
  .CX 523 1551,
  .measureX 523 [] [.Z 524, .Z 528, .Z 786, .Z 1551, .Z 1552, .Z 1554, .Z 794, .CZ 522 525, .CZ 522 793, .CZ 522 1549, .CZ 522 1551, .CZ 522 1554, .CZ 522 794, .CZ 524 526, .CZ 524 786, .CZ 524 789, .CZ 524 791, .CZ 524 1549, .CZ 524 1550, .CZ 524 1551, .CZ 524 1554, .CZ 524 794, .CZ 525 789, .CZ 525 791, .CZ 525 1549, .CZ 526 528, .CZ 526 786, .CZ 526 791, .CZ 526 792, .CZ 526 1553, .CZ 528 789, .CZ 528 790, .CZ 528 791, .CZ 528 1549, .CZ 528 1550, .CZ 528 1552, .CZ 528 1554, .CZ 786 789, .CZ 786 792, .CZ 786 1549, .CZ 786 1550, .CZ 789 791, .CZ 789 792, .CZ 789 1551, .CZ 789 1552, .CZ 789 1554, .CZ 790 791, .CZ 790 793],
  .CX 525 793,
  .CX 525 1551]

def block15 : Program := [
  .measureX 525 [] [.Z 528, .Z 789, .Z 790, .Z 791, .Z 793, .Z 1549, .Z 1551, .Z 1553, .CZ 522 526, .CZ 522 786, .CZ 522 789, .CZ 522 790, .CZ 522 792, .CZ 522 793, .CZ 522 1551, .CZ 522 1553, .CZ 522 1554, .CZ 524 526, .CZ 524 528, .CZ 524 786, .CZ 524 789, .CZ 524 790, .CZ 524 792, .CZ 524 793, .CZ 524 1551, .CZ 524 1552, .CZ 524 1553, .CZ 524 1554, .CZ 524 794, .CZ 526 528, .CZ 526 789, .CZ 526 791, .CZ 526 793, .CZ 526 1551, .CZ 526 1552, .CZ 526 1553, .CZ 526 1554, .CZ 526 794, .CZ 528 786, .CZ 528 790, .CZ 528 791, .CZ 528 792, .CZ 528 793, .CZ 528 1549, .CZ 528 1550, .CZ 528 1553, .CZ 528 1554, .CZ 528 794, .CZ 786 789, .CZ 786 790, .CZ 786 791, .CZ 786 793, .CZ 789 790, .CZ 789 791, .CZ 789 792, .CZ 790 791, .CZ 790 792, .CZ 790 793, .CZ 790 1549, .CZ 790 1552, .CZ 790 1553, .CZ 791 792, .CZ 791 793, .CZ 792 793],
  .CX 522 526,
  .CX 522 528,
  .CX 522 787,
  .CX 522 792,
  .CX 522 1550,
  .CX 522 1551,
  .CX 522 1552,
  .CX 522 1553,
  .CX 522 795,
  .measureX 522 [] [.Z 786, .Z 789, .Z 790, .Z 791, .Z 792, .Z 793, .Z 1550, .Z 1554, .Z 794, .CZ 524 526, .CZ 524 786, .CZ 524 790, .CZ 524 792, .CZ 524 1550, .CZ 524 1551, .CZ 524 1553, .CZ 524 1554, .CZ 526 793, .CZ 526 1549, .CZ 526 1550, .CZ 526 1553, .CZ 526 1554, .CZ 528 793, .CZ 528 1549, .CZ 528 1550, .CZ 528 1551, .CZ 528 1553, .CZ 528 1554, .CZ 528 794, .CZ 786 1549, .CZ 786 1550, .CZ 786 1551, .CZ 786 1554, .CZ 789 1551, .CZ 789 1552, .CZ 789 1554, .CZ 790 791, .CZ 790 793, .CZ 790 1549, .CZ 790 1554, .CZ 791 1549, .CZ 791 1550, .CZ 791 1552, .CZ 792 1549, .CZ 792 1550, .CZ 792 1551, .CZ 792 1554],
  .CX 526 528,
  .CX 526 789,
  .CX 526 791,
  .CX 526 792,
  .CX 526 793,
  .CX 526 1550,
  .CX 526 1551,
  .CX 526 1553,
  .CX 526 1554,
  .CX 526 795,
  .measureX 526 [] [.Z 524, .Z 528, .Z 793, .Z 1551, .Z 1552, .CZ 524 790, .CZ 524 791, .CZ 524 1550, .CZ 524 1551, .CZ 524 1552, .CZ 524 1553, .CZ 524 1554, .CZ 524 794, .CZ 528 786, .CZ 528 792, .CZ 528 1549, .CZ 528 1553, .CZ 528 794, .CZ 786 790, .CZ 786 793, .CZ 786 1552, .CZ 786 1554, .CZ 789 790, .CZ 789 791, .CZ 789 1549, .CZ 789 1552, .CZ 789 1554, .CZ 789 794, .CZ 790 791, .CZ 790 792, .CZ 790 793, .CZ 790 1550, .CZ 790 1551, .CZ 790 1552, .CZ 790 1553, .CZ 791 793, .CZ 791 1550, .CZ 791 1552, .CZ 791 1554, .CZ 791 794, .CZ 792 793, .CZ 792 1552, .CZ 792 1554, .CZ 793 1553, .CZ 793 794, .CZ 1549 1550, .CZ 1549 1551, .CZ 1549 1552, .CZ 1549 1553, .CZ 1549 1554, .CZ 1550 1551, .CZ 1550 1553],
  .CX 789 791,
  .CX 789 793,
  .CX 789 1549,
  .CX 789 1550,
  .CX 789 1551,
  .CX 789 794,
  .measureX 789 [] [.Z 524, .Z 528, .Z 786, .Z 791, .Z 793, .Z 1549, .Z 1553, .Z 1554, .CZ 524 786, .CZ 524 790, .CZ 524 791, .CZ 524 1550, .CZ 524 1552, .CZ 524 1553, .CZ 528 786, .CZ 528 792, .CZ 528 1549, .CZ 528 1550, .CZ 528 1551, .CZ 528 1552, .CZ 528 1554, .CZ 786 792, .CZ 786 793, .CZ 786 1549, .CZ 786 1550, .CZ 786 1553, .CZ 786 1554, .CZ 790 791, .CZ 790 1551, .CZ 790 1553, .CZ 791 793, .CZ 791 1551, .CZ 791 794, .CZ 792 793, .CZ 792 1553, .CZ 792 1554, .CZ 793 1550, .CZ 793 1551, .CZ 793 1552, .CZ 793 1553, .CZ 1549 1550, .CZ 1549 1551, .CZ 1549 794, .CZ 1550 1552, .CZ 1550 1553, .CZ 1550 794],
  .CX 528 787,
  .CX 528 793,
  .CX 528 1549]

def block16 : Program := [
  .CX 528 1550,
  .CX 528 1553,
  .CX 528 794,
  .CX 528 795,
  .measureX 528 [] [.Z 524, .Z 786, .Z 790, .Z 791, .Z 792, .Z 793, .Z 1550, .Z 1553, .Z 1554, .CZ 524 791, .CZ 524 793, .CZ 524 1549, .CZ 524 1551, .CZ 786 790, .CZ 786 791, .CZ 786 1552, .CZ 790 791, .CZ 790 792, .CZ 790 1549, .CZ 790 1551, .CZ 790 1552, .CZ 790 1553, .CZ 790 1554, .CZ 791 792, .CZ 791 793, .CZ 791 1549, .CZ 791 1550, .CZ 791 1553, .CZ 791 1554, .CZ 792 1552, .CZ 793 1549, .CZ 793 1550, .CZ 1549 1551, .CZ 1549 1553, .CZ 1550 1551, .CZ 1550 1553, .CZ 1552 1554, .CZ 1552 794],
  .CX 787 1549,
  .CX 787 1550,
  .CX 787 1551,
  .CX 787 1553,
  .CX 787 1554,
  .CX 787 794,
  .measureX 787 [] [.Z 524, .Z 792, .Z 793, .Z 1549, .Z 1551, .Z 1553, .CZ 524 786, .CZ 524 793, .CZ 524 1549, .CZ 524 1550, .CZ 524 1551, .CZ 524 1552, .CZ 524 1553, .CZ 786 790, .CZ 786 791, .CZ 786 792, .CZ 786 793, .CZ 786 1549, .CZ 786 1551, .CZ 786 1553, .CZ 786 794, .CZ 790 792, .CZ 790 793, .CZ 790 1550, .CZ 790 1551, .CZ 790 1553, .CZ 790 1554, .CZ 791 792, .CZ 791 793, .CZ 791 1550, .CZ 791 1552, .CZ 791 1553, .CZ 791 1554, .CZ 791 794, .CZ 792 793, .CZ 792 1550, .CZ 792 1551, .CZ 792 1553, .CZ 792 794, .CZ 793 1551, .CZ 793 1552, .CZ 793 1553, .CZ 1549 1553, .CZ 1549 1554, .CZ 1550 1551, .CZ 1550 1552, .CZ 1550 1553, .CZ 1551 794, .CZ 1552 1554, .CZ 1554 794],
  .CX 799 798,
  .CX 799 797,
  .CX 799 796,
  .CX 799 795,
  .CX 799 794,
  .CX 799 1551,
  .CX 799 793,
  .CX 799 790,
  .CX 799 789,
  .CX 799 787,
  .CX 799 527,
  .CX 799 525,
  .CX 799 524,
  .CX 799 523,
  .CX 799 520,
  .CX 798 799,
  .CX 798 797,
  .CX 798 796,
  .CX 798 795,
  .CX 798 794]

def block17 : Program := [
  .CX 798 1551,
  .CX 798 793,
  .CX 798 790,
  .CX 798 789,
  .CX 798 787,
  .CX 798 527,
  .CX 798 525,
  .CX 798 524,
  .CX 798 523,
  .CX 798 520,
  .CX 799 798,
  .CX 797 799,
  .CX 797 796,
  .CX 797 795,
  .CX 797 794,
  .CX 797 1551,
  .CX 797 793,
  .CX 797 790,
  .CX 797 789,
  .CX 797 787,
  .CX 797 527,
  .CX 797 525,
  .CX 797 524,
  .CX 797 523,
  .CX 797 520,
  .CX 799 797,
  .CX 796 799,
  .CX 796 795,
  .CX 796 794,
  .CX 796 1551,
  .CX 796 793,
  .CX 796 790]

def block18 : Program := [
  .CX 796 789,
  .CX 796 787,
  .CX 796 527,
  .CX 796 525,
  .CX 796 524,
  .CX 796 523,
  .CX 796 520,
  .CX 799 796,
  .CX 795 799,
  .CX 795 794,
  .CX 795 1551,
  .CX 795 793,
  .CX 795 790,
  .CX 795 789,
  .CX 795 787,
  .CX 795 527,
  .CX 795 525,
  .CX 795 524,
  .CX 795 523,
  .CX 795 520,
  .CX 799 795,
  .CX 794 799,
  .CX 794 1551,
  .CX 794 1550,
  .CX 794 1549,
  .CX 794 793,
  .CX 794 792,
  .CX 794 786,
  .CX 799 794,
  .CX 1554 799,
  .CX 1554 794,
  .CX 1554 1553]

def block19 : Program := [
  .CX 1554 793,
  .CX 1554 792,
  .CX 1554 789,
  .CX 1554 786,
  .CX 1554 527,
  .CX 1554 520,
  .CX 794 1554,
  .CX 1553 1554,
  .CX 1553 1549,
  .CX 1553 792,
  .CX 1553 791,
  .CX 1554 1553,
  .CX 1552 794,
  .CX 1552 1554,
  .CX 1552 1553,
  .CX 1552 1551,
  .CX 1552 1550,
  .CX 1552 789,
  .CX 1552 786,
  .CX 1552 527,
  .CX 1552 524,
  .CX 1552 523,
  .CX 1552 520,
  .CX 1553 1552,
  .CX 1551 1554,
  .CX 1551 1553,
  .CX 1551 1552,
  .CX 1551 793,
  .CX 1551 792,
  .CX 1551 791,
  .CX 1551 790,
  .CX 1551 787]

def block20 : Program := [
  .CX 1551 786,
  .CX 1551 525,
  .CX 1551 524,
  .CX 1551 523,
  .CX 1552 1551,
  .CX 1550 794,
  .CX 1550 1553,
  .CX 1550 793,
  .CX 1550 792,
  .CX 1550 791,
  .CX 1550 789,
  .CX 1550 527,
  .CX 1550 520,
  .CX 1553 1550,
  .CX 1549 1550,
  .CX 1549 793,
  .CX 1549 792,
  .CX 1549 791,
  .CX 1550 1549,
  .CX 793 799,
  .CX 793 794,
  .CX 793 1554,
  .CX 793 1550,
  .CX 793 1549,
  .CX 793 791,
  .CX 793 790,
  .CX 793 789,
  .CX 793 788,
  .CX 793 527,
  .CX 793 526,
  .CX 793 524,
  .CX 793 523]

def block21 : Program := [
  .CX 793 520,
  .CX 792 799,
  .CX 792 794,
  .CX 792 1554,
  .CX 792 1553,
  .CX 792 1552,
  .CX 792 791,
  .CX 792 789,
  .CX 792 786,
  .CX 792 527,
  .CX 792 520,
  .CX 1552 792,
  .CX 791 799,
  .CX 791 1554,
  .CX 791 1553,
  .CX 791 1552,
  .CX 791 1550,
  .CX 791 793,
  .CX 791 790,
  .CX 791 788,
  .CX 791 786,
  .CX 791 529,
  .CX 791 526,
  .CX 791 524,
  .CX 791 522,
  .CX 790 1550,
  .CX 790 793,
  .CX 790 791,
  .CX 790 788,
  .CX 790 786,
  .CX 790 529,
  .CX 790 528]

def block22 : Program := [
  .CX 790 526,
  .CX 790 524,
  .CX 790 522,
  .CX 790 521,
  .CX 789 794,
  .CX 794 789,
  .CX 788 793,
  .CX 793 788,
  .CX 787 792,
  .CX 792 787,
  .CX 786 799,
  .CX 786 1553,
  .CX 786 1550,
  .CX 786 1549,
  .CX 1549 786,
  .CX 529 791,
  .CX 791 529,
  .CX 528 790,
  .CX 790 528,
  .CX 527 789,
  .CX 789 527,
  .CX 526 788,
  .CX 788 526,
  .CX 525 787,
  .CX 787 525,
  .CX 524 1554,
  .CX 524 1553,
  .CX 524 1550,
  .CX 524 1549,
  .CX 524 529,
  .CX 524 522,
  .CX 529 524]

def block23 : Program := [
  .CX 523 786,
  .CX 786 523,
  .CX 522 529,
  .CX 529 522,
  .CX 521 528,
  .CX 528 521,
  .CX 520 527,
  .CX 527 520,
  .X 799,
  .CX 526 527,
  .X 527,
  .CX 526 786]

def cand6 : Program := block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20 ++ block21 ++ block22 ++ block23

def sites : List Wire := [520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 1549, 1550, 1551, 1552, 1553, 1554, 1556, 1557, 1558, 1559, 1560, 1561]

def rows0 : List (Bool × Bool × Nat × Nat) := [(false, false, 0, 1), (false, false, 1, 1), (false, false, 2, 1), (false, false, 3, 1), (false, false, 4, 1), (false, false, 5, 1), (false, false, 6, 1), (false, false, 7, 1), (false, false, 8, 1), (false, false, 9, 1), (false, false, 10, 1), (false, false, 11, 1), (false, false, 12, 1), (false, false, 13, 1), (false, false, 14, 1), (false, false, 15, 1), (false, false, 16, 1), (false, false, 17, 1), (false, false, 18, 1), (false, false, 19, 1), (false, false, 20, 1), (false, false, 21, 1), (false, false, 22, 1), (false, false, 23, 1), (false, false, 24, 1), (false, false, 25, 1), (false, false, 26, 1), (false, false, 27, 1), (false, false, 28, 1), (false, false, 29, 1), (false, false, 30, 1), (false, false, 31, 1), (false, false, 32, 1), (false, false, 33, 1), (false, false, 34, 1), (false, false, 35, 1), (false, false, 36, 1), (false, false, 37, 1), (false, false, 38, 1), (false, false, 39, 1)]
def rows1 : List (Bool × Bool × Nat × Nat) := [(false, false, 40, 1), (false, false, 41, 1), (false, false, 42, 1), (false, false, 43, 1), (false, false, 44, 1), (false, false, 45, 1), (false, false, 46, 1), (false, false, 47, 1), (false, false, 48, 1), (false, false, 49, 1), (false, false, 50, 1), (false, false, 51, 1), (false, false, 52, 1), (false, false, 53, 1), (false, false, 54, 1), (false, false, 55, 1), (false, false, 56, 1), (false, false, 57, 1), (false, false, 58, 1), (false, false, 59, 1), (false, false, 60, 1), (false, false, 61, 1), (false, false, 62, 1), (false, false, 63, 1), (false, false, 1, 3), (false, false, 2, 3), (false, false, 4, 3), (false, false, 5, 3), (false, false, 7, 3), (false, false, 8, 3), (false, false, 10, 3), (false, false, 11, 3), (false, false, 13, 3), (false, false, 14, 3), (false, false, 16, 3), (false, false, 17, 3), (false, false, 19, 3), (false, false, 20, 3), (false, false, 22, 3), (false, false, 23, 3)]
def rows2 : List (Bool × Bool × Nat × Nat) := [(false, false, 25, 3), (false, false, 26, 3), (false, false, 28, 3), (false, false, 29, 3), (false, false, 31, 3), (false, false, 1, 5), (false, false, 2, 5), (false, false, 3, 5), (false, false, 4, 5), (false, false, 6, 5), (false, false, 7, 5), (false, false, 8, 5), (false, false, 9, 5), (false, false, 11, 5), (false, false, 12, 5), (false, false, 13, 5), (false, false, 14, 5), (false, false, 17, 5), (false, false, 19, 5), (false, false, 1, 7), (false, false, 2, 7), (false, false, 3, 7), (false, false, 4, 7), (false, false, 5, 7), (false, false, 6, 7), (false, false, 8, 7), (false, false, 9, 7), (false, false, 10, 7), (false, false, 11, 7), (false, false, 12, 7), (false, false, 13, 7), (false, false, 15, 7), (false, false, 17, 7), (false, false, 19, 7), (false, false, 1, 9), (false, false, 2, 9), (false, false, 4, 9), (false, false, 5, 9), (false, false, 7, 9), (false, false, 11, 9)]
def rows3 : List (Bool × Bool × Nat × Nat) := [(false, false, 13, 9), (false, false, 1, 11), (false, false, 2, 11), (false, false, 3, 11), (false, false, 4, 11), (false, false, 5, 11), (false, false, 6, 11), (false, false, 7, 11), (false, false, 9, 11), (false, false, 13, 11), (false, false, 15, 11), (false, false, 17, 11), (false, false, 1, 13), (false, false, 2, 13), (false, false, 3, 13), (false, false, 4, 13), (false, false, 5, 13), (false, false, 6, 13), (false, false, 7, 13), (false, false, 9, 13), (false, false, 11, 13), (false, false, 15, 13), (false, false, 17, 13), (false, false, 19, 13), (false, false, 1, 15), (false, false, 2, 15), (false, false, 4, 15), (false, false, 7, 15), (false, false, 11, 15), (false, false, 13, 15), (false, false, 17, 15), (false, false, 19, 15), (false, false, 1, 17), (false, false, 2, 17), (false, false, 3, 17), (false, false, 5, 17), (false, false, 7, 17), (false, false, 11, 17), (false, false, 13, 17), (false, false, 15, 17)]
def rows4 : List (Bool × Bool × Nat × Nat) := [(false, false, 19, 17), (false, false, 1, 19), (false, false, 2, 19), (false, false, 3, 19), (false, false, 5, 19), (false, false, 7, 19), (false, false, 13, 19), (false, false, 15, 19), (false, false, 17, 19), (false, false, 21, 19), (false, false, 1, 21), (false, false, 2, 21), (false, false, 19, 21), (false, false, 23, 21), (false, false, 1, 23), (false, false, 2, 23), (false, false, 3, 23), (false, false, 21, 23), (false, false, 25, 23), (false, false, 1, 25), (false, false, 2, 25), (false, false, 3, 25), (false, false, 23, 25), (false, false, 27, 25), (false, false, 1, 27), (false, false, 2, 27), (false, false, 25, 27), (false, false, 29, 27), (false, false, 1, 29), (false, false, 2, 29), (false, false, 3, 29), (false, false, 27, 29), (false, false, 31, 29), (false, false, 1, 31), (false, false, 2, 31), (false, false, 3, 31), (false, false, 29, 31), (false, false, 33, 31), (false, false, 1, 33), (false, false, 31, 33)]
def rows5 : List (Bool × Bool × Nat × Nat) := [(false, false, 1, 35), (false, false, 1, 37), (false, false, 1, 39), (false, false, 1, 41), (false, false, 1, 43), (false, false, 1, 45), (false, false, 1, 47), (false, false, 1, 49), (false, false, 1, 51), (false, false, 1, 53), (false, false, 1, 55), (false, false, 1, 57), (false, false, 1, 59), (false, false, 1, 61), (false, false, 1, 63), (false, true, 0, 1), (false, true, 1, 1), (false, true, 2, 1), (false, true, 3, 1), (false, true, 4, 1), (false, true, 5, 1), (false, true, 6, 1), (false, true, 7, 1), (false, true, 8, 1), (false, true, 9, 1), (false, true, 10, 1), (false, true, 11, 1), (false, true, 12, 1), (false, true, 13, 1), (false, true, 14, 1), (false, true, 15, 1), (false, true, 16, 1), (false, true, 17, 1), (false, true, 18, 1), (false, true, 19, 1), (false, true, 20, 1), (false, true, 21, 1), (false, true, 22, 1), (false, true, 23, 1), (false, true, 24, 1)]
def rows6 : List (Bool × Bool × Nat × Nat) := [(false, true, 25, 1), (false, true, 26, 1), (false, true, 27, 1), (false, true, 28, 1), (false, true, 29, 1), (false, true, 30, 1), (false, true, 31, 1), (false, true, 32, 1), (false, true, 33, 1), (false, true, 34, 1), (false, true, 35, 1), (false, true, 36, 1), (false, true, 37, 1), (false, true, 38, 1), (false, true, 39, 1), (false, true, 40, 1), (false, true, 41, 1), (false, true, 42, 1), (false, true, 43, 1), (false, true, 44, 1), (false, true, 45, 1), (false, true, 46, 1), (false, true, 47, 1), (false, true, 48, 1), (false, true, 49, 1), (false, true, 50, 1), (false, true, 51, 1), (false, true, 52, 1), (false, true, 53, 1), (false, true, 54, 1), (false, true, 55, 1), (false, true, 56, 1), (false, true, 57, 1), (false, true, 58, 1), (false, true, 59, 1), (false, true, 60, 1), (false, true, 61, 1), (false, true, 62, 1), (false, true, 63, 1), (false, true, 1, 3)]
def rows7 : List (Bool × Bool × Nat × Nat) := [(false, true, 2, 3), (false, true, 4, 3), (false, true, 5, 3), (false, true, 7, 3), (false, true, 8, 3), (false, true, 10, 3), (false, true, 11, 3), (false, true, 13, 3), (false, true, 14, 3), (false, true, 16, 3), (false, true, 17, 3), (false, true, 19, 3), (false, true, 20, 3), (false, true, 22, 3), (false, true, 23, 3), (false, true, 25, 3), (false, true, 26, 3), (false, true, 28, 3), (false, true, 29, 3), (false, true, 31, 3), (false, true, 1, 5), (false, true, 2, 5), (false, true, 3, 5), (false, true, 4, 5), (false, true, 6, 5), (false, true, 7, 5), (false, true, 8, 5), (false, true, 9, 5), (false, true, 11, 5), (false, true, 12, 5), (false, true, 13, 5), (false, true, 14, 5), (false, true, 17, 5), (false, true, 19, 5), (false, true, 1, 7), (false, true, 2, 7), (false, true, 3, 7), (false, true, 4, 7), (false, true, 5, 7), (false, true, 6, 7)]
def rows8 : List (Bool × Bool × Nat × Nat) := [(false, true, 8, 7), (false, true, 9, 7), (false, true, 10, 7), (false, true, 11, 7), (false, true, 12, 7), (false, true, 13, 7), (false, true, 15, 7), (false, true, 17, 7), (false, true, 19, 7), (false, true, 1, 9), (false, true, 2, 9), (false, true, 4, 9), (false, true, 5, 9), (false, true, 7, 9), (false, true, 11, 9), (false, true, 13, 9), (false, true, 1, 11), (false, true, 2, 11), (false, true, 3, 11), (false, true, 4, 11), (false, true, 5, 11), (false, true, 6, 11), (false, true, 7, 11), (false, true, 9, 11), (false, true, 13, 11), (false, true, 15, 11), (false, true, 17, 11), (false, true, 1, 13), (false, true, 2, 13), (false, true, 3, 13), (false, true, 4, 13), (false, true, 5, 13), (false, true, 6, 13), (false, true, 7, 13), (false, true, 9, 13), (false, true, 11, 13), (false, true, 15, 13), (false, true, 17, 13), (false, true, 19, 13), (false, true, 1, 15)]
def rows9 : List (Bool × Bool × Nat × Nat) := [(false, true, 2, 15), (false, true, 4, 15), (false, true, 7, 15), (false, true, 11, 15), (false, true, 13, 15), (false, true, 17, 15), (false, true, 19, 15), (false, true, 1, 17), (false, true, 2, 17), (false, true, 3, 17), (false, true, 5, 17), (false, true, 7, 17), (false, true, 11, 17), (false, true, 13, 17), (false, true, 15, 17), (false, true, 19, 17), (false, true, 1, 19), (false, true, 2, 19), (false, true, 3, 19), (false, true, 5, 19), (false, true, 7, 19), (false, true, 13, 19), (false, true, 15, 19), (false, true, 17, 19), (false, true, 21, 19), (false, true, 1, 21), (false, true, 2, 21), (false, true, 19, 21), (false, true, 23, 21), (false, true, 1, 23), (false, true, 2, 23), (false, true, 3, 23), (false, true, 21, 23), (false, true, 25, 23), (false, true, 1, 25), (false, true, 2, 25), (false, true, 3, 25), (false, true, 23, 25), (false, true, 27, 25), (false, true, 1, 27)]
def rows10 : List (Bool × Bool × Nat × Nat) := [(false, true, 2, 27), (false, true, 25, 27), (false, true, 29, 27), (false, true, 1, 29), (false, true, 2, 29), (false, true, 3, 29), (false, true, 27, 29), (false, true, 31, 29), (false, true, 1, 31), (false, true, 2, 31), (false, true, 3, 31), (false, true, 29, 31), (false, true, 33, 31), (false, true, 1, 33), (false, true, 31, 33), (false, true, 1, 35), (false, true, 1, 37), (false, true, 1, 39), (false, true, 1, 41), (false, true, 1, 43), (false, true, 1, 45), (false, true, 1, 47), (false, true, 1, 49), (false, true, 1, 51), (false, true, 1, 53), (false, true, 1, 55), (false, true, 1, 57), (false, true, 1, 59), (false, true, 1, 61), (false, true, 1, 63), (true, false, 0, 1), (true, false, 1, 1), (true, false, 2, 1), (true, false, 3, 1), (true, false, 4, 1), (true, false, 5, 1), (true, false, 6, 1), (true, false, 7, 1), (true, false, 8, 1), (true, false, 9, 1)]
def rows11 : List (Bool × Bool × Nat × Nat) := [(true, false, 10, 1), (true, false, 11, 1), (true, false, 12, 1), (true, false, 13, 1), (true, false, 14, 1), (true, false, 15, 1), (true, false, 16, 1), (true, false, 17, 1), (true, false, 18, 1), (true, false, 19, 1), (true, false, 20, 1), (true, false, 21, 1), (true, false, 22, 1), (true, false, 23, 1), (true, false, 24, 1), (true, false, 25, 1), (true, false, 26, 1), (true, false, 27, 1), (true, false, 28, 1), (true, false, 29, 1), (true, false, 30, 1), (true, false, 31, 1), (true, false, 32, 1), (true, false, 33, 1), (true, false, 34, 1), (true, false, 35, 1), (true, false, 36, 1), (true, false, 37, 1), (true, false, 38, 1), (true, false, 39, 1), (true, false, 40, 1), (true, false, 41, 1), (true, false, 42, 1), (true, false, 43, 1), (true, false, 44, 1), (true, false, 45, 1), (true, false, 46, 1), (true, false, 47, 1), (true, false, 48, 1), (true, false, 49, 1)]
def rows12 : List (Bool × Bool × Nat × Nat) := [(true, false, 50, 1), (true, false, 51, 1), (true, false, 52, 1), (true, false, 53, 1), (true, false, 54, 1), (true, false, 55, 1), (true, false, 56, 1), (true, false, 57, 1), (true, false, 58, 1), (true, false, 59, 1), (true, false, 60, 1), (true, false, 61, 1), (true, false, 62, 1), (true, false, 63, 1), (true, false, 1, 3), (true, false, 2, 3), (true, false, 4, 3), (true, false, 5, 3), (true, false, 7, 3), (true, false, 8, 3), (true, false, 10, 3), (true, false, 11, 3), (true, false, 13, 3), (true, false, 14, 3), (true, false, 16, 3), (true, false, 17, 3), (true, false, 19, 3), (true, false, 20, 3), (true, false, 22, 3), (true, false, 23, 3), (true, false, 25, 3), (true, false, 26, 3), (true, false, 28, 3), (true, false, 29, 3), (true, false, 31, 3), (true, false, 1, 5), (true, false, 2, 5), (true, false, 3, 5), (true, false, 4, 5), (true, false, 6, 5)]
def rows13 : List (Bool × Bool × Nat × Nat) := [(true, false, 7, 5), (true, false, 8, 5), (true, false, 9, 5), (true, false, 11, 5), (true, false, 12, 5), (true, false, 13, 5), (true, false, 14, 5), (true, false, 17, 5), (true, false, 19, 5), (true, false, 1, 7), (true, false, 2, 7), (true, false, 3, 7), (true, false, 4, 7), (true, false, 5, 7), (true, false, 6, 7), (true, false, 8, 7), (true, false, 9, 7), (true, false, 10, 7), (true, false, 11, 7), (true, false, 12, 7), (true, false, 13, 7), (true, false, 15, 7), (true, false, 17, 7), (true, false, 19, 7), (true, false, 1, 9), (true, false, 2, 9), (true, false, 4, 9), (true, false, 5, 9), (true, false, 7, 9), (true, false, 11, 9), (true, false, 13, 9), (true, false, 1, 11), (true, false, 2, 11), (true, false, 3, 11), (true, false, 4, 11), (true, false, 5, 11), (true, false, 6, 11), (true, false, 7, 11), (true, false, 9, 11), (true, false, 13, 11)]
def rows14 : List (Bool × Bool × Nat × Nat) := [(true, false, 15, 11), (true, false, 17, 11), (true, false, 1, 13), (true, false, 2, 13), (true, false, 3, 13), (true, false, 4, 13), (true, false, 5, 13), (true, false, 6, 13), (true, false, 7, 13), (true, false, 9, 13), (true, false, 11, 13), (true, false, 15, 13), (true, false, 17, 13), (true, false, 19, 13), (true, false, 1, 15), (true, false, 2, 15), (true, false, 4, 15), (true, false, 7, 15), (true, false, 11, 15), (true, false, 13, 15), (true, false, 17, 15), (true, false, 19, 15), (true, false, 1, 17), (true, false, 2, 17), (true, false, 3, 17), (true, false, 5, 17), (true, false, 7, 17), (true, false, 11, 17), (true, false, 13, 17), (true, false, 15, 17), (true, false, 19, 17), (true, false, 1, 19), (true, false, 2, 19), (true, false, 3, 19), (true, false, 5, 19), (true, false, 7, 19), (true, false, 13, 19), (true, false, 15, 19), (true, false, 17, 19), (true, false, 21, 19)]
def rows15 : List (Bool × Bool × Nat × Nat) := [(true, false, 1, 21), (true, false, 2, 21), (true, false, 19, 21), (true, false, 23, 21), (true, false, 1, 23), (true, false, 2, 23), (true, false, 3, 23), (true, false, 21, 23), (true, false, 25, 23), (true, false, 1, 25), (true, false, 2, 25), (true, false, 3, 25), (true, false, 23, 25), (true, false, 27, 25), (true, false, 1, 27), (true, false, 2, 27), (true, false, 25, 27), (true, false, 29, 27), (true, false, 1, 29), (true, false, 2, 29), (true, false, 3, 29), (true, false, 27, 29), (true, false, 31, 29), (true, false, 1, 31), (true, false, 2, 31), (true, false, 3, 31), (true, false, 29, 31), (true, false, 33, 31), (true, false, 1, 33), (true, false, 31, 33), (true, false, 1, 35), (true, false, 1, 37), (true, false, 1, 39), (true, false, 1, 41), (true, false, 1, 43), (true, false, 1, 45), (true, false, 1, 47), (true, false, 1, 49), (true, false, 1, 51), (true, false, 1, 53)]
def rows16 : List (Bool × Bool × Nat × Nat) := [(true, false, 1, 55), (true, false, 1, 57), (true, false, 1, 59), (true, false, 1, 61), (true, false, 1, 63), (true, true, 0, 1), (true, true, 1, 1), (true, true, 2, 1), (true, true, 3, 1), (true, true, 4, 1), (true, true, 5, 1), (true, true, 6, 1), (true, true, 7, 1), (true, true, 8, 1), (true, true, 9, 1), (true, true, 10, 1), (true, true, 11, 1), (true, true, 12, 1), (true, true, 13, 1), (true, true, 14, 1), (true, true, 15, 1), (true, true, 16, 1), (true, true, 17, 1), (true, true, 18, 1), (true, true, 19, 1), (true, true, 20, 1), (true, true, 21, 1), (true, true, 22, 1), (true, true, 23, 1), (true, true, 24, 1), (true, true, 25, 1), (true, true, 26, 1), (true, true, 27, 1), (true, true, 28, 1), (true, true, 29, 1), (true, true, 30, 1), (true, true, 31, 1), (true, true, 32, 1), (true, true, 33, 1), (true, true, 34, 1)]
def rows17 : List (Bool × Bool × Nat × Nat) := [(true, true, 35, 1), (true, true, 36, 1), (true, true, 37, 1), (true, true, 38, 1), (true, true, 39, 1), (true, true, 40, 1), (true, true, 41, 1), (true, true, 42, 1), (true, true, 43, 1), (true, true, 44, 1), (true, true, 45, 1), (true, true, 46, 1), (true, true, 47, 1), (true, true, 48, 1), (true, true, 49, 1), (true, true, 50, 1), (true, true, 51, 1), (true, true, 52, 1), (true, true, 53, 1), (true, true, 54, 1), (true, true, 55, 1), (true, true, 56, 1), (true, true, 57, 1), (true, true, 58, 1), (true, true, 59, 1), (true, true, 60, 1), (true, true, 61, 1), (true, true, 62, 1), (true, true, 63, 1), (true, true, 1, 3), (true, true, 2, 3), (true, true, 4, 3), (true, true, 5, 3), (true, true, 7, 3), (true, true, 8, 3), (true, true, 10, 3), (true, true, 11, 3), (true, true, 13, 3), (true, true, 14, 3), (true, true, 16, 3)]
def rows18 : List (Bool × Bool × Nat × Nat) := [(true, true, 17, 3), (true, true, 19, 3), (true, true, 20, 3), (true, true, 22, 3), (true, true, 23, 3), (true, true, 25, 3), (true, true, 26, 3), (true, true, 28, 3), (true, true, 29, 3), (true, true, 31, 3), (true, true, 1, 5), (true, true, 2, 5), (true, true, 3, 5), (true, true, 4, 5), (true, true, 6, 5), (true, true, 7, 5), (true, true, 8, 5), (true, true, 9, 5), (true, true, 11, 5), (true, true, 12, 5), (true, true, 13, 5), (true, true, 14, 5), (true, true, 17, 5), (true, true, 19, 5), (true, true, 1, 7), (true, true, 2, 7), (true, true, 3, 7), (true, true, 4, 7), (true, true, 5, 7), (true, true, 6, 7), (true, true, 8, 7), (true, true, 9, 7), (true, true, 10, 7), (true, true, 11, 7), (true, true, 12, 7), (true, true, 13, 7), (true, true, 15, 7), (true, true, 17, 7), (true, true, 19, 7), (true, true, 1, 9)]
def rows19 : List (Bool × Bool × Nat × Nat) := [(true, true, 2, 9), (true, true, 4, 9), (true, true, 5, 9), (true, true, 7, 9), (true, true, 11, 9), (true, true, 13, 9), (true, true, 1, 11), (true, true, 2, 11), (true, true, 3, 11), (true, true, 4, 11), (true, true, 5, 11), (true, true, 6, 11), (true, true, 7, 11), (true, true, 9, 11), (true, true, 13, 11), (true, true, 15, 11), (true, true, 17, 11), (true, true, 1, 13), (true, true, 2, 13), (true, true, 3, 13), (true, true, 4, 13), (true, true, 5, 13), (true, true, 6, 13), (true, true, 7, 13), (true, true, 9, 13), (true, true, 11, 13), (true, true, 15, 13), (true, true, 17, 13), (true, true, 19, 13), (true, true, 1, 15), (true, true, 2, 15), (true, true, 4, 15), (true, true, 7, 15), (true, true, 11, 15), (true, true, 13, 15), (true, true, 17, 15), (true, true, 19, 15), (true, true, 1, 17), (true, true, 2, 17), (true, true, 3, 17)]
def rows20 : List (Bool × Bool × Nat × Nat) := [(true, true, 5, 17), (true, true, 7, 17), (true, true, 11, 17), (true, true, 13, 17), (true, true, 15, 17), (true, true, 19, 17), (true, true, 1, 19), (true, true, 2, 19), (true, true, 3, 19), (true, true, 5, 19), (true, true, 7, 19), (true, true, 13, 19), (true, true, 15, 19), (true, true, 17, 19), (true, true, 21, 19), (true, true, 1, 21), (true, true, 2, 21), (true, true, 19, 21), (true, true, 23, 21), (true, true, 1, 23), (true, true, 2, 23), (true, true, 3, 23), (true, true, 21, 23), (true, true, 25, 23), (true, true, 1, 25), (true, true, 2, 25), (true, true, 3, 25), (true, true, 23, 25), (true, true, 27, 25), (true, true, 1, 27), (true, true, 2, 27), (true, true, 25, 27), (true, true, 29, 27), (true, true, 1, 29), (true, true, 2, 29), (true, true, 3, 29), (true, true, 27, 29), (true, true, 31, 29), (true, true, 1, 31), (true, true, 2, 31)]
def rows21 : List (Bool × Bool × Nat × Nat) := [(true, true, 3, 31), (true, true, 29, 31), (true, true, 33, 31), (true, true, 1, 33), (true, true, 31, 33), (true, true, 1, 35), (true, true, 1, 37), (true, true, 1, 39), (true, true, 1, 41), (true, true, 1, 43), (true, true, 1, 45), (true, true, 1, 47), (true, true, 1, 49), (true, true, 1, 51), (true, true, 1, 53), (true, true, 1, 55), (true, true, 1, 57), (true, true, 1, 59), (true, true, 1, 61), (true, true, 1, 63)]
def rows : List (Bool × Bool × Nat × Nat) := rows0 ++ rows1 ++ rows2 ++ rows3 ++ rows4 ++ rows5 ++ rows6 ++ rows7 ++ rows8 ++ rows9 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21

def pre505 (g s : Bool) (u v : Nat) : BasisState := fun q =>
  if q = 520 then g
  else if q = 521 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 1 % 2 = 1)
  else if q = 522 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 2 % 2 = 1)
  else if q = 523 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 4 % 2 = 1)
  else if q = 524 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 8 % 2 = 1)
  else if q = 525 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 16 % 2 = 1)
  else if q = 526 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 32 % 2 = 1)
  else if q = 527 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 64 % 2 = 1)
  else if q = 528 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a < 0)
  else if q = 786 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 1 % 2 = 1)
  else if q = 787 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 2 % 2 = 1)
  else if q = 788 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 4 % 2 = 1)
  else if q = 789 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 8 % 2 = 1)
  else if q = 790 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 16 % 2 = 1)
  else if q = 791 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 32 % 2 = 1)
  else if q = 792 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 64 % 2 = 1)
  else if q = 793 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b < 0)
  else false

theorem explicit505 : W.repairedTick base 505 = tick505 := by decide +kernel

def ref : Program := tick505 ++ Five506.cand
def enc (r : Bool × Bool × Nat × Nat) : Nat := encN_t8 (pre505 r.1 r.2.1 r.2.2.1 r.2.2.2) sites
def checkRow (r : Bool × Bool × Nat × Nat) : Bool := agree508 cand6 ref (enc r)

open ECDSAAdd.Entrant.CodecBitSliceVerify
def candidate : Program := [
  .CX 11 2,
  .CCX 1 2 9,
  .CX 3 4,
  .CX 3 5,
  .CX 3 6,
  .CX 3 7,
  .CX 3 8,
  .CX 3 9,
  .CX 3 11,
  .CX 3 12,
  .CX 3 13,
  .CX 3 14,
  .CX 3 15,
  .CX 3 16,
  .CX 3 17,
  .measureX 3 [] [.Z 8, .Z 16, .Z 17, .CZ 0 7, .CZ 0 16],
  .CX 4 13,
  .CX 13 12,
  .CCX 10 12 4,
  .CX 12 5,
  .CX 13 5,
  .CX 14 5,
  .CCX 10 5 3,
  .CX 3 14,
  .measureX 3 [] [.Z 5, .CZ 1 5],
  .CX 12 6,
  .CX 13 6,
  .CX 15 6,
  .CCX 10 6 3,
  .CX 3 15,
  .measureX 3 [] [.Z 6, .CZ 1 6],
  .CX 16 8,
  .CX 9 2,
  .CX 11 2,
  .CCX 8 2 3,
  .CX 12 7,
  .CX 13 7,
  .CX 16 7,
  .CCX 10 7 28,
  .CX 9 11,
  .CX 9 16,
  .CX 9 17,
  .CX 9 28,
  .measureX 9 [] [.Z 7, .Z 28, .CZ 1 7],
  .CX 16 17,
  .CX 16 28,
  .CX 7 2,
  .CX 11 2,
  .CX 12 2,
  .CX 13 2,
  .CX 7 1,
  .CX 11 1,
  .CX 12 1,
  .CX 13 1,
  .CCX 2 1 16,
  .CX 2 16,
  .CX 1 2,
  .CX 1 3,
  .CX 1 11,
  .measureX 1 [] [.Z 3, .Z 8, .CZ 2 8, .CZ 8 10],
  .CX 10 3,
  .CX 16 7,
  .CX 28 7,
  .CCX 3 7 1,
  .CX 7 4,
  .CX 8 4,
  .CX 10 4,
  .CX 11 4,
  .CX 12 4,
  .CX 16 4,
  .CX 17 4,
  .CX 28 4,
  .CX 7 1,
  .CX 8 1,
  .CX 12 1,
  .CX 13 1,
  .CX 17 1,
  .CCX 4 1 9,
  .CX 8 4,
  .CX 10 4,
  .CX 11 4,
  .CX 13 4,
  .CX 14 4,
  .CX 9 7,
  .CX 12 7,
  .CX 16 7,
  .CX 17 7,
  .CX 28 7,
  .CCX 4 7 29,
  .CX 7 5,
  .CX 9 5,
  .CX 12 5,
  .CX 14 5,
  .CX 15 5,
  .CX 17 5,
  .CX 14 7,
  .CX 15 7,
  .CX 29 7,
  .CCX 5 7 6,
  .CX 5 6,
  .CX 5 7,
  .CX 5 29,
  .measureX 5 [] [.Z 1, .Z 7, .Z 8, .Z 9, .Z 13, .Z 14, .Z 15, .Z 17, .CZ 1 8, .CZ 1 10, .CZ 1 11, .CZ 1 17, .CZ 4 8, .CZ 4 9, .CZ 4 13],
  .CX 4 9,
  .CX 4 12,
  .CX 4 13,
  .measureX 4 [] [.Z 9, .CZ 1 8, .CZ 1 10, .CZ 1 11, .CZ 1 13, .CZ 1 14],
  .CX 6 12,
  .CX 6 14,
  .CX 6 15,
  .CX 6 28,
  .measureX 6 [] [.Z 1, .Z 7, .Z 16, .Z 17, .Z 28, .CZ 3 8, .CZ 3 12, .CZ 3 13, .CZ 3 16, .CZ 3 28, .CZ 7 8, .CZ 7 10, .CZ 7 11],
  .CX 7 0,
  .CX 9 0,
  .CX 11 0,
  .CX 13 0,
  .CX 14 0,
  .CX 15 0,
  .CX 17 0,
  .CX 29 0,
  .CX 12 9,
  .CX 14 9,
  .CX 15 9,
  .CX 29 9,
  .CCX 0 9 4,
  .CX 11 2,
  .CX 12 2,
  .CX 13 2,
  .CX 16 2,
  .CX 28 2,
  .CX 12 7,
  .CX 13 7,
  .CX 17 7,
  .CCX 2 7 5,
  .CX 7 8,
  .CX 7 9,
  .CX 7 12,
  .CX 7 13,
  .CX 7 17,
  .CX 7 29,
  .measureX 7 [] [.Z 8, .Z 9, .CZ 8 10, .CZ 9 10, .CZ 10 17],
  .CX 12 13,
  .CX 12 14,
  .CX 12 29,
  .CX 4 2,
  .CX 10 2,
  .CX 11 2,
  .CX 13 2,
  .CX 16 2,
  .CX 28 2,
  .CX 8 1,
  .CX 9 1,
  .CX 13 1,
  .CX 14 1,
  .CX 15 1,
  .CX 17 1,
  .CX 29 1,
  .CCX 2 1 12,
  .CX 14 15,
  .CX 4 2,
  .CX 13 9,
  .CCX 2 9 14,
  .CX 14 16,
  .CX 14 28,
  .CX 4 3,
  .CX 8 3,
  .CX 9 3,
  .CX 16 3,
  .CX 28 3,
  .CX 11 10,
  .CX 13 10,
  .CX 16 10,
  .CX 28 10,
  .CCX 3 10 14,
  .CX 3 5,
  .CX 3 14,
  .measureX 3 [] [.Z 5, .CZ 2 8, .CZ 2 9, .CZ 2 13, .CZ 8 10, .CZ 9 10, .CZ 10 13],
  .CX 14 15,
  .CX 14 16,
  .CX 14 28,
  .CX 14 29,
  .CX 15 1,
  .CX 17 1,
  .CX 29 1,
  .CCX 2 1 14,
  .CX 4 2,
  .CX 5 2,
  .CX 8 2,
  .CX 10 2,
  .CX 13 2,
  .CX 16 2,
  .CX 17 2,
  .CX 28 2,
  .CX 5 1,
  .CX 8 1,
  .CX 14 1,
  .CX 16 1,
  .CX 28 1,
  .CCX 2 1 3,
  .CX 2 3,
  .CX 10 8,
  .CX 12 8,
  .CX 13 8,
  .CX 15 8,
  .CX 16 8,
  .CX 17 8,
  .CX 28 8,
  .CX 29 8,
  .CX 3 2,
  .CX 5 2,
  .CX 13 2,
  .CX 14 2,
  .CX 16 2,
  .CX 17 2,
  .CX 28 2,
  .CCX 8 2 6,
  .CX 2 4,
  .CX 2 8,
  .CX 2 11,
  .CX 2 13,
  .measureX 2 [] [.Z 0, .Z 4, .CZ 0 4, .CZ 0 8, .CZ 0 12, .CZ 0 15, .CZ 0 29],
  .CX 3 8,
  .CX 3 12,
  .CX 3 14,
  .measureX 3 [] [.Z 0, .Z 4, .Z 8, .Z 9, .Z 10, .Z 12, .Z 13, .Z 14, .Z 15, .Z 17, .Z 29, .CZ 0 4, .CZ 0 8, .CZ 0 12, .CZ 0 15, .CZ 0 29, .CZ 1 4, .CZ 1 5, .CZ 1 8, .CZ 1 9, .CZ 1 10, .CZ 1 12, .CZ 1 13, .CZ 1 14, .CZ 1 15, .CZ 1 17, .CZ 1 29, .CZ 4 5, .CZ 5 8, .CZ 5 12, .CZ 5 15, .CZ 5 29],
  .CX 12 9,
  .CX 14 9,
  .CX 15 9,
  .CX 12 6,
  .CX 14 6,
  .CX 17 6,
  .CX 29 6,
  .CCX 9 6 2,
  .CX 4 0,
  .CX 8 0,
  .CX 9 0,
  .CX 10 0,
  .CX 13 0,
  .CX 17 0,
  .CX 29 0,
  .CX 6 2,
  .CX 9 2,
  .CX 12 2,
  .CX 14 2,
  .CX 15 2,
  .CCX 0 2 3,
  .CX 8 4,
  .CX 10 4,
  .CX 12 4,
  .CX 13 4,
  .CX 14 4,
  .CX 15 4,
  .CX 16 4,
  .CX 17 4,
  .CX 28 4,
  .CX 29 4,
  .CX 8 5,
  .CX 9 5,
  .CX 10 5,
  .CX 13 5,
  .CX 17 5,
  .CX 29 5,
  .CCX 4 5 7,
  .CX 8 6,
  .CX 9 6,
  .CX 10 6,
  .CX 12 6,
  .CX 13 6,
  .CX 14 6,
  .CX 15 6,
  .CX 16 6,
  .CX 17 6,
  .CX 28 6,
  .CX 29 6,
  .CCX 4 6 30,
  .CX 4 30,
  .CX 4 1,
  .CX 5 1,
  .CX 8 1,
  .CX 9 1,
  .CX 10 1,
  .CX 14 1,
  .CX 16 1,
  .CX 28 1,
  .CX 29 1,
  .CX 5 2,
  .CX 8 2,
  .CX 12 2,
  .CX 15 2,
  .CX 29 2,
  .CCX 1 2 31,
  .CX 4 2,
  .CX 5 2,
  .CX 8 2,
  .CX 9 2,
  .CX 13 2,
  .CX 29 2,
  .CX 8 7,
  .CX 9 7,
  .CX 10 7,
  .CX 12 7,
  .CX 14 7,
  .CX 15 7,
  .CX 16 7,
  .CX 28 7,
  .CX 31 7,
  .CCX 2 7 32,
  .CX 7 1,
  .CX 4 2,
  .CX 5 2,
  .CX 7 2,
  .CX 8 2,
  .CX 9 2,
  .CX 13 2,
  .CX 29 2,
  .CX 32 2,
  .CCX 1 2 33,
  .CX 1 33,
  .CX 3 1,
  .CX 4 1,
  .CX 7 1,
  .CX 9 1,
  .CX 12 1,
  .CX 13 1,
  .CX 15 1,
  .CX 17 1,
  .CX 9 5,
  .CX 10 5,
  .CX 12 5,
  .CX 14 5,
  .CX 15 5,
  .CX 16 5,
  .CX 28 5,
  .CX 32 5,
  .CX 33 5,
  .CCX 1 5 18,
  .CX 1 0,
  .CX 3 0,
  .CX 7 0,
  .CX 13 0,
  .CX 14 0,
  .CX 15 0,
  .CX 17 0,
  .CX 28 0,
  .CX 2 1,
  .CX 3 1,
  .CX 4 1,
  .CX 5 1,
  .CX 6 1,
  .CX 7 1,
  .CX 12 1,
  .CX 14 1,
  .CX 17 1,
  .CX 29 1,
  .CX 30 1,
  .CX 31 1,
  .CX 32 1,
  .CX 18 1,
  .CCX 0 1 19,
  .CX 1 8,
  .CX 1 9,
  .CX 1 12,
  .CX 1 13,
  .CX 1 15,
  .CX 1 16,
  .CX 1 17,
  .CX 1 29,
  .CX 1 30,
  .measureX 1 [] [.Z 4, .Z 9, .Z 12, .Z 13, .Z 15, .Z 17, .Z 19, .CZ 0 4, .CZ 0 9, .CZ 0 12, .CZ 0 13, .CZ 0 15, .CZ 0 17],
  .CX 12 13,
  .CX 12 28,
  .CX 12 29,
  .measureX 12 [] [.Z 0, .Z 3, .Z 4, .Z 5, .Z 7, .Z 9, .Z 14, .Z 29, .Z 31, .Z 18, .CZ 0 2, .CZ 0 3, .CZ 0 6, .CZ 0 8, .CZ 0 14, .CZ 0 17, .CZ 0 29, .CZ 0 31, .CZ 0 32, .CZ 2 4, .CZ 2 13, .CZ 2 15, .CZ 2 17, .CZ 2 30, .CZ 2 19, .CZ 4 8, .CZ 4 10, .CZ 4 13, .CZ 4 16, .CZ 4 17, .CZ 4 32, .CZ 4 19, .CZ 5 8, .CZ 5 10, .CZ 5 13, .CZ 5 14, .CZ 5 16, .CZ 5 29, .CZ 5 30, .CZ 6 8, .CZ 6 9, .CZ 7 8, .CZ 8 9, .CZ 9 14, .CZ 9 17, .CZ 9 29, .CZ 10 13, .CZ 10 14, .CZ 13 15, .CZ 13 16, .CZ 14 15, .CZ 14 16],
  .CX 9 13,
  .CX 9 28,
  .measureX 9 [] [.Z 2, .Z 7, .Z 15, .Z 17, .Z 30, .Z 31, .Z 32, .Z 19, .CZ 0 2, .CZ 0 4, .CZ 0 5, .CZ 0 6, .CZ 0 13, .CZ 0 14, .CZ 0 31, .CZ 0 32, .CZ 0 33, .CZ 2 4, .CZ 2 14, .CZ 2 15, .CZ 2 17, .CZ 2 31, .CZ 2 32, .CZ 4 7, .CZ 4 13, .CZ 4 15, .CZ 4 17, .CZ 5 6, .CZ 5 15, .CZ 5 29, .CZ 5 30, .CZ 6 8, .CZ 7 13, .CZ 7 14, .CZ 8 13, .CZ 8 14, .CZ 13 14, .CZ 13 15, .CZ 13 17, .CZ 13 30, .CZ 13 33, .CZ 13 19, .CZ 14 15, .CZ 14 17, .CZ 14 30, .CZ 14 33, .CZ 14 19],
  .CX 8 13,
  .CX 8 15,
  .CX 8 16,
  .measureX 8 [] [.Z 0, .Z 2, .Z 7, .Z 13, .Z 15, .Z 17, .Z 30, .Z 32, .Z 33, .CZ 0 2, .CZ 0 4, .CZ 0 5, .CZ 0 13, .CZ 0 15, .CZ 0 17, .CZ 0 31, .CZ 0 32, .CZ 0 33, .CZ 2 4, .CZ 2 5, .CZ 2 13, .CZ 2 15, .CZ 2 17, .CZ 2 31, .CZ 2 32, .CZ 4 5, .CZ 4 14, .CZ 4 17, .CZ 4 29, .CZ 4 32, .CZ 4 33, .CZ 5 6, .CZ 5 13, .CZ 5 14, .CZ 5 15, .CZ 5 29, .CZ 5 30, .CZ 6 14, .CZ 6 17, .CZ 6 29],
  .CX 5 13,
  .CX 5 15,
  .CX 5 16,
  .CX 5 29,
  .CX 5 30,
  .CX 5 33,
  .CX 5 18,
  .measureX 5 [] [.Z 6, .Z 13, .Z 14, .Z 15, .Z 29, .Z 30, .Z 31, .Z 32, .Z 33, .Z 18, .CZ 2 6, .CZ 2 13, .CZ 2 14, .CZ 2 15, .CZ 2 29, .CZ 2 30, .CZ 2 31, .CZ 2 32, .CZ 2 18],
  .CX 2 0,
  .CX 4 0,
  .CX 6 0,
  .CX 10 0,
  .CX 14 0,
  .CX 16 0,
  .CX 30 0,
  .CX 18 0,
  .CX 17 14,
  .CX 29 14,
  .CX 30 14,
  .CX 31 14,
  .CX 32 14,
  .CX 33 14,
  .CX 18 14,
  .CX 19 14,
  .CCX 0 14 1,
  .CX 0 1,
  .CX 17 7,
  .CX 28 7,
  .CX 29 7,
  .CX 30 7,
  .CX 31 7,
  .CX 32 7,
  .CX 6 2,
  .CX 13 2,
  .CX 15 2,
  .CX 28 2,
  .CX 29 2,
  .CX 30 2,
  .CX 32 2,
  .CX 33 2,
  .CX 19 2,
  .CCX 7 2 5,
  .CX 2 0,
  .CX 3 0,
  .CX 7 0,
  .CX 10 0,
  .CX 14 0,
  .CX 16 0,
  .CX 17 0,
  .CX 29 0,
  .CX 31 0,
  .CX 33 0,
  .CX 18 0,
  .CX 4 3,
  .CX 5 3,
  .CX 13 3,
  .CX 15 3,
  .CX 17 3,
  .CX 30 3,
  .CX 31 3,
  .CX 32 3,
  .CX 18 3,
  .CCX 0 3 8,
  .CX 7 8,
  .CX 7 11,
  .CX 7 16,
  .CX 7 17,
  .CX 7 29,
  .CX 7 30,
  .CX 7 31,
  .CX 7 32,
  .CX 7 18,
  .CX 7 19,
  .measureX 7 [] [.Z 8, .CZ 0 3],
  .CX 0 1,
  .CX 0 2,
  .CX 0 3,
  .CX 0 6,
  .CX 0 31,
  .CX 0 32,
  .CX 0 18,
  .CX 0 19,
  .measureX 0 [] [.Z 1, .Z 4, .Z 5, .Z 6, .Z 8, .Z 10, .Z 14, .Z 15, .Z 16, .Z 31, .Z 32, .Z 33, .Z 18, .CZ 1 2, .CZ 1 3, .CZ 1 5, .CZ 1 10, .CZ 1 14, .CZ 1 15, .CZ 1 16, .CZ 1 17, .CZ 1 28, .CZ 1 29, .CZ 1 32, .CZ 1 33, .CZ 2 3, .CZ 2 5, .CZ 2 8, .CZ 2 17, .CZ 2 28, .CZ 2 29, .CZ 2 32, .CZ 2 18, .CZ 3 4, .CZ 3 10, .CZ 3 13, .CZ 3 14, .CZ 3 16, .CZ 3 17, .CZ 3 31, .CZ 3 33, .CZ 3 18, .CZ 4 5, .CZ 4 6, .CZ 4 8, .CZ 4 14, .CZ 4 17, .CZ 4 28, .CZ 4 29, .CZ 4 30, .CZ 4 31, .CZ 4 32, .CZ 5 6, .CZ 5 8, .CZ 5 17, .CZ 5 28, .CZ 5 29, .CZ 6 8, .CZ 6 14],
  .CX 1 6,
  .CX 1 11,
  .CX 1 13,
  .CX 1 15,
  .CX 1 16,
  .CX 1 17,
  .CX 1 28,
  .measureX 1 [] [.Z 2, .Z 5, .Z 8, .Z 33, .CZ 2 3, .CZ 2 13, .CZ 2 14, .CZ 2 29, .CZ 2 30, .CZ 2 31, .CZ 2 32, .CZ 2 18, .CZ 3 4, .CZ 3 8, .CZ 3 14, .CZ 3 31, .CZ 3 18, .CZ 4 5, .CZ 4 6, .CZ 4 8, .CZ 4 10, .CZ 4 13, .CZ 4 14, .CZ 4 16, .CZ 4 28, .CZ 4 29, .CZ 4 30, .CZ 5 15, .CZ 5 17, .CZ 5 29, .CZ 6 8, .CZ 6 13, .CZ 6 15, .CZ 6 17, .CZ 6 30, .CZ 6 31, .CZ 6 33, .CZ 6 18, .CZ 8 14, .CZ 8 31],
  .CX 3 8,
  .CX 3 13,
  .CX 3 15,
  .CX 3 16,
  .CX 3 29,
  .CX 3 30,
  .measureX 3 [] [.Z 4, .Z 8, .Z 10, .Z 30, .Z 31, .Z 33, .Z 18, .CZ 2 5, .CZ 2 17, .CZ 2 28, .CZ 2 30, .CZ 2 33, .CZ 2 18, .CZ 4 6, .CZ 4 10, .CZ 4 13, .CZ 4 15, .CZ 4 28, .CZ 4 29, .CZ 4 30, .CZ 4 33, .CZ 4 18, .CZ 5 13, .CZ 5 15, .CZ 5 28, .CZ 6 8, .CZ 6 10, .CZ 6 15, .CZ 6 16, .CZ 6 32, .CZ 8 13, .CZ 8 14, .CZ 8 15, .CZ 8 28, .CZ 8 29, .CZ 8 31, .CZ 8 33, .CZ 10 13, .CZ 10 16, .CZ 10 28, .CZ 10 29, .CZ 13 15, .CZ 13 16, .CZ 13 30, .CZ 13 31, .CZ 13 33, .CZ 14 15, .CZ 14 17],
  .CX 5 17,
  .CX 5 30,
  .measureX 5 [] [.Z 8, .Z 13, .Z 14, .Z 15, .Z 17, .Z 28, .Z 30, .Z 32, .CZ 2 6, .CZ 2 10, .CZ 2 13, .CZ 2 14, .CZ 2 16, .CZ 2 17, .CZ 2 30, .CZ 2 32, .CZ 2 33, .CZ 4 6, .CZ 4 8, .CZ 4 10, .CZ 4 13, .CZ 4 14, .CZ 4 16, .CZ 4 17, .CZ 4 30, .CZ 4 31, .CZ 4 32, .CZ 4 33, .CZ 4 18, .CZ 6 8, .CZ 6 13, .CZ 6 15, .CZ 6 17, .CZ 6 30, .CZ 6 31, .CZ 6 32, .CZ 6 33, .CZ 6 18, .CZ 8 10, .CZ 8 14, .CZ 8 15, .CZ 8 16, .CZ 8 17, .CZ 8 28, .CZ 8 29, .CZ 8 32, .CZ 8 33, .CZ 8 18, .CZ 10 13, .CZ 10 14, .CZ 10 15, .CZ 10 17, .CZ 13 14, .CZ 13 15, .CZ 13 16, .CZ 14 15, .CZ 14 16, .CZ 14 17, .CZ 14 28, .CZ 14 31, .CZ 14 32, .CZ 15 16, .CZ 15 17, .CZ 16 17],
  .CX 2 6,
  .CX 2 8,
  .CX 2 11,
  .CX 2 16,
  .CX 2 29,
  .CX 2 30,
  .CX 2 31,
  .CX 2 32,
  .CX 2 19,
  .measureX 2 [] [.Z 10, .Z 13, .Z 14, .Z 15, .Z 16, .Z 17, .Z 29, .Z 33, .Z 18, .CZ 4 6, .CZ 4 10, .CZ 4 14, .CZ 4 16, .CZ 4 29, .CZ 4 30, .CZ 4 32, .CZ 4 33, .CZ 6 17, .CZ 6 28, .CZ 6 29, .CZ 6 32, .CZ 6 33, .CZ 8 17, .CZ 8 28, .CZ 8 29, .CZ 8 30, .CZ 8 32, .CZ 8 33, .CZ 8 18, .CZ 10 28, .CZ 10 29, .CZ 10 30, .CZ 10 33, .CZ 13 30, .CZ 13 31, .CZ 13 33, .CZ 14 15, .CZ 14 17, .CZ 14 28, .CZ 14 33, .CZ 15 28, .CZ 15 29, .CZ 15 31, .CZ 16 28, .CZ 16 29, .CZ 16 30, .CZ 16 33],
  .CX 6 8,
  .CX 6 13,
  .CX 6 15,
  .CX 6 16,
  .CX 6 17,
  .CX 6 29,
  .CX 6 30,
  .CX 6 32,
  .CX 6 33,
  .CX 6 19,
  .measureX 6 [] [.Z 4, .Z 8, .Z 17, .Z 30, .Z 31, .CZ 4 14, .CZ 4 15, .CZ 4 29, .CZ 4 30, .CZ 4 31, .CZ 4 32, .CZ 4 33, .CZ 4 18, .CZ 8 10, .CZ 8 16, .CZ 8 28, .CZ 8 32, .CZ 8 18, .CZ 10 14, .CZ 10 17, .CZ 10 31, .CZ 10 33, .CZ 13 14, .CZ 13 15, .CZ 13 28, .CZ 13 31, .CZ 13 33, .CZ 13 18, .CZ 14 15, .CZ 14 16, .CZ 14 17, .CZ 14 29, .CZ 14 30, .CZ 14 31, .CZ 14 32, .CZ 15 17, .CZ 15 29, .CZ 15 31, .CZ 15 33, .CZ 15 18, .CZ 16 17, .CZ 16 31, .CZ 16 33, .CZ 17 32, .CZ 17 18, .CZ 28 29, .CZ 28 30, .CZ 28 31, .CZ 28 32, .CZ 28 33, .CZ 29 30, .CZ 29 32],
  .CX 13 15,
  .CX 13 17,
  .CX 13 28,
  .CX 13 29,
  .CX 13 30,
  .CX 13 18,
  .measureX 13 [] [.Z 4, .Z 8, .Z 10, .Z 15, .Z 17, .Z 28, .Z 32, .Z 33, .CZ 4 10, .CZ 4 14, .CZ 4 15, .CZ 4 29, .CZ 4 31, .CZ 4 32, .CZ 8 10, .CZ 8 16, .CZ 8 28, .CZ 8 29, .CZ 8 30, .CZ 8 31, .CZ 8 33, .CZ 10 16, .CZ 10 17, .CZ 10 28, .CZ 10 29, .CZ 10 32, .CZ 10 33, .CZ 14 15, .CZ 14 30, .CZ 14 32, .CZ 15 17, .CZ 15 30, .CZ 15 18, .CZ 16 17, .CZ 16 32, .CZ 16 33, .CZ 17 29, .CZ 17 30, .CZ 17 31, .CZ 17 32, .CZ 28 29, .CZ 28 30, .CZ 28 18, .CZ 29 31, .CZ 29 32, .CZ 29 18],
  .CX 8 11,
  .CX 8 17,
  .CX 8 28,
  .CX 8 29,
  .CX 8 32,
  .CX 8 18,
  .CX 8 19,
  .measureX 8 [] [.Z 4, .Z 10, .Z 14, .Z 15, .Z 16, .Z 17, .Z 29, .Z 32, .Z 33, .CZ 4 15, .CZ 4 17, .CZ 4 28, .CZ 4 30, .CZ 10 14, .CZ 10 15, .CZ 10 31, .CZ 14 15, .CZ 14 16, .CZ 14 28, .CZ 14 30, .CZ 14 31, .CZ 14 32, .CZ 14 33, .CZ 15 16, .CZ 15 17, .CZ 15 28, .CZ 15 29, .CZ 15 32, .CZ 15 33, .CZ 16 31, .CZ 17 28, .CZ 17 29, .CZ 28 30, .CZ 28 32, .CZ 29 30, .CZ 29 32, .CZ 31 33, .CZ 31 18],
  .CX 11 28,
  .CX 11 29,
  .CX 11 30,
  .CX 11 32,
  .CX 11 33,
  .CX 11 18,
  .measureX 11 [] [.Z 4, .Z 16, .Z 17, .Z 28, .Z 30, .Z 32, .CZ 4 10, .CZ 4 17, .CZ 4 28, .CZ 4 29, .CZ 4 30, .CZ 4 31, .CZ 4 32, .CZ 10 14, .CZ 10 15, .CZ 10 16, .CZ 10 17, .CZ 10 28, .CZ 10 30, .CZ 10 32, .CZ 10 18, .CZ 14 16, .CZ 14 17, .CZ 14 29, .CZ 14 30, .CZ 14 32, .CZ 14 33, .CZ 15 16, .CZ 15 17, .CZ 15 29, .CZ 15 31, .CZ 15 32, .CZ 15 33, .CZ 15 18, .CZ 16 17, .CZ 16 29, .CZ 16 30, .CZ 16 32, .CZ 16 18, .CZ 17 30, .CZ 17 31, .CZ 17 32, .CZ 28 32, .CZ 28 33, .CZ 29 30, .CZ 29 31, .CZ 29 32, .CZ 30 18, .CZ 31 33, .CZ 33 18],
  .CX 23 22,
  .CX 23 21,
  .CX 23 20,
  .CX 23 19,
  .CX 23 18,
  .CX 23 30,
  .CX 23 17,
  .CX 23 14,
  .CX 23 13,
  .CX 23 11,
  .CX 23 7,
  .CX 23 5,
  .CX 23 4,
  .CX 23 3,
  .CX 23 0,
  .CX 22 23,
  .CX 22 21,
  .CX 22 20,
  .CX 22 19,
  .CX 22 18,
  .CX 22 30,
  .CX 22 17,
  .CX 22 14,
  .CX 22 13,
  .CX 22 11,
  .CX 22 7,
  .CX 22 5,
  .CX 22 4,
  .CX 22 3,
  .CX 22 0,
  .CX 23 22,
  .CX 21 23,
  .CX 21 20,
  .CX 21 19,
  .CX 21 18,
  .CX 21 30,
  .CX 21 17,
  .CX 21 14,
  .CX 21 13,
  .CX 21 11,
  .CX 21 7,
  .CX 21 5,
  .CX 21 4,
  .CX 21 3,
  .CX 21 0,
  .CX 23 21,
  .CX 20 23,
  .CX 20 19,
  .CX 20 18,
  .CX 20 30,
  .CX 20 17,
  .CX 20 14,
  .CX 20 13,
  .CX 20 11,
  .CX 20 7,
  .CX 20 5,
  .CX 20 4,
  .CX 20 3,
  .CX 20 0,
  .CX 23 20,
  .CX 19 23,
  .CX 19 18,
  .CX 19 30,
  .CX 19 17,
  .CX 19 14,
  .CX 19 13,
  .CX 19 11,
  .CX 19 7,
  .CX 19 5,
  .CX 19 4,
  .CX 19 3,
  .CX 19 0,
  .CX 23 19,
  .CX 18 23,
  .CX 18 30,
  .CX 18 29,
  .CX 18 28,
  .CX 18 17,
  .CX 18 16,
  .CX 18 10,
  .CX 23 18,
  .CX 33 23,
  .CX 33 18,
  .CX 33 32,
  .CX 33 17,
  .CX 33 16,
  .CX 33 13,
  .CX 33 10,
  .CX 33 7,
  .CX 33 0,
  .CX 18 33,
  .CX 32 33,
  .CX 32 28,
  .CX 32 16,
  .CX 32 15,
  .CX 33 32,
  .CX 31 18,
  .CX 31 33,
  .CX 31 32,
  .CX 31 30,
  .CX 31 29,
  .CX 31 13,
  .CX 31 10,
  .CX 31 7,
  .CX 31 4,
  .CX 31 3,
  .CX 31 0,
  .CX 32 31,
  .CX 30 33,
  .CX 30 32,
  .CX 30 31,
  .CX 30 17,
  .CX 30 16,
  .CX 30 15,
  .CX 30 14,
  .CX 30 11,
  .CX 30 10,
  .CX 30 5,
  .CX 30 4,
  .CX 30 3,
  .CX 31 30,
  .CX 29 18,
  .CX 29 32,
  .CX 29 17,
  .CX 29 16,
  .CX 29 15,
  .CX 29 13,
  .CX 29 7,
  .CX 29 0,
  .CX 32 29,
  .CX 28 29,
  .CX 28 17,
  .CX 28 16,
  .CX 28 15,
  .CX 29 28,
  .CX 17 23,
  .CX 17 18,
  .CX 17 33,
  .CX 17 29,
  .CX 17 28,
  .CX 17 15,
  .CX 17 14,
  .CX 17 13,
  .CX 17 12,
  .CX 17 7,
  .CX 17 6,
  .CX 17 4,
  .CX 17 3,
  .CX 17 0,
  .CX 16 23,
  .CX 16 18,
  .CX 16 33,
  .CX 16 32,
  .CX 16 31,
  .CX 16 15,
  .CX 16 13,
  .CX 16 10,
  .CX 16 7,
  .CX 16 0,
  .CX 31 16,
  .CX 15 23,
  .CX 15 33,
  .CX 15 32,
  .CX 15 31,
  .CX 15 29,
  .CX 15 17,
  .CX 15 14,
  .CX 15 12,
  .CX 15 10,
  .CX 15 9,
  .CX 15 6,
  .CX 15 4,
  .CX 15 2,
  .CX 14 29,
  .CX 14 17,
  .CX 14 15,
  .CX 14 12,
  .CX 14 10,
  .CX 14 9,
  .CX 14 8,
  .CX 14 6,
  .CX 14 4,
  .CX 14 2,
  .CX 14 1,
  .CX 13 18,
  .CX 18 13,
  .CX 12 17,
  .CX 17 12,
  .CX 11 16,
  .CX 16 11,
  .CX 10 23,
  .CX 10 32,
  .CX 10 29,
  .CX 10 28,
  .CX 28 10,
  .CX 9 15,
  .CX 15 9,
  .CX 8 14,
  .CX 14 8,
  .CX 7 13,
  .CX 13 7,
  .CX 6 12,
  .CX 12 6,
  .CX 5 11,
  .CX 11 5,
  .CX 4 33,
  .CX 4 32,
  .CX 4 29,
  .CX 4 28,
  .CX 4 9,
  .CX 4 2,
  .CX 9 4,
  .CX 3 10,
  .CX 10 3,
  .CX 2 9,
  .CX 9 2,
  .CX 1 8,
  .CX 8 1,
  .CX 0 7,
  .CX 7 0,
  .X 23,
  .CX 6 7,
  .X 7,
  .CX 6 10
]
def reference : Program := [
  .CX 11 2,
  .CX 12 3,
  .CX 13 4,
  .CX 14 5,
  .CX 15 6,
  .CX 16 7,
  .CCX 1 2 11,
  .CCX 1 3 12,
  .CCX 1 4 13,
  .CCX 1 5 14,
  .CCX 1 6 15,
  .CCX 1 7 16,
  .CX 11 2,
  .CX 12 3,
  .CX 13 4,
  .CX 14 5,
  .CX 15 6,
  .CX 16 7,
  .CX 8 17,
  .measureX 8 [] [.CZ 0 17],
  .CX 17 8,
  .CX 8 17,
  .CX 16 17,
  .CX 16 8,
  .CX 1 10,
  .CX 8 9,
  .X 28,
  .CX 8 28,
  .CX 16 28,
  .CX 28 2,
  .CX 28 3,
  .CX 28 4,
  .CX 28 5,
  .CX 28 6,
  .CX 28 7,
  .CX 28 8,
  .CX 2 10,
  .CX 2 28,
  .CCX 10 28 34,
  .CX 2 34,
  .CX 2 28,
  .CX 2 10,
  .CX 3 11,
  .CX 3 34,
  .CCX 11 34 35,
  .CX 3 35,
  .CX 3 34,
  .CX 3 11,
  .CX 4 12,
  .CX 4 35,
  .CCX 12 35 36,
  .CX 4 36,
  .CX 4 35,
  .CX 4 12,
  .CX 5 13,
  .CX 5 36,
  .CCX 13 36 37,
  .CX 5 37,
  .CX 5 36,
  .CX 5 13,
  .CX 6 14,
  .CX 6 37,
  .CCX 14 37 38,
  .CX 6 38,
  .CX 6 37,
  .CX 6 14,
  .CX 7 15,
  .CX 7 38,
  .CCX 15 38 39,
  .CX 7 39,
  .CX 7 38,
  .CX 7 15,
  .CX 8 16,
  .CX 39 16,
  .measureX 39 [] [.CZ 7 15, .CZ 7 38, .CZ 15 38],
  .CX 7 15,
  .CX 38 15,
  .measureX 38 [] [.CZ 6 14, .CZ 6 37, .CZ 14 37],
  .CX 6 14,
  .CX 37 14,
  .measureX 37 [] [.CZ 5 13, .CZ 5 36, .CZ 13 36],
  .CX 5 13,
  .CX 36 13,
  .measureX 36 [] [.CZ 4 12, .CZ 4 35, .CZ 12 35],
  .CX 4 12,
  .CX 35 12,
  .measureX 35 [] [.CZ 3 11, .CZ 3 34, .CZ 11 34],
  .CX 3 11,
  .CX 34 11,
  .measureX 34 [] [.CZ 2 10, .CZ 2 28, .CZ 10 28],
  .CX 2 10,
  .CX 28 10,
  .CX 28 2,
  .CX 28 3,
  .CX 28 4,
  .CX 28 5,
  .CX 28 6,
  .CX 28 7,
  .CX 28 8,
  .X 28,
  .CX 8 28,
  .CX 16 28,
  .CX 28 17,
  .CX 0 1,
  .CX 8 9,
  .CX 16 17,
  .CX 11 3,
  .CCX 2 3 9,
  .CX 3 1,
  .CX 9 1,
  .CX 11 1,
  .CX 16 1,
  .CX 15 8,
  .CCX 1 8 17,
  .CX 5 13,
  .CX 15 10,
  .CX 16 10,
  .CX 12 4,
  .CX 13 4,
  .CCX 10 4 5,
  .CX 15 10,
  .CX 16 10,
  .CX 7 6,
  .CX 14 6,
  .CX 15 6,
  .CCX 10 6 29,
  .CX 9 8,
  .CX 10 8,
  .CX 11 8,
  .CX 15 8,
  .CX 16 8,
  .CX 9 3,
  .CX 10 3,
  .CX 11 3,
  .CCX 8 3 30,
  .CX 8 30,
  .CX 14 29,
  .CX 6 4,
  .CX 7 4,
  .CX 13 4,
  .CX 15 4,
  .CCX 10 4 14,
  .CX 7 2,
  .CX 8 2,
  .CX 17 2,
  .CX 16 2,
  .CX 9 7,
  .CX 12 7,
  .CX 14 7,
  .CX 16 7,
  .CX 29 7,
  .CX 30 7,
  .CCX 2 7 31,
  .CX 4 2,
  .CX 5 2,
  .CX 6 2,
  .CX 9 2,
  .CX 17 2,
  .CX 11 2,
  .CX 12 2,
  .CX 13 2,
  .CX 6 4,
  .CX 8 4,
  .CX 10 4,
  .CX 11 4,
  .CX 12 4,
  .CX 14 4,
  .CX 29 4,
  .CX 30 4,
  .CX 31 4,
  .CCX 2 4 32,
  .CX 7 5,
  .CX 9 5,
  .CX 12 5,
  .CX 15 5,
  .CX 16 5,
  .CX 29 5,
  .CX 30 5,
  .CX 9 7,
  .CX 12 7,
  .CX 13 7,
  .CX 14 7,
  .CX 15 7,
  .CX 16 7,
  .CX 29 7,
  .CX 30 7,
  .CX 32 7,
  .CCX 5 7 33,
  .CX 2 1,
  .CX 3 1,
  .CX 4 1,
  .CX 5 1,
  .CX 9 1,
  .CX 13 1,
  .CX 15 1,
  .CX 29 1,
  .CX 30 1,
  .CX 31 1,
  .CX 7 6,
  .CX 33 6,
  .CCX 1 6 34,
  .CX 10 3,
  .CX 5 2,
  .CX 17 2,
  .CX 11 2,
  .CX 13 2,
  .CX 15 2,
  .CX 16 2,
  .CX 29 2,
  .CX 30 2,
  .CX 31 2,
  .CCX 3 2 35,
  .CX 3 35,
  .CX 7 4,
  .CX 15 4,
  .CX 16 4,
  .CCX 3 4 36,
  .CX 7 3,
  .CX 9 3,
  .CX 12 3,
  .CX 13 3,
  .CX 14 3,
  .CX 15 3,
  .CX 16 3,
  .CX 29 3,
  .CX 30 3,
  .CX 32 3,
  .CX 7 6,
  .CX 8 6,
  .CX 17 6,
  .CX 10 6,
  .CX 13 6,
  .CX 15 6,
  .CX 16 6,
  .CX 32 6,
  .CCX 3 6 26,
  .CX 7 6,
  .CX 9 6,
  .CX 17 6,
  .CX 11 6,
  .CX 13 6,
  .CX 15 6,
  .CX 16 6,
  .CX 32 6,
  .CX 5 3,
  .CX 7 3,
  .CX 12 3,
  .CX 14 3,
  .CX 32 3,
  .CX 35 3,
  .CX 26 3,
  .CCX 6 3 27,
  .CX 7 5,
  .CX 12 5,
  .CX 14 5,
  .CX 32 5,
  .CX 35 5,
  .CX 26 5,
  .CX 6 3,
  .CX 7 3,
  .CX 9 3,
  .CX 17 3,
  .CX 11 3,
  .CX 13 3,
  .CX 15 3,
  .CX 16 3,
  .CX 32 3,
  .CX 27 3,
  .CCX 5 3 18,
  .CX 5 18,
  .CX 5 3,
  .CX 6 3,
  .CX 8 3,
  .CX 17 3,
  .CX 10 3,
  .CX 15 3,
  .CX 16 3,
  .CX 34 3,
  .CX 27 3,
  .CX 7 4,
  .CX 9 4,
  .CX 17 4,
  .CX 11 4,
  .CX 15 4,
  .CX 16 4,
  .CX 27 4,
  .CX 18 4,
  .CCX 3 4 19,
  .CX 3 1,
  .CX 5 1,
  .CX 8 1,
  .CX 10 1,
  .CX 11 1,
  .CX 12 1,
  .CX 14 1,
  .CX 16 1,
  .CX 30 1,
  .CX 34 1,
  .CX 5 3,
  .CX 6 3,
  .CX 12 3,
  .CX 13 3,
  .CX 14 3,
  .CX 32 3,
  .CX 34 3,
  .CX 35 3,
  .CX 36 3,
  .CX 27 3,
  .CX 18 3,
  .CX 19 3,
  .CCX 1 3 20,
  .CX 1 20,
  .CX 4 1,
  .CX 5 1,
  .CX 7 1,
  .CX 9 1,
  .CX 17 1,
  .CX 11 1,
  .CX 13 1,
  .CX 16 1,
  .CX 29 1,
  .CX 32 1,
  .CX 26 1,
  .CX 18 1,
  .CX 7 4,
  .CX 9 4,
  .CX 17 4,
  .CX 11 4,
  .CX 12 4,
  .CX 13 4,
  .CX 14 4,
  .CX 16 4,
  .CX 29 4,
  .CX 32 4,
  .CX 35 4,
  .CX 36 4,
  .CX 26 4,
  .CX 27 4,
  .CX 19 4,
  .CX 20 4,
  .CCX 1 4 21,
  .CX 13 29,
  .CX 13 30,
  .CX 13 31,
  .CX 13 32,
  .CX 13 33,
  .CX 13 36,
  .CX 13 18,
  .CX 13 20,
  .CX 5 3,
  .CX 6 3,
  .CX 7 3,
  .CX 8 3,
  .CX 9 3,
  .CX 10 3,
  .CX 11 3,
  .CX 15 3,
  .CX 29 3,
  .CX 18 3,
  .CX 19 3,
  .CX 4 1,
  .CX 12 1,
  .CX 14 1,
  .CX 15 1,
  .CX 29 1,
  .CX 35 1,
  .CX 36 1,
  .CX 26 1,
  .CX 27 1,
  .CCX 3 1 13,
  .CX 5 1,
  .CX 6 1,
  .CX 12 1,
  .CX 14 1,
  .CX 15 1,
  .CX 29 1,
  .CX 32 1,
  .CX 34 1,
  .CX 35 1,
  .CX 36 1,
  .CX 18 1,
  .CX 19 1,
  .CX 20 1,
  .CX 8 7,
  .CX 9 7,
  .CX 10 7,
  .CX 11 7,
  .CX 13 7,
  .CX 32 7,
  .CX 34 7,
  .CX 36 7,
  .CX 26 7,
  .CX 27 7,
  .CX 19 7,
  .CCX 1 7 22,
  .CX 1 22,
  .CX 16 29,
  .CX 16 32,
  .CX 16 33,
  .CX 16 36,
  .CX 16 26,
  .CX 16 22,
  .measureX 16 [] [.Z 1, .Z 22, .CZ 1 7],
  .CX 33 35,
  .CX 33 26,
  .CX 33 27,
  .CX 33 18,
  .CX 33 20,
  .CX 33 22,
  .measureX 33 [] [.Z 3, .Z 8, .Z 10, .Z 11, .Z 30, .Z 36, .Z 27, .CZ 2 3, .CZ 2 8, .CZ 2 10, .CZ 2 11, .CZ 2 30, .CZ 2 35, .CZ 2 36, .CZ 2 27],
  .CX 35 26,
  .CX 35 27,
  .CX 35 18,
  .CX 35 20,
  .CX 35 22,
  .measureX 35 [] [.Z 2, .Z 3, .Z 6, .Z 7, .Z 8, .Z 9, .Z 17, .Z 10, .Z 11, .Z 12, .Z 14, .Z 15, .Z 29, .Z 31, .Z 32, .Z 26, .Z 18, .CZ 1 9, .CZ 1 17, .CZ 1 11, .CZ 1 12, .CZ 1 14, .CZ 1 29, .CZ 1 36, .CZ 1 26, .CZ 1 27, .CZ 1 18, .CZ 2 3, .CZ 2 4, .CZ 2 5, .CZ 2 8, .CZ 2 9, .CZ 2 17, .CZ 2 10, .CZ 2 12, .CZ 2 14, .CZ 2 30, .CZ 2 36, .CZ 2 27, .CZ 3 6, .CZ 3 17, .CZ 3 11, .CZ 3 12, .CZ 3 14, .CZ 3 15, .CZ 3 30, .CZ 3 34, .CZ 3 21, .CZ 4 6, .CZ 4 8, .CZ 4 9, .CZ 4 10, .CZ 4 11, .CZ 4 15, .CZ 4 32, .CZ 5 6, .CZ 5 11, .CZ 5 13, .CZ 5 15, .CZ 5 30, .CZ 5 31, .CZ 6 7, .CZ 6 12, .CZ 6 14, .CZ 7 9, .CZ 7 17, .CZ 7 11, .CZ 7 12, .CZ 7 14, .CZ 7 15, .CZ 7 29, .CZ 7 26, .CZ 8 17, .CZ 17 15],
  .CX 17 13,
  .CX 17 15,
  .CX 17 30,
  .CX 17 31,
  .CX 17 36,
  .CX 17 18,
  .CX 17 20,
  .measureX 17 [] [.Z 1, .Z 3, .Z 4, .Z 5, .Z 6, .Z 7, .Z 8, .Z 10, .Z 13, .Z 15, .Z 31, .Z 32, .Z 34, .Z 27, .Z 18, .Z 19, .CZ 1 2, .CZ 1 8, .CZ 1 9, .CZ 1 10, .CZ 1 12, .CZ 1 13, .CZ 1 14, .CZ 1 15, .CZ 1 29, .CZ 1 30, .CZ 1 31, .CZ 1 32, .CZ 1 36, .CZ 1 18, .CZ 2 3, .CZ 2 5, .CZ 2 7, .CZ 2 8, .CZ 2 10, .CZ 2 11, .CZ 2 12, .CZ 2 13, .CZ 2 14, .CZ 2 30, .CZ 2 32, .CZ 2 26, .CZ 2 27, .CZ 2 22, .CZ 3 6, .CZ 3 8, .CZ 3 10, .CZ 3 12, .CZ 3 13, .CZ 3 14, .CZ 3 15, .CZ 3 34, .CZ 3 26, .CZ 3 27, .CZ 3 18, .CZ 4 5, .CZ 4 6, .CZ 4 8, .CZ 4 10, .CZ 4 12, .CZ 4 13, .CZ 4 14, .CZ 4 15, .CZ 4 32, .CZ 4 36, .CZ 4 26, .CZ 5 6, .CZ 5 7, .CZ 5 8, .CZ 5 9, .CZ 5 10, .CZ 5 11, .CZ 5 13, .CZ 7 12, .CZ 7 13, .CZ 7 14, .CZ 7 15, .CZ 7 29, .CZ 7 22],
  .CX 13 29,
  .CX 13 30,
  .CX 13 31,
  .CX 13 36,
  .CX 13 18,
  .CX 13 20,
  .measureX 13 [] [.Z 2, .Z 3, .Z 4, .Z 5, .Z 6, .Z 10, .Z 11, .Z 15, .Z 29, .Z 32, .Z 34, .Z 26, .Z 18, .Z 22, .CZ 1 3, .CZ 1 6, .CZ 1 7, .CZ 1 15, .CZ 1 36, .CZ 1 27, .CZ 1 18, .CZ 2 3, .CZ 2 6, .CZ 2 7, .CZ 2 8, .CZ 2 10, .CZ 2 31, .CZ 2 36, .CZ 2 27, .CZ 2 22, .CZ 3 4, .CZ 3 8, .CZ 3 12, .CZ 3 14, .CZ 3 15, .CZ 3 32, .CZ 3 34, .CZ 3 18, .CZ 3 21, .CZ 4 6, .CZ 4 7, .CZ 4 8, .CZ 4 10, .CZ 5 7, .CZ 5 8, .CZ 5 9, .CZ 5 10, .CZ 5 11, .CZ 6 11, .CZ 6 12, .CZ 6 14, .CZ 6 15, .CZ 6 30, .CZ 7 8, .CZ 7 10, .CZ 7 12, .CZ 7 14, .CZ 7 15, .CZ 7 36, .CZ 7 18, .CZ 8 9, .CZ 8 10, .CZ 8 12, .CZ 8 14, .CZ 8 30, .CZ 8 36, .CZ 8 27, .CZ 10 12, .CZ 10 14],
  .CX 6 29,
  .CX 6 30,
  .CX 6 31,
  .CX 6 34,
  .CX 6 36,
  .CX 6 18,
  .CX 6 20,
  .measureX 6 [] [.Z 3, .Z 4, .Z 5, .Z 8, .Z 10, .Z 11, .Z 15, .Z 29, .Z 30, .Z 32, .Z 36, .Z 26, .Z 22, .CZ 1 2, .CZ 1 4, .CZ 1 5, .CZ 1 8, .CZ 1 10, .CZ 1 29, .CZ 1 32, .CZ 1 27, .CZ 1 22, .CZ 2 3, .CZ 2 4, .CZ 2 5, .CZ 2 11, .CZ 2 29, .CZ 2 30, .CZ 2 36, .CZ 2 27, .CZ 2 18, .CZ 3 4, .CZ 3 7, .CZ 3 8, .CZ 3 10, .CZ 3 15, .CZ 3 32, .CZ 3 26, .CZ 3 27, .CZ 3 18, .CZ 3 22],
  .CX 1 3,
  .CX 1 4,
  .CX 1 30,
  .CX 1 31,
  .CX 1 36,
  .CX 1 18,
  .CX 1 21,
  .CX 1 22,
  .measureX 1 [] [.Z 4, .Z 7, .Z 10, .Z 11, .Z 12, .Z 29, .Z 30, .Z 31, .Z 36, .Z 26, .Z 27, .Z 19, .Z 22, .CZ 2 7, .CZ 2 8, .CZ 2 10, .CZ 2 15, .CZ 2 29, .CZ 2 32, .CZ 2 27, .CZ 2 18, .CZ 2 19, .CZ 3 4, .CZ 3 5, .CZ 3 10, .CZ 3 12, .CZ 3 14, .CZ 3 15, .CZ 3 29, .CZ 3 26, .CZ 3 27, .CZ 3 18, .CZ 3 19, .CZ 4 7, .CZ 4 11, .CZ 4 30, .CZ 4 26, .CZ 4 18, .CZ 4 19, .CZ 4 21, .CZ 5 7, .CZ 5 8, .CZ 5 9, .CZ 5 10, .CZ 5 11, .CZ 5 12, .CZ 5 14, .CZ 5 29, .CZ 5 32, .CZ 5 34, .CZ 5 19, .CZ 5 22, .CZ 7 9, .CZ 7 11, .CZ 7 12, .CZ 7 14, .CZ 7 32, .CZ 7 34, .CZ 7 36, .CZ 7 18, .CZ 8 9, .CZ 8 10, .CZ 8 12, .CZ 8 14, .CZ 8 31, .CZ 8 36, .CZ 8 27, .CZ 9 18, .CZ 10 12, .CZ 10 15, .CZ 10 29, .CZ 10 31, .CZ 11 18, .CZ 11 21, .CZ 15 21, .CZ 30 21],
  .CX 4 7,
  .CX 4 14,
  .CX 4 29,
  .CX 4 30,
  .CX 4 31,
  .CX 4 18,
  .CX 4 20,
  .CX 4 21,
  .CX 4 22,
  .measureX 4 [] [.Z 5, .Z 7, .Z 10, .Z 12, .Z 14, .Z 15, .Z 29, .Z 32, .Z 26, .Z 18, .Z 22, .CZ 2 3, .CZ 2 5, .CZ 2 8, .CZ 2 12, .CZ 2 14, .CZ 2 15, .CZ 2 30, .CZ 2 32, .CZ 2 34, .CZ 2 26, .CZ 2 27, .CZ 2 18, .CZ 3 7, .CZ 3 9, .CZ 3 11, .CZ 3 12, .CZ 3 30, .CZ 3 34, .CZ 3 36, .CZ 3 19, .CZ 5 7, .CZ 5 8, .CZ 5 9, .CZ 5 10, .CZ 5 15, .CZ 5 29, .CZ 5 30, .CZ 5 36, .CZ 5 26, .CZ 5 27, .CZ 5 19, .CZ 7 9, .CZ 7 11, .CZ 7 12, .CZ 8 11, .CZ 8 14, .CZ 8 29, .CZ 8 30, .CZ 8 31, .CZ 8 36, .CZ 9 14, .CZ 9 15, .CZ 9 29, .CZ 9 36, .CZ 9 27, .CZ 9 18, .CZ 10 12, .CZ 10 14, .CZ 10 29, .CZ 10 36, .CZ 11 30, .CZ 11 31, .CZ 11 18, .CZ 12 15, .CZ 12 30, .CZ 12 32, .CZ 12 26, .CZ 12 19, .CZ 14 15, .CZ 14 32, .CZ 14 34],
  .CX 2 7,
  .CX 2 14,
  .CX 2 29,
  .CX 2 31,
  .CX 2 32,
  .CX 2 36,
  .CX 2 27,
  .CX 2 18,
  .CX 2 19,
  .measureX 2 [] [.Z 3, .Z 5, .Z 7, .Z 8, .Z 9, .Z 11, .Z 12, .Z 14, .Z 29, .Z 30, .Z 31, .Z 32, .Z 34, .Z 36, .Z 19, .Z 21, .CZ 3 7, .CZ 3 9, .CZ 3 14, .CZ 3 29, .CZ 3 31, .CZ 3 26, .CZ 5 8, .CZ 5 10, .CZ 5 15, .CZ 5 31, .CZ 5 32, .CZ 5 34, .CZ 5 36, .CZ 5 27, .CZ 5 18, .CZ 5 19, .CZ 7 8, .CZ 7 9, .CZ 7 10, .CZ 7 14, .CZ 7 30, .CZ 7 31, .CZ 7 34, .CZ 7 26, .CZ 7 22, .CZ 8 10, .CZ 8 12, .CZ 8 15, .CZ 8 29, .CZ 8 31, .CZ 8 32, .CZ 8 36, .CZ 8 26, .CZ 8 27, .CZ 9 11, .CZ 9 12, .CZ 9 29, .CZ 9 30, .CZ 9 32, .CZ 9 36, .CZ 9 27, .CZ 10 11, .CZ 10 12, .CZ 10 29, .CZ 10 31, .CZ 10 32, .CZ 10 36, .CZ 10 26, .CZ 10 27, .CZ 11 32, .CZ 12 29, .CZ 12 32, .CZ 12 36, .CZ 12 26, .CZ 12 27, .CZ 14 29, .CZ 14 30, .CZ 14 32, .CZ 14 34, .CZ 14 36, .CZ 14 27, .CZ 14 19, .CZ 15 29, .CZ 15 30, .CZ 15 31, .CZ 15 32, .CZ 15 36, .CZ 15 19, .CZ 29 34, .CZ 30 31],
  .CX 3 7,
  .CX 3 32,
  .CX 3 26,
  .CX 3 27,
  .CX 3 18,
  .CX 3 19,
  .CX 3 20,
  .measureX 3 [] [.Z 5, .Z 7, .Z 8, .Z 9, .Z 10, .Z 11, .Z 14, .Z 29, .Z 34, .Z 36, .Z 27, .Z 18, .Z 21, .CZ 5 11, .CZ 5 12, .CZ 5 14, .CZ 5 15, .CZ 5 30, .CZ 5 31, .CZ 5 32, .CZ 5 36, .CZ 5 27, .CZ 5 18, .CZ 5 22, .CZ 7 10, .CZ 7 11, .CZ 7 29, .CZ 7 30, .CZ 7 31, .CZ 7 32, .CZ 7 36, .CZ 7 27, .CZ 7 22, .CZ 8 11, .CZ 8 12, .CZ 8 15, .CZ 8 30, .CZ 8 34, .CZ 8 18, .CZ 8 19, .CZ 8 22, .CZ 9 11, .CZ 9 15, .CZ 9 31, .CZ 9 26, .CZ 9 27, .CZ 9 22, .CZ 10 11, .CZ 10 12, .CZ 10 14, .CZ 10 29, .CZ 10 36, .CZ 10 26, .CZ 10 27, .CZ 10 18, .CZ 10 22, .CZ 11 14, .CZ 11 29, .CZ 11 18, .CZ 12 15, .CZ 12 31, .CZ 12 32, .CZ 12 34, .CZ 12 36, .CZ 12 26, .CZ 12 27, .CZ 12 18, .CZ 12 19, .CZ 14 15, .CZ 14 31, .CZ 14 32, .CZ 14 34, .CZ 14 36, .CZ 14 26, .CZ 14 27, .CZ 14 18, .CZ 14 19, .CZ 15 29, .CZ 15 31, .CZ 15 32, .CZ 15 34, .CZ 15 36, .CZ 15 27, .CZ 15 18, .CZ 15 22, .CZ 29 32, .CZ 29 34, .CZ 29 36, .CZ 29 26, .CZ 29 27, .CZ 29 18, .CZ 30 31, .CZ 30 36, .CZ 30 26, .CZ 30 18, .CZ 30 22, .CZ 31 34, .CZ 31 36, .CZ 31 27],
  .CX 7 36,
  .CX 7 26,
  .CX 7 27,
  .CX 7 18,
  .CX 7 20,
  .measureX 7 [] [.Z 5, .Z 8, .Z 9, .Z 10, .Z 11, .Z 12, .Z 15, .Z 32, .Z 34, .Z 27, .Z 21, .Z 22, .CZ 5 9, .CZ 5 12, .CZ 5 14, .CZ 5 15, .CZ 5 29, .CZ 5 30, .CZ 8 9, .CZ 8 11, .CZ 8 14, .CZ 8 15, .CZ 8 30, .CZ 8 31, .CZ 8 34, .CZ 8 36, .CZ 8 26, .CZ 8 19, .CZ 8 22, .CZ 9 11, .CZ 9 30, .CZ 9 32, .CZ 9 26, .CZ 10 11, .CZ 10 15, .CZ 10 29, .CZ 10 31, .CZ 10 27, .CZ 10 22, .CZ 11 14, .CZ 11 29, .CZ 11 30, .CZ 11 32, .CZ 11 22, .CZ 12 31, .CZ 12 34, .CZ 12 26, .CZ 12 27, .CZ 12 18, .CZ 14 31, .CZ 14 34, .CZ 14 26, .CZ 14 27, .CZ 14 18, .CZ 15 30, .CZ 15 31, .CZ 15 22, .CZ 29 32, .CZ 29 34, .CZ 29 26, .CZ 29 22, .CZ 30 36, .CZ 30 26, .CZ 30 27, .CZ 30 22, .CZ 31 32, .CZ 31 34, .CZ 31 26, .CZ 31 27, .CZ 32 34, .CZ 32 19],
  .CX 36 26,
  .CX 36 27,
  .CX 36 19,
  .CX 36 20,
  .CX 36 22,
  .measureX 36 [] [.Z 5, .Z 8, .Z 12, .Z 29, .Z 27, .Z 18, .Z 19, .Z 21, .CZ 5 11, .CZ 5 30, .CZ 5 34, .CZ 5 18, .CZ 5 19, .CZ 5 22, .CZ 8 10, .CZ 8 11, .CZ 8 31, .CZ 8 32, .CZ 8 26, .CZ 8 18, .CZ 8 19, .CZ 9 11, .CZ 9 29, .CZ 9 30, .CZ 9 31, .CZ 9 32, .CZ 9 34, .CZ 9 27, .CZ 9 18, .CZ 10 14, .CZ 10 15, .CZ 10 29, .CZ 10 30, .CZ 10 31, .CZ 10 32, .CZ 10 34, .CZ 10 27, .CZ 10 18, .CZ 11 12, .CZ 11 14, .CZ 11 34, .CZ 11 18, .CZ 12 29, .CZ 12 30, .CZ 12 31, .CZ 12 34, .CZ 12 26, .CZ 12 27, .CZ 12 22, .CZ 14 29, .CZ 14 30, .CZ 14 31, .CZ 14 34, .CZ 14 26, .CZ 14 27, .CZ 14 22, .CZ 15 29, .CZ 15 31, .CZ 15 27, .CZ 15 18, .CZ 15 19, .CZ 15 22, .CZ 29 30, .CZ 29 31, .CZ 29 32, .CZ 29 26, .CZ 29 27, .CZ 30 31, .CZ 30 32, .CZ 30 34, .CZ 30 26, .CZ 30 27, .CZ 30 19, .CZ 31 27, .CZ 31 19, .CZ 31 22, .CZ 32 18, .CZ 32 19, .CZ 32 22],
  .CX 12 14,
  .measureX 12 [] [.Z 8, .Z 9, .Z 11, .Z 14, .Z 15, .Z 29, .Z 30, .Z 34, .Z 26, .Z 27, .Z 19, .CZ 5 8, .CZ 5 9, .CZ 5 10, .CZ 5 11, .CZ 8 14, .CZ 8 29, .CZ 8 30, .CZ 8 32, .CZ 8 19, .CZ 9 14, .CZ 9 29, .CZ 9 32, .CZ 9 34, .CZ 9 26, .CZ 10 11, .CZ 10 15, .CZ 10 30, .CZ 10 31, .CZ 10 32, .CZ 10 34, .CZ 10 26, .CZ 10 27, .CZ 11 14, .CZ 11 29, .CZ 11 30, .CZ 11 32, .CZ 11 19],
  .CX 29 31,
  .CX 29 32,
  .CX 29 27,
  .CX 29 18,
  .CX 29 20,
  .measureX 29 [] [.Z 5, .Z 8, .Z 10, .Z 14, .Z 32, .Z 34, .Z 27, .CZ 5 8, .CZ 5 10, .CZ 5 15, .CZ 5 32, .CZ 5 27, .CZ 5 18, .CZ 10 15, .CZ 14 15, .CZ 15 27, .CZ 32 34, .CZ 32 26, .CZ 32 27],
  .CX 14 30,
  .CX 14 31,
  .CX 14 26,
  .CX 14 27,
  .CX 14 18,
  .CX 14 20,
  .CX 14 22,
  .measureX 14 [] [.Z 5, .Z 9, .Z 32, .CZ 5 8, .CZ 5 9, .CZ 5 10, .CZ 5 11, .CZ 5 15, .CZ 5 34, .CZ 5 26, .CZ 5 27, .CZ 8 11, .CZ 8 32, .CZ 8 34, .CZ 8 22, .CZ 9 11, .CZ 9 15, .CZ 9 32, .CZ 9 34, .CZ 9 26, .CZ 9 27, .CZ 10 11, .CZ 10 32, .CZ 10 34, .CZ 10 22, .CZ 11 30, .CZ 11 32, .CZ 11 34, .CZ 11 19, .CZ 11 22, .CZ 15 30, .CZ 15 31, .CZ 15 32, .CZ 15 21, .CZ 15 22, .CZ 30 34, .CZ 30 27, .CZ 30 22, .CZ 31 27, .CZ 31 22, .CZ 32 27, .CZ 32 21, .CZ 34 27, .CZ 26 18],
  .CX 9 11,
  .CX 9 30,
  .measureX 9 [] [.Z 8, .Z 30, .Z 34, .Z 26, .Z 19, .CZ 8 10, .CZ 10 30, .CZ 10 34, .CZ 10 26, .CZ 10 19],
  .CX 8 11,
  .CX 8 31,
  .CX 8 32,
  .CX 8 26,
  .CX 8 18,
  .CX 8 19,
  .CX 8 21,
  .X 8,
  .measureX 8 [] [.Z 15, .Z 32, .Z 34, .Z 27, .Z 18, .Z 21, .CZ 5 34, .CZ 5 27, .CZ 5 22, .CZ 10 11, .CZ 10 18, .CZ 10 19, .CZ 11 34, .CZ 15 34, .CZ 15 19, .CZ 30 34, .CZ 32 18, .CZ 32 19, .CZ 34 26, .CZ 34 27, .CZ 26 18, .CZ 26 19, .CZ 18 19],
  .CX 30 32,
  .CX 30 26,
  .CX 30 21,
  .measureX 30 [] [.Z 11, .Z 15, .Z 32, .Z 19, .Z 22, .CZ 5 10, .CZ 5 11, .CZ 5 34, .CZ 5 27, .CZ 5 22, .CZ 10 11, .CZ 10 15, .CZ 10 32, .CZ 10 19, .CZ 10 22, .CZ 11 32, .CZ 11 19, .CZ 15 34, .CZ 15 18, .CZ 15 19, .CZ 15 22, .CZ 32 34, .CZ 32 27, .CZ 34 26, .CZ 34 27, .CZ 34 22, .CZ 26 27, .CZ 27 18, .CZ 27 19, .CZ 19 22],
  .measureX 31 [] [.Z 10, .Z 15, .Z 26, .CZ 5 34, .CZ 10 11, .CZ 10 27, .CZ 11 27],
  .CX 15 26,
  .CX 15 27,
  .CX 15 19,
  .CX 15 20,
  .CX 15 21,
  .measureX 15 [] [.Z 11, .CZ 5 10, .CZ 5 11, .CZ 10 11, .CZ 10 32, .CZ 10 34, .CZ 10 26, .CZ 11 32, .CZ 11 34, .CZ 11 26],
  .CX 25 24,
  .CX 25 23,
  .CX 25 22,
  .CX 25 20,
  .CX 25 18,
  .CX 25 11,
  .CX 25 10,
  .CX 24 25,
  .CX 24 23,
  .CX 24 22,
  .CX 24 20,
  .CX 24 18,
  .CX 24 11,
  .CX 24 10,
  .CX 25 24,
  .CX 23 25,
  .CX 23 22,
  .CX 23 20,
  .CX 23 18,
  .CX 23 11,
  .CX 23 10,
  .CX 25 23,
  .CX 22 25,
  .CX 22 20,
  .CX 22 18,
  .CX 22 11,
  .CX 22 10,
  .CX 25 22,
  .CX 21 25,
  .CX 21 20,
  .CX 21 19,
  .CX 21 27,
  .CX 21 36,
  .CX 21 32,
  .CX 21 16,
  .CX 21 13,
  .CX 21 11,
  .CX 21 10,
  .CX 21 9,
  .CX 21 3,
  .CX 20 25,
  .CX 20 21,
  .CX 20 19,
  .CX 20 27,
  .CX 20 36,
  .CX 20 35,
  .CX 20 34,
  .CX 20 29,
  .CX 20 16,
  .CX 20 15,
  .CX 20 13,
  .CX 20 12,
  .CX 20 9,
  .CX 20 8,
  .CX 20 3,
  .CX 20 2,
  .CX 19 20,
  .CX 19 18,
  .CX 19 26,
  .CX 19 35,
  .CX 19 33,
  .CX 19 32,
  .CX 19 29,
  .CX 19 15,
  .CX 19 12,
  .CX 19 10,
  .CX 19 8,
  .CX 19 2,
  .CX 18 25,
  .CX 18 21,
  .CX 18 20,
  .CX 18 26,
  .CX 18 36,
  .CX 18 35,
  .CX 18 34,
  .CX 18 32,
  .CX 18 31,
  .CX 18 30,
  .CX 18 29,
  .CX 18 16,
  .CX 18 15,
  .CX 18 14,
  .CX 18 13,
  .CX 18 12,
  .CX 18 11,
  .CX 18 10,
  .CX 18 17,
  .CX 18 9,
  .CX 18 8,
  .CX 18 7,
  .CX 18 6,
  .CX 18 4,
  .CX 18 3,
  .CX 18 2,
  .CX 18 1,
  .CX 27 21,
  .CX 27 20,
  .CX 27 19,
  .CX 27 18,
  .CX 27 26,
  .CX 27 36,
  .CX 27 35,
  .CX 27 34,
  .CX 27 33,
  .CX 27 31,
  .CX 27 29,
  .CX 27 16,
  .CX 27 15,
  .CX 27 13,
  .CX 27 12,
  .CX 27 9,
  .CX 27 8,
  .CX 27 7,
  .CX 27 6,
  .CX 27 5,
  .CX 27 3,
  .CX 27 2,
  .CX 27 1,
  .CX 18 27,
  .CX 26 20,
  .CX 26 35,
  .CX 26 34,
  .CX 26 15,
  .CX 26 12,
  .CX 26 10,
  .CX 26 8,
  .CX 26 2,
  .CX 20 26,
  .CX 36 21,
  .CX 21 36,
  .CX 35 20,
  .CX 20 35,
  .CX 34 25,
  .CX 34 19,
  .CX 34 18,
  .CX 34 27,
  .CX 34 33,
  .CX 34 31,
  .CX 34 30,
  .CX 34 11,
  .CX 34 7,
  .CX 34 6,
  .CX 34 5,
  .CX 34 1,
  .CX 27 34,
  .CX 33 19,
  .CX 19 33,
  .CX 32 25,
  .CX 32 18,
  .CX 32 27,
  .CX 32 26,
  .CX 32 35,
  .CX 32 31,
  .CX 32 30,
  .CX 32 29,
  .CX 32 15,
  .CX 32 12,
  .CX 32 10,
  .CX 32 8,
  .CX 32 7,
  .CX 32 6,
  .CX 32 5,
  .CX 32 2,
  .CX 32 1,
  .CX 35 32,
  .CX 31 18,
  .CX 18 31,
  .CX 30 27,
  .CX 27 30,
  .CX 29 26,
  .CX 26 29,
  .CX 16 36,
  .CX 36 16,
  .CX 15 35,
  .CX 35 15,
  .CX 14 34,
  .CX 34 14,
  .CX 13 16,
  .CX 16 13,
  .CX 12 15,
  .CX 15 12,
  .CX 11 25,
  .CX 11 32,
  .CX 11 31,
  .CX 11 10,
  .CX 31 11,
  .CX 10 25,
  .CX 10 32,
  .CX 10 31,
  .CX 10 29,
  .CX 10 12,
  .CX 10 11,
  .CX 10 8,
  .CX 10 7,
  .CX 10 2,
  .CX 10 1,
  .CX 11 10,
  .CX 17 14,
  .CX 14 17,
  .CX 9 13,
  .CX 13 9,
  .CX 8 12,
  .CX 12 8,
  .CX 7 11,
  .CX 11 7,
  .CX 6 10,
  .CX 10 6,
  .CX 5 17,
  .CX 5 9,
  .CX 5 8,
  .CX 5 7,
  .CX 5 6,
  .CX 5 4,
  .CX 5 3,
  .CX 5 2,
  .CX 5 1,
  .CX 6 5,
  .CX 4 17,
  .CX 17 4,
  .CX 3 9,
  .CX 9 3,
  .CX 2 8,
  .CX 8 2,
  .CX 1 7,
  .CX 7 1,
  .X 25,
  .CX 6 7,
  .X 7,
  .CX 6 10
]
def inputColumns : Cols := [7687697232696013035490465480201479025983241823794691621558168976140934720122093268938148043346259333988919315645138393722043075239520827405922921108820848699737596665296647163816890855116005321601037974542306666142059861077617469832735753659129776181086257152, 7687693444969798610225496304158821400708122504356994246980073964815325161122547994963453903686419572156266242316155632044893319270650594152013676455409665369284014353948719836278436196598767349558260011127447564076499449696980932221760431985646535725922211157, 7687570989258518260848503419482384060892570186258236921537857733078060865979460122305646562430345564690692890957731022735801617519845131398343767129053081556091044886656106855883903757608657520005498534800008974590319464627359369218329919711974682975684421222, 7687564318618085346893361155983968470840702082542828120351972706243520859993519543409479851814405092427351393623521902213472796425810131612535484983690821266781441552039493228518433746721910635786954383589876554349398075053395232858025509914993015967654115448, 7687563845155104729096125524269777101194669702261881560883682148729693808007580113746667686208031269839622601100956829044149790003904517006453324832863491559485916422083889125254268048482832209418189708642477445829693758314596404740617793743953183992082104192, 7687563844229426400087998931319142450322735007812069512944884169228649357566823494905712458764146858388571015333834246530484725596723843960642318145831451773221772707408320916826540832685066061970518941258910009437930750020522231981702737642365386167347544064, 7687667906458400517130192155366730942948627322040589738471325719625336754827307075402676926256222079025717486028236377843628622611013872699693109608377023408939648161348312699491851879903799206168904423175957973793127504681346074600356323082581164247662723072, 7687697232696013035490465480201479025983241823794691621558168975848938520594272774945113060581440689195752691181230558164974754098126274130226293881697966204865095256301381237030878015541622630014758410785170366351469207732794556661856873263851022886685900800, 7687697232696013035490465480201479025983241823794691621558168975848938520594272774945113060581440689195752691181230558164974754096739886398688383232020842959568910782899976426482665362402407800047631250459761964719812559133629388771070007815229399706277773312, 0, 3787726214425264969176042657625275119319437697374578095011325609558999545273974694139659839761832653073328982761677149755971642902948030059512989597514596666014784364402914271233687717552657399271220484725105534817484776115708366532634886812284138203818, 2562475493849743322258892205756881238440584416097480280624262648208194110254684494465049183924325191393643873308194485240904198041169633721519549563137515725085778739745633342100320321150899346085544043680704660343638998736013523881086824759232733358660046028, 3075047749822264710590014924108783748365819663208989839638716514134456934352795695657918033866520241036147153651205792621437216639312525786172065127833369752007126320739733155311046795807439812455786156045419836515498944643554375484760030678932091600054055152, 3617700921716651650625838055609890982863552438764501905270582984329976160679735076708896726144158471853286210883173920811193482893521682168145803119297452203018931823557974725539871587219197428860499329300269705280157748735596174128910340635811641888476299008, 3828849849557027999397302021314396687460832022256993153521997923249744699269492304076510815774163002927893964445235590945668516478638328403956149983210792760246515106921336005516620117843370172268992205093477327086457709127921104230603898872303647664763764736, 3843701801778695869095367431450915297023044404544162786053369364238857060987013524116617848837676361317516036440051371107275385926239474904361890044742244049754772082941849559873941964721013288653806434909047851571784042737764443389975708941910246693565104128, 3843995247536069109546599364274479928164693408548502115316418846219638437300781882389401982410724228128310277247567221354226201544494863060514412462212551730001967037866149177501520338734683961116786926398314151518586328436938787081741617562018009544287846400, 2772669694120814859578414184143083703436437075375816575170479580509309016137068436342056378420469145778496115560854460574663180288, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem packed_checked : (eval (2^860-1) candidate inputColumns).1=true ∧ (eval (2^860-1) reference inputColumns).1=true ∧ (eval (2^860-1) candidate inputColumns).2=(eval (2^860-1) reference inputColumns).2 := by decide +kernel

open ECDSAAdd.Entrant.MeasuredCodec5
def rowInputs : List Nat := [2, 1028, 2054, 3080, 4106, 5132, 6158, 7184, 8210, 9236, 10262, 11288, 12314, 13340, 14366, 15392, 16418, 17444, 18470, 19496, 20522, 21548, 22574, 23600, 24626, 25652, 26678, 27704, 28730, 29756, 30782, 31808, 32834, 33860, 34886, 35912, 36938, 37964, 38990, 40016, 41042, 42068, 43094, 44120, 45146, 46172, 47198, 48224, 49250, 50276, 51302, 52328, 53354, 54380, 55406, 56432, 57458, 58484, 59510, 60536, 61562, 62588, 63614, 64640, 1032, 2058, 4110, 5136, 7188, 8214, 10266, 11292, 13344, 14370, 16422, 17448, 19500, 20526, 22578, 23604, 25656, 26682, 28734, 29760, 31812, 1036, 2062, 3088, 4114, 6166, 7192, 8218, 9244, 11296, 12322, 13348, 14374, 17452, 19504, 1040, 2066, 3092, 4118, 5144, 6170, 8222, 9248, 10274, 11300, 12326, 13352, 15404, 17456, 19508, 1044, 2070, 4122, 5148, 7200, 11304, 13356, 1048, 2074, 3100, 4126, 5152, 6178, 7204, 9256, 13360, 15412, 17464, 1052, 2078, 3104, 4130, 5156, 6182, 7208, 9260, 11312, 15416, 17468, 19520, 1056, 2082, 4134, 7212, 11316, 13368, 17472, 19524, 1060, 2086, 3112, 5164, 7216, 11320, 13372, 15424, 19528, 1064, 2090, 3116, 5168, 7220, 13376, 15428, 17480, 21584, 1068, 2094, 19536, 23640, 1072, 2098, 3124, 21592, 25696, 1076, 2102, 3128, 23648, 27752, 1080, 2106, 25704, 29808, 1084, 2110, 3136, 27760, 31864, 1088, 2114, 3140, 29816, 33920, 1092, 31872, 1096, 1100, 1104, 1108, 1112, 1116, 1120, 1124, 1128, 1132, 1136, 1140, 1144, 1148, 1152, 2, 261124, 260102, 259080, 258058, 257036, 256014, 254992, 253970, 252948, 251926, 250904, 249882, 248860, 247838, 246816, 245794, 244772, 243750, 242728, 241706, 240684, 239662, 238640, 237618, 236596, 235574, 234552, 233530, 232508, 231486, 230464, 229442, 228420, 227398, 226376, 225354, 224332, 223310, 222288, 221266, 220244, 219222, 218200, 217178, 216156, 215134, 214112, 213090, 212068, 211046, 210024, 209002, 207980, 206958, 205936, 204914, 203892, 202870, 201848, 200826, 199804, 198782, 197760, 261128, 260106, 258062, 257040, 254996, 253974, 251930, 250908, 248864, 247842, 245798, 244776, 242732, 241710, 239666, 238644, 236600, 235578, 233534, 232512, 230468, 261132, 260110, 259088, 258066, 256022, 255000, 253978, 252956, 250912, 249890, 248868, 247846, 244780, 242736, 261136, 260114, 259092, 258070, 257048, 256026, 253982, 252960, 251938, 250916, 249894, 248872, 246828, 244784, 242740, 261140, 260118, 258074, 257052, 255008, 250920, 248876, 261144, 260122, 259100, 258078, 257056, 256034, 255012, 252968, 248880, 246836, 244792, 261148, 260126, 259104, 258082, 257060, 256038, 255016, 252972, 250928, 246840, 244796, 242752, 261152, 260130, 258086, 255020, 250932, 248888, 244800, 242756, 261156, 260134, 259112, 257068, 255024, 250936, 248892, 246848, 242760, 261160, 260138, 259116, 257072, 255028, 248896, 246852, 244808, 240720, 261164, 260142, 242768, 238680, 261168, 260146, 259124, 240728, 236640, 261172, 260150, 259128, 238688, 234600, 261176, 260154, 236648, 232560, 261180, 260158, 259136, 234608, 230520, 261184, 260162, 259140, 232568, 228480, 261188, 230528, 261192, 261196, 261200, 261204, 261208, 261212, 261216, 261220, 261224, 261228, 261232, 261236, 261240, 261244, 261248, 1025, 2051, 3077, 4103, 5129, 6155, 7181, 8207, 9233, 10259, 11285, 12311, 13337, 14363, 15389, 16415, 17441, 18467, 19493, 20519, 21545, 22571, 23597, 24623, 25649, 26675, 27701, 28727, 29753, 30779, 31805, 32831, 33857, 34883, 35909, 36935, 37961, 38987, 40013, 41039, 42065, 43091, 44117, 45143, 46169, 47195, 48221, 49247, 50273, 51299, 52325, 53351, 54377, 55403, 56429, 57455, 58481, 59507, 60533, 61559, 62585, 63611, 64637, 65663, 4099, 5125, 7177, 8203, 10255, 11281, 13333, 14359, 16411, 17437, 19489, 20515, 22567, 23593, 25645, 26671, 28723, 29749, 31801, 32827, 34879, 6147, 7173, 8199, 9225, 11277, 12303, 13329, 14355, 16407, 17433, 18459, 19485, 22563, 24615, 8195, 9221, 10247, 11273, 12299, 13325, 15377, 16403, 17429, 18455, 19481, 20507, 22559, 24611, 26663, 10243, 11269, 13321, 14347, 16399, 20503, 22555, 12291, 13317, 14343, 15369, 16395, 17421, 18447, 20499, 24603, 26655, 28707, 14339, 15365, 16391, 17417, 18443, 19469, 20495, 22547, 24599, 28703, 30755, 32807, 16387, 17413, 19465, 22543, 26647, 28699, 32803, 34855, 18435, 19461, 20487, 22539, 24591, 28695, 30747, 32799, 36903, 20483, 21509, 22535, 24587, 26639, 32795, 34847, 36899, 41003, 22531, 23557, 40999, 45103, 24579, 25605, 26631, 45099, 49203, 26627, 27653, 28679, 49199, 53303, 28675, 29701, 53299, 57403, 30723, 31749, 32775, 57399, 61503, 32771, 33797, 34823, 61499, 65603, 34819, 65599, 36867, 38915, 40963, 43011, 45059, 47107, 49155, 51203, 53251, 55299, 57347, 59395, 61443, 63491, 65539, 1025, 2559, 3581, 4603, 5625, 6647, 7669, 8691, 9713, 10735, 11757, 12779, 13801, 14823, 15845, 16867, 17889, 18911, 19933, 20955, 21977, 22999, 24021, 25043, 26065, 27087, 28109, 29131, 30153, 31175, 32197, 33219, 34241, 35263, 36285, 37307, 38329, 39351, 40373, 41395, 42417, 43439, 44461, 45483, 46505, 47527, 48549, 49571, 50593, 51615, 52637, 53659, 54681, 55703, 56725, 57747, 58769, 59791, 60813, 61835, 62857, 63879, 64901, 65923, 4607, 5629, 7673, 8695, 10739, 11761, 13805, 14827, 16871, 17893, 19937, 20959, 23003, 24025, 26069, 27091, 29135, 30157, 32201, 33223, 35267, 6655, 7677, 8699, 9721, 11765, 12787, 13809, 14831, 16875, 17897, 18919, 19941, 23007, 25051, 8703, 9725, 10747, 11769, 12791, 13813, 15857, 16879, 17901, 18923, 19945, 20967, 23011, 25055, 27099, 10751, 11773, 13817, 14839, 16883, 20971, 23015, 12799, 13821, 14843, 15865, 16887, 17909, 18931, 20975, 25063, 27107, 29151, 14847, 15869, 16891, 17913, 18935, 19957, 20979, 23023, 25067, 29155, 31199, 33243, 16895, 17917, 19961, 23027, 27115, 29159, 33247, 35291, 18943, 19965, 20987, 23031, 25075, 29163, 31207, 33251, 37339, 20991, 22013, 23035, 25079, 27123, 33255, 35299, 37343, 41431, 23039, 24061, 41435, 45523, 25087, 26109, 27131, 45527, 49615, 27135, 28157, 29179, 49619, 53707, 29183, 30205, 53711, 57799, 31231, 32253, 33275, 57803, 61891, 33279, 34301, 35323, 61895, 65983, 35327, 65987, 37375, 39423, 41471, 43519, 45567, 47615, 49663, 51711, 53759, 55807, 57855, 59903, 61951, 63999, 66047]
def rowInput (r : Fin 860) : Nat := (rowInputs[r.val]?).getD 0

theorem input_length : inputColumns.length=40 := by decide +kernel
theorem columns_correct : ∀q : Fin 40,
    get inputColumns q.val = packBits (rowInputs.map (fun x => x.testBit q.val)) := by decide +kernel

theorem finite_input_bits (r : Fin 860) (q : Fin 40) :
    (rowInput r).testBit q.val=(get inputColumns q.val).testBit r.val := by
  rw [columns_correct q,pack_rows]
  rfl

theorem input_bounds : ∀r : Fin 860,rowInput r<2^40 := by decide +kernel

theorem input_rel (r : Fin 860) : Rel inputColumns (rowInput r) r.val := by
  intro q
  by_cases hq:q<40
  · exact finite_input_bits r ⟨q,hq⟩
  · have q40:40≤q:=Nat.le_of_not_gt hq
    have qb:inputColumns.length≤q := by rw [input_length];exact q40
    have z:get inputColumns q=0 := by
      change (inputColumns[q]?).getD 0 = 0
      simp only [List.getElem?_eq_none qb,Option.getD_none]
    rw [z,Nat.zero_testBit]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (input_bounds r)
      (Nat.pow_le_pow_right (by decide) q40))

theorem mask_bits : ∀r : Fin 860,(2^860-1).testBit r.val=true := by decide +kernel

theorem candidate_targets : ∀i∈candidate,target i < inputColumns.length := by
  rw [input_length]
  decide +kernel

theorem reference_targets : ∀i∈reference,target i < inputColumns.length := by
  rw [input_length]
  decide +kernel

attribute [local irreducible] safe bitRun

theorem row_all (r : Fin 860) : safe candidate (rowInput r)=true ∧
    safe reference (rowInput r)=true ∧ bitRun candidate (rowInput r)=bitRun reference (rowInput r) := by
  have hp:=eval_sound (2^860-1) r.val (mask_bits r) candidate inputColumns
    (rowInput r) candidate_targets (input_rel r) packed_checked.1
  have hq:=eval_sound (2^860-1) r.val (mask_bits r) reference inputColumns
    (rowInput r) reference_targets (input_rel r) packed_checked.2.1
  refine ⟨hp.1,hq.1,?_⟩
  apply Nat.eq_of_testBit_eq
  intro q
  exact (hp.2 q).trans ((congrArg (fun s : Cols => (get s q).testBit r.val) packed_checked.2.2).trans
    (hq.2 q).symm)

theorem compact_run (r : Fin 860) (m n : List Bool) (ph : Bool) :
    run candidate m ⟨ph,bitsOf (rowInput r)⟩ = run reference n ⟨ph,bitsOf (rowInput r)⟩ := by
  have h:=row_all r
  rw [run_sim candidate m ph (rowInput r),sim_safe candidate _ h.1 m ph,
    run_sim reference n ph (rowInput r),sim_safe reference _ h.2.1 n ph,h.2.2]

def label (q : Nat) : Wire := (sites[q]?).getD 0

theorem label_inj : ∀a∈Finset.range 40,∀b∈Finset.range 40,label a=label b → a=b := by
  have finite : ∀a b : Fin 40,label a=label b → a=b := by decide +kernel
  intro a ha b hb eq
  exact congrArg Fin.val (finite ⟨a,Finset.mem_range.mp ha⟩ ⟨b,Finset.mem_range.mp hb⟩ eq)

theorem candidate_remap : renameProgram label candidate=cand6 := by decide +kernel
theorem reference_remap : renameProgram label reference=ref := by decide +kernel

theorem rows_length : rows.length=860 := by decide +kernel

def rowAt (r : Fin 860) : Bool × Bool × Nat × Nat := (rows[r.val]?).getD (false,false,0,0)

theorem row_compat : ∀r : Fin 860, ∀q : Fin 40,
    pre505 (rowAt r).1 (rowAt r).2.1 (rowAt r).2.2.1 (rowAt r).2.2.2 (label q.val) =
      bitsOf (rowInput r) q.val := by decide +kernel

theorem candidate_support : wires candidate ⊆ Finset.range 40 :=
  support_of_check candidate 40 (by decide +kernel)
theorem reference_support : wires reference ⊆ Finset.range 40 :=
  support_of_check reference 40 (by decide +kernel)

theorem sample_index (r : Fin 860) (m n : List Bool) :
    run cand6 m ⟨false,pre505 (rowAt r).1 (rowAt r).2.1 (rowAt r).2.2.1 (rowAt r).2.2.2⟩ =
      run ref n ⟨false,pre505 (rowAt r).1 (rowAt r).2.1 (rowAt r).2.2.1 (rowAt r).2.2.2⟩ := by
  let raw : State := ⟨false,pre505 (rowAt r).1 (rowAt r).2.1 (rowAt r).2.2.1 (rowAt r).2.2.2⟩
  let logical : State := ⟨false,bitsOf (rowInput r)⟩
  have input : ∀q∈Finset.range 40, logical.basis q=raw.basis (label q) := by
    intro q hq
    exact (row_compat r ⟨q,Finset.mem_range.mp hq⟩).symm
  have hc := run_rename_pool label (Finset.range 40) label_inj candidate candidate_support m logical raw rfl input
  have hr := run_rename_pool label (Finset.range 40) label_inj reference reference_support n logical raw rfl input
  have same := compact_run r m n false
  have eq : run (renameProgram label candidate) m raw = run (renameProgram label reference) n raw := by
    apply State.extensionality
    · exact hc.1.trans ((congrArg State.phase same).trans hr.1.symm)
    · funext q
      by_cases hq : q ∈ (Finset.range 40).image label
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
        exact (hc.2 j hj).trans ((congrArg (fun s : State => s.basis j) same).trans (hr.2 j hj).symm)
      · exact (run_rename_pool_outside label (Finset.range 40) candidate candidate_support m raw q hq).trans
          (run_rename_pool_outside label (Finset.range 40) reference reference_support n raw q hq).symm
  simpa only [candidate_remap,reference_remap,raw] using eq

theorem sample_fast (r : Bool × Bool × Nat × Nat) (hr : r ∈ rows) (m n : List Bool) :
    run cand6 m ⟨false,pre505 r.1 r.2.1 r.2.2.1 r.2.2.2⟩ =
      run ref n ⟨false,pre505 r.1 r.2.1 r.2.2.1 r.2.2.2⟩ := by
  obtain ⟨i, hi, hir⟩ := List.getElem_of_mem hr
  let k : Fin 860 := ⟨i,by simpa only [rows_length] using hi⟩
  have hrow : rowAt k = r := by
    change (rows[i]?).getD (false,false,0,0) = r
    simp only [List.getElem?_eq_getElem hi,Option.getD_some,hir]
  simpa only [hrow] using sample_index k m n


theorem tick_counts : toffoliCount tick505 = 12 ∧ measurementCount tick505 = 7 := by decide +kernel

theorem cand_counts : toffoliCount cand6 = 31 ∧ measurementCount cand6 = 27 := by
  simp only [cand6, toffoliCount_append, measurementCount_append]
  decide +kernel

def used : List Wire := sites.filter (fun q => decide (q ≠ 1559 ∧ q ≠ 1560 ∧ q ≠ 1561))

theorem bsupport0 : wires block0 ⊆ used.toFinset := by decide +kernel
theorem bphysical0 : GatePhysical block0 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport1 : wires block1 ⊆ used.toFinset := by decide +kernel
theorem bphysical1 : GatePhysical block1 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport2 : wires block2 ⊆ used.toFinset := by decide +kernel
theorem bphysical2 : GatePhysical block2 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport3 : wires block3 ⊆ used.toFinset := by decide +kernel
theorem bphysical3 : GatePhysical block3 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport4 : wires block4 ⊆ used.toFinset := by decide +kernel
theorem bphysical4 : GatePhysical block4 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport5 : wires block5 ⊆ used.toFinset := by decide +kernel
theorem bphysical5 : GatePhysical block5 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport6 : wires block6 ⊆ used.toFinset := by decide +kernel
theorem bphysical6 : GatePhysical block6 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport7 : wires block7 ⊆ used.toFinset := by decide +kernel
theorem bphysical7 : GatePhysical block7 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport8 : wires block8 ⊆ used.toFinset := by decide +kernel
theorem bphysical8 : GatePhysical block8 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport9 : wires block9 ⊆ used.toFinset := by decide +kernel
theorem bphysical9 : GatePhysical block9 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport10 : wires block10 ⊆ used.toFinset := by decide +kernel
theorem bphysical10 : GatePhysical block10 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport11 : wires block11 ⊆ used.toFinset := by decide +kernel
theorem bphysical11 : GatePhysical block11 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport12 : wires block12 ⊆ used.toFinset := by decide +kernel
theorem bphysical12 : GatePhysical block12 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport13 : wires block13 ⊆ used.toFinset := by decide +kernel
theorem bphysical13 : GatePhysical block13 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport14 : wires block14 ⊆ used.toFinset := by decide +kernel
theorem bphysical14 : GatePhysical block14 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport15 : wires block15 ⊆ used.toFinset := by decide +kernel
theorem bphysical15 : GatePhysical block15 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport16 : wires block16 ⊆ used.toFinset := by decide +kernel
theorem bphysical16 : GatePhysical block16 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport17 : wires block17 ⊆ used.toFinset := by decide +kernel
theorem bphysical17 : GatePhysical block17 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport18 : wires block18 ⊆ used.toFinset := by decide +kernel
theorem bphysical18 : GatePhysical block18 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport19 : wires block19 ⊆ used.toFinset := by decide +kernel
theorem bphysical19 : GatePhysical block19 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport20 : wires block20 ⊆ used.toFinset := by decide +kernel
theorem bphysical20 : GatePhysical block20 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport21 : wires block21 ⊆ used.toFinset := by decide +kernel
theorem bphysical21 : GatePhysical block21 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport22 : wires block22 ⊆ used.toFinset := by decide +kernel
theorem bphysical22 : GatePhysical block22 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport23 : wires block23 ⊆ used.toFinset := by decide +kernel
theorem bphysical23 : GatePhysical block23 := Forward11Width.physical_of_all _ (by decide +kernel)

theorem tick_support : wires tick505 ⊆ sites.toFinset := by decide +kernel
theorem five_sub : Five506.candSites.toFinset ⊆ sites.toFinset := by decide +kernel
theorem used_sub : used.toFinset ⊆ sites.toFinset := by decide +kernel
theorem cused : wires cand6 ⊆ used.toFinset := by
  simp only [cand6, wires_append, Finset.union_subset_iff, bsupport0, bsupport1, bsupport2, bsupport3, bsupport4, bsupport5, bsupport6, bsupport7, bsupport8, bsupport9, bsupport10, bsupport11, bsupport12, bsupport13, bsupport14, bsupport15, bsupport16, bsupport17, bsupport18, bsupport19, bsupport20, bsupport21, bsupport22, bsupport23, and_self]
theorem csupport : wires cand6 ⊆ sites.toFinset := cused.trans used_sub
theorem support2 : wires ref ⊆ sites.toFinset := by
  simp only [ref, wires_append, Finset.union_subset_iff]
  exact ⟨tick_support, Five506.csupport.trans five_sub⟩
theorem physical : GatePhysical cand6 := by
  simp only [cand6, gatePhysical_append, bphysical0, bphysical1, bphysical2, bphysical3, bphysical4, bphysical5, bphysical6, bphysical7, bphysical8, bphysical9, bphysical10, bphysical11, bphysical12, bphysical13, bphysical14, bphysical15, bphysical16, bphysical17, bphysical18, bphysical19, bphysical20, bphysical21, bphysical22, bphysical23, and_self]

theorem pre_supp (g s : Bool) (u v : Nat) : ∀ q, pre505 g s u v q = true → q ∈ sites := by
  intro q h
  by_contra hn
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  simp_all [pre505]

theorem sample (r : Bool × Bool × Nat × Nat) (hr : r ∈ rows) (m n : List Bool) :
    run cand6 m ⟨false,pre505 r.1 r.2.1 r.2.2.1 r.2.2.2⟩ = run ref n ⟨false,pre505 r.1 r.2.1 r.2.2.1 r.2.2.2⟩ :=
  sample_fast r hr m n

theorem on_site (r : Bool × Bool × Nat × Nat) (hr : r ∈ rows) (st : State)
    (bits : ∀ q ∈ sites, st.basis q = pre505 r.1 r.2.1 r.2.2.1 r.2.2.2 q) (m n : List Bool) :
    run cand6 m st = run ref n st :=
  Stack5.local_replace cand6 ref sites.toFinset csupport support2 st
    ⟨false,pre505 r.1 r.2.1 r.2.2.1 r.2.2.2⟩ m n (fun q hq => bits q (List.mem_toFinset.mp hq)) (sample r hr m n)


theorem signed8_cases (a b c d e f g h : Wire) (s : BasisState) (v : Int)
    (hh : signedRegValue [a,b,c,d,e,f,g,h] s = v) :
    s a = decide (v % 2 = 1) ∧ s b = decide (v / 2 % 2 = 1) ∧ s c = decide (v / 4 % 2 = 1) ∧
      s d = decide (v / 8 % 2 = 1) ∧ s e = decide (v / 16 % 2 = 1) ∧ s f = decide (v / 32 % 2 = 1) ∧
      s g = decide (v / 64 % 2 = 1) ∧ s h = decide (v < 0) := by
  unfold signedRegValue signedDecode at hh
  simp only [regValue,List.length] at hh
  cases ha : s a <;> cases hb : s b <;> cases hc : s c <;> cases hd : s d <;> cases he : s e <;>
    cases hf : s f <;> cases hg : s g <;> cases hi : s h <;>
    simp [ha,hb,hc,hd,he,hf,hg,hi] at hh <;> subst hh <;> decide

theorem retainedA505 : (W.compactSkywalkSignPoolA base 505).retained =
    [base 505,base 506,base 507,base 508,base 509,base 510,base 511,base 512] := by decide +kernel
theorem retainedB505 : (W.compactSkywalkSignPoolB base 505).retained =
    [base 770,base 771,base 772,base 773,base 774,base 775,base 776,base 777] := by decide +kernel
theorem releasedA505 : ∀ q ∈ [base 513], q ∈ (W.compactSkywalkSignPoolA base 505).released := by decide +kernel
theorem releasedB505 : ∀ q ∈ ([794, 795, 796, 797, 798, 799, 800, 801, 802, 803] : List Wire), q ∈ (W.compactSkywalkSignPoolB base 505).released := by decide +kernel

theorem raw505 (x : Nat) (hx0 : 0<x) (hx : x<p) (raw : State)
    (hraw : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 505 raw.basis) :
    ∃ G S : Bool, ∃ u v : Nat, u+v ≤ 64 ∧ 0 < v ∧ v%2=1 ∧ u.gcd v = 1 ∧
      ∀ q∈sites, raw.basis q = pre505 G S u v q := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := (StackOB5.prime_facts x hx0 hx).2.2.2
  have fields := (W.compactSkywalkStage_fields_iff base _ 505 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨readA, readB, prev, -, future, carry, -, cleanA, cleanB⟩ := fields
  obtain ⟨G, S, encoded⟩ := SkywalkTrace.iter_encoded 505 false false (SkywalkNat.init x p) hp0 hpo
  have sum := W.iter_sum_width x p 505 hp0 hx0 hpo hp hx cop (by omega)
  have valid := SkywalkNat.iter_valid 505 (SkywalkNat.init x p) hp0 hpo
  change (SkywalkNat.step^[505] (SkywalkNat.init x p)).u+
    (SkywalkNat.step^[505] (SkywalkNat.init x p)).v ≤ 2^(511-505) at sum
  change SkywalkTrace.next^[505] (SkywalkRails.encode false false (x : Int) (p : Int)) =
    SkywalkRails.encode G S ((SkywalkNat.step^[505] (SkywalkNat.init x p)).u : Int)
      ((SkywalkNat.step^[505] (SkywalkNat.init x p)).v : Int) at encoded
  generalize SkywalkNat.step^[505] (SkywalkNat.init x p) = z at encoded sum valid
  have sixtyfour : (2:Nat)^(511-505) = 64 := by norm_num
  rw [sixtyfour] at sum
  rw [encoded, retainedA505] at readA
  rw [encoded, retainedB505] at readB
  rw [encoded] at prev
  have bA := signed8_cases _ _ _ _ _ _ _ _ raw.basis _ readA
  have bB := signed8_cases _ _ _ _ _ _ _ _ raw.basis _ readB
  have cK : ∀ k, k < 257 → raw.basis (base (1540+k)) = false := fun k hk =>
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1540+k, by simp; omega, rfl⟩)
  have rel : ∀ q ∈ [base 513], raw.basis q = false := fun q hq => cleanA q (releasedA505 q hq)
  have relB : ∀ q ∈ ([794, 795, 796, 797, 798, 799, 800, 801, 802, 803] : List Wire), raw.basis q = false := fun q hq => cleanB q (releasedB505 q hq)
  have prev' : raw.basis (base 504) = G := by
    have h : skywalkPoolPreviousId 505 = 504 := rfl
    rw [h] at prev
    cases G <;> simpa [SkywalkRails.encode] using prev
  refine ⟨G,S,z.u,z.v,sum,valid.1,valid.2.1,valid.2.2.trans cop,?_⟩
  intro q hq
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prev'
  · simpa [pre505] using bA.1
  · exact bA.2.1
  · exact bA.2.2.1
  · exact bA.2.2.2.1
  · exact bA.2.2.2.2.1
  · exact bA.2.2.2.2.2.1
  · exact bA.2.2.2.2.2.2.1
  · exact bA.2.2.2.2.2.2.2
  · exact rel (base 513) (by decide)
  · simpa [pre505] using bB.1
  · exact bB.2.1
  · exact bB.2.2.1
  · exact bB.2.2.2.1
  · exact bB.2.2.2.2.1
  · exact bB.2.2.2.2.2.1
  · exact bB.2.2.2.2.2.2.1
  · exact bB.2.2.2.2.2.2.2
  · exact relB 794 (by decide)
  · exact relB 795 (by decide)
  · exact relB 796 (by decide)
  · exact relB 797 (by decide)
  · exact relB 798 (by decide)
  · exact relB 799 (by decide)
  · exact relB 800 (by decide)
  · exact relB 801 (by decide)
  · exact relB 802 (by decide)
  · exact relB 803 (by decide)
  · exact (future 505 (by omega) (by omega)).2
  · exact (future 506 (by omega) (by omega)).2
  · exact (future 507 (by omega) (by omega)).2
  · exact (future 508 (by omega) (by omega)).2
  · exact (future 509 (by omega) (by omega)).2
  · exact (future 510 (by omega) (by omega)).2
  · exact cK 0 (by omega)
  · exact cK 1 (by omega)
  · exact cK 2 (by omega)
  · exact cK 3 (by omega)
  · exact cK 4 (by omega)
  · exact cK 5 (by omega)


end ECDSAAdd.Entrant.Six505

namespace ECDSAAdd.Entrant.Five506
open Arithmetic MappedCompressed Secp256k1 History5 OB5 Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward Rolling1588.Integer.regularForward
  Rolling1588TickGap.forward tick506 cand MorningPlacement.merged Forward11Width.candidate

theorem stage_row (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (a : State)
    (hs : Stage base isA x p 506 a.basis) :
    ∃ G S : Bool, ∃ u v : Nat, (G,S,u,v) ∈ rows ∧ ∀ q ∈ sites, a.basis q = pre506 G S u v q := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have hs0 := hs
  obtain ⟨raw,hraw,hbits⟩ := hs
  obtain ⟨G,S,u,v,hsum,hv0,hvo,hg,reads⟩ := raw506 x hx0 hx raw hraw
  have bits : ∀ q ∈ sites, a.basis q = pre506 G S u v q := by
    intro q hq
    rw [hbits, ←reads q hq]
    exact run_preserves_outside _ _ _ q (prefix_avoids isA 506 (le_refl _) q hq)
  refine ⟨G,S,u,v,?_,bits⟩
  have next := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 506
    hp0 hx0 hpo hp gap hx cop (by omega) a [] hs0).2
  rw [explicit506, pack506 isA, List.append_nil] at next
  obtain ⟨raw7,hraw7,hbits7⟩ := next
  obtain ⟨g',s',uv',mem',width,oriented,reads7⟩ := MorningWidth.raw507 x hx0 hx raw7 hraw7
  have hl := Forward11Width.legal_of uv' g' width oriented
  have oldmem : uv' ∈ MorningFour.pairs := (List.mem_filter.mp mem').1
  have b7 : ∀ q ∈ MorningFour.sites, (run tick506 [] a).basis q = MorningFour.pre507 g' s' uv'.1 uv'.2 q := by
    intro q hq
    rw [hbits7, ←reads7 q hq]
    apply run_preserves_outside
    rcases MorningPlacement.layouts q hq with h|h|h|h
    all_goals
      exact fun hh => Finset.disjoint_left.mp
        (prefix_disjoint_layout base isA base_pool_nodup 507 _ (by omega) (by omega)) hh h
  have s7 : ∀ q ∈ MorningFour.sites, (run tick506 [] a).basis q =
      (run tick506 [] ⟨false, pre506 G S u v⟩).basis q := fun q hq =>
    site_run tick506 sites tick_support a ⟨false, pre506 G S u v⟩ bits [] q (morning_sub q hq)
  have good : goodRow (G,S,u,v) = true := by
    unfold goodRow
    rw [decide_eq_true_eq]
    have e1 : tbN_t8 (runN_t8 tick506 [] (false, enc (G,S,u,v))).2 =
        (run tick506 [] ⟨false, pre506 G S u v⟩).basis := by
      rw [tb_enc_t8 (pre506 G S u v) sites (pre_supp G S u v), run_sim_t8]
      rfl
    rw [e1, encN_congr _ (MorningFour.pre507 g' s' uv'.1 uv'.2) _
      (fun q hq => (s7 q hq).symm.trans (b7 q hq))]
    exact legal_codes_spec g' s' uv' oldmem hl
  exact rows_complete v (by omega) u (by omega) G S ⟨hsum, hvo, hg, good⟩

end ECDSAAdd.Entrant.Five506

namespace ECDSAAdd.Entrant.Six505
open Arithmetic MappedCompressed Secp256k1 History5 OB5 Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward Rolling1588.Integer.regularForward
  Rolling1588TickGap.forward Five506.tick506 Five506.cand

def legalFingerprint (x : Nat) : Bool :=
  (0x2000040002201000000800000080002040000104000800530090000000000004000000000008200140000800010100001000a0000900000040000a00004020000000008004000000000406000250000a012000000000002000100000001000020000100000001011000100008080800080000000008040000000000008000000000014c040000404020802000000000000020000002400000020200000084000010000005000008920000000010088000200000000000280053008000004000804440010200000000004000980480000000040020004800000001100a000400240808000020000002400000000082100002012000000005002000104000202004000000100900000001080100008000800000201000020040000080804000000400040000810000001402000200000000400020200000060a000000a01000184000000000000000000020400001000082000200000800000200042040020004000804400010000000000010000120001000200140220000810000001000a0004800408000000801010024000000008025000200020404000050080001200000000000200010101020000012800000000000101000010000000081000000000080004100400008000800000000080440400004000200020000000040000a000051a400000020001000000000010200005000020820000000000080804200 : Nat).testBit (x % 4093) &&
  (0x10000000c0000800000020000080100000020040001002010002000c000020000000804010000200200001002180880c000000000c02000440180000001000000100000000000000000842018008010000002000000880201100000000100200000010040100020086020010001002001000001200c0200000008000000000005000020000411004000000201000000000280080400008020000000200000020000001820008002100600001000100400500000030000220000008000000000001048030000400804000000100000a000000001000000080000000000020020b002000080200800210060200140010000040000001000000000040802000004000000800000020080400080020040080000002010044000000000004008002a010060000002400003000600001000000100000000000040000000108044000040002002010002000804000000000000000000060000000000a10080040000000004000004c0140800200020000100000004000088001042010000000c0000200800080020100002004000000000000008000000208002000040100c80400000100140000004004080020002008010000000812004000010201000000080100280000018040000000004000000000002824019000200800000000100000501040040000000004014000020002000050010000c00004000080201100200080000 : Nat).testBit (x % 4091) &&
  (0x2000000040000052480000205000000000001000001200000000a00008000080021000000000000128001000410000000000006020000000004930000024000200094000100000000420000000000002d258040102000100080004004000800400000080000802000002800020010000010800000081000000000000400000000002492280002000020000000010000000058000400204000292400001000000000000040000009000080001000000000000108000200000000b000010000800040000000000000200000249020000200000000a000080000000040000400004000492400000000001000080240800008000080000000040000000140801000810000a00008004000000000000020000020000324910000100000080400000800000000c100040080000149201000c000008000000260800008000000100000000000100940001000010005222000000000024010200102000100080324804000100400000400004002042000800020010000024d20000080000080000802440000400000000080000000000001000010040040052000400000000208000001020000000009248000008000000024000040000400108000000000800a490080040800041000080201000000000000000001000010000a0000800000000120000000010002000020080000002000092402000400000000040000401000000 : Nat).testBit (x % 4079)

theorem legal_codes_spec : ∀ r ∈ Five506.rows,
    legalFingerprint (encN_t8 (Five506.pre506 r.1 r.2.1 r.2.2.1 r.2.2.2) Five506.sites) = true := by decide +kernel

def goodRow (r : Bool × Bool × Nat × Nat) : Bool :=
  legalFingerprint (encN_t8 (tbN_t8 (runN_t8 tick505 [] (false, enc r)).2) Five506.sites)

def rowKey (r : Bool × Bool × Nat × Nat) : Nat := (if r.1 then 130 else 0) + (if r.2.1 then 65 else 0) + r.2.2.2

def rowFast (r : Bool × Bool × Nat × Nat) : Bool :=
  ((decide (1 ≤ rowKey r) && decide (rowKey r ≤ 1)) && decide (r ∈ rows0)) ||
  ((decide (1 ≤ rowKey r) && decide (rowKey r ≤ 3)) && decide (r ∈ rows1)) ||
  ((decide (3 ≤ rowKey r) && decide (rowKey r ≤ 9)) && decide (r ∈ rows2)) ||
  ((decide (9 ≤ rowKey r) && decide (rowKey r ≤ 17)) && decide (r ∈ rows3)) ||
  ((decide (17 ≤ rowKey r) && decide (rowKey r ≤ 33)) && decide (r ∈ rows4)) ||
  ((decide (35 ≤ rowKey r) && decide (rowKey r ≤ 66)) && decide (r ∈ rows5)) ||
  ((decide (66 ≤ rowKey r) && decide (rowKey r ≤ 68)) && decide (r ∈ rows6)) ||
  ((decide (68 ≤ rowKey r) && decide (rowKey r ≤ 72)) && decide (r ∈ rows7)) ||
  ((decide (72 ≤ rowKey r) && decide (rowKey r ≤ 80)) && decide (r ∈ rows8)) ||
  ((decide (80 ≤ rowKey r) && decide (rowKey r ≤ 92)) && decide (r ∈ rows9)) ||
  ((decide (92 ≤ rowKey r) && decide (rowKey r ≤ 131)) && decide (r ∈ rows10)) ||
  ((decide (131 ≤ rowKey r) && decide (rowKey r ≤ 131)) && decide (r ∈ rows11)) ||
  ((decide (131 ≤ rowKey r) && decide (rowKey r ≤ 135)) && decide (r ∈ rows12)) ||
  ((decide (135 ≤ rowKey r) && decide (rowKey r ≤ 141)) && decide (r ∈ rows13)) ||
  ((decide (141 ≤ rowKey r) && decide (rowKey r ≤ 149)) && decide (r ∈ rows14)) ||
  ((decide (151 ≤ rowKey r) && decide (rowKey r ≤ 183)) && decide (r ∈ rows15)) ||
  ((decide (185 ≤ rowKey r) && decide (rowKey r ≤ 196)) && decide (r ∈ rows16)) ||
  ((decide (196 ≤ rowKey r) && decide (rowKey r ≤ 198)) && decide (r ∈ rows17)) ||
  ((decide (198 ≤ rowKey r) && decide (rowKey r ≤ 204)) && decide (r ∈ rows18)) ||
  ((decide (204 ≤ rowKey r) && decide (rowKey r ≤ 212)) && decide (r ∈ rows19)) ||
  ((decide (212 ≤ rowKey r) && decide (rowKey r ≤ 226)) && decide (r ∈ rows20)) ||
  ((decide (226 ≤ rowKey r) && decide (rowKey r ≤ 258)) && decide (r ∈ rows21))

theorem rowFast_sound (r : Bool × Bool × Nat × Nat) (h : rowFast r = true) : r ∈ rows := by
  simp only [rowFast, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [rows, List.mem_append]
  tauto

def cv (v : Nat) : Bool :=
  (List.range 65).all fun u => [false, true].all fun g => [false, true].all fun s =>
    !(decide (u+v ≤ 64) && decide (v%2=1) && decide (u.gcd v = 1) && goodRow (g,s,u,v)) || rowFast (g,s,u,v)

theorem cv0 : cv 0 = true := by decide +kernel
theorem cv1 : cv 1 = true := by decide +kernel
theorem cv2 : cv 2 = true := by decide +kernel
theorem cv3 : cv 3 = true := by decide +kernel
theorem cv4 : cv 4 = true := by decide +kernel
theorem cv5 : cv 5 = true := by decide +kernel
theorem cv6 : cv 6 = true := by decide +kernel
theorem cv7 : cv 7 = true := by decide +kernel
theorem cv8 : cv 8 = true := by decide +kernel
theorem cv9 : cv 9 = true := by decide +kernel
theorem cv10 : cv 10 = true := by decide +kernel
theorem cv11 : cv 11 = true := by decide +kernel
theorem cv12 : cv 12 = true := by decide +kernel
theorem cv13 : cv 13 = true := by decide +kernel
theorem cv14 : cv 14 = true := by decide +kernel
theorem cv15 : cv 15 = true := by decide +kernel
theorem cv16 : cv 16 = true := by decide +kernel
theorem cv17 : cv 17 = true := by decide +kernel
theorem cv18 : cv 18 = true := by decide +kernel
theorem cv19 : cv 19 = true := by decide +kernel
theorem cv20 : cv 20 = true := by decide +kernel
theorem cv21 : cv 21 = true := by decide +kernel
theorem cv22 : cv 22 = true := by decide +kernel
theorem cv23 : cv 23 = true := by decide +kernel
theorem cv24 : cv 24 = true := by decide +kernel
theorem cv25 : cv 25 = true := by decide +kernel
theorem cv26 : cv 26 = true := by decide +kernel
theorem cv27 : cv 27 = true := by decide +kernel
theorem cv28 : cv 28 = true := by decide +kernel
theorem cv29 : cv 29 = true := by decide +kernel
theorem cv30 : cv 30 = true := by decide +kernel
theorem cv31 : cv 31 = true := by decide +kernel
theorem cv32 : cv 32 = true := by decide +kernel
theorem cv33 : cv 33 = true := by decide +kernel
theorem cv34 : cv 34 = true := by decide +kernel
theorem cv35 : cv 35 = true := by decide +kernel
theorem cv36 : cv 36 = true := by decide +kernel
theorem cv37 : cv 37 = true := by decide +kernel
theorem cv38 : cv 38 = true := by decide +kernel
theorem cv39 : cv 39 = true := by decide +kernel
theorem cv40 : cv 40 = true := by decide +kernel
theorem cv41 : cv 41 = true := by decide +kernel
theorem cv42 : cv 42 = true := by decide +kernel
theorem cv43 : cv 43 = true := by decide +kernel
theorem cv44 : cv 44 = true := by decide +kernel
theorem cv45 : cv 45 = true := by decide +kernel
theorem cv46 : cv 46 = true := by decide +kernel
theorem cv47 : cv 47 = true := by decide +kernel
theorem cv48 : cv 48 = true := by decide +kernel
theorem cv49 : cv 49 = true := by decide +kernel
theorem cv50 : cv 50 = true := by decide +kernel
theorem cv51 : cv 51 = true := by decide +kernel
theorem cv52 : cv 52 = true := by decide +kernel
theorem cv53 : cv 53 = true := by decide +kernel
theorem cv54 : cv 54 = true := by decide +kernel
theorem cv55 : cv 55 = true := by decide +kernel
theorem cv56 : cv 56 = true := by decide +kernel
theorem cv57 : cv 57 = true := by decide +kernel
theorem cv58 : cv 58 = true := by decide +kernel
theorem cv59 : cv 59 = true := by decide +kernel
theorem cv60 : cv 60 = true := by decide +kernel
theorem cv61 : cv 61 = true := by decide +kernel
theorem cv62 : cv 62 = true := by decide +kernel
theorem cv63 : cv 63 = true := by decide +kernel
theorem cv64 : cv 64 = true := by decide +kernel

theorem rows_complete : ∀ v, v < 65 → ∀ u, u < 65 → ∀ g s : Bool,
    (u+v ≤ 64 ∧ v%2=1 ∧ u.gcd v = 1 ∧ goodRow (g,s,u,v) = true) → (g,s,u,v) ∈ rows := by
  intro v hv u hu g s h
  have c1 : cv v = true := by
    interval_cases v <;> simp only [cv0, cv1, cv2, cv3, cv4, cv5, cv6, cv7, cv8, cv9, cv10, cv11, cv12, cv13, cv14, cv15, cv16, cv17, cv18, cv19, cv20, cv21, cv22, cv23, cv24, cv25, cv26, cv27, cv28, cv29, cv30, cv31, cv32, cv33, cv34, cv35, cv36, cv37, cv38, cv39, cv40, cv41, cv42, cv43, cv44, cv45, cv46, cv47, cv48, cv49, cv50, cv51, cv52, cv53, cv54, cv55, cv56, cv57, cv58, cv59, cv60, cv61, cv62, cv63, cv64]
  simp only [cv, List.all_eq_true, List.mem_range] at c1
  have c2 := c1 u hu g (by cases g <;> simp) s (by cases s <;> simp)
  obtain ⟨h1, h2, h3, h4⟩ := h
  apply rowFast_sound
  simpa [h1, h2, h3, h4] using c2

theorem five_in : ∀ q ∈ Five506.sites, q ∈ sites := by decide +kernel
theorem pack_wires (isA : Bool) : wires (packAfter base isA 505) ⊆
    ([516, 517, 518, 519, 520, 1544, 1545, 1546, 1547, 1548] : List Wire).toFinset := by
  cases isA <;> decide +kernel
theorem pack_list_off : ∀ q ∈ Five506.sites,
    q ∉ ([516, 517, 518, 519, 520, 1544, 1545, 1546, 1547, 1548] : List Wire) := by decide +kernel
theorem pack_off (isA : Bool) : ∀ q ∈ Five506.sites, q ∉ wires (packAfter base isA 505) :=
  fun q hq hw => pack_list_off q hq (List.mem_toFinset.mp (pack_wires isA hw))

theorem prefix_avoids (isA : Bool) : ∀ n, n ≤ 505 → ∀ q ∈ sites, q ∉ wires (encodePrefix base isA n) := by
  intro n hn q hq hw
  rw [prefix_support_eq] at hw
  induction n with
  | zero => simp [History5.encodePrefix, wires] at hw
  | succ n ih =>
    simp only [History5.encodePrefix, wires_append, Finset.mem_union] at hw
    rcases hw with hw | hw
    · exact ih (by omega) hw
    · cases due : History5.packDue n
      · simp [History5.packAfter, due, wires] at hw
      · simp only [History5.packAfter, due, if_true] at hw
        obtain ⟨j, rfl⟩ := History5.history_gate_mem base (n-5) _ (Or.inl rfl) _ hw
        have b := History5.packDue_true n due
        simp only [sites, List.mem_cons, List.not_mem_nil, or_false] at hq
        fin_cases j <;> simp [History5.historyMap, History5.historyId, base] at hq <;> omega

theorem at_stage6 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (a : State)
    (hs : Stage base isA x p 505 a.basis) (m n : List Bool) :
    run cand6 m a = run ref n a := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have hs0 := hs
  obtain ⟨raw,hraw,hbits⟩ := hs
  obtain ⟨G,S,u,v,hsum,hv0,hvo,hg,reads⟩ := raw505 x hx0 hx raw hraw
  have bits : ∀ q ∈ sites, a.basis q = pre505 G S u v q := by
    intro q hq
    rw [hbits, ←reads q hq]
    exact run_preserves_outside _ _ _ q (prefix_avoids isA 505 (le_refl _) q hq)
  have mem : (G,S,u,v) ∈ rows := by
    have next := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 505
      hp0 hx0 hpo hp gap hx cop (by omega) a [] hs0).2
    rw [explicit505] at next
    obtain ⟨G',S',u',v',memr,b6⟩ := Five506.stage_row isA x hx0 hx _ next
    have b5 : ∀ q ∈ Five506.sites, (run tick505 [] a).basis q = Five506.pre506 G' S' u' v' q := by
      intro q hq
      rw [←b6 q hq, run_append, List.take_nil, List.drop_nil]
      exact (run_preserves_outside _ _ _ q (pack_off isA q hq)).symm
    have s5 : ∀ q ∈ Five506.sites, (run tick505 [] a).basis q =
        (run tick505 [] ⟨false, pre505 G S u v⟩).basis q := fun q hq =>
      site_run tick505 sites tick_support a ⟨false, pre505 G S u v⟩ bits [] q (five_in q hq)
    have good : goodRow (G,S,u,v) = true := by
      unfold goodRow
      have e1 : tbN_t8 (runN_t8 tick505 [] (false, enc (G,S,u,v))).2 =
          (run tick505 [] ⟨false, pre505 G S u v⟩).basis := by
        rw [tb_enc_t8 (pre505 G S u v) sites (pre_supp G S u v), run_sim_t8]
        rfl
      rw [e1, Five506.encN_congr _ (Five506.pre506 G' S' u' v') _
        (fun q hq => (s5 q hq).symm.trans (b5 q hq))]
      exact legal_codes_spec (G',S',u',v') memr
    exact rows_complete v (by omega) u (by omega) G S ⟨hsum, hvo, hg, good⟩
  exact on_site (G,S,u,v) mem a bits m n

end ECDSAAdd.Entrant.Six505

namespace ECDSAAdd.Entrant.Six505
open Arithmetic MappedCompressed Secp256k1 History5 OB5 Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
attribute [local irreducible] wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward
  Rolling1588TickGap.forward Five506.tick506 Five506.cand

theorem shared_nodup : (skywalkSharedWires base).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact List.nodup_range'

theorem tick_ranges505 : TickRanges.tick base 505 = tick505 := by
  rw [← explicit505]
  unfold TickRanges.tick TickGap.tick
  simp only [show ¬(225 ≤ (505:Nat) ∧ (505:Nat) ≤ 254) from by decide,
    show ¬(255 ≤ (505:Nat) ∧ (505:Nat) ≤ 286) from by decide, if_false]

theorem packFirst505 (isA : Bool) : packFirst base isA 505 = packAfter base isA 505 := by
  simp only [packFirst, show ¬(505:Nat) = 5 from by decide, if_false]

def merged6 : Program := renameProgram (sig 510) cand6
def tickP : Program := renameProgram (sig 505) tick505
def packP (isA : Bool) : Program := renameProgram (sig 505) (packAfter base isA 505)

def stackForward6 (isA : Bool) : Program :=
  Rolling1588TickGap.forward isA 1 504 ++
    (merged6 ++ (packP isA ++ ForwardSixPlacement.after isA))

theorem rename_append (f : Wire → Wire) (a b : Program) :
    renameProgram f (a ++ b) = renameProgram f a ++ renameProgram f b := by
  simp [renameProgram, List.map_append]

theorem shape6 (isA : Bool) : Five506.stackForward5 isA =
    Rolling1588TickGap.forward isA 1 504 ++
      (tickP ++ (packP isA ++ (Five506.merged5 ++ ForwardSixPlacement.after isA))) := by
  rw [Five506.stackForward5, show (505:Nat) = 504+1 from rfl, Five506.forward_snoc]
  simp only [show (1:Nat)+504 = 505 from rfl, tick_ranges505, packFirst505, rename_append,
    tickP, packP, List.append_assoc]

theorem forward_split (isA : Bool) : Rolling1588TickGap.forward isA 1 505 =
    Rolling1588TickGap.forward isA 1 504 ++ (tickP ++ packP isA) := by
  rw [show (505:Nat) = 504+1 from rfl, Five506.forward_snoc]
  simp only [show (1:Nat)+504 = 505 from rfl, tick_ranges505, packFirst505, rename_append, tickP, packP]

theorem packP_eq (isA : Bool) : packP isA = renameProgram (sig 510) (packAfter base isA 505) := by
  cases isA <;> decide +kernel

theorem pack_count (isA : Bool) : measurementCount (packAfter base isA 505) = 4 := by
  cases isA <;> decide +kernel

theorem pack_cand_disjoint (isA : Bool) : Disjoint (wires Five506.cand) (wires (packAfter base isA 505)) := by
  rw [Finset.disjoint_left]
  intro q hq hw
  have h1 := Five506.cand_sub (Five506.csupport hq)
  exact pack_off isA q (List.mem_toFinset.mp h1) hw

theorem align5 (isA : Bool) (x : Nat) (v : State) (i : Nat) (hi : i ≤ 506)
    (h : Stage base isA x p i v.basis) : pullState (sig 505) v = pullState (sig 510) v := by
  have z6 := stage_zero_gen isA x i 506 hi (by omega) v.basis h
  have z7 := stage_zero_gen isA x i 507 (by omega) (by omega) v.basis h
  have z8 := stage_zero_gen isA x i 508 (by omega) (by omega) v.basis h
  have z9 := stage_zero_gen isA x i 509 (by omega) (by omega) v.basis h
  have z10 := stage_zero_gen isA x i 510 (by omega) (by omega) v.basis h
  exact (OB5.pull_step 506 (by omega) v z6.1 z6.2).trans
    ((OB5.pull_step 507 (by omega) v z7.1 z7.2).trans
      ((OB5.pull_step 508 (by omega) v z8.1 z8.2).trans
        ((OB5.pull_step 509 (by omega) v z9.1 z9.2).trans (OB5.pull_step 510 (by omega) v z10.1 z10.2))))

theorem run_split (P Q : Program) (a b : List Bool) (h : a.length = measurementCount P) (s : State) :
    run (P ++ Q) (a ++ b) s = run Q b (run P a s) := by
  rw [run_append, ← h, List.take_left', List.drop_left'] <;> rfl

theorem pack_indep (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (a : State)
    (stage : Stage base isA x p 505 a.basis) (q1 r2 q2 : List Bool) (hq : q1.length = 7) :
    run (packAfter base isA 505) r2 (run tick505 q1 a) =
      run (packAfter base isA 505) q2 (run tick505 q1 a) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have e1 := step_eq base isA base_pool_nodup x p 505 hp0 hx0 hpo hp gap hx cop (by omega) a (q1 ++ r2) [] stage
  have e2 := step_eq base isA base_pool_nodup x p 505 hp0 hx0 hpo hp gap hx cop (by omega) a (q1 ++ q2) [] stage
  rw [explicit505, run_split _ _ _ _ (hq.trans tick_counts.2.symm)] at e1 e2
  exact e1.trans e2.symm

theorem core (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (a : State)
    (stage : Stage base isA x p 505 a.basis) (q1 q2 r r1 r2 : List Bool) (hq : q1.length = 7) :
    run (packP isA) r2 (run merged6 r1 (pullState (sig 505) a)) =
      run Five506.merged5 r (run (packP isA) q2 (run tickP q1 (pullState (sig 505) a))) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  let P := packAfter base isA 505
  let t := run tick505 q1 a
  have hb : Stage base isA x p 506 (run P q2 t).basis := by
    have next := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 505
      hp0 hx0 hpo hp gap hx cop (by omega) a (q1 ++ q2) stage).2
    rw [explicit505, run_split _ _ _ _ (hq.trans tick_counts.2.symm)] at next
    exact next
  have rhs : run Five506.merged5 r (run (packP isA) q2 (run tickP q1 (pullState (sig 505) a))) =
      pullState (sig 510) (run Five506.cand r (run P q2 t)) := by
    rw [tickP, OB5.run_rename 505 (by omega), packP, OB5.run_rename 505 (by omega),
      align5 isA x _ 506 (le_refl _) hb, Five506.merged5, OB5.run_rename 510 (by omega)]
  have lhs : run (packP isA) r2 (run merged6 r1 (pullState (sig 505) a)) =
      pullState (sig 510) (run P r2 (run cand6 r1 a)) := by
    rw [align5 isA x a 505 (by omega) stage, merged6, OB5.run_rename 510 (by omega), packP_eq,
      OB5.run_rename 510 (by omega)]
  rw [lhs, rhs, at_stage6 isA x hx0 hx a stage r1 (q1 ++ r), ref,
    run_split _ _ _ _ (hq.trans tick_counts.2.symm),
    ← run_disjoint_commute Five506.cand P (pack_cand_disjoint isA) r r2 t]
  exact congrArg (fun y => pullState (sig 510) (run Five506.cand r y))
    (pack_indep isA x hx0 hx a stage q1 r2 q2 hq)

theorem regular_indep (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) :
    ∀ n i, i+n ≤ 512 → ∀ (s : State) (m m' : List Bool), Stage base isA x p i s.basis →
      run (regularForward base isA i n) m s = run (regularForward base isA i n) m' s := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  intro n
  induction n with
  | zero =>
    intro i _ s m m' _
    simp [regularForward, run]
  | succ n ih =>
    intro i hi s m m' hs
    simp only [regularForward]
    rw [run_append (W.repairedTick base i ++ packAfter base isA i),
      run_append (W.repairedTick base i ++ packAfter base isA i)]
    generalize measurementCount (W.repairedTick base i ++ packAfter base isA i) = c
    have e1 := step_eq base isA base_pool_nodup x p i hp0 hx0 hpo hp gap hx cop (by omega) s (m.take c) [] hs
    have e2 := step_eq base isA base_pool_nodup x p i hp0 hx0 hpo hp gap hx cop (by omega) s (m'.take c) [] hs
    rw [e1, ← e2]
    exact ih (i+1) (by omega) _ _ _ ((step_spec base isA base_pool_nodup StackOB5.historyAbove x p i
      hp0 hx0 hpo hp gap hx cop (by omega) s (m'.take c) hs).2)

theorem merged6_count : measurementCount merged6 = 27 := by
  rw [merged6, (renameProgram_counts _ _).2]; exact cand_counts.2
theorem tickP_count : measurementCount tickP = 7 := by
  rw [tickP, (renameProgram_counts _ _).2]; exact tick_counts.2
theorem packP_count (isA : Bool) : measurementCount (packP isA) = 4 := by
  rw [packP, (renameProgram_counts _ _).2]; exact pack_count isA
theorem merged5_count : measurementCount Five506.merged5 = 20 := by
  rw [Five506.merged5, (renameProgram_counts _ _).2]; exact Five506.cand_counts.2.1

theorem stackForward6_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward6 isA) m s = run (Rolling1588TickGap.stackForward0 isA) m s := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have indep : ∀ m1 m2, run (Rolling1588TickGap.stackForward0 isA) m1 s =
      run (Rolling1588TickGap.stackForward0 isA) m2 s := by
    intro m1 m2
    rw [Rolling1588TickGap.stackForward0_run_eq isA x hx0 hx s m1 first,
      Rolling1588TickGap.stackForward0_run_eq isA x hx0 hx s m2 first,
      Rolling1588.stackForward_boundary isA shared_nodup StackOB5.historyAbove x hx0 hx s m1 first,
      Rolling1588.stackForward_boundary isA shared_nodup StackOB5.historyAbove x hx0 hx s m2 first]
  generalize hK : measurementCount (Rolling1588TickGap.forward isA 1 504) = K
  have hm0 : (List.replicate (K+31) false ++ m.drop (K+31)).drop K =
      List.replicate 31 false ++ m.drop (K+31) := by
    rw [← List.replicate_append_replicate, List.append_assoc, List.drop_left' (by simp)]
  rw [indep m (List.replicate (K+31) false ++ m.drop (K+31)),
    ← Five506.stackForward5_run_eq isA x hx0 hx s _ first, shape6, stackForward6]
  simp only [run_append (Rolling1588TickGap.forward isA 1 504), run_append merged6,
    run_append (packP isA), run_append tickP, run_append Five506.merged5,
    merged6_count, tickP_count, packP_count, merged5_count, hK, hm0]
  have init := stage_one base isA x p s first
  have st := ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p
    1 504 hp0 hx0 hpo hp gap hx cop (by omega)) s [] init).2
  have start : pullState (sig (1-1)) s = s := by
    apply State.extensionality
    · rfl
    · funext q
      change s.basis (sig 0 q) = s.basis q
      rw [sig_zero]
  have hc : ∀ ml, run (Rolling1588TickGap.forward isA 1 504) ml s =
      pullState (sig 505) (run (regularForward base isA 1 504) [] s) := by
    intro ml
    have pre := Rolling1588TickGap.forward_gen isA x hx0 hx 504 1 (le_refl _) (by omega) s ml init
    rw [start] at pre
    rw [pre, regular_indep isA x hx0 hx 504 1 (by omega) s ml [] init]
    have z5 := stage_zero_gen isA x 505 505 (le_refl _) (by omega) _ st
    exact OB5.pull_step 505 (by omega) _ z5.1 z5.2
  rw [hc, hc]
  have hq : ((List.replicate 31 false ++ m.drop (K+31)).take 7).length = 7 := by simp
  rw [← core isA x hx0 hx _ st _ _ _ ((m.drop K).take 27) (((m.drop K).drop 27).take 4) hq]
  have tail1 : (((List.replicate 31 false ++ m.drop (K+31)).drop 7).drop 4).drop 20 = m.drop (K+31) := by
    simp only [List.drop_drop]
    exact List.drop_left' (by simp)
  have tail2 : ((m.drop K).drop 27).drop 4 = m.drop (K+31) := by
    simp only [List.drop_drop]
  rw [tail1, tail2]

theorem counts6 :
    toffoliCount merged6 + 1 = toffoliCount tickP + toffoliCount Five506.merged5 ∧
      measurementCount merged6 = measurementCount tickP + measurementCount Five506.merged5 := by
  have a := cand_counts
  have b := tick_counts
  have c := Five506.cand_counts
  simp only [merged6, tickP, Five506.merged5, (renameProgram_counts _ _).1, (renameProgram_counts _ _).2]
  omega

theorem slots6 : Challenge.gateSlots merged6 ≤
    Challenge.gateSlots tickP + Challenge.gateSlots Five506.merged5 := by decide +kernel

theorem site_split : ∀ w ∈ used, w ∈ Five506.candSites ∨ sig 510 w ∈ wires tickP := by decide +kernel

theorem support6 (isA : Bool) :
    wires (stackForward6 isA) ⊆ wires (Rolling1588TickGap.stackForward0 isA) := by
  rw [Five506.shape, stackForward6]
  intro q hq
  have head : ∀ r, r ∈ wires (Rolling1588TickGap.forward isA 1 505) →
      r ∈ wires (Rolling1588TickGap.forward isA 1 505 ++
        (Five506.prior5 ++ ForwardSixPlacement.after isA)) := by
    intro r h
    rw [wires_append]
    exact Finset.mem_union_left _ h
  simp only [wires_append, Finset.mem_union] at hq
  rcases hq with h | h | h | h
  · apply head
    rw [forward_split, wires_append]
    exact Finset.mem_union_left _ h
  · rw [merged6, renameProgram_support] at h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
    rcases site_split w (List.mem_toFinset.mp (cused hw)) with g | g
    · exact Five506.site_used isA w g
    · apply head
      rw [forward_split]
      simp only [wires_append, Finset.mem_union]
      exact Or.inr (Or.inl g)
  · apply head
    rw [forward_split]
    simp only [wires_append, Finset.mem_union]
    exact Or.inr (Or.inr h)
  · rw [wires_append, wires_append]
    exact Finset.mem_union_right _ (Finset.mem_union_right _ h)

end ECDSAAdd.Entrant.Six505

end -- Six505

-- ===== Five-tick forward window: the TickGap forward stack now uses Five506 =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.Rolling1588TickGap
open Arithmetic MappedCompressed Secp256k1 OB5
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  forward stackForward0 Rolling1588.forward Rolling1588.stackForward

/-- The forward stack: ticks 1..505, then the jointly re-synthesized five-tick window
(tick 506 and ticks 507..510), then the unchanged tail. -/
def stackForward (isA : Bool) : Program := Six505.stackForward6 isA

theorem stackForward_metrics (isA : Bool) :
    toffoliCount (stackForward isA)+69=toffoliCount (Rolling1588.stackForward isA) ∧
      measurementCount (stackForward isA)=measurementCount (Rolling1588.stackForward isA) ∧
      Challenge.gateSlots (stackForward isA) ≤ Challenge.gateSlots (Rolling1588.stackForward isA)+1005 := by
  have old := stackForward0_metrics isA
  have c := Five506.counts5
  have sl := Five506.slots5
  have c6 := Six505.counts6
  have s6 := Six505.slots6
  rw [Five506.shape, Six505.forward_split] at old
  rw [stackForward, Six505.stackForward6]
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append] at old ⊢
  exact ⟨by omega, by omega, by omega⟩

theorem stackForward_support (isA : Bool) :
    wires (stackForward isA)⊆wires (Rolling1588.stackForward isA) :=
  (Six505.support6 isA).trans (stackForward0_support isA)

theorem stackForward_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward isA) m s=run (Rolling1588.stackForward isA) m s := by
  rw [stackForward, Six505.stackForward6_run_eq isA x hx0 hx s m first]
  exact stackForward0_run_eq isA x hx0 hx s m first

theorem stackForward_boundary (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward isA) m s=pullState (sig 511)
      (run (Rolling1588.allEncode base isA 102) []
        (run (W.compactSkywalkForward base 1 511) [] s)) := by
  rw [stackForward_run_eq isA x hx0 hx s m first]
  exact Rolling1588.stackForward_boundary isA hn hlo x hx0 hx s m first

theorem stack_roundtrip (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (Rolling1588.stackReverse isA) mD (run (stackForward isA) mE s)=s := by
  rw [stackForward_run_eq isA x hx0 hx s mE first]
  exact Rolling1588.stack_roundtrip isA hn hlo x hx0 hx s mE mD first

end ECDSAAdd.Entrant.Rolling1588TickGap
end -- five-tick bridge

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588TickGapPhases =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588TickGapWalk
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Native
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Kernel
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588KernelResources

/-! The new forward phase has the exact old A/B State boundary. All native,
field, inverse, host, and caller interfaces are retained. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588TickGap
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Challenge Baselines
  FrontierEntry1591Callers OB5
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  forward stackForward Rolling1588.forward Rolling1588.stackForward Rolling1588.stackReverse
  FrontierEntry1591Native.forward FrontierEntry1591Native.inverse
  Rolling1588.firstPhase Rolling1588.lastPhase

def tailPhase (isA : Bool) : Program := stackForward isA++skywalkArithmeticClear base

def firstPhase (isA : Bool) : Program := FrontierEntry1591Native.forward base++tailPhase isA

def oldKernel (a b : Bool) (F : Program) : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a)++
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b))

def kernel (a b : Bool) (F : Program) : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (firstPhase a)++
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b))

def entryKernel : Program := kernel true false Rolling1588.entryFieldHosted
def exitKernel : Program := kernel false true Rolling1588.exitFieldHosted

attribute [local irreducible] tailPhase firstPhase oldKernel kernel entryKernel exitKernel
  Rolling1588.entryKernel Rolling1588.exitKernel

private theorem first_run_eq_of_stack (N F F0 C : Program) (s : State) (m : List Bool)
    (records : measurementCount F=measurementCount F0)
    (same : ∀mn mf,run F mf (run N mn s)=run F0 mf (run N mn s)) :
    run (N++(F++C)) m s=run (N++(F0++C)) m s := by
  simp only [run_append,records]
  rw [same]

theorem first_run_eq (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (firstPhase isA) m s=run (Rolling1588.firstPhase isA) m s := by
  have same (mn mf : List Bool) :
      run (stackForward isA) mf (run (FrontierEntry1591Native.forward base) mn s)=
        run (Rolling1588.stackForward isA) mf
          (run (FrontierEntry1591Native.forward base) mn s) :=
    stackForward_run_eq isA x hx0 hx _ mf
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [firstPhase,tailPhase,Rolling1588.firstPhase,List.append_assoc] using
    first_run_eq_of_stack (FrontierEntry1591Native.forward base) (stackForward isA)
      (Rolling1588.stackForward isA) (skywalkArithmeticClear base) s m
      (stackForward_metrics isA).2.1 same

private theorem state_fact_of_eq (P : State→Prop) (a b : State)
    (same : a=b) (fact : P b) : P a := by
  cases same
  exact fact

theorem first_clean (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    ∀q∈FrontierEntry1591Native.workSites,(run (firstPhase isA) m s).basis q=false := by
  exact state_fact_of_eq
    (fun t=>∀q∈FrontierEntry1591Native.workSites,t.basis q=false)
    (run (firstPhase isA) m s) (run (Rolling1588Lifetime.firstPhase isA) m s)
    (first_run_eq isA hn x y hx0 hx s m input)
    (Rolling1588Lifetime.first_clean isA hn hlo x y hx0 hx s m input)

theorem first_phase (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    (run (firstPhase isA) m s).phase=s.phase := by
  exact state_fact_of_eq (fun t=>t.phase=s.phase)
    (run (firstPhase isA) m s) (run (Rolling1588Lifetime.firstPhase isA) m s)
    (first_run_eq isA hn x y hx0 hx s m input)
    (Rolling1588Lifetime.first_phase isA hn hlo x y hx0 hx s m input)

theorem first_boundary (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (firstPhase isA) m s=pullState (sig 511)
      (run (Rolling1588.allEncode base isA 102) []
        (run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) []
          (run (FrontierEntry1591Native.forward base)
            (m.take (measurementCount (FrontierEntry1591Native.forward base))) s)))) := by
  rw [first_run_eq isA hn x y hx0 hx s m input]
  exact Rolling1588Lifetime.first_boundary isA hn hlo x y hx0 hx s m input

theorem phases_roundtrip (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (mE mD : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (Rolling1588.lastPhase isA) mD (run (firstPhase isA) mE s)=s := by
  rw [first_run_eq isA hn x y hx0 hx s mE input]
  exact Rolling1588Lifetime.phases_roundtrip isA hn hlo x y hx0 hx s mE mD input

theorem first_metrics (isA : Bool) :
    toffoliCount (firstPhase isA)+69=toffoliCount (Rolling1588.firstPhase isA) ∧
      measurementCount (firstPhase isA)=measurementCount (Rolling1588.firstPhase isA) ∧
      gateSlots (firstPhase isA) ≤ gateSlots (Rolling1588.firstPhase isA)+1005 := by
  have stack := stackForward_metrics isA
  simp only [firstPhase,tailPhase,Rolling1588.firstPhase,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

theorem first_support (isA : Bool) :
    wires (firstPhase isA)⊆wires (Rolling1588.firstPhase isA) := by
  simp only [firstPhase,tailPhase,Rolling1588.firstPhase,wires_append,Finset.union_assoc]
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (stackForward_support isA) (Finset.Subset.refl _))

private theorem mapped_code_physical (isA : Bool) (f : Fin 10→Wire)
    (hf : Function.Injective f) :
    GatePhysical (renameProgram (MeasuredCodec5.label f) (Rolling1588.codeEncode isA)) := by
  have support : wires (Rolling1588.codeEncode isA)⊆Finset.range 10 := by
    simpa only [(Rolling1588.code_support isA).1] using
      (Finset.Subset.refl (Finset.range 10))
  exact gatePhysical_rename_support _ _
    (fun a ha b hb eq=>FirstNonzeroCodec.label_inj' f hf a (support ha) b (support hb) eq)
    (Rolling1588.code_physical isA).1

private theorem pack_physical (isA : Bool) (i : Nat) (hi : i<512) :
    GatePhysical (Rolling1588.packAtTick isA i) := by
  by_cases first : i=5
  · simp only [Rolling1588.packAtTick,if_pos first]
    exact (ParityCodec5New.first_mapped_physical _
      (History5.historyMap_injective base base_pool_nodup 0 (by decide))).1
  · simp only [Rolling1588.packAtTick,if_neg first]
    split
    · have due := History5.packDue_true i ‹History5.packDue i=true›
      exact mapped_code_physical isA _
        (History5.historyMap_injective base base_pool_nodup (i-5) (by omega))
    · simp [GatePhysical]

theorem forward_physical (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    GatePhysical (forward isA i n) := by
  induction n generalizing i with
  | zero => simp [forward,GatePhysical]
  | succ n ih =>
    have pack : GatePhysical (Rolling1588.Integer.packFirst base isA i) := by
      rw [Rolling1588.Integer.packFirst_base]
      exact pack_physical isA i (by omega)
    rw [forward,gatePhysical_append]
    exact ⟨gatePhysical_rename _ (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr
        ⟨TickRanges.tick_physical base i (by omega) base_pool_nodup,pack⟩),
      ih (i+1) (by omega)⟩

theorem stackForward_physical (isA : Bool) : GatePhysical (stackForward isA) := by
  have old := Rolling1588.stackForward_physical isA
  rw [MorningPlacement.previous_shape] at old
  simp only [gatePhysical_append] at old
  have h5 := forward_physical isA 1 505 (by omega)
  rw [Six505.forward_split] at h5
  simp only [gatePhysical_append] at h5
  rw [stackForward, Six505.stackForward6, Six505.merged6]
  simp only [gatePhysical_append]
  exact ⟨h5.1, gatePhysical_rename _ (sig_injective 510 (by omega)) _ Six505.physical,h5.2.2,old.2.2⟩

theorem first_physical (isA : Bool) : GatePhysical (firstPhase isA) := by
  have old := Rolling1588.firstPhase_physical isA
  simp only [Rolling1588.firstPhase,gatePhysical_append] at old
  simpa only [firstPhase,tailPhase,gatePhysical_append] using
    And.intro old.1.1 (And.intro (stackForward_physical isA) old.2)

private theorem mapped_run_eq (f : Equiv.Perm Wire) (P Q : Program)
    (s : State) (m : List Bool) (clean : pullState f s=s)
    (same : run P m s=run Q m s) :
    run (renameProgram f P) m s=run (renameProgram f Q) m s := by
  apply pullState_perm_injective f
  rw [run_rename _ f.injective,run_rename _ f.injective,clean]
  exact same

theorem first_hosted_run_eq (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (renameProgram Rolling1588Lifetime.phaseHost (firstPhase isA)) m s=
      run (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase isA)) m s := by
  exact mapped_run_eq Rolling1588Lifetime.phaseHost _ _ s m
    (Rolling1588Lifetime.pull_phase_clean s
      (Rolling1588Lifetime.caller_phase_clean x y s input))
    (first_run_eq isA hn x y hx0 hx s m input)

private theorem append_run_eq_tickgap_phases (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem kernel_run_eq (a b : Bool) (F : Program)
    (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (kernel a b F) m s=run (oldKernel a b F) m s := by
  have records :
      measurementCount (renameProgram Rolling1588Lifetime.phaseHost (firstPhase a))=
        measurementCount (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(first_metrics a).2.1]
  simpa only [kernel,oldKernel] using append_run_eq_tickgap_phases
    (renameProgram Rolling1588Lifetime.phaseHost (firstPhase a))
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a))
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b)) s m records
    (fun r=>first_hosted_run_eq a hn x y hx0 hx s r input)

theorem kernel_metrics (a b : Bool) (F : Program) :
    toffoliCount (kernel a b F)+69=toffoliCount (oldKernel a b F) ∧
      measurementCount (kernel a b F)=measurementCount (oldKernel a b F) ∧
      gateSlots (kernel a b F) ≤ gateSlots (oldKernel a b F)+1005 := by
  have first := first_metrics a
  simp only [kernel,oldKernel,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

private theorem mapped_append_support (f : Wire→Wire) (P Q R : Program)
    (first : wires P⊆wires Q) :
    wires (renameProgram f P++R)⊆wires (renameProgram f Q++R) := by
  rw [wires_append,wires_append,renameProgram_support,renameProgram_support]
  exact Finset.union_subset_union
    (Finset.image_mono f first) (Finset.Subset.refl _)

theorem kernel_support (a b : Bool) (F : Program) :
    wires (kernel a b F)⊆wires (oldKernel a b F) := by
  simpa only [kernel,oldKernel] using
    mapped_append_support Rolling1588Lifetime.phaseHost
      (firstPhase a) (Rolling1588.firstPhase a)
      (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b)) (first_support a)

theorem kernel_physical (a b : Bool) (F : Program) (field : GatePhysical F) :
    GatePhysical (kernel a b F) := by
  simpa only [kernel,gatePhysical_append] using
    And.intro (Rolling1588Lifetime.phase_physical _ (first_physical a))
      (And.intro field
        (Rolling1588Lifetime.phase_physical _ (Rolling1588.lastPhase_physical b)))

theorem kernel_entry_correct (F : Program) (raw : EntryCorrect (oldKernel true false F)) :
    EntryCorrect (kernel true false F) := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actual := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  rw [kernel_run_eq true false F hn x _ hx0 hx t m actual]
  exact raw hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half

theorem kernel_exit_correct (F : Program) (raw : ExitCorrect (oldKernel false true F)) :
    ExitCorrect (kernel false true F) := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  rw [kernel_run_eq false true F hn x Y.val hx0 hx s m input]
  exact raw hn hlo ho hf x Y hx0 hx s m input hg hs

theorem entry_correct : EntryCorrect entryKernel := by
  have old : EntryCorrect (oldKernel true false Rolling1588.entryFieldHosted) := by
    simpa only [oldKernel,Rolling1588.entryKernel] using Rolling1588.entry_correct
  simpa only [entryKernel] using kernel_entry_correct Rolling1588.entryFieldHosted old

theorem exit_correct : ExitCorrect exitKernel := by
  have old : ExitCorrect (oldKernel false true Rolling1588.exitFieldHosted) := by
    simpa only [oldKernel,Rolling1588.exitKernel] using Rolling1588.exit_correct
  simpa only [exitKernel] using kernel_exit_correct Rolling1588.exitFieldHosted old

private theorem metrics_of_shapes (P Q A B : Program)
    (left : P=A) (right : Q=B)
    (metrics : toffoliCount A+69=toffoliCount B ∧
      measurementCount A=measurementCount B ∧ gateSlots A ≤ gateSlots B+1005) :
    toffoliCount P+69=toffoliCount Q ∧
      measurementCount P=measurementCount Q ∧ gateSlots P ≤ gateSlots Q+1005 := by
  cases left
  cases right
  exact metrics

theorem entryKernel_metrics :
    toffoliCount entryKernel+69=toffoliCount Rolling1588.entryKernel ∧
      measurementCount entryKernel=measurementCount Rolling1588.entryKernel ∧
      gateSlots entryKernel ≤ gateSlots Rolling1588.entryKernel+1005 := by
  have left : entryKernel=kernel true false Rolling1588.entryFieldHosted := by
    unfold entryKernel
    rfl
  have right : Rolling1588.entryKernel=oldKernel true false Rolling1588.entryFieldHosted := by
    unfold Rolling1588.entryKernel oldKernel
    rfl
  exact metrics_of_shapes entryKernel Rolling1588.entryKernel
    (kernel true false Rolling1588.entryFieldHosted)
    (oldKernel true false Rolling1588.entryFieldHosted) left right
    (kernel_metrics true false Rolling1588.entryFieldHosted)

theorem exitKernel_metrics :
    toffoliCount exitKernel+69=toffoliCount Rolling1588.exitKernel ∧
      measurementCount exitKernel=measurementCount Rolling1588.exitKernel ∧
      gateSlots exitKernel ≤ gateSlots Rolling1588.exitKernel+1005 := by
  have left : exitKernel=kernel false true Rolling1588.exitFieldHosted := by
    unfold exitKernel
    rfl
  have right : Rolling1588.exitKernel=oldKernel false true Rolling1588.exitFieldHosted := by
    unfold Rolling1588.exitKernel oldKernel
    rfl
  exact metrics_of_shapes exitKernel Rolling1588.exitKernel
    (kernel false true Rolling1588.exitFieldHosted)
    (oldKernel false true Rolling1588.exitFieldHosted) left right
    (kernel_metrics false true Rolling1588.exitFieldHosted)

theorem entryKernel_support_subset : wires entryKernel⊆wires Rolling1588.entryKernel := by
  simpa only [entryKernel,oldKernel,Rolling1588.entryKernel] using
    kernel_support true false Rolling1588.entryFieldHosted

theorem exitKernel_support_subset : wires exitKernel⊆wires Rolling1588.exitKernel := by
  simpa only [exitKernel,oldKernel,Rolling1588.exitKernel] using
    kernel_support false true Rolling1588.exitFieldHosted

theorem entryKernel_support : wires entryKernel⊆OB5Support.logicalSites :=
  entryKernel_support_subset.trans Rolling1588.entryKernel_support

theorem exitKernel_support : wires exitKernel⊆OB5Support.logicalSites :=
  exitKernel_support_subset.trans Rolling1588.exitKernel_support

theorem entryKernel_physical : GatePhysical entryKernel := by
  simpa only [entryKernel] using
    kernel_physical true false Rolling1588.entryFieldHosted Rolling1588.entryFieldHosted_physical

theorem exitKernel_physical : GatePhysical exitKernel := by
  simpa only [exitKernel] using
    kernel_physical false true Rolling1588.exitFieldHosted Rolling1588.exitFieldHosted_physical

theorem entryKernel_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_free i hi (entryKernel_support_subset used)

theorem exitKernel_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_free i hi (exitKernel_support_subset used)

theorem entryKernel_768_free : base 768∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_768_free (entryKernel_support_subset used)
theorem exitKernel_768_free : base 768∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_768_free (exitKernel_support_subset used)
theorem entryKernel_718_free : base 718∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_718_free (entryKernel_support_subset used)
theorem exitKernel_718_free : base 718∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_718_free (exitKernel_support_subset used)
theorem entryKernel_719_free : base 719∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_719_free (entryKernel_support_subset used)
theorem exitKernel_719_free : base 719∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_719_free (exitKernel_support_subset used)
theorem entryKernel_760_free : base 760∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_760_free (entryKernel_support_subset used)
theorem exitKernel_760_free : base 760∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_760_free (exitKernel_support_subset used)

end ECDSAAdd.Entrant.Rolling1588TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1TickGap =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Final
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588TickGapPhases

/-! E1 entries and the reflected square are unchanged. Only the two
forward tails use the checked TickGap program. Both inverse phases stay. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1TickGap
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def restE (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase true)++
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))

def restX (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false)++
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))

def entryStage (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky++E1QubitPlacement.entryM L kx++restE L

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  ReflectionE1.squareEntry L k++restX L++exitY L cy

theorem entry_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry Rolling1588TickGap.entryKernel L=
      E1QubitPlacement.tickF L++restE L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,Rolling1588TickGap.entryKernel,
    Rolling1588TickGap.kernel,Rolling1588TickGap.firstPhase,restE,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem exit_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L=
      E1QubitPlacement.tickF L++restX L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,Rolling1588TickGap.exitKernel,
    Rolling1588TickGap.kernel,Rolling1588TickGap.firstPhase,restX,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

section CorrectStages
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem entryStage_step (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStage L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  have add:=fastStep_addX L hw hn X Y G origin kx
  have divide:=division_step Rolling1588TickGap.entryKernel Rolling1588TickGap.entryKernel_support
    Rolling1588TickGap.entry_correct L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior:=add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky++E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx++fusedY L ky++E1QubitPlacement.tickF L)
    (R:=restE L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryStage,division,entry_split,List.append_assoc] using prior

theorem secondStage_step (X Y k cy : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStage L k cy)
      (PointDialogValues L Z (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=fusedMultiply_step L hw hn
    (FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L)
    (exit_correct Rolling1588TickGap.exitKernel Rolling1588TickGap.exitKernel_support
      Rolling1588TickGap.exit_correct L hw hn)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStage,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=ReflectionE1.squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=restX L++exitY L cy)
  · intro s v m1 m2
    exact ReflectionE1.squareEntry_eq L hw hn k X Y G origin s m1 m2 v
  · simpa only [secondStage,fusedMultiply,exit_split,List.append_assoc,Z] using prior

end CorrectStages

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStage L (-cx) (-cy)++secondStage L (ReflectionE1.correction cx) cy++fastConstNeg L cx

def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clrF L++renameProgram (swapF L) (generic L cx cy)++clrF L

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  zrep L++mid L cx cy++zrep L

theorem gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    gen L cx cy=GenericQ5Geometry.wrapG L (generic L cx cy) := rfl

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStage_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStage_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  have finish:=fastStep_negX L hw hn d (a*d-cy) true origin cx
  simp only [if_true] at finish
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at finish
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at second finish
  exact (first.seq second).seq finish

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStage_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStage_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have finish:=fastStep_negX L hw hn X Y false origin cx
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second finish
  rw [back] at second
  exact (first.seq second).seq finish


theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
        L.point.finite ^^ decide (X'.val ≠ 5)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    have mid := midFFused_values L hw hn cx cy 5 0 5 0 false s.basis false
      (fun base' => generic_false L hw hn 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2 := zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (x.val ≠ 5) = true := decide_eq_true (val_ne_five hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide ((genericX x y cx cy).val ≠ 5) = true :=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end Correct
attribute [local irreducible] restE restX entryStage secondStage generic mid gen
  ReflectionE1.restE ReflectionE1.restX ReflectionE1.tailP ReflectionE1.generic ReflectionE1.gen
  Rolling1588TickGap.tailPhase Rolling1588TickGap.stackForward Rolling1588.stackForward
  Rolling1588.firstPhase Rolling1588.lastPhase Rolling1588.entryFieldHosted Rolling1588.exitFieldHosted

private theorem relation_of_shapes (R : Program→Program→Prop) (P Q A B : Program)
    (left : P=A) (right : Q=B) (fact : R A B) : R P Q := by
  cases left
  cases right
  exact fact

private theorem fact_of_shape (R : Program→Prop) (P Q : Program)
    (shape : P=Q) (fact : R Q) : R P := by
  cases shape
  exact fact

private def Facts (n g : Nat) (P Q : Program) : Prop :=
  toffoliCount P+n=toffoliCount Q ∧ measurementCount P=measurementCount Q ∧
    gateSlots P ≤ gateSlots Q+g ∧ wires P⊆wires Q

private theorem append_facts (P Q C : Program)
    (count : toffoliCount P+69=toffoliCount Q ∧ measurementCount P=measurementCount Q ∧
      gateSlots P ≤ gateSlots Q+1005) (sub : wires P⊆wires Q) : Facts 69 1005 (P++C) (Q++C) := by
  simp only [Facts,toffoliCount_append,measurementCount_append,gateSlots_append,wires_append]
  exact ⟨by omega,by omega,by omega,Finset.union_subset_union sub (Finset.Subset.refl _)⟩

private theorem tail_facts (a : Bool) :
    Facts 69 1005 (Rolling1588TickGap.tailPhase a) (ReflectionE1.tailP a) := by
  apply relation_of_shapes (Facts 69 1005) _ _
    (Rolling1588TickGap.stackForward a++skywalkArithmeticClear base)
    (Rolling1588.stackForward a++skywalkArithmeticClear base)
  · unfold Rolling1588TickGap.tailPhase
    rfl
  · unfold ReflectionE1.tailP
    rfl
  · exact append_facts _ _ _ (Rolling1588TickGap.stackForward_metrics a)
      (Rolling1588TickGap.stackForward_support a)

private def restContext (f g : Wire→Wire) (P R : Program) : Program :=
  renameProgram f (renameProgram g P++R)

private theorem rest_facts (f g : Wire→Wire) (P Q R : Program) (h : Facts 69 1005 P Q) :
    Facts 69 1005 (restContext f g P R) (restContext f g Q R) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (restContext f g P R)⊆wires (restContext f g Q R) := by
    simp only [restContext,renameProgram_support,wires_append]
    exact Finset.image_mono f
      (Finset.union_subset_union (Finset.image_mono g hw) (Finset.Subset.refl _))
  simp only [Facts,restContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem restE_facts (L : ControlledPointLayout) :
    Facts 69 1005 (restE L) (ReflectionE1.restE L) := by
  apply relation_of_shapes (Facts 69 1005) _ _
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase true)
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (ReflectionE1.tailP true)
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))
  · unfold restE restContext
    rfl
  · unfold ReflectionE1.restE restContext
    rfl
  · exact rest_facts _ _ _ _ _ (tail_facts true)

private theorem restX_facts (L : ControlledPointLayout) :
    Facts 69 1005 (restX L) (ReflectionE1.restX L) := by
  apply relation_of_shapes (Facts 69 1005) _ _
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false)
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (ReflectionE1.tailP false)
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))
  · unfold restX restContext
    rfl
  · unfold ReflectionE1.restX restContext
    rfl
  · exact rest_facts _ _ _ _ _ (tail_facts false)

private def stagesContext (Y M E S X EY N : Program) : Program :=
  (Y++M++E)++(S++X++EY)++N

private theorem stages_facts (Y M E E0 S X X0 EY N : Program)
    (entry : Facts 69 1005 E E0) (exit : Facts 69 1005 X X0) :
    Facts 138 2010 (stagesContext Y M E S X EY N) (stagesContext Y M E0 S X0 EY N) := by
  rcases entry with ⟨et,em,es,ew⟩
  rcases exit with ⟨xt,xm,xs,xw⟩
  have sub : wires (stagesContext Y M E S X EY N)⊆
      wires (stagesContext Y M E0 S X0 EY N) := by
    simp only [stagesContext,wires_append]
    exact Finset.union_subset_union
      (Finset.union_subset_union
        (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _)
          (Finset.Subset.refl _)) ew)
        (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) xw)
          (Finset.Subset.refl _))) (Finset.Subset.refl _)
  simp only [Facts,stagesContext,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy=stagesContext (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (exitY L cy) (fastConstNeg L cx) := by
  unfold generic entryStage secondStage stagesContext
  rfl

private theorem old_generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    ReflectionE1.generic L cx cy=stagesContext (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx) := by
  unfold ReflectionE1.generic ReflectionE1.entryStage ReflectionE1.secondStage stagesContext
  rfl

private theorem generic_facts (L : ControlledPointLayout) (cx cy : Fp) :
    Facts 138 2010 (generic L cx cy) (ReflectionE1.generic L cx cy) := by
  exact relation_of_shapes (Facts 138 2010) _ _ _ _
    (generic_shape L cx cy) (old_generic_shape L cx cy)
    (stages_facts (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx)
      (restE_facts L) (restX_facts L))

theorem generic_support_subset (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (ReflectionE1.generic L cx cy) :=
  (generic_facts L cx cy).2.2.2

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (generic_support_subset L cx cy).trans (ReflectionE1.generic_sites L hw hn cx cy)

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) :=
  fun used=>ReflectionE1.generic_free L hw hn cx cy i hi (generic_support_subset L cx cy used)

private theorem suffix_physical (P Q R : Program) (shape : P=Q++R)
    (physical : GatePhysical P) : GatePhysical R := by
  rw [shape,gatePhysical_append] at physical
  exact physical.2

private theorem restE_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restE L) := by
  have physical := placed_physical Rolling1588TickGap.entryKernel
    Rolling1588TickGap.entryKernel_support Rolling1588TickGap.entryKernel_physical L hw hn
  have entryPhysical : GatePhysical (FrontierEntry1591Callers.entry Rolling1588TickGap.entryKernel L) :=
    fact_of_shape GatePhysical _ _ (by unfold FrontierEntry1591Callers.entry;rfl) physical
  exact suffix_physical _ _ _ (entry_split L) entryPhysical

private theorem restX_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restX L) := by
  have physical := placed_physical Rolling1588TickGap.exitKernel
    Rolling1588TickGap.exitKernel_support Rolling1588TickGap.exitKernel_physical L hw hn
  have exitPhysical : GatePhysical (FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L) :=
    fact_of_shape GatePhysical _ _ (by unfold FrontierEntry1591Callers.exit;rfl) physical
  exact suffix_physical _ _ _ (exit_split L) exitPhysical

private theorem stages_physical (Y M E E0 S X X0 EY N : Program)
    (old : GatePhysical (stagesContext Y M E0 S X0 EY N))
    (entry : GatePhysical E) (exit : GatePhysical X) :
    GatePhysical (stagesContext Y M E S X EY N) := by
  simp only [stagesContext,gatePhysical_append] at old ⊢
  exact And.intro
    (And.intro (And.intro old.1.1.1 entry)
      (And.intro (And.intro old.1.2.1.1 exit) old.1.2.2)) old.2

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old := fact_of_shape GatePhysical _ _ (old_generic_shape L cx cy).symm
    (ReflectionE1.generic_physical L hw hn cx cy)
  exact fact_of_shape GatePhysical _ _ (generic_shape L cx cy)
    (stages_physical (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx) old
      (restE_physical L hw hn) (restX_physical L hw hn))

private def wrapContext (Z C : Program) (f : Wire→Wire) (P : Program) : Program :=
  Z++(C++renameProgram f P++C)++Z

private theorem wrap_facts (Z C : Program) (f : Wire→Wire) (P Q : Program)
    (h : Facts 138 2010 P Q) : Facts 138 2010 (wrapContext Z C f P) (wrapContext Z C f Q) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (wrapContext Z C f P)⊆wires (wrapContext Z C f Q) := by
    simp only [wrapContext,wires_append,renameProgram_support]
    exact Finset.union_subset_union
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union
          (Finset.union_subset_union (Finset.Subset.refl _) (Finset.image_mono f hw))
          (Finset.Subset.refl _))) (Finset.Subset.refl _)
  simp only [Facts,wrapContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem gen_facts (L : ControlledPointLayout) (cx cy : Fp) :
    Facts 138 2010 (gen L cx cy) (ReflectionE1.gen L cx cy) := by
  apply relation_of_shapes (Facts 138 2010) _ _
    (wrapContext (zrep L) (clrF L) (swapF L) (generic L cx cy))
    (wrapContext (zrep L) (clrF L) (swapF L) (ReflectionE1.generic L cx cy))
  · unfold gen mid wrapContext
    rfl
  · unfold ReflectionE1.gen ReflectionE1.mid wrapContext
    rfl
  · exact wrap_facts _ _ _ _ _ (generic_facts L cx cy)

theorem gen_metrics (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+138=toffoliCount (ReflectionE1.gen L cx cy) ∧
    measurementCount (gen L cx cy)=measurementCount (ReflectionE1.gen L cx cy) ∧
    gateSlots (gen L cx cy) ≤ gateSlots (ReflectionE1.gen L cx cy)+2010 :=
  ⟨(gen_facts L cx cy).1,(gen_facts L cx cy).2.1,(gen_facts L cx cy).2.2.1⟩

theorem gen_support_subset (L : ControlledPointLayout) (cx cy : Fp) :
    wires (gen L cx cy)⊆wires (ReflectionE1.gen L cx cy) := (gen_facts L cx cy).2.2.2

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L cx cy).trans (ReflectionE1.gen_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have g:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append] using And.intro (And.intro z (And.intro (And.intro c g) c)) z

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 1588 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp)) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

private theorem wrapper_facts (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Facts 138 2010 P Q) :
    toffoliCount (Edges.wrapper L C cy P)+138=toffoliCount (Edges.wrapper L C cy Q) ∧
    measurementCount (Edges.wrapper L C cy P)=measurementCount (Edges.wrapper L C cy Q) ∧
    gateSlots (Edges.wrapper L C cy P) ≤ gateSlots (Edges.wrapper L C cy Q)+2010 := by
  rcases h with ⟨ht,hm,hs,_⟩
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 2151282 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout cx cy)).1
  have entryDelta := (ReflectionE1.gen_counts_delta layout layout_widths cx cy).1
  have baseline := Rolling1588BFFinal.wrapper_toffoli cx cy hc
  have entryWrapperDelta :
      toffoliCount (Edges.wrapper layout (.some hc) cy (ReflectionE1.gen layout cx cy))+759=
        toffoliCount (Edges.wrapper layout (.some hc) cy (Rolling1588BFFinal.gen layout cx cy)) := by
    simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,
      (renameProgram_counts _ _).1]
    omega
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 1499214 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout cx cy)).2.1
  have old:=ReflectionE1.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 50191209+Rolling1588.slotGrowth := by
  have diff:=(wrapper_facts layout C cy _ _ (gen_facts layout cx cy)).2.2
  have old:=ReflectionE1.wrapper_slots C cx cy
  omega

end ECDSAAdd.Entrant.ReflectionE1TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1TickGapFinal =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1TickGap

/-! E1/reflected Q1588 point with the two checked TickGap forward tails. -/
namespace ECDSAAdd.Entrant.ReflectionE1TickGap
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151282,1499214,1588,50191209+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2151282 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1499214 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50191209+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1499214
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50191209+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C


end ECDSAAdd.Entrant.ReflectionE1TickGap
end -- original module boundary

-- Checked Low48 dependencies follow; the selected reflected prefix retains both checked TickGap tails.

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Square =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareResources
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Square

/-! Only the retained E1 square prefix changes. The reflected entry and all maps stay fixed. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1Low48Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

abbrev K : Nat := ControlLoan1589BFFold.K

def core (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.branchCK L ext control++LowZero18Square.branchBF L ext control++
    LowZero18Square.branchAF L ext control

def fastCore (L : ControlledPointLayout) : Program :=
  core L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def program (L : ControlledPointLayout) : Program :=
  SquareCarryLoan719BF.place L (fastCore L)

theorem raw_split (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) :
    LowZero18Square.raw L ext control=core L ext control++LowZero18Square.reflection L ext := rfl

theorem program_split (L : ControlledPointLayout) :
    LowZero18Square.program L=program L++ReflectionE1Square.reflectedTail L := by
  change SquareCarryLoan719BF.place L (LowZero18Square.raw L.dialogStreamedSquareWide
      (OwnDiagAll12Square.kext L) L.core.generic)=
    SquareCarryLoan719BF.place L (core L.dialogStreamedSquareWide
      (OwnDiagAll12Square.kext L) L.core.generic)++
    SquareCarryLoan719BF.place L (SquareCarryLoan719BF.reflection
      L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L))
  rw [raw_split,ReflectionE1Square.place_append]
  rfl

theorem raw_core_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (core L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (core L ext control) records s).basis=
      SquareReduction.p-1-
        (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
          (if s.basis control then K else 0))%SquareReduction.p) ∧
    ∀q,q∉L.core.out → (run (core L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (LowZero18Square.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := LowZero18Square.branchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (LowZero18Square.branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := LowZero18Square.branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc)
      ((hf.2 _ (ParkCarryDevelop.sumCarry_off_regs L nd).1).trans hs0) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (LowZero18Square.branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := LowZero18Square.branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc)
      ((hf.2 _ (ParkCarryDevelop.sumCarry_off_regs L nd).1).trans hs0) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := (stepC.seq stepB).seq stepA
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  have oaLt : OA<SquareReduction.p := ofCast_lt _ _
  have reflected : OA=SquareReduction.p-1-
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) := by
    change SquareReduction.p-1-OA=
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) at exactResult
    omega
  exact ⟨phase,value.trans reflected,frame⟩


open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCore_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(((X+p-(if B then Y*Y else 0)%p)%p+(if B then ControlLoan1589BFFold.K else 0))%p) ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (OwnDiagAll12Square.kext_mem L hw q hq))
  have extOK:=OwnDiagAll12Square.kext_ok L hw hn
  have hext : ECDSAAdd.Entrant.ExtOK K L.core.generic (OwnDiagAll12Square.kext L) :=
    ⟨extOK.nodup,extOK.away,extOK.len⟩
  have kernel := raw_core_correct K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean hext hz
  simpa only [fastCore,hb,hp,pow_two] using kernel


private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem sub_val (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

theorem fastCore_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  have fresh:=fastCore_correct L hw hn X.val Y.val G X.isLt s m v.generic v.x v.y v.clean
  refine ⟨fresh.1,?_,fresh.2.2⟩
  have hK : ((SquareCarryLoan719BF.K:Nat):Fp).val=SquareCarryLoan719BF.K :=
    ZMod.val_natCast_of_lt (by norm_num [SquareCarryLoan719BF.K,ControlLoan1589BFFold.K,p])
  rw [ZMod.val_add,sub_val]
  cases G
  · simpa using fresh.2.1
  · simpa [ZMod.val_mul,hK,K,SquareCarryLoan719BF.K] using fresh.2.1

private theorem pool_away_x (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have dis:=(List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  intro hx
  have resident : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis resident hq

theorem boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (program L) m s).phase=s.phase ∧
    regValue L.point.x (run (program L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (program L) m s).basis q=s.basis q := by
  have result:=fastCore_boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (fastCore L) m s=out := ⟨_,rfl⟩
  rw [heq] at result
  have clean : regValue L.dialogPool out.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq)),v.clean]
  have eq:=ReflectionE1Square.place_run_eq L hw (fastCore L) s m v.clean (by rw [heq];exact clean)
  change run (program L) m s=run (fastCore L) m s at eq
  rw [eq,heq]
  exact result

theorem cleanup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    regValue L.dialogPool (run (program L) m s).basis=0 := by
  have result:=boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (program L) m s=out := ⟨_,rfl⟩
  rw [heq] at result ⊢
  exact (regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq))).trans v.clean

/-- This comparison is separate from the direct boundary proof. -/
theorem run_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (mNew mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) mNew s=run (ReflectionE1Square.program L) mOld s := by
  obtain ⟨a,ha⟩ : ∃a : State,run (program L) mNew s=a := ⟨_,rfl⟩
  obtain ⟨b,hb⟩ : ∃b : State,run (ReflectionE1Square.program L) mOld s=b := ⟨_,rfl⟩
  have fresh:=boundary L hw hn X Y G origin s mNew v
  have prior:=ReflectionE1Square.boundary L hw hn X Y G origin s mOld v
  rw [ha] at fresh
  rw [hb] at prior
  rw [ha,hb]
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · funext q
    by_cases hx : q∈L.point.x
    · exact (regValue_eq_iff _ _ _).mp (fresh.2.1.trans prior.2.1.symm) q hx
    · exact (fresh.2.2 q hx).trans (prior.2.2 q hx).symm

private theorem window_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (LowZero18Square.withLowK2 L ext control src dst body)+558+10*(if src.length=128 then 0 else 1)=
      toffoliCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) ∧
    measurementCount (LowZero18Square.withLowK2 L ext control src dst body)+21+3*(if src.length=128 then 0 else 1)=
      measurementCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have a:=LowZero18Square.withLowK2_counts_diff L hw ext control src dst body h128 h129 hd he
  have b:=LowZero18Square.withLowK2_counts_diff L hw ext control src dst body h128 h129 hd he
  constructor <;> omega

private theorem window_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (LowZero18Square.withLowK2 L ext control src dst body)⊆
      wires (SquareCarryLoan719BF.withLowK2 L ext control src dst body) :=
  LowZero18Square.withLowK2_support_subset L hw ext control src dst body h128 h129 hd he

private theorem window_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (SquareCarryLoan719BF.withLowK2 L ext control src dst body) :=
  LowZero18Square.withLowK2_slots_le L hw ext control src dst body h128 h129 hd he

private theorem core_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    toffoliCount (core L ext control)+3026=toffoliCount (ReflectionE1Square.core L ext control) ∧
    measurementCount (core L ext control)+75=measurementCount (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_counts L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_counts L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_counts L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 129 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := CachedCarryBodyDevelop.hosted_window_rel L hw ext control L.core.high (L.core.product.take 256)
  obtain ⟨a1,a2,a3,a4⟩ := InverseCarryDevelop.hostedA_window_rel L hw ext control L.core.low (L.core.product.take 256)
  rw [if_neg (show ¬L.core.sum.length=128 by omega)] at c
  rw [if_pos high] at b
  rw [if_pos low] at a
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,toffoliCount_append,measurementCount_append]
  constructor <;> omega

private theorem core_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    wires (core L ext control)⊆wires (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_support L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_support L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_support L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 129 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := CachedCarryBodyDevelop.hosted_window_rel L hw ext control L.core.high (L.core.product.take 256)
  obtain ⟨a1,a2,a3,a4⟩ := InverseCarryDevelop.hostedA_window_rel L hw ext control L.core.low (L.core.product.take 256)
  have k3 := q3.trans k3
  have b := b3.trans (Finset.insert_subset_insert L.core.sumCarry b)
  have a := a3.trans (Finset.insert_subset_insert L.core.sumCarry a)
  have ck:wires (LowZero18Square.branchCK L ext control)⊆wires (SquareCarryLoan719BF.branchCK L ext control) := by
    simp only [LowZero18Square.branchCK,SquareCarryLoan719BF.branchCK,wires_append]
    repeat' apply Finset.union_subset_union
    all_goals first | exact k3.trans c | exact Finset.Subset.refl _
  have qmem:L.core.sumCarry∈wires (SquareCarryLoan719BF.branchCK L ext control) := by
    simp only [SquareCarryLoan719BF.branchCK,wires_append]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (ParkCarryDevelop.sumCarry_gPrep L hw))
  have cb:=ParkCarryDevelop.absorb_support L.core.sumCarry _ _ _ _ ck b qmem
  have qab:L.core.sumCarry∈wires (SquareCarryLoan719BF.branchCK L ext control++SquareCarryLoan719BF.branchBF L ext control) := by
    rw [wires_append];exact Finset.mem_union_left _ qmem
  have cba:=ParkCarryDevelop.absorb_support L.core.sumCarry _ _ _ _ cb a qab
  simp only [wires_append] at cba
  simp only [core,ReflectionE1Square.core,wires_append]
  exact cba

private theorem core_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (core L ext control)≤Challenge.gateSlots (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_slots L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_slots L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_slots L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 129 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := CachedCarryBodyDevelop.hosted_window_rel L hw ext control L.core.high (L.core.product.take 256)
  obtain ⟨a1,a2,a3,a4⟩ := InverseCarryDevelop.hostedA_window_rel L hw ext control L.core.low (L.core.product.take 256)
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,Challenge.gateSlots_append]
  omega

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+3026=toffoliCount (ReflectionE1Square.program L) ∧
    measurementCount (program L)+75=measurementCount (ReflectionE1Square.program L) := by
  have h:=core_counts_diff L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,ReflectionE1Square.program,fastCore,ReflectionE1Square.fastCore,
    (ReflectionE1Square.place_counts _ _).1,(ReflectionE1Square.place_counts _ _).2] using h

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=48978 ∧ measurementCount (program L)=52745 := by
  have a:=counts_diff L hw
  have b:=ReflectionE1Square.counts L hw
  constructor <;> omega

theorem support_subset (L : ControlledPointLayout) (hw : L.Widths) :
    wires (program L)⊆wires (ReflectionE1Square.program L) := by
  unfold program ReflectionE1Square.program SquareCarryLoan719BF.place
  repeat' apply OneFlagReplay.rename_subset
  exact core_support_subset L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L hw).trans (ReflectionE1Square.support L hw hn)

theorem free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program L) :=
  fun used=>ReflectionE1Square.free L hw hn i hi (support_subset L hw used)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  have full:=LowZero18Square.physical L hw hn
  rw [program_split,gatePhysical_append] at full
  exact full.1

theorem slots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (ReflectionE1Square.program L) := by
  have h:=core_slots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,ReflectionE1Square.program,fastCore,ReflectionE1Square.fastCore,
    SquareCarryLoan719BF.place,Baselines.rename_gateSlots] using h

end ECDSAAdd.Entrant.ReflectionE1Low48Square
end -- original module boundary



section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.CachedCarryBodyDevelop
open Arithmetic

theorem hosted_fold_support (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (hn:L.wires.Nodup) (ext : List Wire) (c : Wire) (hlen:300≤ext.length)
    (away:∀q∈ext,q∉L.wires) :
    wires (hostedBody L (LowZero18Square.foldPerm L ext) c)⊆(c::L.wires).toFinset := by
  rw [hosted_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away)]
  exact body_support L hw hn c

end ECDSAAdd.Entrant.CachedCarryBodyDevelop
end

section
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic
 theorem hostedA_fold_support (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (hn:L.wires.Nodup) (ext : List Wire) (c : Wire) (hlen:300≤ext.length)
    (away:∀q∈ext,q∉L.wires) :
    wires (hostedA L (LowZero18Square.foldPerm L ext) c)⊆(c::L.wires).toFinset := by
  rw [hostedA_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away)]
  exact aBodyCached_support L hw hn c
end ECDSAAdd.Entrant.InverseCarryDevelop
end

-- ===== R2 (sqep component): square with retired poolWire 760 =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


/-! # Square -/

namespace ECDSAAdd.Entrant.R2SqEp760
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

/-! ## Square: definitions -/

/-- The retired square site: fold-pad bit 239 (= `ktmp[108]`, carry #239 of every reflected core
adder; physically `poolWire 760`). -/
def sqRet (L : CuccaroStreamedSquareWideLayout) : Wire := L.foldPad.getD 239 0
/-- Its body host: extension wire 130 (physically `poolWire 1363`). -/
def sqHost (ext : List Wire) : Wire := ext.getD 130 0
def sqSwap (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) : Equiv.Perm Wire :=
  Equiv.swap (sqRet L) (sqHost ext)
def bodySwap (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (B : Program) : Program :=
  renameProgram (sqSwap L ext) B

def branchCK760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagAll12Square.gPrep L++
    LowZero18Square.withLowK2 L ext control L.core.sum L.core.product
      (bodySwap L ext (OwnDiagAll12Square.bodyCKTq L control))++
    OwnDiagAll12Square.gClear L

def branchBF760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.withLowK2 L ext control L.core.high (L.core.product.take 256)
    (bodySwap L ext (CachedCarryBodyDevelop.hostedBody L (LowZero18Square.foldPerm L ext) control))

def branchAF760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.withLowK2 L ext control L.core.low (L.core.product.take 256)
    (bodySwap L ext (InverseCarryDevelop.hostedA L (LowZero18Square.foldPerm L ext) control))

def core760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK760 L ext control++branchBF760 L ext control++branchAF760 L ext control

def fastCore760 (L : ControlledPointLayout) : Program :=
  core760 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

/-- The new square: `ReflectionE1Low48Square.program` with the three body swaps. -/
def program760 (L : ControlledPointLayout) : Program :=
  SquareCarryLoan719BF.place L (fastCore760 L)

/-! ## Square: positions of the two sites -/

section Sites
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
include hw

theorem foldPad_length : L.foldPad.length=254 := by
  simp [foldPad,hw.core.pad,hw.overflowPad]

omit hw in
theorem sqRet_ktmp : sqRet L=(LowZero18LowK.ktmp L).getD 108 0 := by
  simp only [sqRet,LowZero18LowK.ktmp,List.getD_eq_getElem?_getD,List.getElem?_drop]

theorem sqRet_mem_ktmpTail : sqRet L∈(LowZero18LowK.ktmp L).drop 99 := by
  rw [sqRet_ktmp L]
  have len := LowZero18LowK.ktmp_length L hw
  rw [List.getD_eq_getElem _ _ (by omega)]
  have h : (LowZero18LowK.ktmp L)[108]'(by omega)=((LowZero18LowK.ktmp L).drop 99)[9]'(by simp; omega) := by
    simp
  rw [h]
  exact List.getElem_mem _

theorem sqRet_mem_overflow : sqRet L∈L.overflowPad := by
  have h : sqRet L=L.overflowPad.getD 111 0 := by
    simp only [sqRet,foldPad,List.getD_eq_getElem?_getD,List.getElem?_append_right
      (show L.core.pad.length≤239 by rw [hw.core.pad]; omega),hw.core.pad]
  rw [h,List.getD_eq_getElem _ _ (by rw [hw.overflowPad]; omega)]
  exact List.getElem_mem _

theorem sqRet_mem_wires : sqRet L∈L.wires := by
  simp only [CuccaroStreamedSquareWideLayout.wires,List.mem_append]
  exact Or.inr (sqRet_mem_overflow L hw)

end Sites

theorem sqHost_mem (ext : List Wire) (he : 300≤ext.length) : sqHost ext∈ext := by
  rw [sqHost,List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

/-- `sqRet` is outside the core layout (it is an overflow-pad site). -/
theorem sqRet_not_core (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) : sqRet L∉L.core.wires := by
  have overflow := sqRet_mem_overflow L hw
  have dis := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.2
  exact fun used=>dis (sqRet L) used (sqRet L) overflow rfl

/-! ## Square: support facts -/

section Support
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)

/-- Everything a LowZero leaf kernel names, except the untouched tail of `ktmp`. -/
def kOuter : List Wire :=
  (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++
    (LowZero18LowK.ktmp L).take 99)++ext

include hn hs hd hx hdx in
theorem ktail_away (q : Wire) (hq : q∈(LowZero18LowK.ktmp L).drop 99) :
    q∉kOuter L control ext src dst := by
  apply kdis (LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx) _ q hq
  intro w
  have e := congrArg (List.count w) (List.take_append_drop 99 (LowZero18LowK.ktmp L))
  rw [List.count_append] at e
  simp only [kOuter,LowZero18LowK.kbig2,List.count_append,List.count_cons] at e ⊢
  omega

private theorem mem_tk {l : List Wire} {n : Nat} {q : Wire} (h : q∈l.take n) : q∈l := List.mem_of_mem_take h
private theorem mem_dr {l : List Wire} {n : Nat} {q : Wire} (h : q∈l.drop n) : q∈l := List.mem_of_mem_drop h
private theorem mem_dt {l : List Wire} {a b : Nat} {q : Wire} (h : q∈(l.drop a).take b) : q∈l.take (a+b) := by
  have e : (l.drop a).take b=(l.take (a+b)).drop a := by rw [List.drop_take]; simp
  rw [e] at h
  exact List.mem_of_mem_drop h

private theorem mem_66 {l : List Wire} {q : Wire} (h : q∈l.take 66) : q∈l.take 99 := by
  have e : l.take 66=(l.take 99).take 66 := by rw [List.take_take]; rfl
  rw [e] at h
  exact List.mem_of_mem_take h

/-- Every wire of the leaf kernel's register inventory lies in `kOuter`. -/
theorem kall_outer (q : Wire) (h : q∈(LowZero18LowK.kg L ext src dst).all) :
    q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons]
  unfold LowZero18LowK.kg at h
  split_ifs at h
  all_goals
    simp only [LowZero18LowK.kgH,LowZero18LowK.kgS,KG.all,KG.X,KRegs.all,LowZero18LowK.oregs,
      LowZero18LowK.iregs,LowZero18LowK.jregsH,LowZero18LowK.jregsS,KRegs.lo,KRegs.dlo,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    repeat' (refine Or.elim h (fun h => ?_) (fun h => ?_))
    all_goals first
      | simp [h]
      | simp [mem_tk h]
      | simp [mem_dr h]
      | simp [mem_tk (mem_tk h)]
      | simp [mem_dr (mem_tk h)]
      | simp [mem_tk (mem_dr h)]
      | simp [mem_dr (mem_tk (mem_tk h))]
      | simp [mem_66 (mem_tk h)]
      | simp [mem_66 (mem_tk (mem_tk h))]
      | simp [mem_dt h]

include hw hn hs hd hx hdx in
theorem sqRet_not_outer : sqRet L∉kOuter L control ext src dst :=
  ktail_away L control hn ext src dst hs hd hx hdx _ (sqRet_mem_ktmpTail L hw)

include hw hn hs hd hx hdx in
theorem sqRet_ne_of_outer (q : Wire) (hq : q∈kOuter L control ext src dst) : sqRet L≠q :=
  fun e => sqRet_not_outer L hw control hn ext src dst hs hd hx hdx (e ▸ hq)

theorem ktmp_eq : OwnDiagLowK.ktmp L=LowZero18LowK.ktmp L := rfl

theorem tk99_outer (q : Wire) (h : q∈(LowZero18LowK.ktmp L).take 99) : q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons]; tauto

theorem ext_outer (q : Wire) (h : q∈ext) : q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append]; tauto

theorem cs_outer (q : Wire) (h : q∈control::(src++L.inputBank.take src.length)) :
    q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons] at h ⊢; tauto

include hw in
theorem target_outer : SquareCarryLoan719.target L∈kOuter L control ext src dst := by
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.target L∈(LowZero18LowK.ktmp L).take 99 := by
    change (LowZero18LowK.ktmp L).getD 67 0∈_
    rw [List.getD_eq_getElem _ _ (by omega)]
    have : (LowZero18LowK.ktmp L)[67]'(by omega)=((LowZero18LowK.ktmp L).take 99)[67]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _
  exact tk99_outer L control ext src dst _ m

include hw in
theorem earlyHost_outer : SquareCarryLoan719.earlyHost L∈kOuter L control ext src dst := by
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.earlyHost L∈(LowZero18LowK.ktmp L).take 99 := by
    change (LowZero18LowK.ktmp L).getD 1 0∈_
    rw [List.getD_eq_getElem _ _ (by omega)]
    have : (LowZero18LowK.ktmp L)[1]'(by omega)=((LowZero18LowK.ktmp L).take 99)[1]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _
  exact tk99_outer L control ext src dst _ m

include hw hn hs hd hx hdx in
theorem sqRet_masks :
    sqRet L∉wires (copyRegister (some control) src (L.inputBank.take src.length)) ∧
    sqRet L∉wires (eraseMask control src (L.inputBank.take src.length)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  constructor
  · intro used
    have h := List.mem_toFinset.mp (copyRegister_wires_subset (some control) src (L.inputBank.take src.length) used)
    exact ne _ (cs_outer L control ext src dst _ (by simpa only [Option.toList_some,List.singleton_append,
      List.cons_append,List.append_assoc] using h)) rfl
  · intro used
    have h := List.mem_toFinset.mp (eraseMask_wires_subset control src (L.inputBank.take src.length) used)
    exact ne _ (cs_outer L control ext src dst _ h) rfl

include hw hn hs hd hx hdx in
theorem sqRet_cached_mask (hpos : 0<dst.length) :
    sqRet L∉wires (CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst)
      src (L.inputBank.take src.length)) := by
  have masks := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have cacheIn : LowZero18Square.cacheWire L dst∈kOuter L control ext src dst := by
    rw [LowZero18Square.cacheWire_fixed L hw (List.nodup_cons.mp hn).2 dst hd hpos]
    have mem := CachedSquareCopy.head_mem dst hpos
    simp only [kOuter,List.mem_cons,List.mem_append]
    tauto
  intro used
  have h := CachedSquareCopy.wires_subset control (LowZero18Square.cacheWire L dst)
    src (L.inputBank.take src.length) used
  rcases Finset.mem_union.mp h with h|h
  · exact masks.1 h
  · exact ne _ cacheIn (Finset.mem_singleton.mp h)

include hw hn hs hd hx hdx in
theorem sqRet_kernels (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (he : 300≤ext.length) :
    sqRet L∉wires (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) ∧
    sqRet L∉wires (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have sup := LowZero18LowK.kg_support L hw ext src dst h128 hsmax hlen he
  have offAll : sqRet L∉((LowZero18LowK.kg L ext src dst).all.toFinset) := fun h =>
    ne _ (kall_outer L control ext src dst _ (List.mem_toFinset.mp h)) rfl
  have fix : SquareCarryLoan719.earlyPerm L (sqRet L)=sqRet L := by
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (ne _ (target_outer L hw control ext src dst))
      (ne _ (earlyHost_outer L hw control ext src dst))
  have mk : sqRet L∉wires (LowZero18KG.make (LowZero18LowK.kg L ext src dst)) := fun h => offAll (sup.1 h)
  have cl : sqRet L∉wires (LowZero18KG.clear (LowZero18LowK.kg L ext src dst)) := fun h => offAll (sup.2 h)
  let K := LowZero18LowK.kg L ext src dst
  let T := K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591
  let C := K.R.smkT++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591++K.Q2c
  have o1 : LowZero18KG.make K=K.Q1++T := by simp only [LowZero18KG.make,T,List.append_assoc]
  have n1 : LowZero18Square.make L K=renameProgram (SquareCarryLoan719.earlyPerm L) K.Q1++T := by
    simp only [LowZero18Square.make,LowZero18KG.make,SquareCarryLoan719.patchKG,T,List.append_assoc]
  have o2 : LowZero18KG.clear K=C++K.Q1c := by simp only [LowZero18KG.clear,C,List.append_assoc]
  have n2 : LowZero18Square.clear L K=C++renameProgram (SquareCarryLoan719.earlyPerm L) K.Q1c := by
    simp only [LowZero18Square.clear,LowZero18KG.clear,SquareCarryLoan719.patchKG,C,List.append_assoc]
  rw [o1,wires_append,Finset.mem_union,not_or] at mk
  rw [o2,wires_append,Finset.mem_union,not_or] at cl
  constructor
  · change sqRet L∉wires (LowZero18Square.make L K)
    rw [n1,wires_append,Finset.mem_union,not_or]
    exact ⟨OwnPlusHost.rename_avoid _ _ _ fix mk.1,mk.2⟩
  · change sqRet L∉wires (LowZero18Square.clear L K)
    rw [n2,wires_append,Finset.mem_union,not_or]
    exact ⟨cl.1,OwnPlusHost.rename_avoid _ _ _ fix cl.2⟩

end Support

section Core
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)

include hw in
theorem g_core_support :
    wires (OwnDiagAll12Square.gPrep L)⊆L.core.wires.toFinset ∧
    wires (OwnDiagAll12Square.gClear L)⊆L.core.wires.toFinset := by
  let M : CuccaroStreamedSquareWideLayout := ⟨L.core,L.core.pad.take 126⟩
  have mhw : M.Widths := ⟨hw.core,by simp [M,hw.core.pad]⟩
  have sub : (L.core.cin::M.wires).toFinset⊆L.core.wires.toFinset := by
    intro q used
    have h := List.mem_toFinset.mp used
    rcases List.mem_cons.mp h with h|h
    · subst q
      simp [CuccaroStreamedSquareLayout.wires]
    · change q∈L.core.wires++L.core.pad.take 126 at h
      rcases List.mem_append.mp h with h|h
      · exact List.mem_toFinset.mpr h
      · have hp := List.mem_of_mem_take h
        simp [CuccaroStreamedSquareLayout.wires,hp]
  have support := OwnDiagAll12Square.gSum_support M mhw L.core.cin
  exact ⟨support.1.trans sub,support.2.trans sub⟩

end Core

section Free
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
  (hext : 300≤ext.length)

include hext in
theorem sqHost_in : sqHost ext∈ext := sqHost_mem ext hext

include hw hdx hext in
theorem sqHost_ne_target : sqHost ext≠SquareCarryLoan719.target L := by
  intro e
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.target L∈LowZero18LowK.ktmp L := by
    change (LowZero18LowK.ktmp L).getD 67 0∈_
    exact DiagSq.getD_in _ 67 (by omega)
  have w : SquareCarryLoan719.target L∈control::L.wires :=
    List.mem_cons_of_mem _ (LowZero18LowK.ktmp_wires L _ m)
  exact hdx _ (sqHost_in ext hext) (e ▸ w)

include hx hext in
theorem sqHost_ne_ext0 : sqHost ext≠ext.getD 0 0 := by
  intro e
  rw [sqHost,List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  omega

include hw hx hdx hext in
theorem sqHost_fold_free (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqHost ext∉wires (renameProgram (SquareCarryLoan719.foldPerm L ext) B) := by
  rw [SquareCarryLoan719.foldPerm_eq L hw]
  apply OwnPlusHost.rename_avoid _ _ _
    (Equiv.swap_apply_of_ne_of_ne (sqHost_ne_target L hw control ext hdx hext) (sqHost_ne_ext0 ext hx hext))
  exact fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used))

include hw hn hx hdx hext in
theorem sqRet_body_free (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqRet L∉wires (renameProgram (SquareCarryLoan719.foldPerm L ext) (bodySwap L ext B)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  rw [SquareCarryLoan719.foldPerm_eq L hw]
  apply OwnPlusHost.rename_avoid _ _ _
    (Equiv.swap_apply_of_ne_of_ne (ne _ (target_outer L hw control ext src dst))
      (ne _ (ext_outer L control ext src dst _ (DiagSq.getD_in ext 0 (by omega)))))
  exact swap_free _ _ _ (fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used)))

include hw hn hx hdx hext in
theorem withLowK2_760_free (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqRet L∉wires (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B)) := by
  have m := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have k := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen hext
  have cached := sqRet_cached_mask L hw control hn ext src dst hs hd hx hdx (by omega)
  have f := sqRet_body_free L hw control hn ext hx hdx hext src dst hs hd B hb
  simp only [LowZero18Square.withLowK2,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨m.1,k.1⟩,m.2⟩,f⟩,cached⟩,k.2⟩,m.2⟩

include hw hn hx hdx hext in
theorem core760_free : sqRet L∉wires (core760 L ext control) := by
  have nd := (List.nodup_cons.mp hn).2
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have hl (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have hh (q : Wire) : L.core.high.count q≤L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := hh q
    simp only [List.count_append]
    omega
  have hs (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := hh q
    simp only [CuccaroStreamedSquareLayout.sum,List.count_append] at h ⊢
    omega
  have hp (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have sa := withLowK2_760_free L hw control hn ext hx hdx hext L.core.low (L.core.product.take 256)
    hl hp (by omega) (by omega) (by simp [hw.core.product,low]) _ (InverseCarryDevelop.hostedA_fold_support L hw nd ext control hext (fun q hq h=>hdx q hq (List.mem_cons_of_mem control h)))
  have sb := withLowK2_760_free L hw control hn ext hx hdx hext L.core.high (L.core.product.take 256)
    hb hp (by omega) (by omega) (by simp [hw.core.product,high]) _ (CachedCarryBodyDevelop.hosted_fold_support L hw nd ext control hext (fun q hq h=>hdx q hq (List.mem_cons_of_mem control h)))
  have sc := withLowK2_760_free L hw control hn ext hx hdx hext L.core.sum L.core.product
    hs (fun _=>le_rfl) (by omega) (by omega) (by rw [hw.core.product,sum]) _
    (OwnDiagAll12Square.bodyCK_supportTq L hw nd control)
  have coreOff := sqRet_not_core L hw control hn
  have gs := g_core_support L hw
  have gp : sqRet L∉wires (OwnDiagAll12Square.gPrep L) := fun u => coreOff (List.mem_toFinset.mp (gs.1 u))
  have gc : sqRet L∉wires (OwnDiagAll12Square.gClear L) := fun u => coreOff (List.mem_toFinset.mp (gs.2 u))
  simp only [core760,branchCK760,branchBF760,branchAF760,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨gp,sc⟩,gc⟩,sb⟩,sa⟩

end Free

section Placed
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
private theorem pool_getD' (i : Nat) (hi : i<2613) : L.dialogPool.getD i 0=L.core.poolWire i := by
  have shape := pool_block L hw 2613 (le_refl _)
  rw [List.take_of_length_le (by rw [L.dialogPool_length hw])] at shape
  rw [shape,List.getD_eq_getElem _ _ (by simp [wireBlock];omega)]
  simp [wireBlock]

include hw in
theorem sqRet_pool760 : sqRet L.dialogStreamedSquareWide=L.core.poolWire 760 := by
  rw [sqRet_ktmp,← ktmp_eq,SquareCarryLoan719Inventory.ktmp_layout L hw,List.getD_eq_getElem _ _ (by
    simp only [List.length_take,List.length_drop,L.dialogPool_length hw]
    omega)]
  simp only [List.getElem_take,List.getElem_drop,Nat.reduceAdd]
  have bound : 760<L.dialogPool.length := by rw [L.dialogPool_length hw];omega
  have same := pool_getD' L hw 760 (by omega)
  rw [List.getD_eq_getElem L.dialogPool 0 bound] at same
  exact same

theorem sqHost_pool1363 : sqHost (OwnDiagAll12Square.kext L)=L.core.poolWire 1363 := by
  simp [sqHost,OwnDiagAll12Square.kext,wireBlock]

include hw hn in
private theorem pool_fix (k a b : Nat) (hk : k<2613) (ha : a<2613) (hb : b<2613) (na : k≠a) (nb : k≠b) :
    Equiv.swap (L.core.poolWire a) (L.core.poolWire b) (L.core.poolWire k)=L.core.poolWire k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq
    exact na (pool_inj L hw hn k a hk ha eq)
  · intro eq
    exact nb (pool_inj L hw hn k b hk hb eq)

include hw hn in
/-- Every placement map of the square fixes pool sites 760 and 1363. -/
theorem place_fix (k : Nat) (hk : k=760 ∨ k=1363) (P : Program) (free : L.core.poolWire k∉wires P) :
    L.core.poolWire k∉wires (SquareCarryLoan719BF.place L P) := by
  have kb : k<2613 := by omega
  have blockFix : Square5Placement.blockPerm L 202 (L.core.poolWire k)=L.core.poolWire k := by
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) k kb]
    rcases hk with rfl|rfl <;> rfl
  have p0 := OwnPlusHost.rename_avoid _ _ _ blockFix free
  have p1 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 766 1530 kb (by omega) (by omega) (by omega) (by omega)) p0
  have p2 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 765 1531 kb (by omega) (by omega) (by omega) (by omega)) p1
  have p3 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 767 1532 kb (by omega) (by omega) (by omega) (by omega)) p2
  have p4 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 770 1536 kb (by omega) (by omega) (by omega) (by omega)) p3
  have p5 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 1285 1537 kb (by omega) (by omega) (by omega) (by omega)) p4
  have p6 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 1286 1538 kb (by omega) (by omega) (by omega) (by omega)) p5
  have p7 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 769 1539 kb (by omega) (by omega) (by omega) (by omega)) p6
  have p8 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 768 775 kb (by omega) (by omega) (by omega) (by omega)) p7
  have p9 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 718 907 kb (by omega) (by omega) (by omega) (by omega)) p8
  simpa only [SquareCarryLoan719BF.place,OwnPlusSquare.swap,OwnGuardSquare.swap,
    OwnQ4Square.swap,OwnQ5Square.swap,OwnDiagAll12PlacedQ6.swap,OwnDiagAll12PlacedQ7.swap,
    PrefixFrontierSquare1591.swap,Prefix1590Square.swap,ControlLoan1589Square.swap] using p9

include hw hn in
/-- **R2 square deliverable**: the new square never touches physical pool site 760. -/
theorem square760_free : L.core.poolWire 760∉wires (program760 L) := by
  have controlND : (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have he := OwnDiagAll12Square.kext_ok L hw hn
  have core := core760_free L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    L.core.generic controlND (OwnDiagAll12Square.kext L) he.nodup he.away he.len
  rw [sqRet_pool760 L hw] at core
  exact place_fix L hw hn 760 (Or.inl rfl) _ core

end Placed

/-! ## Square: counts, slots, physicality, support -/

theorem gatePhysical_rename_iff (e : Equiv.Perm Wire) (P : Program) :
    GatePhysical (renameProgram e P)↔GatePhysical P := by
  constructor
  · intro h i hi
    have hh := h (renameInstr e i) (List.mem_map_of_mem hi)
    cases i <;> simp_all [renameInstr,RecordedQuantum.PhysicalInstr,ECDSAAdd.ProperGate,e.injective.eq_iff]
  · exact gatePhysical_rename e e.injective P

theorem place_physical_iff (L : ControlledPointLayout) (P : Program) :
    GatePhysical (SquareCarryLoan719BF.place L P)↔GatePhysical P := by
  simp only [SquareCarryLoan719BF.place,gatePhysical_rename_iff]

theorem fastCore760_shape (L : ControlledPointLayout) :
    ReflectionE1Low48Square.program L=SquareCarryLoan719BF.place L (ReflectionE1Low48Square.fastCore L) := rfl

theorem program760_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program760 L) := by
  have old := ReflectionE1Low48Square.physical L hw hn
  rw [fastCore760_shape,place_physical_iff] at old
  rw [program760,place_physical_iff]
  simp only [ReflectionE1Low48Square.fastCore,ReflectionE1Low48Square.core,LowZero18Square.branchCK,
    LowZero18Square.branchBF,LowZero18Square.branchAF,LowZero18Square.withLowK2,
    gatePhysical_append,gatePhysical_rename_iff] at old
  simp only [fastCore760,core760,branchCK760,branchBF760,branchAF760,LowZero18Square.withLowK2,bodySwap,
    gatePhysical_append,gatePhysical_rename_iff]
  exact old

theorem program760_counts (L : ControlledPointLayout) :
    toffoliCount (program760 L)=toffoliCount (ReflectionE1Low48Square.program L) ∧
    measurementCount (program760 L)=measurementCount (ReflectionE1Low48Square.program L) := by
  rw [fastCore760_shape]
  simp only [program760,SquareCarryLoan719BF.place,fastCore760,core760,branchCK760,branchBF760,branchAF760,
    ReflectionE1Low48Square.fastCore,ReflectionE1Low48Square.core,LowZero18Square.branchCK,
    LowZero18Square.branchBF,LowZero18Square.branchAF,LowZero18Square.withLowK2,bodySwap,
    toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    and_self]

theorem program760_slots (L : ControlledPointLayout) :
    Challenge.gateSlots (program760 L)=Challenge.gateSlots (ReflectionE1Low48Square.program L) := by
  rw [fastCore760_shape]
  simp only [program760,SquareCarryLoan719BF.place,fastCore760,core760,branchCK760,branchBF760,branchAF760,
    ReflectionE1Low48Square.fastCore,ReflectionE1Low48Square.core,LowZero18Square.branchCK,
    LowZero18Square.branchBF,LowZero18Square.branchAF,LowZero18Square.withLowK2,bodySwap,
    Challenge.gateSlots_append,Baselines.rename_gateSlots]

theorem counts_diff760 (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program760 L)+3026=toffoliCount (ReflectionE1Square.program L) ∧
    measurementCount (program760 L)+75=measurementCount (ReflectionE1Square.program L) := by
  rw [(program760_counts L).1,(program760_counts L).2]
  exact ReflectionE1Low48Square.counts_diff L hw

theorem slots_le760 (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program760 L)≤Challenge.gateSlots (ReflectionE1Square.program L) := by
  rw [program760_slots]; exact ReflectionE1Low48Square.slots_le L hw

theorem rename_ins (e : Equiv.Perm Wire) (h : Wire) (P Q : Program)
    (sub : wires P⊆insert h (wires Q)) (fix : e h=h) :
    wires (renameProgram e P)⊆insert h (wires (renameProgram e Q)) := by
  rw [renameProgram_support,renameProgram_support]
  intro q hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp (sub hx) with e'|hx'
  · subst x; rw [fix]; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx')

theorem swap_ins (a b : Wire) (P : Program) (hb : b∉wires P) :
    wires (renameProgram (Equiv.swap a b) P)⊆insert b (wires P) :=
  (swap_support a b P hb).trans (Finset.insert_subset_insert _ (Finset.erase_subset _ _))

section SupportNew
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
  (hext : 300≤ext.length)

include hw hx hdx hext in
theorem withLowK2_ins (src dst : List Wire) (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    wires (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B))⊆
      insert (sqHost ext) (wires (LowZero18Square.withLowK2 L ext control src dst B)) := by
  have bfree : sqHost ext∉wires B := fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used))
  have fix : SquareCarryLoan719.foldPerm L ext (sqHost ext)=sqHost ext := by
    rw [SquareCarryLoan719.foldPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (sqHost_ne_target L hw control ext hdx hext) (sqHost_ne_ext0 ext hx hext)
  have body := rename_ins _ _ _ _ (swap_ins (sqRet L) (sqHost ext) B bfree) fix
  intro q hq
  simp only [LowZero18Square.withLowK2,bodySwap,sqSwap,wires_append,Finset.mem_union,Finset.mem_insert] at hq ⊢
  rcases hq with ((((((h|h)|h)|h)|h)|h)|h)
  all_goals first
    | (rcases Finset.mem_insert.mp (body h) with e|e
       · exact Or.inl e
       · tauto)
    | tauto

include hw hn hx hdx hext in
theorem core760_ins : wires (core760 L ext control)⊆
    insert (sqHost ext) (wires (ReflectionE1Low48Square.core L ext control)) := by
  have nd := (List.nodup_cons.mp hn).2
  have a := withLowK2_ins L hw control ext hx hdx hext L.core.low (L.core.product.take 256) _
    (InverseCarryDevelop.hostedA_fold_support L hw nd ext control hext (fun q hq h=>hdx q hq (List.mem_cons_of_mem control h)))
  have b := withLowK2_ins L hw control ext hx hdx hext L.core.high (L.core.product.take 256) _
    (CachedCarryBodyDevelop.hosted_fold_support L hw nd ext control hext (fun q hq h=>hdx q hq (List.mem_cons_of_mem control h)))
  have c := withLowK2_ins L hw control ext hx hdx hext L.core.sum L.core.product _
    (OwnDiagAll12Square.bodyCK_supportTq L hw nd control)
  intro q hq
  simp only [core760,branchCK760,branchBF760,branchAF760,wires_append,Finset.mem_union] at hq
  simp only [ReflectionE1Low48Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,wires_append,Finset.mem_union,Finset.mem_insert]
  rcases hq with (((h|h)|h)|h)|h
  · tauto
  · rcases Finset.mem_insert.mp (c h) with e|e <;> tauto
  · tauto
  · rcases Finset.mem_insert.mp (b h) with e|e <;> tauto
  · rcases Finset.mem_insert.mp (a h) with e|e <;> tauto

end SupportNew

section SupportPlaced
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw hn in
theorem place_ins (P Q : Program) (sub : wires P⊆insert (L.core.poolWire 1363) (wires Q)) :
    wires (SquareCarryLoan719BF.place L P)⊆insert (L.core.poolWire 1363) (wires (SquareCarryLoan719BF.place L Q)) := by
  have kb : 1363<2613 := by omega
  have blockFix : Square5Placement.blockPerm L 202 (L.core.poolWire 1363)=L.core.poolWire 1363 := by
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) 1363 kb]; rfl
  have f (a b : Nat) (ha : a<2613) (hb : b<2613) (na : 1363≠a) (nb : 1363≠b) :=
    pool_fix L hw hn 1363 a b kb ha hb na nb
  simp only [SquareCarryLoan719BF.place]
  apply rename_ins _ _ _ _ _ (f 718 907 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 768 775 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 769 1539 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 1286 1538 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 1285 1537 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 770 1536 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 767 1532 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 765 1531 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 766 1530 (by omega) (by omega) (by omega) (by omega))
  exact rename_ins _ _ _ _ sub blockFix

include hw hn in
/-- New square support: the old square's support with site 760 replaced by site 1363. -/
theorem program760_support_subset :
    wires (program760 L)⊆insert (L.core.poolWire 1363)
      ((wires (ReflectionE1Low48Square.program L)).erase (L.core.poolWire 760)) := by
  have controlND : (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have he := OwnDiagAll12Square.kext_ok L hw hn
  have core := core760_ins L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    L.core.generic controlND (OwnDiagAll12Square.kext L) he.nodup he.away he.len
  rw [sqHost_pool1363 L] at core
  have placed := place_ins L hw hn _ _ core
  have free := square760_free L hw hn
  intro q hq
  rcases Finset.mem_insert.mp (placed hq) with e|e
  · exact e ▸ Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_erase.mpr ⟨fun h => free (h ▸ hq),e⟩

include hw hn in
theorem program760_support : wires (program760 L)⊆(OB5Support.sites L).toFinset := by
  have old := ReflectionE1Low48Square.support L hw hn
  intro q hq
  rcases Finset.mem_insert.mp (program760_support_subset L hw hn hq) with e|e
  · subst e
    simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1363,⟨by omega,by omega⟩,rfl⟩)))))
  · exact old (Finset.mem_of_mem_erase e)

include hw hn in
theorem program760_free_old (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program760 L) := by
  intro used
  rcases Finset.mem_insert.mp (program760_support_subset L hw hn used) with e|e
  · have ib : i<2613 := by simp at hi; omega
    have := pool_inj L hw hn i 1363 ib (by omega) e
    subst this; simp at hi
  · exact ReflectionE1Low48Square.free L hw hn i hi (Finset.mem_of_mem_erase e)

end SupportPlaced

/-! ## Square: the host is clean when the body starts -/

theorem top_bits_zero (r : List Wire) (st : BasisState) (k : Nat) (h : regValue r st<2^k)
    (q : Wire) (hq : q∈r.drop k) : st q=false := by
  by_cases hk : k≤r.length
  · have e := regValue_append (r.take k) (r.drop k) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left hk] at e
    have z : regValue (r.drop k) st=0 := by
      by_contra nz
      have : 2^k≤2^k*regValue (r.drop k) st := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero nz)
      omega
    exact (regValue_zero _ _).mp z q hq
  · rw [List.drop_eq_nil_of_le (by omega)] at hq
    simp at hq

theorem host_not_drop (ext : List Wire) (hx : ext.Nodup) (hext : 300≤ext.length) (k : Nat) (hk : 131≤k) :
    sqHost ext∉ext.drop k := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp h
  rw [List.getElem_drop,sqHost,List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  omega

theorem host_not_take (ext : List Wire) (hx : ext.Nodup) (hext : 300≤ext.length) :
    sqHost ext∉ext.take 130 := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp h
  rw [List.getElem_take,sqHost,List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  simp at hi
  omega

private theorem mem_drop_mono {l : List Wire} {a b : Nat} {q : Wire} (h : q∈l.drop b) (hab : a≤b) :
    q∈l.drop a := by
  have e : l.drop b=(l.drop a).drop (b-a) := by rw [List.drop_drop]; congr 1; omega
  rw [e] at h
  exact List.mem_of_mem_drop h

/-- After copy/make/erase the body host is zero: for 128-bit sources it is outside every kernel
register; for the 129-bit sum it is bit 130 of `T = 2·lo·hi < 2^130`. -/
theorem prefix_host_zero (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (s : State) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (r1 r2 r3 : List Bool) :
    (run (eraseMask control src (L.inputBank.take src.length)) r3
      (run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2
        (run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s))).basis (sqHost ext)=false := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  have hostE := sqHost_in ext he
  -- erase does not touch the host
  have eraseOff : sqHost ext∉wires (eraseMask control src (L.inputBank.take src.length)) := by
    intro used
    have h := List.mem_toFinset.mp (eraseMask_wires_subset control src (L.inputBank.take src.length) used)
    rcases List.mem_cons.mp h with h|h
    · exact hdx _ hostE (by simp [h])
    · rcases List.mem_append.mp h with h|h
      · exact extSrc _ hostE h
      · exact extB _ hostE h
  rw [run_preserves_outside _ _ _ _ eraseOff]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have mkEq := LowZero18Square.make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  rw [mkEq]
  rw [hKR] at mk
  by_cases h : src.length=128
  · -- the host lies in no kernel register
    have notT : sqHost ext∉(LowZero18LowK.oregs L ext src dst).T := by
      intro m
      have m' : sqHost ext∈(ext.take 132).take 130 := by
        simpa [LowZero18LowK.oregs,h] using m
      rw [List.take_take] at m'
      exact host_not_take ext hx he (by simpa using m')
    have notX : sqHost ext∉(LowZero18LowK.kg L ext src dst).X := by
      intro m
      rw [LowZero18LowK.kg,if_pos h] at m
      simp only [LowZero18LowK.kgH,KG.X,LowZero18LowK.iregs,LowZero18LowK.jregsH,List.mem_append,
        List.not_mem_nil,or_false] at m
      rcases m with ((m|m)|(m|m))
      · exact tmpE _ (List.mem_of_mem_drop (List.mem_of_mem_take m)) hostE
      · exact host_not_drop ext hx he 132 (by omega) (List.mem_of_mem_take m)
      · exact host_not_drop ext hx he 198 (by omega) (List.mem_of_mem_take (List.mem_of_mem_take m))
      · exact host_not_drop ext hx he 232 (by omega) (List.mem_of_mem_take m)
    have notD : sqHost ext∉(LowZero18LowK.oregs L ext src dst).dst := fun m =>
      (dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega) : ∀q∈ext,q∉dst) _ hostE m
    rw [mk.2.2.2.2.2.2.2 _ notD notT notX,u0s _ (extB _ hostE)]
    exact ext0 _ hostE
  · -- the host is bit 130 of T = 2·lo·hi < 2^130
    have h129 : src.length=129 := by omega
    have tv := mk.2.2.2.1
    have lo_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).lo u0.basis
    have hi_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).hi u0.basis
    have lol : (LowZero18LowK.oregs L ext src dst).lo.length=64 := by
      simp [LowZero18LowK.oregs,KRegs.lo,sizes.1,h129]
    have hil : (LowZero18LowK.oregs L ext src dst).hi.length=65 := by
      simp [LowZero18LowK.oregs,KRegs.hi,sizes.1,h129]
    rw [lol] at lo_lt
    rw [hil] at hi_lt
    have prod : 2*regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis*
        regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis<2^130 := by
      have := Nat.mul_lt_mul'' lo_lt hi_lt
      have e : (2:Nat)^130=2*(2^64*2^65) := by norm_num
      rw [e,Nat.mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left this (by norm_num)
    rw [← tv] at prod
    apply top_bits_zero _ _ 130 prod
    have tl : (LowZero18LowK.oregs L ext src dst).T=ext.take 132 := by
      simp [LowZero18LowK.oregs,h129]
    rw [tl,sqHost,List.getD_eq_getElem _ _ (by omega)]
    have : ext[130]'(by omega)=((ext.take 132).drop 130)[0]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _

/-! ## Square: run equality -/

theorem mid_swap (Pre X Post : Program) (a b : Wire) (s : State) (m : List Bool)
    (ua : (run Pre (m.take (measurementCount Pre)) s).basis a=false)
    (ub : (run Pre (m.take (measurementCount Pre)) s).basis b=false)
    (bX : b∉wires X) (aPost : a∉wires Post)
    (fin : (run (Pre++X++Post) m s).basis a=false) :
    run (Pre++renameProgram (Equiv.swap a b) X++Post) m s=run (Pre++X++Post) m s := by
  have mc := (renameProgram_counts (Equiv.swap a b) X).2
  simp only [run_append,measurementCount_append,mc] at fin ⊢
  have e : List.take (measurementCount Pre) (List.take (measurementCount Pre+measurementCount X) m)=
      List.take (measurementCount Pre) m := by rw [List.take_take]; congr 1; omega
  simp only [e] at fin ⊢
  generalize run Pre (List.take (measurementCount Pre) m) s=u at ua ub fin ⊢
  rw [run_preserves_outside Post _ _ a aPost] at fin
  congr 1
  exact swap_run_eq a b X u _ ua ub fin ((run_preserves_outside X _ u b bX).trans ub)

theorem swaps_commute (a b c d : Wire) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (P : Program) :
    renameProgram (Equiv.swap c d) (renameProgram (Equiv.swap a b) P)=
      renameProgram (Equiv.swap a b) (renameProgram (Equiv.swap c d) P) := by
  rw [renameProgram_comp,renameProgram_comp]
  congr 1
  funext x
  simp only [Function.comp,Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem withLowK2_swap_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset)
    (s : State) (m : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0)
    (fin : (run (LowZero18Square.withLowK2 L ext control src dst B) m s).basis (sqRet L)=false) :
    run (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B)) m s=
      run (LowZero18Square.withLowK2 L ext control src dst B) m s := by
  have masks := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have kern := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen he
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have rt := ne _ (target_outer L hw control ext src dst)
  have r0 := ne _ (ext_outer L control ext src dst _ (DiagSq.getD_in ext 0 (by omega)))
  have ht := sqHost_ne_target L hw control ext hdx he
  have h0 := sqHost_ne_ext0 ext hx he
  have com : renameProgram (SquareCarryLoan719.foldPerm L ext) (bodySwap L ext B)=
      renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B) := by
    rw [SquareCarryLoan719.foldPerm_eq L hw,bodySwap,sqSwap]
    exact swaps_commute _ _ _ _ rt r0 ht h0 B
  let Pre := copyRegister (some control) src (L.inputBank.take src.length)++
    LowZero18Square.make L (LowZero18LowK.kg L ext src dst)++eraseMask control src (L.inputBank.take src.length)
  let Post := CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst)
    src (L.inputBank.take src.length)++
    LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)++eraseMask control src (L.inputBank.take src.length)
  have s0 : LowZero18Square.withLowK2 L ext control src dst B=
      Pre++renameProgram (SquareCarryLoan719.foldPerm L ext) B++Post := by
    simp only [LowZero18Square.withLowK2,Pre,Post,List.append_assoc]
  have s1 : LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B)=
      Pre++renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B)++Post := by
    rw [← com]
    simp only [LowZero18Square.withLowK2,Pre,Post,List.append_assoc]
  rw [s0] at fin
  rw [s1,s0]
  have retPre : sqRet L∉wires Pre := by
    simp only [Pre,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨masks.1,kern.1⟩,masks.2⟩
  have cached := sqRet_cached_mask L hw control hn ext src dst hs hd hx hdx (by omega)
  have retPost : sqRet L∉wires Post := by
    simp only [Post,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨cached,kern.2⟩,masks.2⟩
  have retS : s.basis (sqRet L)=false := by
    apply (regValue_zero _ _).mp hc.pad
    exact DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega)
  apply mid_swap _ _ _ _ _ s m ((run_preserves_outside _ _ _ _ retPre).trans retS) _
    (sqHost_fold_free L hw control ext hx hdx he B hb) retPost fin
  simp only [Pre,run_append]
  exact prefix_host_zero L hw control hn src dst hs hd h128 hsmax hlen ext hx hdx he s hc hzero hz _ _ _

theorem run3 (A W C : Program) (s : State) (m : List Bool) :
    run (A++W++C) m s=run C (m.drop (measurementCount A+measurementCount W))
      (run W ((m.drop (measurementCount A)).take (measurementCount W)) (run A (m.take (measurementCount A)) s)) := by
  simp only [run_append,measurementCount_append]
  have e1 : List.take (measurementCount A) (List.take (measurementCount A+measurementCount W) m)=
      List.take (measurementCount A) m := by rw [List.take_take]; congr 1; omega
  have e2 : List.drop (measurementCount A) (List.take (measurementCount A+measurementCount W) m)=
      List.take (measurementCount W) (List.drop (measurementCount A) m) := by
    rw [List.drop_take]; congr 1; omega
  rw [e1,e2]

theorem withLowK2_swap_mc (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (B : Program) :
    measurementCount (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B))=
      measurementCount (LowZero18Square.withLowK2 L ext control src dst B) := by
  simp only [LowZero18Square.withLowK2,bodySwap,measurementCount_append,(renameProgram_counts _ _).2]

section Branches
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire) (control : Wire)
  (hn : (control::L.wires).Nodup)

include hw in
theorem sqRet_not_out (hn' : L.wires.Nodup) : sqRet L∉L.core.out :=
  (L.pairAuxAway hn' (sqRet L) (by
    simp only [List.mem_append]
    exact Or.inl (Or.inl (DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega))))).2

include hw in
theorem sqRet_clean (st : BasisState) (hc : L.PairClean st) : st (sqRet L)=false :=
  (regValue_zero _ _).mp hc.pad _ (DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega))

include hw hn in
theorem branchBF760_run_eq (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) (hsum:s.basis L.core.sumCarry=false)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchBF760 L ext control) records s=run (LowZero18Square.branchBF L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have old := (LowZero18Square.branchBF_correct L hw ext control hn B O hO s records hb ho hp0 hc hsum he hz).2.2
    (sqRet L) (sqRet_not_out L hw nd)
  rw [sqRet_clean L hw _ hc] at old
  exact withLowK2_swap_run_eq L hw control hn L.core.high (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) ext he.nodup he.away he.len _
    (CachedCarryBodyDevelop.hosted_fold_support L hw nd ext control he.len (fun q hq h=>he.away q hq (List.mem_cons_of_mem control h))) s records hc dstZero hz old

include hw hn in
theorem branchAF760_run_eq (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) (hsum:s.basis L.core.sumCarry=false)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchAF760 L ext control) records s=run (LowZero18Square.branchAF L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have old := (LowZero18Square.branchAF_correct L hw ext control hn A O hO s records ha ho hp0 hc hsum he hz).2.2
    (sqRet L) (sqRet_not_out L hw nd)
  rw [sqRet_clean L hw _ hc] at old
  exact withLowK2_swap_run_eq L hw control hn L.core.low (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) ext he.nodup he.away he.len _
    (InverseCarryDevelop.hostedA_fold_support L hw nd ext control he.len (fun q hq h=>he.away q hq (List.mem_cons_of_mem control h))) s records hc dstZero hz old

end Branches

theorem branchCK760_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hsum : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchCK760 L ext control) records s=run (LowZero18Square.branchCK L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  let W := LowZero18Square.withLowK2 L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)
  let W' := LowZero18Square.withLowK2 L ext control L.core.sum L.core.product
    (bodySwap L ext (OwnDiagAll12Square.bodyCKTq L control))
  let mp := measurementCount (OwnDiagAll12Square.gPrep L)
  let u := run (OwnDiagAll12Square.gPrep L) (records.take mp) s
  have prep := OwnDiagAll12Square.gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
    s (records.take mp) (show SquareFrame L.core.sum s.basis B s.basis from ⟨hsum,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have hzU : regValue ext u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => he.away q hq (OwnDiagAll12Square.sum_in L control q bad)))).trans hz
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have gOff : sqRet L∉wires (OwnDiagAll12Square.gClear L) := fun used =>
    sqRet_not_core L hw control hn (List.mem_toFinset.mp ((g_core_support L hw).2 used))
  have old := (LowZero18Square.branchCK_correct L hw ext control hn A B O hO s records ha hsum bound ho hp0 hc he hz).2.2
    (sqRet L) (sqRet_not_out L hw nd)
  rw [sqRet_clean L hw _ hc] at old
  have shapeOld : LowZero18Square.branchCK L ext control=OwnDiagAll12Square.gPrep L++W++OwnDiagAll12Square.gClear L := rfl
  have shapeNew : branchCK760 L ext control=OwnDiagAll12Square.gPrep L++W'++OwnDiagAll12Square.gClear L := rfl
  rw [shapeOld,run3,run_preserves_outside _ _ _ _ gOff] at old
  have mid := withLowK2_swap_run_eq L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len _
    (OwnDiagAll12Square.bodyCK_supportTq L hw nd control) u _ cleanU productU hzU old
  rw [shapeNew,shapeOld,run3,run3,withLowK2_swap_mc]
  exact congrArg _ mid

theorem core760_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (core760 L ext control) records s=run (ReflectionE1Low48Square.core L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have keepAll (t : State) (hf : ∀q,q∉L.core.out → t.basis q=s.basis q) :
      regValue L.core.low t.basis=A ∧ regValue L.core.high t.basis=B ∧
      regValue L.core.product t.basis=0 ∧ regValue ext t.basis=0 ∧ L.PairClean t.basis := by
    refine ⟨regValue_congr _ _ _ (fun q hq => hf q (lowAway q hq)),
      regValue_congr _ _ _ (fun q hq => hf q (highAway q hq)),
      (regValue_congr _ _ _ (fun q hq => hf q (List.disjoint_left.mp disProduct hq))).trans hp0,
      (regValue_congr _ _ _ (fun q hq => hf q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz,
      L.squareFrame_clean nd s.basis t.basis _ ⟨rfl,hf⟩ hc⟩
  let CK := LowZero18Square.branchCK L ext control
  let BF := LowZero18Square.branchBF L ext control
  let AF := LowZero18Square.branchAF L ext control
  have mcC : measurementCount (branchCK760 L ext control)=measurementCount CK := by
    simp only [branchCK760,CK,LowZero18Square.branchCK,measurementCount_append,withLowK2_swap_mc]
  have mcB : measurementCount (branchBF760 L ext control)=measurementCount BF := withLowK2_swap_mc _ _ _ _ _ _
  have e0 : core760 L ext control=branchCK760 L ext control++branchBF760 L ext control++branchAF760 L ext control := rfl
  have e1 : ReflectionE1Low48Square.core L ext control=CK++BF++AF := rfl
  rw [e0,e1,run3,run3,mcC,mcB]
  have eqC := branchCK760_run_eq L hw ext control hn A B O hO s (records.take (measurementCount CK)) rfl sumB
    sumBound ho hp0 hc he hz
  rw [eqC]
  have rC := LowZero18Square.branchCK_correct L hw ext control hn A B O hO s (records.take (measurementCount CK))
    rfl sumB sumBound ho hp0 hc he hz
  generalize run CK (records.take (measurementCount CK)) s=t1 at rC ⊢
  have k1 := keepAll t1 rC.2.2
  have hO1 : regValue L.core.out t1.basis<SquareReduction.p := by rw [rC.2.1]; exact ofCast_lt _ _
  have eqB := branchBF760_run_eq L hw ext control hn B _ hO1 t1
    ((records.drop (measurementCount CK)).take (measurementCount BF)) k1.2.1 rfl k1.2.2.1 k1.2.2.2.2 ((rC.2.2 _ (ParkCarryDevelop.sumCarry_off_regs L nd).1).trans hs0) he k1.2.2.2.1
  rw [eqB]
  have rB := LowZero18Square.branchBF_correct L hw ext control hn B _ hO1 t1
    ((records.drop (measurementCount CK)).take (measurementCount BF)) k1.2.1 rfl k1.2.2.1 k1.2.2.2.2 ((rC.2.2 _ (ParkCarryDevelop.sumCarry_off_regs L nd).1).trans hs0) he k1.2.2.2.1
  generalize run BF ((records.drop (measurementCount CK)).take (measurementCount BF)) t1=t2 at rB ⊢
  have k2 := keepAll t2 (fun q hq => (rB.2.2 q hq).trans (rC.2.2 q hq))
  have hO2 : regValue L.core.out t2.basis<SquareReduction.p := by rw [rB.2.1]; exact ofCast_lt _ _
  exact branchAF760_run_eq L hw ext control hn A _ hO2 t2 _ k2.1 rfl k2.2.2.1 k2.2.2.2.2 (((rB.2.2 _ (ParkCarryDevelop.sumCarry_off_regs L nd).1).trans (rC.2.2 _ (ParkCarryDevelop.sumCarry_off_regs L nd).1)).trans hs0) he k2.2.2.2.1

section Final
open Secp256k1 CompressedPointDialog

theorem fastCore760_run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (hX : X<p)
    (s : State) (m : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    run (fastCore760 L) m s=run (ReflectionE1Low48Square.fastCore L) m s := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (OwnDiagAll12Square.kext_mem L hw q hq))
  have extOK:=OwnDiagAll12Square.kext_ok L hw hn
  have hext : ECDSAAdd.Entrant.ExtOK K L.core.generic (OwnDiagAll12Square.kext L) :=
    ⟨extOK.nodup,extOK.away,extOK.len⟩
  exact core760_run_eq K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean hext hz

private theorem pool_away_x' (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have dis:=(List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  intro hx
  have resident : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis resident hq

/-- **R2 square deliverable**: same hypotheses as `ReflectionE1Low48Square.boundary`. -/
theorem program760_run_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program760 L) m s=run (ReflectionE1Low48Square.program L) m s := by
  have core := fastCore760_run_eq L hw hn X.val Y.val X.isLt s m v.x v.y v.clean
  have result := ReflectionE1Low48Square.fastCore_boundary L hw hn X Y G origin s m v
  have clean : regValue L.dialogPool (run (ReflectionE1Low48Square.fastCore L) m s).basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x' L hn q hq)),v.clean]
  have eNew := ReflectionE1Square.place_run_eq L hw (fastCore760 L) s m v.clean (by rw [core]; exact clean)
  have eOld := ReflectionE1Square.place_run_eq L hw (ReflectionE1Low48Square.fastCore L) s m v.clean clean
  change run (program760 L) m s=run (fastCore760 L) m s at eNew
  change run (ReflectionE1Low48Square.program L) m s=run (ReflectionE1Low48Square.fastCore L) m s at eOld
  rw [eNew,eOld,core]

/-- The new square satisfies the old square's boundary verbatim. -/
theorem program760_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (program760 L) m s).phase=s.phase ∧
    regValue L.point.x (run (program760 L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (program760 L) m s).basis q=s.basis q := by
  rw [program760_run_eq L hw hn X Y G origin s m v]
  exact ReflectionE1Low48Square.boundary L hw hn X Y G origin s m v

end Final

end ECDSAAdd.Entrant.R2SqEp760

end -- R2 square

-- ===== Exit-side merged tick (ExitMerge) in the multiplication kernel =====
section

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed
section -- Scope the inlined inverse proof attributes

-- Verified Inverse14Physical
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ECDSAAdd.Entrant.Inverse14Width
open Arithmetic MappedCompressed Secp256k1 History5
def sites : List Wire := MorningFour.sites ++ [530]
def block0 : Program := [
 .X 527,
 .CX 526 527,
 .CX 526 786,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CCX 522 523 527,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 526 1551
]
def block1 : Program := [
 .CX 1551 526,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 524,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 524 526,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 528,
 .CX 522 524,
 .CX 524 522
]
def block2 : Program := [
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 526,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 525 524,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 524,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526
]
def block3 : Program := [
 .CX 524 526,
 .CX 524 523,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 523 522,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 522 524,
 .CCX 522 523 529,
 .CX 522 524,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 523 522,
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 523,
 .CX 524 526,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 525 524,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551
]
def block4 : Program := [
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 528 1552,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1552 1553,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1551 524,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 786
]
def block5 : Program := [
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 1551 524,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1552 1553,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 528 1552,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552
]
def block6 : Program := [
 .CX 526 525,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 1551,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 787,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 525 1551,
 .CX 526 1551
]
def block7 : Program := [
 .CX 1551 526,
 .CX 526 1551,
 .CX 526 525,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 787 786,
 .CX 786 787,
 .CX 786 529,
 .CX 529 786,
 .CX 529 527,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 527 528,
 .CX 527 1553,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1551 525,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 526,
 .CX 525 524
]
def block8 : Program := [
 .CX 525 523,
 .CX 523 525,
 .CX 523 524,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 788,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CX 523 524,
 .CX 523 525,
 .CX 525 523,
 .CX 525 524,
 .CX 525 526,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 1551 525,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 527 1553,
 .CX 527 528,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529
]
def block9 : Program := [
 .CX 529 527,
 .CX 529 786,
 .CX 786 529,
 .CX 786 787,
 .CX 787 786,
 .CX 787 528,
 .CX 786 788,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 529 787,
 .CX 787 529,
 .CX 529 787,
 .CX 528 786,
 .CX 528 1553,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 527 529,
 .CX 529 527,
 .CX 527 529,
 .CX 1554 528,
 .CX 528 1554,
 .CX 1554 528,
 .CX 1553 527,
 .CX 1553 525,
 .CX 1552 1554,
 .CX 1554 1552,
 .CX 1552 1554,
 .CX 1551 1553,
 .CX 1553 1551,
 .CX 1551 1553
]
def block10 : Program := [
 .CX 526 1552,
 .CX 1552 526,
 .CX 526 1552,
 .CX 525 1551,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 526,
 .CX 526 523,
 .CX 523 526,
 .CX 522 525,
 .CX 525 522,
 .CX 522 525,
 .CCX 522 523 524,
 .CX 787 529,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 529 786,
 .CX 529 528,
 .CX 528 529,
 .CX 528 527,
 .CX 527 528,
 .CX 527 526,
 .CX 527 525,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1553 1554
]
def block11 : Program := [
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 526 525,
 .CX 526 524,
 .CX 525 1551,
 .CX 525 526,
 .CX 525 524,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 789,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 525
]
def block12 : Program := [
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 525 524,
 .CX 525 526,
 .CX 525 1551,
 .CX 526 524,
 .CX 526 525,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 527 525,
 .CX 527 526,
 .CX 527 528,
 .CX 528 527,
 .CX 528 529,
 .CX 529 528,
 .CX 529 786,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 787 529
]
def block13 : Program := [
 .CX 787 529,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 529 786,
 .CX 529 1554,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 1554 527,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 526,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 526 524,
 .CX 525 522,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525
]
def block14 : Program := [
 .CX 522 524,
 .CCX 522 523 790,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 525 522,
 .CX 526 524,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1553 526,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1554 527,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 529 1554,
 .CX 529 786,
 .CX 786 787
]
def block15 : Program := [
 .CX 787 786,
 .CX 786 787,
 .CX 787 529,
 .CX 790 787,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 788 789,
 .CX 789 788,
 .CX 788 789,
 .CX 787 788,
 .CX 787 528,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 528 529,
 .CX 528 527,
 .CX 527 528,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 1551,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1551 526,
 .CX 1551 525
]
def block16 : Program := [
 .CX 525 1551,
 .CX 525 526,
 .CX 525 523,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 525,
 .CX 523 522,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 522 524,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CCX 522 523 791,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CX 522 524,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 523 522,
 .CX 523 525,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 525 523,
 .CX 525 526,
 .CX 525 1551,
 .CX 1551 525
]
def block17 : Program := [
 .CX 1551 526,
 .CX 1551 1552,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1553 1551,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1554 527,
 .CX 527 1554,
 .CX 527 528,
 .CX 528 527,
 .CX 528 529,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 787 528,
 .CX 787 788,
 .CX 788 789,
 .CX 789 788,
 .CX 788 789,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 790 787,
 .CX 788 786,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788
]
def block18 : Program := [
 .CX 786 787,
 .CX 786 527,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 527 528,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1554 1552,
 .CX 1554 1551,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1552 526,
 .CX 1551 1553,
 .CX 1551 522,
 .CX 526 1552,
 .CX 526 1551,
 .CX 526 524,
 .CX 526 522,
 .CX 525 1551,
 .CX 1551 525,
 .CX 525 1551,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523
]
def block19 : Program := [
 .CX 523 525,
 .CX 522 524,
 .CX 522 523,
 .CCX 522 523 1556,
 .CX 522 523,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 525 1551,
 .CX 1551 525,
 .CX 525 1551,
 .CX 526 522,
 .CX 526 524,
 .CX 526 1551,
 .CX 526 1552,
 .CX 1551 522,
 .CX 1551 1553,
 .CX 1552 526,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1554 1551,
 .CX 1554 1552,
 .CX 1554 527,
 .CX 527 1554,
 .CX 527 528,
 .CX 528 529
]
def block20 : Program := [
 .CX 529 528,
 .CX 528 529,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 786 527,
 .CX 786 787,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 788 786,
 .CX 1556 788,
 .CX 791 1556,
 .CX 1556 791,
 .CX 791 1556,
 .CX 790 791,
 .CX 791 790,
 .CX 790 791,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 788 789,
 .CX 788 786,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 786 787,
 .CX 786 527,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 528 529
]
def block21 : Program := [
 .CX 529 528,
 .CX 528 529,
 .CX 527 528,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1554 1552,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1552 1553,
 .CX 1552 526,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 526 524,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 1557,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523
]
def block22 : Program := [
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 526 524,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1552 526,
 .CX 1552 1553,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1554 1552,
 .CX 1554 527,
 .CX 527 1554,
 .CX 527 528,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 786 527,
 .CX 786 787,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 788 786,
 .CX 788 789
]
def block23 : Program := [
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 790 791,
 .CX 791 790,
 .CX 790 791,
 .CX 791 1556,
 .CX 1556 791,
 .CX 791 1556,
 .CX 1556 788,
 .CX 786 1554,
 .CX 786 1552,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 1554 1553,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1553 527,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1553 1551,
 .CX 1552 1554,
 .CX 1552 524,
 .CX 1551 1553
]
def block24 : Program := [
 .CX 1551 1552,
 .CX 1551 524,
 .CX 1551 523,
 .CX 526 1552,
 .CX 1552 526,
 .CX 526 1552,
 .CX 525 1551,
 .CX 1551 525,
 .CX 525 1551,
 .CX 524 526,
 .CX 524 522,
 .CX 523 525,
 .CX 522 524,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CCX 522 523 1558,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CX 522 524,
 .CX 523 525,
 .CX 524 522,
 .CX 524 526,
 .CX 525 1551,
 .CX 1551 525,
 .CX 525 1551,
 .CX 526 1552,
 .CX 1552 526,
 .CX 526 1552,
 .CX 1551 523,
 .CX 1551 524
]
def block25 : Program := [
 .CX 1551 1552,
 .CX 1551 1553,
 .CX 1552 524,
 .CX 1552 1554,
 .CX 1553 1551,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1553 527,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1554 1553,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 786 1552,
 .CX 786 1554,
 .CX 1558 788,
 .CX 1557 1558,
 .CX 1558 1557,
 .CX 1557 1558,
 .CX 1556 1557,
 .CX 1557 1556,
 .CX 1556 1557,
 .CX 791 1556,
 .CX 1556 791
]
def block26 : Program := [
 .CX 791 1556,
 .CX 790 791,
 .CX 791 790,
 .CX 790 791,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 788 789,
 .CX 788 787,
 .CX 787 788,
 .CX 787 529,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 529 786,
 .CX 529 528,
 .CX 528 529,
 .CX 528 527,
 .CX 527 528,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1554 1551,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1551 522,
 .CX 526 525,
 .CX 526 1551
]
def block27 : Program := [
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 1551,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CCX 522 523 530,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 525 1551,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 526 525,
 .CX 1551 522,
 .CX 1551 1552,
 .CX 1552 1553
]
def block28 : Program := [
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1554 1551,
 .CX 1554 527,
 .CX 527 1554,
 .CX 527 528,
 .CX 528 527,
 .CX 528 529,
 .CX 529 528,
 .CX 529 786,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 787 529,
 .CX 787 788,
 .CX 788 787,
 .CX 788 789,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 790 791,
 .CX 791 790,
 .CX 790 791,
 .CX 791 1556,
 .CX 1556 791,
 .CX 791 1556,
 .CX 1556 1557,
 .CX 1557 1556,
 .CX 1556 1557
]
def block29 : Program := [
 .CX 1557 1558,
 .CX 1558 1557,
 .CX 1557 1558,
 .CX 1558 788,
 .CX 530 1558,
 .CX 530 1556,
 .CX 530 788,
 .CX 1558 1556,
 .CX 1558 1554,
 .CX 1558 1553,
 .CX 1558 530,
 .CX 530 1558,
 .CX 1558 530,
 .CX 1557 1556,
 .CX 1557 791,
 .CX 1557 790,
 .CX 1557 787,
 .CX 1557 528,
 .CX 1557 1558,
 .CX 1558 1557,
 .CX 1557 1558,
 .CX 1556 530,
 .CX 1556 788,
 .CX 1556 527,
 .CX 1556 1553,
 .CX 1556 524,
 .CX 1556 1558,
 .CX 1558 1556,
 .CX 1556 1558,
 .CX 791 530,
 .CX 791 790,
 .CX 791 787
]
def block30 : Program := [
 .CX 791 528,
 .CX 791 1553,
 .CX 790 530,
 .CX 790 1558,
 .CX 790 527,
 .CX 790 1553,
 .CX 790 1551,
 .CX 790 524,
 .CX 790 1556,
 .CX 1556 790,
 .CX 790 1556,
 .CX 789 530,
 .CX 789 1558,
 .CX 789 1557,
 .CX 789 527,
 .CX 789 1553,
 .CX 789 524,
 .CX 789 522,
 .CX 789 1556,
 .CX 1556 789,
 .CX 789 1556,
 .CX 788 530,
 .CX 788 1558,
 .CX 788 786,
 .CX 788 527,
 .CX 788 1553,
 .CX 788 524,
 .CX 788 1557,
 .CX 1557 788,
 .CX 788 1557,
 .CX 787 530,
 .CX 787 528
]
def block31 : Program := [
 .CX 787 1553,
 .CX 787 523,
 .CX 787 791,
 .CX 791 787,
 .CX 787 791,
 .CX 786 1557,
 .CX 786 528,
 .CX 786 527,
 .CX 786 1556,
 .CX 1556 786,
 .CX 786 1556,
 .CX 529 1556,
 .CX 529 527,
 .CX 529 790,
 .CX 790 529,
 .CX 529 790,
 .CX 528 530,
 .CX 528 1556,
 .CX 528 527,
 .CX 528 1554,
 .CX 528 1553,
 .CX 528 790,
 .CX 790 528,
 .CX 528 790,
 .CX 527 1558,
 .CX 527 1554,
 .CX 527 1552,
 .CX 527 524,
 .CX 527 790,
 .CX 790 527,
 .CX 527 790,
 .CX 1554 530
]
def block32 : Program := [
 .CX 1554 1558,
 .CX 1554 1556,
 .CX 1554 791,
 .CX 1554 790,
 .CX 1554 786,
 .CX 1554 1553,
 .CX 1554 1552,
 .CX 1554 526,
 .CX 1554 524,
 .CX 1554 523,
 .CX 1554 522,
 .CX 1553 530,
 .CX 1553 787,
 .CX 1553 529,
 .CX 1553 528,
 .CX 528 1553,
 .CX 1553 528,
 .CX 1552 1558,
 .CX 1552 1556,
 .CX 1552 791,
 .CX 1552 790,
 .CX 1552 524,
 .CX 1552 523,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 789,
 .CX 1551 788,
 .CX 1551 786,
 .CX 1551 528,
 .CX 1551 1553,
 .CX 1551 526
]
def block33 : Program := [
 .CX 1551 525,
 .CX 1551 522,
 .CX 526 786,
 .CX 526 527,
 .CX 526 1554,
 .CX 526 1553,
 .CX 526 522,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 1558,
 .CX 525 1556,
 .CX 525 791,
 .CX 525 788,
 .CX 525 528,
 .CX 525 1554,
 .CX 525 1553,
 .CX 525 526,
 .CX 525 524,
 .CX 525 523,
 .CX 524 1558,
 .CX 524 1556,
 .CX 524 791,
 .CX 524 788,
 .CX 524 527,
 .CX 524 1553,
 .CX 524 1551,
 .CX 524 523,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 791
]
def block34 : Program := [
 .CX 523 787,
 .CX 523 1554,
 .CX 1554 523,
 .CX 523 1554,
 .CX 522 786,
 .CX 522 1553,
 .CX 522 526,
 .CX 522 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .X 1551,
 .X 1553,
 .X 1554,
 .X 527,
 .measureX 530 [] [.Z 526, .Z 1553, .Z 527, .Z 786, .Z 788, .Z 790, .Z 791, .CZ 522 786, .CZ 522 787, .CZ 522 1558, .CZ 523 524, .CZ 523 525, .CZ 523 526, .CZ 523 1554, .CZ 523 789, .CZ 523 790, .CZ 523 1558, .CZ 524 786, .CZ 524 789, .CZ 1553 528, .CZ 1553 791, .CZ 1553 1558],
 .measureX 1558 [] [.Z 526, .Z 1551, .Z 1552, .Z 1553, .Z 1554, .Z 527, .Z 529, .Z 788, .Z 790, .Z 791, .Z 1556, .CZ 522 524, .CZ 522 1553, .CZ 522 1554, .CZ 522 791, .CZ 522 1556, .CZ 523 1554, .CZ 523 789, .CZ 523 1556, .CZ 524 525, .CZ 524 1553, .CZ 524 527, .CZ 524 528, .CZ 524 529, .CZ 524 786, .CZ 524 787, .CZ 524 789, .CZ 524 790, .CZ 524 791, .CZ 524 1556, .CZ 524 1557, .CZ 525 526, .CZ 525 1551, .CZ 525 786, .CZ 525 788, .CZ 525 1556, .CZ 526 528, .CZ 526 1556, .CZ 1551 1553, .CZ 1553 1554, .CZ 1553 528, .CZ 1553 791, .CZ 1553 1556, .CZ 1554 1556],
 .X 1557,
 .measureX 1557 [] [.Z 522, .Z 523, .Z 525, .Z 1551, .Z 1552, .Z 786, .Z 788, .Z 789, .Z 790, .CZ 522 523, .CZ 522 524, .CZ 522 526, .CZ 522 1554, .CZ 522 786, .CZ 522 788, .CZ 523 524, .CZ 523 526, .CZ 523 789, .CZ 523 790, .CZ 524 525, .CZ 524 526, .CZ 524 528, .CZ 524 529, .CZ 524 787, .CZ 524 789, .CZ 524 790, .CZ 525 526, .CZ 525 1553, .CZ 525 1554, .CZ 525 528, .CZ 525 786, .CZ 525 787, .CZ 525 788, .CZ 526 790, .CZ 1551 1553, .CZ 1551 1554, .CZ 1551 788],
 .X 1556,
 .measureX 1556 [] [.Z 523, .Z 526, .Z 1553, .Z 527, .Z 529, .Z 790, .CZ 522 523, .CZ 522 526, .CZ 522 1553, .CZ 522 527, .CZ 522 786, .CZ 522 787, .CZ 522 789, .CZ 522 790, .CZ 523 525, .CZ 523 1551, .CZ 523 1554, .CZ 523 790, .CZ 524 1553, .CZ 524 1554, .CZ 524 529, .CZ 524 789, .CZ 524 790, .CZ 525 1554, .CZ 525 527, .CZ 525 528, .CZ 525 790, .CZ 526 1553, .CZ 526 527, .CZ 526 528, .CZ 526 786, .CZ 526 788, .CZ 526 790, .CZ 1551 788, .CZ 1553 527, .CZ 1553 528, .CZ 1553 788],
 .measureX 791 [] [.Z 522, .Z 524, .Z 525, .Z 526, .Z 1553, .Z 1554, .Z 786, .Z 789, .Z 790, .CZ 522 524, .CZ 522 1553, .CZ 522 786, .CZ 522 787, .CZ 522 789, .CZ 523 524, .CZ 523 525, .CZ 523 526, .CZ 523 1551, .CZ 523 789, .CZ 523 790, .CZ 524 528, .CZ 524 529, .CZ 524 786, .CZ 525 528, .CZ 525 789],
 .X 790,
 .measureX 790 [] [.Z 522, .Z 525, .Z 1551, .Z 527, .Z 786, .Z 788, .CZ 522 524, .CZ 522 1554, .CZ 522 788, .CZ 523 525, .CZ 523 526, .CZ 523 1551, .CZ 524 1554, .CZ 524 528, .CZ 524 786, .CZ 524 788, .CZ 525 1551, .CZ 525 527, .CZ 525 528, .CZ 525 786, .CZ 525 787, .CZ 525 788, .CZ 526 1553, .CZ 526 527, .CZ 526 786, .CZ 526 788, .CZ 1551 1553, .CZ 1551 1554, .CZ 1551 786, .CZ 1551 788, .CZ 1553 1554, .CZ 1553 528, .CZ 1554 528],
 .measureX 789 [] [.Z 524, .Z 525, .Z 1553, .Z 786, .CZ 522 525, .CZ 522 1554, .CZ 524 525, .CZ 524 1551, .CZ 524 1553, .CZ 524 787, .CZ 525 786, .CZ 1553 1554, .CZ 1553 528, .CZ 1553 787, .CZ 1554 786],
 .measureX 788 [] [.Z 522, .Z 523, .Z 524, .Z 526, .CZ 523 524, .CZ 523 526, .CZ 523 1553, .CZ 523 527],
 .X 787,
 .measureX 787 [] [.Z 1554, .Z 528, .CZ 523 525, .CZ 523 1551, .CZ 523 1554, .CZ 523 528],
 .measureX 786 [] [.Z 522, .Z 523, .Z 524, .CZ 523 524, .CZ 523 1553],
 .CX 1551 527,
 .CX 527 1551,
 .CX 1551 527
]
def block35 : Program := [
 .CX 1552 528,
 .CX 528 1552,
 .CX 1552 528,
 .CX 1553 787,
 .CX 787 1553,
 .CX 1553 787,
 .CX 1554 788,
 .CX 788 1554,
 .CX 1554 788,
 .CX 1551 789,
 .CX 789 1551,
 .CX 1551 789,
 .CX 1552 790,
 .CX 790 1552,
 .CX 1552 790,
 .CX 529 791,
 .CX 791 529,
 .CX 529 791,
 .X 786,
 .CX 523 786,
 .measureX 530 [] []
]
def candidate : Program := block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20 ++ block21 ++ block22 ++ block23 ++ block24 ++ block25 ++ block26 ++ block27 ++ block28 ++ block29 ++ block30 ++ block31 ++ block32 ++ block33 ++ block34 ++ block35
theorem counts0 : toffoliCount block0=1 ∧ measurementCount block0=0 ∧ Challenge.gateSlots block0=32 := by decide +kernel
theorem support0 : wires block0⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical0 : GatePhysical block0 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts1 : toffoliCount block1=1 ∧ measurementCount block1=0 ∧ Challenge.gateSlots block1=32 := by decide +kernel
theorem support1 : wires block1⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical1 : GatePhysical block1 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts2 : toffoliCount block2=0 ∧ measurementCount block2=0 ∧ Challenge.gateSlots block2=32 := by decide +kernel
theorem support2 : wires block2⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical2 : GatePhysical block2 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts3 : toffoliCount block3=1 ∧ measurementCount block3=0 ∧ Challenge.gateSlots block3=32 := by decide +kernel
theorem support3 : wires block3⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical3 : GatePhysical block3 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts4 : toffoliCount block4=1 ∧ measurementCount block4=0 ∧ Challenge.gateSlots block4=32 := by decide +kernel
theorem support4 : wires block4⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical4 : GatePhysical block4 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts5 : toffoliCount block5=0 ∧ measurementCount block5=0 ∧ Challenge.gateSlots block5=32 := by decide +kernel
theorem support5 : wires block5⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical5 : GatePhysical block5 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts6 : toffoliCount block6=1 ∧ measurementCount block6=0 ∧ Challenge.gateSlots block6=32 := by decide +kernel
theorem support6 : wires block6⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical6 : GatePhysical block6 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts7 : toffoliCount block7=0 ∧ measurementCount block7=0 ∧ Challenge.gateSlots block7=32 := by decide +kernel
theorem support7 : wires block7⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical7 : GatePhysical block7 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts8 : toffoliCount block8=1 ∧ measurementCount block8=0 ∧ Challenge.gateSlots block8=32 := by decide +kernel
theorem support8 : wires block8⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical8 : GatePhysical block8 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts9 : toffoliCount block9=0 ∧ measurementCount block9=0 ∧ Challenge.gateSlots block9=32 := by decide +kernel
theorem support9 : wires block9⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical9 : GatePhysical block9 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts10 : toffoliCount block10=1 ∧ measurementCount block10=0 ∧ Challenge.gateSlots block10=32 := by decide +kernel
theorem support10 : wires block10⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical10 : GatePhysical block10 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts11 : toffoliCount block11=1 ∧ measurementCount block11=0 ∧ Challenge.gateSlots block11=32 := by decide +kernel
theorem support11 : wires block11⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical11 : GatePhysical block11 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts12 : toffoliCount block12=0 ∧ measurementCount block12=0 ∧ Challenge.gateSlots block12=32 := by decide +kernel
theorem support12 : wires block12⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical12 : GatePhysical block12 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts13 : toffoliCount block13=0 ∧ measurementCount block13=0 ∧ Challenge.gateSlots block13=32 := by decide +kernel
theorem support13 : wires block13⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical13 : GatePhysical block13 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts14 : toffoliCount block14=1 ∧ measurementCount block14=0 ∧ Challenge.gateSlots block14=32 := by decide +kernel
theorem support14 : wires block14⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical14 : GatePhysical block14 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts15 : toffoliCount block15=0 ∧ measurementCount block15=0 ∧ Challenge.gateSlots block15=32 := by decide +kernel
theorem support15 : wires block15⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical15 : GatePhysical block15 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts16 : toffoliCount block16=1 ∧ measurementCount block16=0 ∧ Challenge.gateSlots block16=32 := by decide +kernel
theorem support16 : wires block16⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical16 : GatePhysical block16 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts17 : toffoliCount block17=0 ∧ measurementCount block17=0 ∧ Challenge.gateSlots block17=32 := by decide +kernel
theorem support17 : wires block17⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical17 : GatePhysical block17 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts18 : toffoliCount block18=0 ∧ measurementCount block18=0 ∧ Challenge.gateSlots block18=32 := by decide +kernel
theorem support18 : wires block18⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical18 : GatePhysical block18 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts19 : toffoliCount block19=1 ∧ measurementCount block19=0 ∧ Challenge.gateSlots block19=32 := by decide +kernel
theorem support19 : wires block19⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical19 : GatePhysical block19 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts20 : toffoliCount block20=0 ∧ measurementCount block20=0 ∧ Challenge.gateSlots block20=32 := by decide +kernel
theorem support20 : wires block20⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical20 : GatePhysical block20 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts21 : toffoliCount block21=1 ∧ measurementCount block21=0 ∧ Challenge.gateSlots block21=32 := by decide +kernel
theorem support21 : wires block21⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical21 : GatePhysical block21 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts22 : toffoliCount block22=0 ∧ measurementCount block22=0 ∧ Challenge.gateSlots block22=32 := by decide +kernel
theorem support22 : wires block22⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical22 : GatePhysical block22 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts23 : toffoliCount block23=0 ∧ measurementCount block23=0 ∧ Challenge.gateSlots block23=32 := by decide +kernel
theorem support23 : wires block23⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical23 : GatePhysical block23 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts24 : toffoliCount block24=1 ∧ measurementCount block24=0 ∧ Challenge.gateSlots block24=32 := by decide +kernel
theorem support24 : wires block24⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical24 : GatePhysical block24 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts25 : toffoliCount block25=0 ∧ measurementCount block25=0 ∧ Challenge.gateSlots block25=32 := by decide +kernel
theorem support25 : wires block25⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical25 : GatePhysical block25 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts26 : toffoliCount block26=0 ∧ measurementCount block26=0 ∧ Challenge.gateSlots block26=32 := by decide +kernel
theorem support26 : wires block26⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical26 : GatePhysical block26 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts27 : toffoliCount block27=1 ∧ measurementCount block27=0 ∧ Challenge.gateSlots block27=32 := by decide +kernel
theorem support27 : wires block27⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical27 : GatePhysical block27 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts28 : toffoliCount block28=0 ∧ measurementCount block28=0 ∧ Challenge.gateSlots block28=32 := by decide +kernel
theorem support28 : wires block28⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical28 : GatePhysical block28 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts29 : toffoliCount block29=0 ∧ measurementCount block29=0 ∧ Challenge.gateSlots block29=32 := by decide +kernel
theorem support29 : wires block29⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical29 : GatePhysical block29 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts30 : toffoliCount block30=0 ∧ measurementCount block30=0 ∧ Challenge.gateSlots block30=32 := by decide +kernel
theorem support30 : wires block30⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical30 : GatePhysical block30 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts31 : toffoliCount block31=0 ∧ measurementCount block31=0 ∧ Challenge.gateSlots block31=32 := by decide +kernel
theorem support31 : wires block31⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical31 : GatePhysical block31 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts32 : toffoliCount block32=0 ∧ measurementCount block32=0 ∧ Challenge.gateSlots block32=32 := by decide +kernel
theorem support32 : wires block32⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical32 : GatePhysical block32 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts33 : toffoliCount block33=0 ∧ measurementCount block33=0 ∧ Challenge.gateSlots block33=32 := by decide +kernel
theorem support33 : wires block33⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical33 : GatePhysical block33 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts34 : toffoliCount block34=0 ∧ measurementCount block34=10 ∧ Challenge.gateSlots block34=264 := by decide +kernel
theorem support34 : wires block34⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical34 : GatePhysical block34 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts35 : toffoliCount block35=0 ∧ measurementCount block35=1 ∧ Challenge.gateSlots block35=21 := by decide +kernel
theorem support35 : wires block35⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical35 : GatePhysical block35 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem resources : toffoliCount candidate=14 ∧ measurementCount candidate=11 ∧ Challenge.gateSlots candidate=1373 := by
 simp only [candidate,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,counts0.1,counts0.2.1,counts0.2.2,counts1.1,counts1.2.1,counts1.2.2,counts2.1,counts2.2.1,counts2.2.2,counts3.1,counts3.2.1,counts3.2.2,counts4.1,counts4.2.1,counts4.2.2,counts5.1,counts5.2.1,counts5.2.2,counts6.1,counts6.2.1,counts6.2.2,counts7.1,counts7.2.1,counts7.2.2,counts8.1,counts8.2.1,counts8.2.2,counts9.1,counts9.2.1,counts9.2.2,counts10.1,counts10.2.1,counts10.2.2,counts11.1,counts11.2.1,counts11.2.2,counts12.1,counts12.2.1,counts12.2.2,counts13.1,counts13.2.1,counts13.2.2,counts14.1,counts14.2.1,counts14.2.2,counts15.1,counts15.2.1,counts15.2.2,counts16.1,counts16.2.1,counts16.2.2,counts17.1,counts17.2.1,counts17.2.2,counts18.1,counts18.2.1,counts18.2.2,counts19.1,counts19.2.1,counts19.2.2,counts20.1,counts20.2.1,counts20.2.2,counts21.1,counts21.2.1,counts21.2.2,counts22.1,counts22.2.1,counts22.2.2,counts23.1,counts23.2.1,counts23.2.2,counts24.1,counts24.2.1,counts24.2.2,counts25.1,counts25.2.1,counts25.2.2,counts26.1,counts26.2.1,counts26.2.2,counts27.1,counts27.2.1,counts27.2.2,counts28.1,counts28.2.1,counts28.2.2,counts29.1,counts29.2.1,counts29.2.2,counts30.1,counts30.2.1,counts30.2.2,counts31.1,counts31.2.1,counts31.2.2,counts32.1,counts32.2.1,counts32.2.2,counts33.1,counts33.2.1,counts33.2.2,counts34.1,counts34.2.1,counts34.2.2,counts35.1,counts35.2.1,counts35.2.2]
 decide +kernel
theorem support_live : wires candidate⊆sites.toFinset.erase 1559 := by
 simp only [candidate,wires_append,Finset.union_subset_iff]
 exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨support0,support1⟩,support2⟩,support3⟩,support4⟩,support5⟩,support6⟩,support7⟩,support8⟩,support9⟩,support10⟩,support11⟩,support12⟩,support13⟩,support14⟩,support15⟩,support16⟩,support17⟩,support18⟩,support19⟩,support20⟩,support21⟩,support22⟩,support23⟩,support24⟩,support25⟩,support26⟩,support27⟩,support28⟩,support29⟩,support30⟩,support31⟩,support32⟩,support33⟩,support34⟩,support35⟩
theorem physical : GatePhysical candidate := by
 simp only [candidate,gatePhysical_append]
 exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨physical0,physical1⟩,physical2⟩,physical3⟩,physical4⟩,physical5⟩,physical6⟩,physical7⟩,physical8⟩,physical9⟩,physical10⟩,physical11⟩,physical12⟩,physical13⟩,physical14⟩,physical15⟩,physical16⟩,physical17⟩,physical18⟩,physical19⟩,physical20⟩,physical21⟩,physical22⟩,physical23⟩,physical24⟩,physical25⟩,physical26⟩,physical27⟩,physical28⟩,physical29⟩,physical30⟩,physical31⟩,physical32⟩,physical33⟩,physical34⟩,physical35⟩
theorem support : wires candidate⊆sites.toFinset := support_live.trans (Finset.erase_subset _ _)
theorem checked_run (P : Program) (b c : Nat) (h : phaseClean508 P b=some c) (m : List Bool) :
 run P m ⟨false,tbN_t8 b⟩=⟨false,tbN_t8 c⟩ := by
 rw [run_sim_t8,phaseClean508_sound P b c h m]
theorem sequence (P Q : Program) (b c d : Nat)
 (hp : ∀m,run P m ⟨false,tbN_t8 b⟩=⟨false,tbN_t8 c⟩)
 (hq : ∀m,run Q m ⟨false,tbN_t8 c⟩=⟨false,tbN_t8 d⟩) :
 ∀m,run (P++Q) m ⟨false,tbN_t8 b⟩=⟨false,tbN_t8 d⟩ := by
 intro m
 rw [run_append,hp,hq]
end ECDSAAdd.Entrant.Inverse14Width

-- Verified CompactInverse14
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.CompactInverse14
open Arithmetic MappedCompressed Secp256k1 History5 CompactCertificates
def perm : Equiv.Perm Wire := Equiv.swap (0:Wire) 522 * Equiv.swap (1:Wire) 523 * Equiv.swap (2:Wire) 524 * Equiv.swap (3:Wire) 525 * Equiv.swap (4:Wire) 526 * Equiv.swap (5:Wire) 527 * Equiv.swap (6:Wire) 528 * Equiv.swap (7:Wire) 529 * Equiv.swap (8:Wire) 786 * Equiv.swap (9:Wire) 787 * Equiv.swap (10:Wire) 788 * Equiv.swap (11:Wire) 789 * Equiv.swap (12:Wire) 790 * Equiv.swap (13:Wire) 791 * Equiv.swap (14:Wire) 1551 * Equiv.swap (15:Wire) 1552 * Equiv.swap (16:Wire) 1553 * Equiv.swap (17:Wire) 1554 * Equiv.swap (18:Wire) 1556 * Equiv.swap (19:Wire) 1557 * Equiv.swap (20:Wire) 1558 * Equiv.swap (21:Wire) 1559 * Equiv.swap (22:Wire) 530
def block0 : Program := [
 .X 5,
 .CX 4 5,
 .CX 4 8,
 .CX 17 16,
 .CX 16 17,
 .CX 16 15,
 .CX 15 16,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CCX 0 1 5,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 4 14
]
theorem placement0 : renameProgram perm block0=Inverse14Width.block0 := by decide +kernel
def block1 : Program := [
 .CX 14 4,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14,
 .CX 15 16,
 .CX 16 15,
 .CX 16 17,
 .CX 17 16,
 .CX 17 16,
 .CX 16 17,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 2,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 2 4,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 6,
 .CX 0 2,
 .CX 2 0
]
theorem placement1 : renameProgram perm block1=Inverse14Width.block1 := by decide +kernel
def block2 : Program := [
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 4,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 3 2,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 15 16,
 .CX 16 15,
 .CX 16 17,
 .CX 17 16,
 .CX 17 16,
 .CX 16 17,
 .CX 16 15,
 .CX 15 16,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 2,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4
]
theorem placement2 : renameProgram perm block2=Inverse14Width.block2 := by decide +kernel
def block3 : Program := [
 .CX 2 4,
 .CX 2 1,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 1 0,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 0 2,
 .CCX 0 1 7,
 .CX 0 2,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 1 0,
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 1,
 .CX 2 4,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 3 2,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14
]
theorem placement3 : renameProgram perm block3=Inverse14Width.block3 := by decide +kernel
def block4 : Program := [
 .CX 15 16,
 .CX 16 15,
 .CX 16 17,
 .CX 17 16,
 .CX 6 15,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 15 16,
 .CX 15 14,
 .CX 14 15,
 .CX 14 2,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 8
]
theorem placement4 : renameProgram perm block4=Inverse14Width.block4 := by decide +kernel
def block5 : Program := [
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 14 2,
 .CX 14 15,
 .CX 15 14,
 .CX 15 16,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 6 15,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15
]
theorem placement5 : renameProgram perm block5=Inverse14Width.block5 := by decide +kernel
def block6 : Program := [
 .CX 4 3,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 14,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 9,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 3 14,
 .CX 4 14
]
theorem placement6 : renameProgram perm block6=Inverse14Width.block6 := by decide +kernel
def block7 : Program := [
 .CX 14 4,
 .CX 4 14,
 .CX 4 3,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 15 16,
 .CX 16 15,
 .CX 9 8,
 .CX 8 9,
 .CX 8 7,
 .CX 7 8,
 .CX 7 5,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 5 6,
 .CX 5 16,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 16 17,
 .CX 16 15,
 .CX 15 16,
 .CX 15 14,
 .CX 14 15,
 .CX 14 3,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 4,
 .CX 3 2
]
theorem placement7 : renameProgram perm block7=Inverse14Width.block7 := by decide +kernel
def block8 : Program := [
 .CX 3 1,
 .CX 1 3,
 .CX 1 2,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 10,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CX 1 2,
 .CX 1 3,
 .CX 3 1,
 .CX 3 2,
 .CX 3 4,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 14 3,
 .CX 14 15,
 .CX 15 14,
 .CX 15 16,
 .CX 16 15,
 .CX 16 17,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 5 16,
 .CX 5 6,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7
]
theorem placement8 : renameProgram perm block8=Inverse14Width.block8 := by decide +kernel
def block9 : Program := [
 .CX 7 5,
 .CX 7 8,
 .CX 8 7,
 .CX 8 9,
 .CX 9 8,
 .CX 9 6,
 .CX 8 10,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 7 9,
 .CX 9 7,
 .CX 7 9,
 .CX 6 8,
 .CX 6 16,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 5 7,
 .CX 7 5,
 .CX 5 7,
 .CX 17 6,
 .CX 6 17,
 .CX 17 6,
 .CX 16 5,
 .CX 16 3,
 .CX 15 17,
 .CX 17 15,
 .CX 15 17,
 .CX 14 16,
 .CX 16 14,
 .CX 14 16
]
theorem placement9 : renameProgram perm block9=Inverse14Width.block9 := by decide +kernel
def block10 : Program := [
 .CX 4 15,
 .CX 15 4,
 .CX 4 15,
 .CX 3 14,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 4,
 .CX 4 1,
 .CX 1 4,
 .CX 0 3,
 .CX 3 0,
 .CX 0 3,
 .CCX 0 1 2,
 .CX 9 7,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 7 8,
 .CX 7 6,
 .CX 6 7,
 .CX 6 5,
 .CX 5 6,
 .CX 5 4,
 .CX 5 3,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 16 17
]
theorem placement10 : renameProgram perm block10=Inverse14Width.block10 := by decide +kernel
def block11 : Program := [
 .CX 17 16,
 .CX 16 17,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 4 3,
 .CX 4 2,
 .CX 3 14,
 .CX 3 4,
 .CX 3 2,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 11,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 3
]
theorem placement11 : renameProgram perm block11=Inverse14Width.block11 := by decide +kernel
def block12 : Program := [
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 3 2,
 .CX 3 4,
 .CX 3 14,
 .CX 4 2,
 .CX 4 3,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 5 3,
 .CX 5 4,
 .CX 5 6,
 .CX 6 5,
 .CX 6 7,
 .CX 7 6,
 .CX 7 8,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 9 7
]
theorem placement12 : renameProgram perm block12=Inverse14Width.block12 := by decide +kernel
def block13 : Program := [
 .CX 9 7,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 7 8,
 .CX 7 17,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 17 5,
 .CX 17 16,
 .CX 16 17,
 .CX 16 4,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 4 2,
 .CX 3 0,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3
]
theorem placement13 : renameProgram perm block13=Inverse14Width.block13 := by decide +kernel
def block14 : Program := [
 .CX 0 2,
 .CCX 0 1 12,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 3 0,
 .CX 4 2,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 16 4,
 .CX 16 17,
 .CX 17 16,
 .CX 17 5,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 7 17,
 .CX 7 8,
 .CX 8 9
]
theorem placement14 : renameProgram perm block14=Inverse14Width.block14 := by decide +kernel
def block15 : Program := [
 .CX 9 8,
 .CX 8 9,
 .CX 9 7,
 .CX 12 9,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 10 11,
 .CX 11 10,
 .CX 10 11,
 .CX 9 10,
 .CX 9 6,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 6 7,
 .CX 6 5,
 .CX 5 6,
 .CX 5 17,
 .CX 17 5,
 .CX 17 16,
 .CX 16 17,
 .CX 16 14,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 14 4,
 .CX 14 3
]
theorem placement15 : renameProgram perm block15=Inverse14Width.block15 := by decide +kernel
def block16 : Program := [
 .CX 3 14,
 .CX 3 4,
 .CX 3 1,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 3,
 .CX 1 0,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 0 2,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CCX 0 1 13,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CX 0 2,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 1 0,
 .CX 1 3,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 3 1,
 .CX 3 4,
 .CX 3 14,
 .CX 14 3
]
theorem placement16 : renameProgram perm block16=Inverse14Width.block16 := by decide +kernel
def block17 : Program := [
 .CX 14 4,
 .CX 14 15,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 16 14,
 .CX 16 17,
 .CX 17 16,
 .CX 17 5,
 .CX 5 17,
 .CX 5 6,
 .CX 6 5,
 .CX 6 7,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 9 6,
 .CX 9 10,
 .CX 10 11,
 .CX 11 10,
 .CX 10 11,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 12 9,
 .CX 10 8,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10
]
theorem placement17 : renameProgram perm block17=Inverse14Width.block17 := by decide +kernel
def block18 : Program := [
 .CX 8 9,
 .CX 8 5,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 5 6,
 .CX 5 17,
 .CX 17 5,
 .CX 17 15,
 .CX 17 14,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 15 4,
 .CX 14 16,
 .CX 14 0,
 .CX 4 15,
 .CX 4 14,
 .CX 4 2,
 .CX 4 0,
 .CX 3 14,
 .CX 14 3,
 .CX 3 14,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1
]
theorem placement18 : renameProgram perm block18=Inverse14Width.block18 := by decide +kernel
def block19 : Program := [
 .CX 1 3,
 .CX 0 2,
 .CX 0 1,
 .CCX 0 1 18,
 .CX 0 1,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 3 14,
 .CX 14 3,
 .CX 3 14,
 .CX 4 0,
 .CX 4 2,
 .CX 4 14,
 .CX 4 15,
 .CX 14 0,
 .CX 14 16,
 .CX 15 4,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 17 14,
 .CX 17 15,
 .CX 17 5,
 .CX 5 17,
 .CX 5 6,
 .CX 6 7
]
theorem placement19 : renameProgram perm block19=Inverse14Width.block19 := by decide +kernel
def block20 : Program := [
 .CX 7 6,
 .CX 6 7,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 8 5,
 .CX 8 9,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 10 8,
 .CX 18 10,
 .CX 13 18,
 .CX 18 13,
 .CX 13 18,
 .CX 12 13,
 .CX 13 12,
 .CX 12 13,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 10 11,
 .CX 10 8,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 8 9,
 .CX 8 5,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 6 7
]
theorem placement20 : renameProgram perm block20=Inverse14Width.block20 := by decide +kernel
def block21 : Program := [
 .CX 7 6,
 .CX 6 7,
 .CX 5 6,
 .CX 5 17,
 .CX 17 5,
 .CX 17 15,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 15 16,
 .CX 15 4,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 4 2,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 19,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1
]
theorem placement21 : renameProgram perm block21=Inverse14Width.block21 := by decide +kernel
def block22 : Program := [
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 4 2,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 15 4,
 .CX 15 16,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 17 15,
 .CX 17 5,
 .CX 5 17,
 .CX 5 6,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 8 5,
 .CX 8 9,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 10 8,
 .CX 10 11
]
theorem placement22 : renameProgram perm block22=Inverse14Width.block22 := by decide +kernel
def block23 : Program := [
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 12 13,
 .CX 13 12,
 .CX 12 13,
 .CX 13 18,
 .CX 18 13,
 .CX 13 18,
 .CX 18 10,
 .CX 8 17,
 .CX 8 15,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 17 16,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 16 5,
 .CX 16 17,
 .CX 16 15,
 .CX 16 14,
 .CX 15 17,
 .CX 15 2,
 .CX 14 16
]
theorem placement23 : renameProgram perm block23=Inverse14Width.block23 := by decide +kernel
def block24 : Program := [
 .CX 14 15,
 .CX 14 2,
 .CX 14 1,
 .CX 4 15,
 .CX 15 4,
 .CX 4 15,
 .CX 3 14,
 .CX 14 3,
 .CX 3 14,
 .CX 2 4,
 .CX 2 0,
 .CX 1 3,
 .CX 0 2,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CCX 0 1 20,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CX 0 2,
 .CX 1 3,
 .CX 2 0,
 .CX 2 4,
 .CX 3 14,
 .CX 14 3,
 .CX 3 14,
 .CX 4 15,
 .CX 15 4,
 .CX 4 15,
 .CX 14 1,
 .CX 14 2
]
theorem placement24 : renameProgram perm block24=Inverse14Width.block24 := by decide +kernel
def block25 : Program := [
 .CX 14 15,
 .CX 14 16,
 .CX 15 2,
 .CX 15 17,
 .CX 16 14,
 .CX 16 15,
 .CX 16 17,
 .CX 16 5,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 17 16,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 8 15,
 .CX 8 17,
 .CX 20 10,
 .CX 19 20,
 .CX 20 19,
 .CX 19 20,
 .CX 18 19,
 .CX 19 18,
 .CX 18 19,
 .CX 13 18,
 .CX 18 13
]
theorem placement25 : renameProgram perm block25=Inverse14Width.block25 := by decide +kernel
def block26 : Program := [
 .CX 13 18,
 .CX 12 13,
 .CX 13 12,
 .CX 12 13,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 10 11,
 .CX 10 9,
 .CX 9 10,
 .CX 9 7,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 7 8,
 .CX 7 6,
 .CX 6 7,
 .CX 6 5,
 .CX 5 6,
 .CX 5 17,
 .CX 17 5,
 .CX 17 14,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 14 0,
 .CX 4 3,
 .CX 4 14
]
theorem placement26 : renameProgram perm block26=Inverse14Width.block26 := by decide +kernel
def block27 : Program := [
 .CX 14 4,
 .CX 4 14,
 .CX 3 14,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CCX 0 1 22,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 3 14,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 4 3,
 .CX 14 0,
 .CX 14 15,
 .CX 15 16
]
theorem placement27 : renameProgram perm block27=Inverse14Width.block27 := by decide +kernel
def block28 : Program := [
 .CX 16 15,
 .CX 15 16,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 17 14,
 .CX 17 5,
 .CX 5 17,
 .CX 5 6,
 .CX 6 5,
 .CX 6 7,
 .CX 7 6,
 .CX 7 8,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 9 7,
 .CX 9 10,
 .CX 10 9,
 .CX 10 11,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 12 13,
 .CX 13 12,
 .CX 12 13,
 .CX 13 18,
 .CX 18 13,
 .CX 13 18,
 .CX 18 19,
 .CX 19 18,
 .CX 18 19
]
theorem placement28 : renameProgram perm block28=Inverse14Width.block28 := by decide +kernel
def block29 : Program := [
 .CX 19 20,
 .CX 20 19,
 .CX 19 20,
 .CX 20 10,
 .CX 22 20,
 .CX 22 18,
 .CX 22 10,
 .CX 20 18,
 .CX 20 17,
 .CX 20 16,
 .CX 20 22,
 .CX 22 20,
 .CX 20 22,
 .CX 19 18,
 .CX 19 13,
 .CX 19 12,
 .CX 19 9,
 .CX 19 6,
 .CX 19 20,
 .CX 20 19,
 .CX 19 20,
 .CX 18 22,
 .CX 18 10,
 .CX 18 5,
 .CX 18 16,
 .CX 18 2,
 .CX 18 20,
 .CX 20 18,
 .CX 18 20,
 .CX 13 22,
 .CX 13 12,
 .CX 13 9
]
theorem placement29 : renameProgram perm block29=Inverse14Width.block29 := by decide +kernel
def block30 : Program := [
 .CX 13 6,
 .CX 13 16,
 .CX 12 22,
 .CX 12 20,
 .CX 12 5,
 .CX 12 16,
 .CX 12 14,
 .CX 12 2,
 .CX 12 18,
 .CX 18 12,
 .CX 12 18,
 .CX 11 22,
 .CX 11 20,
 .CX 11 19,
 .CX 11 5,
 .CX 11 16,
 .CX 11 2,
 .CX 11 0,
 .CX 11 18,
 .CX 18 11,
 .CX 11 18,
 .CX 10 22,
 .CX 10 20,
 .CX 10 8,
 .CX 10 5,
 .CX 10 16,
 .CX 10 2,
 .CX 10 19,
 .CX 19 10,
 .CX 10 19,
 .CX 9 22,
 .CX 9 6
]
theorem placement30 : renameProgram perm block30=Inverse14Width.block30 := by decide +kernel
def block31 : Program := [
 .CX 9 16,
 .CX 9 1,
 .CX 9 13,
 .CX 13 9,
 .CX 9 13,
 .CX 8 19,
 .CX 8 6,
 .CX 8 5,
 .CX 8 18,
 .CX 18 8,
 .CX 8 18,
 .CX 7 18,
 .CX 7 5,
 .CX 7 12,
 .CX 12 7,
 .CX 7 12,
 .CX 6 22,
 .CX 6 18,
 .CX 6 5,
 .CX 6 17,
 .CX 6 16,
 .CX 6 12,
 .CX 12 6,
 .CX 6 12,
 .CX 5 20,
 .CX 5 17,
 .CX 5 15,
 .CX 5 2,
 .CX 5 12,
 .CX 12 5,
 .CX 5 12,
 .CX 17 22
]
theorem placement31 : renameProgram perm block31=Inverse14Width.block31 := by decide +kernel
def block32 : Program := [
 .CX 17 20,
 .CX 17 18,
 .CX 17 13,
 .CX 17 12,
 .CX 17 8,
 .CX 17 16,
 .CX 17 15,
 .CX 17 4,
 .CX 17 2,
 .CX 17 1,
 .CX 17 0,
 .CX 16 22,
 .CX 16 9,
 .CX 16 7,
 .CX 16 6,
 .CX 6 16,
 .CX 16 6,
 .CX 15 20,
 .CX 15 18,
 .CX 15 13,
 .CX 15 12,
 .CX 15 2,
 .CX 15 1,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 14 11,
 .CX 14 10,
 .CX 14 8,
 .CX 14 6,
 .CX 14 16,
 .CX 14 4
]
theorem placement32 : renameProgram perm block32=Inverse14Width.block32 := by decide +kernel
def block33 : Program := [
 .CX 14 3,
 .CX 14 0,
 .CX 4 8,
 .CX 4 5,
 .CX 4 17,
 .CX 4 16,
 .CX 4 0,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 20,
 .CX 3 18,
 .CX 3 13,
 .CX 3 10,
 .CX 3 6,
 .CX 3 17,
 .CX 3 16,
 .CX 3 4,
 .CX 3 2,
 .CX 3 1,
 .CX 2 20,
 .CX 2 18,
 .CX 2 13,
 .CX 2 10,
 .CX 2 5,
 .CX 2 16,
 .CX 2 14,
 .CX 2 1,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 13
]
theorem placement33 : renameProgram perm block33=Inverse14Width.block33 := by decide +kernel
def block34 : Program := [
 .CX 1 9,
 .CX 1 17,
 .CX 17 1,
 .CX 1 17,
 .CX 0 8,
 .CX 0 16,
 .CX 0 4,
 .CX 0 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .X 14,
 .X 16,
 .X 17,
 .X 5,
 .measureX 22 [] [.Z 4, .Z 16, .Z 5, .Z 8, .Z 10, .Z 12, .Z 13, .CZ 0 8, .CZ 0 9, .CZ 0 20, .CZ 1 2, .CZ 1 3, .CZ 1 4, .CZ 1 17, .CZ 1 11, .CZ 1 12, .CZ 1 20, .CZ 2 8, .CZ 2 11, .CZ 16 6, .CZ 16 13, .CZ 16 20],
 .measureX 20 [] [.Z 4, .Z 14, .Z 15, .Z 16, .Z 17, .Z 5, .Z 7, .Z 10, .Z 12, .Z 13, .Z 18, .CZ 0 2, .CZ 0 16, .CZ 0 17, .CZ 0 13, .CZ 0 18, .CZ 1 17, .CZ 1 11, .CZ 1 18, .CZ 2 3, .CZ 2 16, .CZ 2 5, .CZ 2 6, .CZ 2 7, .CZ 2 8, .CZ 2 9, .CZ 2 11, .CZ 2 12, .CZ 2 13, .CZ 2 18, .CZ 2 19, .CZ 3 4, .CZ 3 14, .CZ 3 8, .CZ 3 10, .CZ 3 18, .CZ 4 6, .CZ 4 18, .CZ 14 16, .CZ 16 17, .CZ 16 6, .CZ 16 13, .CZ 16 18, .CZ 17 18],
 .X 19,
 .measureX 19 [] [.Z 0, .Z 1, .Z 3, .Z 14, .Z 15, .Z 8, .Z 10, .Z 11, .Z 12, .CZ 0 1, .CZ 0 2, .CZ 0 4, .CZ 0 17, .CZ 0 8, .CZ 0 10, .CZ 1 2, .CZ 1 4, .CZ 1 11, .CZ 1 12, .CZ 2 3, .CZ 2 4, .CZ 2 6, .CZ 2 7, .CZ 2 9, .CZ 2 11, .CZ 2 12, .CZ 3 4, .CZ 3 16, .CZ 3 17, .CZ 3 6, .CZ 3 8, .CZ 3 9, .CZ 3 10, .CZ 4 12, .CZ 14 16, .CZ 14 17, .CZ 14 10],
 .X 18,
 .measureX 18 [] [.Z 1, .Z 4, .Z 16, .Z 5, .Z 7, .Z 12, .CZ 0 1, .CZ 0 4, .CZ 0 16, .CZ 0 5, .CZ 0 8, .CZ 0 9, .CZ 0 11, .CZ 0 12, .CZ 1 3, .CZ 1 14, .CZ 1 17, .CZ 1 12, .CZ 2 16, .CZ 2 17, .CZ 2 7, .CZ 2 11, .CZ 2 12, .CZ 3 17, .CZ 3 5, .CZ 3 6, .CZ 3 12, .CZ 4 16, .CZ 4 5, .CZ 4 6, .CZ 4 8, .CZ 4 10, .CZ 4 12, .CZ 14 10, .CZ 16 5, .CZ 16 6, .CZ 16 10],
 .measureX 13 [] [.Z 0, .Z 2, .Z 3, .Z 4, .Z 16, .Z 17, .Z 8, .Z 11, .Z 12, .CZ 0 2, .CZ 0 16, .CZ 0 8, .CZ 0 9, .CZ 0 11, .CZ 1 2, .CZ 1 3, .CZ 1 4, .CZ 1 14, .CZ 1 11, .CZ 1 12, .CZ 2 6, .CZ 2 7, .CZ 2 8, .CZ 3 6, .CZ 3 11],
 .X 12,
 .measureX 12 [] [.Z 0, .Z 3, .Z 14, .Z 5, .Z 8, .Z 10, .CZ 0 2, .CZ 0 17, .CZ 0 10, .CZ 1 3, .CZ 1 4, .CZ 1 14, .CZ 2 17, .CZ 2 6, .CZ 2 8, .CZ 2 10, .CZ 3 14, .CZ 3 5, .CZ 3 6, .CZ 3 8, .CZ 3 9, .CZ 3 10, .CZ 4 16, .CZ 4 5, .CZ 4 8, .CZ 4 10, .CZ 14 16, .CZ 14 17, .CZ 14 8, .CZ 14 10, .CZ 16 17, .CZ 16 6, .CZ 17 6],
 .measureX 11 [] [.Z 2, .Z 3, .Z 16, .Z 8, .CZ 0 3, .CZ 0 17, .CZ 2 3, .CZ 2 14, .CZ 2 16, .CZ 2 9, .CZ 3 8, .CZ 16 17, .CZ 16 6, .CZ 16 9, .CZ 17 8],
 .measureX 10 [] [.Z 0, .Z 1, .Z 2, .Z 4, .CZ 1 2, .CZ 1 4, .CZ 1 16, .CZ 1 5],
 .X 9,
 .measureX 9 [] [.Z 17, .Z 6, .CZ 1 3, .CZ 1 14, .CZ 1 17, .CZ 1 6],
 .measureX 8 [] [.Z 0, .Z 1, .Z 2, .CZ 1 2, .CZ 1 16],
 .CX 14 5,
 .CX 5 14,
 .CX 14 5
]
theorem placement34 : renameProgram perm block34=Inverse14Width.block34 := by decide +kernel
def block35 : Program := [
 .CX 15 6,
 .CX 6 15,
 .CX 15 6,
 .CX 16 9,
 .CX 9 16,
 .CX 16 9,
 .CX 17 10,
 .CX 10 17,
 .CX 17 10,
 .CX 14 11,
 .CX 11 14,
 .CX 14 11,
 .CX 15 12,
 .CX 12 15,
 .CX 15 12,
 .CX 7 13,
 .CX 13 7,
 .CX 7 13,
 .X 8,
 .CX 1 8,
 .measureX 22 [] []
]
theorem placement35 : renameProgram perm block35=Inverse14Width.block35 := by decide +kernel
def blocks : List Program := [block0,block1,block2,block3,block4,block5,block6,block7,block8,block9,block10,block11,block12,block13,block14,block15,block16,block17,block18,block19,block20,block21,block22,block23,block24,block25,block26,block27,block28,block29,block30,block31,block32,block33,block34,block35]
def candidate : Program := blocks.flatten
theorem placement : renameProgram perm candidate=Inverse14Width.candidate := by
 rw [candidate,rename_flatten]
 simp only [blocks,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,placement0,placement1,placement2,placement3,placement4,placement5,placement6,placement7,placement8,placement9,placement10,placement11,placement12,placement13,placement14,placement15,placement16,placement17,placement18,placement19,placement20,placement21,placement22,placement23,placement24,placement25,placement26,placement27,placement28,placement29,placement30,placement31,placement32,placement33,placement34,placement35,List.append_nil,Inverse14Width.candidate,List.append_assoc]
def reference : Program := renameProgram perm.symm (tickMR8 ++ W.ReverseCarry.compactReceiverTick base 507)
theorem reference_placement : renameProgram perm reference=(tickMR8 ++ W.ReverseCarry.compactReceiverTick base 507) := rename_inverse _ _
def trace0 : List Nat := [286, 16398, 16408, 16402, 30, 16667, 286, 16646, 16918, 702, 33822, 50195, 99343, 50195, 115723, 54291, 100371, 100371, 54035, 102406, 53491, 59571, 124931, 58387, 250903, 218135, 54291, 124955, 4237331, 4248595, 4968467, 1215543, 7187, 7187, 228642, 2, 2]
theorem checked0 : checkTrace blocks trace0=true := by decide +kernel
theorem old0 : phaseClean508 reference 286=some 2 := by decide +kernel
theorem row0 (m n : List Bool) : run candidate m ⟨false,tbN_t8 286⟩=run reference n ⟨false,tbN_t8 286⟩ := by
 have h:=trace_sound blocks 286 [16398, 16408, 16402, 30, 16667, 286, 16646, 16918, 702, 33822, 50195, 99343, 50195, 115723, 54291, 100371, 100371, 54035, 102406, 53491, 59571, 124931, 58387, 250903, 218135, 54291, 124955, 4237331, 4248595, 4968467, 1215543, 7187, 7187, 228642, 2, 2] checked0 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old0 n]
 rfl
def trace1 : List Nat := [286, 16398, 16408, 16402, 30, 16667, 286, 16646, 16918, 702, 33822, 50195, 99343, 50195, 115723, 54291, 100371, 100371, 54035, 102406, 53491, 59571, 124931, 58387, 250903, 218135, 54291, 124955, 4237331, 4248595, 4968467, 1215543, 7187, 7187, 228642, 2, 2]
theorem checked1 : checkTrace blocks trace1=true := by decide +kernel
theorem old1 : phaseClean508 reference 286=some 2 := by decide +kernel
theorem row1 (m n : List Bool) : run candidate m ⟨false,tbN_t8 286⟩=run reference n ⟨false,tbN_t8 286⟩ := by
 have h:=trace_sound blocks 286 [16398, 16408, 16402, 30, 16667, 286, 16646, 16918, 702, 33822, 50195, 99343, 50195, 115723, 54291, 100371, 100371, 54035, 102406, 53491, 59571, 124931, 58387, 250903, 218135, 54291, 124955, 4237331, 4248595, 4968467, 1215543, 7187, 7187, 228642, 2, 2] checked1 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old1 n]
 rfl
def trace2 : List Nat := [287, 16399, 16413, 16403, 31, 16671, 287, 16647, 16919, 703, 33823, 50203, 115723, 50203, 115726, 50203, 116739, 116747, 49947, 114694, 49403, 51387, 641031, 574491, 771103, 738335, 1098779, 1165331, 1083419, 1098779, 1433727, 1110079, 4346523, 154650, 97574, 1, 257]
theorem checked2 : checkTrace blocks trace2=true := by decide +kernel
theorem old2 : phaseClean508 reference 287=some 257 := by decide +kernel
theorem row2 (m n : List Bool) : run candidate m ⟨false,tbN_t8 287⟩=run reference n ⟨false,tbN_t8 287⟩ := by
 have h:=trace_sound blocks 287 [16399, 16413, 16403, 31, 16671, 287, 16647, 16919, 703, 33823, 50203, 115723, 50203, 115726, 50203, 116739, 116747, 49947, 114694, 49403, 51387, 641031, 574491, 771103, 738335, 1098779, 1165331, 1083419, 1098779, 1433727, 1110079, 4346523, 154650, 97574, 1, 257] checked2 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old2 n]
 rfl
def trace3 : List Nat := [287, 16399, 16413, 16403, 31, 16671, 287, 16647, 16919, 703, 33823, 50203, 115723, 50203, 115726, 50203, 116739, 116747, 49947, 114694, 49403, 51387, 641031, 574491, 771103, 738335, 1098779, 1165331, 1083419, 1098779, 1433727, 1110079, 4346523, 154650, 97574, 1, 257]
theorem checked3 : checkTrace blocks trace3=true := by decide +kernel
theorem old3 : phaseClean508 reference 287=some 257 := by decide +kernel
theorem row3 (m n : List Bool) : run candidate m ⟨false,tbN_t8 287⟩=run reference n ⟨false,tbN_t8 287⟩ := by
 have h:=trace_sound blocks 287 [16399, 16413, 16403, 31, 16671, 287, 16647, 16919, 703, 33823, 50203, 115723, 50203, 115726, 50203, 116739, 116747, 49947, 114694, 49403, 51387, 641031, 574491, 771103, 738335, 1098779, 1165331, 1083419, 1098779, 1433727, 1110079, 4346523, 154650, 97574, 1, 257] checked3 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old3 n]
 rfl
def trace4 : List Nat := [284, 16396, 16400, 16400, 28, 16659, 284, 16644, 16916, 700, 33820, 50179, 99331, 50179, 99337, 50179, 116763, 116755, 49923, 65545, 311523, 51203, 100355, 51203, 508935, 476167, 574467, 624643, 559107, 312323, 5357607, 5357607, 217091, 154690, 31803, 4, 260]
theorem checked4 : checkTrace blocks trace4=true := by decide +kernel
theorem old4 : phaseClean508 reference 284=some 260 := by decide +kernel
theorem row4 (m n : List Bool) : run candidate m ⟨false,tbN_t8 284⟩=run reference n ⟨false,tbN_t8 284⟩ := by
 have h:=trace_sound blocks 284 [16396, 16400, 16400, 28, 16659, 284, 16644, 16916, 700, 33820, 50179, 99331, 50179, 99337, 50179, 116763, 116755, 49923, 65545, 311523, 51203, 100355, 51203, 508935, 476167, 574467, 624643, 559107, 312323, 5357607, 5357607, 217091, 154690, 31803, 4, 260] checked4 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old4 n]
 rfl
def trace5 : List Nat := [16668, 32796, 49168, 49176, 16412, 49169, 32796, 49156, 49172, 16412, 65564, 245767, 229403, 114695, 229401, 114695, 229383, 229383, 114695, 196633, 376839, 114855, 229395, 117767, 458791, 458791, 638983, 770054, 737287, 376839, 5293091, 639239, 180263, 5734048, 5603033, 213188, 16132]
theorem checked5 : checkTrace blocks trace5=true := by decide +kernel
theorem old5 : phaseClean508 reference 16668=some 16132 := by decide +kernel
theorem row5 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16668⟩=run reference n ⟨false,tbN_t8 16668⟩ := by
 have h:=trace_sound blocks 16668 [32796, 49168, 49176, 16412, 49169, 32796, 49156, 49172, 16412, 65564, 245767, 229403, 114695, 229401, 114695, 229383, 229383, 114695, 196633, 376839, 114855, 229395, 117767, 458791, 458791, 638983, 770054, 737287, 376839, 5293091, 639239, 180263, 5734048, 5603033, 213188, 16132] checked5 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old5 n]
 rfl
def trace6 : List Nat := [285, 16397, 16405, 16401, 29, 16663, 285, 16645, 16917, 701, 33821, 50187, 117767, 52235, 101388, 52235, 120851, 120859, 51979, 83977, 313579, 55307, 628743, 579595, 1035279, 1002511, 1625099, 1677323, 5806091, 5557259, 1042507, 5763118, 4281226, 89114, 163110, 65539, 515]
theorem checked6 : checkTrace blocks trace6=true := by decide +kernel
theorem old6 : phaseClean508 reference 285=some 515 := by decide +kernel
theorem row6 (m n : List Bool) : run candidate m ⟨false,tbN_t8 285⟩=run reference n ⟨false,tbN_t8 285⟩ := by
 have h:=trace_sound blocks 285 [16397, 16405, 16401, 29, 16663, 285, 16645, 16917, 701, 33821, 50187, 117767, 52235, 101388, 52235, 120851, 120859, 51979, 83977, 313579, 55307, 628743, 579595, 1035279, 1002511, 1625099, 1677323, 5806091, 5557259, 1042507, 5763118, 4281226, 89114, 163110, 65539, 515] checked6 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old6 n]
 rfl
def trace7 : List Nat := [16669, 32829, 49205, 49209, 16573, 49365, 32957, 49317, 49493, 16797, 66205, 246031, 246047, 115343, 229660, 115471, 247063, 247071, 115855, 214297, 378127, 116143, 754967, 642703, 983855, 983855, 1688207, 1819918, 1787151, 1426063, 4580047, 62159, 189165, 5757994, 5749799, 98367, 639]
theorem checked7 : checkTrace blocks trace7=true := by decide +kernel
theorem old7 : phaseClean508 reference 16669=some 639 := by decide +kernel
theorem row7 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16669⟩=run reference n ⟨false,tbN_t8 16669⟩ := by
 have h:=trace_sound blocks 16669 [32829, 49205, 49209, 16573, 49365, 32957, 49317, 49493, 16797, 66205, 246031, 246047, 115343, 229660, 115471, 247063, 247071, 115855, 214297, 378127, 116143, 754967, 642703, 983855, 983855, 1688207, 1819918, 1787151, 1426063, 4580047, 62159, 189165, 5757994, 5749799, 98367, 639] checked7 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old7 n]
 rfl
def trace8 : List Nat := [282, 16394, 16396, 16406, 26, 16393, 26, 16386, 16414, 26, 26, 49170, 98318, 49170, 114698, 49170, 114698, 114690, 49170, 98317, 311314, 49330, 114690, 52242, 507926, 475158, 573458, 622619, 4800530, 4505618, 1753142, 1229878, 21522, 88386, 227643, 65542, 518]
theorem checked8 : checkTrace blocks trace8=true := by decide +kernel
theorem old8 : phaseClean508 reference 282=some 518 := by decide +kernel
theorem row8 (m n : List Bool) : run candidate m ⟨false,tbN_t8 282⟩=run reference n ⟨false,tbN_t8 282⟩ := by
 have h:=trace_sound blocks 282 [16394, 16396, 16406, 26, 16393, 26, 16386, 16414, 26, 26, 49170, 98318, 49170, 114698, 49170, 114698, 114690, 49170, 98317, 311314, 49330, 114690, 52242, 507926, 475158, 573458, 622619, 4800530, 4505618, 1753142, 1229878, 21522, 88386, 227643, 65542, 518] checked8 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old8 n]
 rfl
def trace9 : List Nat := [33050, 65562, 81998, 82014, 98394, 81929, 82010, 65618, 82066, 33882, 148754, 50736, 99884, 181520, 116256, 181776, 100912, 100912, 180752, 98863, 180752, 182800, 117288, 181520, 214032, 1295376, 450832, 117304, 35376, 704784, 1098036, 1098036, 4804656, 614304, 745433, 213190, 15878]
theorem checked9 : checkTrace blocks trace9=true := by decide +kernel
theorem old9 : phaseClean508 reference 33050=some 15878 := by decide +kernel
theorem row9 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33050⟩=run reference n ⟨false,tbN_t8 33050⟩ := by
 have h:=trace_sound blocks 33050 [65562, 81998, 82014, 98394, 81929, 82010, 65618, 82066, 33882, 148754, 50736, 99884, 181520, 116256, 181776, 100912, 100912, 180752, 98863, 180752, 182800, 117288, 181520, 214032, 1295376, 450832, 117304, 35376, 704784, 1098036, 1098036, 4804656, 614304, 745433, 213190, 15878] checked9 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old9 n]
 rfl
def trace10 : List Nat := [283, 16395, 16393, 16407, 27, 16397, 27, 16387, 16415, 27, 27, 49178, 114698, 49178, 114703, 53274, 98330, 98330, 53274, 118797, 315418, 57530, 647174, 584730, 1036318, 1003550, 1626138, 1679379, 1663002, 1363994, 4517978, 1095742, 4332186, 203083, 96575, 65541, 773]
theorem checked10 : checkTrace blocks trace10=true := by decide +kernel
theorem old10 : phaseClean508 reference 283=some 773 := by decide +kernel
theorem row10 (m n : List Bool) : run candidate m ⟨false,tbN_t8 283⟩=run reference n ⟨false,tbN_t8 283⟩ := by
 have h:=trace_sound blocks 283 [16395, 16393, 16407, 27, 16397, 27, 16387, 16415, 27, 27, 49178, 114698, 49178, 114703, 53274, 98330, 98330, 53274, 118797, 315418, 57530, 647174, 584730, 1036318, 1003550, 1626138, 1679379, 1663002, 1363994, 4517978, 1095742, 4332186, 203083, 96575, 65541, 773] checked10 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old10 n]
 rfl
def trace11 : List Nat := [33051, 65595, 82027, 82047, 98555, 82125, 82171, 65779, 82387, 34267, 149395, 51000, 116520, 182168, 116517, 181528, 118560, 118568, 181912, 116527, 182040, 184088, 642860, 706456, 739096, 1820440, 1500056, 1167152, 1085240, 1754008, 387032, 1700604, 4813562, 654634, 630055, 98365, 893]
theorem checked11 : checkTrace blocks trace11=true := by decide +kernel
theorem old11 : phaseClean508 reference 33051=some 893 := by decide +kernel
theorem row11 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33051⟩=run reference n ⟨false,tbN_t8 33051⟩ := by
 have h:=trace_sound blocks 33051 [65595, 82027, 82047, 98555, 82125, 82171, 65779, 82387, 34267, 149395, 51000, 116520, 182168, 116517, 181528, 118560, 118568, 181912, 116527, 182040, 184088, 642860, 706456, 739096, 1820440, 1500056, 1167152, 1085240, 1754008, 387032, 1700604, 4813562, 654634, 630055, 98365, 893] checked11 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old11 n]
 rfl
def trace12 : List Nat := [280, 16392, 16388, 16404, 24, 16385, 24, 16384, 16412, 24, 24, 49154, 98306, 49154, 98312, 49154, 114714, 114706, 49154, 65538, 49154, 49154, 98306, 49154, 245766, 212998, 49154, 114691, 81922, 49154, 49154, 49154, 49154, 1342804, 30762, 65544, 776]
theorem checked12 : checkTrace blocks trace12=true := by decide +kernel
theorem old12 : phaseClean508 reference 280=some 776 := by decide +kernel
theorem row12 (m n : List Bool) : run candidate m ⟨false,tbN_t8 280⟩=run reference n ⟨false,tbN_t8 280⟩ := by
 have h:=trace_sound blocks 280 [16392, 16388, 16404, 24, 16385, 24, 16384, 16412, 24, 24, 49154, 98306, 49154, 98312, 49154, 114714, 114706, 49154, 65538, 49154, 49154, 98306, 49154, 245766, 212998, 49154, 114691, 81922, 49154, 49154, 49154, 49154, 1342804, 30762, 65544, 776] checked12 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old12 n]
 rfl
def trace13 : List Nat := [33048, 65560, 81990, 82012, 98520, 82049, 82136, 65744, 82332, 33272, 148240, 180792, 98856, 180992, 98848, 180608, 116280, 116272, 181504, 67114, 181984, 181920, 99880, 180992, 213504, 1294848, 452352, 99872, 34336, 706304, 1099556, 639552, 6123558, 1933238, 613064, 147656, 15624]
theorem checked13 : checkTrace blocks trace13=true := by decide +kernel
theorem old13 : phaseClean508 reference 33048=some 15624 := by decide +kernel
theorem row13 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33048⟩=run reference n ⟨false,tbN_t8 33048⟩ := by
 have h:=trace_sound blocks 33048 [65560, 81990, 82012, 98520, 82049, 82136, 65744, 82332, 33272, 148240, 180792, 98856, 180992, 98848, 180608, 116280, 116272, 181504, 67114, 181984, 181920, 99880, 180992, 213504, 1294848, 452352, 99872, 34336, 706304, 1099556, 639552, 6123558, 1933238, 613064, 147656, 15624] checked13 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old13 n]
 rfl
def trace14 : List Nat := [281, 16393, 16385, 16405, 25, 16389, 25, 16385, 16413, 25, 25, 49162, 116742, 51210, 100365, 51210, 118802, 127002, 59402, 92162, 59402, 315402, 888838, 839690, 780302, 747534, 1361930, 1429515, 5591050, 5302282, 2021998, 5675567, 4274569, 15177, 162621, 131079, 1031]
theorem checked14 : checkTrace blocks trace14=true := by decide +kernel
theorem old14 : phaseClean508 reference 281=some 1031 := by decide +kernel
theorem row14 (m n : List Bool) : run candidate m ⟨false,tbN_t8 281⟩=run reference n ⟨false,tbN_t8 281⟩ := by
 have h:=trace_sound blocks 281 [16393, 16385, 16405, 25, 16389, 25, 16385, 16413, 25, 25, 49162, 116742, 51210, 100365, 51210, 118802, 127002, 59402, 92162, 59402, 315402, 888838, 839690, 780302, 747534, 1361930, 1429515, 5591050, 5302282, 2021998, 5675567, 4274569, 15177, 162621, 131079, 1031] checked14 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old14 n]
 rfl
def trace15 : List Nat := [33049, 65593, 82019, 82045, 98425, 81989, 82041, 65649, 82141, 32889, 147857, 181040, 115500, 180616, 99109, 180872, 99112, 107304, 188808, 90922, 189416, 443304, 885548, 967048, 745736, 1827080, 1238408, 1409832, 1344296, 1762696, 4576200, 5282732, 6203630, 695161, 760380, 163899, 1147]
theorem checked15 : checkTrace blocks trace15=true := by decide +kernel
theorem old15 : phaseClean508 reference 33049=some 1147 := by decide +kernel
theorem row15 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33049⟩=run reference n ⟨false,tbN_t8 33049⟩ := by
 have h:=trace_sound blocks 33049 [65593, 82019, 82045, 98425, 81989, 82041, 65649, 82141, 32889, 147857, 181040, 115500, 180616, 99109, 180872, 99112, 107304, 188808, 90922, 189416, 443304, 885548, 967048, 745736, 1827080, 1238408, 1409832, 1344296, 1762696, 4576200, 5282732, 6203630, 695161, 760380, 163899, 1147] checked15 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old15 n]
 rfl
def trace16 : List Nat := [278, 16390, 16412, 16390, 22, 16410, 22, 16398, 16390, 22, 22, 32785, 65549, 32785, 81923, 36881, 81929, 81921, 36881, 36865, 299025, 41137, 90121, 44049, 430101, 430101, 561169, 614425, 4792337, 4493329, 1740853, 4443153, 248849, 1536086, 218408, 131082, 1034]
theorem checked16 : checkTrace blocks trace16=true := by decide +kernel
theorem old16 : phaseClean508 reference 278=some 1034 := by decide +kernel
theorem row16 (m n : List Bool) : run candidate m ⟨false,tbN_t8 278⟩=run reference n ⟨false,tbN_t8 278⟩ := by
 have h:=trace_sound blocks 278 [16390, 16412, 16390, 22, 16410, 22, 16398, 16390, 22, 22, 32785, 65549, 32785, 81923, 36881, 81929, 81921, 36881, 36865, 299025, 41137, 90121, 44049, 430101, 430101, 561169, 614425, 4792337, 4493329, 1740853, 4443153, 248849, 1536086, 218408, 131082, 1034] checked16 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old16 n]
 rfl
def trace17 : List Nat := [65814, 131094, 147550, 147534, 163926, 147480, 16470, 606, 147590, 65782, 16702, 164431, 66143, 33079, 82521, 33335, 82511, 90695, 41271, 41555, 41687, 295575, 344659, 295223, 188499, 155731, 295223, 328286, 311895, 41271, 4240183, 5303059, 5958193, 1004726, 1798600, 147658, 15370]
theorem checked17 : checkTrace blocks trace17=true := by decide +kernel
theorem old17 : phaseClean508 reference 65814=some 15370 := by decide +kernel
theorem row17 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65814⟩=run reference n ⟨false,tbN_t8 65814⟩ := by
 have h:=trace_sound blocks 65814 [131094, 147550, 147534, 163926, 147480, 16470, 606, 147590, 65782, 16702, 164431, 66143, 33079, 82521, 33335, 82511, 90695, 41271, 41555, 41687, 295575, 344659, 295223, 188499, 155731, 295223, 328286, 311895, 41271, 4240183, 5303059, 5958193, 1004726, 1798600, 147658, 15370] checked17 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old17 n]
 rfl
def trace18 : List Nat := [279, 16391, 16409, 16391, 23, 16414, 23, 16399, 16391, 23, 23, 32793, 81929, 32793, 81926, 32793, 65561, 65561, 32793, 49153, 294937, 32953, 606221, 560153, 950301, 950301, 1605657, 1654801, 1638425, 1343513, 4497497, 4304921, 4293273, 1388639, 87340, 131081, 1289]
theorem checked18 : checkTrace blocks trace18=true := by decide +kernel
theorem old18 : phaseClean508 reference 279=some 1289 := by decide +kernel
theorem row18 (m n : List Bool) : run candidate m ⟨false,tbN_t8 279⟩=run reference n ⟨false,tbN_t8 279⟩ := by
 have h:=trace_sound blocks 279 [16391, 16409, 16391, 23, 16414, 23, 16399, 16391, 23, 23, 32793, 81929, 32793, 81926, 32793, 65561, 65561, 32793, 49153, 294937, 32953, 606221, 560153, 950301, 950301, 1605657, 1654801, 1638425, 1343513, 4497497, 4304921, 4293273, 1388639, 87340, 131081, 1289] checked18 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old18 n]
 rfl
def trace19 : List Nat := [65815, 131127, 147579, 147567, 164087, 147676, 16631, 767, 147911, 65911, 17343, 164679, 82779, 33727, 82780, 33087, 67423, 67423, 34239, 51027, 34783, 34719, 608087, 558015, 705371, 672603, 1082303, 1115990, 1099615, 1082303, 1419227, 635647, 5845753, 1618041, 1683772, 163897, 1401]
theorem checked19 : checkTrace blocks trace19=true := by decide +kernel
theorem old19 : phaseClean508 reference 65815=some 1401 := by decide +kernel
theorem row19 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65815⟩=run reference n ⟨false,tbN_t8 65815⟩ := by
 have h:=trace_sound blocks 65815 [131127, 147579, 147567, 164087, 147676, 16631, 767, 147911, 65911, 17343, 164679, 82779, 33727, 82780, 33087, 67423, 67423, 34239, 51027, 34783, 34719, 608087, 558015, 705371, 672603, 1082303, 1115990, 1099615, 1082303, 1419227, 635647, 5845753, 1618041, 1683772, 163897, 1401] checked19 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old19 n]
 rfl
def trace20 : List Nat := [276, 16388, 16404, 16388, 20, 16402, 20, 16396, 16388, 20, 20, 32769, 65537, 32769, 65537, 32769, 65537, 65537, 32769, 14, 32769, 32769, 65545, 32769, 163845, 163845, 32769, 65537, 65537, 32769, 32769, 32769, 32769, 1388551, 21553, 131084, 1292]
theorem checked20 : checkTrace blocks trace20=true := by decide +kernel
theorem old20 : phaseClean508 reference 276=some 1292 := by decide +kernel
theorem row20 (m n : List Bool) : run candidate m ⟨false,tbN_t8 276⟩=run reference n ⟨false,tbN_t8 276⟩ := by
 have h:=trace_sound blocks 276 [16388, 16404, 16388, 20, 16402, 20, 16396, 16388, 20, 20, 32769, 65537, 32769, 65537, 32769, 65537, 65537, 32769, 14, 32769, 32769, 65545, 32769, 163845, 163845, 32769, 65537, 65537, 32769, 32769, 32769, 32769, 1388551, 21553, 131084, 1292] checked20 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old20 n]
 rfl
def trace21 : List Nat := [65812, 131092, 147542, 147532, 164052, 147600, 16596, 732, 147848, 66900, 18236, 34375, 67163, 34599, 67161, 34215, 69191, 69191, 34343, 1622, 34343, 36391, 69203, 34599, 181827, 149059, 34599, 85574, 52807, 34599, 34599, 1671747, 5058597, 799461, 1668819, 82124, 15116]
theorem checked21 : checkTrace blocks trace21=true := by decide +kernel
theorem old21 : phaseClean508 reference 65812=some 15116 := by decide +kernel
theorem row21 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65812⟩=run reference n ⟨false,tbN_t8 65812⟩ := by
 have h:=trace_sound blocks 65812 [131092, 147542, 147532, 164052, 147600, 16596, 732, 147848, 66900, 18236, 34375, 67163, 34599, 67161, 34215, 69191, 69191, 34343, 1622, 34343, 36391, 69203, 34599, 181827, 149059, 34599, 85574, 52807, 34599, 34599, 1671747, 5058597, 799461, 1668819, 82124, 15116] checked21 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old21 n]
 rfl
def trace22 : List Nat := [277, 16389, 16401, 16389, 21, 16406, 21, 16397, 16389, 21, 21, 32777, 83973, 34825, 67588, 34825, 69641, 69641, 34825, 18446, 34825, 36873, 593933, 561161, 690189, 690189, 1083401, 1118217, 5312521, 5277705, 6203501, 438280, 4359048, 1454175, 152876, 196619, 1547]
theorem checked22 : checkTrace blocks trace22=true := by decide +kernel
theorem old22 : phaseClean508 reference 277=some 1547 := by decide +kernel
theorem row22 (m n : List Bool) : run candidate m ⟨false,tbN_t8 277⟩=run reference n ⟨false,tbN_t8 277⟩ := by
 have h:=trace_sound blocks 277 [16389, 16401, 16389, 21, 16406, 21, 16397, 16389, 21, 21, 32777, 83973, 34825, 67588, 34825, 69641, 69641, 34825, 18446, 34825, 36873, 593933, 561161, 690189, 690189, 1083401, 1118217, 5312521, 5277705, 6203501, 438280, 4359048, 1454175, 152876, 196619, 1547] checked22 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old22 n]
 rfl
def trace23 : List Nat := [65813, 131125, 147571, 147565, 163957, 147540, 16501, 637, 147657, 66773, 17853, 34639, 83807, 34223, 67420, 34479, 84823, 84831, 33455, 17238, 33583, 35631, 592727, 558511, 705867, 673099, 1082799, 1133390, 1100623, 1082799, 1417675, 1094027, 5051119, 823407, 1815597, 229431, 1655]
theorem checked23 : checkTrace blocks trace23=true := by decide +kernel
theorem old23 : phaseClean508 reference 65813=some 1655 := by decide +kernel
theorem row23 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65813⟩=run reference n ⟨false,tbN_t8 65813⟩ := by
 have h:=trace_sound blocks 65813 [131125, 147571, 147565, 163957, 147540, 16501, 637, 147657, 66773, 17853, 34639, 83807, 34223, 67420, 34479, 84823, 84831, 33455, 17238, 33583, 35631, 592727, 558511, 705867, 673099, 1082799, 1133390, 1100623, 1082799, 1417675, 1094027, 5051119, 823407, 1815597, 229431, 1655] checked23 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old23 n]
 rfl
def trace24 : List Nat := [274, 16386, 16392, 16386, 18, 16392, 18, 16394, 16386, 1042, 1042, 33808, 66572, 33808, 82946, 33808, 67600, 67600, 33552, 32778, 33008, 34992, 83976, 33808, 164884, 164884, 33808, 67609, 4245520, 4228112, 4947984, 4424720, 230416, 1455367, 217393, 196622, 1550]
theorem checked24 : checkTrace blocks trace24=true := by decide +kernel
theorem old24 : phaseClean508 reference 274=some 1550 := by decide +kernel
theorem row24 (m n : List Bool) : run candidate m ⟨false,tbN_t8 274⟩=run reference n ⟨false,tbN_t8 274⟩ := by
 have h:=trace_sound blocks 274 [16386, 16392, 16386, 18, 16392, 18, 16394, 16386, 1042, 1042, 33808, 66572, 33808, 82946, 33808, 67600, 67600, 33552, 32778, 33008, 34992, 83976, 33808, 164884, 164884, 33808, 67609, 4245520, 4228112, 4947984, 4424720, 230416, 1455367, 217393, 196622, 1550] checked24 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old24 n]
 rfl
def trace25 : List Nat := [65810, 131090, 147466, 147466, 163986, 147592, 16530, 666, 147726, 65810, 562, 32848, 65612, 33328, 81984, 33712, 66640, 66640, 33840, 33866, 33840, 33840, 83016, 33328, 164436, 164436, 33328, 83032, 66640, 33328, 33328, 4227696, 4628530, 1184741, 481235, 82126, 14862]
theorem checked25 : checkTrace blocks trace25=true := by decide +kernel
theorem old25 : phaseClean508 reference 65810=some 14862 := by decide +kernel
theorem row25 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65810⟩=run reference n ⟨false,tbN_t8 65810⟩ := by
 have h:=trace_sound blocks 65810 [131090, 147466, 147466, 163986, 147592, 16530, 666, 147726, 65810, 562, 32848, 65612, 33328, 81984, 33712, 66640, 66640, 33840, 33866, 33840, 33840, 83016, 33328, 164436, 164436, 33328, 83032, 66640, 33328, 33328, 4227696, 4628530, 1184741, 481235, 82126, 14862] checked25 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old25 n]
 rfl
def trace26 : List Nat := [275, 16387, 16397, 16387, 19, 16396, 19, 16395, 16387, 1043, 1043, 33816, 82952, 33816, 82951, 37912, 83968, 83976, 37656, 53258, 37112, 43192, 616460, 566296, 693276, 693276, 1086488, 1124369, 1107992, 1086488, 1421436, 4323352, 4311704, 1340686, 86325, 196621, 1805]
theorem checked26 : checkTrace blocks trace26=true := by decide +kernel
theorem old26 : phaseClean508 reference 275=some 1805 := by decide +kernel
theorem row26 (m n : List Bool) : run candidate m ⟨false,tbN_t8 275⟩=run reference n ⟨false,tbN_t8 275⟩ := by
 have h:=trace_sound blocks 275 [16387, 16397, 16387, 19, 16396, 19, 16395, 16387, 1043, 1043, 33816, 82952, 33816, 82951, 37912, 83968, 83976, 37656, 53258, 37112, 43192, 616460, 566296, 693276, 693276, 1086488, 1124369, 1107992, 1086488, 1421436, 4323352, 4311704, 1340686, 86325, 196621, 1805] checked26 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old26 n]
 rfl
def trace27 : List Nat := [65811, 131123, 147503, 147499, 163891, 147532, 16435, 571, 147535, 65683, 179, 33112, 82248, 32952, 82245, 32952, 82240, 82248, 32952, 49482, 33080, 33080, 606540, 557240, 688476, 688476, 1081528, 1130832, 1114456, 1081528, 1418460, 4829624, 4621048, 1225071, 365869, 229429, 1909]
theorem checked27 : checkTrace blocks trace27=true := by decide +kernel
theorem old27 : phaseClean508 reference 65811=some 1909 := by decide +kernel
theorem row27 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65811⟩=run reference n ⟨false,tbN_t8 65811⟩ := by
 have h:=trace_sound blocks 65811 [131123, 147503, 147499, 163891, 147532, 16435, 571, 147535, 65683, 179, 33112, 82248, 32952, 82245, 32952, 82240, 82248, 32952, 49482, 33080, 33080, 606540, 557240, 688476, 688476, 1081528, 1130832, 1114456, 1081528, 1418460, 4829624, 4621048, 1225071, 365869, 229429, 1909] checked27 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old27 n]
 rfl
def trace28 : List Nat := [272, 16384, 16384, 16384, 16, 16384, 16, 16392, 16384, 16, 16, 32768, 65536, 32768, 65536, 32768, 65536, 65536, 32768, 15, 32768, 32768, 65544, 32768, 163844, 163844, 32768, 65536, 65536, 32768, 32768, 32768, 32768, 1388550, 21552, 196624, 1808]
theorem checked28 : checkTrace blocks trace28=true := by decide +kernel
theorem old28 : phaseClean508 reference 272=some 1808 := by decide +kernel
theorem row28 (m n : List Bool) : run candidate m ⟨false,tbN_t8 272⟩=run reference n ⟨false,tbN_t8 272⟩ := by
 have h:=trace_sound blocks 272 [16384, 16384, 16384, 16, 16384, 16, 16392, 16384, 16, 16, 32768, 65536, 32768, 65536, 32768, 65536, 65536, 32768, 15, 32768, 32768, 65544, 32768, 163844, 163844, 32768, 65536, 65536, 32768, 32768, 32768, 32768, 1388550, 21552, 196624, 1808] checked28 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old28 n]
 rfl
def trace29 : List Nat := [65808, 131088, 147458, 147464, 163856, 147456, 16400, 536, 147456, 65712, 48, 163928, 65608, 32800, 65600, 32800, 82008, 82000, 32800, 69, 294944, 32896, 65608, 35872, 426052, 426052, 557088, 606273, 573504, 294944, 5342212, 557344, 5312548, 1053412, 349906, 16592, 14608]
theorem checked29 : checkTrace blocks trace29=true := by decide +kernel
theorem old29 : phaseClean508 reference 65808=some 14608 := by decide +kernel
theorem row29 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65808⟩=run reference n ⟨false,tbN_t8 65808⟩ := by
 have h:=trace_sound blocks 65808 [131088, 147458, 147464, 163856, 147456, 16400, 536, 147456, 65712, 48, 163928, 65608, 32800, 65600, 32800, 82008, 82000, 32800, 69, 294944, 32896, 65608, 35872, 426052, 426052, 557088, 606273, 573504, 294944, 5342212, 557344, 5312548, 1053412, 349906, 16592, 14608] checked29 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old29 n]
 rfl
def trace30 : List Nat := [273, 16385, 16389, 16385, 17, 16388, 17, 16393, 16385, 17, 17, 32776, 83972, 34824, 67589, 34824, 69640, 77832, 43016, 26639, 43016, 299016, 856076, 823304, 698380, 698380, 1345544, 1380360, 1380360, 1091592, 5611116, 5037833, 4386219, 1528620, 153367, 16399, 2063]
theorem checked30 : checkTrace blocks trace30=true := by decide +kernel
theorem old30 : phaseClean508 reference 273=some 2063 := by decide +kernel
theorem row30 (m n : List Bool) : run candidate m ⟨false,tbN_t8 273⟩=run reference n ⟨false,tbN_t8 273⟩ := by
 have h:=trace_sound blocks 273 [16385, 16389, 16385, 17, 16388, 17, 16393, 16385, 17, 17, 32776, 83972, 34824, 67589, 34824, 69640, 77832, 43016, 26639, 43016, 299016, 856076, 823304, 698380, 698380, 1345544, 1380360, 1380360, 1091592, 5611116, 5037833, 4386219, 1528620, 153367, 16399, 2063] checked30 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old30 n]
 rfl
def trace31 : List Nat := [65809, 131121, 147495, 147497, 164017, 147652, 16561, 697, 147777, 65841, 689, 164176, 82252, 33448, 65861, 33576, 66888, 75080, 42152, 25925, 304424, 296328, 853324, 822952, 959308, 959308, 1868456, 1918281, 6079816, 5546664, 5215464, 4972008, 5332172, 1168156, 497174, 49203, 2163]
theorem checked31 : checkTrace blocks trace31=true := by decide +kernel
theorem old31 : phaseClean508 reference 65809=some 2163 := by decide +kernel
theorem row31 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65809⟩=run reference n ⟨false,tbN_t8 65809⟩ := by
 have h:=trace_sound blocks 65809 [131121, 147495, 147497, 164017, 147652, 16561, 697, 147777, 65841, 689, 164176, 82252, 33448, 65861, 33576, 66888, 75080, 42152, 25925, 304424, 296328, 853324, 822952, 959308, 959308, 1868456, 1918281, 6079816, 5546664, 5215464, 4972008, 5332172, 1168156, 497174, 49203, 2163] checked31 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old31 n]
 rfl
def trace32 : List Nat := [46, 14, 24, 18, 14, 283, 270, 270, 534, 686, 33806, 17427, 33807, 17427, 50187, 21523, 34835, 34835, 21267, 102409, 282867, 26643, 59395, 26643, 349203, 381971, 545811, 583707, 4827155, 4477971, 1725495, 1707319, 236595, 1453348, 223506, 16402, 2066]
theorem checked32 : checkTrace blocks trace32=true := by decide +kernel
theorem old32 : phaseClean508 reference 46=some 2066 := by decide +kernel
theorem row32 (m n : List Bool) : run candidate m ⟨false,tbN_t8 46⟩=run reference n ⟨false,tbN_t8 46⟩ := by
 have h:=trace_sound blocks 46 [14, 24, 18, 14, 283, 270, 270, 534, 686, 33806, 17427, 33807, 17427, 50187, 21523, 34835, 34835, 21267, 102409, 282867, 26643, 59395, 26643, 349203, 381971, 545811, 583707, 4827155, 4477971, 1725495, 1707319, 236595, 1453348, 223506, 16402, 2066] checked32 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old32 n]
 rfl
def trace33 : List Nat := [131118, 16414, 26, 26, 32910, 443, 131470, 131470, 826, 131854, 34382, 17555, 33935, 18003, 50313, 18387, 52363, 60547, 26451, 107657, 287859, 281811, 314499, 281171, 353939, 386707, 804435, 838811, 5082259, 4482643, 5928055, 5975351, 4365875, 1453540, 223698, 16594, 14354]
theorem checked33 : checkTrace blocks trace33=true := by decide +kernel
theorem old33 : phaseClean508 reference 131118=some 14354 := by decide +kernel
theorem row33 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131118⟩=run reference n ⟨false,tbN_t8 131118⟩ := by
 have h:=trace_sound blocks 131118 [16414, 26, 26, 32910, 443, 131470, 131470, 826, 131854, 34382, 17555, 33935, 18003, 50313, 18387, 52363, 60547, 26451, 107657, 287859, 281811, 314499, 281171, 353939, 386707, 804435, 838811, 5082259, 4482643, 5928055, 5975351, 4365875, 1453540, 223698, 16594, 14354] checked33 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old33 n]
 rfl
def trace34 : List Nat := [47, 15, 29, 19, 15, 287, 271, 271, 535, 687, 33807, 17435, 50187, 17435, 50190, 17435, 51203, 51211, 17179, 114697, 278779, 18459, 575495, 542747, 869403, 902171, 1590299, 1624083, 1673243, 1328155, 4482139, 1601855, 4313787, 1338669, 92438, 16401, 2321]
theorem checked34 : checkTrace blocks trace34=true := by decide +kernel
theorem old34 : phaseClean508 reference 47=some 2321 := by decide +kernel
theorem row34 (m n : List Bool) : run candidate m ⟨false,tbN_t8 47⟩=run reference n ⟨false,tbN_t8 47⟩ := by
 have h:=trace_sound blocks 47 [15, 29, 19, 15, 287, 271, 271, 535, 687, 33807, 17435, 50187, 17435, 50190, 17435, 51203, 51211, 17179, 114697, 278779, 18459, 575495, 542747, 869403, 902171, 1590299, 1624083, 1673243, 1328155, 4482139, 1601855, 4313787, 1338669, 92438, 16401, 2321] checked34 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old34 n]
 rfl
def trace35 : List Nat := [131119, 16447, 63, 59, 32815, 383, 131375, 131375, 635, 131727, 33999, 17819, 50571, 17627, 50572, 17627, 35227, 35227, 17371, 115081, 278907, 18907, 575879, 542939, 869787, 902555, 1590491, 1624467, 1673627, 1328347, 4482203, 1602047, 4379355, 1567772, 108822, 49201, 2417]
theorem checked35 : checkTrace blocks trace35=true := by decide +kernel
theorem old35 : phaseClean508 reference 131119=some 2417 := by decide +kernel
theorem row35 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131119⟩=run reference n ⟨false,tbN_t8 131119⟩ := by
 have h:=trace_sound blocks 131119 [16447, 63, 59, 32815, 383, 131375, 131375, 635, 131727, 33999, 17819, 50571, 17627, 50572, 17627, 35227, 35227, 17371, 115081, 278907, 18907, 575879, 542939, 869787, 902555, 1590491, 1624467, 1673627, 1328347, 4482203, 1602047, 4379355, 1567772, 108822, 49201, 2417] checked35 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old35 n]
 rfl
def trace36 : List Nat := [44, 12, 16, 16, 12, 275, 268, 268, 532, 684, 33804, 17411, 33795, 17411, 33801, 17411, 51227, 51219, 17155, 65542, 16611, 18595, 34819, 17411, 82947, 115715, 17411, 34819, 100355, 17411, 17411, 5849383, 53283, 1338741, 26635, 16404, 2324]
theorem checked36 : checkTrace blocks trace36=true := by decide +kernel
theorem old36 : phaseClean508 reference 44=some 2324 := by decide +kernel
theorem row36 (m n : List Bool) : run candidate m ⟨false,tbN_t8 44⟩=run reference n ⟨false,tbN_t8 44⟩ := by
 have h:=trace_sound blocks 44 [12, 16, 16, 12, 275, 268, 268, 532, 684, 33804, 17411, 33795, 17411, 33801, 17411, 51227, 51219, 17155, 65542, 16611, 18595, 34819, 17411, 82947, 115715, 17411, 34819, 100355, 17411, 17411, 5849383, 53283, 1338741, 26635, 16404, 2324] checked36 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old36 n]
 rfl
def trace37 : List Nat := [131116, 16412, 18, 24, 32780, 307, 131340, 131340, 564, 131756, 33868, 148635, 33931, 17475, 33929, 17475, 34947, 34947, 17219, 65670, 16483, 18531, 34947, 17475, 83075, 115843, 17475, 51330, 18563, 17475, 17475, 5849447, 5586951, 1396631, 92905, 196820, 14100]
theorem checked37 : checkTrace blocks trace37=true := by decide +kernel
theorem old37 : phaseClean508 reference 131116=some 14100 := by decide +kernel
theorem row37 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131116⟩=run reference n ⟨false,tbN_t8 131116⟩ := by
 have h:=trace_sound blocks 131116 [16412, 18, 24, 32780, 307, 131340, 131340, 564, 131756, 33868, 148635, 33931, 17475, 33929, 17475, 34947, 34947, 17219, 65670, 16483, 18531, 34947, 17475, 83075, 115843, 17475, 51330, 18563, 17475, 17475, 5849447, 5586951, 1396631, 92905, 196820, 14100] checked37 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old37 n]
 rfl
def trace38 : List Nat := [45, 13, 21, 17, 13, 279, 269, 269, 533, 685, 33805, 17419, 52231, 19467, 35852, 19467, 55315, 55323, 19211, 83974, 18667, 22699, 563207, 545803, 609291, 642059, 1068043, 1087499, 5347339, 5262347, 6188143, 6254894, 4379562, 1535277, 157974, 81939, 2579]
theorem checked38 : checkTrace blocks trace38=true := by decide +kernel
theorem old38 : phaseClean508 reference 45=some 2579 := by decide +kernel
theorem row38 (m n : List Bool) : run candidate m ⟨false,tbN_t8 45⟩=run reference n ⟨false,tbN_t8 45⟩ := by
 have h:=trace_sound blocks 45 [13, 21, 17, 13, 279, 269, 269, 533, 685, 33805, 17419, 52231, 19467, 35852, 19467, 55315, 55323, 19211, 83974, 18667, 22699, 563207, 545803, 609291, 642059, 1068043, 1087499, 5347339, 5262347, 6188143, 6254894, 4379562, 1535277, 157974, 81939, 2579] checked38 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old38 n]
 rfl
def trace39 : List Nat := [131117, 16445, 55, 57, 32941, 503, 131501, 131501, 885, 131885, 34509, 148883, 50575, 18123, 34188, 18251, 52627, 52635, 18379, 83334, 17771, 19819, 560519, 542411, 608139, 640907, 1066699, 1101194, 1068427, 1066699, 1401519, 5272239, 5595853, 1436957, 239639, 114735, 2671]
theorem checked39 : checkTrace blocks trace39=true := by decide +kernel
theorem old39 : phaseClean508 reference 131117=some 2671 := by decide +kernel
theorem row39 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131117⟩=run reference n ⟨false,tbN_t8 131117⟩ := by
 have h:=trace_sound blocks 131117 [16445, 55, 57, 32941, 503, 131501, 131501, 885, 131885, 34509, 148883, 50575, 18123, 34188, 18251, 52627, 52635, 18379, 83334, 17771, 19819, 560519, 542411, 608139, 640907, 1066699, 1101194, 1068427, 1066699, 1401519, 5272239, 5595853, 1436957, 239639, 114735, 2671] checked39 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old39 n]
 rfl
def trace40 : List Nat := [42, 10, 12, 22, 10, 9, 10, 10, 30, 10, 10, 16402, 32782, 16402, 49162, 16402, 49162, 49154, 16402, 98306, 16402, 16402, 49154, 16402, 81938, 114706, 16402, 32795, 4210706, 4210706, 4932626, 1721654, 250930, 1534069, 224523, 81942, 2582]
theorem checked40 : checkTrace blocks trace40=true := by decide +kernel
theorem old40 : phaseClean508 reference 42=some 2582 := by decide +kernel
theorem row40 (m n : List Bool) : run candidate m ⟨false,tbN_t8 42⟩=run reference n ⟨false,tbN_t8 42⟩ := by
 have h:=trace_sound blocks 42 [10, 12, 22, 10, 9, 10, 10, 30, 10, 10, 16402, 32782, 16402, 49162, 16402, 49162, 49154, 16402, 98306, 16402, 16402, 49154, 16402, 81938, 114706, 16402, 32795, 4210706, 4210706, 4932626, 1721654, 250930, 1534069, 224523, 81942, 2582] checked40 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old40 n]
 rfl
def trace41 : List Nat := [131114, 16410, 78, 94, 32842, 299, 131402, 131402, 690, 132842, 49474, 148108, 33436, 16724, 49808, 16980, 33428, 33428, 16724, 98970, 17012, 17012, 49816, 16724, 65684, 65684, 16724, 49820, 98964, 16724, 16724, 16724, 6213648, 749207, 2051049, 196822, 13846]
theorem checked41 : checkTrace blocks trace41=true := by decide +kernel
theorem old41 : phaseClean508 reference 131114=some 13846 := by decide +kernel
theorem row41 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131114⟩=run reference n ⟨false,tbN_t8 131114⟩ := by
 have h:=trace_sound blocks 131114 [16410, 78, 94, 32842, 299, 131402, 131402, 690, 132842, 49474, 148108, 33436, 16724, 49808, 16980, 33428, 33428, 16724, 98970, 17012, 17012, 49816, 16724, 65684, 65684, 16724, 49820, 98964, 16724, 16724, 16724, 6213648, 749207, 2051049, 196822, 13846] checked41 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old41 n]
 rfl
def trace42 : List Nat := [43, 11, 9, 23, 11, 13, 11, 11, 31, 11, 11, 16410, 49162, 16410, 49167, 20506, 32794, 32794, 20506, 118786, 20506, 24602, 581638, 548890, 610330, 643098, 1069082, 1089555, 1073178, 1069082, 1406078, 1587518, 4299450, 1386620, 93455, 81941, 2837]
theorem checked42 : checkTrace blocks trace42=true := by decide +kernel
theorem old42 : phaseClean508 reference 43=some 2837 := by decide +kernel
theorem row42 (m n : List Bool) : run candidate m ⟨false,tbN_t8 43⟩=run reference n ⟨false,tbN_t8 43⟩ := by
 have h:=trace_sound blocks 43 [11, 9, 23, 11, 13, 11, 11, 31, 11, 11, 16410, 49162, 16410, 49167, 20506, 32794, 32794, 20506, 118786, 20506, 24602, 581638, 548890, 610330, 643098, 1069082, 1089555, 1073178, 1069082, 1406078, 1587518, 4299450, 1386620, 93455, 81941, 2837] checked42 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old42 n]
 rfl
def trace43 : List Nat := [131115, 16443, 107, 127, 33003, 495, 131563, 131563, 1011, 132971, 50115, 148356, 50072, 17372, 50069, 16732, 51076, 51084, 17884, 116634, 18300, 18300, 575388, 541660, 590748, 590748, 1065948, 1099668, 1148828, 1065948, 1402808, 619164, 6222554, 773149, 1935639, 114733, 2925]
theorem checked43 : checkTrace blocks trace43=true := by decide +kernel
theorem old43 : phaseClean508 reference 131115=some 2925 := by decide +kernel
theorem row43 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131115⟩=run reference n ⟨false,tbN_t8 131115⟩ := by
 have h:=trace_sound blocks 131115 [16443, 107, 127, 33003, 495, 131563, 131563, 1011, 132971, 50115, 148356, 50072, 17372, 50069, 16732, 51076, 51084, 17884, 116634, 18300, 18300, 575388, 541660, 590748, 590748, 1065948, 1099668, 1148828, 1065948, 1402808, 619164, 6222554, 773149, 1935639, 114733, 2925] checked43 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old43 n]
 rfl
def trace44 : List Nat := [40, 8, 4, 20, 8, 1, 8, 8, 28, 8, 8, 16386, 32770, 16386, 32776, 16386, 49178, 49170, 16386, 65549, 278530, 16546, 32770, 19458, 344066, 376834, 540674, 573443, 540674, 278530, 5325862, 540930, 213026, 150627, 27674, 81944, 2840]
theorem checked44 : checkTrace blocks trace44=true := by decide +kernel
theorem old44 : phaseClean508 reference 40=some 2840 := by decide +kernel
theorem row44 (m n : List Bool) : run candidate m ⟨false,tbN_t8 40⟩=run reference n ⟨false,tbN_t8 40⟩ := by
 have h:=trace_sound blocks 40 [8, 4, 20, 8, 1, 8, 8, 28, 8, 8, 16386, 32770, 16386, 32776, 16386, 49178, 49170, 16386, 65549, 278530, 16546, 32770, 19458, 344066, 376834, 540674, 573443, 540674, 278530, 5325862, 540930, 213026, 150627, 27674, 81944, 2840] checked44 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old44 n]
 rfl
def trace45 : List Nat := [131112, 16408, 70, 92, 32968, 419, 131528, 131528, 956, 131912, 51008, 18052, 34456, 18244, 34448, 17860, 52892, 52884, 17988, 67231, 18052, 20164, 36504, 18244, 67204, 67204, 18244, 36484, 102020, 18244, 18244, 1655328, 4911110, 2051713, 1920760, 131288, 13592]
theorem checked45 : checkTrace blocks trace45=true := by decide +kernel
theorem old45 : phaseClean508 reference 131112=some 13592 := by decide +kernel
theorem row45 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131112⟩=run reference n ⟨false,tbN_t8 131112⟩ := by
 have h:=trace_sound blocks 131112 [16408, 70, 92, 32968, 419, 131528, 131528, 956, 131912, 51008, 18052, 34456, 18244, 34448, 17860, 52892, 52884, 17988, 67231, 18052, 20164, 36504, 18244, 67204, 67204, 18244, 36484, 102020, 18244, 18244, 1655328, 4911110, 2051713, 1920760, 131288, 13592] checked45 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old45 n]
 rfl
def trace46 : List Nat := [41, 9, 1, 21, 9, 5, 9, 9, 29, 9, 9, 16394, 51206, 18442, 34829, 18442, 53266, 61466, 26634, 92173, 288778, 282794, 823302, 809994, 878602, 911370, 1853450, 1888267, 6049802, 5531658, 5201482, 6167343, 4372905, 1444478, 159501, 147479, 3095]
theorem checked46 : checkTrace blocks trace46=true := by decide +kernel
theorem old46 : phaseClean508 reference 41=some 3095 := by decide +kernel
theorem row46 (m n : List Bool) : run candidate m ⟨false,tbN_t8 41⟩=run reference n ⟨false,tbN_t8 41⟩ := by
 have h:=trace_sound blocks 41 [9, 1, 21, 9, 5, 9, 9, 29, 9, 9, 16394, 51206, 18442, 34829, 18442, 53266, 61466, 26634, 92173, 288778, 282794, 823302, 809994, 878602, 911370, 1853450, 1888267, 6049802, 5531658, 5201482, 6167343, 4372905, 1444478, 159501, 147479, 3095] checked46 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old46 n]
 rfl
def trace47 : List Nat := [131113, 16441, 99, 125, 32873, 359, 131433, 131433, 765, 131785, 50625, 18316, 51100, 17868, 34709, 18124, 35724, 43916, 25292, 91039, 25484, 281548, 822172, 804300, 599436, 599436, 1328588, 1346444, 1411980, 1074636, 5591976, 4201420, 4794574, 567886, 2067980, 180267, 3179]
theorem checked47 : checkTrace blocks trace47=true := by decide +kernel
theorem old47 : phaseClean508 reference 131113=some 3179 := by decide +kernel
theorem row47 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131113⟩=run reference n ⟨false,tbN_t8 131113⟩ := by
 have h:=trace_sound blocks 131113 [16441, 99, 125, 32873, 359, 131433, 131433, 765, 131785, 50625, 18316, 51100, 17868, 34709, 18124, 35724, 43916, 25292, 91039, 25484, 281548, 822172, 804300, 599436, 599436, 1328588, 1346444, 1411980, 1074636, 5591976, 4201420, 4794574, 567886, 2067980, 180267, 3179] checked47 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old47 n]
 rfl
def trace48 : List Nat := [38, 6, 28, 6, 6, 26, 6, 6, 6, 6, 6, 17, 13, 17, 16387, 4113, 16393, 16385, 4113, 36878, 4113, 8209, 24585, 8209, 4113, 4113, 4113, 24601, 4202513, 4198417, 4920337, 4934929, 19505, 82273, 213272, 147482, 3098]
theorem checked48 : checkTrace blocks trace48=true := by decide +kernel
theorem old48 : phaseClean508 reference 38=some 3098 := by decide +kernel
theorem row48 (m n : List Bool) : run candidate m ⟨false,tbN_t8 38⟩=run reference n ⟨false,tbN_t8 38⟩ := by
 have h:=trace_sound blocks 38 [6, 28, 6, 6, 26, 6, 6, 6, 6, 6, 17, 13, 17, 16387, 4113, 16393, 16385, 4113, 36878, 4113, 8209, 24585, 8209, 4113, 4113, 4113, 24601, 4202513, 4198417, 4920337, 4934929, 19505, 82273, 213272, 147482, 3098] checked48 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old48 n]
 rfl
def trace49 : List Nat := [131110, 16406, 94, 78, 32838, 56, 131142, 131142, 166, 131142, 16718, 131727, 671, 343, 17049, 599, 17039, 25223, 8535, 41622, 8823, 262775, 279187, 262487, 24727, 57495, 262487, 262814, 377495, 8535, 4207447, 5270387, 6122001, 1926529, 2057720, 131290, 13338]
theorem checked49 : checkTrace blocks trace49=true := by decide +kernel
theorem old49 : phaseClean508 reference 131110=some 13338 := by decide +kernel
theorem row49 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131110⟩=run reference n ⟨false,tbN_t8 131110⟩ := by
 have h:=trace_sound blocks 131110 [16406, 94, 78, 32838, 56, 131142, 131142, 166, 131142, 16718, 131727, 671, 343, 17049, 599, 17039, 25223, 8535, 41622, 8823, 262775, 279187, 262487, 24727, 57495, 262487, 262814, 377495, 8535, 4207447, 5270387, 6122001, 1926529, 2057720, 131290, 13338] checked49 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old49 n]
 rfl
def trace50 : List Nat := [39, 7, 25, 7, 7, 30, 7, 7, 7, 7, 7, 25, 16393, 25, 16390, 25, 25, 25, 25, 49166, 25, 25, 540685, 524313, 524313, 524313, 1048601, 1064977, 1048601, 1048601, 1385597, 4796697, 4326073, 196968, 82204, 147481, 3353]
theorem checked50 : checkTrace blocks trace50=true := by decide +kernel
theorem old50 : phaseClean508 reference 39=some 3353 := by decide +kernel
theorem row50 (m n : List Bool) : run candidate m ⟨false,tbN_t8 39⟩=run reference n ⟨false,tbN_t8 39⟩ := by
 have h:=trace_sound blocks 39 [7, 25, 7, 7, 30, 7, 7, 7, 7, 7, 25, 16393, 25, 16390, 25, 25, 25, 25, 49166, 25, 25, 540685, 524313, 524313, 524313, 1048601, 1064977, 1048601, 1048601, 1385597, 4796697, 4326073, 196968, 82204, 147481, 3353] checked50 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old50 n]
 rfl
def trace51 : List Nat := [131111, 16439, 123, 111, 32999, 252, 131303, 131303, 487, 131527, 17359, 131975, 17307, 991, 17308, 351, 1951, 1951, 1503, 51094, 1919, 1919, 542615, 525279, 541599, 574367, 1049567, 1050518, 1165215, 1049567, 1386427, 602783, 6206169, 688462, 1942796, 180265, 3433]
theorem checked51 : checkTrace blocks trace51=true := by decide +kernel
theorem old51 : phaseClean508 reference 131111=some 3433 := by decide +kernel
theorem row51 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131111⟩=run reference n ⟨false,tbN_t8 131111⟩ := by
 have h:=trace_sound blocks 131111 [16439, 123, 111, 32999, 252, 131303, 131303, 487, 131527, 17359, 131975, 17307, 991, 17308, 351, 1951, 1951, 1503, 51094, 1919, 1919, 542615, 525279, 541599, 574367, 1049567, 1050518, 1165215, 1049567, 1386427, 602783, 6206169, 688462, 1942796, 180265, 3433] checked51 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old51 n]
 rfl
def trace52 : List Nat := [36, 4, 20, 4, 4, 18, 4, 4, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 262145, 161, 9, 3073, 262145, 262145, 524289, 524289, 524289, 262145, 5309477, 524545, 196641, 196912, 16385, 147484, 3356]
theorem checked52 : checkTrace blocks trace52=true := by decide +kernel
theorem old52 : phaseClean508 reference 36=some 3356 := by decide +kernel
theorem row52 (m n : List Bool) : run candidate m ⟨false,tbN_t8 36⟩=run reference n ⟨false,tbN_t8 36⟩ := by
 have h:=trace_sound blocks 36 [4, 20, 4, 4, 18, 4, 4, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 262145, 161, 9, 3073, 262145, 262145, 524289, 524289, 524289, 262145, 5309477, 524545, 196641, 196912, 16385, 147484, 3356] checked52 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old52 n]
 rfl
def trace53 : List Nat := [131108, 16404, 86, 76, 32964, 176, 131268, 131268, 424, 132580, 18252, 1671, 1691, 1863, 1689, 1479, 3719, 3719, 1607, 1683, 1671, 3783, 3731, 1863, 18055, 50823, 1863, 20102, 118407, 1863, 1863, 1638947, 4894725, 1967058, 1925859, 65756, 13084]
theorem checked53 : checkTrace blocks trace53=true := by decide +kernel
theorem old53 : phaseClean508 reference 131108=some 13084 := by decide +kernel
theorem row53 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131108⟩=run reference n ⟨false,tbN_t8 131108⟩ := by
 have h:=trace_sound blocks 131108 [16404, 86, 76, 32964, 176, 131268, 131268, 424, 132580, 18252, 1671, 1691, 1863, 1689, 1479, 3719, 3719, 1607, 1683, 1671, 3783, 3731, 1863, 18055, 50823, 1863, 20102, 118407, 1863, 1863, 1638947, 4894725, 1967058, 1925859, 65756, 13084] checked53 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old53 n]
 rfl
def trace54 : List Nat := [37, 5, 17, 5, 5, 22, 5, 5, 5, 5, 5, 9, 18437, 2057, 2052, 2057, 4105, 4105, 2057, 18433, 264201, 4265, 528397, 531465, 788489, 788489, 1574921, 1576969, 5771273, 5507081, 994377, 930056, 4260776, 360, 147740, 213019, 3611]
theorem checked54 : checkTrace blocks trace54=true := by decide +kernel
theorem old54 : phaseClean508 reference 37=some 3611 := by decide +kernel
theorem row54 (m n : List Bool) : run candidate m ⟨false,tbN_t8 37⟩=run reference n ⟨false,tbN_t8 37⟩ := by
 have h:=trace_sound blocks 37 [5, 17, 5, 5, 22, 5, 5, 5, 5, 5, 9, 18437, 2057, 2052, 2057, 4105, 4105, 2057, 18433, 264201, 4265, 528397, 531465, 788489, 788489, 1574921, 1576969, 5771273, 5507081, 994377, 930056, 4260776, 360, 147740, 213019, 3611] checked54 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old54 n]
 rfl
def trace55 : List Nat := [131109, 16437, 115, 109, 32869, 116, 131173, 131173, 233, 132197, 17869, 1935, 18335, 1487, 1948, 1743, 19351, 19359, 719, 17299, 911, 3023, 527255, 525775, 542095, 574863, 1050063, 1067918, 1166223, 1050063, 1384875, 1061355, 4887247, 2007384, 2072605, 245799, 3687]
theorem checked55 : checkTrace blocks trace55=true := by decide +kernel
theorem old55 : phaseClean508 reference 131109=some 3687 := by decide +kernel
theorem row55 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131109⟩=run reference n ⟨false,tbN_t8 131109⟩ := by
 have h:=trace_sound blocks 131109 [16437, 115, 109, 32869, 116, 131173, 131173, 233, 132197, 17869, 1935, 18335, 1487, 1948, 1743, 19351, 19359, 719, 17299, 911, 3023, 527255, 525775, 542095, 574863, 1050063, 1067918, 1166223, 1050063, 1384875, 1061355, 4887247, 2007384, 2072605, 245799, 3687] checked55 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old55 n]
 rfl
def trace56 : List Nat := [34, 2, 8, 2, 2, 8, 2, 2, 2, 1026, 1026, 1040, 1036, 1040, 17410, 1040, 2064, 2064, 784, 32773, 262384, 2064, 18440, 2064, 263184, 263184, 525328, 526361, 4835344, 4457488, 1705012, 4916496, 1072, 1072, 214273, 213022, 3614]
theorem checked56 : checkTrace blocks trace56=true := by decide +kernel
theorem old56 : phaseClean508 reference 34=some 3614 := by decide +kernel
theorem row56 (m n : List Bool) : run candidate m ⟨false,tbN_t8 34⟩=run reference n ⟨false,tbN_t8 34⟩ := by
 have h:=trace_sound blocks 34 [2, 8, 2, 2, 8, 2, 2, 2, 1026, 1026, 1040, 1036, 1040, 17410, 1040, 2064, 2064, 784, 32773, 262384, 2064, 18440, 2064, 263184, 263184, 525328, 526361, 4835344, 4457488, 1705012, 4916496, 1072, 1072, 214273, 213022, 3614] checked56 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old56 n]
 rfl
def trace57 : List Nat := [131106, 16402, 10, 10, 32898, 168, 131202, 131202, 302, 131490, 578, 144, 140, 592, 16512, 976, 1168, 1168, 1104, 33935, 1168, 1232, 17544, 592, 656, 656, 592, 17560, 1168, 592, 592, 4194832, 4268050, 8914, 213987, 65758, 12830]
theorem checked57 : checkTrace blocks trace57=true := by decide +kernel
theorem old57 : phaseClean508 reference 131106=some 12830 := by decide +kernel
theorem row57 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131106⟩=run reference n ⟨false,tbN_t8 131106⟩ := by
 have h:=trace_sound blocks 131106 [16402, 10, 10, 32898, 168, 131202, 131202, 302, 131490, 578, 144, 140, 592, 16512, 976, 1168, 1168, 1104, 33935, 1168, 1232, 17544, 592, 656, 656, 592, 17560, 1168, 592, 592, 4194832, 4268050, 8914, 213987, 65758, 12830] checked57 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old57 n]
 rfl
def trace58 : List Nat := [35, 3, 13, 3, 3, 12, 3, 3, 3, 1027, 1027, 1048, 17416, 1048, 17415, 5144, 18432, 18440, 4888, 53253, 266488, 10264, 550924, 534552, 791576, 791576, 1578008, 1583121, 1697816, 1315864, 4469848, 4815128, 4344504, 148537, 83205, 213021, 3869]
theorem checked58 : checkTrace blocks trace58=true := by decide +kernel
theorem old58 : phaseClean508 reference 35=some 3869 := by decide +kernel
theorem row58 (m n : List Bool) : run candidate m ⟨false,tbN_t8 35⟩=run reference n ⟨false,tbN_t8 35⟩ := by
 have h:=trace_sound blocks 35 [3, 13, 3, 3, 12, 3, 3, 3, 1027, 1027, 1048, 17416, 1048, 17415, 5144, 18432, 18440, 4888, 53253, 266488, 10264, 550924, 534552, 791576, 791576, 1578008, 1583121, 1697816, 1315864, 4469848, 4815128, 4344504, 148537, 83205, 213021, 3869] checked58 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old58 n]
 rfl
def trace59 : List Nat := [131107, 16435, 47, 43, 32803, 108, 131107, 131107, 111, 131107, 195, 408, 16776, 216, 16773, 216, 16768, 16776, 216, 49551, 408, 472, 541068, 524504, 524696, 524696, 1048792, 1065360, 1048984, 1048792, 1385660, 4796888, 4260568, 32856, 98589, 245797, 3941]
theorem checked59 : checkTrace blocks trace59=true := by decide +kernel
theorem old59 : phaseClean508 reference 131107=some 3941 := by decide +kernel
theorem row59 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131107⟩=run reference n ⟨false,tbN_t8 131107⟩ := by
 have h:=trace_sound blocks 131107 [16435, 47, 43, 32803, 108, 131107, 131107, 111, 131107, 195, 408, 16776, 216, 16773, 216, 16768, 16776, 216, 49551, 408, 472, 541068, 524504, 524696, 524696, 1048792, 1065360, 1048984, 1048792, 1385660, 4796888, 4260568, 32856, 98589, 245797, 3941] checked59 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old59 n]
 rfl
def trace60 : List Nat := [32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 213024, 3872]
theorem checked60 : checkTrace blocks trace60=true := by decide +kernel
theorem old60 : phaseClean508 reference 32=some 3872 := by decide +kernel
theorem row60 (m n : List Bool) : run candidate m ⟨false,tbN_t8 32⟩=run reference n ⟨false,tbN_t8 32⟩ := by
 have h:=trace_sound blocks 32 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 213024, 3872] checked60 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old60 n]
 rfl
def trace61 : List Nat := [131104, 16400, 2, 8, 32768, 32, 131072, 131072, 32, 131072, 64, 131224, 136, 64, 128, 64, 16536, 16528, 64, 128, 128, 192, 128, 64, 128, 128, 64, 16513, 114816, 64, 64, 64, 5607460, 74466, 66274, 224, 12576]
theorem checked61 : checkTrace blocks trace61=true := by decide +kernel
theorem old61 : phaseClean508 reference 131104=some 12576 := by decide +kernel
theorem row61 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131104⟩=run reference n ⟨false,tbN_t8 131104⟩ := by
 have h:=trace_sound blocks 131104 [16400, 2, 8, 32768, 32, 131072, 131072, 32, 131072, 64, 131224, 136, 64, 128, 64, 16536, 16528, 64, 128, 128, 192, 128, 64, 128, 128, 64, 16513, 114816, 64, 64, 64, 5607460, 74466, 66274, 224, 12576] checked61 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old61 n]
 rfl
def trace62 : List Nat := [33, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 8, 18436, 2056, 2053, 2056, 4104, 12296, 10248, 26624, 10248, 266248, 266244, 266248, 10248, 10248, 264200, 266248, 266248, 10248, 4209160, 355849, 28427, 90715, 148327, 95, 4127]
theorem checked62 : checkTrace blocks trace62=true := by decide +kernel
theorem old62 : phaseClean508 reference 33=some 4127 := by decide +kernel
theorem row62 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33⟩=run reference n ⟨false,tbN_t8 33⟩ := by
 have h:=trace_sound blocks 33 [1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 8, 18436, 2056, 2053, 2056, 4104, 12296, 10248, 26624, 10248, 266248, 266244, 266248, 10248, 10248, 264200, 266248, 266248, 10248, 4209160, 355849, 28427, 90715, 148327, 95, 4127] checked62 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old62 n]
 rfl
def trace63 : List Nat := [131105, 16433, 39, 41, 32929, 228, 131233, 131233, 353, 131457, 705, 131472, 16780, 712, 389, 840, 1416, 9608, 9416, 25984, 9608, 263624, 263556, 262856, 9096, 9096, 262856, 279945, 4572552, 4203208, 734408, 683400, 1564268, 254571, 229990, 32867, 4195]
theorem checked63 : checkTrace blocks trace63=true := by decide +kernel
theorem old63 : phaseClean508 reference 131105=some 4195 := by decide +kernel
theorem row63 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131105⟩=run reference n ⟨false,tbN_t8 131105⟩ := by
 have h:=trace_sound blocks 131105 [16433, 39, 41, 32929, 228, 131233, 131233, 353, 131457, 705, 131472, 16780, 712, 389, 840, 1416, 9608, 9416, 25984, 9608, 263624, 263556, 262856, 9096, 9096, 262856, 279945, 4572552, 4203208, 734408, 683400, 1564268, 254571, 229990, 32867, 4195] checked63 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old63 n]
 rfl
def trace64 : List Nat := [49432, 114696, 114758, 114772, 114776, 114947, 115032, 98640, 115344, 49912, 247056, 247332, 230968, 247044, 230962, 247300, 248380, 248372, 246276, 197178, 246276, 248324, 231992, 247044, 230432, 230432, 247044, 248357, 215588, 247044, 247044, 5947424, 4739076, 4808020, 6117418, 8, 264]
theorem checked64 : checkTrace blocks trace64=true := by decide +kernel
theorem old64 : phaseClean508 reference 49432=some 264 := by decide +kernel
theorem row64 (m n : List Bool) : run candidate m ⟨false,tbN_t8 49432⟩=run reference n ⟨false,tbN_t8 49432⟩ := by
 have h:=trace_sound blocks 49432 [114696, 114758, 114772, 114776, 114947, 115032, 98640, 115344, 49912, 247056, 247332, 230968, 247044, 230962, 247300, 248380, 248372, 246276, 197178, 246276, 248324, 231992, 247044, 230432, 230432, 247044, 248357, 215588, 247044, 247044, 5947424, 4739076, 4808020, 6117418, 8, 264] checked64 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old64 n]
 rfl
def trace65 : List Nat := [16664, 32792, 49156, 49180, 16536, 49539, 33176, 49536, 49936, 17176, 99864, 115742, 230418, 116230, 230426, 116614, 248862, 248854, 116486, 197650, 115942, 117926, 232466, 116230, 198182, 1246758, 385542, 232454, 166918, 639494, 1294882, 5489250, 1433632, 4218806, 5536456, 213192, 16136]
theorem checked65 : checkTrace blocks trace65=true := by decide +kernel
theorem old65 : phaseClean508 reference 16664=some 16136 := by decide +kernel
theorem row65 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16664⟩=run reference n ⟨false,tbN_t8 16664⟩ := by
 have h:=trace_sound blocks 16664 [32792, 49156, 49180, 16536, 49539, 33176, 49536, 49936, 17176, 99864, 115742, 230418, 116230, 230426, 116614, 248862, 248854, 116486, 197650, 115942, 117926, 232466, 116230, 198182, 1246758, 385542, 232454, 166918, 639494, 1294882, 5489250, 1433632, 4218806, 5536456, 213192, 16136] checked65 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old65 n]
 rfl
def trace66 : List Nat := [49433, 114697, 114755, 114773, 114777, 114951, 115033, 98641, 115345, 49913, 247057, 247340, 247356, 247052, 230967, 251404, 231980, 240172, 258572, 225850, 258572, 518668, 1026620, 1041676, 767016, 767016, 1561868, 1567277, 5728812, 5502220, 1951592, 579084, 648334, 6052632, 6248996, 131075, 1027]
theorem checked66 : checkTrace blocks trace66=true := by decide +kernel
theorem old66 : phaseClean508 reference 49433=some 1027 := by decide +kernel
theorem row66 (m n : List Bool) : run candidate m ⟨false,tbN_t8 49433⟩=run reference n ⟨false,tbN_t8 49433⟩ := by
 have h:=trace_sound blocks 49433 [114697, 114755, 114773, 114777, 114951, 115033, 98641, 115345, 49913, 247057, 247340, 247356, 247052, 230967, 251404, 231980, 240172, 258572, 225850, 258572, 518668, 1026620, 1041676, 767016, 767016, 1561868, 1567277, 5728812, 5502220, 1951592, 579084, 648334, 6052632, 6248996, 131075, 1027] checked66 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old66 n]
 rfl
def trace67 : List Nat := [16665, 32825, 49185, 49213, 16441, 49479, 33081, 49441, 49745, 17049, 99481, 115990, 249110, 117902, 232735, 121998, 252182, 260382, 129934, 227602, 129518, 391598, 1030422, 914574, 736558, 1785134, 1177742, 1554702, 1489166, 1702030, 4640462, 972687, 1471977, 5700392, 5684005, 163903, 1151]
theorem checked67 : checkTrace blocks trace67=true := by decide +kernel
theorem old67 : phaseClean508 reference 16665=some 1151 := by decide +kernel
theorem row67 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16665⟩=run reference n ⟨false,tbN_t8 16665⟩ := by
 have h:=trace_sound blocks 16665 [32825, 49185, 49213, 16441, 49479, 33081, 49441, 49745, 17049, 99481, 115990, 249110, 117902, 232735, 121998, 252182, 260382, 129934, 227602, 129518, 391598, 1030422, 914574, 736558, 1785134, 1177742, 1554702, 1489166, 1702030, 4640462, 972687, 1471977, 5700392, 5684005, 163903, 1151] checked67 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old67 n]
 rfl
def trace68 : List Nat := [98578, 212994, 213000, 212994, 196626, 213002, 65554, 81930, 212994, 99346, 148538, 164970, 68710, 166962, 85096, 166962, 71794, 79986, 174898, 43106, 174290, 432274, 350306, 431154, 158802, 191570, 429106, 333947, 4511858, 4369458, 637490, 4516403, 1276693, 1210196, 422442, 65546, 522]
theorem checked68 : checkTrace blocks trace68=true := by decide +kernel
theorem old68 : phaseClean508 reference 98578=some 522 := by decide +kernel
theorem row68 (m n : List Bool) : run candidate m ⟨false,tbN_t8 98578⟩=run reference n ⟨false,tbN_t8 98578⟩ := by
 have h:=trace_sound blocks 98578 [212994, 213000, 212994, 196626, 213002, 65554, 81930, 212994, 99346, 148538, 164970, 68710, 166962, 85096, 166962, 71794, 79986, 174898, 43106, 174290, 432274, 350306, 431154, 158802, 191570, 429106, 333947, 4511858, 4369458, 637490, 4516403, 1276693, 1210196, 422442, 65546, 522] checked68 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old68 n]
 rfl
def trace69 : List Nat := [33042, 65554, 81930, 81930, 98450, 82058, 82066, 66202, 82190, 33042, 147994, 163882, 67622, 166418, 84010, 166802, 70706, 78898, 175122, 44066, 175122, 431122, 349218, 430610, 158226, 190994, 428562, 349242, 332850, 174610, 4372498, 4713555, 5660471, 1462710, 160968, 213194, 15882]
theorem checked69 : checkTrace blocks trace69=true := by decide +kernel
theorem old69 : phaseClean508 reference 33042=some 15882 := by decide +kernel
theorem row69 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33042⟩=run reference n ⟨false,tbN_t8 33042⟩ := by
 have h:=trace_sound blocks 33042 [65554, 81930, 81930, 98450, 82058, 82066, 66202, 82190, 33042, 147994, 163882, 67622, 166418, 84010, 166802, 70706, 78898, 175122, 44066, 175122, 431122, 349218, 430610, 158226, 190994, 428562, 349242, 332850, 174610, 4372498, 4713555, 5660471, 1462710, 160968, 213194, 15882] checked69 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old69 n]
 rfl
def trace70 : List Nat := [98579, 212995, 213005, 212995, 196627, 213006, 65555, 81931, 212995, 99347, 148539, 164962, 83042, 164922, 83053, 164922, 67706, 67706, 164666, 49250, 164058, 166042, 608358, 689210, 672858, 705626, 1213498, 1116275, 1099898, 1213498, 1548382, 1224734, 5407390, 405833, 291133, 131077, 1285]
theorem checked70 : checkTrace blocks trace70=true := by decide +kernel
theorem old70 : phaseClean508 reference 98579=some 1285 := by decide +kernel
theorem row70 (m n : List Bool) : run candidate m ⟨false,tbN_t8 98579⟩=run reference n ⟨false,tbN_t8 98579⟩ := by
 have h:=trace_sound blocks 98579 [212995, 213005, 212995, 196627, 213006, 65555, 81931, 212995, 99347, 148539, 164962, 83042, 164922, 83053, 164922, 67706, 67706, 164666, 49250, 164058, 166042, 608358, 689210, 672858, 705626, 1213498, 1116275, 1099898, 1213498, 1548382, 1224734, 5407390, 405833, 291133, 131077, 1285] checked70 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old70 n]
 rfl
def trace71 : List Nat := [33043, 65587, 81967, 81963, 98355, 81998, 81971, 66107, 81999, 32915, 147611, 164130, 82210, 163994, 82223, 168090, 65850, 65850, 168090, 53538, 168218, 172314, 614694, 696474, 676122, 708890, 1216666, 1138994, 1122618, 1216666, 1553662, 1767870, 5622526, 62760, 46373, 163901, 1405]
theorem checked71 : checkTrace blocks trace71=true := by decide +kernel
theorem old71 : phaseClean508 reference 33043=some 1405 := by decide +kernel
theorem row71 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33043⟩=run reference n ⟨false,tbN_t8 33043⟩ := by
 have h:=trace_sound blocks 33043 [65587, 81967, 81963, 98355, 81998, 81971, 66107, 81999, 32915, 147611, 164130, 82210, 163994, 82223, 168090, 65850, 65850, 168090, 53538, 168218, 172314, 614694, 696474, 676122, 708890, 1216666, 1138994, 1122618, 1216666, 1553662, 1767870, 5622526, 62760, 46373, 163901, 1405] checked71 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old71 n]
 rfl
def trace72 : List Nat := [196646, 131078, 131100, 131078, 131078, 131130, 147462, 147478, 131114, 196614, 16494, 215, 2263, 2167, 18649, 2167, 4311, 4311, 2167, 35030, 2231, 4343, 20691, 4215, 2263, 2263, 2167, 20703, 4198615, 4196471, 4918391, 5177718, 459030, 458759, 1205297, 131086, 1038]
theorem checked72 : checkTrace blocks trace72=true := by decide +kernel
theorem old72 : phaseClean508 reference 196646=some 1038 := by decide +kernel
theorem row72 (m n : List Bool) : run candidate m ⟨false,tbN_t8 196646⟩=run reference n ⟨false,tbN_t8 196646⟩ := by
 have h:=trace_sound blocks 196646 [131078, 131100, 131078, 131078, 131130, 147462, 147478, 131114, 196614, 16494, 215, 2263, 2167, 18649, 2167, 4311, 4311, 2167, 35030, 2231, 4343, 20691, 4215, 2263, 2263, 2167, 20703, 4198615, 4196471, 4918391, 5177718, 459030, 458759, 1205297, 131086, 1038] checked72 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old72 n]
 rfl
def trace73 : List Nat := [65574, 147478, 131166, 131150, 163910, 131096, 16454, 16470, 131210, 65606, 294, 131657, 2629, 2353, 19011, 6705, 4689, 12881, 14641, 47694, 15057, 275089, 291401, 274737, 30801, 63569, 268593, 275032, 389713, 14641, 4205361, 5515028, 5908278, 1778919, 934097, 147662, 15374]
theorem checked73 : checkTrace blocks trace73=true := by decide +kernel
theorem old73 : phaseClean508 reference 65574=some 15374 := by decide +kernel
theorem row73 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65574⟩=run reference n ⟨false,tbN_t8 65574⟩ := by
 have h:=trace_sound blocks 65574 [147478, 131166, 131150, 163910, 131096, 16454, 16470, 131210, 65606, 294, 131657, 2629, 2353, 19011, 6705, 4689, 12881, 14641, 47694, 15057, 275089, 291401, 274737, 30801, 63569, 268593, 275032, 389713, 14641, 4205361, 5515028, 5908278, 1778919, 934097, 147662, 15374] checked73 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old73 n]
 rfl
def trace74 : List Nat := [196647, 131079, 131097, 131079, 131079, 131134, 147463, 147479, 131115, 196615, 16495, 223, 16595, 127, 16604, 127, 223, 223, 127, 49366, 191, 255, 540887, 524415, 524511, 524511, 1048703, 1065175, 1048799, 1048703, 1385499, 4796799, 4522655, 262239, 1074476, 196617, 1801]
theorem checked74 : checkTrace blocks trace74=true := by decide +kernel
theorem old74 : phaseClean508 reference 196647=some 1801 := by decide +kernel
theorem row74 (m n : List Bool) : run candidate m ⟨false,tbN_t8 196647⟩=run reference n ⟨false,tbN_t8 196647⟩ := by
 have h:=trace_sound blocks 196647 [131079, 131097, 131079, 131079, 131134, 147463, 147479, 131115, 196615, 16495, 223, 16595, 127, 16604, 127, 223, 223, 127, 49366, 191, 255, 540887, 524415, 524511, 524511, 1048703, 1065175, 1048799, 1048703, 1385499, 4796799, 4522655, 262239, 1074476, 196617, 1801] checked74 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old74 n]
 rfl
def trace75 : List Nat := [65575, 147511, 131195, 131183, 164071, 131292, 16615, 16631, 131531, 65991, 935, 131905, 17217, 953, 17222, 313, 1881, 1881, 1465, 51022, 2009, 1945, 542541, 525241, 541529, 574297, 1049529, 1050448, 1165145, 1049529, 1386461, 602873, 5878527, 884857, 819516, 229433, 1913]
theorem checked75 : checkTrace blocks trace75=true := by decide +kernel
theorem old75 : phaseClean508 reference 65575=some 1913 := by decide +kernel
theorem row75 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65575⟩=run reference n ⟨false,tbN_t8 65575⟩ := by
 have h:=trace_sound blocks 65575 [147511, 131195, 131183, 164071, 131292, 16615, 16631, 131531, 65991, 935, 131905, 17217, 953, 17222, 313, 1881, 1881, 1465, 51022, 2009, 1945, 542541, 525241, 541529, 574297, 1049529, 1050448, 1165145, 1049529, 1386461, 602873, 5878527, 884857, 819516, 229433, 1913] checked75 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old75 n]
 rfl
def trace76 : List Nat := [98576, 212992, 212992, 212992, 196624, 212994, 65552, 81928, 212992, 98320, 147512, 163962, 65642, 163874, 65642, 163874, 65634, 65634, 163874, 103, 163874, 163874, 65634, 163874, 147522, 180290, 163874, 65634, 65634, 163874, 163874, 163874, 1052678, 1052678, 357424, 131088, 1296]
theorem checked76 : checkTrace blocks trace76=true := by decide +kernel
theorem old76 : phaseClean508 reference 98576=some 1296 := by decide +kernel
theorem row76 (m n : List Bool) : run candidate m ⟨false,tbN_t8 98576⟩=run reference n ⟨false,tbN_t8 98576⟩ := by
 have h:=trace_sound blocks 98576 [212992, 212992, 212992, 196624, 212994, 65552, 81928, 212992, 98320, 147512, 163962, 65642, 163874, 65642, 163874, 65634, 65634, 163874, 103, 163874, 163874, 65634, 163874, 147522, 180290, 163874, 65634, 65634, 163874, 163874, 163874, 1052678, 1052678, 357424, 131088, 1296] checked76 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old76 n]
 rfl
def trace77 : List Nat := [33040, 65552, 81922, 81928, 98320, 81922, 81936, 66072, 81920, 32944, 147480, 32802, 65570, 163842, 65578, 163842, 81978, 81970, 163842, 45, 425986, 164002, 65570, 166914, 409602, 442370, 688130, 606243, 573474, 425986, 5473318, 688386, 4292642, 1389284, 30418, 82128, 15120]
theorem checked77 : checkTrace blocks trace77=true := by decide +kernel
theorem old77 : phaseClean508 reference 33040=some 15120 := by decide +kernel
theorem row77 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33040⟩=run reference n ⟨false,tbN_t8 33040⟩ := by
 have h:=trace_sound blocks 33040 [65552, 81922, 81928, 98320, 81922, 81936, 66072, 81920, 32944, 147480, 32802, 65570, 163842, 65578, 163842, 81978, 81970, 163842, 45, 425986, 164002, 65570, 166914, 409602, 442370, 688130, 606243, 573474, 425986, 5473318, 688386, 4292642, 1389284, 30418, 82128, 15120] checked77 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old77 n]
 rfl
def trace78 : List Nat := [98577, 212993, 212997, 212993, 196625, 212998, 65553, 81929, 212993, 98321, 147513, 163954, 82030, 163882, 65647, 167978, 82034, 90234, 176170, 28775, 176170, 434218, 860262, 958506, 684106, 716874, 1478698, 1384554, 1384554, 1224746, 5736014, 4887338, 5386412, 1258365, 488974, 16395, 2059]
theorem checked78 : checkTrace blocks trace78=true := by decide +kernel
theorem old78 : phaseClean508 reference 98577=some 2059 := by decide +kernel
theorem row78 (m n : List Bool) : run candidate m ⟨false,tbN_t8 98577⟩=run reference n ⟨false,tbN_t8 98577⟩ := by
 have h:=trace_sound blocks 98577 [212993, 212997, 212993, 196625, 212998, 65553, 81929, 212993, 98321, 147513, 163954, 82030, 163882, 65647, 167978, 82034, 90234, 176170, 28775, 176170, 434218, 860262, 958506, 684106, 716874, 1478698, 1384554, 1384554, 1224746, 5736014, 4887338, 5386412, 1258365, 488974, 16395, 2059] checked78 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old78 n]
 rfl
def trace79 : List Nat := [33041, 65585, 81959, 81961, 98481, 82118, 82097, 66233, 82241, 33073, 148121, 33066, 84262, 166538, 67887, 170762, 87346, 95546, 179338, 32045, 441610, 439722, 865574, 966282, 949002, 981770, 2005642, 1930539, 6092074, 5683850, 5082314, 5083595, 4293067, 1422157, 177935, 49207, 2167]
theorem checked79 : checkTrace blocks trace79=true := by decide +kernel
theorem old79 : phaseClean508 reference 33041=some 2167 := by decide +kernel
theorem row79 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33041⟩=run reference n ⟨false,tbN_t8 33041⟩ := by
 have h:=trace_sound blocks 33041 [65585, 81959, 81961, 98481, 82118, 82097, 66233, 82241, 33073, 148121, 33066, 84262, 166538, 67887, 170762, 87346, 95546, 179338, 32045, 441610, 439722, 865574, 966282, 949002, 981770, 2005642, 1930539, 6092074, 5683850, 5082314, 5083595, 4293067, 1422157, 177935, 49207, 2167] checked79 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old79 n]
 rfl
def trace80 : List Nat := [196645, 131077, 131089, 131077, 131077, 131126, 147461, 147477, 131113, 197637, 17517, 1231, 17631, 1135, 1246, 1135, 2255, 10447, 9071, 24787, 8271, 264271, 788695, 787567, 533711, 533711, 1311855, 1329358, 1427663, 1057903, 5575179, 4217455, 4614317, 419372, 1270295, 81935, 2575]
theorem checked80 : checkTrace blocks trace80=true := by decide +kernel
theorem old80 : phaseClean508 reference 196645=some 2575 := by decide +kernel
theorem row80 (m n : List Bool) : run candidate m ⟨false,tbN_t8 196645⟩=run reference n ⟨false,tbN_t8 196645⟩ := by
 have h:=trace_sound blocks 196645 [131077, 131089, 131077, 131077, 131126, 147461, 147477, 131113, 197637, 17517, 1231, 17631, 1135, 1246, 1135, 2255, 10447, 9071, 24787, 8271, 264271, 788695, 787567, 533711, 533711, 1311855, 1329358, 1427663, 1057903, 5575179, 4217455, 4614317, 419372, 1270295, 81935, 2575] checked80 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old80 n]
 rfl
def trace81 : List Nat := [65573, 147509, 131187, 131181, 163941, 131156, 16485, 16501, 131269, 65637, 421, 841, 19269, 2473, 2886, 2729, 21329, 29529, 10665, 27457, 273353, 267049, 791373, 794025, 813385, 846153, 1837481, 1839945, 6034249, 5515689, 5185513, 6183564, 5110218, 1623580, 951062, 114739, 2675]
theorem checked81 : checkTrace blocks trace81=true := by decide +kernel
theorem old81 : phaseClean508 reference 65573=some 2675 := by decide +kernel
theorem row81 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65573⟩=run reference n ⟨false,tbN_t8 65573⟩ := by
 have h:=trace_sound blocks 65573 [147509, 131187, 131181, 163941, 131156, 16485, 16501, 131269, 65637, 421, 841, 19269, 2473, 2886, 2729, 21329, 29529, 10665, 27457, 273353, 267049, 791373, 794025, 813385, 846153, 1837481, 1839945, 6034249, 5515689, 5185513, 6183564, 5110218, 1623580, 951062, 114739, 2675] checked81 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old81 n]
 rfl
def trace82 : List Nat := [82196, 180228, 180310, 180292, 180308, 180242, 49236, 33372, 180360, 83188, 83260, 99935, 198227, 99623, 198233, 99879, 199239, 199239, 98855, 131670, 98855, 100903, 199251, 99623, 132199, 132199, 99623, 199239, 199239, 99623, 99623, 5799939, 5799939, 5058565, 5796915, 12, 268]
theorem checked82 : checkTrace blocks trace82=true := by decide +kernel
theorem old82 : phaseClean508 reference 82196=some 268 := by decide +kernel
theorem row82 (m n : List Bool) : run candidate m ⟨false,tbN_t8 82196⟩=run reference n ⟨false,tbN_t8 82196⟩ := by
 have h:=trace_sound blocks 82196 [180228, 180310, 180292, 180308, 180242, 49236, 33372, 180360, 83188, 83260, 99935, 198227, 99623, 198233, 99879, 199239, 199239, 98855, 131670, 98855, 100903, 199251, 99623, 132199, 132199, 99623, 199239, 199239, 99623, 99623, 5799939, 5799939, 5058565, 5796915, 12, 268] checked82 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old82 n]
 rfl
def trace83 : List Nat := [16660, 32788, 49172, 49164, 16532, 49296, 32916, 49292, 49412, 16820, 66068, 98329, 196617, 98817, 196609, 99201, 197633, 197633, 99329, 132110, 99329, 99329, 197641, 98817, 148001, 180769, 98817, 214016, 181249, 98817, 98817, 4293185, 1388583, 5518055, 4282065, 213196, 16140]
theorem checked83 : checkTrace blocks trace83=true := by decide +kernel
theorem old83 : phaseClean508 reference 16660=some 16140 := by decide +kernel
theorem row83 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16660⟩=run reference n ⟨false,tbN_t8 16660⟩ := by
 have h:=trace_sound blocks 16660 [32788, 49172, 49164, 16532, 49296, 32916, 49292, 49412, 16820, 66068, 98329, 196617, 98817, 196609, 99201, 197633, 197633, 99329, 132110, 99329, 99329, 197641, 98817, 148001, 180769, 98817, 214016, 181249, 98817, 98817, 4293185, 1388583, 5518055, 4282065, 213196, 16140] checked83 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old83 n]
 rfl
def trace84 : List Nat := [82197, 180229, 180307, 180293, 180309, 180246, 49237, 33373, 180361, 83189, 83261, 99927, 216663, 101679, 200284, 101935, 203343, 211535, 109103, 158294, 109103, 367151, 989783, 890159, 666735, 666735, 1412399, 1514063, 5708367, 5352751, 2072395, 973358, 1669512, 5862936, 5928740, 196611, 1539]
theorem checked84 : checkTrace blocks trace84=true := by decide +kernel
theorem old84 : phaseClean508 reference 82197=some 1539 := by decide +kernel
theorem row84 (m n : List Bool) : run candidate m ⟨false,tbN_t8 82197⟩=run reference n ⟨false,tbN_t8 82197⟩ := by
 have h:=trace_sound blocks 82197 [180229, 180307, 180293, 180309, 180246, 49237, 33373, 180361, 83189, 83261, 99927, 216663, 101679, 200284, 101935, 203343, 211535, 109103, 158294, 109103, 367151, 989783, 890159, 666735, 666735, 1412399, 1514063, 5708367, 5352751, 2072395, 973358, 1669512, 5862936, 5928740, 196611, 1539] checked84 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old84 n]
 rfl
def trace85 : List Nat := [16661, 32821, 49201, 49197, 16437, 49236, 32821, 49197, 49221, 16437, 65685, 98577, 213261, 98441, 196868, 98441, 213265, 221465, 106633, 155918, 106761, 360713, 983309, 884873, 680233, 713001, 1409161, 1523976, 1491209, 1155209, 5543661, 1629101, 1501423, 4445736, 4429349, 229439, 1663]
theorem checked85 : checkTrace blocks trace85=true := by decide +kernel
theorem old85 : phaseClean508 reference 16661=some 1663 := by decide +kernel
theorem row85 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16661⟩=run reference n ⟨false,tbN_t8 16661⟩ := by
 have h:=trace_sound blocks 16661 [32821, 49201, 49197, 16437, 49236, 32821, 49197, 49221, 16437, 65685, 98577, 213261, 98441, 196868, 98441, 213265, 221465, 106633, 155918, 106761, 360713, 983309, 884873, 680233, 713001, 1409161, 1523976, 1491209, 1155209, 5543661, 1629101, 1501423, 4445736, 4429349, 229439, 1663] checked85 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old85 n]
 rfl
def trace86 : List Nat := [163883, 65547, 65545, 65559, 65547, 65839, 213259, 213787, 66099, 165387, 180291, 147620, 49336, 147548, 49335, 151644, 32956, 32956, 151644, 118970, 151708, 155868, 581820, 680028, 626840, 626840, 1200220, 1089717, 1073340, 1200220, 1537080, 1718648, 5638808, 1509705, 1395005, 196613, 1797]
theorem checked86 : checkTrace blocks trace86=true := by decide +kernel
theorem old86 : phaseClean508 reference 163883=some 1797 := by decide +kernel
theorem row86 (m n : List Bool) : run candidate m ⟨false,tbN_t8 163883⟩=run reference n ⟨false,tbN_t8 163883⟩ := by
 have h:=trace_sound blocks 163883 [65547, 65545, 65559, 65547, 65839, 213259, 213787, 66099, 165387, 180291, 147620, 49336, 147548, 49335, 151644, 32956, 32956, 151644, 118970, 151708, 155868, 581820, 680028, 626840, 626840, 1200220, 1089717, 1073340, 1200220, 1537080, 1718648, 5638808, 1509705, 1395005, 196613, 1797] checked86 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old86 n]
 rfl
def trace87 : List Nat := [32811, 81979, 65643, 65663, 98539, 65741, 82155, 82683, 66015, 33131, 131979, 17210, 49962, 148378, 49965, 147738, 50978, 50986, 148890, 116514, 149498, 149434, 575270, 672666, 639774, 607006, 1196954, 1099570, 1148730, 1196954, 1533950, 750298, 4809464, 650536, 634149, 229437, 1917]
theorem checked87 : checkTrace blocks trace87=true := by decide +kernel
theorem old87 : phaseClean508 reference 32811=some 1917 := by decide +kernel
theorem row87 (m n : List Bool) : run candidate m ⟨false,tbN_t8 32811⟩=run reference n ⟨false,tbN_t8 32811⟩ := by
 have h:=trace_sound blocks 32811 [81979, 65643, 65663, 98539, 65741, 82155, 82683, 66015, 33131, 131979, 17210, 49962, 148378, 49965, 147738, 50978, 50986, 148890, 116514, 149498, 149434, 575270, 672666, 639774, 607006, 1196954, 1099570, 1148730, 1196954, 1533950, 750298, 4809464, 650536, 634149, 229437, 1917] checked87 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old87 n]
 rfl
def trace88 : List Nat := [49425, 114689, 114695, 114689, 114705, 114692, 114705, 98841, 114701, 49329, 213017, 229418, 215078, 231434, 198701, 231434, 200746, 200746, 231434, 149549, 493578, 233642, 725030, 760842, 952366, 2000942, 2075658, 1773610, 1773610, 2067466, 5614702, 6075695, 71595, 4199787, 4355359, 16391, 2055]
theorem checked88 : checkTrace blocks trace88=true := by decide +kernel
theorem old88 : phaseClean508 reference 49425=some 2055 := by decide +kernel
theorem row88 (m n : List Bool) : run candidate m ⟨false,tbN_t8 49425⟩=run reference n ⟨false,tbN_t8 49425⟩ := by
 have h:=trace_sound blocks 49425 [114689, 114695, 114689, 114705, 114692, 114705, 98841, 114701, 49329, 213017, 229418, 215078, 231434, 198701, 231434, 200746, 200746, 231434, 149549, 493578, 233642, 725030, 760842, 952366, 2000942, 2075658, 1773610, 1773610, 2067466, 5614702, 6075695, 71595, 4199787, 4355359, 16391, 2055] checked88 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old88 n]
 rfl
def trace89 : List Nat := [114961, 229425, 245797, 245801, 213169, 245956, 98481, 114857, 246093, 115089, 213689, 98674, 213358, 230058, 196973, 230186, 197994, 197994, 230570, 148839, 230698, 230698, 722278, 754346, 689006, 1737582, 1549994, 1262955, 5424490, 5998250, 5220074, 6010830, 1222348, 4625755, 4699166, 49211, 2171]
theorem checked89 : checkTrace blocks trace89=true := by decide +kernel
theorem old89 : phaseClean508 reference 114961=some 2171 := by decide +kernel
theorem row89 (m n : List Bool) : run candidate m ⟨false,tbN_t8 114961⟩=run reference n ⟨false,tbN_t8 114961⟩ := by
 have h:=trace_sound blocks 114961 [229425, 245797, 245801, 213169, 245956, 98481, 114857, 246093, 115089, 213689, 98674, 213358, 230058, 196973, 230186, 197994, 197994, 230570, 148839, 230698, 230698, 722278, 754346, 689006, 1737582, 1549994, 1262955, 5424490, 5998250, 5220074, 6010830, 1222348, 4625755, 4699166, 49211, 2171] checked89 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old89 n]
 rfl
def trace90 : List Nat := [82193, 180225, 180231, 180225, 180241, 180230, 49169, 33305, 180237, 82097, 65585, 98384, 213068, 98344, 196679, 102440, 213072, 213080, 102440, 151621, 364584, 106632, 729164, 633896, 938088, 2019432, 1946664, 1777736, 1777736, 1938472, 5747788, 5961996, 1165996, 4486458, 4674566, 16387, 2051]
theorem checked90 : checkTrace blocks trace90=true := by decide +kernel
theorem old90 : phaseClean508 reference 82193=some 2051 := by decide +kernel
theorem row90 (m n : List Bool) : run candidate m ⟨false,tbN_t8 82193⟩=run reference n ⟨false,tbN_t8 82193⟩ := by
 have h:=trace_sound blocks 82193 [180225, 180231, 180225, 180241, 180230, 49169, 33305, 180237, 82097, 65585, 98384, 213068, 98344, 196679, 102440, 213072, 213080, 102440, 151621, 364584, 106632, 729164, 633896, 938088, 2019432, 1946664, 1777736, 1777736, 1938472, 5747788, 5961996, 1165996, 4486458, 4674566, 16387, 2051] checked90 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old90 n]
 rfl
def trace91 : List Nat := [16657, 32817, 49189, 49193, 16561, 49350, 32945, 49321, 49485, 16785, 66193, 229640, 215300, 101000, 198919, 105224, 218384, 218392, 105608, 154895, 105736, 111880, 734476, 635528, 678696, 1760040, 1425032, 1275145, 5436680, 5873288, 5095112, 6159341, 162763, 4388106, 4363527, 49215, 2175]
theorem checked91 : checkTrace blocks trace91=true := by decide +kernel
theorem old91 : phaseClean508 reference 16657=some 2175 := by decide +kernel
theorem row91 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16657⟩=run reference n ⟨false,tbN_t8 16657⟩ := by
 have h:=trace_sound blocks 16657 [32817, 49189, 49193, 16561, 49350, 32945, 49321, 49485, 16785, 66193, 229640, 215300, 101000, 198919, 105224, 218384, 218392, 105608, 154895, 105736, 111880, 734476, 635528, 678696, 1760040, 1425032, 1275145, 5436680, 5873288, 5095112, 6159341, 162763, 4388106, 4363527, 49215, 2175] checked91 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old91 n]
 rfl
def trace92 : List Nat := [163875, 65539, 65549, 65539, 65539, 65582, 212995, 213011, 65583, 163843, 131139, 131232, 16544, 131160, 16549, 131160, 184, 184, 131160, 49317, 393368, 131192, 540844, 658520, 835740, 802972, 1704024, 1589424, 1573048, 1441880, 4595736, 4403288, 5673660, 139627, 16671, 16389, 2309]
theorem checked92 : checkTrace blocks trace92=true := by decide +kernel
theorem old92 : phaseClean508 reference 163875=some 2309 := by decide +kernel
theorem row92 (m n : List Bool) : run candidate m ⟨false,tbN_t8 163875⟩=run reference n ⟨false,tbN_t8 163875⟩ := by
 have h:=trace_sound blocks 163875 [65539, 65549, 65539, 65539, 65582, 212995, 213011, 65583, 163843, 131139, 131232, 16544, 131160, 16549, 131160, 184, 184, 131160, 49317, 393368, 131192, 540844, 658520, 835740, 802972, 1704024, 1589424, 1573048, 1441880, 4595736, 4403288, 5673660, 139627, 16671, 16389, 2309] checked92 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old92 n]
 rfl
def trace93 : List Nat := [32803, 81971, 65583, 65579, 98339, 65614, 81955, 81971, 65603, 33827, 132227, 132384, 17696, 132248, 17703, 136344, 2360, 2360, 136088, 53551, 135672, 141752, 551212, 664728, 578844, 546076, 1184920, 1059121, 1173816, 1184920, 1519868, 4421784, 5626588, 58634, 34055, 49213, 2429]
theorem checked93 : checkTrace blocks trace93=true := by decide +kernel
theorem old93 : phaseClean508 reference 32803=some 2429 := by decide +kernel
theorem row93 (m n : List Bool) : run candidate m ⟨false,tbN_t8 32803⟩=run reference n ⟨false,tbN_t8 32803⟩ := by
 have h:=trace_sound blocks 32803 [81971, 65583, 65579, 98339, 65614, 81955, 81971, 65603, 33827, 132227, 132384, 17696, 132248, 17703, 136344, 2360, 2360, 136088, 53551, 135672, 141752, 551212, 664728, 578844, 546076, 1184920, 1059121, 1173816, 1184920, 1519868, 4421784, 5626588, 58634, 34055, 49213, 2429] checked93 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old93 n]
 rfl
def trace94 : List Nat := [81957, 163845, 163923, 163909, 180293, 163862, 49221, 49237, 163973, 81989, 65829, 66129, 148045, 65833, 131654, 66089, 131657, 131657, 65833, 148033, 328393, 66089, 655949, 593193, 819309, 819309, 1638697, 1720904, 1819209, 1376553, 4530537, 4206889, 1675949, 5054571, 5193759, 81927, 2567]
theorem checked94 : checkTrace blocks trace94=true := by decide +kernel
theorem old94 : phaseClean508 reference 81957=some 2567 := by decide +kernel
theorem row94 (m n : List Bool) : run candidate m ⟨false,tbN_t8 81957⟩=run reference n ⟨false,tbN_t8 81957⟩ := by
 have h:=trace_sound blocks 81957 [163845, 163923, 163909, 180293, 163862, 49221, 49237, 163973, 81989, 65829, 66129, 148045, 65833, 131654, 66089, 131657, 131657, 65833, 148033, 328393, 66089, 655949, 593193, 819309, 819309, 1638697, 1720904, 1819209, 1376553, 4530537, 4206889, 1675949, 5054571, 5193759, 81927, 2567] checked94 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old94 n]
 rfl
def trace95 : List Nat := [213029, 180277, 163889, 163885, 147493, 163956, 180261, 180277, 163945, 214053, 83181, 67031, 150999, 68847, 134622, 68847, 154071, 154079, 68591, 149971, 67919, 72015, 661975, 595183, 577003, 544235, 1117423, 1186255, 5380559, 5311727, 6237323, 6173130, 1180618, 5472347, 5415198, 114747, 2683]
theorem checked95 : checkTrace blocks trace95=true := by decide +kernel
theorem old95 : phaseClean508 reference 213029=some 2683 := by decide +kernel
theorem row95 (m n : List Bool) : run candidate m ⟨false,tbN_t8 213029⟩=run reference n ⟨false,tbN_t8 213029⟩ := by
 have h:=trace_sound blocks 213029 [180277, 163889, 163885, 147493, 163956, 180261, 180277, 163945, 214053, 83181, 67031, 150999, 68847, 134622, 68847, 154071, 154079, 68591, 149971, 67919, 72015, 661975, 595183, 577003, 544235, 1117423, 1186255, 5380559, 5311727, 6237323, 6173130, 1180618, 5472347, 5415198, 114747, 2683] checked95 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old95 n]
 rfl
def trace96 : List Nat := [147501, 32781, 32791, 32785, 49165, 32821, 163853, 163853, 32821, 147469, 65613, 82071, 182423, 84047, 166044, 84047, 184471, 184479, 84047, 215190, 84111, 86223, 692375, 610383, 624811, 1673387, 1403983, 1233038, 1200271, 1657935, 419855, 5665898, 1394602, 5589050, 5662982, 81923, 2563]
theorem checked96 : checkTrace blocks trace96=true := by decide +kernel
theorem old96 : phaseClean508 reference 147501=some 2563 := by decide +kernel
theorem row96 (m n : List Bool) : run candidate m ⟨false,tbN_t8 147501⟩=run reference n ⟨false,tbN_t8 147501⟩ := by
 have h:=trace_sound blocks 147501 [32781, 32791, 32785, 49165, 32821, 163853, 163853, 32821, 147469, 65613, 82071, 182423, 84047, 166044, 84047, 184471, 184479, 84047, 215190, 84111, 86223, 692375, 610383, 624811, 1673387, 1403983, 1233038, 1200271, 1657935, 419855, 5665898, 1394602, 5589050, 5662982, 81923, 2563] checked96 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old96 n]
 rfl
def trace97 : List Nat := [16429, 49213, 32821, 32825, 16557, 32981, 32941, 32941, 33109, 16781, 66189, 213263, 180511, 82575, 164124, 82703, 181527, 181535, 83087, 214294, 83215, 83215, 689431, 606863, 623403, 1671979, 1402511, 1213711, 5473551, 5850767, 5072591, 5863403, 194253, 5752842, 5744647, 114751, 2687]
theorem checked97 : checkTrace blocks trace97=true := by decide +kernel
theorem old97 : phaseClean508 reference 16429=some 2687 := by decide +kernel
theorem row97 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16429⟩=run reference n ⟨false,tbN_t8 16429⟩ := by
 have h:=trace_sound blocks 16429 [49213, 32821, 32825, 16557, 32981, 32941, 32941, 33109, 16781, 66189, 213263, 180511, 82575, 164124, 82703, 181527, 181535, 83087, 214294, 83215, 83215, 689431, 606863, 623403, 1671979, 1402511, 1213711, 5473551, 5850767, 5072591, 5863403, 194253, 5752842, 5744647, 114751, 2687] checked97 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old97 n]
 rfl
def trace98 : List Nat := [147497, 32777, 32835, 32853, 49225, 32805, 163913, 163913, 32945, 147529, 82241, 82576, 180876, 82248, 164487, 86600, 164488, 172680, 94536, 225935, 94824, 352872, 959116, 876872, 651436, 618668, 1397064, 1483400, 1548936, 1143112, 5523244, 4805192, 1962158, 4738872, 4935172, 147459, 3075]
theorem checked98 : checkTrace blocks trace98=true := by decide +kernel
theorem old98 : phaseClean508 reference 147497=some 3075 := by decide +kernel
theorem row98 (m n : List Bool) : run candidate m ⟨false,tbN_t8 147497⟩=run reference n ⟨false,tbN_t8 147497⟩ := by
 have h:=trace_sound blocks 147497 [32777, 32835, 32853, 49225, 32805, 163913, 163913, 32945, 147529, 82241, 82576, 180876, 82248, 164487, 86600, 164488, 172680, 94536, 225935, 94824, 352872, 959116, 876872, 651436, 618668, 1397064, 1483400, 1548936, 1143112, 5523244, 4805192, 1962158, 4738872, 4935172, 147459, 3075] checked98 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old98 n]
 rfl
def trace99 : List Nat := [16425, 49209, 32801, 32829, 16425, 33095, 33065, 33065, 33361, 17033, 99465, 83222, 183574, 85134, 167199, 89230, 186646, 194846, 97166, 227613, 358894, 358670, 964886, 882830, 900394, 900394, 1924238, 2029839, 6191374, 5602446, 5130958, 5722795, 1466825, 5697288, 5680901, 180287, 3199]
theorem checked99 : checkTrace blocks trace99=true := by decide +kernel
theorem old99 : phaseClean508 reference 16425=some 3199 := by decide +kernel
theorem row99 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16425⟩=run reference n ⟨false,tbN_t8 16425⟩ := by
 have h:=trace_sound blocks 16425 [49209, 32801, 32829, 16425, 33095, 33065, 33065, 33361, 17033, 99465, 83222, 183574, 85134, 167199, 89230, 186646, 194846, 97166, 227613, 358894, 358670, 964886, 882830, 900394, 900394, 1924238, 2029839, 6191374, 5602446, 5130958, 5722795, 1466825, 5697288, 5680901, 180287, 3199] checked99 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old99 n]
 rfl
def trace100 : List Nat := [147493, 32773, 32851, 32837, 49221, 32822, 163909, 163909, 32937, 148549, 83277, 67223, 151191, 68943, 134812, 69199, 137871, 146063, 76367, 158355, 76431, 334543, 924311, 857423, 568491, 1617067, 1124687, 1464974, 1563279, 1648975, 4595471, 6250090, 1928616, 6119992, 6185732, 212995, 3587]
theorem checked100 : checkTrace blocks trace100=true := by decide +kernel
theorem old100 : phaseClean508 reference 147493=some 3587 := by decide +kernel
theorem row100 (m n : List Bool) : run candidate m ⟨false,tbN_t8 147493⟩=run reference n ⟨false,tbN_t8 147493⟩ := by
 have h:=trace_sound blocks 147493 [32773, 32851, 32837, 49221, 32822, 163909, 163909, 32937, 148549, 83277, 67223, 151191, 68943, 134812, 69199, 137871, 146063, 76367, 158355, 76431, 334543, 924311, 857423, 568491, 1617067, 1124687, 1464974, 1563279, 1648975, 4595471, 6250090, 1928616, 6119992, 6185732, 212995, 3587] checked100 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old100 n]
 rfl
def trace101 : List Nat := [16421, 49205, 32817, 32813, 16421, 32852, 32805, 32805, 32837, 16421, 65669, 65809, 147725, 65673, 131332, 65673, 147729, 155929, 73865, 155905, 336137, 328105, 917773, 855177, 844077, 1859885, 1647753, 1966345, 6160649, 6104201, 6034157, 4284041, 1506511, 4440584, 4424197, 245823, 3711]
theorem checked101 : checkTrace blocks trace101=true := by decide +kernel
theorem old101 : phaseClean508 reference 16421=some 3711 := by decide +kernel
theorem row101 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16421⟩=run reference n ⟨false,tbN_t8 16421⟩ := by
 have h:=trace_sound blocks 16421 [49205, 32817, 32813, 16421, 32852, 32805, 32805, 32837, 16421, 65669, 65809, 147725, 65673, 131332, 65673, 147729, 155929, 73865, 155905, 336137, 328105, 917773, 855177, 844077, 1859885, 1647753, 1966345, 6160649, 6104201, 6034157, 4284041, 1506511, 4440584, 4424197, 245823, 3711] checked101 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old101 n]
 rfl
def trace102 : List Nat := [147489, 32769, 32775, 32769, 49153, 32806, 163841, 163841, 32813, 147457, 65601, 65680, 147596, 65608, 131207, 69704, 147600, 147608, 69704, 151680, 69768, 73928, 139396, 73800, 53420, 20652, 69704, 155785, 4448392, 4264008, 4854856, 4869448, 5561356, 4219226, 4407398, 67, 4099]
theorem checked102 : checkTrace blocks trace102=true := by decide +kernel
theorem old102 : phaseClean508 reference 147489=some 4099 := by decide +kernel
theorem row102 (m n : List Bool) : run candidate m ⟨false,tbN_t8 147489⟩=run reference n ⟨false,tbN_t8 147489⟩ := by
 have h:=trace_sound blocks 147489 [32769, 32775, 32769, 49153, 32806, 163841, 163841, 32813, 147457, 65601, 65680, 147596, 65608, 131207, 69704, 147600, 147608, 69704, 151680, 69768, 73928, 139396, 73800, 53420, 20652, 69704, 155785, 4448392, 4264008, 4854856, 4869448, 5561356, 4219226, 4407398, 67, 4099] checked102 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old102 n]
 rfl
def trace103 : List Nat := [16417, 49201, 32805, 32809, 16545, 32966, 32929, 32929, 33101, 16769, 66177, 196872, 149764, 68232, 133383, 72456, 152848, 152856, 72840, 154880, 72968, 79112, 144644, 78472, 56108, 23340, 72328, 144648, 144648, 72328, 72328, 4542153, 4418923, 4383082, 4358503, 32895, 4223]
theorem checked103 : checkTrace blocks trace103=true := by decide +kernel
theorem old103 : phaseClean508 reference 16417=some 4223 := by decide +kernel
theorem row103 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16417⟩=run reference n ⟨false,tbN_t8 16417⟩ := by
 have h:=trace_sound blocks 16417 [49201, 32805, 32809, 16545, 32966, 32929, 32929, 33101, 16769, 66177, 196872, 149764, 68232, 133383, 72456, 152848, 152856, 72840, 154880, 72968, 79112, 144644, 78472, 56108, 23340, 72328, 144648, 144648, 72328, 72328, 4542153, 4418923, 4383082, 4358503, 32895, 4223] checked103 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old103 n]
 rfl
end ECDSAAdd.Entrant.CompactInverse14

-- Verified CompactInverseFinal
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.CompactInverse14
open Arithmetic MappedCompressed Secp256k1 History5 CompactCertificates
attribute [local irreducible] run candidate reference
def rowInputs : List Nat := [286,286,287,287,284,16668,285,16669,282,33050,283,33051,280,33048,281,33049,278,65814,279,65815,276,65812,277,65813,274,65810,275,65811,272,65808,273,65809,46,131118,47,131119,44,131116,45,131117,42,131114,43,131115,40,131112,41,131113,38,131110,39,131111,36,131108,37,131109,34,131106,35,131107,32,131104,33,131105,49432,16664,49433,16665,98578,33042,98579,33043,196646,65574,196647,65575,98576,33040,98577,33041,196645,65573,82196,16660,82197,16661,163883,32811,49425,114961,82193,16657,163875,32803,81957,213029,147501,16429,147497,16425,147493,16421,147489,16417]
theorem allRows (b : Nat) (h : b∈rowInputs) (m n : List Bool) :
 run candidate m ⟨false,tbN_t8 b⟩=run reference n ⟨false,tbN_t8 b⟩ := by
 simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at h
 rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact row0 m n
 · exact row1 m n
 · exact row2 m n
 · exact row3 m n
 · exact row4 m n
 · exact row5 m n
 · exact row6 m n
 · exact row7 m n
 · exact row8 m n
 · exact row9 m n
 · exact row10 m n
 · exact row11 m n
 · exact row12 m n
 · exact row13 m n
 · exact row14 m n
 · exact row15 m n
 · exact row16 m n
 · exact row17 m n
 · exact row18 m n
 · exact row19 m n
 · exact row20 m n
 · exact row21 m n
 · exact row22 m n
 · exact row23 m n
 · exact row24 m n
 · exact row25 m n
 · exact row26 m n
 · exact row27 m n
 · exact row28 m n
 · exact row29 m n
 · exact row30 m n
 · exact row31 m n
 · exact row32 m n
 · exact row33 m n
 · exact row34 m n
 · exact row35 m n
 · exact row36 m n
 · exact row37 m n
 · exact row38 m n
 · exact row39 m n
 · exact row40 m n
 · exact row41 m n
 · exact row42 m n
 · exact row43 m n
 · exact row44 m n
 · exact row45 m n
 · exact row46 m n
 · exact row47 m n
 · exact row48 m n
 · exact row49 m n
 · exact row50 m n
 · exact row51 m n
 · exact row52 m n
 · exact row53 m n
 · exact row54 m n
 · exact row55 m n
 · exact row56 m n
 · exact row57 m n
 · exact row58 m n
 · exact row59 m n
 · exact row60 m n
 · exact row61 m n
 · exact row62 m n
 · exact row63 m n
 · exact row64 m n
 · exact row65 m n
 · exact row66 m n
 · exact row67 m n
 · exact row68 m n
 · exact row69 m n
 · exact row70 m n
 · exact row71 m n
 · exact row72 m n
 · exact row73 m n
 · exact row74 m n
 · exact row75 m n
 · exact row76 m n
 · exact row77 m n
 · exact row78 m n
 · exact row79 m n
 · exact row80 m n
 · exact row81 m n
 · exact row82 m n
 · exact row83 m n
 · exact row84 m n
 · exact row85 m n
 · exact row86 m n
 · exact row87 m n
 · exact row88 m n
 · exact row89 m n
 · exact row90 m n
 · exact row91 m n
 · exact row92 m n
 · exact row93 m n
 · exact row94 m n
 · exact row95 m n
 · exact row96 m n
 · exact row97 m n
 · exact row98 m n
 · exact row99 m n
 · exact row100 m n
 · exact row101 m n
 · exact row102 m n
 · exact row103 m n
def localSites : List Wire := List.range 23
def sites : List Wire := MorningFour.sites ++ [530]
def postBasis (g s : Bool) (uv : Nat×Nat) : BasisState :=
 (run (MorningFour.tick507++tripF) [] ⟨false,MorningFour.pre507 g s uv.1 uv.2⟩).basis
theorem post_supp (g s : Bool) (uv : Nat×Nat) (q : Wire) (hq : q∉sites) :
 postBasis g s uv q=false := by
 have hp : wires (MorningFour.tick507++tripF)⊆sites.toFinset := by decide +kernel
 have no : q∉wires (MorningFour.tick507++tripF) := by
  intro h
  exact hq (List.mem_toFinset.mp (hp h))
 unfold postBasis
 rw [run_preserves_outside _ [] _ q no]
 apply MorningFour.pre_supp
 intro h
 exact hq (List.mem_append_left _ h)
def encodedInput (g s : Bool) (uv : Nat×Nat) : Nat :=
 encN_t8 (fun q=>postBasis g s uv (perm q)) localSites
def checkInput (uv : Nat×Nat) : Bool :=
 [false,true].all fun g=>[false,true].all fun s=>
  if Forward11Width.legal uv g then decide (encodedInput g s uv∈rowInputs) else true
theorem inputTable : MorningFour.pairs.all checkInput=true := by decide +kernel
theorem sitesTable : sites.all (fun q=>decide (perm.symm q < 23))=true := by decide +kernel
theorem sample_run (g s : Bool) (uv : Nat×Nat) (h : uv∈MorningFour.pairs)
 (hl : Forward11Width.legal uv g=true) (m n : List Bool) :
 run Inverse14Width.candidate m ⟨false,postBasis g s uv⟩=
 run (tickMR8 ++ W.ReverseCarry.compactReceiverTick base 507) n ⟨false,postBasis g s uv⟩ := by
 have ht:=inputTable
 simp only [List.all_eq_true] at ht
 have row:=ht uv h
 simp only [checkInput,List.all_eq_true] at row
 have mem:=row g (by cases g <;> simp) s (by cases s <;> simp)
 simp only [hl,if_true,decide_eq_true_eq] at mem
 have supp : ∀q : Wire,postBasis g s uv (perm q)=true → q∈localSites := by
  intro q yes
  have hg : perm q∈sites := by
   by_contra no
   rw [post_supp g s uv (perm q) no] at yes
   contradiction
  have tab:=sitesTable
  simp only [List.all_eq_true,decide_eq_true_eq] at tab
  have z:=tab (perm q) hg
  simpa only [localSites,List.mem_range,Equiv.symm_apply_apply] using z
 have same:=allRows (encodedInput g s uv) mem m n
 unfold encodedInput at same
 rw [←tb_enc_t8 _ localSites supp] at same
 change run candidate m (pullState perm ⟨false,postBasis g s uv⟩)=
   run reference n (pullState perm ⟨false,postBasis g s uv⟩) at same
 have cancel : pullState perm.symm (pullState perm ⟨false,postBasis g s uv⟩)=
   ⟨false,postBasis g s uv⟩ := by
  simpa only [Equiv.symm_symm] using pull_cancel perm.symm ⟨false,postBasis g s uv⟩
 have pushed:=congrArg (pullState perm.symm) same
 rw [←run_push perm candidate m,←run_push perm reference n,placement,reference_placement,cancel] at pushed
 exact pushed
end ECDSAAdd.Entrant.CompactInverse14

end -- inlined inverse proof scope
namespace ECDSAAdd.Entrant.InverseFour15
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
def sites15 : List Wire := MorningFour.sites ++ [530]
def candidate15 : Program := Inverse14Width.candidate

def old15 : Program := tickMR8 ++ W.ReverseCarry.compactReceiverTick base 507

theorem candidate_support15 : wires candidate15 ⊆ sites15.toFinset := Inverse14Width.support
theorem old_support15 : wires old15 ⊆ sites15.toFinset := by unfold old15 sites15; decide +kernel

theorem replace_sample15 (g s : Bool) (uv : Nat × Nat) (h : uv∈MorningFour.pairs)
 (hl : Forward11Width.legal uv g=true) (state : State) (m n : List Bool)
 (agree : ∀q∈sites15,state.basis q=CompactInverse14.postBasis g s uv q) :
 run Inverse14Width.candidate m state=run old15 n state := by
 apply Stack5.local_replace Inverse14Width.candidate old15 sites15.toFinset
  Inverse14Width.support old_support15 state ⟨false,CompactInverse14.postBasis g s uv⟩ m n
 · intro q hq
   exact agree q (List.mem_toFinset.mp hq)
 · exact CompactInverse14.sample_run g s uv h hl m n


theorem resources : toffoliCount candidate15=14 ∧ measurementCount candidate15=11 ∧ Challenge.gateSlots candidate15=1373 := Inverse14Width.resources
theorem physical : GatePhysical candidate15 := Inverse14Width.physical
open ECDSAAdd.Secp256k1 ECDSAAdd.Entrant.Rolling1588.Integer ECDSAAdd.Entrant.History5 ECDSAAdd.Entrant.OB5
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward Rolling1588.Integer.regularForward
theorem forward_support : wires (MorningFour.tick507 ++ tripF) ⊆ sites15.toFinset := by unfold sites15; decide +kernel

theorem local_stage15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a state : State) (stage : Stage base isA x p 507 a.basis) (m n : List Bool)
    (agree : ∀ q ∈ sites15,
      state.basis q = (run (MorningFour.tick507 ++ tripF) [] a).basis q) :
    run candidate15 m state = run old15 n state := by
  obtain ⟨raw,hraw,hbits⟩ := stage
  obtain ⟨g,s,uv,mem,width,oriented,reads⟩ := MorningWidth.raw507 x hx0 hx raw hraw
  have oldmem : uv∈MorningFour.pairs := (List.mem_filter.mp mem).1
  have hl:=Forward11Width.legal_of uv g width oriented
  have fields := (W.compactSkywalkStage_fields_iff base _ 507 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨_,_,_,_,_,_,_,cleanA,_⟩ := fields
  have free530 : raw.basis 530 = false := cleanA _ (by decide +kernel)
  have used530 : 530 ∈ (W.compactSkywalkTickLayout base 511).wires.toFinset := by decide +kernel
  have kept530 : (run (Rolling1588.Integer.encodePrefix base isA 507) [] raw).basis 530 = raw.basis 530 := by
    apply run_preserves_outside
    intro used
    exact Finset.disjoint_left.mp
      (prefix_disjoint_layout base isA base_pool_nodup 507 511 (by omega) (by omega)) used used530
  have pre : ∀ q ∈ sites15, a.basis q = MorningFour.pre507 g s uv.1 uv.2 q := by
    intro q hq
    have hq' : q ∈ MorningFour.sites ∨ q = 530 := by simpa [sites15] using hq
    rcases hq' with hq | rfl
    · rw [hbits, ←reads q hq]
      apply run_preserves_outside
      rcases MorningPlacement.layouts q hq with h|h|h|h
      all_goals
        exact fun hh => Finset.disjoint_left.mp
          (prefix_disjoint_layout base isA base_pool_nodup 507 _ (by omega) (by omega)) hh h
    · rw [hbits,kept530,free530]
      rfl
  apply replace_sample15 g s uv oldmem hl state m n
  intro q hq
  rw [agree q hq]
  rw [site_run (MorningFour.tick507 ++ tripF) sites15 forward_support a
    ⟨false,MorningFour.pre507 g s uv.1 uv.2⟩ pre [] q hq]
  rfl




theorem codec_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a t : State) (stage : Stage base isA x p 507 a.basis) (codec : Program) (m : List Bool)
    (agree : ∀ q ∈ sites15,
      (run codec (m.take (measurementCount codec)) t).basis q =
        (run (MorningFour.tick507 ++ tripF) [] a).basis q) :
    run (codec ++ candidate15) m t = run (codec ++ old15) m t := by
  rw [run_append,run_append]
  exact local_stage15 isA x hx0 hx a _ stage _ _ agree

theorem placed_codec_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a t : State) (stage : Stage base isA x p 507 a.basis) (codec : Program) (m : List Bool)
    (agree : ∀ q ∈ sites15,
      (run codec (m.take (measurementCount codec)) t).basis q =
        (run (MorningFour.tick507 ++ tripF) [] a).basis q) :
    run (renameProgram (sig 510) (codec ++ candidate15)) m (pullState (sig 510) t) =
    run (renameProgram (sig 510) (codec ++ old15)) m (pullState (sig 510) t) := by
  rw [OB5.run_rename 510 (by omega), OB5.run_rename 510 (by omega),
    codec_replace15 isA x hx0 hx a t stage codec m agree]
theorem same50715 : renameProgram (sig 507) (W.ReverseCarry.compactReceiverTick base 507) =
    renameProgram (sig 510) (W.ReverseCarry.compactReceiverTick base 507) := by decide +kernel

theorem unpack50715 (isA : Bool) : unpackFirst base isA 507 = [] := by
  simp only [unpackFirst,show ¬(507:Nat)=5 from by decide,if_false,Rolling1588.Integer.decodeBefore,
    show History5.packDue 507=false from by decide,Bool.false_eq_true,if_false]

theorem reverse_shape15 (isA : Bool) :
    Rolling1588.stackReverse isA = renameProgram (sig 511) tickR ++
      (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15) ++
        Rolling1588.reverse isA 1 506) := by
  have shape := reverse_snoc isA 1 506
  rw [show (1:Nat)+506=507 by rfl,unpack50715,List.nil_append,
    reverse_eq_packets,same50715] at shape
  rw [reverse_eq_packets] at shape
  rw [Rolling1588.stackReverse,shape]
  simp only [old15,renameProgram,List.map_append,List.append_assoc]

theorem pack_inverse15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool) :
    run (Rolling1588.Integer.decodeBefore base isA 510) mD
      (run (packAfter base isA 510) mE (run (MorningFour.tick507 ++ tripF) [] a)) =
        run (MorningFour.tick507 ++ tripF) [] a := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  let b8 := run (W.repairedTick base 507) [] a
  let b9 := run (W.repairedTick base 508) [] b8
  let b10 := run (W.repairedTick base 509) [] b9
  let b11 := run (W.repairedTick base 510) [] b10
  have s8 : Stage base isA x p 508 b8.basis := by
    have h := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 507 hp0 hx0 hpo hp gap hx cop (by omega) a [] stage).2
    simpa only [MorningPlacement.pack507,List.append_nil,b8] using h
  have s9 : Stage base isA x p 509 b9.basis := by
    have h := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 508 hp0 hx0 hpo hp gap hx cop (by omega) b8 [] s8).2
    simpa only [pack508,List.append_nil,b9] using h
  have s10 : Stage base isA x p 510 b10.basis := by
    have h := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 509 hp0 hx0 hpo hp gap hx cop (by omega) b9 [] s9).2
    simpa only [pack509,List.append_nil,b10] using h
  have rep : W.repairedTick base 510=W.compactSkywalkTick base 510 := by
    rw [tick510ExF_explicit,tick510ExF_compact]
  have legal := tick_pack_legal base isA base_pool_nodup x p 510 hp0 hx0 hpo hp gap hx cop
    (by omega) b10 [] s10 (by decide)
  rw [←rep] at legal
  have dp : run (Rolling1588.Integer.decodeBefore base isA 510) mD
      (run (packAfter base isA 510) mE b11)=b11 := by
    simpa only [Rolling1588.Integer.packAfter,Rolling1588.Integer.decodeBefore,show History5.packDue 510=true from by decide,if_true,b11] using
      encode_decode_roundtrip base isA base_pool_nodup (510-5) (by omega) b11 mE mD legal
  have eq : run (MorningFour.tick507 ++ tripF) [] a = b11 := by
    simp only [tripF,←MorningFour.explicit507,←tick508ExF_explicit,←tick509ExF_explicit,
      ←tick510ExF_explicit,List.append_assoc,run_append,List.take_nil,List.drop_nil,b8,b9,b10,b11]
  rw [eq,dp]

theorem decoded_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool) :
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ candidate15) mD
      (run (packAfter base isA 510) mE (run (MorningFour.tick507 ++ tripF) [] a)) =
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ old15) mD
      (run (packAfter base isA 510) mE (run (MorningFour.tick507 ++ tripF) [] a)) := by
  rw [run_append (Rolling1588.Integer.decodeBefore base isA 510) candidate15,
    run_append (Rolling1588.Integer.decodeBefore base isA 510) old15,
    pack_inverse15 isA x hx0 hx a stage mE]
  exact local_stage15 isA x hx0 hx a _ stage _ _ (fun _ _ => rfl)

theorem sites_pool15 : sites15.toFinset ⊆ (skywalkPoolWires base).toFinset := by
  have layout : sites15 = ([506,507,508,509,510,511,512,513,770,771,772,773,774,775,1535,1536,1537,1538,1540,1541,1542,1543,514] : List Nat).map base := by decide +kernel
  intro q hq
  have member : q ∈ sites15 := List.mem_toFinset.mp hq
  rw [layout] at member
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
  apply List.mem_toFinset.mpr
  apply OB5.base_pool i
  have bound : ∀ i ∈ ([506,507,508,509,510,511,512,513,770,771,772,773,774,775,1535,1536,1537,1538,1540,1541,1542,1543,514] : List Nat), i < 1798 := by decide
  exact bound i hi

theorem decoded_replace_pool15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool)
    (agree : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) mE a).basis q) :
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ candidate15) mD u =
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ old15) mD u := by
  let f := MorningFour.tick507 ++ tripF
  let codec := Rolling1588.Integer.decodeBefore base isA 510
  let ref := run (packAfter base isA 510) mE (run f [] a)
  have dec : wires codec ⊆ (skywalkPoolWires base).toFinset := by
    have d := (History5.pack_support5 base 510 (by omega)).2.trans (History5.integerSites5_pool base)
    rw [←decodeBefore_support_eq base isA 510] at d
    exact d
  have supportC : wires (codec ++ candidate15) ⊆ (skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,candidate_support15.trans sites_pool15⟩
  have supportO : wires (codec ++ old15) ⊆ (skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,old_support15.trans sites_pool15⟩
  apply Stack5.local_replace _ _ _ supportC supportO u ref mD mD
  · intro q hq
    have eq1 := congrFun (run_basis_records (f ++ packAfter base isA 510) a a mE [] rfl) q
    have eq2 := congrFun (run_basis_records (packAfter base isA 510) (run f [] a) (run f [] a) [] mE rfl) q
    have eq3 : (run (f ++ packAfter base isA 510) [] a).basis q =
        (run (packAfter base isA 510) [] (run f [] a)).basis q := by
      rw [run_append]; simp only [List.take_nil,List.drop_nil]
    exact (agree q (List.mem_toFinset.mp hq)).trans (eq1.trans (eq3.trans eq2))
  · exact decoded_replace15 isA x hx0 hx a stage mE mD

def reverseTail15 (isA : Bool) : Program :=
  renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ candidate15) ++
    Rolling1588.reverse isA 1 506

theorem unpack51015 (isA : Bool) :
    Rolling1588.unpackAtTick isA 510 = Rolling1588.Integer.decodeBefore base isA 510 := by
  have h := unpackFirst_base isA 510
  simpa only [unpackFirst,show ¬(510:Nat)=5 from by decide,if_false] using h.symm

theorem old_records15 : measurementCount old15 = 11 := by decide +kernel

theorem placed_block15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool)
    (agree : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) mE a).basis q) :
    run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ candidate15)) mD
      (pullState (sig 510) u) =
    run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15)) mD
      (pullState (sig 510) u) := by
  rw [unpack51015, OB5.run_rename 510 (by omega), OB5.run_rename 510 (by omega),
    decoded_replace_pool15 isA x hx0 hx a u stage mE mD agree]

theorem tail_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool)
    (agree : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) mE a).basis q) :
    run (reverseTail15 isA) mD (pullState (sig 510) u) =
      run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15) ++
        Rolling1588.reverse isA 1 506) mD (pullState (sig 510) u) := by
  have count : measurementCount (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ candidate15)) =
      measurementCount (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,
      measurementCount_append,measurementCount_append,resources.2.1,old_records15]
  rw [reverseTail15,run_append,run_append, count,
    placed_block15 isA x hx0 hx a u stage mE _ agree]


theorem tail_actual15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (u : State) (hu : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run (regularForward base isA 1 510) mE s1).basis q) (mD : List Bool) :
    run (reverseTail15 isA) mD (pullState (sig 510) u) =
      run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15) ++
        Rolling1588.reverse isA 1 506) mD (pullState (sig 510) u) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  let k := measurementCount (regularForward base isA 1 506)
  have stage0 : Stage base isA x p 507
      (run (regularForward base isA 1 506)
        (mE.take (measurementCount (regularForward base isA 1 506))) s1).basis :=
    ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p 1 506
      hp0 hx0 hpo hp gap hx cop (by omega)) s1 _ (stage_one base isA x p s1 first)).2
  change Stage base isA x p 507 (run (regularForward base isA 1 506) (mE.take k) s1).basis at stage0
  obtain ⟨a,ha⟩ : ∃ a : State,run (regularForward base isA 1 506) (mE.take k) s1 = a := ⟨_,rfl⟩
  rw [ha] at stage0
  have fwdP : regularForward base isA 1 510 = regularForward base isA 1 506 ++
      ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) := by
    rw [regularForward_snoc base isA 1 509,show (1:Nat)+509=510 by rfl,
      regularForward_snoc base isA 1 508,show (1:Nat)+508=509 by rfl,
      regularForward_snoc base isA 1 507,show (1:Nat)+507=508 by rfl,
      regularForward_snoc base isA 1 506,show (1:Nat)+506=507 by rfl,
      MorningPlacement.pack507,pack508,pack509,
      MorningFour.explicit507,tick508ExF_explicit,tick509ExF_explicit,tick510ExF_explicit]
    simp only [tripF,List.append_assoc,List.append_nil]
  have agre : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) (mE.drop k) a).basis q := by
    intro q hq
    rw [hu q hq,fwdP,run_append,←show measurementCount (regularForward base isA 1 506)=k from rfl,ha]
  exact tail_replace15 isA x hx0 hx a u stage0 (mE.drop k) mD agre

attribute [local irreducible] Stage
def stackReverse15 (isA : Bool) : Program := renameProgram (sig 511) tickR ++ reverseTail15 isA

theorem reverse_actual15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (t5 : State) (agree : ∀q∈skywalkPoolWires base,
      t5.basis q=(run (regularForward base isA 1 511) mE s1).basis q) (mD : List Bool) :
    run (stackReverse15 isA) mD (pullState (sig 511) t5)=
      run (Rolling1588.stackReverse isA) mD (pullState (sig 511) t5) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  have aStage : Stage base isA x p 511
      (run (regularForward base isA 1 510)
        (mE.take (measurementCount (regularForward base isA 1 510))) s1).basis :=
    ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p 1 510
      hp0 hx0 hpo hp hgap hx cop (by omega)) s1 _ (stage_one base isA x p s1 first)).2
  have whole : run (regularForward base isA 1 510)
      (mE.take (measurementCount (regularForward base isA 1 510))) s1=
        run (regularForward base isA 1 510) mE s1 := run_take _ mE s1
  have last : run (regularForward base isA 1 511) mE s1=
      run (W.repairedTick base 511) (mE.drop (measurementCount (regularForward base isA 1 510)))
        (run (regularForward base isA 1 510)
          (mE.take (measurementCount (regularForward base isA 1 510))) s1) := by
    rw [regularForward_snoc base isA 1 510,show (1:Nat)+510=511 by rfl,regular_pack511,List.append_nil,run_append]
  rw [last] at agree
  generalize run (regularForward base isA 1 510)
    (mE.take (measurementCount (regularForward base isA 1 510))) s1=a at aStage whole agree
  obtain ⟨G,bits⟩ := stage511_bits isA x hx0 hx a aStage
  rw [repaired511_forced G a bits] at agree
  have post : ∀q∈tickSites,t5.basis q=postBits G q := by
    intro q hq
    rw [agree q (tickSites_pool q hq)]
    exact tickF_post G a bits q hq
  have uAgree : ∀q∈skywalkPoolWires base,(run tickR [] t5).basis q=a.basis q := by
    intro q hq
    by_cases ht : q∈tickSites
    · rw [site_run tickR tickSites tickR_wires t5 ⟨false,postBits G⟩ post [] q ht,tickR_pre G q ht]
      exact (bits q ht).symm
    · have hr : q∉wires tickR := fun h => ht (List.mem_toFinset.mp (tickR_wires h))
      have hf : q∉wires tickF := fun h => ht (List.mem_toFinset.mp (tickF_wires h))
      rw [run_preserves_outside tickR [] t5 q hr,agree q hq,run_preserves_outside tickF [] a q hf]
  have z := stage_zero isA x 511 (by omega) a.basis aStage
  have move : pullState (sig 511) (run tickR [] t5)=pullState (sig 510) (run tickR [] t5) :=
    (OB5.pull_step 511 (by omega) _
      ((uAgree _ (StackOB5Base.base_pool _ (by omega))).trans z.1)
      (fun big => (uAgree _ (StackOB5Base.base_pool _ (by omega))).trans (z.2 big))).symm
  have cn : measurementCount (renameProgram (sig 511) tickR)=0 :=
    (renameProgram_counts (sig 511) tickR).2.trans tickR_counts.2
  rw [stackReverse15,reverse_shape15,run_append,run_append,cn]
  simp only [List.take_zero,List.drop_zero]
  rw [OB5.run_rename 511 (by omega),tickR_run,move]
  exact tail_actual15 isA x hx0 hx s1 mE first _
    (fun q hq => (uAgree q hq).trans (congrArg (fun st : State => st.basis q) whole)) mD

theorem stack_roundtrip15 (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackReverse15 isA) mD (run (Rolling1588TickGap.stackForward isA) mE s)=s := by
  have fwd : run (Rolling1588TickGap.stackForward isA) mE s =
      pullState (sig 511) (run (regularForward base isA 1 511) mE s) := by
    rw [Rolling1588TickGap.stackForward_run_eq isA x hx0 hx s mE first,
      ←Rolling1588.Integer.stackForward_eq_packets,Rolling1588.Integer.stackForwardT_run isA hn hlo x hx0 hx s mE first,
      Rolling1588.Integer.forward_run isA x hx0 hx s mE first]
  rw [fwd, reverse_actual15 isA x hx0 hx s mE first _ (fun _ _ => rfl) mD,←fwd]
  exact Rolling1588TickGap.stack_roundtrip isA hn hlo x hx0 hx s mE mD first

open ECDSAAdd.Arithmetic.DirectSkywalk
def lastPhase15 (isA : Bool) : Program :=
  skywalkArithmeticClear base ++ stackReverse15 isA ++ FrontierEntry1591NativeH.inverse base

private theorem compose_roundtrip15 (N F C R I : Program) (s : State) (mp mr : List Bool)
    (clearM : measurementCount C=0)
    (twice : ∀ (t : State) mc,run C [] (run C mc t)=t)
    (stack : ∀mn mf md,run R md (run F mf (run N mn s))=run N mn s)
    (native : ∀mn mi,run I mi (run N mn s)=s) :
    run (C++(R++I)) mr (run (N++(F++C)) mp s)=s := by
  simp only [run_append,clearM,List.take_zero,List.drop_zero]
  rw [twice,stack]
  exact native _ _

theorem phases_roundtrip15 (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (mp mr : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (lastPhase15 isA) mr (run (Rolling1588TickGap.firstPhase isA) mp s)=s := by
  have clearM : measurementCount (skywalkArithmeticClear base)=0 := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,measurementCount]
  have twice (t : State) (mc : List Bool) : run (skywalkArithmeticClear base) []
      (run (skywalkArithmeticClear base) mc t)=t := by
    simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
      (base 511) (base 512) (base 770) (arith_clear_gates base hn) t mc []
  have stack (mn mf md : List Bool) :
      run (stackReverse15 isA) md (run (Rolling1588TickGap.stackForward isA) mf
        (run (FrontierEntry1591Native.forward base) mn s))=
      run (FrontierEntry1591Native.forward base) mn s :=
    stack_roundtrip15 isA hn hlo x hx0 hx _ mf md
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [Rolling1588TickGap.firstPhase,Rolling1588TickGap.tailPhase,lastPhase15,List.append_assoc] using
    compose_roundtrip15 (FrontierEntry1591Native.forward base) (Rolling1588TickGap.stackForward isA)
      (skywalkArithmeticClear base) (stackReverse15 isA)
      (FrontierEntry1591NativeH.inverse base) s mp mr clearM twice stack
      (fun mn mi=>FrontierEntry1591NativeH.inverse_roundtrip base hn x y hx s mn mi input)

attribute [local irreducible] Rolling1588.stackReverse Rolling1588.lastPhase stackReverse15 reverseTail15 lastPhase15 candidate15 old15
theorem cand_extra15 : wires (renameProgram (sig 510) candidate15) ⊆
    wires (renameProgram (sig 510) old15) ∪ {530} := by
  have parts : MorningFour.sites.toFinset ⊆ wires old15 ∪ {1559} := by decide +kernel
  have absent : (1559:Wire) ∉ wires candidate15 := by
    intro h
    have hx : 1559∈wires Inverse14Width.candidate := by simpa only [candidate15] using h
    exact (Finset.mem_erase.mp (Inverse14Width.support_live hx)).1 rfl
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  have member : v ∈ sites15 := List.mem_toFinset.mp (candidate_support15 hv)
  have cases : v ∈ MorningFour.sites ∨ v=530 := by simpa [sites15] using member
  rcases cases with oldsite | extra
  · have member := parts (List.mem_toFinset.mpr oldsite)
    rcases Finset.mem_union.mp member with old | extra
    · apply Finset.mem_union_left
      rw [renameProgram_support]
      exact Finset.mem_image.mpr ⟨v,old,rfl⟩
    · simp only [Finset.mem_singleton] at extra
      exact False.elim (absent (extra ▸ hv))
  · subst v
    apply Finset.mem_union_right
    simp only [Finset.mem_singleton]
    decide +kernel

theorem last_extra15 (isA : Bool) : wires (lastPhase15 isA) ⊆
    wires (Rolling1588.lastPhase isA) ∪ {530} := by
  have ren (p q : Program) : renameProgram (sig 510) (p ++ q) =
      renameProgram (sig 510) p ++ renameProgram (sig 510) q := by simp only [renameProgram,List.map_append]
  have hsub := cand_extra15
  intro q h
  simp only [lastPhase15,stackReverse15,reverseTail15,ren,wires_append,
    Finset.mem_union] at h
  rw [Rolling1588.lastPhase,reverse_shape15]
  simp only [ren,wires_append,Finset.mem_union,Finset.mem_singleton] at h ⊢
  have hh : q ∈ wires (renameProgram (sig 510) candidate15) →
      q ∈ wires (renameProgram (sig 510) old15) ∨ q=530 := by
    intro hc
    have z := hsub hc
    simpa only [Finset.mem_union,Finset.mem_singleton] using z
  rcases h with ((hc | ht | (hcodec | hcand) | hrest) | hinv)
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr (Or.inl ht)))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl hcodec)))))
  · rcases hh hcand with hold | hextra
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr hold)))))
    · exact Or.inr hextra
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr hrest))))
  · exact Or.inl (Or.inr hinv)

theorem extra_pool15 : 530 ∈ (skywalkPoolWires base).toFinset := by
  have h := OB5.base_pool 514 (by decide)
  exact List.mem_toFinset.mpr (by simpa only [show base 514 = 530 from by decide +kernel] using h)

theorem last_pool15 (isA : Bool) : wires (lastPhase15 isA) ⊆ (skywalkPoolWires base).toFinset := by
  intro q h
  rcases Finset.mem_union.mp (last_extra15 isA h) with old | extra
  · exact ((Rolling1588Lifetime.last_support_sub isA).trans FrontierEntry1591Kernel.last_pool) old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact extra_pool15

theorem last_hosts_free15 (isA : Bool) (q : Wire) (hq : q ∈ Rolling1588Lifetime.phaseHosts) :
    q ∉ wires (lastPhase15 isA) := by
  intro h
  rcases Finset.mem_union.mp (last_extra15 isA h) with old | extra
  · exact Rolling1588Lifetime.last_hosts_free isA q hq old
  · simp only [Finset.mem_singleton] at extra
    subst q
    have no : (530:Wire) ∉ Rolling1588Lifetime.phaseHosts := by decide +kernel
    exact no hq

open ECDSAAdd.Entrant.Rolling1588Lifetime
private theorem phase_sites_split :
    phaseSites=FrontierEntry1591Native.workSites∪phaseHosts := by
  ext q
  simp only [phaseSites,phaseHosts,FrontierEntry1591Native.workSites,Finset.mem_union,
    List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem phase_kernel_rebind (P F Q : Program) (s : State) (m : List Bool)
    (input : ∀q∈phaseSites,s.basis q=false)
    (firstFree : ∀q∈phaseHosts,q∉wires P)
    (firstClean : ∀records,∀q∈FrontierEntry1591Native.workSites,
      (run P records s).basis q=false)
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (lastFree : ∀q∈phaseHosts,q∉wires Q)
    (output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel P F Q) m s).basis q=false) :
    run (renameProgram phaseHost P++(F++renameProgram phaseHost Q)) m s=
      run (FrontierEntry1591Native.kernel P F Q) m s := by
  let mp := m.take (measurementCount P)
  let rest := m.drop (measurementCount P)
  let mf := rest.take (measurementCount F)
  let mr := rest.drop (measurementCount F)
  let before := run P mp s
  let after := run F mf before
  have finalClean : ∀q∈phaseSites,(run Q mr after).basis q=false := by
    simpa only [FrontierEntry1591Native.kernel,run_append] using output
  have lastInput : ∀q∈phaseSites,after.basis q=false := by
    intro q hq
    rw [phase_sites_split] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact (run_preserves_outside F mf before q (fieldFree q work)).trans (firstClean mp q work)
    · exact (run_preserves_outside Q mr after q (lastFree q host)).symm.trans
        (finalClean q (by rw [phase_sites_split];exact Finset.mem_union_right _ host))
  have firstOutput : ∀q∈phaseSites,(run P mp s).basis q=false := by
    intro q hq
    rw [phase_sites_split] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact firstClean mp q work
    · exact (run_preserves_outside P mp s q (firstFree q host)).trans
        (input q (by rw [phase_sites_split];exact Finset.mem_union_right _ host))
  have first := phase_run_eq P s mp input firstOutput
  have last := phase_run_eq Q after mr lastInput finalClean
  simp only [FrontierEntry1591Native.kernel,run_append,(renameProgram_counts _ _).2]
  rw [first]
  exact last


private theorem phase_numerator_away (q : Wire) (hq : q∈phaseSites) :
    q∉wireBlock base 2056 256 := by
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact OwnPlusHost.not_block _ 2056 256 (by omega)

/-- The field changes A into B. Its output is compared with a B encoding
of the same raw integer history before the B inverse is applied. -/
theorem raw_result_of_roundtrip (a b : Bool) (F : Program) (s : State) (m : List Bool)
    (value : Nat)
    (roundtrip : ∀mp mr,run (lastPhase15 b) mr (run (firstPhase b) mp s)=s)
    (fieldResult : ∀mp mf,
      let beforeA := run (firstPhase a) mp s
      let beforeB := run (firstPhase b) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (FrontierEntry1591Native.kernel (firstPhase a) F (lastPhase15 b)) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have firstPool : wires (firstPhase b)⊆(skywalkPoolWires base).toFinset := by
    rw [first_support_eq]
    exact FrontierEntry1591Kernel.first_pool
  have lastPool : wires (lastPhase15 b)⊆(skywalkPoolWires base).toFinset :=
    last_pool15 b
  have all := run_three_states (firstPhase a) F (lastPhase15 b)
    (fun initial out=>initial=s → out.phase=s.phase ∧
      regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q) (by
      intro initial beforeA after out mp mf mr h1 h2 h3 eq
      subst initial
      have result := fieldResult mp mf
      dsimp only at result
      rw [h1,h2] at result
      exact FrontierEntry1591Kernel.sandwich_states (firstPhase b) (lastPhase15 b) firstPool lastPool s
        (run (firstPhase b) mp s) after out mp mr value rfl h3 (roundtrip mp mr) result) s m
  simpa only [FrontierEntry1591Native.kernel,List.append_assoc] using all rfl



theorem kernel_result15 (a b : Bool) (F : Program) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool) (value : Nat)
    (input : SkywalkArithmeticInput base x y s.basis)
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (fieldResult : ∀mp mf,
      let beforeA := run (firstPhase a) mp s
      let beforeB := run (firstPhase b) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (renameProgram phaseHost (firstPhase a)++
      (F++renameProgram phaseHost (lastPhase15 b))) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have rt (mp mr : List Bool) : run (lastPhase15 b) mr (run (firstPhase b) mp s)=s := by
    rw [←Rolling1588TickGap.first_run_eq b hn x y hx0 hx s mp input]
    exact phases_roundtrip15 b hn hlo x y hx0 hx s mp mr input
  have raw := raw_result_of_roundtrip a b F s m value rt fieldResult
  have clean := caller_phase_clean x y s input
  have output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel (firstPhase a) F (lastPhase15 b)) m s).basis q=false := by
    intro q hq
    exact (raw.2.2 q (phase_numerator_away q hq)).trans (clean q hq)
  have same := phase_kernel_rebind (firstPhase a) F (lastPhase15 b) s m clean
    (first_hosts_free a) (fun records => Rolling1588Lifetime.first_clean a hn hlo x y hx0 hx s records input)
    fieldFree (last_hosts_free15 b) output
  dsimp only
  rw [same]
  exact raw

open ECDSAAdd.Entrant.Rolling1588 ECDSAAdd.Entrant.FrontierEntry1591Callers ECDSAAdd.Arithmetic.BalancedField
def oldKernel15 (a b : Bool) (F : Program) : Program :=
  renameProgram phaseHost (Rolling1588.firstPhase a) ++
    (F ++ renameProgram phaseHost (lastPhase15 b))
def kernel15 (a b : Bool) (F : Program) : Program :=
  renameProgram phaseHost (Rolling1588TickGap.firstPhase a) ++
    (F ++ renameProgram phaseHost (lastPhase15 b))
def entryKernel15 : Program := kernel15 true false entryFieldHosted
def exitKernel15 : Program := kernel15 false true exitFieldHosted

theorem old_entry_correct15 : EntryCorrect (oldKernel15 true false entryFieldHosted) := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  obtain ⟨out,outEq⟩ : ∃out : State,run (oldKernel15 true false entryFieldHosted) m t=out := ⟨_,rfl⟩
  have actualInput := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  have result := kernel_result15 true false entryFieldHosted hn hlo
    x _ hx0 hx t m (Y/(x:Fp)).val actualInput entryFieldHosted_work_free
    (fun mp mf=>entry_boundary hn hlo ho hf x Y hx0 hx s t mp mf input hg hs phase same half)
  change (run (oldKernel15 true false entryFieldHosted) m t).phase=t.phase ∧
    regValue (wireBlock base 2056 256) (run (oldKernel15 true false entryFieldHosted) m t).basis=(Y/(x:Fp)).val ∧
    ∀q,q∉wireBlock base 2056 256 → (run (oldKernel15 true false entryFieldHosted) m t).basis q=t.basis q at result
  rw [outEq] at result
  have conclusion : out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(Y/(x:Fp)).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q :=
    ⟨result.1.trans phase,result.2.1,fun q hq=>(result.2.2 q hq).trans (same q hq)⟩
  dsimp only
  rw [outEq]
  simpa only [skywalkArithmeticResult,if_true] using conclusion

theorem old_exit_correct15 : ExitCorrect (oldKernel15 false true exitFieldHosted) := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  have result := kernel_result15 false true exitFieldHosted hn hlo
    x Y.val hx0 hx s m (centerWord (Y*(x:Fp)/2)) input exitFieldHosted_work_free
    (fun mp mf=>exit_boundary hn hlo ho hf x Y hx0 hx s mp mf input hg hs)
  simpa only [oldKernel15,skywalkArithmeticNumerator] using result

theorem kernel_first_eq15 (a b : Bool) (F : Program)
    (hn : (skywalkSharedWires base).Nodup) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (kernel15 a b F) m s = run (oldKernel15 a b F) m s := by
  have records : measurementCount (renameProgram phaseHost (Rolling1588TickGap.firstPhase a)) =
      measurementCount (renameProgram phaseHost (Rolling1588.firstPhase a)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(Rolling1588TickGap.first_metrics a).2.1]
  rw [kernel15,oldKernel15,
    run_append (renameProgram phaseHost (Rolling1588TickGap.firstPhase a)),
    run_append (renameProgram phaseHost (Rolling1588.firstPhase a)),records,
    Rolling1588TickGap.first_hosted_run_eq a hn x y hx0 hx s _ input]

theorem entry_correct15 : EntryCorrect entryKernel15 := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actual := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  rw [entryKernel15,kernel_first_eq15 true false entryFieldHosted hn x _ hx0 hx t m actual]
  exact old_entry_correct15 hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half

theorem exit_correct15 : ExitCorrect exitKernel15 := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  rw [exitKernel15,kernel_first_eq15 false true exitFieldHosted hn x _ hx0 hx s m input]
  exact old_exit_correct15 hn hlo ho hf x Y hx0 hx s m input hg hs

theorem last_physical15 (isA : Bool) : GatePhysical (lastPhase15 isA) := by
  have old := Rolling1588.lastPhase_physical isA
  rw [Rolling1588.lastPhase,reverse_shape15] at old
  have ren (p q : Program) : renameProgram (sig 510) (p ++ q) =
      renameProgram (sig 510) p ++ renameProgram (sig 510) q := by simp only [renameProgram,List.map_append]
  simp only [gatePhysical_append,ren] at old
  rw [lastPhase15,stackReverse15,reverseTail15,ren]
  simp only [gatePhysical_append]
  exact ⟨⟨old.1.1,old.1.2.1,⟨old.1.2.2.1.1,
    gatePhysical_rename _ (sig_injective 510 (by omega)) _ physical⟩,old.1.2.2.2⟩,old.2⟩

theorem kernel_physical15 (a b : Bool) (F : Program) (field : GatePhysical F) :
    GatePhysical (kernel15 a b F) := by
  simpa only [kernel15,gatePhysical_append] using
    And.intro (Rolling1588Lifetime.phase_physical _ (Rolling1588TickGap.first_physical a))
      (And.intro field (Rolling1588Lifetime.phase_physical _ (last_physical15 b)))

theorem entry_physical15 : GatePhysical entryKernel15 := by
  simpa only [entryKernel15] using
    kernel_physical15 true false Rolling1588.entryFieldHosted Rolling1588.entryFieldHosted_physical

theorem exit_physical15 : GatePhysical exitKernel15 := by
  simpa only [exitKernel15] using
    kernel_physical15 false true Rolling1588.exitFieldHosted Rolling1588.exitFieldHosted_physical

theorem hosted_extra530 (b : Bool) :
    wires (renameProgram phaseHost (lastPhase15 b)) ⊆
      wires (renameProgram phaseHost (Rolling1588.lastPhase b)) ∪ {530} := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (last_extra15 b hv) with old | extra
  · apply Finset.mem_union_left
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨v,old,rfl⟩
  · simp only [Finset.mem_singleton] at extra
    subst v
    apply Finset.mem_union_right
    simp only [Finset.mem_singleton]
    decide +kernel

theorem kernel_extra530 (a b : Bool) (F : Program) :
    wires (kernel15 a b F) ⊆ wires (Rolling1588TickGap.kernel a b F) ∪ {530} := by
  have hsub := hosted_extra530 b
  intro q h
  simp only [kernel15,wires_append,Finset.mem_union] at h
  simp only [Rolling1588TickGap.kernel,wires_append,Finset.mem_union,Finset.mem_singleton]
  rcases h with hfirst | hfield | hlast
  · exact Or.inl (Or.inl hfirst)
  · exact Or.inl (Or.inr (Or.inl hfield))
  · rcases Finset.mem_union.mp (hsub hlast) with hold | hextra
    · exact Or.inl (Or.inr (Or.inr hold))
    · exact Or.inr (Finset.mem_singleton.mp hextra)

theorem extra_logical530 : (530:Wire) ∈ OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨514,?_,by decide +kernel⟩
  simp [OB5Support.logicalIndices]

theorem entry_support530 : wires entryKernel15 ⊆ OB5Support.logicalSites := by
  intro q hq
  have h := kernel_extra530 true false Rolling1588.entryFieldHosted hq
  rcases Finset.mem_union.mp h with old | extra
  · exact Rolling1588TickGap.entryKernel_support old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact extra_logical530

theorem exit_support530 : wires exitKernel15 ⊆ OB5Support.logicalSites := by
  intro q hq
  have h := kernel_extra530 false true Rolling1588.exitFieldHosted hq
  rcases Finset.mem_union.mp h with old | extra
  · exact Rolling1588TickGap.exitKernel_support old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact extra_logical530

end ECDSAAdd.Entrant.InverseFour15

namespace ECDSAAdd.Entrant.InverseFour15
open ECDSAAdd.Challenge ECDSAAdd.Entrant.Rolling1588Lifetime
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] Rolling1588.stackReverse Rolling1588.lastPhase stackReverse15 reverseTail15 lastPhase15 candidate15 old15
 theorem reverse_metrics_new (isA : Bool) :
    toffoliCount (stackReverse15 isA) + 2 = toffoliCount (Rolling1588.stackReverse isA) ∧
    measurementCount (stackReverse15 isA) = measurementCount (Rolling1588.stackReverse isA) ∧
    gateSlots (stackReverse15 isA) = gateSlots (Rolling1588.stackReverse isA) + 1084 := by
  have old : toffoliCount old15 = 16 ∧ measurementCount old15 = 11 ∧ gateSlots old15 = 289 := by decide +kernel
  have fresh := resources
  rw [reverse_shape15]
  simp only [stackReverse15,reverseTail15,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots] at *
  omega
end ECDSAAdd.Entrant.InverseFour15


namespace ECDSAAdd.Entrant.ExitMergeKernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Rolling1588Lifetime BalancedField
  ControlledPointLayout CompressedPointDialog
attribute [local irreducible] run wires

/-! ### Placement of the merged exit circuit in the unhosted phase coordinates -/

def pi : Equiv.Perm Wire := E1QubitPlacement.rho.trans E1QubitPlacement.nativeSwap

def piN (i : Nat) : Nat :=
  if E1QubitPlacement.rhoN i=1797 then 511 else if E1QubitPlacement.rhoN i=511 then 1797
  else E1QubitPlacement.rhoN i

theorem pi_base (i : Nat) : pi (base i)=base (piN i) := by
  change E1QubitPlacement.nativeSwap (E1QubitPlacement.rho (base i))=_
  rw [E1QubitPlacement.rho_base]
  unfold E1QubitPlacement.nativeSwap
  rw [E1QubitPlacement.swap_base]
  unfold piN
  rfl

/-- The merged exit circuit, placed like the direct first tick. -/
def x1 (k : Nat) : Program := renameProgram pi (ExitMerge.program base (base 2400) k)

/-- The exit last phase with the inverse tick and the controlled negation merged. -/
def lastX (k : Nat) : Program :=
  skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true ++ x1 k

theorem x1_has530x (k : Nat) : (530:Wire) ∈ wires (x1 k) := by
  rw [x1,renameProgram_support]
  apply Finset.mem_image.mpr
  refine ⟨base 514, ?_, ?_⟩
  · simp only [ExitMerge.program,ExitMerge.fPart,wires_append,Finset.mem_union]
    left; left; left; left; left; left; left; right
    simp [wires,Instr.wires]
  · rw [pi_base]
    decide +kernel


def negDiv (k x : Nat) (G : Bool) : Nat := if G then (k+p-x)%p else x

theorem forward_placed :
    FrontierEntry1591Native.forward base=renameProgram pi (NativeFirstDirect.forward base) := by
  have e := E1QubitPlacement.rho_fix E1QubitPlacement.nativeSwap
  change renameProgram (fun q => E1QubitPlacement.nativeSwap (E1QubitPlacement.rho q))
    (NativeFirstDirect.forward base)=renameProgram E1QubitPlacement.nativeSwap
      (NativeFirstDirect.forward base) at e
  rw [show renameProgram pi (NativeFirstDirect.forward base)=renameProgram
    (fun q => E1QubitPlacement.nativeSwap (E1QubitPlacement.rho q)) (NativeFirstDirect.forward base) from rfl,e]
  rfl

theorem mem_pool_iff (q : Wire) : q∈skywalkPoolWires base ↔ ∃ i, i < 1798 ∧ q=base i := by
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hi
    exact ⟨i,by omega,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem piN_lt (i : Nat) (hi : i < 1798) : piN i < 1798 := by
  unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega

theorem pi_pool (q : Wire) (hq : q∈skywalkPoolWires base) : pi q∈skywalkPoolWires base := by
  obtain ⟨i,hi,rfl⟩ := (mem_pool_iff q).mp hq
  rw [pi_base]
  exact (mem_pool_iff _).mpr ⟨_,piN_lt i hi,rfl⟩

theorem pi_out (r : Wire) (h : r∉skywalkPoolWires base) : pi r=r := by
  have ne (i : Nat) (hi : i < 1798) : r≠base i := fun e => h ((mem_pool_iff r).mpr ⟨i,hi,e⟩)
  simp only [pi,Equiv.trans_apply,E1QubitPlacement.rho,E1QubitPlacement.nativeSwap,
    Equiv.swap_apply_of_ne_of_ne (ne 511 (by omega)) (ne 725 (by omega)),
    Equiv.swap_apply_of_ne_of_ne (ne 721 (by omega)) (ne 723 (by omega)),
    Equiv.swap_apply_of_ne_of_ne (ne 722 (by omega)) (ne 724 (by omega)),
    Equiv.swap_apply_of_ne_of_ne (ne 1797 (by omega)) (ne 511 (by omega))]

theorem pi_symm_pool (q : Wire) (hq : q∈skywalkPoolWires base) : pi.symm q∈skywalkPoolWires base := by
  by_contra h
  have e := pi_out (pi.symm q) h
  rw [Equiv.apply_symm_apply] at e
  rw [←e] at h
  exact h hq

theorem piN_kR (i : Nat) (hi : 770 ≤ i ∧ i < 1028) : piN i=i := by
  unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega

theorem pi_kR (q : Wire) (hq : q∈wireBlock base 770 258) : pi q=q := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  rw [pi_base,piN_kR i (by omega)]

theorem pi_symm_kR (q : Wire) (hq : q∈wireBlock base 770 258) : pi.symm q=q := by
  have := pi_kR q hq
  rw [←this,Equiv.symm_apply_apply,this]

theorem pi_fix (i : Nat) (hi : i < 258 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1797) ∨ i=2400) :
    pi (base i)=base i := by
  rw [pi_base]; congr 1
  unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega

/-! ### The merged exit circuit on the image of the placed first tick

Every state comparison below goes through `pull_basis`/`pull_phase` rewrites, so the kernel never
has to evaluate a concrete program to see through `pullState`. -/

theorem pull_basis (f : Wire → Wire) (t : State) (q : Wire) : (pullState f t).basis q=t.basis (f q) := rfl
theorem pull_phase (f : Wire → Wire) (t : State) : (pullState f t).phase=t.phase := rfl
theorem x1_eq (k : Nat) : x1 k=renameProgram pi (ExitMerge.program base (base 2400) k) := rfl

theorem x1_run (k : Nat) (hk : k < p) (x y : Nat) (hx : x < p) (s v : State) (mn r : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis)
    (hphase : v.phase=(run (FrontierEntry1591Native.forward base) mn s).phase)
    (hpool : ∀q∈skywalkPoolWires base,v.basis q=(run (FrontierEntry1591Native.forward base) mn s).basis q) :
    (run (x1 k) r v).phase=s.phase ∧
    regValue (wireBlock base 770 258) (run (x1 k) r v).basis=negDiv k x (v.basis (base 2400)) ∧
    (∀q∈skywalkPoolWires base,q∉wireBlock base 770 258 → (run (x1 k) r v).basis q=s.basis q) ∧
    (∀q,q∉skywalkPoolWires base → (run (x1 k) r v).basis q=v.basis q) := by
  rw [x1_eq]
  have rr := run_rename pi pi.injective (ExitMerge.program base (base 2400) k) r v
  have fr := run_rename pi pi.injective (NativeFirstDirect.forward base) mn s
  rw [←forward_placed] at fr
  have sh : (i : Nat) → (hi : i < 2314) → (hdx : ¬(770 ≤ i ∧ i < 1026)) → (hdy : ¬(2056 ≤ i ∧ i < 2312)) →
      s.basis (base i)=false := by
    intro i hi hdx hdy
    apply input.2.2
    · exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
    · intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
      simp only [List.mem_range'_1] at hj
      have := base_injective e; omega
    · intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
      simp only [List.mem_range'_1] at hj
      have := base_injective e; omega
  have izero (i : Nat) (hi : i < 1798) (hx' : ¬(770 ≤ i ∧ i < 1026)) : (pullState pi s).basis (base i)=false := by
    rw [pull_basis,pi_base]
    have h1 := piN_lt i hi
    apply sh _ (by omega) _ (by omega)
    unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega
  have blk0 (a n : Nat) (h : a+n ≤ 1798) (hd : a+n ≤ 770 ∨ 1026 ≤ a) :
      regValue (wireBlock base a n) (pullState pi s).basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact izero i (by omega) (by omega)
  have hxr : regValue (wireBlock base 770 256) (pullState pi s).basis=x := by
    rw [regValue_congr _ _ s.basis (fun q hq => by
      rw [pull_basis,pi_kR q (E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) q hq)])]
    exact input.1
  have seed : LiteralSkywalkSeedValues (literalSkywalkPoolSeed base) 0 x (pullState pi s).basis := by
    refine ⟨blk0 0 258 (by omega) (by omega),?_,blk0 1540 257 (by omega) (by omega),
      izero 1797 (by omega) (by omega),izero 1028 (by omega) (by omega),izero 1797 (by omega) (by omega)⟩
    change regValue (E1Merge.kR base) (pullState pi s).basis=x
    rw [E1Merge.kR_x base base_pool_nodup,show E1Merge.xR base=wireBlock base 770 256 from rfl,hxr,
      blk0 1026 2 (by omega) (by omega)]
    simp
  have fpool : ∀q∈skywalkPoolWires base,
      (pullState pi v).basis q=(run (NativeFirstDirect.forward base) mn (pullState pi s)).basis q := by
    intro q hq
    rw [←fr,pull_basis,pull_basis]
    exact hpool _ (pi_pool q hq)
  have fphase : (pullState pi v).phase=(run (NativeFirstDirect.forward base) mn (pullState pi s)).phase := by
    rw [←fr,pull_phase,pull_phase]; exact hphase
  have pr := ExitMerge.program_run base (base 2400) base_pool_nodup E1QubitPlacement.g2400 k hk x hx
    (pullState pi s) (pullState pi v) mn r seed (blk0 1029 256 (by omega) (by omega))
    (izero 514 (by omega) (by omega)) (izero 721 (by omega) (by omega)) (izero 722 (by omega) (by omega))
    fphase fpool
  rw [←rr] at pr
  obtain ⟨p1,p2,p3,p4⟩ := pr
  rw [pull_phase,pull_phase] at p1
  rw [pull_basis,pi_fix 2400 (by omega)] at p2
  refine ⟨p1,?_,?_,?_⟩
  · rw [regValue_congr _ _ (pullState pi (run (renameProgram pi (ExitMerge.program base (base 2400) k)) r v)).basis
      (fun q hq => by rw [pull_basis,pi_kR q hq])]
    exact p2
  · intro q hq hk'
    have hs : pi.symm q∉E1Merge.kR base := fun h => hk' (by
      have e := pi_kR _ h; rw [Equiv.apply_symm_apply] at e; rw [e]; exact h)
    have h3 := p3 _ (pi_symm_pool q hq) hs
    rw [pull_basis,pull_basis,Equiv.apply_symm_apply] at h3
    exact h3
  · intro q hq
    have hs : pi.symm q∉skywalkPoolWires base := fun h => hq (by
      have := pi_pool _ h; rwa [Equiv.apply_symm_apply] at this)
    have h4 := p4 _ hs
    rw [pull_basis,pull_basis,Equiv.apply_symm_apply] at h4
    exact h4

/-! ### Kernel with the merged exit: unhosted form -/

private theorem compose_half (N F C R : Program) (s : State) (mp mr : List Bool)
    (clearM : measurementCount C=0)
    (twice : ∀ (t : State) mc,run C [] (run C mc t)=t)
    (stack : ∀mn mf md,run R md (run F mf (run N mn s))=run N mn s) :
    run (C++R) mr (run (N++(F++C)) mp s)=run N (mp.take (measurementCount N)) s := by
  simp only [run_append,clearM,List.take_zero,List.drop_zero]
  rw [twice,stack]

theorem prefix_roundtrip (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (mp mr : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true) mr
        (run (Rolling1588.firstPhase true) mp s)=
      run (FrontierEntry1591Native.forward base)
        (mp.take (measurementCount (FrontierEntry1591Native.forward base))) s := by
  have clearM : measurementCount (skywalkArithmeticClear base)=0 := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,measurementCount]
  have twice (t : State) (mc : List Bool) : run (skywalkArithmeticClear base) []
      (run (skywalkArithmeticClear base) mc t)=t := by
    simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
      (base 511) (base 512) (base 770) (arith_clear_gates base hn) t mc []
  have stack (mn mf md : List Bool) :
      run (InverseFour15.stackReverse15 true) md (run (Rolling1588.stackForward true) mf
        (run (FrontierEntry1591Native.forward base) mn s))=
      run (FrontierEntry1591Native.forward base) mn s := by
    have first := FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input
    rw [← Rolling1588TickGap.stackForward_run_eq true x hx0 hx _ mf first]
    exact InverseFour15.stack_roundtrip15 true hn hlo x hx0 hx _ mf md first
  simpa only [Rolling1588.firstPhase,List.append_assoc] using
    compose_half (FrontierEntry1591Native.forward base) (Rolling1588.stackForward true)
      (skywalkArithmeticClear base) (InverseFour15.stackReverse15 true) s mp mr clearM twice stack

theorem prefix_pool :
    wires (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)⊆(skywalkPoolWires base).toFinset := by
  intro q hq
  apply InverseFour15.last_pool15 true
  simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union] at hq ⊢
  exact Or.inl hq

theorem first_pool (isA : Bool) : wires (Rolling1588.firstPhase isA)⊆(skywalkPoolWires base).toFinset := by
  have h := first_support_eq isA
  simp only [Rolling1588Lifetime.firstPhase] at h
  rw [h]; exact FrontierEntry1591Kernel.first_pool

theorem g_not_pool : base 2400∉skywalkPoolWires base := E1QubitPlacement.g2400

theorem num_not_pool (q : Wire) (hq : q∈skywalkPoolWires base) : q∉wireBlock base 2056 256 := by
  obtain ⟨i,hi,rfl⟩ := (mem_pool_iff q).mp hq
  intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj; have := base_injective e; omega

theorem kR_pool (q : Wire) (hq : q∈wireBlock base 770 258) : q∈skywalkPoolWires base := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact (mem_pool_iff _).mpr ⟨i,by omega,rfl⟩

theorem rawX (F : Program) (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m : List Bool) (value : Nat) (input : SkywalkArithmeticInput base x y s.basis)
    (fieldResult : ∀mp mf,
      let beforeA := run (Rolling1588.firstPhase false) mp s
      let beforeB := run (Rolling1588.firstPhase true) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      regValue (wireBlock base 770 258) out.basis=negDiv k x (s.basis (base 2400)) ∧
      ∀q,q∉wireBlock base 2056 256 → q∉wireBlock base 770 258 → out.basis q=s.basis q := by
  intro out
  obtain ⟨mp,mf,mr,eqOut⟩ : ∃ mp mf mr,
      out=run (lastX k) mr (run F mf (run (Rolling1588.firstPhase false) mp s)) :=
    ⟨_,_,_,by
      show run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s=_
      rw [FrontierEntry1591Native.kernel,run_append,run_append]⟩
  obtain ⟨r1,r2,r3⟩ := fieldResult mp mf
  generalize hAfter : run F mf (run (Rolling1588.firstPhase false) mp s)=after at eqOut r1 r2 r3
  generalize hBefore : run (Rolling1588.firstPhase true) mp s=beforeB at r1 r2 r3
  have eqOut2 : out=run (x1 k)
      (mr.drop (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)))
      (run (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)
        (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) after) := by
    rw [eqOut,show lastX k=(skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)++x1 k from rfl,
      run_append]
  have agree := pool_run_agrees (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)
    (skywalkPoolWires base).toFinset prefix_pool
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) after beforeB r1
    (fun q hq => r3 q (num_not_pool q (List.mem_toFinset.mp hq)))
  generalize hv : run (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) after=v
    at eqOut2 agree
  have vB := prefix_roundtrip hn hlo x y hx0 hx s mp
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) input
  rw [hBefore] at vB
  rw [vB] at agree
  have xr := x1_run k hk x y hx s v _
    (mr.drop (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) input agree.1
    (fun q hq => agree.2 q (List.mem_toFinset.mpr hq))
  rw [←eqOut2] at xr
  obtain ⟨o1,o2,o3,o4⟩ := xr
  have offA (q : Wire) (hq : q∉skywalkPoolWires base) : v.basis q=after.basis q := by
    rw [←hv]
    exact run_preserves_outside _ _ after q (fun h => hq (List.mem_toFinset.mp (prefix_pool h)))
  have offB (q : Wire) (hq : q∉skywalkPoolWires base) : beforeB.basis q=s.basis q := by
    rw [←hBefore]
    exact run_preserves_outside _ _ s q (fun h => hq (List.mem_toFinset.mp (first_pool true h)))
  have g2056 : base 2400∉wireBlock base 2056 256 := by
    intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj; have := base_injective e; omega
  have gv : v.basis (base 2400)=s.basis (base 2400) := by
    rw [offA _ g_not_pool,r3 _ g2056,offB _ g_not_pool]
  have numOut (q : Wire) (hq : q∈wireBlock base 2056 256) : out.basis q=after.basis q := by
    have np : q∉skywalkPoolWires base := fun h => num_not_pool q h hq
    rw [o4 q np,offA q np]
  refine ⟨o1,?_,?_,?_⟩
  · rw [regValue_congr _ _ after.basis numOut]; exact r2
  · rw [o2,gv]
  · intro q h1 h2
    by_cases hp : q∈skywalkPoolWires base
    · exact o3 q hp h2
    · rw [o4 q hp,offA q hp,r3 q h1,offB q hp]

/-! ### Kernel with the merged exit: hosted form -/

private theorem phase_sites_split' : phaseSites=FrontierEntry1591Native.workSites∪phaseHosts := by
  ext q
  simp only [phaseSites,phaseHosts,FrontierEntry1591Native.workSites,Finset.mem_union,
    List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem rebind (P F Q : Program) (s : State) (m : List Bool)
    (input : ∀q∈phaseSites,s.basis q=false)
    (firstFree : ∀q∈phaseHosts,q∉wires P)
    (firstClean : ∀records,∀q∈FrontierEntry1591Native.workSites,
      (run P records s).basis q=false)
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (lastFree : ∀q∈phaseHosts,q∉wires Q)
    (output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel P F Q) m s).basis q=false) :
    run (renameProgram phaseHost P++(F++renameProgram phaseHost Q)) m s=
      run (FrontierEntry1591Native.kernel P F Q) m s := by
  let mp := m.take (measurementCount P)
  let rest := m.drop (measurementCount P)
  let mf := rest.take (measurementCount F)
  let mr := rest.drop (measurementCount F)
  let before := run P mp s
  let after := run F mf before
  have finalClean : ∀q∈phaseSites,(run Q mr after).basis q=false := by
    simpa only [FrontierEntry1591Native.kernel,run_append] using output
  have lastInput : ∀q∈phaseSites,after.basis q=false := by
    intro q hq
    rw [phase_sites_split'] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact (run_preserves_outside F mf before q (fieldFree q work)).trans (firstClean mp q work)
    · exact (run_preserves_outside Q mr after q (lastFree q host)).symm.trans
        (finalClean q (by rw [phase_sites_split'];exact Finset.mem_union_right _ host))
  have firstOutput : ∀q∈phaseSites,(run P mp s).basis q=false := by
    intro q hq
    rw [phase_sites_split'] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact firstClean mp q work
    · exact (run_preserves_outside P mp s q (firstFree q host)).trans
        (input q (by rw [phase_sites_split'];exact Finset.mem_union_right _ host))
  have first := phase_run_eq P s mp input firstOutput
  have last := phase_run_eq Q after mr lastInput finalClean
  simp only [FrontierEntry1591Native.kernel,run_append,(renameProgram_counts _ _).2]
  rw [first]
  exact last

theorem x1_hosts_free (k : Nat) (q : Wire) (hq : q∈phaseHosts) : q∉wires (x1 k) := by
  intro h
  rw [x1_eq,renameProgram_support] at h
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
  obtain ⟨i,rfl,hi⟩ := E1QubitPlacement.S_cases _ (ExitMerge.program_support base (base 2400) k ha)
  rw [pi_base] at hq
  simp only [phaseHosts,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with e|e|e <;> have := base_injective e <;> unfold piN E1QubitPlacement.rhoN at this <;>
    split_ifs at this <;> omega

theorem lastX_hosts_free (k : Nat) (q : Wire) (hq : q∈phaseHosts) : q∉wires (lastX k) := by
  have old := InverseFour15.last_hosts_free15 true q hq
  simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union,not_or] at old
  simp only [lastX,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨old.1.1,old.1.2⟩,x1_hosts_free k q hq⟩

theorem top_zero (t : BasisState) (h : regValue (wireBlock base 770 258) t < 2^256) :
    ∀q∈wireBlock base 1026 2,t q=false := by
  have sp := E1Merge.kR_x base base_pool_nodup t
  change regValue (wireBlock base 770 258) t=_ at sp
  apply (regValue_zero _ _).mp
  by_contra hne
  have : 1 ≤ regValue (wireBlock base 1026 2) t := Nat.one_le_iff_ne_zero.mpr hne
  have : 2^256 ≤ 2^256*regValue (wireBlock base 1026 2) t := Nat.le_mul_of_pos_right _ this
  omega

theorem negDiv_lt (k x : Nat) (G : Bool) (hx : x < p) : negDiv k x G < p := by
  unfold negDiv; split
  · exact Nat.mod_lt _ (by norm_num [p])
  · exact hx

theorem p_lt : p < 2^256 := by norm_num [p]

theorem sites_not_num (q : Wire) (hq : q∈phaseSites) : q∉wireBlock base 2056 256 := by
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  intro h; obtain ⟨j,hj,e'⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  rcases hq with e|e|e|e|e|e <;> rw [e] at e' <;> have := base_injective e' <;> omega

theorem sites_not_kR (q : Wire) (hq : q∈phaseSites) (h26 : q≠base 1026) : q∉wireBlock base 770 258 := by
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  intro h; obtain ⟨j,hj,e'⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  rcases hq with e|e|e|e|e|e
  · exact h26 e
  all_goals (rw [e] at e'; have := base_injective e'; omega)

theorem hostedX (F : Program) (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m : List Bool) (value : Nat) (input : SkywalkArithmeticInput base x y s.basis)
    (integerBoundary : ∀mn mf,
      run (Rolling1588.stackForward false) mf (run (FrontierEntry1591Native.forward base) mn s)=
        pullState (OB5.sig 511) (run (Rolling1588.allEncode base false 102) []
          (run (W.compactSkywalkForward base 1 511) []
            (run (FrontierEntry1591Native.forward base) mn s))))
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (fieldResult : ∀mp mf,
      let beforeA := run (Rolling1588.firstPhase false) mp s
      let beforeB := run (Rolling1588.firstPhase true) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (renameProgram phaseHost (Rolling1588.firstPhase false)++
      (F++renameProgram phaseHost (lastX k))) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      regValue (wireBlock base 770 258) out.basis=negDiv k x (s.basis (base 2400)) ∧
      ∀q,q∉wireBlock base 2056 256 → q∉wireBlock base 770 258 → out.basis q=s.basis q := by
  have raw := rawX F k hk hn hlo x y hx0 hx s m value input fieldResult
  have clean := caller_phase_clean x y s input
  obtain ⟨o1,o2,o3,o4⟩ := raw
  have output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s).basis q=false := by
    intro q hq
    have hq' := hq
    simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq'
    by_cases h26 : q=base 1026
    · subst h26
      apply top_zero _ (by rw [o3]; exact (negDiv_lt k x _ hx).trans p_lt)
      exact List.mem_map.mpr ⟨1026,by simp only [List.mem_range'_1]; omega,rfl⟩
    · rw [o4 q (sites_not_num q hq) (sites_not_kR q hq h26)]
      exact clean q hq
  have same := rebind (Rolling1588.firstPhase false) F (lastX k) s m clean (first_hosts_free false)
    (fun records => first_clean_of_boundary false hn x y hx0 hx s records input integerBoundary)
    fieldFree (lastX_hosts_free k) output
  dsimp only
  rw [same]
  exact ⟨o1,o2,o3,o4⟩

/-! ### The TickGap exit kernel with the merged exit -/

def kernelX (k : Nat) : Program :=
  renameProgram phaseHost (Rolling1588TickGap.firstPhase false)++
    (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k))

def ExitNegCorrect (K : Program) (k : Nat) : Prop := ∀
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false),
    let out := run K m s
    out.phase=s.phase ∧ regValue (skywalkArithmeticNumerator base) out.basis=centerWord (Y*(x:Fp)/2) ∧
      regValue (skywalkArithmeticDivisor base) out.basis=negDiv k x (s.basis (base 2400)) ∧
      ∀q,q∉skywalkArithmeticNumerator base → q∉skywalkArithmeticDivisor base → out.basis q=s.basis q

private theorem append_run_eq' (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem kernelX_correct (k : Nat) (hk : k < p) : ExitNegCorrect (kernelX k) k := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  have records : measurementCount (renameProgram phaseHost (Rolling1588TickGap.firstPhase false))=
      measurementCount (renameProgram phaseHost (Rolling1588.firstPhase false)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(Rolling1588TickGap.first_metrics false).2.1]
  have eq := append_run_eq' _ _ (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k)) s m records
    (fun r => Rolling1588TickGap.first_hosted_run_eq false hn x Y.val hx0 hx s r input)
  have res := hostedX Rolling1588.exitFieldHosted k hk hn hlo x Y.val hx0 hx s m (centerWord (Y*(x:Fp)/2)) input
    (fun mn mf => Rolling1588.stackForward_boundary false hn hlo x hx0 hx _ mf
      (FrontierEntry1591Native.caller_first_stageW base hn x Y.val hx0 hx s mn input))
    Rolling1588.exitFieldHosted_work_free
    (fun mp mf => Rolling1588.exit_boundary hn hlo ho hf x Y hx0 hx s mp mf input hg hs)
  dsimp only at res ⊢
  rw [kernelX,eq]
  obtain ⟨o1,o2,o3,o4⟩ := res
  have tz := top_zero _ (by rw [o3]; exact (negDiv_lt k x _ hx).trans p_lt)
  have sp := E1Merge.kR_x base base_pool_nodup
    (run (renameProgram phaseHost (Rolling1588.firstPhase false)++
      (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k))) m s).basis
  change regValue (wireBlock base 770 258) _=regValue (wireBlock base 770 256) _+_ at sp
  rw [o3,(regValue_zero _ _).mpr tz] at sp
  refine ⟨o1,o2,by simp only [skywalkArithmeticDivisor]; omega,?_⟩
  intro q h1 h2
  by_cases hk' : q∈wireBlock base 770 258
  · have top : q∈wireBlock base 1026 2 := by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk'
      simp only [List.mem_range'_1] at hi
      refine List.mem_map.mpr ⟨i,?_,rfl⟩
      simp only [List.mem_range'_1]
      by_contra hc
      exact h2 (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)
    rw [tz q top]
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp top
    simp only [List.mem_range'_1] at hi
    exact (input.2.2 _ (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩) h2 h1).symm
  · exact o4 q h1 hk'

/-! ### Point-layout transfer -/

theorem wordTransferX (L : ControlledPointLayout) (f : Wire → Wire) (k : Nat)
    (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool)
    (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain)
    (gSite : base 2400∈domain)
    (X : Nat) (Y : Fp) (R : Nat)
    (s : State) (m : List Bool)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (P : Program) (programSites : wires P⊆domain)
    (P_spec : ∀(t : State)(records : List Bool),
      SkywalkArithmeticInput base X Y.val t.basis →
      t.basis (base 2409)=false → t.basis (base 2410)=false →
      (run P records t).phase=t.phase ∧
      regValue (skywalkArithmeticNumerator base) (run P records t).basis=R ∧
      regValue (skywalkArithmeticDivisor base) (run P records t).basis=negDiv k X (t.basis (base 2400)) ∧
      ∀ q,q∉skywalkArithmeticNumerator base → q∉skywalkArithmeticDivisor base →
        (run P records t).basis q=t.basis q) :
    (run (renameProgram f P) m s).phase=s.phase ∧
    regValue L.point.y (run (renameProgram f P) m s).basis=R ∧
    regValue L.point.x (run (renameProgram f P) m s).basis=negDiv k X (s.basis L.core.generic) ∧
      ∀q,q∉L.point.y → q∉L.point.x → (run (renameProgram f P) m s).basis q=s.basis q := by
  let t := ECDSAAdd.Entrant.selInput domain f s
  have inputBits (q : Wire) (hq : q∈domain) : t.basis q=s.basis (f q) := by
    simp only [t,ECDSAAdd.Entrant.selInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : t.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val t.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) t.basis=X
      rw [ECDSAAdd.Entrant.selRegMap f _ t.basis s.basis
        (fun q hq => inputBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hX
    · change regValue (wireBlock base 2056 256) t.basis=Y.val
      rw [ECDSAAdd.Entrant.selRegMap f _ t.basis s.basis
        (fun q hq => inputBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hY
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [t,ECDSAAdd.Entrant.selInput,if_neg used]
  have strong := P_spec t m input (zero _ selectorG) (zero _ selectorS)
  have transfer := run_rename_pool f domain injective P programSites m t s rfl inputBits
  have tg : t.basis (base 2400)=s.basis L.core.generic := by rw [inputBits _ gSite,controlMap]
  refine ⟨transfer.1.trans strong.1,?_,?_,?_⟩
  · rw [←numeratorMap]
    exact (ECDSAAdd.Entrant.selRegMap f _ (run P m t).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · rw [←divisorMap,←tg]
    exact (ECDSAAdd.Entrant.selRegMap f _ (run P m t).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dxSites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.2.1
  · intro q outY outX
    by_cases image : q∈domain.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      have awayY : a∉skywalkArithmeticNumerator base := by
        intro mem; apply outY; rw [←numeratorMap]; exact List.mem_map.mpr ⟨a,mem,rfl⟩
      have awayX : a∉skywalkArithmeticDivisor base := by
        intro mem; apply outX; rw [←divisorMap]; exact List.mem_map.mpr ⟨a,mem,rfl⟩
      exact (transfer.2 a ha).trans ((strong.2.2.2 a awayY awayX).trans (inputBits a ha))
    · exact run_rename_pool_outside f domain P programSites m s q image

theorem lx_support (k : Nat) : wires (lastX k) ⊆ wires (Rolling1588.lastPhase true) ∪ wires (x1 k) := by
  intro q hq
  simp only [lastX,wires_append,Finset.mem_union] at hq
  rcases hq with (hc | hs) | hx
  · have h : q ∈ wires (InverseFour15.lastPhase15 true) := by
      simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union]
      exact Or.inl (Or.inl hc)
    rcases Finset.mem_union.mp (InverseFour15.last_extra15 true h) with old | extra
    · exact Finset.mem_union_left _ old
    · simp only [Finset.mem_singleton] at extra
      subst q
      exact Finset.mem_union_right _ (x1_has530x k)
  · have h : q ∈ wires (InverseFour15.lastPhase15 true) := by
      simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union]
      exact Or.inl (Or.inr hs)
    rcases Finset.mem_union.mp (InverseFour15.last_extra15 true h) with old | extra
    · exact Finset.mem_union_left _ old
    · simp only [Finset.mem_singleton] at extra
      subst q
      exact Finset.mem_union_right _ (x1_has530x k)
  · exact Finset.mem_union_right _ hx

theorem x1_logical (k : Nat) : wires (x1 k)⊆(E1QubitPlacement.S).image pi := by
  rw [x1_eq,renameProgram_support]
  exact Finset.image_subset_image (ExitMerge.program_support base (base 2400) k)

theorem host_pi (q : Wire) : phaseHost (pi q)=E1QubitPlacement.sig (E1QubitPlacement.rho q) := rfl

theorem hostedX1_logical (k : Nat) :
    wires (renameProgram phaseHost (x1 k))⊆OB5Support.logicalSites := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (x1_logical k ha)
  obtain ⟨i,rfl,hi⟩ := E1QubitPlacement.S_cases b hb
  rw [host_pi,E1QubitPlacement.rho_base,E1QubitPlacement.sig_base]
  exact E1QubitPlacement.sw_logical _ (E1QubitPlacement.rhoN_range i hi)

theorem kernelX_support (k : Nat) : wires (kernelX k)⊆OB5Support.logicalSites := by
  have old := Rolling1588TickGap.exitKernel_support
  intro q hq
  simp only [kernelX,wires_append,Finset.mem_union,renameProgram_support] at hq
  simp only [Rolling1588TickGap.exitKernel,Rolling1588TickGap.kernel,wires_append,
    renameProgram_support] at old
  rcases hq with h|h|h
  · exact old (Finset.mem_union_left _ h)
  · exact old (Finset.mem_union_right _ (Finset.mem_union_left _ h))
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    rcases Finset.mem_union.mp (lx_support k ha) with h1|h1
    · exact old (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,h1,rfl⟩)))
    · exact hostedX1_logical k (by rw [renameProgram_support]; exact Finset.mem_image.mpr ⟨a,h1,rfl⟩)

def HalfMultiplyNegCorrect (L : ControlledPointLayout) (P : Program) (k : Nat) : Prop :=
  ∀(X Y : Nat),X < p → 0 < X → Y < p → ∀(s : State)(m : List Bool),
    regValue L.point.x s.basis=X → regValue L.point.y s.basis=Y → regValue L.dialogPool s.basis=0 →
    (run P m s).phase=s.phase ∧
    regValue L.point.y (run P m s).basis=centerWord (((Y:Fp)*(X:Fp))/2) ∧
    regValue L.point.x (run P m s).basis=negDiv k X (s.basis L.core.generic) ∧
    ∀q,q∉L.point.y → q∉L.point.x → (run P m s).basis q=s.basis q

theorem exitX_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k < p) :
    HalfMultiplyNegCorrect L (FrontierEntry1591Callers.exit (kernelX k) L) k := by
  intro X Y hX hX0 hY s m hx hy hc
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  rcases placement2 L hw hn with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,
    selectorG,selectorS,zeroFlag⟩
  have dx : (wireBlock base 770 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have dy : (wireBlock base 2056 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have gSite : base 2400∈OB5Support.logicalSites := by
    have := E1QubitPlacement.sw_logical 2400 (by unfold E1QubitPlacement.Rng; omega)
    simpa [E1QubitPlacement.sw] using this
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have result := wordTransferX L (wireFn2 L) k OB5Support.logicalSites
    (fun a ha b hb eq => injective a (ArithmeticOB5.logical_sub_old ha) b
      (ArithmeticOB5.logical_sub_old hb) eq)
    divisorMap numeratorMap controlMap
    (fun q hq used hx hy => sharedWork q hq (ArithmeticOB5.logical_sub_old used) hx hy)
    selectorG selectorS dx dy gSite X (Y:Fp) (centerWord (((Y:Fp)*(X:Fp))/2))
    s m hx (hy.trans yValue.symm) hc
    (kernelX k) (kernelX_support k)
    (fun t records input hg hs => kernelX_correct k hk
      config.1 above config.2.1 config.2.2 X (Y:Fp) hX0 hX t records input hg hs)
  simpa only [FrontierEntry1591Callers.exit] using result

private theorem sub_val'' (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

/-! ### Point step: the multiplication kernel with the merged negation, then `exitY` -/

theorem fusedMultiplyX_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (P++ExitFusionResearch.exitY L k)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin) := by
  intro s m v
  let n := measurementCount P
  let a := run P (m.take n) s
  have hp : 0 < X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have half := correct X.val Y.val X.isLt hp Y.isLt s (m.take n) v.x v.y v.clean
  have poolY (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.y :=
    fun h => finPool_not_xy L hn q hq (List.mem_append_right _ h)
  have poolX (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    fun h => finPool_not_xy L hn q hq (List.mem_append_left _ h)
  have genY : L.core.generic∉L.point.y :=
    fun h => finGeneric_not_xy L hn (List.mem_append_right _ h)
  have genX : L.core.generic∉L.point.x :=
    fun h => finGeneric_not_xy L hn (List.mem_append_left _ h)
  have ag : a.basis L.core.generic=G := (half.2.2.2 _ genY genX).trans v.generic
  have ac : regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq => half.2.2.2 q (poolY q hq) (poolX q hq)),v.clean]
  have av : regValue L.point.y a.basis=centerWord ((Y*X)/2) := by
    simpa only [ZMod.natCast_zmod_val] using half.2.1
  have out := ExitFusionResearch.exitY_correct L hw hn ((Y*X)/2) k a (m.drop n) av ac
  let b := run (ExitFusionResearch.exitY L k) (m.drop n) a
  have phase : b.phase=s.phase := out.1.trans half.1
  have xy (q : Wire) (hq : q∈L.point.x) : q∉L.point.y := by
    intro h
    have nd := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have p1 := List.count_pos_iff.mpr hq
    have p2 := List.count_pos_iff.mpr h
    simp only [ControlledPointLayout.dialogUsedWires,PointAddLayout.pointWires,List.count_append,
      List.count_cons] at nd
    omega
  have frame (q : Wire) (hy : q∉L.point.y) (hx : q∉L.point.x) : b.basis q=s.basis q :=
    (out.2.2 q hy).trans (half.2.2.2 q hy hx)
  have twice : 2*((Y*X)/2)=Y*X := by
    have two : (2:Fp)≠0 := by decide
    field_simp
  have bv : regValue L.point.y b.basis=(Y*X-(if G then k else 0)).val := by
    rw [out.2.1,ag,twice]
  have bx : regValue L.point.x b.basis=(if G then cx-X else X).val := by
    rw [regValue_congr _ _ a.basis (fun q hq => out.2.2 q (xy q hq)),half.2.2.1,v.generic]
    cases G
    · rfl
    · simp only [negDiv,if_true]; rw [sub_val'']
  rw [run_append]
  change b.phase=s.phase ∧ PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin b.basis
  refine ⟨phase,bx,bv,?_,?_,?_⟩
  · exact (frame _ genY genX).trans v.generic
  · rw [←v.clean]
    exact regValue_congr _ _ _ (fun q hq => frame q (poolY q hq) (poolX q hq))
  · intro q hq
    exact (frame q (fun h => hq (List.mem_append_right _ h)) (fun h => hq (List.mem_append_left _ h))).trans
      (v.rest q hq)

def restXX (L : ControlledPointLayout) (k : Nat) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase false)++
      (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k)))

theorem exit_splitX (L : ControlledPointLayout) (k : Nat) :
    FrontierEntry1591Callers.exit (kernelX k) L=E1QubitPlacement.tickF L++restXX L k := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,kernelX,Rolling1588TickGap.firstPhase,restXX,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

/-! ### Resources of the merged exit inside the stage -/

theorem x1_counts (k : Nat) : toffoliCount (x1 k)=767 ∧ measurementCount (x1 k)=1027 := by
  rw [x1_eq,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  exact ExitMerge.program_counts base (base 2400) k

theorem x1_slots (k : Nat) : Challenge.gateSlots (x1 k) ≤ 22000 := by
  rw [x1_eq,Baselines.rename_gateSlots]
  exact ExitMerge.program_slots base (base 2400) k

theorem x1_physical (k : Nat) : GatePhysical (x1 k) := by
  rw [x1_eq]
  exact gatePhysical_rename pi pi.injective _
    (ExitMerge.program_physical base (base 2400) base_pool_nodup E1QubitPlacement.g2400 k)

theorem restXX_metrics (L : ControlledPointLayout) (k : Nat) :
    toffoliCount (restXX L k)+255=toffoliCount (ReflectionE1TickGap.restX L)+769 ∧
    measurementCount (restXX L k)+508=measurementCount (ReflectionE1TickGap.restX L)+1027 ∧
    Challenge.gateSlots (restXX L k) ≤ Challenge.gateSlots (ReflectionE1TickGap.restX L)+23084 := by
  have c := x1_counts k
  have rev := InverseFour15.reverse_metrics_new true
  have sl := x1_slots k
  have i := FrontierEntry1591NativeH.counts base
  simp only [restXX,ReflectionE1TickGap.restX,lastX,Rolling1588.lastPhase,toffoliCount_append,
    measurementCount_append,Challenge.gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

theorem restXX_support (L : ControlledPointLayout) (k : Nat) :
    wires (restXX L k)⊆wires (ReflectionE1TickGap.restX L)∪
      wires (renameProgram (wireFn2 L) (renameProgram phaseHost (x1 k))) := by
  have sub := Finset.image_subset_image (f := wireFn2 L) (Finset.image_subset_image (f := phaseHost) (lx_support k))
  simp only [Finset.image_union] at sub
  intro q hq
  simp only [restXX,ReflectionE1TickGap.restX,renameProgram_support,
    wires_append,Finset.image_union,Finset.mem_union] at hq ⊢
  have imp : q ∈ ((wires (lastX k)).image phaseHost |>.image (wireFn2 L)) →
      q ∈ ((wires (Rolling1588.lastPhase true)).image phaseHost |>.image (wireFn2 L)) ∨
        q ∈ ((wires (x1 k)).image phaseHost |>.image (wireFn2 L)) := by
    intro h
    exact Finset.mem_union.mp (sub h)
  tauto
theorem placedX1_sites (L : ControlledPointLayout) (hw : L.Widths) (k : Nat) :
    wires (renameProgram (wireFn2 L) (renameProgram phaseHost (x1 k)))⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ (hostedX1_logical k)

theorem hostedX1_labels (k : Nat) (q : Wire) (hq : q∈wires (renameProgram phaseHost (x1 k))) :
    ∃ j, q=base (E1QubitPlacement.sw (E1QubitPlacement.rhoN j)) ∧
      (j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨ j=721 ∨ j=722 ∨ j=2400) := by
  rw [renameProgram_support] at hq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (x1_logical k ha)
  obtain ⟨j,rfl,hj⟩ := E1QubitPlacement.S_cases b hb
  exact ⟨j,by rw [host_pi,E1QubitPlacement.rho_base,E1QubitPlacement.sig_base],hj⟩

theorem kernelX_physical (k : Nat) : GatePhysical (kernelX k) := by
  have old := Rolling1588TickGap.exitKernel_physical
  simp only [Rolling1588TickGap.exitKernel,Rolling1588TickGap.kernel,gatePhysical_append] at old
  have last := InverseFour15.last_physical15 true
  simp only [InverseFour15.lastPhase15,gatePhysical_append] at last
  have lx : GatePhysical (lastX k) := by
    simp only [lastX,gatePhysical_append]; exact ⟨last.1,x1_physical k⟩
  simp only [kernelX,gatePhysical_append]
  exact ⟨old.1,old.2.1,gatePhysical_rename phaseHost phaseHost.injective _ lx⟩

theorem restXX_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Nat) :
    GatePhysical (restXX L k) := by
  have physical := FrontierEntry1591Native.placed_physical L hw hn (kernelX k) (kernelX_support k)
    (kernelX_physical k)
  have e : GatePhysical (FrontierEntry1591Callers.exit (kernelX k) L) := by
    unfold FrontierEntry1591Callers.exit; exact physical
  rw [exit_splitX,gatePhysical_append] at e
  exact e.2

theorem sw760 (j : Nat)
    (hj : j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨ j=721 ∨ j=722 ∨ j=2400) :
    E1QubitPlacement.sw (E1QubitPlacement.rhoN j)≠760 := by
  have range:=E1QubitPlacement.rhoN_range j hj
  generalize E1QubitPlacement.rhoN j=i at range ⊢
  unfold E1QubitPlacement.Rng at range
  unfold E1QubitPlacement.sw
  split_ifs <;> omega

theorem kernelX_760_free (k : Nat) : base 760∉wires (kernelX k) := by
  have old := Rolling1588TickGap.exitKernel_760_free
  simp only [Rolling1588TickGap.exitKernel,Rolling1588TickGap.kernel,wires_append,
    renameProgram_support,Finset.mem_union,not_or] at old
  simp only [kernelX,wires_append,renameProgram_support,Finset.mem_union,not_or]
  refine ⟨old.1,old.2.1,?_⟩
  intro h
  obtain ⟨a,ha,e⟩ := Finset.mem_image.mp h
  rcases Finset.mem_union.mp (lx_support k ha) with h1|h1
  · exact old.2.2 (Finset.mem_image.mpr ⟨a,h1,e⟩)
  · obtain ⟨j,e',hj⟩ := hostedX1_labels k (phaseHost a) (by
      rw [renameProgram_support]; exact Finset.mem_image.mpr ⟨a,h1,rfl⟩)
    rw [e] at e'
    exact sw760 j hj (base_injective e').symm

end ECDSAAdd.Entrant.ExitMergeKernel

end -- exit merge section


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end


set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Generic =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1TickGapFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Low48Square

/-! Keep the checked E1 entries and TickGap tails. Replace only the reflected square prefix. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1TickGapLow48
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def squareEntry (L : ControlledPointLayout) (k : Fp) : Program :=
  R2SqEp760.program760 L++E1ReflectedPlacement.entryR L k

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  squareEntry L k++ReflectionE1TickGap.restX L++exitY L cy


theorem squareEntry_base (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m1 m2 : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (squareEntry L k) m1 s=
      run (SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++
        E1QubitPlacement.tickF L) m2 s := by
  let n1:=measurementCount (R2SqEp760.program760 L)
  let n2:=measurementCount (SquareCarryLoan719BF.program L)
  obtain ⟨a,ha⟩ : ∃a : State,run (R2SqEp760.program760 L) (m1.take n1) s=a := ⟨_,rfl⟩
  obtain ⟨r,hr⟩ : ∃r : State,run (SquareCarryLoan719BF.program L) (m2.take n2) s=r := ⟨_,rfl⟩
  have fresh:=R2SqEp760.program760_boundary L hw hn X Y G origin s (m1.take n1) v
  have prior:=SquareCarryLoan719BF.step L hw hn X Y G origin s (m2.take n2) v
  rw [ha] at fresh
  rw [hr] at prior
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  let R:=p-1-Z.val
  have ppos : 0<p := by norm_num [p]
  have rp : R<p := by
    change p-1-Z.val<p
    omega
  have ax : regValue L.point.x a.basis=R:=fresh.2.1
  have ag : a.basis L.core.generic=G :=
    (fresh.2.2 _ (((E1QubitPlacement.lay L hw hn _).2.2 rfl).1)).trans v.generic
  have ac : regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ s.basis
      (fun q hq=>fresh.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).1)),v.clean]
  have involution (n : Nat) (bound : n<p) : n=p-1-(p-1-n) := by omega
  have rx : regValue L.point.x r.basis=p-1-R := by
    have value : regValue L.point.x r.basis=Z.val:=prior.2.x
    exact value.trans (involution Z.val Z.isLt)
  have outside (q : Wire) (hq : q∉L.point.x) : r.basis q=a.basis q := by
    have oldFrame : r.basis q=s.basis q := by
      by_cases hy : q∈L.point.y
      · exact (regValue_eq_iff _ _ _).mp (prior.2.y.trans v.y.symm) q hy
      · have away : q∉L.point.x++L.point.y:=by simp only [List.mem_append,not_or];exact ⟨hq,hy⟩
        exact (prior.2.rest q away).trans (v.rest q away).symm
    exact oldFrame.trans (fresh.2.2 q hq).symm
  have eq:=E1ReflectedPlacement.entryR_eq L hw hn k a r R rp G ax ag ac
    (prior.1.trans fresh.1.symm) rx outside (m1.drop n1) (m2.drop n2)
  simpa only [squareEntry,run_append,n1,n2,ha,hr,List.append_assoc] using eq

theorem squareEntry_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (mNew mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (squareEntry L k) mNew s=run (ReflectionE1.squareEntry L k) mOld s :=
  (squareEntry_base L hw hn k X Y G origin s mNew [] v).trans
    (ReflectionE1.squareEntry_eq L hw hn k X Y G origin s mOld [] v).symm

section CorrectStages
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem secondStage_step (X Y k cy : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStage L k cy)
      (PointDialogValues L Z (Y*Z-(if G then cy else 0)) G origin) := by
  have prior:=ReflectionE1TickGap.secondStage_step L hw hn X Y k cy G origin hx
  simp only [secondStage,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k) (B:=ReflectionE1.squareEntry L k)
    (R:=ReflectionE1TickGap.restX L++exitY L cy)
  · intro s v m1 m2
    exact squareEntry_eq L hw hn k X Y G origin s m1 m2 v
  · simpa only [ReflectionE1TickGap.secondStage,List.append_assoc] using prior

end CorrectStages

/-- The second stage with the last reverse tick and the trailing constant negation merged. -/
def secondStageX (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  squareEntry L k++ExitMergeKernel.restXX L cx.val++exitY L cy

section CorrectStagesX
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem secondStageX_step (X Y k cy cx : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStageX L k cy cx)
      (PointDialogValues L (if G then cx-Z else Z) (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=ExitMergeKernel.fusedMultiplyX_step L hw hn
    (FrontierEntry1591Callers.exit (ExitMergeKernel.kernelX cx.val) L) cx
    (ExitMergeKernel.exitX_correct L hw hn cx.val cx.isLt)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStageX,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=ExitMergeKernel.restXX L cx.val++exitY L cy)
  · intro s v m1 m2
    exact squareEntry_base L hw hn k X Y G origin s m1 m2 v
  · simpa only [ExitMergeKernel.exit_splitX,List.append_assoc,Z] using prior

end CorrectStagesX

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ReflectionE1TickGap.entryStage L (-cx) (-cy)++secondStageX L (ReflectionE1.correction cx) cy cx

def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clrF L++renameProgram (swapF L) (generic L cx cy)++clrF L

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  zrep L++mid L cx cy++zrep L

theorem gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    gen L cx cy=GenericQ5Geometry.wrapG L (generic L cx cy) := rfl

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=ReflectionE1TickGap.entryStage_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStageX_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy cx true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring,
    show a*d-cy=genericY X Y cx cy from hv.2.2] at second
  exact first.seq second

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=ReflectionE1TickGap.entryStage_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStageX_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy cx false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second
  rw [back] at second
  exact first.seq second


theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
        L.point.finite ^^ decide (X'.val ≠ 5)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    have mid := midFFused_values L hw hn cx cy 5 0 5 0 false s.basis false
      (fun base' => generic_false L hw hn 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2 := zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (x.val ≠ 5) = true := decide_eq_true (val_ne_five hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide ((genericX x y cx cy).val ≠ 5) = true :=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end Correct

attribute [local irreducible] squareEntry secondStage generic mid gen
  ReflectionE1.squareEntry ReflectionE1Square.program ReflectionE1Low48Square.program
  ReflectionE1TickGap.entryStage ReflectionE1TickGap.secondStage ReflectionE1TickGap.restX
  ReflectionE1TickGap.generic ReflectionE1TickGap.gen

private theorem relation_of_shapes (R : Program→Program→Prop) (P Q A B : Program)
    (left : P=A) (right : Q=B) (fact : R A B) : R P Q := by
  cases left
  cases right
  exact fact

private theorem fact_of_shape (R : Program→Prop) (P Q : Program)
    (shape : P=Q) (fact : R Q) : R P := by
  cases shape
  exact fact

private def Facts (P Q : Program) : Prop :=
  toffoliCount P+3278=toffoliCount Q ∧ measurementCount P+323=measurementCount Q ∧
    gateSlots P≤gateSlots Q+23084

private def context (A P B : Program) : Program := A++(P++B)

private theorem context_facts2 (A P Q B B' : Program)
    (h : toffoliCount P+3026=toffoliCount Q ∧ measurementCount P+75=measurementCount Q ∧
      gateSlots P≤gateSlots Q)
    (h' : toffoliCount B+252=toffoliCount B' ∧ measurementCount B+248=measurementCount B' ∧
      gateSlots B≤gateSlots B'+23084) :
    Facts (context A P B) (context A Q B') := by
  rcases h with ⟨ht,hm,hs⟩
  rcases h' with ⟨ht',hm',hs'⟩
  simp only [Facts,context,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem context_wires (A P Q B : Program) :
    wires (context A P B)⊆wires (context A Q B)∪wires P := by
  intro q hq
  simp only [context,wires_append,Finset.mem_union] at hq ⊢
  tauto

private def suffix (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  E1ReflectedPlacement.entryR L (ReflectionE1.correction cx)++ReflectionE1TickGap.restX L++
    exitY L cy++fastConstNeg L cx

/-- The new suffix: the multiplication kernel ends in the merged exit, no trailing negation. -/
private def suffixX (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  E1ReflectedPlacement.entryR L (ReflectionE1.correction cx)++ExitMergeKernel.restXX L cx.val++
    exitY L cy

private theorem generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy=context (ReflectionE1TickGap.entryStage L (-cx) (-cy))
      (R2SqEp760.program760 L) (suffixX L cx cy) := by
  unfold generic secondStageX squareEntry context suffixX
  simp only [List.append_assoc]

private theorem suffix_facts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (suffixX L cx cy)+252=toffoliCount (suffix L cx cy) ∧
    measurementCount (suffixX L cx cy)+248=measurementCount (suffix L cx cy) ∧
    gateSlots (suffixX L cx cy)≤gateSlots (suffix L cx cy)+23084 := by
  have r := ExitMergeKernel.restXX_metrics L cx.val
  have n := fastConstNeg_counts L hw cx
  simp only [suffixX,suffix,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem old_generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    ReflectionE1TickGap.generic L cx cy=context (ReflectionE1TickGap.entryStage L (-cx) (-cy))
      (ReflectionE1Square.program L) (suffix L cx cy) := by
  unfold ReflectionE1TickGap.generic ReflectionE1TickGap.secondStage ReflectionE1.squareEntry context suffix
  simp only [List.append_assoc]

private theorem generic_facts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Facts (generic L cx cy) (ReflectionE1TickGap.generic L cx cy) := by
  exact relation_of_shapes Facts _ _ _ _ (generic_shape L cx cy) (old_generic_shape L cx cy)
    (context_facts2 (ReflectionE1TickGap.entryStage L (-cx) (-cy)) _ _ (suffixX L cx cy) (suffix L cx cy)
      ⟨(R2SqEp760.counts_diff760 L hw).1,(R2SqEp760.counts_diff760 L hw).2,R2SqEp760.slots_le760 L hw⟩
      (suffix_facts L hw cx cy))

/-- The new square adds its host site; the merged exit adds only its placed circuit. -/
theorem generic_support_envelope (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (ReflectionE1TickGap.generic L cx cy)∪wires (R2SqEp760.program760 L)∪
      wires (renameProgram (wireFn2 L) (renameProgram Rolling1588Lifetime.phaseHost
        (ExitMergeKernel.x1 cx.val))) := by
  rw [generic_shape,old_generic_shape]
  intro q hq
  have rx := ExitMergeKernel.restXX_support L cx.val
  simp only [context,suffixX,suffix,wires_append,Finset.mem_union] at hq ⊢
  rcases hq with h|h|(h|h)|h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inr h)
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl h))))))
  · rcases Finset.mem_union.mp (rx h) with h'|h'
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h'))))))
    · exact Or.inr h'
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr h)))))

private def logicalTargetX (i : Nat) : Nat :=
  if i=1800 then 2312 else if i=770 then 1026 else if i=1285 then 1541 else
    if i=1286 then 1542 else if i=769 then 1797 else i

private theorem target_factsX (L : ControlledPointLayout) (i : Nat)
    (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    wireFn2 L (base (logicalTargetX i))=L.core.poolWire i ∧
    base (logicalTargetX i)∈OB5Support.logicalSites ∧
    logicalTargetX i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals refine ⟨rfl,?_,by decide⟩
  all_goals
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨_,?_,rfl⟩
    simp only [logicalTargetX,OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    norm_num

private theorem placedX1_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (renameProgram (wireFn2 L) (renameProgram Rolling1588Lifetime.phaseHost
      (ExitMergeKernel.x1 k))) := by
  obtain ⟨map,logical,target⟩:=target_factsX L i hi
  rw [renameProgram_support]
  intro used
  obtain ⟨q,hq,eq⟩:=Finset.mem_image.mp used
  have same : wireFn2 L q=wireFn2 L (base (logicalTargetX i)):=eq.trans map.symm
  have back:=(placement2 L hw hn).injectiveOnSlots q
    (ArithmeticOB5.logical_sub_old (ExitMergeKernel.hostedX1_logical k hq)) (base (logicalTargetX i))
    (ArithmeticOB5.logical_sub_old logical) same
  rw [back] at hq
  obtain ⟨j,e,hj⟩ := ExitMergeKernel.hostedX1_labels k _ hq
  exact E1QubitPlacement.sw_avoid j hj (base_injective e ▸ target)

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (generic_support_envelope L cx cy).trans (Finset.union_subset (Finset.union_subset
    (ReflectionE1TickGap.generic_sites L hw hn cx cy) (R2SqEp760.program760_support L hw hn))
    (ExitMergeKernel.placedX1_sites L hw cx.val))

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) := by
  intro used
  rcases Finset.mem_union.mp (generic_support_envelope L cx cy used) with old|x
  · rcases Finset.mem_union.mp old with old|sq
    · exact ReflectionE1TickGap.generic_free L hw hn cx cy i hi old
    · exact R2SqEp760.program760_free_old L hw hn i hi sq
  · exact placedX1_free L hw hn cx.val i hi x

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old:=fact_of_shape GatePhysical _ _ (old_generic_shape L cx cy).symm
    (ReflectionE1TickGap.generic_physical L hw hn cx cy)
  have rx := ExitMergeKernel.restXX_physical L hw hn cx.val
  simp only [context,suffix,gatePhysical_append] at old
  rw [generic_shape]
  simp only [context,suffixX,gatePhysical_append]
  exact ⟨old.1,R2SqEp760.program760_physical L hw hn,⟨old.2.2.1.1.1,rx⟩,old.2.2.1.2⟩

private def wrapContext (Z C : Program) (f : Wire→Wire) (P : Program) : Program :=
  Z++(C++renameProgram f P++C)++Z

private theorem wrap_facts (Z C : Program) (f : Wire→Wire) (P Q : Program) (h : Facts P Q) :
    Facts (wrapContext Z C f P) (wrapContext Z C f Q) := by
  rcases h with ⟨ht,hm,hs⟩
  simp only [Facts,wrapContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_facts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Facts (gen L cx cy) (ReflectionE1TickGap.gen L cx cy) := by
  apply relation_of_shapes Facts _ _
    (wrapContext (zrep L) (clrF L) (swapF L) (generic L cx cy))
    (wrapContext (zrep L) (clrF L) (swapF L) (ReflectionE1TickGap.generic L cx cy))
  · unfold gen mid wrapContext
    rfl
  · unfold ReflectionE1TickGap.gen ReflectionE1TickGap.mid wrapContext
    rfl
  · exact wrap_facts _ _ _ _ _ (generic_facts L hw cx cy)

theorem gen_metrics (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+3278=toffoliCount (ReflectionE1TickGap.gen L cx cy) ∧
    measurementCount (gen L cx cy)+323=measurementCount (ReflectionE1TickGap.gen L cx cy) ∧
    gateSlots (gen L cx cy)≤gateSlots (ReflectionE1TickGap.gen L cx cy)+23084 :=
  ⟨(gen_facts L hw cx cy).1,(gen_facts L hw cx cy).2.1,(gen_facts L hw cx cy).2.2⟩

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (generic_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have g:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append] using And.intro (And.intro z (And.intro (And.intro c g) c)) z

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1588 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp)) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

private theorem wrapper_facts (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Facts P Q) :
    toffoliCount (Edges.wrapper L C cy P)+3278=toffoliCount (Edges.wrapper L C cy Q) ∧
    measurementCount (Edges.wrapper L C cy P)+323=measurementCount (Edges.wrapper L C cy Q) ∧
    gateSlots (Edges.wrapper L C cy P)≤gateSlots (Edges.wrapper L C cy Q)+23084 := by
  rcases h with ⟨ht,hm,hs⟩
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2148004 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout layout_widths cx cy)).1
  have old:=ReflectionE1TickGap.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1498893 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout layout_widths cx cy)).2.1
  have old:=ReflectionE1TickGap.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50214293+Rolling1588.slotGrowth := by
  have diff:=(wrapper_facts layout C cy _ _ (gen_facts layout layout_widths cx cy)).2.2
  have old:=ReflectionE1TickGap.wrapper_slots C cx cy
  omega

end ECDSAAdd.Entrant.ReflectionE1TickGapLow48
end -- original module boundary

-- ===== R2 (retired poolWire 760) =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000


/-! ### R2: the retired pool wire `poolWire 760` is absent from the final generic point program. -/
namespace ECDSAAdd.Entrant.R2Final760
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] wires

theorem logical760 : base 760∈OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨760,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  omega

theorem placed_760 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (K : Program) (ks : wires K⊆OB5Support.logicalSites) (kf : base 760∉wires K) :
    L.core.poolWire 760∉wires (renameProgram (wireFn2 L) K) := by
  have map : wireFn2 L (base 760)=L.core.poolWire 760 := rfl
  rw [renameProgram_support]
  intro used
  obtain ⟨old,oldUsed,eq⟩:=Finset.mem_image.mp used
  have mapped : wireFn2 L old=wireFn2 L (base 760) := by rw [map];exact eq
  have back:=(placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (ks oldUsed)) (base 760)
    (ArithmeticOB5.logical_sub_old logical760) mapped
  exact kf (back ▸ oldUsed)

private theorem sw_rho_760 (j : Nat)
    (hj : j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨
      j=721 ∨ j=722 ∨ j=2400) :
    E1QubitPlacement.sw (E1QubitPlacement.rhoN j)≠760 := by
  have range:=E1QubitPlacement.rhoN_range j hj
  generalize E1QubitPlacement.rhoN j=i at range ⊢
  unfold E1QubitPlacement.Rng at range
  unfold E1QubitPlacement.sw
  split_ifs <;> omega

theorem entryM_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    L.core.poolWire 760∉wires (E1QubitPlacement.entryM L k) := by
  rw [E1QubitPlacement.entryM_eq]
  apply placed_760 L hw hn _ (E1QubitPlacement.logicalM k.val)
  intro h
  obtain ⟨j,e,hj⟩ := E1QubitPlacement.merged_labels k.val (base 760) h
  exact sw_rho_760 j hj (base_injective e).symm

private theorem reflected_logical (k : Nat) :
    wires (renameProgram E1QubitPlacement.sig (renameProgram E1QubitPlacement.rho
      (E1Reflected.merged base (base 2400) k)))⊆OB5Support.logicalSites := by
  intro q hq
  simp only [renameProgram_support,Finset.mem_image] at hq
  obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩:=hq
  obtain ⟨j,rfl,hj⟩:=E1QubitPlacement.S_cases b (E1ReflectedPlacement.mergedR_S k hb)
  rw [E1QubitPlacement.rho_base,E1QubitPlacement.sig_base]
  exact E1QubitPlacement.sw_logical _ (E1QubitPlacement.rhoN_range j hj)

theorem entryR_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    L.core.poolWire 760∉wires (E1ReflectedPlacement.entryR L k) := by
  have logicalFree : base 760∉wires (renameProgram E1QubitPlacement.sig (renameProgram E1QubitPlacement.rho
      (E1Reflected.merged base (base 2400) k.val))) := by
    intro h
    simp only [renameProgram_support,Finset.mem_image] at h
    obtain ⟨a,⟨b,hb,rfl⟩,eq⟩ := h
    obtain ⟨j,rfl,hj⟩ := E1QubitPlacement.S_cases b (E1ReflectedPlacement.mergedR_S k.val hb)
    rw [E1QubitPlacement.rho_base,E1QubitPlacement.sig_base] at eq
    exact sw_rho_760 j hj (base_injective eq)
  have h:=placed_760 L hw hn _ (reflected_logical k.val) logicalFree
  simpa only [E1ReflectedPlacement.entryR,renameProgram_comp,E1QubitPlacement.pmapR,
    E1QubitPlacement.pmap,Function.comp_def] using h

private theorem suffix_free (P Q R : Program) (q : Wire) (shape : P=Q++R) (free : q∉wires P) :
    q∉wires R := by
  rw [shape,wires_append] at free
  exact fun h => free (Finset.mem_union_right _ h)

theorem restE_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (kernel : base 760∉wires Rolling1588TickGap.entryKernel) :
    L.core.poolWire 760∉wires (ReflectionE1TickGap.restE L) :=
  suffix_free _ _ _ _ (ReflectionE1TickGap.entry_split L)
    (placed_760 L hw hn _ Rolling1588TickGap.entryKernel_support kernel)

theorem restX_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (kernel : base 760∉wires Rolling1588TickGap.exitKernel) :
    L.core.poolWire 760∉wires (ReflectionE1TickGap.restX L) :=
  suffix_free _ _ _ _ (ReflectionE1TickGap.exit_split L)
    (placed_760 L hw hn _ Rolling1588TickGap.exitKernel_support kernel)

theorem generic_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryK : base 760∉wires Rolling1588TickGap.entryKernel)
    (_exitK : base 760∉wires Rolling1588TickGap.exitKernel)
    (square : L.core.poolWire 760∉wires (R2SqEp760.program760 L)) (cx cy : Fp) :
    L.core.poolWire 760∉wires (ReflectionE1TickGapLow48.generic L cx cy) := by
  have bounds : 515≤760 ∧ 760<2613 := by omega
  have y := ExitGenericQ5.constant_ports_avoid_large L hw hn 760 bounds L.point.y (Or.inr rfl)
  have ey := exitY_support L hw cy
  have fy := fusedY_support L hw (-cy)
  have rx : L.core.poolWire 760∉wires (ExitMergeKernel.restXX L cx.val) :=
    suffix_free _ _ _ _ (ExitMergeKernel.exit_splitX L cx.val)
      (placed_760 L hw hn _ (ExitMergeKernel.kernelX_support cx.val) (ExitMergeKernel.kernelX_760_free cx.val))
  simp only [ReflectionE1TickGapLow48.generic,ReflectionE1TickGap.entryStage,
    ReflectionE1TickGapLow48.secondStageX,ReflectionE1TickGapLow48.squareEntry,
    wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨fun h=>y (fy h),entryM_760_free L hw hn (-cx)⟩,restE_760_free L hw hn entryK⟩,
    ⟨⟨⟨square,entryR_760_free L hw hn _⟩,rx⟩,fun h=>y (ey h)⟩⟩

end ECDSAAdd.Entrant.R2Final760

namespace ECDSAAdd.Entrant.ReflectionE1TickGapLow48
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

theorem generic_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : L.core.poolWire 760∉wires (generic L cx cy) :=
  R2Final760.generic_760_free L hw hn Rolling1588TickGap.entryKernel_760_free
    Rolling1588TickGap.exitKernel_760_free (R2SqEp760.square760_free L hw hn) cx cy

/-- R2: the Low48 point with the lifetime halves and renamed endpoints/square uses 1587 qubits. -/
theorem wrapper_qubits760 (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1587 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits760 _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp))
    (generic_760_free layout layout_widths layout_nodup cx cy) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

end ECDSAAdd.Entrant.ReflectionE1TickGapLow48
end

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Final =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Low48Generic

/-! E1/reflected Q1588 with TickGap tails and the Low48 square prefix. -/
namespace ECDSAAdd.Entrant.ReflectionE1TickGapLow48
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2148004,1498893,1588,50214293+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2148004 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1498893 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50214293+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1498893
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50214293+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C


end ECDSAAdd.Entrant.ReflectionE1TickGapLow48
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1

def sentinel : Nat := 115792089237316195423570985008687907853269984665640564039457584007908834671662
def sentinelHigh : Nat := 452312848583266388373324160190187140051835877600158453279131187530910662655

/-- Bits 1, 2, 5, 10..31 and 33..255 of `v`, packed in this order. -/
def probeVal (v : Nat) : Nat :=
  v / 2 % 4 + 4 * (v / 32 % 2) + 8 * (v / 1024 % 4194304) + 33554432 * (v / 8589934592)

theorem nonresidue_0 : ((115792089237316195423570985008687907853269984665640564039457584007908834671654 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem nonresidue_1 : ((115792089237316195423570985008687907853269984665640564039457584007908834671655 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem nonresidue_2 : ((115792089237316195423570985008687907853269984665640564039457584007908834671662 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem interval_nonresidue (n : Nat)
    (hn : n = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      n = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      n = 115792089237316195423570985008687907853269984665640564039457584007908834671662) :
    ((n : Fp)^3 + 7)^((p-1)/2) = -1 := by
  have hp : 115792089237316195423570985008687907853269984665640564039457584007908834671663 = p := by norm_num [p]
  have he : (p-1)/2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by norm_num [p]
  rw [he]
  have transport (q a : Nat) (hq : q = p)
      (h : ((a : ZMod q)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1) :
      ((a : Fp)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    subst q
    exact h
  rcases hn with rfl | rfl | rfl
  · exact transport _ _ hp nonresidue_0
  · exact transport _ _ hp nonresidue_1
  · exact transport _ _ hp nonresidue_2

theorem curve_x_not_interval {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    ¬ (x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671662) := by
  intro h
  have power := interval_nonresidue x.val h
  rw [ZMod.natCast_zmod_val] at power
  have eq := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at eq
  have square : y^2 = x^3+7 := by simpa [curve,curveA,curveB] using eq
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y ≠ 0 := by
    intro hz
    rw [← square,hz,zero_pow (by decide),zero_pow (by norm_num [p])] at power
    simp at power
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have even : p-1 = 2*((p-1)/2) := by norm_num [p]
  rw [even,pow_mul,square,power] at fermat
  have two : ((2 : Nat) : Fp) = 0 := by
    have sum : (-1 : Fp)+1 = 1+1 := by rw [fermat]
    rw [neg_add_cancel] at sum
    exact_mod_cast (by rw [sum]; norm_num : (2 : Fp) = 0)
  rw [ZMod.natCast_eq_zero_iff] at two
  norm_num [p] at two

theorem probe_cases (v : Nat)
    (hv : v < 115792089237316195423570985008687907853269984665640564039457584007908834671663)
    (h : probeVal v = sentinelHigh) :
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      v = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      v = 115792089237316195423570985008687907853269984665640564039457584007908834671662 := by
  unfold probeVal sentinelHigh at h
  omega

theorem curve_x_high_ne {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    probeVal x.val ≠ sentinelHigh := by
  intro h
  apply curve_x_not_interval hc
  have hv : x.val < 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
    have hp : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by norm_num [p]
    exact lt_of_lt_of_eq (ZMod.val_lt x) hp
  exact probe_cases x.val hv h

theorem sentinel_lt : sentinel < p := by norm_num [sentinel,p]
theorem sentinel_val : (sentinel : Fp).val = sentinel :=
  ZMod.val_natCast_of_lt sentinel_lt
theorem sentinel_ne_zero : (sentinel : Fp) ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  rw [sentinel_val,ZMod.val_zero] at this
  norm_num [sentinel] at this
theorem sentinel_high : probeVal sentinel = sentinelHigh := by
  unfold probeVal sentinel sentinelHigh
  norm_num

end ECDSAAdd.Entrant.FiniteFlagInterval
end

section
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic

theorem drop_sublist_drop (r : List Wire) (a b : Nat) (hab : a ≤ b) : (r.drop b).Sublist (r.drop a) := by
  have e : r.drop b = (r.drop a).drop (b - a) := by
    rw [List.drop_drop]; congr 1; omega
  rw [e]
  exact List.drop_sublist _ _

theorem seg_sublist (r rest : List Wire) (a k : Nat) (h : rest.Sublist (r.drop (a + k))) :
    ((r.drop a).take k ++ rest).Sublist (r.drop a) := by
  have e : (r.drop a).drop k = r.drop (a + k) := by
    rw [List.drop_drop]
  conv_rhs => rw [← List.take_append_drop k (r.drop a)]
  exact List.Sublist.append (List.Sublist.refl _) (e ▸ h)

theorem probe_sublist_gen (r : List Wire) :
    ((r.drop 1).take 2 ++ (r.drop 5).take 1 ++ (r.drop 10).take 22 ++ r.drop 33).Sublist r := by
  simp only [List.append_assoc]
  have hD : (r.drop 33).Sublist (r.drop (10 + 22)) := drop_sublist_drop r _ _ (by omega)
  have hC := seg_sublist r _ 10 22 hD
  have hB := seg_sublist r _ 5 1 ((hC).trans (drop_sublist_drop r _ _ (by omega)))
  have hA := seg_sublist r _ 1 2 ((hB).trans (drop_sublist_drop r _ _ (by omega)))
  exact hA.trans (List.drop_sublist _ _)

theorem probe_value_gen (r : List Wire) (hr : r.length = 256) (s : BasisState) :
    regValue ((r.drop 1).take 2 ++ (r.drop 5).take 1 ++ (r.drop 10).take 22 ++ r.drop 33) s =
      probeVal (regValue r s) := by
  have seg (a k : Nat) (h : a + k ≤ 256) :
      regValue ((r.drop a).take k) s = regValue r s / 2^a % 2^k := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by simp [hr]; omega),
      CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega)]
  have e1 := seg 1 2 (by norm_num)
  have e2 := seg 5 1 (by norm_num)
  have e3 := seg 10 22 (by norm_num)
  have e4 := CuccaroStreamedSquareWideLayout.regValue_drop_div r 33 (by omega) s
  simp only [Arithmetic.regValue_append, List.length_append, List.length_take, List.length_drop, hr,
    e1, e2, e3, e4, probeVal]
  norm_num

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalGadget =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

def probeX (L : ControlledPointLayout) : List Wire :=
  (L.point.x.drop 1).take 2 ++ (L.point.x.drop 5).take 1 ++ (L.point.x.drop 10).take 22 ++ L.point.x.drop 33
def probeControl (L : ControlledPointLayout) : Wire := (probeX L).headD 0
def probeTail (L : ControlledPointLayout) : List Wire := (probeX L).tail
def zrep (L : ControlledPointLayout) : Program :=
  [.X L.point.finite] ++ maskedConstant L.point.finite L.point.x sentinel ++ [.X L.point.finite]
def clrF (L : ControlledPointLayout) : Program :=
  [.X L.point.finite] ++ equalConstant (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw in
theorem probe_length : (probeX L).length = 248 := by
  simp [probeX,show L.point.x.length = 256 from hw.inputX]
include hw in
theorem probe_cons : probeX L = probeControl L :: probeTail L := by
  have h := probe_length L hw
  unfold probeControl probeTail
  cases e : probeX L with
  | nil => simp [e] at h
  | cons a t => rfl
include hw in
theorem probeTail_length : (probeTail L).length = 247 := by
  simp [probeTail,probe_length L hw]
include hw in
theorem probeControl_mem : probeControl L ∈ L.point.x := by
  apply (probe_sublist_gen L.point.x).subset
  change probeControl L ∈ probeX L
  rw [probe_cons L hw]
  simp
theorem probeTail_mem (q : Wire) (hq : q ∈ probeTail L) : q ∈ L.point.x :=
  (probe_sublist_gen L.point.x).subset (show q ∈ probeX L from List.mem_of_mem_tail hq)
include hw in
theorem work_length : (L.dialogPool.take 247).length = 247 := by
  simp [L.dialogPool_length hw]
include hw hn in
theorem probe_nodup :
    (probeControl L :: L.point.finite :: probeTail L ++ L.dialogPool.take 247).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp := (List.take_sublist 247 L.dialogPool).count_le q
  have hx := (probe_sublist_gen L.point.x).count_le q
  have hc := congrArg (List.count q) (probe_cons L hw)
  simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
    List.count_nil,List.cons_append] at h hc ⊢
  change (probeX L).count q ≤ L.point.x.count q at hx
  omega
include hw hn in
theorem finite_ne_probe : L.point.finite ≠ probeControl L := by
  intro h
  apply fin_not_x L hn
  rw [h]
  exact probeControl_mem L hw
include hw in
theorem probe_value_cons (s : BasisState) :
    regValue (probeX L) s = (if s (probeControl L) then 1 else 0) + 2*regValue (probeTail L) s := by
  conv_lhs => rw [probe_cons L hw]
  rfl
include hw in
theorem probe_value (s : BasisState) : regValue (probeX L) s = probeVal (regValue L.point.x s) :=
  probe_value_gen L.point.x hw.inputX s

include hw hn in
theorem clrF_run (s : State) (m : List Bool) (hz : regValue (L.dialogPool.take 247) s.basis = 0) :
    run (clrF L) m s = ⟨s.phase, writeBit s.basis L.point.finite
      (s.basis L.point.finite ^^ decide (regValue (probeX L) s.basis ≠ sentinelHigh))⟩ := by
  have nd := probe_nodup L hw hn
  have hfx := finite_ne_probe L hw hn
  have hft : L.point.finite ∉ (probeTail L) := by
    intro h; exact fin_not_x L hn (probeTail_mem L _ h)
  have hfp : L.point.finite ∉ L.dialogPool.take 247 := by
    intro h
    have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take h)
    simp only [dialogUsedWires, PointAddLayout.pointWires, List.count_append, List.count_cons,
      beq_self_eq_true, if_true] at hh
    omega
  let s1 : State := ⟨s.phase, writeBit s.basis L.point.finite (!s.basis L.point.finite)⟩
  have h1 : run [.X L.point.finite] [] s = s1 := rfl
  have hz1 : regValue (L.dialogPool.take 247) s1.basis = 0 := by
    rw [← hz]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfp (e ▸ hq)
    simp [s1, writeBit, this]
  have hh := equalPorts_correct (probeControl L) L.point.finite (probeTail L) (L.dialogPool.take 247) 226156424291633194186662080095093570025917938800079226639565593765455331327
    ((probeTail_length L hw).trans (work_length L hw).symm) nd
    (by rw [probeTail_length L hw]; norm_num) s1 m hz1
  have hm0 : measurementCount [Instr.X L.point.finite] = 0 := rfl
  rw [clrF, run_append, hm0, List.take_zero, List.drop_zero, h1, hh]
  have e1 : s1.basis L.point.finite = !s.basis L.point.finite := by simp [s1, writeBit]
  have e2 : s1.basis (probeControl L) = s.basis (probeControl L) := by simp [s1, writeBit, Ne.symm hfx]
  have e3 : regValue (probeTail L) s1.basis = regValue (probeTail L) s.basis := by
    apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hft (e ▸ hq)
    simp [s1, writeBit, this]
  rw [e1, e2, e3, probe_value_cons L hw]
  congr 1
  funext q
  by_cases hq : q = L.point.finite
  · subst hq
    simp only [s1, writeBit, Function.update_self]
    cases s.basis L.point.finite <;> cases s.basis (probeControl L) <;>
      by_cases ht : regValue (probeTail L) s.basis = 226156424291633194186662080095093570025917938800079226639565593765455331327 <;> simp [ht,sentinelHigh] <;> omega
  · simp [s1, writeBit, Function.update_of_ne hq]

include hw hn in
theorem zrep_run (s : State) (m : List Bool) :
    (run (zrep L) m s).phase = s.phase ∧
    (∀ q, q ∉ L.point.x → (run (zrep L) m s).basis q = s.basis q) ∧
    regValue L.point.x (run (zrep L) m s).basis =
      regValue L.point.x s.basis ^^^ (if s.basis L.point.finite then 0 else sentinel) := by
  have hfx := fin_not_x L hn
  have hnd := finX_nodup L hn
  let s1 : State := ⟨s.phase, writeBit s.basis L.point.finite (!s.basis L.point.finite)⟩
  have h1 : run [.X L.point.finite] [] s = s1 := rfl
  have hm0 : measurementCount [Instr.X L.point.finite] = 0 := rfl
  have hmc := (maskedConstant_counts L.point.finite L.point.x sentinel).2
  have hk : sentinel < 2 ^ L.point.x.length := by
    rw [show L.point.x.length = 256 from hw.inputX]; norm_num [sentinel]
  obtain ⟨tp, tout, tx⟩ := maskedConstant_correct L.point.finite L.point.x sentinel hnd hfx hk s1 []
  obtain ⟨t, ht⟩ : ∃ t : State, t = run (maskedConstant L.point.finite L.point.x sentinel) [] s1 := ⟨_, rfl⟩
  rw [← ht] at tp tout tx
  have hrun : run (zrep L) m s = ⟨t.phase, writeBit t.basis L.point.finite (!t.basis L.point.finite)⟩ := by
    rw [zrep, run_append, run_append, measurementCount_append, hm0, hmc, Nat.add_zero,
      List.take_zero, List.drop_zero, List.take_nil, List.drop_nil, h1, ← ht]
    rfl
  have tf : t.basis L.point.finite = !s.basis L.point.finite := by
    rw [tout _ hfx]; simp [s1, writeBit]
  rw [hrun]
  refine ⟨tp, ?_, ?_⟩
  · intro q hq
    by_cases hqf : q = L.point.finite
    · subst hqf; simp [writeBit, tf]
    · simp only [writeBit, Function.update_of_ne hqf]
      rw [tout q hq]; simp [s1, writeBit, Function.update_of_ne hqf]
  · have e1 : regValue L.point.x (writeBit t.basis L.point.finite (!t.basis L.point.finite)) =
        regValue L.point.x t.basis := by
      apply regValue_congr; intro q hq
      have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
      simp [writeBit, this]
    have e2 : regValue L.point.x s1.basis = regValue L.point.x s.basis := by
      apply regValue_congr; intro q hq
      have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
      simp [s1, writeBit, this]
    show regValue L.point.x (writeBit t.basis L.point.finite (!t.basis L.point.finite)) = _
    rw [e1, tx, e2]
    have : s1.basis L.point.finite = !s.basis L.point.finite := by simp [s1, writeBit]
    rw [this]
    cases s.basis L.point.finite <;> rfl

include hw hn in
theorem clrF_step (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (clrF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))) := by
  intro s m v
  have hz : regValue (L.dialogPool.take 247) s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  rw [clrF_run L hw hn s m hz,probe_value L hw]
  have hfxy := finite_not_x L hn
  have hfs : s.basis L.point.finite = base L.point.finite := v.rest _ hfxy
  have hfx := fin_not_x L hn
  have hfy : L.point.finite ∉ L.point.y := fun h => hfxy (List.mem_append_right _ h)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show regValue L.point.x (writeBit s.basis L.point.finite _) = _
    rw [← v.x]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
    simp [writeBit, this]
  · show regValue L.point.y (writeBit s.basis L.point.finite _) = _
    rw [← v.y]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfy (e ▸ hq)
    simp [writeBit, this]
  · show writeBit s.basis L.point.finite _ L.core.generic = _
    simp [writeBit, Ne.symm (fin_ne_generic L hn), v.generic]
  · show regValue L.dialogPool (writeBit s.basis L.point.finite _) = _
    rw [← v.clean]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => fin_not_pool L hn (e ▸ hq)
    simp [writeBit, this]
  · intro q hq
    show writeBit s.basis L.point.finite _ q = writeBit base L.point.finite _ q
    by_cases hqf : q = L.point.finite
    · subst hqf; simp [writeBit, hfs, v.x]
    · simp [writeBit, hqf, v.rest q hq]

include hw hn in
theorem zrep_step (X X' Y : Fp) (G : Bool) (base : BasisState)
    (hX : X'.val = X.val ^^^ (if base L.point.finite then 0 else sentinel)) :
    Triple (PointDialogValues L X Y G base) (zrep L) (PointDialogValues L X' Y G base) := by
  intro s m v
  obtain ⟨hp, hout, hx⟩ := zrep_run L hw hn s m
  have hf : s.basis L.point.finite = base L.point.finite := v.rest _ (finite_not_x L hn)
  refine ⟨hp, v.withX hn ?_ hout⟩
  rw [hx, v.x, hf, hX]

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalResources =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
theorem ports_length : (zeroPorts (probeTail L) (L.dialogPool.take 247)).length = 247 := by
  have h := (zeroPorts_maps (probeTail L) (L.dialogPool.take 247)
    ((probeTail_length L hw).trans (work_length L hw).symm)).1
  simpa only [List.length_map,probeTail_length L hw] using congrArg List.length h

theorem zrep_counts : toffoliCount (zrep L) = 0 ∧ measurementCount (zrep L) = 0 := by
  have h := maskedConstant_counts L.point.finite L.point.x sentinel
  simp only [zrep,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hw in
theorem clrF_counts : toffoliCount (clrF L) = 247 ∧ measurementCount (clrF L) = 247 := by
  have h := equalConstant_counts (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327
  rw [ports_length L hw] at h
  simp only [clrF,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hn in
theorem zrep_physical : GatePhysical (zrep L) := by
  simp only [zrep,gatePhysical_append]
  refine ⟨⟨?_,maskedConstant_physical _ _ _ (fin_not_x L hn)⟩,?_⟩
  all_goals intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial

include hw hn in
theorem clrF_physical : GatePhysical (clrF L) := by
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  simp only [clrF,gatePhysical_append]
  refine ⟨?_,equalConstant_physical _ _ _ _ ?_⟩
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial
  · exact (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)

include hw in
theorem old_clrF_support : wires (ECDSAAdd.Entrant.clrF L) =
    (L.point.finite :: (L.point.x ++ L.dialogPool.take 255)).toFinset := by
  have hl := (finTail_length L hw).trans (finWork255_length L hw).symm
  rw [ECDSAAdd.Entrant.clrF,wires_append,equalConstant_wires]
  ext q
  have hp : q ∈ (zeroPorts L.point.x.tail (L.dialogPool.take 255)).flatMap ZeroBit.wires ↔
      q ∈ L.point.x.tail ++ L.dialogPool.take 255 :=
    (zeroPorts_perm L.point.x.tail (L.dialogPool.take 255) hl).mem_iff
  have hx : q ∈ L.point.x ↔ q = x0 L ∨ q ∈ L.point.x.tail := by
    conv_lhs => rw [x_cons L hw]
    simp
  simp only [Finset.mem_union,wires,Instr.wires,Finset.union_empty,Finset.mem_singleton,
    List.mem_toFinset,List.mem_cons] at *
  rw [hp]
  simp only [List.mem_append] at *
  tauto

include hw in
theorem zrep_support_old : wires (zrep L) ⊆ wires (ECDSAAdd.Entrant.clrF L) := by
  rw [old_clrF_support L hw]
  intro q used
  simp only [zrep,wires_append,Finset.mem_union] at used
  rcases used with (h | h) | h
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]
  · have h' := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h' ⊢
    tauto
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]

include hw in
theorem clrF_support_old : wires (clrF L) ⊆ wires (ECDSAAdd.Entrant.clrF L) := by
  rw [old_clrF_support L hw]
  intro q used
  simp only [clrF,wires_append,Finset.mem_union] at used
  rcases used with h | h
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]
  · rw [equalConstant_wires] at h
    have h' := List.mem_toFinset.mp h
    rcases List.mem_cons.mp h' with e | h'
    · subst q
      simp [probeControl_mem L hw]
    rcases List.mem_cons.mp h' with e | h'
    · subst q; simp
    have hl := (probeTail_length L hw).trans (work_length L hw).symm
    rcases List.mem_append.mp ((zeroPorts_perm _ _ hl).subset h') with inp | work
    · simp [probeTail_mem L q inp]
    · have included : L.dialogPool.take 247 ⊆ L.dialogPool.take 255 := by
        have h : L.dialogPool.take 247 = (L.dialogPool.take 255).take 247 := by
          rw [List.take_take]; rfl
        rw [h]
        exact List.take_subset _ _
      simp [included work]

include hw in
theorem zrep_slots : gateSlots (zrep L) ≤ 258 := by
  have h := maskedConstant_gateSlots_le L.point.finite L.point.x sentinel
  rw [show L.point.x.length = 256 from hw.inputX] at h
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [zrep,gateSlots_append,one]
  omega

include hw in
theorem clrF_slots : gateSlots (clrF L) ≤ 2261 := by
  have h := equalConstant_gateSlots_le (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327
  rw [ports_length L hw] at h
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [clrF,gateSlots_append,one]
  omega

def constantSlots : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, k => (if k % 2 = 1 then 1 else 0) + constantSlots n (k/2)

theorem xor_slots_exact (r : List Wire) (k : Nat) :
    gateSlots (xorConstant r k) = constantSlots r.length k := by
  induction r generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [xorConstant,constantSlots,List.length_cons,gateSlots_append]
    split <;> simp [gateSlots_cons,instructionSlots,ih]

theorem masked_slots_exact (c : Wire) (r : List Wire) (k : Nat) :
    gateSlots (maskedConstant c r k) = constantSlots r.length k := by
  induction r generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [maskedConstant,constantSlots,List.length_cons,gateSlots_append]
    split <;> simp [gateSlots_cons,instructionSlots,ih]

theorem equal_slots_exact (c t : Wire) (bs : List ZeroBit) (k : Nat) :
    gateSlots (equalConstant c t bs k) = 7*bs.length+1+2*constantSlots bs.length k := by
  simp only [equalConstant,gateSlots_append,zeroControlled_gateSlots,xor_slots_exact,List.length_map]
  omega

include hw in
theorem zrep_slots_exact : gateSlots (zrep L) = 251 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [zrep,gateSlots_append,one,masked_slots_exact,
    show L.point.x.length = 256 from hw.inputX]
  decide +kernel

include hw in
theorem old_zrep_slots_exact : gateSlots (ECDSAAdd.Entrant.zrep L) = 4 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [ECDSAAdd.Entrant.zrep,gateSlots_append,one,masked_slots_exact,
    show L.point.x.length = 256 from hw.inputX]
  decide +kernel

include hw in
theorem clrF_slots_exact : gateSlots (clrF L) = 2225 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [clrF,gateSlots_append,one,equal_slots_exact,ports_length L hw]
  decide +kernel

include hw in
theorem old_clrF_slots_exact : gateSlots (ECDSAAdd.Entrant.clrF L) = 1789 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [ECDSAAdd.Entrant.clrF,gateSlots_append,one,equal_slots_exact,finClr_ports_length L hw]
  decide +kernel

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalPoint =====
section
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

def clearF : Program := [.X L.point.finite] ++ MeasuredZeroClear.equalClear
  (probeControl L) L.point.finite (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327

include hw hn in
theorem clearF_eq (s : State) (m : List Bool) (hz : regValue (L.dialogPool.take 247) s.basis=0)
    (hzero : (run (clrF L) m s).basis L.point.finite=false) :
    run (clearF L) m s=run (clrF L) m s := by
  let bs := zeroPorts (probeTail L) (L.dialogPool.take 247)
  let s1 := run [Instr.X L.point.finite] [] s
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  have nd : (probeControl L::L.point.finite::bs.flatMap ZeroBit.wires).Nodup :=
    (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)
  have hz1 : ∀b∈bs,s1.basis b.work=false := by
    intro b hb
    have mem : b.work∈L.dialogPool.take 247 := by
      rw [←(zeroPorts_maps _ _ hl).2]
      exact List.mem_map.mpr ⟨b,hb,rfl⟩
    have ne : b.work≠L.point.finite := fun eq =>
      fin_not_pool L hn (eq ▸ List.mem_of_mem_take mem)
    simpa [s1,run,writeBit,ne] using (regValue_zero _ _).mp hz b.work mem
  have zero : (run (equalConstant (probeControl L) L.point.finite bs 226156424291633194186662080095093570025917938800079226639565593765455331327) m s1).basis
      L.point.finite=false := by
    simpa only [clrF,run_append,show measurementCount [Instr.X L.point.finite]=0 from rfl,
      List.take_zero,List.drop_zero] using hzero
  have eq := MeasuredZeroClear.equal_run_eq _ _ bs 226156424291633194186662080095093570025917938800079226639565593765455331327 nd s1 m hz1 zero
  simpa only [clearF,clrF,run_append,show measurementCount [Instr.X L.point.finite]=0 from rfl,
    List.take_zero,List.drop_zero] using eq

include hw hn in
theorem clearF_step (X Y : Fp) (G : Bool) (base : BasisState)
    (hf : base L.point.finite=decide (probeVal X.val ≠ sentinelHigh)) :
    Triple (PointDialogValues L X Y G base) (clearF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))) := by
  intro s m v
  have hz : regValue (L.dialogPool.take 247) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  have zero : (run (clrF L) m s).basis L.point.finite=false := by
    rw [clrF_run L hw hn s m hz,probe_value L hw,v.x]
    simp [writeBit,v.rest _ (finite_not_x L hn),hf]
  rw [clearF_eq L hw hn s m hz zero]
  exact clrF_step L hw hn X Y G base s m v

theorem clearF_support : wires (clearF L) ⊆ wires (clrF L) := by
  simp only [clearF,clrF,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (MeasuredZeroClear.equal_support _ _ _ _)

include hw in
theorem clearF_counts : toffoliCount (clearF L)=246 ∧ measurementCount (clearF L)=247 := by
  have h := MeasuredZeroClear.equal_counts (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327
  rw [ports_length L hw] at h
  simp only [clearF,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hw in
theorem clearF_slots : gateSlots (clearF L)=2221 := by
  have ne : zeroPorts (probeTail L) (L.dialogPool.take 247)≠[] := by
    intro h
    have len := ports_length L hw
    rw [h] at len
    contradiction
  have h := MeasuredZeroClear.equal_slots (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327 ne
  have old := clrF_slots_exact L hw
  simp only [clearF,clrF,gateSlots_append] at old ⊢
  omega

include hw hn in
theorem clearF_physical : GatePhysical (clearF L) := by
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  simp only [clearF,gatePhysical_append]
  refine ⟨?_,MeasuredZeroClear.equal_physical _ _ _ _ ?_⟩
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial
  · exact (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)

end ECDSAAdd.Entrant.FiniteFlagInterval
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires
abbrev generic := ReflectionE1TickGapLow48.generic
def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clearF L ++ renameProgram (swapF L) (generic L cx cy) ++ clrF L
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program := zrep L ++ mid L cx cy ++ zrep L
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (probeVal X.val ≠ sentinelHigh) = fin) (h2 : decide (probeVal X'.val ≠ sentinelHigh) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clearF_step L hw hn X Y G base (hf.trans h1.symm)
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
        L.point.finite ^^ decide (probeVal X'.val ≠ sentinelHigh)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 (sentinel : Fp) 0 false s.basis (by rw [hfin, sentinel_val]; rfl)
    have mid := midFFused_values L hw hn cx cy (sentinel : Fp) 0 (sentinel : Fp) 0 false s.basis false
      (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn (sentinel : Fp) 0 cx cy base' sentinel_ne_zero) hfin
      (by rw [sentinel_val, sentinel_high]; decide) (by rw [sentinel_val, sentinel_high]; decide)
    have z2 := zrep_step L hw hn (sentinel : Fp) 0 0 false s.basis (by rw [hfin, sentinel_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (probeVal x.val ≠ sentinelHigh) = true := decide_eq_true (curve_x_high_ne hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide (probeVal (genericX x y cx cy).val ≠ sentinelHigh) = true :=
        decide_eq_true (curve_x_high_ne (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalFinal =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  ReflectionE1TickGapLow48.generic

theorem gen_support_subset (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (gen L cx cy) ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) := by
  intro q used
  have hz : q ∈ wires (zrep L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => zrep_support_old L hw h
  have hc : q ∈ wires (clrF L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => clrF_support_old L hw h
  have he : q ∈ wires (clearF L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => hc (clearF_support L h)
  simp only [gen,mid,ReflectionE1TickGapLow48.gen,ReflectionE1TickGapLow48.mid,
    generic,wires_append,Finset.mem_union] at used ⊢
  tauto

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy) ⊆ (OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (ReflectionE1TickGapLow48.gen_sites L hw hn cx cy)

theorem gen_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+17 = toffoliCount (ReflectionE1TickGapLow48.gen L cx cy) ∧
    measurementCount (gen L cx cy)+16 = measurementCount (ReflectionE1TickGapLow48.gen L cx cy) ∧
    gateSlots (gen L cx cy) = gateSlots (ReflectionE1TickGapLow48.gen L cx cy)+1362 := by
  have z := zrep_counts L
  have c := clrF_counts L hw
  have e := clearF_counts L hw
  have oz := ECDSAAdd.Entrant.zrep_counts L
  have oc := ECDSAAdd.Entrant.clrF_counts L hw
  simp only [gen,mid,ReflectionE1TickGapLow48.gen,ReflectionE1TickGapLow48.mid,generic,
    toffoliCount_append,measurementCount_append,gateSlots_append,z.1,z.2,c.1,c.2,
    oz.1,oz.2,oc.1,oc.2,e.1,e.2,zrep_slots_exact L hw,clrF_slots_exact L hw,clearF_slots L hw,
    old_zrep_slots_exact L hw,old_clrF_slots_exact L hw]
  omega

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z := zrep_physical L hn
  have c := clrF_physical L hw hn
  have e := clearF_physical L hw hn
  have g := gatePhysical_rename (swapF L) (swapF_injective L hw hn) _
    (ReflectionE1TickGapLow48.generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append,generic] using And.intro (And.intro z (And.intro (And.intro e g) c)) z

theorem wrapper_support_mono (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : wires P ⊆ wires Q) :
    wires (Edges.wrapper L C cy P) ⊆ wires (Edges.wrapper L C cy Q) := by
  simp only [Edges.wrapper,Edges.finiteProgram,wires_append,renameProgram_support]
  repeat' first
    | exact h
    | exact Finset.Subset.refl _
    | apply Finset.union_subset_union
    | apply Finset.image_subset_image

theorem wrapper_counts (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cx cy : Fp) :
    toffoliCount (Edges.wrapper L C cy (gen L cx cy))+17 =
      toffoliCount (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy)) ∧
    measurementCount (Edges.wrapper L C cy (gen L cx cy))+16 =
      measurementCount (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy)) ∧
    gateSlots (Edges.wrapper L C cy (gen L cx cy)) =
      gateSlots (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy))+1362 := by
  have h := gen_counts L hw cx cy
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,renameProgram_counts,rename_gateSlots]
  omega

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 1588 := by
  have h := wrapper_support_mono layout C cy _ _ (gen_support_subset layout layout_widths cx cy)
  have card := Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)
  exact card.trans (ReflectionE1TickGapLow48.wrapper_qubits C cx cy)

theorem wrapper_qubits760 (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 1587 := by
  have h := wrapper_support_mono layout C cy _ _ (gen_support_subset layout layout_widths cx cy)
  have card := Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)
  exact card.trans (ReflectionE1TickGapLow48.wrapper_qubits760 C cx cy)

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 2147987 := by
  have h := (wrapper_counts layout layout_widths (.some hc) cx cy).1
  have old := ReflectionE1TickGapLow48.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 1498877 := by
  have h := (wrapper_counts layout layout_widths (.some hc) cx cy).2.1
  have old := ReflectionE1TickGapLow48.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 50215655+Rolling1588.slotGrowth := by
  have h := (wrapper_counts layout layout_widths C cx cy).2.2
  have old := ReflectionE1TickGapLow48.wrapper_slots C cx cy
  omega

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2147987,1498877,1588,50215655+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2147987 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1498877 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50215655+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1498877
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50215655+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.Main =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.MeasuredDHFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      MeasuredDH.wrapper layout C cy (FiniteFlagInterval.gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2148024,1498904,1588,50215644+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := FiniteFlagInterval.gen_sites layout layout_widths layout_nodup cx cy
    have support := (MeasuredDH.wrapper_support layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ b R _
      (MeasuredDH.full_spec layout layout_widths layout_nodup R hc b _
        (FiniteFlagInterval.genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2148024 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤2148024
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498904 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤1498904
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1588 := by
  cases C with
  | zero => change qubits []≤1588; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := MeasuredDH.wrapper_support layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (FiniteFlagInterval.wrapper_qubits (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact MeasuredDH.wrapper_physical layout layout_widths layout_nodup _ cy _
      (FiniteFlagInterval.gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50215644+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    change gateSlots (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤50215644+Rolling1588.slotGrowth
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498904
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50215644+Rolling1588.slotGrowth
    rw [normalize_slots]; exact program_gateSlots C
end ECDSAAdd.Entrant.MeasuredDHFinal
end
end

-- ===== merged module ECDSAAdd.Submission.Entrant.FusedBoundaryFinal =====
section
namespace ECDSAAdd.Entrant.FusedBoundaryFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      FusedFlags.wrapper layout C cy (FiniteFlagInterval.gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2147984,1498875,1587,50240570⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := FiniteFlagInterval.gen_sites layout layout_widths layout_nodup cx cy
    have support := (FusedFlags.wrapper_support layout hc (FiniteFlagInterval.gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ b R _
      (FusedFlags.full_spec layout layout_widths layout_nodup R hc b _
        (FiniteFlagInterval.genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2147984 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤2147984
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498875 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤1498875
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1587 := by
  cases C with
  | zero => change qubits []≤1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := FusedFlags.wrapper_support layout hc (FiniteFlagInterval.gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (FiniteFlagInterval.wrapper_qubits760 (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact FusedFlags.wrapper_physical layout layout_widths layout_nodup _ cy _
      (FiniteFlagInterval.gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50240570 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    have growth : Rolling1588.slotGrowth=24925 := rfl
    rw [growth] at old
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤50240570
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498875
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50240570
    rw [normalize_slots]; exact program_gateSlots C

end ECDSAAdd.Entrant.FusedBoundaryFinal
end

-- ===== combined module ECDSAAdd.Submission.Entrant.CodexAffineMath =====
section
/-!
A 247-bit affine finite-point probe. The design follows the unintegrated
research direction in Yukon submission a67cb86c-fb4d-4634-98e9-dcb7b60d563a:
bits 1 and 2 agree; bit 5 and the selected high bits are set.
The case split and field proofs below are independently reconstructed.
-/
namespace ECDSAAdd.Entrant.CodexAffineMath
open Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

def matchesX (v : Nat) : Prop :=
  v / 2 % 2 = v / 4 % 2 ∧
  v / 32 % 2 = 1 ∧
  v / 1024 % 4194304 = 4194303 ∧
  v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607

instance : DecidablePred matchesX := fun v =>
  inferInstanceAs (Decidable (v / 2 % 2 = v / 4 % 2 ∧ v / 32 % 2 = 1 ∧
    v / 1024 % 4194304 = 4194303 ∧
    v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607))

def excluded (v : Nat) : Prop :=
  v = 115792089237316195423570985008687907853269984665640564039457584007908834671648 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671649 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671656 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671657 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671662

theorem matches_cases (v : Nat) (hv : v < p) (h : matchesX v) : excluded v := by
  unfold matchesX at h
  unfold excluded
  norm_num [p] at hv
  omega

theorem sentinel_matches : matchesX (p-1) := by
  norm_num [matchesX,p]

private theorem nonresidue_0 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671648 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_1 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671649 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_2 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671654 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_3 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671655 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_4 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_5 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671657 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_6 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671662 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem excluded_nonresidue (v : Nat) (hv : excluded v) :
    ((v : Fp)^3+7)^((p-1)/2) = -1 := by
  have hp : 115792089237316195423570985008687907853269984665640564039457584007908834671663 = p := by norm_num [p]
  have he : (p-1)/2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by norm_num [p]
  rw [he]
  have transport (q a : Nat) (hq : q=p)
      (h : ((a : ZMod q)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1) :
      ((a : Fp)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    subst q
    exact h
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transport _ _ hp nonresidue_0
  · exact transport _ _ hp nonresidue_1
  · exact transport _ _ hp nonresidue_2
  · exact transport _ _ hp nonresidue_3
  · exact transport _ _ hp nonresidue_4
  · exact transport _ _ hp nonresidue_5
  · exact transport _ _ hp nonresidue_6

theorem curve_x_not_matches {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    ¬ matchesX x.val := by
  intro h
  haveI : NeZero p := ⟨by norm_num [p]⟩
  have power := excluded_nonresidue x.val (matches_cases x.val (ZMod.val_lt x) h)
  rw [ZMod.natCast_zmod_val] at power
  have equation := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at equation
  have square : y^2 = x^3+7 := by simpa [curve,curveA,curveB] using equation
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y≠0 := by
    intro hz
    rw [←square,hz,zero_pow (by decide),zero_pow (by norm_num [p])] at power
    simp at power
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have even : p-1=2*((p-1)/2) := by norm_num [p]
  rw [even,pow_mul,square,power] at fermat
  have ne : (-1 : Fp)≠1 := by decide
  exact ne fermat

theorem probe_bridge (a b : Bool) (rest v : Nat)
    (h : (if a then 1 else 0)+2*((if b then 1 else 0)+2*rest) =
      v / 2 % 4 + 4*(v / 32 % 2) + 8*(v / 1024 % 4194304) +
      33554432*(v / 8589934592)) :
    (!(b ^^ a) && decide (rest=2^246-1)) = decide (matchesX v) := by
  change (!(b ^^ a) && decide (rest=113078212145816597093331040047546785012958969400039613319782796882727665663)) = decide (matchesX v)
  have low : v / 2 % 4 = v / 2 % 2 + 2*(v / 4 % 2) := by
    have h4 : v / 2 / 2 = v / 4 := by simp [Nat.div_div_eq_div_mul]
    have h8 : v / 2 / 4 = v / 4 / 2 := by simp [Nat.div_div_eq_div_mul]
    omega
  have tail : rest = v / 32 % 2 + 2*(v / 1024 % 4194304) + 8388608*(v / 8589934592) := by
    have hlt := Nat.mod_lt (v / 2) (by decide : 0 < 4)
    cases a <;> cases b <;> simp_all only [Bool.false_eq_true, if_false, if_true] <;> omega
  have bits : (if a then 1 else 0) = v / 2 % 2 ∧ (if b then 1 else 0) = v / 4 % 2 := by
    cases a <;> cases b <;> simp_all only [Bool.false_eq_true, if_false, if_true] <;> omega
  have tail_iff : rest=113078212145816597093331040047546785012958969400039613319782796882727665663 ↔ v / 32 % 2 = 1 ∧ v / 1024 % 4194304 = 4194303 ∧ v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607 := by
    omega
  cases a <;> cases b <;> simp_all [matchesX] <;> omega

end ECDSAAdd.Entrant.CodexAffineMath
end

-- ===== combined module ECDSAAdd.Submission.Entrant.CodexAffineGadget =====
section
namespace ECDSAAdd.Entrant.CodexAffineGadget
open Arithmetic RecordedQuantum Challenge Baselines

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def view (a b : Wire) : Program := [.CX a b, .X b]
def restore (a b : Wire) : Program := [.X b, .CX a b]
def core (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ equalConstant b f (zeroPorts r work) k
def program (a b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view a b ++ core b f r work k ++ restore a b
def clearCore (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ MeasuredZeroClear.equalClear b f (zeroPorts r work) k
def clearProgram (a b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view a b ++ clearCore b f r work k ++ restore a b

theorem run_concat (P Q : Program) (m : List Bool) (s : State) :
    run (P ++ Q) m s = run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append, run_take]

theorem ports_length (r work : List Wire) (hl : r.length = work.length) :
    (zeroPorts r work).length = r.length := by
  have h := congrArg List.length (zeroPorts_maps r work hl).1
  simpa using h

theorem ports_nodup (a b f : Wire) (r work : List Wire)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    (b :: f :: (zeroPorts r work).flatMap ZeroBit.wires).Nodup := by
  exact (((zeroPorts_perm r work hl).cons f).cons b).nodup_iff.mpr
    (List.nodup_cons.mp hn).2

theorem view_run (a b : Wire) (_hab : a ≠ b) (s : State) (m : List Bool) :
    run (view a b) m s =
      ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ s.basis a))⟩ := by
  simp [view, run, writeBit]

theorem restore_update (a b f : Wire) (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f)
    (s : State) (m : List Bool) (z : Bool) :
    run (restore a b) m
      ⟨s.phase, writeBit (writeBit s.basis b (!(s.basis b ^^ s.basis a))) f z⟩ =
      ⟨s.phase, writeBit s.basis f z⟩ := by
  simp only [restore, run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = b
  · subst q
    cases ha : s.basis a <;> cases hb : s.basis b <;>
      simp [writeBit, hab, haf, hbf, ha, hb]
  · by_cases hqf : q = f
    · subst q
      simp [writeBit, hab, haf, hbf, hbf.symm]
    · simp [writeBit, hq, hqf, hab, haf, hbf]

theorem program_run (a b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (a :: b :: f :: (r ++ work)).Nodup) (hl : r.length = work.length)
    (hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0) :
    run (program a b f r work k) m s =
      ⟨s.phase, writeBit s.basis f
        (s.basis f ^^ !((!(s.basis b ^^ s.basis a)) && decide (regValue r s.basis = k)))⟩ := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have hab : a ≠ b := sep.1.1
  have haf : a ≠ f := sep.1.2.1
  have hbf : b ≠ f := sep.2.1.1
  have hbr : b ∉ r := sep.2.1.2.1
  have hbw : b ∉ work := sep.2.1.2.2
  have hfr : f ∉ r := sep.2.2.1.1
  have hfw : f ∉ work := sep.2.2.1.2
  let u : State := ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ s.basis a))⟩
  let v : State := ⟨s.phase, writeBit u.basis f (!s.basis f)⟩
  have hu : run (view a b) m s = u := view_run a b hab s m
  have uv : run [.X f] m u = v := by simp [run, u, v, writeBit, hbf.symm]
  have hports := zeroPorts_maps r work hl
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← hports.2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    simpa [v, u, writeBit, neb, nef] using (regValue_zero work s.basis).mp hz p.work mem
  have hr : regValue r v.basis = regValue r s.basis := by
    apply regValue_congr
    intro q hq
    simp [v, u, writeBit, show q ≠ b from fun e => hbr (e ▸ hq),
      show q ≠ f from fun e => hfr (e ▸ hq)]
  have eq := equalConstant_correct b f (zeroPorts r work) k (ports_nodup a b f r work hl hn)
    (by simpa only [ports_length r work hl] using hk) v m clean
  rw [hports.1, hr] at eq
  have vb : v.basis b = !(s.basis b ^^ s.basis a) := by simp [v, u, writeBit, hbf]
  have vf : v.basis f = !s.basis f := by simp [v, writeBit]
  rw [vb, vf] at eq
  have folded : ((!s.basis f) ^^
      (!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k))) =
      (s.basis f ^^ !(!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k))) := by
    cases s.basis f <;> cases (!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k)) <;> rfl
  rw [folded] at eq
  have shape : run (program a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, hu, uv]
  rw [shape, eq]
  simpa only [v, u, writeBit, Function.update_idem] using
    restore_update a b f hab haf hbf s (m.drop (zeroPorts r work).length)
      (s.basis f ^^ !(!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k)))

theorem program_counts (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (program a b f r work k) = r.length ∧
    measurementCount (program a b f r work k) = r.length := by
  simp [program, core, view, restore, toffoliCount_append, measurementCount_append,
    equalConstant_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem clearProgram_counts (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (clearProgram a b f r work k) = r.length - 1 ∧
    measurementCount (clearProgram a b f r work k) = r.length := by
  simp [clearProgram, clearCore, view, restore, toffoliCount_append, measurementCount_append,
    MeasuredZeroClear.equal_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem program_support (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    wires (program a b f r work k) ⊆ (a :: b :: f :: (r ++ work)).toFinset := by
  intro q hq
  have hp : q ∈ (zeroPorts r work).flatMap ZeroBit.wires ↔ q ∈ r ++ work :=
    (zeroPorts_perm r work hl).mem_iff
  simp only [program, core, view, restore, wires_append, equalConstant_wires, wires,
    Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty, or_false, List.mem_toFinset, List.mem_cons, hp] at hq ⊢
  tauto

theorem clearProgram_support (a b f : Wire) (r work : List Wire) (k : Nat) :
    wires (clearProgram a b f r work k) ⊆ wires (program a b f r work k) := by
  simp only [clearProgram, clearCore, program, core, wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _)
        (MeasuredZeroClear.equal_support b f (zeroPorts r work) k)))
    (Finset.Subset.refl _)

theorem clearProgram_run_eq (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup)
    (s : State) (m : List Bool) (hz : regValue work s.basis = 0)
    (hzero : (run (program a b f r work k) m s).basis f = false) :
    run (clearProgram a b f r work k) m s = run (program a b f r work k) m s := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have haf : a ≠ f := sep.1.2.1
  have hbf : b ≠ f := sep.2.1.1
  have haw : a ∉ work := sep.1.2.2.2
  have hbw : b ∉ work := sep.2.1.2.2
  have hfw : f ∉ work := sep.2.2.1.2
  let v := run [Instr.X f] m (run (view a b) m s)
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← (zeroPorts_maps r work hl).2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have nea : p.work ≠ a := fun e => haw (e ▸ mem)
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    have away : p.work ∉ wires (view a b) := by simp [view, wires, Instr.wires, nea, neb]
    change (run [Instr.X f] m (run (view a b) m s)).basis p.work = false
    rw [run_preserves_outside _ _ _ _ (by simp [wires, Instr.wires, nef]),
      run_preserves_outside _ _ _ _ away]
    exact (regValue_zero work s.basis).mp hz p.work mem
  have oldShape : run (program a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have newShape : run (clearProgram a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) m v) := by
    simp only [clearProgram, clearCore, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (MeasuredZeroClear.equal_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have away : f ∉ wires (restore a b) := by
    simp [restore, wires, Instr.wires, haf.symm, hbf.symm]
  have keep := run_preserves_outside (restore a b) (m.drop (zeroPorts r work).length)
    (run (equalConstant b f (zeroPorts r work) k) m v) f away
  have zero : (run (equalConstant b f (zeroPorts r work) k) m v).basis f = false := by
    rw [oldShape] at hzero
    exact keep.symm.trans hzero
  have eq := MeasuredZeroClear.equal_run_eq b f (zeroPorts r work) k
    (ports_nodup a b f r work hl hn) v m clean zero
  rw [oldShape, newShape, eq]

theorem clearProgram_eq (a b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (a :: b :: f :: (r ++ work)).Nodup) (hl : r.length = work.length)
    (_hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0)
    (hzero : (run (program a b f r work k) m s).basis f = false) :
    run (clearProgram a b f r work k) m s = run (program a b f r work k) m s :=
  clearProgram_run_eq a b f r work k hl hn s m hz hzero

theorem program_physical (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    GatePhysical (program a b f r work k) := by
  have hab : a ≠ b := by
    intro e
    exact (List.nodup_cons.mp hn).1 (by simp [e])
  have hv : GatePhysical (view a b) := by simp [view, GatePhysical, PhysicalInstr, ProperGate, hab]
  have hr : GatePhysical (restore a b) := by simp [restore, GatePhysical, PhysicalInstr, ProperGate, hab]
  simp only [program, core, gatePhysical_append]
  exact ⟨⟨hv, ⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
    equalConstant_physical b f (zeroPorts r work) k (ports_nodup a b f r work hl hn)⟩⟩, hr⟩

theorem clearProgram_physical (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    GatePhysical (clearProgram a b f r work k) := by
  have old := program_physical a b f r work k hl hn
  simp only [program, core, gatePhysical_append] at old
  simp only [clearProgram, clearCore, gatePhysical_append]
  exact ⟨⟨old.1.1, ⟨old.1.2.1,
    MeasuredZeroClear.equal_physical b f (zeroPorts r work) k
      (ports_nodup a b f r work hl hn)⟩⟩, old.2⟩

theorem program_slots (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (program a b f r work k) ≤ 9 * r.length + 6 := by
  have h := equalConstant_gateSlots_le b f (zeroPorts r work) k
  rw [ports_length r work hl] at h
  simp only [program, core, view, restore, gateSlots_append] at *
  change 2 + (1 + gateSlots (equalConstant b f (zeroPorts r work) k)) + 2 ≤ _
  omega

theorem clearProgram_slots_le (a b f : Wire) (r work : List Wire) (k : Nat) :
    gateSlots (clearProgram a b f r work k) ≤ gateSlots (program a b f r work k) := by
  have h : gateSlots (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) ≤
      gateSlots (equalConstant b f (zeroPorts r work) k) := by
    by_cases he : zeroPorts r work = []
    · rw [he]
      exact Nat.le_refl _
    · have h := MeasuredZeroClear.equal_slots b f (zeroPorts r work) k he
      omega
  simp only [clearProgram, clearCore, program, core, gateSlots_append]
  omega

theorem clearProgram_slots (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (clearProgram a b f r work k) ≤ 9 * r.length + 6 :=
  (clearProgram_slots_le a b f r work k).trans (program_slots a b f r work k hl)

end ECDSAAdd.Entrant.CodexAffineGadget
end

-- ===== combined module ECDSAAdd.Submission.Entrant.CodexAffineProbe =====
section
/-! A reversible affine view combines the two low probe bits into their equality.
The arithmetic backend and public encoding are inherited unchanged. -/
namespace ECDSAAdd.Entrant.CodexAffineProbe
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires

def a (L : ControlledPointLayout) : Wire := FiniteFlagInterval.probeControl L
def b (L : ControlledPointLayout) : Wire := (FiniteFlagInterval.probeTail L).headD 0
def rest (L : ControlledPointLayout) : List Wire := (FiniteFlagInterval.probeTail L).tail
def work (L : ControlledPointLayout) : List Wire := L.dialogPool.take 246
def literal : Nat := 2^246-1
def finiteBit (v : Nat) : Bool := decide (¬ CodexAffineMath.matchesX v)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
theorem tail_cons : FiniteFlagInterval.probeTail L = b L :: rest L := by
  have h := FiniteFlagInterval.probeTail_length L hw
  unfold b rest
  cases e : FiniteFlagInterval.probeTail L with
  | nil => simp [e] at h
  | cons q qs => rfl

include hw in
theorem lengths : (rest L).length=246 ∧ (work L).length=246 := by
  simp [rest,work,FiniteFlagInterval.probeTail_length L hw,L.dialogPool_length hw]

theorem work_subset : work L ⊆ L.dialogPool.take 247 := by
  have h : work L=(L.dialogPool.take 247).take 246 := by
    simp only [work,List.take_take]; rfl
  rw [h]
  exact List.take_subset _ _

include hw hn in
theorem ports_nodup : (a L :: b L :: L.point.finite :: (rest L ++ work L)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (FiniteFlagInterval.probe_nodup L hw hn) q
  have hp : (work L).count q ≤ (L.dialogPool.take 247).count q := by
    have sub : (work L).Sublist (L.dialogPool.take 247) := by
      have e : work L=(L.dialogPool.take 247).take 246 := by
        simp only [work,List.take_take]; rfl
      rw [e]; exact List.take_sublist _ _
    exact sub.count_le q
  rw [tail_cons L hw] at h
  simp only [a,List.count_cons,List.count_append] at h ⊢
  omega

include hw in
theorem inputs_mem : a L∈L.point.x ∧ b L∈L.point.x ∧ ∀q∈rest L,q∈L.point.x := by
  refine ⟨FiniteFlagInterval.probeControl_mem L hw,?_,?_⟩
  · apply FiniteFlagInterval.probeTail_mem L
    rw [tail_cons L hw]; simp
  · intro q hq
    exact FiniteFlagInterval.probeTail_mem L q (List.mem_of_mem_tail hq)

include hw in
theorem hit (s : BasisState) :
    (!(s (b L) ^^ s (a L)) && decide (regValue (rest L) s=literal)) =
      decide (CodexAffineMath.matchesX (regValue L.point.x s)) := by
  have h := FiniteFlagInterval.probe_value L hw s
  rw [FiniteFlagInterval.probe_cons L hw,tail_cons L hw] at h
  exact CodexAffineMath.probe_bridge (s (a L)) (s (b L))
    (regValue (rest L) s) (regValue L.point.x s) h

def clrF : Program := CodexAffineGadget.program (a L) (b L) L.point.finite (rest L) (work L) literal
def clearF : Program := CodexAffineGadget.clearProgram (a L) (b L) L.point.finite (rest L) (work L) literal

include hw hn in
theorem clrF_run (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0) :
    run (clrF L) m s = ⟨s.phase,writeBit s.basis L.point.finite
      (s.basis L.point.finite ^^ finiteBit (regValue L.point.x s.basis))⟩ := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have hk : literal < 2^(rest L).length := by rw [(lengths L hw).1]; decide
  rw [clrF,CodexAffineGadget.program_run _ _ _ _ _ _ (ports_nodup L hw hn) hl hk s m hz,
    hit L hw s.basis]
  simp only [finiteBit,decide_not]

include hw hn in
theorem clearF_eq (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0)
    (hzero : (run (clrF L) m s).basis L.point.finite=false) :
    run (clearF L) m s=run (clrF L) m s := by
  exact CodexAffineGadget.clearProgram_eq _ _ _ _ _ _ (ports_nodup L hw hn)
    ((lengths L hw).1.trans (lengths L hw).2.symm)
    (by rw [(lengths L hw).1]; decide) s m hz hzero

include hw hn in
theorem clrF_step (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (clrF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))) := by
  intro s m v
  have hz : regValue (work L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  rw [clrF_run L hw hn s m hz]
  have hfxy := finite_not_x L hn
  have hfs : s.basis L.point.finite=base L.point.finite := v.rest _ hfxy
  have hfx := fin_not_x L hn
  have hfy : L.point.finite∉L.point.y := fun h => hfxy (List.mem_append_right _ h)
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · show regValue L.point.x (writeBit s.basis L.point.finite _) = _
    rw [←v.x]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => hfx (e ▸ hq)
    simp [writeBit,this]
  · show regValue L.point.y (writeBit s.basis L.point.finite _) = _
    rw [←v.y]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => hfy (e ▸ hq)
    simp [writeBit,this]
  · show writeBit s.basis L.point.finite _ L.core.generic = _
    simp [writeBit,Ne.symm (fin_ne_generic L hn),v.generic]
  · show regValue L.dialogPool (writeBit s.basis L.point.finite _) = _
    rw [←v.clean]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => fin_not_pool L hn (e ▸ hq)
    simp [writeBit,this]
  · intro q hq
    show writeBit s.basis L.point.finite _ q=writeBit base L.point.finite _ q
    by_cases hqf : q=L.point.finite
    · subst hqf; simp [writeBit,hfs,v.x]
    · simp [writeBit,hqf,v.rest q hq]

include hw hn in
theorem clearF_step (X Y : Fp) (G : Bool) (base : BasisState)
    (hf : base L.point.finite=finiteBit X.val) :
    Triple (PointDialogValues L X Y G base) (clearF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))) := by
  intro s m v
  have hz : regValue (work L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  have zero : (run (clrF L) m s).basis L.point.finite=false := by
    rw [clrF_run L hw hn s m hz]
    simp [writeBit,v.x,v.rest _ (finite_not_x L hn),hf]
  rw [clearF_eq L hw hn s m hz zero]
  exact clrF_step L hw hn X Y G base s m v

include hw in
theorem clrF_support_old : wires (clrF L) ⊆ wires (ECDSAAdd.Entrant.clrF L) := by
  rw [FiniteFlagInterval.old_clrF_support L hw]
  intro q hq
  have h := CodexAffineGadget.program_support (a L) (b L) L.point.finite (rest L) (work L) literal
    ((lengths L hw).1.trans (lengths L hw).2.symm) hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
  have inputs := inputs_mem L hw
  rcases h with rfl | rfl | rfl | h | h
  · tauto
  · tauto
  · tauto
  · exact Or.inr (Or.inl (inputs.2.2 q h))
  · apply Or.inr; apply Or.inr
    have sub : L.dialogPool.take 247 ⊆ L.dialogPool.take 255 := by
      have e : L.dialogPool.take 247=(L.dialogPool.take 255).take 247 := by rw [List.take_take]; rfl
      rw [e]; exact List.take_subset _ _
    exact sub (work_subset L h)

include hw in
theorem clearF_support_old : wires (clearF L) ⊆ wires (ECDSAAdd.Entrant.clrF L) :=
  (CodexAffineGadget.clearProgram_support (a L) (b L) L.point.finite (rest L) (work L) literal).trans
    (clrF_support_old L hw)

include hw in
theorem counts :
    toffoliCount (clrF L)=246 ∧ measurementCount (clrF L)=246 ∧
    toffoliCount (clearF L)=245 ∧ measurementCount (clearF L)=246 := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have p := CodexAffineGadget.program_counts (a L) (b L) L.point.finite (rest L) (work L) literal hl
  have c := CodexAffineGadget.clearProgram_counts (a L) (b L) L.point.finite (rest L) (work L) literal hl
  simpa only [(lengths L hw).1,clrF,clearF] using And.intro p.1 (And.intro p.2 c)

include hw hn in
theorem physical : GatePhysical (clrF L) ∧ GatePhysical (clearF L) := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  exact ⟨CodexAffineGadget.program_physical _ _ _ _ _ _ hl (ports_nodup L hw hn),
    CodexAffineGadget.clearProgram_physical _ _ _ _ _ _ hl (ports_nodup L hw hn)⟩

abbrev zrep := FiniteFlagInterval.zrep
abbrev generic := ReflectionE1TickGapLow48.generic
def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clearF L ++ renameProgram (swapF L) (generic L cx cy) ++ clrF L
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program := zrep L ++ mid L cx cy ++ zrep L

theorem sentinel_finiteBit : finiteBit FiniteFlagInterval.sentinel=false := by
  have eq : FiniteFlagInterval.sentinel=p-1 := by norm_num [FiniteFlagInterval.sentinel,p]
  simp [finiteBit,eq,CodexAffineMath.sentinel_matches]

include hw hn
theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : finiteBit X.val = fin) (h2 : finiteBit X'.val = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clearF_step L hw hn X Y G base (hf.trans h1.symm)
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
        L.point.finite ^^ finiteBit X'.val) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := FiniteFlagInterval.zrep_step L hw hn 0 (FiniteFlagInterval.sentinel : Fp) 0 false s.basis (by rw [hfin, FiniteFlagInterval.sentinel_val]; rfl)
    have mid := midFFused_values L hw hn cx cy (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false s.basis false
      (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn (FiniteFlagInterval.sentinel : Fp) 0 cx cy base' FiniteFlagInterval.sentinel_ne_zero) hfin
      (by rw [FiniteFlagInterval.sentinel_val]; exact sentinel_finiteBit) (by rw [FiniteFlagInterval.sentinel_val]; exact sentinel_finiteBit)
    have z2 := FiniteFlagInterval.zrep_step L hw hn (FiniteFlagInterval.sentinel : Fp) 0 0 false s.basis (by rw [hfin, FiniteFlagInterval.sentinel_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : finiteBit x.val = true := decide_eq_true (CodexAffineMath.curve_x_not_matches hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := FiniteFlagInterval.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := FiniteFlagInterval.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : finiteBit (genericX x y cx cy).val = true :=
        decide_eq_true (CodexAffineMath.curve_x_not_matches (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := FiniteFlagInterval.zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := FiniteFlagInterval.zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))


omit hw hn

attribute [local irreducible] toffoliCount measurementCount gateSlots ReflectionE1TickGapLow48.generic

include hw in
theorem gen_support_subset (cx cy : Fp) :
    wires (gen L cx cy) ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) := by
  intro q used
  have hz : q∈wires (zrep L) → q∈wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => FiniteFlagInterval.zrep_support_old L hw h
  have hc : q∈wires (clrF L) → q∈wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => clrF_support_old L hw h
  have he : q∈wires (clearF L) → q∈wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => clearF_support_old L hw h
  simp only [gen,mid,ReflectionE1TickGapLow48.gen,ReflectionE1TickGapLow48.mid,
    generic,wires_append,Finset.mem_union] at used ⊢
  tauto

include hw hn in
theorem gen_sites (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (ReflectionE1TickGapLow48.gen_sites L hw hn cx cy)

include hw in
theorem gen_counts (cx cy : Fp) :
    toffoliCount (gen L cx cy)+2=toffoliCount (FiniteFlagInterval.gen L cx cy) ∧
    measurementCount (gen L cx cy)+2=measurementCount (FiniteFlagInterval.gen L cx cy) := by
  have n := counts L hw
  have o := FiniteFlagInterval.clrF_counts L hw
  have e := FiniteFlagInterval.clearF_counts L hw
  simp only [gen,mid,FiniteFlagInterval.gen,FiniteFlagInterval.mid,FiniteFlagInterval.generic,
    generic,zrep,toffoliCount_append,measurementCount_append,n.1,n.2.1,n.2.2.1,n.2.2.2,
    o.1,o.2,e.1,e.2]
  omega

include hw in
theorem gen_slots (cx cy : Fp) : gateSlots (gen L cx cy)≤gateSlots (FiniteFlagInterval.gen L cx cy) := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have n := CodexAffineGadget.program_slots (a L) (b L) L.point.finite (rest L) (work L) literal hl
  have e := CodexAffineGadget.clearProgram_slots (a L) (b L) L.point.finite (rest L) (work L) literal hl
  rw [(lengths L hw).1] at n e
  change gateSlots (clrF L)≤9*246+6 at n
  change gateSlots (clearF L)≤9*246+6 at e
  have o := FiniteFlagInterval.clrF_slots_exact L hw
  have c := FiniteFlagInterval.clearF_slots L hw
  simp only [gen,mid,FiniteFlagInterval.gen,FiniteFlagInterval.mid,FiniteFlagInterval.generic,
    generic,zrep,gateSlots_append]
  omega

include hw hn in
theorem gen_physical (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z := FiniteFlagInterval.zrep_physical L hn
  have c := (physical L hw hn).1
  have e := (physical L hw hn).2
  have g := gatePhysical_rename (swapF L) (swapF_injective L hw hn) _
    (ReflectionE1TickGapLow48.generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append,generic,zrep] using And.intro (And.intro z (And.intro (And.intro e g) c)) z

include hw in
theorem wrapper_counts (C : Point) (cx cy : Fp) :
    toffoliCount (Edges.wrapper L C cy (gen L cx cy))+2=
      toffoliCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    measurementCount (Edges.wrapper L C cy (gen L cx cy))+2=
      measurementCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    gateSlots (Edges.wrapper L C cy (gen L cx cy))≤
      gateSlots (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) := by
  have h := gen_counts L hw cx cy
  have s := gen_slots L hw cx cy
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,renameProgram_counts,rename_gateSlots]
  omega

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1587 := by
  have h := FiniteFlagInterval.wrapper_support_mono layout C cy _ _
    (gen_support_subset layout layout_widths cx cy)
  exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
    (ReflectionE1TickGapLow48.wrapper_qubits760 C cx cy)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      FusedFlags.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2147982,1498873,1587,50240570⟩

theorem program_correct (C : Point) (control : Bool) (R : Point) :
    Triple (encodes control R) (program C) (encodes control (if control then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := gen_sites layout layout_widths layout_nodup cx cy
    have support := (FusedFlags.wrapper_support layout hc (gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ control R _
      (FusedFlags.full_spec layout layout_widths layout_nodup R hc control _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2147982 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤2147982
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498873 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤1498873
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1587 := by
  cases C with
  | zero => change qubits []≤1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := FusedFlags.wrapper_support layout hc (gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (wrapper_qubits (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact FusedFlags.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50240570 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.2
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    have growth : Rolling1588.slotGrowth=24925 := rfl
    rw [growth] at old
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤50240570
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C control R := (normalize_triple _ _ _).mpr (program_correct C control R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498873
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50240570
    rw [normalize_slots]; exact program_gateSlots C

end ECDSAAdd.Entrant.CodexAffineProbe
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityMath =====
section
namespace ECDSAAdd.Entrant.CodexYParityMath
open Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

def highX (v : Nat) : Prop :=
  v / 1024 % 4194304 = 4194303 ∧
  v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607

instance : DecidablePred highX := fun v => inferInstanceAs (Decidable
  (v / 1024 % 4194304 = 4194303 ∧
  v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607))

def yParity (v : Nat) : Bool :=
  decide (v / 6901746346790563787434755862277025452451108972170386555162524223799296 % 2 = 1) ^^
  decide (v / 441711766194596082395824375185729628956870974218904739530401550323154944 % 2 = 1) ^^
  decide (v / 883423532389192164791648750371459257913741948437809479060803100646309888 % 2 = 1) ^^
  decide (v / 1766847064778384329583297500742918515827483896875618958121606201292619776 % 2 = 1) ^^
  decide (v / 113078212145816597093331040047546785012958969400039613319782796882727665664 % 2 = 1) ^^
  decide (v / 226156424291633194186662080095093570025917938800079226639565593765455331328 % 2 = 1) ^^
  decide (v / 452312848583266388373324160190187140051835877600158453279131187530910662656 % 2 = 1) ^^
  decide (v / 3618502788666131106986593281521497120414687020801267626233049500247285301248 % 2 = 1)

def matchesXY (x y : Nat) : Prop := highX x ∧ yParity y = false
instance (x y : Nat) : Decidable (matchesXY x y) := inferInstanceAs (Decidable (highX x ∧ yParity y = false))

theorem highX_range (v : Nat) (hv : v < p) (h : highX v) : p-47 ≤ v := by
  unfold highX at h
  norm_num [p] at hv ⊢
  omega

theorem sentinel_matches : matchesXY (p-1) 0 := by
  norm_num [matchesXY,highX,yParity,p]

private theorem nonsquare {a y : Fp} (power : a^((p-1)/2) = -1) (hs : y^2 = a) : False := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y≠0 := by
    intro hz
    rw [←hs,hz,zero_pow (by decide),zero_pow (by norm_num [p])] at power
    simp at power
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have even : p-1=2*((p-1)/2) := by norm_num [p]
  rw [even,pow_mul,hs,power] at fermat
  have ne : (-1 : Fp)≠1 := by decide
  exact ne fermat

private theorem powerTransport (q a : Nat) (hq : q=p)
    (h : ((a : ZMod q)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1) :
    ((a : Fp)^3+7)^((p-1)/2) = -1 := by
  have he : (p-1)/2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by norm_num [p]
  rw [he]
  subst q
  exact h

private theorem squareTransport (q a r : Nat) (hq : q=p)
    (h : (r : ZMod q)^2 = (a : ZMod q)^3+7) :
    (r : Fp)^2 = (a : Fp)^3+7 := by
  subst q
  exact h

private theorem case_1 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671662 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671662 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_2 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671661 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671661 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_3 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671660 : Fp)^3+7) : yParity y.val = true := by
  have hr : (6603225675942137755722016048183769717410321709583529039474051610042430502525 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671660 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_4 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671659 : Fp)^3+7) : yParity y.val = true := by
  have hr : (59494462493979449647570233702496999513658646306271329894531992659739671393069 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671659 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_5 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671658 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671658 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_6 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671657 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671657 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_7 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671656 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_8 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671655 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671655 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_9 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671654 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671654 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_10 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671653 : Fp)^3+7) : yParity y.val = true := by
  have hr : (32675455276886538377135961527970747392999635122131544003589039477106874644692 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671653 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_11 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671652 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671652 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_12 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671651 : Fp)^3+7) : yParity y.val = true := by
  have hr : (26128689524504706065261118141317656197887299188579002162273527811606361449708 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671651 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_13 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671650 : Fp)^3+7) : yParity y.val = true := by
  have hr : (8577303908373580249506288492821825305199069524882698424576740044335877264616 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671650 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_14 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671649 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671649 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_15 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671648 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671648 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_16 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671647 : Fp)^3+7) : yParity y.val = true := by
  have hr : (91140719503136456702788776376224035068647810528229755089092598492509977513391 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671647 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_17 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671646 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671646 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_18 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671645 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671645 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_19 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671644 : Fp)^3+7) : yParity y.val = true := by
  have hr : (39884473096376270427702265980090836962804851088800575884979558070656540211742 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671644 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_20 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671643 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671643 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_21 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671642 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671642 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_22 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671641 : Fp)^3+7) : yParity y.val = true := by
  have hr : (87858050732041572112946130011090019437744585579749573053061107584625869568789 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671641 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_23 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671640 : Fp)^3+7) : yParity y.val = true := by
  have hr : (108804142492889174614636371636043929694359971927800610566698906308390880838775 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671640 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_24 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671639 : Fp)^3+7) : yParity y.val = true := by
  have hr : (90251269264737004142706139481528124213741093942080018241141466145201744297488 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671639 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_25 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671638 : Fp)^3+7) : yParity y.val = true := by
  have hr : (75235462138975110463823503735425296584550141080759035749156047496719874561987 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671638 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_26 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671637 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671637 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_27 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671636 : Fp)^3+7) : yParity y.val = true := by
  have hr : (86939888355575964094991750730646468908583063016749246259798665632714130501197 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671636 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_28 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671635 : Fp)^3+7) : yParity y.val = true := by
  have hr : (4182962361524284598535907236655905568231458553838165214763798974835028006434 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671635 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_29 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671634 : Fp)^3+7) : yParity y.val = true := by
  have hr : (68955841494607169053734295970461238553869482894404290786540257300019047034624 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671634 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_30 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671633 : Fp)^3+7) : yParity y.val = true := by
  have hr : (49733659202714845321509626322873875871991168724474382738121548382114922697663 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671633 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_31 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671632 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671632 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_32 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671631 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671631 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_33 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671630 : Fp)^3+7) : yParity y.val = true := by
  have hr : (44691740129539857302436916955866976963397033623780589459590642317128159632006 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671630 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_34 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671629 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671629 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_35 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671628 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671628 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_36 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671627 : Fp)^3+7) : yParity y.val = true := by
  have hr : (51193769181865963694859153139841532078256707687335846879742476169529437790917 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671627 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_37 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671626 : Fp)^3+7) : yParity y.val = true := by
  have hr : (103618749943476312868418606276677894873806957446321936724134933650386344711784 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671626 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_38 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671625 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671625 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_39 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671624 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671624 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_40 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671623 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671623 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_41 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671622 : Fp)^3+7) : yParity y.val = true := by
  have hr : (66850597368902350158169512472851730375964505860741535628662529042753517520652 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671622 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_42 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671621 : Fp)^3+7) : yParity y.val = true := by
  have hr : (70401031564568261752508033145049036971610607287643400116337276464925705083252 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671621 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_43 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671620 : Fp)^3+7) : yParity y.val = true := by
  have hr : (16630661555480012533216961328463789703838228518257063889232934184924812474445 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671620 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_44 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671619 : Fp)^3+7) : yParity y.val = true := by
  have hr : (107334166703719341558589207297916674948985469142494621554787815725265730778893 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671619 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_45 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671618 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671618 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_46 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671617 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671617 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_47 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671616 : Fp)^3+7) : yParity y.val = true := by
  have hr : (112234481090334865465835242450756667684869773413855542198653146390767513213554 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671616 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

theorem highX_curve_parity {x y : Fp} (hc : curve.toAffine.Nonsingular x y)
    (hx : highX x.val) : yParity y.val = true := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  have hv := ZMod.val_lt x
  have lo := highX_range x.val hv hx
  have equation := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at equation
  have square : y^2 = x^3+7 := by simpa [curve,curveA,curveB] using equation
  have xv : (x.val : Fp) = x := ZMod.natCast_zmod_val x
  rw [←xv] at square
  have hcases : x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671662 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671661 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671660 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671659 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671658 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671657 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671656 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671653 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671652 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671651 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671650 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671649 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671648 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671647 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671646 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671645 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671644 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671643 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671642 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671641 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671640 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671639 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671638 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671637 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671636 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671635 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671634 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671633 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671632 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671631 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671630 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671629 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671628 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671627 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671626 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671625 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671624 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671623 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671622 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671621 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671620 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671619 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671618 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671617 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671616 := by
    norm_num [p] at lo hv
    omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47
  · rw [h1] at square; exact case_1 y square
  · rw [h2] at square; exact case_2 y square
  · rw [h3] at square; exact case_3 y square
  · rw [h4] at square; exact case_4 y square
  · rw [h5] at square; exact case_5 y square
  · rw [h6] at square; exact case_6 y square
  · rw [h7] at square; exact case_7 y square
  · rw [h8] at square; exact case_8 y square
  · rw [h9] at square; exact case_9 y square
  · rw [h10] at square; exact case_10 y square
  · rw [h11] at square; exact case_11 y square
  · rw [h12] at square; exact case_12 y square
  · rw [h13] at square; exact case_13 y square
  · rw [h14] at square; exact case_14 y square
  · rw [h15] at square; exact case_15 y square
  · rw [h16] at square; exact case_16 y square
  · rw [h17] at square; exact case_17 y square
  · rw [h18] at square; exact case_18 y square
  · rw [h19] at square; exact case_19 y square
  · rw [h20] at square; exact case_20 y square
  · rw [h21] at square; exact case_21 y square
  · rw [h22] at square; exact case_22 y square
  · rw [h23] at square; exact case_23 y square
  · rw [h24] at square; exact case_24 y square
  · rw [h25] at square; exact case_25 y square
  · rw [h26] at square; exact case_26 y square
  · rw [h27] at square; exact case_27 y square
  · rw [h28] at square; exact case_28 y square
  · rw [h29] at square; exact case_29 y square
  · rw [h30] at square; exact case_30 y square
  · rw [h31] at square; exact case_31 y square
  · rw [h32] at square; exact case_32 y square
  · rw [h33] at square; exact case_33 y square
  · rw [h34] at square; exact case_34 y square
  · rw [h35] at square; exact case_35 y square
  · rw [h36] at square; exact case_36 y square
  · rw [h37] at square; exact case_37 y square
  · rw [h38] at square; exact case_38 y square
  · rw [h39] at square; exact case_39 y square
  · rw [h40] at square; exact case_40 y square
  · rw [h41] at square; exact case_41 y square
  · rw [h42] at square; exact case_42 y square
  · rw [h43] at square; exact case_43 y square
  · rw [h44] at square; exact case_44 y square
  · rw [h45] at square; exact case_45 y square
  · rw [h46] at square; exact case_46 y square
  · rw [h47] at square; exact case_47 y square

theorem curve_not_matches {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    ¬ matchesXY x.val y.val := by
  rintro ⟨hx,hy⟩
  have yes := highX_curve_parity hc hx
  rw [yes] at hy
  contradiction

end ECDSAAdd.Entrant.CodexYParityMath
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityGadget =====
section
/-
Research helper: generic affine parity view for the 246-condition finite probe.
Standalone real-source compilation passed; full integrated certificate remains pending.
Import is for a minimal helper tree containing the official-validated MeasuredZeroClear module;
when integrated into the consolidated Main, omit this import and retain the namespace.
-/

namespace ECDSAAdd.Entrant.CodexYParityGadget
open Arithmetic RecordedQuantum Challenge Baselines

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def parity (xs : List Wire) (s : BasisState) : Bool :=
  xs.foldr (fun x t => s x ^^ t) false

def fan (xs : List Wire) (b : Wire) : Program := xs.map (fun x => .CX x b)
def view (xs : List Wire) (b : Wire) : Program := fan xs b ++ [.X b]
def restore (xs : List Wire) (b : Wire) : Program := [.X b] ++ fan xs.reverse b
def core (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ equalConstant b f (zeroPorts r work) k
def program (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view xs b ++ core b f r work k ++ restore xs b
def clearCore (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ MeasuredZeroClear.equalClear b f (zeroPorts r work) k
def clearProgram (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view xs b ++ clearCore b f r work k ++ restore xs b

theorem run_concat (P Q : Program) (m : List Bool) (s : State) :
    run (P ++ Q) m s = run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append, run_take]

theorem ports_length (r work : List Wire) (hl : r.length = work.length) :
    (zeroPorts r work).length = r.length := by
  have h := congrArg List.length (zeroPorts_maps r work hl).1
  simpa using h

theorem parity_congr (xs : List Wire) (s t : BasisState)
    (h : ∀ q ∈ xs, s q = t q) : parity xs s = parity xs t := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (s x ^^ parity xs s) = (t x ^^ parity xs t)
    rw [h x (by simp), ih (fun q hq => h q (by simp [hq]))]

theorem parity_append (xs ys : List Wire) (s : BasisState) :
    parity (xs ++ ys) s = (parity xs s ^^ parity ys s) := by
  induction xs with
  | nil => simp [parity]
  | cons x xs ih =>
    change (s x ^^ parity (xs ++ ys) s) = ((s x ^^ parity xs s) ^^ parity ys s)
    rw [ih, Bool.xor_assoc]

theorem parity_reverse (xs : List Wire) (s : BasisState) :
    parity xs.reverse s = parity xs s := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, parity_append, ih]
    change (parity xs s ^^ parity [x] s) = (s x ^^ parity xs s)
    simp [parity, Bool.xor_comm]

theorem fan_counts (xs : List Wire) (b : Wire) :
    toffoliCount (fan xs b) = 0 ∧ measurementCount (fan xs b) = 0 := by
  induction xs with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih => simpa only [fan, List.map_cons, toffoliCount, measurementCount] using ih

theorem fan_slots (xs : List Wire) (b : Wire) : gateSlots (fan xs b) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa [fan, gateSlots, instructionSlots, Nat.add_comm] using congrArg Nat.succ ih

theorem fan_support (xs : List Wire) (b : Wire) :
    wires (fan xs b) ⊆ (b :: xs).toFinset := by
  induction xs with
  | nil => simp [fan, wires]
  | cons x xs ih =>
    intro q hq
    simp only [fan, List.map_cons, wires, Instr.wires, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with (rfl | rfl) | hq
    · simp
    · simp
    · have h := ih hq
      simp only [List.mem_toFinset, List.mem_cons] at h ⊢
      tauto

theorem fan_physical (xs : List Wire) (b : Wire) (hb : b ∉ xs) :
    GatePhysical (fan xs b) := by
  intro i hi
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
  have hqb : q ≠ b := fun e => hb (e ▸ hq)
  simpa [PhysicalInstr, ProperGate] using hqb

-- This induction is the same affine fan semantics already used in TerminalGraph.
theorem fan_run (xs : List Wire) (b : Wire) (hb : b ∉ xs)
    (s : State) (m : List Bool) :
    run (fan xs b) m s =
      ⟨s.phase, writeBit s.basis b (s.basis b ^^ parity xs s.basis)⟩ := by
  induction xs generalizing s with
  | nil =>
    simp only [fan, List.map_nil, run, parity, List.foldr_nil, Bool.xor_false]
    cases s with
    | mk phase basis =>
      apply congrArg (State.mk phase)
      funext q
      by_cases hq : q = b <;> simp [writeBit, hq]
  | cons x xs ih =>
    have tail : b ∉ xs := fun h => hb (by simp [h])
    let t : State := ⟨s.phase, writeBit s.basis b (s.basis b ^^ s.basis x)⟩
    have same : parity xs t.basis = parity xs s.basis := parity_congr _ _ _ (by
      intro q hq
      have hqb : q ≠ b := fun e => tail (e ▸ hq)
      simp [t, writeBit, hqb])
    simp only [fan, List.map_cons, run]
    change run (fan xs b) m t = _
    rw [ih tail t, same]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q = b
    · subst q
      simp [t, writeBit, parity, Bool.xor_assoc]
    · simp [t, writeBit, hq]

theorem view_counts (xs : List Wire) (b : Wire) :
    toffoliCount (view xs b) = 0 ∧ measurementCount (view xs b) = 0 := by
  simp [view, toffoliCount_append, measurementCount_append, fan_counts,
    toffoliCount, measurementCount]

theorem restore_counts (xs : List Wire) (b : Wire) :
    toffoliCount (restore xs b) = 0 ∧ measurementCount (restore xs b) = 0 := by
  simp [restore, toffoliCount_append, measurementCount_append, fan_counts,
    toffoliCount, measurementCount]

theorem view_support (xs : List Wire) (b : Wire) :
    wires (view xs b) ⊆ (b :: xs).toFinset := by
  intro q hq
  simp only [view, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact fan_support xs b hq
  · have hqb : q = b := by simpa [wires, Instr.wires] using hq
    simp [hqb]

theorem restore_support (xs : List Wire) (b : Wire) :
    wires (restore xs b) ⊆ (b :: xs).toFinset := by
  intro q hq
  simp only [restore, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · have hqb : q = b := by simpa [wires, Instr.wires] using hq
    simp [hqb]
  · simpa only [List.mem_toFinset, List.mem_cons, List.mem_reverse] using
      fan_support xs.reverse b hq

theorem ports_nodup (xs : List Wire) (b f : Wire) (r work : List Wire)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) :
    (b :: f :: (zeroPorts r work).flatMap ZeroBit.wires).Nodup := by
  have keep : (b :: f :: (r ++ work)).Nodup := by
    exact List.Nodup.sublist
      (List.Sublist.cons₂ b (List.Sublist.cons₂ f (List.sublist_append_right xs (r ++ work)))) hn
  exact (((zeroPorts_perm r work hl).cons f).cons b).nodup_iff.mpr keep

theorem view_run (xs : List Wire) (b : Wire) (hb : b ∉ xs)
    (s : State) (m : List Bool) :
    run (view xs b) m s =
      ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))⟩ := by
  rw [view, run_concat, (fan_counts xs b).2, List.drop_zero, fan_run xs b hb]
  simp [run, writeBit]

theorem restore_update (xs : List Wire) (b f : Wire)
    (hb : b ∉ xs) (hf : f ∉ xs) (hbf : b ≠ f)
    (s : State) (m : List Bool) (z : Bool) :
    run (restore xs b) m
      ⟨s.phase, writeBit (writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))) f z⟩ =
      ⟨s.phase, writeBit s.basis f z⟩ := by
  let t : State := ⟨s.phase, writeBit
    (writeBit (writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))) f z)
    b (s.basis b ^^ parity xs s.basis)⟩
  have first : run [Instr.X b] m
      ⟨s.phase, writeBit (writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))) f z⟩ = t := by
    simp [run, t, writeBit, hbf]
  have same : parity xs t.basis = parity xs s.basis := parity_congr _ _ _ (by
    intro q hq
    simp [t, writeBit, show q ≠ b from fun e => hb (e ▸ hq),
      show q ≠ f from fun e => hf (e ▸ hq)])
  rw [restore, run_concat, show measurementCount [Instr.X b] = 0 from rfl,
    List.drop_zero, first, fan_run xs.reverse b (by simpa using hb), parity_reverse, same]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = b
  · subst q
    cases hp : parity xs s.basis <;> cases hs : s.basis b <;>
      simp [t, writeBit, hbf, hp, hs]
  · by_cases hqf : q = f
    · subst q
      simp [t, writeBit, hbf.symm]
    · simp [t, writeBit, hq, hqf]

theorem program_run (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) (hl : r.length = work.length)
    (hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0) :
    run (program xs b f r work k) m s =
      ⟨s.phase, writeBit s.basis f
        (s.basis f ^^ !((!(s.basis b ^^ parity xs s.basis)) && decide (regValue r s.basis = k)))⟩ := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have hbf : b ≠ f := sep.1.1
  have hbx : b ∉ xs := sep.1.2.1
  have hbr : b ∉ r := sep.1.2.2.1
  have hbw : b ∉ work := sep.1.2.2.2
  have hfx : f ∉ xs := sep.2.1.1
  have hfr : f ∉ r := sep.2.1.2.1
  have hfw : f ∉ work := sep.2.1.2.2
  let u : State := ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))⟩
  let v : State := ⟨s.phase, writeBit u.basis f (!s.basis f)⟩
  have hu : run (view xs b) m s = u := view_run xs b hbx s m
  have uv : run [.X f] m u = v := by simp [run, u, v, writeBit, hbf.symm]
  have hports := zeroPorts_maps r work hl
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← hports.2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    simpa [v, u, writeBit, neb, nef] using (regValue_zero work s.basis).mp hz p.work mem
  have hr : regValue r v.basis = regValue r s.basis := by
    apply regValue_congr
    intro q hq
    simp [v, u, writeBit, show q ≠ b from fun e => hbr (e ▸ hq),
      show q ≠ f from fun e => hfr (e ▸ hq)]
  have eq := equalConstant_correct b f (zeroPorts r work) k (ports_nodup xs b f r work hl hn)
    (by simpa only [ports_length r work hl] using hk) v m clean
  rw [hports.1, hr] at eq
  have vb : v.basis b = !(s.basis b ^^ parity xs s.basis) := by simp [v, u, writeBit, hbf]
  have vf : v.basis f = !s.basis f := by simp [v, writeBit]
  rw [vb, vf] at eq
  have folded : ((!s.basis f) ^^
      (!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k))) =
      (s.basis f ^^ !(!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k))) := by
    cases s.basis f <;> cases (!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k)) <;> rfl
  rw [folded] at eq
  have shape : run (program xs b f r work k) m s =
      run (restore xs b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      (view_counts xs b).2,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, hu, uv]
  rw [shape, eq]
  simpa only [v, u, writeBit, Function.update_idem] using
    restore_update xs b f hbx hfx hbf s (m.drop (zeroPorts r work).length)
      (s.basis f ^^ !(!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k)))

theorem program_counts (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (program xs b f r work k) = r.length ∧
    measurementCount (program xs b f r work k) = r.length := by
  simp [program, core, toffoliCount_append, measurementCount_append,
    (view_counts xs b).1, (view_counts xs b).2,
    (restore_counts xs b).1, (restore_counts xs b).2,
    equalConstant_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem clearProgram_counts (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (clearProgram xs b f r work k) = r.length - 1 ∧
    measurementCount (clearProgram xs b f r work k) = r.length := by
  simp [clearProgram, clearCore, toffoliCount_append, measurementCount_append,
    (view_counts xs b).1, (view_counts xs b).2,
    (restore_counts xs b).1, (restore_counts xs b).2,
    MeasuredZeroClear.equal_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem program_support (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    wires (program xs b f r work k) ⊆ (b :: f :: (xs ++ (r ++ work))).toFinset := by
  have hsmall (q : Wire) (hq : q ∈ (b :: xs).toFinset) :
      q ∈ (b :: f :: (xs ++ (r ++ work))).toFinset := by
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hq ⊢
    tauto
  intro q hq
  simp only [program, core, wires_append, Finset.mem_union] at hq
  rcases hq with (hq | (hq | hq)) | hq
  · exact hsmall q (view_support xs b hq)
  · have hfq : q = f := by simpa [wires, Instr.wires] using hq
    simp [hfq]
  · have hp : q ∈ (zeroPorts r work).flatMap ZeroBit.wires ↔ q ∈ r ++ work :=
      (zeroPorts_perm r work hl).mem_iff
    simp only [equalConstant_wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, List.mem_toFinset, List.mem_cons, List.mem_append, hp] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto
  · exact hsmall q (restore_support xs b hq)

theorem clearProgram_support (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) :
    wires (clearProgram xs b f r work k) ⊆ wires (program xs b f r work k) := by
  simp only [clearProgram, clearCore, program, core, wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _)
        (MeasuredZeroClear.equal_support b f (zeroPorts r work) k)))
    (Finset.Subset.refl _)

theorem clearProgram_run_eq (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup)
    (s : State) (m : List Bool) (hz : regValue work s.basis = 0)
    (hzero : (run (program xs b f r work k) m s).basis f = false) :
    run (clearProgram xs b f r work k) m s = run (program xs b f r work k) m s := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have hbf : b ≠ f := sep.1.1
  have hbx : b ∉ xs := sep.1.2.1
  have hbw : b ∉ work := sep.1.2.2.2
  have hfx : f ∉ xs := sep.2.1.1
  have hfw : f ∉ work := sep.2.1.2.2
  let v := run [Instr.X f] m (run (view xs b) m s)
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← (zeroPorts_maps r work hl).2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    change (run [Instr.X f] m (run (view xs b) m s)).basis p.work = false
    rw [view_run xs b hbx]
    simpa [run, writeBit, neb, nef] using (regValue_zero work s.basis).mp hz p.work mem
  have oldShape : run (program xs b f r work k) m s =
      run (restore xs b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      (view_counts xs b).2,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have newShape : run (clearProgram xs b f r work k) m s =
      run (restore xs b) (m.drop (zeroPorts r work).length)
        (run (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) m v) := by
    simp only [clearProgram, clearCore, run_concat, measurementCount_append,
      (view_counts xs b).2,
      show measurementCount [Instr.X f] = 0 from rfl,
      (MeasuredZeroClear.equal_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have away : f ∉ wires (restore xs b) := by
    intro hf
    have h := restore_support xs b hf
    simp only [List.mem_toFinset, List.mem_cons] at h
    exact h.elim (fun e => hbf e.symm) hfx
  have keep := run_preserves_outside (restore xs b) (m.drop (zeroPorts r work).length)
    (run (equalConstant b f (zeroPorts r work) k) m v) f away
  have zero : (run (equalConstant b f (zeroPorts r work) k) m v).basis f = false := by
    rw [oldShape] at hzero
    exact keep.symm.trans hzero
  have eq := MeasuredZeroClear.equal_run_eq b f (zeroPorts r work) k
    (ports_nodup xs b f r work hl hn) v m clean zero
  rw [oldShape, newShape, eq]

theorem clearProgram_eq (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) (hl : r.length = work.length)
    (_hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0)
    (hzero : (run (program xs b f r work k) m s).basis f = false) :
    run (clearProgram xs b f r work k) m s = run (program xs b f r work k) m s :=
  clearProgram_run_eq xs b f r work k hl hn s m hz hzero

theorem program_physical (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) :
    GatePhysical (program xs b f r work k) := by
  have hbx : b ∉ xs := by
    intro h
    exact (List.nodup_cons.mp hn).1 (by simp [h])
  have hv : GatePhysical (view xs b) := by
    rw [view, gatePhysical_append]
    exact ⟨fan_physical xs b hbx, by simp [GatePhysical, PhysicalInstr, ProperGate]⟩
  have hr : GatePhysical (restore xs b) := by
    rw [restore, gatePhysical_append]
    exact ⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
      fan_physical xs.reverse b (by simpa using hbx)⟩
  simp only [program, core, gatePhysical_append]
  exact ⟨⟨hv, ⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
    equalConstant_physical b f (zeroPorts r work) k (ports_nodup xs b f r work hl hn)⟩⟩, hr⟩

theorem clearProgram_physical (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) :
    GatePhysical (clearProgram xs b f r work k) := by
  have old := program_physical xs b f r work k hl hn
  simp only [program, core, gatePhysical_append] at old
  simp only [clearProgram, clearCore, gatePhysical_append]
  exact ⟨⟨old.1.1, ⟨old.1.2.1,
    MeasuredZeroClear.equal_physical b f (zeroPorts r work) k
      (ports_nodup xs b f r work hl hn)⟩⟩, old.2⟩

theorem program_slots (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (program xs b f r work k) ≤ 9 * r.length + 2 * xs.length + 4 := by
  have h := equalConstant_gateSlots_le b f (zeroPorts r work) k
  rw [ports_length r work hl] at h
  simp only [program, core, view, restore, gateSlots_append, fan_slots, List.length_reverse]
  change (xs.length + 1) + (1 + gateSlots (equalConstant b f (zeroPorts r work) k)) +
    (1 + xs.length) ≤ _
  omega

theorem clearProgram_slots_le (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) :
    gateSlots (clearProgram xs b f r work k) ≤ gateSlots (program xs b f r work k) := by
  have h : gateSlots (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) ≤
      gateSlots (equalConstant b f (zeroPorts r work) k) := by
    by_cases he : zeroPorts r work = []
    · rw [he]
      exact Nat.le_refl _
    · have h := MeasuredZeroClear.equal_slots b f (zeroPorts r work) k he
      omega
  simp only [clearProgram, clearCore, program, core, gateSlots_append]
  omega

theorem clearProgram_slots (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (clearProgram xs b f r work k) ≤ 9 * r.length + 2 * xs.length + 4 :=
  (clearProgram_slots_le xs b f r work k).trans (program_slots xs b f r work k hl)

end ECDSAAdd.Entrant.CodexYParityGadget
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityBridge =====
section
namespace ECDSAAdd.Entrant.CodexYParityProbe
open Arithmetic ControlledPointLayout
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

def b (L : ControlledPointLayout) : Wire := L.point.y.getD 232 0
def xs (L : ControlledPointLayout) : List Wire :=
  [238,239,240,246,247,248,251].map (fun i => L.point.y.getD i 0)
def rest (L : ControlledPointLayout) : List Wire :=
  (L.point.x.drop 10).take 22 ++ L.point.x.drop 33
def work (L : ControlledPointLayout) : List Wire := L.dialogPool.take 245
def literal : Nat := 2^245-1

private theorem drop_sublist_drop (r : List Wire) (a b : Nat) (hab : a ≤ b) :
    (r.drop b).Sublist (r.drop a) := by
  have e : r.drop b = (r.drop a).drop (b-a) := by
    rw [List.drop_drop]; congr 1; omega
  rw [e]
  exact List.drop_sublist _ _

private theorem getD_range (r : List Wire) (n : Nat) (hn : r.length=n) :
    (List.range n).map (fun i => r.getD i 0)=r := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem _ _ hj

theorem rest_sublist (L : ControlledPointLayout) : (rest L).Sublist L.point.x := by
  have h : (L.point.x.drop 33).Sublist ((L.point.x.drop 10).drop 22) := by
    rw [List.drop_drop]
    exact drop_sublist_drop _ _ _ (by omega)
  have h' := List.Sublist.append (List.Sublist.refl ((L.point.x.drop 10).take 22)) h
  rw [List.take_append_drop] at h'
  exact h'.trans (List.drop_sublist _ _)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
private theorem point_x_length : L.point.x.length=256 := hw.inputX
include hw in
private theorem point_y_length : L.point.y.length=256 := hw.inputY

include hw in
theorem y_sublist : (b L :: xs L).Sublist L.point.y := by
  have h : ([232,238,239,240,246,247,248,251] : List Nat).Sublist (List.range 256) := by decide
  have hm := h.map (fun i => L.point.y.getD i 0)
  rw [getD_range L.point.y 256 (point_y_length L hw)] at hm
  simpa only [b,xs,List.map_cons] using hm

include hw in
theorem lengths : (rest L).length=245 ∧ (work L).length=245 := by
  simp [rest,work,point_x_length L hw,L.dialogPool_length hw]

theorem work_subset : work L ⊆ L.dialogPool.take 255 := by
  have h : work L=(L.dialogPool.take 255).take 245 := by
    simp only [work,List.take_take]; rfl
  rw [h]
  exact List.take_subset _ _

include hw hn in
theorem ports_nodup :
    (b L :: L.point.finite :: (xs L ++ (rest L ++ work L))).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hy := (y_sublist L hw).count_le q
  have hx := (rest_sublist L).count_le q
  have hp := (List.take_sublist 245 L.dialogPool).count_le q
  simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
    List.count_nil,List.cons_append,work] at h hy hp ⊢
  omega

include hw in
theorem inputs_mem : b L∈L.point.y ∧ xs L⊆L.point.y ∧ rest L⊆L.point.x := by
  have hy := (y_sublist L hw).subset
  refine ⟨hy (by simp),?_,(rest_sublist L).subset⟩
  intro q hq
  exact hy (List.mem_cons_of_mem _ hq)

include hw in
theorem rest_value (s : BasisState) :
    regValue (rest L) s = regValue L.point.x s / 1024 % 4194304 +
      4194304 * (regValue L.point.x s / 8589934592) := by
  have lo : regValue ((L.point.x.drop 10).take 22) s =
      regValue L.point.x s / 2^10 % 2^22 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by simp [point_x_length L hw]),
      CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [point_x_length L hw]; omega)]
  have hi := CuccaroStreamedSquareWideLayout.regValue_drop_div L.point.x 33
    (by rw [point_x_length L hw]; omega) s
  simp only [rest,regValue_append,lo,hi,List.length_take,List.length_drop,point_x_length L hw]
  norm_num

private theorem packed_eq_highX (v : Nat) :
    (v/1024%4194304 + 4194304*(v/8589934592)=literal) ↔ CodexYParityMath.highX v := by
  have h := Nat.mod_lt (v/1024) (by decide : 0<4194304)
  norm_num [literal,CodexYParityMath.highX]
  omega

private theorem bit_value (r : List Wire) (i : Nat) (s : BasisState) (hi : i<r.length) :
    s (r.getD i 0) = decide (regValue r s / 2^i % 2 = 1) := by
  rw [←regValue_bit r i 0 s hi]
  cases s (r.getD i 0) <;> rfl

include hw in
theorem parity_value (s : BasisState) :
    (s (b L) ^^ CodexYParityGadget.parity (xs L) s) =
      CodexYParityMath.yParity (regValue L.point.y s) := by
  have h232 := bit_value L.point.y 232 s (by rw [point_y_length L hw]; decide)
  have h238 := bit_value L.point.y 238 s (by rw [point_y_length L hw]; decide)
  have h239 := bit_value L.point.y 239 s (by rw [point_y_length L hw]; decide)
  have h240 := bit_value L.point.y 240 s (by rw [point_y_length L hw]; decide)
  have h246 := bit_value L.point.y 246 s (by rw [point_y_length L hw]; decide)
  have h247 := bit_value L.point.y 247 s (by rw [point_y_length L hw]; decide)
  have h248 := bit_value L.point.y 248 s (by rw [point_y_length L hw]; decide)
  have h251 := bit_value L.point.y 251 s (by rw [point_y_length L hw]; decide)
  simp only [b,xs,CodexYParityGadget.parity,List.map_cons,List.map_nil,List.foldr_cons,
    List.foldr_nil,Bool.xor_false,h232,h238,h239,h240,h246,h247,h248,h251,
    CodexYParityMath.yParity,Bool.xor_assoc]
  norm_num

include hw in
theorem hit (s : BasisState) :
    (!(s (b L) ^^ CodexYParityGadget.parity (xs L) s) &&
      decide (regValue (rest L) s=literal)) =
      decide (CodexYParityMath.matchesXY (regValue L.point.x s) (regValue L.point.y s)) := by
  rw [parity_value L hw s,rest_value L hw s]
  have he : decide (regValue L.point.x s/1024%4194304 +
      4194304*(regValue L.point.x s/8589934592)=literal) =
      decide (CodexYParityMath.highX (regValue L.point.x s)) := by
    simp only [packed_eq_highX]
  rw [he]
  cases h : CodexYParityMath.yParity (regValue L.point.y s) <;>
    simp [CodexYParityMath.matchesXY,h]

end ECDSAAdd.Entrant.CodexYParityProbe
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParitySupport =====
section
/-
Research-only integration bridge. Not yet compiled.
The two imports are conveniences for a temporary minimal test tree; strip them when
inserting these declarations after the new gadget in the consolidated Main.
-/

namespace ECDSAAdd.Entrant.CodexYParitySupport
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  ReflectionE1TickGapLow48.generic

/-- The new y sources are the only support beyond the original x-only finite probe. -/
theorem probe_support_old (L : ControlledPointLayout) (hw : L.Widths)
    (xs : List Wire) (b : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hb : b ∈ L.point.y)
    (hxs : xs ⊆ L.point.y) (hr : r ⊆ L.point.x)
    (hwork : work ⊆ L.dialogPool.take 255) :
    wires (CodexYParityGadget.program xs b L.point.finite r work k) ⊆
      wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset := by
  rw [FiniteFlagInterval.old_clrF_support L hw]
  intro q hq
  have h := CodexYParityGadget.program_support xs b L.point.finite r work k hl hq
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at h
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
  rcases h with rfl | rfl | h | h | h
  · exact Or.inr hb
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (hxs h)
  · exact Or.inl (Or.inr (Or.inl (hr h)))
  · exact Or.inl (Or.inr (Or.inr (hwork h)))

theorem clear_support_old (L : ControlledPointLayout) (hw : L.Widths)
    (xs : List Wire) (b : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hb : b ∈ L.point.y)
    (hxs : xs ⊆ L.point.y) (hr : r ⊆ L.point.x)
    (hwork : work ⊆ L.dialogPool.take 255) :
    wires (CodexYParityGadget.clearProgram xs b L.point.finite r work k) ⊆
      wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
  (CodexYParityGadget.clearProgram_support xs b L.point.finite r work k).trans
    (probe_support_old L hw xs b r work k hl hb hxs hr hwork)

/-- Apply to the new clearF and clrF after unfolding only the two small wrappers. -/
theorem gen_support_old (L : ControlledPointLayout) (hw : L.Widths)
    (cx cy : Fp) (Clear Restore : Program)
    (he : wires Clear ⊆ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset)
    (hc : wires Restore ⊆ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset) :
    wires (FiniteFlagInterval.zrep L ++
      (Clear ++ renameProgram (swapF L) (ReflectionE1TickGapLow48.generic L cx cy) ++ Restore) ++
      FiniteFlagInterval.zrep L) ⊆
      wires (ReflectionE1TickGapLow48.gen L cx cy) ∪ L.point.y.toFinset := by
  intro q used
  have hz : q ∈ wires (FiniteFlagInterval.zrep L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => FiniteFlagInterval.zrep_support_old L hw h
  have heq : q ∈ wires Clear → q ∈ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
    fun h => he h
  have hcq : q ∈ wires Restore → q ∈ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
    fun h => hc h
  simp only [Finset.mem_union] at heq hcq
  simp only [ReflectionE1TickGapLow48.gen, ReflectionE1TickGapLow48.mid,
    wires_append, Finset.mem_union] at used ⊢
  tauto

theorem point_y_generic (L : ControlledPointLayout) :
    L.point.y.toFinset ⊆ (OB5Support.genericSites L).toFinset := by
  intro q hq
  simp only [OB5Support.genericSites, PointAddLayout.pointWires,
    List.mem_toFinset, List.mem_append, List.mem_cons] at hq ⊢
  tauto

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (P : Program)
    (hP : wires P ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) ∪ L.point.y.toFinset) :
    wires P ⊆ (OB5Support.genericSites L).toFinset := by
  intro q hq
  rcases Finset.mem_union.mp (hP hq) with old | extra
  · exact ReflectionE1TickGapLow48.gen_sites L hw hn cx cy old
  · exact point_y_generic L extra

/-- Relabel an augmented support set when the added set is closed under the map. -/
theorem rename_support_extra (f : Wire → Wire) (P Q : Program) (S : Finset Wire)
    (h : wires P ⊆ wires Q ∪ S) (closed : ∀ q ∈ S, f q ∈ S) :
    wires (renameProgram f P) ⊆ wires (renameProgram f Q) ∪ S := by
  rw [renameProgram_support, renameProgram_support]
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (h hp) with old | extra
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, old, rfl⟩)
  · exact Finset.mem_union_right _ (closed p extra)

/-- All renamings along the generic-input path are explicit here. -/
theorem wrapper_support_extra (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (S : Finset Wire) (h : wires P ⊆ wires Q ∪ S)
    (hU : ∀ q ∈ S, Wrapper5.U L q ∈ S) (hM : ∀ q ∈ S, tauM L q ∈ S)
    (hE : ∀ q ∈ S, swapE L q ∈ S) (hD : ∀ q ∈ S, swapD L q ∈ S) :
    wires (Edges.wrapper L C cy P) ⊆ wires (Edges.wrapper L C cy Q) ∪ S := by
  have u := rename_support_extra (Wrapper5.U L) P Q S h hU
  have m := rename_support_extra (tauM L) _ _ S u hM
  have e := rename_support_extra (swapE L) _ _ S m hE
  have d := rename_support_extra (swapD L) _ _ S e hD
  have finite :
      wires (Edges.finiteProgram L C cy (renameProgram (Wrapper5.U L) P)) ⊆
      wires (Edges.finiteProgram L C cy (renameProgram (Wrapper5.U L) Q)) ∪ S := by
    intro q hq
    have hd : q ∈ wires (renameProgram (swapD L) (renameProgram (swapE L)
        (renameProgram (tauM L) (renameProgram (Wrapper5.U L) P)))) →
        q ∈ wires (renameProgram (swapD L) (renameProgram (swapE L)
        (renameProgram (tauM L) (renameProgram (Wrapper5.U L) Q)))) ∪ S :=
      fun hh => d hh
    simp only [Finset.mem_union] at hd
    simp only [Edges.finiteProgram, wires_append, Finset.mem_union] at hq ⊢
    tauto
  simpa only [Edges.wrapper] using rename_support_extra (Wrapper5.U L) _ _ S finite hU

/-- The concrete public y register is already counted even if idle. -/
theorem layout_y_io : layout.point.y.toFinset ⊆ ioWires := by decide +kernel

/-- Small finite checks: no arithmetic program is unfolded by these four claims. -/
theorem layout_y_images :
    (layout.point.y.toFinset.image (Wrapper5.U layout) ⊆ layout.point.y.toFinset) ∧
    (layout.point.y.toFinset.image (tauM layout) ⊆ layout.point.y.toFinset) ∧
    (layout.point.y.toFinset.image (swapE layout) ⊆ layout.point.y.toFinset) ∧
    (layout.point.y.toFinset.image (swapD layout) ⊆ layout.point.y.toFinset) := by
  decide +kernel

/-- An old-wrapper-plus-I/O support bound preserves the exact previous static Q bound. -/
theorem wrapper_qubits760 (C : Point) (cx cy : Fp) (P : Program)
    (hP : wires P ⊆ wires (ReflectionE1TickGapLow48.gen layout cx cy) ∪ layout.point.y.toFinset) :
    qubits (Edges.wrapper layout C cy P) ≤ 1587 := by
  have images := layout_y_images
  have image_closed (f : Wire → Wire)
      (h : layout.point.y.toFinset.image f ⊆ layout.point.y.toFinset) :
      ∀ q ∈ layout.point.y.toFinset, f q ∈ layout.point.y.toFinset :=
    fun q hq => h (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  have sup := wrapper_support_extra layout C cy P
    (ReflectionE1TickGapLow48.gen layout cx cy) layout.point.y.toFinset hP
    (image_closed _ images.1) (image_closed _ images.2.1)
    (image_closed _ images.2.2.1) (image_closed _ images.2.2.2)
  have absorb : ioWires ∪ wires (Edges.wrapper layout C cy P) ⊆
      ioWires ∪ wires (Edges.wrapper layout C cy (ReflectionE1TickGapLow48.gen layout cx cy)) := by
    intro q hq
    rcases Finset.mem_union.mp hq with io | used
    · exact Finset.mem_union_left _ io
    · rcases Finset.mem_union.mp (sup used) with old | extra
      · exact Finset.mem_union_right _ old
      · exact Finset.mem_union_left _ (layout_y_io extra)
  exact (Finset.card_le_card absorb).trans (ReflectionE1TickGapLow48.wrapper_qubits760 C cx cy)

/-- FusedFlags changes surrounding flag gates but its existing support lemma is sufficient. -/
theorem fused_wrapper_qubits760 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (P : Program)
    (hP : wires P ⊆ wires (ReflectionE1TickGapLow48.gen layout cx cy) ∪ layout.point.y.toFinset) :
    qubits (FusedFlags.wrapper layout (.some hc) cy P) ≤ 1587 := by
  have sub := FusedFlags.wrapper_support layout hc P
  exact (Finset.card_le_card
    (Finset.union_subset_union (Finset.Subset.refl ioWires) sub)).trans
    (wrapper_qubits760 (.some hc) cx cy P hP)

end ECDSAAdd.Entrant.CodexYParitySupport
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityProbe =====
section
/- Research integration draft, not yet compiled as a complete entrant. -/

namespace ECDSAAdd.Entrant.CodexYParityProbe
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires

def finiteBit (v w : Nat) : Bool := decide (¬ CodexYParityMath.matchesXY v w)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

def clrF : Program := CodexYParityGadget.program (xs L) (b L) L.point.finite (rest L) (work L) literal
def clearF : Program := CodexYParityGadget.clearProgram (xs L) (b L) L.point.finite (rest L) (work L) literal

include hw hn in
theorem clrF_run (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0) :
    run (clrF L) m s = ⟨s.phase,writeBit s.basis L.point.finite
      (s.basis L.point.finite ^^ finiteBit (regValue L.point.x s.basis) (regValue L.point.y s.basis))⟩ := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have hk : literal < 2^(rest L).length := by rw [(lengths L hw).1]; decide
  rw [clrF,CodexYParityGadget.program_run _ _ _ _ _ _ (ports_nodup L hw hn) hl hk s m hz,
    hit L hw s.basis]
  simp only [finiteBit,decide_not]

include hw hn in
theorem clearF_eq (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0)
    (hzero : (run (clrF L) m s).basis L.point.finite=false) :
    run (clearF L) m s=run (clrF L) m s := by
  exact CodexYParityGadget.clearProgram_eq _ _ _ _ _ _ (ports_nodup L hw hn)
    ((lengths L hw).1.trans (lengths L hw).2.symm)
    (by rw [(lengths L hw).1]; decide) s m hz hzero

include hw hn in
theorem clrF_step (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (clrF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))) := by
  intro s m v
  have hz : regValue (work L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  rw [clrF_run L hw hn s m hz]
  have hfxy := finite_not_x L hn
  have hfs : s.basis L.point.finite=base L.point.finite := v.rest _ hfxy
  have hfx := fin_not_x L hn
  have hfy : L.point.finite∉L.point.y := fun h => hfxy (List.mem_append_right _ h)
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · show regValue L.point.x (writeBit s.basis L.point.finite _) = _
    rw [←v.x]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => hfx (e ▸ hq)
    simp [writeBit,this]
  · show regValue L.point.y (writeBit s.basis L.point.finite _) = _
    rw [←v.y]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => hfy (e ▸ hq)
    simp [writeBit,this]
  · show writeBit s.basis L.point.finite _ L.core.generic = _
    simp [writeBit,Ne.symm (fin_ne_generic L hn),v.generic]
  · show regValue L.dialogPool (writeBit s.basis L.point.finite _) = _
    rw [←v.clean]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => fin_not_pool L hn (e ▸ hq)
    simp [writeBit,this]
  · intro q hq
    show writeBit s.basis L.point.finite _ q=writeBit base L.point.finite _ q
    by_cases hqf : q=L.point.finite
    · subst hqf; simp [writeBit,hfs,v.x,v.y]
    · simp [writeBit,hqf,v.rest q hq]

include hw hn in
theorem clearF_step (X Y : Fp) (G : Bool) (base : BasisState)
    (hf : base L.point.finite=finiteBit X.val Y.val) :
    Triple (PointDialogValues L X Y G base) (clearF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))) := by
  intro s m v
  have hz : regValue (work L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  have zero : (run (clrF L) m s).basis L.point.finite=false := by
    rw [clrF_run L hw hn s m hz]
    simp [writeBit,v.x,v.y,v.rest _ (finite_not_x L hn),hf]
  rw [clearF_eq L hw hn s m hz zero]
  exact clrF_step L hw hn X Y G base s m v

include hw in
theorem clrF_support_old : wires (clrF L) ⊆
    wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset := by
  have inputs := inputs_mem L hw
  exact CodexYParitySupport.probe_support_old L hw (xs L) (b L) (rest L) (work L) literal
    ((lengths L hw).1.trans (lengths L hw).2.symm) inputs.1 inputs.2.1 inputs.2.2
    (work_subset L)

include hw in
theorem clearF_support_old : wires (clearF L) ⊆
    wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
  (CodexYParityGadget.clearProgram_support (xs L) (b L) L.point.finite (rest L) (work L) literal).trans
    (clrF_support_old L hw)

include hw in
theorem counts :
    toffoliCount (clrF L)=245 ∧ measurementCount (clrF L)=245 ∧
    toffoliCount (clearF L)=244 ∧ measurementCount (clearF L)=245 := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have p := CodexYParityGadget.program_counts (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  have c := CodexYParityGadget.clearProgram_counts (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  simpa only [(lengths L hw).1,clrF,clearF] using And.intro p.1 (And.intro p.2 c)

include hw hn in
theorem physical : GatePhysical (clrF L) ∧ GatePhysical (clearF L) := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  exact ⟨CodexYParityGadget.program_physical _ _ _ _ _ _ hl (ports_nodup L hw hn),
    CodexYParityGadget.clearProgram_physical _ _ _ _ _ _ hl (ports_nodup L hw hn)⟩

abbrev zrep := FiniteFlagInterval.zrep
abbrev generic := ReflectionE1TickGapLow48.generic
def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clearF L ++ renameProgram (swapF L) (generic L cx cy) ++ clrF L
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program := zrep L ++ mid L cx cy ++ zrep L

theorem sentinel_finiteBit : finiteBit FiniteFlagInterval.sentinel 0=false := by
  have eq : FiniteFlagInterval.sentinel=p-1 := by norm_num [FiniteFlagInterval.sentinel,p]
  simp [finiteBit,eq,CodexYParityMath.sentinel_matches]

include hw hn
theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : finiteBit X.val Y.val = fin) (h2 : finiteBit X'.val Y'.val = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clearF_step L hw hn X Y G base (hf.trans h1.symm)
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
        L.point.finite ^^ finiteBit X'.val Y'.val) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := FiniteFlagInterval.zrep_step L hw hn 0 (FiniteFlagInterval.sentinel : Fp) 0 false s.basis (by rw [hfin, FiniteFlagInterval.sentinel_val]; rfl)
    have mid := midFFused_values L hw hn cx cy (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false s.basis false
      (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn (FiniteFlagInterval.sentinel : Fp) 0 cx cy base' FiniteFlagInterval.sentinel_ne_zero) hfin
      (by rw [FiniteFlagInterval.sentinel_val]; exact sentinel_finiteBit) (by rw [FiniteFlagInterval.sentinel_val]; exact sentinel_finiteBit)
    have z2 := FiniteFlagInterval.zrep_step L hw hn (FiniteFlagInterval.sentinel : Fp) 0 0 false s.basis (by rw [hfin, FiniteFlagInterval.sentinel_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : finiteBit x.val y.val = true := decide_eq_true (CodexYParityMath.curve_not_matches hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := FiniteFlagInterval.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := FiniteFlagInterval.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : finiteBit (genericX x y cx cy).val (genericY x y cx cy).val = true :=
        decide_eq_true (CodexYParityMath.curve_not_matches (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := FiniteFlagInterval.zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := FiniteFlagInterval.zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))


omit hw hn

attribute [local irreducible] toffoliCount measurementCount gateSlots ReflectionE1TickGapLow48.generic

include hw in
theorem gen_support_subset (cx cy : Fp) :
    wires (gen L cx cy) ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) ∪ L.point.y.toFinset := by
  exact CodexYParitySupport.gen_support_old L hw cx cy (clearF L) (clrF L)
    (clearF_support_old L hw) (clrF_support_old L hw)

include hw hn in
theorem gen_sites (cx cy : Fp) : wires (gen L cx cy) ⊆ (OB5Support.genericSites L).toFinset :=
  CodexYParitySupport.gen_sites L hw hn cx cy (gen L cx cy) (gen_support_subset L hw cx cy)

include hw in
theorem gen_counts (cx cy : Fp) :
    toffoliCount (gen L cx cy)+4=toffoliCount (FiniteFlagInterval.gen L cx cy) ∧
    measurementCount (gen L cx cy)+4=measurementCount (FiniteFlagInterval.gen L cx cy) := by
  have n := counts L hw
  have o := FiniteFlagInterval.clrF_counts L hw
  have e := FiniteFlagInterval.clearF_counts L hw
  simp only [gen,mid,FiniteFlagInterval.gen,FiniteFlagInterval.mid,FiniteFlagInterval.generic,
    generic,zrep,toffoliCount_append,measurementCount_append,n.1,n.2.1,n.2.2.1,n.2.2.2,
    o.1,o.2,e.1,e.2]
  omega

include hw in
theorem gen_slots (cx cy : Fp) : gateSlots (gen L cx cy)≤gateSlots (FiniteFlagInterval.gen L cx cy) := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have n := CodexYParityGadget.program_slots (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  have e := CodexYParityGadget.clearProgram_slots (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  rw [(lengths L hw).1] at n e
  have hxs : (xs L).length = 7 := by simp [xs]
  rw [hxs] at n e
  change gateSlots (clrF L)≤2223 at n
  change gateSlots (clearF L)≤2223 at e
  have o := FiniteFlagInterval.clrF_slots_exact L hw
  have c := FiniteFlagInterval.clearF_slots L hw
  simp only [gen,mid,FiniteFlagInterval.gen,FiniteFlagInterval.mid,FiniteFlagInterval.generic,
    generic,zrep,gateSlots_append]
  omega

include hw hn in
theorem gen_physical (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z := FiniteFlagInterval.zrep_physical L hn
  have c := (physical L hw hn).1
  have e := (physical L hw hn).2
  have g := gatePhysical_rename (swapF L) (swapF_injective L hw hn) _
    (ReflectionE1TickGapLow48.generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append,generic,zrep] using And.intro (And.intro z (And.intro (And.intro e g) c)) z

include hw in
theorem wrapper_counts (C : Point) (cx cy : Fp) :
    toffoliCount (Edges.wrapper L C cy (gen L cx cy))+4=
      toffoliCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    measurementCount (Edges.wrapper L C cy (gen L cx cy))+4=
      measurementCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    gateSlots (Edges.wrapper L C cy (gen L cx cy))≤
      gateSlots (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) := by
  have h := gen_counts L hw cx cy
  have s := gen_slots L hw cx cy
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,renameProgram_counts,rename_gateSlots]
  omega

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1587 :=
  CodexYParitySupport.wrapper_qubits760 C cx cy (gen layout cx cy)
    (gen_support_subset layout layout_widths cx cy)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      FusedFlags.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2147975,1498871,1587,50240570⟩

theorem program_correct (C : Point) (control : Bool) (R : Point) :
    Triple (encodes control R) (program C) (encodes control (if control then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := gen_sites layout layout_widths layout_nodup cx cy
    have support := (FusedFlags.wrapper_support layout hc (gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ control R _
      (FusedFlags.full_spec layout layout_widths layout_nodup R hc control _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2147975 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤2147975
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498871 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤1498871
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1587 := by
  cases C with
  | zero => change qubits []≤1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := FusedFlags.wrapper_support layout hc (gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (wrapper_qubits (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact FusedFlags.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50240570 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.2
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    have growth : Rolling1588.slotGrowth=24925 := rfl
    rw [growth] at old
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤50240570
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C control R := (normalize_triple _ _ _).mpr (program_correct C control R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498871
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50240570
    rw [normalize_slots]; exact program_gateSlots C

end ECDSAAdd.Entrant.CodexYParityProbe
end

end
