import ECDSAAdd.Submission.Entrant.FullLogic
import ECDSAAdd.Submission.Entrant.MainPart07Core
import ECDSAAdd.Submission.Entrant.ParkAMany
section

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

end
end

end

section

section
set_option Elab.async false

set_option maxRecDepth 100000

set_option maxHeartbeats 100000000

namespace ECDSAAdd.Entrant.AWideSteps

open ECDSAAdd ZeroReadDevelop

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                     

                                                                                                                                             

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 

end ECDSAAdd.Entrant.AWideSteps

end

section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
namespace ECDSAAdd.Entrant.AWideStaged
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ZeroReadDevelop AWideTemp

                                                  
                                      
def suffix : List Wire := [4756,4728,4729,4730,4731,4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755]
                                                                                                                                                                                                                                     

                                                                   
                          

                                                                                 
                                         
                           

                                                                  
                                                                                             

                                                                                         
                                                                      
                 
                                                  
                             
end ECDSAAdd.Entrant.AWideStaged

end

section
set_option Elab.async false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.AWideTemp
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
                                                                                  
                                                                                                     
                                                                       
                     
           
                  
                                                          
                           
                                                                                                 

                         
                                                                                                         
                                                                                                     
                                                                                                                                                                          

                                                              
                                                                        
                                                                       
                                                         
      

                                                                                                 
                                                           
        
                                                                      
                                                            
                                                            

                                                                                      
                                                                                           
                                                                                       
                                                                                           
                                      

                              
end ECDSAAdd.Entrant.AWideTemp

end

section


open ECDSAAdd ECDSAAdd.Entrant ZeroReadDevelop

set_option Elab.async false

set_option maxRecDepth 100000

set_option maxHeartbeats 100000000

namespace ECDSAAdd.Entrant.RepadASteps

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                       

                                                                                                                                               

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   

                   

end ECDSAAdd.Entrant.RepadASteps

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.RepadAReady
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ZeroReadDevelop
open ECDSAAdd.Entrant.AltASelectedDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000

                                                  
                                      
                                                                                                                                                     
                               
                                                                                                                                                                                                                             

                                                                   
                          

                                                                                 
                                          

                                                              
                                                                                             

                                                                                         
                                                                   
                                                              
                 
                                                    
                             
end ECDSAAdd.Entrant.RepadAReady

namespace ECDSAAdd.Entrant.AltASelectedDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false

                                                                                  
                                                                                                     
                                                                       
                     
           
                   
                                                          
                             
                                                                                                                 

                         
                                                                                                         
                                                                                                     
                                                                                                                                                                          

                                                              
                                                                        
                                                                       
                                                          
      

                                                                                                 
                                                           
        
                                                                      
                                                            
                                                            

                                                                                      
                                                                                           
                                                                                       
                                                                                           
                                      

                              
end ECDSAAdd.Entrant.AltASelectedDevelop

end

end

-- Checked finite support witnesses with direct Boolean membership.
namespace ECDSAAdd.Entrant.A161SupportCover
open Arithmetic FourthASavedCarryDevelop A161FixedFold
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] ECDSAAdd.wires

def correctionTouches (q:Wire) : Correction→Bool
 | .Z a => q==a
 | .CZ a b => q==a || q==b

def instructionTouches (q:Wire) : Instr→Bool
 | .X a => q==a
 | .CX a b => q==a || q==b
 | .CCX a b d => q==a || q==b || q==d
 | .measureX a cs ds => q==a || cs.any (correctionTouches q) || ds.any (correctionTouches q)

theorem corrections_spec (cs:List Correction) (q:Wire) :
 cs.any (correctionTouches q)=true ↔ q∈correctionWires cs := by
 induction cs with
 | nil => simp [correctionWires]
 | cons i cs ih => cases i <;> simp only [correctionTouches,correctionWires,List.any_cons,ih,Bool.or_eq_true,beq_iff_eq,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,or_assoc]

theorem instruction_spec (i:Instr) (q:Wire) : instructionTouches q i=true ↔ q∈i.wires := by
 cases i <;> simp only [instructionTouches,Instr.wires,corrections_spec,Bool.or_eq_true,beq_iff_eq,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,or_assoc]

def touched (P:Program) (q:Wire) : Bool := P.any (instructionTouches q)

theorem touched_spec (P:Program) (q:Wire) : touched P q=true ↔ q∈wires P := by
 induction P with
 | nil => simp [touched,wires]
 | cons i P ih => simpa only [touched,List.any_cons,Bool.or_eq_true,wires,Finset.mem_union,instruction_spec] using (or_congr Iff.rfl ih)

theorem append_left (A B:Program) : wires A⊆wires (A++B) := by
 rw [wires_append]
 exact Finset.subset_union_left

theorem append_right (A B:Program) : wires B⊆wires (A++B) := by
 rw [wires_append]
 exact Finset.subset_union_right

theorem append_union (A B P:Program) (ha:wires A⊆wires P) (hb:wires B⊆wires P) :
 wires (A++B)⊆wires P := by
 rw [wires_append]
 exact Finset.union_subset ha hb

theorem shared35_support : wires ParkAData.shared35⊆wires ParkAData.p0 := by
 change wires ParkAData.shared35⊆wires ((((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))++(((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))
 exact ((((((((show wires ParkAData.shared35⊆wires ParkAData.shared35 from fun _ h=>h)).trans (append_left ParkAData.shared35 ParkAData.shared36)).trans (append_right (ParkAData.shared33++ParkAData.shared34) (ParkAData.shared35++ParkAData.shared36))).trans (append_right (ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32)) ((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))).trans (append_left ((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36))) (((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))).trans (append_left (((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44)))) ((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))).trans (append_right ((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29))))) ((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))).trans (append_left (((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))) (((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))

theorem shared4_support : wires ParkAData.shared4⊆wires ParkAData.p0 := by
 change wires ParkAData.shared4⊆wires ((((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))++(((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))
 exact ((((((((show wires ParkAData.shared4⊆wires ParkAData.shared4 from fun _ h=>h)).trans (append_right ParkAData.shared3 ParkAData.shared4)).trans (append_left (ParkAData.shared3++ParkAData.shared4) (ParkAData.shared5++ParkAData.shared6))).trans (append_right (ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2)) ((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))).trans (append_left ((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6))) (((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))).trans (append_left (((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14)))) (((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))).trans (append_left ((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29))))) ((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))).trans (append_left (((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))) (((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))

theorem shared25_support : wires ParkAData.shared25⊆wires ParkAData.p0 := by
 change wires ParkAData.shared25⊆wires ((((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))++(((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))
 exact ((((((((show wires ParkAData.shared25⊆wires ParkAData.shared25 from fun _ h=>h)).trans (append_right ParkAData.shared24 ParkAData.shared25)).trans (append_right (ParkAData.shared22++ParkAData.shared23) (ParkAData.shared24++ParkAData.shared25))).trans (append_left ((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25)) ((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))).trans (append_right ((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21))) (((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29))))).trans (append_right (((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14)))) (((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))).trans (append_left ((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29))))) ((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))).trans (append_left (((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))) (((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))

theorem shared45_support : wires ParkAData.shared45⊆wires ParkAData.p0 := by
 change wires ParkAData.shared45⊆wires ((((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))++(((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))
 exact ((((((((show wires ParkAData.shared45⊆wires ParkAData.shared45 from fun _ h=>h)).trans (append_left ParkAData.shared45 ParkAData.shared46)).trans (append_left (ParkAData.shared45++ParkAData.shared46) (ParkAData.shared47++ParkAData.shared48))).trans (append_left ((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48)) ((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))).trans (append_left (((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52))) (((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))).trans (append_right (((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44)))) ((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))).trans (append_right ((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29))))) ((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))).trans (append_left (((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))) (((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))

theorem shared38_support : wires ParkAData.shared38⊆wires ParkAData.p0 := by
 change wires ParkAData.shared38⊆wires ((((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))++(((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))
 exact ((((((((show wires ParkAData.shared38⊆wires ParkAData.shared38 from fun _ h=>h)).trans (append_right ParkAData.shared37 ParkAData.shared38)).trans (append_left (ParkAData.shared37++ParkAData.shared38) (ParkAData.shared39++ParkAData.shared40))).trans (append_left ((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40)) ((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44)))).trans (append_right ((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36))) (((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))).trans (append_left (((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44)))) ((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))).trans (append_right ((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29))))) ((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))).trans (append_left (((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))) (((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))

theorem shared106_support : wires ParkAData.shared106⊆wires ParkAData.p0 := by
 change wires ParkAData.shared106⊆wires ((((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))++(((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))
 exact ((((((((show wires ParkAData.shared106⊆wires ParkAData.shared106 from fun _ h=>h)).trans (append_left ParkAData.shared106 ParkAData.shared107)).trans (append_left (ParkAData.shared106++ParkAData.shared107) (ParkAData.shared108++ParkAData.shared109))).trans (append_left ((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109)) ((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))).trans (append_left (((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113))) (((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119))))).trans (append_right (((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105)))) ((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))).trans (append_right ((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90))))) ((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119))))))).trans (append_right (((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))) (((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))

theorem shared33_support : wires ParkAData.shared33⊆wires ParkAData.p0 := by
 change wires ParkAData.shared33⊆wires ((((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))++(((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))
 exact ((((((((show wires ParkAData.shared33⊆wires ParkAData.shared33 from fun _ h=>h)).trans (append_left ParkAData.shared33 ParkAData.shared34)).trans (append_left (ParkAData.shared33++ParkAData.shared34) (ParkAData.shared35++ParkAData.shared36))).trans (append_right (ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32)) ((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))).trans (append_left ((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36))) (((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))).trans (append_left (((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44)))) ((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))).trans (append_right ((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29))))) ((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))).trans (append_left (((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))) (((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))

theorem shared5_support : wires ParkAData.shared5⊆wires ParkAData.p0 := by
 change wires ParkAData.shared5⊆wires ((((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))++(((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))
 exact ((((((((show wires ParkAData.shared5⊆wires ParkAData.shared5 from fun _ h=>h)).trans (append_left ParkAData.shared5 ParkAData.shared6)).trans (append_right (ParkAData.shared3++ParkAData.shared4) (ParkAData.shared5++ParkAData.shared6))).trans (append_right (ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2)) ((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))).trans (append_left ((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6))) (((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))).trans (append_left (((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14)))) (((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))).trans (append_left ((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29))))) ((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))).trans (append_left (((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))) (((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))

theorem shared0_support : wires ParkAData.shared0⊆wires ParkAData.p0 := by
 change wires ParkAData.shared0⊆wires ((((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))++(((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))
 exact (((((((show wires ParkAData.shared0⊆wires ParkAData.shared0 from fun _ h=>h)).trans (append_left ParkAData.shared0 (ParkAData.shared1++ParkAData.shared2))).trans (append_left (ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2)) ((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))).trans (append_left ((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6))) (((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))).trans (append_left (((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14)))) (((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))).trans (append_left ((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29))))) ((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))).trans (append_left (((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))) (((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))

theorem shared22_support : wires ParkAData.shared22⊆wires ParkAData.p0 := by
 change wires ParkAData.shared22⊆wires ((((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))++(((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))
 exact ((((((((show wires ParkAData.shared22⊆wires ParkAData.shared22 from fun _ h=>h)).trans (append_left ParkAData.shared22 ParkAData.shared23)).trans (append_left (ParkAData.shared22++ParkAData.shared23) (ParkAData.shared24++ParkAData.shared25))).trans (append_left ((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25)) ((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))).trans (append_right ((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21))) (((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29))))).trans (append_right (((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14)))) (((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))).trans (append_left ((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29))))) ((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60))))))).trans (append_left (((((ParkAData.shared0++(ParkAData.shared1++ParkAData.shared2))++((ParkAData.shared3++ParkAData.shared4)++(ParkAData.shared5++ParkAData.shared6)))++(((ParkAData.shared7++ParkAData.shared8)++(ParkAData.shared9++ParkAData.shared10))++((ParkAData.shared11++ParkAData.shared12)++(ParkAData.shared13++ParkAData.shared14))))++(((ParkAData.shared15++(ParkAData.shared16++ParkAData.shared17))++((ParkAData.shared18++ParkAData.shared19)++(ParkAData.shared20++ParkAData.shared21)))++(((ParkAData.shared22++ParkAData.shared23)++(ParkAData.shared24++ParkAData.shared25))++((ParkAData.shared26++ParkAData.shared27)++(ParkAData.shared28++ParkAData.shared29)))))++((((ParkAData.shared30++(ParkAData.shared31++ParkAData.shared32))++((ParkAData.shared33++ParkAData.shared34)++(ParkAData.shared35++ParkAData.shared36)))++(((ParkAData.shared37++ParkAData.shared38)++(ParkAData.shared39++ParkAData.shared40))++((ParkAData.shared41++ParkAData.shared42)++(ParkAData.shared43++ParkAData.shared44))))++((((ParkAData.shared45++ParkAData.shared46)++(ParkAData.shared47++ParkAData.shared48))++((ParkAData.shared49++ParkAData.shared50)++(ParkAData.shared51++ParkAData.shared52)))++(((ParkAData.shared53++ParkAData.shared54)++(ParkAData.shared55++ParkAData.shared56))++((ParkAData.shared57++ParkAData.shared58)++(ParkAData.shared59++ParkAData.shared60)))))) (((((ParkAData.shared61++(ParkAData.shared62++ParkAData.shared63))++((ParkAData.shared64++ParkAData.shared65)++(ParkAData.shared66++ParkAData.shared67)))++(((ParkAData.shared68++ParkAData.shared69)++(ParkAData.shared70++ParkAData.shared71))++((ParkAData.shared72++ParkAData.shared73)++(ParkAData.shared74++ParkAData.shared75))))++(((ParkAData.shared76++(ParkAData.shared77++ParkAData.shared78))++((ParkAData.shared79++ParkAData.shared80)++(ParkAData.shared81++ParkAData.shared82)))++(((ParkAData.shared83++ParkAData.shared84)++(ParkAData.shared85++ParkAData.shared86))++((ParkAData.shared87++ParkAData.shared88)++(ParkAData.shared89++ParkAData.shared90)))))++((((ParkAData.shared91++(ParkAData.shared92++ParkAData.shared93))++((ParkAData.shared94++ParkAData.shared95)++(ParkAData.shared96++ParkAData.shared97)))++(((ParkAData.shared98++ParkAData.shared99)++(ParkAData.shared100++ParkAData.shared101))++((ParkAData.shared102++ParkAData.shared103)++(ParkAData.shared104++ParkAData.shared105))))++((((ParkAData.shared106++ParkAData.shared107)++(ParkAData.shared108++ParkAData.shared109))++((ParkAData.shared110++ParkAData.shared111)++(ParkAData.shared112++ParkAData.shared113)))++(((ParkAData.shared114++ParkAData.shared115)++(ParkAData.shared116++ParkAData.shared117))++((ParkAData.shared118++ParkAData.shared1)++(ParkAData.shared2++ParkAData.shared119)))))))

def witnessProgram : Program := (((ParkAData.shared35++ParkAData.shared4)++(ParkAData.shared25++(ParkAData.shared45++ParkAData.shared38)))++((ParkAData.shared106++ParkAData.shared33)++(ParkAData.shared5++(ParkAData.shared0++ParkAData.shared22))))

theorem witness_support : wires witnessProgram⊆wires ParkAData.p0 :=
 (append_union ((ParkAData.shared35++ParkAData.shared4)++(ParkAData.shared25++(ParkAData.shared45++ParkAData.shared38))) ((ParkAData.shared106++ParkAData.shared33)++(ParkAData.shared5++(ParkAData.shared0++ParkAData.shared22))) ParkAData.p0 (append_union (ParkAData.shared35++ParkAData.shared4) (ParkAData.shared25++(ParkAData.shared45++ParkAData.shared38)) ParkAData.p0 (append_union ParkAData.shared35 ParkAData.shared4 ParkAData.p0 shared35_support shared4_support) (append_union ParkAData.shared25 (ParkAData.shared45++ParkAData.shared38) ParkAData.p0 shared25_support (append_union ParkAData.shared45 ParkAData.shared38 ParkAData.p0 shared45_support shared38_support))) (append_union (ParkAData.shared106++ParkAData.shared33) (ParkAData.shared5++(ParkAData.shared0++ParkAData.shared22)) ParkAData.p0 (append_union ParkAData.shared106 ParkAData.shared33 ParkAData.p0 shared106_support shared33_support) (append_union ParkAData.shared5 (ParkAData.shared0++ParkAData.shared22) ParkAData.p0 shared5_support (append_union ParkAData.shared0 ParkAData.shared22 ParkAData.p0 shared0_support shared22_support))))

def cover (u:Wire) : Bool := u==d || (FullPadSupport.supportDomain L).contains u || touched witnessProgram u
theorem used0 : (((A161GenericFold.ambient L g hs96).drop 0).take 80).all cover=true := by decide +kernel
theorem used1 : (((A161GenericFold.ambient L g hs96).drop 80).take 80).all cover=true := by decide +kernel
theorem used2 : (((A161GenericFold.ambient L g hs96).drop 160).take 80).all cover=true := by decide +kernel
theorem used3 : (((A161GenericFold.ambient L g hs96).drop 240).take 80).all cover=true := by decide +kernel
theorem used4 : (((A161GenericFold.ambient L g hs96).drop 320).take 80).all cover=true := by decide +kernel
theorem used5 : (((A161GenericFold.ambient L g hs96).drop 400).take 80).all cover=true := by decide +kernel
theorem used6 : (((A161GenericFold.ambient L g hs96).drop 480).take 80).all cover=true := by decide +kernel
theorem used7 : (((A161GenericFold.ambient L g hs96).drop 560).take 80).all cover=true := by decide +kernel
theorem used8 : (((A161GenericFold.ambient L g hs96).drop 640).take 80).all cover=true := by decide +kernel
theorem used9 : (((A161GenericFold.ambient L g hs96).drop 720).take 80).all cover=true := by decide +kernel
theorem used10 : (((A161GenericFold.ambient L g hs96).drop 800).take 80).all cover=true := by decide +kernel
theorem used11 : (((A161GenericFold.ambient L g hs96).drop 880).take 80).all cover=true := by decide +kernel
theorem used12 : (((A161GenericFold.ambient L g hs96).drop 960).take 80).all cover=true := by decide +kernel
theorem used13 : (((A161GenericFold.ambient L g hs96).drop 1040).take 80).all cover=true := by decide +kernel
theorem used14 : (((A161GenericFold.ambient L g hs96).drop 1120).take 80).all cover=true := by decide +kernel
theorem used15 : (((A161GenericFold.ambient L g hs96).drop 1200).take 80).all cover=true := by decide +kernel
theorem used16 : (((A161GenericFold.ambient L g hs96).drop 1280).take 80).all cover=true := by decide +kernel
theorem partition : A161GenericFold.ambient L g hs96 = (((A161GenericFold.ambient L g hs96).drop 0).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 80).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 160).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 240).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 320).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 400).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 480).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 560).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 640).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 720).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 800).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 880).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 960).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 1040).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 1120).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 1200).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 1280).take 80) := by decide +kernel
theorem all_cover : (A161GenericFold.ambient L g hs96).all cover=true := by
 rw [partition]
 simp only [List.all_append,used0,used1,used2,used3,used4,used5,used6,used7,used8,used9,used10,used11,used12,used13,used14,used15,used16,Bool.true_and]
#print axioms witness_support
#print axioms all_cover
end ECDSAAdd.Entrant.A161SupportCover

section
namespace ECDSAAdd.Entrant.A161FineSupport
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 FourthASavedCarryDevelop A161FixedFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run List.toFinset

theorem middle_in_body (L:CuccaroStreamedSquareWideLayout) (g:Wire) :
 wires (aMiddle L g)⊆wires (aBodyTriple L g) := by
 intro u hu
 simp only [aBodyTriple,aFoldTriple,wires_append,Finset.mem_union]
 exact Or.inr (Or.inr (Or.inl (Or.inr hu)))

theorem ambient_fine : (A161GenericFold.ambient L g hs96).toFinset⊆insert d (wires (aBodyTriple L g)) := by
 intro u hu
 have hh := List.all_eq_true.mp A161SupportCover.all_cover u (List.mem_toFinset.mp hu)
 simp only [A161SupportCover.cover,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at hh
 rcases hh with (hd|hdomain)|hmid
 · exact Finset.mem_insert.mpr (Or.inl hd)
 · exact Finset.mem_insert_of_mem ((hasWire_iff _ _).mp (FullPadSupport.actual_support_ready u hdomain))
 · have hm : u∈wires ParkAData.p0 := A161SupportCover.witness_support ((A161SupportCover.touched_spec _ _).mp hmid)
   have e := congrArg ECDSAAdd.wires ParkAStagedProof.input_eq
   have hn : u∈wires (aMiddle L g) := e ▸ hm
   exact Finset.mem_insert_of_mem (middle_in_body L g hn)

theorem fold_fine : wires fold96⊆insert d (wires (aBodyTriple L g)) :=
 (A161GenericFold.support L hw hn g hs96 checked.out cert96).trans ambient_fine

theorem body_fine : wires body⊆insert d (wires (aBodyTriple L g)) := by
 intro u hu
 simp only [body,wires_append,Finset.mem_union] at hu
 rcases hu with hu|(hu|hu)
 · apply Finset.mem_insert_of_mem
   simp only [aBodyTriple,wires_append,Finset.mem_union]
   exact Or.inl hu
 · apply Finset.mem_insert_of_mem
   simp only [aBodyTriple,wires_append,Finset.mem_union]
   exact Or.inr (Or.inl hu)
 · exact fold_fine hu
#print axioms ambient_fine
#print axioms body_fine
end ECDSAAdd.Entrant.A161FineSupport
end

section
namespace ECDSAAdd.Entrant.A161Low4Fine
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ControlLoan1589BFFold
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run List.toFinset

theorem ambient_subset (L:CuccaroStreamedSquareWideLayout) (g d:Wire) (hs:List Wire) :
 (A161Low4GenericFold.ambient L g ((hs++L.core.work.take 4)++[d])).toFinset⊆
 (A161GenericFold.ambient L g (hs++[d])).toFinset := by
 intro u hu
 have low:∀u∈L.core.work.take 4,u∈A161GenericFold.domain L := by
  intro u hu
  have sub:(L.core.work.take 4).Sublist (A161Fold.accReg L) := by
   have h:=List.take_sublist 4 (L.core.work.take 161)
   simpa only [A161Fold.accReg,List.take_take,show min 4 161=4 by decide] using h
  have acc:=sub.subset hu
  simp only [A161GenericFold.domain,List.mem_cons,List.mem_append]
  tauto
 simp only [A161Low4GenericFold.ambient,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hu
 simp only [A161GenericFold.ambient,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
 rcases hu with h|h|h|h|((h|h)|h)
 · tauto
 · tauto
 · tauto
 · tauto
 · tauto
 · tauto
 · have hLow:u∈L.core.work.take 4→u∈A161GenericFold.domain L:=low u
   tauto

open A161Low4FixedFold

theorem ambient_fine : (A161Low4GenericFold.ambient L g hs100).toFinset⊆insert d (wires (aBodyTriple L g)) :=
 (ambient_subset L g d (A161Facts.loans95 L)).trans A161FineSupport.ambient_fine

theorem fold_fine : wires fold100⊆insert d (wires (aBodyTriple L g)) :=
 (A161Low4GenericFold.support L hw hn g hs100 checked.out cert100).trans ambient_fine

theorem body_fine : wires body⊆insert d (wires (aBodyTriple L g)) := by
 intro u hu
 simp only [A161Low4FixedFold.body,wires_append,Finset.mem_union] at hu
 rcases hu with hu|(hu|hu)
 · apply Finset.mem_insert_of_mem
   simp only [aBodyTriple,wires_append,Finset.mem_union]
   exact Or.inl hu
 · apply Finset.mem_insert_of_mem
   simp only [aBodyTriple,wires_append,Finset.mem_union]
   exact Or.inr (Or.inl hu)
 · exact fold_fine hu
#print axioms ambient_fine
#print axioms body_fine
end ECDSAAdd.Entrant.A161Low4Fine

end
