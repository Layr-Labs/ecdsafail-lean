import ECDSAAdd.Arithmetic.RecordedRailDeferEight
import ECDSAAdd.Arithmetic.RecordedRailMirrorDebt

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply

/-- Saved Defer outcomes stay at their absolute tape ordinals. The seven
boundary carry positions are 31,63,95,127,159,191,223; all other slots are None. -/
def oldSlots (cursor : Nat) : List (Option Nat) :=
  List.replicate 31 none ++ [some (cursor+62)] ++
  List.replicate 31 none ++ [some (cursor+94)] ++
  List.replicate 31 none ++ [some (cursor+126)] ++
  List.replicate 31 none ++ [some (cursor+158)] ++
  List.replicate 31 none ++ [some (cursor+190)] ++
  List.replicate 31 none ++ [some (cursor+222)] ++
  List.replicate 31 none ++ [some (cursor+253)] ++ List.replicate 30 none

/-- Actual bitwise X complement, normal wrapped mirror with saved old Z
corrections and independent fresh MX, then bitwise X complement back. -/
def program (a b mirrorBank : List Wire) (cin : Wire) (oldCursor : Nat) : RecordedProgram :=
  embedRecorded (notRegister b) ++
  RecordedRailRipple.ripple a b (some cin) mirrorBank (oldSlots oldCursor) ++
  embedRecorded (notRegister b)

def pair (a b forwardBank mirrorBank : List Wire) (cin even odd : Wire)
    (oldCursor : Nat) : RecordedProgram :=
  RecordedRailDefer.forward32 a b forwardBank cin even odd ++ program a b mirrorBank cin oldCursor

/-- Real private sites may be reused by Apply: its 254-site bank contains the
31-site forward bank and both alternating boundary sites. No new qubit enters. -/
def Layout (a b forwardBank mirrorBank : List Wire) (cin even odd : Wire) : Prop :=
  a.length=256 ∧ b.length=256 ∧ forwardBank.length=31 ∧ mirrorBank.length=254 ∧
    ([cin]++a++b++mirrorBank).Nodup ∧ (forwardBank++[even,odd]).Nodup ∧
    (∀q∈forwardBank++[even,odd],q∈mirrorBank)

def Ready (a b forwardBank mirrorBank : List Wire) (cin even odd : Wire)
    (bits : BasisState) : Prop :=
  Layout a b forwardBank mirrorBank cin even odd ∧ (∀q∈mirrorBank,bits q=false)

end ECDSAAdd.Arithmetic.RecordedRailApply
