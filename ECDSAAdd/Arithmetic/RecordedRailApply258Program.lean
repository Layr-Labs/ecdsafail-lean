import ECDSAAdd.Arithmetic.RecordedRailApplyProof

namespace ECDSAAdd.Arithmetic.RecordedRailApply258
open RecordedRailDefer

/-- Seven real 32-bit vented words; the final wrapped word has 34 bits and
uses all 32 shared carry-bank sites. The two additional data bits are kept. -/
def forward (a b bank : List Wire) (cin even odd : Wire) : RecordedProgram :=
  segment a b (bank.take 31) cin even odd 0 ++
  segment a b (bank.take 31) cin even odd 1 ++
  segment a b (bank.take 31) cin even odd 2 ++
  segment a b (bank.take 31) cin even odd 3 ++
  segment a b (bank.take 31) cin even odd 4 ++
  segment a b (bank.take 31) cin even odd 5 ++
  segment a b (bank.take 31) cin even odd 6 ++
  finish (a.drop 224) (b.drop 224) bank even

def oldSlots (cursor : Nat) : List (Option Nat) :=
  List.replicate 31 none ++ [some (cursor+62)] ++
  List.replicate 31 none ++ [some (cursor+94)] ++
  List.replicate 31 none ++ [some (cursor+126)] ++
  List.replicate 31 none ++ [some (cursor+158)] ++
  List.replicate 31 none ++ [some (cursor+190)] ++
  List.replicate 31 none ++ [some (cursor+222)] ++
  List.replicate 31 none ++ [some (cursor+255)] ++ List.replicate 32 none

def ordinals : List Nat := [62,94,126,158,190,222,255]
def debt (a b : List Wire) (cin : Wire) (bits : BasisState) (m : List Bool) (cursor : Nat) : Bool :=
  ((ordinals.zip positions).map (fun pair =>
    m.getD (cursor+pair.1) false && prefixCarry a b cin bits (pair.2+1))).foldr Bool.xor false

def applyProgram (a b mirrorBank : List Wire) (cin : Wire) (cursor : Nat) : RecordedProgram :=
  embedRecorded (notRegister b) ++ RecordedRailRipple.ripple a b (some cin) mirrorBank (oldSlots cursor) ++
    embedRecorded (notRegister b)

def pair (a b bank mirrorBank : List Wire) (cin even odd : Wire) (cursor : Nat) : RecordedProgram :=
  forward a b bank cin even odd ++ applyProgram a b mirrorBank cin cursor

def Ready (a b bank : List Wire) (cin even odd : Wire) (bits : BasisState) : Prop :=
  a.length=258 ∧ b.length=258 ∧ bank.length=32 ∧
    ([cin]++a++b++bank++[even,odd]).Nodup ∧
    (∀q∈bank,bits q=false) ∧ bits even=false ∧ bits odd=false

/-- Proof target for the actual 258-bit forward stream; no execution oracle. -/
def ForwardContract (a b bank : List Wire) (cin even odd : Wire) : Prop :=
  ∀(bits : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat),
    Ready a b bank cin even odd bits →
    let out := runWithTape (forward a b bank cin even odd) m cursor ⟨phase,bits⟩
    out.phase=(phase ^^ debt a b cin bits m cursor) ∧
    regValue b out.basis=(regValue a bits+regValue b bits+(bits cin).toNat)%2^258 ∧
    (∀q,q∉b → out.basis q=bits q) ∧
    (∀q∈bank,out.basis q=false) ∧ out.basis even=false ∧ out.basis odd=false

end ECDSAAdd.Arithmetic.RecordedRailApply258
