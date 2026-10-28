import ECDSAAdd.Arithmetic.RecordedRailVentedSpec
import ECDSAAdd.Arithmetic.RecordedRailRippleCertificate

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailDefer

/-- Source Defer stores the previous boundary's MX after the next chunk has
used that boundary as its incoming carry. No immediate correction is emitted. -/
def bareMX (q : Wire) : RecordedProgram := [.gate (.measureX q [] [])]

def advance (a b bank : List Wire) (incoming cout : Wire) : RecordedProgram :=
  RecordedRailVented.vented a b (some incoming) bank cout ++ bareMX incoming

def two (a0 b0 a1 b1 bank : List Wire) (cin q0 q1 : Wire) : RecordedProgram :=
  RecordedRailVented.vented a0 b0 (some cin) bank q0 ++ advance a1 b1 bank q0 q1

def finish (a b bank : List Wire) (incoming : Wire) : RecordedProgram :=
  RecordedRailRipple.ripple a b (some incoming) (bank.take (a.length-2))
    (List.replicate (a.length-2) none) ++ bareMX incoming

def chunk (r : List Wire) (j : Nat) : List Wire := (r.drop (32*j)).take 32

def boundary (even odd : Wire) (j : Nat) : Wire := if j%2=0 then even else odd

def segment (a b bank : List Wire) (cin even odd : Wire) (j : Nat) : RecordedProgram :=
  if j=0 then RecordedRailVented.vented (chunk a j) (chunk b j) (some cin) bank even
  else if j=7 then finish (chunk a j) (chunk b j) bank even
  else advance (chunk a j) (chunk b j) bank (boundary even odd (j-1)) (boundary even odd j)

/-- Literal eight-chunk order. Both alternating boundary sites are physical
operands, and only the first thirty bank sites enter the final wrapped chunk. -/
def forward32 (a b bank : List Wire) (cin even odd : Wire) : RecordedProgram :=
  segment a b bank cin even odd 0 ++ segment a b bank cin even odd 1 ++
  segment a b bank cin even odd 2 ++ segment a b bank cin even odd 3 ++
  segment a b bank cin even odd 4 ++ segment a b bank cin even odd 5 ++
  segment a b bank cin even odd 6 ++ segment a b bank cin even odd 7

def ordinals : List Nat := [62,94,126,158,190,222,253]
def positions : List Nat := [31,63,95,127,159,191,223]

/-- Ordinary original-prefix carry, written as an overflow predicate. -/
def prefixCarry (a b : List Wire) (cin : Wire) (bits : BasisState) (n : Nat) : Bool :=
  decide (2^n ≤ regValue (a.take n) bits+regValue (b.take n) bits+(bits cin).toNat)

def debt32 (a b : List Wire) (cin : Wire) (bits : BasisState) (m : List Bool) (cursor : Nat) : Bool :=
  ((ordinals.zip positions).map (fun pair =>
    m.getD (cursor+pair.1) false && prefixCarry a b cin bits (pair.2+1))).foldr Bool.xor false

def Ready32 (a b bank : List Wire) (cin even odd : Wire) (bits : BasisState) : Prop :=
  a.length=256 ∧ b.length=256 ∧ bank.length=31 ∧
    ([cin]++a++b++bank++[even,odd]).Nodup ∧
    (∀q∈bank,bits q=false) ∧ bits even=false ∧ bits odd=false

/-- Full eight-chunk proof target. This declaration supplies no execution fact. -/
def Contract32 (a b bank : List Wire) (cin even odd : Wire) : Prop :=
  ∀(bits : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat),
    Ready32 a b bank cin even odd bits →
    let out := runWithTape (forward32 a b bank cin even odd) m cursor ⟨phase,bits⟩
    out.phase=(phase ^^ debt32 a b cin bits m cursor) ∧
    regValue b out.basis=(regValue a bits+regValue b bits+(bits cin).toNat)%2^256 ∧
    (∀q,q∉b → out.basis q=bits q) ∧
    (∀q∈bank,out.basis q=false) ∧ out.basis even=false ∧ out.basis odd=false

theorem bare_counts (q : Wire) :
    recordedToffoliCount (bareMX q)=0 ∧ recordedMeasurementCount (bareMX q)=1 := by
  simp [bareMX,recordedToffoliCount,recordedMeasurementCount,toffoliCount,measurementCount]

theorem advance_counts (a b bank : List Wire) (shape : RecordedRailVented.Shape a b bank)
    (incoming cout : Wire) :
    recordedToffoliCount (advance a b bank incoming cout)=a.length ∧
    recordedMeasurementCount (advance a b bank incoming cout)=a.length := by
  have h := RecordedRailVented.counts a b bank shape (some incoming) cout
  have positive := (RecordedRailVented.shape_lengths a b bank shape).1
  simp only [advance,recordedToffoliCount_append,recordedMeasurementCount_append,
    (bare_counts incoming).1,(bare_counts incoming).2,h.1,h.2,Nat.add_zero]
  constructor
  · trivial
  · omega

end ECDSAAdd.Arithmetic.RecordedRailDefer
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.advance_counts
