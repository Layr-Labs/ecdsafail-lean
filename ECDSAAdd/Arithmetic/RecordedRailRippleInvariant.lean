import ECDSAAdd.Arithmetic.RecordedRailRippleTerminalProof
import ECDSAAdd.Arithmetic.RippleAdder

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailRipple

/-- Arithmetic carry as computed by the literal dressed-control CCX. -/
def carryFn (a b incoming : Bool) : Bool := ((a ^^ incoming) && (b ^^ incoming)) ^^ incoming

def recordDebt (slot : Option Nat) (m : List Bool) (carry : Bool) : Bool :=
  match slot with
  | none => false
  | some j => m.getD j false && carry

/-- Saved old-record debt evaluated on the original unsigned inputs. The higher
carry-in is the newly computed Boolean, not a still-zero work-wire lookup. -/
def phaseDebt : List Wire → List Wire → Bool → List (Option Nat) → BasisState → List Bool → Bool
  | a0::a1::a2::as, b0::b1::b2::bs, incoming, d::ds, bits, m =>
      let c := carryFn (bits a0) (bits b0) incoming
      recordDebt d m c ^^ phaseDebt (a1::a2::as) (b1::b2::bs) c ds bits m
  | _, _, _, _, _, _ => false

def incomingValue (prev : Option Wire) (bits : BasisState) : Bool :=
  match prev with
  | none => false
  | some p => bits p

/-- Pure Boolean identity connects the source's literal carry to ordinary
unsigned arithmetic. It is not an assumption about circuit execution. -/
theorem carryFn_eq (a b c : Bool) : carryFn a b c=carryBit a b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem carryValue_eq (a b : Wire) (prev : Option Wire) (bits : BasisState) :
    RecordedRailCarry.carryValue a b prev bits=carryFn (bits a) (bits b) (incomingValue prev bits) := by
  cases prev <;> simp [RecordedRailCarry.carryValue,carryFn,incomingValue]

theorem debt_split (a0 a1 a2 b0 b1 b2 : Wire) (as bs : List Wire) (incoming : Bool)
    (d : Option Nat) (ds : List (Option Nat)) (bits : BasisState) (m : List Bool) :
    phaseDebt (a0::a1::a2::as) (b0::b1::b2::bs) incoming (d::ds) bits m=
      (recordDebt d m (carryFn (bits a0) (bits b0) incoming) ^^
      phaseDebt (a1::a2::as) (b1::b2::bs) (carryFn (bits a0) (bits b0) incoming) ds bits m) := rfl

/-- The low-bit arithmetic equation needed after the higher recursive contract. -/
theorem unsigned_step (a b c : Bool) (X Y n : Nat) :
    ((b ^^ a) ^^ c).toNat + 2*((X+Y+(carryFn a b c).toNat)%2^n)=
      ((a.toNat+2*X)+(b.toNat+2*Y)+c.toNat)%2^(n+1) := by
  have low : ((b ^^ a) ^^ c)=sumBit a b c := by cases a <;> cases b <;> cases c <;> rfl
  rw [low,carryFn_eq]
  exact sum_value_step a b c X Y n

/-- Exact layout and causality preconditions for the forthcoming list induction.
All saved ordinals precede this ripple; no carry lookup or phase result is assumed. -/
def Aligned (a b work : List Wire) (slots : List (Option Nat)) : Prop :=
  0<a.length ∧ b.length=a.length ∧ work.length=a.length-2 ∧ slots.length=work.length

def Ready (a b : List Wire) (prev : Option Wire) (work : List Wire)
    (slots : List (Option Nat)) (bits : BasisState) (cursor : Nat) : Prop :=
  Aligned a b work slots ∧ (prev.toList++a++b++work).Nodup ∧
    (∀q∈work,bits q=false) ∧ (∀j∈slots.filterMap id,j<cursor)

/-- The recursive postcondition preserves every spectator, including all source
and work wires. This is a definition of the proof target, not a semantic oracle. -/
def UnsignedResult (a b work : List Wire) (prev : Option Wire)
    (bits : BasisState) (phase : Bool) (out : State) : Prop :=
  out.phase=phase ∧
    regValue a out.basis=regValue a bits ∧
    regValue b out.basis=(regValue a bits+regValue b bits+(incomingValue prev bits).toNat)%2^b.length ∧
    (∀q,q∉b → out.basis q=bits q) ∧ (∀q∈work,out.basis q=false)

/-- Reviewable full induction goal. No theorem claims it yet: the missing step
must combine actual carryStep, the higher ripple frame, and actual retire/unwind. -/
def UnsignedContract (a b : List Wire) (prev : Option Wire) (work : List Wire)
    (slots : List (Option Nat)) : Prop :=
  ∀(bits : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat),
    Ready a b prev work slots bits cursor →
    UnsignedResult a b work prev bits phase
      (runWithTape (ripple a b prev work slots) m cursor
        ⟨phase ^^ phaseDebt a b (incomingValue prev bits) slots bits m,bits⟩)

end ECDSAAdd.Arithmetic.RecordedRailRipple
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.carryFn_eq
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.unsigned_step
