import ECDSAAdd.Framework.Hoare
import ECDSAAdd.Math.BitcoinPrimes

/-! Protected challenge contract. Signed basis states and fixed measurement
records only; this is not a quantum-channel or hardware claim. -/
namespace ECDSAAdd.Challenge
open Secp256k1

/-- Public classical construction parameter; no secret-input restriction on C. -/
abbrev Entry := Point → Program

def control : Wire := 0

def point : PointReg :=
  ⟨1, (List.range 256).map (· + 2), (List.range 256).map (· + 258)⟩

/-- Control plus the canonical 513-bit point representation. -/
def ioWires : Finset Wire := Finset.range 514

def clean (st : BasisState) : Prop := ∀ w, 514 ≤ w → st w = false

def encodes (b : Bool) (R : Point) (st : BasisState) : Prop :=
  st control = b ∧ Holds.holds st point R ∧ clean st

/-- Includes idle I/O wires. This is static distinct wires, not peak-live. -/
def qubits (p : Program) : Nat := (ioWires ∪ wires p).card

def correctionValid : Correction → Prop
  | .Z _ => True
  | .CZ a b => a ≠ b

def instructionValid : Instr → Prop
  | .X _ => True
  | .CX c t => c ≠ t
  | .CCX a b t => a ≠ b ∧ a ≠ t ∧ b ≠ t
  | .measureX _ c₀ c₁ =>
      (∀ c ∈ c₀, correctionValid c) ∧ (∀ c ∈ c₁, correctionValid c)

/-- Static syntax slots count the measurement itself and BOTH correction lists,
including the branch not taken on a particular record. -/
def instructionSlots : Instr → Nat
  | .measureX _ c₀ c₁ => 1 + c₀.length + c₁.length
  | _ => 1

def gateSlots (p : Program) : Nat := (p.map instructionSlots).sum

/-- Uniform upper bounds over all classical addends, including infinity. -/
structure Bounds where
  toffoli : Nat
  measurements : Nat
  qubits : Nat
  gateSlots : Nat

/-- Every non-I/O bit is zero before and after, and Triple restores phase.
The entrant cannot replace the encoding, layout, semantic model or counters. -/
structure Certificate (entry : Entry) (bounds : Bounds) : Prop where
  correct : ∀ C b R, Triple (encodes b R) (entry C)
    (encodes b (if b then R + C else R))
  physical : ∀ C i, i ∈ entry C → instructionValid i
  toffoli_le : ∀ C, toffoliCount (entry C) ≤ bounds.toffoli
  measurements_le : ∀ C, measurementCount (entry C) ≤ bounds.measurements
  qubits_le : ∀ C, qubits (entry C) ≤ bounds.qubits
  gateSlots_le : ∀ C, gateSlots (entry C) ≤ bounds.gateSlots

/-- Organizer thresholds remain explicit; choosing numeric values is policy. -/
def Within (bounds limits : Bounds) : Prop :=
  bounds.toffoli ≤ limits.toffoli ∧ bounds.measurements ≤ limits.measurements ∧
  bounds.qubits ≤ limits.qubits ∧ bounds.gateSlots ≤ limits.gateSlots

theorem qubits_ge_io (p : Program) : 514 ≤ qubits p := by
  have h := Finset.card_le_card (Finset.subset_union_left : ioWires ⊆ ioWires ∪ wires p)
  simpa [ioWires, qubits] using h

@[simp] theorem qubits_empty : qubits [] = 514 := by
  simp [qubits, ioWires, wires]

@[simp] theorem gateSlots_append (p q : Program) :
    gateSlots (p ++ q) = gateSlots p + gateSlots q := by
  simp [gateSlots]

theorem Certificate.phase_restored {entry bounds} (h : Certificate entry bounds)
    (C : Point) (b : Bool) (R : Point) (s : State) (m : List Bool)
    (hs : encodes b R s.basis) : (run (entry C) m s).phase = s.phase :=
  (h.correct C b R s m hs).1

theorem Certificate.all_work_clean {entry bounds} (h : Certificate entry bounds)
    (C : Point) (b : Bool) (R : Point) (s : State) (m : List Bool)
    (hs : encodes b R s.basis) : clean (run (entry C) m s).basis :=
  (h.correct C b R s m hs).2.2.2

end ECDSAAdd.Challenge
