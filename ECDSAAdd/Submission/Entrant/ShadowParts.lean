import ECDSAAdd.Submission.Entrant.ShadowGates
import ECDSAAdd.Submission.Entrant.Window

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket GateMirror Partial LeaveSelector


def forward (j : Fin 23) := IntegerPacket.seq (Shadow7.shape j) 0 15

def reverse (j : Fin 23) := IntegerPacket.back (Shadow7.shape j) 0 15

def onRails (j:Fin 23) (i:Nat) (z:SkywalkRails.State) (b:BasisState) :=
  ready (Shadow7.shape j) i z (mappedBasis j b)

def leaveJoin (s : Nat) : List Gate :=
  digitsG (tagsP.getD · 0) (fun i => Shadow7.a0P s + i) (Shadow7.e0P s + 6) 1613 0 16 ++ wordG 1614 (Shadow7.columnsP s)

def lowSign (s : Nat) : List Gate := [.cx (Shadow7.e0P s + 3) 1560, .cx 1559 1560, .pop (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559]

def lowRest (s : Nat) : List Gate :=
  (List.range (Shadow7.lowsP s)).map (fun i => .ccx 1556 (Shadow7.a0P s + i) (Shadow7.b0P s + i)) ++ xsG ((List.range (Shadow7.lowsP s)).map (Shadow7.b0P s + ·)) ++
  addG ((List.range (Shadow7.lowsP s)).map (Shadow7.b0P s + ·)) ((List.range (Shadow7.lowsP s - 1)).map (1559 + ·)) 1558 ++
  xsG ((List.range (Shadow7.lowsP s)).map (Shadow7.b0P s + ·)) ++
  [.pop (Shadow7.b0P s - 1) 1557 1558, .cx (Shadow7.a0P s - 1) 1557, .x 1557]

def leaveHeadOps (s : Nat) : List Gate :=
  leaveFix0 s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ leaveFix2 s (Shadow7.sbP s) ++ leaveFix3 s (Shadow7.sbP s) ++
  leaveFix4 s (Shadow7.sbP s) ++ leaveFix5 s (Shadow7.sbP s) ++ Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++
  leaveFix8 s (Shadow7.sbP s) ++ Shadow7.leaveJoin s ++ leaveFix10 s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++
  leaveFix12 s (Shadow7.sbP s) ++ Shadow7.lowSign s

def leaveMidOps (s : Nat) : List Gate := Shadow7.lowRest s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s

def leaveOps (s : Nat) : List Gate :=
  leaveFix0 s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ leaveFix2 s (Shadow7.sbP s) ++ leaveFix3 s (Shadow7.sbP s) ++
  leaveFix4 s (Shadow7.sbP s) ++ leaveFix5 s (Shadow7.sbP s) ++ Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++
  leaveFix8 s (Shadow7.sbP s) ++ Shadow7.leaveJoin s ++ leaveFix10 s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++
  leaveFix12 s (Shadow7.sbP s) ++ Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

def cutsP (s : Nat) : List Nat :=
  let w := Shadow7.wpP s; let L := Shadow7.lowsP s; let H := w + 15 - L
  let p0 := 334 + (5*w - 2)
  let p1 := p0 + 16 + 3*w; let p2 := p1 + 16 + 3*(w+1); let p3 := p2 + 16 + 3*(w+3)
  let p4 := p3 + 16 + 3*(w+7)
  let j := p4 + 2; let r := j + (118 - L) + 2; let a := r + 67; let b := a + (6*L + 4)
  let t := b + (4*(w+15) + 19) + (4*L + 19)
  [0, 78, 93, 169, 172, 242, 245, 275, 334,
   p0, p0+8, p0+8+3*w, p1, p1+8, p1+8+3*(w+1), p2, p2+8, p2+8+3*(w+3), p3, p3+8, p3+8+3*(w+7), p4,
   j, j + (118 - L), r, r+37, r+67, a+3, a + (6*L+4) - 3, b, b + (4*H+10), b + (4*H+11), b + (4*(w+15)+19), t, t+21]

def cutP (s k : Nat) : Nat := (Shadow7.cutsP s).getD k 0

def leaveLength (s : Nat) : Nat := Shadow7.cutP s 33 + 21 + 3*(Shadow7.wpP (s+15) + 3)

def leaveP (j : Fin 23) : Program := GateMirror.forward (Shadow7.leaveOps (start j))

def leaveInvP (j : Fin 23) : Program := inverse (Shadow7.leaveOps (start j))

def moveA (s : Nat) : List Gate :=
  leaveFix0 s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ leaveFix2 s (Shadow7.sbP s) ++ leaveFix3 s (Shadow7.sbP s) ++
  leaveFix4 s (Shadow7.sbP s) ++ (leaveFix5 s (Shadow7.sbP s)).take 27

def moveMux (s : Nat) : List Gate := ((leaveFix5 s (Shadow7.sbP s)).drop 27).take 16

def moveB (s : Nat) : List Gate :=
  (leaveFix5 s (Shadow7.sbP s)).drop 43 ++ Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++ leaveFix8 s (Shadow7.sbP s)

def moveDig (s : Nat) : List Gate := digitsG (tagsP.getD · 0) (fun i => Shadow7.a0P s + i) (Shadow7.e0P s + 6) 1613 0 16

def moveKept (s : Nat) : List Gate := keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s + i) 1613 0 16

def moveC (s : Nat) : List Gate :=
  wordG 1614 (Shadow7.columnsP s) ++ leaveFix10 s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++
  leaveFix12 s (Shadow7.sbP s) ++ Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

def body (j:Fin 23) (admin:Program) := Shadow7.routed j 0 1 ++ (admin ++ Shadow7.routed j 1 14)

def unbody (j:Fin 23) (reverse:Program) := Shadow7.unrouted j 1 14 ++ (reverse ++ Shadow7.unrouted j 0 1)

def physicalCells (j:Fin 23) (s:State) := readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis)

def leaveBox2 (s q : Nat) : Prop :=
  ((s+15 ≤ q ∧ q ≤ min (s + 30 + railP (s+14)) 529) ∨ (786 ≤ q ∧ q ≤ 785 + railP s) ∨ (1556 ≤ q ∧ q ≤ min 1812 (2069 - s)) ∨ (1044+s ≤ q ∧ q < 1059+s)) ∧
  ¬ (s+31 ≤ q ∧ q < Shadow7.a0P s - 1) ∧ ¬ (786 ≤ q ∧ q < Shadow7.b0P s - 1) ∧ ¬ (Shadow7.a0P s + 18 ≤ q ∧ q ≤ 785) ∧ q ≠ s + 15 ∧
  ¬ (1301 ≤ q ∧ q ≤ 1058 + s) ∧ ¬ (2070 ≤ q + s ∧ q ≤ 1812)

def farOps (j : Fin 23) : List Op := (1559 :: (List.range 5).map (1561 + ·)).map (fun a => .xor a (Shadow7.e0P (start j) + 7))

def crossOps (j : Fin 23) : List Op :=
  (List.range 16).map (fun i => .mix (tagsP.getD i 0) (Shadow7.a0P (start j) + i) (Shadow7.e0P (start j) + 6))

def productOps (j : Fin 23) : List Op := [.save (Shadow7.e0P (start j) + 6) 1596 1597]

/-- A record reads only the low bit and the history wire, both fixed by the start tick. -/
theorem readCells_eq (j : Fin 23) (i n : Nat) (s : BasisState) :
    readCells (Shadow7.shape j) i n s = readCells (StairPacket.shape j) i n s := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    change cell (Shadow7.shape j) i s :: _ = cell (StairPacket.shape j) i s :: _
    exact congrArg₂ List.cons rfl (ih (i+1))

theorem physicalCells_eq (j : Fin 23) (s : State) :
    Shadow7.physicalCells j s = StairPacket.physicalCells j s :=
  Shadow7.readCells_eq j 0 15 (mappedBasis j s.basis)

theorem native_raw_read (j : Fin 23) (s : State) (q : Nat) (h : q < 20) :
    let cells := readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis)
    s.basis (nativeRawPort j q) =
      StairArchiveRaw.letterBit (StairArchiveRaw.read (cells.drop 5) (q/2)) q := by
  simpa only [Shadow7.readCells_eq] using StairPacket.native_raw_read j s q h

end ECDSAAdd.Entrant.StairPacket.Shadow7
