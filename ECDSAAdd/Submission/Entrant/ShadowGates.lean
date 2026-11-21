import ECDSAAdd.Submission.Entrant.StairSideA

/-! Integer-walk blocks with a seven-bit reduction in both active rails.
The 15-tick block and the archive's public representation are shared with the stock window. -/
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed GateMirror Partial StairArchiveGates

def sbP (s : Nat) : Nat := (513-s)/2 - 7

def smallBits (j : Fin 23) := Shadow7.sbP (start j)

def shape (j : Fin 23) : IntegerPacket.Shape where
  start := start j
  length := 15
  mid := Shadow7.smallBits j+17
  rangeEnd := by have h:=j.isLt; simp [start]; omega
  extent := by have h:=j.isLt; simp [start,Shadow7.smallBits,Shadow7.sbP]; omega
  midBound := by simp [Shadow7.smallBits,Shadow7.sbP,start]; omega

def routed (j : Fin 23) (a : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (net j a) (skywalkIntegerTick (IntegerPacket.ports (Shadow7.shape j) a)) ++
    Shadow7.routed j (a+1) n

def unrouted (j : Fin 23) (a : Nat) : Nat → Program
  | 0 => []
  | n+1 => Shadow7.unrouted j (a+1) n ++
    renameProgram (net j a) (skywalkIntegerUntick (IntegerPacket.ports (Shadow7.shape j) a))

def wpP (s : Nat) : Nat := railP s - Shadow7.sbP s - 16

def e0P (s : Nat) : Nat := 1574 + Shadow7.sbP s

def lowsP (s : Nat) : Nat := 18 + Shadow7.sbP (s+15) - Shadow7.sbP s

def a0P (s : Nat) : Nat := s + Shadow7.sbP s + 32

def b0P (s : Nat) : Nat := 787 + Shadow7.sbP s

def bankW (s i : Nat) : Wire :=
  if i < 3 then Shadow7.e0P s + i else if i < Shadow7.wpP s then bTopP s + 1 + i - Shadow7.wpP s else 1598 + i - Shadow7.wpP s

def poolW (s i : Nat) : Wire := if 1598 + i < Shadow7.e0P s then 1598 + i else 1608 + i

def leaveAdjust (s : Nat) : List Gate :=
  adjustG ((List.range (Shadow7.wpP s)).map (Shadow7.bankW s)) ((List.range (Shadow7.wpP s - 1)).map (Shadow7.poolW s)) (Shadow7.e0P s + 6) 1597

def leaveBarrel (s : Nat) : List Gate :=
  stageG 1613 (Shadow7.bankW s) controlsP0 1 (Shadow7.wpP s) ++ stageG 1613 (Shadow7.bankW s) controlsP1 2 (Shadow7.wpP s + 1) ++
  stageG 1613 (Shadow7.bankW s) controlsP2 4 (Shadow7.wpP s + 3) ++ stageG 1613 (Shadow7.bankW s) controlsP3 8 (Shadow7.wpP s + 7)

def columnsP (s : Nat) : List HighBankJoin.Column :=
  (List.range 18).map fun i =>
    ⟨decide (i < Shadow7.lowsP s), if i < 16 then some (tagsP.getD i 0) else none, Shadow7.a0P s + i, Shadow7.bankW s i⟩

def leaveLowStore (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s; let bs := (List.range L).map (Shadow7.b0P s + ·)
  [.cx (Shadow7.e0P s + 3) 1560, .cx 1559 1560, .pop (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559] ++
  (List.range L).map (fun i => .ccx 1556 (Shadow7.a0P s + i) (Shadow7.b0P s + i)) ++ xsG bs ++
  addG bs ((List.range (L-1)).map (1559 + ·)) 1558 ++ xsG bs ++
  [.pop (Shadow7.b0P s - 1) 1557 1558, .cx (Shadow7.a0P s - 1) 1557, .x 1557]

/-- Store carries above the anchored ten-wire block while its flags and bank bits are live. -/
def storeW (s i : Nat) : Wire :=
  let q := Partial.storeW i
  if q < Shadow7.e0P s then q else q + 10

def leaveStoreMapped (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s; let top := Shadow7.a0P s + L - 1; let H := Shadow7.wpP s + 15 - L
  let hi := (List.range H).map (fun i => Shadow7.bankW s (L+i))
  let seq := fun i => if i = 0 then top else Shadow7.bankW s (L+i-1)
  let seq2 := (List.range (L+1)).map (Shadow7.b0P s - 1 + ·)
  [.make (top-2) (top-1) 1558, .x 1558, .x top] ++ xsG hi ++
  chainG (Shadow7.storeW s) seq [.cx (Shadow7.storeW s (H+1)) 1557, .x 1557] 0 (H+1) ++
  xsG hi.reverse ++ [.x top, .x 1558, .pop (top-2) (top-1) 1558, .make 1556 1557 1558, .x 1558] ++
  xsG seq2 ++ chainG (1558 + ·) (Shadow7.b0P s - 1 + ·) [.cx (1558+(L+1)) 1556, .x 1556] 0 (L+1) ++
  xsG seq2.reverse ++ [.x 1558]

def leaveLowClose (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s
  xsG ((List.range 15).map (s+16+·)) ++
  (List.range (L+1)).map (fun i => .cx (Shadow7.e0P s + 5) (Shadow7.b0P s - 1 + i)) ++
  (List.range (L+1)).flatMap (fun i => cswapG (s+30) (Shadow7.b0P s - 1 + i) (Shadow7.a0P s - 1 + i))

def movesP (s : Nat) : List (Wire × Wire) :=
  (List.range (Shadow7.wpP (s+15) - 3)).map (fun i => (Shadow7.bankW s (Shadow7.lowsP s + i), bTopP (s+15) + 4 + i - Shadow7.wpP (s+15))) ++
  [(1557, Shadow7.e0P (s+15) + 3), (1558, Shadow7.e0P (s+15) + 4), (Shadow7.e0P s + 5, Shadow7.e0P (s+15) + 5),
   (Shadow7.e0P s + 3, Shadow7.e0P (s+15) + 6), (Shadow7.e0P s + 7, Shadow7.e0P (s+15) + 7), (Shadow7.e0P s + 6, Shadow7.e0P (s+15) + 8)]

def leaveClose (s : Nat) : List Gate :=
  eventsG (Shadow7.e0P s + 7) (Shadow7.e0P s + 4)
    [(OB5.sig (s+14) (s+1044), 1556), (OB5.sig (s+14) (s+1045), 1559), (OB5.sig (s+14) (s+1046), 1560),
     (OB5.sig (s+14) (s+1047), 1561), (OB5.sig (s+14) (s+1048), 1562)] ++
  swapsG (Shadow7.movesP s)

def moveRows (s : Nat) : List MoveChain.Row := (List.range 16).map (fun i => (tagsP.getD i 0, Shadow7.a0P s + i))

def leaveFix5Move (s h : Nat) : List Gate :=
  (leaveFix5 s h).take 27 ++ (rowGates (Shadow7.e0P s + 6) (Shadow7.moveRows s) ++ (leaveFix5 s h).drop 43)

def leaveJoinMove (s : Nat) : List Gate :=
  keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s + i) 1613 0 16 ++ wordG 1614 (Shadow7.columnsP s)

def leaveMoveOps (s : Nat) : List Gate :=
  leaveFix0 s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ leaveFix2 s (Shadow7.sbP s) ++ leaveFix3 s (Shadow7.sbP s) ++
  leaveFix4 s (Shadow7.sbP s) ++ Shadow7.leaveFix5Move s (Shadow7.sbP s) ++ Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++
  leaveFix8 s (Shadow7.sbP s) ++ Shadow7.leaveJoinMove s ++ leaveFix10 s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++
  leaveFix12 s (Shadow7.sbP s) ++ Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

def leaveMoveP (j : Fin 23) : Program := GateMirror.forward (Shadow7.leaveMoveOps (start j))

def leaveMoveInvP (j : Fin 23) : Program := inverse (Shadow7.leaveMoveOps (start j))

def portalOps (t : Nat) : List Gate :=
  let w := Shadow7.wpP t; let aBot := Shadow7.a0P t; let bBot := 802 + Shadow7.sbP t
  let rA := (List.range w).map (aBot + ·); let rB := (List.range w).map (bBot + ·)
  let bA := (List.range (w-3)).map (aBot + 3 + ·); let bB := (List.range (w-3)).map (bBot + 3 + ·)
  let sgn := Shadow7.e0P t + 5; let G := t + 15; let f3 := Shadow7.e0P t + 3; let f4 := Shadow7.e0P t + 4
  [.cx (aBot + w - 1) sgn, .cx (bTopP t) sgn] ++ exchangeG G (rA.zip rB) ++ cxsG sgn rB ++
  [.make aBot (aBot+1) 1557] ++ latchG true none 1556 1557 ((List.range (w-2)).map (fun i => (aBot+2+i, 1558+i))) ++
  [.pop aBot (aBot+1) 1557, .cx 1556 f3, .cx f3 1556] ++
  latchG false (some f3) f4 bBot ((List.range (w-1)).map (fun i => (bBot+1+i, 1556+i))) ++
  [.x (aBot+2), .make (bBot+2) (aBot+2) 1556] ++ addG bB ((List.range (w-4)).map (1557 + ·)) 1556 ++
  (bA.zip bB).map (fun p => .ccx f4 p.1 p.2) ++ [.pop (bBot+2) (aBot+2) 1556, .x (aBot+2)] ++
  transferG (bA.zip bB) ++ cxsG sgn [bBot, bBot+1, bBot+2] ++
  exchangeG G [(aBot, bBot), (aBot+1, bBot+1), (aBot+2, bBot+2)]

def parkOps (e : Nat) : List Gate :=
  swapsG [(Shadow7.e0P e + 6, bTopP e + 1), (Shadow7.e0P e + 7, bTopP e + 2), (Shadow7.e0P e + 8, bTopP e + 3)]

def enterOps (s : Nat) : List Gate := enterFix s (Shadow7.sbP s)

def enterP (j : Fin 23) : Program := GateMirror.forward (Shadow7.enterOps (start j))

def enterInvP (j : Fin 23) : Program := inverse (Shadow7.enterOps (start j))

def portalP (t : Nat) : Program := GateMirror.forward (Shadow7.portalOps t)

def portalInvP (t : Nat) : Program := inverse (Shadow7.portalOps t)

def parkP (e : Nat) : Program := GateMirror.forward (Shadow7.parkOps e)

def parkInvP (e : Nat) : Program := inverse (Shadow7.parkOps e)

def scratchW (t k : Nat) : Nat := if 1556 + k < Shadow7.e0P t then 1556 + k else 1566 + k

def scratchS (t k : Nat) : Nat :=
  if Shadow7.scratchW t k + t < 2068 then Shadow7.scratchW t k else bTopP t + 4 + (Shadow7.scratchW t k + t - 2068)

def loadPortsWP (t f : Nat) : List Wire := cellsLoadP t ++ [f, f+1, f+2] ++ (List.range 132).map (Shadow7.scratchS t)

def restorePortsWP (t : Nat) : List Wire := cellsRestoreP t ++ (List.range 134).map (Shadow7.scratchS t)

def scratchX (e k : Nat) : Nat :=
  if e ≤ 369 then Shadow7.scratchS e k else if 1556 + k + e < 2068 then 1556 + k else bTopP e + 4 + (1556 + k + e - 2068)

def loadPortsXP (e f : Nat) : List Wire := cellsLoadP e ++ [f, f+1, f+2] ++ (List.range 132).map (Shadow7.scratchX e)

def restorePortsXP (e : Nat) : List Wire := cellsRestoreP e ++ (List.range 134).map (Shadow7.scratchX e)

def archiveLoadP (j : Fin 23) (d : Bool) : Program :=
  renameProgram (fun q => (Shadow7.loadPortsWP (start j + 15) (Shadow7.e0P (start j + 15) + 6)).getD q 0)
    (if d then integer_load0 else integer_load1) ++ moveLoadP (start j + 15)

def archiveRestoreP (j : Fin 23) (d : Bool) : Program :=
  renameProgram (fun q => (Shadow7.restorePortsWP (start j + 15)).getD q 0)
    (if d then integer_restore0 else integer_restore1) ++ moveRestoreP (start j + 15) (Shadow7.e0P (start j + 15) + 6)

def exitLoadP (e : Nat) (d : Bool) : Program :=
  renameProgram (fun q => (Shadow7.loadPortsXP e (bTopP e + 1)).getD q 0)
    (if d then integer_load0 else integer_load1) ++ moveLoadP e

def exitRestoreP (e : Nat) (d : Bool) : Program :=
  renameProgram (fun q => (Shadow7.restorePortsXP e).getD q 0)
    (if d then integer_restore0 else integer_restore1) ++ moveRestoreP e (bTopP e + 1)

def params : WindowFold.Pieces Program :=
  {WindowFold.ofParts Shadow7.enterP Shadow7.enterInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP
     Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
     Shadow7.exitLoadP Shadow7.exitRestoreP with routed := Shadow7.routed, unrouted := Shadow7.unrouted}

end ECDSAAdd.Entrant.StairPacket.Shadow7
