import ECDSAAdd.Submission.Entrant.StairSideA
import ECDSAAdd.Submission.Entrant.Window

-- ===== ShadowGates =====
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
    (if d then ReducedWindowArchives.load0 else ReducedWindowArchives.load1) ++ moveLoadP (start j + 15)

def archiveRestoreP (j : Fin 23) (d : Bool) : Program :=
  renameProgram (fun q => (Shadow7.restorePortsWP (start j + 15)).getD q 0)
    (if d then ReducedWindowArchives.restore0 else ReducedWindowArchives.restore1) ++ moveRestoreP (start j + 15) (Shadow7.e0P (start j + 15) + 6)

def exitLoadP (e : Nat) (d : Bool) : Program :=
  renameProgram (fun q => (Shadow7.loadPortsXP e (bTopP e + 1)).getD q 0)
    (if d then ReducedWindowArchives.load0 else ReducedWindowArchives.load1) ++ moveLoadP e

def exitRestoreP (e : Nat) (d : Bool) : Program :=
  renameProgram (fun q => (Shadow7.restorePortsXP e).getD q 0)
    (if d then ReducedWindowArchives.restore0 else ReducedWindowArchives.restore1) ++ moveRestoreP e (bTopP e + 1)

def params : WindowFold.Pieces Program :=
  {WindowFold.ofParts Shadow7.enterP Shadow7.enterInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP
     Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
     Shadow7.exitLoadP Shadow7.exitRestoreP with routed := Shadow7.routed, unrouted := Shadow7.unrouted}

end ECDSAAdd.Entrant.StairPacket.Shadow7

-- ===== ShadowBounds =====
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open SkywalkNat

/-- The far branch alone needs the smaller word to fit the narrowed cutoff. -/
def SmallIfFar (b k : Nat) (z : SkywalkNat.State) : Prop :=
  Shadow.far b k z → min z.u z.v < 2^b

/-- At the end of a block the smaller true word fits the entry cutoff in both branches. -/
def EndSmall (b : Nat) (z : SkywalkNat.State) : Prop :=
  min (step^[15] z).u (step^[15] z).v < 2^b

namespace Envelope

theorem exponent_bound (t : Nat) (h : t ≤ 390) : 512 - t ≤ sbP t + sbP t + 14 := by
  unfold sbP
  omega

theorem small_of_far (b : Nat) (z : SkywalkNat.State)
    (prod : z.u*z.v < 16384 * (2^b * 2^b))
    (far : Shadow.far b 15 z) : min z.u z.v < 2^b := by
  have positive : 0 < Shadow.limb b 15 := by unfold Shadow.limb; positivity
  have hf := (Nat.le_div_iff_mul_le positive).mp far
  have he : Shadow.limb b 15 = 65536*2^b := by
    unfold Shadow.limb
    rw [show b+15+1 = 16+b by omega, pow_add]
    rfl
  rw [he] at hf
  by_contra! large
  have hu := le_trans large (min_le_left z.u z.v)
  have hv := le_trans large (min_le_right z.u z.v)
  have hlarge : 16384*2^b ≤ z.u ∨ 16384*2^b ≤ z.v := by omega
  rcases hlarge with h | h
  · have q := Nat.mul_le_mul h hv
    have e : 16384*2^b*2^b = 16384*(2^b*2^b) := Nat.mul_assoc _ _ _
    omega
  · have q := Nat.mul_le_mul hu h
    have e : 2^b*(16384*2^b) = 16384*(2^b*2^b) := by ring
    omega

theorem endpoint_small (b : Nat) (z : SkywalkNat.State)
    (prod : z.u*z.v < 16384 * (2^b * 2^b)) :
    let e := step^[15] z
    min e.u e.v < 2^b := by
  dsimp only
  have contracted := iter_product_bound 15 z
  change 32768 * ((step^[15] z).u * (step^[15] z).v) ≤ z.u*z.v at contracted
  by_contra! large
  have hu := le_trans large (min_le_left _ _)
  have hv := le_trans large (min_le_right _ _)
  have both := Nat.mul_le_mul hu hv
  omega

theorem inputs_through (x p t : Nat) (hx : x < 2^256) (hp : p < 2^256) (ht : t ≤ 512) :
    let b := sbP t
    let z := step^[t] (init x p)
    SmallIfFar b 15 z ∧ EndSmall b z := by
  let z := step^[t] (init x p)
  have strict : x*p < 2^512 := by
    rw [show (512:Nat)=256+256 by decide, pow_add]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hx.le) (Nat.mul_lt_mul_of_pos_left hp (by positivity))
  have h := iter_product_bound t (init x p)
  change 2^t*(z.u*z.v) ≤ x*p at h
  have stepBound : z.u*z.v < 2^(512-t) := by
    have e : (2:Nat)^512 = 2^t*2^(512-t) := by rw [← pow_add]; congr 1; omega
    rw [e] at strict
    exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h strict)
  have envelope : 512 - t ≤ sbP t + sbP t + 14 := by unfold sbP; omega
  have power := Nat.pow_le_pow_right (by decide : 0 < 2) envelope
  have e : 2^(sbP t + sbP t + 14) = 16384*(2^(sbP t)*2^(sbP t)) := by
    rw [pow_add, pow_add, Nat.mul_comm]
    rfl
  have prod := lt_of_lt_of_le stepBound (power.trans_eq e)
  exact ⟨small_of_far _ _ prod, endpoint_small _ _ prod⟩

theorem inputs (x p t : Nat) (hx : x < 2^256) (hp : p < 2^256) (ht : t ≤ 390) :
    let b := sbP t
    let z := step^[t] (init x p)
    SmallIfFar b 15 z ∧ EndSmall b z :=
  inputs_through x p t hx hp (by omega)

/-- The hand-off uses the next cutoff only when the next state is far. -/
theorem nextFarSmall (x p t : Nat) (hx : x < 2^256) (hp : p < 2^256) (ht : t ≤ 390) :
    SmallIfFar (sbP (t+15)) 15 (step^[15] (step^[t] (init x p))) := by
  rw [← Function.iterate_add_apply, Nat.add_comm 15 t]
  exact (inputs_through x p (t+15) hx hp (by omega)).1

end Envelope
end ECDSAAdd.Entrant.StairPacket.Shadow7

-- ===== ShadowParts =====
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

-- ===== ShadowRoute =====
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

theorem canonical (j : Fin 23) (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Triple (IntegerPacket.ready (Shadow7.shape j) 0 z) (Shadow7.forward j)
      (IntegerPacket.ready (Shadow7.shape j) 15 (SkywalkTrace.next^[15] z)) :=
  IntegerPacket.semantic (Shadow7.shape j) 0 15 (by rfl) z odd

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

theorem restores (j : Fin 23) (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    IntegerPacket.Restores (IntegerPacket.ready (Shadow7.shape j) 0 z) (Shadow7.forward j) (Shadow7.reverse j) :=
  IntegerPacket.roundtrip (Shadow7.shape j) 0 15 (by rfl) z odd

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

theorem bounds (j : Fin 23) :
    toffoliCount (Shadow7.forward j)=15*(2*(Shadow7.smallBits j+18)) ∧
    measurementCount (Shadow7.forward j)=15*(Shadow7.smallBits j+18) ∧
    toffoliCount (Shadow7.reverse j)=15*(2*(Shadow7.smallBits j+18)) ∧
    measurementCount (Shadow7.reverse j)=15*(Shadow7.smallBits j+18) :=
  IntegerPacket.metrics (Shadow7.shape j) 0 15 (by rfl)

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic
set_option maxHeartbeats 3500000

theorem stable {j : Fin 23} {a q : Nat} (ha : a < 15)
    (hq:q∈(IntegerPacket.ports (Shadow7.shape j) a).wires) : net j a q=windowNet j q := by
  have hj:=j.isLt
  simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false] at hq
  unfold windowNet net OB5.sig start
  split <;> split
  all_goals try rfl
  all_goals
    repeat' first | cases_type And | cases_type Or
    all_goals try simp only [Wire] at *
    all_goals omega

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

theorem fixed_route (j : Fin 23) (a n : Nat) (bound:a+n≤15) :
    Shadow7.routed j a n=renameProgram (windowNet j) (IntegerPacket.seq (Shadow7.shape j) a n) ∧
    Shadow7.unrouted j a n=renameProgram (windowNet j) (IntegerPacket.back (Shadow7.shape j) a n) := by
  induction n generalizing a with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have ha : a < 15 := by omega
    have h:=(skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (Shadow7.shape j) ⟨a,ha⟩))
    obtain ⟨f,r⟩:=ih (a+1) (by omega)
    have app (g : Wire → Wire) (P Q : Program) : renameProgram g (P++Q)=renameProgram g P++renameProgram g Q := List.map_append
    simp only [Shadow7.routed,Shadow7.unrouted,IntegerPacket.seq,IntegerPacket.back,app,f,r]
    constructor
    · exact congrArg (fun P=>P++_) (renameProgram_congr_support _ _ _ (fun q hq=>
        Shadow7.stable ha (List.mem_toFinset.mp (h.1 hq))))
    · exact congrArg (fun P=>_++P) (renameProgram_congr_support _ _ _ (fun q hq=>
        Shadow7.stable ha (List.mem_toFinset.mp (h.2 hq))))

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem pull_routed (j:Fin 23) (i n:Nat) (bound:i+n≤15) (m:List Bool) (s:State) :
    pullState (windowNet j) (run (Shadow7.routed j i n) m s)=run (seq (Shadow7.shape j) i n) m (pullState (windowNet j) s) := by
  rw [(Shadow7.fixed_route j i n bound).1,run_rename _ (netInjective j)]

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem route_frame (j:Fin 23) (i n:Nat) (bound:i+n≤15) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) :
    Triple (Shadow7.onRails j i z) (Shadow7.routed j i n) (Shadow7.onRails j (i+n) (SkywalkTrace.next^[n] z)) := by
  intro s m ready
  have h:=IntegerPacket.semantic (Shadow7.shape j) i n bound z odd (pullState (windowNet j) s) m ready
  rw [←Shadow7.pull_routed j i n bound m s] at h
  exact h

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem route_records (j:Fin 23) (i n:Nat) (bound:i+n≤15) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (s:State) (m:List Bool) (h:Shadow7.onRails j i z s.basis) :
    readCells (Shadow7.shape j) i n (mappedBasis j (run (Shadow7.routed j i n) m s).basis)=SkywalkTrace.trace n z ∧
    ∀ d < i, cell (Shadow7.shape j) d (mappedBasis j (run (Shadow7.routed j i n) m s).basis)=cell (Shadow7.shape j) d (mappedBasis j s.basis) := by
  have hh:=records (Shadow7.shape j) i n bound z odd (pullState (windowNet j) s) m h
  rw [←Shadow7.pull_routed j i n bound m s] at hh
  exact hh

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem route_undo (j:Fin 23) (i n:Nat) (bound:i+n≤15) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) :
    Restores (Shadow7.onRails j i z) (Shadow7.routed j i n) (Shadow7.unrouted j i n) := by
  intro s m t ready
  have forward:=Shadow7.pull_routed j i n bound m s
  let actual:=run (Shadow7.routed j i n) m s
  have bk:pullState (windowNet j) (run (Shadow7.unrouted j i n) t actual)=run (back (Shadow7.shape j) i n) t (pullState (windowNet j) actual):=by
    rw [(Shadow7.fixed_route j i n bound).2,run_rename _ (netInjective j)]
  have fin:=IntegerPacket.roundtrip (Shadow7.shape j) i n bound z odd (pullState (windowNet j) s) m t ready
  change pullState (windowNet j) actual=_ at forward
  rw [forward,fin] at bk
  apply congrArg₂ State.mk (congrArg State.phase bk)
  funext q
  have h:=congrArg (fun x:State=>x.basis (windowNet j q)) bk
  change (run (Shadow7.unrouted j i n) t actual).basis (windowNet j (windowNet j q))=s.basis (windowNet j (windowNet j q)) at h
  have inv : windowNet j (windowNet j q)=q := by
    apply OB5.sig_invol
    have hj:=j.isLt
    simp [start];omega
  rwa [inv] at h

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket
attribute [local irreducible] run Shadow7.onRails
set_option maxHeartbeats 2000000

theorem split_run (j:Fin 23) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (s:State) (m n:List Bool)
    (ready:Shadow7.onRails j 0 z s.basis) (v:State)
    (active:Shadow7.onRails j 1 (SkywalkTrace.next z) v.basis)
    (first:cell (Shadow7.shape j) 0 (mappedBasis j v.basis)=
      cell (Shadow7.shape j) 0 (mappedBasis j (run (Shadow7.routed j 0 1) m s).basis)) :
    let out:=run (Shadow7.routed j 1 14) n v
    Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
    readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z := by
  have post:=Shadow7.route_frame j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) v n active
  have back:=Shadow7.route_records j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) v n active
  have front:=(Shadow7.route_records j 0 1 (by decide) z odd s m ready).1
  have firstValue:=congrArg List.head? front
  simp only [readCells,SkywalkTrace.trace,List.head?_cons,Option.some.injEq] at firstValue
  exact ⟨post.2,congr (congrArg List.cons ((back.2 0 (by decide)).trans (first.trans firstValue))) back.1⟩

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket

def watch (j:Fin 23) :=
  let p:=Shadow7.shape j
  let L:=ports p 1
  (L.a++L.b++[L.previous]++L.carry++((List.range' 1 14).flatMap fun r=>[(ports p r).ext,(ports p r).history])++
    [(ports p 0).a0,(ports p 0).history]).map (windowNet j)

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket
set_option linter.unusedSimpArgs false

theorem watch_congr (j:Fin 23) (s t:State) (agree:∀q∈Shadow7.watch j,t.basis q=s.basis q)
    (z:SkywalkRails.State) (active:Shadow7.onRails j 1 z s.basis) :
    Shadow7.onRails j 1 z t.basis ∧ cell (Shadow7.shape j) 0 (mappedBasis j t.basis)=cell (Shadow7.shape j) 0 (mappedBasis j s.basis) := by
  let p:=Shadow7.shape j
  let L:=ports p 1
  let S:=mappedBasis j s.basis
  let T:=mappedBasis j t.basis
  have locality (q:Wire) (mem:q∈L.a++L.b++[L.previous]++L.carry++((List.range' 1 14).flatMap fun r=>[(ports p r).ext,(ports p r).history])++[(ports p 0).a0,(ports p 0).history]) :
      T q=S q := agree _ (List.mem_map.mpr ⟨q,mem,rfl⟩)
  have add (xs:List Wire) (incl:∀q∈xs,T q=S q) : signedRegValue xs T=signedRegValue xs S:=by
    unfold signedRegValue;rw [regValue_congr _ _ _ incl]
  obtain ⟨a,b,prev,carry,free⟩:=active
  refine ⟨⟨(add _ (fun q h=>locality _ (by simp [L,p,h]))).trans a,
    (add _ (fun q h=>locality _ (by simp [L,p,h]))).trans b,
    (locality _ (by simp [L,p])).trans prev,
    (regValue_congr _ _ _ (fun q h=>locality _ (by simp [L,p,h]))).trans carry,?_⟩,?_⟩
  · intro r hr last
    have inRange:r∈List.range' 1 14:=by rw [List.mem_range'_1];exact ⟨hr,last⟩
    obtain ⟨e,h⟩:=free r hr last
    exact ⟨(locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans e,
      (locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans h⟩
  · exact Prod.ext (locality _ (by simp [L,p])) (locality _ (by simp [L,p]))

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run Shadow7.unrouted Shadow7.onRails

structure AdminResult (j:Fin 23) (reverse:Program) (src out:State) : Prop where
  phase : out.phase=src.phase
  unchanged : ∀q∈Shadow7.watch j,out.basis q=src.basis q
  undo : ∀m,run reverse m out=src

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run Shadow7.unrouted Shadow7.onRails

theorem body_run (j:Fin 23) (admin reverse:Program) (s:State) (m:List Bool)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z s.basis)
    (mid:let src:=run (Shadow7.routed j 0 1) m s
      Shadow7.AdminResult j reverse src (run admin (m.drop (measurementCount (Shadow7.routed j 0 1))) src)) :
    let out:=run (Shadow7.body j admin) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (Shadow7.unbody j reverse) n out=s := by
  let src:=run (Shadow7.routed j 0 1) m s
  let t:=m.drop (measurementCount (Shadow7.routed j 0 1))
  let pre:=run admin t src
  let n:=t.drop (measurementCount admin)
  have head:=Shadow7.route_frame j 0 1 (by decide) z odd s m active
  have valid:Shadow7.onRails j 1 (SkywalkTrace.next z) src.basis:=head.2
  have pass:=Shadow7.watch_congr j src pre mid.unchanged _ valid
  have span:=Shadow7.split_run j z odd s m n active pre pass.1 pass.2
  have last:=Shadow7.route_frame j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) pre n pass.1
  dsimp only [Shadow7.body,Shadow7.unbody]
  simp only [run_append,run_take]
  refine ⟨last.1.trans (mid.phase.trans head.1),span.1,span.2,?_⟩
  intro r
  have endBack:=Shadow7.route_undo j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) pre n r pass.1
  change run (Shadow7.unrouted j 0 1) _ (run reverse _ (run (Shadow7.unrouted j 1 14) r (run (Shadow7.routed j 1 14) n pre)))=s
  rw [endBack,mid.undo]
  exact Shadow7.route_undo j 0 1 (by decide) z odd s m _ active

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace SkywalkRails Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run

theorem ready_after_head (j:Fin 23) (P:Program) (s:State) (a b:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z s.basis)
    (preserve:∀t:State,∀q∈Shadow7.watch j,(run P b t).basis q=t.basis q) :
    Shadow7.onRails j 1 (SkywalkTrace.next z) (run P b (run (Shadow7.routed j 0 1) a s)).basis:=
  (Shadow7.watch_congr j _ _ (preserve _) _ (Shadow7.route_frame j 0 1 (by decide) z odd s a active).2).1

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

def tickSites (j:Fin 23) (a:Nat) := ((ports (Shadow7.shape j) a).wires.map (windowNet j))

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

def spanSites (j:Fin 23) (a n:Nat) := (List.range' a n).flatMap (Shadow7.tickSites j)

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

theorem route_sites (j:Fin 23) (a n:Nat) (lim:a+n≤15) (q:Wire) (inP:q∈wires (Shadow7.routed j a n)) :
    q∈Shadow7.spanSites j a n := by
  induction n generalizing a with
  | zero=>simp [Shadow7.routed,wires] at inP
  | succ n ih=>
    rw [Shadow7.routed,wires_append,Finset.mem_union] at inP
    rw [Shadow7.spanSites,List.range'_succ,List.flatMap_cons,List.mem_append]
    rcases inP with h|h
    · rw [renameProgram_support,Finset.mem_image] at h
      obtain ⟨t,used,eq⟩:=h
      have ht:a<15:=by omega
      have inside:=List.mem_toFinset.mp ((skywalkIntegerTick_wires_subset _ (ok (Shadow7.shape j) ⟨a,ht⟩)).1 used)
      exact Or.inl (List.mem_map.mpr ⟨t,inside,(Shadow7.stable ht inside).symm.trans eq⟩)
    · exact Or.inr (ih (a+1) (by omega) h)

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

theorem route_outside (j:Fin 23) (a n:Nat) (lim:a+n≤15) (q:Wire) (free:q∉Shadow7.spanSites j a n) (s:State) (m:List Bool) :
    (run (Shadow7.routed j a n) m s).basis q=s.basis q :=
  run_preserves_outside _ _ _ _ (fun used=>free (Shadow7.route_sites j a n lim q used))

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

theorem old_clear {j:Fin 23} {a n q:Nat} (lim:a+n≤15)
    (old:oldRange (start j+a) (windowNet j q)) : q∉Shadow7.spanSites j a n := by
  intro mem
  obtain ⟨r,hr,inside⟩:=List.mem_flatMap.mp mem
  rw [List.mem_range'_1] at hr
  obtain ⟨w,hw,eq⟩:=List.mem_map.mp inside
  have undo:windowNet j (windowNet j w)=w:=by
    apply OB5.sig_invol
    have hj:=j.isLt;simp [start];omega
  rw [←eq,undo] at old
  have hj:=j.isLt
  simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at hw
  simp only [oldRange,start] at old
  repeat' first | cases_type Or | cases_type And
  all_goals try simp only [Wire] at *
  all_goals omega

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction

theorem native_carry (j:Fin 23) (z:SkywalkRails.State) (s:State) (ready:Shadow7.onRails j 15 z s.basis) (q:Wire)
    (mem:q∈((ports (Shadow7.shape j) 15).carry.map (windowNet j))) : s.basis q=false:=by
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp mem
  exact (regValue_zero _ _).mp ready.2.2.2.1 _ hw

end ECDSAAdd.Entrant.StairPacket.Shadow7

-- ===== ShadowRouteCover =====
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

def MayTouch (j : Fin 23) (w : Wire) : Prop :=
  (start j + 15 ≤ w ∧ w ≤ start j + 14 + 16 + (Shadow7.shape j).mid + 2) ∨
  (786 ≤ w ∧ w ≤ 787 + (Shadow7.shape j).mid) ∨
  (1556 ≤ w ∧ w ≤ 1556 + (Shadow7.shape j).mid) ∨
  (1044 + start j ≤ w ∧ w < 1044 + start j + 15)

instance (j : Fin 23) (w : Wire) : Decidable (Shadow7.MayTouch j w) := by
  unfold Shadow7.MayTouch
  infer_instance

theorem named_range (j : Fin 23) (a n q : Nat) (lim : a + n ≤ 15)
    (outside : ¬Shadow7.MayTouch j (windowNet j q)) : q ∉ Shadow7.spanSites j a n := by
  intro mem
  obtain ⟨r, hr, inside⟩ := List.mem_flatMap.mp mem
  rw [List.mem_range'_1] at hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp inside
  have undo : windowNet j (windowNet j w) = w := by
    apply OB5.sig_invol
    have hj := j.isLt
    simp [start]
    omega
  rw [undo] at outside
  apply outside
  simp only [ports, SkywalkIntegerLayout.wires, SkywalkIntegerLayout.ah, SkywalkIntegerLayout.bh,
    List.mem_cons, List.mem_append, List.mem_range'_1, List.not_mem_nil, or_false,
    Shadow7.shape, Shadow7.smallBits, start] at hw
  simp only [Shadow7.MayTouch, Shadow7.shape, Shadow7.smallBits, start]
  repeat' first | cases_type Or | cases_type And
  all_goals try simp only [Wire] at *
  all_goals omega

theorem through_body (j : Fin 23) (P : Program) (s : State) (m : List Bool) (q : Nat)
    (free : ¬Shadow7.MayTouch j (windowNet j q))
    (admin : let a := run (Shadow7.routed j 0 1) m s
      (run P (m.drop (measurementCount (Shadow7.routed j 0 1))) a).basis q = a.basis q) :
    (run (Shadow7.body j P) m s).basis q = s.basis q := by
  simp only [Shadow7.body, run_append, run_take]
  exact (Shadow7.route_outside j 1 14 (by decide) q (Shadow7.named_range j 1 14 q (by decide) free) _ _).trans
    (admin.trans (Shadow7.route_outside j 0 1 (by decide) q (Shadow7.named_range j 0 1 q (by decide) free) s m))

theorem body_cover (j : Fin 23) (P : Program) (controls effects : List Wire)
    (clean : ∀ q ∈ controls, ¬Shadow7.MayTouch j (windowNet j q))
    (apart : ∀ q ∈ controls, q ∉ effects) (cover : wires P ⊆ effects.toFinset)
    (s : State) (m : List Bool) (q : Wire) (hit : q ∈ controls) :
    (run (Shadow7.body j P) m s).basis q = s.basis q :=
  Shadow7.through_body j P s m q (clean q hit) (run_preserves_outside P _ _ q
    (fun used => apart q hit (List.mem_toFinset.mp (cover used))))

theorem ext_head (P : Program) (j : Fin 23) (Q : Program) (effects : List Wire)
    (s : State) (m n : List Bool) (q : Wire) (native : ¬Shadow7.MayTouch j (windowNet j q))
    (enter : q ∉ wires P) (admin : q ∉ effects) (cover : wires Q ⊆ effects.toFinset) :
    (run (Shadow7.body j Q) n (run P m s)).basis q = s.basis q :=
  (Shadow7.through_body j Q _ n q native (run_preserves_outside Q _ _ q
    (fun used => admin (List.mem_toFinset.mp (cover used))))).trans (run_preserves_outside P _ _ q enter)

theorem sig_tail (j : Fin 23) (h21 : j.val ≤ 21) (q : Wire)
    (lo : Shadow7.e0P (start j) + 6 ≤ q) (hi : q + start j ≤ 2054)
    (i : Nat) (ile : i ≤ start j + 14) : OB5.sig i q = q := by
  have top : start j ≤ 390 := by simp only [start]; omega
  apply WideReference.sig_fixed
  · intro band
    simp only [Shadow7.e0P] at lo
    simp only [Wire] at band
    omega
  · intro mirror
    simp only [Wire] at hi mirror
    omega

section
open MappedCompressed
attribute [local irreducible] run SkywalkIntegerLayout.wires

def firstUnchanged (j : Fin 23) (q : Wire) : Prop :=
  let r := windowNet j q
  r = (ports (Shadow7.shape j) 0).previous ∨ r ∉ (ports (Shadow7.shape j) 0).wires

instance (j : Fin 23) (q : Wire) : Decidable (Shadow7.firstUnchanged j q) := by
  unfold Shadow7.firstUnchanged
  infer_instance

theorem first_preserves (j : Fin 23) (z : SkywalkRails.State) (odd : (z.a + z.b) % 2 = 1)
    (s : State) (m : List Bool) (ready : Shadow7.onRails j 0 z s.basis)
    (q : Wire) (free : Shadow7.firstUnchanged j q) : (run (Shadow7.routed j 0 1) m s).basis q = s.basis q := by
  let p := Shadow7.shape j
  let L := ports p 0
  let virt := pullState (windowNet j) s
  let v := windowNet j q
  have first : 0 < p.length := by
    change 0 < 15
    decide
  have inv : windowNet j v = q := by
    apply OB5.sig_invol
    have hj := j.isLt
    simp [start]
    omega
  have step := Shadow7.pull_routed j 0 1 (by decide) m s
  simp only [seq, List.append_nil] at step
  have at_q := congrArg (fun x : State => x.basis v) step
  change (run (Shadow7.routed j 0 1) m s).basis (windowNet j v) =
    (run (skywalkIntegerTick L) m virt).basis v at at_q
  rw [inv] at at_q
  refine at_q.trans (Eq.trans ?_ (show virt.basis v = s.basis q from congrArg s.basis inv))
  rcases free with e | e
  · change v = L.previous at e
    rw [e]
    obtain ⟨ha, hb, hg, hc, hnew⟩ := ready
    obtain ⟨he, hh⟩ := hnew 0 (by decide) first
    obtain ⟨_, _, _, _, _, prev, _⟩ :=
      executed p ⟨0, first⟩ _ _ _ odd virt m ⟨ha, hb, hg, he, hh, hc⟩
    exact prev.trans hg.symm
  · apply run_preserves_outside
    exact fun used => e (List.mem_toFinset.mp ((skywalkIntegerTick_wires_subset _ (ok p ⟨0, first⟩)).1 used))

end

section
open ArchivePortAction
attribute [local irreducible] run measurementCount

theorem body_keeps (j : Fin 23) (P : Program) (ps : Ports) (d : Bool) (row : Nat)
    (s : State) (m : List Bool) (off : ∀ i : Fin 16, ps ⟨i.val, by omega⟩ ∉ Shadow7.spanSites j 1 14)
    (hold : Frame ps (code d) row (run P (m.drop (measurementCount (Shadow7.routed j 0 1)))
      (run (Shadow7.routed j 0 1) m s))) : Kept ps d row (run (Shadow7.body j P) m s) := by
  intro i
  simp only [Shadow7.body, run_append, run_take]
  exact (Shadow7.route_outside j 1 14 (by decide) _ (off i) _ _).trans (hold ⟨i.val, by omega⟩)

theorem after_encoded (j : Fin 23) (P : Program) (outPorts : Ports) (d : Bool) (row : Nat)
    (src : State) (m : List Bool)
    (final : Frame outPorts (code d) row (run P (m.drop (measurementCount (Shadow7.routed j 0 1)))
      (run (Shadow7.routed j 0 1) m src)))
    (i : Fin 157) (hi : 16 ≤ i.val) (q : Wire) (slot : outPorts i = q)
    (free : ¬Shadow7.MayTouch j (windowNet j q)) : (run (Shadow7.body j P) m src).basis q = false := by
  simp only [Shadow7.body, run_append, run_take]
  apply (Shadow7.route_outside j 1 14 (by decide) q (Shadow7.named_range j 1 14 q (by decide) free) _ _).trans
  rw [←slot, final, archive_blank _ _ hi, Nat.zero_testBit]

end

end ECDSAAdd.Entrant.StairPacket.Shadow7

-- ===== ShadowPortalFacts =====
namespace ECDSAAdd.Entrant.StairPacket.PortalCut


theorem orientation_shadow7 (b U u v e : Nat) (unit : 2*b≤U) (positive:0<b)
    (small : 3*U ≤ u+v → min u v < b) (en:e≤1) :
    (3*U≤u+v ∧ U≤u-e) ↔ (3*U≤u+v ∧ b≤u) := by
  by_cases f : 3*U ≤ u+v
  · exact orientation b U u v e unit positive (small f) en
  · simp [f]

end ECDSAAdd.Entrant.StairPacket.PortalCut

namespace ECDSAAdd.Entrant.StairPacket.PortalCut


theorem clear_value_shadow7 (b U u v e : Nat) (unit:2*b≤U) (positive:0<b)
    (small : 3*U ≤ u+v → min u v < b) (en:e≤1) (eu:e≤u) :
    let M:=u-e
    let X:=u+v
    let w:=if 4*U≤M%(8*U) ∧ X%(8*U)<4*U then 1 else 0
    M/(8*U)+w=if 3*U≤X ∧ b≤u then X/(8*U) else 0 := by
  by_cases f : 3*U ≤ u+v
  · exact clear_value b U u v e unit positive (small f) en eu
  · dsimp only
    have div0 : (u-e)/(8*U) = 0 := Nat.div_eq_of_lt (by omega)
    have rem : (u-e)%(8*U) = u-e := Nat.mod_eq_of_lt (by omega)
    simp [f,div0,rem,show ¬ 4*U ≤ u-e by omega]

end ECDSAAdd.Entrant.StairPacket.PortalCut

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem actual_flags_shadow7 (a b:Wire) (as bs:List (Wire×Wire)) (mag:Wire) (A B:List Wire)
    (aShape:a::b::as.map Prod.fst=A) (bShape:PortalAnd.digits mag bs=B)
    (s:BasisState) (U small u v e:Nat) (ub:2*small≤U) (bp:0<small)
    (sz : 3*U ≤ u+v → min u v < small) (en:e≤1) (x:regValue A s=(u+v)/U) (y:regValue B s=(u-e)/U) :
    PortalAnd.high a b as s=decide (3*U≤u+v) ∧
    (PortalAnd.high a b as s && (PortalAnd.digits mag bs).any s)=decide (3*U≤u+v ∧ small≤u) := by
  have up:0<U:=by omega
  have far:PortalAnd.high a b as s=decide (3*U≤u+v):=by
    rw [PortalAnd.high,atLeastThree,aShape,x]
    apply Bool.eq_iff_iff.mpr; simpa only [decide_eq_true_eq] using (Nat.le_div_iff_mul_le up : 3≤(u+v)/U ↔ _)
  have longer:(PortalAnd.digits mag bs).any s=decide (U≤u-e):=by
    rw [bShape,nonzero,y]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      by_contra hh
      rw [Nat.div_eq_of_lt (by omega)] at h;omega
    · intro hh
      exact Nat.div_pos hh up
  refine ⟨far,?_⟩
  rw [far,longer]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq,Bool.and_eq_true] using PortalCut.orientation_shadow7 small U u v e ub bp sz en

end ECDSAAdd.Entrant.StairPacket.PortalValues

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem input_eq_shadow7 (a0 a1 a2 b0 b1 b2 long:Wire) (xs ys:List Wire) (s:BasisState)
    (U small u v e:Nat) (unit:2*small≤U) (bp:0<small) (sz : 3*U ≤ u+v → min u v < small) (en:e≤1) (eu:e≤u)
    (a:regValue (a0::a1::a2::xs) s=(u+v)/U)
    (b:regValue (b0::b1::b2::ys) s=(u-e)/U)
    (orient:s long=decide (3*U≤u+v ∧ small≤u)) (same:xs.length=ys.length) :
    (regValue ys s+(s b2 && !s a2).toNat)%2^ys.length=copyValue (some long) s (regValue xs s) := by
  have hp:0<U:=by omega
  have ax:=wideThird _ _ _ _ _ U _ hp a
  have by':=wideThird _ _ _ _ _ U _ hp b
  have bits:(s b2 && !s a2).toNat =
      if 4*U≤(u-e)%(8*U) ∧ (u+v)%(8*U)<4*U then 1 else 0 := by
    cases bbit:s b2 <;> cases abit:s a2 <;> simp_all
  have v':=PortalCut.clear_value_shadow7 small U u v e unit bp sz en eu
  rw [upper _ _ _ _ _ U _ b,bits,v',copyValue,orient,upper _ _ _ _ _ U _ a]
  by_cases cond:3*U≤u+v ∧ small≤u
  · simp only [cond]
    apply Nat.mod_eq_of_lt
    rw [←upper _ _ _ _ _ U _ a,←same]
    exact regValue_lt _ _
  · simp [cond]

end ECDSAAdd.Entrant.StairPacket.PortalValues

-- ===== ShadowLeaveFacts =====
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw

theorem shadow_odd_shadow7 (b:Nat) (z:SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (odd:z.v%2=1) :
    (Shadow.reduced b 15 z).v%2=1 := by
  by_cases f : Shadow.far b 15 z
  · exact shadow_odd b z (small f) odd
  · simpa [Shadow.reduced,f] using odd

end ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw

theorem true_records_shadow7 (b:Nat) (z:SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (odd:z.v%2=1) (G S:Bool) :
    let T:=Shadow.reduced b 15 z
    SkywalkTrace.trace 15 (encode G S T.u T.v)=SkywalkTrace.trace 15 (encode G S z.u z.v) := by
  by_cases f : Shadow.far b 15 z
  · exact true_records b z (small f) odd G S
  · simp [Shadow.reduced,f]

end ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw

theorem interrupted_row_shadow7 (b:Nat) (z:SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (odd:z.v%2=1) (G S cross:Bool)
    (cells:List (Bool×Bool))
    (records:let T:=Shadow.reduced b 15 z
      cells=SkywalkTrace.trace 15 (encode G S T.u T.v)) :
    let far:=decide (Shadow.far b 15 z)
    let u:=far && afterFlags (decide (z.v<z.u)) (cells.take 5)
    ∃row<63145,∀q<23,(rawCol q).testBit row=rawBit (read (cells.drop 5)) far u (far && cross) q := by
  rw [records.trans (true_records_shadow7 b z small odd G S)]
  by_cases f:Shadow.far b 15 z
  · simpa only [f,decide_true,Bool.true_and] using
      far_suffix 5 (Shadow.represented _ _ _ (small f) f).1 G S cross (by omega) odd
  · simpa only [f,decide_false,Bool.false_and] using near_suffix 5 z G S (by omega) odd

end ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.SharedSigned
open SkywalkRails IntegerHigh
set_option maxHeartbeats 2500000

theorem same_shadow7 (b:Nat) (z:SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (odd:z.v%2=1) (G S:Bool) :
    let t:=Shadow.reduced b 15 z
    let pair:=flags G S (SkywalkTrace.trace 15 (encode G S z.u z.v))
    SkywalkTrace.next^[15] (encode G S t.u t.v)=encode pair.1 pair.2 (SkywalkNat.step^[15] t).u (SkywalkNat.step^[15] t).v ∧
    SkywalkTrace.next^[15] (encode G S z.u z.v)=encode pair.1 pair.2 (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v:=by
  have shadow:=lift 15 G S (Shadow.reduced b 15 z) (shadow_odd_shadow7 b z small odd)
  rw [true_records_shadow7 b z small odd G S] at shadow
  exact ⟨shadow,lift _ _ _ _ odd⟩

end ECDSAAdd.Entrant.StairPacket.SharedSigned

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed SkywalkRails
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem advance_signed_gen_shadow7 (i b x p:Nat) (lo:15≤ i) (hi:i+15<512) (good:Bounds x p)
    (raw history:State) (dom:Domain i x p raw) (G S:Bool)
    (input:InputAt i (encode G S (unsigned i x p).u (unsigned i x p).v) raw)
    (small : Shadow7.SmallIfFar b 15 (unsigned i x p)) :
    let z:=unsigned i x p
    let t:=Shadow.reduced b 15 z
    let flags:=SharedSigned.flags G S (SkywalkTrace.trace 15 (encode G S z.u z.v))
    let endState:=unsigned (i+15) x p
    SkywalkTrace.next^[15] (encode G S t.u t.v)=encode flags.1 flags.2 (SkywalkNat.step^[15] t).u (SkywalkNat.step^[15] t).v ∧
      InputAt (i+15) (encode flags.1 flags.2 endState.u endState.v) (endRaw i raw history):=by
  let z:=unsigned i x p
  have odd:z.v%2=1:=(SkywalkNat.iter_valid i (SkywalkNat.init x p) good.positive good.odd).2.1
  obtain ⟨a,b'⟩:=SharedSigned.same_shadow7 b z small odd G S
  have eq:=unique_input input (fixed_input i x p (by omega) good raw dom)
  have stepRel:canonical (i+15) x p=SkywalkTrace.next^[15] (canonical i x p):=by rw [Nat.add_comm];exact Function.iterate_add_apply _ _ _ _
  have numRel:unsigned (i+15) x p=SkywalkNat.step^[15] z:=by rw [Nat.add_comm];exact Function.iterate_add_apply _ _ _ _
  have nextDom:=advance_gen i x p lo (by omega) good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw history dom
  have active:=fixed_input (i+15) x p hi good (endRaw i raw history) nextDom
  dsimp only
  refine ⟨a,?_⟩
  rw [stepRel,←eq,b'] at active
  simpa only [numRel] using active

end ECDSAAdd.Entrant.StairPacket.WideReference

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
set_option maxRecDepth 25000
attribute [local irreducible] run SkywalkNat.step

theorem stepInput_gen_shadow7 (i b x p:Nat) (lo:15 ≤ i) (hi:i+15<512) (good:Bounds x p)
    (raw v:State) (g sg:Bool) (domain:Domain i x p raw) (input:InputAt i (signedAt i x p g sg) raw)
    (small : Shadow7.SmallIfFar b 15 (unsigned i x p)) :
    let next:=SharedSigned.flags g sg (SkywalkTrace.trace 15 (signedAt i x p g sg))
    Domain (i+15) x p (endRaw i raw v) ∧ InputAt (i+15) (signedAt (i+15) x p next.1 next.2) (endRaw i raw v) := by
  exact ⟨advance_gen i x p lo (Nat.le_of_lt hi) good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw v domain,
    (advance_signed_gen_shadow7 i b x p lo hi good raw v domain g sg input small).2⟩

end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open IntegerHigh SkywalkNat Shadow HighBankSum

theorem trueControls_shadow7 (b w : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z)
    (odd : z.v%2=1) (room : high b 15 z+1<2^w) (p : Ports) (v : BasisState)
    (bits : ∀i<16,v (p.u+i)=((total (step^[15] (reduced b 15 z)))/2^(b+1)).testBit i)
    (par : parityBits p v=oddBits (letters 15 (reduced b 15 z))) :
    let k:=actualMode b z
    let X:=total (step^[15] (reduced b 15 z))/2^(b+1)
    let d:=X/2^(place b z)
    (crossing p k).read v=(if far b 15 z then cross d else false) ∧
      (far b 15 z → (signExpr p k).read v=(!(decide (2^b≤z.u)) && negative (oddBits (letters 15 (reduced b 15 z))))) := by
  dsimp only
  by_cases f : far b 15 z
  · obtain ⟨idx,side,active⟩:=modeKey b z f
    have fit : place b z<16 := by unfold place; have h:=wait_le 15 z.u; split <;> omega
    have val:=LeaveShadowRails.far_result b w z (small f) f odd room
    let X:=total (step^[15] (reduced b 15 z))/2^(b+1)
    let d:=X/2^(place b z)
    constructor
    · rw [crossing,active,if_pos rfl,Expr.read,idx,bits _ fit,if_pos f]
      change X.testBit (place b z)=cross d
      rw [Nat.testBit_eq_decide_div_mod_eq]
      change decide (d%2=1)=cross d
      have digit : d=(cross d).toNat+2*_ := val.1
      cases e : cross d <;> rw [e] at digit <;> simp only [Bool.toNat_false,Bool.toNat_true] at digit <;>
        apply Bool.eq_iff_iff.mpr <;> simp only [decide_eq_true_eq,Bool.false_eq_true,iff_false,iff_true] <;> omega
    · intro _
      rw [sign_value _ _ _ (by
        intro hs
        rw [side] at hs
        have h : z.u<2^b := by by_contra! hh;simp [hh] at hs
        have rails:=(LeaveShadowRails.rail b z (small f) f).2 h
        rw [par]
        have eq : reduced b 15 z=⟨z.u,(reduced b 15 z).v⟩:=SkywalkNat.State.ext rails.1 rfl
        have g:=rails.2.2
        rw [rails.1] at g
        rw [eq,lead_wait 15 _ _ g,idx,place,if_neg (Nat.not_le.mpr h)]) ,side,par]
  · simp [actualMode,farMode,ofFlags,enabled,crossing,Expr.read,f]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat IntegerHigh Shadow HighBankSum

theorem afterThreshold_shadow7 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (e:Nat) (en:e≤1) :
    let full:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    (2^b≤full.u-e ↔ 2^b≤r.u-e) ∧ (0<full.u ↔ 0<r.u) := by
  by_cases f : Shadow.far b 15 z
  · exact afterThreshold b z (small f) e en
  · simp [Shadow.reduced,f]

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat IntegerHigh Shadow HighBankSum

theorem limbGaps_shadow7 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) :
    let full:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    ∃a c:Nat,full.u=r.u+2^(b+1)*a ∧ full.v=r.v+2^(b+1)*c := by
  by_cases f : Shadow.far b 15 z
  · exact limbGaps b z (small f)
  · exact ⟨0, 0, by simp [Shadow.reduced,f], by simp [Shadow.reduced,f]⟩

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat IntegerHigh Shadow HighBankSum

theorem retainedLow_shadow7 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (sg:Bool) :
    let F:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    let e:=PortalValues.negative sg r.u
    let V:=2^(b+1)
    PortalValues.negative sg F.u=e ∧ (F.u+F.v)%V=(r.u+r.v)%V ∧ (F.u-e.toNat)%V=(r.u-e.toNat)%V := by
  by_cases f : Shadow.far b 15 z
  · exact retainedLow b z (small f) sg
  · simp [Shadow.reduced,f]

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails

namespace ECDSAAdd.Entrant.StairPacket.LeaveRestoreTruth
open SkywalkNat Shadow LeaveCompanion PortalValues
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

theorem truth_shadow7 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (sg:Bool) :
    let F:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    let e:=(negative sg r.u).toNat
    (decide (2^b≤r.u-e)=decide (2^b≤F.u-e)) ∧
      upperBorrow (2^b) r.u r.v e=upperBorrow (2^b) F.u F.v e ∧
      (F.u-e)%(2*2^b)=(r.u-e)%(2*2^b) ∧
      negative sg F.u=negative sg r.u := by
  by_cases f : Shadow.far b 15 z
  · exact truth b z (small f) sg
  · simp [Shadow.reduced,f]

end ECDSAAdd.Entrant.StairPacket.LeaveRestoreTruth

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat Shadow HighBankSum

theorem inputFit_shadow7 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (endSmall : Shadow7.EndSmall b z) :
    let a:=step^[15] (reduced b 15 z)
    min a.u a.v<2^b ∧ (a.u+a.v)/2^b<2^19 := by
  by_cases f : far b 15 z
  · exact inputFit b z (small f)
  · simp only [reduced,if_neg f]
    refine ⟨endSmall,?_⟩
    have upper : z.u+z.v < 3*limb b 15 :=
      (Nat.div_lt_iff_lt_mul (by unfold limb; positivity)).mp (Nat.lt_of_not_ge f)
    have noninc := iter_sum_nonincrease 15 z
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).mpr
    rw [scale,pow_succ] at upper
    omega

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails

namespace ECDSAAdd.Entrant.StairPacket.LeaveRestoreTruth
open SkywalkNat Shadow LeaveCompanion PortalValues
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

theorem restored_shadow7 (b k : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (endSmall : Shadow7.EndSmall b z) (sg:Bool) :
    let F:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    let e:=(negative sg r.u).toNat
    ((if 2^b≤r.u-e then ((F.u+F.v)/2^(b+1))%2^k else 0)+2^k-upperBorrow (2^b) r.u r.v e)%2^k =
      ((F.u-e)/2^(b+1))%2^k := by
  let F:=step^[15] z
  let r:=step^[15] (reduced b 15 z)
  let e:=(negative sg r.u).toNat
  have le:e≤1 := by cases h:negative sg r.u <;> simp [e,h]
  have eq:=truth_shadow7 b z small sg
  have pos:0<F.u ↔ 0<r.u := (LeaveShadowRails.afterThreshold_shadow7 b z small e le).2
  have eu:e≤F.u := by
    by_cases h:0<F.u
    · omega
    · have no:¬0<r.u:=fun hr=>h (pos.mpr hr)
      simp [e,negative,no]
  have sm:min F.u F.v<2^b := endSmall
  have out:=upper_restore (2^b) F.u F.v e (2^k) (Nat.two_pow_pos _) le eu sm (Nat.two_pow_pos _)
  have h:2^b≤r.u-e ↔ 2^b≤F.u-e := (LeaveShadowRails.afterThreshold_shadow7 b z small e le).1.symm
  have two : 2*2^b=2^(b+1) := (Nat.mul_comm _ _).trans (pow_succ 2 b).symm
  change ((if 2^b≤r.u-e then ((F.u+F.v)/2^(b+1))%2^k else 0)+2^k-upperBorrow (2^b) r.u r.v e)%2^k=_
  have bor : upperBorrow (2^b) r.u r.v e=upperBorrow (2^b) F.u F.v e := eq.2.1
  simp only [h,bor]
  simpa only [two] using out

end ECDSAAdd.Entrant.StairPacket.LeaveRestoreTruth

-- ===== ShadowEntryFacts =====
namespace ECDSAAdd.Entrant.StairPacket.Shadow
open SkywalkNat

theorem reduced_values_shadow7 (b k : Nat) (z:SkywalkNat.State) (sg:Bool) (small : Shadow7.SmallIfFar b k z) :
    let T:=reduced b k z
    let f:=far b k z
    let h:=limb b k
    let d:=if f then gap b k z else 0
    let lu:=decide (f ∧ 2^b≤z.u)
    T.u=z.u-(if lu then d else 0) ∧ (T.u+T.v=z.u+z.v-d) ∧ T.u+T.v<3*h ∧
    PortalValues.negative sg T.u=PortalValues.negative sg z.u ∧
    (T.u-(PortalValues.negative sg T.u).toNat)=
      (z.u-(PortalValues.negative sg z.u).toNat)-(if lu then d else 0) := by
  by_cases f : far b k z
  · exact reduced_values b k z sg (small f)
  · have hu : 0 < limb b k := by simp [limb]
    have lt : z.u+z.v < 3*limb b k := (Nat.div_lt_iff_lt_mul hu).mp (Nat.lt_of_not_ge f)
    simp [reduced,f,lt]

end ECDSAAdd.Entrant.StairPacket.Shadow

namespace ECDSAAdd.Entrant.StairPacket.Shadow
open EnterProof

theorem actual_residue_shadow7 (b k:Nat) (z:SkywalkNat.State) (sg:Bool) (small : Shadow7.SmallIfFar b k z) :
    let T:=reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative sg z.u
    (T.u+T.v)%V=(z.u+z.v)%V ∧ (T.u-e.toNat)%V=(z.u-e.toNat)%V := by
  by_cases f : far b k z
  · exact actual_residue b k z sg (small f)
  · simp [reduced,f]

end ECDSAAdd.Entrant.StairPacket.Shadow

namespace ECDSAAdd.Entrant.StairPacket.EnterProof


theorem shadow_digits_shadow7 (b k:Nat) (z:SkywalkNat.State) (sg:Bool) (small : Shadow7.SmallIfFar b k z) :
    let X:=z.u+z.v; let e:=PortalValues.negative sg z.u; let M:=z.u-e.toNat
    let V:=cutUnit b k; let A:=nibble X V; let B:=nibble M V
    let mode:=decide (Shadow.far b k z); let long:=decide (Shadow.far b k z ∧ 2^b≤z.u)
    let T:=Shadow.reduced b k z
    let AA:=nibble (T.u+T.v) V; let BB:=nibble (T.u-e.toNat) V
    updateA A mode=AA ∧ updateM A B mode long=BB ∧ AA<8 ∧ BB<8 := by
  dsimp only
  let V:=cutUnit b k
  let U:=Shadow.limb b k
  let T:=Shadow.reduced b k z
  let e:=PortalValues.negative sg z.u
  have vn:0<V:=by simp [V,cutUnit]
  have mul:2*V=U:=by simp [V,U,cutUnit,Shadow.limb,pow_succ,Nat.mul_comm]
  have limit:2^b≤V:=by unfold V cutUnit;apply Nat.pow_le_pow_right (by decide);omega
  have eu:e.toNat≤z.u:=by
    by_cases pos:0<z.u <;> cases sg <;> simp_all [e,PortalValues.negative];omega
  obtain ⟨tu,tx,hi,_sign,_tm⟩:=Shadow.reduced_values_shadow7 b k z sg small
  change T.u+T.v<3*U at hi
  have less (n:Nat) (h:n≤T.u+T.v):nibble n V<8:=by
    have div:n/V<8:=(Nat.div_lt_iff_lt_mul vn).mpr (by rw [←mul] at hi; omega)
    exact (Nat.mod_le _ _).trans_lt div
  have bound2:=less (T.u-e.toNat) (by omega)
  suffices parts:updateA (nibble (z.u+z.v) V) (decide (Shadow.far b k z))=nibble (T.u+T.v) V ∧
      updateM (nibble (z.u+z.v) V) (nibble (z.u-e.toNat) V) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u))=nibble (T.u-e.toNat) V by
    exact ⟨parts.1,parts.2,less _ (le_refl _),bound2⟩
  dsimp only [T]
  by_cases hf:Shadow.far b k z
  · have h:3≤(z.u+z.v)/(2*V):=mul ▸ hf
    have gap:Shadow.gap b k z=((z.u+z.v)/(2*V)-2)*(2*V):=by rw [mul];rfl
    by_cases hl:2^b≤z.u
    · let X:=z.u+z.v;let M:=z.u-e.toNat
      let w:=borrow (nibble X V) (nibble M V) true
      have bw:w≤1:=by unfold w borrow;cases _ && _ && _ <;> decide
      have rel:X/(2*V)=M/(2*V)+w:=by
        rw [show X=M+(z.v+e.toNat) by dsimp [X,M];omega]
        have add:z.v+e.toNat≤V := by
          change z.v+e.toNat≤V
          have hv:z.v<2^b:=by have hs := small hf; omega
          have ee:e.toNat≤1:=by cases e <;> decide
          omega
        have hh:=half_limb_borrow V M (z.v+e.toNat) vn add
        change (M+(z.v+e.toNat))/(2*V)=M/(2*V)+_ at hh
        change _=M/(2*V)+borrow (nibble X V) (nibble M V) true
        rw [borrowed _ _ _ vn,show X=M+(z.v+e.toNat) by dsimp [X,M];omega]
        exact hh
      have frame:=short_digits X M V w vn bw rel rfl h
      simp only [hf,hl,true_and,decide_true,ite_true] at tu tx _tm ⊢
      rw [gap] at tu tx _tm
      rw [_sign] at _tm
      change T.u+T.v=_ at tx
      change T.u-e.toNat=_ at _tm
      exact ⟨frame.1.trans (congrArg (fun q=>nibble q V) tx.symm),frame.2.trans (congrArg (fun q=>nibble q V) _tm.symm)⟩
    · have frame:=short_other (z.u+z.v) (z.u-e.toNat) V vn h
      simp only [hf,hl,true_and,decide_false,decide_true,ite_true] at tu tx ⊢
      rw [gap] at tx
      exact ⟨frame.1.trans (congrArg (fun q=>nibble q V) tx.symm),frame.2.trans (congrArg (fun q=>nibble (q-e.toNat) V) tu.symm)⟩
  · have dst:Shadow.reduced b k z=z:=by simp [Shadow.reduced,hf]
    simp only [hf,false_and,decide_false,dst]
    exact near_digits (z.u+z.v) (z.u-e.toNat) V

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof


theorem rows_shadow7 (b k:Nat) (z:SkywalkNat.State) (g sg:Bool) (small : Shadow7.SmallIfFar b k z) :
    initialRow b k z g sg<4096 ∧ result (initialRow b k z g sg)=shadowRow b k z g sg := by
  let V:=cutUnit b k
  let U:=Shadow.limb b k
  let e:=PortalValues.negative sg z.u
  let f:=decide (Shadow.far b k z)
  let u:=decide (Shadow.far b k z ∧ 2^b≤z.u)
  let T:=Shadow.reduced b k z
  let A:=nibble (z.u+z.v) V;let M:=nibble (z.u-e.toNat) V
  let A':=nibble (T.u+T.v) V;let M':=nibble (T.u-e.toNat) V
  have sh:=shape ⟨A,Nat.mod_lt _ (by decide)⟩ ⟨M,Nat.mod_lt _ (by decide)⟩ g e f u
  refine ⟨sh.1,sh.2.trans ?_⟩
  obtain ⟨dA,dM,a0,m0⟩:=shadow_digits_shadow7 b k z sg small
  change updateA A f=A' at dA
  change updateM A M f u=M' at dM
  change A'<8 at a0;change M'<8 at m0
  have top (j:Nat) (h:j<8):j.testBit 3=false:=Nat.testBit_lt_two_pow (by simpa only [show 2^3=8 by decide] using h)
  have signedTop : (signedNibble e M').testBit 3=e:=by
    cases e <;> simp [signedNibble,Nat.testBit_xor,top _ m0,show Nat.testBit 15 3=true by decide]
  have head:A/2=Shadow.high b k z%8:=by
    rw [show A=nibble (z.u+z.v) V by rfl,digit,show 2*V=U by simp [V,U,cutUnit,Shadow.limb,pow_succ,Nat.mul_comm]]
    rfl
  change expected A M g e f u=_
  unfold expected
  rw [dA,dM]
  dsimp only
  rw [top _ a0,signedTop,head]
  simp [shadowRow,f,u,e,T,V,A',M']

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 10000

theorem actual_shadow_shadow7 (map:Wire→Wire) (P:Program) (inv:Bool) (b k:Nat) (z:SkywalkNat.State)
    (g s:Bool) (small : Shadow7.SmallIfFar b k z)
    (injective:∀a c:Fin width,map a=map c→a=c) (emitted:P=renameProgram map (step inv))
    (origin:State) (tape:List Bool)
    (data:∀q∈wires (step inv),origin.basis (map q)=(rowBefore inv b k z g s).testBit q) :
    (run P tape origin).phase=origin.phase ∧
    (∀q∈wires (step inv),(run P tape origin).basis (map q)=(rowAfter inv b k z g s).testBit q) ∧
    ∀q∉wires P,(run P tape origin).basis q=origin.basis q := by
  have h:=rows_shadow7 b k z g s small
  let row:Fin 4096:=⟨initialRow b k z g s,h.1⟩
  have each (q:Wire) (hq:q∈wires (step inv)):origin.basis (map q)=(initial inv row).testBit q:=by
    cases inv <;> simpa [initial,row,h.2,rowBefore] using data q hq
  rw [emitted]
  have act:=apply_guard map inv row injective tape origin each
  refine ⟨act.1,?_,act.2.2⟩
  intro q hq
  have value:=act.2.1 q hq
  cases inv <;> simpa [finalValue,row,h.2,rowAfter] using value

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic RailPair
set_option maxRecDepth 12000

theorem short_rails_shadow7 {lo hi g n f u rs L net b k} {A:Aperture lo hi g n f u rs L net (b+k)}
    (P:Program) (place:WordPlacement A P) (z:SkywalkNat.State) (G S:Bool) (small : Shadow7.SmallIfFar b k z)
    (raw pre post:State)
    (cut:PackedCut lo hi g n f u (PortalValues.negative S z.u) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u)) (pullState net raw) pre)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (data:∀q∈wires forward,post.basis (rs.getD q 0)=(shadowRow b k z G S).testBit q)
    (outside:∀q∉wires P,post.basis q=pre.basis q) :
    let T:=Shadow.reduced b k z
    signedRegValue (place.lowA++A.a) post.basis=(SkywalkRails.encode G S T.u T.v).a ∧
    signedRegValue (place.lowB++A.b) post.basis=(SkywalkRails.encode G S T.u T.v).b := by
  let T:=Shadow.reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative S z.u
  let X:=T.u+T.v;let M:=T.u-e.toNat
  have num:=PortalValues.mathematical _ _ _ _ _ _ input
  have residue:=Shadow.actual_residue_shadow7 b k z S small
  obtain ⟨_,_,pos,neg,_⟩:=Shadow.reduced_values_shadow7 b k z S small
  change PortalValues.negative S T.u=e at neg
  change X<3*Shadow.limb b k at pos
  have limb:Shadow.limb b k=2*V:=by simp [Shadow.limb,V,cutUnit,pow_succ,Nat.mul_comm]
  rw [limb] at pos
  have pv:0<V:=by simp [V,cutUnit]
  have bounded (v:Nat) (h:v≤X):v/V<16:=(Nat.div_lt_iff_lt_mul pv).mpr (by omega)
  have Xbound:X<2^(b+k+3):=by rw [pow_add]; change X<V*8; omega
  have high:=output_values rs post.basis b k z G S place.portsCount data
  rw [place.aTop,place.bTop] at high
  have same (q:Wire) (h:q∈place.lowA++place.lowB):post.basis q=raw.basis (net q):=by
    obtain ⟨hp,hn,hf,hu,hh⟩:=place.protected0 q h
    exact (outside q hp).trans (cut.unchanged q hn hf hu hh)
  have valueLo (w full:List Wire) (sub:∀q∈w,q∈place.lowA++place.lowB)
      (shape:w.map net=full.take (b+k)) (size:b+k≤full.length) (flip:Bool) :
      regValue w (fun q=>post.basis q ^^ flip)=regValue full (fun q=>raw.basis q ^^ flip)%V:=by
    calc
      _=regValue w (fun q=>raw.basis (net q) ^^ flip):=regValue_congr _ _ _ (fun q h=>congrArg (· ^^ flip) (same q (sub q h)))
      _=regValue (w.map net) (fun q=>raw.basis q ^^ flip):=(PortalValues.unroute net w (fun q=>raw.basis q ^^ flip)).symm
      _=_:=by rw [shape,takeValue _ _ size];rfl
  have lowA (flag:Bool):=valueLo _ L.a (fun _ h=>List.mem_append_left _ h) place.xa (by have h:=A.na;omega) flag
  have lowB (flag:Bool):=valueLo _ L.b (fun _ h=>List.mem_append_right _ h) place.xb (by have h:=A.nb;omega) flag
  have ds:=high
  change regValue A.a post.basis=leftWord G e (nibble X V) (nibble M V) ∧
    regValue A.b post.basis=rightWord G e (nibble X V) (nibble M V) ∧ _ at ds
  have ybound:T.u≤X:=by simp [X]
  have mbound:M≤X:=Nat.le_trans (Nat.sub_le _ _) ybound
  obtain ⟨_,_,wpos,wmag⟩:=num
  change X%V=(z.u+z.v)%V ∧ M%V=(z.u-e.toNat)%V at residue
  have la:(place.lowA++A.a).length=(b+k+3)+1:=by simp [place.al,A.spec.a]
  have lb:(place.lowB++A.b).length=(b+k+3)+1:=by simp [place.bl,A.spec.b]
  cases G
  · have pl:regValue place.lowA post.basis=X%V:=by
      have v:=lowA false
      simpa only [Bool.xor_false,show regValue L.a raw.basis=z.u+z.v from wpos,←residue.1] using v
    have ml:regValue place.lowB (fun q=>post.basis q ^^ e)=M%V:=by
      rw [lowB e,show regValue L.b (fun q=>raw.basis q ^^ e)=z.u-e.toNat from wmag,←residue.2]
    have px:=join _ _ _ X _ place.al pl ds.1 (bounded _ (le_refl _))
    have mh:=norm_nibble _ A.spec.b _ e _ ds.2.1
    have py:=join _ _ _ M _ place.bl ml mh (bounded _ mbound)
    dsimp only [M] at py
    rw [←neg] at py
    exact ⟨ordinary _ _ la _ X Xbound px,signed _ _ lb _ _ S (lt_of_le_of_lt ybound Xbound) py⟩
  · have pl:regValue place.lowB post.basis=X%V:=by
      have v:=lowB false
      simpa only [Bool.xor_false,show regValue L.b raw.basis=z.u+z.v from wpos,←residue.1] using v
    have ml:regValue place.lowA (fun q=>post.basis q ^^ e)=M%V:=by
      rw [lowA e,show regValue L.a (fun q=>raw.basis q ^^ e)=z.u-e.toNat from wmag,←residue.2]
    have px:=join _ _ _ X _ place.bl pl ds.2.1 (bounded _ (le_refl _))
    have mh:=norm_nibble _ A.spec.a _ e _ ds.1
    have py:=join _ _ _ M _ place.al ml mh (bounded _ mbound)
    dsimp only [M] at py
    rw [←neg] at py
    exact ⟨signed _ _ la _ _ S (lt_of_le_of_lt ybound Xbound) py,ordinary _ _ lb _ X Xbound px⟩

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic MappedCompressed RailPair IntegerPacket
set_option maxRecDepth 16000

structure FramePorts_shadow7 {lo hi g n f u rs L net b k P} {A:Aperture lo hi g n f u rs L net (b+k)}
    (place:WordPlacement A P) (j:Fin 23) : Prop where
  a : ((ports (Shadow7.shape j) 0).a.map (windowNet j))=place.lowA++A.a
  bSites : ((ports (Shadow7.shape j) 0).b.map (windowNet j))=place.lowB++A.b
  prev : windowNet j (ports (Shadow7.shape j) 0).previous=rs.getD 8 0
  carry : ∀q∈(ports (Shadow7.shape j) 0).carry,let v:=windowNet j q
    v∈rs.drop 15 ∨ (v∉wires P ∧ net v∈L.carry ∧ v≠n ∧ v≠f ∧ v≠u ∧ v∉sites hi)
  ext : ∀r:Fin 15,let q:=windowNet j (ports (Shadow7.shape j) r).ext
    q∉wires P ∧ q∈hi.map Prod.fst
  hist : ∀r:Fin 15,let q:=windowNet j (ports (Shadow7.shape j) r).history
    q∉wires P ∧ q≠n ∧ q≠f ∧ q≠u ∧ q∉sites hi

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic MappedCompressed RailPair IntegerPacket
set_option maxRecDepth 16000

theorem complete_shadow7 {lo hi g n f u rs L net b k P} {A:Aperture lo hi g n f u rs L net (b+k)}
    {place:WordPlacement A P} {j:Fin 23} (frame:FramePorts_shadow7 place j)
    (z:SkywalkNat.State) (G S:Bool) (small : Shadow7.SmallIfFar b k z)
    (raw pre post:State)
    (cut:PackedCut lo hi g n f u (PortalValues.negative S z.u) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u)) (pullState net raw) pre)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (data:∀q∈wires forward,post.basis (rs.getD q 0)=(shadowRow b k z G S).testBit q)
    (save:∀q∉wires P,post.basis q=pre.basis q)
    (history:∀r:Fin 15,raw.basis (net (windowNet j (ports (Shadow7.shape j) r).history))=false) :
    let T:=Shadow.reduced b k z
    Shadow7.onRails j 0 (SkywalkRails.encode G S T.u T.v) post.basis := by
  let T:=Shadow.reduced b k z
  let Z:=SkywalkRails.encode G S T.u T.v
  have values:=short_rails_shadow7 P place z G S small raw pre post cut input data save
  have move (qs:List Wire):signedRegValue qs (mappedBasis j post.basis)=signedRegValue (qs.map (windowNet j)) post.basis:=by
    simp only [signedRegValue,List.length_map,PortalValues.unroute]
    rfl
  have gval:=actual_tags rs post.basis b k z G S data
  have sc:=output_values rs post.basis b k z G S place.portsCount data
  have clean:= (regValue_zero _ _).mp sc.2.2
  have retain (q:Wire) (no:q∉wires P) (n0:q≠n) (f0:q≠f) (u0:q≠u) (hi0:q∉sites hi):
      post.basis q=raw.basis (net q):=(save _ no).trans (cut.unchanged _ n0 f0 u0 hi0)
  refine ⟨(move _).trans (frame.a ▸ values.1),(move _).trans (frame.bSites ▸ values.2),?_,?_,?_⟩
  · change post.basis (windowNet j (ports (Shadow7.shape j) 0).previous)=Z.g
    rw [frame.prev,gval.1];cases G <;> rfl
  · apply (regValue_zero _ _).mpr
    intro q hq
    rcases frame.carry q hq with hs|⟨no,qc,n0,f0,u0,hi0⟩
    · exact clean _ hs
    · exact (retain _ no n0 f0 u0 hi0).trans ((regValue_zero _ _).mp input.2.2.2.2.2 _ qc)
  · intro r _ lt
    have bound:r<15:=lt
    let i:Fin 15:=⟨r,bound⟩
    obtain ⟨no,mem⟩:=frame.ext i
    obtain ⟨p,hp,eq⟩:=List.mem_map.mp mem
    obtain ⟨nh,h0,h1,h2,hr⟩:=frame.hist i
    refine ⟨(save _ no).trans (eq ▸ (cut.upper _ hp).1),(retain _ nh h0 h1 h2 hr).trans ?_⟩
    exact history i

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

theorem return_packed_shadow7 {lo hi g n f u rs L net b k} (A:Aperture lo hi g n f u rs L net (b+k))
    (map:Wire→Wire) (p r:Program) (inj:∀a c:Fin width,map a=map c→a=c)
    (map_eq:∀q:Wire,map q=rs.getD q 0) (sz:rs.length=width)
    (pf:p=renameProgram map forward) (pr:r=renameProgram map backward)
    (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (small : Shadow7.SmallIfFar b k z)
    (h:PackedCut lo hi g n f u (PortalValues.negative S z.u) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u)) (pullState net raw) cut)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (m t:List Bool) : run r t (run p m cut)=cut := by
  have sup : wires forward=wires backward := by decide +kernel
  have lim:wires forward ⊆ Finset.range width := by apply ArchiveFieldScratch.bounded;decide +kernel
  have src:=read_packed A raw cut z G S h input
  have initial (q:Wire) (hq:q∈wires forward):cut.basis (map q)=(initialRow b k z G S).testBit q:=by
    rw [map_eq]
    have hv:=bitAt rs cut.basis q (sz ▸ Finset.mem_range.mp (lim hq))
    rwa [src] at hv
  have first:=actual_shadow_shadow7 map p false b k z G S small inj pf cut m initial
  have last:=actual_shadow_shadow7 map r true b k z G S small inj pr (run p m cut) t
    (fun q hq=>first.2.1 q (sup ▸ hq))
  apply congrArg₂ State.mk (last.1.trans first.1)
  funext q
  have pp:wires p=(wires forward).image map:=pf ▸ JointForward1588.wires_rename_image _ _
  have rr:wires r=wires p:=by rw [pr,JointForward1588.wires_rename_image,←sup,pp]
  by_cases mem:q∈wires p
  · obtain ⟨v,vh,rfl⟩:=Finset.mem_image.mp (pp ▸ mem)
    exact (last.2.1 _ (sup ▸ vh)).trans (initial _ vh).symm
  · exact (last.2.2 q (rr ▸ mem)).trans (first.2.2 _ mem)

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem scanRouted_shadow7 (j : Fin 23) (k a b g n : Nat) (ps : List (Wire×Wire))
    (loc : RailPair.ScanGeometry a b g n ps)
    (left : ps.map Prod.fst = ((IntegerPacket.ports (Shadow7.shape j) 15).a.drop k).map (windowNet j))
    (right : ps.map Prod.snd = ((IntegerPacket.ports (Shadow7.shape j) 15).b.drop k).map (windowNet j))
    (aTop : a=windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).aSign)
    (bTop : b=windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).bSign)
    (prev : g=windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).previous)
    (s : State) (m : List Bool) (u v : Nat) (G S : Bool)
    (h : Shadow7.onRails j 15 (SkywalkRails.encode G S u v) s.basis) (fresh:s.basis n=false)
    (la : k≤(IntegerPacket.ports (Shadow7.shape j) 15).a.length) (lb : k≤(IntegerPacket.ports (Shadow7.shape j) 15).b.length) :
    let t:=run (RailPair.scan a b g n ps) m s
    let e:=negative S u
    t.basis n=e ∧ regValue (ps.map Prod.fst) t.basis=(u+v)/2^k ∧
      regValue (ps.map Prod.snd) t.basis=(u-e.toNat)/2^k := by
  let L:=IntegerPacket.ports (Shadow7.shape j) 15
  let e:=negative S u
  have gh : mappedBasis j s.basis L.previous=G := by
    have eq := h.2.2.1
    cases G <;> exact eq
  have math := signedWords L G S u v (mappedBasis j s.basis) h.1 h.2.1 gh
  have gg:s.basis g=G := prev ▸ gh
  have ss:(s.basis a ^^ s.basis b)=e := by rw [aTop,bTop];exact math.2.1
  have act:=RailPair.scan_run _ _ _ _ _ loc s m fresh
  have vals:=scan_values _ _ _ _ _ loc s m fresh
  dsimp only at vals ⊢
  refine ⟨act.2.1.trans ss,?_⟩
  rw [gg,ss] at vals
  rw [left,right] at vals ⊢
  simp only [unroute,shiftedValue,la,lb] at vals ⊢
  obtain ⟨pos,mag⟩:=math.2.2
  cases G <;> simp only [wordPos,wordSigned,ite_true,Bool.false_eq_true,ite_false] at pos mag vals
  all_goals
    exact ⟨vals.1.trans (congrArg (· /2^k) pos),vals.2.trans (congrArg (· /2^k) mag)⟩

end ECDSAAdd.Entrant.StairPacket.PortalValues

-- ===== ShadowPortal90 =====
namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def thresholdPairs : List (Wire×Wire) := [(328, 1558), (329, 1559), (330, 1560), (331, 1561), (332, 1562), (333, 1563), (334, 1564), (335, 1565), (336, 1566), (337, 1567), (338, 1568), (339, 1569), (340, 1570), (341, 1571), (342, 1572), (343, 1573), (344, 1574), (345, 1575), (346, 1576), (347, 1577), (348, 1578), (349, 1579), (350, 1580), (351, 1581), (352, 1582), (353, 1583), (354, 1584), (355, 1585), (356, 1586), (357, 1587), (358, 1588), (359, 1589), (360, 1590), (361, 1591), (362, 1592), (363, 1593)]
def threshold := latch true none 1556 1557 thresholdPairs
theorem threshold_layout : (1556::1557::sites thresholdPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem threshold_slice : (((Shadow7.portalP 90)).drop 155).take 148=threshold := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
def orientationPairs : List (Wire×Wire) := [(1007, 1556), (1008, 1557), (1009, 1558), (1010, 1559), (1011, 1560), (1012, 1561), (1013, 1562), (1014, 1563), (1015, 1564), (1016, 1565), (1017, 1566), (1018, 1567), (1019, 1568), (1020, 1569), (1021, 1570), (1022, 1571), (1023, 1572), (1024, 1573), (1025, 1574), (1026, 1575), (1027, 1576), (1028, 1577), (1029, 1578), (1030, 1579), (1031, 1580), (1032, 1581), (1033, 1582), (1034, 1583), (1035, 1584), (1036, 1585), (1037, 1586), (1038, 1587), (1039, 1588), (1040, 1589), (1041, 1590), (1042, 1591), (1043, 1592)]
def orientation := latch false (some 1781) 1782 1006 orientationPairs
theorem orientation_layout : (1782::1006::sites orientationPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_slice : (((Shadow7.portalP 90)).drop 306).take 152=orientation := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_enable : 1781∉1782::1006::sites orientationPairs := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
def railA : List Wire := [326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363]
def railB : List Wire := [1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043]
def carry : List Wire := [1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590]
def bulkA := railA.drop 3
def bulkB := railB.drop 3
def scan : Program := [.CX 363 1783,.CX 1043 1783] ++
  RailPair.exchange 105 (railA.zip railB) ++ signComplement 1783 railB
def flags : Program := [.CCX 326 327 1557] ++ threshold ++
  [.measureX 1557 [] [.CZ 326 327],.CX 1556 1781,.CX 1781 1556] ++ orientation
def erase : Program := [.X 328,.CCX 1008 328 1556] ++
  Companion.erase bulkA bulkB carry 1782 1556 ++
  [.measureX 1556 [] [.CZ 1008 328],.X 328]
def store : Program := RailPair.transfer false (bulkA.zip bulkB) ++
  signComplement 1783 (railB.take 3) ++ RailPair.exchange 105 ((railA.take 3).zip (railB.take 3))
theorem emitted : (Shadow7.portalP 90)=scan++flags++erase++store := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem exchange_good : (105::RailPair.sites (railA.zip railB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem complement_good : railB.Nodup ∧ 1783∉railB := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem move_good : (RailPair.sites (bulkA.zip bulkB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem copy_good : Companion.Geometry bulkA bulkB carry 1782 1556 := by
  constructor <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def backFlags := PortalAnd.flagsBack 326 327 1557 1556 1781 1782 1006 thresholdPairs orientationPairs
def backErase := PortalBorrow.wrap 328 1008 1556 (PortalBorrow.restore bulkA bulkB carry 1782 1556)
theorem emitted_back : (Shadow7.portalInvP 90)=store.reverse++backErase++backFlags++scan.reverse := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem flags_spec : flags=PortalAnd.flags 326 327 1557 1556 1781 1782 1006 thresholdPairs orientationPairs := by rfl
theorem erase_spec : erase=PortalBorrow.wrap 328 1008 1556 (Companion.erase bulkA bulkB carry 1782 1556) := by rfl
theorem scan_proper : ProperProgram scan := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem store_proper : ProperProgram store := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
def activeScratch : List Wire := [1557,1556,1781,1782,1556]++thresholdPairs.map Prod.snd++orientationPairs.map Prod.snd++carry
end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
theorem away_scan : ∀q∈activeScratch,q∉wires scan := PortalStatic.separated _ _ 1783 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem flags_do (s:State) (m:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    let f:=PortalAnd.high 326 327 thresholdPairs s.basis
    let u:=f && (PortalAnd.digits 1006 orientationPairs).any s.basis
    run flags m s=⟨s.phase,writeBit (writeBit s.basis 1781 f) 1782 u⟩ := by
  rw [flags_spec]
  apply PortalAnd.flags_run
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · decide
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem flags_return (s:State) (m n:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run backFlags n (run flags m s)=s := by
  rw [flags_spec]
  apply PortalAnd.flags_undo
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · decide
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem erase_return (s:State) (m n:List Bool) (h:s.basis 1556=false ∧ ∀q∈carry,s.basis q=false) :
    run backErase n (run erase m s)=s := by
  rw [erase_spec]
  apply PortalBorrow.erase_undo
  · exact copy_good
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · exact PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h.1
  · exact h.2
theorem portal_return (s:State) (m tape:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run (Shadow7.portalInvP 90) tape (run (Shadow7.portalP 90) m s)=s := by
  let v:=run scan m s
  have vh:∀q∈activeScratch,v.basis q=false:=fun q hp=>(run_preserves_outside _ _ _ _ (away_scan _ hp)).trans (h _ hp)
  have hc (m0:List Bool) : (run flags m0 v).basis 1556=false ∧ ∀q∈carry,(run flags m0 v).basis q=false := by
    rw [flags_do v m0 vh]
    have dis: ∀q∈carry,q≠1781 ∧ q≠1782 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    constructor
    · simpa [writeBit] using vh 1556 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
    · intro q hq; simp [writeBit,(dis _ hq).1,(dis _ hq).2,vh q (by simp [activeScratch,hq])]
  rw [emitted,emitted_back]
  simp only [run_append,run_take]
  rw [run_reverse_proper _ store_proper,erase_return _ _ _ (hc _),flags_return _ _ _ vh,run_reverse_proper _ scan_proper]

end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
def pairs := railA.zip railB
theorem source : Source (W.compactSkywalkTickLayout base 90) (OB5.sig 89) 220 363 1043 105 pairs := by constructor <;> decide +kernel
theorem geom : RailPair.ScanGeometry 363 1043 105 1783 pairs := by constructor <;> decide +kernel
theorem scan_shape : scan=RailPair.scan 363 1043 105 1783 pairs := by decide +kernel
theorem scan_real (d:Bool) (x p:Nat) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256) (hq:p+2^32≤2^256)
    (hx:x<p) (hc:x.Coprime p) (s:State) (m:List Bool) (h:Rolling1588.Integer.Stage base d x p 90 s.basis) :
    let z:=SkywalkNat.step^[90] (SkywalkNat.init x p)
    let v:=run scan m (pullState (OB5.sig 89) s)
    ∃g sg:Bool,v.basis 1783=negative sg z.u ∧ v.basis 105=g ∧ regValue railA v.basis=(z.u+z.v)/2^220 ∧
      regValue railB v.basis=(z.u-(negative sg z.u).toNat)/2^220 := by
  obtain ⟨route,sg,inp⟩:=real_input d x p 90 hp0 hx0 hpo hp hq hx hc (by decide) s h
  have clean: (pullState (OB5.sig 89) s).basis 1783=false := by
    apply (regValue_zero _ _).mp inp.2.2.2.2.2 (OB5.sig 89 1783)
    decide +kernel
  have v:=scan_input _ _ _ _ _ _ _ _ source geom s m _ _ _ _ inp clean
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at v
  exact ⟨route,sg,v⟩

end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

theorem flags_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 3*2^220 ≤ u+v → min u v < 2^204) (scratch:∀k∈activeScratch,q.basis k=false)
    (x:regValue railA q.basis=(u+v)/2^220) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^220) :
    let far:=decide (3*2^220≤u+v)
    let long:=decide (3*2^220≤u+v ∧ 2^204≤u)
    run flags m q=⟨q.phase,writeBit (writeBit q.basis 1781 far) 1782 long⟩ := by
  have act:=PortalValues.actual_flags_shadow7 326 327 thresholdPairs orientationPairs 1006 railA railB
    (by decide +kernel) (by decide +kernel) q.basis (2^220) (2^204) u v (negative sg u).toNat
    (by decide) (by decide) small (by cases negative sg u <;> decide) x y
  rw [flags_do q m scratch]
  rw [act.2,act.1]

theorem erase_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 3*2^220 ≤ u+v → min u v < 2^204) (fresh:q.basis 1556=false ∧ ∀w∈carry,q.basis w=false)
    (x:regValue railA q.basis=(u+v)/2^220) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^220)
    (mode:q.basis 1782=decide (3*2^220≤u+v ∧ 2^204≤u)) :
    let r:=run erase m q
    r.phase=q.phase ∧ (∀w,w∉bulkB → r.basis w=q.basis w) ∧ regValue bulkB r.basis=0 := by
  rw [erase_spec]
  apply PortalBorrow.erase_run
  · exact copy_good
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact fresh.1
  · exact fresh.2
  · apply PortalValues.input_eq_shadow7 326 327 328 1006 1007 1008 1782 bulkA bulkB q.basis (2^220) (2^204) u v (negative sg u).toNat
    · decide
    · decide
    · exact small
    · cases negative sg u <;> decide
    · by_cases pos:0<u <;> cases sg <;> simp_all [negative]; omega
    · exact x
    · exact y
    · exact mode
    · decide +kernel


end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def loPairs := (railA.take 3).zip (railB.take 3)
def hiPairs := bulkA.zip bulkB
theorem pair_split : pairs=loPairs++hiPairs := by decide +kernel
theorem store_shape : store=RailPair.store 105 1783 loPairs hiPairs := by decide +kernel
theorem hi_y : hiPairs.map Prod.snd=bulkB := by decide +kernel
theorem noOverlap : ∀p∈hiPairs,p.1∉hiPairs.map Prod.snd := by decide +kernel
theorem bankLayout : CutLayout loPairs hiPairs 105 1783 1781 1782 := by constructor <;> first | constructor <;> decide +kernel | decide +kernel
theorem pot : ∀w∈railA++railB,w≠1781 ∧ w≠1782 := by decide +kernel
theorem carry_apart : ∀w∈carry,w≠1781 ∧ w≠1782 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

/-- The real physical portal applied to the genuine rolling secp trajectory leaves
all ordinary exterior bits alone, clears the redundant upper rail, parks the
positive upper word, and produces its actual arithmetic predicates. -/
theorem clean_for (raw:State) (z:SkywalkNat.State) (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 90) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    ∀q∈activeScratch,(pullState (OB5.sig 89) raw).basis q=false:=by
  have pool : ∀q∈activeScratch,OB5.sig 89 q∈(W.compactSkywalkTickLayout base 90).carry := by decide +kernel
  exact fun q hq=>(regValue_zero _ _).mp record.2.2.2.2.2 _ (pool _ hq)
theorem physical_frame_local (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 204 15 z) (raw:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 90) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let origin:=pullState (OB5.sig 89) raw
    PackedCut loPairs hiPairs 105 1783 1781 1782 (negative sg z.u)
      (decide (3*2^220≤z.u+z.v)) (decide (3*2^220≤z.u+z.v ∧ 2^204≤z.u))
      origin (run (Shadow7.portalP 90) m origin) := by
  let origin:=pullState (OB5.sig 89) raw
  let v:=run scan m origin
  let t1:=m.drop (measurementCount scan)
  let w:=run flags t1 v
  let t2:=m.drop (measurementCount (scan++flags))
  let x:=run erase t2 w
  let t3:=m.drop (measurementCount (scan++flags++erase))
  let far:=decide (3*2^220≤z.u+z.v)
  let long:=decide (3*2^220≤z.u+z.v ∧ 2^204≤z.u)
  have short : 3*2^220 ≤ z.u+z.v → min z.u z.v < 2^204 := by
    intro f
    exact small ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr f)
  have clean:=clean_for raw z route sg record
  have vs:∀q∈activeScratch,v.basis q=false:=fun q mem=>(run_preserves_outside _ m origin q (away_scan _ mem)).trans (clean q mem)
  have fresh:origin.basis 1783=false:=by
    apply (regValue_zero _ _).mp record.2.2.2.2.2 (OB5.sig 89 1783)
    decide +kernel
  have first:=scan_input _ _ _ _ _ _ _ _ source geom raw m _ _ route sg record fresh
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at first
  obtain ⟨neg,_g,left,right⟩:=first
  have wf:w=⟨v.phase,writeBit (writeBit v.basis 1781 far) 1782 long⟩:=flags_values v t1 _ _ sg short vs left right
  have keep (q:Wire) (qf:q≠1781) (qu:q≠1782):w.basis q=v.basis q:=by rw [wf];simp [writeBit,qf,qu]
  have cv:w.basis 1556=false ∧ ∀q∈carry,w.basis q=false := by
    refine ⟨(keep _ (by decide) (by decide)).trans (vs _ (by decide +kernel)),?_⟩
    intro q hq
    exact (keep q (carry_apart _ hq).1 (carry_apart _ hq).2).trans (vs _ (by simp [activeScratch,hq]))
  have vals (r:List Wire) (sub:∀q∈r,q∈railA++railB):regValue r w.basis=regValue r v.basis:=
    regValue_congr _ _ _ (fun q h=>keep _ (pot _ (sub q h)).1 (pot _ (sub q h)).2)
  have xe:=erase_values w t2 _ _ sg short cv
    ((vals _ (fun _ h=>List.mem_append_left _ h)).trans left)
    ((vals _ (fun _ h=>List.mem_append_right _ h)).trans right) (by rw [wf];simp [long,writeBit])
  have scanned:=scan_run 363 1043 105 1783 pairs geom origin m fresh
  rw [←scan_shape] at scanned
  have sign:(origin.basis 363 ^^ origin.basis 1043)=negative sg z.u:=scanned.2.1.symm.trans neg
  rw [sign,pair_split] at scanned
  have clearHi:∀p∈hiPairs,x.basis p.2=false:=by
    intro p hp
    have hy:p.2∈hiPairs.map Prod.snd:=List.mem_map.mpr ⟨p,hp,rfl⟩
    exact (regValue_zero _ _).mp xe.2.2 p.2 (hi_y ▸ hy)
  have stored:=store_run 105 1783 loPairs hiPairs bankLayout.store x t3 clearHi
  rw [←store_shape] at stored
  rw [emitted]
  simp only [run_append,run_take]
  apply packed loPairs hiPairs 105 1783 1781 1782 _ far long origin v w x (run store t3 x)
    bankLayout scanned.1 neg scanned.2.2.1 scanned.2.2.2 wf
  · rw [hi_y];exact xe
  · exact stored.1
  · exact stored.2.1
  · exact stored.2.2.1
  · exact stored.2.2.2
  · exact noOverlap
theorem physical_frame_for (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (h:Rolling1588.Integer.Stage base d seed p 90 raw.basis)
    (route sg:Bool)
    (record:let z:=SkywalkNat.step^[90] (SkywalkNat.init seed p)
      SkywalkIntegerInput (W.compactSkywalkTickLayout base 90) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let z:=SkywalkNat.step^[90] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 89) raw
    PackedCut loPairs hiPairs 105 1783 1781 1782 (negative sg z.u)
      (decide (3*2^220≤z.u+z.v)) (decide (3*2^220≤z.u+z.v ∧ 2^204≤z.u))
      origin (run (Shadow7.portalP 90) m origin) := by
  have _input:=original_input d seed p 90 hp0 hx0 hpo hp hq hx hc (by decide) raw h
  exact physical_frame_local _ (Shadow7.Envelope.inputs seed p 90 (by omega) hp (by decide)).1 raw m route sg record
theorem physical_frame (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (h:Rolling1588.Integer.Stage base d seed p 90 raw.basis) :
    let z:=SkywalkNat.step^[90] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 89) raw
    ∃sg:Bool,PackedCut loPairs hiPairs 105 1783 1781 1782 (negative sg z.u)
      (decide (3*2^220≤z.u+z.v)) (decide (3*2^220≤z.u+z.v ∧ 2^204≤z.u))
      origin (run (Shadow7.portalP 90) m origin) := by
  obtain ⟨route,sg,input⟩:=real_input d seed p 90 hp0 hx0 hpo hp hq hx hc (by decide) raw h
  exact ⟨sg,physical_frame_for d seed p hp0 hx0 hpo hp hq hx hc raw m h route sg input⟩

end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

-- ===== ShadowPortal390 =====
namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def thresholdPairs : List (Wire×Wire) := [(478, 1558), (479, 1559), (480, 1560), (481, 1561), (482, 1562), (483, 1563), (484, 1564), (485, 1565), (486, 1566), (487, 1567), (488, 1568), (489, 1569), (490, 1570), (491, 1571), (492, 1572), (493, 1573), (494, 1574), (495, 1575), (496, 1576), (497, 1577), (498, 1578), (499, 1579), (500, 1580), (501, 1581), (502, 1582), (503, 1583), (504, 1584), (505, 1585), (506, 1586), (507, 1587), (508, 1588), (509, 1589), (510, 1590), (511, 1591), (512, 1592), (513, 1593), (514, 1594), (515, 1595), (516, 1596), (517, 1597), (518, 1598), (519, 1599), (520, 1600), (521, 1601), (522, 1602), (523, 1603), (524, 1604), (525, 1605), (526, 1606), (527, 1607), (528, 1608)]
def threshold := latch true none 1556 1557 thresholdPairs
theorem threshold_layout : (1556::1557::sites thresholdPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem threshold_slice : (((Shadow7.portalP 390)).drop 215).take 208=threshold := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
def orientationPairs : List (Wire×Wire) := [(857, 1556), (858, 1557), (859, 1558), (860, 1559), (861, 1560), (862, 1561), (863, 1562), (864, 1563), (865, 1564), (866, 1565), (867, 1566), (868, 1567), (869, 1568), (870, 1569), (871, 1570), (872, 1571), (873, 1572), (874, 1573), (875, 1574), (876, 1575), (877, 1576), (878, 1577), (879, 1578), (880, 1579), (881, 1580), (882, 1581), (883, 1582), (884, 1583), (885, 1584), (886, 1585), (887, 1586), (888, 1587), (889, 1588), (890, 1589), (891, 1590), (892, 1591), (893, 1592), (894, 1593), (895, 1594), (896, 1595), (897, 1596), (898, 1597), (899, 1598), (900, 1599), (901, 1600), (902, 1601), (903, 1602), (904, 1603), (905, 1604), (906, 1605), (907, 1606), (908, 1607)]
def orientation := latch false (some 1631) 1632 856 orientationPairs
theorem orientation_layout : (1632::856::sites orientationPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_slice : (((Shadow7.portalP 390)).drop 426).take 212=orientation := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_enable : 1631∉1632::856::sites orientationPairs := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
def railA : List Wire := [476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528]
def railB : List Wire := [856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908]
def carry : List Wire := [1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605]
def bulkA := railA.drop 3
def bulkB := railB.drop 3
def scan : Program := [.CX 528 1633,.CX 908 1633] ++
  RailPair.exchange 405 (railA.zip railB) ++ signComplement 1633 railB
def flags : Program := [.CCX 476 477 1557] ++ threshold ++
  [.measureX 1557 [] [.CZ 476 477],.CX 1556 1631,.CX 1631 1556] ++ orientation
def erase : Program := [.X 478,.CCX 858 478 1556] ++
  Companion.erase bulkA bulkB carry 1632 1556 ++
  [.measureX 1556 [] [.CZ 858 478],.X 478]
def store : Program := RailPair.transfer false (bulkA.zip bulkB) ++
  signComplement 1633 (railB.take 3) ++ RailPair.exchange 405 ((railA.take 3).zip (railB.take 3))
theorem emitted : (Shadow7.portalP 390)=scan++flags++erase++store := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem exchange_good : (405::RailPair.sites (railA.zip railB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem complement_good : railB.Nodup ∧ 1633∉railB := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem move_good : (RailPair.sites (bulkA.zip bulkB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem copy_good : Companion.Geometry bulkA bulkB carry 1632 1556 := by
  constructor <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def backFlags := PortalAnd.flagsBack 476 477 1557 1556 1631 1632 856 thresholdPairs orientationPairs
def backErase := PortalBorrow.wrap 478 858 1556 (PortalBorrow.restore bulkA bulkB carry 1632 1556)
theorem emitted_back : (Shadow7.portalInvP 390)=store.reverse++backErase++backFlags++scan.reverse := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem flags_spec : flags=PortalAnd.flags 476 477 1557 1556 1631 1632 856 thresholdPairs orientationPairs := by rfl
theorem erase_spec : erase=PortalBorrow.wrap 478 858 1556 (Companion.erase bulkA bulkB carry 1632 1556) := by rfl
theorem scan_proper : ProperProgram scan := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem store_proper : ProperProgram store := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
def activeScratch : List Wire := [1557,1556,1631,1632,1556]++thresholdPairs.map Prod.snd++orientationPairs.map Prod.snd++carry
end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
theorem away_scan : ∀q∈activeScratch,q∉wires scan := PortalStatic.separated _ _ 1633 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem flags_do (s:State) (m:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    let f:=PortalAnd.high 476 477 thresholdPairs s.basis
    let u:=f && (PortalAnd.digits 856 orientationPairs).any s.basis
    run flags m s=⟨s.phase,writeBit (writeBit s.basis 1631 f) 1632 u⟩ := by
  rw [flags_spec]
  apply PortalAnd.flags_run
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · decide
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem flags_return (s:State) (m n:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run backFlags n (run flags m s)=s := by
  rw [flags_spec]
  apply PortalAnd.flags_undo
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · decide
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem erase_return (s:State) (m n:List Bool) (h:s.basis 1556=false ∧ ∀q∈carry,s.basis q=false) :
    run backErase n (run erase m s)=s := by
  rw [erase_spec]
  apply PortalBorrow.erase_undo
  · exact copy_good
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · exact PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h.1
  · exact h.2
theorem portal_return (s:State) (m tape:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run (Shadow7.portalInvP 390) tape (run (Shadow7.portalP 390) m s)=s := by
  let v:=run scan m s
  have vh:∀q∈activeScratch,v.basis q=false:=fun q hp=>(run_preserves_outside _ _ _ _ (away_scan _ hp)).trans (h _ hp)
  have hc (m0:List Bool) : (run flags m0 v).basis 1556=false ∧ ∀q∈carry,(run flags m0 v).basis q=false := by
    rw [flags_do v m0 vh]
    have dis: ∀q∈carry,q≠1631 ∧ q≠1632 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    constructor
    · simpa [writeBit] using vh 1556 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
    · intro q hq; simp [writeBit,(dis _ hq).1,(dis _ hq).2,vh q (by simp [activeScratch,hq])]
  rw [emitted,emitted_back]
  simp only [run_append,run_take]
  rw [run_reverse_proper _ store_proper,erase_return _ _ _ (hc _),flags_return _ _ _ vh,run_reverse_proper _ scan_proper]

end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
def pairs := railA.zip railB
theorem source : Source (W.compactSkywalkTickLayout base 390) (OB5.sig 389) 70 528 908 405 pairs := by constructor <;> decide +kernel
theorem geom : RailPair.ScanGeometry 528 908 405 1633 pairs := by constructor <;> decide +kernel
theorem scan_shape : scan=RailPair.scan 528 908 405 1633 pairs := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

theorem flags_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 3*2^70 ≤ u+v → min u v < 2^54) (scratch:∀k∈activeScratch,q.basis k=false)
    (x:regValue railA q.basis=(u+v)/2^70) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^70) :
    let far:=decide (3*2^70≤u+v)
    let long:=decide (3*2^70≤u+v ∧ 2^54≤u)
    run flags m q=⟨q.phase,writeBit (writeBit q.basis 1631 far) 1632 long⟩ := by
  have act:=PortalValues.actual_flags_shadow7 476 477 thresholdPairs orientationPairs 856 railA railB
    (by decide +kernel) (by decide +kernel) q.basis (2^70) (2^54) u v (negative sg u).toNat
    (by decide) (by decide) small (by cases negative sg u <;> decide) x y
  rw [flags_do q m scratch]
  rw [act.2,act.1]

theorem erase_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 3*2^70 ≤ u+v → min u v < 2^54) (fresh:q.basis 1556=false ∧ ∀w∈carry,q.basis w=false)
    (x:regValue railA q.basis=(u+v)/2^70) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^70)
    (mode:q.basis 1632=decide (3*2^70≤u+v ∧ 2^54≤u)) :
    let r:=run erase m q
    r.phase=q.phase ∧ (∀w,w∉bulkB → r.basis w=q.basis w) ∧ regValue bulkB r.basis=0 := by
  rw [erase_spec]
  apply PortalBorrow.erase_run
  · exact copy_good
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact fresh.1
  · exact fresh.2
  · apply PortalValues.input_eq_shadow7 476 477 478 856 857 858 1632 bulkA bulkB q.basis (2^70) (2^54) u v (negative sg u).toNat
    · decide
    · decide
    · exact small
    · cases negative sg u <;> decide
    · by_cases pos:0<u <;> cases sg <;> simp_all [negative]; omega
    · exact x
    · exact y
    · exact mode
    · decide +kernel


end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def loPairs := (railA.take 3).zip (railB.take 3)
def hiPairs := bulkA.zip bulkB
theorem pair_split : pairs=loPairs++hiPairs := by decide +kernel
theorem store_shape : store=RailPair.store 405 1633 loPairs hiPairs := by decide +kernel
theorem hi_y : hiPairs.map Prod.snd=bulkB := by decide +kernel
theorem noOverlap : ∀p∈hiPairs,p.1∉hiPairs.map Prod.snd := by decide +kernel
theorem bankLayout : CutLayout loPairs hiPairs 405 1633 1631 1632 := by constructor <;> first | constructor <;> decide +kernel | decide +kernel
theorem pot : ∀w∈railA++railB,w≠1631 ∧ w≠1632 := by decide +kernel
theorem carry_apart : ∀w∈carry,w≠1631 ∧ w≠1632 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

/-- The real physical portal applied to the genuine rolling secp trajectory leaves
all ordinary exterior bits alone, clears the redundant upper rail, parks the
positive upper word, and produces its actual arithmetic predicates. -/
theorem clean_for (raw:State) (z:SkywalkNat.State) (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 390) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    ∀q∈activeScratch,(pullState (OB5.sig 389) raw).basis q=false:=by
  have pool : ∀q∈activeScratch,OB5.sig 389 q∈(W.compactSkywalkTickLayout base 390).carry := by decide +kernel
  exact fun q hq=>(regValue_zero _ _).mp record.2.2.2.2.2 _ (pool _ hq)
theorem physical_frame_local (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 54 15 z) (raw:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 390) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let origin:=pullState (OB5.sig 389) raw
    PackedCut loPairs hiPairs 405 1633 1631 1632 (negative sg z.u)
      (decide (3*2^70≤z.u+z.v)) (decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u))
      origin (run (Shadow7.portalP 390) m origin) := by
  let origin:=pullState (OB5.sig 389) raw
  let v:=run scan m origin
  let t1:=m.drop (measurementCount scan)
  let w:=run flags t1 v
  let t2:=m.drop (measurementCount (scan++flags))
  let x:=run erase t2 w
  let t3:=m.drop (measurementCount (scan++flags++erase))
  let far:=decide (3*2^70≤z.u+z.v)
  let long:=decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u)
  have short : 3*2^70 ≤ z.u+z.v → min z.u z.v < 2^54 := by
    intro f
    exact small ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr f)
  have clean:=clean_for raw z route sg record
  have vs:∀q∈activeScratch,v.basis q=false:=fun q mem=>(run_preserves_outside _ m origin q (away_scan _ mem)).trans (clean q mem)
  have fresh:origin.basis 1633=false:=by
    apply (regValue_zero _ _).mp record.2.2.2.2.2 (OB5.sig 389 1633)
    decide +kernel
  have first:=scan_input _ _ _ _ _ _ _ _ source geom raw m _ _ route sg record fresh
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at first
  obtain ⟨neg,_g,left,right⟩:=first
  have wf:w=⟨v.phase,writeBit (writeBit v.basis 1631 far) 1632 long⟩:=flags_values v t1 _ _ sg short vs left right
  have keep (q:Wire) (qf:q≠1631) (qu:q≠1632):w.basis q=v.basis q:=by rw [wf];simp [writeBit,qf,qu]
  have cv:w.basis 1556=false ∧ ∀q∈carry,w.basis q=false := by
    refine ⟨(keep _ (by decide) (by decide)).trans (vs _ (by decide +kernel)),?_⟩
    intro q hq
    exact (keep q (carry_apart _ hq).1 (carry_apart _ hq).2).trans (vs _ (by simp [activeScratch,hq]))
  have vals (r:List Wire) (sub:∀q∈r,q∈railA++railB):regValue r w.basis=regValue r v.basis:=
    regValue_congr _ _ _ (fun q h=>keep _ (pot _ (sub q h)).1 (pot _ (sub q h)).2)
  have xe:=erase_values w t2 _ _ sg short cv
    ((vals _ (fun _ h=>List.mem_append_left _ h)).trans left)
    ((vals _ (fun _ h=>List.mem_append_right _ h)).trans right) (by rw [wf];simp [long,writeBit])
  have scanned:=scan_run 528 908 405 1633 pairs geom origin m fresh
  rw [←scan_shape] at scanned
  have sign:(origin.basis 528 ^^ origin.basis 908)=negative sg z.u:=scanned.2.1.symm.trans neg
  rw [sign,pair_split] at scanned
  have clearHi:∀p∈hiPairs,x.basis p.2=false:=by
    intro p hp
    have hy:p.2∈hiPairs.map Prod.snd:=List.mem_map.mpr ⟨p,hp,rfl⟩
    exact (regValue_zero _ _).mp xe.2.2 p.2 (hi_y ▸ hy)
  have stored:=store_run 405 1633 loPairs hiPairs bankLayout.store x t3 clearHi
  rw [←store_shape] at stored
  rw [emitted]
  simp only [run_append,run_take]
  apply packed loPairs hiPairs 405 1633 1631 1632 _ far long origin v w x (run store t3 x)
    bankLayout scanned.1 neg scanned.2.2.1 scanned.2.2.2 wf
  · rw [hi_y];exact xe
  · exact stored.1
  · exact stored.2.1
  · exact stored.2.2.1
  · exact stored.2.2.2
  · exact noOverlap
end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

-- ===== ShadowPark390 =====
section
namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary3907
open ArchivePortAction StairArchiveIntegerHook CodecBitSliceVerify
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
def rawPortsList : List Wire := [396,1689,397,1688,398,1687,399,1686,400,1685,401,1684,402,1683,403,1682,404,1681,405,1680,909,910,911,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,912,913,914,915,916,917,918,919,920,921,922,923]
def rawPorts (i:Fin 157) : Wire := rawPortsList.getD i 0
def codePortsList : List Wire := [396,1689,397,1688,398,399,1686,400,401,1684,402,1683,403,404,1681,405,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,912,913,914,915,916,917,918,919,920,921,922,923,1687,1685,1682,1680,909,910,911]
def codePorts (i:Fin 157) : Wire := codePortsList.getD i 0
def loadMapList : List Wire := [396,1689,397,1688,398,1687,399,1686,400,1685,401,1684,402,1683,403,1682,404,1681,405,1680,909,910,911,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,912,913,914,915,916,917,918,919,920,921]
def loadMap (q:Wire) := loadMapList.getD q 0
def loadMoves : List (Wire×Wire) := [(399,1687),(1686,1687),(400,1687),(401,1687),(1684,1685),(402,1687),(1683,1685),(403,1687),(404,1685),(1681,1687),(405,1682)]
def loadRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,17,16,18,19,20,21,22]
def loadRoute (i:Fin 157) := loadRouteList.getD i 0
theorem load_program (d:Bool) : (Shadow7.exitLoadP 390) d=placed loadMap (op true d) ++ moves loadMoves := by cases d <;> rfl
theorem load_unique : Function.Injective rawPorts := by exact injective_list rawPortsList (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem load_map : ∀q:Fin 155, loadMap q=rawPorts ⟨q,by omega⟩ := by
  have h1 : (loadMapList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h2 : (rawPortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro q
  simp only [loadMap, rawPorts, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h2]
  revert q
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem load_route : ∀i,backMap loadMoves (codePorts i)=rawPorts (loadRoute i) := by
  have h1 : (codePortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h2 : (rawPortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h3 : ((loadRouteList.map Fin.val).all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro i
  simp only [codePorts, rawPorts, loadRoute, ECDSAAdd.Entrant.WSlimV3.fin_getD_val, Fin.val_zero, Fin.isValue,
    ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h2, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h3]
  revert i
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem load_sort : ∀ i, loadRoute i=i ∨ (16≤ i.val ∧ 16≤(loadRoute i).val) := by
  have h1 : ((loadRouteList.map Fin.val).all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro i
  simp only [loadRoute, Fin.ext_iff, ECDSAAdd.Entrant.WSlimV3.fin_getD_val, Fin.val_zero, Fin.isValue,
    ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1]
  revert i
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem load_scope : ∀p∈loadMoves,(∃i,rawPorts i=p.1) ∧ (∃i,rawPorts i=p.2) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem load_run (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame rawPorts (startCols true d) row s) :
    let t:=run ((Shadow7.exitLoadP 390) d) m s
    t.phase=s.phase ∧ Frame codePorts (endCols true d) row t ∧ ∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d rawPorts codePorts loadMap loadMoves loadRoute load_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) load_route load_sort load_scope row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map ⟨q,lim⟩⟩
def restoreMapList : List Wire := [396,1689,397,1688,398,399,1686,400,401,1684,402,1683,403,404,1681,405,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,912,913,914,915,916,917,918,919,920,921,922,923]
def restoreMap (q:Wire) := restoreMapList.getD q 0
def restoreMoves : List (Wire×Wire) := [(1687,399),(399,1686),(1686,400),(400,401),(1685,1684),(401,402),(1684,1683),(402,403),(1683,404),(403,1681),(1682,405),(404,1556),(1681,1557),(405,1558),(1680,1559),(909,1560),(910,1561),(911,1562)]
def restoreRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,151,150,152,153,154,155,156,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149]
def restoreRoute (i:Fin 157) := restoreRouteList.getD i 0
theorem restore_program (d:Bool) : (Shadow7.exitRestoreP 390) d=placed restoreMap (op false d) ++ moves restoreMoves := by cases d <;> rfl
theorem restore_unique : Function.Injective codePorts := by exact injective_list codePortsList (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem restore_map : ∀q:Fin 150, restoreMap q=codePorts ⟨q,by omega⟩ := by
  have h1 : (restoreMapList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h2 : (codePortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro q
  simp only [restoreMap, codePorts, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h2]
  revert q
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem restore_route : ∀i,backMap restoreMoves (rawPorts i)=codePorts (restoreRoute i) := by
  have h1 : (rawPortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h2 : (codePortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h3 : ((restoreRouteList.map Fin.val).all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro i
  simp only [codePorts, rawPorts, restoreRoute, ECDSAAdd.Entrant.WSlimV3.fin_getD_val, Fin.val_zero, Fin.isValue,
    ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h2, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h3]
  revert i
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem restore_sort : ∀ i, restoreRoute i=i ∨ (23≤ i.val ∧ 23≤(restoreRoute i).val) := by
  have h1 : ((restoreRouteList.map Fin.val).all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro i
  simp only [restoreRoute, Fin.ext_iff, ECDSAAdd.Entrant.WSlimV3.fin_getD_val, Fin.val_zero, Fin.isValue,
    ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1]
  revert i
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem restore_scope : ∀p∈restoreMoves,(∃i,codePorts i=p.1) ∧ (∃i,codePorts i=p.2) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem restore_run (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame codePorts (startCols false d) row s) :
    let t:=run ((Shadow7.exitRestoreP 390) d) m s
    t.phase=s.phase ∧ Frame rawPorts (endCols false d) row t ∧ ∀q,(∀i,codePorts i≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d codePorts rawPorts restoreMap restoreMoves restoreRoute restore_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) restore_route restore_sort restore_scope row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map ⟨q,lim⟩⟩
theorem code_from_raw : ∀i,∃j,rawPorts j=codePorts i := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem roundtrip (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m n:List Bool)
    (ready:Frame rawPorts raw row s) :
    run ((Shadow7.exitRestoreP 390) d) n (run ((Shadow7.exitLoadP 390) d) m s)=s := by
  have f:=load_run d row hr s m ready
  have b:=restore_run d row hr _ n f.2.1
  apply state_eq
  · exact b.1.trans f.1
  · intro q
    by_cases h:∃i,rawPorts i=q
    · obtain ⟨i,rfl⟩:=h
      exact (b.2.1 i).trans (ready i).symm
    · have no:∀i,rawPorts i≠q:=fun i eq=>h ⟨i,eq⟩
      have noc:∀i,codePorts i≠q:=by
        intro i; obtain ⟨j,eq⟩:=code_from_raw i
        exact eq ▸ no j
      exact (b.2.2 q noc).trans (f.2.2 q no)
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary3907
open ArchivePortAction CodecBitSliceVerify StairArchiveRaw StairArchiveGates
theorem load_record (d:Bool) (data:Nat→Bool) (s:State) (m:List Bool)
    (legal:∃row<63145,∀q<23,(rawCol q).testBit row=data q)
    (recorded:∀i:Fin 157,i.val<23 → s.basis (rawPorts i)=data i)
    (scratch:∀i:Fin 157,23≤ i.val → s.basis (rawPorts i)=false) :
    let t:=run ((Shadow7.exitLoadP 390) d) m s
    ∃row<63145, t.phase=s.phase ∧ Frame codePorts (code d) row t ∧
        (∀i:Fin 16,t.basis (codePorts ⟨i,by omega⟩)=(get (if d then ReducedWindowArchives.enter0StoredIn else ReducedWindowArchives.enter1StoredIn) i).testBit row) ∧
        (∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q) ∧
        (∀ tape, run ((Shadow7.exitRestoreP 390) d) tape t=s) := by
  obtain ⟨row,hr,h⟩:=legal
  have ready:=starting_frame rawPorts s row data h recorded scratch
  have ⟨ph,fr,away⟩:=load_run d row hr s m ready
  refine ⟨row,hr,ph,fr,?_,away,fun tape=>roundtrip d row hr s m tape ready⟩
  intro i
  exact (fr ⟨i,by omega⟩).trans (congrArg (fun x:Nat=>x.testBit row) (field_bits d i))
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary3907

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw ArchivePortAction
namespace ArchiveBoundary3907
def sourceIdx : Fin 23 := ⟨20,by decide⟩
theorem chronological : ∀i:Fin 20, rawPorts ⟨i,by omega⟩=nativeRawPort sourceIdx i := by decide +kernel
theorem observed (before now:State)
    (kept:∀q:Fin 20,now.basis (rawPorts ⟨q,by omega⟩)=before.basis (rawPorts ⟨q,by omega⟩))
    (far u c:Bool) (tags:now.basis (rawPorts 20)=far ∧ now.basis (rawPorts 21)=u ∧ now.basis (rawPorts 22)=c) :
    let cells:=readCells (Shadow7.shape sourceIdx) 0 15 (mappedBasis sourceIdx before.basis)
    ∀i:Fin 157,i.val<23 → now.basis (rawPorts i)=rawBit (read (cells.drop 5)) far u c i := by
  dsimp only
  intro i bound
  by_cases young:i.val<20
  · let col:Fin 20:=⟨i,young⟩
    refine (kept col).trans ?_
    rw [chronological col]
    exact (Shadow7.native_raw_read sourceIdx before i young).trans (by simp [rawBit,young])
  · have eq:i=20 ∨ i=21 ∨ i=22:=by omega
    rcases eq with rfl|rfl|rfl
    · exact tags.1
    · exact tags.2.1
    · exact tags.2.2
end ArchiveBoundary3907
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run unrouted onRails
namespace NativePack3907
def program (d:Bool) := renameProgram (OB5.sig 390) (Rolling1588.packAtTick d 380)
def reverse (d:Bool) := renameProgram (OB5.sig 390) (Rolling1588.unpackAtTick d 380)
end NativePack3907
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run unrouted onRails
namespace NativePack3907
def history (q:Fin 10) := OB5.sig 390 (History5.historyMap base 375 q)
theorem histInj : Function.Injective history := by decide +kernel
theorem equals (d:Bool) : program d=Rolling1588.codeEncodeAt d history ∧ reverse d=Rolling1588.codeDecodeAt d history := by cases d <;> decide +kernel
theorem source_law (d:Bool) (s:State) (m:List Bool) (ok:MeasuredCodec5.legalAt history s.basis) :
    (run (program d) m s).phase=s.phase ∧ ∀t,run (reverse d) t (run (program d) m s)=s:=by
  rw [(equals d).1,(equals d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d history histInj s m ok).1, fun t=>Rolling1588.codeRoundtripAt d history histInj s m t ok⟩
end NativePack3907
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed RailPair
namespace Portal390Flag7
set_option exponentiation.threshold 1024
theorem release (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 54 15 z) (raw packed:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 390) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 (PortalValues.negative sg z.u)
      (decide (3*2^70≤z.u+z.v)) (decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u))
      (pullState (OB5.sig 389) raw) packed) :
    run (Shadow7.portalInvP 390) m packed=pullState (OB5.sig 389) raw := by
  rw [cut.unique (physical_frame_local z small raw [] route sg record)]
  exact portal_return _ [] m (clean_for raw z route sg record)

end Portal390Flag7
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed StairArchiveRaw StairArchiveTrace SkywalkRails ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run onRails
namespace NativePack3907
open ArchiveBoundary3907
theorem prefixMap : ∀r:Fin 5,history ⟨2*r.val,by omega⟩=windowNet sourceIdx (ports (Shadow7.shape sourceIdx) r).a0 ∧
    history ⟨2*r.val+1,by omega⟩=windowNet sourceIdx (ports (Shadow7.shape sourceIdx) r).history := by decide +kernel
theorem legal_prefix (s t:State) (legal:StairArchiveRaw.legal (readCells (Shadow7.shape sourceIdx) 0 15 (mappedBasis sourceIdx s.basis)))
    (kept:∀i,t.basis (history i)=s.basis (history i)) : MeasuredCodec5.legalAt history t.basis := by
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  intro i
  rw [kept,kept,(prefixMap i).1,(prefixMap i).2]
  have good:=legal _ (member_cell (Shadow7.shape sourceIdx) 15 0 i (mappedBasis sourceIdx s.basis) (by have h:=i.isLt;omega))
  apply not_both
  simpa only [Nat.zero_add,cell,mappedBasis] using good
end NativePack3907
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907
open Arithmetic ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024
def src : List Wire := [1634,1635,1636]
def dst : List Wire := [909,910,911]
def pairs : List (Wire×Wire) := [(909,1634),(910,1635),(911,1636)]
def stash (payload:State) (s:State) : State :=
  ⟨s.phase,fun q=>if q∈dst then payload.basis (backMap pairs q) else s.basis q⟩

theorem commutes (p:Program) (free:∀q∈dst,q∉wires p) (m:List Bool) (payload s:State):
    run p m (stash payload s)=stash payload (run p m s) := by
  have inc:=run_measured_locality p (wires p) (Finset.Subset.refl _) (stash payload s) s m rfl
    (fun q h=>by simp [stash,show q∉dst from fun eq=>free _ eq h])
  apply congrArg₂ State.mk inc.1
  funext q
  by_cases h:q∈wires p
  · simpa [stash,show q∉dst from fun eq=>free _ eq h] using inc.2 q h
  · rw [run_preserves_outside _ m _ _ h]
    simp only [stash,run_preserves_outside _ m s _ h]

theorem park (s:State) (m:List Bool) (empty:∀q∈dst,s.basis q=false) :
    run (Shadow7.parkP 390) m s=stash s (eraseSites src s) := by
  rw [show (Shadow7.parkP 390)=moves pairs by rfl,moves_run _ (by decide) s m]
  apply congrArg₂ State.mk rfl
  funext q
  by_cases dest:q∈dst
  · simp [stash,dest]
  by_cases source:q∈src
  · have toDst:∀w∈src,backMap pairs w∈dst:=by decide
    simp [stash,eraseSites,dest,source,empty _ (toDst _ source)]
  · simp only [src,List.mem_cons,List.not_mem_nil,or_false,not_or] at source
    have nod:=dest
    simp only [dst,List.mem_cons,List.not_mem_nil,or_false,not_or] at nod
    simp [stash,eraseSites,dest,src,pairs,backMap,source.1,source.2.1,source.2.2,nod.1,nod.2.1,nod.2.2]

theorem park_undo (s:State) (m n:List Bool) : run (Shadow7.parkInvP 390) n (run (Shadow7.parkP 390) m s)=s := by
  rw [show (Shadow7.parkP 390)=moves pairs by rfl,show (Shadow7.parkInvP 390)=moves pairs.reverse by rfl,moves_run _ (by decide),moves_run _ (by decide)]
  apply congrArg₂ State.mk rfl
  funext q
  by_cases h:q∈src++dst
  · have inv:∀w∈src++dst,backMap pairs (backMap pairs.reverse w)=w:=by decide
    exact congrArg s.basis (inv _ h)
  · simp only [List.mem_append,src,dst,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    rcases h with ⟨⟨h1,h2,h3⟩,⟨h4,h5,h6⟩⟩
    simp [pairs,backMap,h1,h2,h3,h4,h5,h6]


end ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907
open Arithmetic MappedCompressed Portal390Flag7
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
def misses (i:Instr) := decide (909∉i.wires ∧ 910∉i.wires ∧ 911∉i.wires)
theorem misses_all (P:Program) (h:P.all misses=true) : ∀q∈dst,q∉wires P:=by
  intro q hq
  induction P with
  | nil=>simp [wires]
  | cons i P ih=>
    simp only [List.all_cons,Bool.and_eq_true] at h
    have hi:909∉i.wires ∧ 910∉i.wires ∧ 911∉i.wires:=of_decide_eq_true h.1
    simp only [wires,Finset.mem_union,not_or]
    exact ⟨by rcases List.mem_cons.mp hq with rfl|h'
              · exact hi.1
              · rcases List.mem_cons.mp h' with rfl|h''
                · exact hi.2.1
                · obtain rfl:=List.mem_singleton.mp h'';exact hi.2.2,ih h.2⟩
theorem avoid : ∀q∈dst,q∉wires (Shadow7.portalP 390):=misses_all _ (by decide +kernel)
theorem avoidInv : ∀q∈dst,q∉wires (Shadow7.portalInvP 390):=misses_all _ (by decide +kernel)

theorem parked_release (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 54 15 z) (raw s:State) (m n:List Bool)
    (route sg:Bool)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 390) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 (PortalValues.negative sg z.u)
      (decide (3*2^70≤z.u+z.v)) (decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u))
      (pullState (OB5.sig 389) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) :
    let out:=run (Shadow7.portalInvP 390) n (run (Shadow7.parkP 390) m s)
    out=stash s (pullState (OB5.sig 389) raw) ∧ ∀a b,
      run (Shadow7.parkInvP 390) b (run (Shadow7.portalP 390) a out)=s := by
  have fw (a:List Bool):=cut.unique (physical_frame_local z small raw a route sg input)
  have endEq:run (Shadow7.portalInvP 390) n (run (Shadow7.parkP 390) m s)=stash s (pullState (OB5.sig 389) raw):=by
    rw [park _ _ empty,commutes _ avoidInv,release z small raw _ n route sg input cut]
  refine ⟨endEq,?_⟩
  intro a b
  rw [endEq,commutes _ avoid,←fw,←park s m empty,park_undo]

end ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
theorem released : ∀q∈dst,OB5.sig 389 q∈(W.compactSkywalkSignPoolB base 390).released := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
theorem dormant (i:Nat) (d:Bool) (seed p:Nat) (raw:State) (q:Wire)
    (stage:Rolling1588.Integer.Stage base d seed p i raw.basis)
    (outside:q∉wires (Rolling1588.Integer.encodePrefix base d i))
    (inHigh:q∈(W.compactSkywalkSignPoolB base i).released) : raw.basis q=false := by
  obtain ⟨s,hs,eq⟩:=stage
  have clean:(W.compactSkywalkSignPoolB base i).Clean s.basis:=hs.2.2
  rw [eq,run_preserves_outside _ _ s q outside]
  exact clean q inHigh
theorem above_history (i:Nat) (lim:i≤512) (d:Bool) (q:Nat)
    (q0:i+16<q) (q1:q<1044) : q∉wires (Rolling1588.Integer.encodePrefix base d i):=by
  rw [Rolling1588.Integer.prefix_support_eq]
  intro mem
  obtain ⟨j,where',side⟩:=StackOB5Base.encodePrefix_mem i lim _ mem
  change q=j+16 at where'
  omega
theorem clear_dest (d:Bool) (seed p:Nat) (raw:State)
    (stage:Rolling1588.Integer.Stage base d seed p 390 raw.basis) :
    ∀q∈dst,(pullState (OB5.sig 389) raw).basis q=false:=by
  have bounds:∀q∈dst,390+16<OB5.sig 389 q ∧ OB5.sig 389 q<1044:=by decide +kernel
  intro q hit
  exact dormant 390 d seed p raw (OB5.sig 389 q) stage
    (above_history 390 (by decide) d _ (bounds _ hit).1 (bounds _ hit).2) (released _ hit)

end ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907

end

-- ===== ShadowExit390 =====
section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def L:=W.compactSkywalkTickLayout base 390
def P:=TickRanges.tick base 390
def Q:=W.ReverseCarry.compactReceiverTick base 390
def physP:=renameProgram (OB5.sig 390) P
def physQ:=renameProgram (OB5.sig 390) Q
theorem supports : wires P⊆L.wires.toFinset ∧ wires Q⊆L.wires.toFinset :=
  ⟨(TickRanges.tick_support base 390 (by decide) base_pool_nodup).trans
    (W.repairedTick_support base 390 (by decide) base_pool_nodup),
    W.ReverseCarry.compactReceiverTick_support base 390 (by decide) base_pool_nodup⟩
theorem physical_free (R:Program) (sub:wires R⊆L.wires.toFinset) (q:Wire)
    (off:OB5.sig 390 q∉L.wires) : q∉wires (renameProgram (OB5.sig 390) R) := by
  rw [JointForward1588.wires_rename_image]
  intro h
  obtain ⟨w,mem,rfl⟩:=Finset.mem_image.mp h
  rw [OB5.sig_invol 390 (by decide)] at off
  exact off (List.mem_toFinset.mp (sub mem))
theorem spared : ∀q∈ParkEndpoint3907.dst,OB5.sig 390 q∉L.wires := by decide +kernel
theorem stashP : ∀q∈ParkEndpoint3907.dst,q∉wires physP := fun q hit=>physical_free P supports.1 q (spared q hit)
theorem stashQ : ∀q∈ParkEndpoint3907.dst,q∉wires physQ := fun q hit=>physical_free Q supports.2 q (spared q hit)
end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic Secp256k1 MappedCompressed
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
theorem local_reference (i:Nat) (hi:i<512) (d:Bool) (x:Nat) (original:State)
    (stage:Rolling1588.Integer.Stage base d x p i original.basis) :
    ∃raw:State,W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) i raw.basis ∧
      ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset, original.basis q=raw.basis q := by
  obtain ⟨raw,hraw,eq⟩:=stage
  refine ⟨raw,hraw,fun q hq=>?_⟩
  rw [eq]
  exact run_preserves_outside _ _ _ q (fun used=>Finset.disjoint_left.mp
    (Rolling1588.Integer.prefix_disjoint_layout base d base_pool_nodup i i (le_refl _) hi) used hq)

theorem undo_on_domain (w:Nat→Wire) (hn:(skywalkPoolWires w).Nodup) (x p i:Nat)
    (hi:i<512) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256) (hgap:p+2^32≤2^256) (hx:x<p) (hc:x.Coprime p)
    (t raw:State) (a b:List Bool)
    (hraw:W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i raw.basis)
    (read:∀q∈(W.compactSkywalkTickLayout w i).wires,t.basis q=raw.basis q) :
    run (W.ReverseCarry.compactReceiverTick w i) b (run (W.compactSkywalkTick w i) a t)=t:=by
  have loc := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hgap hx hc hi raw hraw
  have hh : t.basis (W.compactSkywalkTickLayout w i).history=false := by
    rw [read _ (by simp [SkywalkIntegerLayout.wires])]
    exact loc.2.2.2.2.1
  have tops : W.trimTick i →
      t.basis (w (i+W.compactSkywalkTickPreWidth i-1))=t.basis (w (i+W.compactSkywalkTickPreWidth i-2)) ∧
      t.basis (w (770+W.compactSkywalkTickPreWidth i-1))=t.basis (w (770+W.compactSkywalkTickPreWidth i-2)) := by
    intro htr
    have st := W.compactSkywalkStage_tops w hn x p i hp0 hx0 hpo hp hgap hx hc hi htr raw hraw
    have split := W.compactSkywalkTick_aMid_split w i hi
    have mem (q : Wire) (h : q∈(W.compactSkywalkTickLayout w i).aMid ∨ q=(W.compactSkywalkTickLayout w i).aSign ∨
        q∈(W.compactSkywalkTickLayout w i).bMid ∨ q=(W.compactSkywalkTickLayout w i).bSign) :
        q∈(W.compactSkywalkTickLayout w i).wires := by
      simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh,
        List.mem_cons,List.mem_append]
      itauto
    have ra := read _ (mem _ (Or.inr (Or.inl rfl)))
    have rb := read _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))
    have la := read (w (i+W.compactSkywalkTickPreWidth i-2))
      (mem _ (Or.inl (by rw [split.1]; simp)))
    have lb := read (w (770+W.compactSkywalkTickPreWidth i-2))
      (mem _ (Or.inr (Or.inr (Or.inl (by rw [split.2]; simp)))))
    simp only [W.compactSkywalkTickLayout] at ra rb
    exact ⟨by rw [ra,la]; exact st.1,by rw [rb,lb]; exact st.2⟩
  have clean : regValue (W.compactSkywalkTickLayout w i).carry t.basis=0 := by
    rw [regValue_congr _ t.basis raw.basis (by
      intro q hq
      exact read q (by simp only [SkywalkIntegerLayout.wires,List.mem_append,List.mem_cons]; itauto))]
    exact loc.2.2.2.2.2
  exact W.ReverseCarry.compactReceiverTick_roundtrip w i hi hn t a b hh clean tops

end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic Secp256k1 MappedCompressed
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
def canonical:= W.compactSkywalkTick base 390
def Reads (a b:State) := ∀q∈L.wires.toFinset,a.basis q=b.basis q
theorem apply_old (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (actual original:State)
    (read:Reads actual original) (stage:Rolling1588.Integer.Stage base d x p 390 original.basis) (a b:List Bool) :
    run P a actual=run canonical b actual:=by
  obtain ⟨w,sw,agree⟩:=Rolling1588.Integer.old_stage_local base d base_pool_nodup x p 390 (by decide) original stage
  have old:=TickRanges.tick_eq5 x hx0 hx 390 (by decide) w a sw
  have same:=Stack5.local_replace P (W.repairedTick base 390) L.wires.toFinset supports.1
    (W.repairedTick_support base 390 (by decide) base_pool_nodup) original w a a agree old
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have reference:=Rolling1588.Integer.repaired_eq base d base_pool_nodup x p 390 hp0 hx0 hpo hp gap hx cop (by decide) original a b stage
  exact Stack5.local_replace P canonical L.wires.toFinset supports.1
    (W.compactSkywalkTick_support base 390 (by decide) base_pool_nodup) actual original a b read (same.trans reference)

theorem compact_undo (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (actual original:State)
    (read:Reads actual original) (stage:Rolling1588.Integer.Stage base d x p 390 original.basis) (a b:List Bool) :
    run Q b (run canonical a actual)=actual:=by
  obtain ⟨ref,stock,agree⟩:=local_reference 390 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  exact undo_on_domain base base_pool_nodup x p 390 (by decide) hp0 hx0 hpo hp gap hx cop actual ref a b stock
    (fun q h=>(read _ (List.mem_toFinset.mpr h)).trans (agree _ (List.mem_toFinset.mpr h)))


end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic MappedCompressed Secp256k1
attribute [local irreducible] run
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
theorem physical (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State)
    (read:Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 390 original.basis)
    (hist:raw.basis (base (1028+390))=false) (swapSlot:raw.basis (base (2053-390))=false)
    (m:List Bool) :
    let start:=ParkEndpoint3907.stash tags (pullState (OB5.sig 389) raw)
    let out:=run physP m start
    out=ParkEndpoint3907.stash tags (pullState (OB5.sig 390) (run canonical [] raw)) ∧
      ∀t,run physQ t out=start := by
  have pre:pullState (OB5.sig 389) raw=pullState (OB5.sig 390) raw:=
    OB5.pull_step 390 (by decide) raw hist (fun _=>swapSlot)
  have result:run physP m (ParkEndpoint3907.stash tags (pullState (OB5.sig 389) raw))=
      ParkEndpoint3907.stash tags (pullState (OB5.sig 390) (run canonical [] raw)):=by
    rw [ParkEndpoint3907.commutes _ stashP,pre,physP,OB5.run_rename _ (by decide),apply_old d x hx0 hx raw original read stage m []]
  refine ⟨result,?_⟩
  intro t
  rw [result,ParkEndpoint3907.commutes _ stashQ,physQ,OB5.run_rename _ (by decide),compact_undo d x hx0 hx raw original read stage,←pre]

end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic ArchivePortAction StairArchiveIntegerHook
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
namespace ArchiveBoundary3907
theorem load_cover (d:Bool) : wires ((Shadow7.exitLoadP 390) d) ⊆ rawPortsList.toFinset := by
  rw [load_program,wires_append,Finset.union_subset_iff]
  constructor
  · rw [placed,renameProgram_support]
    intro q member
    obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp member
    have bound:=Finset.mem_range.mp (sub (op true d) used)
    have small:w<155:=by cases d <;> exact bound
    have inside:∀j:Fin 155,loadMap j∈rawPortsList:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact List.mem_toFinset.mpr (inside ⟨w,small⟩)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ArchiveBoundary3907
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic MappedCompressed IntegerPacket
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
attribute [local irreducible] run
def readOnly (q:Wire) := OB5.sig 390 q∉L.wires ∨ q=405
instance (q:Wire) : Decidable (readOnly q) := by unfold readOnly;infer_instance
theorem observes (q:Wire) (h:readOnly q) (s:State) (m:List Bool) (prev:(run physP m s).basis 405=s.basis 405) : (run physP m s).basis q=s.basis q := by
  rcases h with h|rfl
  · exact run_preserves_outside _ _ _ _ (physical_free P supports.1 _ h)
  · exact prev
theorem oldPrefix : ∀i,readOnly (NativePack3907.history i) := by ((try unfold ECDSAAdd.Entrant.StairPacket.EndTick3907.readOnly); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem oldBank : ∀i:Fin 23,readOnly (ArchiveBoundary3907.rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩) := by ((try unfold ECDSAAdd.Entrant.StairPacket.EndTick3907.readOnly); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3500000
set_option maxRecDepth 18000
set_option exponentiation.threshold 1024
attribute [local irreducible] run

theorem canonical_reads (i:Nat) (hi:i<512) (w s:State)
    (view:∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset,s.basis q=w.basis q) (m:List Bool) :
    ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset,
      (run (W.compactSkywalkTick base i) m s).basis q=(run (W.compactSkywalkTick base i) m w).basis q := by
  let P:=W.compactSkywalkTick base i
  have sub:=W.compactSkywalkTick_support base i hi base_pool_nodup
  have touched:=(run_local_increment P s w m (fun q h=>view _ (sub h))).2
  intro q hit
  by_cases used:q∈wires P
  · exact touched q used
  · exact (run_preserves_outside _ m s q used).trans ((view _ hit).trans (run_preserves_outside _ m w q used).symm)

theorem after_reference (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 390 original.basis) :
    ∃ref:State,W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 390 ref.basis ∧
      W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 391 (run canonical [] ref).basis ∧
      Reads raw ref ∧ Reads (run canonical [] raw) (run canonical [] ref) := by
  obtain ⟨ref,hs,agree⟩:=local_reference 390 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have r:Reads raw ref:=fun q h=>(read q h).trans (agree q h)
  exact ⟨ref,hs,(W.compactSkywalkStageStep base base_pool_nodup x p 390 hp0 hx0 hpo hp gap hx cop (by decide) ref [] hs).2,r,
    canonical_reads 390 (by decide) ref raw r []⟩

theorem pastG (i j:Nat) (hi:i≤512) (hj:j < i) (r:SkywalkRails.State) (b:BasisState)
    (hs:W.CompactSkywalkStage base r i b) :
    b (base j)=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).1 :=
  (((W.compactSkywalkStage_fields_iff base r i hi base_pool_nodup b).mp hs).2.2.2.1 j hj).1

theorem full_carry (i:Nat) (hi:i≤512) (r:SkywalkRails.State) (b:BasisState) (hs:W.CompactSkywalkStage base r i b) :
    ∀q∈wireBlock base 1540 257,b q=false :=
  (regValue_zero _ _).mp (((W.compactSkywalkStage_fields_iff base r i hi base_pool_nodup b).mp hs).2.2.2.2.2.1)

end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3000000
set_option maxRecDepth 15000
attribute [local irreducible] run
theorem carry_member (i:Nat) (q:Wire) (mem:q∈(W.compactSkywalkTickLayout base i).carry) :
    q∈(W.compactSkywalkTickLayout base i).wires.toFinset := List.mem_toFinset.mpr (by simp [SkywalkIntegerLayout.wires,mem])
theorem previous_member (i:Nat) : (W.compactSkywalkTickLayout base i).previous∈(W.compactSkywalkTickLayout base i).wires.toFinset :=
  List.mem_toFinset.mpr (by simp [SkywalkIntegerLayout.wires])
theorem scratch_lanes : ∀k:Fin 134,k.val+390<512 → 1556+k.val∈L.carry ∧ 1556+k.val∈wireBlock base 1540 257 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
/-- window390: the scratch hosts `790+k` (the ports beyond the stock carry) are no wires of the end tick. -/
theorem host_lanes : ∀k:Fin 134,512≤k.val+390 → (790+k.val:Wire)∉L.wires.toFinset := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem after_cells (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 390 original.basis)
    (hosts:∀k:Fin 134,512≤k.val+390 → raw.basis (790+k.val)=false) :
    (run canonical [] raw).basis 405=raw.basis 405 ∧
    ∀k:Fin 134,(run canonical [] raw).basis (Shadow7.scratchX 390 k.val)=false := by
  obtain ⟨ref,old,next,pre,post⟩:=after_reference d x hx0 hx raw original read stage
  have prev:405∈L.wires.toFinset:=previous_member 390
  have a:=pastG 390 389 (by decide) (by decide) _ _ old
  have b:=pastG 391 389 (by decide) (by decide) _ _ next
  exact ⟨(post _ prev).trans (b.trans (a.symm.trans (pre _ prev).symm)),
    fun k=>by
      have _kl:=k.isLt
      by_cases hk:k.val+390<512
      · rw [show Shadow7.scratchX 390 k.val = 1556+k.val by
          unfold Shadow7.scratchX
          rw [if_neg (by decide : ¬ 390 ≤ 369), if_pos (by omega)]]
        exact (post _ (carry_member 390 _ (scratch_lanes k hk).1)).trans (full_carry 391 (by decide) _ _ next _ (scratch_lanes k hk).2)
      · rw [show Shadow7.scratchX 390 k.val = 790+k.val by
          unfold Shadow7.scratchX
          rw [if_neg (by decide : ¬ 390 ≤ 369), if_neg (by omega)]
          change 908+4+(1556+k.val+390-2068) = 790+k.val
          omega,
          run_preserves_outside canonical [] raw _ (fun used=>host_lanes k (by omega)
            ((W.compactSkywalkTick_support base 390 (by decide) base_pool_nodup) used))]
        exact hosts k (by omega)⟩

end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic MappedCompressed Secp256k1 ArchiveBoundary3907 ParkEndpoint3907
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
theorem no_phase (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 390 original.basis) : (run canonical [] raw).phase=raw.phase := by
  obtain ⟨ref,hs,ag⟩:=local_reference 390 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have step:=(W.compactSkywalkStageStep base base_pool_nodup x p 390 hp0 hx0 hpo hp gap hx cop (by decide) ref [] hs).1
  have inc:=(run_local_increment canonical raw ref [] (fun q h=>by
    have mem:=(W.compactSkywalkTick_support base 390 (by decide) base_pool_nodup) h
    exact (read q mem).trans (ag q mem))).1
  change (run canonical [] ref).phase=ref.phase at step
  rw [step,Bool.xor_self] at inc
  cases h:(run canonical [] raw).phase <;> cases k:raw.phase <;> simp_all

theorem scratch_table : ∀i:Fin 157,23≤ i.val →
    rawPorts i∉dst ∧ OB5.sig 390 (rawPorts i)=Shadow7.scratchX 390 (i.val-23) ∧ ∀v:Fin 10,rawPorts i≠NativePack3907.history v := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem coordinate (s raw:State) : (stash s (pullState (OB5.sig 390) raw)).basis 405=raw.basis 405 ∧
    (stash s (pullState (OB5.sig 389) raw)).basis 405=raw.basis 405 := ⟨rfl,rfl⟩

theorem stash_slots (raw after tags:State) (phase:after.phase=raw.phase) (same:after.basis 405=raw.basis 405)
    (zero:∀k:Fin 134,after.basis (Shadow7.scratchX 390 k.val)=false) :
    let start:=stash tags (pullState (OB5.sig 389) raw)
    let out:=stash tags (pullState (OB5.sig 390) after)
    out.phase=start.phase ∧ out.basis 405=start.basis 405 ∧
      ∀i:Fin 157,23≤ i.val → out.basis (rawPorts i)=false := by
  refine ⟨phase,(coordinate _ _).1.trans (same.trans (coordinate _ _).2.symm),?_⟩
  intro i hi
  have ⟨off,eq,_⟩:=scratch_table i hi
  simp only [stash,if_neg off]
  exact (congrArg after.basis eq).trans (zero ⟨i.val-23,by have h:=i.isLt;omega⟩)

theorem exposed (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 390 original.basis)
    (hist:raw.basis (base (1028+390))=false) (swapSlot:raw.basis (base (2053-390))=false)
    (hosts:∀k:Fin 134,512≤k.val+390 → raw.basis (790+k.val)=false) (m:List Bool) :
    let start:=stash tags (pullState (OB5.sig 389) raw)
    let out:=run physP m start
    out.phase=start.phase ∧ out.basis 405=start.basis 405 ∧
      ∀i:Fin 157,23≤ i.val → out.basis (rawPorts i)=false := by
  have out:=(physical d x hx0 hx raw original tags read stage hist swapSlot m).1
  have bits:=after_cells d x hx0 hx raw original read stage hosts
  dsimp only
  rw [out]
  exact stash_slots raw (run canonical [] raw) tags (no_phase d x hx0 hx raw original read stage) bits.1 bits.2

end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907
open Arithmetic MappedCompressed IntegerPacket RailPair Portal390Flag7 ArchiveBoundary3907
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
def ordinary (q:Wire) : Prop := q∉src ∧ q∉dst ∧ q≠1633 ∧ q≠1631 ∧ q≠1632 ∧ q∉sites hiPairs
instance (q:Wire) : Decidable (ordinary q):=by unfold ordinary;infer_instance
theorem past_sites : ∀r:Fin 15,ordinary (windowNet sourceIdx (ports (Shadow7.shape sourceIdx) r).a0) ∧
    ordinary (windowNet sourceIdx (ports (Shadow7.shape sourceIdx) r).history) := by ((try unfold ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907.ordinary); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem earlier (raw s:State) (n f u:Bool) (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 n f u
    (pullState (OB5.sig 389) raw) (eraseSites src s)) (q:Wire) (clean:ordinary q) :
    (stash s (pullState (OB5.sig 389) raw)).basis q=s.basis q := by
  obtain ⟨hs,hd,hn,hf,hu,hh⟩:=clean
  have eq:=cut.unchanged _ hn hf hu hh
  simpa [stash,eraseSites,hs,hd] using eq.symm

theorem past_cells (raw s:State) (n f u:Bool) (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 n f u
    (pullState (OB5.sig 389) raw) (eraseSites src s)) :
    Shadow7.physicalCells sourceIdx (stash s (pullState (OB5.sig 389) raw))=Shadow7.physicalCells sourceIdx s := by
  rw [Shadow7.physicalCells_eq, Shadow7.physicalCells_eq]
  apply cells_congr _ _ _ _ _ _ (by decide)
  intro r
  exact Prod.ext (earlier _ _ _ _ _ cut _ (past_sites r).1) (earlier _ _ _ _ _ cut _ (past_sites r).2)
theorem tag_address (s other:State) :
    (stash s other).basis (rawPorts 20)=s.basis 1634 ∧
    (stash s other).basis (rawPorts 21)=s.basis 1635 ∧
    (stash s other).basis (rawPorts 22)=s.basis 1636:=⟨rfl,rfl,rfl⟩
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack3907
open Arithmetic IntegerPacket MappedCompressed SkywalkRails StairArchiveRaw StairArchiveTrace ArchiveBoundary3907 ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run

theorem pack_support (d:Bool) : wires (program d) ⊆ ((List.finRange 10).map history).toFinset := by cases d <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem outside (d:Bool) (q:Wire) (no:∀v:Fin 10,q≠history v) (m:List Bool) (s:State) :
    (run (program d) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro mem
  obtain ⟨v,_,eq⟩:=List.mem_map.mp (List.mem_toFinset.mp (pack_support d mem))
  exact no v eq.symm
theorem bank_out : ∀q:Fin 23,∀v:Fin 10,rawPorts ⟨q,Nat.lt_trans q.isLt (by decide : 23<157)⟩≠history v := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem archive_ready (d:Bool) (start tick:State) (m:List Bool) (past:SkywalkNat.State) (g sign cross:Bool)
    (odd:past.v%2=1) (small : Shadow7.SmallIfFar 62 15 past) (prior:PastFacts sourceIdx rawPorts 62 past g sign cross start)
    (keptFive:∀i,tick.basis (history i)=start.basis (history i))
    (bank:∀i:Fin 23,tick.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=start.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩))
    (scratch:∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false) :
    MeasuredCodec5.legalAt history tick.basis ∧ ∃row<63145,ArchivePortAction.Frame rawPorts raw row (run (program d) m tick) := by
  let cells:=Shadow7.physicalCells sourceIdx start
  let f:=decide (Shadow.far 62 15 past)
  let u:=f && afterFlags (decide (past.v<past.u)) (cells.take 5)
  let c:=f && cross
  let data:=rawBit (read (cells.drop 5)) f u c
  let out:=run (program d) m tick
  have legal:StairArchiveRaw.legal (Shadow7.physicalCells sourceIdx start):=by rw [Shadow7.physicalCells_eq,prior.records];exact legal_signed 15 past g sign (by omega) odd
  have same (i:Fin 23) : out.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=
      start.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩):=
    (outside d _ (bank_out i) m tick).trans (bank i)
  have tags:out.basis (rawPorts 20)=f ∧ out.basis (rawPorts 21)=u ∧ out.basis (rawPorts 22)=c:=
    ⟨(same 20).trans prior.far,by simpa only [u,f,cells,Shadow7.physicalCells_eq] using (same 21).trans prior.suffix,(same 22).trans prior.crossed⟩
  have hw:∀i:Fin 157,i.val<23 → out.basis (rawPorts i)=data i :=
    observed start out (fun q=>same ⟨q,Nat.lt_trans q.isLt (by decide : 20<23)⟩) f u c tags
  have fresh (i:Fin 157) (hi:23≤ i.val) : out.basis (rawPorts i)=false :=
    (outside d _ (EndTick3907.scratch_table i hi).2.2 m tick).trans (scratch i hi)
  obtain ⟨row,limit,matchRow⟩:=interrupted_row_shadow7 62 past small odd g sign cross cells
    (((Shadow7.physicalCells_eq _ _).trans prior.records).trans (true_records_shadow7 _ _ small odd _ _).symm)
  exact ⟨legal_prefix _ _ legal keptFive,row,limit,starting_frame rawPorts out row data matchRow hw fresh⟩

end ECDSAAdd.Entrant.StairPacket.NativePack3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack3907
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary3907
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
def endSlice (d:Bool) := EndTick3907.physP ++ (program d ++ (Shadow7.exitLoadP 390) d)
def endUndo (d:Bool) := (Shadow7.exitRestoreP 390) d ++ (reverse d ++ EndTick3907.physQ)
structure Transition (inverse:Program) (s tick:State) : Prop where
  phase : tick.phase=s.phase
  keptFive : ∀i,tick.basis (history i)=s.basis (history i)
  keptBank : ∀i:Fin 23,tick.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=s.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)
  scratch : ∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false
  undo : ∀n,run inverse n tick=s

abbrev TickStep:=Transition EndTick3907.physQ

theorem tick_intro (s tick:State) (ph:tick.phase=s.phase)
    (obs:∀q,EndTick3907.readOnly q → tick.basis q=s.basis q)
    (zero:∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false) (undo:∀m,run EndTick3907.physQ m tick=s) :
    TickStep s tick :=
  ⟨ph,fun i=>obs _ (EndTick3907.oldPrefix i),fun i=>obs _ (EndTick3907.oldBank i),zero,undo⟩

theorem observe_tick (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State) (read:EndTick3907.Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 390 original.basis)
    (hist:raw.basis (base (1028+390))=false) (swapSlot:raw.basis (base (2053-390))=false)
    (hosts:∀k:Fin 134,512≤k.val+390 → raw.basis (790+k.val)=false) (m:List Bool) :
    let start:=ParkEndpoint3907.stash tags (pullState (OB5.sig 389) raw)
    TickStep start (run EndTick3907.physP m start) := by
  let s:=ParkEndpoint3907.stash tags (pullState (OB5.sig 389) raw)
  have h:=EndTick3907.exposed d x hx0 hx raw original tags read stage hist swapSlot hosts m
  have u:=(EndTick3907.physical d x hx0 hx raw original tags read stage hist swapSlot m).2
  exact tick_intro s (run EndTick3907.physP m s) h.1 (fun q hq=>EndTick3907.observes q hq s m h.2.1) h.2.2 u

theorem sequence_law (p e f r v q:Program) (s:State) (m:List Bool) (claim:State→Prop)
    (tick:State) (first:run p m s=tick) (phase:tick.phase=s.phase) (inv:∀a,run q a tick=s)
    (packed:State) (store:run e (m.drop (measurementCount p)) tick=packed) (middle:packed.phase=tick.phase)
    (unpack:∀a,run v a packed=tick) (out:State)
    (written:run f ((m.drop (measurementCount p)).drop (measurementCount e)) packed=out)
    (endPhase:out.phase=packed.phase) (good:claim out) (unwrite:∀a,run r a out=packed) :
    let result:=run (p++(e++f)) m s
    result.phase=s.phase ∧ claim result ∧ ∀a,run (r++(v++q)) a result=s := by
  dsimp only
  simp only [run_append,run_take,first,store,written]
  exact ⟨endPhase.trans (middle.trans phase),good,fun a=>by rw [unwrite,unpack,inv]⟩

end ECDSAAdd.Entrant.StairPacket.NativePack3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack3907
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary3907 ParkEndpoint3907 Portal390Flag7 StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
def lastWindow (d:Bool) := (Shadow7.parkP 390) ++ ((Shadow7.portalInvP 390) ++ endSlice d)
def lastUnwind (d:Bool) := endUndo d ++ ((Shadow7.portalP 390) ++ (Shadow7.parkInvP 390))

theorem after_park (raw s:State) (n f u:Bool)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 n f u (pullState (OB5.sig 389) raw) (eraseSites src s))
    (past:SkywalkNat.State) (G S cross:Bool)
    (records:Shadow7.physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode G S past.u past.v))
    (mode:s.basis 1634=decide (Shadow.far 62 15 past))
    (orientation:s.basis 1635=(decide (Shadow.far 62 15 past) && afterFlags (decide (past.v<past.u)) ((Shadow7.physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1636=(decide (Shadow.far 62 15 past) && cross)) :
    PastFacts sourceIdx rawPorts 62 past G S cross (stash s (pullState (OB5.sig 389) raw)) := by
  have cells:=past_cells raw s n f u cut
  have tag:=tag_address s (pullState (OB5.sig 389) raw)
  refine ⟨(Shadow7.physicalCells_eq _ _).symm.trans (cells.trans records),tag.1.trans mode,?_,tag.2.2.trans flipped⟩
  rw [←Shadow7.physicalCells_eq, cells];exact tag.2.1.trans orientation

end ECDSAAdd.Entrant.StairPacket.NativePack3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack3907
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary3907 ParkEndpoint3907 Portal390Flag7 StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
theorem empty_from_cut (raw s:State) (n f u:Bool)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 n f u (pullState (OB5.sig 389) raw) (eraseSites src s))
    (source:∀q∈dst,(pullState (OB5.sig 389) raw).basis q=false) : ∀q∈dst,s.basis q=false:=by
  have regular:∀q∈dst,q∉src ∧ q≠1633 ∧ q≠1631 ∧ q≠1632 ∧ q∉RailPair.sites hiPairs:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro q member
  obtain ⟨out,hn,hf,hu,hh⟩:=regular _ member
  have eq:=cut.unchanged q hn hf hu hh
  simpa [eraseSites,out] using eq.trans (source _ member)
end ECDSAAdd.Entrant.StairPacket.NativePack3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
theorem terminal3907 (d:Bool) (x:Nat) (s:State) (dom:Domain 390 x p s) :
    ∃ref:State,Rolling1588.Integer.Stage base d x p 390 ref.basis ∧ EndTick3907.Reads s ref ∧
    s.basis (base (1028+390))=false ∧ s.basis (base (2053-390))=false ∧
    (∀q∈ParkEndpoint3907.dst,(pullState (OB5.sig 389) s).basis q=false) ∧
    ∀k:Fin 134,512≤k.val+390 → s.basis (790+k.val)=false := by
  obtain ⟨ref,stage,link⟩:=leaves_reference 390 x p (by decide) d s dom
  have bounds:∀q∈ParkEndpoint3907.dst,390+16<OB5.sig 389 q ∧ OB5.sig 389 q<1044:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  refine ⟨ref,stage,reads_now (by decide) link,future_history (Nat.le_refl _) (by decide) dom,?_,?_,?_⟩
  · exact (link.2 _ (outside_above (by decide))).trans ((Rolling1588.Integer.stage_zero d x 390 (by decide) _ stage).2 (by decide))
  · intro q hit
    exact (link.2 _ (outside_between (bounds _ hit).1 (bounds _ hit).2)).trans (ParkEndpoint3907.clear_dest d x p ref stage q hit)
  · intro k hk
    have _kl := k.isLt
    have released : ∀ i : Fin 134, 512 ≤ i.val+390 →
        790+i.val ∈ (W.compactSkywalkSignPoolB base 390).released := by decide +kernel
    exact (link.2 _ (outside_between (by omega) (by omega))).trans
      (ParkEndpoint3907.dormant 390 d x p ref _ stage
        (ParkEndpoint3907.above_history 390 (by decide) d _ (by omega) (by omega)) (released k hk))
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack3907
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary3907
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open ArchiveBoundary3907 ParkEndpoint3907 Portal390Flag7 Secp256k1 SkywalkRails StairArchiveTrace
theorem matched_generic (p q:Program) (d:Bool) (s:State) (m:List Bool) (step:Transition q s (run p m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small : Shadow7.SmallIfFar 62 15 past)
    (prior:PastFacts sourceIdx rawPorts 62 past G S cross s) :
    let out:=run (p ++ (program d ++ (Shadow7.exitLoadP 390) d)) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run ((Shadow7.exitRestoreP 390) d ++ (reverse d ++ q)) n out=s := by
  let tick:=run p m s
  let e:=m.drop (measurementCount p)
  let pre:=run (program d) e tick
  let f:=e.drop (measurementCount (program d))
  have ⟨legal,row,limit,frame⟩:=archive_ready d s tick e past G S cross odd small prior step.keptFive step.keptBank step.scratch
  have truth:=row_truth sourceIdx rawPorts chronological row past G S s pre prior.records
    (fun i=>(outside d _ (bank_out i) e tick).trans (step.keptBank i)) frame
  have enc:=source_law d tick e legal
  have act:=load_run d row limit pre f frame
  exact sequence_law p (program d) ((Shadow7.exitLoadP 390) d) ((Shadow7.exitRestoreP 390) d)
    (reverse d) q s m (fun out=>∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out)
    tick rfl step.phase step.undo pre rfl enc.1 enc.2 (run ((Shadow7.exitLoadP 390) d) f pre) rfl act.1
    ⟨row,limit,truth,act.2.1⟩ (fun n=>roundtrip d row limit pre f n frame)

theorem matched_slice (d:Bool) (s:State) (m:List Bool) (step:TickStep s (run EndTick3907.physP m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small : Shadow7.SmallIfFar 62 15 past)
    (prior:PastFacts sourceIdx rawPorts 62 past G S cross s) :
    let out:=run (endSlice d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run (endUndo d) n out=s :=
  matched_generic EndTick3907.physP EndTick3907.physQ d s m step past G S cross odd small prior
theorem matched_last (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original s:State) (m:List Bool)
    (read:EndTick3907.Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 390 original.basis)
    (hist:raw.basis (base (1028+390))=false) (swapSlot:raw.basis (base (2053-390))=false)
    (hosts:∀k:Fin 134,512≤k.val+390 → raw.basis (790+k.val)=false)
    (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 54 15 z) (G S:Bool)
    (input:SkywalkIntegerInput EndTick3907.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 (PortalValues.negative S z.u)
      (decide (3*2^70≤z.u+z.v)) (decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u)) (pullState (OB5.sig 389) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm : Shadow7.SmallIfFar 62 15 past)
    (records:Shadow7.physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1634=decide (Shadow.far 62 15 past))
    (angle:s.basis 1635=(decide (Shadow.far 62 15 past) && afterFlags (decide (past.v<past.u)) ((Shadow7.physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1636=(decide (Shadow.far 62 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  let n:=m.drop (measurementCount (Shadow7.parkP 390))
  let one:=run (Shadow7.portalInvP 390) n (run (Shadow7.parkP 390) m s)
  let tape:=n.drop (measurementCount (Shadow7.portalInvP 390))
  have restored:=parked_release z small raw s m n G S input cut empty
  have facts:=after_park raw s _ _ _ cut past pg ps cross records mode angle flipped
  have tick:=observe_tick d x hx0 hx raw original s read stage hist swapSlot hosts tape
  have eqOne:one=stash s (pullState (OB5.sig 389) raw):=restored.1
  have A:PastFacts sourceIdx rawPorts 62 past pg ps cross one :=by rw [eqOne];exact facts
  have B:TickStep one (run EndTick3907.physP tape one):=by rw [eqOne];exact tick
  have body:=matched_slice d one tape B past pg ps cross odd pm A
  have phase:one.phase=s.phase:=(congrArg State.phase restored.1).trans cut.phase.symm
  dsimp only [lastWindow,lastUnwind]
  simp only [run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,?_⟩
  intro t
  rw [body.2.2 t]
  exact restored.2 _ _
theorem matched_from_domain (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw s:State) (m:List Bool)
    (domain:WideReference.Domain 390 x p raw) (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 54 15 z) (G S:Bool)
    (input:SkywalkIntegerInput EndTick3907.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 (PortalValues.negative S z.u)
      (decide (3*2^70≤z.u+z.v)) (decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u)) (pullState (OB5.sig 389) raw) (eraseSites src s))
    (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm : Shadow7.SmallIfFar 62 15 past)
    (records:Shadow7.physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1634=decide (Shadow.far 62 15 past))
    (angle:s.basis 1635=(decide (Shadow.far 62 15 past) && afterFlags (decide (past.v<past.u)) ((Shadow7.physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1636=(decide (Shadow.far 62 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty,hosts⟩:=WideReference.terminal3907 d x raw domain
  exact matched_last d x hx0 hx raw ref s m read stage history swapSlot hosts z small G S input cut
    (empty_from_cut _ _ _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped
end ECDSAAdd.Entrant.StairPacket.NativePack3907

end

-- ===== ShadowEnterJ =====
/-! build-chain: Shadow7 renders of the stock window families EnterJ (helpers/build-chain/shadow/render7.py). -/

section

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket MappedCompressed
def zeroSites (j:Fin 23) :=
  let p:=Shadow7.shape j
  let L:=ports p 0
  (L.a++L.b++[L.previous]++L.carry++((List.range' 0 15).flatMap fun r=>[(ports p r).ext,(ports p r).history])++
    [(ports p 0).a0,(ports p 0).history]).map (windowNet j)

set_option linter.unusedSimpArgs false in
theorem zero_congr (j:Fin 23) (s t:State) (agree:∀q∈Shadow7.zeroSites j,t.basis q=s.basis q)
    (z:SkywalkRails.State) (active:Shadow7.onRails j 0 z s.basis) :
    Shadow7.onRails j 0 z t.basis ∧ cell (Shadow7.shape j) 0 (mappedBasis j t.basis)=cell (Shadow7.shape j) 0 (mappedBasis j s.basis) := by
  let p:=Shadow7.shape j
  let L:=ports p 0
  let S:=mappedBasis j s.basis
  let T:=mappedBasis j t.basis
  have locality (q:Wire) (mem:q∈L.a++L.b++[L.previous]++L.carry++((List.range' 0 15).flatMap fun r=>[(ports p r).ext,(ports p r).history])++[(ports p 0).a0,(ports p 0).history]) :
      T q=S q := agree _ (List.mem_map.mpr ⟨q,mem,rfl⟩)
  have add (xs:List Wire) (incl:∀q∈xs,T q=S q) : signedRegValue xs T=signedRegValue xs S:=by
    unfold signedRegValue;rw [regValue_congr _ _ _ incl]
  obtain ⟨a,b,prev,carry,free⟩:=active
  refine ⟨⟨(add _ (fun q h=>locality _ (by simp [L,p,h]))).trans a,
    (add _ (fun q h=>locality _ (by simp [L,p,h]))).trans b,
    (locality _ (by simp [L,p])).trans prev,
    (regValue_congr _ _ _ (fun q h=>locality _ (by simp [L,p,h]))).trans carry,?_⟩,?_⟩
  · intro r hr last
    have inRange:r∈List.range' 0 15:=by rw [List.mem_range'_1];exact ⟨hr,last⟩
    obtain ⟨e,h⟩:=free r hr last
    exact ⟨(locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans e,
      (locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans h⟩
  · exact Prod.ext (locality _ (by simp [L,p])) (locality _ (by simp [L,p]))

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
end ECDSAAdd.Entrant.StairPacket.Shadow7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Generic enter piece of block `j` (par-c2, job C2 of PARAMETRIC.md). Tick `s = start j`, `h = Shadow7.sbP s`.
Every per-block number of dadon's `Enter{s}` / `EnterProof.ports{s}` is a function of `j` here; the
programs are par-b's `Shadow7.enterP j = Shadow7.forward (Shadow7.enterOps (start j))`. `EnterJ7.ports 12 = EnterProof.ports255`. -/

/-- The four A-rail ports `s+h+31..s+h+34`. -/
def railA (j : Fin 23) : List Wire :=
  [start j+Shadow7.sbP (start j)+31, start j+Shadow7.sbP (start j)+32, start j+Shadow7.sbP (start j)+33, start j+Shadow7.sbP (start j)+34]
/-- The four B-rail ports `h+801..h+804`. -/
def railB (j : Fin 23) : List Wire :=
  [Shadow7.sbP (start j)+801, Shadow7.sbP (start j)+802, Shadow7.sbP (start j)+803, Shadow7.sbP (start j)+804]
/-- Orientation gate `s+15` and the three flags `n f u` (`e0+5, e0+3, e0+4`). -/
def gate (j : Fin 23) : Wire := start j+15
def flagN (j : Fin 23) : Wire := Shadow7.sbP (start j)+1579
def flagF (j : Fin 23) : Wire := Shadow7.sbP (start j)+1577
def flagU (j : Fin 23) : Wire := Shadow7.sbP (start j)+1578
/-- Clean ports: `e0..e0+2` and the carry block `1556..1563`. -/
def clear (j : Fin 23) : List Wire :=
  [Shadow7.sbP (start j)+1574, Shadow7.sbP (start j)+1575, Shadow7.sbP (start j)+1576, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563]
/-- The 23 ports of the enter program (`EnterProof.ports{s}`). -/
def ports (j : Fin 23) : List Wire :=
  [start j+Shadow7.sbP (start j)+31, start j+Shadow7.sbP (start j)+32, start j+Shadow7.sbP (start j)+33, start j+Shadow7.sbP (start j)+34,
   Shadow7.sbP (start j)+801, Shadow7.sbP (start j)+802, Shadow7.sbP (start j)+803, Shadow7.sbP (start j)+804, start j+15,
   Shadow7.sbP (start j)+1579, Shadow7.sbP (start j)+1577, Shadow7.sbP (start j)+1578,
   Shadow7.sbP (start j)+1574, Shadow7.sbP (start j)+1575, Shadow7.sbP (start j)+1576, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563]
def map (j : Fin 23) (q : Wire) : Wire := (ports j).getD q 0
/-- The parked bank: three low pairs, then `Wp-3` upper pairs up to the B rail's top `785+R`. -/
def lowerPairs (j : Fin 23) : List (Wire×Wire) :=
  [(start j+Shadow7.sbP (start j)+32, Shadow7.sbP (start j)+802), (start j+Shadow7.sbP (start j)+33, Shadow7.sbP (start j)+803),
   (start j+Shadow7.sbP (start j)+34, Shadow7.sbP (start j)+804)]
def upperPairs (j : Fin 23) : List (Wire×Wire) :=
  (List.range (Shadow7.wpP (start j)-3)).map (fun i => (start j+Shadow7.sbP (start j)+35+i, Shadow7.sbP (start j)+805+i))
/-- Saved high word (`Enter{s}.saved`) and the three pending flags written by the previous leave. -/
def saved (j : Fin 23) : List Wire :=
  [Shadow7.sbP (start j)+1574, Shadow7.sbP (start j)+1575, Shadow7.sbP (start j)+1576]++(upperPairs j).map Prod.snd
def pending (j : Fin 23) : List Wire := [Shadow7.sbP (start j)+1580, Shadow7.sbP (start j)+1581, Shadow7.sbP (start j)+1582]
/-- Low rails `s+16..` and `786..` (`h+15` wires each) and the guard predicate. -/
def lowA (j : Fin 23) : List Wire := List.range' (start j+16) (Shadow7.sbP (start j)+15)
def lowB (j : Fin 23) : List Wire := List.range' 786 (Shadow7.sbP (start j)+15)
def safe (j : Fin 23) (q : Wire) : Prop :=
  (q<start j+16 ∨ start j+Shadow7.sbP (start j)+31≤q) ∧ (q<786 ∨ Shadow7.sbP (start j)+801≤q)
instance (j : Fin 23) (q : Wire) : Decidable (safe j q) := by unfold safe; infer_instance
/-- Stock layout of tick `s` and the frame of tick `s-1`. -/
def lay (j : Fin 23) : SkywalkIntegerLayout := W.compactSkywalkTickLayout base (start j)
def pull (j : Fin 23) : Wire → Wire := OB5.sig (start j-1)
def carryPorts (j : Fin 23) : List Wire := ((IntegerPacket.ports (Shadow7.shape j) 0).carry).map (windowNet j)
def rest (j : Fin 23) : List Wire := (carryPorts j).drop 8
def guarded (j : Fin 23) : List Wire := ports j++[flagN j, flagF j, flagU j]++RailPair.sites (upperPairs j)

theorem ports_split (j : Fin 23) :
    ports j=railA j++railB j++[gate j, flagN j, flagF j, flagU j]++clear j := rfl
theorem ports_length (j : Fin 23) : (ports j).length=EnterProof.width := rfl

/-- `inc{s}` for every block. -/
theorem inc_all : ∀ j : Fin 23, ∀ a b : Fin EnterProof.width, map j a=map j b → a=b := by decide +kernel
theorem inc (j : Fin 23) : ∀ a b : Fin EnterProof.width, map j a=map j b → a=b := inc_all j
/-- `emitted{s}` / `emitted{s}Inv`: definitional for every block. -/
theorem emitted (j : Fin 23) : Shadow7.enterP j=renameProgram (map j) EnterProof.forward := rfl
theorem emittedInv (j : Fin 23) : Shadow7.enterInvP j=renameProgram (map j) EnterProof.backward := rfl

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Geometry of the enter piece of block `j`, once for all `j : Fin 23`: interval lemmas (omega) where a
fact ranges over a long list, one `decide +kernel` over the 23 blocks where it only reads short lists. -/

/-- Arithmetic frame of block `j`: `s = 75+15j`, `2h+s ∈ {512,513}`, `3 < Wp`, `Wp+h ≤ 242`. -/
theorem frame (j : Fin 23) : start j=75+15*j.val ∧ j.val<23 ∧ 2*Shadow7.sbP (start j)+start j≤499 ∧
    498≤2*Shadow7.sbP (start j)+start j ∧ 3<Shadow7.wpP (start j) ∧ Shadow7.wpP (start j)+Shadow7.sbP (start j)≤242 := by
  have hj:=j.isLt
  refine ⟨rfl,hj,?_,?_,?_,?_⟩ <;> simp only [start,Shadow7.wpP,railP,Shadow7.sbP] <;> (try split_ifs) <;> omega

theorem upperSites (j : Fin 23) {q : Wire} (h : q∈RailPair.sites (upperPairs j)) :
    (start j+Shadow7.sbP (start j)+35≤q ∧ q+3<start j+Shadow7.sbP (start j)+35+Shadow7.wpP (start j)) ∨
    (Shadow7.sbP (start j)+805≤q ∧ q+3<Shadow7.sbP (start j)+805+Shadow7.wpP (start j)) := by
  simp only [RailPair.sites,upperPairs,List.mem_flatMap,List.mem_map,List.mem_range,List.mem_cons,
    List.not_mem_nil,or_false] at h
  obtain ⟨p,⟨i,hi,rfl⟩,hp⟩:=h
  simp only [Wire] at *
  rcases hp with rfl|rfl <;> omega

theorem portsRegion (j : Fin 23) {q : Wire} (h : q∈ports j) :
    (start j+Shadow7.sbP (start j)+31≤q ∧ q≤start j+Shadow7.sbP (start j)+34) ∨ (Shadow7.sbP (start j)+801≤q ∧ q≤Shadow7.sbP (start j)+804) ∨
    q=start j+15 ∨ (Shadow7.sbP (start j)+1574≤q ∧ q≤Shadow7.sbP (start j)+1579) ∨ (1556≤q ∧ q≤1563) := by
  simp only [ports,List.mem_cons,List.not_mem_nil,or_false] at h
  simp only [Wire] at *
  omega

theorem g0_all : ∀ j : Fin 23, pull j (gate j)=(lay j).previous := by decide +kernel
theorem xa_all : ∀ j : Fin 23, (railA j).map (pull j)=((lay j).a.drop (Shadow7.sbP (start j)+15)).take 4 := by decide +kernel
theorem xb_all : ∀ j : Fin 23, (railB j).map (pull j)=((lay j).b.drop (Shadow7.sbP (start j)+15)).take 4 := by decide +kernel
theorem na_all : ∀ j : Fin 23, Shadow7.sbP (start j)+15+4≤(lay j).a.length := by decide +kernel
theorem nb_all : ∀ j : Fin 23, Shadow7.sbP (start j)+15+4≤(lay j).b.length := by decide +kernel
theorem temps_all : ∀ j : Fin 23, ∀q∈clear j, pull j q∈(lay j).carry := by decide +kernel

theorem protected0 (j : Fin 23) : ∀q∈gate j::(railA j++railB j++clear j),
    q≠flagN j ∧ q≠flagF j ∧ q≠flagU j ∧ q∉RailPair.sites (upperPairs j) := by
  have f:=frame j
  intro q hq
  simp only [gate,railA,railB,clear,flagN,flagF,flagU,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
  refine ⟨by simp only [Wire] at *;omega,by simp only [Wire] at *;omega,by simp only [Wire] at *;omega,fun hs=>?_⟩
  have u:=upperSites j hs
  simp only [Wire] at *
  omega

/-- `Enter{s}.layout`. -/
def layout (j : Fin 23) : Aperture (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (ports j)
    (lay j) (pull j) (Shadow7.sbP (start j)+15) where
  a:=railA j
  b:=railB j
  spec:=⟨rfl,rfl,clear j,rfl⟩
  g0:=g0_all j
  xa:=xa_all j
  xb:=xb_all j
  na:=na_all j
  nb:=nb_all j
  protected0:=protected0 j
  temps:=temps_all j

/-- `Enter{s}.from_full` for every block. -/
theorem from_full (j : Fin 23) (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (p:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (PortalValues.negative S z.u)
        (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
        (pullState (pull j) raw) v)
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let next:=run (Shadow7.enterP j) m v
    next.phase=v.phase ∧ (∀q∈wires EnterProof.forward,next.basis (map j q)=(shadowRow (Shadow7.sbP (start j)) 15 z G S).testBit q) ∧
      ∀q∉wires (Shadow7.enterP j),next.basis q=v.basis q := by
  have src:=read_packed (layout j) raw v z G S p input
  apply actual_shadow_shadow7 (map j) (Shadow7.enterP j) false (Shadow7.sbP (start j)) 15 z G S small (inc j) (emitted j) v m
  intro q h
  have lim:wires EnterProof.forward ⊆ Finset.range 23 := by apply ArchiveFieldScratch.bounded;decide +kernel
  have hv:=bitAt (ports j) v.basis q ((show (ports j).length=23 from rfl) ▸ Finset.mem_range.mp (lim h))
  rw [src] at hv
  exact hv

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-- Every wire of `Shadow7.enterP j` is one of its 23 ports (from `emitted`, no evaluation). -/
theorem programCover (j : Fin 23) : wires (Shadow7.enterP j) ⊆ (ports j).toFinset := by
  rw [emitted j,renameProgram_support,forward_all]
  intro q hq
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hq
  have lt:w<(ports j).length:=Finset.mem_range.mp hw
  rw [List.mem_toFinset,map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem lt,Option.getD_some]
  exact List.getElem_mem lt
theorem notWire (j : Fin 23) {q : Wire} (h : q∉ports j) : q∉wires (Shadow7.enterP j) :=
  fun m=>h (List.mem_toFinset.mp (programCover j m))

theorem noLow (j : Fin 23) : ∀q∈guarded j, safe j q := by
  have f:=frame j
  intro q hq
  simp only [guarded,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  unfold safe
  rcases hq with (hp|hn)|hs
  · have r:=portsRegion j hp; simp only [Wire] at *; omega
  · simp only [flagN,flagF,flagU,Wire] at *; omega
  · have u:=upperSites j hs; simp only [Wire] at *; omega
theorem lowUnsafe (j : Fin 23) : ∀w∈lowA j++lowB j, ¬safe j w := by
  intro w h
  simp only [lowA,lowB,safe,List.mem_append,List.mem_range'_1,Wire] at *
  omega
theorem lowXa_all : ∀ j : Fin 23, (lowA j).map (pull j)=(lay j).a.take (Shadow7.sbP (start j)+15) := by decide +kernel
theorem lowXb_all : ∀ j : Fin 23, (lowB j).map (pull j)=(lay j).b.take (Shadow7.sbP (start j)+15) := by decide +kernel

theorem protects (j : Fin 23) (q:Wire) (h:q∈lowA j++lowB j) :
    q∉wires (Shadow7.enterP j) ∧ q≠flagN j ∧ q≠flagF j ∧ q≠flagU j ∧ q∉sites (upperPairs j) := by
  have bad:=lowUnsafe j q h
  have gone:q∉guarded j:=fun mem=>bad (noLow j q mem)
  simp only [guarded,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at gone
  exact ⟨notWire j gone.1.1,gone.1.2.1,gone.1.2.2.1,gone.1.2.2.2,gone.2⟩

/-- `Enter{s}.placement`. -/
def placement (j : Fin 23) : WordPlacement (b:=Shadow7.sbP (start j)) (k:=15) (layout j) (Shadow7.enterP j) where
  lowA:=lowA j
  lowB:=lowB j
  al:=List.length_range'
  bl:=List.length_range'
  xa:=lowXa_all j
  xb:=lowXb_all j
  aTop:=rfl
  bTop:=rfl
  protected0:=protects j
  portsCount:=rfl

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-- The carry ports of the block's first tick are fixed by the window frame: `1556..1573+h`. -/
theorem carryPorts_eq (j : Fin 23) : carryPorts j=List.range' 1556 (Shadow7.sbP (start j)+18) := by
  have hj:=j.isLt
  have hc:(IntegerPacket.ports (Shadow7.shape j) 0).carry=List.range' 1556 (Shadow7.sbP (start j)+18) := rfl
  unfold carryPorts
  rw [hc]
  conv => rhs; rw [← List.map_id (List.range' 1556 _)]
  apply List.map_congr_left
  intro q hq
  rw [List.mem_range'_1] at hq
  simp only [windowNet,net,OB5.sig,start,Shadow7.sbP,id,Wire] at hq ⊢
  split <;> omega
theorem rest_eq (j : Fin 23) : rest j=List.range' 1564 (Shadow7.sbP (start j)+10) := by
  rw [rest,carryPorts_eq,List.drop_range']
  congr 1
theorem parts (j : Fin 23) : carryPorts j=((ports j).drop 15)++rest j := by
  rw [rest_eq,carryPorts_eq]
  have e:Shadow7.sbP (start j)+18=8+(Shadow7.sbP (start j)+10):=by omega
  rw [e,← List.range'_append_1]
  rfl
theorem layCarry_all : ∀ j : Fin 23,
    (lay j).carry=List.range' 1556 (W.compactSkywalkTickPreWidth (start j)-1) := by decide +kernel
theorem layWidth_all : ∀ j : Fin 23, Shadow7.sbP (start j)+19≤W.compactSkywalkTickPreWidth (start j) := by decide +kernel
theorem guardedBound_all : ∀ j : Fin 23, ∀q∈guarded j, q<1564 ∨ Shadow7.sbP (start j)+1574≤q := by decide +kernel
theorem clearCover (j : Fin 23) : ∀q∈guarded j, q∉rest j := by
  intro q hq mem
  rw [rest_eq,List.mem_range'_1] at mem
  have:=guardedBound_all j q hq
  simp only [Wire] at *
  omega
theorem sourceCover (j : Fin 23) : ∀q∈rest j, pull j q∈(lay j).carry := by
  intro q hq
  rw [rest_eq,List.mem_range'_1] at hq
  have w:=layWidth_all j
  have hj:=j.isLt
  rw [layCarry_all j,List.mem_range'_1]
  have fix:pull j q=q:=by
    have hq':=hq
    simp only [pull,OB5.sig,start,Shadow7.sbP,Wire] at hq' ⊢
    split <;> omega
  rw [fix]
  simp only [Wire] at *
  omega

theorem frameA_all : ∀ j : Fin 23,
    (IntegerPacket.ports (Shadow7.shape j) 0).a.map (windowNet j)=lowA j++railA j := by decide +kernel
theorem frameB_all : ∀ j : Fin 23,
    (IntegerPacket.ports (Shadow7.shape j) 0).b.map (windowNet j)=lowB j++railB j := by decide +kernel
theorem framePrev_all : ∀ j : Fin 23,
    windowNet j (IntegerPacket.ports (Shadow7.shape j) 0).previous=(ports j).getD 8 0 := by decide +kernel
theorem frameExt_all : ∀ j : Fin 23, ∀r:Fin 15, let q:=windowNet j (IntegerPacket.ports (Shadow7.shape j) r).ext
    q∉ports j ∧ q∈(upperPairs j).map Prod.fst := by decide +kernel

/-- History ports of the block's ticks in the window frame: raw `s+r+1044`, or its mirror `2069-s-r`. -/
theorem histPort (j : Fin 23) (r : Fin 15) :
    let q:=windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history
    (q=start j+r.val+1044 ∧ start j+r.val+1044<1301) ∨ (q=2069-start j-r.val ∧ 1301≤start j+r.val+1044) := by
  have hr:=r.isLt
  have f:=frame j
  simp only [windowNet,net,OB5.sig,IntegerPacket.ports,Shadow7.shape]
  simp only [Wire] at *
  split <;> omega
theorem frameHist (j : Fin 23) : ∀r:Fin 15, let q:=windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history
    q∉ports j ∧ q≠flagN j ∧ q≠flagF j ∧ q≠flagU j ∧ q∉sites (upperPairs j) := by
  intro r
  have f:=frame j
  have hr:=r.isLt
  have hp:=histPort j r
  dsimp only at hp ⊢
  refine ⟨fun m=>?_,?_,?_,?_,fun m=>?_⟩
  · have x:=portsRegion j m; simp only [Wire] at *; omega
  · simp only [flagN,Wire] at *; omega
  · simp only [flagF,Wire] at *; omega
  · simp only [flagU,Wire] at *; omega
  · have x:=upperSites j m; simp only [Wire] at *; omega

/-- `Enter{s}.live`. -/
theorem live (j : Fin 23) : FramePorts_shadow7 (placement j) j where
  a:=frameA_all j
  bSites:=frameB_all j
  prev:=framePrev_all j
  carry:=by
    intro q hq
    let v:=windowNet j q
    have h : v∈carryPorts j:=List.mem_map.mpr ⟨q,hq,rfl⟩
    rw [parts j,List.mem_append] at h
    rcases h with h|h
    · exact Or.inl h
    · have absent : v∉guarded j:=fun inc=>clearCover j v inc h
      simp only [guarded,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at absent
      exact Or.inr ⟨notWire j absent.1.1,sourceCover j _ h,absent.1.2.1,absent.1.2.2.1,absent.1.2.2.2,absent.2⟩
  ext:=fun r=>⟨notWire j (frameExt_all j r).1,(frameExt_all j r).2⟩
  hist:=fun r=>let h:=frameHist j r;⟨notWire j h.1,h.2⟩

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-- `Enter{s}.ready_from_cut`, with the history cells of ticks `s..s+14` given in the pulled frame
(every block; the stock-frame form below holds for `s ≤ 255`). -/
theorem ready_from_cut_at (j : Fin 23) (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (p:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (PortalValues.negative S z.u)
        (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
        (pullState (pull j) raw) v)
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false) :
    let t:=run (Shadow7.enterP j) m v
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    t.phase=v.phase ∧ Shadow7.onRails j 0 (SkywalkRails.encode G S T.u T.v) t.basis := by
  obtain ⟨ph,body,outer⟩:=from_full j raw v z G S m small p input
  exact ⟨ph,complete_shadow7 (live j) _ G S small raw v _ p input body outer hist⟩

/-- Stock-frame history sources (`s ≤ 255`): the stock cell `base (1028+s+r)`, the end scratch `1812`,
or a carry wire of tick `s`. -/
theorem histSources_all : ∀ j : Fin 23, j.val≤12 → ∀r:Fin 15,
    let q:=pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history)
    q=base (1028+start j+r) ∨ q=1812 ∨ q∈(lay j).carry := by decide +kernel

/-- `Enter{s}.ready_from_cut` (dadon's form, `s ≤ 255`). -/
theorem ready_from_cut (j : Fin 23) (hj:j.val≤12) (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (p:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (PortalValues.negative S z.u)
        (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
        (pullState (pull j) raw) v)
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+start j+r))=false) (endScratch:raw.basis 1812=false) :
    let t:=run (Shadow7.enterP j) m v
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    t.phase=v.phase ∧ Shadow7.onRails j 0 (SkywalkRails.encode G S T.u T.v) t.basis := by
  apply ready_from_cut_at j raw v z G S m small p input
  intro r
  rcases histSources_all j hj r with eq|eq|mem
  · rw [eq];exact hist r
  · rw [eq];exact endScratch
  · exact (regValue_zero _ _).mp input.2.2.2.2.2 _ mem

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed
namespace EnterJ7
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

theorem avoid_enter (j : Fin 23) : ∀q∈pending j,q∉wires (Shadow7.enterP j) := by
  have f:=frame j
  intro q hq
  apply notWire j
  intro hp
  have r:=portsRegion j hp
  simp only [pending,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [Wire] at *
  omega
theorem zeroBand_all : ∀ j : Fin 23,
    (Shadow7.zeroSites j).all (fun q=>decide (q<Shadow7.sbP (start j)+1580 ∨ Shadow7.sbP (start j)+1583≤q)) := by decide +kernel
theorem avoid_live (j : Fin 23) : ∀q∈pending j,q∉Shadow7.zeroSites j := by
  intro q hq hz
  have b:=of_decide_eq_true (List.all_eq_true.mp (zeroBand_all j) q hz)
  simp only [pending,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [Wire] at *
  omega

/-- `Enter{s}.ready_pending` with the history sources in the pulled frame (every block). -/
theorem ready_pending_at (j : Fin 23) (raw pre:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (pull j) raw) (eraseSites (pending j) pre))
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false) :
    let t:=run (Shadow7.enterP j) m pre
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    t.phase=pre.phase ∧ Shadow7.onRails j 0 (SkywalkRails.encode G S T.u T.v) t.basis ∧
      ∀q∈pending j,t.basis q=pre.basis q := by
  have eq:=erase_run (pending j) (Shadow7.enterP j) (avoid_enter j) m pre
  have real:=ready_from_cut_at j raw (eraseSites (pending j) pre) z G S m small cut input hist
  rw [eq] at real
  refine ⟨real.1,(Shadow7.zero_congr j _ _ ?_ _ real.2).1,fun q mem=>run_preserves_outside _ m pre _ (avoid_enter j _ mem)⟩
  intro q used
  have absent:q∉pending j:=fun h=>avoid_live j _ h used
  simp [eraseSites,absent]

/-- `Enter{s}.ready_pending` (dadon's form, `s ≤ 255`). -/
theorem ready_pending (j : Fin 23) (hj:j.val≤12) (raw pre:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (pull j) raw) (eraseSites (pending j) pre))
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+start j+r))=false) (endScratch:raw.basis 1812=false) :
    let t:=run (Shadow7.enterP j) m pre
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    t.phase=pre.phase ∧ Shadow7.onRails j 0 (SkywalkRails.encode G S T.u T.v) t.basis ∧
      ∀q∈pending j,t.basis q=pre.basis q := by
  apply ready_pending_at j raw pre z G S m small cut input
  intro r
  rcases histSources_all j hj r with eq|eq|mem
  · rw [eq];exact hist r
  · rw [eq];exact endScratch
  · exact (regValue_zero _ _).mp input.2.2.2.2.2 _ mem
end EnterJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed EnterProof PortalValues Partial
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

theorem highA_all : ∀ j : Fin 23,
    ((upperPairs j).map Prod.fst).map (pull j)=(lay j).a.drop (Shadow7.sbP (start j)+19) := by decide +kernel
theorem highB_all : ∀ j : Fin 23,
    ((upperPairs j).map Prod.snd).map (pull j)=(lay j).b.drop (Shadow7.sbP (start j)+19) := by decide +kernel
theorem highLa_all : ∀ j : Fin 23, Shadow7.sbP (start j)+19≤(lay j).a.length := by decide +kernel
theorem highLb_all : ∀ j : Fin 23, Shadow7.sbP (start j)+19≤(lay j).b.length := by decide +kernel
theorem savedLive (j : Fin 23) : ∀q∈(upperPairs j).map Prod.snd,q∉ports j := by
  have f:=frame j
  intro q hq hp
  simp only [upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp] at hq
  obtain ⟨i,hi,rfl⟩:=hq
  have r:=portsRegion j hp
  simp only [Wire] at *
  omega

/-- `Enter{s}.high_from_cut` for every block. -/
theorem high_from_cut (j : Fin 23) (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (packed:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (pull j) raw) cut)
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    regValue (saved j) (run (Shadow7.enterP j) m cut).basis=
      if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0 :=by
  have high:=SavedHigh.stored (Shadow7.sbP (start j)+19) raw cut z G S packed input (layout j).g0
    (highA_all j) (highB_all j) (highLa_all j) (highLb_all j)
  obtain ⟨_,bits,outer⟩:=from_full j raw cut z G S m small packed input
  have bulk:=regValue_congr ((upperPairs j).map Prod.snd) (run (Shadow7.enterP j) m cut).basis cut.basis
    (fun q hit=>outer q (notWire j (savedLive j q hit)))
  apply SavedHigh.assemble (Shadow7.sbP (start j)) 15 z G S _ (Shadow7.sbP (start j)+1574) (Shadow7.sbP (start j)+1575) (Shadow7.sbP (start j)+1576) _
  · exact bits 12 (by rw [forward_all];decide)
  · exact bits 13 (by rw [forward_all];decide)
  · exact bits 14 (by rw [forward_all];decide)
  · exact bulk.trans high

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

-- ===== ShadowGeometry =====
/-! Shadow7 window geometry (generated by helpers/staircase82/shadow/port.py from StairSideA).
Every declaration is the stock one with the Shadow7 coordinates; statements unchanged otherwise. -/

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem scratchX_low (e k : Nat) (he : e ≤ 369) : scratchX e k = scratchS e k := if_pos he

theorem loadPortsXP_low (e f : Nat) (he : e ≤ 369) : loadPortsXP e f = loadPortsWP e f := by
  rw [loadPortsXP, loadPortsWP, List.map_congr_left (fun k _ => scratchX_low e k he)]

theorem restorePortsXP_low (e : Nat) (he : e ≤ 369) : restorePortsXP e = restorePortsWP e := by
  rw [restorePortsXP, restorePortsWP, List.map_congr_left (fun k _ => scratchX_low e k he)]

theorem loadPortsXP_length (e f : Nat) : (loadPortsXP e f).length = 155 := by
  simp [loadPortsXP, cellsLoadP]

theorem restorePortsXP_length (e : Nat) : (restorePortsXP e).length = 150 := by
  simp [restorePortsXP, cellsRestoreP]

theorem scratchW_def (t k : Nat) : scratchW t k = if 1556 + k < e0P t then 1556 + k else 1566 + k := rfl

theorem scratchW_bounds (t k : Nat) : 1556 + k ≤ scratchW t k ∧ scratchW t k ≤ 1566 + k := by
  by_cases h : 1556 + k < e0P t
  · rw [scratchW_def, if_pos h]; omega
  · rw [scratchW_def, if_neg h]; omega

/-- The scratch never meets the anchored block `e0(t)..e0(t)+9`. -/
theorem scratchW_ne_e0 (t k i : Nat) (hi : i < 10) : scratchW t k ≠ e0P t + i := by
  by_cases h : 1556 + k < e0P t
  · rw [scratchW_def, if_pos h]; exact Nat.ne_of_lt (by omega)
  · rw [scratchW_def, if_neg h]; exact Nat.ne_of_gt (by omega)

theorem scratchW_inj (t k k' : Nat) (h : scratchW t k = scratchW t k') : k = k' := by
  have e1 := scratchW_def t k
  have e2 := scratchW_def t k'
  by_cases a : 1556 + k < e0P t <;> by_cases b : 1556 + k' < e0P t <;> simp only [a, b, if_true, if_false] at e1 e2 <;>
    omega

theorem scratchW_low (t k : Nat) (h : 1556 + k < e0P t) : scratchW t k = 1556 + k := if_pos h

theorem scratchW_le (t k : Nat) (hk : k < 134) : scratchW t k ≤ 1699 := by
  have := scratchW_bounds t k; omega

theorem scratchS_def (t k : Nat) : scratchS t k =
    if scratchW t k + t < 2068 then scratchW t k else bTopP t + 4 + (scratchW t k + t - 2068) := rfl

/-- A carry wire of the stock tick `t` is not moved. -/
theorem scratchS_eq (t k : Nat) (ht : t < 512) (h : scratchW t k + t < 2068) : scratchS t k = scratchW t k := by
  rw [scratchS_def, if_pos h]

/-- Beyond the stock carry the port sits 766 below its raw wire, in `[1302-t, 933]`. -/
theorem scratchS_high (t k : Nat) (ht : t < 512) (hk : k < 134) (h : 2068 ≤ scratchW t k + t) :
    scratchS t k = scratchW t k - 766 := by
  have l := scratchW_le t k hk
  have b := scratchW_bounds t k
  rw [scratchS_def, if_neg (by omega), bTopP_late t (by omega) (by omega)]
  omega

/-- Every window loader up to tick 368 keeps the raw scratch list. -/
theorem scratchS_window (t k : Nat) (ht : t ≤ 368) (hk : k < 134) : scratchS t k = scratchW t k :=
  scratchS_eq t k (by omega) (by have := scratchW_le t k hk; omega)

theorem scratchS_cases (t k : Nat) (ht : t < 512) (hk : k < 134) :
    (scratchS t k = scratchW t k ∧ 1556 ≤ scratchS t k ∧ scratchS t k ≤ 1699 ∧ scratchS t k + t < 2068) ∨
    (369 ≤ t ∧ 1302 ≤ scratchS t k + t ∧ scratchS t k ≤ 933) := by
  have b := scratchW_bounds t k
  have l := scratchW_le t k hk
  by_cases h : scratchW t k + t < 2068
  · left; rw [scratchS_eq t k ht h]; omega
  · right; rw [scratchS_high t k ht hk (by omega)]; omega

theorem scratchS_ne_e0 (t k i : Nat) (ht : t < 512) (hk : k < 134) (hi : i < 10) : scratchS t k ≠ e0P t + i := by
  have he : 1574 ≤ e0P t := by unfold e0P; omega
  rcases scratchS_cases t k ht hk with ⟨h1, -, -⟩ | ⟨-, -, h2⟩
  · rw [h1]; exact scratchW_ne_e0 t k i hi
  · exact Nat.ne_of_lt (by omega)

theorem scratchS_inj (t k k' : Nat) (ht : t < 512) (hk : k < 134) (hk' : k' < 134) (h : scratchS t k = scratchS t k') :
    k = k' := by
  apply scratchW_inj t
  have b := scratchW_bounds t k
  have b' := scratchW_bounds t k'
  have l := scratchW_le t k hk
  have l' := scratchW_le t k' hk'
  by_cases a : scratchW t k + t < 2068 <;> by_cases a' : scratchW t k' + t < 2068
  · rw [scratchS_eq t k ht a, scratchS_eq t k' ht a'] at h; exact h
  · rw [scratchS_eq t k ht a, scratchS_high t k' ht hk' (by omega)] at h; omega
  · rw [scratchS_high t k ht hk (by omega), scratchS_eq t k' ht a'] at h; omega
  · rw [scratchS_high t k ht hk (by omega), scratchS_high t k' ht hk' (by omega)] at h; omega

/-- A carry wire of the stock tick `e`: the plain port. -/
theorem scratchX_plain (e k : Nat) (he : 370 ≤ e) (h : k + e < 512) : scratchX e k = 1556 + k := by
  unfold scratchX; rw [if_neg (by omega), if_pos (by omega)]

/-- Beyond the stock carry: the released B-rail wire `790+k`. -/
theorem scratchX_host (e k : Nat) (he : 370 ≤ e) (hi : e ≤ 512) (h : 512 ≤ k + e) : scratchX e k = 790 + k := by
  unfold scratchX; rw [if_neg (by omega), if_neg (by omega), bTopP_late e (by omega) hi]; omega

theorem scratchX_cases (e k : Nat) (he : e < 512) (hk : k < 134) :
    (e ≤ 369 ∧ scratchX e k = scratchS e k) ∨ (370 ≤ e ∧ k + e < 512 ∧ scratchX e k = 1556 + k) ∨
    (379 ≤ e ∧ 512 ≤ k + e ∧ scratchX e k = 790 + k) := by
  by_cases a : e ≤ 369
  · left; exact ⟨a, scratchX_low e k a⟩
  · by_cases b : k + e < 512
    · right; left; exact ⟨by omega, b, scratchX_plain e k (by omega) b⟩
    · right; right; exact ⟨by omega, by omega, scratchX_host e k (by omega) (by omega) (by omega)⟩

theorem scratchX_inj (e k k' : Nat) (he : e < 512) (hk : k < 134) (hk' : k' < 134) (h : scratchX e k = scratchX e k') :
    k = k' := by
  rcases scratchX_cases e k he hk with ⟨a, e1⟩ | ⟨a, b, e1⟩ | ⟨a, b, e1⟩ <;>
    rcases scratchX_cases e k' he hk' with ⟨a', e2⟩ | ⟨a', b', e2⟩ | ⟨a', b', e2⟩ <;> rw [e1, e2] at h <;>
    first | exact scratchS_inj e k k' he hk hk' h | omega

theorem loadPortsWP_length (t f : Nat) : (loadPortsWP t f).length = 155 := by
  simp [loadPortsWP, cellsLoadP]

theorem restorePortsWP_length (t : Nat) : (restorePortsWP t).length = 150 := by
  simp [restorePortsWP, cellsRestoreP]

theorem loadPortsWP_scratch (t f k : Nat) (hk : k < 132) : (loadPortsWP t f).getD (23 + k) 0 = scratchS t k := by
  have hc : (cellsLoadP t ++ [f, f+1, f+2]).length = 23 := by simp [cellsLoadP]
  rw [loadPortsWP, List.getD_append_right _ _ _ _ (by omega), hc, show 23 + k - 23 = k by omega]
  simp [List.getD_eq_getElem?_getD, hk]

theorem loadPortsWP_flag (t f i : Nat) (hi : i < 3) : (loadPortsWP t f).getD (20 + i) 0 = f + i := by
  have hc : (cellsLoadP t).length = 20 := by simp [cellsLoadP]
  rw [loadPortsWP, List.getD_append _ _ _ _ (by simp [hc]; omega), List.getD_append_right _ _ _ _ (by omega), hc]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

theorem loadPortsWP_cell (t f k : Nat) (hk : k < 20) : (loadPortsWP t f).getD k 0 = (cellsLoadP t).getD k 0 := by
  have hc : (cellsLoadP t).length = 20 := by simp [cellsLoadP]
  rw [loadPortsWP, List.getD_append _ _ _ _ (by simp [hc]; omega), List.getD_append _ _ _ _ (by omega)]

theorem restorePortsWP_scratch (t k : Nat) (hk : k < 134) : (restorePortsWP t).getD (16 + k) 0 = scratchS t k := by
  have hc : (cellsRestoreP t).length = 16 := by simp [cellsRestoreP]
  rw [restorePortsWP, List.getD_append_right _ _ _ _ (by omega), hc, show 16 + k - 16 = k by omega]
  simp [List.getD_eq_getElem?_getD, hk]

theorem restorePortsWP_cell (t k : Nat) (hk : k < 16) : (restorePortsWP t).getD k 0 = (cellsRestoreP t).getD k 0 := by
  have hc : (cellsRestoreP t).length = 16 := by simp [cellsRestoreP]
  rw [restorePortsWP, List.getD_append _ _ _ _ (by omega)]

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Challenge ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem counts_leaveAdjust (s : Nat) (hw : 1 ≤ wpP s) :
    Counts (leaveAdjust s) 0 (wpP s - 1) (wpP s - 1) (5*wpP s - 2) :=
  ((counts_cxsG _ _).app ((counts_addG _ _ _ (by first | omega | (simp <;> omega))).app (counts_cxsG _ _))).congr
    (by simp) (by simp) (by simp) (by first | omega | (simp <;> omega))

theorem counts_leaveBarrel (s : Nat) : Counts (leaveBarrel s) (4*wpP s + 11) 0 0 (12*wpP s + 97) :=
  ((((counts_stageG _ _ _ _ _).app (counts_stageG _ _ _ _ _)).app (counts_stageG _ _ _ _ _)).app
    (counts_stageG _ _ _ _ _)).congr (by omega) rfl rfl
    (by simp only [controlsP0, controlsP1, controlsP2, controlsP3, List.length_cons, List.length_nil]; omega)

theorem counts_leaveJoin (s : Nat) (hL : lowsP s ≤ 18) : Counts (leaveJoin s) 50 0 0 (118 - lowsP s) := by
  have hw := counts_wordG 1614 (columnsP s)
  have e1 : (columnsP s).length = 18 := by simp [columnsP]
  have e2 : (columnsP s).countP (fun r => r.hot.isSome) = 16 := by
    simp only [columnsP, List.countP_map]
    show (List.range 18).countP (fun i => (if i < 16 then some (tagsP.getD i 0) else none : Option Wire).isSome) = 16
    decide
  have e3 : (columnsP s).countP (fun r => r.low) = lowsP s := by
    simp only [columnsP, List.countP_map]
    show (List.range 18).countP (fun i => decide (i < lowsP s)) = lowsP s
    rw [countP_range_lt]; omega
  rw [e1, e2, e3] at hw
  exact ((counts_digitsG _ _ _ _ _ _).app hw).congr (by omega) rfl rfl (by omega)

theorem counts_leaveLowStore (s : Nat) (hL : 1 ≤ lowsP s) :
    Counts (leaveLowStore s) (lowsP s) (lowsP s - 1) (lowsP s + 1) (6*lowsP s + 4) := by
  have a := counts_mapG (List.range (lowsP s)) (fun i => Gate.ccx 1556 (a0P s + i) (b0P s + i)) true false false
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have b := counts_xsG ((List.range (lowsP s)).map (b0P s + ·))
  have c := counts_addG ((List.range (lowsP s - 1)).map (1559 + ·)) ((List.range (lowsP s)).map (b0P s + ·)) 1558
    (by first | omega | (simp <;> omega))
  exact ((((((⟨rfl, rfl, rfl, rfl⟩ :
      Counts [.cx (e0P s + 3) 1560, .cx 1559 1560, .pop (e0P s + 3) (e0P s + 4) 1559] 0 0 1 3).app a).app b).app c).app
    b).app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop (b0P s - 1) 1557 1558, .cx (a0P s - 1) 1557, .x 1557] 0 0 1 3)).congr
    (by simp) (by simp) (by first | omega | (simp <;> omega)) (by first | omega | (simp <;> omega))

theorem counts_leaveStoreMapped (s : Nat) (hL : lowsP s ≤ wpP s + 15) :
    Counts (leaveStoreMapped s) 0 (wpP s + 19) (wpP s + 18) (4*wpP s + 79) := by
  let L := lowsP s; let top := a0P s + L - 1; let H := wpP s + 15 - L
  let hi := (List.range H).map (fun i => bankW s (L+i))
  let seq := fun i => if i = 0 then top else bankW s (L+i-1)
  let seq2 := (List.range (L+1)).map (b0P s - 1 + ·)
  have c1 := counts_chainG (storeW s) seq (⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx (storeW s (H+1)) 1557, .x 1557] 0 0 0 2) 0 (H+1)
  have c2 := counts_chainG (1558 + ·) (b0P s - 1 + ·)
    (⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx (1558+(L+1)) 1556, .x 1556] 0 0 0 2) 0 (L+1)
  have x1 := counts_xsG hi
  have x2 := counts_xsG hi.reverse
  have x3 := counts_xsG seq2
  have x4 := counts_xsG seq2.reverse
  exact ((((((((((⟨rfl, rfl, rfl, rfl⟩ : Counts [.make (top-2) (top-1) 1558, .x 1558, .x top] 0 1 0 3).app
    x1).app c1).app x2).app (⟨rfl, rfl, rfl, rfl⟩ :
      Counts [.x top, .x 1558, .pop (top-2) (top-1) 1558, .make 1556 1557 1558, .x 1558] 0 1 1 5)).app
    x3).app c2).app x4).app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.x 1558] 0 0 0 1))).congr
    (by simp) (by simp [H, L]; omega) (by simp [H, L]; omega) (by simp [hi, seq2, H, L]; omega)

theorem counts_leaveLowClose (s : Nat) : Counts (leaveLowClose s) (lowsP s + 1) 0 0 (4*lowsP s + 19) := by
  have a := counts_xsG ((List.range 15).map (s+16+·))
  have b := counts_mapG (List.range (lowsP s + 1)) (fun i => Gate.cx (e0P s + 5) (b0P s - 1 + i)) false false false
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have c := counts_flatCswap (lowsP s + 1) (s+30) (fun i => b0P s - 1 + i) (fun i => a0P s - 1 + i)
  exact ((a.app b).app c).congr (by simp) (by simp) (by simp) (by first | omega | (simp <;> omega))

theorem counts_leaveClose (s : Nat) (hn : 3 ≤ wpP (s+15)) :
    Counts (leaveClose s) 0 5 5 (21 + 3*(wpP (s+15) + 3)) := by
  have a := counts_eventsG (e0P s + 7) (e0P s + 4)
    [(OB5.sig (s+14) (s+1044), 1556), (OB5.sig (s+14) (s+1045), 1559), (OB5.sig (s+14) (s+1046), 1560),
     (OB5.sig (s+14) (s+1047), 1561), (OB5.sig (s+14) (s+1048), 1562)]
  have b := counts_swapsG (movesP s)
  exact (a.app b).congr (by simp) (by simp) (by simp) (by simp [movesP]; omega)

/-- The whole leave, for every block start `s` with a sane geometry. -/
theorem counts_leaveOps (s : Nat) (hw : 4 ≤ wpP s) (hL1 : 1 ≤ lowsP s) (hL2 : lowsP s ≤ 18)
    (hn : 3 ≤ wpP (s+15)) :
    Counts (leaveOps s) (4*wpP s + 2*lowsP s + 115) (2*wpP s + lowsP s + 94) (2*wpP s + lowsP s + 93)
      (21*wpP s + 9*lowsP s + 750 + 3*wpP (s+15)) := by
  have := ((((((((((((((((counts_leaveFix0 s (sbP s)).app (counts_leaveFix1 s (sbP s))).app
    (counts_leaveFix2 s (sbP s))).app (counts_leaveFix3 s (sbP s))).app (counts_leaveFix4 s (sbP s))).app
    (counts_leaveFix5 s (sbP s))).app (counts_leaveAdjust s (by omega))).app (counts_leaveBarrel s)).app
    (counts_leaveFix8 s (sbP s))).app (counts_leaveJoin s hL2)).app (counts_leaveFix10 s (sbP s))).app
    (counts_leaveFix11 s (sbP s))).app (counts_leaveFix12 s (sbP s))).app (counts_leaveLowStore s hL1)).app
    (counts_leaveStoreMapped s (by omega))).app (counts_leaveLowClose s)).app (counts_leaveClose s hn)
  exact this.congr (by omega) (by omega) (by omega) (by omega)

/-- The portal at tick `t`. -/
theorem counts_portalOps (t : Nat) (hw : 5 ≤ wpP t) :
    Counts (portalOps t) (2*wpP t + 1) (3*wpP t - 5) (3*wpP t - 5) (18*wpP t - 2) := by
  let w := wpP t; let aBot := a0P t; let bBot := 802 + sbP t
  let rA := (List.range w).map (aBot + ·); let rB := (List.range w).map (bBot + ·)
  let bA := (List.range (w-3)).map (aBot + 3 + ·); let bB := (List.range (w-3)).map (bBot + 3 + ·)
  let sgn := e0P t + 5; let G := t + 15; let f3 := e0P t + 3; let f4 := e0P t + 4
  have zAB : (rA.zip rB).length = w := by simp [rA, rB]
  have zb : (bA.zip bB).length = w - 3 := by simp [bA, bB]
  have p1 := counts_exchangeG G (rA.zip rB)
  have p2 := counts_cxsG sgn rB
  have p3 := counts_latchG true none 1556 1557 ((List.range (w-2)).map (fun i => (aBot+2+i, 1558+i)))
  have p4 := counts_latchG false (some f3) f4 bBot ((List.range (w-1)).map (fun i => (bBot+1+i, 1556+i)))
  have p5 := counts_addG ((List.range (w-4)).map (1557 + ·)) bB 1556 (by simp [bB]; omega)
  have p6 := counts_mapG (bA.zip bB) (fun p => Gate.ccx f4 p.1 p.2) true false false (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)
  have p7 := counts_transferG (bA.zip bB)
  have p8 := counts_cxsG sgn [bBot, bBot+1, bBot+2]
  have p9 := counts_exchangeG G [(aBot, bBot), (aBot+1, bBot+1), (aBot+2, bBot+2)]
  exact ((((((((((((((⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx (aBot + w - 1) sgn, .cx (bTopP t) sgn] 0 0 0 2).app
    p1).app p2).app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.make aBot (aBot+1) 1557] 0 1 0 1)).app p3).app
    (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop aBot (aBot+1) 1557, .cx 1556 f3, .cx f3 1556] 0 0 1 3)).app p4).app
    (⟨rfl, rfl, rfl, rfl⟩ : Counts [.x (aBot+2), .make (bBot+2) (aBot+2) 1556] 0 1 0 2)).app p5).app p6).app
    (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop (bBot+2) (aBot+2) 1556, .x (aBot+2)] 0 0 1 2)).app p7).app p8).app p9).congr
    (by simp [zAB, zb, w] at *; omega) (by simp [zAB, zb, w] at *; omega) (by simp [zAB, zb, w] at *; omega)
    (by simp [zAB, zb, rB, w] at *; omega)

theorem counts_parkOps (e : Nat) : Counts (parkOps e) 0 0 0 9 := (counts_swapsG _).congr rfl rfl rfl rfl

theorem window_geom : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    31 ≤ wpP (start j) ∧ 10 ≤ lowsP (start j) ∧ lowsP (start j) ≤ 11 ∧ 38 ≤ wpP (start j + 15) := by
  decide

theorem leave_counts (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    toffoliCount (leaveP j) = 6*wpP (start j) + 3*lowsP (start j) + 209 ∧
    toffoliCount (leaveInvP j) = 6*wpP (start j) + 3*lowsP (start j) + 208 ∧
    measurementCount (leaveP j) = 2*wpP (start j) + lowsP (start j) + 93 ∧
    measurementCount (leaveInvP j) = 2*wpP (start j) + lowsP (start j) + 94 ∧
    gateSlots (leaveP j) = 23*wpP (start j) + 10*lowsP (start j) + 843 + 3*wpP (start j + 15) ∧
    gateSlots (leaveInvP j) = 23*wpP (start j) + 10*lowsP (start j) + 844 + 3*wpP (start j + 15) := by
  obtain ⟨g1,g2,g3,g4⟩ := window_geom j h0 (by omega)
  obtain ⟨t1,t2,m1,m2,s1,s2⟩ := (counts_leaveOps (start j) (by omega) (by omega) (by omega) (by omega)).programs
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [leaveP, t1]; omega
  · rw [leaveInvP, t2]; omega
  · rw [leaveP, m1]
  · rw [leaveInvP, m2]
  · rw [leaveP, s1]; omega
  · rw [leaveInvP, s2]; omega

theorem enter_counts (j : Fin 23) :
    toffoliCount (enterP j) = 18 ∧ toffoliCount (enterInvP j) = 18 ∧
    measurementCount (enterP j) = 6 ∧ measurementCount (enterInvP j) = 6 ∧
    gateSlots (enterP j) = 92 ∧ gateSlots (enterInvP j) = 92 :=
  (counts_enterFix _ _).programs

theorem portal_counts (t : Nat) (hw : 5 ≤ wpP t) :
    toffoliCount (portalP t) = 5*wpP t - 4 ∧ toffoliCount (portalInvP t) = 5*wpP t - 4 ∧
    measurementCount (portalP t) = 3*wpP t - 5 ∧ measurementCount (portalInvP t) = 3*wpP t - 5 ∧
    gateSlots (portalP t) = 21*wpP t - 7 ∧ gateSlots (portalInvP t) = 21*wpP t - 7 := by
  obtain ⟨t1,t2,m1,m2,s1,s2⟩ := (counts_portalOps t hw).programs
  exact ⟨by rw [portalP, t1]; omega, by rw [portalInvP, t2]; omega, by rw [portalP, m1], by rw [portalInvP, m2],
    by rw [portalP, s1]; omega, by rw [portalInvP, s2]; omega⟩

theorem park_counts (e : Nat) :
    toffoliCount (parkP e) = 0 ∧ toffoliCount (parkInvP e) = 0 ∧
    measurementCount (parkP e) = 0 ∧ measurementCount (parkInvP e) = 0 ∧
    gateSlots (parkP e) = 9 ∧ gateSlots (parkInvP e) = 9 :=
  (counts_parkOps e).programs

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Challenge ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem moveRows_length (s : Nat) : (moveRows s).length = 16 := by simp [moveRows]

theorem counts_leaveFix5Move (s h : Nat) : Counts (leaveFix5Move s h) 16 20 0 91 := by
  have a : Counts ((leaveFix5 s h).take 27) 0 19 0 27 := ⟨rfl, rfl, rfl, rfl⟩
  have b : Counts ((leaveFix5 s h).drop 43) 0 1 0 16 := ⟨rfl, rfl, rfl, rfl⟩
  have r := counts_rowGates (e0P s + 6) (moveRows s)
  rw [moveRows_length] at r
  exact (a.app (r.app b)).congr rfl rfl rfl rfl

theorem counts_leaveJoinMove (s : Nat) (hL : lowsP s ≤ 18) : Counts (leaveJoinMove s) 34 0 0 (102 - lowsP s) := by
  have hw := counts_wordG 1614 (columnsP s)
  have e1 : (columnsP s).length = 18 := by simp [columnsP]
  have e2 : (columnsP s).countP (fun r => r.hot.isSome) = 16 := by
    simp only [columnsP, List.countP_map]
    show (List.range 18).countP (fun i => (if i < 16 then some (tagsP.getD i 0) else none : Option Wire).isSome) = 16
    decide
  have e3 : (columnsP s).countP (fun r => r.low) = lowsP s := by
    have hl := (counts_leaveJoin s hL).len
    have hd := (counts_digitsG (tagsP.getD · 0) (fun i => a0P s + i) (e0P s + 6) 1613 0 16).len
    have hw' := hw.len
    simp only [leaveJoin, List.length_append] at hl
    rw [e1, e2] at hw'
    omega
  rw [e1, e2, e3] at hw
  exact ((counts_keptG _ _ 1613 0 16).app hw).congr (by omega) rfl rfl (by omega)

theorem counts_leaveMoveOps (s : Nat) (hw : 4 ≤ wpP s) (hL1 : 1 ≤ lowsP s) (hL2 : lowsP s ≤ 18)
    (hn : 3 ≤ wpP (s+15)) :
    Counts (leaveMoveOps s) (4*wpP s + 2*lowsP s + 99) (2*wpP s + lowsP s + 94) (2*wpP s + lowsP s + 93)
      (21*wpP s + 9*lowsP s + 766 + 3*wpP (s+15)) := by
  have := ((((((((((((((((counts_leaveFix0 s (sbP s)).app (counts_leaveFix1 s (sbP s))).app
    (counts_leaveFix2 s (sbP s))).app (counts_leaveFix3 s (sbP s))).app (counts_leaveFix4 s (sbP s))).app
    (counts_leaveFix5Move s (sbP s))).app (counts_leaveAdjust s (by omega))).app (counts_leaveBarrel s)).app
    (counts_leaveFix8 s (sbP s))).app (counts_leaveJoinMove s hL2)).app (counts_leaveFix10 s (sbP s))).app
    (counts_leaveFix11 s (sbP s))).app (counts_leaveFix12 s (sbP s))).app (counts_leaveLowStore s hL1)).app
    (counts_leaveStoreMapped s (by omega))).app (counts_leaveLowClose s)).app (counts_leaveClose s hn)
  have base := counts_leaveOps s hw hL1 hL2 hn
  exact this.congr (by omega) (by omega) (by omega) (by omega)

theorem leaveMove_counts (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    toffoliCount (leaveMoveP j) = 6*wpP (start j) + 3*lowsP (start j) + 193 ∧
    toffoliCount (leaveMoveInvP j) = 6*wpP (start j) + 3*lowsP (start j) + 192 ∧
    measurementCount (leaveMoveP j) = 2*wpP (start j) + lowsP (start j) + 93 ∧
    measurementCount (leaveMoveInvP j) = 2*wpP (start j) + lowsP (start j) + 94 ∧
    gateSlots (leaveMoveP j) = 23*wpP (start j) + 10*lowsP (start j) + 859 + 3*wpP (start j + 15) ∧
    gateSlots (leaveMoveInvP j) = 23*wpP (start j) + 10*lowsP (start j) + 860 + 3*wpP (start j + 15) := by
  obtain ⟨g1,g2,g3,g4⟩ := window_geom j h0 (by omega)
  obtain ⟨t1,t2,m1,m2,s1,s2⟩ := (counts_leaveMoveOps (start j) (by omega) (by omega) (by omega) (by omega)).programs
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [leaveMoveP, t1]; omega
  · rw [leaveMoveInvP, t2]; omega
  · rw [leaveMoveP, m1]
  · rw [leaveMoveInvP, m2]
  · rw [leaveMoveP, s1]; omega
  · rw [leaveMoveInvP, s2]; omega

theorem leaveOps_shape (s : Nat) :
    leaveOps s = moveA s ++ (moveMux s ++ (moveB s ++ (moveDig s ++ moveC s))) := by
  have e := fix5_split s (sbP s)
  unfold leaveOps moveA moveMux moveB moveDig moveC leaveJoin
  conv_lhs => rw [e]
  simp only [List.append_assoc]

theorem leaveMoveOps_shape (s : Nat) :
    leaveMoveOps s = moveA s ++ (rowGates (e0P s + 6) (moveRows s) ++ (moveB s ++ (moveKept s ++ moveC s))) := by
  unfold leaveMoveOps moveA moveB moveKept moveC leaveJoinMove leaveFix5Move
  simp only [List.append_assoc]

theorem mux_forward (s : Nat) : GateMirror.forward (moveMux s) = MoveChain.mux (e0P s + 6) (moveRows s) := by
  have e : sbP s + 1580 = e0P s + 6 := by unfold e0P; omega
  unfold moveMux
  rw [← e]
  rfl

theorem rowsD_moveRows (s : Nat) : rowsD (tagsP.getD · 0) (fun i => a0P s + i) 0 16 = moveRows s := rfl

theorem dig_forward (s : Nat) :
    GateMirror.forward (moveDig s) = MoveChain.weave (e0P s + 6) (moveRows s) (GateMirror.forward (moveKept s)) := by
  unfold moveDig moveKept; rw [digits_weave, rowsD_moveRows]

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
/-- Segment 6 is `adjust` on the parametric bank and pool. -/
theorem forward_leaveAdjust (s : Nat) : GateMirror.forward (leaveAdjust s) =
    HighBankAdjust.adjust ((List.range (wpP s)).map (bankW s)) ((List.range (wpP s - 1)).map (poolW s)) (e0P s + 6) 1597 :=
  forward_adjustG _ _ _ _

/-- Segment 7 is the four barrel stages. -/
theorem forward_leaveBarrel (s : Nat) : GateMirror.forward (leaveBarrel s) =
    HighBankBarrel.stage 1613 (bankW s) controlsP0 1 (wpP s) ++ HighBankBarrel.stage 1613 (bankW s) controlsP1 2 (wpP s + 1) ++
    HighBankBarrel.stage 1613 (bankW s) controlsP2 4 (wpP s + 3) ++ HighBankBarrel.stage 1613 (bankW s) controlsP3 8 (wpP s + 7) := by
  simp only [leaveBarrel, forward_app, forward_stageG]

/-- Segment 9 is `digitPass ++ wordPass` at the parametric columns. -/
theorem forward_leaveJoin (s : Nat) : GateMirror.forward (leaveJoin s) =
    HighBankJoin.digits (tagsP.getD · 0) (fun i => a0P s + i) (e0P s + 6) 1613 0 16 ++ HighBankJoin.word 1614 (columnsP s) := by
  simp only [leaveJoin, forward_app, forward_digitsG, forward_wordG]

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem rail_facts (s : Nat) (h0 : 90 ≤ s) (h1 : s ≤ 405) :
    sbP s + 54 ≤ railP s ∧ railP s ≤ 258 ∧ sbP s = (513 - s)/2 - 7 ∧ (s ≤ 255 ∨ railP s = 513 - s) := by
  unfold railP sbP; split_ifs <;> omega

theorem enter_proper (s : Nat) (h0 : 90 ≤ s) (h1 : s ≤ 405) : ∀ g ∈ enterOps s, proper g = true := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts s h0 h1
  unfold enterOps enterFix
  simp only [List.forall_mem_cons, List.forall_mem_nil, proper, decide_eq_true_eq, and_true, ne_eq]
  and_intros <;> first | trivial | (intro x hx; cases hx) | omega | exact Nat.ne_of_gt (by omega) | exact Nat.ne_of_lt (by omega)

theorem enterP_physical (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 22) :
    GatePhysical (enterP j) ∧ GatePhysical (enterInvP j) :=
  physical_of_proper _ (enter_proper (start j) (by simp [start]; omega) (by simp [start]; omega))

theorem park_proper (e : Nat) (h0 : 90 ≤ e) (h1 : e ≤ 405) : ∀ g ∈ parkOps e, proper g = true := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts e h0 h1
  have he : e0P e = 1574 + sbP e := rfl
  have hb : bTopP e = 785 + railP e := rfl
  unfold parkOps swapsG swapG
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.forall_mem_nil, proper, decide_eq_true_eq, and_true, ne_eq]
  and_intros <;> first | trivial | (intro x hx; cases hx) | omega | exact Nat.ne_of_gt (by omega) | exact Nat.ne_of_lt (by omega)

theorem parkP_physical (e : Nat) (h0 : 90 ≤ e) (h1 : e ≤ 405) :
    GatePhysical (parkP e) ∧ GatePhysical (parkInvP e) :=
  physical_of_proper _ (park_proper e h0 h1)

theorem portal_proper90 : (portalOps 90).all proper = true := by decide +kernel

theorem portal_proper405 : (portalOps 405).all proper = true := by decide +kernel

theorem portalP_physical90 : GatePhysical (portalP 90) ∧ GatePhysical (portalInvP 90) :=
  physical_of_proper _ (List.all_eq_true.mp portal_proper90)

theorem portalP_physical405 : GatePhysical (portalP 405) ∧ GatePhysical (portalInvP 405) :=
  physical_of_proper _ (List.all_eq_true.mp portal_proper405)

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Challenge ECDSAAdd.Baselines ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
/-- Every archive piece costs what dadon's archive at 240 costs (same codec program, renamed; same move counts). -/
theorem archive_counts (j : Fin 23) (e : Nat) (d : Bool) :
    toffoliCount (archiveLoadP j d) = toffoliCount (archiveLoad240 d) ∧
    measurementCount (archiveLoadP j d) = measurementCount (archiveLoad240 d) ∧
    gateSlots (archiveLoadP j d) = gateSlots (archiveLoad240 d) ∧
    toffoliCount (archiveRestoreP j d) = toffoliCount (archiveRestore240 d) ∧
    measurementCount (archiveRestoreP j d) = measurementCount (archiveRestore240 d) ∧
    gateSlots (archiveRestoreP j d) = gateSlots (archiveRestore240 d) ∧
    toffoliCount (exitLoadP e d) = toffoliCount (archiveLoad240 d) ∧
    measurementCount (exitLoadP e d) = measurementCount (archiveLoad240 d) ∧
    gateSlots (exitLoadP e d) = gateSlots (archiveLoad240 d) ∧
    toffoliCount (exitRestoreP e d) = toffoliCount (archiveRestore240 d) ∧
    measurementCount (exitRestoreP e d) = measurementCount (archiveRestore240 d) ∧
    gateSlots (exitRestoreP e d) = gateSlots (archiveRestore240 d) := by
  have r1 : ∀ (f : Wire → Wire) (p : Program), toffoliCount (renameProgram f p) = toffoliCount p :=
    fun f p => (renameProgram_counts f p).1
  have r2 : ∀ (f : Wire → Wire) (p : Program), measurementCount (renameProgram f p) = measurementCount p :=
    fun f p => (renameProgram_counts f p).2
  obtain ⟨l1,l2,l3,l4,l5,l6⟩ := moves_counts (start j + 15) (e0P (start j + 15) + 6)
  obtain ⟨k1,k2,k3,k4,k5,k6⟩ := moves_counts e (bTopP e + 1)
  obtain ⟨m1,m2,m3,m4,m5,m6⟩ := moves240_counts
  simp only [archiveLoadP, archiveRestoreP, exitLoadP, exitRestoreP, archiveLoad240, archiveRestore240,
    toffoliCount_append, measurementCount_append, gateSlots_append, r1, r2, rename_gateSlots,
    l1, l2, l3, l4, l5, l6, k1, k2, k3, k4, k5, k6, m1, m2, m3, m4, m5, m6, and_self]

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem leaveLowStore_split (s : Nat) : leaveLowStore s = lowSign s ++ lowRest s := rfl

theorem leaveOps_split (s : Nat) : leaveOps s = leaveHeadOps s ++ leaveMidOps s ++ leaveClose s := by
  simp only [leaveOps, leaveHeadOps, leaveMidOps, leaveLowStore_split, List.append_assoc]

/-- Far zeros before the barrel: scratch `1598 .. e0-1` and the pool overflow `e0+10 ..`. -/
def far1M (s : Nat) : Nat := interval 1598 (e0P s - 1598) ||| interval (e0P s + 10) (wpP s - 1 - (e0P s - 1598))

/-- Far zeros from the barrel on: `1615 .. e0-1` and the pool above the anchored block, `e0+10 ..` (the corrected
StoreMapped chain takes its top carries there; the adjust leaves the pool clean). -/
def far2M (s : Nat) : Nat := interval 1615 (e0P s - 1615) ||| interval (e0P s + 10) (wpP s - 1 - (e0P s - 1598))

theorem far1_iff (s : Nat) (q : Nat) :
    Zm (far1M s) q ↔ (1598 ≤ q ∧ q < e0P s) ∨ (e0P s + 10 ≤ q ∧ q < e0P s + 10 + (wpP s - 1 - (e0P s - 1598))) := by
  unfold far1M; rw [zm_or]; unfold Zm; rw [testBit_interval, testBit_interval]
  constructor <;> rintro (⟨a, b⟩|⟨a, b⟩) <;> first | (left; constructor <;> ((try unfold Wire at *); omega)) | (right; constructor <;> ((try unfold Wire at *); omega))

theorem far2_iff (s : Nat) (q : Nat) : Zm (far2M s) q ↔
    (1615 ≤ q ∧ q < e0P s) ∨ (e0P s + 10 ≤ q ∧ q < e0P s + 10 + (wpP s - 1 - (e0P s - 1598))) := by
  unfold far2M; rw [zm_or]; unfold Zm; rw [testBit_interval, testBit_interval]
  constructor <;> rintro (⟨a, b⟩|⟨a, b⟩) <;> first | (left; constructor <;> ((try unfold Wire at *); omega)) | (right; constructor <;> ((try unfold Wire at *); omega))

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem fix0_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix0 (start j) (sbP (start j))) (maskSites cC ||| far1M (start j)) = some (maskSites cC ||| far1M (start j)) := by
  decide +kernel

theorem fix1_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix1 (start j) (sbP (start j))) (maskSites cC ||| far1M (start j)) = some (maskSites cC ||| far1M (start j)) := by
  decide +kernel

theorem fix2_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix2 (start j) (sbP (start j))) (maskSites cK ||| far1M (start j)) = some (maskSites cC ||| far1M (start j)) := by
  decide +kernel

theorem fix3_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix3 (start j) (sbP (start j))) (maskSites cA ||| far1M (start j)) = some (maskSites cK ||| far1M (start j)) := by
  decide +kernel

theorem fix4_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix4 (start j) (sbP (start j))) (maskSites cB ||| far1M (start j)) = some (maskSites cA ||| far1M (start j)) := by
  decide +kernel

theorem fix5_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix5 (start j) (sbP (start j))) (far1M (start j)) = some (maskSites cB ||| far1M (start j)) := by
  decide +kernel

theorem fix8_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix8 (start j) (sbP (start j))) (far2M (start j)) = some (far2M (start j)) := by
  decide +kernel

theorem fix10_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix10 (start j) (sbP (start j))) (far2M (start j)) = some (far2M (start j)) := by
  decide +kernel

theorem fix11_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix11 (start j) (sbP (start j))) (maskSites cB ||| far2M (start j)) = some (far2M (start j)) := by
  decide +kernel

theorem fix12_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix12 (start j) (sbP (start j))) (maskSites cA ||| far2M (start j)) = some (maskSites cB ||| far2M (start j)) := by
  decide +kernel

theorem lowSign_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (lowSign (start j)) (maskSites cK ||| far2M (start j)) = some (maskSites cA ||| far2M (start j)) := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
/-- The window's rail and register facts at the Shadow7 widths (`sbP = (513-s)/2 - 7`): the stock statement with the
constants moved by the seven-bit reduction (`61 ≤ sbP ≤ 211` -> `54 ≤ sbP ≤ 204`, `railP ≤ 2 sbP + 1` -> `+ 15`,
`512 ≤ 2 sbP + s ≤ 513` -> `498 ≤ 2 sbP + s ≤ 499`, `sbP + 47 ≤ railP` -> `+ 54`, `sbP(s+15) + 50` -> `+ 57`). -/
theorem rail_win {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    railP s ≤ 258 ∧ sbP s + 54 ≤ railP s ∧ railP s ≤ 2 * sbP s + 15 ∧ 54 ≤ sbP s ∧ sbP s ≤ 204 ∧
    sbP (s+15) + 7 ≤ sbP s ∧ sbP s ≤ sbP (s+15) + 8 ∧ railP (s+15) ≤ railP s ∧
    railP (s+15) ≤ 2 * sbP (s+15) + 15 ∧ sbP (s+15) + 57 ≤ railP (s+15) ∧
    wpP s + sbP s + 16 = railP s ∧ wpP (s+15) + sbP (s+15) + 16 = railP (s+15) ∧
    e0P s = 1574 + sbP s ∧ e0P (s+15) = 1574 + sbP (s+15) ∧ bTopP s = 785 + railP s ∧
    bTopP (s+15) = 785 + railP (s+15) ∧ a0P s = s + sbP s + 32 ∧ b0P s = 787 + sbP s ∧
    lowsP s = 18 + sbP (s+15) - sbP s ∧ 2 * sbP s + s ≤ 499 ∧ 498 ≤ 2 * sbP s + s := by
  unfold wpP e0P bTopP a0P b0P lowsP railP sbP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try split_ifs) <;> omega

/-- The bank wires `bankW s i`, `i < wp+15`: three disjoint runs. -/
theorem bank_cases {s i : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (hi : i < wpP s + 15) :
    (i < 3 ∧ (bankW s i : Nat) = e0P s + i) ∨ (3 ≤ i ∧ i < wpP s ∧ (bankW s i : Nat) = bTopP s + 1 + i - wpP s ∧
      (bankW s i : Nat) ≤ 1043 ∧ 790 ≤ (bankW s i : Nat)) ∨
    (wpP s ≤ i ∧ (bankW s i : Nat) = 1598 + i - wpP s ∧ (bankW s i : Nat) ≤ 1612) := by
  have r := rail_win h1 h2
  unfold bankW; unfold wpP bTopP e0P at *
  split_ifs <;> ((try unfold Wire at *); omega)

theorem bank_inj {s i k : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (hi : i < wpP s + 15) (hk : k < wpP s + 15)
    (e : bankW s i = bankW s k) : i = k := by
  have r := rail_win h1 h2
  have a := bank_cases h1 h2 hi; have b := bank_cases h1 h2 hk
  unfold wpP bTopP e0P at *
  ((try unfold Wire at *); omega)

theorem pool_cases {s i : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    (1598 + i < e0P s ∧ (poolW s i : Nat) = 1598 + i) ∨ (e0P s ≤ 1598 + i ∧ (poolW s i : Nat) = 1608 + i) := by
  unfold poolW; split_ifs <;> ((try unfold Wire at *); omega)

theorem pool_nodup (s n : Nat) (h1 : 90 ≤ s) (h2 : s ≤ 390) : ((List.range n).map (poolW s)).Nodup := by
  refine List.Nodup.map_on (fun x _ y _ e => ?_) List.nodup_range
  have a := pool_cases (i := x) h1 h2; have b := pool_cases (i := y) h1 h2
  ((try unfold Wire at *); omega)

/-- The corrected StoreMapped carry sites: the stock pool `1558..` (skipping `1598..1612`), moved up by ten from the
anchored block `e0..e0+9` on. -/
theorem storeW_cases {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (k : Nat) :
    (1558 + k < 1598 ∧ (storeW s k : Nat) = 1558 + k) ∨
    (1598 ≤ 1558 + k ∧ 1573 + k < e0P s ∧ (storeW s k : Nat) = 1573 + k) ∨
    (1598 ≤ 1558 + k ∧ e0P s ≤ 1573 + k ∧ (storeW s k : Nat) = 1583 + k) := by
  have r := rail_win h1 h2
  simp only [storeW, Partial.storeW]; split_ifs <;> ((try unfold Wire at *); omega)

theorem adjust_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveAdjust s) (Zm (far1M s)) (Zm (far1M s)) ∧ Proper (leaveAdjust s) := by
  have r := rail_win h1 h2
  have ys_far : ∀ y ∈ (List.range (wpP s)).map (bankW s), ¬ Zm (far1M s) y := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    rw [List.mem_range] at hi
    have b := bank_cases h1 h2 (i := i) (by ((try unfold Wire at *); omega))
    rw [far1_iff]; unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
  have cs_in : ∀ c ∈ (List.range (wpP s - 1)).map (poolW s), Zm (far1M s) c := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    rw [List.mem_range] at hi
    have p := pool_cases (i := i) h1 h2
    rw [far1_iff]; unfold wpP e0P at *; ((try unfold Wire at *); omega)
  refine ⟨?_, ?_⟩
  · unfold leaveAdjust adjustG
    exact safe_append (safe_frame' (noMake_cxsG _ _) (allAT_cxsG _ _ trivial ys_far))
      (safe_append (safe_addG _ _ _ _ cs_in (pool_nodup s _ h1 h2) ys_far)
        (safe_frame' (noMake_cxsG _ _) (allAT_cxsG _ _ trivial ys_far)))
  · unfold leaveAdjust
    refine proper_adjustG _ _ _ _ (fun y hy => ?_) (fun hc => ?_) (pool_nodup s _ h1 h2)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      rw [List.mem_range] at hi
      have b := bank_cases h1 h2 (i := i) (by ((try unfold Wire at *); omega))
      refine ⟨fun hc => ?_, ?_, ?_⟩
      · obtain ⟨k, hk, e⟩ := List.mem_map.mp hc
        rw [List.mem_range] at hk
        have p := pool_cases (i := k) h1 h2; unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
      · unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
      · unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
    · obtain ⟨k, _, e⟩ := List.mem_map.mp hc
      have p := pool_cases (i := k) h1 h2; unfold e0P at *; ((try unfold Wire at *); omega)

theorem bank_far2 {s i : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (hi : i < wpP s + 15) : ¬ Zm (far2M s) (bankW s i) := by
  have r := rail_win h1 h2
  have b := bank_cases h1 h2 hi
  rw [far2_iff]; unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)

theorem barrel_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveBarrel s) (Zm (far2M s)) (Zm (far2M s)) ∧ Proper (leaveBarrel s) := by
  have r := rail_win h1 h2
  have c_far : ¬ Zm (far2M s) 1613 := by rw [far2_iff]; ((try unfold Wire at *); omega)
  have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ wpP s + 15 →
      AllAT (fun _ => True) (fun q => ¬ Zm (far2M s) q) (stageG 1613 (bankW s) xs d n) :=
    fun xs d n hn => allAT_stageG _ _ _ _ _ ⟨trivial, c_far⟩ (fun _ _ => trivial)
      (fun i hi => ⟨⟨trivial, bank_far2 h1 h2 (by ((try unfold Wire at *); omega))⟩, ⟨trivial, bank_far2 h1 h2 (by ((try unfold Wire at *); omega))⟩⟩)
  have pr : ∀ (xs : List Wire) (d n : Nat), 0 < d → n + d ≤ wpP s + 15 → (∀ x ∈ xs, x ≠ 1613) →
      Proper (stageG 1613 (bankW s) xs d n) := by
    intro xs d n hd hn hx
    refine proper_stageG _ _ _ _ _ hx (fun i hi => ⟨fun e => ?_, fun e => ?_⟩)
    · have := bank_inj h1 h2 (i := i+d) (k := i) (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)) e; ((try unfold Wire at *); omega)
    · have b := bank_cases h1 h2 (i := i) (by ((try unfold Wire at *); omega)); unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
  refine ⟨?_, ?_⟩
  · unfold leaveBarrel
    exact safe_append (safe_append (safe_append (safe_frame' (noMake_stageG _ _ _ _ _) (st _ _ _ (by ((try unfold Wire at *); omega))))
      (safe_frame' (noMake_stageG _ _ _ _ _) (st _ _ _ (by ((try unfold Wire at *); omega)))))
      (safe_frame' (noMake_stageG _ _ _ _ _) (st _ _ _ (by ((try unfold Wire at *); omega)))))
      (safe_frame' (noMake_stageG _ _ _ _ _) (st _ _ _ (by ((try unfold Wire at *); omega))))
  · unfold leaveBarrel
    refine proper_append (proper_append (proper_append ?_ ?_) ?_) ?_ <;>
      exact pr _ _ _ (by decide) (by ((try unfold Wire at *); omega)) (by decide)

theorem join_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveJoin s) (Zm (far2M s)) (Zm (far2M s)) ∧ Proper (leaveJoin s) := by
  have r := rail_win h1 h2
  have a_far : ∀ i, i ≤ 18 → ¬ Zm (far2M s) (a0P s + i) := by
    intro i hi; rw [far2_iff]; unfold a0P e0P; ((try unfold Wire at *); omega)
  have rows : ∀ r ∈ columnsP s, ∃ i, i < 18 ∧ r.shadow = a0P s + i ∧ r.tube = bankW s i ∧
      (∀ w, r.hot = some w → 1556 ≤ w ∧ w ≤ 1576) := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    rw [List.mem_range] at hi
    refine ⟨i, hi, rfl, rfl, fun w hw => ?_⟩
    dsimp only at hw
    split at hw
    · cases hw; exact tags_range i (by ((try unfold Wire at *); omega))
    · cases hw
  refine ⟨?_, ?_⟩
  · unfold leaveJoin
    refine safe_append (safe_frame' (noMake_digitsG _ _ _ _ _ _) (allAT_digitsG _ _ _ _ trivial trivial _ _
      (fun i _ hi => ⟨trivial, a_far i (by ((try unfold Wire at *); omega)), a_far (i+1) (by ((try unfold Wire at *); omega))⟩)))
      (safe_frame' (noMake_wordG _ _) (allAT_wordG _ ⟨trivial, ?_⟩ _ (fun r hr => ?_)))
    · rw [far2_iff]; ((try unfold Wire at *); omega)
    · obtain ⟨i, hi, hs, ht, _⟩ := rows r hr
      exact ⟨fun _ _ => trivial, ⟨trivial, hs ▸ a_far i (by ((try unfold Wire at *); omega))⟩, ⟨trivial, ht ▸ bank_far2 h1 h2 (by ((try unfold Wire at *); omega))⟩⟩
  · unfold leaveJoin
    refine proper_append (proper_digitsG _ _ _ _ _ _ (fun i _ hi => ?_)) (proper_wordG _ _ (fun r hr => ?_))
    · have t := tags_range i (by ((try unfold Wire at *); omega))
      ((try unfold Wire at *); omega)
    · obtain ⟨i, hi, hs, ht, hh⟩ := rows r hr
      have b := bank_cases h1 h2 (i := i) (by ((try unfold Wire at *); omega))
      refine ⟨fun w hw => ?_, ?_, ?_, ?_⟩
      · have := hh w hw; ((try unfold Wire at *); omega)
      · rw [hs]; unfold a0P; ((try unfold Wire at *); omega)
      · rw [ht]; unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
      · rw [hs, ht]; unfold a0P wpP bTopP e0P at *; ((try unfold Wire at *); omega)

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem far2_sub {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Wire) (h : Zm (far2M s) q) : Zm (far1M s) q := by
  rw [far2_iff] at h; rw [far1_iff]; ((try unfold Wire at *); omega)

theorem head_ok (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    Safe (leaveHeadOps (start j)) (Zm (maskSites cC ||| far1M (start j))) (Zm (maskSites cK ||| far2M (start j))) ∧
    Proper (leaveHeadOps (start j)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have f0 := safe_bit (fix0_bit j h0 h1); have f1 := safe_bit (fix1_bit j h0 h1)
  have f2 := safe_bit (fix2_bit j h0 h1); have f3 := safe_bit (fix3_bit j h0 h1)
  have f4 := safe_bit (fix4_bit j h0 h1); have f5 := safe_bit (fix5_bit j h0 h1)
  have f8 := safe_bit (fix8_bit j h0 h1); have f10 := safe_bit (fix10_bit j h0 h1)
  have f11 := safe_bit (fix11_bit j h0 h1); have f12 := safe_bit (fix12_bit j h0 h1)
  have fl := safe_bit (lowSign_bit j h0 h1)
  have ad := adjust_ok w1 w2; have ba := barrel_ok w1 w2; have jo := join_ok w1 w2
  refine ⟨?_, ?_⟩
  · unfold leaveHeadOps
    exact safe_append (safe_append (safe_append (safe_append (safe_append (safe_append (safe_append (safe_append
      (safe_append (safe_append (safe_append (safe_append (safe_append f0.1 f1.1) f2.1) f3.1) f4.1) f5.1) ad.1)
      (safe_mono ba.1 (far2_sub w1 w2) (fun _ h => h))) f8.1) jo.1) f10.1) f11.1) f12.1) fl.1
  · unfold leaveHeadOps
    exact proper_append (proper_append (proper_append (proper_append (proper_append (proper_append (proper_append
      (proper_append (proper_append (proper_append (proper_append (proper_append (proper_append f0.2 f1.2) f2.2) f3.2)
      f4.2) f5.2) ad.2) ba.2) f8.2) jo.2) f10.2) f11.2) f12.2) fl.2

/-- The mid part's zero zone: the carries `1559..1597`, the scratch `1613 .. e0-1` and the pool above the anchor. -/
def midZ (s q : Nat) : Prop :=
  (1559 ≤ q ∧ q ≤ 1597) ∨ (1613 ≤ q ∧ q < e0P s) ∨ (e0P s + 10 ≤ q ∧ q < e0P s + 10 + (wpP s - 1 - (e0P s - 1598)))

theorem to_mid {s : Nat} (st : State) (hz : ZeroOn st (Zm (maskSites cK ||| far2M s)))
    (hc : ∀ q ∈ coreW, st.basis q = false) : ZeroOn st (midZ s) := by
  intro q hq
  by_cases hk : q ∈ cK
  · exact hz q ((zm_or _ _ _).mpr (Or.inl ((zm_sites _ _).mpr hk)))
  by_cases hw : q ∈ coreW
  · exact hc q hw
  · apply hz q; apply (zm_or _ _ _).mpr; right; rw [far2_iff]
    rw [mem_cK] at hk; rw [mem_coreW] at hw; unfold midZ at hq; ((try unfold Wire at *); omega)

theorem lowRest_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (lowRest s) (midZ s) (fun q => q = 1558 ∨ midZ s q) ∧ Proper (lowRest s) := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, _, ee, _, _, _, ea, eb, el, _, _⟩ := r
  have hL : lowsP s ≤ 11 := by ((try unfold Wire at *); omega)
  have bs_out : ∀ y ∈ (List.range (lowsP s)).map (b0P s + ·), ¬ midZ s y := by
    intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
    unfold midZ; ((try unfold Wire at *); omega)
  have cs_in : ∀ c ∈ (List.range (lowsP s - 1)).map (1559 + ·), midZ s c := by
    intro c hc; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    unfold midZ; ((try unfold Wire at *); omega)
  have cs_nd : ((List.range (lowsP s - 1)).map (1559 + ·)).Nodup :=
    List.Nodup.map (fun a b e => by ((try unfold Wire at *); omega)) List.nodup_range
  refine ⟨?_, ?_⟩
  · unfold lowRest
    have tail : Safe ([.pop (b0P s - 1) 1557 1558] ++ [.cx (a0P s - 1) 1557, .x 1557]) (midZ s)
        (fun q => q = 1558 ∨ midZ s q) :=
      safe_append safe_pop (safe_lit (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> rfl)
        (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> simp only [target] <;> unfold midZ <;> ((try unfold Wire at *); omega)))
    refine safe_append (safe_app (midZ s) (safe_app (midZ s) (safe_app (midZ s) ?_ ?_) ?_) ?_) tail
    · exact safe_lit (noMake_map _ _ (fun _ _ => rfl)) (fun g hg => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg; rw [List.mem_range] at hi; simp only [target]; unfold midZ; ((try unfold Wire at *); omega))
    · exact safe_frame' (noMake_xsG _) (allAT_xsG _ bs_out)
    · exact safe_addG _ _ _ _ cs_in cs_nd bs_out
    · exact safe_frame' (noMake_xsG _) (allAT_xsG _ bs_out)
  · unfold lowRest
    refine proper_append (proper_append (proper_append (proper_append ?_ (proper_xsG _)) ?_) (proper_xsG _)) ?_
    · exact proper_map _ _ (fun i hi => by rw [List.mem_range] at hi; exact pr_ccx (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
    · refine proper_addG _ _ _ (fun y hy => ?_) (fun hc => ?_) cs_nd
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
        refine ⟨fun hc => ?_, by ((try unfold Wire at *); omega)⟩
        obtain ⟨k, hk, e⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk; ((try unfold Wire at *); omega)
      · obtain ⟨k, hk, e⟩ := List.mem_map.mp hc; ((try unfold Wire at *); omega)
    · exact proper_cons (pr_pop (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (proper_cons (pr_cx (by ((try unfold Wire at *); omega))) (proper_cons rfl proper_nil))

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem storeMapped_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveStoreMapped s) (fun q => q = 1558 ∨ midZ s q) (midZ s) ∧ Proper (leaveStoreMapped s) := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, _, ee, _, et, _, ea, eb, el, _, _⟩ := r
  have hL : 10 ≤ lowsP s ∧ lowsP s ≤ 11 := by ((try unfold Wire at *); omega)
  have bank_out : ∀ i, lowsP s ≤ i → i < wpP s + 15 → ¬ midZ s (bankW s i) ∧ (bankW s i : Nat) ≠ 1558 ∧
      (bankW s i : Nat) ≠ 1557 ∧ (bankW s i : Nat) ≠ 1556 ∧ ∀ k, (storeW s k : Nat) ≠ bankW s i := by
    intro i a b
    have bc := bank_cases h1 h2 b
    refine ⟨?_, ?_, ?_, ?_, fun k => ?_⟩
    · unfold midZ; ((try unfold Wire at *); omega)
    · ((try unfold Wire at *); omega)
    · ((try unfold Wire at *); omega)
    · ((try unfold Wire at *); omega)
    · have sc := storeW_cases h1 h2 k; ((try unfold Wire at *); omega)
  have hi_out : ∀ y ∈ (List.range (wpP s + 15 - lowsP s)).map (fun i => bankW s (lowsP s + i)), ¬ midZ s y := by
    intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
    exact (bank_out _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))).1
  have hir_out : ∀ y ∈ ((List.range (wpP s + 15 - lowsP s)).map (fun i => bankW s (lowsP s + i))).reverse, ¬ midZ s y :=
    fun y hy => hi_out y (List.mem_reverse.mp hy)
  have s2_out : ∀ y ∈ (List.range (lowsP s + 1)).map (b0P s - 1 + ·), ¬ midZ s y := by
    intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
    unfold midZ; ((try unfold Wire at *); omega)
  have s2r_out : ∀ y ∈ ((List.range (lowsP s + 1)).map (b0P s - 1 + ·)).reverse, ¬ midZ s y :=
    fun y hy => s2_out y (List.mem_reverse.mp hy)
  have st_in : ∀ k, 0 < k → k ≤ 0 + (wpP s + 15 - lowsP s + 1) → midZ s (storeW s k) := by
    intro k a b; have sc := storeW_cases h1 h2 k; unfold midZ; ((try unfold Wire at *); omega)
  have st_inj : ∀ k k', 0 < k → k ≤ 0 + (wpP s + 15 - lowsP s + 1) → 0 < k' → k' ≤ 0 + (wpP s + 15 - lowsP s + 1) →
      storeW s k = storeW s k' → k = k' := by
    intro k k' _ _ _ _ e; have a := storeW_cases h1 h2 k; have b := storeW_cases h1 h2 k'; ((try unfold Wire at *); omega)
  have c2_in : ∀ k, 0 < k → k ≤ 0 + (lowsP s + 1) → midZ s (1558 + k) := by
    intro k a b; unfold midZ; ((try unfold Wire at *); omega)
  have c2_inj : ∀ k k', 0 < k → k ≤ 0 + (lowsP s + 1) → 0 < k' → k' ≤ 0 + (lowsP s + 1) →
      (1558 + k : Wire) = 1558 + k' → k = k' := by
    intro k k' _ _ _ _ e; ((try unfold Wire at *); omega)
  have top_out : ¬ midZ s (a0P s + lowsP s - 1) := by unfold midZ; ((try unfold Wire at *); omega)
  refine ⟨?_, ?_⟩
  · simp only [leaveStoreMapped]
    have p1 : Safe ([.make (a0P s + lowsP s - 1 - 2) (a0P s + lowsP s - 1 - 1) 1558] ++
        [.x 1558, .x (a0P s + lowsP s - 1)]) (fun q => q = 1558 ∨ midZ s q) (midZ s) :=
      safe_append (safe_make (Or.inl rfl)) (safe_mono (Z := midZ s)
        (safe_lit (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> rfl)
          (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> simp only [target] <;> first | exact top_out | (unfold midZ; ((try unfold Wire at *); omega))))
        (fun q hq => ⟨fun e => by subst e; unfold midZ at hq; ((try unfold Wire at *); omega), Or.inr hq⟩) (fun _ h => h))
    have p2a : Safe [.x (a0P s + lowsP s - 1), .x 1558] (midZ s) (midZ s) :=
      safe_lit (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> rfl)
        (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> simp only [target] <;> first | exact top_out | (unfold midZ; ((try unfold Wire at *); omega)))
    have p2b : Safe [.x 1558] (fun q => q ≠ 1558 ∧ (q = 1558 ∨ midZ s q)) (midZ s) :=
      safe_mono (Z := midZ s) (safe_lit (fun g hg => by simp at hg; subst hg; rfl)
          (fun g hg => by simp at hg; subst hg; simp only [target]; unfold midZ; ((try unfold Wire at *); omega)))
        (fun q hq => ⟨fun e => by subst e; unfold midZ at hq; ((try unfold Wire at *); omega), Or.inr hq⟩) (fun _ h => h)
    have p2 : Safe ([.x (a0P s + lowsP s - 1), .x 1558] ++ [.pop (a0P s + lowsP s - 1 - 2) (a0P s + lowsP s - 1 - 1) 1558] ++
        [.make 1556 1557 1558] ++ [.x 1558]) (midZ s) (midZ s) :=
      safe_append (safe_append (safe_append p2a safe_pop) (safe_make (Or.inl rfl))) p2b
    have ch1 := safe_chainG (storeW s) (fun i => if i = 0 then a0P s + lowsP s - 1 else bankW s (lowsP s + i - 1))
      [.cx (storeW s (wpP s + 15 - lowsP s + 1)) 1557, .x 1557] 0 (wpP s + 15 - lowsP s + 1) (midZ s) st_in st_inj
      (safe_lit (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> rfl)
        (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> simp only [target, chainZ] <;> intro h <;> unfold midZ at h <;> ((try unfold Wire at *); omega)))
    have ch2 := safe_chainG (fun k => (1558 + k : Wire)) (fun k => b0P s - 1 + k) [.cx (1558 + (lowsP s + 1)) 1556, .x 1556]
      0 (lowsP s + 1) (midZ s) c2_in c2_inj
      (safe_lit (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> rfl)
        (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> simp only [target, chainZ] <;> intro h <;> unfold midZ at h <;> ((try unfold Wire at *); omega)))
    have x58 : Safe [GateMirror.Gate.x 1558] (midZ s) (midZ s) :=
      safe_lit (fun g hg => by simp at hg; subst hg; rfl) (fun g hg => by simp at hg; subst hg; simp only [target]; unfold midZ; ((try unfold Wire at *); omega))
    have q1 := safe_then (midZ s) p1 (safe_frame' (noMake_xsG _) (allAT_xsG _ hi_out))
    have q2 := safe_then (midZ s) q1 ch1
    have q3 := safe_then (midZ s) q2 (safe_frame' (noMake_xsG _) (allAT_xsG _ hir_out))
    have q4 := safe_then (midZ s) q3 p2
    have q5 := safe_then (midZ s) q4 (safe_frame' (noMake_xsG _) (allAT_xsG _ s2_out))
    have q6 := safe_then (midZ s) q5 ch2
    have q7 := safe_then (midZ s) q6 (safe_frame' (noMake_xsG _) (allAT_xsG _ s2r_out))
    exact safe_then (midZ s) q7 x58
  · simp only [leaveStoreMapped]
    refine proper_append (proper_append (proper_append (proper_append (proper_append (proper_append (proper_append
      (proper_append ?_ (proper_xsG _)) ?_) (proper_xsG _)) ?_) (proper_xsG _)) ?_) (proper_xsG _)) (proper_cons rfl proper_nil)
    · exact proper_cons (pr_make (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (proper_cons rfl (proper_cons rfl proper_nil))
    · refine proper_chainG _ _ _ (proper_cons (pr_cx ?_) (proper_cons rfl proper_nil)) _ _ (fun k _ hk => ⟨?_, ?_⟩)
      · have sc := storeW_cases h1 h2 (wpP s + 15 - lowsP s + 1); ((try unfold Wire at *); omega)
      · intro e; have := st_inj k (k+1) ; have a := storeW_cases h1 h2 k; have b := storeW_cases h1 h2 (k+1); ((try unfold Wire at *); omega)
      · dsimp only
        split
        · have sc := storeW_cases h1 h2 (k+1); ((try unfold Wire at *); omega)
        · exact Ne.symm ((bank_out (lowsP s + k - 1) (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))).2.2.2.2 (k+1))
    · exact proper_cons rfl (proper_cons rfl (proper_cons (pr_pop (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
        (proper_cons (pr_make (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (proper_cons rfl proper_nil))))
    · exact proper_chainG _ _ _ (proper_cons (pr_cx (by ((try unfold Wire at *); omega))) (proper_cons rfl proper_nil)) _ _
        (fun k _ hk => ⟨by ((try unfold Wire at *); omega), by ((try unfold Wire at *); omega)⟩)

theorem lowClose_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveLowClose s) (midZ s) (midZ s) ∧ Proper (leaveLowClose s) := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, _, ee, _, et, _, ea, eb, el, _, _⟩ := r
  refine ⟨?_, ?_⟩
  · simp only [leaveLowClose]
    refine safe_app (midZ s) (safe_app (midZ s) (safe_frame' (noMake_xsG _) (allAT_xsG _ (fun y hy => ?_)))
      (safe_lit (noMake_map _ _ (fun _ _ => rfl)) (fun g hg => ?_)))
      (safe_lit (noMake_flatMap _ _ (fun _ _ => noMake_cswapG _ _ _)) (fun g hg => ?_))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; unfold midZ; ((try unfold Wire at *); omega)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg; rw [List.mem_range] at hi; simp only [target]; unfold midZ; ((try unfold Wire at *); omega)
    · obtain ⟨i, hi, hg⟩ := List.mem_flatMap.mp hg; rw [List.mem_range] at hi
      simp only [cswapG, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl|rfl|rfl <;> simp only [target] <;> unfold midZ <;> ((try unfold Wire at *); omega)
  · simp only [leaveLowClose]
    refine proper_append (proper_append (proper_xsG _) (proper_map _ _ (fun i hi => pr_cx ?_)))
      (proper_flatMap _ _ (fun i hi => proper_cswapG ?_ ?_))
    all_goals (rw [List.mem_range] at hi; ((try unfold Wire at *); omega))

/-- History wires of the block in the `OB5.sig (s+14)` frame: raw below 1301, else moved above `e0+10`. -/
theorem sig_hist {s c : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (hc1 : 1044 ≤ c) (hc2 : c ≤ 1058) :
    ((OB5.sig (s+14) (s+c) : Nat) = s + c ∧ s + c ≤ 1300) ∨
    ((OB5.sig (s+14) (s+c) : Nat) = 3113 - (s + c) ∧ e0P s + 10 ≤ 3113 - (s + c) ∧ 3113 - (s + c) ≤ 1812) := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, _, ee, _, et, _, ea, eb, el, _, _⟩ := r
  unfold OB5.sig; split_ifs <;> ((try unfold Wire at *); omega)

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem moves_ne {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) : ∀ p ∈ movesP s, p.1 ≠ p.2 := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, ew', ee, ee', et, et', ea, eb, el, _, _⟩ := r
  intro p hp
  rcases List.mem_append.mp hp with hp|hp
  · obtain ⟨i, hi, e⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
    have bc := bank_cases (i := lowsP s + i) h1 h2 (by ((try unfold Wire at *); omega))
    rw [← e]; show (bankW s (lowsP s + i) : Nat) ≠ bTopP (s+15) + 4 + i - wpP (s+15)
    ((try unfold Wire at *); omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with e|e|e|e|e|e <;> rw [e] <;> show (_ : Nat) ≠ _ <;> ((try unfold Wire at *); omega)

set_option maxHeartbeats 1000000 in
theorem close_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveClose s) (fun q => q = 1556 ∨ midZ s q) (fun _ => False) ∧ Proper (leaveClose s) := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, ew', ee, ee', et, et', ea, eb, el, _, _⟩ := r
  have e44 := sig_hist (c := 1044) h1 h2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  have e45 := sig_hist (c := 1045) h1 h2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  have e46 := sig_hist (c := 1046) h1 h2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  have e47 := sig_hist (c := 1047) h1 h2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  have e48 := sig_hist (c := 1048) h1 h2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  refine ⟨?_, ?_⟩
  · unfold leaveClose
    refine safe_append (safe_eventsG _ _ _ _ ?_ ?_ ?_) (safe_drop (noMake_swapsG _))
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> unfold midZ <;> ((try unfold Wire at *); omega)
    · show [1556, 1559, 1560, 1561, 1562].Nodup
      decide
    · unfold midZ; ((try unfold Wire at *); omega)
  · unfold leaveClose
    refine proper_append (proper_eventsG _ _ _ ?_ ?_ ?_ (by ((try unfold Wire at *); omega))) (proper_swapsG _ ?_)
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> ((try unfold Wire at *); omega)
    · show ((e0P s + 7) :: [1556, 1559, 1560, 1561, 1562]).Nodup
      refine List.nodup_cons.mpr ⟨?_, by decide⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]; ((try unfold Wire at *); omega)
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> ((try unfold Wire at *); omega)
    · exact moves_ne h1 h2

theorem leaveMidOps_eq (s : Nat) : leaveMidOps s = lowRest s ++ leaveStoreMapped s ++ leaveLowClose s := rfl

attribute [local irreducible] leaveOps leaveHeadOps leaveMidOps leaveClose lowRest leaveStoreMapped leaveLowClose
  GateMirror.Ready
theorem leave_ready (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State)
    (initial : ∀ q, 1556 ≤ q → q < e0P (start j) → s.basis q = false)
    (extra : ∀ q, e0P (start j) + 10 ≤ q → q < e0P (start j) + 10 + (wpP (start j) - 1 - (e0P (start j) - 1598)) →
      s.basis q = false)
    (core : ∀ q ∈ coreW, (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis q = false)
    (post : (run (GateMirror.forward (leaveHeadOps (start j) ++ leaveMidOps (start j))) [] s).basis 1556 = false) :
    Ready s (leaveOps (start j)) ∧ (∀ g ∈ leaveOps (start j), proper g = true) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have hd := head_ok j h0 h1
  have lr := lowRest_ok w1 w2; have sm := storeMapped_ok w1 w2; have lc := lowClose_ok w1 w2
  have cl := close_ok w1 w2
  have z0 : ZeroOn s (Zm (maskSites cC ||| far1M (start j))) := by
    intro q hq
    rcases (zm_or _ _ _).mp hq with h|h
    · rw [zm_sites, mem_cC] at h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ee, _⟩ := rail_win w1 w2
      exact initial q (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
    · rw [far1_iff] at h
      rcases h with ⟨a, b⟩|⟨a, b⟩
      · exact initial q (by ((try unfold Wire at *); omega)) b
      · exact extra q a b
  obtain ⟨r1, z1⟩ := hd.1 s z0
  have mid : Safe (leaveMidOps (start j)) (midZ (start j)) (midZ (start j)) := by
    rw [leaveMidOps_eq]; exact safe_append (Z1 := midZ (start j)) (safe_append (Z1 := fun q => q = 1558 ∨ midZ (start j) q) lr.1 sm.1) lc.1
  obtain ⟨r2, z2⟩ := mid _ (to_mid _ z1 core)
  have z2' : ZeroOn (run (GateMirror.forward (leaveMidOps (start j))) []
      (run (GateMirror.forward (leaveHeadOps (start j))) [] s)) (fun q => q = 1556 ∨ midZ (start j) q) := by
    intro q hq
    rcases hq with rfl|hq
    · rw [← run_forward_append]; exact post
    · exact z2 q hq
  obtain ⟨r3, _⟩ := cl.1 _ z2'
  refine ⟨?_, ?_⟩
  · rw [leaveOps_split]
    refine ready_append _ _ _ (ready_append _ _ _ r1 r2) ?_
    rw [run_forward_append]; exact r3
  · rw [leaveOps_split]
    rw [leaveMidOps_eq]; exact proper_append (proper_append hd.2 (proper_append (proper_append lr.2 sm.2) lc.2)) cl.2

/-- The generic leave Mirror: `leaveInvP j` undoes `leaveP j` (dadon's `Leave{s}Mirror.inverts`, all blocks). -/
theorem leave_inverts (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State)
    (phase : ∀ m, (run (leaveP j) m s).phase = s.phase)
    (initial : ∀ q, 1556 ≤ q → q < e0P (start j) → s.basis q = false)
    (extra : ∀ q, e0P (start j) + 10 ≤ q → q < e0P (start j) + 10 + (wpP (start j) - 1 - (e0P (start j) - 1598)) →
      s.basis q = false)
    (core : ∀ q ∈ coreW, (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis q = false)
    (post : (run (GateMirror.forward (leaveHeadOps (start j) ++ leaveMidOps (start j))) [] s).basis 1556 = false)
    (m n : List Bool) :
    run (leaveInvP j) n (run (leaveP j) m s) = s := by
  obtain ⟨ready, phys⟩ := leave_ready j h0 h1 s initial extra core post
  exact invert (leaveOps (start j)) s phys (all_prepared _ s phys phase) ready m n

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Challenge ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
/-- A control that never reads a join cell. -/
def MoveA (s q : Nat) : Prop := ¬ (a0P s ≤ q ∧ q < a0P s + 16)

/-- A target that is no join cell, no tag and not the crossing wire. -/
def MoveT (s q : Nat) : Prop := MoveA s q ∧ (q < 1556 ∨ 1576 < q) ∧ q ≠ e0P s + 6

theorem mem_moveRows {s : Nat} {r : MoveChain.Row} (hr : r ∈ moveRows s) :
    ∃ i, i < 16 ∧ r = (tagsP.getD i 0, a0P s + i) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  exact ⟨i, List.mem_range.mp hi, rfl⟩

/-- The join cells sit below 500 and the crossing wire `e0+6` above the tags (Shadow7: `e0+6 ≥ 1574+54+6 = 1634`). -/
theorem cell_lt {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) : a0P s + 16 ≤ 500 ∧ 1634 ≤ e0P s + 6 := by
  have r := rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  omega

theorem calm_of {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) {r : MoveChain.Row} (hr : r ∈ moveRows s) (g : Gate)
    (hg : (∀ q ∈ g.controls, MoveA s q) ∧ MoveT s (target g)) : calmGate (e0P s + 6) r g = true := by
  obtain ⟨i, hi, rfl⟩ := mem_moveRows hr
  have t := tags_range i hi
  have cl := cell_lt w1 w2
  obtain ⟨hc, ⟨ht0, ht1, ht2⟩⟩ := hg
  unfold MoveA at hc ht0
  cases g <;>
  simp only [Gate.controls, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies,
    implies_true, target] at hc ht0 ht1 ht2 <;>
  simp only [calmGate, MoveChain.quiet, front, erase, plainGate, MoveChain.corrFree, target, Bool.true_or,
    Bool.false_or, Bool.or_true, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] <;>
  (repeat' constructor) <;> (try unfold Wire at *) <;> omega

/-- The segment between the mux and the digit pass never writes a tag or the crossing wire and never reads a cell. -/
theorem moveB_away {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) : AllAT (MoveA s) (MoveT s) (moveB s) := by
  have r := rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have cl := cell_lt w1 w2
  have far : ∀ q : Nat, 786 ≤ q → MoveA s q := by intro q h; unfold MoveA; omega
  have farT : ∀ q : Nat, 786 ≤ q → (q < 1556 ∨ 1576 < q) → q ≠ e0P s + 6 → MoveT s q :=
    fun q h a b => ⟨far q h, a, b⟩
  have bank : ∀ i, i < wpP s + 15 → MoveA s (bankW s i) ∧ MoveT s (bankW s i) := by
    intro i hi
    rcases bank_cases w1 w2 hi with ⟨a, e⟩ | ⟨a, b, e, c, d⟩ | ⟨a, e, c⟩ <;>
      (rw [e] at *; exact ⟨far _ (by omega), farT _ (by omega) (by omega) (by omega)⟩)
  have tagsA : ∀ x ∈ [1562, 1564, 1566, 1568, 1570, 1572, 1574, 1560, 1563, 1567, 1571, 1575, 1565, 1573, 1569],
      MoveA s x := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    apply far; rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have ctl : ∀ xs : List Wire, (∀ x ∈ xs, 1556 ≤ x) → ∀ x ∈ xs, MoveA s x := fun xs h x hx => far x (by
    have := h x hx; unfold Wire at *; omega)
  unfold moveB
  refine allAT_append (allAT_append (allAT_append ?_ ?_) ?_) ?_
  · rw [fix5_tail]
    have c6 : MoveA s (sbP s + 1580) := far _ (by omega)
    have t96 : MoveT s 1596 := farT _ (by omega) (by omega) (by omega)
    have t97 : MoveT s 1597 := farT _ (by omega) (by omega) (by omega)
    have a96 : MoveA s 1596 := far _ (by omega)
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    exact allAT_cons (ok_make c6 a96 t97) allAT_nil
  · unfold leaveAdjust
    refine allAT_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (far _ (by omega)) (far _ (by omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by omega)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have p := pool_cases (i := i) w1 w2
      exact ⟨far _ (by unfold Wire at *; omega), farT _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)
        (by unfold Wire at *; omega)⟩
  · unfold leaveBarrel
    have c13 : MoveA s 1613 ∧ MoveT s 1613 := ⟨far _ (by omega), farT _ (by omega) (by omega) (by omega)⟩
    have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ wpP s + 15 → (∀ x ∈ xs, 1556 ≤ x) →
        AllAT (MoveA s) (MoveT s) (stageG 1613 (bankW s) xs d n) :=
      fun xs d n hn hx => allAT_stageG _ _ _ _ _ c13 (ctl xs hx)
        (fun i hi => ⟨bank i (by omega), bank (i+d) (by omega)⟩)
    refine allAT_append ?_ (st _ _ _ (by omega) (by decide))
    refine allAT_append ?_ (st _ _ _ (by omega) (by decide))
    exact allAT_append (st _ _ _ (by omega) (by decide)) (st _ _ _ (by omega) (by decide))
  · show AllAT (MoveA s) (MoveT s) [.x 1613, .cx 1597 1613]
    exact allAT_cons (ok_x (farT _ (by omega) (by omega) (by omega)))
      (allAT_cons (ok_cx (far _ (by omega)) (farT _ (by omega) (by omega) (by omega))) allAT_nil)

theorem calmB {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) :
    (moveRows s).all (fun r => (moveB s).all (calmGate (e0P s + 6) r)) = true := by
  have h := moveB_away w1 w2
  rw [List.all_eq_true]; intro r hr
  rw [List.all_eq_true]; intro g hg
  exact calm_of w1 w2 hr g (h g hg)

theorem stillB {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) :
    (moveRows s).all (fun r => (GateMirror.forward (moveB s)).all (MoveChain.quiet (e0P s + 6) r)) = true := by
  have h := moveB_away w1 w2
  rw [List.all_eq_true]; intro r hr
  rw [List.all_eq_true]; intro i hi
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi
  exact (Bool.and_eq_true_iff.mp (calm_of w1 w2 hr g (h g hg))).1

theorem apart_move {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) : MoveChain.apart (e0P s + 6) (moveRows s) = true := by
  have cl := cell_lt w1 w2
  unfold MoveChain.apart
  rw [List.all_eq_true]; intro r hr
  obtain ⟨i, hi, rfl⟩ := mem_moveRows hr
  have t := tags_range i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨by unfold Wire at *; omega, by unfold Wire at *; omega, by unfold Wire at *; omega, fun r' hr' => ?_⟩
  obtain ⟨i', hi', rfl⟩ := mem_moveRows hr'
  have t' := tags_range i' hi'
  simp only [decide_eq_true_eq]; unfold Wire at *; omega

theorem lone_move (s : Nat) : MoveChain.lone (moveRows s) = true := by
  apply lone_of_nodup
  simp only [moveRows, List.map_map]
  exact List.Nodup.map (fun a b e => by simpa using e) List.nodup_range

theorem woven_move {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) :
    MoveChain.woven (e0P s + 6) (moveRows s) (GateMirror.forward (moveKept s)) = true := by
  have cl := cell_lt w1 w2
  apply woven_of
  · simp [moveRows_length, GateMirror.forward, moveKept, keptG_length]
  · intro k hk r hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
    obtain ⟨i, _, hi, rfl⟩ := mem_keptG _ _ _ _ _ g hg
    obtain ⟨i', hi', rfl⟩ := mem_moveRows hr
    have t := tags_range i (by omega)
    have t' := tags_range i' hi'
    simp only [front, MoveChain.quiet, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try unfold Wire at *) <;> omega

/-- The move leave runs exactly like the reference leave whenever, in front of the mux, the crossing wire is clean
and every hot tag selects the same cell. -/
theorem leaveMove_same {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) (v : State) (m : List Bool) (a0 : Wire)
    (clean : (run (GateMirror.forward (moveA s)) m v).basis (e0P s + 6) = false)
    (sel : ∀ r ∈ moveRows s, (run (GateMirror.forward (moveA s)) m v).basis r.1 = true → r.2 = a0) :
    run (GateMirror.forward (leaveMoveOps s)) m v = run (GateMirror.forward (leaveOps s)) m v := by
  rw [leaveMoveOps_shape, leaveOps_shape]
  simp only [forward_app]
  rw [rowGates_forward, mux_forward, dig_forward]
  exact MoveChain.splice (e0P s + 6) (moveRows s) (GateMirror.forward (moveA s)) (GateMirror.forward (moveB s))
    (GateMirror.forward (moveC s)) (GateMirror.forward (moveKept s)) v m a0 (apart_move w1 w2) (lone_move s)
    (stillB w1 w2) (woven_move w1 w2) clean sel

theorem kept_proper {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) : ∀ g ∈ moveKept s, proper g = true := by
  have cl := cell_lt w1 w2
  intro g hg
  obtain ⟨i, _, hi, rfl⟩ := mem_keptG _ _ _ _ _ g hg
  have t := tags_range i (by omega)
  simp only [proper, decide_eq_true_eq]
  constructor <;> (try unfold Wire at *) <;> omega

theorem moveMux_eq (s : Nat) : moveMux s = muxG (e0P s + 6) (moveRows s) := by
  have e : sbP s + 1580 = e0P s + 6 := by unfold e0P; omega
  unfold moveMux
  rw [← e]
  rfl

theorem allW_leaveMove {P : Wire → Prop} (s : Nat) (h : AllW P (leaveOps s)) : AllW P (leaveMoveOps s) := by
  rw [leaveOps_shape] at h
  rw [leaveMoveOps_shape]
  simp only [allW_append_iff] at h ⊢
  obtain ⟨hA, hM, hB, hD, hC⟩ := h
  rw [moveMux_eq] at hM
  exact ⟨hA, allW_rowGates _ _ hM, hB, allW_keptG _ _ _ _ _ _ hD, hC⟩

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Challenge ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
theorem leaveMove_proper_of {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) (p : ∀ g ∈ leaveOps s, proper g = true) :
    ∀ g ∈ leaveMoveOps s, proper g = true := by
  rw [leaveOps_shape] at p
  rw [leaveMoveOps_shape]
  intro g hg
  simp only [List.mem_append] at hg p
  rcases hg with h | h | h | h | h
  · exact p g (Or.inl h)
  · exact rowGates_proper _ _ (MoveChain.apart_sep _ _ (apart_move w1 w2)) g h
  · exact p g (Or.inr (Or.inr (Or.inl h)))
  · exact kept_proper w1 w2 g h
  · exact p g (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- The move leave's mirror undoes it (c9cc6a76's `Leave{s}Mirror.invertsMove`, all blocks): `leave_inverts`'s
hypotheses plus the clean crossing wire and the one-hot tags in front of the mux, on every tape. -/
theorem leaveMove_inverts (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State)
    (phase : ∀ m, (run (leaveP j) m s).phase = s.phase)
    (initial : ∀ q, 1556 ≤ q → q < e0P (start j) → s.basis q = false)
    (extra : ∀ q, e0P (start j) + 10 ≤ q → q < e0P (start j) + 10 + (wpP (start j) - 1 - (e0P (start j) - 1598)) →
      s.basis q = false)
    (core : ∀ q ∈ coreW, (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis q = false)
    (post : (run (GateMirror.forward (leaveHeadOps (start j) ++ leaveMidOps (start j))) [] s).basis 1556 = false)
    (a0 : Wire)
    (hot : ∀ o, (run (GateMirror.forward (moveA (start j))) o s).basis (e0P (start j) + 6) = false ∧
      ∀ r ∈ moveRows (start j), (run (GateMirror.forward (moveA (start j))) o s).basis r.1 = true → r.2 = a0)
    (m n : List Bool) :
    run (leaveMoveInvP j) n (run (leaveMoveP j) m s) = s := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  obtain ⟨ready, phys⟩ := leave_ready j h0 h1 s initial extra core post
  generalize hs : start j = t at *
  have same (o : List Bool) : run (GateMirror.forward (leaveMoveOps t)) o s = run (GateMirror.forward (leaveOps t)) o s :=
    leaveMove_same w1 w2 s o a0 (hot o).1 (hot o).2
  have physM : ∀ g ∈ leaveMoveOps t, proper g = true := leaveMove_proper_of w1 w2 phys
  have ready' : Ready s (moveA t ++ (moveMux t ++ (moveB t ++ (moveDig t ++ moveC t)))) := by
    rw [← leaveOps_shape]; exact ready
  have readyM : Ready s (moveA t ++ (rowGates (e0P t + 6) (moveRows t) ++ (moveB t ++ (moveKept t ++ moveC t)))) :=
    GateMirror.ready_move (e0P t + 6) (moveRows t) (moveA t) (moveB t) (moveC t) (moveMux t) (moveDig t) (moveKept t)
      s a0 (mux_forward t) (dig_forward t) (kept_plain _ _ _ _ _)
      (apart_move w1 w2) (lone_move t) (stillB w1 w2) (calmB w1 w2) (woven_move w1 w2) (hot []).1 (hot []).2 ready'
  rw [← leaveMoveOps_shape] at readyM
  have ph : ∀ o, (run (GateMirror.forward (leaveMoveOps t)) o s).phase = s.phase := by
    intro o; rw [same o]; have := phase o; rw [leaveP, hs] at this; exact this
  rw [leaveMoveP, leaveMoveInvP, hs]
  exact invert _ s physM (all_prepared _ s physM ph) readyM m n

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem fixed_box : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    segBox (start j) (leaveFix0 (start j) (sbP (start j)) ++ leaveFix1 (start j) (sbP (start j)) ++
      leaveFix2 (start j) (sbP (start j)) ++ leaveFix3 (start j) (sbP (start j)) ++ leaveFix4 (start j) (sbP (start j)) ++
      leaveFix5 (start j) (sbP (start j)) ++ leaveFix8 (start j) (sbP (start j)) ++ leaveFix10 (start j) (sbP (start j)) ++
      leaveFix11 (start j) (sbP (start j)) ++ leaveFix12 (start j) (sbP (start j)) ++ lowSign (start j)) = true := by
  decide +kernel

theorem leaveOps_box (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    AllW (leaveBox (start j)) (leaveOps (start j)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have fb := allW_of_segBox (fixed_box j h0 h1)
  simp only [allW_append_iff] at fb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, f4⟩, f5⟩, f8⟩, f10⟩, f11⟩, f12⟩, fl⟩ := fb
  generalize hs : start j = s at *
  have r := rail_win w1 w2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, ew', ee, ee', et, et', ea, eb, el, _, _⟩ := r
  have hL : 10 ≤ lowsP s ∧ lowsP s ≤ 11 := by ((try unfold Wire at *); omega)
  have bank : ∀ i, i < wpP s + 15 → leaveBox s (bankW s i) := by
    intro i hi; have bc := bank_cases w1 w2 hi; unfold leaveBox; ((try unfold Wire at *); omega)
  have tags : ∀ i, i < 16 → leaveBox s (tagsP.getD i 0) := by
    intro i hi; have t := tags_range i hi; unfold leaveBox; ((try unfold Wire at *); omega)
  have aside : ∀ i, i ≤ 19 → leaveBox s (a0P s - 1 + i) := by intro i hi; unfold leaveBox; ((try unfold Wire at *); omega)
  have bside : ∀ i, i ≤ 12 → leaveBox s (b0P s - 1 + i) := by intro i hi; unfold leaveBox; ((try unfold Wire at *); omega)
  have scr : ∀ q, 1556 ≤ q → q ≤ 1812 → leaveBox s q := by intro q a b; unfold leaveBox; ((try unfold Wire at *); omega)
  have ctl : ∀ (xs : List Wire), (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1812) → ∀ x ∈ xs, leaveBox s x :=
    fun xs h x hx => scr x (h x hx).1 (h x hx).2
  have adj : AllW (leaveBox s) (leaveAdjust s) := by
    unfold leaveAdjust
    refine allW_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by ((try unfold Wire at *); omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have p := pool_cases (i := i) w1 w2; exact scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  have bar : AllW (leaveBox s) (leaveBarrel s) := by
    unfold leaveBarrel
    have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ wpP s + 15 → (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1812) →
        AllW (leaveBox s) (stageG 1613 (bankW s) xs d n) :=
      fun xs d n hn hx => allW_stageG _ _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (ctl xs hx)
        (fun i hi => ⟨bank i (by ((try unfold Wire at *); omega)), bank (i+d) (by ((try unfold Wire at *); omega))⟩)
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    exact allW_append (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide)) (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
  have joi : AllW (leaveBox s) (leaveJoin s) := by
    unfold leaveJoin
    refine allW_append (allW_digitsG _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ _
      (fun i _ hi => ⟨tags i (by ((try unfold Wire at *); omega)), ?_, ?_⟩)) (allW_wordG _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ (fun r hr => ?_))
    · have := aside (i+1) (by ((try unfold Wire at *); omega)); rwa [show a0P s - 1 + (i+1) = a0P s + i by ((try unfold Wire at *); omega)] at this
    · have := aside (i+2) (by ((try unfold Wire at *); omega)); rwa [show a0P s - 1 + (i+2) = a0P s + (i+1) by ((try unfold Wire at *); omega)] at this
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr; rw [List.mem_range] at hi
      refine ⟨fun w hw => ?_, ?_, bank i (by ((try unfold Wire at *); omega))⟩
      · dsimp only at hw; split at hw
        · cases hw; exact tags i (by ((try unfold Wire at *); omega))
        · cases hw
      · have := aside (i+1) (by ((try unfold Wire at *); omega)); dsimp only; rwa [show a0P s - 1 + (i+1) = a0P s + i by ((try unfold Wire at *); omega)] at this
  have lr : AllW (leaveBox s) (lowRest s) := by
    unfold lowRest
    refine allW_append (allW_append (allW_append (allW_append ?_ (allW_xsG _ ?_)) (allW_addG _ _ _ ?_ ?_ ?_))
      (allW_xsG _ ?_)) ?_
    · refine allW_map _ _ (fun i hi q hq => ?_); rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl|rfl <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
    all_goals try (intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; unfold leaveBox; ((try unfold Wire at *); omega))
    · unfold leaveBox; ((try unfold Wire at *); omega)
    · rw [allW_iff_flat]
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
  have sm : AllW (leaveBox s) (leaveStoreMapped s) := by
    simp only [leaveStoreMapped]
    have lit : ∀ (gs : List Gate), (∀ q ∈ gs.flatMap Gate.wires, leaveBox s q) → AllW (leaveBox s) gs :=
      fun gs h => allW_iff_flat.mpr h
    have hi : ∀ y ∈ (List.range (wpP s + 15 - lowsP s)).map (fun i => bankW s (lowsP s + i)), leaveBox s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank _ (by ((try unfold Wire at *); omega))
    have s2 : ∀ y ∈ (List.range (lowsP s + 1)).map (b0P s - 1 + ·), leaveBox s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bside i (by ((try unfold Wire at *); omega))
    refine allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append
      ?_ (allW_xsG _ hi)) ?_) (allW_xsG _ (fun y h => hi y (List.mem_reverse.mp h)))) ?_) (allW_xsG _ s2)) ?_)
      (allW_xsG _ (fun y h => s2 y (List.mem_reverse.mp h)))) ?_
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        have sc := storeW_cases w1 w2 (wpP s + 15 - lowsP s + 1)
        split_ands <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
      · have sc := storeW_cases w1 w2 k; unfold leaveBox; ((try unfold Wire at *); omega)
      · dsimp only; split
        · unfold leaveBox; ((try unfold Wire at *); omega)
        · exact bank _ (by ((try unfold Wire at *); omega))
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        split_ands <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
      · unfold leaveBox; ((try unfold Wire at *); omega)
      · unfold leaveBox; ((try unfold Wire at *); omega)
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      unfold leaveBox; ((try unfold Wire at *); omega)
  have lc : AllW (leaveBox s) (leaveLowClose s) := by
    simp only [leaveLowClose]
    refine allW_append (allW_append (allW_xsG _ (fun y hy => ?_)) (allW_map _ _ (fun i hi q hq => ?_)))
      (allW_flatMap _ _ (fun i hi => allW_cswapG _ _ _ ?_ ?_ ?_))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; unfold leaveBox; ((try unfold Wire at *); omega)
    · rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
    all_goals (rw [List.mem_range] at hi; unfold leaveBox; ((try unfold Wire at *); omega))
  have cl : AllW (leaveBox s) (leaveClose s) := by
    unfold leaveClose
    refine allW_append (allW_eventsG _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) ?_) (allW_swapsG _ ?_)
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;>
        exact ⟨sig_box w1 w2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)), scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))⟩
    · intro p hp
      unfold movesP at hp
      rcases List.mem_append.mp hp with hp|hp
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
        exact ⟨bank _ (by ((try unfold Wire at *); omega)), by unfold leaveBox; ((try unfold Wire at *); omega)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
  rw [leaveOps_split]
  refine allW_append (allW_append ?_ (allW_append (allW_append lr sm) lc)) cl
  unfold leaveHeadOps
  refine allW_append ?_ fl; refine allW_append ?_ f12; refine allW_append ?_ f11; refine allW_append ?_ f10
  refine allW_append ?_ joi; refine allW_append ?_ f8; refine allW_append ?_ bar; refine allW_append ?_ adj
  refine allW_append ?_ f5; refine allW_append ?_ f4; refine allW_append ?_ f3; refine allW_append ?_ f2
  exact allW_append f0 f1

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem portal_foot (t : Nat) (h0 : 90 ≤ t) (h1 : t ≤ 405) : AllW (footP t) (portalOps t) := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts t h0 h1
  have hw : wpP t = railP t - sbP t - 16 := rfl
  have he : e0P t = 1574 + sbP t := rfl
  have hb : bTopP t = 785 + railP t := rfl
  have ha : a0P t = t + sbP t + 32 := rfl
  have pA : ∀ i, i < wpP t → footP t (a0P t + i) := by intro i hi; unfold footP; omega
  have pB : ∀ i, i < wpP t → footP t (802 + sbP t + i) := by intro i hi; unfold footP; omega
  have pC : ∀ i, i ≤ 250 → footP t (1556 + i) := by intro i hi; unfold footP; omega
  have pE : ∀ k, k ≤ 9 → footP t (e0P t + k) := by intro k hk; unfold footP; omega
  have pG : footP t (t+15) := by unfold footP; omega
  have pT : footP t (bTopP t) := by unfold footP; omega
  have pAt : footP t (a0P t + wpP t - 1) := by unfold footP; omega
  have mA : ∀ x ∈ (List.range (wpP t)).map (a0P t + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact pA i (List.mem_range.mp hi)
  have mB : ∀ x ∈ (List.range (wpP t)).map (802 + sbP t + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact pB i (List.mem_range.mp hi)
  have mA3 : ∀ x ∈ (List.range (wpP t - 3)).map (a0P t + 3 + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; have := List.mem_range.mp hi
    rw [show a0P t + 3 + i = a0P t + (3+i) by omega]; exact pA _ (by omega)
  have mB3 : ∀ x ∈ (List.range (wpP t - 3)).map (802 + sbP t + 3 + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; have := List.mem_range.mp hi
    rw [show 802 + sbP t + 3 + i = 802 + sbP t + (3+i) by omega]; exact pB _ (by omega)
  have zip : ∀ (l1 l2 : List Wire), (∀ x ∈ l1, footP t x) → (∀ x ∈ l2, footP t x) →
      ∀ p ∈ l1.zip l2, footP t p.1 ∧ footP t p.2 := by
    intro l1 l2 h1 h2 p hp; exact ⟨h1 _ (List.of_mem_zip hp).1, h2 _ (List.of_mem_zip hp).2⟩
  have thr : ∀ p ∈ (List.range (wpP t - 2)).map (fun i => (a0P t + 2 + i, 1558 + i)), footP t p.1 ∧ footP t p.2 := by
    intro p hp; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; have := List.mem_range.mp hi
    exact ⟨by rw [show a0P t + 2 + i = a0P t + (2+i) by omega]; exact pA _ (by omega),
      by rw [show 1558 + i = 1556 + (2+i) by omega]; exact pC _ (by omega)⟩
  have ori : ∀ p ∈ (List.range (wpP t - 1)).map (fun i => (802 + sbP t + 1 + i, 1556 + i)),
      footP t p.1 ∧ footP t p.2 := by
    intro p hp; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; have := List.mem_range.mp hi
    exact ⟨by rw [show 802 + sbP t + 1 + i = 802 + sbP t + (1+i) by omega]; exact pB _ (by omega), pC _ (by omega)⟩
  have car : ∀ x ∈ (List.range (wpP t - 4)).map (1557 + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; have := List.mem_range.mp hi
    rw [show 1557 + i = 1556 + (1+i) by omega]; exact pC _ (by omega)
  have p0 : footP t (a0P t) := by have := pA 0 (by omega); simpa using this
  have p1 : footP t (a0P t + 1) := pA 1 (by omega)
  have p2 : footP t (a0P t + 2) := pA 2 (by omega)
  have q0 : footP t (802 + sbP t) := by have := pB 0 (by omega); simpa using this
  have q1 : footP t (802 + sbP t + 1) := pB 1 (by omega)
  have q2 : footP t (802 + sbP t + 2) := pB 2 (by omega)
  have c56 : footP t 1556 := by have := pC 0 (by omega); simpa using this
  have c57 : footP t 1557 := pC 1 (by omega)
  have e3 : footP t (e0P t + 3) := pE 3 (by omega)
  have e4 : footP t (e0P t + 4) := pE 4 (by omega)
  have e5 : footP t (e0P t + 5) := pE 5 (by omega)
  unfold portalOps
  refine allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append
    (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_)
    ?_) ?_) ?_) ?_) ?_) ?_
  · intro g hg q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl <;> assumption
  · exact allW_exchangeG _ _ pG (zip _ _ mA mB)
  · exact allW_cxsG _ _ e5 mB
  · refine allW_cons ?_ allW_nil
    intro q hq; simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  · exact allW_latchG _ _ _ _ _ (fun w h => by cases h) c56 c57 thr
  · intro g hg q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl | rfl <;> assumption
  · exact allW_latchG _ _ _ _ _ (fun w h => by cases h; exact e3) e4 q0 ori
  · intro g hg q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl | rfl <;> assumption
  · exact allW_addG _ _ _ mB3 car c56
  · exact allW_map _ _ (fun p hp q hq => by
      obtain ⟨h1, h2⟩ := zip _ _ mA3 mB3 p hp
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> assumption)
  · intro g hg q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl | rfl <;> assumption
  · exact allW_transferG _ (zip _ _ mA3 mB3)
  · refine allW_cxsG _ _ e5 ?_
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · refine allW_exchangeG _ _ pG ?_
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨by assumption, by assumption⟩

theorem park_foot (e : Nat) (h0 : 90 ≤ e) (h1 : e ≤ 405) : AllW (parkFootP e) (parkOps e) := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts e h0 h1
  have he : e0P e = 1574 + sbP e := rfl
  have hb : bTopP e = 785 + railP e := rfl
  apply allW_swapsG
  intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> constructor <;> unfold parkFootP <;> omega

theorem enter_foot (s : Nat) (h0 : 90 ≤ s) (h1 : s ≤ 405) : AllW (footP s) (enterOps s) := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts s h0 h1
  unfold enterOps enterFix AllW
  simp only [List.forall_mem_cons, List.forall_mem_nil, Gate.wires, and_true, implies_true]
  and_intros <;> first | (intro x hx; cases hx) | (unfold footP; omega)

theorem enter_wires (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 22) :
    (∀ q ∈ wires (enterP j), footP (start j) q) ∧ (∀ q ∈ wires (enterInvP j), footP (start j) q) :=
  allW_programs (enter_foot (start j) (by simp [start]; omega) (by simp [start]; omega))

/-- Wires of the parametric programs (portal, park), for `Covered`. -/
theorem portal_wires (t : Nat) (h0 : 90 ≤ t) (h1 : t ≤ 405) :
    (∀ q ∈ wires (portalP t), footP t q) ∧ (∀ q ∈ wires (portalInvP t), footP t q) :=
  allW_programs (portal_foot t h0 h1)

theorem park_wires (e : Nat) (h0 : 90 ≤ e) (h1 : e ≤ 405) :
    (∀ q ∈ wires (parkP e), parkFootP e q) ∧ (∀ q ∈ wires (parkInvP e), parkFootP e q) :=
  allW_programs (park_foot e h0 h1)

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.Partial

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem scratch_foot (t f k : Nat) (ht : t < 512) (hk : k < 134) : archFootP t f (scratchS t k) := by
  have := scratchS_cases t k ht hk; unfold archFootP; omega

theorem scratchX_foot (e f k : Nat) (he : e < 512) (hk : k < 134) : archFootP e f (scratchX e k) := by
  rcases scratchX_cases e k he hk with ⟨a, e1⟩ | ⟨a, b, e1⟩ | ⟨a, b, e1⟩
  · rw [e1]; exact scratch_foot e f k he hk
  · rw [e1]; unfold archFootP; omega
  · rw [e1]; unfold archFootP; omega

theorem loadPortsWP_foot (t f p : Nat) (ht : t < 512) (hp : p < 155) :
    archFootP t f ((loadPortsWP t f).getD p 0) := by
  by_cases h1 : p < 20
  · rw [loadPortsWP_cell t f p h1]
    have hc : (cellsLoadP t).length = 20 := by simp [cellsLoadP]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact cellsLoad_foot t f _ (by omega) (List.getElem_mem _)
  by_cases h2 : p < 23
  · obtain ⟨i, rfl⟩ : ∃ i, p = 20 + i := ⟨p - 20, by omega⟩
    rw [loadPortsWP_flag t f i (by omega)]; unfold archFootP; omega
  · obtain ⟨k, rfl⟩ : ∃ k, p = 23 + k := ⟨p - 23, by omega⟩
    rw [loadPortsWP_scratch t f k (by omega)]; exact scratch_foot t f k (by omega) (by omega)

theorem restorePortsWP_foot (t f p : Nat) (ht : t < 512) (hp : p < 150) :
    archFootP t f ((restorePortsWP t).getD p 0) := by
  by_cases h1 : p < 16
  · rw [restorePortsWP_cell t p h1]
    have hc : (cellsRestoreP t).length = 16 := by simp [cellsRestoreP]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact cellsRestore_foot t f (by omega) _ (List.getElem_mem _)
  · obtain ⟨k, rfl⟩ : ∃ k, p = 16 + k := ⟨p - 16, by omega⟩
    rw [restorePortsWP_scratch t k (by omega)]; exact scratch_foot t f k (by omega) (by omega)

attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1 ReducedWindowArchives.restore0 ReducedWindowArchives.restore1
/-- Window-form archives of block `j` (tick `t = start j + 15`, flags `e0(t)+6..8`). -/
theorem archiveLoadP_wires (j : Fin 23) (d : Bool) (hj : j.val ≤ 21) :
    ∀ q ∈ wires (archiveLoadP j d), archFootP (start j + 15) (e0P (start j + 15) + 6) q := by
  have ht : start j + 15 < 512 := by simp [start]; omega
  intro q hq
  rw [archiveLoadP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_foot _ _ 155 _ _ (by cases d <;> first | exact load0_ports | exact load1_ports)
      (fun p hp => loadPortsWP_foot _ _ p ht hp) q hq
  · exact (allW_programs (moves_foot _ (e0P (start j + 15) + 6) (by omega)).1).1 q hq

theorem archiveRestoreP_wires (j : Fin 23) (d : Bool) (hj : j.val ≤ 21) :
    ∀ q ∈ wires (archiveRestoreP j d), archFootP (start j + 15) (e0P (start j + 15) + 6) q := by
  have ht : start j + 15 < 512 := by simp [start]; omega
  intro q hq
  rw [archiveRestoreP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_foot _ _ 150 _ _ (by cases d <;> first | exact restore0_ports | exact restore1_ports)
      (fun p hp => restorePortsWP_foot _ _ p ht hp) q hq
  · exact (allW_programs (moves_foot _ (e0P (start j + 15) + 6) (by omega)).2).1 q hq

theorem loadPortsXP_foot (e f p : Nat) (he : e < 512) (hp : p < 155) :
    archFootP e f ((loadPortsXP e f).getD p 0) := by
  by_cases h : e ≤ 369
  · rw [loadPortsXP_low e f h]; exact loadPortsWP_foot e f p he hp
  · have len := loadPortsXP_length e f
    have mem : (loadPortsXP e f).getD p 0 ∈ loadPortsXP e f := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    generalize (loadPortsXP e f).getD p 0 = x at mem ⊢
    simp only [loadPortsXP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at mem
    rcases mem with (m | m) | ⟨k, hk, rfl⟩
    · exact cellsLoad_foot e f x (by omega) m
    · rcases m with rfl | rfl | rfl <;> (unfold archFootP; omega)
    · exact scratchX_foot e f k he (by omega)

theorem restorePortsXP_foot (e f p : Nat) (he : e < 512) (hp : p < 150) :
    archFootP e f ((restorePortsXP e).getD p 0) := by
  by_cases h : e ≤ 369
  · rw [restorePortsXP_low e h]; exact restorePortsWP_foot e f p he hp
  · have len := restorePortsXP_length e
    have mem : (restorePortsXP e).getD p 0 ∈ restorePortsXP e := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    generalize (restorePortsXP e).getD p 0 = x at mem ⊢
    simp only [restorePortsXP, List.mem_append, List.mem_map, List.mem_range] at mem
    rcases mem with m | ⟨k, hk, rfl⟩
    · exact cellsRestore_foot e f (by omega) x m
    · exact scratchX_foot e f k he hk

/-- Stock-form exit archives at tick `e` (flags `bTop(e)+1..3`). -/
theorem exitLoadP_wires (e : Nat) (d : Bool) (he : e < 512) :
    ∀ q ∈ wires (exitLoadP e d), archFootP e (bTopP e + 1) q := by
  intro q hq
  rw [exitLoadP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_foot _ _ 155 _ _ (by cases d <;> first | exact load0_ports | exact load1_ports)
      (fun p hp => loadPortsXP_foot _ _ p he hp) q hq
  · exact (allW_programs (moves_foot e (bTopP e + 1) (by omega)).1).1 q hq

theorem exitRestoreP_wires (e : Nat) (d : Bool) (he : e < 512) :
    ∀ q ∈ wires (exitRestoreP e d), archFootP e (bTopP e + 1) q := by
  intro q hq
  rw [exitRestoreP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_foot _ _ 150 _ _ (by cases d <;> first | exact restore0_ports | exact restore1_ports)
      (fun p hp => restorePortsXP_foot _ _ p he hp) q hq
  · exact (allW_programs (moves_foot e (bTopP e + 1) (by omega)).2).1 q hq

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.Partial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1 ReducedWindowArchives.restore0 ReducedWindowArchives.restore1
theorem scratch_footW (t f k : Nat) (ht : t < 512) (hk : k < 134) : archFootW t f (scratchS t k) := by
  have := scratchS_cases t k ht hk; unfold archFootW; omega

theorem scratchX_footW (e f k : Nat) (he : e < 512) (hk : k < 134) : archFootW e f (scratchX e k) := by
  rcases scratchX_cases e k he hk with ⟨a, e1⟩ | ⟨a, b, e1⟩ | ⟨a, b, e1⟩
  · rw [e1]; exact scratch_footW e f k he hk
  · rw [e1]; unfold archFootW; omega
  · rw [e1]; unfold archFootW; omega

theorem loadPortsWP_footW (t f p : Nat) (ht : t < 512) (hp : p < 155) :
    archFootW t f ((loadPortsWP t f).getD p 0) := by
  by_cases h1 : p < 20
  · rw [loadPortsWP_cell t f p h1]
    have hc : (cellsLoadP t).length = 20 := by simp [cellsLoadP]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact cellsLoad_footW t f _ (by omega) (List.getElem_mem _)
  by_cases h2 : p < 23
  · obtain ⟨i, rfl⟩ : ∃ i, p = 20 + i := ⟨p - 20, by omega⟩
    rw [loadPortsWP_flag t f i (by omega)]; unfold archFootW; omega
  · obtain ⟨k, rfl⟩ : ∃ k, p = 23 + k := ⟨p - 23, by omega⟩
    rw [loadPortsWP_scratch t f k (by omega)]; exact scratch_footW t f k (by omega) (by omega)

theorem restorePortsWP_footW (t f p : Nat) (ht : t < 512) (hp : p < 150) :
    archFootW t f ((restorePortsWP t).getD p 0) := by
  by_cases h1 : p < 16
  · rw [restorePortsWP_cell t p h1]
    have hc : (cellsRestoreP t).length = 16 := by simp [cellsRestoreP]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact cellsRestore_footW t f (by omega) _ (List.getElem_mem _)
  · obtain ⟨k, rfl⟩ : ∃ k, p = 16 + k := ⟨p - 16, by omega⟩
    rw [restorePortsWP_scratch t k (by omega)]; exact scratch_footW t f k (by omega) (by omega)

/-- Window-form archives of block `j` (tick `t = start j + 15`, flags `e0(t)+6..8`). -/
theorem archiveLoadP_wiresW (j : Fin 23) (d : Bool) (hj : j.val ≤ 20) :
    ∀ q ∈ wires (archiveLoadP j d), archFootW (start j + 15) (e0P (start j + 15) + 6) q := by
  have ht : start j + 15 < 512 := by simp [start]; omega
  intro q hq
  rw [archiveLoadP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_footW _ _ 155 _ _ (by cases d <;> first | exact load0_ports | exact load1_ports)
      (fun p hp => loadPortsWP_footW _ _ p ht hp) q hq
  · exact (allW_programs (moves_footW _ (e0P (start j + 15) + 6) (by omega)).1).1 q hq

theorem archiveRestoreP_wiresW (j : Fin 23) (d : Bool) (hj : j.val ≤ 20) :
    ∀ q ∈ wires (archiveRestoreP j d), archFootW (start j + 15) (e0P (start j + 15) + 6) q := by
  have ht : start j + 15 < 512 := by simp [start]; omega
  intro q hq
  rw [archiveRestoreP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_footW _ _ 150 _ _ (by cases d <;> first | exact restore0_ports | exact restore1_ports)
      (fun p hp => restorePortsWP_footW _ _ p ht hp) q hq
  · exact (allW_programs (moves_footW _ (e0P (start j + 15) + 6) (by omega)).2).1 q hq

theorem loadPortsXP_footW (e f p : Nat) (he : e < 512) (hp : p < 155) :
    archFootW e f ((loadPortsXP e f).getD p 0) := by
  by_cases h : e ≤ 369
  · rw [loadPortsXP_low e f h]; exact loadPortsWP_footW e f p (by omega) hp
  · have len := loadPortsXP_length e f
    have mem : (loadPortsXP e f).getD p 0 ∈ loadPortsXP e f := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    generalize (loadPortsXP e f).getD p 0 = x at mem ⊢
    simp only [loadPortsXP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at mem
    rcases mem with (m | m) | ⟨k, hk, rfl⟩
    · exact cellsLoad_footW e f x (by omega) m
    · rcases m with rfl | rfl | rfl <;> (unfold archFootW; omega)
    · exact scratchX_footW e f k (by omega) (by omega)

theorem restorePortsXP_footW (e f p : Nat) (he : e < 512) (hp : p < 150) :
    archFootW e f ((restorePortsXP e).getD p 0) := by
  by_cases h : e ≤ 369
  · rw [restorePortsXP_low e h]; exact restorePortsWP_footW e f p (by omega) hp
  · have len := restorePortsXP_length e
    have mem : (restorePortsXP e).getD p 0 ∈ restorePortsXP e := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    generalize (restorePortsXP e).getD p 0 = x at mem ⊢
    simp only [restorePortsXP, List.mem_append, List.mem_map, List.mem_range] at mem
    rcases mem with m | ⟨k, hk, rfl⟩
    · exact cellsRestore_footW e f (by omega) x m
    · exact scratchX_footW e f k (by omega) hk

/-- Stock-form exit archives at tick `e` (flags `bTop(e)+1..3`). -/
theorem exitLoadP_wiresW (e : Nat) (d : Bool) (he : e < 512) :
    ∀ q ∈ wires (exitLoadP e d), archFootW e (bTopP e + 1) q := by
  intro q hq
  rw [exitLoadP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_footW _ _ 155 _ _ (by cases d <;> first | exact load0_ports | exact load1_ports)
      (fun p hp => loadPortsXP_footW _ _ p he hp) q hq
  · exact (allW_programs (moves_footW e (bTopP e + 1) (by omega)).1).1 q hq

theorem exitRestoreP_wiresW (e : Nat) (d : Bool) (he : e < 512) :
    ∀ q ∈ wires (exitRestoreP e d), archFootW e (bTopP e + 1) q := by
  intro q hq
  rw [exitRestoreP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_footW _ _ 150 _ _ (by cases d <;> first | exact restore0_ports | exact restore1_ports)
      (fun p hp => restorePortsXP_footW _ _ p he hp) q hq
  · exact (allW_programs (moves_footW e (bTopP e + 1) (by omega)).2).1 q hq

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFold7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Baselines ECDSAAdd.Challenge ECDSAAdd.Entrant.StairPacket.WindowFold

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem routed_counts (j : Fin 23) (a n : Nat) (bound : a+n≤15) :
    toffoliCount (Shadow7.routed j a n)=n*(2*(Shadow7.smallBits j+18)) ∧
    measurementCount (Shadow7.routed j a n)=n*(Shadow7.smallBits j+18) ∧
    toffoliCount (Shadow7.unrouted j a n)=n*(2*(Shadow7.smallBits j+18)) ∧
    measurementCount (Shadow7.unrouted j a n)=n*(Shadow7.smallBits j+18) := by
  obtain ⟨f,r⟩ := Shadow7.fixed_route j a n bound
  have hs := IntegerPacket.metrics (Shadow7.shape j) a n bound
  have mid : (Shadow7.shape j).mid+1=Shadow7.smallBits j+18 := rfl
  rw [mid] at hs
  rw [f,r,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2]
  exact hs

end ECDSAAdd.Entrant.StairPacket.WindowFold7
end

section
namespace ECDSAAdd.Entrant.StairPacket.PartialPhysical
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum

private theorem integer_ticks (L : SkywalkIntegerLayout) (hv : L.Valid) :
    GatePhysical (skywalkIntegerTick L) ∧ GatePhysical (skywalkIntegerUntick L) := by
  have enough : 1 ≤ L.half.length := by simp [SkywalkIntegerLayout.half]
  have narrow := narrowTicks_physical L 1 hv (by decide) enough
  simp only [narrowSkywalkTick, narrowSkywalkUntick, gatePhysical_append] at narrow
  obtain ⟨⟨⟨⟨route, half⟩, _⟩, prev⟩, ⟨⟨⟨⟨_, _⟩, _⟩, cx⟩, sw⟩⟩ := narrow
  have nd := L.record_nodup hv
  have fresh := (List.nodup_cons.mp nd).1
  have sx : L.ext ≠ L.history := by
    intro e
    apply fresh
    rw [← e]
    simp [SkywalkIntegerLayout.half]
  have sy : L.bSign ≠ L.history := by
    intro e
    apply fresh
    rw [← e]
    simp [SkywalkIntegerLayout.b, SkywalkIntegerLayout.bh]
  have toggle : GatePhysical (skywalkSignToggle L.ext L.bSign L.history) := by
    simp [skywalkSignToggle, GatePhysical, PhysicalInstr, ProperGate, sx, sy]
  have arithmetic := signedWords_physical L.history L.half L.b L.carry nd
  simp only [skywalkIntegerTick, skywalkIntegerUntick, signedRecord, signedUnrecord,
    gatePhysical_append]
  exact ⟨⟨⟨⟨route, half⟩, ⟨⟨toggle, arithmetic.1⟩, toggle⟩⟩, prev⟩,
    ⟨⟨⟨⟨prev, ⟨⟨toggle, arithmetic.2⟩, toggle⟩⟩, half⟩, cx⟩, sw⟩⟩

end ECDSAAdd.Entrant.StairPacket.PartialPhysical
end

section
namespace ECDSAAdd.Entrant.StairPacket.ArchiveJ7
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket.ArchivePortAction ECDSAAdd.Entrant.StairArchiveIntegerHook ECDSAAdd.Entrant.CodecBitSliceVerify ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.ArchiveJ

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
def rawHead (i : Fin 23) : List Wire := cellsLoadP (start i+15)++[Shadow7.e0P (start i+15)+6,Shadow7.e0P (start i+15)+6+1,Shadow7.e0P (start i+15)+6+2]

def scratch (i : Fin 23) : List Wire := (List.range 134).map (Shadow7.scratchS (start i+15))

def rawPortsList (i : Fin 23) : List Wire :=
  Shadow7.loadPortsWP (start i+15) (Shadow7.e0P (start i+15)+6)++[Shadow7.scratchS (start i+15) 132,Shadow7.scratchS (start i+15) 133]

def rawPorts (i : Fin 23) (q : Fin 157) : Wire := (rawPortsList i).getD q 0

def codeTail (i : Fin 23) : List Wire :=
  [OB5.sig (start i+15) (start i+15+1036),OB5.sig (start i+15) (start i+15+1038),OB5.sig (start i+15) (start i+15+1041),
   OB5.sig (start i+15) (start i+15+1043),Shadow7.e0P (start i+15)+6,Shadow7.e0P (start i+15)+7,Shadow7.e0P (start i+15)+8]

def codePortsList (i : Fin 23) : List Wire := Shadow7.restorePortsWP (start i+15)++codeTail i

def codePorts (i : Fin 23) (q : Fin 157) : Wire := (codePortsList i).getD q 0

def loadMap (i : Fin 23) (q : Wire) : Wire := (Shadow7.loadPortsWP (start i+15) (Shadow7.e0P (start i+15)+6)).getD q 0

def restoreMap (i : Fin 23) (q : Wire) : Wire := (Shadow7.restorePortsWP (start i+15)).getD q 0

def restoreMoves (i : Fin 23) : List (Wire×Wire) := (moveRestorePairs (start i+15) (Shadow7.e0P (start i+15)+6)).map Prod.swap

/-- Wires the scratch block never takes: below 1556 off the hosts `[1302-t, 933]` (from tick 369), from 1700 on, or
in the live block `e0..e0+9`. -/
def Band (t q : Nat) : Prop :=
  (q<1301 ∧ (q+t<1302 ∨ 933<q ∨ t<369)) ∨ (1044+t<q ∧ q<1556) ∨ 2069≤q+t ∨ 1700≤q ∨ ∃c<10, q=Shadow7.e0P t+c

instance (t q : Nat) : Decidable (Band t q) := by unfold Band; infer_instance

theorem band_off (t : Nat) (ht : t<512) {q k : Nat} (hk : k<134) (h : Band t q) : Shadow7.scratchS t k≠q := by
  have b:=Shadow7.scratchW_bounds t k
  have l:=Shadow7.scratchW_le t k hk
  have he:1574≤Shadow7.e0P t:=by unfold Shadow7.e0P; omega
  rcases Shadow7.scratchS_cases t k ht hk with ⟨e1, lo, hi, nm⟩ | ⟨t369, lo, hi⟩
  · rw [e1] at lo hi nm ⊢
    rcases h with h|h|h|h|⟨c,hc,rfl⟩
    · omega
    · omega
    · omega
    · omega
    · exact Shadow7.scratchW_ne_e0 t k c hc
  · rcases h with h|h|h|h|⟨c,hc,rfl⟩ <;> omega

theorem rawLength (i : Fin 23) : (rawPortsList i).length=157 := by
  simp only [rawPortsList,List.length_append,Shadow7.loadPortsWP_length,List.length_cons,List.length_nil]

theorem codeLength (i : Fin 23) : (codePortsList i).length=157 := by
  simp only [codePortsList,List.length_append,Shadow7.restorePortsWP_length,codeTail,List.length_cons,List.length_nil]

theorem raw_split (i : Fin 23) : rawPortsList i=rawHead i++scratch i := by
  simp only [rawPortsList,rawHead,scratch,Shadow7.loadPortsWP,List.append_assoc]
  rw [range_two]

theorem code_split (i : Fin 23) : codePortsList i=cellsRestoreP (start i+15)++scratch i++codeTail i := by
  simp only [codePortsList,Shadow7.restorePortsWP,scratch]

theorem raw_scratch (i : Fin 23) {k : Nat} (hk : k<134) : (rawPortsList i).getD (23+k) 0=Shadow7.scratchS (start i+15) k := by
  rw [raw_split,List.getD_append_right _ _ _ _ (by simp [rawHead,cellsLoadP]),scratch]
  have e:23+k-(rawHead i).length=k:=by simp [rawHead,cellsLoadP]
  rw [e,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

theorem code_scratch (i : Fin 23) {k : Nat} (hk : k<134) : (codePortsList i).getD (16+k) 0=Shadow7.scratchS (start i+15) k := by
  rw [codePortsList,List.getD_append _ _ _ _ (by rw [Shadow7.restorePortsWP_length]; omega),Shadow7.restorePortsWP_scratch _ _ hk]

theorem rawIndex (i : Fin 23) {q : Wire} (h : q∈rawPortsList i) : ∃k:Fin 157, rawPorts i k=q := by
  obtain ⟨n,hn,eq⟩:=List.getElem_of_mem h
  refine ⟨⟨n,(rawLength i) ▸ hn⟩,?_⟩
  rw [rawPorts,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact eq

theorem codeIndex (i : Fin 23) {q : Wire} (h : q∈codePortsList i) : ∃k:Fin 157, codePorts i k=q := by
  obtain ⟨n,hn,eq⟩:=List.getElem_of_mem h
  refine ⟨⟨n,(codeLength i) ▸ hn⟩,?_⟩
  rw [codePorts,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact eq

theorem scratch_mem (i : Fin 23) {k : Nat} (hk : k<134) : Shadow7.scratchS (start i+15) k∈scratch i :=
  List.mem_map.mpr ⟨k,List.mem_range.mpr hk,rfl⟩

theorem scratch_nodup (i : Fin 23) : (scratch i).Nodup :=
  List.Nodup.map_on (fun a ha b hb h=>Shadow7.scratchS_inj _ a b (tick_lt i) (List.mem_range.mp ha) (List.mem_range.mp hb) h)
    List.nodup_range

/-- Head facts, one `decide` over the window archives `i ≤ 18` (short lists only). -/
theorem heads_all : ∀ i : Fin 23, i.val≤20 →
    (rawHead i).Nodup ∧ (∀q∈rawHead i, Band (start i+15) q) ∧
    (cellsRestoreP (start i+15)++codeTail i).Nodup ∧ (∀q∈cellsRestoreP (start i+15)++codeTail i, Band (start i+15) q) ∧
    (∀q∈cellsRestoreP (start i+15)++codeTail i, q∈rawHead i) ∧
    (∀p∈loadMoves i, p.1∈rawHead i ∧ p.2∈rawHead i ∧ p.1≠p.2) ∧
    (∀p∈restoreMoves i, p.1≠p.2 ∧ (p.1∈cellsRestoreP (start i+15)++codeTail i ∨ ∃c<7, p.1=Shadow7.scratchS (start i+15) c) ∧
      (p.2∈cellsRestoreP (start i+15)++codeTail i ∨ ∃c<7, p.2=Shadow7.scratchS (start i+15) c)) := by
  decide +kernel

theorem routes_head_all : ∀ i : Fin 23, i.val≤20 → ∀k:Fin 157,
    ((k.val<16 ∨ 150≤k.val) → backMap (loadMoves i) (codePorts i k)=rawPorts i (loadRoute k)) ∧
    (k.val<30 → backMap (restoreMoves i) (rawPorts i k)=codePorts i (restoreRoute k)) := by
  decide +kernel

theorem rawNodup (i : Fin 23) (hi : i.val≤20) : (rawPortsList i).Nodup := by
  obtain ⟨hn,hb,-⟩:=heads_all i hi
  rw [raw_split,List.nodup_append]
  refine ⟨hn,scratch_nodup i,?_⟩
  intro a ha b hb' eq
  obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hb'
  exact band_off _ (tick_lt i) (List.mem_range.mp hk) (hb a ha) eq.symm

theorem codeNodup (i : Fin 23) (hi : i.val≤20) : (codePortsList i).Nodup := by
  obtain ⟨-,-,hn,hb,-⟩:=heads_all i hi
  rw [code_split,List.nodup_append,List.nodup_append]
  rw [List.nodup_append] at hn
  refine ⟨⟨hn.1,scratch_nodup i,?_⟩,hn.2.1,?_⟩
  · intro a ha b hb' eq
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hb'
    exact band_off _ (tick_lt i) (List.mem_range.mp hk) (hb a (List.mem_append_left _ ha)) eq.symm
  · intro a ha b hb' eq
    rcases List.mem_append.mp ha with ha|ha
    · exact hn.2.2 a ha b hb' eq
    · obtain ⟨k,hk,rfl⟩:=List.mem_map.mp ha
      exact band_off _ (tick_lt i) (List.mem_range.mp hk) (hb b (List.mem_append_right _ hb')) eq

theorem load_unique (i : Fin 23) (hi : i.val≤20) : Function.Injective (rawPorts i) :=
  injective_list (rawPortsList i) (rawLength i) (rawNodup i hi)

theorem restore_unique (i : Fin 23) (hi : i.val≤20) : Function.Injective (codePorts i) :=
  injective_list (codePortsList i) (codeLength i) (codeNodup i hi)

theorem load_map (i : Fin 23) : ∀q:Fin 155, loadMap i q=rawPorts i ⟨q,by omega⟩ := by
  intro q
  simp only [loadMap,rawPorts,rawPortsList]
  rw [List.getD_append _ _ _ _ (by rw [Shadow7.loadPortsWP_length]; exact q.isLt)]

theorem restore_map (i : Fin 23) : ∀q:Fin 150, restoreMap i q=codePorts i ⟨q,by omega⟩ := by
  intro q
  simp only [restoreMap,codePorts,codePortsList]
  rw [List.getD_append _ _ _ _ (by rw [Shadow7.restorePortsWP_length]; exact q.isLt)]

theorem load_route (i : Fin 23) (hi : i.val≤20) : ∀k,backMap (loadMoves i) (codePorts i k)=rawPorts i (loadRoute k) := by
  intro k
  by_cases h:k.val<16 ∨ 150≤k.val
  · exact (routes_head_all i hi k).1 h
  · have m:=(routes_mid k).1 (by omega) (by omega)
    have hc:codePorts i k=Shadow7.scratchS (start i+15) (k.val-16):=by
      have e:=code_scratch i (k:=k.val-16) (by omega); rw [show 16+(k.val-16)=k.val by omega] at e; exact e
    have hr:rawPorts i (loadRoute k)=Shadow7.scratchS (start i+15) (k.val-16):=by
      have e:=raw_scratch i (k:=k.val-16) (by omega); rw [show 23+(k.val-16)=k.val+7 by omega,← m] at e; exact e
    rw [hc,hr]
    apply backMap_outside
    intro p hp
    obtain ⟨h1,h2,-⟩:=(heads_all i hi).2.2.2.2.2.1 p hp
    have b:=(heads_all i hi).2.1
    exact ⟨band_off _ (tick_lt i) (by omega) (b _ h1),band_off _ (tick_lt i) (by omega) (b _ h2)⟩

theorem restore_route (i : Fin 23) (hi : i.val≤20) :
    ∀k,backMap (restoreMoves i) (rawPorts i k)=codePorts i (restoreRoute k) := by
  intro k
  by_cases h:k.val<30
  · exact (routes_head_all i hi k).2 h
  · have m:=(routes_mid k).2 (by omega)
    have hr:rawPorts i k=Shadow7.scratchS (start i+15) (k.val-23):=by
      have e:=raw_scratch i (k:=k.val-23) (by omega); rw [show 23+(k.val-23)=k.val by omega] at e; exact e
    have hc:codePorts i (restoreRoute k)=Shadow7.scratchS (start i+15) (k.val-23):=by
      have e:=code_scratch i (k:=k.val-23) (by omega); rw [show 16+(k.val-23)=(restoreRoute k).val by omega] at e; exact e
    rw [hr,hc]
    apply backMap_outside
    intro p hp
    obtain ⟨-,h1,h2⟩:=(heads_all i hi).2.2.2.2.2.2 p hp
    have b:=(heads_all i hi).2.2.2.1
    have off (q : Wire) (hq : q∈cellsRestoreP (start i+15)++codeTail i ∨ ∃c<7, q=Shadow7.scratchS (start i+15) c) :
        Shadow7.scratchS (start i+15) (k.val-23)≠q := by
      rcases hq with hq|⟨c,hc,rfl⟩
      · exact band_off _ (tick_lt i) (by omega) (b _ hq)
      · intro eq; have:=Shadow7.scratchS_inj _ _ _ (tick_lt i) (by omega) (by omega) eq; omega
    exact ⟨off _ h1,off _ h2⟩

theorem load_scope (i : Fin 23) (hi : i.val≤20) : ∀p∈loadMoves i,(∃k,rawPorts i k=p.1) ∧ (∃k,rawPorts i k=p.2) := by
  intro p hp
  obtain ⟨h1,h2,-⟩:=(heads_all i hi).2.2.2.2.2.1 p hp
  exact ⟨rawIndex i (raw_split i ▸ List.mem_append_left _ h1),rawIndex i (raw_split i ▸ List.mem_append_left _ h2)⟩

theorem restore_scope (i : Fin 23) (hi : i.val≤20) : ∀p∈restoreMoves i,(∃k,codePorts i k=p.1) ∧ (∃k,codePorts i k=p.2) := by
  intro p hp
  obtain ⟨-,h1,h2⟩:=(heads_all i hi).2.2.2.2.2.2 p hp
  have mem (q : Wire) (hq : q∈cellsRestoreP (start i+15)++codeTail i ∨ ∃c<7, q=Shadow7.scratchS (start i+15) c) :
      q∈codePortsList i := by
    rw [code_split]
    rcases hq with hq|⟨c,hc,rfl⟩
    · rcases List.mem_append.mp hq with hq|hq
      · exact List.mem_append_left _ (List.mem_append_left _ hq)
      · exact List.mem_append_right _ hq
    · exact List.mem_append_left _ (List.mem_append_right _ (scratch_mem i (by omega)))
  exact ⟨codeIndex i (mem _ h1),codeIndex i (mem _ h2)⟩

theorem restore_proper (i : Fin 23) (hi : i.val≤20) : ∀p∈restoreMoves i,p.1≠p.2 :=
  fun p hp=>((heads_all i hi).2.2.2.2.2.2 p hp).1

theorem load_program (i : Fin 23) (d : Bool) : Shadow7.archiveLoadP i d=placed (loadMap i) (op true d)++moves (loadMoves i) := by
  cases d <;> rfl

theorem restore_program (i : Fin 23) (d : Bool) :
    Shadow7.archiveRestoreP i d=placed (restoreMap i) (op false d)++moves (restoreMoves i) := by
  cases d <;> rfl

theorem load_run (i : Fin 23) (hi : i.val≤20) (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame (rawPorts i) (startCols true d) row s) :
    let t:=run (Shadow7.archiveLoadP i d) m s
    t.phase=s.phase ∧ Frame (codePorts i) (endCols true d) row t ∧ ∀q,(∀k,rawPorts i k≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d (rawPorts i) (codePorts i) (loadMap i) (loadMoves i) loadRoute (load_unique i hi) _
    (load_proper i hi) (load_route i hi) load_sort (load_scope i hi) row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map i ⟨q,lim⟩⟩

theorem restore_run (i : Fin 23) (hi : i.val≤20) (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame (codePorts i) (startCols false d) row s) :
    let t:=run (Shadow7.archiveRestoreP i d) m s
    t.phase=s.phase ∧ Frame (rawPorts i) (endCols false d) row t ∧ ∀q,(∀k,codePorts i k≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d (codePorts i) (rawPorts i) (restoreMap i) (restoreMoves i) restoreRoute (restore_unique i hi) _
    (restore_proper i hi) (restore_route i hi) restore_sort (restore_scope i hi) row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map i ⟨q,lim⟩⟩

theorem code_from_raw (i : Fin 23) (hi : i.val≤20) : ∀k,∃m,rawPorts i m=codePorts i k := by
  intro k
  have sub:=(heads_all i hi).2.2.2.2.1
  have mem:codePorts i k∈codePortsList i:=by
    rw [codePorts,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ((codeLength i).symm ▸ k.isLt),Option.getD_some]
    exact List.getElem_mem _
  apply rawIndex i
  rw [raw_split]
  rw [code_split] at mem
  rcases List.mem_append.mp mem with mem|mem
  · rcases List.mem_append.mp mem with mem|mem
    · exact List.mem_append_left _ (sub _ (List.mem_append_left _ mem))
    · exact List.mem_append_right _ mem
  · exact List.mem_append_left _ (sub _ (List.mem_append_right _ mem))

theorem roundtrip (i : Fin 23) (hi : i.val≤20) (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m n:List Bool)
    (ready:Frame (rawPorts i) raw row s) :
    run (Shadow7.archiveRestoreP i d) n (run (Shadow7.archiveLoadP i d) m s)=s := by
  have f:=load_run i hi d row hr s m ready
  have b:=restore_run i hi d row hr _ n f.2.1
  apply state_eq
  · exact b.1.trans f.1
  · intro q
    by_cases h:∃k,rawPorts i k=q
    · obtain ⟨k,rfl⟩:=h
      exact (b.2.1 k).trans (ready k).symm
    · have no:∀k,rawPorts i k≠q:=fun k eq=>h ⟨k,eq⟩
      have noc:∀k,codePorts i k≠q:=by
        intro k; obtain ⟨m,eq⟩:=code_from_raw i hi k
        exact eq ▸ no m
      exact (b.2.2 q noc).trans (f.2.2 q no)

end ECDSAAdd.Entrant.StairPacket.ArchiveJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.ArchiveJ7
open ECDSAAdd.Entrant.StairPacket.ArchivePortAction ECDSAAdd.Entrant.CodecBitSliceVerify ECDSAAdd.Entrant.StairArchiveRaw ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.ArchiveJ

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
theorem load_record (i : Fin 23) (hi : i.val≤20) (d:Bool) (data:Nat→Bool) (s:State) (m:List Bool)
    (legal:∃row<63145,∀q<23,(rawCol q).testBit row=data q)
    (recorded:∀k:Fin 157,k.val<23 → s.basis (rawPorts i k)=data k)
    (blank:∀k:Fin 157,23≤ k.val → s.basis (rawPorts i k)=false) :
    let t:=run (Shadow7.archiveLoadP i d) m s
    ∃row<63145, t.phase=s.phase ∧ Frame (codePorts i) (code d) row t ∧
        (∀k:Fin 16,t.basis (codePorts i ⟨k,by omega⟩)=(get (if d then ReducedWindowArchives.enter0StoredIn else ReducedWindowArchives.enter1StoredIn) k).testBit row) ∧
        (∀q,(∀k,rawPorts i k≠q) → t.basis q=s.basis q) ∧
        (∀ tape, run (Shadow7.archiveRestoreP i d) tape t=s) := by
  obtain ⟨row,hr,h⟩:=legal
  have ready:=starting_frame (rawPorts i) s row data h recorded blank
  have ⟨ph,fr,away⟩:=load_run i hi d row hr s m ready
  refine ⟨row,hr,ph,fr,?_,away,fun tape=>roundtrip i hi d row hr s m tape ready⟩
  intro k
  exact (fr ⟨k,by omega⟩).trans (congrArg (fun x:Nat=>x.testBit row) (field_bits d k))

end ECDSAAdd.Entrant.StairPacket.ArchiveJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowParams
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Baselines ECDSAAdd.Challenge ECDSAAdd.Entrant.StairArchiveGates

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.exitLoadP Shadow7.exitRestoreP Shadow7.routed Shadow7.unrouted Rolling1588.packAtTick Rolling1588.unpackAtTick
private theorem due_of {t : Nat} (h : dueTick t=true) : t≠5 ∧ History5.packDue t=true := by
  simp only [dueTick,Bool.and_eq_true,bne_iff_ne,ne_eq] at h
  exact h

end ECDSAAdd.Entrant.StairPacket.WindowParams
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Entrant.StairPacket.Partial

def forward45plus1 (d:Bool) : Program :=
  forwardW params d WindowParams.first WindowParams.rest

def reverse45plus1 (d:Bool) : Program :=
  reverseW params d WindowParams.first WindowParams.rest

end ECDSAAdd.Entrant.StairPacket.Shadow7
end


-- ===== ShadowBox2 =====
/-! Shadow7 leave footprints (leave-move, for build-leaves / build-chain): Window's `Partial` leaveBox2 box and the
swap-cell preservation (`swaps_kept`) at the seven-bit shadow coordinates. Generated from the stock Window blocks
(0a4223d) by helpers/leave-move/shadow/gen_box2.py; statements are the stock ones with `Shadow7.` names. Shadow
changes: the store-chain sites come from `Shadow7.storeW_cases` (three cases, above the anchor when `e0P ≤ 1573+k`),
the adjust's pool is bounded through `Shadow7.pool_cases` (it runs past `e0P+20`: 1725 > 1716 at s = 255), and
`sbP ≥ 54`. Stock helpers reused unchanged: `leaveBox`, `hfree`, `swap_not_free`, `notarget_of_free`, `tgtOK`, `segT`,
`swap_not_ok`, `keep_append`, `rail14`, `allW_iff_flat(2)`, `start_win`, `tags_range`. -/

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open GateMirror Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

/-- The scratch: `1556 .. min 1812 (2069-s)`. -/
theorem box2_S {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (a : 1556 ≤ q) (b : q ≤ 1812) (c : q + s ≤ 2069) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  unfold Shadow7.leaveBox2; omega
/-- The A columns `a0-1 .. a0+17`. -/
theorem box2_A {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (a : Shadow7.a0P s ≤ q + 1) (b : q ≤ Shadow7.a0P s + 17) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  have r14 := rail14 s
  unfold Shadow7.leaveBox2; omega
/-- The B rail from the low columns up: `b0-1 .. 785 + R`. -/
theorem box2_B {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (a : Shadow7.b0P s ≤ q + 1) (b : q ≤ 785 + railP s) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  unfold Shadow7.leaveBox2; omega
/-- The history letters `s+16 .. s+30`. -/
theorem box2_H {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (a : s + 16 ≤ q) (b : q ≤ s + 30) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  have r14 := rail14 s
  unfold Shadow7.leaveBox2; omega
/-- The history cells that the frame does not move: `s+1044 .. s+1058`, at most 1300. -/
theorem box2_C {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (a : 1044 + s ≤ q) (b : q ≤ 1058 + s) (c : q ≤ 1300) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  unfold Shadow7.leaveBox2; omega

/-- Boolean test of the five intervals (scratch first: most wires of the fixed segments are there). -/
def inBox2B (s q : Nat) : Bool :=
  (Nat.ble 1556 q && (Nat.ble q 1812 && Nat.ble (q + s) 2069)) ||
  ((Nat.ble (Shadow7.a0P s) (q + 1) && Nat.ble q (Shadow7.a0P s + 17)) ||
  ((Nat.ble (Shadow7.b0P s) (q + 1) && Nat.ble q (785 + railP s)) ||
  ((Nat.ble (s + 16) q && Nat.ble q (s + 30)) ||
  (Nat.ble (1044 + s) q && (Nat.ble q (1058 + s) && Nat.ble q 1300)))))

theorem inBox2B_sound {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Nat) (h : Shadow7.inBox2B s q = true) : Shadow7.leaveBox2 s q := by
  unfold Shadow7.inBox2B at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  rcases h with h | h | h | h | h
  · exact Shadow7.box2_S h1 h2 q h.1 h.2.1 h.2.2
  · exact Shadow7.box2_A h1 h2 q h.1 h.2
  · exact Shadow7.box2_B h1 h2 q h.1 h.2
  · exact Shadow7.box2_H h1 h2 q h.1 h.2
  · exact Shadow7.box2_C h1 h2 q h.1 h.2.1 h.2.2

def segBox2 (s : Nat) (gs : List Gate) : Bool := gs.all (fun g => g.wires.all (Shadow7.inBox2B s))
theorem allW_of_segBox2 {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) {gs : List Gate} (h : Shadow7.segBox2 s gs = true) :
    AllW (Shadow7.leaveBox2 s) gs := by
  intro g hg q hq
  unfold Shadow7.segBox2 at h; rw [List.all_eq_true] at h
  have := h g hg; rw [List.all_eq_true] at this
  exact Shadow7.inBox2B_sound h1 h2 q (this q hq)

theorem sig_box2 {s c : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (hc1 : 1044 ≤ c) (hc2 : c ≤ 1058) :
    Shadow7.leaveBox2 s (OB5.sig (s+14) (s+c)) := by
  have e := Shadow7.sig_hist h1 h2 hc1 hc2
  have r := Shadow7.rail_win h1 h2
  rcases e with ⟨e, le⟩ | ⟨e, lo, hi⟩
  · rw [e]; exact Shadow7.box2_C h1 h2 _ (by omega) (by omega) le
  · rw [e]; exact Shadow7.box2_S h1 h2 _ (by omega) hi (by omega)

theorem fixed_box2 : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    Shadow7.segBox2 (start j) (leaveFix0 (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)) ++
      leaveFix2 (start j) (Shadow7.sbP (start j)) ++ leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      leaveFix5 (start j) (Shadow7.sbP (start j)) ++ leaveFix8 (start j) (Shadow7.sbP (start j)) ++ leaveFix10 (start j) (Shadow7.sbP (start j)) ++
      leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j)) = true := by
  decide +kernel

section Main
attribute [local irreducible] Shadow7.leaveBox2

theorem leaveOps_box2 (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    AllW (Shadow7.leaveBox2 (start j)) (Shadow7.leaveOps (start j)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have fb := Shadow7.allW_of_segBox2 w1 w2 (Shadow7.fixed_box2 j h0 h1)
  simp only [allW_append_iff] at fb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, f4⟩, f5⟩, f8⟩, f10⟩, f11⟩, f12⟩, fl⟩ := fb
  generalize hs : start j = s at *
  have r := Shadow7.rail_win w1 w2
  have r14 := rail14 s
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have hL : 10 ≤ Shadow7.lowsP s ∧ Shadow7.lowsP s ≤ 11 := by ((try unfold Wire at *); omega)
  have boxS : ∀ q : Nat, 1556 ≤ q → q ≤ 1812 → q + s ≤ 2069 → Shadow7.leaveBox2 s q := fun q => Shadow7.box2_S w1 w2 q
  have boxA : ∀ q : Nat, Shadow7.a0P s ≤ q + 1 → q ≤ Shadow7.a0P s + 17 → Shadow7.leaveBox2 s q := fun q => Shadow7.box2_A w1 w2 q
  have boxB : ∀ q : Nat, Shadow7.b0P s ≤ q + 1 → q ≤ 785 + railP s → Shadow7.leaveBox2 s q := fun q => Shadow7.box2_B w1 w2 q
  have boxH : ∀ q : Nat, s + 16 ≤ q → q ≤ s + 30 → Shadow7.leaveBox2 s q := fun q => Shadow7.box2_H w1 w2 q
  have bank : ∀ i, i < Shadow7.wpP s + 15 → Shadow7.leaveBox2 s (Shadow7.bankW s i) := by
    intro i hi
    rcases Shadow7.bank_cases w1 w2 hi with ⟨a, e⟩ | ⟨a, b, e, c, d⟩ | ⟨a, e, c⟩
    · rw [e]; apply boxS <;> omega
    · rw [e]; apply boxB <;> omega
    · rw [e]; apply boxS <;> omega
  have tags : ∀ i, i < 16 → Shadow7.leaveBox2 s (tagsP.getD i 0) := by
    intro i hi; have t := tags_range i hi; apply boxS <;> ((try unfold Wire at *); omega)
  have aside : ∀ i, i ≤ 18 → Shadow7.leaveBox2 s (Shadow7.a0P s - 1 + i) := by intro i hi; apply boxA <;> omega
  have bside : ∀ i, i ≤ 12 → Shadow7.leaveBox2 s (Shadow7.b0P s - 1 + i) := by intro i hi; apply boxB <;> omega
  have scr : ∀ q, 1556 ≤ q → q ≤ Shadow7.e0P s + 20 → Shadow7.leaveBox2 s q := by intro q a b; apply boxS <;> ((try unfold Wire at *); omega)
  have ctl : ∀ (xs : List Wire), (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1614) → ∀ x ∈ xs, Shadow7.leaveBox2 s x :=
    fun xs h x hx => scr x (h x hx).1 (by have := (h x hx).2; (try unfold Wire at *); omega)
  have adj : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveAdjust s) := by
    unfold Shadow7.leaveAdjust
    refine allW_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by ((try unfold Wire at *); omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have p := Shadow7.pool_cases (i := i) w1 w2; apply boxS <;> ((try unfold Wire at *); omega)
  have bar : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveBarrel s) := by
    unfold Shadow7.leaveBarrel
    have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ Shadow7.wpP s + 15 → (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1614) →
        AllW (Shadow7.leaveBox2 s) (stageG 1613 (Shadow7.bankW s) xs d n) :=
      fun xs d n hn hx => allW_stageG _ _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (ctl xs hx)
        (fun i hi => ⟨bank i (by ((try unfold Wire at *); omega)), bank (i+d) (by ((try unfold Wire at *); omega))⟩)
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    exact allW_append (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide)) (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
  have joi : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveJoin s) := by
    unfold Shadow7.leaveJoin
    refine allW_append (allW_digitsG _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ _
      (fun i _ hi => ⟨tags i (by ((try unfold Wire at *); omega)), ?_, ?_⟩)) (allW_wordG _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ (fun r hr => ?_))
    · have := aside (i+1) (by ((try unfold Wire at *); omega)); rwa [show Shadow7.a0P s - 1 + (i+1) = Shadow7.a0P s + i by ((try unfold Wire at *); omega)] at this
    · have := aside (i+2) (by ((try unfold Wire at *); omega)); rwa [show Shadow7.a0P s - 1 + (i+2) = Shadow7.a0P s + (i+1) by ((try unfold Wire at *); omega)] at this
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr; rw [List.mem_range] at hi
      refine ⟨fun w hw => ?_, ?_, bank i (by ((try unfold Wire at *); omega))⟩
      · dsimp only at hw; split at hw
        · cases hw; exact tags i (by ((try unfold Wire at *); omega))
        · cases hw
      · have := aside (i+1) (by ((try unfold Wire at *); omega)); dsimp only; rwa [show Shadow7.a0P s - 1 + (i+1) = Shadow7.a0P s + i by ((try unfold Wire at *); omega)] at this
  have lr : AllW (Shadow7.leaveBox2 s) (Shadow7.lowRest s) := by
    unfold Shadow7.lowRest
    refine allW_append (allW_append (allW_append (allW_append ?_ (allW_xsG _ ?_)) (allW_addG _ _ _ ?_ ?_ ?_))
      (allW_xsG _ ?_)) ?_
    · refine allW_map _ _ (fun i hi q hq => ?_); rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl|rfl <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    all_goals try (intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega)))
    · first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    · rw [allW_iff_flat2]
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
  have sm : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveStoreMapped s) := by
    simp only [Shadow7.leaveStoreMapped]
    have lit : ∀ (gs : List Gate), (∀ q ∈ gs.flatMap Gate.wires, Shadow7.leaveBox2 s q) → AllW (Shadow7.leaveBox2 s) gs :=
      fun gs h => allW_iff_flat2.mpr h
    have hi : ∀ y ∈ (List.range (Shadow7.wpP s + 15 - Shadow7.lowsP s)).map (fun i => Shadow7.bankW s (Shadow7.lowsP s + i)), Shadow7.leaveBox2 s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank _ (by ((try unfold Wire at *); omega))
    have s2 : ∀ y ∈ (List.range (Shadow7.lowsP s + 1)).map (Shadow7.b0P s - 1 + ·), Shadow7.leaveBox2 s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bside i (by ((try unfold Wire at *); omega))
    refine allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append
      ?_ (allW_xsG _ hi)) ?_) (allW_xsG _ (fun y h => hi y (List.mem_reverse.mp h)))) ?_) (allW_xsG _ s2)) ?_)
      (allW_xsG _ (fun y h => s2 y (List.mem_reverse.mp h)))) ?_
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        have sc := Shadow7.storeW_cases w1 w2 (Shadow7.wpP s + 15 - Shadow7.lowsP s + 1)
        split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
      · have sc := Shadow7.storeW_cases w1 w2 k; first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
      · dsimp only; split
        · first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
        · exact bank _ (by ((try unfold Wire at *); omega))
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
      · first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
      · first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
  have lc : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveLowClose s) := by
    simp only [Shadow7.leaveLowClose]
    refine allW_append (allW_append (allW_xsG _ (fun y hy => ?_)) (allW_map _ _ (fun i hi q hq => ?_)))
      (allW_flatMap _ _ (fun i hi => allW_cswapG _ _ _ ?_ ?_ ?_))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    · rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
    all_goals (rw [List.mem_range] at hi; first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega)))
  have cl : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveClose s) := by
    unfold Shadow7.leaveClose
    refine allW_append (allW_eventsG _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) ?_) (allW_swapsG _ ?_)
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;>
        exact ⟨Shadow7.sig_box2 w1 w2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)), scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))⟩
    · intro p hp
      unfold Shadow7.movesP at hp
      rcases List.mem_append.mp hp with hp|hp
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
        exact ⟨bank _ (by ((try unfold Wire at *); omega)), by first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> refine ⟨?_, ?_⟩ <;> first | (apply boxS <;> ((try unfold Wire at *); omega)) | (apply boxA <;> ((try unfold Wire at *); omega)) | (apply boxB <;> ((try unfold Wire at *); omega)) | (apply boxH <;> ((try unfold Wire at *); omega))
  rw [Shadow7.leaveOps_split]
  refine allW_append (allW_append ?_ (allW_append (allW_append lr sm) lc)) cl
  unfold Shadow7.leaveHeadOps
  refine allW_append ?_ fl; refine allW_append ?_ f12; refine allW_append ?_ f11; refine allW_append ?_ f10
  refine allW_append ?_ joi; refine allW_append ?_ f8; refine allW_append ?_ bar; refine allW_append ?_ adj
  refine allW_append ?_ f5; refine allW_append ?_ f4; refine allW_append ?_ f3; refine allW_append ?_ f2
  exact allW_append f0 f1

end Main

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open GateMirror Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

theorem gadgets_free (s : Nat) (w1 : 90 ≤ s) (w2 : s ≤ 390) :
    AllW (hfree s) (Shadow7.leaveAdjust s) ∧ AllW (hfree s) (Shadow7.leaveBarrel s) ∧ AllW (hfree s) (Shadow7.leaveJoin s) ∧
    AllW (hfree s) (Shadow7.lowRest s) ∧ AllW (hfree s) (Shadow7.leaveStoreMapped s) ∧ AllW (hfree s) (Shadow7.leaveLowClose s) ∧
    AllW (hfree s) (swapsG (Shadow7.movesP s)) := by
  have e0b : Shadow7.e0P s + 20 + s < 2055 := by unfold Shadow7.e0P Shadow7.sbP; omega
  have e1b : Shadow7.e0P (s+15) + 8 + s < 2055 := by unfold Shadow7.e0P Shadow7.sbP; omega
  have r := Shadow7.rail_win w1 w2
  have r14 : railP (s+15) ≤ railP (s+14) := by unfold railP; split_ifs <;> omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have hL : 10 ≤ Shadow7.lowsP s ∧ Shadow7.lowsP s ≤ 11 := by ((try unfold Wire at *); omega)
  have bank : ∀ i, i < Shadow7.wpP s + 15 → hfree s (Shadow7.bankW s i) := by
    intro i hi; have bc := Shadow7.bank_cases w1 w2 hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have tags : ∀ i, i < 16 → hfree s (tagsP.getD i 0) := by
    intro i hi; have t := tags_range i hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have aside : ∀ i, i ≤ 19 → hfree s (Shadow7.a0P s - 1 + i) := by intro i hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have bside : ∀ i, i ≤ 12 → hfree s (Shadow7.b0P s - 1 + i) := by intro i hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have scr : ∀ q, 1556 ≤ q → q ≤ Shadow7.e0P s + 20 → hfree s q := by intro q a b; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have ehi : 1614 ≤ Shadow7.e0P s + 20 := by omega
  have ctl : ∀ (xs : List Wire), (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1614) → ∀ x ∈ xs, hfree s x :=
    fun xs h x hx => scr x (h x hx).1 (le_trans (h x hx).2 ehi)
  have adj : AllW (hfree s) (Shadow7.leaveAdjust s) := by
    unfold Shadow7.leaveAdjust
    refine allW_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by ((try unfold Wire at *); omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have p := Shadow7.pool_cases (i := i) w1 w2; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have bar : AllW (hfree s) (Shadow7.leaveBarrel s) := by
    unfold Shadow7.leaveBarrel
    have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ Shadow7.wpP s + 15 → (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1614) →
        AllW (hfree s) (stageG 1613 (Shadow7.bankW s) xs d n) :=
      fun xs d n hn hx => allW_stageG _ _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (ctl xs hx)
        (fun i hi => ⟨bank i (by ((try unfold Wire at *); omega)), bank (i+d) (by ((try unfold Wire at *); omega))⟩)
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    exact allW_append (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide)) (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
  have joi : AllW (hfree s) (Shadow7.leaveJoin s) := by
    unfold Shadow7.leaveJoin
    refine allW_append (allW_digitsG _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ _
      (fun i _ hi => ⟨tags i (by ((try unfold Wire at *); omega)), ?_, ?_⟩)) (allW_wordG _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ (fun r hr => ?_))
    · have := aside (i+1) (by ((try unfold Wire at *); omega)); rwa [show Shadow7.a0P s - 1 + (i+1) = Shadow7.a0P s + i by ((try unfold Wire at *); omega)] at this
    · have := aside (i+2) (by ((try unfold Wire at *); omega)); rwa [show Shadow7.a0P s - 1 + (i+2) = Shadow7.a0P s + (i+1) by ((try unfold Wire at *); omega)] at this
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr; rw [List.mem_range] at hi
      refine ⟨fun w hw => ?_, ?_, bank i (by ((try unfold Wire at *); omega))⟩
      · dsimp only at hw; split at hw
        · cases hw; exact tags i (by ((try unfold Wire at *); omega))
        · cases hw
      · have := aside (i+1) (by ((try unfold Wire at *); omega)); dsimp only; rwa [show Shadow7.a0P s - 1 + (i+1) = Shadow7.a0P s + i by ((try unfold Wire at *); omega)] at this
  have lr : AllW (hfree s) (Shadow7.lowRest s) := by
    unfold Shadow7.lowRest
    refine allW_append (allW_append (allW_append (allW_append ?_ (allW_xsG _ ?_)) (allW_addG _ _ _ ?_ ?_ ?_))
      (allW_xsG _ ?_)) ?_
    · refine allW_map _ _ (fun i hi q hq => ?_); rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl|rfl <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
    all_goals try (intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega))
    · ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
    · rw [allW_iff_flat]
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
  have sm : AllW (hfree s) (Shadow7.leaveStoreMapped s) := by
    simp only [Shadow7.leaveStoreMapped]
    have lit : ∀ (gs : List Gate), (∀ q ∈ gs.flatMap Gate.wires, hfree s q) → AllW (hfree s) gs :=
      fun gs h => allW_iff_flat.mpr h
    have hi : ∀ y ∈ (List.range (Shadow7.wpP s + 15 - Shadow7.lowsP s)).map (fun i => Shadow7.bankW s (Shadow7.lowsP s + i)), hfree s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank _ (by ((try unfold Wire at *); omega))
    have s2 : ∀ y ∈ (List.range (Shadow7.lowsP s + 1)).map (Shadow7.b0P s - 1 + ·), hfree s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bside i (by ((try unfold Wire at *); omega))
    refine allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append
      ?_ (allW_xsG _ hi)) ?_) (allW_xsG _ (fun y h => hi y (List.mem_reverse.mp h)))) ?_) (allW_xsG _ s2)) ?_)
      (allW_xsG _ (fun y h => s2 y (List.mem_reverse.mp h)))) ?_
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        have sc := Shadow7.storeW_cases w1 w2 (Shadow7.wpP s + 15 - Shadow7.lowsP s + 1)
        split_ands <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
      · have sc := Shadow7.storeW_cases w1 w2 k; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
      · dsimp only; split
        · ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
        · exact bank _ (by ((try unfold Wire at *); omega))
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        split_ands <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
      · ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
      · ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
  have lc : AllW (hfree s) (Shadow7.leaveLowClose s) := by
    simp only [Shadow7.leaveLowClose]
    refine allW_append (allW_append (allW_xsG _ (fun y hy => ?_)) (allW_map _ _ (fun i hi q hq => ?_)))
      (allW_flatMap _ _ (fun i hi => allW_cswapG _ _ _ ?_ ?_ ?_))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
    · rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
    all_goals (rw [List.mem_range] at hi; ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega))
  have mv : AllW (hfree s) (swapsG (Shadow7.movesP s)) := by
    refine allW_swapsG _ ?_
    intro p hp
    unfold Shadow7.movesP at hp
    rcases List.mem_append.mp hp with hp|hp
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
      exact ⟨bank _ (by ((try unfold Wire at *); omega)), by ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> ((try unfold hfree); (try unfold leaveBox)) <;> ((try unfold Wire at *); omega)
  exact ⟨adj, bar, joi, lr, sm, lc, mv⟩

theorem fixed_targets : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    segT (start j) (leaveFix0 (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)) ++
      leaveFix2 (start j) (Shadow7.sbP (start j)) ++ leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      leaveFix5 (start j) (Shadow7.sbP (start j)) ++ leaveFix8 (start j) (Shadow7.sbP (start j)) ++ leaveFix10 (start j) (Shadow7.sbP (start j)) ++
      leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j)) = true := by
  decide +kernel

/-- The event chain of the close flips each of the first five swap cells twice and targets no other. -/
theorem events_parity : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 → ∀ i : Fin 15,
    LeaveSelector.parityAt (OB5.sig (start j+14) (start j+1044+i.val))
      (GateMirror.forward (eventsG (Shadow7.e0P (start j) + 7) (Shadow7.e0P (start j) + 4)
        [(OB5.sig (start j+14) (start j+1044), 1556), (OB5.sig (start j+14) (start j+1045), 1559),
         (OB5.sig (start j+14) (start j+1046), 1560), (OB5.sig (start j+14) (start j+1047), 1561),
         (OB5.sig (start j+14) (start j+1048), 1562)])) = some false := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open GateMirror Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run measurementCount leaveFix0 leaveFix1 leaveFix2 leaveFix3 leaveFix4 leaveFix5 leaveFix8
  leaveFix10 leaveFix11 leaveFix12 Shadow7.lowSign Shadow7.leaveAdjust Shadow7.leaveBarrel Shadow7.leaveJoin Shadow7.lowRest
  Shadow7.leaveStoreMapped Shadow7.leaveLowClose eventsG swapsG Shadow7.movesP

/-- The leave keeps every swap cell. -/
theorem swaps_kept (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (i : Nat) (hi : i < 15) (s : State) (m : List Bool) :
    (run (Shadow7.leaveP j) m s).basis (OB5.sig (start j+14) (start j+1044+i)) = s.basis (OB5.sig (start j+14) (start j+1044+i)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  obtain ⟨adj, bar, joi, lr, sm, lc, mv⟩ := Shadow7.gadgets_free (start j) w1 w2
  have fx := Shadow7.fixed_targets j h0 h1
  have ev := Shadow7.events_parity j h0 h1 ⟨i, hi⟩
  generalize hq : OB5.sig (start j+14) (start j+1044+i) = q at *
  have fixNo : ∀ g ∈ leaveFix0 (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)) ++
      leaveFix2 (start j) (Shadow7.sbP (start j)) ++ leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      leaveFix5 (start j) (Shadow7.sbP (start j)) ++ leaveFix8 (start j) (Shadow7.sbP (start j)) ++ leaveFix10 (start j) (Shadow7.sbP (start j)) ++
      leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j),
      CodecBitSliceVerify.target (front g) ≠ q := by
    intro g hg e
    have t := List.all_eq_true.mp fx g hg
    rw [e, ←hq, swap_not_ok (start j) i w1 w2 hi] at t
    exact Bool.false_ne_true t
  have gad : ∀ {gs : List Gate}, AllW (hfree (start j)) gs → ∀ g ∈ gs, CodecBitSliceVerify.target (front g) ≠ q := by
    intro gs h g hg e
    exact notarget_of_free h w1 w2 i hi _ (List.mem_map.mpr ⟨g, hg, rfl⟩) (e.trans hq.symm)
  -- head ++ mid: no target is q
  have nt_app : ∀ {a b : List Gate}, (∀ g ∈ a, CodecBitSliceVerify.target (front g) ≠ q) →
      (∀ g ∈ b, CodecBitSliceVerify.target (front g) ≠ q) → ∀ g ∈ a ++ b, CodecBitSliceVerify.target (front g) ≠ q := by
    intro a b ha hb g hg
    rcases List.mem_append.mp hg with h|h
    · exact ha g h
    · exact hb g h
  have f0 : ∀ g ∈ leaveFix0 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f1 : ∀ g ∈ leaveFix1 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f2 : ∀ g ∈ leaveFix2 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f3 : ∀ g ∈ leaveFix3 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f4 : ∀ g ∈ leaveFix4 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f5 : ∀ g ∈ leaveFix5 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f8 : ∀ g ∈ leaveFix8 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f10 : ∀ g ∈ leaveFix10 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f11 : ∀ g ∈ leaveFix11 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f12 : ∀ g ∈ leaveFix12 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have fl : ∀ g ∈ Shadow7.lowSign (start j), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have hm' : ∀ g ∈ Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j), CodecBitSliceVerify.target (front g) ≠ q := by
    rw [Shadow7.leaveMidOps_eq]
    refine nt_app ?_ (nt_app (nt_app (gad lr) (gad sm)) (gad lc))
    unfold Shadow7.leaveHeadOps
    refine nt_app ?_ fl; refine nt_app ?_ f12; refine nt_app ?_ f11; refine nt_app ?_ f10
    refine nt_app ?_ (gad joi); refine nt_app ?_ f8; refine nt_app ?_ (gad bar); refine nt_app ?_ (gad adj)
    refine nt_app ?_ f5; refine nt_app ?_ f4; refine nt_app ?_ f3; refine nt_app ?_ f2
    exact nt_app f0 f1
  have hm : ∀ ins ∈ GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j)), CodecBitSliceVerify.target ins ≠ q := by
    intro ins hins
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hins
    exact hm' g hg
  have mvNo : ∀ ins ∈ GateMirror.forward (swapsG (Shadow7.movesP (start j))), CodecBitSliceVerify.target ins ≠ q := by
    intro ins hins
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hins
    exact gad mv g hg
  have A : ∀ m s, (run (GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j))) m s).basis q = s.basis q :=
    fun m s => preserve_readonly _ q hm s m
  have E : ∀ m s, (run (GateMirror.forward (eventsG (Shadow7.e0P (start j) + 7) (Shadow7.e0P (start j) + 4)
        [(OB5.sig (start j+14) (start j+1044), 1556), (OB5.sig (start j+14) (start j+1045), 1559),
         (OB5.sig (start j+14) (start j+1046), 1560), (OB5.sig (start j+14) (start j+1047), 1561),
         (OB5.sig (start j+14) (start j+1048), 1562)])) m s).basis q = s.basis q := by
    intro m s; rw [LeaveSelector.polarity q _ false ev, Bool.xor_false]
  have M : ∀ m s, (run (GateMirror.forward (swapsG (Shadow7.movesP (start j)))) m s).basis q = s.basis q :=
    fun m s => preserve_readonly _ q mvNo s m
  have split : Shadow7.leaveP j = GateMirror.forward (Shadow7.leaveHeadOps (start j) ++ Shadow7.leaveMidOps (start j)) ++
      (GateMirror.forward (eventsG (Shadow7.e0P (start j) + 7) (Shadow7.e0P (start j) + 4)
        [(OB5.sig (start j+14) (start j+1044), 1556), (OB5.sig (start j+14) (start j+1045), 1559),
         (OB5.sig (start j+14) (start j+1046), 1560), (OB5.sig (start j+14) (start j+1047), 1561),
         (OB5.sig (start j+14) (start j+1048), 1562)]) ++ GateMirror.forward (swapsG (Shadow7.movesP (start j)))) := by
    rw [Shadow7.leaveP, Shadow7.leaveOps_split, Shadow7.leaveClose, fwAppend, fwAppend, fwAppend]
  rw [split, keep_append _ _ q A (keep_append _ _ q E M)]

end ECDSAAdd.Entrant.StairPacket.Shadow7
end

-- ===== ShadowCounts =====
/-! Shadow7 window counts, slots, coverage and physicality (generated by
helpers/staircase82/shadow/port.py from StairSideA; the Main-side families). -/

section
namespace ECDSAAdd.Entrant.StairPacket.WindowSlots7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Baselines ECDSAAdd.Challenge ECDSAAdd.Entrant.StairPacket.WindowSlots

set_option maxHeartbeats 900000
theorem route (j : Fin 23) (i n : Nat) : gateSlots (Shadow7.routed j i n) ≤ 5000*n ∧
    gateSlots (Shadow7.unrouted j i n) ≤ 5000*n := by
  induction n generalizing i with
  | zero => exact ⟨by rfl,by rfl⟩
  | succ n ih =>
    have tail := ih (i+1)
    have t := tick (Shadow7.shape j) i
    simp only [Shadow7.routed,Shadow7.unrouted,gateSlots_append,rename_gateSlots,Nat.mul_succ]
    exact ⟨by omega,by omega⟩

end ECDSAAdd.Entrant.StairPacket.WindowSlots7
end

section
namespace ECDSAAdd.Entrant.StairPacket.PartialPhysical
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum

private theorem integer_ticks_ShadowCounts (L : SkywalkIntegerLayout) (hv : L.Valid) :
    GatePhysical (skywalkIntegerTick L) ∧ GatePhysical (skywalkIntegerUntick L) := by
  have enough : 1 ≤ L.half.length := by simp [SkywalkIntegerLayout.half]
  have narrow := narrowTicks_physical L 1 hv (by decide) enough
  simp only [narrowSkywalkTick, narrowSkywalkUntick, gatePhysical_append] at narrow
  obtain ⟨⟨⟨⟨route, half⟩, _⟩, prev⟩, ⟨⟨⟨⟨_, _⟩, _⟩, cx⟩, sw⟩⟩ := narrow
  have nd := L.record_nodup hv
  have fresh := (List.nodup_cons.mp nd).1
  have sx : L.ext ≠ L.history := by
    intro e
    apply fresh
    rw [← e]
    simp [SkywalkIntegerLayout.half]
  have sy : L.bSign ≠ L.history := by
    intro e
    apply fresh
    rw [← e]
    simp [SkywalkIntegerLayout.b, SkywalkIntegerLayout.bh]
  have toggle : GatePhysical (skywalkSignToggle L.ext L.bSign L.history) := by
    simp [skywalkSignToggle, GatePhysical, PhysicalInstr, ProperGate, sx, sy]
  have arithmetic := signedWords_physical L.history L.half L.b L.carry nd
  simp only [skywalkIntegerTick, skywalkIntegerUntick, signedRecord, signedUnrecord,
    gatePhysical_append]
  exact ⟨⟨⟨⟨route, half⟩, ⟨⟨toggle, arithmetic.1⟩, toggle⟩⟩, prev⟩,
    ⟨⟨⟨⟨prev, ⟨⟨toggle, arithmetic.2⟩, toggle⟩⟩, half⟩, cx⟩, sw⟩⟩

end ECDSAAdd.Entrant.StairPacket.PartialPhysical
end

section
namespace ECDSAAdd.Entrant.StairPacket.PartialPhysical7
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum ECDSAAdd.Entrant.StairPacket.PartialPhysical

theorem route (j : Fin 23) (a n : Nat) (h : a+n ≤ 15) :
    GatePhysical (Shadow7.routed j a n) ∧ GatePhysical (Shadow7.unrouted j a n) := by
  induction n generalizing a with
  | zero => simp [Shadow7.routed, Shadow7.unrouted, GatePhysical]
  | succ n ih =>
    have ha : a < 15 := by omega
    have valid := IntegerPacket.ok (Shadow7.shape j) ⟨a, ha⟩
    have tick := integer_ticks_ShadowCounts (IntegerPacket.ports (Shadow7.shape j) a) valid
    have range := (Shadow7.shape j).rangeEnd
    change start j + 15 ≤ 510 at range
    have inj := OB5.sig_injective (start j+a) (by omega)
    have tail := ih (a+1) (by omega)
    exact ⟨(gatePhysical_append _ _).2 ⟨gatePhysical_rename _ inj _ tick.1, tail.1⟩,
      (gatePhysical_append _ _).2 ⟨tail.2, gatePhysical_rename _ inj _ tick.2⟩⟩

end ECDSAAdd.Entrant.StairPacket.PartialPhysical7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowParams7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Baselines ECDSAAdd.Challenge ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.WindowParams

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.exitLoadP Shadow7.exitRestoreP Shadow7.routed Shadow7.unrouted Rolling1588.packAtTick Rolling1588.unpackAtTick
theorem portal_ok : ∀ t < 391, portalTick t=true → 5 ≤ Shadow7.wpP t := by decide

theorem portal_ok' (t : Nat) (h : portalTick t=true) : 5 ≤ Shadow7.wpP t := by
  have lt : t < 391 := by simp only [portalTick,Bool.and_eq_true,decide_eq_true_eq] at h; omega
  exact portal_ok t lt h

def tcV : Pieces Nat where
  enter _ := 18
  enterInv _ := 18
  leave j := if inBlocks j then 6*Shadow7.wpP (start j)+3*Shadow7.lowsP (start j)+193 else toffoliCount (Shadow7.leaveMoveP j)
  leaveInv j := if inBlocks j then 6*Shadow7.wpP (start j)+3*Shadow7.lowsP (start j)+192 else toffoliCount (Shadow7.leaveMoveInvP j)
  load _ d := if d then 77 else 77
  restore _ d := if d then 80 else 80
  portal t := if portalTick t then 5*Shadow7.wpP t-4 else toffoliCount (Shadow7.portalP t)
  portalInv t := if portalTick t then 5*Shadow7.wpP t-4 else toffoliCount (Shadow7.portalInvP t)
  park _ := 0
  parkInv _ := 0
  exitLoad _ d := if d then 77 else 77
  exitRestore _ d := if d then 80 else 80
  routed j a n := if a+n ≤ 15 then n*(2*(Shadow7.smallBits j+18)) else toffoliCount (Shadow7.routed j a n)
  unrouted j a n := if a+n ≤ 15 then n*(2*(Shadow7.smallBits j+18)) else toffoliCount (Shadow7.unrouted j a n)
  pack d s t := if dueTick t then 9 else toffoliCount (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))
  unpack d s t := if dueTick t then 11 else toffoliCount (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))
  tick e := if e < 511 then tickT e else toffoliCount (renameProgram (OB5.sig e) (TickRanges.tick base e))
  receiver e := if e < 511 then recvT e else
    toffoliCount (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))

def mcV : Pieces Nat where
  enter _ := 6
  enterInv _ := 6
  leave j := if inBlocks j then 2*Shadow7.wpP (start j)+Shadow7.lowsP (start j)+93 else measurementCount (Shadow7.leaveMoveP j)
  leaveInv j := if inBlocks j then 2*Shadow7.wpP (start j)+Shadow7.lowsP (start j)+94 else measurementCount (Shadow7.leaveMoveInvP j)
  load _ _ := 136
  restore _ _ := 124
  portal t := if portalTick t then 3*Shadow7.wpP t-5 else measurementCount (Shadow7.portalP t)
  portalInv t := if portalTick t then 3*Shadow7.wpP t-5 else measurementCount (Shadow7.portalInvP t)
  park _ := 0
  parkInv _ := 0
  exitLoad _ _ := 136
  exitRestore _ _ := 124
  routed j a n := if a+n ≤ 15 then n*(Shadow7.smallBits j+18) else measurementCount (Shadow7.routed j a n)
  unrouted j a n := if a+n ≤ 15 then n*(Shadow7.smallBits j+18) else measurementCount (Shadow7.unrouted j a n)
  pack d s t := if dueTick t then 4 else measurementCount (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))
  unpack d s t := if dueTick t then 2 else measurementCount (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))
  tick e := if e < 511 then tickM e else measurementCount (renameProgram (OB5.sig e) (TickRanges.tick base e))
  receiver e := if e < 511 then recvM e else
    measurementCount (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))

end ECDSAAdd.Entrant.StairPacket.WindowParams7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowParams
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Baselines ECDSAAdd.Challenge ECDSAAdd.Entrant.StairArchiveGates

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.exitLoadP Shadow7.exitRestoreP Shadow7.routed Shadow7.unrouted Rolling1588.packAtTick Rolling1588.unpackAtTick
private theorem due_of_ShadowCounts {t : Nat} (h : dueTick t=true) : t≠5 ∧ History5.packDue t=true := by
  simp only [dueTick,Bool.and_eq_true,bne_iff_ne,ne_eq] at h
  exact h

end ECDSAAdd.Entrant.StairPacket.WindowParams
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowParams7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Baselines ECDSAAdd.Challenge ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.WindowParams

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.exitLoadP Shadow7.exitRestoreP Shadow7.routed Shadow7.unrouted Rolling1588.packAtTick Rolling1588.unpackAtTick
theorem tc_eq : Shadow7.params.map toffoliCount=tcV := by
  simp only [Pieces.map,Shadow7.params,ofParts,tcV]
  congr 1
  · funext j; exact (Shadow7.enter_counts j).1
  · funext j; exact (Shadow7.enter_counts j).2.1
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (Shadow7.leaveMove_counts j (by omega) (by omega)).1
    · rfl
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (Shadow7.leaveMove_counts j (by omega) (by omega)).2.1
    · rfl
  · funext j d; rw [(Shadow7.archive_counts j 0 d).1]; cases d
    · exact PartialCosts.part9.1
    · exact PartialCosts.part25.1
  · funext j d; rw [(Shadow7.archive_counts j 0 d).2.2.2.1]; cases d
    · exact PartialCosts.part43.1
    · exact PartialCosts.part57.1
  · funext t; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).1
    · rfl
  · funext t; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).2.1
    · rfl
  · funext e; exact (Shadow7.park_counts e).1
  · funext e; exact (Shadow7.park_counts e).2.1
  · funext e d; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part9.1
    · exact PartialCosts.part25.1
  · funext e d; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part43.1
    · exact PartialCosts.part57.1
  · funext j a n; split
    · rename_i h; exact (WindowFold7.routed_counts j a n h).1
    · rfl
  · funext j a n; split
    · rename_i h; exact (WindowFold7.routed_counts j a n h).2.2.1
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of_ShadowCounts h).1 (due_of_ShadowCounts h).2).1
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of_ShadowCounts h).1 (due_of_ShadowCounts h).2).2.2.1
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).1
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).2.2.1
    · rfl

theorem mc_eq : Shadow7.params.map measurementCount=mcV := by
  simp only [Pieces.map,Shadow7.params,ofParts,mcV]
  congr 1
  · funext j; exact (Shadow7.enter_counts j).2.2.1
  · funext j; exact (Shadow7.enter_counts j).2.2.2.1
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (Shadow7.leaveMove_counts j (by omega) (by omega)).2.2.1
    · rfl
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (Shadow7.leaveMove_counts j (by omega) (by omega)).2.2.2.1
    · rfl
  · funext j d; rw [(Shadow7.archive_counts j 0 d).2.1]; cases d
    · exact PartialCosts.part9.2
    · exact PartialCosts.part25.2
  · funext j d; rw [(Shadow7.archive_counts j 0 d).2.2.2.2.1]; cases d
    · exact PartialCosts.part43.2
    · exact PartialCosts.part57.2
  · funext t; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).2.2.1
    · rfl
  · funext t; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).2.2.2.1
    · rfl
  · funext e; exact (Shadow7.park_counts e).2.2.1
  · funext e; exact (Shadow7.park_counts e).2.2.2.1
  · funext e d; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part9.2
    · exact PartialCosts.part25.2
  · funext e d; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part43.2
    · exact PartialCosts.part57.2
  · funext j a n; split
    · rename_i h; exact (WindowFold7.routed_counts j a n h).2.1
    · rfl
  · funext j a n; split
    · rename_i h; exact (WindowFold7.routed_counts j a n h).2.2.2
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of_ShadowCounts h).1 (due_of_ShadowCounts h).2).2.1
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of_ShadowCounts h).1 (due_of_ShadowCounts h).2).2.2.2
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).2.1
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).2.2.2
    · rfl

/-- Toffoli and measurement counts of any window, as Nat folds over closed forms. -/
theorem counts (d : Bool) (j : Fin 23) (js : List (Fin 23)) :
    toffoliCount (forwardW Shadow7.params d j js)=(forwardL tcV d j js).sum ∧
    toffoliCount (reverseW Shadow7.params d j js)=(reverseL tcV d j js).sum ∧
    measurementCount (forwardW Shadow7.params d j js)=(forwardL mcV d j js).sum ∧
    measurementCount (reverseW Shadow7.params d j js)=(reverseL mcV d j js).sum := by
  have f := measure_forward toffoliCount toffoliCount_append Shadow7.params d j js
  have r := measure_reverse toffoliCount toffoliCount_append Shadow7.params d j js
  have g := measure_forward measurementCount measurementCount_append Shadow7.params d j js
  have q := measure_reverse measurementCount measurementCount_append Shadow7.params d j js
  change toffoliCount _=(forwardL (Shadow7.params.map toffoliCount) d j js).sum at f
  change toffoliCount _=(reverseL (Shadow7.params.map toffoliCount) d j js).sum at r
  change measurementCount _=(forwardL (Shadow7.params.map measurementCount) d j js).sum at g
  change measurementCount _=(reverseL (Shadow7.params.map measurementCount) d j js).sum at q
  rw [tc_eq] at f r
  rw [mc_eq] at g q
  exact ⟨f,r,g,q⟩

/-- The window 90..360 (exit 375): window counts by one Nat decide over the closed forms. -/
theorem ship_counts :
    toffoliCount (forwardW Shadow7.params true first rest)=107690 ∧ toffoliCount (forwardW Shadow7.params false first rest)=107690 ∧
    toffoliCount (reverseW Shadow7.params true first rest)=107772 ∧ toffoliCount (reverseW Shadow7.params false first rest)=107772 ∧
    measurementCount (forwardW Shadow7.params true first rest)=53953 ∧ measurementCount (forwardW Shadow7.params false first rest)=53953 ∧
    measurementCount (reverseW Shadow7.params true first rest)=53690 ∧ measurementCount (reverseW Shadow7.params false first rest)=53690 := by
  rw [(counts true first rest).1,(counts false first rest).1,(counts true first rest).2.1,(counts false first rest).2.1,
    (counts true first rest).2.2.1,(counts false first rest).2.2.1,(counts true first rest).2.2.2,(counts false first rest).2.2.2]
  decide +kernel

/-- The window sizes (blocks 1..19, exit 375), by kernel evaluation of the fold's piece sums
(`counts` reduces them to `forwardL tcV d first rest` / `forwardL mcV d first rest`). -/
theorem ship_toffoliF_true : toffoliCount (forwardW Shadow7.params true first rest)=107690 := by
  rw [(counts true first rest).1]; decide +kernel

theorem ship_toffoliF_false : toffoliCount (forwardW Shadow7.params false first rest)=107690 := by
  rw [(counts false first rest).1]; decide +kernel

theorem ship_toffoliR_true : toffoliCount (reverseW Shadow7.params true first rest)=107772 := by
  rw [(counts true first rest).2.1]; decide +kernel

theorem ship_toffoliR_false : toffoliCount (reverseW Shadow7.params false first rest)=107772 := by
  rw [(counts false first rest).2.1]; decide +kernel

theorem ship_measureF : measurementCount (forwardW Shadow7.params true first rest)=53953 ∧
    measurementCount (forwardW Shadow7.params false first rest)=53953 := by
  rw [(counts true first rest).2.2.1,(counts false first rest).2.2.1]; decide +kernel

theorem ship_measureR : measurementCount (reverseW Shadow7.params true first rest)=53690 ∧
    measurementCount (reverseW Shadow7.params false first rest)=53690 := by
  rw [(counts true first rest).2.2.2,(counts false first rest).2.2.2]; decide +kernel

/-- `slotsV`: upper bounds of the piece slot counts. Exact closed forms where par-b's count lemmas apply (enter,
leave, portal, park, pack), the record's `WindowSlots` bounds for the archives (`part9/25/43/57`) and for the exit
tick/receiver at 270 (`part20/32`), `5000*n` for the routes (`WindowSlots.route`); the measured piece elsewhere, so
`slots_le` holds for every argument and a window `decide` only evaluates closed forms. -/
def slotsV : Pieces Nat where
  enter _ := 92
  enterInv _ := 92
  leave j := if inBlocks j then 23*Shadow7.wpP (start j)+10*Shadow7.lowsP (start j)+859+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveP j)
  leaveInv j := if inBlocks j then 23*Shadow7.wpP (start j)+10*Shadow7.lowsP (start j)+860+3*Shadow7.wpP (start j+15) else
    gateSlots (Shadow7.leaveMoveInvP j)
  load _ d := if d then 15978 else 15988
  restore _ d := if d then 12242 else 12262
  portal t := if portalTick t then 21*Shadow7.wpP t-7 else gateSlots (Shadow7.portalP t)
  portalInv t := if portalTick t then 21*Shadow7.wpP t-7 else gateSlots (Shadow7.portalInvP t)
  park _ := 9
  parkInv _ := 9
  exitLoad _ d := if d then 15978 else 15988
  exitRestore _ d := if d then 12242 else 12262
  routed _ _ n := 5000*n
  unrouted _ _ n := 5000*n
  pack d s t := if dueTick t then 144+(if d then 24 else 12) else
    gateSlots (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))
  unpack d s t := if dueTick t then 142+(if d then 24 else 12) else
    gateSlots (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))
  tick e := if e = 270 then 6004 else gateSlots (renameProgram (OB5.sig e) (TickRanges.tick base e))
  receiver e := if e = 270 then 6001 else
    gateSlots (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))

theorem slots_le : (Shadow7.params.map gateSlots).Le slotsV := by
  simp only [Pieces.map,Shadow7.params,ofParts,slotsV]
  constructor
  · intro j; exact (Shadow7.enter_counts j).2.2.2.2.1.le
  · intro j; exact (Shadow7.enter_counts j).2.2.2.2.2.le
  · intro j; dsimp only; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h
      exact (Shadow7.leaveMove_counts j (by omega) (by omega)).2.2.2.2.1.le
    · exact Nat.le_refl _
  · intro j; dsimp only; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h
      exact (Shadow7.leaveMove_counts j (by omega) (by omega)).2.2.2.2.2.le
    · exact Nat.le_refl _
  · intro j d; dsimp only; rw [(Shadow7.archive_counts j 0 d).2.2.1]; cases d
    · exact WindowSlots.part9
    · exact WindowSlots.part25
  · intro j d; dsimp only; rw [(Shadow7.archive_counts j 0 d).2.2.2.2.2.1]; cases d
    · exact WindowSlots.part43
    · exact WindowSlots.part57
  · intro t; dsimp only; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).2.2.2.2.1.le
    · exact Nat.le_refl _
  · intro t; dsimp only; split
    · rename_i h; exact (Shadow7.portal_counts t (portal_ok' t h)).2.2.2.2.2.le
    · exact Nat.le_refl _
  · intro e; exact (Shadow7.park_counts e).2.2.2.2.1.le
  · intro e; exact (Shadow7.park_counts e).2.2.2.2.2.le
  · intro e d; dsimp only; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.2.2.1]; cases d
    · exact WindowSlots.part9
    · exact WindowSlots.part25
  · intro e d; dsimp only; rw [(Shadow7.archive_counts first e d).2.2.2.2.2.2.2.2.2.2.2]; cases d
    · exact WindowSlots.part43
    · exact WindowSlots.part57
  · intro j a n; exact (WindowSlots7.route j a n).1
  · intro j a n; exact (WindowSlots7.route j a n).2
  · intro d s t; dsimp only; split
    · rename_i h; exact (pack_slots d s t (due_of_ShadowCounts h).1 (due_of_ShadowCounts h).2).1.le
    · exact Nat.le_refl _
  · intro d s t; dsimp only; split
    · rename_i h; exact (pack_slots d s t (due_of_ShadowCounts h).1 (due_of_ShadowCounts h).2).2.le
    · exact Nat.le_refl _
  · intro e; dsimp only; split
    · rename_i h; subst h; rw [rename_gateSlots]; exact WindowSlots.part20
    · exact Nat.le_refl _
  · intro e; dsimp only; split
    · rename_i h; subst h; rw [rename_gateSlots]; exact WindowSlots.part32
    · exact Nat.le_refl _

/-- The window 90..360 (exit 375): the slot sums of `slotsV`, one Nat evaluation (no program is evaluated). -/
theorem slot_sums : (forwardL slotsV true first rest).sum ≤ 1890801 ∧ (forwardL slotsV false first rest).sum ≤ 1890801 ∧
    (reverseL slotsV true first rest).sum ≤ 1816292 ∧ (reverseL slotsV false first rest).sum ≤ 1816440 := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.WindowParams7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowCovered7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.WindowCovered

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.exitLoadP Shadow7.exitRestoreP
/-- Window-form archives (flags at `e0(t)+6..8`) for ticks up to 390, on the sharp footprint `archFootW`. -/
theorem archFoot_dom {t q : Nat} (lo : 105 ≤ t) (hi : t ≤ 390) (h : archFootW t (Shadow7.e0P t + 6) q) : domainW q = true := by
  rw [dom_iff]; unfold archFootW Shadow7.e0P Shadow7.sbP at h; omega

theorem enter_cov (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : CoveredW (Shadow7.enterP j) ∧ CoveredW (Shadow7.enterInvP j) := by
  have w := Shadow7.enter_wires j (by omega) (by omega)
  exact ⟨fun q hq => footP_dom (start_lo j h0) (Nat.le_trans (start_hi j h1) (by decide)) (w.1 q hq),
    fun q hq => footP_dom (start_lo j h0) (Nat.le_trans (start_hi j h1) (by decide)) (w.2 q hq)⟩

attribute [local irreducible] Shadow7.leaveOps GateMirror.forward GateMirror.inverse in
theorem leave_cov (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : CoveredW (Shadow7.leaveP j) ∧ CoveredW (Shadow7.leaveInvP j) := by
  obtain ⟨w1, w2⟩ := allW_programs (Shadow7.leaveOps_box j (by omega) (by omega))
  constructor
  · intro q hq
    rw [Shadow7.leaveP] at hq
    exact leaveBox_dom (start_lo j h0) (start_hi j h1) (w1 q hq)
  · intro q hq
    rw [Shadow7.leaveInvP] at hq
    exact leaveBox_dom (start_lo j h0) (start_hi j h1) (w2 q hq)

attribute [local irreducible] Shadow7.leaveOps Shadow7.leaveMoveOps GateMirror.forward GateMirror.inverse in
theorem leaveMove_cov (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    CoveredW (Shadow7.leaveMoveP j) ∧ CoveredW (Shadow7.leaveMoveInvP j) := by
  obtain ⟨w1, w2⟩ := allW_programs (Shadow7.allW_leaveMove (start j) (Shadow7.leaveOps_box j (by omega) (by omega)))
  constructor
  · intro q hq
    rw [Shadow7.leaveMoveP] at hq
    exact leaveBox_dom (start_lo j h0) (start_hi j h1) (w1 q hq)
  · intro q hq
    rw [Shadow7.leaveMoveInvP] at hq
    exact leaveBox_dom (start_lo j h0) (start_hi j h1) (w2 q hq)

theorem portal_cov (t : Nat) (lo : 90 ≤ t) (hi : t ≤ 405) : CoveredW (Shadow7.portalP t) ∧ CoveredW (Shadow7.portalInvP t) := by
  have w := Shadow7.portal_wires t (by omega) (by omega)
  exact ⟨fun q hq => footP_dom lo hi (w.1 q hq), fun q hq => footP_dom lo hi (w.2 q hq)⟩

theorem park_cov (e : Nat) (lo : 225 ≤ e) (hi : e ≤ 405) : CoveredW (Shadow7.parkP e) ∧ CoveredW (Shadow7.parkInvP e) := by
  have w := Shadow7.park_wires e (by omega) hi
  exact ⟨fun q hq => parkFoot_dom lo (w.1 q hq), fun q hq => parkFoot_dom lo (w.2 q hq)⟩

theorem archive_cov (j : Fin 23) (d : Bool) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    CoveredW (Shadow7.archiveLoadP j d) ∧ CoveredW (Shadow7.archiveRestoreP j d) := by
  have lo : 105 ≤ start j+15 := by simp only [start]; omega
  have hi : start j+15 ≤ 390 := by simp only [start]; omega
  exact ⟨fun q hq => archFoot_dom lo hi (Shadow7.archiveLoadP_wiresW j d (by omega) q hq),
    fun q hq => archFoot_dom lo hi (Shadow7.archiveRestoreP_wiresW j d (by omega) q hq)⟩

theorem exitArch_cov (e : Nat) (d : Bool) (lo : 225 ≤ e) (hi : e ≤ 405) :
    CoveredW (Shadow7.exitLoadP e d) ∧ CoveredW (Shadow7.exitRestoreP e d) :=
  ⟨fun q hq => exitFoot_dom lo hi (Shadow7.exitLoadP_wiresW e d (by omega) q hq),
    fun q hq => exitFoot_dom lo hi (Shadow7.exitRestoreP_wiresW e d (by omega) q hq)⟩

/-- Routed ports of block `j` (dadon's `PartialSites.portsPass` decides, generic). -/
theorem ports_dom {j : Fin 23} (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) {a q : Nat} (ha : a < 15)
    (hq : q∈(IntegerPacket.ports (Shadow7.shape j) a).wires) : domainW (net j a q) = true := by
  have hj := j.isLt
  simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false] at hq
  rw [dom_iff]
  unfold net OB5.sig start
  split
  all_goals
    repeat' first | cases_type And | cases_type Or
    all_goals try simp only [Wire] at *
    all_goals omega

theorem routed_cov (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    ∀ (a n : Nat), a+n ≤ 15 → CoveredW (Shadow7.routed j a n) ∧ CoveredW (Shadow7.unrouted j a n) := by
  intro a n bound
  induction n generalizing a with
  | zero => constructor <;> intro q h <;> simp [Shadow7.routed,Shadow7.unrouted,wires] at h
  | succ n ih =>
    have h : a < 15 := by omega
    have step := skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (Shadow7.shape j) ⟨a,h⟩)
    have sub := ih (a+1) (by omega)
    have ok (P : Program) (hp : wires P ⊆ (IntegerPacket.ports (Shadow7.shape j) a).wires.toFinset) :
        CoveredW (renameProgram (net j a) P) := by
      intro q hq
      rw [renameProgram_support] at hq
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
      exact ports_dom h0 h1 h (List.mem_toFinset.mp (hp hx))
    exact ⟨appW (ok _ step.1) sub.1, appW sub.2 (ok _ step.2)⟩

theorem exit390 (d : Bool) :
    CoveredW (renameProgram (OB5.sig 390) (TickRanges.tick base 390)) ∧
    CoveredW (renameProgram (OB5.sig 390) (W.ReverseCarry.compactReceiverTick base 390)) ∧
    CoveredW (Shadow7.exitLoadP 390 d) ∧ CoveredW (Shadow7.exitRestoreP 390 d) := by
  have t := exit_tick 390 (by decide) (by decide +kernel)
  exact ⟨t.1,t.2,(exitArch_cov 390 d (by omega) (by omega)).1,(exitArch_cov 390 d (by omega) (by omega)).2⟩

theorem params_onE (d : Bool) : Shadow7.params.OnE CoveredW d 1 20 where
  block j h0 h1 := by
    have e := enter_cov j h0 (by omega)
    have l := leaveMove_cov j h0 (by omega)
    have r0 := routed_cov j h0 (by omega) 0 1 (by omega)
    have r1 := routed_cov j h0 (by omega) 1 14 (by omega)
    exact ⟨e.1,e.2,l.1,l.2,r0.1,r1.1,r0.2,r1.2⟩
  first j h := by
    have hs : start j = 90 := by simp only [start]; omega
    rw [hs]
    have p := pack_cov d 90 90 (by omega) (by omega) (by omega) (by omega)
    have o := portal_cov 90 (by omega) (by omega)
    exact ⟨p.1,p.2,o.1,o.2⟩
  later j h0 h1 := by
    have lo : 105 ≤ start j := by simp only [start]; omega
    have hi : start j ≤ 390 := by simp only [start]; omega
    have m : (start j-10)%5=0 := by simp only [start]; omega
    have p := pack_cov d (start j) (start j-10) (by omega) (by omega) (by omega) m
    exact ⟨p.1,p.2⟩
  saved j h0 h1 := archive_cov j d h0 (by omega)
  exit j h := by
    have hs : start j = 390 := by simp only [start]; omega
    rw [hs]
    have k := park_cov 390 (by omega) (by omega)
    have o := portal_cov 390 (by omega) (by omega)
    have p := pack_cov d 390 380 (by omega) (by omega) (by omega) (by omega)
    have x := exit390 d
    exact ⟨k.1,k.2,o.1,o.2,x.1,x.2.1,p.1,p.2,x.2.2.1,x.2.2.2⟩

/-- The window (both directions, both kernels) lies in the K2 domain. -/
theorem window_covered (d : Bool) :
    CoveredW (forwardW Shadow7.params d WindowParams.first WindowParams.rest) ∧
    CoveredW (reverseW Shadow7.params d WindowParams.first WindowParams.rest) :=
  ⟨flatten_of nilW (fun ha hb => appW ha hb) _
      (forwardL_onE (params_onE d) _ _ consec rfl last (by decide)),
    flatten_of nilW (fun ha hb => appW ha hb) _
      (reverseL_onE (params_onE d) _ _ consec rfl last (by decide))⟩

end ECDSAAdd.Entrant.StairPacket.WindowCovered7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowPhysicalW7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.WindowPhysicalW

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1 ReducedWindowArchives.restore0 ReducedWindowArchives.restore1
/-- Every gate of the leave is proper (no control on its target): par-c1's segment lemmas, without the state
hypotheses of `leave_ready`. -/
theorem leave_proper (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : ∀ g ∈ Shadow7.leaveOps (start j), proper g = true := by
  obtain ⟨w1,w2⟩ := start_win j h0 h1
  rw [Shadow7.leaveOps_split, Shadow7.leaveMidOps_eq]
  exact proper_append (proper_append (Shadow7.head_ok j h0 h1).2
    (proper_append (proper_append (Shadow7.lowRest_ok w1 w2).2 (Shadow7.storeMapped_ok w1 w2).2) (Shadow7.lowClose_ok w1 w2).2)) (Shadow7.close_ok w1 w2).2

theorem leave_phys (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    GatePhysical (Shadow7.leaveP j) ∧ GatePhysical (Shadow7.leaveInvP j) := by
  rw [Shadow7.leaveP, Shadow7.leaveInvP]; exact physical_of_proper _ (leave_proper j h0 h1)

/-- The move leave (`leaveMoveOps`): every gate is proper. -/
theorem leaveMove_proper (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    ∀ g ∈ Shadow7.leaveMoveOps (start j), proper g = true := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  exact Shadow7.leaveMove_proper_of w1 w2 (leave_proper j h0 h1)

theorem leaveMove_phys (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    GatePhysical (Shadow7.leaveMoveP j) ∧ GatePhysical (Shadow7.leaveMoveInvP j) := by
  rw [Shadow7.leaveMoveP, Shadow7.leaveMoveInvP]; exact physical_of_proper _ (leaveMove_proper j h0 h1)

theorem portal_properW90 : (Shadow7.portalOps 90).all proper = true := by decide +kernel

theorem portal_proper390 : (Shadow7.portalOps 390).all proper = true := by decide +kernel

theorem portal_phys90 : GatePhysical (Shadow7.portalP 90) ∧ GatePhysical (Shadow7.portalInvP 90) :=
  physical_of_proper _ (List.all_eq_true.mp portal_properW90)

theorem portal_phys390 : GatePhysical (Shadow7.portalP 390) ∧ GatePhysical (Shadow7.portalInvP 390) :=
  physical_of_proper _ (List.all_eq_true.mp portal_proper390)

/-- Window-form archives of block `j` (tick `start j + 15`), every window block up to 20. -/
theorem archive_phys (j : Fin 23) (d : Bool) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    GatePhysical (Shadow7.archiveLoadP j d) ∧ GatePhysical (Shadow7.archiveRestoreP j d) := by
  have lo : 90 ≤ start j+15 := by simp only [start]; omega
  have hi : start j+15 ≤ 405 := by simp only [start]; omega
  have nl : (Shadow7.loadPortsWP (start j+15) (Shadow7.e0P (start j+15)+6)).Nodup :=
    (List.nodup_append.mp (ArchiveJ7.rawNodup j h1)).1
  have nr : (Shadow7.restorePortsWP (start j+15)).Nodup := (List.nodup_append.mp (ArchiveJ7.codeNodup j h1)).1
  have fl : 1563 ≤ Shadow7.e0P (start j+15)+6 ∨ Shadow7.e0P (start j+15)+6+3 ≤ 1560 := Or.inl (by unfold Shadow7.e0P Shadow7.sbP; omega)
  constructor
  · rw [Shadow7.archiveLoadP]
    exact appP (load_codec_phys _ nl (by rw [Shadow7.loadPortsWP_length]) d) (moveLoad_phys _ lo hi)
  · rw [Shadow7.archiveRestoreP]
    exact appP (restore_codec_phys _ nr (by rw [Shadow7.restorePortsWP_length]) d) (moveRestore_phys _ _ lo hi fl)

/-- Stock-form exit archives at 390 (the two port lists by one decide each). -/
theorem exit_phys390 (d : Bool) : GatePhysical (Shadow7.exitLoadP 390 d) ∧ GatePhysical (Shadow7.exitRestoreP 390 d) := by
  have hb : bTopP 390+1 = 909 := by decide
  have nl : (Shadow7.loadPortsXP 390 909).Nodup := by decide +kernel
  have nr : (Shadow7.restorePortsXP 390).Nodup := by decide +kernel
  constructor
  · rw [Shadow7.exitLoadP, hb]
    exact appP (load_codec_phys _ nl (by rw [Shadow7.loadPortsXP_length]) d) (moveLoad_phys _ (by omega) (by omega))
  · rw [Shadow7.exitRestoreP, hb]
    exact appP (restore_codec_phys _ nr (by rw [Shadow7.restorePortsXP_length]) d)
      (moveRestore_phys _ _ (by omega) (by omega) (Or.inr (by omega)))

attribute [local irreducible] GatePhysical Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP
  Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP Shadow7.exitLoadP Shadow7.exitRestoreP Shadow7.routed Shadow7.unrouted Rolling1588.packAtTick
  Rolling1588.unpackAtTick in
theorem params_onE_phys (d : Bool) : Shadow7.params.OnE GatePhysical d 1 20 where
  block j h0 h1 := by
    have e := Shadow7.enterP_physical j (by omega) (by omega)
    have l := leaveMove_phys j (by omega) (by omega)
    have r0 := PartialPhysical7.route j 0 1 (by omega)
    have r1 := PartialPhysical7.route j 1 14 (by omega)
    exact ⟨e.1,e.2,l.1,l.2,r0.1,r1.1,r0.2,r1.2⟩
  first j h := by
    have hs : start j = 90 := by simp only [start]; omega
    rw [hs]
    have p := pack_phys d 90 90 (by omega) (by omega) (by omega) (by decide)
    exact ⟨p.1,p.2,portal_phys90.1,portal_phys90.2⟩
  later j h0 h1 := by
    have lo : 105 ≤ start j := by simp only [start]; omega
    have hi : start j ≤ 390 := by simp only [start]; omega
    have due : History5.packDue (start j-10)=true := by
      simp only [History5.packDue,decide_eq_true_eq,start]; omega
    have p := pack_phys d (start j) (start j-10) (by omega) (by omega) (by omega) due
    exact ⟨p.1,p.2⟩
  saved j h0 h1 := archive_phys j d h0 (by omega)
  exit j h := by
    have hs : start j = 390 := by simp only [start]; omega
    rw [hs]
    have k := Shadow7.parkP_physical 390 (by omega) (by omega)
    have p := pack_phys d 390 380 (by omega) (by omega) (by omega) (by decide)
    have t := tick_phys 390 (by omega)
    have x := exit_phys390 d
    exact ⟨k.1,k.2,portal_phys390.1,portal_phys390.2,t.1,t.2,p.1,p.2,x.1,x.2⟩

/-- The window (both directions, both kernels) is physical. -/
theorem window_physical (d : Bool) :
    GatePhysical (forwardW Shadow7.params d WindowParams.first WindowParams.rest) ∧
    GatePhysical (reverseW Shadow7.params d WindowParams.first WindowParams.rest) :=
  ⟨flatten_of nilP (fun ha hb => appP ha hb) _
      (forwardL_onE (params_onE_phys d) _ _ WindowCovered.consec rfl WindowCovered.last (by decide)),
    flatten_of nilP (fun ha hb => appP ha hb) _
      (reverseL_onE (params_onE_phys d) _ _ WindowCovered.consec rfl WindowCovered.last (by decide))⟩

end ECDSAAdd.Entrant.StairPacket.WindowPhysicalW7
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowParams7
open ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Challenge ECDSAAdd.Entrant.StairPacket.WindowParams

/-- Slot bounds of the window (upper bounds only; the judge has no slot ceiling). -/
theorem ship_slotsF : gateSlots (Shadow7.forward45plus1 true) ≤ 1890801 ∧
    gateSlots (Shadow7.forward45plus1 false) ≤ 1890801 := by
  show gateSlots (forwardW Shadow7.params true first rest) ≤ 1890801 ∧ gateSlots (forwardW Shadow7.params false first rest) ≤ 1890801
  rw [measure_forward gateSlots gateSlots_append, measure_forward gateSlots gateSlots_append]
  exact ⟨(forwardL_le slots_le true first rest).trans slot_sums.1,
    (forwardL_le slots_le false first rest).trans slot_sums.2.1⟩

theorem ship_slotsR : gateSlots (Shadow7.reverse45plus1 true) ≤ 1816292 ∧
    gateSlots (Shadow7.reverse45plus1 false) ≤ 1816440 := by
  show gateSlots (reverseW Shadow7.params true first rest) ≤ 1816292 ∧ gateSlots (reverseW Shadow7.params false first rest) ≤ 1816440
  rw [measure_reverse gateSlots gateSlots_append, measure_reverse gateSlots gateSlots_append]
  exact ⟨(reverseL_le slots_le true first rest).trans slot_sums.2.2.1,
    (reverseL_le slots_le false first rest).trans slot_sums.2.2.2⟩

end ECDSAAdd.Entrant.StairPacket.WindowParams7
end

